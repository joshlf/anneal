/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Mir.IeeeFloatArith
import LeanMiriSpec.FloatCastLM
import Miri.Memory.CtfeProvenance

/-!
# IEEE-754 Float Arithmetic, Negation, Comparison, and `Ptr2IntTransmutePolicy` Correspondence (`LeanMiriSpec.FloatArithLM`)
Dual-authority correspondence between Anneal's trusted MIR semantics (`Trusted.Rustc.V2026_06_01.MirSemantics`, `Anneal.Mir.IeeeFloatArith`) and vendored `lean-miri` (`Miri.Interpreter.{Float,FloatOps,ScalarOps,Rvalue,Step,Cast}` and `Miri.Memory.Allocation` under runtime `Provenance` vs. CTFE `CtfeProvenance`):
* **Part 1 — Engine-Level `FloatBits` (`f32` & `f64`)**: `floatBits_{negate,partialCompare,comparison,exactSum,arithmetic,nanChoices_*}_eq` (`.sub` mapped to `.Sub` *before* `adjustNaN`).
* **Part 2 — `FloatOps.{unary, binary}` & Step-Hook Overlay**: `floatOps_unary_neg_eq`, `floatOps_binary_{cmp,arith_deterministic}_eq`, nondet soundness & index-exact completeness (`floatOps_binary_arith_{any_chooseNaN_rel,pure_index_exact,completeness}`), valid default selector `annealChooseBinaryNaN`, exact fail-closed errors, and `annealStepHooksFloatArith`.
* **Part 3 — Real `Step.step` vs. `stepMirFn` / `EvalRvalueFloatRel` Simulations**: immediate & indirect simulations over `StateRelLM3_1`/`StepRelLM3_1` for unary negation, comparisons (`-> bool`), deterministic (`copy/copy`, `const/const`, mixed `copy/const` & `const/copy`, `move/copy`, indirect dst) & nondeterministic (`copy/copy`, `const/const`, index-exact mixed `const/copy` & `copy/const`) arithmetic, exact-message uninit unary/binary UB lockstep, and `f16`/`f128` + invalid-`BinOp` fail-closed boundaries.
* **Part 4 — `Ptr2IntTransmutePolicy` & Witnesses `W1–W12`**: runtime `Provenance` (strip) vs. `CtfeProvenance` (`.readPointerAsInt`), provenance-free `{to,from}_bits` agreement, `Cast.cast`-level-ONLY transmute model (`miriTransmuteScalarCheck`; NOT wired into `annealStepHooksFloatArith`), `usize -> *const T` vs. `usize -> &T`/`fn()` & uninit UB, `w1_lm_*..w12_lm_*` (`W10`: all five IEEE-754 indeterminate forms give positive-sign `preferredNaN` on BOTH engines; `W11`: real `binary64` `Step.step` & mixed `const - copy qNaN`; `W12`: mixed `copy - const` & two-NaN operand-order flip), and standard-axiom guards.
`miri#5643` ordering: for `.sub`, BOTH authorities build `nanChoices` from the ORIGINAL un-negated operands (`w3_lm_nan_choices_and_sub_order`, `w7_lm_f64_and_sub_index_exact`). -/
namespace LeanMiriSpec.FloatArithLM
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.Mir.IeeeFloatArith
open LeanMiriSpec.Correspondence
/-! ## Part 1. Engine-Level `Miri.Interpreter.FloatBits` Correspondence (`f32` & `f64`) -/
local macro "miriExactSum" : term => `(miri_private% Miri.Interpreter.Float Miri.Interpreter.FloatBits.exactSum)
local macro "miriSignedNumerator" : term => `(miri_private% Miri.Interpreter.Float Miri.Interpreter.FloatBits.signedNumerator)
local macro "miriEncode" : term => `(miri_private% Miri.Interpreter.Float Miri.Interpreter.FloatBits.encode)
local macro "miriFloatOpsScalarResult" : term => `(miri_private% Miri.Interpreter.FloatOps Miri.Interpreter.FloatOps.scalarResult)
local macro "miriFloatOpsLiftResult" : term => `(miri_private% Miri.Interpreter.FloatOps Miri.Interpreter.FloatOps.liftResult)
local macro "miriReadScalarBits" : term => `(miri_private% Miri.Interpreter.FloatOps Miri.Interpreter.FloatOps.readScalarBits)
local macro "miriReadTargetUInt" : term => `(miri_private% Miri.Memory.Allocation Miri.Memory.readTargetUInt)
local macro "miriScalarOpsFinish" : term => `(miri_private% Miri.Interpreter.ScalarOps Miri.Interpreter.ScalarOps.finish)
local macro "miriScalarOpsToScalar" : term => `(miri_private% Miri.Interpreter.ScalarOps Miri.Interpreter.ScalarOps.toScalar)
local macro "miriScalarOpsAssertSameType" : term => `(miri_private% Miri.Interpreter.ScalarOps Miri.Interpreter.ScalarOps.assertSameType)
/-! ### 1.1 Bitwise unary negation (`FloatBits.negate` vs. `evalFloatNeg`) -/
private theorem unpackBits_neg_eq_decide (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    (unpackBits f bits).neg = decide (2 ^ (f.width - 1) ≤ bits) := by
  have hsplit : 2 ^ f.width = 2 * 2 ^ (f.width - 1) := by cases f <;> decide
  have hpos : 0 < 2 ^ (f.width - 1) := Nat.two_pow_pos _
  unfold unpackBits; dsimp only
  by_cases hle : 2 ^ (f.width - 1) ≤ bits
  · have hlt2 : bits / 2 ^ (f.width - 1) < 2 := (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
    have hge1 : 1 ≤ bits / 2 ^ (f.width - 1) := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
    have hdiv : bits / 2 ^ (f.width - 1) = 1 := by omega
    rw [hdiv]; simp only [hle, decide_true]; rfl
  · rw [Nat.div_eq_of_lt (Nat.lt_of_not_le hle)]; simp only [hle, decide_false]; rfl
private theorem floatKindToMiriDecoded_negative (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    (floatKindToMiriDecoded f (decodeBits f bits)).negative = decide (2 ^ (f.width - 1) ≤ bits) := by
  rw [← unpackBits_neg_eq_decide f bits h]
  unfold decodeBits; dsimp only
  by_cases h1 : (unpackBits f bits).exponent = 2 ^ f.exponentBits - 1
  · simp only [h1, ↓reduceIte]
    by_cases h2 : (unpackBits f bits).fraction = 0 <;> simp only [h2, ↓reduceIte] <;> rfl
  · simp only [h1, ↓reduceIte]
    by_cases h2 : (unpackBits f bits).exponent = 0
    · simp only [h2, ↓reduceIte]
      by_cases h3 : (unpackBits f bits).fraction = 0 <;> simp only [h3, ↓reduceIte] <;> rfl
    · simp only [h2, ↓reduceIte]; rfl
/-- **Bitwise negation equivalence**: on every canonical `f32`/`f64` bit pattern (`bits < 2 ^ f.width`), `Miri.Interpreter.FloatBits.negate` flips only the sign bit, agreeing bit-for-bit with `evalFloatNeg` (preserving sNaN/qNaN payloads verbatim). -/
theorem floatBits_negate_eq (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    Miri.Interpreter.FloatBits.negate ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩ =
      .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128 (evalFloatNeg f bits)⟩ := by
  rw [LeanMiriSpec.Correspondence.floatBits_negate_eq f bits h, floatKindToMiriDecoded_negative f bits h]
  unfold evalFloatNeg; rw [Nat.mod_eq_of_lt h]
  by_cases hle : 2 ^ (f.width - 1) ≤ bits <;> simp [hle]
/-! ### 1.2 Partial ordering and 6-operator comparisons -/
private theorem int_compare_eq_if (x y : Int) :
    compare x y = (if x < y then Ordering.lt else if x = y then Ordering.eq else Ordering.gt) := rfl
private theorem bool_compare_not_eq (ln rn : Bool) :
    compare (!ln) (!rn) =
      (match ln, rn with
       | true, true | false, false => Ordering.eq
       | true, false => Ordering.lt | false, true => Ordering.gt) := by
  cases ln <;> cases rn <;> rfl
private theorem zero_vs_finite_compare (rn : Bool) (rnum zden : Nat) (hrn : 0 < rnum) (hz : 0 < zden) :
    compare (0 : Int) ((if rn then -(Int.ofNat rnum) else Int.ofNat rnum) * Int.ofNat zden) =
      (if rn then Ordering.gt else Ordering.lt) := by
  rw [int_compare_eq_if]
  have hpos : (0 : Int) < (rnum : Int) * (zden : Int) := Int.mul_pos (by omega) (by omega)
  cases rn with
  | true =>
    simp only [↓reduceIte, Int.ofNat_eq_natCast]
    have hneg : -(rnum : Int) * (zden : Int) < 0 := by rw [Int.neg_mul]; omega
    simp only [show ¬ ((0 : Int) < -(rnum : Int) * (zden : Int)) by omega, show ¬ ((0 : Int) = -(rnum : Int) * (zden : Int)) by omega, ↓reduceIte]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_natCast, hpos]
private theorem finite_vs_zero_compare (ln : Bool) (lnum zden : Nat) (hln : 0 < lnum) (hz : 0 < zden) :
    compare ((if ln then -(Int.ofNat lnum) else Int.ofNat lnum) * Int.ofNat zden) (0 : Int) =
      (if ln then Ordering.lt else Ordering.gt) := by
  rw [int_compare_eq_if]
  have hpos : (0 : Int) < (lnum : Int) * (zden : Int) := Int.mul_pos (by omega) (by omega)
  cases ln with
  | true =>
    simp only [↓reduceIte, Int.ofNat_eq_natCast]
    have hneg : -(lnum : Int) * (zden : Int) < 0 := by rw [Int.neg_mul]; omega
    simp only [hneg, ↓reduceIte]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_natCast]
    simp only [show ¬ ((lnum : Int) * (zden : Int) < 0) by omega, show ¬ ((lnum : Int) * (zden : Int) = 0) by omega, ↓reduceIte]
private theorem miriSignedNumerator_eq_signedNum (neg : Bool) (n : Nat) :
    miriSignedNumerator neg n = signedNum neg n := rfl
/-- **Partial comparison equivalence**: across all canonical `f32`/`f64` bit pairs (including `-0.0 == +0.0`, `±∞`, qNaN, and sNaN), `FloatBits.partialCompare` agrees identically with `evalFloatPartialCompare`. -/
theorem floatBits_partialCompare_eq (f : IeeeFormat) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    Miri.Interpreter.FloatBits.partialCompare
        ⟨ieeeFormatToMiri f, BitVec.ofNat 128 a⟩ ⟨ieeeFormatToMiri f, BitVec.ofNat 128 b⟩ =
      .ok (evalFloatPartialCompare f a b) := by
  unfold Miri.Interpreter.FloatBits.partialCompare evalFloatPartialCompare
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, floatBits_decode_eq f a ha, floatBits_decode_eq f b hb,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, bind, Except.bind, pure, Except.pure]
  have hzden : 0 < (powScale 0 1 (f.minExponent - (f.fractionBits : Int))).2 :=
    Anneal.Mir.IeeeFloatCast.powScale_snd_pos 0 _
  cases hda : decodeBits f a with
  | nan _ _ _ => cases hdb : decodeBits f b <;> rfl
  | inf ln =>
    cases hdb : decodeBits f b with
    | inf rn => show Except.ok (some (compare (!ln) (!rn))) = _; rw [bool_compare_not_eq]; rfl
    | _ => rfl
  | zero ln =>
    cases hdb : decodeBits f b with
    | zero rn =>
      show Except.ok (some (compare (miriSignedNumerator ln 0 * Int.ofNat _) (miriSignedNumerator rn 0 * Int.ofNat _))) = _
      have hl0 : miriSignedNumerator ln 0 = 0 := by cases ln <;> rfl
      have hr0 : miriSignedNumerator rn 0 = 0 := by cases rn <;> rfl
      rw [hl0, hr0, Int.zero_mul]; rfl
    | finite rn rnum rden =>
      have hrpos := decodeBits_finite_num_pos f b rn rnum rden hdb
      show Except.ok (some (compare (miriSignedNumerator ln 0 * Int.ofNat rden)
        (miriSignedNumerator rn rnum * Int.ofNat (powScale 0 1 (f.minExponent - (f.fractionBits : Int))).2))) = _
      have hl0 : miriSignedNumerator ln 0 = 0 := by cases ln <;> rfl
      rw [hl0, Int.zero_mul, miri_signedNumerator_eq, zero_vs_finite_compare rn rnum _ hrpos hzden]
      simp [Nat.ne_of_gt hrpos]
    | _ => rfl
  | finite ln lnum lden =>
    have hlpos := decodeBits_finite_num_pos f a ln lnum lden hda
    cases hdb : decodeBits f b with
    | zero rn =>
      show Except.ok (some (compare (miriSignedNumerator ln lnum * Int.ofNat (powScale 0 1 (f.minExponent - (f.fractionBits : Int))).2)
        (miriSignedNumerator rn 0 * Int.ofNat lden))) = _
      have hr0 : miriSignedNumerator rn 0 = 0 := by cases rn <;> rfl
      rw [hr0, Int.zero_mul, miri_signedNumerator_eq, finite_vs_zero_compare ln lnum _ hlpos hzden]
      simp [Nat.ne_of_gt hlpos]
    | finite rn rnum rden =>
      show Except.ok (some (compare (miriSignedNumerator ln lnum * Int.ofNat rden)
        (miriSignedNumerator rn rnum * Int.ofNat lden))) = _
      rw [int_compare_eq_if, miriSignedNumerator_eq_signedNum, miriSignedNumerator_eq_signedNum]; rfl
    | _ => rfl
/-- **Comparison equivalence**: across all canonical `f32`/`f64` bit pairs and every `BinOp`, `FloatBits.comparison (translateBinOp op)` agrees with `evalFloatCmp` on `eq`/`ne`/`lt`/`le`/`gt`/`ge` and throws `.invalidBinaryOperator` on all other operators. -/
theorem floatBits_comparison_eq (op : MirAst.BinOp) (f : IeeeFormat) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    Miri.Interpreter.FloatBits.comparison (translateBinOp op)
        ⟨ieeeFormatToMiri f, BitVec.ofNat 128 a⟩ ⟨ieeeFormatToMiri f, BitVec.ofNat 128 b⟩ =
      match evalFloatCmp op f a b with
      | .some res => .ok res
      | .none => .error (.invalidBinaryOperator (translateBinOp op)) := by
  unfold Miri.Interpreter.FloatBits.comparison evalFloatCmp
  rw [floatBits_partialCompare_eq f a b ha hb]; simp only [bind, Except.bind, pure, Except.pure]
  cases op <;> try rfl
  all_goals cases evalFloatPartialCompare f a b with | none => rfl | some ord => cases ord <;> rfl
/-! ### 1.3 Exact sum and 5-operator arithmetic (`Add`, `Sub`, `Mul`, `Div`, `Rem`) -/
private theorem miriExactSum_eq (f : Miri.Interpreter.FloatFormat)
    (l r : Miri.Interpreter.FloatDecoded) :
    miriExactSum f l r =
      match l.value, r.value with
      | .nan _, _ | _, .nan _ => pure (Miri.Interpreter.FloatBits.preferredNaN f)
      | .infinite, .infinite =>
        pure (if l.negative != r.negative then Miri.Interpreter.FloatBits.preferredNaN f
              else Miri.Interpreter.FloatBits.infinity f l.negative)
      | .infinite, _ => pure (Miri.Interpreter.FloatBits.infinity f l.negative)
      | _, .infinite => pure (Miri.Interpreter.FloatBits.infinity f r.negative)
      | .finite ln ld, .finite rn rd =>
        let n := miriSignedNumerator l.negative ln * Int.ofNat rd + miriSignedNumerator r.negative rn * Int.ofNat ld
        let sign := if n == 0 then ln == 0 && rn == 0 && l.negative && r.negative else decide (n < 0)
        Miri.Interpreter.FloatBits.roundRatio f sign n.natAbs (ld * rd) := rfl
private theorem roundRatioTiesToEven_mul_scale (f : IeeeFormat) (neg : Bool) (n d c : Nat) (hc : 0 < c) :
    roundRatioTiesToEven f neg (n * c) (d * c) = roundRatioTiesToEven f neg n d := by
  rw [← Anneal.Mir.IeeeFloatCast.roundRatioBits_tiesToEven f neg (n * c) (d * c), ← Anneal.Mir.IeeeFloatCast.roundRatioBits_tiesToEven f neg n d]
  exact Anneal.Mir.IeeeFloatCast.roundRatioBits_mul .tiesToEven f neg n d c hc
private theorem floatKindToMiriDecoded_negateFloatKind (f : IeeeFormat) (k : FloatKind) :
    floatKindToMiriDecoded f (negateFloatKind k) =
      { floatKindToMiriDecoded f k with negative := !(floatKindToMiriDecoded f k).negative } := by
  cases k <;> rfl
private theorem signedProd_nonzero_sign_abs (neg : Bool) (num zden : Nat) (hnum : 0 < num) (hz : 0 < zden) :
    let prod : Int := miriSignedNumerator neg num * Int.ofNat zden
    (prod == 0) = false ∧ decide (prod < 0) = neg ∧ prod.natAbs = num * zden := by
  dsimp only; rw [miri_signedNumerator_eq]
  have hpos : (0 : Int) < (num : Int) * (zden : Int) := Int.mul_pos (by omega) (by omega)
  cases neg with
  | true =>
    simp only [↓reduceIte, Int.ofNat_eq_natCast]
    rw [Int.neg_mul]
    exact ⟨by simp only [beq_eq_false_iff_ne]; omega,
      by simp only [show -((num : Int) * (zden : Int)) < 0 by omega, decide_true],
      by simp [Int.natAbs_mul]⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_natCast]
    exact ⟨by simp only [beq_eq_false_iff_ne]; omega,
      by simp only [show ¬ ((num : Int) * (zden : Int) < 0) by omega, decide_false],
      by simp [Int.natAbs_mul]⟩
private theorem roundRatio_zero_eq_zeroBits (f : IeeeFormat) (neg : Bool) (d : Nat) (hd : d ≠ 0) :
    Miri.Interpreter.FloatBits.roundRatio (ieeeFormatToMiri f) neg 0 d =
      .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128 (zeroBits f neg)⟩ := by
  rw [floatBits_roundRatio_eq f neg 0 d hd]; unfold roundRatioTiesToEven; simp [hd]
/-- **Exact-sum equivalence**: vendored `FloatBits.exactSum` agrees identically with `exactSumFloat` on all decoded `FloatKind` values with positive finite numerators/denominators. -/
theorem floatBits_exactSum_eq (f : IeeeFormat) (lk rk : FloatKind)
    (hl : ∀ neg n d, lk = .finite neg n d → 0 < n ∧ 0 < d) (hr : ∀ neg n d, rk = .finite neg n d → 0 < n ∧ 0 < d) :
    miriExactSum (ieeeFormatToMiri f) (floatKindToMiriDecoded f lk) (floatKindToMiriDecoded f rk) =
      .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128 (exactSumFloat f lk rk)⟩ := by
  have hzden_pos : 0 < (powScale 0 1 (f.minExponent - (f.fractionBits : Int))).2 :=
    Anneal.Mir.IeeeFloatCast.powScale_snd_pos 0 _
  have hzden_ne : (powScale 0 1 (f.minExponent - (f.fractionBits : Int))).2 ≠ 0 := Nat.ne_of_gt hzden_pos
  rw [miriExactSum_eq]
  cases lk with
  | nan _ _ _ => cases rk <;> simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, exactSumFloat, floatBits_preferredNaN_eq, pure, Except.pure]
  | inf ln =>
    cases rk with
    | nan _ _ _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, exactSumFloat, floatBits_preferredNaN_eq, pure, Except.pure]
    | inf rn => cases ln <;> cases rn <;> simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, exactSumFloat, floatBits_preferredNaN_eq, floatBits_infinity_eq, pure, Except.pure]
    | zero _ | finite _ _ _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, exactSumFloat, floatBits_infinity_eq, pure, Except.pure]
  | zero ln =>
    cases rk with
    | nan _ _ _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, exactSumFloat, floatBits_preferredNaN_eq, pure, Except.pure]
    | inf rn => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, exactSumFloat, floatBits_infinity_eq, pure, Except.pure]
    | zero rn =>
      dsimp only [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, exactSumFloat]
      have hl0 : miriSignedNumerator ln 0 = 0 := by cases ln <;> rfl
      have hr0 : miriSignedNumerator rn 0 = 0 := by cases rn <;> rfl
      rw [hl0, hr0]; simp only [Int.zero_mul, Int.add_zero, beq_self_eq_true, Bool.true_and, ↓reduceIte, Int.natAbs_zero]
      exact roundRatio_zero_eq_zeroBits f (ln && rn) _ (Nat.mul_ne_zero hzden_ne hzden_ne)
    | finite rn rnum rden =>
      obtain ⟨hrn_pos, hrd_pos⟩ := hr rn rnum rden rfl
      obtain ⟨hn_ne, hsign, habs⟩ := signedProd_nonzero_sign_abs rn rnum _ hrn_pos hzden_pos
      have hrn_ne : rnum ≠ 0 := Nat.ne_of_gt hrn_pos
      dsimp only [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, exactSumFloat]
      have hl0 : miriSignedNumerator ln 0 = 0 := by cases ln <;> rfl
      rw [hl0, Int.zero_mul, Int.zero_add, hn_ne]; simp only [Bool.false_eq_true, ↓reduceIte, hsign, habs, hrn_ne]
      rw [floatBits_roundRatio_eq f rn _ _ (Nat.mul_ne_zero hzden_ne (Nat.ne_of_gt hrd_pos)), Nat.mul_comm (powScale 0 1 (f.minExponent - (f.fractionBits : Int))).2 rden,
        roundRatioTiesToEven_mul_scale f rn rnum rden _ hzden_pos]
  | finite ln lnum lden =>
    obtain ⟨hln_pos, hld_pos⟩ := hl ln lnum lden rfl
    have hld_ne : lden ≠ 0 := Nat.ne_of_gt hld_pos
    cases rk with
    | nan _ _ _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, exactSumFloat, floatBits_preferredNaN_eq, pure, Except.pure]
    | inf rn => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, exactSumFloat, floatBits_infinity_eq, pure, Except.pure]
    | zero rn =>
      obtain ⟨hn_ne, hsign, habs⟩ := signedProd_nonzero_sign_abs ln lnum _ hln_pos hzden_pos
      have hln_ne : lnum ≠ 0 := Nat.ne_of_gt hln_pos
      dsimp only [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, exactSumFloat]
      have hr0 : miriSignedNumerator rn 0 = 0 := by cases rn <;> rfl
      rw [hr0, Int.zero_mul, Int.add_zero, hn_ne]; simp only [Bool.false_eq_true, ↓reduceIte, hsign, habs, hln_ne]
      rw [floatBits_roundRatio_eq f ln _ _ (Nat.mul_ne_zero hld_ne hzden_ne), roundRatioTiesToEven_mul_scale f ln lnum lden _ hzden_pos]
    | finite rn rnum rden =>
      obtain ⟨_, hrd_pos⟩ := hr rn rnum rden rfl
      dsimp only [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, exactSumFloat]
      rw [miriSignedNumerator_eq_signedNum, miriSignedNumerator_eq_signedNum]
      have hbeq : ∀ x : Int, (x == 0) = decide (x = 0) := fun x => by by_cases hx : x = 0 <;> simp [hx]
      rw [hbeq]
      have hsign_eq :
          (if decide (signedNum ln lnum * Int.ofNat rden + signedNum rn rnum * Int.ofNat lden = 0) = true then
              (lnum == 0) && (rnum == 0) && ln && rn
            else decide (signedNum ln lnum * Int.ofNat rden + signedNum rn rnum * Int.ofNat lden < 0)) =
          (if signedNum ln lnum * (rden : Int) + signedNum rn rnum * (lden : Int) = 0 then
              Bool.and (Nat.beq lnum 0) (Bool.and (Nat.beq rnum 0) (Bool.and ln rn))
            else decide (signedNum ln lnum * (rden : Int) + signedNum rn rnum * (lden : Int) < 0)) := by
        by_cases h0 : signedNum ln lnum * (rden : Int) + signedNum rn rnum * (lden : Int) = 0
        · simp only [Int.ofNat_eq_natCast, h0, decide_true, ↓reduceIte]
          have h1 : (lnum == 0) = Nat.beq lnum 0 := by cases lnum <;> rfl
          have h2 : (rnum == 0) = Nat.beq rnum 0 := by cases rnum <;> rfl
          rw [h1, h2]; cases Nat.beq lnum 0 <;> cases Nat.beq rnum 0 <;> cases ln <;> cases rn <;> rfl
        · simp only [Int.ofNat_eq_natCast, h0, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [hsign_eq, floatBits_roundRatio_eq f _ _ _ (Nat.mul_ne_zero hld_ne (Nat.ne_of_gt hrd_pos))]; rfl
/-- **Arithmetic equivalence**: across all canonical `f32`/`f64` bit pairs and every `BinOp`, `FloatBits.arithmetic (translateBinOp op)` agrees identically with `evalFloatArithBase` on `add`/`sub`/`mul`/`div`/`rem` and throws `.invalidBinaryOperator` otherwise. Note `.sub` maps directly to `FloatBits.arithmetic .Sub` *before* `adjustNaN`, preserving `nanChoices` order. -/
theorem floatBits_arithmetic_eq (op : MirAst.BinOp) (f : IeeeFormat) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    Miri.Interpreter.FloatBits.arithmetic (translateBinOp op)
        ⟨ieeeFormatToMiri f, BitVec.ofNat 128 a⟩ ⟨ieeeFormatToMiri f, BitVec.ofNat 128 b⟩ =
      match evalFloatArithBase op f a b with
      | .some bits => .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩
      | .none => .error (.invalidBinaryOperator (translateBinOp op)) := by
  have hzden_ne : (powScale 0 1 (f.minExponent - (f.fractionBits : Int))).2 ≠ 0 :=
    Nat.ne_of_gt (Anneal.Mir.IeeeFloatCast.powScale_snd_pos 0 _)
  have hl_pos : ∀ neg n d, decodeBits f a = .finite neg n d → 0 < n ∧ 0 < d := fun neg n d hk =>
    ⟨decodeBits_finite_num_pos f a neg n d hk, Anneal.Mir.IeeeFloatCast.decodeBits_finite_den_pos f a neg n d hk⟩
  have hr_pos : ∀ neg n d, decodeBits f b = .finite neg n d → 0 < n ∧ 0 < d := fun neg n d hk =>
    ⟨decodeBits_finite_num_pos f b neg n d hk, Anneal.Mir.IeeeFloatCast.decodeBits_finite_den_pos f b neg n d hk⟩
  unfold Miri.Interpreter.FloatBits.arithmetic evalFloatArithBase
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, floatBits_decode_eq f a ha,
    floatBits_decode_eq f b hb, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, bind, Except.bind, pure, Except.pure]
  cases op with
  | add => exact floatBits_exactSum_eq f (decodeBits f a) (decodeBits f b) hl_pos hr_pos
  | sub =>
    rw [← floatKindToMiriDecoded_negateFloatKind]
    refine floatBits_exactSum_eq f (decodeBits f a) (negateFloatKind (decodeBits f b)) hl_pos ?_
    intro neg n d hneg
    cases hdb : decodeBits f b with
    | finite rn _ _ => rw [hdb] at hneg; cases hneg; exact hr_pos rn n d hdb
    | _ => rw [hdb] at hneg; cases hneg
  | mul =>
    dsimp only [translateBinOp]
    cases hda : decodeBits f a with
    | nan _ _ _ => cases hdb : decodeBits f b <;> simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_preferredNaN_eq]
    | inf ln =>
      cases hdb : decodeBits f b with
      | nan _ _ _ | zero _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_preferredNaN_eq]
      | inf _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_infinity_eq]
      | finite rn rnum rden =>
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hr_pos rn rnum rden hdb).1)
        simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_infinity_eq]
    | zero ln =>
      cases hdb : decodeBits f b with
      | nan _ _ _ | inf _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_preferredNaN_eq]
      | zero _ => dsimp only [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri]; rw [Nat.zero_mul]; exact roundRatio_zero_eq_zeroBits f _ _ (Nat.mul_ne_zero hzden_ne hzden_ne)
      | finite rn rnum rden =>
        obtain ⟨_, hrd_pos⟩ := hr_pos rn rnum rden hdb
        dsimp only [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri]
        rw [Nat.zero_mul]; exact roundRatio_zero_eq_zeroBits f _ _ (Nat.mul_ne_zero hzden_ne (Nat.ne_of_gt hrd_pos))
    | finite ln lnum lden =>
      obtain ⟨hln_pos, hld_pos⟩ := hl_pos ln lnum lden hda
      cases hdb : decodeBits f b with
      | nan _ _ _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_preferredNaN_eq]
      | inf _ =>
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hln_pos)
        simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_infinity_eq]
      | zero _ => dsimp only [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri]; rw [Nat.mul_zero]; exact roundRatio_zero_eq_zeroBits f _ _ (Nat.mul_ne_zero (Nat.ne_of_gt hld_pos) hzden_ne)
      | finite rn rnum rden =>
        obtain ⟨_, hrd_pos⟩ := hr_pos rn rnum rden hdb
        dsimp only [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri]
        exact floatBits_roundRatio_eq f _ _ _ (Nat.mul_ne_zero (Nat.ne_of_gt hld_pos) (Nat.ne_of_gt hrd_pos))
  | div =>
    dsimp only [translateBinOp]
    cases hda : decodeBits f a with
    | nan _ _ _ => cases hdb : decodeBits f b <;> simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_preferredNaN_eq]
    | inf _ =>
      cases hdb : decodeBits f b with
      | nan _ _ _ | inf _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_preferredNaN_eq]
      | zero _ | finite _ _ _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_infinity_eq]
    | zero _ =>
      cases hdb : decodeBits f b with
      | nan _ _ _ | zero _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_preferredNaN_eq]
      | inf _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_zero_eq]
      | finite rn rnum rden =>
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hr_pos rn rnum rden hdb).1)
        dsimp only [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri]
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.zero_mul]
        exact roundRatio_zero_eq_zeroBits f _ _ (Nat.mul_ne_zero hzden_ne (Nat.succ_ne_zero k))
    | finite ln lnum lden =>
      obtain ⟨hln_pos, hld_pos⟩ := hl_pos ln lnum lden hda
      cases hdb : decodeBits f b with
      | nan _ _ _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_preferredNaN_eq]
      | inf _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_zero_eq]
      | zero _ =>
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hln_pos)
        simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_infinity_eq]
      | finite rn rnum rden =>
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hr_pos rn rnum rden hdb).1)
        dsimp only [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri]
        simp only [Nat.succ_ne_zero, ↓reduceIte]
        exact floatBits_roundRatio_eq f _ _ _ (Nat.mul_ne_zero (Nat.ne_of_gt hld_pos) (Nat.succ_ne_zero k))
  | rem =>
    dsimp only [translateBinOp]
    cases hda : decodeBits f a with
    | nan _ _ _ | inf _ => cases hdb : decodeBits f b <;> simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_preferredNaN_eq]
    | zero ln =>
      cases hdb : decodeBits f b with
      | nan _ _ _ | zero _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_preferredNaN_eq]
      | inf _ => rfl
      | finite rn rnum rden =>
        obtain ⟨hrn_pos, hrd_pos⟩ := hr_pos rn rnum rden hdb
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrn_pos)
        dsimp only [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri]
        simp only [Nat.zero_mul, Nat.zero_div, Nat.sub_zero, Nat.succ_ne_zero, ↓reduceIte]
        exact roundRatio_zero_eq_zeroBits f ln _ (Nat.mul_ne_zero hzden_ne (Nat.ne_of_gt hrd_pos))
    | finite ln lnum lden =>
      obtain ⟨_, hld_pos⟩ := hl_pos ln lnum lden hda
      cases hdb : decodeBits f b with
      | nan _ _ _ | zero _ => simp [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, floatBits_preferredNaN_eq]
      | inf _ => rfl
      | finite rn rnum rden =>
        obtain ⟨hrn_pos, hrd_pos⟩ := hr_pos rn rnum rden hdb
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrn_pos)
        dsimp only [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri]
        simp only [Nat.succ_ne_zero, ↓reduceIte]
        exact floatBits_roundRatio_eq f ln _ _ (Nat.mul_ne_zero (Nat.ne_of_gt hld_pos) (Nat.ne_of_gt hrd_pos))
  | _ => rfl
/-! ### 1.4 Ordered `FloatBits.nanChoices` correspondence (general list & binary) -/
private def nanCollectBody (target : Miri.Interpreter.FloatFormat) (input : Miri.Interpreter.FloatBits)
    (acc : List Miri.Interpreter.FloatBits × List Miri.Interpreter.FloatBits) :
    Except Miri.Interpreter.FloatError
      (ForInStep (List Miri.Interpreter.FloatBits × List Miri.Interpreter.FloatBits)) :=
  have quieted := acc.fst; have signaling := acc.snd
  do
    let __do_lift ← input.isNaN
    have __do_jp : Unit → List Miri.Interpreter.FloatBits →
        Except Miri.Interpreter.FloatError
          (ForInStep (List Miri.Interpreter.FloatBits × List Miri.Interpreter.FloatBits)) :=
      fun _ quieted => do
        let __do_lift ← input.isSignaling
        if __do_lift = true then do
          let converted ← input.convert target; let decoded ← converted.decode
          match decoded.value with
          | .nan payload =>
            have lower := payload % 2 ^ (target.fractionBits - 1)
            if (lower != 0) = true then
              have signaling := signaling ++ [miriEncode target decoded.negative (2 ^ target.exponentBits - 1) lower]
              pure (ForInStep.yield (quieted, signaling))
            else pure (ForInStep.yield (quieted, signaling))
          | _ => do throw Miri.Interpreter.FloatError.inconsistentRounding; pure (ForInStep.yield (quieted, signaling))
        else pure (ForInStep.yield (quieted, signaling))
    if __do_lift = true then do
      let __do_lift ← input.convert target
      have quieted : List Miri.Interpreter.FloatBits := quieted ++ [__do_lift]
      __do_jp () quieted
    else __do_jp () quieted
private def nanSignBody (candidate : Miri.Interpreter.FloatBits) (acc : List Miri.Interpreter.FloatBits) :
    Except Miri.Interpreter.FloatError (ForInStep (List Miri.Interpreter.FloatBits)) :=
  have signed := acc
  do
    let __do_lift ← candidate.negate
    have signed : List Miri.Interpreter.FloatBits := signed ++ [candidate, __do_lift]
    pure (ForInStep.yield signed)
private def miriNanQuietFn (dst : IeeeFormat) (fb : Miri.Interpreter.FloatBits) :
    Option Miri.Interpreter.FloatBits :=
  match miriFormatToIeee? fb.format with
  | some src =>
    if isNaNBits src fb.bits.toNat then
      some ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst fb.bits.toNat)⟩
    else none
  | none => none
private def miriNanSigFn (dst : IeeeFormat) (fb : Miri.Interpreter.FloatBits) :
    Option Miri.Interpreter.FloatBits :=
  match miriFormatToIeee? fb.format with
  | some src =>
    if isSignalingNaNBits src fb.bits.toNat then
      let conv := evalFloatToFloatRoundTiesToEven src dst fb.bits.toNat
      let c := unpackBits dst conv; let lower := c.fraction % 2 ^ (dst.fractionBits - 1)
      if lower = 0 then none
      else some ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (encodeBits dst c.neg (2 ^ dst.exponentBits - 1) lower)⟩
    else none
  | none => none
private theorem nanChoices_collect_eq (target : Miri.Interpreter.FloatFormat)
    (quietFn sigFn : Miri.Interpreter.FloatBits → Option Miri.Interpreter.FloatBits) (inputs accQ accS : List Miri.Interpreter.FloatBits)
    (hstep : ∀ x ∈ inputs, ∀ q s, nanCollectBody target x (q, s) =
      .ok (ForInStep.yield
        (match quietFn x with | none => q | some c => q ++ [c],
         match sigFn x with | none => s | some c => s ++ [c]))) :
    forIn (m := Except Miri.Interpreter.FloatError) inputs (accQ, accS) (nanCollectBody target) =
      .ok (accQ ++ inputs.filterMap quietFn, accS ++ inputs.filterMap sigFn) := by
  induction inputs generalizing accQ accS with
  | nil => simp [pure, Except.pure]
  | cons x xs ih =>
    rw [List.forIn_cons, hstep x List.mem_cons_self accQ accS]
    simp only [bind, Except.bind, List.filterMap_cons]
    cases quietFn x <;> cases sigFn x <;> dsimp only <;>
      rw [ih _ _ fun y hy => hstep y (List.mem_cons_of_mem _ hy)] <;> simp
private theorem nanChoices_sign_eq (negFn : Miri.Interpreter.FloatBits → Miri.Interpreter.FloatBits)
    (cands acc : List Miri.Interpreter.FloatBits) (hneg : ∀ c ∈ cands, c.negate = .ok (negFn c)) :
    forIn (m := Except Miri.Interpreter.FloatError) cands acc nanSignBody =
      .ok (acc ++ cands.flatMap fun c => [c, negFn c]) := by
  induction cands generalizing acc with
  | nil => simp [pure, Except.pure]
  | cons c cs ih =>
    have hstep : nanSignBody c acc = .ok (ForInStep.yield (acc ++ [c, negFn c])) := by
      unfold nanSignBody; simp [hneg c List.mem_cons_self, bind, Except.bind, pure, Except.pure]
    rw [List.forIn_cons, hstep]; simp only [bind, Except.bind, List.flatMap_cons]
    rw [ih (acc ++ [c, negFn c]) (fun y hy => hneg y (List.mem_cons_of_mem _ hy)), List.append_assoc]
private theorem miri_nanChoices_nondet_decomp (target : Miri.Interpreter.FloatFormat)
    (inputs : List Miri.Interpreter.FloatBits) (quietFn sigFn : Miri.Interpreter.FloatBits → Option Miri.Interpreter.FloatBits)
    (negFn : Miri.Interpreter.FloatBits → Miri.Interpreter.FloatBits) (hstep : ∀ x ∈ inputs, ∀ q s, nanCollectBody target x (q, s) =
      .ok (ForInStep.yield
        (match quietFn x with | none => q | some c => q ++ [c],
         match sigFn x with | none => s | some c => s ++ [c])))
    (hneg : ∀ c ∈ Miri.Interpreter.FloatBits.preferredNaN target ::
        (inputs.filterMap quietFn ++ inputs.filterMap sigFn), c.negate = .ok (negFn c)) :
    Miri.Interpreter.FloatBits.nanChoices target inputs true =
      .ok ((Miri.Interpreter.FloatBits.preferredNaN target ::
          (inputs.filterMap quietFn ++ inputs.filterMap sigFn)).flatMap fun c => [c, negFn c]) := by
  have h1 := nanChoices_collect_eq target quietFn sigFn inputs [] [] hstep
  have h2 := nanChoices_sign_eq negFn
    (Miri.Interpreter.FloatBits.preferredNaN target :: (inputs.filterMap quietFn ++ inputs.filterMap sigFn)) [] hneg
  simp only [List.nil_append] at h1 h2
  change (forIn (m := Except Miri.Interpreter.FloatError) inputs ([], []) (nanCollectBody target) >>=
    fun r =>
      let candidates := Miri.Interpreter.FloatBits.preferredNaN target :: (r.1 ++ r.2)
      forIn (m := Except Miri.Interpreter.FloatError) candidates [] nanSignBody >>=
        fun signed => pure signed) = _
  rw [h1]; simp only [bind, Except.bind]; rw [h2]; rfl
private theorem expandNanSigns_map_eq (dst : IeeeFormat) (cands : List Nat)
    (hcan : ∀ b ∈ cands, b < 2 ^ dst.width) : (cands.map fun b => (⟨ieeeFormatToMiri dst, BitVec.ofNat 128 b⟩ : Miri.Interpreter.FloatBits)).flatMap
        (fun c => [c, ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatNeg dst c.bits.toNat)⟩]) =
      (expandNanSigns dst cands).map fun b => (⟨ieeeFormatToMiri dst, BitVec.ofNat 128 b⟩ : Miri.Interpreter.FloatBits) := by
  induction cands with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.flatMap_cons, expandNanSigns, List.cons_append, List.nil_append, bitVec128_toNat_of_lt_width (hcan b List.mem_cons_self)]
    exact congrArg (fun rest => _ :: _ :: rest) (ih fun x hx => hcan x (List.mem_cons_of_mem _ hx))
private theorem nanChoicesQuieted_filterMap_eq (dst : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (hcan : ∀ p ∈ inputs, p.2 < 2 ^ p.1.width) : ((inputs.map fun p => (⟨ieeeFormatToMiri p.1, BitVec.ofNat 128 p.2⟩ : Miri.Interpreter.FloatBits)).filterMap
      (miriNanQuietFn dst)) =
      (nanChoicesQuieted dst inputs).map fun b => (⟨ieeeFormatToMiri dst, BitVec.ofNat 128 b⟩ : Miri.Interpreter.FloatBits) := by
  induction inputs with
  | nil => rfl
  | cons p ps ih =>
    have hp := hcan p List.mem_cons_self
    have hrest : ∀ q ∈ ps, q.2 < 2 ^ q.1.width := fun q hq => hcan q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, List.filterMap_cons, miriNanQuietFn, miriFormatToIeee?_ieeeFormatToMiri, bitVec128_toNat_of_lt_width hp, nanChoicesQuieted, Nat.mod_eq_of_lt hp]
    cases isNaNBits p.1 p.2 with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ih hrest
    | true => simp only [↓reduceIte, List.map_cons]; exact congrArg _ (ih hrest)
private theorem nanChoicesSignaling_filterMap_eq (dst : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (hcan : ∀ p ∈ inputs, p.2 < 2 ^ p.1.width) : ((inputs.map fun p => (⟨ieeeFormatToMiri p.1, BitVec.ofNat 128 p.2⟩ : Miri.Interpreter.FloatBits)).filterMap
      (miriNanSigFn dst)) =
      (nanChoicesSignaling dst inputs).map fun b => (⟨ieeeFormatToMiri dst, BitVec.ofNat 128 b⟩ : Miri.Interpreter.FloatBits) := by
  induction inputs with
  | nil => rfl
  | cons p ps ih =>
    have hp := hcan p List.mem_cons_self
    have hrest : ∀ q ∈ ps, q.2 < 2 ^ q.1.width := fun q hq => hcan q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, List.filterMap_cons, miriNanSigFn, miriFormatToIeee?_ieeeFormatToMiri, bitVec128_toNat_of_lt_width hp, nanChoicesSignaling, Nat.mod_eq_of_lt hp]
    cases isSignalingNaNBits p.1 p.2 with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ih hrest
    | true =>
      simp only [↓reduceIte]
      by_cases hlow : (unpackBits dst (evalFloatToFloatRoundTiesToEven p.1 dst p.2)).fraction % 2 ^ (dst.fractionBits - 1) = 0
      · simp only [hlow, ↓reduceIte]; exact ih hrest
      · simp only [hlow, ↓reduceIte, List.map_cons]; exact congrArg _ (ih hrest)
private theorem ieeeFormatToMiri_fractionBits (f : IeeeFormat) :
    (ieeeFormatToMiri f).fractionBits = f.fractionBits := by cases f <;> rfl
private theorem ieeeFormatToMiri_exponentBits (f : IeeeFormat) :
    (ieeeFormatToMiri f).exponentBits = f.exponentBits := by cases f <;> rfl
private theorem nanCollectBody_step_eq (dst src : IeeeFormat) (bits : Nat)
    (h : bits < 2 ^ src.width) (q s : List Miri.Interpreter.FloatBits) :
    let fb : Miri.Interpreter.FloatBits := ⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩
    nanCollectBody (ieeeFormatToMiri dst) fb (q, s) =
      .ok (ForInStep.yield
        (match miriNanQuietFn dst fb with | none => q | some c => q ++ [c],
         match miriNanSigFn dst fb with | none => s | some c => s ++ [c])) := by
  dsimp only; unfold nanCollectBody
  rw [floatBits_isNaN_eq src bits h, floatBits_isSignaling_eq src bits h]
  simp only [bind, Except.bind, pure, Except.pure, miriNanQuietFn, miriNanSigFn, miriFormatToIeee?_ieeeFormatToMiri, bitVec128_toNat_of_lt_width h]
  cases hdec : decodeBits src bits with
  | zero _ | finite _ _ _ | inf _ => simp [isNaNBits, isSignalingNaNBits, hdec]
  | nan neg qbit payload =>
    have hnan := Anneal.Mir.IeeeFloatCast.isNaNBits_of_nan src bits neg qbit payload hdec
    have hconv := floatBits_convert_eq src dst bits h
    have hdk := Anneal.Mir.IeeeFloatCast.decodeBits_evalFloatToFloatRoundTiesToEven_of_nan src dst bits neg qbit payload hdec
    have hdecc := floatBits_decode_eq dst _ (Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst bits)
    rw [hdk] at hdecc
    let payload' := Nat.lor
      (if src.fractionBits ≤ dst.fractionBits then
        Nat.lor payload (2 ^ (src.fractionBits - 1)) * 2 ^ (dst.fractionBits - src.fractionBits)
      else Nat.lor payload (2 ^ (src.fractionBits - 1)) / 2 ^ (src.fractionBits - dst.fractionBits))
      (2 ^ (dst.fractionBits - 1))
    change _ = Except.ok (floatKindToMiriDecoded dst (.nan neg true payload')) at hdecc
    have hunp : (unpackBits dst (evalFloatToFloatRoundTiesToEven src dst bits)).neg = neg ∧
        (unpackBits dst (evalFloatToFloatRoundTiesToEven src dst bits)).fraction = payload' := by
      unfold decodeBits at hdk; dsimp only at hdk
      by_cases h1 : (unpackBits dst (evalFloatToFloatRoundTiesToEven src dst bits)).exponent = 2 ^ dst.exponentBits - 1
      · simp only [h1, ↓reduceIte] at hdk
        by_cases h2 : (unpackBits dst (evalFloatToFloatRoundTiesToEven src dst bits)).fraction = 0
        · simp only [h2, ↓reduceIte] at hdk; cases hdk
        · simp only [h2, ↓reduceIte] at hdk; injection hdk with hn _ hf; exact ⟨hn, hf⟩
      · simp only [h1, ↓reduceIte] at hdk
        by_cases h2 : (unpackBits dst (evalFloatToFloatRoundTiesToEven src dst bits)).exponent = 0
        · simp only [h2, ↓reduceIte] at hdk
          by_cases h3 : (unpackBits dst (evalFloatToFloatRoundTiesToEven src dst bits)).fraction = 0 <;>
            simp only [h3, ↓reduceIte] at hdk <;> cases hdk
        · simp only [h2, ↓reduceIte] at hdk; cases hdk
    simp only [hnan, isSignalingNaNBits, hdec, ↓reduceIte, hconv]
    cases qbit with
    | true => simp
    | false =>
      simp only [Bool.not_false, ↓reduceIte, hdecc, floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri, ieeeFormatToMiri_fractionBits,
        ieeeFormatToMiri_exponentBits, miri_encode_eq, hunp.1, hunp.2]
      by_cases hlow : payload' % 2 ^ (dst.fractionBits - 1) = 0 <;> simp [hlow]
/-- **General ordered-list `nanChoices` equivalence**: for ANY list of canonical `(src, bits)` inputs and BOTH modes (`nondet = false` and `nondet = true`), `FloatBits.nanChoices` returns the exact ordered list of `Trusted`'s `nanChoices` candidates. -/
theorem floatBits_nanChoices_list_eq (dst : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (hcan : ∀ p ∈ inputs, p.2 < 2 ^ p.1.width) (nondet : Bool) :
    Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
        (inputs.map fun p => ⟨ieeeFormatToMiri p.1, BitVec.ofNat 128 p.2⟩) nondet =
      .ok ((nanChoices dst inputs (if nondet then .nondeterministic else .deterministic)).map
        fun b => ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 b⟩) := by
  cases nondet with
  | false => simp [floatBits_nanChoices_deterministic, nanChoices, floatBits_preferredNaN_eq]
  | true =>
    let negFn : Miri.Interpreter.FloatBits → Miri.Interpreter.FloatBits := fun fb =>
      ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatNeg dst fb.bits.toNat)⟩
    have hstep : ∀ x ∈ inputs.map (fun p => (⟨ieeeFormatToMiri p.1, BitVec.ofNat 128 p.2⟩ : Miri.Interpreter.FloatBits)),
        ∀ q s, nanCollectBody (ieeeFormatToMiri dst) x (q, s) =
          .ok (ForInStep.yield
            (match miriNanQuietFn dst x with | none => q | some c => q ++ [c],
             match miriNanSigFn dst x with | none => s | some c => s ++ [c])) := by
      intro x hx q s
      rcases List.mem_map.mp hx with ⟨p, hp_mem, rfl⟩
      exact nanCollectBody_step_eq dst p.1 p.2 (hcan p hp_mem) q s
    let rawCands := preferredNaNBits dst :: (nanChoicesQuieted dst inputs ++ nanChoicesSignaling dst inputs)
    have hraw_lt : ∀ b ∈ rawCands, b < 2 ^ dst.width := by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hrest
      · exact Anneal.Mir.IeeeFloatCast.preferredNaNBits_lt dst
      · rcases List.mem_append.mp hrest with hqm | hsm
        · exact (mem_nanChoicesQuieted_props dst inputs b hqm).1
        · exact (mem_nanChoicesSignaling_props dst inputs b hsm).1
    have hcands_eq :
        Miri.Interpreter.FloatBits.preferredNaN (ieeeFormatToMiri dst) ::
          ((inputs.map fun p => (⟨ieeeFormatToMiri p.1, BitVec.ofNat 128 p.2⟩ : Miri.Interpreter.FloatBits)).filterMap (miriNanQuietFn dst) ++
           (inputs.map fun p => (⟨ieeeFormatToMiri p.1, BitVec.ofNat 128 p.2⟩ : Miri.Interpreter.FloatBits)).filterMap (miriNanSigFn dst)) =
        rawCands.map fun b => (⟨ieeeFormatToMiri dst, BitVec.ofNat 128 b⟩ : Miri.Interpreter.FloatBits) := by
      rw [floatBits_preferredNaN_eq, nanChoicesQuieted_filterMap_eq dst inputs hcan, nanChoicesSignaling_filterMap_eq dst inputs hcan, List.map_cons, List.map_append]
    have hneg : ∀ c ∈ Miri.Interpreter.FloatBits.preferredNaN (ieeeFormatToMiri dst) ::
          ((inputs.map fun p => (⟨ieeeFormatToMiri p.1, BitVec.ofNat 128 p.2⟩ : Miri.Interpreter.FloatBits)).filterMap (miriNanQuietFn dst) ++
           (inputs.map fun p => (⟨ieeeFormatToMiri p.1, BitVec.ofNat 128 p.2⟩ : Miri.Interpreter.FloatBits)).filterMap (miriNanSigFn dst)),
        c.negate = .ok (negFn c) := by
      intro c hc; rw [hcands_eq] at hc
      rcases List.mem_map.mp hc with ⟨b, hb_mem, rfl⟩
      have hblt := hraw_lt b hb_mem
      simpa [negFn, bitVec128_toNat_of_lt_width hblt] using floatBits_negate_eq dst b hblt
    rw [miri_nanChoices_nondet_decomp (ieeeFormatToMiri dst) _ (miriNanQuietFn dst) (miriNanSigFn dst) negFn hstep hneg, hcands_eq, expandNanSigns_map_eq dst rawCands hraw_lt]
    rfl
/-- **Binary `FloatBits.nanChoices` ordered-list equivalence** (both modes, all canonical `(a, b)`). -/
theorem floatBits_nanChoices_binary_eq (f : IeeeFormat) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) (nondet : Bool) :
    Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri f)
        [⟨ieeeFormatToMiri f, BitVec.ofNat 128 a⟩, ⟨ieeeFormatToMiri f, BitVec.ofNat 128 b⟩] nondet =
      .ok ((nanChoices f [(f, a), (f, b)] (if nondet then .nondeterministic else .deterministic)).map
        fun bits => ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩) := by
  refine floatBits_nanChoices_list_eq f [(f, a), (f, b)] ?_ nondet
  intro p hp; rcases List.mem_cons.mp hp with rfl | hp'
  · exact ha
  · rcases List.mem_cons.mp hp' with rfl | hnil
    · exact hb
    · cases hnil
/-- **Binary `nanChoices` bitvector-projection equivalence** (`List.map FloatBits.bits`). -/
theorem floatBits_nanChoices_binary_bits_eq (f : IeeeFormat) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) (nondet : Bool) : (Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri f)
        [⟨ieeeFormatToMiri f, BitVec.ofNat 128 a⟩, ⟨ieeeFormatToMiri f, BitVec.ofNat 128 b⟩] nondet).map
        (List.map Miri.Interpreter.FloatBits.bits) =
      .ok ((nanChoices f [(f, a), (f, b)] (if nondet then .nondeterministic else .deterministic)).map
        (BitVec.ofNat 128)) := by
  rw [floatBits_nanChoices_binary_eq f a b ha hb nondet]; simp [Except.map, List.map_map]
/-- **Binary `nanChoices` `Nat`-projection equivalence** (`List.map (·.bits.toNat)`). -/
theorem floatBits_nanChoices_binary_toNat_eq (f : IeeeFormat) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) (nondet : Bool) : (Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri f)
        [⟨ieeeFormatToMiri f, BitVec.ofNat 128 a⟩, ⟨ieeeFormatToMiri f, BitVec.ofNat 128 b⟩] nondet).map
        (List.map fun fb => fb.bits.toNat) =
      .ok (nanChoices f [(f, a), (f, b)] (if nondet then .nondeterministic else .deterministic)) := by
  rw [floatBits_nanChoices_binary_eq f a b ha hb nondet]; simp only [Except.map, List.map_map]
  congr 1
  refine (List.map_congr_left (g := id) fun bits hmem => ?_).trans (List.map_id _)
  exact bitVec128_toNat_of_lt_width (mem_nanChoices_props f [(f, a), (f, b)] _ bits hmem).1
/-! ## Part 2. `Miri.Interpreter.FloatOps.{unary, binary}` & Conservative Step-Hook Overlay -/
/-- Valid state-preserving NaN selector for binary float arithmetic (`cs.length ≥ 2` holds unconditionally in nondeterministic mode by `nanChoices_length_bounds`). -/
def ValidBinaryChooseNaN
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) :
    Prop :=
  ∀ (st : AnnealStepState) (cs : List Miri.Interpreter.FloatBits),
    2 ≤ cs.length → ∃ idx < cs.length, chooseNaN () cs st = .ok idx st
theorem validBinaryChooseNaN_pure (i : Nat) (hi : i < 2) :
    ValidBinaryChooseNaN (fun _ _ => pure i) :=
  fun _ _ hlen => ⟨i, by omega, rfl⟩
/-- Default binary-arithmetic NaN selector, valid on EVERY nonempty candidate list: index `2` (the quieted first NaN input, agreeing with `annealChooseQuietedNaN` on every list of length `≥ 3`) when it exists, else index `0` (preferred NaN). -/
def annealChooseBinaryNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat :=
  fun _ cs => pure (if 2 < cs.length then 2 else 0)
theorem annealChooseBinaryNaN_valid : ValidBinaryChooseNaN annealChooseBinaryNaN :=
  fun _ cs hlen => ⟨if 2 < cs.length then 2 else 0, by split <;> omega, rfl⟩
/-- `annealChooseBinaryNaN` is valid on EVERY nonempty candidate list (`1 ≤ cs.length`, covering lengths `1, 2, 4, 6, 8`, ...): returns `2` when `2 < cs.length` and `0` otherwise. -/
theorem annealChooseBinaryNaN_valid_nonempty (st : AnnealStepState)
    (cs : List Miri.Interpreter.FloatBits) (hlen : 1 ≤ cs.length) :
    ∃ idx < cs.length, annealChooseBinaryNaN () cs st = .ok idx st ∧
      idx = (if 2 < cs.length then 2 else 0) :=
  ⟨if 2 < cs.length then 2 else 0, by split <;> omega, rfl, rfl⟩
/-- **Round-1 finding (repaired default)**: the float-cast refinement witness `annealChooseQuietedNaN` (`pure 2`) is NOT a valid binary selector. NaN-producing arithmetic on non-NaN operands (`∞ - ∞`, `0 * ∞`, `0 / 0`, `x % 0`) has exactly the two candidates `[pref, -pref]`, so index `2` makes `FloatOps.adjustNaN` throw `invalid floating NaN choice index` where `Trusted` succeeds; the `*FloatArith` overlays below therefore default to `annealChooseBinaryNaN`. -/
theorem annealChooseQuietedNaN_not_validBinary (st : AnnealStepState) (c : Miri.Interpreter.FloatBits) :
    ¬ ValidBinaryChooseNaN annealChooseQuietedNaN := by
  intro h
  obtain ⟨idx, hlt, hsel⟩ := h st [c, c] (Nat.le_refl 2)
  have h2 : (2 : Nat) = idx := by injection hsel
  have hlt' : idx < 2 := hlt
  omega
/-- **`FloatOps.unary` on `.Neg` correspondence**: agrees bit-for-bit with `evalFloatNeg` across all canonical `f32`/`f64` bit patterns with **zero NaN adjustment** (preserving sNaN/qNaN payloads). -/
theorem floatOps_unary_neg_eq (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {ty : Ty} {f : IeeeFormat} (hf : ieeeFormatOfTy? ty = some f)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) (hsz : sc.sizeBytes = f.byteWidth) :
    ∃ msc', ScalarRel ⟨evalFloatNeg f sc.bits, f.byteWidth⟩ msc' ∧
      Miri.Interpreter.FloatOps.unary (annealFloatOpsHooks nondet chooseNaN) () .Neg
          ⟨.scalar (.fromScalarInt msc), translateTy ty layouts⟩ =
        pure ⟨.scalar (.fromScalarInt msc'), translateTy ty layouts⟩ := by
  have hbits : sc.bits < 2 ^ f.width := by have := hrel.canonical; rwa [hsz, scalarModulus_byteWidth] at this
  obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec (validScalarBytes_byteWidth f)
    (caseVal := evalFloatNeg f sc.bits) (by rw [scalarModulus_byteWidth]; exact evalFloatNeg_lt f sc.bits)
  rw [translateSizeBytes_byteWidth] at hfrom; refine ⟨msc', hrel', ?_⟩
  have hT := translateTy_of_ieeeFormatOfTy? hf layouts
  have htoBits : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBits
      (ieeeFormatToMiri f).size = .ok (BitVec.ofNat 128 sc.bits) := by
    rw [← translateSizeBytes_byteWidth, ← hsz]; exact scalar_fromScalarInt_toBits_eq hrel
  unfold Miri.Interpreter.FloatOps.unary; rw [hT]
  simp only [Miri.Interpreter.Immediate.toScalar, Except.mapError, floatOps_liftResult_ok, pure_bind, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, floatOps_readScalarBits_unfold,
    annealFloatOpsHooks, floatFormatOfEncodedTyId_floatTyIdOf, floatLayoutData_size, htoBits,
    floatBits_negate_eq f sc.bits hbits, floatOps_engine_ok]
  rw [← hT]; exact floatOps_scalarResult_eq f hf layouts _ hfrom
/-- `FloatOps.unary` rejects non-`.Neg` unary operators with `.invalidProgram`. -/
theorem floatOps_unary_nonNeg_err (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {ty : Ty} {f : IeeeFormat} (hf : ieeeFormatOfTy? ty = some f)
    {op : Miri.MIR.UnOp} (hne : op ≠ .Neg) (msc : Miri.Memory.ScalarInt) (st : AnnealStepState) :
    Miri.Interpreter.FloatOps.unary (annealFloatOpsHooks nondet chooseNaN) () op
        ⟨.scalar (.fromScalarInt msc), translateTy ty layouts⟩ st =
      .error (.invalidProgram "invalid floating unary operation") st := by
  have hbne : (op != .Neg) = true := bne_iff_ne.mpr hne
  unfold Miri.Interpreter.FloatOps.unary; rw [translateTy_of_ieeeFormatOfTy? hf layouts]
  simp only [Miri.Interpreter.Immediate.toScalar, Except.mapError, floatOps_liftResult_ok, pure_bind, hbne, ↓reduceIte]; rfl
private theorem floatOps_adjustNaN_not_nan (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) (f : IeeeFormat) (baseBits : Nat) (hblt : baseBits < 2 ^ f.width)
    (hnan : isNaNBits f baseBits = false) (inputs : List Miri.Interpreter.FloatBits) :
    Miri.Interpreter.FloatOps.adjustNaN (annealFloatOpsHooks nondet chooseNaN) ()
        ⟨ieeeFormatToMiri f, BitVec.ofNat 128 baseBits⟩ inputs =
      pure ⟨ieeeFormatToMiri f, BitVec.ofNat 128 baseBits⟩ := by
  unfold Miri.Interpreter.FloatOps.adjustNaN
  simp [floatBits_isNaN_eq f baseBits hblt, hnan, floatOps_engine_ok, pure_bind]
private theorem floatOps_binary_arith_red (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {op : MirAst.BinOp} (harith : isFloatArithBinOp op = true)
    {lTy rTy : Ty} {f : IeeeFormat} (hlf : ieeeFormatOfTy? lTy = some f) (hrf : ieeeFormatOfTy? rTy = some f) {lSc rSc : MirAst.ScalarInt} {lMsc rMsc : Miri.Memory.ScalarInt}
    (hlrel : ScalarRel lSc lMsc) (hrrel : ScalarRel rSc rMsc) (hlsz : lSc.sizeBytes = f.byteWidth) (hrsz : rSc.sizeBytes = f.byteWidth)
    {baseBits : Nat} (hbase : evalFloatArithBase op f lSc.bits rSc.bits = .some baseBits) :
    Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks nondet chooseNaN) () (translateBinOp op)
        ⟨.scalar (.fromScalarInt lMsc), translateTy lTy layouts⟩
        ⟨.scalar (.fromScalarInt rMsc), translateTy rTy layouts⟩ =
      (do
        let result ← Miri.Interpreter.FloatOps.adjustNaN (annealFloatOpsHooks nondet chooseNaN) ()
          ⟨ieeeFormatToMiri f, BitVec.ofNat 128 baseBits⟩
          [⟨ieeeFormatToMiri f, BitVec.ofNat 128 lSc.bits⟩, ⟨ieeeFormatToMiri f, BitVec.ofNat 128 rSc.bits⟩]
        miriFloatOpsScalarResult result (translateTy lTy layouts)) := by
  have ha : lSc.bits < 2 ^ f.width := by have := hlrel.canonical; rwa [hlsz, scalarModulus_byteWidth] at this
  have hb : rSc.bits < 2 ^ f.width := by have := hrrel.canonical; rwa [hrsz, scalarModulus_byteWidth] at this
  have htoL : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) lMsc).toBits (ieeeFormatToMiri f).size =
      .ok (BitVec.ofNat 128 lSc.bits) := by rw [← translateSizeBytes_byteWidth, ← hlsz]; exact scalar_fromScalarInt_toBits_eq hlrel
  have htoR : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) rMsc).toBits (ieeeFormatToMiri f).size =
      .ok (BitVec.ofNat 128 rSc.bits) := by rw [← translateSizeBytes_byteWidth, ← hrsz]; exact scalar_fromScalarInt_toBits_eq hrrel
  have har := floatBits_arithmetic_eq op f lSc.bits rSc.bits ha hb; rw [hbase] at har
  have hL := translateTy_of_ieeeFormatOfTy? hlf layouts
  have hR := translateTy_of_ieeeFormatOfTy? hrf layouts
  unfold Miri.Interpreter.FloatOps.binary; rw [hL, hR]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Miri.Interpreter.Immediate.toScalar, Except.mapError, floatOps_liftResult_ok, pure_bind, floatOps_readScalarBits_unfold,
    annealFloatOpsHooks, floatFormatOfEncodedTyId_floatTyIdOf, floatLayoutData_size, htoL, htoR]
  cases op <;> simp only [isFloatArithBinOp] at harith <;> try cases harith
  all_goals simp only [translateBinOp] at har ⊢; simp only [har, floatOps_engine_ok, pure_bind]
/-- **`FloatOps.binary` comparison correspondence** (`Eq`, `Ne`, `Lt`, `Le`, `Gt`, `Ge`): produces `Scalar.fromBool` matching `evalFloatCmp`, independently of `nondet` and `chooseNaN`. -/
theorem floatOps_binary_cmp_eq (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {op : MirAst.BinOp} (hcmp : isFloatCmpBinOp op = true)
    {lTy rTy : Ty} {f : IeeeFormat} (hlf : ieeeFormatOfTy? lTy = some f) (hrf : ieeeFormatOfTy? rTy = some f) {lSc rSc : MirAst.ScalarInt} {lMsc rMsc : Miri.Memory.ScalarInt}
    (hlrel : ScalarRel lSc lMsc) (hrrel : ScalarRel rSc rMsc) (hlsz : lSc.sizeBytes = f.byteWidth) (hrsz : rSc.sizeBytes = f.byteWidth) :
    ∃ res, evalFloatCmp op f lSc.bits rSc.bits = .some res ∧
      ScalarRel (boolToScalar res) (Miri.Memory.ScalarInt.ofBool res) ∧
      Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks nondet chooseNaN) () (translateBinOp op)
          ⟨.scalar (.fromScalarInt lMsc), translateTy lTy layouts⟩
          ⟨.scalar (.fromScalarInt rMsc), translateTy rTy layouts⟩ =
        pure ⟨.scalar (.fromBool res), translateTy { kind := .bool, layoutIdx := 0 }⟩ := by
  obtain ⟨res, hres⟩ := (evalFloatCmp_isSome_iff op f lSc.bits rSc.bits).mpr hcmp
  have ha : lSc.bits < 2 ^ f.width := by have := hlrel.canonical; rwa [hlsz, scalarModulus_byteWidth] at this
  have hb : rSc.bits < 2 ^ f.width := by have := hrrel.canonical; rwa [hrsz, scalarModulus_byteWidth] at this
  have htoL : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) lMsc).toBits (ieeeFormatToMiri f).size =
      .ok (BitVec.ofNat 128 lSc.bits) := by rw [← translateSizeBytes_byteWidth, ← hlsz]; exact scalar_fromScalarInt_toBits_eq hlrel
  have htoR : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) rMsc).toBits (ieeeFormatToMiri f).size =
      .ok (BitVec.ofNat 128 rSc.bits) := by rw [← translateSizeBytes_byteWidth, ← hrsz]; exact scalar_fromScalarInt_toBits_eq hrrel
  have hcomp := floatBits_comparison_eq op f lSc.bits rSc.bits ha hb; rw [hres] at hcomp
  refine ⟨res, hres, ScalarRel.of_boolToScalar res, ?_⟩
  unfold Miri.Interpreter.FloatOps.binary
  rw [translateTy_of_ieeeFormatOfTy? hlf layouts, translateTy_of_ieeeFormatOfTy? hrf layouts]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Miri.Interpreter.Immediate.toScalar, Except.mapError, floatOps_liftResult_ok, pure_bind, floatOps_readScalarBits_unfold,
    annealFloatOpsHooks, floatFormatOfEncodedTyId_floatTyIdOf, floatLayoutData_size, htoL, htoR]
  cases op <;> simp only [isFloatCmpBinOp] at hcmp <;> try cases hcmp
  all_goals simp only [translateBinOp] at hcomp ⊢; simp only [hcomp, floatOps_engine_ok, pure_bind]
/-- **`FloatOps.binary` deterministic arithmetic correspondence** (`floatNondeterministic := false`): matches `evalFloatBinOp` (`evalFloatArithBase`) bit-for-bit across `add`/`sub`/`mul`/`div`/`rem`. -/
theorem floatOps_binary_arith_deterministic_eq (layouts : LayoutTable)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {op : MirAst.BinOp} (harith : isFloatArithBinOp op = true)
    {lTy rTy : Ty} {f : IeeeFormat} (hlf : ieeeFormatOfTy? lTy = some f) (hrf : ieeeFormatOfTy? rTy = some f) {lSc rSc : MirAst.ScalarInt} {lMsc rMsc : Miri.Memory.ScalarInt}
    (hlrel : ScalarRel lSc lMsc) (hrrel : ScalarRel rSc rMsc) (hlsz : lSc.sizeBytes = f.byteWidth) (hrsz : rSc.sizeBytes = f.byteWidth) :
    ∃ baseBits msc',
      evalFloatArithBase op f lSc.bits rSc.bits = .some baseBits ∧
      evalFloatBinOp op f lSc.bits rSc.bits = .some ⟨baseBits, f.byteWidth⟩ ∧
      ScalarRel ⟨baseBits, f.byteWidth⟩ msc' ∧
      Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks false chooseNaN) () (translateBinOp op)
          ⟨.scalar (.fromScalarInt lMsc), translateTy lTy layouts⟩
          ⟨.scalar (.fromScalarInt rMsc), translateTy rTy layouts⟩ =
        pure ⟨.scalar (.fromScalarInt msc'), translateTy lTy layouts⟩ := by
  obtain ⟨baseBits, hbase⟩ := (evalFloatArithBase_isSome_iff op f lSc.bits rSc.bits).mpr harith
  have hbin : evalFloatBinOp op f lSc.bits rSc.bits = .some ⟨baseBits, f.byteWidth⟩ := by
    unfold evalFloatBinOp; rw [evalFloatCmp_of_arith op f lSc.bits rSc.bits harith, hbase]
  have hblt := evalFloatArithBase_lt op f lSc.bits rSc.bits baseBits hbase
  obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec (validScalarBytes_byteWidth f)
    (caseVal := baseBits) (by rw [scalarModulus_byteWidth]; exact hblt)
  rw [translateSizeBytes_byteWidth] at hfrom; refine ⟨baseBits, msc', hbase, hbin, hrel', ?_⟩
  rw [floatOps_binary_arith_red layouts false chooseNaN harith hlf hrf hlrel hrrel hlsz hrsz hbase]
  have hadj : Miri.Interpreter.FloatOps.adjustNaN (annealFloatOpsHooks false chooseNaN) ()
      ⟨ieeeFormatToMiri f, BitVec.ofNat 128 baseBits⟩
      [⟨ieeeFormatToMiri f, BitVec.ofNat 128 lSc.bits⟩, ⟨ieeeFormatToMiri f, BitVec.ofNat 128 rSc.bits⟩] =
      pure ⟨ieeeFormatToMiri f, BitVec.ofNat 128 baseBits⟩ := by
    cases hnan : isNaNBits f baseBits with
    | false => exact floatOps_adjustNaN_not_nan false chooseNaN f baseBits hblt hnan _
    | true =>
      have hpref := evalFloatArithBase_nan_eq_preferred op f lSc.bits rSc.bits baseBits hbase hnan
      unfold Miri.Interpreter.FloatOps.adjustNaN
      rw [floatBits_isNaN_eq f baseBits hblt, hnan]
      simp only [floatOps_engine_ok, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, annealFloatOpsHooks, floatBits_nanChoices_deterministic, Bool.not_false]
      rw [floatBits_preferredNaN_eq, hpref]
  rw [hadj, pure_bind, floatOps_scalarResult_eq f hlf layouts baseBits hfrom]
/-- **Nondeterministic `FloatOps.binary` SOUNDNESS**: for ANY valid state-preserving `chooseNaN` selector, `FloatOps.binary` (`floatNondeterministic := true`) produces an `outSc` satisfying `EvalFloatBinOpRel .nondeterministic op f lSc.bits rSc.bits outSc`. -/
theorem floatOps_binary_arith_any_chooseNaN_rel (layouts : LayoutTable)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hvalid : ValidBinaryChooseNaN chooseNaN) {op : MirAst.BinOp} (harith : isFloatArithBinOp op = true)
    {lTy rTy : Ty} {f : IeeeFormat} (hlf : ieeeFormatOfTy? lTy = some f) (hrf : ieeeFormatOfTy? rTy = some f) {lSc rSc : MirAst.ScalarInt} {lMsc rMsc : Miri.Memory.ScalarInt}
    (hlrel : ScalarRel lSc lMsc) (hrrel : ScalarRel rSc rMsc) (hlsz : lSc.sizeBytes = f.byteWidth) (hrsz : rSc.sizeBytes = f.byteWidth) (st : AnnealStepState) :
    ∃ outSc msc', EvalFloatBinOpRel .nondeterministic op f lSc.bits rSc.bits outSc ∧ ScalarRel outSc msc' ∧
      Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks true chooseNaN) () (translateBinOp op)
          ⟨.scalar (.fromScalarInt lMsc), translateTy lTy layouts⟩
          ⟨.scalar (.fromScalarInt rMsc), translateTy rTy layouts⟩ st =
        .ok ⟨.scalar (.fromScalarInt msc'), translateTy lTy layouts⟩ st := by
  obtain ⟨baseBits, hbase⟩ := (evalFloatArithBase_isSome_iff op f lSc.bits rSc.bits).mpr harith
  have ha : lSc.bits < 2 ^ f.width := by have := hlrel.canonical; rwa [hlsz, scalarModulus_byteWidth] at this
  have hb : rSc.bits < 2 ^ f.width := by have := hrrel.canonical; rwa [hrsz, scalarModulus_byteWidth] at this
  have hblt := evalFloatArithBase_lt op f lSc.bits rSc.bits baseBits hbase
  have hbin_red := floatOps_binary_arith_red layouts true chooseNaN harith hlf hrf hlrel hrrel hlsz hrsz hbase
  cases hnan : isNaNBits f baseBits with
  | false =>
    obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec (validScalarBytes_byteWidth f)
      (caseVal := baseBits) (by rw [scalarModulus_byteWidth]; exact hblt)
    rw [translateSizeBytes_byteWidth] at hfrom
    refine ⟨⟨baseBits, f.byteWidth⟩, msc',
      (EvalFloatBinOpRel_arith_iff .nondeterministic op f lSc.bits rSc.bits _ harith).mpr
        ⟨baseBits, hbase, Or.inr ⟨hnan, rfl⟩⟩, hrel', ?_⟩
    rw [hbin_red, floatOps_adjustNaN_not_nan true chooseNaN f baseBits hblt hnan, pure_bind, floatOps_scalarResult_eq f hlf layouts baseBits hfrom]; rfl
  | true =>
    let nc := nanChoices f [(f, lSc.bits), (f, rSc.bits)] .nondeterministic
    let cs : List Miri.Interpreter.FloatBits := nc.map fun bits => ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩
    have hcs_eq := floatBits_nanChoices_binary_eq f lSc.bits rSc.bits ha hb true
    simp only [↓reduceIte] at hcs_eq
    have hlen : 2 ≤ cs.length := by
      simp only [cs, List.length_map]; exact (nanChoices_length_bounds f [(f, lSc.bits), (f, rSc.bits)]).2
    obtain ⟨idx, hidx_lt, hsel⟩ := hvalid st cs hlen
    have hidx_nc : idx < nc.length := by simpa [cs] using hidx_lt
    let candBits : Nat := nc[idx]'hidx_nc
    have hcand_mem : candBits ∈ nc := List.getElem_mem hidx_nc
    have hcand_lt := (mem_nanChoices_props f [(f, lSc.bits), (f, rSc.bits)] .nondeterministic candBits hcand_mem).1
    obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec (validScalarBytes_byteWidth f)
      (caseVal := candBits) (by rw [scalarModulus_byteWidth]; exact hcand_lt)
    rw [translateSizeBytes_byteWidth] at hfrom
    have hget : cs[idx]? = some ⟨ieeeFormatToMiri f, BitVec.ofNat 128 candBits⟩ := by
      simp [cs, List.getElem?_map, List.getElem?_eq_getElem hidx_nc, candBits]
    have hadj_fn : Miri.Interpreter.FloatOps.adjustNaN (annealFloatOpsHooks true chooseNaN) ()
        ⟨ieeeFormatToMiri f, BitVec.ofNat 128 baseBits⟩
        [⟨ieeeFormatToMiri f, BitVec.ofNat 128 lSc.bits⟩, ⟨ieeeFormatToMiri f, BitVec.ofNat 128 rSc.bits⟩] =
        (chooseNaN () cs >>= fun index => match cs[index]? with
          | some chosen => pure chosen
          | none => throw (.invalidProgram "invalid floating NaN choice index")) := by
      unfold Miri.Interpreter.FloatOps.adjustNaN
      simp only [floatBits_isNaN_eq f baseBits hblt, hnan, annealFloatOpsHooks, hcs_eq, floatOps_engine_ok, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      congr 1; funext index; cases cs[index]? <;> rfl
    have hadj_st : Miri.Interpreter.FloatOps.adjustNaN (annealFloatOpsHooks true chooseNaN) ()
        ⟨ieeeFormatToMiri f, BitVec.ofNat 128 baseBits⟩
        [⟨ieeeFormatToMiri f, BitVec.ofNat 128 lSc.bits⟩, ⟨ieeeFormatToMiri f, BitVec.ofNat 128 rSc.bits⟩] st =
        .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128 candBits⟩ st := by
      rw [congrFun hadj_fn st, EStateM.bind_eq_ok hsel, hget]; rfl
    refine ⟨⟨candBits, f.byteWidth⟩, msc',
      (EvalFloatBinOpRel_arith_iff .nondeterministic op f lSc.bits rSc.bits _ harith).mpr
        ⟨baseBits, hbase, Or.inl ⟨hnan, candBits, hcand_mem, rfl⟩⟩, hrel', ?_⟩
    rw [congrFun hbin_red st, EStateM.bind_eq_ok hadj_st, congrFun (floatOps_scalarResult_eq f hlf layouts candBits hfrom) st]; rfl
/-- **Index-exact nondeterministic `FloatOps.binary` correspondence** (sharpens completeness): under the constant selector `fun _ _ => pure idx`, `FloatOps.binary` returns EXACTLY the `idx`-th element of `Trusted`'s ordered `nanChoices f [(f, lhs), (f, rhs)]` when the base result is NaN, and `baseBits` for EVERY `idx` otherwise. For `.sub` the list is built from the ORIGINAL (un-negated) rhs in BOTH authorities (`miri#5643`): vendored `FloatOps.binary` passes `[leftBits, rightBits]` to `adjustNaN` for all five arithmetic operators. -/
theorem floatOps_binary_arith_pure_index_exact (layouts : LayoutTable) (idx : Nat)
    {op : MirAst.BinOp} (harith : isFloatArithBinOp op = true) {lTy rTy : Ty} {f : IeeeFormat} (hlf : ieeeFormatOfTy? lTy = some f) (hrf : ieeeFormatOfTy? rTy = some f)
    {lSc rSc : MirAst.ScalarInt} {lMsc rMsc : Miri.Memory.ScalarInt} (hlrel : ScalarRel lSc lMsc) (hrrel : ScalarRel rSc rMsc)
    (hlsz : lSc.sizeBytes = f.byteWidth) (hrsz : rSc.sizeBytes = f.byteWidth) {baseBits outBits : Nat} (hbase : evalFloatArithBase op f lSc.bits rSc.bits = .some baseBits)
    (hsel : (isNaNBits f baseBits = true ∧ (nanChoices f [(f, lSc.bits), (f, rSc.bits)] .nondeterministic)[idx]? = some outBits) ∨
      (isNaNBits f baseBits = false ∧ outBits = baseBits)) :
    ∃ msc', ScalarRel ⟨outBits, f.byteWidth⟩ msc' ∧
      Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks true (fun _ _ => pure idx)) () (translateBinOp op)
          ⟨.scalar (.fromScalarInt lMsc), translateTy lTy layouts⟩
          ⟨.scalar (.fromScalarInt rMsc), translateTy rTy layouts⟩ =
        pure ⟨.scalar (.fromScalarInt msc'), translateTy lTy layouts⟩ := by
  have ha : lSc.bits < 2 ^ f.width := by have := hlrel.canonical; rwa [hlsz, scalarModulus_byteWidth] at this
  have hb : rSc.bits < 2 ^ f.width := by have := hrrel.canonical; rwa [hrsz, scalarModulus_byteWidth] at this
  have hblt := evalFloatArithBase_lt op f lSc.bits rSc.bits baseBits hbase
  rcases hsel with ⟨hnan, hcand⟩ | ⟨hnan, hout⟩
  · have hcand_lt := (mem_nanChoices_props f [(f, lSc.bits), (f, rSc.bits)] .nondeterministic outBits (List.mem_of_getElem? hcand)).1
    obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec (validScalarBytes_byteWidth f)
      (caseVal := outBits) (by rw [scalarModulus_byteWidth]; exact hcand_lt)
    rw [translateSizeBytes_byteWidth] at hfrom
    have hcs_eq := floatBits_nanChoices_binary_eq f lSc.bits rSc.bits ha hb true
    simp only [↓reduceIte] at hcs_eq
    have hget : ((nanChoices f [(f, lSc.bits), (f, rSc.bits)] .nondeterministic).map
        fun bits => (⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩ : Miri.Interpreter.FloatBits))[idx]? =
        some ⟨ieeeFormatToMiri f, BitVec.ofNat 128 outBits⟩ := by
      simp [List.getElem?_map, hcand]
    refine ⟨msc', hrel', ?_⟩
    rw [floatOps_binary_arith_red layouts true (fun _ _ => pure idx) harith hlf hrf hlrel hrrel hlsz hrsz hbase]
    have hadj : Miri.Interpreter.FloatOps.adjustNaN (annealFloatOpsHooks true (fun _ _ => pure idx)) ()
        ⟨ieeeFormatToMiri f, BitVec.ofNat 128 baseBits⟩
        [⟨ieeeFormatToMiri f, BitVec.ofNat 128 lSc.bits⟩, ⟨ieeeFormatToMiri f, BitVec.ofNat 128 rSc.bits⟩] =
        pure ⟨ieeeFormatToMiri f, BitVec.ofNat 128 outBits⟩ := by
      unfold Miri.Interpreter.FloatOps.adjustNaN
      simp only [floatBits_isNaN_eq f baseBits hblt, hnan, annealFloatOpsHooks, hcs_eq, floatOps_engine_ok, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hget]
    rw [hadj, pure_bind, floatOps_scalarResult_eq f hlf layouts outBits hfrom]
  · rw [hout]
    obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec (validScalarBytes_byteWidth f)
      (caseVal := baseBits) (by rw [scalarModulus_byteWidth]; exact hblt)
    rw [translateSizeBytes_byteWidth] at hfrom; refine ⟨msc', hrel', ?_⟩
    rw [floatOps_binary_arith_red layouts true (fun _ _ => pure idx) harith hlf hrf hlrel hrrel hlsz hrsz hbase, floatOps_adjustNaN_not_nan true (fun _ _ => pure idx) f baseBits hblt hnan,
      pure_bind, floatOps_scalarResult_eq f hlf layouts baseBits hfrom]
/-- **Nondeterministic `FloatOps.binary` COMPLETENESS (converse of soundness)**: for EVERY `outSc` admitted by `EvalFloatBinOpRel .nondeterministic`, there EXISTS a constant index `idx` such that `chooseNaN := fun _ _ => pure idx` makes `FloatOps.binary` return a `ScalarRel`-related `msc'` (corollary of `floatOps_binary_arith_pure_index_exact`). -/
theorem floatOps_binary_arith_completeness (layouts : LayoutTable)
    {op : MirAst.BinOp} (harith : isFloatArithBinOp op = true) {lTy rTy : Ty} {f : IeeeFormat} (hlf : ieeeFormatOfTy? lTy = some f) (hrf : ieeeFormatOfTy? rTy = some f)
    {lSc rSc : MirAst.ScalarInt} {lMsc rMsc : Miri.Memory.ScalarInt} (hlrel : ScalarRel lSc lMsc) (hrrel : ScalarRel rSc rMsc)
    (hlsz : lSc.sizeBytes = f.byteWidth) (hrsz : rSc.sizeBytes = f.byteWidth) {outSc : MirAst.ScalarInt} (hout : EvalFloatBinOpRel .nondeterministic op f lSc.bits rSc.bits outSc) :
    ∃ idx msc', ScalarRel outSc msc' ∧
      Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks true (fun _ _ => pure idx)) () (translateBinOp op)
          ⟨.scalar (.fromScalarInt lMsc), translateTy lTy layouts⟩
          ⟨.scalar (.fromScalarInt rMsc), translateTy rTy layouts⟩ =
        pure ⟨.scalar (.fromScalarInt msc'), translateTy lTy layouts⟩ := by
  obtain ⟨baseBits, hbase, hcase⟩ :=
    (EvalFloatBinOpRel_arith_iff .nondeterministic op f lSc.bits rSc.bits outSc harith).mp hout
  rcases hcase with ⟨hnan, cand, hcand_mem, rfl⟩ | ⟨hnan, rfl⟩
  · obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hcand_mem
    obtain ⟨msc', hrel', h⟩ := floatOps_binary_arith_pure_index_exact layouts idx harith hlf hrf hlrel hrrel hlsz hrsz
      (outBits := cand) hbase (Or.inl ⟨hnan, by rw [List.getElem?_eq_getElem hidx_lt, hidx_eq]⟩)
    exact ⟨idx, msc', hrel', h⟩
  · obtain ⟨msc', hrel', h⟩ := floatOps_binary_arith_pure_index_exact layouts 0 harith hlf hrf hlrel hrrel hlsz hrsz
      (outBits := baseBits) hbase (Or.inr ⟨hnan, rfl⟩)
    exact ⟨0, msc', hrel', h⟩
/-- `FloatOps.binary` rejects every non-float `BinOp` (`bitXor`, `shl`, `cmp`, etc.) with `.invalidProgram`, matching `Trusted`'s `evalFloatBinOp = .none`. -/
theorem floatOps_binary_unsupported_err (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {op : MirAst.BinOp} (hnot : isFloatBinOp op = false)
    {lTy rTy : Ty} {f : IeeeFormat} (hlf : ieeeFormatOfTy? lTy = some f) (hrf : ieeeFormatOfTy? rTy = some f) {lSc rSc : MirAst.ScalarInt} {lMsc rMsc : Miri.Memory.ScalarInt}
    (hlrel : ScalarRel lSc lMsc) (hrrel : ScalarRel rSc rMsc) (hlsz : lSc.sizeBytes = f.byteWidth) (hrsz : rSc.sizeBytes = f.byteWidth) (st : AnnealStepState) :
    Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks nondet chooseNaN) () (translateBinOp op)
        ⟨.scalar (.fromScalarInt lMsc), translateTy lTy layouts⟩
        ⟨.scalar (.fromScalarInt rMsc), translateTy rTy layouts⟩ st =
      .error (.invalidProgram "invalid floating binary operation") st := by
  have htoL : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) lMsc).toBits (ieeeFormatToMiri f).size =
      .ok (BitVec.ofNat 128 lSc.bits) := by rw [← translateSizeBytes_byteWidth, ← hlsz]; exact scalar_fromScalarInt_toBits_eq hlrel
  have htoR : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) rMsc).toBits (ieeeFormatToMiri f).size =
      .ok (BitVec.ofNat 128 rSc.bits) := by rw [← translateSizeBytes_byteWidth, ← hrsz]; exact scalar_fromScalarInt_toBits_eq hrrel
  unfold Miri.Interpreter.FloatOps.binary
  rw [translateTy_of_ieeeFormatOfTy? hlf layouts, translateTy_of_ieeeFormatOfTy? hrf layouts]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Miri.Interpreter.Immediate.toScalar, Except.mapError, floatOps_liftResult_ok, pure_bind, floatOps_readScalarBits_unfold,
    annealFloatOpsHooks, floatFormatOfEncodedTyId_floatTyIdOf, floatLayoutData_size, htoL, htoR]
  cases op <;> simp only [isFloatBinOp] at hnot <;> try cases hnot
  all_goals rfl
/-- `f16` (`TyId = 30`) and `f128` (`TyId = 33`) fail closed with the exact `StepError.unsupported` message in `FloatOps.unary` and `FloatOps.binary`, matching `ieeeFormatOfTy? = none`. -/
theorem floatOps_f16_f128_unsupported (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {ty : Ty} (h16 : ty.kind = .float .f16 ∨ ty.kind = .float .f128)
    (msc₁ msc₂ : Miri.Memory.ScalarInt) (op : Miri.MIR.BinOp) (st : AnnealStepState) :
    Miri.Interpreter.FloatOps.unary (annealFloatOpsHooks nondet chooseNaN) () .Neg
        ⟨.scalar (.fromScalarInt msc₁), translateTy ty layouts⟩ st =
      .error (.unsupported s!"floatOps.formatOf: TyId {encodeTyId ty} is not f32/f64") st ∧
    Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks nondet chooseNaN) () op
        ⟨.scalar (.fromScalarInt msc₁), translateTy ty layouts⟩
        ⟨.scalar (.fromScalarInt msc₂), translateTy ty layouts⟩ st =
      .error (.unsupported s!"floatOps.formatOf: TyId {encodeTyId ty} is not f32/f64") st := by
  have htyId : (translateTy ty layouts).ty = 30 ∨ (translateTy ty layouts).ty = 33 := by
    rcases h16 with hk | hk
    · left; unfold translateTy encodeTyId; dsimp only; rw [hk]
    · right; unfold translateTy encodeTyId; dsimp only; rw [hk]
  let msg := s!"floatOps.formatOf: TyId {(translateTy ty layouts).ty} is not f32/f64"
  have hfmt : (annealFloatOpsHooks nondet chooseNaN).formatOf () (translateTy ty layouts).ty = throw (.unsupported msg) := by
    have hraw : floatFormatOfEncodedTyId (translateTy ty layouts).ty = .error (.unsupported msg) := by
      rcases htyId with h | h <;> simp only [msg, h] <;> rfl
    simp only [annealFloatOpsHooks, hraw]
  have hrb : ∀ (v : Miri.Interpreter.RvalueImmTy AnnealProv) (sc : Miri.Memory.Scalar AnnealProv),
      v.layout = translateTy ty layouts →
      (miriReadScalarBits (annealFloatOpsHooks nondet chooseNaN) () v sc :
        Miri.Interpreter.RvalueM AnnealStepState Miri.Interpreter.FloatBits) = throw (.unsupported msg) := by
    intro v sc hv
    change (do
      let format ← (annealFloatOpsHooks nondet chooseNaN).formatOf () v.layout.ty
      if v.layout.layout.size != format.size then throw (Miri.Interpreter.StepError.invalidProgram "float operand layout size mismatch")
      let bits ← miriFloatOpsLiftResult (sc.toBits format.size |>.mapError Miri.Interpreter.ScalarOps.scalarError)
      return (⟨format, bits⟩ : Miri.Interpreter.FloatBits)) =
      (throw (Miri.Interpreter.StepError.unsupported msg) : Miri.Interpreter.RvalueM AnnealStepState Miri.Interpreter.FloatBits)
    rw [hv, hfmt]; rfl
  constructor
  · unfold Miri.Interpreter.FloatOps.unary
    simp only [Miri.Interpreter.Immediate.toScalar, Except.mapError, floatOps_liftResult_ok, pure_bind, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]; rw [hrb _ _ rfl]; rfl
  · unfold Miri.Interpreter.FloatOps.binary
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Miri.Interpreter.Immediate.toScalar, Except.mapError, floatOps_liftResult_ok, pure_bind]; rw [hrb _ _ rfl]; rfl
/-! ### 2.1 Conservative `ScalarOpsHooks` / `RvalueHooks` / `StepHooks` Overlay -/
/-- `ScalarOpsHooks` overlay over `annealScalarOpsHooks` dispatching float unary/binary ops through `Miri.Interpreter.FloatOps.{unary, binary}` while leaving all non-float ops untouched. -/
def annealScalarOpsHooksFloatArith (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) (nondet : Bool := true) (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat := annealChooseBinaryNaN) :
    Miri.Interpreter.ScalarOpsHooks AnnealProv AnnealStepState Unit :=
  { annealScalarOpsHooks localDecls layouts with
    floatBinary := fun c op l r => Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks nondet chooseNaN) c op l r
    floatUnary := fun c op v => Miri.Interpreter.FloatOps.unary (annealFloatOpsHooks nondet chooseNaN) c op v }
/-- `RvalueHooks` overlay over `annealRvalueHooksFloat` wiring `binaryOp`/`unaryOp` through `annealScalarOpsHooksFloatArith`. -/
def annealRvalueHooksFloatArith (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) (nondet : Bool := true) (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat := annealChooseBinaryNaN) :
    Miri.Interpreter.RvalueHooks AnnealProv AnnealStepState Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealRvalueHooksFloat localDecls layouts nondet chooseNaN with
    binaryOp := fun c op l r => Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooksFloatArith localDecls layouts nondet chooseNaN) c op l r
    unaryOp := fun c op v => Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooksFloatArith localDecls layouts nondet chooseNaN) c op v }
def isFloatArithRvalue : Miri.MIR.Rvalue → Bool
  | .UnaryOp _ _ | .BinaryOp _ _ _ => true
  | _ => false
/-- Conservative `StepHooks` overlay extending `annealStepHooksFloat` with `UnaryOp`/`BinaryOp` float dispatch via `annealRvalueHooksFloatArith`. -/
def annealStepHooksFloatArith (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) (nondet : Bool := true) (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat := annealChooseBinaryNaN) :
    Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealStepHooksFloat localDecls layouts nondet chooseNaN
  { base with
    assign := fun choice place rvalue state =>
      if isFloatArithRvalue rvalue then
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooksFloatArith localDecls layouts nondet chooseNaN) choice rvalue place)
          state
      else base.assign choice place rvalue state }
/-- **Non-float `ScalarOps.binary` conservative extension**. -/
theorem scalarOps_binary_floatArith_eq_base (localDecls : List LocalDecl) (layouts : LayoutTable)
    (nondet : Bool) (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (op : Miri.MIR.BinOp) (left right : Miri.Interpreter.RvalueImmTy AnnealProv) (hnotf : classifyEncodedTyId left.layout.ty ≠ .ok .floating) :
    Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooksFloatArith localDecls layouts nondet chooseNaN) () op left right =
      Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks localDecls layouts) () op left right := by
  have hcls : ∀ tyId, (annealScalarOpsHooksFloatArith localDecls layouts nondet chooseNaN).classify () tyId = match classifyEncodedTyId tyId with | .ok c => pure c | .error e => throw e := fun _ => rfl
  have hcls_base : ∀ tyId, (annealScalarOpsHooks localDecls layouts).classify () tyId = match classifyEncodedTyId tyId with | .ok c => pure c | .error e => throw e := fun _ => rfl
  have hfin : ∀ lay res, (miriScalarOpsFinish (annealScalarOpsHooksFloatArith localDecls layouts nondet chooseNaN) () lay res : Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RvalueImmTy AnnealProv)) = miriScalarOpsFinish (annealScalarOpsHooks localDecls layouts) () lay res := fun _ res => by cases res <;> rfl
  unfold Miri.Interpreter.ScalarOps.binary; rw [hcls left.layout.ty, hcls_base left.layout.ty]
  cases hc : classifyEncodedTyId left.layout.ty with
  | error _ => rfl
  | ok cls =>
    simp only [pure_bind]
    cases cls with
    | floating => exact absurd hc hnotf
    | character | boolean => simp only [hfin]
    | integer _ =>
      have hcls_eq : (annealScalarOpsHooksFloatArith localDecls layouts nondet chooseNaN).classify () right.layout.ty = (annealScalarOpsHooks localDecls layouts).classify () right.layout.ty := rfl
      simp only [hcls_eq, hfin]
    | pointer | functionPointer => rfl
/-- **Non-float `ScalarOps.unary` conservative extension**. -/
theorem scalarOps_unary_floatArith_eq_base (localDecls : List LocalDecl) (layouts : LayoutTable)
    (nondet : Bool) (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) (op : Miri.MIR.UnOp) (value : Miri.Interpreter.RvalueImmTy AnnealProv)
    (hnotf : classifyEncodedTyId value.layout.ty ≠ .ok .floating) :
    Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooksFloatArith localDecls layouts nondet chooseNaN) () op value =
      Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooks localDecls layouts) () op value := by
  have hcls : ∀ tyId, (annealScalarOpsHooksFloatArith localDecls layouts nondet chooseNaN).classify () tyId = match classifyEncodedTyId tyId with | .ok c => pure c | .error e => throw e := fun _ => rfl
  have hcls_base : ∀ tyId, (annealScalarOpsHooks localDecls layouts).classify () tyId = match classifyEncodedTyId tyId with | .ok c => pure c | .error e => throw e := fun _ => rfl
  have hfin : ∀ lay res, (miriScalarOpsFinish (annealScalarOpsHooksFloatArith localDecls layouts nondet chooseNaN) () lay res : Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RvalueImmTy AnnealProv)) = miriScalarOpsFinish (annealScalarOpsHooks localDecls layouts) () lay res := fun _ res => by cases res <;> rfl
  unfold Miri.Interpreter.ScalarOps.unary; rw [hcls value.layout.ty, hcls_base value.layout.ty]
  cases hc : classifyEncodedTyId value.layout.ty with
  | error _ => rfl
  | ok cls =>
    simp only [pure_bind]
    cases cls with
    | floating => exact absurd hc hnotf
    | boolean => simp only [hfin]
    | integer _ | character | pointer | functionPointer => rfl
def stmtFreeOfFloatArith (stmt : Miri.MIR.Statement) : Prop :=
  match stmt.kind with | .Assign _ rvalue => isFloatArithRvalue rvalue = false | _ => True
def BodyFreeOfFloatArith (body : Miri.MIR.Body) : Prop :=
  ∀ bb ∈ body.basicBlocks.toList, ∀ stmt ∈ bb.statements.toList, stmtFreeOfFloatArith stmt
/-- **Statement-level conservative extension** over `annealStepHooksFloat`. -/
theorem evalStatement_floatArith_eq_base_of_stmtFree {localDecls : List LocalDecl}
    {layouts : LayoutTable} {nondet : Bool} {chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat}
    {stmt : Miri.MIR.Statement} (hfree : stmtFreeOfFloatArith stmt) (choice : Unit) (state : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith localDecls layouts nondet chooseNaN) choice stmt state =
      Miri.Interpreter.Step.evalStatement (annealStepHooksFloat localDecls layouts nondet chooseNaN) choice stmt state := by
  rcases stmt with ⟨si, kind⟩
  cases kind with
  | Assign place rvalue =>
    dsimp [stmtFreeOfFloatArith] at hfree
    simp [Miri.Interpreter.Step.evalStatement, annealStepHooksFloatArith, hfree]
  | _ => rfl
/-- **Conservative extension of `Step.step`** on bodies free of `UnaryOp`/`BinaryOp` assignments. -/
theorem step_floatArith_eq_base_of_floatArithFree {localDecls : List LocalDecl}
    {layouts : LayoutTable} {nondet : Bool} {chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat} {state : AnnealStepState}
    (hfree : ∀ frame, state.stack.currentFrame? = some frame → BodyFreeOfFloatArith frame.body) (choice : Unit) :
    Miri.Interpreter.Step.step (annealStepHooksFloatArith localDecls layouts nondet chooseNaN) choice state =
      Miri.Interpreter.Step.step (annealStepHooksFloat localDecls layouts nondet chooseNaN) choice state := by
  unfold Miri.Interpreter.Step.step
  cases hcf : state.stack.currentFrame? with
  | none => rfl
  | some frame =>
    dsimp only [Id.run]
    cases hloc : frame.location with
    | unwinding _ => rfl
    | mir loc =>
      dsimp only
      cases hbb : frame.body.basicBlocks[loc.block]? with
      | none => rfl
      | some bb =>
        have hbb_mem : bb ∈ frame.body.basicBlocks.toList := by
          obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hbb; exact Array.getElem_mem_toList hlt
        dsimp only
        cases hst : bb.statements[loc.statementIndex]? with
        | none => rfl
        | some stmt =>
          have hst_mem : stmt ∈ bb.statements.toList := by
            obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hst; exact Array.getElem_mem_toList hlt
          dsimp only; rw [evalStatement_floatArith_eq_base_of_stmtFree (hfree frame hcf bb hbb_mem stmt hst_mem)]
/-- **Terminator-level conservative extension** over `annealStepHooks`. -/
theorem step_floatArith_eq_annealStepHooks_at_terminator {body : CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {bb : BasicBlockData} (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = none) :
    Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () m =
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  unfold Miri.Interpreter.Step.step; rw [stack_currentFrame?_singleton m.stack tf hframes]
  dsimp only [Id.run]; rw [hfr.location_eq, hfr.body_eq]; dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]; dsimp only [Option.map]
  rw [translateBasicBlockData_statements_getElem?, hstmt]; rfl
/-! ## Part 3. Real `Miri.Interpreter.Step.step` vs. `Trusted` (`stepMirFn` / `EvalRvalueFloatRel`) Step Simulations -/
/-! ### 3.1 Shared `evalStatement` unfolding and operand / destination helpers -/
private theorem classifyEncodedTyId_floatTyIdOf (f : IeeeFormat) :
    classifyEncodedTyId (floatTyIdOf f) = .ok .floating := by cases f <;> rfl
private theorem translateOperand_copy_unproj (idx : Local) :
    translateOperand (.copy ⟨idx, .nil⟩) = .Copy ⟨idx, #[]⟩ := rfl
private theorem translateOperand_move_unproj (idx : Local) :
    translateOperand (.move ⟨idx, .nil⟩) = .Move ⟨idx, #[]⟩ := rfl
private theorem evalStatement_assign_unaryNeg_floatArith_eq (ld : List LocalDecl) (ly : LayoutTable)
    (nondet : Bool) (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (dstIdx : Local) (op : MirAst.Operand) (span : String) (m : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith ld ly nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg op), span⟩) m =
      Miri.Interpreter.runRvalue (do
        let dest ← annealEvalPlace ld ly ⟨dstIdx, #[]⟩
        let layout := dest.layout
        let valOp ← annealEvalOperand ld ly (translateOperand op) (some layout)
        let val ← annealReadImmediate valOp
        let result ← Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooksFloatArith ld ly nondet chooseNaN) () .Neg val
        assertRvalueLayoutPub result.layout layout
        annealWriteImmediate result.imm dest) m := by
  unfold Miri.Interpreter.Step.evalStatement translateStmt
  dsimp only [translateStmtKind, translateRvalue, annealStepHooksFloatArith, isFloatArithRvalue]
  simp only [↓reduceIte]; apply runRvalue_eq_of_eq; rw [evalRvalueIntoPlace_unaryOp_def]; rfl
private theorem evalStatement_assign_binaryOp_floatArith_eq (ld : List LocalDecl) (ly : LayoutTable)
    (nondet : Bool) (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (dstIdx : Local) (bop : MirAst.BinOp) (lhsOp rhsOp : MirAst.Operand) (span : String) (m : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith ld ly nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop lhsOp rhsOp), span⟩) m =
      Miri.Interpreter.runRvalue (do
        let dest ← annealEvalPlace ld ly ⟨dstIdx, #[]⟩
        let layout := dest.layout
        let leftOp ← annealEvalOperand ld ly (translateOperand lhsOp) (if (translateBinOp bop).leftHomogeneous then some layout else none)
        let left ← annealReadImmediate leftOp
        let rightOp ← annealEvalOperand ld ly (translateOperand rhsOp) (if (translateBinOp bop).rightHomogeneous then some left.layout else none)
        let right ← annealReadImmediate rightOp
        let result ← Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooksFloatArith ld ly nondet chooseNaN) () (translateBinOp bop) left right
        assertRvalueLayoutPub result.layout layout
        annealWriteImmediate result.imm dest) m := by
  unfold Miri.Interpreter.Step.evalStatement translateStmt
  dsimp only [translateStmtKind, translateRvalue, annealStepHooksFloatArith, isFloatArithRvalue]
  simp only [↓reduceIte]; apply runRvalue_eq_of_eq; rw [evalRvalueIntoPlace_binaryOp_def]; rfl
private theorem scalarOps_unary_floatNeg_eq (ld : List LocalDecl) (ly : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {ty : Ty} {f : IeeeFormat} (hf : ieeeFormatOfTy? ty = some f)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) (hsz : sc.sizeBytes = f.byteWidth) :
    ∃ msc', ScalarRel ⟨evalFloatNeg f sc.bits, f.byteWidth⟩ msc' ∧
      Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooksFloatArith ld ly nondet chooseNaN) () .Neg
          ⟨.scalar (.fromScalarInt msc), translateTy ty ly⟩ =
        pure ⟨.scalar (.fromScalarInt msc'), translateTy ty ly⟩ := by
  obtain ⟨msc', hrel', hfu⟩ := floatOps_unary_neg_eq ly nondet chooseNaN hf hrel hsz
  refine ⟨msc', hrel', ?_⟩
  have hT := translateTy_of_ieeeFormatOfTy? hf ly
  have hcls : (annealScalarOpsHooksFloatArith ld ly nondet chooseNaN).classify () (translateTy ty ly).ty =
      pure .floating := by simp only [annealScalarOpsHooksFloatArith, annealScalarOpsHooks, hT, classifyEncodedTyId_floatTyIdOf]
  unfold Miri.Interpreter.ScalarOps.unary; rw [hcls, pure_bind]; dsimp only
  have hto : (miriScalarOpsToScalar (⟨.scalar (.fromScalarInt msc), translateTy ty ly⟩ :
      Miri.Interpreter.RvalueImmTy AnnealProv) : Miri.Interpreter.RvalueM AnnealStepState (Miri.Memory.Scalar AnnealProv)) =
      pure (.fromScalarInt msc) := rfl
  rw [hto, pure_bind]; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]; exact hfu
private theorem scalarOps_binary_float_eq (ld : List LocalDecl) (ly : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {lTy rTy : Ty} {f : IeeeFormat} (hlf : ieeeFormatOfTy? lTy = some f) (hrf : ieeeFormatOfTy? rTy = some f) (op : Miri.MIR.BinOp) (lImm rImm : Miri.Interpreter.Immediate AnnealProv) :
    Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooksFloatArith ld ly nondet chooseNaN) () op
        ⟨lImm, translateTy lTy ly⟩ ⟨rImm, translateTy rTy ly⟩ =
      Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks nondet chooseNaN) () op
        ⟨lImm, translateTy lTy ly⟩ ⟨rImm, translateTy rTy ly⟩ := by
  have hL := translateTy_of_ieeeFormatOfTy? hlf ly
  have hR := translateTy_of_ieeeFormatOfTy? hrf ly
  have hcls : (annealScalarOpsHooksFloatArith ld ly nondet chooseNaN).classify () (translateTy lTy ly).ty =
      pure .floating := by simp only [annealScalarOpsHooksFloatArith, annealScalarOpsHooks, hL, classifyEncodedTyId_floatTyIdOf]
  unfold Miri.Interpreter.ScalarOps.binary; rw [hcls, pure_bind]; dsimp only
  have hsame : (miriScalarOpsAssertSameType (⟨lImm, translateTy lTy ly⟩ : Miri.Interpreter.RvalueImmTy AnnealProv)
      (⟨rImm, translateTy rTy ly⟩ : Miri.Interpreter.RvalueImmTy AnnealProv) :
      Miri.Interpreter.RvalueM AnnealStepState Unit) = pure () := by
    change (if ((translateTy lTy ly).ty == (translateTy rTy ly).ty) then pure ()
      else throw (Miri.Interpreter.StepError.invalidProgram "asymmetric scalar operand types")) = pure ()
    simp [hL, hR]
  rw [hsame, pure_bind]; rfl
private theorem bool_dst_localRel {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {dstDecl : LocalDecl} {layouts : LayoutTable} (hdst_bool : dstDecl.ty.kind = .bool) (b : Bool) (cachedLay : Option Miri.Interpreter.LocalLayout)
    (hc : ∀ l, cachedLay = some l → l = translateTy dstDecl.ty layouts) :
    LocalRelLM3_1 mach allocMap dstDecl layouts (.init (.scalar (boolToScalar b)))
      ⟨.live (.immediate (.scalar (.fromBool b))), cachedLay⟩ := by
  have hsz : (translateTy dstDecl.ty layouts).layout.size = translateSizeBytes (boolToScalar b).sizeBytes := by
    rw [translateTy_bool_eq hdst_bool layouts]; cases b <;> rfl
  exact .base (.immediate (.init (.scalar (boolToScalar b))) (.scalar (.fromBool b)) cachedLay hc
    (Or.inr ⟨.scalar (boolToScalar b), rfl,
      .scalar (boolToScalar b) (Miri.Memory.ScalarInt.ofBool b) (ScalarRel.of_boolToScalar b) hsz
        (fun _ => by cases b <;> simp [boolToScalar])
        (fun hch => by rw [hdst_bool] at hch; cases hch)⟩))
private theorem isFloatOptTy_some_of_ieee {ty : Ty} {f : IeeeFormat} (hf : ieeeFormatOfTy? ty = some f) :
    isFloatOptTy (some ty) = true := by
  rcases ieeeFormatOfTy?_kind hf with ⟨hk, _⟩ | ⟨hk, _⟩ <;> simp [isFloatOptTy, isFloatTy, hk]
private theorem annealEvalOperand_constant_float_ok {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit} (hframes : m.stack.frames = #[tf]) {c : ConstOperand} {f : IeeeFormat} (hf : ieeeFormatOfTy? c.ty = some f)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc)) (hsz : sc.sizeBytes = f.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (known : Option Miri.Interpreter.LocalLayout) :
    ∃ msc, ScalarRel sc msc ∧
      annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c)) known m =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ m := by
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical (hsz ▸ validScalarBytes_byteWidth f) hcan
  refine ⟨msc, hrel, ?_⟩
  with_unfolding_all
    unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
    dsimp only; rw [hval]
    simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get, EStateM.get,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, stack_currentFrame?_singleton m.stack tf hframes,
      Option.isNone_some, Bool.false_eq_true, ↓reduceIte, htry,
      layoutOfEncodedTyId_floatCastScalar (Or.inl ⟨f, hf⟩) body.layouts]
private theorem evalOperand_copy_scalar_ok {locals : List LocalSlot} {mem : Memory}
    {ld : List LocalDecl} {ly : LayoutTable} {idx : Local} {sc : MirAst.ScalarInt} (hslot : get? locals idx = some (.init (.scalar sc))) :
    evalOperand locals (.copy ⟨idx, .nil⟩) mem.borrows mem.globals ly mem.callerLocals ld mem.callStack =
      .ok (.scalar sc) locals := by unfold evalOperand readProjectedValue; dsimp only []; rw [hslot]
private theorem evalOperand_move_scalar_ok {locals : List LocalSlot} {mem : Memory}
    {ld : List LocalDecl} {ly : LayoutTable} {idx : Local} {sc : MirAst.ScalarInt} (hslot : get? locals idx = some (.init (.scalar sc))) :
    evalOperand locals (.move ⟨idx, .nil⟩) mem.borrows mem.globals ly mem.callerLocals ld mem.callStack =
      .ok (.scalar sc) (locals.set idx .uninit) := by
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp (by rw [← get?_eq_getElem?]; exact hslot)
  unfold evalOperand readProjectedValue; dsimp only []; rw [hslot, set?_eq_some_set hlt]
private theorem evalOperand_const_scalar_ok {locals : List LocalSlot} {mem : Memory}
    {ld : List LocalDecl} {ly : LayoutTable} {c : ConstOperand} {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc)) :
    evalOperand locals (.constant c) mem.borrows mem.globals ly mem.callerLocals ld mem.callStack =
      .ok (.scalar sc) locals := by unfold evalOperand; dsimp only; rw [hval]; rfl
/-- Shared initialized copy/copy binary float evaluation, polymorphic over `(nondet, chooseNaN)` so both soundness and completeness reuse the exact same `(lMsc, rMsc)` witnesses. -/
private theorem binary_copy_copy_float_init_eval
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap)
    {dstIdx lhsIdx rhsIdx : Local} {bop : MirAst.BinOp} {span : String} {dstDecl lhsDecl rhsDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl) (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl)
    (hf_lhs : ieeeFormatOfTy? lhsDecl.ty = some f) (hf_rhs : ieeeFormatOfTy? rhsDecl.ty = some f) {lSc rSc : MirAst.ScalarInt}
    (hslot_l : get? s.frame.locals lhsIdx = some (.init (.scalar lSc))) (hslot_r : get? s.frame.locals rhsIdx = some (.init (.scalar rSc))) (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame lhsIdx ∧ IsImmediateFrameLocal topFrame rhsIdx) :
    ∃ (tf tfc : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (lMsc rMsc : Miri.Memory.ScalarInt),
      m.stack.frames = #[tf] ∧ tf.body = translateBody body ∧
      tf.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tfc]⟩ } allocMap ∧
      IsImmediateFrameLocal tfc dstIdx ∧
      ScalarRel lSc lMsc ∧ ScalarRel rSc rMsc ∧
      lSc.sizeBytes = f.byteWidth ∧ rSc.sizeBytes = f.byteWidth ∧
      ∀ (nondet : Bool) (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat),
        Miri.Interpreter.Step.evalStatement
          (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m =
          Miri.Interpreter.runRvalue (do
            let result ← Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks nondet chooseNaN) () (translateBinOp bop)
              ⟨.scalar (.fromScalarInt lMsc), translateTy lhsDecl.ty body.layouts⟩
              ⟨.scalar (.fromScalarInt rMsc), translateTy rhsDecl.ty body.layouts⟩
            assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
            annealWriteImmediate result.imm ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
            { m with stack := ⟨#[tfc]⟩ } := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate; obtain ⟨himm_d, himm_l, himm_r⟩ := himm tf hframes
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts); have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_l0, mls_l, _, hlt_la, hslot_l0, hmls_l, hmls_l_eq, hloc_l⟩ := hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_lhs
  have hslot_l_eq : slot_l0 = .init (.scalar lSc) := Option.some.inj (hslot_l0.symm.trans hslot_l); subst hslot_l_eq
  let tfb := cacheFrameLocalLayout tfa lhsIdx hlt_la (translateTy lhsDecl.ty body.layouts); have hstate_b := hstate_a.cache_layout rfl hdecl_lhs hlt_la
  rcases hloc_l.floatCast_immediate_cases (Or.inl ⟨f, hf_lhs⟩) ((himm_l.cache_layout hlt_d _) mls_l hmls_l) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨lSc', lMsc, hl_eq, hlrel, hlsz, hml⟩
  · cases h
  · cases h
  · injection hl_eq with hl_eq'; injection hl_eq' with hl_eq''; subst hl_eq''
    have hl_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none)
      rfl hlt_la hdecl_lhs (by rw [hmls_l_eq]; rcases mls_l with ⟨v0, l0⟩; dsimp only at hml; subst hml; rfl) hloc_l.cachedLayout_eq
    obtain ⟨slot_r0, mls_r, _, hlt_rb, hslot_r0, hmls_r, hmls_r_eq, hloc_r⟩ := hstate_b.frame_rel_singleton rfl |>.lookup_local hdecl_rhs
    have hslot_r_eq : slot_r0 = .init (.scalar rSc) := Option.some.inj (hslot_r0.symm.trans hslot_r); subst hslot_r_eq
    let tfc := cacheFrameLocalLayout tfb rhsIdx hlt_rb (translateTy rhsDecl.ty body.layouts); have hstate_c := hstate_b.cache_layout rfl hdecl_rhs hlt_rb
    rcases hloc_r.floatCast_immediate_cases (Or.inl ⟨f, hf_rhs⟩) (((himm_r.cache_layout hlt_d _).cache_layout hlt_la _) mls_r hmls_r) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨rSc', rMsc, hr_eq, hrrel, hrsz, hmr⟩
    · cases h
    · cases h
    · injection hr_eq with hr_eq'; injection hr_eq' with hr_eq''; subst hr_eq''
      rw [translateTy_of_ieeeFormatOfTy? hf_lhs body.layouts] at hlsz; rw [translateTy_of_ieeeFormatOfTy? hf_rhs body.layouts] at hrsz
      have hr_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfb]⟩ }) (known := if (translateBinOp bop).rightHomogeneous then some (translateTy lhsDecl.ty body.layouts) else none)
        rfl hlt_rb hdecl_rhs (by rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr; subst hmr; rfl) hloc_r.cachedLayout_eq
      refine ⟨tf, tfc, lMsc, rMsc, hframes, hfr.body_eq, hfr.location_eq, hstate_c, (((himm_d.cache_layout hlt_d _).cache_layout hlt_la _).cache_layout hlt_rb _), hlrel, hrrel,
        sizeBytes_of_float_layout hlrel.validBytes hlsz, sizeBytes_of_float_layout hrrel.validBytes hrsz, fun nondet chooseNaN => ?_⟩
      rw [evalStatement_assign_binaryOp_floatArith_eq, translateOperand_copy_unproj, translateOperand_copy_unproj]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_scalar, pure_bind, EStateM.bind_eq_ok hr_ok, annealReadImmediate_scalar, pure_bind, scalarOps_binary_float_eq _ _ _ _ hf_lhs hf_rhs]
/-- Shared copy/copy binary float dispatch: closes `.dead`/`.uninit` operands as lockstep `.ub`, or delegates initialized operands to `binary_copy_copy_float_init_eval`. -/
private theorem binary_copy_copy_float_setup
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool) (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx lhsIdx rhsIdx : Local} {bop : MirAst.BinOp} {span : String} (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩)
    {dstDecl lhsDecl rhsDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl)
    (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl) (hf_lhs : ieeeFormatOfTy? lhsDecl.ty = some f) (hf_rhs : ieeeFormatOfTy? rhsDecl.ty = some f)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame lhsIdx ∧ IsImmediateFrameLocal topFrame rhsIdx) :
    StepRelLM3_1 body m allocMap (stepMirFn body s) (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () m) ∨
      ∃ (lSc rSc : MirAst.ScalarInt), get? s.frame.locals lhsIdx = some (.init (.scalar lSc)) ∧ get? s.frame.locals rhsIdx = some (.init (.scalar rSc)) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate; obtain ⟨_, himm_l, himm_r⟩ := himm tf hframes
  have hm_stmt := evalStatement_assign_binaryOp_floatArith_eq body.localDecls body.layouts nondet chooseNaN dstIdx bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩) span m
  rw [translateOperand_copy_unproj, translateOperand_copy_unproj] at hm_stmt
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts); have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_l, mls_l, _, hlt_la, hslot_l, hmls_l, hmls_l_eq, hloc_l⟩ := hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_lhs
  let tfb := cacheFrameLocalLayout tfa lhsIdx hlt_la (translateTy lhsDecl.ty body.layouts); have hstate_b := hstate_a.cache_layout rfl hdecl_lhs hlt_la
  rcases hloc_l.floatCast_immediate_cases (Or.inl ⟨f, hf_lhs⟩) ((himm_l.cache_layout hlt_d _) mls_l hmls_l) with ⟨hsl, hml⟩ | ⟨hsl, hml⟩ | ⟨lSc, lMsc, hsl, _, _, hml⟩
  · left; subst hsl
    have hl_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none)
      rfl hlt_la hdecl_lhs (by rw [hmls_l_eq]; rcases mls_l with ⟨v0, l0⟩; dsimp only at hml; subst hml; rfl) hloc_l.cachedLayout_eq
    have ha_ub : stepMirFn body s = .fail .ub := by rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_l]
    have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hl_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact .ub _ _
  · left; subst hsl
    have hl_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none)
      rfl hlt_la hdecl_lhs (by rw [hmls_l_eq]; rcases mls_l with ⟨v0, l0⟩; dsimp only at hml; subst hml; rfl) hloc_l.cachedLayout_eq
    have ha_ub : stepMirFn body s = .fail .ub := by rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_l]
    have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_uninit_eq]; rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact .ub _ _
  · subst hsl
    have hl_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none)
      rfl hlt_la hdecl_lhs (by rw [hmls_l_eq]; rcases mls_l with ⟨v0, l0⟩; dsimp only at hml; subst hml; rfl) hloc_l.cachedLayout_eq
    obtain ⟨slot_r, mls_r, _, hlt_rb, hslot_r, hmls_r, hmls_r_eq, hloc_r⟩ := hstate_b.frame_rel_singleton rfl |>.lookup_local hdecl_rhs
    let tfc := cacheFrameLocalLayout tfb rhsIdx hlt_rb (translateTy rhsDecl.ty body.layouts)
    rcases hloc_r.floatCast_immediate_cases (Or.inl ⟨f, hf_rhs⟩) (((himm_r.cache_layout hlt_d _).cache_layout hlt_la _) mls_r hmls_r) with ⟨hsr, hmr⟩ | ⟨hsr, hmr⟩ | ⟨rSc, _, hsr, _, _, _⟩
    · left; subst hsr
      have hr_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfb]⟩ }) (known := if (translateBinOp bop).rightHomogeneous then some (translateTy lhsDecl.ty body.layouts) else none)
        rfl hlt_rb hdecl_rhs (by rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr; subst hmr; rfl) hloc_r.cachedLayout_eq
      have ha_ub : stepMirFn body s = .fail .ub := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; unfold evalStmt evalRvalue; dsimp only []; rw [evalOperand_copy_scalar_ok hslot_l]; dsimp only []; unfold evalOperand; dsimp only []; rw [hslot_r]
      have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m =
          ({ m with stack := ⟨#[tfc]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_scalar, pure_bind, EStateM.bind_eq_error hr_err]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact .ub _ _
    · left; subst hsr
      have hr_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfb]⟩ }) (known := if (translateBinOp bop).rightHomogeneous then some (translateTy lhsDecl.ty body.layouts) else none)
        rfl hlt_rb hdecl_rhs (by rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr; subst hmr; rfl) hloc_r.cachedLayout_eq
      have ha_ub : stepMirFn body s = .fail .ub := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; unfold evalStmt evalRvalue; dsimp only []; rw [evalOperand_copy_scalar_ok hslot_l]; dsimp only []; unfold evalOperand; dsimp only []; rw [hslot_r]
      have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m =
          ({ m with stack := ⟨#[tfc]⟩ }, .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_scalar, pure_bind, EStateM.bind_eq_ok hr_ok, annealReadImmediate_uninit_eq]; rfl
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact .ub _ _
    · right; subst hsr; exact ⟨lSc, rSc, hslot_l, hslot_r⟩
/-- Shared const/const binary float setup. -/
private theorem binary_const_const_float_eval
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {dstIdx : Local} {bop : MirAst.BinOp} {c₁ c₂ : ConstOperand} {span : String}
    {dstDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hf₁ : ieeeFormatOfTy? c₁.ty = some f) (hf₂ : ieeeFormatOfTy? c₂.ty = some f)
    {sc₁ sc₂ : MirAst.ScalarInt} (hv₁ : c₁.val = .scalar (.int sc₁)) (hv₂ : c₂.val = .scalar (.int sc₂)) (hsz₁ : sc₁.sizeBytes = f.byteWidth) (hsz₂ : sc₂.sizeBytes = f.byteWidth)
    (hcan₁ : sc₁.bits < scalarModulus sc₁.sizeBytes) (hcan₂ : sc₂.bits < scalarModulus sc₂.sizeBytes) :
    ∃ (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (hlt_d : dstIdx < tf.locals.size) (msc₁ msc₂ : Miri.Memory.ScalarInt),
      let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
      m.stack.frames = #[tf] ∧ tf.body = translateBody body ∧
      tf.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap ∧
      ScalarRel sc₁ msc₁ ∧ ScalarRel sc₂ msc₂ ∧
      Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c₁) (.constant c₂)), span⟩) m =
        Miri.Interpreter.runRvalue (do
          let result ← Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks nondet chooseNaN) () (translateBinOp bop)
            ⟨.scalar (.fromScalarInt msc₁), translateTy c₁.ty body.layouts⟩
            ⟨.scalar (.fromScalarInt msc₂), translateTy c₂.ty body.layouts⟩
          assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
          annealWriteImmediate result.imm ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfa]⟩ } := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  obtain ⟨msc₁, hrel₁, hl_ok⟩ := annealEvalOperand_constant_float_ok (body := body) (m := { m with stack := ⟨#[tfa]⟩ }) rfl hf₁ hv₁ hsz₁ hcan₁ _
  obtain ⟨msc₂, hrel₂, hr_ok⟩ := annealEvalOperand_constant_float_ok (body := body) (m := { m with stack := ⟨#[tfa]⟩ }) rfl hf₂ hv₂ hsz₂ hcan₂ _
  refine ⟨tf, hlt_d, msc₁, msc₂, hframes, hfr.body_eq, hfr.location_eq, hstate.cache_layout hframes hdecl_dst hlt_d, hrel₁, hrel₂, ?_⟩
  rw [evalStatement_assign_binaryOp_floatArith_eq]; unfold Miri.Interpreter.runRvalue
  rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_scalar, pure_bind, EStateM.bind_eq_ok hr_ok, annealReadImmediate_scalar, pure_bind,
    scalarOps_binary_float_eq _ _ _ _ hf₁ hf₂]
/-! ### 3.2 Real `Step.step` simulations for `Rvalue.unaryOp .neg` (copy / move / constant / indirect) -/
/-- **Copy-operand unary negation real-step simulation** (`_d = -copy _s`, immediate locals). -/
theorem step_float_unaryNeg_copy_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {bb : BasicBlockData} {dstIdx srcIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)), span⟩)
    {dstDecl srcDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hf_src : ieeeFormatOfTy? srcDecl.ty = some f) (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
  have hm_stmt := evalStatement_assign_unaryNeg_floatArith_eq body.localDecls body.layouts nondet chooseNaN dstIdx (.copy ⟨srcIdx, .nil⟩) span m
  rw [translateOperand_copy_unproj] at hm_stmt
  have hdstT : translateTy srcDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by
    rw [translateTy_of_ieeeFormatOfTy? hf_src, translateTy_of_ieeeFormatOfTy? hf_dst]
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
  rcases hloc_s.floatCast_immediate_cases (Or.inl ⟨f, hf_src⟩) ((himm_s.cache_layout hlt_d _) mls_s hmls_s) with
    ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
  · subst hss
    have hsrc_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src
      (by rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl) hloc_s.cachedLayout_eq
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)), span⟩ body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact .ub _ _
  · subst hss
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src
      (by rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl) hloc_s.cachedLayout_eq
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)), span⟩ body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, annealReadImmediate_uninit_eq]; rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact .ub _ _
  · subst hss
    rw [translateTy_of_ieeeFormatOfTy? hf_src body.layouts] at hsz
    have hbw := sizeBytes_of_float_layout hrel.validBytes hsz
    obtain ⟨msc', hrel', hsu⟩ := scalarOps_unary_floatNeg_eq body.localDecls body.layouts nondet chooseNaN hf_src hrel hbw
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src
      (by rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl) hloc_s.cachedLayout_eq
    have hrv_a : evalRvalue s.frame.locals (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)) s.memory body.localDecls body.layouts =
        .ok (.scalar ⟨evalFloatNeg f sc.bits, f.byteWidth⟩) s.frame.locals s.memory := by
      rw [evalRvalue_unaryOp_neg_float _ _ _ sc _ _ _ (evalOperand_copy_scalar_ok hslot_s) (by rw [operandTy_copy_local hdecl_src]; exact isFloatOptTy_some_of_ieee hf_src)]
      unfold evalFloatUnaryNeg; rw [operandTy_copy_local hdecl_src]; dsimp only; rw [hf_src, hbw]; dsimp only; rw [Nat.beq_refl]
    have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
        Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩) { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, annealReadImmediate_scalar, pure_bind, hsu, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
    have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes f.byteWidth := by
      rw [translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
    exact finish_write_immediate_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_b rfl hbb hstmt hdecl_dst ((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _)
      hrv_a hm_write (floatCast_dst_localRel (Or.inl ⟨f, hf_dst⟩) hrel' hdst_sz)
/-- **Move-operand unary negation real-step simulation** (`_d = -move _s`, immediate locals). -/
theorem step_float_unaryNeg_move_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {bb : BasicBlockData} {dstIdx srcIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.move ⟨srcIdx, .nil⟩)), span⟩)
    {dstDecl srcDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hf_src : ieeeFormatOfTy? srcDecl.ty = some f) (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
  have hm_stmt := evalStatement_assign_unaryNeg_floatArith_eq body.localDecls body.layouts nondet chooseNaN dstIdx (.move ⟨srcIdx, .nil⟩) span m
  rw [translateOperand_move_unproj] at hm_stmt
  have hdstT : translateTy srcDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by
    rw [translateTy_of_ieeeFormatOfTy? hf_src, translateTy_of_ieeeFormatOfTy? hf_dst]
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
  rcases hloc_s.floatCast_immediate_cases (Or.inl ⟨f, hf_src⟩) ((himm_s.cache_layout hlt_d _) mls_s hmls_s) with
    ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
  · subst hss
    have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src
      (by rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl) hloc_s.cachedLayout_eq
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.move ⟨srcIdx, .nil⟩)), span⟩ body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.move ⟨srcIdx, .nil⟩)), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact .ub _ _
  · subst hss
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src
      (by rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl) hloc_s.cachedLayout_eq
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.move ⟨srcIdx, .nil⟩)), span⟩ body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.move ⟨srcIdx, .nil⟩)), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ }, .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, annealReadImmediate_uninit_eq]; rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact .ub _ _
  · subst hss
    rw [translateTy_of_ieeeFormatOfTy? hf_src body.layouts] at hsz
    have hbw := sizeBytes_of_float_layout hrel.validBytes hsz
    obtain ⟨msc', hrel', hsu⟩ := scalarOps_unary_floatNeg_eq body.localDecls body.layouts nondet chooseNaN hf_src hrel hbw
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src
      (by rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl) hloc_s.cachedLayout_eq
    have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hslot_s (by simp)
      ((himm_s.cache_layout hlt_d _).cache_layout hlt_sa _) hlt_sb
    have hrv_a : evalRvalue s.frame.locals (.unaryOp .neg (.move ⟨srcIdx, .nil⟩)) s.memory body.localDecls body.layouts =
        .ok (.scalar ⟨evalFloatNeg f sc.bits, f.byteWidth⟩) (s.frame.locals.set srcIdx .uninit) s.memory := by
      rw [evalRvalue_unaryOp_neg_float _ _ _ sc _ _ _ (evalOperand_move_scalar_ok hslot_s) (by rw [operandTy_move_local hdecl_src]; exact isFloatOptTy_some_of_ieee hf_src)]
      unfold evalFloatUnaryNeg; rw [operandTy_move_local hdecl_src]; dsimp only; rw [hf_src, hbw]; dsimp only; rw [Nat.beq_refl]
    have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.move ⟨srcIdx, .nil⟩)), span⟩) m =
        Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, annealReadImmediate_scalar, pure_bind, hsu, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
    have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes f.byteWidth := by
      rw [translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
    exact finish_write_immediate_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_mid rfl hbb hstmt hdecl_dst
      (((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb)
      hrv_a hm_write (floatCast_dst_localRel (Or.inl ⟨f, hf_dst⟩) hrel' hdst_sz)
/-- **Constant-operand unary negation real-step simulation** (`_d = -const c`). -/
theorem step_float_unaryNeg_constant_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.constant c)), span⟩)
    {dstDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hf_c : ieeeFormatOfTy? c.ty = some f) (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc)) (hsz : sc.sizeBytes = f.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have hdstT : translateTy c.ty body.layouts = translateTy dstDecl.ty body.layouts := by
    rw [translateTy_of_ieeeFormatOfTy? hf_c, translateTy_of_ieeeFormatOfTy? hf_dst]
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  obtain ⟨msc, hrel, hsrc_ok⟩ := annealEvalOperand_constant_float_ok (body := body) (m := { m with stack := ⟨#[tfa]⟩ }) rfl hf_c hval hsz hcan _
  obtain ⟨msc', hrel', hsu⟩ := scalarOps_unary_floatNeg_eq body.localDecls body.layouts nondet chooseNaN hf_c hrel hsz
  have hrv_a : evalRvalue s.frame.locals (.unaryOp .neg (.constant c)) s.memory body.localDecls body.layouts =
      .ok (.scalar ⟨evalFloatNeg f sc.bits, f.byteWidth⟩) s.frame.locals s.memory := by
    rw [evalRvalue_unaryOp_neg_float _ _ _ sc _ _ _ (evalOperand_const_scalar_ok hval) (isFloatOptTy_some_of_ieee hf_c)]
    unfold evalFloatUnaryNeg; simp [hf_c, hsz]
  have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.constant c)), span⟩) m =
      Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc'))
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩) { m with stack := ⟨#[tfa]⟩ } := by
    rw [evalStatement_assign_unaryNeg_floatArith_eq]; unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, annealReadImmediate_scalar, pure_bind, hsu, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
  have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes f.byteWidth := by
    rw [translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
  rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
  exact finish_write_immediate_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
    (hstate.cache_layout hframes hdecl_dst hlt_d) rfl hbb hstmt hdecl_dst ((himm tf hframes).cache_layout hlt_d _) hrv_a hm_write
    (floatCast_dst_localRel (Or.inl ⟨f, hf_dst⟩) hrel' hdst_sz)
/-- **Memory-backed (`LocalRel.indirect`) source & destination unary negation real-step simulation**. -/
theorem step_float_unaryNeg_copy_indirect_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {bb : BasicBlockData} {dstIdx srcIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)), span⟩)
    {dstDecl srcDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hf_src : ieeeFormatOfTy? srcDecl.ty = some f) (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f) {srcAllocId dstAllocId : Miri.Memory.AllocId}
    {srcLocalAlloc dstLocalAlloc : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind} (hsid_lt : srcAllocId.value.toNat < 2 ^ 32)
    (hsbase : m.machine.lookupBaseAddr srcAllocId = some (annealStackBaseAddr srcAllocId))
    (hsfind : m.machine.memory.live.find? (fun x => x.1 == srcAllocId) = some (srcAllocId, srcLocalAlloc))
    (hsuniq : ∀ la₁ la₂, (srcAllocId, la₁) ∈ m.machine.memory.live.toList → (srcAllocId, la₂) ∈ m.machine.memory.live.toList → la₁ = la₂)
    (hsshape : StackScalarAllocShape (translateTy srcDecl.ty body.layouts).layout.size srcLocalAlloc.allocation)
    (hind_src : ∀ topFrame, m.stack.frames = #[topFrame] → ∃ lay, topFrame.locals[srcIdx]? = some ⟨.live (.indirect (stackAllocPlace srcAllocId)), lay⟩)
    (hsc_src : ∀ v, get? s.frame.locals srcIdx = some (.init v) → ∃ sc, v = .scalar sc) (hdid_lt : dstAllocId.value.toNat < 2 ^ 32)
    (hdbase : m.machine.lookupBaseAddr dstAllocId = some (annealStackBaseAddr dstAllocId))
    (hdfind : m.machine.memory.live.find? (fun x => x.1 == dstAllocId) = some (dstAllocId, dstLocalAlloc))
    (hdshape : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size dstLocalAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] → ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace dstAllocId)), lay⟩) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨lay_s0, hlay_s0⟩ := hind_src tf hframes; obtain ⟨lay_d0, hlay_d0⟩ := hind_dst tf hframes
  have hnot_dst := hstate.not_mem_allocMap_of_ieeeFormatOfTy? hdecl_dst hf_dst
  have hm_stmt := evalStatement_assign_unaryNeg_floatArith_eq body.localDecls body.layouts nondet chooseNaN dstIdx (.copy ⟨srcIdx, .nil⟩) span m
  rw [translateOperand_copy_unproj] at hm_stmt
  have hdstT : translateTy srcDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by
    rw [translateTy_of_ieeeFormatOfTy? hf_src, translateTy_of_ieeeFormatOfTy? hf_dst]
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have hlay_tfa_s : ∃ lay_s, tfa.locals[srcIdx]? = some ⟨.live (.indirect (stackAllocPlace srcAllocId)), lay_s⟩ := by
    dsimp [tfa, cacheFrameLocalLayout]; rw [Array.getElem?_set]
    by_cases hds : dstIdx = srcIdx
    · subst hds; simp only [↓reduceIte, Array.getElem?_eq_getElem hlt_d] at hlay_s0 ⊢
      injection hlay_s0 with hm0; rw [hm0]; exact ⟨_, rfl⟩
    · simp only [hds, ↓reduceIte]; exact ⟨lay_s0, hlay_s0⟩
  obtain ⟨lay_s, hlay_s⟩ := hlay_tfa_s
  have hmls_s_ind : mls_s = ⟨.live (.indirect (stackAllocPlace srcAllocId)), lay_s⟩ := by rw [hmls_s] at hlay_s; exact Option.some.inj hlay_s
  have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
    (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src
    (by rw [hmls_s_eq]; exact hmls_s_ind) (by have hc := hloc_s.cachedLayout_eq; rw [hmls_s_ind] at hc; exact hc)
  have hsrc_sc : IsFloatCastScalarTy srcDecl.ty := Or.inl ⟨f, hf_src⟩
  obtain ⟨hun_s, hsc_s⟩ := hloc_s.indirect_stackAllocPlace_spec (e := { tag := 0, localIdx := srcIdx, allocId := srcAllocId, perm := .active })
    hmls_s_ind hsbase hsfind hsuniq (hsrc_sc.size_ne_zero body.layouts)
  have hread_mem := annealReadMemoryPlace_floatCastScalar_zero_offset_eq hsrc_sc
    hsid_lt hsbase hsfind hsshape.byteSize_eq (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tfb]⟩ })
  rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
  cases hss : slot_s with
  | dead =>
    exfalso; cases hloc_s with
    | rawPtr _ _ _ _ _ _ _ _ => cases hmls_s_ind
    | base hb => cases hb with | dead _ _ | immediate _ _ _ _ _ => cases hmls_s_ind | indirect _ _ _ _ hne _ => exact hne hss
  | uninit =>
    obtain ⟨_, hread_err⟩ := hsshape.uninit_readScalar_err (hun_s hss) false
    have hri_err : annealReadImmediate ⟨.indirect (stackAllocPlace srcAllocId), translateTy srcDecl.ty body.layouts⟩ { m with stack := ⟨#[tfb]⟩ } =
        .error (.undefinedBehavior "read of uninitialized memory") { m with stack := ⟨#[tfb]⟩ } := by
      rw [annealReadImmediate_indirect_floatCastScalar_eq hsrc_sc, stackAllocPlace, hread_mem, hread_err]
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)), span⟩ body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss]
    have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of uninitialized memory")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, EStateM.bind_eq_error hri_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact .ub _ _
  | init vs =>
    obtain ⟨sc, rfl⟩ := hsc_src vs (hss ▸ hslot_s)
    obtain ⟨hsz, _, _, msc, hrel, hread_ok⟩ := hsc_s sc hss
    have hri_ok : annealReadImmediate ⟨.indirect (stackAllocPlace srcAllocId), translateTy srcDecl.ty body.layouts⟩ { m with stack := ⟨#[tfb]⟩ } =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩ { m with stack := ⟨#[tfb]⟩ } := by
      rw [annealReadImmediate_indirect_floatCastScalar_eq hsrc_sc, stackAllocPlace, hread_mem, hread_ok]
      dsimp only []; rw [hsrc_sc.validateScalar_true msc]; rfl
    rw [translateTy_of_ieeeFormatOfTy? hf_src body.layouts] at hsz
    have hbw := sizeBytes_of_float_layout hrel.validBytes hsz
    obtain ⟨msc', hrel', hsu⟩ := scalarOps_unary_floatNeg_eq body.localDecls body.layouts nondet chooseNaN hf_src hrel hbw
    have hrv_a : evalRvalue s.frame.locals (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)) s.memory body.localDecls body.layouts =
        .ok (.scalar ⟨evalFloatNeg f sc.bits, f.byteWidth⟩) s.frame.locals s.memory := by
      rw [evalRvalue_unaryOp_neg_float _ _ _ sc _ _ _ (evalOperand_copy_scalar_ok (hss ▸ hslot_s)) (by rw [operandTy_copy_local hdecl_src]; exact isFloatOptTy_some_of_ieee hf_src)]
      unfold evalFloatUnaryNeg; rw [operandTy_copy_local hdecl_src]; dsimp only; rw [hf_src, hbw]; dsimp only; rw [Nat.beq_refl]
    have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
        Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩) { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, EStateM.bind_eq_ok hri_ok, hsu, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
    have hlay_tfb_d : ∃ lay_d, tfb.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace dstAllocId)), lay_d⟩ := by
      have h1 : ∃ lay_da, tfa.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace dstAllocId)), lay_da⟩ := by
        dsimp [tfa, cacheFrameLocalLayout]; rw [Array.getElem?_set_self hlt_d]
        rw [Array.getElem?_eq_getElem hlt_d] at hlay_d0; injection hlay_d0 with hm0; rw [hm0]; exact ⟨_, rfl⟩
      obtain ⟨lay_da, hlay_da⟩ := h1; dsimp [tfb, cacheFrameLocalLayout]; rw [Array.getElem?_set]
      by_cases hsd : srcIdx = dstIdx
      · subst hsd; simp only [↓reduceIte]; dsimp only [tfa] at hlay_da ⊢
        rw [Array.getElem?_eq_getElem hlt_sa] at hlay_da
        injection hlay_da with hm0; rw [hm0]; exact ⟨_, rfl⟩
      · simp only [hsd, ↓reduceIte]; exact ⟨lay_da, hlay_da⟩
    obtain ⟨lay_d, hlay_d⟩ := hlay_tfb_d
    have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes f.byteWidth := by
      rw [translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
    exact finish_write_unpromoted_indirect_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_b rfl hbb hstmt hdecl_dst (Or.inl ⟨f, hf_dst⟩) hnot_dst hlay_d
      hdid_lt hdbase hdfind hdshape hrel' hdst_sz hrv_a hm_write
/-! ### 3.3 Real `Step.step` simulations for `Rvalue.binaryOp` comparisons (`eq`..`ge` -> `bool`) -/
/-- **Copy/copy float comparison real-step simulation** (`_d = Op(copy _l, copy _r) -> bool`). -/
theorem step_float_cmp_copy_copy_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx lhsIdx rhsIdx : Local} {bop : MirAst.BinOp} {span : String} (hbop : isFloatCmpBinOp bop = true) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩)
    {dstDecl lhsDecl rhsDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl)
    (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl) (hf_lhs : ieeeFormatOfTy? lhsDecl.ty = some f) (hf_rhs : ieeeFormatOfTy? rhsDecl.ty = some f)
    (hdst_bool : dstDecl.ty.kind = .bool) (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame lhsIdx ∧ IsImmediateFrameLocal topFrame rhsIdx) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () m) := by
  rcases binary_copy_copy_float_setup hstate hphase nondet chooseNaN hbb hstmt hdecl_dst hdecl_lhs hdecl_rhs hf_lhs hf_rhs himm with
    hub | ⟨lSc, rSc, hslot_l, hslot_r⟩
  · exact hub
  · obtain ⟨_, _, _, _, _, hcal, _, _, _, _, _, _⟩ := id hstate
    obtain ⟨tf, tfc, lMsc, rMsc, hframes, hbody, hloc, hstate_c, himm_dc, hlrel, hrrel, hlbw, hrbw, hm_eval⟩ :=
      binary_copy_copy_float_init_eval hstate (bop := bop) (span := span) hdecl_dst hdecl_lhs hdecl_rhs hf_lhs hf_rhs hslot_l hslot_r himm
    have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
    obtain ⟨res, hres, _, hfb⟩ := floatOps_binary_cmp_eq body.layouts nondet chooseNaN hbop hf_lhs hf_rhs hlrel hrrel hlbw hrbw
    have hrv_a : evalRvalue s.frame.locals (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)) s.memory
        body.localDecls body.layouts = .ok (.scalar (boolToScalar res)) s.frame.locals s.memory := by
      rw [evalRvalue_binaryOp_float _ _ _ bop _ _ lSc rSc _ _ _ hnot_off (evalOperand_copy_scalar_ok hslot_l) (evalOperand_copy_scalar_ok hslot_r)
        (by rw [operandTy_copy_local hdecl_lhs, isFloatOptTy_some_of_ieee hf_lhs]; rfl),
        operandTy_copy_local hdecl_lhs, operandTy_copy_local hdecl_rhs,
        evalFloatScalarBinOp_of_fmt bop lSc rSc lhsDecl.ty rhsDecl.ty f s.frame.locals s.memory hf_lhs hf_rhs hlbw hrbw]
      unfold evalFloatBinOp; rw [hres]
    have hbool_lay : translateTy { kind := .bool, layoutIdx := 0 } emptyLayoutTable = translateTy dstDecl.ty body.layouts :=
      (translateTy_bool_eq hdst_bool body.layouts).symm
    have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m =
        Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromBool res))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩) { m with stack := ⟨#[tfc]⟩ } := by
      rw [hm_eval nondet chooseNaN]; unfold Miri.Interpreter.runRvalue
      rw [hfb, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hbool_lay _)]
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
    exact finish_write_immediate_from_mid_hooks _ hframes hbody hloc hstate_c rfl hbb hstmt
      hdecl_dst himm_dc hrv_a hm_write (bool_dst_localRel hdst_bool res)
/-- **Constant/constant float comparison real-step simulation** (`_d = Op(const c₁, const c₂)`). -/
theorem step_float_cmp_const_const_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx : Local} {bop : MirAst.BinOp} {c₁ c₂ : ConstOperand} {span : String}
    (hbop : isFloatCmpBinOp bop = true) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c₁) (.constant c₂)), span⟩) {dstDecl : LocalDecl} {f : IeeeFormat}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hf₁ : ieeeFormatOfTy? c₁.ty = some f) (hf₂ : ieeeFormatOfTy? c₂.ty = some f) (hdst_bool : dstDecl.ty.kind = .bool)
    {sc₁ sc₂ : MirAst.ScalarInt} (hv₁ : c₁.val = .scalar (.int sc₁)) (hv₂ : c₂.val = .scalar (.int sc₂)) (hsz₁ : sc₁.sizeBytes = f.byteWidth) (hsz₂ : sc₂.sizeBytes = f.byteWidth)
    (hcan₁ : sc₁.bits < scalarModulus sc₁.sizeBytes) (hcan₂ : sc₂.bits < scalarModulus sc₂.sizeBytes)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨_, _, _, _, _, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨tf, hlt_d, msc₁, msc₂, hframes, hbody, hloc, hstate_a, hrel₁, hrel₂, hm_eval⟩ :=
    binary_const_const_float_eval hstate nondet chooseNaN hdecl_dst hf₁ hf₂ hv₁ hv₂ hsz₁ hsz₂ hcan₁ hcan₂
  have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
  obtain ⟨res, hres, _, hfb⟩ := floatOps_binary_cmp_eq body.layouts nondet chooseNaN hbop hf₁ hf₂ hrel₁ hrel₂ hsz₁ hsz₂
  have hrv_a : evalRvalue s.frame.locals (.binaryOp bop (.constant c₁) (.constant c₂)) s.memory body.localDecls body.layouts =
      .ok (.scalar (boolToScalar res)) s.frame.locals s.memory := by
    rw [evalRvalue_binaryOp_float _ _ _ bop _ _ sc₁ sc₂ _ _ _ hnot_off (evalOperand_const_scalar_ok hv₁) (evalOperand_const_scalar_ok hv₂)
      (by simp [operandTy, isFloatOptTy_some_of_ieee hf₁])]
    dsimp only [operandTy]; rw [evalFloatScalarBinOp_of_fmt bop sc₁ sc₂ c₁.ty c₂.ty f s.frame.locals s.memory hf₁ hf₂ hsz₁ hsz₂]
    unfold evalFloatBinOp; rw [hres]
  have hbool_lay : translateTy { kind := .bool, layoutIdx := 0 } emptyLayoutTable = translateTy dstDecl.ty body.layouts :=
    (translateTy_bool_eq hdst_bool body.layouts).symm
  have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c₁) (.constant c₂)), span⟩) m =
      Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromBool res))
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)]⟩ } := by
    rw [hm_eval]; unfold Miri.Interpreter.runRvalue
    rw [hfb, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hbool_lay _)]
  rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
  exact finish_write_immediate_from_mid_hooks _ hframes hbody hloc hstate_a rfl hbb hstmt
    hdecl_dst ((himm tf hframes).cache_layout hlt_d _) hrv_a hm_write (bool_dst_localRel hdst_bool res)
/-! ### 3.4 Real `Step.step` simulations for `Rvalue.binaryOp` arithmetic (deterministic & nondeterministic) -/
/-- **Deterministic copy/copy float arithmetic real-step simulation** (`floatNondeterministic = false`). -/
theorem step_float_arith_copy_copy_deterministic_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx lhsIdx rhsIdx : Local} {bop : MirAst.BinOp} {span : String} (hbop : isFloatArithBinOp bop = true) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩)
    {dstDecl lhsDecl rhsDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl)
    (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl) (hf_lhs : ieeeFormatOfTy? lhsDecl.ty = some f) (hf_rhs : ieeeFormatOfTy? rhsDecl.ty = some f)
    (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f) (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame lhsIdx ∧ IsImmediateFrameLocal topFrame rhsIdx) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) () m) := by
  rcases binary_copy_copy_float_setup hstate hphase false chooseNaN hbb hstmt hdecl_dst hdecl_lhs hdecl_rhs hf_lhs hf_rhs himm with
    hub | ⟨lSc, rSc, hslot_l, hslot_r⟩
  · exact hub
  · obtain ⟨_, _, _, _, _, hcal, _, _, _, _, _, _⟩ := id hstate
    obtain ⟨tf, tfc, lMsc, rMsc, hframes, hbody, hloc, hstate_c, himm_dc, hlrel, hrrel, hlbw, hrbw, hm_eval⟩ :=
      binary_copy_copy_float_init_eval hstate (bop := bop) (span := span) hdecl_dst hdecl_lhs hdecl_rhs hf_lhs hf_rhs hslot_l hslot_r himm
    have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
    have hdstT : translateTy lhsDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by
      rw [translateTy_of_ieeeFormatOfTy? hf_lhs, translateTy_of_ieeeFormatOfTy? hf_dst]
    obtain ⟨baseBits, msc', _, hbin, hrel', hfb⟩ :=
      floatOps_binary_arith_deterministic_eq body.layouts chooseNaN hbop hf_lhs hf_rhs hlrel hrrel hlbw hrbw
    have hrv_a : evalRvalue s.frame.locals (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)) s.memory
        body.localDecls body.layouts = .ok (.scalar ⟨baseBits, f.byteWidth⟩) s.frame.locals s.memory := by
      rw [evalRvalue_binaryOp_float _ _ _ bop _ _ lSc rSc _ _ _ hnot_off (evalOperand_copy_scalar_ok hslot_l) (evalOperand_copy_scalar_ok hslot_r)
        (by rw [operandTy_copy_local hdecl_lhs, isFloatOptTy_some_of_ieee hf_lhs]; rfl),
        operandTy_copy_local hdecl_lhs, operandTy_copy_local hdecl_rhs,
        evalFloatScalarBinOp_of_fmt bop lSc rSc lhsDecl.ty rhsDecl.ty f s.frame.locals s.memory hf_lhs hf_rhs hlbw hrbw, hbin]
    have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m =
        Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩) { m with stack := ⟨#[tfc]⟩ } := by
      rw [hm_eval false chooseNaN]; unfold Miri.Interpreter.runRvalue
      rw [hfb, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
    have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes f.byteWidth := by
      rw [translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
    exact finish_write_immediate_from_mid_hooks _ hframes hbody hloc hstate_c rfl hbb hstmt
      hdecl_dst himm_dc hrv_a hm_write (floatCast_dst_localRel (Or.inl ⟨f, hf_dst⟩) hrel' hdst_sz)
/-- **Deterministic constant/constant float arithmetic real-step simulation**. -/
theorem step_float_arith_const_const_deterministic_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx : Local} {bop : MirAst.BinOp} {c₁ c₂ : ConstOperand} {span : String}
    (hbop : isFloatArithBinOp bop = true) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c₁) (.constant c₂)), span⟩) {dstDecl : LocalDecl} {f : IeeeFormat}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hf₁ : ieeeFormatOfTy? c₁.ty = some f) (hf₂ : ieeeFormatOfTy? c₂.ty = some f) (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f)
    {sc₁ sc₂ : MirAst.ScalarInt} (hv₁ : c₁.val = .scalar (.int sc₁)) (hv₂ : c₂.val = .scalar (.int sc₂)) (hsz₁ : sc₁.sizeBytes = f.byteWidth) (hsz₂ : sc₂.sizeBytes = f.byteWidth)
    (hcan₁ : sc₁.bits < scalarModulus sc₁.sizeBytes) (hcan₂ : sc₂.bits < scalarModulus sc₂.sizeBytes)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) () m) := by
  obtain ⟨_, _, _, _, _, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨tf, hlt_d, msc₁, msc₂, hframes, hbody, hloc, hstate_a, hrel₁, hrel₂, hm_eval⟩ :=
    binary_const_const_float_eval hstate false chooseNaN hdecl_dst hf₁ hf₂ hv₁ hv₂ hsz₁ hsz₂ hcan₁ hcan₂
  have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
  have hdstT : translateTy c₁.ty body.layouts = translateTy dstDecl.ty body.layouts := by
    rw [translateTy_of_ieeeFormatOfTy? hf₁, translateTy_of_ieeeFormatOfTy? hf_dst]
  obtain ⟨baseBits, msc', _, hbin, hrel', hfb⟩ :=
    floatOps_binary_arith_deterministic_eq body.layouts chooseNaN hbop hf₁ hf₂ hrel₁ hrel₂ hsz₁ hsz₂
  have hrv_a : evalRvalue s.frame.locals (.binaryOp bop (.constant c₁) (.constant c₂)) s.memory body.localDecls body.layouts =
      .ok (.scalar ⟨baseBits, f.byteWidth⟩) s.frame.locals s.memory := by
    rw [evalRvalue_binaryOp_float _ _ _ bop _ _ sc₁ sc₂ _ _ _ hnot_off (evalOperand_const_scalar_ok hv₁) (evalOperand_const_scalar_ok hv₂)
      (by simp [operandTy, isFloatOptTy_some_of_ieee hf₁])]
    dsimp only [operandTy]; rw [evalFloatScalarBinOp_of_fmt bop sc₁ sc₂ c₁.ty c₂.ty f s.frame.locals s.memory hf₁ hf₂ hsz₁ hsz₂, hbin]
  have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c₁) (.constant c₂)), span⟩) m =
      Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc'))
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)]⟩ } := by
    rw [hm_eval]; unfold Miri.Interpreter.runRvalue
    rw [hfb, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
  have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes f.byteWidth := by
    rw [translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
  rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
  exact finish_write_immediate_from_mid_hooks _ hframes hbody hloc hstate_a rfl hbb hstmt
    hdecl_dst ((himm tf hframes).cache_layout hlt_d _) hrv_a hm_write
    (floatCast_dst_localRel (Or.inl ⟨f, hf_dst⟩) hrel' hdst_sz)
private theorem operandTy_const (decls : List LocalDecl) (layouts : LayoutTable) (c : ConstOperand) :
    operandTy decls layouts (.constant c) = some c.ty := rfl
/-- **Deterministic copy/constant float arithmetic real-step simulation** (`_d = Op(copy _l, const c)`, covering non-commutative `.sub`/`.div`/`.rem` and `.dead`/`.uninit` UB lockstep). -/
theorem step_float_arith_copy_const_deterministic_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx lhsIdx : Local} {bop : MirAst.BinOp} {c : ConstOperand} {span : String}
    (hbop : isFloatArithBinOp bop = true) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.constant c)), span⟩)
    {dstDecl lhsDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl)
    (hf_lhs : ieeeFormatOfTy? lhsDecl.ty = some f) (hf_c : ieeeFormatOfTy? c.ty = some f) (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f)
    {sc : MirAst.ScalarInt} (hv_c : c.val = .scalar (.int sc)) (hsz_c : sc.sizeBytes = f.byteWidth) (hcan_c : sc.bits < scalarModulus sc.sizeBytes)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame lhsIdx) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_l⟩ := himm tf hframes
  have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
  have hm_stmt := evalStatement_assign_binaryOp_floatArith_eq body.localDecls body.layouts false chooseNaN dstIdx bop (.copy ⟨lhsIdx, .nil⟩) (.constant c) span m
  rw [translateOperand_copy_unproj] at hm_stmt
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_l, mls_l, _, hlt_la, hslot_l, hmls_l, hmls_l_eq, hloc_l⟩ := hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_lhs
  let tfb := cacheFrameLocalLayout tfa lhsIdx hlt_la (translateTy lhsDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_lhs hlt_la
  rcases hloc_l.floatCast_immediate_cases (Or.inl ⟨f, hf_lhs⟩) ((himm_l.cache_layout hlt_d _) mls_l hmls_l) with ⟨hsl, hml⟩ | ⟨hsl, hml⟩ | ⟨lSc, lMsc, hsl, hlrel, hlsz, hml⟩
  · subst hsl
    have hl_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none)
      rfl hlt_la hdecl_lhs (by rw [hmls_l_eq]; rcases mls_l with ⟨v0, l0⟩; dsimp only at hml; subst hml; rfl) hloc_l.cachedLayout_eq
    have ha_ub : stepMirFn body s = .fail .ub := by rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_l]
    have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.constant c)), span⟩) m = ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hl_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact .ub _ _
  · subst hsl
    have hl_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none)
      rfl hlt_la hdecl_lhs (by rw [hmls_l_eq]; rcases mls_l with ⟨v0, l0⟩; dsimp only at hml; subst hml; rfl) hloc_l.cachedLayout_eq
    have ha_ub : stepMirFn body s = .fail .ub := by rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_l]
    have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.constant c)), span⟩) m = ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_uninit_eq]; rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact .ub _ _
  · subst hsl; rw [translateTy_of_ieeeFormatOfTy? hf_lhs body.layouts] at hlsz
    have hlbw := sizeBytes_of_float_layout hlrel.validBytes hlsz
    have hl_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none)
      rfl hlt_la hdecl_lhs (by rw [hmls_l_eq]; rcases mls_l with ⟨v0, l0⟩; dsimp only at hml; subst hml; rfl) hloc_l.cachedLayout_eq
    obtain ⟨rMsc, hrrel, hr_ok⟩ := annealEvalOperand_constant_float_ok (body := body) (m := { m with stack := ⟨#[tfb]⟩ }) rfl hf_c hv_c hsz_c hcan_c
      (if (translateBinOp bop).rightHomogeneous then some (translateTy lhsDecl.ty body.layouts) else none)
    have hdstT : translateTy lhsDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by rw [translateTy_of_ieeeFormatOfTy? hf_lhs, translateTy_of_ieeeFormatOfTy? hf_dst]
    obtain ⟨baseBits, msc', _, hbin, hrel', hfb⟩ := floatOps_binary_arith_deterministic_eq body.layouts chooseNaN hbop hf_lhs hf_c hlrel hrrel hlbw hsz_c
    have hrv_a : evalRvalue s.frame.locals (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.constant c)) s.memory body.localDecls body.layouts = .ok (.scalar ⟨baseBits, f.byteWidth⟩) s.frame.locals s.memory := by
      rw [evalRvalue_binaryOp_float _ _ _ bop _ _ lSc sc _ _ _ hnot_off (evalOperand_copy_scalar_ok hslot_l) (evalOperand_const_scalar_ok hv_c)
        (by rw [operandTy_copy_local hdecl_lhs, isFloatOptTy_some_of_ieee hf_lhs]; rfl), operandTy_copy_local hdecl_lhs, operandTy_const,
        evalFloatScalarBinOp_of_fmt bop lSc sc lhsDecl.ty c.ty f s.frame.locals s.memory hf_lhs hf_c hlbw hsz_c, hbin]
    have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.constant c)), span⟩) m =
        Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩) { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_scalar, pure_bind, EStateM.bind_eq_ok hr_ok, annealReadImmediate_scalar, pure_bind,
        scalarOps_binary_float_eq _ _ _ _ hf_lhs hf_c, hfb, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
    have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes f.byteWidth := by rw [translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
    exact finish_write_immediate_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq hstate_b rfl hbb hstmt
      hdecl_dst ((himm_d.cache_layout hlt_d _).cache_layout hlt_la _) hrv_a hm_write (floatCast_dst_localRel (Or.inl ⟨f, hf_dst⟩) hrel' hdst_sz)
/-- **Deterministic constant/copy float arithmetic real-step simulation** (`_d = Op(const c, copy _r)`, covering non-commutative `.sub`/`.div`/`.rem` and `.dead`/`.uninit` UB lockstep). -/
theorem step_float_arith_const_copy_deterministic_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx rhsIdx : Local} {bop : MirAst.BinOp} {c : ConstOperand} {span : String}
    (hbop : isFloatArithBinOp bop = true) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c) (.copy ⟨rhsIdx, .nil⟩)), span⟩)
    {dstDecl rhsDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl)
    (hf_c : ieeeFormatOfTy? c.ty = some f) (hf_rhs : ieeeFormatOfTy? rhsDecl.ty = some f) (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f)
    {sc : MirAst.ScalarInt} (hv_c : c.val = .scalar (.int sc)) (hsz_c : sc.sizeBytes = f.byteWidth) (hcan_c : sc.bits < scalarModulus sc.sizeBytes)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame rhsIdx) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_r⟩ := himm tf hframes
  have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
  have hm_stmt := evalStatement_assign_binaryOp_floatArith_eq body.localDecls body.layouts false chooseNaN dstIdx bop (.constant c) (.copy ⟨rhsIdx, .nil⟩) span m
  rw [translateOperand_copy_unproj] at hm_stmt
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨lMsc, hlrel, hl_ok⟩ := annealEvalOperand_constant_float_ok (body := body) (m := { m with stack := ⟨#[tfa]⟩ }) rfl hf_c hv_c hsz_c hcan_c
    (if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none)
  obtain ⟨slot_r, mls_r, _, hlt_ra, hslot_r, hmls_r, hmls_r_eq, hloc_r⟩ := hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_rhs
  let tfb := cacheFrameLocalLayout tfa rhsIdx hlt_ra (translateTy rhsDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_rhs hlt_ra
  rcases hloc_r.floatCast_immediate_cases (Or.inl ⟨f, hf_rhs⟩) ((himm_r.cache_layout hlt_d _) mls_r hmls_r) with ⟨hsr, hmr⟩ | ⟨hsr, hmr⟩ | ⟨rSc, rMsc, hsr, hrrel, hrsz, hmr⟩
  · subst hsr
    have hr_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).rightHomogeneous then some (translateTy c.ty body.layouts) else none)
      rfl hlt_ra hdecl_rhs (by rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr; subst hmr; rfl) hloc_r.cachedLayout_eq
    have ha_ub : stepMirFn body s = .fail .ub := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; unfold evalStmt evalRvalue; dsimp only []
      rw [evalOperand_const_scalar_ok hv_c]; dsimp only []; unfold evalOperand; dsimp only []; rw [hslot_r]
    have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m = ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_scalar, pure_bind, EStateM.bind_eq_error hr_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact .ub _ _
  · subst hsr
    have hr_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).rightHomogeneous then some (translateTy c.ty body.layouts) else none)
      rfl hlt_ra hdecl_rhs (by rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr; subst hmr; rfl) hloc_r.cachedLayout_eq
    have ha_ub : stepMirFn body s = .fail .ub := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; unfold evalStmt evalRvalue; dsimp only []
      rw [evalOperand_const_scalar_ok hv_c]; dsimp only []; unfold evalOperand; dsimp only []; rw [hslot_r]
    have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m = ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_scalar, pure_bind, EStateM.bind_eq_ok hr_ok, annealReadImmediate_uninit_eq]; rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact .ub _ _
  · subst hsr; rw [translateTy_of_ieeeFormatOfTy? hf_rhs body.layouts] at hrsz
    have hrbw := sizeBytes_of_float_layout hrrel.validBytes hrsz
    have hr_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).rightHomogeneous then some (translateTy c.ty body.layouts) else none)
      rfl hlt_ra hdecl_rhs (by rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr; subst hmr; rfl) hloc_r.cachedLayout_eq
    have hdstT : translateTy c.ty body.layouts = translateTy dstDecl.ty body.layouts := by rw [translateTy_of_ieeeFormatOfTy? hf_c, translateTy_of_ieeeFormatOfTy? hf_dst]
    obtain ⟨baseBits, msc', _, hbin, hrel', hfb⟩ := floatOps_binary_arith_deterministic_eq body.layouts chooseNaN hbop hf_c hf_rhs hlrel hrrel hsz_c hrbw
    have hrv_a : evalRvalue s.frame.locals (.binaryOp bop (.constant c) (.copy ⟨rhsIdx, .nil⟩)) s.memory body.localDecls body.layouts = .ok (.scalar ⟨baseBits, f.byteWidth⟩) s.frame.locals s.memory := by
      rw [evalRvalue_binaryOp_float _ _ _ bop _ _ sc rSc _ _ _ hnot_off (evalOperand_const_scalar_ok hv_c) (evalOperand_copy_scalar_ok hslot_r)
        (by rw [operandTy_const, isFloatOptTy_some_of_ieee hf_c]; rfl), operandTy_const, operandTy_copy_local hdecl_rhs,
        evalFloatScalarBinOp_of_fmt bop sc rSc c.ty rhsDecl.ty f s.frame.locals s.memory hf_c hf_rhs hsz_c hrbw, hbin]
    have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m =
        Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩) { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_scalar, pure_bind, EStateM.bind_eq_ok hr_ok, annealReadImmediate_scalar, pure_bind,
        scalarOps_binary_float_eq _ _ _ _ hf_c hf_rhs, hfb, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
    have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes f.byteWidth := by rw [translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
    exact finish_write_immediate_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq hstate_b rfl hbb hstmt
      hdecl_dst ((himm_d.cache_layout hlt_d _).cache_layout hlt_ra _) hrv_a hm_write (floatCast_dst_localRel (Or.inl ⟨f, hf_dst⟩) hrel' hdst_sz)
/-- **Deterministic move/copy float arithmetic real-step simulation** (`lhsIdx ≠ rhsIdx`). -/
theorem step_float_arith_move_copy_deterministic_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx lhsIdx rhsIdx : Local} {bop : MirAst.BinOp} {span : String} (hbop : isFloatArithBinOp bop = true) (hlr_ne : lhsIdx ≠ rhsIdx)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.move ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩)
    {dstDecl lhsDecl rhsDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl)
    (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl) (hf_lhs : ieeeFormatOfTy? lhsDecl.ty = some f) (hf_rhs : ieeeFormatOfTy? rhsDecl.ty = some f)
    (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f) {lSc rSc : MirAst.ScalarInt} (hslot_l : get? s.frame.locals lhsIdx = some (.init (.scalar lSc)))
    (hslot_r : get? s.frame.locals rhsIdx = some (.init (.scalar rSc))) (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame lhsIdx ∧ IsImmediateFrameLocal topFrame rhsIdx) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate; obtain ⟨himm_d, himm_l, himm_r⟩ := himm tf hframes
  have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
  have hdstT : translateTy lhsDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by rw [translateTy_of_ieeeFormatOfTy? hf_lhs, translateTy_of_ieeeFormatOfTy? hf_dst]
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts); have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_l0, mls_l, _, hlt_la, hslot_l0, hmls_l, hmls_l_eq, hloc_l⟩ := hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_lhs
  have hslot_l_eq : slot_l0 = .init (.scalar lSc) := Option.some.inj (hslot_l0.symm.trans hslot_l); subst hslot_l_eq
  let tfb := cacheFrameLocalLayout tfa lhsIdx hlt_la (translateTy lhsDecl.ty body.layouts)
  have hlt_lb : lhsIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_la
  have hstate_b := hstate_a.cache_layout rfl hdecl_lhs hlt_la
  rcases hloc_l.floatCast_immediate_cases (Or.inl ⟨f, hf_lhs⟩) ((himm_l.cache_layout hlt_d _) mls_l hmls_l) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨lSc', lMsc, hl_eq, hlrel, hlsz, hml⟩
  · cases h
  · cases h
  · injection hl_eq with hl_eq'; injection hl_eq' with hl_eq''; subst hl_eq''
    have hl_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none)
      rfl hlt_la hdecl_lhs (by rw [hmls_l_eq]; rcases mls_l with ⟨v0, l0⟩; dsimp only at hml; subst hml; rfl) hloc_l.cachedLayout_eq
    have hstate_deinit := hstate_b.deinit_immediate_local rfl hdecl_lhs hslot_l (by simp) ((himm_l.cache_layout hlt_d _).cache_layout hlt_la _) hlt_lb
    let tfb' := deinitFrameLocal tfb lhsIdx hlt_lb
    obtain ⟨slot_r0, mls_r, _, hlt_rb, hslot_r0, hmls_r, hmls_r_eq, hloc_r⟩ := hstate_deinit.frame_rel_singleton rfl |>.lookup_local hdecl_rhs
    have hslot_r_set : get? (s.frame.locals.set lhsIdx .uninit) rhsIdx = some (.init (.scalar rSc)) := by rw [get?_eq_getElem?, List.getElem?_set_ne hlr_ne, ← get?_eq_getElem?]; exact hslot_r
    have hslot_r_eq : slot_r0 = .init (.scalar rSc) := Option.some.inj (hslot_r0.symm.trans hslot_r_set); subst hslot_r_eq
    let tfc := cacheFrameLocalLayout tfb' rhsIdx hlt_rb (translateTy rhsDecl.ty body.layouts); have hstate_c := hstate_deinit.cache_layout rfl hdecl_rhs hlt_rb
    rcases hloc_r.floatCast_immediate_cases (Or.inl ⟨f, hf_rhs⟩) ((((himm_r.cache_layout hlt_d _).cache_layout hlt_la _).deinit_local hlt_lb) mls_r hmls_r) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨rSc', rMsc, hr_eq, hrrel, hrsz, hmr⟩
    · cases h
    · cases h
    · injection hr_eq with hr_eq'; injection hr_eq' with hr_eq''; subst hr_eq''
      rw [translateTy_of_ieeeFormatOfTy? hf_lhs body.layouts] at hlsz; rw [translateTy_of_ieeeFormatOfTy? hf_rhs body.layouts] at hrsz
      have hlbw := sizeBytes_of_float_layout hlrel.validBytes hlsz; have hrbw := sizeBytes_of_float_layout hrrel.validBytes hrsz
      obtain ⟨baseBits, msc', _, hbin, hrel', hfb⟩ := floatOps_binary_arith_deterministic_eq body.layouts chooseNaN hbop hf_lhs hf_rhs hlrel hrrel hlbw hrbw
      have hr_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfb']⟩ }) (known := if (translateBinOp bop).rightHomogeneous then some (translateTy lhsDecl.ty body.layouts) else none)
        rfl hlt_rb hdecl_rhs (by rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr; subst hmr; rfl) hloc_r.cachedLayout_eq
      have hrv_a : evalRvalue s.frame.locals (.binaryOp bop (.move ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)) s.memory body.localDecls body.layouts = .ok (.scalar ⟨baseBits, f.byteWidth⟩) (s.frame.locals.set lhsIdx .uninit) s.memory := by
        rw [evalRvalue_binaryOp_float _ _ _ bop _ _ lSc rSc _ _ _ hnot_off (evalOperand_move_scalar_ok hslot_l) (evalOperand_copy_scalar_ok hslot_r_set)
          (by rw [operandTy_move_local hdecl_lhs, isFloatOptTy_some_of_ieee hf_lhs]; rfl), operandTy_move_local hdecl_lhs, operandTy_copy_local hdecl_rhs,
          evalFloatScalarBinOp_of_fmt bop lSc rSc lhsDecl.ty rhsDecl.ty f (s.frame.locals.set lhsIdx .uninit) s.memory hf_lhs hf_rhs hlbw hrbw, hbin]
      have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.move ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m =
          Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩) { m with stack := ⟨#[tfc]⟩ } := by
        rw [evalStatement_assign_binaryOp_floatArith_eq, translateOperand_move_unproj, translateOperand_copy_unproj]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_scalar, pure_bind, EStateM.bind_eq_ok hr_ok, annealReadImmediate_scalar, pure_bind,
          scalarOps_binary_float_eq _ _ _ _ hf_lhs hf_rhs, hfb, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
      have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes f.byteWidth := by rw [translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
      rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
      exact finish_write_immediate_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq hstate_c rfl hbb hstmt
        hdecl_dst ((((himm_d.cache_layout hlt_d _).cache_layout hlt_la _).deinit_local hlt_lb).cache_layout hlt_rb _) hrv_a hm_write (floatCast_dst_localRel (Or.inl ⟨f, hf_dst⟩) hrel' hdst_sz)
/-- **Deterministic indirect-destination float arithmetic real-step simulation**. -/
theorem step_float_arith_const_const_indirect_dst_deterministic_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx : Local} {bop : MirAst.BinOp} {c₁ c₂ : ConstOperand} {span : String}
    (hbop : isFloatArithBinOp bop = true) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c₁) (.constant c₂)), span⟩) {dstDecl : LocalDecl} {f : IeeeFormat}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hf₁ : ieeeFormatOfTy? c₁.ty = some f) (hf₂ : ieeeFormatOfTy? c₂.ty = some f) (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f)
    {sc₁ sc₂ : MirAst.ScalarInt} (hv₁ : c₁.val = .scalar (.int sc₁)) (hv₂ : c₂.val = .scalar (.int sc₂)) (hsz₁ : sc₁.sizeBytes = f.byteWidth) (hsz₂ : sc₂.sizeBytes = f.byteWidth)
    (hcan₁ : sc₁.bits < scalarModulus sc₁.sizeBytes) (hcan₂ : sc₂.bits < scalarModulus sc₂.sizeBytes) {dstAllocId : Miri.Memory.AllocId}
    {dstLocalAlloc : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind} (hdid_lt : dstAllocId.value.toNat < 2 ^ 32)
    (hdbase : m.machine.lookupBaseAddr dstAllocId = some (annealStackBaseAddr dstAllocId))
    (hdfind : m.machine.memory.live.find? (fun x => x.1 == dstAllocId) = some (dstAllocId, dstLocalAlloc))
    (hdshape : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size dstLocalAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] → ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace dstAllocId)), lay⟩) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) () m) := by
  obtain ⟨_, _, _, _, _, hcal, _, _, _, _, _, _⟩ := id hstate
  have hnot_dst := hstate.not_mem_allocMap_of_ieeeFormatOfTy? hdecl_dst hf_dst
  obtain ⟨tf, hlt_d, msc₁, msc₂, hframes, hbody, hloc, hstate_a, hrel₁, hrel₂, hm_eval⟩ :=
    binary_const_const_float_eval hstate false chooseNaN hdecl_dst hf₁ hf₂ hv₁ hv₂ hsz₁ hsz₂ hcan₁ hcan₂
  obtain ⟨lay_d0, hlay_d0⟩ := hind_dst tf hframes
  have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
  have hdstT : translateTy c₁.ty body.layouts = translateTy dstDecl.ty body.layouts := by
    rw [translateTy_of_ieeeFormatOfTy? hf₁, translateTy_of_ieeeFormatOfTy? hf_dst]
  obtain ⟨baseBits, msc', _, hbin, hrel', hfb⟩ :=
    floatOps_binary_arith_deterministic_eq body.layouts chooseNaN hbop hf₁ hf₂ hrel₁ hrel₂ hsz₁ hsz₂
  have hrv_a : evalRvalue s.frame.locals (.binaryOp bop (.constant c₁) (.constant c₂)) s.memory body.localDecls body.layouts =
      .ok (.scalar ⟨baseBits, f.byteWidth⟩) s.frame.locals s.memory := by
    rw [evalRvalue_binaryOp_float _ _ _ bop _ _ sc₁ sc₂ _ _ _ hnot_off (evalOperand_const_scalar_ok hv₁) (evalOperand_const_scalar_ok hv₂)
      (by simp [operandTy, isFloatOptTy_some_of_ieee hf₁])]
    dsimp only [operandTy]; rw [evalFloatScalarBinOp_of_fmt bop sc₁ sc₂ c₁.ty c₂.ty f s.frame.locals s.memory hf₁ hf₂ hsz₁ hsz₂, hbin]
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts false chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c₁) (.constant c₂)), span⟩) m =
      Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc'))
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩) { m with stack := ⟨#[tfa]⟩ } := by
    rw [hm_eval]; unfold Miri.Interpreter.runRvalue
    rw [hfb, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
  have hlay_d : tfa.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace dstAllocId)), some (translateTy dstDecl.ty body.layouts)⟩ := by
    dsimp [tfa, cacheFrameLocalLayout]; rw [Array.getElem?_set_self hlt_d]
    rw [Array.getElem?_eq_getElem hlt_d] at hlay_d0; injection hlay_d0 with hm0; rw [hm0]
  have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes f.byteWidth := by
    rw [translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
  rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]
  exact finish_write_unpromoted_indirect_from_mid_hooks _ hframes hbody hloc hstate_a rfl hbb hstmt
    hdecl_dst (Or.inl ⟨f, hf_dst⟩) hnot_dst hlay_d hdid_lt hdbase hdfind hdshape hrel' hdst_sz hrv_a hm_write
/-- **Nondeterministic float arithmetic real-step SOUNDNESS**: for ANY valid `chooseNaN`, `Step.step` steps into a `StepRelLM3_1`-related successor storing an `outSc` admitted by `EvalRvalueFloatRel .nondeterministic policy` (for EVERY `policy`). -/
theorem step_float_arith_copy_copy_nondet_soundness
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) (hvalid : ValidBinaryChooseNaN chooseNaN)
    {bb : BasicBlockData} {dstIdx lhsIdx rhsIdx : Local} {bop : MirAst.BinOp} {span : String} (hbop : isFloatArithBinOp bop = true) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩)
    {dstDecl lhsDecl rhsDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl)
    (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl) (hf_lhs : ieeeFormatOfTy? lhsDecl.ty = some f) (hf_rhs : ieeeFormatOfTy? rhsDecl.ty = some f)
    (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f) (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead) {lSc rSc : MirAst.ScalarInt}
    (hslot_l : get? s.frame.locals lhsIdx = some (.init (.scalar lSc))) (hslot_r : get? s.frame.locals rhsIdx = some (.init (.scalar rSc))) (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame lhsIdx ∧ IsImmediateFrameLocal topFrame rhsIdx) :
    ∃ outSc,
      (∀ policy, EvalRvalueFloatRel .nondeterministic policy s.frame.locals (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)) s.memory body.localDecls body.layouts (.ok (.scalar outSc) s.frame.locals s.memory)) ∧
      StepRelLM3_1 body m allocMap (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar outSc))) s.memory))
        (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts true chooseNaN) () m) := by
  obtain ⟨tf, tfc, lMsc, rMsc, hframes, hbody, hloc, hstate_c, himm_dc, hlrel, hrrel, hlbw, hrbw, hm_eval⟩ := binary_copy_copy_float_init_eval hstate (bop := bop) (span := span) hdecl_dst hdecl_lhs hdecl_rhs hf_lhs hf_rhs hslot_l hslot_r himm
  have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
  have hdstT : translateTy lhsDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by
    rw [translateTy_of_ieeeFormatOfTy? hf_lhs, translateTy_of_ieeeFormatOfTy? hf_dst]
  obtain ⟨outSc, msc', hrel_t, hrel', hfb_st⟩ :=
    floatOps_binary_arith_any_chooseNaN_rel body.layouts chooseNaN hvalid hbop hf_lhs hf_rhs hlrel hrrel hlbw hrbw { m with stack := ⟨#[tfc]⟩ }
  obtain ⟨baseBits, hbase⟩ := (evalFloatArithBase_isSome_iff bop f lSc.bits rSc.bits).mpr hbop
  have hbin : evalFloatBinOp bop f lSc.bits rSc.bits = .some ⟨baseBits, f.byteWidth⟩ := by
    unfold evalFloatBinOp; rw [evalFloatCmp_of_arith bop f _ _ hbop, hbase]
  have hrv_a : evalRvalue s.frame.locals (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)) s.memory
      body.localDecls body.layouts = .ok (.scalar ⟨baseBits, f.byteWidth⟩) s.frame.locals s.memory := by
    rw [evalRvalue_binaryOp_float _ _ _ bop _ _ lSc rSc _ _ _ hnot_off (evalOperand_copy_scalar_ok hslot_l) (evalOperand_copy_scalar_ok hslot_r)
      (by rw [operandTy_copy_local hdecl_lhs, isFloatOptTy_some_of_ieee hf_lhs]; rfl),
      operandTy_copy_local hdecl_lhs, operandTy_copy_local hdecl_rhs,
      evalFloatScalarBinOp_of_fmt bop lSc rSc lhsDecl.ty rhsDecl.ty f s.frame.locals s.memory hf_lhs hf_rhs hlbw hrbw, hbin]
  have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts true chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m =
      Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc'))
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩) { m with stack := ⟨#[tfc]⟩ } := by
    rw [hm_eval true chooseNaN]; unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hfb_st, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
  have hout_sz : outSc.sizeBytes = f.byteWidth := by
    rcases (EvalFloatBinOpRel_arith_iff .nondeterministic bop f lSc.bits rSc.bits outSc hbop).mp hrel_t with
      ⟨_, _, ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩⟩ <;> rfl
  have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes outSc.sizeBytes := by
    rw [hout_sz, translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
  have hfin := finish_write_immediate_split_hooks _ hframes hbody hloc hstate_c rfl hbb hstmt
    hdecl_dst himm_dc hlive_dst hrv_a hm_write (floatCast_dst_localRel (Or.inl ⟨f, hf_dst⟩) hrel' hdst_sz)
  refine ⟨outSc, fun policy => ?_, hfin.2⟩
  exact (EvalRvalueFloatRel_binaryOp_float_iff .nondeterministic policy s.frame.locals s.frame.locals s.frame.locals bop _ _ lSc rSc lhsDecl.ty rhsDecl.ty f s.memory body.localDecls body.layouts _ hnot_off
    (evalOperand_copy_scalar_ok hslot_l) (evalOperand_copy_scalar_ok hslot_r) (operandTy_copy_local hdecl_lhs) (operandTy_copy_local hdecl_rhs) hf_lhs hf_rhs hlbw hrbw).mpr (Or.inl ⟨outSc, hrel_t, rfl⟩)
/-- **Index-exact nondeterministic real-step correspondence** (sharpens completeness): under the constant selector `fun _ _ => pure idx`, real `Step.step` stores EXACTLY the `idx`-th element of `Trusted`'s ordered `nanChoices f [(f, lhs), (f, rhs)]` (ORIGINAL un-negated rhs, also for `.sub`) when the base result is NaN, and `baseBits` for EVERY `idx` otherwise. -/
theorem step_float_arith_copy_copy_nondet_index_exact
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dstIdx lhsIdx rhsIdx : Local} {bop : MirAst.BinOp} {span : String} (hbop : isFloatArithBinOp bop = true) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩)
    {dstDecl lhsDecl rhsDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl)
    (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl) (hf_lhs : ieeeFormatOfTy? lhsDecl.ty = some f) (hf_rhs : ieeeFormatOfTy? rhsDecl.ty = some f)
    (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f) (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead) {lSc rSc : MirAst.ScalarInt} (idx : Nat) {baseBits outBits : Nat}
    (hslot_l : get? s.frame.locals lhsIdx = some (.init (.scalar lSc))) (hslot_r : get? s.frame.locals rhsIdx = some (.init (.scalar rSc)))
    (hbase : evalFloatArithBase bop f lSc.bits rSc.bits = .some baseBits)
    (hsel : (isNaNBits f baseBits = true ∧ (nanChoices f [(f, lSc.bits), (f, rSc.bits)] .nondeterministic)[idx]? = some outBits) ∨ (isNaNBits f baseBits = false ∧ outBits = baseBits))
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame lhsIdx ∧ IsImmediateFrameLocal topFrame rhsIdx) :
    StepRelLM3_1 body m allocMap (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar ⟨outBits, f.byteWidth⟩))) s.memory))
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts true (fun _ _ => pure idx)) () m) := by
  have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
  obtain ⟨tf, tfc, lMsc, rMsc, hframes, hbody, hloc, hstate_c, himm_dc, hlrel, hrrel, hlbw, hrbw, hm_eval⟩ :=
    binary_copy_copy_float_init_eval hstate (bop := bop) (span := span) hdecl_dst hdecl_lhs hdecl_rhs hf_lhs hf_rhs hslot_l hslot_r himm
  obtain ⟨msc', hrel', hfb⟩ :=
    floatOps_binary_arith_pure_index_exact body.layouts idx hbop hf_lhs hf_rhs hlrel hrrel hlbw hrbw hbase hsel
  have hdstT : translateTy lhsDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by
    rw [translateTy_of_ieeeFormatOfTy? hf_lhs, translateTy_of_ieeeFormatOfTy? hf_dst]
  have hbin : evalFloatBinOp bop f lSc.bits rSc.bits = .some ⟨baseBits, f.byteWidth⟩ := by
    unfold evalFloatBinOp; rw [evalFloatCmp_of_arith bop f _ _ hbop, hbase]
  have hrv_a : evalRvalue s.frame.locals (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)) s.memory
      body.localDecls body.layouts = .ok (.scalar ⟨baseBits, f.byteWidth⟩) s.frame.locals s.memory := by
    rw [evalRvalue_binaryOp_float _ _ _ bop _ _ lSc rSc _ _ _ hnot_off (evalOperand_copy_scalar_ok hslot_l) (evalOperand_copy_scalar_ok hslot_r)
      (by rw [operandTy_copy_local hdecl_lhs, isFloatOptTy_some_of_ieee hf_lhs]; rfl),
      operandTy_copy_local hdecl_lhs, operandTy_copy_local hdecl_rhs,
      evalFloatScalarBinOp_of_fmt bop lSc rSc lhsDecl.ty rhsDecl.ty f s.frame.locals s.memory hf_lhs hf_rhs hlbw hrbw, hbin]
  have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts true (fun _ _ => pure idx)) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m =
      Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc'))
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩) { m with stack := ⟨#[tfc]⟩ } := by
    rw [hm_eval true (fun _ _ => pure idx)]; unfold Miri.Interpreter.runRvalue
    rw [hfb, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
  have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes f.byteWidth := by
    rw [translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
  exact (finish_write_immediate_split_hooks _ hframes hbody hloc hstate_c rfl hbb hstmt
    hdecl_dst himm_dc hlive_dst hrv_a hm_write (floatCast_dst_localRel (Or.inl ⟨f, hf_dst⟩) hrel' hdst_sz)).2
/-- **Nondeterministic float arithmetic real-step COMPLETENESS (converse)**: for EVERY `outSc` admitted by `EvalRvalueFloatRel .nondeterministic policy`, there EXISTS a constant index `idx` realizing that exact `outSc` in `Miri.Interpreter.Step.step` (corollary of `step_float_arith_copy_copy_nondet_index_exact`). -/
theorem step_float_arith_copy_copy_nondet_completeness
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dstIdx lhsIdx rhsIdx : Local} {bop : MirAst.BinOp} {span : String} (hbop : isFloatArithBinOp bop = true) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩)
    {dstDecl lhsDecl rhsDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl)
    (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl) (hf_lhs : ieeeFormatOfTy? lhsDecl.ty = some f) (hf_rhs : ieeeFormatOfTy? rhsDecl.ty = some f)
    (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f) (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead) {lSc rSc outSc : MirAst.ScalarInt} (policy : Ptr2IntTransmutePolicy)
    (hslot_l : get? s.frame.locals lhsIdx = some (.init (.scalar lSc))) (hslot_r : get? s.frame.locals rhsIdx = some (.init (.scalar rSc)))
    (hrel_rv : EvalRvalueFloatRel .nondeterministic policy s.frame.locals (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)) s.memory body.localDecls body.layouts (.ok (.scalar outSc) s.frame.locals s.memory))
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame lhsIdx ∧ IsImmediateFrameLocal topFrame rhsIdx) :
    ∃ idx : Nat, StepRelLM3_1 body m allocMap (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar outSc))) s.memory))
        (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts true (fun _ _ => pure idx)) () m) := by
  have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlbw, hrbw, _⟩ := binary_copy_copy_float_init_eval hstate (bop := bop) (span := span) hdecl_dst hdecl_lhs hdecl_rhs hf_lhs hf_rhs hslot_l hslot_r himm
  have hrel_bin : EvalFloatBinOpRel .nondeterministic bop f lSc.bits rSc.bits outSc := by
    rcases (EvalRvalueFloatRel_binaryOp_float_iff .nondeterministic policy s.frame.locals s.frame.locals s.frame.locals bop _ _ lSc rSc lhsDecl.ty rhsDecl.ty f s.memory body.localDecls body.layouts _ hnot_off
      (evalOperand_copy_scalar_ok hslot_l) (evalOperand_copy_scalar_ok hslot_r) (operandTy_copy_local hdecl_lhs) (operandTy_copy_local hdecl_rhs) hf_lhs hf_rhs hlbw hrbw).mp hrel_rv with ⟨outSc', hrel', hok⟩ | ⟨_, huns⟩
    · injection hok with hv _ _; injection hv with hsc; rw [hsc]; exact hrel'
    · cases huns
  obtain ⟨baseBits, hbase, hcase⟩ :=
    (EvalFloatBinOpRel_arith_iff .nondeterministic bop f lSc.bits rSc.bits outSc hbop).mp hrel_bin
  rcases hcase with ⟨hnan, cand, hcand_mem, rfl⟩ | ⟨hnan, rfl⟩
  · obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hcand_mem
    exact ⟨idx, step_float_arith_copy_copy_nondet_index_exact hstate hbop hbb hstmt hdecl_dst hdecl_lhs hdecl_rhs
      hf_lhs hf_rhs hf_dst hlive_dst idx (outBits := cand) hslot_l hslot_r hbase
      (Or.inl ⟨hnan, by rw [List.getElem?_eq_getElem hidx_lt, hidx_eq]⟩) himm⟩
  · exact ⟨0, step_float_arith_copy_copy_nondet_index_exact hstate hbop hbb hstmt hdecl_dst hdecl_lhs hdecl_rhs
      hf_lhs hf_rhs hf_dst hlive_dst 0 (outBits := baseBits) hslot_l hslot_r hbase (Or.inr ⟨hnan, rfl⟩) himm⟩
/-- **Nondeterministic constant/constant float arithmetic real-step SOUNDNESS** (e.g. `const Inf - const Inf` or `const sNaN + const 1.0`): for ANY valid `chooseNaN`, `Step.step` stores an `outSc` admitted by `EvalRvalueFloatRel .nondeterministic policy` for every `policy`. -/
theorem step_float_arith_const_const_nondet_soundness
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) (hvalid : ValidBinaryChooseNaN chooseNaN)
    {bb : BasicBlockData} {dstIdx : Local} {bop : MirAst.BinOp} {c₁ c₂ : ConstOperand} {span : String} (hbop : isFloatArithBinOp bop = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c₁) (.constant c₂)), span⟩)
    {dstDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hf₁ : ieeeFormatOfTy? c₁.ty = some f) (hf₂ : ieeeFormatOfTy? c₂.ty = some f)
    (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f) (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead) {sc₁ sc₂ : MirAst.ScalarInt}
    (hv₁ : c₁.val = .scalar (.int sc₁)) (hv₂ : c₂.val = .scalar (.int sc₂)) (hsz₁ : sc₁.sizeBytes = f.byteWidth) (hsz₂ : sc₂.sizeBytes = f.byteWidth)
    (hcan₁ : sc₁.bits < scalarModulus sc₁.sizeBytes) (hcan₂ : sc₂.bits < scalarModulus sc₂.sizeBytes) (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    ∃ outSc,
      (∀ policy, EvalRvalueFloatRel .nondeterministic policy s.frame.locals (.binaryOp bop (.constant c₁) (.constant c₂)) s.memory body.localDecls body.layouts (.ok (.scalar outSc) s.frame.locals s.memory)) ∧
      StepRelLM3_1 body m allocMap (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar outSc))) s.memory))
        (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts true chooseNaN) () m) := by
  obtain ⟨tf, hlt_d, msc₁, msc₂, hframes, hbody, hloc, hstate_a, hrel₁, hrel₂, hm_eval⟩ :=
    binary_const_const_float_eval hstate true chooseNaN (bop := bop) (span := span) hdecl_dst hf₁ hf₂ hv₁ hv₂ hsz₁ hsz₂ hcan₁ hcan₂
  have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
  have hdstT : translateTy c₁.ty body.layouts = translateTy dstDecl.ty body.layouts := by rw [translateTy_of_ieeeFormatOfTy? hf₁, translateTy_of_ieeeFormatOfTy? hf_dst]
  obtain ⟨outSc, msc', hrel_t, hrel', hfb_st⟩ :=
    floatOps_binary_arith_any_chooseNaN_rel body.layouts chooseNaN hvalid hbop hf₁ hf₂ hrel₁ hrel₂ hsz₁ hsz₂ { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)]⟩ }
  obtain ⟨baseBits, hbase⟩ := (evalFloatArithBase_isSome_iff bop f sc₁.bits sc₂.bits).mpr hbop
  have hbin : evalFloatBinOp bop f sc₁.bits sc₂.bits = .some ⟨baseBits, f.byteWidth⟩ := by unfold evalFloatBinOp; rw [evalFloatCmp_of_arith bop f _ _ hbop, hbase]
  have hrv_a : evalRvalue s.frame.locals (.binaryOp bop (.constant c₁) (.constant c₂)) s.memory body.localDecls body.layouts = .ok (.scalar ⟨baseBits, f.byteWidth⟩) s.frame.locals s.memory := by
    rw [evalRvalue_binaryOp_float _ _ _ bop _ _ sc₁ sc₂ _ _ _ hnot_off (evalOperand_const_scalar_ok hv₁) (evalOperand_const_scalar_ok hv₂) (by simp [operandTy, isFloatOptTy_some_of_ieee hf₁])]
    dsimp only [operandTy]; rw [evalFloatScalarBinOp_of_fmt bop sc₁ sc₂ c₁.ty c₂.ty f s.frame.locals s.memory hf₁ hf₂ hsz₁ hsz₂, hbin]
  have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts true chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c₁) (.constant c₂)), span⟩) m =
      Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)]⟩ } := by
    rw [hm_eval]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_ok hfb_st, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
  have hout_sz : outSc.sizeBytes = f.byteWidth := by
    rcases (EvalFloatBinOpRel_arith_iff .nondeterministic bop f sc₁.bits sc₂.bits outSc hbop).mp hrel_t with ⟨_, _, ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩⟩ <;> rfl
  have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes outSc.sizeBytes := by
    rw [hout_sz, translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
  have hfin := finish_write_immediate_split_hooks _ hframes hbody hloc hstate_a rfl hbb hstmt hdecl_dst ((himm tf hframes).cache_layout hlt_d _) hlive_dst hrv_a hm_write
    (floatCast_dst_localRel (Or.inl ⟨f, hf_dst⟩) hrel' hdst_sz)
  refine ⟨outSc, fun policy => ?_, hfin.2⟩
  exact (EvalRvalueFloatRel_binaryOp_float_iff .nondeterministic policy s.frame.locals s.frame.locals s.frame.locals bop _ _ sc₁ sc₂ c₁.ty c₂.ty f s.memory body.localDecls body.layouts _
    hnot_off (evalOperand_const_scalar_ok hv₁) (evalOperand_const_scalar_ok hv₂) rfl rfl hf₁ hf₂ hsz₁ hsz₂).mpr (Or.inl ⟨outSc, hrel_t, rfl⟩)
/-- **Index-exact nondeterministic constant/constant float arithmetic real-step correspondence**: under `fun _ _ => pure idx`, real `Step.step` on `const c₁ <op> const c₂` stores EXACTLY the `idx`-th element of `Trusted`'s ordered `nanChoices f [(f, sc₁.bits), (f, sc₂.bits)]` on NaN, and `baseBits` otherwise. -/
theorem step_float_arith_const_const_nondet_index_exact
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dstIdx : Local} {bop : MirAst.BinOp} {c₁ c₂ : ConstOperand} {span : String} (hbop : isFloatArithBinOp bop = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c₁) (.constant c₂)), span⟩)
    {dstDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hf₁ : ieeeFormatOfTy? c₁.ty = some f) (hf₂ : ieeeFormatOfTy? c₂.ty = some f)
    (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f) (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead) {sc₁ sc₂ : MirAst.ScalarInt} (idx : Nat) {baseBits outBits : Nat}
    (hv₁ : c₁.val = .scalar (.int sc₁)) (hv₂ : c₂.val = .scalar (.int sc₂)) (hsz₁ : sc₁.sizeBytes = f.byteWidth) (hsz₂ : sc₂.sizeBytes = f.byteWidth)
    (hcan₁ : sc₁.bits < scalarModulus sc₁.sizeBytes) (hcan₂ : sc₂.bits < scalarModulus sc₂.sizeBytes) (hbase : evalFloatArithBase bop f sc₁.bits sc₂.bits = .some baseBits)
    (hsel : (isNaNBits f baseBits = true ∧ (nanChoices f [(f, sc₁.bits), (f, sc₂.bits)] .nondeterministic)[idx]? = some outBits) ∨ (isNaNBits f baseBits = false ∧ outBits = baseBits))
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    StepRelLM3_1 body m allocMap (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar ⟨outBits, f.byteWidth⟩))) s.memory))
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts true (fun _ _ => pure idx)) () m) := by
  have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
  obtain ⟨tf, hlt_d, msc₁, msc₂, hframes, hbody, hloc, hstate_a, hrel₁, hrel₂, hm_eval⟩ :=
    binary_const_const_float_eval hstate true (fun _ _ => pure idx) (bop := bop) (span := span) hdecl_dst hf₁ hf₂ hv₁ hv₂ hsz₁ hsz₂ hcan₁ hcan₂
  obtain ⟨msc', hrel', hfb⟩ := floatOps_binary_arith_pure_index_exact body.layouts idx hbop hf₁ hf₂ hrel₁ hrel₂ hsz₁ hsz₂ hbase hsel
  have hdstT : translateTy c₁.ty body.layouts = translateTy dstDecl.ty body.layouts := by rw [translateTy_of_ieeeFormatOfTy? hf₁, translateTy_of_ieeeFormatOfTy? hf_dst]
  have hbin : evalFloatBinOp bop f sc₁.bits sc₂.bits = .some ⟨baseBits, f.byteWidth⟩ := by unfold evalFloatBinOp; rw [evalFloatCmp_of_arith bop f _ _ hbop, hbase]
  have hrv_a : evalRvalue s.frame.locals (.binaryOp bop (.constant c₁) (.constant c₂)) s.memory body.localDecls body.layouts = .ok (.scalar ⟨baseBits, f.byteWidth⟩) s.frame.locals s.memory := by
    rw [evalRvalue_binaryOp_float _ _ _ bop _ _ sc₁ sc₂ _ _ _ hnot_off (evalOperand_const_scalar_ok hv₁) (evalOperand_const_scalar_ok hv₂) (by simp [operandTy, isFloatOptTy_some_of_ieee hf₁])]
    dsimp only [operandTy]; rw [evalFloatScalarBinOp_of_fmt bop sc₁ sc₂ c₁.ty c₂.ty f s.frame.locals s.memory hf₁ hf₂ hsz₁ hsz₂, hbin]
  have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts true (fun _ _ => pure idx)) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c₁) (.constant c₂)), span⟩) m =
      Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)]⟩ } := by
    rw [hm_eval]; unfold Miri.Interpreter.runRvalue; rw [hfb, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
  have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes f.byteWidth := by
    rw [translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
  exact (finish_write_immediate_split_hooks _ hframes hbody hloc hstate_a rfl hbb hstmt hdecl_dst ((himm tf hframes).cache_layout hlt_d _) hlive_dst hrv_a hm_write
    (floatCast_dst_localRel (Or.inl ⟨f, hf_dst⟩) hrel' hdst_sz)).2
/-- **Index-exact nondeterministic constant/copy float arithmetic real-step correspondence** (`_d = Op(const c, copy _r)`, Round-3 `B3`): under `fun _ _ => pure idx`, real `Step.step` stores EXACTLY the `idx`-th element of `Trusted`'s ordered `nanChoices f [(f, sc.bits), (f, rSc.bits)]` (the ORIGINAL un-negated COPIED rhs, also for `.sub`: `const 1.0 - copy qNaN`) on NaN, and `baseBits` otherwise. -/
theorem step_float_arith_const_copy_nondet_index_exact
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dstIdx rhsIdx : Local} {bop : MirAst.BinOp} {c : ConstOperand} {span : String} (hbop : isFloatArithBinOp bop = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c) (.copy ⟨rhsIdx, .nil⟩)), span⟩)
    {dstDecl rhsDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl)
    (hf_c : ieeeFormatOfTy? c.ty = some f) (hf_rhs : ieeeFormatOfTy? rhsDecl.ty = some f) (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f) (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    {sc rSc : MirAst.ScalarInt} (idx : Nat) {baseBits outBits : Nat} (hv_c : c.val = .scalar (.int sc)) (hsz_c : sc.sizeBytes = f.byteWidth) (hcan_c : sc.bits < scalarModulus sc.sizeBytes)
    (hslot_r : get? s.frame.locals rhsIdx = some (.init (.scalar rSc))) (hbase : evalFloatArithBase bop f sc.bits rSc.bits = .some baseBits)
    (hsel : (isNaNBits f baseBits = true ∧ (nanChoices f [(f, sc.bits), (f, rSc.bits)] .nondeterministic)[idx]? = some outBits) ∨ (isNaNBits f baseBits = false ∧ outBits = baseBits))
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame rhsIdx) :
    StepRelLM3_1 body m allocMap (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar ⟨outBits, f.byteWidth⟩))) s.memory))
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts true (fun _ _ => pure idx)) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate; obtain ⟨himm_d, himm_r⟩ := himm tf hframes
  have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
  have hm_stmt := evalStatement_assign_binaryOp_floatArith_eq body.localDecls body.layouts true (fun _ _ => pure idx) dstIdx bop (.constant c) (.copy ⟨rhsIdx, .nil⟩) span m
  rw [translateOperand_copy_unproj] at hm_stmt
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts); have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨lMsc, hlrel, hl_ok⟩ := annealEvalOperand_constant_float_ok (body := body) (m := { m with stack := ⟨#[tfa]⟩ }) rfl hf_c hv_c hsz_c hcan_c
    (if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none)
  obtain ⟨slot_r0, mls_r, _, hlt_ra, hslot_r0, hmls_r, hmls_r_eq, hloc_r⟩ := hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_rhs
  have hslot_r_eq : slot_r0 = .init (.scalar rSc) := Option.some.inj (hslot_r0.symm.trans hslot_r); subst hslot_r_eq
  let tfb := cacheFrameLocalLayout tfa rhsIdx hlt_ra (translateTy rhsDecl.ty body.layouts); have hstate_b := hstate_a.cache_layout rfl hdecl_rhs hlt_ra
  rcases hloc_r.floatCast_immediate_cases (Or.inl ⟨f, hf_rhs⟩) ((himm_r.cache_layout hlt_d _) mls_r hmls_r) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨rSc', rMsc, hr_eq, hrrel, hrsz, hmr⟩
  · cases h
  · cases h
  · injection hr_eq with hr_eq'; injection hr_eq' with hr_eq''; subst hr_eq''; rw [translateTy_of_ieeeFormatOfTy? hf_rhs body.layouts] at hrsz
    have hrbw := sizeBytes_of_float_layout hrrel.validBytes hrsz
    have hr_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).rightHomogeneous then some (translateTy c.ty body.layouts) else none)
      rfl hlt_ra hdecl_rhs (by rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr; subst hmr; rfl) hloc_r.cachedLayout_eq
    obtain ⟨msc', hrel', hfb⟩ := floatOps_binary_arith_pure_index_exact body.layouts idx hbop hf_c hf_rhs hlrel hrrel hsz_c hrbw hbase hsel
    have hdstT : translateTy c.ty body.layouts = translateTy dstDecl.ty body.layouts := by rw [translateTy_of_ieeeFormatOfTy? hf_c, translateTy_of_ieeeFormatOfTy? hf_dst]
    have hbin : evalFloatBinOp bop f sc.bits rSc.bits = .some ⟨baseBits, f.byteWidth⟩ := by unfold evalFloatBinOp; rw [evalFloatCmp_of_arith bop f _ _ hbop, hbase]
    have hrv_a : evalRvalue s.frame.locals (.binaryOp bop (.constant c) (.copy ⟨rhsIdx, .nil⟩)) s.memory body.localDecls body.layouts = .ok (.scalar ⟨baseBits, f.byteWidth⟩) s.frame.locals s.memory := by
      rw [evalRvalue_binaryOp_float _ _ _ bop _ _ sc rSc _ _ _ hnot_off (evalOperand_const_scalar_ok hv_c) (evalOperand_copy_scalar_ok hslot_r)
        (by rw [operandTy_const, isFloatOptTy_some_of_ieee hf_c]; rfl), operandTy_const, operandTy_copy_local hdecl_rhs,
        evalFloatScalarBinOp_of_fmt bop sc rSc c.ty rhsDecl.ty f s.frame.locals s.memory hf_c hf_rhs hsz_c hrbw, hbin]
    have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts true (fun _ _ => pure idx)) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m =
        Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩) { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_scalar, pure_bind, EStateM.bind_eq_ok hr_ok, annealReadImmediate_scalar, pure_bind,
        scalarOps_binary_float_eq _ _ _ _ hf_c hf_rhs, hfb, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
    have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes f.byteWidth := by rw [translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
    exact (finish_write_immediate_split_hooks _ hframes hfr.body_eq hfr.location_eq hstate_b rfl hbb hstmt hdecl_dst ((himm_d.cache_layout hlt_d _).cache_layout hlt_ra _) hlive_dst hrv_a hm_write
      (floatCast_dst_localRel (Or.inl ⟨f, hf_dst⟩) hrel' hdst_sz)).2
/-- **Index-exact nondeterministic copy/constant float arithmetic real-step correspondence** (`_d = Op(copy _l, const c)`, Round-3 `A3`): symmetric counterpart of `step_float_arith_const_copy_nondet_index_exact`; under `fun _ _ => pure idx`, real `Step.step` stores EXACTLY the `idx`-th element of `Trusted`'s ordered `nanChoices f [(f, lSc.bits), (f, sc.bits)]` (preserving operand order and un-negated rhs, also for `.sub`) on NaN, and `baseBits` otherwise. -/
theorem step_float_arith_copy_const_nondet_index_exact
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dstIdx lhsIdx : Local} {bop : MirAst.BinOp} {c : ConstOperand} {span : String} (hbop : isFloatArithBinOp bop = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.constant c)), span⟩)
    {dstDecl lhsDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl)
    (hf_lhs : ieeeFormatOfTy? lhsDecl.ty = some f) (hf_c : ieeeFormatOfTy? c.ty = some f) (hf_dst : ieeeFormatOfTy? dstDecl.ty = some f) (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    {lSc sc : MirAst.ScalarInt} (idx : Nat) {baseBits outBits : Nat} (hslot_l : get? s.frame.locals lhsIdx = some (.init (.scalar lSc)))
    (hv_c : c.val = .scalar (.int sc)) (hsz_c : sc.sizeBytes = f.byteWidth) (hcan_c : sc.bits < scalarModulus sc.sizeBytes)
    (hbase : evalFloatArithBase bop f lSc.bits sc.bits = .some baseBits)
    (hsel : (isNaNBits f baseBits = true ∧ (nanChoices f [(f, lSc.bits), (f, sc.bits)] .nondeterministic)[idx]? = some outBits) ∨ (isNaNBits f baseBits = false ∧ outBits = baseBits))
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame lhsIdx) :
    StepRelLM3_1 body m allocMap (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar ⟨outBits, f.byteWidth⟩))) s.memory))
      (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts true (fun _ _ => pure idx)) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate; obtain ⟨himm_d, himm_l⟩ := himm tf hframes
  have hnot_off : bop ≠ .offset := by intro h; subst h; cases hbop
  have hm_stmt := evalStatement_assign_binaryOp_floatArith_eq body.localDecls body.layouts true (fun _ _ => pure idx) dstIdx bop (.copy ⟨lhsIdx, .nil⟩) (.constant c) span m
  rw [translateOperand_copy_unproj] at hm_stmt
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts); have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_l0, mls_l, _, hlt_la, hslot_l0, hmls_l, hmls_l_eq, hloc_l⟩ := hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_lhs
  have hslot_l_eq : slot_l0 = .init (.scalar lSc) := Option.some.inj (hslot_l0.symm.trans hslot_l); subst hslot_l_eq
  let tfb := cacheFrameLocalLayout tfa lhsIdx hlt_la (translateTy lhsDecl.ty body.layouts); have hstate_b := hstate_a.cache_layout rfl hdecl_lhs hlt_la
  rcases hloc_l.floatCast_immediate_cases (Or.inl ⟨f, hf_lhs⟩) ((himm_l.cache_layout hlt_d _) mls_l hmls_l) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨lSc', lMsc, hl_eq, hlrel, hlsz, hml⟩
  · cases h
  · cases h
  · injection hl_eq with hl_eq'; injection hl_eq' with hl_eq''; subst hl_eq''; rw [translateTy_of_ieeeFormatOfTy? hf_lhs body.layouts] at hlsz
    have hlbw := sizeBytes_of_float_layout hlrel.validBytes hlsz
    have hl_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none)
      rfl hlt_la hdecl_lhs (by rw [hmls_l_eq]; rcases mls_l with ⟨v0, l0⟩; dsimp only at hml; subst hml; rfl) hloc_l.cachedLayout_eq
    obtain ⟨rMsc, hrrel, hr_ok⟩ := annealEvalOperand_constant_float_ok (body := body) (m := { m with stack := ⟨#[tfb]⟩ }) rfl hf_c hv_c hsz_c hcan_c
      (if (translateBinOp bop).rightHomogeneous then some (translateTy lhsDecl.ty body.layouts) else none)
    obtain ⟨msc', hrel', hfb⟩ := floatOps_binary_arith_pure_index_exact body.layouts idx hbop hf_lhs hf_c hlrel hrrel hlbw hsz_c hbase hsel
    have hdstT : translateTy lhsDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by rw [translateTy_of_ieeeFormatOfTy? hf_lhs, translateTy_of_ieeeFormatOfTy? hf_dst]
    have hbin : evalFloatBinOp bop f lSc.bits sc.bits = .some ⟨baseBits, f.byteWidth⟩ := by unfold evalFloatBinOp; rw [evalFloatCmp_of_arith bop f _ _ hbop, hbase]
    have hrv_a : evalRvalue s.frame.locals (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.constant c)) s.memory body.localDecls body.layouts = .ok (.scalar ⟨baseBits, f.byteWidth⟩) s.frame.locals s.memory := by
      rw [evalRvalue_binaryOp_float _ _ _ bop _ _ lSc sc _ _ _ hnot_off (evalOperand_copy_scalar_ok hslot_l) (evalOperand_const_scalar_ok hv_c)
        (by rw [operandTy_copy_local hdecl_lhs, isFloatOptTy_some_of_ieee hf_lhs]; rfl), operandTy_copy_local hdecl_lhs, operandTy_const,
        evalFloatScalarBinOp_of_fmt bop lSc sc lhsDecl.ty c.ty f s.frame.locals s.memory hf_lhs hf_c hlbw hsz_c, hbin]
    have hm_write : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts true (fun _ _ => pure idx)) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.constant c)), span⟩) m =
        Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩) { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_scalar, pure_bind, EStateM.bind_eq_ok hr_ok, annealReadImmediate_scalar, pure_bind,
        scalarOps_binary_float_eq _ _ _ _ hf_lhs hf_c, hfb, pure_bind, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ hdstT _)]
    have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes f.byteWidth := by rw [translateTy_of_ieeeFormatOfTy? hf_dst, translateSizeBytes_byteWidth, floatLayoutData_size]
    exact (finish_write_immediate_split_hooks _ hframes hfr.body_eq hfr.location_eq hstate_b rfl hbb hstmt hdecl_dst ((himm_d.cache_layout hlt_d _).cache_layout hlt_la _) hlive_dst hrv_a hm_write
      (floatCast_dst_localRel (Or.inl ⟨f, hf_dst⟩) hrel' hdst_sz)).2
/-! ### 3.5 Fail-closed and UB boundaries (`uninit`, `f16`/`f128`, invalid float `BinOp`) -/
/-- **Uninitialized float local unary-negation UB lockstep** (exact `"read of uninitialized local"` error). -/
theorem step_float_uninit_unaryNeg_ub_lockstep
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {bb : BasicBlockData} {dstIdx srcIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)), span⟩)
    {dstDecl srcDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hf_src : ieeeFormatOfTy? srcDecl.ty = some f) (_hf_dst : ieeeFormatOfTy? dstDecl.ty = some f) (huninit : get? s.frame.locals srcIdx = some .uninit)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    stepMirFn body s = .fail .ub ∧
      ∃ m', Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () m =
        (m', .error (.undefinedBehavior "read of uninitialized local")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, himm_s⟩ := himm tf hframes
  have ha : stepMirFn body s = .fail .ub := by rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [huninit]
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ := hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hslot_eq : slot_s = .uninit := Option.some.inj (hslot_s.symm.trans huninit); subst hslot_eq
  rcases hloc_s.floatCast_immediate_cases (Or.inl ⟨f, hf_src⟩) ((himm_s.cache_layout hlt_d _) mls_s hmls_s) with ⟨h, _⟩ | ⟨_, hms⟩ | ⟨_, _, h, _, _, _⟩
  · cases h
  · have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ }) (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src
      (by rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl) hloc_s.cachedLayout_eq
    have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
        ({ m with stack := ⟨#[cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)]⟩ }, .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [evalStatement_assign_unaryNeg_floatArith_eq, translateOperand_copy_unproj]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, annealReadImmediate_uninit_eq]; rfl
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact ⟨ha, _, rfl⟩
  · cases h
/-- **Uninitialized binary float operand UB lockstep** (left-uninit OR init-left / right-uninit, exact `"read of uninitialized local"` error for both arithmetic and comparison binary ops). -/
theorem step_float_uninit_binaryOp_ub_lockstep
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx lhsIdx rhsIdx : Local} {bop : MirAst.BinOp} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩)
    {dstDecl lhsDecl rhsDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl) (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl)
    (hf_lhs : ieeeFormatOfTy? lhsDecl.ty = some f) (hf_rhs : ieeeFormatOfTy? rhsDecl.ty = some f)
    (huninit : get? s.frame.locals lhsIdx = some .uninit ∨ (∃ lSc, get? s.frame.locals lhsIdx = some (.init (.scalar lSc)) ∧ get? s.frame.locals rhsIdx = some .uninit))
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame lhsIdx ∧ IsImmediateFrameLocal topFrame rhsIdx) :
    stepMirFn body s = .fail .ub ∧
      ∃ m', Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () m =
        (m', .error (.undefinedBehavior "read of uninitialized local")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, himm_l, himm_r⟩ := himm tf hframes
  have hm_stmt := evalStatement_assign_binaryOp_floatArith_eq body.localDecls body.layouts nondet chooseNaN dstIdx bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩) span m
  rw [translateOperand_copy_unproj, translateOperand_copy_unproj] at hm_stmt
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_l, mls_l, _, hlt_la, hslot_l, hmls_l, hmls_l_eq, hloc_l⟩ := hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_lhs
  let tfb := cacheFrameLocalLayout tfa lhsIdx hlt_la (translateTy lhsDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_lhs hlt_la
  rcases huninit with hl_un | ⟨lSc, hl_init, hr_un⟩
  · have hslot_eq : slot_l = .uninit := Option.some.inj (hslot_l.symm.trans hl_un); subst hslot_eq
    have ha : stepMirFn body s = .fail .ub := by rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hl_un]
    rcases hloc_l.floatCast_immediate_cases (Or.inl ⟨f, hf_lhs⟩) ((himm_l.cache_layout hlt_d _) mls_l hmls_l) with ⟨h, _⟩ | ⟨_, hml⟩ | ⟨_, _, h, _, _, _⟩
    · cases h
    · have hl_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none)
        rfl hlt_la hdecl_lhs (by rw [hmls_l_eq]; rcases mls_l with ⟨v0, l0⟩; dsimp only at hml; subst hml; rfl) hloc_l.cachedLayout_eq
      have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_uninit_eq]; rfl
      rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact ⟨ha, _, rfl⟩
    · cases h
  · have hslot_eq : slot_l = .init (.scalar lSc) := Option.some.inj (hslot_l.symm.trans hl_init); subst hslot_eq
    have ha : stepMirFn body s = .fail .ub := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; unfold evalStmt evalRvalue; dsimp only []
      rw [evalOperand_copy_scalar_ok hl_init]; dsimp only []; unfold evalOperand; dsimp only []; rw [hr_un]
    rcases hloc_l.floatCast_immediate_cases (Or.inl ⟨f, hf_lhs⟩) ((himm_l.cache_layout hlt_d _) mls_l hmls_l) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, lMsc, _, _, _, hml⟩
    · cases h
    · cases h
    · have hl_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ }) (known := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none)
        rfl hlt_la hdecl_lhs (by rw [hmls_l_eq]; rcases mls_l with ⟨v0, l0⟩; dsimp only at hml; subst hml; rfl) hloc_l.cachedLayout_eq
      obtain ⟨slot_r, mls_r, _, hlt_rb, hslot_r, hmls_r, hmls_r_eq, hloc_r⟩ := hstate_b.frame_rel_singleton rfl |>.lookup_local hdecl_rhs
      have hr_eq : slot_r = .uninit := Option.some.inj (hslot_r.symm.trans hr_un); subst hr_eq
      rcases hloc_r.floatCast_immediate_cases (Or.inl ⟨f, hf_rhs⟩) (((himm_r.cache_layout hlt_d _).cache_layout hlt_la _) mls_r hmls_r) with ⟨h, _⟩ | ⟨_, hmr⟩ | ⟨_, _, h, _, _, _⟩
      · cases h
      · have hr_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfb]⟩ }) (known := if (translateBinOp bop).rightHomogeneous then some (translateTy lhsDecl.ty body.layouts) else none)
          rfl hlt_rb hdecl_rhs (by rw [hmls_r_eq]; rcases mls_r with ⟨v0, l0⟩; dsimp only at hmr; subst hmr; rfl) hloc_r.cachedLayout_eq
        have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)), span⟩) m =
            ({ m with stack := ⟨#[cacheFrameLocalLayout tfb rhsIdx hlt_rb (translateTy rhsDecl.ty body.layouts)]⟩ }, .error (.undefinedBehavior "read of uninitialized local")) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hl_ok, annealReadImmediate_scalar, pure_bind, EStateM.bind_eq_ok hr_ok, annealReadImmediate_uninit_eq]; rfl
        rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact ⟨ha, _, rfl⟩
      · cases h
/-- **`f16`/`f128` fail-closed boundary** at real `Step.step` / `stepMirFn` (exact error message). -/
theorem step_float_f16_f128_fail_closed
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) {bb : BasicBlockData} {dstIdx srcIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)), span⟩)
    {dstDecl srcDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (h16 : srcDecl.ty.kind = .float .f16 ∨ srcDecl.ty.kind = .float .f128) {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hslot_s : get? s.frame.locals srcIdx = some (.init (.scalar sc))) (himm_s : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[srcIdx]? = some ⟨.live (.immediate (.scalar (.fromScalarInt msc))), lay⟩) :
    stepMirFn body s = .fail .unsupported ∧
      ∃ m', Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () m =
        (m', .error (.unsupported s!"floatOps.formatOf: TyId {encodeTyId srcDecl.ty} is not f32/f64")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨lay_s0, hlay_s0⟩ := himm_s tf hframes
  have hfmt_none : ieeeFormatOfTy? srcDecl.ty = none := by rcases h16 with hk | hk <;> simp [ieeeFormatOfTy?, hk]
  have hfloat_opt : isFloatOptTy (some srcDecl.ty) = true := by rcases h16 with hk | hk <;> simp [isFloatOptTy, isFloatTy, hk]
  have ha : stepMirFn body s = .fail .unsupported := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; unfold evalStmt; dsimp only []
    rw [evalRvalue_unaryOp_neg_float _ _ _ sc _ _ _ (evalOperand_copy_scalar_ok hslot_s) (by rw [operandTy_copy_local hdecl_src]; exact hfloat_opt)]
    unfold evalFloatUnaryNeg; rw [operandTy_copy_local hdecl_src]; dsimp only; rw [hfmt_none]; rfl
  refine ⟨ha, ?_⟩
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst (by rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq)
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨_, mls_s, _, hlt_sa, _, hmls_s, hmls_s_eq, hloc_s⟩ := hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlay_tfa : ∃ lay_s, tfa.locals[srcIdx]? = some ⟨.live (.immediate (.scalar (.fromScalarInt msc))), lay_s⟩ := by
    dsimp [tfa, cacheFrameLocalLayout]; rw [Array.getElem?_set]
    by_cases hds : dstIdx = srcIdx
    · subst hds; simp only [↓reduceIte, Array.getElem?_eq_getElem hlt_d] at hlay_s0 ⊢; injection hlay_s0 with hm0; rw [hm0]; exact ⟨_, rfl⟩
    · simp only [hds, ↓reduceIte]; exact ⟨lay_s0, hlay_s0⟩
  obtain ⟨lay_s, hlay_s⟩ := hlay_tfa
  have hmls_s_eq_val : mls_s = ⟨.live (.immediate (.scalar (.fromScalarInt msc))), lay_s⟩ := by rw [hmls_s] at hlay_s; exact Option.some.inj hlay_s
  have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ }) (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src
    (by rw [hmls_s_eq]; exact hmls_s_eq_val) (by have hc := hloc_s.cachedLayout_eq; rw [hmls_s_eq_val] at hc; exact hc)
  have hfu_err := (floatOps_f16_f128_unsupported body.layouts nondet chooseNaN h16 msc msc .Add { m with stack := ⟨#[tfb]⟩ }).1
  have hcls : (annealScalarOpsHooksFloatArith body.localDecls body.layouts nondet chooseNaN).classify () (translateTy srcDecl.ty body.layouts).ty = pure .floating := by
    have hc : classifyEncodedTyId (translateTy srcDecl.ty body.layouts).ty = .ok .floating := by rcases h16 with hk | hk <;> simp [translateTy, encodeTyId, hk, classifyEncodedTyId]
    simp only [annealScalarOpsHooksFloatArith, annealScalarOpsHooks, hc]
  have hsu_err : Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () .Neg
      ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩ { m with stack := ⟨#[tfb]⟩ } =
      .error (.unsupported s!"floatOps.formatOf: TyId {encodeTyId srcDecl.ty} is not f32/f64") { m with stack := ⟨#[tfb]⟩ } := by
    have hsu_fn : Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () .Neg
        ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩ =
        Miri.Interpreter.FloatOps.unary (annealFloatOpsHooks nondet chooseNaN) () .Neg ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩ := by
      unfold Miri.Interpreter.ScalarOps.unary; rw [hcls, pure_bind]; dsimp only
      have hto : (miriScalarOpsToScalar (⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩ : Miri.Interpreter.RvalueImmTy AnnealProv) : Miri.Interpreter.RvalueM AnnealStepState (Miri.Memory.Scalar AnnealProv)) = pure (.fromScalarInt msc) := rfl
      rw [hto, pure_bind]; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]; rfl
    rw [congrFun hsu_fn _, hfu_err]
  have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .neg (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
      ({ m with stack := ⟨#[tfb]⟩ }, .error (.unsupported s!"floatOps.formatOf: TyId {encodeTyId srcDecl.ty} is not f32/f64")) := by
    rw [evalStatement_assign_unaryNeg_floatArith_eq, translateOperand_copy_unproj]; unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, annealReadImmediate_scalar, pure_bind, EStateM.bind_eq_error hsu_err]
  rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]; exact ⟨_, rfl⟩
/-- **Invalid float `BinOp` fail-closed boundary** (`bitXor`, `shl`, `cmp`, etc.). -/
theorem step_float_invalid_binOp_fail_closed
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap) (hphase : ∀ p, body.phase ≠ .other p) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx : Local} {bop : MirAst.BinOp} {c₁ c₂ : ConstOperand} {span : String} (hnot : isFloatBinOp bop = false) (hnot_off : bop ≠ .offset)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c₁) (.constant c₂)), span⟩)
    {dstDecl : LocalDecl} {f : IeeeFormat} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl) (hf₁ : ieeeFormatOfTy? c₁.ty = some f) (hf₂ : ieeeFormatOfTy? c₂.ty = some f)
    {sc₁ sc₂ : MirAst.ScalarInt} (hv₁ : c₁.val = .scalar (.int sc₁)) (hv₂ : c₂.val = .scalar (.int sc₂)) (hsz₁ : sc₁.sizeBytes = f.byteWidth) (hsz₂ : sc₂.sizeBytes = f.byteWidth)
    (hcan₁ : sc₁.bits < scalarModulus sc₁.sizeBytes) (hcan₂ : sc₂.bits < scalarModulus sc₂.sizeBytes) :
    stepMirFn body s = .fail .unsupported ∧
      ∃ m', Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) () m =
        (m', .error (.invalidProgram "invalid floating binary operation")) := by
  obtain ⟨_, _, _, _, _, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨tf, hlt_d, msc₁, msc₂, hframes, hbody, hloc, _, hrel₁, hrel₂, hm_eval⟩ :=
    binary_const_const_float_eval hstate nondet chooseNaN hdecl_dst hf₁ hf₂ hv₁ hv₂ hsz₁ hsz₂ hcan₁ hcan₂
  have ha : stepMirFn body s = .fail .unsupported := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; unfold evalStmt; dsimp only []
    rw [evalRvalue_binaryOp_float _ _ _ bop _ _ sc₁ sc₂ _ _ _ hnot_off (evalOperand_const_scalar_ok hv₁) (evalOperand_const_scalar_ok hv₂)
      (by simp [operandTy, isFloatOptTy_some_of_ieee hf₁])]
    dsimp only [operandTy]
    rw [evalFloatScalarBinOp_of_fmt bop sc₁ sc₂ c₁.ty c₂.ty f s.frame.locals s.memory hf₁ hf₂ hsz₁ hsz₂, (evalFloatBinOp_eq_none_iff bop f sc₁.bits sc₂.bits).mpr hnot]; rfl
  have hfb_err := floatOps_binary_unsupported_err body.layouts nondet chooseNaN hnot hf₁ hf₂ hrel₁ hrel₂ hsz₁ hsz₂
    { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)]⟩ }
  have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksFloatArith body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.constant c₁) (.constant c₂)), span⟩) m =
      ({ m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)]⟩ },
        .error (.invalidProgram "invalid floating binary operation")) := by
    rw [hm_eval]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hfb_err]
  rw [miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]; exact ⟨ha, _, rfl⟩
/-! ## Part 4. `Ptr2IntTransmutePolicy` (`ucg#630` vs. `reference#1752`) & Shared Witnesses `W1–W12` -/
/-! ### 4.1 Vendored `Miri.Memory.Allocation.readScalar` provenance-stripping vs. CTFE rejection -/
/-- **Runtime Miri provenance stripping (`offsetIsAddr = true`)**: under `Miri.Memory.Provenance`, `Allocation.readScalar ... false` unconditionally strips provenance (`Ptr2IntTransmutePolicy.stripProvenance`). -/
theorem alloc_readScalar_strip_runtime {Extra : Type}
    (alloc : Miri.Memory.Allocation Miri.Memory.Provenance Extra) (layout : Miri.ABI.TargetDataLayout) (range : Miri.Memory.AllocRange)
    {bytes : Array UInt8} {bits : Miri.ABI.U128} {sc : Miri.Memory.Scalar Miri.Memory.Provenance} (hinit : alloc.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (hbytes : alloc.getBytesUnchecked range = .ok bytes) (hread : miriReadTargetUInt layout bytes = .ok bits) (hfrom : Miri.Memory.Scalar.fromUInt bits range.size = .ok sc) :
    alloc.readScalar layout range false = .ok sc := by
  unfold Miri.Memory.Allocation.readScalar
  have hi : (alloc.initializationMask.isRangeInitialized range).mapError Miri.Memory.AllocError.memory = .ok (.ok ()) := by rw [hinit]; rfl
  change (do
    match ← (alloc.initializationMask.isRangeInitialized range).mapError Miri.Memory.AllocError.memory with
    | .error bad => throw (Miri.Memory.AllocError.invalidUninitBytes (some ⟨range, bad⟩))
    | .ok () => pure ()
    let bytes ← alloc.getBytesUnchecked range; let bits ← miriReadTargetUInt layout bytes
    (Miri.Memory.Scalar.fromUInt bits range.size).mapError Miri.Memory.AllocError.scalar) = .ok sc
  rw [hi]; simp only [hbytes, hread, hfrom, Except.mapError, bind, Except.bind]
/-- **CTFE Miri strict pointer-as-int rejection (`offsetIsAddr = false`)**: under `Miri.Memory.CtfeProvenance`, `Allocation.readScalar ... false` rejects provenance-carrying ranges with `.error (.readPointerAsInt none)` (`Ptr2IntTransmutePolicy.strictUcg630Ub`). -/
theorem alloc_readScalar_ctfe_rejects_prov {Extra : Type}
    (alloc : Miri.Memory.Allocation Miri.Memory.CtfeProvenance Extra) (layout : Miri.ABI.TargetDataLayout) (range : Miri.Memory.AllocRange) {bytes : Array UInt8} {bits : Miri.ABI.U128}
    (hinit : alloc.initializationMask.isRangeInitialized range = .ok (.ok ())) (hbytes : alloc.getBytesUnchecked range = .ok bytes) (hread : miriReadTargetUInt layout bytes = .ok bits)
    (hnonempty : alloc.provenanceMap.rangeEmpty range (Miri.ABI.Size.fromBits layout.pointerWidth.bits) = .ok false) :
    alloc.readScalar layout range false = .error (Miri.Memory.AllocError.readPointerAsInt none) := by
  unfold Miri.Memory.Allocation.readScalar
  have hi : (alloc.initializationMask.isRangeInitialized range).mapError Miri.Memory.AllocError.memory = .ok (.ok ()) := by rw [hinit]; rfl
  have hp : (alloc.provenanceMap.rangeEmpty range (Miri.ABI.Size.fromBits layout.pointerWidth.bits)).mapError
      Miri.Memory.AllocError.provenance = .ok false := by rw [hnonempty]; rfl
  change (do
    match ← (alloc.initializationMask.isRangeInitialized range).mapError Miri.Memory.AllocError.memory with
    | .error bad => throw (Miri.Memory.AllocError.invalidUninitBytes (some ⟨range, bad⟩))
    | .ok () => pure ()
    let bytes ← alloc.getBytesUnchecked range; let bits ← miriReadTargetUInt layout bytes
    let isEmpty ← (alloc.provenanceMap.rangeEmpty range (Miri.ABI.Size.fromBits layout.pointerWidth.bits)).mapError Miri.Memory.AllocError.provenance
    if isEmpty then (Miri.Memory.Scalar.fromUInt bits range.size).mapError Miri.Memory.AllocError.scalar
    else throw (Miri.Memory.AllocError.readPointerAsInt none)) = .error (Miri.Memory.AllocError.readPointerAsInt none)
  rw [hi]; simp only [hbytes, hread, bind, Except.bind]; rw [hp]; rfl
/-- **Provenance-free agreement (`f32 <-> u32`, `f64 <-> u64` `{to,from}_bits`)**: whenever `provenanceMap.rangeEmpty = .ok true`, CTFE `readScalar` agrees with runtime `Provenance`. -/
theorem alloc_readScalar_ctfe_provFree_ok {Extra : Type}
    (alloc : Miri.Memory.Allocation Miri.Memory.CtfeProvenance Extra) (layout : Miri.ABI.TargetDataLayout) (range : Miri.Memory.AllocRange)
    {bytes : Array UInt8} {bits : Miri.ABI.U128} {sc : Miri.Memory.Scalar Miri.Memory.CtfeProvenance} (hinit : alloc.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (hbytes : alloc.getBytesUnchecked range = .ok bytes) (hread : miriReadTargetUInt layout bytes = .ok bits)
    (hempty : alloc.provenanceMap.rangeEmpty range (Miri.ABI.Size.fromBits layout.pointerWidth.bits) = .ok true) (hfrom : Miri.Memory.Scalar.fromUInt bits range.size = .ok sc) :
    alloc.readScalar layout range false = .ok sc := by
  unfold Miri.Memory.Allocation.readScalar
  have hi : (alloc.initializationMask.isRangeInitialized range).mapError Miri.Memory.AllocError.memory = .ok (.ok ()) := by rw [hinit]; rfl
  have hp : (alloc.provenanceMap.rangeEmpty range (Miri.ABI.Size.fromBits layout.pointerWidth.bits)).mapError
      Miri.Memory.AllocError.provenance = .ok true := by rw [hempty]; rfl
  change (do
    match ← (alloc.initializationMask.isRangeInitialized range).mapError Miri.Memory.AllocError.memory with
    | .error bad => throw (Miri.Memory.AllocError.invalidUninitBytes (some ⟨range, bad⟩))
    | .ok () => pure ()
    let bytes ← alloc.getBytesUnchecked range; let bits ← miriReadTargetUInt layout bytes
    let isEmpty ← (alloc.provenanceMap.rangeEmpty range (Miri.ABI.Size.fromBits layout.pointerWidth.bits)).mapError Miri.Memory.AllocError.provenance
    if isEmpty then (Miri.Memory.Scalar.fromUInt bits range.size).mapError Miri.Memory.AllocError.scalar
    else throw (Miri.Memory.AllocError.readPointerAsInt none)) = .ok sc
  rw [hi]; simp only [hbytes, hread, bind, Except.bind]; rw [hp]; simp only [↓reduceIte, hfrom, Except.mapError]
/-- **Shared uninitialized-bytes UB under EVERY `PointerProvenance`**. -/
theorem alloc_readScalar_uninit_both
    {Prov Extra : Type} [DecidableEq Prov] [Miri.Memory.PointerProvenance Prov]
    (alloc : Miri.Memory.Allocation Prov Extra) (layout : Miri.ABI.TargetDataLayout) (range bad : Miri.Memory.AllocRange) (readProv : Bool)
    (huninit : alloc.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    alloc.readScalar layout range readProv =
      .error (Miri.Memory.AllocError.invalidUninitBytes (some ⟨range, bad⟩)) := by
  unfold Miri.Memory.Allocation.readScalar
  have hi : (alloc.initializationMask.isRangeInitialized range).mapError Miri.Memory.AllocError.memory = .ok (.error bad) := by rw [huninit]; rfl
  change (do
    match ← (alloc.initializationMask.isRangeInitialized range).mapError Miri.Memory.AllocError.memory with
    | .error bad => throw (Miri.Memory.AllocError.invalidUninitBytes (some ⟨range, bad⟩))
    | .ok () => pure ()
    let bytes ← alloc.getBytesUnchecked range; let bits ← miriReadTargetUInt layout bytes
    if readProv then
      let targetSize := Miri.ABI.Size.fromBits layout.pointerWidth.bits
      if range.size != targetSize then throw (Miri.Memory.AllocError.scalarPointerNotTargetSized range.size targetSize)
      let provenance ← match alloc.provenanceMap.readPtr range.start targetSize with
        | .ok provenance => pure provenance
        | .error (.readPartialPointer offset) => throw (Miri.Memory.AllocError.readPartialPointer offset)
        | .error reason => throw (Miri.Memory.AllocError.provenance reason)
      match provenance with
      | some provenance =>
        if bits.toNat > 18446744073709551615 then throw (Miri.Memory.AllocError.pointerBitsDoNotFitOffset bits)
        return Miri.Memory.Scalar.fromPointer layout (Miri.Memory.Pointer.new provenance (Miri.ABI.Size.ofBytes (UInt64.ofNat bits.toNat)))
      | none => (Miri.Memory.Scalar.fromUInt bits range.size).mapError Miri.Memory.AllocError.scalar
    else
      if Miri.Memory.PointerProvenance.offsetIsAddr (Prov := Prov) then
        (Miri.Memory.Scalar.fromUInt bits range.size).mapError Miri.Memory.AllocError.scalar
      else
        let isEmpty ← (alloc.provenanceMap.rangeEmpty range (Miri.ABI.Size.fromBits layout.pointerWidth.bits)).mapError Miri.Memory.AllocError.provenance
        if isEmpty then (Miri.Memory.Scalar.fromUInt bits range.size).mapError Miri.Memory.AllocError.scalar
        else throw (Miri.Memory.AllocError.readPointerAsInt none)) =
    .error (Miri.Memory.AllocError.invalidUninitBytes (some ⟨range, bad⟩))
  rw [hi]; rfl
/-! ### 4.2 `Cast.cast .Transmute` under an Anneal-authored `copyAllowTransmute` (NOT step-wired): no-forgery (`usize -> &u8`) & uninit UB -/
/-- Policy-aware scalar transmute validator for `CastHooks.copyAllowTransmute` (an Anneal-authored model, NOT vendored Miri validity): - `&T`/`&mut T` (`41`) and `fn()` (`42`) require non-null pointer provenance & matching size under BOTH policies, and ONLY that: no alignment / dereferenceability / is-a-function check (as permissive as `Trusted`'s `decodePtrBytesNoForge true`); - raw pointers (`encodeRawPtrTyId` in `{40, 60..82}`) accept provenance-carrying pointers AND provenance-free integers under BOTH policies; - primitive non-pointer scalars (`usize`, `f64`, ...) enforce `Ptr2IntTransmutePolicy` on pointer provenance. Non-primitive `TyId`s (ADT `100 + i`, arrays, `()`) fail closed (`.unsupported`). -/
def miriTransmuteScalarCheck (policy : Ptr2IntTransmutePolicy)
    (destLay : Miri.Interpreter.LocalLayout) (sc : Miri.Memory.Scalar AnnealProv) :
    Except Miri.Interpreter.StepError (Miri.Memory.Scalar AnnealProv) :=
  match destLay.ty with
  | 41 | 42 =>
    match sc.toPointer annealTargetDataLayout with
    | .ok p =>
      if p.provenance.isNone || p.offset == Miri.ABI.Size.ZERO then
        .error (.undefinedBehavior "transmute forged reference/fn-pointer without provenance")
      else if sc.size == destLay.layout.size then .ok sc
      else .error (.undefinedBehavior "transmute scalar size mismatch")
    | .error _ => .error (.undefinedBehavior "transmute produced invalid reference")
  | _ =>
    if !annealValidateScalarForTyId destLay.ty sc then
      .error (.undefinedBehavior "transmute produced invalid scalar value")
    else if (match classifyEncodedTyId destLay.ty with | .ok _ => false | .error _ => true) then
      .error (.unsupported "transmute into non-primitive TyId (ADT/array/ZST)")
    else if sc.isPointer && (match classifyEncodedTyId destLay.ty with | .ok .pointer => true | _ => false) then
      if sc.size == destLay.layout.size then .ok sc
      else .error (.undefinedBehavior "transmute scalar size mismatch")
    else
      match sc.isPointer, policy with
      | true, .strictUcg630Ub =>
        .error (.undefinedBehavior "transmute of pointer provenance into non-pointer scalar (ucg#630)")
      | true, .stripProvenance =>
        if sc.size != destLay.layout.size then .error (.undefinedBehavior "transmute scalar size mismatch") else
        match sc.toPointer annealTargetDataLayout with
        | .ok p =>
          match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 p.offset.bytes.toNat) destLay.layout.size with
          | .ok stripped => .ok stripped
          | .error _ => .error (.undefinedBehavior "transmute stripped scalar width mismatch")
        | .error _ => .error (.undefinedBehavior "malformed pointer scalar")
      | false, _ =>
        if sc.size == destLay.layout.size then .ok sc
        else .error (.undefinedBehavior "transmute scalar size mismatch")
/-- `CastHooks` overlay enforcing `miriTransmuteScalarCheck` inside `copyAllowTransmute`. `Cast.cast`-level ONLY: no `RvalueHooks` / `StepHooks` uses it. -/
def annealCastHooksTransmutePolicy (layouts : LayoutTable) (policy : Ptr2IntTransmutePolicy) :
    Miri.Interpreter.CastHooks AnnealProv AnnealStepState Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealCastHooksFloat layouts with
    copyAllowTransmute := fun _ src dest => do
      let imm ← annealReadImmediate src
      match imm.imm with
      | .uninit => throw (.undefinedBehavior "transmute of uninitialized value")
      | .scalar sc =>
        match miriTransmuteScalarCheck policy dest.layout sc with
        | .ok sc' => annealWriteImmediate (.scalar sc') dest
        | .error err => throw err
      | .scalarPair _ _ => throw (.unsupported "scalarPair transmute") }
private theorem encodeRawPtrTyId_spec (pt : RigidTy) :
    encodeRawPtrTyId pt ≠ 41 ∧ encodeRawPtrTyId pt ≠ 42 ∧
    (∀ sc, annealValidateScalarForTyId (encodeRawPtrTyId pt) sc = true) ∧
    classifyEncodedTyId (encodeRawPtrTyId pt) = .ok .pointer := by
  cases pt with
  | int it => cases it <;> exact ⟨(by intro h; cases h), (by intro h; cases h), fun _ => rfl, rfl⟩
  | uint ut => cases ut <;> exact ⟨(by intro h; cases h), (by intro h; cases h), fun _ => rfl, rfl⟩
  | float ft => cases ft <;> exact ⟨(by intro h; cases h), (by intro h; cases h), fun _ => rfl, rfl⟩
  | tuple ts => cases ts <;> exact ⟨(by intro h; cases h), (by intro h; cases h), fun _ => rfl, rfl⟩
  | _ => exact ⟨(by intro h; cases h), (by intro h; cases h), fun _ => rfl, rfl⟩
/-- **Pinned policy arms of `miriTransmuteScalarCheck`** on a pointer scalar `sc` (`sc.size = lay.size`): `usize` (`25`) and `f64` (`32`) flip (`.strictUcg630Ub` UB vs. `.stripProvenance` stripped address), ANY raw pointer (`encodeRawPtrTyId pt`) preserves `sc` under BOTH policies, and `&T` (`41`) / `fn()` (`42`) accept non-null provenance-carrying pointers while rejecting null pointers under BOTH policies. -/
theorem miriTransmuteScalarCheck_ptr_policy_arms (lay : Miri.ABI.LayoutData)
    (sc : Miri.Memory.Scalar AnnealProv) (hptr : sc.isPointer = true) (hsz : sc.size = lay.size) :
    miriTransmuteScalarCheck .strictUcg630Ub ⟨25, lay⟩ sc =
      .error (.undefinedBehavior "transmute of pointer provenance into non-pointer scalar (ucg#630)") ∧
    miriTransmuteScalarCheck .strictUcg630Ub ⟨32, lay⟩ sc =
      .error (.undefinedBehavior "transmute of pointer provenance into non-pointer scalar (ucg#630)") ∧
    (∀ p, sc.toPointer annealTargetDataLayout = .ok p →
      miriTransmuteScalarCheck .stripProvenance ⟨25, lay⟩ sc =
        (match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 p.offset.bytes.toNat) lay.size with
         | .ok stripped => .ok stripped
         | .error _ => .error (.undefinedBehavior "transmute stripped scalar width mismatch")) ∧
      miriTransmuteScalarCheck .stripProvenance ⟨32, lay⟩ sc =
        (match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 p.offset.bytes.toNat) lay.size with
         | .ok stripped => .ok stripped
         | .error _ => .error (.undefinedBehavior "transmute stripped scalar width mismatch"))) ∧
    (∀ policy (pt : RigidTy), miriTransmuteScalarCheck policy ⟨encodeRawPtrTyId pt, lay⟩ sc = .ok sc) ∧
    (∀ policy p, sc.toPointer annealTargetDataLayout = .ok p →
      p.provenance.isNone = false → (p.offset == Miri.ABI.Size.ZERO) = false →
      miriTransmuteScalarCheck policy ⟨41, lay⟩ sc = .ok sc ∧ miriTransmuteScalarCheck policy ⟨42, lay⟩ sc = .ok sc) ∧
    (∀ policy p, sc.toPointer annealTargetDataLayout = .ok p → (p.offset == Miri.ABI.Size.ZERO) = true →
      miriTransmuteScalarCheck policy ⟨41, lay⟩ sc = .error (.undefinedBehavior "transmute forged reference/fn-pointer without provenance") ∧
      miriTransmuteScalarCheck policy ⟨42, lay⟩ sc = .error (.undefinedBehavior "transmute forged reference/fn-pointer without provenance")) := by
  refine ⟨?_, ?_, fun p hp => ⟨?_, ?_⟩, fun policy pt => ?_, fun policy p hp hprov hnz => ⟨?_, ?_⟩, fun policy p hp hz => ⟨?_, ?_⟩⟩
  · simp [miriTransmuteScalarCheck, annealValidateScalarForTyId, classifyEncodedTyId, hptr]
  · simp [miriTransmuteScalarCheck, annealValidateScalarForTyId, classifyEncodedTyId, hptr]
  · simp [miriTransmuteScalarCheck, annealValidateScalarForTyId, classifyEncodedTyId, hptr, hp, hsz]
  · simp [miriTransmuteScalarCheck, annealValidateScalarForTyId, classifyEncodedTyId, hptr, hp, hsz]
  · obtain ⟨h41, h42, hval, hcls⟩ := encodeRawPtrTyId_spec pt
    unfold miriTransmuteScalarCheck; split
    · next h => exact absurd h h41
    · next h => exact absurd h h42
    · simp [hval, hcls, hptr, hsz]
  · simp [miriTransmuteScalarCheck, hp, hprov, hnz, hsz]
  · simp [miriTransmuteScalarCheck, hp, hprov, hnz, hsz]
  all_goals simp [miriTransmuteScalarCheck, hp, hz]
/-- **Integer-to-raw-pointer transmute (`usize -> *const T` / `*mut T`) passes the check under BOTH policies**: unlike `&T` (`41`) and `fn()` (`42`), raw-pointer destinations accept provenance-free 8-byte integer scalars (including null) as detached provenance, so `Cast.cast` REDUCES TO the destination write `annealWriteImmediate` (whose success depends on `destRef`); cf. `decodePtrBytesNoForge false`. -/
theorem miri_transmute_int_to_rawPtr_ok (layouts : LayoutTable) (policy : Ptr2IntTransmutePolicy)
    (mutbl : MirAst.Mutability) (pt : RigidTy) (msc : Miri.Memory.ScalarInt)
    (hmsc_sz : msc.size = Miri.ABI.Size.ofBytes 8) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) (st : AnnealStepState) :
    let usizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
    let rawPtrTy : Ty := { kind := .rawPtr mutbl pt, layoutIdx := 0 }
    miriTransmuteScalarCheck policy (translateTy rawPtrTy layouts) (.fromScalarInt msc) = .ok (.fromScalarInt msc) ∧
    Miri.Interpreter.Cast.cast (annealCastHooksTransmutePolicy layouts policy) () 16
        ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy usizeTy layouts⟩
        .Transmute (encodeTyId rawPtrTy) ⟨destRef, translateTy rawPtrTy layouts⟩ st =
      annealWriteImmediate (.scalar (.fromScalarInt msc)) ⟨destRef, translateTy rawPtrTy layouts⟩ st := by
  dsimp only
  have hty_usize : translateTy { kind := .uint .usize, layoutIdx := 0 } layouts = ⟨25, scalarLayoutData 8 false⟩ := rfl
  have hty_raw : translateTy { kind := .rawPtr mutbl pt, layoutIdx := 0 } layouts = ⟨encodeRawPtrTyId pt, pointerLayoutData false⟩ := rfl
  have henc_raw : encodeTyId { kind := .rawPtr mutbl pt, layoutIdx := 0 } = encodeRawPtrTyId pt := rfl
  have hchk : miriTransmuteScalarCheck policy ⟨encodeRawPtrTyId pt, pointerLayoutData false⟩ (.fromScalarInt msc) = .ok (.fromScalarInt msc) := by
    obtain ⟨h41, h42, hval, hcls⟩ := encodeRawPtrTyId_spec pt
    have hisp : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).isPointer = false := rfl
    have hscsz : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).size = (pointerLayoutData false).size := by
      change msc.size = Miri.ABI.Size.ofBytes 8; exact hmsc_sz
    unfold miriTransmuteScalarCheck; split
    · next h => exact absurd h h41
    · next h => exact absurd h h42
    · simp [hval, hcls, hisp, hscsz]
  refine ⟨by rw [hty_raw]; exact hchk, ?_⟩
  have hsz1 : (scalarLayoutData 8 false).isSized = true := rfl
  have hsz2 : (pointerLayoutData false).isSized = true := rfl
  have hsz_eq : (scalarLayoutData 8 false).size = (pointerLayoutData false).size := rfl
  have hnb : (Miri.MIR.CastKind.Transmute == Miri.MIR.CastKind.BoxDerefTransmute) = false := rfl
  rw [hty_usize, hty_raw, henc_raw]; unfold Miri.Interpreter.Cast.cast
  simp only [annealCastHooksTransmutePolicy, annealCastHooksFloat, annealCastHooks, hsz1, hsz2, hsz_eq, hnb,
    beq_self_eq_true, bne_self_eq_false, Bool.false_eq_true, Bool.not_true, Bool.or_self, ↓reduceIte,
    pure_bind, annealReadImmediate_scalar, hchk]
private theorem scalar_fromScalarInt_toPointer_none (msc : Miri.Memory.ScalarInt)
    (hmsc_sz : msc.size = Miri.ABI.Size.ofBytes 8) (hmsc_lt : msc.data.toNat < 2 ^ 64) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toPointer annealTargetDataLayout =
      .ok ⟨Miri.ABI.Size.ofBytes (UInt64.ofNat msc.data.toNat), none⟩ := by
  have hle : ¬ (msc.data.toNat > 18446744073709551615) := by omega
  have htb : msc.toBits (Miri.ABI.Size.ofBytes 8) = .ok msc.data := by
    unfold Miri.Memory.ScalarInt.toBits
    have hsz' : (Miri.ABI.Size.ofBytes 8 != msc.size) = false := by rw [hmsc_sz]; rfl
    change (if Miri.ABI.Size.ofBytes 8 != msc.size then
      throw (Miri.Memory.ScalarIntError.sizeMismatch (Miri.ABI.Size.ofBytes 8) msc.size)
      else pure msc.data : Except Miri.Memory.ScalarIntError Miri.ABI.U128) = Except.ok msc.data
    rw [hsz']; rfl
  have h1 : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBitsOrPtrInternal (Miri.ABI.Size.ofBytes 8) =
      .ok (.bits msc.data) := by unfold Miri.Memory.Scalar.toBitsOrPtrInternal Miri.Memory.Scalar.fromScalarInt; dsimp only []; rw [htb]; rfl
  unfold Miri.Memory.Scalar.toPointer
  have hts : (miri_private% Miri.Memory.Scalar Miri.Memory.Scalar.targetPointerSize) annealTargetDataLayout =
      Miri.ABI.Size.ofBytes 8 := rfl
  rw [hts, h1]; simp only [bind, Except.bind, pure, Except.pure, hle, ↓reduceIte]; rfl
/-- **No-forgery UB on `usize -> &u8` transmute (`TyId = 41`) under BOTH policies**. -/
theorem miri_transmute_ref_no_forge_ub (layouts : LayoutTable) (policy : Ptr2IntTransmutePolicy)
    (msc : Miri.Memory.ScalarInt) (hmsc_sz : msc.size = Miri.ABI.Size.ofBytes 8) (hmsc_lt : msc.data.toNat < 2 ^ 64)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) (st : AnnealStepState) :
    let usizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
    let refU8Ty : Ty := { kind := .ref .not (.uint .u8), layoutIdx := 0 }
    Miri.Interpreter.Cast.cast (annealCastHooksTransmutePolicy layouts policy) () 16
        ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy usizeTy layouts⟩
        .Transmute (encodeTyId refU8Ty) ⟨destRef, translateTy refU8Ty layouts⟩ st =
      .error (.undefinedBehavior "transmute forged reference/fn-pointer without provenance") st := by
  dsimp only
  have hty_usize : translateTy { kind := .uint .usize, layoutIdx := 0 } layouts = ⟨25, scalarLayoutData 8 false⟩ := rfl
  have hty_ref : translateTy { kind := .ref .not (.uint .u8), layoutIdx := 0 } layouts = ⟨41, pointerLayoutData true⟩ := rfl
  have henc_ref : encodeTyId { kind := .ref .not (.uint .u8), layoutIdx := 0 } = 41 := rfl
  have htoptr := scalar_fromScalarInt_toPointer_none msc hmsc_sz hmsc_lt
  rw [hty_usize, hty_ref, henc_ref]; unfold Miri.Interpreter.Cast.cast
  simp only [annealCastHooksTransmutePolicy, annealCastHooksFloat, annealCastHooks, Miri.ABI.LayoutData.isSized, pointerLayoutData, scalarLayoutData, beq_self_eq_true,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    pure_bind, annealReadImmediate_scalar, miriTransmuteScalarCheck, htoptr, Option.isNone_none, Bool.true_or]
  rfl
/-- **No-forgery UB on `usize -> fn()` transmute (`TyId = 42`) under BOTH policies**, matching `miri_transmute_ref_no_forge_ub` and `Trusted`'s `decodePtrBytesNoForge true`. -/
theorem miri_transmute_fnPtr_no_forge_ub (layouts : LayoutTable) (policy : Ptr2IntTransmutePolicy)
    (inputs : List RigidTy) (output : RigidTy) (safety : MirAst.Safety) (abi : Layout.CallConv)
    (msc : Miri.Memory.ScalarInt) (hmsc_sz : msc.size = Miri.ABI.Size.ofBytes 8) (hmsc_lt : msc.data.toNat < 2 ^ 64)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) (st : AnnealStepState) :
    let usizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
    let fnPtrTy : Ty := { kind := .fnPtr inputs output safety abi, layoutIdx := 0 }
    Miri.Interpreter.Cast.cast (annealCastHooksTransmutePolicy layouts policy) () 16
        ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy usizeTy layouts⟩
        .Transmute (encodeTyId fnPtrTy) ⟨destRef, translateTy fnPtrTy layouts⟩ st =
      .error (.undefinedBehavior "transmute forged reference/fn-pointer without provenance") st := by
  dsimp only
  have hty_usize : translateTy { kind := .uint .usize, layoutIdx := 0 } layouts = ⟨25, scalarLayoutData 8 false⟩ := rfl
  have hty_fn : translateTy { kind := .fnPtr inputs output safety abi, layoutIdx := 0 } layouts = ⟨42, pointerLayoutData true⟩ := rfl
  have henc_fn : encodeTyId { kind := .fnPtr inputs output safety abi, layoutIdx := 0 } = 42 := rfl
  have htoptr := scalar_fromScalarInt_toPointer_none msc hmsc_sz hmsc_lt
  rw [hty_usize, hty_fn, henc_fn]; unfold Miri.Interpreter.Cast.cast
  simp only [annealCastHooksTransmutePolicy, annealCastHooksFloat, annealCastHooks, Miri.ABI.LayoutData.isSized, pointerLayoutData, scalarLayoutData, beq_self_eq_true,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    pure_bind, annealReadImmediate_scalar, miriTransmuteScalarCheck, htoptr, Option.isNone_none, Bool.true_or]
  rfl
/-- **Uninit transmute UB under BOTH policies**. -/
theorem miri_transmute_uninit_ub (layouts : LayoutTable) (policy : Ptr2IntTransmutePolicy)
    (srcTy dstTy : Ty) (hsrc_sz : (translateTy srcTy layouts).layout.isSized = true) (hdst_sz : (translateTy dstTy layouts).layout.isSized = true)
    (hsize_eq : (translateTy srcTy layouts).layout.size = (translateTy dstTy layouts).layout.size) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) (st : AnnealStepState) :
    Miri.Interpreter.Cast.cast (annealCastHooksTransmutePolicy layouts policy) () 16
        ⟨.immediate .uninit, translateTy srcTy layouts⟩
        .Transmute (encodeTyId dstTy) ⟨destRef, translateTy dstTy layouts⟩ st =
      .error (.undefinedBehavior "read of uninitialized local") st := by
  unfold Miri.Interpreter.Cast.cast
  have henc : encodeTyId dstTy = (translateTy dstTy layouts).ty := rfl
  simp only [annealCastHooksTransmutePolicy, annealCastHooksFloat, annealCastHooks, hsrc_sz, hdst_sz, hsize_eq, henc, beq_self_eq_true, bne_self_eq_false, Bool.false_eq_true,
    Bool.not_true, Bool.or_self, ↓reduceIte, pure_bind, annealReadImmediate_uninit_eq]; rfl
/-! ### 4.3 Concrete Kernel-Checked Shared Witnesses `W1–W12` -/
section Witnesses
open LeanMiriSpec.Correspondence.Witness
private def faF32Ty : Ty := { kind := .float .f32, layoutIdx := 0 }
private def faF16Ty : Ty := { kind := .float .f16, layoutIdx := 0 }
private def faBoolTy : Ty := { kind := .bool, layoutIdx := 0 }
private def faU32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
private def faUsizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
private def faPtrU8Ty : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }
private def faRefU8Ty : Ty := { kind := .ref .not (.uint .u8), layoutIdx := 0 }
private def faF32LayoutTy : Ty := { kind := .float .f32, layoutIdx := 1 }
private def faRetLayout (retTy : Ty) : TypeLayout :=
  match retTy.kind with
  | .bool => lm12BoolLayout
  | _ => lm12I32Layout
private def faFloatLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true
    entries :=
      [ { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .arbitrary [] [], variants := .single 0, isUninhabited := false },
        { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .scalar (.initialized (.float 32) ⟨0, 0xFFFFFFFF⟩), fields := .primitive, variants := .single 0, isUninhabited := false } ] }
private def faF32Const (bits : Nat) : ConstOperand := { ty := faF32Ty, val := .scalar (.int ⟨bits, 4⟩) }
private def faF64Ty : Ty := { kind := .float .f64, layoutIdx := 0 }
private def faF64Const (bits : Nat) : ConstOperand := { ty := faF64Ty, val := .scalar (.int ⟨bits, 8⟩) }
private def faMkBody (name : String) (decls : List LocalDecl) (retTy : Ty) (stmt : StatementKind) : CapturedMir where
  defPath := name; phase := .runtimePostCleanup; role := .subject; argCount := 0
  localDecls := decls
  basicBlocks := [{ statements := [mkStmt stmt], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm12FnAbi (faRetLayout retTy); layouts := emptyLayoutTable; allocations := []
private def faMkState (body : CapturedMir) (locals : List LocalSlot) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals }, memory := (initMachineState body []).memory }
private def faMkFrame (body : CapturedMir) (retTy : Ty)
    (locals : Array (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody body, bodyIdentity := .ofCanonicalIndex 0, functionInstance := { kind := .Item 0, args := #[] },
    extra := (), returnContinuation := .stop false, returnPlace := .frameLocal 0 0 none (translateTy retTy) (.ofAllocationToken 0),
    localsIdentity := .ofAllocationToken 0, locals := locals, vaList := #[], trackCallerArg := none, location := .mir ⟨0, 0⟩ }
private def faMkMiri (body : CapturedMir) (retTy : Ty)
    (locals : Array (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)) : AnnealStepState :=
  { stack := ⟨#[faMkFrame body retTy locals]⟩, machine := AnnealMachine.empty }
private theorem fa_stateRel_1uninit (name : String) (dstTy : Ty) (stmt : StatementKind) :
    let body := faMkBody name [⟨.mut, dstTy, none⟩] dstTy stmt
    StateRelLM3_1 body (faMkState body [.uninit]) (faMkMiri body dstTy #[⟨.live (.immediate .uninit), none⟩]) [] := by
  dsimp only
  refine (StateRel.mk _ rfl rfl ⟨translateTy dstTy, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (fun i _ _ _ _ _ _ hi _ => by revert hi; match i with | 0 | _ + 1 => rintro ⟨⟩)).toLM3_1
  refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
  match i with
  | 0 =>
    have hs : slot = .uninit := by simpa [faMkState, get?] using hslot.symm
    have hm : mls = ⟨.live (.immediate .uninit), none⟩ := by simpa [faMkFrame] using hmls.symm
    subst hs hm; exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 1 => simp [faMkBody, get?] at hdecl
private theorem fa_all_imm_1 (body : CapturedMir) (retTy : Ty)
    (v0 : Miri.Interpreter.Immediate AnnealProv) (l0 : Option Miri.Interpreter.LocalLayout) :
    ∀ tf, (faMkMiri body retTy #[⟨.live (.immediate v0), l0⟩]).stack.frames = #[tf] → IsImmediateFrameLocal tf 0 := by
  intro tf h mls hmls mp hmp; injection h with h₁; injection h₁ with h₂; subst h₂; simp [faMkFrame] at hmls; subst hmls; cases hmp
private theorem fa_all_imm_2 (body : CapturedMir) (retTy : Ty)
    (v0 v1 : Miri.Interpreter.Immediate AnnealProv) (l0 l1 : Option Miri.Interpreter.LocalLayout) :
    ∀ tf, (faMkMiri body retTy #[⟨.live (.immediate v0), l0⟩, ⟨.live (.immediate v1), l1⟩]).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 ∧ IsImmediateFrameLocal tf 1 := by
  intro tf h; injection h with h₁; injection h₁ with h₂; subst h₂
  exact ⟨(fun mls hm mp hmp => by simp [faMkFrame] at hm; subst hm; cases hmp), (fun mls hm mp hmp => by simp [faMkFrame] at hm; subst hm; cases hmp)⟩
private theorem fa_stateRel_2f32 (name : String) (stmt : StatementKind)
    (sc1 : MirAst.ScalarInt) (msc1 : Miri.Memory.ScalarInt) (hrel1 : ScalarRel sc1 msc1) (hsz1 : sc1.sizeBytes = 4) :
    let body := faMkBody name [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩] faF32Ty stmt
    StateRelLM3_1 body (faMkState body [.uninit, .init (.scalar sc1)])
      (faMkMiri body faF32Ty #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), some (translateTy faF32Ty)⟩]) [] := by
  dsimp only
  refine (StateRel.mk _ rfl rfl ⟨translateTy faF32Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (fun i _ _ _ _ _ _ hi _ => by revert hi; match i with | 0 | 1 | _ + 2 => rintro ⟨⟩)).toLM3_1
  refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
  match i with
  | 0 =>
    have hs : slot = .uninit := by simpa [faMkState, get?] using hslot.symm
    have hm : mls = ⟨.live (.immediate .uninit), none⟩ := by simpa [faMkFrame] using hmls.symm
    subst hs hm; exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = ⟨.not, faF32Ty, none⟩ := by simpa [faMkBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar sc1) := by simpa [faMkState, get?] using hslot.symm
    have hm : mls = ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), some (translateTy faF32Ty)⟩ := by simpa [faMkFrame] using hmls.symm
    subst hd hs hm; exact .immediate _ _ (some (translateTy faF32Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ hrel1 (by rw [hsz1]; rfl) (fun h => nomatch h) (fun h => nomatch h)⟩)
  | _ + 2 => simp [faMkBody, get?] at hdecl
private theorem fa_stateRel_3f32 (name : String) (stmt : StatementKind)
    (sc1 sc2 : MirAst.ScalarInt) (msc1 msc2 : Miri.Memory.ScalarInt) (hrel1 : ScalarRel sc1 msc1) (hrel2 : ScalarRel sc2 msc2) (hsz1 : sc1.sizeBytes = 4) (hsz2 : sc2.sizeBytes = 4) :
    let body := faMkBody name [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩] faF32Ty stmt
    StateRelLM3_1 body (faMkState body [.uninit, .init (.scalar sc1), .init (.scalar sc2)])
      (faMkMiri body faF32Ty #[⟨.live (.immediate .uninit), none⟩,
        ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), some (translateTy faF32Ty)⟩,
        ⟨.live (.immediate (.scalar (.fromScalarInt msc2))), some (translateTy faF32Ty)⟩]) [] := by
  dsimp only
  refine (StateRel.mk _ rfl rfl ⟨translateTy faF32Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (fun i _ _ _ _ _ _ hi _ => by revert hi; match i with | 0 | 1 | 2 | _ + 3 => rintro ⟨⟩)).toLM3_1
  refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
  match i with
  | 0 =>
    have hs : slot = .uninit := by simpa [faMkState, get?] using hslot.symm
    have hm : mls = ⟨.live (.immediate .uninit), none⟩ := by simpa [faMkFrame] using hmls.symm
    subst hs hm; exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = ⟨.not, faF32Ty, none⟩ := by simpa [faMkBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar sc1) := by simpa [faMkState, get?] using hslot.symm
    have hm : mls = ⟨.live (.immediate (.scalar (.fromScalarInt msc1))), some (translateTy faF32Ty)⟩ := by simpa [faMkFrame] using hmls.symm
    subst hd hs hm; exact .immediate _ _ (some (translateTy faF32Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ hrel1 (by rw [hsz1]; rfl) (fun h => nomatch h) (fun h => nomatch h)⟩)
  | 2 =>
    have hd : decl = ⟨.not, faF32Ty, none⟩ := by simpa [faMkBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar sc2) := by simpa [faMkState, get?] using hslot.symm
    have hm : mls = ⟨.live (.immediate (.scalar (.fromScalarInt msc2))), some (translateTy faF32Ty)⟩ := by simpa [faMkFrame] using hmls.symm
    subst hd hs hm; exact .immediate _ _ (some (translateTy faF32Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ hrel2 (by rw [hsz2]; rfl) (fun h => nomatch h) (fun h => nomatch h)⟩)
  | _ + 3 => simp [faMkBody, get?] at hdecl
/-- **`W1` Witness (finite, subnormal, overflow, signed-zero)** at `FloatBits.arithmetic` & real `Step.step`. -/
theorem w1_lm_finite_subnormal_overflow :
    let bodyAdd := faMkBody "w1::add" [⟨.mut, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.binaryOp .add (.constant (faF32Const 0x3F800000)) (.constant (faF32Const 0x40000000))))
    let sAdd := faMkState bodyAdd [.uninit]; let mAdd := faMkMiri bodyAdd faF32Ty #[⟨.live (.immediate .uninit), none⟩]
    StepRelLM3_1 bodyAdd mAdd [] (stepMirFn bodyAdd sAdd) (Miri.Interpreter.Step.step (annealStepHooksFloatArith bodyAdd.localDecls bodyAdd.layouts false) () mAdd) ∧
    (∃ s', stepMirFn bodyAdd sAdd = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar ⟨0x40400000, 4⟩))) ∧
    Miri.Interpreter.FloatBits.arithmetic .Add ⟨.binary32, BitVec.ofNat 128 0x00000001⟩ ⟨.binary32, BitVec.ofNat 128 0x00000001⟩ = .ok ⟨.binary32, BitVec.ofNat 128 0x00000002⟩ ∧
    Miri.Interpreter.FloatBits.arithmetic .Add ⟨.binary32, BitVec.ofNat 128 0x7F7FFFFF⟩ ⟨.binary32, BitVec.ofNat 128 0x7F7FFFFF⟩ = .ok ⟨.binary32, BitVec.ofNat 128 0x7F800000⟩ ∧
    Miri.Interpreter.FloatBits.arithmetic .Add ⟨.binary32, BitVec.ofNat 128 0x80000000⟩ ⟨.binary32, BitVec.ofNat 128 0x80000000⟩ = .ok ⟨.binary32, BitVec.ofNat 128 0x80000000⟩ ∧
    Miri.Interpreter.FloatBits.arithmetic .Add ⟨.binary32, BitVec.ofNat 128 0x80000000⟩ ⟨.binary32, BitVec.ofNat 128 0x00000000⟩ = .ok ⟨.binary32, BitVec.ofNat 128 0x00000000⟩ ∧
    Miri.Interpreter.FloatBits.arithmetic .Mul ⟨.binary32, BitVec.ofNat 128 0x80000000⟩ ⟨.binary32, BitVec.ofNat 128 0x00000000⟩ = .ok ⟨.binary32, BitVec.ofNat 128 0x80000000⟩ := by
  dsimp only
  let bodyAdd := faMkBody "w1::add" [⟨.mut, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.binaryOp .add (.constant (faF32Const 0x3F800000)) (.constant (faF32Const 0x40000000))))
  let sAdd := faMkState bodyAdd [.uninit]
  have hstep := step_float_arith_const_const_deterministic_simulation (fa_stateRel_1uninit "w1::add" faF32Ty (.assign (local_ 0) (.binaryOp .add (.constant (faF32Const 0x3F800000)) (.constant (faF32Const 0x40000000)))))
    (fun _ h => nomatch h) annealChooseBinaryNaN (bop := .add) rfl rfl rfl rfl (f := .binary32) rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (fa_all_imm_1 _ _ .uninit none)
  have hadd_ev : evalFloatArithBase .add .binary32 0x3F800000 0x40000000 = .some 0x40400000 := by decide +kernel
  have hstep_val : ∃ s', stepMirFn bodyAdd sAdd = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar ⟨0x40400000, 4⟩)) := by
    rw [stepMirFn_eq_of_not_other bodyAdd sAdd rfl (fun _ h => nomatch h)]
    simp only [bodyAdd, sAdd, faMkBody, faMkState, get?, List.getElem?_cons_zero, mkStmt]; unfold evalStmt; dsimp only []
    rw [evalRvalue_binaryOp_float _ _ _ .add _ _ ⟨0x3F800000, 4⟩ ⟨0x40000000, 4⟩ _ _ _ (fun h => nomatch h) (evalOperand_const_scalar_ok (c := faF32Const 0x3F800000) rfl) (evalOperand_const_scalar_ok (c := faF32Const 0x40000000) rfl) rfl]
    dsimp only [operandTy, faF32Const]; rw [evalFloatScalarBinOp_of_fmt .add ⟨0x3F800000, 4⟩ ⟨0x40000000, 4⟩ faF32Ty faF32Ty .binary32 _ _ rfl rfl rfl rfl]
    unfold evalFloatBinOp; dsimp only [evalFloatCmp]; rw [hadd_ev]; exact ⟨_, rfl, rfl⟩
  have h1 : evalFloatArithBase .add .binary32 0x00000001 0x00000001 = .some 0x00000002 := by decide +kernel
  have h2 : evalFloatArithBase .add .binary32 0x7F7FFFFF 0x7F7FFFFF = .some 0x7F800000 := by decide +kernel
  have h3 : evalFloatArithBase .add .binary32 0x80000000 0x80000000 = .some 0x80000000 := by decide +kernel
  have h4 : evalFloatArithBase .add .binary32 0x80000000 0x00000000 = .some 0x00000000 := by decide +kernel
  have h5 : evalFloatArithBase .mul .binary32 0x80000000 0x00000000 = .some 0x80000000 := by decide +kernel
  have hm1 := floatBits_arithmetic_eq .add .binary32 0x00000001 0x00000001 (by decide) (by decide); rw [h1] at hm1
  have hm2 := floatBits_arithmetic_eq .add .binary32 0x7F7FFFFF 0x7F7FFFFF (by decide) (by decide); rw [h2] at hm2
  have hm3 := floatBits_arithmetic_eq .add .binary32 0x80000000 0x80000000 (by decide) (by decide); rw [h3] at hm3
  have hm4 := floatBits_arithmetic_eq .add .binary32 0x80000000 0x00000000 (by decide) (by decide); rw [h4] at hm4
  have hm5 := floatBits_arithmetic_eq .mul .binary32 0x80000000 0x00000000 (by decide) (by decide); rw [h5] at hm5
  exact ⟨hstep, hstep_val, hm1, hm2, hm3, hm4, hm5⟩
/-- **`W2` Witness (IEEE-754 comparisons & sNaN-preserving unary negation)** at `FloatBits` & `Step.step`. -/
theorem w2_lm_cmp_and_snan_neg :
    let bodyCmp := faMkBody "w2::cmp" [⟨.mut, faBoolTy, none⟩] faBoolTy (.assign (local_ 0) (.binaryOp .eq (.constant (faF32Const 0x80000000)) (.constant (faF32Const 0x00000000))))
    let sCmp := faMkState bodyCmp [.uninit]; let mCmp := faMkMiri bodyCmp faBoolTy #[⟨.live (.immediate .uninit), none⟩]
    let snanMsc : Miri.Memory.ScalarInt := .ofUInt32 0x7FA00001
    let bodyNeg := faMkBody "w2::neg" [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.unaryOp .neg (.copy (local_ 1))))
    let sNeg := faMkState bodyNeg [.uninit, .init (.scalar ⟨0x7FA00001, 4⟩)]
    let mNeg := faMkMiri bodyNeg faF32Ty #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate (.scalar (.fromScalarInt snanMsc))), some (translateTy faF32Ty)⟩]
    StepRelLM3_1 bodyCmp mCmp [] (stepMirFn bodyCmp sCmp) (Miri.Interpreter.Step.step (annealStepHooksFloatArith bodyCmp.localDecls bodyCmp.layouts true) () mCmp) ∧
    (∃ s', stepMirFn bodyCmp sCmp = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar (boolToScalar true)))) ∧
    Miri.Interpreter.FloatBits.comparison .Eq ⟨.binary32, BitVec.ofNat 128 0x7FC00000⟩ ⟨.binary32, BitVec.ofNat 128 0x7FC00000⟩ = .ok false ∧
    Miri.Interpreter.FloatBits.comparison .Ne ⟨.binary32, BitVec.ofNat 128 0x7FC00000⟩ ⟨.binary32, BitVec.ofNat 128 0x7FC00000⟩ = .ok true ∧
    Miri.Interpreter.FloatBits.comparison .Lt ⟨.binary32, BitVec.ofNat 128 0x7FA00001⟩ ⟨.binary32, BitVec.ofNat 128 0x3F800000⟩ = .ok false ∧
    StepRelLM3_1 bodyNeg mNeg [] (stepMirFn bodyNeg sNeg) (Miri.Interpreter.Step.step (annealStepHooksFloatArith bodyNeg.localDecls bodyNeg.layouts true) () mNeg) ∧
    (∃ s', stepMirFn bodyNeg sNeg = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar ⟨0xFFA00001, 4⟩))) ∧
    isSignalingNaNBits .binary32 0xFFA00001 = true := by
  dsimp only
  let bodyCmp := faMkBody "w2::cmp" [⟨.mut, faBoolTy, none⟩] faBoolTy (.assign (local_ 0) (.binaryOp .eq (.constant (faF32Const 0x80000000)) (.constant (faF32Const 0x00000000))))
  let sCmp := faMkState bodyCmp [.uninit]
  let bodyNeg := faMkBody "w2::neg" [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.unaryOp .neg (.copy (local_ 1))))
  let sNeg := faMkState bodyNeg [.uninit, .init (.scalar ⟨0x7FA00001, 4⟩)]
  have hcmp := step_float_cmp_const_const_simulation (fa_stateRel_1uninit "w2::cmp" faBoolTy (.assign (local_ 0) (.binaryOp .eq (.constant (faF32Const 0x80000000)) (.constant (faF32Const 0x00000000)))))
    (fun _ h => nomatch h) true annealChooseBinaryNaN (bop := .eq) rfl rfl rfl rfl (f := .binary32) rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (fa_all_imm_1 _ _ .uninit none)
  have hcmp_ev : evalFloatCmp .eq .binary32 0x80000000 0x00000000 = .some true := by decide +kernel
  have hcmp_val : ∃ s', stepMirFn bodyCmp sCmp = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar (boolToScalar true))) := by
    rw [stepMirFn_eq_of_not_other bodyCmp sCmp rfl (fun _ h => nomatch h)]
    simp only [bodyCmp, sCmp, faMkBody, faMkState, get?, List.getElem?_cons_zero, mkStmt]; unfold evalStmt; dsimp only []
    rw [evalRvalue_binaryOp_float _ _ _ .eq _ _ ⟨0x80000000, 4⟩ ⟨0x00000000, 4⟩ _ _ _ (fun h => nomatch h) (evalOperand_const_scalar_ok (c := faF32Const 0x80000000) rfl) (evalOperand_const_scalar_ok (c := faF32Const 0x00000000) rfl) rfl]
    dsimp only [operandTy, faF32Const]; rw [evalFloatScalarBinOp_of_fmt .eq ⟨0x80000000, 4⟩ ⟨0x00000000, 4⟩ faF32Ty faF32Ty .binary32 _ _ rfl rfl rfl rfl]
    unfold evalFloatBinOp; rw [hcmp_ev]; exact ⟨_, rfl, rfl⟩
  have hsnan_rel : ScalarRel ⟨0x7FA00001, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 0x7FA00001) := ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
  have hneg := step_float_unaryNeg_copy_simulation (fa_stateRel_2f32 "w2::neg" (.assign (local_ 0) (.unaryOp .neg (.copy (local_ 1)))) ⟨0x7FA00001, 4⟩ _ hsnan_rel rfl)
    (fun _ h => nomatch h) true annealChooseBinaryNaN rfl rfl rfl rfl (f := .binary32) rfl rfl (by
      intro tf h; injection h with h₁; injection h₁ with h₂; subst h₂
      exact ⟨(fun mls hm mp hmp => by simp [faMkFrame] at hm; subst hm; cases hmp), (fun mls hm mp hmp => by simp [faMkFrame] at hm; subst hm; cases hmp)⟩)
  have hneg_ev : evalFloatNeg .binary32 0x7FA00001 = 0xFFA00001 := by decide +kernel
  have hneg_val : ∃ s', stepMirFn bodyNeg sNeg = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar ⟨0xFFA00001, 4⟩)) := by
    rw [stepMirFn_eq_of_not_other bodyNeg sNeg rfl (fun _ h => nomatch h)]
    simp only [bodyNeg, sNeg, faMkBody, faMkState, get?, List.getElem?_cons_zero, mkStmt, local_]; unfold evalStmt; dsimp only []
    rw [evalRvalue_unaryOp_neg_float _ _ _ ⟨0x7FA00001, 4⟩ _ [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩] emptyLayoutTable (evalOperand_copy_scalar_ok (locals := [.uninit, .init (.scalar ⟨0x7FA00001, 4⟩)]) (idx := 1) rfl) rfl]
    unfold evalFloatUnaryNeg; rw [operandTy_copy_local (ld := [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩]) (idx := 1) (decl := ⟨.not, faF32Ty, none⟩) rfl]
    dsimp only [faF32Ty, ieeeFormatOfTy?, IeeeFormat.byteWidth, Nat.beq]; rw [hneg_ev]; exact ⟨_, rfl, rfl⟩
  have hc1 := floatBits_comparison_eq .eq .binary32 0x7FC00000 0x7FC00000 (by decide) (by decide)
  have hc2 := floatBits_comparison_eq .ne .binary32 0x7FC00000 0x7FC00000 (by decide) (by decide)
  have hc3 := floatBits_comparison_eq .lt .binary32 0x7FA00001 0x3F800000 (by decide) (by decide)
  have he1 : evalFloatCmp .eq .binary32 0x7FC00000 0x7FC00000 = .some false := by decide +kernel
  have he2 : evalFloatCmp .ne .binary32 0x7FC00000 0x7FC00000 = .some true := by decide +kernel
  have he3 : evalFloatCmp .lt .binary32 0x7FA00001 0x3F800000 = .some false := by decide +kernel
  rw [he1] at hc1; rw [he2] at hc2; rw [he3] at hc3; exact ⟨hcmp, hcmp_val, hc1, hc2, hc3, hneg, hneg_val, by decide +kernel⟩
/-- **`W3` Witness (`miri#5643` `nanChoices` indices `0..5` & `.Sub` candidate order)** at both `FloatBits.nanChoices` and real nondeterministic `Step.step` / `EvalRvalueFloatRel`. -/
theorem w3_lm_nan_choices_and_sub_order :
    let expected6 := [0x7FC00000, 0xFFC00000, 0x7FE00001, 0xFFE00001, 0x7FA00001, 0xFFA00001]
    let snanMsc : Miri.Memory.ScalarInt := .ofUInt32 0x7FA00001; let oneMsc : Miri.Memory.ScalarInt := .ofUInt32 0x3F800000
    let body := faMkBody "w3::nan" [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.binaryOp .add (.copy (local_ 1)) (.copy (local_ 2))))
    let s := faMkState body [.uninit, .init (.scalar ⟨0x7FA00001, 4⟩), .init (.scalar ⟨0x3F800000, 4⟩)]
    let m := faMkMiri body faF32Ty #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate (.scalar (.fromScalarInt snanMsc))), some (translateTy faF32Ty)⟩, ⟨.live (.immediate (.scalar (.fromScalarInt oneMsc))), some (translateTy faF32Ty)⟩]
    (Miri.Interpreter.FloatBits.nanChoices .binary32 [⟨.binary32, BitVec.ofNat 128 0x7FA00001⟩, ⟨.binary32, BitVec.ofNat 128 0x3F800000⟩] true).map (List.map fun fb => fb.bits.toNat) = .ok expected6 ∧
    (∀ bits ∈ expected6, ∃ idx : Nat, StepRelLM3_1 body m [] (MirStepNode.step (advanceStmt s (s.frame.locals.set 0 (.init (.scalar ⟨bits, 4⟩))) s.memory))
        (Miri.Interpreter.Step.step (annealStepHooksFloatArith body.localDecls body.layouts true (fun _ _ => pure idx)) () m)) ∧
    (Miri.Interpreter.FloatBits.nanChoices .binary32 [⟨.binary32, BitVec.ofNat 128 0x3F800000⟩, ⟨.binary32, BitVec.ofNat 128 0x7FC0002A⟩] true).map (List.map fun fb => fb.bits.toNat) = .ok [0x7FC00000, 0xFFC00000, 0x7FC0002A, 0xFFC0002A] ∧
    (Miri.Interpreter.FloatBits.nanChoices .binary32 [⟨.binary32, BitVec.ofNat 128 0x3F800000⟩, ⟨.binary32, BitVec.ofNat 128 (evalFloatNeg .binary32 0x7FC0002A)⟩] true).map (List.map fun fb => fb.bits.toNat) = .ok [0x7FC00000, 0xFFC00000, 0xFFC0002A, 0x7FC0002A] := by
  dsimp only
  let decls : List LocalDecl := [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩]
  let body := faMkBody "w3::nan" decls faF32Ty (.assign (local_ 0) (.binaryOp .add (.copy (local_ 1)) (.copy (local_ 2))))
  let locs : List LocalSlot := [.uninit, .init (.scalar ⟨0x7FA00001, 4⟩), .init (.scalar ⟨0x3F800000, 4⟩)]
  let s := faMkState body locs
  have hnc6 := floatBits_nanChoices_binary_toNat_eq .binary32 0x7FA00001 0x3F800000 (by decide) (by decide) true
  have he6 : nanChoices .binary32 [(.binary32, 0x7FA00001), (.binary32, 0x3F800000)] .nondeterministic = [0x7FC00000, 0xFFC00000, 0x7FE00001, 0xFFE00001, 0x7FA00001, 0xFFA00001] := by decide +kernel
  simp only [↓reduceIte] at hnc6; rw [he6] at hnc6
  have hsub1 := floatBits_nanChoices_binary_toNat_eq .binary32 0x3F800000 0x7FC0002A (by decide) (by decide) true
  have hes1 : nanChoices .binary32 [(.binary32, 0x3F800000), (.binary32, 0x7FC0002A)] .nondeterministic = [0x7FC00000, 0xFFC00000, 0x7FC0002A, 0xFFC0002A] := by decide +kernel
  simp only [↓reduceIte] at hsub1; rw [hes1] at hsub1
  have hsub2 := floatBits_nanChoices_binary_toNat_eq .binary32 0x3F800000 (evalFloatNeg .binary32 0x7FC0002A) (by decide) (evalFloatNeg_lt _ _) true
  have hes2 : nanChoices .binary32 [(.binary32, 0x3F800000), (.binary32, evalFloatNeg .binary32 0x7FC0002A)] .nondeterministic = [0x7FC00000, 0xFFC00000, 0xFFC0002A, 0x7FC0002A] := by decide +kernel
  simp only [↓reduceIte] at hsub2; rw [hes2] at hsub2
  refine ⟨hnc6, ?_, hsub1, hsub2⟩
  intro bits hbits
  have hsnan_rel : ScalarRel ⟨0x7FA00001, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 0x7FA00001) := ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
  have hone_rel : ScalarRel ⟨0x3F800000, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 0x3F800000) := ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
  have hbase : evalFloatArithBase .add .binary32 0x7FA00001 0x3F800000 = .some 0x7FC00000 := by decide +kernel
  have hrel_bin : EvalFloatBinOpRel .nondeterministic .add .binary32 0x7FA00001 0x3F800000 ⟨bits, 4⟩ :=
    (EvalFloatBinOpRel_arith_iff .nondeterministic .add .binary32 0x7FA00001 0x3F800000 ⟨bits, 4⟩ rfl).mpr ⟨0x7FC00000, hbase, Or.inl ⟨by decide +kernel, bits, by rw [he6]; exact hbits, rfl⟩⟩
  have hrv : EvalRvalueFloatRel .nondeterministic .strictUcg630Ub locs (.binaryOp .add (.copy (local_ 1)) (.copy (local_ 2))) s.memory decls emptyLayoutTable (.ok (.scalar ⟨bits, 4⟩) locs s.memory) :=
    (EvalRvalueFloatRel_binaryOp_float_iff .nondeterministic .strictUcg630Ub locs locs locs .add (.copy (local_ 1)) (.copy (local_ 2)) ⟨0x7FA00001, 4⟩ ⟨0x3F800000, 4⟩ faF32Ty faF32Ty .binary32
      s.memory decls emptyLayoutTable _ (fun h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl).mpr (Or.inl ⟨⟨bits, 4⟩, hrel_bin, rfl⟩)
  exact step_float_arith_copy_copy_nondet_completeness (fa_stateRel_3f32 "w3::nan" (.assign (local_ 0) (.binaryOp .add (.copy (local_ 1)) (.copy (local_ 2)))) ⟨0x7FA00001, 4⟩ ⟨0x3F800000, 4⟩ _ _ hsnan_rel hone_rel rfl rfl)
    (bop := .add) rfl rfl rfl rfl rfl rfl (f := .binary32) rfl rfl rfl (by simp [faMkState, get?]) .strictUcg630Ub rfl rfl hrv (by
      intro tf h; injection h with h₁; injection h₁ with h₂; subst h₂
      exact ⟨(fun mls hm mp hmp => by simp [faMkFrame] at hm; subst hm; cases hmp), (fun mls hm mp hmp => by simp [faMkFrame] at hm; subst hm; cases hmp), (fun mls hm mp hmp => by simp [faMkFrame] at hm; subst hm; cases hmp)⟩)
/-- **`W4` Witness (uninit UB, `1.0 / 0.0 = +Inf` vs. int `/ 0` UB, `f16` & `bitXor` fail-closed)**. -/
theorem w4_lm_uninit_divzero_and_f16_boundary :
    let bodyUn := faMkBody "w4::uninit" [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.unaryOp .neg (.copy (local_ 1))))
    let sUn := faMkState bodyUn [.uninit, .uninit]; let mUn := faMkMiri bodyUn faF32Ty #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate .uninit), none⟩]
    let bodyDiv := faMkBody "w4::div0" [⟨.mut, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.binaryOp .div (.constant (faF32Const 0x3F800000)) (.constant (faF32Const 0x00000000))))
    let sDiv := faMkState bodyDiv [.uninit]; let mDiv := faMkMiri bodyDiv faF32Ty #[⟨.live (.immediate .uninit), none⟩]
    let bodyXor := faMkBody "w4::xor" [⟨.mut, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.binaryOp .bitXor (.constant (faF32Const 0x3F800000)) (.constant (faF32Const 0x40000000))))
    let sXor := faMkState bodyXor [.uninit]; let mXor := faMkMiri bodyXor faF32Ty #[⟨.live (.immediate .uninit), none⟩]
    let f16Msc : Miri.Memory.ScalarInt := .ofUInt16 0x3C00
    (stepMirFn bodyUn sUn = .fail .ub ∧ ∃ m', Miri.Interpreter.Step.step (annealStepHooksFloatArith bodyUn.localDecls bodyUn.layouts true) () mUn = (m', .error (.undefinedBehavior "read of uninitialized local"))) ∧
    (StepRelLM3_1 bodyDiv mDiv [] (stepMirFn bodyDiv sDiv) (Miri.Interpreter.Step.step (annealStepHooksFloatArith bodyDiv.localDecls bodyDiv.layouts false) () mDiv) ∧
      ∃ s', stepMirFn bodyDiv sDiv = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar ⟨0x7F800000, 4⟩))) ∧
    (evalScalarBinOp .div ⟨1, 4⟩ ⟨0, 4⟩ [] emptyMemory true = .ub ∧
      Miri.Interpreter.IntegerOps.binary .Div ⟨.ofUInt32 1, ⟨Miri.ABI.Size.ofBytes 4, .i32⟩⟩ ⟨.ofUInt32 0, ⟨Miri.ABI.Size.ofBytes 4, .i32⟩⟩ = .error (.undefinedBehavior .divisionByZero)) ∧
    Miri.Interpreter.FloatOps.unary (annealFloatOpsHooks true) () .Neg ⟨.scalar (.fromScalarInt f16Msc), translateTy faF16Ty emptyLayoutTable⟩ mDiv = .error (.unsupported "floatOps.formatOf: TyId 30 is not f32/f64") mDiv ∧
    (stepMirFn bodyXor sXor = .fail .unsupported ∧ ∃ m', Miri.Interpreter.Step.step (annealStepHooksFloatArith bodyXor.localDecls bodyXor.layouts true) () mXor = (m', .error (.invalidProgram "invalid floating binary operation"))) := by
  dsimp only
  let bodyUn := faMkBody "w4::uninit" [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.unaryOp .neg (.copy (local_ 1))))
  let bodyDiv := faMkBody "w4::div0" [⟨.mut, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.binaryOp .div (.constant (faF32Const 0x3F800000)) (.constant (faF32Const 0x00000000))))
  let sDiv := faMkState bodyDiv [.uninit]
  have hsr_un : StateRelLM3_1 bodyUn (faMkState bodyUn [.uninit, .uninit]) (faMkMiri bodyUn faF32Ty #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate .uninit), none⟩]) [] := by
    refine (StateRel.mk _ rfl rfl ⟨translateTy faF32Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl (fun i _ _ _ _ _ _ hi _ => by revert hi; match i with | 0 | 1 | _ + 2 => rintro ⟨⟩)).toLM3_1
    refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
    match i with
    | 0 | 1 =>
      have hs : slot = .uninit := by simpa [faMkState, get?] using hslot.symm
      have hm : mls = ⟨.live (.immediate .uninit), none⟩ := by simpa [faMkFrame] using hmls.symm
      subst hs hm; exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | _ + 2 => simp [bodyUn, faMkBody, get?] at hdecl
  have hun := step_float_uninit_unaryNeg_ub_lockstep hsr_un (fun _ h => nomatch h) true annealChooseBinaryNaN rfl rfl rfl rfl (f := .binary32) rfl rfl rfl (by
    intro tf h; injection h with h₁; injection h₁ with h₂; subst h₂
    exact ⟨(fun mls hm mp hmp => by simp [faMkFrame] at hm; subst hm; cases hmp), (fun mls hm mp hmp => by simp [faMkFrame] at hm; subst hm; cases hmp)⟩)
  have hdiv := step_float_arith_const_const_deterministic_simulation (fa_stateRel_1uninit "w4::div0" faF32Ty (.assign (local_ 0) (.binaryOp .div (.constant (faF32Const 0x3F800000)) (.constant (faF32Const 0x00000000)))))
    (fun _ h => nomatch h) annealChooseBinaryNaN (bop := .div) rfl rfl rfl rfl (f := .binary32) rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (fa_all_imm_1 _ _ .uninit none)
  have hdiv_ev : evalFloatArithBase .div .binary32 0x3F800000 0x00000000 = .some 0x7F800000 := by decide +kernel
  have hdiv_val : ∃ s', stepMirFn bodyDiv sDiv = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar ⟨0x7F800000, 4⟩)) := by
    rw [stepMirFn_eq_of_not_other bodyDiv sDiv rfl (fun _ h => nomatch h)]
    simp only [bodyDiv, sDiv, faMkBody, faMkState, get?, List.getElem?_cons_zero, mkStmt]; unfold evalStmt; dsimp only []
    rw [evalRvalue_binaryOp_float _ _ _ .div _ _ ⟨0x3F800000, 4⟩ ⟨0x00000000, 4⟩ _ _ _ (fun h => nomatch h) (evalOperand_const_scalar_ok (c := faF32Const 0x3F800000) rfl) (evalOperand_const_scalar_ok (c := faF32Const 0x00000000) rfl) rfl]
    dsimp only [operandTy, faF32Const]; rw [evalFloatScalarBinOp_of_fmt .div ⟨0x3F800000, 4⟩ ⟨0x00000000, 4⟩ faF32Ty faF32Ty .binary32 _ _ rfl rfl rfl rfl]
    unfold evalFloatBinOp; dsimp only [evalFloatCmp]; rw [hdiv_ev]; exact ⟨_, rfl, rfl⟩
  have hxor := step_float_invalid_binOp_fail_closed (fa_stateRel_1uninit "w4::xor" faF32Ty (.assign (local_ 0) (.binaryOp .bitXor (.constant (faF32Const 0x3F800000)) (.constant (faF32Const 0x40000000)))))
    (fun _ h => nomatch h) true annealChooseBinaryNaN (bop := .bitXor) rfl (fun h => nomatch h) rfl rfl rfl (f := .binary32) rfl rfl rfl rfl rfl rfl (by decide) (by decide)
  have hf16 := (floatOps_f16_f128_unsupported emptyLayoutTable true annealChooseQuietedNaN (ty := faF16Ty) (Or.inl rfl) (.ofUInt16 0x3C00) (.ofUInt16 0x3C00) .Add (faMkMiri bodyDiv faF32Ty #[⟨.live (.immediate .uninit), none⟩])).1
  have hf16_msg : s!"floatOps.formatOf: TyId {encodeTyId faF16Ty} is not f32/f64" = "floatOps.formatOf: TyId 30 is not f32/f64" := by decide
  rw [hf16_msg] at hf16; exact ⟨hun, ⟨hdiv, hdiv_val⟩, ⟨rfl, by with_unfolding_all rfl⟩, hf16, hxor⟩
/-- **`W5` Witness (`Ptr2IntTransmutePolicy` flip-direction & `{to,from}_bits` agreement)**. -/
theorem w5_lm_ptr2int_policy_flip :
    let aid : Miri.Memory.AllocId := ⟨1, by decide⟩
    let sz8 := Miri.ABI.Size.ofBytes 8
    let range8 := Miri.Memory.allocRange Miri.ABI.Size.ZERO sz8
    let sz4 := Miri.ABI.Size.ofBytes 4
    let range4 := Miri.Memory.allocRange Miri.ABI.Size.ZERO sz4
    let ptrLocals : List LocalSlot := [.init (.ptr { allocId := 1, offsetBytes := 0x1000 } 8)]
    let ptrDecls : List LocalDecl := [⟨.not, faPtrU8Ty, none⟩]
    let f32Locals : List LocalSlot := [.init (.scalar ⟨0x3F800000, 4⟩)]
    let f32Decls : List LocalDecl := [⟨.not, faF32LayoutTy, none⟩]
    (((Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance) (Array.replicate 8 0) Miri.ABI.Align.ONE .Mut).bind fun a0 =>
      match Miri.Memory.Allocation.writeScalar annealTargetDataLayout range8
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes 0x1000, .concrete aid .one⟩) a0 with
      | .ok () a1 => a1.readScalar annealTargetDataLayout range8 false
      | .error e _ => .error e) =
      (Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 0x1000) sz8 |>.mapError Miri.Memory.AllocError.scalar) ∧
      evalByteCast ptrLocals (.copy (local_ 0)) faUsizeTy emptyMemory ptrDecls emptyLayoutTable .stripProvenance = .ok (.scalar ⟨0x1000, 8⟩) ptrLocals emptyMemory) ∧
    ((∃ (provCtfe : Miri.Memory.CtfeProvenance) (pm : Miri.Memory.ProvenanceMap Miri.Memory.CtfeProvenance) (aCtfe : Miri.Memory.Allocation Miri.Memory.CtfeProvenance Unit),
      Miri.Memory.CtfeProvenance.fromAllocId aid = .ok provCtfe ∧
      Miri.Memory.ProvenanceMap.insertPtr Miri.ABI.Size.ZERO provCtfe sz8 Miri.Memory.ProvenanceMap.new = .ok () pm ∧
      aCtfe.provenanceMap = pm ∧
      aCtfe.readScalar annealTargetDataLayout range8 false = .error (.readPointerAsInt none)) ∧
      evalByteCast ptrLocals (.copy (local_ 0)) faUsizeTy emptyMemory ptrDecls emptyLayoutTable .strictUcg630Ub = .ub) ∧
    (((Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance) #[0x00, 0x00, 0x80, 0x3F] Miri.ABI.Align.ONE .Mut).bind fun a => a.readScalar annealTargetDataLayout range4 false) =
      (Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 0x3F800000) sz4 |>.mapError Miri.Memory.AllocError.scalar) ∧
      ((Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.CtfeProvenance) #[0x00, 0x00, 0x80, 0x3F] Miri.ABI.Align.ONE .Mut).bind fun a => a.readScalar annealTargetDataLayout range4 false) =
      (Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 0x3F800000) sz4 |>.mapError Miri.Memory.AllocError.scalar) ∧
      ∀ policy, evalByteCast f32Locals (.copy (local_ 0)) faU32Ty emptyMemory f32Decls faFloatLayouts policy = .ok (.scalar ⟨0x3F800000, 4⟩) f32Locals emptyMemory) := by
  dsimp only
  have hlt : (1 : UInt64) < 4611686018427387904 := by decide
  have hp_ex : ∃ provCtfe, Miri.Memory.CtfeProvenance.fromAllocId ⟨1, by decide⟩ = .ok provCtfe := by
    unfold Miri.Memory.CtfeProvenance.fromAllocId; simp [hlt]
  obtain ⟨provCtfe, hp_ok⟩ := hp_ex
  have hctfe : ∃ (pm : Miri.Memory.ProvenanceMap Miri.Memory.CtfeProvenance)
      (aCtfe : Miri.Memory.Allocation Miri.Memory.CtfeProvenance Unit),
      Miri.Memory.ProvenanceMap.insertPtr Miri.ABI.Size.ZERO provCtfe (Miri.ABI.Size.ofBytes 8) Miri.Memory.ProvenanceMap.new = .ok () pm ∧
      aCtfe.provenanceMap = pm ∧
      aCtfe.readScalar annealTargetDataLayout (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) false =
        .error (.readPointerAsInt none) := by
    let sz8 := Miri.ABI.Size.ofBytes 8; let range8 := Miri.Memory.allocRange Miri.ABI.Size.ZERO sz8
    have hins := Miri.Memory.ProvenanceMap.insertPtr_new Miri.ABI.Size.ZERO sz8 sz8 provCtfe (by decide) (by rfl)
    let pm := (miri_private% Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.mk) #[(Miri.ABI.Size.ZERO, provCtfe)] none
    have hfilt : (Array.filter (fun entry : Miri.ABI.Size × Miri.Memory.CtfeProvenance =>
        Miri.ABI.Size.ZERO.bytes ≤ entry.1.bytes && entry.1.bytes < sz8.bytes) #[(Miri.ABI.Size.ZERO, provCtfe)]).isEmpty = false := by
      simp [sz8, Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes, Array.isEmpty]
    have hre_empty : pm.rangeEmpty range8 sz8 = .ok false := by
      unfold Miri.Memory.ProvenanceMap.rangeEmpty Miri.Memory.ProvenanceMap.rangePtrs
      have hadj : (miri_private% Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.adjustedStart) range8 sz8 = .ok Miri.ABI.Size.ZERO := rfl
      have hend : (miri_private% Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.rangeEnd) range8 = .ok sz8 := rfl
      change (do
        let ptrs ← do
          let start ← (miri_private% Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.adjustedStart) range8 sz8
          let finish ← (miri_private% Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.rangeEnd) range8
          pure ((miri_private% Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.rangeEntries) #[(Miri.ABI.Size.ZERO, provCtfe)] start finish)
        if !ptrs.isEmpty then pure false else do let b ← pm.rangeBytes range8; pure b.isEmpty) = .ok false
      rw [hadj, hend]; simp only [bind, Except.bind, pure, Except.pure]
      have hre : ((miri_private% Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.rangeEntries)
          #[(Miri.ABI.Size.ZERO, provCtfe)] Miri.ABI.Size.ZERO sz8).isEmpty = false := hfilt
      rw [hre]; rfl
    let aCtfe : Miri.Memory.Allocation Miri.Memory.CtfeProvenance Unit :=
      (miri_private% Miri.Memory.Allocation Miri.Memory.Allocation.mk)
        #[0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] sz8 pm (Miri.Memory.InitMask.new sz8 true) Miri.ABI.Align.ONE .Mut () none
    refine ⟨pm, aCtfe, hins, rfl, alloc_readScalar_ctfe_rejects_prov aCtfe annealTargetDataLayout range8
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl) hre_empty⟩
  obtain ⟨pm, aCtfe, hins, hpm, hrej⟩ := hctfe
  refine ⟨⟨by with_unfolding_all rfl, rfl⟩, ⟨⟨provCtfe, pm, aCtfe, hp_ok, hins, hpm, hrej⟩, rfl⟩,
    ⟨by with_unfolding_all rfl, by with_unfolding_all rfl, fun policy => by cases policy <;> rfl⟩⟩
/-- **`W6` Witness (no-forgery `usize -> &u8` & uninit UB under BOTH policies)**. -/
theorem w6_lm_no_forge_ref_uninit (st : AnnealStepState) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    let sz8 := Miri.ABI.Size.ofBytes 8
    let range8 := Miri.Memory.allocRange Miri.ABI.Size.ZERO sz8
    let usizeLocals : List LocalSlot := [.init (.scalar ⟨0x1000, 8⟩)]
    let usizeDecls : List LocalDecl := [⟨.not, faUsizeTy, none⟩]
    let uninitLocals : List LocalSlot := [.uninit]
    (∀ policy,
      evalByteCast usizeLocals (.copy (local_ 0)) faRefU8Ty emptyMemory usizeDecls emptyLayoutTable policy = .ub ∧
      Miri.Interpreter.Cast.cast (annealCastHooksTransmutePolicy emptyLayoutTable policy) () 16 ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 0x1000))), translateTy faUsizeTy emptyLayoutTable⟩
        .Transmute (encodeTyId faRefU8Ty) ⟨destRef, translateTy faRefU8Ty emptyLayoutTable⟩ st = .error (.undefinedBehavior "transmute forged reference/fn-pointer without provenance") st) ∧
    (∀ policy,
      evalByteCast uninitLocals (.copy (local_ 0)) faUsizeTy emptyMemory usizeDecls emptyLayoutTable policy = .ub ∧
      Miri.Interpreter.Cast.cast (annealCastHooksTransmutePolicy emptyLayoutTable policy) () 16 ⟨.immediate .uninit, translateTy faUsizeTy emptyLayoutTable⟩
        .Transmute (encodeTyId faUsizeTy) ⟨destRef, translateTy faUsizeTy emptyLayoutTable⟩ st = .error (.undefinedBehavior "read of uninitialized local") st) ∧
    ((Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance) sz8 Miri.ABI.Align.ONE .Uninit (fun s _ => some (Array.replicate s.bytes.toNat 0))).bind fun a => a.readScalar annealTargetDataLayout range8 false) =
      .error (.invalidUninitBytes (some ⟨range8, range8⟩)) ∧
    ((Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.CtfeProvenance) sz8 Miri.ABI.Align.ONE .Uninit (fun s _ => some (Array.replicate s.bytes.toNat 0))).bind fun a => a.readScalar annealTargetDataLayout range8 false) =
      .error (.invalidUninitBytes (some ⟨range8, range8⟩)) := by
  dsimp only
  refine ⟨fun policy => ⟨by cases policy <;> rfl,
      miri_transmute_ref_no_forge_ub emptyLayoutTable policy (.ofUInt64 0x1000) rfl (by decide) destRef st⟩,
    fun policy => ⟨by cases policy <;> rfl,
      miri_transmute_uninit_ub emptyLayoutTable policy faUsizeTy faUsizeTy rfl rfl rfl destRef st⟩,
    by with_unfolding_all rfl, by with_unfolding_all rfl⟩
/-- **`W7` Witness (round-1 hardening)**: `binary64` engine parity (`FloatBits.{arithmetic, negate, comparison, nanChoices}`), index-exact `.Sub` NaN-candidate order at real `FloatOps.binary` (index `2` is the UN-NEGATED quieted rhs `0x7FC0002A`, index `3` its negation), `∞ - ∞` under the default `annealChooseBinaryNaN` selector, and the pinned `miriTransmuteScalarCheck` policy arms on a real provenance-carrying pointer scalar. -/
theorem w7_lm_f64_and_sub_index_exact (st : AnnealStepState) (lay : Miri.ABI.LayoutData)
    (hlay : lay.size = Miri.ABI.Size.ofBytes 8) :
    Miri.Interpreter.FloatBits.arithmetic .Add ⟨.binary64, BitVec.ofNat 128 0x1⟩ ⟨.binary64, BitVec.ofNat 128 0x1⟩ = .ok ⟨.binary64, BitVec.ofNat 128 0x2⟩ ∧
    Miri.Interpreter.FloatBits.arithmetic .Sub ⟨.binary64, BitVec.ofNat 128 0x4008000000000000⟩ ⟨.binary64, BitVec.ofNat 128 0x3FF0000000000000⟩ = .ok ⟨.binary64, BitVec.ofNat 128 0x4000000000000000⟩ ∧
    Miri.Interpreter.FloatBits.negate ⟨.binary64, BitVec.ofNat 128 0x7FF4000000000001⟩ = .ok ⟨.binary64, BitVec.ofNat 128 0xFFF4000000000001⟩ ∧
    Miri.Interpreter.FloatBits.comparison .Eq ⟨.binary64, BitVec.ofNat 128 0x8000000000000000⟩ ⟨.binary64, BitVec.ofNat 128 0x0⟩ = .ok true ∧
    (Miri.Interpreter.FloatBits.nanChoices .binary64 [⟨.binary64, BitVec.ofNat 128 0x7FF4000000000001⟩, ⟨.binary64, BitVec.ofNat 128 0x3FF0000000000000⟩] true).map (List.map fun fb => fb.bits.toNat) =
      .ok [0x7FF8000000000000, 0xFFF8000000000000, 0x7FFC000000000001, 0xFFFC000000000001, 0x7FF4000000000001, 0xFFF4000000000001] ∧
    (∃ msc', ScalarRel ⟨0x7FC0002A, 4⟩ msc' ∧
      Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks true (fun _ _ => pure 2)) () .Sub ⟨.scalar (.fromScalarInt (.ofUInt32 0x3F800000)), translateTy faF32Ty emptyLayoutTable⟩ ⟨.scalar (.fromScalarInt (.ofUInt32 0x7FC0002A)), translateTy faF32Ty emptyLayoutTable⟩ =
        pure ⟨.scalar (.fromScalarInt msc'), translateTy faF32Ty emptyLayoutTable⟩) ∧
    (∃ msc', ScalarRel ⟨0xFFC0002A, 4⟩ msc' ∧
      Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks true (fun _ _ => pure 3)) () .Sub ⟨.scalar (.fromScalarInt (.ofUInt32 0x3F800000)), translateTy faF32Ty emptyLayoutTable⟩ ⟨.scalar (.fromScalarInt (.ofUInt32 0x7FC0002A)), translateTy faF32Ty emptyLayoutTable⟩ =
        pure ⟨.scalar (.fromScalarInt msc'), translateTy faF32Ty emptyLayoutTable⟩) ∧
    (∃ outSc msc', EvalFloatBinOpRel .nondeterministic .sub .binary32 0x7F800000 0x7F800000 outSc ∧ ScalarRel outSc msc' ∧
      Miri.Interpreter.FloatOps.binary (annealFloatOpsHooks true annealChooseBinaryNaN) () .Sub ⟨.scalar (.fromScalarInt (.ofUInt32 0x7F800000)), translateTy faF32Ty emptyLayoutTable⟩ ⟨.scalar (.fromScalarInt (.ofUInt32 0x7F800000)), translateTy faF32Ty emptyLayoutTable⟩ st =
        .ok ⟨.scalar (.fromScalarInt msc'), translateTy faF32Ty emptyLayoutTable⟩ st) ∧
    (∃ ptrSc : Miri.Memory.Scalar AnnealProv, ptrSc.isPointer = true ∧
      ptrSc.toPointer annealTargetDataLayout = .ok ⟨Miri.ABI.Size.ofBytes 0x1000, some (.concrete ⟨1, by decide⟩ .one)⟩ ∧
      miriTransmuteScalarCheck .strictUcg630Ub ⟨25, lay⟩ ptrSc = .error (.undefinedBehavior "transmute of pointer provenance into non-pointer scalar (ucg#630)") ∧
      (∀ policy, miriTransmuteScalarCheck policy ⟨70, lay⟩ ptrSc = .ok ptrSc)) := by
  have h1 : evalFloatArithBase .add .binary64 0x1 0x1 = .some 0x2 := by decide +kernel
  have h2 : evalFloatArithBase .sub .binary64 0x4008000000000000 0x3FF0000000000000 = .some 0x4000000000000000 := by decide +kernel
  have hm1 := floatBits_arithmetic_eq .add .binary64 0x1 0x1 (by decide) (by decide); rw [h1] at hm1
  have hm2 := floatBits_arithmetic_eq .sub .binary64 0x4008000000000000 0x3FF0000000000000 (by decide) (by decide); rw [h2] at hm2
  have hneg := floatBits_negate_eq .binary64 0x7FF4000000000001 (by decide)
  have hnegv : evalFloatNeg .binary64 0x7FF4000000000001 = 0xFFF4000000000001 := by decide +kernel
  rw [hnegv] at hneg
  have hcmp := floatBits_comparison_eq .eq .binary64 0x8000000000000000 0x0 (by decide) (by decide)
  have hcmpv : evalFloatCmp .eq .binary64 0x8000000000000000 0x0 = .some true := by decide +kernel
  rw [hcmpv] at hcmp
  have hnc := floatBits_nanChoices_binary_toNat_eq .binary64 0x7FF4000000000001 0x3FF0000000000000 (by decide) (by decide) true
  have hncv : nanChoices .binary64 [(.binary64, 0x7FF4000000000001), (.binary64, 0x3FF0000000000000)] .nondeterministic =
      [0x7FF8000000000000, 0xFFF8000000000000, 0x7FFC000000000001, 0xFFFC000000000001, 0x7FF4000000000001, 0xFFF4000000000001] := by decide +kernel
  simp only [↓reduceIte] at hnc; rw [hncv] at hnc
  have hone : ScalarRel ⟨0x3F800000, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 0x3F800000) := ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
  have hq : ScalarRel ⟨0x7FC0002A, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 0x7FC0002A) := ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
  have hinf : ScalarRel ⟨0x7F800000, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 0x7F800000) := ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
  have hsb : evalFloatArithBase .sub .binary32 0x3F800000 0x7FC0002A = .some 0x7FC00000 := by decide +kernel
  have hsn : isNaNBits .binary32 0x7FC00000 = true := by decide +kernel
  have hs2 : (nanChoices .binary32 [(.binary32, 0x3F800000), (.binary32, 0x7FC0002A)] .nondeterministic)[2]? = some 0x7FC0002A := by decide +kernel
  have hs3 : (nanChoices .binary32 [(.binary32, 0x3F800000), (.binary32, 0x7FC0002A)] .nondeterministic)[3]? = some 0xFFC0002A := by decide +kernel
  have hsub2 := floatOps_binary_arith_pure_index_exact emptyLayoutTable 2 (op := .sub) rfl (lTy := faF32Ty) (rTy := faF32Ty) (f := .binary32) rfl rfl hone hq rfl rfl (baseBits := 0x7FC00000) (outBits := 0x7FC0002A) hsb (Or.inl ⟨hsn, hs2⟩)
  have hsub3 := floatOps_binary_arith_pure_index_exact emptyLayoutTable 3 (op := .sub) rfl (lTy := faF32Ty) (rTy := faF32Ty) (f := .binary32) rfl rfl hone hq rfl rfl (baseBits := 0x7FC00000) (outBits := 0xFFC0002A) hsb (Or.inl ⟨hsn, hs3⟩)
  have hdef := floatOps_binary_arith_any_chooseNaN_rel emptyLayoutTable annealChooseBinaryNaN annealChooseBinaryNaN_valid (op := .sub) rfl (lTy := faF32Ty) (rTy := faF32Ty) (f := .binary32) rfl rfl hinf hinf rfl rfl st
  have hp := miriTransmuteScalarCheck_ptr_policy_arms lay (Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes 0x1000, .concrete ⟨1, by decide⟩ .one⟩) rfl (by rw [hlay]; rfl)
  refine ⟨hm1, hm2, hneg, hcmp, hnc, hsub2, hsub3, hdef, ?_⟩
  exact ⟨_, rfl, by with_unfolding_all rfl, hp.1, fun policy => hp.2.2.2.1 policy (.uint .u8)⟩
/-- **`W8` Witness (round-1 counter-audit)**: real-step `const/const` nondeterministic `sNaN + 1.0` & `∞ - ∞` index-exact & `annealChooseBinaryNaN` soundness, `usize -> *const u8` (valid under BOTH policies!) vs. `usize -> &u8` / `usize -> fn()` (UB under BOTH policies!), and exact-message uninit binary float UB lockstep. -/
theorem w8_lm_const_nondet_rawPtr_vs_ref_and_uninit_binop (st : AnnealStepState) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    let bodySnan := faMkBody "w8::const_snan" [⟨.mut, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.binaryOp .add (.constant (faF32Const 0x7FA00001)) (.constant (faF32Const 0x3F800000))))
    let sSnan := faMkState bodySnan [.uninit]; let mSnan := faMkMiri bodySnan faF32Ty #[⟨.live (.immediate .uninit), none⟩]
    let bodyInf := faMkBody "w8::const_inf" [⟨.mut, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.binaryOp .sub (.constant (faF32Const 0x7F800000)) (.constant (faF32Const 0x7F800000))))
    let sInf := faMkState bodyInf [.uninit]; let mInf := faMkMiri bodyInf faF32Ty #[⟨.live (.immediate .uninit), none⟩]
    let fnUnitTy : Ty := { kind := .fnPtr [] (.tuple []) .safe .rust, layoutIdx := 0 }
    let bodyUnBin := faMkBody "w8::uninit_bin" [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.binaryOp .add (.copy (local_ 1)) (.copy (local_ 2))))
    let sUnBin := faMkState bodyUnBin [.uninit, .init (.scalar ⟨0x3F800000, 4⟩), .uninit]
    let mUnBin := faMkMiri bodyUnBin faF32Ty #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt32 0x3F800000)))), some (translateTy faF32Ty)⟩, ⟨.live (.immediate .uninit), none⟩]
    (∀ (idx bits : Nat), (nanChoices .binary32 [(.binary32, 0x7FA00001), (.binary32, 0x3F800000)] .nondeterministic)[idx]? = some bits →
      StepRelLM3_1 bodySnan mSnan [] (MirStepNode.step (advanceStmt sSnan (sSnan.frame.locals.set 0 (.init (.scalar ⟨bits, 4⟩))) sSnan.memory))
        (Miri.Interpreter.Step.step (annealStepHooksFloatArith bodySnan.localDecls bodySnan.layouts true (fun _ _ => pure idx)) () mSnan)) ∧
    (∃ outSc, (∀ policy, EvalRvalueFloatRel .nondeterministic policy sInf.frame.locals (.binaryOp .sub (.constant (faF32Const 0x7F800000)) (.constant (faF32Const 0x7F800000)))
        sInf.memory bodyInf.localDecls bodyInf.layouts (.ok (.scalar outSc) sInf.frame.locals sInf.memory)) ∧
      StepRelLM3_1 bodyInf mInf [] (MirStepNode.step (advanceStmt sInf (sInf.frame.locals.set 0 (.init (.scalar outSc))) sInf.memory))
        (Miri.Interpreter.Step.step (annealStepHooksFloatArith bodyInf.localDecls bodyInf.layouts true annealChooseBinaryNaN) () mInf)) ∧
    (∀ (idx bits : Nat), (nanChoices .binary32 [(.binary32, 0x7F800000), (.binary32, 0x7F800000)] .nondeterministic)[idx]? = some bits →
      StepRelLM3_1 bodyInf mInf [] (MirStepNode.step (advanceStmt sInf (sInf.frame.locals.set 0 (.init (.scalar ⟨bits, 4⟩))) sInf.memory))
        (Miri.Interpreter.Step.step (annealStepHooksFloatArith bodyInf.localDecls bodyInf.layouts true (fun _ _ => pure idx)) () mInf)) ∧
    (∀ policy,
      evalByteCast [.init (.scalar ⟨0x1000, 8⟩)] (.copy (local_ 0)) faPtrU8Ty emptyMemory [⟨.not, faUsizeTy, none⟩] emptyLayoutTable policy = .ok (.scalar ⟨0x1000, 8⟩) [.init (.scalar ⟨0x1000, 8⟩)] emptyMemory ∧
      evalByteCast [.init (.scalar ⟨0, 8⟩)] (.copy (local_ 0)) faPtrU8Ty emptyMemory [⟨.not, faUsizeTy, none⟩] emptyLayoutTable policy = .ok (.scalar ⟨0, 8⟩) [.init (.scalar ⟨0, 8⟩)] emptyMemory ∧
      Miri.Interpreter.Cast.cast (annealCastHooksTransmutePolicy emptyLayoutTable policy) () 16 ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 0x1000))), translateTy faUsizeTy emptyLayoutTable⟩
        .Transmute (encodeTyId faPtrU8Ty) ⟨destRef, translateTy faPtrU8Ty emptyLayoutTable⟩ st = annealWriteImmediate (.scalar (.fromScalarInt (.ofUInt64 0x1000))) ⟨destRef, translateTy faPtrU8Ty emptyLayoutTable⟩ st ∧
      evalByteCast [.init (.scalar ⟨0x1000, 8⟩)] (.copy (local_ 0)) fnUnitTy emptyMemory [⟨.not, faUsizeTy, none⟩] emptyLayoutTable policy = .ub ∧
      Miri.Interpreter.Cast.cast (annealCastHooksTransmutePolicy emptyLayoutTable policy) () 16 ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 0x1000))), translateTy faUsizeTy emptyLayoutTable⟩
        .Transmute (encodeTyId fnUnitTy) ⟨destRef, translateTy fnUnitTy emptyLayoutTable⟩ st = .error (.undefinedBehavior "transmute forged reference/fn-pointer without provenance") st) ∧
    (stepMirFn bodyUnBin sUnBin = .fail .ub ∧
      ∃ m', Miri.Interpreter.Step.step (annealStepHooksFloatArith bodyUnBin.localDecls bodyUnBin.layouts true) () mUnBin = (m', .error (.undefinedBehavior "read of uninitialized local"))) := by
  dsimp only
  have hsn_base : evalFloatArithBase .add .binary32 0x7FA00001 0x3F800000 = .some 0x7FC00000 := by decide +kernel
  have hinf_base : evalFloatArithBase .sub .binary32 0x7F800000 0x7F800000 = .some 0x7FC00000 := by decide +kernel
  have hnan : isNaNBits .binary32 0x7FC00000 = true := by decide +kernel
  have hone_rel : ScalarRel ⟨0x3F800000, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 0x3F800000) := ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
  let bodyUnBin := faMkBody "w8::uninit_bin" [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.binaryOp .add (.copy (local_ 1)) (.copy (local_ 2))))
  have hsr_unbin : StateRelLM3_1 bodyUnBin (faMkState bodyUnBin [.uninit, .init (.scalar ⟨0x3F800000, 4⟩), .uninit])
      (faMkMiri bodyUnBin faF32Ty #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt32 0x3F800000)))), some (translateTy faF32Ty)⟩, ⟨.live (.immediate .uninit), none⟩]) [] := by
    refine (StateRel.mk _ rfl rfl ⟨translateTy faF32Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl (fun i _ _ _ _ _ _ hi _ => by revert hi; match i with | 0 | 1 | 2 | _ + 3 => rintro ⟨⟩)).toLM3_1
    refine ⟨rfl, rfl, rfl, rfl, fun i decl slot mls hdecl hslot hmls => ?_⟩
    match i with
    | 0 | 2 =>
      have hs : slot = .uninit := by simpa [faMkState, get?] using hslot.symm
      have hm : mls = ⟨.live (.immediate .uninit), none⟩ := by simpa [faMkFrame] using hmls.symm
      subst hs hm; exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 1 =>
      have hd : decl = ⟨.not, faF32Ty, none⟩ := by simpa [bodyUnBin, faMkBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨0x3F800000, 4⟩) := by simpa [faMkState, get?] using hslot.symm
      have hm : mls = ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt32 0x3F800000)))), some (translateTy faF32Ty)⟩ := by simpa [faMkFrame] using hmls.symm
      subst hd hs hm; exact .immediate _ _ (some (translateTy faF32Ty)) (fun _ h => Option.some.inj h.symm) (Or.inr ⟨_, rfl, .scalar _ _ hone_rel rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
    | _ + 3 => simp [bodyUnBin, faMkBody, get?] at hdecl
  refine ⟨fun idx bits hget => step_float_arith_const_const_nondet_index_exact
      (fa_stateRel_1uninit "w8::const_snan" faF32Ty (.assign (local_ 0) (.binaryOp .add (.constant (faF32Const 0x7FA00001)) (.constant (faF32Const 0x3F800000)))))
      (bop := .add) rfl rfl rfl rfl (f := .binary32) rfl rfl rfl (by simp [faMkState, get?]) idx rfl rfl rfl rfl (by decide) (by decide) hsn_base (Or.inl ⟨hnan, hget⟩) (fa_all_imm_1 _ _ .uninit none),
    step_float_arith_const_const_nondet_soundness
      (fa_stateRel_1uninit "w8::const_inf" faF32Ty (.assign (local_ 0) (.binaryOp .sub (.constant (faF32Const 0x7F800000)) (.constant (faF32Const 0x7F800000)))))
      annealChooseBinaryNaN annealChooseBinaryNaN_valid (bop := .sub) rfl rfl rfl rfl (f := .binary32) rfl rfl rfl (by simp [faMkState, get?]) rfl rfl rfl rfl (by decide) (by decide) (fa_all_imm_1 _ _ .uninit none),
    fun idx bits hget => step_float_arith_const_const_nondet_index_exact
      (fa_stateRel_1uninit "w8::const_inf" faF32Ty (.assign (local_ 0) (.binaryOp .sub (.constant (faF32Const 0x7F800000)) (.constant (faF32Const 0x7F800000)))))
      (bop := .sub) rfl rfl rfl rfl (f := .binary32) rfl rfl rfl (by simp [faMkState, get?]) idx rfl rfl rfl rfl (by decide) (by decide) hinf_base (Or.inl ⟨hnan, hget⟩) (fa_all_imm_1 _ _ .uninit none),
    fun policy => ⟨by cases policy <;> rfl, by cases policy <;> rfl, (miri_transmute_int_to_rawPtr_ok emptyLayoutTable policy .not (.uint .u8) (.ofUInt64 0x1000) rfl destRef st).2, by cases policy <;> rfl, miri_transmute_fnPtr_no_forge_ub emptyLayoutTable policy [] (.tuple []) .safe .rust (.ofUInt64 0x1000) rfl (by decide) destRef st⟩,
    step_float_uninit_binaryOp_ub_lockstep hsr_unbin (fun _ h => nomatch h) true annealChooseBinaryNaN rfl rfl rfl rfl rfl (f := .binary32) rfl rfl (Or.inr ⟨⟨0x3F800000, 4⟩, rfl, rfl⟩) (by
      intro tf h; injection h with h₁; injection h₁ with h₂; subst h₂
      exact ⟨(fun mls hm mp hmp => by simp [faMkFrame] at hm; subst hm; cases hmp), (fun mls hm mp hmp => by simp [faMkFrame] at hm; subst hm; cases hmp), (fun mls hm mp hmp => by simp [faMkFrame] at hm; subst hm; cases hmp)⟩)⟩
/-- **`W9` Witness (`B2`: `%` keeps the DIVIDEND's sign, including on an exactly-zero remainder)**: direct kernel evaluation of BOTH engines (independent of `floatBits_arithmetic_eq`) on `(lhs, rhs, result)` bit triples — `-2.0 % 2.0 = -0.0` (NOT `+0.0`), `2.0 % -2.0 = +0.0`, `-5.0 % 2.0 = -1.0`, `5.0 % -2.0 = 1.0`, `-0.5 % 1.0 = -0.5`, subnormal `-3ε % 2ε = -ε`, `-MAX % ε = -0.0`, `-2.0 % +∞ = -2.0`, `-0.0 % 2.0 = -0.0`, and the NaN cases `-2.0 % -0.0` / `-∞ % 2.0` — on `f32` AND `f64`: vendored `FloatBits.arithmetic .Rem` and `Trusted` `evalFloatArithBase .rem` agree bit-for-bit. -/
theorem w9_lm_rem_dividend_sign_and_zero_remainder :
    (∀ p ∈ [(0xC0000000, 0x40000000, 0x80000000), (0x40000000, 0xC0000000, 0x00000000), (0xC0A00000, 0x40000000, 0xBF800000),
        (0x40A00000, 0xC0000000, 0x3F800000), (0xBF000000, 0x3F800000, 0xBF000000), (0x80000003, 0x00000002, 0x80000001),
        (0xFF7FFFFF, 0x00000001, 0x80000000), (0xC0000000, 0x7F800000, 0xC0000000), (0x80000000, 0x40000000, 0x80000000),
        (0xC0000000, 0x80000000, 0x7FC00000), (0xFF800000, 0x40000000, 0x7FC00000)],
      Miri.Interpreter.FloatBits.arithmetic .Rem ⟨.binary32, BitVec.ofNat 128 p.1⟩ ⟨.binary32, BitVec.ofNat 128 p.2.1⟩ =
        .ok ⟨.binary32, BitVec.ofNat 128 p.2.2⟩ ∧ evalFloatArithBase .rem .binary32 p.1 p.2.1 = .some p.2.2) ∧
    (∀ p ∈ [(0xC000000000000000, 0x4000000000000000, 0x8000000000000000), (0x4000000000000000, 0xC000000000000000, 0),
        (0xC014000000000000, 0x4000000000000000, 0xBFF0000000000000), (0xBFE0000000000000, 0x3FF0000000000000, 0xBFE0000000000000),
        (0x8000000000000003, 0x0000000000000002, 0x8000000000000001), (0xFFEFFFFFFFFFFFFF, 0x0000000000000001, 0x8000000000000000),
        (0xC000000000000000, 0xFFF0000000000000, 0xC000000000000000), (0xC000000000000000, 0x8000000000000000, 0x7FF8000000000000)],
      Miri.Interpreter.FloatBits.arithmetic .Rem ⟨.binary64, BitVec.ofNat 128 p.1⟩ ⟨.binary64, BitVec.ofNat 128 p.2.1⟩ =
        .ok ⟨.binary64, BitVec.ofNat 128 p.2.2⟩ ∧ evalFloatArithBase .rem .binary64 p.1 p.2.1 = .some p.2.2) := by
  decide +kernel
/-- **`W10` Witness (`B3`: ALL FIVE IEEE-754 indeterminate forms on BOTH engines)**: direct kernel evaluation (independent of `floatBits_arithmetic_eq` and `floatBits_nanChoices_binary_toNat_eq`) of `0 / 0`, `∞ / ∞`, `0 × ∞`, `x % 0`, `∞ % y` with every signed variant (`-0.0 / +0.0`, `-∞ / -∞`, `-0.0 × +∞`, `-∞ × -0.0`, `1.0 % -0.0`, `-∞ % 1.0`, `∞ % ∞`, …) on `f32` AND `f64`, as `(Trusted op, Miri op, lhs, rhs)` tuples: vendored `FloatBits.arithmetic` and `Trusted` `evalFloatArithBase` BOTH return the POSITIVE-sign canonical qNaN `preferredNaN` (`0x7FC00000` and `0x7FF8000000000000`; never the sign-flipped x86 "default NaN" nor an operand-derived sign), and with ZERO input NaNs BOTH nondeterministic `nanChoices` are EXACTLY the 2-element `[pref, -pref]` list (so only selector indices `0, 1` are valid). -/
theorem w10_lm_indeterminate_forms_preferredNaN :
    (∀ p ∈ ([(MirAst.BinOp.div, Miri.MIR.BinOp.Div, 0x00000000, 0x00000000), (.div, .Div, 0x80000000, 0x00000000), (.div, .Div, 0x00000000, 0x80000000), (.div, .Div, 0x80000000, 0x80000000), (.div, .Div, 0x7F800000, 0x7F800000), (.div, .Div, 0xFF800000, 0x7F800000), (.div, .Div, 0x7F800000, 0xFF800000), (.div, .Div, 0xFF800000, 0xFF800000), (.mul, .Mul, 0x00000000, 0x7F800000), (.mul, .Mul, 0x80000000, 0x7F800000), (.mul, .Mul, 0x7F800000, 0x00000000),
        (.mul, .Mul, 0xFF800000, 0x80000000), (.mul, .Mul, 0x00000000, 0xFF800000), (.rem, .Rem, 0x3F800000, 0x00000000), (.rem, .Rem, 0x3F800000, 0x80000000), (.rem, .Rem, 0xBF800000, 0x00000000), (.rem, .Rem, 0x00000000, 0x00000000), (.rem, .Rem, 0x7F800000, 0x3F800000), (.rem, .Rem, 0xFF800000, 0x3F800000), (.rem, .Rem, 0x7F800000, 0xBF800000), (.rem, .Rem, 0x7F800000, 0x7F800000), (.rem, .Rem, 0xFF800000, 0x00000000)] : List (MirAst.BinOp × Miri.MIR.BinOp × Nat × Nat)),
      Miri.Interpreter.FloatBits.arithmetic p.2.1 ⟨.binary32, BitVec.ofNat 128 p.2.2.1⟩ ⟨.binary32, BitVec.ofNat 128 p.2.2.2⟩ = .ok ⟨.binary32, BitVec.ofNat 128 0x7FC00000⟩ ∧ evalFloatArithBase p.1 .binary32 p.2.2.1 p.2.2.2 = .some 0x7FC00000 ∧
      nanChoices .binary32 [(.binary32, p.2.2.1), (.binary32, p.2.2.2)] .nondeterministic = [0x7FC00000, 0xFFC00000] ∧ (Miri.Interpreter.FloatBits.nanChoices .binary32 [⟨.binary32, BitVec.ofNat 128 p.2.2.1⟩, ⟨.binary32, BitVec.ofNat 128 p.2.2.2⟩] true).map (List.map fun fb => fb.bits.toNat) = .ok [0x7FC00000, 0xFFC00000]) ∧
    (∀ p ∈ ([(MirAst.BinOp.div, Miri.MIR.BinOp.Div, 0x0000000000000000, 0x0000000000000000), (.div, .Div, 0x8000000000000000, 0x0000000000000000), (.div, .Div, 0x8000000000000000, 0x8000000000000000), (.div, .Div, 0x7FF0000000000000, 0x7FF0000000000000), (.div, .Div, 0xFFF0000000000000, 0x7FF0000000000000), (.div, .Div, 0xFFF0000000000000, 0xFFF0000000000000), (.mul, .Mul, 0x0000000000000000, 0x7FF0000000000000), (.mul, .Mul, 0x8000000000000000, 0x7FF0000000000000),
        (.mul, .Mul, 0x7FF0000000000000, 0x0000000000000000), (.mul, .Mul, 0xFFF0000000000000, 0x8000000000000000), (.rem, .Rem, 0x3FF0000000000000, 0x0000000000000000), (.rem, .Rem, 0x3FF0000000000000, 0x8000000000000000), (.rem, .Rem, 0xBFF0000000000000, 0x0000000000000000), (.rem, .Rem, 0x7FF0000000000000, 0x3FF0000000000000), (.rem, .Rem, 0xFFF0000000000000, 0x3FF0000000000000), (.rem, .Rem, 0x7FF0000000000000, 0x7FF0000000000000)] : List (MirAst.BinOp × Miri.MIR.BinOp × Nat × Nat)),
      Miri.Interpreter.FloatBits.arithmetic p.2.1 ⟨.binary64, BitVec.ofNat 128 p.2.2.1⟩ ⟨.binary64, BitVec.ofNat 128 p.2.2.2⟩ = .ok ⟨.binary64, BitVec.ofNat 128 0x7FF8000000000000⟩ ∧ evalFloatArithBase p.1 .binary64 p.2.2.1 p.2.2.2 = .some 0x7FF8000000000000 ∧
      nanChoices .binary64 [(.binary64, p.2.2.1), (.binary64, p.2.2.2)] .nondeterministic = [0x7FF8000000000000, 0xFFF8000000000000] ∧ (Miri.Interpreter.FloatBits.nanChoices .binary64 [⟨.binary64, BitVec.ofNat 128 p.2.2.1⟩, ⟨.binary64, BitVec.ofNat 128 p.2.2.2⟩] true).map (List.map fun fb => fb.bits.toNat) = .ok [0x7FF8000000000000, 0xFFF8000000000000]) := by
  decide +kernel
/-- **`W11` Witness (`B3`: real `binary64` `Step.step` & mixed `const - copy qNaN` `.sub` candidate order)**: for `f64` (`faF64Ty`, 8-byte immediates) `const 1.0_f64 - const qNaN(0x7FF800000000002A)`, (0) the deterministic REAL `Miri.Interpreter.Step.step` ↔ `stepMirFn` simulation, whose `Trusted` step is kernel-EVALUATED to store `0x7FF8000000000000`, and (1) the index-exact nondeterministic REAL `Step.step` ↔ `Trusted` successor states; plus (2) the same index-exact correspondence for mixed-operand `f32` `const 1.0 - copy qNaN(0x7FC0002A)` (via `step_float_arith_const_copy_nondet_index_exact`), each paired with the pinned ordered candidate list: index `2` is the UN-NEGATED quieted rhs and index `3` its negation (the negated-rhs order `[…, -q, q]` would swap them), so under `fun _ _ => pure 2` real `Step.step` stores the rhs payload with its ORIGINAL sign. -/
theorem w11_lm_f64_step_and_const_copy_nondet_sub_order :
    let body64 := faMkBody "w11::f64_sub" [⟨.mut, faF64Ty, none⟩] faF64Ty (.assign (local_ 0) (.binaryOp .sub (.constant (faF64Const 0x3FF0000000000000)) (.constant (faF64Const 0x7FF800000000002A))))
    let s64 := faMkState body64 [.uninit]; let m64 := faMkMiri body64 faF64Ty #[⟨.live (.immediate .uninit), none⟩]
    let bodyKC := faMkBody "w11::sub_const_copy" [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.binaryOp .sub (.constant (faF32Const 0x3F800000)) (.copy (local_ 1))))
    let sKC := faMkState bodyKC [.uninit, .init (.scalar ⟨0x7FC0002A, 4⟩)]
    let mKC := faMkMiri bodyKC faF32Ty #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt32 0x7FC0002A)))), some (translateTy faF32Ty)⟩]
    StepRelLM3_1 body64 m64 [] (stepMirFn body64 s64) (Miri.Interpreter.Step.step (annealStepHooksFloatArith body64.localDecls body64.layouts false) () m64) ∧
    (match stepMirFn body64 s64 with | .step s' => (get? s'.frame.locals 0).map (fun sl => match sl with | .init (.scalar sc) => (sc.bits, sc.sizeBytes) | _ => (0, 0)) | _ => none) = some (0x7FF8000000000000, 8) ∧
    (∀ (idx bits : Nat), (nanChoices .binary64 [(.binary64, 0x3FF0000000000000), (.binary64, 0x7FF800000000002A)] .nondeterministic)[idx]? = some bits →
      StepRelLM3_1 body64 m64 [] (MirStepNode.step (advanceStmt s64 (s64.frame.locals.set 0 (.init (.scalar ⟨bits, 8⟩))) s64.memory))
        (Miri.Interpreter.Step.step (annealStepHooksFloatArith body64.localDecls body64.layouts true (fun _ _ => pure idx)) () m64)) ∧
    nanChoices .binary64 [(.binary64, 0x3FF0000000000000), (.binary64, 0x7FF800000000002A)] .nondeterministic = [0x7FF8000000000000, 0xFFF8000000000000, 0x7FF800000000002A, 0xFFF800000000002A] ∧
    (∀ (idx bits : Nat), (nanChoices .binary32 [(.binary32, 0x3F800000), (.binary32, 0x7FC0002A)] .nondeterministic)[idx]? = some bits →
      StepRelLM3_1 bodyKC mKC [] (MirStepNode.step (advanceStmt sKC (sKC.frame.locals.set 0 (.init (.scalar ⟨bits, 4⟩))) sKC.memory))
        (Miri.Interpreter.Step.step (annealStepHooksFloatArith bodyKC.localDecls bodyKC.layouts true (fun _ _ => pure idx)) () mKC)) ∧
    nanChoices .binary32 [(.binary32, 0x3F800000), (.binary32, 0x7FC0002A)] .nondeterministic = [0x7FC00000, 0xFFC00000, 0x7FC0002A, 0xFFC0002A] := by
  dsimp only
  have h64b : evalFloatArithBase .sub .binary64 0x3FF0000000000000 0x7FF800000000002A = .some 0x7FF8000000000000 := by decide +kernel
  have h64n : isNaNBits .binary64 0x7FF8000000000000 = true := by decide +kernel
  have hkb : evalFloatArithBase .sub .binary32 0x3F800000 0x7FC0002A = .some 0x7FC00000 := by decide +kernel
  have hkn : isNaNBits .binary32 0x7FC00000 = true := by decide +kernel
  have hq : ScalarRel ⟨0x7FC0002A, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 0x7FC0002A) := ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
  refine ⟨step_float_arith_const_const_deterministic_simulation (fa_stateRel_1uninit "w11::f64_sub" faF64Ty (.assign (local_ 0) (.binaryOp .sub (.constant (faF64Const 0x3FF0000000000000)) (.constant (faF64Const 0x7FF800000000002A))))) (fun _ h => nomatch h) annealChooseBinaryNaN
      (bop := .sub) rfl rfl rfl rfl (f := .binary64) rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (fa_all_imm_1 _ _ .uninit none),
    by decide +kernel,
    fun idx bits hget => step_float_arith_const_const_nondet_index_exact (fa_stateRel_1uninit "w11::f64_sub" faF64Ty (.assign (local_ 0) (.binaryOp .sub (.constant (faF64Const 0x3FF0000000000000)) (.constant (faF64Const 0x7FF800000000002A)))))
      (bop := .sub) rfl rfl rfl rfl (f := .binary64) rfl rfl rfl (by simp [faMkState, get?]) idx rfl rfl rfl rfl (by decide) (by decide) h64b (Or.inl ⟨h64n, hget⟩) (fa_all_imm_1 _ _ .uninit none),
    by decide +kernel,
    fun idx bits hget => step_float_arith_const_copy_nondet_index_exact (fa_stateRel_2f32 "w11::sub_const_copy" (.assign (local_ 0) (.binaryOp .sub (.constant (faF32Const 0x3F800000)) (.copy (local_ 1)))) ⟨0x7FC0002A, 4⟩ _ hq rfl)
      (bop := .sub) rfl rfl rfl rfl rfl (f := .binary32) rfl rfl rfl (by simp [faMkState, get?]) idx rfl rfl (by decide) rfl hkb (Or.inl ⟨hkn, hget⟩) (fa_all_imm_2 _ _ _ _ _ _),
    by decide +kernel⟩
/-- **`W12` Witness (`A3`: symmetric mixed `copy - const` nondet `Step.step` & two-NaN operand-order flip)**: instantiates `step_float_arith_copy_const_nondet_index_exact` on `copy qNaN(0x7FC0002A) - const 1.0` (matching `W11`'s `const 1.0 - copy qNaN(0x7FC0002A)` over indices `0..3` since neither negates rhs and `1.0` is non-NaN) AND contrasts `copy qNaN(0x7FC0002A) - const qNaN(0x7FC00007)` vs. `const qNaN(0x7FC00007) - copy qNaN(0x7FC0002A)`, where real `Step.step` index `2` and index `4` swap `0x7FC0002A` ↔ `0x7FC00007` with NEITHER rhs negated! -/
theorem w12_lm_copy_const_nondet_sub_and_order_flip :
    let bodyCK := faMkBody "w12::sub_copy_const" [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.binaryOp .sub (.copy (local_ 1)) (.constant (faF32Const 0x3F800000))))
    let sCK := faMkState bodyCK [.uninit, .init (.scalar ⟨0x7FC0002A, 4⟩)]
    let mCK := faMkMiri bodyCK faF32Ty #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt32 0x7FC0002A)))), some (translateTy faF32Ty)⟩]
    let bodyFlipCK := faMkBody "w12::sub_flip_ck" [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.binaryOp .sub (.copy (local_ 1)) (.constant (faF32Const 0x7FC00007))))
    let sFlipCK := faMkState bodyFlipCK [.uninit, .init (.scalar ⟨0x7FC0002A, 4⟩)]
    let mFlipCK := faMkMiri bodyFlipCK faF32Ty #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt32 0x7FC0002A)))), some (translateTy faF32Ty)⟩]
    let bodyFlipKC := faMkBody "w12::sub_flip_kc" [⟨.mut, faF32Ty, none⟩, ⟨.not, faF32Ty, none⟩] faF32Ty (.assign (local_ 0) (.binaryOp .sub (.constant (faF32Const 0x7FC00007)) (.copy (local_ 1))))
    let sFlipKC := faMkState bodyFlipKC [.uninit, .init (.scalar ⟨0x7FC0002A, 4⟩)]
    let mFlipKC := faMkMiri bodyFlipKC faF32Ty #[⟨.live (.immediate .uninit), none⟩, ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt32 0x7FC0002A)))), some (translateTy faF32Ty)⟩]
    (∀ (idx bits : Nat), (nanChoices .binary32 [(.binary32, 0x7FC0002A), (.binary32, 0x3F800000)] .nondeterministic)[idx]? = some bits →
      StepRelLM3_1 bodyCK mCK [] (MirStepNode.step (advanceStmt sCK (sCK.frame.locals.set 0 (.init (.scalar ⟨bits, 4⟩))) sCK.memory))
        (Miri.Interpreter.Step.step (annealStepHooksFloatArith bodyCK.localDecls bodyCK.layouts true (fun _ _ => pure idx)) () mCK)) ∧
    nanChoices .binary32 [(.binary32, 0x7FC0002A), (.binary32, 0x3F800000)] .nondeterministic = [0x7FC00000, 0xFFC00000, 0x7FC0002A, 0xFFC0002A] ∧
    (∀ (idx bits : Nat), (nanChoices .binary32 [(.binary32, 0x7FC0002A), (.binary32, 0x7FC00007)] .nondeterministic)[idx]? = some bits →
      StepRelLM3_1 bodyFlipCK mFlipCK [] (MirStepNode.step (advanceStmt sFlipCK (sFlipCK.frame.locals.set 0 (.init (.scalar ⟨bits, 4⟩))) sFlipCK.memory))
        (Miri.Interpreter.Step.step (annealStepHooksFloatArith bodyFlipCK.localDecls bodyFlipCK.layouts true (fun _ _ => pure idx)) () mFlipCK)) ∧
    nanChoices .binary32 [(.binary32, 0x7FC0002A), (.binary32, 0x7FC00007)] .nondeterministic = [0x7FC00000, 0xFFC00000, 0x7FC0002A, 0xFFC0002A, 0x7FC00007, 0xFFC00007] ∧
    (∀ (idx bits : Nat), (nanChoices .binary32 [(.binary32, 0x7FC00007), (.binary32, 0x7FC0002A)] .nondeterministic)[idx]? = some bits →
      StepRelLM3_1 bodyFlipKC mFlipKC [] (MirStepNode.step (advanceStmt sFlipKC (sFlipKC.frame.locals.set 0 (.init (.scalar ⟨bits, 4⟩))) sFlipKC.memory))
        (Miri.Interpreter.Step.step (annealStepHooksFloatArith bodyFlipKC.localDecls bodyFlipKC.layouts true (fun _ _ => pure idx)) () mFlipKC)) ∧
    nanChoices .binary32 [(.binary32, 0x7FC00007), (.binary32, 0x7FC0002A)] .nondeterministic = [0x7FC00000, 0xFFC00000, 0x7FC00007, 0xFFC00007, 0x7FC0002A, 0xFFC0002A] := by
  dsimp only
  have hckb : evalFloatArithBase .sub .binary32 0x7FC0002A 0x3F800000 = .some 0x7FC00000 := by decide +kernel
  have hfckb : evalFloatArithBase .sub .binary32 0x7FC0002A 0x7FC00007 = .some 0x7FC00000 := by decide +kernel
  have hfkcb : evalFloatArithBase .sub .binary32 0x7FC00007 0x7FC0002A = .some 0x7FC00000 := by decide +kernel
  have hnan : isNaNBits .binary32 0x7FC00000 = true := by decide +kernel
  have hq : ScalarRel ⟨0x7FC0002A, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 0x7FC0002A) := ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
  refine ⟨fun idx bits hget => step_float_arith_copy_const_nondet_index_exact (fa_stateRel_2f32 "w12::sub_copy_const" (.assign (local_ 0) (.binaryOp .sub (.copy (local_ 1)) (.constant (faF32Const 0x3F800000)))) ⟨0x7FC0002A, 4⟩ _ hq rfl)
      (bop := .sub) rfl rfl rfl rfl rfl (f := .binary32) rfl rfl rfl (by simp [faMkState, get?]) idx rfl rfl rfl (by decide) hckb (Or.inl ⟨hnan, hget⟩) (fa_all_imm_2 _ _ _ _ _ _),
    by decide +kernel,
    fun idx bits hget => step_float_arith_copy_const_nondet_index_exact (fa_stateRel_2f32 "w12::sub_flip_ck" (.assign (local_ 0) (.binaryOp .sub (.copy (local_ 1)) (.constant (faF32Const 0x7FC00007)))) ⟨0x7FC0002A, 4⟩ _ hq rfl)
      (bop := .sub) rfl rfl rfl rfl rfl (f := .binary32) rfl rfl rfl (by simp [faMkState, get?]) idx rfl rfl rfl (by decide) hfckb (Or.inl ⟨hnan, hget⟩) (fa_all_imm_2 _ _ _ _ _ _),
    by decide +kernel,
    fun idx bits hget => step_float_arith_const_copy_nondet_index_exact (fa_stateRel_2f32 "w12::sub_flip_kc" (.assign (local_ 0) (.binaryOp .sub (.constant (faF32Const 0x7FC00007)) (.copy (local_ 1)))) ⟨0x7FC0002A, 4⟩ _ hq rfl)
      (bop := .sub) rfl rfl rfl rfl rfl (f := .binary32) rfl rfl rfl (by simp [faMkState, get?]) idx rfl rfl (by decide) rfl hfkcb (Or.inl ⟨hnan, hget⟩) (fa_all_imm_2 _ _ _ _ _ _),
    by decide +kernel⟩
end Witnesses
/-! ### 4.4 Complete Module Axiom Audit (EVERY Public Theorem Pinned to Standard Axioms) -/
section AxiomAudit
set_option linter.defProp false in
/-- Master axiom-audit bundle referencing EVERY public theorem of `LeanMiriSpec.FloatArithLM`. -/
def axiomAudit_floatArithLM :=
  And.intro (@floatBits_negate_eq) <| And.intro (@floatBits_partialCompare_eq) <| And.intro (@floatBits_comparison_eq) <| And.intro (@floatBits_exactSum_eq) <|
  And.intro (@floatBits_arithmetic_eq) <| And.intro (@floatBits_nanChoices_list_eq) <| And.intro (@floatBits_nanChoices_binary_eq) <| And.intro (@floatBits_nanChoices_binary_bits_eq) <|
  And.intro (@floatBits_nanChoices_binary_toNat_eq) <| And.intro (@validBinaryChooseNaN_pure) <| And.intro (@floatOps_unary_neg_eq) <| And.intro (@floatOps_unary_nonNeg_err) <|
  And.intro (@floatOps_binary_cmp_eq) <| And.intro (@floatOps_binary_arith_deterministic_eq) <| And.intro (@floatOps_binary_arith_any_chooseNaN_rel) <| And.intro (@floatOps_binary_arith_completeness) <|
  And.intro (@floatOps_binary_unsupported_err) <| And.intro (@floatOps_f16_f128_unsupported) <| And.intro (@scalarOps_binary_floatArith_eq_base) <| And.intro (@scalarOps_unary_floatArith_eq_base) <|
  And.intro (@evalStatement_floatArith_eq_base_of_stmtFree) <| And.intro (@step_floatArith_eq_base_of_floatArithFree) <| And.intro (@step_floatArith_eq_annealStepHooks_at_terminator) <|
  And.intro (@step_float_unaryNeg_copy_simulation) <| And.intro (@step_float_unaryNeg_move_simulation) <| And.intro (@step_float_unaryNeg_constant_simulation) <|
  And.intro (@step_float_unaryNeg_copy_indirect_simulation) <| And.intro (@step_float_cmp_copy_copy_simulation) <| And.intro (@step_float_cmp_const_const_simulation) <|
  And.intro (@step_float_arith_copy_copy_deterministic_simulation) <| And.intro (@step_float_arith_const_const_deterministic_simulation) <|
  And.intro (@step_float_arith_copy_const_deterministic_simulation) <| And.intro (@step_float_arith_const_copy_deterministic_simulation) <|
  And.intro (@step_float_arith_move_copy_deterministic_simulation) <| And.intro (@step_float_arith_const_const_indirect_dst_deterministic_simulation) <|
  And.intro (@step_float_arith_copy_copy_nondet_soundness) <| And.intro (@step_float_arith_copy_copy_nondet_completeness) <| And.intro (@step_float_uninit_unaryNeg_ub_lockstep) <|
  And.intro (@step_float_f16_f128_fail_closed) <| And.intro (@step_float_invalid_binOp_fail_closed) <| And.intro (@alloc_readScalar_strip_runtime) <| And.intro (@alloc_readScalar_ctfe_rejects_prov) <|
  And.intro (@alloc_readScalar_ctfe_provFree_ok) <| And.intro (@alloc_readScalar_uninit_both) <| And.intro (@miri_transmute_ref_no_forge_ub) <| And.intro (@miri_transmute_uninit_ub) <|
  And.intro (@w1_lm_finite_subnormal_overflow) <| And.intro (@w2_lm_cmp_and_snan_neg) <| And.intro (@w3_lm_nan_choices_and_sub_order) <| And.intro (@w4_lm_uninit_divzero_and_f16_boundary) <|
  And.intro (@w5_lm_ptr2int_policy_flip) <| And.intro (@w6_lm_no_forge_ref_uninit) <| And.intro (@annealChooseBinaryNaN_valid) <| And.intro (@annealChooseBinaryNaN_valid_nonempty) <|
  And.intro (@annealChooseQuietedNaN_not_validBinary) <| And.intro (@floatOps_binary_arith_pure_index_exact) <| And.intro (@step_float_arith_copy_copy_nondet_index_exact) <|
  And.intro (@step_float_arith_const_const_nondet_soundness) <| And.intro (@step_float_arith_const_const_nondet_index_exact) <| And.intro (@step_float_uninit_binaryOp_ub_lockstep) <|
  And.intro (@miriTransmuteScalarCheck_ptr_policy_arms) <| And.intro (@miri_transmute_int_to_rawPtr_ok) <| And.intro (@miri_transmute_fnPtr_no_forge_ub) <|
  And.intro (@w7_lm_f64_and_sub_index_exact) <| And.intro (@w8_lm_const_nondet_rawPtr_vs_ref_and_uninit_binop) <| And.intro (@w9_lm_rem_dividend_sign_and_zero_remainder) <|
  And.intro (@step_float_arith_const_copy_nondet_index_exact) <| And.intro (@step_float_arith_copy_const_nondet_index_exact) <|
  And.intro (@w10_lm_indeterminate_forms_preferredNaN) <| And.intro (@w11_lm_f64_step_and_const_copy_nondet_sub_order) <| @w12_lm_copy_const_nondet_sub_and_order_flip
/-- info: 'LeanMiriSpec.FloatArithLM.axiomAudit_floatArithLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms axiomAudit_floatArithLM
open Lean Elab Command in
/-- Walk every declaration elaborated in `LeanMiriSpec.FloatArithLM` and assert that only standard Lean axioms (`propext`, `Quot.sound`, `Classical.choice`) are used. -/
elab "#assert_float_arith_lm_standard_axioms" : command => do
  let env ← getEnv
  let mut checked : Nat := 0
  for (c, _) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
  if checked == 0 then
    throwError "LeanMiriSpec.FloatArithLM: found 0 module declarations"
  logInfo m!"LeanMiriSpec.FloatArithLM: verified standard axioms for {checked} declarations (0 sorryAx, 0 ofReduceBool)"
#assert_float_arith_lm_standard_axioms
end AxiomAudit
end LeanMiriSpec.FloatArithLM
