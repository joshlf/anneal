import LeanMiriSpec.Correspondence.SimLM1_4
/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.Relation

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. BitVec & Modular Arithmetic Bridge Lemmas -/

theorem scalarModulus_eq_two_pow (sz : Nat) :
    scalarModulus sz = 2 ^ (8 * sz) := by
  induction sz with
  | zero => rfl
  | succ k ih =>
    show 256 * scalarModulus k = 2 ^ (8 * (k + 1))
    rw [ih, show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mul_comm]

theorem scalarPow2_eq_two_pow (k : Nat) :
    scalarPow2 k = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show 2 * scalarPow2 k = 2 ^ (k + 1)
    rw [ih, Nat.pow_succ, Nat.mul_comm]

theorem wrapScalarBits_eq_mod (v m : Nat) :
    wrapScalarBits v m = v % m := by
  unfold wrapScalarBits
  cases h : Nat.ble m v with
  | true => rfl
  | false =>
    have hle : ¬ m ≤ v := by
      intro hle'
      have := Nat.ble_eq_true_of_le hle'
      rw [h] at this
      contradiction
    show v = v % m
    exact (Nat.mod_eq_of_lt (by omega)).symm

theorem validScalarBytes_bits_le_128 {sz : Nat} (h : ValidScalarBytes sz) :
    8 * sz ≤ 128 ∧ 0 < 8 * sz := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> omega

theorem validScalarBytes_modulus_le_u128 {sz : Nat} (h : ValidScalarBytes sz) :
    scalarModulus sz ≤ 2 ^ 128 := by
  rw [scalarModulus_eq_two_pow]
  have ⟨hle, _⟩ := validScalarBytes_bits_le_128 h
  exact Nat.pow_le_pow_right (by decide) hle

theorem bitVec_ofNat_toNat_of_valid {sz x : Nat}
    (hsz : ValidScalarBytes sz) (hx : x < scalarModulus sz) :
    (BitVec.ofNat 128 x).toNat = x := by
  have hle := validScalarBytes_modulus_le_u128 hsz
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx hle)

/-- Mathematical integer decoded from an unsigned bit pattern `x < 2 ^ (8 * sz)`
with signedness `signed`. -/
def decodeBitsInt (signed : Bool) (sz : Nat) (x : Nat) : Int :=
  if signed then
    if x < 2 ^ (8 * sz - 1) then (x : Int)
    else (x : Int) - (2 ^ (8 * sz) : Nat)
  else
    (x : Int)

theorem zeroExtend_extractLsb_eq_ofNat (w : Nat) (hw0 : 0 < w) (hw128 : w ≤ 128)
    (data : BitVec 128) :
    BitVec.zeroExtend 128 (BitVec.extractLsb (w - 1) 0 data) =
      BitVec.ofNat 128 (data.toNat % 2 ^ w) := by
  apply BitVec.eq_of_toNat_eq
  unfold BitVec.zeroExtend BitVec.extractLsb BitVec.extractLsb'
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hlen : w - 1 + 1 = w := by omega
  simp only [Nat.sub_zero, Nat.shiftRight_zero, hlen]

theorem signExtend_extractLsb_toInt_eq (sz : Nat) (hsz : ValidScalarBytes sz)
    (data : BitVec 128) :
    (BitVec.signExtend 128 (BitVec.extractLsb (8 * sz - 1) 0 data)).toInt =
      decodeBitsInt true sz (data.toNat % 2 ^ (8 * sz)) := by
  have ⟨hw128, hw0⟩ := validScalarBytes_bits_le_128 hsz
  have hlen : 8 * sz - 1 - 0 + 1 ≤ 128 := by omega
  rw [BitVec.toInt_signExtend_of_le hlen]
  unfold BitVec.toInt decodeBitsInt BitVec.extractLsb BitVec.extractLsb'
  rw [BitVec.toNat_ofNat]
  have hlen_eq : 8 * sz - 1 + 1 = 8 * sz := by omega
  have hsplit : 2 ^ (8 * sz) = 2 * 2 ^ (8 * sz - 1) := by
    rcases hsz with rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [Nat.sub_zero, Nat.shiftRight_zero, hlen_eq, ↓reduceIte]
  generalize data.toNat % 2 ^ (8 * sz) = r
  by_cases hr : r < 2 ^ (8 * sz - 1)
  · have hr2 : 2 * r < 2 ^ (8 * sz) := by omega
    simp [hr, hr2]
  · have hr2 : ¬(2 * r < 2 ^ (8 * sz)) := by omega
    simp [hr, hr2]

theorem size_truncate_translateSizeBytes {sz : Nat} (hsz : ValidScalarBytes sz)
    (data : BitVec 128) :
    (translateSizeBytes sz).truncate data =
      .ok (BitVec.ofNat 128 (data.toNat % 2 ^ (8 * sz))) := by
  have ⟨hw128, hw0⟩ := validScalarBytes_bits_le_128 hsz
  have hze := zeroExtend_extractLsb_eq_ofNat (8 * sz) hw0 hw128 data
  rcases hsz with rfl | rfl | rfl | rfl | rfl <;>
    exact congrArg Except.ok hze

theorem size_signExtend_translateSizeBytes {sz : Nat} (hsz : ValidScalarBytes sz)
    (data : BitVec 128) :
    (translateSizeBytes sz).signExtend data =
      .ok (decodeBitsInt true sz (data.toNat % 2 ^ (8 * sz))) := by
  have hse := signExtend_extractLsb_toInt_eq sz hsz data
  rcases hsz with rfl | rfl | rfl | rfl | rfl <;>
    exact congrArg Except.ok hse

theorem truncateFromUInt_translateSizeBytes_raw {sz : Nat} (hsz : ValidScalarBytes sz)
    (data : BitVec 128) :
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.truncateFromUInt data (translateSizeBytes sz) =
        .ok (msc, BitVec.zeroExtend 128 (BitVec.extractLsb (8 * sz - 1) 0 data) != data) ∧
      ScalarRel ⟨data.toNat % 2 ^ (8 * sz), sz⟩ msc := by
  have ⟨hw128, hw0⟩ := validScalarBytes_bits_le_128 hsz
  have hze := zeroExtend_extractLsb_eq_ofNat (8 * sz) hw0 hw128 data
  have hmod : data.toNat % 2 ^ (8 * sz) < scalarModulus sz := by
    rw [scalarModulus_eq_two_pow]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  rcases hsz with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, rfl, ⟨by simp [ValidScalarBytes], hmod, rfl, hze⟩⟩

theorem truncateFromUInt_translateSizeBytes_spec {sz : Nat} (hsz : ValidScalarBytes sz)
    (data : BitVec 128) :
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.truncateFromUInt data (translateSizeBytes sz) =
        .ok (msc, BitVec.ofNat 128 (data.toNat % 2 ^ (8 * sz)) != data) ∧
      ScalarRel ⟨data.toNat % 2 ^ (8 * sz), sz⟩ msc := by
  have ⟨hw128, hw0⟩ := validScalarBytes_bits_le_128 hsz
  have hze := zeroExtend_extractLsb_eq_ofNat (8 * sz) hw0 hw128 data
  obtain ⟨msc, hmsc, hrel⟩ := truncateFromUInt_translateSizeBytes_raw hsz data
  rw [hze] at hmsc
  exact ⟨msc, hmsc, hrel⟩

theorem integerOps_decode_eq {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (kind : Miri.MIR.IntegerKind) :
    Miri.Interpreter.IntegerOps.decode ⟨msc, ⟨translateSizeBytes sc.sizeBytes, kind⟩⟩ =
      .ok (decodeBitsInt kind.signed sc.sizeBytes sc.bits) := by
  unfold Miri.Interpreter.IntegerOps.decode Miri.Interpreter.IntegerType.signed
  have htoNat := bitVec_ofNat_toNat_of_valid hrel.validBytes hrel.canonical
  have hlt : sc.bits < 2 ^ (8 * sc.sizeBytes) := by
    rw [← scalarModulus_eq_two_pow]; exact hrel.canonical
  cases hs : kind.signed
  · simp only [Bool.false_eq_true, ↓reduceIte, hrel.toUInt_eq, Except.mapError, bind, Except.bind,
      pure, Except.pure, htoNat, decodeBitsInt]
    rfl
  · simp only [↓reduceIte, Miri.Memory.ScalarInt.toInt, hrel.toBits_eq,
      size_signExtend_translateSizeBytes hrel.validBytes, htoNat, Nat.mod_eq_of_lt hlt,
      Except.mapError, bind, Except.bind]

/-- Whether a mathematical integer `val` is representable in width `8 * sz` with signedness `signed`. -/
def canRepresentInt (signed : Bool) (sz : Nat) (val : Int) : Bool :=
  if signed then
    decide (-(2 : Int) ^ (8 * sz - 1) ≤ val ∧ val < (2 : Int) ^ (8 * sz - 1))
  else
    decide (0 ≤ val ∧ val < (2 : Int) ^ (8 * sz))

theorem bitVec_ofInt_toNat_mod_valid {sz : Nat} (hsz : ValidScalarBytes sz) (val : Int) :
    (BitVec.ofInt 128 val).toNat % 2 ^ (8 * sz) =
      (val % (2 : Int) ^ (8 * sz)).toNat := by
  rw [BitVec.toNat_ofInt]
  have ⟨hw128, _⟩ := validScalarBytes_bits_le_128 hsz
  have hpos : (0 : Int) < (2 : Int) ^ (8 * sz) := Int.pow_pos (by decide)
  have hnonneg128 : 0 ≤ val % (2 ^ 128 : Nat) :=
    Int.emod_nonneg val (by decide)
  have hnonneg : 0 ≤ val % (2 : Int) ^ (8 * sz) :=
    Int.emod_nonneg val (Int.ne_of_gt hpos)
  have hdvd : ((2 : Int) ^ (8 * sz)) ∣ ((2 ^ 128 : Nat) : Int) := by
    have hdvdNat : (2 : Nat) ^ (8 * sz) ∣ 2 ^ 128 := Nat.pow_dvd_pow 2 hw128
    have hp : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
    rw [hp]
    exact_mod_cast hdvdNat
  apply Int.ofNat.inj
  change (((val % (2 ^ 128 : Nat)).toNat % 2 ^ (8 * sz) : Nat) : Int) =
    ((val % (2 : Int) ^ (8 * sz)).toNat : Int)
  rw [Int.natCast_emod, Int.toNat_of_nonneg hnonneg128, Int.toNat_of_nonneg hnonneg]
  have hp : ((2 ^ (8 * sz) : Nat) : Int) = (2 : Int) ^ (8 * sz) := by push_cast; rfl
  rw [hp, Int.emod_emod_of_dvd val hdvd]

theorem bitVec_toInt_in_i128 (bv : BitVec 128) :
    (bv.toInt < -(2 ^ 127 : Int) || bv.toInt ≥ (2 ^ 127 : Int)) = false := by
  have hlt := bv.isLt
  unfold BitVec.toInt
  rw [Bool.or_eq_false_iff]
  split <;> simp <;> omega

theorem truncateFromInt_ofInt_translateSizeBytes_spec {sz : Nat} (hsz : ValidScalarBytes sz)
    (val : Int) :
    let wrapped := (BitVec.ofInt 128 val).toInt
    let r := (val % (2 : Int) ^ (8 * sz)).toNat
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.truncateFromInt wrapped (translateSizeBytes sz) =
        .ok (msc, decodeBitsInt true sz r != wrapped) ∧
      ScalarRel ⟨r, sz⟩ msc := by
  dsimp only
  have hbounds := bitVec_toInt_in_i128 (BitVec.ofInt 128 val)
  have hofInt : BitVec.ofInt 128 (BitVec.ofInt 128 val).toInt = BitVec.ofInt 128 val :=
    BitVec.ofInt_toInt
  have ⟨hw128, hw0⟩ := validScalarBytes_bits_le_128 hsz
  have hmod_eq := bitVec_ofInt_toNat_mod_valid hsz val
  have hze := zeroExtend_extractLsb_eq_ofNat (8 * sz) hw0 hw128 (BitVec.ofInt 128 val)
  rw [hmod_eq] at hze
  have hlt : (val % (2 : Int) ^ (8 * sz)).toNat < scalarModulus sz := by
    rw [scalarModulus_eq_two_pow]
    rw [← hmod_eq]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have htoNat : (BitVec.ofNat 128 (val % (2 : Int) ^ (8 * sz)).toNat).toNat =
      (val % (2 : Int) ^ (8 * sz)).toNat :=
    bitVec_ofNat_toNat_of_valid hsz hlt
  have hrhs : decodeBitsInt true sz
      ((BitVec.zeroExtend 128 (BitVec.extractLsb (8 * sz - 1) 0 (BitVec.ofInt 128 val))).toNat %
        2 ^ (8 * sz)) =
      decodeBitsInt true sz (val % (2 : Int) ^ (8 * sz)).toNat := by
    rw [hze, htoNat, Nat.mod_eq_of_lt (by rw [← scalarModulus_eq_two_pow]; exact hlt)]
  have hse := (signExtend_extractLsb_toInt_eq sz hsz
    (BitVec.zeroExtend 128 (BitVec.extractLsb (8 * sz - 1) 0 (BitVec.ofInt 128 val)))).trans hrhs
  unfold Miri.Memory.ScalarInt.truncateFromInt
  rw [hbounds, hofInt]
  rcases hsz with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, congrArg (fun d => Except.ok (_, d != (BitVec.ofInt 128 val).toInt)) hse,
      ⟨by simp [ValidScalarBytes], hlt, rfl, hze⟩⟩

theorem truncateFromUInt_ofInt_translateSizeBytes_spec {sz : Nat} (hsz : ValidScalarBytes sz)
    (val : Int) :
    let r := (val % (2 : Int) ^ (8 * sz)).toNat
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofInt 128 val) (translateSizeBytes sz) =
        .ok (msc, BitVec.ofNat 128 r != BitVec.ofInt 128 val) ∧
      ScalarRel ⟨r, sz⟩ msc := by
  dsimp only
  obtain ⟨msc, hmsc, hrel⟩ := truncateFromUInt_translateSizeBytes_spec hsz (BitVec.ofInt 128 val)
  rw [bitVec_ofInt_toNat_mod_valid hsz val] at hmsc hrel
  exact ⟨msc, hmsc, hrel⟩

theorem eq_of_emod_eq_of_window {x y lo m : Int} (hm : 0 < m)
    (hx₁ : lo ≤ x) (hx₂ : x < lo + m) (hy₁ : lo ≤ y) (hy₂ : y < lo + m)
    (h : x % m = y % m) : x = y := by
  have hd : m ∣ x - y := by
    rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, h, Int.sub_self, Int.zero_emod]
  have habs : (x - y).natAbs < m.natAbs := by omega
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd habs
  omega

theorem decodeBitsInt_signed_window {sz : Nat} (hsz : ValidScalarBytes sz)
    {r : Nat} (hr : r < 2 ^ (8 * sz)) :
    -(2 : Int) ^ (8 * sz - 1) ≤ decodeBitsInt true sz r ∧
      decodeBitsInt true sz r < (2 : Int) ^ (8 * sz - 1) ∧
      decodeBitsInt true sz r % (2 : Int) ^ (8 * sz) = (r : Int) := by
  have hsplit : (2 : Int) ^ (8 * sz) = 2 * (2 : Int) ^ (8 * sz - 1) := by
    rcases hsz with rfl | rfl | rfl | rfl | rfl <;> decide
  have hr' : (r : Int) < (2 : Int) ^ (8 * sz) := by exact_mod_cast hr
  have hp : ((2 ^ (8 * sz) : Nat) : Int) = (2 : Int) ^ (8 * sz) := by push_cast; rfl
  unfold decodeBitsInt
  simp only [↓reduceIte, hp]
  by_cases hlt : r < 2 ^ (8 * sz - 1)
  · have hlt' : (r : Int) < (2 : Int) ^ (8 * sz - 1) := by exact_mod_cast hlt
    simp only [hlt, ↓reduceIte]
    refine ⟨by omega, hlt', Int.emod_eq_of_lt (by omega) hr'⟩
  · have hge' : (2 : Int) ^ (8 * sz - 1) ≤ (r : Int) := by
      have := Nat.le_of_not_lt hlt
      exact_mod_cast this
    simp only [hlt, ↓reduceIte]
    refine ⟨by omega, by omega, ?_⟩
    rw [Int.sub_emod, Int.emod_self, Int.sub_zero, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
    exact Int.emod_eq_of_lt (by omega) hr'

theorem bitVec_toInt_ofInt_eq_of_in_i128 {val : Int}
    (hlo : -(2 ^ 127 : Int) ≤ val) (hhi : val < (2 ^ 127 : Int)) :
    (BitVec.ofInt 128 val).toInt = val := by
  unfold BitVec.toInt
  rw [BitVec.toNat_ofInt]
  by_cases hv0 : 0 ≤ val
  · have hmod : val % (2 ^ 128 : Nat) = val :=
      Int.emod_eq_of_lt hv0 (by omega)
    rw [hmod]
    have h2 : 2 * val.toNat < 2 ^ 128 := by omega
    simp [h2, Int.toNat_of_nonneg hv0]
  · have hmod : val % (2 ^ 128 : Nat) = val + (2 ^ 128 : Nat) := by
      rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hmod]
    have h2 : ¬(2 * (val + (2 ^ 128 : Nat)).toNat < 2 ^ 128) := by omega
    simp only [h2, ↓reduceIte]
    omega

theorem unsigned_truncate_overflow_eq {sz : Nat} (hsz : ValidScalarBytes sz) (val : Int) :
    ((val < 0 || val ≥ (2 ^ 128 : Int)) ||
      (BitVec.ofNat 128 (val % (2 : Int) ^ (8 * sz)).toNat != BitVec.ofInt 128 val)) =
      !canRepresentInt false sz val := by
  have ⟨hw128, _⟩ := validScalarBytes_bits_le_128 hsz
  have hpow : (2 : Int) ^ (8 * sz) ≤ (2 ^ 128 : Int) := by
    rcases hsz with rfl | rfl | rfl | rfl | rfl <;> decide
  have hpos : (0 : Int) < (2 : Int) ^ (8 * sz) := Int.pow_pos (by decide)
  have hlt_r : (val % (2 : Int) ^ (8 * sz)).toNat < scalarModulus sz := by
    rw [scalarModulus_eq_two_pow, ← bitVec_ofInt_toNat_mod_valid hsz val]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have htoNat_r := bitVec_ofNat_toNat_of_valid hsz hlt_r
  unfold canRepresentInt
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hhost : val < 0 ∨ val ≥ (2 ^ 128 : Int)
  · have hhostB : (val < 0 || val ≥ (2 ^ 128 : Int)) = true := by
      rw [Bool.or_eq_true]; simp only [decide_eq_true_eq]; exact hhost
    have hrep : decide (0 ≤ val ∧ val < (2 : Int) ^ (8 * sz)) = false :=
      decide_eq_false (by omega)
    rw [hhostB, hrep]; rfl
  · have hhostB : (val < 0 || val ≥ (2 ^ 128 : Int)) = false := by
      rw [Bool.or_eq_false_iff]; simp only [decide_eq_false_iff_not]; omega
    have hv0 : 0 ≤ val := by omega
    have hv128 : val < (2 ^ 128 : Int) := by omega
    rw [hhostB, Bool.false_or]
    have htoNat_val : (BitVec.ofInt 128 val).toNat = val.toNat := by
      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt hv0 (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, Ne, Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · intro hne ⟨_, hlt⟩
      apply hne
      apply BitVec.eq_of_toNat_eq
      rw [htoNat_r, htoNat_val, Int.emod_eq_of_lt hv0 hlt]
    · intro hnot heq
      have htoNat_eq := congrArg BitVec.toNat heq
      rw [htoNat_r, htoNat_val] at htoNat_eq
      apply hnot
      refine ⟨hv0, ?_⟩
      have hr_lt : (val % (2 : Int) ^ (8 * sz)).toNat < 2 ^ (8 * sz) := by
        rw [← scalarModulus_eq_two_pow]; exact hlt_r
      rw [htoNat_eq] at hr_lt
      have hp : ((2 ^ (8 * sz) : Nat) : Int) = (2 : Int) ^ (8 * sz) := by push_cast; rfl
      rw [← hp]
      have : (val.toNat : Int) < ((2 ^ (8 * sz) : Nat) : Int) := by exact_mod_cast hr_lt
      rwa [Int.toNat_of_nonneg hv0] at this

theorem signed_truncate_overflow_eq {sz : Nat} (hsz : ValidScalarBytes sz) (val : Int) :
    ((val < -(2 ^ 127 : Int) || val ≥ (2 ^ 127 : Int)) ||
      (decodeBitsInt true sz (val % (2 : Int) ^ (8 * sz)).toNat != (BitVec.ofInt 128 val).toInt)) =
      !canRepresentInt true sz val := by
  have hpow : (2 : Int) ^ (8 * sz - 1) ≤ (2 ^ 127 : Int) := by
    rcases hsz with rfl | rfl | rfl | rfl | rfl <;> decide
  have hsplit : (2 : Int) ^ (8 * sz) = 2 * (2 : Int) ^ (8 * sz - 1) := by
    rcases hsz with rfl | rfl | rfl | rfl | rfl <;> decide
  have hpos : (0 : Int) < (2 : Int) ^ (8 * sz) := Int.pow_pos (by decide)
  have hnonneg : 0 ≤ val % (2 : Int) ^ (8 * sz) := Int.emod_nonneg val (Int.ne_of_gt hpos)
  have hr_lt : (val % (2 : Int) ^ (8 * sz)).toNat < 2 ^ (8 * sz) := by
    rw [← bitVec_ofInt_toNat_mod_valid hsz val]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨hd_lo, hd_hi, hd_mod⟩ := decodeBitsInt_signed_window hsz hr_lt
  rw [Int.toNat_of_nonneg hnonneg] at hd_mod
  unfold canRepresentInt
  simp only [↓reduceIte]
  by_cases hhost : val < -(2 ^ 127 : Int) ∨ val ≥ (2 ^ 127 : Int)
  · have hhostB : (val < -(2 ^ 127 : Int) || val ≥ (2 ^ 127 : Int)) = true := by
      rw [Bool.or_eq_true]; simp only [decide_eq_true_eq]; exact hhost
    have hrep : decide (-(2 : Int) ^ (8 * sz - 1) ≤ val ∧ val < (2 : Int) ^ (8 * sz - 1)) = false :=
      decide_eq_false (by omega)
    rw [hhostB, hrep]; rfl
  · have hhostB : (val < -(2 ^ 127 : Int) || val ≥ (2 ^ 127 : Int)) = false := by
      rw [Bool.or_eq_false_iff]; simp only [decide_eq_false_iff_not]; omega
    have hlo127 : -(2 ^ 127 : Int) ≤ val := by omega
    have hhi127 : val < (2 ^ 127 : Int) := by omega
    rw [hhostB, Bool.false_or, bitVec_toInt_ofInt_eq_of_in_i128 hlo127 hhi127]
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, Ne, Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · intro hne ⟨hlo, hhi⟩
      apply hne
      exact eq_of_emod_eq_of_window hpos hd_lo (by omega) hlo (by omega) hd_mod
    · intro hnot heq
      apply hnot
      rw [← heq]
      exact ⟨hd_lo, hd_hi⟩

/-- Public mirror of `Miri.Interpreter.IntegerOps.truncate` (which is `private` in `IntegerOps.lean`). -/
def truncateInt (value : Int) (type : Miri.Interpreter.IntegerType) :
    Except Miri.Interpreter.IntegerOpError (Miri.Memory.ScalarInt × Bool) :=
  if type.signed then
    let wrapped := (BitVec.ofInt 128 value).toInt
    (Miri.Memory.ScalarInt.truncateFromInt wrapped type.size).mapError .scalar
  else
    (Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofInt 128 value) type.size).mapError .scalar

/-- Public mirror of `Miri.Interpreter.IntegerOps.scalarResult` (which is `private` in `IntegerOps.lean`). -/
def scalarResultInt (op : Miri.MIR.BinOp) (value : Miri.Memory.ScalarInt) (overflow : Bool) :
    Except Miri.Interpreter.IntegerOpError Miri.Interpreter.IntegerResult := do
  if overflow && op.isUnchecked then throw (.undefinedBehavior (.arithmeticOverflow op))
  return if op.isOverflowing then .withOverflow value overflow else .scalar value

/-- Public mirror of `Miri.Interpreter.IntegerOps.arithmetic` (which is `private` in `IntegerOps.lean`). -/
def arithmeticInt (op : Miri.MIR.BinOp) (l r : Int) (type : Miri.Interpreter.IntegerType) :
    Except Miri.Interpreter.IntegerOpError Miri.Interpreter.IntegerResult := do
  if r == 0 then
    if op == .Div then throw (.undefinedBehavior .divisionByZero)
    if op == .Rem then throw (.undefinedBehavior .remainderByZero)
  if type.signed && (op == .Div || op == .Rem) then
    let min ← type.size.signedIntMin |>.mapError
      (Miri.Interpreter.IntegerOpError.scalar ∘ Miri.Memory.ScalarIntError.sizeError)
    if l == min && r == -1 then
      throw (.undefinedBehavior (if op == .Div then .divisionOverflow else .remainderOverflow))
  let result ← match op with
    | .Add | .AddUnchecked | .AddWithOverflow => pure (l + r)
    | .Sub | .SubUnchecked | .SubWithOverflow => pure (l - r)
    | .Mul | .MulUnchecked | .MulWithOverflow => pure (l * r)
    | .Div => pure (Int.tdiv l r)
    | .Rem => pure (Int.tmod l r)
    | _ => throw (.invalidBinaryOperator op)
  let hostOverflow := if type.signed then
      result < -(2 ^ 127 : Int) || result ≥ (2 ^ 127 : Int)
    else result < 0 || result ≥ (2 ^ 128 : Int)
  let (value, lossy) ← truncateInt result type
  scalarResultInt op value (hostOverflow || lossy)

/-- Public mirror of `Miri.Interpreter.IntegerOps.shift` (which is `private` in `IntegerOps.lean`). -/
def shiftInt (op : Miri.MIR.BinOp) (left right : Miri.Interpreter.IntegerValue) (l r : Int) :
    Except Miri.Interpreter.IntegerOpError Miri.Interpreter.IntegerResult := do
  let bits ← left.type.size.bits |>.mapError
    (Miri.Interpreter.IntegerOpError.scalar ∘ Miri.Memory.ScalarIntError.sizeError)
  let amount := r % Int.ofNat bits.toNat
  let overflow := amount != r
  let result := match op with
    | .Shl | .ShlUnchecked => l <<< amount.toNat
    | _ => l >>> amount.toNat
  let (value, _) ← truncateInt result left.type
  if overflow && op.isUnchecked then
    throw (.undefinedBehavior (.shiftOverflow op r right.type.signed))
  return .scalar value

/-- Unfold `Miri.Interpreter.IntegerOps.unary` through its private `truncate` helper. -/
theorem integerOps_unary_eq {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (kind : Miri.MIR.IntegerKind) (op : Miri.MIR.UnOp) :
    Miri.Interpreter.IntegerOps.unary op ⟨msc, ⟨translateSizeBytes sc.sizeBytes, kind⟩⟩ =
      (do
        let integer ← Except.ok (decodeBitsInt kind.signed sc.sizeBytes sc.bits)
        let result ← match op with
          | .Not => pure (~~~integer)
          | .Neg =>
              if kind.signed then pure (-integer)
              else throw (Miri.Interpreter.IntegerOpError.invalidUnaryOperator op kind.signed)
          | .PtrMetadata =>
              throw (Miri.Interpreter.IntegerOpError.invalidUnaryOperator op kind.signed)
        return (← truncateInt result ⟨translateSizeBytes sc.sizeBytes, kind⟩).1) := by
  unfold Miri.Interpreter.IntegerOps.unary
  rw [integerOps_decode_eq hrel kind]
  rfl

/-- Unfold `Miri.Interpreter.IntegerOps.binary` through its private `shift` and `arithmetic` helpers. -/
theorem integerOps_binary_eq
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (kind₁ kind₂ : Miri.MIR.IntegerKind) (op : Miri.MIR.BinOp) :
    let left : Miri.Interpreter.IntegerValue := ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind₁⟩⟩
    let right : Miri.Interpreter.IntegerValue := ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind₂⟩⟩
    Miri.Interpreter.IntegerOps.binary op left right =
      (do
        let l ← Except.ok (decodeBitsInt kind₁.signed sc₁.sizeBytes sc₁.bits)
        let r ← Except.ok (decodeBitsInt kind₂.signed sc₂.sizeBytes sc₂.bits)
        if op == .Shl || op == .ShlUnchecked || op == .Shr || op == .ShrUnchecked then
          return ← shiftInt op left right l r
        if left.type != right.type then throw (.asymmetricTypes left.type right.type)
        match op with
        | .Eq => return .boolean (l == r)
        | .Ne => return .boolean (l != r)
        | .Lt => return .boolean (l < r)
        | .Le => return .boolean (l ≤ r)
        | .Gt => return .boolean (l > r)
        | .Ge => return .boolean (l ≥ r)
        | .Cmp => return .ordering (compare l r)
        | .BitAnd | .BitOr | .BitXor =>
            let lb ← left.scalar.toUInt left.type.size |>.mapError .scalar
            let rb ← right.scalar.toUInt right.type.size |>.mapError .scalar
            let bits := match op with
              | .BitAnd => lb &&& rb
              | .BitOr => lb ||| rb
              | _ => lb ^^^ rb
            let (value, _) ← Miri.Memory.ScalarInt.truncateFromUInt bits left.type.size |>.mapError .scalar
            return .scalar value
        | _ => arithmeticInt op l r left.type) := by
  dsimp only
  unfold Miri.Interpreter.IntegerOps.binary
  rw [integerOps_decode_eq hrel₁ kind₁, integerOps_decode_eq hrel₂ kind₂]
  rfl

theorem truncateInt_spec {sz : Nat} (hsz : ValidScalarBytes sz)
    (kind : Miri.MIR.IntegerKind) (val : Int) :
    let hostOverflow := if kind.signed then
        val < -(2 ^ 127 : Int) || val ≥ (2 ^ 127 : Int)
      else val < 0 || val ≥ (2 ^ 128 : Int)
    ∃ msc : Miri.Memory.ScalarInt, ∃ lossy : Bool,
      truncateInt val ⟨translateSizeBytes sz, kind⟩ = .ok (msc, lossy) ∧
      ScalarRel ⟨(val % (2 : Int) ^ (8 * sz)).toNat, sz⟩ msc ∧
      (hostOverflow || lossy) = !canRepresentInt kind.signed sz val := by
  dsimp only
  unfold truncateInt Miri.Interpreter.IntegerType.signed
  dsimp only
  cases hs : kind.signed
  · obtain ⟨msc, hmsc, hrel⟩ := truncateFromUInt_ofInt_translateSizeBytes_spec hsz val
    refine ⟨msc, BitVec.ofNat 128 (val % (2 : Int) ^ (8 * sz)).toNat != BitVec.ofInt 128 val,
      ?_, hrel, ?_⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, hmsc, Except.mapError]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact unsigned_truncate_overflow_eq hsz val
  · obtain ⟨msc, hmsc, hrel⟩ := truncateFromInt_ofInt_translateSizeBytes_spec hsz val
    refine ⟨msc, decodeBitsInt true sz (val % (2 : Int) ^ (8 * sz)).toNat != (BitVec.ofInt 128 val).toInt,
      ?_, hrel, ?_⟩
    · simp only [↓reduceIte, hmsc, Except.mapError]
    · simp only [↓reduceIte]
      exact signed_truncate_overflow_eq hsz val

theorem int_shiftLeft_eq_mul_pow (l : Int) (k : Nat) :
    l <<< k = l * (2 : Int) ^ k := by
  cases l with
  | ofNat n =>
    change (Int.ofNat (n <<< k)) = (n : Int) * (2 : Int) ^ k
    rw [Nat.shiftLeft_eq]
    push_cast
    rfl
  | negSucc n =>
    change Int.negSucc (((n + 1) <<< k) - 1) = Int.negSucc n * (2 : Int) ^ k
    rw [Nat.shiftLeft_eq]
    have hpos : 0 < (n + 1) * 2 ^ k := Nat.mul_pos (by omega) (Nat.two_pow_pos k)
    rw [Int.negSucc_eq, Int.negSucc_eq, Int.neg_mul]
    have hcast : (((n + 1) * 2 ^ k - 1 : Nat) : Int) + 1 =
        ((n : Int) + 1) * (2 : Int) ^ k := by
      have h1 : (((n + 1) * 2 ^ k : Nat) : Int) = ((n : Int) + 1) * (2 : Int) ^ k := by
        push_cast; rfl
      omega
    omega

theorem int_shiftRight_eq_ediv_pow (l : Int) (k : Nat) :
    l >>> k = l / (2 : Int) ^ k := by
  cases l with
  | ofNat n =>
    change Int.ofNat (n >>> k) = (n : Int) / (2 : Int) ^ k
    rw [Nat.shiftRight_eq_div_pow]
    have hp : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) := by push_cast; rfl
    rw [hp]
    rfl
  | negSucc n =>
    change Int.negSucc (n >>> k) = Int.negSucc n / (2 : Int) ^ k
    rw [Nat.shiftRight_eq_div_pow]
    have hp : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) := by push_cast; rfl
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    rw [hp]
    have hdiv := Nat.div_add_mod n (2 ^ k)
    have hmod := Nat.mod_lt n hpos
    rw [Int.negSucc_eq, Int.negSucc_eq]
    have hrew : -((n : Int) + 1) =
        ((2 ^ k - 1 - (n % 2 ^ k) : Nat) : Int) +
          (-((n / 2 ^ k + 1 : Nat) : Int)) * ((2 ^ k : Nat) : Int) := by
      rw [Int.neg_mul]
      have hmul : (((n / 2 ^ k + 1) * 2 ^ k : Nat) : Int) =
          ((n / 2 ^ k + 1 : Nat) : Int) * ((2 ^ k : Nat) : Int) := by push_cast; rfl
      have hnat : (n + 1) + (2 ^ k - 1 - n % 2 ^ k) = (n / 2 ^ k + 1) * 2 ^ k := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / 2 ^ k)]
        omega
      omega
    rw [hrew, Int.add_mul_ediv_right _ _ (by omega)]
    have hed : ((2 ^ k - 1 - n % 2 ^ k : Nat) : Int) / ((2 ^ k : Nat) : Int) = 0 :=
      Int.ediv_eq_zero_of_lt (by omega) (by omega)
    omega

theorem nat_beq_eq_decide (a b : Nat) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.beq_eq])

theorem nat_ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.ble_eq])

theorem nat_div_eq_div (a b : Nat) : Nat.div a b = a / b := rfl

theorem nat_mod_eq_mod (a b : Nat) : Nat.mod a b = a % b := rfl

theorem nat_land_step (x y : Nat) :
    (x &&& y) =
      (match Bool.and (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1) with | true => 1 | false => 0) +
        2 * ((x / 2) &&& (y / 2)) := by
  change Nat.bitwise and x y =
    (match Bool.and (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1) with | true => 1 | false => 0) +
      2 * Nat.bitwise and (x / 2) (y / 2)
  rw [Nat.bitwise]
  by_cases hx : x = 0
  · subst hx
    simp [Nat.bitwise, nat_beq_eq_decide]
  · by_cases hy : y = 0
    · subst hy
      have h0 : Nat.bitwise and (x / 2) 0 = 0 := by rw [Nat.bitwise]; split <;> rfl
      simp [hx, h0, nat_beq_eq_decide]
    · simp only [hx, hy, ↓reduceIte, nat_beq_eq_decide]
      rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hx2 | hx2 <;>
        rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hy2 | hy2 <;>
        simp [hx2, hy2] <;> omega

theorem nat_lor_step (x y : Nat) :
    (x ||| y) =
      (match Bool.or (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1) with | true => 1 | false => 0) +
        2 * ((x / 2) ||| (y / 2)) := by
  change Nat.bitwise or x y =
    (match Bool.or (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1) with | true => 1 | false => 0) +
      2 * Nat.bitwise or (x / 2) (y / 2)
  rw [Nat.bitwise]
  by_cases hx : x = 0
  · subst hx
    have h0 : Nat.bitwise or 0 (y / 2) = y / 2 := by rw [Nat.bitwise]; rfl
    simp only [↓reduceIte, h0, Nat.zero_mod, nat_beq_eq_decide]
    rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hy2 | hy2 <;> simp [hy2] <;> omega
  · by_cases hy : y = 0
    · subst hy
      have h0 : Nat.bitwise or (x / 2) 0 = x / 2 := by
        rw [Nat.bitwise]
        split
        · next h => exact h.symm
        · rfl
      simp only [hx, ↓reduceIte, h0, Nat.zero_mod, nat_beq_eq_decide]
      rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hx2 | hx2 <;> simp [hx2] <;> omega
    · simp only [hx, hy, ↓reduceIte, nat_beq_eq_decide]
      rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hx2 | hx2 <;>
        rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hy2 | hy2 <;>
        simp [hx2, hy2] <;> omega

theorem nat_xor_step (x y : Nat) :
    (x ^^^ y) =
      (match Nat.beq (x % 2) (y % 2) with | true => 0 | false => 1) +
        2 * ((x / 2) ^^^ (y / 2)) := by
  change Nat.bitwise bne x y =
    (match Nat.beq (x % 2) (y % 2) with | true => 0 | false => 1) +
      2 * Nat.bitwise bne (x / 2) (y / 2)
  rw [Nat.bitwise]
  by_cases hx : x = 0
  · subst hx
    have h0 : Nat.bitwise bne 0 (y / 2) = y / 2 := by rw [Nat.bitwise]; rfl
    simp only [↓reduceIte, h0, Nat.zero_mod, nat_beq_eq_decide]
    rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hy2 | hy2 <;> simp [hy2] <;> omega
  · by_cases hy : y = 0
    · subst hy
      have h0 : Nat.bitwise bne (x / 2) 0 = x / 2 := by
        rw [Nat.bitwise]
        split
        · next h => exact h.symm
        · rfl
      simp only [hx, ↓reduceIte, h0, Nat.zero_mod, nat_beq_eq_decide]
      rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hx2 | hx2 <;> simp [hx2] <;> omega
    · simp only [hx, hy, ↓reduceIte, nat_beq_eq_decide]
      rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hx2 | hx2 <;>
        rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hy2 | hy2 <;>
        simp [hx2, hy2] <;> omega

theorem bitwiseAndBits_eq_land (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    bitwiseAndBits k x y = (x &&& y) ∧ (x &&& y) < 2 ^ k := by
  induction k generalizing x y with
  | zero =>
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    subst hx0 hy0
    exact ⟨rfl, by decide⟩
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    obtain ⟨ih_eq, ih_lt⟩ := ih (x / 2) (y / 2) (by omega) (by omega)
    have hstep := nat_land_step x y
    unfold bitwiseAndBits
    change (match Bool.and (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1) with | true => 1 | false => 0) +
        2 * bitwiseAndBits k (x / 2) (y / 2) = (x &&& y) ∧ (x &&& y) < 2 ^ (k + 1)
    rw [ih_eq, ← hstep]
    refine ⟨rfl, ?_⟩
    rw [hstep, hpow]
    rcases (Bool.and (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1)) <;> dsimp only <;> omega

theorem bitwiseOrBits_eq_lor (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    bitwiseOrBits k x y = (x ||| y) ∧ (x ||| y) < 2 ^ k := by
  induction k generalizing x y with
  | zero =>
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    subst hx0 hy0
    exact ⟨rfl, by decide⟩
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    obtain ⟨ih_eq, ih_lt⟩ := ih (x / 2) (y / 2) (by omega) (by omega)
    have hstep := nat_lor_step x y
    unfold bitwiseOrBits
    change (match Bool.or (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1) with | true => 1 | false => 0) +
        2 * bitwiseOrBits k (x / 2) (y / 2) = (x ||| y) ∧ (x ||| y) < 2 ^ (k + 1)
    rw [ih_eq, ← hstep]
    refine ⟨rfl, ?_⟩
    rw [hstep, hpow]
    rcases (Bool.or (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1)) <;> dsimp only <;> omega

theorem bitwiseXorBits_eq_xor (k x y : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    bitwiseXorBits k x y = (x ^^^ y) ∧ (x ^^^ y) < 2 ^ k := by
  induction k generalizing x y with
  | zero =>
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    subst hx0 hy0
    exact ⟨rfl, by decide⟩
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    obtain ⟨ih_eq, ih_lt⟩ := ih (x / 2) (y / 2) (by omega) (by omega)
    have hstep := nat_xor_step x y
    unfold bitwiseXorBits
    change (match Nat.beq (x % 2) (y % 2) with | true => 0 | false => 1) +
        2 * bitwiseXorBits k (x / 2) (y / 2) = (x ^^^ y) ∧ (x ^^^ y) < 2 ^ (k + 1)
    rw [ih_eq, ← hstep]
    refine ⟨rfl, ?_⟩
    rw [hstep, hpow]
    rcases (Nat.beq (x % 2) (y % 2)) <;> dsimp only <;> omega

/-! ## 2. Unary & Binary Scalar Operator Simulation Lemmas -/

theorem decodeBitsInt_emod {signed : Bool} {sz x : Nat}
    (hx : x < 2 ^ (8 * sz)) :
    decodeBitsInt signed sz x % (2 : Int) ^ (8 * sz) = (x : Int) := by
  have hx' : (x : Int) < (2 : Int) ^ (8 * sz) := by exact_mod_cast hx
  have hp : ((2 ^ (8 * sz) : Nat) : Int) = (2 : Int) ^ (8 * sz) := by push_cast; rfl
  unfold decodeBitsInt
  cases signed
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact Int.emod_eq_of_lt (by omega) hx'
  · simp only [↓reduceIte, hp]
    split
    · exact Int.emod_eq_of_lt (by omega) hx'
    · rw [Int.sub_emod, Int.emod_self, Int.sub_zero, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
      exact Int.emod_eq_of_lt (by omega) hx'

theorem decodeBitsInt_inj {signed : Bool} {sz x y : Nat}
    (_hsz : ValidScalarBytes sz) (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    decodeBitsInt signed sz x = decodeBitsInt signed sz y ↔ x = y := by
  constructor
  · intro heq
    have hmod := congrArg (· % (2 : Int) ^ (8 * sz)) heq
    rw [decodeBitsInt_emod hx, decodeBitsInt_emod hy] at hmod
    exact Int.ofNat.inj hmod
  · intro rfl; rfl

theorem decodeBitsInt_eq_zero_iff {signed : Bool} {sz x : Nat}
    (hsz : ValidScalarBytes sz) (hx : x < 2 ^ (8 * sz)) :
    decodeBitsInt signed sz x = 0 ↔ x = 0 := by
  have h0 : decodeBitsInt signed sz 0 = 0 := by
    unfold decodeBitsInt
    cases signed <;> simp [Nat.two_pow_pos _]
  rw [← h0]
  exact decodeBitsInt_inj hsz hx (Nat.two_pow_pos _)

theorem wrap_eq_toNat (v sz : Nat) :
    wrapScalarBits v (scalarModulus sz) = ((v : Int) % (2 : Int) ^ (8 * sz)).toNat := by
  rw [wrapScalarBits_eq_mod, scalarModulus_eq_two_pow]
  have : ((v : Int) % (2 : Int) ^ (8 * sz)) = ((v % 2 ^ (8 * sz) : Nat) : Int) := by
    rw [Int.natCast_emod]; push_cast; rfl
  rw [this, Int.toNat_natCast]

theorem int_complement_eq (v : Int) : ~~~v = -v - 1 := by
  cases v with
  | ofNat n =>
    change Int.negSucc n = -(n : Int) - 1
    rw [Int.negSucc_eq]
    omega
  | negSucc n =>
    change (n : Int) = -Int.negSucc n - 1
    rw [Int.negSucc_eq]
    omega

theorem neg_decodeBitsInt_emod (signed : Bool) (sz x : Nat) :
    (-decodeBitsInt signed sz x) % (2 : Int) ^ (8 * sz) =
      (-(x : Int)) % (2 : Int) ^ (8 * sz) := by
  have hp : ((2 ^ (8 * sz) : Nat) : Int) = (2 : Int) ^ (8 * sz) := by push_cast; rfl
  unfold decodeBitsInt
  cases signed
  · rfl
  · simp only [↓reduceIte, hp]
    split
    · rfl
    · have hrew : -((x : Int) - (2 : Int) ^ (8 * sz)) = -(x : Int) + (2 : Int) ^ (8 * sz) := by
        omega
      rw [hrew, Int.add_emod_right]

theorem wrap_neg_decodeBitsInt {sz x : Nat} (hx : x < 2 ^ (8 * sz)) :
    let m := scalarModulus sz
    wrapScalarBits (m - wrapScalarBits x m) m =
      ((-decodeBitsInt true sz x) % (2 : Int) ^ (8 * sz)).toNat := by
  dsimp only
  have hm := scalarModulus_eq_two_pow sz
  rw [neg_decodeBitsInt_emod]
  simp only [wrapScalarBits_eq_mod, hm, Nat.mod_eq_of_lt hx]
  by_cases hx0 : x = 0
  · subst hx0; simp
  · have hlt : 2 ^ (8 * sz) - x < 2 ^ (8 * sz) := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have hp : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
    rw [hp]
    have : (-(x : Int)) % ((2 ^ (8 * sz) : Nat) : Int) =
        (-(x : Int)) + ((2 ^ (8 * sz) : Nat) : Int) := by
      rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [this]
    omega

theorem wrap_not_decodeBitsInt {signed : Bool} {sz x : Nat} (hx : x < 2 ^ (8 * sz)) :
    let m := scalarModulus sz
    (m - 1) - wrapScalarBits x m =
      ((~~~decodeBitsInt signed sz x) % (2 : Int) ^ (8 * sz)).toNat := by
  dsimp only
  have hm := scalarModulus_eq_two_pow sz
  rw [int_complement_eq]
  have hmod : (-decodeBitsInt signed sz x - 1) % (2 : Int) ^ (8 * sz) =
      (-(x : Int) - 1) % (2 : Int) ^ (8 * sz) := by
    rw [Int.sub_emod, neg_decodeBitsInt_emod, ← Int.sub_emod]
  rw [hmod]
  simp only [wrapScalarBits_eq_mod, hm, Nat.mod_eq_of_lt hx]
  have hp : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  rw [hp]
  have : (-(x : Int) - 1) % ((2 ^ (8 * sz) : Nat) : Int) =
      (-(x : Int) - 1) + ((2 ^ (8 * sz) : Nat) : Int) := by
    rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [this]
  omega

/-- Theorem 4 (`LM-1.1`): Unary `Neg` and `Not` simulation between Anneal's
`MirSemantics` (`evalUnaryNot` and wrapping two's-complement negation) and
`lean-miri`'s `Miri.Interpreter.IntegerOps.unary` / `Miri.Memory.Scalar.toBool`. -/
theorem evalUnOp_neg_not_simulation
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    (locals : List LocalSlot) (mem : Memory) :
    -- (1) Integer bitwise NOT (`UnOp.not` ↔ `IntegerOps.unary .Not`) for all integer kinds:
    (∀ (kind : Miri.MIR.IntegerKind) (ty : Ty),
      (ty.kind = .int .i8 ∨ ty.kind = .int .i16 ∨ ty.kind = .int .i32 ∨
        ty.kind = .int .i64 ∨ ty.kind = .int .i128 ∨ ty.kind = .int .isize ∨
        ty.kind = .uint .u8 ∨ ty.kind = .uint .u16 ∨ ty.kind = .uint .u32 ∨
        ty.kind = .uint .u64 ∨ ty.kind = .uint .u128 ∨ ty.kind = .uint .usize) →
      ∃ sc' msc',
        evalUnaryNot sc (some ty) locals mem = .ok (.scalar sc') locals mem ∧
        Miri.Interpreter.IntegerOps.unary .Not
          ⟨msc, ⟨translateSizeBytes sc.sizeBytes, kind⟩⟩ = .ok msc' ∧
        ScalarRel sc' msc') ∧
    -- (2) Signed integer negation (`UnOp.neg` ↔ `IntegerOps.unary .Neg`):
    (∀ (kind : Miri.MIR.IntegerKind),
      kind.signed = true →
      let m := scalarModulus sc.sizeBytes
      let negSc : MirAst.ScalarInt :=
        ⟨wrapScalarBits (m - wrapScalarBits sc.bits m) m, sc.sizeBytes⟩
      ∃ msc',
        Miri.Interpreter.IntegerOps.unary .Neg
          ⟨msc, ⟨translateSizeBytes sc.sizeBytes, kind⟩⟩ = .ok msc' ∧
        ScalarRel negSc msc') ∧
    -- (3) Boolean logical NOT (`UnOp.not` on `Ty.bool` ↔ boolean inversion):
    (∀ (ty : Ty) (b : Bool),
      ty.kind = .bool →
      sc = boolToScalar b →
      msc = Miri.Memory.ScalarInt.ofBool b →
      evalUnaryNot sc (some ty) locals mem =
        .ok (.scalar (boolToScalar (!b))) locals mem ∧
      (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBool = .ok b ∧
      ScalarRel (boolToScalar (!b)) (Miri.Memory.ScalarInt.ofBool (!b))) := by
  have hbeq0 := hrel.beq_sizeBytes_zero
  have hx : sc.bits < 2 ^ (8 * sc.sizeBytes) := by
    rw [← scalarModulus_eq_two_pow]; exact hrel.canonical
  refine ⟨?_, ?_, ?_⟩
  · intro kind ty hty
    rw [integerOps_unary_eq hrel kind .Not]
    obtain ⟨msc', _, htr, hrel', _⟩ :=
      truncateInt_spec hrel.validBytes kind (~~~decodeBitsInt kind.signed sc.sizeBytes sc.bits)
    rw [← wrap_not_decodeBitsInt hx] at hrel'
    refine ⟨⟨(scalarModulus sc.sizeBytes - 1) - wrapScalarBits sc.bits (scalarModulus sc.sizeBytes),
      sc.sizeBytes⟩, msc', ?_, ?_, hrel'⟩
    · rcases hty with h | h | h | h | h | h | h | h | h | h | h | h <;>
        simp [evalUnaryNot, h, hbeq0, Nat.sub_eq]
    · simp [htr, bind, Except.bind, pure, Except.pure]
  · intro kind hsigned
    dsimp only
    rw [integerOps_unary_eq hrel kind .Neg]
    obtain ⟨msc', _, htr, hrel', _⟩ :=
      truncateInt_spec hrel.validBytes kind (-decodeBitsInt true sc.sizeBytes sc.bits)
    rw [hsigned]
    rw [← wrap_neg_decodeBitsInt hx] at hrel'
    refine ⟨msc', ?_, hrel'⟩
    simp [htr, bind, Except.bind, pure, Except.pure]
  · intro ty b hty hsc hmsc
    subst hsc hmsc
    cases b <;>
      exact ⟨by simp [evalUnaryNot, hty, boolToScalar], rfl, ScalarRel.of_boolToScalar _⟩

/-- Outcome correspondence between Anneal's `evalScalarBinOp` (`RvalueEvalResult`)
and `lean-miri`'s `Miri.Interpreter.IntegerOps.binary` / `binaryBool`
(`Except IntegerOpError IntegerResult`). -/
inductive IntegerBinOpResultRel (locals : List LocalSlot) (mem : Memory) :
    RvalueEvalResult →
    Except Miri.Interpreter.IntegerOpError Miri.Interpreter.IntegerResult →
    Prop where
  | scalar (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt) :
      ScalarRel sc msc →
      IntegerBinOpResultRel locals mem
        (.ok (.scalar sc) locals mem)
        (.ok (.scalar msc))
  | withOverflow (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt) (ovf : Bool) :
      ScalarRel sc msc →
      IntegerBinOpResultRel locals mem
        (.ok (.aggregate 0 [.scalar sc, .scalar (boolToScalar ovf)]) locals mem)
        (.ok (.withOverflow msc ovf))
  | boolean (b : Bool) :
      IntegerBinOpResultRel locals mem
        (.ok (.scalar (boolToScalar b)) locals mem)
        (.ok (.boolean b))
  | ub (reason : Miri.Interpreter.IntegerUB) :
      IntegerBinOpResultRel locals mem
        .ub
        (.error (.undefinedBehavior reason))

/-- Predicate for bitwise binary operators (`BitAnd`, `BitOr`, `BitXor`). -/
def IsBitwiseBinOp (op : MirAst.BinOp) : Prop :=
  op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor

/-- Theorem 2 (`LM-1.1`): Bitwise binary operator simulation (`BitAnd`, `BitOr`, `BitXor`)
between Anneal's `MirSemantics.evalScalarBinOp` and `lean-miri`'s
`Miri.Interpreter.IntegerOps.binary` (for all signed/unsigned integer types) and
`Miri.Interpreter.IntegerOps.binaryBool` (for `bool`). -/
theorem evalBinOp_bitwise_simulation
    {op : MirAst.BinOp} {mop : Miri.MIR.BinOp}
    (hbw : IsBitwiseBinOp op)
    (hop : translateBinOp op = some mop)
    (locals : List LocalSlot) (mem : Memory) :
    -- (1) Signed and unsigned integer bitwise operators (`BitAnd`, `BitOr`, `BitXor`):
    (∀ {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
      (kind : Miri.MIR.IntegerKind),
      ScalarRel sc₁ msc₁ →
      ScalarRel sc₂ msc₂ →
      sc₁.sizeBytes = sc₂.sizeBytes →
      IntegerBinOpResultRel locals mem
        (evalScalarBinOp op sc₁ sc₂ locals mem kind.signed)
        (Miri.Interpreter.IntegerOps.binary mop
          ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
          ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩)) ∧
    -- (2) Boolean bitwise operators (`BitAnd`, `BitOr`, `BitXor`):
    (∀ (b₁ b₂ : Bool),
      IntegerBinOpResultRel locals mem
        (evalScalarBinOp op (boolToScalar b₁) (boolToScalar b₂) locals mem false)
        (Miri.Interpreter.IntegerOps.binaryBool mop b₁ b₂)) := by
  refine ⟨?_, ?_⟩
  · intro sc₁ sc₂ msc₁ msc₂ kind hrel₁ hrel₂ hsz_eq
    have hbeq0 := hrel₁.beq_sizeBytes_zero
    have hbeq_eq : Nat.beq sc₁.sizeBytes sc₂.sizeBytes = true := by
      rw [hsz_eq, Nat.beq_refl]
    have hx : sc₁.bits < 2 ^ (8 * sc₁.sizeBytes) := by
      rw [← scalarModulus_eq_two_pow]; exact hrel₁.canonical
    have hy : sc₂.bits < 2 ^ (8 * sc₁.sizeBytes) := by
      rw [hsz_eq, ← scalarModulus_eq_two_pow]; exact hrel₂.canonical
    have hx' : sc₁.bits < 2 ^ (sc₁.sizeBytes * 8) := by
      rw [Nat.mul_comm]; exact hx
    have hy' : sc₂.bits < 2 ^ (sc₁.sizeBytes * 8) := by
      rw [Nat.mul_comm]; exact hy
    have htoNat₁ := bitVec_ofNat_toNat_of_valid hrel₁.validBytes hrel₁.canonical
    have htoNat₂ := bitVec_ofNat_toNat_of_valid hrel₂.validBytes hrel₂.canonical
    rw [integerOps_binary_eq hrel₁ hrel₂ kind kind mop]
    have htoUInt₁ := hrel₁.toUInt_eq
    have htoUInt₂ := hrel₂.toUInt_eq
    rw [← hsz_eq] at htoUInt₂ ⊢
    rcases hbw with rfl | rfl | rfl
    · simp only [translateBinOp, Option.some.injEq] at hop; subst hop
      obtain ⟨hand_eq, hand_lt⟩ := bitwiseAndBits_eq_land (sc₁.sizeBytes * 8) sc₁.bits sc₂.bits hx' hy'
      rw [Nat.mul_comm] at hand_lt
      obtain ⟨msc', hmsc', hrel'⟩ :=
        truncateFromUInt_translateSizeBytes_spec hrel₁.validBytes
          (BitVec.ofNat 128 sc₁.bits &&& BitVec.ofNat 128 sc₂.bits)
      have hbv : (BitVec.ofNat 128 sc₁.bits &&& BitVec.ofNat 128 sc₂.bits).toNat % 2 ^ (8 * sc₁.sizeBytes) =
          bitwiseAndBits (sc₁.sizeBytes * 8) sc₁.bits sc₂.bits := by
        rw [BitVec.toNat_and, htoNat₁, htoNat₂, Nat.mod_eq_of_lt hand_lt, hand_eq]
      rw [hbv] at hrel'
      simp only [evalScalarBinOp, hbeq0, hbeq_eq, Nat.mul_eq, htoUInt₁, htoUInt₂, hmsc',
        Except.mapError, bind, Except.bind, pure, Except.pure, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, BEq.beq]
      exact IntegerBinOpResultRel.scalar _ msc' hrel'
    · simp only [translateBinOp, Option.some.injEq] at hop; subst hop
      obtain ⟨hor_eq, hor_lt⟩ := bitwiseOrBits_eq_lor (sc₁.sizeBytes * 8) sc₁.bits sc₂.bits hx' hy'
      rw [Nat.mul_comm] at hor_lt
      obtain ⟨msc', hmsc', hrel'⟩ :=
        truncateFromUInt_translateSizeBytes_spec hrel₁.validBytes
          (BitVec.ofNat 128 sc₁.bits ||| BitVec.ofNat 128 sc₂.bits)
      have hbv : (BitVec.ofNat 128 sc₁.bits ||| BitVec.ofNat 128 sc₂.bits).toNat % 2 ^ (8 * sc₁.sizeBytes) =
          bitwiseOrBits (sc₁.sizeBytes * 8) sc₁.bits sc₂.bits := by
        rw [BitVec.toNat_or, htoNat₁, htoNat₂, Nat.mod_eq_of_lt hor_lt, hor_eq]
      rw [hbv] at hrel'
      simp only [evalScalarBinOp, hbeq0, hbeq_eq, Nat.mul_eq, htoUInt₁, htoUInt₂, hmsc',
        Except.mapError, bind, Except.bind, pure, Except.pure, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, BEq.beq]
      exact IntegerBinOpResultRel.scalar _ msc' hrel'
    · simp only [translateBinOp, Option.some.injEq] at hop; subst hop
      obtain ⟨hxor_eq, hxor_lt⟩ := bitwiseXorBits_eq_xor (sc₁.sizeBytes * 8) sc₁.bits sc₂.bits hx' hy'
      rw [Nat.mul_comm] at hxor_lt
      obtain ⟨msc', hmsc', hrel'⟩ :=
        truncateFromUInt_translateSizeBytes_spec hrel₁.validBytes
          (BitVec.ofNat 128 sc₁.bits ^^^ BitVec.ofNat 128 sc₂.bits)
      have hbv : (BitVec.ofNat 128 sc₁.bits ^^^ BitVec.ofNat 128 sc₂.bits).toNat % 2 ^ (8 * sc₁.sizeBytes) =
          bitwiseXorBits (sc₁.sizeBytes * 8) sc₁.bits sc₂.bits := by
        rw [BitVec.toNat_xor, htoNat₁, htoNat₂, Nat.mod_eq_of_lt hxor_lt, hxor_eq]
      rw [hbv] at hrel'
      simp only [evalScalarBinOp, hbeq0, hbeq_eq, Nat.mul_eq, htoUInt₁, htoUInt₂, hmsc',
        Except.mapError, bind, Except.bind, pure, Except.pure, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, BEq.beq]
      exact IntegerBinOpResultRel.scalar _ msc' hrel'
  · intro b₁ b₂
    rcases hbw with rfl | rfl | rfl
    · simp only [translateBinOp, Option.some.injEq] at hop; subst hop
      cases b₁ <;> cases b₂
      · exact IntegerBinOpResultRel.boolean false
      · exact IntegerBinOpResultRel.boolean false
      · exact IntegerBinOpResultRel.boolean false
      · exact IntegerBinOpResultRel.boolean true
    · simp only [translateBinOp, Option.some.injEq] at hop; subst hop
      cases b₁ <;> cases b₂
      · exact IntegerBinOpResultRel.boolean false
      · exact IntegerBinOpResultRel.boolean true
      · exact IntegerBinOpResultRel.boolean true
      · exact IntegerBinOpResultRel.boolean true
    · simp only [translateBinOp, Option.some.injEq] at hop; subst hop
      cases b₁ <;> cases b₂
      · exact IntegerBinOpResultRel.boolean false
      · exact IntegerBinOpResultRel.boolean true
      · exact IntegerBinOpResultRel.boolean true
      · exact IntegerBinOpResultRel.boolean false

/-! ## 3. Shift Binary Operator Simulation (`evalBinOp_shift_simulation`) -/

theorem translateSizeBytes_bits_eq {sz : Nat} (hsz : ValidScalarBytes sz) :
    (translateSizeBytes sz).bits = .ok (UInt64.ofNat (sz * 8)) ∧
      (UInt64.ofNat (sz * 8)).toNat = sz * 8 := by
  rcases hsz with rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem valid_bits_dvd_two_pow {sz₁ sz₂ : Nat}
    (hsz₁ : ValidScalarBytes sz₁) (hsz₂ : ValidScalarBytes sz₂) :
    ((sz₁ * 8 : Nat) : Int) ∣ (2 : Int) ^ (8 * sz₂) := by
  rcases hsz₁ with rfl | rfl | rfl | rfl | rfl <;>
    rcases hsz₂ with rfl | rfl | rfl | rfl | rfl <;> decide

theorem valid_bits_le_half_modulus {sz₁ sz₂ : Nat}
    (hsz₁ : ValidScalarBytes sz₁) (hsz₂ : ValidScalarBytes sz₂) :
    sz₁ * 8 ≤ 2 ^ (8 * sz₂ - 1) := by
  rcases hsz₁ with rfl | rfl | rfl | rfl | rfl <;>
    rcases hsz₂ with rfl | rfl | rfl | rfl | rfl <;> decide

theorem shift_amount_toNat_eq {sz₁ sz₂ : Nat}
    (hsz₁ : ValidScalarBytes sz₁) (hsz₂ : ValidScalarBytes sz₂)
    (signed₂ : Bool) (y : Nat) :
    (decodeBitsInt signed₂ sz₂ y % Int.ofNat (sz₁ * 8)).toNat = y % (sz₁ * 8) := by
  change (decodeBitsInt signed₂ sz₂ y % ((sz₁ * 8 : Nat) : Int)).toNat = y % (sz₁ * 8)
  have hcast : ((y % (sz₁ * 8) : Nat) : Int) = (y : Int) % ((sz₁ * 8 : Nat) : Int) := by
    rw [Int.natCast_emod]
  have hp : ((2 ^ (8 * sz₂) : Nat) : Int) = (2 : Int) ^ (8 * sz₂) := by push_cast; rfl
  unfold decodeBitsInt
  cases signed₂
  · simp only [Bool.false_eq_true, ↓reduceIte, ← hcast, Int.toNat_natCast]
  · simp only [↓reduceIte, hp]
    split
    · rw [← hcast, Int.toNat_natCast]
    · have hdvd := valid_bits_dvd_two_pow hsz₁ hsz₂
      rw [Int.sub_emod, Int.emod_eq_zero_of_dvd hdvd, Int.sub_zero,
        Int.emod_emod, ← hcast, Int.toNat_natCast]

theorem shift_overflow_eq {sz₁ sz₂ : Nat}
    (hsz₁ : ValidScalarBytes sz₁) (hsz₂ : ValidScalarBytes sz₂)
    (signed₂ : Bool) (y : Nat) (hy : y < 2 ^ (8 * sz₂)) :
    let r := decodeBitsInt signed₂ sz₂ y
    ((r % Int.ofNat (sz₁ * 8)) != r) = Nat.ble (sz₁ * 8) y := by
  dsimp only
  change ((decodeBitsInt signed₂ sz₂ y % ((sz₁ * 8 : Nat) : Int)) !=
    decodeBitsInt signed₂ sz₂ y) = Nat.ble (sz₁ * 8) y
  rw [nat_ble_eq_decide]
  have hle := valid_bits_le_half_modulus hsz₁ hsz₂
  have hpos : (0 : Int) < ((sz₁ * 8 : Nat) : Int) := by
    rcases hsz₁ with rfl | rfl | rfl | rfl | rfl <;> decide
  have hmod_nonneg : 0 ≤ decodeBitsInt signed₂ sz₂ y % ((sz₁ * 8 : Nat) : Int) :=
    Int.emod_nonneg _ (Int.ne_of_gt hpos)
  have hmod_lt : decodeBitsInt signed₂ sz₂ y % ((sz₁ * 8 : Nat) : Int) < ((sz₁ * 8 : Nat) : Int) :=
    Int.emod_lt_of_pos _ hpos
  have hp : ((2 ^ (8 * sz₂) : Nat) : Int) = (2 : Int) ^ (8 * sz₂) := by push_cast; rfl
  have hy' : (y : Int) < (2 : Int) ^ (8 * sz₂) := by exact_mod_cast hy
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, Ne, decide_eq_true_eq]
  unfold decodeBitsInt at hmod_nonneg hmod_lt ⊢
  cases signed₂
  · simp only [Bool.false_eq_true, ↓reduceIte] at hmod_nonneg hmod_lt ⊢
    constructor
    · intro hne
      by_cases hlt : y < sz₁ * 8
      · exact absurd (Int.emod_eq_of_lt (by omega) (by omega)) hne
      · omega
    · intro hge heq
      omega
  · simp only [↓reduceIte, hp] at hmod_nonneg hmod_lt ⊢
    by_cases hlt_half : y < 2 ^ (8 * sz₂ - 1) <;>
      simp only [hlt_half, ↓reduceIte] at hmod_nonneg hmod_lt ⊢
    · constructor
      · intro hne
        by_cases hlt : y < sz₁ * 8
        · exact absurd (Int.emod_eq_of_lt (by omega) (by omega)) hne
        · omega
      · intro hge heq
        omega
    · constructor
      · intro _; omega
      · intro _ heq; omega

theorem shiftLeftBits_decodeBitsInt {signed : Bool} {sz x : Nat}
    (hx : x < 2 ^ (8 * sz)) (k : Nat) :
    shiftLeftBits x k (scalarModulus sz) =
      ((decodeBitsInt signed sz x <<< k) % (2 : Int) ^ (8 * sz)).toNat := by
  unfold shiftLeftBits
  rw [Nat.mul_eq, scalarPow2_eq_two_pow, wrap_eq_toNat, int_shiftLeft_eq_mul_pow]
  congr 1
  have hcast : ((x * 2 ^ k : Nat) : Int) = (x : Int) * (2 : Int) ^ k := by push_cast; rfl
  have hxMod : (x : Int) % (2 : Int) ^ (8 * sz) = (x : Int) :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast hx)
  rw [hcast, Int.mul_emod (decodeBitsInt signed sz x), decodeBitsInt_emod hx,
    Int.mul_emod (x : Int), hxMod]

theorem shiftRightUnsigned_decodeBitsInt {sz x : Nat}
    (hx : x < 2 ^ (8 * sz)) (k : Nat) :
    wrapScalarBits (shiftRightUnsignedBits x k) (scalarModulus sz) =
      ((decodeBitsInt false sz x >>> k) % (2 : Int) ^ (8 * sz)).toNat := by
  unfold shiftRightUnsignedBits
  rw [int_shiftRight_eq_ediv_pow]
  have hlt : x / 2 ^ k < 2 ^ (8 * sz) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  have hdiv : (x : Int) / (2 : Int) ^ k = ((x / 2 ^ k : Nat) : Int) := by
    have hpk : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) := by push_cast; rfl
    rw [hpk]; rfl
  simp only [nat_div_eq_div, scalarPow2_eq_two_pow, wrapScalarBits_eq_mod,
    scalarModulus_eq_two_pow, Nat.mod_eq_of_lt hlt, decodeBitsInt, Bool.false_eq_true, ↓reduceIte]
  rw [hdiv, Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hlt), Int.toNat_natCast]

theorem two_pow_div_two (n : Nat) (hn : 0 < n) : Nat.div (2 ^ n) 2 = 2 ^ (n - 1) := by
  change 2 ^ n / 2 = 2 ^ (n - 1)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [Nat.pow_succ]

theorem isSignedNegative_eq {sz x : Nat} (hsz : ValidScalarBytes sz) (hx : x < 2 ^ (8 * sz)) :
    isSignedNegative x sz = decide (2 ^ (8 * sz - 1) ≤ x) := by
  have hsz0 : sz ≠ 0 := by rcases hsz with rfl | rfl | rfl | rfl | rfl <;> omega
  have ⟨_, hw0⟩ := validScalarBytes_bits_le_128 hsz
  simp only [isSignedNegative, nat_beq_eq_decide, decide_eq_false hsz0,
    scalarModulus_eq_two_pow, two_pow_div_two (8 * sz) hw0, wrapScalarBits_eq_mod,
    Nat.mod_eq_of_lt hx, nat_ble_eq_decide]

theorem arithmeticShrBits_decodeBitsInt {sz x k : Nat}
    (hsz : ValidScalarBytes sz) (hx : x < 2 ^ (8 * sz)) (hk : k < sz * 8) :
    arithmeticShrBits x sz k =
      ((decodeBitsInt true sz x >>> k) % (2 : Int) ^ (8 * sz)).toNat := by
  rw [int_shiftRight_eq_ediv_pow]
  have hk' : k < 8 * sz := by omega
  have hp : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  have hpk : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) := by push_cast; rfl
  have hsplit : 2 ^ (8 * sz) = 2 ^ (8 * sz - k) * 2 ^ k := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have hQpos : 0 < 2 ^ (8 * sz - k) := Nat.two_pow_pos _
  have hSpos : 0 < 2 ^ k := Nat.two_pow_pos _
  have hqlt : x / 2 ^ k < 2 ^ (8 * sz - k) :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hsplit]; exact hx)
  have hltM : x / 2 ^ k < 2 ^ (8 * sz) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  simp only [arithmeticShrBits, scalarModulus_eq_two_pow, wrapScalarBits_eq_mod,
    Nat.mod_eq_of_lt hx, shiftRightUnsignedBits, nat_div_eq_div, isSignedNegative_eq hsz hx,
    Nat.mul_eq, Nat.sub_eq, Nat.add_eq, Nat.mul_comm sz 8, scalarPow2_eq_two_pow,
    decodeBitsInt, ↓reduceIte]
  rw [hp, hpk]
  by_cases hxH : 2 ^ (8 * sz - 1) ≤ x
  · rw [decide_eq_true hxH]; dsimp only
    simp only [show ¬(x < 2 ^ (8 * sz - 1)) by omega, ↓reduceIte]
    have hdiv : ((x : Int) - ((2 ^ (8 * sz) : Nat) : Int)) / ((2 ^ k : Nat) : Int) =
        ((x / 2 ^ k : Nat) : Int) - ((2 ^ (8 * sz - k) : Nat) : Int) := by
      have hrew : (x : Int) - ((2 ^ (8 * sz) : Nat) : Int) =
          (x : Int) + (-((2 ^ (8 * sz - k) : Nat) : Int)) * ((2 ^ k : Nat) : Int) := by
        have hmul : ((2 ^ (8 * sz - k) * 2 ^ k : Nat) : Int) =
            ((2 ^ (8 * sz - k) : Nat) : Int) * ((2 ^ k : Nat) : Int) := by push_cast; rfl
        rw [hsplit, hmul, Int.neg_mul]; omega
      rw [hrew, Int.add_mul_ediv_right _ _ (by omega)]
      have hed : (x : Int) / ((2 ^ k : Nat) : Int) = ((x / 2 ^ k : Nat) : Int) := rfl
      rw [hed]; omega
    rw [hdiv]
    generalize x / 2 ^ k = q at hqlt ⊢
    generalize 2 ^ (8 * sz - k) = Q at hsplit hqlt hQpos ⊢
    generalize 2 ^ (8 * sz) = M at hsplit ⊢
    have hQM : Q ≤ M := by
      have : Q * 1 ≤ Q * 2 ^ k := Nat.mul_le_mul_left Q hSpos
      omega
    rw [Nat.mod_eq_of_lt (by omega : q + (M - Q) < M)]
    have hemod : ((q : Int) - (Q : Int)) % (M : Int) = (q : Int) - (Q : Int) + (M : Int) := by
      rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hemod]
    omega
  · rw [decide_eq_false hxH]; dsimp only
    simp only [show x < 2 ^ (8 * sz - 1) by omega, ↓reduceIte, Nat.mod_eq_of_lt hltM]
    have hed : (x : Int) / ((2 ^ k : Nat) : Int) = ((x / 2 ^ k : Nat) : Int) := rfl
    rw [hed, Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hltM), Int.toNat_natCast]

/-- Predicate for shift binary operators (`Shl`, `Shr`, `ShlUnchecked`, `ShrUnchecked`). -/
def IsShiftBinOp (op : MirAst.BinOp) : Prop :=
  op = .shl ∨ op = .shr ∨ op = .shlUnchecked ∨ op = .shrUnchecked

/-- Theorem 3 (`LM-1.1`): Shift binary operator simulation (`Shl`, `Shr`, `ShlUnchecked`,
`ShrUnchecked`) between Anneal's `MirSemantics.evalScalarBinOp` and `lean-miri`'s
`Miri.Interpreter.IntegerOps.binary` across arbitrary LHS and RHS integer widths and signednesses. -/
theorem evalBinOp_shift_simulation
    {op : MirAst.BinOp} {mop : Miri.MIR.BinOp}
    (hsh : IsShiftBinOp op)
    (hop : translateBinOp op = some mop)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (kind₁ kind₂ : Miri.MIR.IntegerKind)
    (locals : List LocalSlot) (mem : Memory) :
    IntegerBinOpResultRel locals mem
      (evalScalarBinOp op sc₁ sc₂ locals mem kind₁.signed)
      (Miri.Interpreter.IntegerOps.binary mop
        ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind₁⟩⟩
        ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind₂⟩⟩) := by
  have hbeq₁ := hrel₁.beq_sizeBytes_zero
  have hbeq₂ := hrel₂.beq_sizeBytes_zero
  have hx : sc₁.bits < 2 ^ (8 * sc₁.sizeBytes) := by
    rw [← scalarModulus_eq_two_pow]; exact hrel₁.canonical
  have hy : sc₂.bits < 2 ^ (8 * sc₂.sizeBytes) := by
    rw [← scalarModulus_eq_two_pow]; exact hrel₂.canonical
  obtain ⟨hbits_ok, hbits_toNat⟩ := translateSizeBytes_bits_eq hrel₁.validBytes
  have hamt := shift_amount_toNat_eq hrel₁.validBytes hrel₂.validBytes kind₂.signed sc₂.bits
  have hovf := shift_overflow_eq hrel₁.validBytes hrel₂.validBytes kind₂.signed sc₂.bits hy
  dsimp only at hovf
  rw [integerOps_binary_eq hrel₁ hrel₂ kind₁ kind₂ mop]
  rcases hsh with rfl | rfl | rfl | rfl
  · simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    obtain ⟨msc', lossy, htr, hrel', _⟩ :=
      truncateInt_spec hrel₁.validBytes kind₁
        (decodeBitsInt kind₁.signed sc₁.sizeBytes sc₁.bits <<<
          (sc₂.bits % (sc₁.sizeBytes * 8)))
    rw [← shiftLeftBits_decodeBitsInt hx] at hrel'
    simp only [evalScalarBinOp, hbeq₁, hbeq₂, Nat.mul_eq, nat_mod_eq_mod,
      shiftInt, hbits_ok, hbits_toNat, hamt, htr, Miri.MIR.BinOp.isUnchecked,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte, Except.mapError,
      bind, Except.bind, pure, Except.pure, BEq.beq]
    exact IntegerBinOpResultRel.scalar _ msc' hrel'
  · simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    obtain ⟨msc', lossy, htr, hrel', _⟩ :=
      truncateInt_spec hrel₁.validBytes kind₁
        (decodeBitsInt kind₁.signed sc₁.sizeBytes sc₁.bits >>>
          (sc₂.bits % (sc₁.sizeBytes * 8)))
    have hklt : sc₂.bits % (sc₁.sizeBytes * 8) < sc₁.sizeBytes * 8 := by
      have ⟨_, hw0⟩ := validScalarBytes_bits_le_128 hrel₁.validBytes
      exact Nat.mod_lt _ (by omega)
    simp only [evalScalarBinOp, hbeq₁, hbeq₂, Nat.mul_eq, nat_mod_eq_mod,
      shiftInt, hbits_ok, hbits_toNat, hamt, htr, Miri.MIR.BinOp.isUnchecked,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte, Except.mapError,
      bind, Except.bind, pure, Except.pure, BEq.beq]
    cases hs : kind₁.signed
    · rw [hs, ← shiftRightUnsigned_decodeBitsInt hx] at hrel'
      exact IntegerBinOpResultRel.scalar _ msc' hrel'
    · rw [hs, ← arithmeticShrBits_decodeBitsInt hrel₁.validBytes hx hklt] at hrel'
      exact IntegerBinOpResultRel.scalar _ msc' hrel'
  · simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    obtain ⟨msc', lossy, htr, hrel', _⟩ :=
      truncateInt_spec hrel₁.validBytes kind₁
        (decodeBitsInt kind₁.signed sc₁.sizeBytes sc₁.bits <<<
          (sc₂.bits % (sc₁.sizeBytes * 8)))
    rw [← shiftLeftBits_decodeBitsInt hx] at hrel'
    simp only [evalScalarBinOp, hbeq₁, hbeq₂, Nat.mul_eq,
      shiftInt, hbits_ok, hbits_toNat, hamt, hovf, htr, Miri.MIR.BinOp.isUnchecked,
      Bool.and_true, Except.mapError, bind, Except.bind, pure, Except.pure, BEq.beq]
    cases hble : Nat.ble (sc₁.sizeBytes * 8) sc₂.bits
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hlt : sc₂.bits < sc₁.sizeBytes * 8 := by
        rw [nat_ble_eq_decide, decide_eq_false_iff_not] at hble; omega
      rw [Nat.mod_eq_of_lt hlt] at hrel'
      exact IntegerBinOpResultRel.scalar _ msc' hrel'
    · simp only [↓reduceIte]
      exact IntegerBinOpResultRel.ub _
  · simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    obtain ⟨msc', lossy, htr, hrel', _⟩ :=
      truncateInt_spec hrel₁.validBytes kind₁
        (decodeBitsInt kind₁.signed sc₁.sizeBytes sc₁.bits >>>
          (sc₂.bits % (sc₁.sizeBytes * 8)))
    simp only [evalScalarBinOp, hbeq₁, hbeq₂, Nat.mul_eq,
      shiftInt, hbits_ok, hbits_toNat, hamt, hovf, htr, Miri.MIR.BinOp.isUnchecked,
      Bool.and_true, Except.mapError, bind, Except.bind, pure, Except.pure, BEq.beq]
    cases hble : Nat.ble (sc₁.sizeBytes * 8) sc₂.bits
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hlt : sc₂.bits < sc₁.sizeBytes * 8 := by
        rw [nat_ble_eq_decide, decide_eq_false_iff_not] at hble; omega
      rw [Nat.mod_eq_of_lt hlt] at hrel'
      cases hs : kind₁.signed
      · rw [hs, ← shiftRightUnsigned_decodeBitsInt hx] at hrel'
        exact IntegerBinOpResultRel.scalar _ msc' hrel'
      · rw [hs, ← arithmeticShrBits_decodeBitsInt hrel₁.validBytes hx hlt] at hrel'
        exact IntegerBinOpResultRel.scalar _ msc' hrel'
    · simp only [↓reduceIte]
      exact IntegerBinOpResultRel.ub _

/-! ## 4. Arithmetic, Checked, Division/Remainder & Comparison Simulation (`evalBinOp_arithmetic_simulation`) -/

theorem two_pow_byte_split {sz : Nat} (hsz : ValidScalarBytes sz) :
    2 ^ (8 * sz) = 2 * 2 ^ (8 * sz - 1) ∧ 2 ≤ 2 ^ (8 * sz - 1) := by
  rcases hsz with rfl | rfl | rfl | rfl | rfl <;> decide

theorem canRepresentInt_unsigned (sz : Nat) (v : Int) :
    canRepresentInt false sz v = decide (0 ≤ v ∧ v < ((2 ^ (8 * sz) : Nat) : Int)) := by
  have hp : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  simp only [canRepresentInt, Bool.false_eq_true, ↓reduceIte, hp]

theorem canRepresentInt_signed (sz : Nat) (v : Int) :
    canRepresentInt true sz v =
      decide (-((2 ^ (8 * sz - 1) : Nat) : Int) ≤ v ∧ v < ((2 ^ (8 * sz - 1) : Nat) : Int)) := by
  have hp : (2 : Int) ^ (8 * sz - 1) = ((2 ^ (8 * sz - 1) : Nat) : Int) := by push_cast; rfl
  simp only [canRepresentInt, ↓reduceIte, hp]

theorem nat_emod_toNat_of_lt (q M : Nat) (hqM : q < M) :
    ((q : Int) % (M : Int)).toNat = q := by
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]

theorem neg_nat_emod_toNat (q M : Nat) (hq0 : 0 < q) (hqM : q < M) :
    ((-(q : Int)) % (M : Int)).toNat = M - q := by
  have : (-(q : Int)) % (M : Int) = (-(q : Int)) + (M : Int) := by
    rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [this]
  omega

theorem tdiv_nat_nat (a b : Nat) :
    Int.tdiv (a : Int) (b : Int) = ((a / b : Nat) : Int) := rfl

theorem tmod_nat_nat (a b : Nat) :
    Int.tmod (a : Int) (b : Int) = ((a % b : Nat) : Int) := rfl

theorem tdiv_nat_neg (a b : Nat) (hb : b ≠ 0) :
    Int.tdiv (a : Int) (-(b : Int)) = -((a / b : Nat) : Int) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

theorem tmod_nat_neg (a b : Nat) (hb : b ≠ 0) :
    Int.tmod (a : Int) (-(b : Int)) = ((a % b : Nat) : Int) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

theorem tdiv_neg_nat (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) :
    Int.tdiv (-(a : Int)) (b : Int) = -((a / b : Nat) : Int) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

theorem tmod_neg_nat (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) :
    Int.tmod (-(a : Int)) (b : Int) = -((a % b : Nat) : Int) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

theorem tdiv_neg_neg (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) :
    Int.tdiv (-(a : Int)) (-(b : Int)) = ((a / b : Nat) : Int) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

theorem tmod_neg_neg (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) :
    Int.tmod (-(a : Int)) (-(b : Int)) = -((a % b : Nat) : Int) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

theorem wrap_add_decodeBitsInt (signed : Bool) {sz x y : Nat}
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    wrapScalarBits (x + y) (scalarModulus sz) =
      ((decodeBitsInt signed sz x + decodeBitsInt signed sz y) % (2 : Int) ^ (8 * sz)).toNat := by
  rw [wrap_eq_toNat]
  congr 1
  rw [Int.add_emod (decodeBitsInt signed sz x), decodeBitsInt_emod hx, decodeBitsInt_emod hy]
  push_cast; rfl

theorem wrap_sub_decodeBitsInt (signed : Bool) {sz x y : Nat}
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    (let m := scalarModulus sz
      match Nat.ble y x with
      | true => wrapScalarBits (x - y) m
      | false => wrapScalarBits (m + wrapScalarBits x m - wrapScalarBits y m) m) =
      ((decodeBitsInt signed sz x - decodeBitsInt signed sz y) % (2 : Int) ^ (8 * sz)).toNat := by
  dsimp only
  have hp : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  have hmod : (decodeBitsInt signed sz x - decodeBitsInt signed sz y) % (2 : Int) ^ (8 * sz) =
      ((x : Int) - (y : Int)) % (2 : Int) ^ (8 * sz) := by
    rw [Int.sub_emod (decodeBitsInt signed sz x), decodeBitsInt_emod hx, decodeBitsInt_emod hy]
  rw [hmod, hp]
  clear hp hmod
  simp only [wrapScalarBits_eq_mod, scalarModulus_eq_two_pow, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy, nat_ble_eq_decide]
  generalize 2 ^ (8 * sz) = M at hx hy ⊢
  by_cases hle : y ≤ x
  · rw [decide_eq_true hle]; dsimp only
    rw [Nat.mod_eq_of_lt (by omega : x - y < M)]
    have hcast : (x : Int) - (y : Int) = ((x - y : Nat) : Int) := by omega
    rw [hcast, nat_emod_toNat_of_lt (x - y) M (by omega)]
  · rw [decide_eq_false hle]; dsimp only
    rw [Nat.mod_eq_of_lt (by omega : M + x - y < M)]
    have hcast : (x : Int) - (y : Int) = -((y - x : Nat) : Int) := by omega
    rw [hcast, neg_nat_emod_toNat (y - x) M (by omega) (by omega)]
    omega

theorem wrap_mul_decodeBitsInt (signed : Bool) {sz x y : Nat}
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    wrapScalarBits (x * y) (scalarModulus sz) =
      ((decodeBitsInt signed sz x * decodeBitsInt signed sz y) % (2 : Int) ^ (8 * sz)).toNat := by
  rw [wrap_eq_toNat]
  congr 1
  rw [Int.mul_emod (decodeBitsInt signed sz x), decodeBitsInt_emod hx, decodeBitsInt_emod hy]
  push_cast; rfl

theorem unsignedOverflowAdd_eq {sz x y : Nat} :
    Nat.ble (scalarModulus sz) (x + y) =
      !canRepresentInt false sz (decodeBitsInt false sz x + decodeBitsInt false sz y) := by
  rw [scalarModulus_eq_two_pow, nat_ble_eq_decide, canRepresentInt_unsigned]
  unfold decodeBitsInt
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem unsignedOverflowSub_eq {sz x y : Nat} (hx : x < 2 ^ (8 * sz)) :
    (!Nat.ble y x) =
      !canRepresentInt false sz (decodeBitsInt false sz x - decodeBitsInt false sz y) := by
  rw [nat_ble_eq_decide, canRepresentInt_unsigned]
  unfold decodeBitsInt
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  omega

theorem unsignedOverflowMul_eq {sz x y : Nat} :
    Nat.ble (scalarModulus sz) (x * y) =
      !canRepresentInt false sz (decodeBitsInt false sz x * decodeBitsInt false sz y) := by
  rw [scalarModulus_eq_two_pow, nat_ble_eq_decide, canRepresentInt_unsigned]
  unfold decodeBitsInt
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hcast : (x : Int) * (y : Int) = ((x * y : Nat) : Int) := by push_cast; rfl
  rw [hcast]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem signedOverflowAdd_eq {sz x y : Nat} (hsz : ValidScalarBytes sz)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    signedOverflowAdd x y sz =
      !canRepresentInt true sz (decodeBitsInt true sz x + decodeBitsInt true sz y) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split hsz
  have hsum_lt : (x + y) % 2 ^ (8 * sz) < 2 ^ (8 * sz) := Nat.mod_lt _ (by omega)
  have hsum_mod : (x + y) % 2 ^ (8 * sz) =
      if x + y < 2 ^ (8 * sz) then x + y else x + y - 2 ^ (8 * sz) := by
    split
    · next hlt => exact Nat.mod_eq_of_lt hlt
    · next hge =>
      have heq : x + y = (x + y - 2 ^ (8 * sz)) + 2 ^ (8 * sz) := by omega
      conv => lhs; rw [heq]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  simp only [signedOverflowAdd, scalarModulus_eq_two_pow, Nat.add_eq, wrapScalarBits_eq_mod,
    isSignedNegative_eq hsz hx, isSignedNegative_eq hsz hy,
    isSignedNegative_eq hsz hsum_lt, canRepresentInt_signed sz,
    decodeBitsInt, ↓reduceIte]
  rw [hsum_mod]
  clear hsum_lt hsum_mod
  generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy ⊢
  generalize 2 ^ (8 * sz) = M at hM hx hy ⊢
  apply Bool.eq_iff_iff.mpr
  by_cases hxyM : x + y < M
  · simp only [hxyM, ↓reduceIte]
    by_cases hxH : H ≤ x <;> by_cases hyH : H ≤ y <;> by_cases hsH : H ≤ x + y <;>
      simp [hxH, hyH, hsH, show x < H ↔ ¬(H ≤ x) by omega, show y < H ↔ ¬(H ≤ y) by omega] <;>
      omega
  · simp only [hxyM, ↓reduceIte]
    by_cases hxH : H ≤ x <;> by_cases hyH : H ≤ y <;> by_cases hsH : H ≤ x + y - M <;>
      simp [hxH, hyH, hsH, show x < H ↔ ¬(H ≤ x) by omega, show y < H ↔ ¬(H ≤ y) by omega] <;>
      omega

theorem signedOverflowSub_eq {sz x y : Nat} (hsz : ValidScalarBytes sz)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    signedOverflowSub x y sz =
      !canRepresentInt true sz (decodeBitsInt true sz x - decodeBitsInt true sz y) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split hsz
  simp only [signedOverflowSub, scalarModulus_eq_two_pow, Nat.add_eq, Nat.sub_eq,
    wrapScalarBits_eq_mod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, nat_ble_eq_decide,
    isSignedNegative_eq hsz hx, isSignedNegative_eq hsz hy,
    canRepresentInt_signed sz, decodeBitsInt, ↓reduceIte]
  by_cases hyx : y ≤ x
  · have hlt : x - y < 2 ^ (8 * sz) := by omega
    simp only [decide_eq_true hyx, Nat.mod_eq_of_lt hlt, isSignedNegative_eq hsz hlt]
    clear hlt
    generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy ⊢
    generalize 2 ^ (8 * sz) = M at hM hx hy ⊢
    apply Bool.eq_iff_iff.mpr
    by_cases hxH : H ≤ x <;> by_cases hyH : H ≤ y <;> by_cases hdH : H ≤ x - y <;>
      simp [hxH, hyH, hdH, show x < H ↔ ¬(H ≤ x) by omega, show y < H ↔ ¬(H ≤ y) by omega] <;>
      omega
  · have hlt : 2 ^ (8 * sz) + x - y < 2 ^ (8 * sz) := by omega
    simp only [decide_eq_false hyx, Nat.mod_eq_of_lt hlt, isSignedNegative_eq hsz hlt]
    clear hlt
    generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy ⊢
    generalize 2 ^ (8 * sz) = M at hM hx hy ⊢
    apply Bool.eq_iff_iff.mpr
    by_cases hxH : H ≤ x <;> by_cases hyH : H ≤ y <;> by_cases hdH : H ≤ M + x - y <;>
      simp [hxH, hyH, hdH, show x < H ↔ ¬(H ≤ x) by omega, show y < H ↔ ¬(H ≤ y) by omega] <;>
      omega

theorem signedOverflowMul_eq {sz x y : Nat} (hsz : ValidScalarBytes sz)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    signedOverflowMul x y sz =
      !canRepresentInt true sz (decodeBitsInt true sz x * decodeBitsInt true sz y) := by
  have hsz0 : sz ≠ 0 := by rcases hsz with rfl | rfl | rfl | rfl | rfl <;> omega
  have ⟨_, hw0⟩ := validScalarBytes_bits_le_128 hsz
  obtain ⟨hM, hH⟩ := two_pow_byte_split hsz
  unfold signedOverflowMul
  simp only [nat_beq_eq_decide, decide_eq_false hsz0, scalarModulus_eq_two_pow,
    two_pow_div_two (8 * sz) hw0, wrapScalarBits_eq_mod,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    isSignedNegative_eq hsz hx, isSignedNegative_eq hsz hy,
    nat_ble_eq_decide, Nat.sub_eq, Nat.mul_eq, canRepresentInt_signed sz,
    decodeBitsInt, ↓reduceIte]
  generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy ⊢
  generalize 2 ^ (8 * sz) = M at hM hx hy ⊢
  apply Bool.eq_iff_iff.mpr
  by_cases hxH : x < H <;> by_cases hyH : y < H
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
      decide_eq_false (by omega : ¬(H ≤ y))]
    have hmul : (x : Int) * (y : Int) = ((x * y : Nat) : Int) := by push_cast; rfl
    rw [hmul]
    generalize x * y = P
    by_cases hP0 : P = 0 <;> simp [hP0] <;> omega
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
      decide_eq_true (by omega : H ≤ y)]
    have hmul : (x : Int) * ((y : Int) - (M : Int)) = -((x * (M - y) : Nat) : Int) := by
      have hy' : (y : Int) - (M : Int) = -((M - y : Nat) : Int) := by omega
      rw [hy', Int.mul_neg]; push_cast; rfl
    rw [hmul]
    generalize x * (M - y) = P
    by_cases hP0 : P = 0 <;> simp [hP0] <;> omega
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_true (by omega : H ≤ x),
      decide_eq_false (by omega : ¬(H ≤ y))]
    have hmul : ((x : Int) - (M : Int)) * (y : Int) = -(((M - x) * y : Nat) : Int) := by
      have hx' : (x : Int) - (M : Int) = -((M - x : Nat) : Int) := by omega
      rw [hx', Int.neg_mul]; push_cast; rfl
    rw [hmul]
    generalize (M - x) * y = P
    by_cases hP0 : P = 0 <;> simp [hP0] <;> omega
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_true (by omega : H ≤ x),
      decide_eq_true (by omega : H ≤ y)]
    have hmul : ((x : Int) - (M : Int)) * ((y : Int) - (M : Int)) =
        (((M - x) * (M - y) : Nat) : Int) := by
      have hx' : (x : Int) - (M : Int) = -((M - x : Nat) : Int) := by omega
      have hy' : (y : Int) - (M : Int) = -((M - y : Nat) : Int) := by omega
      rw [hx', hy', Int.neg_mul_neg]; push_cast; rfl
    rw [hmul]
    generalize (M - x) * (M - y) = P
    by_cases hP0 : P = 0 <;> simp [hP0] <;> omega

theorem translateSizeBytes_signedIntMin_eq {sz : Nat} (hsz : ValidScalarBytes sz) :
    (translateSizeBytes sz).signedIntMin = .ok (-((2 ^ (8 * sz - 1) : Nat) : Int)) := by
  rcases hsz with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem decodeBitsInt_signed_min_iff {sz x : Nat} (hsz : ValidScalarBytes sz) :
    (decodeBitsInt true sz x == -((2 ^ (8 * sz - 1) : Nat) : Int)) =
      Nat.beq x (2 ^ (8 * sz - 1)) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split hsz
  rw [nat_beq_eq_decide]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, decodeBitsInt, ↓reduceIte]
  split <;> omega

theorem decodeBitsInt_signed_neg_one_iff {sz y : Nat} (hsz : ValidScalarBytes sz) :
    (decodeBitsInt true sz y == -1) = Nat.beq y (2 ^ (8 * sz) - 1) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split hsz
  rw [nat_beq_eq_decide]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, decodeBitsInt, ↓reduceIte]
  split <;> omega

theorem bool_and_eq_and (a b : Bool) : Bool.and a b = (a && b) := rfl

theorem bool_not_eq_not (a : Bool) : Bool.not a = !a := rfl

theorem evalSignedDiv_decodeBitsInt {sz x y : Nat} (hsz : ValidScalarBytes sz)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) (hy0 : y ≠ 0)
    (hno_ovf : (Nat.beq x (2 ^ (8 * sz - 1)) && Nat.beq y (2 ^ (8 * sz) - 1)) = false)
    (locals : List LocalSlot) (mem : Memory) :
    let q := Int.tdiv (decodeBitsInt true sz x) (decodeBitsInt true sz y)
    canRepresentInt true sz q = true ∧
      evalSignedDiv x y sz locals mem =
        .ok (.scalar ⟨(q % (2 : Int) ^ (8 * sz)).toNat, sz⟩) locals mem := by
  dsimp only
  obtain ⟨hM, hH⟩ := two_pow_byte_split hsz
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  have hcond : (decide (x = 2 ^ (8 * sz - 1)) && decide (y = 2 ^ (8 * sz) - 1)) = false := by
    rw [← nat_beq_eq_decide, ← nat_beq_eq_decide]; exact hno_ovf
  have hovf_not : ¬(x = 2 ^ (8 * sz - 1) ∧ y = 2 ^ (8 * sz) - 1) := by
    intro ⟨hxEq, hyEq⟩
    rw [decide_eq_true hxEq, decide_eq_true hyEq] at hcond
    cases hcond
  simp only [evalSignedDiv, scalarModulus_eq_two_pow, Nat.mul_eq, Nat.sub_eq,
    Nat.mul_comm sz 8, scalarPow2_eq_two_pow, wrapScalarBits_eq_mod,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    isSignedNegative_eq hsz hx, isSignedNegative_eq hsz hy,
    nat_beq_eq_decide, hcond, nat_div_eq_div, canRepresentInt_signed sz,
    decodeBitsInt, ↓reduceIte]
  rw [hp]
  generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy hovf_not ⊢
  generalize 2 ^ (8 * sz) = M at hM hx hy hovf_not ⊢
  by_cases hxH : x < H <;> by_cases hyH : y < H
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
      decide_eq_false (by omega : ¬(H ≤ y))]
    rw [tdiv_nat_nat]
    have hqH : x / y < H := Nat.lt_of_le_of_lt (Nat.div_le_self x y) hxH
    generalize x / y = q at hqH ⊢
    refine ⟨decide_eq_true (by omega), ?_⟩
    by_cases hq0 : q = 0
    · subst hq0; simp
    · rw [decide_eq_false hq0]; dsimp only
      rw [Nat.mod_eq_of_lt (by omega : q < M), nat_emod_toNat_of_lt q M (by omega)]
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
      decide_eq_true (by omega : H ≤ y)]
    have hy' : (y : Int) - (M : Int) = -((M - y : Nat) : Int) := by omega
    rw [hy', tdiv_nat_neg x (M - y) (by omega)]
    have hqH : x / (M - y) < H := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxH
    generalize x / (M - y) = q at hqH ⊢
    refine ⟨decide_eq_true (by omega), ?_⟩
    by_cases hq0 : q = 0
    · subst hq0; simp
    · rw [decide_eq_false hq0]; dsimp only
      rw [Nat.mod_eq_of_lt (by omega : M - q < M),
        neg_nat_emod_toNat q M (by omega) (by omega)]
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_true (by omega : H ≤ x),
      decide_eq_false (by omega : ¬(H ≤ y))]
    have hx' : (x : Int) - (M : Int) = -((M - x : Nat) : Int) := by omega
    rw [hx', tdiv_neg_nat (M - x) y (by omega) hy0]
    have hqH : (M - x) / y ≤ H := Nat.le_trans (Nat.div_le_self _ _) (by omega)
    generalize (M - x) / y = q at hqH ⊢
    refine ⟨decide_eq_true (by omega), ?_⟩
    by_cases hq0 : q = 0
    · subst hq0; simp
    · rw [decide_eq_false hq0]; dsimp only
      rw [Nat.mod_eq_of_lt (by omega : M - q < M),
        neg_nat_emod_toNat q M (by omega) (by omega)]
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_true (by omega : H ≤ x),
      decide_eq_true (by omega : H ≤ y)]
    have hx' : (x : Int) - (M : Int) = -((M - x : Nat) : Int) := by omega
    have hy' : (y : Int) - (M : Int) = -((M - y : Nat) : Int) := by omega
    rw [hx', hy', tdiv_neg_neg (M - x) (M - y) (by omega) (by omega)]
    have hqH : (M - x) / (M - y) < H := by
      by_cases hxEq : x = H
      · rw [hxEq, show M - H = H by omega]
        exact Nat.div_lt_self (by omega) (by omega)
      · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    generalize (M - x) / (M - y) = q at hqH ⊢
    refine ⟨decide_eq_true (by omega), ?_⟩
    by_cases hq0 : q = 0
    · subst hq0; simp
    · rw [decide_eq_false hq0]; dsimp only
      rw [Nat.mod_eq_of_lt (by omega : q < M), nat_emod_toNat_of_lt q M (by omega)]

theorem evalSignedRem_decodeBitsInt {sz x y : Nat} (hsz : ValidScalarBytes sz)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) (hy0 : y ≠ 0)
    (hno_ovf : (Nat.beq x (2 ^ (8 * sz - 1)) && Nat.beq y (2 ^ (8 * sz) - 1)) = false)
    (locals : List LocalSlot) (mem : Memory) :
    let r := Int.tmod (decodeBitsInt true sz x) (decodeBitsInt true sz y)
    canRepresentInt true sz r = true ∧
      evalSignedRem x y sz locals mem =
        .ok (.scalar ⟨(r % (2 : Int) ^ (8 * sz)).toNat, sz⟩) locals mem := by
  dsimp only
  obtain ⟨hM, hH⟩ := two_pow_byte_split hsz
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  have hcond : (decide (x = 2 ^ (8 * sz - 1)) && decide (y = 2 ^ (8 * sz) - 1)) = false := by
    rw [← nat_beq_eq_decide, ← nat_beq_eq_decide]; exact hno_ovf
  simp only [evalSignedRem, scalarModulus_eq_two_pow, Nat.mul_eq, Nat.sub_eq,
    Nat.mul_comm sz 8, scalarPow2_eq_two_pow, wrapScalarBits_eq_mod,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    isSignedNegative_eq hsz hx, isSignedNegative_eq hsz hy,
    nat_beq_eq_decide, hcond, nat_mod_eq_mod, canRepresentInt_signed sz,
    decodeBitsInt, ↓reduceIte]
  rw [hp]
  generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy ⊢
  generalize 2 ^ (8 * sz) = M at hM hx hy ⊢
  by_cases hxH : x < H <;> by_cases hyH : y < H
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
      decide_eq_false (by omega : ¬(H ≤ y))]
    rw [tmod_nat_nat]
    have hrH : x % y < H := Nat.lt_trans (Nat.mod_lt x (by omega)) hyH
    generalize x % y = r at hrH ⊢
    refine ⟨decide_eq_true (by omega), ?_⟩
    by_cases hr0 : r = 0
    · subst hr0; simp
    · rw [decide_eq_false hr0]; dsimp only
      rw [Nat.mod_eq_of_lt (by omega : r < M), nat_emod_toNat_of_lt r M (by omega)]
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
      decide_eq_true (by omega : H ≤ y)]
    have hy' : (y : Int) - (M : Int) = -((M - y : Nat) : Int) := by omega
    rw [hy', tmod_nat_neg x (M - y) (by omega)]
    have hrH : x % (M - y) < H := Nat.lt_of_le_of_lt (Nat.mod_le x (M - y)) hxH
    generalize x % (M - y) = r at hrH ⊢
    refine ⟨decide_eq_true (by omega), ?_⟩
    by_cases hr0 : r = 0
    · subst hr0; simp
    · rw [decide_eq_false hr0]; dsimp only
      rw [Nat.mod_eq_of_lt (by omega : r < M), nat_emod_toNat_of_lt r M (by omega)]
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_true (by omega : H ≤ x),
      decide_eq_false (by omega : ¬(H ≤ y))]
    have hx' : (x : Int) - (M : Int) = -((M - x : Nat) : Int) := by omega
    rw [hx', tmod_neg_nat (M - x) y (by omega) hy0]
    have hrH : (M - x) % y < H := Nat.lt_trans (Nat.mod_lt _ (by omega)) hyH
    generalize (M - x) % y = r at hrH ⊢
    refine ⟨decide_eq_true (by omega), ?_⟩
    by_cases hr0 : r = 0
    · subst hr0; simp
    · rw [decide_eq_false hr0]; dsimp only
      rw [Nat.mod_eq_of_lt (by omega : M - r < M),
        neg_nat_emod_toNat r M (by omega) (by omega)]
  · simp only [hxH, hyH, ↓reduceIte, decide_eq_true (by omega : H ≤ x),
      decide_eq_true (by omega : H ≤ y)]
    have hx' : (x : Int) - (M : Int) = -((M - x : Nat) : Int) := by omega
    have hy' : (y : Int) - (M : Int) = -((M - y : Nat) : Int) := by omega
    rw [hx', hy', tmod_neg_neg (M - x) (M - y) (by omega) (by omega)]
    have hrH : (M - x) % (M - y) ≤ H :=
      Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))
    generalize (M - x) % (M - y) = r at hrH ⊢
    refine ⟨decide_eq_true (by omega), ?_⟩
    by_cases hr0 : r = 0
    · subst hr0; simp
    · rw [decide_eq_false hr0]; dsimp only
      rw [Nat.mod_eq_of_lt (by omega : M - r < M),
        neg_nat_emod_toNat r M (by omega) (by omega)]

theorem integerOps_binary_sameType_eq
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes)
    (kind : Miri.MIR.IntegerKind) (op : Miri.MIR.BinOp)
    (hsh : (op == .Shl || op == .ShlUnchecked || op == .Shr || op == .ShrUnchecked) = false) :
    Miri.Interpreter.IntegerOps.binary op
      ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
      ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ =
      (let l := decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits
       let r := decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits
       let type : Miri.Interpreter.IntegerType := ⟨translateSizeBytes sc₁.sizeBytes, kind⟩
       match op with
       | .Eq => .ok (.boolean (l == r))
       | .Ne => .ok (.boolean (l != r))
       | .Lt => .ok (.boolean (l < r))
       | .Le => .ok (.boolean (l ≤ r))
       | .Gt => .ok (.boolean (l > r))
       | .Ge => .ok (.boolean (l ≥ r))
       | .Cmp => .ok (.ordering (compare l r))
       | .BitAnd | .BitOr | .BitXor =>
           do
             let lb ← msc₁.toUInt type.size |>.mapError .scalar
             let rb ← msc₂.toUInt type.size |>.mapError .scalar
             let bits := match op with
               | .BitAnd => lb &&& rb
               | .BitOr => lb ||| rb
               | _ => lb ^^^ rb
             let (value, _) ← Miri.Memory.ScalarInt.truncateFromUInt bits type.size |>.mapError .scalar
             return .scalar value
       | _ => arithmeticInt op l r type) := by
  rw [integerOps_binary_eq hrel₁ hrel₂ kind kind op]
  dsimp only
  rw [← hsz_eq, bne_self_eq_false]
  cases op <;> (try cases hsh) <;> rfl

theorem arithmeticInt_nonDivRem_eq (op : Miri.MIR.BinOp) (l r : Int)
    (sz : Nat) (kind : Miri.MIR.IntegerKind)
    (hdiv : (op == .Div) = false) (hrem : (op == .Rem) = false) :
    arithmeticInt op l r ⟨translateSizeBytes sz, kind⟩ =
      (do
        let result ← match op with
          | .Add | .AddUnchecked | .AddWithOverflow => pure (l + r)
          | .Sub | .SubUnchecked | .SubWithOverflow => pure (l - r)
          | .Mul | .MulUnchecked | .MulWithOverflow => pure (l * r)
          | .Div => pure (Int.tdiv l r)
          | .Rem => pure (Int.tmod l r)
          | _ => throw (.invalidBinaryOperator op)
        let hostOverflow := if kind.signed then
            result < -(2 ^ 127 : Int) || result ≥ (2 ^ 127 : Int)
          else result < 0 || result ≥ (2 ^ 128 : Int)
        let (value, lossy) ← truncateInt result ⟨translateSizeBytes sz, kind⟩
        scalarResultInt op value (hostOverflow || lossy)) := by
  unfold arithmeticInt Miri.Interpreter.IntegerType.signed
  rw [hdiv, hrem]
  cases (r == 0) <;> cases kind.signed <;> rfl

theorem arithmeticInt_div_eq (l r : Int) (sz : Nat) (kind : Miri.MIR.IntegerKind) :
    arithmeticInt .Div l r ⟨translateSizeBytes sz, kind⟩ =
      (if r == 0 then
        .error (.undefinedBehavior .divisionByZero)
      else if kind.signed then
        match (translateSizeBytes sz).signedIntMin with
        | .error e => .error (.scalar (.sizeError e))
        | .ok min =>
            if l == min && r == -1 then
              .error (.undefinedBehavior .divisionOverflow)
            else do
              let (value, _) ← truncateInt (Int.tdiv l r) ⟨translateSizeBytes sz, kind⟩
              return .scalar value
      else do
        let (value, _) ← truncateInt (Int.tdiv l r) ⟨translateSizeBytes sz, kind⟩
        return .scalar value) := by
  unfold arithmeticInt scalarResultInt Miri.Interpreter.IntegerType.signed
    Miri.MIR.BinOp.isUnchecked Miri.MIR.BinOp.isOverflowing
  simp only [Bool.and_false]
  cases (r == 0) <;> cases kind.signed <;>
    rcases (translateSizeBytes sz).signedIntMin with e | min <;>
    (try cases (l == min && r == -1)) <;>
    rfl

theorem arithmeticInt_rem_eq (l r : Int) (sz : Nat) (kind : Miri.MIR.IntegerKind) :
    arithmeticInt .Rem l r ⟨translateSizeBytes sz, kind⟩ =
      (if r == 0 then
        .error (.undefinedBehavior .remainderByZero)
      else if kind.signed then
        match (translateSizeBytes sz).signedIntMin with
        | .error e => .error (.scalar (.sizeError e))
        | .ok min =>
            if l == min && r == -1 then
              .error (.undefinedBehavior .remainderOverflow)
            else do
              let (value, _) ← truncateInt (Int.tmod l r) ⟨translateSizeBytes sz, kind⟩
              return .scalar value
      else do
        let (value, _) ← truncateInt (Int.tmod l r) ⟨translateSizeBytes sz, kind⟩
        return .scalar value) := by
  unfold arithmeticInt scalarResultInt Miri.Interpreter.IntegerType.signed
    Miri.MIR.BinOp.isUnchecked Miri.MIR.BinOp.isOverflowing
  simp only [Bool.and_false]
  cases (r == 0) <;> cases kind.signed <;>
    rcases (translateSizeBytes sz).signedIntMin with e | min <;>
    (try cases (l == min && r == -1)) <;>
    rfl

theorem signedLt_eq {sz x y : Nat} (hsz : ValidScalarBytes sz)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    signedLt x y sz = decide (decodeBitsInt true sz x < decodeBitsInt true sz y) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split hsz
  simp only [signedLt, scalarModulus_eq_two_pow, wrapScalarBits_eq_mod,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    isSignedNegative_eq hsz hx, isSignedNegative_eq hsz hy,
    nat_ble_eq_decide, decodeBitsInt, ↓reduceIte]
  generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy ⊢
  generalize 2 ^ (8 * sz) = M at hM hx hy ⊢
  apply Bool.eq_iff_iff.mpr
  by_cases hxH : H ≤ x <;> by_cases hyH : H ≤ y <;>
    simp [hxH, hyH, show x < H ↔ ¬(H ≤ x) by omega, show y < H ↔ ¬(H ≤ y) by omega] <;>
    omega

theorem signedLe_eq {sz x y : Nat} (hsz : ValidScalarBytes sz)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    signedLe x y sz = decide (decodeBitsInt true sz x ≤ decodeBitsInt true sz y) := by
  unfold signedLe
  rw [signedLt_eq hsz hy hx]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  omega

/-- Predicate for wrapping, unchecked, checked (`WithOverflow`), division/remainder,
and comparison binary operators covered by `evalBinOp_arithmetic_simulation`. -/
def IsArithmeticOrCmpBinOp (op : MirAst.BinOp) : Prop :=
  op = .add ∨ op = .sub ∨ op = .mul ∨
  op = .addUnchecked ∨ op = .subUnchecked ∨ op = .mulUnchecked ∨
  op = .addWithOverflow ∨ op = .subWithOverflow ∨ op = .mulWithOverflow ∨
  op = .div ∨ op = .rem ∨
  op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge

/-- Theorem 1 (`LM-1.1`): Arithmetic (`Add`, `Sub`, `Mul`), unchecked (`AddUnchecked`,
`SubUnchecked`, `MulUnchecked`), checked (`AddWithOverflow`, `SubWithOverflow`,
`MulWithOverflow`), division/remainder (`Div`, `Rem`), and comparison (`Eq`, `Ne`,
`Lt`, `Le`, `Gt`, `Ge`) binary operator simulation between Anneal's
`MirSemantics.evalScalarBinOp` and `lean-miri`'s `Miri.Interpreter.IntegerOps.binary`
across all 10 integer types (`u8`, `u16`, `u32`, `u64`, `u128`, `usize`,
`i8`, `i16`, `i32`, `i64`, `i128`, `isize`). -/
theorem evalBinOp_arithmetic_simulation
    {op : MirAst.BinOp} {mop : Miri.MIR.BinOp}
    (harith : IsArithmeticOrCmpBinOp op)
    (hop : translateBinOp op = some mop)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes)
    (kind : Miri.MIR.IntegerKind)
    (locals : List LocalSlot) (mem : Memory) :
    IntegerBinOpResultRel locals mem
      (evalScalarBinOp op sc₁ sc₂ locals mem kind.signed)
      (Miri.Interpreter.IntegerOps.binary mop
        ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
        ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩) := by
  have hbeq0 := hrel₁.beq_sizeBytes_zero
  have hbeq_eq : Nat.beq sc₁.sizeBytes sc₂.sizeBytes = true := by
    rw [hsz_eq, Nat.beq_refl]
  have hx : sc₁.bits < 2 ^ (8 * sc₁.sizeBytes) := by
    rw [← scalarModulus_eq_two_pow]; exact hrel₁.canonical
  have hy : sc₂.bits < 2 ^ (8 * sc₁.sizeBytes) := by
    rw [hsz_eq, ← scalarModulus_eq_two_pow]; exact hrel₂.canonical
  have hxMod : wrapScalarBits sc₁.bits (scalarModulus sc₁.sizeBytes) = sc₁.bits :=
    hrel₁.wrapScalarBits_self
  have hyMod : wrapScalarBits sc₂.bits (scalarModulus sc₁.sizeBytes) = sc₂.bits := by
    rw [hsz_eq]; exact hrel₂.wrapScalarBits_self
  rcases harith with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- .add
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .Add rfl]
    dsimp only
    rw [arithmeticInt_nonDivRem_eq .Add _ _ _ kind rfl rfl]
    obtain ⟨msc', lossy, htr, hrel', _⟩ :=
      truncateInt_spec hrel₁.validBytes kind
        (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits +
          decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits)
    rw [← wrap_add_decodeBitsInt kind.signed hx hy] at hrel'
    simp only [evalScalarBinOp, hbeq0, hbeq_eq, Nat.add_eq,
      scalarResultInt, htr, Miri.MIR.BinOp.isUnchecked,
      Miri.MIR.BinOp.isOverflowing, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure]
    exact IntegerBinOpResultRel.scalar _ msc' hrel'
  · -- .sub
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .Sub rfl]
    dsimp only
    rw [arithmeticInt_nonDivRem_eq .Sub _ _ _ kind rfl rfl]
    obtain ⟨msc', lossy, htr, hrel', _⟩ :=
      truncateInt_spec hrel₁.validBytes kind
        (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits -
          decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits)
    have hsub := wrap_sub_decodeBitsInt kind.signed hx hy
    dsimp only at hsub
    rw [← hsub] at hrel'
    simp only [evalScalarBinOp, hbeq0, hbeq_eq, Nat.sub_eq, Nat.add_eq,
      scalarResultInt, htr, Miri.MIR.BinOp.isUnchecked,
      Miri.MIR.BinOp.isOverflowing, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure]
    cases hble : Nat.ble sc₂.bits sc₁.bits <;>
      simp only [hble] at hrel' ⊢ <;>
      exact IntegerBinOpResultRel.scalar _ msc' hrel'
  · -- .mul
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .Mul rfl]
    dsimp only
    rw [arithmeticInt_nonDivRem_eq .Mul _ _ _ kind rfl rfl]
    obtain ⟨msc', lossy, htr, hrel', _⟩ :=
      truncateInt_spec hrel₁.validBytes kind
        (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits *
          decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits)
    rw [← wrap_mul_decodeBitsInt kind.signed hx hy] at hrel'
    simp only [evalScalarBinOp, hbeq0, hbeq_eq, Nat.mul_eq,
      scalarResultInt, htr, Miri.MIR.BinOp.isUnchecked,
      Miri.MIR.BinOp.isOverflowing, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure]
    exact IntegerBinOpResultRel.scalar _ msc' hrel'
  · -- .addUnchecked
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .AddUnchecked rfl]
    dsimp only
    rw [arithmeticInt_nonDivRem_eq .AddUnchecked _ _ _ kind rfl rfl]
    obtain ⟨msc', lossy, htr, hrel', hovf⟩ :=
      truncateInt_spec hrel₁.validBytes kind
        (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits +
          decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits)
    rw [← wrap_add_decodeBitsInt kind.signed hx hy] at hrel'
    simp only [evalScalarBinOp, hbeq0, hbeq_eq, Nat.add_eq,
      scalarResultInt, htr,
      Miri.MIR.BinOp.isUnchecked, Miri.MIR.BinOp.isOverflowing, Bool.and_true,
      Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rw [hovf]
    cases hs : kind.signed
    · rw [← unsignedOverflowAdd_eq]
      cases hble : Nat.ble (scalarModulus sc₁.sizeBytes) (sc₁.bits + sc₂.bits)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hwrap : wrapScalarBits (sc₁.bits + sc₂.bits) (scalarModulus sc₁.sizeBytes) =
            sc₁.bits + sc₂.bits := by
          unfold wrapScalarBits; rw [hble]
        rw [hwrap] at hrel'
        exact IntegerBinOpResultRel.scalar _ msc' hrel'
      · simp only [↓reduceIte]
        exact IntegerBinOpResultRel.ub _
    · rw [← signedOverflowAdd_eq hrel₁.validBytes hx hy]
      cases hov : signedOverflowAdd sc₁.bits sc₂.bits sc₁.sizeBytes
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact IntegerBinOpResultRel.scalar _ msc' hrel'
      · simp only [↓reduceIte]
        exact IntegerBinOpResultRel.ub _
  · -- .subUnchecked
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .SubUnchecked rfl]
    dsimp only
    rw [arithmeticInt_nonDivRem_eq .SubUnchecked _ _ _ kind rfl rfl]
    obtain ⟨msc', lossy, htr, hrel', hovf⟩ :=
      truncateInt_spec hrel₁.validBytes kind
        (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits -
          decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits)
    have hsub := wrap_sub_decodeBitsInt kind.signed hx hy
    dsimp only at hsub
    rw [← hsub, hxMod, hyMod] at hrel'
    simp only [evalScalarBinOp, hbeq0, hbeq_eq, Nat.sub_eq, Nat.add_eq, hxMod, hyMod,
      scalarResultInt, htr,
      Miri.MIR.BinOp.isUnchecked, Miri.MIR.BinOp.isOverflowing, Bool.and_true,
      Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rw [hovf]
    cases hs : kind.signed
    · rw [← unsignedOverflowSub_eq hx]
      cases hble : Nat.ble sc₂.bits sc₁.bits
      · simp only [Bool.not_false, ↓reduceIte]
        exact IntegerBinOpResultRel.ub _
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have hlt_diff : sc₁.bits - sc₂.bits < scalarModulus sc₁.sizeBytes := by
          have := hrel₁.canonical; omega
        have hble_diff : Nat.ble (scalarModulus sc₁.sizeBytes) (sc₁.bits - sc₂.bits) = false := by
          rw [nat_ble_eq_decide, decide_eq_false (by omega)]
        rw [hble_diff]
        simp only [hble, wrapScalarBits, hble_diff] at hrel'
        exact IntegerBinOpResultRel.scalar _ msc' hrel'
    · rw [← signedOverflowSub_eq hrel₁.validBytes hx hy]
      cases hov : signedOverflowSub sc₁.bits sc₂.bits sc₁.sizeBytes
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hble : Nat.ble sc₂.bits sc₁.bits <;>
          simp only [hble] at hrel' ⊢ <;>
          exact IntegerBinOpResultRel.scalar _ msc' hrel'
      · simp only [↓reduceIte]
        exact IntegerBinOpResultRel.ub _
  · -- .mulUnchecked
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .MulUnchecked rfl]
    dsimp only
    rw [arithmeticInt_nonDivRem_eq .MulUnchecked _ _ _ kind rfl rfl]
    obtain ⟨msc', lossy, htr, hrel', hovf⟩ :=
      truncateInt_spec hrel₁.validBytes kind
        (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits *
          decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits)
    rw [← wrap_mul_decodeBitsInt kind.signed hx hy] at hrel'
    simp only [evalScalarBinOp, hbeq0, hbeq_eq, Nat.mul_eq,
      scalarResultInt, htr,
      Miri.MIR.BinOp.isUnchecked, Miri.MIR.BinOp.isOverflowing, Bool.and_true,
      Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rw [hovf]
    cases hs : kind.signed
    · rw [← unsignedOverflowMul_eq]
      cases hble : Nat.ble (scalarModulus sc₁.sizeBytes) (sc₁.bits * sc₂.bits)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hwrap : wrapScalarBits (sc₁.bits * sc₂.bits) (scalarModulus sc₁.sizeBytes) =
            sc₁.bits * sc₂.bits := by
          unfold wrapScalarBits; rw [hble]
        rw [hwrap] at hrel'
        exact IntegerBinOpResultRel.scalar _ msc' hrel'
      · simp only [↓reduceIte]
        exact IntegerBinOpResultRel.ub _
    · rw [← signedOverflowMul_eq hrel₁.validBytes hx hy]
      cases hov : signedOverflowMul sc₁.bits sc₂.bits sc₁.sizeBytes
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact IntegerBinOpResultRel.scalar _ msc' hrel'
      · simp only [↓reduceIte]
        exact IntegerBinOpResultRel.ub _
  · -- .addWithOverflow
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .AddWithOverflow rfl]
    dsimp only
    rw [arithmeticInt_nonDivRem_eq .AddWithOverflow _ _ _ kind rfl rfl]
    obtain ⟨msc', lossy, htr, hrel', hovf⟩ :=
      truncateInt_spec hrel₁.validBytes kind
        (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits +
          decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits)
    rw [← wrap_add_decodeBitsInt kind.signed hx hy] at hrel'
    simp only [evalScalarBinOp, hbeq0, hbeq_eq, Nat.add_eq,
      scalarResultInt, htr,
      Miri.MIR.BinOp.isUnchecked, Miri.MIR.BinOp.isOverflowing, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rw [hovf]
    cases hs : kind.signed
    · rw [← unsignedOverflowAdd_eq]
      cases Nat.ble (scalarModulus sc₁.sizeBytes) (sc₁.bits + sc₂.bits)
      · exact IntegerBinOpResultRel.withOverflow _ msc' false hrel'
      · exact IntegerBinOpResultRel.withOverflow _ msc' true hrel'
    · rw [← signedOverflowAdd_eq hrel₁.validBytes hx hy]
      cases signedOverflowAdd sc₁.bits sc₂.bits sc₁.sizeBytes
      · exact IntegerBinOpResultRel.withOverflow _ msc' false hrel'
      · exact IntegerBinOpResultRel.withOverflow _ msc' true hrel'
  · -- .subWithOverflow
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .SubWithOverflow rfl]
    dsimp only
    rw [arithmeticInt_nonDivRem_eq .SubWithOverflow _ _ _ kind rfl rfl]
    obtain ⟨msc', lossy, htr, hrel', hovf⟩ :=
      truncateInt_spec hrel₁.validBytes kind
        (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits -
          decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits)
    have hsub := wrap_sub_decodeBitsInt kind.signed hx hy
    dsimp only at hsub
    rw [← hsub, hxMod, hyMod] at hrel'
    simp only [evalScalarBinOp, hbeq0, hbeq_eq, Nat.sub_eq, Nat.add_eq, hxMod, hyMod,
      scalarResultInt, htr,
      Miri.MIR.BinOp.isUnchecked, Miri.MIR.BinOp.isOverflowing, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rw [hovf]
    cases hs : kind.signed
    · rw [← unsignedOverflowSub_eq hx]
      cases hble : Nat.ble sc₂.bits sc₁.bits <;>
        simp only [hble, Bool.not_true, Bool.not_false] at hrel' ⊢
      · exact IntegerBinOpResultRel.withOverflow _ msc' true hrel'
      · exact IntegerBinOpResultRel.withOverflow _ msc' false hrel'
    · rw [← signedOverflowSub_eq hrel₁.validBytes hx hy]
      cases hble : Nat.ble sc₂.bits sc₁.bits <;>
        cases signedOverflowSub sc₁.bits sc₂.bits sc₁.sizeBytes <;>
        simp only [hble] at hrel' ⊢
      · exact IntegerBinOpResultRel.withOverflow _ msc' false hrel'
      · exact IntegerBinOpResultRel.withOverflow _ msc' true hrel'
      · exact IntegerBinOpResultRel.withOverflow _ msc' false hrel'
      · exact IntegerBinOpResultRel.withOverflow _ msc' true hrel'
  · -- .mulWithOverflow
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .MulWithOverflow rfl]
    dsimp only
    rw [arithmeticInt_nonDivRem_eq .MulWithOverflow _ _ _ kind rfl rfl]
    obtain ⟨msc', lossy, htr, hrel', hovf⟩ :=
      truncateInt_spec hrel₁.validBytes kind
        (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits *
          decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits)
    rw [← wrap_mul_decodeBitsInt kind.signed hx hy] at hrel'
    simp only [evalScalarBinOp, hbeq0, hbeq_eq, Nat.mul_eq,
      scalarResultInt, htr,
      Miri.MIR.BinOp.isUnchecked, Miri.MIR.BinOp.isOverflowing, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rw [hovf]
    cases hs : kind.signed
    · rw [← unsignedOverflowMul_eq]
      cases Nat.ble (scalarModulus sc₁.sizeBytes) (sc₁.bits * sc₂.bits)
      · exact IntegerBinOpResultRel.withOverflow _ msc' false hrel'
      · exact IntegerBinOpResultRel.withOverflow _ msc' true hrel'
    · rw [← signedOverflowMul_eq hrel₁.validBytes hx hy]
      cases signedOverflowMul sc₁.bits sc₂.bits sc₁.sizeBytes
      · exact IntegerBinOpResultRel.withOverflow _ msc' false hrel'
      · exact IntegerBinOpResultRel.withOverflow _ msc' true hrel'
  · -- .div
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .Div rfl]
    dsimp only
    rw [arithmeticInt_div_eq]
    have hzero_beq : (decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits == 0) =
        Nat.beq sc₂.bits 0 := by
      rw [nat_beq_eq_decide]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact decodeBitsInt_eq_zero_iff hrel₁.validBytes hy
    simp only [evalScalarBinOp, hbeq0, hbeq_eq,
      hzero_beq, bind, Except.bind]
    cases hy0 : Nat.beq sc₂.bits 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hy_ne : sc₂.bits ≠ 0 := by
        rw [nat_beq_eq_decide, decide_eq_false_iff_not] at hy0; exact hy0
      cases hs : kind.signed
      · simp only [Bool.false_eq_true, ↓reduceIte, nat_div_eq_div]
        obtain ⟨msc', lossy, htr, hrel', _⟩ :=
          truncateInt_spec hrel₁.validBytes kind
            (Int.tdiv (decodeBitsInt false sc₁.sizeBytes sc₁.bits)
              (decodeBitsInt false sc₁.sizeBytes sc₂.bits))
        have hlt_q : sc₁.bits / sc₂.bits < 2 ^ (8 * sc₁.sizeBytes) :=
          Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
        have hq_eq : (Int.tdiv (decodeBitsInt false sc₁.sizeBytes sc₁.bits)
            (decodeBitsInt false sc₁.sizeBytes sc₂.bits) % (2 : Int) ^ (8 * sc₁.sizeBytes)).toNat =
            wrapScalarBits (sc₁.bits / sc₂.bits) (scalarModulus sc₁.sizeBytes) := by
          simp only [decodeBitsInt, Bool.false_eq_true, ↓reduceIte, tdiv_nat_nat,
            wrapScalarBits_eq_mod, scalarModulus_eq_two_pow, Nat.mod_eq_of_lt hlt_q]
          rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hlt_q), Int.toNat_natCast]
        rw [hq_eq] at hrel'
        simp only [htr, pure, Except.pure]
        exact IntegerBinOpResultRel.scalar _ msc' hrel'
      · simp only [↓reduceIte,
          translateSizeBytes_signedIntMin_eq hrel₁.validBytes,
          decodeBitsInt_signed_min_iff hrel₁.validBytes,
          decodeBitsInt_signed_neg_one_iff hrel₁.validBytes]
        cases hovf : (Nat.beq sc₁.bits (2 ^ (8 * sc₁.sizeBytes - 1)) &&
            Nat.beq sc₂.bits (2 ^ (8 * sc₁.sizeBytes) - 1))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          obtain ⟨_, hdiv_eq⟩ :=
            evalSignedDiv_decodeBitsInt hrel₁.validBytes hx hy hy_ne hovf locals mem
          obtain ⟨msc', lossy, htr, hrel', _⟩ :=
            truncateInt_spec hrel₁.validBytes kind
              (Int.tdiv (decodeBitsInt true sc₁.sizeBytes sc₁.bits)
                (decodeBitsInt true sc₁.sizeBytes sc₂.bits))
          simp only [hdiv_eq, htr, pure, Except.pure]
          exact IntegerBinOpResultRel.scalar _ msc' hrel'
        · simp only [↓reduceIte]
          have hdiv_ub : evalSignedDiv sc₁.bits sc₂.bits sc₁.sizeBytes locals mem = .ub := by
            simp only [evalSignedDiv, scalarModulus_eq_two_pow, Nat.mul_eq, Nat.sub_eq,
              Nat.mul_comm sc₁.sizeBytes 8, scalarPow2_eq_two_pow, wrapScalarBits_eq_mod,
              Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, hovf]
          rw [hdiv_ub]
          exact IntegerBinOpResultRel.ub _
    · simp only [↓reduceIte]
      exact IntegerBinOpResultRel.ub _
  · -- .rem
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .Rem rfl]
    dsimp only
    rw [arithmeticInt_rem_eq]
    have hzero_beq : (decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits == 0) =
        Nat.beq sc₂.bits 0 := by
      rw [nat_beq_eq_decide]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact decodeBitsInt_eq_zero_iff hrel₁.validBytes hy
    simp only [evalScalarBinOp, hbeq0, hbeq_eq,
      hzero_beq, bind, Except.bind]
    cases hy0 : Nat.beq sc₂.bits 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hy_ne : sc₂.bits ≠ 0 := by
        rw [nat_beq_eq_decide, decide_eq_false_iff_not] at hy0; exact hy0
      cases hs : kind.signed
      · simp only [Bool.false_eq_true, ↓reduceIte, nat_mod_eq_mod]
        obtain ⟨msc', lossy, htr, hrel', _⟩ :=
          truncateInt_spec hrel₁.validBytes kind
            (Int.tmod (decodeBitsInt false sc₁.sizeBytes sc₁.bits)
              (decodeBitsInt false sc₁.sizeBytes sc₂.bits))
        have hlt_r : sc₁.bits % sc₂.bits < 2 ^ (8 * sc₁.sizeBytes) :=
          Nat.lt_trans (Nat.mod_lt _ (by omega)) hy
        have hr_eq : (Int.tmod (decodeBitsInt false sc₁.sizeBytes sc₁.bits)
            (decodeBitsInt false sc₁.sizeBytes sc₂.bits) % (2 : Int) ^ (8 * sc₁.sizeBytes)).toNat =
            wrapScalarBits (sc₁.bits % sc₂.bits) (scalarModulus sc₁.sizeBytes) := by
          simp only [decodeBitsInt, Bool.false_eq_true, ↓reduceIte, tmod_nat_nat,
            wrapScalarBits_eq_mod, scalarModulus_eq_two_pow, Nat.mod_eq_of_lt hlt_r]
          rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hlt_r), Int.toNat_natCast]
        rw [hr_eq] at hrel'
        simp only [htr, pure, Except.pure]
        exact IntegerBinOpResultRel.scalar _ msc' hrel'
      · simp only [↓reduceIte,
          translateSizeBytes_signedIntMin_eq hrel₁.validBytes,
          decodeBitsInt_signed_min_iff hrel₁.validBytes,
          decodeBitsInt_signed_neg_one_iff hrel₁.validBytes]
        cases hovf : (Nat.beq sc₁.bits (2 ^ (8 * sc₁.sizeBytes - 1)) &&
            Nat.beq sc₂.bits (2 ^ (8 * sc₁.sizeBytes) - 1))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          obtain ⟨_, hrem_eq⟩ :=
            evalSignedRem_decodeBitsInt hrel₁.validBytes hx hy hy_ne hovf locals mem
          obtain ⟨msc', lossy, htr, hrel', _⟩ :=
            truncateInt_spec hrel₁.validBytes kind
              (Int.tmod (decodeBitsInt true sc₁.sizeBytes sc₁.bits)
                (decodeBitsInt true sc₁.sizeBytes sc₂.bits))
          simp only [hrem_eq, htr, pure, Except.pure]
          exact IntegerBinOpResultRel.scalar _ msc' hrel'
        · simp only [↓reduceIte]
          have hrem_ub : evalSignedRem sc₁.bits sc₂.bits sc₁.sizeBytes locals mem = .ub := by
            simp only [evalSignedRem, scalarModulus_eq_two_pow, Nat.mul_eq, Nat.sub_eq,
              Nat.mul_comm sc₁.sizeBytes 8, scalarPow2_eq_two_pow, wrapScalarBits_eq_mod,
              Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, hovf]
          rw [hrem_ub]
          exact IntegerBinOpResultRel.ub _
    · simp only [↓reduceIte]
      exact IntegerBinOpResultRel.ub _
  · -- .eq
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .Eq rfl]
    dsimp only
    have heq_b : (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits ==
        decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits) = Nat.beq sc₁.bits sc₂.bits := by
      rw [nat_beq_eq_decide]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact decodeBitsInt_inj hrel₁.validBytes hx hy
    simp only [evalScalarBinOp, hbeq0, hbeq_eq, heq_b]
    exact IntegerBinOpResultRel.boolean _
  · -- .ne
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .Ne rfl]
    dsimp only
    have hne_b : (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits !=
        decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits) = !Nat.beq sc₁.bits sc₂.bits := by
      rw [nat_beq_eq_decide]
      apply Bool.eq_iff_iff.mpr
      simp only [bne_iff_ne, Ne, Bool.not_eq_true', decide_eq_false_iff_not]
      exact not_congr (decodeBitsInt_inj hrel₁.validBytes hx hy)
    simp only [evalScalarBinOp, hbeq0, hbeq_eq, hne_b]
    exact IntegerBinOpResultRel.boolean _
  · -- .lt
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .Lt rfl]
    dsimp only
    simp only [evalScalarBinOp, hbeq0, hbeq_eq]
    cases hs : kind.signed
    · dsimp only
      have hlt_b : (!Nat.ble sc₂.bits sc₁.bits) =
          decide (decodeBitsInt false sc₁.sizeBytes sc₁.bits <
            decodeBitsInt false sc₁.sizeBytes sc₂.bits) := by
        rw [nat_ble_eq_decide]
        unfold decodeBitsInt
        simp only [Bool.false_eq_true, ↓reduceIte]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
        omega
      rw [hlt_b]
      exact IntegerBinOpResultRel.boolean _
    · dsimp only
      rw [signedLt_eq hrel₁.validBytes hx hy]
      exact IntegerBinOpResultRel.boolean _
  · -- .le
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .Le rfl]
    dsimp only
    simp only [evalScalarBinOp, hbeq0, hbeq_eq]
    cases hs : kind.signed
    · dsimp only
      have hle_b : Nat.ble sc₁.bits sc₂.bits =
          decide (decodeBitsInt false sc₁.sizeBytes sc₁.bits ≤
            decodeBitsInt false sc₁.sizeBytes sc₂.bits) := by
        rw [nat_ble_eq_decide]
        unfold decodeBitsInt
        simp only [Bool.false_eq_true, ↓reduceIte]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        omega
      rw [hle_b]
      exact IntegerBinOpResultRel.boolean _
    · dsimp only
      rw [signedLe_eq hrel₁.validBytes hx hy]
      exact IntegerBinOpResultRel.boolean _
  · -- .gt
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .Gt rfl]
    dsimp only
    simp only [evalScalarBinOp, hbeq0, hbeq_eq]
    cases hs : kind.signed
    · dsimp only
      have hgt_b : (!Nat.ble sc₁.bits sc₂.bits) =
          decide (decodeBitsInt false sc₁.sizeBytes sc₁.bits >
            decodeBitsInt false sc₁.sizeBytes sc₂.bits) := by
        rw [nat_ble_eq_decide]
        unfold decodeBitsInt
        simp only [Bool.false_eq_true, ↓reduceIte]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
        omega
      rw [hgt_b]
      exact IntegerBinOpResultRel.boolean _
    · dsimp only
      rw [signedLt_eq hrel₁.validBytes hy hx]
      exact IntegerBinOpResultRel.boolean _
  · -- .ge
    simp only [translateBinOp, Option.some.injEq] at hop; subst hop
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .Ge rfl]
    dsimp only
    simp only [evalScalarBinOp, hbeq0, hbeq_eq]
    cases hs : kind.signed
    · dsimp only
      have hge_b : Nat.ble sc₂.bits sc₁.bits =
          decide (decodeBitsInt false sc₁.sizeBytes sc₁.bits ≥
            decodeBitsInt false sc₁.sizeBytes sc₂.bits) := by
        rw [nat_ble_eq_decide]
        unfold decodeBitsInt
        simp only [Bool.false_eq_true, ↓reduceIte]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        omega
      rw [hge_b]
      exact IntegerBinOpResultRel.boolean _
    · dsimp only
      rw [signedLe_eq hrel₁.validBytes hy hx]
      exact IntegerBinOpResultRel.boolean _

/-! ## 5. Statement & Terminator Small-Step Simulation (`step_assign_scalar_simulation`, `step_terminator_goto_return_simulation`) -/

/-- Only memory-backed locals own an allocation, so `deallocate_local` of any
other local value is a no-op. -/
theorem annealLocalStorageHooks_deallocateLocal_of_not_indirect
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (st : AnnealMemory)
    (v : Miri.Interpreter.LocalValue AnnealProv)
    (hv : ∀ mp, v ≠ .live (.indirect mp)) :
    Miri.Interpreter.Frame.deallocateLocal (annealLocalStorageHooks localDecls layouts) st v =
      ⟨st, .ok ()⟩ := by
  unfold Miri.Interpreter.Frame.deallocateLocal
  cases v with
  | dead => rfl
  | live op =>
    cases op with
    | immediate _ => rfl
    | indirect mp => exact absurd rfl (hv mp)

/-- As in `lean-miri` (and rustc), `StorageDead` of the return place `_0` fails
with `StackError.cannotMakeReturnPlaceDead`, which is not undefined behavior. -/
theorem annealStepHooks_storageDead_returnPlace
    {localDecls : List LocalDecl} {layouts : LayoutTable} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame]) :
    (annealStepHooks localDecls layouts).storageDead () 0 m =
      (m, .error (.stack .cannotMakeReturnPlaceDead)) := by
  simp only [annealStepHooks, annealRunFrameStorage, stack_currentFrame?_singleton m.stack topFrame hframes]
  simp only [Miri.Interpreter.Frame.storageDead, Id.run, hframes]
  rcases m with ⟨⟨frames⟩, ⟨mem, addr, bt⟩⟩
  dsimp only at hframes
  subst hframes
  rfl

theorem FrameRel.lookup_local
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRel body mach af mf) {i : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls i = some decl) :
    ∃ (slot : LocalSlot) (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
      (_ : i < af.locals.length) (hlt_mf : i < mf.locals.size),
      get? af.locals i = some slot ∧
      mf.locals[i]? = some mls ∧
      mf.locals[i]'hlt_mf = mls ∧
      LocalRel mach decl body.layouts slot mls := by
  rw [get?_eq_getElem?] at hdecl
  obtain ⟨hlt_d, _⟩ := List.getElem?_eq_some_iff.mp hdecl
  have hlt_af : i < af.locals.length := by rw [hrel.af_locals_len]; exact hlt_d
  have hlt_mf : i < mf.locals.size := by rw [hrel.mf_locals_size]; exact hlt_d
  have hslot : get? af.locals i = some (af.locals[i]'hlt_af) := by
    rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt_af]
  have hmls : mf.locals[i]? = some (mf.locals[i]'hlt_mf) :=
    Array.getElem?_eq_getElem hlt_mf
  have hdecl' : get? body.localDecls i = some decl := hdecl
  exact ⟨af.locals[i]'hlt_af, mf.locals[i]'hlt_mf, hlt_af, hlt_mf, hslot, hmls, rfl,
    hrel.locals_rel i decl _ _ hdecl' hslot hmls⟩

theorem FrameRel.update_local
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRel body mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot) (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : LocalRel mach decl body.layouts newSlot { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRel body mach
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf } where
  body_eq := hrel.body_eq
  location_eq := hrel.location_eq
  af_locals_len := by rw [List.length_set, hrel.af_locals_len]
  mf_locals_size := by rw [Array.size_set, hrel.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    have hlt_af : idx < af.locals.length := by
      rw [hrel.af_locals_len, ← hrel.mf_locals_size]; exact hlt_mf
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i hmls_i
      have hdecl_eq : decl_i = decl := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
      subst hdecl_eq hslot_i hmls_i
      exact hnew
    · simp only [h_eq, ↓reduceIte] at hslot_i hmls_i
      exact hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i

/-- Predicate characterizing an unprojected local `idx` whose `LocalState` in `mf`
is not an `.indirect` memory allocation (i.e. `.dead` or `.live (.immediate _)`). -/
def IsImmediateFrameLocal
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (idx : Nat) : Prop :=
  ∀ mls, mf.locals[idx]? = some mls → ∀ mp, mls.value ≠ .live (.indirect mp)

theorem IsImmediateFrameLocal.set_immediate
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx j : Nat} (h : IsImmediateFrameLocal mf idx)
    (hlt : j < mf.locals.size) (imm : Miri.Interpreter.Immediate AnnealProv) :
    IsImmediateFrameLocal
      { mf with locals := mf.locals.set j { mf.locals[j]'hlt with value := .live (.immediate imm) } hlt }
      idx := by
  intro mls hmls mp hmp
  rw [Array.getElem?_set] at hmls
  by_cases hj : j = idx
  · simp only [hj, ↓reduceIte, Option.some.injEq] at hmls
    rw [← hmls] at hmp
    cases hmp
  · simp only [hj, ↓reduceIte] at hmls
    exact h mls hmls mp hmp

theorem IsImmediateFrameLocal.set_dead
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx j : Nat} (h : IsImmediateFrameLocal mf idx)
    (hlt : j < mf.locals.size) :
    IsImmediateFrameLocal
      { mf with locals := mf.locals.set j { mf.locals[j]'hlt with value := .dead } hlt }
      idx := by
  intro mls hmls mp hmp
  rw [Array.getElem?_set] at hmls
  by_cases hj : j = idx
  · simp only [hj, ↓reduceIte, Option.some.injEq] at hmls
    rw [← hmls] at hmp
    cases hmp
  · simp only [hj, ↓reduceIte] at hmls
    exact h mls hmls mp hmp

theorem IsImmediateFrameLocal.cache_layout
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx j : Nat} (h : IsImmediateFrameLocal mf idx)
    (hlt : j < mf.locals.size) (lay : Miri.Interpreter.LocalLayout) :
    IsImmediateFrameLocal (cacheFrameLocalLayout mf j hlt lay) idx := by
  intro mls hmls mp hmp
  unfold cacheFrameLocalLayout at hmls
  rw [Array.getElem?_set] at hmls
  by_cases hj : j = idx
  · subst hj
    simp only [↓reduceIte, Option.some.injEq] at hmls
    rw [← hmls] at hmp
    exact h (mf.locals[j]'hlt) (Array.getElem?_eq_getElem hlt) mp hmp
  · simp only [hj, ↓reduceIte] at hmls
    exact h mls hmls mp hmp

theorem LocalRel.cache_layout
    {mach : AnnealMachine}
    {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRel mach decl layouts slot mls) :
    LocalRel mach decl layouts slot { mls with layout := some (translateTy decl.ty layouts) } := by
  have hc : ∀ l ∈ (some (translateTy decl.ty layouts)), l = translateTy decl.ty layouts := by
    intro l hl; exact (Option.some.inj hl).symm
  cases h with
  | dead _ _ => exact .dead _ hc
  | immediate _ imm _ _ hval => exact .immediate _ imm _ hc hval
  | indirect _ mp _ _ hne hmp => exact .indirect _ mp _ hc hne hmp

theorem FrameRel.cache_local_layout
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRel body mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    (hlt_mf : idx < mf.locals.size) :
    FrameRel body mach af
      (cacheFrameLocalLayout mf idx hlt_mf (translateTy decl.ty body.layouts)) where
  body_eq := hrel.body_eq
  location_eq := hrel.location_eq
  af_locals_len := hrel.af_locals_len
  mf_locals_size := by unfold cacheFrameLocalLayout; rw [Array.size_set, hrel.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    unfold cacheFrameLocalLayout at hmls_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, Option.some.injEq] at hmls_i
      rw [hdecl] at hdecl_i
      cases hdecl_i
      cases hmls_i
      have hmls_orig : mf.locals[idx]? = some (mf.locals[idx]'hlt_mf) :=
        Array.getElem?_eq_getElem hlt_mf
      exact (hrel.locals_rel idx decl slot_i _ hdecl hslot_i hmls_orig).cache_layout
    · simp only [h_eq, ↓reduceIte] at hmls_i
      exact hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i

theorem EStateM.bind_eq_ok {ε σ α β : Type} {x : EStateM ε σ α} {f : α → EStateM ε σ β}
    {s s' : σ} {a : α} (h : x s = .ok a s') :
    (x >>= f) s = f a s' := by
  change (match x s with | .ok a s' => f a s' | .error e s' => .error e s') = f a s'
  rw [h]

theorem EStateM.bind_eq_error {ε σ α β : Type} {x : EStateM ε σ α} {f : α → EStateM ε σ β}
    {s s' : σ} {e : ε} (h : x s = .error e s') :
    (x >>= f) s = .error e s' := by
  change (match x s with | .ok a s' => f a s' | .error e s' => .error e s') = .error e s'
  rw [h]

theorem LocalRel.layout_eq
    {mach : AnnealMachine}
    {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot} {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRel mach decl layouts slot mls) :
    ∀ l, mls.layout = some l → l = translateTy decl.ty layouts := by
  cases h with
  | dead _ hlay => exact hlay
  | immediate _ _ _ hlay _ => exact hlay
  | indirect _ _ _ hlay _ _ => exact hlay

theorem cachedLayout_orElse_lookupLocalDeclLayout
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {idx : Nat} {decl : LocalDecl} {cachedLayout : Option Miri.Interpreter.LocalLayout}
    (hdecl : get? localDecls idx = some decl)
    (hcache : ∀ l, cachedLayout = some l → l = translateTy decl.ty layouts) :
    (cachedLayout <|> lookupLocalDeclLayout localDecls layouts idx) =
      some (translateTy decl.ty layouts) := by
  unfold lookupLocalDeclLayout
  rw [hdecl]
  cases hc : cachedLayout with
  | none => rfl
  | some l =>
    rw [hcache l hc]
    rfl

theorem cachedLayout_orElse_lookupLocalDeclLayout_orElse
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {idx : Nat} {decl : LocalDecl}
    {cachedLayout known : Option Miri.Interpreter.LocalLayout}
    (hdecl : get? localDecls idx = some decl)
    (hcache : ∀ l, cachedLayout = some l → l = translateTy decl.ty layouts) :
    (cachedLayout <|> lookupLocalDeclLayout localDecls layouts idx <|> known) =
      some (translateTy decl.ty layouts) := by
  unfold lookupLocalDeclLayout
  rw [hdecl]
  cases hc : cachedLayout with
  | none => rfl
  | some l =>
    rw [hcache l hc]
    rfl

/-! ### 5.1 Scalar Type Classification & Constant/Operand Bridge Lemmas -/

/-- Primitive scalar types (`bool`, `char`, signed `int`, unsigned `uint`). -/
def IsPrimScalarTy (ty : Ty) : Prop :=
  ty.kind = .bool ∨ ty.kind = .char ∨
    (∃ it, ty.kind = .int it) ∨ (∃ ut, ty.kind = .uint ut)

theorem IsPrimScalarTy.layoutOfEncoded {ty : Ty} {layouts : LayoutTable}
    (h : IsPrimScalarTy ty) :
    layoutOfEncodedTyId (encodeTyId ty) layouts = translateTy ty layouts := by
  rcases h with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
  · simp [encodeTyId, layoutOfEncodedTyId, translateTy, hk]
  · simp [encodeTyId, layoutOfEncodedTyId, translateTy, hk]
  · cases it <;> simp [encodeTyId, layoutOfEncodedTyId, translateTy, hk]
  · cases ut <;> simp [encodeTyId, layoutOfEncodedTyId, translateTy, hk]

theorem IsPrimScalarTy.size_ne_zero {ty : Ty} {layouts : LayoutTable}
    (h : IsPrimScalarTy ty) :
    (translateTy ty layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
  rcases h with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
    (try cases it) <;> (try cases ut) <;>
    (simp only [translateTy, hk]; decide)

/-- Predicate relating an Anneal `Ty` to its 64-bit `Miri.MIR.IntegerKind`. -/
inductive IsIntegralTy (ty : Ty) : Miri.MIR.IntegerKind → Prop where
  | int (it : IntTy) : ty.kind = .int it → IsIntegralTy ty (translateIntTy it)
  | uint (ut : UintTy) : ty.kind = .uint ut → IsIntegralTy ty (translateUintTy ut)

/-- Canonical `Ty` representative for each `Miri.MIR.IntegerKind`. -/
def canonicalIntegralTy : Miri.MIR.IntegerKind → Ty
  | .i8 => { kind := .int .i8, layoutIdx := 0 }
  | .i16 => { kind := .int .i16, layoutIdx := 0 }
  | .i32 => { kind := .int .i32, layoutIdx := 0 }
  | .i64 => { kind := .int .i64, layoutIdx := 0 }
  | .i128 => { kind := .int .i128, layoutIdx := 0 }
  | .isize => { kind := .int .isize, layoutIdx := 0 }
  | .u8 => { kind := .uint .u8, layoutIdx := 0 }
  | .u16 => { kind := .uint .u16, layoutIdx := 0 }
  | .u32 => { kind := .uint .u32, layoutIdx := 0 }
  | .u64 => { kind := .uint .u64, layoutIdx := 0 }
  | .u128 => { kind := .uint .u128, layoutIdx := 0 }
  | .usize => { kind := .uint .usize, layoutIdx := 0 }

namespace IsIntegralTy

theorem prim {ty : Ty} {kind : Miri.MIR.IntegerKind} (h : IsIntegralTy ty kind) :
    IsPrimScalarTy ty := by
  rcases h with ⟨it, hk⟩ | ⟨ut, hk⟩
  · exact Or.inr (Or.inr (Or.inl ⟨it, hk⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ut, hk⟩))

theorem ne_bool {ty : Ty} {kind : Miri.MIR.IntegerKind} (h : IsIntegralTy ty kind) :
    ty.kind ≠ .bool := by
  rcases h with ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] <;> nofun

theorem ne_char {ty : Ty} {kind : Miri.MIR.IntegerKind} (h : IsIntegralTy ty kind) :
    ty.kind ≠ .char := by
  rcases h with ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] <;> nofun

theorem classify {ty : Ty} {kind : Miri.MIR.IntegerKind} (h : IsIntegralTy ty kind) :
    classifyEncodedTyId (encodeTyId ty) = .ok (.integer kind) := by
  rcases h with ⟨it, hk⟩ | ⟨ut, hk⟩
  · cases it <;> simp [encodeTyId, classifyEncodedTyId, translateIntTy, hk]
  · cases ut <;> simp [encodeTyId, classifyEncodedTyId, translateUintTy, hk]

theorem translateTy_canonical {ty : Ty} {kind : Miri.MIR.IntegerKind}
    (h : IsIntegralTy ty kind) (layouts : LayoutTable) :
    translateTy ty layouts = translateTy (canonicalIntegralTy kind) emptyLayoutTable := by
  rcases h with ⟨it, hk⟩ | ⟨ut, hk⟩
  · cases it <;> simp [translateTy, encodeTyId, translateIntTy, canonicalIntegralTy, hk]
  · cases ut <;> simp [translateTy, encodeTyId, translateUintTy, canonicalIntegralTy, hk]

theorem translateTy_eq {ty₁ ty₂ : Ty} {kind : Miri.MIR.IntegerKind}
    (h₁ : IsIntegralTy ty₁ kind) (h₂ : IsIntegralTy ty₂ kind)
    (l₁ l₂ : LayoutTable) :
    translateTy ty₁ l₁ = translateTy ty₂ l₂ := by
  rw [h₁.translateTy_canonical l₁, h₂.translateTy_canonical l₂]

theorem size_eq {ty : Ty} {kind : Miri.MIR.IntegerKind}
    (h : IsIntegralTy ty kind) (layouts : LayoutTable) :
    (translateTy ty layouts).layout.size = translateSizeBytes (integerKindByteWidth kind) := by
  rcases h with ⟨it, hk⟩ | ⟨ut, hk⟩
  · cases it <;> (simp [translateTy, translateIntTy, integerKindByteWidth, scalarLayoutData, IntTy.byteWidth, hk]; rfl)
  · cases ut <;> (simp [translateTy, translateUintTy, integerKindByteWidth, scalarLayoutData, UintTy.byteWidth, hk]; rfl)

theorem signed_eq {ty : Ty} {kind : Miri.MIR.IntegerKind} (h : IsIntegralTy ty kind) :
    tyIsSigned ty = kind.signed := by
  rcases h with ⟨it, hk⟩ | ⟨ut, hk⟩
  · cases it <;> (rw [tyIsSigned_eq, hk]; rfl)
  · cases ut <;> (rw [tyIsSigned_eq, hk]; rfl)

theorem not_kinds {ty : Ty} {kind : Miri.MIR.IntegerKind} (h : IsIntegralTy ty kind) :
    ty.kind = .int .i8 ∨ ty.kind = .int .i16 ∨ ty.kind = .int .i32 ∨
      ty.kind = .int .i64 ∨ ty.kind = .int .i128 ∨ ty.kind = .int .isize ∨
      ty.kind = .uint .u8 ∨ ty.kind = .uint .u16 ∨ ty.kind = .uint .u32 ∨
      ty.kind = .uint .u64 ∨ ty.kind = .uint .u128 ∨ ty.kind = .uint .usize := by
  rcases h with ⟨it, hk⟩ | ⟨ut, hk⟩
  · cases it <;> simp [hk]
  · cases ut <;> simp [hk]

end IsIntegralTy

theorem translateSizeBytes_inj {a b : Nat}
    (ha : ValidScalarBytes a) (hb : ValidScalarBytes b)
    (heq : translateSizeBytes a = translateSizeBytes b) : a = b := by
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    (try rfl) <;>
    (exfalso; revert heq; decide)

theorem translateTy_bool_eq {ty : Ty} (hk : ty.kind = .bool) (layouts : LayoutTable) :
    translateTy ty layouts = translateTy { kind := .bool, layoutIdx := 0 } := by
  simp [translateTy, encodeTyId, hk]

theorem tryFromUInt_of_valid_canonical {sc : MirAst.ScalarInt}
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes) :
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 sc.bits) (translateSizeBytes sc.sizeBytes) =
        .ok (some msc) ∧
      ScalarRel sc msc := by
  obtain ⟨msc, htr, hrel⟩ :=
    truncateFromUInt_translateSizeBytes_spec hsz (BitVec.ofNat 128 sc.bits)
  have hlt : sc.bits < 2 ^ (8 * sc.sizeBytes) := by
    rw [← scalarModulus_eq_two_pow]; exact hcan
  have hmod : (BitVec.ofNat 128 sc.bits).toNat % 2 ^ (8 * sc.sizeBytes) = sc.bits := by
    rw [bitVec_ofNat_toNat_of_valid hsz hcan, Nat.mod_eq_of_lt hlt]
  rw [hmod] at htr hrel
  have hsc : (⟨sc.bits, sc.sizeBytes⟩ : MirAst.ScalarInt) = sc := by
    cases sc; rfl
  rw [hsc] at hrel
  refine ⟨msc, ?_, hrel⟩
  unfold Miri.Memory.ScalarInt.tryFromUInt
  change (do
    let (result, overflow) ← Miri.Memory.ScalarInt.truncateFromUInt
      (BitVec.ofNat 128 sc.bits) (translateSizeBytes sc.sizeBytes)
    if overflow then return none else return some result) = .ok (some msc)
  rw [htr]
  simp [bne_self_eq_false, bind, Except.bind, pure, Except.pure]

theorem bool_of_immediateRel {ty : Ty} {layouts : LayoutTable}
    {v : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    (hk : ty.kind = .bool)
    (himm : ImmediateRel ty layouts v imm) :
    ∃ (b : Bool) (msc : Miri.Memory.ScalarInt),
      v = .scalar (boolToScalar b) ∧
      imm = .scalar (.fromScalarInt msc) ∧
      ScalarRel (boolToScalar b) msc ∧
      (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBool = .ok b := by
  obtain ⟨sc, msc, rfl, rfl, hrel, _, hbool, _⟩ :=
    himm.of_primitive_scalar (Or.inl hk)
  obtain ⟨hsz1, hbits⟩ := hbool hk
  rcases sc with ⟨bits, sz⟩
  dsimp only at hsz1 hbits
  subst hsz1
  rcases hbits with rfl | rfl
  · refine ⟨false, msc, rfl, rfl, hrel, ?_⟩
    have htb : msc.toBits (Miri.ABI.Size.ofBytes 1) = .ok 0#128 := hrel.toBits_eq
    unfold Miri.Memory.Scalar.toBool Miri.Memory.Scalar.toUInt8
      Miri.Memory.Scalar.toUInt
      Miri.Memory.Scalar.toBits Miri.Memory.Scalar.toScalarInt
      Miri.Memory.Scalar.tryToScalarInt Miri.Memory.Scalar.fromScalarInt
    dsimp only [bind, Except.bind, Except.mapError, pure, Except.pure]
    rw [htb]
    rfl
  · refine ⟨true, msc, rfl, rfl, hrel, ?_⟩
    have htb : msc.toBits (Miri.ABI.Size.ofBytes 1) = .ok 1#128 := hrel.toBits_eq
    unfold Miri.Memory.Scalar.toBool Miri.Memory.Scalar.toUInt8
      Miri.Memory.Scalar.toUInt
      Miri.Memory.Scalar.toBits Miri.Memory.Scalar.toScalarInt
      Miri.Memory.Scalar.tryToScalarInt Miri.Memory.Scalar.fromScalarInt
    dsimp only [bind, Except.bind, Except.mapError, pure, Except.pure]
    rw [htb]
    rfl

theorem annealReadImmediate_of_immediateRel {ty : Ty} {layouts : LayoutTable}
    {v : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    (himm : ImmediateRel ty layouts v imm)
    (hsz : (translateTy ty layouts).layout.size ≠ Miri.ABI.Size.ZERO)
    (lay : Miri.Interpreter.LocalLayout) (m : AnnealStepState) :
    annealReadImmediate ⟨.immediate imm, lay⟩ m = .ok ⟨imm, lay⟩ m ∧ imm ≠ .uninit := by
  cases himm with
  | unit hzero => exact False.elim (hsz hzero)
  | scalar _ _ _ _ _ _ => exact ⟨rfl, nofun⟩
  | scalarPair _ _ _ _ _ _ _ _ => exact ⟨rfl, nofun⟩

/-! ### 5.2 `annealEvalPlace`, `annealWriteImmediate`, and `annealEvalOperand` Lemmas -/

theorem annealResolveAndCacheLocalLayout_eq
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {decl : LocalDecl}
    {known : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hcache : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts) :
    annealResolveAndCacheLocalLayout body.localDecls body.layouts idx known m =
      .ok (cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts),
            translateTy decl.ty body.layouts)
        { m with
          stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts)]⟩ } := by
  have hget : topFrame.getLocal idx = .ok (topFrame.locals[idx]'hlt) := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt, pure, Except.pure]
  have hgor := frame_getOrCacheLocalLayout_eq topFrame hlt hcache
  with_unfolding_all
    unfold annealResolveAndCacheLocalLayout
    simp only [get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      stack_currentFrame?_singleton m.stack topFrame hframes,
      hget, cachedLayout_orElse_lookupLocalDeclLayout_orElse hdecl hcache,
      hgor, hframes]
    rfl

theorem frame_getLocalOperand_dead
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {idx : Nat} {lay : Option Miri.Interpreter.LocalLayout}
    (hget : mf.getLocal idx = .ok ⟨.dead, lay⟩) :
    mf.getLocalOperand idx = .error (.localExpectedLive idx) := by
  unfold Miri.Interpreter.Frame.getLocalOperand
  rw [hget]
  rfl

theorem frame_getLocalOperand_live
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {idx : Nat} {opVal : Miri.Interpreter.Operand AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hget : mf.getLocal idx = .ok ⟨.live opVal, lay⟩) :
    mf.getLocalOperand idx = .ok opVal := by
  unfold Miri.Interpreter.Frame.getLocalOperand
  rw [hget]
  rfl

theorem annealEvalPlace_unprojected
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {dstDecl : LocalDecl}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : dstIdx < topFrame.locals.size)
    (hdecl : get? body.localDecls dstIdx = some dstDecl)
    (hcache : ∀ l, (topFrame.locals[dstIdx]'hlt).layout = some l →
      l = translateTy dstDecl.ty body.layouts) :
    annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
      .ok ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with
          stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt
            (translateTy dstDecl.ty body.layouts)]⟩ } := by
  have hres := annealResolveAndCacheLocalLayout_eq (known := none) hframes hlt hdecl hcache
  with_unfolding_all
    unfold annealEvalPlace
    simp only [Array.isEmpty_empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, stack_currentFrame?_singleton m.stack topFrame hframes,
      Option.isNone_some, hframes, hres]
    rfl

theorem annealWriteImmediate_dead
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {val : Miri.Interpreter.Immediate AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {dstLay : Miri.Interpreter.LocalLayout}
    {id0 : Miri.Interpreter.LocalsIdentity}
    (hframes : m.stack.frames = #[topFrame])
    (hget : topFrame.getLocal dstIdx = .ok ⟨.dead, lay⟩) :
    annealWriteImmediate val ⟨.local 0 dstIdx none id0, dstLay⟩ m =
      .error (.undefinedBehavior "write to dead local") m := by
  have hgop := frame_getLocalOperand_dead topFrame hget
  with_unfolding_all
    unfold annealWriteImmediate
    simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      stack_currentFrame?_singleton m.stack topFrame hframes, hframes, hgop]
    rfl

theorem annealWriteImmediate_live
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {val oldImm : Miri.Interpreter.Immediate AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {dstLay : Miri.Interpreter.LocalLayout}
    {id0 : Miri.Interpreter.LocalsIdentity}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : dstIdx < topFrame.locals.size)
    (hget : topFrame.getLocal dstIdx = .ok ⟨.live (.immediate oldImm), lay⟩) :
    annealWriteImmediate val ⟨.local 0 dstIdx none id0, dstLay⟩ m =
      .ok ()
        { m with
          stack :=
            ⟨#[{ topFrame with
                  locals := topFrame.locals.set dstIdx
                    { topFrame.locals[dstIdx]'hlt with value := .live (.immediate val) } hlt }]⟩ } := by
  have hgop := frame_getLocalOperand_live topFrame hget
  with_unfolding_all
    unfold annealWriteImmediate
    simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      stack_currentFrame?_singleton m.stack topFrame hframes, hframes, hgop,
      frame_replaceLocalValue_of_lt topFrame dstIdx hlt (.live (.immediate val))]
    rfl

/-- `StatementKind.deinit` never succeeds as a silent no-op under `annealStepHooks`
(unlike a `PlaceMention` lowering). -/
theorem annealStepHooks_deinit_ne_ok
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Place) (span : String) (m m' : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks localDecls layouts) ()
      (translateStmt ⟨.deinit place, span⟩) m ≠ (m', .ok ()) := by
  unfold Miri.Interpreter.Step.evalStatement translateStmt translateStmtKind
    annealStepHooks Miri.Interpreter.runRvalue Miri.Interpreter.evalRvalueIntoPlace
    annealRvalueHooks
  dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
  with_unfolding_all
    simp only [Bind.bind, EStateM.bind]
    cases annealEvalPlace localDecls layouts (translatePlace place) m with
    | error _ _ => nofun
    | ok dest s₁ =>
      dsimp only [annealEvalOperand, untranslatableConstOperand, evalMirConstImmediate,
        get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw]
      cases s₁.stack.currentFrame?.isNone <;> nofun

/-- `StatementKind.retag` never succeeds as a silent no-op under `annealStepHooks`
(unlike a `PlaceMention` lowering). -/
theorem annealStepHooks_retag_ne_ok
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (rk : RetagKind) (place : Place) (span : String) (m m' : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks localDecls layouts) ()
      (translateStmt ⟨.retag rk place, span⟩) m ≠ (m', .ok ()) := by
  unfold Miri.Interpreter.Step.evalStatement translateStmt translateStmtKind
    annealStepHooks Miri.Interpreter.runRvalue Miri.Interpreter.evalRvalueIntoPlace
    annealRvalueHooks
  dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
  with_unfolding_all
    simp only [Bind.bind, EStateM.bind]
    cases annealEvalPlace localDecls layouts (translatePlace place) m with
    | error _ _ => nofun
    | ok dest s₁ =>
      dsimp only [annealEvalOperand, untranslatableConstOperand, evalMirConstImmediate,
        get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw]
      cases s₁.stack.currentFrame?.isNone <;> nofun

/-- Syntactic well-typedness of a scalar or scalar-pair `MirAst.Operand` in `body`
relative to `topFrame`.

`Operand.move` is deliberately absent. Anneal's `evalOperand` deinitializes a
moved-from root local, whereas `lean-miri` (like the pinned rustc) leaves it
unchanged, so after a move the two states differ in exactly that local and a
later read of it is undefined behavior only in Anneal. Relating moves needs a
refinement argument (or a static no-use-after-move invariant) that lockstep
`StepRel` cannot express. -/
inductive WellTypedScalarOperand
    (body : CapturedMir)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    MirAst.Operand → Ty → Prop where
  | constScalar (c : ConstOperand) (sc : MirAst.ScalarInt) :
      c.val = .scalar (.int sc) →
      IsPrimScalarTy c.ty →
      ValidScalarBytes sc.sizeBytes →
      sc.bits < scalarModulus sc.sizeBytes →
      (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes →
      (c.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) →
      (c.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) →
      WellTypedScalarOperand body topFrame (.constant c) c.ty
  | copyLocal (idx : Local) (decl : LocalDecl) :
      get? body.localDecls idx = some decl →
      (translateTy decl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO →
      IsImmediateFrameLocal topFrame idx →
      WellTypedScalarOperand body topFrame (.copy ⟨idx, .nil⟩) decl.ty

theorem WellTypedScalarOperand.mono_immediate
    {body : CapturedMir}
    {tf tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (h : WellTypedScalarOperand body tf op ty)
    (hmono : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) :
    WellTypedScalarOperand body tf' op ty := by
  cases h with
  | constScalar c sc hval hprim hsz hcan hlaysz hbool hchar =>
    exact .constScalar c sc hval hprim hsz hcan hlaysz hbool hchar
  | copyLocal idx decl hdecl hsz himm =>
    exact .copyLocal idx decl hdecl hsz (hmono idx himm)

/-- Joint outcome relation for `evalOperand` (Anneal) vs
`annealEvalOperand >>= annealReadImmediate` (`lean-miri`). -/
inductive OperandEvalSimRel
    (body : CapturedMir) (af : StackFrame)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (m : AnnealStepState) (ty : Ty) :
    PlaceReadResult →
    EStateM.Result Miri.Interpreter.StepError AnnealStepState
      (Miri.Interpreter.RvalueImmTy AnnealProv) →
    Prop where
  | ok (v : Value) (locals' : List LocalSlot)
      (topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (imm : Miri.Interpreter.Immediate AnnealProv) :
      FrameRel body m.machine { af with locals := locals' } topFrame' →
      ImmediateRel ty body.layouts v imm →
      (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j) →
      topFrame' = { topFrame with locals := topFrame'.locals } →
      (MemoryAllocDisjoint topFrame → MemoryAllocDisjoint topFrame') →
      OperandEvalSimRel body af topFrame m ty
        (.ok v locals')
        (.ok ⟨imm, translateTy ty body.layouts⟩ { m with stack := ⟨#[topFrame']⟩ })
  | ub (m' : AnnealStepState) (msg : String) :
      OperandEvalSimRel body af topFrame m ty
        .ub
        (.error (.undefinedBehavior msg) m')

theorem WellTypedScalarOperand.operandTy_eq
    {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (h : WellTypedScalarOperand body tf op ty) :
    operandTy body.localDecls body.layouts op = some ty := by
  cases h with
  | constScalar _ _ _ _ _ _ _ _ _ => rfl
  | copyLocal idx decl hdecl _ _ => simp [operandTy, resolveProjectedTy, hdecl]


theorem annealEvalOperand_copy_dead
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {decl : LocalDecl}
    {lay : Option Miri.Interpreter.LocalLayout}
    {known : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hmls : topFrame.locals[idx]'hlt = ⟨.dead, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts) :
    annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) known m =
      .error (.undefinedBehavior "read of dead local")
        { m with
          stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt
            (translateTy decl.ty body.layouts)]⟩ } := by
  have hcache' : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_dead _ hget_c
  with_unfolding_all
    unfold annealEvalOperand
    simp only [Array.isEmpty_empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      Pure.pure, stack_currentFrame?_singleton m.stack topFrame hframes,
      Option.isNone_some, hres, hgop]
    rfl

theorem annealEvalOperand_copy_live
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {decl : LocalDecl}
    {opVal : Miri.Interpreter.Operand AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {known : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hmls : topFrame.locals[idx]'hlt = ⟨.live opVal, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts) :
    annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) known m =
      .ok ⟨opVal, translateTy decl.ty body.layouts⟩
        { m with
          stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt
            (translateTy decl.ty body.layouts)]⟩ } := by
  have hcache' : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_live _ hget_c
  with_unfolding_all
    unfold annealEvalOperand
    simp only [Array.isEmpty_empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      Pure.pure, stack_currentFrame?_singleton m.stack topFrame hframes,
      Option.isNone_some, hres, hgop]
    rfl

theorem evalOperand_scalar_simulation
    {body : CapturedMir} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {op : MirAst.Operand} {ty : Ty}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRel body m.machine af topFrame)
    (hop : WellTypedScalarOperand body topFrame op ty)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    OperandEvalSimRel body af topFrame m ty
      (evalOperand af.locals op .nil globals body.layouts .nil)
      ((annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediate) m) := by
  have hsame : { m with stack := ⟨#[topFrame]⟩ } = m :=
    stepState_with_same_singleton m topFrame hframes
  cases hop with
  | constScalar c sc hval hprim hsz hcan hlaysz hbool hchar =>
    obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
    have heval_a : evalOperand af.locals (.constant c) .nil globals body.layouts .nil =
        .ok (.scalar sc) af.locals := by
      unfold evalOperand
      dsimp only
      rw [hval]; rfl
    have heval_m : annealEvalOperand body.localDecls body.layouts
        (translateOperand (.constant c)) known m =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ m := by
      with_unfolding_all
        unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
        dsimp only
        rw [hval]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry, hprim.layoutOfEncoded]
    rw [heval_a, EStateM.bind_eq_ok heval_m]
    change OperandEvalSimRel body af topFrame m c.ty (.ok (.scalar sc) af.locals)
      (.ok ⟨.scalar (.fromScalarInt msc), translateTy c.ty body.layouts⟩ m)
    rw [← hsame]
    exact .ok (.scalar sc) af.locals topFrame (.scalar (.fromScalarInt msc))
      hframe (.scalar sc msc hrel hlaysz hbool hchar) (fun _ h => h) rfl (fun hdisj => hdisj)
  | copyLocal idx decl hdecl hsz_nz himm =>
    obtain ⟨slot, mls, _, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
    have hcache := hloc.layout_eq
    have himm' := himm mls hmls
    have htr : translateOperand (.copy ⟨idx, .nil⟩) = .Copy ⟨idx, #[]⟩ := rfl
    rw [htr]
    cases hloc with
    | dead cachedLayout _ =>
      have ha : evalOperand af.locals (.copy ⟨idx, .nil⟩) .nil globals body.layouts .nil = .ub := by
        simp [evalOperand, hslot]
      rw [ha, EStateM.bind_eq_error
        (annealEvalOperand_copy_dead hframes hlt_mf hdecl hmls_eq hcache)]
      exact .ub _ _
    | indirect _ mp _ _ _ _ =>
      exact False.elim (himm' mp rfl)
    | immediate _ imm cachedLayout _ hval =>
      let topFrame' := cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · have ha : evalOperand af.locals (.copy ⟨idx, .nil⟩) .nil globals body.layouts .nil = .ub := by
          simp [evalOperand, hslot]
        rw [ha, EStateM.bind_eq_ok
          (annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache)]
        exact .ub _ _
      · have ha : evalOperand af.locals (.copy ⟨idx, .nil⟩) .nil globals body.layouts .nil =
            .ok v af.locals := by
          simp [evalOperand, readProjectedValue, hslot]
        obtain ⟨hread, _⟩ :=
          annealReadImmediate_of_immediateRel himmRel hsz_nz (translateTy decl.ty body.layouts)
            { m with stack := ⟨#[topFrame']⟩ }
        rw [ha, EStateM.bind_eq_ok
          (annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache), hread]
        exact .ok v af.locals topFrame' imm
          (hframe.cache_local_layout hdecl hlt_mf)
          himmRel
          (fun _ hj => hj.cache_layout hlt_mf _)
          rfl
          (fun hdisj => by
            apply MemoryAllocDisjoint.mono_layout hdisj
            intro k
            by_cases hk : k = idx
            · subst hk
              exists (translateTy decl.ty body.layouts)
              dsimp [topFrame', cacheFrameLocalLayout]
              rw [Array.getElem?_set]
              rw [if_pos rfl]
              simp [hmls, hmls_eq]
            · exists (topFrame.locals[k]?).bind (fun x => x.layout)
              dsimp [topFrame', cacheFrameLocalLayout]
              rw [Array.getElem?_set_ne _ (Ne.symm hk)]
              simp [Option.map_eq_bind]
              cases topFrame.locals[k]? <;> rfl)

/-! ### 5.3 Public Mirrors & Operator-Result Shape Lemmas for `ScalarOps` / `Rvalue` -/

theorem EStateM.bind_assoc_apply {ε σ α β γ : Type}
    (ma : EStateM ε σ α) (mb : α → EStateM ε σ β) (mc : β → EStateM ε σ γ) (s : σ) :
    (ma >>= fun x => mb x >>= mc) s = ((ma >>= mb) >>= mc) s := by
  with_unfolding_all
    simp only [Bind.bind, EStateM.bind]
    cases ma s <;> rfl

/-- Public mirror of `Miri.Interpreter.ScalarOps.liftResult` (`private` in `ScalarOps.lean`). -/
def liftScalarResult {S A : Type} (result : Except Miri.Interpreter.StepError A) :
    Miri.Interpreter.RvalueM S A :=
  match result with | .ok value => pure value | .error reason => throw reason

/-- Public mirror of `Miri.Interpreter.ScalarOps.toScalar` (`private` in `ScalarOps.lean`). -/
def scalarOpsToScalar {Prov S : Type} (value : Miri.Interpreter.RvalueImmTy Prov) :
    Miri.Interpreter.RvalueM S (Miri.Memory.Scalar Prov) :=
  liftScalarResult (value.imm.toScalar.mapError Miri.Interpreter.ScalarOps.immediateError)

/-- Public mirror of `Miri.Interpreter.ScalarOps.toInteger` (`private` in `ScalarOps.lean`). -/
def scalarOpsToInteger {Prov S : Type} [Miri.Memory.PointerProvenance Prov]
    (value : Miri.Interpreter.RvalueImmTy Prov) (kind : Miri.MIR.IntegerKind) :
    Miri.Interpreter.RvalueM S Miri.Interpreter.IntegerValue := do
  let scalar ← scalarOpsToScalar value
  let scalar ← liftScalarResult (scalar.toScalarInt.mapError Miri.Interpreter.ScalarOps.scalarError)
  let _ ← liftScalarResult
    (scalar.toBits value.layout.layout.size |>.mapError Miri.Interpreter.ScalarOps.scalarIntError)
  return ⟨scalar, ⟨value.layout.layout.size, kind⟩⟩

/-- Public mirror of `Miri.Interpreter.ScalarOps.finish` (`private` in `ScalarOps.lean`). -/
def scalarOpsFinish {Prov S C : Type}
    (h : Miri.Interpreter.ScalarOpsHooks Prov S C) (choice : C)
    (input : Miri.ABI.TyAndLayout Miri.MIR.TyId) :
    Miri.Interpreter.IntegerResult → Miri.Interpreter.RvalueM S (Miri.Interpreter.RvalueImmTy Prov)
  | .scalar value => pure ⟨.scalar (.fromScalarInt value), input⟩
  | .withOverflow value overflow => do
    let layout ← h.overflowLayout choice input
    return ⟨.scalarPair (.fromScalarInt value) (.fromBool overflow), layout⟩
  | .boolean value => do
    let layout ← h.boolLayout choice
    return ⟨.scalar (.fromBool value), layout⟩
  | .ordering value => do
    let layout ← h.orderingLayout choice
    let integer : Int := match value with | .lt => -1 | .eq => 0 | .gt => 1
    let scalar ← liftScalarResult
      (Miri.Memory.Scalar.fromInt integer (Miri.ABI.Size.ofBytes 1) |>.mapError Miri.Interpreter.ScalarOps.scalarError)
    return ⟨.scalar scalar, layout⟩

/-- Public mirror of `Miri.Interpreter.ScalarOps.assertSameType` (`private` in `ScalarOps.lean`). -/
def scalarOpsAssertSameType {Prov S : Type}
    (left right : Miri.Interpreter.RvalueImmTy Prov) : Miri.Interpreter.RvalueM S Unit :=
  if left.layout.ty == right.layout.ty then pure ()
  else throw (.invalidProgram "asymmetric scalar operand types")

/-- Public mirror of `Miri.Interpreter.ScalarOps.isShift` (`private` in `ScalarOps.lean`). -/
def scalarOpsIsShift (op : Miri.MIR.BinOp) : Bool :=
  op == .Shl || op == .ShlUnchecked || op == .Shr || op == .ShrUnchecked

/-- Public mirror of `Miri.Interpreter.assertRvalueLayout` (`private` in `Rvalue.lean`). -/
def assertRvalueLayoutPub {S : Type}
    (actual expected : Miri.ABI.TyAndLayout Miri.MIR.TyId) : Miri.Interpreter.RvalueM S Unit :=
  if actual == expected then pure () else throw (.invalidProgram "rvalue result layout mismatch")

theorem scalarOps_unary_def {Prov S C : Type} [Miri.Memory.PointerProvenance Prov]
    (h : Miri.Interpreter.ScalarOpsHooks Prov S C) (choice : C)
    (op : Miri.MIR.UnOp) (value : Miri.Interpreter.RvalueImmTy Prov) :
    Miri.Interpreter.ScalarOps.unary h choice op value =
      (do
        match ← h.classify choice value.layout.ty with
        | .boolean =>
          let scalar ← scalarOpsToScalar value
          let b ← liftScalarResult (scalar.toBool.mapError Miri.Interpreter.ScalarOps.scalarError)
          if op != .Not then throw (.invalidProgram "invalid boolean unary operation")
          scalarOpsFinish h choice value.layout (.boolean (!b))
        | .integer kind =>
          let integer ← scalarOpsToInteger value kind
          let scalar ← liftScalarResult
            (Miri.Interpreter.IntegerOps.unary op integer |>.mapError Miri.Interpreter.ScalarOps.integerError)
          return ⟨.scalar (.fromScalarInt scalar), value.layout⟩
        | .floating =>
          let _ ← scalarOpsToScalar value
          if op != .Neg then throw (.invalidProgram "invalid float unary operation")
          h.floatUnary choice op value
        | .pointer =>
          if op != .PtrMetadata then throw (.invalidProgram "invalid pointer unary operation")
          h.derefValidity choice value
          let (_, metadata) ← liftScalarResult
            (value.imm.toScalarAndMeta |>.mapError Miri.Interpreter.ScalarOps.immediateError)
          match metadata with
          | .metadata scalar =>
            let layout ← h.metadataLayout choice value.layout.ty
            return ⟨.scalar scalar, layout⟩
          | .none =>
            let layout ← h.unitLayout choice
            return ⟨.uninit, layout⟩
        | .character => throw (.invalidProgram "invalid character unary operation")
        | .functionPointer => throw (.invalidProgram "invalid function-pointer unary operation")) := rfl

theorem scalarOps_binary_def {Prov S C : Type} [Miri.Memory.PointerProvenance Prov]
    (h : Miri.Interpreter.ScalarOpsHooks Prov S C) (choice : C)
    (op : Miri.MIR.BinOp) (left right : Miri.Interpreter.RvalueImmTy Prov) :
    Miri.Interpreter.ScalarOps.binary h choice op left right =
      (do
        match ← h.classify choice left.layout.ty with
        | .character =>
          scalarOpsAssertSameType left right
          let l ← scalarOpsToScalar left
          let r ← scalarOpsToScalar right
          let l ← liftScalarResult (l.toChar.mapError Miri.Interpreter.ScalarOps.scalarError)
          let r ← liftScalarResult (r.toChar.mapError Miri.Interpreter.ScalarOps.scalarError)
          let result ← liftScalarResult
            (Miri.Interpreter.IntegerOps.binaryChar op l r |>.mapError Miri.Interpreter.ScalarOps.integerError)
          scalarOpsFinish h choice left.layout result
        | .boolean =>
          scalarOpsAssertSameType left right
          let l ← scalarOpsToScalar left
          let r ← scalarOpsToScalar right
          let l ← liftScalarResult (l.toBool.mapError Miri.Interpreter.ScalarOps.scalarError)
          let r ← liftScalarResult (r.toBool.mapError Miri.Interpreter.ScalarOps.scalarError)
          let result ← liftScalarResult
            (Miri.Interpreter.IntegerOps.binaryBool op l r |>.mapError Miri.Interpreter.ScalarOps.integerError)
          scalarOpsFinish h choice left.layout result
        | .floating =>
          scalarOpsAssertSameType left right
          h.floatBinary choice op left right
        | .integer kind =>
          let .integer rightKind ← h.classify choice right.layout.ty
            | throw (.invalidProgram "integer binary RHS is not integral")
          let l ← scalarOpsToInteger left kind
          let r ← scalarOpsToInteger right rightKind
          if !scalarOpsIsShift op then scalarOpsAssertSameType left right
          let result ← liftScalarResult
            (Miri.Interpreter.IntegerOps.binary op l r |>.mapError Miri.Interpreter.ScalarOps.integerError)
          scalarOpsFinish h choice left.layout result
        | .pointer | .functionPointer =>
          let rhs ← h.classify choice right.layout.ty
          match rhs with
          | .pointer | .functionPointer | .integer _ => h.pointerBinary choice op left right
          | _ => throw (.invalidProgram "pointer binary RHS is neither pointer nor integer")) := rfl

theorem evalRvalueIntoPlace_unaryOp_def {P S C V : Type}
    (h : Miri.Interpreter.RvalueHooks P S C V) (choice : C)
    (uop : Miri.MIR.UnOp) (op : Miri.MIR.Operand) (place : Miri.MIR.Place) :
    Miri.Interpreter.evalRvalueIntoPlace h choice (.UnaryOp uop op) place =
      (do
        let dest ← h.evalPlace choice place true
        let layout := h.placeLayout dest
        let val ← h.evalOperandAt choice (Miri.Interpreter.OperandPath.rvalue "operand") op
          (if uop.homogeneous then some layout else none)
        let val ← h.readImmediate choice val
        let result ← h.unaryOp choice uop val
        assertRvalueLayoutPub result.layout layout
        h.writeImmediate choice result.imm dest) := rfl

theorem evalRvalueIntoPlace_binaryOp_def {P S C V : Type}
    (h : Miri.Interpreter.RvalueHooks P S C V) (choice : C)
    (bop : Miri.MIR.BinOp) (l r : Miri.MIR.Operand) (place : Miri.MIR.Place) :
    Miri.Interpreter.evalRvalueIntoPlace h choice (.BinaryOp bop l r) place =
      (do
        let dest ← h.evalPlace choice place true
        let layout := h.placeLayout dest
        let left ← h.evalOperandAt choice (Miri.Interpreter.OperandPath.rvalue "left") l
          (if bop.leftHomogeneous then some layout else none)
        let left ← h.readImmediate choice left
        let right ← h.evalOperandAt choice (Miri.Interpreter.OperandPath.rvalue "right") r
          (if bop.rightHomogeneous then some left.layout else none)
        let right ← h.readImmediate choice right
        let result ← h.binaryOp choice bop left right
        assertRvalueLayoutPub result.layout layout
        h.writeImmediate choice result.imm dest) := rfl

theorem truncateInt_size {sz : Nat} (hsz : ValidScalarBytes sz)
    {kind : Miri.MIR.IntegerKind} {val : Int}
    {v : Miri.Memory.ScalarInt} {ovf : Bool}
    (h : truncateInt val ⟨translateSizeBytes sz, kind⟩ = .ok (v, ovf)) :
    v.size = translateSizeBytes sz := by
  obtain ⟨msc, lossy, htr, hrel, _⟩ := truncateInt_spec hsz kind val
  rw [htr] at h
  injection h with h'
  injection h' with hv _
  subst hv
  exact hrel.size_eq

def IsNonOvfArithOrBitwiseBinOp (op : MirAst.BinOp) : Prop :=
  op = .add ∨ op = .sub ∨ op = .mul ∨
  op = .addUnchecked ∨ op = .subUnchecked ∨ op = .mulUnchecked ∨
  op = .div ∨ op = .rem ∨
  IsBitwiseBinOp op

def IsCmpBinOp (op : MirAst.BinOp) : Prop :=
  op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge

def IsWithOverflowBinOp (op : MirAst.BinOp) : Prop :=
  op = .addWithOverflow ∨ op = .subWithOverflow ∨ op = .mulWithOverflow

theorem except_err_nonovf_shape (sz : Miri.ABI.Size) (e : Miri.Interpreter.IntegerOpError) :
    (∀ msc', (Except.error e : Except Miri.Interpreter.IntegerOpError Miri.Interpreter.IntegerResult) =
      .ok (.scalar msc') → msc'.size = sz) ∧
    (∀ msc' b, (Except.error e : Except Miri.Interpreter.IntegerOpError Miri.Interpreter.IntegerResult) ≠
      .ok (.withOverflow msc' b)) ∧
    (∀ b, (Except.error e : Except Miri.Interpreter.IntegerOpError Miri.Interpreter.IntegerResult) ≠
      .ok (.boolean b)) := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro _ h; cases h
  · intro _ _ h; cases h
  · intro _ h; cases h

theorem except_ok_scalar_nonovf_shape {val : Miri.Memory.ScalarInt} {sz : Miri.ABI.Size}
    (hsz : val.size = sz) :
    (∀ msc', (Except.ok (.scalar val) : Except Miri.Interpreter.IntegerOpError Miri.Interpreter.IntegerResult) =
      .ok (.scalar msc') → msc'.size = sz) ∧
    (∀ msc' b, (Except.ok (.scalar val) : Except Miri.Interpreter.IntegerOpError Miri.Interpreter.IntegerResult) ≠
      .ok (.withOverflow msc' b)) ∧
    (∀ b, (Except.ok (.scalar val) : Except Miri.Interpreter.IntegerOpError Miri.Interpreter.IntegerResult) ≠
      .ok (.boolean b)) := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro msc' h; cases h; exact hsz
  · intro _ _ h; cases h
  · intro _ h; cases h

theorem scalarResultInt_nonovf_shape {op : Miri.MIR.BinOp}
    (hno : op.isOverflowing = false) {val : Miri.Memory.ScalarInt}
    {sz : Miri.ABI.Size} (hsz : val.size = sz) (ovf : Bool) :
    (∀ msc', scalarResultInt op val ovf = .ok (.scalar msc') → msc'.size = sz) ∧
    (∀ msc' b, scalarResultInt op val ovf ≠ .ok (.withOverflow msc' b)) ∧
    (∀ b, scalarResultInt op val ovf ≠ .ok (.boolean b)) := by
  unfold scalarResultInt
  rw [hno]
  cases (ovf && op.isUnchecked) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind,
      MonadExcept.throw, throwThe, MonadExceptOf.throw]
  · exact except_ok_scalar_nonovf_shape hsz
  · exact except_err_nonovf_shape sz _

theorem arithmeticInt_nonovf_shape {op : Miri.MIR.BinOp}
    (hop : op = .Add ∨ op = .Sub ∨ op = .Mul ∨
      op = .AddUnchecked ∨ op = .SubUnchecked ∨ op = .MulUnchecked ∨
      op = .Div ∨ op = .Rem)
    {sz : Nat} (hsz : ValidScalarBytes sz) (kind : Miri.MIR.IntegerKind) (l r : Int) :
    (∀ msc', arithmeticInt op l r ⟨translateSizeBytes sz, kind⟩ = .ok (.scalar msc') →
      msc'.size = translateSizeBytes sz) ∧
    (∀ msc' b, arithmeticInt op l r ⟨translateSizeBytes sz, kind⟩ ≠ .ok (.withOverflow msc' b)) ∧
    (∀ b, arithmeticInt op l r ⟨translateSizeBytes sz, kind⟩ ≠ .ok (.boolean b)) := by
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [arithmeticInt_nonDivRem_eq .Add l r sz kind rfl rfl]
    obtain ⟨val, lossy, htr, hval, _⟩ := truncateInt_spec hsz kind (l + r)
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [htr]; dsimp only [bind, Except.bind]
    exact scalarResultInt_nonovf_shape rfl hval.size_eq _
  · rw [arithmeticInt_nonDivRem_eq .Sub l r sz kind rfl rfl]
    obtain ⟨val, lossy, htr, hval, _⟩ := truncateInt_spec hsz kind (l - r)
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [htr]; dsimp only [bind, Except.bind]
    exact scalarResultInt_nonovf_shape rfl hval.size_eq _
  · rw [arithmeticInt_nonDivRem_eq .Mul l r sz kind rfl rfl]
    obtain ⟨val, lossy, htr, hval, _⟩ := truncateInt_spec hsz kind (l * r)
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [htr]; dsimp only [bind, Except.bind]
    exact scalarResultInt_nonovf_shape rfl hval.size_eq _
  · rw [arithmeticInt_nonDivRem_eq .AddUnchecked l r sz kind rfl rfl]
    obtain ⟨val, lossy, htr, hval, _⟩ := truncateInt_spec hsz kind (l + r)
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [htr]; dsimp only [bind, Except.bind]
    exact scalarResultInt_nonovf_shape rfl hval.size_eq _
  · rw [arithmeticInt_nonDivRem_eq .SubUnchecked l r sz kind rfl rfl]
    obtain ⟨val, lossy, htr, hval, _⟩ := truncateInt_spec hsz kind (l - r)
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [htr]; dsimp only [bind, Except.bind]
    exact scalarResultInt_nonovf_shape rfl hval.size_eq _
  · rw [arithmeticInt_nonDivRem_eq .MulUnchecked l r sz kind rfl rfl]
    obtain ⟨val, lossy, htr, hval, _⟩ := truncateInt_spec hsz kind (l * r)
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [htr]; dsimp only [bind, Except.bind]
    exact scalarResultInt_nonovf_shape rfl hval.size_eq _
  · rw [arithmeticInt_div_eq]
    obtain ⟨val, lossy, htr, hval, _⟩ := truncateInt_spec hsz kind (Int.tdiv l r)
    cases (r == 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases kind.signed
      · simp only [Bool.false_eq_true, ↓reduceIte, htr, bind, Except.bind, pure, Except.pure]
        exact except_ok_scalar_nonovf_shape hval.size_eq
      · simp only [↓reduceIte]
        rcases (translateSizeBytes sz).signedIntMin with e | min
        · exact except_err_nonovf_shape _ _
        · dsimp only
          cases (l == min && r == -1)
          · simp only [Bool.false_eq_true, ↓reduceIte, htr, bind, Except.bind, pure, Except.pure]
            exact except_ok_scalar_nonovf_shape hval.size_eq
          · simp only [↓reduceIte]; exact except_err_nonovf_shape _ _
    · simp only [↓reduceIte]; exact except_err_nonovf_shape _ _
  · rw [arithmeticInt_rem_eq]
    obtain ⟨val, lossy, htr, hval, _⟩ := truncateInt_spec hsz kind (Int.tmod l r)
    cases (r == 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases kind.signed
      · simp only [Bool.false_eq_true, ↓reduceIte, htr, bind, Except.bind, pure, Except.pure]
        exact except_ok_scalar_nonovf_shape hval.size_eq
      · simp only [↓reduceIte]
        rcases (translateSizeBytes sz).signedIntMin with e | min
        · exact except_err_nonovf_shape _ _
        · dsimp only
          cases (l == min && r == -1)
          · simp only [Bool.false_eq_true, ↓reduceIte, htr, bind, Except.bind, pure, Except.pure]
            exact except_ok_scalar_nonovf_shape hval.size_eq
          · simp only [↓reduceIte]; exact except_err_nonovf_shape _ _
    · simp only [↓reduceIte]; exact except_err_nonovf_shape _ _

theorem bitwise_truncate_nonovf_shape {sz₁ sz₂ : Nat} (hsz₁ : ValidScalarBytes sz₁)
    (msc₁ msc₂ : Miri.Memory.ScalarInt) (f : BitVec 128 → BitVec 128 → BitVec 128) :
    let r : Except Miri.Interpreter.IntegerOpError Miri.Interpreter.IntegerResult := do
      let lb ← msc₁.toUInt (translateSizeBytes sz₁) |>.mapError .scalar
      let rb ← msc₂.toUInt (translateSizeBytes sz₂) |>.mapError .scalar
      let (value, _) ← Miri.Memory.ScalarInt.truncateFromUInt (f lb rb) (translateSizeBytes sz₁)
        |>.mapError .scalar
      return .scalar value
    (∀ msc', r = .ok (.scalar msc') → msc'.size = translateSizeBytes sz₁) ∧
    (∀ msc' ovf, r ≠ .ok (.withOverflow msc' ovf)) ∧
    (∀ b, r ≠ .ok (.boolean b)) := by
  dsimp only
  rcases msc₁.toUInt (translateSizeBytes sz₁) with _ | lb
  · exact except_err_nonovf_shape _ _
  dsimp only [Except.mapError, bind, Except.bind]
  rcases msc₂.toUInt (translateSizeBytes sz₂) with _ | rb
  · exact except_err_nonovf_shape _ _
  dsimp only [Except.mapError, bind, Except.bind]
  obtain ⟨val, htr, hval_rel⟩ := truncateFromUInt_translateSizeBytes_spec hsz₁ (f lb rb)
  rw [htr]
  exact except_ok_scalar_nonovf_shape hval_rel.size_eq

theorem integerOps_binary_noncmp_nonovf_shape
    {op : MirAst.BinOp}
    (h : IsNonOvfArithOrBitwiseBinOp op ∨ IsShiftBinOp op)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (kind₁ kind₂ : Miri.MIR.IntegerKind) :
    let left : Miri.Interpreter.IntegerValue := ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind₁⟩⟩
    let right : Miri.Interpreter.IntegerValue := ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind₂⟩⟩
    (∀ msc', Miri.Interpreter.IntegerOps.binary (translateBinOp op) left right = .ok (.scalar msc') →
      msc'.size = translateSizeBytes sc₁.sizeBytes) ∧
    (∀ msc' ovf, Miri.Interpreter.IntegerOps.binary (translateBinOp op) left right ≠ .ok (.withOverflow msc' ovf)) ∧
    (∀ b, Miri.Interpreter.IntegerOps.binary (translateBinOp op) left right ≠ .ok (.boolean b)) := by
  dsimp only
  rw [integerOps_binary_eq hrel₁ hrel₂ kind₁ kind₂ (translateBinOp op)]
  dsimp only [bind, Except.bind]
  rcases h with hnonsh | hsh
  · have hnot_sh : (translateBinOp op == .Shl || translateBinOp op == .ShlUnchecked ||
        translateBinOp op == .Shr || translateBinOp op == .ShrUnchecked) = false := by
      rcases hnonsh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | (rfl | rfl | rfl) <;> rfl
    rw [hnot_sh]
    cases hty : ((⟨translateSizeBytes sc₁.sizeBytes, kind₁⟩ : Miri.Interpreter.IntegerType) !=
        ⟨translateSizeBytes sc₂.sizeBytes, kind₂⟩)
    · simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
      rcases hnonsh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hbw
      · exact arithmeticInt_nonovf_shape (Or.inl rfl) hrel₁.validBytes kind₁ _ _
      · exact arithmeticInt_nonovf_shape (Or.inr (Or.inl rfl)) hrel₁.validBytes kind₁ _ _
      · exact arithmeticInt_nonovf_shape (Or.inr (Or.inr (Or.inl rfl))) hrel₁.validBytes kind₁ _ _
      · exact arithmeticInt_nonovf_shape (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hrel₁.validBytes kind₁ _ _
      · exact arithmeticInt_nonovf_shape (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hrel₁.validBytes kind₁ _ _
      · exact arithmeticInt_nonovf_shape (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hrel₁.validBytes kind₁ _ _
      · exact arithmeticInt_nonovf_shape (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) hrel₁.validBytes kind₁ _ _
      · exact arithmeticInt_nonovf_shape (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))) hrel₁.validBytes kind₁ _ _
      · rcases hbw with rfl | rfl | rfl
        · exact bitwise_truncate_nonovf_shape hrel₁.validBytes msc₁ msc₂ (· &&& ·)
        · exact bitwise_truncate_nonovf_shape hrel₁.validBytes msc₁ msc₂ (· ||| ·)
        · exact bitwise_truncate_nonovf_shape hrel₁.validBytes msc₁ msc₂ (· ^^^ ·)
    · simp only [Bool.false_eq_true, ↓reduceIte,
        MonadExcept.throw, throwThe, MonadExceptOf.throw]
      exact except_err_nonovf_shape _ _
  · have his_sh : (translateBinOp op == .Shl || translateBinOp op == .ShlUnchecked ||
        translateBinOp op == .Shr || translateBinOp op == .ShrUnchecked) = true := by
      rcases hsh with rfl | rfl | rfl | rfl <;> rfl
    rw [his_sh]
    simp only [↓reduceIte]
    unfold shiftInt
    rcases (translateSizeBytes sc₁.sizeBytes).bits with _ | bits
    · exact except_err_nonovf_shape _ _
    dsimp only [Except.mapError, bind, Except.bind]
    rcases htr : truncateInt _ ⟨translateSizeBytes sc₁.sizeBytes, kind₁⟩ with _ | ⟨val, _⟩
    · exact except_err_nonovf_shape _ _
    dsimp only [bind, Except.bind]
    cases (_ && (translateBinOp op).isUnchecked) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        MonadExcept.throw, throwThe, MonadExceptOf.throw]
    · exact except_ok_scalar_nonovf_shape (truncateInt_size hrel₁.validBytes htr)
    · exact except_err_nonovf_shape _ _

theorem integerOps_binary_cmp_shape
    {op : MirAst.BinOp} (h : IsCmpBinOp op)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (kind₁ kind₂ : Miri.MIR.IntegerKind) :
    let left : Miri.Interpreter.IntegerValue := ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind₁⟩⟩
    let right : Miri.Interpreter.IntegerValue := ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind₂⟩⟩
    (∀ msc', Miri.Interpreter.IntegerOps.binary (translateBinOp op) left right ≠ .ok (.scalar msc')) ∧
    (∀ msc' ovf, Miri.Interpreter.IntegerOps.binary (translateBinOp op) left right ≠ .ok (.withOverflow msc' ovf)) := by
  dsimp only
  rw [integerOps_binary_eq hrel₁ hrel₂ kind₁ kind₂ (translateBinOp op)]
  dsimp only [bind, Except.bind]
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp only [translateBinOp] <;>
    cases ((⟨translateSizeBytes sc₁.sizeBytes, kind₁⟩ : Miri.Interpreter.IntegerType) !=
      ⟨translateSizeBytes sc₂.sizeBytes, kind₂⟩) <;>
    simp [MonadExcept.throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

theorem scalarResultInt_ovf_shape {op : Miri.MIR.BinOp}
    (hovf : op.isOverflowing = true) (hunch : op.isUnchecked = false)
    (val : Miri.Memory.ScalarInt) (ovf : Bool) :
    (∀ msc', scalarResultInt op val ovf ≠ .ok (.scalar msc')) ∧
    (∀ b, scalarResultInt op val ovf ≠ .ok (.boolean b)) ∧
    (∀ reason, scalarResultInt op val ovf ≠ .error (.undefinedBehavior reason)) := by
  unfold scalarResultInt
  rw [hovf, hunch, Bool.and_false]
  simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h

theorem arithmeticInt_ovf_shape {op : Miri.MIR.BinOp}
    (hop : op = .AddWithOverflow ∨ op = .SubWithOverflow ∨ op = .MulWithOverflow)
    {sz : Nat} (hsz : ValidScalarBytes sz) (kind : Miri.MIR.IntegerKind) (l r : Int) :
    (∀ msc', arithmeticInt op l r ⟨translateSizeBytes sz, kind⟩ ≠ .ok (.scalar msc')) ∧
    (∀ b, arithmeticInt op l r ⟨translateSizeBytes sz, kind⟩ ≠ .ok (.boolean b)) ∧
    (∀ reason, arithmeticInt op l r ⟨translateSizeBytes sz, kind⟩ ≠
      .error (.undefinedBehavior reason)) := by
  rcases hop with rfl | rfl | rfl
  · rw [arithmeticInt_nonDivRem_eq .AddWithOverflow l r sz kind rfl rfl]
    obtain ⟨val, lossy, htr, _, _⟩ := truncateInt_spec hsz kind (l + r)
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [htr]; dsimp only [bind, Except.bind]
    exact scalarResultInt_ovf_shape rfl rfl val _
  · rw [arithmeticInt_nonDivRem_eq .SubWithOverflow l r sz kind rfl rfl]
    obtain ⟨val, lossy, htr, _, _⟩ := truncateInt_spec hsz kind (l - r)
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [htr]; dsimp only [bind, Except.bind]
    exact scalarResultInt_ovf_shape rfl rfl val _
  · rw [arithmeticInt_nonDivRem_eq .MulWithOverflow l r sz kind rfl rfl]
    obtain ⟨val, lossy, htr, _, _⟩ := truncateInt_spec hsz kind (l * r)
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [htr]; dsimp only [bind, Except.bind]
    exact scalarResultInt_ovf_shape rfl rfl val _

theorem integerOps_binary_withOverflow_shape
    {op : MirAst.BinOp} (h : IsWithOverflowBinOp op)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (kind₁ kind₂ : Miri.MIR.IntegerKind) :
    let left : Miri.Interpreter.IntegerValue := ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind₁⟩⟩
    let right : Miri.Interpreter.IntegerValue := ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind₂⟩⟩
    (∀ msc', Miri.Interpreter.IntegerOps.binary (translateBinOp op) left right ≠ .ok (.scalar msc')) ∧
    (∀ b, Miri.Interpreter.IntegerOps.binary (translateBinOp op) left right ≠ .ok (.boolean b)) ∧
    (∀ reason, Miri.Interpreter.IntegerOps.binary (translateBinOp op) left right ≠ .error (.undefinedBehavior reason)) := by
  dsimp only
  rw [integerOps_binary_eq hrel₁ hrel₂ kind₁ kind₂ (translateBinOp op)]
  dsimp only [bind, Except.bind]
  have hnot_sh : (translateBinOp op == .Shl || translateBinOp op == .ShlUnchecked ||
      translateBinOp op == .Shr || translateBinOp op == .ShrUnchecked) = false := by
    rcases h with rfl | rfl | rfl <;> rfl
  rw [hnot_sh]
  cases hty : ((⟨translateSizeBytes sc₁.sizeBytes, kind₁⟩ : Miri.Interpreter.IntegerType) !=
      ⟨translateSizeBytes sc₂.sizeBytes, kind₂⟩)
  · simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
    rcases h with rfl | rfl | rfl
    · exact arithmeticInt_ovf_shape (Or.inl rfl) hrel₁.validBytes kind₁ _ _
    · exact arithmeticInt_ovf_shape (Or.inr (Or.inl rfl)) hrel₁.validBytes kind₁ _ _
    · exact arithmeticInt_ovf_shape (Or.inr (Or.inr rfl)) hrel₁.validBytes kind₁ _ _
  · simp only [Bool.false_eq_true, ↓reduceIte,
      MonadExcept.throw, throwThe, MonadExceptOf.throw]
    refine ⟨?_, ⟨?_, ?_⟩⟩ <;> (intro _ h'; cases h')

theorem scalarOps_toInteger_eq
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    {ty : Ty} {layouts : LayoutTable} {kind : Miri.MIR.IntegerKind}
    (hrel : ScalarRel sc msc)
    (hsz : (translateTy ty layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (m : AnnealStepState) :
    scalarOpsToInteger
      (Prov := AnnealProv) ⟨.scalar (.fromScalarInt msc), translateTy ty layouts⟩ kind m =
      .ok ⟨msc, ⟨translateSizeBytes sc.sizeBytes, kind⟩⟩ m := by
  with_unfolding_all
    unfold scalarOpsToInteger scalarOpsToScalar liftScalarResult
      Miri.Interpreter.Immediate.toScalar
      Miri.Memory.Scalar.toScalarInt Miri.Memory.Scalar.tryToScalarInt
      Miri.Memory.Scalar.fromScalarInt
    simp only [hsz, hrel.toBits_eq, Except.mapError, bind, Except.bind, pure, Except.pure,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

/-! ### 5.4 Well-Typed Scalar Rvalues & `evalRvalueIntoPlace` Simulation -/

/-- Well-typedness of a unary scalar operator `(uop, srcTy, dstTy)` in `LM-1.1`. -/
inductive WellTypedScalarUnOp : MirAst.UnOp → Ty → Ty → Prop where
  | intNot (srcTy dstTy : Ty) (kind : Miri.MIR.IntegerKind) :
      IsIntegralTy srcTy kind →
      IsIntegralTy dstTy kind →
      WellTypedScalarUnOp .not srcTy dstTy
  | boolNot (srcTy dstTy : Ty) :
      srcTy.kind = .bool →
      dstTy.kind = .bool →
      WellTypedScalarUnOp .not srcTy dstTy
  | intNeg (srcTy dstTy : Ty) (kind : Miri.MIR.IntegerKind) :
      IsIntegralTy srcTy kind →
      IsIntegralTy dstTy kind →
      kind.signed = true →
      WellTypedScalarUnOp .neg srcTy dstTy

/-- Well-typedness of a binary scalar operator `(bop, lhsTy, rhsTy, dstTy)` in `LM-1.1`. -/
inductive WellTypedScalarBinOp (layouts : LayoutTable) (localDecls : List LocalDecl := .nil) :
    MirAst.BinOp → Ty → Ty → Ty → Prop where
  | intArithOrBitwise (bop : MirAst.BinOp) (lhsTy rhsTy dstTy : Ty)
      (kind : Miri.MIR.IntegerKind) :
      IsNonOvfArithOrBitwiseBinOp bop →
      IsIntegralTy lhsTy kind →
      IsIntegralTy rhsTy kind →
      IsIntegralTy dstTy kind →
      WellTypedScalarBinOp layouts localDecls bop lhsTy rhsTy dstTy
  | intCmp (bop : MirAst.BinOp) (lhsTy rhsTy dstTy : Ty)
      (kind : Miri.MIR.IntegerKind) :
      IsCmpBinOp bop →
      IsIntegralTy lhsTy kind →
      IsIntegralTy rhsTy kind →
      dstTy.kind = .bool →
      WellTypedScalarBinOp layouts localDecls bop lhsTy rhsTy dstTy
  | intWithOverflow (bop : MirAst.BinOp) (lhsTy rhsTy dstTy : Ty)
      (kind : Miri.MIR.IntegerKind) :
      IsWithOverflowBinOp bop →
      IsIntegralTy lhsTy kind →
      IsIntegralTy rhsTy kind →
      ((∃ ts, dstTy.kind = .tuple ts) ∨ (∃ p a, dstTy.kind = .adt p a)) →
      translateTy dstTy layouts =
        findOverflowTupleLayout localDecls layouts (translateTy lhsTy layouts) →
      WellTypedScalarBinOp layouts localDecls bop lhsTy rhsTy dstTy
  | intShift (bop : MirAst.BinOp) (lhsTy rhsTy dstTy : Ty)
      (kind₁ kind₂ : Miri.MIR.IntegerKind) :
      IsShiftBinOp bop →
      IsIntegralTy lhsTy kind₁ →
      IsIntegralTy rhsTy kind₂ →
      IsIntegralTy dstTy kind₁ →
      WellTypedScalarBinOp layouts localDecls bop lhsTy rhsTy dstTy
  | boolBitwise (bop : MirAst.BinOp) (lhsTy rhsTy dstTy : Ty) :
      IsBitwiseBinOp bop →
      lhsTy.kind = .bool →
      rhsTy.kind = .bool →
      dstTy.kind = .bool →
      WellTypedScalarBinOp layouts localDecls bop lhsTy rhsTy dstTy

/-- Syntactic well-typedness of a scalar `MirAst.Rvalue` producing `dstTy`. -/
inductive WellTypedScalarRvalue
    (body : CapturedMir)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    MirAst.Rvalue → Ty → Prop where
  | use (op : MirAst.Operand) (dstTy : Ty) :
      WellTypedScalarOperand body topFrame op dstTy →
      WellTypedScalarRvalue body topFrame (.use op) dstTy
  | unaryOp (uop : MirAst.UnOp) (op : MirAst.Operand) (srcTy dstTy : Ty) :
      WellTypedScalarOperand body topFrame op srcTy →
      WellTypedScalarUnOp uop srcTy dstTy →
      WellTypedScalarRvalue body topFrame (.unaryOp uop op) dstTy
  | binaryOp (bop : MirAst.BinOp) (lhsOp rhsOp : MirAst.Operand)
      (lhsTy rhsTy dstTy : Ty) :
      WellTypedScalarOperand body topFrame lhsOp lhsTy →
      WellTypedScalarOperand body topFrame rhsOp rhsTy →
      WellTypedScalarBinOp body.layouts body.localDecls bop lhsTy rhsTy dstTy →
      WellTypedScalarRvalue body topFrame (.binaryOp bop lhsOp rhsOp) dstTy

theorem WellTypedScalarRvalue.mono_immediate
    {body : CapturedMir}
    {tf tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {rv : MirAst.Rvalue} {ty : Ty}
    (h : WellTypedScalarRvalue body tf rv ty)
    (hmono : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) :
    WellTypedScalarRvalue body tf' rv ty := by
  cases h with
  | use op _ hop => exact .use op ty (hop.mono_immediate hmono)
  | unaryOp uop op srcTy _ hop huop =>
    exact .unaryOp uop op srcTy ty (hop.mono_immediate hmono) huop
  | binaryOp bop lhsOp rhsOp lhsTy rhsTy _ hlhs hrhs hbop =>
    exact .binaryOp bop lhsOp rhsOp lhsTy rhsTy ty
      (hlhs.mono_immediate hmono) (hrhs.mono_immediate hmono) hbop

/-- Syntactic well-typedness of a scalar `MirAst.Statement` in `LM-1.1`, covering
`nop`, `storageLive`, `storageDead`, and `assign` of constants, copies,
unary `Neg`/`Not`, and arithmetic/checked/comparison/bitwise/shift binary operators. -/
inductive WellTypedScalarStmt
    (body : CapturedMir)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    MirAst.Statement → Prop where
  | nop (stmt : Statement) :
      stmt.kind = .nop →
      WellTypedScalarStmt body topFrame stmt
  | storageLive (stmt : Statement) (loc : Local) (decl : LocalDecl) :
      stmt.kind = .storageLive loc →
      get? body.localDecls loc = some decl →
      IsImmediateFrameLocal topFrame loc →
      WellTypedScalarStmt body topFrame stmt
  /-- `StorageDead` of the return place `_0` is excluded: rustc's MIR validator
  forbids it, and `lean-miri` rejects it with `cannotMakeReturnPlaceDead`
  while Anneal accepts it. -/
  | storageDead (stmt : Statement) (loc : Local) (decl : LocalDecl) :
      stmt.kind = .storageDead loc →
      get? body.localDecls loc = some decl →
      loc ≠ 0 →
      IsImmediateFrameLocal topFrame loc →
      WellTypedScalarStmt body topFrame stmt
  | assign (stmt : Statement) (dstIdx : Local) (dstDecl : LocalDecl) (rv : MirAst.Rvalue) :
      stmt.kind = .assign ⟨dstIdx, .nil⟩ rv →
      get? body.localDecls dstIdx = some dstDecl →
      IsImmediateFrameLocal topFrame dstIdx →
      WellTypedScalarRvalue body topFrame rv dstDecl.ty →
      WellTypedScalarStmt body topFrame stmt

theorem assertRvalueLayoutPub_eq_ok
    (lay₁ lay₂ : Miri.ABI.TyAndLayout Miri.MIR.TyId)
    (h : lay₁ = lay₂) (m : AnnealStepState) :
    assertRvalueLayoutPub lay₁ lay₂ m = .ok () m := by
  subst h
  with_unfolding_all
    unfold assertRvalueLayoutPub
    simp [Pure.pure, EStateM.pure]

theorem miri_step_at_statement_error
    {PlaceTy : Type}
    (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit PlaceTy)
    {body : CapturedMir} {m m' : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData} {stmt : Statement}
    {err : Miri.Interpreter.StepError}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hstmt : get? bb.statements stmtIdx = some stmt)
    (heval : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = (m', .error err)) :
    Miri.Interpreter.Step.step hooks () m = (m', .error err) := by
  unfold Miri.Interpreter.Step.step
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map]
  rw [translateBasicBlockData_statements_getElem?, hstmt]
  dsimp only [Option.map]
  rw [heval]
  rfl

theorem miri_step_at_statement_ok
    {PlaceTy : Type}
    (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit PlaceTy)
    {body : CapturedMir} {m m' : AnnealStepState}
    {topFrame topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData} {stmt : Statement}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hstmt : get? bb.statements stmtIdx = some stmt)
    (heval : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = (m', .ok ()))
    (hframes' : m'.stack.frames = #[topFrame'])
    (hloc' : topFrame'.location = .mir ⟨blockIdx, stmtIdx⟩) :
    Miri.Interpreter.Step.step hooks () m =
      ({ m' with stack := ⟨#[{ topFrame' with location := .mir ⟨blockIdx, stmtIdx + 1⟩ }]⟩ },
        .ok true) := by
  unfold Miri.Interpreter.Step.step
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map]
  rw [translateBasicBlockData_statements_getElem?, hstmt]
  dsimp only [Option.map]
  rw [heval, stack_currentFrame?_singleton m'.stack topFrame' hframes']
  dsimp only
  rw [hloc', hframes, hframes']
  rfl

theorem write_after_rvalue_simulation_ext
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {tf₀ topFrame₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {locals₁ : List LocalSlot}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {val : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    {id0 : Miri.Interpreter.LocalsIdentity}
    {bb : BasicBlockData} {stmt : Statement}
    (hretCont : topFrame₁.returnContinuation = .stop false)
    (hretPlace : ∃ retLay, topFrame₁.returnPlace = .frameLocal 0 0 none retLay topFrame₁.localsIdentity)
    (hcal : s.memory.activeCallee = none)
    (hstack : s.memory.callStack = .nil)
    (hbor : s.memory.borrows = .nil)
    (hprot : s.memory.activeProtectors = .nil)
    (hcaller : s.memory.callerLocals = .nil)
    (hframes : m.stack.frames = #[tf₀])
    (hbody₀ : tf₀.body = translateBody body)
    (hloc₀ : tf₀.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hmono_prev : ∀ j, IsImmediateFrameLocal tf₀ j → IsImmediateFrameLocal topFrame₁ j)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hframe₁ : FrameRel body m.machine { s.frame with locals := locals₁ } topFrame₁)
    (hdisj : MemoryAllocDisjoint topFrame₁)
    (hdecl : get? body.localDecls dstIdx = some dstDecl)
    (himm_dst : IsImmediateFrameLocal topFrame₁ dstIdx)
    (himmRel : ImmediateRel dstDecl.ty body.layouts val imm)
    (heval_a : evalStmt s stmt body.localDecls body.layouts =
      match get? locals₁ dstIdx with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? locals₁ dstIdx (.init val) with
        | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub)
    (heval_m : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate imm ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[topFrame₁]⟩ }) :
    StepRel body m
      (evalStmt s stmt body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ j, IsImmediateFrameLocal tf₀ j →
      ∀ tf',
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames = #[tf'] →
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 = .ok true →
        IsImmediateFrameLocal tf' j) := by
  obtain ⟨slot_d, mls_d, hlt_af, hlt_mf, hslot_d, hmls_d, hmls_eq, hloc_d⟩ :=
    hframe₁.lookup_local hdecl
  have hget_d := frame_getLocal_of_getElem? topFrame₁ dstIdx mls_d hmls_d
  have himm_d := himm_dst mls_d hmls_d
  dsimp only at hslot_d hlt_af
  rw [heval_a, hslot_d]
  cases hloc_d with
  | dead cachedLayout _ =>
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
        ({ m with stack := ⟨#[topFrame₁]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
      rw [heval_m]
      unfold Miri.Interpreter.runRvalue
      rw [annealWriteImmediate_dead (topFrame := topFrame₁) rfl hget_d]
    rw [miri_step_at_statement_error _ hframes hbody₀ hloc₀ hbb hstmt hm_err]
    exact ⟨.ub _ _, fun _ _ _ _ hok => nomatch hok⟩
  | indirect _ mp _ _ _ _ =>
    exact False.elim (himm_d mp rfl)
  | immediate _ imm_old cachedLayout hc hval =>
    have hnot_dead : (match some slot_d with
        | .some .dead => MirStepNode.fail .ub
        | .some _ =>
          match set? locals₁ dstIdx (.init val) with
          | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
          | .none => MirStepNode.fail .ub
        | .none => MirStepNode.fail .ub) =
        MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init val)) s.memory) := by
      rcases hval with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;>
        simp [set?_eq_some_set hlt_af]
    rw [hnot_dead]
    let topFrame₂ :=
      { topFrame₁ with
        locals := topFrame₁.locals.set dstIdx
          { topFrame₁.locals[dstIdx]'hlt_mf with value := .live (.immediate imm) } hlt_mf }
    have hm_ok : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
        ({ m with stack := ⟨#[topFrame₂]⟩ }, .ok ()) := by
      rw [heval_m]
      unfold Miri.Interpreter.runRvalue
      rw [annealWriteImmediate_live (topFrame := topFrame₁) rfl hlt_mf hget_d]
    have hloc₁ : topFrame₂.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
      hframe₁.location_eq
    rw [miri_step_at_statement_ok _ hframes hbody₀ hloc₀ hbb hstmt hm_ok rfl hloc₁]
    refine ⟨?_, ?_⟩
    · apply StepRel.step
      have hloc_new : LocalRel m.machine dstDecl body.layouts (.init val)
          { topFrame₁.locals[dstIdx]'hlt_mf with value := .live (.immediate imm) } := by
        rw [hmls_eq]
        exact .immediate (.init val) imm cachedLayout hc (Or.inr ⟨val, rfl, himmRel⟩)
      have hfr₂ := hframe₁.update_local hdecl (.init val) (.live (.immediate imm)) hloc_new
      obtain ⟨retLay, hretP⟩ := hretPlace
      exact StateRel.mk
        { topFrame₂ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
        rfl hretCont ⟨retLay, hretP⟩
        ⟨hfr₂.body_eq, rfl, hfr₂.af_locals_len, hfr₂.mf_locals_size, hfr₂.locals_rel⟩
        hcal hstack hbor hprot hcaller (by
          apply MemoryAllocDisjoint.mono_immediate hdisj
          intro k
          by_cases hk : k = dstIdx
          · subst hk
            right
            exists imm, topFrame₁.locals[k].layout
            dsimp [topFrame₂]
            rw [Array.getElem?_set]
            rw [if_pos rfl]
          · left
            dsimp [topFrame₂]
            rw [Array.getElem?_set_ne _ (Ne.symm hk)])
    · intro j hj tf' htf' _
      dsimp only at htf'
      have h_eq : { topFrame₂ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ } = tf' := by
        injection htf' with h_arr
        injection h_arr with h_hd _
      subst h_eq
      exact (hmono_prev j hj).set_immediate hlt_mf imm

theorem scalarOps_unary_simulation
    {body : CapturedMir} {locals₁ : List LocalSlot} {mem : Memory}
    {m₁ : AnnealStepState}
    {uop : MirAst.UnOp} {op : MirAst.Operand} {srcTy dstTy : Ty}
    {v : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    (hop_ty : operandTy body.localDecls body.layouts op = some srcTy)
    (huop : WellTypedScalarUnOp uop srcTy dstTy)
    (himm : ImmediateRel srcTy body.layouts v imm) :
    ∃ sc v' imm',
      v = .scalar sc ∧
      (match uop with
      | .not => evalUnaryNot sc (operandTy body.localDecls body.layouts op) locals₁ mem
      | .neg =>
        match Nat.beq sc.sizeBytes 0 with
        | true => .unsupported
        | false =>
          let mod := scalarModulus sc.sizeBytes
          let can := wrapScalarBits sc.bits mod
          let negB := wrapScalarBits (Nat.sub mod can) mod
          .ok (.scalar ⟨negB, sc.sizeBytes⟩) locals₁ mem
      | .ptrMetadata => .unsupported) = .ok v' locals₁ mem ∧
      (do
        let result ← Miri.Interpreter.ScalarOps.unary
          (annealScalarOpsHooks body.localDecls body.layouts) ()
          (translateUnOp uop) ⟨imm, translateTy srcTy body.layouts⟩
        assertRvalueLayoutPub result.layout (translateTy dstTy body.layouts)
        pure result.imm) m₁ = .ok imm' m₁ ∧
      ImmediateRel dstTy body.layouts v' imm' := by
  cases huop with
  | intNot _ _ kind hsrc hdst =>
    obtain ⟨sc, msc, rfl, rfl, hrel, hsz, _, _⟩ := himm.of_primitive_scalar hsrc.prim
    obtain ⟨sc', msc', ha_not, hm_not, hrel'⟩ :=
      (evalUnOp_neg_not_simulation hrel locals₁ mem).1 kind srcTy hsrc.not_kinds
    have hsc'_sz : (translateTy dstTy body.layouts).layout.size = translateSizeBytes sc'.sizeBytes := by
      have hm_eq := hm_not
      rw [integerOps_unary_eq hrel kind .Not] at hm_eq
      dsimp only [bind, Except.bind, pure, Except.pure] at hm_eq
      obtain ⟨v0, lossy, htr, hv0_rel, _⟩ :=
        truncateInt_spec hrel.validBytes kind (~~~decodeBitsInt kind.signed sc.sizeBytes sc.bits)
      simp only [htr, Except.ok.injEq] at hm_eq
      subst hm_eq
      rw [← hsrc.translateTy_eq hdst body.layouts body.layouts, hsz, ← hv0_rel.size_eq, hrel'.size_eq]
    have hm_unary : Miri.Interpreter.ScalarOps.unary
        (annealScalarOpsHooks body.localDecls body.layouts) () .Not
        ⟨.scalar (.fromScalarInt msc), translateTy srcTy body.layouts⟩ m₁ =
        .ok ⟨.scalar (.fromScalarInt msc'), translateTy srcTy body.layouts⟩ m₁ := by
      rw [scalarOps_unary_def]
      have hcls : (annealScalarOpsHooks body.localDecls body.layouts).classify ()
          (translateTy srcTy body.layouts).ty m₁ =
          .ok (.integer kind) m₁ := by
        with_unfolding_all
          unfold annealScalarOpsHooks translateTy
          simp [hsrc.classify, Pure.pure, EStateM.pure]
      rw [EStateM.bind_eq_ok hcls]
      dsimp only
      rw [EStateM.bind_eq_ok (scalarOps_toInteger_eq hrel hsz m₁)]
      with_unfolding_all
        unfold liftScalarResult
        simp only [hm_not, Except.mapError, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    refine ⟨sc, .scalar sc', .scalar (.fromScalarInt msc'), rfl, ?_, ?_,
      .scalar sc' msc' hrel' hsc'_sz (fun hb => False.elim (hdst.ne_bool hb))
        (fun hc => False.elim (hdst.ne_char hc))⟩
    · rw [hop_ty]; exact ha_not
    · dsimp only [translateUnOp]
      rw [EStateM.bind_eq_ok hm_unary,
        EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ (hsrc.translateTy_eq hdst _ _) m₁)]
      rfl
  | boolNot _ _ hsrc hdst =>
    obtain ⟨b, msc, rfl, rfl, hrel, htoBool⟩ := bool_of_immediateRel hsrc himm
    have hcls : classifyEncodedTyId (encodeTyId srcTy) = .ok .boolean := by
      simp [encodeTyId, classifyEncodedTyId, hsrc]
    have hm_unary : Miri.Interpreter.ScalarOps.unary
        (annealScalarOpsHooks body.localDecls body.layouts) () .Not
        ⟨.scalar (.fromScalarInt msc), translateTy srcTy body.layouts⟩ m₁ =
        .ok ⟨.scalar (.fromScalarInt (.ofBool (!b))), translateTy dstTy body.layouts⟩ m₁ := by
      rw [scalarOps_unary_def, translateTy_bool_eq hdst body.layouts]
      with_unfolding_all
        unfold annealScalarOpsHooks scalarOpsToScalar liftScalarResult scalarOpsFinish
          Miri.Interpreter.Immediate.toScalar Miri.Memory.Scalar.fromBool
        simp only [translateTy, hcls, htoBool,
          Except.mapError, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    have ha_not : evalUnaryNot (boolToScalar b) (some srcTy) locals₁ mem =
        .ok (.scalar (boolToScalar (!b))) locals₁ mem := by
      unfold evalUnaryNot
      dsimp only
      rw [hsrc]
      cases b <;> rfl
    refine ⟨boolToScalar b, .scalar (boolToScalar (!b)), .scalar (.fromScalarInt (.ofBool (!b))), rfl, ?_, ?_, ?_⟩
    · rw [hop_ty]; exact ha_not
    · dsimp only [translateUnOp]
      rw [EStateM.bind_eq_ok hm_unary,
        EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ rfl m₁)]
      rfl
    · refine .scalar (boolToScalar (!b)) (.ofBool (!b)) (ScalarRel.of_boolToScalar (!b)) ?_ ?_
        (fun hc => by rw [hdst] at hc; cases hc)
      · simp [translateTy, hdst, scalarLayoutData, boolToScalar]
        cases b <;> rfl
      · intro _; cases b <;> simp [boolToScalar]
  | intNeg _ _ kind hsrc hdst hsigned =>
    obtain ⟨sc, msc, rfl, rfl, hrel, hsz, _, _⟩ := himm.of_primitive_scalar hsrc.prim
    obtain ⟨msc', hm_neg, hrel'⟩ :=
      (evalUnOp_neg_not_simulation hrel locals₁ mem).2.1 kind hsigned
    let mod := scalarModulus sc.sizeBytes
    let negSc : MirAst.ScalarInt := ⟨wrapScalarBits (mod - wrapScalarBits sc.bits mod) mod, sc.sizeBytes⟩
    have hsz_dst : (translateTy dstTy body.layouts).layout.size = translateSizeBytes negSc.sizeBytes := by
      rw [← hsrc.translateTy_eq hdst body.layouts body.layouts, hsz]
    have hm_unary : Miri.Interpreter.ScalarOps.unary
        (annealScalarOpsHooks body.localDecls body.layouts) () .Neg
        ⟨.scalar (.fromScalarInt msc), translateTy srcTy body.layouts⟩ m₁ =
        .ok ⟨.scalar (.fromScalarInt msc'), translateTy srcTy body.layouts⟩ m₁ := by
      rw [scalarOps_unary_def]
      have hcls : (annealScalarOpsHooks body.localDecls body.layouts).classify ()
          (translateTy srcTy body.layouts).ty m₁ =
          .ok (.integer kind) m₁ := by
        with_unfolding_all
          unfold annealScalarOpsHooks translateTy
          simp [hsrc.classify, Pure.pure, EStateM.pure]
      rw [EStateM.bind_eq_ok hcls]
      dsimp only
      rw [EStateM.bind_eq_ok (scalarOps_toInteger_eq hrel hsz m₁)]
      with_unfolding_all
        unfold liftScalarResult
        simp only [hm_neg, Except.mapError, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    refine ⟨sc, .scalar negSc, .scalar (.fromScalarInt msc'), rfl, ?_, ?_,
      .scalar negSc msc' hrel' hsz_dst (fun hb => False.elim (hdst.ne_bool hb))
        (fun hc => False.elim (hdst.ne_char hc))⟩
    · simp only [hrel.beq_sizeBytes_zero, Nat.sub_eq]
      rfl
    · dsimp only [translateUnOp]
      rw [EStateM.bind_eq_ok hm_unary,
        EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ (hsrc.translateTy_eq hdst _ _) m₁)]
      rfl

/-- Outcome correspondence for `ScalarOps.binary >>= assertRvalueLayoutPub` vs `evalScalarBinOp`. -/
inductive BinaryRvalueSimRel (dstTy : Ty) (layouts : LayoutTable)
    (locals₂ : List LocalSlot) (mem : Memory) (m₂ : AnnealStepState) :
    RvalueEvalResult →
    EStateM.Result Miri.Interpreter.StepError AnnealStepState
      (Miri.Interpreter.Immediate AnnealProv) →
    Prop where
  | ok (v' : Value) (imm' : Miri.Interpreter.Immediate AnnealProv) :
      ImmediateRel dstTy layouts v' imm' →
      BinaryRvalueSimRel dstTy layouts locals₂ mem m₂
        (.ok v' locals₂ mem) (.ok imm' m₂)
  | ub (msg : String) :
      BinaryRvalueSimRel dstTy layouts locals₂ mem m₂
        .ub (.error (.undefinedBehavior msg) m₂)

theorem scalarOps_binary_integer_step
    (localDecls : List LocalDecl)
    {bop : MirAst.BinOp} {lhsTy rhsTy : Ty} {layouts : LayoutTable}
    {kind₁ kind₂ : Miri.MIR.IntegerKind}
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hlhs : IsIntegralTy lhsTy kind₁) (hrhs : IsIntegralTy rhsTy kind₂)
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (hsz₁ : (translateTy lhsTy layouts).layout.size = translateSizeBytes sc₁.sizeBytes)
    (hsz₂ : (translateTy rhsTy layouts).layout.size = translateSizeBytes sc₂.sizeBytes)
    (hsame_or_shift : scalarOpsIsShift (translateBinOp bop) = true ∨
      (translateTy lhsTy layouts).ty = (translateTy rhsTy layouts).ty)
    (m₂ : AnnealStepState) :
    Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks localDecls layouts) ()
      (translateBinOp bop)
      ⟨.scalar (.fromScalarInt msc₁), translateTy lhsTy layouts⟩
      ⟨.scalar (.fromScalarInt msc₂), translateTy rhsTy layouts⟩ m₂ =
      (do
        let result ← liftScalarResult
          (Miri.Interpreter.IntegerOps.binary (translateBinOp bop)
            ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind₁⟩⟩
            ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind₂⟩⟩
            |>.mapError Miri.Interpreter.ScalarOps.integerError)
        scalarOpsFinish (annealScalarOpsHooks localDecls layouts) ()
          (translateTy lhsTy layouts) result) m₂ := by
  have htoInt₁ := scalarOps_toInteger_eq (kind := kind₁) hrel₁ hsz₁ m₂
  have htoInt₂ := scalarOps_toInteger_eq (kind := kind₂) hrel₂ hsz₂ m₂
  have hcls₁ : (annealScalarOpsHooks localDecls layouts).classify ()
      (translateTy lhsTy layouts).ty m₂ =
      .ok (.integer kind₁) m₂ := by
    with_unfolding_all
      unfold annealScalarOpsHooks translateTy
      simp [hlhs.classify, Pure.pure, EStateM.pure]
  have hcls₂ : (annealScalarOpsHooks localDecls layouts).classify ()
      (translateTy rhsTy layouts).ty m₂ =
      .ok (.integer kind₂) m₂ := by
    with_unfolding_all
      unfold annealScalarOpsHooks translateTy
      simp [hrhs.classify, Pure.pure, EStateM.pure]
  rw [scalarOps_binary_def]
  rw [EStateM.bind_eq_ok hcls₁]
  dsimp only
  rw [EStateM.bind_eq_ok hcls₂]
  dsimp only
  rw [EStateM.bind_eq_ok htoInt₁, EStateM.bind_eq_ok htoInt₂]
  rcases hsame_or_shift with hsh | hty_eq
  · simp only [hsh, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · cases hsh_b : scalarOpsIsShift (translateBinOp bop)
    · simp only [Bool.not_false, ↓reduceIte]
      have hass : scalarOpsAssertSameType (Prov := AnnealProv)
          ⟨.scalar (.fromScalarInt msc₁), translateTy lhsTy layouts⟩
          ⟨.scalar (.fromScalarInt msc₂), translateTy rhsTy layouts⟩ m₂ = .ok () m₂ := by
        with_unfolding_all
          unfold scalarOpsAssertSameType
          simp [hty_eq, Pure.pure, EStateM.pure]
      rw [EStateM.bind_eq_ok hass]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem scalarOps_binary_simulation
    {body : CapturedMir} {locals₂ : List LocalSlot} {mem : Memory}
    {m₂ : AnnealStepState}
    {bop : MirAst.BinOp} {lhsOp : MirAst.Operand} {lhsTy rhsTy dstTy : Ty}
    {v₁ v₂ : Value} {imm₁ imm₂ : Miri.Interpreter.Immediate AnnealProv}
    (hlhs_op : operandTy body.localDecls body.layouts lhsOp = some lhsTy)
    (hbop : WellTypedScalarBinOp body.layouts body.localDecls bop lhsTy rhsTy dstTy)
    (himm₁ : ImmediateRel lhsTy body.layouts v₁ imm₁)
    (himm₂ : ImmediateRel rhsTy body.layouts v₂ imm₂) :
    ∃ v₁_sc v₂_sc,
      v₁ = .scalar v₁_sc ∧ v₂ = .scalar v₂_sc ∧
      BinaryRvalueSimRel dstTy body.layouts locals₂ mem m₂
        (evalScalarBinOp bop v₁_sc v₂_sc locals₂ mem
          (operandIsSigned body.localDecls lhsOp body.layouts))
        ((do
          let result ← Miri.Interpreter.ScalarOps.binary
            (annealScalarOpsHooks body.localDecls body.layouts) ()
            (translateBinOp bop)
            ⟨imm₁, translateTy lhsTy body.layouts⟩
            ⟨imm₂, translateTy rhsTy body.layouts⟩
          assertRvalueLayoutPub result.layout (translateTy dstTy body.layouts)
          pure result.imm) m₂) := by
  have hisSigned : operandIsSigned body.localDecls lhsOp body.layouts = tyIsSigned lhsTy := by
    simp [hlhs_op]
  rw [hisSigned]
  cases hbop with
  | intArithOrBitwise kind hkind hlhs hrhs hdst =>
    obtain ⟨sc₁, msc₁, rfl, rfl, hrel₁, hsz₁, _, _⟩ := himm₁.of_primitive_scalar hlhs.prim
    obtain ⟨sc₂, msc₂, rfl, rfl, hrel₂, hsz₂, _, _⟩ := himm₂.of_primitive_scalar hrhs.prim
    refine ⟨sc₁, sc₂, rfl, rfl, ?_⟩
    rw [hlhs.signed_eq]
    have hlay_eq := hlhs.translateTy_eq hrhs body.layouts body.layouts
    have hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes := by
      apply translateSizeBytes_inj hrel₁.validBytes hrel₂.validBytes
      rw [← hsz₁, ← hsz₂, hlay_eq]
    have hstep := scalarOps_binary_integer_step body.localDecls (bop := bop) hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂
      (Or.inr (congrArg Miri.ABI.TyAndLayout.ty hlay_eq)) m₂
    obtain ⟨hsz_res, hno_ovf, hno_bool⟩ :=
      integerOps_binary_noncmp_nonovf_shape (Or.inl hkind) hrel₁ hrel₂ kind kind
    have hirel : IntegerBinOpResultRel locals₂ mem
        (evalScalarBinOp bop sc₁ sc₂ locals₂ mem kind.signed)
        (Miri.Interpreter.IntegerOps.binary (translateBinOp bop)
          ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
          ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩) := by
      rcases hkind with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hbw
      · exact evalBinOp_arithmetic_simulation (by simp [IsArithmeticOrCmpBinOp]) rfl hrel₁ hrel₂ hsz_eq kind locals₂ mem
      · exact evalBinOp_arithmetic_simulation (by simp [IsArithmeticOrCmpBinOp]) rfl hrel₁ hrel₂ hsz_eq kind locals₂ mem
      · exact evalBinOp_arithmetic_simulation (by simp [IsArithmeticOrCmpBinOp]) rfl hrel₁ hrel₂ hsz_eq kind locals₂ mem
      · exact evalBinOp_arithmetic_simulation (by simp [IsArithmeticOrCmpBinOp]) rfl hrel₁ hrel₂ hsz_eq kind locals₂ mem
      · exact evalBinOp_arithmetic_simulation (by simp [IsArithmeticOrCmpBinOp]) rfl hrel₁ hrel₂ hsz_eq kind locals₂ mem
      · exact evalBinOp_arithmetic_simulation (by simp [IsArithmeticOrCmpBinOp]) rfl hrel₁ hrel₂ hsz_eq kind locals₂ mem
      · exact evalBinOp_arithmetic_simulation (by simp [IsArithmeticOrCmpBinOp]) rfl hrel₁ hrel₂ hsz_eq kind locals₂ mem
      · exact evalBinOp_arithmetic_simulation (by simp [IsArithmeticOrCmpBinOp]) rfl hrel₁ hrel₂ hsz_eq kind locals₂ mem
      · exact (evalBinOp_bitwise_simulation hbw rfl locals₂ mem).1 kind hrel₁ hrel₂ hsz_eq
    generalize evalScalarBinOp bop sc₁ sc₂ locals₂ mem kind.signed = aRes at hirel ⊢
    generalize Miri.Interpreter.IntegerOps.binary (translateBinOp bop)
      ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
      ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ = binRes at hirel hstep hsz_res hno_ovf hno_bool
    cases hirel with
    | withOverflow msc_a msc' ovf _ => exact False.elim (hno_ovf msc' ovf rfl)
    | boolean b => exact False.elim (hno_bool b rfl)
    | ub reason =>
      have hm_err : Miri.Interpreter.ScalarOps.binary
          (annealScalarOpsHooks body.localDecls body.layouts) () (translateBinOp bop)
          ⟨.scalar (.fromScalarInt msc₁), translateTy lhsTy body.layouts⟩
          ⟨.scalar (.fromScalarInt msc₂), translateTy rhsTy body.layouts⟩ m₂ =
          .error (.undefinedBehavior s!"{repr reason}") m₂ := by
        rw [hstep]
        with_unfolding_all
          unfold liftScalarResult Miri.Interpreter.ScalarOps.integerError
          simp [Except.mapError, Bind.bind, EStateM.bind]
          rfl
      rw [EStateM.bind_eq_error hm_err]
      exact .ub _
    | scalar sc' msc' hrel' =>
      have hm_ok : Miri.Interpreter.ScalarOps.binary
          (annealScalarOpsHooks body.localDecls body.layouts) () (translateBinOp bop)
          ⟨.scalar (.fromScalarInt msc₁), translateTy lhsTy body.layouts⟩
          ⟨.scalar (.fromScalarInt msc₂), translateTy rhsTy body.layouts⟩ m₂ =
          .ok ⟨.scalar (.fromScalarInt msc'), translateTy lhsTy body.layouts⟩ m₂ := by
        rw [hstep]
        with_unfolding_all
          unfold liftScalarResult scalarOpsFinish
          simp [Except.mapError, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      rw [EStateM.bind_eq_ok hm_ok,
        EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ (hlhs.translateTy_eq hdst _ _) m₂)]
      have hsz_dst : (translateTy dstTy body.layouts).layout.size = translateSizeBytes sc'.sizeBytes := by
        have hmsc'_sz := hsz_res msc' rfl
        rw [← hlhs.translateTy_eq hdst body.layouts body.layouts, hsz₁, ← hmsc'_sz, hrel'.size_eq]
      exact .ok (.scalar sc') (.scalar (.fromScalarInt msc'))
        (.scalar sc' msc' hrel' hsz_dst (fun hb => False.elim (hdst.ne_bool hb))
          (fun hc => False.elim (hdst.ne_char hc)))
  | intCmp kind hcmp hlhs hrhs hdst_bool =>
    obtain ⟨sc₁, msc₁, rfl, rfl, hrel₁, hsz₁, _, _⟩ := himm₁.of_primitive_scalar hlhs.prim
    obtain ⟨sc₂, msc₂, rfl, rfl, hrel₂, hsz₂, _, _⟩ := himm₂.of_primitive_scalar hrhs.prim
    refine ⟨sc₁, sc₂, rfl, rfl, ?_⟩
    rw [hlhs.signed_eq]
    have hlay_eq := hlhs.translateTy_eq hrhs body.layouts body.layouts
    have hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes := by
      apply translateSizeBytes_inj hrel₁.validBytes hrel₂.validBytes
      rw [← hsz₁, ← hsz₂, hlay_eq]
    have hstep := scalarOps_binary_integer_step body.localDecls (bop := bop) hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂
      (Or.inr (congrArg Miri.ABI.TyAndLayout.ty hlay_eq)) m₂
    obtain ⟨hno_sc, hno_ovf⟩ := integerOps_binary_cmp_shape hcmp hrel₁ hrel₂ kind kind
    have harith : IsArithmeticOrCmpBinOp bop := by
      rcases hcmp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [IsArithmeticOrCmpBinOp]
    have hirel := evalBinOp_arithmetic_simulation harith rfl hrel₁ hrel₂ hsz_eq kind locals₂ mem
    generalize evalScalarBinOp bop sc₁ sc₂ locals₂ mem kind.signed = aRes at hirel ⊢
    generalize Miri.Interpreter.IntegerOps.binary (translateBinOp bop)
      ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
      ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ = binRes at hirel hstep hno_sc hno_ovf
    cases hirel with
    | scalar _ msc' _ => exact False.elim (hno_sc msc' rfl)
    | withOverflow _ msc' ovf _ => exact False.elim (hno_ovf msc' ovf rfl)
    | ub reason =>
      have hm_err : Miri.Interpreter.ScalarOps.binary
          (annealScalarOpsHooks body.localDecls body.layouts) () (translateBinOp bop)
          ⟨.scalar (.fromScalarInt msc₁), translateTy lhsTy body.layouts⟩
          ⟨.scalar (.fromScalarInt msc₂), translateTy rhsTy body.layouts⟩ m₂ =
          .error (.undefinedBehavior s!"{repr reason}") m₂ := by
        rw [hstep]
        with_unfolding_all
          unfold liftScalarResult Miri.Interpreter.ScalarOps.integerError
          simp [Except.mapError, Bind.bind, EStateM.bind]
          rfl
      rw [EStateM.bind_eq_error hm_err]
      exact .ub _
    | boolean b =>
      have hm_ok : Miri.Interpreter.ScalarOps.binary
          (annealScalarOpsHooks body.localDecls body.layouts) () (translateBinOp bop)
          ⟨.scalar (.fromScalarInt msc₁), translateTy lhsTy body.layouts⟩
          ⟨.scalar (.fromScalarInt msc₂), translateTy rhsTy body.layouts⟩ m₂ =
          .ok ⟨.scalar (.fromScalarInt (.ofBool b)), translateTy dstTy body.layouts⟩ m₂ := by
        rw [hstep]
        with_unfolding_all
          unfold liftScalarResult scalarOpsFinish
            annealScalarOpsHooks Miri.Memory.Scalar.fromBool
          simp [translateTy_bool_eq hdst_bool body.layouts, Except.mapError,
            Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      rw [EStateM.bind_eq_ok hm_ok, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ rfl m₂)]
      refine .ok (.scalar (boolToScalar b)) (.scalar (.fromScalarInt (.ofBool b)))
        (.scalar (boolToScalar b) (.ofBool b) (ScalarRel.of_boolToScalar b) ?_ ?_
          (fun hc => by rw [hdst_bool] at hc; cases hc))
      · simp [translateTy, hdst_bool, scalarLayoutData, boolToScalar]
        cases b <;> rfl
      · intro _; cases b <;> simp [boolToScalar]
  | intWithOverflow kind hovf hlhs hrhs hdst_agg hdst_lay =>
    obtain ⟨sc₁, msc₁, rfl, rfl, hrel₁, hsz₁, _, _⟩ := himm₁.of_primitive_scalar hlhs.prim
    obtain ⟨sc₂, msc₂, rfl, rfl, hrel₂, hsz₂, _, _⟩ := himm₂.of_primitive_scalar hrhs.prim
    refine ⟨sc₁, sc₂, rfl, rfl, ?_⟩
    rw [hlhs.signed_eq]
    have hlay_eq := hlhs.translateTy_eq hrhs body.layouts body.layouts
    have hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes := by
      apply translateSizeBytes_inj hrel₁.validBytes hrel₂.validBytes
      rw [← hsz₁, ← hsz₂, hlay_eq]
    have hstep := scalarOps_binary_integer_step body.localDecls (bop := bop) hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂
      (Or.inr (congrArg Miri.ABI.TyAndLayout.ty hlay_eq)) m₂
    obtain ⟨hno_sc, hno_bool, hno_ub⟩ :=
      integerOps_binary_withOverflow_shape hovf hrel₁ hrel₂ kind kind
    have harith : IsArithmeticOrCmpBinOp bop := by
      rcases hovf with rfl | rfl | rfl <;> simp [IsArithmeticOrCmpBinOp]
    have hirel := evalBinOp_arithmetic_simulation harith rfl hrel₁ hrel₂ hsz_eq kind locals₂ mem
    generalize evalScalarBinOp bop sc₁ sc₂ locals₂ mem kind.signed = aRes at hirel ⊢
    generalize Miri.Interpreter.IntegerOps.binary (translateBinOp bop)
      ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
      ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ = binRes at hirel hstep hno_sc hno_bool hno_ub
    cases hirel with
    | scalar _ msc' _ => exact False.elim (hno_sc msc' rfl)
    | boolean b => exact False.elim (hno_bool b rfl)
    | ub reason => exact False.elim (hno_ub reason rfl)
    | withOverflow sc' msc' b hrel' =>
      have hm_ok : Miri.Interpreter.ScalarOps.binary
          (annealScalarOpsHooks body.localDecls body.layouts) () (translateBinOp bop)
          ⟨.scalar (.fromScalarInt msc₁), translateTy lhsTy body.layouts⟩
          ⟨.scalar (.fromScalarInt msc₂), translateTy rhsTy body.layouts⟩ m₂ =
          .ok ⟨.scalarPair (.fromScalarInt msc') (.fromScalarInt (.ofBool b)),
            translateTy dstTy body.layouts⟩ m₂ := by
        rw [hstep]
        with_unfolding_all
          unfold liftScalarResult scalarOpsFinish
            annealScalarOpsHooks Miri.Memory.Scalar.fromBool
          simp [hdst_lay, Except.mapError, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      rw [EStateM.bind_eq_ok hm_ok, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ rfl m₂)]
      exact .ok _ _ (.scalarPair sc' (boolToScalar b) msc' (.ofBool b)
        hrel' (ScalarRel.of_boolToScalar b) hdst_agg
        (fun _ _ => by cases b <;> simp [boolToScalar]))
  | intShift kind₁ kind₂ hsh hlhs hrhs hdst =>
    obtain ⟨sc₁, msc₁, rfl, rfl, hrel₁, hsz₁, _, _⟩ := himm₁.of_primitive_scalar hlhs.prim
    obtain ⟨sc₂, msc₂, rfl, rfl, hrel₂, hsz₂, _, _⟩ := himm₂.of_primitive_scalar hrhs.prim
    refine ⟨sc₁, sc₂, rfl, rfl, ?_⟩
    rw [hlhs.signed_eq]
    have his_sh : scalarOpsIsShift (translateBinOp bop) = true := by
      rcases hsh with rfl | rfl | rfl | rfl <;> rfl
    have hstep := scalarOps_binary_integer_step body.localDecls (bop := bop) hlhs hrhs hrel₁ hrel₂ hsz₁ hsz₂
      (Or.inl his_sh) m₂
    obtain ⟨hsz_res, hno_ovf, hno_bool⟩ :=
      integerOps_binary_noncmp_nonovf_shape (Or.inr hsh) hrel₁ hrel₂ kind₁ kind₂
    have hirel := evalBinOp_shift_simulation hsh rfl hrel₁ hrel₂ kind₁ kind₂ locals₂ mem
    generalize evalScalarBinOp bop sc₁ sc₂ locals₂ mem kind₁.signed = aRes at hirel ⊢
    generalize Miri.Interpreter.IntegerOps.binary (translateBinOp bop)
      ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind₁⟩⟩
      ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind₂⟩⟩ = binRes at hirel hstep hsz_res hno_ovf hno_bool
    cases hirel with
    | withOverflow _ msc' ovf _ => exact False.elim (hno_ovf msc' ovf rfl)
    | boolean b => exact False.elim (hno_bool b rfl)
    | ub reason =>
      have hm_err : Miri.Interpreter.ScalarOps.binary
          (annealScalarOpsHooks body.localDecls body.layouts) () (translateBinOp bop)
          ⟨.scalar (.fromScalarInt msc₁), translateTy lhsTy body.layouts⟩
          ⟨.scalar (.fromScalarInt msc₂), translateTy rhsTy body.layouts⟩ m₂ =
          .error (.undefinedBehavior s!"{repr reason}") m₂ := by
        rw [hstep]
        with_unfolding_all
          unfold liftScalarResult Miri.Interpreter.ScalarOps.integerError
          simp [Except.mapError, Bind.bind, EStateM.bind]
          rfl
      rw [EStateM.bind_eq_error hm_err]
      exact .ub _
    | scalar sc' msc' hrel' =>
      have hm_ok : Miri.Interpreter.ScalarOps.binary
          (annealScalarOpsHooks body.localDecls body.layouts) () (translateBinOp bop)
          ⟨.scalar (.fromScalarInt msc₁), translateTy lhsTy body.layouts⟩
          ⟨.scalar (.fromScalarInt msc₂), translateTy rhsTy body.layouts⟩ m₂ =
          .ok ⟨.scalar (.fromScalarInt msc'), translateTy lhsTy body.layouts⟩ m₂ := by
        rw [hstep]
        with_unfolding_all
          unfold liftScalarResult scalarOpsFinish
          simp [Except.mapError, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      rw [EStateM.bind_eq_ok hm_ok,
        EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ (hlhs.translateTy_eq hdst _ _) m₂)]
      have hsz_dst : (translateTy dstTy body.layouts).layout.size = translateSizeBytes sc'.sizeBytes := by
        have hmsc'_sz := hsz_res msc' rfl
        rw [← hlhs.translateTy_eq hdst body.layouts body.layouts, hsz₁, ← hmsc'_sz, hrel'.size_eq]
      exact .ok (.scalar sc') (.scalar (.fromScalarInt msc'))
        (.scalar sc' msc' hrel' hsz_dst (fun hb => False.elim (hdst.ne_bool hb))
          (fun hc => False.elim (hdst.ne_char hc)))
  | boolBitwise hbw hlhs_b hrhs_b hdst_b =>
    obtain ⟨b₁, msc₁, rfl, rfl, hrel₁, htoB₁⟩ := bool_of_immediateRel hlhs_b himm₁
    obtain ⟨b₂, msc₂, rfl, rfl, hrel₂, htoB₂⟩ := bool_of_immediateRel hrhs_b himm₂
    refine ⟨boolToScalar b₁, boolToScalar b₂, rfl, rfl, ?_⟩
    have hnot_signed : tyIsSigned lhsTy = false := by
      rw [tyIsSigned_eq, hlhs_b]
    rw [hnot_signed]
    have hbool_res : ∃ b', Miri.Interpreter.IntegerOps.binaryBool (translateBinOp bop) b₁ b₂ =
        .ok (.boolean b') ∧
        evalScalarBinOp bop (boolToScalar b₁) (boolToScalar b₂) locals₂ mem false =
          .ok (.scalar (boolToScalar b')) locals₂ mem := by
      rcases hbw with rfl | rfl | rfl <;>
        cases b₁ <;> cases b₂ <;>
        simp [evalScalarBinOp, boolToScalar, Miri.Interpreter.IntegerOps.binaryBool,
          translateBinOp, bitwiseAndBits, bitwiseOrBits, bitwiseXorBits,
          bind, Except.bind, pure, Except.pure]
    obtain ⟨b', hm_bb, ha_bb⟩ := hbool_res
    have hm_ok : Miri.Interpreter.ScalarOps.binary
        (annealScalarOpsHooks body.localDecls body.layouts) () (translateBinOp bop)
        ⟨.scalar (.fromScalarInt msc₁), translateTy lhsTy body.layouts⟩
        ⟨.scalar (.fromScalarInt msc₂), translateTy rhsTy body.layouts⟩ m₂ =
        .ok ⟨.scalar (.fromScalarInt (.ofBool b')), translateTy dstTy body.layouts⟩ m₂ := by
      rw [scalarOps_binary_def, translateTy_bool_eq hdst_b body.layouts]
      with_unfolding_all
        unfold annealScalarOpsHooks scalarOpsAssertSameType scalarOpsToScalar
          liftScalarResult scalarOpsFinish Miri.Interpreter.Immediate.toScalar
          Miri.Memory.Scalar.fromBool
        simp [translateTy, encodeTyId, classifyEncodedTyId, hlhs_b, hrhs_b,
          htoB₁, htoB₂, hm_bb, Except.mapError, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    rw [ha_bb, EStateM.bind_eq_ok hm_ok, EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ rfl m₂)]
    refine .ok (.scalar (boolToScalar b')) (.scalar (.fromScalarInt (.ofBool b')))
      (.scalar (boolToScalar b') (.ofBool b') (ScalarRel.of_boolToScalar b') ?_ ?_
        (fun hc => by rw [hdst_b] at hc; cases hc))
    · simp [translateTy, hdst_b, scalarLayoutData, boolToScalar]
      cases b' <;> rfl
    · intro _; cases b' <;> simp [boolToScalar]

/-! ### 5.5 Statement & Terminator Step Simulation Theorems (Theorems 5 & 6) -/

theorem runRvalue_eq_of_eq {S : Type} {f g : Miri.Interpreter.RvalueM S Unit}
    {s₁ s₂ : S} (h : f s₁ = g s₂) :
    Miri.Interpreter.runRvalue f s₁ = Miri.Interpreter.runRvalue g s₂ := by
  unfold Miri.Interpreter.runRvalue
  rw [h]

theorem estate_bind_pure_assoc {ε σ α β γ : Type}
    (act : EStateM ε σ α) (chk : α → EStateM ε σ Unit) (proj : α → β)
    (cont : β → EStateM ε σ γ) (s : σ) :
    ((do let a ← act; chk a; cont (proj a)) s) =
    (((do let a ← act; chk a; pure (proj a)) >>= cont) s) := by
  with_unfolding_all
    simp only [Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
    cases act s with
    | error _ _ => rfl
    | ok a s₁ =>
      dsimp only
      cases chk a s₁ <;> rfl

/-- Theorem 5 (`LM-1.1`): Small-step statement simulation (`step_assign_scalar_simulation`)
between Anneal's `stepMirFn` and `lean-miri`'s `Miri.Interpreter.Step.step` for
`StatementKind.nop`, `StatementKind.storageLive`, `StatementKind.storageDead`, and
`StatementKind.assign` of scalar constants, local copies, unary `Neg`/`Not`,
and arithmetic (`Add`, `Sub`, `Mul`, `Div`, `Rem`), unchecked (`AddUnchecked`,
`SubUnchecked`, `MulUnchecked`), checked (`AddWithOverflow`, `SubWithOverflow`,
`MulWithOverflow`), comparison (`Eq`, `Ne`, `Lt`, `Le`, `Gt`, `Ge`), bitwise
(`BitAnd`, `BitOr`, `BitXor`), and heterogeneous shift (`Shl`, `Shr`,
`ShlUnchecked`, `ShrUnchecked`) operations, with zero vacuous `¬isUB` hypotheses. -/
theorem step_assign_scalar_simulation_ext
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] → WellTypedScalarStmt body topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ j, IsImmediateFrameLocal topFrame j →
        ∀ tf',
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames = #[tf'] →
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 = .ok true →
          IsImmediateFrameLocal tf' j) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hd_tf⟩
  suffices StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ j, IsImmediateFrameLocal topFrame j →
      ∀ tf',
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames = #[tf'] →
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 = .ok true →
        IsImmediateFrameLocal tf' j) by
    refine ⟨this.1, fun tf₀ htf₀ j hj tf' htf' hok => ?_⟩
    rw [hframes] at htf₀
    injection htf₀ with h_arr
    injection h_arr with h_eq _
    subst h_eq
    exact this.2 j hj tf' htf' hok
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hwt' := hwt topFrame hframes
  cases hwt' with
  | nop hkind =>
    have ha : evalStmt s stmt body.localDecls body.layouts =
        MirStepNode.step (advanceStmt s s.frame.locals) := by
      unfold evalStmt; rw [hkind]
    have hm : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
        (m, .ok ()) := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      rw [hkind]; rfl
    rw [ha, miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
      hm hframes hframe.location_eq]
    refine ⟨?_, ?_⟩
    · apply StepRel.step
      exact StateRel.mk
        { topFrame with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
        rfl hretCont ⟨retLay, hretPlace⟩
        ⟨hframe.body_eq, rfl, hframe.af_locals_len, hframe.mf_locals_size, hframe.locals_rel⟩
        hcal hstack hbor hprot hcaller hd_tf
    · intro j hj tf' htf' _
      dsimp only at htf'
      injection htf' with h_arr
      injection h_arr with h_eq _
      subst h_eq
      exact hj
  | storageLive loc decl hkind hdecl himm_loc =>
    obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
    have ha : evalStmt s stmt body.localDecls body.layouts =
        MirStepNode.step (advanceStmt s (s.frame.locals.set loc .uninit)) := by
      unfold evalStmt; rw [hkind]; dsimp only; rw [hslot, set?_eq_some_set hlt_af]
    let topFrame' :=
      { topFrame with
        locals := topFrame.locals.set loc
          { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }
    have hty : ∃ ty, topFrame.body.locals[loc]? = some ty := by
      rw [hframe.body_eq, translateBody_locals_getElem?, hdecl]
      exact ⟨_, rfl⟩
    have hnotInd : ∀ mp, (topFrame.locals[loc]'hlt_mf).value ≠ .live (.indirect mp) := by
      rw [hmls_eq]; exact himm_loc mls hmls
    have hm : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
        ({ m with stack := ⟨#[topFrame']⟩ }, .ok ()) := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      rw [hkind]
      exact annealStepHooks_storageLive_eq hframes hlt_mf hty
    have hloc' : topFrame'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hframe.location_eq
    rw [ha, miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
      hm rfl hloc']
    refine ⟨?_, ?_⟩
    · apply StepRel.step
      have hloc_new : LocalRel m.machine decl body.layouts .uninit
          { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } := by
        rw [hmls_eq]
        exact .immediate .uninit .uninit mls.layout hloc.cachedLayout_eq (Or.inl ⟨rfl, rfl⟩)
      have hfr' := hframe.update_local hdecl .uninit (.live (.immediate .uninit)) hloc_new
      exact StateRel.mk
        { topFrame' with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
        rfl hretCont ⟨retLay, hretPlace⟩
        ⟨hfr'.body_eq, rfl, hfr'.af_locals_len, hfr'.mf_locals_size, hfr'.locals_rel⟩
        hcal hstack hbor hprot hcaller (by
          apply MemoryAllocDisjoint.mono_immediate hd_tf
          intro k
          by_cases hk : k = loc
          · subst hk
            right
            exists .uninit, topFrame.locals[k].layout
            dsimp [topFrame']
            rw [Array.getElem?_set]
            rw [if_pos rfl]
          · left
            dsimp [topFrame']
            rw [Array.getElem?_set_ne _ (Ne.symm hk)])
    · intro j hj tf' htf' _
      dsimp only at htf'
      injection htf' with h_arr
      injection h_arr with h_eq _
      subst h_eq
      exact hj.set_immediate hlt_mf .uninit
  | storageDead loc decl hkind hdecl hne himm_loc =>
    obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
    have ha : evalStmt s stmt body.localDecls body.layouts =
        MirStepNode.step (advanceStmt s (s.frame.locals.set loc .dead)) := by
      unfold evalStmt; rw [hkind]; dsimp only; rw [hslot, set?_eq_some_set hlt_af]
    let topFrame' :=
      { topFrame with
        locals := topFrame.locals.set loc
          { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf }
    have hnotInd : ∀ mp, (topFrame.locals[loc]'hlt_mf).value ≠ .live (.indirect mp) := by
      rw [hmls_eq]; exact himm_loc mls hmls
    have hm : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
        ({ m with stack := ⟨#[topFrame']⟩ }, .ok ()) := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      rw [hkind]
      exact annealStepHooks_storageDead_eq hframes hlt_mf hne
    have hloc' : topFrame'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hframe.location_eq
    rw [ha, miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
      hm rfl hloc']
    refine ⟨?_, ?_⟩
    · apply StepRel.step
      have hloc_new : LocalRel m.machine decl body.layouts .dead
          { topFrame.locals[loc]'hlt_mf with value := .dead } := by
        rw [hmls_eq]
        exact .dead mls.layout hloc.cachedLayout_eq
      have hfr' := hframe.update_local hdecl .dead .dead hloc_new
      exact StateRel.mk
        { topFrame' with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
        rfl hretCont ⟨retLay, hretPlace⟩
        ⟨hfr'.body_eq, rfl, hfr'.af_locals_len, hfr'.mf_locals_size, hfr'.locals_rel⟩
        hcal hstack hbor hprot hcaller (by
          apply MemoryAllocDisjoint.mono_dead hd_tf
          intro k
          by_cases hk : k = loc
          · subst hk
            right
            exists topFrame.locals[k].layout
            dsimp [topFrame']
            rw [Array.getElem?_set]
            rw [if_pos rfl]
          · left
            rw [Array.getElem?_set_ne _ (Ne.symm hk)])
    · intro j hj tf' htf' _
      dsimp only at htf'
      injection htf' with h_arr
      injection h_arr with h_eq _
      subst h_eq
      exact hj.set_dead hlt_mf
  | assign dstIdx dstDecl rv hkind hdecl_dst himm_dst hrv =>
    obtain ⟨_, mls_dst0, _, hlt_dst0, _, hmls_opt, hmls_eq0, hloc_dst0⟩ := hframe.lookup_local hdecl_dst
    let topFrame₀ := cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy dstDecl.ty body.layouts)
    have hdisj_tf₀_inner : MemoryAllocDisjoint topFrame₀ := by
      apply MemoryAllocDisjoint.mono_layout hd_tf
      intro k
      by_cases hk : k = dstIdx
      · subst hk
        exists (translateTy dstDecl.ty body.layouts)
        dsimp [topFrame₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set]
        rw [if_pos rfl]
        rw [hmls_opt, hmls_eq0]
        rfl
      · exists (topFrame.locals[k]?).bind (fun x => x.layout)
        dsimp [topFrame₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ (Ne.symm hk)]
        cases topFrame.locals[k]? <;> rfl
    let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
    have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_eq0]; exact hloc_dst0.layout_eq
    have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
        .ok ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩ m₀ :=
      annealEvalPlace_unprojected hframes hlt_dst0 hdecl_dst hcache_dst0
    have hframe₀ : FrameRel body m₀.machine s.frame topFrame₀ :=
      hframe.cache_local_layout hdecl_dst hlt_dst0
    have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
      fun _ hj => hj.cache_layout hlt_dst0 _
    have htf₀ : topFrame₀ = { topFrame with locals := topFrame₀.locals } := rfl
    have hrv₀ : WellTypedScalarRvalue body topFrame₀ rv dstDecl.ty :=
      hrv.mono_immediate hmono₀
    let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
    have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
      revert hbor hprot
      generalize s.memory = mem
      intro hbor hprot
      cases mem
      dsimp only at hbor hprot
      subst hbor hprot
      rfl
    dsimp only at hmem_same
    cases hrv₀ with
    | use op _ hop =>
      have hop_sim := evalOperand_scalar_simulation (m := m₀) rfl hframe₀ hop
        s.memory.globals (some (translateTy dstDecl.ty body.layouts))
      have hm_eval : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          Miri.Interpreter.runRvalue
            ((annealEvalOperand body.localDecls body.layouts (translateOperand op)
                (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) >>=
              fun imm => annealWriteImmediate imm.imm destPlace) m₀ := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt
        rw [hkind]
        dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
          translateRvalue, annealStepHooks]
        apply runRvalue_eq_of_eq
        unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
        dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
        rw [EStateM.bind_eq_ok hevalPlace_dst]
        exact EStateM.bind_assoc_apply _ _ _ m₀
      generalize ha_op : evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = aOp at hop_sim
      generalize hm_op : (annealEvalOperand body.localDecls body.layouts (translateOperand op)
        (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) m₀ = mOp at hop_sim
      cases hop_sim with
      | ub m' msg =>
        have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; rw [hkind]
          simp [evalRvalue, hbor, hcaller, ha_op]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
            (m', .error (.undefinedBehavior msg)) := by
          rw [hm_eval]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_error hm_op]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
        exact ⟨.ub _ _, fun _ _ _ _ hok => nomatch hok⟩
      | ok val locals₁ topFrame₁ imm hframe₁ himmRel hmono htf₁ hdisj_fn =>
        have ha_ok : evalStmt s stmt body.localDecls body.layouts =
            match get? locals₁ dstIdx with
            | .some .dead => MirStepNode.fail .ub
            | .some _ =>
              match set? locals₁ dstIdx (.init val) with
              | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
              | .none => MirStepNode.fail .ub
            | .none => MirStepNode.fail .ub := by
          unfold evalStmt; rw [hkind]; dsimp only
          have huse : evalRvalue s.frame.locals (.use op) s.memory body.localDecls body.layouts =
              .ok val locals₁ s.memory := by
            unfold evalRvalue
            dsimp only
            rw [hbor, hcaller, ha_op]
            cases op with
            | constant _ => rfl
            | copy p =>
              rcases p with ⟨_, _ | ⟨hd, _⟩⟩
              · rfl
              · cases hd <;> rfl
            | move p =>
              rcases p with ⟨_, _ | ⟨hd, _⟩⟩
              · rfl
              · cases hd <;> rfl
          rw [huse]
          dsimp only
          rw [hprot, hbor]
          dsimp only [invalidateConflictingBorrows]
          rw [hmem_same]; rfl
        have hm_write : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
            Miri.Interpreter.runRvalue
              (annealWriteImmediate imm destPlace)
              { m with stack := ⟨#[topFrame₁]⟩ } := by
          rw [hm_eval]
          apply runRvalue_eq_of_eq
          exact EStateM.bind_eq_ok hm_op
        have hrc₁ : topFrame₁.returnContinuation = .stop false := by
          rw [htf₁, htf₀]; exact hretCont
        have hrp₁ : ∃ rl, topFrame₁.returnPlace = .frameLocal 0 0 none rl topFrame₁.localsIdentity := by
          rw [htf₁, htf₀]; exact ⟨retLay, hretPlace⟩
        have hdisj_tf₁ := hdisj_fn hdisj_tf₀_inner
        exact write_after_rvalue_simulation_ext hrc₁ hrp₁ hcal hstack hbor hprot hcaller
          hframes hframe.body_eq hframe.location_eq (fun j hj => hmono j (hmono₀ j hj))
          hbb hstmt hframe₁ hdisj_tf₁ hdecl_dst (hmono dstIdx (hmono₀ dstIdx himm_dst)) himmRel ha_ok hm_write
    | unaryOp uop op srcTy _ hop huop =>
      let knownU := if (translateUnOp uop).homogeneous then some (translateTy dstDecl.ty body.layouts) else none
      have hop_sim := evalOperand_scalar_simulation (m := m₀) rfl hframe₀ hop s.memory.globals knownU
      have hm_eval : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          Miri.Interpreter.runRvalue
            ((annealEvalOperand body.localDecls body.layouts (translateOperand op) knownU >>=
                annealReadImmediate) >>=
              fun val => do
                let result ← Miri.Interpreter.ScalarOps.unary
                  (annealScalarOpsHooks body.localDecls body.layouts) ()
                  (translateUnOp uop) val
                assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
                annealWriteImmediate result.imm destPlace) m₀ := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt
        rw [hkind]
        dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
          translateRvalue, annealStepHooks]
        apply runRvalue_eq_of_eq
        rw [evalRvalueIntoPlace_unaryOp_def]
        unfold annealRvalueHooks
        dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
        rw [EStateM.bind_eq_ok hevalPlace_dst]
        exact EStateM.bind_assoc_apply _ _ _ m₀
      generalize ha_op : evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = aOp at hop_sim
      generalize hm_op : (annealEvalOperand body.localDecls body.layouts (translateOperand op) knownU >>=
        annealReadImmediate) m₀ = mOp at hop_sim
      cases hop_sim with
      | ub m' msg =>
        have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; rw [hkind]
          cases huop <;> simp [evalRvalue, hbor, hcaller, ha_op]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
            (m', .error (.undefinedBehavior msg)) := by
          rw [hm_eval]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_error hm_op]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
        exact ⟨.ub _ _, fun _ _ _ _ hok => nomatch hok⟩
      | ok val locals₁ topFrame₁ imm hframe₁ himmRel hmono htf₁ hdisj_fn =>
        let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
        obtain ⟨sc, v', imm', rfl, ha_uop, hm_uop, himmRel'⟩ :=
          scalarOps_unary_simulation (locals₁ := locals₁) (mem := s.memory) (m₁ := m₁)
            hop.operandTy_eq huop himmRel
        have ha_ok : evalStmt s stmt body.localDecls body.layouts =
            match get? locals₁ dstIdx with
            | .some .dead => MirStepNode.fail .ub
            | .some _ =>
              match set? locals₁ dstIdx (.init v') with
              | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
              | .none => MirStepNode.fail .ub
            | .none => MirStepNode.fail .ub := by
          unfold evalStmt; rw [hkind]; dsimp only
          have hrv_ok : evalRvalue s.frame.locals (.unaryOp uop op) s.memory body.localDecls body.layouts =
              .ok v' locals₁ s.memory := by
            cases uop with
            | not => unfold evalRvalue; dsimp only; rw [hbor, hcaller, ha_op]; exact ha_uop
            | neg => unfold evalRvalue; dsimp only; rw [hbor, hcaller, ha_op]; exact ha_uop
            | ptrMetadata => cases huop
          rw [hrv_ok]
          dsimp only
          rw [hprot, hbor]
          dsimp only [invalidateConflictingBorrows]
          rw [hmem_same]; rfl
        have hm_write : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
            Miri.Interpreter.runRvalue
              (annealWriteImmediate imm' destPlace)
              m₁ := by
          rw [hm_eval]
          apply runRvalue_eq_of_eq
          rw [EStateM.bind_eq_ok hm_op]
          change ((do
            let result ← Miri.Interpreter.ScalarOps.unary
              (annealScalarOpsHooks body.localDecls body.layouts) ()
              (translateUnOp uop) ⟨imm, translateTy srcTy body.layouts⟩
            assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
            annealWriteImmediate result.imm destPlace) m₁) = _
          rw [estate_bind_pure_assoc
            (Miri.Interpreter.ScalarOps.unary
              (annealScalarOpsHooks body.localDecls body.layouts) ()
              (translateUnOp uop) ⟨imm, translateTy srcTy body.layouts⟩)
            (fun result => assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts))
            (fun result => result.imm)
            (fun i => annealWriteImmediate i destPlace)
            m₁]
          exact EStateM.bind_eq_ok hm_uop
        have hrc₁ : topFrame₁.returnContinuation = .stop false := by
          rw [htf₁, htf₀]; exact hretCont
        have hrp₁ : ∃ rl, topFrame₁.returnPlace = .frameLocal 0 0 none rl topFrame₁.localsIdentity := by
          rw [htf₁, htf₀]; exact ⟨retLay, hretPlace⟩
        have hdisj_tf₁ := hdisj_fn hdisj_tf₀_inner
        exact write_after_rvalue_simulation_ext hrc₁ hrp₁ hcal hstack hbor hprot hcaller
          hframes hframe.body_eq hframe.location_eq (fun j hj => hmono j (hmono₀ j hj))
          hbb hstmt hframe₁ hdisj_tf₁ hdecl_dst (hmono dstIdx (hmono₀ dstIdx himm_dst)) himmRel' ha_ok hm_write
    | binaryOp bop lhsOp rhsOp lhsTy rhsTy _ hlhsOp hrhsOp hbop =>
      let knownL := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none
      have hlhs_sim := evalOperand_scalar_simulation (m := m₀) rfl hframe₀ hlhsOp s.memory.globals knownL
      have hm_eval : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          Miri.Interpreter.runRvalue
            ((annealEvalOperand body.localDecls body.layouts (translateOperand lhsOp) knownL >>=
                annealReadImmediate) >>=
              fun left =>
                ((annealEvalOperand body.localDecls body.layouts (translateOperand rhsOp)
                    (if (translateBinOp bop).rightHomogeneous then some left.layout else none) >>=
                    annealReadImmediate) >>=
                  fun right => do
                    let result ← Miri.Interpreter.ScalarOps.binary
                      (annealScalarOpsHooks body.localDecls body.layouts) ()
                      (translateBinOp bop) left right
                    assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
                    annealWriteImmediate result.imm destPlace)) m₀ := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt
        rw [hkind]
        dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
          translateRvalue, annealStepHooks]
        apply runRvalue_eq_of_eq
        rw [evalRvalueIntoPlace_binaryOp_def]
        unfold annealRvalueHooks
        dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
        rw [EStateM.bind_eq_ok hevalPlace_dst, EStateM.bind_assoc_apply]
        dsimp only [knownL, destPlace]
        with_unfolding_all
          simp only [Bind.bind, EStateM.bind]
          cases annealEvalOperand body.localDecls body.layouts (translateOperand lhsOp)
            (if (translateBinOp bop).leftHomogeneous = true then some (translateTy dstDecl.ty body.layouts) else none) m₀ with
          | error _ _ => rfl
          | ok opL st₁ =>
            dsimp only
            cases annealReadImmediate opL st₁ with
            | error _ _ => rfl
            | ok left st₂ =>
              dsimp only
              cases annealEvalOperand body.localDecls body.layouts (translateOperand rhsOp)
                (if (translateBinOp bop).rightHomogeneous = true then some left.layout else none) st₂ <;> rfl
      generalize ha_lhs : evalOperand s.frame.locals lhsOp .nil s.memory.globals body.layouts .nil = aLhs at hlhs_sim
      generalize hm_lhs : (annealEvalOperand body.localDecls body.layouts (translateOperand lhsOp) knownL >>=
        annealReadImmediate) m₀ = mLhs at hlhs_sim
      cases hlhs_sim with
      | ub m' msg =>
        have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; rw [hkind]
          simp [evalRvalue, hbor, hcaller, ha_lhs]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
            (m', .error (.undefinedBehavior msg)) := by
          rw [hm_eval]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_error hm_lhs]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
        exact ⟨.ub _ _, fun _ _ _ _ hok => nomatch hok⟩
      | ok v₁ locals₁ topFrame₁ imm₁ hframe₁ himm₁ hmono₁ htf₁ hdisj_fn₁ =>
        let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
        let knownR := if (translateBinOp bop).rightHomogeneous then some (translateTy lhsTy body.layouts) else none
        have hrhs_sim := evalOperand_scalar_simulation (m := m₁) rfl hframe₁
          (hrhsOp.mono_immediate hmono₁) s.memory.globals knownR
        dsimp only at hrhs_sim
        generalize ha_rhs : evalOperand locals₁ rhsOp .nil s.memory.globals body.layouts .nil = aRhs at hrhs_sim
        generalize hm_rhs : (annealEvalOperand body.localDecls body.layouts (translateOperand rhsOp) knownR >>=
          annealReadImmediate) m₁ = mRhs at hrhs_sim
        cases hrhs_sim with
        | ub m'' msg =>
          have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
            unfold evalStmt; rw [hkind]
            simp [evalRvalue, hbor, hcaller, ha_lhs, ha_rhs]
          have hm_err : Miri.Interpreter.Step.evalStatement
              (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
              (m'', .error (.undefinedBehavior msg)) := by
            rw [hm_eval]
            unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_ok hm_lhs]
            dsimp only
            rw [EStateM.bind_eq_error hm_rhs]
          rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
          exact ⟨.ub _ _, fun _ _ _ _ hok => nomatch hok⟩
        | ok v₂ locals₂ topFrame₂ imm₂ hframe₂ himm₂ hmono₂ htf₂ hdisj_fn₂ =>
          let m₂ : AnnealStepState := { m with stack := ⟨#[topFrame₂]⟩ }
          obtain ⟨sc₁, sc₂, rfl, rfl, hbin_sim⟩ :=
            scalarOps_binary_simulation (locals₂ := locals₂) (mem := s.memory) (m₂ := m₂)
              hlhsOp.operandTy_eq hbop himm₁ himm₂
          have hbind₂ := estate_bind_pure_assoc
            (Miri.Interpreter.ScalarOps.binary
              (annealScalarOpsHooks body.localDecls body.layouts) ()
              (translateBinOp bop) ⟨imm₁, translateTy lhsTy body.layouts⟩
              ⟨imm₂, translateTy rhsTy body.layouts⟩)
            (fun result => assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts))
            (fun result => result.imm)
            (fun i => annealWriteImmediate i destPlace)
            m₂
          generalize ha_bin : evalScalarBinOp bop sc₁ sc₂ locals₂ s.memory
            (operandIsSigned body.localDecls lhsOp body.layouts) = aBin at hbin_sim
          generalize hm_bin : (do
            let result ← Miri.Interpreter.ScalarOps.binary
              (annealScalarOpsHooks body.localDecls body.layouts) ()
              (translateBinOp bop) ⟨imm₁, translateTy lhsTy body.layouts⟩
              ⟨imm₂, translateTy rhsTy body.layouts⟩
            assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
            pure result.imm) m₂ = mBin at hbin_sim
          cases hbin_sim with
          | ub msg =>
            have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
              unfold evalStmt; rw [hkind]; dsimp only
              unfold evalRvalue; dsimp only
              rw [hbor, hcaller, ha_lhs]
              dsimp only
              rw [ha_rhs]
              dsimp only
              rw [ha_bin]
            have hm_err : Miri.Interpreter.Step.evalStatement
                (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
                (m₂, .error (.undefinedBehavior msg)) := by
              rw [hm_eval]
              unfold Miri.Interpreter.runRvalue
              rw [EStateM.bind_eq_ok hm_lhs]
              dsimp only
              rw [EStateM.bind_eq_ok hm_rhs]
              rw [hbind₂, EStateM.bind_eq_error hm_bin]
            rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
            exact ⟨.ub _ _, fun _ _ _ _ hok => nomatch hok⟩
          | ok v' imm' himmRel' =>
            have ha_ok : evalStmt s stmt body.localDecls body.layouts =
                match get? locals₂ dstIdx with
                | .some .dead => MirStepNode.fail .ub
                | .some _ =>
                  match set? locals₂ dstIdx (.init v') with
                  | .some locals₃ => MirStepNode.step (advanceStmt s locals₃ s.memory)
                  | .none => MirStepNode.fail .ub
                | .none => MirStepNode.fail .ub := by
              unfold evalStmt; rw [hkind]; dsimp only
              have hrv_ok : evalRvalue s.frame.locals (.binaryOp bop lhsOp rhsOp) s.memory body.localDecls body.layouts =
                  .ok v' locals₂ s.memory := by
                unfold evalRvalue; dsimp only
                rw [hbor, hcaller, ha_lhs]
                dsimp only
                rw [ha_rhs]
                dsimp only
                exact ha_bin
              rw [hrv_ok]
              dsimp only
              rw [hprot, hbor]
              dsimp only [invalidateConflictingBorrows]
              rw [hmem_same]; rfl
            have hm_write : Miri.Interpreter.Step.evalStatement
                (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
                Miri.Interpreter.runRvalue
                  (annealWriteImmediate imm' destPlace)
                  m₂ := by
              rw [hm_eval]
              apply runRvalue_eq_of_eq
              rw [EStateM.bind_eq_ok hm_lhs]
              dsimp only
              rw [EStateM.bind_eq_ok hm_rhs]
              rw [hbind₂, EStateM.bind_eq_ok hm_bin]
            have hrc₂ : topFrame₂.returnContinuation = .stop false := by
              rw [htf₂, htf₁, htf₀]; exact hretCont
            have hrp₂ : ∃ rl, topFrame₂.returnPlace = .frameLocal 0 0 none rl topFrame₂.localsIdentity := by
              rw [htf₂, htf₁, htf₀]; exact ⟨retLay, hretPlace⟩
            have hdisj_tf₁ := hdisj_fn₁ hdisj_tf₀_inner
            have hdisj_tf₂ := hdisj_fn₂ hdisj_tf₁
            exact write_after_rvalue_simulation_ext hrc₂ hrp₂ hcal hstack hbor hprot hcaller
              hframes hframe.body_eq hframe.location_eq
              (fun j hj => hmono₂ j (hmono₁ j (hmono₀ j hj)))
              hbb hstmt hframe₂ hdisj_tf₂ hdecl_dst
              (hmono₂ dstIdx (hmono₁ dstIdx (hmono₀ dstIdx himm_dst)))
              himmRel' ha_ok hm_write

theorem step_assign_scalar_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] → WellTypedScalarStmt body topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  (step_assign_scalar_simulation_ext hstate hphase hbb hstmt hwt).1

theorem miri_step_at_terminator
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none) :
    Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      let res := Miri.Interpreter.ControlFlow.evalTerminator
        (annealTerminatorHooks body.localDecls body.layouts) () (translateTerminator bb.terminator) m
      (res.1, res.2.map fun _ => true) := by
  unfold Miri.Interpreter.Step.step
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map]
  rw [translateBasicBlockData_statements_getElem?, hstmt_none]
  rfl

theorem annealTerminatorHooks_toControlHooks
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    (annealTerminatorHooks localDecls layouts).toControlHooks = annealControlHooks := rfl

theorem returnFromCurrentFrame_of_error
    (hooks : Miri.Interpreter.ControlHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.Operand AnnealProv))
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData}
    {err : Miri.Interpreter.StepError}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hcleanup : bb.isCleanup = false)
    (hop : hooks.returnOperand () m = (m, .error err)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame hooks () false m = (m, .error err) := by
  rcases hooks with ⟨bodySpan, returnOperand, popFrame, copyReturn, cleanupFrame, unwindTerminate⟩
  dsimp only at hop
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map, translateBasicBlockData]
  rw [hcleanup, hop]
  rfl

theorem returnFromCurrentFrame_of_ok
    (hooks : Miri.Interpreter.ControlHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.Operand AnnealProv))
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData}
    {op : Miri.Interpreter.Operand AnnealProv}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hcleanup : bb.isCleanup = false)
    (hretCont : topFrame.returnContinuation = .stop false)
    (hop : hooks.returnOperand () m = (m, .ok op))
    (hpop : hooks.popFrame () m = ({ m with stack := ⟨#[]⟩ }, .ok topFrame))
    (hcopy : hooks.copyReturn () op topFrame.returnPlace { m with stack := ⟨#[]⟩ } =
      ({ m with stack := ⟨#[]⟩ }, .ok ()))
    (hclean : hooks.cleanupFrame () false topFrame { m with stack := ⟨#[]⟩ } =
      ({ m with stack := ⟨#[]⟩ }, .ok .normal)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame hooks () false m =
      ({ m with stack := ⟨#[]⟩ }, .ok ()) := by
  rcases hooks with ⟨bodySpan, returnOperand, popFrame, copyReturn, cleanupFrame, unwindTerminate⟩
  dsimp only at hop hpop hcopy hclean
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map, translateBasicBlockData]
  simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, Bool.not_false,
    hcleanup, hop, hpop, hcopy, hclean, hretCont]
  rfl

theorem annealControlHooks_returnOperand_dead
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hget0 : topFrame.getLocal 0 = .ok ⟨.dead, lay⟩) :
    annealControlHooks.returnOperand () m =
      (m, .error (.undefinedBehavior "return with uninitialized or dead _0")) := by
  unfold annealControlHooks
  dsimp only
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hget0]

theorem annealControlHooks_returnOperand_uninit
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hget0 : topFrame.getLocal 0 = .ok ⟨.live (.immediate .uninit), lay⟩) :
    annealControlHooks.returnOperand () m =
      (m, .error (.undefinedBehavior "return with uninitialized or dead _0")) := by
  unfold annealControlHooks
  dsimp only
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hget0]

theorem annealControlHooks_returnOperand_scalar
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {msc : Miri.Memory.Scalar AnnealProv} {lay : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hget0 : topFrame.getLocal 0 = .ok ⟨.live (.immediate (.scalar msc)), lay⟩) :
    annealControlHooks.returnOperand () m =
      (m, .ok (.immediate (.scalar msc))) := by
  unfold annealControlHooks
  dsimp only
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hget0]

theorem annealControlHooks_returnOperand_scalarPair
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {msc₁ msc₂ : Miri.Memory.Scalar AnnealProv} {lay : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hget0 : topFrame.getLocal 0 = .ok ⟨.live (.immediate (.scalarPair msc₁ msc₂)), lay⟩) :
    annealControlHooks.returnOperand () m =
      (m, .ok (.immediate (.scalarPair msc₁ msc₂))) := by
  unfold annealControlHooks
  dsimp only
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hget0]

theorem annealControlHooks_popFrame_singleton
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame]) :
    annealControlHooks.popFrame () m = ({ m with stack := ⟨#[]⟩ }, .ok topFrame) := by
  unfold annealControlHooks Miri.Interpreter.Stack.popFrame
  dsimp only
  rw [hframes]
  rfl

theorem annealControlHooks_copyReturn_empty
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (retOp : Miri.Interpreter.Operand AnnealProv)
    {retLay : Miri.Interpreter.LocalLayout}
    (hretPlace : topFrame.returnPlace = .frameLocal 0 0 none retLay topFrame.localsIdentity) :
    annealControlHooks.copyReturn () retOp topFrame.returnPlace { m with stack := ⟨#[]⟩ } =
      ({ m with stack := ⟨#[]⟩ }, .ok ()) := by
  rw [hretPlace]
  rfl

theorem annealControlHooks_cleanupFrame_eq
    (unw : Bool)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (st : AnnealStepState) :
    annealControlHooks.cleanupFrame () unw topFrame st = (st, .ok .normal) := rfl

theorem step_terminator_goto_return_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hterm :
      (∃ target, bb.terminator.kind = .goto target) ∨
      (bb.terminator.kind = .return_ ∧
        ∃ decl0,
          get? body.localDecls 0 = some decl0 ∧
          (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO ∧
          ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 0) ∨
      bb.terminator.kind = .unreachable) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hd_tf⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
    simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  rcases hterm with ⟨target, hgoto⟩ | ⟨hret, decl0, hdecl0, hsz0, himm0⟩ | hunreach
  · unfold evalTerminator translateTerminator
      Miri.Interpreter.ControlFlow.evalTerminator
      Miri.Interpreter.ControlFlow.goToBlock
      Miri.Interpreter.ControlFlow.setLocation
    rw [hgoto, stack_currentFrame?_singleton m.stack topFrame hframes, hframes]
    dsimp only [translateTerminatorKind, Except.map, Id.run]
    apply StepRel.step
    exact StateRel.mk
      { topFrame with location := .mir ⟨target, 0⟩ }
      rfl hretCont ⟨retLay, hretPlace⟩
      ⟨hframe.body_eq, rfl, hframe.af_locals_len, hframe.mf_locals_size, hframe.locals_rel⟩
      hcal hstack hbor hprot hcaller hd_tf
  · obtain ⟨slot0, mls0, _, _, hslot0, hmls0, _, hloc0⟩ := hframe.lookup_local hdecl0
    have hget0 := frame_getLocal_of_getElem? topFrame 0 mls0 hmls0
    have himm0' := himm0 topFrame hframes mls0 hmls0
    unfold evalTerminator translateTerminator
      Miri.Interpreter.ControlFlow.evalTerminator
    rw [hret, hstack, annealTerminatorHooks_toControlHooks, hslot0]
    dsimp only [translateTerminatorKind, Id.run, Pure.pure]
    cases hloc0 with
    | dead cachedLayout _ =>
      rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
        hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_dead hframes hget0)]
      exact StepRel.ub _ _
    | indirect _ mp _ _ _ _ =>
      exact False.elim (himm0' mp rfl)
    | immediate _ imm cachedLayout _ hval =>
      rcases hval with ⟨rfl, rfl⟩ | ⟨retVal, rfl, himmRel⟩
      · rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
          hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_uninit hframes hget0)]
        exact StepRel.ub _ _
      · cases himmRel with
        | unit hzero =>
          exact False.elim (hsz0 hzero)
        | scalar sc msc hsc hsz_sc hbool_sc hchar_sc =>
          have hop0 := annealControlHooks_returnOperand_scalar hframes hget0
          rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
            hframe.location_eq hbb hcleanup hretCont hop0
            (annealControlHooks_popFrame_singleton hframes)
            (annealControlHooks_copyReturn_empty _ hretPlace)
            (annealControlHooks_cleanupFrame_eq false topFrame _)]
          exact StepRel.retRoot decl0 _ _ s.memory _ hdecl0 hop0
            (.scalar sc msc hsc hsz_sc hbool_sc hchar_sc) rfl
        | scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair =>
          have hop0 := annealControlHooks_returnOperand_scalarPair hframes hget0
          rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
            hframe.location_eq hbb hcleanup hretCont hop0
            (annealControlHooks_popFrame_singleton hframes)
            (annealControlHooks_copyReturn_empty _ hretPlace)
            (annealControlHooks_cleanupFrame_eq false topFrame _)]
          exact StepRel.retRoot decl0 _ _ s.memory _ hdecl0 hop0
            (.scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair) rfl
  · unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
    rw [hunreach]
    dsimp only [translateTerminatorKind, Except.map, Id.run]
    exact StepRel.ub _ _

/-! ### 5.6 Whole-Body Syntactic Well-Typedness (`WellTypedBody`) & Unified Step Simulation -/

theorem FrameRel.isImmediateFrameLocal_of_live_nil
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRel body mach af mf) (hlive : mach.memory.live.toList = [])
    {idx : Nat} {decl : LocalDecl} (hdecl : get? body.localDecls idx = some decl) :
    IsImmediateFrameLocal mf idx := by
  obtain ⟨_, mls, _, _, _, hmls, _, hloc⟩ := hfr.lookup_local hdecl
  intro mls' hmls' mp hmp
  rw [hmls] at hmls'
  injection hmls' with h_eq; subst h_eq
  cases hloc with
  | dead _ _ => cases hmp
  | immediate _ _ _ _ _ => cases hmp
  | indirect _ _ _ _ _ hmemp =>
    rcases hmemp with ⟨_, _, _, _, _, _, _, _, hin, _⟩
    rw [hlive] at hin; cases hin

/-- Purely syntactic operand well-typedness on `CapturedMir` (parametric in the
set `nonAddrTaken` of immediate/non-address-taken locals, with zero reference to
runtime `Miri.Interpreter.Frame` state). -/
inductive WellTypedScalarOperandSyn
    (body : CapturedMir) (nonAddrTaken : Nat → Prop) :
    MirAst.Operand → Ty → Prop where
  | constScalar (c : ConstOperand) (sc : MirAst.ScalarInt) :
      c.val = .scalar (.int sc) →
      IsPrimScalarTy c.ty →
      ValidScalarBytes sc.sizeBytes →
      sc.bits < scalarModulus sc.sizeBytes →
      (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes →
      (c.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) →
      (c.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) →
      WellTypedScalarOperandSyn body nonAddrTaken (.constant c) c.ty
  | copyLocal (idx : Local) (decl : LocalDecl) :
      get? body.localDecls idx = some decl →
      (translateTy decl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO →
      nonAddrTaken idx →
      WellTypedScalarOperandSyn body nonAddrTaken (.copy ⟨idx, .nil⟩) decl.ty

/-- Purely syntactic rvalue well-typedness on `CapturedMir`. -/
inductive WellTypedScalarRvalueSyn
    (body : CapturedMir) (nonAddrTaken : Nat → Prop) :
    MirAst.Rvalue → Ty → Prop where
  | use (op : MirAst.Operand) (dstTy : Ty) :
      WellTypedScalarOperandSyn body nonAddrTaken op dstTy →
      WellTypedScalarRvalueSyn body nonAddrTaken (.use op) dstTy
  | unaryOp (uop : MirAst.UnOp) (op : MirAst.Operand) (srcTy dstTy : Ty) :
      WellTypedScalarOperandSyn body nonAddrTaken op srcTy →
      WellTypedScalarUnOp uop srcTy dstTy →
      WellTypedScalarRvalueSyn body nonAddrTaken (.unaryOp uop op) dstTy
  | binaryOp (bop : MirAst.BinOp) (lhsOp rhsOp : MirAst.Operand)
      (lhsTy rhsTy dstTy : Ty) :
      WellTypedScalarOperandSyn body nonAddrTaken lhsOp lhsTy →
      WellTypedScalarOperandSyn body nonAddrTaken rhsOp rhsTy →
      WellTypedScalarBinOp body.layouts body.localDecls bop lhsTy rhsTy dstTy →
      WellTypedScalarRvalueSyn body nonAddrTaken (.binaryOp bop lhsOp rhsOp) dstTy

/-- Purely syntactic statement well-typedness on `CapturedMir`. -/
inductive WellTypedScalarStmtSyn
    (body : CapturedMir) (nonAddrTaken : Nat → Prop) :
    MirAst.Statement → Prop where
  | nop (stmt : Statement) :
      stmt.kind = .nop →
      WellTypedScalarStmtSyn body nonAddrTaken stmt
  | storageLive (stmt : Statement) (loc : Local) (decl : LocalDecl) :
      stmt.kind = .storageLive loc →
      get? body.localDecls loc = some decl →
      nonAddrTaken loc →
      WellTypedScalarStmtSyn body nonAddrTaken stmt
  | storageDead (stmt : Statement) (loc : Local) (decl : LocalDecl) :
      stmt.kind = .storageDead loc →
      get? body.localDecls loc = some decl →
      loc ≠ 0 →
      nonAddrTaken loc →
      WellTypedScalarStmtSyn body nonAddrTaken stmt
  | assign (stmt : Statement) (dstIdx : Local) (dstDecl : LocalDecl) (rv : MirAst.Rvalue) :
      stmt.kind = .assign ⟨dstIdx, .nil⟩ rv →
      get? body.localDecls dstIdx = some dstDecl →
      nonAddrTaken dstIdx →
      WellTypedScalarRvalueSyn body nonAddrTaken rv dstDecl.ty →
      WellTypedScalarStmtSyn body nonAddrTaken stmt

/-- Purely syntactic basic-block well-typedness on `CapturedMir` (`LM-1.1` scalar fragment). -/
structure WellTypedBasicBlock
    (body : CapturedMir) (nonAddrTaken : Nat → Prop) (bb : BasicBlockData) : Prop where
  not_cleanup : bb.isCleanup = false
  stmts_wt : ∀ stmt, stmt ∈ bb.statements → WellTypedScalarStmtSyn body nonAddrTaken stmt
  term_wt :
    (∃ target targetBb,
      bb.terminator.kind = .goto target ∧
      get? body.basicBlocks target = some targetBb) ∨
    (bb.terminator.kind = .return_ ∧
      nonAddrTaken 0 ∧
      ∃ decl0,
        get? body.localDecls 0 = some decl0 ∧
        (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO) ∨
    bb.terminator.kind = .unreachable

/-- Purely syntactic whole-body well-typedness (`WellTypedBody`) for the `LM-1.1`
scalar MIR fragment, parametric in `nonAddrTaken` (defaulting to `fun _ => True`
when all locals are immediate). -/
structure WellTypedBody
    (body : CapturedMir) (nonAddrTaken : Nat → Prop := fun _ => True) : Prop where
  phase_ok : ∀ p, body.phase ≠ .other p
  blocks_wt : ∀ bb, bb ∈ body.basicBlocks → WellTypedBasicBlock body nonAddrTaken bb

/-- In-bounds program counter (`blockIdx`, `stmtIdx`) within `body.basicBlocks`. -/
def ValidFrameLocation (body : CapturedMir) (af : StackFrame) : Prop :=
  ∃ bb, get? body.basicBlocks af.blockIdx = some bb ∧ af.stmtIdx ≤ bb.statements.length

/-- State invariant asserting that every declared local in `nonAddrTaken` is an
immediate (non-indirect) frame local in `m`. -/
def NonAddrTakenImmediate (body : CapturedMir) (nonAddrTaken : Nat → Prop)
    (m : AnnealStepState) : Prop :=
  ∀ topFrame, m.stack.frames = #[topFrame] →
    ∀ idx decl, get? body.localDecls idx = some decl →
      nonAddrTaken idx → IsImmediateFrameLocal topFrame idx

theorem NonAddrTakenImmediate.of_live_nil
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (nonAddrTaken : Nat → Prop)
    (hstate : StateRel body s m) (hlive : m.machine.memory.live.toList = []) :
    NonAddrTakenImmediate body nonAddrTaken m := by
  rcases hstate with ⟨tf, hframes, _, _, hfr, _, _, _, _, _⟩
  intro topFrame htf idx decl hdecl _
  rw [hframes] at htf
  have h_eq : tf = topFrame := by
    injection htf with h_arr
    injection h_arr with h_hd _
  subst h_eq
  exact hfr.isImmediateFrameLocal_of_live_nil hlive hdecl

theorem WellTypedScalarOperandSyn.toFrame
    {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (h : WellTypedScalarOperandSyn body nonAddrTaken op ty)
    (hframes : m.stack.frames = #[topFrame])
    (himm : NonAddrTakenImmediate body nonAddrTaken m) :
    WellTypedScalarOperand body topFrame op ty := by
  cases h with
  | constScalar c sc hval hprim hsz hcan hlaysz hbool hchar =>
    exact .constScalar c sc hval hprim hsz hcan hlaysz hbool hchar
  | copyLocal idx decl hdecl hsz hna =>
    exact .copyLocal idx decl hdecl hsz (himm topFrame hframes idx decl hdecl hna)

theorem WellTypedScalarRvalueSyn.toFrame
    {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {rv : MirAst.Rvalue} {ty : Ty}
    (h : WellTypedScalarRvalueSyn body nonAddrTaken rv ty)
    (hframes : m.stack.frames = #[topFrame])
    (himm : NonAddrTakenImmediate body nonAddrTaken m) :
    WellTypedScalarRvalue body topFrame rv ty := by
  cases h with
  | use op _ hop =>
    exact .use op ty (hop.toFrame hframes himm)
  | unaryOp uop op srcTy _ hop huop =>
    exact .unaryOp uop op srcTy ty (hop.toFrame hframes himm) huop
  | binaryOp bop lhsOp rhsOp lhsTy rhsTy _ hlhs hrhs hbop =>
    exact .binaryOp bop lhsOp rhsOp lhsTy rhsTy ty
      (hlhs.toFrame hframes himm) (hrhs.toFrame hframes himm) hbop

theorem WellTypedScalarStmtSyn.toFrame
    {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {stmt : MirAst.Statement}
    (h : WellTypedScalarStmtSyn body nonAddrTaken stmt)
    (hframes : m.stack.frames = #[topFrame])
    (himm : NonAddrTakenImmediate body nonAddrTaken m) :
    WellTypedScalarStmt body topFrame stmt := by
  cases h with
  | nop hkind => exact .nop stmt hkind
  | storageLive loc decl hkind hdecl hna =>
    exact .storageLive stmt loc decl hkind hdecl (himm topFrame hframes loc decl hdecl hna)
  | storageDead loc decl hkind hdecl hne hna =>
    exact .storageDead stmt loc decl hkind hdecl hne (himm topFrame hframes loc decl hdecl hna)
  | assign dstIdx dstDecl rv hkind hdecl hna hrv =>
    exact .assign stmt dstIdx dstDecl rv hkind hdecl
      (himm topFrame hframes dstIdx dstDecl hdecl hna)
      (hrv.toFrame hframes himm)

/-- Unified whole-body small-step simulation under purely syntactic `WellTypedBody`:
dispatches automatically between `step_assign_scalar_simulation` (when `stmtIdx`
points at a statement) and `step_terminator_goto_return_simulation` (when `stmtIdx`
reaches the end of the basic block). -/
theorem step_wellTypedBody_simulation
    {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {s : MachineState} {m : AnnealStepState}
    (hbody : WellTypedBody body nonAddrTaken)
    (hstate : StateRel body s m)
    (hloc : ValidFrameLocation body s.frame)
    (himm : NonAddrTakenImmediate body nonAddrTaken m) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨bb, hbb, hle⟩ := hloc
  have hbb_mem : bb ∈ body.basicBlocks := by
    rw [get?_eq_getElem?] at hbb
    exact List.mem_of_getElem? hbb
  have hbb_wt := hbody.blocks_wt bb hbb_mem
  by_cases hlt : s.frame.stmtIdx < bb.statements.length
  · have hstmt : get? bb.statements s.frame.stmtIdx = some (bb.statements[s.frame.stmtIdx]'hlt) := by
      rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt]
    have hstmt_mem : bb.statements[s.frame.stmtIdx]'hlt ∈ bb.statements :=
      List.getElem_mem hlt
    have hstmt_syn := hbb_wt.stmts_wt _ hstmt_mem
    exact step_assign_scalar_simulation hstate hbody.phase_ok hbb hstmt
      (fun tf hframes => hstmt_syn.toFrame hframes himm)
  · have hlen_eq : s.frame.stmtIdx = length bb.statements := by
      rw [length_eq_length]; omega
    have hstmt_none : get? bb.statements s.frame.stmtIdx = none := by
      rw [get?_eq_getElem?, List.getElem?_eq_none (by omega)]
    apply step_terminator_goto_return_simulation hstate hbody.phase_ok hbb hstmt_none
      hlen_eq hbb_wt.not_cleanup
    rcases hbb_wt.term_wt with ⟨target, _, hgoto, _⟩ | ⟨hret, hna0, decl0, hdecl0, hsz0⟩ | hunreach
    · exact Or.inl ⟨target, hgoto⟩
    · exact Or.inr (Or.inl ⟨hret, decl0, hdecl0, hsz0,
        fun tf hframes => himm tf hframes 0 decl0 hdecl0 hna0⟩)
    · exact Or.inr (Or.inr hunreach)

/-- The `LM-1.1` correspondence stated directly on the two step functions,
without `StepRel`. Under `StateRel` and the syntactic `WellTypedBody`
fragment:

1. Anneal steps within the frame, to a state related to `lean-miri`'s
   post-state, iff `lean-miri` continues (`.ok true`) with a nonempty stack;
2. Anneal returns normally from the root frame iff `lean-miri` continues
   (`.ok true`) after popping the root frame;
3. Anneal reports undefined behavior iff `lean-miri` reports
   `StepError.undefinedBehavior`; and
4. Anneal produces no other outcome (in particular no `unsupported` and no
   failure other than undefined behavior). -/
theorem step_wellTypedBody_bisim
    {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {s : MachineState} {m : AnnealStepState}
    (hbody : WellTypedBody body nonAddrTaken)
    (hstate : StateRel body s m)
    (hloc : ValidFrameLocation body s.frame)
    (himm : NonAddrTakenImmediate body nonAddrTaken m) :
    ((∃ s', stepMirFn body s = .step s' ∧
        StateRel body s' (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1) ↔
      ((Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 = .ok true ∧
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames ≠ #[])) ∧
    ((∃ retVal mem', stepMirFn body s = .retNormal retVal mem') ↔
      ((Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 = .ok true ∧
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames = #[])) ∧
    (stepMirFn body s = .fail .ub ↔
      ∃ msg, (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 =
        .error (.undefinedBehavior msg)) ∧
    ((∃ s', stepMirFn body s = .step s') ∨
      (∃ retVal mem', stepMirFn body s = .retNormal retVal mem') ∨
      stepMirFn body s = .fail .ub) := by
  have h := step_wellTypedBody_simulation hbody hstate hloc himm
  refine ⟨h.step_iff, h.retNormal_iff, h.ub_iff, ?_⟩
  generalize stepMirFn body s = aRes at h
  generalize Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = mRes at h
  cases h with
  | step s' _ _ => exact Or.inl ⟨s', rfl⟩
  | retRoot _ retVal _ mem' _ _ _ _ _ => exact Or.inr (Or.inl ⟨retVal, mem', rfl⟩)
  | ub _ _ => exact Or.inr (Or.inr rfl)

/-! ### 5.7 Step-Invariant Preservation & Multi-Step Bounded Simulation / Bisimulation -/

theorem MirStepNode_step_inj {s₁ s₂ : MachineState}
    (h : MirStepNode.step s₁ = MirStepNode.step s₂) : s₁ = s₂ := by
  unfold MirStepNode.step at h
  injection h with hr
  injection hr

theorem MirStepNode_fail_ne_step {k : Trusted.Effect.FailureKind} {s : MachineState} :
    MirStepNode.fail k ≠ MirStepNode.step s := nofun

theorem MirStepNode_unsupported_ne_step {s : MachineState} :
    MirStepNode.unsupported ≠ MirStepNode.step s := nofun

theorem MirStepNode_retNormal_ne_step {v : Value} {mem : Memory} {s : MachineState} :
    MirStepNode.retNormal v mem ≠ MirStepNode.step s := nofun

theorem evalStmt_step_location
    {s s' : MachineState} {stmt : Statement}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    (hk : stmt.kind = .nop ∨ (∃ l, stmt.kind = .storageLive l) ∨
      (∃ l, stmt.kind = .storageDead l) ∨ (∃ dstIdx rv, stmt.kind = .assign ⟨dstIdx, .nil⟩ rv))
    (hstep : evalStmt s stmt localDecls layouts = .step s') :
    s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 := by
  unfold evalStmt at hstep
  rcases hk with hnop | ⟨l, hsl⟩ | ⟨l, hsd⟩ | ⟨dstIdx, rv, hasgn⟩
  · rw [hnop] at hstep
    have h := MirStepNode_step_inj hstep
    subst h; exact ⟨rfl, rfl⟩
  · rw [hsl] at hstep; dsimp only at hstep
    revert hstep
    cases get? s.frame.locals l with
    | none => exact fun hstep => absurd hstep MirStepNode_fail_ne_step
    | some _ =>
      cases set? s.frame.locals l .uninit with
      | none => exact fun hstep => absurd hstep MirStepNode_fail_ne_step
      | some _ =>
        intro hstep
        have h := MirStepNode_step_inj hstep
        subst h; exact ⟨rfl, rfl⟩
  · rw [hsd] at hstep; dsimp only at hstep
    revert hstep
    cases get? s.frame.locals l with
    | none => exact fun hstep => absurd hstep MirStepNode_fail_ne_step
    | some _ =>
      cases set? s.frame.locals l .dead with
      | none => exact fun hstep => absurd hstep MirStepNode_fail_ne_step
      | some _ =>
        intro hstep
        have h := MirStepNode_step_inj hstep
        subst h; exact ⟨rfl, rfl⟩
  · rw [hasgn] at hstep; dsimp only at hstep
    revert hstep
    cases evalRvalue s.frame.locals rv s.memory localDecls layouts with
    | ub => exact fun hstep => absurd hstep MirStepNode_fail_ne_step
    | unsupported => exact fun hstep => absurd hstep MirStepNode_unsupported_ne_step
    | ok val locals₁ mem₁ =>
      dsimp only
      cases get? locals₁ dstIdx with
      | none => exact fun hstep => absurd hstep MirStepNode_fail_ne_step
      | some slot =>
        cases slot with
        | dead => exact fun hstep => absurd hstep MirStepNode_fail_ne_step
        | uninit =>
          dsimp only
          cases set? locals₁ dstIdx (.init val) with
          | none => exact fun hstep => absurd hstep MirStepNode_fail_ne_step
          | some _ =>
            dsimp only
            cases mem₁.activeProtectors with
            | nil =>
              intro hstep
              have h := MirStepNode_step_inj hstep
              subst h; exact ⟨rfl, rfl⟩
            | cons protHead protTail =>
              dsimp only
              cases hasProtectedWriteConflict mem₁.borrows (protHead :: protTail) dstIdx none with
              | true => exact fun hstep => absurd hstep MirStepNode_fail_ne_step
              | false =>
                intro hstep
                have h := MirStepNode_step_inj hstep
                subst h; exact ⟨rfl, rfl⟩
        | init _ =>
          dsimp only
          cases set? locals₁ dstIdx (.init val) with
          | none => exact fun hstep => absurd hstep MirStepNode_fail_ne_step
          | some _ =>
            dsimp only
            cases mem₁.activeProtectors with
            | nil =>
              intro hstep
              have h := MirStepNode_step_inj hstep
              subst h; exact ⟨rfl, rfl⟩
            | cons protHead protTail =>
              dsimp only
              cases hasProtectedWriteConflict mem₁.borrows (protHead :: protTail) dstIdx none with
              | true => exact fun hstep => absurd hstep MirStepNode_fail_ne_step
              | false =>
                intro hstep
                have h := MirStepNode_step_inj hstep
                subst h; exact ⟨rfl, rfl⟩

/-- `ValidFrameLocation` is preserved across every intra-frame step of a
`WellTypedBody`. -/
theorem ValidFrameLocation.preserved
    {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {s s' : MachineState} {m : AnnealStepState}
    (hbody : WellTypedBody body nonAddrTaken)
    (hstate : StateRel body s m)
    (hloc : ValidFrameLocation body s.frame)
    (hstep : stepMirFn body s = .step s') :
    ValidFrameLocation body s'.frame := by
  rcases hstate with ⟨_, _, _, _, _, hcal, hstack, _, _, _⟩
  obtain ⟨bb, hbb, hle⟩ := hloc
  have hbb_mem : bb ∈ body.basicBlocks := by
    rw [get?_eq_getElem?] at hbb
    exact List.mem_of_getElem? hbb
  have hbb_wt := hbody.blocks_wt bb hbb_mem
  rw [stepMirFn_eq_of_not_other body s hcal hbody.phase_ok] at hstep
  simp only [hbb] at hstep
  by_cases hlt : s.frame.stmtIdx < bb.statements.length
  · have hstmt : get? bb.statements s.frame.stmtIdx = some (bb.statements[s.frame.stmtIdx]'hlt) := by
      rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt]
    rw [hstmt] at hstep
    have hstmt_syn := hbb_wt.stmts_wt _ (List.getElem_mem hlt)
    have hk : (bb.statements[s.frame.stmtIdx]'hlt).kind = .nop ∨
        (∃ l, (bb.statements[s.frame.stmtIdx]'hlt).kind = .storageLive l) ∨
        (∃ l, (bb.statements[s.frame.stmtIdx]'hlt).kind = .storageDead l) ∨
        (∃ dstIdx rv, (bb.statements[s.frame.stmtIdx]'hlt).kind = .assign ⟨dstIdx, .nil⟩ rv) := by
      cases hstmt_syn with
      | nop hk => exact Or.inl hk
      | storageLive loc _ hk _ _ => exact Or.inr (Or.inl ⟨loc, hk⟩)
      | storageDead loc _ hk _ _ _ => exact Or.inr (Or.inr (Or.inl ⟨loc, hk⟩))
      | assign dstIdx _ rv hk _ _ _ => exact Or.inr (Or.inr (Or.inr ⟨dstIdx, rv, hk⟩))
    obtain ⟨hblk, hidx⟩ := evalStmt_step_location hk hstep
    exact ⟨bb, by rw [hblk]; exact hbb, by omega⟩
  · have hlen_eq : s.frame.stmtIdx = length bb.statements := by
      rw [length_eq_length]; omega
    have hstmt_none : get? bb.statements s.frame.stmtIdx = none := by
      rw [get?_eq_getElem?, List.getElem?_eq_none (by omega)]
    have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
      simp [hlen_eq]
    simp only [hstmt_none, hbeq_len, ↓reduceIte] at hstep
    rcases hbb_wt.term_wt with ⟨target, targetBb, hgoto, htargetBb⟩ | ⟨hret, _, _, _, _⟩ | hunreach
    · unfold evalTerminator at hstep
      rw [hgoto] at hstep
      have h := MirStepNode_step_inj hstep
      subst h
      exact ⟨targetBb, htargetBb, Nat.zero_le _⟩
    · unfold evalTerminator at hstep
      rw [hret, hstack] at hstep
      dsimp only at hstep
      revert hstep
      cases get? s.frame.locals 0 with
      | none => exact fun hstep => absurd hstep MirStepNode_fail_ne_step
      | some slot =>
        cases slot with
        | dead => exact fun hstep => absurd hstep MirStepNode_fail_ne_step
        | uninit => exact fun hstep => absurd hstep MirStepNode_fail_ne_step
        | init _ => exact fun hstep => absurd hstep MirStepNode_retNormal_ne_step
    · unfold evalTerminator at hstep
      rw [hunreach] at hstep
      exact absurd hstep MirStepNode_fail_ne_step

/-- `NonAddrTakenImmediate` is preserved across every `lean-miri` step that
continues (`.ok true`) on a `WellTypedBody`. -/
theorem NonAddrTakenImmediate.preserved
    {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {s : MachineState} {m : AnnealStepState}
    (hbody : WellTypedBody body nonAddrTaken)
    (hstate : StateRel body s m)
    (hloc : ValidFrameLocation body s.frame)
    (himm : NonAddrTakenImmediate body nonAddrTaken m)
    (hm_ok : (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 = .ok true) :
    NonAddrTakenImmediate body nonAddrTaken
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1 := by
  intro tf' htf' idx decl hdecl hna
  obtain ⟨bb, hbb, hle⟩ := hloc
  have hbb_mem : bb ∈ body.basicBlocks := by
    rw [get?_eq_getElem?] at hbb
    exact List.mem_of_getElem? hbb
  have hbb_wt := hbody.blocks_wt bb hbb_mem
  by_cases hlt : s.frame.stmtIdx < bb.statements.length
  · have hstmt : get? bb.statements s.frame.stmtIdx = some (bb.statements[s.frame.stmtIdx]'hlt) := by
      rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt]
    have hstmt_syn := hbb_wt.stmts_wt _ (List.getElem_mem hlt)
    have hext := (step_assign_scalar_simulation_ext hstate hbody.phase_ok hbb hstmt
      (fun tf hframes => hstmt_syn.toFrame hframes himm)).2
    rcases hstate with ⟨topFrame, hframes, _, _, _, _, _, _, _, _⟩
    exact hext topFrame hframes idx (himm topFrame hframes idx decl hdecl hna) tf' htf' hm_ok
  · have hlen_eq : s.frame.stmtIdx = length bb.statements := by
      rw [length_eq_length]; omega
    have hstmt_none : get? bb.statements s.frame.stmtIdx = none := by
      rw [get?_eq_getElem?, List.getElem?_eq_none (by omega)]
    rcases hbb_wt.term_wt with ⟨target, _, hgoto, _⟩ | ⟨hret, hna0, decl0, hdecl0, hsz0⟩ | hunreach
    · rcases hstate with ⟨topFrame, hframes, _, _, hframe, _, _, _, _, _⟩
      have himm_orig := himm topFrame hframes idx decl hdecl hna
      have hm_step := miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none
      unfold translateTerminator
        Miri.Interpreter.ControlFlow.evalTerminator
        Miri.Interpreter.ControlFlow.goToBlock
        Miri.Interpreter.ControlFlow.setLocation at hm_step
      rw [hgoto, stack_currentFrame?_singleton m.stack topFrame hframes, hframes] at hm_step
      dsimp only [translateTerminatorKind, Except.map, Id.run] at hm_step
      rw [hm_step] at htf'
      dsimp only at htf'
      injection htf' with h_arr
      injection h_arr with h_eq _
      subst h_eq
      exact himm_orig
    · have hsim := step_terminator_goto_return_simulation hstate hbody.phase_ok hbb hstmt_none
        hlen_eq hbb_wt.not_cleanup
        (Or.inr (Or.inl ⟨hret, decl0, hdecl0, hsz0, fun tf hframes => himm tf hframes 0 decl0 hdecl0 hna0⟩))
      rcases hstate with ⟨_, _, _, _, _, hcal, hstack, _, _, _⟩
      generalize ha_eq : stepMirFn body s = aRes at hsim
      generalize Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = mRes at hsim htf' hm_ok
      cases hsim with
      | ub _ _ => cases hm_ok
      | retRoot _ _ _ _ _ _ _ _ hm' =>
        subst hm'
        dsimp only at htf'
        cases htf'
      | step s' _ _ =>
        rw [stepMirFn_eq_of_not_other body s hcal hbody.phase_ok] at ha_eq
        have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
          simp [hlen_eq]
        simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte] at ha_eq
        unfold evalTerminator at ha_eq
        rw [hret, hstack] at ha_eq
        dsimp only at ha_eq
        revert ha_eq
        cases get? s.frame.locals 0 with
        | none => exact fun ha_eq => absurd ha_eq MirStepNode_fail_ne_step
        | some slot =>
          cases slot with
          | dead => exact fun ha_eq => absurd ha_eq MirStepNode_fail_ne_step
          | uninit => exact fun ha_eq => absurd ha_eq MirStepNode_fail_ne_step
          | init _ => exact fun ha_eq => absurd ha_eq MirStepNode_retNormal_ne_step
    · rcases hstate with ⟨topFrame, hframes, _, _, hframe, _, _, _, _, _⟩
      have hm_step := miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none
      unfold translateTerminator Miri.Interpreter.ControlFlow.evalTerminator at hm_step
      rw [hunreach] at hm_step
      dsimp only [translateTerminatorKind, Except.map, Id.run] at hm_step
      rw [hm_step] at hm_ok
      cases hm_ok

/-- Outcome of running Anneal's `stepMirFn` for at most `fuel` steps. -/
inductive AnnealRunOutcome : Type where
  | running (state : MachineState)
  | returned (retVal : Value) (mem : Memory)
  | faulted (kind : Trusted.Effect.FailureKind)
  | haltedOther (out : MirOutcome)
  | blocked

/-- Fuel-bounded execution of Anneal's `stepMirFn` on `body`. Handles both silent
`.tau` steps and trace-emitting `MirObsE` steps (`MirStepNode.emitStep (.event tag) s'`,
emitted by `TerminatorKind.switchInt`). -/
def runAnnealBounded (body : CapturedMir) : Nat → MachineState → AnnealRunOutcome
  | 0, s => .running s
  | fuel + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => runAnnealBounded body fuel s'
    | .tau (.halted (.normal (retVal, mem))) => .returned retVal mem
    | .tau (.halted out) => .haltedOther out
    | .tau (.faulted kind) => .faulted kind
    | .ret (.normal (retVal, mem)) => .returned retVal mem
    | .ret out => .haltedOther out
    | .vis (.inl (.fail kind)) _ => .faulted kind
    | .vis (.inr (.inl (.emit _))) k =>
        match k PUnit.unit with
        | .running s' => runAnnealBounded body fuel s'
        | .halted (.normal (retVal, mem)) => .returned retVal mem
        | .halted out => .haltedOther out
        | .faulted kind => .faulted kind
    | .vis (.inr (.inr _)) _ => .blocked

/-- Stepping across `MirStepNode.emitStep obs s'` (both `.silent` and `SwitchInt`'s
`.event tag`) advances `runAnnealBounded` directly to `s'` with `fuel` remaining. -/
theorem runAnnealBounded_emitStep (body : CapturedMir) (fuel : Nat)
    (s s' : MachineState) (obs : MirObs)
    (hstep : stepMirFn body s = .emitStep obs s') :
    runAnnealBounded body (fuel + 1) s = runAnnealBounded body fuel s' := by
  conv => lhs; unfold runAnnealBounded
  rw [hstep]
  cases obs <;> rfl

/-- Outcome of running `lean-miri`'s `Step.step` for at most `fuel` steps from a
live root frame, recording the root `_0` return operand upon root-frame pop. -/
inductive MiriRunOutcome : Type where
  | running (state : AnnealStepState)
  | returned (postState : AnnealStepState)
      (retOperand : Except Miri.Interpreter.StepError (Miri.Interpreter.Operand AnnealProv))
  | error (postState : AnnealStepState) (err : Miri.Interpreter.StepError)

/-- Fuel-bounded execution of `lean-miri`'s `Step.step` on `body`. -/
def runMiriBounded (body : CapturedMir) : Nat → AnnealStepState → MiriRunOutcome
  | 0, m => .running m
  | fuel + 1, m =>
    match Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m with
    | (m', .ok true) =>
      if m'.stack.frames.isEmpty then
        .returned m' (annealControlHooks.returnOperand () m).2
      else
        runMiriBounded body fuel m'
    | (m', .ok false) =>
      .returned m' (.error (.stack .emptyStack))
    | (m', .error err) =>
      .error m' err

/-- Multi-step bounded execution correspondence between `runAnnealBounded` and
`runMiriBounded`: after any number of steps `fuel`, either both machines are
still running in `StateRel`-related states (preserving `ValidFrameLocation` and
`NonAddrTakenImmediate`), both returned normally with `ImmediateRel`-related
return values in `_0`, or both halted with undefined behavior. -/
inductive RunRel (body : CapturedMir) (nonAddrTaken : Nat → Prop := fun _ => True) :
    AnnealRunOutcome → MiriRunOutcome → Prop where
  | running (s' : MachineState) (m' : AnnealStepState) :
      StateRel body s' m' →
      ValidFrameLocation body s'.frame →
      NonAddrTakenImmediate body nonAddrTaken m' →
      RunRel body nonAddrTaken (.running s') (.running m')
  | returned (decl0 : LocalDecl) (retVal : Value) (mem' : Memory)
      (m' : AnnealStepState) (retImm : Miri.Interpreter.Immediate AnnealProv) :
      get? body.localDecls 0 = some decl0 →
      ImmediateRel decl0.ty body.layouts retVal retImm →
      m'.stack.frames = #[] →
      RunRel body nonAddrTaken (.returned retVal mem') (.returned m' (.ok (.immediate retImm)))
  | ub (m' : AnnealStepState) (msg : String) :
      RunRel body nonAddrTaken (.faulted .ub) (.error m' (.undefinedBehavior msg))

/-- Fuel-bounded whole-body multi-step lockstep simulation under `WellTypedBody`. -/
theorem run_wellTypedBody_simulation
    {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    (fuel : Nat)
    {s : MachineState} {m : AnnealStepState}
    (hbody : WellTypedBody body nonAddrTaken)
    (hstate : StateRel body s m)
    (hloc : ValidFrameLocation body s.frame)
    (himm : NonAddrTakenImmediate body nonAddrTaken m) :
    RunRel body nonAddrTaken
      (runAnnealBounded body fuel s)
      (runMiriBounded body fuel m) := by
  induction fuel generalizing s m with
  | zero =>
    exact .running s m hstate hloc himm
  | succ fuel ih =>
    have hstep := step_wellTypedBody_simulation hbody hstate hloc himm
    have hloc' : ∀ s', stepMirFn body s = .step s' → ValidFrameLocation body s'.frame :=
      fun _ hs => ValidFrameLocation.preserved hbody hstate hloc hs
    have himm' := NonAddrTakenImmediate.preserved hbody hstate hloc himm
    unfold runAnnealBounded runMiriBounded
    generalize ha : stepMirFn body s = aRes at hstep hloc'
    generalize hm : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = mRes at hstep himm'
    cases hstep with
    | step s' m' hstate' =>
      rcases hstate' with ⟨tf', htf', hrc', hrp', hfr', hcal', hstack', hbor', hprot', hcaller', hdisjoint⟩
      have hemp : m'.stack.frames.isEmpty = false := by
        rw [htf']; rfl
      simp only [hemp, Bool.false_eq_true, ↓reduceIte]
      exact ih (StateRel.mk tf' htf' hrc' hrp' hfr' hcal' hstack' hbor' hprot' hcaller' hdisjoint)
        (hloc' s' rfl) (himm' rfl)
    | retRoot decl0 retVal retImm mem' m' hdecl0 hop0 himmRel hm' =>
      subst hm'
      have hemp : ({ m with stack := ⟨#[]⟩ } : AnnealStepState).stack.frames.isEmpty = true := rfl
      simp only [hemp, ↓reduceIte, hop0]
      exact .returned decl0 retVal mem' _ retImm hdecl0 himmRel rfl
    | ub m' msg =>
      exact .ub m' msg

/-- Fuel-bounded multi-step bisimulation stated directly on `runAnnealBounded`
and `runMiriBounded` without `RunRel`: after `fuel` steps, running states,
normal returns (including `ImmediateRel` agreement on the returned value in `_0`),
and undefined behavior correspond if and only if, with zero `unsupported` or
other non-UB failures reachable. -/
theorem run_wellTypedBody_bisim
    {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    (fuel : Nat)
    {s : MachineState} {m : AnnealStepState}
    (hbody : WellTypedBody body nonAddrTaken)
    (hstate : StateRel body s m)
    (hloc : ValidFrameLocation body s.frame)
    (himm : NonAddrTakenImmediate body nonAddrTaken m) :
    ((∃ s', runAnnealBounded body fuel s = .running s') ↔
      (∃ m', runMiriBounded body fuel m = .running m')) ∧
    (∀ s' m',
      runAnnealBounded body fuel s = .running s' →
      runMiriBounded body fuel m = .running m' →
      StateRel body s' m') ∧
    ((∃ retVal mem', runAnnealBounded body fuel s = .returned retVal mem') ↔
      (∃ m' retImm, runMiriBounded body fuel m = .returned m' (.ok (.immediate retImm)))) ∧
    (∀ retVal mem' m' retImm,
      runAnnealBounded body fuel s = .returned retVal mem' →
      runMiriBounded body fuel m = .returned m' (.ok (.immediate retImm)) →
      ∃ decl0, get? body.localDecls 0 = some decl0 ∧
        ImmediateRel decl0.ty body.layouts retVal retImm) ∧
    (runAnnealBounded body fuel s = .faulted .ub ↔
      ∃ m' msg, runMiriBounded body fuel m = .error m' (.undefinedBehavior msg)) ∧
    ((∃ s', runAnnealBounded body fuel s = .running s') ∨
      (∃ retVal mem', runAnnealBounded body fuel s = .returned retVal mem') ∨
      runAnnealBounded body fuel s = .faulted .ub) := by
  have h := run_wellTypedBody_simulation fuel hbody hstate hloc himm
  generalize runAnnealBounded body fuel s = aOut at h ⊢
  generalize runMiriBounded body fuel m = mOut at h ⊢
  cases h with
  | running s' m' hst _ _ =>
    refine ⟨⟨fun _ => ⟨m', rfl⟩, fun _ => ⟨s', rfl⟩⟩, ?_,
      ⟨fun ⟨_, _, hc⟩ => (by cases hc), fun ⟨_, _, hc⟩ => (by cases hc)⟩,
      fun _ _ _ _ hc => (by cases hc),
      ⟨fun hc => (by cases hc), fun ⟨_, _, hc⟩ => (by cases hc)⟩,
      Or.inl ⟨s', rfl⟩⟩
    intro s₁ m₁ hs₁ hm₁
    cases hs₁; cases hm₁; exact hst
  | returned decl0 retVal mem' m' retImm hdecl0 himmRel _ =>
    refine ⟨⟨fun ⟨_, hc⟩ => (by cases hc), fun ⟨_, hc⟩ => (by cases hc)⟩,
      fun _ _ hc => (by cases hc),
      ⟨fun _ => ⟨m', retImm, rfl⟩, fun _ => ⟨retVal, mem', rfl⟩⟩, ?_,
      ⟨fun hc => (by cases hc), fun ⟨_, _, hc⟩ => (by cases hc)⟩,
      Or.inr (Or.inl ⟨retVal, mem', rfl⟩)⟩
    intro rv₁ mem₁ m₁ ri₁ ha₁ hm₁
    cases ha₁; cases hm₁
    exact ⟨decl0, hdecl0, himmRel⟩
  | ub m' msg =>
    exact ⟨⟨fun ⟨_, hc⟩ => (by cases hc), fun ⟨_, hc⟩ => (by cases hc)⟩,
      fun _ _ hc => (by cases hc),
      ⟨fun ⟨_, _, hc⟩ => (by cases hc), fun ⟨_, _, hc⟩ => (by cases hc)⟩,
      fun _ _ _ _ hc => (by cases hc),
      ⟨fun _ => ⟨m', msg, rfl⟩, fun _ => rfl⟩,
      Or.inr (Or.inr rfl)⟩

end LeanMiriSpec.Correspondence

