/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.MiniRustEval

/-!
# Symbolic evaluation of Anneal's MIR semantics on fragment bodies

Facts about `Trusted.Rustc.V2026_06_01.MirSemantics` (`evalOperand`,
`evalRvalue`, `evalScalarBinOp`, `evalStmt`, `evalTerminator`, `stepMirFn`)
on fragment statements and terminators. These lemmas only *compute* Anneal's
trusted definitions; they do not restate or modify them.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Sequence
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-- Slot facts for Anneal locals (the Anneal half of `FrameOk`). -/
def SlotsOk (decls : List LocalDecl) (locals : List LocalSlot) : Prop :=
  ∀ (i : Nat) d slot, decls[i]? = some d → locals[i]? = some slot → SlotOk (itOf d) slot

theorem evalOperand_frag (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk decls locals) (hn : locals.length = decls.length)
    (it : Gen.IntType) (op : Operand) (hok : operandOk decls it op = true)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation) (layouts : Layout.LayoutTable)
    (callerLocals : List LocalSlot) :
    (∀ bits, opBits locals op = some bits →
      evalOperand locals op borrows globals layouts callerLocals =
        .ok (.scalar ⟨bits, it.size.bytes⟩) locals) ∧
    (opBits locals op = none → evalOperand locals op borrows globals layouts callerLocals = .ub) := by
  match op, hok with
  | .copy ⟨j, []⟩, hok =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hj, hty⟩ := hok
    have hjl : j < locals.length := by rw [hn]; exact hj
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    have hit : itOf d = it := by
      simp [operandIntType, hd] at hty
      simp [itOf, hty]
    have hs : locals[j]? = some locals[j] := by simp [hjl]
    have hslot := hslots j d _ hd hs
    rw [hit] at hslot
    unfold evalOperand
    simp only [opBits, get?]
    generalize locals[j] = slot at hs hslot
    match slot, hslot with
    | .uninit, _ => simp [hs]
    | .init (.scalar sc), hsc =>
      obtain ⟨hsz, _⟩ := hsc
      refine ⟨fun bits hb => ?_, fun hnone => by simp [hs] at hnone⟩
      simp [hs] at hb
      subst hb
      simp [hs, readProjectedValue, ← hsz]
  | .constant c, hok =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hty, htr⟩ := hok
    simp only [operandIntType] at hty
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp htr
    simp only [translateOperand, hty] at he
    match hv : c.val, he with
    | .scalar (.int ⟨bits, sz⟩), he =>
      simp only at he
      split at he
      · next hc =>
        obtain ⟨hsz, _⟩ := hc
        refine ⟨fun bits' hb => ?_, fun hnone => by simp [opBits, hv] at hnone⟩
        simp [opBits, hv] at hb
        subst hb
        simp [evalOperand, hv, evalConstValue, hsz]
      · simp at he

theorem wrap_eq_toNat (v : Nat) (n : Nat) :
    MirSemantics.wrapScalarBits v (MirSemantics.scalarModulus n) = (((v : Int)) % 2 ^ (8 * n)).toNat := by
  rw [wrapScalarBits_eq, scalarModulus_eq]
  have : ((v : Int) % 2 ^ (8 * n)) = ((v % 2 ^ (8 * n) : Nat) : Int) := by
    rw [Int.natCast_emod]; push_cast; rfl
  rw [this, Int.toNat_natCast]

theorem scalarPow2_eq (k : Nat) : MirSemantics.scalarPow2 k = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show 2 * MirSemantics.scalarPow2 k = 2 ^ (k + 1)
    rw [ih, Nat.pow_succ, Nat.mul_comm]

theorem two_pow_div_two (n : Nat) (hn : 0 < n) : Nat.div (2 ^ n) 2 = 2 ^ (n - 1) := by
  change 2 ^ n / 2 = 2 ^ (n - 1)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [Nat.pow_succ]

theorem two_pow_byte_split (sz : Nat) (hsz : sz ≠ 0) :
    2 ^ (8 * sz) = 2 * 2 ^ (8 * sz - 1) ∧ 2 ≤ 2 ^ (8 * sz - 1) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k, 8 * sz = k + 1 := ⟨8 * sz - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
  · exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ 8 * sz - 1)

theorem nat_ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.ble_eq])

theorem nat_beq_eq_decide (a b : Nat) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.beq_eq])

theorem nat_div_eq_div (a b : Nat) : Nat.div a b = a / b := rfl

theorem nat_mod_eq_mod (a b : Nat) : Nat.mod a b = a % b := rfl

theorem isSignedNegative_eq (v sz : Nat) (hsz : sz ≠ 0) (hv : v < 2 ^ (8 * sz)) :
    MirSemantics.isSignedNegative v sz = decide (2 ^ (8 * sz - 1) ≤ v) := by
  simp only [MirSemantics.isSignedNegative, nat_beq_eq_decide, decide_eq_false hsz,
    scalarModulus_eq, two_pow_div_two (8 * sz) (by omega), wrapScalarBits_eq,
    Nat.mod_eq_of_lt hv, nat_ble_eq_decide]

theorem canRepresent_unsigned (sz : Nat) (hsz : sz ≠ 0) (v : Int) :
    IntType.can_represent ⟨.Unsigned, ⟨sz⟩⟩ v =
      decide (0 ≤ v ∧ v < ((2 ^ (8 * sz) : Nat) : Int)) := by
  have hp : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  apply Bool.eq_iff_iff.mpr
  unfold IntType.can_represent
  rw [inBounds_iff _ _ _ (by simp [Size.bits]; omega)]
  simp only [windowLo, Size.bits, decide_eq_true_eq]
  rw [hp]
  omega

theorem canRepresent_signed (sz : Nat) (hsz : sz ≠ 0) (v : Int) :
    IntType.can_represent ⟨.Signed, ⟨sz⟩⟩ v =
      decide (-((2 ^ (8 * sz - 1) : Nat) : Int) ≤ v ∧ v < ((2 ^ (8 * sz - 1) : Nat) : Int)) := by
  have hp1 : (2 : Int) ^ (8 * sz - 1) = ((2 ^ (8 * sz - 1) : Nat) : Int) := by push_cast; rfl
  have hp2 : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  apply Bool.eq_iff_iff.mpr
  unfold IntType.can_represent
  rw [inBounds_iff _ _ _ (by simp [Size.bits]; omega)]
  have hpred := two_pow_pred_add (8 * sz) (by omega)
  simp only [windowLo, Size.bits, decide_eq_true_eq]
  rw [hp1, hp2] at hpred ⊢
  omega

theorem nat_emod_toNat_of_lt (q M : Nat) (hqM : q < M) :
    ((q : Int) % (M : Int)).toNat = q := by
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]

theorem neg_nat_emod_toNat (q M : Nat) (hq0 : 0 < q) (hqM : q < M) :
    ((- (q : Int)) % (M : Int)).toNat = M - q := by
  have : (- (q : Int)) % (M : Int) = (- (q : Int)) + (M : Int) := by
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

theorem signedOverflowAdd_eq (x y sz : Nat) (hsz : sz ≠ 0)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    MirSemantics.signedOverflowAdd x y sz =
      !IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
        (intFromBits x ⟨.Signed, ⟨sz⟩⟩ + intFromBits y ⟨.Signed, ⟨sz⟩⟩) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
  have hsum_lt : (x + y) % 2 ^ (8 * sz) < 2 ^ (8 * sz) := Nat.mod_lt _ (by omega)
  have hsum_mod : (x + y) % 2 ^ (8 * sz) =
      if x + y < 2 ^ (8 * sz) then x + y else x + y - 2 ^ (8 * sz) := by
    split
    · next hlt => exact Nat.mod_eq_of_lt hlt
    · next hge =>
      have heq : x + y = (x + y - 2 ^ (8 * sz)) + 2 ^ (8 * sz) := by omega
      conv => lhs; rw [heq]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  simp only [MirSemantics.signedOverflowAdd, scalarModulus_eq, Nat.add_eq, wrapScalarBits_eq,
    isSignedNegative_eq x sz hsz hx, isSignedNegative_eq y sz hsz hy,
    isSignedNegative_eq _ sz hsz hsum_lt, canRepresent_signed sz hsz,
    intFromBits]
  rw [hsum_mod, hp]
  clear hp hsum_lt hsum_mod
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

theorem signedOverflowSub_eq (x y sz : Nat) (hsz : sz ≠ 0)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    MirSemantics.signedOverflowSub x y sz =
      !IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
        (intFromBits x ⟨.Signed, ⟨sz⟩⟩ - intFromBits y ⟨.Signed, ⟨sz⟩⟩) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  simp only [MirSemantics.signedOverflowSub, scalarModulus_eq, Nat.add_eq, Nat.sub_eq,
    wrapScalarBits_eq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, nat_ble_eq_decide,
    isSignedNegative_eq x sz hsz hx, isSignedNegative_eq y sz hsz hy,
    canRepresent_signed sz hsz, intFromBits]
  rw [hp]
  clear hp
  by_cases hyx : y ≤ x
  · have hlt : x - y < 2 ^ (8 * sz) := by omega
    simp only [decide_eq_true hyx, Nat.mod_eq_of_lt hlt, isSignedNegative_eq _ sz hsz hlt]
    clear hlt
    generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy ⊢
    generalize 2 ^ (8 * sz) = M at hM hx hy ⊢
    apply Bool.eq_iff_iff.mpr
    by_cases hxH : H ≤ x <;> by_cases hyH : H ≤ y <;> by_cases hdH : H ≤ x - y <;>
      simp [hxH, hyH, hdH, show x < H ↔ ¬(H ≤ x) by omega, show y < H ↔ ¬(H ≤ y) by omega] <;>
      omega
  · have hlt : 2 ^ (8 * sz) + x - y < 2 ^ (8 * sz) := by omega
    simp only [decide_eq_false hyx, Nat.mod_eq_of_lt hlt, isSignedNegative_eq _ sz hsz hlt]
    clear hlt
    generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy ⊢
    generalize 2 ^ (8 * sz) = M at hM hx hy ⊢
    apply Bool.eq_iff_iff.mpr
    by_cases hxH : H ≤ x <;> by_cases hyH : H ≤ y <;> by_cases hdH : H ≤ M + x - y <;>
      simp [hxH, hyH, hdH, show x < H ↔ ¬(H ≤ x) by omega, show y < H ↔ ¬(H ≤ y) by omega] <;>
      omega

theorem signedOverflowMul_eq (x y sz : Nat) (hsz : sz ≠ 0)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    MirSemantics.signedOverflowMul x y sz =
      !IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
        (intFromBits x ⟨.Signed, ⟨sz⟩⟩ * intFromBits y ⟨.Signed, ⟨sz⟩⟩) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
  unfold MirSemantics.signedOverflowMul
  simp only [nat_beq_eq_decide, decide_eq_false hsz, scalarModulus_eq,
    two_pow_div_two (8 * sz) (by omega), wrapScalarBits_eq,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    isSignedNegative_eq x sz hsz hx, isSignedNegative_eq y sz hsz hy,
    nat_ble_eq_decide, Nat.sub_eq, Nat.mul_eq, canRepresent_signed sz hsz, intFromBits]
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  rw [hp]
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

theorem intFromBits_eq_zero_iff (it : Gen.IntType) (hsz : it.size.bytes ≠ 0)
    (v : Nat) (hv : v < 2 ^ (8 * it.size.bytes)) :
    intFromBits v it = 0 ↔ v = 0 := by
  have hzero : intFromBits 0 it = 0 := by
    rcases it with ⟨s, ⟨sz⟩⟩
    cases s with
    | Unsigned => rfl
    | Signed => simp [intFromBits, Nat.two_pow_pos _]
  rw [← hzero]
  exact intFromBits_inj it v 0 hv (Nat.two_pow_pos _)

theorem evalSignedDiv_spec (x y sz : Nat) (hsz : sz ≠ 0)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) (hy0 : y ≠ 0)
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    (∀ z, intBinEval .Div (intFromBits x ⟨.Signed, ⟨sz⟩⟩)
        (intFromBits y ⟨.Signed, ⟨sz⟩⟩) ⟨.Signed, ⟨sz⟩⟩ = some z →
      MirSemantics.evalSignedDiv x y sz locals mem =
        .ok (.scalar ⟨(z % 2 ^ (8 * sz)).toNat, sz⟩) locals mem) ∧
    (intBinEval .Div (intFromBits x ⟨.Signed, ⟨sz⟩⟩)
        (intFromBits y ⟨.Signed, ⟨sz⟩⟩) ⟨.Signed, ⟨sz⟩⟩ = none →
      MirSemantics.evalSignedDiv x y sz locals mem = .ub) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
  have hyInt0 : intFromBits y ⟨.Signed, ⟨sz⟩⟩ ≠ 0 := by
    rw [Ne, intFromBits_eq_zero_iff ⟨.Signed, ⟨sz⟩⟩ hsz y hy]; exact hy0
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  simp only [MirSemantics.evalSignedDiv, intBinEval, hyInt0, ↓reduceIte, scalarModulus_eq,
    Nat.mul_eq, Nat.sub_eq, Nat.mul_comm sz 8, scalarPow2_eq, wrapScalarBits_eq,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    isSignedNegative_eq x sz hsz hx, isSignedNegative_eq y sz hsz hy,
    nat_beq_eq_decide, nat_div_eq_div, canRepresent_signed sz hsz]
  rw [hp]
  by_cases hovf : x = 2 ^ (8 * sz - 1) ∧ y = 2 ^ (8 * sz) - 1
  · obtain ⟨rfl, rfl⟩ := hovf
    have hnot1 : ¬(2 ^ (8 * sz - 1) < 2 ^ (8 * sz - 1)) := Nat.lt_irrefl _
    have hnot2 : ¬(2 ^ (8 * sz) - 1 < 2 ^ (8 * sz - 1)) := by omega
    simp only [decide_true, Bool.and_self, intFromBits, hnot1, hnot2, ↓reduceIte]
    rw [hp]
    have hx' : ((2 ^ (8 * sz - 1) : Nat) : Int) - ((2 ^ (8 * sz) : Nat) : Int) =
        -((2 ^ (8 * sz - 1) : Nat) : Int) := by omega
    have hy' : ((2 ^ (8 * sz) - 1 : Nat) : Int) - ((2 ^ (8 * sz) : Nat) : Int) =
        -((1 : Nat) : Int) := by omega
    rw [hx', hy', tdiv_neg_neg _ 1 (by omega) (by omega), Nat.div_one]
    rw [decide_eq_false (by omega : ¬(-((2 ^ (8 * sz - 1) : Nat) : Int) ≤ ((2 ^ (8 * sz - 1) : Nat) : Int) ∧
        ((2 ^ (8 * sz - 1) : Nat) : Int) < ((2 ^ (8 * sz - 1) : Nat) : Int)))]
    simp
  · have hcond : (decide (x = 2 ^ (8 * sz - 1)) && decide (y = 2 ^ (8 * sz) - 1)) = false := by
      rw [Bool.and_eq_false_iff]; simp only [decide_eq_false_iff_not]; omega
    simp only [hcond, intFromBits]
    rw [hp]
    generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy hovf ⊢
    generalize 2 ^ (8 * sz) = M at hM hx hy hovf ⊢
    by_cases hxH : x < H <;> by_cases hyH : y < H
    · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
        decide_eq_false (by omega : ¬(H ≤ y))]
      rw [tdiv_nat_nat]
      have hqH : x / y < H := Nat.lt_of_le_of_lt (Nat.div_le_self x y) hxH
      generalize x / y = q at hqH ⊢
      rw [decide_eq_true (by omega : -(H : Int) ≤ (q : Int) ∧ (q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
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
      rw [decide_eq_true (by omega : -(H : Int) ≤ -(q : Int) ∧ -(q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
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
      rw [decide_eq_true (by omega : -(H : Int) ≤ -(q : Int) ∧ -(q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
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
      rw [decide_eq_true (by omega : -(H : Int) ≤ (q : Int) ∧ (q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      by_cases hq0 : q = 0
      · subst hq0; simp
      · rw [decide_eq_false hq0]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega : q < M), nat_emod_toNat_of_lt q M (by omega)]

theorem evalSignedRem_spec (x y sz : Nat) (hsz : sz ≠ 0)
    (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) (hy0 : y ≠ 0)
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    (∀ z, intBinEval .Rem (intFromBits x ⟨.Signed, ⟨sz⟩⟩)
        (intFromBits y ⟨.Signed, ⟨sz⟩⟩) ⟨.Signed, ⟨sz⟩⟩ = some z →
      MirSemantics.evalSignedRem x y sz locals mem =
        .ok (.scalar ⟨(z % 2 ^ (8 * sz)).toNat, sz⟩) locals mem) ∧
    (intBinEval .Rem (intFromBits x ⟨.Signed, ⟨sz⟩⟩)
        (intFromBits y ⟨.Signed, ⟨sz⟩⟩) ⟨.Signed, ⟨sz⟩⟩ = none →
      MirSemantics.evalSignedRem x y sz locals mem = .ub) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
  have hyInt0 : intFromBits y ⟨.Signed, ⟨sz⟩⟩ ≠ 0 := by
    rw [Ne, intFromBits_eq_zero_iff ⟨.Signed, ⟨sz⟩⟩ hsz y hy]; exact hy0
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  simp only [MirSemantics.evalSignedRem, intBinEval, hyInt0, ↓reduceIte, scalarModulus_eq,
    Nat.mul_eq, Nat.sub_eq, Nat.mul_comm sz 8, scalarPow2_eq, wrapScalarBits_eq,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    isSignedNegative_eq x sz hsz hx, isSignedNegative_eq y sz hsz hy,
    nat_beq_eq_decide, nat_mod_eq_mod, canRepresent_signed sz hsz]
  rw [hp]
  by_cases hovf : x = 2 ^ (8 * sz - 1) ∧ y = 2 ^ (8 * sz) - 1
  · obtain ⟨rfl, rfl⟩ := hovf
    have hnot1 : ¬(2 ^ (8 * sz - 1) < 2 ^ (8 * sz - 1)) := Nat.lt_irrefl _
    have hnot2 : ¬(2 ^ (8 * sz) - 1 < 2 ^ (8 * sz - 1)) := by omega
    simp only [decide_true, Bool.and_self, intFromBits, hnot1, hnot2, ↓reduceIte]
    rw [hp]
    have hx' : ((2 ^ (8 * sz - 1) : Nat) : Int) - ((2 ^ (8 * sz) : Nat) : Int) =
        -((2 ^ (8 * sz - 1) : Nat) : Int) := by omega
    have hy' : ((2 ^ (8 * sz) - 1 : Nat) : Int) - ((2 ^ (8 * sz) : Nat) : Int) =
        -((1 : Nat) : Int) := by omega
    rw [hx', hy', tdiv_neg_neg _ 1 (by omega) (by omega), Nat.div_one]
    rw [decide_eq_false (by omega : ¬(-((2 ^ (8 * sz - 1) : Nat) : Int) ≤ ((2 ^ (8 * sz - 1) : Nat) : Int) ∧
        ((2 ^ (8 * sz - 1) : Nat) : Int) < ((2 ^ (8 * sz - 1) : Nat) : Int)))]
    simp
  · have hcond : (decide (x = 2 ^ (8 * sz - 1)) && decide (y = 2 ^ (8 * sz) - 1)) = false := by
      rw [Bool.and_eq_false_iff]; simp only [decide_eq_false_iff_not]; omega
    simp only [hcond, intFromBits]
    rw [hp]
    generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy hovf ⊢
    generalize 2 ^ (8 * sz) = M at hM hx hy hovf ⊢
    by_cases hxH : x < H <;> by_cases hyH : y < H
    · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
        decide_eq_false (by omega : ¬(H ≤ y))]
      rw [tdiv_nat_nat, tmod_nat_nat]
      have hqH : x / y < H := Nat.lt_of_le_of_lt (Nat.div_le_self x y) hxH
      have hrH : x % y < H := Nat.lt_trans (Nat.mod_lt x (by omega)) hyH
      generalize x / y = q at hqH ⊢
      generalize x % y = r at hrH ⊢
      rw [decide_eq_true (by omega : -(H : Int) ≤ (q : Int) ∧ (q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      by_cases hr0 : r = 0
      · subst hr0; simp
      · rw [decide_eq_false hr0]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega : r < M), nat_emod_toNat_of_lt r M (by omega)]
    · simp only [hxH, hyH, ↓reduceIte, decide_eq_false (by omega : ¬(H ≤ x)),
        decide_eq_true (by omega : H ≤ y)]
      have hy' : (y : Int) - (M : Int) = -((M - y : Nat) : Int) := by omega
      rw [hy', tdiv_nat_neg x (M - y) (by omega), tmod_nat_neg x (M - y) (by omega)]
      have hqH : x / (M - y) < H := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxH
      have hrH : x % (M - y) ≤ H :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))
      generalize x / (M - y) = q at hqH ⊢
      generalize x % (M - y) = r at hrH ⊢
      rw [decide_eq_true (by omega : -(H : Int) ≤ -(q : Int) ∧ -(q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      by_cases hr0 : r = 0
      · subst hr0; simp
      · rw [decide_eq_false hr0]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega : r < M), nat_emod_toNat_of_lt r M (by omega)]
    · simp only [hxH, hyH, ↓reduceIte, decide_eq_true (by omega : H ≤ x),
        decide_eq_false (by omega : ¬(H ≤ y))]
      have hx' : (x : Int) - (M : Int) = -((M - x : Nat) : Int) := by omega
      rw [hx', tdiv_neg_nat (M - x) y (by omega) hy0, tmod_neg_nat (M - x) y (by omega) hy0]
      have hqH : (M - x) / y ≤ H := Nat.le_trans (Nat.div_le_self _ _) (by omega)
      have hrH : (M - x) % y < H := Nat.lt_trans (Nat.mod_lt _ (by omega)) hyH
      generalize (M - x) / y = q at hqH ⊢
      generalize (M - x) % y = r at hrH ⊢
      rw [decide_eq_true (by omega : -(H : Int) ≤ -(q : Int) ∧ -(q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      by_cases hr0 : r = 0
      · subst hr0; simp
      · rw [decide_eq_false hr0]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega : M - r < M),
          neg_nat_emod_toNat r M (by omega) (by omega)]
    · simp only [hxH, hyH, ↓reduceIte, decide_eq_true (by omega : H ≤ x),
        decide_eq_true (by omega : H ≤ y)]
      have hx' : (x : Int) - (M : Int) = -((M - x : Nat) : Int) := by omega
      have hy' : (y : Int) - (M : Int) = -((M - y : Nat) : Int) := by omega
      rw [hx', hy', tdiv_neg_neg (M - x) (M - y) (by omega) (by omega),
        tmod_neg_neg (M - x) (M - y) (by omega) (by omega)]
      have hqH : (M - x) / (M - y) < H := by
        by_cases hxEq : x = H
        · rw [hxEq, show M - H = H by omega]
          exact Nat.div_lt_self (by omega) (by omega)
        · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      have hrH : (M - x) % (M - y) ≤ H :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))
      generalize (M - x) / (M - y) = q at hqH ⊢
      generalize (M - x) % (M - y) = r at hrH ⊢
      rw [decide_eq_true (by omega : -(H : Int) ≤ (q : Int) ∧ (q : Int) < (H : Int))]
      simp only [↓reduceIte]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      by_cases hr0 : r = 0
      · subst hr0; simp
      · rw [decide_eq_false hr0]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega : M - r < M),
          neg_nat_emod_toNat r M (by omega) (by omega)]

theorem wrap_add_intFromBits (it : Gen.IntType) (x y : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes)) :
    MirSemantics.wrapScalarBits (x + y) (MirSemantics.scalarModulus it.size.bytes) =
      ((intFromBits x it + intFromBits y it) % 2 ^ (8 * it.size.bytes)).toNat := by
  rw [wrap_eq_toNat]
  congr 1
  rw [Int.add_emod (intFromBits x it), intFromBits_emod x it hx, intFromBits_emod y it hy]
  push_cast; rfl

theorem wrap_sub_intFromBits (it : Gen.IntType) (x y : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes)) :
    (let m := MirSemantics.scalarModulus it.size.bytes
      match Nat.ble y x with
      | true => MirSemantics.wrapScalarBits (x - y) m
      | false => MirSemantics.wrapScalarBits (m + MirSemantics.wrapScalarBits x m -
          MirSemantics.wrapScalarBits y m) m) =
      ((intFromBits x it - intFromBits y it) % 2 ^ (8 * it.size.bytes)).toNat := by
  dsimp only
  have hp : (2 : Int) ^ (8 * it.size.bytes) = ((2 ^ (8 * it.size.bytes) : Nat) : Int) := by
    push_cast; rfl
  have hmod : (intFromBits x it - intFromBits y it) % 2 ^ (8 * it.size.bytes) =
      ((x : Int) - (y : Int)) % 2 ^ (8 * it.size.bytes) := by
    rw [Int.sub_emod (intFromBits x it), intFromBits_emod x it hx, intFromBits_emod y it hy]
  rw [hmod, hp]
  clear hp hmod
  simp only [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    nat_ble_eq_decide]
  generalize 2 ^ (8 * it.size.bytes) = M at hx hy ⊢
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

theorem wrap_mul_intFromBits (it : Gen.IntType) (x y : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes)) :
    MirSemantics.wrapScalarBits (x * y) (MirSemantics.scalarModulus it.size.bytes) =
      ((intFromBits x it * intFromBits y it) % 2 ^ (8 * it.size.bytes)).toNat := by
  rw [wrap_eq_toNat]
  congr 1
  rw [Int.mul_emod (intFromBits x it), intFromBits_emod x it hx, intFromBits_emod y it hy]
  push_cast; rfl

theorem evalScalarBinOp_frag (op : MirAst.BinOp) (iop : Gen.IntBinOp) (hop : translateBinOp op = some iop)
    (it : Gen.IntType) (hsz : it.size.bytes ≠ 0)
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    (∀ z, intBinEval iop (intFromBits x it) (intFromBits y it) it = some z →
      evalScalarBinOp op ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ locals mem
        (match it.signed with | .Unsigned => false | .Signed => true) =
        .ok (.scalar ⟨(z % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩) locals mem) ∧
    (intBinEval iop (intFromBits x it) (intFromBits y it) it = none →
      evalScalarBinOp op ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ locals mem
        (match it.signed with | .Unsigned => false | .Signed => true) = .ub) := by
  rcases it with ⟨signed, ⟨sz⟩⟩
  dsimp only at hsz hx hy ⊢
  have hbeq : Nat.beq sz 0 = false := by rw [nat_beq_eq_decide, decide_eq_false hsz]
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  match op, hop with
  | .add, hop =>
    simp [translateBinOp] at hop; subst hop
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    simp [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.add_eq,
      wrap_add_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy]
  | .sub, hop =>
    simp [translateBinOp] at hop; subst hop
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    have hsub := wrap_sub_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy
    dsimp only at hsub
    simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.sub_eq, Nat.add_eq]
    cases hble : Nat.ble y x <;> simp only [hble] at hsub ⊢ <;> rw [hsub]
  | .mul, hop =>
    simp [translateBinOp] at hop; subst hop
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    simp [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq,
      wrap_mul_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy]
  | .addUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    cases signed with
    | Unsigned =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.add_eq, scalarModulus_eq,
        nat_ble_eq_decide, intBinEval, canRepresent_unsigned sz hsz, intFromBits]
      by_cases hlt : x + y < 2 ^ (8 * sz)
      · rw [decide_eq_false (by omega : ¬(2 ^ (8 * sz) ≤ x + y)),
          decide_eq_true (by omega : 0 ≤ (x : Int) + y ∧ (x : Int) + y < ((2 ^ (8 * sz) : Nat) : Int))]
        refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        simp at hz; subst hz
        have hcast : (x : Int) + (y : Int) = ((x + y : Nat) : Int) := by push_cast; rfl
        rw [hcast, hp, nat_emod_toNat_of_lt (x + y) _ hlt]
      · rw [decide_eq_true (by omega : 2 ^ (8 * sz) ≤ x + y),
          decide_eq_false (by omega : ¬(0 ≤ (x : Int) + y ∧ (x : Int) + y < ((2 ^ (8 * sz) : Nat) : Int)))]
        simp
    | Signed =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.add_eq, intBinEval,
        signedOverflowAdd_eq x y sz hsz hx hy]
      cases hrep : IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
          (intFromBits x ⟨.Signed, ⟨sz⟩⟩ + intFromBits y ⟨.Signed, ⟨sz⟩⟩)
      · simp
      · refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        simp at hz; subst hz
        simp [wrap_add_intFromBits ⟨.Signed, ⟨sz⟩⟩ x y hx hy]
  | .subUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    cases signed with
    | Unsigned =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.sub_eq, scalarModulus_eq,
        nat_ble_eq_decide, intBinEval, canRepresent_unsigned sz hsz, intFromBits]
      by_cases hle : y ≤ x
      · have hlt : x - y < 2 ^ (8 * sz) := by omega
        rw [decide_eq_true hle, decide_eq_false (by omega : ¬(2 ^ (8 * sz) ≤ x - y)),
          decide_eq_true (by omega : 0 ≤ (x : Int) - y ∧ (x : Int) - y < ((2 ^ (8 * sz) : Nat) : Int))]
        refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        simp at hz; subst hz
        have hcast : (x : Int) - (y : Int) = ((x - y : Nat) : Int) := by omega
        rw [hcast, hp, nat_emod_toNat_of_lt (x - y) _ hlt]
      · rw [decide_eq_false hle,
          decide_eq_false (by omega : ¬(0 ≤ (x : Int) - y ∧ (x : Int) - y < ((2 ^ (8 * sz) : Nat) : Int)))]
        simp
    | Signed =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.sub_eq, Nat.add_eq, intBinEval,
        signedOverflowSub_eq x y sz hsz hx hy]
      cases hrep : IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
          (intFromBits x ⟨.Signed, ⟨sz⟩⟩ - intFromBits y ⟨.Signed, ⟨sz⟩⟩)
      · simp
      · refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        simp at hz; subst hz
        have hsub := wrap_sub_intFromBits ⟨.Signed, ⟨sz⟩⟩ x y hx hy
        dsimp only at hsub
        have hxMod : MirSemantics.wrapScalarBits x (MirSemantics.scalarModulus sz) = x := by
          rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hx]
        have hyMod : MirSemantics.wrapScalarBits y (MirSemantics.scalarModulus sz) = y := by
          rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hy]
        simp only [hxMod, hyMod] at hsub ⊢
        cases hble : Nat.ble y x <;> simp only [hble, Bool.not_true] at hsub ⊢ <;> rw [hsub]
  | .mulUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    cases signed with
    | Unsigned =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq, scalarModulus_eq,
        nat_ble_eq_decide, intBinEval, canRepresent_unsigned sz hsz, intFromBits]
      have hcast : (x : Int) * (y : Int) = ((x * y : Nat) : Int) := by push_cast; rfl
      by_cases hlt : x * y < 2 ^ (8 * sz)
      · rw [decide_eq_false (by omega : ¬(2 ^ (8 * sz) ≤ x * y)), hcast,
          decide_eq_true (by omega : 0 ≤ ((x * y : Nat) : Int) ∧ ((x * y : Nat) : Int) < ((2 ^ (8 * sz) : Nat) : Int))]
        refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        injection hz with hz; subst hz
        rw [hp, nat_emod_toNat_of_lt (x * y) _ hlt]
      · rw [decide_eq_true (by omega : 2 ^ (8 * sz) ≤ x * y), hcast,
          decide_eq_false (by omega : ¬(0 ≤ ((x * y : Nat) : Int) ∧ ((x * y : Nat) : Int) < ((2 ^ (8 * sz) : Nat) : Int)))]
        simp
    | Signed =>
      simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq, intBinEval,
        signedOverflowMul_eq x y sz hsz hx hy]
      cases hrep : IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
          (intFromBits x ⟨.Signed, ⟨sz⟩⟩ * intFromBits y ⟨.Signed, ⟨sz⟩⟩)
      · simp
      · refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        simp at hz; subst hz
        simp [wrap_mul_intFromBits ⟨.Signed, ⟨sz⟩⟩ x y hx hy]
  | .div, hop =>
    simp [translateBinOp] at hop; subst hop
    by_cases hy0 : y = 0
    · subst hy0
      have hyInt0 := (intFromBits_eq_zero_iff ⟨signed, ⟨sz⟩⟩ hsz 0 (Nat.two_pow_pos _)).mpr rfl
      simp [evalScalarBinOp, hbeq, Nat.beq_refl, intBinEval, hyInt0]
    · have hyBeq : Nat.beq y 0 = false := by rw [nat_beq_eq_decide, decide_eq_false hy0]
      cases signed with
      | Unsigned =>
        have hyInt0 : (y : Int) ≠ 0 := by omega
        have hqlt : x / y < 2 ^ (8 * sz) := Nat.lt_of_le_of_lt (Nat.div_le_self x y) hx
        simp only [evalScalarBinOp, hbeq, Nat.beq_refl, hyBeq, nat_div_eq_div, wrapScalarBits_eq,
          scalarModulus_eq, Nat.mod_eq_of_lt hqlt, intBinEval, intFromBits, hyInt0, ↓reduceIte,
          canRepresent_unsigned sz hsz]
        rw [tdiv_nat_nat]
        generalize x / y = q at hqlt ⊢
        rw [decide_eq_true (by omega : 0 ≤ (q : Int) ∧ (q : Int) < ((2 ^ (8 * sz) : Nat) : Int))]
        refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        injection hz with hz; subst hz
        rw [hp, nat_emod_toNat_of_lt q _ hqlt]
      | Signed =>
        simp only [evalScalarBinOp, hbeq, Nat.beq_refl, hyBeq]
        exact evalSignedDiv_spec x y sz hsz hx hy hy0 locals mem
  | .rem, hop =>
    simp [translateBinOp] at hop; subst hop
    by_cases hy0 : y = 0
    · subst hy0
      have hyInt0 := (intFromBits_eq_zero_iff ⟨signed, ⟨sz⟩⟩ hsz 0 (Nat.two_pow_pos _)).mpr rfl
      simp [evalScalarBinOp, hbeq, Nat.beq_refl, intBinEval, hyInt0]
    · have hyBeq : Nat.beq y 0 = false := by rw [nat_beq_eq_decide, decide_eq_false hy0]
      cases signed with
      | Unsigned =>
        have hyInt0 : (y : Int) ≠ 0 := by omega
        have hqlt : x / y < 2 ^ (8 * sz) := Nat.lt_of_le_of_lt (Nat.div_le_self x y) hx
        have hrlt : x % y < 2 ^ (8 * sz) := Nat.lt_trans (Nat.mod_lt x (by omega)) hy
        simp only [evalScalarBinOp, hbeq, Nat.beq_refl, hyBeq, nat_mod_eq_mod, wrapScalarBits_eq,
          scalarModulus_eq, Nat.mod_eq_of_lt hrlt, intBinEval, intFromBits, hyInt0, ↓reduceIte,
          canRepresent_unsigned sz hsz]
        rw [tdiv_nat_nat, tmod_nat_nat]
        generalize x / y = q at hqlt ⊢
        generalize x % y = r at hrlt ⊢
        rw [decide_eq_true (by omega : 0 ≤ (q : Int) ∧ (q : Int) < ((2 ^ (8 * sz) : Nat) : Int))]
        refine ⟨fun z hz => ?_, fun h => by simp at h⟩
        injection hz with hz; subst hz
        rw [hp, nat_emod_toNat_of_lt r _ hrlt]
      | Signed =>
        simp only [evalScalarBinOp, hbeq, Nat.beq_refl, hyBeq]
        exact evalSignedRem_spec x y sz hsz hx hy hy0 locals mem

theorem opBits_lt (decls : List LocalDecl) (locals : List LocalSlot) (hslots : SlotsOk decls locals)
    (it : Gen.IntType) (op : Operand) (hok : operandOk decls it op = true) (bits : Nat)
    (hb : opBits locals op = some bits) : bits < 2 ^ (8 * it.size.bytes) := by
  match op, hok, hb with
  | .copy ⟨j, []⟩, hok, hb =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hj, hty⟩ := hok
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    have hit : itOf d = it := by
      simp [operandIntType, hd] at hty
      simp [itOf, hty]
    simp only [opBits] at hb
    match hs : locals[j]?, hb with
    | some (.init (.scalar sc)), hb =>
      simp at hb; subst hb
      have := hslots j d _ hd hs
      rw [hit] at this
      exact this.2
  | .constant c, hok, hb =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hty, htr⟩ := hok
    simp only [operandIntType] at hty
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp htr
    simp only [translateOperand, hty] at he
    simp only [opBits] at hb
    match hv : c.val, he, hb with
    | .scalar (.int ⟨bits', sz⟩), he, hb =>
      simp only at he hb
      simp at hb; subst hb
      split at he
      · next hc => obtain ⟨hsz, hlt⟩ := hc; subst hsz; exact hlt
      · simp at he

theorem wrap_neg_eq_toNat (x sz : Nat) (hx : x < 2 ^ (8 * sz)) :
    let m := MirSemantics.scalarModulus sz
    MirSemantics.wrapScalarBits (m - MirSemantics.wrapScalarBits x m) m =
      ((- (x : Int)) % 2 ^ (8 * sz)).toNat := by
  dsimp only
  have hm := scalarModulus_eq sz
  have hpos : 0 < 2 ^ (8 * sz) := Nat.two_pow_pos _
  have hp : ((2 : Nat) ^ (8 * sz) : Int) = 2 ^ (8 * sz) := by push_cast; rfl
  simp only [wrapScalarBits_eq, hm, Nat.mod_eq_of_lt hx]
  by_cases hx0 : x = 0
  · subst hx0; simp
  · have hlt : 2 ^ (8 * sz) - x < 2 ^ (8 * sz) := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have : (- (x : Int)) % 2 ^ (8 * sz) = (- (x : Int)) + 2 ^ (8 * sz) := by
      rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [this]
    omega

theorem wrap_not_eq_toNat (x sz : Nat) (hx : x < 2 ^ (8 * sz)) :
    let m := MirSemantics.scalarModulus sz
    (m - 1) - MirSemantics.wrapScalarBits x m =
      ((- (x : Int) - 1) % 2 ^ (8 * sz)).toNat := by
  dsimp only
  have hm := scalarModulus_eq sz
  have hpos : 0 < 2 ^ (8 * sz) := Nat.two_pow_pos _
  have hp : ((2 : Nat) ^ (8 * sz) : Int) = 2 ^ (8 * sz) := by push_cast; rfl
  simp only [wrapScalarBits_eq, hm, Nat.mod_eq_of_lt hx]
  have : (- (x : Int) - 1) % 2 ^ (8 * sz) = (- (x : Int) - 1) + 2 ^ (8 * sz) := by
    rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [this]
  omega

theorem operandTy_of_operandOk (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (srcIt : Gen.IntType) (op : Operand) (hok : operandOk decls srcIt op = true) :
    ∃ ty, MirSemantics.operandTy decls layouts op = some ty ∧ intTypeOf ty = some srcIt := by
  match op, hok with
  | .copy ⟨j, []⟩, hok =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq, operandIntType] at hok
    obtain ⟨hj, hty⟩ := hok
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    simp [hd] at hty
    exact ⟨d.ty, by simp [MirSemantics.operandTy, MirSemantics.placeTy, get?, hd,
      MirSemantics.resolveProjectedTy], hty⟩
  | .constant c, hok =>
    simp only [operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hty, _⟩ := hok
    simp only [operandIntType] at hty
    exact ⟨c.ty, rfl, hty⟩

theorem intTypeOf_kind {ty : MirAst.Ty} {it : Gen.IntType} (h : intTypeOf ty = some it) :
    ((∃ u, ty.kind = .uint u) ∧ it.signed = .Unsigned) ∨
    ((∃ i, ty.kind = .int i) ∧ it.signed = .Signed) := by
  unfold intTypeOf intTyBytes at h
  split at h <;> simp at h <;> subst h <;> simp_all

theorem evalUnaryNot_frag (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (it : Gen.IntType) (hsz : it.size.bytes ≠ 0) (op : Operand) (hok : operandOk decls it op = true)
    (x : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (locals : List LocalSlot)
    (mem : MirSemantics.Memory) :
    MirSemantics.evalUnaryNot ⟨x, it.size.bytes⟩ (MirSemantics.operandTy decls layouts op) locals mem =
      .ok (.scalar ⟨((- (x : Int) - 1) % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩) locals mem := by
  obtain ⟨ty, hty, hit⟩ := operandTy_of_operandOk decls layouts it op hok
  have hbeq : Nat.beq it.size.bytes 0 = false := by
    cases h : Nat.beq it.size.bytes 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hsz
  rcases intTypeOf_kind hit with ⟨⟨u, hu⟩, _⟩ | ⟨⟨i, hi⟩, _⟩
  · simp [MirSemantics.evalUnaryNot, hty, hu, hbeq, Nat.sub_eq, wrap_not_eq_toNat x _ hx]
  · simp [MirSemantics.evalUnaryNot, hty, hi, hbeq, Nat.sub_eq, wrap_not_eq_toNat x _ hx]

theorem intCastTargetBytes_of_intTypeOf {ty : MirAst.Ty} {it : Gen.IntType}
    (h : intTypeOf ty = some it) :
    MirSemantics.intCastTargetBytes ty.kind = some it.size.bytes := by
  unfold intTypeOf intTyBytes at h
  split at h <;> simp at h <;> subst h <;> simp_all [MirSemantics.intCastTargetBytes]

theorem operandIsSigned_of_operandOk (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (srcIt : Gen.IntType) (op : Operand) (hok : operandOk decls srcIt op = true) :
    MirSemantics.operandIsSigned decls op layouts =
      match srcIt.signed with | .Unsigned => false | .Signed => true := by
  obtain ⟨ty, hty, hit⟩ := operandTy_of_operandOk decls layouts srcIt op hok
  simp only [MirSemantics.operandIsSigned, hty, MirSemantics.tyIsSigned]
  rcases intTypeOf_kind hit with ⟨⟨u, hu⟩, hs⟩ | ⟨⟨i, hi⟩, hs⟩
  · simp [hu, hs]
  · simp [hi, hs]

theorem castBits_eq_toNat (srcIt it : Gen.IntType) (hsrcGood : GoodSize srcIt.size.bytes)
    (x : Nat) (hx : x < 2 ^ (8 * srcIt.size.bytes)) :
    let m := MirSemantics.scalarModulus it.size.bytes
    (match srcIt.signed with
      | .Unsigned => MirSemantics.wrapScalarBits x m
      | .Signed =>
        match Nat.ble it.size.bytes srcIt.size.bytes with
        | true => MirSemantics.wrapScalarBits x m
        | false => MirSemantics.signExtendBits x srcIt.size.bytes it.size.bytes) =
      (intFromBits x srcIt % 2 ^ (8 * it.size.bytes)).toNat := by
  dsimp only
  rcases srcIt with ⟨s, ⟨srcBytes⟩⟩
  rcases it with ⟨_, ⟨dstBytes⟩⟩
  dsimp only at hsrcGood hx ⊢
  have hsrcPos : 0 < srcBytes := hsrcGood.pos
  cases s with
  | Unsigned =>
    rw [wrap_eq_toNat]
    rfl
  | Signed =>
    simp only [intFromBits]
    cases hble : Nat.ble dstBytes srcBytes with
    | true =>
      dsimp only
      have hle : dstBytes ≤ srcBytes := Nat.ble_eq.mp hble
      rw [wrap_eq_toNat]
      by_cases hneg : x < 2 ^ (8 * srcBytes - 1)
      · simp [hneg]
      · simp only [hneg, ↓reduceIte]
        congr 1
        have hdvd : ((2 : Int) ^ (8 * dstBytes)) ∣ (2 : Int) ^ (8 * srcBytes) := by
          have hdvdNat : (2 : Nat) ^ (8 * dstBytes) ∣ 2 ^ (8 * srcBytes) :=
            Nat.pow_dvd_pow 2 (by omega)
          exact_mod_cast hdvdNat
        rw [Int.sub_emod, Int.emod_eq_zero_of_dvd hdvd, Int.sub_zero,
          Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
    | false =>
      dsimp only
      have hlt : srcBytes < dstBytes :=
        Nat.lt_of_not_ge (fun hle => by rw [Nat.ble_eq.mpr hle] at hble; cases hble)
      have hsrcBeq : Nat.beq srcBytes 0 = false := by
        cases h : Nat.beq srcBytes 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
      have hpowLe : 2 ^ (8 * srcBytes) ≤ 2 ^ (8 * dstBytes) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hdstPos : 0 < 2 ^ (8 * dstBytes) := Nat.two_pow_pos _
      have hpSrc : ((2 : Nat) ^ (8 * srcBytes) : Int) = 2 ^ (8 * srcBytes) := by push_cast; rfl
      have hpDst : ((2 : Nat) ^ (8 * dstBytes) : Int) = 2 ^ (8 * dstBytes) := by push_cast; rfl
      have hhalf : Nat.div (2 ^ (8 * srcBytes)) 2 = 2 ^ (8 * srcBytes - 1) :=
        two_pow_div_two (8 * srcBytes) (by omega)
      simp only [MirSemantics.signExtendBits, hble, MirSemantics.isSignedNegative, hsrcBeq,
        scalarModulus_eq, wrapScalarBits_eq, Nat.mod_eq_of_lt hx, hhalf,
        Nat.add_eq, Nat.sub_eq]
      by_cases hneg : x < 2 ^ (8 * srcBytes - 1)
      · have hbleNeg : Nat.ble (2 ^ (8 * srcBytes - 1)) x = false := by
          cases h : Nat.ble (2 ^ (8 * srcBytes - 1)) x
          · rfl
          · exact absurd (Nat.ble_eq.mp h) (by omega)
        simp only [hneg, ↓reduceIte, hbleNeg]
        have hxDst : (x : Int) < 2 ^ (8 * dstBytes) := by omega
        rw [Int.emod_eq_of_lt (by omega) hxDst, Int.toNat_natCast]
      · have hbleNeg : Nat.ble (2 ^ (8 * srcBytes - 1)) x = true :=
          Nat.ble_eq.mpr (by omega)
        simp only [hneg, ↓reduceIte, hbleNeg]
        have : ((x : Int) - 2 ^ (8 * srcBytes)) % 2 ^ (8 * dstBytes) =
            ((x : Int) - 2 ^ (8 * srcBytes)) + 2 ^ (8 * dstBytes) := by
          rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
        rw [this]
        omega

theorem evalRvalue_frag (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk decls locals) (hn : locals.length = decls.length)
    (it : Gen.IntType) (hsz : it.size.bytes ≠ 0) (rv : Rvalue) (hok : rvalueOk decls it rv = true)
    (mem : MirSemantics.Memory) (layouts : Layout.LayoutTable) :
    (∀ r, rvBits decls locals it rv = some r →
      evalRvalue locals rv mem decls layouts = .ok (.scalar ⟨r, it.size.bytes⟩) locals mem) ∧
    (rvBits decls locals it rv = none → evalRvalue locals rv mem decls layouts = .ub) := by
  match rv, hok with
  | .use op, hok =>
    simp only [rvalueOk] at hok
    obtain ⟨hsome, hnone⟩ :=
      evalOperand_frag decls locals hslots hn it op hok mem.borrows mem.globals layouts mem.callerLocals
    refine ⟨fun r hr => ?_, fun h => ?_⟩
    · simp [evalRvalue, hsome r hr]
    · simp [evalRvalue, hnone h]
  | .unaryOp uop op, hok =>
    simp only [rvalueOk, Bool.and_eq_true] at hok
    obtain ⟨huop, hok⟩ := hok
    obtain ⟨iuop, hiuop⟩ := Option.isSome_iff_exists.mp huop
    obtain ⟨ha, hanone⟩ :=
      evalOperand_frag decls locals hslots hn it op hok mem.borrows mem.globals layouts mem.callerLocals
    have hbeq : Nat.beq it.size.bytes 0 = false := by
      cases h : Nat.beq it.size.bytes 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hsz
    cases hxo : opBits locals op with
    | none =>
      refine ⟨fun r hr => by simp [rvBits, hiuop, hxo] at hr, fun _ => ?_⟩
      cases uop <;> simp [translateUnOp] at hiuop <;> simp [evalRvalue, hanone hxo]
    | some x =>
      refine ⟨fun r hr => ?_, fun h => by simp [rvBits, hiuop, hxo] at h⟩
      simp [rvBits, hiuop, hxo] at hr
      subst hr
      have hx := opBits_lt decls locals hslots it op hok x hxo
      cases uop <;> simp [translateUnOp] at hiuop <;> subst hiuop
      · simp only [evalRvalue, ha x hxo, evalUnaryNot_frag decls layouts it hsz op hok x hx, intUnArith]
      · simp [evalRvalue, ha x hxo, hbeq, Nat.sub_eq, wrap_neg_eq_toNat x _ hx, intUnArith]
  | .binaryOp op a b, hok =>
    simp only [rvalueOk, Bool.and_eq_true] at hok
    obtain ⟨⟨hop, hoka⟩, hokb⟩ := hok
    obtain ⟨iop, hiop⟩ := Option.isSome_iff_exists.mp hop
    obtain ⟨ha, hanone⟩ :=
      evalOperand_frag decls locals hslots hn it a hoka mem.borrows mem.globals layouts mem.callerLocals
    obtain ⟨hb, hbnone⟩ :=
      evalOperand_frag decls locals hslots hn it b hokb mem.borrows mem.globals layouts mem.callerLocals
    cases hxa : opBits locals a with
    | none =>
      refine ⟨fun r hr => by simp [rvBits, hiop, hxa] at hr, fun _ => ?_⟩
      simp [evalRvalue, hanone hxa]
    | some x =>
      cases hyb : opBits locals b with
      | none =>
        refine ⟨fun r hr => by simp [rvBits, hiop, hxa, hyb] at hr, fun _ => ?_⟩
        simp [evalRvalue, ha x hxa, hbnone hyb]
      | some y =>
        have hx := opBits_lt decls locals hslots it a hoka x hxa
        have hy := opBits_lt decls locals hslots it b hokb y hyb
        have hsigned := operandIsSigned_of_operandOk decls layouts it a hoka
        obtain ⟨hbinOk, hbinNone⟩ :=
          evalScalarBinOp_frag op iop hiop it hsz x y hx hy locals mem
        cases hz : intBinEval iop (intFromBits x it) (intFromBits y it) it with
        | none =>
          refine ⟨fun r hr => by simp [rvBits, hiop, hxa, hyb, hz] at hr, fun _ => ?_⟩
          simp [evalRvalue, ha x hxa, hb y hyb, hsigned, hbinNone hz]
        | some z =>
          refine ⟨fun r hr => ?_, fun h => by simp [rvBits, hiop, hxa, hyb, hz] at h⟩
          simp [rvBits, hiop, hxa, hyb, hz] at hr
          subst hr
          simp [evalRvalue, ha x hxa, hb y hyb, hsigned, hbinOk z hz]
  | .cast .intToInt op targetTy, hok =>
    simp only [rvalueOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨htgt, hsrc⟩ := hok
    cases hsrcIt : operandIntType decls op with
    | none => simp [hsrcIt] at hsrc
    | some srcIt =>
      simp only [hsrcIt] at hsrc
      obtain ⟨ha, hanone⟩ :=
        evalOperand_frag decls locals hslots hn srcIt op hsrc mem.borrows mem.globals layouts mem.callerLocals
      obtain ⟨ty, _, hsrcTy⟩ := operandTy_of_operandOk decls layouts srcIt op hsrc
      have hsrcGood : GoodSize srcIt.size.bytes := intTypeOf_good hsrcTy
      have hsrcBeq : Nat.beq srcIt.size.bytes 0 = false := by
        cases h : Nat.beq srcIt.size.bytes 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) (Nat.ne_of_gt hsrcGood.pos)
      have htgtBytes := intCastTargetBytes_of_intTypeOf htgt
      have hsigned := operandIsSigned_of_operandOk decls layouts srcIt op hsrc
      cases hxo : opBits locals op with
      | none =>
        refine ⟨fun r hr => by simp [rvBits, hsrcIt, hxo] at hr, fun _ => ?_⟩
        simp [evalRvalue, hanone hxo]
      | some x =>
        refine ⟨fun r hr => ?_, fun h => by simp [rvBits, hsrcIt, hxo] at h⟩
        simp [rvBits, hsrcIt, hxo] at hr
        subst hr
        have hx := opBits_lt decls locals hslots srcIt op hsrc x hxo
        have hcast := castBits_eq_toNat srcIt it hsrcGood x hx
        dsimp only at hcast
        simp only [evalRvalue, ha x hxo, hsrcBeq, htgtBytes, hsigned]
        cases hs : srcIt.signed <;> simp only [hs] at hcast ⊢
        · rw [hcast]
        · cases hble : Nat.ble it.size.bytes srcIt.size.bytes <;> simp only [hble] at hcast ⊢ <;> rw [hcast]

theorem evalStmt_assign (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (rv : Rvalue) (span : String) (hslots : SlotsOk decls s.frame.locals)
    (hn : s.frame.locals.length = decls.length) (d : LocalDecl) (hd : decls[i]? = some d)
    (hsz : (itOf d).size.bytes ≠ 0) (hok : rvalueOk decls (itOf d) rv = true)
    (hbor : s.memory.borrows = []) (hprot : s.memory.activeProtectors = []) :
    (∀ r, rvBits decls s.frame.locals (itOf d) rv = some r →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.scalar ⟨r, (itOf d).size.bytes⟩)))
          { s.memory with borrows := [] }))) ∧
    (rvBits decls s.frame.locals (itOf d) rv = none →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hi : i < s.frame.locals.length := by rw [hn]; exact (List.getElem?_eq_some_iff.mp hd).1
  have hs : s.frame.locals[i]? = some s.frame.locals[i] := by simp [hi]
  have hslot := hslots i d _ hd hs
  have hlive : s.frame.locals[i] ≠ .dead := by
    intro h; rw [h] at hslot; exact hslot
  obtain ⟨hok', hnone⟩ := evalRvalue_frag decls s.frame.locals hslots hn (itOf d) hsz rv hok s.memory layouts
  refine ⟨fun r hr => ?_, fun h => ?_⟩
  · simp only [evalStmt, hok' r hr, get?, hs, set?, hi, hprot, hbor, invalidateConflictingBorrows_nil]
    cases hsl : s.frame.locals[i] with
    | dead => exact absurd hsl hlive
    | uninit => simp [MirStepNode.step]
    | init v => simp [MirStepNode.step]
  · simp [evalStmt, hnone h]

theorem evalStmt_placeMention (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (span : String) (hslots : SlotsOk decls s.frame.locals)
    (hn : s.frame.locals.length = decls.length) (hi : i < decls.length) :
    evalStmt s ⟨.placeMention ⟨i, []⟩, span⟩ decls layouts =
      .tau (.running (advanceStmt s s.frame.locals)) := by
  have hil : i < s.frame.locals.length := by rw [hn]; exact hi
  obtain ⟨d, hd⟩ : ∃ d, decls[i]? = some d := ⟨decls[i], by simp [hi]⟩
  have hs : s.frame.locals[i]? = some s.frame.locals[i] := by simp [hil]
  have hslot := hslots i d _ hd hs
  have hlive : s.frame.locals[i] ≠ .dead := by
    intro h; rw [h] at hslot; exact hslot
  simp only [evalStmt, get?, hs]
  cases hsl : s.frame.locals[i] with
  | dead => exact absurd hsl hlive
  | uninit => simp [MirStepNode.step]
  | init v => simp [MirStepNode.step]

theorem stepMirFn_stmt (body : CapturedMir) (s : MachineState) (bb : BasicBlockData)
    (stmt : MirAst.Statement) (hcallee : s.memory.activeCallee = none)
    (hphase : body.phase = .runtimePostCleanup)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some stmt) :
    stepMirFn body s = evalStmt s stmt body.localDecls body.layouts := by
  simp [stepMirFn, hcallee, hphase, get?, hbb, hst]

theorem stepMirFn_term (body : CapturedMir) (s : MachineState) (bb : BasicBlockData)
    (hcallee : s.memory.activeCallee = none) (hphase : body.phase = .runtimePostCleanup)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hlen : s.frame.stmtIdx = bb.statements.length) :
    stepMirFn body s = evalTerminator s bb.terminator (some body) := by
  simp [stepMirFn, hcallee, hphase, get?, hbb, hlen, length]

end MiniRustSpec.Correspondence
