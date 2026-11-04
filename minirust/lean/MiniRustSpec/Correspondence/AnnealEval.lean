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
  ∀ (i : Nat) d slot, decls[i]? = some d → locals[i]? = some slot → SlotOk (tyOf d) slot

/-- Evaluating a fragment operand of fragment type `T` (stored like `it`) in
Anneal's semantics: the scalar of its bit pattern, or UB for an uninitialized
local. -/
theorem evalOperand_fragT (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk decls locals) (hn : locals.length = decls.length)
    {T : Gen.Type} {it : Gen.IntType} (hT : FragTy T it) (op : Operand)
    (hok : OperandOkT decls T op)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation) (layouts : Layout.LayoutTable)
    (callerLocals : List LocalSlot) :
    (∀ bits, opBits locals op = some bits →
      evalOperand locals op borrows globals layouts callerLocals =
        .ok (.scalar ⟨bits, it.size.bytes⟩) locals) ∧
    (opBits locals op = none → evalOperand locals op borrows globals layouts callerLocals = .ub) := by
  match op, hok with
  | .copy ⟨j, []⟩, hok =>
    obtain ⟨hj, hty⟩ := hok
    have hjl : j < locals.length := by rw [hn]; exact hj
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    have hTd : tyOf d = T := by
      simp only [operandType, hd, Option.bind_some] at hty
      exact tyOf_of_scalarTypeOf hty
    have hs : locals[j]? = some locals[j] := by simp [hjl]
    have hslot := hslots j d _ hd hs
    rw [hTd] at hslot
    unfold evalOperand
    simp only [opBits, get?]
    generalize locals[j] = slot at hs hslot
    match slot, hslot with
    | .uninit, _ => simp [hs]
    | .init (.scalar sc), hsc =>
      obtain ⟨hsz, _⟩ := hsc
      rw [hT.tyBytes] at hsz
      refine ⟨fun bits hb => ?_, fun hnone => by simp [hs] at hnone⟩
      simp [hs] at hb
      subst hb
      simp [hs, readProjectedValue, ← hsz]
  | .constant c, hok =>
    obtain ⟨hty, htr⟩ := hok
    simp only [operandType] at hty
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp htr
    rcases scalarTypeOf_cases hty with ⟨hb, hTb⟩ | ⟨it', hit', hTi⟩
    · subst hTb
      cases hT
      simp only [translateOperand, hb, ↓reduceIte] at he
      match hv : c.val, he with
      | .scalar (.int ⟨bits, sz⟩), he =>
        simp only at he
        split at he
        · next hc =>
          obtain ⟨hsz, _⟩ := hc
          subst hsz
          refine ⟨fun bits' hb' => ?_, fun hnone => by simp [opBits, hv] at hnone⟩
          simp [opBits, hv] at hb'
          subst hb'
          simp [evalOperand, hv, evalConstValue, u8Ty]
        · simp at he
    · subst hTi
      cases hT with
      | int _ _ =>
        simp only [translateOperand, intTypeOf_isBoolTy hit', hit', Bool.false_eq_true,
          ↓reduceIte] at he
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

theorem evalOperand_frag (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk decls locals) (hn : locals.length = decls.length)
    (it : Gen.IntType) (op : Operand) (hok : operandOk decls it op = true)
    (borrows : List BorrowEntry) (globals : List MirAst.CapturedAllocation) (layouts : Layout.LayoutTable)
    (callerLocals : List LocalSlot) :
    (∀ bits, opBits locals op = some bits →
      evalOperand locals op borrows globals layouts callerLocals =
        .ok (.scalar ⟨bits, it.size.bytes⟩) locals) ∧
    (opBits locals op = none → evalOperand locals op borrows globals layouts callerLocals = .ub) :=
  evalOperand_fragT decls locals hslots hn (.int it (operandOk_good hok)) op (operandOk_T hok)
    borrows globals layouts callerLocals

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

theorem bits_dvd_two_pow (lhsSz rhsSz : Nat) (hlhs : GoodSize lhsSz) (hrhs : GoodSize rhsSz) :
    ((8 * lhsSz : Nat) : Int) ∣ (2 : Int) ^ (8 * rhsSz) := by
  rcases hlhs with rfl | rfl | rfl | rfl | rfl <;>
    rcases hrhs with rfl | rfl | rfl | rfl | rfl <;> decide

theorem bits_le_half_modulus (lhsSz rhsSz : Nat) (hlhs : GoodSize lhsSz) (hrhs : GoodSize rhsSz) :
    8 * lhsSz ≤ 2 ^ (8 * rhsSz - 1) := by
  rcases hlhs with rfl | rfl | rfl | rfl | rfl <;>
    rcases hrhs with rfl | rfl | rfl | rfl | rfl <;> decide

theorem shift_offset_eq (it rhsIt : Gen.IntType) (hlhs : GoodSize it.size.bytes)
    (hrhs : GoodSize rhsIt.size.bytes) (y : Nat) :
    (intFromBits y rhsIt % (Size.bits it.size : Int)).toNat = y % (it.size.bytes * 8) := by
  rcases it with ⟨_, ⟨lhsSz⟩⟩
  rcases rhsIt with ⟨s, ⟨rhsSz⟩⟩
  dsimp only [Size.bits] at hlhs hrhs ⊢
  rw [Nat.mul_comm lhsSz 8]
  have hcast : ((y % (8 * lhsSz) : Nat) : Int) = (y : Int) % ((8 * lhsSz : Nat) : Int) := by
    rw [Int.natCast_emod]
  cases s with
  | Unsigned =>
    simp only [intFromBits]
    rw [← hcast, Int.toNat_natCast]
  | Signed =>
    simp only [intFromBits]
    split
    · rw [← hcast, Int.toNat_natCast]
    · have hdvd := bits_dvd_two_pow lhsSz rhsSz hlhs hrhs
      rw [Int.sub_emod, Int.emod_eq_zero_of_dvd hdvd, Int.sub_zero,
        Int.emod_emod, ← hcast, Int.toNat_natCast]

theorem unchecked_shift_oob_iff (it rhsIt : Gen.IntType) (hlhs : GoodSize it.size.bytes)
    (hrhs : GoodSize rhsIt.size.bytes) (y : Nat) (hy : y < 2 ^ (8 * rhsIt.size.bytes)) :
    (intFromBits y rhsIt < 0 ∨ intFromBits y rhsIt ≥ (Size.bits it.size : Int)) ↔
      it.size.bytes * 8 ≤ y := by
  rcases it with ⟨_, ⟨lhsSz⟩⟩
  rcases rhsIt with ⟨s, ⟨rhsSz⟩⟩
  dsimp only [Size.bits] at hlhs hrhs hy ⊢
  rw [Nat.mul_comm lhsSz 8]
  have hle := bits_le_half_modulus lhsSz rhsSz hlhs hrhs
  have hp : (2 : Int) ^ (8 * rhsSz) = ((2 ^ (8 * rhsSz) : Nat) : Int) := by push_cast; rfl
  cases s with
  | Unsigned =>
    simp only [intFromBits]
    omega
  | Signed =>
    simp only [intFromBits, hp]
    split <;> omega

theorem unchecked_shift_toNat (lhsSz : Nat) (rhsIt : Gen.IntType)
    (hlhs : GoodSize lhsSz) (hrhs : GoodSize rhsIt.size.bytes)
    (y : Nat) (hlt : y < lhsSz * 8) :
    (intFromBits y rhsIt).toNat = y := by
  rcases rhsIt with ⟨signed, ⟨rhsSz⟩⟩
  dsimp only at hrhs ⊢
  have hle := bits_le_half_modulus lhsSz rhsSz hlhs hrhs
  cases signed with
  | Unsigned => simp [intFromBits]
  | Signed =>
    have hyHalf : y < 2 ^ (8 * rhsSz - 1) := by omega
    simp [intFromBits, hyHalf]

theorem shiftLeftBits_eq (v k m : Nat) :
    MirSemantics.shiftLeftBits v k m = MirSemantics.wrapScalarBits (v * 2 ^ k) m := by
  simp [MirSemantics.shiftLeftBits, Nat.mul_eq, scalarPow2_eq]

theorem shiftLeftBits_intFromBits (it : Gen.IntType) (x k : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) :
    MirSemantics.shiftLeftBits x k (MirSemantics.scalarModulus it.size.bytes) =
      ((intFromBits x it * (2 : Int) ^ k) % 2 ^ (8 * it.size.bytes)).toNat := by
  rw [shiftLeftBits_eq, wrap_eq_toNat]
  congr 1
  have hcast : ((x * 2 ^ k : Nat) : Int) = (x : Int) * (2 : Int) ^ k := by push_cast; rfl
  have hxMod : (x : Int) % (2 : Int) ^ (8 * it.size.bytes) = (x : Int) :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast hx)
  rw [hcast, Int.mul_emod (intFromBits x it), intFromBits_emod x it hx,
    Int.mul_emod (x : Int), hxMod]

theorem shiftRightUnsignedBits_eq (v k : Nat) :
    MirSemantics.shiftRightUnsignedBits v k = v / 2 ^ k := by
  simp [MirSemantics.shiftRightUnsignedBits, nat_div_eq_div, scalarPow2_eq]

theorem shiftRightUnsigned_intFromBits (sz x k : Nat) (hx : x < 2 ^ (8 * sz)) :
    MirSemantics.wrapScalarBits (MirSemantics.shiftRightUnsignedBits x k)
      (MirSemantics.scalarModulus sz) =
      ((intFromBits x ⟨.Unsigned, ⟨sz⟩⟩ / (2 : Int) ^ k) % 2 ^ (8 * sz)).toNat := by
  have hlt : x / 2 ^ k < 2 ^ (8 * sz) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  have hp : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  have hdiv : (x : Int) / (2 : Int) ^ k = ((x / 2 ^ k : Nat) : Int) := by
    have hpk : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) := by push_cast; rfl
    rw [hpk]; rfl
  simp only [shiftRightUnsignedBits_eq, wrapScalarBits_eq, scalarModulus_eq,
    Nat.mod_eq_of_lt hlt, intFromBits]
  rw [hdiv, hp, nat_emod_toNat_of_lt _ _ hlt]

theorem arithmeticShrBits_intFromBits (sz x k : Nat) (hsz : sz ≠ 0)
    (hx : x < 2 ^ (8 * sz)) (hk : k < 8 * sz) :
    MirSemantics.arithmeticShrBits x sz k =
      ((intFromBits x ⟨.Signed, ⟨sz⟩⟩ / (2 : Int) ^ k) % 2 ^ (8 * sz)).toNat := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
  have hp : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  have hpk : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) := by push_cast; rfl
  have hsplit : 2 ^ (8 * sz) = 2 ^ (8 * sz - k) * 2 ^ k := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have hQpos : 0 < 2 ^ (8 * sz - k) := Nat.two_pow_pos _
  have hSpos : 0 < 2 ^ k := Nat.two_pow_pos _
  have hqlt : x / 2 ^ k < 2 ^ (8 * sz - k) :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hsplit]; exact hx)
  have hltM : x / 2 ^ k < 2 ^ (8 * sz) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  simp only [MirSemantics.arithmeticShrBits, scalarModulus_eq, wrapScalarBits_eq,
    Nat.mod_eq_of_lt hx, shiftRightUnsignedBits_eq, isSignedNegative_eq x sz hsz hx,
    Nat.mul_eq, Nat.sub_eq, Nat.add_eq, Nat.mul_comm sz 8, scalarPow2_eq, intFromBits]
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
    rw [hed, nat_emod_toNat_of_lt _ _ hltM]

theorem emod_pow_succ_two (w : Int) (k : Nat) :
    (w % (2 : Int) ^ (k + 1)) % 2 = w % 2 :=
  Int.emod_emod_of_dvd w ⟨(2 : Int) ^ k, by rw [Int.pow_succ, Int.mul_comm]⟩

theorem ediv_two_emod_pow (w : Int) (k : Nat) :
    (w / 2) % (2 : Int) ^ k = (w % (2 : Int) ^ (k + 1)) / 2 := by
  have hM : 0 < (2 : Int) ^ k := two_pow_pos k
  have h2M : (2 : Int) ^ (k + 1) = 2 * (2 : Int) ^ k := by rw [Int.pow_succ, Int.mul_comm]
  rw [h2M]
  generalize (2 : Int) ^ k = M at hM ⊢
  have hr0 : 0 ≤ w % (2 * M) := Int.emod_nonneg w (by omega)
  have hrlt : w % (2 * M) < 2 * M := Int.emod_lt_of_pos w (by omega)
  have hw : w = w % (2 * M) + (M * (w / (2 * M))) * 2 := by
    have hdiv := Int.emod_def w (2 * M)
    have hmul : 2 * M * (w / (2 * M)) = (M * (w / (2 * M))) * 2 := by
      rw [Int.mul_assoc, Int.mul_comm 2 _]
    omega
  conv => lhs; rw [hw]
  rw [Int.add_mul_ediv_right _ _ (by decide : (2 : Int) ≠ 0),
    Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]

theorem two_mul_add_bit_emod_toNat (Q : Int) (bit k : Nat) (hbit : bit < 2) :
    ((2 * Q + (bit : Int)) % (2 : Int) ^ (k + 1)).toNat =
      bit + 2 * (Q % (2 : Int) ^ k).toNat := by
  have hM : 0 < (2 : Int) ^ k := two_pow_pos k
  have h2M : (2 : Int) ^ (k + 1) = 2 * (2 : Int) ^ k := by rw [Int.pow_succ, Int.mul_comm]
  rw [h2M]
  generalize (2 : Int) ^ k = M at hM ⊢
  have hr0 : 0 ≤ Q % M := Int.emod_nonneg Q (by omega)
  have hrlt : Q % M < M := Int.emod_lt_of_pos Q hM
  have hrew : 2 * Q + (bit : Int) = (2 * (Q % M) + (bit : Int)) + (2 * M) * (Q / M) := by
    have hdiv := Int.emod_def Q M
    have hmul : 2 * (M * (Q / M)) = (2 * M) * (Q / M) := (Int.mul_assoc 2 M (Q / M)).symm
    omega
  rw [hrew, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem intBitMeasure_pos {a : Int} (h0 : a ≠ 0) (h1 : a ≠ -1) : 0 < intBitMeasure a := by
  simp only [intBitMeasure]; split <;> omega

theorem intBitMeasure_ediv_lt {a : Int} (h0 : a ≠ 0) (h1 : a ≠ -1) :
    intBitMeasure (a / 2) < intBitMeasure a := by
  simp only [intBitMeasure]; split <;> (try split) <;> omega

theorem intBitRec_irrel (z o : Int → Int) (f : Int → Int → Int) (n m : Nat) (a b : Int)
    (hn : intBitMeasure a ≤ n) (hm : intBitMeasure a ≤ m) :
    intBitRec z o f n a b = intBitRec z o f m a b := by
  induction n generalizing m a b with
  | zero =>
    by_cases ha0 : a = 0
    · subst ha0; cases m <;> simp [intBitRec]
    · by_cases ha1 : a = -1
      · subst ha1; cases m <;> simp [intBitRec]
      · exact absurd (intBitMeasure_pos ha0 ha1) (by omega)
  | succ n ih =>
    by_cases ha0 : a = 0
    · subst ha0; cases m <;> simp [intBitRec]
    · by_cases ha1 : a = -1
      · subst ha1; cases m <;> simp [intBitRec]
      · have hpos := intBitMeasure_pos ha0 ha1
        have hlt := intBitMeasure_ediv_lt ha0 ha1
        cases m with
        | zero => exact absurd hpos (by omega)
        | succ m =>
          simp only [intBitRec, ha0, ha1, ↓reduceIte]
          rw [ih m (a / 2) (b / 2) (by omega) (by omega)]

theorem intBitRec_unfold (z o : Int → Int) (f : Int → Int → Int) (a b : Int) :
    intBitRec z o f (intBitMeasure a) a b =
      if a = 0 then z b
      else if a = -1 then o b
      else 2 * intBitRec z o f (intBitMeasure (a / 2)) (a / 2) (b / 2) + f (a % 2) (b % 2) := by
  rw [intBitRec_irrel z o f (intBitMeasure a) (intBitMeasure a + 1) a b (Nat.le_refl _) (Nat.le_succ _)]
  simp only [intBitRec]
  by_cases ha0 : a = 0
  · simp [ha0]
  · by_cases ha1 : a = -1
    · simp [ha1]
    · simp only [ha0, ha1, ↓reduceIte]
      have hlt := intBitMeasure_ediv_lt ha0 ha1
      rw [intBitRec_irrel z o f (intBitMeasure a) (intBitMeasure (a / 2)) (a / 2) (b / 2)
        (by omega) (Nat.le_refl _)]

theorem intBitAnd_unfold (a b : Int) :
    intBitAnd a b =
      if a = 0 then 0
      else if a = -1 then b
      else 2 * intBitAnd (a / 2) (b / 2) + (if a % 2 = 1 ∧ b % 2 = 1 then 1 else 0) :=
  intBitRec_unfold _ _ _ a b

theorem intBitOr_unfold (a b : Int) :
    intBitOr a b =
      if a = 0 then b
      else if a = -1 then -1
      else 2 * intBitOr (a / 2) (b / 2) + (if a % 2 = 1 ∨ b % 2 = 1 then 1 else 0) :=
  intBitRec_unfold _ _ _ a b

theorem intBitXor_unfold (a b : Int) :
    intBitXor a b =
      if a = 0 then b
      else if a = -1 then -b - 1
      else 2 * intBitXor (a / 2) (b / 2) + (if a % 2 = b % 2 then 0 else 1) :=
  intBitRec_unfold _ _ _ a b

theorem intBitAnd_step (a b : Int) :
    intBitAnd a b = 2 * intBitAnd (a / 2) (b / 2) + (if a % 2 = 1 ∧ b % 2 = 1 then 1 else 0) := by
  rw [intBitAnd_unfold a b]
  by_cases ha0 : a = 0
  · subst ha0
    have hd : (0 : Int) / 2 = 0 := by decide
    have hm : (0 : Int) % 2 = 0 := by decide
    rw [hd, hm, intBitAnd_unfold 0 (b / 2)]
    simp
  · by_cases ha1 : a = -1
    · subst ha1
      have hd : (-1 : Int) / 2 = -1 := by decide
      have hm : (-1 : Int) % 2 = 1 := by decide
      rw [hd, hm, intBitAnd_unfold (-1) (b / 2)]
      simp only [show (-1 : Int) ≠ 0 by decide, ↓reduceIte, true_and]
      split <;> omega
    · simp [ha0, ha1]

theorem intBitOr_step (a b : Int) :
    intBitOr a b = 2 * intBitOr (a / 2) (b / 2) + (if a % 2 = 1 ∨ b % 2 = 1 then 1 else 0) := by
  rw [intBitOr_unfold a b]
  by_cases ha0 : a = 0
  · subst ha0
    have hd : (0 : Int) / 2 = 0 := by decide
    have hm : (0 : Int) % 2 = 0 := by decide
    rw [hd, hm, intBitOr_unfold 0 (b / 2)]
    simp only [↓reduceIte, show (0 : Int) = 1 ↔ False by decide, false_or]
    split <;> omega
  · by_cases ha1 : a = -1
    · subst ha1
      have hd : (-1 : Int) / 2 = -1 := by decide
      have hm : (-1 : Int) % 2 = 1 := by decide
      rw [hd, hm, intBitOr_unfold (-1) (b / 2)]
      simp [show (-1 : Int) ≠ 0 by decide]
    · simp [ha0, ha1]

theorem intBitXor_step (a b : Int) :
    intBitXor a b = 2 * intBitXor (a / 2) (b / 2) + (if a % 2 = b % 2 then 0 else 1) := by
  rw [intBitXor_unfold a b]
  by_cases ha0 : a = 0
  · subst ha0
    have hd : (0 : Int) / 2 = 0 := by decide
    have hm : (0 : Int) % 2 = 0 := by decide
    rw [hd, hm, intBitXor_unfold 0 (b / 2)]
    simp only [↓reduceIte]
    split <;> omega
  · by_cases ha1 : a = -1
    · subst ha1
      have hd : (-1 : Int) / 2 = -1 := by decide
      have hm : (-1 : Int) % 2 = 1 := by decide
      rw [hd, hm, intBitXor_unfold (-1) (b / 2)]
      simp only [show (-1 : Int) ≠ 0 by decide, ↓reduceIte]
      split <;> omega
    · simp [ha0, ha1]

theorem bitwiseAndBits_eq_intBitAnd (k x y : Nat) (a b : Int)
    (ha : a % (2 : Int) ^ k = (x : Int) % (2 : Int) ^ k)
    (hb : b % (2 : Int) ^ k = (y : Int) % (2 : Int) ^ k) :
    MirSemantics.bitwiseAndBits k x y = (intBitAnd a b % (2 : Int) ^ k).toNat := by
  induction k generalizing x y a b with
  | zero => simp [MirSemantics.bitwiseAndBits]
  | succ k ih =>
    have ha2 : a % 2 = ((x % 2 : Nat) : Int) := by
      rw [← emod_pow_succ_two a k, ha, emod_pow_succ_two]; omega
    have hb2 : b % 2 = ((y % 2 : Nat) : Int) := by
      rw [← emod_pow_succ_two b k, hb, emod_pow_succ_two]; omega
    have hadiv : (a / 2) % (2 : Int) ^ k = ((x / 2 : Nat) : Int) % (2 : Int) ^ k := by
      rw [ediv_two_emod_pow a k, ha, ← ediv_two_emod_pow (x : Int) k]; rfl
    have hbdiv : (b / 2) % (2 : Int) ^ k = ((y / 2 : Nat) : Int) % (2 : Int) ^ k := by
      rw [ediv_two_emod_pow b k, hb, ← ediv_two_emod_pow (y : Int) k]; rfl
    have hrec := ih (x / 2) (y / 2) (a / 2) (b / 2) hadiv hbdiv
    simp only [MirSemantics.bitwiseAndBits, nat_mod_eq_mod, nat_div_eq_div, Nat.add_eq, Nat.mul_eq]
    rw [intBitAnd_step a b, ha2, hb2, hrec]
    have hbit :
        (if ((x % 2 : Nat) : Int) = 1 ∧ ((y % 2 : Nat) : Int) = 1 then (1 : Int) else 0) =
          (((match Bool.and (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1) with
              | true => 1 | false => 0) : Nat) : Int) ∧
        (match Bool.and (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1) with | true => 1 | false => 0) < 2 := by
      rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hx2 | hx2 <;>
        rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hy2 | hy2 <;>
        simp [hx2, hy2]
    rw [hbit.1, two_mul_add_bit_emod_toNat _ _ k hbit.2]; rfl

theorem bitwiseOrBits_eq_intBitOr (k x y : Nat) (a b : Int)
    (ha : a % (2 : Int) ^ k = (x : Int) % (2 : Int) ^ k)
    (hb : b % (2 : Int) ^ k = (y : Int) % (2 : Int) ^ k) :
    MirSemantics.bitwiseOrBits k x y = (intBitOr a b % (2 : Int) ^ k).toNat := by
  induction k generalizing x y a b with
  | zero => simp [MirSemantics.bitwiseOrBits]
  | succ k ih =>
    have ha2 : a % 2 = ((x % 2 : Nat) : Int) := by
      rw [← emod_pow_succ_two a k, ha, emod_pow_succ_two]; omega
    have hb2 : b % 2 = ((y % 2 : Nat) : Int) := by
      rw [← emod_pow_succ_two b k, hb, emod_pow_succ_two]; omega
    have hadiv : (a / 2) % (2 : Int) ^ k = ((x / 2 : Nat) : Int) % (2 : Int) ^ k := by
      rw [ediv_two_emod_pow a k, ha, ← ediv_two_emod_pow (x : Int) k]; rfl
    have hbdiv : (b / 2) % (2 : Int) ^ k = ((y / 2 : Nat) : Int) % (2 : Int) ^ k := by
      rw [ediv_two_emod_pow b k, hb, ← ediv_two_emod_pow (y : Int) k]; rfl
    have hrec := ih (x / 2) (y / 2) (a / 2) (b / 2) hadiv hbdiv
    simp only [MirSemantics.bitwiseOrBits, nat_mod_eq_mod, nat_div_eq_div, Nat.add_eq, Nat.mul_eq]
    rw [intBitOr_step a b, ha2, hb2, hrec]
    have hbit :
        (if ((x % 2 : Nat) : Int) = 1 ∨ ((y % 2 : Nat) : Int) = 1 then (1 : Int) else 0) =
          (((match Bool.or (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1) with
              | true => 1 | false => 0) : Nat) : Int) ∧
        (match Bool.or (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1) with | true => 1 | false => 0) < 2 := by
      rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hx2 | hx2 <;>
        rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hy2 | hy2 <;>
        simp [hx2, hy2]
    rw [hbit.1, two_mul_add_bit_emod_toNat _ _ k hbit.2]; rfl

theorem bitwiseXorBits_eq_intBitXor (k x y : Nat) (a b : Int)
    (ha : a % (2 : Int) ^ k = (x : Int) % (2 : Int) ^ k)
    (hb : b % (2 : Int) ^ k = (y : Int) % (2 : Int) ^ k) :
    MirSemantics.bitwiseXorBits k x y = (intBitXor a b % (2 : Int) ^ k).toNat := by
  induction k generalizing x y a b with
  | zero => simp [MirSemantics.bitwiseXorBits]
  | succ k ih =>
    have ha2 : a % 2 = ((x % 2 : Nat) : Int) := by
      rw [← emod_pow_succ_two a k, ha, emod_pow_succ_two]; omega
    have hb2 : b % 2 = ((y % 2 : Nat) : Int) := by
      rw [← emod_pow_succ_two b k, hb, emod_pow_succ_two]; omega
    have hadiv : (a / 2) % (2 : Int) ^ k = ((x / 2 : Nat) : Int) % (2 : Int) ^ k := by
      rw [ediv_two_emod_pow a k, ha, ← ediv_two_emod_pow (x : Int) k]; rfl
    have hbdiv : (b / 2) % (2 : Int) ^ k = ((y / 2 : Nat) : Int) % (2 : Int) ^ k := by
      rw [ediv_two_emod_pow b k, hb, ← ediv_two_emod_pow (y : Int) k]; rfl
    have hrec := ih (x / 2) (y / 2) (a / 2) (b / 2) hadiv hbdiv
    simp only [MirSemantics.bitwiseXorBits, nat_mod_eq_mod, nat_div_eq_div, Nat.add_eq, Nat.mul_eq]
    rw [intBitXor_step a b, ha2, hb2, hrec]
    have hbit :
        (if ((x % 2 : Nat) : Int) = ((y % 2 : Nat) : Int) then (0 : Int) else 1) =
          (((match Nat.beq (x % 2) (y % 2) with
              | true => 0 | false => 1) : Nat) : Int) ∧
        (match Nat.beq (x % 2) (y % 2) with | true => 0 | false => 1) < 2 := by
      rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hx2 | hx2 <;>
        rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hy2 | hy2 <;>
        simp [hx2, hy2]
    rw [hbit.1, two_mul_add_bit_emod_toNat _ _ k hbit.2]; rfl

theorem intFromBits_emod_nat (it : Gen.IntType) (v : Nat) (hv : v < 2 ^ (8 * it.size.bytes)) :
    intFromBits v it % (2 : Int) ^ (8 * it.size.bytes) = (v : Int) % (2 : Int) ^ (8 * it.size.bytes) := by
  rw [intFromBits_emod v it hv, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hv)]

theorem bitwiseAndBits_intFromBits (it : Gen.IntType) (x y : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes)) :
    MirSemantics.bitwiseAndBits (it.size.bytes * 8) x y =
      (intBitAnd (intFromBits x it) (intFromBits y it) % (2 : Int) ^ (8 * it.size.bytes)).toNat := by
  rw [Nat.mul_comm _ 8]
  exact bitwiseAndBits_eq_intBitAnd (8 * it.size.bytes) x y _ _
    (intFromBits_emod_nat it x hx) (intFromBits_emod_nat it y hy)

theorem bitwiseOrBits_intFromBits (it : Gen.IntType) (x y : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes)) :
    MirSemantics.bitwiseOrBits (it.size.bytes * 8) x y =
      (intBitOr (intFromBits x it) (intFromBits y it) % (2 : Int) ^ (8 * it.size.bytes)).toNat := by
  rw [Nat.mul_comm _ 8]
  exact bitwiseOrBits_eq_intBitOr (8 * it.size.bytes) x y _ _
    (intFromBits_emod_nat it x hx) (intFromBits_emod_nat it y hy)

theorem bitwiseXorBits_intFromBits (it : Gen.IntType) (x y : Nat)
    (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes)) :
    MirSemantics.bitwiseXorBits (it.size.bytes * 8) x y =
      (intBitXor (intFromBits x it) (intFromBits y it) % (2 : Int) ^ (8 * it.size.bytes)).toNat := by
  rw [Nat.mul_comm _ 8]
  exact bitwiseXorBits_eq_intBitXor (8 * it.size.bytes) x y _ _
    (intFromBits_emod_nat it x hx) (intFromBits_emod_nat it y hy)

theorem evalScalarBinOp_frag (op : MirAst.BinOp) (iop : Gen.IntBinOp) (hop : translateBinOp op = some iop)
    (it rhsIt : Gen.IntType) (hgood : GoodSize it.size.bytes) (hrhsGood : GoodSize rhsIt.size.bytes)
    (hhom : isShiftIntBinOp iop = false → rhsIt = it)
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * rhsIt.size.bytes))
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    (∀ z, intBinEval iop (intFromBits x it) (intFromBits y rhsIt) it = some z →
      evalScalarBinOp op ⟨x, it.size.bytes⟩ ⟨y, rhsIt.size.bytes⟩ locals mem
        (match it.signed with | .Unsigned => false | .Signed => true) =
        .ok (.scalar ⟨(z % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩) locals mem) ∧
    (intBinEval iop (intFromBits x it) (intFromBits y rhsIt) it = none →
      evalScalarBinOp op ⟨x, it.size.bytes⟩ ⟨y, rhsIt.size.bytes⟩ locals mem
        (match it.signed with | .Unsigned => false | .Signed => true) = .ub) := by
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hrhsSz : rhsIt.size.bytes ≠ 0 := Nat.ne_of_gt hrhsGood.pos
  rcases it with ⟨signed, ⟨sz⟩⟩
  dsimp only at hgood hsz hx ⊢
  have hbeq : Nat.beq sz 0 = false := by rw [nat_beq_eq_decide, decide_eq_false hsz]
  have hrhsBeq : Nat.beq rhsIt.size.bytes 0 = false := by
    rw [nat_beq_eq_decide, decide_eq_false hrhsSz]
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  match op, hop with
  | .add, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    simp [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.add_eq,
      wrap_add_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy]
  | .sub, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    have hsub := wrap_sub_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy
    dsimp only at hsub
    simp only [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.sub_eq, Nat.add_eq]
    cases hble : Nat.ble y x <;> simp only [hble] at hsub ⊢ <;> rw [hsub]
  | .mul, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    simp [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq,
      wrap_mul_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy]
  | .bitAnd, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    simp [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq,
      bitwiseAndBits_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy]
  | .bitOr, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    simp [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq,
      bitwiseOrBits_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy]
  | .bitXor, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    simp [evalScalarBinOp, hbeq, Nat.beq_refl, Nat.mul_eq,
      bitwiseXorBits_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx hy]
  | .addUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
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
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
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
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
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
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
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
    have hrhsEq := hhom rfl; subst hrhsEq; dsimp only at hy
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
  | .shl, hop =>
    simp [translateBinOp] at hop; subst hop
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    have hoff := shift_offset_eq ⟨signed, ⟨sz⟩⟩ rhsIt hgood hrhsGood y
    dsimp only at hoff
    simp [evalScalarBinOp, hbeq, hrhsBeq, Nat.mul_eq, nat_mod_eq_mod, hoff,
      shiftLeftBits_intFromBits ⟨signed, ⟨sz⟩⟩ x _ hx]
  | .shr, hop =>
    simp [translateBinOp] at hop; subst hop
    refine ⟨fun z hz => ?_, fun h => by simp [intBinEval] at h⟩
    simp [intBinEval] at hz; subst hz
    have hoff := shift_offset_eq ⟨signed, ⟨sz⟩⟩ rhsIt hgood hrhsGood y
    dsimp only at hoff
    have hklt : y % (sz * 8) < 8 * sz := by rw [Nat.mul_comm]; exact Nat.mod_lt _ (by omega)
    cases signed with
    | Unsigned =>
      simp [evalScalarBinOp, hbeq, hrhsBeq, Nat.mul_eq, nat_mod_eq_mod, hoff,
        shiftRightUnsigned_intFromBits sz x _ hx]
    | Signed =>
      simp [evalScalarBinOp, hbeq, hrhsBeq, Nat.mul_eq, nat_mod_eq_mod, hoff,
        arithmeticShrBits_intFromBits sz x _ hsz hx hklt]
  | .shlUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    have hoob := unchecked_shift_oob_iff ⟨signed, ⟨sz⟩⟩ rhsIt hgood hrhsGood y hy
    dsimp only at hoob
    by_cases hle : sz * 8 ≤ y
    · have hoob' : intFromBits y rhsIt < 0 ∨
          intFromBits y rhsIt ≥ (Size.bits ⟨sz⟩ : Int) := hoob.mpr hle
      simp [evalScalarBinOp, hbeq, hrhsBeq, Nat.mul_eq, nat_ble_eq_decide, decide_eq_true hle,
        intBinEval, hoob']
    · have hnoob : ¬(intFromBits y rhsIt < 0 ∨
          intFromBits y rhsIt ≥ (Size.bits ⟨sz⟩ : Int)) := by
        rw [hoob]; exact hle
      have htoNat := unchecked_shift_toNat sz rhsIt hgood hrhsGood y (by omega)
      simp only [evalScalarBinOp, hbeq, hrhsBeq, Nat.mul_eq, nat_ble_eq_decide, decide_eq_false hle,
        intBinEval, hnoob, ↓reduceIte, htoNat]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      simp [shiftLeftBits_intFromBits ⟨signed, ⟨sz⟩⟩ x y hx]
  | .shrUnchecked, hop =>
    simp [translateBinOp] at hop; subst hop
    have hoob := unchecked_shift_oob_iff ⟨signed, ⟨sz⟩⟩ rhsIt hgood hrhsGood y hy
    dsimp only at hoob
    by_cases hle : sz * 8 ≤ y
    · have hoob' : intFromBits y rhsIt < 0 ∨
          intFromBits y rhsIt ≥ (Size.bits ⟨sz⟩ : Int) := hoob.mpr hle
      simp [evalScalarBinOp, hbeq, hrhsBeq, Nat.mul_eq, nat_ble_eq_decide, decide_eq_true hle,
        intBinEval, hoob']
    · have hnoob : ¬(intFromBits y rhsIt < 0 ∨
          intFromBits y rhsIt ≥ (Size.bits ⟨sz⟩ : Int)) := by
        rw [hoob]; exact hle
      have htoNat := unchecked_shift_toNat sz rhsIt hgood hrhsGood y (by omega)
      have hklt : y < 8 * sz := by omega
      simp only [evalScalarBinOp, hbeq, hrhsBeq, Nat.mul_eq, nat_ble_eq_decide, decide_eq_false hle,
        intBinEval, hnoob, ↓reduceIte, htoNat]
      refine ⟨fun z hz => ?_, fun h => by simp at h⟩
      injection hz with hz; subst hz
      cases signed with
      | Unsigned => simp [shiftRightUnsigned_intFromBits sz x y hx]
      | Signed => simp [arithmeticShrBits_intFromBits sz x y hsz hx hklt]

/-- The bit pattern of a fragment operand of type `T` is valid at `T`. -/
theorem opBits_valid (decls : List LocalDecl) (locals : List LocalSlot) (hslots : SlotsOk decls locals)
    {T : Gen.Type} {it : Gen.IntType} (hT : FragTy T it) (op : Operand)
    (hok : OperandOkT decls T op) (bits : Nat) (hb : opBits locals op = some bits) :
    ValidBits T bits := by
  match op, hok, hb with
  | .copy ⟨j, []⟩, hok, hb =>
    obtain ⟨hj, hty⟩ := hok
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    have hTd : tyOf d = T := by
      simp only [operandType, hd, Option.bind_some] at hty
      exact tyOf_of_scalarTypeOf hty
    simp only [opBits] at hb
    match hs : locals[j]?, hb with
    | some (.init (.scalar sc)), hb =>
      simp at hb; subst hb
      have := hslots j d _ hd hs
      rw [hTd] at this
      exact this.2
  | .constant c, hok, hb =>
    obtain ⟨hty, htr⟩ := hok
    simp only [operandType] at hty
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp htr
    simp only [opBits] at hb
    rcases scalarTypeOf_cases hty with ⟨hbool, hTb⟩ | ⟨it', hit', hTi⟩
    · subst hTb
      simp only [translateOperand, hbool, ↓reduceIte] at he
      match hv : c.val, he, hb with
      | .scalar (.int ⟨bits', sz⟩), he, hb =>
        simp only at he hb
        simp at hb; subst hb
        split at he
        · next hc => exact hc.2
        · simp at he
    · subst hTi
      simp only [translateOperand, intTypeOf_isBoolTy hit', hit', Bool.false_eq_true,
        ↓reduceIte] at he
      match hv : c.val, he, hb with
      | .scalar (.int ⟨bits', sz⟩), he, hb =>
        simp only at he hb
        simp at hb; subst hb
        split at he
        · next hc => obtain ⟨hsz, hlt⟩ := hc; subst hsz; exact hlt
        · simp at he

theorem opBits_lt (decls : List LocalDecl) (locals : List LocalSlot) (hslots : SlotsOk decls locals)
    (it : Gen.IntType) (op : Operand) (hok : operandOk decls it op = true) (bits : Nat)
    (hb : opBits locals op = some bits) : bits < 2 ^ (8 * it.size.bytes) :=
  opBits_valid decls locals hslots (.int it (operandOk_good hok)) op (operandOk_T hok) bits hb

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
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes) (rv : Rvalue) (hok : rvalueOk decls it rv = true)
    (mem : MirSemantics.Memory) (layouts : Layout.LayoutTable) :
    (∀ r, rvBits decls locals it rv = some r →
      evalRvalue locals rv mem decls layouts = .ok (.scalar ⟨r, it.size.bytes⟩) locals mem) ∧
    (rvBits decls locals it rv = none → evalRvalue locals rv mem decls layouts = .ub) := by
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
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
    obtain ⟨iop, rhsIt, hiop, hoka, hrhsTy, hokb, hhom⟩ := rvalueOk_binaryOp hok
    obtain ⟨_, _, hrhsTyOf⟩ := operandTy_of_operandOk decls layouts rhsIt b hokb
    have hrhsGood : GoodSize rhsIt.size.bytes := intTypeOf_good hrhsTyOf
    obtain ⟨ha, hanone⟩ :=
      evalOperand_frag decls locals hslots hn it a hoka mem.borrows mem.globals layouts mem.callerLocals
    obtain ⟨hb, hbnone⟩ :=
      evalOperand_frag decls locals hslots hn rhsIt b hokb mem.borrows mem.globals layouts mem.callerLocals
    cases hxa : opBits locals a with
    | none =>
      refine ⟨fun r hr => by simp [rvBits, hiop, hrhsTy, hxa] at hr, fun _ => ?_⟩
      simp [evalRvalue, hanone hxa]
    | some x =>
      cases hyb : opBits locals b with
      | none =>
        refine ⟨fun r hr => by simp [rvBits, hiop, hrhsTy, hxa, hyb] at hr, fun _ => ?_⟩
        simp [evalRvalue, ha x hxa, hbnone hyb]
      | some y =>
        have hx := opBits_lt decls locals hslots it a hoka x hxa
        have hy := opBits_lt decls locals hslots rhsIt b hokb y hyb
        have hsigned := operandIsSigned_of_operandOk decls layouts it a hoka
        obtain ⟨hbinOk, hbinNone⟩ :=
          evalScalarBinOp_frag op iop hiop it rhsIt hgood hrhsGood hhom x y hx hy locals mem
        cases hz : intBinEval iop (intFromBits x it) (intFromBits y rhsIt) it with
        | none =>
          refine ⟨fun r hr => by simp [rvBits, hiop, hrhsTy, hxa, hyb, hz] at hr, fun _ => ?_⟩
          simp [evalRvalue, ha x hxa, hb y hyb, hsigned, hbinNone hz]
        | some z =>
          refine ⟨fun r hr => ?_, fun h => by simp [rvBits, hiop, hrhsTy, hxa, hyb, hz] at h⟩
          simp [rvBits, hiop, hrhsTy, hxa, hyb, hz] at hr
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

/-! ## Comparisons, `!` on `bool`, and `bool` rvalues -/

theorem signedLt_eq (x y sz : Nat) (hsz : sz ≠ 0) (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    MirSemantics.signedLt x y sz =
      decide (intFromBits x ⟨.Signed, ⟨sz⟩⟩ < intFromBits y ⟨.Signed, ⟨sz⟩⟩) := by
  obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
  have hp : ((2 : Int) ^ (8 * sz)) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
  simp only [MirSemantics.signedLt, scalarModulus_eq, wrapScalarBits_eq, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy, isSignedNegative_eq x sz hsz hx, isSignedNegative_eq y sz hsz hy,
    nat_ble_eq_decide, intFromBits]
  rw [hp]
  generalize 2 ^ (8 * sz - 1) = H at hM hH ⊢
  generalize 2 ^ (8 * sz) = M at hM hx hy ⊢
  apply Bool.eq_iff_iff.mpr
  by_cases hxH : H ≤ x <;> by_cases hyH : H ≤ y <;>
    simp [hxH, hyH, show x < H ↔ ¬(H ≤ x) by omega, show y < H ↔ ¬(H ≤ y) by omega] <;> omega

theorem signedLe_eq (x y sz : Nat) (hsz : sz ≠ 0) (hx : x < 2 ^ (8 * sz)) (hy : y < 2 ^ (8 * sz)) :
    MirSemantics.signedLe x y sz =
      decide (intFromBits x ⟨.Signed, ⟨sz⟩⟩ ≤ intFromBits y ⟨.Signed, ⟨sz⟩⟩) := by
  simp only [MirSemantics.signedLe, signedLt_eq y x sz hsz hy hx]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  omega

theorem relBool_intCmp_lt (a b : Int) : relBool .Lt (intCmp a b) = decide (a < b) := by
  unfold intCmp; by_cases h1 : a < b <;> by_cases h2 : a = b <;> simp [h1, h2, relBool]
theorem relBool_intCmp_gt (a b : Int) : relBool .Gt (intCmp a b) = decide (b < a) := by
  unfold intCmp; by_cases h1 : a < b <;> by_cases h2 : a = b <;> simp [h1, h2, relBool] <;> omega
theorem relBool_intCmp_le (a b : Int) : relBool .Le (intCmp a b) = decide (a ≤ b) := by
  unfold intCmp; by_cases h1 : a < b <;> by_cases h2 : a = b <;> simp [h1, h2, relBool] <;> omega
theorem relBool_intCmp_ge (a b : Int) : relBool .Ge (intCmp a b) = decide (b ≤ a) := by
  unfold intCmp; by_cases h1 : a < b <;> by_cases h2 : a = b <;> simp [h1, h2, relBool] <;> omega
theorem relBool_intCmp_eq (a b : Int) : relBool .Eq (intCmp a b) = decide (a = b) := by
  unfold intCmp; by_cases h1 : a < b <;> by_cases h2 : a = b <;> simp [h1, h2, relBool] <;> omega
theorem relBool_intCmp_ne (a b : Int) : relBool .Ne (intCmp a b) = decide (a ≠ b) := by
  unfold intCmp; by_cases h1 : a < b <;> by_cases h2 : a = b <;> simp [h1, h2, relBool] <;> omega

theorem intFromBits_unsigned (sz x : Nat) : intFromBits x ⟨.Unsigned, ⟨sz⟩⟩ = (x : Int) := rfl

theorem decide_intFromBits_eq (it : Gen.IntType) (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes))
    (hy : y < 2 ^ (8 * it.size.bytes)) :
    decide (intFromBits x it = intFromBits y it) = Nat.beq x y := by
  rw [nat_beq_eq_decide]
  exact decide_eq_decide.mpr (intFromBits_inj it x y hx hy)

/-- Anneal's comparison of two integers of one fragment type agrees with
MiniRust's `BinOp::Rel` on the decoded values (`cmpOf`), for both signed and
unsigned types. -/
theorem evalScalarBinOp_rel_int (op : MirAst.BinOp) (rel : Gen.RelOp)
    (hrel : translateRelOp op = some rel) (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    evalScalarBinOp op ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ locals mem
        (match it.signed with | .Unsigned => false | .Signed => true) =
      .ok (.scalar (boolToScalar (relBool rel (cmpOf (.Int it) x y)))) locals mem := by
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hbeq : Nat.beq it.size.bytes 0 = false := by rw [nat_beq_eq_decide, decide_eq_false hsz]
  have heq := decide_intFromBits_eq it x y hx hy
  rcases it with ⟨signed, ⟨sz⟩⟩
  dsimp only at hsz hbeq hx hy heq ⊢
  cases op <;> simp [translateRelOp] at hrel <;> subst hrel <;>
    cases signed <;>
    simp only [evalScalarBinOp, hbeq, Nat.beq_refl, cmpOf, relBool_intCmp_lt, relBool_intCmp_gt,
      relBool_intCmp_le, relBool_intCmp_ge, relBool_intCmp_eq, relBool_intCmp_ne, heq,
      intFromBits_unsigned, signedLt_eq _ _ sz hsz hx hy, signedLt_eq _ _ sz hsz hy hx,
      signedLe_eq _ _ sz hsz hx hy, signedLe_eq _ _ sz hsz hy hx, nat_ble_eq_decide,
      nat_beq_eq_decide, decide_not] <;>
    (congr 3; apply Bool.eq_iff_iff.mpr; simp only [Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq]; omega)

/-- Anneal's comparison of two `bool`s (one byte each, `0` or `1`, compared
unsigned) agrees with MiniRust's `false < true`. -/
theorem evalScalarBinOp_rel_bool (op : MirAst.BinOp) (rel : Gen.RelOp)
    (hrel : translateRelOp op = some rel) (x y : Nat) (hx : x < 2) (hy : y < 2)
    (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    evalScalarBinOp op ⟨x, u8Ty.size.bytes⟩ ⟨y, u8Ty.size.bytes⟩ locals mem false =
      .ok (.scalar (boolToScalar (relBool rel (cmpOf .Bool x y)))) locals mem := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;>
    cases op <;> simp [translateRelOp] at hrel <;> subst hrel <;> rfl

/-- The signedness Anneal uses for a fragment operand of type `T`. -/
def signedOf : Gen.Type → Bool
  | .Int it => match it.signed with | .Unsigned => false | .Signed => true
  | _ => false

theorem operandIsSigned_of_OperandOkT (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    {T : Gen.Type} (op : Operand) (hok : OperandOkT decls T op) :
    MirSemantics.operandIsSigned decls op layouts = signedOf T := by
  have hty : ∃ ty, MirSemantics.operandTy decls layouts op = some ty ∧ scalarTypeOf ty = some T := by
    match op, hok with
    | .copy ⟨j, []⟩, hok =>
      obtain ⟨hj, hty⟩ := hok
      obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
      simp only [operandType, hd, Option.bind_some] at hty
      exact ⟨d.ty, by simp [MirSemantics.operandTy, MirSemantics.placeTy, get?, hd,
        MirSemantics.resolveProjectedTy], hty⟩
    | .constant c, hok => exact ⟨c.ty, rfl, hok.1⟩
  obtain ⟨ty, hty, hT⟩ := hty
  simp only [MirSemantics.operandIsSigned, hty, MirSemantics.tyIsSigned]
  rcases scalarTypeOf_cases hT with ⟨hb, rfl⟩ | ⟨it, hit, rfl⟩
  · unfold isBoolTy at hb
    split at hb <;> simp_all [signedOf]
  · rcases intTypeOf_kind hit with ⟨⟨u, hu⟩, hs⟩ | ⟨⟨i, hi⟩, hs⟩
    · simp [hu, hs, signedOf]
    · simp [hi, hs, signedOf]

theorem operandTy_of_OperandOkT (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    {T : Gen.Type} (op : Operand) (hok : OperandOkT decls T op) :
    ∃ ty, MirSemantics.operandTy decls layouts op = some ty ∧ scalarTypeOf ty = some T := by
  match op, hok with
  | .copy ⟨j, []⟩, hok =>
    obtain ⟨hj, hty⟩ := hok
    obtain ⟨d, hd⟩ : ∃ d, decls[j]? = some d := ⟨decls[j], by simp [hj]⟩
    simp only [operandType, hd, Option.bind_some] at hty
    exact ⟨d.ty, by simp [MirSemantics.operandTy, MirSemantics.placeTy, get?, hd,
      MirSemantics.resolveProjectedTy], hty⟩
  | .constant c, hok => exact ⟨c.ty, rfl, hok.1⟩

/-- Anneal's `!` on a `bool` operand (`0` or `1`) is `1 - x`. -/
theorem evalUnaryNot_bool (decls : List LocalDecl) (layouts : Layout.LayoutTable) (op : Operand)
    (hok : OperandOkT decls .Bool op) (x : Nat) (hx : x < 2) (locals : List LocalSlot)
    (mem : MirSemantics.Memory) :
    MirSemantics.evalUnaryNot ⟨x, u8Ty.size.bytes⟩ (MirSemantics.operandTy decls layouts op) locals mem =
      .ok (.scalar ⟨1 - x, u8Ty.size.bytes⟩) locals mem := by
  obtain ⟨ty, hty, hT⟩ := operandTy_of_OperandOkT decls layouts op hok
  have hkind : ty.kind = .bool := by
    rcases scalarTypeOf_cases hT with ⟨hb, _⟩ | ⟨it, _, h⟩
    · unfold isBoolTy at hb; split at hb <;> simp_all
    · cases h
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    simp [MirSemantics.evalUnaryNot, hty, hkind, u8Ty]

/-- Evaluating a fragment rvalue of type `bool` in Anneal's semantics. -/
theorem evalRvalue_fragB (decls : List LocalDecl) (locals : List LocalSlot)
    (hslots : SlotsOk decls locals) (hn : locals.length = decls.length)
    (rv : Rvalue) (hok : rvalueOkB decls rv = true)
    (mem : MirSemantics.Memory) (layouts : Layout.LayoutTable) :
    (∀ r, rvBitsB decls locals rv = some r →
      evalRvalue locals rv mem decls layouts = .ok (.scalar ⟨r, u8Ty.size.bytes⟩) locals mem) ∧
    (rvBitsB decls locals rv = none → evalRvalue locals rv mem decls layouts = .ub) := by
  match rv, hok with
  | .use op, hok =>
    simp only [rvalueOkB] at hok
    obtain ⟨hsome, hnone⟩ := evalOperand_fragT decls locals hslots hn .bool op (operandOkB_T hok)
      mem.borrows mem.globals layouts mem.callerLocals
    refine ⟨fun r hr => ?_, fun h => ?_⟩
    · simp [evalRvalue, hsome r hr]
    · simp [evalRvalue, hnone h]
  | .unaryOp .not op, hok =>
    simp only [rvalueOkB] at hok
    have hokT := operandOkB_T hok
    obtain ⟨hsome, hnone⟩ := evalOperand_fragT decls locals hslots hn .bool op hokT
      mem.borrows mem.globals layouts mem.callerLocals
    cases hxo : opBits locals op with
    | none =>
      refine ⟨fun r hr => by simp [rvBitsB, hxo] at hr, fun _ => ?_⟩
      simp [evalRvalue, hnone hxo]
    | some x =>
      have hx : x < 2 := by simpa [ValidBits] using opBits_valid decls locals hslots .bool op hokT x hxo
      refine ⟨fun r hr => ?_, fun h => by simp [rvBitsB, hxo] at h⟩
      simp [rvBitsB, hxo] at hr
      subst hr
      simp only [evalRvalue, hsome x hxo, evalUnaryNot_bool decls layouts op hokT x hx]
  | .unaryOp .neg _, hok => simp [rvalueOkB] at hok
  | .unaryOp .ptrMetadata _, hok => simp [rvalueOkB] at hok
  | .binaryOp op a b, hok =>
    simp only [rvalueOkB, Bool.and_eq_true] at hok
    obtain ⟨hrelSome, hops⟩ := hok
    obtain ⟨rel, hrel⟩ := Option.isSome_iff_exists.mp hrelSome
    obtain ⟨T, it, hT, htyA, hokA, hokB⟩ := relOperandsOk_spec hops
    obtain ⟨ha, hanone⟩ := evalOperand_fragT decls locals hslots hn hT a hokA
      mem.borrows mem.globals layouts mem.callerLocals
    obtain ⟨hb, hbnone⟩ := evalOperand_fragT decls locals hslots hn hT b hokB
      mem.borrows mem.globals layouts mem.callerLocals
    have hsigned := operandIsSigned_of_OperandOkT decls layouts a hokA
    cases hxa : opBits locals a with
    | none =>
      refine ⟨fun r hr => by simp [rvBitsB, hrel, htyA, hxa] at hr, fun _ => ?_⟩
      simp [evalRvalue, hanone hxa]
    | some x =>
      cases hyb : opBits locals b with
      | none =>
        refine ⟨fun r hr => by simp [rvBitsB, hrel, htyA, hxa, hyb] at hr, fun _ => ?_⟩
        simp [evalRvalue, ha x hxa, hbnone hyb]
      | some y =>
        have hx := opBits_valid decls locals hslots hT a hokA x hxa
        have hy := opBits_valid decls locals hslots hT b hokB y hyb
        refine ⟨fun r hr => ?_, fun h => by simp [rvBitsB, hrel, htyA, hxa, hyb] at h⟩
        simp [rvBitsB, hrel, htyA, hxa, hyb] at hr
        subst hr
        have hres : evalScalarBinOp op ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ locals mem (signedOf T) =
            .ok (.scalar (boolToScalar (relBool rel (cmpOf T x y)))) locals mem := by
          cases hT with
          | int it hgood => exact evalScalarBinOp_rel_int op rel hrel it hgood x y hx hy locals mem
          | bool =>
            exact evalScalarBinOp_rel_bool op rel hrel x y (by simpa [ValidBits] using hx)
              (by simpa [ValidBits] using hy) locals mem
        simp only [evalRvalue, ha x hxa, hb y hyb, hsigned, hres]
        cases relBool rel (cmpOf T x y) <;> rfl
  | .cast _ _ _, hok => simp [rvalueOkB] at hok
  | .copyForDeref _, hok => simp [rvalueOkB] at hok
  | .repeat _ _, hok => simp [rvalueOkB] at hok
  | .ref _ _, hok => simp [rvalueOkB] at hok
  | .rawPtr _ _, hok => simp [rvalueOkB] at hok
  | .len _, hok => simp [rvalueOkB] at hok
  | .discriminant _, hok => simp [rvalueOkB] at hok
  | .aggregate _ _, hok => simp [rvalueOkB] at hok
  | .threadLocalRef _, hok => simp [rvalueOkB] at hok
  | .nullaryOp _ _, hok => simp [rvalueOkB] at hok
  | .shallowInitBox _ _, hok => simp [rvalueOkB] at hok
  | .wrapUnsafeBinder _ _, hok => simp [rvalueOkB] at hok

/-! ## Statements -/

/-- Anneal's assignment to a live local `_i` from an rvalue that evaluates to
a scalar (or to UB). -/
theorem evalStmt_assign_of (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (rv : Rvalue) (span : String) (hslots : SlotsOk decls s.frame.locals)
    (hn : s.frame.locals.length = decls.length) (d : LocalDecl) (hd : decls[i]? = some d)
    (hbor : s.memory.borrows = []) (hprot : s.memory.activeProtectors = []) :
    (∀ sc, evalRvalue s.frame.locals rv s.memory decls layouts = .ok (.scalar sc) s.frame.locals s.memory →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.scalar sc)))
          { s.memory with borrows := [] }))) ∧
    (evalRvalue s.frame.locals rv s.memory decls layouts = .ub →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hi : i < s.frame.locals.length := by rw [hn]; exact (List.getElem?_eq_some_iff.mp hd).1
  have hs : s.frame.locals[i]? = some s.frame.locals[i] := by simp [hi]
  have hslot := hslots i d _ hd hs
  have hlive : s.frame.locals[i] ≠ .dead := by
    intro h; rw [h] at hslot; exact hslot
  refine ⟨fun sc hsc => ?_, fun h => ?_⟩
  · simp only [evalStmt, hsc, get?, hs, set?, hi, hprot, hbor, invalidateConflictingBorrows_nil]
    cases hsl : s.frame.locals[i] with
    | dead => exact absurd hsl hlive
    | uninit => simp [MirStepNode.step]
    | init v => simp [MirStepNode.step]
  · simp [evalStmt, h]

theorem evalStmt_assign (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (rv : Rvalue) (span : String) (hslots : SlotsOk decls s.frame.locals)
    (hn : s.frame.locals.length = decls.length) (d : LocalDecl) (hd : decls[i]? = some d)
    (hgood : GoodSize (itOf d).size.bytes) (hok : rvalueOk decls (itOf d) rv = true)
    (hbor : s.memory.borrows = []) (hprot : s.memory.activeProtectors = []) :
    (∀ r, rvBits decls s.frame.locals (itOf d) rv = some r →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.scalar ⟨r, (itOf d).size.bytes⟩)))
          { s.memory with borrows := [] }))) ∧
    (rvBits decls s.frame.locals (itOf d) rv = none →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  obtain ⟨hok', hnone⟩ := evalRvalue_frag decls s.frame.locals hslots hn (itOf d) hgood rv hok s.memory layouts
  obtain ⟨hA, hAub⟩ := evalStmt_assign_of s decls layouts i rv span hslots hn d hd hbor hprot
  exact ⟨fun r hr => hA _ (hok' r hr), fun h => hAub (hnone h)⟩

theorem evalStmt_assignB (s : MachineState) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (i : Nat) (rv : Rvalue) (span : String) (hslots : SlotsOk decls s.frame.locals)
    (hn : s.frame.locals.length = decls.length) (d : LocalDecl) (hd : decls[i]? = some d)
    (hbool : isBoolTy d.ty = true) (hok : rvalueOkB decls rv = true)
    (hbor : s.memory.borrows = []) (hprot : s.memory.activeProtectors = []) :
    (∀ r, rvBitsB decls s.frame.locals rv = some r →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s (s.frame.locals.set i (.init (.scalar ⟨r, (itOf d).size.bytes⟩)))
          { s.memory with borrows := [] }))) ∧
    (rvBitsB decls s.frame.locals rv = none →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hit : itOf d = u8Ty := (tyOf_bool hbool).2
  obtain ⟨hok', hnone⟩ := evalRvalue_fragB decls s.frame.locals hslots hn rv hok s.memory layouts
  obtain ⟨hA, hAub⟩ := evalStmt_assign_of s decls layouts i rv span hslots hn d hd hbor hprot
  refine ⟨fun r hr => ?_, fun h => hAub (hnone h)⟩
  rw [hit]
  exact hA _ (hok' r hr)

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
