/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Translate

/-!
# Integer and byte-encoding lemmas

Facts relating the two integer representations: Anneal stores a scalar as an
unsigned bit pattern `bits < 2^(8·size)` and computes modulo `2^(8·size)`;
MiniRust stores a mathematical integer in the representable range of its
`IntType` and calls `bring_in_bounds` after each operation. The bridge is
`intFromBits` (MiniRust's own `int_from_bits`, used by `minimize`).
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-! ## Little-endian bytes -/

theorem leBytes_length (u k : Nat) : (leBytes u k).length = k := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

theorem leValue_leBytes (u k : Nat) : leValue (leBytes u k) = u % 256 ^ k := by
  induction k generalizing u with
  | zero => simp [leBytes, leValue, Nat.mod_one]
  | succ k ih =>
    simp only [leBytes, leValue, ih, UInt8.toNat_ofNat']
    have e1 : u % 256 % 2 ^ 8 = u % 256 := Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
    rw [e1, show (256 : Nat) ^ (k + 1) = 256 * 256 ^ k by rw [Nat.pow_succ, Nat.mul_comm],
      Nat.mod_mul]

/-! ## Representatives modulo `2^n` -/

/-- Two integers in a half-open window of width `m` that agree modulo `m` are equal. -/
theorem eq_of_emod_eq_of_window {x y lo m : Int} (hm : 0 < m)
    (hx₁ : lo ≤ x) (hx₂ : x < lo + m) (hy₁ : lo ≤ y) (hy₂ : y < lo + m)
    (h : x % m = y % m) : x = y := by
  have hd : m ∣ x - y := by
    rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, h, Int.sub_self, Int.zero_emod]
  have habs : (x - y).natAbs < m.natAbs := by omega
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd habs
  omega

theorem two_pow_pos (n : Nat) : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)

/-- The window of `IntType`: `[0, 2^n)` unsigned, `[-2^(n-1), 2^(n-1))` signed. -/
def windowLo (signed : Signedness) (n : Nat) : Int :=
  match signed with
  | .Unsigned => 0
  | .Signed => -(2 : Int) ^ (n - 1)

theorem two_pow_pred_add (n : Nat) (hn : 0 < n) :
    (2 : Int) ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [Int.pow_succ]
  omega

theorem inBounds_iff (i : Int) (signed : Signedness) (size : Size) (hn : 0 < Size.bits size) :
    inBounds i signed size = true ↔
      windowLo signed (Size.bits size) ≤ i ∧ i < windowLo signed (Size.bits size) + 2 ^ Size.bits size := by
  cases signed with
  | Unsigned => simp [inBounds, windowLo]
  | Signed =>
    have := two_pow_pred_add (Size.bits size) hn
    simp [inBounds, windowLo]
    omega

theorem intFromBits_window (bits : Nat) (it : Gen.IntType) (hn : 0 < 8 * it.size.bytes)
    (hb : bits < 2 ^ (8 * it.size.bytes)) :
    windowLo it.signed (8 * it.size.bytes) ≤ intFromBits bits it ∧
      intFromBits bits it < windowLo it.signed (8 * it.size.bytes) + 2 ^ (8 * it.size.bytes) := by
  have hb' : (bits : Int) < 2 ^ (8 * it.size.bytes) := by exact_mod_cast hb
  cases h : it.signed with
  | Unsigned => simp [intFromBits, windowLo, h]; omega
  | Signed =>
    have := two_pow_pred_add (8 * it.size.bytes) hn
    simp only [intFromBits, windowLo, h]
    split
    · next hlt =>
      have : (bits : Int) < 2 ^ (8 * it.size.bytes - 1) := by exact_mod_cast hlt
      omega
    · next hge =>
      have : (2 : Int) ^ (8 * it.size.bytes - 1) ≤ bits := by
        have := Nat.le_of_not_lt hge; exact_mod_cast this
      omega

theorem intFromBits_emod (bits : Nat) (it : Gen.IntType) (hb : bits < 2 ^ (8 * it.size.bytes)) :
    intFromBits bits it % 2 ^ (8 * it.size.bytes) = bits := by
  have hb' : (bits : Int) < 2 ^ (8 * it.size.bytes) := by exact_mod_cast hb
  have hpos := two_pow_pos (8 * it.size.bytes)
  cases h : it.signed with
  | Unsigned => simp [intFromBits, h]; exact Int.emod_eq_of_lt (by omega) hb'
  | Signed =>
    simp only [intFromBits, h]
    split
    · exact Int.emod_eq_of_lt (by omega) hb'
    · rw [Int.sub_emod, Int.emod_self, Int.sub_zero, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
      exact Int.emod_eq_of_lt (by omega) hb'

theorem bringInBounds_emod (x : Int) (signed : Signedness) (size : Size) :
    bringInBounds x signed size % 2 ^ Size.bits size = x % 2 ^ Size.bits size := by
  have hpos := two_pow_pos (Size.bits size)
  cases signed with
  | Unsigned => simp [bringInBounds, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
  | Signed =>
    simp only [bringInBounds]
    split
    · simp [Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
    · simp [Int.emod_emod_of_dvd _ (Int.dvd_refl _)]

theorem bringInBounds_window (x : Int) (signed : Signedness) (size : Size) (hn : 0 < Size.bits size) :
    windowLo signed (Size.bits size) ≤ bringInBounds x signed size ∧
      bringInBounds x signed size < windowLo signed (Size.bits size) + 2 ^ Size.bits size := by
  have hpos := two_pow_pos (Size.bits size)
  have h0 := Int.emod_nonneg x (Int.ne_of_gt hpos)
  have h1 := Int.emod_lt_of_pos x hpos
  cases signed with
  | Unsigned => simp [bringInBounds, windowLo]; omega
  | Signed =>
    have := two_pow_pred_add (Size.bits size) hn
    simp only [bringInBounds, windowLo]
    split <;> omega

/-- The key bridge: an in-window integer is `intFromBits` of its residue. -/
theorem eq_intFromBits (v : Int) (it : Gen.IntType) (hn : 0 < 8 * it.size.bytes)
    (hw₁ : windowLo it.signed (8 * it.size.bytes) ≤ v)
    (hw₂ : v < windowLo it.signed (8 * it.size.bytes) + 2 ^ (8 * it.size.bytes)) :
    v = intFromBits (v % 2 ^ (8 * it.size.bytes)).toNat it := by
  have hpos := two_pow_pos (8 * it.size.bytes)
  have h0 := Int.emod_nonneg v (Int.ne_of_gt hpos)
  have h1 := Int.emod_lt_of_pos v hpos
  have hb : (v % 2 ^ (8 * it.size.bytes)).toNat < 2 ^ (8 * it.size.bytes) := by
    have : ((v % 2 ^ (8 * it.size.bytes)).toNat : Int) < 2 ^ (8 * it.size.bytes) := by
      rw [Int.toNat_of_nonneg h0]; exact h1
    exact_mod_cast this
  obtain ⟨hl, hr⟩ := intFromBits_window _ it hn hb
  apply eq_of_emod_eq_of_window hpos hw₁ hw₂ hl hr
  rw [intFromBits_emod _ it hb, Int.toNat_of_nonneg h0]

/-! ## Anneal's modular arithmetic -/

theorem scalarModulus_eq (sz : Nat) : MirSemantics.scalarModulus sz = 2 ^ (8 * sz) := by
  induction sz with
  | zero => rfl
  | succ k ih =>
    show 256 * MirSemantics.scalarModulus k = 2 ^ (8 * (k + 1))
    rw [ih, show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mul_comm]

theorem wrapScalarBits_eq (v m : Nat) : MirSemantics.wrapScalarBits v m = v % m := by
  unfold MirSemantics.wrapScalarBits
  cases h : Nat.ble m v with
  | true => rfl
  | false =>
    have : ¬ m ≤ v := by rw [← Nat.ble_eq]; simp [h]
    show v = v % m
    exact (Nat.mod_eq_of_lt (by omega)).symm

end MiniRustSpec.Correspondence
