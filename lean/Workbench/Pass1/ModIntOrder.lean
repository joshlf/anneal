-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.SimpLemmas
import Init.Tactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Fin.Basic
import Init.Data.BitVec.BasicAux
import Init.Data.UInt.BasicAux
import Init.Data.Int.Basic
import Init.Data.List.Basic

/-!
# Modular Arithmetic, Constructive `Int` Order, and `BitVec` / `UInt` Lemmas

Pass-1-portable (`prelude` + 51 locked `Init.*` foundation modules only, zero
`._unsafe_rec`, exact `TrustedBoundary` CST syntax, axioms `⊆ [propext]`)
theorems eliminating repeated boilerplate across real-crate proofs (`zerocopy`,
`byteorder`, `ryu`, `bytes`), `MirCorrespondence`, and MIR lowering proofs where
`Init.Data.Int.Order`, `Init.Data.Nat.ModLemmas`, `Init.Data.BitVec.Lemmas`, and
`Init.Data.UInt.Lemmas` are outside `foundation-lock.json`:

1. `Nat` power-of-two monotonicity (`nat_two_pow_lt_succ`,
   `nat_two_pow_lt_of_lt`, `nat_two_pow_le_of_le`) and modular arithmetic
   identities (`nat_mod_lt`, `nat_add_mul_div_left`,
   `nat_mul_add_mod_self_left`, `nat_add_mul_mod_self_left`, `nat_add_mod_mod`,
   `nat_mod_add_mod`, `nat_mod_mod_mul_left`, `nat_mod_sq_sub_succ`).
2. Constructive `Int` order and `Int.ofNat` subtraction over `Init.Data.Int.Basic`
   (`int_sub_ofNat_ofNat`, `int_ofNat_le_iff`, `int_ofNat_lt_iff`,
   `int_le_refl`, `int_le_trans`, `int_lt_of_lt_of_le`, `int_lt_of_le_of_lt`,
   `int_le_antisymm`, `int_not_lt_of_ge`, `int_not_le_of_gt`, `int_ofNat_sub`,
   `int_sub_ofNat_neg_swap`).
3. `BitVec` `toNat`/`ofNat`, non-wrapping `+`/`-`, and `<`/`≤` bridges over
   `Init.Data.BitVec.BasicAux` (`bv_eq_of_toNat_eq`, `bv_toNat_lt`,
   `bv_toNat_ofNat`, `bv_toNat_ofNat_of_lt`, `bv_toNat_add`,
   `bv_toNat_add_of_lt`, `bv_add_ofNat_of_lt`, `bv_not_add_lt_left_of_lt`,
   `bv_toNat_sub_of_le`).
4. Fixed-width `UInt8`/`UInt16`/`UInt32`/`UInt64` extensionality and bounded
   `ofNat`/`toNat` lemmas over `Init.Data.UInt.BasicAux` (`u8_eq_of_toNat_eq` ..
   `u64_eq_of_toNat_eq`, `u8_toNat_ofNat_of_lt` .. `u64_toNat_ofNat_of_lt`,
   `u64_ofNat_ne_zero`).
5. Polymorphic `List.beq` equality reflection (`list_beq_refl`,
   `list_eq_of_beq`, `list_beq_iff` for `[BEq α] [LawfulBEq α]`).
-/

namespace Workbench.Pass1.ModIntOrder

/-! ## 1. `Nat` Power-of-Two Monotonicity and Modular Arithmetic -/

theorem nat_two_pow_lt_succ (n : Nat) : Nat.pow 2 n < Nat.pow 2 (n + 1) := by
  have hSucc : Nat.pow 2 (n + 1) = Nat.pow 2 n * 2 := Nat.pow_succ 2 n
  rw [hSucc, Nat.mul_two]
  exact Nat.lt_add_of_pos_right (Nat.two_pow_pos n)

theorem nat_two_pow_lt_of_lt {i j : Nat} (h : i < j) :
    Nat.pow 2 i < Nat.pow 2 j :=
  Nat.lt_of_lt_of_le (nat_two_pow_lt_succ i)
    (Nat.pow_le_pow_right (by decide : 0 < 2) h)

theorem nat_two_pow_le_of_le {i j : Nat} (h : i ≤ j) :
    Nat.pow 2 i ≤ Nat.pow 2 j :=
  Nat.pow_le_pow_right (by decide : 0 < 2) h

theorem nat_mod_lt (a : Nat) {b : Nat} (hb : 0 < b) : Nat.mod a b < b :=
  Nat.mod_lt a hb

theorem nat_add_mul_div_left (x z : Nat) {y : Nat} (hy : 0 < y) :
    Nat.div (x + y * z) y = Nat.div x y + z :=
  Nat.add_mul_div_left x z hy

theorem nat_mul_add_mod_self_left (a b c : Nat) :
    Nat.mod (a * b + c) a = Nat.mod c a :=
  Nat.mul_add_mod_self_left a b c

theorem nat_add_mul_mod_self_left (x y z : Nat) :
    Nat.mod (x + y * z) y = Nat.mod x y :=
  Nat.add_mul_mod_self_left x y z

theorem nat_add_mod_left (x z : Nat) :
    Nat.mod (x + z) x = Nat.mod z x :=
  Nat.add_mod_left x z

theorem nat_mul_mod_right (m n : Nat) :
    Nat.mod (m * n) m = 0 :=
  Nat.mul_mod_right m n

theorem nat_add_mod_mod (a b m : Nat) :
    Nat.mod (a + Nat.mod b m) m = Nat.mod (a + b) m := by
  have hDiv : Nat.mod b m + m * Nat.div b m = b := by
    rw [Nat.add_comm]
    exact Nat.div_add_mod b m
  have hStep :
      Nat.mod (a + Nat.mod b m) m =
        Nat.mod (a + Nat.mod b m + m * Nat.div b m) m :=
    Eq.symm (nat_add_mul_mod_self_left (a + Nat.mod b m) m (Nat.div b m))
  rw [Nat.add_assoc a (Nat.mod b m) (m * Nat.div b m), hDiv] at hStep
  exact hStep

theorem nat_mod_add_mod (a b m : Nat) :
    Nat.mod (Nat.mod a m + b) m = Nat.mod (a + b) m := by
  rw [Nat.add_comm (Nat.mod a m) b, nat_add_mod_mod, Nat.add_comm b a]

theorem nat_mod_mod_mul_left (n a b : Nat) :
    Nat.mod (Nat.mod n (a * b)) a = Nat.mod n a := by
  have hDiv : Nat.mod n (a * b) + a * (b * Nat.div n (a * b)) = n := by
    rw [← Nat.mul_assoc]
    exact Nat.mod_add_div n (a * b)
  exact (Nat.add_mul_mod_self_left (Nat.mod n (a * b)) a
    (b * Nat.div n (a * b))).symm.trans (congrArg (fun k => Nat.mod k a) hDiv)

theorem nat_mod_sq_sub_succ (p k : Nat) (hk : k < p) :
    Nat.mod (p * p - (k + 1)) p = p - (k + 1) := by
  have hPos : 0 < p := Nat.lt_of_lt_of_le (Nat.zero_lt_succ k) hk
  have hFactor : p * p = p * (p - 1) + p := by
    have hMul : p = (p - 1) + 1 := Eq.symm (Nat.sub_add_cancel hPos)
    have hDist : p * ((p - 1) + 1) = p * (p - 1) + p := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [← hMul] at hDist
    exact hDist
  rw [hFactor, Nat.add_sub_assoc hk, Nat.add_comm (p * (p - 1)) (p - (k + 1)),
      nat_add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (Nat.sub_lt hPos (Nat.zero_lt_succ k))

/-! ## 2. Constructive `Int` Order and Subtraction (`Init.Data.Int.Basic`) -/

theorem int_sub_ofNat_ofNat (b a : Nat) :
    Int.ofNat b - Int.ofNat a = Int.subNatNat b a := by
  cases a with
  | zero =>
    unfold Int.subNatNat
    rw [Nat.zero_sub]
    change Int.ofNat (b + 0) = Int.ofNat (b - 0)
    rw [Nat.add_zero, Nat.sub_zero]
  | succ _ => rfl

theorem int_sub_negSucc_ofNat_not_nonNeg (b a : Nat) :
    ¬ Int.NonNeg (Int.negSucc b - Int.ofNat a) := by
  cases a with
  | zero => intro h; cases h
  | succ _ => intro h; cases h

theorem nonNeg_subNatNat_le {a b : Nat}
    (h : Int.NonNeg (Int.subNatNat a b)) : b ≤ a := by
  unfold Int.subNatNat at h
  cases hsub : b - a with
  | zero => exact Nat.le_of_sub_eq_zero hsub
  | succ _ =>
    rw [hsub] at h
    cases h

theorem le_nonNeg_subNatNat {a b : Nat} (h : b ≤ a) :
    Int.NonNeg (Int.subNatNat a b) := by
  unfold Int.subNatNat
  rw [Nat.sub_eq_zero_of_le h]
  exact Int.NonNeg.mk (a - b)

theorem int_ofNat_zero_le (n : Nat) : (0 : Int) ≤ Int.ofNat n := by
  change Int.NonNeg (Int.ofNat n - Int.ofNat 0)
  rw [int_sub_ofNat_ofNat]
  exact le_nonNeg_subNatNat (Nat.zero_le n)

theorem int_ofNat_le_of_le {a b : Nat} (h : a ≤ b) :
    Int.ofNat a ≤ Int.ofNat b := by
  change Int.NonNeg (Int.ofNat b - Int.ofNat a)
  rw [int_sub_ofNat_ofNat]
  exact le_nonNeg_subNatNat h

theorem le_of_int_ofNat_le {a b : Nat} (h : Int.ofNat a ≤ Int.ofNat b) :
    a ≤ b := by
  have hSub : Int.NonNeg (Int.ofNat b - Int.ofNat a) := h
  rw [int_sub_ofNat_ofNat] at hSub
  exact nonNeg_subNatNat_le hSub

theorem int_ofNat_le_iff {a b : Nat} :
    (Int.ofNat a ≤ Int.ofNat b) ↔ a ≤ b :=
  ⟨le_of_int_ofNat_le, int_ofNat_le_of_le⟩

theorem int_ofNat_lt_iff {a b : Nat} :
    (Int.ofNat a < Int.ofNat b) ↔ a < b := by
  change (Int.ofNat (a + 1) ≤ Int.ofNat b) ↔ a + 1 ≤ b
  exact int_ofNat_le_iff

theorem int_negSucc_le_ofNat (a b : Nat) : Int.negSucc a ≤ Int.ofNat b :=
  Int.NonNeg.mk (b + (a + 1))

theorem int_negSucc_le_negSucc_iff {a b : Nat} :
    (Int.negSucc a ≤ Int.negSucc b) ↔ b + 1 ≤ a + 1 := by
  constructor
  · intro h
    exact nonNeg_subNatNat_le h
  · intro h
    exact le_nonNeg_subNatNat h

theorem int_le_refl (a : Int) : a ≤ a := by
  cases a with
  | ofNat x => exact int_ofNat_le_of_le (Nat.le_refl x)
  | negSucc x => exact le_nonNeg_subNatNat (Nat.le_refl (x + 1))

theorem int_le_trans {a b c : Int} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases a with
  | ofNat x =>
    cases b with
    | ofNat y =>
      cases c with
      | ofNat z =>
        exact int_ofNat_le_of_le
          (Nat.le_trans (le_of_int_ofNat_le hab) (le_of_int_ofNat_le hbc))
      | negSucc z =>
        exact False.elim (int_sub_negSucc_ofNat_not_nonNeg z y hbc)
    | negSucc y =>
      exact False.elim (int_sub_negSucc_ofNat_not_nonNeg y x hab)
  | negSucc x =>
    cases b with
    | ofNat y =>
      cases c with
      | ofNat z => exact int_negSucc_le_ofNat x z
      | negSucc z =>
        exact False.elim (int_sub_negSucc_ofNat_not_nonNeg z y hbc)
    | negSucc y =>
      cases c with
      | ofNat z => exact int_negSucc_le_ofNat x z
      | negSucc z =>
        exact le_nonNeg_subNatNat
          (Nat.le_trans (nonNeg_subNatNat_le hbc) (nonNeg_subNatNat_le hab))

theorem int_lt_of_lt_of_le {a b c : Int} (hab : a < b) (hbc : b ≤ c) : a < c :=
  int_le_trans hab hbc

theorem int_add_one_le_add_one {a b : Int} (h : a ≤ b) : a + 1 ≤ b + 1 := by
  cases a with
  | ofNat x =>
    cases b with
    | ofNat y =>
      exact int_ofNat_le_of_le (Nat.succ_le_succ (le_of_int_ofNat_le h))
    | negSucc y =>
      exact False.elim (int_sub_negSucc_ofNat_not_nonNeg y x h)
  | negSucc x =>
    cases b with
    | ofNat y =>
      cases x with
      | zero => exact int_ofNat_le_of_le (Nat.zero_le (y + 1))
      | succ x' => exact int_negSucc_le_ofNat x' (y + 1)
    | negSucc y =>
      have hyx : y + 1 ≤ x + 1 := nonNeg_subNatNat_le h
      cases x with
      | zero =>
        cases y with
        | zero => exact int_ofNat_le_of_le (Nat.le_refl 0)
        | succ y' =>
          exact False.elim (Nat.not_lt_of_le hyx (Nat.succ_lt_succ (Nat.zero_lt_succ y')))
      | succ x' =>
        cases y with
        | zero => exact int_negSucc_le_ofNat x' 0
        | succ y' =>
          exact le_nonNeg_subNatNat (Nat.le_of_succ_le_succ hyx)

theorem int_lt_of_le_of_lt {a b c : Int} (hab : a ≤ b) (hbc : b < c) : a < c :=
  int_le_trans (int_add_one_le_add_one hab) hbc

theorem int_le_antisymm {a b : Int} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases a with
  | ofNat x =>
    cases b with
    | ofNat y =>
      exact congrArg Int.ofNat
        (Nat.le_antisymm (le_of_int_ofNat_le hab) (le_of_int_ofNat_le hba))
    | negSucc y =>
      exact False.elim (int_sub_negSucc_ofNat_not_nonNeg y x hab)
  | negSucc x =>
    cases b with
    | ofNat y =>
      exact False.elim (int_sub_negSucc_ofNat_not_nonNeg x y hba)
    | negSucc y =>
      have hEq : x + 1 = y + 1 :=
        Nat.le_antisymm (nonNeg_subNatNat_le hba) (nonNeg_subNatNat_le hab)
      exact congrArg Int.negSucc (Nat.succ.inj hEq)

theorem int_not_add_one_le (a : Int) (h : a + 1 ≤ a) : False := by
  cases a with
  | ofNat n =>
    exact Nat.not_lt_of_le (le_of_int_ofNat_le h) (Nat.lt_succ_self n)
  | negSucc m =>
    cases m with
    | zero =>
      exact int_sub_negSucc_ofNat_not_nonNeg 0 0 h
    | succ k =>
      exact Nat.not_lt_of_le (nonNeg_subNatNat_le h) (Nat.lt_succ_self (k + 1))

theorem int_not_lt_of_ge {a b : Int} (h : b ≤ a) : ¬ (a < b) :=
  fun hlt => int_not_add_one_le a (int_le_trans hlt h)

theorem int_not_le_of_gt {a b : Int} (h : b < a) : ¬ (a ≤ b) :=
  fun hle => int_not_add_one_le b (int_le_trans h hle)

theorem int_ofNat_sub {a b : Nat} (h : b ≤ a) :
    Int.ofNat a - Int.ofNat b = Int.ofNat (a - b) := by
  rw [int_sub_ofNat_ofNat]
  unfold Int.subNatNat
  rw [Nat.sub_eq_zero_of_le h]

theorem int_sub_ofNat_neg_swap (a b : Nat) :
    Int.ofNat b - Int.ofNat a = Int.neg (Int.ofNat a - Int.ofNat b) := by
  rw [int_sub_ofNat_ofNat b a, int_sub_ofNat_ofNat a b]
  unfold Int.subNatNat
  cases Nat.lt_or_ge a b with
  | inl hab =>
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hab)]
    cases hS : b - a with
    | zero =>
      exact False.elim (Nat.not_lt_of_le (Nat.le_of_sub_eq_zero hS) hab)
    | succ _ => rfl
  | inr hba =>
    rw [Nat.sub_eq_zero_of_le hba]
    cases hS : a - b with
    | zero =>
      have hEq : a = b := Nat.le_antisymm (Nat.le_of_sub_eq_zero hS) hba
      subst hEq
      rfl
    | succ _ => rfl

/-! ## 3. `BitVec` `toNat`, Non-Wrapping `+`/`-`, and Order (`Init.Data.BitVec.BasicAux`) -/

theorem bv_eq_of_toNat_eq {w : Nat} {a b : BitVec w}
    (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofFin fa =>
    cases b with
    | ofFin fb =>
      exact congrArg BitVec.ofFin (Fin.eq_of_val_eq h)

theorem bv_toNat_lt {w : Nat} (x : BitVec w) : x.toNat < Nat.pow 2 w :=
  x.toFin.isLt

theorem bv_toNat_ofNat (w n : Nat) :
    (BitVec.ofNat w n).toNat = Nat.mod n (Nat.pow 2 w) := rfl

theorem bv_toNat_ofNat_of_lt {w n : Nat} (h : n < Nat.pow 2 w) :
    (BitVec.ofNat w n).toNat = n :=
  Nat.mod_eq_of_lt h

theorem bv_toNat_zero (w : Nat) : (0 : BitVec w).toNat = 0 :=
  Nat.mod_eq_of_lt (Nat.two_pow_pos w)

theorem bv_toNat_add {w : Nat} (x y : BitVec w) :
    (x + y).toNat = Nat.mod (x.toNat + y.toNat) (Nat.pow 2 w) := rfl

theorem bv_toNat_add_of_lt {w : Nat} {x y : BitVec w}
    (h : x.toNat + y.toNat < Nat.pow 2 w) :
    (x + y).toNat = x.toNat + y.toNat :=
  Nat.mod_eq_of_lt h

theorem bv_add_ofNat_of_lt {w a b : Nat} (h : a + b < Nat.pow 2 w) :
    BitVec.ofNat w a + BitVec.ofNat w b = BitVec.ofNat w (a + b) := by
  apply bv_eq_of_toNat_eq
  have ha : a < Nat.pow 2 w := Nat.lt_of_le_of_lt (Nat.le_add_right a b) h
  have hb : b < Nat.pow 2 w := Nat.lt_of_le_of_lt (Nat.le_add_left b a) h
  change Nat.mod ((BitVec.ofNat w a).toNat + (BitVec.ofNat w b).toNat) (Nat.pow 2 w) =
    (BitVec.ofNat w (a + b)).toNat
  rw [bv_toNat_ofNat_of_lt ha, bv_toNat_ofNat_of_lt hb, bv_toNat_ofNat_of_lt h]
  exact Nat.mod_eq_of_lt h

theorem bv_lt_iff_toNat_lt {w : Nat} (x y : BitVec w) :
    (x < y) ↔ x.toNat < y.toNat := Iff.rfl

theorem bv_le_iff_toNat_le {w : Nat} (x y : BitVec w) :
    (x ≤ y) ↔ x.toNat ≤ y.toNat := Iff.rfl

theorem bv_not_add_lt_left_of_lt {w : Nat} {x y : BitVec w}
    (h : x.toNat + y.toNat < Nat.pow 2 w) : ¬ (x + y < x) := by
  rw [bv_lt_iff_toNat_lt, bv_toNat_add_of_lt h]
  exact Nat.not_lt_of_ge (Nat.le_add_right x.toNat y.toNat)

theorem bv_toNat_sub_of_le {w : Nat} {x y : BitVec w} (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat := by
  change Nat.mod (Nat.pow 2 w - y.toNat + x.toNat) (Nat.pow 2 w) = x.toNat - y.toNat
  have hyLt : y.toNat < Nat.pow 2 w := bv_toNat_lt y
  have hyLe : y.toNat ≤ Nat.pow 2 w := Nat.le_of_lt hyLt
  have hRearr : Nat.pow 2 w - y.toNat + x.toNat = (x.toNat - y.toNat) + Nat.pow 2 w * 1 := by
    rw [Nat.mul_one, Nat.add_comm (x.toNat - y.toNat) (Nat.pow 2 w)]
    have h1 : (Nat.pow 2 w - y.toNat + x.toNat) + y.toNat =
        (Nat.pow 2 w + (x.toNat - y.toNat)) + y.toNat := by
      rw [Nat.add_assoc (Nat.pow 2 w - y.toNat) x.toNat y.toNat,
          Nat.add_comm x.toNat y.toNat,
          ← Nat.add_assoc (Nat.pow 2 w - y.toNat) y.toNat x.toNat,
          Nat.sub_add_cancel hyLe,
          Nat.add_assoc (Nat.pow 2 w) (x.toNat - y.toNat) y.toNat,
          Nat.sub_add_cancel h]
    exact Nat.add_right_cancel h1
  rw [hRearr, nat_add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le x.toNat y.toNat) (bv_toNat_lt x))

/-! ## 4. Fixed-Width `UInt8` / `UInt16` / `UInt32` / `UInt64` (`Init.Data.UInt.BasicAux`) -/

theorem u8_eq_of_toNat_eq {x y : UInt8} (h : x.toNat = y.toNat) : x = y := by
  cases x with
  | ofBitVec bx =>
    cases y with
    | ofBitVec by_ =>
      exact congrArg UInt8.ofBitVec (bv_eq_of_toNat_eq h)

theorem u16_eq_of_toNat_eq {x y : UInt16} (h : x.toNat = y.toNat) : x = y := by
  cases x with
  | ofBitVec bx =>
    cases y with
    | ofBitVec by_ =>
      exact congrArg UInt16.ofBitVec (bv_eq_of_toNat_eq h)

theorem u32_eq_of_toNat_eq {x y : UInt32} (h : x.toNat = y.toNat) : x = y := by
  cases x with
  | ofBitVec bx =>
    cases y with
    | ofBitVec by_ =>
      exact congrArg UInt32.ofBitVec (bv_eq_of_toNat_eq h)

theorem u64_eq_of_toNat_eq {x y : UInt64} (h : x.toNat = y.toNat) : x = y := by
  cases x with
  | ofBitVec bx =>
    cases y with
    | ofBitVec by_ =>
      exact congrArg UInt64.ofBitVec (bv_eq_of_toNat_eq h)

theorem u8_toNat_lt (x : UInt8) : x.toNat < Nat.pow 2 8 := x.toBitVec.toFin.isLt
theorem u16_toNat_lt (x : UInt16) : x.toNat < Nat.pow 2 16 := x.toBitVec.toFin.isLt
theorem u32_toNat_lt (x : UInt32) : x.toNat < Nat.pow 2 32 := x.toBitVec.toFin.isLt
theorem u64_toNat_lt (x : UInt64) : x.toNat < Nat.pow 2 64 := x.toBitVec.toFin.isLt

theorem u8_toNat_ofNat (n : Nat) : (UInt8.ofNat n).toNat = Nat.mod n (Nat.pow 2 8) := rfl
theorem u16_toNat_ofNat (n : Nat) : (UInt16.ofNat n).toNat = Nat.mod n (Nat.pow 2 16) := rfl
theorem u32_toNat_ofNat (n : Nat) : (UInt32.ofNat n).toNat = Nat.mod n (Nat.pow 2 32) := rfl
theorem u64_toNat_ofNat (n : Nat) : (UInt64.ofNat n).toNat = Nat.mod n (Nat.pow 2 64) := rfl

theorem u8_toNat_ofNat_of_lt {n : Nat} (h : n < Nat.pow 2 8) :
    (UInt8.ofNat n).toNat = n := Nat.mod_eq_of_lt h

theorem u16_toNat_ofNat_of_lt {n : Nat} (h : n < Nat.pow 2 16) :
    (UInt16.ofNat n).toNat = n := Nat.mod_eq_of_lt h

theorem u32_toNat_ofNat_of_lt {n : Nat} (h : n < Nat.pow 2 32) :
    (UInt32.ofNat n).toNat = n := Nat.mod_eq_of_lt h

theorem u64_toNat_ofNat_of_lt {n : Nat} (h : n < Nat.pow 2 64) :
    (UInt64.ofNat n).toNat = n := Nat.mod_eq_of_lt h

theorem u8_ofNat_ne_zero {n : Nat} (hPos : 0 < n) (hLt : n < Nat.pow 2 8) :
    UInt8.ofNat n ≠ 0 := by
  intro hEq
  have h1 : (UInt8.ofNat n).toNat = (0 : UInt8).toNat := congrArg UInt8.toNat hEq
  rw [u8_toNat_ofNat_of_lt hLt] at h1
  change n = 0 at h1
  rw [h1] at hPos
  exact Nat.lt_irrefl 0 hPos

theorem u32_ofNat_ne_zero {n : Nat} (hPos : 0 < n) (hLt : n < Nat.pow 2 32) :
    UInt32.ofNat n ≠ 0 := by
  intro hEq
  have h1 : (UInt32.ofNat n).toNat = (0 : UInt32).toNat := congrArg UInt32.toNat hEq
  rw [u32_toNat_ofNat_of_lt hLt] at h1
  change n = 0 at h1
  rw [h1] at hPos
  exact Nat.lt_irrefl 0 hPos

theorem u64_ofNat_ne_zero {n : Nat} (hPos : 0 < n) (hLt : n < Nat.pow 2 64) :
    UInt64.ofNat n ≠ 0 := by
  intro hEq
  have h1 : (UInt64.ofNat n).toNat = (0 : UInt64).toNat := congrArg UInt64.toNat hEq
  rw [u64_toNat_ofNat_of_lt hLt] at h1
  change n = 0 at h1
  rw [h1] at hPos
  exact Nat.lt_irrefl 0 hPos

/-! ## 5. Polymorphic `List.beq` Equality Reflection (`Init.Data.List.Basic`) -/

private theorem bool_and_left_local {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => cases b <;> nomatch h
  | true => rfl

private theorem bool_and_right_local {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => cases b <;> nomatch h
  | true => exact h

theorem list_beq_refl {α : Type u} [BEq α] [LawfulBEq α] :
    ∀ (xs : List α), List.beq xs xs = true
  | [] => rfl
  | x :: xs => by
    change ((x == x) && List.beq xs xs) = true
    rw [beq_self_eq_true x, list_beq_refl xs]
    rfl

theorem list_eq_of_beq {α : Type u} [BEq α] [LawfulBEq α] :
    ∀ {xs ys : List α}, List.beq xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by nomatch h
  | _ :: _, [], h => by nomatch h
  | x :: xs, y :: ys, h => by
    change ((x == y) && List.beq xs ys) = true at h
    have hx : x = y := eq_of_beq (bool_and_left_local h)
    have hxs : xs = ys := list_eq_of_beq (bool_and_right_local h)
    rw [hx, hxs]

theorem list_beq_iff {α : Type u} [BEq α] [LawfulBEq α] (xs ys : List α) :
    List.beq xs ys = true ↔ xs = ys := by
  constructor
  · intro h
    exact list_eq_of_beq h
  · intro h
    rw [h]
    exact list_beq_refl ys

end Workbench.Pass1.ModIntOrder
