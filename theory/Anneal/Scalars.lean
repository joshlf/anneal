-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted

namespace Anneal.Scalars

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-!
Toolchain-independent fixed-width scalar bounds, two's-complement range
predicates, endian byte-swapping, modular arithmetic lemmas, closed-form
bitwise/shift equivalences, and `BitVec (8 * sz)` homomorphism bridges for
`theory/Anneal/` (`#100`, `#103`, `FF-1.3`).
-/

/-! ## 1. Fixed-Width Moduli, Bounds, and Two's-Complement Range Predicates -/

/-- Modulus $2^8 = 256$ for 8-bit integers (`u8`, `i8`). -/
def U8Modulus : Nat := 256
/-- Maximum unsigned value $2^8 - 1 = 255$ for `u8`. -/
def U8Max : Nat := 255
/-- Sign-bit threshold $2^7 = 128$ for two's-complement `i8`. -/
def I8SignBit : Nat := 128

/-- Modulus $2^{16} = 65536$ for 16-bit integers (`u16`, `i16`). -/
def U16Modulus : Nat := 65536
/-- Maximum unsigned value $2^{16} - 1 = 65535$ for `u16`. -/
def U16Max : Nat := 65535
/-- Sign-bit threshold $2^{15} = 32768$ for two's-complement `i16`. -/
def I16SignBit : Nat := 32768

/-- Modulus $2^{32} = 4294967296$ for 32-bit integers (`u32`, `i32`). -/
def U32Modulus : Nat := 4294967296
/-- Maximum unsigned value $2^{32} - 1 = 4294967295$ for `u32`. -/
def U32Max : Nat := 4294967295
/-- Sign-bit threshold $2^{31} = 2147483648$ for two's-complement `i32`. -/
def I32SignBit : Nat := 2147483648

/-- Modulus $2^{64}$ for 64-bit integers (`u64`, `i64`, `usize`, `isize`). -/
def U64Modulus : Nat := 18446744073709551616
/-- Maximum unsigned value $2^{64} - 1$ for `u64` / `usize`. -/
def U64Max : Nat := 18446744073709551615
/-- Sign-bit threshold $2^{63}$ for two's-complement `i64` / `isize`. -/
def I64SignBit : Nat := 9223372036854775808

/-- Modulus $2^{128}$ for 128-bit integers (`u128`, `i128`). -/
def U128Modulus : Nat := 2 ^ 128
/-- Maximum unsigned value $2^{128} - 1$ for `u128`. -/
def U128Max : Nat := 2 ^ 128 - 1
/-- Sign-bit threshold $2^{127}$ for two's-complement `i128`. -/
def I128SignBit : Nat := 2 ^ 127

/-- Modulus $2^{8 \cdot \text{sizeBytes}}$ for a scalar of width `sizeBytes`. -/
def widthModulus (sizeBytes : Nat) : Nat :=
  2 ^ (sizeBytes * 8)

/-- Sign-bit threshold $2^{8 \cdot \text{sizeBytes} - 1}$ for width `sizeBytes`. -/
def widthSignBit (sizeBytes : Nat) : Nat :=
  2 ^ (sizeBytes * 8 - 1)

/-- Whether `bits` lies in the unsigned range $[0, 2^{8 \cdot \text{sizeBytes}})$. -/
def inUnsignedRange (bits sizeBytes : Nat) : Prop :=
  bits < widthModulus sizeBytes

/-- Whether `bits` is a non-negative two's-complement integer of width `sizeBytes`. -/
def inSignedNonNegRange (bits sizeBytes : Nat) : Prop :=
  bits < widthSignBit sizeBytes

/-- Whether `bits` is a negative two's-complement integer of width `sizeBytes`. -/
def inSignedNegRange (bits sizeBytes : Nat) : Prop :=
  widthSignBit sizeBytes ≤ bits ∧ bits < widthModulus sizeBytes

@[simp] theorem widthModulus_one : widthModulus 1 = U8Modulus := rfl
@[simp] theorem widthModulus_two : widthModulus 2 = U16Modulus := rfl
@[simp] theorem widthModulus_four : widthModulus 4 = U32Modulus := rfl
@[simp] theorem widthModulus_eight : widthModulus 8 = U64Modulus := rfl
@[simp] theorem widthModulus_sixteen : widthModulus 16 = U128Modulus := rfl

@[simp] theorem widthSignBit_one : widthSignBit 1 = I8SignBit := rfl
@[simp] theorem widthSignBit_two : widthSignBit 2 = I16SignBit := rfl
@[simp] theorem widthSignBit_four : widthSignBit 4 = I32SignBit := rfl
@[simp] theorem widthSignBit_eight : widthSignBit 8 = I64SignBit := rfl
@[simp] theorem widthSignBit_sixteen : widthSignBit 16 = I128SignBit := rfl

/--
When `x < bound` and `bound < modulus`, incrementing `x` by `1` does not reach
`modulus`.
-/
theorem add_one_no_overflow_of_lt {x bound modulus : Nat}
    (h_lt : x < bound) (h_bound : Nat.ble modulus bound = false) :
    Nat.ble modulus (x + 1) = false := by
  cases hb : Nat.ble modulus (x + 1)
  · rfl
  · have h1 := Nat.le_of_ble_eq_true hb
    have h2 : ¬ modulus ≤ bound := fun hle => by
      rw [Nat.ble_eq_true_of_le hle] at h_bound; nomatch h_bound
    omega

/-- Swap the low and high bytes of a 16-bit unsigned integer (`u16::swap_bytes`). -/
def swapBytes16 (n : Nat) : Nat :=
  ((n % 256) * 256) + ((n / 256) % 256)

/-- `swapBytes16` is an involution on every 16-bit integer `n < 65536`. -/
theorem swapBytes16_involutive {n : Nat} (hn : n < U16Modulus) :
    swapBytes16 (swapBytes16 n) = n := by
  unfold swapBytes16 U16Modulus at *
  have hhi : (n / 256) % 256 = n / 256 := by omega
  rw [hhi]
  have h1 : (n % 256 * 256 + n / 256) % 256 = n / 256 := by omega
  have h2 : (n % 256 * 256 + n / 256) / 256 = n % 256 := by omega
  rw [h1, h2]
  omega

/-- Reverse the 4 bytes of a 32-bit unsigned integer (`u32::swap_bytes`). -/
def swapBytes32 (n : Nat) : Nat :=
  (n % 256) * 16777216 +
    ((n / 256) % 256) * 65536 +
    ((n / 65536) % 256) * 256 +
    ((n / 16777216) % 256)

theorem swapBytes32_of_bytes {b0 b1 b2 b3 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) :
    swapBytes32 (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) =
      b0 * 16777216 + b1 * 65536 + b2 * 256 + b3 := by
  unfold swapBytes32
  omega

/-- `swapBytes32` is an involution on every 32-bit integer `n < 2^32`. -/
theorem swapBytes32_involutive {n : Nat} (hn : n < U32Modulus) :
    swapBytes32 (swapBytes32 n) = n := by
  unfold U32Modulus at hn
  have h0 : n % 256 < 256 := by omega
  have h1 : (n / 256) % 256 < 256 := by omega
  have h2 : (n / 65536) % 256 < 256 := by omega
  have h3 : (n / 16777216) % 256 < 256 := by omega
  have h_decomp :
      n = (n % 256) + ((n / 256) % 256) * 256 +
        ((n / 65536) % 256) * 65536 + ((n / 16777216) % 256) * 16777216 := by
    omega
  have h_step1 :
      swapBytes32 n =
        (n / 16777216) % 256 + ((n / 65536) % 256) * 256 +
          ((n / 256) % 256) * 65536 + (n % 256) * 16777216 := by
    unfold swapBytes32
    omega
  rw [h_step1, swapBytes32_of_bytes h3 h2 h1 h0]
  omega

/-- Reverse the 8 bytes of a 64-bit unsigned integer (`u64::swap_bytes`). -/
def swapBytes64 (n : Nat) : Nat :=
  (n % 256) * 72057594037927936 +
    ((n / 256) % 256) * 281474976710656 +
    ((n / 65536) % 256) * 1099511627776 +
    ((n / 16777216) % 256) * 4294967296 +
    ((n / 4294967296) % 256) * 16777216 +
    ((n / 1099511627776) % 256) * 65536 +
    ((n / 281474976710656) % 256) * 256 +
    ((n / 72057594037927936) % 256)

theorem swapBytes64_eq_swapBytes32_halves (n : Nat) :
    swapBytes64 n =
      swapBytes32 (n % 4294967296) * 4294967296 +
        swapBytes32 (n / 4294967296) := by
  unfold swapBytes64 swapBytes32
  have hb0 : n % 256 = (n % 4294967296) % 256 := by omega
  have hb1 : (n / 256) % 256 = ((n % 4294967296) / 256) % 256 := by omega
  have hb2 : (n / 65536) % 256 = ((n % 4294967296) / 65536) % 256 := by omega
  have hb3 : (n / 16777216) % 256 = ((n % 4294967296) / 16777216) % 256 := by omega
  have hb5 : n / 1099511627776 = (n / 4294967296) / 256 :=
    (Nat.div_div_eq_div_mul n 4294967296 256).symm
  have hb6 : n / 281474976710656 = (n / 4294967296) / 65536 :=
    (Nat.div_div_eq_div_mul n 4294967296 65536).symm
  have hb7 : n / 72057594037927936 = (n / 4294967296) / 16777216 :=
    (Nat.div_div_eq_div_mul n 4294967296 16777216).symm
  rw [hb0, hb1, hb2, hb3, hb5, hb6, hb7]
  omega

theorem swapBytes64_of_u32_halves (lo hi : Nat)
    (hlo : lo < U32Modulus) (_hhi : hi < U32Modulus) :
    swapBytes64 (lo + hi * 4294967296) =
      swapBytes32 lo * 4294967296 + swapBytes32 hi := by
  unfold U32Modulus at hlo
  rw [swapBytes64_eq_swapBytes32_halves]
  have hmod : (lo + hi * 4294967296) % 4294967296 = lo := by omega
  have hdiv : (lo + hi * 4294967296) / 4294967296 = hi := by omega
  rw [hmod, hdiv]

/-- `swapBytes64` is an involution on every 64-bit integer `n < 2^64`. -/
theorem swapBytes64_involutive {n : Nat} (hn : n < U64Modulus) :
    swapBytes64 (swapBytes64 n) = n := by
  unfold U64Modulus at hn
  let lo := n % 4294967296
  let hi := n / 4294967296
  have hlo : lo < U32Modulus := by unfold lo U32Modulus; omega
  have hhi : hi < U32Modulus := by unfold hi U32Modulus; omega
  have hn_eq : n = lo + hi * 4294967296 := by unfold lo hi; omega
  have h_swap_lo_lt : swapBytes32 lo < U32Modulus := by
    unfold swapBytes32 U32Modulus at hlo ⊢; omega
  have h_swap_hi_lt : swapBytes32 hi < U32Modulus := by
    unfold swapBytes32 U32Modulus at hhi ⊢; omega
  conv => lhs; arg 1; rw [hn_eq]
  rw [swapBytes64_of_u32_halves lo hi hlo hhi,
      Nat.add_comm (swapBytes32 lo * 4294967296) (swapBytes32 hi),
      swapBytes64_of_u32_halves (swapBytes32 hi) (swapBytes32 lo) h_swap_hi_lt h_swap_lo_lt,
      swapBytes32_involutive hhi, swapBytes32_involutive hlo]
  omega

/-! ## 2. Closed-Form Bridges for `scalarPow2`, `scalarModulus`, and `wrapScalarBits` -/

private theorem beq_zero_eq_false_of_pos {n : Nat} (h : 0 < n) :
    Nat.beq n 0 = false := by
  cases n with
  | zero => omega
  | succ _ => rfl

private theorem nat_ble_eq_decide (a b : Nat) :
    Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b with
  | true => exact (decide_eq_true (Nat.le_of_ble_eq_true h)).symm
  | false =>
    refine (decide_eq_false (fun hle => ?_)).symm
    rw [Nat.ble_eq_true_of_le hle] at h; nomatch h

/-- `scalarPow2 k` equals $2^k$. -/
@[simp]
theorem scalarPow2_eq_two_pow : ∀ k : Nat, scalarPow2 k = 2 ^ k
  | 0 => rfl
  | k + 1 => by
    unfold scalarPow2
    change 2 * scalarPow2 k = 2 ^ (k + 1)
    rw [scalarPow2_eq_two_pow k, Nat.pow_succ, Nat.mul_comm]

theorem scalarPow2_pos (k : Nat) : 0 < scalarPow2 k := by
  rw [scalarPow2_eq_two_pow]
  exact Nat.two_pow_pos k

/-- `scalarModulus sz` equals $2^{8 \cdot \text{sz}}$. -/
@[simp]
theorem scalarModulus_eq_two_pow : ∀ sz : Nat, scalarModulus sz = 2 ^ (8 * sz)
  | 0 => rfl
  | k + 1 => by
    unfold scalarModulus
    change 256 * scalarModulus k = 2 ^ (8 * (k + 1))
    have h256 : (256 : Nat) = 2 ^ 8 := rfl
    have hmul : 8 * (k + 1) = 8 * k + 8 := by omega
    rw [scalarModulus_eq_two_pow k, h256, hmul, Nat.pow_add, Nat.mul_comm]

/-- `scalarModulus sz` coincides with `widthModulus sz`. -/
theorem scalarModulus_eq_widthModulus (sz : Nat) :
    scalarModulus sz = widthModulus sz := by
  unfold widthModulus
  rw [scalarModulus_eq_two_pow, Nat.mul_comm]

theorem scalarModulus_pos (sz : Nat) : 0 < scalarModulus sz := by
  rw [scalarModulus_eq_two_pow]
  exact Nat.two_pow_pos (8 * sz)

/-- For positive byte width `sz > 0`, `signedHalfModulus sz = 2 ^ (8 * sz - 1)`. -/
@[simp]
theorem signedHalfModulus_eq_two_pow {sz : Nat} (hsz : 0 < sz) :
    signedHalfModulus sz = 2 ^ (8 * sz - 1) := by
  unfold signedHalfModulus
  change scalarModulus sz / 2 = 2 ^ (8 * sz - 1)
  rw [scalarModulus_eq_two_pow]
  have hsplit : 8 * sz = (8 * sz - 1) + 1 := by omega
  conv => lhs; arg 1; rw [hsplit]
  rw [Nat.pow_succ]
  omega

/-- For positive byte width `sz > 0`, `signedHalfModulus sz = widthSignBit sz`. -/
theorem signedHalfModulus_eq_widthSignBit {sz : Nat} (hsz : 0 < sz) :
    signedHalfModulus sz = widthSignBit sz := by
  unfold widthSignBit
  rw [signedHalfModulus_eq_two_pow hsz, Nat.mul_comm]

/-- `wrapScalarBits val modulus` reduces to `val % modulus` for all `val` and `modulus`. -/
@[simp]
theorem wrapScalarBits_eq_mod_modulus (val modulus : Nat) :
    wrapScalarBits val modulus = val % modulus := by
  unfold wrapScalarBits
  cases h : Nat.ble modulus val with
  | true => rfl
  | false =>
    have hlt : val < modulus := by
      cases Nat.lt_or_ge val modulus with
      | inl hlt => exact hlt
      | inr hge =>
        rw [Nat.ble_eq_true_of_le hge] at h
        nomatch h
    exact (Nat.mod_eq_of_lt hlt).symm

/-- When `val < modulus`, `wrapScalarBits val modulus = val`. -/
theorem wrapScalarBits_eq_self_of_lt {val modulus : Nat} (h : val < modulus) :
    wrapScalarBits val modulus = val := by
  rw [wrapScalarBits_eq_mod_modulus]
  exact Nat.mod_eq_of_lt h

/-- When `0 < modulus`, `wrapScalarBits val modulus < modulus`. -/
theorem wrapScalarBits_lt_of_pos (val : Nat) {modulus : Nat} (h : 0 < modulus) :
    wrapScalarBits val modulus < modulus := by
  rw [wrapScalarBits_eq_mod_modulus]
  exact Nat.mod_lt val h

/-- `wrapScalarBits` is idempotent. -/
@[simp]
theorem wrapScalarBits_idem (val modulus : Nat) :
    wrapScalarBits (wrapScalarBits val modulus) modulus =
      wrapScalarBits val modulus := by
  rw [wrapScalarBits_eq_mod_modulus, wrapScalarBits_eq_mod_modulus, Nat.mod_mod]

/-! ## 3. Closed-Form Bitwise Equivalences (`bitwiseAndBits`, `bitwiseOrBits`, `bitwiseXorBits`) -/

private theorem mod_two_mul_decomp (a p : Nat) (hp : 0 < p) :
    a % (2 * p) = a % 2 + 2 * ((a / 2) % p) := by
  have h1 := Nat.div_add_mod a 2
  have h2 := Nat.div_add_mod (a / 2) p
  have h_decomp : a = (2 * p) * ((a / 2) / p) + (a % 2 + 2 * ((a / 2) % p)) := by
    calc
      a = 2 * (a / 2) + a % 2 := h1.symm
      _ = 2 * (p * ((a / 2) / p) + (a / 2) % p) + a % 2 :=
        congrArg (· + a % 2) (congrArg (2 * ·) h2.symm)
      _ = (2 * p) * ((a / 2) / p) + (a % 2 + 2 * ((a / 2) % p)) := by
        rw [Nat.left_distrib, ← Nat.mul_assoc, Nat.add_assoc,
            Nat.add_comm (2 * ((a / 2) % p)) (a % 2)]
  have h_rem_lt : a % 2 + 2 * ((a / 2) % p) < 2 * p := by
    have h_lt1 : a % 2 < 2 := Nat.mod_lt a (by decide)
    have h_lt2 : (a / 2) % p < p := Nat.mod_lt (a / 2) hp
    omega
  conv => lhs; rw [h_decomp]
  rw [Nat.mul_comm (2 * p) _, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt h_rem_lt]

private theorem mod_two_pow_succ_decomp (x k : Nat) :
    x % (2 ^ (k + 1)) = x % 2 + 2 * ((x / 2) % (2 ^ k)) := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hpow]
  exact mod_two_mul_decomp x (2 ^ k) (Nat.two_pow_pos k)

private theorem land_low_bit_eq (a b : Nat) :
    (match Bool.and (Nat.beq (a % 2) 1) (Nat.beq (b % 2) 1) with
     | true => 1
     | false => 0) = (a &&& b) % 2 := by
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hab : (a &&& b) % 2 = 0 ∨ (a &&& b) % 2 = 1 := by omega
  have hiff := @Nat.and_mod_two_eq_one a b
  rcases hab with hab0 | hab1 <;> rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1
  · rw [hab0, ha0, hb0] at hiff ⊢; revert hiff; decide
  · rw [hab0, ha0, hb1] at hiff ⊢; revert hiff; decide
  · rw [hab0, ha1, hb0] at hiff ⊢; revert hiff; decide
  · rw [hab0, ha1, hb1] at hiff ⊢; revert hiff; decide
  · rw [hab1, ha0, hb0] at hiff ⊢; revert hiff; decide
  · rw [hab1, ha0, hb1] at hiff ⊢; revert hiff; decide
  · rw [hab1, ha1, hb0] at hiff ⊢; revert hiff; decide
  · rw [hab1, ha1, hb1] at hiff ⊢; revert hiff; decide

private theorem lor_low_bit_eq (a b : Nat) :
    (match Bool.or (Nat.beq (a % 2) 1) (Nat.beq (b % 2) 1) with
     | true => 1
     | false => 0) = (a ||| b) % 2 := by
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hab : (a ||| b) % 2 = 0 ∨ (a ||| b) % 2 = 1 := by omega
  have hiff := @Nat.or_mod_two_eq_one a b
  rcases hab with hab0 | hab1 <;> rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1
  · rw [hab0, ha0, hb0] at hiff ⊢; revert hiff; decide
  · rw [hab0, ha0, hb1] at hiff ⊢; revert hiff; decide
  · rw [hab0, ha1, hb0] at hiff ⊢; revert hiff; decide
  · rw [hab0, ha1, hb1] at hiff ⊢; revert hiff; decide
  · rw [hab1, ha0, hb0] at hiff ⊢; revert hiff; decide
  · rw [hab1, ha0, hb1] at hiff ⊢; revert hiff; decide
  · rw [hab1, ha1, hb0] at hiff ⊢; revert hiff; decide
  · rw [hab1, ha1, hb1] at hiff ⊢; revert hiff; decide

private theorem xor_low_bit_eq (a b : Nat) :
    (match Nat.beq (a % 2) (b % 2) with
     | true => 0
     | false => 1) = (a ^^^ b) % 2 := by
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hab : (a ^^^ b) % 2 = 0 ∨ (a ^^^ b) % 2 = 1 := by omega
  have hiff := @Nat.xor_mod_two_eq_one a b
  rcases hab with hab0 | hab1 <;> rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1
  · rw [hab0, ha0, hb0]
  · rw [hab0, ha0, hb1] at hiff ⊢; revert hiff; decide
  · rw [hab0, ha1, hb0] at hiff ⊢; revert hiff; decide
  · rw [hab0, ha1, hb1]
  · rw [hab1, ha0, hb0] at hiff ⊢; revert hiff; decide
  · rw [hab1, ha0, hb1]
  · rw [hab1, ha1, hb0]
  · rw [hab1, ha1, hb1] at hiff ⊢; revert hiff; decide

/--
Closed-form equivalence for `bitwiseAndBits`: recursive `w`-bit AND equals
`(a &&& b) % (2 ^ w)` without bit-by-bit unrolling.
-/
@[simp]
theorem bitwiseAndBits_eq_land (w a b : Nat) :
    bitwiseAndBits w a b = (a &&& b) % (2 ^ w) := by
  induction w generalizing a b with
  | zero =>
    simp [bitwiseAndBits, Nat.mod_one]
  | succ k ih =>
    unfold bitwiseAndBits
    change (match Bool.and (Nat.beq (a % 2) 1) (Nat.beq (b % 2) 1) with
            | true => 1
            | false => 0) + 2 * bitwiseAndBits k (a / 2) (b / 2) =
      (a &&& b) % (2 ^ (k + 1))
    rw [land_low_bit_eq a b, ih (a / 2) (b / 2),
        ← Nat.and_div_two, ← mod_two_pow_succ_decomp]

/-- When `a < 2 ^ w`, `bitwiseAndBits w a b = a &&& b`. -/
theorem bitwiseAndBits_eq_land_of_lt_left {w a b : Nat} (ha : a < 2 ^ w) :
    bitwiseAndBits w a b = a &&& b := by
  rw [bitwiseAndBits_eq_land]
  have hlt : a &&& b < 2 ^ w := by
    rw [Nat.and_comm]
    exact Nat.and_lt_two_pow b ha
  exact Nat.mod_eq_of_lt hlt

/-- When `b < 2 ^ w`, `bitwiseAndBits w a b = a &&& b`. -/
theorem bitwiseAndBits_eq_land_of_lt_right {w a b : Nat} (hb : b < 2 ^ w) :
    bitwiseAndBits w a b = a &&& b := by
  rw [bitwiseAndBits_eq_land]
  exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow a hb)

theorem bitwiseAndBits_lt_two_pow (w a b : Nat) :
    bitwiseAndBits w a b < 2 ^ w := by
  rw [bitwiseAndBits_eq_land]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem bitwiseAndBits_comm (w a b : Nat) :
    bitwiseAndBits w a b = bitwiseAndBits w b a := by
  rw [bitwiseAndBits_eq_land, bitwiseAndBits_eq_land, Nat.and_comm]

@[simp]
theorem bitwiseAndBits_idem (w a : Nat) :
    bitwiseAndBits w a a = a % (2 ^ w) := by
  rw [bitwiseAndBits_eq_land, Nat.and_self]

/--
Closed-form equivalence for `bitwiseOrBits`: recursive `w`-bit OR equals
`(a ||| b) % (2 ^ w)` without bit-by-bit unrolling.
-/
@[simp]
theorem bitwiseOrBits_eq_lor (w a b : Nat) :
    bitwiseOrBits w a b = (a ||| b) % (2 ^ w) := by
  induction w generalizing a b with
  | zero =>
    simp [bitwiseOrBits, Nat.mod_one]
  | succ k ih =>
    unfold bitwiseOrBits
    change (match Bool.or (Nat.beq (a % 2) 1) (Nat.beq (b % 2) 1) with
            | true => 1
            | false => 0) + 2 * bitwiseOrBits k (a / 2) (b / 2) =
      (a ||| b) % (2 ^ (k + 1))
    rw [lor_low_bit_eq a b, ih (a / 2) (b / 2),
        ← Nat.or_div_two, ← mod_two_pow_succ_decomp]

/-- When `a < 2 ^ w` and `b < 2 ^ w`, `bitwiseOrBits w a b = a ||| b`. -/
theorem bitwiseOrBits_eq_lor_of_lt {w a b : Nat}
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    bitwiseOrBits w a b = a ||| b := by
  rw [bitwiseOrBits_eq_lor]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha hb)

theorem bitwiseOrBits_lt_two_pow (w a b : Nat) :
    bitwiseOrBits w a b < 2 ^ w := by
  rw [bitwiseOrBits_eq_lor]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem bitwiseOrBits_comm (w a b : Nat) :
    bitwiseOrBits w a b = bitwiseOrBits w b a := by
  rw [bitwiseOrBits_eq_lor, bitwiseOrBits_eq_lor, Nat.or_comm]

@[simp]
theorem bitwiseOrBits_idem (w a : Nat) :
    bitwiseOrBits w a a = a % (2 ^ w) := by
  rw [bitwiseOrBits_eq_lor, Nat.or_self]

/--
Closed-form equivalence for `bitwiseXorBits`: recursive `w`-bit XOR equals
`(a ^^^ b) % (2 ^ w)` without bit-by-bit unrolling.
-/
@[simp]
theorem bitwiseXorBits_eq_xor (w a b : Nat) :
    bitwiseXorBits w a b = (a ^^^ b) % (2 ^ w) := by
  induction w generalizing a b with
  | zero =>
    simp [bitwiseXorBits, Nat.mod_one]
  | succ k ih =>
    unfold bitwiseXorBits
    change (match Nat.beq (a % 2) (b % 2) with
            | true => 0
            | false => 1) + 2 * bitwiseXorBits k (a / 2) (b / 2) =
      (a ^^^ b) % (2 ^ (k + 1))
    rw [xor_low_bit_eq a b, ih (a / 2) (b / 2),
        ← Nat.xor_div_two, ← mod_two_pow_succ_decomp]

/-- When `a < 2 ^ w` and `b < 2 ^ w`, `bitwiseXorBits w a b = a ^^^ b`. -/
theorem bitwiseXorBits_eq_xor_of_lt {w a b : Nat}
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    bitwiseXorBits w a b = a ^^^ b := by
  rw [bitwiseXorBits_eq_xor]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb)

theorem bitwiseXorBits_lt_two_pow (w a b : Nat) :
    bitwiseXorBits w a b < 2 ^ w := by
  rw [bitwiseXorBits_eq_xor]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem bitwiseXorBits_comm (w a b : Nat) :
    bitwiseXorBits w a b = bitwiseXorBits w b a := by
  rw [bitwiseXorBits_eq_xor, bitwiseXorBits_eq_xor, Nat.xor_comm]

@[simp]
theorem bitwiseXorBits_self (w a : Nat) :
    bitwiseXorBits w a a = 0 := by
  rw [bitwiseXorBits_eq_xor, Nat.xor_self, Nat.zero_mod]

/-! ## 4. Closed-Form Shift, Sign-Bit, Arithmetic `shr`, and Sign-Extension Bridges -/

/-- `shiftLeftBits a shift (scalarModulus sz)` equals `(a <<< shift) % (2 ^ (8 * sz))`. -/
@[simp]
theorem shiftLeftBits_eq_shiftLeft_mod (a shift sz : Nat) :
    shiftLeftBits a shift (scalarModulus sz) = (a <<< shift) % (2 ^ (8 * sz)) := by
  unfold shiftLeftBits
  change wrapScalarBits (a * scalarPow2 shift) (scalarModulus sz) =
    (a <<< shift) % (2 ^ (8 * sz))
  rw [wrapScalarBits_eq_mod_modulus, scalarPow2_eq_two_pow,
      scalarModulus_eq_two_pow, Nat.shiftLeft_eq]

/-- `shiftLeftBits a shift modulus` equals `(a <<< shift) % modulus`. -/
@[simp]
theorem shiftLeftBits_eq_shiftLeft_mod_general (a shift modulus : Nat) :
    shiftLeftBits a shift modulus = (a <<< shift) % modulus := by
  unfold shiftLeftBits
  change wrapScalarBits (a * scalarPow2 shift) modulus = (a <<< shift) % modulus
  rw [wrapScalarBits_eq_mod_modulus, scalarPow2_eq_two_pow, Nat.shiftLeft_eq]

/-- `shiftRightUnsignedBits a shift` equals `a >>> shift`. -/
@[simp]
theorem shiftRightUnsignedBits_eq_shiftRight (a shift : Nat) :
    shiftRightUnsignedBits a shift = a >>> shift := by
  unfold shiftRightUnsignedBits
  change a / scalarPow2 shift = a >>> shift
  rw [scalarPow2_eq_two_pow, Nat.shiftRight_eq_div_pow]

/-- `isSignedNegative bits sizeBytes` equals `(BitVec.ofNat (8 * sizeBytes) bits).msb`. -/
@[simp]
theorem isSignedNegative_eq_msb (bits sizeBytes : Nat) :
    isSignedNegative bits sizeBytes =
      (BitVec.ofNat (8 * sizeBytes) bits).msb := by
  unfold isSignedNegative
  cases hsz : Nat.beq sizeBytes 0 with
  | true =>
    have h0 : sizeBytes = 0 := Nat.eq_of_beq_eq_true hsz
    subst h0
    rfl
  | false =>
    have hpos : 0 < sizeBytes := by
      cases sizeBytes with
      | zero => nomatch hsz
      | succ k => exact Nat.succ_pos k
    dsimp only
    change Nat.ble (scalarModulus sizeBytes / 2)
      (wrapScalarBits bits (scalarModulus sizeBytes)) =
      (BitVec.ofNat (8 * sizeBytes) bits).msb
    have hhalf : scalarModulus sizeBytes / 2 = 2 ^ (8 * sizeBytes - 1) :=
      signedHalfModulus_eq_two_pow hpos
    rw [hhalf, wrapScalarBits_eq_mod_modulus, scalarModulus_eq_two_pow,
        BitVec.msb_eq_decide, BitVec.toNat_ofNat, nat_ble_eq_decide]

@[simp]
theorem isSignedNegative_wrapScalarBits (bits sizeBytes : Nat) :
    isSignedNegative (wrapScalarBits bits (scalarModulus sizeBytes)) sizeBytes =
      isSignedNegative bits sizeBytes := by
  rw [isSignedNegative_eq_msb, isSignedNegative_eq_msb,
      wrapScalarBits_eq_mod_modulus, scalarModulus_eq_two_pow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod]

private theorem mul_add_div_of_lt {a b p : Nat} (hp : 0 < p) (hb : b < p) :
    (a * p + b) / p = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right b a hp, Nat.div_eq_of_lt hb, Nat.zero_add]

private theorem sub_one_sub_linear {m q d : Nat} (hd : d < q) (hq : q ≤ m) :
    m - 1 - (q - 1 - d) = d + (m - q) := by
  omega

private theorem sub_one_sub_div_mul {q p c : Nat} (hp : 0 < p) (hc : c < q * p) :
    q * p - 1 - (q * p - 1 - c) / p = c / p + (q * p - q) := by
  have h_div_mod : p * (c / p) + c % p = c := Nat.div_add_mod c p
  have h_mod_lt : c % p < p := Nat.mod_lt c hp
  have h_div_lt : c / p < q :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hc)
  have h_mul_comm : p * (c / p) = (c / p) * p := Nat.mul_comm _ _
  have h_split : (q - 1 - c / p) * p + p + (c / p) * p = q * p := by
    have h1 : (q - 1 - c / p) + 1 + (c / p) = q := by omega
    calc
      (q - 1 - c / p) * p + p + (c / p) * p
        = ((q - 1 - c / p) + 1 + (c / p)) * p := by
          rw [Nat.right_distrib, Nat.right_distrib, Nat.one_mul]
      _ = q * p := by rw [h1]
  have h_decomp : q * p - 1 - c = (q - 1 - c / p) * p + (p - 1 - c % p) := by
    omega
  have h_rem_lt : p - 1 - c % p < p := by omega
  have h_quot : (q * p - 1 - c) / p = q - 1 - c / p := by
    rw [h_decomp]
    exact mul_add_div_of_lt hp h_rem_lt
  rw [h_quot]
  exact sub_one_sub_linear h_div_lt (Nat.le_mul_of_pos_right q hp)

/--
Key two's-complement arithmetic right-shift identity: for `c < 2 ^ w` and
`s ≤ w`, complement-shift-complement `2^w - 1 - (2^w - 1 - c) / 2^s` equals
`c / 2^s + (2^w - 2^(w - s))`.
-/
theorem sub_one_sub_div_two_pow {w s c : Nat} (hc : c < 2 ^ w) (hs : s ≤ w) :
    2 ^ w - 1 - (2 ^ w - 1 - c) / (2 ^ s) = c / (2 ^ s) + (2 ^ w - 2 ^ (w - s)) := by
  have h_w : w - s + s = w := by omega
  have h_pow_split : 2 ^ w = 2 ^ (w - s) * 2 ^ s := by
    rw [← Nat.pow_add, h_w]
  rw [h_pow_split] at hc ⊢
  exact sub_one_sub_div_mul (Nat.two_pow_pos s) hc

/--
Closed-form `BitVec.sshiftRight` equivalence for `arithmeticShrBits`: whenever
`0 < sizeBytes` and `shift ≤ 8 * sizeBytes`, `arithmeticShrBits bits sizeBytes shift`
equals `((BitVec.ofNat (8 * sizeBytes) bits).sshiftRight shift).toNat`.
-/
theorem arithmeticShrBits_eq_sshiftRight {bits sizeBytes shift : Nat}
    (_hsz : 0 < sizeBytes) (hshift : shift ≤ 8 * sizeBytes) :
    arithmeticShrBits bits sizeBytes shift =
      ((BitVec.ofNat (8 * sizeBytes) bits).sshiftRight shift).toNat := by
  unfold arithmeticShrBits
  dsimp only
  rw [isSignedNegative_wrapScalarBits, isSignedNegative_eq_msb,
      BitVec.toNat_sshiftRight, BitVec.toNat_ofNat]
  have hc_lt : bits % 2 ^ (8 * sizeBytes) < 2 ^ (8 * sizeBytes) :=
    Nat.mod_lt bits (Nat.two_pow_pos (8 * sizeBytes))
  cases hmsb : (BitVec.ofNat (8 * sizeBytes) bits).msb with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, wrapScalarBits_eq_mod_modulus,
               scalarModulus_eq_two_pow, shiftRightUnsignedBits_eq_shiftRight]
    have hdiv_lt : (bits % 2 ^ (8 * sizeBytes)) >>> shift < 2 ^ (8 * sizeBytes) := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hc_lt
    exact Nat.mod_eq_of_lt hdiv_lt
  | true =>
    simp only [↓reduceIte, wrapScalarBits_eq_mod_modulus,
               scalarModulus_eq_two_pow, shiftRightUnsignedBits_eq_shiftRight,
               scalarPow2_eq_two_pow]
    have hmul8 : sizeBytes.mul 8 = 8 * sizeBytes := Nat.mul_comm sizeBytes 8
    change ((bits % 2 ^ (8 * sizeBytes)) >>> shift +
        (2 ^ (8 * sizeBytes) - 2 ^ (sizeBytes.mul 8 - shift))) % 2 ^ (8 * sizeBytes) =
      2 ^ (8 * sizeBytes) - 1 - (2 ^ (8 * sizeBytes) - 1 - bits % 2 ^ (8 * sizeBytes)) >>> shift
    rw [hmul8, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    rw [sub_one_sub_div_two_pow hc_lt hshift]
    have h_w : 8 * sizeBytes - shift + shift = 8 * sizeBytes := by omega
    have h_pow_split : 2 ^ (8 * sizeBytes) = 2 ^ (8 * sizeBytes - shift) * 2 ^ shift := by
      rw [← Nat.pow_add, h_w]
    have h_quot_lt : (bits % 2 ^ (8 * sizeBytes)) / 2 ^ shift < 2 ^ (8 * sizeBytes - shift) := by
      have h1 : bits % 2 ^ (8 * sizeBytes) < 2 ^ shift * 2 ^ (8 * sizeBytes - shift) := by
        rw [Nat.mul_comm (2 ^ shift) (2 ^ (8 * sizeBytes - shift)), ← h_pow_split]
        exact hc_lt
      exact Nat.div_lt_of_lt_mul h1
    have h_le : 2 ^ (8 * sizeBytes - shift) ≤ 2 ^ (8 * sizeBytes) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h_sum_lt :
        (bits % 2 ^ (8 * sizeBytes)) / 2 ^ shift +
          (2 ^ (8 * sizeBytes) - 2 ^ (8 * sizeBytes - shift)) < 2 ^ (8 * sizeBytes) := by
      omega
    exact Nat.mod_eq_of_lt h_sum_lt

/--
For any shift operand `b` and `0 < sizeBytes`, `arithmeticShrBits` with masked
shift `b % (sizeBytes * 8)` equals `BitVec.sshiftRight` by `b % (8 * sizeBytes)`.
-/
@[simp]
theorem arithmeticShrBits_mod_eq_sshiftRight {bits sizeBytes b : Nat}
    (hsz : 0 < sizeBytes) :
    arithmeticShrBits bits sizeBytes (b % (sizeBytes * 8)) =
      ((BitVec.ofNat (8 * sizeBytes) bits).sshiftRight (b % (8 * sizeBytes))).toNat := by
  have hmul : sizeBytes * 8 = 8 * sizeBytes := Nat.mul_comm sizeBytes 8
  rw [hmul]
  have hlt : b % (8 * sizeBytes) ≤ 8 * sizeBytes :=
    Nat.le_of_lt (Nat.mod_lt b (by omega))
  exact arithmeticShrBits_eq_sshiftRight hsz hlt

theorem arithmeticShrBits_lt_two_pow (bits sizeBytes shift : Nat) :
    arithmeticShrBits bits sizeBytes shift < 2 ^ (8 * sizeBytes) := by
  unfold arithmeticShrBits
  dsimp only
  split <;>
  · rw [wrapScalarBits_eq_mod_modulus, scalarModulus_eq_two_pow]
    exact Nat.mod_lt _ (Nat.two_pow_pos (8 * sizeBytes))

/--
When `w' ≤ w`, `BitVec.signExtend w' x` truncates to the low `w'` bits, matching
`x.setWidth w'`.
-/
theorem toNat_signExtend_of_le {w w' : Nat} (hle : w' ≤ w) (x : BitVec w) :
    (x.signExtend w').toNat = (x.setWidth w').toNat := by
  rw [BitVec.toNat_signExtend]
  have h_sub_zero : 2 ^ w' - 2 ^ w = 0 := by
    have : 2 ^ w' ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hle
    omega
  rw [h_sub_zero]
  cases x.msb <;> simp

/--
When `w' ≤ w`, `((BitVec.ofNat w a).signExtend w').toNat` reduces directly to
`a % (2 ^ w')`.
-/
theorem toNat_signExtend_ofNat_of_le {w w' : Nat} (hle : w' ≤ w) (a : Nat) :
    ((BitVec.ofNat w a).signExtend w').toNat = a % (2 ^ w') := by
  rw [toNat_signExtend_of_le hle, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 2 hle)

/--
Unconditional closed-form `BitVec.signExtend` characterization of
`signExtendBits`: for all `bits`, `srcBytes`, and `dstBytes` (both truncating
`dstBytes ≤ srcBytes` and widening `srcBytes < dstBytes`),
`signExtendBits bits srcBytes dstBytes` equals
`((BitVec.ofNat (8 * srcBytes) bits).signExtend (8 * dstBytes)).toNat`.
-/
@[simp]
theorem signExtendBits_eq_bitVec (bits srcBytes dstBytes : Nat) :
    signExtendBits bits srcBytes dstBytes =
      ((BitVec.ofNat (8 * srcBytes) bits).signExtend (8 * dstBytes)).toNat := by
  unfold signExtendBits
  dsimp only
  cases hle : Nat.ble dstBytes srcBytes with
  | true =>
    have h_le : dstBytes ≤ srcBytes := Nat.le_of_ble_eq_true hle
    have h_bits_le : 8 * dstBytes ≤ 8 * srcBytes := by omega
    simp only [wrapScalarBits_eq_mod_modulus, scalarModulus_eq_two_pow]
    rw [toNat_signExtend_of_le h_bits_le, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  | false =>
    rw [isSignedNegative_wrapScalarBits, isSignedNegative_eq_msb,
        BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have h_not_le : ¬ dstBytes ≤ srcBytes := fun h => by
      rw [Nat.ble_eq_true_of_le h] at hle; nomatch hle
    have h_lt : srcBytes < dstBytes := by omega
    have h_c_lt : bits % 2 ^ (8 * srcBytes) < 2 ^ (8 * dstBytes) :=
      Nat.lt_trans
        (Nat.mod_lt bits (Nat.two_pow_pos (8 * srcBytes)))
        (Nat.pow_lt_pow_right (by decide) (by omega))
    rw [Nat.mod_eq_of_lt h_c_lt]
    cases (BitVec.ofNat (8 * srcBytes) bits).msb with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
                 wrapScalarBits_eq_mod_modulus, scalarModulus_eq_two_pow]
    | true =>
      simp only [↓reduceIte, wrapScalarBits_eq_mod_modulus, scalarModulus_eq_two_pow]
      change 2 ^ (8 * dstBytes) - 2 ^ (8 * srcBytes) + bits % 2 ^ (8 * srcBytes) =
        bits % 2 ^ (8 * srcBytes) + (2 ^ (8 * dstBytes) - 2 ^ (8 * srcBytes))
      exact Nat.add_comm _ _

/-- When `dstBytes ≤ srcBytes`, `signExtendBits` truncates to `bits % 2 ^ (8 * dstBytes)`. -/
theorem signExtendBits_of_le {bits srcBytes dstBytes : Nat} (hle : dstBytes ≤ srcBytes) :
    signExtendBits bits srcBytes dstBytes = bits % (2 ^ (8 * dstBytes)) := by
  rw [signExtendBits_eq_bitVec]
  exact toNat_signExtend_ofNat_of_le (by omega) bits

theorem signExtendBits_lt_two_pow (bits srcBytes dstBytes : Nat) :
    signExtendBits bits srcBytes dstBytes < 2 ^ (8 * dstBytes) := by
  rw [signExtendBits_eq_bitVec]
  exact ((BitVec.ofNat (8 * srcBytes) bits).signExtend (8 * dstBytes)).isLt

/-! ## 5. `ScalarValue` & `BitVec (8 * s.sizeBytes)` Isomorphism -/

/--
Canonical alias for `Trusted.MirAst.ScalarInt` (`{ bits : Nat, sizeBytes : Nat }`).
-/
abbrev ScalarValue : Type := ScalarInt

namespace ScalarValue

/-- Convert a `ScalarValue` `s` to a fixed-width `BitVec (8 * s.sizeBytes)`. -/
@[reducible]
def toBitVec (s : ScalarValue) : BitVec (8 * s.sizeBytes) :=
  BitVec.ofNat (8 * s.sizeBytes) s.bits

/-- Construct a `ScalarValue` of byte width `sz` from a `BitVec w`. -/
@[reducible]
def ofBitVec {w : Nat} (sz : Nat) (bv : BitVec w) : ScalarValue :=
  { bits := bv.toNat, sizeBytes := sz }

/-- Well-formedness predicate for a canonical fixed-width `ScalarValue`. -/
def Wf (s : ScalarValue) : Prop :=
  0 < s.sizeBytes ∧ s.bits < 2 ^ (8 * s.sizeBytes)

/-- Canonicalize `s.bits` modulo `2 ^ (8 * s.sizeBytes)`. -/
@[reducible]
def canonicalize (s : ScalarValue) : ScalarValue :=
  { bits := s.bits % (2 ^ (8 * s.sizeBytes)), sizeBytes := s.sizeBytes }

/-- Fixed-width scalar constructors for Rust primitive integer types. -/
@[reducible] def u8 (bits : Nat) : ScalarValue := ⟨bits % U8Modulus, 1⟩
@[reducible] def u16 (bits : Nat) : ScalarValue := ⟨bits % U16Modulus, 2⟩
@[reducible] def u32 (bits : Nat) : ScalarValue := ⟨bits % U32Modulus, 4⟩
@[reducible] def u64 (bits : Nat) : ScalarValue := ⟨bits % U64Modulus, 8⟩
@[reducible] def usize (bits : Nat) : ScalarValue := ⟨bits % U64Modulus, 8⟩
@[reducible] def u128 (bits : Nat) : ScalarValue := ⟨bits % U128Modulus, 16⟩
@[reducible] def i8 (bits : Nat) : ScalarValue := ⟨bits % U8Modulus, 1⟩
@[reducible] def i16 (bits : Nat) : ScalarValue := ⟨bits % U16Modulus, 2⟩
@[reducible] def i32 (bits : Nat) : ScalarValue := ⟨bits % U32Modulus, 4⟩
@[reducible] def i64 (bits : Nat) : ScalarValue := ⟨bits % U64Modulus, 8⟩
@[reducible] def isize (bits : Nat) : ScalarValue := ⟨bits % U64Modulus, 8⟩
@[reducible] def i128 (bits : Nat) : ScalarValue := ⟨bits % U128Modulus, 16⟩

@[simp]
theorem sizeBytes_ofBitVec {w : Nat} (sz : Nat) (bv : BitVec w) :
    (ofBitVec sz bv).sizeBytes = sz := rfl

@[simp]
theorem bits_ofBitVec {w : Nat} (sz : Nat) (bv : BitVec w) :
    (ofBitVec sz bv).bits = bv.toNat := rfl

@[simp]
theorem toNat_toBitVec (s : ScalarValue) :
    s.toBitVec.toNat = s.bits % (2 ^ (8 * s.sizeBytes)) :=
  BitVec.toNat_ofNat s.bits (8 * s.sizeBytes)

theorem toNat_toBitVec_of_lt {s : ScalarValue} (hb : s.bits < 2 ^ (8 * s.sizeBytes)) :
    s.toBitVec.toNat = s.bits := by
  rw [toNat_toBitVec]
  exact Nat.mod_eq_of_lt hb

/-- Round-trip `toBitVec (ofBitVec sz bv)` at matching bit width `8 * sz`. -/
@[simp]
theorem toBitVec_ofBitVec_same (sz : Nat) (bv : BitVec (8 * sz)) :
    (ofBitVec sz bv).toBitVec = bv := by
  unfold toBitVec ofBitVec
  dsimp only
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- General `toBitVec (ofBitVec sz bv)` across arbitrary bit width `w`. -/
@[simp]
theorem toBitVec_ofBitVec {w : Nat} (sz : Nat) (bv : BitVec w) :
    (ofBitVec sz bv).toBitVec = bv.setWidth (8 * sz) := by
  unfold toBitVec ofBitVec
  dsimp only
  exact BitVec.ofNat_toNat (8 * sz) bv

/-- Round-trip `ofBitVec s.sizeBytes s.toBitVec = s.canonicalize`. -/
@[simp]
theorem ofBitVec_toBitVec_canonical (s : ScalarValue) :
    ofBitVec s.sizeBytes s.toBitVec = s.canonicalize := by
  unfold ofBitVec toBitVec canonicalize
  rw [BitVec.toNat_ofNat]

/-- Round-trip `ofBitVec s.sizeBytes s.toBitVec = s` when `s.bits < 2 ^ (8 * s.sizeBytes)`. -/
theorem ofBitVec_toBitVec {s : ScalarValue} (hb : s.bits < 2 ^ (8 * s.sizeBytes)) :
    ofBitVec s.sizeBytes s.toBitVec = s := by
  cases s with
  | mk bits sz =>
    unfold ofBitVec toBitVec
    dsimp only at hb ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

theorem wf_ofBitVec (sz : Nat) (hsz : 0 < sz) (bv : BitVec (8 * sz)) :
    Wf (ofBitVec sz bv) :=
  ⟨hsz, bv.isLt⟩

end ScalarValue

namespace _root_.Trusted.Rustc.V2026_06_01.MirAst.ScalarInt

/-- Alias of `ScalarValue.toBitVec` in namespace `ScalarInt` for dot notation. -/
@[reducible]
def toBitVec (s : ScalarInt) : BitVec (8 * s.sizeBytes) :=
  ScalarValue.toBitVec s

/-- Alias of `ScalarValue.ofBitVec` in namespace `ScalarInt` for dot notation. -/
@[reducible]
def ofBitVec {w : Nat} (sz : Nat) (bv : BitVec w) : ScalarInt :=
  ScalarValue.ofBitVec sz bv

end _root_.Trusted.Rustc.V2026_06_01.MirAst.ScalarInt

/-! ## 6. Closed-Form Scalar Evaluators (`evalBinOp`, `evalBinOpChecked`, `evalUnOp`, `evalCastValue`) -/

/--
Pure closed-form binary scalar operator over `ScalarValue`, matching the
scalar-returning branches of `Trusted.MirSemantics.evalScalarBinOp`.
-/
@[reducible]
def evalBinOp
    (op : BinOp)
    (lhs rhs : ScalarValue)
    (isSigned : Bool := false) :
    Option ScalarValue :=
  match Nat.beq lhs.sizeBytes 0 with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let numBits := 8 * sz
    let modulus := 2 ^ numBits
    let a := lhs.bits
    let b := rhs.bits
    match op with
    | .shl =>
      match Nat.beq rhs.sizeBytes 0 with
      | true => .none
      | false =>
        let shift := b % numBits
        .some ⟨(a <<< shift) % modulus, sz⟩
    | .shlUnchecked =>
      match Nat.beq rhs.sizeBytes 0 with
      | true => .none
      | false =>
        match Nat.ble numBits b with
        | true => .none
        | false => .some ⟨(a <<< b) % modulus, sz⟩
    | .shr =>
      match Nat.beq rhs.sizeBytes 0 with
      | true => .none
      | false =>
        let shift := b % numBits
        let shifted :=
          match isSigned with
          | false => (a >>> shift) % modulus
          | true => ((BitVec.ofNat numBits a).sshiftRight shift).toNat
        .some ⟨shifted, sz⟩
    | .shrUnchecked =>
      match Nat.beq rhs.sizeBytes 0 with
      | true => .none
      | false =>
        match Nat.ble numBits b with
        | true => .none
        | false =>
          let shifted :=
            match isSigned with
            | false => (a >>> b) % modulus
            | true => ((BitVec.ofNat numBits a).sshiftRight b).toNat
          .some ⟨shifted, sz⟩
    | _ =>
      match Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => .none
      | true =>
        match op with
        | .bitAnd => .some ⟨(a &&& b) % modulus, sz⟩
        | .bitOr => .some ⟨(a ||| b) % modulus, sz⟩
        | .bitXor => .some ⟨(a ^^^ b) % modulus, sz⟩
        | .add => .some ⟨(a + b) % modulus, sz⟩
        | .sub =>
          match Nat.ble b a with
          | true => .some ⟨(a - b) % modulus, sz⟩
          | false => .some ⟨(modulus + (a % modulus) - (b % modulus)) % modulus, sz⟩
        | .mul => .some ⟨(a * b) % modulus, sz⟩
        | .addUnchecked =>
          match isSigned with
          | false =>
            match Nat.ble modulus (a + b) with
            | true => .none
            | false => .some ⟨a + b, sz⟩
          | true =>
            match signedOverflowAdd a b sz with
            | true => .none
            | false => .some ⟨(a + b) % modulus, sz⟩
        | .subUnchecked =>
          match isSigned with
          | false =>
            match Nat.ble b a with
            | true =>
              match Nat.ble modulus (a - b) with
              | true => .none
              | false => .some ⟨a - b, sz⟩
            | false => .none
          | true =>
            match signedOverflowSub a b sz with
            | true => .none
            | false =>
              let ca := a % modulus
              let cb := b % modulus
              let diff :=
                match Nat.ble cb ca with
                | true => (ca - cb) % modulus
                | false => (modulus + ca - cb) % modulus
              .some ⟨diff, sz⟩
        | .mulUnchecked =>
          match isSigned with
          | false =>
            match Nat.ble modulus (a * b) with
            | true => .none
            | false => .some ⟨a * b, sz⟩
          | true =>
            match signedOverflowMul a b sz with
            | true => .none
            | false => .some ⟨(a * b) % modulus, sz⟩
        | .div =>
          match Nat.beq b 0 with
          | true => .none
          | false =>
            match isSigned with
            | false => .some ⟨(a / b) % modulus, sz⟩
            | true =>
              let minSigned := 2 ^ (numBits - 1)
              let minusOne := modulus - 1
              let ca := a % modulus
              let cb := b % modulus
              match Bool.and (Nat.beq ca minSigned) (Nat.beq cb minusOne) with
              | true => .none
              | false =>
                let negA := isSignedNegative ca sz
                let negB := isSignedNegative cb sz
                let magA := match negA with | false => ca | true => modulus - ca
                let magB := match negB with | false => cb | true => modulus - cb
                let magQ := magA / magB
                let quotBits :=
                  match Nat.beq magQ 0 with
                  | true => 0
                  | false =>
                    match negA, negB with
                    | false, false => magQ % modulus
                    | true, true => magQ % modulus
                    | _, _ => (modulus - magQ) % modulus
                .some ⟨quotBits, sz⟩
        | .rem =>
          match Nat.beq b 0 with
          | true => .none
          | false =>
            match isSigned with
            | false => .some ⟨(a % b) % modulus, sz⟩
            | true =>
              let minSigned := 2 ^ (numBits - 1)
              let minusOne := modulus - 1
              let ca := a % modulus
              let cb := b % modulus
              match Bool.and (Nat.beq ca minSigned) (Nat.beq cb minusOne) with
              | true => .none
              | false =>
                let negA := isSignedNegative ca sz
                let negB := isSignedNegative cb sz
                let magA := match negA with | false => ca | true => modulus - ca
                let magB := match negB with | false => cb | true => modulus - cb
                let magR := magA % magB
                let remBits :=
                  match Nat.beq magR 0 with
                  | true => 0
                  | false =>
                    match negA with
                    | false => magR % modulus
                    | true => (modulus - magR) % modulus
                .some ⟨remBits, sz⟩
        | .eq => .some (boolToScalar (Nat.beq a b))
        | .ne => .some (boolToScalar (Bool.not (Nat.beq a b)))
        | .lt =>
          let cmp :=
            match isSigned with
            | false => Bool.not (Nat.ble b a)
            | true => signedLt a b sz
          .some (boolToScalar cmp)
        | .le =>
          let cmp :=
            match isSigned with
            | false => Nat.ble a b
            | true => signedLe a b sz
          .some (boolToScalar cmp)
        | .gt =>
          let cmp :=
            match isSigned with
            | false => Bool.not (Nat.ble a b)
            | true => signedLt b a sz
          .some (boolToScalar cmp)
        | .ge =>
          let cmp :=
            match isSigned with
            | false => Nat.ble b a
            | true => signedLe b a sz
          .some (boolToScalar cmp)
        | .cmp =>
          match isSigned with
          | false =>
            match Nat.beq a b with
            | true => .some ⟨0, 1⟩
            | false =>
              match Nat.ble a b with
              | true => .some ⟨255, 1⟩
              | false => .some ⟨1, 1⟩
          | true =>
            let ca := a % modulus
            let cb := b % modulus
            match Nat.beq ca cb with
            | true => .some ⟨0, 1⟩
            | false =>
              match signedLt ca cb sz with
              | true => .some ⟨255, 1⟩
              | false => .some ⟨1, 1⟩
        | _ => .none

/--
Checked binary arithmetic evaluator returning `(wrappedResult, overflowed)` for
`.add` / `.addWithOverflow`, `.sub` / `.subWithOverflow`, and
`.mul` / `.mulWithOverflow`.
-/
@[reducible]
def evalBinOpChecked
    (op : BinOp)
    (lhs rhs : ScalarValue)
    (isSigned : Bool := false) :
    Option (ScalarValue × Bool) :=
  match
    Bool.or
      (Nat.beq lhs.sizeBytes 0)
      (Bool.not (Nat.beq lhs.sizeBytes rhs.sizeBytes))
  with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let modulus := 2 ^ (8 * sz)
    let a := lhs.bits
    let b := rhs.bits
    match op with
    | .add | .addWithOverflow =>
      let wrapped : ScalarValue := ⟨(a + b) % modulus, sz⟩
      let ovf :=
        match isSigned with
        | false => Nat.ble modulus (a + b)
        | true => signedOverflowAdd a b sz
      .some (wrapped, ovf)
    | .sub | .subWithOverflow =>
      match isSigned with
      | false =>
        match Nat.ble b a with
        | true => .some (⟨(a - b) % modulus, sz⟩, false)
        | false => .some (⟨(modulus + (a % modulus) - (b % modulus)) % modulus, sz⟩, true)
      | true =>
        let ca := a % modulus
        let cb := b % modulus
        let diff :=
          match Nat.ble cb ca with
          | true => (ca - cb) % modulus
          | false => (modulus + ca - cb) % modulus
        .some (⟨diff, sz⟩, signedOverflowSub a b sz)
    | .mul | .mulWithOverflow =>
      let wrapped : ScalarValue := ⟨(a * b) % modulus, sz⟩
      let ovf :=
        match isSigned with
        | false => Nat.ble modulus (a * b)
        | true => signedOverflowMul a b sz
      .some (wrapped, ovf)
    | _ => .none

/--
Pure unary scalar evaluator for `UnOp.not` and `UnOp.neg` on `ScalarValue`.
-/
@[reducible]
def evalUnOp
    (op : UnOp)
    (sc : ScalarValue)
    (isBool : Bool := false) :
    Option ScalarValue :=
  match op with
  | .not =>
    match isBool with
    | true =>
      match Nat.beq sc.sizeBytes 1 with
      | false => .none
      | true =>
        match Nat.beq sc.bits 0 with
        | true => .some ⟨1, 1⟩
        | false =>
          match Nat.beq sc.bits 1 with
          | true => .some ⟨0, 1⟩
          | false => .none
    | false =>
      match Nat.beq sc.sizeBytes 0 with
      | true => .none
      | false =>
        let modulus := 2 ^ (8 * sc.sizeBytes)
        let canonical := sc.bits % modulus
        .some ⟨modulus - 1 - canonical, sc.sizeBytes⟩
  | .neg =>
    match Nat.beq sc.sizeBytes 0 with
    | true => .none
    | false =>
      let modulus := 2 ^ (8 * sc.sizeBytes)
      let canonical := sc.bits % modulus
      .some ⟨(modulus - canonical) % modulus, sc.sizeBytes⟩
  | .ptrMetadata => .none

/--
Pure integer cast evaluator (`CastKind.intToInt`) from `sc` to byte width
`dstBytes`, zero-extending or truncating when `srcIsSigned = false` and
sign-extending or truncating when `srcIsSigned = true`.
-/
@[reducible]
def evalCastValue
    (sc : ScalarValue)
    (dstBytes : Nat)
    (srcIsSigned : Bool := false) :
    Option ScalarValue :=
  match Bool.or (Nat.beq sc.sizeBytes 0) (Nat.beq dstBytes 0) with
  | true => .none
  | false =>
    let dstMod := 2 ^ (8 * dstBytes)
    let castedBits :=
      match srcIsSigned with
      | false => sc.bits % dstMod
      | true =>
        match Nat.ble dstBytes sc.sizeBytes with
        | true => sc.bits % dstMod
        | false => signExtendBits sc.bits sc.sizeBytes dstBytes
    .some ⟨castedBits, dstBytes⟩

/-! ## 7. Closed-Form `@[simp]` Lemmas for `evalBinOp` and `evalScalarBinOp` -/

@[simp]
theorem evalBinOp_bitAnd_apply {sz a b : Nat} (hsz : 0 < sz) (isSigned : Bool) :
    evalBinOp .bitAnd ⟨a, sz⟩ ⟨b, sz⟩ isSigned =
      .some ⟨(a &&& b) % (2 ^ (8 * sz)), sz⟩ := by
  unfold evalBinOp
  simp [beq_zero_eq_false_of_pos hsz]

@[simp]
theorem evalBinOp_bitOr_apply {sz a b : Nat} (hsz : 0 < sz) (isSigned : Bool) :
    evalBinOp .bitOr ⟨a, sz⟩ ⟨b, sz⟩ isSigned =
      .some ⟨(a ||| b) % (2 ^ (8 * sz)), sz⟩ := by
  unfold evalBinOp
  simp [beq_zero_eq_false_of_pos hsz]

@[simp]
theorem evalBinOp_bitXor_apply {sz a b : Nat} (hsz : 0 < sz) (isSigned : Bool) :
    evalBinOp .bitXor ⟨a, sz⟩ ⟨b, sz⟩ isSigned =
      .some ⟨(a ^^^ b) % (2 ^ (8 * sz)), sz⟩ := by
  unfold evalBinOp
  simp [beq_zero_eq_false_of_pos hsz]

@[simp]
theorem evalBinOp_shl_apply {szL szR a b : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR) (isSigned : Bool) :
    evalBinOp .shl ⟨a, szL⟩ ⟨b, szR⟩ isSigned =
      .some ⟨(a <<< (b % (8 * szL))) % (2 ^ (8 * szL)), szL⟩ := by
  unfold evalBinOp
  simp [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR]

@[simp]
theorem evalBinOp_shlUnchecked_apply {szL szR a b : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR) (hb : b < 8 * szL) (isSigned : Bool) :
    evalBinOp .shlUnchecked ⟨a, szL⟩ ⟨b, szR⟩ isSigned =
      .some ⟨(a <<< b) % (2 ^ (8 * szL)), szL⟩ := by
  unfold evalBinOp
  have hble : Nat.ble (8 * szL) b = false := by
    cases h : Nat.ble (8 * szL) b with
    | false => rfl
    | true => exact absurd (Nat.le_of_ble_eq_true h) (by omega)
  simp [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR, hble]

@[simp]
theorem evalBinOp_shr_unsigned {szL szR a b : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR) :
    evalBinOp .shr ⟨a, szL⟩ ⟨b, szR⟩ false =
      .some ⟨(a >>> (b % (8 * szL))) % (2 ^ (8 * szL)), szL⟩ := by
  unfold evalBinOp
  simp [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR]

@[simp]
theorem evalBinOp_shr_signed {szL szR a b : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR) :
    evalBinOp .shr ⟨a, szL⟩ ⟨b, szR⟩ true =
      .some ⟨((BitVec.ofNat (8 * szL) a).sshiftRight (b % (8 * szL))).toNat, szL⟩ := by
  unfold evalBinOp
  simp [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR]

@[simp]
theorem evalBinOp_shrUnchecked_unsigned {szL szR a b : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR) (hb : b < 8 * szL) :
    evalBinOp .shrUnchecked ⟨a, szL⟩ ⟨b, szR⟩ false =
      .some ⟨(a >>> b) % (2 ^ (8 * szL)), szL⟩ := by
  unfold evalBinOp
  have hble : Nat.ble (8 * szL) b = false := by
    cases h : Nat.ble (8 * szL) b with
    | false => rfl
    | true => exact absurd (Nat.le_of_ble_eq_true h) (by omega)
  simp [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR, hble]

@[simp]
theorem evalBinOp_shrUnchecked_signed {szL szR a b : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR) (hb : b < 8 * szL) :
    evalBinOp .shrUnchecked ⟨a, szL⟩ ⟨b, szR⟩ true =
      .some ⟨((BitVec.ofNat (8 * szL) a).sshiftRight b).toNat, szL⟩ := by
  unfold evalBinOp
  have hble : Nat.ble (8 * szL) b = false := by
    cases h : Nat.ble (8 * szL) b with
    | false => rfl
    | true => exact absurd (Nat.le_of_ble_eq_true h) (by omega)
  simp [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR, hble]

/-- Out-of-bounds unchecked left shift (`8 * szL ≤ b`) produces `.none` (UB). -/
@[simp]
theorem evalBinOp_shlUnchecked_of_ge {szL szR a b : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR) (hb : 8 * szL ≤ b) (isSigned : Bool) :
    evalBinOp .shlUnchecked ⟨a, szL⟩ ⟨b, szR⟩ isSigned = .none := by
  unfold evalBinOp
  simp [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR,
        Nat.ble_eq_true_of_le hb]

/-- Out-of-bounds unchecked right shift (`8 * szL ≤ b`) produces `.none` (UB). -/
@[simp]
theorem evalBinOp_shrUnchecked_of_ge {szL szR a b : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR) (hb : 8 * szL ≤ b) (isSigned : Bool) :
    evalBinOp .shrUnchecked ⟨a, szL⟩ ⟨b, szR⟩ isSigned = .none := by
  unfold evalBinOp
  simp [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR,
        Nat.ble_eq_true_of_le hb]

/-- Closed-form `@[simp]` lemmas for `evalCastValue` (unsigned and signed). -/
@[simp]
theorem evalCastValue_unsigned_apply {sz dstBytes a : Nat}
    (hsz : 0 < sz) (hdst : 0 < dstBytes) :
    evalCastValue ⟨a, sz⟩ dstBytes false =
      .some ⟨a % (2 ^ (8 * dstBytes)), dstBytes⟩ := by
  unfold evalCastValue
  simp [beq_zero_eq_false_of_pos hsz, beq_zero_eq_false_of_pos hdst]

/--
Unconditional closed-form `@[simp]` lemma for signed `evalCastValue`: for all
`0 < sz` and `0 < dstBytes` (both truncating `dstBytes ≤ sz` and widening
`sz < dstBytes`), `evalCastValue ⟨a, sz⟩ dstBytes true` equals
`.some ⟨((BitVec.ofNat (8 * sz) a).signExtend (8 * dstBytes)).toNat, dstBytes⟩`.
-/
@[simp]
theorem evalCastValue_signed_apply {sz dstBytes a : Nat}
    (hsz : 0 < sz) (hdst : 0 < dstBytes) :
    evalCastValue ⟨a, sz⟩ dstBytes true =
      .some ⟨((BitVec.ofNat (8 * sz) a).signExtend (8 * dstBytes)).toNat, dstBytes⟩ := by
  unfold evalCastValue
  simp only [beq_zero_eq_false_of_pos hsz, beq_zero_eq_false_of_pos hdst, Bool.or_false]
  cases h : Nat.ble dstBytes sz with
  | true =>
    have hle := Nat.le_of_ble_eq_true h
    dsimp only
    congr 1; congr 1
    exact (toNat_signExtend_ofNat_of_le (by omega) a).symm
  | false =>
    simp only [signExtendBits_eq_bitVec]

/-- When `dstBytes ≤ sz`, signed `evalCastValue` truncates to `a % 2 ^ (8 * dstBytes)`. -/
theorem evalCastValue_signed_of_le {sz dstBytes a : Nat}
    (hsz : 0 < sz) (hdst : 0 < dstBytes) (hle : dstBytes ≤ sz) :
    evalCastValue ⟨a, sz⟩ dstBytes true =
      .some ⟨a % (2 ^ (8 * dstBytes)), dstBytes⟩ := by
  rw [evalCastValue_signed_apply hsz hdst, toNat_signExtend_ofNat_of_le (by omega)]

/-- Concrete width-specialized `@[simp]` lemmas for `u8`, `u16`, `u32`, `u64`, `u128`, `usize`, and `i8`, `i16`, `i32`, `i64`, `i128`, `isize`. -/
@[simp] theorem evalBinOp_bitAnd_u8 (a b : Nat) (s : Bool) :
    evalBinOp .bitAnd ⟨a, 1⟩ ⟨b, 1⟩ s = .some ⟨(a &&& b) % 256, 1⟩ := rfl
@[simp] theorem evalBinOp_bitAnd_u16 (a b : Nat) (s : Bool) :
    evalBinOp .bitAnd ⟨a, 2⟩ ⟨b, 2⟩ s = .some ⟨(a &&& b) % 65536, 2⟩ := rfl
@[simp] theorem evalBinOp_bitAnd_u32 (a b : Nat) (s : Bool) :
    evalBinOp .bitAnd ⟨a, 4⟩ ⟨b, 4⟩ s = .some ⟨(a &&& b) % 4294967296, 4⟩ := rfl
@[simp] theorem evalBinOp_bitAnd_u64 (a b : Nat) (s : Bool) :
    evalBinOp .bitAnd ⟨a, 8⟩ ⟨b, 8⟩ s = .some ⟨(a &&& b) % 18446744073709551616, 8⟩ := rfl
@[simp] theorem evalBinOp_bitAnd_u128 (a b : Nat) (s : Bool) :
    evalBinOp .bitAnd ⟨a, 16⟩ ⟨b, 16⟩ s = .some ⟨(a &&& b) % (2 ^ 128), 16⟩ := rfl
@[simp] theorem evalBinOp_bitAnd_usize (a b : Nat) (s : Bool) :
    evalBinOp .bitAnd ⟨a, 8⟩ ⟨b, 8⟩ s = .some ⟨(a &&& b) % 18446744073709551616, 8⟩ := rfl

@[simp] theorem evalBinOp_bitOr_u8 (a b : Nat) (s : Bool) :
    evalBinOp .bitOr ⟨a, 1⟩ ⟨b, 1⟩ s = .some ⟨(a ||| b) % 256, 1⟩ := rfl
@[simp] theorem evalBinOp_bitOr_u16 (a b : Nat) (s : Bool) :
    evalBinOp .bitOr ⟨a, 2⟩ ⟨b, 2⟩ s = .some ⟨(a ||| b) % 65536, 2⟩ := rfl
@[simp] theorem evalBinOp_bitOr_u32 (a b : Nat) (s : Bool) :
    evalBinOp .bitOr ⟨a, 4⟩ ⟨b, 4⟩ s = .some ⟨(a ||| b) % 4294967296, 4⟩ := rfl
@[simp] theorem evalBinOp_bitOr_u64 (a b : Nat) (s : Bool) :
    evalBinOp .bitOr ⟨a, 8⟩ ⟨b, 8⟩ s = .some ⟨(a ||| b) % 18446744073709551616, 8⟩ := rfl
@[simp] theorem evalBinOp_bitOr_u128 (a b : Nat) (s : Bool) :
    evalBinOp .bitOr ⟨a, 16⟩ ⟨b, 16⟩ s = .some ⟨(a ||| b) % (2 ^ 128), 16⟩ := rfl
@[simp] theorem evalBinOp_bitOr_usize (a b : Nat) (s : Bool) :
    evalBinOp .bitOr ⟨a, 8⟩ ⟨b, 8⟩ s = .some ⟨(a ||| b) % 18446744073709551616, 8⟩ := rfl

@[simp] theorem evalBinOp_bitXor_u8 (a b : Nat) (s : Bool) :
    evalBinOp .bitXor ⟨a, 1⟩ ⟨b, 1⟩ s = .some ⟨(a ^^^ b) % 256, 1⟩ := rfl
@[simp] theorem evalBinOp_bitXor_u16 (a b : Nat) (s : Bool) :
    evalBinOp .bitXor ⟨a, 2⟩ ⟨b, 2⟩ s = .some ⟨(a ^^^ b) % 65536, 2⟩ := rfl
@[simp] theorem evalBinOp_bitXor_u32 (a b : Nat) (s : Bool) :
    evalBinOp .bitXor ⟨a, 4⟩ ⟨b, 4⟩ s = .some ⟨(a ^^^ b) % 4294967296, 4⟩ := rfl
@[simp] theorem evalBinOp_bitXor_u64 (a b : Nat) (s : Bool) :
    evalBinOp .bitXor ⟨a, 8⟩ ⟨b, 8⟩ s = .some ⟨(a ^^^ b) % 18446744073709551616, 8⟩ := rfl
@[simp] theorem evalBinOp_bitXor_u128 (a b : Nat) (s : Bool) :
    evalBinOp .bitXor ⟨a, 16⟩ ⟨b, 16⟩ s = .some ⟨(a ^^^ b) % (2 ^ 128), 16⟩ := rfl
@[simp] theorem evalBinOp_bitXor_usize (a b : Nat) (s : Bool) :
    evalBinOp .bitXor ⟨a, 8⟩ ⟨b, 8⟩ s = .some ⟨(a ^^^ b) % 18446744073709551616, 8⟩ := rfl

@[simp] theorem evalBinOp_shl_u8 (a b : Nat) (szR : Nat) (hR : 0 < szR) (s : Bool) :
    evalBinOp .shl ⟨a, 1⟩ ⟨b, szR⟩ s = .some ⟨(a <<< (b % 8)) % 256, 1⟩ :=
  evalBinOp_shl_apply (by decide) hR s
@[simp] theorem evalBinOp_shl_u16 (a b : Nat) (szR : Nat) (hR : 0 < szR) (s : Bool) :
    evalBinOp .shl ⟨a, 2⟩ ⟨b, szR⟩ s = .some ⟨(a <<< (b % 16)) % 65536, 2⟩ :=
  evalBinOp_shl_apply (by decide) hR s
@[simp] theorem evalBinOp_shl_u32 (a b : Nat) (szR : Nat) (hR : 0 < szR) (s : Bool) :
    evalBinOp .shl ⟨a, 4⟩ ⟨b, szR⟩ s = .some ⟨(a <<< (b % 32)) % 4294967296, 4⟩ :=
  evalBinOp_shl_apply (by decide) hR s
@[simp] theorem evalBinOp_shl_u64 (a b : Nat) (szR : Nat) (hR : 0 < szR) (s : Bool) :
    evalBinOp .shl ⟨a, 8⟩ ⟨b, szR⟩ s = .some ⟨(a <<< (b % 64)) % 18446744073709551616, 8⟩ :=
  evalBinOp_shl_apply (by decide) hR s
@[simp] theorem evalBinOp_shl_u128 (a b : Nat) (szR : Nat) (hR : 0 < szR) (s : Bool) :
    evalBinOp .shl ⟨a, 16⟩ ⟨b, szR⟩ s = .some ⟨(a <<< (b % 128)) % (2 ^ 128), 16⟩ :=
  evalBinOp_shl_apply (by decide) hR s
@[simp] theorem evalBinOp_shl_usize (a b : Nat) (szR : Nat) (hR : 0 < szR) (s : Bool) :
    evalBinOp .shl ⟨a, 8⟩ ⟨b, szR⟩ s = .some ⟨(a <<< (b % 64)) % 18446744073709551616, 8⟩ :=
  evalBinOp_shl_u64 a b szR hR s

@[simp] theorem evalBinOp_shr_u8 (a b : Nat) (szR : Nat) (hR : 0 < szR) :
    evalBinOp .shr ⟨a, 1⟩ ⟨b, szR⟩ false = .some ⟨(a >>> (b % 8)) % 256, 1⟩ :=
  evalBinOp_shr_unsigned (by decide) hR
@[simp] theorem evalBinOp_shr_u16 (a b : Nat) (szR : Nat) (hR : 0 < szR) :
    evalBinOp .shr ⟨a, 2⟩ ⟨b, szR⟩ false = .some ⟨(a >>> (b % 16)) % 65536, 2⟩ :=
  evalBinOp_shr_unsigned (by decide) hR
@[simp] theorem evalBinOp_shr_u32 (a b : Nat) (szR : Nat) (hR : 0 < szR) :
    evalBinOp .shr ⟨a, 4⟩ ⟨b, szR⟩ false = .some ⟨(a >>> (b % 32)) % 4294967296, 4⟩ :=
  evalBinOp_shr_unsigned (by decide) hR
@[simp] theorem evalBinOp_shr_u64 (a b : Nat) (szR : Nat) (hR : 0 < szR) :
    evalBinOp .shr ⟨a, 8⟩ ⟨b, szR⟩ false = .some ⟨(a >>> (b % 64)) % 18446744073709551616, 8⟩ :=
  evalBinOp_shr_unsigned (by decide) hR
@[simp] theorem evalBinOp_shr_u128 (a b : Nat) (szR : Nat) (hR : 0 < szR) :
    evalBinOp .shr ⟨a, 16⟩ ⟨b, szR⟩ false = .some ⟨(a >>> (b % 128)) % (2 ^ 128), 16⟩ :=
  evalBinOp_shr_unsigned (by decide) hR
@[simp] theorem evalBinOp_shr_usize (a b : Nat) (szR : Nat) (hR : 0 < szR) :
    evalBinOp .shr ⟨a, 8⟩ ⟨b, szR⟩ false = .some ⟨(a >>> (b % 64)) % 18446744073709551616, 8⟩ :=
  evalBinOp_shr_u64 a b szR hR

@[simp] theorem evalBinOp_shr_i8 (a b : Nat) (szR : Nat) (hR : 0 < szR) :
    evalBinOp .shr ⟨a, 1⟩ ⟨b, szR⟩ true =
      .some ⟨((BitVec.ofNat 8 a).sshiftRight (b % 8)).toNat, 1⟩ :=
  evalBinOp_shr_signed (by decide) hR
@[simp] theorem evalBinOp_shr_i16 (a b : Nat) (szR : Nat) (hR : 0 < szR) :
    evalBinOp .shr ⟨a, 2⟩ ⟨b, szR⟩ true =
      .some ⟨((BitVec.ofNat 16 a).sshiftRight (b % 16)).toNat, 2⟩ :=
  evalBinOp_shr_signed (by decide) hR
@[simp] theorem evalBinOp_shr_i32 (a b : Nat) (szR : Nat) (hR : 0 < szR) :
    evalBinOp .shr ⟨a, 4⟩ ⟨b, szR⟩ true =
      .some ⟨((BitVec.ofNat 32 a).sshiftRight (b % 32)).toNat, 4⟩ :=
  evalBinOp_shr_signed (by decide) hR
@[simp] theorem evalBinOp_shr_i64 (a b : Nat) (szR : Nat) (hR : 0 < szR) :
    evalBinOp .shr ⟨a, 8⟩ ⟨b, szR⟩ true =
      .some ⟨((BitVec.ofNat 64 a).sshiftRight (b % 64)).toNat, 8⟩ :=
  evalBinOp_shr_signed (by decide) hR
@[simp] theorem evalBinOp_shr_i128 (a b : Nat) (szR : Nat) (hR : 0 < szR) :
    evalBinOp .shr ⟨a, 16⟩ ⟨b, szR⟩ true =
      .some ⟨((BitVec.ofNat 128 a).sshiftRight (b % 128)).toNat, 16⟩ :=
  evalBinOp_shr_signed (by decide) hR
@[simp] theorem evalBinOp_shr_isize (a b : Nat) (szR : Nat) (hR : 0 < szR) :
    evalBinOp .shr ⟨a, 8⟩ ⟨b, szR⟩ true =
      .some ⟨((BitVec.ofNat 64 a).sshiftRight (b % 64)).toNat, 8⟩ :=
  evalBinOp_shr_i64 a b szR hR

@[simp] theorem evalBinOp_shlUnchecked_u8 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 8) (s : Bool) :
    evalBinOp .shlUnchecked ⟨a, 1⟩ ⟨b, szR⟩ s = .some ⟨(a <<< b) % 256, 1⟩ :=
  evalBinOp_shlUnchecked_apply (by decide) hR hb s
@[simp] theorem evalBinOp_shlUnchecked_u16 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 16) (s : Bool) :
    evalBinOp .shlUnchecked ⟨a, 2⟩ ⟨b, szR⟩ s = .some ⟨(a <<< b) % 65536, 2⟩ :=
  evalBinOp_shlUnchecked_apply (by decide) hR hb s
@[simp] theorem evalBinOp_shlUnchecked_u32 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 32) (s : Bool) :
    evalBinOp .shlUnchecked ⟨a, 4⟩ ⟨b, szR⟩ s = .some ⟨(a <<< b) % 4294967296, 4⟩ :=
  evalBinOp_shlUnchecked_apply (by decide) hR hb s
@[simp] theorem evalBinOp_shlUnchecked_u64 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 64) (s : Bool) :
    evalBinOp .shlUnchecked ⟨a, 8⟩ ⟨b, szR⟩ s = .some ⟨(a <<< b) % 18446744073709551616, 8⟩ :=
  evalBinOp_shlUnchecked_apply (by decide) hR hb s
@[simp] theorem evalBinOp_shlUnchecked_u128 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 128) (s : Bool) :
    evalBinOp .shlUnchecked ⟨a, 16⟩ ⟨b, szR⟩ s = .some ⟨(a <<< b) % (2 ^ 128), 16⟩ :=
  evalBinOp_shlUnchecked_apply (by decide) hR hb s
@[simp] theorem evalBinOp_shlUnchecked_usize (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 64) (s : Bool) :
    evalBinOp .shlUnchecked ⟨a, 8⟩ ⟨b, szR⟩ s = .some ⟨(a <<< b) % 18446744073709551616, 8⟩ :=
  evalBinOp_shlUnchecked_u64 a b szR hR hb s

@[simp] theorem evalBinOp_shrUnchecked_u8 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 8) :
    evalBinOp .shrUnchecked ⟨a, 1⟩ ⟨b, szR⟩ false = .some ⟨(a >>> b) % 256, 1⟩ :=
  evalBinOp_shrUnchecked_unsigned (by decide) hR hb
@[simp] theorem evalBinOp_shrUnchecked_u16 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 16) :
    evalBinOp .shrUnchecked ⟨a, 2⟩ ⟨b, szR⟩ false = .some ⟨(a >>> b) % 65536, 2⟩ :=
  evalBinOp_shrUnchecked_unsigned (by decide) hR hb
@[simp] theorem evalBinOp_shrUnchecked_u32 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 32) :
    evalBinOp .shrUnchecked ⟨a, 4⟩ ⟨b, szR⟩ false = .some ⟨(a >>> b) % 4294967296, 4⟩ :=
  evalBinOp_shrUnchecked_unsigned (by decide) hR hb
@[simp] theorem evalBinOp_shrUnchecked_u64 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 64) :
    evalBinOp .shrUnchecked ⟨a, 8⟩ ⟨b, szR⟩ false = .some ⟨(a >>> b) % 18446744073709551616, 8⟩ :=
  evalBinOp_shrUnchecked_unsigned (by decide) hR hb
@[simp] theorem evalBinOp_shrUnchecked_u128 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 128) :
    evalBinOp .shrUnchecked ⟨a, 16⟩ ⟨b, szR⟩ false = .some ⟨(a >>> b) % (2 ^ 128), 16⟩ :=
  evalBinOp_shrUnchecked_unsigned (by decide) hR hb
@[simp] theorem evalBinOp_shrUnchecked_usize (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 64) :
    evalBinOp .shrUnchecked ⟨a, 8⟩ ⟨b, szR⟩ false = .some ⟨(a >>> b) % 18446744073709551616, 8⟩ :=
  evalBinOp_shrUnchecked_u64 a b szR hR hb

@[simp] theorem evalBinOp_shrUnchecked_i8 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 8) :
    evalBinOp .shrUnchecked ⟨a, 1⟩ ⟨b, szR⟩ true = .some ⟨((BitVec.ofNat 8 a).sshiftRight b).toNat, 1⟩ :=
  evalBinOp_shrUnchecked_signed (by decide) hR hb
@[simp] theorem evalBinOp_shrUnchecked_i16 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 16) :
    evalBinOp .shrUnchecked ⟨a, 2⟩ ⟨b, szR⟩ true = .some ⟨((BitVec.ofNat 16 a).sshiftRight b).toNat, 2⟩ :=
  evalBinOp_shrUnchecked_signed (by decide) hR hb
@[simp] theorem evalBinOp_shrUnchecked_i32 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 32) :
    evalBinOp .shrUnchecked ⟨a, 4⟩ ⟨b, szR⟩ true = .some ⟨((BitVec.ofNat 32 a).sshiftRight b).toNat, 4⟩ :=
  evalBinOp_shrUnchecked_signed (by decide) hR hb
@[simp] theorem evalBinOp_shrUnchecked_i64 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 64) :
    evalBinOp .shrUnchecked ⟨a, 8⟩ ⟨b, szR⟩ true = .some ⟨((BitVec.ofNat 64 a).sshiftRight b).toNat, 8⟩ :=
  evalBinOp_shrUnchecked_signed (by decide) hR hb
@[simp] theorem evalBinOp_shrUnchecked_i128 (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 128) :
    evalBinOp .shrUnchecked ⟨a, 16⟩ ⟨b, szR⟩ true = .some ⟨((BitVec.ofNat 128 a).sshiftRight b).toNat, 16⟩ :=
  evalBinOp_shrUnchecked_signed (by decide) hR hb
@[simp] theorem evalBinOp_shrUnchecked_isize (a b : Nat) (szR : Nat) (hR : 0 < szR) (hb : b < 64) :
    evalBinOp .shrUnchecked ⟨a, 8⟩ ⟨b, szR⟩ true = .some ⟨((BitVec.ofNat 64 a).sshiftRight b).toNat, 8⟩ :=
  evalBinOp_shrUnchecked_i64 a b szR hR hb

@[simp] theorem evalCastValue_u8 (a dstBytes : Nat) (hdst : 0 < dstBytes) :
    evalCastValue ⟨a, 1⟩ dstBytes false = .some ⟨a % (2 ^ (8 * dstBytes)), dstBytes⟩ :=
  evalCastValue_unsigned_apply (by decide) hdst
@[simp] theorem evalCastValue_u16 (a dstBytes : Nat) (hdst : 0 < dstBytes) :
    evalCastValue ⟨a, 2⟩ dstBytes false = .some ⟨a % (2 ^ (8 * dstBytes)), dstBytes⟩ :=
  evalCastValue_unsigned_apply (by decide) hdst
@[simp] theorem evalCastValue_u32 (a dstBytes : Nat) (hdst : 0 < dstBytes) :
    evalCastValue ⟨a, 4⟩ dstBytes false = .some ⟨a % (2 ^ (8 * dstBytes)), dstBytes⟩ :=
  evalCastValue_unsigned_apply (by decide) hdst
@[simp] theorem evalCastValue_u64 (a dstBytes : Nat) (hdst : 0 < dstBytes) :
    evalCastValue ⟨a, 8⟩ dstBytes false = .some ⟨a % (2 ^ (8 * dstBytes)), dstBytes⟩ :=
  evalCastValue_unsigned_apply (by decide) hdst
@[simp] theorem evalCastValue_u128 (a dstBytes : Nat) (hdst : 0 < dstBytes) :
    evalCastValue ⟨a, 16⟩ dstBytes false = .some ⟨a % (2 ^ (8 * dstBytes)), dstBytes⟩ :=
  evalCastValue_unsigned_apply (by decide) hdst
@[simp] theorem evalCastValue_usize (a dstBytes : Nat) (hdst : 0 < dstBytes) :
    evalCastValue ⟨a, 8⟩ dstBytes false = .some ⟨a % (2 ^ (8 * dstBytes)), dstBytes⟩ :=
  evalCastValue_u64 a dstBytes hdst

@[simp] theorem evalCastValue_i8 (a dstBytes : Nat) (hdst : 0 < dstBytes) :
    evalCastValue ⟨a, 1⟩ dstBytes true =
      .some ⟨((BitVec.ofNat 8 a).signExtend (8 * dstBytes)).toNat, dstBytes⟩ :=
  evalCastValue_signed_apply (by decide) hdst
@[simp] theorem evalCastValue_i16 (a dstBytes : Nat) (hdst : 0 < dstBytes) :
    evalCastValue ⟨a, 2⟩ dstBytes true =
      .some ⟨((BitVec.ofNat 16 a).signExtend (8 * dstBytes)).toNat, dstBytes⟩ :=
  evalCastValue_signed_apply (by decide) hdst
@[simp] theorem evalCastValue_i32 (a dstBytes : Nat) (hdst : 0 < dstBytes) :
    evalCastValue ⟨a, 4⟩ dstBytes true =
      .some ⟨((BitVec.ofNat 32 a).signExtend (8 * dstBytes)).toNat, dstBytes⟩ :=
  evalCastValue_signed_apply (by decide) hdst
@[simp] theorem evalCastValue_i64 (a dstBytes : Nat) (hdst : 0 < dstBytes) :
    evalCastValue ⟨a, 8⟩ dstBytes true =
      .some ⟨((BitVec.ofNat 64 a).signExtend (8 * dstBytes)).toNat, dstBytes⟩ :=
  evalCastValue_signed_apply (by decide) hdst
@[simp] theorem evalCastValue_i128 (a dstBytes : Nat) (hdst : 0 < dstBytes) :
    evalCastValue ⟨a, 16⟩ dstBytes true =
      .some ⟨((BitVec.ofNat 128 a).signExtend (8 * dstBytes)).toNat, dstBytes⟩ :=
  evalCastValue_signed_apply (by decide) hdst
@[simp] theorem evalCastValue_isize (a dstBytes : Nat) (hdst : 0 < dstBytes) :
    evalCastValue ⟨a, 8⟩ dstBytes true =
      .some ⟨((BitVec.ofNat 64 a).signExtend (8 * dstBytes)).toNat, dstBytes⟩ :=
  evalCastValue_i64 a dstBytes hdst

/--
Exact operational correspondence between `Trusted.MirSemantics.evalScalarBinOp`
and `evalBinOp` across `.bitAnd`, `.bitOr`, `.bitXor`, `.shl`, `.shr`,
`.shlUnchecked`, and `.shrUnchecked`.
-/
@[simp]
theorem evalScalarBinOp_bitAnd {sz a b : Nat} (hsz : 0 < sz)
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp .bitAnd ⟨a, sz⟩ ⟨b, sz⟩ locals mem isSigned =
      .ok (.scalar ⟨(a &&& b) % (2 ^ (8 * sz)), sz⟩) locals mem := by
  unfold evalScalarBinOp
  have hmul8 : sz.mul 8 = 8 * sz := Nat.mul_comm sz 8
  simp only [beq_zero_eq_false_of_pos hsz, Nat.beq_refl, bitwiseAndBits_eq_land, hmul8]

@[simp]
theorem evalScalarBinOp_bitOr {sz a b : Nat} (hsz : 0 < sz)
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp .bitOr ⟨a, sz⟩ ⟨b, sz⟩ locals mem isSigned =
      .ok (.scalar ⟨(a ||| b) % (2 ^ (8 * sz)), sz⟩) locals mem := by
  unfold evalScalarBinOp
  have hmul8 : sz.mul 8 = 8 * sz := Nat.mul_comm sz 8
  simp only [beq_zero_eq_false_of_pos hsz, Nat.beq_refl, bitwiseOrBits_eq_lor, hmul8]

@[simp]
theorem evalScalarBinOp_bitXor {sz a b : Nat} (hsz : 0 < sz)
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp .bitXor ⟨a, sz⟩ ⟨b, sz⟩ locals mem isSigned =
      .ok (.scalar ⟨(a ^^^ b) % (2 ^ (8 * sz)), sz⟩) locals mem := by
  unfold evalScalarBinOp
  have hmul8 : sz.mul 8 = 8 * sz := Nat.mul_comm sz 8
  simp only [beq_zero_eq_false_of_pos hsz, Nat.beq_refl, bitwiseXorBits_eq_xor, hmul8]

@[simp]
theorem evalScalarBinOp_shl {szL szR a b : Nat} (hszL : 0 < szL) (hszR : 0 < szR)
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp .shl ⟨a, szL⟩ ⟨b, szR⟩ locals mem isSigned =
      .ok (.scalar ⟨(a <<< (b % (8 * szL))) % (2 ^ (8 * szL)), szL⟩) locals mem := by
  unfold evalScalarBinOp
  simp only [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR,
             shiftLeftBits_eq_shiftLeft_mod]
  congr 2; congr 1
  change (a <<< (b % (szL * 8))) % 2 ^ (8 * szL) = (a <<< (b % (8 * szL))) % 2 ^ (8 * szL)
  rw [Nat.mul_comm szL 8]

@[simp]
theorem evalScalarBinOp_shr_unsigned {szL szR a b : Nat} (hszL : 0 < szL) (hszR : 0 < szR)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .shr ⟨a, szL⟩ ⟨b, szR⟩ locals mem false =
      .ok (.scalar ⟨(a >>> (b % (8 * szL))) % (2 ^ (8 * szL)), szL⟩) locals mem := by
  unfold evalScalarBinOp
  simp only [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR,
             shiftRightUnsignedBits_eq_shiftRight, wrapScalarBits_eq_mod_modulus,
             scalarModulus_eq_two_pow]
  congr 2; congr 1
  change (a >>> (b % (szL * 8))) % 2 ^ (8 * szL) = (a >>> (b % (8 * szL))) % 2 ^ (8 * szL)
  rw [Nat.mul_comm szL 8]

@[simp]
theorem evalScalarBinOp_shr_signed {szL szR a b : Nat} (hszL : 0 < szL) (hszR : 0 < szR)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .shr ⟨a, szL⟩ ⟨b, szR⟩ locals mem true =
      .ok (.scalar ⟨((BitVec.ofNat (8 * szL) a).sshiftRight (b % (8 * szL))).toNat, szL⟩)
        locals mem := by
  unfold evalScalarBinOp
  simp only [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR]
  congr 2; congr 1
  exact arithmeticShrBits_mod_eq_sshiftRight hszL

@[simp]
theorem evalScalarBinOp_shlUnchecked {szL szR a b : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR) (hb : b < 8 * szL)
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp .shlUnchecked ⟨a, szL⟩ ⟨b, szR⟩ locals mem isSigned =
      .ok (.scalar ⟨(a <<< b) % (2 ^ (8 * szL)), szL⟩) locals mem := by
  unfold evalScalarBinOp
  have hble : Nat.ble (Nat.mul szL 8) b = false := by
    cases h : Nat.ble (Nat.mul szL 8) b with
    | false => rfl
    | true =>
      have hle := Nat.le_of_ble_eq_true h
      change szL * 8 ≤ b at hle
      omega
  simp only [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR,
             hble, shiftLeftBits_eq_shiftLeft_mod]

@[simp]
theorem evalScalarBinOp_shrUnchecked_unsigned {szL szR a b : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR) (hb : b < 8 * szL)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .shrUnchecked ⟨a, szL⟩ ⟨b, szR⟩ locals mem false =
      .ok (.scalar ⟨(a >>> b) % (2 ^ (8 * szL)), szL⟩) locals mem := by
  unfold evalScalarBinOp
  have hble : Nat.ble (Nat.mul szL 8) b = false := by
    cases h : Nat.ble (Nat.mul szL 8) b with
    | false => rfl
    | true =>
      have hle := Nat.le_of_ble_eq_true h
      change szL * 8 ≤ b at hle
      omega
  simp only [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR,
             hble, shiftRightUnsignedBits_eq_shiftRight,
             wrapScalarBits_eq_mod_modulus, scalarModulus_eq_two_pow]

@[simp]
theorem evalScalarBinOp_shrUnchecked_signed {szL szR a b : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR) (hb : b < 8 * szL)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .shrUnchecked ⟨a, szL⟩ ⟨b, szR⟩ locals mem true =
      .ok (.scalar ⟨((BitVec.ofNat (8 * szL) a).sshiftRight b).toNat, szL⟩)
        locals mem := by
  unfold evalScalarBinOp
  have hble : Nat.ble (Nat.mul szL 8) b = false := by
    cases h : Nat.ble (Nat.mul szL 8) b with
    | false => rfl
    | true =>
      have hle := Nat.le_of_ble_eq_true h
      change szL * 8 ≤ b at hle
      omega
  simp only [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR,
             hble, arithmeticShrBits_eq_sshiftRight hszL (Nat.le_of_lt hb)]

/-- Out-of-bounds unchecked left shift (`8 * szL ≤ b`) produces `.ub` in `evalScalarBinOp`. -/
@[simp]
theorem evalScalarBinOp_shlUnchecked_of_ge {szL szR a b : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR) (hb : 8 * szL ≤ b)
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp .shlUnchecked ⟨a, szL⟩ ⟨b, szR⟩ locals mem isSigned = .ub := by
  unfold evalScalarBinOp
  have hble : Nat.ble (Nat.mul szL 8) b = true := by
    apply Nat.ble_eq_true_of_le
    change szL * 8 ≤ b
    omega
  simp only [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR, hble]

/-- Out-of-bounds unchecked right shift (`8 * szL ≤ b`) produces `.ub` in `evalScalarBinOp`. -/
@[simp]
theorem evalScalarBinOp_shrUnchecked_of_ge {szL szR a b : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR) (hb : 8 * szL ≤ b)
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp .shrUnchecked ⟨a, szL⟩ ⟨b, szR⟩ locals mem isSigned = .ub := by
  unfold evalScalarBinOp
  have hble : Nat.ble (Nat.mul szL 8) b = true := by
    apply Nat.ble_eq_true_of_le
    change szL * 8 ≤ b
    omega
  simp only [beq_zero_eq_false_of_pos hszL, beq_zero_eq_false_of_pos hszR, hble]

/-- Closed-form `@[simp]` lemmas for `evalExactDiv` and `evalScalarExactDiv` (`BRIEF-1.2`). -/
@[simp]
theorem evalExactDiv_unsigned_apply {sz a b : Nat}
    (hsz : 0 < sz) (hb : b % (2 ^ (8 * sz)) ≠ 0)
    (hdiv : (a % (2 ^ (8 * sz))) % (b % (2 ^ (8 * sz))) = 0) :
    evalExactDiv ⟨a, sz⟩ ⟨b, sz⟩ false =
      .some ⟨(a % (2 ^ (8 * sz))) / (b % (2 ^ (8 * sz))), sz⟩ := by
  unfold evalExactDiv
  have hb_beq : Nat.beq (b % (2 ^ (8 * sz))) 0 = false := by
    cases h : Nat.beq (b % (2 ^ (8 * sz))) 0 with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true h) hb
  have hmod_beq : Nat.beq (Nat.mod (a % (2 ^ (8 * sz))) (b % (2 ^ (8 * sz)))) 0 = true := by
    change Nat.beq ((a % (2 ^ (8 * sz))) % (b % (2 ^ (8 * sz)))) 0 = true
    rw [hdiv]
    rfl
  simp [beq_zero_eq_false_of_pos hsz, hb_beq, hmod_beq]
  rfl

@[simp]
theorem evalExactDiv_zero_right {sz a : Nat} (hsz : 0 < sz) (isSigned : Bool) :
    evalExactDiv ⟨a, sz⟩ ⟨0, sz⟩ isSigned = .none := by
  unfold evalExactDiv
  simp [beq_zero_eq_false_of_pos hsz]

@[simp]
theorem evalScalarExactDiv_unsigned_apply {sz a b : Nat}
    (hsz : 0 < sz) (hb : b % (2 ^ (8 * sz)) ≠ 0)
    (hdiv : (a % (2 ^ (8 * sz))) % (b % (2 ^ (8 * sz))) = 0)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarExactDiv ⟨a, sz⟩ ⟨b, sz⟩ locals mem false =
      .ok (.scalar ⟨(a % (2 ^ (8 * sz))) / (b % (2 ^ (8 * sz))), sz⟩) locals mem := by
  unfold evalScalarExactDiv
  rw [evalExactDiv_unsigned_apply hsz hb hdiv]

@[simp]
theorem evalScalarExactDiv_zero_right {sz a : Nat} (hsz : 0 < sz)
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarExactDiv ⟨a, sz⟩ ⟨0, sz⟩ locals mem isSigned = .ub := by
  unfold evalScalarExactDiv
  rw [evalExactDiv_zero_right hsz]

/-! ## 8. `BitVec (8 * sz)` Homomorphism Theorems for `evalBinOp`, `evalBinOpChecked`, `evalUnOp`, and `evalCastValue` -/

/-- `evalBinOp .bitAnd` commutes with `ScalarValue.ofBitVec` and `BitVec.and` (`&&&`). -/
@[simp]
theorem evalBinOp_ofBitVec_bitAnd {sz : Nat} (hsz : 0 < sz)
    (x y : BitVec (8 * sz)) (isSigned : Bool) :
    evalBinOp .bitAnd (ScalarValue.ofBitVec sz x) (ScalarValue.ofBitVec sz y) isSigned =
      .some (ScalarValue.ofBitVec sz (x &&& y)) := by
  rw [evalBinOp_bitAnd_apply hsz]
  unfold ScalarValue.ofBitVec
  congr 1; congr 1
  rw [← BitVec.toNat_and, Nat.mod_eq_of_lt (x &&& y).isLt]

/-- `evalBinOp .bitOr` commutes with `ScalarValue.ofBitVec` and `BitVec.or` (`|||`). -/
@[simp]
theorem evalBinOp_ofBitVec_bitOr {sz : Nat} (hsz : 0 < sz)
    (x y : BitVec (8 * sz)) (isSigned : Bool) :
    evalBinOp .bitOr (ScalarValue.ofBitVec sz x) (ScalarValue.ofBitVec sz y) isSigned =
      .some (ScalarValue.ofBitVec sz (x ||| y)) := by
  rw [evalBinOp_bitOr_apply hsz]
  unfold ScalarValue.ofBitVec
  congr 1; congr 1
  rw [← BitVec.toNat_or, Nat.mod_eq_of_lt (x ||| y).isLt]

/-- `evalBinOp .bitXor` commutes with `ScalarValue.ofBitVec` and `BitVec.xor` (`^^^`). -/
@[simp]
theorem evalBinOp_ofBitVec_bitXor {sz : Nat} (hsz : 0 < sz)
    (x y : BitVec (8 * sz)) (isSigned : Bool) :
    evalBinOp .bitXor (ScalarValue.ofBitVec sz x) (ScalarValue.ofBitVec sz y) isSigned =
      .some (ScalarValue.ofBitVec sz (x ^^^ y)) := by
  rw [evalBinOp_bitXor_apply hsz]
  unfold ScalarValue.ofBitVec
  congr 1; congr 1
  rw [← BitVec.toNat_xor, Nat.mod_eq_of_lt (x ^^^ y).isLt]

/-- `evalBinOp .shl` commutes with `ScalarValue.ofBitVec` and `BitVec.shiftLeft` (`<<<`). -/
@[simp]
theorem evalBinOp_ofBitVec_shl {szL szR : Nat} (hszL : 0 < szL) (hszR : 0 < szR)
    (x : BitVec (8 * szL)) (y : BitVec (8 * szR)) (isSigned : Bool) :
    evalBinOp .shl (ScalarValue.ofBitVec szL x) (ScalarValue.ofBitVec szR y) isSigned =
      .some (ScalarValue.ofBitVec szL (x <<< (y.toNat % (8 * szL)))) := by
  rw [evalBinOp_shl_apply hszL hszR]
  rfl

/-- `evalBinOp .shr` (unsigned) commutes with `ScalarValue.ofBitVec` and `BitVec.ushiftRight` (`>>>`). -/
@[simp]
theorem evalBinOp_ofBitVec_shr_unsigned {szL szR : Nat} (hszL : 0 < szL) (hszR : 0 < szR)
    (x : BitVec (8 * szL)) (y : BitVec (8 * szR)) :
    evalBinOp .shr (ScalarValue.ofBitVec szL x) (ScalarValue.ofBitVec szR y) false =
      .some (ScalarValue.ofBitVec szL (x >>> (y.toNat % (8 * szL)))) := by
  rw [evalBinOp_shr_unsigned hszL hszR]
  unfold ScalarValue.ofBitVec
  congr 1; congr 1
  rw [← BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt (x >>> (y.toNat % (8 * szL))).isLt]

/-- `evalBinOp .shr` (signed) commutes with `ScalarValue.ofBitVec` and `BitVec.sshiftRight`. -/
@[simp]
theorem evalBinOp_ofBitVec_shr_signed {szL szR : Nat} (hszL : 0 < szL) (hszR : 0 < szR)
    (x : BitVec (8 * szL)) (y : BitVec (8 * szR)) :
    evalBinOp .shr (ScalarValue.ofBitVec szL x) (ScalarValue.ofBitVec szR y) true =
      .some (ScalarValue.ofBitVec szL (x.sshiftRight (y.toNat % (8 * szL)))) := by
  rw [evalBinOp_shr_signed hszL hszR]
  unfold ScalarValue.ofBitVec
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `evalBinOp .shlUnchecked` commutes with `ScalarValue.ofBitVec` and `BitVec.shiftLeft` (`<<<`). -/
@[simp]
theorem evalBinOp_ofBitVec_shlUnchecked {szL szR : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR)
    (x : BitVec (8 * szL)) (y : BitVec (8 * szR))
    (hy : y.toNat < 8 * szL) (isSigned : Bool) :
    evalBinOp .shlUnchecked (ScalarValue.ofBitVec szL x) (ScalarValue.ofBitVec szR y) isSigned =
      .some (ScalarValue.ofBitVec szL (x <<< y.toNat)) := by
  rw [evalBinOp_shlUnchecked_apply hszL hszR hy]
  rfl

/-- `evalBinOp .shrUnchecked` (unsigned) commutes with `ScalarValue.ofBitVec` and `BitVec.ushiftRight` (`>>>`). -/
@[simp]
theorem evalBinOp_ofBitVec_shrUnchecked_unsigned {szL szR : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR)
    (x : BitVec (8 * szL)) (y : BitVec (8 * szR))
    (hy : y.toNat < 8 * szL) :
    evalBinOp .shrUnchecked (ScalarValue.ofBitVec szL x) (ScalarValue.ofBitVec szR y) false =
      .some (ScalarValue.ofBitVec szL (x >>> y.toNat)) := by
  rw [evalBinOp_shrUnchecked_unsigned hszL hszR hy]
  unfold ScalarValue.ofBitVec
  congr 1; congr 1
  rw [← BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt (x >>> y.toNat).isLt]

/-- `evalBinOp .shrUnchecked` (signed) commutes with `ScalarValue.ofBitVec` and `BitVec.sshiftRight`. -/
@[simp]
theorem evalBinOp_ofBitVec_shrUnchecked_signed {szL szR : Nat}
    (hszL : 0 < szL) (hszR : 0 < szR)
    (x : BitVec (8 * szL)) (y : BitVec (8 * szR))
    (hy : y.toNat < 8 * szL) :
    evalBinOp .shrUnchecked (ScalarValue.ofBitVec szL x) (ScalarValue.ofBitVec szR y) true =
      .some (ScalarValue.ofBitVec szL (x.sshiftRight y.toNat)) := by
  rw [evalBinOp_shrUnchecked_signed hszL hszR hy]
  unfold ScalarValue.ofBitVec
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `evalBinOp .add` commutes with `ScalarValue.ofBitVec` and `BitVec.add` (`+`). -/
@[simp]
theorem evalBinOp_ofBitVec_add {sz : Nat} (hsz : 0 < sz)
    (x y : BitVec (8 * sz)) (isSigned : Bool) :
    evalBinOp .add (ScalarValue.ofBitVec sz x) (ScalarValue.ofBitVec sz y) isSigned =
      .some (ScalarValue.ofBitVec sz (x + y)) := by
  unfold evalBinOp ScalarValue.ofBitVec
  simp [beq_zero_eq_false_of_pos hsz, BitVec.toNat_add]

/-- `evalBinOp .sub` commutes with `ScalarValue.ofBitVec` and `BitVec.sub` (`-`). -/
@[simp]
theorem evalBinOp_ofBitVec_sub {sz : Nat} (hsz : 0 < sz)
    (x y : BitVec (8 * sz)) (isSigned : Bool) :
    evalBinOp .sub (ScalarValue.ofBitVec sz x) (ScalarValue.ofBitVec sz y) isSigned =
      .some (ScalarValue.ofBitVec sz (x - y)) := by
  unfold evalBinOp ScalarValue.ofBitVec
  simp only [beq_zero_eq_false_of_pos hsz, Nat.beq_refl, BitVec.toNat_sub]
  have hx : x.toNat < 2 ^ (8 * sz) := x.isLt
  have hy : y.toNat < 2 ^ (8 * sz) := y.isLt
  cases hle : Nat.ble y.toNat x.toNat with
  | true =>
    have h_le : y.toNat ≤ x.toNat := Nat.le_of_ble_eq_true hle
    dsimp only
    congr 1; congr 1
    have h1 : 2 ^ (8 * sz) - y.toNat + x.toNat = 2 ^ (8 * sz) + (x.toNat - y.toNat) := by omega
    rw [h1, Nat.add_mod_left]
  | false =>
    dsimp only
    congr 1; congr 1
    rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
    have h1 : 2 ^ (8 * sz) + x.toNat - y.toNat = 2 ^ (8 * sz) - y.toNat + x.toNat := by omega
    rw [h1]

/-- `evalBinOp .mul` commutes with `ScalarValue.ofBitVec` and `BitVec.mul` (`*`). -/
@[simp]
theorem evalBinOp_ofBitVec_mul {sz : Nat} (hsz : 0 < sz)
    (x y : BitVec (8 * sz)) (isSigned : Bool) :
    evalBinOp .mul (ScalarValue.ofBitVec sz x) (ScalarValue.ofBitVec sz y) isSigned =
      .some (ScalarValue.ofBitVec sz (x * y)) := by
  unfold evalBinOp ScalarValue.ofBitVec
  simp [beq_zero_eq_false_of_pos hsz, BitVec.toNat_mul]

/-- `evalBinOpChecked .add` yields `ScalarValue.ofBitVec sz (x + y)` as its first component. -/
@[simp]
theorem evalBinOpChecked_ofBitVec_add_fst {sz : Nat} (hsz : 0 < sz)
    (x y : BitVec (8 * sz)) (isSigned : Bool) :
    (evalBinOpChecked .add (ScalarValue.ofBitVec sz x) (ScalarValue.ofBitVec sz y) isSigned).map Prod.fst =
      .some (ScalarValue.ofBitVec sz (x + y)) := by
  unfold evalBinOpChecked ScalarValue.ofBitVec
  simp [beq_zero_eq_false_of_pos hsz, BitVec.toNat_add]

/-- `evalBinOpChecked .sub` yields `ScalarValue.ofBitVec sz (x - y)` as its first component. -/
@[simp]
theorem evalBinOpChecked_ofBitVec_sub_fst {sz : Nat} (hsz : 0 < sz)
    (x y : BitVec (8 * sz)) (isSigned : Bool) :
    (evalBinOpChecked .sub (ScalarValue.ofBitVec sz x) (ScalarValue.ofBitVec sz y) isSigned).map Prod.fst =
      .some (ScalarValue.ofBitVec sz (x - y)) := by
  have hsub := evalBinOp_ofBitVec_sub hsz x y isSigned
  unfold evalBinOpChecked ScalarValue.ofBitVec
  unfold evalBinOp ScalarValue.ofBitVec at hsub
  simp only [beq_zero_eq_false_of_pos hsz, Nat.beq_refl, Bool.not_true, Bool.or_false,
             Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at hsub ⊢
  cases isSigned <;> cases hle : Nat.ble y.toNat x.toNat <;>
    simp only [hle, Option.map_some] at hsub ⊢ <;> exact hsub

/-- `evalBinOpChecked .mul` yields `ScalarValue.ofBitVec sz (x * y)` as its first component. -/
@[simp]
theorem evalBinOpChecked_ofBitVec_mul_fst {sz : Nat} (hsz : 0 < sz)
    (x y : BitVec (8 * sz)) (isSigned : Bool) :
    (evalBinOpChecked .mul (ScalarValue.ofBitVec sz x) (ScalarValue.ofBitVec sz y) isSigned).map Prod.fst =
      .some (ScalarValue.ofBitVec sz (x * y)) := by
  unfold evalBinOpChecked ScalarValue.ofBitVec
  simp [beq_zero_eq_false_of_pos hsz, BitVec.toNat_mul]

/-- `evalUnOp .not` on integer scalars commutes with `ScalarValue.ofBitVec` and `BitVec.not` (`~~~`). -/
@[simp]
theorem evalUnOp_ofBitVec_not {sz : Nat} (hsz : 0 < sz) (x : BitVec (8 * sz)) :
    evalUnOp .not (ScalarValue.ofBitVec sz x) false =
      .some (ScalarValue.ofBitVec sz (~~~x)) := by
  unfold evalUnOp ScalarValue.ofBitVec
  simp only [beq_zero_eq_false_of_pos hsz, BitVec.toNat_not, Nat.mod_eq_of_lt x.isLt]

/-- `evalUnOp .neg` on integer scalars commutes with `ScalarValue.ofBitVec` and `BitVec.neg` (`-`). -/
@[simp]
theorem evalUnOp_ofBitVec_neg {sz : Nat} (hsz : 0 < sz) (x : BitVec (8 * sz)) :
    evalUnOp .neg (ScalarValue.ofBitVec sz x) false =
      .some (ScalarValue.ofBitVec sz (-x)) := by
  unfold evalUnOp ScalarValue.ofBitVec
  simp only [beq_zero_eq_false_of_pos hsz, BitVec.toNat_neg, Nat.mod_eq_of_lt x.isLt]

/-- `evalUnaryNot` on `.uint` types matches `evalUnOp .not sc false`. -/
theorem evalUnaryNot_uint_eq_evalUnOp {sc : ScalarValue} (hsz : 0 < sc.sizeBytes)
    (uintTy : UintTy) (layoutIdx : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalUnaryNot sc (.some { kind := .uint uintTy, layoutIdx := layoutIdx }) locals mem =
      .ok (.scalar ⟨(~~~sc.toBitVec).toNat, sc.sizeBytes⟩) locals mem := by
  unfold evalUnaryNot ScalarValue.toBitVec
  simp [beq_zero_eq_false_of_pos hsz, BitVec.toNat_not, BitVec.toNat_ofNat]

/-- `evalUnaryNot` on `.int` types matches `evalUnOp .not sc false`. -/
theorem evalUnaryNot_int_eq_evalUnOp {sc : ScalarValue} (hsz : 0 < sc.sizeBytes)
    (intTy : IntTy) (layoutIdx : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalUnaryNot sc (.some { kind := .int intTy, layoutIdx := layoutIdx }) locals mem =
      .ok (.scalar ⟨(~~~sc.toBitVec).toNat, sc.sizeBytes⟩) locals mem := by
  unfold evalUnaryNot ScalarValue.toBitVec
  simp [beq_zero_eq_false_of_pos hsz, BitVec.toNat_not, BitVec.toNat_ofNat]

/--
`evalCastValue` (unsigned) commutes with `ScalarValue.ofBitVec` and
`BitVec.setWidth` (zero-extension when `srcBytes < dstBytes`, truncation when
`dstBytes ≤ srcBytes`).
-/
@[simp]
theorem evalCastValue_ofBitVec_unsigned {srcBytes dstBytes : Nat}
    (hsrc : 0 < srcBytes) (hdst : 0 < dstBytes) (x : BitVec (8 * srcBytes)) :
    evalCastValue (ScalarValue.ofBitVec srcBytes x) dstBytes false =
      .some (ScalarValue.ofBitVec dstBytes (x.setWidth (8 * dstBytes))) := by
  unfold evalCastValue ScalarValue.ofBitVec
  simp [beq_zero_eq_false_of_pos hsrc, beq_zero_eq_false_of_pos hdst,
        BitVec.toNat_setWidth]

/--
`evalCastValue` (signed) commutes with `ScalarValue.ofBitVec` and
`BitVec.signExtend`.
-/
@[simp]
theorem evalCastValue_ofBitVec_signed {srcBytes dstBytes : Nat}
    (hsrc : 0 < srcBytes) (hdst : 0 < dstBytes) (x : BitVec (8 * srcBytes)) :
    evalCastValue (ScalarValue.ofBitVec srcBytes x) dstBytes true =
      .some (ScalarValue.ofBitVec dstBytes (x.signExtend (8 * dstBytes))) := by
  rw [evalCastValue_signed_apply hsrc hdst]
  unfold ScalarValue.ofBitVec
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## 9. `BRIEF-1.2` Bit & Arithmetic Intrinsic Helpers (`ctlz`, `cttz`, `ctpop`, `bswap`, `bitreverse`, `wrapping_*`) -/

/--
Count the number of set (`1`) bits in the low `remBits` bits of `bits` by
structural recursion (`core::intrinsics::ctpop`).
-/
@[reducible]
def ctpopLoop : Nat → Nat → Nat
  | .zero, _ => 0
  | .succ remBits, bits =>
    Nat.add (Nat.mod bits 2) (ctpopLoop remBits (Nat.div bits 2))

/--
Count consecutive trailing zero (`0`) bits starting from the least significant
bit across `remBits` bits of `bits` (`core::intrinsics::cttz`).
-/
@[reducible]
def cttzLoop : Nat → Nat → Nat
  | .zero, _ => 0
  | .succ remBits, bits =>
    match Nat.beq (Nat.mod bits 2) 0 with
    | true => Nat.add 1 (cttzLoop remBits (Nat.div bits 2))
    | false => 0

/--
Reverse the low `remBits` bits of `bits` into accumulator `acc`
(`core::intrinsics::bitreverse`).
-/
@[reducible]
def bitreverseLoop : Nat → Nat → Nat → Nat
  | .zero, _, acc => acc
  | .succ remBits, bits, acc =>
    bitreverseLoop
      remBits
      (Nat.div bits 2)
      (Nat.add (Nat.mul acc 2) (Nat.mod bits 2))

/--
Count consecutive leading zero (`0`) bits of a `numBits`-bit unsigned word
`bits` (`core::intrinsics::ctlz`).
-/
@[reducible]
def ctlzBits (numBits bits : Nat) : Nat :=
  cttzLoop numBits (bitreverseLoop numBits bits 0)

/--
Reverse the low `remBytes` bytes of `bits` into accumulator `acc`
(`core::intrinsics::bswap`).
-/
@[reducible]
def bswapLoop : Nat → Nat → Nat → Nat
  | .zero, _, acc => acc
  | .succ remBytes, bits, acc =>
    bswapLoop
      remBytes
      (Nat.div bits 256)
      (Nat.add (Nat.mul acc 256) (Nat.mod bits 256))

theorem ctpopLoop_le (remBits bits : Nat) : ctpopLoop remBits bits ≤ remBits := by
  induction remBits generalizing bits with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    unfold ctpopLoop
    change bits % 2 + ctpopLoop k (bits / 2) ≤ k + 1
    have hih : ctpopLoop k (bits / 2) ≤ k := ih (bits / 2)
    omega

theorem cttzLoop_le (remBits bits : Nat) : cttzLoop remBits bits ≤ remBits := by
  induction remBits generalizing bits with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    unfold cttzLoop
    cases Nat.beq (Nat.mod bits 2) 0 with
    | false => exact Nat.zero_le (k + 1)
    | true =>
      change 1 + cttzLoop k (bits / 2) ≤ k + 1
      have hih : cttzLoop k (bits / 2) ≤ k := ih (bits / 2)
      omega

theorem ctlzBits_le (numBits bits : Nat) : ctlzBits numBits bits ≤ numBits :=
  cttzLoop_le numBits (bitreverseLoop numBits bits 0)

@[simp]
theorem cttzLoop_zero (remBits : Nat) : cttzLoop remBits 0 = remBits := by
  induction remBits with
  | zero => rfl
  | succ k ih =>
    unfold cttzLoop
    change 1 + cttzLoop k 0 = k + 1
    rw [ih]
    omega

@[simp]
theorem ctpopLoop_zero (remBits : Nat) : ctpopLoop remBits 0 = 0 := by
  induction remBits with
  | zero => rfl
  | succ k ih =>
    unfold ctpopLoop
    change 0 + ctpopLoop k 0 = 0
    rw [ih]

@[simp]
theorem bitreverseLoop_zero (remBits : Nat) : bitreverseLoop remBits 0 0 = 0 := by
  induction remBits with
  | zero => rfl
  | succ k ih =>
    unfold bitreverseLoop
    exact ih

@[simp]
theorem ctlzBits_zero (numBits : Nat) : ctlzBits numBits 0 = numBits := by
  unfold ctlzBits
  rw [bitreverseLoop_zero, cttzLoop_zero]

@[simp]
theorem bswapLoop_zero (remBytes : Nat) : bswapLoop remBytes 0 0 = 0 := by
  induction remBytes with
  | zero => rfl
  | succ k ih =>
    unfold bswapLoop
    exact ih

/-- `bswapLoop 1 n 0` extracts the low byte `n % 256`. -/
@[simp]
theorem bswapLoop_one (n : Nat) : bswapLoop 1 n 0 = n % 256 := by
  unfold bswapLoop
  change 0 * 256 + n % 256 = n % 256
  omega

/-- `bswapLoop 2 n 0` equals `swapBytes16 n` in closed form. -/
@[simp]
theorem bswapLoop_two_eq_swapBytes16 (n : Nat) :
  bswapLoop 2 n 0 = swapBytes16 n := by
  unfold bswapLoop swapBytes16
  change (0 * 256 + n % 256) * 256 + (n / 256) % 256 =
    (n % 256) * 256 + (n / 256) % 256
  omega

/-- `bswapLoop 4 n 0` equals `swapBytes32 n` in closed form. -/
@[simp]
theorem bswapLoop_four_eq_swapBytes32 (n : Nat) :
    bswapLoop 4 n 0 = swapBytes32 n := by
  unfold bswapLoop swapBytes32
  change (((0 * 256 + n % 256) * 256 + (n / 256) % 256) * 256 +
      ((n / 256) / 256) % 256) * 256 + (((n / 256) / 256) / 256) % 256 =
    (n % 256) * 16777216 + ((n / 256) % 256) * 65536 +
      ((n / 65536) % 256) * 256 + (n / 16777216) % 256
  have hdiv2 : (n / 256) / 256 = n / 65536 := Nat.div_div_eq_div_mul n 256 256
  have hdiv3 : (n / 65536) / 256 = n / 16777216 := Nat.div_div_eq_div_mul n 65536 256
  rw [hdiv2, hdiv3]
  omega

/-- `bswapLoop 8 n 0` equals `swapBytes64 n` in closed form. -/
@[simp]
theorem bswapLoop_eight_eq_swapBytes64 (n : Nat) :
    bswapLoop 8 n 0 = swapBytes64 n := by
  unfold bswapLoop swapBytes64
  change (((((((0 * 256 + n % 256) * 256 + (n / 256) % 256) * 256 +
      ((n / 256) / 256) % 256) * 256 + (((n / 256) / 256) / 256) % 256) * 256 +
      ((((n / 256) / 256) / 256) / 256) % 256) * 256 +
      (((((n / 256) / 256) / 256) / 256) / 256) % 256) * 256 +
      ((((((n / 256) / 256) / 256) / 256) / 256) / 256) % 256) * 256 +
      (((((((n / 256) / 256) / 256) / 256) / 256) / 256) / 256) % 256 =
    (n % 256) * 72057594037927936 +
      ((n / 256) % 256) * 281474976710656 +
      ((n / 65536) % 256) * 1099511627776 +
      ((n / 16777216) % 256) * 4294967296 +
      ((n / 4294967296) % 256) * 16777216 +
      ((n / 1099511627776) % 256) * 65536 +
      ((n / 281474976710656) % 256) * 256 +
      ((n / 72057594037927936) % 256)
  have h2 : (n / 256) / 256 = n / 65536 := Nat.div_div_eq_div_mul n 256 256
  have h3 : (n / 65536) / 256 = n / 16777216 := Nat.div_div_eq_div_mul n 65536 256
  have h4 : (n / 16777216) / 256 = n / 4294967296 := Nat.div_div_eq_div_mul n 16777216 256
  have h5 : (n / 4294967296) / 256 = n / 1099511627776 := Nat.div_div_eq_div_mul n 4294967296 256
  have h6 : (n / 1099511627776) / 256 = n / 281474976710656 := Nat.div_div_eq_div_mul n 1099511627776 256
  have h7 : (n / 281474976710656) / 256 = n / 72057594037927936 := Nat.div_div_eq_div_mul n 281474976710656 256
  rw [h2, h3, h4, h5, h6, h7]
  omega

/-! ## 10. Performance Benchmark Witness (< 2000 Heartbeats on 32-Bit Symbolic Header Extraction) -/

/--
Symbolic 32-bit header extraction expression
`((hdr >>> 16) &&& 0xFF) ||| ((hdr &&& 0xFF) <<< 8)` evaluated through
`evalBinOp` on 32-bit `ScalarValue` operands.
-/
def evalHeaderExtract32 (hdr : Nat) : Option ScalarValue := do
  let h : ScalarValue := ⟨hdr, 4⟩
  let c16 : ScalarValue := ⟨16, 4⟩
  let c8 : ScalarValue := ⟨8, 4⟩
  let mask : ScalarValue := ⟨0xFF, 4⟩
  let s1 ← evalBinOp .shr h c16 false
  let hi ← evalBinOp .bitAnd s1 mask false
  let lo ← evalBinOp .bitAnd h mask false
  let s2 ← evalBinOp .shl lo c8 false
  evalBinOp .bitOr hi s2 false

set_option maxHeartbeats 2000 in
/--
Benchmark witness (`FF-1.3` Section 4): simplifies a 32-bit symbolic header
extraction `((hdr >>> 16) &&& 0xFF) ||| ((hdr &&& 0xFF) <<< 8)` via `evalBinOp`
in `< 2000` heartbeats without 32-bit recursive bit unrolling.
-/
theorem evalHeaderExtract32_closed_form (hdr : Nat) :
    evalHeaderExtract32 hdr =
      .some ⟨((((hdr >>> 16) % 4294967296 &&& 255) % 4294967296) |||
        ((((hdr &&& 255) % 4294967296) <<< 8) % 4294967296)) % 4294967296, 4⟩ := by
  simp [evalHeaderExtract32]

set_option maxHeartbeats 2000 in
/--
Operational `MirSemantics.evalScalarBinOp` 32-bit symbolic header extraction
benchmark witness in `< 2000` heartbeats.
-/
theorem evalScalarBinOp_headerExtract32_closed_form
    (hdr : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .shr ⟨hdr, 4⟩ ⟨16, 4⟩ locals mem false =
      .ok (.scalar ⟨(hdr >>> 16) % 4294967296, 4⟩) locals mem ∧
    evalScalarBinOp .bitAnd ⟨(hdr >>> 16) % 4294967296, 4⟩ ⟨0xFF, 4⟩ locals mem false =
      .ok (.scalar ⟨((hdr >>> 16) % 4294967296 &&& 255) % 4294967296, 4⟩) locals mem ∧
    evalScalarBinOp .bitAnd ⟨hdr, 4⟩ ⟨0xFF, 4⟩ locals mem false =
      .ok (.scalar ⟨(hdr &&& 255) % 4294967296, 4⟩) locals mem ∧
    evalScalarBinOp .shl ⟨(hdr &&& 255) % 4294967296, 4⟩ ⟨8, 4⟩ locals mem false =
      .ok (.scalar ⟨(((hdr &&& 255) % 4294967296) <<< 8) % 4294967296, 4⟩) locals mem ∧
    evalScalarBinOp .bitOr
      ⟨((hdr >>> 16) % 4294967296 &&& 255) % 4294967296, 4⟩
      ⟨(((hdr &&& 255) % 4294967296) <<< 8) % 4294967296, 4⟩
      locals mem false =
      .ok (.scalar ⟨((((hdr >>> 16) % 4294967296 &&& 255) % 4294967296) |||
        ((((hdr &&& 255) % 4294967296) <<< 8) % 4294967296)) % 4294967296, 4⟩)
        locals mem := by
  simp

end Anneal.Scalars
