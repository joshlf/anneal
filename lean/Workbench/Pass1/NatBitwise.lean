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
import Init.Data.Nat.Bitwise.Basic

/-!
# Foundation-Locked `Nat` Bitwise, Shift, and `testBit` Library (`Workbench.Pass1.NatBitwise`)

Pass-1-portable (`prelude` + locked `Init.*` only, zero `._unsafe_rec`, exact
`TrustedBoundary` CST syntax, axioms `⊆ [propext]`) library consolidating the
`Nat.bitwise`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`,
`Nat.shiftRight`, and `Nat.testBit` lemmas missing from `foundation-lock.json`
(`Init.Data.Nat.Bitwise.Lemmas` is outside the 51 locked foundation modules):

1. Single-point `Nat.bitwise.eq_def` unfolding bridge (`nat_bitwise_unfold`)
   and width-preservation bounds (`nat_bitwise_lt_two_pow`,
   `nat_land_lt_two_pow`, `nat_lor_lt_two_pow`, `nat_xor_lt_two_pow`).
2. `Nat.testBit` characterization on numerals, powers of two, low masks
   `2^k - 1`, `Nat.mod _ (2^k)`, `Nat.shiftLeft`, and `Nat.shiftRight`.
3. Pointwise `Nat.testBit` distribution over `Nat.bitwise`, `Nat.land`,
   `Nat.lor`, and `Nat.xor`.
4. Arbitrary-`Nat` bit extensionality (`nat_eq_of_testBit_eq`), bit-implication
   order (`nat_le_of_testBit_imp`), `nat_land_le_left`/`nat_land_le_right`,
   mask-modulo equivalence (`nat_land_two_pow_sub_one_eq_mod`), commutativity,
   associativity, zero/self identities, and `nat_lor_add_land`.
-/

namespace Workbench.Pass1.NatBitwise

/-! ## Internal Sugar-Free `Nat` Helpers -/

private theorem ite_prop_true {α : Type} {p : Prop} [hdec : Decidable p]
    (h : p) {a b : α} : (if p then a else b) = a := by
  cases hdec with
  | isTrue _ => rfl
  | isFalse hnp => exact False.elim (hnp h)

private theorem ite_prop_false {α : Type} {p : Prop} [hdec : Decidable p]
    (h : ¬ p) {a b : α} : (if p then a else b) = b := by
  cases hdec with
  | isTrue hp => exact False.elim (h hp)
  | isFalse _ => rfl

private theorem ite_bool_true {α : Type} {a b : α} :
    (if true = true then a else b) = a :=
  rfl

private theorem ite_bool_false {α : Type} {a b : α} :
    (if false = true then a else b) = b :=
  rfl

private theorem nat_pow_succ (b n : Nat) :
    Nat.pow b (n + 1) = Nat.pow b n * b :=
  Nat.pow_succ b n

private theorem nat_pow_le_pow_right {b i j : Nat} (hb : 0 < b) (h : i ≤ j) :
    Nat.pow b i ≤ Nat.pow b j :=
  Nat.pow_le_pow_right hb h

private theorem nat_two_pow_pos (n : Nat) : 0 < Nat.pow 2 n :=
  Nat.two_pow_pos n

private theorem nat_pow_add (b m : Nat) :
    ∀ n : Nat, Nat.pow b (m + n) = Nat.pow b m * Nat.pow b n
  | 0 => by
    rw [Nat.add_zero]
    change Nat.pow b m = Nat.pow b m * 1
    rw [Nat.mul_one]
  | n + 1 => by
    rw [Nat.add_succ, nat_pow_succ, nat_pow_add b m n, nat_pow_succ, Nat.mul_assoc]

private theorem nat_div_add_mod (a b : Nat) :
    b * Nat.div a b + Nat.mod a b = a :=
  Nat.div_add_mod a b

private theorem nat_mod_lt (a : Nat) {b : Nat} (hb : 0 < b) :
    Nat.mod a b < b :=
  Nat.mod_lt a hb

private theorem nat_div_eq_of_lt {a b : Nat} (h : a < b) :
    Nat.div a b = 0 :=
  Nat.div_eq_of_lt h

private theorem nat_div_one (n : Nat) : Nat.div n 1 = n :=
  Nat.div_one n

private theorem nat_div_div_eq_div_mul (a b c : Nat) :
    Nat.div (Nat.div a b) c = Nat.div a (b * c) :=
  Nat.div_div_eq_div_mul a b c

private theorem nat_zero_div (b : Nat) : Nat.div 0 b = 0 :=
  Nat.zero_div b

private theorem nat_zero_mod (b : Nat) : Nat.mod 0 b = 0 :=
  Nat.zero_mod b

private theorem nat_add_mul_div_left (x z : Nat) {y : Nat} (hy : 0 < y) :
    Nat.div (x + y * z) y = Nat.div x y + z :=
  Nat.add_mul_div_left x z hy

private theorem nat_add_mul_mod_self_left (x y z : Nat) :
    Nat.mod (x + y * z) y = Nat.mod x y :=
  Nat.add_mul_mod_self_left x y z

private theorem nat_mul_div_left (a : Nat) {b : Nat} (hb : 0 < b) :
    Nat.div (b * a) b = a :=
  Nat.mul_div_right a hb

private theorem nat_mul_div_mul_right (a b : Nat) {c : Nat} (hc : 0 < c) :
    Nat.div (a * c) (b * c) = Nat.div a b :=
  Nat.mul_div_mul_right a b hc

private theorem nat_mul_mod_right (a b : Nat) :
    Nat.mod (a * b) a = 0 :=
  Nat.mul_mod_right a b

private theorem nat_two_mul_mod_two (r : Nat) : Nat.mod (r + r) 2 = 0 := by
  have h : r + r = 2 * r := by
    rw [Nat.two_mul]
  rw [h, nat_mul_mod_right]

private theorem nat_two_mul_add_one_mod_two (r : Nat) :
    Nat.mod (r + r + 1) 2 = 1 := by
  have h : r + r + 1 = 1 + 2 * r := by
    rw [Nat.two_mul, Nat.add_comm]
  rw [h, nat_add_mul_mod_self_left]

private theorem nat_two_mul_div_two (r : Nat) : Nat.div (r + r) 2 = r := by
  have h : r + r = 2 * r := by
    rw [Nat.two_mul]
  rw [h]
  exact nat_mul_div_left r (by decide : 0 < 2)

private theorem nat_two_mul_add_one_div_two (r : Nat) :
    Nat.div (r + r + 1) 2 = r := by
  have h : r + r + 1 = 1 + 2 * r := by
    rw [Nat.two_mul, Nat.add_comm]
  rw [h, nat_add_mul_div_left 1 r (by decide : 0 < 2)]
  change 0 + r = r
  exact Nat.zero_add r

private theorem nat_mod_two_eq_zero_or_one (n : Nat) :
    Nat.mod n 2 = 0 ∨ Nat.mod n 2 = 1 := by
  have hlt : Nat.mod n 2 < 2 := nat_mod_lt n (by decide : 0 < 2)
  cases hm : Nat.mod n 2 with
  | zero => exact Or.inl rfl
  | succ k =>
    cases k with
    | zero => exact Or.inr rfl
    | succ k' =>
      rw [hm] at hlt
      exact False.elim (Nat.not_lt_zero k' (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hlt)))

private theorem nat_div_two_lt_pow {x k : Nat} (hx : x < Nat.pow 2 (k + 1)) :
    Nat.div x 2 < Nat.pow 2 k := by
  cases Nat.lt_or_ge (Nat.div x 2) (Nat.pow 2 k) with
  | inl hlt => exact hlt
  | inr hge =>
    have hmul : 2 * Nat.pow 2 k ≤ 2 * Nat.div x 2 := Nat.mul_le_mul_left 2 hge
    have hle : 2 * Nat.div x 2 ≤ x := by
      have h0 : 2 * Nat.div x 2 ≤ 2 * Nat.div x 2 + Nat.mod x 2 :=
        Nat.le_add_right (2 * Nat.div x 2) (Nat.mod x 2)
      rw [nat_div_add_mod] at h0
      exact h0
    have hpow : Nat.pow 2 (k + 1) = 2 * Nat.pow 2 k := by
      rw [nat_pow_succ, Nat.mul_comm]
    rw [hpow] at hx
    exact False.elim (Nat.not_lt_of_ge (Nat.le_trans hmul hle) hx)

private theorem nat_lt_two_pow_self : ∀ n : Nat, n < Nat.pow 2 n
  | 0 => by decide
  | n + 1 => by
    have ih : n < Nat.pow 2 n := nat_lt_two_pow_self n
    have hpos : 0 < Nat.pow 2 n := nat_two_pow_pos n
    rw [nat_pow_succ, Nat.mul_two]
    exact Nat.lt_of_succ_le (Nat.add_le_add ih hpos)

/-! ## 1. `Nat.bitwise` Unfolding and Width Bounds -/

theorem nat_bitwise_unfold (f : Bool → Bool → Bool) (n m : Nat) :
    Nat.bitwise f n m =
      if n = 0 then
        if f false true then m else 0
      else if m = 0 then
        if f true false then n else 0
      else
        let r := Nat.bitwise f (Nat.div n 2) (Nat.div m 2)
        if f (decide (Nat.mod n 2 = 1)) (decide (Nat.mod m 2 = 1)) then
          r + r + 1
        else
          r + r :=
  Nat.bitwise.eq_def f n m

theorem nat_land_eq_bitwise (n m : Nat) :
    Nat.land n m = Nat.bitwise and n m := rfl

theorem nat_lor_eq_bitwise (n m : Nat) :
    Nat.lor n m = Nat.bitwise or n m := rfl

theorem nat_xor_eq_bitwise (n m : Nat) :
    Nat.xor n m = Nat.bitwise bne n m := rfl

theorem nat_bitwise_lt_two_pow (f : Bool → Bool → Bool) (w : Nat) :
    ∀ {n m : Nat}, n < Nat.pow 2 w → m < Nat.pow 2 w →
      Nat.bitwise f n m < Nat.pow 2 w := by
  induction w with
  | zero =>
    intro n m hn hm
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hn)
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hm)
    subst hn0
    subst hm0
    rw [nat_bitwise_unfold, ite_prop_true rfl]
    cases f false true <;> exact hm
  | succ w ih =>
    intro n m hn hm
    rw [nat_bitwise_unfold]
    cases n with
    | zero =>
      rw [ite_prop_true rfl]
      cases f false true
      · exact Nat.two_pow_pos (w + 1)
      · exact hm
    | succ n' =>
      rw [ite_prop_false (fun h => nomatch h)]
      cases m with
      | zero =>
        rw [ite_prop_true rfl]
        cases f true false
        · exact Nat.two_pow_pos (w + 1)
        · exact hn
      | succ m' =>
        rw [ite_prop_false (fun h => nomatch h)]
        dsimp only
        have hr : Nat.bitwise f (Nat.div (Nat.succ n') 2) (Nat.div (Nat.succ m') 2) < Nat.pow 2 w :=
          ih (nat_div_two_lt_pow hn) (nat_div_two_lt_pow hm)
        have hpow : Nat.pow 2 (w + 1) = Nat.pow 2 w + Nat.pow 2 w := by
          rw [nat_pow_succ, Nat.mul_two]
        rw [hpow]
        have hstep : ∀ r : Nat, r < Nat.pow 2 w → r + r + 1 < Nat.pow 2 w + Nat.pow 2 w := by
          intro r hr'
          have hle : r + 1 ≤ Nat.pow 2 w := hr'
          have hsum : (r + 1) + r < Nat.pow 2 w + Nat.pow 2 w :=
            Nat.lt_of_le_of_lt (Nat.add_le_add_right hle r) (Nat.add_lt_add_left hr' (Nat.pow 2 w))
          rw [Nat.add_comm r 1, Nat.add_assoc 1 r r, Nat.add_comm 1 (r + r)] at hsum
          exact hsum
        cases f (decide (Nat.mod (Nat.succ n') 2 = 1)) (decide (Nat.mod (Nat.succ m') 2 = 1))
        · exact Nat.add_lt_add hr hr
        · exact hstep _ hr

theorem nat_land_lt_two_pow {w n m : Nat}
    (hn : n < Nat.pow 2 w) (hm : m < Nat.pow 2 w) :
    Nat.land n m < Nat.pow 2 w :=
  nat_bitwise_lt_two_pow and w hn hm

theorem nat_lor_lt_two_pow {w n m : Nat}
    (hn : n < Nat.pow 2 w) (hm : m < Nat.pow 2 w) :
    Nat.lor n m < Nat.pow 2 w :=
  nat_bitwise_lt_two_pow or w hn hm

theorem nat_xor_lt_two_pow {w n m : Nat}
    (hn : n < Nat.pow 2 w) (hm : m < Nat.pow 2 w) :
    Nat.xor n m < Nat.pow 2 w :=
  nat_bitwise_lt_two_pow bne w hn hm

/-! ## 2. `Nat.testBit` Characterization and Shifts -/

private theorem nat_land_one_eq (k : Nat) :
    Nat.land 1 k = if decide (Nat.mod k 2 = 1) then 1 else 0 := by
  rw [nat_land_eq_bitwise, nat_bitwise_unfold]
  cases k with
  | zero =>
    rw [ite_prop_false (by decide : ¬ (1 = 0)), ite_prop_true rfl]
    rfl
  | succ k' =>
    have hdiv1 : Nat.div 1 2 = 0 := by decide
    have hmod1 : decide (Nat.mod 1 2 = 1) = true := by decide
    have hbw0 : Nat.bitwise and 0 (Nat.div (Nat.succ k') 2) = 0 := by
      rw [nat_bitwise_unfold]
      rfl
    rw [ite_prop_false (by decide : ¬ (1 = 0)),
      ite_prop_false (fun h => nomatch h)]
    dsimp only
    rw [hdiv1, hbw0, hmod1]
    cases decide (Nat.mod (Nat.succ k') 2 = 1) <;> rfl

theorem nat_testBit_eq (m i : Nat) :
    m.testBit i = decide (Nat.mod (Nat.div m (Nat.pow 2 i)) 2 = 1) := by
  unfold Nat.testBit
  have hsr : Nat.shiftRight m i = Nat.div m (Nat.pow 2 i) :=
    Nat.shiftRight_eq_div_pow m i
  change (Nat.land 1 (Nat.shiftRight m i) != 0) = _
  rw [hsr, nat_land_one_eq]
  cases decide (Nat.mod (Nat.div m (Nat.pow 2 i)) 2 = 1) <;> rfl

theorem nat_testBit_zero_bit (m : Nat) :
    m.testBit 0 = decide (Nat.mod m 2 = 1) := by
  rw [nat_testBit_eq]
  change decide (Nat.mod (Nat.div m 1) 2 = 1) = decide (Nat.mod m 2 = 1)
  rw [nat_div_one]

theorem nat_testBit_succ (m i : Nat) :
    m.testBit (i + 1) = (Nat.div m 2).testBit i := by
  rw [nat_testBit_eq, nat_testBit_eq, nat_div_div_eq_div_mul,
    Nat.mul_comm 2 (Nat.pow 2 i), ← nat_pow_succ]

theorem nat_testBit_zero (i : Nat) :
    (0 : Nat).testBit i = false := by
  rw [nat_testBit_eq, nat_zero_div, nat_zero_mod]
  rfl

theorem nat_testBit_eq_false_of_lt {m i : Nat} (h : m < Nat.pow 2 i) :
    m.testBit i = false := by
  rw [nat_testBit_eq, nat_div_eq_of_lt h, nat_zero_mod]
  rfl

theorem nat_testBit_two_pow (k i : Nat) :
    (Nat.pow 2 k).testBit i = decide (k = i) := by
  rw [nat_testBit_eq]
  cases Nat.lt_or_ge k i with
  | inl hlt =>
    have hpow : Nat.pow 2 k < Nat.pow 2 i :=
      Nat.lt_of_lt_of_le
        (by
          have hsucc : Nat.pow 2 (k + 1) = Nat.pow 2 k * 2 := nat_pow_succ 2 k
          rw [hsucc, Nat.mul_two]
          exact Nat.lt_add_of_pos_right (nat_two_pow_pos k))
        (nat_pow_le_pow_right (by decide : 0 < 2) hlt)
    rw [nat_div_eq_of_lt hpow, nat_zero_mod]
    exact Eq.symm (decide_eq_false (Nat.ne_of_lt hlt))
  | inr hge =>
    cases Nat.lt_or_ge i k with
    | inl hgt =>
      have hk : k = i + (k - i) := Eq.symm (Nat.add_sub_of_le (Nat.le_of_lt hgt))
      have hki_pos : 0 < k - i := Nat.zero_lt_sub_of_lt hgt
      have hki_eq : k - i = (k - i - 1) + 1 := Eq.symm (Nat.sub_add_cancel hki_pos)
      have hpow_k : Nat.pow 2 k = Nat.pow 2 i * Nat.pow 2 (k - i) := by
        have h1 := congrArg (Nat.pow 2) hk
        rw [nat_pow_add] at h1
        exact h1
      have hpow_even : Nat.pow 2 (k - i) = 2 * Nat.pow 2 (k - i - 1) := by
        have h1 := congrArg (Nat.pow 2) hki_eq
        rw [nat_pow_succ, Nat.mul_comm] at h1
        exact h1
      rw [hpow_k, nat_mul_div_left _ (nat_two_pow_pos i), hpow_even, nat_mul_mod_right]
      exact Eq.symm (decide_eq_false (Nat.ne_of_gt hgt))
    | inr hle =>
      have heq : k = i := Nat.le_antisymm hle hge
      subst heq
      have hself : Nat.div (Nat.pow 2 k) (Nat.pow 2 k) = 1 :=
        Nat.div_self (nat_two_pow_pos k)
      rw [hself]
      exact Eq.symm (decide_eq_true rfl)

theorem nat_testBit_two_pow_sub_one (k : Nat) :
    ∀ i : Nat, (Nat.pow 2 k - 1).testBit i = decide (i < k) := by
  induction k with
  | zero =>
    intro i
    change (0 : Nat).testBit i = decide (i < 0)
    rw [nat_testBit_zero]
    exact Eq.symm (decide_eq_false (Nat.not_lt_zero i))
  | succ k ih =>
    intro i
    have hpos : 0 < Nat.pow 2 k := nat_two_pow_pos k
    have hsplit : Nat.pow 2 (k + 1) - 1 =
        (Nat.pow 2 k - 1) + (Nat.pow 2 k - 1) + 1 := by
      rw [nat_pow_succ, Nat.mul_two]
      have hsub : Nat.pow 2 k = (Nat.pow 2 k - 1) + 1 :=
        Eq.symm (Nat.sub_add_cancel hpos)
      have hsum : Nat.pow 2 k + Nat.pow 2 k =
          ((Nat.pow 2 k - 1) + (Nat.pow 2 k - 1) + 1) + 1 := by
        have h1 :
            ((Nat.pow 2 k - 1) + 1) + ((Nat.pow 2 k - 1) + 1) =
            ((Nat.pow 2 k - 1) + (Nat.pow 2 k - 1) + 1) + 1 := by
          rw [Nat.add_assoc (Nat.pow 2 k - 1) 1,
            Nat.add_comm 1 ((Nat.pow 2 k - 1) + 1),
            ← Nat.add_assoc (Nat.pow 2 k - 1),
            ← Nat.add_assoc (Nat.pow 2 k - 1)]
        rw [← hsub] at h1
        exact h1
      rw [hsum, Nat.add_sub_cancel]
    cases i with
    | zero =>
      rw [nat_testBit_zero_bit, hsplit, nat_two_mul_add_one_mod_two]
      exact Eq.symm (decide_eq_true (Nat.zero_lt_succ k))
    | succ i =>
      rw [nat_testBit_succ, hsplit, nat_two_mul_add_one_div_two, ih i]
      cases Nat.lt_or_ge i k with
      | inl hlt =>
        rw [decide_eq_true hlt, decide_eq_true (Nat.succ_lt_succ hlt)]
      | inr hge =>
        rw [decide_eq_false (Nat.not_lt_of_ge hge),
          decide_eq_false (Nat.not_lt_of_ge (Nat.succ_le_succ hge))]

theorem nat_testBit_mod_two_pow (m k i : Nat) :
    (Nat.mod m (Nat.pow 2 k)).testBit i = (decide (i < k) && m.testBit i) := by
  cases Nat.lt_or_ge i k with
  | inr hge =>
    rw [decide_eq_false (Nat.not_lt_of_ge hge), Bool.false_and]
    exact nat_testBit_eq_false_of_lt
      (Nat.lt_of_lt_of_le (nat_mod_lt m (nat_two_pow_pos k))
        (nat_pow_le_pow_right (by decide : 0 < 2) hge))
  | inl hlt =>
    rw [decide_eq_true hlt, Bool.true_and, nat_testBit_eq, nat_testBit_eq]
    have hk : k = i + (k - i) := Eq.symm (Nat.add_sub_of_le (Nat.le_of_lt hlt))
    have hki_pos : 0 < k - i := Nat.zero_lt_sub_of_lt hlt
    have hki_eq : k - i = (k - i - 1) + 1 :=
      Eq.symm (Nat.sub_add_cancel hki_pos)
    have hpow_k : Nat.pow 2 k = Nat.pow 2 i * Nat.pow 2 (k - i) := by
      have h1 := congrArg (Nat.pow 2) hk
      rw [nat_pow_add] at h1
      exact h1
    have hdecomp : m = Nat.mod m (Nat.pow 2 k) +
        Nat.pow 2 i * (Nat.pow 2 (k - i) * Nat.div m (Nat.pow 2 k)) := by
      have h1 := nat_div_add_mod m (Nat.pow 2 k)
      have h2 : Nat.pow 2 k * Nat.div m (Nat.pow 2 k) =
          Nat.pow 2 i * (Nat.pow 2 (k - i) * Nat.div m (Nat.pow 2 k)) := by
        rw [hpow_k, Nat.mul_assoc]
      rw [h2, Nat.add_comm] at h1
      exact Eq.symm h1
    have hdiv : Nat.div m (Nat.pow 2 i) =
        Nat.div (Nat.mod m (Nat.pow 2 k)) (Nat.pow 2 i) +
        Nat.pow 2 (k - i) * Nat.div m (Nat.pow 2 k) := by
      have h1 := congrArg (fun z => Nat.div z (Nat.pow 2 i)) hdecomp
      rw [nat_add_mul_div_left _ _ (nat_two_pow_pos i)] at h1
      exact h1
    have hpow_even : Nat.pow 2 (k - i) = 2 * Nat.pow 2 (k - i - 1) := by
      have h1 := congrArg (Nat.pow 2) hki_eq
      rw [nat_pow_succ, Nat.mul_comm] at h1
      exact h1
    rw [hdiv, hpow_even, Nat.mul_assoc, nat_add_mul_mod_self_left]

theorem nat_testBit_shiftLeft (m k i : Nat) :
    (Nat.shiftLeft m k).testBit i = (decide (k ≤ i) && m.testBit (i - k)) := by
  have hsl : Nat.shiftLeft m k = m * Nat.pow 2 k := Nat.shiftLeft_eq m k
  rw [hsl]
  cases Nat.lt_or_ge i k with
  | inl hlt =>
    rw [decide_eq_false (Nat.not_le_of_gt hlt), Bool.false_and, nat_testBit_eq]
    have hk : k = i + (k - i) := Eq.symm (Nat.add_sub_of_le (Nat.le_of_lt hlt))
    have hki_pos : 0 < k - i := Nat.zero_lt_sub_of_lt hlt
    have hki_eq : k - i = (k - i - 1) + 1 :=
      Eq.symm (Nat.sub_add_cancel hki_pos)
    have hpow_k : Nat.pow 2 k = Nat.pow 2 (k - i) * Nat.pow 2 i := by
      have h1 := congrArg (Nat.pow 2) hk
      rw [nat_pow_add, Nat.mul_comm] at h1
      exact h1
    have hpow_even : Nat.pow 2 (k - i) = 2 * Nat.pow 2 (k - i - 1) := by
      have h1 := congrArg (Nat.pow 2) hki_eq
      rw [nat_pow_succ, Nat.mul_comm] at h1
      exact h1
    rw [hpow_k, ← Nat.mul_assoc, Nat.mul_comm (m * Nat.pow 2 (k - i)) (Nat.pow 2 i),
      nat_mul_div_left _ (nat_two_pow_pos i), hpow_even,
      Nat.mul_left_comm, nat_mul_mod_right]
    rfl
  | inr hge =>
    rw [decide_eq_true hge, Bool.true_and, nat_testBit_eq, nat_testBit_eq]
    have hi : i = (i - k) + k := Eq.symm (Nat.sub_add_cancel hge)
    have hpow_i : Nat.pow 2 i = Nat.pow 2 (i - k) * Nat.pow 2 k := by
      have h1 := congrArg (Nat.pow 2) hi
      rw [nat_pow_add] at h1
      exact h1
    rw [hpow_i, nat_mul_div_mul_right m (Nat.pow 2 (i - k)) (nat_two_pow_pos k)]

theorem nat_testBit_shiftRight (m k i : Nat) :
    (Nat.shiftRight m k).testBit i = m.testBit (i + k) := by
  have hsr : Nat.shiftRight m k = Nat.div m (Nat.pow 2 k) :=
    Nat.shiftRight_eq_div_pow m k
  rw [hsr, nat_testBit_eq, nat_testBit_eq, nat_div_div_eq_div_mul,
    Nat.mul_comm (Nat.pow 2 k) (Nat.pow 2 i), ← nat_pow_add]

/-! ## 3. `Nat.testBit` Distribution Over Bitwise Operations -/

theorem nat_testBit_bitwise {f : Bool → Bool → Bool}
    (hf : f false false = false) (i : Nat) :
    ∀ n m : Nat, (Nat.bitwise f n m).testBit i = f (n.testBit i) (m.testBit i) := by
  induction i with
  | zero =>
    intro n m
    rw [nat_bitwise_unfold]
    cases n with
    | zero =>
      rw [ite_prop_true rfl, nat_testBit_zero]
      cases hft : f false true with
      | false =>
        rw [ite_bool_false, nat_testBit_zero]
        cases m.testBit 0
        · exact Eq.symm hf
        · exact Eq.symm hft
      | true =>
        rw [ite_bool_true]
        cases m.testBit 0
        · exact Eq.symm hf
        · exact Eq.symm hft
    | succ n' =>
      rw [ite_prop_false (fun h => nomatch h)]
      cases m with
      | zero =>
        rw [ite_prop_true rfl, nat_testBit_zero]
        cases htf : f true false with
        | false =>
          rw [ite_bool_false, nat_testBit_zero]
          cases (Nat.succ n').testBit 0
          · exact Eq.symm hf
          · exact Eq.symm htf
        | true =>
          rw [ite_bool_true]
          cases (Nat.succ n').testBit 0
          · exact Eq.symm hf
          · exact Eq.symm htf
      | succ m' =>
        rw [ite_prop_false (fun h => nomatch h)]
        dsimp only
        rw [nat_testBit_zero_bit (Nat.succ n'),
          nat_testBit_zero_bit (Nat.succ m')]
        cases f (decide (Nat.mod (Nat.succ n') 2 = 1))
            (decide (Nat.mod (Nat.succ m') 2 = 1)) with
        | false =>
          rw [ite_bool_false, nat_testBit_zero_bit, nat_two_mul_mod_two]
          rfl
        | true =>
          rw [ite_bool_true, nat_testBit_zero_bit, nat_two_mul_add_one_mod_two]
          rfl
  | succ i ih =>
    intro n m
    rw [nat_bitwise_unfold]
    cases n with
    | zero =>
      rw [ite_prop_true rfl, nat_testBit_zero]
      cases hft : f false true with
      | false =>
        rw [ite_bool_false, nat_testBit_zero]
        cases m.testBit (i + 1)
        · exact Eq.symm hf
        · exact Eq.symm hft
      | true =>
        rw [ite_bool_true]
        cases m.testBit (i + 1)
        · exact Eq.symm hf
        · exact Eq.symm hft
    | succ n' =>
      rw [ite_prop_false (fun h => nomatch h)]
      cases m with
      | zero =>
        rw [ite_prop_true rfl, nat_testBit_zero]
        cases htf : f true false with
        | false =>
          rw [ite_bool_false, nat_testBit_zero]
          cases (Nat.succ n').testBit (i + 1)
          · exact Eq.symm hf
          · exact Eq.symm htf
        | true =>
          rw [ite_bool_true]
          cases (Nat.succ n').testBit (i + 1)
          · exact Eq.symm hf
          · exact Eq.symm htf
      | succ m' =>
        rw [ite_prop_false (fun h => nomatch h)]
        dsimp only
        rw [nat_testBit_succ (Nat.succ n') i, nat_testBit_succ (Nat.succ m') i]
        cases f (decide (Nat.mod (Nat.succ n') 2 = 1))
            (decide (Nat.mod (Nat.succ m') 2 = 1)) with
        | false =>
          rw [ite_bool_false, nat_testBit_succ, nat_two_mul_div_two]
          exact ih (Nat.div (Nat.succ n') 2) (Nat.div (Nat.succ m') 2)
        | true =>
          rw [ite_bool_true, nat_testBit_succ, nat_two_mul_add_one_div_two]
          exact ih (Nat.div (Nat.succ n') 2) (Nat.div (Nat.succ m') 2)

theorem nat_testBit_land (n m i : Nat) :
    (Nat.land n m).testBit i = (n.testBit i && m.testBit i) :=
  nat_testBit_bitwise rfl i n m

theorem nat_testBit_lor (n m i : Nat) :
    (Nat.lor n m).testBit i = (n.testBit i || m.testBit i) :=
  nat_testBit_bitwise rfl i n m

theorem nat_testBit_xor (n m i : Nat) :
    (Nat.xor n m).testBit i = bne (n.testBit i) (m.testBit i) :=
  nat_testBit_bitwise rfl i n m

/-! ## 4. Bitwise Extensionality, Order, and Algebraic Laws -/

private theorem nat_eq_of_testBit_eq_lt :
    ∀ (k : Nat) {x y : Nat}, x < Nat.pow 2 k → y < Nat.pow 2 k →
      (∀ i : Nat, x.testBit i = y.testBit i) → x = y
  | 0, x, y, hx, hy, _ => by
    rw [Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hx),
        Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hy)]
  | k + 1, x, y, hx, hy, hbits => by
    have hdiv : Nat.div x 2 = Nat.div y 2 :=
      nat_eq_of_testBit_eq_lt k (nat_div_two_lt_pow hx) (nat_div_two_lt_pow hy) (fun i => by
        rw [← nat_testBit_succ, ← nat_testBit_succ]
        exact hbits (i + 1))
    have hbit0 : decide (Nat.mod x 2 = 1) = decide (Nat.mod y 2 = 1) := by
      rw [← nat_testBit_zero_bit, ← nat_testBit_zero_bit]
      exact hbits 0
    have hmod : Nat.mod x 2 = Nat.mod y 2 := by
      cases nat_mod_two_eq_zero_or_one x with
      | inl hx0 =>
        cases nat_mod_two_eq_zero_or_one y with
        | inl hy0 => rw [hx0, hy0]
        | inr hy1 =>
          rw [hx0, hy1] at hbit0
          nomatch hbit0
      | inr hx1 =>
        cases nat_mod_two_eq_zero_or_one y with
        | inl hy0 =>
          rw [hx1, hy0] at hbit0
          nomatch hbit0
        | inr hy1 => rw [hx1, hy1]
    rw [← nat_div_add_mod x 2, ← nat_div_add_mod y 2, hdiv, hmod]

theorem nat_eq_of_testBit_eq {x y : Nat}
    (h : ∀ i : Nat, x.testBit i = y.testBit i) : x = y := by
  have hx : x < Nat.pow 2 (x + y) :=
    Nat.lt_of_lt_of_le (nat_lt_two_pow_self x)
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right x y))
  have hy : y < Nat.pow 2 (x + y) :=
    Nat.lt_of_lt_of_le (nat_lt_two_pow_self y)
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left y x))
  exact nat_eq_of_testBit_eq_lt (x + y) hx hy h

private theorem nat_le_of_testBit_imp_lt :
    ∀ (k : Nat) {x y : Nat}, x < Nat.pow 2 k →
      (∀ i : Nat, x.testBit i = true → y.testBit i = true) → x ≤ y
  | 0, x, y, hx, _ => by
    rw [Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hx)]
    exact Nat.zero_le y
  | k + 1, x, y, hx, himp => by
    have hdiv : Nat.div x 2 ≤ Nat.div y 2 :=
      nat_le_of_testBit_imp_lt k (nat_div_two_lt_pow hx) (fun i hi => by
        rw [← nat_testBit_succ]
        rw [← nat_testBit_succ] at hi
        exact himp (i + 1) hi)
    have hmod : Nat.mod x 2 ≤ Nat.mod y 2 := by
      cases nat_mod_two_eq_zero_or_one x with
      | inl hx0 =>
        rw [hx0]
        exact Nat.zero_le _
      | inr hx1 =>
        have hxt : x.testBit 0 = true := by
          rw [nat_testBit_zero_bit, hx1]
          rfl
        have hyt : y.testBit 0 = true := himp 0 hxt
        rw [nat_testBit_zero_bit] at hyt
        cases nat_mod_two_eq_zero_or_one y with
        | inl hy0 =>
          rw [hy0] at hyt
          nomatch hyt
        | inr hy1 =>
          rw [hx1, hy1]
          exact Nat.le_refl 1
    rw [← nat_div_add_mod x 2, ← nat_div_add_mod y 2]
    exact Nat.add_le_add (Nat.mul_le_mul_left 2 hdiv) hmod

theorem nat_le_of_testBit_imp {x y : Nat}
    (h : ∀ i : Nat, x.testBit i = true → y.testBit i = true) : x ≤ y :=
  nat_le_of_testBit_imp_lt x (nat_lt_two_pow_self x) h

theorem nat_land_le_left (n m : Nat) : Nat.land n m ≤ n :=
  nat_le_of_testBit_imp (fun i hi => by
    rw [nat_testBit_land] at hi
    cases hn : n.testBit i
    · rw [hn] at hi
      nomatch hi
    · rfl)

theorem nat_land_le_right (n m : Nat) : Nat.land n m ≤ m :=
  nat_le_of_testBit_imp (fun i hi => by
    rw [nat_testBit_land] at hi
    cases hm : m.testBit i
    · rw [hm, Bool.and_false] at hi
      nomatch hi
    · rfl)

theorem nat_land_two_pow_sub_one_eq_mod (x k : Nat) :
    Nat.land x (Nat.pow 2 k - 1) = Nat.mod x (Nat.pow 2 k) := by
  apply nat_eq_of_testBit_eq
  intro i
  rw [nat_testBit_land, nat_testBit_two_pow_sub_one, nat_testBit_mod_two_pow]
  cases x.testBit i <;> cases decide (i < k) <;> rfl

theorem nat_land_comm (a b : Nat) : Nat.land a b = Nat.land b a := by
  apply nat_eq_of_testBit_eq
  intro i
  rw [nat_testBit_land, nat_testBit_land]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem nat_lor_comm (a b : Nat) : Nat.lor a b = Nat.lor b a := by
  apply nat_eq_of_testBit_eq
  intro i
  rw [nat_testBit_lor, nat_testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem nat_xor_comm (a b : Nat) : Nat.xor a b = Nat.xor b a := by
  apply nat_eq_of_testBit_eq
  intro i
  rw [nat_testBit_xor, nat_testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem nat_land_assoc (a b c : Nat) :
    Nat.land (Nat.land a b) c = Nat.land a (Nat.land b c) := by
  apply nat_eq_of_testBit_eq
  intro i
  rw [nat_testBit_land, nat_testBit_land, nat_testBit_land, nat_testBit_land, Bool.and_assoc]

theorem nat_lor_assoc (a b c : Nat) :
    Nat.lor (Nat.lor a b) c = Nat.lor a (Nat.lor b c) := by
  apply nat_eq_of_testBit_eq
  intro i
  rw [nat_testBit_lor, nat_testBit_lor, nat_testBit_lor, nat_testBit_lor, Bool.or_assoc]

theorem nat_xor_assoc (a b c : Nat) :
    Nat.xor (Nat.xor a b) c = Nat.xor a (Nat.xor b c) := by
  apply nat_eq_of_testBit_eq
  intro i
  rw [nat_testBit_xor, nat_testBit_xor, nat_testBit_xor, nat_testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

theorem nat_xor_self (a : Nat) : Nat.xor a a = 0 := by
  apply nat_eq_of_testBit_eq
  intro i
  rw [nat_testBit_xor, nat_testBit_zero]
  cases a.testBit i <;> rfl

theorem nat_lor_zero_left (a : Nat) : Nat.lor 0 a = a := by
  apply nat_eq_of_testBit_eq
  intro i
  rw [nat_testBit_lor, nat_testBit_zero, Bool.false_or]

theorem nat_lor_zero_right (a : Nat) : Nat.lor a 0 = a := by
  rw [nat_lor_comm, nat_lor_zero_left]

theorem nat_land_zero_left (a : Nat) : Nat.land 0 a = 0 := by
  apply nat_eq_of_testBit_eq
  intro i
  rw [nat_testBit_land, nat_testBit_zero, Bool.false_and]

theorem nat_land_zero_right (a : Nat) : Nat.land a 0 = 0 := by
  rw [nat_land_comm, nat_land_zero_left]

theorem nat_xor_zero_left (a : Nat) : Nat.xor 0 a = a := by
  apply nat_eq_of_testBit_eq
  intro i
  rw [nat_testBit_xor, nat_testBit_zero]
  cases a.testBit i <;> rfl

theorem nat_xor_zero_right (a : Nat) : Nat.xor a 0 = a := by
  rw [nat_xor_comm, nat_xor_zero_left]

private theorem nat_lor_add_land_lt :
    ∀ (k : Nat) {a b : Nat}, a < Nat.pow 2 k → b < Nat.pow 2 k →
      Nat.lor a b + Nat.land a b = a + b
  | 0, a, b, ha, hb => by
    rw [Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ha),
        Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hb),
        nat_lor_zero_left, nat_land_zero_left]
  | k + 1, a, b, ha, hb => by
    cases a with
    | zero =>
      rw [nat_lor_zero_left, nat_land_zero_left, Nat.add_zero, Nat.zero_add]
    | succ a' =>
      cases b with
      | zero =>
        rw [nat_lor_zero_right, nat_land_zero_right, Nat.add_zero, Nat.add_zero]
      | succ b' =>
        have ih : Nat.lor (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) +
            Nat.land (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) =
            Nat.div (Nat.succ a') 2 + Nat.div (Nat.succ b') 2 :=
          nat_lor_add_land_lt k (nat_div_two_lt_pow ha) (nat_div_two_lt_pow hb)
        rw [nat_lor_eq_bitwise, nat_land_eq_bitwise]
        rw [nat_bitwise_unfold or (Nat.succ a') (Nat.succ b'),
            nat_bitwise_unfold and (Nat.succ a') (Nat.succ b')]
        rw [ite_prop_false (fun h => nomatch h), ite_prop_false (fun h => nomatch h)]
        dsimp only
        rw [← nat_lor_eq_bitwise, ← nat_land_eq_bitwise]
        have hstep :
            ∀ (ro ra qa qb ma mb : Nat),
              ro + ra = qa + qb →
              (ro + ro) + (ra + ra) = 2 * qa + 2 * qb := by
          intro ro ra qa qb _ _ heq
          rw [← Nat.two_mul ro, ← Nat.two_mul ra, ← Nat.mul_add 2 ro ra, heq, Nat.mul_add]
        have hsum_ab :
            Nat.succ a' + Nat.succ b' =
              (2 * Nat.div (Nat.succ a') 2 + 2 * Nat.div (Nat.succ b') 2) +
                (Nat.mod (Nat.succ a') 2 + Nat.mod (Nat.succ b') 2) := by
          have hrearr :
              (2 * Nat.div (Nat.succ a') 2 + Nat.mod (Nat.succ a') 2) +
                (2 * Nat.div (Nat.succ b') 2 + Nat.mod (Nat.succ b') 2) =
              (2 * Nat.div (Nat.succ a') 2 + 2 * Nat.div (Nat.succ b') 2) +
                (Nat.mod (Nat.succ a') 2 + Nat.mod (Nat.succ b') 2) := by
            rw [Nat.add_assoc (2 * Nat.div (Nat.succ a') 2) (Nat.mod (Nat.succ a') 2),
                ← Nat.add_assoc (Nat.mod (Nat.succ a') 2) (2 * Nat.div (Nat.succ b') 2),
                Nat.add_comm (Nat.mod (Nat.succ a') 2) (2 * Nat.div (Nat.succ b') 2),
                Nat.add_assoc (2 * Nat.div (Nat.succ b') 2),
                ← Nat.add_assoc (2 * Nat.div (Nat.succ a') 2)]
          rw [nat_div_add_mod, nat_div_add_mod] at hrearr
          exact hrearr
        have hdouble :
            (Nat.lor (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) +
              Nat.lor (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2)) +
            (Nat.land (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) +
              Nat.land (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2)) =
            2 * Nat.div (Nat.succ a') 2 + 2 * Nat.div (Nat.succ b') 2 :=
          hstep _ _ _ _ 0 0 ih
        have hadd11 : ∀ x y : Nat, (x + 1) + (y + 1) = (x + y) + (1 + 1) := by
          intro x y
          rw [Nat.add_assoc x 1 (y + 1), Nat.add_comm 1 (y + 1),
              Nat.add_assoc y 1 1, ← Nat.add_assoc x y (1 + 1)]
        have h01 : decide (0 = 1) = false := rfl
        have h11 : decide (1 = 1) = true := rfl
        cases nat_mod_two_eq_zero_or_one (Nat.succ a') with
        | inl hma =>
          cases nat_mod_two_eq_zero_or_one (Nat.succ b') with
          | inl hmb =>
            rw [hma, hmb, h01]
            change (Nat.lor (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) +
              Nat.lor (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2)) +
              (Nat.land (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) +
              Nat.land (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2)) =
              Nat.succ a' + Nat.succ b'
            rw [hdouble, hsum_ab, hma, hmb, Nat.add_zero]
          | inr hmb =>
            rw [hma, hmb, h01, h11]
            change (Nat.lor (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) +
              Nat.lor (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) + 1) +
              (Nat.land (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) +
              Nat.land (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2)) =
              Nat.succ a' + Nat.succ b'
            rw [Nat.add_right_comm, hdouble, hsum_ab, hma, hmb, Nat.zero_add]
        | inr hma =>
          cases nat_mod_two_eq_zero_or_one (Nat.succ b') with
          | inl hmb =>
            rw [hma, hmb, h01, h11]
            change (Nat.lor (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) +
              Nat.lor (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) + 1) +
              (Nat.land (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) +
              Nat.land (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2)) =
              Nat.succ a' + Nat.succ b'
            rw [Nat.add_right_comm, hdouble, hsum_ab, hma, hmb, Nat.add_zero]
          | inr hmb =>
            rw [hma, hmb, h11]
            change (Nat.lor (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) +
              Nat.lor (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) + 1) +
              (Nat.land (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) +
              Nat.land (Nat.div (Nat.succ a') 2) (Nat.div (Nat.succ b') 2) + 1) =
              Nat.succ a' + Nat.succ b'
            rw [hadd11, hdouble, hsum_ab, hma, hmb]

theorem nat_lor_add_land (a b : Nat) :
    Nat.lor a b + Nat.land a b = a + b := by
  have ha : a < Nat.pow 2 (a + b) :=
    Nat.lt_of_lt_of_le (nat_lt_two_pow_self a)
      (nat_pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right a b))
  have hb : b < Nat.pow 2 (a + b) :=
    Nat.lt_of_lt_of_le (nat_lt_two_pow_self b)
      (nat_pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left b a))
  exact nat_lor_add_land_lt (a + b) ha hb

end Workbench.Pass1.NatBitwise
