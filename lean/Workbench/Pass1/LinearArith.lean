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
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Int.Basic
import Init.Data.List.Basic

/-!
# Sparse Linear Arithmetic & Chvatal-Gomory Cut Certifier (`Workbench.Pass1.LinearArith`)

Pass-1-portable (`prelude` + locked `Init.*` only, `[propext]` only, zero
`._unsafe_rec`, zero `omega`) reflective linear-inequality solver replacing
banned `omega` in `anneal/theory/` and `anneal/correspondence/`:

- Discharges `Nat` (`checkNatCutGoal_sound`) and `Int` (`checkIntCutGoal_sound`)
  linear bounds by `rfl` or `decide`.
- Supports both nonnegative Farkas combinations (`CutStep.comb`) and exact
  integer Chvatal-Gomory floor cuts (`CutStep.divCut g s`), solving parity,
  stride, and alignment obligations (e.g. `2 * i + 1 ≤ 2 * n → i < n`) that
  rational Farkas cannot prove.
- Pair with `scripts/farkas_cert_gen.py` to synthesize `CutStep` witnesses
  automatically from surface inequalities.
-/

namespace Workbench.Pass1.LinearArith

/-! ## 1. Constructive `Int` <-> Sign-Magnitude `Nat` Bridge (`IntBalance`) -/

def intPos : Int → Nat
  | .ofNat n => n
  | .negSucc _ => 0

def intNeg : Int → Nat
  | .ofNat _ => 0
  | .negSucc m => m + 1

def IntBalance (x : Int) (p n : Nat) : Prop :=
  intPos x + n = intNeg x + p

theorem add_four_rearrange (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc a b (c + d), ← Nat.add_assoc b c d, Nat.add_comm b c,
      Nat.add_assoc c b d, ← Nat.add_assoc a c (b + d)]

theorem add_three_mid (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b c, ← Nat.add_assoc]

theorem intBalance_iff_of_add_eq {x : Int} {p1 n1 p2 n2 : Nat}
    (h1 : IntBalance x p1 n1) (hEq : p1 + n2 = p2 + n1) :
    IntBalance x p2 n2 := by
  unfold IntBalance at h1
  unfold IntBalance
  have hSum : (intPos x + n2) + (p1 + n1) = (intNeg x + p2) + (p1 + n1) := by
    have hL : (intPos x + n2) + (p1 + n1) = (intPos x + n1) + (p1 + n2) := by
      rw [add_four_rearrange (intPos x) n2 p1 n1, Nat.add_comm n2 n1,
          ← add_four_rearrange (intPos x) p1 n1 n2]
    have hR : (intNeg x + p2) + (p1 + n1) = (intNeg x + p1) + (p2 + n1) :=
      add_four_rearrange (intNeg x) p2 p1 n1
    rw [hL, hR, h1, hEq]
  exact Nat.add_right_cancel hSum

theorem intBalance_eq_of_eq {x y : Int} {p n : Nat}
    (hx : IntBalance x p n) (hy : IntBalance y p n) : x = y := by
  unfold IntBalance at hx hy
  cases x with
  | ofNat px =>
    cases y with
    | ofNat py =>
      dsimp [intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hEq : px + n = py + n := by rw [hx, hy]
      rw [Nat.add_right_cancel hEq]
    | negSucc ny =>
      dsimp [intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hBad : px + (ny + 1) + p = 0 + p := by
        rw [Nat.add_assoc, ← hy, hx, Nat.zero_add]
      have hZero : px + (ny + 1) = 0 := Nat.add_right_cancel hBad
      nomatch hZero
  | negSucc nx =>
    cases y with
    | ofNat py =>
      dsimp [intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hBad : py + (nx + 1) + p = 0 + p := by
        rw [Nat.add_assoc, ← hx, hy, Nat.zero_add]
      have hZero : py + (nx + 1) = 0 := Nat.add_right_cancel hBad
      nomatch hZero
    | negSucc ny =>
      dsimp [intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hEq : nx + 1 + p = ny + 1 + p := by rw [← hx, ← hy]
      have hSucc : nx + 1 = ny + 1 := Nat.add_right_cancel hEq
      have hN : nx = ny := Nat.succ.inj hSucc
      rw [hN]

theorem intBalance_self (x : Int) : IntBalance x (intPos x) (intNeg x) := by
  unfold IntBalance
  exact Nat.add_comm (intPos x) (intNeg x)

theorem intBalance_ofNat (n : Nat) : IntBalance (Int.ofNat n) n 0 := by
  dsimp [IntBalance, intPos, intNeg]; simp only [Nat.zero_add]

theorem intBalance_negOfNat : ∀ n : Nat, IntBalance (Int.negOfNat n) 0 n
  | 0 => rfl
  | _ + 1 => by
    dsimp [IntBalance, Int.negOfNat, intPos, intNeg]
    simp only [Nat.zero_add]

theorem intBalance_subNatNat (p n : Nat) :
    IntBalance (Int.subNatNat p n) p n := by
  unfold Int.subNatNat
  cases hSub : n - p with
  | zero =>
    have hLe : n ≤ p := Nat.le_of_sub_eq_zero hSub
    dsimp [IntBalance, intPos, intNeg]
    rw [Nat.zero_add, Nat.sub_add_cancel hLe]
  | succ k =>
    have hLt : p < n := Nat.lt_of_sub_eq_succ hSub
    have hAdd : p + (k + 1) = n := by
      rw [← hSub]
      exact Nat.add_sub_of_le (Nat.le_of_lt hLt)
    dsimp [IntBalance, intPos, intNeg]
    rw [Nat.zero_add, Nat.add_comm (k + 1) p]
    exact hAdd.symm

theorem intBalance_neg {x : Int} {p n : Nat} (h : IntBalance x p n) :
    IntBalance (Int.neg x) n p := by
  cases x with
  | ofNat mx =>
    dsimp [IntBalance, intPos, intNeg] at h
    rw [Nat.zero_add] at h
    have hb := intBalance_negOfNat mx
    exact intBalance_iff_of_add_eq hb (by rw [Nat.zero_add, Nat.add_comm, h])
  | negSucc nx =>
    dsimp [IntBalance, intPos, intNeg] at h
    rw [Nat.zero_add] at h
    have hb := intBalance_ofNat (nx + 1)
    exact intBalance_iff_of_add_eq hb (by rw [← h, Nat.add_zero])

theorem intBalance_add {x y : Int} {px nx py ny : Nat}
    (hx : IntBalance x px nx) (hy : IntBalance y py ny) :
    IntBalance (Int.add x y) (px + py) (nx + ny) := by
  cases x with
  | ofNat mx =>
    cases y with
    | ofNat my =>
      dsimp [IntBalance, intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hb := intBalance_ofNat (mx + my)
      exact intBalance_iff_of_add_eq hb
        (by rw [Nat.add_zero, ← hx, ← hy, add_four_rearrange])
    | negSucc ny' =>
      dsimp [IntBalance, intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hb := intBalance_subNatNat mx (ny' + 1)
      exact intBalance_iff_of_add_eq hb
        (by rw [← hx, hy, ← Nat.add_assoc mx nx ((ny' + 1) + py),
                Nat.add_comm (ny' + 1) py,
                ← Nat.add_assoc (mx + nx) py (ny' + 1)])
  | negSucc nx' =>
    cases y with
    | ofNat my =>
      dsimp [IntBalance, intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hb := intBalance_subNatNat my (nx' + 1)
      exact intBalance_iff_of_add_eq hb
        (by rw [hx, ← hy, Nat.add_assoc (nx' + 1) px ny,
                Nat.add_comm (nx' + 1) (px + ny),
                ← Nat.add_assoc my (px + ny) (nx' + 1),
                ← Nat.add_assoc my px ny,
                Nat.add_comm my px, Nat.add_assoc px my ny])
    | negSucc ny' =>
      dsimp [IntBalance, intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      have hRHS :
          Int.add (Int.negSucc nx') (Int.negSucc ny') =
            Int.negSucc (Nat.succ (nx' + ny')) := rfl
      rw [hRHS]
      have hSum : Nat.succ (nx' + ny') + 1 = (nx' + 1) + (ny' + 1) := by
        rw [Nat.succ_eq_add_one, Nat.add_assoc nx' ny' 1,
            Nat.add_assoc nx' (ny' + 1) 1, Nat.add_comm (ny' + 1) 1,
            ← Nat.add_assoc nx' 1 (ny' + 1)]
      have hb :
          IntBalance (Int.negSucc (Nat.succ (nx' + ny'))) 0
            ((nx' + 1) + (ny' + 1)) := by
        dsimp [IntBalance, intPos, intNeg]
        rw [Nat.zero_add, Nat.add_zero, hSum]
      exact intBalance_iff_of_add_eq hb
        (by rw [Nat.zero_add, hx, hy, add_four_rearrange,
                Nat.add_comm ((nx' + 1) + (ny' + 1)) (px + py)])

theorem intBalance_sub {x y : Int} {px nx py ny : Nat}
    (hx : IntBalance x px nx) (hy : IntBalance y py ny) :
    IntBalance (Int.sub x y) (px + ny) (nx + py) :=
  intBalance_add hx (intBalance_neg hy)

theorem intBalance_mul_nat {x : Int} {p n : Nat} (k : Nat)
    (h : IntBalance x p n) :
    IntBalance (Int.mul (Int.ofNat k) x) (k * p) (k * n) := by
  cases x with
  | ofNat mx =>
    dsimp [IntBalance, intPos, intNeg] at h
    rw [Nat.zero_add] at h
    have hb := intBalance_ofNat (k * mx)
    exact intBalance_iff_of_add_eq hb (by rw [Nat.add_zero, ← Nat.mul_add, h])
  | negSucc nx =>
    dsimp [IntBalance, intPos, intNeg] at h
    rw [Nat.zero_add] at h
    have hb := intBalance_negOfNat (k * (nx + 1))
    exact intBalance_iff_of_add_eq hb
      (by rw [Nat.zero_add, h, Nat.mul_add, Nat.add_comm (k * (nx + 1)) (k * p)])

theorem int_mul_negSucc_left (a : Nat) (y : Int) :
    Int.mul (Int.negSucc a) y = Int.neg (Int.mul (Int.ofNat (a + 1)) y) := by
  cases y with
  | ofNat _ => rfl
  | negSucc b =>
    exact (intBalance_eq_of_eq
      (intBalance_neg (intBalance_negOfNat ((a + 1) * (b + 1))))
      (intBalance_ofNat ((a + 1) * (b + 1)))).symm

theorem int_mul_negSucc_right (a b : Nat) :
    Int.mul (Int.ofNat a) (Int.negSucc b) =
      Int.neg (Int.mul (Int.ofNat a) (Int.ofNat (b + 1))) :=
  rfl

theorem nat_mul_balance_cancel (a nx px b ny py : Nat)
    (hx : a + nx = px) (hy : b + ny = py) :
    a * b + (px * ny + nx * py) = px * py + nx * ny := by
  rw [← hx, ← hy]
  rw [Nat.add_mul a nx ny, Nat.add_mul a nx (b + ny),
      Nat.mul_add a b ny, Nat.mul_add nx b ny]
  rw [Nat.add_comm (a * ny) (nx * ny),
      Nat.add_assoc (nx * ny) (a * ny) (nx * b + nx * ny)]
  rw [Nat.add_comm (nx * ny) (a * ny + (nx * b + nx * ny)),
      ← Nat.add_assoc (a * b)]
  rw [Nat.add_assoc (a * b) (a * ny) (nx * b + nx * ny)]

theorem intBalance_mul_nat_var (a : Nat) {px nx : Nat}
    (hx : IntBalance (Int.ofNat a) px nx)
    {y : Int} {py ny : Nat} (hy : IntBalance y py ny) :
    IntBalance (Int.mul (Int.ofNat a) y)
      (px * py + nx * ny) (px * ny + nx * py) := by
  dsimp [IntBalance, intPos, intNeg] at hx
  rw [Nat.zero_add] at hx
  cases y with
  | ofNat b =>
    dsimp [IntBalance, intPos, intNeg] at hy
    rw [Nat.zero_add] at hy
    have hEq := nat_mul_balance_cancel a nx px b ny py hx hy
    have hb := intBalance_ofNat (a * b)
    exact intBalance_iff_of_add_eq hb (by rw [Nat.add_zero]; exact hEq)
  | negSucc b' =>
    dsimp [IntBalance, intPos, intNeg] at hy
    rw [Nat.zero_add] at hy
    have hEq := nat_mul_balance_cancel a nx px (b' + 1) py ny hx hy.symm
    rw [int_mul_negSucc_right]
    have hb := intBalance_neg (intBalance_ofNat (a * (b' + 1)))
    exact intBalance_iff_of_add_eq hb
      (by rw [Nat.zero_add,
              Nat.add_comm (px * py + nx * ny) (a * (b' + 1))]
          exact hEq.symm)

theorem intBalance_mul {x y : Int} {px nx py ny : Nat}
    (hx : IntBalance x px nx) (hy : IntBalance y py ny) :
    IntBalance (Int.mul x y) (px * py + nx * ny) (px * ny + nx * py) := by
  cases x with
  | ofNat a => exact intBalance_mul_nat_var a hx hy
  | negSucc a' =>
    rw [int_mul_negSucc_left]
    have hxNeg : IntBalance (Int.ofNat (a' + 1)) nx px := intBalance_neg hx
    have hPos := intBalance_mul_nat_var (a' + 1) hxNeg hy
    have hRes := intBalance_neg hPos
    exact intBalance_iff_of_add_eq hRes
      (by rw [Nat.add_comm (nx * py) (px * ny),
              Nat.add_comm (nx * ny) (px * py)])

theorem intBalance_le {x y : Int} {px nx py ny : Nat}
    (hx : IntBalance x px nx) (hy : IntBalance y py ny) :
    (x ≤ y) ↔ (px + ny ≤ py + nx) := by
  have hDiff : IntBalance (Int.sub y x) (py + nx) (ny + px) :=
    intBalance_sub hy hx
  unfold IntBalance at hDiff
  constructor
  · intro hLe
    cases hSub : Int.sub y x with
    | ofNat m =>
      rw [hSub] at hDiff
      dsimp [intPos, intNeg] at hDiff
      rw [Nat.zero_add, Nat.add_comm ny px] at hDiff
      have hLe' : px + ny ≤ m + (px + ny) := Nat.le_add_left (px + ny) m
      rw [hDiff] at hLe'
      exact hLe'
    | negSucc _ =>
      change Int.NonNeg (Int.sub y x) at hLe
      rw [hSub] at hLe
      nomatch hLe
  · intro hNat
    change Int.NonNeg (Int.sub y x)
    cases hSub : Int.sub y x with
    | ofNat m => exact Int.NonNeg.mk m
    | negSucc k =>
      rw [hSub] at hDiff
      dsimp [intPos, intNeg] at hDiff
      rw [Nat.zero_add] at hDiff
      have hBound : py + nx + (k + 1) ≤ py + nx := by
        rw [Nat.add_comm (k + 1) (py + nx)] at hDiff
        rw [← hDiff, Nat.add_comm ny px]
        exact hNat
      have hBad : k + 1 ≤ 0 := Nat.le_of_add_le_add_left hBound
      nomatch hBad

theorem int_le_of_not_succ_le (a b : Int)
    (h : Int.add b (Int.ofNat 1) ≤ a → False) : a ≤ b := by
  have ha := intBalance_self a
  have hb := intBalance_self b
  have hb1 := intBalance_add hb (intBalance_ofNat 1)
  cases Nat.lt_or_ge (intPos b + intNeg a + 1) (intPos a + intNeg b + 1) with
  | inl hLt =>
    have hLeNat : intPos b + intNeg a + 1 ≤ intPos a + intNeg b :=
      Nat.le_of_lt_succ hLt
    have hLeInt : Int.add b (Int.ofNat 1) ≤ a := by
      have hIff := intBalance_le hb1 ha
      apply hIff.2
      rw [Nat.add_zero, add_three_mid (intPos b) 1 (intNeg a)]
      exact hLeNat
    exact False.elim (h hLeInt)
  | inr hGe =>
    have hLeNat : intPos a + intNeg b ≤ intPos b + intNeg a :=
      Nat.le_of_succ_le_succ hGe
    exact (intBalance_le ha hb).2 hLeNat

/-! ## 2. Sign-Magnitude `Nat` Carrier (`SInt`) with `magCap128` Guard -/

def magCap128 : Nat := Nat.shiftLeft 1 128

structure SInt where
  neg : Bool
  mag : Nat

def SInt.zero : SInt := ⟨false, 0⟩
def SInt.one : SInt := ⟨false, 1⟩
def SInt.negOne : SInt := ⟨true, 1⟩

def SInt.toInt (s : SInt) : Int :=
  match s.neg with
  | false => Int.ofNat s.mag
  | true => Int.negOfNat s.mag

def SInt.posPart (s : SInt) : Nat :=
  match s.neg with
  | false => s.mag
  | true => 0

def SInt.negPart (s : SInt) : Nat :=
  match s.neg with
  | false => 0
  | true => s.mag

theorem sint_intBalance (s : SInt) :
    IntBalance s.toInt s.posPart s.negPart := by
  cases hNeg : s.neg with
  | false =>
    dsimp [SInt.toInt, SInt.posPart, SInt.negPart]
    rw [hNeg]
    exact intBalance_ofNat s.mag
  | true =>
    dsimp [SInt.toInt, SInt.posPart, SInt.negPart]
    rw [hNeg]
    exact intBalance_negOfNat s.mag

def SInt.ofPN (p n : Nat) : SInt :=
  match Nat.ble n p with
  | true => ⟨false, p - n⟩
  | false => ⟨true, n - p⟩

theorem sint_ofPN_balance (p n : Nat) :
    IntBalance (SInt.ofPN p n).toInt p n := by
  dsimp [SInt.ofPN]
  cases hBle : Nat.ble n p with
  | true =>
    have hLe : n ≤ p := Nat.le_of_ble_eq_true hBle
    exact intBalance_iff_of_add_eq (sint_intBalance ⟨false, p - n⟩)
      (by dsimp [SInt.posPart, SInt.negPart]; rw [Nat.sub_add_cancel hLe])
  | false =>
    have hNot : ¬ (n ≤ p) := fun h => by
      have ht := Nat.ble_eq_true_of_le h
      rw [ht] at hBle
      nomatch hBle
    have hLe : p ≤ n := Nat.le_of_lt (Nat.lt_of_not_le hNot)
    exact intBalance_iff_of_add_eq (sint_intBalance ⟨true, n - p⟩)
      (by dsimp [SInt.posPart, SInt.negPart]
          rw [Nat.zero_add, Nat.add_comm p (n - p), Nat.sub_add_cancel hLe])

def SInt.negate (s : SInt) : SInt :=
  match Nat.beq s.mag 0 with
  | true => SInt.zero
  | false => ⟨!s.neg, s.mag⟩

theorem sint_negate_balance (s : SInt) :
    IntBalance (SInt.negate s).toInt s.negPart s.posPart := by
  dsimp [SInt.negate]
  cases hZero : Nat.beq s.mag 0 with
  | true =>
    have hEq : s.mag = 0 := Nat.eq_of_beq_eq_true hZero
    cases hN : s.neg with
    | false =>
      dsimp [SInt.zero, SInt.toInt, SInt.posPart, SInt.negPart]
      rw [hN, hEq]; rfl
    | true =>
      dsimp [SInt.zero, SInt.toInt, SInt.posPart, SInt.negPart]
      rw [hN, hEq]; rfl
  | false =>
    cases hN : s.neg with
    | false =>
      dsimp [SInt.toInt, SInt.posPart, SInt.negPart]
      rw [hN]
      exact intBalance_negOfNat s.mag
    | true =>
      dsimp [SInt.toInt, SInt.posPart, SInt.negPart]
      rw [hN]
      exact intBalance_ofNat s.mag

def SInt.add (a b : SInt) : SInt :=
  SInt.ofPN (a.posPart + b.posPart) (a.negPart + b.negPart)

theorem sint_add_balance (a b : SInt) :
    IntBalance (SInt.add a b).toInt
      (a.posPart + b.posPart) (a.negPart + b.negPart) :=
  sint_ofPN_balance (a.posPart + b.posPart) (a.negPart + b.negPart)

theorem sint_add_toInt (a b : SInt) :
    (SInt.add a b).toInt = Int.add a.toInt b.toInt :=
  intBalance_eq_of_eq (sint_add_balance a b)
    (intBalance_add (sint_intBalance a) (sint_intBalance b))

def SInt.sub (a b : SInt) : SInt :=
  SInt.add a (SInt.negate b)

def SInt.scaleNat (k : Nat) (s : SInt) : SInt :=
  match Nat.beq k 0 with
  | true => SInt.zero
  | false =>
    match Nat.beq s.mag 0 with
    | true => SInt.zero
    | false => ⟨s.neg, k * s.mag⟩

theorem sint_scaleNat_toInt (k : Nat) (s : SInt) :
    (SInt.scaleNat k s).toInt = Int.mul (Int.ofNat k) s.toInt := by
  dsimp [SInt.scaleNat]
  cases hk : Nat.beq k 0 with
  | true =>
    have hK0 : k = 0 := Nat.eq_of_beq_eq_true hk
    rw [hK0]
    dsimp only [SInt.zero, SInt.toInt]
    exact intBalance_eq_of_eq (intBalance_ofNat 0)
      (intBalance_iff_of_add_eq (intBalance_mul_nat 0 (sint_intBalance s))
        (by rw [Nat.zero_mul, Nat.zero_mul]))
  | false =>
    cases hm : Nat.beq s.mag 0 with
    | true =>
      have hM0 : s.mag = 0 := Nat.eq_of_beq_eq_true hm
      cases hN : s.neg with
      | false =>
        dsimp [SInt.toInt]; rw [hN, hM0]
        exact (intBalance_eq_of_eq (intBalance_mul_nat k (intBalance_ofNat 0))
          (intBalance_iff_of_add_eq (intBalance_ofNat 0)
            (by rw [Nat.mul_zero]))).symm
      | true =>
        dsimp [SInt.toInt]; rw [hN, hM0]
        exact (intBalance_eq_of_eq
          (intBalance_mul_nat k (intBalance_negOfNat 0))
          (intBalance_iff_of_add_eq (intBalance_ofNat 0)
            (by rw [Nat.mul_zero]))).symm
    | false =>
      cases hN : s.neg with
      | false =>
        dsimp [SInt.toInt]; rw [hN]
        exact intBalance_eq_of_eq (intBalance_ofNat (k * s.mag))
          (intBalance_mul_nat k (intBalance_ofNat s.mag))
      | true =>
        dsimp [SInt.toInt]; rw [hN]
        exact intBalance_eq_of_eq (intBalance_negOfNat (k * s.mag))
          (intBalance_mul_nat k (intBalance_negOfNat s.mag))

def boolXor (a b : Bool) : Bool :=
  match a, b with
  | false, false => false
  | true, true => false
  | _, _ => true

def SInt.mul (a b : SInt) : SInt :=
  match Nat.beq a.mag 0 || Nat.beq b.mag 0 with
  | true => SInt.zero
  | false => ⟨boolXor a.neg b.neg, a.mag * b.mag⟩

theorem sint_mul_toInt (a b : SInt) :
    (SInt.mul a b).toInt = Int.mul a.toInt b.toInt := by
  have ha := sint_intBalance a
  have hb := sint_intBalance b
  dsimp [SInt.mul]
  cases ha0 : Nat.beq a.mag 0 with
  | true =>
    have hMa : a.mag = 0 := Nat.eq_of_beq_eq_true ha0
    have haZero : IntBalance a.toInt 0 0 := by
      cases hNa : a.neg with
      | false => dsimp [SInt.toInt]; rw [hNa, hMa]; exact intBalance_ofNat 0
      | true => dsimp [SInt.toInt]; rw [hNa, hMa]; exact intBalance_negOfNat 0
    have hProd := intBalance_mul haZero hb
    rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero] at hProd
    exact intBalance_eq_of_eq (intBalance_ofNat 0) hProd
  | false =>
    cases hb0 : Nat.beq b.mag 0 with
    | true =>
      have hMb : b.mag = 0 := Nat.eq_of_beq_eq_true hb0
      have hbZero : IntBalance b.toInt 0 0 := by
        cases hNb : b.neg with
        | false => dsimp [SInt.toInt]; rw [hNb, hMb]; exact intBalance_ofNat 0
        | true => dsimp [SInt.toInt]; rw [hNb, hMb]; exact intBalance_negOfNat 0
      have hProd := intBalance_mul ha hbZero
      rw [Nat.mul_zero, Nat.mul_zero, Nat.add_zero] at hProd
      exact intBalance_eq_of_eq (intBalance_ofNat 0) hProd
    | false =>
      dsimp [Bool.or]
      cases hNa : a.neg with
      | false =>
        cases hNb : b.neg with
        | false =>
          dsimp [boolXor, SInt.toInt]; rw [hNa, hNb]
          have hProd :=
            intBalance_mul (intBalance_ofNat a.mag) (intBalance_ofNat b.mag)
          simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hProd
          exact intBalance_eq_of_eq (intBalance_ofNat (a.mag * b.mag)) hProd
        | true =>
          dsimp [boolXor, SInt.toInt]; rw [hNa, hNb]
          have hProd :=
            intBalance_mul (intBalance_ofNat a.mag) (intBalance_negOfNat b.mag)
          simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hProd
          exact intBalance_eq_of_eq (intBalance_negOfNat (a.mag * b.mag)) hProd
      | true =>
        cases hNb : b.neg with
        | false =>
          dsimp [boolXor, SInt.toInt]; rw [hNa, hNb]
          have hProd :=
            intBalance_mul (intBalance_negOfNat a.mag) (intBalance_ofNat b.mag)
          simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero,
                     Nat.zero_add] at hProd
          exact intBalance_eq_of_eq (intBalance_negOfNat (a.mag * b.mag)) hProd
        | true =>
          dsimp [boolXor, SInt.toInt]; rw [hNa, hNb]
          have hProd :=
            intBalance_mul (intBalance_negOfNat a.mag)
              (intBalance_negOfNat b.mag)
          simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero,
                     Nat.zero_add] at hProd
          exact intBalance_eq_of_eq (intBalance_ofNat (a.mag * b.mag)) hProd

def SInt.isZero (s : SInt) : Bool := Nat.beq s.mag 0

def SInt.isStrictlyNeg (s : SInt) : Bool :=
  s.neg && Nat.ble 1 s.mag

def SInt.withinCap (s : SInt) : Bool := Nat.ble s.mag magCap128

def SInt.divExact (g : Nat) (s : SInt) : SInt :=
  ⟨s.neg, Nat.div s.mag g⟩

def SInt.fdiv (s : SInt) (g : Nat) : SInt :=
  match s.neg with
  | false => ⟨false, Nat.div s.mag g⟩
  | true =>
    match s.mag with
    | 0 => SInt.zero
    | m + 1 => ⟨true, Nat.div m g + 1⟩

theorem sint_divExact_scale (g : Nat) (s : SInt)
    (hg : 0 < g) (hd : Nat.mod s.mag g = 0) :
    SInt.scaleNat g (SInt.divExact g s) = ⟨s.neg, s.mag⟩ ∨
    (s.mag = 0 ∧ SInt.scaleNat g (SInt.divExact g s) = SInt.zero) := by
  have hMulDiv : g * Nat.div s.mag g = s.mag := by
    have h := Nat.div_add_mod s.mag g
    dsimp only [HDiv.hDiv, Div.div, HMod.hMod, Mod.mod] at h
    rw [hd, Nat.add_zero] at h
    exact h
  cases hm : Nat.beq s.mag 0 with
  | true =>
    have hm0 : s.mag = 0 := Nat.eq_of_beq_eq_true hm
    right
    refine ⟨hm0, ?_⟩
    cases hg0 : Nat.beq g 0 with
    | true =>
      have hgZero : g = 0 := Nat.eq_of_beq_eq_true hg0
      rw [hgZero] at hg
      nomatch hg
    | false =>
      have hZeroDiv : Nat.div 0 g = 0 := by
        have h := Nat.zero_div g
        dsimp only [HDiv.hDiv, Div.div] at h
        exact h
      dsimp only [SInt.scaleNat, SInt.divExact]
      rw [hg0, hm0, hZeroDiv]
  | false =>
    left
    have hDivNe : Nat.beq (Nat.div s.mag g) 0 = false := by
      cases hq : Nat.beq (Nat.div s.mag g) 0 with
      | false => rfl
      | true =>
        have hq0 : Nat.div s.mag g = 0 := Nat.eq_of_beq_eq_true hq
        rw [hq0, Nat.mul_zero] at hMulDiv
        rw [← hMulDiv] at hm
        nomatch hm
    have hg0 : Nat.beq g 0 = false := by
      cases hb : Nat.beq g 0 with
      | false => rfl
      | true =>
        have hgZero : g = 0 := Nat.eq_of_beq_eq_true hb
        rw [hgZero] at hg
        nomatch hg
    dsimp [SInt.scaleNat, SInt.divExact]
    rw [hg0, hDivNe, hMulDiv]

theorem sint_divExact_toInt (g : Nat) (s : SInt)
    (hg : 0 < g) (hd : Nat.mod s.mag g = 0) :
    Int.mul (Int.ofNat g) (SInt.divExact g s).toInt = s.toInt := by
  rw [← sint_scaleNat_toInt]
  cases sint_divExact_scale g s hg hd with
  | inl hEq => rw [hEq]
  | inr hPair =>
    rw [hPair.2]
    cases hN : s.neg with
    | false => dsimp [SInt.toInt, SInt.zero]; rw [hN, hPair.1]; rfl
    | true => dsimp [SInt.toInt, SInt.zero]; rw [hN, hPair.1]; rfl

theorem chvatal_gomory_floor_sound {g : Nat} {lhs : Int} {rhs : SInt}
    (hg : 0 < g) (hLe : Int.mul (Int.ofNat g) lhs ≤ rhs.toInt) :
    lhs ≤ (SInt.fdiv rhs g).toInt := by
  have hl := intBalance_self lhs
  have hgl := intBalance_mul_nat g hl
  have hr := sint_intBalance rhs
  have hNat : g * intPos lhs + rhs.negPart ≤ rhs.posPart + g * intNeg lhs :=
    (intBalance_le hgl hr).1 hLe
  cases hNeg : rhs.neg with
  | false =>
    dsimp [SInt.posPart, SInt.negPart] at hNat
    rw [hNeg, Nat.add_zero] at hNat
    have hr' : IntBalance (SInt.fdiv rhs g).toInt (Nat.div rhs.mag g) 0 := by
      dsimp [SInt.fdiv]; rw [hNeg]; exact intBalance_ofNat (Nat.div rhs.mag g)
    apply (intBalance_le hl hr').2
    rw [Nat.add_zero]
    cases Nat.lt_or_ge (intPos lhs) (intNeg lhs) with
    | inl hLt =>
      exact Nat.le_trans (Nat.le_of_lt hLt)
        (Nat.le_add_left (intNeg lhs) (Nat.div rhs.mag g))
    | inr hGe =>
      have hDiffMul : g * (intPos lhs - intNeg lhs) ≤ rhs.mag := by
        dsimp only at hNat
        have hAdded :
            g * (intPos lhs - intNeg lhs) + g * intNeg lhs ≤
              rhs.mag + g * intNeg lhs := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hGe]
          exact hNat
        exact Nat.le_of_add_le_add_right hAdded
      have hDiv : intPos lhs - intNeg lhs ≤ Nat.div rhs.mag g := by
        rw [Nat.mul_comm] at hDiffMul
        exact (Nat.le_div_iff_mul_le hg).2 hDiffMul
      have hAdd := Nat.add_le_add_right hDiv (intNeg lhs)
      rw [Nat.sub_add_cancel hGe] at hAdd
      exact hAdd
  | true =>
    cases hMag : rhs.mag with
    | zero =>
      dsimp [SInt.posPart, SInt.negPart] at hNat
      rw [hNeg, hMag, Nat.add_zero, Nat.zero_add] at hNat
      have hr' : IntBalance (SInt.fdiv rhs g).toInt 0 0 := by
        dsimp [SInt.fdiv]; rw [hNeg, hMag]; exact intBalance_ofNat 0
      apply (intBalance_le hl hr').2
      rw [Nat.add_zero, Nat.zero_add]
      exact Nat.le_of_mul_le_mul_left hNat hg
    | succ m =>
      dsimp [SInt.posPart, SInt.negPart] at hNat
      rw [hNeg, hMag, Nat.zero_add] at hNat
      have hr' : IntBalance (SInt.fdiv rhs g).toInt 0 (Nat.div m g + 1) := by
        dsimp [SInt.fdiv]; rw [hNeg, hMag]
        exact intBalance_negOfNat (Nat.div m g + 1)
      apply (intBalance_le hl hr').2
      rw [Nat.zero_add]
      cases Nat.lt_or_ge (intNeg lhs) (intPos lhs + (Nat.div m g + 1)) with
      | inr hGe => exact hGe
      | inl hLt =>
        have hLeSub : intNeg lhs ≤ intPos lhs + Nat.div m g :=
          Nat.le_of_lt_succ hLt
        have hMulLe : g * intNeg lhs ≤ g * intPos lhs + g * Nat.div m g := by
          rw [← Nat.mul_add]
          exact Nat.mul_le_mul_left g hLeSub
        have hDivMul : g * Nat.div m g ≤ m := by
          rw [Nat.mul_comm]
          exact Nat.div_mul_le_self m g
        have hUp : g * intNeg lhs ≤ g * intPos lhs + m :=
          Nat.le_trans hMulLe (Nat.add_le_add_left hDivMul (g * intPos lhs))
        have hBad : g * intPos lhs + m + 1 ≤ g * intPos lhs + m :=
          Nat.le_trans hNat hUp
        exact False.elim (Nat.not_succ_le_self (g * intPos lhs + m) hBad)

/-! ## 3. Surface `Int` & `Nat` ASTs and Sparse Cut Certifier -/

noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i + 1 => listGet? xs i

noncomputable def envLookupInt (env : List Int) (idx : Nat) : Int :=
  match listGet? env idx with
  | some v => v
  | none => 0

noncomputable def envLookupNat (env : List Nat) (idx : Nat) : Nat :=
  match listGet? env idx with
  | some v => v
  | none => 0

inductive IntLinExpr where
  | cst  (c : SInt)
  | var  (idx : Nat)
  | add  (a b : IntLinExpr)
  | sub  (a b : IntLinExpr)
  | neg  (a : IntLinExpr)
  | mulC (k : SInt) (a : IntLinExpr)

noncomputable def IntLinExpr.eval (env : List Int) : IntLinExpr → Int
  | .cst c => c.toInt
  | .var idx => envLookupInt env idx
  | .add a b => Int.add (a.eval env) (b.eval env)
  | .sub a b => Int.sub (a.eval env) (b.eval env)
  | .neg a => Int.neg (a.eval env)
  | .mulC k a => Int.mul k.toInt (a.eval env)

structure IntCutIneq where
  lhs : IntLinExpr
  rhs : IntLinExpr

def IntCutIneq.holds (env : List Int) (iq : IntCutIneq) : Prop :=
  iq.lhs.eval env ≤ iq.rhs.eval env

def HypsImp {α : Type} (holds : α → Prop) (xs : List α) (post : Prop) : Prop :=
  List.foldr (fun h acc => holds h → acc) post xs

structure IntCutGoal where
  hyps  : List IntCutIneq
  concl : IntCutIneq

def IntCutGoal.denote (g : IntCutGoal) : Prop :=
  ∀ env : List Int, HypsImp (IntCutIneq.holds env) g.hyps (g.concl.holds env)

inductive NatLinExpr where
  | cst  (n : Nat)
  | var  (idx : Nat)
  | add  (a b : NatLinExpr)
  | mulC (k : Nat) (a : NatLinExpr)

noncomputable def NatLinExpr.eval (env : List Nat) : NatLinExpr → Nat
  | .cst n => n
  | .var idx => envLookupNat env idx
  | .add a b => a.eval env + b.eval env
  | .mulC k a => k * a.eval env

noncomputable def NatLinExpr.toIntExpr : NatLinExpr → IntLinExpr
  | .cst n => .cst ⟨false, n⟩
  | .var idx => .var idx
  | .add a b => .add a.toIntExpr b.toIntExpr
  | .mulC k a => .mulC ⟨false, k⟩ a.toIntExpr

theorem natLinExpr_toInt_eval (env : List Nat) :
    ∀ e : NatLinExpr,
      e.toIntExpr.eval (env.map Int.ofNat) = Int.ofNat (e.eval env)
  | .cst _ => rfl
  | .var idx => by
    dsimp [NatLinExpr.toIntExpr, IntLinExpr.eval, NatLinExpr.eval,
           envLookupInt, envLookupNat]
    revert idx
    induction env with
    | nil => intro idx; cases idx <;> rfl
    | cons _ _ ih =>
      intro idx
      cases idx with
      | zero => rfl
      | succ i => exact ih i
  | .add a b => by
    dsimp [NatLinExpr.toIntExpr, IntLinExpr.eval, NatLinExpr.eval]
    rw [natLinExpr_toInt_eval env a, natLinExpr_toInt_eval env b]
    rfl
  | .mulC _ a => by
    dsimp [NatLinExpr.toIntExpr, IntLinExpr.eval, NatLinExpr.eval]
    rw [natLinExpr_toInt_eval env a]
    rfl

structure NatCutIneq where
  lhs : NatLinExpr
  rhs : NatLinExpr

def NatCutIneq.holds (env : List Nat) (iq : NatCutIneq) : Prop :=
  iq.lhs.eval env ≤ iq.rhs.eval env

noncomputable def NatCutIneq.toIntIneq (iq : NatCutIneq) : IntCutIneq :=
  ⟨iq.lhs.toIntExpr, iq.rhs.toIntExpr⟩

structure NatCutGoal where
  hyps  : List NatCutIneq
  concl : NatCutIneq

def NatCutGoal.denote (g : NatCutGoal) : Prop :=
  ∀ env : List Nat, HypsImp (NatCutIneq.holds env) g.hyps (g.concl.holds env)

structure SparseIneq where
  terms : List (Nat × SInt)
  rhs   : SInt

noncomputable def evalTerms (env : List Int) : List (Nat × SInt) → Int
  | [] => 0
  | (v, c) :: rest =>
    Int.add (Int.mul c.toInt (envLookupInt env v)) (evalTerms env rest)

def SparseIneq.holds (env : List Int) (row : SparseIneq) : Prop :=
  evalTerms env row.terms ≤ row.rhs.toInt

noncomputable def addTermsAux (v1 : Nat) (c1 : SInt) (tail1 : List (Nat × SInt))
    (rec1 : List (Nat × SInt) → List (Nat × SInt)) :
    List (Nat × SInt) → List (Nat × SInt)
  | [] => (v1, c1) :: tail1
  | (v2, c2) :: rest2 =>
    match Nat.blt v1 v2 with
    | true => (v1, c1) :: rec1 ((v2, c2) :: rest2)
    | false =>
      match Nat.beq v1 v2 with
      | true =>
        let sum := SInt.add c1 c2
        match sum.isZero with
        | true => rec1 rest2
        | false => (v1, sum) :: rec1 rest2
      | false => (v2, c2) :: addTermsAux v1 c1 tail1 rec1 rest2

noncomputable def addTerms :
    List (Nat × SInt) → List (Nat × SInt) → List (Nat × SInt)
  | [] => fun t2 => t2
  | (v1, c1) :: rest1 => addTermsAux v1 c1 rest1 (addTerms rest1)

theorem int_add_comm (a b : Int) : Int.add a b = Int.add b a :=
  intBalance_eq_of_eq (intBalance_add (intBalance_self a) (intBalance_self b))
    (intBalance_iff_of_add_eq
      (intBalance_add (intBalance_self b) (intBalance_self a))
      (by rw [Nat.add_comm (intPos b) (intPos a),
              Nat.add_comm (intNeg b) (intNeg a)]))

theorem int_add_assoc (a b c : Int) :
    Int.add (Int.add a b) c = Int.add a (Int.add b c) :=
  intBalance_eq_of_eq
    (intBalance_add (intBalance_add (intBalance_self a) (intBalance_self b))
      (intBalance_self c))
    (intBalance_iff_of_add_eq
      (intBalance_add (intBalance_self a)
        (intBalance_add (intBalance_self b) (intBalance_self c)))
      (by rw [Nat.add_assoc (intPos a) (intPos b) (intPos c),
              Nat.add_assoc (intNeg a) (intNeg b) (intNeg c)]))

theorem int_zero_add (a : Int) : Int.add 0 a = a :=
  intBalance_eq_of_eq
    (intBalance_iff_of_add_eq
      (intBalance_add (intBalance_ofNat 0) (intBalance_self a))
      (by rw [Nat.zero_add, Nat.zero_add]))
    (intBalance_self a)

theorem int_add_zero (a : Int) : Int.add a 0 = a := by
  rw [int_add_comm]; exact int_zero_add a

theorem int_mul_add (a b c : Int) :
    Int.mul a (Int.add b c) = Int.add (Int.mul a b) (Int.mul a c) := by
  have ha := intBalance_self a
  have hb := intBalance_self b
  have hc := intBalance_self c
  have hL := intBalance_mul ha (intBalance_add hb hc)
  have hR := intBalance_add (intBalance_mul ha hb) (intBalance_mul ha hc)
  apply intBalance_eq_of_eq hL
  apply intBalance_iff_of_add_eq hR
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  rw [add_four_rearrange (intPos a * intPos b) (intPos a * intPos c)
        (intNeg a * intNeg b) (intNeg a * intNeg c)]
  rw [add_four_rearrange (intPos a * intNeg b) (intPos a * intNeg c)
        (intNeg a * intPos b) (intNeg a * intPos c)]

theorem int_add_mul (a b c : Int) :
    Int.mul (Int.add a b) c = Int.add (Int.mul a c) (Int.mul b c) := by
  have ha := intBalance_self a
  have hb := intBalance_self b
  have hc := intBalance_self c
  have hL := intBalance_mul (intBalance_add ha hb) hc
  have hR := intBalance_add (intBalance_mul ha hc) (intBalance_mul hb hc)
  apply intBalance_eq_of_eq hL
  apply intBalance_iff_of_add_eq hR
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
  rw [add_four_rearrange (intPos a * intPos c) (intPos b * intPos c)
        (intNeg a * intNeg c) (intNeg b * intNeg c)]
  rw [add_four_rearrange (intPos a * intNeg c) (intPos b * intNeg c)
        (intNeg a * intPos c) (intNeg b * intPos c)]

theorem int_mul_assoc (a b c : Int) :
    Int.mul (Int.mul a b) c = Int.mul a (Int.mul b c) := by
  have ha := intBalance_self a
  have hb := intBalance_self b
  have hc := intBalance_self c
  have hL := intBalance_mul (intBalance_mul ha hb) hc
  have hR := intBalance_mul ha (intBalance_mul hb hc)
  apply intBalance_eq_of_eq hL
  apply intBalance_iff_of_add_eq hR
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
  rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
  have hSwap :
      (intPos a * (intPos b * intPos c) + intNeg a * (intNeg b * intPos c)) +
      (intPos a * (intNeg b * intNeg c) + intNeg a * (intPos b * intNeg c)) =
      (intPos a * (intPos b * intPos c) + intPos a * (intNeg b * intNeg c)) +
      (intNeg a * (intPos b * intNeg c) + intNeg a * (intNeg b * intPos c)) := by
    rw [add_four_rearrange]
    rw [Nat.add_comm (intNeg a * (intNeg b * intPos c))
          (intNeg a * (intPos b * intNeg c))]
  have hSwap2 :
      (intPos a * (intPos b * intNeg c) + intNeg a * (intNeg b * intNeg c)) +
      (intPos a * (intNeg b * intPos c) + intNeg a * (intPos b * intPos c)) =
      (intPos a * (intPos b * intNeg c) + intPos a * (intNeg b * intPos c)) +
      (intNeg a * (intPos b * intPos c) + intNeg a * (intNeg b * intNeg c)) := by
    rw [add_four_rearrange]
    rw [Nat.add_comm (intNeg a * (intNeg b * intNeg c))
          (intNeg a * (intPos b * intPos c))]
  rw [hSwap, hSwap2]

theorem int_zero_mul (a : Int) : Int.mul 0 a = 0 :=
  intBalance_eq_of_eq
    (intBalance_iff_of_add_eq
      (intBalance_mul (intBalance_ofNat 0) (intBalance_self a))
      (by rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero]))
    (intBalance_ofNat 0)

theorem int_neg_toInt_zero (s : SInt) (h : s.isZero = true) : s.toInt = 0 := by
  have hm : s.mag = 0 := Nat.eq_of_beq_eq_true h
  cases hN : s.neg with
  | false => dsimp [SInt.toInt]; rw [hN, hm]; rfl
  | true => dsimp [SInt.toInt]; rw [hN, hm]; rfl

theorem evalTerms_addAux (env : List Int) (v1 : Nat) (c1 : SInt)
    (tail1 : List (Nat × SInt))
    (rec1 : List (Nat × SInt) → List (Nat × SInt))
    (hRec : ∀ t, evalTerms env (rec1 t) =
      Int.add (evalTerms env tail1) (evalTerms env t)) :
    ∀ t2 : List (Nat × SInt),
      evalTerms env (addTermsAux v1 c1 tail1 rec1 t2) =
        Int.add (Int.add (Int.mul c1.toInt (envLookupInt env v1))
          (evalTerms env tail1)) (evalTerms env t2)
  | [] => by dsimp [addTermsAux, evalTerms]; rw [int_add_zero]
  | (v2, c2) :: rest2 => by
    dsimp [addTermsAux]
    cases hLt : Nat.blt v1 v2 with
    | true =>
      dsimp [evalTerms]
      rw [hRec ((v2, c2) :: rest2), int_add_assoc]
      rfl
    | false =>
      cases hEq : Nat.beq v1 v2 with
      | true =>
        have hV : v1 = v2 := Nat.eq_of_beq_eq_true hEq
        dsimp
        cases hZ : (SInt.add c1 c2).isZero with
        | true =>
          rw [hRec rest2]
          dsimp [evalTerms]
          have hSumZero : Int.add c1.toInt c2.toInt = 0 := by
            rw [← sint_add_toInt]; exact int_neg_toInt_zero _ hZ
          rw [← hV]
          have hComb :
              Int.add (Int.mul c1.toInt (envLookupInt env v1))
                (Int.mul c2.toInt (envLookupInt env v1)) = 0 := by
            rw [← int_add_mul, hSumZero, int_zero_mul]
          have hRearr :
              Int.add (Int.add (Int.mul c1.toInt (envLookupInt env v1))
                (evalTerms env tail1))
                (Int.add (Int.mul c2.toInt (envLookupInt env v1))
                  (evalTerms env rest2)) =
              Int.add (Int.add (Int.mul c1.toInt (envLookupInt env v1))
                (Int.mul c2.toInt (envLookupInt env v1)))
                (Int.add (evalTerms env tail1) (evalTerms env rest2)) := by
            rw [int_add_assoc, int_add_assoc]
            rw [← int_add_assoc (evalTerms env tail1),
                int_add_comm (evalTerms env tail1) (Int.mul c2.toInt _)]
            rw [int_add_assoc (Int.mul c2.toInt _)]
          rw [hRearr, hComb, int_zero_add]
        | false =>
          dsimp only [evalTerms]
          rw [hRec rest2, sint_add_toInt, int_add_mul, ← hV]
          rw [int_add_assoc, int_add_assoc]
          rw [← int_add_assoc (Int.mul c2.toInt _),
              int_add_comm (Int.mul c2.toInt _) (evalTerms env tail1)]
          rw [int_add_assoc (evalTerms env tail1)]
      | false =>
        dsimp only [evalTerms]
        rw [evalTerms_addAux env v1 c1 tail1 rec1 hRec rest2]
        rw [← int_add_assoc, int_add_comm (Int.mul c2.toInt _), int_add_assoc]

theorem evalTerms_add (env : List Int) :
    ∀ t1 t2 : List (Nat × SInt),
      evalTerms env (addTerms t1 t2) =
        Int.add (evalTerms env t1) (evalTerms env t2)
  | [], _ => by dsimp [addTerms, evalTerms]; rw [int_zero_add]
  | (v1, c1) :: rest1, t2 => by
    dsimp [addTerms]
    exact evalTerms_addAux env v1 c1 rest1 (addTerms rest1)
      (evalTerms_add env rest1) t2

noncomputable def scaleTermsNat (k : Nat) :
    List (Nat × SInt) → List (Nat × SInt)
  | [] => []
  | (v, c) :: rest =>
    let scaled := SInt.scaleNat k c
    match scaled.isZero with
    | true => scaleTermsNat k rest
    | false => (v, scaled) :: scaleTermsNat k rest

noncomputable def scaleTermsSInt (k : SInt) :
    List (Nat × SInt) → List (Nat × SInt)
  | [] => []
  | (v, c) :: rest =>
    let scaled := SInt.mul k c
    match scaled.isZero with
    | true => scaleTermsSInt k rest
    | false => (v, scaled) :: scaleTermsSInt k rest

theorem evalTerms_scaleNat (env : List Int) (k : Nat) :
    ∀ ts : List (Nat × SInt),
      evalTerms env (scaleTermsNat k ts) =
        Int.mul (Int.ofNat k) (evalTerms env ts)
  | [] => by
    dsimp only [scaleTermsNat, evalTerms]
    exact intBalance_eq_of_eq (intBalance_ofNat 0)
      (intBalance_mul_nat k (intBalance_ofNat 0))
  | (_, c) :: rest => by
    dsimp only [scaleTermsNat, evalTerms]
    cases hz : (SInt.scaleNat k c).isZero with
    | true =>
      rw [evalTerms_scaleNat env k rest, int_mul_add, ← int_mul_assoc]
      have hK0 : Int.mul (Int.ofNat k) c.toInt = 0 := by
        rw [← sint_scaleNat_toInt, int_neg_toInt_zero _ hz]
      rw [hK0, int_zero_mul, int_zero_add]
    | false =>
      dsimp only [evalTerms]
      rw [evalTerms_scaleNat env k rest, int_mul_add, ← int_mul_assoc,
          sint_scaleNat_toInt]

theorem evalTerms_scaleSInt (env : List Int) (k : SInt) :
    ∀ ts : List (Nat × SInt),
      evalTerms env (scaleTermsSInt k ts) =
        Int.mul k.toInt (evalTerms env ts)
  | [] => by
    dsimp only [scaleTermsSInt, evalTerms]
    exact intBalance_eq_of_eq (intBalance_ofNat 0)
      (intBalance_mul (sint_intBalance k) (intBalance_ofNat 0))
  | (_, c) :: rest => by
    dsimp only [scaleTermsSInt, evalTerms]
    cases hz : (SInt.mul k c).isZero with
    | true =>
      rw [evalTerms_scaleSInt env k rest, int_mul_add, ← int_mul_assoc]
      have hK0 : Int.mul k.toInt c.toInt = 0 := by
        rw [← sint_mul_toInt, int_neg_toInt_zero _ hz]
      rw [hK0, int_zero_mul, int_zero_add]
    | false =>
      dsimp only [evalTerms]
      rw [evalTerms_scaleSInt env k rest, int_mul_add, ← int_mul_assoc,
          sint_mul_toInt]

noncomputable def normIntLinExpr : IntLinExpr → List (Nat × SInt) × SInt
  | .cst c => ([], c)
  | .var idx => ([(idx, SInt.one)], SInt.zero)
  | .add a b =>
    let na := normIntLinExpr a
    let nb := normIntLinExpr b
    (addTerms na.1 nb.1, SInt.add na.2 nb.2)
  | .sub a b =>
    let na := normIntLinExpr a
    let nb := normIntLinExpr b
    (addTerms na.1 (scaleTermsSInt SInt.negOne nb.1), SInt.sub na.2 nb.2)
  | .neg a =>
    let na := normIntLinExpr a
    (scaleTermsSInt SInt.negOne na.1, SInt.negate na.2)
  | .mulC k a =>
    let na := normIntLinExpr a
    (scaleTermsSInt k na.1, SInt.mul k na.2)

theorem int_one_mul (a : Int) : Int.mul 1 a = a :=
  intBalance_eq_of_eq
    (intBalance_iff_of_add_eq (intBalance_mul_nat 1 (intBalance_self a))
      (by rw [Nat.one_mul, Nat.one_mul]))
    (intBalance_self a)

theorem int_negOne_mul (a : Int) : Int.mul (SInt.negOne).toInt a = Int.neg a :=
  intBalance_eq_of_eq
    (intBalance_mul (intBalance_negOfNat 1) (intBalance_self a))
    (intBalance_iff_of_add_eq (intBalance_neg (intBalance_self a))
      (by simp only [Nat.zero_mul, Nat.one_mul, Nat.zero_add]))

theorem int_sub_eq_add_neg (a b : Int) :
    Int.sub a b = Int.add a (Int.neg b) := rfl

theorem normIntLinExpr_sound (env : List Int) :
    ∀ e : IntLinExpr,
      Int.add (evalTerms env (normIntLinExpr e).1)
        (normIntLinExpr e).2.toInt = e.eval env
  | .cst c => by
    dsimp [normIntLinExpr, evalTerms, IntLinExpr.eval]
    exact int_zero_add c.toInt
  | .var _ => by
    dsimp [normIntLinExpr, evalTerms, IntLinExpr.eval, SInt.one, SInt.zero,
           SInt.toInt]
    rw [int_add_zero, int_add_zero, int_one_mul]
  | .add a b => by
    dsimp [normIntLinExpr, IntLinExpr.eval]
    rw [evalTerms_add, sint_add_toInt]
    rw [← normIntLinExpr_sound env a, ← normIntLinExpr_sound env b]
    rw [int_add_assoc, int_add_assoc]
    rw [← int_add_assoc (evalTerms env (normIntLinExpr b).1)]
    rw [int_add_comm (evalTerms env (normIntLinExpr b).1)
          (normIntLinExpr a).2.toInt]
    rw [int_add_assoc (normIntLinExpr a).2.toInt]
  | .sub a b => by
    dsimp [normIntLinExpr, IntLinExpr.eval, SInt.sub]
    rw [evalTerms_add, evalTerms_scaleSInt, sint_add_toInt]
    have hNegC :
        (SInt.negate (normIntLinExpr b).2).toInt =
          Int.neg (normIntLinExpr b).2.toInt :=
      intBalance_eq_of_eq (sint_negate_balance _)
        (intBalance_neg (sint_intBalance _))
    rw [hNegC, int_negOne_mul, int_sub_eq_add_neg]
    rw [← normIntLinExpr_sound env a, ← normIntLinExpr_sound env b]
    have hNegAdd :
        Int.neg (Int.add (evalTerms env (normIntLinExpr b).1)
          (normIntLinExpr b).2.toInt) =
        Int.add (Int.neg (evalTerms env (normIntLinExpr b).1))
          (Int.neg (normIntLinExpr b).2.toInt) :=
      intBalance_eq_of_eq
        (intBalance_neg (intBalance_add (intBalance_self _)
          (intBalance_self _)))
        (intBalance_add (intBalance_neg (intBalance_self _))
          (intBalance_neg (intBalance_self _)))
    rw [hNegAdd, int_add_assoc, int_add_assoc]
    rw [← int_add_assoc (Int.neg (evalTerms env (normIntLinExpr b).1))]
    rw [int_add_comm (Int.neg (evalTerms env (normIntLinExpr b).1))
          (normIntLinExpr a).2.toInt]
    rw [int_add_assoc (normIntLinExpr a).2.toInt]
  | .neg a => by
    dsimp [normIntLinExpr, IntLinExpr.eval]
    rw [evalTerms_scaleSInt, int_negOne_mul]
    have hNegC :
        (SInt.negate (normIntLinExpr a).2).toInt =
          Int.neg (normIntLinExpr a).2.toInt :=
      intBalance_eq_of_eq (sint_negate_balance _)
        (intBalance_neg (sint_intBalance _))
    rw [hNegC, ← normIntLinExpr_sound env a]
    exact intBalance_eq_of_eq
      (intBalance_add (intBalance_neg (intBalance_self _))
        (intBalance_neg (intBalance_self _)))
      (intBalance_neg (intBalance_add (intBalance_self _) (intBalance_self _)))
  | .mulC k a => by
    dsimp [normIntLinExpr, IntLinExpr.eval]
    rw [evalTerms_scaleSInt, sint_mul_toInt, ← int_mul_add,
        normIntLinExpr_sound env a]

noncomputable def ineqToSparse (iq : IntCutIneq) : SparseIneq :=
  let n := normIntLinExpr (.sub iq.lhs iq.rhs)
  ⟨n.1, SInt.negate n.2⟩

theorem ineqToSparse_sound (env : List Int) (iq : IntCutIneq) :
    iq.holds env → (ineqToSparse iq).holds env := by
  intro hLe
  dsimp [ineqToSparse, SparseIneq.holds]
  have hN := normIntLinExpr_sound env (.sub iq.lhs iq.rhs)
  dsimp [IntLinExpr.eval] at hN
  have hDiff : Int.sub (iq.lhs.eval env) (iq.rhs.eval env) ≤ 0 := by
    have ha := intBalance_self (iq.lhs.eval env)
    have hb := intBalance_self (iq.rhs.eval env)
    apply (intBalance_le (intBalance_sub ha hb) (intBalance_ofNat 0)).2
    rw [Nat.zero_add,
        Nat.add_comm (intNeg (iq.lhs.eval env)) (intPos (iq.rhs.eval env))]
    exact (intBalance_le ha hb).1 hLe
  rw [← hN] at hDiff
  have hNegC := sint_negate_balance (normIntLinExpr (.sub iq.lhs iq.rhs)).2
  have hNegS :=
    intBalance_neg (sint_intBalance (normIntLinExpr (.sub iq.lhs iq.rhs)).2)
  have hEqNeg :
      (SInt.negate (normIntLinExpr (.sub iq.lhs iq.rhs)).2).toInt =
        Int.neg (normIntLinExpr (.sub iq.lhs iq.rhs)).2.toInt :=
    intBalance_eq_of_eq hNegC hNegS
  rw [hEqNeg]
  have ht :=
    intBalance_self (evalTerms env (normIntLinExpr (.sub iq.lhs iq.rhs)).1)
  have hc := intBalance_self (normIntLinExpr (.sub iq.lhs iq.rhs)).2.toInt
  apply (intBalance_le ht (intBalance_neg hc)).2
  have hZero := (intBalance_le (intBalance_add ht hc) (intBalance_ofNat 0)).1
    hDiff
  rw [Nat.zero_add,
      Nat.add_comm
        (intNeg (evalTerms env (normIntLinExpr (.sub iq.lhs iq.rhs)).1))
        (intNeg (normIntLinExpr (.sub iq.lhs iq.rhs)).2.toInt)] at hZero
  exact hZero

inductive CutStep where
  | hyp    (idx : Nat)
  | comb   (s1 : Nat) (k1 : Nat) (s2 : Nat) (k2 : Nat)
  | divCut (g : Nat) (s : Nat)

noncomputable def allDivisible (g : Nat) : List (Nat × SInt) → Bool
  | [] => true
  | (_, c) :: rest => Nat.beq (Nat.mod c.mag g) 0 && allDivisible g rest

noncomputable def divTerms (g : Nat) :
    List (Nat × SInt) → List (Nat × SInt)
  | [] => []
  | (v, c) :: rest =>
    let q := SInt.divExact g c
    match q.isZero with
    | true => divTerms g rest
    | false => (v, q) :: divTerms g rest

theorem evalTerms_divTerms (env : List Int) (g : Nat) (hg : 0 < g) :
    ∀ ts : List (Nat × SInt),
      allDivisible g ts = true →
      Int.mul (Int.ofNat g) (evalTerms env (divTerms g ts)) = evalTerms env ts
  | [], _ => by
    dsimp [divTerms, evalTerms]
    exact intBalance_eq_of_eq
      (intBalance_mul_nat g (intBalance_ofNat 0)) (intBalance_ofNat 0)
  | (_, c) :: rest, hDiv => by
    dsimp only [allDivisible] at hDiv
    revert hDiv
    cases hMod : Nat.beq (Nat.mod c.mag g) 0 with
    | false => intro h; nomatch h
    | true =>
      intro hRest
      dsimp only [Bool.and] at hRest
      have hMod0 : Nat.mod c.mag g = 0 := Nat.eq_of_beq_eq_true hMod
      have hHead := sint_divExact_toInt g c hg hMod0
      dsimp only [divTerms]
      cases hz : (SInt.divExact g c).isZero with
      | true =>
        have hC0 : c.toInt = 0 := by
          rw [← hHead, int_neg_toInt_zero _ hz]
          exact intBalance_eq_of_eq
            (intBalance_mul_nat g (intBalance_ofNat 0)) (intBalance_ofNat 0)
        dsimp only [evalTerms]
        rw [hC0, int_zero_mul, int_zero_add]
        exact evalTerms_divTerms env g hg rest hRest
      | false =>
        dsimp only [evalTerms]
        rw [int_mul_add, ← int_mul_assoc, hHead,
            evalTerms_divTerms env g hg rest hRest]

noncomputable def stepCut (hyps : List SparseIneq) (derived : List SparseIneq) :
    CutStep → Option SparseIneq
  | .hyp idx => listGet? hyps idx
  | .comb s1 k1 s2 k2 =>
    match Nat.ble k1 magCap128 && Nat.ble k2 magCap128 with
    | false => none
    | true =>
      match listGet? derived s1, listGet? derived s2 with
      | some r1, some r2 =>
        let t := addTerms (scaleTermsNat k1 r1.terms)
          (scaleTermsNat k2 r2.terms)
        let r := SInt.add (SInt.scaleNat k1 r1.rhs) (SInt.scaleNat k2 r2.rhs)
        match r.withinCap with
        | true => some ⟨t, r⟩
        | false => none
      | _, _ => none
  | .divCut g s =>
    match Nat.ble 1 g && Nat.ble g magCap128 with
    | false => none
    | true =>
      match listGet? derived s with
      | none => none
      | some row =>
        match allDivisible g row.terms with
        | false => none
        | true =>
          let r := SInt.fdiv row.rhs g
          match r.withinCap with
          | true => some ⟨divTerms g row.terms, r⟩
          | false => none

def AllHolds (env : List Int) (rows : List SparseIneq) : Prop :=
  ∀ r : SparseIneq, r ∈ rows → r.holds env

theorem allHolds_listGet {env : List Int} {rows : List SparseIneq}
    (hAll : AllHolds env rows) :
    ∀ (idx : Nat) (r : SparseIneq), listGet? rows idx = some r → r.holds env := by
  intro idx
  revert rows
  induction idx with
  | zero =>
    intro rows hAll r hGet
    cases rows with
    | nil => nomatch hGet
    | cons x xs =>
      dsimp [listGet?] at hGet
      injection hGet with hEq
      rw [← hEq]
      exact hAll x (List.Mem.head xs)
  | succ _ ih =>
    intro rows hAll r hGet
    cases rows with
    | nil => nomatch hGet
    | cons x _ =>
      dsimp [listGet?] at hGet
      apply ih (fun y hy => hAll y (List.Mem.tail x hy)) r hGet

theorem mem_of_mem_append {α : Type} {x : α} {xs ys : List α} :
    x ∈ xs ++ ys → x ∈ xs ∨ x ∈ ys := by
  induction xs with
  | nil => intro h; exact Or.inr h
  | cons a _ ih =>
    intro h
    cases h with
    | head _ => exact Or.inl (List.Mem.head _)
    | tail _ hTail =>
      cases ih hTail with
      | inl hL => exact Or.inl (List.Mem.tail a hL)
      | inr hR => exact Or.inr hR

theorem int_add_le_add {a b c d : Int} (h1 : a ≤ b) (h2 : c ≤ d) :
    Int.add a c ≤ Int.add b d := by
  have ha := intBalance_self a
  have hb := intBalance_self b
  have hc := intBalance_self c
  have hd := intBalance_self d
  have hn1 := (intBalance_le ha hb).1 h1
  have hn2 := (intBalance_le hc hd).1 h2
  apply (intBalance_le (intBalance_add ha hc) (intBalance_add hb hd)).2
  rw [add_four_rearrange (intPos a) (intPos c) (intNeg b) (intNeg d)]
  rw [add_four_rearrange (intPos b) (intPos d) (intNeg a) (intNeg c)]
  exact Nat.add_le_add hn1 hn2

theorem int_mul_nat_le_mul_nat (k : Nat) {a b : Int} (h : a ≤ b) :
    Int.mul (Int.ofNat k) a ≤ Int.mul (Int.ofNat k) b := by
  have ha := intBalance_self a
  have hb := intBalance_self b
  have hn := (intBalance_le ha hb).1 h
  apply (intBalance_le (intBalance_mul_nat k ha) (intBalance_mul_nat k hb)).2
  rw [← Nat.mul_add, ← Nat.mul_add]
  exact Nat.mul_le_mul_left k hn

theorem stepCut_sound {env : List Int} {hyps derived : List SparseIneq}
    {st : CutStep} {out : SparseIneq}
    (hHyps : AllHolds env hyps) (hDer : AllHolds env derived)
    (hStep : stepCut hyps derived st = some out) :
    out.holds env := by
  cases st with
  | hyp idx =>
    dsimp [stepCut] at hStep
    exact allHolds_listGet hHyps idx out hStep
  | comb s1 k1 s2 k2 =>
    dsimp [stepCut] at hStep
    revert hStep
    cases Nat.ble k1 magCap128 && Nat.ble k2 magCap128 with
    | false => intro h; nomatch h
    | true =>
      cases hg1 : listGet? derived s1 with
      | none => intro h; nomatch h
      | some r1 =>
        cases hg2 : listGet? derived s2 with
        | none => intro h; nomatch h
        | some r2 =>
          dsimp
          cases (SInt.add (SInt.scaleNat k1 r1.rhs)
                  (SInt.scaleNat k2 r2.rhs)).withinCap with
          | false => intro h; nomatch h
          | true =>
            intro hEq
            injection hEq with hOut
            rw [← hOut]
            dsimp [SparseIneq.holds]
            rw [evalTerms_add, evalTerms_scaleNat, evalTerms_scaleNat,
                sint_add_toInt, sint_scaleNat_toInt, sint_scaleNat_toInt]
            have h1 :=
              int_mul_nat_le_mul_nat k1 (allHolds_listGet hDer s1 r1 hg1)
            have h2 :=
              int_mul_nat_le_mul_nat k2 (allHolds_listGet hDer s2 r2 hg2)
            exact int_add_le_add h1 h2
  | divCut g s =>
    dsimp [stepCut] at hStep
    revert hStep
    cases hg : Nat.ble 1 g && Nat.ble g magCap128 with
    | false => intro h; nomatch h
    | true =>
      cases hGet : listGet? derived s with
      | none => intro h; nomatch h
      | some row =>
        dsimp
        cases hDiv : allDivisible g row.terms with
        | false => intro h; nomatch h
        | true =>
          dsimp
          cases (SInt.fdiv row.rhs g).withinCap with
          | false => intro h; nomatch h
          | true =>
            intro hEq
            injection hEq with hOut
            rw [← hOut]
            dsimp [SparseIneq.holds]
            have hg1 : Nat.ble 1 g = true := by
              cases hb : Nat.ble 1 g with
              | true => rfl
              | false => rw [hb] at hg; nomatch hg
            have hgPos : 0 < g := Nat.le_of_ble_eq_true hg1
            have hRow := allHolds_listGet hDer s row hGet
            dsimp [SparseIneq.holds] at hRow
            rw [← evalTerms_divTerms env g hgPos row.terms hDiv] at hRow
            exact chvatal_gomory_floor_sound hgPos hRow

noncomputable def runCutStepsAux (hyps : List SparseIneq) :
    List CutStep → List SparseIneq → Option (List SparseIneq)
  | [], acc => some acc
  | st :: rest, acc =>
    match stepCut hyps acc st with
    | none => none
    | some next => runCutStepsAux hyps rest (acc ++ [next])

noncomputable def listLast? {α : Type} : List α → Option α
  | [] => none
  | [x] => some x
  | _ :: xs => listLast? xs

theorem listLast?_mem {α : Type} :
    ∀ {xs : List α} {x : α}, listLast? xs = some x → x ∈ xs
  | [], _, h => nomatch h
  | [_], _, h => by
    dsimp [listLast?] at h
    injection h with hEq
    rw [← hEq]
    exact List.Mem.head []
  | a :: _ :: _, _, h => by
    dsimp [listLast?] at h
    exact List.Mem.tail a (listLast?_mem h)

theorem runCutStepsAux_sound {env : List Int} {hyps : List SparseIneq}
    (hHyps : AllHolds env hyps) :
    ∀ (steps : List CutStep) (acc res : List SparseIneq),
      AllHolds env acc →
      runCutStepsAux hyps steps acc = some res →
      AllHolds env res
  | [], acc, res, hAcc, hRun => by
    dsimp [runCutStepsAux] at hRun
    injection hRun with hEq
    rw [← hEq]
    exact hAcc
  | st :: rest, acc, res, hAcc, hRun => by
    dsimp [runCutStepsAux] at hRun
    revert hRun
    cases hSt : stepCut hyps acc st with
    | none => intro h; nomatch h
    | some next =>
      intro hRest
      have hNext := stepCut_sound hHyps hAcc hSt
      have hAcc' : AllHolds env (acc ++ [next]) := by
        intro r hr
        cases mem_of_mem_append hr with
        | inl hL => exact hAcc r hL
        | inr hR =>
          cases hR with
          | head _ => exact hNext
          | tail _ hNil => nomatch hNil
      exact runCutStepsAux_sound hHyps rest (acc ++ [next]) res hAcc' hRest

noncomputable def checkCutRefute (hyps : List SparseIneq)
    (steps : List CutStep) : Bool :=
  match runCutStepsAux hyps steps [] with
  | none => false
  | some derived =>
    match listLast? derived with
    | none => false
    | some last =>
      match last.terms with
      | [] => last.rhs.isStrictlyNeg
      | _ :: _ => false

theorem checkCutRefute_sound {env : List Int} {hyps : List SparseIneq}
    {steps : List CutStep}
    (hChk : checkCutRefute hyps steps = true)
    (hHyps : AllHolds env hyps) : False := by
  dsimp [checkCutRefute] at hChk
  cases hRun : runCutStepsAux hyps steps [] with
  | none => rw [hRun] at hChk; nomatch hChk
  | some derived =>
    rw [hRun] at hChk
    dsimp at hChk
    cases hLast : listLast? derived with
    | none => rw [hLast] at hChk; nomatch hChk
    | some last =>
      rw [hLast] at hChk
      dsimp at hChk
      cases hTerms : last.terms with
      | cons _ _ => rw [hTerms] at hChk; nomatch hChk
      | nil =>
        rw [hTerms] at hChk
        dsimp [SInt.isStrictlyNeg] at hChk
        have hAll :=
          runCutStepsAux_sound hHyps steps [] derived (fun _ hm => nomatch hm)
            hRun
        have hHold := hAll last (listLast?_mem hLast)
        dsimp [SparseIneq.holds] at hHold
        rw [hTerms] at hHold
        dsimp [evalTerms] at hHold
        cases hN : last.rhs.neg with
        | false => rw [hN] at hChk; nomatch hChk
        | true =>
          rw [hN] at hChk
          dsimp [Bool.and] at hChk
          have hGe1 : 1 ≤ last.rhs.mag := Nat.le_of_ble_eq_true hChk
          have hr := sint_intBalance last.rhs
          have hBad := (intBalance_le (intBalance_ofNat 0) hr).1 hHold
          dsimp [SInt.posPart, SInt.negPart] at hBad
          rw [hN, Nat.zero_add] at hBad
          dsimp only at hBad
          have hContra : 1 ≤ 0 := Nat.le_trans hGe1 hBad
          nomatch hContra

noncomputable def checkIntCutGoal (g : IntCutGoal) (steps : List CutStep) :
    Bool :=
  let negConcl : IntCutIneq := ⟨.add g.concl.rhs (.cst SInt.one), g.concl.lhs⟩
  let allSparse := (g.hyps ++ [negConcl]).map ineqToSparse
  checkCutRefute allSparse steps

theorem hypsImp_allHolds_int (env : List Int) (iqs : List IntCutIneq)
    (post : Prop)
    (hCont : (AllHolds env (iqs.map ineqToSparse)) → post) :
    HypsImp (IntCutIneq.holds env) iqs post := by
  induction iqs generalizing post with
  | nil =>
    apply hCont
    intro _ hr
    nomatch hr
  | cons iq _ ih =>
    intro hHere
    apply ih
    intro hRest
    apply hCont
    intro r hr
    dsimp [List.map] at hr
    cases hr with
    | head _ => exact ineqToSparse_sound env iq hHere
    | tail _ hTail => exact hRest r hTail

theorem checkIntCutGoal_sound (g : IntCutGoal) (steps : List CutStep)
    (hChk : checkIntCutGoal g steps = true) : g.denote := by
  intro env
  apply hypsImp_allHolds_int env g.hyps
  intro hHypsSparse
  apply int_le_of_not_succ_le
  intro hNegConcl
  let negConcl : IntCutIneq := ⟨.add g.concl.rhs (.cst SInt.one), g.concl.lhs⟩
  have hNegSparse : (ineqToSparse negConcl).holds env :=
    ineqToSparse_sound env negConcl hNegConcl
  apply checkCutRefute_sound hChk (env := env)
  intro r hr
  have hMap :
      (g.hyps ++ [negConcl]).map ineqToSparse =
        g.hyps.map ineqToSparse ++ [ineqToSparse negConcl] := by
    induction g.hyps with
    | nil => rfl
    | cons _ _ ih => dsimp [List.map]; rw [ih]
  rw [hMap] at hr
  cases mem_of_mem_append hr with
  | inl hL => exact hHypsSparse r hL
  | inr hR =>
    cases hR with
    | head _ => exact hNegSparse
    | tail _ hNil => nomatch hNil

noncomputable def checkNatCutGoal (g : NatCutGoal) (steps : List CutStep) :
    Bool :=
  let intG : IntCutGoal :=
    ⟨g.hyps.map NatCutIneq.toIntIneq, g.concl.toIntIneq⟩
  checkIntCutGoal intG steps

theorem hypsImp_nat_to_int (env : List Nat) (iqs : List NatCutIneq)
    (post : Prop)
    (hInt : HypsImp (IntCutIneq.holds (env.map Int.ofNat))
              (iqs.map NatCutIneq.toIntIneq) post) :
    HypsImp (NatCutIneq.holds env) iqs post := by
  induction iqs with
  | nil => exact hInt
  | cons iq _ ih =>
    intro hNat
    apply ih
    apply hInt
    dsimp [NatCutIneq.toIntIneq, IntCutIneq.holds]
    rw [natLinExpr_toInt_eval env iq.lhs, natLinExpr_toInt_eval env iq.rhs]
    exact (intBalance_le (intBalance_ofNat _) (intBalance_ofNat _)).2 hNat

theorem hypsImp_concl_mono {α : Type} {f : α → Prop} {p q : Prop}
    (hpq : p → q) : ∀ {xs : List α}, HypsImp f xs p → HypsImp f xs q
  | [], h => hpq h
  | _ :: _, h => fun ha => hypsImp_concl_mono hpq (h ha)

/-- Master `Nat` linear-inequality reflection theorem: replaces `omega` in
Pass-1 `theory/` and `correspondence/` modules via `rfl` or `decide`. -/
theorem checkNatCutGoal_sound (g : NatCutGoal) (steps : List CutStep)
    (hChk : checkNatCutGoal g steps = true) : g.denote := by
  intro env
  have hInt := checkIntCutGoal_sound _ steps hChk (env.map Int.ofNat)
  apply hypsImp_nat_to_int env g.hyps
  refine hypsImp_concl_mono ?_ hInt
  intro hC
  dsimp [NatCutIneq.toIntIneq, IntCutIneq.holds] at hC
  rw [natLinExpr_toInt_eval env g.concl.lhs,
      natLinExpr_toInt_eval env g.concl.rhs] at hC
  exact (intBalance_le (intBalance_ofNat _) (intBalance_ofNat _)).1 hC

/-! ## 4. Built-In Parity Canary (`2 * i + 1 <= 2 * n -> i < n`) -/

def parityStrideGoal : NatCutGoal :=
  let i := NatLinExpr.var 0
  let n := NatLinExpr.var 1
  { hyps := [⟨.add (.mulC 2 i) (.cst 1), .mulC 2 n⟩]
    concl := ⟨.add i (.cst 1), n⟩ }

def parityStrideCert : List CutStep :=
  [ .hyp 0
  , .divCut 2 0
  , .hyp 1
  , .comb 1 1 2 1
  ]

theorem parity_stride_lt (i n : Nat) (h : 2 * i + 1 ≤ 2 * n) : i < n :=
  checkNatCutGoal_sound parityStrideGoal parityStrideCert rfl [i, n] h

end Workbench.Pass1.LinearArith
