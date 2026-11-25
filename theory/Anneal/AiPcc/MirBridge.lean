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
import Init.Data.List.Basic
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine
import Anneal.Scalars
import Anneal.AiPcc.BitArith
import Anneal.AiPcc.Tnum
import Anneal.AiPcc.WrappedInterval
import Anneal.AiPcc.ReducedProduct

namespace Anneal.AiPcc

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-!
# MIR Abstract State and Scalar Bridge (`Anneal.AiPcc.MirBridge`)

Connects the reduced-product value domain `AbsVal` (`InitDom` x `Tnum` x
`WrappedInterval` x `StridedCong`) to the ground operational semantics
`Trusted.Rustc.V2026_06_01.MirSemantics` over unsigned integer (`UintTy`),
boolean, and unit locals.

* Section 1 relates `ScalarInt` arithmetic (`scalarModulus`,
  `wrapScalarBits`, `evalScalarBinOp` at `isSigned = false`, `boolToScalar`)
  to the `Nat`-level operations used by the `AbsVal` transfer theorems.
* Section 2 defines relational comparison guards (`RelGuard`), abstract
  booleans (`BoolAbs`), abstract local slots (`MirAbsSlot`) and frames
  (`MirAbsEnv`), their concretizations against `List LocalSlot`, the
  lattice order and join, guard-clearing writes (`setMirAbsSlot`), and branch
  refinements (`refineEnvByGuard`), all consumed by `Anneal.AiPcc.MirTransfer`.

Integer widths follow `intCastTargetBytes`: `usize` is 8 bytes wide, exactly
as in the `CastKind.intToInt` arm of `evalRvalue`; scalars of any other byte
width at a `usize` local are simply not denoted (fail-closed).
-/

/-! ## 1. Unsigned Widths and `evalScalarBinOp` Bridge -/

/-- Byte width of an unsigned integer type (`usize` is 8 bytes, matching
`intCastTargetBytes`). -/
def uintBytes : UintTy → Nat
  | .u8 => 1
  | .u16 => 2
  | .u32 => 4
  | .u64 => 8
  | .u128 => 16
  | .usize => 8

/-- Bit width (`8 * uintBytes u`) of an unsigned integer type. -/
def uintWidth : UintTy → Nat
  | .u8 => 8
  | .u16 => 16
  | .u32 => 32
  | .u64 => 64
  | .u128 => 128
  | .usize => 64

/-- Structural equality on `UintTy`. -/
def uintTyBeq : UintTy → UintTy → Bool
  | .u8, .u8 => true
  | .u16, .u16 => true
  | .u32, .u32 => true
  | .u64, .u64 => true
  | .u128, .u128 => true
  | .usize, .usize => true
  | _, _ => false

theorem uintTyBeq_refl (u : UintTy) : uintTyBeq u u = true := by
  cases u <;> rfl

theorem uintTy_eq_of_beq {u1 u2 : UintTy} (h : uintTyBeq u1 u2 = true) :
    u1 = u2 := by
  cases u1 <;> cases u2 <;> first | rfl | nomatch h

/-- Every `uintWidth u` is a supported `AbsVal` width. -/
theorem uintWidth_valid (u : UintTy) : validWidth (uintWidth u) = true := by
  cases u <;> rfl

/-- `scalarModulus (uintBytes u) = 2 ^ uintWidth u`. -/
theorem scalarModulus_uintBytes (u : UintTy) :
    scalarModulus (uintBytes u) = modPow2 (uintWidth u) := by
  cases u <;> rfl

theorem uintBytes_beq_zero (u : UintTy) :
    Nat.beq (uintBytes u) 0 = false := by
  cases u <;> rfl

theorem uintBytes_mul_eight (u : UintTy) :
    Nat.mul (uintBytes u) 8 = uintWidth u := by
  cases u <;> rfl

theorem intCastTargetBytes_uint (u : UintTy) :
    intCastTargetBytes (.uint u) = some (uintBytes u) := by
  cases u <;> rfl

theorem modPow2_uintWidth_mono {u1 u2 : UintTy}
    (h : Nat.ble (uintWidth u1) (uintWidth u2) = true) :
    modPow2 (uintWidth u1) ≤ modPow2 (uintWidth u2) :=
  modPow2_mono (Nat.le_of_ble_eq_true h)

/-- `wrapScalarBits` at an unsigned byte width is `wrapVal`. -/
theorem wrapScalarBits_eq_wrapVal (u : UintTy) (x : Nat) :
    wrapScalarBits x (scalarModulus (uintBytes u)) =
      wrapVal (uintWidth u) x := by
  rw [Anneal.Scalars.wrapScalarBits_eq_mod_modulus, scalarModulus_uintBytes]
  rfl

theorem wrapVal_of_lt {w x : Nat} (h : x < modPow2 w) : wrapVal w x = x :=
  nat_mod_eq_of_lt h

theorem modPow2_eq_two_pow (w : Nat) : modPow2 w = 2 ^ w := modPow2_eq_pow w

theorem wrapScalarBits_of_lt_uint {u : UintTy} {x : Nat}
    (h : x < modPow2 (uintWidth u)) :
    wrapScalarBits x (scalarModulus (uintBytes u)) = x := by
  rw [wrapScalarBits_eq_wrapVal]
  exact wrapVal_of_lt h

/-- `wrapVal w (2^w + x - y)` is the canonical modular difference for in-range
`x`, `y`, whether or not `y ≤ x`. -/
theorem wrapVal_sub_of_le {w x y : Nat} (hLe : y ≤ x) (_hx : x < modPow2 w) :
    wrapVal w (x - y) = wrapVal w (modPow2 w + x - y) := by
  dsimp only [wrapVal]
  rw [Nat.add_sub_assoc hLe]
  change (x - y) % modPow2 w = (modPow2 w + (x - y)) % modPow2 w
  rw [Nat.add_mod_left]

theorem nat_blt_eq_not_ble (a b : Nat) : Nat.blt a b = !(Nat.ble b a) := by
  cases h : Nat.ble b a with
  | true =>
    have hLe : b ≤ a := Nat.le_of_ble_eq_true h
    cases h2 : Nat.blt a b with
    | false => rfl
    | true => exact False.elim (Nat.not_le_of_gt (lt_of_blt_true h2) hLe)
  | false =>
    have hLt : a < b := Nat.lt_of_not_le (fun hLe => by
      rw [Nat.ble_eq_true_of_le hLe] at h; nomatch h)
    rw [blt_true_of_lt hLt]
    rfl

section ScalarOps

variable {u : UintTy} {a b : Nat} (locals : List LocalSlot) (mem : Memory)

/-- Unsigned wrapping `.add`. -/
theorem evalScalarBinOp_uint_add :
    evalScalarBinOp .add ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem false =
      .ok (.scalar ⟨wrapVal (uintWidth u) (a + b), uintBytes u⟩)
        locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  rw [← wrapScalarBits_eq_wrapVal]
  rfl

/-- Unsigned `.addUnchecked` without overflow. -/
theorem evalScalarBinOp_uint_addUnchecked
    (hNoOv : a + b < modPow2 (uintWidth u)) :
    evalScalarBinOp .addUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem
        false =
      .ok (.scalar ⟨wrapVal (uintWidth u) (a + b), uintBytes u⟩)
        locals mem := by
  have hB : Nat.ble (scalarModulus (uintBytes u)) (Nat.add a b) = false := by
    rw [scalarModulus_uintBytes]
    cases h : Nat.ble (modPow2 (uintWidth u)) (Nat.add a b) with
    | false => rfl
    | true => exact False.elim (Nat.not_le_of_gt hNoOv (Nat.le_of_ble_eq_true h))
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hB]
  rw [wrapVal_of_lt hNoOv]
  rfl

/-- Unsigned wrapping `.sub` for in-range operands. -/
theorem evalScalarBinOp_uint_sub
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u)) :
    evalScalarBinOp .sub ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem false =
      .ok (.scalar ⟨wrapVal (uintWidth u) (modPow2 (uintWidth u) + a - b),
        uintBytes u⟩) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  cases h : Nat.ble b a with
  | true =>
    simp only
    rw [wrapScalarBits_eq_wrapVal, show Nat.sub a b = a - b from rfl,
      wrapVal_sub_of_le (Nat.le_of_ble_eq_true h) ha]
  | false =>
    simp only
    rw [wrapScalarBits_of_lt_uint ha, wrapScalarBits_of_lt_uint hb,
      wrapScalarBits_eq_wrapVal, scalarModulus_uintBytes]
    rfl

/-- Unsigned `.subUnchecked` without underflow. -/
theorem evalScalarBinOp_uint_subUnchecked
    (ha : a < modPow2 (uintWidth u)) (hLe : b ≤ a) :
    evalScalarBinOp .subUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem
        false =
      .ok (.scalar ⟨wrapVal (uintWidth u) (modPow2 (uintWidth u) + a - b),
        uintBytes u⟩) locals mem := by
  have hDiff : a - b < modPow2 (uintWidth u) :=
    Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  have hB : Nat.ble (scalarModulus (uintBytes u)) (Nat.sub a b) = false := by
    rw [scalarModulus_uintBytes]
    cases h : Nat.ble (modPow2 (uintWidth u)) (Nat.sub a b) with
    | false => rfl
    | true => exact False.elim (Nat.not_le_of_gt hDiff (Nat.le_of_ble_eq_true h))
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl,
    Nat.ble_eq_true_of_le hLe, hB]
  rw [← wrapVal_sub_of_le hLe ha, wrapVal_of_lt hDiff]
  rfl

/-- Unsigned wrapping `.mul`. -/
theorem evalScalarBinOp_uint_mul :
    evalScalarBinOp .mul ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem false =
      .ok (.scalar ⟨wrapVal (uintWidth u) (a * b), uintBytes u⟩)
        locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  rw [← wrapScalarBits_eq_wrapVal]
  rfl

/-- Unsigned `.mulUnchecked` without overflow. -/
theorem evalScalarBinOp_uint_mulUnchecked
    (hNoOv : a * b < modPow2 (uintWidth u)) :
    evalScalarBinOp .mulUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem
        false =
      .ok (.scalar ⟨wrapVal (uintWidth u) (a * b), uintBytes u⟩)
        locals mem := by
  have hB : Nat.ble (scalarModulus (uintBytes u)) (Nat.mul a b) = false := by
    rw [scalarModulus_uintBytes]
    cases h : Nat.ble (modPow2 (uintWidth u)) (Nat.mul a b) with
    | false => rfl
    | true => exact False.elim (Nat.not_le_of_gt hNoOv (Nat.le_of_ble_eq_true h))
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hB]
  rw [wrapVal_of_lt hNoOv]
  rfl

/-- Unsigned `.div` by a nonzero divisor. -/
theorem evalScalarBinOp_uint_div (hb : 0 < b) :
    evalScalarBinOp .div ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem false =
      .ok (.scalar ⟨wrapVal (uintWidth u) (a / b), uintBytes u⟩)
        locals mem := by
  have hB : Nat.beq b 0 = false := by
    cases h : Nat.beq b 0 with
    | false => rfl
    | true => rw [Nat.eq_of_beq_eq_true h] at hb; nomatch hb
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hB]
  rw [← wrapScalarBits_eq_wrapVal]
  rfl

/-- Unsigned `.rem` by a nonzero divisor. -/
theorem evalScalarBinOp_uint_rem (hb : 0 < b) :
    evalScalarBinOp .rem ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem false =
      .ok (.scalar ⟨wrapVal (uintWidth u) (a % b), uintBytes u⟩)
        locals mem := by
  have hB : Nat.beq b 0 = false := by
    cases h : Nat.beq b 0 with
    | false => rfl
    | true => rw [Nat.eq_of_beq_eq_true h] at hb; nomatch hb
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hB]
  rw [← wrapScalarBits_eq_wrapVal]
  rfl

/-- Unsigned `.bitAnd` for an in-range left operand. -/
theorem evalScalarBinOp_uint_bitAnd (ha : a < modPow2 (uintWidth u)) :
    evalScalarBinOp .bitAnd ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem
        false =
      .ok (.scalar ⟨Nat.land a b, uintBytes u⟩) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl,
    uintBytes_mul_eight]
  rw [Anneal.Scalars.bitwiseAndBits_eq_land_of_lt_left
    (by rw [← modPow2_eq_two_pow]; exact ha)]
  rfl

/-- Unsigned `.bitOr` for in-range operands. -/
theorem evalScalarBinOp_uint_bitOr
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u)) :
    evalScalarBinOp .bitOr ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem
        false =
      .ok (.scalar ⟨Nat.lor a b, uintBytes u⟩) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl,
    uintBytes_mul_eight]
  rw [modPow2_eq_two_pow] at ha hb
  rw [Anneal.Scalars.bitwiseOrBits_eq_lor_of_lt ha hb]
  rfl

/-- Unsigned `.bitXor` for in-range operands. -/
theorem evalScalarBinOp_uint_bitXor
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u)) :
    evalScalarBinOp .bitXor ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem
        false =
      .ok (.scalar ⟨Nat.xor a b, uintBytes u⟩) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl,
    uintBytes_mul_eight]
  rw [modPow2_eq_two_pow] at ha hb
  rw [Anneal.Scalars.bitwiseXorBits_eq_xor_of_lt ha hb]
  rfl

/-- Unsigned `.shl` (shift amount reduced modulo the bit width). -/
theorem evalScalarBinOp_uint_shl {u2 : UintTy} :
    evalScalarBinOp .shl ⟨a, uintBytes u⟩ ⟨b, uintBytes u2⟩ locals mem false =
      .ok (.scalar ⟨wrapVal (uintWidth u)
        (Nat.shiftLeft a (Nat.mod b (uintWidth u))), uintBytes u⟩)
        locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, uintBytes_mul_eight]
  rw [Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod_general,
    scalarModulus_uintBytes]
  rfl

/-- Unsigned `.shlUnchecked` with an in-range shift amount. -/
theorem evalScalarBinOp_uint_shlUnchecked {u2 : UintTy}
    (hb : b < uintWidth u) :
    evalScalarBinOp .shlUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u2⟩ locals mem
        false =
      .ok (.scalar ⟨wrapVal (uintWidth u) (Nat.shiftLeft a b), uintBytes u⟩)
        locals mem := by
  have hB : Nat.ble (uintWidth u) b = false := by
    cases h : Nat.ble (uintWidth u) b with
    | false => rfl
    | true => exact False.elim (Nat.not_le_of_gt hb (Nat.le_of_ble_eq_true h))
  simp only [evalScalarBinOp, uintBytes_beq_zero, uintBytes_mul_eight, hB]
  rw [Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod_general,
    scalarModulus_uintBytes]
  rfl

theorem shiftRight_lt_of_lt {a s M : Nat} (ha : a < M) :
    a >>> s < M :=
  Nat.lt_of_le_of_lt (Nat.shiftRight_le a s) ha

/-- Unsigned logical `.shr` (shift amount reduced modulo the bit width). -/
theorem evalScalarBinOp_uint_shr {u2 : UintTy}
    (ha : a < modPow2 (uintWidth u)) :
    evalScalarBinOp .shr ⟨a, uintBytes u⟩ ⟨b, uintBytes u2⟩ locals mem false =
      .ok (.scalar ⟨Nat.shiftRight a (Nat.mod b (uintWidth u)), uintBytes u⟩)
        locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, uintBytes_mul_eight]
  rw [Anneal.Scalars.shiftRightUnsignedBits_eq_shiftRight,
    wrapScalarBits_of_lt_uint (shiftRight_lt_of_lt ha)]
  rfl

/-- Unsigned logical `.shrUnchecked` with an in-range shift amount. -/
theorem evalScalarBinOp_uint_shrUnchecked {u2 : UintTy}
    (ha : a < modPow2 (uintWidth u)) (hb : b < uintWidth u) :
    evalScalarBinOp .shrUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u2⟩ locals mem
        false =
      .ok (.scalar ⟨Nat.shiftRight a b, uintBytes u⟩) locals mem := by
  have hB : Nat.ble (uintWidth u) b = false := by
    cases h : Nat.ble (uintWidth u) b with
    | false => rfl
    | true => exact False.elim (Nat.not_le_of_gt hb (Nat.le_of_ble_eq_true h))
  simp only [evalScalarBinOp, uintBytes_beq_zero, uintBytes_mul_eight, hB]
  rw [Anneal.Scalars.shiftRightUnsignedBits_eq_shiftRight,
    wrapScalarBits_of_lt_uint (shiftRight_lt_of_lt ha)]
  rfl

/-- Unsigned `.eq`. -/
theorem evalScalarBinOp_uint_eq :
    evalScalarBinOp .eq ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem false =
      .ok (.scalar (boolToScalar (Nat.beq a b))) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]

/-- Unsigned `.ne`. -/
theorem evalScalarBinOp_uint_ne :
    evalScalarBinOp .ne ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem false =
      .ok (.scalar (boolToScalar (!(Nat.beq a b)))) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]

/-- Unsigned `.lt`. -/
theorem evalScalarBinOp_uint_lt :
    evalScalarBinOp .lt ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem false =
      .ok (.scalar (boolToScalar (Nat.blt a b))) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  rw [nat_blt_eq_not_ble]

/-- Unsigned `.le`. -/
theorem evalScalarBinOp_uint_le :
    evalScalarBinOp .le ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem false =
      .ok (.scalar (boolToScalar (Nat.ble a b))) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]

/-- Unsigned `.gt`. -/
theorem evalScalarBinOp_uint_gt :
    evalScalarBinOp .gt ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem false =
      .ok (.scalar (boolToScalar (Nat.blt b a))) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  rw [nat_blt_eq_not_ble]

/-- Unsigned `.ge`. -/
theorem evalScalarBinOp_uint_ge :
    evalScalarBinOp .ge ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem false =
      .ok (.scalar (boolToScalar (Nat.ble b a))) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]

/-- Unsigned bitwise `UnOp.not` (`evalUnaryNot` at a `.uint` operand type). -/
theorem evalUnaryNot_uint {ty : Ty} {u2 : UintTy} (hTy : ty.kind = .uint u2)
    (ha : a < modPow2 (uintWidth u)) :
    evalUnaryNot ⟨a, uintBytes u⟩ (some ty) locals mem =
      .ok (.scalar ⟨modPow2 (uintWidth u) - 1 - a, uintBytes u⟩)
        locals mem := by
  cases ty with
  | mk kind idx =>
    simp only at hTy
    subst hTy
    simp only [evalUnaryNot, uintBytes_beq_zero]
    rw [wrapScalarBits_of_lt_uint ha, scalarModulus_uintBytes]
    rfl

/-- Boolean `UnOp.not` (`evalUnaryNot` at a `.bool` operand type). -/
theorem evalUnaryNot_bool {ty : Ty} (hTy : ty.kind = .bool) (c : Bool) :
    evalUnaryNot (boolToScalar c) (some ty) locals mem =
      .ok (.scalar (boolToScalar (!c))) locals mem := by
  cases ty with
  | mk kind idx =>
    simp only at hTy
    subst hTy
    cases c <;> rfl

/-- Unsigned checked `.addWithOverflow` returning `(u, bool)`. -/
theorem evalScalarBinOp_uint_addWithOverflow :
    evalScalarBinOp .addWithOverflow ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals
        mem false =
      .ok (.aggregate 0
        [.scalar ⟨wrapVal (uintWidth u) (a + b), uintBytes u⟩,
         .scalar (boolToScalar (Nat.ble (modPow2 (uintWidth u)) (a + b)))])
        locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  rw [← wrapScalarBits_eq_wrapVal, scalarModulus_uintBytes]
  cases Nat.ble (modPow2 (uintWidth u)) (Nat.add a b) <;> rfl

/-- Unsigned checked `.subWithOverflow` for in-range operands. -/
theorem evalScalarBinOp_uint_subWithOverflow
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u)) :
    evalScalarBinOp .subWithOverflow ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals
        mem false =
      .ok (.aggregate 0
        [.scalar ⟨wrapVal (uintWidth u) (modPow2 (uintWidth u) + a - b),
          uintBytes u⟩,
         .scalar (boolToScalar (!(Nat.ble b a)))])
        locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  cases h : Nat.ble b a with
  | true =>
    simp only
    rw [wrapScalarBits_eq_wrapVal, show Nat.sub a b = a - b from rfl,
      wrapVal_sub_of_le (Nat.le_of_ble_eq_true h) ha]
    rfl
  | false =>
    simp only
    rw [wrapScalarBits_of_lt_uint ha, wrapScalarBits_of_lt_uint hb,
      wrapScalarBits_eq_wrapVal, scalarModulus_uintBytes]
    rfl

/-- Unsigned checked `.mulWithOverflow` returning `(u, bool)`. -/
theorem evalScalarBinOp_uint_mulWithOverflow :
    evalScalarBinOp .mulWithOverflow ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals
        mem false =
      .ok (.aggregate 0
        [.scalar ⟨wrapVal (uintWidth u) (a * b), uintBytes u⟩,
         .scalar (boolToScalar (Nat.ble (modPow2 (uintWidth u)) (a * b)))])
        locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  rw [← wrapScalarBits_eq_wrapVal, scalarModulus_uintBytes]
  cases Nat.ble (modPow2 (uintWidth u)) (Nat.mul a b) <;> rfl

/-- Boolean `.bitAnd`. -/
theorem evalScalarBinOp_bool_bitAnd (c1 c2 : Bool) :
    evalScalarBinOp .bitAnd (boolToScalar c1) (boolToScalar c2) locals mem
        false =
      .ok (.scalar (boolToScalar (c1 && c2))) locals mem := by
  cases c1 <;> cases c2 <;> rfl

/-- Boolean `.bitOr`. -/
theorem evalScalarBinOp_bool_bitOr (c1 c2 : Bool) :
    evalScalarBinOp .bitOr (boolToScalar c1) (boolToScalar c2) locals mem
        false =
      .ok (.scalar (boolToScalar (c1 || c2))) locals mem := by
  cases c1 <;> cases c2 <;> rfl

/-- Boolean `.bitXor`. -/
theorem evalScalarBinOp_bool_bitXor (c1 c2 : Bool) :
    evalScalarBinOp .bitXor (boolToScalar c1) (boolToScalar c2) locals mem
        false =
      .ok (.scalar (boolToScalar (xor c1 c2))) locals mem := by
  cases c1 <;> cases c2 <;> rfl

/-- Boolean `.eq`. -/
theorem evalScalarBinOp_bool_eq (c1 c2 : Bool) :
    evalScalarBinOp .eq (boolToScalar c1) (boolToScalar c2) locals mem false =
      .ok (.scalar (boolToScalar (c1 == c2))) locals mem := by
  cases c1 <;> cases c2 <;> rfl

/-- Boolean `.ne`. -/
theorem evalScalarBinOp_bool_ne (c1 c2 : Bool) :
    evalScalarBinOp .ne (boolToScalar c1) (boolToScalar c2) locals mem false =
      .ok (.scalar (boolToScalar (c1 != c2))) locals mem := by
  cases c1 <;> cases c2 <;> rfl

/-- Boolean `.lt`. -/
theorem evalScalarBinOp_bool_lt (c1 c2 : Bool) :
    evalScalarBinOp .lt (boolToScalar c1) (boolToScalar c2) locals mem false =
      .ok (.scalar (boolToScalar (!c1 && c2))) locals mem := by
  cases c1 <;> cases c2 <;> rfl

/-- Boolean `.le`. -/
theorem evalScalarBinOp_bool_le (c1 c2 : Bool) :
    evalScalarBinOp .le (boolToScalar c1) (boolToScalar c2) locals mem false =
      .ok (.scalar (boolToScalar (!c1 || c2))) locals mem := by
  cases c1 <;> cases c2 <;> rfl

/-- Boolean `.gt`. -/
theorem evalScalarBinOp_bool_gt (c1 c2 : Bool) :
    evalScalarBinOp .gt (boolToScalar c1) (boolToScalar c2) locals mem false =
      .ok (.scalar (boolToScalar (c1 && !c2))) locals mem := by
  cases c1 <;> cases c2 <;> rfl

/-- Boolean `.ge`. -/
theorem evalScalarBinOp_bool_ge (c1 c2 : Bool) :
    evalScalarBinOp .ge (boolToScalar c1) (boolToScalar c2) locals mem false =
      .ok (.scalar (boolToScalar (c1 || !c2))) locals mem := by
  cases c1 <;> cases c2 <;> rfl

end ScalarOps

/-- Bitwise complement of an in-range unsigned integer equals XOR with
`2^w - 1`. -/
theorem nat_xor_mask_eq_sub {w x : Nat} (hx : x < modPow2 w) :
    Nat.xor x (modPow2 w - 1) = modPow2 w - 1 - x := by
  let c := Nat.xor x (modPow2 w - 1)
  have hDisj : Nat.land x c = 0 := by
    apply nat_eq_of_bitAt
    intro k
    rw [bitAt_land, bitAt_xor, bitAt_modPow2_sub_one, bitAt_zero_nat]
    cases hk : Nat.blt k w with
    | true => cases bitAt x k <;> rfl
    | false =>
      have hGe : w ≤ k := Nat.le_of_not_lt (fun hLt => by
        rw [blt_true_of_lt hLt] at hk; nomatch hk)
      rw [bitAt_zero_ge_of_lt_modPow2 hx k hGe]
      rfl
  have hUnion : Nat.lor x c = modPow2 w - 1 := by
    apply nat_eq_of_bitAt
    intro k
    rw [bitAt_lor, bitAt_xor, bitAt_modPow2_sub_one]
    cases hk : Nat.blt k w with
    | true => cases bitAt x k <;> rfl
    | false =>
      have hGe : w ≤ k := Nat.le_of_not_lt (fun hLt => by
        rw [blt_true_of_lt hLt] at hk; nomatch hk)
      rw [bitAt_zero_ge_of_lt_modPow2 hx k hGe]
      rfl
  have hSum : x + c = modPow2 w - 1 :=
    Eq.trans (nat_add_eq_lor_of_disjoint x c hDisj) hUnion
  have hSub := congrArg (fun z => z - x) hSum
  rw [Nat.add_comm x c, Nat.add_sub_cancel] at hSub
  exact hSub

/-- `Tnum.capPow2 k a` soundly abstracts `wrapVal k x` for any `x` denoted by
`a` (preserves low `k` known bits across narrowing integer casts). -/
theorem tnum_capPow2_wrap_sound {k x : Nat} {a : Tnum} (ha : a.denote x) :
    (Tnum.capPow2 k a).denote (wrapVal k x) := by
  rw [tnum_denote_iff_bitAt] at ha
  rw [tnum_denote_iff_bitAt]
  dsimp only [Tnum.capPow2, Tnum.wf, wrapVal]
  refine ⟨?_, ?_⟩
  · apply nat_beq_of_eq
    apply nat_eq_of_bitAt
    intro j
    rw [bitAt_land, bitAt_land, bitAt_land, bitAt_zero_nat]
    have hWfA : bitAt (Nat.land a.val a.mask) j = bitAt 0 j := by
      rw [Nat.eq_of_beq_eq_true ha.1]
    rw [bitAt_land, bitAt_zero_nat] at hWfA
    cases hav : bitAt a.val j with
    | false => cases bitAt (modPow2 k - 1) j <;> rfl
    | true =>
      cases ham : bitAt a.mask j with
      | false => cases bitAt (modPow2 k - 1) j <;> rfl
      | true => rw [hav, ham] at hWfA; nomatch hWfA
  · intro j hm0
    rw [bitAt_land, bitAt_modPow2_sub_one] at hm0
    rw [bitAt_land, bitAt_modPow2_sub_one, bitAt_mod_modPow2]
    cases hjk : Nat.blt j k with
    | true =>
      rw [hjk, Bool.and_true] at hm0
      rw [Bool.and_true]
      exact ha.2 j hm0
    | false =>
      rw [Bool.and_false]

/-! ## 2. `Trusted.Sequence` and Projection Helpers -/

section ListHelpers

variable {α β : Type}

theorem get?_set?_same {xs xs' : List α} {i : Nat} {v : α}
    (h : set? xs i v = some xs') : get? xs' i = some v := by
  unfold set? at h
  split at h
  · injection h with h
    subst h
    exact List.getElem?_set_self ‹_›
  · nomatch h

theorem get?_set?_ne {xs xs' : List α} {i j : Nat} {v : α}
    (h : set? xs i v = some xs') (hNe : i ≠ j) : get? xs' j = get? xs j := by
  unfold set? at h
  split at h
  · injection h with h
    subst h
    exact List.getElem?_set_ne hNe
  · nomatch h

theorem length_set? {xs xs' : List α} {i : Nat} {v : α}
    (h : set? xs i v = some xs') : length xs' = length xs := by
  unfold set? at h
  split at h
  · injection h with h
    subst h
    exact List.length_set
  · nomatch h

theorem set?_some_of_get? {xs : List α} {i : Nat} {x : α} (v : α)
    (h : get? xs i = some x) : ∃ xs', set? xs i v = some xs' := by
  have hLt : i < xs.length := (List.getElem?_eq_some_iff.mp h).1
  refine ⟨xs.set i v, ?_⟩
  simp only [set?, hLt, ite_true]

theorem get?_exists_of_length {xs : List α} {ys : List β} {i : Nat} {y : β}
    (hLen : length xs = length ys) (h : get? ys i = some y) :
    ∃ x, get? xs i = some x := by
  have hLt : i < ys.length := (List.getElem?_eq_some_iff.mp h).1
  have hLt' : i < xs.length := by
    have hL : xs.length = ys.length := hLen
    rw [hL]
    exact hLt
  exact ⟨xs[i], List.getElem?_eq_getElem hLt'⟩

theorem get?_some_of_lt {xs : List α} {i : Nat} (h : i < length xs) :
    ∃ x, get? xs i = some x :=
  ⟨xs[i], List.getElem?_eq_getElem h⟩

theorem get?_none_of_len (xs : List α) : get? xs (length xs) = none :=
  List.getElem?_eq_none (Nat.le_refl xs.length)

theorem get?_map (f : α → β) (xs : List α) (i : Nat) :
    get? (xs.map f) i = (get? xs i).map f :=
  List.getElem?_map

theorem length_map (f : α → β) (xs : List α) :
    length (xs.map f) = length xs :=
  List.length_map f

theorem nat_ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b :=
  fun hEq => by rw [hEq, Nat.beq_refl] at h; nomatch h

/-- `resolveTyWithLocalDecls` preserves `ty.kind`. -/
theorem resolveTyWithLocalDecls_kind (decls : List LocalDecl)
    (layouts : LayoutTable) (ty : Ty) :
    (resolveTyWithLocalDecls decls layouts ty).kind = ty.kind := by
  unfold resolveTyWithLocalDecls
  cases isUnresolvedLayoutIdx layouts ty.layoutIdx with
  | false => rfl
  | true =>
    simp only
    cases findDeclOrContainerElemTyWithKind? decls layouts ty.kind with
    | some _ => rfl
    | none =>
      simp only
      cases Nat.beq ty.layoutIdx 0 with
      | false => rfl
      | true =>
        cases decls with
        | nil => rfl
        | cons _ _ =>
          simp only
          cases isPrimitiveScalarKind ty.kind <;> rfl

/-- A single `.field` projection on a tuple local never touches a union. -/
theorem placeTouchesUnion_tuple_field_false (decls : List LocalDecl)
    (layouts : LayoutTable) {l idx : Nat} {fty : Ty} {d : LocalDecl}
    {ts : List RigidTy} (hD : get? decls l = some d)
    (hTuple : d.ty.kind = .tuple ts) :
    placeTouchesUnion decls layouts ⟨l, [.field idx fty]⟩ = false := by
  unfold placeTouchesUnion
  cases decls with
  | nil => rfl
  | cons hd tl =>
    cases layouts with
    | mk pb le entries =>
      cases entries with
      | nil => rfl
      | cons e es =>
        simp only [hD, tyProjTouchesUnion]
        have hK : (resolveTyWithLocalDecls (hd :: tl) ⟨pb, le, e :: es⟩
            d.ty).kind = .tuple ts :=
          Eq.trans (resolveTyWithLocalDecls_kind _ _ d.ty) hTuple
        have hNotU : isUnionLayout ⟨pb, le, e :: es⟩
            (resolveTyWithLocalDecls (hd :: tl) ⟨pb, le, e :: es⟩ d.ty) =
            false := by
          unfold isUnionLayout
          rw [hK]
        rw [hNotU]

end ListHelpers

/-! ## 3. Relational Comparison Guards -/

/-- Relational predicate attached to a `bool` local recording the unsigned
comparison that produced it, enabling path-sensitive refinement at
`switchInt` and `assert` without fused compare-and-branch instructions. -/
inductive RelGuard where
  | none
  | uleConst (reg : Nat) (u : UintTy) (bound : Nat)
  | ugtConst (reg : Nat) (u : UintTy) (bound : Nat)
  | ultReg (lhs rhs : Nat) (u : UintTy)
  | ugeReg (lhs rhs : Nat) (u : UintTy)
  | ueqConst (reg : Nat) (u : UintTy) (val : Nat)
  | uneConst (reg : Nat) (u : UintTy) (val : Nat)

/-- Structural equality on `RelGuard`. -/
def RelGuard.beq : RelGuard → RelGuard → Bool
  | .none, .none => true
  | .uleConst r1 u1 b1, .uleConst r2 u2 b2 =>
    Nat.beq r1 r2 && uintTyBeq u1 u2 && Nat.beq b1 b2
  | .ugtConst r1 u1 b1, .ugtConst r2 u2 b2 =>
    Nat.beq r1 r2 && uintTyBeq u1 u2 && Nat.beq b1 b2
  | .ultReg l1 r1 u1, .ultReg l2 r2 u2 =>
    Nat.beq l1 l2 && Nat.beq r1 r2 && uintTyBeq u1 u2
  | .ugeReg l1 r1 u1, .ugeReg l2 r2 u2 =>
    Nat.beq l1 l2 && Nat.beq r1 r2 && uintTyBeq u1 u2
  | .ueqConst r1 u1 v1, .ueqConst r2 u2 v2 =>
    Nat.beq r1 r2 && uintTyBeq u1 u2 && Nat.beq v1 v2
  | .uneConst r1 u1 v1, .uneConst r2 u2 v2 =>
    Nat.beq r1 r2 && uintTyBeq u1 u2 && Nat.beq v1 v2
  | _, _ => false

/-- Soundness of `RelGuard.beq`. -/
theorem relGuard_eq_of_beq {g1 g2 : RelGuard} (h : RelGuard.beq g1 g2 = true) :
    g1 = g2 := by
  cases g1 <;> cases g2 <;> simp only [RelGuard.beq] at h <;>
    first
    | rfl
    | (have h12 := bool_and_true_left h
       have h1 := bool_and_true_left h12
       have h2 := bool_and_true_right h12
       have h3 := bool_and_true_right h
       first
       | rw [Nat.eq_of_beq_eq_true h1, uintTy_eq_of_beq h2,
           Nat.eq_of_beq_eq_true h3]
       | rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2,
           uintTy_eq_of_beq h3])
    | nomatch h

/-- Logical negation of a `RelGuard`. -/
def RelGuard.negate : RelGuard → RelGuard
  | .none => .none
  | .uleConst r u b => .ugtConst r u b
  | .ugtConst r u b => .uleConst r u b
  | .ultReg l r u => .ugeReg l r u
  | .ugeReg l r u => .ultReg l r u
  | .ueqConst r u v => .uneConst r u v
  | .uneConst r u v => .ueqConst r u v

/-- True iff `g` references local `id`. -/
def RelGuard.mentions (id : Nat) : RelGuard → Bool
  | .none => false
  | .uleConst r _ _ => Nat.beq r id
  | .ugtConst r _ _ => Nat.beq r id
  | .ultReg l r _ => Nat.beq l id || Nat.beq r id
  | .ugeReg l r _ => Nat.beq l id || Nat.beq r id
  | .ueqConst r _ _ => Nat.beq r id
  | .uneConst r _ _ => Nat.beq r id

/-- Unsigned bit pattern of a scalar `Value` at byte width `uintBytes u`. -/
def uintValNat? (u : UintTy) : Value → Option Nat
  | .scalar sc =>
    match Nat.beq sc.sizeBytes (uintBytes u) with
    | true => some sc.bits
    | false => none
  | _ => none

/-- Unsigned bit pattern held by local `r` (initialized scalars only). -/
def localUintNat? (locals : List LocalSlot) (r : Nat) (u : UintTy) :
    Option Nat :=
  match get? locals r with
  | some (.init v) => uintValNat? u v
  | _ => none

theorem localUintNat?_of_get? {locals : List LocalSlot} {r : Nat}
    {u : UintTy} {sc : ScalarInt}
    (hGet : get? locals r = some (.init (.scalar sc)))
    (hSz : sc.sizeBytes = uintBytes u) :
    localUintNat? locals r u = some sc.bits := by
  unfold localUintNat?
  rw [hGet]
  simp only [uintValNat?, hSz, Nat.beq_refl]

/-- Concrete meaning of `RelGuard` on boolean outcome `b` in `locals`. -/
def RelGuard.denote (locals : List LocalSlot) (g : RelGuard) (b : Bool) :
    Prop :=
  match g with
  | .none => True
  | .uleConst r u bound =>
    ∀ x, localUintNat? locals r u = some x → (b = true ↔ x ≤ bound)
  | .ugtConst r u bound =>
    ∀ x, localUintNat? locals r u = some x → (b = true ↔ bound < x)
  | .ultReg l r u =>
    ∀ x y, localUintNat? locals l u = some x →
      localUintNat? locals r u = some y → (b = true ↔ x < y)
  | .ugeReg l r u =>
    ∀ x y, localUintNat? locals l u = some x →
      localUintNat? locals r u = some y → (b = true ↔ y ≤ x)
  | .ueqConst r u val =>
    ∀ x, localUintNat? locals r u = some x → (b = true ↔ x = val)
  | .uneConst r u val =>
    ∀ x, localUintNat? locals r u = some x → (b = true ↔ x ≠ val)

/-- Soundness of `RelGuard.negate`. -/
theorem relGuard_negate_sound {locals : List LocalSlot} {g : RelGuard}
    {b : Bool} (h : g.denote locals b) : g.negate.denote locals (!b) := by
  cases g with
  | none => exact True.intro
  | uleConst r u bound =>
    intro x hx
    have hIff := h x hx
    cases b with
    | true =>
      have hLe := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF),
        (fun hGt => False.elim (Nat.not_le_of_gt hGt hLe))⟩
    | false =>
      have hNotLe : ¬ (x ≤ bound) := fun hLe => nomatch (hIff.mpr hLe)
      exact ⟨(fun _ => Nat.lt_of_not_le hNotLe), (fun _ => rfl)⟩
  | ugtConst r u bound =>
    intro x hx
    have hIff := h x hx
    cases b with
    | true =>
      have hGt := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF),
        (fun hLe => False.elim (Nat.not_le_of_gt hGt hLe))⟩
    | false =>
      have hNotGt : ¬ (bound < x) := fun hGt => nomatch (hIff.mpr hGt)
      exact ⟨(fun _ => Nat.le_of_not_lt hNotGt), (fun _ => rfl)⟩
  | ultReg l r u =>
    intro x y hx hy
    have hIff := h x y hx hy
    cases b with
    | true =>
      have hLt := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF),
        (fun hGe => False.elim (Nat.not_le_of_gt hLt hGe))⟩
    | false =>
      have hNotLt : ¬ (x < y) := fun hLt => nomatch (hIff.mpr hLt)
      exact ⟨(fun _ => Nat.le_of_not_lt hNotLt), (fun _ => rfl)⟩
  | ugeReg l r u =>
    intro x y hx hy
    have hIff := h x y hx hy
    cases b with
    | true =>
      have hGe := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF),
        (fun hLt => False.elim (Nat.not_le_of_gt hLt hGe))⟩
    | false =>
      have hNotGe : ¬ (y ≤ x) := fun hGe => nomatch (hIff.mpr hGe)
      exact ⟨(fun _ => Nat.lt_of_not_le hNotGe), (fun _ => rfl)⟩
  | ueqConst r u val =>
    intro x hx
    have hIff := h x hx
    cases b with
    | true =>
      have hEq := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF), (fun hNe => False.elim (hNe hEq))⟩
    | false =>
      have hNe : x ≠ val := fun hEq => nomatch (hIff.mpr hEq)
      exact ⟨(fun _ => hNe), (fun _ => rfl)⟩
  | uneConst r u val =>
    intro x hx
    have hIff := h x hx
    cases b with
    | true =>
      have hNe := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF), (fun hEq => False.elim (hNe hEq))⟩
    | false =>
      have hEq : x = val := by
        cases hB : Nat.beq x val with
        | true => exact Nat.eq_of_beq_eq_true hB
        | false => exact False.elim (nomatch (hIff.mpr (nat_ne_of_beq_false hB)))
      exact ⟨(fun _ => hEq), (fun _ => rfl)⟩

/-- Writing local `id` leaves `localUintNat?` of every other local intact. -/
theorem localUintNat?_set?_ne {locals locals' : List LocalSlot} {id r : Nat}
    {newCs : LocalSlot} (u : UintTy) (hSet : set? locals id newCs = some locals')
    (hNe : id ≠ r) : localUintNat? locals' r u = localUintNat? locals r u := by
  unfold localUintNat?
  rw [get?_set?_ne hSet hNe]

/-- A guard not mentioning `id` is preserved by any write to local `id`. -/
theorem relGuard_preserved_on_update {locals locals' : List LocalSlot}
    {id : Nat} {newCs : LocalSlot} {g : RelGuard} {b : Bool}
    (hSet : set? locals id newCs = some locals')
    (hNoMent : g.mentions id = false)
    (hDen : g.denote locals b) :
    g.denote locals' b := by
  have hLocEq : ∀ r u, Nat.beq r id = false →
      localUintNat? locals' r u = localUintNat? locals r u := by
    intro r u hNeB
    have hNe : id ≠ r := fun hE => nat_ne_of_beq_false hNeB hE.symm
    unfold localUintNat?
    rw [get?_set?_ne hSet hNe]
  cases g with
  | none => exact True.intro
  | uleConst r u bound =>
    intro x hx
    rw [hLocEq r u hNoMent] at hx
    exact hDen x hx
  | ugtConst r u bound =>
    intro x hx
    rw [hLocEq r u hNoMent] at hx
    exact hDen x hx
  | ultReg l r u =>
    intro x y hx hy
    simp only [RelGuard.mentions] at hNoMent
    rw [hLocEq l u (bool_or_false_left hNoMent)] at hx
    rw [hLocEq r u (bool_or_false_right hNoMent)] at hy
    exact hDen x y hx hy
  | ugeReg l r u =>
    intro x y hx hy
    simp only [RelGuard.mentions] at hNoMent
    rw [hLocEq l u (bool_or_false_left hNoMent)] at hx
    rw [hLocEq r u (bool_or_false_right hNoMent)] at hy
    exact hDen x y hx hy
  | ueqConst r u val =>
    intro x hx
    rw [hLocEq r u hNoMent] at hx
    exact hDen x hx
  | uneConst r u val =>
    intro x hx
    rw [hLocEq r u hNoMent] at hx
    exact hDen x hx

/-! ## 4. Abstract Booleans (`BoolAbs`) -/

/-- Decode a `Value` as a Rust `bool` (`0x00` / `0x01` at byte width `1`). -/
def boolOfValue? : Value → Option Bool
  | .scalar sc =>
    match Nat.beq sc.sizeBytes 1, Nat.beq sc.bits 0, Nat.beq sc.bits 1 with
    | true, true, _ => some false
    | true, false, true => some true
    | _, _, _ => none
  | _ => none

theorem boolOfValue?_boolToScalar (b : Bool) :
    boolOfValue? (.scalar (boolToScalar b)) = some b := by
  cases b <;> rfl

theorem eq_of_boolOfValue? {v : Value} {b : Bool}
    (h : boolOfValue? v = some b) : v = .scalar (boolToScalar b) := by
  cases v with
  | scalar sc =>
    cases sc with
    | mk bits sz =>
      simp only [boolOfValue?] at h
      cases h1 : Nat.beq sz 1 with
      | false => rw [h1] at h; nomatch h
      | true =>
        have hSz := Nat.eq_of_beq_eq_true h1
        subst hSz
        cases h2 : Nat.beq bits 0 with
        | true =>
          rw [h1, h2] at h
          injection h with hb
          subst hb
          rw [Nat.eq_of_beq_eq_true h2]
          rfl
        | false =>
          cases h3 : Nat.beq bits 1 with
          | false => rw [h1, h2, h3] at h; nomatch h
          | true =>
            rw [h1, h2, h3] at h
            injection h with hb
            subst hb
            rw [Nat.eq_of_beq_eq_true h3]
            rfl
  | unit | ptr _ _ | aggregate _ _ | uninit => nomatch h

/-- Abstract boolean local with an optional attached `RelGuard`. -/
inductive BoolAbs where
  | bot
  | uninit
  | top (guard : RelGuard)
  | exact (val : Bool) (guard : RelGuard)

/-- Concrete meaning of `BoolAbs` on a decoded boolean `b`. -/
def BoolAbs.denoteBool (locals : List LocalSlot) (ba : BoolAbs) (b : Bool) :
    Prop :=
  match ba with
  | .bot => False
  | .uninit => True
  | .top g => g.denote locals b
  | .exact c g => b = c ∧ g.denote locals b

/-- Concrete denotation of `BoolAbs` on `Option Value` (`none` is an
uninitialized slot). -/
def BoolAbs.denote (locals : List LocalSlot) (ba : BoolAbs) :
    Option Value → Prop
  | none =>
    match ba with
    | .uninit => True
    | _ => False
  | some v =>
    match boolOfValue? v with
    | none => False
    | some b => ba.denoteBool locals b

/-- `ba` guarantees an initialized `bool`. -/
def BoolAbs.isInit : BoolAbs → Bool
  | .top _ => true
  | .exact _ _ => true
  | .bot | .uninit => false

theorem boolAbs_denote_some {locals : List LocalSlot} {ba : BoolAbs}
    {v : Value} (h : ba.denote locals (some v)) :
    ∃ b, v = .scalar (boolToScalar b) ∧ ba.denoteBool locals b := by
  simp only [BoolAbs.denote] at h
  cases hB : boolOfValue? v with
  | none => rw [hB] at h; exact False.elim h
  | some b =>
    rw [hB] at h
    exact ⟨b, eq_of_boolOfValue? hB, h⟩

theorem boolAbs_denote_of_bool {locals : List LocalSlot} {ba : BoolAbs}
    {b : Bool} (h : ba.denoteBool locals b) :
    ba.denote locals (some (.scalar (boolToScalar b))) := by
  simp only [BoolAbs.denote]
  rw [boolOfValue?_boolToScalar]
  exact h

/-- Structural equality on `Bool`. -/
def boolBeq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

theorem bool_eq_of_boolBeq {a b : Bool} (h : boolBeq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | nomatch h

/-- Lattice inclusion on `BoolAbs`. -/
def BoolAbs.le (a b : BoolAbs) : Bool :=
  match a, b with
  | .bot, _ => true
  | _, .uninit => true
  | .top g1, .top g2 =>
    match g2 with
    | .none => true
    | _ => RelGuard.beq g1 g2
  | .exact _ g1, .top g2 =>
    match g2 with
    | .none => true
    | _ => RelGuard.beq g1 g2
  | .exact v1 g1, .exact v2 g2 =>
    boolBeq v1 v2 &&
    match g2 with
    | .none => true
    | _ => RelGuard.beq g1 g2
  | _, _ => false

theorem relGuard_le_sound {locals : List LocalSlot} {g1 g2 : RelGuard}
    {b : Bool}
    (hLe : (match g2 with
            | .none => true
            | _ => RelGuard.beq g1 g2) = true)
    (h : g1.denote locals b) : g2.denote locals b := by
  cases g2 with
  | none => exact True.intro
  | _ => rw [← relGuard_eq_of_beq hLe]; exact h

theorem boolAbs_le_denoteBool {locals : List LocalSlot} {a b : BoolAbs}
    {v : Bool} (hLe : BoolAbs.le a b = true) (ha : a.denoteBool locals v) :
    b.denoteBool locals v := by
  cases a with
  | bot => exact False.elim ha
  | uninit =>
    cases b with
    | uninit => exact True.intro
    | _ => nomatch hLe
  | top g1 =>
    cases b with
    | bot => nomatch hLe
    | uninit => exact True.intro
    | exact _ _ => nomatch hLe
    | top g2 => exact relGuard_le_sound hLe ha
  | exact v1 g1 =>
    cases b with
    | bot => nomatch hLe
    | uninit => exact True.intro
    | top g2 => exact relGuard_le_sound hLe ha.2
    | exact v2 g2 =>
      simp only [BoolAbs.le] at hLe
      have hv := bool_eq_of_boolBeq (bool_and_true_left hLe)
      exact ⟨Eq.trans ha.1 hv, relGuard_le_sound (bool_and_true_right hLe) ha.2⟩

/-- Soundness of `BoolAbs.le`. -/
theorem boolAbs_le_sound {locals : List LocalSlot} {a b : BoolAbs}
    {opt : Option Value} (hLe : BoolAbs.le a b = true)
    (ha : a.denote locals opt) : b.denote locals opt := by
  cases opt with
  | none =>
    cases a with
    | uninit =>
      cases b with
      | uninit => exact True.intro
      | _ => nomatch hLe
    | _ => exact False.elim ha
  | some v =>
    simp only [BoolAbs.denote] at ha ⊢
    cases hB : boolOfValue? v with
    | none => rw [hB] at ha; exact ha
    | some bv =>
      rw [hB] at ha
      exact boolAbs_le_denoteBool hLe ha

/-- Join of two guards: kept only if structurally equal. -/
def RelGuard.join (g1 g2 : RelGuard) : RelGuard :=
  match RelGuard.beq g1 g2 with
  | true => g1
  | false => .none

theorem relGuard_join_left {locals : List LocalSlot} {g1 g2 : RelGuard}
    {b : Bool} (h : g1.denote locals b) : (RelGuard.join g1 g2).denote locals b := by
  simp only [RelGuard.join]
  cases RelGuard.beq g1 g2 with
  | true => exact h
  | false => exact True.intro

theorem relGuard_join_right {locals : List LocalSlot} {g1 g2 : RelGuard}
    {b : Bool} (h : g2.denote locals b) : (RelGuard.join g1 g2).denote locals b := by
  simp only [RelGuard.join]
  cases hB : RelGuard.beq g1 g2 with
  | true => rw [relGuard_eq_of_beq hB]; exact h
  | false => exact True.intro

/-- Lattice join on `BoolAbs`. -/
def BoolAbs.join (a b : BoolAbs) : BoolAbs :=
  match a, b with
  | .bot, x => x
  | x, .bot => x
  | .uninit, _ => .uninit
  | _, .uninit => .uninit
  | .exact v1 g1, .exact v2 g2 =>
    match boolBeq v1 v2 with
    | true => .exact v1 (RelGuard.join g1 g2)
    | false => .top (RelGuard.join g1 g2)
  | .exact _ g1, .top g2 => .top (RelGuard.join g1 g2)
  | .top g1, .exact _ g2 => .top (RelGuard.join g1 g2)
  | .top g1, .top g2 => .top (RelGuard.join g1 g2)

theorem boolAbs_join_denoteBool_left {locals : List LocalSlot} {a b : BoolAbs}
    {v : Bool} (ha : a.denoteBool locals v) :
    (BoolAbs.join a b).denoteBool locals v := by
  cases a with
  | bot => exact False.elim ha
  | uninit => cases b <;> exact True.intro
  | top g1 =>
    cases b with
    | bot => exact ha
    | uninit => exact True.intro
    | top g2 => exact relGuard_join_left ha
    | exact _ g2 => exact relGuard_join_left ha
  | exact v1 g1 =>
    cases b with
    | bot => exact ha
    | uninit => exact True.intro
    | top g2 => exact relGuard_join_left ha.2
    | exact v2 g2 =>
      simp only [BoolAbs.join]
      cases boolBeq v1 v2 with
      | true => exact ⟨ha.1, relGuard_join_left ha.2⟩
      | false => exact relGuard_join_left ha.2

theorem boolAbs_join_denoteBool_right {locals : List LocalSlot} {a b : BoolAbs}
    {v : Bool} (hb : b.denoteBool locals v) :
    (BoolAbs.join a b).denoteBool locals v := by
  cases b with
  | bot => exact False.elim hb
  | uninit => cases a <;> exact True.intro
  | top g2 =>
    cases a with
    | bot => exact hb
    | uninit => exact True.intro
    | top g1 => exact relGuard_join_right hb
    | exact _ g1 => exact relGuard_join_right hb
  | exact v2 g2 =>
    cases a with
    | bot => exact hb
    | uninit => exact True.intro
    | top g1 => exact relGuard_join_right hb.2
    | exact v1 g1 =>
      simp only [BoolAbs.join]
      cases hV : boolBeq v1 v2 with
      | true =>
        exact ⟨Eq.trans hb.1 (bool_eq_of_boolBeq hV).symm,
          relGuard_join_right hb.2⟩
      | false => exact relGuard_join_right hb.2

theorem boolAbs_join_sound_left {locals : List LocalSlot} {a b : BoolAbs}
    {opt : Option Value} (ha : a.denote locals opt) :
    (BoolAbs.join a b).denote locals opt := by
  cases opt with
  | none =>
    cases a with
    | uninit => cases b <;> exact True.intro
    | _ => exact False.elim ha
  | some v =>
    simp only [BoolAbs.denote] at ha ⊢
    cases hB : boolOfValue? v with
    | none => rw [hB] at ha; exact ha
    | some bv => rw [hB] at ha; exact boolAbs_join_denoteBool_left ha

theorem boolAbs_join_sound_right {locals : List LocalSlot} {a b : BoolAbs}
    {opt : Option Value} (hb : b.denote locals opt) :
    (BoolAbs.join a b).denote locals opt := by
  cases opt with
  | none =>
    cases b with
    | uninit => cases a <;> exact True.intro
    | _ => exact False.elim hb
  | some v =>
    simp only [BoolAbs.denote] at hb ⊢
    cases hB : boolOfValue? v with
    | none => rw [hB] at hb; exact hb
    | some bv => rw [hB] at hb; exact boolAbs_join_denoteBool_right hb

/-- Drop the `RelGuard` of `ba` if it mentions local `id`. -/
def BoolAbs.clearGuardIf (id : Nat) : BoolAbs → BoolAbs
  | .bot => .bot
  | .uninit => .uninit
  | .top g =>
    match g.mentions id with
    | true => .top .none
    | false => .top g
  | .exact v g =>
    match g.mentions id with
    | true => .exact v .none
    | false => .exact v g

theorem boolAbs_clearGuardIf_update {locals locals' : List LocalSlot}
    {id : Nat} {newCs : LocalSlot} {ba : BoolAbs} {v : Bool}
    (hSet : set? locals id newCs = some locals')
    (h : ba.denoteBool locals v) :
    (ba.clearGuardIf id).denoteBool locals' v := by
  cases ba with
  | bot => exact h
  | uninit => exact h
  | top g =>
    simp only [BoolAbs.clearGuardIf]
    cases hM : g.mentions id with
    | true => exact True.intro
    | false => exact relGuard_preserved_on_update hSet hM h
  | exact c g =>
    simp only [BoolAbs.clearGuardIf]
    cases hM : g.mentions id with
    | true => exact ⟨h.1, True.intro⟩
    | false => exact ⟨h.1, relGuard_preserved_on_update hSet hM h.2⟩

theorem boolAbs_clearGuardIf_denote_update {locals locals' : List LocalSlot}
    {id : Nat} {newCs : LocalSlot} {ba : BoolAbs} {opt : Option Value}
    (hSet : set? locals id newCs = some locals')
    (h : ba.denote locals opt) :
    (ba.clearGuardIf id).denote locals' opt := by
  cases opt with
  | none =>
    cases ba with
    | uninit => exact True.intro
    | _ => exact False.elim h
  | some v =>
    simp only [BoolAbs.denote] at h ⊢
    cases hB : boolOfValue? v with
    | none => rw [hB] at h; exact h
    | some bv => rw [hB] at h; exact boolAbs_clearGuardIf_update hSet h

theorem boolAbs_clearGuardIf_isInit (id : Nat) (ba : BoolAbs) :
    (ba.clearGuardIf id).isInit = ba.isInit := by
  cases ba with
  | bot => rfl
  | uninit => rfl
  | top g =>
    simp only [BoolAbs.clearGuardIf]
    cases g.mentions id <;> rfl
  | exact c g =>
    simp only [BoolAbs.clearGuardIf]
    cases g.mentions id <;> rfl

/-- True iff `ba` is unreachable (`.bot`). -/
def BoolAbs.isBot : BoolAbs → Bool
  | .bot => true
  | _ => false

/-- True iff `ba` carries no frame-relative `RelGuard`. -/
def BoolAbs.noRelGuard : BoolAbs → Bool
  | .top g => RelGuard.beq g .none
  | .exact _ g => RelGuard.beq g .none
  | _ => true

theorem boolAbs_valDenote_of_denote {locals : List LocalSlot} {ba : BoolAbs}
    {v : Value} (hNoG : ba.noRelGuard = true) (hD : ba.denote locals (some v)) :
    ba.denote [] (some v) := by
  simp only [BoolAbs.denote] at hD ⊢
  cases hB : boolOfValue? v with
  | none => rw [hB] at hD; exact hD
  | some b =>
    rw [hB] at hD
    cases ba with
    | bot => exact hD
    | uninit => exact True.intro
    | top g =>
      simp only [BoolAbs.noRelGuard] at hNoG
      rw [relGuard_eq_of_beq hNoG]
      exact True.intro
    | exact c g =>
      simp only [BoolAbs.noRelGuard] at hNoG
      rw [relGuard_eq_of_beq hNoG]
      exact ⟨hD.1, True.intro⟩

theorem boolAbs_not_isBot {locals : List LocalSlot} {ba : BoolAbs}
    {opt : Option Value} (hBot : ba.isBot = true) (h : ba.denote locals opt) :
    False := by
  cases ba with
  | bot =>
    cases opt with
    | none => exact h
    | some v =>
      simp only [BoolAbs.denote] at h
      cases hB : boolOfValue? v with
      | none => rw [hB] at h; exact h
      | some b => rw [hB] at h; exact h
  | _ => nomatch hBot

/-- True iff `a` is unreachable (`InitDom.bot`). -/
def AbsVal.isBot (a : AbsVal) : Bool :=
  match a.init with
  | .bot => true
  | _ => false

theorem absVal_not_isBot {w : Nat} {a : AbsVal} {opt : Option Nat}
    (hBot : a.isBot = true) (h : a.denote w opt) : False := by
  cases a with
  | mk i0 tn wi sc =>
    cases i0 with
    | bot => exact h.1
    | _ => nomatch hBot

/-- Lower bound of an initialized, non-wrapping interval component. -/
def AbsVal.lbound? (a : AbsVal) : Option Nat :=
  match a.init, a.wi with
  | .init, .iv lo hi =>
    match Nat.ble lo hi with
    | true => some lo
    | false => none
  | _, _ => none

theorem absVal_lbound?_sound {w x lo : Nat} {a : AbsVal}
    (h : a.lbound? = some lo) (ha : a.denote w (some x)) : lo ≤ x := by
  have hWi := (absVal_some_elim ha).2.2.1
  unfold AbsVal.lbound? at h
  split at h
  · rename_i lo' hi _ hW
    split at h
    · rename_i hB
      injection h with h
      subst h
      rw [hW] at hWi
      simp only [WrappedInterval.denote, hB] at hWi
      exact hWi.2.2.2.1
    · nomatch h
  · nomatch h

/-- Upper bound of an initialized, non-wrapping interval component. -/
def AbsVal.ubound? (a : AbsVal) : Option Nat :=
  match a.init, a.wi with
  | .init, .iv lo hi =>
    match Nat.ble lo hi with
    | true => some hi
    | false => none
  | _, _ => none

theorem absVal_ubound?_sound {w x hi : Nat} {a : AbsVal}
    (h : a.ubound? = some hi) (ha : a.denote w (some x)) : x ≤ hi := by
  have hWi := (absVal_some_elim ha).2.2.1
  unfold AbsVal.ubound? at h
  split at h
  · rename_i lo hi' _ hW
    split at h
    · rename_i hB
      injection h with h
      subst h
      rw [hW] at hWi
      simp only [WrappedInterval.denote, hB] at hWi
      exact hWi.2.2.2.2
    · nomatch h
  · nomatch h

/-- Refine `a` under `x ≠ v` by tightening endpoint exclusions (`v = 0`,
`v = lo`, `v = hi`, or `v = 2^w - 1`). -/
def AbsVal.refineUneConst (w : Nat) (a : AbsVal) (v : Nat) : AbsVal :=
  match Nat.beq v 0 with
  | true => AbsVal.refineUgtConst w a 0
  | false =>
    match a.lbound? with
    | some lo =>
      match Nat.beq v lo with
      | true => AbsVal.refineUgtConst w a lo
      | false =>
        match a.ubound? with
        | some (k + 1) =>
          match Nat.beq v (k + 1) with
          | true => AbsVal.refineUleConst w a k
          | false => a
        | _ =>
          match Nat.beq v (modPow2 w - 1) with
          | true => AbsVal.refineUleConst w a (modPow2 w - 2)
          | false => a
    | none =>
      match Nat.beq v (modPow2 w - 1) with
      | true => AbsVal.refineUleConst w a (modPow2 w - 2)
      | false => a

/-- Soundness of `AbsVal.refineUneConst`. -/
theorem absVal_refineUneConst_sound {w x v : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x))
    (hai : a.isInit = true) (hNe : x ≠ v) :
    (AbsVal.refineUneConst w a v).denote w (some x) := by
  have hTopExcl : Nat.beq v (modPow2 w - 1) = true →
      (AbsVal.refineUleConst w a (modPow2 w - 2)).denote w (some x) := by
    intro hTop
    have hvEq := Nat.eq_of_beq_eq_true hTop
    have hxLe : x ≤ modPow2 w - 1 := Nat.le_sub_one_of_lt (absVal_some_elim ha).1
    have hxLt : x < modPow2 w - 1 :=
      Nat.lt_of_le_of_ne hxLe (fun hEq => hNe (Eq.trans hEq hvEq.symm))
    have hxLe2 : x ≤ modPow2 w - 2 := by
      have h1 : x ≤ (modPow2 w - 1) - 1 := Nat.le_sub_one_of_lt hxLt
      rw [Nat.sub_sub] at h1
      exact h1
    exact absVal_refineUleConst_sound hw ha hai hxLe2
  unfold AbsVal.refineUneConst
  cases h0 : Nat.beq v 0 with
  | true =>
    simp only
    have hv0 := Nat.eq_of_beq_eq_true h0
    subst hv0
    exact absVal_refineUgtConst_sound hw ha hai (Nat.pos_of_ne_zero hNe)
  | false =>
    simp only
    cases hLo : a.lbound? with
    | none =>
      simp only
      cases hTop : Nat.beq v (modPow2 w - 1) with
      | true => simp only; exact hTopExcl hTop
      | false => exact ha
    | some lo =>
      simp only
      cases hEqLo : Nat.beq v lo with
      | true =>
        simp only
        have hvLo := Nat.eq_of_beq_eq_true hEqLo
        subst hvLo
        exact absVal_refineUgtConst_sound hw ha hai
          (Nat.lt_of_le_of_ne (absVal_lbound?_sound hLo ha) (fun h => hNe h.symm))
      | false =>
        simp only
        cases hHi : a.ubound? with
        | none =>
          simp only
          cases hTop : Nat.beq v (modPow2 w - 1) with
          | true => simp only; exact hTopExcl hTop
          | false => exact ha
        | some hi =>
          cases hi with
          | zero =>
            simp only
            cases hTop : Nat.beq v (modPow2 w - 1) with
            | true => simp only; exact hTopExcl hTop
            | false => exact ha
          | succ k =>
            simp only
            cases hEqHi : Nat.beq v (k + 1) with
            | true =>
              simp only
              have hvHi := Nat.eq_of_beq_eq_true hEqHi
              subst hvHi
              exact absVal_refineUleConst_sound hw ha hai
                (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne
                  (absVal_ubound?_sound hHi ha) hNe))
            | false => exact ha

/-! ## 5. Abstract Local Slots (`MirAbsSlot`) and Frames (`MirAbsEnv`) -/

/-- Abstract local slot. `.top` describes any concrete slot (used for locals
of unsupported type), `.dead` a storage-dead local, `.uint` / `.bool` scalar
locals, `.unit isInit` a `()` local, and `.uintBoolPair` a `(u, bool)` checked
arithmetic tuple (`*WithOverflow`). `.uintCopy u a src` is a `.uint u a` slot
that, when initialized, additionally holds the same bit pattern as local `src`
(recorded by `_t = copy _src`, so that comparisons on the temporary `_t`
synthesize `RelGuard`s on `_src`). -/
inductive MirAbsSlot where
  | top
  | dead
  | uint (u : UintTy) (a : AbsVal)
  | bool (b : BoolAbs)
  | unit (isInit : Bool)
  | uintBoolPair (u : UintTy) (a : AbsVal) (ov : BoolAbs)
  | uintCopy (u : UintTy) (a : AbsVal) (src : Nat)

/-- Abstract MIR local frame, one `MirAbsSlot` per `LocalDecl`. -/
abbrev MirAbsEnv := List MirAbsSlot

/-- Concrete denotation of one `MirAbsSlot` at declared type `ty` against a
`LocalSlot` (`locals` is the enclosing frame, read by `RelGuard`s). -/
def MirAbsSlot.denote (ty : Ty) (locals : List LocalSlot) (slot : MirAbsSlot)
    (cs : LocalSlot) : Prop :=
  match slot with
  | .top => True
  | .dead => cs = .dead
  | .uint u a =>
    ty.kind = .uint u ∧
    match cs with
    | .dead => False
    | .uninit => a.denote (uintWidth u) none
    | .init v =>
      match v with
      | .scalar sc =>
        sc.sizeBytes = uintBytes u ∧ a.denote (uintWidth u) (some sc.bits)
      | _ => False
  | .bool ba =>
    ty.kind = .bool ∧
    match cs with
    | .dead => False
    | .uninit => ba.denote locals none
    | .init v => ba.denote locals (some v)
  | .unit isInit =>
    ty.kind = .tuple [] ∧
    match cs with
    | .dead => False
    | .uninit => isInit = false
    | .init v => v = .unit ∨ v = .aggregate 0 []
  | .uintBoolPair u a ov =>
    ty.kind = .tuple [.uint u, .bool] ∧
    match cs with
    | .dead => False
    | .uninit => a.denote (uintWidth u) none ∧ ov.denote locals none
    | .init v =>
      match v with
      | .aggregate 0 [.scalar sc, vb] =>
        sc.sizeBytes = uintBytes u ∧ a.denote (uintWidth u) (some sc.bits) ∧
        ov.denote locals (some vb)
      | _ => False
  | .uintCopy u a src =>
    ty.kind = .uint u ∧
    match cs with
    | .dead => False
    | .uninit => a.denote (uintWidth u) none
    | .init v =>
      match v with
      | .scalar sc =>
        sc.sizeBytes = uintBytes u ∧ a.denote (uintWidth u) (some sc.bits) ∧
        localUintNat? locals src u = some sc.bits
      | _ => False

/-- Forgetting the copy alias of a `.uintCopy` slot is sound. -/
theorem uintCopy_denote_uint {ty : Ty} {locals : List LocalSlot} {u : UintTy}
    {a : AbsVal} {src : Nat} {cs : LocalSlot}
    (h : (MirAbsSlot.uintCopy u a src).denote ty locals cs) :
    (MirAbsSlot.uint u a).denote ty locals cs := by
  refine ⟨h.1, ?_⟩
  cases cs with
  | dead => exact h.2
  | uninit => exact h.2
  | init v =>
    cases v with
    | scalar sc => exact ⟨h.2.1, h.2.2.1⟩
    | _ => exact h.2

/-- Live-but-uninitialized abstract slot for a local of declared type `ty`
(the abstract counterpart of `StorageLive` / `Deinit`). -/
def uninitSlotFor (ty : Ty) : MirAbsSlot :=
  match ty.kind with
  | .uint u => .uint u (AbsVal.uninit (uintWidth u))
  | .bool => .bool .uninit
  | .tuple [] => .unit false
  | .tuple [.uint u, .bool] => .uintBoolPair u (AbsVal.uninit (uintWidth u)) .uninit
  | _ => .top

theorem uninitSlotFor_denote (ty : Ty) (locals : List LocalSlot) :
    (uninitSlotFor ty).denote ty locals .uninit := by
  unfold uninitSlotFor
  split
  · rename_i u h
    exact ⟨h, absVal_uninit_sound_none⟩
  · rename_i h
    exact ⟨h, True.intro⟩
  · rename_i h
    exact ⟨h, rfl⟩
  · rename_i u h
    exact ⟨h, absVal_uninit_sound_none, True.intro⟩
  · exact True.intro

/-- `slot` guarantees the concrete local is live (not `.dead`). -/
def MirAbsSlot.isLive : MirAbsSlot → Bool
  | .top => false
  | .dead => false
  | _ => true

/-- `slot` guarantees an initialized value. -/
def MirAbsSlot.isInit : MirAbsSlot → Bool
  | .uint _ a => a.isInit
  | .bool ba => ba.isInit
  | .unit i => i
  | .uintBoolPair _ a ov => a.isInit && ov.isInit
  | .uintCopy _ a _ => a.isInit
  | _ => false

/-- `slot` is unreachable (empty concretization). -/
def MirAbsSlot.isBot : MirAbsSlot → Bool
  | .uint _ a => a.isBot
  | .bool ba => ba.isBot
  | .uintBoolPair _ a ov => a.isBot || ov.isBot
  | .uintCopy _ a _ => a.isBot
  | _ => false

theorem mirAbsSlot_not_isBot {ty : Ty} {locals : List LocalSlot}
    {s : MirAbsSlot} {cs : LocalSlot} (hBot : s.isBot = true)
    (h : s.denote ty locals cs) : False := by
  cases s with
  | top | dead | unit _ => nomatch hBot
  | uint u a =>
    cases cs with
    | dead => exact h.2
    | uninit => exact absVal_not_isBot hBot h.2
    | init v =>
      cases v with
      | scalar sc => exact absVal_not_isBot hBot h.2.2
      | _ => exact h.2
  | bool ba =>
    cases cs with
    | dead => exact h.2
    | uninit => exact boolAbs_not_isBot hBot h.2
    | init v => exact boolAbs_not_isBot hBot h.2
  | uintCopy u a src =>
    have h' := uintCopy_denote_uint h
    cases cs with
    | dead => exact h'.2
    | uninit => exact absVal_not_isBot hBot h'.2
    | init v =>
      cases v with
      | scalar sc => exact absVal_not_isBot hBot h'.2.2
      | _ => exact h'.2
  | uintBoolPair u a ov =>
    cases hA : a.isBot with
    | true =>
      cases cs with
      | dead => exact h.2
      | uninit => exact absVal_not_isBot hA h.2.1
      | init v =>
        cases v with
        | aggregate tag fs =>
          cases tag with
          | succ _ => exact h.2
          | zero =>
            cases fs with
            | nil => exact h.2
            | cons v0 rest =>
              cases v0 with
              | scalar sc =>
                cases rest with
                | nil => exact h.2
                | cons vb rest2 =>
                  cases rest2 with
                  | nil => exact absVal_not_isBot hA h.2.2.1
                  | cons _ _ => exact h.2
              | _ => exact h.2
        | _ => exact h.2
    | false =>
      simp only [MirAbsSlot.isBot, hA, Bool.false_or] at hBot
      cases cs with
      | dead => exact h.2
      | uninit => exact boolAbs_not_isBot hBot h.2.2
      | init v =>
        cases v with
        | aggregate tag fs =>
          cases tag with
          | succ _ => exact h.2
          | zero =>
            cases fs with
            | nil => exact h.2
            | cons v0 rest =>
              cases v0 with
              | scalar sc =>
                cases rest with
                | nil => exact h.2
                | cons vb rest2 =>
                  cases rest2 with
                  | nil => exact boolAbs_not_isBot hBot h.2.2.2
                  | cons _ _ => exact h.2
              | _ => exact h.2
        | _ => exact h.2

/-- Deinitialized live counterpart of a live `MirAbsSlot`. -/
def MirAbsSlot.toUninit : MirAbsSlot → MirAbsSlot
  | .uint u _ => .uint u (AbsVal.uninit (uintWidth u))
  | .bool _ => .bool .uninit
  | .unit _ => .unit false
  | .uintBoolPair u _ _ => .uintBoolPair u (AbsVal.uninit (uintWidth u)) .uninit
  | .uintCopy u _ _ => .uint u (AbsVal.uninit (uintWidth u))
  | _ => .top

theorem mirAbsSlot_toUninit_denote {ty : Ty} {locals : List LocalSlot}
    {s : MirAbsSlot} {cs : LocalSlot} (hLive : s.isLive = true)
    (h : s.denote ty locals cs) : s.toUninit.denote ty locals .uninit := by
  cases s with
  | top | dead => nomatch hLive
  | uint u _ => exact ⟨h.1, absVal_uninit_sound_none⟩
  | bool _ => exact ⟨h.1, True.intro⟩
  | unit _ => exact ⟨h.1, rfl⟩
  | uintBoolPair u _ _ => exact ⟨h.1, absVal_uninit_sound_none, True.intro⟩
  | uintCopy u _ _ => exact ⟨h.1, absVal_uninit_sound_none⟩

theorem mirAbsSlot_live {ty : Ty} {locals : List LocalSlot} {s : MirAbsSlot}
    {cs : LocalSlot} (hLive : s.isLive = true) (h : s.denote ty locals cs) :
    cs ≠ .dead := by
  intro hD
  subst hD
  cases s with
  | top => nomatch hLive
  | dead => nomatch hLive
  | uint _ _ => exact h.2
  | bool _ => exact h.2
  | unit _ => exact h.2
  | uintBoolPair _ _ _ => exact h.2
  | uintCopy _ _ _ => exact h.2

/-- An initialized slot denotes an initialized concrete local. -/
theorem mirAbsSlot_init {ty : Ty} {locals : List LocalSlot} {s : MirAbsSlot}
    {cs : LocalSlot} (hInit : s.isInit = true) (h : s.denote ty locals cs) :
    ∃ v, cs = .init v ∧ valueContainsUninit v = false := by
  cases s with
  | top => nomatch hInit
  | dead => nomatch hInit
  | uint u a =>
    cases cs with
    | dead => exact False.elim h.2
    | uninit =>
      cases absVal_init_of_isInit hInit h.2 with
      | intro _ hx => nomatch hx.1
    | init v =>
      cases v with
      | scalar sc => exact ⟨.scalar sc, rfl, rfl⟩
      | _ => exact False.elim h.2
  | bool ba =>
    cases cs with
    | dead => exact False.elim h.2
    | uninit =>
      cases ba with
      | top _ => exact False.elim h.2
      | exact _ _ => exact False.elim h.2
      | bot => nomatch hInit
      | uninit => nomatch hInit
    | init v =>
      cases boolAbs_denote_some h.2 with
      | intro b hb =>
        rw [hb.1]
        exact ⟨_, rfl, rfl⟩
  | unit i =>
    cases cs with
    | dead => exact False.elim h.2
    | uninit =>
      have hF : i = false := h.2
      rw [hF] at hInit
      nomatch hInit
    | init v =>
      cases h.2 with
      | inl hV =>
        rw [hV]
        exact ⟨_, rfl, rfl⟩
      | inr hV =>
        rw [hV]
        exact ⟨_, rfl, rfl⟩
  | uintBoolPair u a ov =>
    have hAInit := bool_and_true_left hInit
    cases cs with
    | dead => exact False.elim h.2
    | uninit =>
      cases absVal_init_of_isInit hAInit h.2.1 with
      | intro _ hx => nomatch hx.1
    | init v =>
      cases v with
      | aggregate tag fs =>
        cases tag with
        | succ _ => exact False.elim h.2
        | zero =>
          cases fs with
          | nil => exact False.elim h.2
          | cons v0 rest =>
            cases v0 with
            | scalar sc =>
              cases rest with
              | nil => exact False.elim h.2
              | cons vb rest2 =>
                cases rest2 with
                | cons _ _ => exact False.elim h.2
                | nil =>
                  cases boolAbs_denote_some h.2.2.2 with
                  | intro b hb =>
                    rw [hb.1]
                    exact ⟨_, rfl, rfl⟩
            | _ => exact False.elim h.2
      | _ => exact False.elim h.2
  | uintCopy u a src =>
    cases cs with
    | dead => exact False.elim h.2
    | uninit =>
      cases absVal_init_of_isInit hInit h.2 with
      | intro _ hx => nomatch hx.1
    | init v =>
      cases v with
      | scalar sc => exact ⟨.scalar sc, rfl, rfl⟩
      | _ => exact False.elim h.2

/-- Extract the concrete scalar of an initialized `.uint` slot. -/
theorem uint_slot_extract {ty : Ty} {locals : List LocalSlot} {u : UintTy}
    {a : AbsVal} {cs : LocalSlot} (hInit : a.isInit = true)
    (h : (MirAbsSlot.uint u a).denote ty locals cs) :
    ∃ sc, cs = .init (.scalar sc) ∧ sc.sizeBytes = uintBytes u ∧
      a.denote (uintWidth u) (some sc.bits) := by
  cases cs with
  | dead => exact False.elim h.2
  | uninit =>
    cases absVal_init_of_isInit hInit h.2 with
    | intro _ hx => nomatch hx.1
  | init v =>
    cases v with
    | scalar sc => exact ⟨sc, rfl, h.2.1, h.2.2⟩
    | _ => exact False.elim h.2

/-- Extract the concrete `(scalar, bool)` aggregate of an initialized
`.uintBoolPair` slot. -/
theorem uintBoolPair_slot_extract {ty : Ty} {locals : List LocalSlot}
    {u : UintTy} {a : AbsVal} {ov : BoolAbs} {cs : LocalSlot}
    (hInit : (a.isInit && ov.isInit) = true)
    (h : (MirAbsSlot.uintBoolPair u a ov).denote ty locals cs) :
    ∃ sc vb, cs = .init (.aggregate 0 [.scalar sc, vb]) ∧
      sc.sizeBytes = uintBytes u ∧ a.denote (uintWidth u) (some sc.bits) ∧
      ov.denote locals (some vb) := by
  have hAInit := bool_and_true_left hInit
  cases cs with
  | dead => exact False.elim h.2
  | uninit =>
    cases absVal_init_of_isInit hAInit h.2.1 with
    | intro _ hx => nomatch hx.1
  | init v =>
    cases v with
    | aggregate tag fs =>
      cases tag with
      | succ _ => exact False.elim h.2
      | zero =>
        cases fs with
        | nil => exact False.elim h.2
        | cons v0 rest =>
          cases v0 with
          | scalar sc =>
            cases rest with
            | nil => exact False.elim h.2
            | cons vb rest2 =>
              cases rest2 with
              | cons _ _ => exact False.elim h.2
              | nil => exact ⟨sc, vb, rfl, h.2.1, h.2.2.1, h.2.2.2⟩
          | _ => exact False.elim h.2
    | _ => exact False.elim h.2

/-- True iff `slot` carries no frame-relative `RelGuard` (required of return
postcondition slots, which describe a returned `Value` after frame exit). -/
def MirAbsSlot.noRelGuard : MirAbsSlot → Bool
  | .bool ba => ba.noRelGuard
  | .uintBoolPair _ _ ov => ov.noRelGuard
  | .uintCopy _ _ _ => false
  | _ => true

/-- Frame-independent value denotation of a slot at declared type `ty`. -/
def MirAbsSlot.valDenote (ty : Ty) (slot : MirAbsSlot) (v : Value) : Prop :=
  slot.denote ty [] (.init v)

/-- A guard-free slot denoting `.init v` in any frame satisfies the
frame-independent `valDenote ty v`. -/
theorem mirAbsSlot_valDenote_of_denote {ty : Ty} {locals : List LocalSlot}
    {slot : MirAbsSlot} {v : Value} (hNoG : slot.noRelGuard = true)
    (hDen : slot.denote ty locals (.init v)) : slot.valDenote ty v := by
  cases slot with
  | top => exact True.intro
  | dead => exact hDen
  | uint _ _ => exact hDen
  | unit _ => exact hDen
  | bool ba => exact ⟨hDen.1, boolAbs_valDenote_of_denote hNoG hDen.2⟩
  | uintCopy _ _ _ => nomatch hNoG
  | uintBoolPair u a ov =>
    refine ⟨hDen.1, ?_⟩
    cases v with
    | aggregate tag fs =>
      cases tag with
      | succ _ => exact hDen.2
      | zero =>
        cases fs with
        | nil => exact hDen.2
        | cons v0 rest =>
          cases v0 with
          | scalar sc =>
            cases rest with
            | nil => exact hDen.2
            | cons vb rest2 =>
              cases rest2 with
              | cons _ _ => exact hDen.2
              | nil =>
                exact ⟨hDen.2.1, hDen.2.2.1,
                  boolAbs_valDenote_of_denote hNoG hDen.2.2.2⟩
          | _ => exact hDen.2
    | _ => exact hDen.2

/-- Drop any `RelGuard` mentioning `id` from a slot. -/
def MirAbsSlot.clearGuardIf (id : Nat) : MirAbsSlot → MirAbsSlot
  | .bool ba => .bool (ba.clearGuardIf id)
  | .uintBoolPair u a ov => .uintBoolPair u a (ov.clearGuardIf id)
  | .uintCopy u a src =>
    match Nat.beq src id with
    | true => .uint u a
    | false => .uintCopy u a src
  | s => s

theorem mirAbsSlot_clearGuardIf_update {ty : Ty}
    {locals locals' : List LocalSlot} {id : Nat} {newCs : LocalSlot}
    {s : MirAbsSlot} {cs : LocalSlot}
    (hSet : set? locals id newCs = some locals')
    (h : s.denote ty locals cs) : (s.clearGuardIf id).denote ty locals' cs := by
  cases s with
  | top => exact h
  | dead => exact h
  | uint _ _ => exact h
  | unit _ => exact h
  | bool ba =>
    refine ⟨h.1, ?_⟩
    cases cs with
    | dead => exact h.2
    | uninit => exact boolAbs_clearGuardIf_denote_update hSet h.2
    | init v => exact boolAbs_clearGuardIf_denote_update hSet h.2
  | uintCopy u a src =>
    cases hS : Nat.beq src id with
    | true =>
      simp only [MirAbsSlot.clearGuardIf, hS]
      have h' := uintCopy_denote_uint h
      exact h'
    | false =>
      simp only [MirAbsSlot.clearGuardIf, hS]
      refine ⟨h.1, ?_⟩
      cases cs with
      | dead => exact h.2
      | uninit => exact h.2
      | init v =>
        cases v with
        | scalar sc =>
          refine ⟨h.2.1, h.2.2.1, ?_⟩
          rw [localUintNat?_set?_ne u hSet (fun hE => nat_ne_of_beq_false hS hE.symm)]
          exact h.2.2.2
        | _ => exact h.2
  | uintBoolPair u a ov =>
    refine ⟨h.1, ?_⟩
    cases cs with
    | dead => exact h.2
    | uninit => exact ⟨h.2.1, boolAbs_clearGuardIf_denote_update hSet h.2.2⟩
    | init v =>
      cases v with
      | aggregate tag fs =>
        cases tag with
        | succ _ => exact h.2
        | zero =>
          cases fs with
          | nil => exact h.2
          | cons v0 rest =>
            cases v0 with
            | scalar sc =>
              cases rest with
              | nil => exact h.2
              | cons vb rest2 =>
                cases rest2 with
                | cons _ _ => exact h.2
                | nil =>
                  exact ⟨h.2.1, h.2.2.1,
                    boolAbs_clearGuardIf_denote_update hSet h.2.2.2⟩
            | _ => exact h.2
      | _ => exact h.2

/-- Concrete denotation of `MirAbsEnv` on a concrete MIR local frame typed by
`decls`. -/
def mirAbsEnvDenote (decls : List LocalDecl) (env : MirAbsEnv)
    (locals : List LocalSlot) : Prop :=
  length env = length decls ∧
  length locals = length decls ∧
  ∀ (i : Nat) (d : LocalDecl) (s : MirAbsSlot) (cs : LocalSlot),
    get? decls i = some d →
    get? env i = some s →
    get? locals i = some cs →
    s.denote d.ty locals cs

/-- Look up the declaration and concrete slot behind an abstract slot. -/
theorem mirAbsEnv_lookup {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {i : Nat} {s : MirAbsSlot}
    (hEnv : mirAbsEnvDenote decls env locals) (hGet : get? env i = some s) :
    ∃ d cs, get? decls i = some d ∧ get? locals i = some cs ∧
      s.denote d.ty locals cs := by
  cases get?_exists_of_length hEnv.1.symm hGet with
  | intro d hD =>
    cases get?_exists_of_length (Eq.trans hEnv.2.1 hEnv.1.symm) hGet with
    | intro cs hCs => exact ⟨d, cs, hD, hCs, hEnv.2.2 i d s cs hD hGet hCs⟩

/-- True iff some slot in `env` is unreachable (`.isBot`). -/
def mirAbsEnvIsBot : MirAbsEnv → Bool
  | [] => false
  | s :: rest => s.isBot || mirAbsEnvIsBot rest

theorem mirAbsEnvIsBot_exists :
    ∀ {env : MirAbsEnv}, mirAbsEnvIsBot env = true →
      ∃ i s, get? env i = some s ∧ s.isBot = true
  | [], h => nomatch h
  | s :: rest, h => by
    simp only [mirAbsEnvIsBot] at h
    cases hs : s.isBot with
    | true => exact ⟨0, s, rfl, hs⟩
    | false =>
      rw [hs, Bool.false_or] at h
      cases mirAbsEnvIsBot_exists h with
      | intro i hi =>
        cases hi with
        | intro s' hs' => exact ⟨i + 1, s', hs'.1, hs'.2⟩

/-- An unreachable abstract environment denotes no concrete frame. -/
theorem mirAbsEnv_not_isBot {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} (hBot : mirAbsEnvIsBot env = true)
    (hEnv : mirAbsEnvDenote decls env locals) : False := by
  cases mirAbsEnvIsBot_exists hBot with
  | intro i hi =>
    cases hi with
    | intro s hs =>
      cases mirAbsEnv_lookup hEnv hs.1 with
      | intro d hd =>
        cases hd with
        | intro cs hcs => exact mirAbsSlot_not_isBot hs.2 hcs.2.2

/-- Pointwise lattice inclusion on `MirAbsSlot`. -/
def MirAbsSlot.le (a b : MirAbsSlot) : Bool :=
  match a.isBot with
  | true => true
  | false =>
    match a, b with
    | _, .top => true
    | .dead, .dead => true
    | .uint u1 a1, .uint u2 a2 =>
      uintTyBeq u1 u2 && AbsVal.le (uintWidth u1) a1 a2
    | .bool b1, .bool b2 => BoolAbs.le b1 b2
    | .unit i1, .unit i2 => !i2 || i1
    | .uintBoolPair u1 a1 ov1, .uintBoolPair u2 a2 ov2 =>
      uintTyBeq u1 u2 && AbsVal.le (uintWidth u1) a1 a2 && BoolAbs.le ov1 ov2
    | .uintCopy u1 a1 _, .uint u2 a2 =>
      uintTyBeq u1 u2 && AbsVal.le (uintWidth u1) a1 a2
    | .uintCopy u1 a1 s1, .uintCopy u2 a2 s2 =>
      (uintTyBeq u1 u2 && Nat.beq s1 s2) && AbsVal.le (uintWidth u1) a1 a2
    | _, _ => false

/-- Soundness of `MirAbsSlot.le`. -/
theorem mirAbsSlot_le_sound {ty : Ty} {locals : List LocalSlot}
    {a b : MirAbsSlot} {cs : LocalSlot}
    (hLe : MirAbsSlot.le a b = true) (ha : a.denote ty locals cs) :
    b.denote ty locals cs := by
  cases hBot : a.isBot with
  | true => exact False.elim (mirAbsSlot_not_isBot hBot ha)
  | false =>
    simp only [MirAbsSlot.le, hBot] at hLe
    cases b with
    | top => exact True.intro
    | dead =>
      cases a with
      | dead => exact ha
      | _ => nomatch hLe
    | uint u2 a2 =>
      cases a with
      | uint u1 a1 =>
        have hu := uintTy_eq_of_beq (bool_and_true_left hLe)
        have hA := bool_and_true_right hLe
        subst hu
        refine ⟨ha.1, ?_⟩
        cases cs with
        | dead => exact ha.2
        | uninit => exact absVal_le_sound hA ha.2
        | init v =>
          cases v with
          | scalar sc => exact ⟨ha.2.1, absVal_le_sound hA ha.2.2⟩
          | _ => exact ha.2
      | uintCopy u1 a1 s1 =>
        have hu := uintTy_eq_of_beq (bool_and_true_left hLe)
        have hA := bool_and_true_right hLe
        subst hu
        refine ⟨ha.1, ?_⟩
        cases cs with
        | dead => exact ha.2
        | uninit => exact absVal_le_sound hA ha.2
        | init v =>
          cases v with
          | scalar sc => exact ⟨ha.2.1, absVal_le_sound hA ha.2.2.1⟩
          | _ => exact ha.2
      | _ => nomatch hLe
    | uintCopy u2 a2 s2 =>
      cases a with
      | uintCopy u1 a1 s1 =>
        have h12 := bool_and_true_left hLe
        have hu := uintTy_eq_of_beq (bool_and_true_left h12)
        have hs := Nat.eq_of_beq_eq_true (bool_and_true_right h12)
        have hA := bool_and_true_right hLe
        subst hu
        subst hs
        refine ⟨ha.1, ?_⟩
        cases cs with
        | dead => exact ha.2
        | uninit => exact absVal_le_sound hA ha.2
        | init v =>
          cases v with
          | scalar sc => exact ⟨ha.2.1, absVal_le_sound hA ha.2.2.1, ha.2.2.2⟩
          | _ => exact ha.2
      | _ => nomatch hLe
    | bool b2 =>
      cases a with
      | bool b1 =>
        refine ⟨ha.1, ?_⟩
        cases cs with
        | dead => exact ha.2
        | uninit => exact boolAbs_le_sound hLe ha.2
        | init v => exact boolAbs_le_sound hLe ha.2
      | _ => nomatch hLe
    | unit i2 =>
      cases a with
      | unit i1 =>
        refine ⟨ha.1, ?_⟩
        cases cs with
        | dead => exact ha.2
        | init v => exact ha.2
        | uninit =>
          have hF : i1 = false := ha.2
          subst hF
          cases i2 with
          | false => rfl
          | true => nomatch hLe
      | _ => nomatch hLe
    | uintBoolPair u2 a2 ov2 =>
      cases a with
      | uintBoolPair u1 a1 ov1 =>
        have h12 := bool_and_true_left hLe
        have hu := uintTy_eq_of_beq (bool_and_true_left h12)
        have hA := bool_and_true_right h12
        have hOv := bool_and_true_right hLe
        subst hu
        refine ⟨ha.1, ?_⟩
        cases cs with
        | dead => exact ha.2
        | uninit => exact ⟨absVal_le_sound hA ha.2.1, boolAbs_le_sound hOv ha.2.2⟩
        | init v =>
          cases v with
          | aggregate tag fs =>
            cases tag with
            | succ _ => exact ha.2
            | zero =>
              cases fs with
              | nil => exact ha.2
              | cons v0 rest =>
                cases v0 with
                | scalar sc =>
                  cases rest with
                  | nil => exact ha.2
                  | cons vb rest2 =>
                    cases rest2 with
                    | cons _ _ => exact ha.2
                    | nil =>
                      exact ⟨ha.2.1, absVal_le_sound hA ha.2.2.1,
                        boolAbs_le_sound hOv ha.2.2.2⟩
                | _ => exact ha.2
          | _ => exact ha.2
      | _ => nomatch hLe

/-- Pointwise inclusion on `MirAbsEnv`. -/
def mirAbsEnvLe : MirAbsEnv → MirAbsEnv → Bool
  | [], [] => true
  | a :: as, b :: bs => MirAbsSlot.le a b && mirAbsEnvLe as bs
  | _, _ => false

theorem mirAbsEnvLe_length :
    ∀ {e1 e2 : MirAbsEnv}, mirAbsEnvLe e1 e2 = true → length e1 = length e2
  | [], [], _ => rfl
  | _ :: _, _ :: _, h =>
    congrArg Nat.succ (mirAbsEnvLe_length (bool_and_true_right h))
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem mirAbsEnvLe_get :
    ∀ {e1 e2 : MirAbsEnv} {i : Nat} {a b : MirAbsSlot},
      mirAbsEnvLe e1 e2 = true → get? e1 i = some a → get? e2 i = some b →
      MirAbsSlot.le a b = true
  | [], _, _, _, _, _, h1, _ => nomatch h1
  | _ :: _, [], _, _, _, h, _, _ => nomatch h
  | _ :: _, _ :: _, 0, _, _, h, h1, h2 => by
    injection h1 with ha
    injection h2 with hb
    subst ha
    subst hb
    exact bool_and_true_left h
  | _ :: xs, _ :: ys, i + 1, _, _, h, h1, h2 =>
    mirAbsEnvLe_get (e1 := xs) (e2 := ys) (i := i) (bool_and_true_right h) h1 h2

/-- Soundness of `mirAbsEnvLe`. -/
theorem mirAbsEnvLe_sound {decls : List LocalDecl} {e1 e2 : MirAbsEnv}
    {locals : List LocalSlot}
    (hLe : mirAbsEnvLe e1 e2 = true) (h1 : mirAbsEnvDenote decls e1 locals) :
    mirAbsEnvDenote decls e2 locals := by
  refine ⟨Eq.trans (mirAbsEnvLe_length hLe).symm h1.1, h1.2.1, ?_⟩
  intro i d s2 cs hD h2 hCs
  cases get?_exists_of_length (mirAbsEnvLe_length hLe) h2 with
  | intro s1 hs1 =>
    exact mirAbsSlot_le_sound (mirAbsEnvLe_get hLe hs1 h2)
      (h1.2.2 i d s1 cs hD hs1 hCs)

/-- Join of two plain unsigned slots (`.top` on a type mismatch). -/
def uintJoinSlot (u1 : UintTy) (a1 : AbsVal) (u2 : UintTy) (a2 : AbsVal) :
    MirAbsSlot :=
  match uintTyBeq u1 u2 with
  | true => .uint u1 (AbsVal.join (uintWidth u1) a1 a2)
  | false => .top

theorem uintJoinSlot_sound_left {ty : Ty} {locals : List LocalSlot}
    {u1 u2 : UintTy} {a1 a2 : AbsVal} {cs : LocalSlot}
    (ha : (MirAbsSlot.uint u1 a1).denote ty locals cs) :
    (uintJoinSlot u1 a1 u2 a2).denote ty locals cs := by
  unfold uintJoinSlot
  cases uintTyBeq u1 u2 with
  | false => exact True.intro
  | true =>
    refine ⟨ha.1, ?_⟩
    cases cs with
    | dead => exact ha.2
    | uninit => exact absVal_join_sound_left (uintWidth_valid u1) a1 a2 ha.2
    | init v =>
      cases v with
      | scalar sc =>
        exact ⟨ha.2.1, absVal_join_sound_left (uintWidth_valid u1) a1 a2 ha.2.2⟩
      | _ => exact ha.2

theorem uintJoinSlot_sound_right {ty : Ty} {locals : List LocalSlot}
    {u1 u2 : UintTy} {a1 a2 : AbsVal} {cs : LocalSlot}
    (hb : (MirAbsSlot.uint u2 a2).denote ty locals cs) :
    (uintJoinSlot u1 a1 u2 a2).denote ty locals cs := by
  unfold uintJoinSlot
  cases hU : uintTyBeq u1 u2 with
  | false => exact True.intro
  | true =>
    have hu := uintTy_eq_of_beq hU
    subst hu
    refine ⟨hb.1, ?_⟩
    cases cs with
    | dead => exact hb.2
    | uninit => exact absVal_join_sound_right (uintWidth_valid u1) a1 a2 hb.2
    | init v =>
      cases v with
      | scalar sc =>
        exact ⟨hb.2.1, absVal_join_sound_right (uintWidth_valid u1) a1 a2 hb.2.2⟩
      | _ => exact hb.2

/-- Pointwise join on `MirAbsSlot` (unreachable slots act as bottom;
incompatible live tags join to `.top`). -/
def MirAbsSlot.join (a b : MirAbsSlot) : MirAbsSlot :=
  match a.isBot, b.isBot with
  | true, _ => b
  | false, true => a
  | false, false =>
    match a, b with
    | .dead, .dead => .dead
    | .uint u1 a1, .uint u2 a2 =>
      match uintTyBeq u1 u2 with
      | true => .uint u1 (AbsVal.join (uintWidth u1) a1 a2)
      | false => .top
    | .bool b1, .bool b2 => .bool (BoolAbs.join b1 b2)
    | .unit i1, .unit i2 => .unit (i1 && i2)
    | .uintBoolPair u1 a1 ov1, .uintBoolPair u2 a2 ov2 =>
      match uintTyBeq u1 u2 with
      | true =>
        .uintBoolPair u1 (AbsVal.join (uintWidth u1) a1 a2)
          (BoolAbs.join ov1 ov2)
      | false => .top
    | .uintCopy u1 a1 s1, .uintCopy u2 a2 s2 =>
      match Nat.beq s1 s2 with
      | true =>
        match uintTyBeq u1 u2 with
        | true => .uintCopy u1 (AbsVal.join (uintWidth u1) a1 a2) s1
        | false => .top
      | false => uintJoinSlot u1 a1 u2 a2
    | .uintCopy u1 a1 _, .uint u2 a2 => uintJoinSlot u1 a1 u2 a2
    | .uint u1 a1, .uintCopy u2 a2 _ => uintJoinSlot u1 a1 u2 a2
    | _, _ => .top

theorem mirAbsSlot_join_sound_left {ty : Ty} {locals : List LocalSlot}
    {a b : MirAbsSlot} {cs : LocalSlot} (ha : a.denote ty locals cs) :
    (MirAbsSlot.join a b).denote ty locals cs := by
  cases hBa : a.isBot with
  | true => exact False.elim (mirAbsSlot_not_isBot hBa ha)
  | false =>
    cases hBb : b.isBot with
    | true => simp only [MirAbsSlot.join, hBa, hBb]; exact ha
    | false =>
      simp only [MirAbsSlot.join, hBa, hBb]
      cases a with
      | top => cases b <;> exact True.intro
      | dead => cases b <;> first | exact ha | exact True.intro
      | uint u1 a1 =>
        cases b with
        | uint u2 a2 =>
          simp only
          cases uintTyBeq u1 u2 with
          | false => exact True.intro
          | true =>
            refine ⟨ha.1, ?_⟩
            cases cs with
            | dead => exact ha.2
            | uninit => exact absVal_join_sound_left (uintWidth_valid u1) a1 a2 ha.2
            | init v =>
              cases v with
              | scalar sc =>
                exact ⟨ha.2.1, absVal_join_sound_left (uintWidth_valid u1) a1 a2 ha.2.2⟩
              | _ => exact ha.2
        | uintCopy u2 a2 s2 => exact uintJoinSlot_sound_left ha
        | _ => exact True.intro
      | uintCopy u1 a1 s1 =>
        cases b with
        | uintCopy u2 a2 s2 =>
          simp only
          cases hS : Nat.beq s1 s2 with
          | false => exact uintJoinSlot_sound_left (uintCopy_denote_uint ha)
          | true =>
            simp only
            cases uintTyBeq u1 u2 with
            | false => exact True.intro
            | true =>
              refine ⟨ha.1, ?_⟩
              cases cs with
              | dead => exact ha.2
              | uninit =>
                exact absVal_join_sound_left (uintWidth_valid u1) a1 a2 ha.2
              | init v =>
                cases v with
                | scalar sc =>
                  exact ⟨ha.2.1,
                    absVal_join_sound_left (uintWidth_valid u1) a1 a2 ha.2.2.1,
                    ha.2.2.2⟩
                | _ => exact ha.2
        | uint u2 a2 => exact uintJoinSlot_sound_left (uintCopy_denote_uint ha)
        | _ => exact True.intro
      | bool b1 =>
        cases b with
        | bool b2 =>
          simp only
          refine ⟨ha.1, ?_⟩
          cases cs with
          | dead => exact ha.2
          | uninit => exact boolAbs_join_sound_left ha.2
          | init v => exact boolAbs_join_sound_left ha.2
        | _ => exact True.intro
      | unit i1 =>
        cases b with
        | unit i2 =>
          simp only
          refine ⟨ha.1, ?_⟩
          cases cs with
          | dead => exact ha.2
          | init v => exact ha.2
          | uninit =>
            have hF : i1 = false := ha.2
            subst hF
            rfl
        | _ => exact True.intro
      | uintBoolPair u1 a1 ov1 =>
        cases b with
        | uintBoolPair u2 a2 ov2 =>
          simp only
          cases uintTyBeq u1 u2 with
          | false => exact True.intro
          | true =>
            refine ⟨ha.1, ?_⟩
            cases cs with
            | dead => exact ha.2
            | uninit =>
              exact ⟨absVal_join_sound_left (uintWidth_valid u1) a1 a2 ha.2.1,
                boolAbs_join_sound_left ha.2.2⟩
            | init v =>
              cases v with
              | aggregate tag fs =>
                cases tag with
                | succ _ => exact ha.2
                | zero =>
                  cases fs with
                  | nil => exact ha.2
                  | cons v0 rest =>
                    cases v0 with
                    | scalar sc =>
                      cases rest with
                      | nil => exact ha.2
                      | cons vb rest2 =>
                        cases rest2 with
                        | cons _ _ => exact ha.2
                        | nil =>
                          exact ⟨ha.2.1,
                            absVal_join_sound_left (uintWidth_valid u1) a1 a2 ha.2.2.1,
                            boolAbs_join_sound_left ha.2.2.2⟩
                    | _ => exact ha.2
              | _ => exact ha.2
        | _ => exact True.intro

theorem mirAbsSlot_join_sound_right {ty : Ty} {locals : List LocalSlot}
    {a b : MirAbsSlot} {cs : LocalSlot} (hb : b.denote ty locals cs) :
    (MirAbsSlot.join a b).denote ty locals cs := by
  cases hBb : b.isBot with
  | true => exact False.elim (mirAbsSlot_not_isBot hBb hb)
  | false =>
    cases hBa : a.isBot with
    | true => simp only [MirAbsSlot.join, hBa]; exact hb
    | false =>
      simp only [MirAbsSlot.join, hBa, hBb]
      cases b with
      | top => cases a <;> exact True.intro
      | dead => cases a <;> first | exact hb | exact True.intro
      | uint u2 a2 =>
        cases a with
        | uint u1 a1 =>
          simp only
          cases hU : uintTyBeq u1 u2 with
          | false => exact True.intro
          | true =>
            have hu := uintTy_eq_of_beq hU
            subst hu
            refine ⟨hb.1, ?_⟩
            cases cs with
            | dead => exact hb.2
            | uninit => exact absVal_join_sound_right (uintWidth_valid u1) a1 a2 hb.2
            | init v =>
              cases v with
              | scalar sc =>
                exact ⟨hb.2.1, absVal_join_sound_right (uintWidth_valid u1) a1 a2 hb.2.2⟩
              | _ => exact hb.2
        | uintCopy u1 a1 s1 => exact uintJoinSlot_sound_right hb
        | _ => exact True.intro
      | uintCopy u2 a2 s2 =>
        cases a with
        | uintCopy u1 a1 s1 =>
          simp only
          cases hS : Nat.beq s1 s2 with
          | false => exact uintJoinSlot_sound_right (uintCopy_denote_uint hb)
          | true =>
            have hs := Nat.eq_of_beq_eq_true hS
            subst hs
            simp only
            cases hU : uintTyBeq u1 u2 with
            | false => exact True.intro
            | true =>
              have hu := uintTy_eq_of_beq hU
              subst hu
              refine ⟨hb.1, ?_⟩
              cases cs with
              | dead => exact hb.2
              | uninit =>
                exact absVal_join_sound_right (uintWidth_valid u1) a1 a2 hb.2
              | init v =>
                cases v with
                | scalar sc =>
                  exact ⟨hb.2.1,
                    absVal_join_sound_right (uintWidth_valid u1) a1 a2 hb.2.2.1,
                    hb.2.2.2⟩
                | _ => exact hb.2
        | uint u1 a1 => exact uintJoinSlot_sound_right (uintCopy_denote_uint hb)
        | _ => exact True.intro
      | bool b2 =>
        cases a with
        | bool b1 =>
          simp only
          refine ⟨hb.1, ?_⟩
          cases cs with
          | dead => exact hb.2
          | uninit => exact boolAbs_join_sound_right hb.2
          | init v => exact boolAbs_join_sound_right hb.2
        | _ => exact True.intro
      | unit i2 =>
        cases a with
        | unit i1 =>
          simp only
          refine ⟨hb.1, ?_⟩
          cases cs with
          | dead => exact hb.2
          | init v => exact hb.2
          | uninit =>
            have hF : i2 = false := hb.2
            subst hF
            cases i1 <;> rfl
        | _ => exact True.intro
      | uintBoolPair u2 a2 ov2 =>
        cases a with
        | uintBoolPair u1 a1 ov1 =>
          simp only
          cases hU : uintTyBeq u1 u2 with
          | false => exact True.intro
          | true =>
            have hu := uintTy_eq_of_beq hU
            subst hu
            refine ⟨hb.1, ?_⟩
            cases cs with
            | dead => exact hb.2
            | uninit =>
              exact ⟨absVal_join_sound_right (uintWidth_valid u1) a1 a2 hb.2.1,
                boolAbs_join_sound_right hb.2.2⟩
            | init v =>
              cases v with
              | aggregate tag fs =>
                cases tag with
                | succ _ => exact hb.2
                | zero =>
                  cases fs with
                  | nil => exact hb.2
                  | cons v0 rest =>
                    cases v0 with
                    | scalar sc =>
                      cases rest with
                      | nil => exact hb.2
                      | cons vb rest2 =>
                        cases rest2 with
                        | cons _ _ => exact hb.2
                        | nil =>
                          exact ⟨hb.2.1,
                            absVal_join_sound_right (uintWidth_valid u1) a1 a2 hb.2.2.1,
                            boolAbs_join_sound_right hb.2.2.2⟩
                    | _ => exact hb.2
              | _ => exact hb.2
        | _ => exact True.intro

/-- Pointwise join on `MirAbsEnv` (fails closed on a length mismatch). -/
def mirAbsEnvJoin : MirAbsEnv → MirAbsEnv → Option MirAbsEnv
  | [], [] => some []
  | a :: as, b :: bs =>
    match mirAbsEnvJoin as bs with
    | some cs => some (MirAbsSlot.join a b :: cs)
    | none => none
  | _, _ => none

theorem mirAbsEnvJoin_get :
    ∀ {e1 e2 e3 : MirAbsEnv}, mirAbsEnvJoin e1 e2 = some e3 →
      length e1 = length e3 ∧ length e2 = length e3 ∧
      ∀ {i : Nat} {c : MirAbsSlot}, get? e3 i = some c →
        ∃ a b, get? e1 i = some a ∧ get? e2 i = some b ∧
          c = MirAbsSlot.join a b
  | [], [], e3, h => by
    injection h with h
    subst h
    exact ⟨rfl, rfl, fun hc => nomatch hc⟩
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | a :: as, b :: bs, e3, h => by
    simp only [mirAbsEnvJoin] at h
    cases hJ : mirAbsEnvJoin as bs with
    | none => rw [hJ] at h; nomatch h
    | some cs =>
      rw [hJ] at h
      injection h with h
      subst h
      have ih := mirAbsEnvJoin_get hJ
      refine ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2.1, ?_⟩
      intro i c hc
      cases i with
      | zero =>
        injection hc with hc
        exact ⟨a, b, rfl, rfl, hc.symm⟩
      | succ k => exact ih.2.2 hc

theorem mirAbsEnvJoin_sound_left {decls : List LocalDecl}
    {e1 e2 e3 : MirAbsEnv} {locals : List LocalSlot}
    (hJ : mirAbsEnvJoin e1 e2 = some e3) (h1 : mirAbsEnvDenote decls e1 locals) :
    mirAbsEnvDenote decls e3 locals := by
  have hG := mirAbsEnvJoin_get hJ
  refine ⟨Eq.trans hG.1.symm h1.1, h1.2.1, ?_⟩
  intro i d c cs hD hC hCs
  cases hG.2.2 hC with
  | intro a hab =>
    cases hab with
    | intro b hab =>
      rw [hab.2.2]
      exact mirAbsSlot_join_sound_left (h1.2.2 i d a cs hD hab.1 hCs)

theorem mirAbsEnvJoin_sound_right {decls : List LocalDecl}
    {e1 e2 e3 : MirAbsEnv} {locals : List LocalSlot}
    (hJ : mirAbsEnvJoin e1 e2 = some e3) (h2 : mirAbsEnvDenote decls e2 locals) :
    mirAbsEnvDenote decls e3 locals := by
  have hG := mirAbsEnvJoin_get hJ
  refine ⟨Eq.trans hG.2.1.symm h2.1, h2.2.1, ?_⟩
  intro i d c cs hD hC hCs
  cases hG.2.2 hC with
  | intro a hab =>
    cases hab with
    | intro b hab =>
      rw [hab.2.2]
      exact mirAbsSlot_join_sound_right (h2.2.2 i d b cs hD hab.2.1 hCs)

/-! ## 6. Guard-Clearing Writes (`setMirAbsSlot`) -/

/-- Clear every `RelGuard` in `env` mentioning local `id`. -/
def clearGuardsFor (id : Nat) (env : MirAbsEnv) : MirAbsEnv :=
  env.map (MirAbsSlot.clearGuardIf id)

/-- Abstract write `env[id] := newSlot`, clearing every `RelGuard` (including
the one carried by `newSlot`) that mentions `id`. -/
def setMirAbsSlot (id : Nat) (newSlot : MirAbsSlot) (env : MirAbsEnv) :
    Option MirAbsEnv :=
  set? (clearGuardsFor id env) id (newSlot.clearGuardIf id)

theorem setMirAbsSlot_some_of_get? {env : MirAbsEnv} {id : Nat}
    {s : MirAbsSlot} (newSlot : MirAbsSlot) (h : get? env id = some s) :
    ∃ env', setMirAbsSlot id newSlot env = some env' := by
  unfold setMirAbsSlot clearGuardsFor
  apply set?_some_of_get? (x := s.clearGuardIf id)
  rw [get?_map, h]
  rfl

/-- A concrete write `locals[id] := newCs` mirrored by
`setMirAbsSlot id newSlot env` preserves `mirAbsEnvDenote`, provided
`newSlot` denotes `newCs` in the pre-write frame. -/
theorem setMirAbsSlot_sound {decls : List LocalDecl} {env env' : MirAbsEnv}
    {locals locals' : List LocalSlot} {id : Nat} {newSlot : MirAbsSlot}
    {newCs : LocalSlot} {d : LocalDecl}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hDecl : get? decls id = some d)
    (hSetAbs : setMirAbsSlot id newSlot env = some env')
    (hSetConc : set? locals id newCs = some locals')
    (hNewDen : newSlot.denote d.ty locals newCs) :
    mirAbsEnvDenote decls env' locals' := by
  unfold setMirAbsSlot at hSetAbs
  have hLenClr : length (clearGuardsFor id env) = length env :=
    length_map _ env
  refine ⟨Eq.trans (length_set? hSetAbs) (Eq.trans hLenClr hEnv.1),
    Eq.trans (length_set? hSetConc) hEnv.2.1, ?_⟩
  intro i d' s cs hD hS hCs
  cases hEq : Nat.beq id i with
  | true =>
    have hI := Nat.eq_of_beq_eq_true hEq
    subst hI
    rw [get?_set?_same hSetAbs] at hS
    rw [get?_set?_same hSetConc] at hCs
    rw [hDecl] at hD
    injection hS with hs
    injection hCs with hcs
    injection hD with hd
    subst hs
    subst hcs
    subst hd
    exact mirAbsSlot_clearGuardIf_update hSetConc hNewDen
  | false =>
    have hNe := nat_ne_of_beq_false hEq
    rw [get?_set?_ne hSetAbs hNe] at hS
    rw [get?_set?_ne hSetConc hNe] at hCs
    unfold clearGuardsFor at hS
    rw [get?_map] at hS
    cases hOld : get? env i with
    | none => rw [hOld] at hS; nomatch hS
    | some old =>
      rw [hOld] at hS
      injection hS with hs
      subst hs
      exact mirAbsSlot_clearGuardIf_update hSetConc (hEnv.2.2 i d' old cs hD hOld hCs)

/-! ## 7. Branch Guard Refinement (`refineEnvByGuard`) -/

/-- Replace an initialized `.uint u` slot `a` at local `r` by `f a`. -/
def refineUintSlot (env : MirAbsEnv) (r : Nat) (u : UintTy)
    (f : AbsVal → AbsVal) : MirAbsEnv :=
  match get? env r with
  | some (.uint u' a) =>
    match uintTyBeq u u' && a.isInit with
    | true =>
      match set? env r (.uint u (f a)) with
      | some env' => env'
      | none => env
    | false => env
  | some (.uintCopy u' a src) =>
    match uintTyBeq u u' && a.isInit with
    | true =>
      match set? env r (.uintCopy u (f a) src) with
      | some env' => env'
      | none => env
    | false => env
  | _ => env

/-- In-place slot refinement at local `r` without modifying `locals`. -/
theorem refineSingleSlot_sound {decls : List LocalDecl} {env env' : MirAbsEnv}
    {locals : List LocalSlot} {r : Nat} {newSlot : MirAbsSlot}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hSet : set? env r newSlot = some env')
    (hRef : ∀ d cs, get? decls r = some d → get? locals r = some cs →
      newSlot.denote d.ty locals cs) :
    mirAbsEnvDenote decls env' locals := by
  refine ⟨Eq.trans (length_set? hSet) hEnv.1, hEnv.2.1, ?_⟩
  intro i d s cs hD hS hCs
  cases hEq : Nat.beq r i with
  | true =>
    have hI := Nat.eq_of_beq_eq_true hEq
    subst hI
    rw [get?_set?_same hSet] at hS
    injection hS with hs
    subst hs
    exact hRef d cs hD hCs
  | false =>
    rw [get?_set?_ne hSet (nat_ne_of_beq_false hEq)] at hS
    exact hEnv.2.2 i d s cs hD hS hCs

/-- Soundness of `refineUintSlot` under a pointwise refinement hypothesis. -/
theorem refineUintSlot_sound {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {r : Nat} {u : UintTy} {f : AbsVal → AbsVal}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hRef : ∀ (a : AbsVal) (x : Nat), a.isInit = true →
      a.denote (uintWidth u) (some x) → localUintNat? locals r u = some x →
      (f a).denote (uintWidth u) (some x)) :
    mirAbsEnvDenote decls (refineUintSlot env r u f) locals := by
  unfold refineUintSlot
  cases hGet : get? env r with
  | none => exact hEnv
  | some s =>
    cases s with
    | uint u' a =>
      simp only
      cases hC : (uintTyBeq u u' && a.isInit) with
      | false => exact hEnv
      | true =>
        have hu := uintTy_eq_of_beq (bool_and_true_left hC)
        have hInit := bool_and_true_right hC
        subst hu
        simp only
        cases hSet : set? env r (.uint u (f a)) with
        | none => exact hEnv
        | some env' =>
          simp only
          apply refineSingleSlot_sound hEnv hSet
          intro d cs hD hCs
          have hDen := hEnv.2.2 r d (.uint u a) cs hD hGet hCs
          cases uint_slot_extract hInit hDen with
          | intro sc hsc =>
            rw [hsc.1]
            rw [hsc.1] at hCs
            exact ⟨hDen.1, hsc.2.1, hRef a sc.bits hInit hsc.2.2
              (localUintNat?_of_get? hCs hsc.2.1)⟩
    | uintCopy u' a src =>
      simp only
      cases hC : (uintTyBeq u u' && a.isInit) with
      | false => exact hEnv
      | true =>
        have hu := uintTy_eq_of_beq (bool_and_true_left hC)
        have hInit := bool_and_true_right hC
        subst hu
        simp only
        cases hSet : set? env r (.uintCopy u (f a) src) with
        | none => exact hEnv
        | some env' =>
          simp only
          apply refineSingleSlot_sound hEnv hSet
          intro d cs hD hCs
          have hDen := hEnv.2.2 r d (.uintCopy u a src) cs hD hGet hCs
          cases uint_slot_extract hInit (uintCopy_denote_uint hDen) with
          | intro sc hsc =>
            rw [hsc.1] at hDen hCs ⊢
            exact ⟨hDen.1, hsc.2.1, hRef a sc.bits hInit hsc.2.2
              (localUintNat?_of_get? hCs hsc.2.1), hDen.2.2.2⟩
    | _ => exact hEnv

/-- Refine `env` using `RelGuard` `g` assuming boolean outcome `branchVal`.
Register-register guards refine both operands symmetrically; `.uneConst`
refines interval endpoints (`v = 0`, `v = lo`, `v = hi`, `v = 2^w - 1`). -/
def refineEnvByGuard (env : MirAbsEnv) (g : RelGuard) (branchVal : Bool) :
    MirAbsEnv :=
  let eff :=
    match branchVal with
    | true => g
    | false => g.negate
  match eff with
  | .none => env
  | .uleConst r u bound =>
    refineUintSlot env r u (fun a => AbsVal.refineUleConst (uintWidth u) a bound)
  | .ugtConst r u bound =>
    refineUintSlot env r u (fun a => AbsVal.refineUgtConst (uintWidth u) a bound)
  | .ultReg l r u =>
    let env₁ :=
      match get? env r with
      | some (.uint u' ar) =>
        match uintTyBeq u u' && ar.isInit with
        | true =>
          refineUintSlot env l u
            (fun al => AbsVal.refineBltReg (uintWidth u) al ar)
        | false => env
      | _ => env
    match get? env l with
    | some (.uint u' al) =>
      match uintTyBeq u u' && al.isInit, al.lbound? with
      | true, some loL =>
        refineUintSlot env₁ r u
          (fun ar => AbsVal.refineUgtConst (uintWidth u) ar loL)
      | _, _ => env₁
    | _ => env₁
  | .ugeReg l r u =>
    let env₁ :=
      match get? env r with
      | some (.uint u' ar) =>
        match uintTyBeq u u' && ar.isInit with
        | true =>
          refineUintSlot env l u
            (fun al => AbsVal.refineBgeReg (uintWidth u) al ar)
        | false => env
      | _ => env
    match get? env l with
    | some (.uint u' al) =>
      match uintTyBeq u u' && al.isInit, al.ubound? with
      | true, some hiL =>
        refineUintSlot env₁ r u
          (fun ar => AbsVal.refineUleConst (uintWidth u) ar hiL)
      | _, _ => env₁
    | _ => env₁
  | .ueqConst r u val =>
    refineUintSlot env r u (fun a => AbsVal.refineEqConst (uintWidth u) a val)
  | .uneConst r u val =>
    refineUintSlot env r u (fun a => AbsVal.refineUneConst (uintWidth u) a val)

/-- Concrete scalar of local `r` behind an initialized `.uint` slot. -/
theorem env_uint_extract {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {r : Nat} {u : UintTy} {a : AbsVal}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hGet : get? env r = some (.uint u a)) (hInit : a.isInit = true) :
    ∃ sc d, get? locals r = some (.init (.scalar sc)) ∧
      get? decls r = some d ∧ d.ty.kind = .uint u ∧
      sc.sizeBytes = uintBytes u ∧ a.denote (uintWidth u) (some sc.bits) ∧
      localUintNat? locals r u = some sc.bits := by
  cases mirAbsEnv_lookup hEnv hGet with
  | intro d hd =>
    cases hd with
    | intro cs hcs =>
      cases uint_slot_extract hInit hcs.2.2 with
      | intro sc hsc =>
        have hL : get? locals r = some (.init (.scalar sc)) := by
          rw [hcs.2.1, hsc.1]
        exact ⟨sc, d, hL, hcs.1, hcs.2.2.1, hsc.2.1, hsc.2.2,
          localUintNat?_of_get? hL hsc.2.1⟩

/-- Soundness of `refineEnvByGuard`. -/
theorem refineEnvByGuard_sound {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {g : RelGuard} {b : Bool}
    (hEnv : mirAbsEnvDenote decls env locals) (hGuard : g.denote locals b) :
    mirAbsEnvDenote decls (refineEnvByGuard env g b) locals := by
  have hEff : (match b with
      | true => g
      | false => g.negate).denote locals true := by
    cases b with
    | true => exact hGuard
    | false => exact relGuard_negate_sound hGuard
  unfold refineEnvByGuard
  generalize (match b with
      | true => g
      | false => g.negate) = eff at hEff ⊢
  cases eff with
  | none => exact hEnv
  | uneConst r u val =>
    apply refineUintSlot_sound hEnv
    intro a x hInit ha hx
    exact absVal_refineUneConst_sound (uintWidth_valid u) ha hInit
      ((hEff x hx).mp rfl)
  | uleConst r u bound =>
    apply refineUintSlot_sound hEnv
    intro a x hInit ha hx
    exact absVal_refineUleConst_sound (uintWidth_valid u) ha hInit
      ((hEff x hx).mp rfl)
  | ugtConst r u bound =>
    apply refineUintSlot_sound hEnv
    intro a x hInit ha hx
    exact absVal_refineUgtConst_sound (uintWidth_valid u) ha hInit
      ((hEff x hx).mp rfl)
  | ueqConst r u val =>
    apply refineUintSlot_sound hEnv
    intro a x hInit ha hx
    exact absVal_refineEqConst_sound (uintWidth_valid u) ha hInit
      ((hEff x hx).mp rfl)
  | ultReg l r u =>
    have hEnv1 : mirAbsEnvDenote decls
        (match get? env r with
         | some (.uint u' ar) =>
           match uintTyBeq u u' && ar.isInit with
           | true =>
             refineUintSlot env l u
               (fun al => AbsVal.refineBltReg (uintWidth u) al ar)
           | false => env
         | _ => env) locals := by
      cases hGet : get? env r with
      | none => exact hEnv
      | some s =>
        cases s with
        | uint u' ar =>
          simp only
          cases hC : (uintTyBeq u u' && ar.isInit) with
          | false => exact hEnv
          | true =>
            have hu := uintTy_eq_of_beq (bool_and_true_left hC)
            have hInitR := bool_and_true_right hC
            subst hu
            simp only
            cases env_uint_extract hEnv hGet hInitR with
            | intro scR hR =>
              cases hR with
              | intro dR hR =>
                apply refineUintSlot_sound hEnv
                intro al x hInitL hal hx
                exact absVal_refineBltReg_sound (uintWidth_valid u) hal
                  hR.2.2.2.2.1 hInitL hInitR
                  ((hEff x scR.bits hx hR.2.2.2.2.2).mp rfl)
        | _ => exact hEnv
    simp only
    cases hGetL : get? env l with
    | none => exact hEnv1
    | some sL =>
      cases sL with
      | uint u' al =>
        simp only
        cases hCL : (uintTyBeq u u' && al.isInit) with
        | false => exact hEnv1
        | true =>
          have hu := uintTy_eq_of_beq (bool_and_true_left hCL)
          have hInitL := bool_and_true_right hCL
          subst hu
          cases hLo : al.lbound? with
          | none => exact hEnv1
          | some loL =>
            simp only
            cases env_uint_extract hEnv hGetL hInitL with
            | intro scL hL =>
              cases hL with
              | intro dL hL =>
                apply refineUintSlot_sound hEnv1
                intro ar y hInitR har hy
                have hLoLe : loL ≤ scL.bits :=
                  absVal_lbound?_sound hLo hL.2.2.2.2.1
                have hLt : scL.bits < y :=
                  (hEff scL.bits y hL.2.2.2.2.2 hy).mp rfl
                exact absVal_refineUgtConst_sound (uintWidth_valid u) har hInitR
                  (Nat.lt_of_le_of_lt hLoLe hLt)
      | _ => exact hEnv1
  | ugeReg l r u =>
    have hEnv1 : mirAbsEnvDenote decls
        (match get? env r with
         | some (.uint u' ar) =>
           match uintTyBeq u u' && ar.isInit with
           | true =>
             refineUintSlot env l u
               (fun al => AbsVal.refineBgeReg (uintWidth u) al ar)
           | false => env
         | _ => env) locals := by
      cases hGet : get? env r with
      | none => exact hEnv
      | some s =>
        cases s with
        | uint u' ar =>
          simp only
          cases hC : (uintTyBeq u u' && ar.isInit) with
          | false => exact hEnv
          | true =>
            have hu := uintTy_eq_of_beq (bool_and_true_left hC)
            have hInitR := bool_and_true_right hC
            subst hu
            simp only
            cases env_uint_extract hEnv hGet hInitR with
            | intro scR hR =>
              cases hR with
              | intro dR hR =>
                apply refineUintSlot_sound hEnv
                intro al x hInitL hal hx
                exact absVal_refineBgeReg_sound (uintWidth_valid u) hal
                  hR.2.2.2.2.1 hInitL hInitR
                  ((hEff x scR.bits hx hR.2.2.2.2.2).mp rfl)
        | _ => exact hEnv
    simp only
    cases hGetL : get? env l with
    | none => exact hEnv1
    | some sL =>
      cases sL with
      | uint u' al =>
        simp only
        cases hCL : (uintTyBeq u u' && al.isInit) with
        | false => exact hEnv1
        | true =>
          have hu := uintTy_eq_of_beq (bool_and_true_left hCL)
          have hInitL := bool_and_true_right hCL
          subst hu
          cases hHi : al.ubound? with
          | none => exact hEnv1
          | some hiL =>
            simp only
            cases env_uint_extract hEnv hGetL hInitL with
            | intro scL hL =>
              cases hL with
              | intro dL hL =>
                apply refineUintSlot_sound hEnv1
                intro ar y hInitR har hy
                have hHiLe : scL.bits ≤ hiL :=
                  absVal_ubound?_sound hHi hL.2.2.2.2.1
                have hGe : y ≤ scL.bits :=
                  (hEff scL.bits y hL.2.2.2.2.2 hy).mp rfl
                exact absVal_refineUleConst_sound (uintWidth_valid u) har hInitR
                  (Nat.le_trans hGe hHiLe)
      | _ => exact hEnv1

end Anneal.AiPcc
