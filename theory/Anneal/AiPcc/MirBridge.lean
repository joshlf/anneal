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
`Trusted.Rustc.V2026_06_01.MirSemantics` over unsigned (`UintTy`) and signed
(`IntTy`) integer, boolean, unit, and `(u, bool)` checked-arithmetic locals.

* Section 1 relates `ScalarInt` arithmetic (`scalarModulus`,
  `wrapScalarBits`, `evalScalarBinOp`, `evalUnaryNot`, `boolToScalar`) to the
  `Nat`-level operations used by the `AbsVal` transfer theorems. Signed values
  are tracked by their two's-complement bit pattern at the width of the
  unsigned twin type (`intTwin`): sign-agnostic operators
  (`binOpSignAgnostic`) evaluate identically at `isSigned = true`, and signed
  ordered comparisons coincide with unsigned ones on non-negative operands.
  The biased coordinate `signedBias w x = (x + 2^(w-1)) mod 2^w` of
  `ReducedProduct`'s signed domain is bridged to `signedLt` / `signedLe`
  (`signedLt_iff_signedBias_lt`, `signedLe_iff_signedBias_le`), to
  `signedOverflowAdd` / `signedOverflowSub`
  (`signedOverflowAdd_false_of_biased_bounds`,
  `signedOverflowSub_false_of_biased_bounds`), to signed `div` / `rem`
  (`safeSignedDiv_sound_v2026`), and to `CastKind.intToInt` sign extension
  (`intCastBits`).
* Section 2 defines relational comparison guards (`RelGuard`), abstract
  booleans (`BoolAbs`), abstract local slots (`MirAbsSlot`) and frames
  (`MirAbsEnv`), their concretizations against `List LocalSlot`, the
  lattice order and join, guard-clearing writes (`setMirAbsSlot`), and branch
  refinements (`refineEnvByGuard`, including the signed constant guards
  `.sleConst` / `.sgtConst` / `.seqConst` / `.sneConst`), all consumed by
  `Anneal.AiPcc.MirTransfer`.

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

/-- Unsigned type of the same width as a signed type (`isize ↦ usize`). Signed
values are tracked by their two's-complement bit pattern at this width. -/
def intTwin : IntTy → UintTy
  | .i8 => .u8
  | .i16 => .u16
  | .i32 => .u32
  | .i64 => .u64
  | .i128 => .u128
  | .isize => .usize

/-- Structural equality on `IntTy`. -/
def intTyBeq : IntTy → IntTy → Bool
  | .i8, .i8 => true
  | .i16, .i16 => true
  | .i32, .i32 => true
  | .i64, .i64 => true
  | .i128, .i128 => true
  | .isize, .isize => true
  | _, _ => false

theorem intTyBeq_refl (i : IntTy) : intTyBeq i i = true := by
  cases i <;> rfl

theorem intTy_eq_of_beq {i1 i2 : IntTy} (h : intTyBeq i1 i2 = true) :
    i1 = i2 := by
  cases i1 <;> cases i2 <;> first | rfl | nomatch h

theorem intCastTargetBytes_int (i : IntTy) :
    intCastTargetBytes (.int i) = some (uintBytes (intTwin i)) := by
  cases i <;> rfl

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

/-- `BinOp`s whose `evalScalarBinOp` result does not depend on `isSigned`
(two's-complement wrapping arithmetic, bitwise operations, equality, and
left shifts). -/
def binOpSignAgnostic : BinOp → Bool
  | .add | .sub | .mul | .bitAnd | .bitOr | .bitXor | .eq | .ne
  | .shl | .shlUnchecked => true
  | _ => false

/-- Sign-agnostic operators evaluate identically at `isSigned = true`. -/
theorem evalScalarBinOp_signAgnostic {op : BinOp}
    (h : binOpSignAgnostic op = true) (lhs rhs : ScalarInt) :
    evalScalarBinOp op lhs rhs locals mem true =
      evalScalarBinOp op lhs rhs locals mem false := by
  cases op <;> simp only [binOpSignAgnostic, reduceCtorEq] at h <;>
    simp only [evalScalarBinOp]

/-- Signed relational operators (`lt`, `le`, `gt`, `ge`). -/
def binOpIsOrdCmp : BinOp → Bool
  | .lt | .le | .gt | .ge => true
  | _ => false

theorem isSignedNegative_of_lt_half {x : Nat}
    (hx : x < modPow2 (uintWidth u) / 2) :
    isSignedNegative x (uintBytes u) = false := by
  have hM : x < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hx (Nat.div_le_self _ 2)
  simp only [isSignedNegative, uintBytes_beq_zero]
  rw [wrapScalarBits_of_lt_uint hM, scalarModulus_uintBytes]
  cases h : Nat.ble (modPow2 (uintWidth u) / 2) x with
  | false => rfl
  | true => exact False.elim (Nat.not_le_of_gt hx (Nat.le_of_ble_eq_true h))

theorem signedLt_of_nonneg {x y : Nat}
    (hx : x < modPow2 (uintWidth u) / 2) (hy : y < modPow2 (uintWidth u) / 2) :
    signedLt x y (uintBytes u) = !(Nat.ble y x) := by
  have hxM : x < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hx (Nat.div_le_self _ 2)
  have hyM : y < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hy (Nat.div_le_self _ 2)
  simp only [signedLt]
  rw [wrapScalarBits_of_lt_uint hxM, wrapScalarBits_of_lt_uint hyM,
    isSignedNegative_of_lt_half hx, isSignedNegative_of_lt_half hy]

/-- On non-negative operands (below the signed half-range), signed ordered
comparisons coincide with unsigned ones. -/
theorem evalScalarBinOp_ordCmp_nonneg {op : BinOp}
    (hop : binOpIsOrdCmp op = true) {x y : Nat}
    (hx : x < modPow2 (uintWidth u) / 2) (hy : y < modPow2 (uintWidth u) / 2) :
    evalScalarBinOp op ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem true =
      evalScalarBinOp op ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem false := by
  cases op <;> simp only [binOpIsOrdCmp, reduceCtorEq] at hop <;>
    simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, signedLe,
      signedLt_of_nonneg hx hy, signedLt_of_nonneg hy hx, Bool.not_not]

/-- Signed ordered comparisons always produce a `bool` scalar. -/
theorem evalScalarBinOp_ordCmp_bool {op : BinOp}
    (hop : binOpIsOrdCmp op = true) {x y : Nat} :
    ∃ c, evalScalarBinOp op ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem true =
      .ok (.scalar (boolToScalar c)) locals mem := by
  cases op <;> simp only [binOpIsOrdCmp, reduceCtorEq] at hop <;>
    simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl] <;>
    exact ⟨_, rfl⟩

theorem two_pow_uintBytes (u : UintTy) :
    2 ^ (8 * uintBytes u) = modPow2 (uintWidth u) := by
  cases u <;> rfl

/-- Signed arithmetic `.shr` stays within the bit width. -/
theorem evalScalarBinOp_sint_shr {u2 : UintTy} :
    ∃ bits, bits < modPow2 (uintWidth u) ∧
      evalScalarBinOp .shr ⟨a, uintBytes u⟩ ⟨b, uintBytes u2⟩ locals mem true =
        .ok (.scalar ⟨bits, uintBytes u⟩) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, uintBytes_mul_eight]
  refine ⟨_, ?_, rfl⟩
  rw [← two_pow_uintBytes]
  exact Anneal.Scalars.arithmeticShrBits_lt_two_pow _ _ _

/-- Signed arithmetic `.shrUnchecked` with an in-range shift amount. -/
theorem evalScalarBinOp_sint_shrUnchecked {u2 : UintTy}
    (hb : b < uintWidth u) :
    ∃ bits, bits < modPow2 (uintWidth u) ∧
      evalScalarBinOp .shrUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u2⟩ locals
        mem true = .ok (.scalar ⟨bits, uintBytes u⟩) locals mem := by
  have hB : Nat.ble (uintWidth u) b = false := by
    cases h : Nat.ble (uintWidth u) b with
    | false => rfl
    | true => exact False.elim (Nat.not_le_of_gt hb (Nat.le_of_ble_eq_true h))
  simp only [evalScalarBinOp, uintBytes_beq_zero, uintBytes_mul_eight, hB]
  refine ⟨_, ?_, rfl⟩
  rw [← two_pow_uintBytes]
  exact Anneal.Scalars.arithmeticShrBits_lt_two_pow _ _ _

/-- Signed bitwise `UnOp.not` (`evalUnaryNot` at an `.int` operand type). -/
theorem evalUnaryNot_int {ty : Ty} {i2 : IntTy} (hTy : ty.kind = .int i2)
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

theorem uintBytes_ble_eq_width (u1 u2 : UintTy) :
    Nat.ble (uintBytes u1) (uintBytes u2) =
      Nat.ble (uintWidth u1) (uintWidth u2) := by
  cases u1 <;> cases u2 <;> rfl

/-- Sign extension of a non-negative bit pattern to a wider type is the
identity. -/
theorem signExtendBits_nonneg {u2 : UintTy}
    (hx : a < modPow2 (uintWidth u) / 2)
    (hW : Nat.ble (uintBytes u2) (uintBytes u) = false) :
    signExtendBits a (uintBytes u) (uintBytes u2) = a := by
  have hM : a < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hx (Nat.div_le_self _ 2)
  simp only [signExtendBits, hW]
  rw [wrapScalarBits_of_lt_uint hM, isSignedNegative_of_lt_half hx]

theorem signExtendBits_lt_uint (u1 u2 : UintTy) (x : Nat) :
    signExtendBits x (uintBytes u1) (uintBytes u2) < modPow2 (uintWidth u2) := by
  have hPos1 := modPow2_pos (uintWidth u1)
  have hPos2 := modPow2_pos (uintWidth u2)
  have hcLt : wrapScalarBits x (modPow2 (uintWidth u1)) < modPow2 (uintWidth u1) := by
    rw [Anneal.Scalars.wrapScalarBits_eq_mod_modulus]
    exact nat_mod_lt _ hPos1
  simp only [signExtendBits]
  rw [scalarModulus_uintBytes, scalarModulus_uintBytes]
  cases hB : Nat.ble (uintBytes u2) (uintBytes u1) with
  | true =>
    simp only
    rw [Anneal.Scalars.wrapScalarBits_eq_mod_modulus]
    exact nat_mod_lt _ hPos2
  | false =>
    simp only
    rw [uintBytes_ble_eq_width] at hB
    have hW : uintWidth u1 < uintWidth u2 :=
      Nat.lt_of_not_le (fun h => by rw [Nat.ble_eq_true_of_le h] at hB; nomatch hB)
    have hMono := modPow2_mono (Nat.le_of_lt hW)
    cases isSignedNegative (wrapScalarBits x (modPow2 (uintWidth u1)))
        (uintBytes u1) with
    | false => exact Nat.lt_of_lt_of_le hcLt hMono
    | true =>
      have h := Nat.add_lt_add_left hcLt (modPow2 (uintWidth u2) - modPow2 (uintWidth u1))
      rw [Nat.sub_add_cancel hMono] at h
      exact h

theorem modPow2_uintWidth_half (u : UintTy) :
    modPow2 (uintWidth u) / 2 = modPow2 (uintWidth u - 1) := by
  cases u <;> rfl

theorem modPow2_uintWidth_eq_add_half (u : UintTy) :
    modPow2 (uintWidth u) =
      modPow2 (uintWidth u) / 2 + modPow2 (uintWidth u) / 2 := by
  cases u <;> rfl

theorem scalarPow2_sub_one_eq_half (u : UintTy) :
    scalarPow2 (Nat.sub (uintWidth u) 1) = modPow2 (uintWidth u) / 2 := by
  cases u <;> rfl

theorem half_pos_uint (u : UintTy) : 0 < modPow2 (uintWidth u) / 2 := by
  rw [modPow2_uintWidth_half]
  exact modPow2_pos _

theorem half_le_sub_one_uint (u : UintTy) :
    modPow2 (uintWidth u) / 2 ≤ modPow2 (uintWidth u) - 1 := by
  have hAdd := modPow2_uintWidth_eq_add_half u
  have hPos := half_pos_uint u
  have hLe : modPow2 (uintWidth u) / 2 + 1 ≤
      modPow2 (uintWidth u) / 2 + modPow2 (uintWidth u) / 2 :=
    Nat.add_le_add_left hPos _
  rw [← hAdd] at hLe
  exact Nat.le_sub_of_add_le hLe

theorem isSignedNegative_of_ge_half {x : Nat}
    (hx : modPow2 (uintWidth u) / 2 ≤ x) (hxM : x < modPow2 (uintWidth u)) :
    isSignedNegative x (uintBytes u) = true := by
  simp only [isSignedNegative, uintBytes_beq_zero]
  rw [wrapScalarBits_of_lt_uint hxM, scalarModulus_uintBytes]
  exact Nat.ble_eq_true_of_le hx

theorem signedLt_of_neg {x y : Nat}
    (hx : modPow2 (uintWidth u) / 2 ≤ x) (hxM : x < modPow2 (uintWidth u))
    (hy : modPow2 (uintWidth u) / 2 ≤ y) (hyM : y < modPow2 (uintWidth u)) :
    signedLt x y (uintBytes u) = !(Nat.ble y x) := by
  simp only [signedLt]
  rw [wrapScalarBits_of_lt_uint hxM, wrapScalarBits_of_lt_uint hyM,
    isSignedNegative_of_ge_half hx hxM, isSignedNegative_of_ge_half hy hyM]

/-- On two negative operands (`≥ 2^(w-1)`), signed ordered comparisons also
coincide with unsigned ones. -/
theorem evalScalarBinOp_ordCmp_neg {op : BinOp}
    (hop : binOpIsOrdCmp op = true) {x y : Nat}
    (hx : modPow2 (uintWidth u) / 2 ≤ x) (hxM : x < modPow2 (uintWidth u))
    (hy : modPow2 (uintWidth u) / 2 ≤ y) (hyM : y < modPow2 (uintWidth u)) :
    evalScalarBinOp op ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem true =
      evalScalarBinOp op ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem false := by
  cases op <;> simp only [binOpIsOrdCmp, reduceCtorEq] at hop <;>
    simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, signedLe,
      signedLt_of_neg hx hxM hy hyM, signedLt_of_neg hy hyM hx hxM,
      Bool.not_not]

/-- Signed ordered comparisons with a negative LHS and non-negative RHS. -/
theorem evalScalarBinOp_ordCmp_neg_nonneg {op : BinOp}
    (hop : binOpIsOrdCmp op = true) {x y : Nat}
    (hx : modPow2 (uintWidth u) / 2 ≤ x) (hxM : x < modPow2 (uintWidth u))
    (hy : y < modPow2 (uintWidth u) / 2) :
    evalScalarBinOp op ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem true =
      .ok (.scalar (boolToScalar
        (match op with | .lt | .le => true | _ => false))) locals mem := by
  have hyM : y < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hy (Nat.div_le_self _ 2)
  have hxy : signedLt x y (uintBytes u) = true := by
    simp only [signedLt]
    rw [wrapScalarBits_of_lt_uint hxM, wrapScalarBits_of_lt_uint hyM,
      isSignedNegative_of_ge_half hx hxM, isSignedNegative_of_lt_half hy]
  have hyx : signedLt y x (uintBytes u) = false := by
    simp only [signedLt]
    rw [wrapScalarBits_of_lt_uint hxM, wrapScalarBits_of_lt_uint hyM,
      isSignedNegative_of_ge_half hx hxM, isSignedNegative_of_lt_half hy]
  cases op <;> simp only [binOpIsOrdCmp, reduceCtorEq] at hop <;>
    simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, signedLe,
      hxy, hyx] <;> rfl

/-- Signed ordered comparisons with a non-negative LHS and negative RHS. -/
theorem evalScalarBinOp_ordCmp_nonneg_neg {op : BinOp}
    (hop : binOpIsOrdCmp op = true) {x y : Nat}
    (hx : x < modPow2 (uintWidth u) / 2)
    (hy : modPow2 (uintWidth u) / 2 ≤ y) (hyM : y < modPow2 (uintWidth u)) :
    evalScalarBinOp op ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem true =
      .ok (.scalar (boolToScalar
        (match op with | .lt | .le => false | _ => true))) locals mem := by
  have hxM : x < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hx (Nat.div_le_self _ 2)
  have hxy : signedLt x y (uintBytes u) = false := by
    simp only [signedLt]
    rw [wrapScalarBits_of_lt_uint hxM, wrapScalarBits_of_lt_uint hyM,
      isSignedNegative_of_lt_half hx, isSignedNegative_of_ge_half hy hyM]
  have hyx : signedLt y x (uintBytes u) = true := by
    simp only [signedLt]
    rw [wrapScalarBits_of_lt_uint hxM, wrapScalarBits_of_lt_uint hyM,
      isSignedNegative_of_lt_half hx, isSignedNegative_of_ge_half hy hyM]
  cases op <;> simp only [binOpIsOrdCmp, reduceCtorEq] at hop <;>
    simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, signedLe,
      hxy, hyx] <;> rfl

/-- `x <_signed 0` iff `x > 2^(w-1) - 1` (sign bit is set). -/
theorem signedLt_zero_eq {x : Nat} (hx : x < modPow2 (uintWidth u)) :
    signedLt x 0 (uintBytes u) =
      !(Nat.ble x (modPow2 (uintWidth u) / 2 - 1)) := by
  have h0Lt : 0 < modPow2 (uintWidth u) / 2 := half_pos_uint u
  have h0M : 0 < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le h0Lt (Nat.div_le_self _ 2)
  simp only [signedLt]
  rw [wrapScalarBits_of_lt_uint hx, wrapScalarBits_of_lt_uint h0M,
    isSignedNegative_of_lt_half h0Lt]
  cases Nat.lt_or_ge x (modPow2 (uintWidth u) / 2) with
  | inl hLt =>
    have hLe : x ≤ modPow2 (uintWidth u) / 2 - 1 :=
      Nat.le_sub_one_of_lt hLt
    rw [isSignedNegative_of_lt_half hLt, Nat.ble_eq_true_of_le hLe,
      Nat.ble_eq_true_of_le (Nat.zero_le x)]
  | inr hGe =>
    have hGt : modPow2 (uintWidth u) / 2 - 1 < x :=
      Nat.lt_of_lt_of_le (Nat.sub_lt h0Lt Nat.zero_lt_one) hGe
    have hBleF : Nat.ble x (modPow2 (uintWidth u) / 2 - 1) = false := by
      cases hb : Nat.ble x (modPow2 (uintWidth u) / 2 - 1) with
      | false => rfl
      | true => exact False.elim (Nat.not_le_of_gt hGt (Nat.le_of_ble_eq_true hb))
    rw [isSignedNegative_of_ge_half hGe hx, hBleF]
    rfl

/-- `-1 <_signed x` iff `x ≤ 2^(w-1) - 1` (`x` is non-negative). -/
theorem signedLt_minusOne_eq {x : Nat} (hx : x < modPow2 (uintWidth u)) :
    signedLt (modPow2 (uintWidth u) - 1) x (uintBytes u) =
      Nat.ble x (modPow2 (uintWidth u) / 2 - 1) := by
  have hPos := half_pos_uint u
  have hM1Lt : modPow2 (uintWidth u) - 1 < modPow2 (uintWidth u) :=
    Nat.sub_lt (modPow2_pos _) Nat.zero_lt_one
  have hM1Neg : isSignedNegative (modPow2 (uintWidth u) - 1) (uintBytes u) = true :=
    isSignedNegative_of_ge_half (half_le_sub_one_uint u) hM1Lt
  simp only [signedLt]
  rw [wrapScalarBits_of_lt_uint hM1Lt, wrapScalarBits_of_lt_uint hx, hM1Neg]
  cases Nat.lt_or_ge x (modPow2 (uintWidth u) / 2) with
  | inl hLt =>
    have hLe : x ≤ modPow2 (uintWidth u) / 2 - 1 :=
      Nat.le_sub_one_of_lt hLt
    rw [isSignedNegative_of_lt_half hLt, Nat.ble_eq_true_of_le hLe]
  | inr hGe =>
    have hGt : modPow2 (uintWidth u) / 2 - 1 < x :=
      Nat.lt_of_lt_of_le (Nat.sub_lt hPos Nat.zero_lt_one) hGe
    have hBleF : Nat.ble x (modPow2 (uintWidth u) / 2 - 1) = false := by
      cases hb : Nat.ble x (modPow2 (uintWidth u) / 2 - 1) with
      | false => rfl
      | true => exact False.elim (Nat.not_le_of_gt hGt (Nat.le_of_ble_eq_true hb))
    have hXLe : x ≤ modPow2 (uintWidth u) - 1 := Nat.le_sub_one_of_lt hx
    rw [isSignedNegative_of_ge_half hGe hx, Nat.ble_eq_true_of_le hXLe, hBleF]
    rfl

/-- Arithmetic right shift of a non-negative bit pattern coincides with logical
right shift. -/
theorem evalScalarBinOp_sint_shr_nonneg {u2 : UintTy}
    (ha : a < modPow2 (uintWidth u) / 2) :
    evalScalarBinOp .shr ⟨a, uintBytes u⟩ ⟨b, uintBytes u2⟩ locals mem true =
      evalScalarBinOp .shr ⟨a, uintBytes u⟩ ⟨b, uintBytes u2⟩ locals mem false := by
  have haM : a < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le ha (Nat.div_le_self _ 2)
  simp only [evalScalarBinOp, uintBytes_beq_zero, uintBytes_mul_eight,
    arithmeticShrBits]
  rw [wrapScalarBits_of_lt_uint haM, isSignedNegative_of_lt_half ha]

/-- Unchecked arithmetic right shift of a non-negative bit pattern coincides
with unchecked logical right shift. -/
theorem evalScalarBinOp_sint_shrUnchecked_nonneg {u2 : UintTy}
    (ha : a < modPow2 (uintWidth u) / 2) :
    evalScalarBinOp .shrUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u2⟩ locals mem true =
      evalScalarBinOp .shrUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u2⟩ locals mem false := by
  have haM : a < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le ha (Nat.div_le_self _ 2)
  simp only [evalScalarBinOp, uintBytes_beq_zero, uintBytes_mul_eight,
    arithmeticShrBits]
  cases Nat.ble (uintWidth u) b with
  | true => rfl
  | false =>
    rw [wrapScalarBits_of_lt_uint haM, isSignedNegative_of_lt_half ha]

theorem signedOverflowAdd_false_of_nonneg_lt
    (hx : a < modPow2 (uintWidth u) / 2) (hy : b < modPow2 (uintWidth u) / 2)
    (hSum : a + b < modPow2 (uintWidth u) / 2) :
    signedOverflowAdd a b (uintBytes u) = false := by
  have hSumM : a + b < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hSum (Nat.div_le_self _ 2)
  have hAddEq : Nat.add a b = a + b := rfl
  simp only [signedOverflowAdd]
  rw [hAddEq, isSignedNegative_of_lt_half hx, isSignedNegative_of_lt_half hy,
    wrapScalarBits_of_lt_uint hSumM, isSignedNegative_of_lt_half hSum]

theorem signedOverflowAdd_false_of_opp_sign
    (h : (a < modPow2 (uintWidth u) / 2 ∧
          modPow2 (uintWidth u) / 2 ≤ b ∧ b < modPow2 (uintWidth u)) ∨
         (modPow2 (uintWidth u) / 2 ≤ a ∧ a < modPow2 (uintWidth u) ∧
          b < modPow2 (uintWidth u) / 2)) :
    signedOverflowAdd a b (uintBytes u) = false := by
  simp only [signedOverflowAdd]
  cases h with
  | inl h1 =>
    rw [isSignedNegative_of_lt_half h1.1,
      isSignedNegative_of_ge_half h1.2.1 h1.2.2]
  | inr h2 =>
    rw [isSignedNegative_of_ge_half h2.1 h2.2.1,
      isSignedNegative_of_lt_half h2.2.2]

theorem signedOverflowAdd_false_of_zero_left
    (hy : b < modPow2 (uintWidth u)) :
    signedOverflowAdd 0 b (uintBytes u) = false := by
  simp only [signedOverflowAdd]
  rw [isSignedNegative_of_lt_half (half_pos_uint u)]
  have hAdd : Nat.add 0 b = b := Nat.zero_add b
  rw [hAdd, wrapScalarBits_of_lt_uint hy]
  cases isSignedNegative b (uintBytes u) <;> rfl

theorem signedOverflowAdd_false_of_zero_right
    (hx : a < modPow2 (uintWidth u)) :
    signedOverflowAdd a 0 (uintBytes u) = false := by
  simp only [signedOverflowAdd]
  rw [isSignedNegative_of_lt_half (half_pos_uint u)]
  have hAdd : Nat.add a 0 = a := Nat.add_zero a
  rw [hAdd, wrapScalarBits_of_lt_uint hx]
  cases isSignedNegative a (uintBytes u) <;> rfl

theorem signedOverflowSub_false_of_same_sign
    (h : (a < modPow2 (uintWidth u) / 2 ∧ b < modPow2 (uintWidth u) / 2) ∨
         (modPow2 (uintWidth u) / 2 ≤ a ∧ a < modPow2 (uintWidth u) ∧
          modPow2 (uintWidth u) / 2 ≤ b ∧ b < modPow2 (uintWidth u))) :
    signedOverflowSub a b (uintBytes u) = false := by
  simp only [signedOverflowSub]
  cases h with
  | inl h1 =>
    have haM : a < modPow2 (uintWidth u) :=
      Nat.lt_of_lt_of_le h1.1 (Nat.div_le_self _ 2)
    have hbM : b < modPow2 (uintWidth u) :=
      Nat.lt_of_lt_of_le h1.2 (Nat.div_le_self _ 2)
    rw [wrapScalarBits_of_lt_uint haM, wrapScalarBits_of_lt_uint hbM,
      isSignedNegative_of_lt_half h1.1, isSignedNegative_of_lt_half h1.2]
  | inr h2 =>
    rw [wrapScalarBits_of_lt_uint h2.2.1, wrapScalarBits_of_lt_uint h2.2.2.2,
      isSignedNegative_of_ge_half h2.1 h2.2.1,
      isSignedNegative_of_ge_half h2.2.2.1 h2.2.2.2]

theorem signedOverflowSub_false_of_zero_right
    (hx : a < modPow2 (uintWidth u)) :
    signedOverflowSub a 0 (uintBytes u) = false := by
  have h0M : 0 < modPow2 (uintWidth u) := modPow2_pos _
  simp only [signedOverflowSub]
  rw [wrapScalarBits_of_lt_uint hx, wrapScalarBits_of_lt_uint h0M,
    Nat.ble_eq_true_of_le (Nat.zero_le a)]
  have hSub : Nat.sub a 0 = a := Nat.sub_zero a
  rw [hSub, wrapScalarBits_of_lt_uint hx,
    isSignedNegative_of_lt_half (half_pos_uint u)]
  cases isSignedNegative a (uintBytes u) <;> rfl

theorem signedOverflowMul_false_of_zero_left
    (hy : b < modPow2 (uintWidth u)) :
    signedOverflowMul 0 b (uintBytes u) = false := by
  have h0M : 0 < modPow2 (uintWidth u) := modPow2_pos _
  have h0 : ∀ n, Nat.mul 0 n = 0 := Nat.zero_mul
  simp only [signedOverflowMul, uintBytes_beq_zero]
  rw [wrapScalarBits_of_lt_uint h0M, wrapScalarBits_of_lt_uint hy,
    isSignedNegative_of_lt_half (half_pos_uint u)]
  cases isSignedNegative b (uintBytes u) <;> dsimp only <;> rw [h0] <;> rfl

theorem signedOverflowMul_false_of_zero_right
    (hx : a < modPow2 (uintWidth u)) :
    signedOverflowMul a 0 (uintBytes u) = false := by
  have h0M : 0 < modPow2 (uintWidth u) := modPow2_pos _
  have h0 : ∀ n, Nat.mul n 0 = 0 := Nat.mul_zero
  simp only [signedOverflowMul, uintBytes_beq_zero]
  rw [wrapScalarBits_of_lt_uint hx, wrapScalarBits_of_lt_uint h0M,
    isSignedNegative_of_lt_half (half_pos_uint u)]
  cases isSignedNegative a (uintBytes u) <;> dsimp only <;> rw [h0] <;> rfl

theorem signedOverflowMul_false_of_nonneg_lt
    (hx : a < modPow2 (uintWidth u) / 2) (hy : b < modPow2 (uintWidth u) / 2)
    (hProd : a * b < modPow2 (uintWidth u) / 2) :
    signedOverflowMul a b (uintBytes u) = false := by
  have hxM : a < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hx (Nat.div_le_self _ 2)
  have hyM : b < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hy (Nat.div_le_self _ 2)
  simp only [signedOverflowMul, uintBytes_beq_zero]
  rw [wrapScalarBits_of_lt_uint hxM, wrapScalarBits_of_lt_uint hyM,
    isSignedNegative_of_lt_half hx, isSignedNegative_of_lt_half hy,
    scalarModulus_uintBytes]
  cases Nat.beq (Nat.mul a b) 0 with
  | true => rfl
  | false =>
    cases hb : Nat.ble (Nat.div (modPow2 (uintWidth u)) 2) (Nat.mul a b) with
    | false => rfl
    | true =>
      exact False.elim (Nat.not_le_of_gt hProd (Nat.le_of_ble_eq_true hb))

theorem evalScalarBinOp_sint_addUnchecked
    (hNoOv : signedOverflowAdd a b (uintBytes u) = false) :
    evalScalarBinOp .addUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem true =
      .ok (.scalar ⟨wrapVal (uintWidth u) (a + b), uintBytes u⟩) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hNoOv]
  rw [wrapScalarBits_eq_wrapVal]
  rfl

theorem evalScalarBinOp_sint_subUnchecked
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u))
    (hNoOv : signedOverflowSub a b (uintBytes u) = false) :
    evalScalarBinOp .subUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem true =
      .ok (.scalar ⟨wrapVal (uintWidth u) (a + modPow2 (uintWidth u) - b),
        uintBytes u⟩) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hNoOv]
  rw [wrapScalarBits_of_lt_uint ha, wrapScalarBits_of_lt_uint hb]
  cases hLe : Nat.ble b a with
  | true =>
    simp only
    have hSub : Nat.sub a b = a - b := rfl
    rw [hSub, wrapScalarBits_eq_wrapVal,
      wrapVal_sub_of_le (Nat.le_of_ble_eq_true hLe),
      Nat.add_comm (modPow2 (uintWidth u)) a]
    exact ha
  | false =>
    simp only
    rw [wrapScalarBits_eq_wrapVal, scalarModulus_uintBytes]
    have hComm : Nat.add (modPow2 (uintWidth u)) a = a + modPow2 (uintWidth u) :=
      Nat.add_comm _ _
    rw [hComm]
    rfl

theorem evalScalarBinOp_sint_mulUnchecked
    (hNoOv : signedOverflowMul a b (uintBytes u) = false) :
    evalScalarBinOp .mulUnchecked ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem true =
      .ok (.scalar ⟨wrapVal (uintWidth u) (a * b), uintBytes u⟩) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hNoOv]
  rw [wrapScalarBits_eq_wrapVal]
  rfl

theorem evalScalarBinOp_sint_addWithOverflow :
    evalScalarBinOp .addWithOverflow ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem true =
      .ok (.aggregate 0 [.scalar ⟨wrapVal (uintWidth u) (a + b), uintBytes u⟩,
        .scalar (boolToScalar (signedOverflowAdd a b (uintBytes u)))])
        locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  rw [wrapScalarBits_eq_wrapVal]
  cases signedOverflowAdd a b (uintBytes u) <;> rfl

theorem evalScalarBinOp_sint_subWithOverflow
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u)) :
    evalScalarBinOp .subWithOverflow ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem true =
      .ok (.aggregate 0
        [.scalar ⟨wrapVal (uintWidth u) (a + modPow2 (uintWidth u) - b), uintBytes u⟩,
         .scalar (boolToScalar (signedOverflowSub a b (uintBytes u)))])
        locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  rw [wrapScalarBits_of_lt_uint ha, wrapScalarBits_of_lt_uint hb]
  cases hLe : Nat.ble b a with
  | true =>
    simp only
    have hSub : Nat.sub a b = a - b := rfl
    rw [hSub, wrapScalarBits_eq_wrapVal,
      wrapVal_sub_of_le (Nat.le_of_ble_eq_true hLe),
      Nat.add_comm (modPow2 (uintWidth u)) a]
    · cases signedOverflowSub a b (uintBytes u) <;> rfl
    · exact ha
  | false =>
    simp only
    rw [wrapScalarBits_eq_wrapVal, scalarModulus_uintBytes]
    have hComm : Nat.add (modPow2 (uintWidth u)) a = a + modPow2 (uintWidth u) :=
      Nat.add_comm _ _
    rw [hComm]
    cases signedOverflowSub a b (uintBytes u) <;> rfl

theorem evalScalarBinOp_sint_mulWithOverflow :
    evalScalarBinOp .mulWithOverflow ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem true =
      .ok (.aggregate 0 [.scalar ⟨wrapVal (uintWidth u) (a * b), uintBytes u⟩,
        .scalar (boolToScalar (signedOverflowMul a b (uintBytes u)))])
        locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  rw [wrapScalarBits_eq_wrapVal]
  cases signedOverflowMul a b (uintBytes u) <;> rfl

theorem evalScalarBinOp_sint_div_nonneg
    (ha : a < modPow2 (uintWidth u) / 2) (hb : b < modPow2 (uintWidth u) / 2)
    (hbNe : b ≠ 0) :
    evalScalarBinOp .div ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem true =
      .ok (.scalar ⟨a / b, uintBytes u⟩) locals mem := by
  have haM : a < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le ha (Nat.div_le_self _ 2)
  have hbM : b < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hb (Nat.div_le_self _ 2)
  have hb0 : Nat.beq b 0 = false := by
    cases h : Nat.beq b 0 with
    | false => rfl
    | true => exact False.elim (hbNe (Nat.eq_of_beq_eq_true h))
  have hNeMin : Nat.beq a (modPow2 (uintWidth u) / 2) = false := by
    cases h : Nat.beq a (modPow2 (uintWidth u) / 2) with
    | false => rfl
    | true =>
      have hEq := Nat.eq_of_beq_eq_true h
      rw [hEq] at ha
      exact False.elim (Nat.lt_irrefl _ ha)
  have hDivLt : Nat.div a b < modPow2 (uintWidth u) :=
    Nat.lt_of_le_of_lt (Nat.div_le_self a b) haM
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hb0,
    evalSignedDiv, uintBytes_mul_eight, scalarPow2_sub_one_eq_half]
  rw [wrapScalarBits_of_lt_uint haM, wrapScalarBits_of_lt_uint hbM, hNeMin]
  simp only [Bool.false_and, isSignedNegative_of_lt_half ha,
    isSignedNegative_of_lt_half hb]
  cases hQ : Nat.beq (Nat.div a b) 0 with
  | true =>
    have hEq : a / b = 0 := Nat.eq_of_beq_eq_true hQ
    rw [hEq]
  | false =>
    simp only
    rw [wrapScalarBits_of_lt_uint hDivLt]
    rfl

theorem evalScalarBinOp_sint_rem_nonneg
    (ha : a < modPow2 (uintWidth u) / 2) (hb : b < modPow2 (uintWidth u) / 2)
    (hbNe : b ≠ 0) :
    evalScalarBinOp .rem ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem true =
      .ok (.scalar ⟨a % b, uintBytes u⟩) locals mem := by
  have haM : a < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le ha (Nat.div_le_self _ 2)
  have hbM : b < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hb (Nat.div_le_self _ 2)
  have hb0 : Nat.beq b 0 = false := by
    cases h : Nat.beq b 0 with
    | false => rfl
    | true => exact False.elim (hbNe (Nat.eq_of_beq_eq_true h))
  have hNeMin : Nat.beq a (modPow2 (uintWidth u) / 2) = false := by
    cases h : Nat.beq a (modPow2 (uintWidth u) / 2) with
    | false => rfl
    | true =>
      have hEq := Nat.eq_of_beq_eq_true h
      rw [hEq] at ha
      exact False.elim (Nat.lt_irrefl _ ha)
  have hRemLt : Nat.mod a b < modPow2 (uintWidth u) :=
    Nat.lt_of_le_of_lt (Nat.mod_le a b) haM
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hb0,
    evalSignedRem, uintBytes_mul_eight, scalarPow2_sub_one_eq_half]
  rw [wrapScalarBits_of_lt_uint haM, wrapScalarBits_of_lt_uint hbM, hNeMin]
  simp only [Bool.false_and, isSignedNegative_of_lt_half ha,
    isSignedNegative_of_lt_half hb]
  cases hR : Nat.beq (Nat.mod a b) 0 with
  | true =>
    have hEq : a % b = 0 := Nat.eq_of_beq_eq_true hR
    rw [hEq]
  | false =>
    simp only
    rw [wrapScalarBits_of_lt_uint hRemLt]
    rfl

theorem evalScalarBinOp_sint_div_safe
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u))
    (hbNe : b ≠ 0)
    (hNoOv : ¬ (a = modPow2 (uintWidth u) / 2 ∧ b = modPow2 (uintWidth u) - 1)) :
    ∃ bits, bits < modPow2 (uintWidth u) ∧
      evalScalarBinOp .div ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem true =
        .ok (.scalar ⟨bits, uintBytes u⟩) locals mem := by
  have hb0 : Nat.beq b 0 = false := by
    cases h : Nat.beq b 0 with
    | false => rfl
    | true => exact False.elim (hbNe (Nat.eq_of_beq_eq_true h))
  have hOvF : Bool.and (Nat.beq a (modPow2 (uintWidth u) / 2))
      (Nat.beq b (Nat.sub (modPow2 (uintWidth u)) 1)) = false := by
    cases h1 : Nat.beq a (modPow2 (uintWidth u) / 2) with
    | false => rfl
    | true =>
      cases h2 : Nat.beq b (Nat.sub (modPow2 (uintWidth u)) 1) with
      | false => rfl
      | true =>
        exact False.elim (hNoOv ⟨Nat.eq_of_beq_eq_true h1,
          Nat.eq_of_beq_eq_true h2⟩)
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hb0,
    evalSignedDiv, uintBytes_mul_eight, scalarPow2_sub_one_eq_half]
  rw [wrapScalarBits_of_lt_uint ha, wrapScalarBits_of_lt_uint hb,
    scalarModulus_uintBytes, hOvF]
  refine ⟨_, ?_, rfl⟩
  cases Nat.beq _ 0 with
  | true => exact modPow2_pos _
  | false =>
    cases isSignedNegative a (uintBytes u) <;>
    cases isSignedNegative b (uintBytes u) <;>
    · dsimp only
      rw [Anneal.Scalars.wrapScalarBits_eq_mod_modulus]
      exact nat_mod_lt _ (modPow2_pos _)

theorem evalScalarBinOp_sint_rem_safe
    (ha : a < modPow2 (uintWidth u)) (hb : b < modPow2 (uintWidth u))
    (hbNe : b ≠ 0)
    (hNoOv : ¬ (a = modPow2 (uintWidth u) / 2 ∧ b = modPow2 (uintWidth u) - 1)) :
    ∃ bits, bits < modPow2 (uintWidth u) ∧
      evalScalarBinOp .rem ⟨a, uintBytes u⟩ ⟨b, uintBytes u⟩ locals mem true =
        .ok (.scalar ⟨bits, uintBytes u⟩) locals mem := by
  have hb0 : Nat.beq b 0 = false := by
    cases h : Nat.beq b 0 with
    | false => rfl
    | true => exact False.elim (hbNe (Nat.eq_of_beq_eq_true h))
  have hOvF : Bool.and (Nat.beq a (modPow2 (uintWidth u) / 2))
      (Nat.beq b (Nat.sub (modPow2 (uintWidth u)) 1)) = false := by
    cases h1 : Nat.beq a (modPow2 (uintWidth u) / 2) with
    | false => rfl
    | true =>
      cases h2 : Nat.beq b (Nat.sub (modPow2 (uintWidth u)) 1) with
      | false => rfl
      | true =>
        exact False.elim (hNoOv ⟨Nat.eq_of_beq_eq_true h1,
          Nat.eq_of_beq_eq_true h2⟩)
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hb0,
    evalSignedRem, uintBytes_mul_eight, scalarPow2_sub_one_eq_half]
  rw [wrapScalarBits_of_lt_uint ha, wrapScalarBits_of_lt_uint hb,
    scalarModulus_uintBytes, hOvF]
  refine ⟨_, ?_, rfl⟩
  cases Nat.beq _ 0 with
  | true => exact modPow2_pos _
  | false =>
    cases isSignedNegative a (uintBytes u) <;>
    · dsimp only
      rw [Anneal.Scalars.wrapScalarBits_eq_mod_modulus]
      exact nat_mod_lt _ (modPow2_pos _)

end ScalarOps

/-! ### Biased signed coordinates (`signedBias`) against `MirSemantics.Scalars`

`ReducedProduct`'s signed domain works in the biased coordinate
`signedBias w x = (x + 2^(w-1)) mod 2^w`, an order isomorphism from signed
two's-complement order onto unsigned order. The lemmas below relate it to
`signedLt` / `signedLe` / `signedOverflowAdd` / `signedOverflowSub` /
`evalSignedDiv` / `evalSignedRem` of `Trusted.Rustc.V2026_06_01.MirSemantics`. -/

section SignedBias

variable {u : UintTy}

/-- `halfModPow2 (uintWidth u)` is the `MirSemantics` sign threshold
`modPow2 (uintWidth u) / 2`. -/
theorem halfModPow2_uintWidth_eq_half (u : UintTy) :
    halfModPow2 (uintWidth u) = modPow2 (uintWidth u) / 2 := by
  cases u <;> rfl

theorem nat_sub_lt_of_lt_add {x h : Nat} (hG : h ≤ x) (hLt : x < h + h) :
    x - h < h :=
  nat_lt_of_add_lt_add_right (c := h) (by rw [Nat.sub_add_cancel hG]; exact hLt)

theorem lt_half_add_half_uint {x : Nat} (hx : x < modPow2 (uintWidth u)) :
    x < modPow2 (uintWidth u) / 2 + modPow2 (uintWidth u) / 2 := by
  rw [← modPow2_uintWidth_eq_add_half]
  exact hx

/-- Biased coordinate of a non-negative bit pattern. -/
theorem signedBias_uint_of_lt_half {x : Nat}
    (hx : x < modPow2 (uintWidth u) / 2) :
    signedBias (uintWidth u) x = x + modPow2 (uintWidth u) / 2 := by
  have h := signedBias_of_lt_half (w := uintWidth u) (x := x) (uintWidth_valid u)
    (by rw [halfModPow2_uintWidth_eq_half]; exact hx)
  rw [halfModPow2_uintWidth_eq_half] at h
  exact h

/-- Biased coordinate of a negative bit pattern. -/
theorem signedBias_uint_of_ge_half {x : Nat}
    (hx : modPow2 (uintWidth u) / 2 ≤ x) (hxM : x < modPow2 (uintWidth u)) :
    signedBias (uintWidth u) x = x - modPow2 (uintWidth u) / 2 := by
  have h := signedBias_of_ge_half (w := uintWidth u) (x := x) (uintWidth_valid u)
    (by rw [halfModPow2_uintWidth_eq_half]; exact hx) hxM
  rw [halfModPow2_uintWidth_eq_half] at h
  exact h

/-- `signedBias` is an involution on `[0, 2^w)`. -/
theorem signedBias_signedBias {w x : Nat} (hw : validWidth w = true)
    (hx : x < modPow2 w) : signedBias w (signedBias w x) = x := by
  have h := signedBias_inv hw hx
  rw [Nat.add_comm] at h
  exact h

/-- `signedBias` is injective on `[0, 2^w)`. -/
theorem signedBias_inj {w x y : Nat} (hw : validWidth w = true)
    (hx : x < modPow2 w) (hy : y < modPow2 w)
    (h : signedBias w x = signedBias w y) : x = y := by
  have h1 := signedBias_signedBias hw hx
  rw [h, signedBias_signedBias hw hy] at h1
  exact h1.symm

/-- Equality of bit patterns is equality of biased coordinates. -/
theorem signedBias_beq {w x y : Nat} (hw : validWidth w = true)
    (hx : x < modPow2 w) (hy : y < modPow2 w) :
    Nat.beq (signedBias w x) (signedBias w y) = Nat.beq x y := by
  cases hB : Nat.beq x y with
  | true => rw [Nat.eq_of_beq_eq_true hB, nat_beq_refl]
  | false =>
    cases hB2 : Nat.beq (signedBias w x) (signedBias w y) with
    | false => rfl
    | true =>
      rw [signedBias_inj hw hx hy (Nat.eq_of_beq_eq_true hB2), nat_beq_refl] at hB
      nomatch hB

theorem signedLt_of_neg_nonneg {x y : Nat}
    (hx : modPow2 (uintWidth u) / 2 ≤ x) (hxM : x < modPow2 (uintWidth u))
    (hy : y < modPow2 (uintWidth u) / 2) :
    signedLt x y (uintBytes u) = true := by
  have hyM : y < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hy (Nat.div_le_self _ 2)
  simp only [signedLt]
  rw [wrapScalarBits_of_lt_uint hxM, wrapScalarBits_of_lt_uint hyM,
    isSignedNegative_of_ge_half hx hxM, isSignedNegative_of_lt_half hy]

theorem signedLt_of_nonneg_neg {x y : Nat}
    (hx : x < modPow2 (uintWidth u) / 2)
    (hy : modPow2 (uintWidth u) / 2 ≤ y) (hyM : y < modPow2 (uintWidth u)) :
    signedLt x y (uintBytes u) = false := by
  have hxM : x < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hx (Nat.div_le_self _ 2)
  simp only [signedLt]
  rw [wrapScalarBits_of_lt_uint hxM, wrapScalarBits_of_lt_uint hyM,
    isSignedNegative_of_lt_half hx, isSignedNegative_of_ge_half hy hyM]

theorem not_ble_true_iff_lt {a b : Nat} : (!(Nat.ble b a)) = true ↔ a < b := by
  rw [← nat_blt_eq_not_ble]
  exact ⟨lt_of_blt_true, blt_true_of_lt⟩

/-- `MirSemantics.Scalars.signedLt` is unsigned `<` on biased coordinates. -/
theorem signedLt_iff_signedBias_lt {x y : Nat}
    (hx : x < modPow2 (uintWidth u)) (hy : y < modPow2 (uintWidth u)) :
    signedLt x y (uintBytes u) = true ↔
      signedBias (uintWidth u) x < signedBias (uintWidth u) y := by
  cases Nat.lt_or_ge x (modPow2 (uintWidth u) / 2) with
  | inl hxL =>
    cases Nat.lt_or_ge y (modPow2 (uintWidth u) / 2) with
    | inl hyL =>
      rw [signedLt_of_nonneg hxL hyL, signedBias_uint_of_lt_half hxL,
        signedBias_uint_of_lt_half hyL]
      exact Iff.trans not_ble_true_iff_lt
        ⟨fun h => Nat.add_lt_add_right h _, nat_lt_of_add_lt_add_right⟩
    | inr hyG =>
      rw [signedLt_of_nonneg_neg hxL hyG hy, signedBias_uint_of_lt_half hxL,
        signedBias_uint_of_ge_half hyG hy]
      refine ⟨(fun h => nomatch h), fun h => ?_⟩
      have hyLt := nat_sub_lt_of_lt_add hyG (lt_half_add_half_uint hy)
      exact False.elim (Nat.lt_irrefl _
        (Nat.lt_trans (Nat.lt_of_lt_of_le hyLt (Nat.le_add_left _ x)) h))
  | inr hxG =>
    cases Nat.lt_or_ge y (modPow2 (uintWidth u) / 2) with
    | inl hyL =>
      rw [signedLt_of_neg_nonneg hxG hx hyL, signedBias_uint_of_ge_half hxG hx,
        signedBias_uint_of_lt_half hyL]
      have hxLt := nat_sub_lt_of_lt_add hxG (lt_half_add_half_uint hx)
      exact ⟨fun _ => Nat.lt_of_lt_of_le hxLt (Nat.le_add_left _ y), fun _ => rfl⟩
    | inr hyG =>
      rw [signedLt_of_neg hxG hx hyG hy, signedBias_uint_of_ge_half hxG hx,
        signedBias_uint_of_ge_half hyG hy]
      exact Iff.trans not_ble_true_iff_lt
        ⟨fun h => Nat.sub_lt_sub_right hxG h, fun h => by
          have h2 := Nat.add_lt_add_right h (modPow2 (uintWidth u) / 2)
          rw [Nat.sub_add_cancel hxG, Nat.sub_add_cancel hyG] at h2
          exact h2⟩

/-- `MirSemantics.Scalars.signedLe` is unsigned `≤` on biased coordinates. -/
theorem signedLe_iff_signedBias_le {x y : Nat}
    (hx : x < modPow2 (uintWidth u)) (hy : y < modPow2 (uintWidth u)) :
    signedLe x y (uintBytes u) = true ↔
      signedBias (uintWidth u) x ≤ signedBias (uintWidth u) y := by
  have hIff := signedLt_iff_signedBias_lt (u := u) hy hx
  simp only [signedLe]
  cases hLt : signedLt y x (uintBytes u) with
  | true =>
    exact ⟨(fun h => nomatch h),
      fun hLe => False.elim (Nat.not_le_of_gt (hIff.mp hLt) hLe)⟩
  | false =>
    exact ⟨fun _ => Nat.le_of_not_lt (fun hGt => by
      rw [hIff.mpr hGt] at hLt; nomatch hLt), fun _ => rfl⟩

/-- Boolean form of `signedLt_iff_signedBias_lt`. -/
theorem signedLt_eq_blt_signedBias {x y : Nat}
    (hx : x < modPow2 (uintWidth u)) (hy : y < modPow2 (uintWidth u)) :
    signedLt x y (uintBytes u) =
      Nat.blt (signedBias (uintWidth u) x) (signedBias (uintWidth u) y) := by
  have hIff := signedLt_iff_signedBias_lt (u := u) hx hy
  cases hB : Nat.blt (signedBias (uintWidth u) x) (signedBias (uintWidth u) y) with
  | true => exact hIff.mpr (lt_of_blt_true hB)
  | false =>
    cases hS : signedLt x y (uintBytes u) with
    | false => rfl
    | true => rw [blt_true_of_lt (hIff.mp hS)] at hB; nomatch hB

/-- Boolean form of `signedLe_iff_signedBias_le`. -/
theorem signedLe_eq_ble_signedBias {x y : Nat}
    (hx : x < modPow2 (uintWidth u)) (hy : y < modPow2 (uintWidth u)) :
    signedLe x y (uintBytes u) =
      Nat.ble (signedBias (uintWidth u) x) (signedBias (uintWidth u) y) := by
  have hIff := signedLe_iff_signedBias_le (u := u) hx hy
  cases hB : Nat.ble (signedBias (uintWidth u) x) (signedBias (uintWidth u) y) with
  | true => exact hIff.mpr (Nat.le_of_ble_eq_true hB)
  | false =>
    cases hS : signedLe x y (uintBytes u) with
    | false => rfl
    | true => rw [Nat.ble_eq_true_of_le (hIff.mp hS)] at hB; nomatch hB

theorem three_mul_eq (h : Nat) : 3 * h = h + (h + h) := by
  have h3 : 3 * h = 2 * h + h := Nat.succ_mul 2 h
  rw [h3, Nat.two_mul, Nat.add_comm]

/-- Two negative operands whose sum stays `≥ 2^w + 2^(w-1)` do not overflow. -/
theorem signedOverflowAdd_false_of_neg_ge {a b : Nat}
    (hx : modPow2 (uintWidth u) / 2 ≤ a) (hxM : a < modPow2 (uintWidth u))
    (hy : modPow2 (uintWidth u) / 2 ≤ b) (hyM : b < modPow2 (uintWidth u))
    (hSum : modPow2 (uintWidth u) + modPow2 (uintWidth u) / 2 ≤ a + b) :
    signedOverflowAdd a b (uintBytes u) = false := by
  have hMLe : modPow2 (uintWidth u) ≤ a + b :=
    Nat.le_trans (Nat.le_add_right _ _) hSum
  have hSubLt : a + b - modPow2 (uintWidth u) < modPow2 (uintWidth u) := by
    apply nat_lt_of_add_lt_add_right (c := modPow2 (uintWidth u))
    rw [Nat.sub_add_cancel hMLe]
    exact Nat.add_lt_add hxM hyM
  have hSubGe : modPow2 (uintWidth u) / 2 ≤ a + b - modPow2 (uintWidth u) := by
    apply Nat.le_sub_of_add_le
    rw [Nat.add_comm]
    exact hSum
  have hMod : wrapVal (uintWidth u) (a + b) = a + b - modPow2 (uintWidth u) := by
    dsimp only [wrapVal]
    rw [nat_mod_eq_sub_mod hMLe]
    exact nat_mod_eq_of_lt hSubLt
  have hAddEq : Nat.add a b = a + b := rfl
  simp only [signedOverflowAdd]
  rw [isSignedNegative_of_ge_half hx hxM, isSignedNegative_of_ge_half hy hyM,
    hAddEq, wrapScalarBits_eq_wrapVal, hMod,
    isSignedNegative_of_ge_half hSubGe hSubLt]

/-- Bridge from `AbsVal.noSignedOverflowAdd`'s biased bounds
(`H ≤ bias x + bias y < 3 * H`) to `signedOverflowAdd = false`. -/
theorem signedOverflowAdd_false_of_biased_bounds {x y : Nat}
    (hx : x < modPow2 (uintWidth u)) (hy : y < modPow2 (uintWidth u))
    (hLo : halfModPow2 (uintWidth u) ≤
      signedBias (uintWidth u) x + signedBias (uintWidth u) y)
    (hHi : signedBias (uintWidth u) x + signedBias (uintWidth u) y <
      3 * halfModPow2 (uintWidth u)) :
    signedOverflowAdd x y (uintBytes u) = false := by
  rw [halfModPow2_uintWidth_eq_half] at hLo hHi
  cases Nat.lt_or_ge x (modPow2 (uintWidth u) / 2) with
  | inl hxL =>
    cases Nat.lt_or_ge y (modPow2 (uintWidth u) / 2) with
    | inl hyL =>
      rw [signedBias_uint_of_lt_half hxL, signedBias_uint_of_lt_half hyL,
        Nat.add_add_add_comm, three_mul_eq] at hHi
      exact signedOverflowAdd_false_of_nonneg_lt hxL hyL
        (nat_lt_of_add_lt_add_right hHi)
    | inr hyG =>
      exact signedOverflowAdd_false_of_opp_sign (Or.inl ⟨hxL, hyG, hy⟩)
  | inr hxG =>
    cases Nat.lt_or_ge y (modPow2 (uintWidth u) / 2) with
    | inl hyL =>
      exact signedOverflowAdd_false_of_opp_sign (Or.inr ⟨hxG, hx, hyL⟩)
    | inr hyG =>
      rw [signedBias_uint_of_ge_half hxG hx, signedBias_uint_of_ge_half hyG hy]
        at hLo
      have h2 := Nat.add_le_add_right hLo
        (modPow2 (uintWidth u) / 2 + modPow2 (uintWidth u) / 2)
      rw [Nat.add_add_add_comm (x - _) (y - _), Nat.sub_add_cancel hxG,
        Nat.sub_add_cancel hyG, ← modPow2_uintWidth_eq_add_half,
        Nat.add_comm] at h2
      exact signedOverflowAdd_false_of_neg_ge hxG hx hyG hy h2

/-- Negative minus non-negative that stays negative does not overflow. -/
theorem signedOverflowSub_false_of_neg_nonneg {a b : Nat}
    (hx : modPow2 (uintWidth u) / 2 ≤ a) (hxM : a < modPow2 (uintWidth u))
    (hy : b < modPow2 (uintWidth u) / 2)
    (hDiff : b + modPow2 (uintWidth u) / 2 ≤ a) :
    signedOverflowSub a b (uintBytes u) = false := by
  have hyM : b < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hy (Nat.div_le_self _ 2)
  have hLe : b ≤ a := Nat.le_trans (Nat.le_add_right _ _) hDiff
  have hSubLt : a - b < modPow2 (uintWidth u) :=
    Nat.lt_of_le_of_lt (Nat.sub_le a b) hxM
  have hSubGe : modPow2 (uintWidth u) / 2 ≤ a - b := by
    apply Nat.le_sub_of_add_le
    rw [Nat.add_comm]
    exact hDiff
  have hSub : Nat.sub a b = a - b := rfl
  simp only [signedOverflowSub]
  rw [wrapScalarBits_of_lt_uint hxM, wrapScalarBits_of_lt_uint hyM,
    Nat.ble_eq_true_of_le hLe]
  simp only
  rw [hSub, wrapScalarBits_of_lt_uint hSubLt,
    isSignedNegative_of_ge_half hx hxM, isSignedNegative_of_lt_half hy,
    isSignedNegative_of_ge_half hSubGe hSubLt]

/-- Non-negative minus negative that stays non-negative does not overflow. -/
theorem signedOverflowSub_false_of_nonneg_neg {a b : Nat}
    (hx : a < modPow2 (uintWidth u) / 2)
    (hy : modPow2 (uintWidth u) / 2 ≤ b) (hyM : b < modPow2 (uintWidth u))
    (hDiff : a + modPow2 (uintWidth u) / 2 < b) :
    signedOverflowSub a b (uintBytes u) = false := by
  have hxM : a < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hx (Nat.div_le_self _ 2)
  have hLt : a < b := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hDiff
  have hBle : Nat.ble b a = false := by
    cases hB : Nat.ble b a with
    | false => rfl
    | true => exact False.elim (Nat.not_le_of_gt hLt (Nat.le_of_ble_eq_true hB))
  have hbLe : b ≤ modPow2 (uintWidth u) + a :=
    Nat.le_trans (Nat.le_of_lt hyM) (Nat.le_add_right _ _)
  have hDiffLt : modPow2 (uintWidth u) + a - b < modPow2 (uintWidth u) / 2 := by
    apply nat_lt_of_add_lt_add_right (c := b)
    rw [Nat.sub_add_cancel hbLe]
    have h2 := Nat.add_lt_add_left hDiff (modPow2 (uintWidth u) / 2)
    rw [← Nat.add_assoc, Nat.add_comm (modPow2 (uintWidth u) / 2) a,
      Nat.add_assoc, ← modPow2_uintWidth_eq_add_half, Nat.add_comm a] at h2
    exact h2
  have hDiffM : modPow2 (uintWidth u) + a - b < modPow2 (uintWidth u) :=
    Nat.lt_of_lt_of_le hDiffLt (Nat.div_le_self _ 2)
  have hW : wrapScalarBits (Nat.sub (Nat.add (scalarModulus (uintBytes u)) a) b)
      (scalarModulus (uintBytes u)) = modPow2 (uintWidth u) + a - b := by
    rw [wrapScalarBits_eq_wrapVal, scalarModulus_uintBytes]
    exact wrapVal_of_lt hDiffM
  simp only [signedOverflowSub]
  rw [wrapScalarBits_of_lt_uint hxM, wrapScalarBits_of_lt_uint hyM, hBle]
  simp only
  rw [hW, isSignedNegative_of_lt_half hx, isSignedNegative_of_ge_half hy hyM,
    isSignedNegative_of_lt_half hDiffLt]

/-- Bridge from `AbsVal.noSignedOverflowSub`'s biased bounds
(`bias y ≤ bias x + H` and `bias x < bias y + H`) to
`signedOverflowSub = false`. -/
theorem signedOverflowSub_false_of_biased_bounds {x y : Nat}
    (hx : x < modPow2 (uintWidth u)) (hy : y < modPow2 (uintWidth u))
    (hLo : signedBias (uintWidth u) y ≤
      signedBias (uintWidth u) x + halfModPow2 (uintWidth u))
    (hHi : signedBias (uintWidth u) x <
      signedBias (uintWidth u) y + halfModPow2 (uintWidth u)) :
    signedOverflowSub x y (uintBytes u) = false := by
  rw [halfModPow2_uintWidth_eq_half] at hLo hHi
  cases Nat.lt_or_ge x (modPow2 (uintWidth u) / 2) with
  | inl hxL =>
    cases Nat.lt_or_ge y (modPow2 (uintWidth u) / 2) with
    | inl hyL =>
      exact signedOverflowSub_false_of_same_sign (Or.inl ⟨hxL, hyL⟩)
    | inr hyG =>
      rw [signedBias_uint_of_lt_half hxL, signedBias_uint_of_ge_half hyG hy,
        Nat.sub_add_cancel hyG] at hHi
      exact signedOverflowSub_false_of_nonneg_neg hxL hyG hy hHi
  | inr hxG =>
    cases Nat.lt_or_ge y (modPow2 (uintWidth u) / 2) with
    | inl hyL =>
      rw [signedBias_uint_of_ge_half hxG hx, signedBias_uint_of_lt_half hyL,
        Nat.sub_add_cancel hxG] at hLo
      exact signedOverflowSub_false_of_neg_nonneg hxG hx hyL hLo
    | inr hyG =>
      exact signedOverflowSub_false_of_same_sign (Or.inr ⟨hxG, hx, hyG, hy⟩)

theorem half_lt_modPow2_uint (u : UintTy) :
    modPow2 (uintWidth u) / 2 < modPow2 (uintWidth u) :=
  Nat.lt_of_le_of_lt (half_le_sub_one_uint u)
    (Nat.sub_lt (modPow2_pos _) Nat.zero_lt_one)

/-- `0` has biased coordinate `2^(w-1)`. -/
theorem signedBias_zero_uint (u : UintTy) :
    signedBias (uintWidth u) 0 = modPow2 (uintWidth u) / 2 := by
  rw [signedBias_uint_of_lt_half (half_pos_uint u), Nat.zero_add]

/-- `INT_MIN = 2^(w-1)` has biased coordinate `0`. -/
theorem signedBias_half_uint (u : UintTy) :
    signedBias (uintWidth u) (modPow2 (uintWidth u) / 2) = 0 := by
  rw [signedBias_uint_of_ge_half (Nat.le_refl _) (half_lt_modPow2_uint u),
    Nat.sub_self]

/-- `-1 = 2^w - 1` has biased coordinate `2^(w-1) - 1`. -/
theorem signedBias_minusOne_uint (u : UintTy) :
    signedBias (uintWidth u) (modPow2 (uintWidth u) - 1) =
      modPow2 (uintWidth u) / 2 - 1 := by
  rw [signedBias_uint_of_ge_half (half_le_sub_one_uint u)
    (Nat.sub_lt (modPow2_pos _) Nat.zero_lt_one), Nat.sub_right_comm,
    Nat.sub_eq_of_eq_add (modPow2_uintWidth_eq_add_half u)]

/-- Bridge from `AbsVal.safeSignedDiv` to the `MirSemantics` side conditions
of signed `div` / `rem`: the divisor is nonzero and the operands are not
`(INT_MIN, -1)` (`minSigned = 2^(w-1)`, `minusOne = 2^w - 1`). -/
theorem safeSignedDiv_sound_v2026 {a b : AbsVal} {x y : Nat}
    (hOk : AbsVal.safeSignedDiv (uintWidth u) a b = true)
    (ha : a.denote (uintWidth u) (some x))
    (hb : b.denote (uintWidth u) (some y)) :
    y ≠ 0 ∧
      ¬ (x = modPow2 (uintWidth u) / 2 ∧ y = modPow2 (uintWidth u) - 1) := by
  have h := absVal_safeSignedDiv_sound hOk ha hb
  rw [halfModPow2_uintWidth_eq_half] at h
  refine ⟨fun hy0 => h.1 (by rw [hy0]; exact signedBias_zero_uint u),
    fun hBad => h.2 ⟨?_, ?_⟩⟩
  · rw [hBad.1]; exact signedBias_half_uint u
  · rw [hBad.2]; exact signedBias_minusOne_uint u

/-- Signed `div` / `rem` under the `safeSignedDiv` side conditions never
fault; the operator is selected by unification against `hop`. -/
theorem evalScalarBinOp_sint_divrem_safe {op : BinOp} {x y : Nat}
    (locals : List LocalSlot) (mem : Memory) (hop : op = .div ∨ op = .rem)
    (hx : x < modPow2 (uintWidth u)) (hy : y < modPow2 (uintWidth u))
    (hyNe : y ≠ 0)
    (hNoOv : ¬ (x = modPow2 (uintWidth u) / 2 ∧
      y = modPow2 (uintWidth u) - 1)) :
    ∃ bits, bits < modPow2 (uintWidth u) ∧
      evalScalarBinOp op ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem true =
        .ok (.scalar ⟨bits, uintBytes u⟩) locals mem := by
  cases hop with
  | inl h => subst h; exact evalScalarBinOp_sint_div_safe locals mem hx hy hyNe hNoOv
  | inr h => subst h; exact evalScalarBinOp_sint_rem_safe locals mem hx hy hyNe hNoOv

/-- `evalSignedDiv` / `evalSignedRem` are fault-free on operands certified by
`AbsVal.safeSignedDiv`. -/
theorem safeSignedDiv_evalSigned_v2026 {a b : AbsVal} {x y : Nat}
    (locals : List LocalSlot) (mem : Memory)
    (hOk : AbsVal.safeSignedDiv (uintWidth u) a b = true)
    (ha : a.denote (uintWidth u) (some x))
    (hb : b.denote (uintWidth u) (some y)) :
    (∃ q, q < modPow2 (uintWidth u) ∧
      evalSignedDiv x y (uintBytes u) locals mem =
        .ok (.scalar ⟨q, uintBytes u⟩) locals mem) ∧
    (∃ r, r < modPow2 (uintWidth u) ∧
      evalSignedRem x y (uintBytes u) locals mem =
        .ok (.scalar ⟨r, uintBytes u⟩) locals mem) := by
  have hS := safeSignedDiv_sound_v2026 hOk ha hb
  have hx := (absVal_some_elim ha).1
  have hy := (absVal_some_elim hb).1
  have hb0 : Nat.beq y 0 = false := by
    cases h : Nat.beq y 0 with
    | false => rfl
    | true => exact False.elim (hS.1 (Nat.eq_of_beq_eq_true h))
  have hD : evalScalarBinOp .div ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem
      true = evalSignedDiv x y (uintBytes u) locals mem := by
    simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hb0]
  have hR : evalScalarBinOp .rem ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem
      true = evalSignedRem x y (uintBytes u) locals mem := by
    simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl, hb0]
  refine ⟨?_, ?_⟩
  · cases evalScalarBinOp_sint_div_safe locals mem hx hy hS.1 hS.2 with
    | intro q hq => exact ⟨q, hq.1, Eq.trans hD.symm hq.2⟩
  · cases evalScalarBinOp_sint_rem_safe locals mem hx hy hS.1 hS.2 with
    | intro r hr => exact ⟨r, hr.1, Eq.trans hR.symm hr.2⟩

/-- Signed `<` evaluates to unsigned `<` on biased coordinates. -/
theorem evalScalarBinOp_sint_lt {x y : Nat} (locals : List LocalSlot)
    (mem : Memory)
    (hx : x < modPow2 (uintWidth u)) (hy : y < modPow2 (uintWidth u)) :
    evalScalarBinOp .lt ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem true =
      .ok (.scalar (boolToScalar (Nat.blt (signedBias (uintWidth u) x)
        (signedBias (uintWidth u) y)))) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  rw [signedLt_eq_blt_signedBias hx hy]

/-- Signed `<=` evaluates to unsigned `<=` on biased coordinates. -/
theorem evalScalarBinOp_sint_le {x y : Nat} (locals : List LocalSlot)
    (mem : Memory)
    (hx : x < modPow2 (uintWidth u)) (hy : y < modPow2 (uintWidth u)) :
    evalScalarBinOp .le ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem true =
      .ok (.scalar (boolToScalar (Nat.ble (signedBias (uintWidth u) x)
        (signedBias (uintWidth u) y)))) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  rw [signedLe_eq_ble_signedBias hx hy]

/-- Signed `>` evaluates to unsigned `>` on biased coordinates. -/
theorem evalScalarBinOp_sint_gt {x y : Nat} (locals : List LocalSlot)
    (mem : Memory)
    (hx : x < modPow2 (uintWidth u)) (hy : y < modPow2 (uintWidth u)) :
    evalScalarBinOp .gt ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem true =
      .ok (.scalar (boolToScalar (Nat.blt (signedBias (uintWidth u) y)
        (signedBias (uintWidth u) x)))) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  rw [signedLt_eq_blt_signedBias hy hx]

/-- Signed `>=` evaluates to unsigned `>=` on biased coordinates. -/
theorem evalScalarBinOp_sint_ge {x y : Nat} (locals : List LocalSlot)
    (mem : Memory)
    (hx : x < modPow2 (uintWidth u)) (hy : y < modPow2 (uintWidth u)) :
    evalScalarBinOp .ge ⟨x, uintBytes u⟩ ⟨y, uintBytes u⟩ locals mem true =
      .ok (.scalar (boolToScalar (Nat.ble (signedBias (uintWidth u) y)
        (signedBias (uintWidth u) x)))) locals mem := by
  simp only [evalScalarBinOp, uintBytes_beq_zero, Nat.beq_refl]
  rw [signedLe_eq_ble_signedBias hy hx]

/-- Sign extension of a negative bit pattern to a strictly wider type sets
the new high bits (`2^w₂ - 2^w₁ + x`). -/
theorem signExtendBits_neg {u2 : UintTy} {x : Nat}
    (hx : modPow2 (uintWidth u) / 2 ≤ x) (hxM : x < modPow2 (uintWidth u))
    (hW : Nat.ble (uintBytes u2) (uintBytes u) = false) :
    signExtendBits x (uintBytes u) (uintBytes u2) =
      modPow2 (uintWidth u2) - modPow2 (uintWidth u) + x := by
  simp only [signExtendBits, hW]
  rw [wrapScalarBits_of_lt_uint hxM, isSignedNegative_of_ge_half hx hxM,
    scalarModulus_uintBytes, scalarModulus_uintBytes]
  rfl

/-- Narrowing (or same-width) `signExtendBits` truncates the bit pattern. -/
theorem signExtendBits_narrow {u2 : UintTy} {x : Nat}
    (hxM : x < modPow2 (uintWidth u))
    (hW : Nat.ble (uintBytes u2) (uintBytes u) = true) :
    signExtendBits x (uintBytes u) (uintBytes u2) = wrapVal (uintWidth u2) x := by
  simp only [signExtendBits, hW]
  rw [wrapScalarBits_of_lt_uint hxM, wrapScalarBits_eq_wrapVal]

/-- Bit pattern produced by `CastKind.intToInt` from a `uSrc`-wide source
(sign-extended iff `srcSigned` and strictly widening) to `uDst`, exactly as
computed by `evalRvalue`. -/
def intCastBits (srcSigned : Bool) (uSrc uDst : UintTy) (x : Nat) : Nat :=
  match srcSigned with
  | false => wrapScalarBits x (scalarModulus (uintBytes uDst))
  | true =>
    match Nat.ble (uintBytes uDst) (uintBytes uSrc) with
    | true => wrapScalarBits x (scalarModulus (uintBytes uDst))
    | false => signExtendBits x (uintBytes uSrc) (uintBytes uDst)

/-- Every `intToInt` cast result fits the target width. -/
theorem intCastBits_lt (srcSigned : Bool) (uSrc uDst : UintTy) (x : Nat) :
    intCastBits srcSigned uSrc uDst x < modPow2 (uintWidth uDst) := by
  have hWrap : wrapScalarBits x (scalarModulus (uintBytes uDst)) <
      modPow2 (uintWidth uDst) := by
    rw [wrapScalarBits_eq_wrapVal]
    exact nat_mod_lt _ (modPow2_pos _)
  cases srcSigned with
  | false => exact hWrap
  | true =>
    dsimp only [intCastBits]
    cases Nat.ble (uintBytes uDst) (uintBytes uSrc) with
    | true => exact hWrap
    | false => exact signExtendBits_lt_uint uSrc uDst x

/-- Unsigned-source, narrowing, and same-width casts wrap the bit pattern. -/
theorem intCastBits_wrap {srcSigned : Bool} {uSrc uDst : UintTy} (x : Nat)
    (h : srcSigned = false ∨
      Nat.ble (uintWidth uDst) (uintWidth uSrc) = true) :
    intCastBits srcSigned uSrc uDst x = wrapVal (uintWidth uDst) x := by
  cases srcSigned with
  | false => exact wrapScalarBits_eq_wrapVal uDst x
  | true =>
    cases h with
    | inl hF => nomatch hF
    | inr hLe =>
      dsimp only [intCastBits]
      rw [uintBytes_ble_eq_width, hLe]
      exact wrapScalarBits_eq_wrapVal uDst x

/-- A strictly widening cast of a non-negative signed value is the identity. -/
theorem intCastBits_widen_nonneg {uSrc uDst : UintTy} {x : Nat}
    (hx : x < modPow2 (uintWidth uSrc) / 2)
    (hW : Nat.ble (uintWidth uDst) (uintWidth uSrc) = false) :
    intCastBits true uSrc uDst x = x := by
  have hWb : Nat.ble (uintBytes uDst) (uintBytes uSrc) = false := by
    rw [uintBytes_ble_eq_width]; exact hW
  dsimp only [intCastBits]
  rw [hWb]
  exact signExtendBits_nonneg hx hWb

end SignedBias

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

/-- Relational predicate attached to a `bool` local recording the comparison
that produced it, enabling path-sensitive refinement at `switchInt` and
`assert` without fused compare-and-branch instructions. The `u*` guards
compare bit patterns in unsigned order; the `s*Const` guards compare the
two's-complement bit pattern of a signed local (at `uintWidth (intTwin i)`)
against the bit pattern of a constant in signed order (`signedBias`). -/
inductive RelGuard where
  | none
  | uleConst (reg : Nat) (u : UintTy) (bound : Nat)
  | ugtConst (reg : Nat) (u : UintTy) (bound : Nat)
  | ultReg (lhs rhs : Nat) (u : UintTy)
  | ugeReg (lhs rhs : Nat) (u : UintTy)
  | ueqConst (reg : Nat) (u : UintTy) (val : Nat)
  | uneConst (reg : Nat) (u : UintTy) (val : Nat)
  | ueqReg (lhs rhs : Nat) (u : UintTy)
  | uneReg (lhs rhs : Nat) (u : UintTy)
  | sleConst (reg : Nat) (i : IntTy) (boundBits : Nat)
  | sgtConst (reg : Nat) (i : IntTy) (boundBits : Nat)
  | seqConst (reg : Nat) (i : IntTy) (val : Nat)
  | sneConst (reg : Nat) (i : IntTy) (val : Nat)

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
  | .ueqReg l1 r1 u1, .ueqReg l2 r2 u2 =>
    Nat.beq l1 l2 && Nat.beq r1 r2 && uintTyBeq u1 u2
  | .uneReg l1 r1 u1, .uneReg l2 r2 u2 =>
    Nat.beq l1 l2 && Nat.beq r1 r2 && uintTyBeq u1 u2
  | .sleConst r1 i1 b1, .sleConst r2 i2 b2 =>
    Nat.beq r1 r2 && intTyBeq i1 i2 && Nat.beq b1 b2
  | .sgtConst r1 i1 b1, .sgtConst r2 i2 b2 =>
    Nat.beq r1 r2 && intTyBeq i1 i2 && Nat.beq b1 b2
  | .seqConst r1 i1 v1, .seqConst r2 i2 v2 =>
    Nat.beq r1 r2 && intTyBeq i1 i2 && Nat.beq v1 v2
  | .sneConst r1 i1 v1, .sneConst r2 i2 v2 =>
    Nat.beq r1 r2 && intTyBeq i1 i2 && Nat.beq v1 v2
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
           uintTy_eq_of_beq h3]
       | rw [Nat.eq_of_beq_eq_true h1, intTy_eq_of_beq h2,
           Nat.eq_of_beq_eq_true h3])
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
  | .ueqReg l r u => .uneReg l r u
  | .uneReg l r u => .ueqReg l r u
  | .sleConst r i b => .sgtConst r i b
  | .sgtConst r i b => .sleConst r i b
  | .seqConst r i v => .sneConst r i v
  | .sneConst r i v => .seqConst r i v

/-- True iff `g` references local `id`. -/
def RelGuard.mentions (id : Nat) : RelGuard → Bool
  | .none => false
  | .uleConst r _ _ => Nat.beq r id
  | .ugtConst r _ _ => Nat.beq r id
  | .ultReg l r _ => Nat.beq l id || Nat.beq r id
  | .ugeReg l r _ => Nat.beq l id || Nat.beq r id
  | .ueqConst r _ _ => Nat.beq r id
  | .uneConst r _ _ => Nat.beq r id
  | .ueqReg l r _ => Nat.beq l id || Nat.beq r id
  | .uneReg l r _ => Nat.beq l id || Nat.beq r id
  | .sleConst r _ _ => Nat.beq r id
  | .sgtConst r _ _ => Nat.beq r id
  | .seqConst r _ _ => Nat.beq r id
  | .sneConst r _ _ => Nat.beq r id

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
  | .ueqReg l r u =>
    ∀ x y, localUintNat? locals l u = some x →
      localUintNat? locals r u = some y → (b = true ↔ x = y)
  | .uneReg l r u =>
    ∀ x y, localUintNat? locals l u = some x →
      localUintNat? locals r u = some y → (b = true ↔ x ≠ y)
  | .sleConst r i boundBits =>
    ∀ x, localUintNat? locals r (intTwin i) = some x →
      (b = true ↔ signedBias (uintWidth (intTwin i)) x ≤
        signedBias (uintWidth (intTwin i)) boundBits)
  | .sgtConst r i boundBits =>
    ∀ x, localUintNat? locals r (intTwin i) = some x →
      (b = true ↔ signedBias (uintWidth (intTwin i)) boundBits <
        signedBias (uintWidth (intTwin i)) x)
  | .seqConst r i val =>
    ∀ x, localUintNat? locals r (intTwin i) = some x → (b = true ↔ x = val)
  | .sneConst r i val =>
    ∀ x, localUintNat? locals r (intTwin i) = some x → (b = true ↔ x ≠ val)

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
  | ueqReg l r u =>
    intro x y hx hy
    have hIff := h x y hx hy
    cases b with
    | true =>
      have hEq := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF), (fun hNe => False.elim (hNe hEq))⟩
    | false =>
      have hNe : x ≠ y := fun hEq => nomatch (hIff.mpr hEq)
      exact ⟨(fun _ => hNe), (fun _ => rfl)⟩
  | uneReg l r u =>
    intro x y hx hy
    have hIff := h x y hx hy
    cases b with
    | true =>
      have hNe := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF), (fun hEq => False.elim (hNe hEq))⟩
    | false =>
      have hEq : x = y := by
        cases hB : Nat.beq x y with
        | true => exact Nat.eq_of_beq_eq_true hB
        | false => exact False.elim (nomatch (hIff.mpr (nat_ne_of_beq_false hB)))
      exact ⟨(fun _ => hEq), (fun _ => rfl)⟩
  | sleConst r i bound =>
    intro x hx
    have hIff := h x hx
    cases b with
    | true =>
      have hLe := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF),
        (fun hGt => False.elim (Nat.not_le_of_gt hGt hLe))⟩
    | false =>
      exact ⟨(fun _ => Nat.lt_of_not_le (fun hLe => nomatch (hIff.mpr hLe))),
        (fun _ => rfl)⟩
  | sgtConst r i bound =>
    intro x hx
    have hIff := h x hx
    cases b with
    | true =>
      have hGt := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF),
        (fun hLe => False.elim (Nat.not_le_of_gt hGt hLe))⟩
    | false =>
      exact ⟨(fun _ => Nat.le_of_not_lt (fun hGt => nomatch (hIff.mpr hGt))),
        (fun _ => rfl)⟩
  | seqConst r i val =>
    intro x hx
    have hIff := h x hx
    cases b with
    | true =>
      have hEq := hIff.mp rfl
      exact ⟨(fun hF => nomatch hF), (fun hNe => False.elim (hNe hEq))⟩
    | false =>
      have hNe : x ≠ val := fun hEq => nomatch (hIff.mpr hEq)
      exact ⟨(fun _ => hNe), (fun _ => rfl)⟩
  | sneConst r i val =>
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
  | ueqReg l r u =>
    intro x y hx hy
    simp only [RelGuard.mentions] at hNoMent
    rw [hLocEq l u (bool_or_false_left hNoMent)] at hx
    rw [hLocEq r u (bool_or_false_right hNoMent)] at hy
    exact hDen x y hx hy
  | uneReg l r u =>
    intro x y hx hy
    simp only [RelGuard.mentions] at hNoMent
    rw [hLocEq l u (bool_or_false_left hNoMent)] at hx
    rw [hLocEq r u (bool_or_false_right hNoMent)] at hy
    exact hDen x y hx hy
  | sleConst r i bound =>
    intro x hx
    rw [hLocEq r (intTwin i) hNoMent] at hx
    exact hDen x hx
  | sgtConst r i bound =>
    intro x hx
    rw [hLocEq r (intTwin i) hNoMent] at hx
    exact hDen x hx
  | seqConst r i val =>
    intro x hx
    rw [hLocEq r (intTwin i) hNoMent] at hx
    exact hDen x hx
  | sneConst r i val =>
    intro x hx
    rw [hLocEq r (intTwin i) hNoMent] at hx
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

/-- Refine `a` under `x ≠ v` by intersecting with the exact ring complement
`[(v + 1) mod 2^w, (v - 1) mod 2^w]` on `Z / 2^w Z`. -/
def AbsVal.refineUneConst (w : Nat) (a : AbsVal) (v : Nat) : AbsVal :=
  match validWidth w && a.isInit with
  | false => AbsVal.bot
  | true =>
    let M := modPow2 w
    match Nat.blt v M with
    | false => a
    | true =>
      let lo := Nat.mod (v + 1) M
      let hi := Nat.mod (M + v - 1) M
      reduceAbsVal w
        ⟨.init, a.tnum, WrappedInterval.meet M a.wi (.iv lo hi), a.sc⟩

private theorem wrapped_denote_complement {w x v : Nat}
    (hw : validWidth w = true) (hx : x < modPow2 w) (hv : v < modPow2 w)
    (hNe : x ≠ v) :
    WrappedInterval.denote (modPow2 w)
      (.iv (Nat.mod (v + 1) (modPow2 w))
           (Nat.mod (modPow2 w + v - 1) (modPow2 w))) x := by
  let M := modPow2 w
  have h2Le : 2 ≤ M := modPow2_mono (Nat.le_of_ble_eq_true (bool_and_true_left hw))
  have hMPos : 0 < M := modPow2_pos w
  cases v with
  | zero =>
    have h1Lt : 1 < M := Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) h2Le
    have hM1Lt : M - 1 < M := Nat.sub_lt hMPos Nat.zero_lt_one
    have h1LeM1 : 1 ≤ M - 1 := Nat.le_sub_one_of_lt h1Lt
    have hLo : Nat.mod (0 + 1) M = 1 := Nat.mod_eq_of_lt h1Lt
    have hHi : Nat.mod (M + 0 - 1) M = M - 1 := by
      rw [Nat.add_zero]
      exact Nat.mod_eq_of_lt hM1Lt
    rw [hLo, hHi]
    exact wrapped_denote_iv_of_le h1Lt hM1Lt h1LeM1
      (Nat.pos_of_ne_zero hNe) (Nat.le_sub_one_of_lt hx)
  | succ k =>
    have hkLt : k < M := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_of_lt hv)
    have hHi : Nat.mod (M + (k + 1) - 1) M = k := by
      have hSub : M + (k + 1) - 1 = M + k := by
        rw [← Nat.add_assoc, Nat.add_sub_cancel]
      rw [hSub]
      change (M + k) % M = k
      rw [Nat.add_mod_left]
      exact Nat.mod_eq_of_lt hkLt
    cases hTop : Nat.beq (k + 1) (M - 1) with
    | true =>
      have hEq : k + 1 = M - 1 := Nat.eq_of_beq_eq_true hTop
      have hLo : Nat.mod (k + 1 + 1) M = 0 := by
        rw [hEq, Nat.sub_add_cancel hMPos]
        exact Nat.mod_self M
      have hxLtTop : x < k + 1 := by
        rw [hEq]
        exact Nat.lt_of_le_of_ne (Nat.le_sub_one_of_lt hx) (by rw [← hEq]; exact hNe)
      rw [hLo, hHi]
      exact wrapped_denote_iv_of_le hMPos hkLt (Nat.zero_le k) (Nat.zero_le x)
        (Nat.le_of_lt_succ hxLtTop)
    | false =>
      have hNeTop : k + 1 ≠ M - 1 := nat_ne_of_beq_false hTop
      have hLtTop : k + 1 < M - 1 :=
        Nat.lt_of_le_of_ne (Nat.le_sub_one_of_lt hv) hNeTop
      have hk2Lt : k + 2 < M := by
        have h1 : k + 1 + 1 ≤ M - 1 := hLtTop
        exact Nat.lt_of_le_of_lt h1 (Nat.sub_lt hMPos Nat.zero_lt_one)
      have hLo : Nat.mod (k + 1 + 1) M = k + 2 := Nat.mod_eq_of_lt hk2Lt
      have hNotLe : Nat.ble (k + 2) k = false := by
        cases hB : Nat.ble (k + 2) k with
        | false => rfl
        | true =>
          exact False.elim (Nat.not_le_of_gt
            (Nat.lt_trans (Nat.lt_succ_self k) (Nat.lt_succ_self (k + 1)))
            (Nat.le_of_ble_eq_true hB))
      rw [hLo, hHi]
      simp only [WrappedInterval.denote, hNotLe]
      refine ⟨hk2Lt, hkLt, hx, ?_⟩
      cases Nat.lt_or_ge x (k + 1) with
      | inl hLt => exact Or.inr (Nat.le_of_lt_succ hLt)
      | inr hGe =>
        exact Or.inl (Nat.lt_of_le_of_ne hGe (fun h => hNe h.symm))

/-- Soundness of `AbsVal.refineUneConst`. -/
theorem absVal_refineUneConst_sound {w x v : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x))
    (hai : a.isInit = true) (hNe : x ≠ v) :
    (AbsVal.refineUneConst w a v).denote w (some x) := by
  unfold AbsVal.refineUneConst
  rw [hw, hai]
  dsimp only
  cases hV : Nat.blt v (modPow2 w) with
  | false => exact ha
  | true =>
    dsimp only
    have haE := absVal_some_elim ha
    apply reduceAbsVal_sound hw
    exact ⟨⟨x, rfl, haE.1⟩, haE.2.1,
      wrappedInterval_meet_sound (modPow2_pos w) haE.2.2.1
        (wrapped_denote_complement hw haE.1 (lt_of_blt_true hV) hNe),
      haE.2.2.2⟩

/-- Reduced-product meet of two initialized `AbsVal`s (returns `AbsVal.bot`
when the components are disjoint). -/
def AbsVal.meetInit (w : Nat) (a b : AbsVal) : AbsVal :=
  match validWidth w && a.isInit && b.isInit with
  | false => AbsVal.bot
  | true =>
    match Tnum.meet a.tnum b.tnum with
    | none => AbsVal.bot
    | some tn =>
      reduceAbsVal w
        ⟨.init, tn, WrappedInterval.meet (modPow2 w) a.wi b.wi,
          StridedCong.meet a.sc b.sc⟩

/-- Soundness of `AbsVal.meetInit`. -/
theorem absVal_meetInit_sound {w x : Nat} {a b : AbsVal}
    (hw : validWidth w = true) (hai : a.isInit = true) (hbi : b.isInit = true)
    (ha : a.denote w (some x)) (hb : b.denote w (some x)) :
    (AbsVal.meetInit w a b).denote w (some x) := by
  have haE := absVal_some_elim ha
  have hbE := absVal_some_elim hb
  unfold AbsVal.meetInit
  rw [hw, hai, hbi]
  cases hT : Tnum.meet a.tnum b.tnum with
  | none =>
    exact False.elim (tnum_meet_none_impossible haE.2.1 hbE.2.1 hT)
  | some tn =>
    simp only
    apply reduceAbsVal_sound hw
    exact ⟨⟨x, rfl, haE.1⟩, tnum_meet_sound haE.2.1 hbE.2.1 hT,
      wrappedInterval_meet_sound (modPow2_pos w) haE.2.2.1 hbE.2.2.1,
      stridedCong_meet_sound haE.2.2.2 hbE.2.2.2⟩

/-! ## 5. Abstract Local Slots (`MirAbsSlot`) and Frames (`MirAbsEnv`) -/

/-- Abstract local slot. `.top` describes any concrete slot (used for locals
of unsupported type), `.dead` a storage-dead local, `.uint` / `.bool` scalar
locals, `.unit isInit` a `()` local, and `.uintBoolPair` / `.sintBoolPair`
checked-arithmetic `(T, bool)` tuples (`*WithOverflow`). `.uintCopy u a src`
and `.sintCopy i a src` additionally hold the same bit pattern as local `src`
(recorded by `_t = copy _src`, so comparisons on `_t` synthesize `RelGuard`s
on `_src`). `.sint i a` is a signed local tracked at `uintWidth (intTwin i)`. -/
inductive MirAbsSlot where
  | top
  | dead
  | uint (u : UintTy) (a : AbsVal)
  | bool (b : BoolAbs)
  | unit (isInit : Bool)
  | uintBoolPair (u : UintTy) (a : AbsVal) (ov : BoolAbs)
  | uintCopy (u : UintTy) (a : AbsVal) (src : Nat)
  | sint (i : IntTy) (a : AbsVal)
  | sintBoolPair (i : IntTy) (a : AbsVal) (ov : BoolAbs)
  | sintCopy (i : IntTy) (a : AbsVal) (src : Nat)

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
  | .sint i a =>
    ty.kind = .int i ∧
    match cs with
    | .dead => False
    | .uninit => a.denote (uintWidth (intTwin i)) none
    | .init v =>
      match v with
      | .scalar sc =>
        sc.sizeBytes = uintBytes (intTwin i) ∧
        a.denote (uintWidth (intTwin i)) (some sc.bits)
      | _ => False
  | .sintBoolPair i a ov =>
    ty.kind = .tuple [.int i, .bool] ∧
    match cs with
    | .dead => False
    | .uninit => a.denote (uintWidth (intTwin i)) none ∧ ov.denote locals none
    | .init v =>
      match v with
      | .aggregate 0 [.scalar sc, vb] =>
        sc.sizeBytes = uintBytes (intTwin i) ∧
        a.denote (uintWidth (intTwin i)) (some sc.bits) ∧
        ov.denote locals (some vb)
      | _ => False
  | .sintCopy i a src =>
    ty.kind = .int i ∧
    match cs with
    | .dead => False
    | .uninit => a.denote (uintWidth (intTwin i)) none
    | .init v =>
      match v with
      | .scalar sc =>
        sc.sizeBytes = uintBytes (intTwin i) ∧
        a.denote (uintWidth (intTwin i)) (some sc.bits) ∧
        localUintNat? locals src (intTwin i) = some sc.bits
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

/-- Forgetting the copy alias of a `.sintCopy` slot is sound. -/
theorem sintCopy_denote_sint {ty : Ty} {locals : List LocalSlot} {i : IntTy}
    {a : AbsVal} {src : Nat} {cs : LocalSlot}
    (h : (MirAbsSlot.sintCopy i a src).denote ty locals cs) :
    (MirAbsSlot.sint i a).denote ty locals cs := by
  refine ⟨h.1, ?_⟩
  cases cs with
  | dead => exact h.2
  | uninit => exact h.2
  | init v =>
    cases v with
    | scalar sc => exact ⟨h.2.1, h.2.2.1⟩
    | _ => exact h.2

/-- Canonical denotation of an initialized `.sint` slot: the declared type is
`int i`, and the stored scalar has the twin byte width with its
two's-complement bit pattern described by `a` (signed order is recovered
through `signedBias (uintWidth (intTwin i))`). -/
theorem mirAbsSlot_sint_denote_iff {ty : Ty} {locals : List LocalSlot}
    {i : IntTy} {a : AbsVal} {sc : ScalarInt} :
    (MirAbsSlot.sint i a).denote ty locals (.init (.scalar sc)) ↔
      ty.kind = .int i ∧ sc.sizeBytes = uintBytes (intTwin i) ∧
        a.denote (uintWidth (intTwin i)) (some sc.bits) := Iff.rfl

/-- A `.sint` slot denotes exactly what the `.uint` slot of its unsigned twin
denotes at the twin type. -/
theorem mirAbsSlot_sint_denote_twin {ty ty' : Ty} {locals : List LocalSlot}
    {i : IntTy} {a : AbsVal} {cs : LocalSlot}
    (hTy : ty.kind = .int i) (hTy' : ty'.kind = .uint (intTwin i)) :
    (MirAbsSlot.sint i a).denote ty locals cs ↔
      (MirAbsSlot.uint (intTwin i) a).denote ty' locals cs := by
  cases cs with
  | dead => exact ⟨fun h => ⟨hTy', h.2⟩, fun h => ⟨hTy, h.2⟩⟩
  | uninit => exact ⟨fun h => ⟨hTy', h.2⟩, fun h => ⟨hTy, h.2⟩⟩
  | init v => exact ⟨fun h => ⟨hTy', h.2⟩, fun h => ⟨hTy, h.2⟩⟩

/-- Live-but-uninitialized abstract slot for a local of declared type `ty`
(the abstract counterpart of `StorageLive` / `Deinit`). -/
def uninitSlotFor (ty : Ty) : MirAbsSlot :=
  match ty.kind with
  | .uint u => .uint u (AbsVal.uninit (uintWidth u))
  | .bool => .bool .uninit
  | .tuple [] => .unit false
  | .tuple [.uint u, .bool] => .uintBoolPair u (AbsVal.uninit (uintWidth u)) .uninit
  | .int i => .sint i (AbsVal.uninit (uintWidth (intTwin i)))
  | .tuple [.int i, .bool] =>
    .sintBoolPair i (AbsVal.uninit (uintWidth (intTwin i))) .uninit
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
  · rename_i i h
    exact ⟨h, absVal_uninit_sound_none⟩
  · rename_i i h
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
  | .sint _ a => a.isInit
  | .sintBoolPair _ a ov => a.isInit && ov.isInit
  | .sintCopy _ a _ => a.isInit
  | _ => false

/-- `slot` is unreachable (empty concretization). -/
def MirAbsSlot.isBot : MirAbsSlot → Bool
  | .uint _ a => a.isBot
  | .bool ba => ba.isBot
  | .uintBoolPair _ a ov => a.isBot || ov.isBot
  | .uintCopy _ a _ => a.isBot
  | .sint _ a => a.isBot
  | .sintBoolPair _ a ov => a.isBot || ov.isBot
  | .sintCopy _ a _ => a.isBot
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
  | sint i a =>
    cases cs with
    | dead => exact h.2
    | uninit => exact absVal_not_isBot hBot h.2
    | init v =>
      cases v with
      | scalar sc => exact absVal_not_isBot hBot h.2.2
      | _ => exact h.2
  | sintCopy i a src =>
    have h' := sintCopy_denote_sint h
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
  | sintBoolPair i a ov =>
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
  | .sint i _ => .sint i (AbsVal.uninit (uintWidth (intTwin i)))
  | .sintBoolPair i _ _ =>
    .sintBoolPair i (AbsVal.uninit (uintWidth (intTwin i))) .uninit
  | .sintCopy i _ _ => .sint i (AbsVal.uninit (uintWidth (intTwin i)))
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
  | sint i _ => exact ⟨h.1, absVal_uninit_sound_none⟩
  | sintBoolPair i _ _ => exact ⟨h.1, absVal_uninit_sound_none, True.intro⟩
  | sintCopy i _ _ => exact ⟨h.1, absVal_uninit_sound_none⟩

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
  | sint _ _ => exact h.2
  | sintBoolPair _ _ _ => exact h.2
  | sintCopy _ _ _ => exact h.2

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
  | sint i a =>
    cases cs with
    | dead => exact False.elim h.2
    | uninit =>
      cases absVal_init_of_isInit hInit h.2 with
      | intro _ hx => nomatch hx.1
    | init v =>
      cases v with
      | scalar sc => exact ⟨.scalar sc, rfl, rfl⟩
      | _ => exact False.elim h.2
  | sintBoolPair i a ov =>
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
  | sintCopy i a src =>
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

/-- Extract the concrete scalar of an initialized `.sint` slot. -/
theorem sint_slot_extract {ty : Ty} {locals : List LocalSlot} {i : IntTy}
    {a : AbsVal} {cs : LocalSlot} (hInit : a.isInit = true)
    (h : (MirAbsSlot.sint i a).denote ty locals cs) :
    ∃ sc, cs = .init (.scalar sc) ∧ sc.sizeBytes = uintBytes (intTwin i) ∧
      a.denote (uintWidth (intTwin i)) (some sc.bits) := by
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

/-- Extract the concrete `(scalar, bool)` aggregate of an initialized
`.sintBoolPair` slot. -/
theorem sintBoolPair_slot_extract {ty : Ty} {locals : List LocalSlot}
    {i : IntTy} {a : AbsVal} {ov : BoolAbs} {cs : LocalSlot}
    (hInit : (a.isInit && ov.isInit) = true)
    (h : (MirAbsSlot.sintBoolPair i a ov).denote ty locals cs) :
    ∃ sc vb, cs = .init (.aggregate 0 [.scalar sc, vb]) ∧
      sc.sizeBytes = uintBytes (intTwin i) ∧
      a.denote (uintWidth (intTwin i)) (some sc.bits) ∧
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
  | .sintBoolPair _ _ ov => ov.noRelGuard
  | .sintCopy _ _ _ => false
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
  | sint _ _ => exact hDen
  | sintCopy _ _ _ => nomatch hNoG
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
  | sintBoolPair i a ov =>
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
  | .sintBoolPair i a ov => .sintBoolPair i a (ov.clearGuardIf id)
  | .sintCopy i a src =>
    match Nat.beq src id with
    | true => .sint i a
    | false => .sintCopy i a src
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
  | sint _ _ => exact h
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
  | sintCopy i a src =>
    cases hS : Nat.beq src id with
    | true =>
      simp only [MirAbsSlot.clearGuardIf, hS]
      have h' := sintCopy_denote_sint h
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
          rw [localUintNat?_set?_ne (intTwin i) hSet
            (fun hE => nat_ne_of_beq_false hS hE.symm)]
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
  | sintBoolPair i a ov =>
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
    | .sint i1 a1, .sint i2 a2 =>
      intTyBeq i1 i2 && AbsVal.le (uintWidth (intTwin i1)) a1 a2
    | .sintBoolPair i1 a1 ov1, .sintBoolPair i2 a2 ov2 =>
      intTyBeq i1 i2 && AbsVal.le (uintWidth (intTwin i1)) a1 a2 &&
        BoolAbs.le ov1 ov2
    | .sintCopy i1 a1 _, .sint i2 a2 =>
      intTyBeq i1 i2 && AbsVal.le (uintWidth (intTwin i1)) a1 a2
    | .sintCopy i1 a1 s1, .sintCopy i2 a2 s2 =>
      (intTyBeq i1 i2 && Nat.beq s1 s2) &&
        AbsVal.le (uintWidth (intTwin i1)) a1 a2
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
    | sint i2 a2 =>
      cases a with
      | sint i1 a1 =>
        have hi := intTy_eq_of_beq (bool_and_true_left hLe)
        have hA := bool_and_true_right hLe
        subst hi
        refine ⟨ha.1, ?_⟩
        cases cs with
        | dead => exact ha.2
        | uninit => exact absVal_le_sound hA ha.2
        | init v =>
          cases v with
          | scalar sc => exact ⟨ha.2.1, absVal_le_sound hA ha.2.2⟩
          | _ => exact ha.2
      | sintCopy i1 a1 s1 =>
        have hi := intTy_eq_of_beq (bool_and_true_left hLe)
        have hA := bool_and_true_right hLe
        subst hi
        refine ⟨ha.1, ?_⟩
        cases cs with
        | dead => exact ha.2
        | uninit => exact absVal_le_sound hA ha.2
        | init v =>
          cases v with
          | scalar sc => exact ⟨ha.2.1, absVal_le_sound hA ha.2.2.1⟩
          | _ => exact ha.2
      | _ => nomatch hLe
    | sintCopy i2 a2 s2 =>
      cases a with
      | sintCopy i1 a1 s1 =>
        have h12 := bool_and_true_left hLe
        have hi := intTy_eq_of_beq (bool_and_true_left h12)
        have hs := Nat.eq_of_beq_eq_true (bool_and_true_right h12)
        have hA := bool_and_true_right hLe
        subst hi
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
    | sintBoolPair i2 a2 ov2 =>
      cases a with
      | sintBoolPair i1 a1 ov1 =>
        have h12 := bool_and_true_left hLe
        have hi := intTy_eq_of_beq (bool_and_true_left h12)
        have hA := bool_and_true_right h12
        have hOv := bool_and_true_right hLe
        subst hi
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

/-- Pointwise inclusion helper on `MirAbsEnv`. -/
private def mirAbsEnvLeAux : MirAbsEnv → MirAbsEnv → Bool
  | [], [] => true
  | a :: as, b :: bs => MirAbsSlot.le a b && mirAbsEnvLeAux as bs
  | _, _ => false

/-- Lattice inclusion on `MirAbsEnv` (an unreachable `mirAbsEnvIsBot`
environment is bottom and included in every same-length environment). -/
def mirAbsEnvLe (e1 e2 : MirAbsEnv) : Bool :=
  match mirAbsEnvIsBot e1 with
  | true => Nat.beq (length e1) (length e2)
  | false => mirAbsEnvLeAux e1 e2

private theorem mirAbsEnvLeAux_length :
    ∀ {e1 e2 : MirAbsEnv}, mirAbsEnvLeAux e1 e2 = true → length e1 = length e2
  | [], [], _ => rfl
  | _ :: _, _ :: _, h =>
    congrArg Nat.succ (mirAbsEnvLeAux_length (bool_and_true_right h))
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem mirAbsEnvLe_length {e1 e2 : MirAbsEnv}
    (h : mirAbsEnvLe e1 e2 = true) : length e1 = length e2 := by
  unfold mirAbsEnvLe at h
  cases hB : mirAbsEnvIsBot e1 with
  | true => rw [hB] at h; exact Nat.eq_of_beq_eq_true h
  | false => rw [hB] at h; exact mirAbsEnvLeAux_length h

private theorem mirAbsEnvLeAux_get :
    ∀ {e1 e2 : MirAbsEnv} {i : Nat} {a b : MirAbsSlot},
      mirAbsEnvLeAux e1 e2 = true → get? e1 i = some a → get? e2 i = some b →
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
    mirAbsEnvLeAux_get (e1 := xs) (e2 := ys) (i := i) (bool_and_true_right h) h1 h2

/-- Soundness of `mirAbsEnvLe`. -/
theorem mirAbsEnvLe_sound {decls : List LocalDecl} {e1 e2 : MirAbsEnv}
    {locals : List LocalSlot}
    (hLe : mirAbsEnvLe e1 e2 = true) (h1 : mirAbsEnvDenote decls e1 locals) :
    mirAbsEnvDenote decls e2 locals := by
  unfold mirAbsEnvLe at hLe
  cases hB : mirAbsEnvIsBot e1 with
  | true => exact False.elim (mirAbsEnv_not_isBot hB h1)
  | false =>
    rw [hB] at hLe
    refine ⟨Eq.trans (mirAbsEnvLeAux_length hLe).symm h1.1, h1.2.1, ?_⟩
    intro i d s2 cs hD h2 hCs
    cases get?_exists_of_length (mirAbsEnvLeAux_length hLe) h2 with
    | intro s1 hs1 =>
      exact mirAbsSlot_le_sound (mirAbsEnvLeAux_get hLe hs1 h2)
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

/-- Join of two plain signed slots (`.top` on a type mismatch). -/
def sintJoinSlot (i1 : IntTy) (a1 : AbsVal) (i2 : IntTy) (a2 : AbsVal) :
    MirAbsSlot :=
  match intTyBeq i1 i2 with
  | true => .sint i1 (AbsVal.join (uintWidth (intTwin i1)) a1 a2)
  | false => .top

theorem sintJoinSlot_sound_left {ty : Ty} {locals : List LocalSlot}
    {i1 i2 : IntTy} {a1 a2 : AbsVal} {cs : LocalSlot}
    (ha : (MirAbsSlot.sint i1 a1).denote ty locals cs) :
    (sintJoinSlot i1 a1 i2 a2).denote ty locals cs := by
  unfold sintJoinSlot
  cases intTyBeq i1 i2 with
  | false => exact True.intro
  | true =>
    refine ⟨ha.1, ?_⟩
    cases cs with
    | dead => exact ha.2
    | uninit => exact absVal_join_sound_left (uintWidth_valid (intTwin i1)) a1 a2 ha.2
    | init v =>
      cases v with
      | scalar sc =>
        exact ⟨ha.2.1,
          absVal_join_sound_left (uintWidth_valid (intTwin i1)) a1 a2 ha.2.2⟩
      | _ => exact ha.2

theorem sintJoinSlot_sound_right {ty : Ty} {locals : List LocalSlot}
    {i1 i2 : IntTy} {a1 a2 : AbsVal} {cs : LocalSlot}
    (hb : (MirAbsSlot.sint i2 a2).denote ty locals cs) :
    (sintJoinSlot i1 a1 i2 a2).denote ty locals cs := by
  unfold sintJoinSlot
  cases hI : intTyBeq i1 i2 with
  | false => exact True.intro
  | true =>
    have hi := intTy_eq_of_beq hI
    subst hi
    refine ⟨hb.1, ?_⟩
    cases cs with
    | dead => exact hb.2
    | uninit => exact absVal_join_sound_right (uintWidth_valid (intTwin i1)) a1 a2 hb.2
    | init v =>
      cases v with
      | scalar sc =>
        exact ⟨hb.2.1,
          absVal_join_sound_right (uintWidth_valid (intTwin i1)) a1 a2 hb.2.2⟩
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
    | .sint i1 a1, .sint i2 a2 =>
      match intTyBeq i1 i2 with
      | true => .sint i1 (AbsVal.join (uintWidth (intTwin i1)) a1 a2)
      | false => .top
    | .sintBoolPair i1 a1 ov1, .sintBoolPair i2 a2 ov2 =>
      match intTyBeq i1 i2 with
      | true =>
        .sintBoolPair i1 (AbsVal.join (uintWidth (intTwin i1)) a1 a2)
          (BoolAbs.join ov1 ov2)
      | false => .top
    | .sintCopy i1 a1 s1, .sintCopy i2 a2 s2 =>
      match Nat.beq s1 s2 with
      | true =>
        match intTyBeq i1 i2 with
        | true => .sintCopy i1 (AbsVal.join (uintWidth (intTwin i1)) a1 a2) s1
        | false => .top
      | false => sintJoinSlot i1 a1 i2 a2
    | .sintCopy i1 a1 _, .sint i2 a2 => sintJoinSlot i1 a1 i2 a2
    | .sint i1 a1, .sintCopy i2 a2 _ => sintJoinSlot i1 a1 i2 a2
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
      | sint i1 a1 =>
        cases b with
        | sint i2 a2 =>
          simp only
          cases intTyBeq i1 i2 with
          | false => exact True.intro
          | true =>
            refine ⟨ha.1, ?_⟩
            cases cs with
            | dead => exact ha.2
            | uninit =>
              exact absVal_join_sound_left (uintWidth_valid (intTwin i1)) a1 a2 ha.2
            | init v =>
              cases v with
              | scalar sc =>
                exact ⟨ha.2.1,
                  absVal_join_sound_left (uintWidth_valid (intTwin i1)) a1 a2 ha.2.2⟩
              | _ => exact ha.2
        | sintCopy i2 a2 s2 => exact sintJoinSlot_sound_left ha
        | _ => exact True.intro
      | sintCopy i1 a1 s1 =>
        cases b with
        | sintCopy i2 a2 s2 =>
          simp only
          cases hS : Nat.beq s1 s2 with
          | false => exact sintJoinSlot_sound_left (sintCopy_denote_sint ha)
          | true =>
            simp only
            cases intTyBeq i1 i2 with
            | false => exact True.intro
            | true =>
              refine ⟨ha.1, ?_⟩
              cases cs with
              | dead => exact ha.2
              | uninit =>
                exact absVal_join_sound_left (uintWidth_valid (intTwin i1)) a1 a2 ha.2
              | init v =>
                cases v with
                | scalar sc =>
                  exact ⟨ha.2.1,
                    absVal_join_sound_left (uintWidth_valid (intTwin i1)) a1 a2
                      ha.2.2.1,
                    ha.2.2.2⟩
                | _ => exact ha.2
        | sint i2 a2 => exact sintJoinSlot_sound_left (sintCopy_denote_sint ha)
        | _ => exact True.intro
      | sintBoolPair i1 a1 ov1 =>
        cases b with
        | sintBoolPair i2 a2 ov2 =>
          simp only
          cases intTyBeq i1 i2 with
          | false => exact True.intro
          | true =>
            refine ⟨ha.1, ?_⟩
            cases cs with
            | dead => exact ha.2
            | uninit =>
              exact ⟨absVal_join_sound_left (uintWidth_valid (intTwin i1)) a1 a2 ha.2.1,
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
                            absVal_join_sound_left (uintWidth_valid (intTwin i1)) a1 a2
                              ha.2.2.1,
                            boolAbs_join_sound_left ha.2.2.2⟩
                    | _ => exact ha.2
              | _ => exact ha.2
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
      | sint i2 a2 =>
        cases a with
        | sint i1 a1 =>
          simp only
          cases hI : intTyBeq i1 i2 with
          | false => exact True.intro
          | true =>
            have hi := intTy_eq_of_beq hI
            subst hi
            refine ⟨hb.1, ?_⟩
            cases cs with
            | dead => exact hb.2
            | uninit =>
              exact absVal_join_sound_right (uintWidth_valid (intTwin i1)) a1 a2 hb.2
            | init v =>
              cases v with
              | scalar sc =>
                exact ⟨hb.2.1,
                  absVal_join_sound_right (uintWidth_valid (intTwin i1)) a1 a2 hb.2.2⟩
              | _ => exact hb.2
        | sintCopy i1 a1 s1 => exact sintJoinSlot_sound_right hb
        | _ => exact True.intro
      | sintCopy i2 a2 s2 =>
        cases a with
        | sintCopy i1 a1 s1 =>
          simp only
          cases hS : Nat.beq s1 s2 with
          | false => exact sintJoinSlot_sound_right (sintCopy_denote_sint hb)
          | true =>
            have hs := Nat.eq_of_beq_eq_true hS
            subst hs
            simp only
            cases hI : intTyBeq i1 i2 with
            | false => exact True.intro
            | true =>
              have hi := intTy_eq_of_beq hI
              subst hi
              refine ⟨hb.1, ?_⟩
              cases cs with
              | dead => exact hb.2
              | uninit =>
                exact absVal_join_sound_right (uintWidth_valid (intTwin i1)) a1 a2 hb.2
              | init v =>
                cases v with
                | scalar sc =>
                  exact ⟨hb.2.1,
                    absVal_join_sound_right (uintWidth_valid (intTwin i1)) a1 a2
                      hb.2.2.1,
                    hb.2.2.2⟩
                | _ => exact hb.2
        | sint i1 a1 => exact sintJoinSlot_sound_right (sintCopy_denote_sint hb)
        | _ => exact True.intro
      | sintBoolPair i2 a2 ov2 =>
        cases a with
        | sintBoolPair i1 a1 ov1 =>
          simp only
          cases hI : intTyBeq i1 i2 with
          | false => exact True.intro
          | true =>
            have hi := intTy_eq_of_beq hI
            subst hi
            refine ⟨hb.1, ?_⟩
            cases cs with
            | dead => exact hb.2
            | uninit =>
              exact ⟨absVal_join_sound_right (uintWidth_valid (intTwin i1)) a1 a2 hb.2.1,
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
                            absVal_join_sound_right (uintWidth_valid (intTwin i1)) a1 a2
                              hb.2.2.1,
                            boolAbs_join_sound_right hb.2.2.2⟩
                    | _ => exact hb.2
              | _ => exact hb.2
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

/-- Pointwise join helper on `MirAbsEnv`. -/
private def mirAbsEnvJoinAux : MirAbsEnv → MirAbsEnv → Option MirAbsEnv
  | [], [] => some []
  | a :: as, b :: bs =>
    match mirAbsEnvJoinAux as bs with
    | some cs => some (MirAbsSlot.join a b :: cs)
    | none => none
  | _, _ => none

/-- Lattice join on `MirAbsEnv` (fails closed on a length mismatch; an
unreachable environment `mirAbsEnvIsBot` acts as smashed bottom). -/
def mirAbsEnvJoin (e1 e2 : MirAbsEnv) : Option MirAbsEnv :=
  match Nat.beq (length e1) (length e2) with
  | false => none
  | true =>
    match mirAbsEnvIsBot e1 with
    | true => some e2
    | false =>
      match mirAbsEnvIsBot e2 with
      | true => some e1
      | false => mirAbsEnvJoinAux e1 e2

private theorem mirAbsEnvJoinAux_get :
    ∀ {e1 e2 e3 : MirAbsEnv}, mirAbsEnvJoinAux e1 e2 = some e3 →
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
    simp only [mirAbsEnvJoinAux] at h
    cases hJ : mirAbsEnvJoinAux as bs with
    | none => rw [hJ] at h; nomatch h
    | some cs =>
      rw [hJ] at h
      injection h with h
      subst h
      have ih := mirAbsEnvJoinAux_get hJ
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
  unfold mirAbsEnvJoin at hJ
  cases hLen : Nat.beq (length e1) (length e2) with
  | false => rw [hLen] at hJ; nomatch hJ
  | true =>
    rw [hLen] at hJ
    cases hB1 : mirAbsEnvIsBot e1 with
    | true => exact False.elim (mirAbsEnv_not_isBot hB1 h1)
    | false =>
      rw [hB1] at hJ
      cases hB2 : mirAbsEnvIsBot e2 with
      | true =>
        rw [hB2] at hJ
        injection hJ with hEq
        subst hEq
        exact h1
      | false =>
        rw [hB2] at hJ
        have hG := mirAbsEnvJoinAux_get hJ
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
  unfold mirAbsEnvJoin at hJ
  cases hLen : Nat.beq (length e1) (length e2) with
  | false => rw [hLen] at hJ; nomatch hJ
  | true =>
    rw [hLen] at hJ
    cases hB1 : mirAbsEnvIsBot e1 with
    | true =>
      rw [hB1] at hJ
      injection hJ with hEq
      subst hEq
      exact h2
    | false =>
      rw [hB1] at hJ
      cases hB2 : mirAbsEnvIsBot e2 with
      | true => exact False.elim (mirAbsEnv_not_isBot hB2 h2)
      | false =>
        rw [hB2] at hJ
        have hG := mirAbsEnvJoinAux_get hJ
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

/-- Extract the initialized `AbsVal` of a `.uint u`, `.uintCopy u`, `.sint i`,
or `.sintCopy i` slot (matching `intTwin i = u`). -/
def MirAbsSlot.uintAbsVal? (u : UintTy) : MirAbsSlot → Option AbsVal
  | .uint u' a =>
    match uintTyBeq u u' && a.isInit with
    | true => some a
    | false => none
  | .uintCopy u' a _ =>
    match uintTyBeq u u' && a.isInit with
    | true => some a
    | false => none
  | .sint i' a =>
    match uintTyBeq u (intTwin i') && a.isInit with
    | true => some a
    | false => none
  | .sintCopy i' a _ =>
    match uintTyBeq u (intTwin i') && a.isInit with
    | true => some a
    | false => none
  | _ => none

/-- Extract the initialized `AbsVal` at local `r` in `env` for twin width `u`
(covering `.uint`, `.uintCopy`, `.sint`, and `.sintCopy` slots). -/
def envUintAbsVal? (env : MirAbsEnv) (r : Nat) (u : UintTy) : Option AbsVal :=
  match get? env r with
  | some s => s.uintAbsVal? u
  | none => none

/-- Refine a single slot at index `i` under a bit-pattern constraint on local
`r` of width `u`: updates index `r` itself (`.uint`, `.uintCopy`, `.sint`,
`.sintCopy`) and every live `.uintCopy` / `.sintCopy` alias rooted at `r`. -/
def refineUintSlotEntry (r : Nat) (u : UintTy) (f : AbsVal → AbsVal)
    (i : Nat) (s : MirAbsSlot) : MirAbsSlot :=
  match s with
  | .uint u' a =>
    match Nat.beq i r && uintTyBeq u u' && a.isInit with
    | true => .uint u (f a)
    | false => s
  | .uintCopy u' a src =>
    match (Nat.beq i r || Nat.beq src r) && uintTyBeq u u' && a.isInit with
    | true => .uintCopy u (f a) src
    | false => s
  | .sint i' a =>
    match Nat.beq i r && uintTyBeq u (intTwin i') && a.isInit with
    | true => .sint i' (f a)
    | false => s
  | .sintCopy i' a src =>
    match (Nat.beq i r || Nat.beq src r) && uintTyBeq u (intTwin i') && a.isInit with
    | true => .sintCopy i' (f a) src
    | false => s
  | _ => s

private def refineUintSlotAux (r : Nat) (u : UintTy) (f : AbsVal → AbsVal)
    (idx : Nat) : MirAbsEnv → MirAbsEnv
  | [] => []
  | s :: rest =>
    refineUintSlotEntry r u f idx s :: refineUintSlotAux r u f (idx + 1) rest

/-- Replace every initialized `.uint u` / `.uintCopy u` slot at local `r` and
every initialized `.uintCopy u` alias whose root is `r` by `f a`. -/
def refineUintSlot (env : MirAbsEnv) (r : Nat) (u : UintTy)
    (f : AbsVal → AbsVal) : MirAbsEnv :=
  refineUintSlotAux r u f 0 env

private theorem length_refineUintSlotAux (r : Nat) (u : UintTy)
    (f : AbsVal → AbsVal) :
    ∀ (idx : Nat) (env : MirAbsEnv),
      length (refineUintSlotAux r u f idx env) = length env
  | _, [] => rfl
  | idx, _ :: rest => congrArg Nat.succ (length_refineUintSlotAux r u f (idx + 1) rest)

private theorem get?_refineUintSlotAux (r : Nat) (u : UintTy)
    (f : AbsVal → AbsVal) :
    ∀ (idx : Nat) (env : MirAbsEnv) (i : Nat),
      get? (refineUintSlotAux r u f idx env) i =
        (get? env i).map (refineUintSlotEntry r u f (idx + i))
  | _, [], _ => rfl
  | idx, s :: rest, 0 => by
    simp only [refineUintSlotAux, get?, List.getElem?_cons_zero, Option.map,
      Nat.add_zero]
  | idx, s :: rest, i + 1 => by
    have h := get?_refineUintSlotAux r u f (idx + 1) rest i
    have hAdd : idx + 1 + i = idx + (i + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 i]
    rw [hAdd] at h
    exact h

/-- Soundness of `refineUintSlot` under a pointwise refinement hypothesis. -/
theorem refineUintSlot_sound {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {r : Nat} {u : UintTy} {f : AbsVal → AbsVal}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hRef : ∀ (a : AbsVal) (x : Nat), a.isInit = true →
      a.denote (uintWidth u) (some x) → localUintNat? locals r u = some x →
      (f a).denote (uintWidth u) (some x)) :
    mirAbsEnvDenote decls (refineUintSlot env r u f) locals := by
  refine ⟨Eq.trans (length_refineUintSlotAux r u f 0 env) hEnv.1, hEnv.2.1, ?_⟩
  intro i d s' cs hD hS' hCs
  unfold refineUintSlot at hS'
  rw [get?_refineUintSlotAux, Nat.zero_add] at hS'
  cases hGet : get? env i with
  | none => rw [hGet] at hS'; nomatch hS'
  | some s =>
    rw [hGet] at hS'
    injection hS' with hEqS
    subst hEqS
    have hDen := hEnv.2.2 i d s cs hD hGet hCs
    cases s with
    | uint u' a =>
      simp only [refineUintSlotEntry]
      cases hC : (Nat.beq i r && uintTyBeq u u' && a.isInit) with
      | false => exact hDen
      | true =>
        simp only
        have h12 := bool_and_true_left hC
        have hiR := Nat.eq_of_beq_eq_true (bool_and_true_left h12)
        have hu := uintTy_eq_of_beq (bool_and_true_right h12)
        have hInit := bool_and_true_right hC
        subst hiR
        subst hu
        cases uint_slot_extract hInit hDen with
        | intro sc hsc =>
          rw [hsc.1] at hCs ⊢
          exact ⟨hDen.1, hsc.2.1, hRef a sc.bits hInit hsc.2.2
            (localUintNat?_of_get? hCs hsc.2.1)⟩
    | uintCopy u' a src =>
      simp only [refineUintSlotEntry]
      cases hC : ((Nat.beq i r || Nat.beq src r) && uintTyBeq u u' && a.isInit) with
      | false => exact hDen
      | true =>
        simp only
        have h12 := bool_and_true_left hC
        have hOr := bool_and_true_left h12
        have hu := uintTy_eq_of_beq (bool_and_true_right h12)
        have hInit := bool_and_true_right hC
        subst hu
        cases uint_slot_extract hInit (uintCopy_denote_uint hDen) with
        | intro sc hsc =>
          rw [hsc.1] at hDen hCs ⊢
          have hLocR : localUintNat? locals r u = some sc.bits := by
            cases hIR : Nat.beq i r with
            | true =>
              have hiR := Nat.eq_of_beq_eq_true hIR
              subst hiR
              exact localUintNat?_of_get? hCs hsc.2.1
            | false =>
              rw [hIR, Bool.false_or] at hOr
              have hSrcR := Nat.eq_of_beq_eq_true hOr
              subst hSrcR
              exact hDen.2.2.2
          exact ⟨hDen.1, hsc.2.1, hRef a sc.bits hInit hsc.2.2 hLocR,
            hDen.2.2.2⟩
    | sint i' a =>
      simp only [refineUintSlotEntry]
      cases hC : (Nat.beq i r && uintTyBeq u (intTwin i') && a.isInit) with
      | false => exact hDen
      | true =>
        simp only
        have h12 := bool_and_true_left hC
        have hiR := Nat.eq_of_beq_eq_true (bool_and_true_left h12)
        have hu := uintTy_eq_of_beq (bool_and_true_right h12)
        have hInit := bool_and_true_right hC
        subst hiR
        subst hu
        cases sint_slot_extract hInit hDen with
        | intro sc hsc =>
          rw [hsc.1] at hCs ⊢
          exact ⟨hDen.1, hsc.2.1, hRef a sc.bits hInit hsc.2.2
            (localUintNat?_of_get? hCs hsc.2.1)⟩
    | sintCopy i' a src =>
      simp only [refineUintSlotEntry]
      cases hC :
          ((Nat.beq i r || Nat.beq src r) && uintTyBeq u (intTwin i') &&
            a.isInit) with
      | false => exact hDen
      | true =>
        simp only
        have h12 := bool_and_true_left hC
        have hOr := bool_and_true_left h12
        have hu := uintTy_eq_of_beq (bool_and_true_right h12)
        have hInit := bool_and_true_right hC
        subst hu
        cases sint_slot_extract hInit (sintCopy_denote_sint hDen) with
        | intro sc hsc =>
          rw [hsc.1] at hDen hCs ⊢
          have hLocR : localUintNat? locals r (intTwin i') = some sc.bits := by
            cases hIR : Nat.beq i r with
            | true =>
              have hiR := Nat.eq_of_beq_eq_true hIR
              subst hiR
              exact localUintNat?_of_get? hCs hsc.2.1
            | false =>
              rw [hIR, Bool.false_or] at hOr
              have hSrcR := Nat.eq_of_beq_eq_true hOr
              subst hSrcR
              exact hDen.2.2.2
          exact ⟨hDen.1, hsc.2.1, hRef a sc.bits hInit hsc.2.2 hLocR,
            hDen.2.2.2⟩
    | top | dead | bool _ | unit _ | uintBoolPair _ _ _ | sintBoolPair _ _ _ =>
      exact hDen

/-- Concrete scalar of local `r` behind an initialized `.uint`, `.uintCopy`,
`.sint`, or `.sintCopy` slot of twin width `u`. -/
theorem env_uintAbsVal?_extract {decls : List LocalDecl} {env : MirAbsEnv}
    {locals : List LocalSlot} {r : Nat} {u : UintTy} {a : AbsVal}
    (hEnv : mirAbsEnvDenote decls env locals)
    (hGet : envUintAbsVal? env r u = some a) :
    a.isInit = true ∧
    ∃ sc d, get? locals r = some (.init (.scalar sc)) ∧
      get? decls r = some d ∧
      (d.ty.kind = .uint u ∨ ∃ i', intTwin i' = u ∧ d.ty.kind = .int i') ∧
      sc.sizeBytes = uintBytes u ∧ a.denote (uintWidth u) (some sc.bits) ∧
      localUintNat? locals r u = some sc.bits := by
  unfold envUintAbsVal? at hGet
  cases hS : get? env r with
  | none => rw [hS] at hGet; nomatch hGet
  | some s =>
    rw [hS] at hGet
    cases mirAbsEnv_lookup hEnv hS with
    | intro d hd =>
      cases hd with
      | intro cs hcs =>
        cases s with
        | uint u' a' =>
          simp only [MirAbsSlot.uintAbsVal?] at hGet
          cases hC : (uintTyBeq u u' && a'.isInit) with
          | false => rw [hC] at hGet; nomatch hGet
          | true =>
            rw [hC] at hGet
            injection hGet with hEqA
            subst hEqA
            have hu := uintTy_eq_of_beq (bool_and_true_left hC)
            have hInit := bool_and_true_right hC
            subst hu
            cases uint_slot_extract hInit hcs.2.2 with
            | intro sc hsc =>
              have hL : get? locals r = some (.init (.scalar sc)) := by
                rw [hcs.2.1, hsc.1]
              exact ⟨hInit, sc, d, hL, hcs.1, Or.inl hcs.2.2.1, hsc.2.1, hsc.2.2,
                localUintNat?_of_get? hL hsc.2.1⟩
        | uintCopy u' a' src =>
          simp only [MirAbsSlot.uintAbsVal?] at hGet
          cases hC : (uintTyBeq u u' && a'.isInit) with
          | false => rw [hC] at hGet; nomatch hGet
          | true =>
            rw [hC] at hGet
            injection hGet with hEqA
            subst hEqA
            have hu := uintTy_eq_of_beq (bool_and_true_left hC)
            have hInit := bool_and_true_right hC
            subst hu
            cases uint_slot_extract hInit (uintCopy_denote_uint hcs.2.2) with
            | intro sc hsc =>
              have hL : get? locals r = some (.init (.scalar sc)) := by
                rw [hcs.2.1, hsc.1]
              exact ⟨hInit, sc, d, hL, hcs.1, Or.inl hcs.2.2.1, hsc.2.1, hsc.2.2,
                localUintNat?_of_get? hL hsc.2.1⟩
        | sint i' a' =>
          simp only [MirAbsSlot.uintAbsVal?] at hGet
          cases hC : (uintTyBeq u (intTwin i') && a'.isInit) with
          | false => rw [hC] at hGet; nomatch hGet
          | true =>
            rw [hC] at hGet
            injection hGet with hEqA
            subst hEqA
            have hu := uintTy_eq_of_beq (bool_and_true_left hC)
            have hInit := bool_and_true_right hC
            subst hu
            cases sint_slot_extract hInit hcs.2.2 with
            | intro sc hsc =>
              have hL : get? locals r = some (.init (.scalar sc)) := by
                rw [hcs.2.1, hsc.1]
              exact ⟨hInit, sc, d, hL, hcs.1, Or.inr ⟨i', rfl, hcs.2.2.1⟩,
                hsc.2.1, hsc.2.2, localUintNat?_of_get? hL hsc.2.1⟩
        | sintCopy i' a' src =>
          simp only [MirAbsSlot.uintAbsVal?] at hGet
          cases hC : (uintTyBeq u (intTwin i') && a'.isInit) with
          | false => rw [hC] at hGet; nomatch hGet
          | true =>
            rw [hC] at hGet
            injection hGet with hEqA
            subst hEqA
            have hu := uintTy_eq_of_beq (bool_and_true_left hC)
            have hInit := bool_and_true_right hC
            subst hu
            cases sint_slot_extract hInit (sintCopy_denote_sint hcs.2.2) with
            | intro sc hsc =>
              have hL : get? locals r = some (.init (.scalar sc)) := by
                rw [hcs.2.1, hsc.1]
              exact ⟨hInit, sc, d, hL, hcs.1, Or.inr ⟨i', rfl, hcs.2.2.1⟩,
                hsc.2.1, hsc.2.2, localUintNat?_of_get? hL hsc.2.1⟩
        | top | dead | bool _ | unit _ | uintBoolPair _ _ _ | sintBoolPair _ _ _ =>
          nomatch hGet

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

/-- `AbsVal.refineSleConst` is sound for every bound (out-of-range bounds
leave `a` unchanged). -/
theorem absVal_refineSleConst_sound_any {w x boundBits : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x))
    (hai : a.isInit = true)
    (hSle : signedBias w x ≤ signedBias w boundBits) :
    (AbsVal.refineSleConst w a boundBits).denote w (some x) := by
  cases hB : Nat.blt boundBits (modPow2 w) with
  | true => exact absVal_refineSleConst_sound hw ha hai (lt_of_blt_true hB) hSle
  | false =>
    dsimp only [AbsVal.refineSleConst]
    rw [hw, hai, hB]
    exact ha

/-- `AbsVal.refineSgtConst` is sound for every bound (out-of-range bounds
leave `a` unchanged). -/
theorem absVal_refineSgtConst_sound_any {w x boundBits : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x))
    (hai : a.isInit = true)
    (hSgt : signedBias w boundBits < signedBias w x) :
    (AbsVal.refineSgtConst w a boundBits).denote w (some x) := by
  cases hB : Nat.blt boundBits (modPow2 w) with
  | true => exact absVal_refineSgtConst_sound hw ha hai (lt_of_blt_true hB) hSgt
  | false =>
    dsimp only [AbsVal.refineSgtConst]
    rw [hw, hai, hB]
    exact ha

/-- Tightens an upper bound `hi` downward to the largest `hi' ≤ hi` satisfying
`sc` (`none` if no non-negative `x ≤ hi` satisfies `sc`). -/
def tightHiByCongNat (hi : Nat) : StridedCong → Option Nat
  | .bot => none
  | .top => some hi
  | .cong m r =>
    match Nat.ble 1 m && Nat.blt r m with
    | false => some hi
    | true =>
      let rem := hi % m
      let delta :=
        match Nat.ble r rem with
        | true => rem - r
        | false => rem + m - r
      match Nat.ble delta hi with
      | true => some (hi - delta)
      | false => none

/-- Soundness and completeness of `tightHiByCongNat`: any concrete witness
`x ≤ hi` satisfying `sc` guarantees `some hi'` with `x ≤ hi' ≤ hi`. -/
theorem tightHiByCongNat_sound {hi x : Nat} {sc : StridedCong}
    (hLe : x ≤ hi) (hSc : sc.denote x) :
    ∃ hi', tightHiByCongNat hi sc = some hi' ∧ x ≤ hi' ∧ hi' ≤ hi := by
  cases sc with
  | bot => exact False.elim hSc
  | top => exact ⟨hi, rfl, hLe, Nat.le_refl hi⟩
  | cong m r =>
    have hm : 1 ≤ m := hSc.1
    have hmPos : 0 < m := hm
    have hr : r < m := hSc.2.1
    have hxMod : x % m = r := hSc.2.2
    have hWf : (Nat.ble 1 m && Nat.blt r m) = true := by
      rw [Nat.ble_eq_true_of_le hm, blt_true_of_lt hr]; rfl
    have hXEq : m * (x / m) + r = x := by
      have h := Nat.div_add_mod x m
      rw [hxMod] at h
      exact h
    have hHiEq : m * (hi / m) + hi % m = hi := Nat.div_add_mod hi m
    have hRemLt : hi % m < m := Nat.mod_lt hi hmPos
    unfold tightHiByCongNat
    dsimp only
    rw [hWf]
    dsimp only
    cases hR : Nat.ble r (hi % m) with
    | true =>
      have hRLe : r ≤ hi % m := Nat.le_of_ble_eq_true hR
      have hDeltaLe : hi % m - r ≤ hi :=
        Nat.le_trans (Nat.sub_le _ _)
          (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hHiEq))
      rw [Nat.ble_eq_true_of_le hDeltaLe]
      refine ⟨hi - (hi % m - r), rfl, ?_, Nat.sub_le _ _⟩
      have hHiSub : hi - (hi % m - r) = m * (hi / m) + r := by
        calc hi - (hi % m - r)
            = m * (hi / m) + hi % m - (hi % m - r) := congrArg (· - _) hHiEq.symm
          _ = m * (hi / m) + (hi % m - (hi % m - r)) := Nat.add_sub_assoc (Nat.sub_le _ _) _
          _ = m * (hi / m) + r := congrArg (m * (hi / m) + ·) (Nat.sub_sub_self hRLe)
      rw [hHiSub]
      have hQLe : x / m ≤ hi / m := by
        cases Nat.lt_or_ge (hi / m) (x / m) with
        | inr h => exact h
        | inl hGt =>
          have hStep : m * (hi / m) + m ≤ m * (x / m) := by
            rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left m hGt
          have hLt : hi < m * (hi / m) + m :=
            Nat.lt_of_le_of_lt (Nat.le_of_eq hHiEq.symm)
              (Nat.add_lt_add_left hRemLt (m * (hi / m)))
          have hLeX : m * (x / m) ≤ x :=
            Nat.le_trans (Nat.le_add_right (m * (x / m)) r) (Nat.le_of_eq hXEq)
          exact False.elim
            (Nat.not_le_of_gt (Nat.lt_of_lt_of_le hLt (Nat.le_trans hStep hLeX)) hLe)
      exact hXEq ▸ Nat.add_le_add_right (Nat.mul_le_mul_left m hQLe) r
    | false =>
      have hRemLtR : hi % m < r := by
        cases Nat.lt_or_ge (hi % m) r with
        | inl h => exact h
        | inr h => rw [Nat.ble_eq_true_of_le h] at hR; nomatch hR
      cases hQ : hi / m with
      | zero =>
        rw [hQ, Nat.mul_zero, Nat.zero_add] at hHiEq
        have hRLex : r ≤ x := hXEq ▸ Nat.le_add_left r (m * (x / m))
        have hHiLtX : hi < x :=
          Nat.lt_of_lt_of_le (hHiEq ▸ hRemLtR) hRLex
        exact False.elim (Nat.not_le_of_gt hHiLtX hLe)
      | succ q' =>
        have hHiEq' : m * q' + (hi % m + m) = hi := by
          rw [hQ, Nat.mul_succ, Nat.add_assoc, Nat.add_comm m (hi % m)] at hHiEq
          exact hHiEq
        have hRLeAdd : r ≤ hi % m + m :=
          Nat.le_trans (Nat.le_of_lt hr) (Nat.le_add_left _ _)
        have hDeltaLe : hi % m + m - r ≤ hi :=
          Nat.le_trans (Nat.sub_le _ _)
            (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hHiEq'))
        rw [Nat.ble_eq_true_of_le hDeltaLe]
        refine ⟨hi - (hi % m + m - r), rfl, ?_, Nat.sub_le _ _⟩
        have hHiSub : hi - (hi % m + m - r) = m * q' + r := by
          calc hi - (hi % m + m - r)
              = m * q' + (hi % m + m) - (hi % m + m - r) := congrArg (· - _) hHiEq'.symm
            _ = m * q' + ((hi % m + m) - (hi % m + m - r)) := Nat.add_sub_assoc (Nat.sub_le _ _) _
            _ = m * q' + r := congrArg (m * q' + ·) (Nat.sub_sub_self hRLeAdd)
        rw [hHiSub]
        have hQLe : x / m ≤ q' := by
          cases Nat.lt_or_ge q' (x / m) with
          | inr h => exact h
          | inl hGt =>
            have hStep : m * (q' + 1) ≤ m * (x / m) := Nat.mul_le_mul_left m hGt
            have hHiLt : hi < m * (q' + 1) + r :=
              (hQ ▸ hHiEq) ▸ Nat.add_lt_add_left hRemLtR (m * (q' + 1))
            have hLeX : m * (q' + 1) + r ≤ x :=
              hXEq ▸ Nat.add_le_add_right hStep r
            exact False.elim (Nat.not_le_of_gt (Nat.lt_of_lt_of_le hHiLt hLeX) hLe)
        exact hXEq ▸ Nat.add_le_add_right (Nat.mul_le_mul_left m hQLe) r

/-- Adding or subtracting `halfModPow2 w` preserves residue modulo any divisor
`m` of `halfModPow2 w`. -/
theorem signedBias_mod_of_dvd_half {w x m : Nat} (hw : validWidth w = true)
    (hx : x < modPow2 w) (hDvd : halfModPow2 w % m = 0) :
    signedBias w x % m = x % m := by
  cases hLt : Nat.blt x (halfModPow2 w) with
  | true =>
    rw [signedBias_of_lt_half hw (lt_of_blt_true hLt), Nat.add_mod, hDvd,
      Nat.add_zero, Nat.mod_mod]
  | false =>
    have hGe : halfModPow2 w ≤ x := by
      cases Nat.lt_or_ge x (halfModPow2 w) with
      | inl h => rw [blt_true_of_lt h] at hLt; nomatch hLt
      | inr h => exact h
    rw [signedBias_of_ge_half hw hGe hx]
    have hEq : x % m = ((x - halfModPow2 w) + halfModPow2 w) % m := by
      rw [Nat.sub_add_cancel hGe]
    rw [hEq, Nat.add_mod, hDvd, Nat.add_zero, Nat.mod_mod]

/-- Transports a `StridedCong` on bit patterns `x` to biased coordinates
`signedBias w x` whenever its modulus divides `halfModPow2 w` (all power-of-two
strides `2^k ≤ 2^(w-1)`). -/
def congForSignedBias (w : Nat) : StridedCong → StridedCong
  | .cong m r =>
    match Nat.beq (halfModPow2 w % m) 0 with
    | true => .cong m r
    | false => .top
  | sc => sc

theorem congForSignedBias_sound {w x : Nat} {sc : StridedCong}
    (hw : validWidth w = true) (hx : x < modPow2 w) (hSc : sc.denote x) :
    (congForSignedBias w sc).denote (signedBias w x) := by
  cases sc with
  | bot => exact False.elim hSc
  | top => exact True.intro
  | cong m r =>
    unfold congForSignedBias
    dsimp only
    cases hDvd : Nat.beq (halfModPow2 w % m) 0 with
    | false => exact True.intro
    | true =>
      refine ⟨hSc.1, hSc.2.1, ?_⟩
      show signedBias w x % m = r
      rw [signedBias_mod_of_dvd_half hw hx (Nat.eq_of_beq_eq_true hDvd)]
      exact hSc.2.2

/-- Tightens an unsigned `x ≤ bound` refinement using `a.sc` congruence before
intersecting via `AbsVal.refineUleConst`. -/
def refineUleConstWithCong (w : Nat) (a : AbsVal) (bound : Nat) : AbsVal :=
  match tightHiByCongNat bound a.sc with
  | none => AbsVal.bot
  | some bound' => AbsVal.refineUleConst w a bound'

theorem refineUleConstWithCong_sound {w x bound : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x))
    (hai : a.isInit = true) (hLe : x ≤ bound) :
    (refineUleConstWithCong w a bound).denote w (some x) := by
  have haE := absVal_some_elim ha
  cases tightHiByCongNat_sound hLe haE.2.2.2 with
  | intro bound' hb =>
    unfold refineUleConstWithCong
    rw [hb.1]
    exact absVal_refineUleConst_sound hw ha hai hb.2.1

/-- Tightens an unsigned `bound < x` refinement using `a.sc` congruence before
intersecting via `AbsVal.refineUgtConst`. -/
def refineUgtConstWithCong (w : Nat) (a : AbsVal) (bound : Nat) : AbsVal :=
  match validWidth w && a.isInit with
  | false => AbsVal.refineUgtConst w a bound
  | true =>
    let M := modPow2 w
    match Nat.blt (bound + 1) M with
    | false => AbsVal.bot
    | true =>
      match tightLoByCong (bound + 1) (M - 1) a.sc with
      | none => AbsVal.bot
      | some lo' =>
        match Nat.blt 0 lo' with
        | true => AbsVal.refineUgtConst w a (lo' - 1)
        | false => AbsVal.refineUgtConst w a bound

theorem refineUgtConstWithCong_sound {w x bound : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x))
    (hai : a.isInit = true) (hGt : bound < x) :
    (refineUgtConstWithCong w a bound).denote w (some x) := by
  have haE := absVal_some_elim ha
  have hB1Lt : bound + 1 < modPow2 w := Nat.lt_of_le_of_lt hGt haE.1
  unfold refineUgtConstWithCong
  rw [hw, hai]
  dsimp only
  rw [blt_true_of_lt hB1Lt]
  dsimp only
  have hNoNone := tightLoByCong_none_impossible hGt (Nat.le_sub_one_of_lt haE.1)
    haE.2.2.2
  cases hLo : tightLoByCong (bound + 1) (modPow2 w - 1) a.sc with
  | none => exact False.elim (hNoNone hLo)
  | some lo' =>
    dsimp only
    have hLoLe : lo' ≤ x := tightLoByCong_sound hGt haE.2.2.2 hLo
    cases hPos : Nat.blt 0 lo' with
    | false => exact absVal_refineUgtConst_sound hw ha hai hGt
    | true =>
      exact absVal_refineUgtConst_sound hw ha hai
        (Nat.lt_of_lt_of_le (Nat.sub_lt (lt_of_blt_true hPos) (Nat.zero_lt_succ 0))
          hLoLe)

/-- Tightens a signed `signedBias w x ≤ signedBias w boundBits` refinement
using `a.sc` congruence (in biased coordinates) before intersecting via
`AbsVal.refineSleConst`. -/
def refineSleConstWithCong (w : Nat) (a : AbsVal) (boundBits : Nat) : AbsVal :=
  match validWidth w && a.isInit && Nat.blt boundBits (modPow2 w) with
  | false => AbsVal.refineSleConst w a boundBits
  | true =>
    let sb := signedBias w boundBits
    match tightHiByCongNat sb (congForSignedBias w a.sc) with
    | none => AbsVal.bot
    | some sb' => AbsVal.refineSleConst w a (signedBias w sb')

theorem refineSleConstWithCong_sound {w x boundBits : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x))
    (hai : a.isInit = true)
    (hSle : signedBias w x ≤ signedBias w boundBits) :
    (refineSleConstWithCong w a boundBits).denote w (some x) := by
  unfold refineSleConstWithCong
  rw [hw, hai]
  cases hB : Nat.blt boundBits (modPow2 w) with
  | false => exact absVal_refineSleConst_sound_any hw ha hai hSle
  | true =>
    dsimp only
    have haE := absVal_some_elim ha
    have hScB := congForSignedBias_sound hw haE.1 haE.2.2.2
    cases tightHiByCongNat_sound hSle hScB with
    | intro sb' hsb' =>
      rw [hsb'.1]
      dsimp only
      have hSb'Lt : sb' < modPow2 w :=
        Nat.lt_of_le_of_lt hsb'.2.2 (signedBias_lt boundBits)
      apply absVal_refineSleConst_sound_any hw ha hai
      rw [signedBias_signedBias hw hSb'Lt]
      exact hsb'.2.1

/-- Tightens a signed `signedBias w boundBits < signedBias w x` refinement
using `a.sc` congruence (in biased coordinates) before intersecting via
`AbsVal.refineSgtConst`. -/
def refineSgtConstWithCong (w : Nat) (a : AbsVal) (boundBits : Nat) : AbsVal :=
  match validWidth w && a.isInit && Nat.blt boundBits (modPow2 w) with
  | false => AbsVal.refineSgtConst w a boundBits
  | true =>
    let M := modPow2 w
    let sb := signedBias w boundBits
    match Nat.blt (sb + 1) M with
    | false => AbsVal.bot
    | true =>
      match tightLoByCong (sb + 1) (M - 1) (congForSignedBias w a.sc) with
      | none => AbsVal.bot
      | some lo' =>
        match Nat.blt 0 lo' && Nat.blt lo' M with
        | true => AbsVal.refineSgtConst w a (signedBias w (lo' - 1))
        | false => AbsVal.refineSgtConst w a boundBits

theorem refineSgtConstWithCong_sound {w x boundBits : Nat} {a : AbsVal}
    (hw : validWidth w = true) (ha : a.denote w (some x))
    (hai : a.isInit = true)
    (hSgt : signedBias w boundBits < signedBias w x) :
    (refineSgtConstWithCong w a boundBits).denote w (some x) := by
  unfold refineSgtConstWithCong
  rw [hw, hai]
  cases hB : Nat.blt boundBits (modPow2 w) with
  | false => exact absVal_refineSgtConst_sound_any hw ha hai hSgt
  | true =>
    dsimp only
    have haE := absVal_some_elim ha
    have hSbXLt : signedBias w x < modPow2 w := signedBias_lt x
    have hSb1Lt : signedBias w boundBits + 1 < modPow2 w :=
      Nat.lt_of_le_of_lt hSgt hSbXLt
    rw [blt_true_of_lt hSb1Lt]
    dsimp only
    have hScB := congForSignedBias_sound hw haE.1 haE.2.2.2
    have hNoNone := tightLoByCong_none_impossible hSgt
      (Nat.le_sub_one_of_lt hSbXLt) hScB
    cases hLo : tightLoByCong (signedBias w boundBits + 1) (modPow2 w - 1)
        (congForSignedBias w a.sc) with
    | none => exact False.elim (hNoNone hLo)
    | some lo' =>
      dsimp only
      have hLoLe : lo' ≤ signedBias w x := tightLoByCong_sound hSgt hScB hLo
      cases hOk : (Nat.blt 0 lo' && Nat.blt lo' (modPow2 w)) with
      | false => exact absVal_refineSgtConst_sound_any hw ha hai hSgt
      | true =>
        have hPos : 0 < lo' := lt_of_blt_true (bool_and_true_left hOk)
        have hPredLtLo : lo' - 1 < lo' := Nat.sub_lt hPos (Nat.zero_lt_succ 0)
        have hPredLtM : lo' - 1 < modPow2 w :=
          Nat.lt_trans hPredLtLo (lt_of_blt_true (bool_and_true_right hOk))
        apply absVal_refineSgtConst_sound_any hw ha hai
        rw [signedBias_signedBias hw hPredLtM]
        exact Nat.lt_of_lt_of_le hPredLtLo hLoLe

/-- Refine `env` using `RelGuard` `g` assuming boolean outcome `branchVal`.
Register-register guards refine both operands symmetrically (across `.uint`,
`.uintCopy`, `.sint`, and `.sintCopy` slots, propagating refinements to copy
aliases), `.ueqReg` meets both operands via `AbsVal.meetInit`,
self-contradictions (`l < l`, `l ≠ l`) yield `AbsVal.bot`, `.uneConst` /
`.sneConst` refine via ring-complement intersection
(`AbsVal.refineUneConst`), and the signed constant guards `.sleConst` /
`.sgtConst` / `.seqConst` refine `.sint` / `.sintCopy` slots (and aliases)
through `refineSleConstWithCong` / `refineSgtConstWithCong` (congruence-aware
tightening over `AbsVal.refineSleConst` / `AbsVal.refineSgtConst` in biased
signed coordinates) and `AbsVal.refineEqConst`; `.uleConst` / `.ugtConst`
similarly apply congruence-aware tightening (`refineUleConstWithCong` /
`refineUgtConstWithCong`) so stride-aligned loops verify across arbitrary
non-power-of-two, negative, and sign-straddling bounds. -/
def refineEnvByGuard (env : MirAbsEnv) (g : RelGuard) (branchVal : Bool) :
    MirAbsEnv :=
  let eff :=
    match branchVal with
    | true => g
    | false => g.negate
  match eff with
  | .none => env
  | .uleConst r u bound =>
    refineUintSlot env r u (fun a => refineUleConstWithCong (uintWidth u) a bound)
  | .ugtConst r u bound =>
    refineUintSlot env r u (fun a => refineUgtConstWithCong (uintWidth u) a bound)
  | .ultReg l r u =>
    match Nat.beq l r with
    | true => refineUintSlot env l u (fun _ => AbsVal.bot)
    | false =>
      let env₁ :=
        match envUintAbsVal? env r u with
        | some ar =>
          refineUintSlot env l u
            (fun al => AbsVal.refineBltReg (uintWidth u) al ar)
        | none => env
      match envUintAbsVal? env₁ l u with
      | some al =>
        match al.lbound? with
        | some loL =>
          refineUintSlot env₁ r u
            (fun ar => AbsVal.refineUgtConst (uintWidth u) ar loL)
        | none => env₁
      | none => env₁
  | .ugeReg l r u =>
    let env₁ :=
      match envUintAbsVal? env r u with
      | some ar =>
        refineUintSlot env l u
          (fun al => AbsVal.refineBgeReg (uintWidth u) al ar)
      | none => env
    match envUintAbsVal? env₁ l u with
    | some al =>
      match al.ubound? with
      | some hiL =>
        refineUintSlot env₁ r u
          (fun ar => AbsVal.refineUleConst (uintWidth u) ar hiL)
      | none => env₁
    | none => env₁
  | .ueqConst r u val =>
    refineUintSlot env r u (fun a => AbsVal.refineEqConst (uintWidth u) a val)
  | .uneConst r u val =>
    refineUintSlot env r u (fun a => AbsVal.refineUneConst (uintWidth u) a val)
  | .ueqReg l r u =>
    match envUintAbsVal? env l u, envUintAbsVal? env r u with
    | some al, some ar =>
      let m := AbsVal.meetInit (uintWidth u) al ar
      let env₁ := refineUintSlot env l u (fun _ => m)
      refineUintSlot env₁ r u (fun _ => m)
    | _, _ => env
  | .uneReg l r u =>
    match Nat.beq l r with
    | true => refineUintSlot env l u (fun _ => AbsVal.bot)
    | false =>
      let env₁ :=
        match envUintAbsVal? env r u with
        | some ar =>
          match ar.exactVal? (uintWidth u) with
          | some v =>
            refineUintSlot env l u
              (fun al => AbsVal.refineUneConst (uintWidth u) al v)
          | none => env
        | none => env
      match envUintAbsVal? env₁ l u with
      | some al =>
        match al.exactVal? (uintWidth u) with
        | some v =>
          refineUintSlot env₁ r u
            (fun ar => AbsVal.refineUneConst (uintWidth u) ar v)
        | none => env₁
      | none => env₁
  | .sleConst r i boundBits =>
    refineUintSlot env r (intTwin i)
      (fun a => refineSleConstWithCong (uintWidth (intTwin i)) a boundBits)
  | .sgtConst r i boundBits =>
    refineUintSlot env r (intTwin i)
      (fun a => refineSgtConstWithCong (uintWidth (intTwin i)) a boundBits)
  | .seqConst r i val =>
    refineUintSlot env r (intTwin i)
      (fun a => AbsVal.refineEqConst (uintWidth (intTwin i)) a val)
  | .sneConst r i val =>
    refineUintSlot env r (intTwin i)
      (fun a => AbsVal.refineUneConst (uintWidth (intTwin i)) a val)

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
  | sleConst r i boundBits =>
    apply refineUintSlot_sound hEnv
    intro a x hInit ha hx
    exact refineSleConstWithCong_sound (uintWidth_valid (intTwin i)) ha hInit
      ((hEff x hx).mp rfl)
  | sgtConst r i boundBits =>
    apply refineUintSlot_sound hEnv
    intro a x hInit ha hx
    exact refineSgtConstWithCong_sound (uintWidth_valid (intTwin i)) ha hInit
      ((hEff x hx).mp rfl)
  | seqConst r i val =>
    apply refineUintSlot_sound hEnv
    intro a x hInit ha hx
    exact absVal_refineEqConst_sound (uintWidth_valid (intTwin i)) ha hInit
      ((hEff x hx).mp rfl)
  | sneConst r i val =>
    apply refineUintSlot_sound hEnv
    intro a x hInit ha hx
    exact absVal_refineUneConst_sound (uintWidth_valid (intTwin i)) ha hInit
      ((hEff x hx).mp rfl)
  | uneConst r u val =>
    apply refineUintSlot_sound hEnv
    intro a x hInit ha hx
    exact absVal_refineUneConst_sound (uintWidth_valid u) ha hInit
      ((hEff x hx).mp rfl)
  | uleConst r u bound =>
    apply refineUintSlot_sound hEnv
    intro a x hInit ha hx
    exact refineUleConstWithCong_sound (uintWidth_valid u) ha hInit
      ((hEff x hx).mp rfl)
  | ugtConst r u bound =>
    apply refineUintSlot_sound hEnv
    intro a x hInit ha hx
    exact refineUgtConstWithCong_sound (uintWidth_valid u) ha hInit
      ((hEff x hx).mp rfl)
  | ueqConst r u val =>
    apply refineUintSlot_sound hEnv
    intro a x hInit ha hx
    exact absVal_refineEqConst_sound (uintWidth_valid u) ha hInit
      ((hEff x hx).mp rfl)
  | ultReg l r u =>
    dsimp only
    cases hEqLR : Nat.beq l r with
    | true =>
      have hLR := Nat.eq_of_beq_eq_true hEqLR
      subst hLR
      apply refineUintSlot_sound hEnv
      intro a x _ _ hx
      exact False.elim (Nat.lt_irrefl x ((hEff x x hx hx).mp rfl))
    | false =>
      dsimp only
      let env₁ :=
        match envUintAbsVal? env r u with
        | some ar =>
          refineUintSlot env l u
            (fun al => AbsVal.refineBltReg (uintWidth u) al ar)
        | none => env
      have hEnv1 : mirAbsEnvDenote decls env₁ locals := by
        dsimp only [env₁]
        cases hGet : envUintAbsVal? env r u with
        | none => exact hEnv
        | some ar =>
          have hEx := env_uintAbsVal?_extract hEnv hGet
          cases hEx.2 with
          | intro scR hR =>
            cases hR with
            | intro dR hR =>
              apply refineUintSlot_sound hEnv
              intro al x hInitL hal hx
              exact absVal_refineBltReg_sound (uintWidth_valid u) hal
                hR.2.2.2.2.1 hInitL hEx.1
                ((hEff x scR.bits hx hR.2.2.2.2.2).mp rfl)
      change mirAbsEnvDenote decls
        (match envUintAbsVal? env₁ l u with
         | some al =>
           match al.lbound? with
           | some loL =>
             refineUintSlot env₁ r u
               (fun ar => AbsVal.refineUgtConst (uintWidth u) ar loL)
           | none => env₁
         | none => env₁) locals
      cases hGetL : envUintAbsVal? env₁ l u with
      | none => exact hEnv1
      | some al =>
        dsimp only
        cases hLo : al.lbound? with
        | none => exact hEnv1
        | some loL =>
          have hEx := env_uintAbsVal?_extract hEnv1 hGetL
          cases hEx.2 with
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
  | ugeReg l r u =>
    dsimp only
    let env₁ :=
      match envUintAbsVal? env r u with
      | some ar =>
        refineUintSlot env l u
          (fun al => AbsVal.refineBgeReg (uintWidth u) al ar)
      | none => env
    have hEnv1 : mirAbsEnvDenote decls env₁ locals := by
      dsimp only [env₁]
      cases hGet : envUintAbsVal? env r u with
      | none => exact hEnv
      | some ar =>
        have hEx := env_uintAbsVal?_extract hEnv hGet
        cases hEx.2 with
        | intro scR hR =>
          cases hR with
          | intro dR hR =>
            apply refineUintSlot_sound hEnv
            intro al x hInitL hal hx
            exact absVal_refineBgeReg_sound (uintWidth_valid u) hal
              hR.2.2.2.2.1 hInitL hEx.1
              ((hEff x scR.bits hx hR.2.2.2.2.2).mp rfl)
    change mirAbsEnvDenote decls
      (match envUintAbsVal? env₁ l u with
       | some al =>
         match al.ubound? with
         | some hiL =>
           refineUintSlot env₁ r u
             (fun ar => AbsVal.refineUleConst (uintWidth u) ar hiL)
         | none => env₁
       | none => env₁) locals
    cases hGetL : envUintAbsVal? env₁ l u with
    | none => exact hEnv1
    | some al =>
      dsimp only
      cases hHi : al.ubound? with
      | none => exact hEnv1
      | some hiL =>
        have hEx := env_uintAbsVal?_extract hEnv1 hGetL
        cases hEx.2 with
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
  | ueqReg l r u =>
    dsimp only
    cases hGetL : envUintAbsVal? env l u with
    | none => exact hEnv
    | some al =>
      cases hGetR : envUintAbsVal? env r u with
      | none => exact hEnv
      | some ar =>
        have hExL := env_uintAbsVal?_extract hEnv hGetL
        have hExR := env_uintAbsVal?_extract hEnv hGetR
        cases hExL.2 with
        | intro scL hL =>
          cases hL with
          | intro dL hL =>
            cases hExR.2 with
            | intro scR hR =>
              cases hR with
              | intro dR hR =>
                have hEqBits : scL.bits = scR.bits :=
                  (hEff scL.bits scR.bits hL.2.2.2.2.2 hR.2.2.2.2.2).mp rfl
                have hMeetL : (AbsVal.meetInit (uintWidth u) al ar).denote
                    (uintWidth u) (some scL.bits) := by
                  apply absVal_meetInit_sound (uintWidth_valid u) hExL.1 hExR.1
                    hL.2.2.2.2.1
                  rw [hEqBits]
                  exact hR.2.2.2.2.1
                have hEnv1 : mirAbsEnvDenote decls
                    (refineUintSlot env l u
                      (fun _ => AbsVal.meetInit (uintWidth u) al ar)) locals := by
                  apply refineUintSlot_sound hEnv
                  intro _ x _ _ hx
                  rw [hL.2.2.2.2.2] at hx
                  injection hx with hx
                  subst hx
                  exact hMeetL
                apply refineUintSlot_sound hEnv1
                intro _ y _ _ hy
                rw [hR.2.2.2.2.2] at hy
                injection hy with hy
                subst hy
                rw [← hEqBits]
                exact hMeetL
  | uneReg l r u =>
    dsimp only
    cases hEqLR : Nat.beq l r with
    | true =>
      have hLR := Nat.eq_of_beq_eq_true hEqLR
      subst hLR
      apply refineUintSlot_sound hEnv
      intro a x _ _ hx
      exact False.elim ((hEff x x hx hx).mp rfl rfl)
    | false =>
      dsimp only
      let env₁ :=
        match envUintAbsVal? env r u with
        | some ar =>
          match ar.exactVal? (uintWidth u) with
          | some v =>
            refineUintSlot env l u
              (fun al => AbsVal.refineUneConst (uintWidth u) al v)
          | none => env
        | none => env
      have hEnv1 : mirAbsEnvDenote decls env₁ locals := by
        dsimp only [env₁]
        cases hGet : envUintAbsVal? env r u with
        | none => exact hEnv
        | some ar =>
          dsimp only
          cases hExV : ar.exactVal? (uintWidth u) with
          | none => exact hEnv
          | some v =>
            have hEx := env_uintAbsVal?_extract hEnv hGet
            cases hEx.2 with
            | intro scR hR =>
              cases hR with
              | intro dR hR =>
                have hvEq := (absVal_exactVal?_sound hExV hR.2.2.2.2.1).1
                injection hvEq with hvEq
                subst hvEq
                apply refineUintSlot_sound hEnv
                intro al x hInitL hal hx
                exact absVal_refineUneConst_sound (uintWidth_valid u) hal hInitL
                  ((hEff x scR.bits hx hR.2.2.2.2.2).mp rfl)
      change mirAbsEnvDenote decls
        (match envUintAbsVal? env₁ l u with
         | some al =>
           match al.exactVal? (uintWidth u) with
           | some v =>
             refineUintSlot env₁ r u
               (fun ar => AbsVal.refineUneConst (uintWidth u) ar v)
           | none => env₁
         | none => env₁) locals
      cases hGetL : envUintAbsVal? env₁ l u with
      | none => exact hEnv1
      | some al =>
        dsimp only
        cases hExV : al.exactVal? (uintWidth u) with
        | none => exact hEnv1
        | some v =>
          have hEx := env_uintAbsVal?_extract hEnv1 hGetL
          cases hEx.2 with
          | intro scL hL =>
            cases hL with
            | intro dL hL =>
              have hvEq := (absVal_exactVal?_sound hExV hL.2.2.2.2.1).1
              injection hvEq with hvEq
              subst hvEq
              apply refineUintSlot_sound hEnv1
              intro ar y hInitR har hy
              have hNe := (hEff scL.bits y hL.2.2.2.2.2 hy).mp rfl
              exact absVal_refineUneConst_sound (uintWidth_valid u) har hInitR
                (fun h => hNe h.symm)

end Anneal.AiPcc
