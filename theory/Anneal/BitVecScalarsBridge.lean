-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted
import Anneal.NatBitwise
import Anneal.BitVec
import Anneal.BitVecArith
import Anneal.LeBytes
import Anneal.ListChunks
import Anneal.Scalars
import Anneal.BitValidity
import Anneal.ByteCodec

namespace Anneal.BitVecScalarsBridge

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.BitValidity
open Anneal.ByteCodec

/-!
# Bridge from `Anneal.BitVec` / `BitVecArith` / `LeBytes` / `ListChunks` to MIR Scalars and Bytes

Connects the pure, width-parametric libraries ported from `google/zerocopy`
(`Anneal.NatBitwise`, `Anneal.BitVec`, `Anneal.BitVecArith`, `Anneal.LeBytes`,
`Anneal.ListChunks`) to the operational MIR semantics
(`Trusted.Rustc.V2026_06_01.MirSemantics.{Scalars,Bytes}`) and to the existing
verification stack (`Anneal.Scalars`, `Anneal.ByteCodec`, `Anneal.BitValidity`).

Naming discipline. `Anneal.BitVec` shadows 59 core `BitVec.*` names inside any
`namespace Anneal...`, so this module never opens `Anneal.BitVec`: ported names
are written `Anneal.BitVec.*` / `Anneal.BitVecArith.*` and core lemmas are written
`_root_.BitVec.*`. `Anneal.Scalars` is not opened either, so the unqualified
intrinsic loops (`ctlzBits`, `bswapLoop`, ...) always denote the `Trusted` copies
and the theory copies are written `Anneal.Scalars.*`.

Sections:
0. Notation bridges (`Nat.mod` vs `%`, ported operations vs core `BitVec`).
1. Width alignment between `BitVec (8 * sz)` and `BitVec (sz * 8)`.
2. Bitwise, shift, sign and two's-complement value bridges.
3. `evalBinOp` / `evalScalarBinOp` / `evalWrapping*` value bridges.
4. Disjoint-mask packing and bitfield extraction on scalars.
5. `ScalarTnum`, `ScalarRange`, `ScalarSRange` abstract-domain transfers.
6. Intrinsics (`ctlz`, `bswap`).
7. Little-endian byte serialization.
8. `bitVecLE` fixed-width codec.
9. Chunking, arrays and `BitValidity` transmutation.
10. Derived transfers: abstraction normalization, signed casts, `ctlz` from ranges.
-/

/-! ## 0. Notation Bridges -/

/-- `Nat.mod` (emitted by `Anneal.BitVec` / `BitVecArith` statements) is `%`. -/
theorem natMod_eq (a b : Nat) : Nat.mod a b = a % b := rfl

/-- `Nat.div` (emitted by `Anneal.BitVec` / `BitVecArith` statements) is `/`. -/
theorem natDiv_eq (a b : Nat) : Nat.div a b = a / b := rfl

/-- `Nat.pow` (emitted by `Anneal.BitVec` / `BitVecArith` statements) is `^`. -/
theorem natPow_eq (a b : Nat) : Nat.pow a b = a ^ b := rfl

/-- `Nat.mul` (emitted by `Trusted` definitions) is `*`. -/
theorem natMul_eq (a b : Nat) : Nat.mul a b = a * b := rfl

/-- `Nat.add` (emitted by `Trusted` definitions) is `+`. -/
theorem natAdd_eq (a b : Nat) : Nat.add a b = a + b := rfl

/-- `Nat.sub` (emitted by `Trusted` definitions) is `-`. -/
theorem natSub_eq (a b : Nat) : Nat.sub a b = a - b := rfl

/-- `Nat.land` is `&&&`. -/
theorem natLand_eq (a b : Nat) : Nat.land a b = a &&& b := rfl

/-- `Nat.lor` is `|||`. -/
theorem natLor_eq (a b : Nat) : Nat.lor a b = a ||| b := rfl

/-- `Nat.xor` is `^^^`. -/
theorem natXor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

/-- `Nat.shiftLeft` is `<<<`. -/
theorem natShiftLeft_eq (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl

/-- `Nat.shiftRight` is `>>>`. -/
theorem natShiftRight_eq (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl

/-- `Trusted.Sequence.length` is `List.length`. -/
theorem seqLength_eq {α : Type} (xs : List α) : Trusted.Sequence.length xs = xs.length := rfl

/-- The byte-width bit count `Nat.mul sz 8` used by `Trusted` is `8 * sz`. -/
theorem natMul_eight (sz : Nat) : Nat.mul sz 8 = 8 * sz := Nat.mul_comm sz 8

/-- Ported `and` is core `&&&`. -/
theorem and_eq_core {w : Nat} (x y : BitVec w) : Anneal.BitVec.and x y = x &&& y := rfl

/-- Ported `or` is core `|||`. -/
theorem or_eq_core {w : Nat} (x y : BitVec w) : Anneal.BitVec.or x y = x ||| y := rfl

/-- Ported `xor` is core `^^^`. -/
theorem xor_eq_core {w : Nat} (x y : BitVec w) : Anneal.BitVec.xor x y = x ^^^ y := rfl

/-- Ported `not` is core `~~~`. -/
theorem not_eq_core {w : Nat} (x : BitVec w) : Anneal.BitVec.not x = ~~~x := rfl

/-- Ported `shl` is core `<<<`. -/
theorem shl_eq_core {w : Nat} (x : BitVec w) (k : Nat) : Anneal.BitVec.shl x k = x <<< k := rfl

/-- Ported `ushr` is core `>>>`. -/
theorem ushr_eq_core {w : Nat} (x : BitVec w) (k : Nat) : Anneal.BitVec.ushr x k = x >>> k := rfl

/-- Ported `setWidth` is core `BitVec.setWidth`. -/
theorem setWidth_eq_core {w : Nat} (v : Nat) (x : BitVec w) :
    Anneal.BitVec.setWidth v x = _root_.BitVec.setWidth v x := rfl

/-- Ported `getLsbD` is core `BitVec.getLsbD`. -/
theorem getLsbD_eq_core {w : Nat} (x : BitVec w) (i : Nat) :
    Anneal.BitVec.getLsbD x i = _root_.BitVec.getLsbD x i := rfl

/-- Ported `msb` is core `BitVec.msb`. -/
theorem msb_eq_core {w : Nat} (x : BitVec w) :
    Anneal.BitVecArith.msb x = _root_.BitVec.msb x := rfl

/-- Ported `allOnes` is core `BitVec.allOnes`. -/
theorem allOnes_eq_core (w : Nat) : Anneal.BitVec.allOnes w = _root_.BitVec.allOnes w := rfl

/-- Ported arithmetic shift right agrees with core `BitVec.sshiftRight` at every width and shift. -/
theorem ashr_eq_core {w : Nat} (x : BitVec w) (k : Nat) :
    Anneal.BitVecArith.ashr x k = _root_.BitVec.sshiftRight x k := by
  apply _root_.BitVec.eq_of_getLsbD_eq
  intro i hi
  have h := Anneal.BitVecArith.getLsbD_ashr x k i
  rw [getLsbD_eq_core] at h
  rw [h, _root_.BitVec.getLsbD_sshiftRight, Nat.add_comm i k, msb_eq_core, getLsbD_eq_core]
  simp [hi, Nat.not_le.mpr hi]

/-- Ported sign extension agrees with core `BitVec.signExtend` at every pair of widths. -/
theorem signExtend_eq_core {w : Nat} (v : Nat) (x : BitVec w) :
    Anneal.BitVecArith.signExtend v x = _root_.BitVec.signExtend v x := by
  apply _root_.BitVec.eq_of_getLsbD_eq
  intro i hi
  have h := Anneal.BitVecArith.getLsbD_signExtend v x i
  rw [getLsbD_eq_core] at h
  rw [h, _root_.BitVec.getLsbD_signExtend, msb_eq_core, getLsbD_eq_core]

/-- The ported signed order key is the two's-complement value shifted by `2 ^ (w - 1)`. -/
theorem signedKey_eq_toInt_add {w : Nat} (hw : 0 < w) (x : BitVec w) :
    ((Anneal.BitVecArith.signedKey x : Nat) : Int) = x.toInt + ((2 ^ (w - 1) : Nat) : Int) := by
  have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
    have hw' : w = (w - 1) + 1 := by omega
    conv => lhs; rw [hw']
    rw [Nat.pow_succ, Nat.mul_comm]
  have hlt : x.toNat < 2 ^ w := x.isLt
  rw [_root_.BitVec.toInt_eq_msb_cond]
  cases hm : Anneal.BitVecArith.msb x with
  | false =>
    have hk := Anneal.BitVecArith.signedKey_eq_of_msb_false hw hm
    have hm' : x.msb = false := hm
    rw [hm', hk, natPow_eq]
    simp
  | true =>
    have hk := Anneal.BitVecArith.signedKey_eq_of_msb_true hw hm
    have hge := (Anneal.BitVecArith.msb_eq_true_iff hw x).1 hm
    have hm' : x.msb = true := hm
    rw [natPow_eq] at hge hk
    rw [hm', hk]
    simp only [↓reduceIte]
    omega

/-- Ported signed `≤` agrees with core `BitVec.sle` at every width. -/
theorem sle_iff_core {w : Nat} (a b : BitVec w) :
    Anneal.BitVecArith.sle a b ↔ _root_.BitVec.sle a b = true := by
  cases w with
  | zero =>
    have hab : a = b := by rw [_root_.BitVec.eq_nil a, _root_.BitVec.eq_nil b]
    subst hab
    exact ⟨fun _ => by simp [_root_.BitVec.sle_eq_decide], fun _ => Anneal.BitVecArith.sle_refl a⟩
  | succ n =>
    have ha := signedKey_eq_toInt_add (Nat.succ_pos n) a
    have hb := signedKey_eq_toInt_add (Nat.succ_pos n) b
    unfold Anneal.BitVecArith.sle
    rw [_root_.BitVec.sle_eq_decide, decide_eq_true_iff]
    omega

/-- Ported signed `<` agrees with core `BitVec.slt` at every width. -/
theorem slt_iff_core {w : Nat} (a b : BitVec w) :
    Anneal.BitVecArith.slt a b ↔ _root_.BitVec.slt a b = true := by
  cases w with
  | zero =>
    have hab : a = b := by rw [_root_.BitVec.eq_nil a, _root_.BitVec.eq_nil b]
    subst hab
    exact ⟨fun h => absurd h (Nat.lt_irrefl _), fun h => by simp [_root_.BitVec.slt_eq_decide] at h⟩
  | succ n =>
    have ha := signedKey_eq_toInt_add (Nat.succ_pos n) a
    have hb := signedKey_eq_toInt_add (Nat.succ_pos n) b
    unfold Anneal.BitVecArith.slt
    rw [_root_.BitVec.slt_eq_decide, decide_eq_true_iff]
    omega

/-- Decision procedure for the ported signed `≤` (the port ships none). -/
instance decSle {w : Nat} (a b : BitVec w) : Decidable (Anneal.BitVecArith.sle a b) :=
  inferInstanceAs
    (Decidable (Anneal.BitVecArith.signedKey a ≤ Anneal.BitVecArith.signedKey b))

/-- Decision procedure for the ported signed `<` (the port ships none). -/
instance decSlt {w : Nat} (a b : BitVec w) : Decidable (Anneal.BitVecArith.slt a b) :=
  inferInstanceAs
    (Decidable (Anneal.BitVecArith.signedKey a < Anneal.BitVecArith.signedKey b))

/-- `BitVec.ofNat w x.toNat` is `x`. -/
theorem ofNat_toNat_self {w : Nat} (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  apply _root_.BitVec.eq_of_toNat_eq
  rw [_root_.BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt x.isLt

/-- `BitVec.ofNat` at the scalar width collapses equal residues. -/
theorem ofNat_eq_ofNat_iff (w a b : Nat) :
    BitVec.ofNat w a = BitVec.ofNat w b ↔ a % 2 ^ w = b % 2 ^ w := by
  constructor
  · intro h
    have h' := congrArg _root_.BitVec.toNat h
    rw [_root_.BitVec.toNat_ofNat, _root_.BitVec.toNat_ofNat] at h'
    exact h'
  · intro h
    apply _root_.BitVec.eq_of_toNat_eq
    rw [_root_.BitVec.toNat_ofNat, _root_.BitVec.toNat_ofNat]
    exact h

/-! ## 1. Width Alignment (`8 * sz` vs `sz * 8`) -/

/-- Re-index a scalar-width bitvector (`8 * sz`, used by `Anneal.Scalars`, `ByteCodec` and
`bswapBytes`) at the byte-list width (`sz * 8`, used by `Anneal.LeBytes` and `Trusted`). -/
def toLeWidth {sz : Nat} (x : BitVec (8 * sz)) : BitVec (sz * 8) :=
  x.cast (Nat.mul_comm 8 sz)

/-- Re-index a byte-list-width bitvector (`sz * 8`) at the scalar width (`8 * sz`). -/
def ofLeWidth {sz : Nat} (x : BitVec (sz * 8)) : BitVec (8 * sz) :=
  x.cast (Nat.mul_comm sz 8)

@[simp] theorem toNat_toLeWidth {sz : Nat} (x : BitVec (8 * sz)) :
    (toLeWidth x).toNat = x.toNat := rfl

@[simp] theorem toNat_ofLeWidth {sz : Nat} (x : BitVec (sz * 8)) :
    (ofLeWidth x).toNat = x.toNat := rfl

@[simp] theorem ofLeWidth_toLeWidth {sz : Nat} (x : BitVec (8 * sz)) :
    ofLeWidth (toLeWidth x) = x :=
  _root_.BitVec.eq_of_toNat_eq rfl

@[simp] theorem toLeWidth_ofLeWidth {sz : Nat} (x : BitVec (sz * 8)) :
    toLeWidth (ofLeWidth x) = x :=
  _root_.BitVec.eq_of_toNat_eq rfl

/-- Width re-indexing is injective. -/
theorem toLeWidth_injective {sz : Nat} {x y : BitVec (8 * sz)}
    (h : toLeWidth x = toLeWidth y) : x = y := by
  rw [← ofLeWidth_toLeWidth x, ← ofLeWidth_toLeWidth y, h]

/-- Width re-indexing commutes with `BitVec.ofNat`. -/
theorem toLeWidth_ofNat (sz a : Nat) :
    toLeWidth (BitVec.ofNat (8 * sz) a) = BitVec.ofNat (sz * 8) a := by
  apply _root_.BitVec.eq_of_toNat_eq
  rw [toNat_toLeWidth, _root_.BitVec.toNat_ofNat, _root_.BitVec.toNat_ofNat, Nat.mul_comm]

/-- `scalarModulus sz` is `2 ^ (8 * sz)`. -/
theorem scalarModulus_eq (sz : Nat) : scalarModulus sz = 2 ^ (8 * sz) :=
  Anneal.Scalars.scalarModulus_eq_two_pow sz

/-- `scalarModulus sz` is `2 ^ (sz * 8)` (byte-list width shape). -/
theorem scalarModulus_eq_le (sz : Nat) : scalarModulus sz = 2 ^ (sz * 8) := by
  rw [scalarModulus_eq, Nat.mul_comm]

/-- Every `BitVec (8 * sz)` value is a canonical scalar bit pattern. -/
theorem toNat_lt_scalarModulus {sz : Nat} (x : BitVec (8 * sz)) :
    x.toNat < scalarModulus sz := by
  rw [scalarModulus_eq]
  exact x.isLt

/-- Canonicalization of scalar bits is the `toNat` of the `8 * sz`-bit vector. Holds for
non-canonical `a ≥ scalarModulus sz` and for `sz = 0`. -/
theorem wrapScalarBits_eq_toNat (a sz : Nat) :
    wrapScalarBits a (scalarModulus sz) = (BitVec.ofNat (8 * sz) a).toNat := by
  rw [Anneal.Scalars.wrapScalarBits_eq_mod_modulus, scalarModulus_eq, _root_.BitVec.toNat_ofNat]

/-- Canonical scalar bits are fixed by `BitVec.ofNat (8 * sz) ·` followed by `toNat`. -/
theorem toNat_ofNat_of_lt {a sz : Nat} (h : a < scalarModulus sz) :
    (BitVec.ofNat (8 * sz) a).toNat = a := by
  rw [_root_.BitVec.toNat_ofNat]
  rw [scalarModulus_eq] at h
  exact Nat.mod_eq_of_lt h

/-- Canonical scalar bits are fixed by `wrapScalarBits`. -/
theorem wrapScalarBits_of_lt {a sz : Nat} (h : a < scalarModulus sz) :
    wrapScalarBits a (scalarModulus sz) = a := by
  rw [wrapScalarBits_eq_toNat, toNat_ofNat_of_lt h]

/-! ## 2. Bitwise, Shift, Sign and Two's-Complement Value Bridges -/

/-- `bitwiseAndBits` is ported `and` at every bit width `w` (including `w = 0`) and for
arbitrary (possibly out-of-range) operands. -/
theorem bitwiseAndBits_eq_and (w a b : Nat) :
    bitwiseAndBits w a b =
      (Anneal.BitVec.and (BitVec.ofNat w a) (BitVec.ofNat w b)).toNat := by
  rw [Anneal.Scalars.bitwiseAndBits_eq_land, and_eq_core, _root_.BitVec.toNat_and,
    _root_.BitVec.toNat_ofNat, _root_.BitVec.toNat_ofNat, Nat.and_mod_two_pow]

/-- `bitwiseOrBits` is ported `or` at every bit width `w` and for arbitrary operands. -/
theorem bitwiseOrBits_eq_or (w a b : Nat) :
    bitwiseOrBits w a b =
      (Anneal.BitVec.or (BitVec.ofNat w a) (BitVec.ofNat w b)).toNat := by
  rw [Anneal.Scalars.bitwiseOrBits_eq_lor, or_eq_core, _root_.BitVec.toNat_or,
    _root_.BitVec.toNat_ofNat, _root_.BitVec.toNat_ofNat, Nat.or_mod_two_pow]

/-- `bitwiseXorBits` is ported `xor` at every bit width `w` and for arbitrary operands. -/
theorem bitwiseXorBits_eq_xor (w a b : Nat) :
    bitwiseXorBits w a b =
      (Anneal.BitVec.xor (BitVec.ofNat w a) (BitVec.ofNat w b)).toNat := by
  rw [Anneal.Scalars.bitwiseXorBits_eq_xor, xor_eq_core, _root_.BitVec.toNat_xor,
    _root_.BitVec.toNat_ofNat, _root_.BitVec.toNat_ofNat, Nat.xor_mod_two_pow]

/-- `bitwiseAndBits` on bitvector operands. -/
theorem bitwiseAndBits_toNat {w : Nat} (x y : BitVec w) :
    bitwiseAndBits w x.toNat y.toNat = (Anneal.BitVec.and x y).toNat := by
  rw [bitwiseAndBits_eq_and, ofNat_toNat_self, ofNat_toNat_self]

/-- `bitwiseOrBits` on bitvector operands. -/
theorem bitwiseOrBits_toNat {w : Nat} (x y : BitVec w) :
    bitwiseOrBits w x.toNat y.toNat = (Anneal.BitVec.or x y).toNat := by
  rw [bitwiseOrBits_eq_or, ofNat_toNat_self, ofNat_toNat_self]

/-- `bitwiseXorBits` on bitvector operands. -/
theorem bitwiseXorBits_toNat {w : Nat} (x y : BitVec w) :
    bitwiseXorBits w x.toNat y.toNat = (Anneal.BitVec.xor x y).toNat := by
  rw [bitwiseXorBits_eq_xor, ofNat_toNat_self, ofNat_toNat_self]

/-- Scalar bitwise complement (`bitwiseXorBits` against the all-ones pattern) is ported `not`. -/
theorem bitwiseXorBits_allOnes_eq_not (w a : Nat) :
    bitwiseXorBits w (2 ^ w - 1) a = (Anneal.BitVec.not (BitVec.ofNat w a)).toNat := by
  rw [bitwiseXorBits_eq_xor]
  have h : BitVec.ofNat w (2 ^ w - 1) = Anneal.BitVec.allOnes w := by
    apply _root_.BitVec.eq_of_toNat_eq
    rw [_root_.BitVec.toNat_ofNat, Anneal.BitVec.toNat_allOnes, natPow_eq]
    exact Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos)
  rw [h]
  rfl

/-- `shiftLeftBits` is ported `shl` for every shift amount (including `shift ≥ 8 * sz`), every
byte width (including `sz = 0`) and arbitrary (possibly non-canonical) `a`. -/
theorem shiftLeftBits_eq_shl (a shift sz : Nat) :
    shiftLeftBits a shift (scalarModulus sz) =
      (Anneal.BitVec.shl (BitVec.ofNat (8 * sz) a) shift).toNat := by
  rw [Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod, shl_eq_core, _root_.BitVec.toNat_shiftLeft,
    _root_.BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mod_mul_mod]

/-- `shiftRightUnsignedBits` on canonicalized bits is ported `ushr` for every shift amount and
byte width. The canonicalization is required: `shiftRightUnsignedBits` itself does not wrap. -/
theorem shiftRightUnsignedBits_eq_ushr (a shift sz : Nat) :
    shiftRightUnsignedBits (wrapScalarBits a (scalarModulus sz)) shift =
      (Anneal.BitVec.ushr (BitVec.ofNat (8 * sz) a) shift).toNat := by
  rw [Anneal.Scalars.shiftRightUnsignedBits_eq_shiftRight, wrapScalarBits_eq_toNat, ushr_eq_core,
    _root_.BitVec.toNat_ushiftRight]

/-- `shiftRightUnsignedBits` on already-canonical bits is ported `ushr`. -/
theorem shiftRightUnsignedBits_eq_ushr_of_lt {a sz : Nat} (h : a < scalarModulus sz)
    (shift : Nat) :
    shiftRightUnsignedBits a shift =
      (Anneal.BitVec.ushr (BitVec.ofNat (8 * sz) a) shift).toNat := by
  rw [← shiftRightUnsignedBits_eq_ushr, wrapScalarBits_of_lt h]

/-- `shiftRightUnsignedBits` on a bitvector operand. -/
theorem shiftRightUnsignedBits_toNat {w : Nat} (x : BitVec w) (shift : Nat) :
    shiftRightUnsignedBits x.toNat shift = (Anneal.BitVec.ushr x shift).toNat := by
  rw [Anneal.Scalars.shiftRightUnsignedBits_eq_shiftRight, ushr_eq_core,
    _root_.BitVec.toNat_ushiftRight]

/-- `isSignedNegative` is ported `msb` for arbitrary (possibly non-canonical) bits and every
byte width (`false` at `sz = 0`). -/
theorem isSignedNegative_eq_msb (bits sz : Nat) :
    isSignedNegative bits sz = Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) bits) :=
  (Anneal.Scalars.isSignedNegative_eq_msb bits sz).trans (msb_eq_core _).symm

/-- A ported arithmetic shift by at least the width saturates at a shift by the width. -/
theorem ashr_of_width_le {w : Nat} (x : BitVec w) {k : Nat} (hk : w ≤ k) :
    Anneal.BitVecArith.ashr x k = Anneal.BitVecArith.ashr x w := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [Anneal.BitVecArith.getLsbD_ashr, Anneal.BitVecArith.getLsbD_ashr]
  have h1 : ¬ (i + k < w) := by omega
  have h2 : ¬ (i + w < w) := by omega
  simp only [h1, h2, ↓reduceIte]

/-- `arithmeticShrBits` by at least the bit width saturates at a shift by the bit width. -/
theorem arithmeticShrBits_of_width_le (bits sz : Nat) {shift : Nat} (h : 8 * sz ≤ shift) :
    arithmeticShrBits bits sz shift = arithmeticShrBits bits sz (8 * sz) := by
  have hc : wrapScalarBits bits (scalarModulus sz) < 2 ^ (8 * sz) := by
    rw [wrapScalarBits_eq_toNat]
    exact (BitVec.ofNat (8 * sz) bits).isLt
  have hpow : 2 ^ (8 * sz) ≤ 2 ^ shift := Nat.pow_le_pow_right (by decide) h
  have h1 : shiftRightUnsignedBits (wrapScalarBits bits (scalarModulus sz)) shift = 0 := by
    rw [Anneal.Scalars.shiftRightUnsignedBits_eq_shiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hc hpow)
  have h2 : shiftRightUnsignedBits (wrapScalarBits bits (scalarModulus sz)) (8 * sz) = 0 := by
    rw [Anneal.Scalars.shiftRightUnsignedBits_eq_shiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hc
  have h3 : Nat.sub (Nat.mul sz 8) shift = 0 := by
    rw [natMul_eight]; exact Nat.sub_eq_zero_of_le h
  have h4 : Nat.sub (Nat.mul sz 8) (8 * sz) = 0 := by
    rw [natMul_eight]; exact Nat.sub_self _
  unfold arithmeticShrBits
  simp only [h1, h2, h3, h4]

/-- `arithmeticShrBits` is ported `ashr` for arbitrary (possibly non-canonical) bits, every
byte width (including `sz = 0`) and every shift amount (including `shift > 8 * sz`). -/
theorem arithmeticShrBits_eq_ashr (bits sz shift : Nat) :
    arithmeticShrBits bits sz shift =
      (Anneal.BitVecArith.ashr (BitVec.ofNat (8 * sz) bits) shift).toNat := by
  cases sz with
  | zero =>
    have hr := (Anneal.BitVecArith.ashr (BitVec.ofNat (8 * 0) bits) shift).isLt
    have hl : arithmeticShrBits bits 0 shift =
        wrapScalarBits
          (shiftRightUnsignedBits (wrapScalarBits bits (scalarModulus 0)) shift)
          (scalarModulus 0) := rfl
    rw [hl, Anneal.Scalars.wrapScalarBits_eq_mod_modulus]
    have hm : scalarModulus 0 = 1 := rfl
    rw [hm, Nat.mod_one]
    simp at hr
    omega
  | succ n =>
    cases Nat.le_total shift (8 * (n + 1)) with
    | inl hs =>
      rw [Anneal.Scalars.arithmeticShrBits_eq_sshiftRight (Nat.succ_pos n) hs, ashr_eq_core]
    | inr hs =>
      rw [arithmeticShrBits_of_width_le bits (n + 1) hs, ashr_of_width_le _ hs,
        Anneal.Scalars.arithmeticShrBits_eq_sshiftRight (Nat.succ_pos n) (Nat.le_refl _),
        ashr_eq_core]

/-- `arithmeticShrBits` on canonicalized bits is ported `ashr`. -/
theorem arithmeticShrBits_wrap_eq_ashr (bits sz shift : Nat) :
    arithmeticShrBits (wrapScalarBits bits (scalarModulus sz)) sz shift =
      (Anneal.BitVecArith.ashr (BitVec.ofNat (8 * sz) bits) shift).toNat := by
  rw [arithmeticShrBits_eq_ashr, wrapScalarBits_eq_toNat, ofNat_toNat_self]

/-- `signExtendBits` is ported `signExtend` for arbitrary bits and every pair of byte widths
(widening, same-width and truncating, including `srcSz = 0` and `dstSz = 0`). -/
theorem signExtendBits_eq_signExtend (bits srcSz dstSz : Nat) :
    signExtendBits bits srcSz dstSz =
      (Anneal.BitVecArith.signExtend (8 * dstSz) (BitVec.ofNat (8 * srcSz) bits)).toNat := by
  rw [Anneal.Scalars.signExtendBits_eq_bitVec, signExtend_eq_core]

/-- `signedLt` decides ported `slt` for arbitrary bits and every byte width. -/
theorem signedLt_eq_true_iff (a b sz : Nat) :
    signedLt a b sz = true ↔
      Anneal.BitVecArith.slt (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b) := by
  rw [Anneal.Scalars.signedLt_eq_slt, slt_iff_core]

/-- `signedLe` decides ported `sle` for arbitrary bits and every byte width. -/
theorem signedLe_eq_true_iff (a b sz : Nat) :
    signedLe a b sz = true ↔
      Anneal.BitVecArith.sle (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b) := by
  rw [Anneal.Scalars.signedLe_eq_sle, sle_iff_core]

/-- `signedLt` as an exact Boolean value. -/
theorem signedLt_eq_decide (a b sz : Nat) :
    signedLt a b sz =
      decide (Anneal.BitVecArith.slt (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)) := by
  cases h : signedLt a b sz with
  | true => exact (decide_eq_true ((signedLt_eq_true_iff a b sz).1 h)).symm
  | false =>
    refine (decide_eq_false (fun hs => ?_)).symm
    rw [(signedLt_eq_true_iff a b sz).2 hs] at h
    nomatch h

/-- `signedLe` as an exact Boolean value. -/
theorem signedLe_eq_decide (a b sz : Nat) :
    signedLe a b sz =
      decide (Anneal.BitVecArith.sle (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)) := by
  cases h : signedLe a b sz with
  | true => exact (decide_eq_true ((signedLe_eq_true_iff a b sz).1 h)).symm
  | false =>
    refine (decide_eq_false (fun hs => ?_)).symm
    rw [(signedLe_eq_true_iff a b sz).2 hs] at h
    nomatch h

/-- Wrapping addition of scalar bits is `BitVec` addition, for arbitrary operands. -/
theorem add_mod_eq_toNat_add (a b sz : Nat) :
    (a + b) % 2 ^ (8 * sz) =
      (BitVec.ofNat (8 * sz) a + BitVec.ofNat (8 * sz) b).toNat := by
  rw [_root_.BitVec.toNat_add, _root_.BitVec.toNat_ofNat, _root_.BitVec.toNat_ofNat,
    ← Nat.add_mod]

/-- Wrapping subtraction of scalar bits is `BitVec` subtraction, for arbitrary operands. -/
theorem sub_mod_eq_toNat_sub (a b sz : Nat) :
    (2 ^ (8 * sz) + a % 2 ^ (8 * sz) - b % 2 ^ (8 * sz)) % 2 ^ (8 * sz) =
      (BitVec.ofNat (8 * sz) a - BitVec.ofNat (8 * sz) b).toNat := by
  rw [_root_.BitVec.toNat_sub, _root_.BitVec.toNat_ofNat, _root_.BitVec.toNat_ofNat]
  have hb : b % 2 ^ (8 * sz) < 2 ^ (8 * sz) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h : 2 ^ (8 * sz) + a % 2 ^ (8 * sz) - b % 2 ^ (8 * sz) =
      2 ^ (8 * sz) - b % 2 ^ (8 * sz) + a % 2 ^ (8 * sz) := by omega
  rw [h]

/-! ## 3. `evalBinOp`, `evalScalarBinOp` and `evalWrapping*` Value Bridges -/

/-- `Nat.beq n 0 = false` for positive `n`. -/
theorem beq_zero_of_pos {n : Nat} (h : 0 < n) : Nat.beq n 0 = false :=
  nat_beq_eq_false_of_ne (Nat.ne_of_gt h)

/-- `evalBinOp .bitAnd` computes ported `and` (arbitrary, possibly non-canonical operands). -/
theorem evalBinOp_bitAnd_eq_and {sz : Nat} (hsz : 0 < sz) (a b : Nat) (isSigned : Bool) :
    Anneal.Scalars.evalBinOp .bitAnd ⟨a, sz⟩ ⟨b, sz⟩ isSigned =
      some ⟨(Anneal.BitVec.and (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)).toNat, sz⟩ := by
  rw [Anneal.Scalars.evalBinOp_bitAnd_apply hsz, ← Anneal.Scalars.bitwiseAndBits_eq_land,
    bitwiseAndBits_eq_and]

/-- `evalBinOp .bitOr` computes ported `or` (arbitrary operands). -/
theorem evalBinOp_bitOr_eq_or {sz : Nat} (hsz : 0 < sz) (a b : Nat) (isSigned : Bool) :
    Anneal.Scalars.evalBinOp .bitOr ⟨a, sz⟩ ⟨b, sz⟩ isSigned =
      some ⟨(Anneal.BitVec.or (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)).toNat, sz⟩ := by
  rw [Anneal.Scalars.evalBinOp_bitOr_apply hsz, ← Anneal.Scalars.bitwiseOrBits_eq_lor,
    bitwiseOrBits_eq_or]

/-- `evalBinOp .bitXor` computes ported `xor` (arbitrary operands). -/
theorem evalBinOp_bitXor_eq_xor {sz : Nat} (hsz : 0 < sz) (a b : Nat) (isSigned : Bool) :
    Anneal.Scalars.evalBinOp .bitXor ⟨a, sz⟩ ⟨b, sz⟩ isSigned =
      some ⟨(Anneal.BitVec.xor (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)).toNat, sz⟩ := by
  rw [Anneal.Scalars.evalBinOp_bitXor_apply hsz, ← Anneal.Scalars.bitwiseXorBits_eq_xor,
    bitwiseXorBits_eq_xor]

/-- `evalBinOp .shl` computes ported `shl` by the masked shift amount `b % (8 * szL)`
(arbitrary operands; the right operand may have a different byte width). -/
theorem evalBinOp_shl_eq_shl {szL szR : Nat} (hszL : 0 < szL) (hszR : 0 < szR) (a b : Nat)
    (isSigned : Bool) :
    Anneal.Scalars.evalBinOp .shl ⟨a, szL⟩ ⟨b, szR⟩ isSigned =
      some ⟨(Anneal.BitVec.shl (BitVec.ofNat (8 * szL) a) (b % (8 * szL))).toNat, szL⟩ := by
  rw [Anneal.Scalars.evalBinOp_shl_apply hszL hszR,
    ← Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod, shiftLeftBits_eq_shl]

/-- `evalBinOp .shr` (unsigned) computes ported `ushr` by the masked shift amount on a
canonical left operand. -/
theorem evalBinOp_shr_unsigned_eq_ushr {szL szR : Nat} (hszL : 0 < szL) (hszR : 0 < szR)
    {a : Nat} (ha : a < scalarModulus szL) (b : Nat) :
    Anneal.Scalars.evalBinOp .shr ⟨a, szL⟩ ⟨b, szR⟩ false =
      some ⟨(Anneal.BitVec.ushr (BitVec.ofNat (8 * szL) a) (b % (8 * szL))).toNat, szL⟩ := by
  rw [Anneal.Scalars.evalBinOp_shr_unsigned hszL hszR, ushr_eq_core,
    _root_.BitVec.toNat_ushiftRight, toNat_ofNat_of_lt ha]
  rw [scalarModulus_eq] at ha
  have hle : a >>> (b % (8 * szL)) ≤ a := Nat.shiftRight_le a _
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle ha)]

/-- `evalBinOp .shr` (signed) computes ported `ashr` by the masked shift amount (arbitrary
operands). -/
theorem evalBinOp_shr_signed_eq_ashr {szL szR : Nat} (hszL : 0 < szL) (hszR : 0 < szR)
    (a b : Nat) :
    Anneal.Scalars.evalBinOp .shr ⟨a, szL⟩ ⟨b, szR⟩ true =
      some ⟨(Anneal.BitVecArith.ashr (BitVec.ofNat (8 * szL) a) (b % (8 * szL))).toNat, szL⟩ := by
  rw [Anneal.Scalars.evalBinOp_shr_signed hszL hszR, ashr_eq_core]

/-- `evalBinOp .add` computes wrapping `BitVec` addition (arbitrary operands). -/
theorem evalBinOp_add_eq_add {sz : Nat} (hsz : 0 < sz) (a b : Nat) (isSigned : Bool) :
    Anneal.Scalars.evalBinOp .add ⟨a, sz⟩ ⟨b, sz⟩ isSigned =
      some ⟨(BitVec.ofNat (8 * sz) a + BitVec.ofNat (8 * sz) b).toNat, sz⟩ := by
  rw [Anneal.Scalars.evalBinOp_add_apply hsz, add_mod_eq_toNat_add]

/-- `evalBinOp .sub` computes wrapping `BitVec` subtraction (arbitrary operands). -/
theorem evalBinOp_sub_eq_sub {sz : Nat} (hsz : 0 < sz) (a b : Nat) (isSigned : Bool) :
    Anneal.Scalars.evalBinOp .sub ⟨a, sz⟩ ⟨b, sz⟩ isSigned =
      some ⟨(BitVec.ofNat (8 * sz) a - BitVec.ofNat (8 * sz) b).toNat, sz⟩ := by
  rw [Anneal.Scalars.evalBinOp_sub_apply hsz, sub_mod_eq_toNat_sub]

/-- `evalBinOp .lt` (signed) decides ported `slt`. -/
theorem evalBinOp_lt_signed_eq_slt {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    Anneal.Scalars.evalBinOp .lt ⟨a, sz⟩ ⟨b, sz⟩ true =
      some (boolToScalar
        (decide (Anneal.BitVecArith.slt (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)))) := by
  rw [Anneal.Scalars.evalBinOp_lt_signed hsz, ← Anneal.Scalars.signedLt_eq_slt,
    signedLt_eq_decide]

/-- `evalBinOp .le` (signed) decides ported `sle`. -/
theorem evalBinOp_le_signed_eq_sle {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    Anneal.Scalars.evalBinOp .le ⟨a, sz⟩ ⟨b, sz⟩ true =
      some (boolToScalar
        (decide (Anneal.BitVecArith.sle (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)))) := by
  rw [Anneal.Scalars.evalBinOp_le_signed hsz, ← Anneal.Scalars.signedLe_eq_sle,
    signedLe_eq_decide]

/-- Every `evalBinOp` on a zero-width left operand is rejected: the `sz = 0` edge is
excluded by the evaluator, not silently treated as a `BitVec 0` computation. -/
theorem evalBinOp_eq_none_of_size_zero (op : BinOp) (a : Nat) (rhs : ScalarInt)
    (isSigned : Bool) :
    Anneal.Scalars.evalBinOp op ⟨a, 0⟩ rhs isSigned = none := rfl

/-- Operational (`Trusted`) `evalScalarBinOp .bitAnd` computes ported `and`. -/
theorem evalScalarBinOp_bitAnd_eq_and {sz : Nat} (hsz : 0 < sz) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp .bitAnd ⟨a, sz⟩ ⟨b, sz⟩ locals mem isSigned =
      .ok (.scalar
        ⟨(Anneal.BitVec.and (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)).toNat, sz⟩)
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_bitAnd hsz, ← Anneal.Scalars.bitwiseAndBits_eq_land,
    bitwiseAndBits_eq_and]

/-- Operational `evalScalarBinOp .bitOr` computes ported `or`. -/
theorem evalScalarBinOp_bitOr_eq_or {sz : Nat} (hsz : 0 < sz) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp .bitOr ⟨a, sz⟩ ⟨b, sz⟩ locals mem isSigned =
      .ok (.scalar
        ⟨(Anneal.BitVec.or (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)).toNat, sz⟩)
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_bitOr hsz, ← Anneal.Scalars.bitwiseOrBits_eq_lor,
    bitwiseOrBits_eq_or]

/-- Operational `evalScalarBinOp .bitXor` computes ported `xor`. -/
theorem evalScalarBinOp_bitXor_eq_xor {sz : Nat} (hsz : 0 < sz) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp .bitXor ⟨a, sz⟩ ⟨b, sz⟩ locals mem isSigned =
      .ok (.scalar
        ⟨(Anneal.BitVec.xor (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)).toNat, sz⟩)
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_bitXor hsz, ← Anneal.Scalars.bitwiseXorBits_eq_xor,
    bitwiseXorBits_eq_xor]

/-- Operational `evalScalarBinOp .shl` computes ported `shl` by the masked shift amount. -/
theorem evalScalarBinOp_shl_eq_shl {szL szR : Nat} (hszL : 0 < szL) (hszR : 0 < szR)
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp .shl ⟨a, szL⟩ ⟨b, szR⟩ locals mem isSigned =
      .ok (.scalar
        ⟨(Anneal.BitVec.shl (BitVec.ofNat (8 * szL) a) (b % (8 * szL))).toNat, szL⟩)
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_shl hszL hszR,
    ← Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod, shiftLeftBits_eq_shl]

/-- Operational `evalScalarBinOp .shr` (unsigned) computes ported `ushr` on a canonical left
operand. -/
theorem evalScalarBinOp_shr_unsigned_eq_ushr {szL szR : Nat} (hszL : 0 < szL) (hszR : 0 < szR)
    {a : Nat} (ha : a < scalarModulus szL) (b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .shr ⟨a, szL⟩ ⟨b, szR⟩ locals mem false =
      .ok (.scalar
        ⟨(Anneal.BitVec.ushr (BitVec.ofNat (8 * szL) a) (b % (8 * szL))).toNat, szL⟩)
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_shr_unsigned hszL hszR, ushr_eq_core,
    _root_.BitVec.toNat_ushiftRight, toNat_ofNat_of_lt ha]
  rw [scalarModulus_eq] at ha
  have hle : a >>> (b % (8 * szL)) ≤ a := Nat.shiftRight_le a _
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle ha)]

/-- Operational `evalScalarBinOp .shr` (signed) computes ported `ashr`. -/
theorem evalScalarBinOp_shr_signed_eq_ashr {szL szR : Nat} (hszL : 0 < szL) (hszR : 0 < szR)
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .shr ⟨a, szL⟩ ⟨b, szR⟩ locals mem true =
      .ok (.scalar
        ⟨(Anneal.BitVecArith.ashr (BitVec.ofNat (8 * szL) a) (b % (8 * szL))).toNat, szL⟩)
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_shr_signed hszL hszR, ashr_eq_core]

/-- Operational `evalScalarBinOp .add` computes wrapping `BitVec` addition. -/
theorem evalScalarBinOp_add_eq_add {sz : Nat} (hsz : 0 < sz) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp .add ⟨a, sz⟩ ⟨b, sz⟩ locals mem isSigned =
      .ok (.scalar ⟨(BitVec.ofNat (8 * sz) a + BitVec.ofNat (8 * sz) b).toNat, sz⟩)
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_add hsz, add_mod_eq_toNat_add]

/-- Operational `evalScalarBinOp .sub` computes wrapping `BitVec` subtraction. -/
theorem evalScalarBinOp_sub_eq_sub {sz : Nat} (hsz : 0 < sz) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp .sub ⟨a, sz⟩ ⟨b, sz⟩ locals mem isSigned =
      .ok (.scalar ⟨(BitVec.ofNat (8 * sz) a - BitVec.ofNat (8 * sz) b).toNat, sz⟩)
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_sub hsz, sub_mod_eq_toNat_sub]

/-- `evalWrappingAdd` computes wrapping `BitVec` addition (arbitrary operands). -/
theorem evalWrappingAdd_eq_add {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    evalWrappingAdd ⟨a, sz⟩ ⟨b, sz⟩ =
      some ⟨(BitVec.ofNat (8 * sz) a + BitVec.ofNat (8 * sz) b).toNat, sz⟩ := by
  have h0 : Nat.beq sz 0 = false := beq_zero_of_pos hsz
  have h1 : Nat.beq sz sz = true := nat_beq_self sz
  unfold evalWrappingAdd
  simp only [h0, h1, Bool.not_true, Bool.or_false]
  rw [Anneal.Scalars.wrapScalarBits_eq_mod_modulus, Anneal.Scalars.wrapScalarBits_eq_mod_modulus,
    Anneal.Scalars.wrapScalarBits_eq_mod_modulus, scalarModulus_eq, natAdd_eq, ← Nat.add_mod,
    add_mod_eq_toNat_add]

/-- `evalWrappingSub` computes wrapping `BitVec` subtraction (arbitrary operands). -/
theorem evalWrappingSub_eq_sub {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    evalWrappingSub ⟨a, sz⟩ ⟨b, sz⟩ =
      some ⟨(BitVec.ofNat (8 * sz) a - BitVec.ofNat (8 * sz) b).toNat, sz⟩ := by
  have h0 : Nat.beq sz 0 = false := beq_zero_of_pos hsz
  have h1 : Nat.beq sz sz = true := nat_beq_self sz
  have hM : 0 < 2 ^ (8 * sz) := Nat.two_pow_pos _
  have ha : a % 2 ^ (8 * sz) < 2 ^ (8 * sz) := Nat.mod_lt _ hM
  have hb : b % 2 ^ (8 * sz) < 2 ^ (8 * sz) := Nat.mod_lt _ hM
  unfold evalWrappingSub
  simp only [h0, h1, Bool.not_true, Bool.or_false]
  rw [← sub_mod_eq_toNat_sub]
  simp only [Anneal.Scalars.wrapScalarBits_eq_mod_modulus, scalarModulus_eq, natAdd_eq, natSub_eq]
  cases hble : Nat.ble (b % 2 ^ (8 * sz)) (a % 2 ^ (8 * sz)) with
  | true =>
    have hle : b % 2 ^ (8 * sz) ≤ a % 2 ^ (8 * sz) := Nat.le_of_ble_eq_true hble
    have h : 2 ^ (8 * sz) + a % 2 ^ (8 * sz) - b % 2 ^ (8 * sz) =
        (a % 2 ^ (8 * sz) - b % 2 ^ (8 * sz)) + 2 ^ (8 * sz) := by omega
    simp only [h, Nat.add_mod_right]
  | false => rfl

/-- `evalWrappingAdd` is rejected exactly on zero-width or mismatched-width operands. -/
theorem evalWrappingAdd_eq_none_iff (x y : ScalarInt) :
    evalWrappingAdd x y = none ↔ x.sizeBytes = 0 ∨ x.sizeBytes ≠ y.sizeBytes := by
  unfold evalWrappingAdd
  cases h0 : Nat.beq x.sizeBytes 0 with
  | true =>
    exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h0), fun _ => rfl⟩
  | false =>
    have hne : x.sizeBytes ≠ 0 := fun h => by rw [h] at h0; nomatch h0
    cases h1 : Nat.beq x.sizeBytes y.sizeBytes with
    | true =>
      have heq : x.sizeBytes = y.sizeBytes := Nat.eq_of_beq_eq_true h1
      refine ⟨fun h => ?_, fun h => ?_⟩
      · cases h
      · cases h with
        | inl h => exact absurd h hne
        | inr h => exact absurd heq h
    | false =>
      have hneq : x.sizeBytes ≠ y.sizeBytes := fun h => by
        rw [h, nat_beq_self] at h1; nomatch h1
      exact ⟨fun _ => Or.inr hneq, fun _ => rfl⟩

/-- `evalWrappingSub` is rejected exactly on zero-width or mismatched-width operands. -/
theorem evalWrappingSub_eq_none_iff (x y : ScalarInt) :
    evalWrappingSub x y = none ↔ x.sizeBytes = 0 ∨ x.sizeBytes ≠ y.sizeBytes := by
  unfold evalWrappingSub
  cases h0 : Nat.beq x.sizeBytes 0 with
  | true =>
    exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h0), fun _ => rfl⟩
  | false =>
    have hne : x.sizeBytes ≠ 0 := fun h => by rw [h] at h0; nomatch h0
    cases h1 : Nat.beq x.sizeBytes y.sizeBytes with
    | true =>
      have heq : x.sizeBytes = y.sizeBytes := Nat.eq_of_beq_eq_true h1
      refine ⟨fun h => ?_, fun h => ?_⟩
      · cases h
      · cases h with
        | inl h => exact absurd h hne
        | inr h => exact absurd heq h
    | false =>
      have hneq : x.sizeBytes ≠ y.sizeBytes := fun h => by
        rw [h, nat_beq_self] at h1; nomatch h1
      exact ⟨fun _ => Or.inr hneq, fun _ => rfl⟩

/-! ## 4. Disjoint-Mask Packing and Bitfield Extraction on Scalars -/

/-- Equal `BitVec.ofNat` images of in-range naturals force equal naturals. -/
theorem eq_of_ofNat_eq {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b := by
  have h' := (ofNat_eq_ofNat_iff w a b).1 h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

/-- `bitwiseAndBits` results are canonical at the scalar width. -/
theorem bitwiseAndBits_lt_scalarModulus (sz a b : Nat) :
    bitwiseAndBits (8 * sz) a b < scalarModulus sz := by
  rw [scalarModulus_eq]; exact Anneal.Scalars.bitwiseAndBits_lt_two_pow _ _ _

/-- `bitwiseOrBits` results are canonical at the scalar width. -/
theorem bitwiseOrBits_lt_scalarModulus (sz a b : Nat) :
    bitwiseOrBits (8 * sz) a b < scalarModulus sz := by
  rw [scalarModulus_eq]; exact Anneal.Scalars.bitwiseOrBits_lt_two_pow _ _ _

/-- `bitwiseXorBits` results are canonical at the scalar width. -/
theorem bitwiseXorBits_lt_scalarModulus (sz a b : Nat) :
    bitwiseXorBits (8 * sz) a b < scalarModulus sz := by
  rw [scalarModulus_eq]; exact Anneal.Scalars.bitwiseXorBits_lt_two_pow _ _ _

/-- `shiftLeftBits` results are canonical at the scalar width. -/
theorem shiftLeftBits_lt_scalarModulus (a shift sz : Nat) :
    shiftLeftBits a shift (scalarModulus sz) < scalarModulus sz := by
  rw [shiftLeftBits_eq_shl]; exact toNat_lt_scalarModulus _

/-- Disjoint-mask OR injectivity (`Anneal.BitVec.disjoint_or_injective`) on `bitwiseOrBits` /
`bitwiseAndBits`, for arbitrary (possibly non-canonical) operands: the packed operands are
determined modulo `2 ^ w`. The complement mask is the scalar NOT `bitwiseXorBits w (2^w - 1) mask`. -/
theorem bitwiseOrBits_disjoint_injective_mod {w mask a₁ b₁ a₂ b₂ : Nat}
    (hm₁ : bitwiseAndBits w a₁ mask = 0) (hm₂ : bitwiseAndBits w a₂ mask = 0)
    (hn₁ : bitwiseAndBits w b₁ (bitwiseXorBits w (2 ^ w - 1) mask) = 0)
    (hn₂ : bitwiseAndBits w b₂ (bitwiseXorBits w (2 ^ w - 1) mask) = 0)
    (h : bitwiseOrBits w a₁ b₁ = bitwiseOrBits w a₂ b₂) :
    a₁ % 2 ^ w = a₂ % 2 ^ w ∧ b₁ % 2 ^ w = b₂ % 2 ^ w := by
  rw [bitwiseAndBits_eq_and] at hm₁ hm₂ hn₁ hn₂
  rw [bitwiseXorBits_allOnes_eq_not, ofNat_toNat_self] at hn₁ hn₂
  rw [bitwiseOrBits_eq_or, bitwiseOrBits_eq_or] at h
  have hz := (Anneal.BitVec.toNat_zero w).symm
  have r := Anneal.BitVec.disjoint_or_injective (mask := BitVec.ofNat w mask)
    (Anneal.BitVec.eq_of_toNat_eq (hm₁.trans hz)) (Anneal.BitVec.eq_of_toNat_eq (hm₂.trans hz))
    (Anneal.BitVec.eq_of_toNat_eq (hn₁.trans hz)) (Anneal.BitVec.eq_of_toNat_eq (hn₂.trans hz))
    (Anneal.BitVec.eq_of_toNat_eq h)
  exact ⟨(ofNat_eq_ofNat_iff w a₁ a₂).1 r.1, (ofNat_eq_ofNat_iff w b₁ b₂).1 r.2⟩

/-- Disjoint-mask OR injectivity on canonical operands: the packed operands are recovered
exactly. -/
theorem bitwiseOrBits_disjoint_injective {w mask a₁ b₁ a₂ b₂ : Nat}
    (ha₁ : a₁ < 2 ^ w) (hb₁ : b₁ < 2 ^ w) (ha₂ : a₂ < 2 ^ w) (hb₂ : b₂ < 2 ^ w)
    (hm₁ : bitwiseAndBits w a₁ mask = 0) (hm₂ : bitwiseAndBits w a₂ mask = 0)
    (hn₁ : bitwiseAndBits w b₁ (bitwiseXorBits w (2 ^ w - 1) mask) = 0)
    (hn₂ : bitwiseAndBits w b₂ (bitwiseXorBits w (2 ^ w - 1) mask) = 0)
    (h : bitwiseOrBits w a₁ b₁ = bitwiseOrBits w a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have r := bitwiseOrBits_disjoint_injective_mod hm₁ hm₂ hn₁ hn₂ h
  rw [Nat.mod_eq_of_lt ha₁, Nat.mod_eq_of_lt ha₂, Nat.mod_eq_of_lt hb₁, Nat.mod_eq_of_lt hb₂] at r
  exact r

/-- Aligned/bounded OR injectivity (`Anneal.BitVec.aligned_or_bounded_injective`) on
`bitwiseOrBits`: a `2^k`-aligned high part and a `< 2^k` low part are recovered exactly. -/
theorem bitwiseOrBits_aligned_bounded_injective {w k a₁ b₁ a₂ b₂ : Nat} (hk : k ≤ w)
    (ha₁ : a₁ < 2 ^ w) (ha₂ : a₂ < 2 ^ w)
    (hal₁ : a₁ % 2 ^ k = 0) (hal₂ : a₂ % 2 ^ k = 0)
    (hb₁ : b₁ < 2 ^ k) (hb₂ : b₂ < 2 ^ k)
    (h : bitwiseOrBits w a₁ b₁ = bitwiseOrBits w a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hkw : 2 ^ k ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hk
  have hb₁w : b₁ < 2 ^ w := Nat.lt_of_lt_of_le hb₁ hkw
  have hb₂w : b₂ < 2 ^ w := Nat.lt_of_lt_of_le hb₂ hkw
  have t : ∀ {c : Nat}, c < 2 ^ w → (BitVec.ofNat w c).toNat = c := fun hc => by
    rw [_root_.BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hc
  rw [bitwiseOrBits_eq_or, bitwiseOrBits_eq_or] at h
  have r := Anneal.BitVec.aligned_or_bounded_injective
    (a₁ := BitVec.ofNat w a₁) (b₁ := BitVec.ofNat w b₁)
    (a₂ := BitVec.ofNat w a₂) (b₂ := BitVec.ofNat w b₂) hk
    (by rw [t ha₁]; exact hal₁) (by rw [t ha₂]; exact hal₂)
    (by rw [t hb₁w]; exact hb₁) (by rw [t hb₂w]; exact hb₂)
    (Anneal.BitVec.eq_of_toNat_eq h)
  exact ⟨eq_of_ofNat_eq ha₁ ha₂ r.1, eq_of_ofNat_eq hb₁w hb₂w r.2⟩

/-- A left shift that stays inside the scalar width is exact multiplication. -/
theorem shiftLeftBits_eq_mul_of_lt {sz k hi : Nat} (hk : k ≤ 8 * sz)
    (h : hi < 2 ^ (8 * sz - k)) :
    shiftLeftBits hi k (scalarModulus sz) = hi * 2 ^ k := by
  rw [Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have hp : 2 ^ (8 * sz) = 2 ^ (8 * sz - k) * 2 ^ k := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hp]
  exact (Nat.mul_lt_mul_right (Nat.two_pow_pos k)).2 h

/-- Shift-and-OR packing `(hi << k) | lo` on scalars is injective on in-range fields. -/
theorem shiftLeftBits_or_injective {sz k hi₁ lo₁ hi₂ lo₂ : Nat} (hk : k ≤ 8 * sz)
    (hhi₁ : hi₁ < 2 ^ (8 * sz - k)) (hhi₂ : hi₂ < 2 ^ (8 * sz - k))
    (hlo₁ : lo₁ < 2 ^ k) (hlo₂ : lo₂ < 2 ^ k)
    (h : bitwiseOrBits (8 * sz) (shiftLeftBits hi₁ k (scalarModulus sz)) lo₁ =
      bitwiseOrBits (8 * sz) (shiftLeftBits hi₂ k (scalarModulus sz)) lo₂) :
    hi₁ = hi₂ ∧ lo₁ = lo₂ := by
  have hp : 2 ^ (8 * sz) = 2 ^ (8 * sz - k) * 2 ^ k := by
    rw [← Nat.pow_add]; congr 1; omega
  have c₁ : hi₁ * 2 ^ k < 2 ^ (8 * sz) := by
    rw [hp]; exact (Nat.mul_lt_mul_right (Nat.two_pow_pos k)).2 hhi₁
  have c₂ : hi₂ * 2 ^ k < 2 ^ (8 * sz) := by
    rw [hp]; exact (Nat.mul_lt_mul_right (Nat.two_pow_pos k)).2 hhi₂
  rw [shiftLeftBits_eq_mul_of_lt hk hhi₁, shiftLeftBits_eq_mul_of_lt hk hhi₂] at h
  have r := bitwiseOrBits_aligned_bounded_injective hk c₁ c₂
    (Nat.mul_mod_left _ _) (Nat.mul_mod_left _ _) hlo₁ hlo₂ h
  exact ⟨Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos k) r.1, r.2⟩

/-- Scalar-level bitfield extraction `(x >> lo) & (2 ^ len - 1)` at byte width `sz`, composed
from `shiftRightUnsignedBits` and `bitwiseAndBits`. -/
def extractField (sz x lo len : Nat) : Nat :=
  bitwiseAndBits (8 * sz) (shiftRightUnsignedBits x lo) (2 ^ len - 1)

/-- `extractField` on a bitvector operand is ported `extractBits`, for every `lo` and `len`
(including `len = 0`, `lo ≥ 8 * sz` and `len > 8 * sz`). -/
theorem extractField_toNat {sz : Nat} (x : BitVec (8 * sz)) (lo len : Nat) :
    extractField sz x.toNat lo len = (Anneal.BitVecArith.extractBits x lo len).toNat := by
  unfold extractField Anneal.BitVecArith.extractBits
  rw [Anneal.Scalars.bitwiseAndBits_eq_land, Anneal.Scalars.shiftRightUnsignedBits_eq_shiftRight,
    Nat.and_two_pow_sub_one_eq_mod, setWidth_eq_core, ushr_eq_core,
    _root_.BitVec.toNat_setWidth, _root_.BitVec.toNat_ushiftRight]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _)
    (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt)

/-- `extractField` on canonical scalar bits is ported `extractBits`. -/
theorem extractField_eq_extractBits {sz x : Nat} (hx : x < scalarModulus sz) (lo len : Nat) :
    extractField sz x lo len =
      (Anneal.BitVecArith.extractBits (BitVec.ofNat (8 * sz) x) lo len).toNat := by
  rw [← extractField_toNat, toNat_ofNat_of_lt hx]

/-- Extraction distributes over OR-packing of canonical scalars. -/
theorem extractField_bitwiseOrBits {sz x y : Nat} (hx : x < scalarModulus sz)
    (hy : y < scalarModulus sz) (lo len : Nat) :
    extractField sz (bitwiseOrBits (8 * sz) x y) lo len =
      extractField sz x lo len ||| extractField sz y lo len := by
  rw [bitwiseOrBits_eq_or, extractField_toNat, Anneal.BitVecArith.extractBits_or, or_eq_core,
    _root_.BitVec.toNat_or, ← extractField_eq_extractBits hx, ← extractField_eq_extractBits hy]

/-- An in-range value is its own zero-extension at the scalar width. -/
theorem ofNat_eq_setWidth_ofNat {sz len a : Nat} (ha : a < 2 ^ len) :
    BitVec.ofNat (8 * sz) a = Anneal.BitVec.setWidth (8 * sz) (BitVec.ofNat len a) := by
  apply _root_.BitVec.eq_of_toNat_eq
  rw [setWidth_eq_core, _root_.BitVec.toNat_setWidth, _root_.BitVec.toNat_ofNat,
    _root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

/-- A field shifted into place is recovered exactly by `extractField`. -/
theorem extractField_shiftLeftBits_self {sz lo len a : Nat} (ha : a < 2 ^ len)
    (h : lo + len ≤ 8 * sz) :
    extractField sz (shiftLeftBits a lo (scalarModulus sz)) lo len = a := by
  rw [shiftLeftBits_eq_shl, extractField_toNat, ofNat_eq_setWidth_ofNat ha,
    Anneal.BitVecArith.extractBits_shl_setWidth _ h, _root_.BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha]

/-- A field shifted into a disjoint bit range contributes nothing to `extractField`. -/
theorem extractField_shiftLeftBits_disjoint {sz lo₁ len₁ lo₂ len₂ b : Nat} (hb : b < 2 ^ len₂)
    (h₁ : lo₁ + len₁ ≤ 8 * sz) (h₂ : lo₂ + len₂ ≤ 8 * sz)
    (hd : lo₁ + len₁ ≤ lo₂ ∨ lo₂ + len₂ ≤ lo₁) :
    extractField sz (shiftLeftBits b lo₂ (scalarModulus sz)) lo₁ len₁ = 0 := by
  have key :
      Anneal.BitVecArith.extractBits
          (Anneal.BitVec.or
            (Anneal.BitVec.shl (Anneal.BitVec.setWidth (8 * sz) (BitVec.ofNat len₁ 0)) lo₁)
            (Anneal.BitVec.shl (Anneal.BitVec.setWidth (8 * sz) (BitVec.ofNat len₂ b)) lo₂))
          lo₁ len₁ = BitVec.ofNat len₁ 0 :=
    (Anneal.BitVecArith.extractBits_or_disjoint (w := 8 * sz)
      (BitVec.ofNat len₁ 0) (BitVec.ofNat len₂ b) h₁ h₂ hd).1
  have hz : Anneal.BitVec.shl (Anneal.BitVec.setWidth (8 * sz) (BitVec.ofNat len₁ 0)) lo₁ =
      BitVec.ofNat (8 * sz) 0 := by
    apply _root_.BitVec.eq_of_toNat_eq
    simp [shl_eq_core, setWidth_eq_core]
  rw [hz, Anneal.BitVec.zero_or] at key
  rw [shiftLeftBits_eq_shl, extractField_toNat, ofNat_eq_setWidth_ofNat hb, key,
    _root_.BitVec.toNat_ofNat, Nat.zero_mod]

/-- Bitfield recovery (`Anneal.BitVecArith.extractBits_or_disjoint`) on scalars: both fields of
`(a << lo₁) | (b << lo₂)` are recovered by `extractField` when the bit ranges are disjoint. -/
theorem extractField_pack_disjoint {sz lo₁ len₁ lo₂ len₂ a b : Nat}
    (ha : a < 2 ^ len₁) (hb : b < 2 ^ len₂)
    (h₁ : lo₁ + len₁ ≤ 8 * sz) (h₂ : lo₂ + len₂ ≤ 8 * sz)
    (hd : lo₁ + len₁ ≤ lo₂ ∨ lo₂ + len₂ ≤ lo₁) :
    extractField sz
        (bitwiseOrBits (8 * sz) (shiftLeftBits a lo₁ (scalarModulus sz))
          (shiftLeftBits b lo₂ (scalarModulus sz))) lo₁ len₁ = a ∧
      extractField sz
        (bitwiseOrBits (8 * sz) (shiftLeftBits a lo₁ (scalarModulus sz))
          (shiftLeftBits b lo₂ (scalarModulus sz))) lo₂ len₂ = b := by
  have ca := shiftLeftBits_lt_scalarModulus a lo₁ sz
  have cb := shiftLeftBits_lt_scalarModulus b lo₂ sz
  constructor
  · rw [extractField_bitwiseOrBits ca cb, extractField_shiftLeftBits_self ha h₁,
      extractField_shiftLeftBits_disjoint hb h₁ h₂ hd, Nat.or_zero]
  · rw [extractField_bitwiseOrBits ca cb, extractField_shiftLeftBits_self hb h₂,
      extractField_shiftLeftBits_disjoint ha h₂ h₁ hd.symm, Nat.zero_or]

/-- Two-field shift-and-OR packing on scalars is injective on in-range fields with disjoint bit
ranges. -/
theorem pack_disjoint_injective {sz lo₁ len₁ lo₂ len₂ a₁ b₁ a₂ b₂ : Nat}
    (ha₁ : a₁ < 2 ^ len₁) (hb₁ : b₁ < 2 ^ len₂) (ha₂ : a₂ < 2 ^ len₁) (hb₂ : b₂ < 2 ^ len₂)
    (h₁ : lo₁ + len₁ ≤ 8 * sz) (h₂ : lo₂ + len₂ ≤ 8 * sz)
    (hd : lo₁ + len₁ ≤ lo₂ ∨ lo₂ + len₂ ≤ lo₁)
    (h : bitwiseOrBits (8 * sz) (shiftLeftBits a₁ lo₁ (scalarModulus sz))
          (shiftLeftBits b₁ lo₂ (scalarModulus sz)) =
        bitwiseOrBits (8 * sz) (shiftLeftBits a₂ lo₁ (scalarModulus sz))
          (shiftLeftBits b₂ lo₂ (scalarModulus sz))) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have e₁ := extractField_pack_disjoint ha₁ hb₁ h₁ h₂ hd
  have e₂ := extractField_pack_disjoint ha₂ hb₂ h₁ h₂ hd
  rw [h] at e₁
  exact ⟨e₁.1.symm.trans e₂.1, e₁.2.symm.trans e₂.2⟩

/-- The MIR pipeline `(x >> lo) & (2 ^ len - 1)` through `evalBinOp` computes `extractField` on a
canonical operand with an in-range shift amount. -/
theorem evalBinOp_shr_bitAnd_eq_extractField {sz szR : Nat} (hsz : 0 < sz) (hszR : 0 < szR)
    {x lo : Nat} (hx : x < scalarModulus sz) (hlo : lo < 8 * sz) (len : Nat) :
    (Anneal.Scalars.evalBinOp .shr ⟨x, sz⟩ ⟨lo, szR⟩ false).bind
        (fun r => Anneal.Scalars.evalBinOp .bitAnd r ⟨2 ^ len - 1, sz⟩ false) =
      some ⟨extractField sz x lo len, sz⟩ := by
  rw [Anneal.Scalars.evalBinOp_shr_unsigned hsz hszR, Option.bind_some,
    Anneal.Scalars.evalBinOp_bitAnd_apply hsz, Nat.mod_eq_of_lt hlo]
  rw [scalarModulus_eq] at hx
  have hle : x >>> lo ≤ x := Nat.shiftRight_le x lo
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hx)]
  unfold extractField
  rw [Anneal.Scalars.bitwiseAndBits_eq_land, Anneal.Scalars.shiftRightUnsignedBits_eq_shiftRight]

/-- The MIR pipeline `(a << lo₁) | (b << lo₂)` through `evalBinOp` computes the scalar
shift-and-OR pack for in-range shift amounts. -/
theorem evalBinOp_shl_bitOr_eq_pack {sz szR : Nat} (hsz : 0 < sz) (hszR : 0 < szR)
    {lo₁ lo₂ : Nat} (h₁ : lo₁ < 8 * sz) (h₂ : lo₂ < 8 * sz) (a b : Nat) :
    (Anneal.Scalars.evalBinOp .shl ⟨a, sz⟩ ⟨lo₁, szR⟩ false).bind (fun sa =>
        (Anneal.Scalars.evalBinOp .shl ⟨b, sz⟩ ⟨lo₂, szR⟩ false).bind (fun sb =>
          Anneal.Scalars.evalBinOp .bitOr sa sb false)) =
      some ⟨bitwiseOrBits (8 * sz) (shiftLeftBits a lo₁ (scalarModulus sz))
        (shiftLeftBits b lo₂ (scalarModulus sz)), sz⟩ := by
  rw [Anneal.Scalars.evalBinOp_shl_apply hsz hszR, Option.bind_some,
    Anneal.Scalars.evalBinOp_shl_apply hsz hszR, Option.bind_some,
    Anneal.Scalars.evalBinOp_bitOr_apply hsz, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂,
    Anneal.Scalars.bitwiseOrBits_eq_lor, Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod,
    Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod]

/-- Disjoint-mask OR injectivity on `evalBinOp`: if canonical operands are masked apart
(`a & mask = 0`, `b & !mask = 0`, observed through `evalBinOp .bitAnd`), then equal
`evalBinOp .bitOr` results force equal operands. -/
theorem evalBinOp_bitOr_disjoint_injective {sz : Nat} (hsz : 0 < sz)
    {mask a₁ b₁ a₂ b₂ : Nat} (isSigned : Bool)
    (ha₁ : a₁ < scalarModulus sz) (hb₁ : b₁ < scalarModulus sz)
    (ha₂ : a₂ < scalarModulus sz) (hb₂ : b₂ < scalarModulus sz)
    (hm₁ : Anneal.Scalars.evalBinOp .bitAnd ⟨a₁, sz⟩ ⟨mask, sz⟩ isSigned = some ⟨0, sz⟩)
    (hm₂ : Anneal.Scalars.evalBinOp .bitAnd ⟨a₂, sz⟩ ⟨mask, sz⟩ isSigned = some ⟨0, sz⟩)
    (hn₁ : Anneal.Scalars.evalBinOp .bitAnd ⟨b₁, sz⟩
      ⟨bitwiseXorBits (8 * sz) (2 ^ (8 * sz) - 1) mask, sz⟩ isSigned = some ⟨0, sz⟩)
    (hn₂ : Anneal.Scalars.evalBinOp .bitAnd ⟨b₂, sz⟩
      ⟨bitwiseXorBits (8 * sz) (2 ^ (8 * sz) - 1) mask, sz⟩ isSigned = some ⟨0, sz⟩)
    (h : Anneal.Scalars.evalBinOp .bitOr ⟨a₁, sz⟩ ⟨b₁, sz⟩ isSigned =
      Anneal.Scalars.evalBinOp .bitOr ⟨a₂, sz⟩ ⟨b₂, sz⟩ isSigned) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  rw [scalarModulus_eq] at ha₁ hb₁ ha₂ hb₂
  rw [Anneal.Scalars.evalBinOp_bitAnd_apply hsz, ← Anneal.Scalars.bitwiseAndBits_eq_land]
    at hm₁ hm₂ hn₁ hn₂
  rw [Anneal.Scalars.evalBinOp_bitOr_apply hsz, Anneal.Scalars.evalBinOp_bitOr_apply hsz,
    ← Anneal.Scalars.bitwiseOrBits_eq_lor, ← Anneal.Scalars.bitwiseOrBits_eq_lor] at h
  exact bitwiseOrBits_disjoint_injective ha₁ hb₁ ha₂ hb₂
    (ScalarInt.mk.inj (Option.some.inj hm₁)).1 (ScalarInt.mk.inj (Option.some.inj hm₂)).1
    (ScalarInt.mk.inj (Option.some.inj hn₁)).1 (ScalarInt.mk.inj (Option.some.inj hn₂)).1
    (ScalarInt.mk.inj (Option.some.inj h)).1

/-- Shift-and-OR pack injectivity on `evalBinOp`: equal results of the MIR pipeline
`(a << lo₁) | (b << lo₂)` force equal in-range fields when the bit ranges are disjoint. -/
theorem evalBinOp_pack_injective {sz szR : Nat} (hsz : 0 < sz) (hszR : 0 < szR)
    {lo₁ len₁ lo₂ len₂ a₁ b₁ a₂ b₂ : Nat}
    (ha₁ : a₁ < 2 ^ len₁) (hb₁ : b₁ < 2 ^ len₂) (ha₂ : a₂ < 2 ^ len₁) (hb₂ : b₂ < 2 ^ len₂)
    (hl₁ : 0 < len₁) (hl₂ : 0 < len₂)
    (h₁ : lo₁ + len₁ ≤ 8 * sz) (h₂ : lo₂ + len₂ ≤ 8 * sz)
    (hd : lo₁ + len₁ ≤ lo₂ ∨ lo₂ + len₂ ≤ lo₁)
    (h : (Anneal.Scalars.evalBinOp .shl ⟨a₁, sz⟩ ⟨lo₁, szR⟩ false).bind (fun sa =>
          (Anneal.Scalars.evalBinOp .shl ⟨b₁, sz⟩ ⟨lo₂, szR⟩ false).bind (fun sb =>
            Anneal.Scalars.evalBinOp .bitOr sa sb false)) =
        (Anneal.Scalars.evalBinOp .shl ⟨a₂, sz⟩ ⟨lo₁, szR⟩ false).bind (fun sa =>
          (Anneal.Scalars.evalBinOp .shl ⟨b₂, sz⟩ ⟨lo₂, szR⟩ false).bind (fun sb =>
            Anneal.Scalars.evalBinOp .bitOr sa sb false))) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hlo₁ : lo₁ < 8 * sz := by omega
  have hlo₂ : lo₂ < 8 * sz := by omega
  rw [evalBinOp_shl_bitOr_eq_pack hsz hszR hlo₁ hlo₂,
    evalBinOp_shl_bitOr_eq_pack hsz hszR hlo₁ hlo₂] at h
  exact pack_disjoint_injective ha₁ hb₁ ha₂ hb₂ h₁ h₂ hd
    (ScalarInt.mk.inj (Option.some.inj h)).1

/-! ## 5. Abstract-Domain Transfers (`ScalarTnum`, `ScalarRange`, `ScalarSRange`) -/

/-- Tristate-number (tnum) abstraction of a MIR scalar: `sc` is a canonical `sz`-byte scalar
whose bits agree with the reference value `v` on every bit that the mask `m` marks as known
(`m[i] = false`). Canonicality (`sc.bits < scalarModulus sz`) is part of the predicate, so a
non-canonical `ScalarInt` is never abstracted. -/
def ScalarTnum (sz : Nat) (m v : BitVec (8 * sz)) (sc : ScalarInt) : Prop :=
  sc.sizeBytes = sz ∧ sc.bits < scalarModulus sz ∧
    Anneal.BitVec.MaskEq m (BitVec.ofNat (8 * sz) sc.bits) v

/-- Unsigned interval abstraction of a MIR scalar: `sc` is a canonical `sz`-byte scalar whose
bits lie in `[lo, hi]` (unsigned order). -/
def ScalarRange (sz : Nat) (lo hi : BitVec (8 * sz)) (sc : ScalarInt) : Prop :=
  sc.sizeBytes = sz ∧ sc.bits < scalarModulus sz ∧
    lo ≤ BitVec.ofNat (8 * sz) sc.bits ∧ BitVec.ofNat (8 * sz) sc.bits ≤ hi

/-- Signed interval abstraction of a MIR scalar: `sc` is a canonical `sz`-byte scalar whose
bits lie in `[lo, hi]` under the two's-complement order `Anneal.BitVecArith.sle`. -/
def ScalarSRange (sz : Nat) (lo hi : BitVec (8 * sz)) (sc : ScalarInt) : Prop :=
  sc.sizeBytes = sz ∧ sc.bits < scalarModulus sz ∧
    Anneal.BitVecArith.sle lo (BitVec.ofNat (8 * sz) sc.bits) ∧
    Anneal.BitVecArith.sle (BitVec.ofNat (8 * sz) sc.bits) hi

/-- Introduction: the scalar carrying a bitvector satisfies every tnum the bitvector does. -/
theorem scalarTnum_of_bitVec {sz : Nat} {m v : BitVec (8 * sz)} (x : BitVec (8 * sz))
    (h : Anneal.BitVec.MaskEq m x v) : ScalarTnum sz m v ⟨x.toNat, sz⟩ := by
  refine ⟨rfl, toNat_lt_scalarModulus x, ?_⟩
  show Anneal.BitVec.MaskEq m (BitVec.ofNat (8 * sz) x.toNat) v
  rw [ofNat_toNat_self]
  exact h

/-- Elimination: a `ScalarTnum` scalar is literally `⟨bits, sz⟩` with canonical bits. -/
theorem scalarTnum_exists {sz : Nat} {m v : BitVec (8 * sz)} {sc : ScalarInt}
    (h : ScalarTnum sz m v sc) :
    ∃ b, sc = ⟨b, sz⟩ ∧ b < scalarModulus sz ∧
      Anneal.BitVec.MaskEq m (BitVec.ofNat (8 * sz) b) v := by
  cases sc with
  | mk b s =>
    have hs : s = sz := h.1
    subst hs
    exact ⟨b, rfl, h.2.1, h.2.2⟩

/-- A fully-known tnum (`m = 0`) pins the scalar down exactly. -/
theorem scalarTnum_zero_mask_iff {sz : Nat} {v : BitVec (8 * sz)} {sc : ScalarInt} :
    ScalarTnum sz (BitVec.ofNat (8 * sz) 0) v sc ↔ sc = ⟨v.toNat, sz⟩ := by
  constructor
  · intro h
    obtain ⟨b, rfl, hb, hm⟩ := scalarTnum_exists h
    have hv := Anneal.BitVec.maskEq_zero_iff_eq.1 hm
    rw [← hv, toNat_ofNat_of_lt hb]
  · intro h
    subst h
    exact scalarTnum_of_bitVec v (Anneal.BitVec.maskEq_refl _ v)

/-- A fully-unknown tnum (`m = allOnes`) holds of exactly the canonical `sz`-byte scalars. -/
theorem scalarTnum_allOnes_iff {sz : Nat} {v : BitVec (8 * sz)} {sc : ScalarInt} :
    ScalarTnum sz (Anneal.BitVec.allOnes (8 * sz)) v sc ↔
      sc.sizeBytes = sz ∧ sc.bits < scalarModulus sz :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, Anneal.BitVec.maskEq_allOnes _ _⟩⟩

/-- Introduction: the scalar carrying a bitvector lies in every unsigned interval the bitvector
does. -/
theorem scalarRange_of_bitVec {sz : Nat} {lo hi : BitVec (8 * sz)} (x : BitVec (8 * sz))
    (h₁ : lo ≤ x) (h₂ : x ≤ hi) : ScalarRange sz lo hi ⟨x.toNat, sz⟩ := by
  refine ⟨rfl, toNat_lt_scalarModulus x, ?_⟩
  show lo ≤ BitVec.ofNat (8 * sz) x.toNat ∧ BitVec.ofNat (8 * sz) x.toNat ≤ hi
  rw [ofNat_toNat_self]
  exact ⟨h₁, h₂⟩

/-- Elimination: a `ScalarRange` scalar is literally `⟨bits, sz⟩` with canonical bits. -/
theorem scalarRange_exists {sz : Nat} {lo hi : BitVec (8 * sz)} {sc : ScalarInt}
    (h : ScalarRange sz lo hi sc) :
    ∃ b, sc = ⟨b, sz⟩ ∧ b < scalarModulus sz ∧
      lo ≤ BitVec.ofNat (8 * sz) b ∧ BitVec.ofNat (8 * sz) b ≤ hi := by
  cases sc with
  | mk b s =>
    have hs : s = sz := h.1
    subst hs
    exact ⟨b, rfl, h.2.1, h.2.2.1, h.2.2.2⟩

/-- `ScalarRange` on a literal scalar is the natural-number interval test on its bits. -/
theorem scalarRange_iff_bits {sz : Nat} {lo hi : BitVec (8 * sz)} {b : Nat} :
    ScalarRange sz lo hi ⟨b, sz⟩ ↔ b < scalarModulus sz ∧ lo.toNat ≤ b ∧ b ≤ hi.toNat := by
  constructor
  · intro h
    have hb : b < scalarModulus sz := h.2.1
    have h₁ : lo.toNat ≤ (BitVec.ofNat (8 * sz) b).toNat := h.2.2.1
    have h₂ : (BitVec.ofNat (8 * sz) b).toNat ≤ hi.toNat := h.2.2.2
    rw [toNat_ofNat_of_lt hb] at h₁ h₂
    exact ⟨hb, h₁, h₂⟩
  · intro h
    refine ⟨rfl, h.1, ?_, ?_⟩
    · show lo.toNat ≤ (BitVec.ofNat (8 * sz) b).toNat
      rw [toNat_ofNat_of_lt h.1]; exact h.2.1
    · show (BitVec.ofNat (8 * sz) b).toNat ≤ hi.toNat
      rw [toNat_ofNat_of_lt h.1]; exact h.2.2

/-- Introduction: the scalar carrying a bitvector lies in every signed interval the bitvector
does. -/
theorem scalarSRange_of_bitVec {sz : Nat} {lo hi : BitVec (8 * sz)} (x : BitVec (8 * sz))
    (h₁ : Anneal.BitVecArith.sle lo x) (h₂ : Anneal.BitVecArith.sle x hi) :
    ScalarSRange sz lo hi ⟨x.toNat, sz⟩ := by
  refine ⟨rfl, toNat_lt_scalarModulus x, ?_⟩
  show Anneal.BitVecArith.sle lo (BitVec.ofNat (8 * sz) x.toNat) ∧
    Anneal.BitVecArith.sle (BitVec.ofNat (8 * sz) x.toNat) hi
  rw [ofNat_toNat_self]
  exact ⟨h₁, h₂⟩

/-- Elimination: a `ScalarSRange` scalar is literally `⟨bits, sz⟩` with canonical bits. -/
theorem scalarSRange_exists {sz : Nat} {lo hi : BitVec (8 * sz)} {sc : ScalarInt}
    (h : ScalarSRange sz lo hi sc) :
    ∃ b, sc = ⟨b, sz⟩ ∧ b < scalarModulus sz ∧
      Anneal.BitVecArith.sle lo (BitVec.ofNat (8 * sz) b) ∧
      Anneal.BitVecArith.sle (BitVec.ofNat (8 * sz) b) hi := by
  cases sc with
  | mk b s =>
    have hs : s = sz := h.1
    subst hs
    exact ⟨b, rfl, h.2.1, h.2.2.1, h.2.2.2⟩

/-! ### 5.1 Tnum transfers through bitwise operations and shifts -/

/-- Tnum AND transfer on `bitwiseAndBits`. -/
theorem scalarTnum_bitwiseAndBits {sz : Nat} {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ScalarTnum sz
      (Anneal.BitVec.or (Anneal.BitVec.or (Anneal.BitVec.and m₁ m₂) (Anneal.BitVec.and m₁ v₂))
        (Anneal.BitVec.and v₁ m₂))
      (Anneal.BitVec.and v₁ v₂)
      ⟨bitwiseAndBits (8 * sz) x.bits y.bits, sz⟩ := by
  rw [bitwiseAndBits_eq_and]
  exact scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_and_sound hx.2.2 hy.2.2)

/-- Tnum OR transfer on `bitwiseOrBits`. -/
theorem scalarTnum_bitwiseOrBits {sz : Nat} {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ScalarTnum sz
      (Anneal.BitVec.or
        (Anneal.BitVec.or (Anneal.BitVec.and m₁ m₂)
          (Anneal.BitVec.and m₁ (Anneal.BitVec.not v₂)))
        (Anneal.BitVec.and (Anneal.BitVec.not v₁) m₂))
      (Anneal.BitVec.or v₁ v₂)
      ⟨bitwiseOrBits (8 * sz) x.bits y.bits, sz⟩ := by
  rw [bitwiseOrBits_eq_or]
  exact scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_or_sound hx.2.2 hy.2.2)

/-- Tnum XOR transfer on `bitwiseXorBits`. -/
theorem scalarTnum_bitwiseXorBits {sz : Nat} {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ScalarTnum sz (Anneal.BitVec.or m₁ m₂) (Anneal.BitVec.xor v₁ v₂)
      ⟨bitwiseXorBits (8 * sz) x.bits y.bits, sz⟩ := by
  rw [bitwiseXorBits_eq_xor]
  exact scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_xor_sound hx.2.2 hy.2.2)

/-- Tnum left-shift transfer on `shiftLeftBits` (any shift amount). -/
theorem scalarTnum_shiftLeftBits {sz : Nat} {m v : BitVec (8 * sz)} {x : ScalarInt}
    (hx : ScalarTnum sz m v x) (k : Nat) :
    ScalarTnum sz (Anneal.BitVec.shl m k) (Anneal.BitVec.shl v k)
      ⟨shiftLeftBits x.bits k (scalarModulus sz), sz⟩ := by
  rw [shiftLeftBits_eq_shl]
  exact scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_shl_sound k hx.2.2)

/-- Tnum logical-right-shift transfer on `shiftRightUnsignedBits` (any shift amount). -/
theorem scalarTnum_shiftRightUnsignedBits {sz : Nat} {m v : BitVec (8 * sz)} {x : ScalarInt}
    (hx : ScalarTnum sz m v x) (k : Nat) :
    ScalarTnum sz (Anneal.BitVec.ushr m k) (Anneal.BitVec.ushr v k)
      ⟨shiftRightUnsignedBits x.bits k, sz⟩ := by
  rw [shiftRightUnsignedBits_eq_ushr_of_lt hx.2.1]
  exact scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_ushr_sound k hx.2.2)

/-- Tnum arithmetic-right-shift transfer on `arithmeticShrBits` (any shift amount). -/
theorem scalarTnum_arithmeticShrBits {sz : Nat} {m v : BitVec (8 * sz)} {x : ScalarInt}
    (hx : ScalarTnum sz m v x) (k : Nat) :
    ScalarTnum sz (Anneal.BitVecArith.ashr m k) (Anneal.BitVecArith.ashr v k)
      ⟨arithmeticShrBits x.bits sz k, sz⟩ := by
  rw [arithmeticShrBits_eq_ashr]
  exact scalarTnum_of_bitVec _ (Anneal.BitVecArith.tnum_ashr_sound k hx.2.2)

/-- Tnum sign-extension (or truncation) transfer on `signExtendBits` between any byte widths. -/
theorem scalarTnum_signExtendBits {srcSz : Nat} {m v : BitVec (8 * srcSz)} {x : ScalarInt}
    (hx : ScalarTnum srcSz m v x) (dstSz : Nat) :
    ScalarTnum dstSz (Anneal.BitVecArith.signExtend (8 * dstSz) m)
      (Anneal.BitVecArith.signExtend (8 * dstSz) v)
      ⟨signExtendBits x.bits srcSz dstSz, dstSz⟩ := by
  rw [signExtendBits_eq_signExtend]
  exact scalarTnum_of_bitVec _ (Anneal.BitVecArith.tnum_signExtend_sound (8 * dstSz) hx.2.2)

/-- Tnum AND transfer through `evalBinOp .bitAnd`. -/
theorem scalarTnum_evalBinOp_bitAnd {sz : Nat} (hsz : 0 < sz)
    {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt} (isSigned : Bool)
    (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ∃ r, Anneal.Scalars.evalBinOp .bitAnd x y isSigned = some r ∧
      ScalarTnum sz
        (Anneal.BitVec.or (Anneal.BitVec.or (Anneal.BitVec.and m₁ m₂) (Anneal.BitVec.and m₁ v₂))
          (Anneal.BitVec.and v₁ m₂))
        (Anneal.BitVec.and v₁ v₂) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  obtain ⟨yb, rfl, _, hym⟩ := scalarTnum_exists hy
  exact ⟨_, evalBinOp_bitAnd_eq_and hsz xb yb isSigned,
    scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_and_sound hxm hym)⟩

/-- Tnum OR transfer through `evalBinOp .bitOr`. -/
theorem scalarTnum_evalBinOp_bitOr {sz : Nat} (hsz : 0 < sz)
    {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt} (isSigned : Bool)
    (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ∃ r, Anneal.Scalars.evalBinOp .bitOr x y isSigned = some r ∧
      ScalarTnum sz
        (Anneal.BitVec.or
          (Anneal.BitVec.or (Anneal.BitVec.and m₁ m₂)
            (Anneal.BitVec.and m₁ (Anneal.BitVec.not v₂)))
          (Anneal.BitVec.and (Anneal.BitVec.not v₁) m₂))
        (Anneal.BitVec.or v₁ v₂) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  obtain ⟨yb, rfl, _, hym⟩ := scalarTnum_exists hy
  exact ⟨_, evalBinOp_bitOr_eq_or hsz xb yb isSigned,
    scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_or_sound hxm hym)⟩

/-- Tnum XOR transfer through `evalBinOp .bitXor`. -/
theorem scalarTnum_evalBinOp_bitXor {sz : Nat} (hsz : 0 < sz)
    {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt} (isSigned : Bool)
    (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ∃ r, Anneal.Scalars.evalBinOp .bitXor x y isSigned = some r ∧
      ScalarTnum sz (Anneal.BitVec.or m₁ m₂) (Anneal.BitVec.xor v₁ v₂) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  obtain ⟨yb, rfl, _, hym⟩ := scalarTnum_exists hy
  exact ⟨_, evalBinOp_bitXor_eq_xor hsz xb yb isSigned,
    scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_xor_sound hxm hym)⟩

/-- Tnum left-shift transfer through `evalBinOp .shl`; the (concrete) shift amount is the
right operand's bits masked by the left operand's bit width. -/
theorem scalarTnum_evalBinOp_shl {sz : Nat} (hsz : 0 < sz) {m v : BitVec (8 * sz)}
    {x : ScalarInt} (y : ScalarInt) (hy : 0 < y.sizeBytes) (isSigned : Bool)
    (hx : ScalarTnum sz m v x) :
    ∃ r, Anneal.Scalars.evalBinOp .shl x y isSigned = some r ∧
      ScalarTnum sz (Anneal.BitVec.shl m (y.bits % (8 * sz)))
        (Anneal.BitVec.shl v (y.bits % (8 * sz))) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  cases y with
  | mk yb ys =>
    exact ⟨_, evalBinOp_shl_eq_shl hsz hy xb yb isSigned,
      scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_shl_sound _ hxm)⟩

/-- Tnum logical-right-shift transfer through unsigned `evalBinOp .shr`. -/
theorem scalarTnum_evalBinOp_shr_unsigned {sz : Nat} (hsz : 0 < sz) {m v : BitVec (8 * sz)}
    {x : ScalarInt} (y : ScalarInt) (hy : 0 < y.sizeBytes)
    (hx : ScalarTnum sz m v x) :
    ∃ r, Anneal.Scalars.evalBinOp .shr x y false = some r ∧
      ScalarTnum sz (Anneal.BitVec.ushr m (y.bits % (8 * sz)))
        (Anneal.BitVec.ushr v (y.bits % (8 * sz))) r := by
  obtain ⟨xb, rfl, hxb, hxm⟩ := scalarTnum_exists hx
  cases y with
  | mk yb ys =>
    exact ⟨_, evalBinOp_shr_unsigned_eq_ushr hsz hy hxb yb,
      scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_ushr_sound _ hxm)⟩

/-- Tnum arithmetic-right-shift transfer through signed `evalBinOp .shr`. -/
theorem scalarTnum_evalBinOp_shr_signed {sz : Nat} (hsz : 0 < sz) {m v : BitVec (8 * sz)}
    {x : ScalarInt} (y : ScalarInt) (hy : 0 < y.sizeBytes)
    (hx : ScalarTnum sz m v x) :
    ∃ r, Anneal.Scalars.evalBinOp .shr x y true = some r ∧
      ScalarTnum sz (Anneal.BitVecArith.ashr m (y.bits % (8 * sz)))
        (Anneal.BitVecArith.ashr v (y.bits % (8 * sz))) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  cases y with
  | mk yb ys =>
    exact ⟨_, evalBinOp_shr_signed_eq_ashr hsz hy xb yb,
      scalarTnum_of_bitVec _ (Anneal.BitVecArith.tnum_ashr_sound _ hxm)⟩

/-! ### 5.2 Tnum transfers through wrapping addition and subtraction -/

/-- Unknown-bit mask of the carry-propagating tnum sum (`Anneal.BitVecArith.tnum_add_sound_general`,
reference values canonicalized by `v &&& ~~~m`). -/
def tnumAddMask {w : Nat} (m₁ v₁ m₂ v₂ : BitVec w) : BitVec w :=
  Anneal.BitVec.or
    (Anneal.BitVec.xor
      ((m₁ + m₂) +
        (Anneal.BitVec.and v₁ (Anneal.BitVec.not m₁) + Anneal.BitVec.and v₂ (Anneal.BitVec.not m₂)))
      (Anneal.BitVec.and v₁ (Anneal.BitVec.not m₁) + Anneal.BitVec.and v₂ (Anneal.BitVec.not m₂)))
    (Anneal.BitVec.or m₁ m₂)

/-- Reference value of the carry-propagating tnum sum. -/
def tnumAddValue {w : Nat} (m₁ v₁ m₂ v₂ : BitVec w) : BitVec w :=
  Anneal.BitVec.and
    (Anneal.BitVec.and v₁ (Anneal.BitVec.not m₁) + Anneal.BitVec.and v₂ (Anneal.BitVec.not m₂))
    (Anneal.BitVec.not (tnumAddMask m₁ v₁ m₂ v₂))

/-- Unknown-bit mask of the borrow-propagating tnum difference
(`Anneal.BitVecArith.tnum_sub_sound_general`). -/
def tnumSubMask {w : Nat} (m₁ v₁ m₂ v₂ : BitVec w) : BitVec w :=
  Anneal.BitVec.or
    (Anneal.BitVec.xor
      ((Anneal.BitVec.and v₁ (Anneal.BitVec.not m₁) - Anneal.BitVec.and v₂ (Anneal.BitVec.not m₂))
        + m₁)
      ((Anneal.BitVec.and v₁ (Anneal.BitVec.not m₁) - Anneal.BitVec.and v₂ (Anneal.BitVec.not m₂))
        - m₂))
    (Anneal.BitVec.or m₁ m₂)

/-- Reference value of the borrow-propagating tnum difference. -/
def tnumSubValue {w : Nat} (m₁ v₁ m₂ v₂ : BitVec w) : BitVec w :=
  Anneal.BitVec.and
    (Anneal.BitVec.and v₁ (Anneal.BitVec.not m₁) - Anneal.BitVec.and v₂ (Anneal.BitVec.not m₂))
    (Anneal.BitVec.not (tnumSubMask m₁ v₁ m₂ v₂))

/-- Tnum addition soundness in closed form (no `let` telescope, no canonicality side
conditions on the reference values). -/
theorem tnumAdd_sound {w : Nat} {m₁ m₂ x₁ x₂ v₁ v₂ : BitVec w}
    (h₁ : Anneal.BitVec.MaskEq m₁ x₁ v₁) (h₂ : Anneal.BitVec.MaskEq m₂ x₂ v₂) :
    Anneal.BitVec.MaskEq (tnumAddMask m₁ v₁ m₂ v₂) (x₁ + x₂) (tnumAddValue m₁ v₁ m₂ v₂) :=
  Anneal.BitVecArith.tnum_add_sound_general h₁ h₂

/-- Tnum subtraction soundness in closed form. -/
theorem tnumSub_sound {w : Nat} {m₁ m₂ x₁ x₂ v₁ v₂ : BitVec w}
    (h₁ : Anneal.BitVec.MaskEq m₁ x₁ v₁) (h₂ : Anneal.BitVec.MaskEq m₂ x₂ v₂) :
    Anneal.BitVec.MaskEq (tnumSubMask m₁ v₁ m₂ v₂) (x₁ - x₂) (tnumSubValue m₁ v₁ m₂ v₂) :=
  Anneal.BitVecArith.tnum_sub_sound_general h₁ h₂

/-- Tnum addition transfer through `evalBinOp .add`. -/
theorem scalarTnum_evalBinOp_add {sz : Nat} (hsz : 0 < sz)
    {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt} (isSigned : Bool)
    (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ∃ r, Anneal.Scalars.evalBinOp .add x y isSigned = some r ∧
      ScalarTnum sz (tnumAddMask m₁ v₁ m₂ v₂) (tnumAddValue m₁ v₁ m₂ v₂) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  obtain ⟨yb, rfl, _, hym⟩ := scalarTnum_exists hy
  exact ⟨_, evalBinOp_add_eq_add hsz xb yb isSigned,
    scalarTnum_of_bitVec _ (tnumAdd_sound hxm hym)⟩

/-- Tnum subtraction transfer through `evalBinOp .sub`. -/
theorem scalarTnum_evalBinOp_sub {sz : Nat} (hsz : 0 < sz)
    {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt} (isSigned : Bool)
    (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ∃ r, Anneal.Scalars.evalBinOp .sub x y isSigned = some r ∧
      ScalarTnum sz (tnumSubMask m₁ v₁ m₂ v₂) (tnumSubValue m₁ v₁ m₂ v₂) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  obtain ⟨yb, rfl, _, hym⟩ := scalarTnum_exists hy
  exact ⟨_, evalBinOp_sub_eq_sub hsz xb yb isSigned,
    scalarTnum_of_bitVec _ (tnumSub_sound hxm hym)⟩

/-- Tnum addition transfer through the `wrapping_add` intrinsic. -/
theorem scalarTnum_evalWrappingAdd {sz : Nat} (hsz : 0 < sz)
    {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ∃ r, evalWrappingAdd x y = some r ∧
      ScalarTnum sz (tnumAddMask m₁ v₁ m₂ v₂) (tnumAddValue m₁ v₁ m₂ v₂) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  obtain ⟨yb, rfl, _, hym⟩ := scalarTnum_exists hy
  exact ⟨_, evalWrappingAdd_eq_add hsz xb yb, scalarTnum_of_bitVec _ (tnumAdd_sound hxm hym)⟩

/-- Tnum subtraction transfer through the `wrapping_sub` intrinsic. -/
theorem scalarTnum_evalWrappingSub {sz : Nat} (hsz : 0 < sz)
    {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ∃ r, evalWrappingSub x y = some r ∧
      ScalarTnum sz (tnumSubMask m₁ v₁ m₂ v₂) (tnumSubValue m₁ v₁ m₂ v₂) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  obtain ⟨yb, rfl, _, hym⟩ := scalarTnum_exists hy
  exact ⟨_, evalWrappingSub_eq_sub hsz xb yb, scalarTnum_of_bitVec _ (tnumSub_sound hxm hym)⟩

/-! ### 5.3 Empty-abstraction pruning (`arXiv:2611.23584`) -/

/-- Two tnums over the same bitvector are jointly satisfiable exactly when their reference
values agree on every bit both masks mark as known. -/
theorem maskEq_inter_nonempty_iff {w : Nat} {m₁ v₁ m₂ v₂ : BitVec w} :
    (∃ x, Anneal.BitVec.MaskEq m₁ x v₁ ∧ Anneal.BitVec.MaskEq m₂ x v₂) ↔
      Anneal.BitVec.and (Anneal.BitVec.xor v₁ v₂)
        (Anneal.BitVec.and (Anneal.BitVec.not m₁) (Anneal.BitVec.not m₂)) = BitVec.ofNat w 0 := by
  constructor
  · rintro ⟨x, h₁, h₂⟩
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro i hi
    have e₁ := Anneal.BitVec.maskEq_iff_getLsbD.1 h₁ i hi
    have e₂ := Anneal.BitVec.maskEq_iff_getLsbD.1 h₂ i hi
    rw [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_xor, Anneal.BitVec.getLsbD_and,
      Anneal.BitVec.getLsbD_not_of_lt _ hi, Anneal.BitVec.getLsbD_not_of_lt _ hi,
      Anneal.BitVec.getLsbD_zero]
    cases hm₁ : Anneal.BitVec.getLsbD m₁ i with
    | true => simp
    | false =>
      cases hm₂ : Anneal.BitVec.getLsbD m₂ i with
      | true => simp
      | false =>
        rw [← e₁ hm₁, ← e₂ hm₂]
        simp
  · intro h
    refine ⟨Anneal.BitVec.or (Anneal.BitVec.and v₁ (Anneal.BitVec.not m₁))
      (Anneal.BitVec.and v₂ (Anneal.BitVec.not m₂)), ?_, ?_⟩
    · apply Anneal.BitVec.maskEq_iff_getLsbD.2
      intro i hi hm₁
      have hb := congrArg (fun z => Anneal.BitVec.getLsbD z i) h
      simp only [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_xor,
        Anneal.BitVec.getLsbD_not_of_lt _ hi, Anneal.BitVec.getLsbD_zero, hm₁] at hb
      rw [Anneal.BitVec.getLsbD_or, Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_and,
        Anneal.BitVec.getLsbD_not_of_lt _ hi, Anneal.BitVec.getLsbD_not_of_lt _ hi, hm₁]
      cases hv₁ : Anneal.BitVec.getLsbD v₁ i <;> cases hv₂ : Anneal.BitVec.getLsbD v₂ i <;>
        cases hm₂ : Anneal.BitVec.getLsbD m₂ i <;> simp_all
    · apply Anneal.BitVec.maskEq_iff_getLsbD.2
      intro i hi hm₂
      have hb := congrArg (fun z => Anneal.BitVec.getLsbD z i) h
      simp only [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_xor,
        Anneal.BitVec.getLsbD_not_of_lt _ hi, Anneal.BitVec.getLsbD_zero, hm₂] at hb
      rw [Anneal.BitVec.getLsbD_or, Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_and,
        Anneal.BitVec.getLsbD_not_of_lt _ hi, Anneal.BitVec.getLsbD_not_of_lt _ hi, hm₂]
      cases hv₁ : Anneal.BitVec.getLsbD v₁ i <;> cases hv₂ : Anneal.BitVec.getLsbD v₂ i <;>
        cases hm₁ : Anneal.BitVec.getLsbD m₁ i <;> simp_all

/-- Empty-abstraction pruning: if the reference values of two tnums disagree on a bit that
both masks mark as known, no MIR scalar satisfies both abstractions. -/
theorem scalarTnum_empty_of_conflict {sz : Nat} {m₁ v₁ m₂ v₂ : BitVec (8 * sz)}
    (h : Anneal.BitVec.and (Anneal.BitVec.xor v₁ v₂)
      (Anneal.BitVec.and (Anneal.BitVec.not m₁) (Anneal.BitVec.not m₂)) ≠
        BitVec.ofNat (8 * sz) 0) :
    ¬ ∃ sc, ScalarTnum sz m₁ v₁ sc ∧ ScalarTnum sz m₂ v₂ sc := by
  rintro ⟨sc, h₁, h₂⟩
  exact h (maskEq_inter_nonempty_iff.1 ⟨_, h₁.2.2, h₂.2.2⟩)

/-- Pruning is exact: the intersection of two scalar tnums is non-empty precisely when the
conflict vector vanishes, so `scalarTnum_empty_of_conflict` never prunes a satisfiable state
and never keeps an unsatisfiable one. -/
theorem scalarTnum_inter_nonempty_iff {sz : Nat} {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} :
    (∃ sc, ScalarTnum sz m₁ v₁ sc ∧ ScalarTnum sz m₂ v₂ sc) ↔
      Anneal.BitVec.and (Anneal.BitVec.xor v₁ v₂)
        (Anneal.BitVec.and (Anneal.BitVec.not m₁) (Anneal.BitVec.not m₂)) =
          BitVec.ofNat (8 * sz) 0 := by
  constructor
  · rintro ⟨sc, h₁, h₂⟩
    exact maskEq_inter_nonempty_iff.1 ⟨_, h₁.2.2, h₂.2.2⟩
  · intro h
    obtain ⟨x, h₁, h₂⟩ := maskEq_inter_nonempty_iff.2 h
    exact ⟨⟨x.toNat, sz⟩, scalarTnum_of_bitVec x h₁, scalarTnum_of_bitVec x h₂⟩

/-! ### 5.4 Interval transfers -/

/-- Lower endpoint of the wrap-aware unsigned interval sum (`Anneal.BitVec.range_add_sound`). -/
def rangeAddLo {w : Nat} (a_lo a_hi b_lo b_hi : BitVec w) : BitVec w :=
  if (decide (Nat.pow 2 w ≤ a_lo.toNat + b_lo.toNat) !=
      decide (Nat.pow 2 w ≤ a_hi.toNat + b_hi.toNat)) = true
  then BitVec.ofNat w 0 else a_lo + b_lo

/-- Upper endpoint of the wrap-aware unsigned interval sum. -/
def rangeAddHi {w : Nat} (a_lo a_hi b_lo b_hi : BitVec w) : BitVec w :=
  if (decide (Nat.pow 2 w ≤ a_lo.toNat + b_lo.toNat) !=
      decide (Nat.pow 2 w ≤ a_hi.toNat + b_hi.toNat)) = true
  then Anneal.BitVec.allOnes w else a_hi + b_hi

/-- Wrap-aware unsigned interval addition soundness in closed form (no `let` telescope). -/
theorem rangeAdd_sound {w : Nat} {a_lo x a_hi b_lo y b_hi : BitVec w}
    (h₁ : a_lo ≤ x) (h₂ : x ≤ a_hi) (h₃ : b_lo ≤ y) (h₄ : y ≤ b_hi) :
    rangeAddLo a_lo a_hi b_lo b_hi ≤ x + y ∧ x + y ≤ rangeAddHi a_lo a_hi b_lo b_hi :=
  Anneal.BitVec.range_add_sound h₁ h₂ h₃ h₄

/-- Unsigned interval transfer through `evalBinOp .add` (wrap-aware). -/
theorem scalarRange_evalBinOp_add {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt} (isSigned : Bool)
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y) :
    ∃ r, Anneal.Scalars.evalBinOp .add x y isSigned = some r ∧
      ScalarRange sz (rangeAddLo a_lo a_hi b_lo b_hi) (rangeAddHi a_lo a_hi b_lo b_hi) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarRange_exists hy
  have hs := rangeAdd_sound hx₁ hx₂ hy₁ hy₂
  exact ⟨_, evalBinOp_add_eq_add hsz xb yb isSigned, scalarRange_of_bitVec _ hs.1 hs.2⟩

/-- Unsigned interval transfer through the `wrapping_add` intrinsic (wrap-aware). -/
theorem scalarRange_evalWrappingAdd {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y) :
    ∃ r, evalWrappingAdd x y = some r ∧
      ScalarRange sz (rangeAddLo a_lo a_hi b_lo b_hi) (rangeAddHi a_lo a_hi b_lo b_hi) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarRange_exists hy
  have hs := rangeAdd_sound hx₁ hx₂ hy₁ hy₂
  exact ⟨_, evalWrappingAdd_eq_add hsz xb yb, scalarRange_of_bitVec _ hs.1 hs.2⟩

/-- Unsigned interval transfer on `shiftRightUnsignedBits` with a shift amount known to lie in
`[kmin, kmax]` (`Anneal.BitVecArith.range_ushr_sound`). -/
theorem scalarRange_shiftRightUnsignedBits {sz : Nat} {umin umax : BitVec (8 * sz)}
    {x : ScalarInt} {kmin k kmax : Nat}
    (hx : ScalarRange sz umin umax x) (hk₁ : kmin ≤ k) (hk₂ : k ≤ kmax) :
    ScalarRange sz (Anneal.BitVec.ushr umin kmax) (Anneal.BitVec.ushr umax kmin)
      ⟨shiftRightUnsignedBits x.bits k, sz⟩ := by
  rw [shiftRightUnsignedBits_eq_ushr_of_lt hx.2.1]
  have hs := Anneal.BitVecArith.range_ushr_sound hx.2.2.1 hx.2.2.2 hk₁ hk₂
  exact scalarRange_of_bitVec _ hs.1 hs.2

/-- Unsigned interval transfer through unsigned `evalBinOp .shr` with the masked shift amount
known to lie in `[kmin, kmax]`. -/
theorem scalarRange_evalBinOp_shr_unsigned {sz : Nat} (hsz : 0 < sz)
    {umin umax : BitVec (8 * sz)} {x : ScalarInt} (y : ScalarInt) (hy : 0 < y.sizeBytes)
    {kmin kmax : Nat} (hx : ScalarRange sz umin umax x)
    (hk₁ : kmin ≤ y.bits % (8 * sz)) (hk₂ : y.bits % (8 * sz) ≤ kmax) :
    ∃ r, Anneal.Scalars.evalBinOp .shr x y false = some r ∧
      ScalarRange sz (Anneal.BitVec.ushr umin kmax) (Anneal.BitVec.ushr umax kmin) r := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  cases y with
  | mk yb ys =>
    have hs := Anneal.BitVecArith.range_ushr_sound hx₁ hx₂ hk₁ hk₂
    exact ⟨_, evalBinOp_shr_unsigned_eq_ushr hsz hy hxb yb, scalarRange_of_bitVec _ hs.1 hs.2⟩

/-- Signed interval transfer through `evalBinOp .add` when neither signed underflow nor signed
overflow can occur (`Anneal.BitVecArith.signed_range_add_no_overflow_sound`). -/
theorem scalarSRange_evalBinOp_add_no_overflow {sz : Nat} (hsz : 0 < sz)
    {smin₁ smax₁ smin₂ smax₂ : BitVec (8 * sz)} {x y : ScalarInt} (isSigned : Bool)
    (hx : ScalarSRange sz smin₁ smax₁ x) (hy : ScalarSRange sz smin₂ smax₂ y)
    (hno_udf : 2 ^ (8 * sz - 1) ≤
      Anneal.BitVecArith.signedKey smin₁ + Anneal.BitVecArith.signedKey smin₂)
    (hno_ovf : Anneal.BitVecArith.signedKey smax₁ + Anneal.BitVecArith.signedKey smax₂ <
      2 ^ (8 * sz - 1) + 2 ^ (8 * sz)) :
    ∃ r, Anneal.Scalars.evalBinOp .add x y isSigned = some r ∧
      ScalarSRange sz (smin₁ + smin₂) (smax₁ + smax₂) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarSRange_exists hy
  have hs := Anneal.BitVecArith.signed_range_add_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno_udf hno_ovf
  exact ⟨_, evalBinOp_add_eq_add hsz xb yb isSigned, scalarSRange_of_bitVec _ hs.1 hs.2⟩

/-- Signed branch refinement on a taken `signedLt x c` test
(`Anneal.BitVecArith.signed_range_refine_slt`). -/
theorem scalarSRange_refine_signedLt {sz : Nat} {lo hi : BitVec (8 * sz)} {x : ScalarInt}
    (hx : ScalarSRange sz lo hi x) (c : Nat) (hlt : signedLt x.bits c sz = true) :
    ScalarSRange sz lo
      (Anneal.BitVecArith.sbvMin hi (BitVec.ofNat (8 * sz) c - BitVec.ofNat (8 * sz) 1)) x := by
  have hs := Anneal.BitVecArith.signed_range_refine_slt hx.2.2.1 hx.2.2.2
    ((signedLt_eq_true_iff x.bits c sz).1 hlt)
  exact ⟨hx.1, hx.2.1, hs.1, hs.2⟩

/-- Signed branch refinement on a taken `signedLe x c` test
(`Anneal.BitVecArith.signed_range_refine_sle`). -/
theorem scalarSRange_refine_signedLe {sz : Nat} {lo hi : BitVec (8 * sz)} {x : ScalarInt}
    (hx : ScalarSRange sz lo hi x) (c : Nat) (hle : signedLe x.bits c sz = true) :
    ScalarSRange sz lo (Anneal.BitVecArith.sbvMin hi (BitVec.ofNat (8 * sz) c)) x := by
  have hs := Anneal.BitVecArith.signed_range_refine_sle hx.2.2.1 hx.2.2.2
    ((signedLe_eq_true_iff x.bits c sz).1 hle)
  exact ⟨hx.1, hx.2.1, hs.1, hs.2⟩

/-- `boolToScalar` is injective at `true`. -/
theorem boolToScalar_eq_true_iff (b : Bool) : boolToScalar b = boolToScalar true ↔ b = true := by
  cases b with
  | true => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | false =>
    refine ⟨fun h => ?_, fun h => nomatch h⟩
    have h' : (0 : Nat) = 1 := (ScalarInt.mk.inj h).1
    nomatch h'

/-- Signed branch refinement on a taken signed `evalBinOp .lt x c` test. -/
theorem scalarSRange_refine_evalBinOp_lt {sz : Nat} (hsz : 0 < sz) {lo hi : BitVec (8 * sz)}
    {x : ScalarInt} (c : Nat) (hx : ScalarSRange sz lo hi x)
    (hlt : Anneal.Scalars.evalBinOp .lt x ⟨c, sz⟩ true = some (boolToScalar true)) :
    ScalarSRange sz lo
      (Anneal.BitVecArith.sbvMin hi (BitVec.ofNat (8 * sz) c - BitVec.ofNat (8 * sz) 1)) x := by
  obtain ⟨xb, rfl, _, _, _⟩ := scalarSRange_exists hx
  rw [Anneal.Scalars.evalBinOp_lt_signed hsz, ← Anneal.Scalars.signedLt_eq_slt] at hlt
  exact scalarSRange_refine_signedLt hx c ((boolToScalar_eq_true_iff _).1 (Option.some.inj hlt))

/-- Signed branch refinement on a taken signed `evalBinOp .le x c` test. -/
theorem scalarSRange_refine_evalBinOp_le {sz : Nat} (hsz : 0 < sz) {lo hi : BitVec (8 * sz)}
    {x : ScalarInt} (c : Nat) (hx : ScalarSRange sz lo hi x)
    (hle : Anneal.Scalars.evalBinOp .le x ⟨c, sz⟩ true = some (boolToScalar true)) :
    ScalarSRange sz lo (Anneal.BitVecArith.sbvMin hi (BitVec.ofNat (8 * sz) c)) x := by
  obtain ⟨xb, rfl, _, _, _⟩ := scalarSRange_exists hx
  rw [Anneal.Scalars.evalBinOp_le_signed hsz, ← Anneal.Scalars.signedLe_eq_sle] at hle
  exact scalarSRange_refine_signedLe hx c ((boolToScalar_eq_true_iff _).1 (Option.some.inj hle))

/-- Range-to-tnum tightening (`Anneal.BitVec.maskEq_clz_of_bounds`): a scalar in `[umin, umax]`
shares with `umin` every bit above the highest bit where `umin` and `umax` differ. -/
theorem scalarTnum_of_scalarRange_clz {sz : Nat} {umin umax : BitVec (8 * sz)} {x : ScalarInt}
    (hx : ScalarRange sz umin umax x) :
    ScalarTnum sz
      (Anneal.BitVec.lowMask (8 * sz)
        (8 * sz - Anneal.BitVec.clz (Anneal.BitVec.xor umin umax)))
      umin x :=
  ⟨hx.1, hx.2.1, Anneal.BitVec.maskEq_clz_of_bounds hx.2.2.1 hx.2.2.2⟩

/-! ## 6. Intrinsics (`ctlz`, `bswap`) -/

/-! ### 6.1 The duplicated intrinsic loops agree pointwise

`Anneal.Scalars` re-declares `ctpopLoop`, `cttzLoop`, `bitreverseLoop`, `ctlzBits` and
`bswapLoop` separately from `Trusted.Rustc.V2026_06_01.MirSemantics`. The copies are distinct
constants; the lemmas below identify them pointwise. -/

/-- `Anneal.Scalars.ctpopLoop` agrees with the `Trusted` copy. -/
theorem ctpopLoop_eq_trusted : ∀ (n b : Nat),
    Anneal.Scalars.ctpopLoop n b = Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop n b
  | 0, _ => rfl
  | n + 1, b => congrArg (Nat.add (Nat.mod b 2)) (ctpopLoop_eq_trusted n (Nat.div b 2))

/-- `Anneal.Scalars.cttzLoop` agrees with the `Trusted` copy. -/
theorem cttzLoop_eq_trusted : ∀ (n b : Nat),
    Anneal.Scalars.cttzLoop n b = Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop n b
  | 0, _ => rfl
  | n + 1, b => by
    show (match Nat.beq (Nat.mod b 2) 0 with
        | true => Nat.add 1 (Anneal.Scalars.cttzLoop n (Nat.div b 2))
        | false => 0) =
      (match Nat.beq (Nat.mod b 2) 0 with
        | true => Nat.add 1 (Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop n (Nat.div b 2))
        | false => 0)
    rw [cttzLoop_eq_trusted n (Nat.div b 2)]

/-- `Anneal.Scalars.bitreverseLoop` agrees with the `Trusted` copy. -/
theorem bitreverseLoop_eq_trusted : ∀ (n b acc : Nat),
    Anneal.Scalars.bitreverseLoop n b acc =
      Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop n b acc
  | 0, _, _ => rfl
  | n + 1, b, acc => bitreverseLoop_eq_trusted n (Nat.div b 2) (Nat.add (Nat.mul acc 2) (Nat.mod b 2))

/-- `Anneal.Scalars.ctlzBits` agrees with the `Trusted` copy. -/
theorem ctlzBits_eq_trusted (w b : Nat) :
    Anneal.Scalars.ctlzBits w b = Trusted.Rustc.V2026_06_01.MirSemantics.ctlzBits w b := by
  show Anneal.Scalars.cttzLoop w (Anneal.Scalars.bitreverseLoop w b 0) =
    Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop w
      (Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop w b 0)
  rw [bitreverseLoop_eq_trusted, cttzLoop_eq_trusted]

/-- `Anneal.Scalars.bswapLoop` agrees with the `Trusted` copy. -/
theorem bswapLoop_eq_trusted : ∀ (n b acc : Nat),
    Anneal.Scalars.bswapLoop n b acc = Trusted.Rustc.V2026_06_01.MirSemantics.bswapLoop n b acc
  | 0, _, _ => rfl
  | n + 1, b, acc =>
    bswapLoop_eq_trusted n (Nat.div b 256) (Nat.add (Nat.mul acc 256) (Nat.mod b 256))

/-! ### 6.2 `ctlz` -/

/-- Bit characterization of the `Trusted` bit-reversal loop: the low `n` output bits are the low
`n` input bits reversed, and the accumulator is shifted above them. -/
theorem testBit_bitreverseLoop (n b acc j : Nat) :
    (Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop n b acc).testBit j =
      if j < n then b.testBit (n - 1 - j) else acc.testBit (j - n) := by
  induction n generalizing b acc j with
  | zero => rfl
  | succ k ih =>
    have hstep : Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop (k + 1) b acc =
        Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop k (b / 2) (acc * 2 + b % 2) := rfl
    rw [hstep, ih]
    cases Nat.lt_or_ge j k with
    | inl h1 =>
      have h2 : j < k + 1 := by omega
      have h3 : k + 1 - 1 - j = (k - 1 - j) + 1 := by omega
      simp only [h1, h2, ↓reduceIte]
      rw [h3, Nat.testBit_add_one]
    | inr h1 =>
      cases Nat.eq_or_lt_of_le h1 with
      | inl h2 =>
        subst h2
        have h3 : ¬ (k < k) := Nat.lt_irrefl k
        have h4 : k < k + 1 := Nat.lt_succ_self k
        have h5 : k + 1 - 1 - k = 0 := by omega
        simp only [h3, h4, ↓reduceIte, Nat.sub_self]
        rw [h5, Nat.testBit_zero, Nat.testBit_zero]
        have h6 : (acc * 2 + b % 2) % 2 = b % 2 := by omega
        rw [h6]
      | inr h2 =>
        have h3 : ¬ (j < k) := by omega
        have h4 : ¬ (j < k + 1) := by omega
        have h5 : j - k = (j - (k + 1)) + 1 := by omega
        have h6 : (acc * 2 + b % 2) / 2 = acc := by omega
        simp only [h3, h4, ↓reduceIte]
        rw [h5, Nat.testBit_add_one, h6]

/-- The `Trusted` trailing-zero loop on a bit-reversed word is the ported leading-zero count. -/
theorem cttzLoop_eq_clzAux {w : Nat} (x : BitVec w) : ∀ (k y : Nat),
    (∀ j, j < k → y.testBit j = x.toNat.testBit (k - 1 - j)) →
      Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop k y = Anneal.BitVec.clzAux x k
  | 0, _, _ => rfl
  | k + 1, y, h => by
    have hstep : Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop (k + 1) y =
        (match Nat.beq (y % 2) 0 with
          | true => 1 + Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop k (y / 2)
          | false => 0) := rfl
    have hclz : Anneal.BitVec.clzAux x (k + 1) =
        if x.toNat.testBit k then 0 else Anneal.BitVec.clzAux x k + 1 := rfl
    have ih := cttzLoop_eq_clzAux x k (y / 2) (fun j hj => by
      have hj' := h (j + 1) (by omega)
      rw [Nat.testBit_add_one] at hj'
      have hidx : k + 1 - 1 - (j + 1) = k - 1 - j := by omega
      rw [hj', hidx])
    have h0 := h 0 (Nat.succ_pos k)
    have hk : k + 1 - 1 - 0 = k := by omega
    rw [Nat.testBit_zero, hk] at h0
    rw [hstep, hclz, ih, ← h0]
    cases Nat.mod_two_eq_zero_or_one y with
    | inl hy =>
      rw [hy]
      show 1 + Anneal.BitVec.clzAux x k = if decide ((0 : Nat) = 1) = true then 0 else _
      simp only [Nat.zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact Nat.add_comm _ _
    | inr hy =>
      rw [hy]
      rfl

/-- `ctlzBits` (the `Trusted` `ctlz` kernel) is the ported `clz`, at every bit width `w`
(including `w = 0`) and for every `x : BitVec w`. -/
theorem ctlzBits_eq_clz {w : Nat} (x : BitVec w) :
    Trusted.Rustc.V2026_06_01.MirSemantics.ctlzBits w x.toNat = Anneal.BitVec.clz x := by
  show Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop w
      (Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop w x.toNat 0) =
    Anneal.BitVec.clzAux x w
  apply cttzLoop_eq_clzAux
  intro j hj
  rw [testBit_bitreverseLoop]
  simp only [hj, ↓reduceIte]

/-- The theory copy `Anneal.Scalars.ctlzBits` is the ported `clz` as well. -/
theorem scalars_ctlzBits_eq_clz {w : Nat} (x : BitVec w) :
    Anneal.Scalars.ctlzBits w x.toNat = Anneal.BitVec.clz x := by
  rw [ctlzBits_eq_trusted, ctlzBits_eq_clz]

/-- `evalCtlz` returns the ported `clz` of the operand's `8 * sz`-bit vector, for arbitrary
(possibly non-canonical) bits. -/
theorem evalCtlz_eq_clz {sz retBytes : Nat} (hsz : 0 < sz) (hret : 0 < retBytes) (bits : Nat) :
    evalCtlz ⟨bits, sz⟩ retBytes =
      some ⟨Anneal.BitVec.clz (BitVec.ofNat (8 * sz) bits), retBytes⟩ := by
  have h0 : Nat.beq sz 0 = false := beq_zero_of_pos hsz
  have h1 : Nat.beq retBytes 0 = false := beq_zero_of_pos hret
  unfold evalCtlz
  simp only [h0, h1, Bool.or_false]
  rw [natMul_eight, wrapScalarBits_eq_toNat, ctlzBits_eq_clz]

/-- `evalCtlz` is rejected exactly on a zero-width operand or a zero-width return type. -/
theorem evalCtlz_eq_none_iff (sc : ScalarInt) (retBytes : Nat) :
    evalCtlz sc retBytes = none ↔ sc.sizeBytes = 0 ∨ retBytes = 0 := by
  unfold evalCtlz
  cases h0 : Nat.beq sc.sizeBytes 0 with
  | true => exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h0), fun _ => rfl⟩
  | false =>
    have hne : sc.sizeBytes ≠ 0 := fun h => by rw [h] at h0; nomatch h0
    cases h1 : Nat.beq retBytes 0 with
    | true => exact ⟨fun _ => Or.inr (Nat.eq_of_beq_eq_true h1), fun _ => rfl⟩
    | false =>
      have hne' : retBytes ≠ 0 := fun h => by rw [h] at h1; nomatch h1
      refine ⟨fun h => ?_, fun h => ?_⟩
      · cases h
      · cases h with
        | inl h => exact absurd h hne
        | inr h => exact absurd h hne'

/-- The leading-zero count returned by `evalCtlz` never exceeds the operand bit width. -/
theorem evalCtlz_bits_le {sz retBytes : Nat} (hsz : 0 < sz) (hret : 0 < retBytes) (bits : Nat) :
    ∃ r, evalCtlz ⟨bits, sz⟩ retBytes = some r ∧ r.bits ≤ 8 * sz ∧ r.sizeBytes = retBytes :=
  ⟨_, evalCtlz_eq_clz hsz hret bits, Anneal.BitVec.clz_le _, rfl⟩

/-- `evalCtlzNonzero` is undefined behavior (`none`) on a zero operand
(`Anneal.BitVec.clz_eq_width_iff`): for positive widths it is rejected exactly when the ported
leading-zero count equals the full bit width. -/
theorem evalCtlzNonzero_eq_none_iff {sz retBytes : Nat} (hsz : 0 < sz) (hret : 0 < retBytes)
    (bits : Nat) :
    evalCtlzNonzero ⟨bits, sz⟩ retBytes = none ↔
      Anneal.BitVec.clz (BitVec.ofNat (8 * sz) bits) = 8 * sz := by
  have h0 : Nat.beq sz 0 = false := beq_zero_of_pos hsz
  have h1 : Nat.beq retBytes 0 = false := beq_zero_of_pos hret
  rw [Anneal.BitVec.clz_eq_width_iff]
  unfold evalCtlzNonzero
  simp only [h0, h1, Bool.or_false]
  rw [wrapScalarBits_eq_toNat]
  cases hz : Nat.beq (BitVec.ofNat (8 * sz) bits).toNat 0 with
  | true =>
    have hz' : (BitVec.ofNat (8 * sz) bits).toNat = 0 := Nat.eq_of_beq_eq_true hz
    exact ⟨fun _ => Anneal.BitVec.eq_of_toNat_eq (hz'.trans (Anneal.BitVec.toNat_zero _).symm),
      fun _ => rfl⟩
  | false =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h
    · rw [h] at hz
      cases hz

/-- `evalCtlzNonzero` on a zero operand is `none`, at every operand and return width. -/
theorem evalCtlzNonzero_eq_none_of_zero (sc : ScalarInt) (retBytes : Nat)
    (h : BitVec.ofNat (8 * sc.sizeBytes) sc.bits = BitVec.ofNat (8 * sc.sizeBytes) 0) :
    evalCtlzNonzero sc retBytes = none := by
  cases sc with
  | mk bits sz =>
    cases Nat.eq_zero_or_pos sz with
    | inl hsz => subst hsz; rfl
    | inr hsz =>
      cases Nat.eq_zero_or_pos retBytes with
      | inl hret =>
        subst hret
        unfold evalCtlzNonzero
        cases Nat.beq sz 0 <;> rfl
      | inr hret =>
        exact (evalCtlzNonzero_eq_none_iff hsz hret bits).2
          ((Anneal.BitVec.clz_eq_width_iff _).2 h)

/-- `evalCtlzNonzero` on a non-zero operand returns the ported `clz`, which is strictly below the
operand bit width. -/
theorem evalCtlzNonzero_eq_clz {sz retBytes : Nat} (hsz : 0 < sz) (hret : 0 < retBytes)
    {bits : Nat} (hne : BitVec.ofNat (8 * sz) bits ≠ BitVec.ofNat (8 * sz) 0) :
    evalCtlzNonzero ⟨bits, sz⟩ retBytes =
        some ⟨Anneal.BitVec.clz (BitVec.ofNat (8 * sz) bits), retBytes⟩ ∧
      Anneal.BitVec.clz (BitVec.ofNat (8 * sz) bits) < 8 * sz := by
  have h0 : Nat.beq sz 0 = false := beq_zero_of_pos hsz
  have h1 : Nat.beq retBytes 0 = false := beq_zero_of_pos hret
  have hlt : Anneal.BitVec.clz (BitVec.ofNat (8 * sz) bits) < 8 * sz :=
    Nat.lt_of_le_of_ne (Anneal.BitVec.clz_le _)
      (fun h => hne ((Anneal.BitVec.clz_eq_width_iff _).1 h))
  refine ⟨?_, hlt⟩
  have hnz : Nat.beq (BitVec.ofNat (8 * sz) bits).toNat 0 = false :=
    nat_beq_eq_false_of_ne (fun hz =>
      hne (Anneal.BitVec.eq_of_toNat_eq (hz.trans (Anneal.BitVec.toNat_zero _).symm)))
  unfold evalCtlzNonzero
  simp only [h0, h1, Bool.or_false]
  rw [wrapScalarBits_eq_toNat]
  simp only [hnz]
  rw [natMul_eight, ctlzBits_eq_clz]

/-- Range-to-tnum tightening with the mask computed by the MIR `ctlz` kernel on the MIR XOR of
the interval endpoints (`maskEq_clz_of_bounds` end to end on `Trusted` operations). -/
theorem scalarTnum_of_scalarRange_ctlzBits {sz : Nat} {umin umax : BitVec (8 * sz)}
    {x : ScalarInt} (hx : ScalarRange sz umin umax x) :
    ScalarTnum sz
      (Anneal.BitVec.lowMask (8 * sz)
        (8 * sz - Trusted.Rustc.V2026_06_01.MirSemantics.ctlzBits (8 * sz)
          (bitwiseXorBits (8 * sz) umin.toNat umax.toNat)))
      umin x := by
  rw [bitwiseXorBits_toNat, ctlzBits_eq_clz]
  exact scalarTnum_of_scalarRange_clz hx

/-! ### 6.3 `bswap` -/

/-- Closed form of the `Trusted` byte-reversal loop with an arbitrary accumulator. -/
theorem bswapLoop_eq_fromBeBytes_acc : ∀ (n v acc : Nat),
    Trusted.Rustc.V2026_06_01.MirSemantics.bswapLoop n v acc =
      acc * 256 ^ n + Anneal.LeBytes.fromBeBytes (Anneal.LeBytes.toLeBytesAux n v)
  | 0, v, acc => by
    show acc = acc * 256 ^ 0 + Anneal.LeBytes.fromLeBytes ([] : List (BitVec 8)).reverse
    simp
  | n + 1, v, acc => by
    have hstep : Trusted.Rustc.V2026_06_01.MirSemantics.bswapLoop (n + 1) v acc =
        Trusted.Rustc.V2026_06_01.MirSemantics.bswapLoop n (v / 256) (acc * 256 + v % 256) := rfl
    rw [hstep, bswapLoop_eq_fromBeBytes_acc n (v / 256) (acc * 256 + v % 256)]
    unfold Anneal.LeBytes.fromBeBytes
    rw [Anneal.LeBytes.toLeBytesAux_succ, List.reverse_cons, Anneal.LeBytes.fromLeBytes_append,
      List.length_reverse, Anneal.LeBytes.toLeBytesAux_length]
    have h1 : Anneal.LeBytes.fromLeBytes [BitVec.ofNat 8 v] = v % 256 := by
      rw [Anneal.LeBytes.fromLeBytes_cons, Anneal.LeBytes.fromLeBytes_nil,
        _root_.BitVec.toNat_ofNat]
      rfl
    have h2 : (2 : Nat) ^ (n * 8) = 256 ^ n := by
      rw [Nat.mul_comm, Nat.pow_mul]
    rw [h1, h2, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ n),
      Nat.mul_comm (v % 256) (256 ^ n)]
    omega

/-- The `Trusted` byte-reversal loop is big-endian reassembly of the little-endian byte list,
for every byte count `n` and every (possibly out-of-range) `v`. -/
theorem bswapLoop_eq_fromBeBytes (n v : Nat) :
    Trusted.Rustc.V2026_06_01.MirSemantics.bswapLoop n v 0 =
      Anneal.LeBytes.fromBeBytes (Anneal.LeBytes.toLeBytesAux n v) := by
  rw [bswapLoop_eq_fromBeBytes_acc, Nat.zero_mul, Nat.zero_add]

/-- Bit characterization of little-endian reassembly: bit `i` of `fromLeBytes bs` is bit `i % 8`
of byte `i / 8` (and `false` past the end of the list). -/
theorem testBit_fromLeBytes : ∀ (bs : List (BitVec 8)) (i : Nat),
    (Anneal.LeBytes.fromLeBytes bs).testBit i =
      ((bs[i / 8]?).getD (BitVec.ofNat 8 0)).toNat.testBit (i % 8)
  | [], i => by simp
  | b :: rest, i => by
    rw [Anneal.LeBytes.fromLeBytes_cons]
    have hb : b.toNat < 2 ^ 8 := b.isLt
    have hcomm : b.toNat + 256 * Anneal.LeBytes.fromLeBytes rest =
        2 ^ 8 * Anneal.LeBytes.fromLeBytes rest + b.toNat := by
      rw [Nat.add_comm]
    rw [hcomm, Nat.testBit_two_pow_mul_add _ hb]
    cases Nat.lt_or_ge i 8 with
    | inl hi =>
      have h1 : i / 8 = 0 := by omega
      have h2 : i % 8 = i := by omega
      simp only [hi, ↓reduceIte, h1, h2, List.getElem?_cons_zero, Option.getD_some]
    | inr hi =>
      have h1 : ¬ (i < 8) := by omega
      have h2 : i / 8 = (i - 8) / 8 + 1 := by omega
      have h3 : i % 8 = (i - 8) % 8 := by omega
      simp only [h1, ↓reduceIte]
      rw [testBit_fromLeBytes rest (i - 8), h2, h3, List.getElem?_cons_succ]

/-- The ported `bswapBytes` is big-endian reassembly of the little-endian byte list, for every
byte count `n` (including `n = 0`) and every `x : BitVec (8 * n)`. -/
theorem toNat_bswapBytes_eq_fromBeBytes (n : Nat) (x : BitVec (8 * n)) :
    (Anneal.BitVecArith.bswapBytes n x).toNat =
      Anneal.LeBytes.fromBeBytes (Anneal.LeBytes.toLeBytesAux n x.toNat) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hl : (Anneal.BitVecArith.bswapBytes n x).toNat.testBit i =
      Anneal.BitVec.getLsbD (Anneal.BitVecArith.bswapBytes n x) i := rfl
  rw [hl, Anneal.BitVecArith.getLsbD_bswapBytes]
  unfold Anneal.LeBytes.fromBeBytes
  rw [testBit_fromLeBytes]
  cases Nat.lt_or_ge i (8 * n) with
  | inl hi =>
    have hj : i / 8 < n := by omega
    have hlen : i / 8 < (Anneal.LeBytes.toLeBytesAux n x.toNat).length := by
      rw [Anneal.LeBytes.toLeBytesAux_length]; exact hj
    have hr : i % 8 < 8 := Nat.mod_lt _ (by decide)
    rw [List.getElem?_reverse hlen, Anneal.LeBytes.toLeBytesAux_length,
      Anneal.LeBytes.toLeBytes_getElem? n x.toNat (n - 1 - i / 8) (by omega),
      Option.getD_some, _root_.BitVec.toNat_ofNat, Nat.testBit_mod_two_pow,
      Nat.testBit_div_two_pow]
    simp only [hi, hr, decide_true, Bool.true_and]
    show x.toNat.testBit (i % 8 + 8 * (n - 1 - i / 8)) = _
    rw [Nat.add_comm]
  | inr hi =>
    have h1 : ¬ (i < 8 * n) := by omega
    have hlen : (Anneal.LeBytes.toLeBytesAux n x.toNat).reverse.length ≤ i / 8 := by
      rw [List.length_reverse, Anneal.LeBytes.toLeBytesAux_length]; omega
    rw [List.getElem?_eq_none hlen]
    simp [h1]

/-- The ported `bswapBytes` is the `Trusted` byte-reversal loop, for every byte count `n`
(including `n = 0`) and every `x : BitVec (8 * n)`. -/
theorem toNat_bswapBytes_eq_bswapLoop (n : Nat) (x : BitVec (8 * n)) :
    (Anneal.BitVecArith.bswapBytes n x).toNat =
      Trusted.Rustc.V2026_06_01.MirSemantics.bswapLoop n x.toNat 0 := by
  rw [toNat_bswapBytes_eq_fromBeBytes, bswapLoop_eq_fromBeBytes]

/-- `evalBswap` computes the ported `bswapBytes`, for arbitrary (possibly non-canonical) bits. -/
theorem evalBswap_eq_bswapBytes {sz : Nat} (hsz : 0 < sz) (bits : Nat) :
    evalBswap ⟨bits, sz⟩ =
      some ⟨(Anneal.BitVecArith.bswapBytes sz (BitVec.ofNat (8 * sz) bits)).toNat, sz⟩ := by
  have h0 : Nat.beq sz 0 = false := beq_zero_of_pos hsz
  unfold evalBswap
  simp only [h0]
  rw [toNat_bswapBytes_eq_bswapLoop, wrapScalarBits_eq_toNat]

/-- `evalBswap` is rejected exactly on a zero-width operand. -/
theorem evalBswap_eq_none_iff (sc : ScalarInt) : evalBswap sc = none ↔ sc.sizeBytes = 0 := by
  unfold evalBswap
  cases h0 : Nat.beq sc.sizeBytes 0 with
  | true => exact ⟨fun _ => Nat.eq_of_beq_eq_true h0, fun _ => rfl⟩
  | false =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h
    · rw [h] at h0
      cases h0

/-- `evalBswap` is an involution on canonical scalars. -/
theorem evalBswap_evalBswap {sz : Nat} (hsz : 0 < sz) {bits : Nat}
    (hb : bits < scalarModulus sz) :
    (evalBswap ⟨bits, sz⟩).bind evalBswap = some ⟨bits, sz⟩ := by
  rw [evalBswap_eq_bswapBytes hsz, Option.bind_some, evalBswap_eq_bswapBytes hsz,
    ofNat_toNat_self, Anneal.BitVecArith.bswapBytes_bswapBytes, toNat_ofNat_of_lt hb]

/-- Tnum transfer through the `bswap` intrinsic. -/
theorem scalarTnum_evalBswap {sz : Nat} (hsz : 0 < sz) {m v : BitVec (8 * sz)} {x : ScalarInt}
    (hx : ScalarTnum sz m v x) :
    ∃ r, evalBswap x = some r ∧
      ScalarTnum sz (Anneal.BitVecArith.bswapBytes sz m) (Anneal.BitVecArith.bswapBytes sz v) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  exact ⟨_, evalBswap_eq_bswapBytes hsz xb,
    scalarTnum_of_bitVec _ (Anneal.BitVecArith.tnum_bswapBytes_sound sz hxm)⟩

/-- `Anneal.Scalars.swapBytes16` is the ported `bswap16`, for arbitrary `n`. -/
theorem swapBytes16_eq_bswap16 (n : Nat) :
    Anneal.Scalars.swapBytes16 n = (Anneal.BitVecArith.bswap16 (BitVec.ofNat 16 n)).toNat := by
  have h : (Anneal.BitVecArith.bswap16 (BitVec.ofNat 16 n)).toNat =
      Anneal.Scalars.swapBytes16 (n % 65536) := by
    show (Anneal.BitVecArith.bswapBytes 2 (BitVec.ofNat (8 * 2) n)).toNat = _
    rw [toNat_bswapBytes_eq_bswapLoop, ← bswapLoop_eq_trusted,
      Anneal.Scalars.bswapLoop_two_eq_swapBytes16, _root_.BitVec.toNat_ofNat]
  rw [h]
  unfold Anneal.Scalars.swapBytes16
  omega

/-- `Anneal.Scalars.swapBytes32` is the ported `bswap32`, for arbitrary `n`. -/
theorem swapBytes32_eq_bswap32 (n : Nat) :
    Anneal.Scalars.swapBytes32 n = (Anneal.BitVecArith.bswap32 (BitVec.ofNat 32 n)).toNat := by
  have h : (Anneal.BitVecArith.bswap32 (BitVec.ofNat 32 n)).toNat =
      Anneal.Scalars.swapBytes32 (n % 4294967296) := by
    show (Anneal.BitVecArith.bswapBytes 4 (BitVec.ofNat (8 * 4) n)).toNat = _
    rw [toNat_bswapBytes_eq_bswapLoop, ← bswapLoop_eq_trusted,
      Anneal.Scalars.bswapLoop_four_eq_swapBytes32, _root_.BitVec.toNat_ofNat]
  rw [h]
  unfold Anneal.Scalars.swapBytes32
  omega

/-- `Anneal.Scalars.swapBytes64` is the ported `bswap64`, for arbitrary `n`. -/
theorem swapBytes64_eq_bswap64 (n : Nat) :
    Anneal.Scalars.swapBytes64 n = (Anneal.BitVecArith.bswap64 (BitVec.ofNat 64 n)).toNat := by
  have h : (Anneal.BitVecArith.bswap64 (BitVec.ofNat 64 n)).toNat =
      Anneal.Scalars.swapBytes64 (n % 18446744073709551616) := by
    show (Anneal.BitVecArith.bswapBytes 8 (BitVec.ofNat (8 * 8) n)).toNat = _
    rw [toNat_bswapBytes_eq_bswapLoop, ← bswapLoop_eq_trusted,
      Anneal.Scalars.bswapLoop_eight_eq_swapBytes64, _root_.BitVec.toNat_ofNat]
  rw [h]
  unfold Anneal.Scalars.swapBytes64
  omega

/-- The ported `bswap16` on a bitvector is `Anneal.Scalars.swapBytes16` on its bits. -/
theorem toNat_bswap16 (x : BitVec 16) :
    (Anneal.BitVecArith.bswap16 x).toNat = Anneal.Scalars.swapBytes16 x.toNat := by
  rw [swapBytes16_eq_bswap16, ofNat_toNat_self]

/-- The ported `bswap32` on a bitvector is `Anneal.Scalars.swapBytes32` on its bits. -/
theorem toNat_bswap32 (x : BitVec 32) :
    (Anneal.BitVecArith.bswap32 x).toNat = Anneal.Scalars.swapBytes32 x.toNat := by
  rw [swapBytes32_eq_bswap32, ofNat_toNat_self]

/-- The ported `bswap64` on a bitvector is `Anneal.Scalars.swapBytes64` on its bits. -/
theorem toNat_bswap64 (x : BitVec 64) :
    (Anneal.BitVecArith.bswap64 x).toNat = Anneal.Scalars.swapBytes64 x.toNat := by
  rw [swapBytes64_eq_bswap64, ofNat_toNat_self]

/-- `evalBswap` at 2 bytes is `Anneal.Scalars.swapBytes16` (arbitrary bits). -/
theorem evalBswap_two (bits : Nat) :
    evalBswap ⟨bits, 2⟩ = some ⟨Anneal.Scalars.swapBytes16 bits, 2⟩ := by
  rw [evalBswap_eq_bswapBytes (by decide), swapBytes16_eq_bswap16]
  rfl

/-- `evalBswap` at 4 bytes is `Anneal.Scalars.swapBytes32` (arbitrary bits). -/
theorem evalBswap_four (bits : Nat) :
    evalBswap ⟨bits, 4⟩ = some ⟨Anneal.Scalars.swapBytes32 bits, 4⟩ := by
  rw [evalBswap_eq_bswapBytes (by decide), swapBytes32_eq_bswap32]
  rfl

/-- `evalBswap` at 8 bytes is `Anneal.Scalars.swapBytes64` (arbitrary bits). -/
theorem evalBswap_eight (bits : Nat) :
    evalBswap ⟨bits, 8⟩ = some ⟨Anneal.Scalars.swapBytes64 bits, 8⟩ := by
  rw [evalBswap_eq_bswapBytes (by decide), swapBytes64_eq_bswap64]
  rfl

/-! ## 7. Little-Endian Byte Serialization -/

/-- Embed a `BitVec 8` byte as an initialized `AbstractByte` carrying provenance `prov`
(`none` by default). -/
def bvByteToAbstract (prov : Option (Nat × Nat) := none) (b : BitVec 8) : AbstractByte :=
  .init (UInt8.ofBitVec b) prov

/-- Extract the payload of every initialized byte, in order, skipping `.uninit` bytes. On a
fully initialized list (`allBytesInitialized bs = true`) this is the exact inverse of
`List.map (bvByteToAbstract prov)` up to provenance (`length_extractInitBvBytes_eq_iff`,
`extractInitBvBytes_map`, `map_extractInitBvBytes_of_uniform`). -/
def extractInitBvBytes : List AbstractByte → List (BitVec 8)
  | [] => []
  | .uninit :: rest => extractInitBvBytes rest
  | .init b _ :: rest => b.toBitVec :: extractInitBvBytes rest

/-- `bvByteToAbstract` is injective in the byte. -/
theorem bvByteToAbstract_injective {prov : Option (Nat × Nat)} {a b : BitVec 8}
    (h : bvByteToAbstract prov a = bvByteToAbstract prov b) : a = b := by
  have h' : UInt8.ofBitVec a = UInt8.ofBitVec b := (AbstractByte.init.inj h).1
  exact UInt8.ofBitVec.inj h'

/-- Byte lists embedded by `bvByteToAbstract` are fully initialized. -/
theorem allBytesInitialized_map_bvByteToAbstract (prov : Option (Nat × Nat)) :
    ∀ bs : List (BitVec 8), allBytesInitialized (bs.map (bvByteToAbstract prov)) = true
  | [] => rfl
  | _ :: rest => allBytesInitialized_map_bvByteToAbstract prov rest

/-- Left inverse: extraction undoes the embedding, for every provenance. -/
theorem extractInitBvBytes_map (prov : Option (Nat × Nat)) :
    ∀ bs : List (BitVec 8), extractInitBvBytes (bs.map (bvByteToAbstract prov)) = bs
  | [] => rfl
  | b :: rest => congrArg (b :: ·) (extractInitBvBytes_map prov rest)

/-- The embedding is injective on byte lists. -/
theorem map_bvByteToAbstract_injective {prov : Option (Nat × Nat)} {bs cs : List (BitVec 8)}
    (h : bs.map (bvByteToAbstract prov) = cs.map (bvByteToAbstract prov)) : bs = cs := by
  have h' := congrArg extractInitBvBytes h
  rwa [extractInitBvBytes_map, extractInitBvBytes_map] at h'

/-- Extraction never lengthens the list. -/
theorem length_extractInitBvBytes_le :
    ∀ bs : List AbstractByte, (extractInitBvBytes bs).length ≤ bs.length
  | [] => Nat.le_refl 0
  | .uninit :: rest => Nat.le_succ_of_le (length_extractInitBvBytes_le rest)
  | .init _ _ :: rest => Nat.succ_le_succ (length_extractInitBvBytes_le rest)

/-- Extraction preserves length exactly on fully initialized lists: a single `.uninit` byte is
detected by a length drop. -/
theorem length_extractInitBvBytes_eq_iff :
    ∀ bs : List AbstractByte,
      (extractInitBvBytes bs).length = bs.length ↔ allBytesInitialized bs = true
  | [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | .uninit :: rest => by
    have hle := length_extractInitBvBytes_le rest
    constructor
    · intro h
      have h' : (extractInitBvBytes rest).length = rest.length + 1 := h
      omega
    · intro h
      cases h
  | .init b p :: rest => by
    have ih := length_extractInitBvBytes_eq_iff rest
    constructor
    · intro h
      have h' : (extractInitBvBytes rest).length + 1 = rest.length + 1 := h
      exact ih.1 (Nat.succ.inj h')
    · intro h
      have h' : allBytesInitialized rest = true := h
      show (extractInitBvBytes rest).length + 1 = rest.length + 1
      rw [ih.2 h']

/-- Right inverse: on a list whose bytes are all initialized with the same provenance,
re-embedding the extracted payload reproduces the list exactly. -/
theorem map_extractInitBvBytes_of_uniform (prov : Option (Nat × Nat)) :
    ∀ bs : List AbstractByte, (∀ b ∈ bs, ∃ byte, b = AbstractByte.init byte prov) →
      (extractInitBvBytes bs).map (bvByteToAbstract prov) = bs
  | [], _ => rfl
  | b :: rest, h => by
    obtain ⟨byte, hb⟩ := h b List.mem_cons_self
    subst hb
    have ih := map_extractInitBvBytes_of_uniform prov rest
      (fun c hc => h c (List.mem_cons_of_mem _ hc))
    show bvByteToAbstract prov byte.toBitVec ::
        (extractInitBvBytes rest).map (bvByteToAbstract prov) = _
    rw [ih]
    rfl

/-- `encodeLittleEndianBytes` is the embedded `Anneal.LeBytes.toLeBytesAux` byte list, for every
byte count (including `n = 0`), every (possibly out-of-range) `bits` and every provenance. Note
the argument orders: `encodeLittleEndianBytes bits n` vs `toLeBytesAux n bits`. -/
theorem encodeLittleEndianBytes_eq_map (prov : Option (Nat × Nat)) : ∀ (n bits : Nat),
    encodeLittleEndianBytes bits n prov =
      (Anneal.LeBytes.toLeBytesAux n bits).map (bvByteToAbstract prov)
  | 0, _ => rfl
  | n + 1, bits =>
    congrArg (List.cons (bvByteToAbstract prov (BitVec.ofNat 8 bits)))
      (encodeLittleEndianBytes_eq_map prov n (Nat.div bits 256))

/-- `encodeLittleEndianBytes` on a `BitVec (n * 8)` is the embedded `Anneal.LeBytes.toLeBytes`. -/
theorem encodeLittleEndianBytes_toLeBytes (n : Nat) (x : BitVec (n * 8))
    (prov : Option (Nat × Nat)) :
    encodeLittleEndianBytes x.toNat n prov =
      (Anneal.LeBytes.toLeBytes n x).map (bvByteToAbstract prov) :=
  encodeLittleEndianBytes_eq_map prov n x.toNat

/-- `decodeLittleEndianBytes` on an embedded byte list is `Anneal.LeBytes.fromLeBytes`; the
merged provenance is the uniform provenance (or `none` on the empty list). -/
theorem decodeLittleEndianBytes_map (prov : Option (Nat × Nat)) : ∀ (bs : List (BitVec 8)),
    decodeLittleEndianBytes (bs.map (bvByteToAbstract prov)) =
      some (Anneal.LeBytes.fromLeBytes bs, match bs with | [] => none | _ :: _ => prov)
  | [] => rfl
  | b :: rest => by
    have hstep : decodeLittleEndianBytes ((b :: rest).map (bvByteToAbstract prov)) =
        (match decodeLittleEndianBytes (rest.map (bvByteToAbstract prov)) with
          | some (highBits, restProv) =>
            some (b.toNat + 256 * highBits, mergeByteProvenance prov restProv)
          | none => none) := rfl
    rw [hstep, decodeLittleEndianBytes_map prov rest]
    cases rest with
    | nil => cases prov <;> rfl
    | cons c r => cases prov <;> rfl

/-- `decodeLittleEndianBytes` on a provenance-free embedded byte list. -/
theorem decodeLittleEndianBytes_map_none (bs : List (BitVec 8)) :
    decodeLittleEndianBytes (bs.map (bvByteToAbstract none)) =
      some (Anneal.LeBytes.fromLeBytes bs, none) := by
  rw [decodeLittleEndianBytes_map]
  cases bs <;> rfl

/-- On any fully initialized byte list (arbitrary, possibly mixed provenance),
`decodeLittleEndianBytes` returns `fromLeBytes` of the extracted payload. -/
theorem decodeLittleEndianBytes_of_init : ∀ (bs : List AbstractByte),
    allBytesInitialized bs = true →
      ∃ prov, decodeLittleEndianBytes bs =
        some (Anneal.LeBytes.fromLeBytes (extractInitBvBytes bs), prov)
  | [], _ => ⟨none, rfl⟩
  | .uninit :: _, h => nomatch h
  | .init b p :: rest, h => by
    obtain ⟨q, hq⟩ := decodeLittleEndianBytes_of_init rest h
    have hstep : decodeLittleEndianBytes (.init b p :: rest) =
        (match decodeLittleEndianBytes rest with
          | some (highBits, restProv) =>
            some (b.toBitVec.toNat + 256 * highBits, mergeByteProvenance p restProv)
          | none => none) := rfl
    exact ⟨mergeByteProvenance p q, by rw [hstep, hq]; rfl⟩

/-- A single `.uninit` byte anywhere in the list poisons `decodeLittleEndianBytes`. -/
theorem decodeLittleEndianBytes_eq_none_of_uninit : ∀ (bs : List AbstractByte),
    allBytesInitialized bs = false → decodeLittleEndianBytes bs = none
  | [], h => nomatch h
  | .uninit :: _, _ => rfl
  | .init b p :: rest, h => by
    have hstep : decodeLittleEndianBytes (.init b p :: rest) =
        (match decodeLittleEndianBytes rest with
          | some (highBits, restProv) =>
            some (b.toBitVec.toNat + 256 * highBits, mergeByteProvenance p restProv)
          | none => none) := rfl
    rw [hstep, decodeLittleEndianBytes_eq_none_of_uninit rest h]

/-- `decodeLittleEndianBytes` fails exactly on lists containing an `.uninit` byte. -/
theorem decodeLittleEndianBytes_eq_none_iff (bs : List AbstractByte) :
    decodeLittleEndianBytes bs = none ↔ allBytesInitialized bs = false := by
  constructor
  · intro h
    cases hi : allBytesInitialized bs with
    | false => rfl
    | true =>
      obtain ⟨p, hp⟩ := decodeLittleEndianBytes_of_init bs hi
      rw [hp] at h
      cases h
  · exact decodeLittleEndianBytes_eq_none_of_uninit bs

/-- `decodeScalarBytes` on a non-empty embedded byte list is `fromLeBytes` at the list's
length. -/
theorem decodeScalarBytes_map (prov : Option (Nat × Nat)) {bs : List (BitVec 8)}
    (hne : bs ≠ []) (signed : Bool) :
    decodeScalarBytes (bs.map (bvByteToAbstract prov)) signed =
      some (⟨Anneal.LeBytes.fromLeBytes bs, bs.length⟩, prov) := by
  cases bs with
  | nil => exact absurd rfl hne
  | cons b rest =>
    have hlen : Trusted.Sequence.length ((b :: rest).map (bvByteToAbstract prov)) =
        (b :: rest).length := List.length_map _
    unfold decodeScalarBytes
    rw [hlen, decodeLittleEndianBytes_map]
    rfl

/-- `decodeScalarBytes` on a non-empty provenance-free embedded byte list. -/
theorem decodeScalarBytes_map_none {bs : List (BitVec 8)} (hne : bs ≠ []) (signed : Bool) :
    decodeScalarBytes (bs.map (bvByteToAbstract none)) signed =
      some (⟨Anneal.LeBytes.fromLeBytes bs, bs.length⟩, none) :=
  decodeScalarBytes_map none hne signed

/-- `decodeScalarBytes` rejects the empty byte list (a zero-width scalar is not a scalar). -/
theorem decodeScalarBytes_nil (signed : Bool) : decodeScalarBytes [] signed = none := rfl

/-- `decodeScalarBytes` rejects any list containing an `.uninit` byte. -/
theorem decodeScalarBytes_eq_none_of_uninit {bs : List AbstractByte}
    (h : allBytesInitialized bs = false) (signed : Bool) :
    decodeScalarBytes bs signed = none := by
  unfold decodeScalarBytes
  dsimp only
  rw [decodeLittleEndianBytes_eq_none_of_uninit bs h]
  cases Nat.beq (Trusted.Sequence.length bs) 0 <;> rfl

/-- Scalar round trip through the byte lists: decoding the little-endian encoding of `v` at a
positive width `n` returns `v` reduced modulo `2 ^ (n * 8)` (so a non-canonical `v` is
canonicalized, never rejected). -/
theorem decodeScalarBytes_encodeLittleEndianBytes {n : Nat} (hn : 0 < n) (v : Nat)
    (prov : Option (Nat × Nat)) (signed : Bool) :
    decodeScalarBytes (encodeLittleEndianBytes v n prov) signed =
      some (⟨v % 2 ^ (n * 8), n⟩, prov) := by
  have hne : Anneal.LeBytes.toLeBytesAux n v ≠ [] := by
    intro h
    have hl := Anneal.LeBytes.toLeBytesAux_length n v
    rw [h] at hl
    have hl' : 0 = n := hl
    omega
  rw [encodeLittleEndianBytes_eq_map, decodeScalarBytes_map prov hne,
    Anneal.LeBytes.fromLeBytes_toLeBytesAux, Anneal.LeBytes.toLeBytesAux_length]

/-- `toLeBytesAux` only depends on the low `n * 8` bits. -/
theorem toLeBytesAux_mod (n v : Nat) :
    Anneal.LeBytes.toLeBytesAux n (v % 2 ^ (n * 8)) = Anneal.LeBytes.toLeBytesAux n v := by
  have h := Anneal.LeBytes.toLeBytesAux_fromLeBytes (Anneal.LeBytes.toLeBytesAux n v)
  rw [Anneal.LeBytes.toLeBytesAux_length, Anneal.LeBytes.fromLeBytes_toLeBytesAux] at h
  exact h

/-- Concatenating the little-endian bytes of an `m`-byte value and an `n`-byte value gives the
little-endian bytes of the `(m + n)`-byte value `a + 2 ^ (m * 8) * b`
(`Anneal.LeBytes.toLeBytesAux_add` / `fromLeBytes_append` read right to left). -/
theorem toLeBytesAux_append {m : Nat} (n : Nat) {a : Nat} (ha : a < 2 ^ (m * 8)) (b : Nat) :
    Anneal.LeBytes.toLeBytesAux m a ++ Anneal.LeBytes.toLeBytesAux n b =
      Anneal.LeBytes.toLeBytesAux (m + n) (a + 2 ^ (m * 8) * b) := by
  have hpos : 0 < 2 ^ (m * 8) := Nat.two_pow_pos _
  have hmod : (a + 2 ^ (m * 8) * b) % 2 ^ (m * 8) = a := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have hdiv : (a + 2 ^ (m * 8) * b) / 2 ^ (m * 8) = b := by
    rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt ha, Nat.zero_add]
  rw [Anneal.LeBytes.toLeBytesAux_add, hdiv, ← toLeBytesAux_mod m (a + 2 ^ (m * 8) * b), hmod]

/-! ## 8. `bitVecLE`: Fixed-Width Little-Endian Codec for `BitVec (8 * sz)` -/

/-- Fixed-width little-endian codec for `BitVec (8 * sz)` at positive byte width `sz`, obtained
from `Anneal.ByteCodec.FixedByteCodec.uintBitsLE` by transporting along
`{ bits // bits < 2 ^ (8 * sz) } ≃ BitVec (8 * sz)`. -/
def bitVecLE (sz : Nat) (hNz : 0 < sz) : FixedByteCodec (BitVec (8 * sz)) sz :=
  (FixedByteCodec.uintBitsLE sz hNz).mapEquiv
    (fun b => BitVec.ofNatLT b.val b.property)
    (fun x => ⟨x.toNat, x.isLt⟩)
    (fun _ => rfl)
    (fun _ => rfl)

/-- `bitVecLE` encodes through the `Trusted` little-endian encoder. -/
theorem bitVecLE_encode (sz : Nat) (hNz : 0 < sz) (x : BitVec (8 * sz)) :
    (bitVecLE sz hNz).encode x = encodeLittleEndianBytes x.toNat sz none := rfl

/-- `bitVecLE.encode` is the embedded `Anneal.LeBytes.toLeBytesAux` byte list. -/
theorem bitVecLE_encode_eq_toLeBytesAux (sz : Nat) (hNz : 0 < sz) (x : BitVec (8 * sz)) :
    (bitVecLE sz hNz).encode x =
      (Anneal.LeBytes.toLeBytesAux sz x.toNat).map (bvByteToAbstract none) :=
  encodeLittleEndianBytes_eq_map none sz x.toNat

/-- `bitVecLE.encode` is the embedded `Anneal.LeBytes.toLeBytes` byte list (after re-indexing the
width from `8 * sz` to `sz * 8`). -/
theorem bitVecLE_encode_eq_toLeBytes (sz : Nat) (hNz : 0 < sz) (x : BitVec (8 * sz)) :
    (bitVecLE sz hNz).encode x =
      (Anneal.LeBytes.toLeBytes sz (toLeWidth x)).map (bvByteToAbstract none) :=
  encodeLittleEndianBytes_eq_map none sz x.toNat

/-- Closed form of `bitVecLE.decode`: an exact-length check followed by the `Trusted`
little-endian decoder. -/
theorem bitVecLE_decode (sz : Nat) (hNz : 0 < sz) (bs : List AbstractByte) :
    (bitVecLE sz hNz).decode bs =
      if bs.length = sz then
        (decodeLittleEndianBytes bs).map (fun p => BitVec.ofNat (8 * sz) p.1)
      else none := by
  show ((FixedByteCodec.uintBitsLE sz hNz).decode bs).map
      (fun b => BitVec.ofNatLT b.val b.property) = _
  unfold FixedByteCodec.uintBitsLE FixedByteCodec.ofRoundTrip
  dsimp only
  cases hbeq : Nat.beq bs.length sz with
  | false =>
    have hne : bs.length ≠ sz := fun h => by rw [h, nat_beq_self] at hbeq; cases hbeq
    simp only [hne, ↓reduceIte, Option.map_none]
  | true =>
    have heq : bs.length = sz := Nat.eq_of_beq_eq_true hbeq
    simp only [heq, ↓reduceIte]
    cases hdec : decodeLittleEndianBytes bs with
    | none => rfl
    | some p =>
      obtain ⟨bits, prov⟩ := p
      have hlt := decodeLittleEndianBytes_lt_scalarModulus bs bits prov hdec
      rw [seqLength_eq, heq, scalarModulus_eq] at hlt
      simp only [hlt, ↓reduceDIte, Option.map_some]
      congr 1
      apply _root_.BitVec.eq_of_toNat_eq
      rw [_root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      rfl

/-- `bitVecLE.decode` on an embedded byte list of the right length is `fromLeBytes` (any
provenance is accepted and discarded). -/
theorem bitVecLE_decode_map (sz : Nat) (hNz : 0 < sz) (prov : Option (Nat × Nat))
    {bs : List (BitVec 8)} (hlen : bs.length = sz) :
    (bitVecLE sz hNz).decode (bs.map (bvByteToAbstract prov)) =
      some (BitVec.ofNat (8 * sz) (Anneal.LeBytes.fromLeBytes bs)) := by
  have hl : (bs.map (bvByteToAbstract prov)).length = sz := by rw [List.length_map, hlen]
  rw [bitVecLE_decode, decodeLittleEndianBytes_map]
  simp only [hl, ↓reduceIte, Option.map_some]

/-- `bitVecLE.decode` rejects every byte list of the wrong length (truncated or trailing). -/
theorem bitVecLE_decode_eq_none_of_length_ne (sz : Nat) (hNz : 0 < sz) {bs : List AbstractByte}
    (hne : bs.length ≠ sz) : (bitVecLE sz hNz).decode bs = none := by
  rw [bitVecLE_decode]
  simp only [hne, ↓reduceIte]

/-- `bitVecLE.decode` rejects every byte list containing an `.uninit` byte. -/
theorem bitVecLE_decode_eq_none_of_uninit (sz : Nat) (hNz : 0 < sz) {bs : List AbstractByte}
    (h : allBytesInitialized bs = false) : (bitVecLE sz hNz).decode bs = none := by
  rw [bitVecLE_decode, decodeLittleEndianBytes_eq_none_of_uninit bs h]
  cases Nat.decEq bs.length sz with
  | isTrue he => simp only [he, ↓reduceIte, Option.map_none]
  | isFalse hn => simp only [hn, ↓reduceIte]

/-- Exact characterization of successful `bitVecLE` decoding: the byte list has length `sz`, is
fully initialized, and its extracted payload reassembles (little-endian) to the value. -/
theorem bitVecLE_decode_eq_some_iff (sz : Nat) (hNz : 0 < sz) (bs : List AbstractByte)
    (x : BitVec (8 * sz)) :
    (bitVecLE sz hNz).decode bs = some x ↔
      bs.length = sz ∧ allBytesInitialized bs = true ∧
        Anneal.LeBytes.fromLeBytes (extractInitBvBytes bs) = x.toNat := by
  constructor
  · intro h
    cases Nat.decEq bs.length sz with
    | isFalse hn =>
      rw [bitVecLE_decode_eq_none_of_length_ne sz hNz hn] at h
      cases h
    | isTrue hl =>
      cases hi : allBytesInitialized bs with
      | false =>
        rw [bitVecLE_decode_eq_none_of_uninit sz hNz hi] at h
        cases h
      | true =>
        obtain ⟨p, hp⟩ := decodeLittleEndianBytes_of_init bs hi
        have hlt := decodeLittleEndianBytes_lt_scalarModulus bs _ p hp
        rw [seqLength_eq, hl, scalarModulus_eq] at hlt
        rw [bitVecLE_decode, hp] at h
        simp only [hl, ↓reduceIte, Option.map_some] at h
        have hx := congrArg _root_.BitVec.toNat (Option.some.inj h)
        rw [_root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at hx
        exact ⟨hl, rfl, hx⟩
  · rintro ⟨hl, hi, hx⟩
    obtain ⟨p, hp⟩ := decodeLittleEndianBytes_of_init bs hi
    rw [bitVecLE_decode, hp]
    simp only [hl, ↓reduceIte, Option.map_some]
    rw [hx, ofNat_toNat_self]

/-- `bitVecLE` rejects wrong-length byte lists. -/
theorem bitVecLE_isExactWidth (sz : Nat) (hNz : 0 < sz) : (bitVecLE sz hNz).IsExactWidth :=
  FixedByteCodec.mapEquiv_isExactWidth _ _ _ _ _ (FixedByteCodec.uintBitsLE_isExactWidth sz hNz)

/-- `bitVecLE` only emits initialized bytes (`IntoBytes` side condition). -/
theorem bitVecLE_isInitCodec (sz : Nat) (hNz : 0 < sz) : (bitVecLE sz hNz).IsInitCodec :=
  FixedByteCodec.mapEquiv_isInitCodec _ _ _ _ _ (FixedByteCodec.uintBitsLE_isInitCodec sz hNz)

/-- `bitVecLE` accepts every initialized `sz`-byte list (`FromBytes` side condition). -/
theorem bitVecLE_isSurjectiveInitDecoder (sz : Nat) (hNz : 0 < sz) :
    (bitVecLE sz hNz).IsSurjectiveInitDecoder :=
  FixedByteCodec.mapEquiv_isSurjectiveInitDecoder _ _ _ _ _
    (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder sz hNz)

/-- `bitVecLE` accepts the all-zero byte list (`FromZeros` side condition). -/
theorem bitVecLE_hasZeroValid (sz : Nat) (hNz : 0 < sz) : (bitVecLE sz hNz).HasZeroValid :=
  FixedByteCodec.mapEquiv_hasZeroValid _ _ _ _ _ (FixedByteCodec.uintBitsLE_hasZeroValid sz hNz)

/-- The all-zero byte list decodes to the zero bitvector. -/
theorem bitVecLE_decode_zeroInitBytes (sz : Nat) (hNz : 0 < sz) :
    (bitVecLE sz hNz).decode (zeroInitBytes sz) = some (BitVec.ofNat (8 * sz) 0) := by
  have hl : (zeroInitBytes sz).length = sz := length_zeroInitBytes sz
  rw [bitVecLE_decode, decodeLittleEndianBytes_zeroInitBytes]
  simp only [hl, ↓reduceIte, Option.map_some]

/-- `bitVecLE.encode` agrees with the MIR scalar encoder on the scalar carrying the bitvector. -/
theorem encodeScalarBytes_eq_bitVecLE_encode (sz : Nat) (hNz : 0 < sz) (x : BitVec (8 * sz)) :
    encodeScalarBytes ⟨x.toNat, sz⟩ none = some ((bitVecLE sz hNz).encode x) := by
  unfold encodeScalarBytes
  simp only [beq_zero_of_pos hNz]
  rfl

/-- Concatenating two `bitVecLE` encodings is the `bitVecLE` encoding of the concatenated
value at the summed width: the 4-byte-pair / 8-byte-chunk correspondence behind `[u32; 2k]` to
`[u64; k]` transmutation. -/
theorem bitVecLE_encode_append (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (a : BitVec (8 * m)) (b : BitVec (8 * n)) :
    (bitVecLE m hm).encode a ++ (bitVecLE n hn).encode b =
      (bitVecLE (m + n) (Nat.add_pos_left hm n)).encode
        (BitVec.ofNat (8 * (m + n)) (a.toNat + 2 ^ (m * 8) * b.toNat)) := by
  have ha : a.toNat < 2 ^ (m * 8) := by
    have h := toNat_lt_scalarModulus a
    rw [scalarModulus_eq_le] at h
    exact h
  have hb : b.toNat < 2 ^ (n * 8) := by
    have h := toNat_lt_scalarModulus b
    rw [scalarModulus_eq_le] at h
    exact h
  have hsum : a.toNat + 2 ^ (m * 8) * b.toNat < 2 ^ (8 * (m + n)) := by
    have hp : 2 ^ (8 * (m + n)) = 2 ^ (m * 8) * 2 ^ (n * 8) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hp]
    have h1 : 2 ^ (m * 8) * (b.toNat + 1) ≤ 2 ^ (m * 8) * 2 ^ (n * 8) :=
      Nat.mul_le_mul_left _ hb
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega
  rw [bitVecLE_encode_eq_toLeBytesAux, bitVecLE_encode_eq_toLeBytesAux,
    bitVecLE_encode_eq_toLeBytesAux, ← List.map_append, toLeBytesAux_append n ha,
    _root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum]

/-! ## 9. Chunking, Arrays and `BitValidity` Transmutation -/

/-- Collect a list of optional results, failing as soon as one element fails. -/
def sequenceOptions {β : Type} : List (Option β) → Option (List β)
  | [] => some []
  | none :: _ => none
  | some x :: rest => (sequenceOptions rest).map (x :: ·)

/-- `sequenceOptions` succeeds exactly on lists of `some`s, returning the payloads. -/
theorem sequenceOptions_eq_some_iff {β : Type} :
    ∀ (l : List (Option β)) (xs : List β), sequenceOptions l = some xs ↔ l = xs.map some
  | [], xs => by
    cases xs with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons x xs => exact ⟨fun h => (nomatch h), fun h => nomatch h⟩
  | none :: rest, xs => by
    cases xs with
    | nil => exact ⟨fun h => (nomatch h), fun h => nomatch h⟩
    | cons x xs =>
      refine ⟨fun h => (nomatch h), fun h => ?_⟩
      have h' : (none : Option β) = some x := (List.cons.inj h).1
      nomatch h'
  | some y :: rest, xs => by
    have ih := sequenceOptions_eq_some_iff rest
    show (sequenceOptions rest).map (y :: ·) = some xs ↔ _
    cases xs with
    | nil =>
      refine ⟨fun h => ?_, fun h => nomatch h⟩
      cases hr : sequenceOptions rest with
      | none => rw [hr] at h; nomatch h
      | some ys => rw [hr] at h; nomatch h
    | cons x xs =>
      constructor
      · intro h
        cases hr : sequenceOptions rest with
        | none => rw [hr] at h; nomatch h
        | some ys =>
          rw [hr] at h
          have h' : y :: ys = x :: xs := Option.some.inj h
          have hx : y = x := (List.cons.inj h').1
          have hxs : ys = xs := (List.cons.inj h').2
          subst hx; subst hxs
          show some y :: rest = some y :: ys.map some
          rw [(ih ys).1 hr]
      · intro h
        have hy : some y = some x := (List.cons.inj h).1
        have hrest : rest = xs.map some := (List.cons.inj h).2
        have hx : y = x := Option.some.inj hy
        subst hx
        rw [(ih xs).2 hrest]
        rfl

/-- `sequenceOptions` fails as soon as some element is `none`. -/
theorem sequenceOptions_eq_none_of_mem {β : Type} :
    ∀ (l : List (Option β)), none ∈ l → sequenceOptions l = none
  | [], h => nomatch h
  | none :: _, _ => rfl
  | some y :: rest, h => by
    have hmem : none ∈ rest := by
      cases h with
      | tail _ h' => exact h'
    show (sequenceOptions rest).map (y :: ·) = none
    rw [sequenceOptions_eq_none_of_mem rest hmem]
    rfl

/-- A list of exactly one chunk width is a single chunk. -/
theorem chunksOf_eq_singleton {α : Type} {n : Nat} (hn : 0 < n) {xs : List α}
    (h : xs.length = n) : Anneal.ListChunks.chunksOf n xs = [xs] := by
  have hne : xs ≠ [] := by
    intro he
    rw [he] at h
    have h' : 0 = n := h
    omega
  rw [Anneal.ListChunks.chunksOf_of_nonempty hn hne, List.take_of_length_le (Nat.le_of_eq h),
    List.drop_of_length_le (Nat.le_of_eq h), Anneal.ListChunks.chunksOf_nil]

/-- A buffer of `k * n` bytes splits into exactly `k` chunks of width `n`
(`divCeil (k * n) n = k`). -/
theorem length_chunksOf_of_length_eq_mul {α : Type} {n : Nat} (hn : 0 < n) {k : Nat}
    {xs : List α} (h : xs.length = k * n) :
    (Anneal.ListChunks.chunksOf n xs).length = k := by
  rw [Anneal.ListChunks.chunksOf_length hn, h, Anneal.ListChunks.divCeil_mul_right k n hn]

/-- Chunking distributes over element-wise encoding: splitting the concatenated encoding of
`xs` into `n`-byte chunks recovers each element's encoding (including `xs = []`). -/
theorem chunksOf_encodeElems {α : Type} {n : Nat} (c : FixedByteCodec α n) (hn : 0 < n) :
    ∀ xs : List α, Anneal.ListChunks.chunksOf n (c.encodeElems xs) = xs.map c.encode
  | [] => Anneal.ListChunks.chunksOf_nil n
  | x :: xs => by
    have hlen : (c.encode x).length % n = 0 := by rw [c.encode_length x, Nat.mod_self]
    show Anneal.ListChunks.chunksOf n (c.encode x ++ c.encodeElems xs) = _
    rw [Anneal.ListChunks.chunksOf_append_exact hn _ _ hlen,
      chunksOf_eq_singleton hn (c.encode_length x), chunksOf_encodeElems c hn xs]
    rfl

/-- Mapping an injective function over lists is injective. -/
theorem list_map_injective {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {xs ys : List α}, xs.map f = ys.map f → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    have h₁ : f x = f y := (List.cons.inj h).1
    have h₂ : xs.map f = ys.map f := (List.cons.inj h).2
    rw [hf x y h₁, list_map_injective hf h₂]

/-- Element-wise encoding is injective for every positive-width codec. -/
theorem encodeElems_injective {α : Type} {n : Nat} (c : FixedByteCodec α n) (hn : 0 < n)
    {xs ys : List α} (h : c.encodeElems xs = c.encodeElems ys) : xs = ys := by
  have h' := congrArg (Anneal.ListChunks.chunksOf n) h
  rw [chunksOf_encodeElems c hn, chunksOf_encodeElems c hn] at h'
  exact list_map_injective (fun _ _ he => c.encode_injective he) h'

/-- Exact agreement between `Trusted` `decodeArrayChunksWith` and `Anneal.ListChunks.chunksOf`:
decoding `k` chunks of positive width `n` succeeds exactly when the buffer has length `k * n`
and every `chunksOf n` chunk decodes; a malformed buffer (wrong length, hence a short or
surplus trailing chunk) is rejected. -/
theorem decodeArrayChunksWith_eq_chunksOf (decVal : List AbstractByte → Option Value) {n : Nat}
    (hn : 0 < n) : ∀ (k : Nat) (bs : List AbstractByte),
    decodeArrayChunksWith decVal n k bs =
      if bs.length = k * n then
        sequenceOptions ((Anneal.ListChunks.chunksOf n bs).map decVal)
      else none
  | 0, [] => by simp [decodeArrayChunksWith, sequenceOptions]
  | 0, b :: bs => by simp [decodeArrayChunksWith]
  | k + 1, bs => by
    have ih := decodeArrayChunksWith_eq_chunksOf decVal hn k (bs.drop n)
    have hmul : (k + 1) * n = k * n + n := Nat.succ_mul k n
    unfold decodeArrayChunksWith
    dsimp only
    rw [seqLength_eq, takeAbstractBytes_eq_take, dropAbstractBytes_eq_drop, ih, List.length_drop]
    cases hble : Nat.ble n bs.length with
    | false =>
      have hlt : ¬ n ≤ bs.length := fun hle => by
        rw [Nat.ble_eq_true_of_le hle] at hble; cases hble
      have hne : bs.length ≠ (k + 1) * n := by omega
      simp only [hne, ↓reduceIte]
    | true =>
      have hle : n ≤ bs.length := Nat.le_of_ble_eq_true hble
      have hnil : bs ≠ [] := by
        intro he
        rw [he] at hle
        have hle' : n ≤ 0 := hle
        omega
      rw [Anneal.ListChunks.chunksOf_of_nonempty hn hnil, List.map_cons]
      cases Nat.decEq bs.length ((k + 1) * n) with
      | isTrue he =>
        have he' : bs.length - n = k * n := by omega
        simp only [he', ↓reduceIte]
        simp only [he, ↓reduceIte]
        cases decVal (bs.take n) with
        | none => rfl
        | some v =>
          show (match sequenceOptions
              ((Anneal.ListChunks.chunksOf n (bs.drop n)).map decVal) with
            | some vs => some (v :: vs)
            | none => none) =
            (sequenceOptions ((Anneal.ListChunks.chunksOf n (bs.drop n)).map decVal)).map
              (v :: ·)
          cases sequenceOptions ((Anneal.ListChunks.chunksOf n (bs.drop n)).map decVal) <;> rfl
      | isFalse hne =>
        have hne' : bs.length - n ≠ k * n := by omega
        simp only [hne', ↓reduceIte]
        simp only [hne, ↓reduceIte]
        cases decVal (bs.take n) <;> rfl

/-- `decodeArrayChunksWith` succeeds exactly when the buffer has length `k * n` and the
`chunksOf n` chunks decode, in order, to the returned values. -/
theorem decodeArrayChunksWith_eq_some_iff (decVal : List AbstractByte → Option Value) {n : Nat}
    (hn : 0 < n) (k : Nat) (bs : List AbstractByte) (vs : List Value) :
    decodeArrayChunksWith decVal n k bs = some vs ↔
      bs.length = k * n ∧ (Anneal.ListChunks.chunksOf n bs).map decVal = vs.map some := by
  rw [decodeArrayChunksWith_eq_chunksOf decVal hn]
  cases Nat.decEq bs.length (k * n) with
  | isTrue he =>
    simp only [he, ↓reduceIte, true_and]
    exact sequenceOptions_eq_some_iff _ _
  | isFalse hne =>
    simp only [hne, ↓reduceIte, false_and]
    exact ⟨fun h => (nomatch h), fun h => h.elim⟩

/-- `decodeArrayChunksWith` rejects every buffer whose length is not `k * n` (for example a
buffer with a short trailing chunk), whatever the element decoder. -/
theorem decodeArrayChunksWith_eq_none_of_length_ne (decVal : List AbstractByte → Option Value)
    {n : Nat} (hn : 0 < n) {k : Nat} {bs : List AbstractByte} (hne : bs.length ≠ k * n) :
    decodeArrayChunksWith decVal n k bs = none := by
  rw [decodeArrayChunksWith_eq_chunksOf decVal hn]
  simp only [hne, ↓reduceIte]

/-- Exact agreement between `FixedByteCodec.decodeChunks` and `Anneal.ListChunks.chunksOf`. -/
theorem decodeChunks_eq_chunksOf {α : Type} {n : Nat} (c : FixedByteCodec α n) (hn : 0 < n) :
    ∀ (k : Nat) (bs : List AbstractByte),
    (c.decodeChunks k bs).map Subtype.val =
      if bs.length = k * n then
        sequenceOptions ((Anneal.ListChunks.chunksOf n bs).map c.decode)
      else none
  | 0, [] => by simp [FixedByteCodec.decodeChunks, sequenceOptions]
  | 0, b :: bs => by simp [FixedByteCodec.decodeChunks]
  | k + 1, bs => by
    have ih := decodeChunks_eq_chunksOf c hn k (bs.drop n)
    have hmul : (k + 1) * n = k * n + n := Nat.succ_mul k n
    rw [List.length_drop] at ih
    unfold FixedByteCodec.decodeChunks
    cases hble : Nat.ble n bs.length with
    | false =>
      have hlt : ¬ n ≤ bs.length := fun hle => by
        rw [Nat.ble_eq_true_of_le hle] at hble; cases hble
      have hne : bs.length ≠ (k + 1) * n := by omega
      simp only [hne, ↓reduceIte, Option.map_none]
    | true =>
      have hle : n ≤ bs.length := Nat.le_of_ble_eq_true hble
      have hnil : bs ≠ [] := by
        intro he
        rw [he] at hle
        have hle' : n ≤ 0 := hle
        omega
      rw [Anneal.ListChunks.chunksOf_of_nonempty hn hnil, List.map_cons]
      cases Nat.decEq bs.length ((k + 1) * n) with
      | isTrue he =>
        have he' : bs.length - n = k * n := by omega
        simp only [he', ↓reduceIte] at ih
        simp only [he, ↓reduceIte]
        cases c.decode (bs.take n) with
        | none => rfl
        | some x =>
          cases hr : c.decodeChunks k (bs.drop n) with
          | none =>
            rw [hr] at ih
            show none = (sequenceOptions _).map (x :: ·)
            rw [← ih]
            rfl
          | some tl =>
            rw [hr] at ih
            obtain ⟨xs, hxs⟩ := tl
            show some (x :: xs) = (sequenceOptions _).map (x :: ·)
            rw [← ih]
            rfl
      | isFalse hne =>
        have hne' : bs.length - n ≠ k * n := by omega
        simp only [hne', ↓reduceIte] at ih
        simp only [hne, ↓reduceIte]
        cases c.decode (bs.take n) with
        | none => rfl
        | some x =>
          cases hr : c.decodeChunks k (bs.drop n) with
          | none => rfl
          | some tl =>
            rw [hr] at ih
            cases ih

/-- `decodeChunks` succeeds exactly when the buffer has length `k * n` and the `chunksOf n`
chunks decode, in order, to the returned elements. -/
theorem decodeChunks_eq_some_iff {α : Type} {n : Nat} (c : FixedByteCodec α n) (hn : 0 < n)
    (k : Nat) (bs : List AbstractByte) (xs : List α) :
    (c.decodeChunks k bs).map Subtype.val = some xs ↔
      bs.length = k * n ∧ (Anneal.ListChunks.chunksOf n bs).map c.decode = xs.map some := by
  rw [decodeChunks_eq_chunksOf c hn]
  cases Nat.decEq bs.length (k * n) with
  | isTrue he =>
    simp only [he, ↓reduceIte, true_and]
    exact sequenceOptions_eq_some_iff _ _
  | isFalse hne =>
    simp only [hne, ↓reduceIte, false_and]
    exact ⟨fun h => (nomatch h), fun h => h.elim⟩

/-- `decodeChunks` rejects every buffer whose length is not `k * n`. -/
theorem decodeChunks_eq_none_of_length_ne {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (hn : 0 < n) {k : Nat} {bs : List AbstractByte} (hne : bs.length ≠ k * n) :
    c.decodeChunks k bs = none := by
  have h := decodeChunks_eq_chunksOf c hn k bs
  simp only [hne, ↓reduceIte] at h
  cases hd : c.decodeChunks k bs with
  | none => rfl
  | some r => rw [hd] at h; cases h

/-- `decodeChunks` rejects every buffer one of whose `chunksOf n` chunks fails to decode (for
example a chunk containing an `.uninit` byte). -/
theorem decodeChunks_eq_none_of_chunk {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (hn : 0 < n) (k : Nat) {bs ch : List AbstractByte}
    (hmem : ch ∈ Anneal.ListChunks.chunksOf n bs) (hch : c.decode ch = none) :
    c.decodeChunks k bs = none := by
  have h := decodeChunks_eq_chunksOf c hn k bs
  have hnone : sequenceOptions ((Anneal.ListChunks.chunksOf n bs).map c.decode) = none :=
    sequenceOptions_eq_none_of_mem _ (hch ▸ List.mem_map_of_mem hmem)
  rw [hnone] at h
  cases hd : c.decodeChunks k bs with
  | none => rfl
  | some r =>
    rw [hd] at h
    cases Nat.decEq bs.length (k * n) with
    | isTrue he => simp only [he, ↓reduceIte] at h; cases h
    | isFalse hne => simp only [hne, ↓reduceIte] at h; cases h

/-- Round trip through chunking: decoding the element-wise encoding returns the elements, and
the chunks seen by the decoder are exactly the per-element encodings. -/
theorem decodeChunks_encodeElems_val {α : Type} {n : Nat} (c : FixedByteCodec α n)
    (xs : List α) :
    (c.decodeChunks xs.length (c.encodeElems xs)).map Subtype.val = some xs := by
  rw [FixedByteCodec.decodeChunks_encodeElems c xs.length xs rfl]
  rfl

/-- `bitVecLE` element-wise encoding is the flattened, embedded `toLeBytesAux` byte lists. -/
theorem encodeElems_bitVecLE (sz : Nat) (hNz : 0 < sz) : ∀ xs : List (BitVec (8 * sz)),
    (bitVecLE sz hNz).encodeElems xs =
      ((xs.map (fun x => Anneal.LeBytes.toLeBytesAux sz x.toNat)).flatten).map
        (bvByteToAbstract none)
  | [] => rfl
  | x :: xs => by
    show (bitVecLE sz hNz).encode x ++ (bitVecLE sz hNz).encodeElems xs = _
    rw [encodeElems_bitVecLE sz hNz xs, bitVecLE_encode_eq_toLeBytesAux, List.map_cons,
      List.flatten_cons, List.map_append]

/-- `bitVecLE` element-wise encoding agrees with the subtype-valued `uintBitsLE` encoding used by
`MirValueCodec.uintArray`. -/
theorem encodeElems_bitVecLE_eq_uintBitsLE (sz : Nat) (hNz : 0 < sz) :
    ∀ xs : List (BitVec (8 * sz)),
    (bitVecLE sz hNz).encodeElems xs =
      (FixedByteCodec.uintBitsLE sz hNz).encodeElems
        (xs.map (fun x => (⟨x.toNat, x.isLt⟩ : { bits : Nat // bits < 2 ^ (8 * sz) })))
  | [] => rfl
  | x :: xs => by
    show (bitVecLE sz hNz).encode x ++ (bitVecLE sz hNz).encodeElems xs = _
    rw [encodeElems_bitVecLE_eq_uintBitsLE sz hNz xs]
    rfl

/-- Little-endian pair injectivity (`Anneal.LeBytes.toLeBytes_append_injective`) transferred
onto `Trusted` `encodeListWith`: two-element lists of `bitVecLE`-encoded values with equal
encodings have equal elements. -/
theorem encodeListWith_pair_injective {sz : Nat} (hNz : 0 < sz)
    (encVal : Value → Option (List AbstractByte)) (toVal : BitVec (8 * sz) → Value)
    (hEnc : ∀ x, encVal (toVal x) = some ((bitVecLE sz hNz).encode x))
    {a₁ b₁ a₂ b₂ : BitVec (8 * sz)}
    (h : encodeListWith encVal sz [toVal a₁, toVal b₁] =
      encodeListWith encVal sz [toVal a₂, toVal b₂]) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have e₁ := FixedByteCodec.encodeListWith_map_eq_encodeElems (bitVecLE sz hNz) toVal encVal hEnc
    [a₁, b₁]
  have e₂ := FixedByteCodec.encodeListWith_map_eq_encodeElems (bitVecLE sz hNz) toVal encVal hEnc
    [a₂, b₂]
  have h' : (bitVecLE sz hNz).encodeElems [a₁, b₁] = (bitVecLE sz hNz).encodeElems [a₂, b₂] :=
    Option.some.inj (e₁.symm.trans (h.trans e₂))
  have h'' : (bitVecLE sz hNz).encode a₁ ++ (bitVecLE sz hNz).encode b₁ =
      (bitVecLE sz hNz).encode a₂ ++ (bitVecLE sz hNz).encode b₂ := by
    have hl : ∀ a b : BitVec (8 * sz), (bitVecLE sz hNz).encodeElems [a, b] =
        (bitVecLE sz hNz).encode a ++ (bitVecLE sz hNz).encode b := fun a b =>
      congrArg ((bitVecLE sz hNz).encode a ++ ·) (List.append_nil _)
    rw [← hl, ← hl]
    exact h'
  rw [bitVecLE_encode_eq_toLeBytes, bitVecLE_encode_eq_toLeBytes, bitVecLE_encode_eq_toLeBytes,
    bitVecLE_encode_eq_toLeBytes, ← List.map_append, ← List.map_append] at h''
  have r := Anneal.LeBytes.toLeBytes_append_injective (map_bvByteToAbstract_injective h'')
  exact ⟨toLeWidth_injective r.1, toLeWidth_injective r.2⟩

/-- Injectivity of `Trusted` `encodeListWith` on lists of `bitVecLE`-encoded values of any
length. -/
theorem encodeListWith_injective {sz : Nat} (hNz : 0 < sz)
    (encVal : Value → Option (List AbstractByte)) (toVal : BitVec (8 * sz) → Value)
    (hEnc : ∀ x, encVal (toVal x) = some ((bitVecLE sz hNz).encode x))
    {xs ys : List (BitVec (8 * sz))}
    (h : encodeListWith encVal sz (xs.map toVal) = encodeListWith encVal sz (ys.map toVal)) :
    xs = ys := by
  have e₁ := FixedByteCodec.encodeListWith_map_eq_encodeElems (bitVecLE sz hNz) toVal encVal hEnc xs
  have e₂ := FixedByteCodec.encodeListWith_map_eq_encodeElems (bitVecLE sz hNz) toVal encVal hEnc ys
  exact encodeElems_injective (bitVecLE sz hNz) hNz (Option.some.inj (e₁.symm.trans (h.trans e₂)))

/-- The MIR runtime value of an array of `sz`-byte unsigned integers given as bitvectors. -/
def bitVecArrayValue (sz : Nat) (xs : List (BitVec (8 * sz))) : Value :=
  .aggregate 0 (xs.map (fun x => Value.scalar ⟨x.toNat, sz⟩))

/-- Byte size of `[uN; n]` (including `n = 0`). -/
theorem rigidTyByteSize_array_uint (layouts : LayoutTable) (w : UintTy) (n : Nat)
    (idx : LayoutIdx) :
    rigidTyByteSize layouts { kind := .array (.uint w) n, layoutIdx := idx } =
      some (MirValueCodec.uintByteSize w * n) := by
  cases w <;> rfl

/-- `encodeValueToBytes` on a non-empty array of unsigned integers given as bitvectors is the
element-wise `bitVecLE` encoding. -/
theorem encodeValueToBytes_bitVecArray (layouts : LayoutTable) (w : UintTy) (idx : LayoutIdx)
    {xs : List (BitVec (8 * MirValueCodec.uintByteSize w))} (hne : xs ≠ []) :
    encodeValueToBytes defaultCodecFuel layouts
        { kind := .array (.uint w) xs.length, layoutIdx := idx }
        (bitVecArrayValue (MirValueCodec.uintByteSize w) xs) =
      some ((bitVecLE (MirValueCodec.uintByteSize w)
        (MirValueCodec.uintByteSize_pos w)).encodeElems xs) := by
  have hk : 0 < xs.length := List.length_pos_iff.2 hne
  have h := (MirValueCodec.uintArray layouts w xs.length hk idx).encode_toValue
    ⟨xs.map (fun x => (⟨x.toNat, x.isLt⟩ :
      { bits : Nat // bits < 2 ^ (8 * MirValueCodec.uintByteSize w) })), List.length_map _⟩
  rw [encodeElems_bitVecLE_eq_uintBitsLE]
  have hv : bitVecArrayValue (MirValueCodec.uintByteSize w) xs =
      (MirValueCodec.uintArray layouts w xs.length hk idx).toValue
        ⟨xs.map (fun x => (⟨x.toNat, x.isLt⟩ :
          { bits : Nat // bits < 2 ^ (8 * MirValueCodec.uintByteSize w) })), List.length_map _⟩ := by
    show Value.aggregate 0 _ = Value.aggregate 0 _
    rw [List.map_map]
    rfl
  rw [hv]
  exact h

/-- `decodeValueFromBytes` recovers a non-empty array of unsigned integers from its element-wise
`bitVecLE` encoding. -/
theorem decodeValueFromBytes_encodeElems_bitVecLE (layouts : LayoutTable) (w : UintTy)
    (idx : LayoutIdx) {xs : List (BitVec (8 * MirValueCodec.uintByteSize w))} (hne : xs ≠ []) :
    decodeValueFromBytes defaultCodecFuel layouts
        { kind := .array (.uint w) xs.length, layoutIdx := idx }
        ((bitVecLE (MirValueCodec.uintByteSize w)
          (MirValueCodec.uintByteSize_pos w)).encodeElems xs) =
      some (bitVecArrayValue (MirValueCodec.uintByteSize w) xs) := by
  have hk : 0 < xs.length := List.length_pos_iff.2 hne
  have m := MirValueCodec.uintArray layouts w xs.length hk idx
  rw [encodeElems_bitVecLE_eq_uintBitsLE,
    (MirValueCodec.uintArray layouts w xs.length hk idx).decode_eq_map]
  have hdec := (MirValueCodec.uintArray layouts w xs.length hk idx).codec.decode_encode
    ⟨xs.map (fun x => (⟨x.toNat, x.isLt⟩ :
      { bits : Nat // bits < 2 ^ (8 * MirValueCodec.uintByteSize w) })), List.length_map _⟩
  have henc : (MirValueCodec.uintArray layouts w xs.length hk idx).codec.encode
      ⟨xs.map (fun x => (⟨x.toNat, x.isLt⟩ :
        { bits : Nat // bits < 2 ^ (8 * MirValueCodec.uintByteSize w) })), List.length_map _⟩ =
      (FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w)
        (MirValueCodec.uintByteSize_pos w)).encodeElems
        (xs.map (fun x => (⟨x.toNat, x.isLt⟩ :
          { bits : Nat // bits < 2 ^ (8 * MirValueCodec.uintByteSize w) }))) := rfl
  rw [← henc, hdec, Option.map_some]
  show some (Value.aggregate 0 _) = some (Value.aggregate 0 _)
  rw [List.map_map]
  rfl

/-- `BitValidity` array-trait compatibility: any value of `[uA; n₁]` transmutes soundly to
`[uB; n₂]` whenever the byte sizes agree (`array_uint_isIntoBytes`, `array_uint_isFromBytes`,
`transmute_sound_of_into_from_bytes`), including the empty arrays `n₁ = n₂ = 0`. -/
theorem array_uint_transmute_sound (layouts : LayoutTable) (w₁ w₂ : UintTy) (n₁ n₂ : Nat)
    (idx₁ idx₂ : LayoutIdx)
    (hsize : MirValueCodec.uintByteSize w₁ * n₁ = MirValueCodec.uintByteSize w₂ * n₂)
    (v : Value) (bs : List AbstractByte)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts
      { kind := .array (.uint w₁) n₁, layoutIdx := idx₁ } v = some bs) :
    ∃ v', decodeValueFromBytes defaultCodecFuel layouts
      { kind := .array (.uint w₂) n₂, layoutIdx := idx₂ } bs = some v' :=
  transmute_sound_of_into_from_bytes layouts _ _
    (array_uint_isIntoBytes layouts w₁ n₁ idx₁) (array_uint_isFromBytes layouts w₂ n₂ idx₂)
    (by rw [rigidTyByteSize_array_uint, rigidTyByteSize_array_uint, hsize]) v bs hEnc

/-- Typed transmutation of bitvector arrays: the bytes of a non-empty `[uA; n₁]` array given as
bitvectors decode at `[uB; n₂]` whenever the byte sizes agree. -/
theorem bitVecArray_transmute_sound (layouts : LayoutTable) (w₁ w₂ : UintTy) (n₂ : Nat)
    (idx₁ idx₂ : LayoutIdx) {xs : List (BitVec (8 * MirValueCodec.uintByteSize w₁))}
    (hne : xs ≠ [])
    (hsize : MirValueCodec.uintByteSize w₁ * xs.length = MirValueCodec.uintByteSize w₂ * n₂) :
    ∃ v', decodeValueFromBytes defaultCodecFuel layouts
      { kind := .array (.uint w₂) n₂, layoutIdx := idx₂ }
      ((bitVecLE (MirValueCodec.uintByteSize w₁)
        (MirValueCodec.uintByteSize_pos w₁)).encodeElems xs) = some v' :=
  array_uint_transmute_sound layouts w₁ w₂ xs.length n₂ idx₁ idx₂ hsize _ _
    (encodeValueToBytes_bitVecArray layouts w₁ idx₁ hne)

/-! ## 10. Derived Transfers: Abstraction Normalization, Signed Casts and `ctlz` from Ranges -/

/-- Rewrite the mask and reference value of a scalar tnum along equalities (used to replace a
computed transfer mask by its closed form). -/
theorem scalarTnum_congr {sz : Nat} {m m' v v' : BitVec (8 * sz)} {sc : ScalarInt}
    (hm : m = m') (hv : v = v') (h : ScalarTnum sz m v sc) : ScalarTnum sz m' v' sc := by
  subst hm; subst hv; exact h

/-- Rewrite the endpoints of an unsigned scalar interval along equalities. -/
theorem scalarRange_congr {sz : Nat} {lo lo' hi hi' : BitVec (8 * sz)} {sc : ScalarInt}
    (hlo : lo = lo') (hhi : hi = hi') (h : ScalarRange sz lo hi sc) :
    ScalarRange sz lo' hi' sc := by
  subst hlo; subst hhi; exact h

/-- Rewrite the endpoints of a signed scalar interval along equalities. -/
theorem scalarSRange_congr {sz : Nat} {lo lo' hi hi' : BitVec (8 * sz)} {sc : ScalarInt}
    (hlo : lo = lo') (hhi : hi = hi') (h : ScalarSRange sz lo hi sc) :
    ScalarSRange sz lo' hi' sc := by
  subst hlo; subst hhi; exact h

/-- A canonical constant is abstracted by the fully-known tnum at its own value. -/
theorem scalarTnum_const {sz c : Nat} (hc : c < scalarModulus sz) :
    ScalarTnum sz (BitVec.ofNat (8 * sz) 0) (BitVec.ofNat (8 * sz) c) ⟨c, sz⟩ :=
  ⟨rfl, hc, Anneal.BitVec.maskEq_refl _ _⟩

/-- A fully-known scalar tnum determines the bits. -/
theorem scalarTnum_zero_mask_bits {sz : Nat} {v : BitVec (8 * sz)} {sc : ScalarInt}
    (h : ScalarTnum sz (BitVec.ofNat (8 * sz) 0) v sc) : sc.bits = v.toNat := by
  rw [scalarTnum_zero_mask_iff.1 h]

/-- Signed `evalCastValue` (sign extension or truncation between positive byte widths) computes
the ported `signExtend`, for arbitrary (possibly non-canonical) bits. -/
theorem evalCastValue_signed_eq_signExtend {srcSz dstSz : Nat} (hs : 0 < srcSz)
    (hd : 0 < dstSz) (bits : Nat) :
    Anneal.Scalars.evalCastValue ⟨bits, srcSz⟩ dstSz true =
      some ⟨(Anneal.BitVecArith.signExtend (8 * dstSz)
        (BitVec.ofNat (8 * srcSz) bits)).toNat, dstSz⟩ := by
  rw [← signExtendBits_eq_signExtend]
  unfold Anneal.Scalars.evalCastValue
  simp only [beq_zero_of_pos hs, beq_zero_of_pos hd, Bool.or_false]
  cases hble : Nat.ble dstSz srcSz with
  | true => rw [Anneal.Scalars.signExtendBits_of_le (Nat.le_of_ble_eq_true hble)]
  | false => rfl

/-- Tnum transfer through a signed integer cast between positive byte widths. -/
theorem scalarTnum_evalCastValue_signed {srcSz dstSz : Nat} (hs : 0 < srcSz) (hd : 0 < dstSz)
    {m v : BitVec (8 * srcSz)} {x : ScalarInt} (hx : ScalarTnum srcSz m v x) :
    ∃ r, Anneal.Scalars.evalCastValue x dstSz true = some r ∧
      ScalarTnum dstSz (Anneal.BitVecArith.signExtend (8 * dstSz) m)
        (Anneal.BitVecArith.signExtend (8 * dstSz) v) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  exact ⟨_, evalCastValue_signed_eq_signExtend hs hd xb,
    scalarTnum_of_bitVec _ (Anneal.BitVecArith.tnum_signExtend_sound (8 * dstSz) hxm)⟩

/-- The ported leading-zero count of a value whose highest set bit is bit `k`. -/
theorem clz_eq_of_bounds {w k : Nat} (x : BitVec w) (hk : k < w) (hlo : 2 ^ k ≤ x.toNat)
    (hhi : x.toNat < 2 ^ (k + 1)) : Anneal.BitVec.clz x = w - 1 - k := by
  have hc := Anneal.BitVec.clz_le x
  have hne : x ≠ BitVec.ofNat w 0 := by
    intro h
    rw [h, Anneal.BitVec.toNat_zero] at hlo
    have hpos := Nat.two_pow_pos k
    omega
  have hbit : x.toNat.testBit (w - Anneal.BitVec.clz x - 1) = true :=
    Anneal.BitVec.getLsbD_sub_clz_sub_one hne
  have h₁ : 2 ^ (w - Anneal.BitVec.clz x - 1) ≤ x.toNat := Nat.ge_two_pow_of_testBit hbit
  have h₂ : x.toNat < 2 ^ (w - Anneal.BitVec.clz x) := Anneal.BitVec.toNat_lt_two_pow_sub_clz x
  have e₁ : w - Anneal.BitVec.clz x - 1 < k + 1 :=
    (Nat.pow_lt_pow_iff_right (by decide)).1 (Nat.lt_of_le_of_lt h₁ hhi)
  have e₂ : k < w - Anneal.BitVec.clz x :=
    (Nat.pow_lt_pow_iff_right (by decide)).1 (Nat.lt_of_le_of_lt hlo h₂)
  omega

/-- `evalCtlz` is determined exactly by the position `k` of the operand's highest set bit. -/
theorem evalCtlz_eq_of_bounds {sz retBytes k : Nat} (hsz : 0 < sz) (hret : 0 < retBytes)
    {bits : Nat} (hk : k < 8 * sz) (hlo : 2 ^ k ≤ bits) (hhi : bits < 2 ^ (k + 1)) :
    evalCtlz ⟨bits, sz⟩ retBytes = some ⟨8 * sz - 1 - k, retBytes⟩ := by
  have hpow : 2 ^ (k + 1) ≤ 2 ^ (8 * sz) := Nat.pow_le_pow_right (by decide) (by omega)
  have hb : bits < scalarModulus sz := by
    rw [scalarModulus_eq]; exact Nat.lt_of_lt_of_le hhi hpow
  have ht := toNat_ofNat_of_lt hb
  rw [evalCtlz_eq_clz hsz hret, clz_eq_of_bounds _ hk (by rw [ht]; exact hlo) (by rw [ht]; exact hhi)]

/-- Interval-to-`ctlz` transfer: on any scalar whose unsigned interval `[lo, hi]` fixes the
highest set bit at position `k`, `evalCtlz` returns exactly `8 * sz - 1 - k`. -/
theorem scalarRange_evalCtlz {sz retBytes k : Nat} (hsz : 0 < sz) (hret : 0 < retBytes)
    {lo hi : BitVec (8 * sz)} {x : ScalarInt} (hx : ScalarRange sz lo hi x) (hk : k < 8 * sz)
    (hlo : 2 ^ k ≤ lo.toNat) (hhi : hi.toNat < 2 ^ (k + 1)) :
    evalCtlz x retBytes = some ⟨8 * sz - 1 - k, retBytes⟩ := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  have h₁ : lo.toNat ≤ (BitVec.ofNat (8 * sz) xb).toNat := hx₁
  have h₂ : (BitVec.ofNat (8 * sz) xb).toNat ≤ hi.toNat := hx₂
  rw [toNat_ofNat_of_lt hxb] at h₁ h₂
  exact evalCtlz_eq_of_bounds hsz hret hk (Nat.le_trans hlo h₁) (Nat.lt_of_le_of_lt h₂ hhi)

/-- A fully-known tnum on a literal scalar determines its bits (stated on `⟨b, sz⟩` so that the
conclusion mentions `b` verbatim, without a structure projection). -/
theorem scalarTnum_zero_mask_mk {sz : Nat} {v : BitVec (8 * sz)} {b : Nat}
    (h : ScalarTnum sz (BitVec.ofNat (8 * sz) 0) v ⟨b, sz⟩) : b = v.toNat :=
  scalarTnum_zero_mask_bits h

/-- Tnum transfer through `bitwiseAndBits` with a constant mask `c` (arbitrary, possibly
out-of-range): unknown bits survive only where `c` is set. -/
theorem scalarTnum_bitwiseAndBits_const {sz : Nat} {m v : BitVec (8 * sz)} {x : ScalarInt}
    (hx : ScalarTnum sz m v x) (c : Nat) :
    ScalarTnum sz (Anneal.BitVec.and m (BitVec.ofNat (8 * sz) c))
      (Anneal.BitVec.and v (BitVec.ofNat (8 * sz) c))
      ⟨bitwiseAndBits (8 * sz) x.bits c, sz⟩ := by
  have h := Anneal.BitVec.tnum_and_sound hx.2.2
    (Anneal.BitVec.maskEq_refl (BitVec.ofNat (8 * sz) 0) (BitVec.ofNat (8 * sz) c))
  rw [Anneal.BitVec.and_zero, Anneal.BitVec.and_zero, Anneal.BitVec.zero_or,
    Anneal.BitVec.or_zero] at h
  rw [bitwiseAndBits_eq_and]
  exact scalarTnum_of_bitVec _ h

/-- A literal scalar with canonical bits in `[lo, hi]` lies in the unsigned scalar interval. -/
theorem scalarRange_mk {sz : Nat} {lo hi : BitVec (8 * sz)} {b : Nat}
    (hb : b < scalarModulus sz) (h₁ : lo.toNat ≤ b) (h₂ : b ≤ hi.toNat) :
    ScalarRange sz lo hi ⟨b, sz⟩ :=
  scalarRange_iff_bits.2 ⟨hb, h₁, h₂⟩

/-- Logical right shift of arbitrary (possibly non-canonical) bits followed by wrapping is a
ported bitfield extraction from the `(w + s)`-bit vector: bits `s .. s + w - 1`. -/
theorem shiftRight_mod_eq_extractBits (a s w : Nat) :
    (a >>> s) % 2 ^ w = (Anneal.BitVecArith.extractBits (BitVec.ofNat (w + s) a) s w).toNat := by
  unfold Anneal.BitVecArith.extractBits
  rw [setWidth_eq_core, ushr_eq_core, _root_.BitVec.toNat_setWidth,
    _root_.BitVec.toNat_ushiftRight, _root_.BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.add_comm w s, Nat.pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod]

/-- Unconditional form of the unsigned `evalBinOp .shr` bridge: for arbitrary (possibly
non-canonical) left-operand bits, the result is the ported extraction of the `8 * szL` bits
starting at the masked shift amount. On canonical bits this is `evalBinOp_shr_unsigned_eq_ushr`. -/
theorem evalBinOp_shr_unsigned_eq_extractBits {szL szR : Nat} (hszL : 0 < szL) (hszR : 0 < szR)
    (a b : Nat) :
    Anneal.Scalars.evalBinOp .shr ⟨a, szL⟩ ⟨b, szR⟩ false =
      some ⟨(Anneal.BitVecArith.extractBits
        (BitVec.ofNat (8 * szL + b % (8 * szL)) a) (b % (8 * szL)) (8 * szL)).toNat, szL⟩ := by
  rw [Anneal.Scalars.evalBinOp_shr_unsigned hszL hszR, shiftRight_mod_eq_extractBits]

/-- Chunk width `0` is degenerate: `chunksOf 0` returns no chunks at all, so
`chunksOf_encodeElems` genuinely needs `0 < n`. -/
theorem chunksOf_encodeElems_zero_width {α : Type} (c : FixedByteCodec α 0) (xs : List α) :
    Anneal.ListChunks.chunksOf 0 (c.encodeElems xs) = [] :=
  Anneal.ListChunks.chunksOf_zero_size _

end Anneal.BitVecScalarsBridge
