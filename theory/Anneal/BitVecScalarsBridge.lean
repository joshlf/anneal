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
11. Sign-flag independence, operational `evalScalarBinOp` lifts, signed-integer arrays.
12. Checked/unchecked MIR arithmetic & shifts, bitwise interval bounds, big-endian decode and
    typed `[iN; n]` codecs.
13. Pure `evalBinOpChecked` & operational `*WithOverflow`/`*Unchecked` equivalences, signed
    subtraction range transfers, and typed signed-array transmutation.
14. Exact signed-overflow biconditionals, unary negation, unsigned/signed saturating arithmetic,
    `bitreverse`/`cttz` alignment, `extractBits`/product byte-splitting, and `ByteSeqValid`.
15. Sharpened `(k + 1)`-bit `cttz`/`evalCttzNonzero` tnums, signed saturating clamping, `ctpop`
    complement identities, and core `unchecked_*`/`three_way_compare` bridges.
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

/-- `evalBinOp .gt` (signed) decides ported `slt` with swapped arguments. -/
theorem evalBinOp_gt_signed_eq_slt {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    Anneal.Scalars.evalBinOp .gt ⟨a, sz⟩ ⟨b, sz⟩ true =
      some (boolToScalar
        (decide (Anneal.BitVecArith.slt (BitVec.ofNat (8 * sz) b) (BitVec.ofNat (8 * sz) a)))) := by
  rw [Anneal.Scalars.evalBinOp_gt_signed hsz, ← Anneal.Scalars.signedLt_eq_slt,
    signedLt_eq_decide]

/-- `evalBinOp .ge` (signed) decides ported `sle` with swapped arguments. -/
theorem evalBinOp_ge_signed_eq_sle {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    Anneal.Scalars.evalBinOp .ge ⟨a, sz⟩ ⟨b, sz⟩ true =
      some (boolToScalar
        (decide (Anneal.BitVecArith.sle (BitVec.ofNat (8 * sz) b) (BitVec.ofNat (8 * sz) a)))) := by
  rw [Anneal.Scalars.evalBinOp_ge_signed hsz, ← Anneal.Scalars.signedLe_eq_sle,
    signedLe_eq_decide]

/-- Wrapping multiplication of scalar bits is ported `Anneal.BitVec.mul` (arbitrary operands). -/
theorem mul_mod_eq_toNat_mul (a b sz : Nat) :
    (a * b) % 2 ^ (8 * sz) =
      (Anneal.BitVec.mul (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)).toNat := by
  rw [Anneal.BitVec.toNat_mul, natMod_eq, natPow_eq, _root_.BitVec.toNat_ofNat,
    _root_.BitVec.toNat_ofNat, ← Nat.mul_mod]

/-- `evalBinOp .mul` computes ported `mul` (arbitrary operands). -/
theorem evalBinOp_mul_eq_mul {sz : Nat} (hsz : 0 < sz) (a b : Nat) (isSigned : Bool) :
    Anneal.Scalars.evalBinOp .mul ⟨a, sz⟩ ⟨b, sz⟩ isSigned =
      some ⟨(Anneal.BitVec.mul (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)).toNat, sz⟩ := by
  rw [Anneal.Scalars.evalBinOp_mul_apply hsz, mul_mod_eq_toNat_mul]

/-- `evalBinOp .div` (unsigned) computes ported `udiv` on canonical operands with non-zero divisor. -/
theorem evalBinOp_div_unsigned_eq_udiv {sz : Nat} (hsz : 0 < sz) {a b : Nat}
    (ha : a < scalarModulus sz) (hb : b < scalarModulus sz) (hbz : b ≠ 0) :
    Anneal.Scalars.evalBinOp .div ⟨a, sz⟩ ⟨b, sz⟩ false =
      some ⟨(Anneal.BitVec.udiv (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)).toNat, sz⟩ := by
  rw [Anneal.Scalars.evalBinOp_div_unsigned hsz hbz, Anneal.BitVec.toNat_udiv, natDiv_eq,
    toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb]
  rw [scalarModulus_eq] at ha
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha)]

/-- `evalBinOp .rem` (unsigned) computes ported `urem` on canonical operands with non-zero divisor. -/
theorem evalBinOp_rem_unsigned_eq_urem {sz : Nat} (hsz : 0 < sz) {a b : Nat}
    (ha : a < scalarModulus sz) (hb : b < scalarModulus sz) (hbz : b ≠ 0) :
    Anneal.Scalars.evalBinOp .rem ⟨a, sz⟩ ⟨b, sz⟩ false =
      some ⟨(Anneal.BitVecArith.urem (BitVec.ofNat (8 * sz) a)
        (BitVec.ofNat (8 * sz) b)).toNat, sz⟩ := by
  rw [Anneal.Scalars.evalBinOp_rem_unsigned hsz hbz, Anneal.BitVecArith.toNat_urem, natMod_eq,
    toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb]
  rw [scalarModulus_eq] at ha
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le a b) ha)]

/-- Every `evalBinOp` on a zero-width left operand is rejected: the `sz = 0` edge is
excluded by the evaluator, not silently treated as a `BitVec 0` computation. -/
theorem evalBinOp_eq_none_of_size_zero (op : BinOp) (a : Nat) (rhs : ScalarInt)
    (isSigned : Bool) :
    Anneal.Scalars.evalBinOp op ⟨a, 0⟩ rhs isSigned = none := rfl

/-- `evalUnOp .not` on integer scalars computes ported `Anneal.BitVec.not` (arbitrary operand). -/
theorem evalUnOp_not_eq_not {sz : Nat} (hsz : 0 < sz) (a : Nat) :
    Anneal.Scalars.evalUnOp .not ⟨a, sz⟩ false =
      some ⟨(Anneal.BitVec.not (BitVec.ofNat (8 * sz) a)).toNat, sz⟩ := by
  rw [Anneal.Scalars.evalUnOp_not_int_apply hsz, Anneal.BitVecArith.toNat_not_eq_sub, natPow_eq,
    _root_.BitVec.toNat_ofNat]

/-- `evalUnOp .neg` computes ported `Anneal.BitVecArith.neg` (arbitrary operand). -/
theorem evalUnOp_neg_eq_neg {sz : Nat} (hsz : 0 < sz) (a : Nat) (isBool : Bool) :
    Anneal.Scalars.evalUnOp .neg ⟨a, sz⟩ isBool =
      some ⟨(Anneal.BitVecArith.neg (BitVec.ofNat (8 * sz) a)).toNat, sz⟩ := by
  rw [Anneal.Scalars.evalUnOp_neg_apply hsz, Anneal.BitVecArith.toNat_neg, natMod_eq, natPow_eq,
    _root_.BitVec.toNat_ofNat]

/-- Operational `evalUnaryNot` on unsigned integer types computes ported `Anneal.BitVec.not`. -/
theorem evalUnaryNot_uint_eq_not {sz : Nat} (hsz : 0 < sz) (a : Nat) (w : UintTy) (idx : LayoutIdx)
    (locals : List LocalSlot) (mem : Memory) :
    evalUnaryNot ⟨a, sz⟩ (some { kind := .uint w, layoutIdx := idx }) locals mem =
      .ok (.scalar ⟨(Anneal.BitVec.not (BitVec.ofNat (8 * sz) a)).toNat, sz⟩) locals mem := by
  rw [Anneal.Scalars.evalUnaryNot_uint_eq_evalUnOp hsz w idx]
  rfl

/-- Operational `evalUnaryNot` on signed integer types computes ported `Anneal.BitVec.not`. -/
theorem evalUnaryNot_int_eq_not {sz : Nat} (hsz : 0 < sz) (a : Nat) (w : IntTy) (idx : LayoutIdx)
    (locals : List LocalSlot) (mem : Memory) :
    evalUnaryNot ⟨a, sz⟩ (some { kind := .int w, layoutIdx := idx }) locals mem =
      .ok (.scalar ⟨(Anneal.BitVec.not (BitVec.ofNat (8 * sz) a)).toNat, sz⟩) locals mem := by
  rw [Anneal.Scalars.evalUnaryNot_int_eq_evalUnOp hsz w idx]
  rfl

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

/-- Operational `evalScalarBinOp .mul` computes ported `mul`. -/
theorem evalScalarBinOp_mul_eq_mul {sz : Nat} (hsz : 0 < sz) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp .mul ⟨a, sz⟩ ⟨b, sz⟩ locals mem isSigned =
      .ok (.scalar
        ⟨(Anneal.BitVec.mul (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)).toNat, sz⟩)
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_mul hsz, mul_mod_eq_toNat_mul]

/-- Operational `evalScalarBinOp .div` (unsigned) computes ported `udiv` on canonical operands. -/
theorem evalScalarBinOp_div_unsigned_eq_udiv {sz : Nat} (hsz : 0 < sz) {a b : Nat}
    (ha : a < scalarModulus sz) (hb : b < scalarModulus sz) (hbz : b ≠ 0)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .div ⟨a, sz⟩ ⟨b, sz⟩ locals mem false =
      .ok (.scalar
        ⟨(Anneal.BitVec.udiv (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)).toNat, sz⟩)
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_div_unsigned hsz hbz, Anneal.BitVec.toNat_udiv, natDiv_eq,
    toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb]
  rw [scalarModulus_eq] at ha
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha)]

/-- Operational `evalScalarBinOp .rem` (unsigned) computes ported `urem` on canonical operands. -/
theorem evalScalarBinOp_rem_unsigned_eq_urem {sz : Nat} (hsz : 0 < sz) {a b : Nat}
    (ha : a < scalarModulus sz) (hb : b < scalarModulus sz) (hbz : b ≠ 0)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .rem ⟨a, sz⟩ ⟨b, sz⟩ locals mem false =
      .ok (.scalar
        ⟨(Anneal.BitVecArith.urem (BitVec.ofNat (8 * sz) a)
          (BitVec.ofNat (8 * sz) b)).toNat, sz⟩)
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_rem_unsigned hsz hbz, Anneal.BitVecArith.toNat_urem, natMod_eq,
    toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb]
  rw [scalarModulus_eq] at ha
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le a b) ha)]

/-- Operational `evalScalarBinOp .lt` (signed) decides ported `slt`. -/
theorem evalScalarBinOp_lt_signed_eq_slt {sz : Nat} (hsz : 0 < sz) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .lt ⟨a, sz⟩ ⟨b, sz⟩ locals mem true =
      .ok (.scalar (boolToScalar
        (decide (Anneal.BitVecArith.slt (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)))))
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_lt_signed hsz, ← Anneal.Scalars.signedLt_eq_slt,
    signedLt_eq_decide]

/-- Operational `evalScalarBinOp .le` (signed) decides ported `sle`. -/
theorem evalScalarBinOp_le_signed_eq_sle {sz : Nat} (hsz : 0 < sz) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .le ⟨a, sz⟩ ⟨b, sz⟩ locals mem true =
      .ok (.scalar (boolToScalar
        (decide (Anneal.BitVecArith.sle (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)))))
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_le_signed hsz, ← Anneal.Scalars.signedLe_eq_sle,
    signedLe_eq_decide]

/-- Operational `evalScalarBinOp .gt` (signed) decides ported `slt` with swapped arguments. -/
theorem evalScalarBinOp_gt_signed_eq_slt {sz : Nat} (hsz : 0 < sz) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .gt ⟨a, sz⟩ ⟨b, sz⟩ locals mem true =
      .ok (.scalar (boolToScalar
        (decide (Anneal.BitVecArith.slt (BitVec.ofNat (8 * sz) b) (BitVec.ofNat (8 * sz) a)))))
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_gt_signed hsz, ← Anneal.Scalars.signedLt_eq_slt,
    signedLt_eq_decide]

/-- Operational `evalScalarBinOp .ge` (signed) decides ported `sle` with swapped arguments. -/
theorem evalScalarBinOp_ge_signed_eq_sle {sz : Nat} (hsz : 0 < sz) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .ge ⟨a, sz⟩ ⟨b, sz⟩ locals mem true =
      .ok (.scalar (boolToScalar
        (decide (Anneal.BitVecArith.sle (BitVec.ofNat (8 * sz) b) (BitVec.ofNat (8 * sz) a)))))
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_ge_signed hsz, ← Anneal.Scalars.signedLe_eq_sle,
    signedLe_eq_decide]

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

/-- `evalWrappingMul` computes ported `Anneal.BitVec.mul` (arbitrary operands). -/
theorem evalWrappingMul_eq_mul {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    evalWrappingMul ⟨a, sz⟩ ⟨b, sz⟩ =
      some ⟨(Anneal.BitVec.mul (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)).toNat, sz⟩ := by
  have h0 : Nat.beq sz 0 = false := beq_zero_of_pos hsz
  have h1 : Nat.beq sz sz = true := nat_beq_self sz
  unfold evalWrappingMul
  simp only [h0, h1, Bool.not_true, Bool.or_false]
  rw [Anneal.Scalars.wrapScalarBits_eq_mod_modulus, Anneal.Scalars.wrapScalarBits_eq_mod_modulus,
    Anneal.Scalars.wrapScalarBits_eq_mod_modulus, scalarModulus_eq, natMul_eq, ← Nat.mul_mod,
    mul_mod_eq_toNat_mul]

/-- `evalWrappingMul` is rejected exactly on zero-width or mismatched-width operands. -/
theorem evalWrappingMul_eq_none_iff (x y : ScalarInt) :
    evalWrappingMul x y = none ↔ x.sizeBytes = 0 ∨ x.sizeBytes ≠ y.sizeBytes := by
  unfold evalWrappingMul
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

/-- `extractField` on canonicalized (`wrapScalarBits`) bits is ported `extractBits`, for
arbitrary (possibly non-canonical) `x`. -/
theorem extractField_wrap_eq_extractBits (sz x lo len : Nat) :
    extractField sz (wrapScalarBits x (scalarModulus sz)) lo len =
      (Anneal.BitVecArith.extractBits (BitVec.ofNat (8 * sz) x) lo len).toNat := by
  rw [wrapScalarBits_eq_toNat, extractField_toNat]

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
`(a << lo₁) | (b << lo₂)` force equal in-range fields when the bit ranges are disjoint,
including zero-width fields (`len₁ = 0` or `len₂ = 0`, even at `lo = 8 * sz`). -/
theorem evalBinOp_pack_injective {sz szR : Nat} (hsz : 0 < sz) (hszR : 0 < szR)
    {lo₁ len₁ lo₂ len₂ a₁ b₁ a₂ b₂ : Nat}
    (ha₁ : a₁ < 2 ^ len₁) (hb₁ : b₁ < 2 ^ len₂) (ha₂ : a₂ < 2 ^ len₁) (hb₂ : b₂ < 2 ^ len₂)
    (h₁ : lo₁ + len₁ ≤ 8 * sz) (h₂ : lo₂ + len₂ ≤ 8 * sz)
    (hd : lo₁ + len₁ ≤ lo₂ ∨ lo₂ + len₂ ≤ lo₁)
    (h : (Anneal.Scalars.evalBinOp .shl ⟨a₁, sz⟩ ⟨lo₁, szR⟩ false).bind (fun sa =>
          (Anneal.Scalars.evalBinOp .shl ⟨b₁, sz⟩ ⟨lo₂, szR⟩ false).bind (fun sb =>
            Anneal.Scalars.evalBinOp .bitOr sa sb false)) =
        (Anneal.Scalars.evalBinOp .shl ⟨a₂, sz⟩ ⟨lo₁, szR⟩ false).bind (fun sa =>
          (Anneal.Scalars.evalBinOp .shl ⟨b₂, sz⟩ ⟨lo₂, szR⟩ false).bind (fun sb =>
            Anneal.Scalars.evalBinOp .bitOr sa sb false))) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  cases Nat.eq_zero_or_pos len₁ with
  | inl hl₁ =>
    subst hl₁
    have ha₁0 : a₁ = 0 := by simpa using ha₁
    have ha₂0 : a₂ = 0 := by simpa using ha₂
    subst ha₁0; subst ha₂0
    cases Nat.eq_zero_or_pos len₂ with
    | inl hl₂ =>
      subst hl₂
      have hb₁0 : b₁ = 0 := by simpa using hb₁
      have hb₂0 : b₂ = 0 := by simpa using hb₂
      exact ⟨rfl, hb₁0.trans hb₂0.symm⟩
    | inr hl₂ =>
      have hlo₂ : lo₂ < 8 * sz := by omega
      simp only [Anneal.Scalars.evalBinOp_shl_apply hsz hszR, Option.bind_some,
        Anneal.Scalars.evalBinOp_bitOr_apply hsz, Nat.mod_eq_of_lt hlo₂] at h
      have hbits : (0 ||| (b₁ <<< lo₂) % 2 ^ (8 * sz)) % 2 ^ (8 * sz) =
          (0 ||| (b₂ <<< lo₂) % 2 ^ (8 * sz)) % 2 ^ (8 * sz) := by
        simpa [Nat.zero_shiftLeft] using (ScalarInt.mk.inj (Option.some.inj h)).1
      rw [Nat.zero_or, Nat.zero_or, Nat.mod_mod, Nat.mod_mod,
        ← Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod,
        ← Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod] at hbits
      have e₁ := extractField_shiftLeftBits_self hb₁ h₂
      have e₂ := extractField_shiftLeftBits_self hb₂ h₂
      rw [hbits] at e₁
      exact ⟨rfl, e₁.symm.trans e₂⟩
  | inr hl₁ =>
    cases Nat.eq_zero_or_pos len₂ with
    | inl hl₂ =>
      subst hl₂
      have hb₁0 : b₁ = 0 := by simpa using hb₁
      have hb₂0 : b₂ = 0 := by simpa using hb₂
      subst hb₁0; subst hb₂0
      have hlo₁ : lo₁ < 8 * sz := by omega
      simp only [Anneal.Scalars.evalBinOp_shl_apply hsz hszR, Option.bind_some,
        Anneal.Scalars.evalBinOp_bitOr_apply hsz, Nat.mod_eq_of_lt hlo₁] at h
      have hbits : ((a₁ <<< lo₁) % 2 ^ (8 * sz) ||| 0) % 2 ^ (8 * sz) =
          ((a₂ <<< lo₁) % 2 ^ (8 * sz) ||| 0) % 2 ^ (8 * sz) := by
        simpa [Nat.zero_shiftLeft] using (ScalarInt.mk.inj (Option.some.inj h)).1
      rw [Nat.or_zero, Nat.or_zero, Nat.mod_mod, Nat.mod_mod,
        ← Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod,
        ← Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod] at hbits
      have e₁ := extractField_shiftLeftBits_self ha₁ h₁
      have e₂ := extractField_shiftLeftBits_self ha₂ h₁
      rw [hbits] at e₁
      exact ⟨e₁.symm.trans e₂, rfl⟩
    | inr hl₂ =>
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

/-- No non-canonical scalar (`sc.bits ≥ scalarModulus sz`) satisfies any `ScalarTnum`. -/
theorem scalarTnum_not_noncanonical {sz : Nat} {m v : BitVec (8 * sz)} {sc : ScalarInt}
    (hge : scalarModulus sz ≤ sc.bits) : ¬ ScalarTnum sz m v sc :=
  fun h => Nat.not_lt_of_ge hge h.2.1

/-- Reference-value canonicalization for `ScalarTnum` (`v ↔ v &&& ~~~m`). -/
theorem scalarTnum_canonical {sz : Nat} {m v : BitVec (8 * sz)} {sc : ScalarInt} :
    ScalarTnum sz m v sc ↔ ScalarTnum sz m (Anneal.BitVec.and v (Anneal.BitVec.not m)) sc :=
  ⟨fun h => ⟨h.1, h.2.1, Anneal.BitVec.maskEq_canonical.1 h.2.2⟩,
   fun h => ⟨h.1, h.2.1, Anneal.BitVec.maskEq_canonical.2 h.2.2⟩⟩

/-- Mask monotonicity: weakening the unknown mask preserves `ScalarTnum`. -/
theorem scalarTnum_mono {sz : Nat} {m₁ m₂ v : BitVec (8 * sz)} {sc : ScalarInt}
    (hsub : Anneal.BitVec.and m₁ (Anneal.BitVec.not m₂) = BitVec.ofNat (8 * sz) 0)
    (h : ScalarTnum sz m₁ v sc) : ScalarTnum sz m₂ v sc :=
  ⟨h.1, h.2.1, Anneal.BitVec.maskEq_mono hsub h.2.2⟩

/-- Exact meet (intersection) of two `ScalarTnum` abstractions: any scalar satisfying both
satisfies the sharpened mask `m₁ &&& m₂` with reference value `(v₁ &&& ~~~m₁) ||| (v₂ &&& ~~~m₂)`. -/
theorem scalarTnum_inter {sz : Nat} {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {sc : ScalarInt}
    (h₁ : ScalarTnum sz m₁ v₁ sc) (h₂ : ScalarTnum sz m₂ v₂ sc) :
    ScalarTnum sz (Anneal.BitVec.and m₁ m₂)
      (Anneal.BitVec.or (Anneal.BitVec.and v₁ (Anneal.BitVec.not m₁))
        (Anneal.BitVec.and v₂ (Anneal.BitVec.not m₂))) sc := by
  refine ⟨h₁.1, h₁.2.1, Anneal.BitVec.maskEq_iff_getLsbD.2 (fun i hi hm => ?_)⟩
  rw [Anneal.BitVec.getLsbD_and] at hm
  have e₁ := Anneal.BitVec.maskEq_iff_getLsbD.1 h₁.2.2 i hi
  have e₂ := Anneal.BitVec.maskEq_iff_getLsbD.1 h₂.2.2 i hi
  rw [Anneal.BitVec.getLsbD_or, Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_and,
    Anneal.BitVec.getLsbD_not_of_lt _ hi, Anneal.BitVec.getLsbD_not_of_lt _ hi]
  cases hm₁ : Anneal.BitVec.getLsbD m₁ i with
  | false =>
    cases hm₂ : Anneal.BitVec.getLsbD m₂ i with
    | false =>
      have hv₁ := e₁ hm₁
      have hv₂ := e₂ hm₂
      rw [← hv₁, ← hv₂]
      simp
    | true =>
      rw [e₁ hm₁]
      simp
  | true =>
    cases hm₂ : Anneal.BitVec.getLsbD m₂ i with
    | false =>
      rw [e₂ hm₂]
      simp
    | true =>
      rw [hm₁, hm₂] at hm
      cases hm

/-- Tnum-to-range widening (`Anneal.BitVec.tnum_and_bounds_sound`, closing the `ScalarTnum ↔
ScalarRange` connection without requiring canonicality of `v`): every scalar satisfying
`ScalarTnum sz m v` lies in `[v &&& ~~~m, v ||| m]`. -/
theorem scalarRange_of_scalarTnum {sz : Nat} {m v : BitVec (8 * sz)} {sc : ScalarInt}
    (h : ScalarTnum sz m v sc) :
    ScalarRange sz (Anneal.BitVec.and v (Anneal.BitVec.not m)) (Anneal.BitVec.or v m) sc := by
  have hc : Anneal.BitVec.MaskEq m (BitVec.ofNat (8 * sz) sc.bits)
      (Anneal.BitVec.and v (Anneal.BitVec.not m)) :=
    Anneal.BitVec.maskEq_canonical.1 h.2.2
  have hdisj : Anneal.BitVec.and (Anneal.BitVec.and v (Anneal.BitVec.not m)) m =
      BitVec.ofNat (8 * sz) 0 := by
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_and,
      Anneal.BitVec.getLsbD_not_of_lt _ hi, Anneal.BitVec.getLsbD_zero]
    cases Anneal.BitVec.getLsbD m i <;> simp
  have hor : Anneal.BitVec.or (Anneal.BitVec.and v (Anneal.BitVec.not m)) m =
      Anneal.BitVec.or v m := by
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [Anneal.BitVec.getLsbD_or, Anneal.BitVec.getLsbD_and,
      Anneal.BitVec.getLsbD_not_of_lt _ hi, Anneal.BitVec.getLsbD_or]
    cases Anneal.BitVec.getLsbD m i <;> simp
  have hb := Anneal.BitVec.tnum_and_bounds_sound hc hdisj
  rw [hor] at hb
  exact ⟨h.1, h.2.1, hb.1, hb.2⟩

/-- No non-canonical scalar (`sc.bits ≥ scalarModulus sz`) satisfies any `ScalarRange`. -/
theorem scalarRange_not_noncanonical {sz : Nat} {lo hi : BitVec (8 * sz)} {sc : ScalarInt}
    (hge : scalarModulus sz ≤ sc.bits) : ¬ ScalarRange sz lo hi sc :=
  fun h => Nat.not_lt_of_ge hge h.2.1

/-- No non-canonical scalar (`sc.bits ≥ scalarModulus sz`) satisfies any `ScalarSRange`. -/
theorem scalarSRange_not_noncanonical {sz : Nat} {lo hi : BitVec (8 * sz)} {sc : ScalarInt}
    (hge : scalarModulus sz ≤ sc.bits) : ¬ ScalarSRange sz lo hi sc :=
  fun h => Nat.not_lt_of_ge hge h.2.1

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

/-- Tnum transfer through `extractField` (`Anneal.BitVecArith.tnum_extractBits_sound`): extracting
`len` bits starting at `lo` from a scalar abstracted by `(m, v)` satisfies the extracted tnum
at width `len`. -/
theorem scalarTnum_extractField {sz : Nat} {m v : BitVec (8 * sz)} {x : ScalarInt}
    (hx : ScalarTnum sz m v x) (lo len : Nat) :
    Anneal.BitVec.MaskEq (Anneal.BitVecArith.extractBits m lo len)
      (BitVec.ofNat len (extractField sz x.bits lo len))
      (Anneal.BitVecArith.extractBits v lo len) := by
  rw [extractField_eq_extractBits hx.2.1, ofNat_toNat_self]
  exact Anneal.BitVecArith.tnum_extractBits_sound lo len hx.2.2

/-- Tnum bitwise-NOT transfer through `evalUnOp .not` (`Anneal.BitVec.tnum_not_sound`). -/
theorem scalarTnum_evalUnOp_not {sz : Nat} (hsz : 0 < sz) {m v : BitVec (8 * sz)} {x : ScalarInt}
    (hx : ScalarTnum sz m v x) :
    ∃ r, Anneal.Scalars.evalUnOp .not x false = some r ∧
      ScalarTnum sz m (Anneal.BitVec.not v) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  exact ⟨_, evalUnOp_not_eq_not hsz xb, scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_not_sound hxm)⟩

/-- Operational tnum bitwise-NOT transfer through `Trusted` `evalUnaryNot` on unsigned types. -/
theorem scalarTnum_evalUnaryNot_uint {sz : Nat} (hsz : 0 < sz) {m v : BitVec (8 * sz)}
    {x : ScalarInt} (w : UintTy) (idx : LayoutIdx) (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarTnum sz m v x) :
    ∃ r, evalUnaryNot x (some { kind := .uint w, layoutIdx := idx }) locals mem =
        .ok (.scalar r) locals mem ∧
      ScalarTnum sz m (Anneal.BitVec.not v) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  exact ⟨_, evalUnaryNot_uint_eq_not hsz xb w idx locals mem,
    scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_not_sound hxm)⟩

/-- Operational tnum bitwise-NOT transfer through `Trusted` `evalUnaryNot` on signed types. -/
theorem scalarTnum_evalUnaryNot_int {sz : Nat} (hsz : 0 < sz) {m v : BitVec (8 * sz)}
    {x : ScalarInt} (w : IntTy) (idx : LayoutIdx) (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarTnum sz m v x) :
    ∃ r, evalUnaryNot x (some { kind := .int w, layoutIdx := idx }) locals mem =
        .ok (.scalar r) locals mem ∧
      ScalarTnum sz m (Anneal.BitVec.not v) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  exact ⟨_, evalUnaryNot_int_eq_not hsz xb w idx locals mem,
    scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_not_sound hxm)⟩

/-- Operational tnum AND transfer through `Trusted` `evalScalarBinOp .bitAnd`. -/
theorem scalarTnum_evalScalarBinOp_bitAnd {sz : Nat} (hsz : 0 < sz)
    {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt} (locals : List LocalSlot) (mem : Memory)
    (isSigned : Bool) (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ∃ r, evalScalarBinOp .bitAnd x y locals mem isSigned = .ok (.scalar r) locals mem ∧
      ScalarTnum sz
        (Anneal.BitVec.or (Anneal.BitVec.or (Anneal.BitVec.and m₁ m₂) (Anneal.BitVec.and m₁ v₂))
          (Anneal.BitVec.and v₁ m₂))
        (Anneal.BitVec.and v₁ v₂) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  obtain ⟨yb, rfl, _, hym⟩ := scalarTnum_exists hy
  exact ⟨_, evalScalarBinOp_bitAnd_eq_and hsz xb yb locals mem isSigned,
    scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_and_sound hxm hym)⟩

/-- Operational tnum OR transfer through `Trusted` `evalScalarBinOp .bitOr`. -/
theorem scalarTnum_evalScalarBinOp_bitOr {sz : Nat} (hsz : 0 < sz)
    {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt} (locals : List LocalSlot) (mem : Memory)
    (isSigned : Bool) (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ∃ r, evalScalarBinOp .bitOr x y locals mem isSigned = .ok (.scalar r) locals mem ∧
      ScalarTnum sz
        (Anneal.BitVec.or
          (Anneal.BitVec.or (Anneal.BitVec.and m₁ m₂)
            (Anneal.BitVec.and m₁ (Anneal.BitVec.not v₂)))
          (Anneal.BitVec.and (Anneal.BitVec.not v₁) m₂))
        (Anneal.BitVec.or v₁ v₂) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  obtain ⟨yb, rfl, _, hym⟩ := scalarTnum_exists hy
  exact ⟨_, evalScalarBinOp_bitOr_eq_or hsz xb yb locals mem isSigned,
    scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_or_sound hxm hym)⟩

/-- Operational tnum XOR transfer through `Trusted` `evalScalarBinOp .bitXor`. -/
theorem scalarTnum_evalScalarBinOp_bitXor {sz : Nat} (hsz : 0 < sz)
    {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt} (locals : List LocalSlot) (mem : Memory)
    (isSigned : Bool) (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ∃ r, evalScalarBinOp .bitXor x y locals mem isSigned = .ok (.scalar r) locals mem ∧
      ScalarTnum sz (Anneal.BitVec.or m₁ m₂) (Anneal.BitVec.xor v₁ v₂) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  obtain ⟨yb, rfl, _, hym⟩ := scalarTnum_exists hy
  exact ⟨_, evalScalarBinOp_bitXor_eq_xor hsz xb yb locals mem isSigned,
    scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_xor_sound hxm hym)⟩

/-- Operational tnum left-shift transfer through `Trusted` `evalScalarBinOp .shl`. -/
theorem scalarTnum_evalScalarBinOp_shl {sz : Nat} (hsz : 0 < sz) {m v : BitVec (8 * sz)}
    {x : ScalarInt} (y : ScalarInt) (hy : 0 < y.sizeBytes) (locals : List LocalSlot) (mem : Memory)
    (isSigned : Bool) (hx : ScalarTnum sz m v x) :
    ∃ r, evalScalarBinOp .shl x y locals mem isSigned = .ok (.scalar r) locals mem ∧
      ScalarTnum sz (Anneal.BitVec.shl m (y.bits % (8 * sz)))
        (Anneal.BitVec.shl v (y.bits % (8 * sz))) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  cases y with
  | mk yb ys =>
    exact ⟨_, evalScalarBinOp_shl_eq_shl hsz hy xb yb locals mem isSigned,
      scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_shl_sound _ hxm)⟩

/-- Operational tnum logical-right-shift transfer through unsigned `Trusted` `evalScalarBinOp .shr`. -/
theorem scalarTnum_evalScalarBinOp_shr_unsigned {sz : Nat} (hsz : 0 < sz) {m v : BitVec (8 * sz)}
    {x : ScalarInt} (y : ScalarInt) (hy : 0 < y.sizeBytes) (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarTnum sz m v x) :
    ∃ r, evalScalarBinOp .shr x y locals mem false = .ok (.scalar r) locals mem ∧
      ScalarTnum sz (Anneal.BitVec.ushr m (y.bits % (8 * sz)))
        (Anneal.BitVec.ushr v (y.bits % (8 * sz))) r := by
  obtain ⟨xb, rfl, hxb, hxm⟩ := scalarTnum_exists hx
  cases y with
  | mk yb ys =>
    exact ⟨_, evalScalarBinOp_shr_unsigned_eq_ushr hsz hy hxb yb locals mem,
      scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_ushr_sound _ hxm)⟩

/-- Operational tnum arithmetic-right-shift transfer through signed `Trusted` `evalScalarBinOp .shr`. -/
theorem scalarTnum_evalScalarBinOp_shr_signed {sz : Nat} (hsz : 0 < sz) {m v : BitVec (8 * sz)}
    {x : ScalarInt} (y : ScalarInt) (hy : 0 < y.sizeBytes) (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarTnum sz m v x) :
    ∃ r, evalScalarBinOp .shr x y locals mem true = .ok (.scalar r) locals mem ∧
      ScalarTnum sz (Anneal.BitVecArith.ashr m (y.bits % (8 * sz)))
        (Anneal.BitVecArith.ashr v (y.bits % (8 * sz))) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  cases y with
  | mk yb ys =>
    exact ⟨_, evalScalarBinOp_shr_signed_eq_ashr hsz hy xb yb locals mem,
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

/-- Operational tnum addition transfer through `Trusted` `evalScalarBinOp .add`. -/
theorem scalarTnum_evalScalarBinOp_add {sz : Nat} (hsz : 0 < sz)
    {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt} (locals : List LocalSlot) (mem : Memory)
    (isSigned : Bool) (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ∃ r, evalScalarBinOp .add x y locals mem isSigned = .ok (.scalar r) locals mem ∧
      ScalarTnum sz (tnumAddMask m₁ v₁ m₂ v₂) (tnumAddValue m₁ v₁ m₂ v₂) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  obtain ⟨yb, rfl, _, hym⟩ := scalarTnum_exists hy
  exact ⟨_, evalScalarBinOp_add_eq_add hsz xb yb locals mem isSigned,
    scalarTnum_of_bitVec _ (tnumAdd_sound hxm hym)⟩

/-- Operational tnum subtraction transfer through `Trusted` `evalScalarBinOp .sub`. -/
theorem scalarTnum_evalScalarBinOp_sub {sz : Nat} (hsz : 0 < sz)
    {m₁ v₁ m₂ v₂ : BitVec (8 * sz)} {x y : ScalarInt} (locals : List LocalSlot) (mem : Memory)
    (isSigned : Bool) (hx : ScalarTnum sz m₁ v₁ x) (hy : ScalarTnum sz m₂ v₂ y) :
    ∃ r, evalScalarBinOp .sub x y locals mem isSigned = .ok (.scalar r) locals mem ∧
      ScalarTnum sz (tnumSubMask m₁ v₁ m₂ v₂) (tnumSubValue m₁ v₁ m₂ v₂) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  obtain ⟨yb, rfl, _, hym⟩ := scalarTnum_exists hy
  exact ⟨_, evalScalarBinOp_sub_eq_sub hsz xb yb locals mem isSigned,
    scalarTnum_of_bitVec _ (tnumSub_sound hxm hym)⟩

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

/-- Unsigned interval intersection (`Anneal.BitVecArith.range_intersect_sound`). -/
theorem scalarRange_intersect {sz : Nat} {lo₁ hi₁ lo₂ hi₂ : BitVec (8 * sz)} {x : ScalarInt}
    (h₁ : ScalarRange sz lo₁ hi₁ x) (h₂ : ScalarRange sz lo₂ hi₂ x) :
    ScalarRange sz (Anneal.BitVecArith.bvMax lo₁ lo₂) (Anneal.BitVecArith.bvMin hi₁ hi₂) x := by
  have hs := Anneal.BitVecArith.range_intersect_sound h₁.2.2 h₂.2.2
  exact ⟨h₁.1, h₁.2.1, hs.1, hs.2⟩

/-- Signed interval intersection (`Anneal.BitVecArith.signed_range_intersect_sound`). -/
theorem scalarSRange_intersect {sz : Nat} {lo₁ hi₁ lo₂ hi₂ : BitVec (8 * sz)} {x : ScalarInt}
    (h₁ : ScalarSRange sz lo₁ hi₁ x) (h₂ : ScalarSRange sz lo₂ hi₂ x) :
    ScalarSRange sz (Anneal.BitVecArith.sbvMax lo₁ lo₂) (Anneal.BitVecArith.sbvMin hi₁ hi₂) x := by
  have hs := Anneal.BitVecArith.signed_range_intersect_sound h₁.2.2 h₂.2.2
  exact ⟨h₁.1, h₁.2.1, hs.1, hs.2⟩

/-- Operational unsigned interval transfer through `Trusted` `evalScalarBinOp .add`. -/
theorem scalarRange_evalScalarBinOp_add {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt} (locals : List LocalSlot)
    (mem : Memory) (isSigned : Bool)
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y) :
    ∃ r, evalScalarBinOp .add x y locals mem isSigned = .ok (.scalar r) locals mem ∧
      ScalarRange sz (rangeAddLo a_lo a_hi b_lo b_hi) (rangeAddHi a_lo a_hi b_lo b_hi) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarRange_exists hy
  have hs := rangeAdd_sound hx₁ hx₂ hy₁ hy₂
  exact ⟨_, evalScalarBinOp_add_eq_add hsz xb yb locals mem isSigned,
    scalarRange_of_bitVec _ hs.1 hs.2⟩

/-- Operational unsigned interval transfer through unsigned `Trusted` `evalScalarBinOp .shr`. -/
theorem scalarRange_evalScalarBinOp_shr_unsigned {sz : Nat} (hsz : 0 < sz)
    {umin umax : BitVec (8 * sz)} {x : ScalarInt} (y : ScalarInt) (hy : 0 < y.sizeBytes)
    (locals : List LocalSlot) (mem : Memory) {kmin kmax : Nat}
    (hx : ScalarRange sz umin umax x)
    (hk₁ : kmin ≤ y.bits % (8 * sz)) (hk₂ : y.bits % (8 * sz) ≤ kmax) :
    ∃ r, evalScalarBinOp .shr x y locals mem false = .ok (.scalar r) locals mem ∧
      ScalarRange sz (Anneal.BitVec.ushr umin kmax) (Anneal.BitVec.ushr umax kmin) r := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  cases y with
  | mk yb ys =>
    have hs := Anneal.BitVecArith.range_ushr_sound hx₁ hx₂ hk₁ hk₂
    exact ⟨_, evalScalarBinOp_shr_unsigned_eq_ushr hsz hy hxb yb locals mem,
      scalarRange_of_bitVec _ hs.1 hs.2⟩

/-- Unsigned interval transfer through `evalBinOp .sub` without underflow
(`Anneal.BitVec.range_sub_no_underflow_sound`). -/
theorem scalarRange_evalBinOp_sub_no_underflow {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt} (isSigned : Bool)
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y) (hno : b_hi ≤ a_lo) :
    ∃ r, Anneal.Scalars.evalBinOp .sub x y isSigned = some r ∧
      ScalarRange sz (a_lo - b_hi) (a_hi - b_lo) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarRange_exists hy
  have hs := Anneal.BitVec.range_sub_no_underflow_sound hx₁ hx₂ hy₁ hy₂ hno
  exact ⟨_, evalBinOp_sub_eq_sub hsz xb yb isSigned, scalarRange_of_bitVec _ hs.1 hs.2⟩

/-- Unsigned interval transfer through `evalWrappingSub` without underflow. -/
theorem scalarRange_evalWrappingSub_no_underflow {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y) (hno : b_hi ≤ a_lo) :
    ∃ r, evalWrappingSub x y = some r ∧
      ScalarRange sz (a_lo - b_hi) (a_hi - b_lo) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarRange_exists hy
  have hs := Anneal.BitVec.range_sub_no_underflow_sound hx₁ hx₂ hy₁ hy₂ hno
  exact ⟨_, evalWrappingSub_eq_sub hsz xb yb, scalarRange_of_bitVec _ hs.1 hs.2⟩

/-- Unsigned interval transfer through `evalBinOp .mul` without overflow
(`Anneal.BitVec.range_mul_no_overflow_sound`). -/
theorem scalarRange_evalBinOp_mul_no_overflow {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt} (isSigned : Bool)
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y)
    (hno : a_hi.toNat * b_hi.toNat < 2 ^ (8 * sz)) :
    ∃ r, Anneal.Scalars.evalBinOp .mul x y isSigned = some r ∧
      ScalarRange sz (Anneal.BitVec.mul a_lo b_lo) (Anneal.BitVec.mul a_hi b_hi) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarRange_exists hy
  have hs := Anneal.BitVec.range_mul_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno
  exact ⟨_, evalBinOp_mul_eq_mul hsz xb yb isSigned, scalarRange_of_bitVec _ hs.1 hs.2⟩

/-- Unsigned interval transfer through `evalWrappingMul` without overflow. -/
theorem scalarRange_evalWrappingMul_no_overflow {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y)
    (hno : a_hi.toNat * b_hi.toNat < 2 ^ (8 * sz)) :
    ∃ r, evalWrappingMul x y = some r ∧
      ScalarRange sz (Anneal.BitVec.mul a_lo b_lo) (Anneal.BitVec.mul a_hi b_hi) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarRange_exists hy
  have hs := Anneal.BitVec.range_mul_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno
  exact ⟨_, evalWrappingMul_eq_mul hsz xb yb, scalarRange_of_bitVec _ hs.1 hs.2⟩

/-- Unsigned interval transfer through unsigned `evalBinOp .div` with positive lower bound on the
divisor (`Anneal.BitVec.range_udiv_sound`). -/
theorem scalarRange_evalBinOp_div_unsigned {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y) (hb : 0 < b_lo.toNat) :
    ∃ r, Anneal.Scalars.evalBinOp .div x y false = some r ∧
      ScalarRange sz (Anneal.BitVec.udiv a_lo b_hi) (Anneal.BitVec.udiv a_hi b_lo) r := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, hy₂⟩ := scalarRange_exists hy
  have hypos : 0 < yb := by
    have hle : b_lo.toNat ≤ (BitVec.ofNat (8 * sz) yb).toNat := hy₁
    rw [toNat_ofNat_of_lt hyb] at hle
    exact Nat.lt_of_lt_of_le hb hle
  have hs := Anneal.BitVec.range_udiv_sound hx₁ hx₂ hy₁ hy₂ hb
  exact ⟨_, evalBinOp_div_unsigned_eq_udiv hsz hxb hyb (Nat.ne_of_gt hypos),
    scalarRange_of_bitVec _ hs.1 hs.2⟩

/-- Unsigned interval upper bound through unsigned `evalBinOp .rem`
(`Anneal.BitVecArith.range_urem_sound`). -/
theorem scalarRange_evalBinOp_rem_unsigned {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y) (hb : 0 < b_lo.toNat) :
    ∃ r, Anneal.Scalars.evalBinOp .rem x y false = some r ∧
      r.bits ≤ a_hi.toNat ∧ r.bits < b_hi.toNat := by
  obtain ⟨xb, rfl, hxb, _, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, hy₂⟩ := scalarRange_exists hy
  have hypos : 0 < (BitVec.ofNat (8 * sz) yb).toNat := by
    have hle : b_lo.toNat ≤ (BitVec.ofNat (8 * sz) yb).toNat := hy₁
    exact Nat.lt_of_lt_of_le hb hle
  have hyne : yb ≠ 0 := by
    rw [toNat_ofNat_of_lt hyb] at hypos
    exact Nat.ne_of_gt hypos
  have hs := Anneal.BitVecArith.range_urem_sound hypos hx₂ hy₂
  exact ⟨_, evalBinOp_rem_unsigned_eq_urem hsz hxb hyb hyne, hs.1, hs.2⟩

/-- Unsigned interval transfer through `evalBinOp .shl` without overflow
(`Anneal.BitVecArith.range_shl_no_overflow_sound`). -/
theorem scalarRange_evalBinOp_shl_no_overflow {sz : Nat} (hsz : 0 < sz)
    {umin umax : BitVec (8 * sz)} {x : ScalarInt} (y : ScalarInt) (hy : 0 < y.sizeBytes)
    {kmin kmax : Nat} (isSigned : Bool) (hx : ScalarRange sz umin umax x)
    (hk₁ : kmin ≤ y.bits % (8 * sz)) (hk₂ : y.bits % (8 * sz) ≤ kmax)
    (hno : umax.toNat * 2 ^ kmax < 2 ^ (8 * sz)) :
    ∃ r, Anneal.Scalars.evalBinOp .shl x y isSigned = some r ∧
      ScalarRange sz (Anneal.BitVec.shl umin kmin) (Anneal.BitVec.shl umax kmax) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarRange_exists hx
  cases y with
  | mk yb ys =>
    have hs := Anneal.BitVecArith.range_shl_no_overflow_sound hx₁ hx₂ hk₁ hk₂ hno
    exact ⟨_, evalBinOp_shl_eq_shl hsz hy xb yb isSigned, scalarRange_of_bitVec _ hs.1 hs.2⟩

/-- Signed interval transfer through `evalWrappingAdd` when neither signed underflow nor signed
overflow can occur. -/
theorem scalarSRange_evalWrappingAdd_no_overflow {sz : Nat} (hsz : 0 < sz)
    {smin₁ smax₁ smin₂ smax₂ : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarSRange sz smin₁ smax₁ x) (hy : ScalarSRange sz smin₂ smax₂ y)
    (hno_udf : 2 ^ (8 * sz - 1) ≤
      Anneal.BitVecArith.signedKey smin₁ + Anneal.BitVecArith.signedKey smin₂)
    (hno_ovf : Anneal.BitVecArith.signedKey smax₁ + Anneal.BitVecArith.signedKey smax₂ <
      2 ^ (8 * sz - 1) + 2 ^ (8 * sz)) :
    ∃ r, evalWrappingAdd x y = some r ∧
      ScalarSRange sz (smin₁ + smin₂) (smax₁ + smax₂) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarSRange_exists hy
  have hs := Anneal.BitVecArith.signed_range_add_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno_udf hno_ovf
  exact ⟨_, evalWrappingAdd_eq_add hsz xb yb, scalarSRange_of_bitVec _ hs.1 hs.2⟩

/-- Operational signed interval transfer through `Trusted` `evalScalarBinOp .add`. -/
theorem scalarSRange_evalScalarBinOp_add_no_overflow {sz : Nat} (hsz : 0 < sz)
    {smin₁ smax₁ smin₂ smax₂ : BitVec (8 * sz)} {x y : ScalarInt}
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool)
    (hx : ScalarSRange sz smin₁ smax₁ x) (hy : ScalarSRange sz smin₂ smax₂ y)
    (hno_udf : 2 ^ (8 * sz - 1) ≤
      Anneal.BitVecArith.signedKey smin₁ + Anneal.BitVecArith.signedKey smin₂)
    (hno_ovf : Anneal.BitVecArith.signedKey smax₁ + Anneal.BitVecArith.signedKey smax₂ <
      2 ^ (8 * sz - 1) + 2 ^ (8 * sz)) :
    ∃ r, evalScalarBinOp .add x y locals mem isSigned = .ok (.scalar r) locals mem ∧
      ScalarSRange sz (smin₁ + smin₂) (smax₁ + smax₂) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarSRange_exists hy
  have hs := Anneal.BitVecArith.signed_range_add_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno_udf hno_ovf
  exact ⟨_, evalScalarBinOp_add_eq_add hsz xb yb locals mem isSigned,
    scalarSRange_of_bitVec _ hs.1 hs.2⟩

/-- Signed branch refinement on a taken signed `evalBinOp .gt x c` test
(`Anneal.BitVecArith.signed_range_refine_sgt`). -/
theorem scalarSRange_refine_evalBinOp_gt {sz : Nat} (hsz : 0 < sz) {lo hi : BitVec (8 * sz)}
    {x : ScalarInt} (c : Nat) (hx : ScalarSRange sz lo hi x)
    (hgt : Anneal.Scalars.evalBinOp .gt x ⟨c, sz⟩ true = some (boolToScalar true)) :
    ScalarSRange sz
      (Anneal.BitVecArith.sbvMax lo (BitVec.ofNat (8 * sz) c + BitVec.ofNat (8 * sz) 1)) hi x := by
  obtain ⟨xb, rfl, _, _, _⟩ := scalarSRange_exists hx
  rw [Anneal.Scalars.evalBinOp_gt_signed hsz, ← Anneal.Scalars.signedLt_eq_slt] at hgt
  have hlt := (signedLt_eq_true_iff c xb sz).1 ((boolToScalar_eq_true_iff _).1 (Option.some.inj hgt))
  have hs := Anneal.BitVecArith.signed_range_refine_sgt hx.2.2.1 hx.2.2.2 hlt
  exact ⟨hx.1, hx.2.1, hs.1, hs.2⟩

/-- Signed branch refinement on a taken signed `evalBinOp .ge x c` test
(`Anneal.BitVecArith.signed_range_refine_sge`). -/
theorem scalarSRange_refine_evalBinOp_ge {sz : Nat} (hsz : 0 < sz) {lo hi : BitVec (8 * sz)}
    {x : ScalarInt} (c : Nat) (hx : ScalarSRange sz lo hi x)
    (hge : Anneal.Scalars.evalBinOp .ge x ⟨c, sz⟩ true = some (boolToScalar true)) :
    ScalarSRange sz (Anneal.BitVecArith.sbvMax lo (BitVec.ofNat (8 * sz) c)) hi x := by
  obtain ⟨xb, rfl, _, _, _⟩ := scalarSRange_exists hx
  rw [Anneal.Scalars.evalBinOp_ge_signed hsz, ← Anneal.Scalars.signedLe_eq_sle] at hge
  have hle := (signedLe_eq_true_iff c xb sz).1 ((boolToScalar_eq_true_iff _).1 (Option.some.inj hge))
  have hs := Anneal.BitVecArith.signed_range_refine_sge hx.2.2.1 hx.2.2.2 hle
  exact ⟨hx.1, hx.2.1, hs.1, hs.2⟩

/-- Operational signed branch refinement on `Trusted` `evalScalarBinOp .lt`. -/
theorem scalarSRange_refine_evalScalarBinOp_lt {sz : Nat} (hsz : 0 < sz) {lo hi : BitVec (8 * sz)}
    {x : ScalarInt} (c : Nat) (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarSRange sz lo hi x)
    (hlt : evalScalarBinOp .lt x ⟨c, sz⟩ locals mem true =
      .ok (.scalar (boolToScalar true)) locals mem) :
    ScalarSRange sz lo
      (Anneal.BitVecArith.sbvMin hi (BitVec.ofNat (8 * sz) c - BitVec.ofNat (8 * sz) 1)) x := by
  obtain ⟨xb, rfl, _, _, _⟩ := scalarSRange_exists hx
  rw [Anneal.Scalars.evalScalarBinOp_lt_signed hsz, ← Anneal.Scalars.signedLt_eq_slt] at hlt
  have hsc : boolToScalar (signedLt xb c sz) = boolToScalar true :=
    Value.scalar.inj (RvalueEvalResult.ok.inj hlt).1
  exact scalarSRange_refine_signedLt hx c ((boolToScalar_eq_true_iff _).1 hsc)

/-- Operational signed branch refinement on `Trusted` `evalScalarBinOp .le`. -/
theorem scalarSRange_refine_evalScalarBinOp_le {sz : Nat} (hsz : 0 < sz) {lo hi : BitVec (8 * sz)}
    {x : ScalarInt} (c : Nat) (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarSRange sz lo hi x)
    (hle : evalScalarBinOp .le x ⟨c, sz⟩ locals mem true =
      .ok (.scalar (boolToScalar true)) locals mem) :
    ScalarSRange sz lo (Anneal.BitVecArith.sbvMin hi (BitVec.ofNat (8 * sz) c)) x := by
  obtain ⟨xb, rfl, _, _, _⟩ := scalarSRange_exists hx
  rw [Anneal.Scalars.evalScalarBinOp_le_signed hsz, ← Anneal.Scalars.signedLe_eq_sle] at hle
  have hsc : boolToScalar (signedLe xb c sz) = boolToScalar true :=
    Value.scalar.inj (RvalueEvalResult.ok.inj hle).1
  exact scalarSRange_refine_signedLe hx c ((boolToScalar_eq_true_iff _).1 hsc)

/-- Operational signed branch refinement on `Trusted` `evalScalarBinOp .gt`. -/
theorem scalarSRange_refine_evalScalarBinOp_gt {sz : Nat} (hsz : 0 < sz) {lo hi : BitVec (8 * sz)}
    {x : ScalarInt} (c : Nat) (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarSRange sz lo hi x)
    (hgt : evalScalarBinOp .gt x ⟨c, sz⟩ locals mem true =
      .ok (.scalar (boolToScalar true)) locals mem) :
    ScalarSRange sz
      (Anneal.BitVecArith.sbvMax lo (BitVec.ofNat (8 * sz) c + BitVec.ofNat (8 * sz) 1)) hi x := by
  obtain ⟨xb, rfl, _, _, _⟩ := scalarSRange_exists hx
  rw [Anneal.Scalars.evalScalarBinOp_gt_signed hsz, ← Anneal.Scalars.signedLt_eq_slt] at hgt
  have hsc : boolToScalar (signedLt c xb sz) = boolToScalar true :=
    Value.scalar.inj (RvalueEvalResult.ok.inj hgt).1
  have hs := Anneal.BitVecArith.signed_range_refine_sgt hx.2.2.1 hx.2.2.2
    ((signedLt_eq_true_iff c xb sz).1 ((boolToScalar_eq_true_iff _).1 hsc))
  exact ⟨hx.1, hx.2.1, hs.1, hs.2⟩

/-- Operational signed branch refinement on `Trusted` `evalScalarBinOp .ge`. -/
theorem scalarSRange_refine_evalScalarBinOp_ge {sz : Nat} (hsz : 0 < sz) {lo hi : BitVec (8 * sz)}
    {x : ScalarInt} (c : Nat) (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarSRange sz lo hi x)
    (hge : evalScalarBinOp .ge x ⟨c, sz⟩ locals mem true =
      .ok (.scalar (boolToScalar true)) locals mem) :
    ScalarSRange sz (Anneal.BitVecArith.sbvMax lo (BitVec.ofNat (8 * sz) c)) hi x := by
  obtain ⟨xb, rfl, _, _, _⟩ := scalarSRange_exists hx
  rw [Anneal.Scalars.evalScalarBinOp_ge_signed hsz, ← Anneal.Scalars.signedLe_eq_sle] at hge
  have hsc : boolToScalar (signedLe c xb sz) = boolToScalar true :=
    Value.scalar.inj (RvalueEvalResult.ok.inj hge).1
  have hs := Anneal.BitVecArith.signed_range_refine_sge hx.2.2.1 hx.2.2.2
    ((signedLe_eq_true_iff c xb sz).1 ((boolToScalar_eq_true_iff _).1 hsc))
  exact ⟨hx.1, hx.2.1, hs.1, hs.2⟩

/-- Unsigned branch refinement on a taken unsigned `evalBinOp .lt x c` test
(`Anneal.BitVecArith.range_refine_ult`). -/
theorem scalarRange_refine_evalBinOp_lt {sz : Nat} (hsz : 0 < sz) {lo hi : BitVec (8 * sz)}
    {x : ScalarInt} {c : Nat} (hc : c < scalarModulus sz) (hx : ScalarRange sz lo hi x)
    (hlt : Anneal.Scalars.evalBinOp .lt x ⟨c, sz⟩ false = some (boolToScalar true)) :
    ScalarRange sz lo
      (Anneal.BitVecArith.bvMin hi (BitVec.ofNat (8 * sz) c - BitVec.ofNat (8 * sz) 1)) x := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  rw [Anneal.Scalars.evalBinOp_lt_unsigned hsz] at hlt
  have hlt' : xb < c := of_decide_eq_true ((boolToScalar_eq_true_iff _).1 (Option.some.inj hlt))
  have hbv : BitVec.ofNat (8 * sz) xb < BitVec.ofNat (8 * sz) c := by
    show (BitVec.ofNat (8 * sz) xb).toNat < (BitVec.ofNat (8 * sz) c).toNat
    rw [toNat_ofNat_of_lt hxb, toNat_ofNat_of_lt hc]
    exact hlt'
  have hs := Anneal.BitVecArith.range_refine_ult hx₁ hx₂ hbv
  exact ⟨rfl, hxb, hs.1, hs.2⟩

/-- Unsigned branch refinement on a taken unsigned `evalBinOp .le x c` test
(`Anneal.BitVecArith.range_refine_ule`). -/
theorem scalarRange_refine_evalBinOp_le {sz : Nat} (hsz : 0 < sz) {lo hi : BitVec (8 * sz)}
    {x : ScalarInt} {c : Nat} (hc : c < scalarModulus sz) (hx : ScalarRange sz lo hi x)
    (hle : Anneal.Scalars.evalBinOp .le x ⟨c, sz⟩ false = some (boolToScalar true)) :
    ScalarRange sz lo (Anneal.BitVecArith.bvMin hi (BitVec.ofNat (8 * sz) c)) x := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  rw [Anneal.Scalars.evalBinOp_le_unsigned hsz] at hle
  have hle' : xb ≤ c := of_decide_eq_true ((boolToScalar_eq_true_iff _).1 (Option.some.inj hle))
  have hbv : BitVec.ofNat (8 * sz) xb ≤ BitVec.ofNat (8 * sz) c := by
    show (BitVec.ofNat (8 * sz) xb).toNat ≤ (BitVec.ofNat (8 * sz) c).toNat
    rw [toNat_ofNat_of_lt hxb, toNat_ofNat_of_lt hc]
    exact hle'
  have hs := Anneal.BitVecArith.range_refine_ule hx₁ hx₂ hbv
  exact ⟨rfl, hxb, hs.1, hs.2⟩

/-- Unsigned branch refinement on a taken unsigned `evalBinOp .gt x c` test
(`Anneal.BitVecArith.range_refine_ugt`). -/
theorem scalarRange_refine_evalBinOp_gt {sz : Nat} (hsz : 0 < sz) {lo hi : BitVec (8 * sz)}
    {x : ScalarInt} {c : Nat} (hc : c < scalarModulus sz) (hx : ScalarRange sz lo hi x)
    (hgt : Anneal.Scalars.evalBinOp .gt x ⟨c, sz⟩ false = some (boolToScalar true)) :
    ScalarRange sz
      (Anneal.BitVecArith.bvMax lo (BitVec.ofNat (8 * sz) c + BitVec.ofNat (8 * sz) 1)) hi x := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  rw [Anneal.Scalars.evalBinOp_gt_unsigned hsz] at hgt
  have hgt' : c < xb := of_decide_eq_true ((boolToScalar_eq_true_iff _).1 (Option.some.inj hgt))
  have hbv : BitVec.ofNat (8 * sz) c < BitVec.ofNat (8 * sz) xb := by
    show (BitVec.ofNat (8 * sz) c).toNat < (BitVec.ofNat (8 * sz) xb).toNat
    rw [toNat_ofNat_of_lt hxb, toNat_ofNat_of_lt hc]
    exact hgt'
  have hs := Anneal.BitVecArith.range_refine_ugt hx₁ hx₂ hbv
  exact ⟨rfl, hxb, hs.1, hs.2⟩

/-- Unsigned branch refinement on a taken unsigned `evalBinOp .ge x c` test
(`Anneal.BitVecArith.range_refine_uge`). -/
theorem scalarRange_refine_evalBinOp_ge {sz : Nat} (hsz : 0 < sz) {lo hi : BitVec (8 * sz)}
    {x : ScalarInt} {c : Nat} (hc : c < scalarModulus sz) (hx : ScalarRange sz lo hi x)
    (hge : Anneal.Scalars.evalBinOp .ge x ⟨c, sz⟩ false = some (boolToScalar true)) :
    ScalarRange sz (Anneal.BitVecArith.bvMax lo (BitVec.ofNat (8 * sz) c)) hi x := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  rw [Anneal.Scalars.evalBinOp_ge_unsigned hsz] at hge
  have hge' : c ≤ xb := of_decide_eq_true ((boolToScalar_eq_true_iff _).1 (Option.some.inj hge))
  have hbv : BitVec.ofNat (8 * sz) c ≤ BitVec.ofNat (8 * sz) xb := by
    show (BitVec.ofNat (8 * sz) c).toNat ≤ (BitVec.ofNat (8 * sz) xb).toNat
    rw [toNat_ofNat_of_lt hxb, toNat_ofNat_of_lt hc]
    exact hge'
  have hs := Anneal.BitVecArith.range_refine_uge hx₁ hx₂ hbv
  exact ⟨rfl, hxb, hs.1, hs.2⟩

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

/-- Leading-zero count is antitone in the unsigned bitvector order: `a ≤ b → clz b ≤ clz a`,
at every bit width `w` (including `w = 0`). -/
theorem clz_antitone {w : Nat} {a b : BitVec w} (h : a ≤ b) :
    Anneal.BitVec.clz b ≤ Anneal.BitVec.clz a := by
  by_cases hb : b = BitVec.ofNat w 0
  · subst hb
    have ha0 : a.toNat = 0 := Nat.eq_zero_of_le_zero h
    have ha : a = BitVec.ofNat w 0 :=
      Anneal.BitVec.eq_of_toNat_eq (ha0.trans (Anneal.BitVec.toNat_zero w).symm)
    subst ha
    exact Nat.le_refl _
  · by_cases hle : Anneal.BitVec.clz b ≤ Anneal.BitVec.clz a
    · exact hle
    · exfalso
      have hlt : Anneal.BitVec.clz a < Anneal.BitVec.clz b := Nat.lt_of_not_ge hle
      have hcb : Anneal.BitVec.clz b ≤ w := Anneal.BitVec.clz_le b
      have ha_ne : a ≠ BitVec.ofNat w 0 := by
        intro ha0
        have hca := (Anneal.BitVec.clz_eq_width_iff a).2 ha0
        omega
      have hbit : a.toNat.testBit (w - Anneal.BitVec.clz a - 1) = true :=
        Anneal.BitVec.getLsbD_sub_clz_sub_one ha_ne
      have ha_ge : 2 ^ (w - Anneal.BitVec.clz a - 1) ≤ a.toNat :=
        Nat.ge_two_pow_of_testBit hbit
      have hb_lt : b.toNat < 2 ^ (w - Anneal.BitVec.clz b) :=
        Anneal.BitVec.toNat_lt_two_pow_sub_clz b
      have hpow : 2 ^ (w - Anneal.BitVec.clz b) ≤ 2 ^ (w - Anneal.BitVec.clz a - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hab : a.toNat ≤ b.toNat := h
      omega

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

/-- Little-endian serialization of `bswapBytes n x` is big-endian serialization of `x`
(equivalently, reversing the little-endian bytes of `x`), for every `n` including `n = 0`. -/
theorem toLeBytes_bswapBytes (n : Nat) (x : BitVec (8 * n)) :
    Anneal.LeBytes.toLeBytes n (toLeWidth (Anneal.BitVecArith.bswapBytes n x)) =
      Anneal.LeBytes.toBeBytes n (toLeWidth x) := by
  unfold Anneal.LeBytes.toLeBytes Anneal.LeBytes.toBeBytes
  rw [toNat_toLeWidth, toNat_bswapBytes_eq_fromBeBytes]
  unfold Anneal.LeBytes.fromBeBytes
  have hlen : (Anneal.LeBytes.toLeBytesAux n x.toNat).reverse.length = n := by
    rw [List.length_reverse, Anneal.LeBytes.toLeBytesAux_length]
  have h := Anneal.LeBytes.toLeBytesAux_fromLeBytes (Anneal.LeBytes.toLeBytesAux n x.toNat).reverse
  rw [hlen] at h
  exact h

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

/-- Payload extraction distributes over list concatenation (even when `.uninit` bytes are present). -/
theorem extractInitBvBytes_append :
    ∀ xs ys : List AbstractByte,
      extractInitBvBytes (xs ++ ys) = extractInitBvBytes xs ++ extractInitBvBytes ys
  | [], _ => rfl
  | .uninit :: rest, ys => extractInitBvBytes_append rest ys
  | .init b _ :: rest, ys => congrArg (b.toBitVec :: ·) (extractInitBvBytes_append rest ys)

/-- On a fully initialized byte list, `extractInitBvBytes` commutes with `List.take`. -/
theorem extractInitBvBytes_take :
    ∀ (n : Nat) (bs : List AbstractByte),
      allBytesInitialized bs = true →
        extractInitBvBytes (bs.take n) = (extractInitBvBytes bs).take n
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, .uninit :: _, h => nomatch h
  | k + 1, .init b _ :: rest, h => congrArg (b.toBitVec :: ·) (extractInitBvBytes_take k rest h)

/-- On a fully initialized byte list, `extractInitBvBytes` commutes with `List.drop`. -/
theorem extractInitBvBytes_drop :
    ∀ (n : Nat) (bs : List AbstractByte),
      allBytesInitialized bs = true →
        extractInitBvBytes (bs.drop n) = (extractInitBvBytes bs).drop n
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, .uninit :: _, h => nomatch h
  | k + 1, .init _ _ :: rest, h => extractInitBvBytes_drop k rest h

/-- On a fully initialized byte list, `extractInitBvBytes` commutes with `chunksOf n` for every
`n` (including `n = 0`). -/
theorem chunksOf_extractInitBvBytes (n : Nat) (bs : List AbstractByte)
    (hinit : allBytesInitialized bs = true) :
    (Anneal.ListChunks.chunksOf n bs).map extractInitBvBytes =
      Anneal.ListChunks.chunksOf n (extractInitBvBytes bs) := by
  cases Nat.eq_zero_or_pos n with
  | inl hn =>
    subst hn
    rw [Anneal.ListChunks.chunksOf_zero_size, Anneal.ListChunks.chunksOf_zero_size]
    rfl
  | inr hn =>
    suffices haux : ∀ (fuel : Nat) (xs : List AbstractByte),
        allBytesInitialized xs = true → xs.length ≤ fuel →
          (Anneal.ListChunks.chunksOfAux n fuel xs).map extractInitBvBytes =
            Anneal.ListChunks.chunksOfAux n fuel (extractInitBvBytes xs) by
      have hlen : (extractInitBvBytes bs).length = bs.length :=
        (length_extractInitBvBytes_eq_iff bs).2 hinit
      unfold Anneal.ListChunks.chunksOf
      simp only [Nat.ne_of_gt hn, ↓reduceIte]
      rw [hlen]
      exact haux bs.length bs hinit (Nat.le_refl _)
    intro fuel
    induction fuel with
    | zero =>
      intro xs _ _
      rfl
    | succ f ih =>
      intro xs hxi hle
      cases xs with
      | nil => rfl
      | cons b rest =>
        cases b with
        | uninit => nomatch hxi
        | init byte prov =>
          show extractInitBvBytes ((AbstractByte.init byte prov :: rest).take n) ::
              (Anneal.ListChunks.chunksOfAux n f
                ((AbstractByte.init byte prov :: rest).drop n)).map extractInitBvBytes =
            (extractInitBvBytes (AbstractByte.init byte prov :: rest)).take n ::
              Anneal.ListChunks.chunksOfAux n f
                ((extractInitBvBytes (AbstractByte.init byte prov :: rest)).drop n)
          rw [extractInitBvBytes_take n _ hxi, ← extractInitBvBytes_drop n _ hxi]
          have hdrop_init : allBytesInitialized ((AbstractByte.init byte prov :: rest).drop n) = true :=
            allBytesInitialized_drop n hxi
          have hdrop_le : ((AbstractByte.init byte prov :: rest).drop n).length ≤ f := by
            rw [List.length_drop, List.length_cons]
            rw [List.length_cons] at hle
            omega
          rw [ih _ hdrop_init hdrop_le]

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

/-- Round trip of `encodeLittleEndianBytes` followed by `decodeLittleEndianBytes` at every byte
count `n` (including `n = 0`, where provenance collapses to `none`). -/
theorem decodeLittleEndianBytes_encodeLittleEndianBytes (n v : Nat)
    (prov : Option (Nat × Nat)) :
    decodeLittleEndianBytes (encodeLittleEndianBytes v n prov) =
      some (v % 2 ^ (n * 8), match n with | 0 => none | _ + 1 => prov) := by
  rw [encodeLittleEndianBytes_eq_map, decodeLittleEndianBytes_map,
    Anneal.LeBytes.fromLeBytes_toLeBytesAux]
  cases n <;> rfl

/-- `encodeScalarBytes` rejects exactly zero-width scalars. -/
theorem encodeScalarBytes_eq_none_iff (sv : ScalarVal) (prov : Option (Nat × Nat)) :
    encodeScalarBytes sv prov = none ↔ sv.sizeBytes = 0 := by
  unfold encodeScalarBytes
  cases h0 : Nat.beq sv.sizeBytes 0 with
  | true => exact ⟨fun _ => Nat.eq_of_beq_eq_true h0, fun _ => rfl⟩
  | false =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h
    · rw [h] at h0; cases h0

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

/-- On any non-empty fully initialized byte list (arbitrary, possibly mixed provenance),
`decodeScalarBytes` returns `fromLeBytes` of the extracted payload at the list's length. -/
theorem decodeScalarBytes_of_init {bs : List AbstractByte} (hne : bs ≠ [])
    (hinit : allBytesInitialized bs = true) (signed : Bool) :
    ∃ prov, decodeScalarBytes bs signed =
      some (⟨Anneal.LeBytes.fromLeBytes (extractInitBvBytes bs), bs.length⟩, prov) := by
  obtain ⟨prov, hp⟩ := decodeLittleEndianBytes_of_init bs hinit
  have hpos : 0 < bs.length := List.length_pos_iff.2 hne
  refine ⟨prov, ?_⟩
  unfold decodeScalarBytes
  dsimp only
  rw [seqLength_eq, beq_zero_of_pos hpos, hp]

/-- `decodeScalarBytes` fails exactly when the byte list is empty or contains an `.uninit` byte. -/
theorem decodeScalarBytes_eq_none_iff (bs : List AbstractByte) (signed : Bool) :
    decodeScalarBytes bs signed = none ↔ bs = [] ∨ allBytesInitialized bs = false := by
  cases bs with
  | nil => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | cons b rest =>
    constructor
    · intro h
      cases hi : allBytesInitialized (b :: rest) with
      | false => exact Or.inr rfl
      | true =>
        obtain ⟨p, hp⟩ := decodeScalarBytes_of_init (by simp) hi signed
        rw [hp] at h
        cases h
    · rintro (he | hu)
      · cases he
      · exact decodeScalarBytes_eq_none_of_uninit hu signed

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

/-- `bitVecLE.encode` on a byte-swapped value is the reversed encoding of the original value. -/
theorem bitVecLE_encode_bswapBytes (sz : Nat) (hNz : 0 < sz) (x : BitVec (8 * sz)) :
    (bitVecLE sz hNz).encode (Anneal.BitVecArith.bswapBytes sz x) =
      ((bitVecLE sz hNz).encode x).reverse := by
  rw [bitVecLE_encode_eq_toLeBytes, bitVecLE_encode_eq_toLeBytes, toLeBytes_bswapBytes,
    Anneal.LeBytes.toBeBytes, List.map_reverse]

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

/-- `decodeArrayChunksWith` rejects every buffer one of whose `chunksOf n` chunks fails to decode
(symmetric to `decodeChunks_eq_none_of_chunk`). -/
theorem decodeArrayChunksWith_eq_none_of_chunk (decVal : List AbstractByte → Option Value)
    {n : Nat} (hn : 0 < n) (k : Nat) {bs ch : List AbstractByte}
    (hmem : ch ∈ Anneal.ListChunks.chunksOf n bs) (hch : decVal ch = none) :
    decodeArrayChunksWith decVal n k bs = none := by
  rw [decodeArrayChunksWith_eq_chunksOf decVal hn]
  have hnone : sequenceOptions ((Anneal.ListChunks.chunksOf n bs).map decVal) = none :=
    sequenceOptions_eq_none_of_mem _ (hch ▸ List.mem_map_of_mem hmem)
  rw [hnone]
  cases Nat.decEq bs.length (k * n) with
  | isTrue he => simp only [he, ↓reduceIte]
  | isFalse hne => simp only [hne, ↓reduceIte]

/-- Zero-width chunk decoding (`n = 0`) on `[]`: when `decVal [] = some v`, `decodeArrayChunksWith`
produces `k` copies of `v`, whereas `chunksOf 0 [] = []` has length `0` (so `0 < n` in
`decodeArrayChunksWith_eq_chunksOf` is genuinely necessary). -/
theorem decodeArrayChunksWith_zero_width (decVal : List AbstractByte → Option Value)
    {v : Value} (hv : decVal [] = some v) :
    ∀ k : Nat, decodeArrayChunksWith decVal 0 k [] = some (List.replicate k v)
  | 0 => rfl
  | k + 1 => by
    unfold decodeArrayChunksWith
    dsimp only
    rw [seqLength_eq, takeAbstractBytes_eq_take, dropAbstractBytes_eq_drop]
    simp only [List.length_nil, Nat.ble_self_eq_true, List.take_nil, List.drop_nil, hv,
      decodeArrayChunksWith_zero_width decVal hv k, List.replicate_succ]

/-- Zero-width `decodeChunks` (`n = 0`) on `[]`: produces `k` copies of `x` whenever
`c.decode [] = some x`, demonstrating why `0 < n` is necessary in `decodeChunks_eq_chunksOf`. -/
theorem decodeChunks_zero_width {α : Type} (c : FixedByteCodec α 0) {x : α}
    (hx : c.decode [] = some x) :
    ∀ k : Nat, (c.decodeChunks k []).map Subtype.val = some (List.replicate k x)
  | 0 => rfl
  | k + 1 => by
    have ih := decodeChunks_zero_width c hx k
    unfold FixedByteCodec.decodeChunks
    simp only [List.length_nil, Nat.ble_self_eq_true, List.take_nil, List.drop_nil, hx]
    cases hr : c.decodeChunks k [] with
    | none => rw [hr] at ih; cases ih
    | some tl =>
      rw [hr] at ih
      obtain ⟨xs, hxs⟩ := tl
      have hval : xs = List.replicate k x := Option.some.inj ih
      subst hval
      rfl

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

/-- Chunking distributes over any successful `Trusted` `encodeListWith` at positive element width
`n` (no `FixedByteCodec` required): splitting the encoded buffer into `n`-byte chunks recovers
every element's encoding in order. -/
theorem chunksOf_of_encodeListWith (encVal : Value → Option (List AbstractByte)) {n : Nat}
    (hn : 0 < n) : ∀ {vs : List Value} {bs : List AbstractByte},
    encodeListWith encVal n vs = some bs →
      (Anneal.ListChunks.chunksOf n bs).map some = vs.map encVal
  | [], bs, h => by
    have hbs : bs = [] := (Option.some.inj h).symm
    subst hbs
    rw [Anneal.ListChunks.chunksOf_nil]
    rfl
  | v :: rest, bs, h => by
    unfold encodeListWith at h
    cases he : encVal v with
    | none => rw [he] at h; cases h
    | some eBs =>
      rw [he] at h
      dsimp only at h
      cases hbeq : Nat.beq (Trusted.Sequence.length eBs) n with
      | false => rw [hbeq] at h; cases h
      | true =>
        rw [hbeq] at h
        dsimp only at h
        cases hr : encodeListWith encVal n rest with
        | none => rw [hr] at h; cases h
        | some restBs =>
          rw [hr] at h
          have hbs : eBs ++ restBs = bs := by
            rw [← appendAbstractBytes_eq_append]
            exact Option.some.inj h
          subst hbs
          have hlen : eBs.length = n := Nat.eq_of_beq_eq_true hbeq
          have hmod : eBs.length % n = 0 := by rw [hlen, Nat.mod_self]
          rw [Anneal.ListChunks.chunksOf_append_exact hn _ _ hmod, chunksOf_eq_singleton hn hlen,
            List.singleton_append, List.map_cons, List.map_cons, he,
            chunksOf_of_encodeListWith encVal hn hr]

/-- The MIR runtime value of an array of `sz`-byte unsigned integers given as bitvectors. -/
def bitVecArrayValue (sz : Nat) (xs : List (BitVec (8 * sz))) : Value :=
  .aggregate 0 (xs.map (fun x => Value.scalar ⟨x.toNat, sz⟩))

/-- Byte size of `[uN; n]` (including `n = 0`). -/
theorem rigidTyByteSize_array_uint (layouts : LayoutTable) (w : UintTy) (n : Nat)
    (idx : LayoutIdx) :
    rigidTyByteSize layouts { kind := .array (.uint w) n, layoutIdx := idx } =
      some (MirValueCodec.uintByteSize w * n) := by
  cases w <;> rfl

/-- `encodeValueToBytes` on any array of unsigned integers given as bitvectors (including the
empty array `xs = []`) is the element-wise `bitVecLE` encoding. -/
theorem encodeValueToBytes_bitVecArray (layouts : LayoutTable) (w : UintTy) (idx : LayoutIdx)
    (xs : List (BitVec (8 * MirValueCodec.uintByteSize w))) :
    encodeValueToBytes defaultCodecFuel layouts
        { kind := .array (.uint w) xs.length, layoutIdx := idx }
        (bitVecArrayValue (MirValueCodec.uintByteSize w) xs) =
      some ((bitVecLE (MirValueCodec.uintByteSize w)
        (MirValueCodec.uintByteSize_pos w)).encodeElems xs) := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    have hk : 0 < (y :: ys).length := Nat.succ_pos ys.length
    have h := (MirValueCodec.uintArray layouts w (y :: ys).length hk idx).encode_toValue
      ⟨(y :: ys).map (fun x => (⟨x.toNat, x.isLt⟩ :
        { bits : Nat // bits < 2 ^ (8 * MirValueCodec.uintByteSize w) })), List.length_map _⟩
    rw [encodeElems_bitVecLE_eq_uintBitsLE]
    have hv : bitVecArrayValue (MirValueCodec.uintByteSize w) (y :: ys) =
        (MirValueCodec.uintArray layouts w (y :: ys).length hk idx).toValue
          ⟨(y :: ys).map (fun x => (⟨x.toNat, x.isLt⟩ :
            { bits : Nat // bits < 2 ^ (8 * MirValueCodec.uintByteSize w) })), List.length_map _⟩ := by
      show Value.aggregate 0 _ = Value.aggregate 0 _
      rw [List.map_map]
      rfl
    rw [hv]
    exact h

/-- `decodeValueFromBytes` recovers any array of unsigned integers (including the empty array
`xs = []`) from its element-wise `bitVecLE` encoding. -/
theorem decodeValueFromBytes_encodeElems_bitVecLE (layouts : LayoutTable) (w : UintTy)
    (idx : LayoutIdx) (xs : List (BitVec (8 * MirValueCodec.uintByteSize w))) :
    decodeValueFromBytes defaultCodecFuel layouts
        { kind := .array (.uint w) xs.length, layoutIdx := idx }
        ((bitVecLE (MirValueCodec.uintByteSize w)
          (MirValueCodec.uintByteSize_pos w)).encodeElems xs) =
      some (bitVecArrayValue (MirValueCodec.uintByteSize w) xs) := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    have hk : 0 < (y :: ys).length := Nat.succ_pos ys.length
    rw [encodeElems_bitVecLE_eq_uintBitsLE,
      (MirValueCodec.uintArray layouts w (y :: ys).length hk idx).decode_eq_map]
    have hdec := (MirValueCodec.uintArray layouts w (y :: ys).length hk idx).codec.decode_encode
      ⟨(y :: ys).map (fun x => (⟨x.toNat, x.isLt⟩ :
        { bits : Nat // bits < 2 ^ (8 * MirValueCodec.uintByteSize w) })), List.length_map _⟩
    have henc : (MirValueCodec.uintArray layouts w (y :: ys).length hk idx).codec.encode
        ⟨(y :: ys).map (fun x => (⟨x.toNat, x.isLt⟩ :
          { bits : Nat // bits < 2 ^ (8 * MirValueCodec.uintByteSize w) })), List.length_map _⟩ =
        (FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w)
          (MirValueCodec.uintByteSize_pos w)).encodeElems
          ((y :: ys).map (fun x => (⟨x.toNat, x.isLt⟩ :
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

/-- Typed transmutation of bitvector arrays (including the empty array `xs = []`): the bytes of
any `[uA; n₁]` array given as bitvectors decode at `[uB; n₂]` whenever the byte sizes agree. -/
theorem bitVecArray_transmute_sound (layouts : LayoutTable) (w₁ w₂ : UintTy) (n₂ : Nat)
    (idx₁ idx₂ : LayoutIdx) (xs : List (BitVec (8 * MirValueCodec.uintByteSize w₁)))
    (hsize : MirValueCodec.uintByteSize w₁ * xs.length = MirValueCodec.uintByteSize w₂ * n₂) :
    ∃ v', decodeValueFromBytes defaultCodecFuel layouts
      { kind := .array (.uint w₂) n₂, layoutIdx := idx₂ }
      ((bitVecLE (MirValueCodec.uintByteSize w₁)
        (MirValueCodec.uintByteSize_pos w₁)).encodeElems xs) = some v' :=
  array_uint_transmute_sound layouts w₁ w₂ xs.length n₂ idx₁ idx₂ hsize _ _
    (encodeValueToBytes_bitVecArray layouts w₁ idx₁ xs)

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

/-- Unsigned `evalCastValue` on a canonical operand computes ported `Anneal.BitVec.setWidth`
(zero-extension when widening, low-bit truncation when narrowing). Canonicality is required when
widening because `evalCastValue` does not wrap the source before modding by the destination. -/
theorem evalCastValue_unsigned_eq_setWidth {srcSz dstSz : Nat} (hs : 0 < srcSz) (hd : 0 < dstSz)
    {bits : Nat} (hb : bits < scalarModulus srcSz) :
    Anneal.Scalars.evalCastValue ⟨bits, srcSz⟩ dstSz false =
      some ⟨(Anneal.BitVec.setWidth (8 * dstSz) (BitVec.ofNat (8 * srcSz) bits)).toNat, dstSz⟩ := by
  rw [Anneal.Scalars.evalCastValue_unsigned_apply hs hd, Anneal.BitVec.toNat_setWidth, natMod_eq,
    natPow_eq, toNat_ofNat_of_lt hb]

/-- Unconditional unsigned `evalCastValue` bridge using `wrapScalarBits` canonicalization. -/
theorem evalCastValue_unsigned_wrap_eq_setWidth {srcSz dstSz : Nat} (hs : 0 < srcSz)
    (hd : 0 < dstSz) (bits : Nat) :
    Anneal.Scalars.evalCastValue ⟨wrapScalarBits bits (scalarModulus srcSz), srcSz⟩ dstSz false =
      some ⟨(Anneal.BitVec.setWidth (8 * dstSz) (BitVec.ofNat (8 * srcSz) bits)).toNat, dstSz⟩ := by
  have hlt : wrapScalarBits bits (scalarModulus srcSz) < scalarModulus srcSz := by
    rw [wrapScalarBits_eq_toNat]
    exact toNat_lt_scalarModulus _
  rw [evalCastValue_unsigned_eq_setWidth hs hd hlt, wrapScalarBits_eq_toNat, ofNat_toNat_self]

/-- Tnum transfer through an unsigned integer cast (`Anneal.BitVecArith.tnum_setWidth_sound`). -/
theorem scalarTnum_evalCastValue_unsigned {srcSz dstSz : Nat} (hs : 0 < srcSz) (hd : 0 < dstSz)
    {m v : BitVec (8 * srcSz)} {x : ScalarInt} (hx : ScalarTnum srcSz m v x) :
    ∃ r, Anneal.Scalars.evalCastValue x dstSz false = some r ∧
      ScalarTnum dstSz (Anneal.BitVec.setWidth (8 * dstSz) m)
        (Anneal.BitVec.setWidth (8 * dstSz) v) r := by
  obtain ⟨xb, rfl, hxb, hxm⟩ := scalarTnum_exists hx
  exact ⟨_, evalCastValue_unsigned_eq_setWidth hs hd hxb,
    scalarTnum_of_bitVec _ (Anneal.BitVecArith.tnum_setWidth_sound (8 * dstSz) hxm)⟩

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

/-- General antitone interval transfer through `evalCtlz`: for *any* unsigned interval `[lo, hi]`
(even spanning multiple bit lengths) whose width fits in `retBytes`, `evalCtlz x retBytes`
lies in `[clz hi, clz lo]`. -/
theorem scalarRange_evalCtlz_range {sz retBytes : Nat} (hsz : 0 < sz) (hret : 0 < retBytes)
    (hfit : 8 * sz < scalarModulus retBytes)
    {lo hi : BitVec (8 * sz)} {x : ScalarInt} (hx : ScalarRange sz lo hi x) :
    ∃ r, evalCtlz x retBytes = some r ∧
      ScalarRange retBytes (BitVec.ofNat (8 * retBytes) (Anneal.BitVec.clz hi))
        (BitVec.ofNat (8 * retBytes) (Anneal.BitVec.clz lo)) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarRange_exists hx
  have hlo_lt : Anneal.BitVec.clz hi < scalarModulus retBytes :=
    Nat.lt_of_le_of_lt (Anneal.BitVec.clz_le hi) hfit
  have hhi_lt : Anneal.BitVec.clz lo < scalarModulus retBytes :=
    Nat.lt_of_le_of_lt (Anneal.BitVec.clz_le lo) hfit
  have hcur_lt : Anneal.BitVec.clz (BitVec.ofNat (8 * sz) xb) < scalarModulus retBytes :=
    Nat.lt_of_le_of_lt (Anneal.BitVec.clz_le _) hfit
  refine ⟨_, evalCtlz_eq_clz hsz hret xb, scalarRange_iff_bits.2 ⟨hcur_lt, ?_, ?_⟩⟩
  · rw [toNat_ofNat_of_lt hlo_lt]; exact clz_antitone hx₂
  · rw [toNat_ofNat_of_lt hhi_lt]; exact clz_antitone hx₁

/-- Non-zero interval transfer through `evalCtlzNonzero`: whenever `0 < lo.toNat`, `evalCtlzNonzero`
never hits UB and its result lies in `[clz hi, clz lo]` (strictly below `8 * sz`). -/
theorem scalarRange_evalCtlzNonzero_range {sz retBytes : Nat} (hsz : 0 < sz) (hret : 0 < retBytes)
    (hfit : 8 * sz < scalarModulus retBytes)
    {lo hi : BitVec (8 * sz)} {x : ScalarInt} (hx : ScalarRange sz lo hi x) (hpos : 0 < lo.toNat) :
    ∃ r, evalCtlzNonzero x retBytes = some r ∧ r.bits < 8 * sz ∧
      ScalarRange retBytes (BitVec.ofNat (8 * retBytes) (Anneal.BitVec.clz hi))
        (BitVec.ofNat (8 * retBytes) (Anneal.BitVec.clz lo)) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarRange_exists hx
  have hne : BitVec.ofNat (8 * sz) xb ≠ BitVec.ofNat (8 * sz) 0 := by
    intro hz
    have hle : lo.toNat ≤ (BitVec.ofNat (8 * sz) xb).toNat := hx₁
    rw [hz, Anneal.BitVec.toNat_zero] at hle
    omega
  have hev := evalCtlzNonzero_eq_clz hsz hret hne
  have hlo_lt : Anneal.BitVec.clz hi < scalarModulus retBytes :=
    Nat.lt_of_le_of_lt (Anneal.BitVec.clz_le hi) hfit
  have hhi_lt : Anneal.BitVec.clz lo < scalarModulus retBytes :=
    Nat.lt_of_le_of_lt (Anneal.BitVec.clz_le lo) hfit
  have hcur_lt : Anneal.BitVec.clz (BitVec.ofNat (8 * sz) xb) < scalarModulus retBytes :=
    Nat.lt_of_le_of_lt (Anneal.BitVec.clz_le _) hfit
  refine ⟨_, hev.1, hev.2, scalarRange_iff_bits.2 ⟨hcur_lt, ?_, ?_⟩⟩
  · rw [toNat_ofNat_of_lt hlo_lt]; exact clz_antitone hx₂
  · rw [toNat_ofNat_of_lt hhi_lt]; exact clz_antitone hx₁

/-- Exact interval transfer through `evalCtlzNonzero` when the highest set bit is fixed at `k`. -/
theorem scalarRange_evalCtlzNonzero {sz retBytes k : Nat} (hsz : 0 < sz) (hret : 0 < retBytes)
    {lo hi : BitVec (8 * sz)} {x : ScalarInt} (hx : ScalarRange sz lo hi x) (hk : k < 8 * sz)
    (hlo : 2 ^ k ≤ lo.toNat) (hhi : hi.toNat < 2 ^ (k + 1)) :
    evalCtlzNonzero x retBytes = some ⟨8 * sz - 1 - k, retBytes⟩ := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  have h₁ : lo.toNat ≤ (BitVec.ofNat (8 * sz) xb).toNat := hx₁
  have h₂ : (BitVec.ofNat (8 * sz) xb).toNat ≤ hi.toNat := hx₂
  have hpow : 0 < 2 ^ k := Nat.two_pow_pos k
  have hne : BitVec.ofNat (8 * sz) xb ≠ BitVec.ofNat (8 * sz) 0 := by
    intro hz
    rw [hz, Anneal.BitVec.toNat_zero] at h₁
    omega
  have hev := (evalCtlzNonzero_eq_clz hsz hret hne).1
  rw [toNat_ofNat_of_lt hxb] at h₁ h₂
  have hclz : Anneal.BitVec.clz (BitVec.ofNat (8 * sz) xb) = 8 * sz - 1 - k :=
    clz_eq_of_bounds _ hk (by rw [toNat_ofNat_of_lt hxb]; exact Nat.le_trans hlo h₁)
      (by rw [toNat_ofNat_of_lt hxb]; exact Nat.lt_of_le_of_lt h₂ hhi)
  rw [hev, hclz]

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

/-- Unconditional form of the unsigned operational `Trusted` `evalScalarBinOp .shr` bridge. -/
theorem evalScalarBinOp_shr_unsigned_eq_extractBits {szL szR : Nat} (hszL : 0 < szL)
    (hszR : 0 < szR) (a b : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp .shr ⟨a, szL⟩ ⟨b, szR⟩ locals mem false =
      .ok (.scalar ⟨(Anneal.BitVecArith.extractBits
        (BitVec.ofNat (8 * szL + b % (8 * szL)) a) (b % (8 * szL)) (8 * szL)).toNat, szL⟩)
        locals mem := by
  rw [Anneal.Scalars.evalScalarBinOp_shr_unsigned hszL hszR, shiftRight_mod_eq_extractBits]

/-- Chunk width `0` is degenerate: `chunksOf 0` returns no chunks at all, so
`chunksOf_encodeElems` genuinely needs `0 < n`. -/
theorem chunksOf_encodeElems_zero_width {α : Type} (c : FixedByteCodec α 0) (xs : List α) :
    Anneal.ListChunks.chunksOf 0 (c.encodeElems xs) = [] :=
  Anneal.ListChunks.chunksOf_zero_size _

/-! ## 11. Sign-Flag Independence, Operational Lifts and Signed-Integer Arrays -/

/-- The `isSigned` flag is irrelevant to the bitwise, left-shift, wrapping-arithmetic and
(in)equality operators of `evalBinOp`: any two flags give the same result, on arbitrary
(possibly zero-width or mismatched-width) operands. -/
theorem evalBinOp_isSigned_irrel {op : BinOp}
    (hop : op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor ∨ op = .shl ∨ op = .add ∨ op = .sub ∨
      op = .mul ∨ op = .eq ∨ op = .ne)
    (x y : ScalarInt) (s₁ s₂ : Bool) :
    Anneal.Scalars.evalBinOp op x y s₁ = Anneal.Scalars.evalBinOp op x y s₂ := by
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `evalBinOp_shr_bitAnd_eq_extractField` with an arbitrary sign flag on the masking step (the
shift itself must be the unsigned, logical one). -/
theorem evalBinOp_shr_bitAnd_eq_extractField_flag {sz szR : Nat} (hsz : 0 < sz) (hszR : 0 < szR)
    {x lo : Nat} (hx : x < scalarModulus sz) (hlo : lo < 8 * sz) (len : Nat) (s : Bool) :
    (Anneal.Scalars.evalBinOp .shr ⟨x, sz⟩ ⟨lo, szR⟩ false).bind
        (fun r => Anneal.Scalars.evalBinOp .bitAnd r ⟨2 ^ len - 1, sz⟩ s) =
      some ⟨extractField sz x lo len, sz⟩ :=
  evalBinOp_shr_bitAnd_eq_extractField hsz hszR hx hlo len

/-- `evalBinOp_shl_bitOr_eq_pack` with arbitrary sign flags on all three steps. -/
theorem evalBinOp_shl_bitOr_eq_pack_flag {sz szR : Nat} (hsz : 0 < sz) (hszR : 0 < szR)
    {lo₁ lo₂ : Nat} (h₁ : lo₁ < 8 * sz) (h₂ : lo₂ < 8 * sz) (a b : Nat) (s₁ s₂ s₃ : Bool) :
    (Anneal.Scalars.evalBinOp .shl ⟨a, sz⟩ ⟨lo₁, szR⟩ s₁).bind (fun sa =>
        (Anneal.Scalars.evalBinOp .shl ⟨b, sz⟩ ⟨lo₂, szR⟩ s₂).bind (fun sb =>
          Anneal.Scalars.evalBinOp .bitOr sa sb s₃)) =
      some ⟨bitwiseOrBits (8 * sz) (shiftLeftBits a lo₁ (scalarModulus sz))
        (shiftLeftBits b lo₂ (scalarModulus sz)), sz⟩ :=
  evalBinOp_shl_bitOr_eq_pack hsz hszR h₁ h₂ a b

/-- `evalBinOp_pack_injective` with arbitrary sign flags on all three steps of both packs. -/
theorem evalBinOp_pack_injective_flag {sz szR : Nat} (hsz : 0 < sz) (hszR : 0 < szR)
    {lo₁ len₁ lo₂ len₂ a₁ b₁ a₂ b₂ : Nat} (s₁ s₂ s₃ t₁ t₂ t₃ : Bool)
    (ha₁ : a₁ < 2 ^ len₁) (hb₁ : b₁ < 2 ^ len₂) (ha₂ : a₂ < 2 ^ len₁) (hb₂ : b₂ < 2 ^ len₂)
    (h₁ : lo₁ + len₁ ≤ 8 * sz) (h₂ : lo₂ + len₂ ≤ 8 * sz)
    (hd : lo₁ + len₁ ≤ lo₂ ∨ lo₂ + len₂ ≤ lo₁)
    (h : (Anneal.Scalars.evalBinOp .shl ⟨a₁, sz⟩ ⟨lo₁, szR⟩ s₁).bind (fun sa =>
          (Anneal.Scalars.evalBinOp .shl ⟨b₁, sz⟩ ⟨lo₂, szR⟩ s₂).bind (fun sb =>
            Anneal.Scalars.evalBinOp .bitOr sa sb s₃)) =
        (Anneal.Scalars.evalBinOp .shl ⟨a₂, sz⟩ ⟨lo₁, szR⟩ t₁).bind (fun sa =>
          (Anneal.Scalars.evalBinOp .shl ⟨b₂, sz⟩ ⟨lo₂, szR⟩ t₂).bind (fun sb =>
            Anneal.Scalars.evalBinOp .bitOr sa sb t₃))) :
    a₁ = a₂ ∧ b₁ = b₂ :=
  evalBinOp_pack_injective hsz hszR ha₁ hb₁ ha₂ hb₂ h₁ h₂ hd h

/-- On same-width operands, every scalar-returning total operator of `evalBinOp` (bitwise,
wrapping arithmetic, equality and both signednesses of the comparisons) succeeds, and the
operational `evalScalarBinOp` returns the same scalar without touching locals or memory. -/
theorem evalScalarBinOp_of_evalBinOp {sz : Nat} (hsz : 0 < sz) {op : BinOp}
    (hop : op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor ∨ op = .add ∨ op = .sub ∨ op = .mul ∨
      op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) (s : Bool) :
    ∃ r, Anneal.Scalars.evalBinOp op ⟨a, sz⟩ ⟨b, sz⟩ s = some r ∧
      evalScalarBinOp op ⟨a, sz⟩ ⟨b, sz⟩ locals mem s = .ok (.scalar r) locals mem := by
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, Anneal.Scalars.evalBinOp_bitAnd_apply hsz s,
      Anneal.Scalars.evalScalarBinOp_bitAnd hsz locals mem s⟩
  · exact ⟨_, Anneal.Scalars.evalBinOp_bitOr_apply hsz s,
      Anneal.Scalars.evalScalarBinOp_bitOr hsz locals mem s⟩
  · exact ⟨_, Anneal.Scalars.evalBinOp_bitXor_apply hsz s,
      Anneal.Scalars.evalScalarBinOp_bitXor hsz locals mem s⟩
  · exact ⟨_, Anneal.Scalars.evalBinOp_add_apply hsz s,
      Anneal.Scalars.evalScalarBinOp_add hsz locals mem s⟩
  · exact ⟨_, Anneal.Scalars.evalBinOp_sub_apply hsz s,
      Anneal.Scalars.evalScalarBinOp_sub hsz locals mem s⟩
  · exact ⟨_, Anneal.Scalars.evalBinOp_mul_apply hsz s,
      Anneal.Scalars.evalScalarBinOp_mul hsz locals mem s⟩
  · exact ⟨_, Anneal.Scalars.evalBinOp_eq_apply hsz s,
      Anneal.Scalars.evalScalarBinOp_eq hsz locals mem s⟩
  · exact ⟨_, Anneal.Scalars.evalBinOp_ne_apply hsz s,
      Anneal.Scalars.evalScalarBinOp_ne hsz locals mem s⟩
  · cases s with
    | false => exact ⟨_, Anneal.Scalars.evalBinOp_lt_unsigned hsz,
        Anneal.Scalars.evalScalarBinOp_lt_unsigned hsz locals mem⟩
    | true => exact ⟨_, Anneal.Scalars.evalBinOp_lt_signed hsz,
        Anneal.Scalars.evalScalarBinOp_lt_signed hsz locals mem⟩
  · cases s with
    | false => exact ⟨_, Anneal.Scalars.evalBinOp_le_unsigned hsz,
        Anneal.Scalars.evalScalarBinOp_le_unsigned hsz locals mem⟩
    | true => exact ⟨_, Anneal.Scalars.evalBinOp_le_signed hsz,
        Anneal.Scalars.evalScalarBinOp_le_signed hsz locals mem⟩
  · cases s with
    | false => exact ⟨_, Anneal.Scalars.evalBinOp_gt_unsigned hsz,
        Anneal.Scalars.evalScalarBinOp_gt_unsigned hsz locals mem⟩
    | true => exact ⟨_, Anneal.Scalars.evalBinOp_gt_signed hsz,
        Anneal.Scalars.evalScalarBinOp_gt_signed hsz locals mem⟩
  · cases s with
    | false => exact ⟨_, Anneal.Scalars.evalBinOp_ge_unsigned hsz,
        Anneal.Scalars.evalScalarBinOp_ge_unsigned hsz locals mem⟩
    | true => exact ⟨_, Anneal.Scalars.evalBinOp_ge_signed hsz,
        Anneal.Scalars.evalScalarBinOp_ge_signed hsz locals mem⟩

/-- Shift counterpart of `evalScalarBinOp_of_evalBinOp`: the right operand may have a different
positive byte width. -/
theorem evalScalarBinOp_shift_of_evalBinOp {szL szR : Nat} (hszL : 0 < szL) (hszR : 0 < szR)
    {op : BinOp} (hop : op = .shl ∨ op = .shr) (a b : Nat) (locals : List LocalSlot)
    (mem : Memory) (s : Bool) :
    ∃ r, Anneal.Scalars.evalBinOp op ⟨a, szL⟩ ⟨b, szR⟩ s = some r ∧
      evalScalarBinOp op ⟨a, szL⟩ ⟨b, szR⟩ locals mem s = .ok (.scalar r) locals mem := by
  rcases hop with rfl | rfl
  · exact ⟨_, Anneal.Scalars.evalBinOp_shl_apply hszL hszR s,
      Anneal.Scalars.evalScalarBinOp_shl hszL hszR locals mem s⟩
  · cases s with
    | false => exact ⟨_, Anneal.Scalars.evalBinOp_shr_unsigned hszL hszR,
        Anneal.Scalars.evalScalarBinOp_shr_unsigned hszL hszR locals mem⟩
    | true => exact ⟨_, Anneal.Scalars.evalBinOp_shr_signed hszL hszR,
        Anneal.Scalars.evalScalarBinOp_shr_signed hszL hszR locals mem⟩

/-- Unsigned division and remainder: whenever `evalBinOp` returns a scalar (the divisor is
non-zero), the operational `evalScalarBinOp` returns the same scalar. -/
theorem evalScalarBinOp_divRem_unsigned_of_evalBinOp {sz : Nat} (hsz : 0 < sz) {op : BinOp}
    (hop : op = .div ∨ op = .rem) {a b : Nat} {r : ScalarInt}
    (h : Anneal.Scalars.evalBinOp op ⟨a, sz⟩ ⟨b, sz⟩ false = some r)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp op ⟨a, sz⟩ ⟨b, sz⟩ locals mem false = .ok (.scalar r) locals mem := by
  rcases hop with rfl | rfl
  · cases Nat.eq_zero_or_pos b with
    | inl hb =>
      subst hb
      rw [Anneal.Scalars.evalBinOp_div_zero hsz] at h
      cases h
    | inr hb =>
      rw [Anneal.Scalars.evalBinOp_div_unsigned hsz (Nat.ne_of_gt hb)] at h
      rw [Anneal.Scalars.evalScalarBinOp_div_unsigned hsz (Nat.ne_of_gt hb),
        ← Option.some.inj h]
  · cases Nat.eq_zero_or_pos b with
    | inl hb =>
      subst hb
      rw [Anneal.Scalars.evalBinOp_rem_zero hsz] at h
      cases h
    | inr hb =>
      rw [Anneal.Scalars.evalBinOp_rem_unsigned hsz (Nat.ne_of_gt hb)] at h
      rw [Anneal.Scalars.evalScalarBinOp_rem_unsigned hsz (Nat.ne_of_gt hb),
        ← Option.some.inj h]

/-- Generic operational lift: any property established for the `evalBinOp` result of a
same-width total operator on `sz`-byte scalars (for example a `ScalarTnum`, `ScalarRange` or
`ScalarSRange` transfer) holds for the scalar returned by the operational `evalScalarBinOp`. -/
theorem evalScalarBinOp_transfer {sz : Nat} (hsz : 0 < sz) {op : BinOp}
    (hop : op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor ∨ op = .add ∨ op = .sub ∨ op = .mul ∨
      op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {x y : ScalarInt} (hx : x.sizeBytes = sz) (hy : y.sizeBytes = sz) (s : Bool)
    {P : ScalarInt → Prop} (h : ∃ r, Anneal.Scalars.evalBinOp op x y s = some r ∧ P r)
    (locals : List LocalSlot) (mem : Memory) :
    ∃ r, evalScalarBinOp op x y locals mem s = .ok (.scalar r) locals mem ∧ P r := by
  cases x with
  | mk a sx =>
    cases y with
    | mk b sy =>
      have hx' : sx = sz := hx
      have hy' : sy = sz := hy
      subst hx'; subst hy'
      obtain ⟨r, hr, hP⟩ := h
      obtain ⟨r', hr', hop'⟩ := evalScalarBinOp_of_evalBinOp hsz hop a b locals mem s
      have hrr : r' = r := Option.some.inj (hr'.symm.trans hr)
      subst hrr
      exact ⟨r', hop', hP⟩

/-- Generic operational lift for shifts (the right operand may have any positive width). -/
theorem evalScalarBinOp_shift_transfer {szL : Nat} (hszL : 0 < szL) {op : BinOp}
    (hop : op = .shl ∨ op = .shr) {x y : ScalarInt} (hx : x.sizeBytes = szL)
    (hy : 0 < y.sizeBytes) (s : Bool) {P : ScalarInt → Prop}
    (h : ∃ r, Anneal.Scalars.evalBinOp op x y s = some r ∧ P r)
    (locals : List LocalSlot) (mem : Memory) :
    ∃ r, evalScalarBinOp op x y locals mem s = .ok (.scalar r) locals mem ∧ P r := by
  cases x with
  | mk a sx =>
    cases y with
    | mk b sy =>
      have hx' : sx = szL := hx
      subst hx'
      obtain ⟨r, hr, hP⟩ := h
      obtain ⟨r', hr', hop'⟩ := evalScalarBinOp_shift_of_evalBinOp hszL hy hop a b locals mem s
      have hrr : r' = r := Option.some.inj (hr'.symm.trans hr)
      subst hrr
      exact ⟨r', hop', hP⟩

/-- Operational counterpart of `evalBinOp_shr_bitAnd_eq_extractField`: on a canonical operand
with an in-range shift amount, the `Trusted` evaluator's logical shift returns
`shiftRightUnsignedBits`, and masking that result returns `extractField` (any sign flag on the
mask step). -/
theorem evalScalarBinOp_shr_bitAnd_eq_extractField {sz szR : Nat} (hsz : 0 < sz)
    (hszR : 0 < szR) {x lo : Nat} (hx : x < scalarModulus sz) (hlo : lo < 8 * sz) (len : Nat)
    (locals : List LocalSlot) (mem : Memory) (s : Bool) :
    evalScalarBinOp .shr ⟨x, sz⟩ ⟨lo, szR⟩ locals mem false =
        .ok (.scalar ⟨shiftRightUnsignedBits x lo, sz⟩) locals mem ∧
      evalScalarBinOp .bitAnd ⟨shiftRightUnsignedBits x lo, sz⟩ ⟨2 ^ len - 1, sz⟩ locals mem s =
        .ok (.scalar ⟨extractField sz x lo len, sz⟩) locals mem := by
  have hx' : x < 2 ^ (8 * sz) := by rw [← scalarModulus_eq]; exact hx
  have hle : x >>> lo ≤ x := Nat.shiftRight_le x lo
  constructor
  · rw [Anneal.Scalars.evalScalarBinOp_shr_unsigned hsz hszR, Nat.mod_eq_of_lt hlo,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hx'),
      Anneal.Scalars.shiftRightUnsignedBits_eq_shiftRight]
  · rw [Anneal.Scalars.evalScalarBinOp_bitAnd hsz]
    unfold extractField
    rw [Anneal.Scalars.bitwiseAndBits_eq_land]

/-- Operational counterpart of `evalBinOp_shl_bitOr_eq_pack`: the `Trusted` evaluator's two
left shifts return `shiftLeftBits`, and OR-ing those results returns the scalar pack (any sign
flags, in-range shift amounts). -/
theorem evalScalarBinOp_shl_bitOr_eq_pack {sz szR : Nat} (hsz : 0 < sz) (hszR : 0 < szR)
    {lo₁ lo₂ : Nat} (h₁ : lo₁ < 8 * sz) (h₂ : lo₂ < 8 * sz) (a b : Nat)
    (locals : List LocalSlot) (mem : Memory) (s₁ s₂ s₃ : Bool) :
    evalScalarBinOp .shl ⟨a, sz⟩ ⟨lo₁, szR⟩ locals mem s₁ =
        .ok (.scalar ⟨shiftLeftBits a lo₁ (scalarModulus sz), sz⟩) locals mem ∧
      evalScalarBinOp .shl ⟨b, sz⟩ ⟨lo₂, szR⟩ locals mem s₂ =
        .ok (.scalar ⟨shiftLeftBits b lo₂ (scalarModulus sz), sz⟩) locals mem ∧
      evalScalarBinOp .bitOr ⟨shiftLeftBits a lo₁ (scalarModulus sz), sz⟩
          ⟨shiftLeftBits b lo₂ (scalarModulus sz), sz⟩ locals mem s₃ =
        .ok (.scalar ⟨bitwiseOrBits (8 * sz) (shiftLeftBits a lo₁ (scalarModulus sz))
          (shiftLeftBits b lo₂ (scalarModulus sz)), sz⟩) locals mem := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Anneal.Scalars.evalScalarBinOp_shl hsz hszR, Nat.mod_eq_of_lt h₁,
      Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod]
  · rw [Anneal.Scalars.evalScalarBinOp_shl hsz hszR, Nat.mod_eq_of_lt h₂,
      Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod]
  · rw [Anneal.Scalars.evalScalarBinOp_bitOr hsz, Anneal.Scalars.bitwiseOrBits_eq_lor]

/-- Byte size of `[iN; n]` (including `n = 0`). -/
theorem rigidTyByteSize_array_int (layouts : LayoutTable) (w : IntTy) (n : Nat)
    (idx : LayoutIdx) :
    rigidTyByteSize layouts { kind := .array (.int w) n, layoutIdx := idx } =
      some (MirValueCodec.intByteSize w * n) := by
  cases w <;> rfl

/-- Signed-array transmutation: any value of `[iA; n₁]` transmutes soundly to `[iB; n₂]`
whenever the byte sizes agree (`array_int_isIntoBytes`, `array_int_isFromBytes`). -/
theorem array_int_transmute_sound (layouts : LayoutTable) (w₁ w₂ : IntTy) (n₁ n₂ : Nat)
    (idx₁ idx₂ : LayoutIdx)
    (hsize : MirValueCodec.intByteSize w₁ * n₁ = MirValueCodec.intByteSize w₂ * n₂)
    (v : Value) (bs : List AbstractByte)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts
      { kind := .array (.int w₁) n₁, layoutIdx := idx₁ } v = some bs) :
    ∃ v', decodeValueFromBytes defaultCodecFuel layouts
      { kind := .array (.int w₂) n₂, layoutIdx := idx₂ } bs = some v' :=
  transmute_sound_of_into_from_bytes layouts _ _
    (array_int_isIntoBytes layouts w₁ n₁ idx₁) (array_int_isFromBytes layouts w₂ n₂ idx₂)
    (by rw [rigidTyByteSize_array_int, rigidTyByteSize_array_int, hsize]) v bs hEnc

/-- Unsigned-to-signed array transmutation (`[uA; n₁] → [iB; n₂]`) at equal byte sizes. -/
theorem array_uint_to_int_transmute_sound (layouts : LayoutTable) (w₁ : UintTy) (w₂ : IntTy)
    (n₁ n₂ : Nat) (idx₁ idx₂ : LayoutIdx)
    (hsize : MirValueCodec.uintByteSize w₁ * n₁ = MirValueCodec.intByteSize w₂ * n₂)
    (v : Value) (bs : List AbstractByte)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts
      { kind := .array (.uint w₁) n₁, layoutIdx := idx₁ } v = some bs) :
    ∃ v', decodeValueFromBytes defaultCodecFuel layouts
      { kind := .array (.int w₂) n₂, layoutIdx := idx₂ } bs = some v' :=
  transmute_sound_of_into_from_bytes layouts _ _
    (array_uint_isIntoBytes layouts w₁ n₁ idx₁) (array_int_isFromBytes layouts w₂ n₂ idx₂)
    (by rw [rigidTyByteSize_array_uint, rigidTyByteSize_array_int, hsize]) v bs hEnc

/-- Signed-to-unsigned array transmutation (`[iA; n₁] → [uB; n₂]`) at equal byte sizes. -/
theorem array_int_to_uint_transmute_sound (layouts : LayoutTable) (w₁ : IntTy) (w₂ : UintTy)
    (n₁ n₂ : Nat) (idx₁ idx₂ : LayoutIdx)
    (hsize : MirValueCodec.intByteSize w₁ * n₁ = MirValueCodec.uintByteSize w₂ * n₂)
    (v : Value) (bs : List AbstractByte)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts
      { kind := .array (.int w₁) n₁, layoutIdx := idx₁ } v = some bs) :
    ∃ v', decodeValueFromBytes defaultCodecFuel layouts
      { kind := .array (.uint w₂) n₂, layoutIdx := idx₂ } bs = some v' :=
  transmute_sound_of_into_from_bytes layouts _ _
    (array_int_isIntoBytes layouts w₁ n₁ idx₁) (array_uint_isFromBytes layouts w₂ n₂ idx₂)
    (by rw [rigidTyByteSize_array_int, rigidTyByteSize_array_uint, hsize]) v bs hEnc

/-! ## 12. Checked/Unchecked Arithmetic & Shifts, Bitwise Ranges, Big-Endian Decode and `[iN; n]` -/

/-- Generic operational lift for unsigned division and remainder: any transfer proved on
`evalBinOp` lifts directly to `Trusted` `evalScalarBinOp`. -/
theorem evalScalarBinOp_divRem_unsigned_transfer {sz : Nat} (hsz : 0 < sz) {op : BinOp}
    (hop : op = .div ∨ op = .rem) {x y : ScalarInt} (hx : x.sizeBytes = sz) (hy : y.sizeBytes = sz)
    {P : ScalarInt → Prop} (h : ∃ r, Anneal.Scalars.evalBinOp op x y false = some r ∧ P r)
    (locals : List LocalSlot) (mem : Memory) :
    ∃ r, evalScalarBinOp op x y locals mem false = .ok (.scalar r) locals mem ∧ P r := by
  cases x with
  | mk a sx =>
    cases y with
    | mk b sy =>
      have hx' : sx = sz := hx
      have hy' : sy = sz := hy
      subst hx'; subst hy'
      obtain ⟨r, hr, hP⟩ := h
      exact ⟨r, evalScalarBinOp_divRem_unsigned_of_evalBinOp hsz hop hr locals mem, hP⟩

/-- `evalCastValue` is rejected exactly on a zero-width source or zero-width destination. -/
theorem evalCastValue_eq_none_iff (sc : ScalarInt) (dstBytes : Nat) (srcIsSigned : Bool) :
    Anneal.Scalars.evalCastValue sc dstBytes srcIsSigned = none ↔
      sc.sizeBytes = 0 ∨ dstBytes = 0 := by
  unfold Anneal.Scalars.evalCastValue
  cases h0 : Nat.beq sc.sizeBytes 0 with
  | true => exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h0), fun _ => rfl⟩
  | false =>
    have hne : sc.sizeBytes ≠ 0 := fun h => by rw [h] at h0; nomatch h0
    cases h1 : Nat.beq dstBytes 0 with
    | true => exact ⟨fun _ => Or.inr (Nat.eq_of_beq_eq_true h1), fun _ => rfl⟩
    | false =>
      have hne' : dstBytes ≠ 0 := fun h => by rw [h] at h1; nomatch h1
      refine ⟨fun h => ?_, fun h => ?_⟩
      · cases h
      · cases h with
        | inl h => exact absurd h hne
        | inr h => exact absurd h hne'

/-- `signedOverflowAdd` is `false` whenever the ported `signedKey` sum stays within the
two's-complement no-underflow / no-overflow window (`2^(w-1) ≤ signedKey a + signedKey b <
2^(w-1) + 2^w`). -/
theorem signedOverflowAdd_eq_false_of_signedKey_bounds {sz : Nat} (hsz : 0 < sz) (a b : Nat)
    (hno_udf : 2 ^ (8 * sz - 1) ≤
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) a) +
        Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) b))
    (hno_ovf :
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) a) +
        Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) b) <
          2 ^ (8 * sz - 1) + 2 ^ (8 * sz)) :
    signedOverflowAdd a b sz = false := by
  have hw : 0 < 8 * sz := by omega
  have hsum := Anneal.BitVecArith.signedKey_add_no_overflow hw
    (a := BitVec.ofNat (8 * sz) a) (b := BitVec.ofNat (8 * sz) b) hno_udf hno_ovf
  rw [Anneal.Scalars.signedOverflowAdd_eq_msb]
  cases ha : (BitVec.ofNat (8 * sz) a).msb with
  | false =>
    cases hb : (BitVec.ofNat (8 * sz) b).msb with
    | true => rfl
    | false =>
      have hka := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw ha
      have hkb := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hb
      rw [natPow_eq] at hka hkb hsum
      cases hs : (BitVec.ofNat (8 * sz) a + BitVec.ofNat (8 * sz) b).msb with
      | false => rfl
      | true =>
        have hks := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hs
        rw [natPow_eq] at hks
        omega
  | true =>
    cases hb : (BitVec.ofNat (8 * sz) b).msb with
    | false => rfl
    | true =>
      have hka := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw ha
      have hkb := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hb
      rw [natPow_eq] at hka hkb hsum
      cases hs : (BitVec.ofNat (8 * sz) a + BitVec.ofNat (8 * sz) b).msb with
      | true => rfl
      | false =>
        have hks := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hs
        rw [natPow_eq] at hks
        omega

/-- Operational unsigned `addUnchecked`: when `a_hi + b_hi < 2^(8*sz)`, `evalScalarBinOp`
never hits `.ub` and returns a scalar in `[a_lo + b_lo, a_hi + b_hi]`. -/
theorem scalarRange_evalScalarBinOp_addUnchecked_unsigned {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt} (locals : List LocalSlot)
    (mem : Memory) (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y)
    (hno : a_hi.toNat + b_hi.toNat < 2 ^ (8 * sz)) :
    ∃ r, evalScalarBinOp .addUnchecked x y locals mem false = .ok (.scalar r) locals mem ∧
      ScalarRange sz (a_lo + b_lo) (a_hi + b_hi) r := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, hy₂⟩ := scalarRange_exists hy
  have hle_x : xb ≤ a_hi.toNat := by
    have h : (BitVec.ofNat (8 * sz) xb).toNat ≤ a_hi.toNat := hx₂
    rwa [toNat_ofNat_of_lt hxb] at h
  have hle_y : yb ≤ b_hi.toNat := by
    have h : (BitVec.ofNat (8 * sz) yb).toNat ≤ b_hi.toNat := hy₂
    rwa [toNat_ofNat_of_lt hyb] at h
  have hlt : xb + yb < 2 ^ (8 * sz) := by omega
  have hble : Nat.ble (2 ^ (8 * sz)) (xb + yb) = false := by
    cases h : Nat.ble (2 ^ (8 * sz)) (xb + yb) with
    | false => rfl
    | true =>
      have := Nat.le_of_ble_eq_true h
      omega
  have hs := Anneal.BitVec.range_add_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno
  have heq : (BitVec.ofNat (8 * sz) xb + BitVec.ofNat (8 * sz) yb).toNat = xb + yb := by
    rw [← add_mod_eq_toNat_add, Nat.mod_eq_of_lt hlt]
  refine ⟨⟨xb + yb, sz⟩, ?_, ?_⟩
  · rw [Anneal.Scalars.evalScalarBinOp_addUnchecked_unsigned hsz, hble]
  · rw [← heq]
    exact scalarRange_of_bitVec _ hs.1 hs.2

/-- Operational unsigned `addWithOverflow`: when `a_hi + b_hi < 2^(8*sz)`, the overflow flag is
`false` (`0`) and the sum lies in `[a_lo + b_lo, a_hi + b_hi]`. -/
theorem scalarRange_evalScalarBinOp_addWithOverflow_unsigned {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt} (locals : List LocalSlot)
    (mem : Memory) (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y)
    (hno : a_hi.toNat + b_hi.toNat < 2 ^ (8 * sz)) :
    ∃ r, evalScalarBinOp .addWithOverflow x y locals mem false =
        .ok (.aggregate 0 [.scalar r, .scalar (boolToScalar false)]) locals mem ∧
      ScalarRange sz (a_lo + b_lo) (a_hi + b_hi) r := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, hy₂⟩ := scalarRange_exists hy
  have hle_x : xb ≤ a_hi.toNat := by
    have h : (BitVec.ofNat (8 * sz) xb).toNat ≤ a_hi.toNat := hx₂
    rwa [toNat_ofNat_of_lt hxb] at h
  have hle_y : yb ≤ b_hi.toNat := by
    have h : (BitVec.ofNat (8 * sz) yb).toNat ≤ b_hi.toNat := hy₂
    rwa [toNat_ofNat_of_lt hyb] at h
  have hble : Nat.ble (2 ^ (8 * sz)) (xb + yb) = false := by
    cases h : Nat.ble (2 ^ (8 * sz)) (xb + yb) with
    | false => rfl
    | true =>
      have := Nat.le_of_ble_eq_true h
      omega
  have hs := Anneal.BitVec.range_add_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno
  refine ⟨⟨(BitVec.ofNat (8 * sz) xb + BitVec.ofNat (8 * sz) yb).toNat, sz⟩, ?_,
    scalarRange_of_bitVec _ hs.1 hs.2⟩
  rw [Anneal.Scalars.evalScalarBinOp_addWithOverflow hsz, hble, add_mod_eq_toNat_add]
  rfl

/-- Operational unsigned `subUnchecked`: when `b_hi ≤ a_lo`, `evalScalarBinOp` never hits `.ub`
and returns a scalar in `[a_lo - b_hi, a_hi - b_lo]`. -/
theorem scalarRange_evalScalarBinOp_subUnchecked_unsigned {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt} (locals : List LocalSlot)
    (mem : Memory) (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y)
    (hno : b_hi ≤ a_lo) :
    ∃ r, evalScalarBinOp .subUnchecked x y locals mem false = .ok (.scalar r) locals mem ∧
      ScalarRange sz (a_lo - b_hi) (a_hi - b_lo) r := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, hy₂⟩ := scalarRange_exists hy
  have hax : a_lo.toNat ≤ xb := by
    have h : a_lo.toNat ≤ (BitVec.ofNat (8 * sz) xb).toNat := hx₁
    rwa [toNat_ofNat_of_lt hxb] at h
  have hby : yb ≤ b_hi.toNat := by
    have h : (BitVec.ofNat (8 * sz) yb).toNat ≤ b_hi.toNat := hy₂
    rwa [toNat_ofNat_of_lt hyb] at h
  have hba : b_hi.toNat ≤ a_lo.toNat := hno
  have hyx : yb ≤ xb := by omega
  have hxb_lt : xb < 2 ^ (8 * sz) := by rw [← scalarModulus_eq]; exact hxb
  have hble : Nat.ble (2 ^ (8 * sz)) (xb - yb) = false := by
    cases h : Nat.ble (2 ^ (8 * sz)) (xb - yb) with
    | false => rfl
    | true =>
      have := Nat.le_of_ble_eq_true h
      omega
  have hs := Anneal.BitVec.range_sub_no_underflow_sound hx₁ hx₂ hy₁ hy₂ hno
  have hbv_le : BitVec.ofNat (8 * sz) yb ≤ BitVec.ofNat (8 * sz) xb := by
    show (BitVec.ofNat (8 * sz) yb).toNat ≤ (BitVec.ofNat (8 * sz) xb).toNat
    rw [toNat_ofNat_of_lt hxb, toNat_ofNat_of_lt hyb]
    exact hyx
  have heq : (BitVec.ofNat (8 * sz) xb - BitVec.ofNat (8 * sz) yb).toNat = xb - yb := by
    rw [Anneal.BitVec.toNat_sub_of_le hbv_le, toNat_ofNat_of_lt hxb, toNat_ofNat_of_lt hyb]
  refine ⟨⟨xb - yb, sz⟩, ?_, ?_⟩
  · rw [Anneal.Scalars.evalScalarBinOp_subUnchecked_unsigned hsz]
    simp only [hyx, ↓reduceDIte, hble]
  · rw [← heq]
    exact scalarRange_of_bitVec _ hs.1 hs.2

/-- Operational unsigned `subWithOverflow`: when `b_hi ≤ a_lo`, the overflow flag is `false` (`0`)
and the difference lies in `[a_lo - b_hi, a_hi - b_lo]`. -/
theorem scalarRange_evalScalarBinOp_subWithOverflow_unsigned {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt} (locals : List LocalSlot)
    (mem : Memory) (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y)
    (hno : b_hi ≤ a_lo) :
    ∃ r, evalScalarBinOp .subWithOverflow x y locals mem false =
        .ok (.aggregate 0 [.scalar r, .scalar (boolToScalar false)]) locals mem ∧
      ScalarRange sz (a_lo - b_hi) (a_hi - b_lo) r := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, hy₂⟩ := scalarRange_exists hy
  have hax : a_lo.toNat ≤ xb := by
    have h : a_lo.toNat ≤ (BitVec.ofNat (8 * sz) xb).toNat := hx₁
    rwa [toNat_ofNat_of_lt hxb] at h
  have hby : yb ≤ b_hi.toNat := by
    have h : (BitVec.ofNat (8 * sz) yb).toNat ≤ b_hi.toNat := hy₂
    rwa [toNat_ofNat_of_lt hyb] at h
  have hba : b_hi.toNat ≤ a_lo.toNat := hno
  have hble : Nat.ble yb xb = true := Nat.ble_eq_true_of_le (by omega)
  have hs := Anneal.BitVec.range_sub_no_underflow_sound hx₁ hx₂ hy₁ hy₂ hno
  refine ⟨⟨(BitVec.ofNat (8 * sz) xb - BitVec.ofNat (8 * sz) yb).toNat, sz⟩, ?_,
    scalarRange_of_bitVec _ hs.1 hs.2⟩
  rw [Anneal.Scalars.evalScalarBinOp_subWithOverflow hsz, hble, sub_mod_eq_toNat_sub]
  rfl

/-- Operational unsigned `mulUnchecked`: when `a_hi * b_hi < 2^(8*sz)`, `evalScalarBinOp` never
hits `.ub` and returns a scalar in `[a_lo * b_lo, a_hi * b_hi]`. -/
theorem scalarRange_evalScalarBinOp_mulUnchecked_unsigned {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt} (locals : List LocalSlot)
    (mem : Memory) (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y)
    (hno : a_hi.toNat * b_hi.toNat < 2 ^ (8 * sz)) :
    ∃ r, evalScalarBinOp .mulUnchecked x y locals mem false = .ok (.scalar r) locals mem ∧
      ScalarRange sz (Anneal.BitVec.mul a_lo b_lo) (Anneal.BitVec.mul a_hi b_hi) r := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, hy₂⟩ := scalarRange_exists hy
  have hle_x : xb ≤ a_hi.toNat := by
    have h : (BitVec.ofNat (8 * sz) xb).toNat ≤ a_hi.toNat := hx₂
    rwa [toNat_ofNat_of_lt hxb] at h
  have hle_y : yb ≤ b_hi.toNat := by
    have h : (BitVec.ofNat (8 * sz) yb).toNat ≤ b_hi.toNat := hy₂
    rwa [toNat_ofNat_of_lt hyb] at h
  have hlt : xb * yb < 2 ^ (8 * sz) :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul hle_x hle_y) hno
  have hble : Nat.ble (2 ^ (8 * sz)) (xb * yb) = false := by
    cases h : Nat.ble (2 ^ (8 * sz)) (xb * yb) with
    | false => rfl
    | true =>
      have := Nat.le_of_ble_eq_true h
      omega
  have hs := Anneal.BitVec.range_mul_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno
  have heq : (Anneal.BitVec.mul (BitVec.ofNat (8 * sz) xb) (BitVec.ofNat (8 * sz) yb)).toNat =
      xb * yb := by
    rw [← mul_mod_eq_toNat_mul, Nat.mod_eq_of_lt hlt]
  refine ⟨⟨xb * yb, sz⟩, ?_, ?_⟩
  · rw [Anneal.Scalars.evalScalarBinOp_mulUnchecked_unsigned hsz, hble]
  · rw [← heq]
    exact scalarRange_of_bitVec _ hs.1 hs.2

/-- Operational unsigned `mulWithOverflow`: when `a_hi * b_hi < 2^(8*sz)`, the overflow flag is
`false` (`0`) and the product lies in `[a_lo * b_lo, a_hi * b_hi]`. -/
theorem scalarRange_evalScalarBinOp_mulWithOverflow_unsigned {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt} (locals : List LocalSlot)
    (mem : Memory) (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y)
    (hno : a_hi.toNat * b_hi.toNat < 2 ^ (8 * sz)) :
    ∃ r, evalScalarBinOp .mulWithOverflow x y locals mem false =
        .ok (.aggregate 0 [.scalar r, .scalar (boolToScalar false)]) locals mem ∧
      ScalarRange sz (Anneal.BitVec.mul a_lo b_lo) (Anneal.BitVec.mul a_hi b_hi) r := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, hy₂⟩ := scalarRange_exists hy
  have hle_x : xb ≤ a_hi.toNat := by
    have h : (BitVec.ofNat (8 * sz) xb).toNat ≤ a_hi.toNat := hx₂
    rwa [toNat_ofNat_of_lt hxb] at h
  have hle_y : yb ≤ b_hi.toNat := by
    have h : (BitVec.ofNat (8 * sz) yb).toNat ≤ b_hi.toNat := hy₂
    rwa [toNat_ofNat_of_lt hyb] at h
  have hlt : xb * yb < 2 ^ (8 * sz) :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul hle_x hle_y) hno
  have hble : Nat.ble (2 ^ (8 * sz)) (xb * yb) = false := by
    cases h : Nat.ble (2 ^ (8 * sz)) (xb * yb) with
    | false => rfl
    | true =>
      have := Nat.le_of_ble_eq_true h
      omega
  have hs := Anneal.BitVec.range_mul_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno
  refine ⟨⟨(Anneal.BitVec.mul (BitVec.ofNat (8 * sz) xb) (BitVec.ofNat (8 * sz) yb)).toNat, sz⟩,
    ?_, scalarRange_of_bitVec _ hs.1 hs.2⟩
  rw [Anneal.Scalars.evalScalarBinOp_mulWithOverflow hsz, hble, mul_mod_eq_toNat_mul]
  rfl

/-- Operational signed `addUnchecked`: when the `ScalarSRange` endpoints satisfy the
no-underflow and no-overflow bounds, `evalScalarBinOp` never hits `.ub` and returns a scalar in
`[smin₁ + smin₂, smax₁ + smax₂]`. -/
theorem scalarSRange_evalScalarBinOp_addUnchecked_signed {sz : Nat} (hsz : 0 < sz)
    {smin₁ smax₁ smin₂ smax₂ : BitVec (8 * sz)} {x y : ScalarInt}
    (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarSRange sz smin₁ smax₁ x) (hy : ScalarSRange sz smin₂ smax₂ y)
    (hno_udf : 2 ^ (8 * sz - 1) ≤
      Anneal.BitVecArith.signedKey smin₁ + Anneal.BitVecArith.signedKey smin₂)
    (hno_ovf : Anneal.BitVecArith.signedKey smax₁ + Anneal.BitVecArith.signedKey smax₂ <
      2 ^ (8 * sz - 1) + 2 ^ (8 * sz)) :
    ∃ r, evalScalarBinOp .addUnchecked x y locals mem true = .ok (.scalar r) locals mem ∧
      ScalarSRange sz (smin₁ + smin₂) (smax₁ + smax₂) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarSRange_exists hy
  have hovf : signedOverflowAdd xb yb sz = false :=
    signedOverflowAdd_eq_false_of_signedKey_bounds hsz xb yb
      (Nat.le_trans hno_udf (Nat.add_le_add hx₁ hy₁))
      (Nat.lt_of_le_of_lt (Nat.add_le_add hx₂ hy₂) hno_ovf)
  have hs := Anneal.BitVecArith.signed_range_add_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno_udf hno_ovf
  refine ⟨⟨(BitVec.ofNat (8 * sz) xb + BitVec.ofNat (8 * sz) yb).toNat, sz⟩, ?_,
    scalarSRange_of_bitVec _ hs.1 hs.2⟩
  rw [Anneal.Scalars.evalScalarBinOp_addUnchecked_signed hsz, hovf, add_mod_eq_toNat_add]

/-- Operational signed `addWithOverflow`: when the `ScalarSRange` endpoints satisfy the
no-underflow and no-overflow bounds, the overflow flag is `false` (`0`) and the sum lies in
`[smin₁ + smin₂, smax₁ + smax₂]`. -/
theorem scalarSRange_evalScalarBinOp_addWithOverflow_signed {sz : Nat} (hsz : 0 < sz)
    {smin₁ smax₁ smin₂ smax₂ : BitVec (8 * sz)} {x y : ScalarInt}
    (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarSRange sz smin₁ smax₁ x) (hy : ScalarSRange sz smin₂ smax₂ y)
    (hno_udf : 2 ^ (8 * sz - 1) ≤
      Anneal.BitVecArith.signedKey smin₁ + Anneal.BitVecArith.signedKey smin₂)
    (hno_ovf : Anneal.BitVecArith.signedKey smax₁ + Anneal.BitVecArith.signedKey smax₂ <
      2 ^ (8 * sz - 1) + 2 ^ (8 * sz)) :
    ∃ r, evalScalarBinOp .addWithOverflow x y locals mem true =
        .ok (.aggregate 0 [.scalar r, .scalar (boolToScalar false)]) locals mem ∧
      ScalarSRange sz (smin₁ + smin₂) (smax₁ + smax₂) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarSRange_exists hy
  have hovf : signedOverflowAdd xb yb sz = false :=
    signedOverflowAdd_eq_false_of_signedKey_bounds hsz xb yb
      (Nat.le_trans hno_udf (Nat.add_le_add hx₁ hy₁))
      (Nat.lt_of_le_of_lt (Nat.add_le_add hx₂ hy₂) hno_ovf)
  have hs := Anneal.BitVecArith.signed_range_add_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno_udf hno_ovf
  refine ⟨⟨(BitVec.ofNat (8 * sz) xb + BitVec.ofNat (8 * sz) yb).toNat, sz⟩, ?_,
    scalarSRange_of_bitVec _ hs.1 hs.2⟩
  rw [Anneal.Scalars.evalScalarBinOp_addWithOverflow hsz, hovf, add_mod_eq_toNat_add]
  rfl

/-- Operational tnum transfer through `shlUnchecked` when the shift amount is in bounds
(`y.bits < 8 * sz`): no `.ub` and exact unmasked shift transfer. -/
theorem scalarTnum_evalScalarBinOp_shlUnchecked {sz : Nat} (hsz : 0 < sz)
    {m v : BitVec (8 * sz)} {x : ScalarInt} (y : ScalarInt) (hy : 0 < y.sizeBytes)
    (hb : y.bits < 8 * sz) (locals : List LocalSlot) (mem : Memory) (isSigned : Bool)
    (hx : ScalarTnum sz m v x) :
    ∃ r, evalScalarBinOp .shlUnchecked x y locals mem isSigned = .ok (.scalar r) locals mem ∧
      ScalarTnum sz (Anneal.BitVec.shl m y.bits) (Anneal.BitVec.shl v y.bits) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  cases y with
  | mk yb ys =>
    refine ⟨_, ?_, scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_shl_sound yb hxm)⟩
    rw [Anneal.Scalars.evalScalarBinOp_shlUnchecked hsz hy hb,
      ← Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod, shiftLeftBits_eq_shl]

/-- Operational tnum transfer through unsigned `shrUnchecked` when `y.bits < 8 * sz`. -/
theorem scalarTnum_evalScalarBinOp_shrUnchecked_unsigned {sz : Nat} (hsz : 0 < sz)
    {m v : BitVec (8 * sz)} {x : ScalarInt} (y : ScalarInt) (hy : 0 < y.sizeBytes)
    (hb : y.bits < 8 * sz) (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarTnum sz m v x) :
    ∃ r, evalScalarBinOp .shrUnchecked x y locals mem false = .ok (.scalar r) locals mem ∧
      ScalarTnum sz (Anneal.BitVec.ushr m y.bits) (Anneal.BitVec.ushr v y.bits) r := by
  obtain ⟨xb, rfl, hxb, hxm⟩ := scalarTnum_exists hx
  cases y with
  | mk yb ys =>
    have hlt : xb >>> yb < 2 ^ (8 * sz) := by
      have hxb' : xb < 2 ^ (8 * sz) := by rw [← scalarModulus_eq]; exact hxb
      exact Nat.lt_of_le_of_lt (Nat.shiftRight_le xb yb) hxb'
    refine ⟨_, ?_, scalarTnum_of_bitVec _ (Anneal.BitVec.tnum_ushr_sound yb hxm)⟩
    rw [Anneal.Scalars.evalScalarBinOp_shrUnchecked_unsigned hsz hy hb, Nat.mod_eq_of_lt hlt,
      ushr_eq_core, _root_.BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hxb]

/-- Operational tnum transfer through signed `shrUnchecked` when `y.bits < 8 * sz`. -/
theorem scalarTnum_evalScalarBinOp_shrUnchecked_signed {sz : Nat} (hsz : 0 < sz)
    {m v : BitVec (8 * sz)} {x : ScalarInt} (y : ScalarInt) (hy : 0 < y.sizeBytes)
    (hb : y.bits < 8 * sz) (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarTnum sz m v x) :
    ∃ r, evalScalarBinOp .shrUnchecked x y locals mem true = .ok (.scalar r) locals mem ∧
      ScalarTnum sz (Anneal.BitVecArith.ashr m y.bits) (Anneal.BitVecArith.ashr v y.bits) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  cases y with
  | mk yb ys =>
    refine ⟨_, ?_, scalarTnum_of_bitVec _ (Anneal.BitVecArith.tnum_ashr_sound yb hxm)⟩
    rw [Anneal.Scalars.evalScalarBinOp_shrUnchecked_signed hsz hy hb, ashr_eq_core]

/-- Operational unsigned interval transfer through `shlUnchecked` when `kmax < 8 * sz` and no
overflow occurs. -/
theorem scalarRange_evalScalarBinOp_shlUnchecked_no_overflow {sz : Nat} (hsz : 0 < sz)
    {umin umax : BitVec (8 * sz)} {x : ScalarInt} (y : ScalarInt) (hy : 0 < y.sizeBytes)
    {kmin kmax : Nat} (locals : List LocalSlot) (mem : Memory) (isSigned : Bool)
    (hx : ScalarRange sz umin umax x) (hk₁ : kmin ≤ y.bits) (hk₂ : y.bits ≤ kmax)
    (hklt : kmax < 8 * sz) (hno : umax.toNat * 2 ^ kmax < 2 ^ (8 * sz)) :
    ∃ r, evalScalarBinOp .shlUnchecked x y locals mem isSigned = .ok (.scalar r) locals mem ∧
      ScalarRange sz (Anneal.BitVec.shl umin kmin) (Anneal.BitVec.shl umax kmax) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarRange_exists hx
  cases y with
  | mk yb ys =>
    have hb : yb < 8 * sz := Nat.lt_of_le_of_lt hk₂ hklt
    have hs := Anneal.BitVecArith.range_shl_no_overflow_sound hx₁ hx₂ hk₁ hk₂ hno
    refine ⟨_, ?_, scalarRange_of_bitVec _ hs.1 hs.2⟩
    rw [Anneal.Scalars.evalScalarBinOp_shlUnchecked hsz hy hb,
      ← Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod, shiftLeftBits_eq_shl]

/-- Operational unsigned interval transfer through unsigned `shrUnchecked` when `kmax < 8 * sz`. -/
theorem scalarRange_evalScalarBinOp_shrUnchecked_unsigned {sz : Nat} (hsz : 0 < sz)
    {umin umax : BitVec (8 * sz)} {x : ScalarInt} (y : ScalarInt) (hy : 0 < y.sizeBytes)
    {kmin kmax : Nat} (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarRange sz umin umax x) (hk₁ : kmin ≤ y.bits) (hk₂ : y.bits ≤ kmax)
    (hklt : kmax < 8 * sz) :
    ∃ r, evalScalarBinOp .shrUnchecked x y locals mem false = .ok (.scalar r) locals mem ∧
      ScalarRange sz (Anneal.BitVec.ushr umin kmax) (Anneal.BitVec.ushr umax kmin) r := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  cases y with
  | mk yb ys =>
    have hb : yb < 8 * sz := Nat.lt_of_le_of_lt hk₂ hklt
    have hlt : xb >>> yb < 2 ^ (8 * sz) := by
      have hxb' : xb < 2 ^ (8 * sz) := by rw [← scalarModulus_eq]; exact hxb
      exact Nat.lt_of_le_of_lt (Nat.shiftRight_le xb yb) hxb'
    have hs := Anneal.BitVecArith.range_ushr_sound hx₁ hx₂ hk₁ hk₂
    refine ⟨_, ?_, scalarRange_of_bitVec _ hs.1 hs.2⟩
    rw [Anneal.Scalars.evalScalarBinOp_shrUnchecked_unsigned hsz hy hb, Nat.mod_eq_of_lt hlt,
      ushr_eq_core, _root_.BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hxb]

/-- Unsigned interval transfer through `evalBinOp .bitAnd` (`Anneal.BitVecArith.range_and_upper_sound`):
the result lies in `[0, min a_hi b_hi]`. -/
theorem scalarRange_evalBinOp_bitAnd {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt} (isSigned : Bool)
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y) :
    ∃ r, Anneal.Scalars.evalBinOp .bitAnd x y isSigned = some r ∧
      ScalarRange sz (BitVec.ofNat (8 * sz) 0) (Anneal.BitVecArith.bvMin a_hi b_hi) r := by
  obtain ⟨xb, rfl, _, _, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, _, _, hy₂⟩ := scalarRange_exists hy
  have hu := Anneal.BitVecArith.range_and_upper_sound hx₂ hy₂
  have hmin : (Anneal.BitVecArith.bvMin a_hi b_hi).toNat = min a_hi.toNat b_hi.toNat := by
    unfold Anneal.BitVecArith.bvMin
    cases hle : decide (a_hi.toNat ≤ b_hi.toNat) with
    | true =>
      have h := of_decide_eq_true hle
      simp [h, Nat.min_eq_left h]
    | false =>
      have hn : ¬ (a_hi.toNat ≤ b_hi.toNat) := of_decide_eq_false hle
      have h : b_hi.toNat ≤ a_hi.toNat := Nat.le_of_not_ge hn
      simp [hn, Nat.min_eq_right h]
  refine ⟨_, evalBinOp_bitAnd_eq_and hsz xb yb isSigned,
    scalarRange_of_bitVec _ (Nat.zero_le _) ?_⟩
  show (Anneal.BitVec.and _ _).toNat ≤ (Anneal.BitVecArith.bvMin a_hi b_hi).toNat
  rw [hmin]
  exact hu

/-- Unsigned interval bounds through `evalBinOp .bitOr` (`Anneal.BitVecArith.range_or_lower_sound`,
`range_or_upper_sound`): `max a_lo b_lo ≤ r.bits ≤ a_hi + b_hi` (and `r.bits < 2^(8*sz)`). -/
theorem scalarRange_evalBinOp_bitOr_bounds {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt} (isSigned : Bool)
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y) :
    ∃ r, Anneal.Scalars.evalBinOp .bitOr x y isSigned = some r ∧
      max a_lo.toNat b_lo.toNat ≤ r.bits ∧ r.bits ≤ a_hi.toNat + b_hi.toNat ∧
      r.bits < scalarModulus sz := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarRange_exists hy
  have hlo := Anneal.BitVecArith.range_or_lower_sound hx₁ hy₁
  have hhi := Anneal.BitVecArith.range_or_upper_sound hx₂ hy₂
  exact ⟨_, evalBinOp_bitOr_eq_or hsz xb yb isSigned, hlo, hhi.1,
    by rw [scalarModulus_eq]; exact hhi.2⟩

/-- Unsigned interval upper bound through `evalBinOp .bitXor`
(`Anneal.BitVecArith.range_xor_upper_sound`): `r.bits ≤ a_hi + b_hi` (and `r.bits < 2^(8*sz)`). -/
theorem scalarRange_evalBinOp_bitXor_upper {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt} (isSigned : Bool)
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y) :
    ∃ r, Anneal.Scalars.evalBinOp .bitXor x y isSigned = some r ∧
      r.bits ≤ a_hi.toNat + b_hi.toNat ∧ r.bits < scalarModulus sz := by
  obtain ⟨xb, rfl, _, _, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, _, _, hy₂⟩ := scalarRange_exists hy
  have hhi := Anneal.BitVecArith.range_xor_upper_sound hx₂ hy₂
  exact ⟨_, evalBinOp_bitXor_eq_xor hsz xb yb isSigned, hhi.1,
    by rw [scalarModulus_eq]; exact hhi.2⟩

/-- `allBytesInitialized` is invariant under list reversal. -/
theorem allBytesInitialized_reverse :
    ∀ bs : List AbstractByte, allBytesInitialized bs.reverse = allBytesInitialized bs
  | [] => rfl
  | .uninit :: rest => by
    rw [List.reverse_cons]
    exact allBytesInitialized_append_eq_false_right rest.reverse rfl
  | .init b p :: rest => by
    rw [List.reverse_cons]
    cases hi : allBytesInitialized rest with
    | true =>
      have hrev : allBytesInitialized rest.reverse = true := by
        rw [allBytesInitialized_reverse rest]; exact hi
      exact allBytesInitialized_append hrev rfl
    | false =>
      have hrev : allBytesInitialized rest.reverse = false := by
        rw [allBytesInitialized_reverse rest]; exact hi
      exact allBytesInitialized_append_eq_false_left _ hrev

/-- `extractInitBvBytes` commutes with list reversal (even when `.uninit` bytes are present). -/
theorem extractInitBvBytes_reverse :
    ∀ bs : List AbstractByte, extractInitBvBytes bs.reverse = (extractInitBvBytes bs).reverse
  | [] => rfl
  | .uninit :: rest => by
    rw [List.reverse_cons, extractInitBvBytes_append, extractInitBvBytes_reverse rest]
    exact List.append_nil _
  | .init b _ :: rest => by
    rw [List.reverse_cons, extractInitBvBytes_append, extractInitBvBytes_reverse rest]
    show (extractInitBvBytes rest).reverse ++ [b.toBitVec] =
      (b.toBitVec :: extractInitBvBytes rest).reverse
    rw [List.reverse_cons]

/-- Big-endian decoding via `bitVecLE` + `bswapBytes`: decoding a reversed byte buffer with
`bitVecLE` agrees with decoding the buffer in little-endian order and byte-swapping the result,
for *every* `bs : List AbstractByte` (including wrong-length, `.uninit`, and mixed-provenance
buffers). -/
theorem bitVecLE_decode_reverse (sz : Nat) (hNz : 0 < sz) (bs : List AbstractByte) :
    (bitVecLE sz hNz).decode bs.reverse =
      ((bitVecLE sz hNz).decode bs).map (Anneal.BitVecArith.bswapBytes sz) := by
  cases Nat.decEq bs.length sz with
  | isFalse hne =>
    have hne' : bs.reverse.length ≠ sz := by rw [List.length_reverse]; exact hne
    rw [bitVecLE_decode_eq_none_of_length_ne sz hNz hne',
      bitVecLE_decode_eq_none_of_length_ne sz hNz hne]
    rfl
  | isTrue hlen =>
    cases hi : allBytesInitialized bs with
    | false =>
      have hi' : allBytesInitialized bs.reverse = false := by
        rw [allBytesInitialized_reverse]; exact hi
      rw [bitVecLE_decode_eq_none_of_uninit sz hNz hi',
        bitVecLE_decode_eq_none_of_uninit sz hNz hi]
      rfl
    | true =>
      have hi' : allBytesInitialized bs.reverse = true := by
        rw [allBytesInitialized_reverse]; exact hi
      have hlen' : bs.reverse.length = sz := by rw [List.length_reverse]; exact hlen
      have hexLen : (extractInitBvBytes bs).length = sz := by
        rw [(length_extractInitBvBytes_eq_iff bs).2 hi, hlen]
      have hx_lt : Anneal.LeBytes.fromLeBytes (extractInitBvBytes bs) < 2 ^ (8 * sz) := by
        have h := Anneal.LeBytes.fromLeBytes_lt (extractInitBvBytes bs)
        rw [hexLen, Nat.mul_comm] at h
        exact h
      let x : BitVec (8 * sz) := BitVec.ofNat (8 * sz)
        (Anneal.LeBytes.fromLeBytes (extractInitBvBytes bs))
      have hdec : (bitVecLE sz hNz).decode bs = some x :=
        (bitVecLE_decode_eq_some_iff sz hNz bs x).2 ⟨hlen, hi, by
          show _ = (BitVec.ofNat (8 * sz) _).toNat
          rw [_root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx_lt]⟩
      have hswap : Anneal.LeBytes.fromLeBytes (extractInitBvBytes bs.reverse) =
          (Anneal.BitVecArith.bswapBytes sz x).toNat := by
        rw [extractInitBvBytes_reverse, toNat_bswapBytes_eq_fromBeBytes]
        have hx_nat : x.toNat = Anneal.LeBytes.fromLeBytes (extractInitBvBytes bs) := by
          show (BitVec.ofNat (8 * sz) _).toNat = _
          rw [_root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx_lt]
        rw [hx_nat]
        have haux := Anneal.LeBytes.toLeBytesAux_fromLeBytes (extractInitBvBytes bs)
        rw [hexLen] at haux
        rw [haux]
        rfl
      have hdec_rev : (bitVecLE sz hNz).decode bs.reverse =
          some (Anneal.BitVecArith.bswapBytes sz x) :=
        (bitVecLE_decode_eq_some_iff sz hNz bs.reverse _).2 ⟨hlen', hi', hswap⟩
      rw [hdec_rev, hdec]
      rfl

/-- Single unsigned scalar `encodeValueToBytes` agrees with `bitVecLE.encode`. -/
theorem encodeValueToBytes_bitVec_uint (layouts : LayoutTable) (w : UintTy) (idx : LayoutIdx)
    (x : BitVec (8 * MirValueCodec.uintByteSize w)) :
    encodeValueToBytes defaultCodecFuel layouts { kind := .uint w, layoutIdx := idx }
        (.scalar ⟨x.toNat, MirValueCodec.uintByteSize w⟩) =
      some ((bitVecLE (MirValueCodec.uintByteSize w)
        (MirValueCodec.uintByteSize_pos w)).encode x) := by
  cases w <;> rfl

/-- Single unsigned scalar `decodeValueFromBytes` agrees with `bitVecLE.decode`. -/
theorem decodeValueFromBytes_bitVec_uint (layouts : LayoutTable) (w : UintTy) (idx : LayoutIdx)
    (bs : List AbstractByte) :
    decodeValueFromBytes defaultCodecFuel layouts { kind := .uint w, layoutIdx := idx } bs =
      ((bitVecLE (MirValueCodec.uintByteSize w)
        (MirValueCodec.uintByteSize_pos w)).decode bs).map
          (fun x => Value.scalar ⟨x.toNat, MirValueCodec.uintByteSize w⟩) := by
  have h := (MirValueCodec.uint layouts w idx).decode_eq_map bs
  rw [h]
  show ((FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w)
      (MirValueCodec.uintByteSize_pos w)).decode bs).map _ =
    (((FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w)
      (MirValueCodec.uintByteSize_pos w)).decode bs).map _).map _
  cases (FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w)
      (MirValueCodec.uintByteSize_pos w)).decode bs <;> rfl

/-- Single signed scalar `encodeValueToBytes` agrees with `bitVecLE.encode` (using the same
two's-complement bit pattern). -/
theorem encodeValueToBytes_bitVec_int (layouts : LayoutTable) (w : IntTy) (idx : LayoutIdx)
    (x : BitVec (8 * MirValueCodec.intByteSize w)) :
    encodeValueToBytes defaultCodecFuel layouts { kind := .int w, layoutIdx := idx }
        (.scalar ⟨x.toNat, MirValueCodec.intByteSize w⟩) =
      some ((bitVecLE (MirValueCodec.intByteSize w)
        (MirValueCodec.intByteSize_pos w)).encode x) := by
  cases w <;> rfl

/-- Single signed scalar `decodeValueFromBytes` agrees with `bitVecLE.decode`. -/
theorem decodeValueFromBytes_bitVec_int (layouts : LayoutTable) (w : IntTy) (idx : LayoutIdx)
    (bs : List AbstractByte) :
    decodeValueFromBytes defaultCodecFuel layouts { kind := .int w, layoutIdx := idx } bs =
      ((bitVecLE (MirValueCodec.intByteSize w)
        (MirValueCodec.intByteSize_pos w)).decode bs).map
          (fun x => Value.scalar ⟨x.toNat, MirValueCodec.intByteSize w⟩) := by
  have h := (MirValueCodec.int layouts w idx).decode_eq_map bs
  rw [h]
  show ((FixedByteCodec.uintBitsLE (MirValueCodec.intByteSize w)
      (MirValueCodec.intByteSize_pos w)).decode bs).map _ =
    (((FixedByteCodec.uintBitsLE (MirValueCodec.intByteSize w)
      (MirValueCodec.intByteSize_pos w)).decode bs).map _).map _
  cases (FixedByteCodec.uintBitsLE (MirValueCodec.intByteSize w)
      (MirValueCodec.intByteSize_pos w)).decode bs <;> rfl

/-- `encodeValueToBytes` on any signed integer array `[iN; n]` given as bitvectors (including the
empty array `xs = []`) is the element-wise `bitVecLE` encoding. -/
theorem encodeValueToBytes_bitVecArray_int (layouts : LayoutTable) (w : IntTy) (idx : LayoutIdx)
    (xs : List (BitVec (8 * MirValueCodec.intByteSize w))) :
    encodeValueToBytes defaultCodecFuel layouts
        { kind := .array (.int w) xs.length, layoutIdx := idx }
        (bitVecArrayValue (MirValueCodec.intByteSize w) xs) =
      some ((bitVecLE (MirValueCodec.intByteSize w)
        (MirValueCodec.intByteSize_pos w)).encodeElems xs) := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    have hne : Nat.beq (y :: ys).length 0 = false := rfl
    have hlen : Nat.beq (Trusted.Sequence.length ((y :: ys).map
        (fun x => Value.scalar ⟨x.toNat, MirValueCodec.intByteSize w⟩))) (y :: ys).length = true := by
      rw [seqLength_eq, List.length_map]
      exact nat_beq_self _
    have hsz : rigidTyKindByteSize (.int w) = some (MirValueCodec.intByteSize w) := by
      cases w <;> rfl
    unfold defaultCodecFuel encodeValueToBytes bitVecArrayValue
    simp only [hne, hlen, hsz]
    exact FixedByteCodec.encodeListWith_map_eq_encodeElems
      (bitVecLE (MirValueCodec.intByteSize w) (MirValueCodec.intByteSize_pos w))
      (fun x => Value.scalar ⟨x.toNat, MirValueCodec.intByteSize w⟩)
      (fun e => encodeValueToBytes 15 layouts { kind := .int w, layoutIdx := 0 } e)
      (fun x => by cases w <;> rfl) (y :: ys)

/-- `decodeValueFromBytes` recovers any signed integer array `[iN; n]` (including `xs = []`) from
its element-wise `bitVecLE` encoding. -/
theorem decodeValueFromBytes_encodeElems_bitVecLE_int (layouts : LayoutTable) (w : IntTy)
    (idx : LayoutIdx) (xs : List (BitVec (8 * MirValueCodec.intByteSize w))) :
    decodeValueFromBytes defaultCodecFuel layouts
        { kind := .array (.int w) xs.length, layoutIdx := idx }
        ((bitVecLE (MirValueCodec.intByteSize w)
          (MirValueCodec.intByteSize_pos w)).encodeElems xs) =
      some (bitVecArrayValue (MirValueCodec.intByteSize w) xs) := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    let sz := MirValueCodec.intByteSize w
    let hNz := MirValueCodec.intByteSize_pos w
    let c := bitVecLE sz hNz
    have hne : Nat.beq (y :: ys).length 0 = false := rfl
    have hsz : rigidTyKindByteSize (.int w) = some sz := by cases w <;> rfl
    have hlen_eq : (c.encodeElems (y :: ys)).length = sz * (y :: ys).length := by
      rw [FixedByteCodec.length_encodeElems, Nat.mul_comm]
    have hbeq : Nat.beq (Trusted.Sequence.length (c.encodeElems (y :: ys)))
        (Nat.mul sz (y :: ys).length) = true := by
      rw [seqLength_eq, natMul_eq, hlen_eq]
      exact nat_beq_self _
    have hdecElem : ∀ x : BitVec (8 * sz),
        decodeValueFromBytes 15 layouts { kind := .int w, layoutIdx := 0 } (c.encode x) =
          some (Value.scalar ⟨x.toNat, sz⟩) := by
      intro x
      have h1 : decodeValueFromBytes 15 layouts { kind := .int w, layoutIdx := 0 } (c.encode x) =
          decodeValueFromBytes defaultCodecFuel layouts { kind := .int w, layoutIdx := 0 }
            (c.encode x) := by
        cases w <;> rfl
      rw [h1, decodeValueFromBytes_bitVec_int, c.decode_encode x]
      rfl
    have hchunks : decodeArrayChunksWith
        (fun ch => decodeValueFromBytes 15 layouts { kind := .int w, layoutIdx := 0 } ch)
        sz (y :: ys).length (c.encodeElems (y :: ys)) =
          some ((y :: ys).map (fun x => Value.scalar ⟨x.toNat, sz⟩)) := by
      rw [decodeArrayChunksWith_eq_some_iff _ hNz]
      refine ⟨FixedByteCodec.length_encodeElems c (y :: ys), ?_⟩
      rw [chunksOf_encodeElems c hNz, List.map_map, List.map_map]
      congr 1
      funext x
      exact hdecElem x
    unfold defaultCodecFuel decodeValueFromBytes bitVecArrayValue
    dsimp only
    rw [hne]
    dsimp only
    rw [hsz]
    dsimp only
    rw [hbeq]
    dsimp only
    rw [hchunks]

/-! ## 13. Checked/Unchecked Pure-to-Operational Bridges, Signed Subtraction Ranges and Typed Signed-Array Transmutes -/

/-- Exact characterization of signed addition overflow on the ported `msb`: the operands have
equal sign bits and the wrapped sum has the other one. Holds for arbitrary (possibly
non-canonical) bits and every byte width (including `sz = 0`). -/
theorem signedOverflowAdd_eq_msb (a b sz : Nat) :
    signedOverflowAdd a b sz =
      ((Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a) ==
          Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) b)) &&
        (Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a) !=
          Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a + BitVec.ofNat (8 * sz) b))) :=
  Anneal.Scalars.signedOverflowAdd_eq_msb a b sz

/-- Exact characterization of signed subtraction overflow on the ported `msb`: the operands
have different sign bits and the wrapped difference does not keep the minuend's. Holds for
arbitrary bits and every byte width (including `sz = 0`). -/
theorem signedOverflowSub_eq_msb (a b sz : Nat) :
    signedOverflowSub a b sz =
      ((Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a) !=
          Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) b)) &&
        (Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a) !=
          Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a - BitVec.ofNat (8 * sz) b))) :=
  Anneal.Scalars.signedOverflowSub_eq_msb a b sz

/-- Signed subtraction cannot overflow when the operands have the same sign bit. -/
theorem signedOverflowSub_eq_false_of_msb_eq {a b sz : Nat}
    (h : Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a) =
      Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) b)) :
    signedOverflowSub a b sz = false := by
  rw [signedOverflowSub_eq_msb, h]
  cases Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) b) <;> rfl

/-- Signed addition cannot overflow when the operands have different sign bits. -/
theorem signedOverflowAdd_eq_false_of_msb_ne {a b sz : Nat}
    (h : Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a) ≠
      Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) b)) :
    signedOverflowAdd a b sz = false := by
  rw [signedOverflowAdd_eq_msb]
  cases ha : Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a) <;>
    cases hb : Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) b) <;>
    first
      | rfl
      | exact absurd (ha.trans hb.symm) h

/-- Modulo reduction when `x < 2 * m`: either `x` itself or `x - m`. -/
theorem mod_of_lt_two_mul {x m : Nat} (h : x < 2 * m) :
    x % m = if x < m then x else x - m := by
  cases Nat.lt_or_ge x m with
  | inl hlt =>
    simp only [hlt, ↓reduceIte]
    exact Nat.mod_eq_of_lt hlt
  | inr hge =>
    have hnlt : ¬ x < m := Nat.not_lt_of_ge hge
    simp only [hnlt, ↓reduceIte]
    have hsplit : x = (x - m) + m := (Nat.sub_add_cancel hge).symm
    have hsub_lt : x - m < m := by omega
    conv => lhs; rw [hsplit]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hsub_lt]

/-- Piecewise linear relation between `x.toNat` and the ported `signedKey x` for positive bit
widths. -/
theorem signedKey_linear {w : Nat} (hw : 0 < w) (x : BitVec w) :
    (Anneal.BitVecArith.signedKey x < 2 ^ (w - 1) ∧
        x.toNat = Anneal.BitVecArith.signedKey x + 2 ^ (w - 1)) ∨
      (2 ^ (w - 1) ≤ Anneal.BitVecArith.signedKey x ∧
        Anneal.BitVecArith.signedKey x < 2 ^ w ∧
        x.toNat = Anneal.BitVecArith.signedKey x - 2 ^ (w - 1)) := by
  cases hm : Anneal.BitVecArith.msb x with
  | true =>
    left
    have hk := Anneal.BitVecArith.signedKey_eq_of_msb_true hw hm
    have hlt := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hm
    have hge := (Anneal.BitVecArith.msb_eq_true_iff hw x).1 hm
    rw [natPow_eq] at hk hlt hge
    exact ⟨hlt, by omega⟩
  | false =>
    right
    have hk := Anneal.BitVecArith.signedKey_eq_of_msb_false hw hm
    have hge := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hm
    have hlt := Anneal.BitVecArith.signedKey_lt x
    rw [natPow_eq] at hk hge hlt
    exact ⟨hge, hlt, by omega⟩

/-- Exact `signedKey` of overflow-free and underflow-free signed subtraction
(`signedKey b ≤ signedKey a + 2^(w - 1)` and `signedKey a < signedKey b + 2^(w - 1)`). -/
theorem signedKey_sub_no_overflow {w : Nat} (hw : 0 < w) {a b : BitVec w}
    (hno_udf : Anneal.BitVecArith.signedKey b ≤
      Anneal.BitVecArith.signedKey a + 2 ^ (w - 1))
    (hno_ovf : Anneal.BitVecArith.signedKey a <
      Anneal.BitVecArith.signedKey b + 2 ^ (w - 1)) :
    Anneal.BitVecArith.signedKey (a - b) =
      Anneal.BitVecArith.signedKey a + 2 ^ (w - 1) - Anneal.BitVecArith.signedKey b := by
  have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
    cases w with
    | zero => omega
    | succ k =>
      change 2 ^ (k + 1) = 2 * 2 ^ k
      rw [Nat.pow_succ, Nat.mul_comm]
  have ha_lt : a.toNat < 2 ^ w := a.isLt
  have hb_lt : b.toNat < 2 ^ w := b.isLt
  have hsub_toNat : (a - b).toNat =
      if 2 ^ w - b.toNat + a.toNat < 2 ^ w then 2 ^ w - b.toNat + a.toNat
      else 2 ^ w - b.toNat + a.toNat - 2 ^ w := by
    rw [_root_.BitVec.toNat_sub]
    exact mod_of_lt_two_mul (by omega)
  rcases signedKey_linear hw a with ⟨hka, ha_eq⟩ | ⟨hka1, hka2, ha_eq⟩ <;>
    rcases signedKey_linear hw b with ⟨hkb, hb_eq⟩ | ⟨hkb1, hkb2, hb_eq⟩ <;>
    rcases signedKey_linear hw (a - b) with ⟨hkd, hd_eq⟩ | ⟨hkd1, hkd2, hd_eq⟩ <;>
    · rw [hd_eq] at hsub_toNat
      split at hsub_toNat <;> omega

/-- Soundness of signed interval subtraction when neither signed underflow
(`signedKey smax₂ ≤ signedKey smin₁ + 2^(w - 1)`) nor signed overflow
(`signedKey smax₁ < signedKey smin₂ + 2^(w - 1)`) occurs; holds at every width `w` (including
`w = 0`). -/
theorem signed_range_sub_no_overflow_sound {w : Nat}
    {smin₁ x smax₁ smin₂ y smax₂ : BitVec w}
    (hlo₁ : Anneal.BitVecArith.sle smin₁ x) (hhi₁ : Anneal.BitVecArith.sle x smax₁)
    (hlo₂ : Anneal.BitVecArith.sle smin₂ y) (hhi₂ : Anneal.BitVecArith.sle y smax₂)
    (hno_udf : Anneal.BitVecArith.signedKey smax₂ ≤
      Anneal.BitVecArith.signedKey smin₁ + 2 ^ (w - 1))
    (hno_ovf : Anneal.BitVecArith.signedKey smax₁ <
      Anneal.BitVecArith.signedKey smin₂ + 2 ^ (w - 1)) :
    Anneal.BitVecArith.sle (smin₁ - smax₂) (x - y) ∧
      Anneal.BitVecArith.sle (x - y) (smax₁ - smin₂) := by
  cases w with
  | zero =>
    unfold Anneal.BitVecArith.sle
    have h1 := Anneal.BitVecArith.signedKey_lt (smin₁ - smax₂)
    have h2 := Anneal.BitVecArith.signedKey_lt (x - y)
    have h3 := Anneal.BitVecArith.signedKey_lt (smax₁ - smin₂)
    rw [natPow_eq] at h1 h2 h3
    exact ⟨by omega, by omega⟩
  | succ w' =>
    have hw : 0 < w' + 1 := Nat.succ_pos w'
    unfold Anneal.BitVecArith.sle at hlo₁ hhi₁ hlo₂ hhi₂ ⊢
    rw [signedKey_sub_no_overflow hw hno_udf (by omega),
      signedKey_sub_no_overflow hw (by omega) (by omega),
      signedKey_sub_no_overflow hw (by omega) hno_ovf]
    exact ⟨by omega, by omega⟩

/-- `signedOverflowSub` is `false` whenever the ported `signedKey` difference stays within the
two's-complement no-underflow / no-overflow window (holds for arbitrary, possibly non-canonical
`a` and `b`). -/
theorem signedOverflowSub_eq_false_of_signedKey_bounds {sz : Nat} (hsz : 0 < sz) (a b : Nat)
    (hno_udf : Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) b) ≤
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) a) + 2 ^ (8 * sz - 1))
    (hno_ovf : Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) a) <
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) b) + 2 ^ (8 * sz - 1)) :
    signedOverflowSub a b sz = false := by
  have hw : 0 < 8 * sz := by omega
  have hdiff := signedKey_sub_no_overflow hw
    (a := BitVec.ofNat (8 * sz) a) (b := BitVec.ofNat (8 * sz) b) hno_udf hno_ovf
  rw [signedOverflowSub_eq_msb, msb_eq_core, msb_eq_core, msb_eq_core]
  cases ha : (BitVec.ofNat (8 * sz) a).msb with
  | false =>
    cases hb : (BitVec.ofNat (8 * sz) b).msb with
    | false => rfl
    | true =>
      have hka := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw ha
      have hkb := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hb
      rw [natPow_eq] at hka hkb
      cases hd : (BitVec.ofNat (8 * sz) a - BitVec.ofNat (8 * sz) b).msb with
      | false => rfl
      | true =>
        have hkd := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hd
        rw [natPow_eq] at hkd
        omega
  | true =>
    cases hb : (BitVec.ofNat (8 * sz) b).msb with
    | true => rfl
    | false =>
      have hka := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw ha
      have hkb := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hb
      rw [natPow_eq] at hka hkb
      cases hd : (BitVec.ofNat (8 * sz) a - BitVec.ofNat (8 * sz) b).msb with
      | true => rfl
      | false =>
        have hkd := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hd
        rw [natPow_eq] at hkd
        omega

/-- Signed interval transfer through `evalBinOp .sub` when neither signed underflow nor signed
overflow can occur. -/
theorem scalarSRange_evalBinOp_sub_no_overflow {sz : Nat} (hsz : 0 < sz)
    {smin₁ smax₁ smin₂ smax₂ : BitVec (8 * sz)} {x y : ScalarInt} (isSigned : Bool)
    (hx : ScalarSRange sz smin₁ smax₁ x) (hy : ScalarSRange sz smin₂ smax₂ y)
    (hno_udf : Anneal.BitVecArith.signedKey smax₂ ≤
      Anneal.BitVecArith.signedKey smin₁ + 2 ^ (8 * sz - 1))
    (hno_ovf : Anneal.BitVecArith.signedKey smax₁ <
      Anneal.BitVecArith.signedKey smin₂ + 2 ^ (8 * sz - 1)) :
    ∃ r, Anneal.Scalars.evalBinOp .sub x y isSigned = some r ∧
      ScalarSRange sz (smin₁ - smax₂) (smax₁ - smin₂) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarSRange_exists hy
  have hs := signed_range_sub_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno_udf hno_ovf
  exact ⟨_, evalBinOp_sub_eq_sub hsz xb yb isSigned, scalarSRange_of_bitVec _ hs.1 hs.2⟩

/-- Signed interval transfer through `evalWrappingSub` when neither signed underflow nor signed
overflow can occur. -/
theorem scalarSRange_evalWrappingSub_no_overflow {sz : Nat} (hsz : 0 < sz)
    {smin₁ smax₁ smin₂ smax₂ : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarSRange sz smin₁ smax₁ x) (hy : ScalarSRange sz smin₂ smax₂ y)
    (hno_udf : Anneal.BitVecArith.signedKey smax₂ ≤
      Anneal.BitVecArith.signedKey smin₁ + 2 ^ (8 * sz - 1))
    (hno_ovf : Anneal.BitVecArith.signedKey smax₁ <
      Anneal.BitVecArith.signedKey smin₂ + 2 ^ (8 * sz - 1)) :
    ∃ r, evalWrappingSub x y = some r ∧
      ScalarSRange sz (smin₁ - smax₂) (smax₁ - smin₂) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarSRange_exists hy
  have hs := signed_range_sub_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno_udf hno_ovf
  exact ⟨_, evalWrappingSub_eq_sub hsz xb yb, scalarSRange_of_bitVec _ hs.1 hs.2⟩

/-- Operational signed interval transfer through `Trusted` `evalScalarBinOp .sub`. -/
theorem scalarSRange_evalScalarBinOp_sub_no_overflow {sz : Nat} (hsz : 0 < sz)
    {smin₁ smax₁ smin₂ smax₂ : BitVec (8 * sz)} {x y : ScalarInt}
    (locals : List LocalSlot) (mem : Memory) (isSigned : Bool)
    (hx : ScalarSRange sz smin₁ smax₁ x) (hy : ScalarSRange sz smin₂ smax₂ y)
    (hno_udf : Anneal.BitVecArith.signedKey smax₂ ≤
      Anneal.BitVecArith.signedKey smin₁ + 2 ^ (8 * sz - 1))
    (hno_ovf : Anneal.BitVecArith.signedKey smax₁ <
      Anneal.BitVecArith.signedKey smin₂ + 2 ^ (8 * sz - 1)) :
    ∃ r, evalScalarBinOp .sub x y locals mem isSigned = .ok (.scalar r) locals mem ∧
      ScalarSRange sz (smin₁ - smax₂) (smax₁ - smin₂) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarSRange_exists hy
  have hs := signed_range_sub_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno_udf hno_ovf
  exact ⟨_, evalScalarBinOp_sub_eq_sub hsz xb yb locals mem isSigned,
    scalarSRange_of_bitVec _ hs.1 hs.2⟩

/-- Operational signed `subUnchecked`: when the `ScalarSRange` endpoints satisfy the
no-underflow and no-overflow bounds, `evalScalarBinOp` never hits `.ub` and returns a scalar in
`[smin₁ - smax₂, smax₁ - smin₂]`. -/
theorem scalarSRange_evalScalarBinOp_subUnchecked_signed {sz : Nat} (hsz : 0 < sz)
    {smin₁ smax₁ smin₂ smax₂ : BitVec (8 * sz)} {x y : ScalarInt}
    (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarSRange sz smin₁ smax₁ x) (hy : ScalarSRange sz smin₂ smax₂ y)
    (hno_udf : Anneal.BitVecArith.signedKey smax₂ ≤
      Anneal.BitVecArith.signedKey smin₁ + 2 ^ (8 * sz - 1))
    (hno_ovf : Anneal.BitVecArith.signedKey smax₁ <
      Anneal.BitVecArith.signedKey smin₂ + 2 ^ (8 * sz - 1)) :
    ∃ r, evalScalarBinOp .subUnchecked x y locals mem true = .ok (.scalar r) locals mem ∧
      ScalarSRange sz (smin₁ - smax₂) (smax₁ - smin₂) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarSRange_exists hy
  have hlo₁' : Anneal.BitVecArith.signedKey smin₁ ≤
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) xb) := hx₁
  have hhi₁' : Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) xb) ≤
      Anneal.BitVecArith.signedKey smax₁ := hx₂
  have hlo₂' : Anneal.BitVecArith.signedKey smin₂ ≤
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) yb) := hy₁
  have hhi₂' : Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) yb) ≤
      Anneal.BitVecArith.signedKey smax₂ := hy₂
  have hovf : signedOverflowSub xb yb sz = false :=
    signedOverflowSub_eq_false_of_signedKey_bounds hsz xb yb (by omega) (by omega)
  have hs := signed_range_sub_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno_udf hno_ovf
  refine ⟨⟨(BitVec.ofNat (8 * sz) xb - BitVec.ofNat (8 * sz) yb).toNat, sz⟩, ?_,
    scalarSRange_of_bitVec _ hs.1 hs.2⟩
  rw [Anneal.Scalars.evalScalarBinOp_subUnchecked_signed hsz, hovf, sub_mod_eq_toNat_sub]

/-- Operational signed `subWithOverflow`: when the `ScalarSRange` endpoints satisfy the
no-underflow and no-overflow bounds, the overflow flag is `false` (`0`) and the difference lies
in `[smin₁ - smax₂, smax₁ - smin₂]`. -/
theorem scalarSRange_evalScalarBinOp_subWithOverflow_signed {sz : Nat} (hsz : 0 < sz)
    {smin₁ smax₁ smin₂ smax₂ : BitVec (8 * sz)} {x y : ScalarInt}
    (locals : List LocalSlot) (mem : Memory)
    (hx : ScalarSRange sz smin₁ smax₁ x) (hy : ScalarSRange sz smin₂ smax₂ y)
    (hno_udf : Anneal.BitVecArith.signedKey smax₂ ≤
      Anneal.BitVecArith.signedKey smin₁ + 2 ^ (8 * sz - 1))
    (hno_ovf : Anneal.BitVecArith.signedKey smax₁ <
      Anneal.BitVecArith.signedKey smin₂ + 2 ^ (8 * sz - 1)) :
    ∃ r, evalScalarBinOp .subWithOverflow x y locals mem true =
        .ok (.aggregate 0 [.scalar r, .scalar (boolToScalar false)]) locals mem ∧
      ScalarSRange sz (smin₁ - smax₂) (smax₁ - smin₂) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, _, hy₁, hy₂⟩ := scalarSRange_exists hy
  have hlo₁' : Anneal.BitVecArith.signedKey smin₁ ≤
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) xb) := hx₁
  have hhi₁' : Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) xb) ≤
      Anneal.BitVecArith.signedKey smax₁ := hx₂
  have hlo₂' : Anneal.BitVecArith.signedKey smin₂ ≤
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) yb) := hy₁
  have hhi₂' : Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) yb) ≤
      Anneal.BitVecArith.signedKey smax₂ := hy₂
  have hovf : signedOverflowSub xb yb sz = false :=
    signedOverflowSub_eq_false_of_signedKey_bounds hsz xb yb (by omega) (by omega)
  have hs := signed_range_sub_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno_udf hno_ovf
  refine ⟨⟨(BitVec.ofNat (8 * sz) xb - BitVec.ofNat (8 * sz) yb).toNat, sz⟩, ?_,
    scalarSRange_of_bitVec _ hs.1 hs.2⟩
  rw [Anneal.Scalars.evalScalarBinOp_subWithOverflow hsz, hovf, sub_mod_eq_toNat_sub]
  rfl

/-- Exact failure characterization of `Anneal.Scalars.evalBinOpChecked`: it returns `none` iff the
operands are zero-width, mismatched in byte width, or the operator is outside the six checked
arithmetic variants. -/
theorem evalBinOpChecked_eq_none_iff (op : BinOp) (lhs rhs : ScalarInt) (isSigned : Bool) :
    Anneal.Scalars.evalBinOpChecked op lhs rhs isSigned = none ↔
      lhs.sizeBytes = 0 ∨ lhs.sizeBytes ≠ rhs.sizeBytes ∨
        ¬ (op = .add ∨ op = .addWithOverflow ∨ op = .sub ∨ op = .subWithOverflow ∨
          op = .mul ∨ op = .mulWithOverflow) := by
  unfold Anneal.Scalars.evalBinOpChecked
  cases h0 : Nat.beq lhs.sizeBytes 0 with
  | true =>
    rw [Bool.true_or]
    exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h0), fun _ => rfl⟩
  | false =>
    have hnz : lhs.sizeBytes ≠ 0 := fun h => by rw [h] at h0; nomatch h0
    cases heq : Nat.beq lhs.sizeBytes rhs.sizeBytes with
    | false =>
      have hne : lhs.sizeBytes ≠ rhs.sizeBytes := fun h => by
        rw [h, Nat.beq_refl] at heq; nomatch heq
      rw [Bool.false_or, Bool.not_false]
      exact ⟨fun _ => Or.inr (Or.inl hne), fun _ => rfl⟩
    | true =>
      have hsz_eq : lhs.sizeBytes = rhs.sizeBytes := Nat.eq_of_beq_eq_true heq
      rw [Bool.false_or, Bool.not_true]
      dsimp only
      refine ⟨fun h => Or.inr (Or.inr (fun hop => ?_)), fun h => ?_⟩
      · rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
        · cases h
        · cases h
        · cases isSigned with
          | false => cases hb : Nat.ble rhs.bits lhs.bits <;> rw [hb] at h <;> cases h
          | true => cases h
        · cases isSigned with
          | false => cases hb : Nat.ble rhs.bits lhs.bits <;> rw [hb] at h <;> cases h
          | true => cases h
        · cases h
        · cases h
      · rcases h with hz | hne | hnot
        · exact absurd hz hnz
        · exact absurd hsz_eq hne
        · cases op <;> first | rfl | exact absurd (by simp) hnot

/-- `evalBinOpChecked` identifies `.addWithOverflow` with `.add` on arbitrary scalars. -/
theorem evalBinOpChecked_addWithOverflow_eq_add (lhs rhs : ScalarInt) (isSigned : Bool) :
    Anneal.Scalars.evalBinOpChecked .addWithOverflow lhs rhs isSigned =
      Anneal.Scalars.evalBinOpChecked .add lhs rhs isSigned := rfl

/-- `evalBinOpChecked` identifies `.subWithOverflow` with `.sub` on arbitrary scalars. -/
theorem evalBinOpChecked_subWithOverflow_eq_sub (lhs rhs : ScalarInt) (isSigned : Bool) :
    Anneal.Scalars.evalBinOpChecked .subWithOverflow lhs rhs isSigned =
      Anneal.Scalars.evalBinOpChecked .sub lhs rhs isSigned := rfl

/-- `evalBinOpChecked` identifies `.mulWithOverflow` with `.mul` on arbitrary scalars. -/
theorem evalBinOpChecked_mulWithOverflow_eq_mul (lhs rhs : ScalarInt) (isSigned : Bool) :
    Anneal.Scalars.evalBinOpChecked .mulWithOverflow lhs rhs isSigned =
      Anneal.Scalars.evalBinOpChecked .mul lhs rhs isSigned := rfl

/-- Signed `evalBinOpChecked .add`: the wrapped `BitVec` sum together with the exact overflow
flag on the ported `msb` (arbitrary bits). -/
theorem evalBinOpChecked_add_signed_eq {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    Anneal.Scalars.evalBinOpChecked .add ⟨a, sz⟩ ⟨b, sz⟩ true =
      some (⟨(BitVec.ofNat (8 * sz) a + BitVec.ofNat (8 * sz) b).toNat, sz⟩,
        (Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a) ==
            Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) b)) &&
          (Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a) !=
            Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a + BitVec.ofNat (8 * sz) b))) := by
  rw [Anneal.Scalars.evalBinOpChecked_add_apply hsz, add_mod_eq_toNat_add,
    ← signedOverflowAdd_eq_msb]

/-- Unsigned `evalBinOpChecked .add`: the wrapped `BitVec` sum together with the carry-out of
the raw operand bits. -/
theorem evalBinOpChecked_add_unsigned_eq {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    Anneal.Scalars.evalBinOpChecked .add ⟨a, sz⟩ ⟨b, sz⟩ false =
      some (⟨(BitVec.ofNat (8 * sz) a + BitVec.ofNat (8 * sz) b).toNat, sz⟩,
        Nat.ble (2 ^ (8 * sz)) (a + b)) := by
  rw [Anneal.Scalars.evalBinOpChecked_add_apply hsz, add_mod_eq_toNat_add]

/-- Signed `evalBinOpChecked .sub`: the wrapped `BitVec` difference together with the exact
overflow flag on the ported `msb` (arbitrary bits). -/
theorem evalBinOpChecked_sub_signed_eq {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    Anneal.Scalars.evalBinOpChecked .sub ⟨a, sz⟩ ⟨b, sz⟩ true =
      some (⟨(BitVec.ofNat (8 * sz) a - BitVec.ofNat (8 * sz) b).toNat, sz⟩,
        (Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a) !=
            Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) b)) &&
          (Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a) !=
            Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) a - BitVec.ofNat (8 * sz) b))) := by
  rw [Anneal.Scalars.evalBinOpChecked_sub_apply hsz, sub_mod_eq_toNat_sub,
    ← signedOverflowSub_eq_msb]

/-- Unsigned `evalBinOpChecked .sub`: the wrapped `BitVec` difference together with the
borrow of the raw operand bits. -/
theorem evalBinOpChecked_sub_unsigned_eq {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    Anneal.Scalars.evalBinOpChecked .sub ⟨a, sz⟩ ⟨b, sz⟩ false =
      some (⟨(BitVec.ofNat (8 * sz) a - BitVec.ofNat (8 * sz) b).toNat, sz⟩,
        Bool.not (Nat.ble b a)) := by
  rw [Anneal.Scalars.evalBinOpChecked_sub_apply hsz, sub_mod_eq_toNat_sub]

/-- Signed `evalBinOpChecked .mul`: the wrapped ported `BitVec.mul` product together with
`signedOverflowMul` (arbitrary bits). -/
theorem evalBinOpChecked_mul_signed_eq {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    Anneal.Scalars.evalBinOpChecked .mul ⟨a, sz⟩ ⟨b, sz⟩ true =
      some (⟨(Anneal.BitVec.mul (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)).toNat, sz⟩,
        signedOverflowMul a b sz) := by
  rw [Anneal.Scalars.evalBinOpChecked_mul_apply hsz, mul_mod_eq_toNat_mul]

/-- Unsigned `evalBinOpChecked .mul`: the wrapped ported `BitVec.mul` product together with the
overflow flag of the raw product. -/
theorem evalBinOpChecked_mul_unsigned_eq {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    Anneal.Scalars.evalBinOpChecked .mul ⟨a, sz⟩ ⟨b, sz⟩ false =
      some (⟨(Anneal.BitVec.mul (BitVec.ofNat (8 * sz) a) (BitVec.ofNat (8 * sz) b)).toNat, sz⟩,
        Nat.ble (2 ^ (8 * sz)) (a * b)) := by
  rw [Anneal.Scalars.evalBinOpChecked_mul_apply hsz, mul_mod_eq_toNat_mul]

/-- For `.add`, `.sub` and `.mul`, the value component of `evalBinOpChecked` agrees identically
with the wrapping `evalBinOp` result (on arbitrary same-width or mismatched/zero-width scalars). -/
theorem evalBinOpChecked_fst_eq_evalBinOp {op : BinOp}
    (hop : op = .add ∨ op = .sub ∨ op = .mul) (lhs rhs : ScalarInt) (isSigned : Bool) :
    (Anneal.Scalars.evalBinOpChecked op lhs rhs isSigned).map Prod.fst =
      Anneal.Scalars.evalBinOp op lhs rhs isSigned := by
  cases lhs with
  | mk a sx =>
    cases rhs with
    | mk b sy =>
      cases h0 : Nat.beq sx 0 with
      | true =>
        have hz : sx = 0 := Nat.eq_of_beq_eq_true h0
        subst hz
        rcases hop with rfl | rfl | rfl <;> rfl
      | false =>
        have hpos : 0 < sx := by
          cases sx with
          | zero => nomatch h0
          | succ k => exact Nat.succ_pos k
        cases heq : Nat.beq sx sy with
        | false =>
          rcases hop with rfl | rfl | rfl <;>
            · unfold Anneal.Scalars.evalBinOpChecked Anneal.Scalars.evalBinOp
              simp [h0, heq]
        | true =>
          have hsy : sy = sx := (Nat.eq_of_beq_eq_true heq).symm
          subst hsy
          rcases hop with rfl | rfl | rfl
          · rw [Anneal.Scalars.evalBinOpChecked_add_apply hpos,
              Anneal.Scalars.evalBinOp_add_apply hpos]; rfl
          · rw [Anneal.Scalars.evalBinOpChecked_sub_apply hpos,
              Anneal.Scalars.evalBinOp_sub_apply hpos]; rfl
          · rw [Anneal.Scalars.evalBinOpChecked_mul_apply hpos,
              Anneal.Scalars.evalBinOp_mul_apply hpos]; rfl

/-- Unconditional operational correspondence between pure `evalBinOpChecked` and `Trusted`
`evalScalarBinOp` on `.addWithOverflow`, `.subWithOverflow`, and `.mulWithOverflow`: for every
`0 < sz`, `a, b : Nat`, and `isSigned : Bool`, both evaluators return the identical `(r, ovf)`
pair (packaged operationally as `.aggregate 0 [.scalar r, .scalar (boolToScalar ovf)]`). -/
theorem evalScalarBinOp_withOverflow_of_evalBinOpChecked {sz : Nat} (hsz : 0 < sz) {op : BinOp}
    (hop : op = .addWithOverflow ∨ op = .subWithOverflow ∨ op = .mulWithOverflow)
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    ∃ r ovf, Anneal.Scalars.evalBinOpChecked op ⟨a, sz⟩ ⟨b, sz⟩ isSigned = some (r, ovf) ∧
      evalScalarBinOp op ⟨a, sz⟩ ⟨b, sz⟩ locals mem isSigned =
        .ok (.aggregate 0 [.scalar r, .scalar (boolToScalar ovf)]) locals mem := by
  rcases hop with rfl | rfl | rfl
  · refine ⟨_, _, Anneal.Scalars.evalBinOpChecked_addWithOverflow_apply hsz isSigned, ?_⟩
    rw [Anneal.Scalars.evalScalarBinOp_addWithOverflow hsz]
    cases isSigned with
    | false => cases Nat.ble (2 ^ (8 * sz)) (a + b) <;> rfl
    | true => cases signedOverflowAdd a b sz <;> rfl
  · refine ⟨_, _, Anneal.Scalars.evalBinOpChecked_subWithOverflow_apply hsz isSigned, ?_⟩
    rw [Anneal.Scalars.evalScalarBinOp_subWithOverflow hsz]
    cases isSigned with
    | false => cases Nat.ble b a <;> rfl
    | true => cases signedOverflowSub a b sz <;> rfl
  · refine ⟨_, _, Anneal.Scalars.evalBinOpChecked_mulWithOverflow_apply hsz isSigned, ?_⟩
    rw [Anneal.Scalars.evalScalarBinOp_mulWithOverflow hsz]
    cases isSigned with
    | false => cases Nat.ble (2 ^ (8 * sz)) (a * b) <;> rfl
    | true => cases signedOverflowMul a b sz <;> rfl

/-- Exact biconditional operational equivalence for unchecked arithmetic (`.addUnchecked`,
`.subUnchecked`, `.mulUnchecked`) on positive same-width scalars: `evalBinOp` returns `some r`
iff `evalScalarBinOp` returns `.ok (.scalar r)`, and `evalBinOp` returns `none` iff
`evalScalarBinOp` triggers `.ub`. -/
theorem evalScalarBinOp_unchecked_arith_iff {sz : Nat} (hsz : 0 < sz) {op : BinOp}
    (hop : op = .addUnchecked ∨ op = .subUnchecked ∨ op = .mulUnchecked)
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    (∀ r, Anneal.Scalars.evalBinOp op ⟨a, sz⟩ ⟨b, sz⟩ isSigned = some r ↔
        evalScalarBinOp op ⟨a, sz⟩ ⟨b, sz⟩ locals mem isSigned = .ok (.scalar r) locals mem) ∧
      (Anneal.Scalars.evalBinOp op ⟨a, sz⟩ ⟨b, sz⟩ isSigned = none ↔
        evalScalarBinOp op ⟨a, sz⟩ ⟨b, sz⟩ locals mem isSigned = .ub) := by
  rcases hop with rfl | rfl | rfl
  · cases isSigned with
    | false =>
      rw [Anneal.Scalars.evalBinOp_addUnchecked_apply_unsigned hsz,
        Anneal.Scalars.evalScalarBinOp_addUnchecked_unsigned hsz]
      cases Nat.ble (2 ^ (8 * sz)) (a + b) <;> simp
    | true =>
      rw [Anneal.Scalars.evalBinOp_addUnchecked_apply_signed hsz,
        Anneal.Scalars.evalScalarBinOp_addUnchecked_signed hsz]
      cases signedOverflowAdd a b sz <;> simp
  · cases isSigned with
    | false =>
      rw [Anneal.Scalars.evalBinOp_subUnchecked_apply_unsigned hsz,
        Anneal.Scalars.evalScalarBinOp_subUnchecked_unsigned hsz]
      by_cases hba : b ≤ a
      · simp only [hba, ↓reduceDIte]
        cases Nat.ble (2 ^ (8 * sz)) (a - b) <;> simp
      · simp [hba]
    | true =>
      rw [Anneal.Scalars.evalBinOp_subUnchecked_apply_signed hsz,
        Anneal.Scalars.evalScalarBinOp_subUnchecked_signed hsz]
      cases signedOverflowSub a b sz <;> simp
  · cases isSigned with
    | false =>
      rw [Anneal.Scalars.evalBinOp_mulUnchecked_apply_unsigned hsz,
        Anneal.Scalars.evalScalarBinOp_mulUnchecked_unsigned hsz]
      cases Nat.ble (2 ^ (8 * sz)) (a * b) <;> simp
    | true =>
      rw [Anneal.Scalars.evalBinOp_mulUnchecked_apply_signed hsz,
        Anneal.Scalars.evalScalarBinOp_mulUnchecked_signed hsz]
      cases signedOverflowMul a b sz <;> simp

/-- Exact biconditional operational equivalence for unchecked shifts (`.shlUnchecked`,
`.shrUnchecked`) on positive-width scalars: `evalBinOp` returns `some r` iff `evalScalarBinOp`
returns `.ok (.scalar r)`, and `evalBinOp` returns `none` iff `evalScalarBinOp` triggers `.ub`. -/
theorem evalScalarBinOp_unchecked_shift_iff {szL szR : Nat} (hszL : 0 < szL) (hszR : 0 < szR)
    {op : BinOp} (hop : op = .shlUnchecked ∨ op = .shrUnchecked)
    (a b : Nat) (locals : List LocalSlot) (mem : Memory) (isSigned : Bool) :
    (∀ r, Anneal.Scalars.evalBinOp op ⟨a, szL⟩ ⟨b, szR⟩ isSigned = some r ↔
        evalScalarBinOp op ⟨a, szL⟩ ⟨b, szR⟩ locals mem isSigned = .ok (.scalar r) locals mem) ∧
      (Anneal.Scalars.evalBinOp op ⟨a, szL⟩ ⟨b, szR⟩ isSigned = none ↔
        evalScalarBinOp op ⟨a, szL⟩ ⟨b, szR⟩ locals mem isSigned = .ub) := by
  cases Nat.lt_or_ge b (8 * szL) with
  | inl hb =>
    rcases hop with rfl | rfl
    · rw [Anneal.Scalars.evalBinOp_shlUnchecked_apply hszL hszR hb,
        Anneal.Scalars.evalScalarBinOp_shlUnchecked hszL hszR hb]
      simp
    · cases isSigned with
      | false =>
        rw [Anneal.Scalars.evalBinOp_shrUnchecked_unsigned hszL hszR hb,
          Anneal.Scalars.evalScalarBinOp_shrUnchecked_unsigned hszL hszR hb]
        simp
      | true =>
        rw [Anneal.Scalars.evalBinOp_shrUnchecked_signed hszL hszR hb,
          Anneal.Scalars.evalScalarBinOp_shrUnchecked_signed hszL hszR hb]
        simp
  | inr hb =>
    rcases hop with rfl | rfl
    · rw [Anneal.Scalars.evalBinOp_shlUnchecked_of_ge hszL hszR hb,
        Anneal.Scalars.evalScalarBinOp_shlUnchecked_of_ge hszL hszR hb]
      simp
    · rw [Anneal.Scalars.evalBinOp_shrUnchecked_of_ge hszL hszR hb,
        Anneal.Scalars.evalScalarBinOp_shrUnchecked_of_ge hszL hszR hb]
      simp

/-- Typed transmutation of signed bitvector arrays (`[iA; xs.length] → [iB; n₂]`, including
`xs = []`) whenever the byte sizes agree. -/
theorem bitVecArray_int_transmute_sound (layouts : LayoutTable) (w₁ w₂ : IntTy) (n₂ : Nat)
    (idx₁ idx₂ : LayoutIdx) (xs : List (BitVec (8 * MirValueCodec.intByteSize w₁)))
    (hsize : MirValueCodec.intByteSize w₁ * xs.length = MirValueCodec.intByteSize w₂ * n₂) :
    ∃ v', decodeValueFromBytes defaultCodecFuel layouts
      { kind := .array (.int w₂) n₂, layoutIdx := idx₂ }
      ((bitVecLE (MirValueCodec.intByteSize w₁)
        (MirValueCodec.intByteSize_pos w₁)).encodeElems xs) = some v' :=
  array_int_transmute_sound layouts w₁ w₂ xs.length n₂ idx₁ idx₂ hsize _ _
    (encodeValueToBytes_bitVecArray_int layouts w₁ idx₁ xs)

/-- Typed unsigned-to-signed bitvector array transmutation (`[uA; xs.length] → [iB; n₂]`,
including `xs = []`) whenever the byte sizes agree. -/
theorem bitVecArray_uint_to_int_transmute_sound (layouts : LayoutTable) (w₁ : UintTy) (w₂ : IntTy)
    (n₂ : Nat) (idx₁ idx₂ : LayoutIdx) (xs : List (BitVec (8 * MirValueCodec.uintByteSize w₁)))
    (hsize : MirValueCodec.uintByteSize w₁ * xs.length = MirValueCodec.intByteSize w₂ * n₂) :
    ∃ v', decodeValueFromBytes defaultCodecFuel layouts
      { kind := .array (.int w₂) n₂, layoutIdx := idx₂ }
      ((bitVecLE (MirValueCodec.uintByteSize w₁)
        (MirValueCodec.uintByteSize_pos w₁)).encodeElems xs) = some v' :=
  array_uint_to_int_transmute_sound layouts w₁ w₂ xs.length n₂ idx₁ idx₂ hsize _ _
    (encodeValueToBytes_bitVecArray layouts w₁ idx₁ xs)

/-- Typed signed-to-unsigned bitvector array transmutation (`[iA; xs.length] → [uB; n₂]`,
including `xs = []`) whenever the byte sizes agree. -/
theorem bitVecArray_int_to_uint_transmute_sound (layouts : LayoutTable) (w₁ : IntTy) (w₂ : UintTy)
    (n₂ : Nat) (idx₁ idx₂ : LayoutIdx) (xs : List (BitVec (8 * MirValueCodec.intByteSize w₁)))
    (hsize : MirValueCodec.intByteSize w₁ * xs.length = MirValueCodec.uintByteSize w₂ * n₂) :
    ∃ v', decodeValueFromBytes defaultCodecFuel layouts
      { kind := .array (.uint w₂) n₂, layoutIdx := idx₂ }
      ((bitVecLE (MirValueCodec.intByteSize w₁)
        (MirValueCodec.intByteSize_pos w₁)).encodeElems xs) = some v' :=
  array_int_to_uint_transmute_sound layouts w₁ w₂ xs.length n₂ idx₁ idx₂ hsize _ _
    (encodeValueToBytes_bitVecArray_int layouts w₁ idx₁ xs)

/-! ## 14. Exact Signed-Overflow Biconditionals, Unary Negation, Saturating Ops, `cttz`/Alignment, Byte-Splitting and `ByteSeqValid` -/

/-- Exact biconditional characterization of `signedOverflowAdd a b sz = false` on the ported
`signedKey` window (proving the `ScalarSRange` addition no-overflow side conditions are both
necessary and sufficient). -/
theorem signedOverflowAdd_eq_false_iff_signedKey_bounds {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    signedOverflowAdd a b sz = false ↔
      2 ^ (8 * sz - 1) ≤
          Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) a) +
            Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) b) ∧
        Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) a) +
            Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) b) <
          2 ^ (8 * sz - 1) + 2 ^ (8 * sz) := by
  constructor
  · intro h
    have hw : 0 < 8 * sz := by omega
    have hpow : 2 ^ (8 * sz) = 2 * 2 ^ (8 * sz - 1) := by
      have hw' : 8 * sz = (8 * sz - 1) + 1 := by omega
      conv => lhs; rw [hw']
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [Anneal.Scalars.signedOverflowAdd_eq_msb] at h
    rcases signedKey_linear hw (BitVec.ofNat (8 * sz) a) with ⟨hka, ha_eq⟩ | ⟨hka1, hka2, ha_eq⟩ <;>
      rcases signedKey_linear hw (BitVec.ofNat (8 * sz) b) with ⟨hkb, hb_eq⟩ | ⟨hkb1, hkb2, hb_eq⟩
    · have hma : (BitVec.ofNat (8 * sz) a).msb = true := by
        rw [← msb_eq_core, Anneal.BitVecArith.msb_eq_true_iff hw, natPow_eq]; omega
      have hmb : (BitVec.ofNat (8 * sz) b).msb = true := by
        rw [← msb_eq_core, Anneal.BitVecArith.msb_eq_true_iff hw, natPow_eq]; omega
      rw [hma, hmb] at h
      have hms : (BitVec.ofNat (8 * sz) a + BitVec.ofNat (8 * sz) b).msb = true := by
        cases hms' : (BitVec.ofNat (8 * sz) a + BitVec.ofNat (8 * sz) b).msb with
        | true => rfl
        | false => rw [hms'] at h; cases h
      have hge := (Anneal.BitVecArith.msb_eq_true_iff hw _).1 hms
      rw [natPow_eq, _root_.BitVec.toNat_add, ha_eq, hb_eq] at hge
      have hadd : Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) a) + 2 ^ (8 * sz - 1) +
            (Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) b) + 2 ^ (8 * sz - 1)) =
          (Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) a) +
            Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) b)) + 2 ^ (8 * sz) := by omega
      rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hge
      omega
    · omega
    · omega
    · have hma : (BitVec.ofNat (8 * sz) a).msb = false := by
        rw [← msb_eq_core, Anneal.BitVecArith.msb_eq_false_iff hw, natPow_eq]; omega
      have hmb : (BitVec.ofNat (8 * sz) b).msb = false := by
        rw [← msb_eq_core, Anneal.BitVecArith.msb_eq_false_iff hw, natPow_eq]; omega
      rw [hma, hmb] at h
      have hms : (BitVec.ofNat (8 * sz) a + BitVec.ofNat (8 * sz) b).msb = false := by
        cases hms' : (BitVec.ofNat (8 * sz) a + BitVec.ofNat (8 * sz) b).msb with
        | false => rfl
        | true => rw [hms'] at h; cases h
      have hlt := (Anneal.BitVecArith.msb_eq_false_iff hw _).1 hms
      rw [natPow_eq, _root_.BitVec.toNat_add, ha_eq, hb_eq, Nat.mod_eq_of_lt (by omega)] at hlt
      omega
  · rintro ⟨h1, h2⟩
    exact signedOverflowAdd_eq_false_of_signedKey_bounds hsz a b h1 h2

/-- Exact biconditional characterization of `signedOverflowSub a b sz = false` on the ported
`signedKey` window (proving the `ScalarSRange` subtraction no-overflow side conditions are both
necessary and sufficient). -/
theorem signedOverflowSub_eq_false_iff_signedKey_bounds {sz : Nat} (hsz : 0 < sz) (a b : Nat) :
    signedOverflowSub a b sz = false ↔
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) b) ≤
          Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) a) + 2 ^ (8 * sz - 1) ∧
        Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) a) <
          Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) b) + 2 ^ (8 * sz - 1) := by
  constructor
  · intro h
    have hw : 0 < 8 * sz := by omega
    have hpow : 2 ^ (8 * sz) = 2 * 2 ^ (8 * sz - 1) := by
      have hw' : 8 * sz = (8 * sz - 1) + 1 := by omega
      conv => lhs; rw [hw']
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [Anneal.Scalars.signedOverflowSub_eq_msb] at h
    rcases signedKey_linear hw (BitVec.ofNat (8 * sz) a) with ⟨hka, ha_eq⟩ | ⟨hka1, hka2, ha_eq⟩ <;>
      rcases signedKey_linear hw (BitVec.ofNat (8 * sz) b) with ⟨hkb, hb_eq⟩ | ⟨hkb1, hkb2, hb_eq⟩
    · omega
    · have hma : (BitVec.ofNat (8 * sz) a).msb = true := by
        rw [← msb_eq_core, Anneal.BitVecArith.msb_eq_true_iff hw, natPow_eq]; omega
      have hmb : (BitVec.ofNat (8 * sz) b).msb = false := by
        rw [← msb_eq_core, Anneal.BitVecArith.msb_eq_false_iff hw, natPow_eq]; omega
      rw [hma, hmb] at h
      have hmd : (BitVec.ofNat (8 * sz) a - BitVec.ofNat (8 * sz) b).msb = true := by
        cases hmd' : (BitVec.ofNat (8 * sz) a - BitVec.ofNat (8 * sz) b).msb with
        | true => rfl
        | false => rw [hmd'] at h; cases h
      have hge := (Anneal.BitVecArith.msb_eq_true_iff hw _).1 hmd
      rw [natPow_eq, _root_.BitVec.toNat_sub, ha_eq, hb_eq] at hge
      have hsub : 2 ^ (8 * sz) -
            (Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) b) - 2 ^ (8 * sz - 1)) +
            (Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) a) + 2 ^ (8 * sz - 1)) =
          (Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) a) + 2 ^ (8 * sz) -
            Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) b)) + 2 ^ (8 * sz) := by omega
      rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hge
      omega
    · have hma : (BitVec.ofNat (8 * sz) a).msb = false := by
        rw [← msb_eq_core, Anneal.BitVecArith.msb_eq_false_iff hw, natPow_eq]; omega
      have hmb : (BitVec.ofNat (8 * sz) b).msb = true := by
        rw [← msb_eq_core, Anneal.BitVecArith.msb_eq_true_iff hw, natPow_eq]; omega
      rw [hma, hmb] at h
      have hmd : (BitVec.ofNat (8 * sz) a - BitVec.ofNat (8 * sz) b).msb = false := by
        cases hmd' : (BitVec.ofNat (8 * sz) a - BitVec.ofNat (8 * sz) b).msb with
        | false => rfl
        | true => rw [hmd'] at h; cases h
      have hlt := (Anneal.BitVecArith.msb_eq_false_iff hw _).1 hmd
      rw [natPow_eq, _root_.BitVec.toNat_sub, ha_eq, hb_eq, Nat.mod_eq_of_lt (by omega)] at hlt
      omega
    · omega
  · rintro ⟨h1, h2⟩
    exact signedOverflowSub_eq_false_of_signedKey_bounds hsz a b h1 h2

/-- Ported `signedKey` of two's-complement negation whenever `x` is not the minimum signed value
(`0 < signedKey x`, i.e., `x ≠ signBit`). -/
theorem signedKey_neg_of_pos {w : Nat} (hw : 0 < w) {x : BitVec w}
    (hx : 0 < Anneal.BitVecArith.signedKey x) :
    Anneal.BitVecArith.signedKey (Anneal.BitVecArith.neg x) =
      2 ^ w - Anneal.BitVecArith.signedKey x := by
  have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
    cases w with
    | zero => omega
    | succ k => change 2 ^ (k + 1) = 2 * 2 ^ k; rw [Nat.pow_succ, Nat.mul_comm]
  have hzero : Anneal.BitVecArith.signedKey (BitVec.ofNat w 0) = 2 ^ (w - 1) := by
    have hm : Anneal.BitVecArith.msb (BitVec.ofNat w 0) = false := by
      rw [Anneal.BitVecArith.msb_eq_false_iff hw, Anneal.BitVec.toNat_zero, natPow_eq]
      exact Nat.two_pow_pos _
    have hk := Anneal.BitVecArith.signedKey_eq_of_msb_false hw hm
    rw [Anneal.BitVec.toNat_zero, natPow_eq, Nat.zero_add] at hk
    exact hk
  have hneg : Anneal.BitVecArith.neg x = BitVec.ofNat w 0 - x := by
    rw [Anneal.BitVecArith.sub_eq_add_neg]
    apply _root_.BitVec.eq_of_toNat_eq
    rw [_root_.BitVec.toNat_add, Anneal.BitVec.toNat_zero, Nat.zero_add,
      Nat.mod_eq_of_lt (Anneal.BitVecArith.neg x).isLt]
  have hlt := Anneal.BitVecArith.signedKey_lt x
  rw [natPow_eq] at hlt
  rw [hneg, signedKey_sub_no_overflow hw (by rw [hzero]; omega) (by rw [hzero]; omega), hzero]
  omega

/-- Signed interval transfer through `evalUnOp .neg` whenever `smin` excludes `T::MIN`
(`0 < signedKey smin`). -/
theorem scalarSRange_evalUnOp_neg_no_overflow {sz : Nat} (hsz : 0 < sz)
    {smin smax : BitVec (8 * sz)} {x : ScalarInt} (isBool : Bool)
    (hx : ScalarSRange sz smin smax x) (hpos : 0 < Anneal.BitVecArith.signedKey smin) :
    ∃ r, Anneal.Scalars.evalUnOp .neg x isBool = some r ∧
      ScalarSRange sz (Anneal.BitVecArith.neg smax) (Anneal.BitVecArith.neg smin) r := by
  obtain ⟨xb, rfl, _, hx₁, hx₂⟩ := scalarSRange_exists hx
  have hw : 0 < 8 * sz := by omega
  have hlo : Anneal.BitVecArith.signedKey smin ≤
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) xb) := hx₁
  have hhi : Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) xb) ≤
      Anneal.BitVecArith.signedKey smax := hx₂
  have h1 := signedKey_neg_of_pos hw hpos
  have h2 := signedKey_neg_of_pos hw (Nat.lt_of_lt_of_le hpos hlo)
  have h3 := signedKey_neg_of_pos hw (Nat.lt_of_lt_of_le hpos (Nat.le_trans hlo hhi))
  refine ⟨_, evalUnOp_neg_eq_neg hsz xb isBool, scalarSRange_of_bitVec _ ?_ ?_⟩
  · unfold Anneal.BitVecArith.sle; rw [h3, h2]; omega
  · unfold Anneal.BitVecArith.sle; rw [h2, h1]; omega

/-- Tnum transfer through `evalUnOp .neg` via `neg x = 0 - x` (`tnumSub_sound`). -/
theorem scalarTnum_evalUnOp_neg {sz : Nat} (hsz : 0 < sz) {m v : BitVec (8 * sz)}
    {x : ScalarInt} (isBool : Bool) (hx : ScalarTnum sz m v x) :
    ∃ r, Anneal.Scalars.evalUnOp .neg x isBool = some r ∧
      ScalarTnum sz (tnumSubMask (BitVec.ofNat (8 * sz) 0) (BitVec.ofNat (8 * sz) 0) m v)
        (tnumSubValue (BitVec.ofNat (8 * sz) 0) (BitVec.ofNat (8 * sz) 0) m v) r := by
  obtain ⟨xb, rfl, _, hxm⟩ := scalarTnum_exists hx
  have hneg : Anneal.BitVecArith.neg (BitVec.ofNat (8 * sz) xb) =
      BitVec.ofNat (8 * sz) 0 - BitVec.ofNat (8 * sz) xb := by
    rw [Anneal.BitVecArith.sub_eq_add_neg]
    apply _root_.BitVec.eq_of_toNat_eq
    rw [_root_.BitVec.toNat_add, Anneal.BitVec.toNat_zero, Nat.zero_add,
      Nat.mod_eq_of_lt (Anneal.BitVecArith.neg _).isLt]
  refine ⟨_, evalUnOp_neg_eq_neg hsz xb isBool, ?_⟩
  rw [hneg]
  exact scalarTnum_of_bitVec _ (tnumSub_sound (Anneal.BitVec.maskEq_refl _ _) hxm)

/-- Unsigned `evalSaturatingAdd` when the interval cannot overflow: agrees with exact `BitVec`
addition and preserves `[a_lo + b_lo, a_hi + b_hi]`. -/
theorem scalarRange_evalSaturatingAdd_no_overflow {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y)
    (hno : a_hi.toNat + b_hi.toNat < 2 ^ (8 * sz)) :
    ∃ r, evalSaturatingAdd x y false = some r ∧
      ScalarRange sz (a_lo + b_lo) (a_hi + b_hi) r := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, hy₂⟩ := scalarRange_exists hy
  have hle_x : xb ≤ a_hi.toNat := by
    have h : (BitVec.ofNat (8 * sz) xb).toNat ≤ a_hi.toNat := hx₂
    rwa [toNat_ofNat_of_lt hxb] at h
  have hle_y : yb ≤ b_hi.toNat := by
    have h : (BitVec.ofNat (8 * sz) yb).toNat ≤ b_hi.toNat := hy₂
    rwa [toNat_ofNat_of_lt hyb] at h
  have hlt : xb + yb < 2 ^ (8 * sz) := by omega
  have hble : Nat.ble (2 ^ (8 * sz)) (xb + yb) = false := by
    cases h : Nat.ble (2 ^ (8 * sz)) (xb + yb) with
    | false => rfl
    | true => have := Nat.le_of_ble_eq_true h; omega
  have hs := Anneal.BitVec.range_add_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hno
  have heq : (BitVec.ofNat (8 * sz) xb + BitVec.ofNat (8 * sz) yb).toNat = xb + yb := by
    rw [← add_mod_eq_toNat_add, Nat.mod_eq_of_lt hlt]
  refine ⟨⟨xb + yb, sz⟩, ?_, by rw [← heq]; exact scalarRange_of_bitVec _ hs.1 hs.2⟩
  unfold evalSaturatingAdd
  simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
    wrapScalarBits_of_lt hxb, wrapScalarBits_of_lt hyb]
  simp only [scalarModulus_eq, natAdd_eq, hble]

/-- Unsigned `evalSaturatingAdd` when the interval is guaranteed to overflow: clamps exactly to
`allOnes (8 * sz)`. -/
theorem scalarRange_evalSaturatingAdd_overflow_clamps {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y)
    (hovf : 2 ^ (8 * sz) ≤ a_lo.toNat + b_lo.toNat) :
    evalSaturatingAdd x y false = some ⟨(Anneal.BitVec.allOnes (8 * sz)).toNat, sz⟩ := by
  obtain ⟨xb, rfl, hxb, hx₁, _⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, _⟩ := scalarRange_exists hy
  have hle_x : a_lo.toNat ≤ xb := by
    have h : a_lo.toNat ≤ (BitVec.ofNat (8 * sz) xb).toNat := hx₁
    rwa [toNat_ofNat_of_lt hxb] at h
  have hle_y : b_lo.toNat ≤ yb := by
    have h : b_lo.toNat ≤ (BitVec.ofNat (8 * sz) yb).toNat := hy₁
    rwa [toNat_ofNat_of_lt hyb] at h
  have hble : Nat.ble (2 ^ (8 * sz)) (xb + yb) = true := Nat.ble_eq_true_of_le (by omega)
  unfold evalSaturatingAdd
  simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
    wrapScalarBits_of_lt hxb, wrapScalarBits_of_lt hyb]
  simp only [scalarModulus_eq, natAdd_eq, natSub_eq, hble, Anneal.BitVec.toNat_allOnes, natPow_eq]

/-- Unsigned `evalSaturatingSub` when the interval cannot underflow: agrees with exact `BitVec`
subtraction and preserves `[a_lo - b_hi, a_hi - b_lo]`. -/
theorem scalarRange_evalSaturatingSub_no_underflow {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y) (hno : b_hi ≤ a_lo) :
    ∃ r, evalSaturatingSub x y false = some r ∧
      ScalarRange sz (a_lo - b_hi) (a_hi - b_lo) r := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, hy₂⟩ := scalarRange_exists hy
  have hax : a_lo.toNat ≤ xb := by
    have h : a_lo.toNat ≤ (BitVec.ofNat (8 * sz) xb).toNat := hx₁
    rwa [toNat_ofNat_of_lt hxb] at h
  have hby : yb ≤ b_hi.toNat := by
    have h : (BitVec.ofNat (8 * sz) yb).toNat ≤ b_hi.toNat := hy₂
    rwa [toNat_ofNat_of_lt hyb] at h
  have hba : b_hi.toNat ≤ a_lo.toNat := hno
  have hyx : yb ≤ xb := by omega
  have hble : Nat.ble yb xb = true := Nat.ble_eq_true_of_le hyx
  have hbv_le : BitVec.ofNat (8 * sz) yb ≤ BitVec.ofNat (8 * sz) xb := by
    show (BitVec.ofNat (8 * sz) yb).toNat ≤ (BitVec.ofNat (8 * sz) xb).toNat
    rw [toNat_ofNat_of_lt hxb, toNat_ofNat_of_lt hyb]; exact hyx
  have heq : (BitVec.ofNat (8 * sz) xb - BitVec.ofNat (8 * sz) yb).toNat = xb - yb := by
    rw [Anneal.BitVec.toNat_sub_of_le hbv_le, toNat_ofNat_of_lt hxb, toNat_ofNat_of_lt hyb]
  have hs := Anneal.BitVec.range_sub_no_underflow_sound hx₁ hx₂ hy₁ hy₂ hno
  refine ⟨⟨xb - yb, sz⟩, ?_, by rw [← heq]; exact scalarRange_of_bitVec _ hs.1 hs.2⟩
  unfold evalSaturatingSub
  simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
    wrapScalarBits_of_lt hxb, wrapScalarBits_of_lt hyb, hble, natSub_eq]

/-- Unsigned `evalSaturatingSub` when `a_hi ≤ b_lo`: clamps exactly to `0`. -/
theorem scalarRange_evalSaturatingSub_underflow_clamps {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarRange sz a_lo a_hi x) (hy : ScalarRange sz b_lo b_hi y) (hudf : a_hi ≤ b_lo) :
    evalSaturatingSub x y false = some ⟨0, sz⟩ := by
  obtain ⟨xb, rfl, hxb, _, hx₂⟩ := scalarRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, _⟩ := scalarRange_exists hy
  have hxa : xb ≤ a_hi.toNat := by
    have h : (BitVec.ofNat (8 * sz) xb).toNat ≤ a_hi.toNat := hx₂
    rwa [toNat_ofNat_of_lt hxb] at h
  have hby : b_lo.toNat ≤ yb := by
    have h : b_lo.toNat ≤ (BitVec.ofNat (8 * sz) yb).toNat := hy₁
    rwa [toNat_ofNat_of_lt hyb] at h
  have hab : a_hi.toNat ≤ b_lo.toNat := hudf
  unfold evalSaturatingSub
  simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
    wrapScalarBits_of_lt hxb, wrapScalarBits_of_lt hyb]
  cases hble : Nat.ble yb xb with
  | false => rfl
  | true =>
    have hyx := Nat.le_of_ble_eq_true hble
    have hsub : Nat.sub xb yb = 0 := by rw [natSub_eq]; omega
    rw [hsub]

/-- Signed `evalSaturatingAdd` when the `ScalarSRange` intervals cannot overflow: agrees with exact
two's-complement addition and preserves `[a_lo + b_lo, a_hi + b_hi]`. -/
theorem scalarSRange_evalSaturatingAdd_no_overflow {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarSRange sz a_lo a_hi x) (hy : ScalarSRange sz b_lo b_hi y)
    (hlo : 2 ^ (8 * sz - 1) ≤
      Anneal.BitVecArith.signedKey a_lo + Anneal.BitVecArith.signedKey b_lo)
    (hhi : Anneal.BitVecArith.signedKey a_hi + Anneal.BitVecArith.signedKey b_hi <
      2 ^ (8 * sz - 1) + 2 ^ (8 * sz)) :
    ∃ r, evalSaturatingAdd x y true = some r ∧
      ScalarSRange sz (a_lo + b_lo) (a_hi + b_hi) r := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, hy₂⟩ := scalarSRange_exists hy
  have hlo' : 2 ^ (8 * sz - 1) ≤
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) xb) +
        Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) yb) :=
    Nat.le_trans hlo (Nat.add_le_add hx₁ hy₁)
  have hhi' : Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) xb) +
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) yb) <
      2 ^ (8 * sz - 1) + 2 ^ (8 * sz) :=
    Nat.lt_of_le_of_lt (Nat.add_le_add hx₂ hy₂) hhi
  have hno := signedOverflowAdd_eq_false_of_signedKey_bounds hsz xb yb hlo' hhi'
  have hs := Anneal.BitVecArith.signed_range_add_no_overflow_sound
    hx₁ hx₂ hy₁ hy₂ (by rwa [natPow_eq]) (by rwa [natPow_eq, natPow_eq])
  refine ⟨⟨(BitVec.ofNat (8 * sz) xb + BitVec.ofNat (8 * sz) yb).toNat, sz⟩, ?_,
    scalarSRange_of_bitVec _ hs.1 hs.2⟩
  unfold evalSaturatingAdd
  simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
    wrapScalarBits_of_lt hxb, wrapScalarBits_of_lt hyb, hno]
  rw [natAdd_eq, wrapScalarBits_eq_toNat, ← add_mod_eq_toNat_add, _root_.BitVec.toNat_ofNat]

/-- Signed `evalSaturatingSub` when the `ScalarSRange` intervals cannot overflow: agrees with exact
two's-complement subtraction and preserves `[a_lo - b_hi, a_hi - b_lo]`. -/
theorem scalarSRange_evalSaturatingSub_no_overflow {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarSRange sz a_lo a_hi x) (hy : ScalarSRange sz b_lo b_hi y)
    (hlo : Anneal.BitVecArith.signedKey b_hi ≤
      Anneal.BitVecArith.signedKey a_lo + 2 ^ (8 * sz - 1))
    (hhi : Anneal.BitVecArith.signedKey a_hi <
      Anneal.BitVecArith.signedKey b_lo + 2 ^ (8 * sz - 1)) :
    ∃ r, evalSaturatingSub x y true = some r ∧
      ScalarSRange sz (a_lo - b_hi) (a_hi - b_lo) r := by
  obtain ⟨xb, rfl, hxb, hx₁, hx₂⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, hy₂⟩ := scalarSRange_exists hy
  have hlo' : Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) yb) ≤
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) xb) + 2 ^ (8 * sz - 1) :=
    Nat.le_trans hy₂ (Nat.le_trans hlo (Nat.add_le_add_right hx₁ _))
  have hhi' : Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) xb) <
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) yb) + 2 ^ (8 * sz - 1) :=
    Nat.lt_of_le_of_lt hx₂ (Nat.lt_of_lt_of_le hhi (Nat.add_le_add_right hy₁ _))
  have hno := signedOverflowSub_eq_false_of_signedKey_bounds hsz xb yb hlo' hhi'
  have hs := signed_range_sub_no_overflow_sound hx₁ hx₂ hy₁ hy₂ hlo hhi
  refine ⟨⟨(BitVec.ofNat (8 * sz) xb - BitVec.ofNat (8 * sz) yb).toNat, sz⟩, ?_,
    scalarSRange_of_bitVec _ hs.1 hs.2⟩
  unfold evalSaturatingSub
  simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
    wrapScalarBits_of_lt hxb, wrapScalarBits_of_lt hyb, hno]
  rw [natAdd_eq, natSub_eq, wrapScalarBits_eq_toNat, scalarModulus_eq, _root_.BitVec.toNat_ofNat,
    _root_.BitVec.toNat_sub, toNat_ofNat_of_lt hxb, toNat_ofNat_of_lt hyb, Nat.add_comm]

/-- `bitreverseLoop` is an involution on `BitVec w` at every width `w` (including `w = 0`). -/
theorem bitreverseLoop_involutive {w : Nat} (x : BitVec w) :
    BitVec.ofNat w (Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop w
      (Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop w x.toNat 0) 0) = x := by
  apply Anneal.BitVec.eq_of_testBit_eq
  intro i hi
  rw [_root_.BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
    testBit_bitreverseLoop]
  simp only [hi, ↓reduceIte, testBit_bitreverseLoop]
  have hj : w - 1 - i < w := by omega
  have hinv : w - 1 - (w - 1 - i) = i := by omega
  simp only [hj, ↓reduceIte, hinv]

/-- `bitreverseLoop w b 0` is always strictly below `2 ^ w` (for every `w`, including `w = 0`). -/
theorem bitreverseLoop_lt (w b : Nat) :
    Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop w b 0 < 2 ^ w := by
  have h : ∀ n b acc, acc < 2 ^ (w - n) → n ≤ w →
      Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop n b acc < 2 ^ w := by
    intro n
    induction n with
    | zero => intro b acc ha _; simpa using ha
    | succ k ih =>
      intro b acc ha hk
      have hstep : Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop (k + 1) b acc =
          Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop k (b / 2)
            (acc * 2 + b % 2) := rfl
      rw [hstep]
      apply ih
      · have hp : 2 ^ (w - k) = 2 ^ (w - (k + 1)) * 2 := by
          rw [← Nat.pow_succ]; congr 1; omega
        have hmod : b % 2 < 2 := Nat.mod_lt b (by decide)
        omega
      · omega
  exact h w b 0 (by simp) (Nat.le_refl _)

/-- `evalBitreverse` is an involution up to `wrapScalarBits` normalization (no canonicity
hypothesis on `bits` required). -/
theorem evalBitreverse_evalBitreverse {sz : Nat} (hsz : 0 < sz) (bits : Nat) :
    (evalBitreverse ⟨bits, sz⟩).bind evalBitreverse =
      some ⟨wrapScalarBits bits (scalarModulus sz), sz⟩ := by
  have hlt1 : Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop (8 * sz)
      (wrapScalarBits bits (scalarModulus sz)) 0 < scalarModulus sz := by
    rw [scalarModulus_eq]
    exact bitreverseLoop_lt (8 * sz) _
  have hlt2 := bitreverseLoop_lt (8 * sz)
    (Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop (8 * sz)
      (wrapScalarBits bits (scalarModulus sz)) 0)
  unfold evalBitreverse
  simp only [beq_zero_of_pos hsz, natMul_eight, Option.bind_some, wrapScalarBits_of_lt hlt1]
  congr 1; congr 1
  have hinv := congrArg _root_.BitVec.toNat (bitreverseLoop_involutive (BitVec.ofNat (8 * sz) bits))
  rw [_root_.BitVec.toNat_ofNat] at hinv
  rw [← wrapScalarBits_eq_toNat] at hinv
  rw [Nat.mod_eq_of_lt hlt2] at hinv
  exact hinv

/-- `Trusted` `cttzLoop` on `x` is the ported `clz` of `bitreverse x`, at every width `w`
(including `w = 0`). -/
theorem cttzLoop_eq_clz_bitreverse {w : Nat} (x : BitVec w) :
    Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop w x.toNat =
      Anneal.BitVec.clz
        (BitVec.ofNat w (Trusted.Rustc.V2026_06_01.MirSemantics.bitreverseLoop w x.toNat 0)) := by
  apply cttzLoop_eq_clzAux
  intro j hj
  rw [_root_.BitVec.toNat_ofNat, Nat.testBit_mod_two_pow]
  have h1 : w - 1 - j < w := by omega
  have h2 : w - 1 - (w - 1 - j) = j := by omega
  simp only [h1, decide_true, Bool.true_and, testBit_bitreverseLoop, ↓reduceIte, h2]

/-- Every bit strictly below `cttzLoop w v` is `false`. -/
theorem testBit_false_of_lt_cttzLoop :
    ∀ (w v j : Nat), j < Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop w v → v.testBit j = false
  | 0, _, _, h => by cases h
  | k + 1, v, j, h => by
    have hstep : Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop (k + 1) v =
        (match Nat.beq (v % 2) 0 with
          | true => 1 + Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop k (v / 2)
          | false => 0) := rfl
    rw [hstep] at h
    cases hmod : Nat.mod_two_eq_zero_or_one v with
    | inr h1 =>
      rw [h1] at h
      cases h
    | inl h0 =>
      rw [h0] at h
      cases j with
      | zero =>
        rw [Nat.testBit_zero, h0]
        rfl
      | succ j' =>
        rw [Nat.testBit_add_one]
        change j' + 1 < 1 + Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop k (v / 2) at h
        exact testBit_false_of_lt_cttzLoop k (v / 2) j' (by omega)

/-- `evalCttz` is rejected exactly on a zero-width operand or return type. -/
theorem evalCttz_eq_none_iff (sc : ScalarInt) (retBytes : Nat) :
    evalCttz sc retBytes = none ↔ sc.sizeBytes = 0 ∨ retBytes = 0 := by
  unfold evalCttz
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

/-- `evalCttzNonzero` is undefined behavior (`none`) on positive widths iff the operand is zero. -/
theorem evalCttzNonzero_eq_none_iff {sz retBytes : Nat} (hsz : 0 < sz) (hret : 0 < retBytes)
    (bits : Nat) :
    evalCttzNonzero ⟨bits, sz⟩ retBytes = none ↔
      BitVec.ofNat (8 * sz) bits = BitVec.ofNat (8 * sz) 0 := by
  unfold evalCttzNonzero
  simp only [beq_zero_of_pos hsz, beq_zero_of_pos hret, Bool.or_false, wrapScalarBits_eq_toNat]
  cases hz : Nat.beq (BitVec.ofNat (8 * sz) bits).toNat 0 with
  | true =>
    have hz' : (BitVec.ofNat (8 * sz) bits).toNat = 0 := Nat.eq_of_beq_eq_true hz
    exact ⟨fun _ => Anneal.BitVec.eq_of_toNat_eq (hz'.trans (Anneal.BitVec.toNat_zero _).symm),
      fun _ => rfl⟩
  | false =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h
    · rw [h] at hz; cases hz

/-- Trailing-zero alignment bridge: whenever `evalCttz` on a canonical scalar returns `k`, the
low `k` bits are known zero in `ScalarTnum` (`MaskEq (not (lowMask (8 * sz) k)) x 0`) and the
scalar is `2^k`-aligned (`x.bits % 2^k = 0`), plugging directly into
`bitwiseOrBits_aligned_bounded_injective`. -/
theorem scalarTnum_lowMask_of_evalCttz {sz retBytes k : Nat} (hsz : 0 < sz) (hret : 0 < retBytes)
    {x : ScalarInt} (hszx : x.sizeBytes = sz) (hcan : x.bits < scalarModulus sz)
    (hcttz : evalCttz x retBytes = some ⟨k, retBytes⟩) :
    ScalarTnum sz (Anneal.BitVec.not (Anneal.BitVec.lowMask (8 * sz) k))
        (BitVec.ofNat (8 * sz) 0) x ∧ x.bits % 2 ^ k = 0 := by
  obtain ⟨xb, xs⟩ := x
  dsimp only at hszx hcan hcttz
  subst xs
  unfold evalCttz at hcttz
  simp only [beq_zero_of_pos hsz, beq_zero_of_pos hret, Bool.or_false, natMul_eight,
    wrapScalarBits_of_lt hcan] at hcttz
  have hk : Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop (8 * sz) xb = k :=
    (ScalarInt.mk.inj (Option.some.inj hcttz)).1
  have hlow : ∀ j, j < k → xb.testBit j = false := fun j hj =>
    testBit_false_of_lt_cttzLoop (8 * sz) xb j (hk.symm ▸ hj)
  have htnum : ScalarTnum sz (Anneal.BitVec.not (Anneal.BitVec.lowMask (8 * sz) k))
      (BitVec.ofNat (8 * sz) 0) ⟨xb, sz⟩ := by
    refine ⟨rfl, hcan, Anneal.BitVec.maskEq_iff_getLsbD.2 (fun i hi hm => ?_)⟩
    rw [Anneal.BitVec.getLsbD_not_of_lt _ hi, Anneal.BitVec.getLsbD_lowMask hi] at hm
    have hik : i < k := by
      cases hdec : decide (i < k) with
      | true => exact of_decide_eq_true hdec
      | false => rw [hdec] at hm; cases hm
    rw [Anneal.BitVec.getLsbD_zero]
    show (BitVec.ofNat (8 * sz) xb).toNat.testBit i = false
    rw [toNat_ofNat_of_lt hcan]
    exact hlow i hik
  have hmod : xb % 2 ^ k = 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    cases Nat.lt_or_ge j k with
    | inl hj => simp [hj, hlow j hj]
    | inr hj => simp [Nat.not_lt_of_ge hj]
  exact ⟨htnum, hmod⟩

/-- Byte-splitting bridge connecting `Anneal.BitVecArith.extractBits` to `bitVecLE`: encoding an
`8 * (m + n)`-bit vector splits cleanly into the `bitVecLE m` encoding of its low `8 * m` bits
followed by the `bitVecLE n` encoding of its high `8 * n` bits. -/
theorem bitVecLE_encode_split_extractBits (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (x : BitVec (8 * (m + n))) :
    (bitVecLE (m + n) (Nat.add_pos_left hm n)).encode x =
      (bitVecLE m hm).encode (Anneal.BitVecArith.extractBits x 0 (8 * m)) ++
        (bitVecLE n hn).encode (Anneal.BitVecArith.extractBits x (8 * m) (8 * n)) := by
  have hlo : (Anneal.BitVecArith.extractBits x 0 (8 * m)).toNat = x.toNat % 2 ^ (m * 8) := by
    unfold Anneal.BitVecArith.extractBits
    rw [setWidth_eq_core, ushr_eq_core, _root_.BitVec.toNat_setWidth,
      _root_.BitVec.toNat_ushiftRight, Nat.shiftRight_zero, Nat.mul_comm 8 m]
  have hhi : (Anneal.BitVecArith.extractBits x (8 * m) (8 * n)).toNat = x.toNat / 2 ^ (m * 8) := by
    unfold Anneal.BitVecArith.extractBits
    rw [setWidth_eq_core, ushr_eq_core, _root_.BitVec.toNat_setWidth,
      _root_.BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mul_comm 8 m]
    have hlt : x.toNat / 2 ^ (m * 8) < 2 ^ (8 * n) := by
      have hx := x.isLt
      have hp : 2 ^ (8 * (m + n)) = 2 ^ (m * 8) * 2 ^ (8 * n) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [hp] at hx
      exact Nat.div_lt_of_lt_mul hx
    exact Nat.mod_eq_of_lt hlt
  rw [bitVecLE_encode_append m n hm hn, hlo, hhi]
  congr 1
  apply _root_.BitVec.eq_of_toNat_eq
  rw [_root_.BitVec.toNat_ofNat, Nat.mod_add_div, Nat.mod_eq_of_lt x.isLt]

/-- Product-decoder bridge: decoding *any* `bs : List AbstractByte` (including wrong-length,
`.uninit`, and mixed-provenance buffers) with `FixedByteCodec.prod (bitVecLE m) (bitVecLE n)`
and concatenating the resulting `(a, b)` agrees identically with `(bitVecLE (m + n)).decode bs`. -/
theorem bitVecLE_decode_prod (m n : Nat) (hm : 0 < m) (hn : 0 < n) (bs : List AbstractByte) :
    ((FixedByteCodec.prod (bitVecLE m hm) (bitVecLE n hn)).decode bs).map
        (fun p => BitVec.ofNat (8 * (m + n)) (p.1.toNat + 2 ^ (m * 8) * p.2.toNat)) =
      (bitVecLE (m + n) (Nat.add_pos_left hm n)).decode bs := by
  cases Nat.decEq bs.length (m + n) with
  | isFalse hne =>
    have h1 := FixedByteCodec.IsExactWidth.decode_eq_none_of_length_ne
      (FixedByteCodec.prod_isExactWidth (bitVecLE m hm) (bitVecLE n hn)) hne
    have h2 := bitVecLE_decode_eq_none_of_length_ne (m + n) (Nat.add_pos_left hm n) hne
    rw [h1, h2]
    rfl
  | isTrue hlen =>
    cases hi : allBytesInitialized bs with
    | false =>
      have h2 := bitVecLE_decode_eq_none_of_uninit (m + n) (Nat.add_pos_left hm n) hi
      rw [h2]
      cases h1 : (FixedByteCodec.prod (bitVecLE m hm) (bitVecLE n hn)).decode bs with
      | none => rfl
      | some p =>
        obtain ⟨a, b⟩ := p
        unfold FixedByteCodec.prod FixedByteCodec.ofRoundTrip at h1
        dsimp only at h1
        rw [Nat.beq_eq.mpr hlen] at h1
        dsimp only at h1
        cases hta : (bitVecLE m hm).decode (bs.take m) with
        | none => rw [hta] at h1; cases h1
        | some a' =>
          cases htb : (bitVecLE n hn).decode (bs.drop m) with
          | none => rw [hta, htb] at h1; cases h1
          | some b' =>
            have hi1 := ((bitVecLE_decode_eq_some_iff m hm (bs.take m) a').1 hta).2.1
            have hi2 := ((bitVecLE_decode_eq_some_iff n hn (bs.drop m) b').1 htb).2.1
            have hall : allBytesInitialized bs = true := by
              rw [← List.take_append_drop m bs]
              exact allBytesInitialized_append hi1 hi2
            rw [hall] at hi
            cases hi
    | true =>
      have htake_len : (bs.take m).length = m := by rw [List.length_take]; omega
      have hdrop_len : (bs.drop m).length = n := by rw [List.length_drop]; omega
      have htake_init : allBytesInitialized (bs.take m) = true := allBytesInitialized_take m hi
      have hdrop_init : allBytesInitialized (bs.drop m) = true := allBytesInitialized_drop m hi
      obtain ⟨a, ha⟩ := bitVecLE_isSurjectiveInitDecoder m hm (bs.take m) htake_len htake_init
      obtain ⟨b, hb⟩ := bitVecLE_isSurjectiveInitDecoder n hn (bs.drop m) hdrop_len hdrop_init
      have hprod : (FixedByteCodec.prod (bitVecLE m hm) (bitVecLE n hn)).decode bs = some (a, b) := by
        unfold FixedByteCodec.prod FixedByteCodec.ofRoundTrip
        dsimp only
        rw [Nat.beq_eq.mpr hlen]
        dsimp only
        rw [ha, hb]
      rw [hprod, Option.map_some]
      have ha' := ((bitVecLE_decode_eq_some_iff m hm (bs.take m) a).1 ha).2.2
      have hb' := ((bitVecLE_decode_eq_some_iff n hn (bs.drop m) b).1 hb).2.2
      have hcat : Anneal.LeBytes.fromLeBytes (extractInitBvBytes bs) =
          a.toNat + 2 ^ (m * 8) * b.toNat := by
        have hsplit : bs = bs.take m ++ bs.drop m := (List.take_append_drop m bs).symm
        conv => lhs; rw [hsplit]
        rw [extractInitBvBytes_append, Anneal.LeBytes.fromLeBytes_append, ha', hb',
          (length_extractInitBvBytes_eq_iff (bs.take m)).2 htake_init, htake_len]
      have hsum_lt : a.toNat + 2 ^ (m * 8) * b.toNat < 2 ^ (8 * (m + n)) := by
        have hlt := Anneal.LeBytes.fromLeBytes_lt (extractInitBvBytes bs)
        rw [(length_extractInitBvBytes_eq_iff bs).2 hi, hlen, Nat.mul_comm] at hlt
        rwa [hcat] at hlt
      symm
      exact (bitVecLE_decode_eq_some_iff (m + n) (Nat.add_pos_left hm n) bs _).2
        ⟨hlen, hi, by rw [_root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum_lt]; exact hcat⟩

/-- Exact `ByteSeqValid` characterization for unsigned integer arrays `[uN; n]` (including `n = 0`):
a byte sequence is `.BitValid` iff it has byte length `uintByteSize w * n` and no `.uninit` bytes. -/
theorem byteSeqValid_bitValid_array_uint_iff (layouts : LayoutTable) (w : UintTy) (n : Nat)
    (idx : LayoutIdx) (bs : List AbstractByte) :
    ByteSeqValid layouts { kind := .array (.uint w) n, layoutIdx := idx } .BitValid bs ↔
      bs.length = MirValueCodec.uintByteSize w * n ∧ allBytesInitialized bs = true := by
  constructor
  · rintro ⟨sz, v, hsz, hlen, hdec⟩
    rw [rigidTyByteSize_array_uint] at hsz
    have hsz' : sz = MirValueCodec.uintByteSize w * n := Option.some.inj hsz.symm
    subst hsz'
    rw [seqLength_eq] at hlen
    refine ⟨hlen, ?_⟩
    cases n with
    | zero =>
      have hbs : bs = [] := List.length_eq_zero_iff.1 (by simpa using hlen)
      subst hbs; rfl
    | succ k =>
      cases hi : allBytesInitialized bs with
      | true => rfl
      | false =>
        exfalso
        have hnz := MirValueCodec.uintByteSize_pos w
        let hm := MirValueCodec.uintArray layouts w (k + 1) (Nat.succ_pos k) idx
        rw [hm.decode_eq_map] at hdec
        cases hd : hm.codec.decode bs with
        | none => rw [hd] at hdec; cases hdec
        | some xs =>
          have hch : (FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w) hnz).decodeChunks
              (k + 1) bs = some xs := hd
          have hchunks_eq := decodeChunks_eq_chunksOf
            (FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w) hnz) hnz (k + 1) bs
          rw [hch] at hchunks_eq
          have hlen_mul : bs.length = (k + 1) * MirValueCodec.uintByteSize w := by
            rw [hlen, Nat.mul_comm]
          simp only [hlen_mul, ↓reduceIte, Option.map_some] at hchunks_eq
          have hmap := (sequenceOptions_eq_some_iff _ _).1 hchunks_eq.symm
          have hflat : (Anneal.ListChunks.chunksOf (MirValueCodec.uintByteSize w) bs).flatten = bs :=
            Anneal.ListChunks.chunksOf_flatten hnz bs
          have hall_chunks : ∀ ch ∈ Anneal.ListChunks.chunksOf (MirValueCodec.uintByteSize w) bs,
              allBytesInitialized ch = true := by
            intro ch hmem
            have hsome : (FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w) hnz).decode ch ∈
                xs.val.map some := by
              rw [← hmap]; exact List.mem_map_of_mem hmem
            obtain ⟨y, _, hy⟩ := List.mem_map.1 hsome
            cases hci : allBytesInitialized ch with
            | true => rfl
            | false =>
              exfalso
              have hnone : (bitVecLE (MirValueCodec.uintByteSize w) hnz).decode ch = none :=
                bitVecLE_decode_eq_none_of_uninit _ hnz hci
              have : ((FixedByteCodec.uintBitsLE (MirValueCodec.uintByteSize w) hnz).decode ch).map
                  (fun b => BitVec.ofNatLT b.val b.property) = none := hnone
              rw [hy.symm] at this
              cases this
          have hall_flat : ∀ l : List (List AbstractByte),
              (∀ ch ∈ l, allBytesInitialized ch = true) →
                allBytesInitialized l.flatten = true := by
            intro l
            induction l with
            | nil => intro _; rfl
            | cons c cs ih =>
              intro hcs
              exact allBytesInitialized_append (hcs c List.mem_cons_self)
                (ih (fun d hd => hcs d (List.mem_cons_of_mem _ hd)))
          have hall := hall_flat _ hall_chunks
          rw [hflat] at hall
          rw [hall] at hi
          cases hi
  · rintro ⟨hlen, hinit⟩
    obtain ⟨sz, hsz, hfrom⟩ := array_uint_isFromBytes layouts w n idx
    rw [rigidTyByteSize_array_uint] at hsz
    have hsz' : sz = MirValueCodec.uintByteSize w * n := Option.some.inj hsz.symm
    subst hsz'
    obtain ⟨v, hv⟩ := hfrom bs hlen hinit
    exact ⟨MirValueCodec.uintByteSize w * n, v, rigidTyByteSize_array_uint layouts w n idx,
      hlen, hv⟩

/-- Exact `ByteSeqValid` characterization for signed integer arrays `[iN; n]` (including `n = 0`):
a byte sequence is `.BitValid` iff it has byte length `intByteSize w * n` and no `.uninit` bytes. -/
theorem byteSeqValid_bitValid_array_int_iff (layouts : LayoutTable) (w : IntTy) (n : Nat)
    (idx : LayoutIdx) (bs : List AbstractByte) :
    ByteSeqValid layouts { kind := .array (.int w) n, layoutIdx := idx } .BitValid bs ↔
      bs.length = MirValueCodec.intByteSize w * n ∧ allBytesInitialized bs = true := by
  have hsz_ty : rigidTyByteSize layouts { kind := .array (.int w) n, layoutIdx := idx } =
      some (MirValueCodec.intByteSize w * n) := by
    unfold rigidTyByteSize rigidTyKindByteSize
    cases w <;> rfl
  constructor
  · rintro ⟨sz, v, hsz, hlen, hdec⟩
    rw [hsz_ty] at hsz
    have hsz' : sz = MirValueCodec.intByteSize w * n := Option.some.inj hsz.symm
    subst hsz'
    rw [seqLength_eq] at hlen
    refine ⟨hlen, ?_⟩
    cases n with
    | zero =>
      have hbs : bs = [] := List.length_eq_zero_iff.1 (by simpa using hlen)
      subst hbs; rfl
    | succ k =>
      cases hi : allBytesInitialized bs with
      | true => rfl
      | false =>
        exfalso
        have hnz := MirValueCodec.intByteSize_pos w
        have hne : Nat.beq (k + 1) 0 = false := rfl
        have hksz : rigidTyKindByteSize (.int w) = some (MirValueCodec.intByteSize w) := by
          cases w <;> rfl
        have hbeq : Nat.beq (Trusted.Sequence.length bs)
            (Nat.mul (MirValueCodec.intByteSize w) (k + 1)) = true := by
          rw [seqLength_eq, natMul_eq, hlen]
          exact nat_beq_self _
        unfold defaultCodecFuel decodeValueFromBytes at hdec
        dsimp only at hdec
        rw [hne] at hdec; dsimp only at hdec
        rw [hksz] at hdec; dsimp only at hdec
        rw [hbeq] at hdec; dsimp only at hdec
        cases hch : decodeArrayChunksWith
            (fun ch => decodeValueFromBytes 15 layouts { kind := .int w, layoutIdx := 0 } ch)
            (MirValueCodec.intByteSize w) (k + 1) bs with
        | none => rw [hch] at hdec; cases hdec
        | some vs =>
          have hmap := ((decodeArrayChunksWith_eq_some_iff _ hnz (k + 1) bs vs).1 hch).2
          have hflat : (Anneal.ListChunks.chunksOf (MirValueCodec.intByteSize w) bs).flatten = bs :=
            Anneal.ListChunks.chunksOf_flatten hnz bs
          have hall_chunks : ∀ ch ∈ Anneal.ListChunks.chunksOf (MirValueCodec.intByteSize w) bs,
              allBytesInitialized ch = true := by
            intro ch hmem
            have hsome : decodeValueFromBytes 15 layouts { kind := .int w, layoutIdx := 0 } ch ∈
                vs.map some := by
              rw [← hmap]; exact List.mem_map_of_mem hmem
            obtain ⟨y, _, hy⟩ := List.mem_map.1 hsome
            cases hci : allBytesInitialized ch with
            | true => rfl
            | false =>
              exfalso
              have h15 : decodeValueFromBytes 15 layouts { kind := .int w, layoutIdx := 0 } ch =
                  decodeValueFromBytes defaultCodecFuel layouts
                    { kind := .int w, layoutIdx := 0 } ch := by
                cases w <;> rfl
              rw [h15, decodeValueFromBytes_bitVec_int,
                bitVecLE_decode_eq_none_of_uninit _ hnz hci] at hy
              cases hy
          have hall_flat : ∀ l : List (List AbstractByte),
              (∀ ch ∈ l, allBytesInitialized ch = true) →
                allBytesInitialized l.flatten = true := by
            intro l
            induction l with
            | nil => intro _; rfl
            | cons c cs ih =>
              intro hcs
              exact allBytesInitialized_append (hcs c List.mem_cons_self)
                (ih (fun d hd => hcs d (List.mem_cons_of_mem _ hd)))
          have hall := hall_flat _ hall_chunks
          rw [hflat] at hall
          rw [hall] at hi
          cases hi
  · rintro ⟨hlen, hinit⟩
    obtain ⟨sz, hsz, hfrom⟩ := array_int_isFromBytes layouts w n idx
    rw [hsz_ty] at hsz
    have hsz' : sz = MirValueCodec.intByteSize w * n := Option.some.inj hsz.symm
    subst hsz'
    obtain ⟨v, hv⟩ := hfrom bs hlen hinit
    exact ⟨MirValueCodec.intByteSize w * n, v, hsz_ty, hlen, hv⟩

/-- Every element-wise `bitVecLE` encoding of a `[uN; n]` array satisfies `ByteSeqValid` in all
four validity modes (`.BitValid`, `.Initialized`, `.AsInitialized`, `.Uninit`). -/
theorem byteSeqValid_encodeElems_bitVecLE (layouts : LayoutTable) (w : UintTy) (idx : LayoutIdx)
    (xs : List (BitVec (8 * MirValueCodec.uintByteSize w))) :
    let ty : Ty := { kind := .array (.uint w) xs.length, layoutIdx := idx }
    let bs := (bitVecLE (MirValueCodec.uintByteSize w) (MirValueCodec.uintByteSize_pos w)).encodeElems xs
    ByteSeqValid layouts ty .BitValid bs ∧
      ByteSeqValid layouts ty .Initialized bs ∧
      ByteSeqValid layouts ty .AsInitialized bs ∧
      ByteSeqValid layouts ty .Uninit bs := by
  have hlen : ((bitVecLE (MirValueCodec.uintByteSize w)
      (MirValueCodec.uintByteSize_pos w)).encodeElems xs).length =
      MirValueCodec.uintByteSize w * xs.length := by
    rw [FixedByteCodec.length_encodeElems, Nat.mul_comm]
  have hinit : allBytesInitialized ((bitVecLE (MirValueCodec.uintByteSize w)
      (MirValueCodec.uintByteSize_pos w)).encodeElems xs) = true :=
    FixedByteCodec.allBytesInitialized_encodeElems
      (bitVecLE_isInitCodec (MirValueCodec.uintByteSize w) (MirValueCodec.uintByteSize_pos w)) xs
  have hbv : ByteSeqValid layouts { kind := .array (.uint w) xs.length, layoutIdx := idx }
      .BitValid ((bitVecLE (MirValueCodec.uintByteSize w)
        (MirValueCodec.uintByteSize_pos w)).encodeElems xs) :=
    (byteSeqValid_bitValid_array_uint_iff layouts w xs.length idx _).2 ⟨hlen, hinit⟩
  exact ⟨hbv,
    ⟨MirValueCodec.uintByteSize w * xs.length, rigidTyByteSize_array_uint layouts w xs.length idx,
      hlen, hinit⟩,
    byteSeqValid_bitValid_implies_asInitialized layouts _ _ hbv,
    byteSeqValid_bitValid_implies_uninit layouts _ _ hbv⟩

/-- Every element-wise `bitVecLE` encoding of a `[iN; n]` array satisfies `ByteSeqValid` in all
four validity modes (`.BitValid`, `.Initialized`, `.AsInitialized`, `.Uninit`). -/
theorem byteSeqValid_encodeElems_bitVecLE_int (layouts : LayoutTable) (w : IntTy) (idx : LayoutIdx)
    (xs : List (BitVec (8 * MirValueCodec.intByteSize w))) :
    let ty : Ty := { kind := .array (.int w) xs.length, layoutIdx := idx }
    let bs := (bitVecLE (MirValueCodec.intByteSize w) (MirValueCodec.intByteSize_pos w)).encodeElems xs
    ByteSeqValid layouts ty .BitValid bs ∧
      ByteSeqValid layouts ty .Initialized bs ∧
      ByteSeqValid layouts ty .AsInitialized bs ∧
      ByteSeqValid layouts ty .Uninit bs := by
  have hsz_ty : rigidTyByteSize layouts { kind := .array (.int w) xs.length, layoutIdx := idx } =
      some (MirValueCodec.intByteSize w * xs.length) := by
    unfold rigidTyByteSize rigidTyKindByteSize
    cases w <;> rfl
  have hlen : ((bitVecLE (MirValueCodec.intByteSize w)
      (MirValueCodec.intByteSize_pos w)).encodeElems xs).length =
      MirValueCodec.intByteSize w * xs.length := by
    rw [FixedByteCodec.length_encodeElems, Nat.mul_comm]
  have hinit : allBytesInitialized ((bitVecLE (MirValueCodec.intByteSize w)
      (MirValueCodec.intByteSize_pos w)).encodeElems xs) = true :=
    FixedByteCodec.allBytesInitialized_encodeElems
      (bitVecLE_isInitCodec (MirValueCodec.intByteSize w) (MirValueCodec.intByteSize_pos w)) xs
  have hbv : ByteSeqValid layouts { kind := .array (.int w) xs.length, layoutIdx := idx }
      .BitValid ((bitVecLE (MirValueCodec.intByteSize w)
        (MirValueCodec.intByteSize_pos w)).encodeElems xs) :=
    (byteSeqValid_bitValid_array_int_iff layouts w xs.length idx _).2 ⟨hlen, hinit⟩
  exact ⟨hbv, ⟨MirValueCodec.intByteSize w * xs.length, hsz_ty, hlen, hinit⟩,
    byteSeqValid_bitValid_implies_asInitialized layouts _ _ hbv,
    byteSeqValid_bitValid_implies_uninit layouts _ _ hbv⟩

/-! ## 15. Sharpened `cttz` / `evalCttzNonzero` Tnum, Signed Saturating Clamping, `ctpop`, and Core Unchecked/Three-Way Intrinsics -/

/-- `evalBswap` is an involution up to `wrapScalarBits` normalization on arbitrary (possibly
non-canonical) bits, matching `evalBitreverse_evalBitreverse`. -/
theorem evalBswap_evalBswap_general {sz : Nat} (hsz : 0 < sz) (bits : Nat) :
    (evalBswap ⟨bits, sz⟩).bind evalBswap =
      some ⟨wrapScalarBits bits (scalarModulus sz), sz⟩ := by
  rw [evalBswap_eq_bswapBytes hsz, Option.bind_some, evalBswap_eq_bswapBytes hsz,
    ofNat_toNat_self, Anneal.BitVecArith.bswapBytes_bswapBytes, wrapScalarBits_eq_toNat]

/-- Recursive characterization of `b % 2 ^ (k + 1) = 0` in terms of `b % 2` and `b / 2`. -/
theorem mod_two_pow_succ_eq_zero_iff (k b : Nat) :
    b % 2 ^ (k + 1) = 0 ↔ b % 2 = 0 ∧ (b / 2) % 2 ^ k = 0 := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hpow]
  constructor
  · intro h
    have h2 : b % 2 = 0 := by
      have hdvd : 2 ∣ 2 * 2 ^ k := ⟨2 ^ k, rfl⟩
      rw [← Nat.mod_mod_of_dvd b hdvd, h]
    have hdiv : (b / 2) % 2 ^ k = 0 := by
      rw [← Nat.mod_mul_left_div_self, Nat.mul_comm _ 2, h]
    exact ⟨h2, hdiv⟩
  · rintro ⟨h2, hdiv⟩
    have h1 := (Nat.div_add_mod b 2).symm
    have h3 := (Nat.div_add_mod (b / 2) (2 ^ k)).symm
    rw [h2, Nat.add_zero] at h1
    rw [hdiv, Nat.add_zero] at h3
    rw [h1, h3, ← Nat.mul_assoc, Nat.mul_mod_right]

/-- `cttzLoop w v` never exceeds `w` (for every `w`, including `w = 0`). -/
theorem cttzLoop_le :
    ∀ (w v : Nat), Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop w v ≤ w
  | 0, _ => Nat.le_refl 0
  | k + 1, v => by
    unfold Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop
    rw [natMod_eq, natDiv_eq]
    cases Nat.beq (v % 2) 0 with
    | false => exact Nat.zero_le _
    | true =>
      dsimp only
      rw [natAdd_eq]
      have ih := cttzLoop_le k (v / 2)
      omega

/-- Whenever `cttzLoop w v < w`, bit `cttzLoop w v` of `v` is set (`true`). -/
theorem testBit_cttzLoop_of_lt :
    ∀ (w v : Nat), Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop w v < w →
      v.testBit (Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop w v) = true
  | 0, _, h => by cases h
  | k + 1, v, h => by
    unfold Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop at h ⊢
    rw [natMod_eq, natDiv_eq] at h ⊢
    cases Nat.mod_two_eq_zero_or_one v with
    | inr h1 =>
      rw [h1]
      dsimp only
      rw [Nat.testBit_zero, h1]
      rfl
    | inl h0 =>
      rw [h0] at h ⊢
      dsimp only at h ⊢
      rw [natAdd_eq] at h ⊢
      have hcomm : 1 + Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop k (v / 2) =
          Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop k (v / 2) + 1 := Nat.add_comm _ _
      rw [hcomm, Nat.testBit_add_one]
      exact testBit_cttzLoop_of_lt k (v / 2) (by omega)

/-- `cttzLoop w v` equals the full width `w` iff the low `w` bits of `v` are all zero. -/
theorem cttzLoop_eq_width_iff :
    ∀ (w v : Nat), Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop w v = w ↔ v % 2 ^ w = 0
  | 0, v => by simp [Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop, Nat.mod_one]
  | k + 1, v => by
    unfold Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop
    rw [natMod_eq, natDiv_eq, mod_two_pow_succ_eq_zero_iff, ← cttzLoop_eq_width_iff k (v / 2)]
    cases Nat.mod_two_eq_zero_or_one v with
    | inl h0 =>
      rw [h0]
      dsimp only
      rw [natAdd_eq]
      omega
    | inr h1 =>
      rw [h1]
      dsimp only
      omega

/-- On a non-zero `8 * sz`-bit operand, `evalCttzNonzero` succeeds and returns `cttzLoop`, which is
strictly below `8 * sz` (holds for arbitrary, possibly non-canonical `bits`). -/
theorem evalCttzNonzero_eq_cttzLoop {sz retBytes : Nat} (hsz : 0 < sz) (hret : 0 < retBytes)
    {bits : Nat} (hne : BitVec.ofNat (8 * sz) bits ≠ BitVec.ofNat (8 * sz) 0) :
    evalCttzNonzero ⟨bits, sz⟩ retBytes =
        some ⟨Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop (8 * sz)
          (BitVec.ofNat (8 * sz) bits).toNat, retBytes⟩ ∧
      Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop (8 * sz)
        (BitVec.ofNat (8 * sz) bits).toNat < 8 * sz := by
  have hnz : Nat.beq (BitVec.ofNat (8 * sz) bits).toNat 0 = false :=
    nat_beq_eq_false_of_ne (fun hz =>
      hne (Anneal.BitVec.eq_of_toNat_eq (hz.trans (Anneal.BitVec.toNat_zero _).symm)))
  have hlt : Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop (8 * sz)
      (BitVec.ofNat (8 * sz) bits).toNat < 8 * sz := by
    apply Nat.lt_of_le_of_ne (cttzLoop_le _ _)
    intro heq
    have hmod := (cttzLoop_eq_width_iff (8 * sz) (BitVec.ofNat (8 * sz) bits).toNat).1 heq
    rw [Nat.mod_eq_of_lt (BitVec.ofNat (8 * sz) bits).isLt] at hmod
    exact hne (Anneal.BitVec.eq_of_toNat_eq (hmod.trans (Anneal.BitVec.toNat_zero _).symm))
  refine ⟨?_, hlt⟩
  unfold evalCttzNonzero
  simp only [beq_zero_of_pos hsz, beq_zero_of_pos hret, Bool.or_false, wrapScalarBits_eq_toNat,
    hnz, natMul_eight]

/-- Sharpened `(k + 1)`-bit `ScalarTnum` from `evalCttz`: whenever `evalCttz x retBytes = some ⟨k, _⟩`
with `k < 8 * sz`, not only are bits `0 .. k - 1` zero, bit `k` itself is `1`, pinning all low
`k + 1` bits to `2 ^ k` (`MaskEq (not (lowMask (8 * sz) (k + 1))) x (2 ^ k)`). -/
theorem scalarTnum_exact_lowMask_of_evalCttz {sz retBytes k : Nat} (hsz : 0 < sz)
    (hret : 0 < retBytes) {x : ScalarInt} (hszx : x.sizeBytes = sz)
    (hcan : x.bits < scalarModulus sz) (hcttz : evalCttz x retBytes = some ⟨k, retBytes⟩)
    (hlt : k < 8 * sz) :
    ScalarTnum sz (Anneal.BitVec.not (Anneal.BitVec.lowMask (8 * sz) (k + 1)))
        (BitVec.ofNat (8 * sz) (2 ^ k)) x ∧
      x.bits % 2 ^ k = 0 ∧ x.bits ≠ 0 := by
  have ⟨_, hmod⟩ := scalarTnum_lowMask_of_evalCttz hsz hret hszx hcan hcttz
  obtain ⟨xb, xs⟩ := x
  dsimp only at hszx hcan hcttz hmod ⊢
  subst xs
  unfold evalCttz at hcttz
  simp only [beq_zero_of_pos hsz, beq_zero_of_pos hret, Bool.or_false, natMul_eight,
    wrapScalarBits_of_lt hcan] at hcttz
  have hk : Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop (8 * sz) xb = k :=
    (ScalarInt.mk.inj (Option.some.inj hcttz)).1
  have hbitk : xb.testBit k = true := by
    rw [← hk]
    exact testBit_cttzLoop_of_lt (8 * sz) xb (hk ▸ hlt)
  have hlow : ∀ j, j < k → xb.testBit j = false := fun j hj =>
    testBit_false_of_lt_cttzLoop (8 * sz) xb j (hk.symm ▸ hj)
  have hpow_lt : 2 ^ k < 2 ^ (8 * sz) := Nat.pow_lt_pow_right (by decide) hlt
  have hnz : xb ≠ 0 := by
    intro hz
    subst hz
    rw [Nat.zero_testBit] at hbitk
    cases hbitk
  refine ⟨⟨rfl, hcan, Anneal.BitVec.maskEq_iff_getLsbD.2 (fun i hi hm => ?_)⟩, hmod, hnz⟩
  rw [Anneal.BitVec.getLsbD_not_of_lt _ hi, Anneal.BitVec.getLsbD_lowMask hi] at hm
  have hik : i < k + 1 := by
    cases hdec : decide (i < k + 1) with
    | true => exact of_decide_eq_true hdec
    | false => rw [hdec] at hm; cases hm
  show (BitVec.ofNat (8 * sz) xb).toNat.testBit i =
    (BitVec.ofNat (8 * sz) (2 ^ k)).toNat.testBit i
  rw [toNat_ofNat_of_lt hcan, _root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpow_lt,
    Nat.testBit_two_pow]
  cases Nat.lt_or_ge i k with
  | inl hik' =>
    have hne : k ≠ i := Nat.ne_of_gt hik'
    simp [hne, hlow i hik']
  | inr hge =>
    have heq : i = k := by omega
    subst heq
    simp [hbitk]

/-- `evalCttzNonzero` automatically guarantees `k < 8 * sz` and therefore always yields the sharp
`(k + 1)`-bit `ScalarTnum` (`bits 0 .. k - 1 = 0` and `bit k = 1`), `2^k`-alignment, and `x.bits ≠ 0`. -/
theorem scalarTnum_of_evalCttzNonzero {sz retBytes k : Nat} (hsz : 0 < sz) (hret : 0 < retBytes)
    {x : ScalarInt} (hszx : x.sizeBytes = sz) (hcan : x.bits < scalarModulus sz)
    (hcttz : evalCttzNonzero x retBytes = some ⟨k, retBytes⟩) :
    k < 8 * sz ∧
      ScalarTnum sz (Anneal.BitVec.not (Anneal.BitVec.lowMask (8 * sz) (k + 1)))
        (BitVec.ofNat (8 * sz) (2 ^ k)) x ∧
      x.bits % 2 ^ k = 0 ∧ x.bits ≠ 0 := by
  obtain ⟨xb, xs⟩ := x
  dsimp only at hszx hcan hcttz ⊢
  subst xs
  have hne : BitVec.ofNat (8 * sz) xb ≠ BitVec.ofNat (8 * sz) 0 := by
    intro hz
    rw [(evalCttzNonzero_eq_none_iff hsz hret xb).2 hz] at hcttz
    cases hcttz
  have ⟨hev, hlt_loop⟩ := evalCttzNonzero_eq_cttzLoop hsz hret hne
  rw [hev] at hcttz
  have hk : Trusted.Rustc.V2026_06_01.MirSemantics.cttzLoop (8 * sz)
      (BitVec.ofNat (8 * sz) xb).toNat = k :=
    (ScalarInt.mk.inj (Option.some.inj hcttz)).1
  have hlt : k < 8 * sz := hk ▸ hlt_loop
  rw [toNat_ofNat_of_lt hcan] at hk
  have hev_cttz : evalCttz ⟨xb, sz⟩ retBytes = some ⟨k, retBytes⟩ := by
    unfold evalCttz
    simp only [beq_zero_of_pos hsz, beq_zero_of_pos hret, Bool.or_false, natMul_eight,
      wrapScalarBits_of_lt hcan, hk]
  exact ⟨hlt, scalarTnum_exact_lowMask_of_evalCttz hsz hret rfl hcan hev_cttz hlt⟩

/-- `evalSaturatingAdd` fails iff the left operand is zero-width or the operand byte widths differ. -/
theorem evalSaturatingAdd_eq_none_iff (lhs rhs : ScalarInt) (isSigned : Bool) :
    evalSaturatingAdd lhs rhs isSigned = none ↔
      lhs.sizeBytes = 0 ∨ lhs.sizeBytes ≠ rhs.sizeBytes := by
  unfold evalSaturatingAdd
  cases h0 : Nat.beq lhs.sizeBytes 0 with
  | true =>
    rw [Bool.true_or]
    exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h0), fun _ => rfl⟩
  | false =>
    have hnz : lhs.sizeBytes ≠ 0 := fun h => by rw [h] at h0; nomatch h0
    cases heq : Nat.beq lhs.sizeBytes rhs.sizeBytes with
    | false =>
      have hne : lhs.sizeBytes ≠ rhs.sizeBytes := fun h => by
        rw [h, Nat.beq_refl] at heq; nomatch heq
      rw [Bool.false_or, Bool.not_false]
      exact ⟨fun _ => Or.inr hne, fun _ => rfl⟩
    | true =>
      have hsz_eq : lhs.sizeBytes = rhs.sizeBytes := Nat.eq_of_beq_eq_true heq
      rw [Bool.false_or, Bool.not_true]
      dsimp only
      refine ⟨fun h => ?_, fun h => ?_⟩
      · cases isSigned with
        | false =>
          cases hb : Nat.ble (scalarModulus lhs.sizeBytes)
            (Nat.add (wrapScalarBits lhs.bits (scalarModulus lhs.sizeBytes))
              (wrapScalarBits rhs.bits (scalarModulus lhs.sizeBytes))) <;>
            rw [hb] at h <;> cases h
        | true =>
          cases ho : signedOverflowAdd (wrapScalarBits lhs.bits (scalarModulus lhs.sizeBytes))
            (wrapScalarBits rhs.bits (scalarModulus lhs.sizeBytes)) lhs.sizeBytes with
          | false => rw [ho] at h; cases h
          | true =>
            rw [ho] at h
            cases hn : isSignedNegative (wrapScalarBits lhs.bits (scalarModulus lhs.sizeBytes))
              lhs.sizeBytes <;> rw [hn] at h <;> cases h
      · rcases h with hz | hne
        · exact absurd hz hnz
        · exact absurd hsz_eq hne

/-- `evalSaturatingSub` fails iff the left operand is zero-width or the operand byte widths differ. -/
theorem evalSaturatingSub_eq_none_iff (lhs rhs : ScalarInt) (isSigned : Bool) :
    evalSaturatingSub lhs rhs isSigned = none ↔
      lhs.sizeBytes = 0 ∨ lhs.sizeBytes ≠ rhs.sizeBytes := by
  unfold evalSaturatingSub
  cases h0 : Nat.beq lhs.sizeBytes 0 with
  | true =>
    rw [Bool.true_or]
    exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h0), fun _ => rfl⟩
  | false =>
    have hnz : lhs.sizeBytes ≠ 0 := fun h => by rw [h] at h0; nomatch h0
    cases heq : Nat.beq lhs.sizeBytes rhs.sizeBytes with
    | false =>
      have hne : lhs.sizeBytes ≠ rhs.sizeBytes := fun h => by
        rw [h, Nat.beq_refl] at heq; nomatch heq
      rw [Bool.false_or, Bool.not_false]
      exact ⟨fun _ => Or.inr hne, fun _ => rfl⟩
    | true =>
      have hsz_eq : lhs.sizeBytes = rhs.sizeBytes := Nat.eq_of_beq_eq_true heq
      rw [Bool.false_or, Bool.not_true]
      dsimp only
      refine ⟨fun h => ?_, fun h => ?_⟩
      · cases isSigned with
        | false =>
          cases hb : Nat.ble (wrapScalarBits rhs.bits (scalarModulus lhs.sizeBytes))
            (wrapScalarBits lhs.bits (scalarModulus lhs.sizeBytes)) <;>
            rw [hb] at h <;> cases h
        | true =>
          cases ho : signedOverflowSub (wrapScalarBits lhs.bits (scalarModulus lhs.sizeBytes))
            (wrapScalarBits rhs.bits (scalarModulus lhs.sizeBytes)) lhs.sizeBytes with
          | false => rw [ho] at h; cases h
          | true =>
            rw [ho] at h
            cases hn : isSignedNegative (wrapScalarBits lhs.bits (scalarModulus lhs.sizeBytes))
              lhs.sizeBytes <;> rw [hn] at h <;> cases h
      · rcases h with hz | hne
        · exact absurd hz hnz
        · exact absurd hsz_eq hne

/-- Signed `evalSaturatingAdd` under guaranteed signed underflow
(`signedKey a_hi + signedKey b_hi < 2^(8*sz - 1)`): clamps to `T::MIN = signBit` (`2^(8*sz - 1)`). -/
theorem scalarSRange_evalSaturatingAdd_underflow_clamps {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarSRange sz a_lo a_hi x) (hy : ScalarSRange sz b_lo b_hi y)
    (hudf : Anneal.BitVecArith.signedKey a_hi + Anneal.BitVecArith.signedKey b_hi <
      2 ^ (8 * sz - 1)) :
    evalSaturatingAdd x y true =
      some ⟨(Anneal.BitVecArith.signBit (w := 8 * sz)).toNat, sz⟩ := by
  obtain ⟨xb, rfl, hxb, _, hx₂⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, hyb, _, hy₂⟩ := scalarSRange_exists hy
  have hw : 0 < 8 * sz := by omega
  have hsum_lt : Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) xb) +
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) yb) < 2 ^ (8 * sz - 1) :=
    Nat.lt_of_le_of_lt (Nat.add_le_add hx₂ hy₂) hudf
  have hovf : signedOverflowAdd xb yb sz = true := by
    cases ho : signedOverflowAdd xb yb sz with
    | true => rfl
    | false =>
      have hb := (signedOverflowAdd_eq_false_iff_signedKey_bounds hsz xb yb).1 ho
      omega
  have hneg : isSignedNegative xb sz = true := by
    rw [Anneal.Scalars.isSignedNegative_eq_msb, ← msb_eq_core]
    cases hm : Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) xb) with
    | true => rfl
    | false =>
      have hge := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hm
      rw [natPow_eq] at hge
      omega
  unfold evalSaturatingAdd
  simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
    wrapScalarBits_of_lt hxb, wrapScalarBits_of_lt hyb, hovf, hneg]
  rw [Anneal.Scalars.signedHalfModulus_eq_two_pow hsz,
    Anneal.BitVecArith.toNat_signBit_of_pos hw, natPow_eq]

/-- Signed `evalSaturatingAdd` under guaranteed signed overflow
(`2^(8*sz - 1) + 2^(8*sz) ≤ signedKey a_lo + signedKey b_lo`): clamps to `T::MAX = 2^(8*sz - 1) - 1`. -/
theorem scalarSRange_evalSaturatingAdd_overflow_clamps {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarSRange sz a_lo a_hi x) (hy : ScalarSRange sz b_lo b_hi y)
    (hovf_in : 2 ^ (8 * sz - 1) + 2 ^ (8 * sz) ≤
      Anneal.BitVecArith.signedKey a_lo + Anneal.BitVecArith.signedKey b_lo) :
    evalSaturatingAdd x y true = some ⟨2 ^ (8 * sz - 1) - 1, sz⟩ := by
  obtain ⟨xb, rfl, hxb, hx₁, _⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, _⟩ := scalarSRange_exists hy
  have hw : 0 < 8 * sz := by omega
  have hsum_ge : 2 ^ (8 * sz - 1) + 2 ^ (8 * sz) ≤
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) xb) +
        Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) yb) :=
    Nat.le_trans hovf_in (Nat.add_le_add hx₁ hy₁)
  have hovf : signedOverflowAdd xb yb sz = true := by
    cases ho : signedOverflowAdd xb yb sz with
    | true => rfl
    | false =>
      have hb := (signedOverflowAdd_eq_false_iff_signedKey_bounds hsz xb yb).1 ho
      omega
  have hneg : isSignedNegative xb sz = false := by
    rw [Anneal.Scalars.isSignedNegative_eq_msb, ← msb_eq_core]
    cases hm : Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) xb) with
    | false => rfl
    | true =>
      have hlt_x := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hm
      have hlt_y := Anneal.BitVecArith.signedKey_lt (BitVec.ofNat (8 * sz) yb)
      rw [natPow_eq] at hlt_x hlt_y
      omega
  unfold evalSaturatingAdd
  simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
    wrapScalarBits_of_lt hxb, wrapScalarBits_of_lt hyb, hovf, hneg]
  rw [Anneal.Scalars.signedHalfModulus_eq_two_pow hsz, natSub_eq]

/-- Signed `evalSaturatingSub` under guaranteed signed underflow
(`signedKey a_hi + 2^(8*sz - 1) < signedKey b_lo`): clamps to `T::MIN = signBit` (`2^(8*sz - 1)`). -/
theorem scalarSRange_evalSaturatingSub_underflow_clamps {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarSRange sz a_lo a_hi x) (hy : ScalarSRange sz b_lo b_hi y)
    (hudf : Anneal.BitVecArith.signedKey a_hi + 2 ^ (8 * sz - 1) <
      Anneal.BitVecArith.signedKey b_lo) :
    evalSaturatingSub x y true =
      some ⟨(Anneal.BitVecArith.signBit (w := 8 * sz)).toNat, sz⟩ := by
  obtain ⟨xb, rfl, hxb, _, hx₂⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, hyb, hy₁, _⟩ := scalarSRange_exists hy
  have hw : 0 < 8 * sz := by omega
  have hpow : 2 ^ (8 * sz) = 2 * 2 ^ (8 * sz - 1) := by
    have hw' : 8 * sz = (8 * sz - 1) + 1 := by omega
    conv => lhs; rw [hw']
    rw [Nat.pow_succ, Nat.mul_comm]
  have hx₂' : Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) xb) ≤
      Anneal.BitVecArith.signedKey a_hi := hx₂
  have hy₁' : Anneal.BitVecArith.signedKey b_lo ≤
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) yb) := hy₁
  have hovf : signedOverflowSub xb yb sz = true := by
    cases ho : signedOverflowSub xb yb sz with
    | true => rfl
    | false =>
      have hb := (signedOverflowSub_eq_false_iff_signedKey_bounds hsz xb yb).1 ho
      omega
  have hneg : isSignedNegative xb sz = true := by
    rw [Anneal.Scalars.isSignedNegative_eq_msb, ← msb_eq_core]
    cases hm : Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) xb) with
    | true => rfl
    | false =>
      have hge := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hm
      have hlt_y := Anneal.BitVecArith.signedKey_lt (BitVec.ofNat (8 * sz) yb)
      rw [natPow_eq] at hge hlt_y
      omega
  unfold evalSaturatingSub
  simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
    wrapScalarBits_of_lt hxb, wrapScalarBits_of_lt hyb, hovf, hneg]
  rw [Anneal.Scalars.signedHalfModulus_eq_two_pow hsz,
    Anneal.BitVecArith.toNat_signBit_of_pos hw, natPow_eq]

/-- Signed `evalSaturatingSub` under guaranteed signed overflow
(`signedKey b_hi + 2^(8*sz - 1) ≤ signedKey a_lo`): clamps to `T::MAX = 2^(8*sz - 1) - 1`. -/
theorem scalarSRange_evalSaturatingSub_overflow_clamps {sz : Nat} (hsz : 0 < sz)
    {a_lo a_hi b_lo b_hi : BitVec (8 * sz)} {x y : ScalarInt}
    (hx : ScalarSRange sz a_lo a_hi x) (hy : ScalarSRange sz b_lo b_hi y)
    (hovf_in : Anneal.BitVecArith.signedKey b_hi + 2 ^ (8 * sz - 1) ≤
      Anneal.BitVecArith.signedKey a_lo) :
    evalSaturatingSub x y true = some ⟨2 ^ (8 * sz - 1) - 1, sz⟩ := by
  obtain ⟨xb, rfl, hxb, hx₁, _⟩ := scalarSRange_exists hx
  obtain ⟨yb, rfl, hyb, _, hy₂⟩ := scalarSRange_exists hy
  have hw : 0 < 8 * sz := by omega
  have hx₁' : Anneal.BitVecArith.signedKey a_lo ≤
      Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) xb) := hx₁
  have hy₂' : Anneal.BitVecArith.signedKey (BitVec.ofNat (8 * sz) yb) ≤
      Anneal.BitVecArith.signedKey b_hi := hy₂
  have hovf : signedOverflowSub xb yb sz = true := by
    cases ho : signedOverflowSub xb yb sz with
    | true => rfl
    | false =>
      have hb := (signedOverflowSub_eq_false_iff_signedKey_bounds hsz xb yb).1 ho
      omega
  have hneg : isSignedNegative xb sz = false := by
    rw [Anneal.Scalars.isSignedNegative_eq_msb, ← msb_eq_core]
    cases hm : Anneal.BitVecArith.msb (BitVec.ofNat (8 * sz) xb) with
    | false => rfl
    | true =>
      have hlt_x := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hm
      rw [natPow_eq] at hlt_x
      omega
  unfold evalSaturatingSub
  simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
    wrapScalarBits_of_lt hxb, wrapScalarBits_of_lt hyb, hovf, hneg]
  rw [Anneal.Scalars.signedHalfModulus_eq_two_pow hsz, natSub_eq]

/-- `ctpopLoop w b` never exceeds `w` (for every `w`, including `w = 0`). -/
theorem ctpopLoop_le :
    ∀ (w b : Nat), Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop w b ≤ w
  | 0, _ => Nat.le_refl 0
  | k + 1, b => by
    have hstep : Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop (k + 1) b =
        b % 2 + Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop k (b / 2) := rfl
    have hmod : b % 2 < 2 := Nat.mod_lt b (by decide)
    have ih := ctpopLoop_le k (b / 2)
    rw [hstep]
    omega

/-- `ctpopLoop w b` is zero iff the low `w` bits of `b` are all zero. -/
theorem ctpopLoop_eq_zero_iff :
    ∀ (w b : Nat), Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop w b = 0 ↔ b % 2 ^ w = 0
  | 0, b => by simp [Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop, Nat.mod_one]
  | k + 1, b => by
    have hstep : Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop (k + 1) b =
        b % 2 + Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop k (b / 2) := rfl
    rw [hstep, mod_two_pow_succ_eq_zero_iff, ← ctpopLoop_eq_zero_iff k (b / 2)]
    omega

/-- Complement population-count helper on natural numbers below `2 ^ w`. -/
theorem ctpopLoop_sub_one :
    ∀ (w b : Nat), b < 2 ^ w →
      Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop w (2 ^ w - 1 - b) +
        Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop w b = w
  | 0, b, _ => rfl
  | k + 1, b, hb => by
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hstep1 : Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop (k + 1)
          (2 ^ (k + 1) - 1 - b) =
        (2 ^ (k + 1) - 1 - b) % 2 +
          Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop k ((2 ^ (k + 1) - 1 - b) / 2) := rfl
    have hstep2 : Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop (k + 1) b =
        b % 2 + Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop k (b / 2) := rfl
    have hdiv : (2 ^ (k + 1) - 1 - b) / 2 = 2 ^ k - 1 - b / 2 := by omega
    have hmod_sum : (2 ^ (k + 1) - 1 - b) % 2 + b % 2 = 1 := by omega
    have ih := ctpopLoop_sub_one k (b / 2) (by omega)
    rw [hstep1, hstep2, hdiv]
    omega

/-- Complement population-count identity on `BitVec w` (including `w = 0`):
`ctpopLoop w (~~~x) + ctpopLoop w x = w`. -/
theorem ctpopLoop_not {w : Nat} (x : BitVec w) :
    Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop w (Anneal.BitVec.not x).toNat +
      Trusted.Rustc.V2026_06_01.MirSemantics.ctpopLoop w x.toNat = w := by
  rw [Anneal.BitVecArith.toNat_not_eq_sub, natPow_eq]
  exact ctpopLoop_sub_one w x.toNat x.isLt

/-- `evalCtpop` fails iff the operand or return width is zero. -/
theorem evalCtpop_eq_none_iff (sc : ScalarInt) (retBytes : Nat) :
    evalCtpop sc retBytes = none ↔ sc.sizeBytes = 0 ∨ retBytes = 0 := by
  unfold evalCtpop
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
      · rcases h with h | h
        · exact absurd h hne
        · exact absurd h hne'

/-- On positive operand and return widths, `evalCtpop` succeeds with population count `≤ 8 * sz`. -/
theorem evalCtpop_bits_le {sz retBytes : Nat} (hsz : 0 < sz) (hret : 0 < retBytes) (bits : Nat) :
    ∃ r, evalCtpop ⟨bits, sz⟩ retBytes = some r ∧ r.bits ≤ 8 * sz ∧ r.sizeBytes = retBytes := by
  unfold evalCtpop
  simp only [beq_zero_of_pos hsz, beq_zero_of_pos hret, Bool.or_false, natMul_eight]
  exact ⟨_, rfl, ctpopLoop_le (8 * sz) _, rfl⟩

/-- On canonical scalars (including `sz = 0`), the core `unchecked_add` intrinsic `evalUncheckedAdd`
agrees identically with `Anneal.Scalars.evalBinOp .addUnchecked`. -/
theorem evalUncheckedAdd_eq_evalBinOp {sz : Nat} {a b : Nat}
    (ha : a < scalarModulus sz) (hb : b < scalarModulus sz) (isSigned : Bool) :
    evalUncheckedAdd ⟨a, sz⟩ ⟨b, sz⟩ isSigned =
      Anneal.Scalars.evalBinOp .addUnchecked ⟨a, sz⟩ ⟨b, sz⟩ isSigned := by
  cases Nat.eq_zero_or_pos sz with
  | inl hz => subst hz; rfl
  | inr hsz =>
    cases isSigned with
    | false =>
      rw [Anneal.Scalars.evalBinOp_addUnchecked_apply_unsigned hsz]
      unfold evalUncheckedAdd
      dsimp only
      simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
        wrapScalarBits_of_lt ha, wrapScalarBits_of_lt hb]
      simp only [scalarModulus_eq, natAdd_eq]
      cases Nat.ble (2 ^ (8 * sz)) (a + b) <;> rfl
    | true =>
      rw [Anneal.Scalars.evalBinOp_addUnchecked_apply_signed hsz]
      unfold evalUncheckedAdd
      dsimp only
      simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
        wrapScalarBits_of_lt ha, wrapScalarBits_of_lt hb]
      simp only [natAdd_eq, Anneal.Scalars.wrapScalarBits_eq_mod_modulus, scalarModulus_eq]
      cases signedOverflowAdd a b sz <;> rfl

/-- On canonical scalars (including `sz = 0`), the core `unchecked_sub` intrinsic `evalUncheckedSub`
agrees identically with `Anneal.Scalars.evalBinOp .subUnchecked`. -/
theorem evalUncheckedSub_eq_evalBinOp {sz : Nat} {a b : Nat}
    (ha : a < scalarModulus sz) (hb : b < scalarModulus sz) (isSigned : Bool) :
    evalUncheckedSub ⟨a, sz⟩ ⟨b, sz⟩ isSigned =
      Anneal.Scalars.evalBinOp .subUnchecked ⟨a, sz⟩ ⟨b, sz⟩ isSigned := by
  cases Nat.eq_zero_or_pos sz with
  | inl hz => subst hz; rfl
  | inr hsz =>
    cases isSigned with
    | false =>
      rw [Anneal.Scalars.evalBinOp_subUnchecked_apply_unsigned hsz]
      unfold evalUncheckedSub
      dsimp only
      simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
        wrapScalarBits_of_lt ha, wrapScalarBits_of_lt hb]
      simp only [scalarModulus_eq, natSub_eq]
      cases hble : Nat.ble b a with
      | false =>
        have hnle : ¬ b ≤ a := fun h => by rw [Nat.ble_eq_true_of_le h] at hble; cases hble
        simp [hnle]
      | true =>
        have hle : b ≤ a := Nat.le_of_ble_eq_true hble
        simp only [hle, ↓reduceDIte]
        cases Nat.ble (2 ^ (8 * sz)) (a - b) <;> rfl
    | true =>
      rw [Anneal.Scalars.evalBinOp_subUnchecked_apply_signed hsz]
      unfold evalUncheckedSub
      dsimp only
      simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
        wrapScalarBits_of_lt ha, wrapScalarBits_of_lt hb]
      cases signedOverflowSub a b sz with
      | true => rfl
      | false =>
        dsimp only
        have ha' : a < 2 ^ (8 * sz) := by rwa [← scalarModulus_eq]
        have hb' : b < 2 ^ (8 * sz) := by rwa [← scalarModulus_eq]
        rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb']
        cases hble : Nat.ble b a with
        | false =>
          simp only [Anneal.Scalars.wrapScalarBits_eq_mod_modulus, scalarModulus_eq,
            natAdd_eq, natSub_eq]
        | true =>
          have hle : b ≤ a := Nat.le_of_ble_eq_true hble
          simp only [Anneal.Scalars.wrapScalarBits_eq_mod_modulus, scalarModulus_eq, natSub_eq]
          have heq : 2 ^ (8 * sz) + a - b = (a - b) + 2 ^ (8 * sz) := by omega
          rw [heq, Nat.add_mod_right]

/-- On canonical scalars (including `sz = 0`), the core `unchecked_mul` intrinsic `evalUncheckedMul`
agrees identically with `Anneal.Scalars.evalBinOp .mulUnchecked`. -/
theorem evalUncheckedMul_eq_evalBinOp {sz : Nat} {a b : Nat}
    (ha : a < scalarModulus sz) (hb : b < scalarModulus sz) (isSigned : Bool) :
    evalUncheckedMul ⟨a, sz⟩ ⟨b, sz⟩ isSigned =
      Anneal.Scalars.evalBinOp .mulUnchecked ⟨a, sz⟩ ⟨b, sz⟩ isSigned := by
  cases Nat.eq_zero_or_pos sz with
  | inl hz => subst hz; rfl
  | inr hsz =>
    cases isSigned with
    | false =>
      rw [Anneal.Scalars.evalBinOp_mulUnchecked_apply_unsigned hsz]
      unfold evalUncheckedMul
      dsimp only
      simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
        wrapScalarBits_of_lt ha, wrapScalarBits_of_lt hb]
      simp only [scalarModulus_eq, natMul_eq]
      cases Nat.ble (2 ^ (8 * sz)) (a * b) <;> rfl
    | true =>
      rw [Anneal.Scalars.evalBinOp_mulUnchecked_apply_signed hsz]
      unfold evalUncheckedMul
      dsimp only
      simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
        wrapScalarBits_of_lt ha, wrapScalarBits_of_lt hb]
      simp only [natMul_eq, Anneal.Scalars.wrapScalarBits_eq_mod_modulus, scalarModulus_eq]
      cases signedOverflowMul a b sz <;> rfl

/-- `evalUncheckedShl` triggers undefined behavior (`none`) whenever `rhsIsSigned = true` and the
shift operand has its sign bit set (`msb = true`, i.e., a negative shift amount). -/
theorem evalUncheckedShl_eq_none_of_msb_true (lhs rhs : ScalarInt)
    (hneg : Anneal.BitVecArith.msb (BitVec.ofNat (8 * rhs.sizeBytes) rhs.bits) = true) :
    evalUncheckedShl lhs rhs true = none := by
  unfold evalUncheckedShl
  cases h0 : Bool.or (Nat.beq lhs.sizeBytes 0) (Nat.beq rhs.sizeBytes 0) with
  | true => rfl
  | false =>
    dsimp only
    rw [Anneal.Scalars.isSignedNegative_wrapScalarBits, Anneal.Scalars.isSignedNegative_eq_msb,
      ← msb_eq_core, hneg, Bool.true_and, Bool.true_or]

/-- `evalUncheckedShr` triggers undefined behavior (`none`) whenever `rhsIsSigned = true` and the
shift operand has its sign bit set (`msb = true`, i.e., a negative shift amount). -/
theorem evalUncheckedShr_eq_none_of_msb_true (lhs rhs : ScalarInt) (lhsIsSigned : Bool)
    (hneg : Anneal.BitVecArith.msb (BitVec.ofNat (8 * rhs.sizeBytes) rhs.bits) = true) :
    evalUncheckedShr lhs rhs lhsIsSigned true = none := by
  unfold evalUncheckedShr
  cases h0 : Bool.or (Nat.beq lhs.sizeBytes 0) (Nat.beq rhs.sizeBytes 0) with
  | true => rfl
  | false =>
    dsimp only
    rw [Anneal.Scalars.isSignedNegative_wrapScalarBits, Anneal.Scalars.isSignedNegative_eq_msb,
      ← msb_eq_core, hneg, Bool.true_and, Bool.true_or]

/-- On canonical scalars (including `sz = 0`), `evalThreeWayCompare` agrees identically with
`Anneal.Scalars.evalBinOp .cmp` across both signednesses (`Ordering::Less = 255`,
`Ordering::Equal = 0`, `Ordering::Greater = 1`). -/
theorem evalThreeWayCompare_eq_evalBinOp_cmp {sz : Nat} {a b : Nat}
    (ha : a < scalarModulus sz) (hb : b < scalarModulus sz) (isSigned : Bool) :
    evalThreeWayCompare ⟨a, sz⟩ ⟨b, sz⟩ isSigned =
      Anneal.Scalars.evalBinOp .cmp ⟨a, sz⟩ ⟨b, sz⟩ isSigned := by
  cases Nat.eq_zero_or_pos sz with
  | inl hz => subst hz; rfl
  | inr hsz =>
    cases isSigned with
    | false =>
      rw [Anneal.Scalars.evalBinOp_cmp_unsigned hsz]
      unfold evalThreeWayCompare
      dsimp only
      simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
        wrapScalarBits_of_lt ha, wrapScalarBits_of_lt hb]
      cases Nat.beq a b <;> cases Nat.ble a b <;> rfl
    | true =>
      have ha' : a < 2 ^ (8 * sz) := by rwa [← scalarModulus_eq]
      have hb' : b < 2 ^ (8 * sz) := by rwa [← scalarModulus_eq]
      rw [Anneal.Scalars.evalBinOp_cmp_signed hsz]
      unfold evalThreeWayCompare
      dsimp only
      simp only [beq_zero_of_pos hsz, nat_beq_self, Bool.not_true, Bool.or_false,
        wrapScalarBits_of_lt ha, wrapScalarBits_of_lt hb, Nat.mod_eq_of_lt ha',
        Nat.mod_eq_of_lt hb', Anneal.Scalars.signedLt_eq_slt]
      cases Nat.beq a b <;> cases (BitVec.ofNat (8 * sz) a).slt (BitVec.ofNat (8 * sz) b) <;> rfl

end Anneal.BitVecScalarsBridge
