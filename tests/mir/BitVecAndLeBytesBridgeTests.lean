-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.BitVecScalarsBridge

namespace Anneal.BitVecAndLeBytesBridgeTests

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.BitValidity
open Anneal.ByteCodec
open Anneal.BitVecScalarsBridge

/-!
# Kernel-Checked Canaries for `Anneal.BitVecScalarsBridge`

End-to-end, non-vacuous checks that the bridge between the ported pure libraries
(`Anneal.BitVec`, `Anneal.BitVecArith`, `Anneal.LeBytes`, `Anneal.ListChunks`) and the MIR
semantics (`Trusted.Rustc.V2026_06_01.MirSemantics`, `Anneal.Scalars`, `Anneal.ByteCodec`,
`Anneal.BitValidity`) is usable on symbolic programs:

0. Edge regressions: zero widths, shifts past the width, non-canonical bits.
1. Canary 1: symbolic 32-bit / 64-bit tnum and interval pipelines through `evalWrappingAdd`,
   `evalWrappingSub`, `bitwiseAndBits`, `shiftRightUnsignedBits`, `arithmeticShrBits`,
   `evalBswap` and `evalCtlz`, range-to-prefix extraction, and empty-abstraction pruning.
2. Canary 2: symbolic 32-bit wire header `(version : 4, flags : 12, payloadLen : 16)` packed by
   shift-and-OR, with injectivity and exact field recovery.
3. Canary 3: `[u32; 4]` / `[u64; 2]` little-endian byte-chunk round trips and transmutation.
4. Canary 4: negative refutations (overlapping masks, malformed chunk buffers, `.uninit`).
5. Axiom audit guards.

Every hypothesis used by a symbolic canary is shown satisfiable by a concrete witness theorem
next to it, so no canary holds vacuously.
-/

/-! ## 0. Edge Regressions (zero widths, over-wide shifts, non-canonical bits) -/

/-- Width `0`: the `ctlz` kernel and the ported `clz` agree (both count zero bits). -/
theorem ctlz_width_zero :
    Trusted.Rustc.V2026_06_01.MirSemantics.ctlzBits 0 (BitVec.ofNat 0 5).toNat = 0 ∧
      Anneal.BitVec.clz (BitVec.ofNat 0 5) = 0 :=
  ⟨rfl, (ctlzBits_eq_clz (BitVec.ofNat 0 5)).symm.trans rfl⟩

/-- Width `0`: bitwise operations on out-of-range operands collapse to `0` on both sides of the
bridge. -/
theorem bitwise_width_zero :
    bitwiseAndBits 0 5 7 = 0 ∧ bitwiseOrBits 0 5 7 = 0 ∧ bitwiseXorBits 0 5 7 = 0 ∧
      (Anneal.BitVec.and (BitVec.ofNat 0 5) (BitVec.ofNat 0 7)).toNat = 0 :=
  ⟨rfl, rfl, rfl, (bitwiseAndBits_eq_and 0 5 7).symm.trans rfl⟩

/-- Byte width `0`: every scalar evaluator rejects, so the bridge theorems' `0 < sz` hypotheses
are necessary rather than cosmetic. -/
theorem evaluators_reject_size_zero (a b : Nat) :
    Anneal.Scalars.evalBinOp .bitAnd ⟨a, 0⟩ ⟨b, 0⟩ false = none ∧
      evalWrappingAdd ⟨a, 0⟩ ⟨b, 0⟩ = none ∧ evalWrappingSub ⟨a, 0⟩ ⟨b, 0⟩ = none ∧
      evalBswap ⟨a, 0⟩ = none ∧ evalCtlz ⟨a, 0⟩ = none ∧ evalCtlzNonzero ⟨a, 0⟩ = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Mismatched operand widths are rejected by the wrapping intrinsics. -/
theorem wrapping_rejects_mismatched_widths (a b : Nat) :
    evalWrappingAdd ⟨a, 4⟩ ⟨b, 8⟩ = none ∧ evalWrappingSub ⟨a, 4⟩ ⟨b, 8⟩ = none :=
  ⟨(evalWrappingAdd_eq_none_iff _ _).2 (Or.inr (show (4 : Nat) ≠ 8 by decide)),
    (evalWrappingSub_eq_none_iff _ _).2 (Or.inr (show (4 : Nat) ≠ 8 by decide))⟩

/-- Shift amounts at or past the bit width: the scalar shifts and the ported shifts agree on a
symbolic 32-bit operand (left and logical right shifts flush to `0`). -/
theorem shifts_past_width (a : Nat) :
    shiftLeftBits a 32 (scalarModulus 4) = 0 ∧
      shiftRightUnsignedBits (wrapScalarBits a (scalarModulus 4)) 40 = 0 := by
  constructor
  · rw [Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod, Nat.shiftLeft_eq]
    exact Nat.mul_mod_left _ _
  · have h := (BitVec.ofNat (8 * 4) a).isLt
    rw [wrapScalarBits_eq_toNat, Anneal.Scalars.shiftRightUnsignedBits_eq_shiftRight,
      Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (Nat.lt_trans h (by decide))

/-- Arithmetic shift past the width saturates at the sign fill, on both sides of the bridge:
`-1 >> 1000 = -1` and `1 >> 1000 = 0` at 8 bits. -/
theorem ashr_past_width :
    arithmeticShrBits 0xFF 1 1000 = 0xFF ∧ arithmeticShrBits 0x01 1 1000 = 0 ∧
      (Anneal.BitVecArith.ashr (BitVec.ofNat (8 * 1) 0xFF) 1000).toNat = 0xFF := by
  refine ⟨?_, ?_, ?_⟩
  · rw [arithmeticShrBits_of_width_le 0xFF 1 (by decide)]; rfl
  · rw [arithmeticShrBits_of_width_le 0x01 1 (by decide)]; rfl
  · rw [← arithmeticShrBits_eq_ashr, arithmeticShrBits_of_width_le 0xFF 1 (by decide)]; rfl

/-- Non-canonical bits: `evalBinOp .bitAnd`, `.add` and `.shl` canonicalize, and agree with the
ported operations on `BitVec.ofNat` of the raw bits (here `2^32 + 5` at 4 bytes). -/
theorem noncanonical_bits_canonicalized :
    Anneal.Scalars.evalBinOp .bitAnd ⟨4294967301, 4⟩ ⟨7, 4⟩ false = some ⟨5, 4⟩ ∧
      Anneal.Scalars.evalBinOp .add ⟨4294967301, 4⟩ ⟨1, 4⟩ false = some ⟨6, 4⟩ ∧
      Anneal.Scalars.evalBinOp .shl ⟨4294967301, 4⟩ ⟨1, 4⟩ false = some ⟨10, 4⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [evalBinOp_bitAnd_eq_and (by decide)]; rfl
  · rw [evalBinOp_add_eq_add (by decide)]; rfl
  · rw [evalBinOp_shl_eq_shl (by decide) (by decide)]; rfl

/-- Non-canonical bits: unsigned `evalBinOp .shr` does *not* canonicalize its left operand, so it
differs from the ported `ushr` of `BitVec.ofNat` of the raw bits. This is why
`evalBinOp_shr_unsigned_eq_ushr` requires a canonical operand; the unconditional bridge
`evalBinOp_shr_unsigned_eq_extractBits` (a 33-bit extraction here) still predicts the result. -/
theorem noncanonical_shr_differs :
    Anneal.Scalars.evalBinOp .shr ⟨4294967296, 4⟩ ⟨1, 4⟩ false = some ⟨2147483648, 4⟩ ∧
      (Anneal.BitVec.ushr (BitVec.ofNat (8 * 4) 4294967296) 1).toNat = 0 ∧
      (Anneal.BitVecArith.extractBits (BitVec.ofNat (8 * 4 + 1 % (8 * 4)) 4294967296)
        (1 % (8 * 4)) (8 * 4)).toNat = 2147483648 := by
  have h3 : (Anneal.BitVecArith.extractBits (BitVec.ofNat (8 * 4 + 1 % (8 * 4)) 4294967296)
      (1 % (8 * 4)) (8 * 4)).toNat = 2147483648 := by decide
  refine ⟨?_, by decide, h3⟩
  rw [evalBinOp_shr_unsigned_eq_extractBits (by decide) (by decide), h3]

/-- Non-canonical scalars are never abstracted: `2^32` at 4 bytes satisfies no tnum and lies in
no interval. -/
theorem noncanonical_not_abstracted (m v : BitVec (8 * 4)) :
    ¬ ScalarTnum 4 m v ⟨4294967296, 4⟩ ∧ ¬ ScalarRange 4 m v ⟨4294967296, 4⟩ :=
  ⟨fun h => absurd h.2.1 (by decide), fun h => absurd h.2.1 (by decide)⟩

/-- Symbolic non-canonical rejection: at *every* byte width `sz`, any scalar with
`bits ≥ scalarModulus sz` satisfies no `ScalarTnum`, `ScalarRange`, or `ScalarSRange`. -/
theorem noncanonical_not_abstracted_general (sz b : Nat) (hge : scalarModulus sz ≤ b)
    (m v : BitVec (8 * sz)) :
    ¬ ScalarTnum sz m v ⟨b, sz⟩ ∧ ¬ ScalarRange sz m v ⟨b, sz⟩ ∧
      ¬ ScalarSRange sz m v ⟨b, sz⟩ :=
  ⟨scalarTnum_not_noncanonical hge, scalarRange_not_noncanonical hge,
    scalarSRange_not_noncanonical hge⟩

/-- Non-canonical multiple of `2^32`: `evalCtlzNonzero` wraps `2^32` to `0` and returns `none`
(UB), and `evalBswap` on 64-bit concrete bytes matches `swapBytes64` and `bswap64`. -/
theorem ctlzNonzero_noncanonical_and_bswap64 :
    evalCtlzNonzero ⟨4294967296, 4⟩ = none ∧
      evalBswap ⟨0x0102030405060708, 8⟩ = some ⟨0x0807060504030201, 8⟩ ∧
      Anneal.Scalars.swapBytes64 0x0102030405060708 = 0x0807060504030201 ∧
      (Anneal.BitVecArith.bswap64 (BitVec.ofNat 64 0x0102030405060708)).toNat =
        0x0807060504030201 := by
  refine ⟨evalCtlzNonzero_eq_none_of_zero ⟨4294967296, 4⟩ 4 rfl, rfl, rfl, ?_⟩
  rw [toNat_bswap64]
  rfl

/-- Empty arrays (`n = 0`) round-trip through `encodeValueToBytes` / `decodeValueFromBytes` and
transmute soundly (`[u32; 0] → [u64; 0]`), and zero-width chunks (`n = 0`) demonstrate why
`0 < n` is necessary in `chunksOf_encodeElems` / `decodeChunks_eq_chunksOf` /
`decodeArrayChunksWith_eq_chunksOf`. -/
theorem zero_length_array_and_zero_width_chunk_edges (layouts : LayoutTable)
    (idx₁ idx₂ : LayoutIdx) :
    encodeValueToBytes defaultCodecFuel layouts { kind := .array (.uint .u32) 0, layoutIdx := idx₁ }
        (bitVecArrayValue 4 []) = some [] ∧
      decodeValueFromBytes defaultCodecFuel layouts
        { kind := .array (.uint .u32) 0, layoutIdx := idx₁ } [] = some (bitVecArrayValue 4 []) ∧
      (∃ v', decodeValueFromBytes defaultCodecFuel layouts
        { kind := .array (.uint .u64) 0, layoutIdx := idx₂ } [] = some v') ∧
      Anneal.ListChunks.chunksOf 0 (FixedByteCodec.unit.encodeElems [(), (), ()]) = [] ∧
      (FixedByteCodec.unit.decodeChunks 3 []).map Subtype.val = some [(), (), ()] ∧
      decodeArrayChunksWith (fun bs => match bs with | [] => some .unit | _ :: _ => none) 0 3 [] =
        some [.unit, .unit, .unit] :=
  ⟨encodeValueToBytes_bitVecArray layouts .u32 idx₁ [],
    decodeValueFromBytes_encodeElems_bitVecLE layouts .u32 idx₁ [],
    bitVecArray_transmute_sound layouts .u32 .u64 0 idx₁ idx₂ [] rfl,
    chunksOf_encodeElems_zero_width FixedByteCodec.unit [(), (), ()],
    decodeChunks_zero_width FixedByteCodec.unit rfl 3,
    decodeArrayChunksWith_zero_width
      (fun bs => match bs with | [] => some .unit | _ :: _ => none) rfl 3⟩

/-- Provenance edges: `decodeLittleEndianBytes` collapses provenance to `none` on `[]` while
preserving uniform provenance on non-empty lists; mixed-provenance initialized buffers still
decode through `decodeScalarBytes_of_init` to `fromLeBytes` of their extracted payload. -/
theorem provenance_byte_edges (b0 b1 : BitVec 8) :
    decodeLittleEndianBytes (([] : List (BitVec 8)).map (bvByteToAbstract (some (7, 1)))) =
        some (0, none) ∧
      decodeLittleEndianBytes ([b0, b1].map (bvByteToAbstract (some (7, 1)))) =
        some (Anneal.LeBytes.fromLeBytes [b0, b1], some (7, 1)) ∧
      (∃ prov, decodeScalarBytes
          [bvByteToAbstract (some (1, 0)) b0, bvByteToAbstract (some (2, 0)) b1] false =
        some (⟨Anneal.LeBytes.fromLeBytes [b0, b1], 2⟩, prov)) := by
  refine ⟨decodeLittleEndianBytes_map (some (7, 1)) [],
    decodeLittleEndianBytes_map (some (7, 1)) [b0, b1], ?_⟩
  have h := decodeScalarBytes_of_init
    (bs := [bvByteToAbstract (some (1, 0)) b0, bvByteToAbstract (some (2, 0)) b1])
    (by simp) rfl false
  simpa [extractInitBvBytes, bvByteToAbstract] using h

/-- Sign extension truncates when the destination is narrower, widens with the sign bit
otherwise, on a concrete negative byte and its 16-bit and 0-byte images. -/
theorem signExtend_edges :
    signExtendBits 0x80 1 2 = 0xFF80 ∧ signExtendBits 0x1234 2 1 = 0x34 ∧
      signExtendBits 0x80 1 0 = 0 ∧
      (Anneal.BitVecArith.signExtend (8 * 2) (BitVec.ofNat (8 * 1) 0x80)).toNat = 0xFF80 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [← signExtendBits_eq_signExtend]
  rfl

/-- Signed comparison bridge on concrete operands across the sign boundary. -/
theorem signed_compare_edges :
    signedLt 0x80 0x7F 1 = true ∧ signedLe 0x7F 0x80 1 = false ∧
      Anneal.BitVecArith.slt (BitVec.ofNat (8 * 1) 0x80) (BitVec.ofNat (8 * 1) 0x7F) ∧
      ¬ Anneal.BitVecArith.sle (BitVec.ofNat (8 * 1) 0x7F) (BitVec.ofNat (8 * 1) 0x80) := by
  refine ⟨rfl, rfl, (signedLt_eq_true_iff _ _ _).1 rfl, fun h => ?_⟩
  have h' := (signedLe_eq_true_iff 0x7F 0x80 1).2 h
  cases h'

/-- `ctlz` and `bswap` on concrete operands agree with the ported operations
(`clz 1 = 31`, `bswap 0x11223344 = 0x44332211`, and the 16/64-bit closed forms). -/
theorem intrinsics_concrete :
    evalCtlz ⟨1, 4⟩ = some ⟨31, 4⟩ ∧ evalCtlz ⟨0, 4⟩ = some ⟨32, 4⟩ ∧
      evalCtlzNonzero ⟨0, 4⟩ = none ∧
      evalBswap ⟨0x11223344, 4⟩ = some ⟨0x44332211, 4⟩ ∧
      evalBswap ⟨0x1122, 2⟩ = some ⟨Anneal.Scalars.swapBytes16 0x1122, 2⟩ ∧
      Anneal.BitVec.clz (BitVec.ofNat 32 1) = 31 ∧
      (Anneal.BitVecArith.bswap32 (BitVec.ofNat 32 0x11223344)).toNat = 0x44332211 := by
  refine ⟨rfl, rfl, rfl, rfl, evalBswap_two _, ?_, ?_⟩
  · rw [← ctlzBits_eq_clz]; rfl
  · rw [toNat_bswap32]; rfl

/-! ## 1. Canary 1: Tnum, Intervals, Pruning, `ctlz` and `bswap` on Symbolic Scalars -/

/-- Witness — a 32-bit scalar whose low half is `0x1234` satisfies the tnum used below. -/
theorem witness_tnum_x :
    ScalarTnum 4 0xFFFF0000#32 0x00001234#32 ⟨0xABCD1234, 4⟩ :=
  scalarTnum_of_bitVec (sz := 4) (m := 0xFFFF0000#32) (v := 0x00001234#32) 0xABCD1234#32
    (show Anneal.BitVec.and _ _ = Anneal.BitVec.and _ _ by decide)

/-- Witness — a 32-bit scalar whose low half is `0x0100` satisfies the tnum used below. -/
theorem witness_tnum_y :
    ScalarTnum 4 0xFFFF0000#32 0x00000100#32 ⟨0x55550100, 4⟩ :=
  scalarTnum_of_bitVec (sz := 4) (m := 0xFFFF0000#32) (v := 0x00000100#32) 0x55550100#32
    (show Anneal.BitVec.and _ _ = Anneal.BitVec.and _ _ by decide)

/-- Canary 1a (tnum through `wrapping_add` / `wrapping_sub` / AND / logical shift).

For *every* pair of 32-bit scalars whose low halves are known (`0x1234` and `0x0100`) and whose
high halves are unknown, `x + y` and `(x + y) - y` evaluate, their low halves are known
(`0x1334` and `0x1234`), byte 1 of the sum is exactly `0x13`, and the low half of the
difference is exactly `0x1234`. -/
theorem canary1_tnum_add_sub (x y : ScalarInt)
    (hx : ScalarTnum 4 0xFFFF0000#32 0x00001234#32 x)
    (hy : ScalarTnum 4 0xFFFF0000#32 0x00000100#32 y) :
    ∃ s d, evalWrappingAdd x y = some s ∧ evalWrappingSub s y = some d ∧
      ScalarTnum 4 0xFFFF0000#32 0x00001334#32 s ∧
      ScalarTnum 4 0xFFFF0000#32 0x00001234#32 d ∧
      shiftRightUnsignedBits (bitwiseAndBits 32 s.bits 0xFF00) 8 = 0x13 ∧
      bitwiseAndBits 32 d.bits 0xFFFF = 0x1234 := by
  obtain ⟨s, hs, hst⟩ := scalarTnum_evalWrappingAdd (by decide) hx hy
  have hst' : ScalarTnum 4 0xFFFF0000#32 0x00001334#32 s :=
    scalarTnum_congr (by decide) (by decide) hst
  obtain ⟨d, hd, hdt⟩ := scalarTnum_evalWrappingSub (by decide) hst' hy
  have hdt' : ScalarTnum 4 0xFFFF0000#32 0x00001234#32 d :=
    scalarTnum_congr (by decide) (by decide) hdt
  refine ⟨s, d, hs, hd, hst', hdt', ?_, ?_⟩
  · have h0 := scalarTnum_bitwiseAndBits_const hst' 0xFF00
    have ha := scalarTnum_congr (m' := 0#32) (v' := 0x00001300#32) (by decide) (by decide) h0
    have hb : bitwiseAndBits 32 s.bits 0xFF00 = 0x1300 := scalarTnum_zero_mask_mk ha
    rw [hb]
    rfl
  · have h0 := scalarTnum_bitwiseAndBits_const hdt' 0xFFFF
    have ha := scalarTnum_congr (m' := 0#32) (v' := 0x00001234#32) (by decide) (by decide) h0
    exact scalarTnum_zero_mask_mk ha

/-- Canary 1a is not vacuous: on the concrete witnesses the pipeline produces the predicted
sum and difference. -/
theorem canary1_tnum_add_sub_witness :
    evalWrappingAdd ⟨0xABCD1234, 4⟩ ⟨0x55550100, 4⟩ = some ⟨0x01221334, 4⟩ ∧
      evalWrappingSub ⟨0x01221334, 4⟩ ⟨0x55550100, 4⟩ = some ⟨0xABCD1234, 4⟩ ∧
      shiftRightUnsignedBits (bitwiseAndBits 32 0x01221334 0xFF00) 8 = 0x13 :=
  ⟨rfl, rfl, rfl⟩

/-- Witness — a negative 32-bit scalar satisfies the sign-bit tnum used below. -/
theorem witness_tnum_negative :
    ScalarTnum 4 0x7FFFFFFF#32 0x80000000#32 ⟨0x80000001, 4⟩ :=
  scalarTnum_of_bitVec (sz := 4) (m := 0x7FFFFFFF#32) (v := 0x80000000#32) 0x80000001#32
    (show Anneal.BitVec.and _ _ = Anneal.BitVec.and _ _ by decide)

/-- Canary 1b (tnum through `arithmeticShrBits`): for *every* 32-bit scalar whose sign bit is
known to be set (all other bits unknown), the arithmetic shift by 31 is exactly `-1`, and the
MIR sign test agrees. -/
theorem canary1_ashr_negative (z : ScalarInt)
    (hz : ScalarTnum 4 0x7FFFFFFF#32 0x80000000#32 z) :
    arithmeticShrBits z.bits 4 31 = 0xFFFFFFFF ∧ isSignedNegative z.bits 4 = true := by
  constructor
  · have h0 := scalarTnum_arithmeticShrBits hz 31
    have ha := scalarTnum_congr (m' := 0#32) (v' := 0xFFFFFFFF#32) (by decide) (by decide) h0
    exact scalarTnum_zero_mask_mk ha
  · rw [isSignedNegative_eq_msb, Anneal.BitVecArith.msb_of_pos (by decide)]
    exact (Anneal.BitVec.maskEq_iff_getLsbD.1 hz.2.2 31 (by decide) (by decide)).trans
      (by decide)

/-- Canary 1c (tnum through `bswap`, 32-bit): for *every* 32-bit scalar whose low half is
`0x1234`, the byte swap evaluates, its *high* half is exactly `0x3412`, and swapping back
returns the original scalar. -/
theorem canary1_bswap32 (x : ScalarInt)
    (hx : ScalarTnum 4 0xFFFF0000#32 0x00001234#32 x) :
    ∃ b, evalBswap x = some b ∧ ScalarTnum 4 0x0000FFFF#32 0x34120000#32 b ∧
      shiftRightUnsignedBits b.bits 16 = 0x3412 ∧ evalBswap b = some x := by
  obtain ⟨b, hb, hbt⟩ := scalarTnum_evalBswap (by decide) hx
  have hbt' : ScalarTnum 4 0x0000FFFF#32 0x34120000#32 b :=
    scalarTnum_congr (by decide) (by decide) hbt
  refine ⟨b, hb, hbt', ?_, ?_⟩
  · have h0 := scalarTnum_shiftRightUnsignedBits hbt' 16
    have ha := scalarTnum_congr (m' := 0#32) (v' := 0x00003412#32) (by decide) (by decide) h0
    exact scalarTnum_zero_mask_mk ha
  · obtain ⟨xb, rfl, hxb, _⟩ := scalarTnum_exists hx
    have hinv := evalBswap_evalBswap (sz := 4) (by decide) hxb
    rw [hb] at hinv
    exact hinv

/-- Witness — a 64-bit scalar whose low half is `0xDEADBEEF` satisfies the tnum used below. -/
theorem witness_tnum_x64 :
    ScalarTnum 8 0xFFFFFFFF00000000#64 0x00000000DEADBEEF#64 ⟨0x01234567DEADBEEF, 8⟩ :=
  scalarTnum_of_bitVec (sz := 8) (m := 0xFFFFFFFF00000000#64) (v := 0x00000000DEADBEEF#64)
    0x01234567DEADBEEF#64 (show Anneal.BitVec.and _ _ = Anneal.BitVec.and _ _ by decide)

/-- Canary 1c (tnum through `bswap`, 64-bit): for *every* 64-bit scalar whose low half is
`0xDEADBEEF`, the byte swap evaluates and its high half is exactly `0xEFBEADDE`. -/
theorem canary1_bswap64 (x : ScalarInt)
    (hx : ScalarTnum 8 0xFFFFFFFF00000000#64 0x00000000DEADBEEF#64 x) :
    ∃ b, evalBswap x = some b ∧ shiftRightUnsignedBits b.bits 32 = 0xEFBEADDE := by
  obtain ⟨b, hb, hbt⟩ := scalarTnum_evalBswap (by decide) hx
  have hbt' : ScalarTnum 8 0x00000000FFFFFFFF#64 0xEFBEADDE00000000#64 b :=
    scalarTnum_congr (by decide) (by decide) hbt
  have h0 := scalarTnum_shiftRightUnsignedBits hbt' 32
  have ha := scalarTnum_congr (m' := 0#64) (v' := 0x00000000EFBEADDE#64) (by decide) (by decide) h0
  exact ⟨b, hb, scalarTnum_zero_mask_mk ha⟩

/-- Canary 1c is not vacuous: the 64-bit witness swaps to the predicted bytes. -/
theorem canary1_bswap64_witness :
    evalBswap ⟨0x01234567DEADBEEF, 8⟩ = some ⟨0xEFBEADDE67452301, 8⟩ := rfl

/-- Witness — scalars inside the intervals used by canary 1d. -/
theorem witness_range_xy :
    ScalarRange 4 0x00000010#32 0x000000FF#32 ⟨0x42, 4⟩ ∧
      ScalarRange 4 0x00000800#32 0x00000E00#32 ⟨0x900, 4⟩ :=
  ⟨scalarRange_mk (by decide) (by decide) (by decide),
    scalarRange_mk (by decide) (by decide) (by decide)⟩

/-- Canary 1d (unsigned intervals through `wrapping_add`, logical shift and `ctlz`): for *every*
`x ∈ [0x10, 0xFF]` and `y ∈ [0x800, 0xE00]` (32-bit), the sum evaluates and lies in
`[0x810, 0xEFF]`, its `ctlz` is exactly `20`, and `sum >> 8` lies in `[0x8, 0xE]`. -/
theorem canary1_range_add_ctlz (x y : ScalarInt)
    (hx : ScalarRange 4 0x00000010#32 0x000000FF#32 x)
    (hy : ScalarRange 4 0x00000800#32 0x00000E00#32 y) :
    ∃ s, evalWrappingAdd x y = some s ∧
      ScalarRange 4 0x00000810#32 0x00000EFF#32 s ∧
      evalCtlz s = some ⟨20, 4⟩ ∧
      ScalarRange 4 0x00000008#32 0x0000000E#32 ⟨shiftRightUnsignedBits s.bits 8, 4⟩ := by
  obtain ⟨s, hs, hsr⟩ := scalarRange_evalWrappingAdd (by decide) hx hy
  have hsr' : ScalarRange 4 0x00000810#32 0x00000EFF#32 s :=
    scalarRange_congr (by decide) (by decide) hsr
  refine ⟨s, hs, hsr', ?_, ?_⟩
  · exact scalarRange_evalCtlz (sz := 4) (retBytes := 4) (k := 11) (by decide) (by decide) hsr'
      (by decide) (by decide) (by decide)
  · have h0 := scalarRange_shiftRightUnsignedBits (kmin := 8) (kmax := 8) hsr' (Nat.le_refl 8)
      (Nat.le_refl 8)
    exact scalarRange_congr (lo' := 0x00000008#32) (hi' := 0x0000000E#32) (by decide) (by decide) h0

/-- Canary 1d is not vacuous: on the concrete witnesses the sum is `0x942` with `ctlz = 20`. -/
theorem canary1_range_add_ctlz_witness :
    evalWrappingAdd ⟨0x42, 4⟩ ⟨0x900, 4⟩ = some ⟨0x942, 4⟩ ∧
      evalCtlz ⟨0x942, 4⟩ = some ⟨20, 4⟩ :=
  ⟨rfl, rfl⟩

/-- Canary 1d (wrap-aware interval sum): when the lower endpoints do not overflow but the upper
endpoints do, the transfer soundly degrades to the full range instead of claiming a bogus
interval; when both overflow it stays precise. -/
theorem canary1_range_add_wrap (x y : ScalarInt)
    (hx : ScalarRange 4 0xFFFFFFF0#32 0xFFFFFFFF#32 x) :
    (ScalarRange 4 0x00000000#32 0x00000020#32 y →
        ∃ s, evalWrappingAdd x y = some s ∧ ScalarRange 4 0x00000000#32 0xFFFFFFFF#32 s) ∧
      (ScalarRange 4 0x00000010#32 0x00000020#32 y →
        ∃ s, evalWrappingAdd x y = some s ∧ ScalarRange 4 0x00000000#32 0x0000001F#32 s) := by
  constructor
  · intro hy
    obtain ⟨s, hs, hsr⟩ := scalarRange_evalWrappingAdd (by decide) hx hy
    exact ⟨s, hs, scalarRange_congr (by decide) (by decide) hsr⟩
  · intro hy
    obtain ⟨s, hs, hsr⟩ := scalarRange_evalWrappingAdd (by decide) hx hy
    exact ⟨s, hs, scalarRange_congr (by decide) (by decide) hsr⟩

/-- Canary 1e (range-to-prefix extraction via the MIR `ctlz` kernel, fully symbolic): for *every*
32-bit interval `[umin, umax]` and every scalar in it, `ctlz (umin ^ umax)` evaluates and the
scalar agrees with `umin` on all bits above the low `32 - ctlz` bits. -/
theorem canary1_clz_prefix (umin umax : BitVec 32) (x : ScalarInt)
    (hx : ScalarRange 4 umin umax x) :
    ∃ c, evalCtlz ⟨bitwiseXorBits 32 umin.toNat umax.toNat, 4⟩ = some c ∧ c.bits ≤ 32 ∧
      ScalarTnum 4 (Anneal.BitVec.lowMask 32 (32 - c.bits)) umin x := by
  have hc := evalCtlz_eq_clz (sz := 4) (retBytes := 4) (by decide) (by decide)
    (Anneal.BitVec.xor umin umax).toNat
  rw [ofNat_toNat_self] at hc
  rw [bitwiseXorBits_toNat]
  exact ⟨⟨Anneal.BitVec.clz (Anneal.BitVec.xor umin umax), 4⟩, hc,
    Anneal.BitVec.clz_le (Anneal.BitVec.xor umin umax), scalarTnum_of_scalarRange_clz hx⟩

/-- Canary 1e instance: every 32-bit scalar in `[0x12340000, 0x1234FFFF]` has high half exactly
`0x1234` (derived through the `ctlz`-computed mask) and `ctlz` exactly `3`. -/
theorem canary1_clz_prefix_instance (x : ScalarInt)
    (hx : ScalarRange 4 0x12340000#32 0x1234FFFF#32 x) :
    shiftRightUnsignedBits x.bits 16 = 0x1234 ∧ evalCtlz x = some ⟨3, 4⟩ := by
  constructor
  · have ht : ScalarTnum 4 0x0000FFFF#32 0x12340000#32 x :=
      scalarTnum_congr (by decide) rfl (scalarTnum_of_scalarRange_clz hx)
    have h0 := scalarTnum_shiftRightUnsignedBits ht 16
    have ha := scalarTnum_congr (m' := 0#32) (v' := 0x00001234#32) (by decide) (by decide) h0
    exact scalarTnum_zero_mask_mk ha
  · exact scalarRange_evalCtlz (sz := 4) (retBytes := 4) (k := 28) (by decide) (by decide) hx
      (by decide) (by decide) (by decide)

/-- Witness — signed scalars inside the intervals used by canary 1f (`-2` and `3`). -/
theorem witness_srange_xy :
    ScalarSRange 4 0xFFFFFFFB#32 0x00000005#32 ⟨0xFFFFFFFE, 4⟩ ∧
      ScalarSRange 4 0xFFFFFFFD#32 0x00000003#32 ⟨0x3, 4⟩ :=
  ⟨scalarSRange_of_bitVec (sz := 4) (lo := 0xFFFFFFFB#32) (hi := 0x00000005#32) 0xFFFFFFFE#32
      (by decide) (by decide),
    scalarSRange_of_bitVec (sz := 4) (lo := 0xFFFFFFFD#32) (hi := 0x00000003#32) 0x00000003#32
      (by decide) (by decide)⟩

/-- Canary 1f (signed intervals through `evalBinOp .add` and a signed branch): for *every*
`x ∈ [-5, 5]` and `y ∈ [-3, 3]` (32-bit, signed), the sum evaluates and lies in `[-8, 8]`; on
the taken branch of a signed `sum < 0` test the interval tightens to `[-8, -1]`. -/
theorem canary1_signed_range (x y : ScalarInt)
    (hx : ScalarSRange 4 0xFFFFFFFB#32 0x00000005#32 x)
    (hy : ScalarSRange 4 0xFFFFFFFD#32 0x00000003#32 y) :
    ∃ s, Anneal.Scalars.evalBinOp .add x y true = some s ∧
      ScalarSRange 4 0xFFFFFFF8#32 0x00000008#32 s ∧
      (Anneal.Scalars.evalBinOp .lt s ⟨0, 4⟩ true = some (boolToScalar true) →
        ScalarSRange 4 0xFFFFFFF8#32 0xFFFFFFFF#32 s) ∧
      (Anneal.Scalars.evalBinOp .le s ⟨2, 4⟩ true = some (boolToScalar true) →
        ScalarSRange 4 0xFFFFFFF8#32 0x00000002#32 s) := by
  obtain ⟨s, hs, hsr⟩ :=
    scalarSRange_evalBinOp_add_no_overflow (by decide) true hx hy (by decide) (by decide)
  have hsr' : ScalarSRange 4 0xFFFFFFF8#32 0x00000008#32 s :=
    scalarSRange_congr (by decide) (by decide) hsr
  refine ⟨s, hs, hsr', fun hlt => ?_, fun hle => ?_⟩
  · have h0 := scalarSRange_refine_evalBinOp_lt (sz := 4) (by decide) 0 hsr' hlt
    exact scalarSRange_congr (hi' := 0xFFFFFFFF#32) rfl (by decide) h0
  · have h0 := scalarSRange_refine_evalBinOp_le (sz := 4) (by decide) 2 hsr' hle
    exact scalarSRange_congr (hi' := 0x00000002#32) rfl (by decide) h0

/-- Canary 1f is not vacuous: on the concrete witnesses `-2 + 3 = 1`, and both branch tests
evaluate (`1 < 0` is not taken, `1 ≤ 2` is taken). -/
theorem canary1_signed_range_witness :
    Anneal.Scalars.evalBinOp .add ⟨0xFFFFFFFE, 4⟩ ⟨0x3, 4⟩ true = some ⟨1, 4⟩ ∧
      Anneal.Scalars.evalBinOp .lt ⟨1, 4⟩ ⟨0, 4⟩ true = some (boolToScalar false) ∧
      Anneal.Scalars.evalBinOp .le ⟨1, 4⟩ ⟨2, 4⟩ true = some (boolToScalar true) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [evalBinOp_add_eq_add (by decide)]; rfl
  · rw [evalBinOp_lt_signed_eq_slt (by decide)]; rfl
  · rw [evalBinOp_le_signed_eq_sle (by decide)]; rfl

/-- Canary 1g (empty-abstraction pruning, `arXiv:2611.23584`): a tnum that knows the low byte is
`0x10` and a tnum that knows the low nibble is `0x1` disagree on known bit 0, so no 32-bit
scalar satisfies both. -/
theorem canary1_prune_conflict :
    ¬ ∃ sc, ScalarTnum 4 0xFFFFFF00#32 0x00000010#32 sc ∧
      ScalarTnum 4 0xFFFFFFF0#32 0x00000001#32 sc :=
  scalarTnum_empty_of_conflict (by decide)

/-- Canary 1g (pruning an infeasible branch of the symbolic pipeline): bit 8 of the canary 1a
sum is known to be `1`, so the abstract state of a branch that assumes bit 8 is `0` is empty for
*every* pair of inputs. -/
theorem canary1_prune_pipeline (x y : ScalarInt)
    (hx : ScalarTnum 4 0xFFFF0000#32 0x00001234#32 x)
    (hy : ScalarTnum 4 0xFFFF0000#32 0x00000100#32 y) :
    ¬ ∃ s, evalWrappingAdd x y = some s ∧ ScalarTnum 4 0xFFFFFEFF#32 0x00000000#32 s := by
  rintro ⟨s, hs, hbranch⟩
  obtain ⟨s', _, hs', _, hst, _, _, _⟩ := canary1_tnum_add_sub x y hx hy
  have hss : s' = s := Option.some.inj (hs'.symm.trans hs)
  subst hss
  exact scalarTnum_empty_of_conflict (by decide) ⟨s', hst, hbranch⟩

/-- Canary 1g is exact, not merely sound: compatible tnums are *not* pruned. The low-byte tnum
`0x10` and the low-nibble tnum `0x0` have a common scalar, and the conflict test agrees. -/
theorem canary1_prune_exact :
    (∃ sc, ScalarTnum 4 0xFFFFFF00#32 0x00000010#32 sc ∧
        ScalarTnum 4 0xFFFFFFF0#32 0x00000000#32 sc) ∧
      Anneal.BitVec.and (Anneal.BitVec.xor 0x00000010#32 0x00000000#32)
        (Anneal.BitVec.and (Anneal.BitVec.not 0xFFFFFF00#32) (Anneal.BitVec.not 0xFFFFFFF0#32)) =
          0#32 :=
  ⟨scalarTnum_inter_nonempty_iff.2 (by decide), by decide⟩

/-- Canary 1h (operational `Trusted` `evalScalarBinOp` & `evalUnaryNot` pipeline): end-to-end
symbolic tnum, unsigned-range, and signed-range transfers directly on the MIR interpreter's
`evalScalarBinOp` and `evalUnaryNot` without dropping down to pure helpers. -/
theorem canary1_evalScalarBinOp_pipeline (locals : List LocalSlot) (mem : Memory)
    (idx : LayoutIdx) (x y z : ScalarInt)
    (hx : ScalarTnum 4 0xFFFF0000#32 0x00001234#32 x)
    (hy : ScalarTnum 4 0xFFFF0000#32 0x00000100#32 y)
    (hz : ScalarSRange 4 0xFFFFFFFB#32 0x00000005#32 z) :
    (∃ s ns, evalScalarBinOp .add x y locals mem false = .ok (.scalar s) locals mem ∧
        evalUnaryNot s (some { kind := .uint .u32, layoutIdx := idx }) locals mem =
          .ok (.scalar ns) locals mem ∧
        ScalarTnum 4 0xFFFF0000#32 0x00001334#32 s ∧
        ScalarTnum 4 0xFFFF0000#32 0xFFFFECCB#32 ns) ∧
      (evalScalarBinOp .ge z ⟨0, 4⟩ locals mem true =
          .ok (.scalar (boolToScalar true)) locals mem →
        ScalarSRange 4 0x00000000#32 0x00000005#32 z) := by
  constructor
  · obtain ⟨s, hs, hst⟩ := scalarTnum_evalScalarBinOp_add (by decide) locals mem false hx hy
    have hst' : ScalarTnum 4 0xFFFF0000#32 0x00001334#32 s :=
      scalarTnum_congr (by decide) (by decide) hst
    obtain ⟨ns, hns, hnst⟩ := scalarTnum_evalUnaryNot_uint (by decide) .u32 idx locals mem hst'
    have hnst' : ScalarTnum 4 0xFFFF0000#32 0xFFFFECCB#32 ns :=
      scalarTnum_congr rfl (by decide) hnst
    exact ⟨s, ns, hs, hns, hst', hnst'⟩
  · intro hge
    have h0 := scalarSRange_refine_evalScalarBinOp_ge (sz := 4) (by decide) 0 locals mem hz hge
    exact scalarSRange_congr (lo' := 0x00000000#32) (by decide) rfl h0

/-- Canary 1i (tnum meet, tnum-to-range Galois widening, `extractField` tnum, and unsigned/signed
`evalCastValue`): intersecting two compatible tnums sharpens the mask to `m₁ &&& m₂`, widens to
`[v &&& ~~~m, v ||| m]`, transfers through `extractField`, and preserves known bits through
unsigned `setWidth` and signed `signExtend` casts. -/
theorem canary1_tnum_meet_range_casts (x : ScalarInt)
    (h₁ : ScalarTnum 4 0xFFFFFF00#32 0x000000AB#32 x)
    (h₂ : ScalarTnum 4 0xFFFF00FF#32 0x0000CD00#32 x) :
    ScalarTnum 4 0xFFFF0000#32 0x0000CDAB#32 x ∧
      ScalarRange 4 0x0000CDAB#32 0xFFFFCDAB#32 x ∧
      extractField 4 x.bits 8 8 = 0xCD ∧
      (∃ u16, Anneal.Scalars.evalCastValue x 2 false = some u16 ∧ u16 = ⟨0xCDAB, 2⟩) ∧
      (∃ i64, Anneal.Scalars.evalCastValue x 8 true = some i64 ∧
        ScalarTnum 8 0xFFFFFFFFFFFF0000#64 0x000000000000CDAB#64 i64) := by
  have hmeet : ScalarTnum 4 0xFFFF0000#32 0x0000CDAB#32 x :=
    scalarTnum_congr (by decide) (by decide) (scalarTnum_inter h₁ h₂)
  have hrng : ScalarRange 4 0x0000CDAB#32 0xFFFFCDAB#32 x :=
    scalarRange_congr (by decide) (by decide) (scalarRange_of_scalarTnum hmeet)
  have hext : extractField 4 x.bits 8 8 = 0xCD := by
    have hm := scalarTnum_extractField hmeet 8 8
    have hm0 : Anneal.BitVec.MaskEq 0#8 (BitVec.ofNat 8 (extractField 4 x.bits 8 8)) 0xCD#8 := by
      have h1 : Anneal.BitVecArith.extractBits 0xFFFF0000#32 8 8 = 0#8 := by decide
      have h2 : Anneal.BitVecArith.extractBits 0x0000CDAB#32 8 8 = 0xCD#8 := by decide
      rw [h1, h2] at hm
      exact hm
    have heq := Anneal.BitVec.maskEq_zero_iff_eq.1 hm0
    have hlt : extractField 4 x.bits 8 8 < 2 ^ 8 := by
      rw [extractField_eq_extractBits hmeet.2.1]
      exact (Anneal.BitVecArith.extractBits _ 8 8).isLt
    have ht := congrArg _root_.BitVec.toNat heq
    rw [_root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
    exact ht
  obtain ⟨u16, hu16, hu16t⟩ :=
    scalarTnum_evalCastValue_unsigned (dstSz := 2) (by decide) (by decide) hmeet
  have hu16eq : u16 = ⟨0xCDAB, 2⟩ :=
    scalarTnum_zero_mask_iff.1 (scalarTnum_congr (m' := 0#16) (v' := 0xCDAB#16) (by decide) (by decide) hu16t)
  obtain ⟨i64, hi64, hi64t⟩ :=
    scalarTnum_evalCastValue_signed (dstSz := 8) (by decide) (by decide) hmeet
  have hi64t' : ScalarTnum 8 0xFFFFFFFFFFFF0000#64 0x000000000000CDAB#64 i64 :=
    scalarTnum_congr (by decide) (by decide) hi64t
  exact ⟨hmeet, hrng, hext, ⟨u16, hu16, hu16eq⟩, ⟨i64, hi64, hi64t'⟩⟩

/-- Witness for canary 1i: `0x8001CDAB` satisfies both input tnums. -/
theorem witness_canary1_meet :
    ScalarTnum 4 0xFFFFFF00#32 0x000000AB#32 ⟨0x8001CDAB, 4⟩ ∧
      ScalarTnum 4 0xFFFF00FF#32 0x0000CD00#32 ⟨0x8001CDAB, 4⟩ :=
  ⟨scalarTnum_of_bitVec (sz := 4) (m := 0xFFFFFF00#32) (v := 0x000000AB#32) 0x8001CDAB#32
      (show Anneal.BitVec.and _ _ = Anneal.BitVec.and _ _ by decide),
    scalarTnum_of_bitVec (sz := 4) (m := 0xFFFF00FF#32) (v := 0x0000CD00#32) 0x8001CDAB#32
      (show Anneal.BitVec.and _ _ = Anneal.BitVec.and _ _ by decide)⟩

/-- Canary 1j (arithmetic intervals + `evalCtlzNonzero` non-UB & antitone bounds): for every
`x ∈ [0x10, 0xFF]` and `y ∈ [0x2, 0x8]`, `evalCtlzNonzero x` succeeds and lies in `[24, 27]`,
`x - y ∈ [0x8, 0xFD]`, `x * y ∈ [0x20, 0x7F8]`, `x / y ∈ [0x2, 0x7F]`, `x % y < 8`, and
`x << 4 ∈ [0x100, 0xFF0]`. -/
theorem canary1_range_arith_and_ctlzNonzero (x y : ScalarInt)
    (hx : ScalarRange 4 0x00000010#32 0x000000FF#32 x)
    (hy : ScalarRange 4 0x00000002#32 0x00000008#32 y) :
    (∃ c, evalCtlzNonzero x = some c ∧ c.bits < 32 ∧ ScalarRange 4 24#32 27#32 c) ∧
      (∃ d, evalWrappingSub x y = some d ∧ ScalarRange 4 0x00000008#32 0x000000FD#32 d) ∧
      (∃ p, evalWrappingMul x y = some p ∧ ScalarRange 4 0x00000020#32 0x000007F8#32 p) ∧
      (∃ q, Anneal.Scalars.evalBinOp .div x y false = some q ∧
        ScalarRange 4 0x00000002#32 0x0000007F#32 q) ∧
      (∃ r, Anneal.Scalars.evalBinOp .rem x y false = some r ∧ r.bits < 8) ∧
      (∃ s, Anneal.Scalars.evalBinOp .shl x ⟨4, 4⟩ false = some s ∧
        ScalarRange 4 0x00000100#32 0x00000FF0#32 s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨c, hc, hlt, hcr⟩ :=
      scalarRange_evalCtlzNonzero_range (sz := 4) (retBytes := 4) (by decide) (by decide)
        (by decide) hx (by decide)
    exact ⟨c, hc, hlt, scalarRange_congr (by decide) (by decide) hcr⟩
  · obtain ⟨d, hd, hdr⟩ := scalarRange_evalWrappingSub_no_underflow (by decide) hx hy (by decide)
    exact ⟨d, hd, scalarRange_congr (by decide) (by decide) hdr⟩
  · obtain ⟨p, hp, hpr⟩ := scalarRange_evalWrappingMul_no_overflow (by decide) hx hy (by decide)
    exact ⟨p, hp, scalarRange_congr (by decide) (by decide) hpr⟩
  · obtain ⟨q, hq, hqr⟩ := scalarRange_evalBinOp_div_unsigned (by decide) hx hy (by decide)
    exact ⟨q, hq, scalarRange_congr (by decide) (by decide) hqr⟩
  · obtain ⟨r, hr, _, hrb⟩ := scalarRange_evalBinOp_rem_unsigned (by decide) hx hy (by decide)
    exact ⟨r, hr, hrb⟩
  · obtain ⟨s, hs, hsr⟩ := scalarRange_evalBinOp_shl_no_overflow (by decide) ⟨4, 4⟩ (by decide)
      (kmin := 4) (kmax := 4) false hx (by decide) (by decide) (by decide)
    exact ⟨s, hs, scalarRange_congr (by decide) (by decide) hsr⟩

/-- Witness for canary 1j: `x = 0x42 ∈ [0x10, 0xFF]` and `y = 4 ∈ [2, 8]` satisfy the inputs and
yield concrete outputs `ctlz_nonzero = 25`, `0x42 - 4 = 0x3E`, `0x42 * 4 = 0x108`. -/
theorem canary1_range_arith_and_ctlzNonzero_witness :
    ScalarRange 4 0x00000002#32 0x00000008#32 ⟨4, 4⟩ ∧
      evalCtlzNonzero ⟨0x42, 4⟩ = some ⟨25, 4⟩ ∧
      evalWrappingSub ⟨0x42, 4⟩ ⟨4, 4⟩ = some ⟨0x3E, 4⟩ ∧
      evalWrappingMul ⟨0x42, 4⟩ ⟨4, 4⟩ = some ⟨0x108, 4⟩ :=
  ⟨scalarRange_mk (by decide) (by decide) (by decide), rfl, rfl, rfl⟩

/-! ## 2. Canary 2: Disjoint-Mask Bitfield Packing (*Isomer*, `arXiv:2611.19113`) -/

/-- Pack a 32-bit wire header `(version : 4 bits, flags : 12 bits, payloadLen : 16 bits)` with
the MIR scalar primitives `shiftLeftBits` and `bitwiseOrBits`:
`(version << 28) | (flags << 16) | (payloadLen << 0)`. -/
def packHeader (version flags payloadLen : Nat) : Nat :=
  bitwiseOrBits (8 * 4)
    (bitwiseOrBits (8 * 4) (shiftLeftBits version 28 (scalarModulus 4))
      (shiftLeftBits flags 16 (scalarModulus 4)))
    (shiftLeftBits payloadLen 0 (scalarModulus 4))

/-- The same header packed through the MIR evaluator `evalBinOp` (three shifts, two ORs). -/
def evalPackHeader (version flags payloadLen : Nat) : Option ScalarInt :=
  (Anneal.Scalars.evalBinOp .shl ⟨version, 4⟩ ⟨28, 4⟩ false).bind fun a =>
  (Anneal.Scalars.evalBinOp .shl ⟨flags, 4⟩ ⟨16, 4⟩ false).bind fun b =>
  (Anneal.Scalars.evalBinOp .shl ⟨payloadLen, 4⟩ ⟨0, 4⟩ false).bind fun c =>
  (Anneal.Scalars.evalBinOp .bitOr a b false).bind fun ab =>
  Anneal.Scalars.evalBinOp .bitOr ab c false

/-- The packed header is a canonical 32-bit scalar. -/
theorem packHeader_lt (version flags payloadLen : Nat) :
    packHeader version flags payloadLen < scalarModulus 4 :=
  bitwiseOrBits_lt_scalarModulus 4 _ _

/-- Canary 2a (exact field recovery): for *every* in-range `(version, flags, payloadLen)`, each
field is recovered from the packed word by `shiftRightUnsignedBits` followed by
`bitwiseAndBits` with the field mask. -/
theorem canary2_fields {version flags payloadLen : Nat}
    (hv : version < 2 ^ 4) (hf : flags < 2 ^ 12) (hp : payloadLen < 2 ^ 16) :
    extractField 4 (packHeader version flags payloadLen) 28 4 = version ∧
      extractField 4 (packHeader version flags payloadLen) 16 12 = flags ∧
      extractField 4 (packHeader version flags payloadLen) 0 16 = payloadLen := by
  have cv := shiftLeftBits_lt_scalarModulus version 28 4
  have cf := shiftLeftBits_lt_scalarModulus flags 16 4
  have cp := shiftLeftBits_lt_scalarModulus payloadLen 0 4
  have cvf := bitwiseOrBits_lt_scalarModulus 4 (shiftLeftBits version 28 (scalarModulus 4))
    (shiftLeftBits flags 16 (scalarModulus 4))
  unfold packHeader
  refine ⟨?_, ?_, ?_⟩
  · rw [extractField_bitwiseOrBits cvf cp, extractField_bitwiseOrBits cv cf,
      extractField_shiftLeftBits_self hv (by decide),
      extractField_shiftLeftBits_disjoint hf (by decide) (by decide) (by decide),
      extractField_shiftLeftBits_disjoint hp (by decide) (by decide) (by decide),
      Nat.or_zero, Nat.or_zero]
  · rw [extractField_bitwiseOrBits cvf cp, extractField_bitwiseOrBits cv cf,
      extractField_shiftLeftBits_self hf (by decide),
      extractField_shiftLeftBits_disjoint hv (by decide) (by decide) (by decide),
      extractField_shiftLeftBits_disjoint hp (by decide) (by decide) (by decide),
      Nat.zero_or, Nat.or_zero]
  · rw [extractField_bitwiseOrBits cvf cp, extractField_bitwiseOrBits cv cf,
      extractField_shiftLeftBits_self hp (by decide),
      extractField_shiftLeftBits_disjoint hv (by decide) (by decide) (by decide),
      extractField_shiftLeftBits_disjoint hf (by decide) (by decide) (by decide),
      Nat.or_zero, Nat.zero_or]

/-- Canary 2a, spelled out on the MIR primitives: `extractField` is literally
`bitwiseAndBits 32 (shiftRightUnsignedBits · lo) mask`. -/
theorem canary2_fields_primitives {version flags payloadLen : Nat}
    (hv : version < 2 ^ 4) (hf : flags < 2 ^ 12) (hp : payloadLen < 2 ^ 16) :
    bitwiseAndBits 32 (shiftRightUnsignedBits (packHeader version flags payloadLen) 28) 0xF =
        version ∧
      bitwiseAndBits 32 (shiftRightUnsignedBits (packHeader version flags payloadLen) 16) 0xFFF =
        flags ∧
      bitwiseAndBits 32 (shiftRightUnsignedBits (packHeader version flags payloadLen) 0) 0xFFFF =
        payloadLen :=
  canary2_fields hv hf hp

/-- Canary 2b (pack injectivity): two in-range headers with the same packed word are equal
field by field. -/
theorem canary2_injective {v₁ f₁ p₁ v₂ f₂ p₂ : Nat}
    (hv₁ : v₁ < 2 ^ 4) (hf₁ : f₁ < 2 ^ 12) (hp₁ : p₁ < 2 ^ 16)
    (hv₂ : v₂ < 2 ^ 4) (hf₂ : f₂ < 2 ^ 12) (hp₂ : p₂ < 2 ^ 16)
    (h : packHeader v₁ f₁ p₁ = packHeader v₂ f₂ p₂) :
    v₁ = v₂ ∧ f₁ = f₂ ∧ p₁ = p₂ := by
  have e₁ := canary2_fields hv₁ hf₁ hp₁
  have e₂ := canary2_fields hv₂ hf₂ hp₂
  rw [h] at e₁
  exact ⟨e₁.1.symm.trans e₂.1, e₁.2.1.symm.trans e₂.2.1, e₁.2.2.symm.trans e₂.2.2⟩

/-- Canary 2c (agreement with the ported bitvector library): the packed scalar is the ported
shift-and-OR pack of the zero-extended fields, and field recovery on the scalar is the ported
`extractBits` (the two sides of `Anneal.BitVecArith.extractBits_or_disjoint`). -/
theorem canary2_extractBits {version flags payloadLen : Nat}
    (hv : version < 2 ^ 4) (hf : flags < 2 ^ 12) (hp : payloadLen < 2 ^ 16) :
    BitVec.ofNat (8 * 4) (packHeader version flags payloadLen) =
        Anneal.BitVec.or
          (Anneal.BitVec.or
            (Anneal.BitVec.shl (Anneal.BitVec.setWidth (8 * 4) (BitVec.ofNat 4 version)) 28)
            (Anneal.BitVec.shl (Anneal.BitVec.setWidth (8 * 4) (BitVec.ofNat 12 flags)) 16))
          (Anneal.BitVec.shl (Anneal.BitVec.setWidth (8 * 4) (BitVec.ofNat 16 payloadLen)) 0) ∧
      (Anneal.BitVecArith.extractBits
        (BitVec.ofNat (8 * 4) (packHeader version flags payloadLen)) 28 4).toNat = version ∧
      (Anneal.BitVecArith.extractBits
        (BitVec.ofNat (8 * 4) (packHeader version flags payloadLen)) 16 12).toNat = flags ∧
      (Anneal.BitVecArith.extractBits
        (BitVec.ofNat (8 * 4) (packHeader version flags payloadLen)) 0 16).toNat = payloadLen := by
  have e := canary2_fields hv hf hp
  have c := packHeader_lt version flags payloadLen
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold packHeader
    rw [bitwiseOrBits_eq_or, bitwiseOrBits_eq_or, ofNat_toNat_self, ofNat_toNat_self,
      shiftLeftBits_eq_shl, shiftLeftBits_eq_shl, shiftLeftBits_eq_shl, ofNat_toNat_self,
      ofNat_toNat_self, ofNat_toNat_self, ofNat_eq_setWidth_ofNat hv, ofNat_eq_setWidth_ofNat hf,
      ofNat_eq_setWidth_ofNat hp]
  · rw [← extractField_eq_extractBits c]; exact e.1
  · rw [← extractField_eq_extractBits c]; exact e.2.1
  · rw [← extractField_eq_extractBits c]; exact e.2.2

/-- Canary 2d (the MIR evaluator computes the pack): for *every* `(version, flags,
payloadLen)`, the `evalBinOp` shift/OR pipeline returns the packed word. -/
theorem canary2_evalPackHeader (version flags payloadLen : Nat) :
    evalPackHeader version flags payloadLen = some ⟨packHeader version flags payloadLen, 4⟩ := by
  unfold evalPackHeader packHeader
  rw [Anneal.Scalars.evalBinOp_shl_apply (by decide) (by decide), Option.bind_some,
    Anneal.Scalars.evalBinOp_shl_apply (by decide) (by decide), Option.bind_some,
    Anneal.Scalars.evalBinOp_shl_apply (by decide) (by decide), Option.bind_some,
    Anneal.Scalars.evalBinOp_bitOr_apply (by decide), Option.bind_some,
    Anneal.Scalars.evalBinOp_bitOr_apply (by decide),
    Anneal.Scalars.bitwiseOrBits_eq_lor, Anneal.Scalars.bitwiseOrBits_eq_lor,
    Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod, Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod,
    Anneal.Scalars.shiftLeftBits_eq_shiftLeft_mod]

/-- Canary 2d (the MIR evaluator recovers the fields): on the evaluator's packed scalar, the
`evalBinOp` pipelines `(hdr >> lo) & mask` return each field, for *every* in-range header. -/
theorem canary2_evalBinOp_fields {version flags payloadLen : Nat}
    (hv : version < 2 ^ 4) (hf : flags < 2 ^ 12) (hp : payloadLen < 2 ^ 16) :
    ∃ hdr, evalPackHeader version flags payloadLen = some hdr ∧
      (Anneal.Scalars.evalBinOp .shr hdr ⟨28, 4⟩ false).bind
          (fun r => Anneal.Scalars.evalBinOp .bitAnd r ⟨2 ^ 4 - 1, 4⟩ false) =
        some ⟨version, 4⟩ ∧
      (Anneal.Scalars.evalBinOp .shr hdr ⟨16, 4⟩ false).bind
          (fun r => Anneal.Scalars.evalBinOp .bitAnd r ⟨2 ^ 12 - 1, 4⟩ false) =
        some ⟨flags, 4⟩ ∧
      (Anneal.Scalars.evalBinOp .shr hdr ⟨0, 4⟩ false).bind
          (fun r => Anneal.Scalars.evalBinOp .bitAnd r ⟨2 ^ 16 - 1, 4⟩ false) =
        some ⟨payloadLen, 4⟩ := by
  have e := canary2_fields hv hf hp
  have c := packHeader_lt version flags payloadLen
  refine ⟨_, canary2_evalPackHeader version flags payloadLen, ?_, ?_, ?_⟩
  · rw [evalBinOp_shr_bitAnd_eq_extractField (by decide) (by decide) c (by decide), e.1]
  · rw [evalBinOp_shr_bitAnd_eq_extractField (by decide) (by decide) c (by decide), e.2.1]
  · rw [evalBinOp_shr_bitAnd_eq_extractField (by decide) (by decide) c (by decide), e.2.2]

/-- Canary 2d (injectivity at the evaluator): equal `evalBinOp` pack results force equal
in-range headers. -/
theorem canary2_evalPackHeader_injective {v₁ f₁ p₁ v₂ f₂ p₂ : Nat}
    (hv₁ : v₁ < 2 ^ 4) (hf₁ : f₁ < 2 ^ 12) (hp₁ : p₁ < 2 ^ 16)
    (hv₂ : v₂ < 2 ^ 4) (hf₂ : f₂ < 2 ^ 12) (hp₂ : p₂ < 2 ^ 16)
    (h : evalPackHeader v₁ f₁ p₁ = evalPackHeader v₂ f₂ p₂) :
    v₁ = v₂ ∧ f₁ = f₂ ∧ p₁ = p₂ := by
  rw [canary2_evalPackHeader, canary2_evalPackHeader] at h
  exact canary2_injective hv₁ hf₁ hp₁ hv₂ hf₂ hp₂ (ScalarInt.mk.inj (Option.some.inj h)).1

/-- Canary 2e (`evalBinOp_pack_injective` directly, including zero-width field at `lo = 32`):
equal two-field `evalBinOp` shift/OR packs force equal in-range fields even when one field has
width `0` placed at the top boundary `lo = 32`. -/
theorem canary2_evalBinOp_pack_zero_width {a₁ b₁ a₂ b₂ : Nat}
    (ha₁ : a₁ < 2 ^ 0) (hb₁ : b₁ < 2 ^ 16) (ha₂ : a₂ < 2 ^ 0) (hb₂ : b₂ < 2 ^ 16)
    (h : (Anneal.Scalars.evalBinOp .shl ⟨a₁, 4⟩ ⟨32, 4⟩ false).bind (fun sa =>
          (Anneal.Scalars.evalBinOp .shl ⟨b₁, 4⟩ ⟨0, 4⟩ false).bind (fun sb =>
            Anneal.Scalars.evalBinOp .bitOr sa sb false)) =
        (Anneal.Scalars.evalBinOp .shl ⟨a₂, 4⟩ ⟨32, 4⟩ false).bind (fun sa =>
          (Anneal.Scalars.evalBinOp .shl ⟨b₂, 4⟩ ⟨0, 4⟩ false).bind (fun sb =>
            Anneal.Scalars.evalBinOp .bitOr sa sb false))) :
    a₁ = a₂ ∧ b₁ = b₂ :=
  evalBinOp_pack_injective (by decide) (by decide) ha₁ hb₁ ha₂ hb₂ (by decide) (by decide)
    (by decide) h

/-- Canary 2 is not vacuous: the header `(4, 0xABC, 0x1234)` packs to `0x4ABC1234` through the
evaluator, and the version field is extracted by the evaluator pipeline. -/
theorem canary2_witness :
    evalPackHeader 0x4 0xABC 0x1234 = some ⟨0x4ABC1234, 4⟩ ∧
      (Anneal.Scalars.evalBinOp .shr ⟨0x4ABC1234, 4⟩ ⟨28, 4⟩ false).bind
          (fun r => Anneal.Scalars.evalBinOp .bitAnd r ⟨0xF, 4⟩ false) = some ⟨0x4, 4⟩ := by
  refine ⟨?_, ?_⟩
  · rw [canary2_evalPackHeader]; rfl
  · rw [Anneal.Scalars.evalBinOp_shr_unsigned (by decide) (by decide), Option.bind_some,
      Anneal.Scalars.evalBinOp_bitAnd_apply (by decide)]
    rfl

/-! ## 3. Canary 3: `[u32; 4]` / `[u64; 2]` Little-Endian Chunk Round Trips and Transmutation -/

/-- The `bitVecLE` codec at 4 bytes (`u32`). -/
abbrev u32LE : FixedByteCodec (BitVec (8 * 4)) 4 := bitVecLE 4 (by decide)

/-- The `bitVecLE` codec at 8 bytes (`u64`). -/
abbrev u64LE : FixedByteCodec (BitVec (8 * 8)) 8 := bitVecLE 8 (by decide)

/-- Little-endian concatenation of two 32-bit words into one 64-bit word (`lo` in the low
half). -/
def concat32 (lo hi : BitVec 32) : BitVec 64 :=
  BitVec.ofNat 64 (lo.toNat + 2 ^ 32 * hi.toNat)

/-- Canary 3a (`encodeValueToBytes`): for *every* `[a, b, c, d] : [u32; 4]`, the MIR byte
encoder emits the element-wise `bitVecLE 4` encoding. -/
theorem canary3_encodeValueToBytes (layouts : LayoutTable) (idx : LayoutIdx)
    (a b c d : BitVec 32) :
    encodeValueToBytes defaultCodecFuel layouts
        { kind := .array (.uint .u32) 4, layoutIdx := idx } (bitVecArrayValue 4 [a, b, c, d]) =
      some (u32LE.encodeElems [a, b, c, d]) :=
  encodeValueToBytes_bitVecArray layouts .u32 idx [a, b, c, d]

/-- Canary 3a (`encodeListWith`): the element encoder threaded through `Trusted`
`encodeListWith` emits the same bytes. -/
theorem canary3_encodeListWith (layouts : LayoutTable) (a b c d : BitVec 32) :
    encodeListWith
        (fun e => encodeValueToBytes 15 layouts { kind := .uint .u32, layoutIdx := 0 } e) 4
        ([a, b, c, d].map (fun x => Value.scalar ⟨x.toNat, 4⟩)) =
      some (u32LE.encodeElems [a, b, c, d]) :=
  FixedByteCodec.encodeListWith_map_eq_encodeElems u32LE (fun x => Value.scalar ⟨x.toNat, 4⟩)
    (fun e => encodeValueToBytes 15 layouts { kind := .uint .u32, layoutIdx := 0 } e)
    (fun _ => rfl) [a, b, c, d]

/-- Canary 3b (chunking): splitting the 16 encoded bytes into 4-byte chunks yields exactly the
four per-element encodings, and the chunk count is `divCeil 16 4 = 4`. -/
theorem canary3_chunks (a b c d : BitVec 32) :
    Anneal.ListChunks.chunksOf 4 (u32LE.encodeElems [a, b, c, d]) =
        [u32LE.encode a, u32LE.encode b, u32LE.encode c, u32LE.encode d] ∧
      (Anneal.ListChunks.chunksOf 4 (u32LE.encodeElems [a, b, c, d])).length =
        Anneal.ListChunks.divCeil 16 4 := by
  have h := chunksOf_encodeElems u32LE (by decide) [a, b, c, d]
  exact ⟨h, by rw [h]; rfl⟩

/-- A single `u32` survives encode / payload extraction / `LeBytes.u32FromLeBytes`. -/
theorem u32_roundtrip (x : BitVec 32) :
    Anneal.LeBytes.u32FromLeBytes (extractInitBvBytes (u32LE.encode x)) = x := by
  rw [bitVecLE_encode_eq_toLeBytesAux, extractInitBvBytes_map]
  exact Anneal.LeBytes.u32FromLeBytes_u32ToLeBytes x

/-- Canary 3c (recovery through `ListChunks.chunksOf` and `LeBytes.u32FromLeBytes`): for
*every* `[a, b, c, d]`, chunking the encoded bytes and decoding each chunk with the ported
little-endian reader returns `[a, b, c, d]`. -/
theorem canary3_recover_u32 (a b c d : BitVec 32) :
    (Anneal.ListChunks.chunksOf 4 (u32LE.encodeElems [a, b, c, d])).map
        (fun ch => Anneal.LeBytes.u32FromLeBytes (extractInitBvBytes ch)) = [a, b, c, d] := by
  rw [(canary3_chunks a b c d).1]
  simp only [List.map_cons, List.map_nil, u32_roundtrip]

/-- Canary 3d (recovery through `decodeValueFromBytes` and `decodeChunks`): the MIR byte decoder
and the codec-level chunk decoder both return the original array. -/
theorem canary3_decode (layouts : LayoutTable) (idx : LayoutIdx) (a b c d : BitVec 32) :
    decodeValueFromBytes defaultCodecFuel layouts
          { kind := .array (.uint .u32) 4, layoutIdx := idx }
          (u32LE.encodeElems [a, b, c, d]) = some (bitVecArrayValue 4 [a, b, c, d]) ∧
      (u32LE.decodeChunks 4 (u32LE.encodeElems [a, b, c, d])).map Subtype.val =
        some [a, b, c, d] :=
  ⟨decodeValueFromBytes_encodeElems_bitVecLE layouts .u32 idx [a, b, c, d],
    decodeChunks_encodeElems_val u32LE [a, b, c, d]⟩

/-- Two adjacent `u32` encodings are one `u64` encoding of their little-endian concatenation
(`Anneal.LeBytes.toLeBytesAux_add` / `fromLeBytes_append`). -/
theorem u32_pair_eq_u64 (a b : BitVec 32) :
    u32LE.encode a ++ u32LE.encode b = u64LE.encode (concat32 a b) :=
  bitVecLE_encode_append 4 4 (by decide) (by decide) a b

/-- Canary 3e (4-byte-pair / 8-byte-chunk correspondence): the bytes of `[a, b, c, d] : [u32; 4]`
are the bytes of `[concat32 a b, concat32 c d] : [u64; 2]`. -/
theorem canary3_bytes_eq (a b c d : BitVec 32) :
    u32LE.encodeElems [a, b, c, d] = u64LE.encodeElems [concat32 a b, concat32 c d] := by
  show u32LE.encode a ++ (u32LE.encode b ++ (u32LE.encode c ++ (u32LE.encode d ++ []))) =
    u64LE.encode (concat32 a b) ++ (u64LE.encode (concat32 c d) ++ [])
  rw [List.append_nil, List.append_nil, ← u32_pair_eq_u64 a b, ← u32_pair_eq_u64 c d,
    List.append_assoc]

/-- Canary 3e (8-byte chunks and `fromLeBytes_append`): splitting the same 16 bytes into 8-byte
chunks yields the two pair encodings, and the ported little-endian reader on a pair chunk
returns `a + 2^32 * b`, i.e. `concat32 a b`. -/
theorem canary3_chunk_pairs (a b c d : BitVec 32) :
    Anneal.ListChunks.chunksOf 8 (u32LE.encodeElems [a, b, c, d]) =
        [u32LE.encode a ++ u32LE.encode b, u32LE.encode c ++ u32LE.encode d] ∧
      Anneal.LeBytes.fromLeBytes (extractInitBvBytes (u32LE.encode a ++ u32LE.encode b)) =
        a.toNat + 2 ^ 32 * b.toNat ∧
      Anneal.LeBytes.u64FromLeBytes (extractInitBvBytes (u32LE.encode a ++ u32LE.encode b)) =
        concat32 a b := by
  have hsplit : Anneal.LeBytes.fromLeBytes
      (extractInitBvBytes (u32LE.encode a ++ u32LE.encode b)) = a.toNat + 2 ^ 32 * b.toNat := by
    have ha : a.toNat % 2 ^ (4 * 8) = a.toNat := Nat.mod_eq_of_lt a.isLt
    have hb : b.toNat % 2 ^ (4 * 8) = b.toNat := Nat.mod_eq_of_lt b.isLt
    rw [bitVecLE_encode_eq_toLeBytesAux, bitVecLE_encode_eq_toLeBytesAux, ← List.map_append,
      extractInitBvBytes_map, Anneal.LeBytes.fromLeBytes_append,
      Anneal.LeBytes.fromLeBytes_toLeBytesAux, Anneal.LeBytes.fromLeBytes_toLeBytesAux,
      Anneal.LeBytes.toLeBytesAux_length, ha, hb]
  refine ⟨?_, hsplit, ?_⟩
  · rw [canary3_bytes_eq, chunksOf_encodeElems u64LE (by decide), u32_pair_eq_u64 a b,
      u32_pair_eq_u64 c d]
    rfl
  · show BitVec.ofNat 64 _ = _
    rw [hsplit]
    rfl

/-- Canary 3f (`[u32; 4] → [u64; 2]` transmutation): for *every* `[a, b, c, d]`, the encoded
bytes decode at `[u64; 2]` (soundness, via `transmute_sound_of_into_from_bytes`), and the decoded
value is exactly `[concat32 a b, concat32 c d]`. -/
theorem canary3_transmute (layouts : LayoutTable) (idx₁ idx₂ : LayoutIdx)
    (a b c d : BitVec 32) :
    (∃ v', decodeValueFromBytes defaultCodecFuel layouts
        { kind := .array (.uint .u64) 2, layoutIdx := idx₂ }
        (u32LE.encodeElems [a, b, c, d]) = some v') ∧
      decodeValueFromBytes defaultCodecFuel layouts
          { kind := .array (.uint .u64) 2, layoutIdx := idx₂ }
          (u32LE.encodeElems [a, b, c, d]) =
        some (bitVecArrayValue 8 [concat32 a b, concat32 c d]) := by
  refine ⟨bitVecArray_transmute_sound layouts .u32 .u64 2 idx₁ idx₂ [a, b, c, d] rfl, ?_⟩
  rw [canary3_bytes_eq]
  exact decodeValueFromBytes_encodeElems_bitVecLE layouts .u64 idx₂ [concat32 a b, concat32 c d]

/-- Canary 3h (byte reversal of `bswap` + `chunksOf_extractInitBvBytes` + `chunksOf_of_encodeListWith`):
byte-swapping a 32-bit or 64-bit word reverses its `bitVecLE` encoding, `extractInitBvBytes`
commutes with `chunksOf 4`, and `chunksOf 4` recovers the per-element `encodeListWith` slices. -/
theorem canary3_bswap_and_chunksOf_commute (layouts : LayoutTable) (a b c d : BitVec 32)
    (w : BitVec 64) :
    u32LE.encode (Anneal.BitVecArith.bswap32 a) = (u32LE.encode a).reverse ∧
      u64LE.encode (Anneal.BitVecArith.bswap64 w) = (u64LE.encode w).reverse ∧
      (Anneal.ListChunks.chunksOf 4 (u32LE.encodeElems [a, b, c, d])).map extractInitBvBytes =
        Anneal.ListChunks.chunksOf 4 (extractInitBvBytes (u32LE.encodeElems [a, b, c, d])) ∧
      (Anneal.ListChunks.chunksOf 4 (u32LE.encodeElems [a, b, c, d])).map some =
        ([a, b, c, d].map (fun x => Value.scalar ⟨x.toNat, 4⟩)).map
          (fun e => encodeValueToBytes 15 layouts { kind := .uint .u32, layoutIdx := 0 } e) :=
  ⟨bitVecLE_encode_bswapBytes 4 (by decide) a,
    bitVecLE_encode_bswapBytes 8 (by decide) w,
    chunksOf_extractInitBvBytes 4 _
      (FixedByteCodec.allBytesInitialized_encodeElems (bitVecLE_isInitCodec 4 (by decide)) _),
    chunksOf_of_encodeListWith
      (fun e => encodeValueToBytes 15 layouts { kind := .uint .u32, layoutIdx := 0 } e)
      (by decide) (canary3_encodeListWith layouts a b c d)⟩

/-- Canary 3g (pair injectivity through `encodeListWith`,
`Anneal.LeBytes.toLeBytes_append_injective`): two `[u32; 2]` arrays with the same
`encodeListWith` bytes are equal element by element. -/
theorem canary3_pair_injective (layouts : LayoutTable) {a₁ b₁ a₂ b₂ : BitVec 32}
    (h : encodeListWith
          (fun e => encodeValueToBytes 15 layouts { kind := .uint .u32, layoutIdx := 0 } e) 4
          [Value.scalar ⟨a₁.toNat, 4⟩, Value.scalar ⟨b₁.toNat, 4⟩] =
        encodeListWith
          (fun e => encodeValueToBytes 15 layouts { kind := .uint .u32, layoutIdx := 0 } e) 4
          [Value.scalar ⟨a₂.toNat, 4⟩, Value.scalar ⟨b₂.toNat, 4⟩]) :
    a₁ = a₂ ∧ b₁ = b₂ :=
  encodeListWith_pair_injective (sz := 4) (by decide)
    (fun e => encodeValueToBytes 15 layouts { kind := .uint .u32, layoutIdx := 0 } e)
    (fun x => Value.scalar ⟨x.toNat, 4⟩) (fun _ => rfl) h

/-- Canary 3 is not vacuous: the concrete array `[0x04030201, 0x08070605]` encodes to the bytes
`1, 2, ..., 8`, and its pair concatenation is `0x0807060504030201`. -/
theorem canary3_witness :
    u32LE.encodeElems [0x04030201#32, 0x08070605#32] =
        [1#8, 2#8, 3#8, 4#8, 5#8, 6#8, 7#8, 8#8].map (bvByteToAbstract none) ∧
      concat32 0x04030201#32 0x08070605#32 = 0x0807060504030201#64 :=
  ⟨rfl, by decide⟩

/-! ## 4. Canary 4: Negative Counterexample Refutations -/

/-- Canary 4a (overlapping bitmask collision): without the disjoint-mask hypothesis,
`bitwiseOrBits 32` is not injective. The distinct canonical pairs `(1, 2)` and `(3, 0)` have the
same OR. -/
theorem canary4_or_collision :
    ((1 : Nat), (2 : Nat)) ≠ (3, 0) ∧ bitwiseOrBits 32 1 2 = bitwiseOrBits 32 3 0 :=
  ⟨by decide, rfl⟩

/-- Canary 4a (`¬ Injective`): OR-packing of two arbitrary 32-bit operands is not injective. -/
theorem canary4_or_not_injective :
    ¬ Function.Injective (fun p : Nat × Nat => bitwiseOrBits 32 p.1 p.2) := by
  intro h
  have he : ((1 : Nat), (2 : Nat)) = (3, 0) := h canary4_or_collision.2
  exact canary4_or_collision.1 he

/-- Canary 4a (overlapping header fields): if `flags` were given 16 bits at offset 16, it would
overlap `version` at offset 28, and two distinct in-range headers would collide. The
disjointness hypothesis of `pack_disjoint_injective` is therefore necessary. -/
theorem canary4_overlapping_fields_collide :
    ((1 : Nat), (0 : Nat)) ≠ (0, 0x1000) ∧ (1 : Nat) < 2 ^ 4 ∧ (0x1000 : Nat) < 2 ^ 16 ∧
      bitwiseOrBits 32 (shiftLeftBits 1 28 (scalarModulus 4))
          (shiftLeftBits 0 16 (scalarModulus 4)) =
        bitwiseOrBits 32 (shiftLeftBits 0 28 (scalarModulus 4))
          (shiftLeftBits 0x1000 16 (scalarModulus 4)) :=
  ⟨by decide, by decide, by decide, rfl⟩

/-- Canary 4a (the mask hypothesis is what fails): the colliding pairs are not separated by any
mask, because a separating mask would make the injectivity theorem apply. -/
theorem canary4_no_separating_mask (mask : Nat)
    (hm₁ : bitwiseAndBits 32 1 mask = 0) (hm₂ : bitwiseAndBits 32 3 mask = 0)
    (hn₁ : bitwiseAndBits 32 2 (bitwiseXorBits 32 (2 ^ 32 - 1) mask) = 0)
    (hn₂ : bitwiseAndBits 32 0 (bitwiseXorBits 32 (2 ^ 32 - 1) mask) = 0) : False := by
  have r := bitwiseOrBits_disjoint_injective (w := 32) (a₁ := 1) (b₁ := 2) (a₂ := 3) (b₂ := 0)
    (by decide) (by decide) (by decide) (by decide) hm₁ hm₂ hn₁ hn₂ canary4_or_collision.2
  exact absurd r.1 (by decide)

/-- Canary 4b (malformed chunk buffer): *every* 10-byte buffer splits into `divCeil 10 4 = 3`
chunks of lengths `[4, 4, 2]`, and is rejected (`= none`) by `decodeChunks (bitVecLE 4 _)` and by
`Trusted` `decodeArrayChunksWith` for every element count and every element decoder. -/
theorem canary4_malformed_chunks (bs : List AbstractByte) (hlen : bs.length = 10) :
    Anneal.ListChunks.divCeil 10 4 = 3 ∧
      (Anneal.ListChunks.chunksOf 4 bs).map List.length = [4, 4, 2] ∧
      (∀ k, u32LE.decodeChunks k bs = none) ∧
      (∀ k (decVal : List AbstractByte → Option Value),
        decodeArrayChunksWith decVal 4 k bs = none) := by
  refine ⟨rfl, ?_, fun k => ?_, fun k decVal => ?_⟩
  · have h1 : bs ≠ [] := fun h => by rw [h] at hlen; cases hlen
    have l1 : (bs.drop 4).length = 6 := by rw [List.length_drop, hlen]
    have h2 : bs.drop 4 ≠ [] := fun h => by rw [h] at l1; cases l1
    have l2 : ((bs.drop 4).drop 4).length = 2 := by rw [List.length_drop, l1]
    have h3 : (bs.drop 4).drop 4 ≠ [] := fun h => by rw [h] at l2; cases l2
    have l3 : (((bs.drop 4).drop 4).drop 4).length = 0 := by rw [List.length_drop, l2]
    have h4 : ((bs.drop 4).drop 4).drop 4 = [] := List.length_eq_zero_iff.1 l3
    rw [Anneal.ListChunks.chunksOf_of_nonempty (by decide) h1,
      Anneal.ListChunks.chunksOf_of_nonempty (by decide) h2,
      Anneal.ListChunks.chunksOf_of_nonempty (by decide) h3, h4,
      Anneal.ListChunks.chunksOf_nil]
    simp only [List.map_cons, List.map_nil, List.length_take, hlen, l1, l2]
    rfl
  · exact decodeChunks_eq_none_of_length_ne u32LE (by decide) (by omega)
  · exact decodeArrayChunksWith_eq_none_of_length_ne decVal (by decide) (by omega)

/-- Canary 4b is not vacuous: two valid `u32` chunks followed by two stray bytes form a 10-byte
buffer, so the rejection is caused by the short trailing chunk alone. -/
theorem canary4_malformed_witness (a b : BitVec 32) (x y : BitVec 8) :
    (u32LE.encode a ++ u32LE.encode b ++
        [bvByteToAbstract none x, bvByteToAbstract none y]).length = 10 ∧
      u32LE.decodeChunks 2 (u32LE.encode a ++ u32LE.encode b ++
        [bvByteToAbstract none x, bvByteToAbstract none y]) = none ∧
      u32LE.decodeChunks 3 (u32LE.encode a ++ u32LE.encode b ++
        [bvByteToAbstract none x, bvByteToAbstract none y]) = none := by
  have hl : (u32LE.encode a ++ u32LE.encode b ++
      [bvByteToAbstract none x, bvByteToAbstract none y]).length = 10 := by
    rw [List.length_append, List.length_append, u32LE.encode_length, u32LE.encode_length]
    rfl
  exact ⟨hl, (canary4_malformed_chunks _ hl).2.2.1 2, (canary4_malformed_chunks _ hl).2.2.1 3⟩

/-- An 8-byte buffer of the right length for `[u32; 2]` whose second chunk contains one
`.uninit` byte. -/
def poisonedBuffer (a : BitVec 32) (b0 b2 b3 : BitVec 8) : List AbstractByte :=
  u32LE.encode a ++
    [bvByteToAbstract none b0, AbstractByte.uninit, bvByteToAbstract none b2,
      bvByteToAbstract none b3]

/-- Canary 4c (`.uninit` poison): for *every* valid first element and every choice of the three
initialized bytes, the right-length buffer with a single `.uninit` byte is rejected by the
element codec, by `decodeChunks`, by `Trusted` `decodeArrayChunksWith` with the MIR `u32`
decoder, and by `decodeValueFromBytes` at `[u32; 2]`. -/
theorem canary4_uninit_poison (layouts : LayoutTable) (idx : LayoutIdx) (a : BitVec 32)
    (b0 b2 b3 : BitVec 8) :
    (poisonedBuffer a b0 b2 b3).length = 2 * 4 ∧
      u32LE.decode [bvByteToAbstract none b0, AbstractByte.uninit, bvByteToAbstract none b2,
        bvByteToAbstract none b3] = none ∧
      u32LE.decodeChunks 2 (poisonedBuffer a b0 b2 b3) = none ∧
      decodeArrayChunksWith
        (fun ch => decodeValueFromBytes 15 layouts { kind := .uint .u32, layoutIdx := 0 } ch)
        4 2 (poisonedBuffer a b0 b2 b3) = none ∧
      decodeValueFromBytes defaultCodecFuel layouts
        { kind := .array (.uint .u32) 2, layoutIdx := idx } (poisonedBuffer a b0 b2 b3) = none := by
  have hl : (poisonedBuffer a b0 b2 b3).length = 2 * 4 := by
    unfold poisonedBuffer
    rw [List.length_append, u32LE.encode_length]
    rfl
  have hbad : u32LE.decode [bvByteToAbstract none b0, AbstractByte.uninit,
      bvByteToAbstract none b2, bvByteToAbstract none b3] = none :=
    bitVecLE_decode_eq_none_of_uninit 4 (by decide) rfl
  have hchunks : Anneal.ListChunks.chunksOf 4 (poisonedBuffer a b0 b2 b3) =
      [u32LE.encode a, [bvByteToAbstract none b0, AbstractByte.uninit, bvByteToAbstract none b2,
        bvByteToAbstract none b3]] := by
    unfold poisonedBuffer
    rw [Anneal.ListChunks.chunksOf_append_exact (by decide) _ _
        (by rw [u32LE.encode_length]),
      chunksOf_eq_singleton (by decide) (u32LE.encode_length a),
      chunksOf_eq_singleton (n := 4)
        (xs := [bvByteToAbstract none b0, AbstractByte.uninit, bvByteToAbstract none b2,
          bvByteToAbstract none b3]) (by decide) rfl]
    rfl
  have hmem : [bvByteToAbstract none b0, AbstractByte.uninit, bvByteToAbstract none b2,
      bvByteToAbstract none b3] ∈ Anneal.ListChunks.chunksOf 4 (poisonedBuffer a b0 b2 b3) := by
    rw [hchunks]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  refine ⟨hl, hbad, decodeChunks_eq_none_of_chunk u32LE (by decide) 2 hmem hbad, ?_, ?_⟩
  · rw [decodeArrayChunksWith_eq_chunksOf _ (by decide), hchunks]
    simp only [hl, ↓reduceIte, List.map_cons, List.map_nil]
    exact sequenceOptions_eq_none_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rw [(MirValueCodec.uintArray layouts .u32 2 (by decide) idx).decode_eq_map]
    have hbad' : (FixedByteCodec.uintBitsLE 4 (by decide)).decode
        [bvByteToAbstract none b0, AbstractByte.uninit, bvByteToAbstract none b2,
          bvByteToAbstract none b3] = none := rfl
    have hnone : (FixedByteCodec.uintBitsLE 4 (by decide)).decodeChunks 2
        (poisonedBuffer a b0 b2 b3) = none :=
      decodeChunks_eq_none_of_chunk _ (by decide) 2 hmem hbad'
    show ((FixedByteCodec.uintBitsLE 4 (by decide)).decodeChunks 2
      (poisonedBuffer a b0 b2 b3)).map _ = none
    rw [hnone]
    rfl

/-- Canary 4c is not vacuous: replacing the `.uninit` byte by an initialized byte makes the same
buffer decode, so the rejection is caused by the `.uninit` byte alone. -/
theorem canary4_uninit_poison_contrast (a b : BitVec 32) :
    (u32LE.decodeChunks 2 (u32LE.encode a ++ u32LE.encode b)).map Subtype.val = some [a, b] := by
  have h := decodeChunks_encodeElems_val u32LE [a, b]
  have he : u32LE.encodeElems [a, b] = u32LE.encode a ++ u32LE.encode b :=
    congrArg (u32LE.encode a ++ ·) (List.append_nil _)
  rw [he] at h
  exact h

/-- Canary 4d (wrong element count): the 16 bytes of a `[u32; 4]` are rejected when decoded as
three or five elements. -/
theorem canary4_wrong_count (a b c d : BitVec 32) :
    u32LE.decodeChunks 3 (u32LE.encodeElems [a, b, c, d]) = none ∧
      u32LE.decodeChunks 5 (u32LE.encodeElems [a, b, c, d]) = none := by
  have hl : (u32LE.encodeElems [a, b, c, d]).length = 16 :=
    FixedByteCodec.length_encodeElems u32LE [a, b, c, d]
  exact ⟨decodeChunks_eq_none_of_length_ne u32LE (by decide) (by rw [hl]; decide),
    decodeChunks_eq_none_of_length_ne u32LE (by decide) (by rw [hl]; decide)⟩

/-! ### 4.1 Sign-Flag Independence, Operational Lifts and Signed-Integer Arrays -/

/-- The sign flag is irrelevant to `.bitOr` and `.shl` on *every* pair of scalars, but not to
`.shr` or `.lt`: at one byte, `0x80 >> 1` is `0xC0` signed and `0x40` unsigned, and
`0x80 < 0x7F` holds signed only. The flag-generalized pack lemmas therefore keep the logical
shift pinned to `false`. -/
theorem signFlag_irrel_and_counterexamples (x y : ScalarInt) :
    Anneal.Scalars.evalBinOp .bitOr x y true = Anneal.Scalars.evalBinOp .bitOr x y false ∧
      Anneal.Scalars.evalBinOp .shl x y true = Anneal.Scalars.evalBinOp .shl x y false ∧
      Anneal.Scalars.evalBinOp .shr ⟨0x80, 1⟩ ⟨1, 1⟩ true ≠
        Anneal.Scalars.evalBinOp .shr ⟨0x80, 1⟩ ⟨1, 1⟩ false ∧
      Anneal.Scalars.evalBinOp .lt ⟨0x80, 1⟩ ⟨0x7F, 1⟩ true ≠
        Anneal.Scalars.evalBinOp .lt ⟨0x80, 1⟩ ⟨0x7F, 1⟩ false := by
  refine ⟨evalBinOp_isSigned_irrel (Or.inr (Or.inl rfl)) x y true false,
    evalBinOp_isSigned_irrel (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) x y true false,
    fun h => ?_, fun h => ?_⟩
  · rw [Anneal.Scalars.evalBinOp_shr_signed (by decide) (by decide),
      Anneal.Scalars.evalBinOp_shr_unsigned (by decide) (by decide)] at h
    exact absurd (ScalarInt.mk.inj (Option.some.inj h)).1 (by decide)
  · rw [Anneal.Scalars.evalBinOp_lt_signed (by decide),
      Anneal.Scalars.evalBinOp_lt_unsigned (by decide)] at h
    exact absurd (congrArg ScalarInt.bits (Option.some.inj h)) (by decide)

/-- Canary 2 with arbitrary sign flags: a two-field header packed with all flags `true` and one
packed with all flags `false` are equal only if the in-range fields are equal. -/
theorem canary2_pack_injective_any_flags {v₁ p₁ v₂ p₂ : Nat}
    (hv₁ : v₁ < 2 ^ 4) (hp₁ : p₁ < 2 ^ 16) (hv₂ : v₂ < 2 ^ 4) (hp₂ : p₂ < 2 ^ 16)
    (h : (Anneal.Scalars.evalBinOp .shl ⟨v₁, 4⟩ ⟨28, 4⟩ true).bind (fun a =>
          (Anneal.Scalars.evalBinOp .shl ⟨p₁, 4⟩ ⟨0, 4⟩ true).bind (fun b =>
            Anneal.Scalars.evalBinOp .bitOr a b true)) =
        (Anneal.Scalars.evalBinOp .shl ⟨v₂, 4⟩ ⟨28, 4⟩ false).bind (fun a =>
          (Anneal.Scalars.evalBinOp .shl ⟨p₂, 4⟩ ⟨0, 4⟩ false).bind (fun b =>
            Anneal.Scalars.evalBinOp .bitOr a b false))) :
    v₁ = v₂ ∧ p₁ = p₂ :=
  evalBinOp_pack_injective_flag (sz := 4) (szR := 4) (by decide) (by decide)
    true true true false false false hv₁ hp₁ hv₂ hp₂ (by decide) (by decide) (by decide) h

/-- Canary 2 on the operational evaluator: for *every* in-range header, `Trusted`
`evalScalarBinOp` computes the logical shift of the packed word and then the masked `version`
field, without touching locals or memory and for either sign flag on the mask. -/
theorem canary2_evalScalarBinOp_fields {version flags payloadLen : Nat}
    (hv : version < 2 ^ 4) (hf : flags < 2 ^ 12) (hp : payloadLen < 2 ^ 16)
    (locals : List LocalSlot) (mem : Memory) (s : Bool) :
    evalScalarBinOp .shr ⟨packHeader version flags payloadLen, 4⟩ ⟨28, 4⟩ locals mem false =
        .ok (.scalar ⟨shiftRightUnsignedBits (packHeader version flags payloadLen) 28, 4⟩)
          locals mem ∧
      evalScalarBinOp .bitAnd
          ⟨shiftRightUnsignedBits (packHeader version flags payloadLen) 28, 4⟩ ⟨2 ^ 4 - 1, 4⟩
          locals mem s = .ok (.scalar ⟨version, 4⟩) locals mem := by
  have e := canary2_fields hv hf hp
  have c := packHeader_lt version flags payloadLen
  have h := evalScalarBinOp_shr_bitAnd_eq_extractField (sz := 4) (szR := 4) (by decide)
    (by decide) c (lo := 28) (by decide) 4 locals mem s
  rw [e.1] at h
  exact h

/-- Canary 1 through the generic operational lift: the tnum transfer proved for
`evalBinOp .sub` holds verbatim for the scalar returned by `Trusted` `evalScalarBinOp .sub`, for
*every* pair of inputs with known low halves `0x1234` and `0x0100` (difference low half
`0x1134`). -/
theorem canary1_operational_lift (x y : ScalarInt)
    (hx : ScalarTnum 4 0xFFFF0000#32 0x00001234#32 x)
    (hy : ScalarTnum 4 0xFFFF0000#32 0x00000100#32 y)
    (locals : List LocalSlot) (mem : Memory) :
    ∃ r, evalScalarBinOp .sub x y locals mem false = .ok (.scalar r) locals mem ∧
      ScalarTnum 4 0xFFFF0000#32 0x00001134#32 r := by
  have h0 := scalarTnum_evalBinOp_sub (by decide) false hx hy
  obtain ⟨r, hr, ht⟩ := evalScalarBinOp_transfer (sz := 4) (by decide)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hx.1 hy.1 false h0 locals mem
  exact ⟨r, hr, scalarTnum_congr (by decide) (by decide) ht⟩

/-- Division by zero is where the two evaluators differ in *how* they fail (`none` vs `.ub`),
for every dividend; on a non-zero divisor the operational result is the lifted one
(`17 % 5 = 2`). -/
theorem operational_divRem_lift (a : Nat) (locals : List LocalSlot) (mem : Memory) :
    Anneal.Scalars.evalBinOp .div ⟨a, 4⟩ ⟨0, 4⟩ false = none ∧
      evalScalarBinOp .div ⟨a, 4⟩ ⟨0, 4⟩ locals mem false = .ub ∧
      evalScalarBinOp .rem ⟨17, 4⟩ ⟨5, 4⟩ locals mem false = .ok (.scalar ⟨2, 4⟩) locals mem := by
  refine ⟨Anneal.Scalars.evalBinOp_div_zero (by decide) false,
    Anneal.Scalars.evalScalarBinOp_div_zero (by decide) locals mem false, ?_⟩
  have h : Anneal.Scalars.evalBinOp .rem ⟨17, 4⟩ ⟨5, 4⟩ false = some ⟨2, 4⟩ := by
    rw [Anneal.Scalars.evalBinOp_rem_unsigned (by decide) (by decide)]
  exact evalScalarBinOp_divRem_unsigned_of_evalBinOp (sz := 4) (by decide) (Or.inr rfl) h
    locals mem

/-- Witness for the signed-array canary: a concrete `[i32; 4]` value encodes. -/
theorem canary3_signed_array_witness (layouts : LayoutTable) (idx : LayoutIdx) :
    ∃ bs, encodeValueToBytes defaultCodecFuel layouts
      { kind := .array (.int .i32) 4, layoutIdx := idx }
      (bitVecArrayValue 4 [1#32, 2#32, 3#32, 4#32]) = some bs :=
  ⟨_, rfl⟩

/-- Canary 3 across signedness: the bytes of *every* `[u32; 4]` decode at `[i64; 2]`, and the
bytes of *every* encodable `[i32; 4]` value decode at `[u64; 2]` and at `[i16; 8]`. -/
theorem canary3_signed_array_transmute (layouts : LayoutTable) (idx₁ idx₂ : LayoutIdx)
    (a b c d : BitVec 32) (v : Value) (bs : List AbstractByte)
    (hEnc : encodeValueToBytes defaultCodecFuel layouts
      { kind := .array (.int .i32) 4, layoutIdx := idx₁ } v = some bs) :
    (∃ v', decodeValueFromBytes defaultCodecFuel layouts
        { kind := .array (.int .i64) 2, layoutIdx := idx₂ }
        (u32LE.encodeElems [a, b, c, d]) = some v') ∧
      (∃ v', decodeValueFromBytes defaultCodecFuel layouts
        { kind := .array (.uint .u64) 2, layoutIdx := idx₂ } bs = some v') ∧
      (∃ v', decodeValueFromBytes defaultCodecFuel layouts
        { kind := .array (.int .i16) 8, layoutIdx := idx₂ } bs = some v') :=
  ⟨array_uint_to_int_transmute_sound layouts .u32 .i64 4 2 idx₁ idx₂ rfl _ _
      (canary3_encodeValueToBytes layouts idx₁ a b c d),
    array_int_to_uint_transmute_sound layouts .i32 .u64 4 2 idx₁ idx₂ rfl v bs hEnc,
    array_int_transmute_sound layouts .i32 .i16 4 8 idx₁ idx₂ rfl v bs hEnc⟩

/-! ## 5. Axiom Audit Guards

Every declaration of `Anneal.BitVecScalarsBridge` (theorems, definitions and instances) and every
theorem and definition of this file is pinned to its exact axiom set. All sets are subsets of
`[propext, Classical.choice, Quot.sound]`; no declaration uses unsound or compiler-trust axioms.
-/

/-- info: 'Anneal.BitVecScalarsBridge.natMod_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.natMod_eq

/-- info: 'Anneal.BitVecScalarsBridge.natDiv_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.natDiv_eq

/-- info: 'Anneal.BitVecScalarsBridge.natPow_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.natPow_eq

/-- info: 'Anneal.BitVecScalarsBridge.natMul_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.natMul_eq

/-- info: 'Anneal.BitVecScalarsBridge.natAdd_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.natAdd_eq

/-- info: 'Anneal.BitVecScalarsBridge.natSub_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.natSub_eq

/-- info: 'Anneal.BitVecScalarsBridge.natLand_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.natLand_eq

/-- info: 'Anneal.BitVecScalarsBridge.natLor_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.natLor_eq

/-- info: 'Anneal.BitVecScalarsBridge.natXor_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.natXor_eq

/-- info: 'Anneal.BitVecScalarsBridge.natShiftLeft_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.natShiftLeft_eq

/-- info: 'Anneal.BitVecScalarsBridge.natShiftRight_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.natShiftRight_eq

/-- info: 'Anneal.BitVecScalarsBridge.seqLength_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.seqLength_eq

/-- info: 'Anneal.BitVecScalarsBridge.natMul_eight' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.natMul_eight

/-- info: 'Anneal.BitVecScalarsBridge.and_eq_core' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.and_eq_core

/-- info: 'Anneal.BitVecScalarsBridge.or_eq_core' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.or_eq_core

/-- info: 'Anneal.BitVecScalarsBridge.xor_eq_core' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.xor_eq_core

/-- info: 'Anneal.BitVecScalarsBridge.not_eq_core' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.not_eq_core

/-- info: 'Anneal.BitVecScalarsBridge.shl_eq_core' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.shl_eq_core

/-- info: 'Anneal.BitVecScalarsBridge.ushr_eq_core' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.ushr_eq_core

/-- info: 'Anneal.BitVecScalarsBridge.setWidth_eq_core' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.setWidth_eq_core

/-- info: 'Anneal.BitVecScalarsBridge.getLsbD_eq_core' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.getLsbD_eq_core

/-- info: 'Anneal.BitVecScalarsBridge.msb_eq_core' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.msb_eq_core

/-- info: 'Anneal.BitVecScalarsBridge.allOnes_eq_core' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.allOnes_eq_core

/-- info: 'Anneal.BitVecScalarsBridge.ashr_eq_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.ashr_eq_core

/-- info: 'Anneal.BitVecScalarsBridge.signExtend_eq_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.signExtend_eq_core

/-- info: 'Anneal.BitVecScalarsBridge.signedKey_eq_toInt_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.signedKey_eq_toInt_add

/-- info: 'Anneal.BitVecScalarsBridge.sle_iff_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.sle_iff_core

/-- info: 'Anneal.BitVecScalarsBridge.slt_iff_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.slt_iff_core

/-- info: 'Anneal.BitVecScalarsBridge.decSle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decSle

/-- info: 'Anneal.BitVecScalarsBridge.decSlt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decSlt

/-- info: 'Anneal.BitVecScalarsBridge.ofNat_toNat_self' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.ofNat_toNat_self

/-- info: 'Anneal.BitVecScalarsBridge.ofNat_eq_ofNat_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.ofNat_eq_ofNat_iff

/-- info: 'Anneal.BitVecScalarsBridge.toLeWidth' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toLeWidth

/-- info: 'Anneal.BitVecScalarsBridge.ofLeWidth' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.ofLeWidth

/-- info: 'Anneal.BitVecScalarsBridge.toNat_toLeWidth' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toNat_toLeWidth

/-- info: 'Anneal.BitVecScalarsBridge.toNat_ofLeWidth' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toNat_ofLeWidth

/-- info: 'Anneal.BitVecScalarsBridge.ofLeWidth_toLeWidth' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.ofLeWidth_toLeWidth

/-- info: 'Anneal.BitVecScalarsBridge.toLeWidth_ofLeWidth' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toLeWidth_ofLeWidth

/-- info: 'Anneal.BitVecScalarsBridge.toLeWidth_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toLeWidth_injective

/-- info: 'Anneal.BitVecScalarsBridge.toLeWidth_ofNat' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toLeWidth_ofNat

/-- info: 'Anneal.BitVecScalarsBridge.scalarModulus_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarModulus_eq

/-- info: 'Anneal.BitVecScalarsBridge.scalarModulus_eq_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarModulus_eq_le

/-- info: 'Anneal.BitVecScalarsBridge.toNat_lt_scalarModulus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toNat_lt_scalarModulus

/-- info: 'Anneal.BitVecScalarsBridge.wrapScalarBits_eq_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.wrapScalarBits_eq_toNat

/-- info: 'Anneal.BitVecScalarsBridge.toNat_ofNat_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toNat_ofNat_of_lt

/-- info: 'Anneal.BitVecScalarsBridge.wrapScalarBits_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.wrapScalarBits_of_lt

/-- info: 'Anneal.BitVecScalarsBridge.bitwiseAndBits_eq_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitwiseAndBits_eq_and

/-- info: 'Anneal.BitVecScalarsBridge.bitwiseOrBits_eq_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitwiseOrBits_eq_or

/-- info: 'Anneal.BitVecScalarsBridge.bitwiseXorBits_eq_xor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitwiseXorBits_eq_xor

/-- info: 'Anneal.BitVecScalarsBridge.bitwiseAndBits_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitwiseAndBits_toNat

/-- info: 'Anneal.BitVecScalarsBridge.bitwiseOrBits_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitwiseOrBits_toNat

/-- info: 'Anneal.BitVecScalarsBridge.bitwiseXorBits_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitwiseXorBits_toNat

/-- info: 'Anneal.BitVecScalarsBridge.bitwiseXorBits_allOnes_eq_not' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitwiseXorBits_allOnes_eq_not

/-- info: 'Anneal.BitVecScalarsBridge.shiftLeftBits_eq_shl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.shiftLeftBits_eq_shl

/-- info: 'Anneal.BitVecScalarsBridge.shiftRightUnsignedBits_eq_ushr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.shiftRightUnsignedBits_eq_ushr

/-- info: 'Anneal.BitVecScalarsBridge.shiftRightUnsignedBits_eq_ushr_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.shiftRightUnsignedBits_eq_ushr_of_lt

/-- info: 'Anneal.BitVecScalarsBridge.shiftRightUnsignedBits_toNat' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.shiftRightUnsignedBits_toNat

/-- info: 'Anneal.BitVecScalarsBridge.isSignedNegative_eq_msb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.isSignedNegative_eq_msb

/-- info: 'Anneal.BitVecScalarsBridge.ashr_of_width_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.ashr_of_width_le

/-- info: 'Anneal.BitVecScalarsBridge.arithmeticShrBits_of_width_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.arithmeticShrBits_of_width_le

/-- info: 'Anneal.BitVecScalarsBridge.arithmeticShrBits_eq_ashr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.arithmeticShrBits_eq_ashr

/-- info: 'Anneal.BitVecScalarsBridge.arithmeticShrBits_wrap_eq_ashr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.arithmeticShrBits_wrap_eq_ashr

/-- info: 'Anneal.BitVecScalarsBridge.signExtendBits_eq_signExtend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.signExtendBits_eq_signExtend

/-- info: 'Anneal.BitVecScalarsBridge.signedLt_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.signedLt_eq_true_iff

/-- info: 'Anneal.BitVecScalarsBridge.signedLe_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.signedLe_eq_true_iff

/-- info: 'Anneal.BitVecScalarsBridge.signedLt_eq_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.signedLt_eq_decide

/-- info: 'Anneal.BitVecScalarsBridge.signedLe_eq_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.signedLe_eq_decide

/-- info: 'Anneal.BitVecScalarsBridge.add_mod_eq_toNat_add' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.add_mod_eq_toNat_add

/-- info: 'Anneal.BitVecScalarsBridge.sub_mod_eq_toNat_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.sub_mod_eq_toNat_sub

/-- info: 'Anneal.BitVecScalarsBridge.beq_zero_of_pos' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.beq_zero_of_pos

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_bitAnd_eq_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_bitAnd_eq_and

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_bitOr_eq_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_bitOr_eq_or

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_bitXor_eq_xor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_bitXor_eq_xor

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_shl_eq_shl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_shl_eq_shl

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_shr_unsigned_eq_ushr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_shr_unsigned_eq_ushr

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_shr_signed_eq_ashr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_shr_signed_eq_ashr

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_add_eq_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_add_eq_add

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_sub_eq_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_sub_eq_sub

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_lt_signed_eq_slt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_lt_signed_eq_slt

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_le_signed_eq_sle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_le_signed_eq_sle

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_gt_signed_eq_slt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_gt_signed_eq_slt

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_ge_signed_eq_sle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_ge_signed_eq_sle

/-- info: 'Anneal.BitVecScalarsBridge.mul_mod_eq_toNat_mul' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.mul_mod_eq_toNat_mul

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_mul_eq_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_mul_eq_mul

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_div_unsigned_eq_udiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_div_unsigned_eq_udiv

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_rem_unsigned_eq_urem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_rem_unsigned_eq_urem

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_eq_none_of_size_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_eq_none_of_size_zero

/-- info: 'Anneal.BitVecScalarsBridge.evalUnOp_not_eq_not' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalUnOp_not_eq_not

/-- info: 'Anneal.BitVecScalarsBridge.evalUnOp_neg_eq_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalUnOp_neg_eq_neg

/-- info: 'Anneal.BitVecScalarsBridge.evalUnaryNot_uint_eq_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalUnaryNot_uint_eq_not

/-- info: 'Anneal.BitVecScalarsBridge.evalUnaryNot_int_eq_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalUnaryNot_int_eq_not

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_bitAnd_eq_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_bitAnd_eq_and

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_bitOr_eq_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_bitOr_eq_or

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_bitXor_eq_xor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_bitXor_eq_xor

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_shl_eq_shl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_shl_eq_shl

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_shr_unsigned_eq_ushr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_shr_unsigned_eq_ushr

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_shr_signed_eq_ashr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_shr_signed_eq_ashr

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_add_eq_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_add_eq_add

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_sub_eq_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_sub_eq_sub

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_mul_eq_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_mul_eq_mul

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_div_unsigned_eq_udiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_div_unsigned_eq_udiv

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_rem_unsigned_eq_urem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_rem_unsigned_eq_urem

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_lt_signed_eq_slt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_lt_signed_eq_slt

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_le_signed_eq_sle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_le_signed_eq_sle

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_gt_signed_eq_slt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_gt_signed_eq_slt

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_ge_signed_eq_sle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_ge_signed_eq_sle

/-- info: 'Anneal.BitVecScalarsBridge.evalWrappingAdd_eq_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalWrappingAdd_eq_add

/-- info: 'Anneal.BitVecScalarsBridge.evalWrappingSub_eq_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalWrappingSub_eq_sub

/-- info: 'Anneal.BitVecScalarsBridge.evalWrappingAdd_eq_none_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalWrappingAdd_eq_none_iff

/-- info: 'Anneal.BitVecScalarsBridge.evalWrappingSub_eq_none_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalWrappingSub_eq_none_iff

/-- info: 'Anneal.BitVecScalarsBridge.evalWrappingMul_eq_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalWrappingMul_eq_mul

/-- info: 'Anneal.BitVecScalarsBridge.evalWrappingMul_eq_none_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalWrappingMul_eq_none_iff

/-- info: 'Anneal.BitVecScalarsBridge.eq_of_ofNat_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.eq_of_ofNat_eq

/-- info: 'Anneal.BitVecScalarsBridge.bitwiseAndBits_lt_scalarModulus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitwiseAndBits_lt_scalarModulus

/-- info: 'Anneal.BitVecScalarsBridge.bitwiseOrBits_lt_scalarModulus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitwiseOrBits_lt_scalarModulus

/-- info: 'Anneal.BitVecScalarsBridge.bitwiseXorBits_lt_scalarModulus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitwiseXorBits_lt_scalarModulus

/-- info: 'Anneal.BitVecScalarsBridge.shiftLeftBits_lt_scalarModulus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.shiftLeftBits_lt_scalarModulus

/-- info: 'Anneal.BitVecScalarsBridge.bitwiseOrBits_disjoint_injective_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitwiseOrBits_disjoint_injective_mod

/-- info: 'Anneal.BitVecScalarsBridge.bitwiseOrBits_disjoint_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitwiseOrBits_disjoint_injective

/-- info: 'Anneal.BitVecScalarsBridge.bitwiseOrBits_aligned_bounded_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitwiseOrBits_aligned_bounded_injective

/-- info: 'Anneal.BitVecScalarsBridge.shiftLeftBits_eq_mul_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.shiftLeftBits_eq_mul_of_lt

/-- info: 'Anneal.BitVecScalarsBridge.shiftLeftBits_or_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.shiftLeftBits_or_injective

/-- info: 'Anneal.BitVecScalarsBridge.extractField' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.extractField

/-- info: 'Anneal.BitVecScalarsBridge.extractField_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.extractField_toNat

/-- info: 'Anneal.BitVecScalarsBridge.extractField_eq_extractBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.extractField_eq_extractBits

/-- info: 'Anneal.BitVecScalarsBridge.extractField_wrap_eq_extractBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.extractField_wrap_eq_extractBits

/-- info: 'Anneal.BitVecScalarsBridge.extractField_bitwiseOrBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.extractField_bitwiseOrBits

/-- info: 'Anneal.BitVecScalarsBridge.ofNat_eq_setWidth_ofNat' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.ofNat_eq_setWidth_ofNat

/-- info: 'Anneal.BitVecScalarsBridge.extractField_shiftLeftBits_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.extractField_shiftLeftBits_self

/-- info: 'Anneal.BitVecScalarsBridge.extractField_shiftLeftBits_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.extractField_shiftLeftBits_disjoint

/-- info: 'Anneal.BitVecScalarsBridge.extractField_pack_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.extractField_pack_disjoint

/-- info: 'Anneal.BitVecScalarsBridge.pack_disjoint_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.pack_disjoint_injective

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_shr_bitAnd_eq_extractField' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_shr_bitAnd_eq_extractField

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_shl_bitOr_eq_pack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_shl_bitOr_eq_pack

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_bitOr_disjoint_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_bitOr_disjoint_injective

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_pack_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_pack_injective

/-- info: 'Anneal.BitVecScalarsBridge.ScalarTnum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.ScalarTnum

/-- info: 'Anneal.BitVecScalarsBridge.ScalarRange' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.ScalarRange

/-- info: 'Anneal.BitVecScalarsBridge.ScalarSRange' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.ScalarSRange

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_of_bitVec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_of_bitVec

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_exists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_exists

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_zero_mask_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_zero_mask_iff

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_allOnes_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_allOnes_iff

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_not_noncanonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_not_noncanonical

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_canonical

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_mono

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_inter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_inter

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_of_scalarTnum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_of_scalarTnum

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_not_noncanonical' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_not_noncanonical

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_not_noncanonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_not_noncanonical

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_of_bitVec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_of_bitVec

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_exists' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_exists

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_iff_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_iff_bits

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_of_bitVec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_of_bitVec

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_exists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_exists

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_bitwiseAndBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_bitwiseAndBits

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_bitwiseOrBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_bitwiseOrBits

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_bitwiseXorBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_bitwiseXorBits

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_shiftLeftBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_shiftLeftBits

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_shiftRightUnsignedBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_shiftRightUnsignedBits

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_arithmeticShrBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_arithmeticShrBits

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_signExtendBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_signExtendBits

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_bitAnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_bitAnd

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_bitOr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_bitOr

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_bitXor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_bitXor

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_shl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_shl

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_shr_unsigned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_shr_unsigned

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_shr_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_shr_signed

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_extractField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_extractField

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalUnOp_not' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalUnOp_not

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalUnaryNot_uint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalUnaryNot_uint

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalUnaryNot_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalUnaryNot_int

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_bitAnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_bitAnd

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_bitOr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_bitOr

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_bitXor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_bitXor

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_shl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_shl

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_shr_unsigned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_shr_unsigned

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_shr_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_shr_signed

/-- info: 'Anneal.BitVecScalarsBridge.tnumAddMask' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.tnumAddMask

/-- info: 'Anneal.BitVecScalarsBridge.tnumAddValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.tnumAddValue

/-- info: 'Anneal.BitVecScalarsBridge.tnumSubMask' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.tnumSubMask

/-- info: 'Anneal.BitVecScalarsBridge.tnumSubValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.tnumSubValue

/-- info: 'Anneal.BitVecScalarsBridge.tnumAdd_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.tnumAdd_sound

/-- info: 'Anneal.BitVecScalarsBridge.tnumSub_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.tnumSub_sound

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_add

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalBinOp_sub

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalWrappingAdd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalWrappingAdd

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalWrappingSub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalWrappingSub

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_add

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalScalarBinOp_sub

/-- info: 'Anneal.BitVecScalarsBridge.maskEq_inter_nonempty_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.maskEq_inter_nonempty_iff

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_empty_of_conflict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_empty_of_conflict

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_inter_nonempty_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_inter_nonempty_iff

/-- info: 'Anneal.BitVecScalarsBridge.rangeAddLo' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.rangeAddLo

/-- info: 'Anneal.BitVecScalarsBridge.rangeAddHi' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.rangeAddHi

/-- info: 'Anneal.BitVecScalarsBridge.rangeAdd_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.rangeAdd_sound

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalBinOp_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalBinOp_add

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalWrappingAdd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalWrappingAdd

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_shiftRightUnsignedBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_shiftRightUnsignedBits

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalBinOp_shr_unsigned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalBinOp_shr_unsigned

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_evalBinOp_add_no_overflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_evalBinOp_add_no_overflow

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_refine_signedLt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_refine_signedLt

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_refine_signedLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_refine_signedLe

/-- info: 'Anneal.BitVecScalarsBridge.boolToScalar_eq_true_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.boolToScalar_eq_true_iff

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_refine_evalBinOp_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_refine_evalBinOp_lt

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_refine_evalBinOp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_refine_evalBinOp_le

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_intersect' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_intersect

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_intersect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_intersect

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalScalarBinOp_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalScalarBinOp_add

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalScalarBinOp_shr_unsigned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalScalarBinOp_shr_unsigned

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalBinOp_sub_no_underflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalBinOp_sub_no_underflow

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalWrappingSub_no_underflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalWrappingSub_no_underflow

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalBinOp_mul_no_overflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalBinOp_mul_no_overflow

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalWrappingMul_no_overflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalWrappingMul_no_overflow

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalBinOp_div_unsigned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalBinOp_div_unsigned

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalBinOp_rem_unsigned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalBinOp_rem_unsigned

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalBinOp_shl_no_overflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalBinOp_shl_no_overflow

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_evalWrappingAdd_no_overflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_evalWrappingAdd_no_overflow

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_evalScalarBinOp_add_no_overflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_evalScalarBinOp_add_no_overflow

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_refine_evalBinOp_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_refine_evalBinOp_gt

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_refine_evalBinOp_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_refine_evalBinOp_ge

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_refine_evalScalarBinOp_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_refine_evalScalarBinOp_lt

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_refine_evalScalarBinOp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_refine_evalScalarBinOp_le

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_refine_evalScalarBinOp_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_refine_evalScalarBinOp_gt

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_refine_evalScalarBinOp_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_refine_evalScalarBinOp_ge

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_refine_evalBinOp_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_refine_evalBinOp_lt

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_refine_evalBinOp_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_refine_evalBinOp_le

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_refine_evalBinOp_gt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_refine_evalBinOp_gt

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_refine_evalBinOp_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_refine_evalBinOp_ge

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_of_scalarRange_clz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_of_scalarRange_clz

/-- info: 'Anneal.BitVecScalarsBridge.ctpopLoop_eq_trusted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.ctpopLoop_eq_trusted

/-- info: 'Anneal.BitVecScalarsBridge.cttzLoop_eq_trusted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.cttzLoop_eq_trusted

/-- info: 'Anneal.BitVecScalarsBridge.bitreverseLoop_eq_trusted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitreverseLoop_eq_trusted

/-- info: 'Anneal.BitVecScalarsBridge.ctlzBits_eq_trusted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.ctlzBits_eq_trusted

/-- info: 'Anneal.BitVecScalarsBridge.bswapLoop_eq_trusted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bswapLoop_eq_trusted

/-- info: 'Anneal.BitVecScalarsBridge.testBit_bitreverseLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.testBit_bitreverseLoop

/-- info: 'Anneal.BitVecScalarsBridge.cttzLoop_eq_clzAux' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.cttzLoop_eq_clzAux

/-- info: 'Anneal.BitVecScalarsBridge.ctlzBits_eq_clz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.ctlzBits_eq_clz

/-- info: 'Anneal.BitVecScalarsBridge.scalars_ctlzBits_eq_clz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalars_ctlzBits_eq_clz

/-- info: 'Anneal.BitVecScalarsBridge.evalCtlz_eq_clz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalCtlz_eq_clz

/-- info: 'Anneal.BitVecScalarsBridge.evalCtlz_eq_none_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalCtlz_eq_none_iff

/-- info: 'Anneal.BitVecScalarsBridge.evalCtlz_bits_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalCtlz_bits_le

/-- info: 'Anneal.BitVecScalarsBridge.evalCtlzNonzero_eq_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalCtlzNonzero_eq_none_iff

/-- info: 'Anneal.BitVecScalarsBridge.evalCtlzNonzero_eq_none_of_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalCtlzNonzero_eq_none_of_zero

/-- info: 'Anneal.BitVecScalarsBridge.evalCtlzNonzero_eq_clz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalCtlzNonzero_eq_clz

/-- info: 'Anneal.BitVecScalarsBridge.clz_antitone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.clz_antitone

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_of_scalarRange_ctlzBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_of_scalarRange_ctlzBits

/-- info: 'Anneal.BitVecScalarsBridge.bswapLoop_eq_fromBeBytes_acc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bswapLoop_eq_fromBeBytes_acc

/-- info: 'Anneal.BitVecScalarsBridge.bswapLoop_eq_fromBeBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bswapLoop_eq_fromBeBytes

/-- info: 'Anneal.BitVecScalarsBridge.testBit_fromLeBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.testBit_fromLeBytes

/-- info: 'Anneal.BitVecScalarsBridge.toNat_bswapBytes_eq_fromBeBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toNat_bswapBytes_eq_fromBeBytes

/-- info: 'Anneal.BitVecScalarsBridge.toNat_bswapBytes_eq_bswapLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toNat_bswapBytes_eq_bswapLoop

/-- info: 'Anneal.BitVecScalarsBridge.toLeBytes_bswapBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toLeBytes_bswapBytes

/-- info: 'Anneal.BitVecScalarsBridge.evalBswap_eq_bswapBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBswap_eq_bswapBytes

/-- info: 'Anneal.BitVecScalarsBridge.evalBswap_eq_none_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBswap_eq_none_iff

/-- info: 'Anneal.BitVecScalarsBridge.evalBswap_evalBswap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBswap_evalBswap

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalBswap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalBswap

/-- info: 'Anneal.BitVecScalarsBridge.swapBytes16_eq_bswap16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.swapBytes16_eq_bswap16

/-- info: 'Anneal.BitVecScalarsBridge.swapBytes32_eq_bswap32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.swapBytes32_eq_bswap32

/-- info: 'Anneal.BitVecScalarsBridge.swapBytes64_eq_bswap64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.swapBytes64_eq_bswap64

/-- info: 'Anneal.BitVecScalarsBridge.toNat_bswap16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toNat_bswap16

/-- info: 'Anneal.BitVecScalarsBridge.toNat_bswap32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toNat_bswap32

/-- info: 'Anneal.BitVecScalarsBridge.toNat_bswap64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toNat_bswap64

/-- info: 'Anneal.BitVecScalarsBridge.evalBswap_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBswap_two

/-- info: 'Anneal.BitVecScalarsBridge.evalBswap_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBswap_four

/-- info: 'Anneal.BitVecScalarsBridge.evalBswap_eight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBswap_eight

/-- info: 'Anneal.BitVecScalarsBridge.bvByteToAbstract' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bvByteToAbstract

/-- info: 'Anneal.BitVecScalarsBridge.extractInitBvBytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.extractInitBvBytes

/-- info: 'Anneal.BitVecScalarsBridge.bvByteToAbstract_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bvByteToAbstract_injective

/-- info: 'Anneal.BitVecScalarsBridge.allBytesInitialized_map_bvByteToAbstract' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.allBytesInitialized_map_bvByteToAbstract

/-- info: 'Anneal.BitVecScalarsBridge.extractInitBvBytes_map' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.extractInitBvBytes_map

/-- info: 'Anneal.BitVecScalarsBridge.map_bvByteToAbstract_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.map_bvByteToAbstract_injective

/-- info: 'Anneal.BitVecScalarsBridge.length_extractInitBvBytes_le' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.length_extractInitBvBytes_le

/-- info: 'Anneal.BitVecScalarsBridge.length_extractInitBvBytes_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.length_extractInitBvBytes_eq_iff

/-- info: 'Anneal.BitVecScalarsBridge.map_extractInitBvBytes_of_uniform' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.map_extractInitBvBytes_of_uniform

/-- info: 'Anneal.BitVecScalarsBridge.extractInitBvBytes_append' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.extractInitBvBytes_append

/-- info: 'Anneal.BitVecScalarsBridge.extractInitBvBytes_take' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.extractInitBvBytes_take

/-- info: 'Anneal.BitVecScalarsBridge.extractInitBvBytes_drop' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.extractInitBvBytes_drop

/-- info: 'Anneal.BitVecScalarsBridge.chunksOf_extractInitBvBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.chunksOf_extractInitBvBytes

/-- info: 'Anneal.BitVecScalarsBridge.encodeLittleEndianBytes_eq_map' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.encodeLittleEndianBytes_eq_map

/-- info: 'Anneal.BitVecScalarsBridge.encodeLittleEndianBytes_toLeBytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.encodeLittleEndianBytes_toLeBytes

/-- info: 'Anneal.BitVecScalarsBridge.decodeLittleEndianBytes_map' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeLittleEndianBytes_map

/-- info: 'Anneal.BitVecScalarsBridge.decodeLittleEndianBytes_map_none' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeLittleEndianBytes_map_none

/-- info: 'Anneal.BitVecScalarsBridge.decodeLittleEndianBytes_of_init' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeLittleEndianBytes_of_init

/-- info: 'Anneal.BitVecScalarsBridge.decodeLittleEndianBytes_eq_none_of_uninit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeLittleEndianBytes_eq_none_of_uninit

/-- info: 'Anneal.BitVecScalarsBridge.decodeLittleEndianBytes_eq_none_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeLittleEndianBytes_eq_none_iff

/-- info: 'Anneal.BitVecScalarsBridge.decodeLittleEndianBytes_encodeLittleEndianBytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeLittleEndianBytes_encodeLittleEndianBytes

/-- info: 'Anneal.BitVecScalarsBridge.encodeScalarBytes_eq_none_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.encodeScalarBytes_eq_none_iff

/-- info: 'Anneal.BitVecScalarsBridge.decodeScalarBytes_map' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeScalarBytes_map

/-- info: 'Anneal.BitVecScalarsBridge.decodeScalarBytes_map_none' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeScalarBytes_map_none

/-- info: 'Anneal.BitVecScalarsBridge.decodeScalarBytes_nil' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeScalarBytes_nil

/-- info: 'Anneal.BitVecScalarsBridge.decodeScalarBytes_eq_none_of_uninit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeScalarBytes_eq_none_of_uninit

/-- info: 'Anneal.BitVecScalarsBridge.decodeScalarBytes_of_init' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeScalarBytes_of_init

/-- info: 'Anneal.BitVecScalarsBridge.decodeScalarBytes_eq_none_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeScalarBytes_eq_none_iff

/-- info: 'Anneal.BitVecScalarsBridge.decodeScalarBytes_encodeLittleEndianBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeScalarBytes_encodeLittleEndianBytes

/-- info: 'Anneal.BitVecScalarsBridge.toLeBytesAux_mod' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toLeBytesAux_mod

/-- info: 'Anneal.BitVecScalarsBridge.toLeBytesAux_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.toLeBytesAux_append

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_encode

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_encode_eq_toLeBytesAux' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_encode_eq_toLeBytesAux

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_encode_eq_toLeBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_encode_eq_toLeBytes

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_decode

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_decode_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_decode_map

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_decode_eq_none_of_length_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_decode_eq_none_of_length_ne

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_decode_eq_none_of_uninit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_decode_eq_none_of_uninit

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_decode_eq_some_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_decode_eq_some_iff

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_isExactWidth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_isExactWidth

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_isInitCodec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_isInitCodec

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_isSurjectiveInitDecoder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_isSurjectiveInitDecoder

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_hasZeroValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_hasZeroValid

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_decode_zeroInitBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_decode_zeroInitBytes

/-- info: 'Anneal.BitVecScalarsBridge.encodeScalarBytes_eq_bitVecLE_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.encodeScalarBytes_eq_bitVecLE_encode

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_encode_bswapBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_encode_bswapBytes

/-- info: 'Anneal.BitVecScalarsBridge.bitVecLE_encode_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecLE_encode_append

/-- info: 'Anneal.BitVecScalarsBridge.sequenceOptions' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.sequenceOptions

/-- info: 'Anneal.BitVecScalarsBridge.sequenceOptions_eq_some_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.sequenceOptions_eq_some_iff

/-- info: 'Anneal.BitVecScalarsBridge.sequenceOptions_eq_none_of_mem' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.sequenceOptions_eq_none_of_mem

/-- info: 'Anneal.BitVecScalarsBridge.chunksOf_eq_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.chunksOf_eq_singleton

/-- info: 'Anneal.BitVecScalarsBridge.length_chunksOf_of_length_eq_mul' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.length_chunksOf_of_length_eq_mul

/-- info: 'Anneal.BitVecScalarsBridge.chunksOf_encodeElems' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.chunksOf_encodeElems

/-- info: 'Anneal.BitVecScalarsBridge.list_map_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.list_map_injective

/-- info: 'Anneal.BitVecScalarsBridge.encodeElems_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.encodeElems_injective

/-- info: 'Anneal.BitVecScalarsBridge.decodeArrayChunksWith_eq_chunksOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeArrayChunksWith_eq_chunksOf

/-- info: 'Anneal.BitVecScalarsBridge.decodeArrayChunksWith_eq_some_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeArrayChunksWith_eq_some_iff

/-- info: 'Anneal.BitVecScalarsBridge.decodeArrayChunksWith_eq_none_of_length_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeArrayChunksWith_eq_none_of_length_ne

/-- info: 'Anneal.BitVecScalarsBridge.decodeArrayChunksWith_eq_none_of_chunk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeArrayChunksWith_eq_none_of_chunk

/-- info: 'Anneal.BitVecScalarsBridge.decodeArrayChunksWith_zero_width' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeArrayChunksWith_zero_width

/-- info: 'Anneal.BitVecScalarsBridge.decodeChunks_zero_width' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeChunks_zero_width

/-- info: 'Anneal.BitVecScalarsBridge.decodeChunks_eq_chunksOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeChunks_eq_chunksOf

/-- info: 'Anneal.BitVecScalarsBridge.decodeChunks_eq_some_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeChunks_eq_some_iff

/-- info: 'Anneal.BitVecScalarsBridge.decodeChunks_eq_none_of_length_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeChunks_eq_none_of_length_ne

/-- info: 'Anneal.BitVecScalarsBridge.decodeChunks_eq_none_of_chunk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeChunks_eq_none_of_chunk

/-- info: 'Anneal.BitVecScalarsBridge.decodeChunks_encodeElems_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeChunks_encodeElems_val

/-- info: 'Anneal.BitVecScalarsBridge.encodeElems_bitVecLE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.encodeElems_bitVecLE

/-- info: 'Anneal.BitVecScalarsBridge.encodeElems_bitVecLE_eq_uintBitsLE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.encodeElems_bitVecLE_eq_uintBitsLE

/-- info: 'Anneal.BitVecScalarsBridge.encodeListWith_pair_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.encodeListWith_pair_injective

/-- info: 'Anneal.BitVecScalarsBridge.encodeListWith_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.encodeListWith_injective

/-- info: 'Anneal.BitVecScalarsBridge.chunksOf_of_encodeListWith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.chunksOf_of_encodeListWith

/-- info: 'Anneal.BitVecScalarsBridge.bitVecArrayValue' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecArrayValue

/-- info: 'Anneal.BitVecScalarsBridge.rigidTyByteSize_array_uint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.rigidTyByteSize_array_uint

/-- info: 'Anneal.BitVecScalarsBridge.encodeValueToBytes_bitVecArray' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.encodeValueToBytes_bitVecArray

/-- info: 'Anneal.BitVecScalarsBridge.decodeValueFromBytes_encodeElems_bitVecLE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.decodeValueFromBytes_encodeElems_bitVecLE

/-- info: 'Anneal.BitVecScalarsBridge.array_uint_transmute_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.array_uint_transmute_sound

/-- info: 'Anneal.BitVecScalarsBridge.bitVecArray_transmute_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.bitVecArray_transmute_sound

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_congr

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_congr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_congr

/-- info: 'Anneal.BitVecScalarsBridge.scalarSRange_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarSRange_congr

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_const' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_const

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_zero_mask_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_zero_mask_bits

/-- info: 'Anneal.BitVecScalarsBridge.evalCastValue_signed_eq_signExtend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalCastValue_signed_eq_signExtend

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalCastValue_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalCastValue_signed

/-- info: 'Anneal.BitVecScalarsBridge.evalCastValue_unsigned_eq_setWidth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalCastValue_unsigned_eq_setWidth

/-- info: 'Anneal.BitVecScalarsBridge.evalCastValue_unsigned_wrap_eq_setWidth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalCastValue_unsigned_wrap_eq_setWidth

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_evalCastValue_unsigned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_evalCastValue_unsigned

/-- info: 'Anneal.BitVecScalarsBridge.clz_eq_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.clz_eq_of_bounds

/-- info: 'Anneal.BitVecScalarsBridge.evalCtlz_eq_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalCtlz_eq_of_bounds

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalCtlz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalCtlz

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalCtlz_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalCtlz_range

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalCtlzNonzero_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalCtlzNonzero_range

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_evalCtlzNonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_evalCtlzNonzero

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_zero_mask_mk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_zero_mask_mk

/-- info: 'Anneal.BitVecScalarsBridge.scalarTnum_bitwiseAndBits_const' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarTnum_bitwiseAndBits_const

/-- info: 'Anneal.BitVecScalarsBridge.scalarRange_mk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.scalarRange_mk

/-- info: 'Anneal.BitVecScalarsBridge.shiftRight_mod_eq_extractBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.shiftRight_mod_eq_extractBits

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_shr_unsigned_eq_extractBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_shr_unsigned_eq_extractBits

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_shr_unsigned_eq_extractBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_shr_unsigned_eq_extractBits

/-- info: 'Anneal.BitVecScalarsBridge.chunksOf_encodeElems_zero_width' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.chunksOf_encodeElems_zero_width

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_isSigned_irrel' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_isSigned_irrel

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_shr_bitAnd_eq_extractField_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_shr_bitAnd_eq_extractField_flag

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_shl_bitOr_eq_pack_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_shl_bitOr_eq_pack_flag

/-- info: 'Anneal.BitVecScalarsBridge.evalBinOp_pack_injective_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalBinOp_pack_injective_flag

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_of_evalBinOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_of_evalBinOp

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_shift_of_evalBinOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_shift_of_evalBinOp

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_divRem_unsigned_of_evalBinOp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_divRem_unsigned_of_evalBinOp

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_transfer

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_shift_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_shift_transfer

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_shr_bitAnd_eq_extractField' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_shr_bitAnd_eq_extractField

/-- info: 'Anneal.BitVecScalarsBridge.evalScalarBinOp_shl_bitOr_eq_pack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.evalScalarBinOp_shl_bitOr_eq_pack

/-- info: 'Anneal.BitVecScalarsBridge.rigidTyByteSize_array_int' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.rigidTyByteSize_array_int

/-- info: 'Anneal.BitVecScalarsBridge.array_int_transmute_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.array_int_transmute_sound

/-- info: 'Anneal.BitVecScalarsBridge.array_uint_to_int_transmute_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.array_uint_to_int_transmute_sound

/-- info: 'Anneal.BitVecScalarsBridge.array_int_to_uint_transmute_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecScalarsBridge.array_int_to_uint_transmute_sound

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.ctlz_width_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.ctlz_width_zero

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.bitwise_width_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.bitwise_width_zero

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.evaluators_reject_size_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.evaluators_reject_size_zero

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.wrapping_rejects_mismatched_widths' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.wrapping_rejects_mismatched_widths

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.shifts_past_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.shifts_past_width

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.ashr_past_width' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.ashr_past_width

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.noncanonical_bits_canonicalized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.noncanonical_bits_canonicalized

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.noncanonical_shr_differs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.noncanonical_shr_differs

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.noncanonical_not_abstracted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.noncanonical_not_abstracted

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.noncanonical_not_abstracted_general' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.noncanonical_not_abstracted_general

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.ctlzNonzero_noncanonical_and_bswap64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.ctlzNonzero_noncanonical_and_bswap64

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.zero_length_array_and_zero_width_chunk_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.zero_length_array_and_zero_width_chunk_edges

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.provenance_byte_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.provenance_byte_edges

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.signExtend_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.signExtend_edges

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.signed_compare_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.signed_compare_edges

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.intrinsics_concrete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.intrinsics_concrete

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.witness_tnum_x' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.witness_tnum_x

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.witness_tnum_y' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.witness_tnum_y

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_tnum_add_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_tnum_add_sub

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_tnum_add_sub_witness' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_tnum_add_sub_witness

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.witness_tnum_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.witness_tnum_negative

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_ashr_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_ashr_negative

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_bswap32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_bswap32

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.witness_tnum_x64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.witness_tnum_x64

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_bswap64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_bswap64

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_bswap64_witness' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_bswap64_witness

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.witness_range_xy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.witness_range_xy

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_range_add_ctlz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_range_add_ctlz

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_range_add_ctlz_witness' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_range_add_ctlz_witness

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_range_add_wrap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_range_add_wrap

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_clz_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_clz_prefix

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_clz_prefix_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_clz_prefix_instance

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.witness_srange_xy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.witness_srange_xy

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_signed_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_signed_range

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_signed_range_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_signed_range_witness

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_prune_conflict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_prune_conflict

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_prune_pipeline' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_prune_pipeline

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_prune_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_prune_exact

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_evalScalarBinOp_pipeline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_evalScalarBinOp_pipeline

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_tnum_meet_range_casts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_tnum_meet_range_casts

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.witness_canary1_meet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.witness_canary1_meet

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_range_arith_and_ctlzNonzero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_range_arith_and_ctlzNonzero

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_range_arith_and_ctlzNonzero_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_range_arith_and_ctlzNonzero_witness

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.packHeader' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.packHeader

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.evalPackHeader' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.evalPackHeader

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.packHeader_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.packHeader_lt

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary2_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary2_fields

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary2_fields_primitives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary2_fields_primitives

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary2_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary2_injective

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary2_extractBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary2_extractBits

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary2_evalPackHeader' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary2_evalPackHeader

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary2_evalBinOp_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary2_evalBinOp_fields

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary2_evalPackHeader_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary2_evalPackHeader_injective

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary2_evalBinOp_pack_zero_width' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary2_evalBinOp_pack_zero_width

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary2_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary2_witness

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.u32LE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.u32LE

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.u64LE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.u64LE

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.concat32' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.concat32

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary3_encodeValueToBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary3_encodeValueToBytes

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary3_encodeListWith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary3_encodeListWith

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary3_chunks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary3_chunks

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.u32_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.u32_roundtrip

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary3_recover_u32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary3_recover_u32

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary3_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary3_decode

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.u32_pair_eq_u64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.u32_pair_eq_u64

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary3_bytes_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary3_bytes_eq

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary3_chunk_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary3_chunk_pairs

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary3_transmute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary3_transmute

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary3_bswap_and_chunksOf_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary3_bswap_and_chunksOf_commute

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary3_pair_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary3_pair_injective

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary3_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary3_witness

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary4_or_collision' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary4_or_collision

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary4_or_not_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary4_or_not_injective

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary4_overlapping_fields_collide' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary4_overlapping_fields_collide

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary4_no_separating_mask' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary4_no_separating_mask

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary4_malformed_chunks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary4_malformed_chunks

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary4_malformed_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary4_malformed_witness

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.poisonedBuffer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.poisonedBuffer

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary4_uninit_poison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary4_uninit_poison

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary4_uninit_poison_contrast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary4_uninit_poison_contrast

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary4_wrong_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary4_wrong_count

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.signFlag_irrel_and_counterexamples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.signFlag_irrel_and_counterexamples

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary2_pack_injective_any_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary2_pack_injective_any_flags

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary2_evalScalarBinOp_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary2_evalScalarBinOp_fields

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary1_operational_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary1_operational_lift

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.operational_divRem_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.operational_divRem_lift

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary3_signed_array_witness' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary3_signed_array_witness

/-- info: 'Anneal.BitVecAndLeBytesBridgeTests.canary3_signed_array_transmute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.BitVecAndLeBytesBridgeTests.canary3_signed_array_transmute

end Anneal.BitVecAndLeBytesBridgeTests
