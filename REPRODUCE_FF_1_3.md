<!--
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-->

# Reproduction Guide: FF-1.3 (`Anneal.Scalars` Fixed-Width `BitVec w` & `Nat` Closed-Form Scalar Lifting)

This document describes how to reproduce and verify Work Unit **FF-1.3**
(`theory/Anneal/Scalars.lean`), which provides closed-form `@[simp]` bridges
between `Trusted.Rustc.V2026_06_01.MirSemantics` recursive bit-by-bit scalar
evaluators and Lean 4's native `Nat` (`&&&`, `|||`, `^^^`, `<<<`, `>>>`) and
fixed-width `BitVec (8 * sz)` representations.

## Summary of Deliverables in `theory/Anneal/Scalars.lean`

1. **Closed-Form Power-of-Two & Modulus Bridges (Section 2)**:
   - `scalarPow2_eq_two_pow : scalarPow2 w = 2 ^ w` (`@[simp]`)
   - `scalarModulus_eq_two_pow : scalarModulus sz = 2 ^ (8 * sz)` (`@[simp]`)
   - `signedHalfModulus_eq_two_pow : signedHalfModulus sz = 2 ^ (8 * sz - 1)`
     (`@[simp]`)
   - `wrapScalarBits_eq_mod_modulus : wrapScalarBits bits sz = bits % (2 ^ (8 * sz))`
     (`@[simp]`)

2. **Closed-Form Bitwise Equivalences (Section 3, Solving Bottleneck 3)**:
   - `bitwiseAndBits_eq_land : bitwiseAndBits w a b = (a &&& b) % (2 ^ w)`
     (`@[simp]`)
   - `bitwiseAndBits_eq_land_of_lt_left` / `bitwiseAndBits_eq_land_of_lt_right`
   - `bitwiseOrBits_eq_lor : bitwiseOrBits w a b = (a ||| b) % (2 ^ w)`
     (`@[simp]`)
   - `bitwiseOrBits_eq_lor_of_lt`
   - `bitwiseXorBits_eq_xor : bitwiseXorBits w a b = (a ^^^ b) % (2 ^ w)`
     (`@[simp]`)
   - `bitwiseXorBits_eq_xor_of_lt`

3. **Shifts, Two's-Complement Sign Bit & Arithmetic Right Shift (Section 4)**:
   - `shiftLeftBits_eq_shiftLeft_mod` (`@[simp]`)
   - `shiftRightUnsignedBits_eq_shiftRight` (`@[simp]`)
   - `isSignedNegative_eq_msb` (`@[simp]`)
   - `arithmeticShrBits_eq_sshiftRight` and
     `arithmeticShrBits_mod_eq_sshiftRight` (`@[simp]`)
   - `toNat_signExtend_of_le`, `toNat_signExtend_ofNat_of_le`,
     `signExtendBits_of_le`, and unconditional `signExtendBits_eq_bitVec`
     (`@[simp]`)

4. **`ScalarValue` & `BitVec (8 * s.sizeBytes)` Isomorphism (Section 5)**:
   - `ScalarValue.toBitVec (s : ScalarValue) : BitVec (8 * s.sizeBytes)`
   - `ScalarValue.ofBitVec {w : Nat} (sz : Nat) (bv : BitVec w) : ScalarValue`
   - Round-trip lemmas: `toBitVec_ofBitVec_same`, `toBitVec_ofBitVec`,
     `ofBitVec_toBitVec_canonical`, `ofBitVec_toBitVec`, and primitive scalar
     constructors (`u8`, `u16`, `u32`, `u64`, `u128`, `usize`, `i8`, `i16`,
     `i32`, `i64`, `i128`, `isize`).

5. **Pure Scalar Evaluators & Closed-Form `@[simp]` Lemmas (Sections 6–8)**:
   - Pure scalar evaluators `evalBinOp`, `evalBinOpChecked`, `evalUnOp`, and
     `evalCastValue` mirroring `Trusted.Rustc.V2026_06_01.MirSemantics`.
   - Closed-form `@[simp]` lemmas for `evalBinOp`, `evalScalarBinOp`,
     `evalCastValue`, `evalExactDiv`, and `evalScalarExactDiv` across `.bitAnd`,
     `.bitOr`, `.bitXor`, `.shl`, `.shr` (both unsigned logical and signed
     two's-complement arithmetic), `.shlUnchecked` / `.shrUnchecked` (both
     in-bounds `< 8 * sz` and out-of-bounds UB `8 * sz ≤ b`), wrapping/checked
     arithmetic, and comparisons, including width-specialized lemmas for `u8`,
     `u16`, `u32`, `u64`, `u128`, `usize`, `i8`, `i16`, `i32`, `i64`, `i128`,
     and `isize`.
   - `BitVec (8 * sz)` homomorphism theorems (`evalBinOp_ofBitVec_*`,
     `evalBinOpChecked_ofBitVec_*`, `evalUnOp_ofBitVec_*`,
     `evalCastValue_ofBitVec_*`).

6. **Bit Intrinsic Helpers (`BRIEF-1.2` Support, Section 9)**:
   - `ctpopLoop`, `cttzLoop`, `bitreverseLoop`, `ctlzBits`, and `bswapLoop`
     along with width bounds (`ctpopLoop_le`, `cttzLoop_le`, `ctlzBits_le`),
     zero-input `@[simp]` lemmas (`ctpopLoop_zero`, `cttzLoop_zero`,
     `bitreverseLoop_zero`, `ctlzBits_zero`, `bswapLoop_zero`), and closed-form
     byte swap equivalences (`bswapLoop_one`, `bswapLoop_two_eq_swapBytes16`,
     `bswapLoop_four_eq_swapBytes32`, `bswapLoop_eight_eq_swapBytes64`).

7. **32-Bit Symbolic Header Extraction Benchmark (Section 10)**:
   - `evalHeaderExtract32_closed_form` and
     `evalScalarBinOp_headerExtract32_closed_form`: kernel-checked in `< 2000`
     heartbeats (`set_option maxHeartbeats 2000`) for
     `((hdr >>> 16) &&& 0xFF) ||| ((hdr &&& 0xFF) <<< 8)`.

## Verification & Receipt Commands

Run the following commands from the worktree root:

```bash
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"

# 1. Check marker and copyright header formatting
./ci/check_todo.sh

# 2. Fast trusted-base audit
python3 trusted/audit/check_trusted.py --fast

# 3. Single-file check of theory/Anneal/Scalars.lean (zero warnings, zero sorry)
cd examples && anneal-lean-run --mode file --concurrency 2 -- \
  lake env lean ../theory/Anneal/Scalars.lean && cd ..

# 4. Full Anneal library build
cd examples && anneal-lean-run --mode build --concurrency 2 -- \
  lake build Anneal && cd ..
```
