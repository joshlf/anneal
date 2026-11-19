/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars

/-!
# Pure IEEE-754 `binary32` / `binary64` `as` casts: theory

Correctness theory for the trusted float-cast primitives of
`Trusted.Rustc.V2026_06_01.MirSemantics` (`MirSemantics/Scalars.lean`): exact
decoding (`decodeBits`), `roundTiesToEven` rounding of exact rationals
(`roundQuotientTiesToEven`, `roundRatioTiesToEven`), and the three Rust
`as`-cast families `evalFloatToIntSaturating` (`CastKind.floatToInt`),
`evalIntToFloatRoundTiesToEven` (`CastKind.intToFloat`), and
`evalFloatToFloatRoundTiesToEven` (`CastKind.floatToFloat`). Everything operates
on raw `F32Bits := BitVec 32` / `F64Bits := BitVec 64` bit patterns with exact
rational arithmetic: no host `Float`, no `extern`.

The trusted primitives are specialized to `roundTiesToEven`. This module adds
the theory-only, rounding-mode-generic core (`RoundingMode`, `roundQuotient`,
`roundRatioBits`, `convertFloatBits`), so that the `b/585733184`
half-away-from-zero contrast model (`evalIntToFloatHalfAwayFromZero`) can be
stated, together with definitional (`rfl`) bridges back to the trusted
definitions (`roundRatioBits_tiesToEven`, `convertFloatBits_tiesToEven`,
`evalIntToFloatRoundTiesToEven_eq_roundRatioBits`), and a literal
transliteration of Miri's `FloatBits.decode` (`miriDecode`) against which
`decodeBits` is pinned.

Headline results:
- float → int: `evalFloatToIntSaturating_sound`, `evalFloatToIntSaturating_nan`,
  `floatToIntValue_monotone`,
  `evalFloatToIntSaturating_roundtrip_of_intToFloat`;
- rounding core: `roundRatioTiesToEven_correctly_rounded`,
  `roundRatioTiesToEven_float_half_ulp`, `roundRatioTiesToEven_overflow_iff`,
  `roundRatioBits_valid_and_not_nan`,
  `roundRatioBits_sign_and_underflow_zero_preserved`;
- int → float: `evalIntToFloatRoundTiesToEven_sound`,
  `b585733184_ties_to_even_separation`;
- float → float: `evalFloatToFloatRoundTiesToEven_sound`,
  `f32ToF64_exact_and_roundtrip`, `convertFloatBits_nan_quiet`,
  `f64ToF32_signaling_nan_quietized`;
- decoding: `decodeBits_agrees_miriDecode`, `pack_unpack_f32`,
  `pack_unpack_f64`;
- `lean-miri` bridges (§4b): `ratioExponent_eq_miri`, `powScale_eq_miri`,
  `roundQuotientTiesToEven_eq_miri`, `floatToIntValue_eq_miri`,
  `ratioExponent_floor_log2`, `ratioExponent_eq_iff_powScale_bounds`
  (uniqueness of `⌊log₂(n / d)⌋`), `roundRatioTiesToEven_consistent`, the width
  bounds `roundRatioTiesToEven_lt` / `evalIntToFloatRoundTiesToEven_lt` /
  `evalFloatToFloatRoundTiesToEven_lt` / `evalFloatToIntSaturating_bits_lt`,
  `isNaNBits_evalFloatToFloatRoundTiesToEven`, universal NaN-inclusive self and
  widening round-trips (`evalFloatToFloatRoundTiesToEven_self_eq`,
  `evalFloatToFloatRoundTiesToEven_f32_f64_f32_eq_self`), `BitVec 32` / `BitVec 64`
  → `BitVec 128` `setWidth` conversion bridges (`f32ToF64_setWidth128`,
  `f64ToF32_setWidth128`), and two's-complement `BitVec w` / `BitVec 128`
  round-trip bridges (`encodeTwosComplement_eq_toNat_ofInt`,
  `bitVec_ofNat_encodeTwosComplement`, `encodeTwosComplement_bitVec_toInt`,
  `intValueOfBits_signed_bounds`, `bitVec128_ofInt_intValueOfBits_toInt`,
  `bitVec128_ofNat_intValueOfBits_toNat`, `evalFloatToIntSaturating_bitVec_eq`), the
  saturation endpoints `evalFloatToIntSaturating_infBits` (`+∞ ↦ MAX`, `-∞ ↦ MIN`, via
  `encodeTwosComplement_maxValue` / `encodeTwosComplement_minValue`),
  `evalFloatToIntSaturating_zeroBits` (`±0.0 ↦ 0`),
  `evalFloatToIntSaturating_of_ge_maxValue` / `evalFloatToIntSaturating_of_le_minValue`
  (finite truncation saturation), `evalFloatToIntSaturating_of_in_range` (exact in-range
  truncation), `evalFloatToIntSaturating_finite_eq` (complete finite-case trichotomy),
  `evalIntToFloatRoundTiesToEven_zero` (`0 : iN/uN ↦ +0.0`),
  `intValueOfBits_{unsigned_eq_mod,signed_min,signed_neg_one}`, and
  `evalFloatToFloatRoundTiesToEven_{zeroBits,infBits}`.

Every theorem is kernel-checked and depends only on `propext` / `Quot.sound` (no
`Classical.choice`); see the `#guard_msgs in #print axioms` block at the end of
the file.
-/

namespace Anneal.Mir.IeeeFloatCast

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.MirAst

/-! ## §1. Theory-only definitions

The trusted bit-level primitives (`IeeeFormat`, `unpackBits`, `decodeBits`,
`roundRatioTiesToEven`, `evalFloatToIntSaturating`,
`evalIntToFloatRoundTiesToEven`, `evalFloatToFloatRoundTiesToEven`, ...) live in
`Trusted.Rustc.V2026_06_01.MirSemantics`. The definitions below exist only for
the theory. -/

/-- Assemble a bit pattern from sign, biased exponent, and fraction fields. -/
def packBits (f : IeeeFormat) (c : FloatComponents) : Nat :=
  (if c.neg then 2 ^ (f.width - 1) else 0) + c.exponent * 2 ^ f.fractionBits + c.fraction

/-- Unpack an `F32Bits`. -/
def unpackF32 (x : F32Bits) : FloatComponents := unpackBits .binary32 x.toNat
/-- Pack an `F32Bits`. -/
def packF32 (c : FloatComponents) : F32Bits := BitVec.ofNat 32 (packBits .binary32 c)
/-- Unpack an `F64Bits`. -/
def unpackF64 (x : F64Bits) : FloatComponents := unpackBits .binary64 x.toNat
/-- Pack an `F64Bits`. -/
def packF64 (c : FloatComponents) : F64Bits := BitVec.ofNat 64 (packBits .binary64 c)

/-- `Miri.Interpreter.FloatClass`. -/
inductive MiriFloatClass : Type where
  /-- Finite value `numerator / denominator` (zeros have `numerator = 0`). -/
  | finite (numerator denominator : Nat) : MiriFloatClass
  /-- Infinity. -/
  | infinite : MiriFloatClass
  /-- NaN with its full fraction payload. -/
  | nan (payload : Nat) : MiriFloatClass
deriving DecidableEq

/-- `Miri.Interpreter.FloatDecoded`. -/
structure MiriFloatDecoded : Type where
  /-- Sign bit. -/
  negative : Bool
  /-- Magnitude class. -/
  value : MiriFloatClass
deriving DecidableEq

/-- Literal transliteration of `Miri.Interpreter.FloatBits.decode`
(`lean-miri/vendor/Miri/Interpreter/Float.lean:57-69`); `none` is Miri's
`.encodingExceedsWidth` error. -/
def miriDecode (f : IeeeFormat) (bits : Nat) : Option MiriFloatDecoded :=
  if bits ≥ 2 ^ f.width then none
  else
    let negative := bits / 2 ^ (f.width - 1) != 0
    let exponent := (bits / 2 ^ f.fractionBits) % 2 ^ f.exponentBits
    let fraction := bits % 2 ^ f.fractionBits
    if exponent == 2 ^ f.exponentBits - 1 then
      some ⟨negative, if fraction == 0 then .infinite else .nan fraction⟩
    else
      let significand := if exponent == 0 then fraction else 2 ^ f.fractionBits + fraction
      let unbiased : Int :=
        if exponent == 0 then f.minExponent else (exponent : Int) - (f.bias : Int)
      let nd := powScale significand 1 (unbiased - (f.fractionBits : Int))
      some ⟨negative, .finite nd.1 nd.2⟩

/-- Project a `FloatKind` to Miri's decoded representation (zeros become
`.finite 0 den` exactly as Miri decodes them). -/
def floatKindToMiri (f : IeeeFormat) : FloatKind → MiriFloatDecoded
  | .zero neg => ⟨neg, .finite 0 (powScale 0 1 (f.minExponent - (f.fractionBits : Int))).2⟩
  | .finite neg n d => ⟨neg, .finite n d⟩
  | .inf neg => ⟨neg, .infinite⟩
  | .nan neg _ payload => ⟨neg, .nan payload⟩

/-- Rounding direction of the generic integer quotient core. -/
inductive RoundingMode : Type where
  /-- IEEE-754 `roundTiesToEven` (Rust `as`, `rustc_apfloat` default). -/
  | tiesToEven : RoundingMode
  /-- Round half away from zero (`f64::round`; the `b/585733184` bug model). -/
  | halfAwayFromZero : RoundingMode

/-- Nearest integer to `n / d`, ties away from zero (contrast model). -/
def roundQuotientHalfAwayFromZero (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if r * 2 ≥ d then q + 1 else q

/-- Dispatch on `RoundingMode`. -/
def roundQuotient : RoundingMode → Nat → Nat → Nat
  | .tiesToEven => roundQuotientTiesToEven
  | .halfAwayFromZero => roundQuotientHalfAwayFromZero

/-- Correctly rounded encoding of the exact nonnegative rational `n / d` with a
separate sign (transliterates `Miri.Interpreter.FloatBits.roundRatio`,
`lean-miri/vendor/Miri/Interpreter/Float.lean:98-112`, with the rounding
direction abstracted by `mode`). Gradual underflow comes from clamping the
working exponent to `minExponent`; rounding carry-out bumps the exponent;
overflow produces `±∞`. Miri's `throw` branches (zero denominator, inconsistent
rounding) are mapped to the preferred NaN and are unreachable from decoded
inputs. In `.tiesToEven` mode this *is* the trusted `roundRatioTiesToEven`
(`roundRatioBits_tiesToEven`). -/
def roundRatioBits (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (n d : Nat) : Nat :=
  if d = 0 then preferredNaNBits f
  else if n = 0 then zeroBits f neg
  else
    let exponent := max (ratioExponent n d) f.minExponent
    if exponent > f.maxExponent then infBits f neg
    else
      let scaled := powScale n d ((f.fractionBits : Int) - exponent)
      let significand := roundQuotient mode scaled.1 scaled.2
      let carry := decide (2 ^ (f.fractionBits + 1) ≤ significand)
      let significand' := if carry then significand / 2 else significand
      let exponent' := if carry then exponent + 1 else exponent
      if exponent' > f.maxExponent then infBits f neg
      else if significand' < 2 ^ f.fractionBits then
        if exponent' = f.minExponent then encodeBits f neg 0 significand'
        else preferredNaNBits f
      else if 2 ^ (f.fractionBits + 1) ≤ significand' then preferredNaNBits f
      else encodeBits f neg (exponent' + (f.bias : Int)).toNat (significand' - 2 ^ f.fractionBits)

/-- `true` iff `bits` decodes to a NaN. -/
def isNaNBits (f : IeeeFormat) (bits : Nat) : Bool :=
  match decodeBits f bits with
  | .nan _ _ _ => true
  | _ => false

/-- `true` iff `bits` decodes to a quiet NaN. -/
def isQuietNaNBits (f : IeeeFormat) (bits : Nat) : Bool :=
  match decodeBits f bits with
  | .nan _ quiet _ => quiet
  | _ => false

/-- Half-away-from-zero contrast model of the int-to-float cast
(`b/585733184`). -/
def evalIntToFloatHalfAwayFromZero (signed : Bool) (w bits : Nat) (dst : IeeeFormat) : Nat :=
  let v := intValueOfBits signed w bits
  roundRatioBits .halfAwayFromZero dst (decide (v < 0)) v.natAbs 1

/-- Float-to-float conversion (transliterates
`Miri.Interpreter.FloatBits.convert`,
`lean-miri/vendor/Miri/Interpreter/Float.lean:117-128`) with the rounding
direction abstracted by `mode`: finite values are correctly rounded; NaN
payloads are quieted, shifted to the target precision, and get the target quiet
bit forced (pinned `rustc_apfloat` `ieee.rs::convert_r`). In `.tiesToEven` mode
this *is* the trusted `evalFloatToFloatRoundTiesToEven`
(`convertFloatBits_tiesToEven`). -/
def convertFloatBits (mode : RoundingMode) (src dst : IeeeFormat) (bits : Nat) : Nat :=
  match decodeBits src bits with
  | .zero neg => zeroBits dst neg
  | .finite neg n d => roundRatioBits mode dst neg n d
  | .inf neg => infBits dst neg
  | .nan neg _ payload =>
    let quiet := Nat.lor payload (2 ^ (src.fractionBits - 1))
    let payload' :=
      if src.fractionBits ≤ dst.fractionBits then
        quiet * 2 ^ (dst.fractionBits - src.fractionBits)
      else quiet / 2 ^ (src.fractionBits - dst.fractionBits)
    encodeBits dst neg (2 ^ dst.exponentBits - 1) (Nat.lor payload' (2 ^ (dst.fractionBits - 1)))

/-- `x as f64` for `x : f32` (the trusted `evalFloatToFloatRoundTiesToEven`). -/
def f32ToF64 (x : F32Bits) : F64Bits :=
  BitVec.ofNat 64 (evalFloatToFloatRoundTiesToEven .binary32 .binary64 x.toNat)

/-- `x as f32` for `x : f64` (the trusted `evalFloatToFloatRoundTiesToEven`). -/
def f64ToF32 (x : F64Bits) : F32Bits :=
  BitVec.ofNat 32 (evalFloatToFloatRoundTiesToEven .binary64 .binary32 x.toNat)

/-! ## §2. `rfl` bridges to the trusted `roundTiesToEven` primitives

The trusted primitives inline the `.tiesToEven` instance of the generic core:
`roundRatioTiesToEven` is `roundRatioBits .tiesToEven`,
`evalFloatToFloatRoundTiesToEven` is `convertFloatBits .tiesToEven`, and
`evalIntToFloatRoundTiesToEven` rounds the exact source integer with
`roundRatioBits .tiesToEven`. All bridges hold definitionally. -/

/-- The generic quotient core in `.tiesToEven` mode is the trusted
`roundQuotientTiesToEven`. -/
theorem roundQuotient_tiesToEven (n d : Nat) :
    roundQuotient .tiesToEven n d = roundQuotientTiesToEven n d := rfl

/-- The generic rounding core in `.tiesToEven` mode is the trusted
`roundRatioTiesToEven`. -/
theorem roundRatioBits_tiesToEven (f : IeeeFormat) (neg : Bool) (n d : Nat) :
    roundRatioBits .tiesToEven f neg n d = roundRatioTiesToEven f neg n d := rfl

/-- The generic float-to-float conversion in `.tiesToEven` mode is the trusted
`evalFloatToFloatRoundTiesToEven`. -/
theorem convertFloatBits_tiesToEven (src dst : IeeeFormat) (bits : Nat) :
    convertFloatBits .tiesToEven src dst bits = evalFloatToFloatRoundTiesToEven src dst bits :=
  rfl

/-- The trusted int-to-float cast is the generic rounding core in `.tiesToEven`
mode applied to the exact source integer. -/
theorem evalIntToFloatRoundTiesToEven_eq_roundRatioBits (signed : Bool) (w bits : Nat)
    (dst : IeeeFormat) :
    evalIntToFloatRoundTiesToEven signed w bits dst =
      roundRatioBits .tiesToEven dst (decide (intValueOfBits signed w bits < 0))
        (intValueOfBits signed w bits).natAbs 1 := rfl

/-! ## §3. Witnesses: IEEE-754 casts on raw bit patterns -/

section Witnesses

/-- `evalFloatToIntSaturating` on an `f64` bit pattern, as
`(bits, sizeBytes)`. -/
def f2i64 (bits : Nat) (t : FloatIntTarget) (pw : FloatPtrWidth := .bits64) : Nat × Nat :=
  let r := evalFloatToIntSaturating .binary64 bits t pw
  (r.bits, r.sizeBytes)

/-- `evalFloatToIntSaturating` on an `f32` bit pattern. -/
def f2i32 (bits : Nat) (t : FloatIntTarget) (pw : FloatPtrWidth := .bits64) : Nat × Nat :=
  let r := evalFloatToIntSaturating .binary32 bits t pw
  (r.bits, r.sizeBytes)

/-- **Saturating `FloatToInt` canaries**: NaN ↦ 0; ±∞ clamp; finite values
truncate toward zero (positive and negative fractions); exact boundary clamping
for every integer width
(`i8`/`u8`/`i32`/`u32`/`i64`/`u64`/`i128`/`u128`/`isize`/`usize`). -/
theorem evalFloatToIntSaturating_canaries :
    -- NaN, ±∞, ±0
    f2i64 0x7FF8000000000000 (.signed .i32) = (0, 4) ∧
    f2i64 0xFFF8000000000001 (.unsigned .u64) = (0, 8) ∧
    f2i64 0x7FF0000000000000 (.signed .i32) = (0x7FFFFFFF, 4) ∧
    f2i64 0xFFF0000000000000 (.signed .i32) = (0x80000000, 4) ∧
    f2i64 0xFFF0000000000000 (.unsigned .u32) = (0, 4) ∧
    f2i64 0x8000000000000000 (.signed .i64) = (0, 8) ∧
    f2i32 0x7FC00000 (.unsigned .u16) = (0, 2) ∧
    -- truncation toward zero
    f2i64 0x400599999999999A (.signed .i32) = (2, 4) ∧
    f2i64 0xC00599999999999A (.signed .i32) = (0xFFFFFFFE, 4) ∧
    f2i32 0x3FC00000 (.signed .i8) = (1, 1) ∧
    -- u8 / i8 boundaries
    f2i64 0x406FFCCCCCCCCCCD (.unsigned .u8) = (255, 1) ∧
    f2i64 0x4072C00000000000 (.unsigned .u8) = (255, 1) ∧
    f2i64 0xBFF0000000000000 (.unsigned .u8) = (0, 1) ∧
    f2i64 0x405FF9999999999A (.signed .i8) = (127, 1) ∧
    f2i64 0x4060000000000000 (.signed .i8) = (127, 1) ∧
    f2i64 0xC0601CCCCCCCCCCD (.signed .i8) = (0x80, 1) ∧
    f2i64 0xC060200000000000 (.signed .i8) = (0x80, 1) ∧
    -- u16 / i16 boundaries
    f2i64 0x40DFFFC000000000 (.signed .i16) = (32767, 2) ∧
    f2i64 0x40E0000000000000 (.signed .i16) = (32767, 2) ∧
    f2i64 0xC0E0002000000000 (.signed .i16) = (0x8000, 2) ∧
    f2i64 0xC0E0004000000000 (.signed .i16) = (0x8000, 2) ∧
    f2i64 0x40EFFFE000000000 (.unsigned .u16) = (65535, 2) ∧
    f2i64 0x40F0000000000000 (.unsigned .u16) = (65535, 2) ∧
    f2i64 0xBFF0000000000000 (.unsigned .u16) = (0, 2) ∧
    -- i32 / u32 boundaries
    f2i64 0x41DFFFFFFFF9999A (.signed .i32) = (0x7FFFFFFF, 4) ∧
    f2i64 0x41E0000000000000 (.signed .i32) = (0x7FFFFFFF, 4) ∧
    f2i64 0xC1E00000001CCCCD (.signed .i32) = (0x80000000, 4) ∧
    f2i64 0xC1E0000000200000 (.signed .i32) = (0x80000000, 4) ∧
    f2i64 0x41F0000000000000 (.unsigned .u32) = (0xFFFFFFFF, 4) ∧
    -- i64 / u64 boundaries
    f2i64 0x43E0000000000000 (.signed .i64) = (0x7FFFFFFFFFFFFFFF, 8) ∧
    f2i64 0xC3E0000000000000 (.signed .i64) = (0x8000000000000000, 8) ∧
    f2i64 0x43F0000000000000 (.unsigned .u64) = (0xFFFFFFFFFFFFFFFF, 8) ∧
    -- i128 / u128 boundaries (including f32 exact 2^127 and -2^127 boundary)
    f2i64 0x483D6329F1C35CA5 (.signed .i128) = (2 ^ 127 - 1, 16) ∧
    f2i64 0xC83D6329F1C35CA5 (.signed .i128) = (2 ^ 127, 16) ∧
    f2i64 0x483D6329F1C35CA5 (.unsigned .u128) = (2 ^ 128 - 1, 16) ∧
    f2i32 0x7F000000 (.signed .i128) = (2 ^ 127 - 1, 16) ∧
    f2i32 0x7F000000 (.unsigned .u128) = (2 ^ 127, 16) ∧
    f2i32 0xFF000000 (.signed .i128) = (2 ^ 127, 16) ∧
    -- isize / usize on 64- and 32-bit targets
    f2i64 0x43E0000000000000 (.signed .isize) .bits64 = (0x7FFFFFFFFFFFFFFF, 8) ∧
    f2i64 0x43E0000000000000 (.signed .isize) .bits32 = (0x7FFFFFFF, 4) ∧
    f2i64 0xC1E0000000200000 (.signed .isize) .bits32 = (0x80000000, 4) ∧
    f2i64 0x43F0000000000000 (.unsigned .usize) .bits64 = (0xFFFFFFFFFFFFFFFF, 8) ∧
    f2i64 0x41F0000000000000 (.unsigned .usize) .bits32 = (0xFFFFFFFF, 4) ∧
    f2i64 0xBFF0000000000000 (.unsigned .usize) .bits32 = (0, 4) := by
  repeat' apply And.intro
  all_goals decide +kernel

/-- **`b/585733184` (`cl/1021519279`) ties-to-even vs. half-away-from-zero
separation witnesses** on the integer rounding core (`0.5 ↦ 0` vs `1`,
`-0.5 ↦ -0` vs `-1`, `2.5 ↦ 2` vs `3`, `3.5 ↦ 4`) and on full int-to-float
casts. -/
theorem b585733184_ties_to_even_separation :
    -- 0.5, -0.5 (sign carried separately: magnitude 0 is -0), 2.5, 3.5
    (roundQuotientTiesToEven 1 2, roundQuotientHalfAwayFromZero 1 2) = (0, 1) ∧
    ((true, roundQuotientTiesToEven 1 2), (true, roundQuotientHalfAwayFromZero 1 2)) =
      ((true, 0), (true, 1)) ∧
    (roundQuotientTiesToEven 5 2, roundQuotientHalfAwayFromZero 5 2) = (2, 3) ∧
    (roundQuotientTiesToEven 7 2, roundQuotientHalfAwayFromZero 7 2) = (4, 4) ∧
    -- 2^24 + 1 : u32 -> f32
    evalIntToFloatRoundTiesToEven false 32 16777217 .binary32 = 0x4B800000 ∧
    evalIntToFloatHalfAwayFromZero false 32 16777217 .binary32 = 0x4B800001 ∧
    -- 2^24 + 3 : u32 -> f32
    evalIntToFloatRoundTiesToEven false 32 16777219 .binary32 = 0x4B800002 ∧
    evalIntToFloatHalfAwayFromZero false 32 16777219 .binary32 = 0x4B800002 ∧
    -- -(2^24 + 1) : i32 -> f32
    evalIntToFloatRoundTiesToEven true 32 (2 ^ 32 - 16777217) .binary32 = 0xCB800000 ∧
    evalIntToFloatHalfAwayFromZero true 32 (2 ^ 32 - 16777217) .binary32 = 0xCB800001 ∧
    -- 2^53 + 1 : u64 -> f64
    evalIntToFloatRoundTiesToEven false 64 9007199254740993 .binary64 = 0x4340000000000000 ∧
    evalIntToFloatHalfAwayFromZero false 64 9007199254740993 .binary64 = 0x4340000000000001 := by
  repeat' apply And.intro
  all_goals decide +kernel

/-- Int-to-float canaries: signed zero, `±1`, `i32::MIN`, `u32::MAX`,
`i64::MAX`, `u64::MAX`, and the exact `u128 -> f32` overflow threshold
`2^128 - 2^103` (ties to the even "significand" `2^24`, i.e. `+∞`), with
`u128::MAX ↦ +∞`. -/
theorem evalIntToFloatRoundTiesToEven_canaries :
    evalIntToFloatRoundTiesToEven true 32 0 .binary32 = 0 ∧
    evalIntToFloatRoundTiesToEven true 32 1 .binary32 = 0x3F800000 ∧
    evalIntToFloatRoundTiesToEven true 32 0xFFFFFFFF .binary32 = 0xBF800000 ∧
    evalIntToFloatRoundTiesToEven true 32 0x80000000 .binary32 = 0xCF000000 ∧
    evalIntToFloatRoundTiesToEven true 32 0x7FFFFFFF .binary32 = 0x4F000000 ∧
    evalIntToFloatRoundTiesToEven false 32 0xFFFFFFFF .binary32 = 0x4F800000 ∧
    evalIntToFloatRoundTiesToEven false 32 0xFFFFFFFF .binary64 = 0x41EFFFFFFFE00000 ∧
    evalIntToFloatRoundTiesToEven true 64 0x7FFFFFFFFFFFFFFF .binary64 = 0x43E0000000000000 ∧
    evalIntToFloatRoundTiesToEven false 64 0xFFFFFFFFFFFFFFFF .binary64 = 0x43F0000000000000 ∧
    evalIntToFloatRoundTiesToEven false 128 (2 ^ 128 - 1) .binary32 = 0x7F800000 ∧
    evalIntToFloatRoundTiesToEven false 128 (2 ^ 128 - 2 ^ 103) .binary32 = 0x7F800000 ∧
    evalIntToFloatRoundTiesToEven false 128 (2 ^ 128 - 2 ^ 103 - 1) .binary32 = 0x7F7FFFFF := by
  repeat' apply And.intro
  all_goals decide +kernel

/-- **Signaling-NaN quietization negative canary**: `f64 -> f32` of the
signaling NaN `0x7FF0_0000_0000_0001` is the quiet NaN `0x7FC0_0000`, never `+∞`
(`0x7F80_0000`). -/
theorem f64ToF32_signaling_nan_quietized :
    f64ToF32 0x7FF0000000000001#64 = 0x7FC00000#32 ∧
    f64ToF32 0x7FF0000000000001#64 ≠ 0x7F800000#32 ∧
    isQuietNaNBits .binary32 (f64ToF32 0x7FF0000000000001#64).toNat = true := by
  repeat' apply And.intro
  all_goals decide +kernel

/-- Float-to-float canaries: NaN payload propagation (both directions), signed
zeros, subnormals (gradual underflow and ties at the subnormal boundary),
overflow to `+∞` at the exact tie `2^128 - 2^103`, and ties-to-even in the
normal range. -/
theorem evalFloatToFloatRoundTiesToEven_canaries :
    -- NaN propagation
    f64ToF32 0x7FF8000000000123#64 = 0x7FC00000#32 ∧
    f64ToF32 0xFFF8000000000000#64 = 0xFFC00000#32 ∧
    f32ToF64 0x7F800001#32 = 0x7FF8000020000000#64 ∧
    f32ToF64 0x7FC00000#32 = 0x7FF8000000000000#64 ∧
    -- signed zeros
    f64ToF32 0x8000000000000000#64 = 0x80000000#32 ∧
    f32ToF64 0x80000000#32 = 0x8000000000000000#64 ∧
    -- exact widening of extremes
    f32ToF64 0x00000001#32 = 0x36A0000000000000#64 ∧
    f32ToF64 0x7F7FFFFF#32 = 0x47EFFFFFE0000000#64 ∧
    f32ToF64 0x3FC00000#32 = 0x3FF8000000000000#64 ∧
    -- underflow / gradual underflow
    f64ToF32 0x358DEE7A4AD4B81F#64 = 0x00000000#32 ∧
    f64ToF32 0xB58DEE7A4AD4B81F#64 = 0x80000000#32 ∧
    f64ToF32 0x3690000000000000#64 = 0x00000000#32 ∧
    f64ToF32 0x3690000000000001#64 = 0x00000001#32 ∧
    f64ToF32 0x36A8000000000000#64 = 0x00000002#32 ∧
    -- overflow
    f64ToF32 0x47EFFFFFF0000000#64 = 0x7F800000#32 ∧
    f64ToF32 0x47EFFFFFEFFFFFFF#64 = 0x7F7FFFFF#32 ∧
    f64ToF32 0x48078287F49C4A1D#64 = 0x7F800000#32 ∧
    f64ToF32 0x7FF0000000000000#64 = 0x7F800000#32 ∧
    -- ties to even in the normal range
    f64ToF32 0x3FF0000010000000#64 = 0x3F800000#32 ∧
    f64ToF32 0x3FF0000030000000#64 = 0x3F800002#32 ∧
    f64ToF32 0x3FD5555555555555#64 = 0x3EAAAAAB#32 := by
  repeat' apply And.intro
  all_goals decide +kernel

/-- **Subnormal single-rounding (no double rounding) & carry-out canaries**:
1. At `e = -127` (`f32.minExponent - 1`), `0x3800_0000_5FFF_FFFF : f64`
   (`(2^22 + 1.5 - 2^-30) * 2^-149`) rounds in one step to the subnormal
   `0x0040_0001 : f32` (`(2^22 + 1) * 2^-149`), whereas first rounding the
   53-bit significand to 24 bits
   (`roundQuotientTiesToEven (2^52 + 2^30 + 2^29 - 1) (2^29) = 2^23 + 3`) and
   then shifting into the subnormal slot
   (`roundQuotientTiesToEven (2^23 + 3) 2 = 2^22 + 2`, a tie broken to even)
   would double-round to `0x0040_0002`;
2. subnormal-to-normal carry-out: `0x380F_FFFF_DFFF_FFFF` rounds to the greatest
   `f32` subnormal `0x007F_FFFF`, while `0x380F_FFFF_E000_0000`
   (`2^-126 - 2^-150`, an exact tie) carries into the minimum normal
   `0x0080_0000` (`2^-126`);
3. `u64 -> f32` single rounding vs `u64 -> f64 -> f32` double rounding on
   `0x0040_0000_BFFF_FFFF = 2^54 + 3 * 2^30 - 1`: the direct cast yields
   `0x5A80_0001`, whereas routing through `f64` (`2^54 + 3 * 2^30`)
   double-rounds to `0x5A80_0002`. -/
theorem f64ToF32_subnormal_and_double_rounding_canaries :
    f64ToF32 0x380000005FFFFFFF#64 = 0x00400001#32 ∧
    roundQuotientTiesToEven
        (roundQuotientTiesToEven (2 ^ 52 + 2 ^ 30 + 2 ^ 29 - 1) (2 ^ 29)) 2 =
      0x00400002 ∧
    f64ToF32 0x380FFFFFDFFFFFFF#64 = 0x007FFFFF#32 ∧
    f64ToF32 0x380FFFFFE0000000#64 = 0x00800000#32 ∧
    evalIntToFloatRoundTiesToEven false 64 0x400000BFFFFFFF .binary32 = 0x5A800001 ∧
    evalFloatToFloatRoundTiesToEven .binary64 .binary32
        (evalIntToFloatRoundTiesToEven false 64 0x400000BFFFFFFF .binary64) =
      0x5A800002 := by
  repeat' apply And.intro
  all_goals decide +kernel

end Witnesses

/-! ## §4. Universal theorems -/

section Theorems

theorem if_pos' {c : Prop} [Decidable c] (h : c) {α : Sort _} (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem if_neg' {c : Prop} [Decidable c] (h : ¬c) {α : Sort _} (a b : α) :
    (if c then a else b) = b := by simp [h]

/-! ### Constructive arithmetic helpers

In Lean `v4.34.1`, core's `Nat.pow_lt_pow_right`, `Nat.pow_lt_pow_iff_right`,
`Nat.mul_lt_mul_left`, `Nat.mul_lt_mul_right`, `Nat.div_lt_of_lt_mul`, and
`Nat.log2_two_pow` transitively depend on `Classical.choice`. The replacements
below depend on at most `propext`/`Quot.sound`. Likewise `omega` discharges a
negated conjunction `¬(A ∧ B)` (from a conjunction or iff goal, or such a
hypothesis) through `Classical.propDecidable`, so every `omega` call in this
file is fed atomic goals. -/

theorem two_pow_le_two_pow {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

theorem two_pow_lt_two_pow {a b : Nat} (h : a < b) : 2 ^ a < 2 ^ b := by
  have h1 : 2 ^ (a + 1) ≤ 2 ^ b := two_pow_le_two_pow h
  rw [Nat.pow_succ] at h1
  have := Nat.two_pow_pos a
  omega

theorem lt_of_two_pow_lt {a b : Nat} (h : 2 ^ a < 2 ^ b) : a < b := by
  cases Nat.lt_or_ge a b with
  | inl h' => exact h'
  | inr h' => have := two_pow_le_two_pow h'; omega

theorem nat_mul_lt_mul_right_iff {a b c : Nat} (hc : 0 < c) : a * c < b * c ↔ a < b :=
  ⟨fun h => by
    cases Nat.lt_or_ge a b with
    | inl h' => exact h'
    | inr h' => have := Nat.mul_le_mul_right c h'; omega,
   fun h => Nat.mul_lt_mul_of_pos_right h hc⟩

/-- `Nat.beq a b` is `decide (a = b)`; normalizes the sign and quiet bits of
unpacked fields so that `omega` can reason about them. -/
theorem nat_beq_eq_decide (a b : Nat) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · have : a ≠ b := fun he => by rw [he, Nat.beq_refl] at h; exact Bool.noConfusion h
    simp [this]
  · simp [Nat.eq_of_beq_eq_true h]

theorem nat_div_lt_of_lt_mul {m n k : Nat} (h : m < n * k) : m / n < k := by
  have hn : 0 < n := by
    cases n with
    | zero => rw [Nat.zero_mul] at h; exact absurd h (Nat.not_lt_zero m)
    | succ n => exact Nat.succ_pos n
  exact (Nat.div_lt_iff_lt_mul hn).mpr (by rw [Nat.mul_comm]; exact h)

/-! ### Bit-field packing -/

theorem unpackBits_encodeBits (f : IeeeFormat) (neg : Bool) (E F : Nat)
    (hE : E < 2 ^ f.exponentBits) (hF : F < 2 ^ f.fractionBits) :
    unpackBits f (encodeBits f neg E F) = ⟨neg, E, F⟩ := by
  cases f <;>
  · simp only [IeeeFormat.exponentBits, IeeeFormat.fractionBits, Nat.reducePow] at hE hF
    simp only [unpackBits, encodeBits, zeroBits, IeeeFormat.width, IeeeFormat.fractionBits,
      IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub, FloatComponents.mk.injEq,
      nat_beq_eq_decide]
    cases neg <;> simp <;> (repeat' apply And.intro) <;> omega

theorem encodeBits_lt (f : IeeeFormat) (neg : Bool) (E F : Nat)
    (hE : E < 2 ^ f.exponentBits) (hF : F < 2 ^ f.fractionBits) :
    encodeBits f neg E F < 2 ^ f.width := by
  cases f <;>
  · simp only [IeeeFormat.exponentBits, IeeeFormat.fractionBits, Nat.reducePow] at hE hF
    simp only [encodeBits, zeroBits, IeeeFormat.width, IeeeFormat.fractionBits, Nat.reducePow,
      Nat.reduceSub]
    cases neg <;> simp <;> (repeat' apply And.intro) <;> omega

/-- `pack ∘ unpack = id` on every `F32Bits`. -/
theorem pack_unpack_f32 (x : F32Bits) : packF32 (unpackF32 x) = x := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [packF32, unpackF32, packBits, unpackBits, BitVec.toNat_ofNat, IeeeFormat.width,
    IeeeFormat.fractionBits, IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub,
    nat_beq_eq_decide] at hx ⊢
  generalize x.toNat = n at hx ⊢
  by_cases h : n / 2147483648 % 2 = 1
  · simp only [h, decide_true, ite_true]; omega
  · simp only [h, decide_false, ite_false, Bool.false_eq_true]; omega

/-- `pack ∘ unpack = id` on every `F64Bits`. -/
theorem pack_unpack_f64 (x : F64Bits) : packF64 (unpackF64 x) = x := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [packF64, unpackF64, packBits, unpackBits, BitVec.toNat_ofNat, IeeeFormat.width,
    IeeeFormat.fractionBits, IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub,
    nat_beq_eq_decide] at hx ⊢
  generalize x.toNat = n at hx ⊢
  by_cases h : n / 9223372036854775808 % 2 = 1
  · simp only [h, decide_true, ite_true]; omega
  · simp only [h, decide_false, ite_false, Bool.false_eq_true]; omega

/-- `unpack ∘ pack = id` on well-formed `binary32` fields. -/
theorem unpack_pack_f32 (c : FloatComponents) (he : c.exponent < 2 ^ 8)
    (hf : c.fraction < 2 ^ 23) :
    unpackF32 (packF32 c) = c := by
  obtain ⟨neg, e, fr⟩ := c
  simp only [Nat.reducePow] at he hf
  simp only [packF32, unpackF32, packBits, unpackBits, BitVec.toNat_ofNat, IeeeFormat.width,
    IeeeFormat.fractionBits, IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub,
    FloatComponents.mk.injEq, nat_beq_eq_decide]
  cases neg <;> simp <;> (repeat' apply And.intro) <;> omega

/-- `unpack ∘ pack = id` on well-formed `binary64` fields. -/
theorem unpack_pack_f64 (c : FloatComponents) (he : c.exponent < 2 ^ 11)
    (hf : c.fraction < 2 ^ 52) :
    unpackF64 (packF64 c) = c := by
  obtain ⟨neg, e, fr⟩ := c
  simp only [Nat.reducePow] at he hf
  simp only [packF64, unpackF64, packBits, unpackBits, BitVec.toNat_ofNat, IeeeFormat.width,
    IeeeFormat.fractionBits, IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub,
    FloatComponents.mk.injEq, nat_beq_eq_decide]
  cases neg <;> simp <;> (repeat' apply And.intro) <;> omega

/-! ### Decoding agrees with Miri -/

theorem powScale_zero_fst (d : Nat) (e : Int) : (powScale 0 d e).1 = 0 := by
  cases e <;> simp [powScale]

/-- `Nat`'s `==` is `decide (· = ·)` by definition (`instBEqOfDecidableEq`);
unlike `BEq.rfl`, this rewrite is axiom-free. -/
theorem nat_beq_op_eq_decide (a b : Nat) : (a == b) = decide (a = b) := rfl

/-- `decodeBits` agrees with the literal transliteration of
`Miri.Interpreter.FloatBits.decode` on every in-width bit pattern. -/
theorem decodeBits_agrees_miriDecode (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    miriDecode f bits = some (floatKindToMiri f (decodeBits f bits)) := by
  have hnot : ¬ (bits ≥ 2 ^ f.width) := by omega
  unfold miriDecode
  simp only [hnot, ↓reduceIte]
  have hneg : (bits / 2 ^ (f.width - 1) != 0) = Nat.beq ((bits / 2 ^ (f.width - 1)) % 2) 1 := by
    have h2 : bits / 2 ^ (f.width - 1) < 2 := by
      cases f <;> simp only [IeeeFormat.width, Nat.reducePow, Nat.reduceSub] at h ⊢ <;> omega
    rw [nat_beq_eq_decide]
    generalize bits / 2 ^ (f.width - 1) = q at h2
    have : q = 0 ∨ q = 1 := by omega
    rcases this with rfl | rfl <;> rfl
  simp only [decodeBits, unpackBits, hneg]
  generalize Nat.beq ((bits / 2 ^ (f.width - 1)) % 2) 1 = neg
  by_cases hE : (bits / 2 ^ f.fractionBits) % 2 ^ f.exponentBits = 2 ^ f.exponentBits - 1
  · by_cases hF : bits % 2 ^ f.fractionBits = 0
    · simp only [hE, nat_beq_op_eq_decide, decide_true, ↓reduceIte, hF, floatKindToMiri]
    · simp only [hE, nat_beq_op_eq_decide, Bool.false_eq_true, decide_true, decide_false,
        ↓reduceIte, hF, floatKindToMiri]
  · by_cases hZ : (bits / 2 ^ f.fractionBits) % 2 ^ f.exponentBits = 0
    · have h0 : ¬ ((0 : Nat) = 2 ^ f.exponentBits - 1) := by cases f <;> decide
      by_cases hF : bits % 2 ^ f.fractionBits = 0
      · simp only [hZ, nat_beq_op_eq_decide, Bool.false_eq_true, h0, decide_true, decide_false,
          ↓reduceIte, hF, powScale_zero_fst, floatKindToMiri]
      · simp only [hZ, nat_beq_op_eq_decide, Bool.false_eq_true, h0, decide_true, decide_false,
          ↓reduceIte, hF, floatKindToMiri]
    · simp only [nat_beq_op_eq_decide, Bool.false_eq_true, hE, decide_false, ↓reduceIte, hZ,
        Int.natCast_emod, Int.natCast_ediv, Int.natCast_pow, Int.cast_ofNat_Int, floatKindToMiri]

/-! ### Float → int soundness -/

theorem floatToIntValue_mem (k : FloatKind) (lo hi : Int) (h0 : lo ≤ 0) (h1 : 0 ≤ hi) :
    lo ≤ floatToIntValue k lo hi ∧ floatToIntValue k lo hi ≤ hi := by
  cases k with
  | nan => simp only [floatToIntValue]; exact ⟨by omega, by omega⟩
  | inf neg =>
    cases neg <;> simp only [floatToIntValue, Bool.false_eq_true, ite_false, ite_true] <;>
      exact ⟨by omega, by omega⟩
  | zero => simp only [floatToIntValue]; exact ⟨by omega, by omega⟩
  | finite neg n d => simp only [floatToIntValue, clampInt]; exact ⟨by omega, by omega⟩

theorem twos_roundtrip (signed : Bool) (w : Nat)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128) (v : Int)
    (hlo : (if signed = true then -((2 ^ (w - 1) : Nat) : Int) else 0) ≤ v)
    (hhi : v ≤
      (if signed = true then ((2 ^ (w - 1) : Nat) : Int) - 1 else ((2 ^ w : Nat) : Int) - 1)) :
    intValueOfBits signed w (encodeTwosComplement w v) = v ∧ encodeTwosComplement w v < 2 ^ w := by
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> cases signed <;>
    simp only [intValueOfBits, encodeTwosComplement, Nat.reducePow, Nat.reduceSub,
      Bool.false_eq_true, ite_false, ite_true, true_and, false_and] at hlo hhi ⊢ <;>
    (repeat' apply And.intro) <;> omega

theorem FloatIntTarget.bitWidth_cases (t : FloatIntTarget) (pw : FloatPtrWidth) :
    t.bitWidth pw = 8 ∨ t.bitWidth pw = 16 ∨ t.bitWidth pw = 32 ∨ t.bitWidth pw = 64 ∨
      t.bitWidth pw = 128 := by
  cases t <;> rename_i w <;> cases w <;> cases pw <;>
    simp [FloatIntTarget.bitWidth, IntTy.bitWidth, UintTy.bitWidth, FloatPtrWidth.bits]

theorem scalarModulus_div8 (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128) :
    scalarModulus (w / 8) = 2 ^ w ∧ w / 8 * 8 = w := by
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide +kernel, rfl⟩

/-- **`evalFloatToIntSaturating_sound`**: the result is a canonical
two's-complement `ScalarInt` of the target width whose integer value is exactly
the saturating, truncating Rust `as` result `floatToIntValue` (NaN ↦ 0, ±∞ ↦
max/min, finite ↦ `clamp (trunc x)`), and lies in `[min, max]`. -/
theorem evalFloatToIntSaturating_sound (src : IeeeFormat) (bits : Nat) (t : FloatIntTarget)
    (pw : FloatPtrWidth) :
    (evalFloatToIntSaturating src bits t pw).sizeBytes * 8 = t.bitWidth pw ∧
    (evalFloatToIntSaturating src bits t pw).bits <
      scalarModulus (evalFloatToIntSaturating src bits t pw).sizeBytes ∧
    intValueOfBits t.isSigned (t.bitWidth pw) (evalFloatToIntSaturating src bits t pw).bits =
      floatToIntValue (decodeBits src bits) (t.minValue pw) (t.maxValue pw) ∧
    t.minValue pw ≤
      intValueOfBits t.isSigned (t.bitWidth pw) (evalFloatToIntSaturating src bits t pw).bits ∧
    intValueOfBits t.isSigned (t.bitWidth pw) (evalFloatToIntSaturating src bits t pw).bits ≤
      t.maxValue pw := by
  have hw := FloatIntTarget.bitWidth_cases t pw
  obtain ⟨hmod, hdiv⟩ := scalarModulus_div8 _ hw
  have hpos : 1 ≤ t.bitWidth pw := by rcases hw with h | h | h | h | h <;> omega
  have hp1 : 1 ≤ 2 ^ (t.bitWidth pw - 1) := Nat.one_le_two_pow
  have hp2 : 1 ≤ 2 ^ t.bitWidth pw := Nat.one_le_two_pow
  have h0 : t.minValue pw ≤ 0 := by
    unfold FloatIntTarget.minValue; split <;> omega
  have h1 : 0 ≤ t.maxValue pw := by
    unfold FloatIntTarget.maxValue; split <;> omega
  obtain ⟨hlo, hhi⟩ := floatToIntValue_mem (decodeBits src bits) _ _ h0 h1
  have hrt := twos_roundtrip t.isSigned (t.bitWidth pw) hw
    (floatToIntValue (decodeBits src bits) (t.minValue pw) (t.maxValue pw))
    (by unfold FloatIntTarget.minValue at hlo; exact hlo)
    (by unfold FloatIntTarget.maxValue at hhi; exact hhi)
  simp only [evalFloatToIntSaturating]
  refine ⟨hdiv, ?_, hrt.1, ?_, ?_⟩
  · rw [hmod]; exact hrt.2
  · rw [hrt.1]; exact hlo
  · rw [hrt.1]; exact hhi

/-- NaN inputs produce `0`. -/
theorem evalFloatToIntSaturating_nan (src : IeeeFormat) (bits : Nat) (t : FloatIntTarget)
    (pw : FloatPtrWidth) (h : isNaNBits src bits = true) :
    (evalFloatToIntSaturating src bits t pw).bits = 0 := by
  simp only [isNaNBits] at h
  simp only [evalFloatToIntSaturating, encodeTwosComplement]
  split at h <;> simp_all [floatToIntValue]

/-! ### Rounding core -/

/-- **`<= 0.5` ULP**: the ties-to-even quotient is within half a unit of the
exact quotient. -/
theorem roundQuotientTiesToEven_half_ulp (n d : Nat) (hd : 0 < d) :
    2 * (((roundQuotientTiesToEven n d * d : Nat) : Int) - (n : Int)).natAbs ≤ d := by
  have hdm := Nat.div_add_mod n d
  have hr := Nat.mod_lt n hd
  unfold roundQuotientTiesToEven
  simp only
  split
  · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d) d]
    generalize d * (n / d) = D at hdm ⊢
    omega
  · rw [Nat.mul_comm (n / d) d]
    generalize d * (n / d) = D at hdm ⊢
    omega

/-- **Even-LSB tie-breaking**: at an exact tie, the ties-to-even quotient is
even. -/
theorem roundQuotientTiesToEven_tie_even (n d : Nat) (hd : 0 < d)
    (htie : 2 * (((roundQuotientTiesToEven n d * d : Nat) : Int) - (n : Int)).natAbs = d) :
    roundQuotientTiesToEven n d % 2 = 0 := by
  have hdm := Nat.div_add_mod n d
  have hr := Nat.mod_lt n hd
  unfold roundQuotientTiesToEven at htie ⊢
  simp only at htie ⊢
  split at htie <;> rename_i hc <;> simp only [hc, ite_true, ite_false] at ⊢
  · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d) d] at htie
    generalize d * (n / d) = D at hdm htie
    omega
  · rw [Nat.mul_comm (n / d) d] at htie
    by_cases hE : n % d * 2 = d
    · cases Nat.mod_two_eq_zero_or_one (n / d) with
      | inl h' => exact h'
      | inr h' => exact absurd (Or.inr ⟨hE, h'⟩) hc
    · clear hc
      generalize d * (n / d) = D at hdm htie
      omega

/-! ### Exactness machinery for `roundRatioBits` -/

theorem nat_log2_eq_of_bounds (m L : Nat) (h1 : 2 ^ L ≤ m) (h2 : m < 2 ^ (L + 1)) :
    Nat.log2 m = L := by
  have hm : m ≠ 0 := by have := Nat.one_le_two_pow (n := L); omega
  have ha : L ≤ Nat.log2 m := (Nat.le_log2 hm).mpr h1
  have hb : Nat.log2 m < L + 1 := (Nat.log2_lt hm).mpr h2
  omega

theorem nat_log2_two_pow (L : Nat) : Nat.log2 (2 ^ L) = L :=
  nat_log2_eq_of_bounds (2 ^ L) L (Nat.le_refl _) (two_pow_lt_two_pow (Nat.lt_succ_self L))

theorem pow_mul_pow (a b : Nat) : 2 ^ a * 2 ^ b = 2 ^ (a + b) := (Nat.pow_add 2 a b).symm

/-- `ratioExponent (S * 2^k) 1 = log2 S + k`. -/
theorem ratioExponent_mul_pow (S k : Nat) (hS : 0 < S) :
    ratioExponent (S * 2 ^ k) 1 = ((Nat.log2 S + k : Nat) : Int) := by
  have hL1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hS)
  have hL2 := Nat.lt_log2_self (n := S)
  have hk := Nat.one_le_two_pow (n := k)
  unfold ratioExponent
  have h1 : 1 ≤ S * 2 ^ k := Nat.mul_le_mul hS hk
  rw [if_pos' h1, Nat.div_one]
  congr 1
  apply nat_log2_eq_of_bounds
  · rw [← pow_mul_pow]; exact Nat.mul_le_mul_right _ hL1
  · rw [show Nat.log2 S + k + 1 = (Nat.log2 S + 1) + k by omega, ← pow_mul_pow]
    exact Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos k)

/-- `ratioExponent S (2^j) = log2 S - j`. -/
theorem ratioExponent_div_pow (S j : Nat) (hS : 0 < S) :
    ratioExponent S (2 ^ j) = (Nat.log2 S : Int) - (j : Int) := by
  have hL1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hS)
  have hL2 := Nat.lt_log2_self (n := S)
  generalize hL : Nat.log2 S = L at hL1 hL2
  unfold ratioExponent
  by_cases hc : 2 ^ j ≤ S
  · rw [if_pos' hc]
    have hjL : j ≤ L := by
      have : 2 ^ j < 2 ^ (L + 1) := Nat.lt_of_le_of_lt hc hL2
      have := lt_of_two_pow_lt this
      omega
    have hlog : Nat.log2 (S / 2 ^ j) = L - j := by
      apply nat_log2_eq_of_bounds
      · rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos j), pow_mul_pow, Nat.sub_add_cancel hjL]
        exact hL1
      · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos j), pow_mul_pow,
          show L - j + 1 + j = L + 1 by omega]
        exact hL2
    rw [hlog]; omega
  · rw [if_neg' hc]
    have hLj : L < j := by
      have : 2 ^ L < 2 ^ j := Nat.lt_of_le_of_lt hL1 (Nat.lt_of_not_le hc)
      exact lt_of_two_pow_lt this
    by_cases hp : S = 2 ^ L
    · subst hp
      have hdiv : 2 ^ j / 2 ^ L = 2 ^ (j - L) := Nat.pow_div (Nat.le_of_lt hLj) (by decide)
      simp only [hdiv, nat_log2_two_pow]
      have : 2 ^ j ≤ 2 ^ L * 2 ^ (j - L) := by
        rw [pow_mul_pow, Nat.add_sub_cancel' (Nat.le_of_lt hLj)]; exact Nat.le_refl _
      rw [if_pos' this]; omega
    · have hgt : 2 ^ L < S := Nat.lt_of_le_of_ne hL1 (Ne.symm hp)
      have hlog : Nat.log2 (2 ^ j / S) = j - L - 1 := by
        apply nat_log2_eq_of_bounds
        · rw [Nat.le_div_iff_mul_le hS]
          have : 2 ^ (j - L - 1) * S < 2 ^ (j - L - 1) * 2 ^ (L + 1) :=
            Nat.mul_lt_mul_of_pos_left hL2 (Nat.two_pow_pos _)
          rw [pow_mul_pow, show j - L - 1 + (L + 1) = j by omega] at this
          exact Nat.le_of_lt this
        · rw [Nat.div_lt_iff_lt_mul hS, show j - L - 1 + 1 = j - L by omega]
          have : 2 ^ (j - L) * 2 ^ L < 2 ^ (j - L) * S :=
            Nat.mul_lt_mul_of_pos_left hgt (Nat.two_pow_pos _)
          rw [pow_mul_pow, show j - L + L = j by omega] at this
          exact this
      rw [hlog]
      have hnot : ¬ (2 ^ j ≤ S * 2 ^ (j - L - 1)) := by
        have : S * 2 ^ (j - L - 1) < 2 ^ (L + 1) * 2 ^ (j - L - 1) :=
          Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
        rw [pow_mul_pow, show L + 1 + (j - L - 1) = j by omega] at this
        omega
      rw [if_neg' hnot]; omega

/-- Scale invariance of `ratioExponent`. -/
theorem ratioExponent_mul (n d c : Nat) (hc : 0 < c) :
    ratioExponent (n * c) (d * c) = ratioExponent n d := by
  unfold ratioExponent
  have e1 : (d * c ≤ n * c) ↔ d ≤ n := Nat.mul_le_mul_right_iff hc
  have e2 : n * c / (d * c) = n / d := Nat.mul_div_mul_right n d hc
  have e3 : d * c / (n * c) = d / n := Nat.mul_div_mul_right d n hc
  have e4 : ∀ k, (d * c ≤ n * c * 2 ^ k) ↔ d ≤ n * 2 ^ k := fun k => by
    rw [Nat.mul_right_comm n c]; exact Nat.mul_le_mul_right_iff hc
  by_cases h : d ≤ n
  · rw [if_pos' (e1.mpr h), if_pos' h, e2]
  · rw [if_neg' (fun h' => h (e1.mp h')), if_neg' h, e3]
    by_cases h' : d ≤ n * 2 ^ (d / n).log2
    · rw [if_pos' ((e4 _).mpr h'), if_pos' h']
    · rw [if_neg' (fun h'' => h' ((e4 _).mp h'')), if_neg' h']

/-- Scale invariance of `powScale`. -/
theorem powScale_mul (n d c : Nat) (e : Int) :
    powScale (n * c) (d * c) e = ((powScale n d e).1 * c, (powScale n d e).2 * c) := by
  cases e <;> simp [powScale, Nat.mul_right_comm]

/-- Scale invariance of the rounding core. -/
theorem roundQuotient_mul (mode : RoundingMode) (a b c : Nat) (hc : 0 < c) :
    roundQuotient mode (a * c) (b * c) = roundQuotient mode a b := by
  have hq : a * c / (b * c) = a / b := Nat.mul_div_mul_right a b hc
  have hr : a * c % (b * c) = a % b * c := Nat.mul_mod_mul_right c a b
  have g1 : (a % b * c * 2 > b * c) ↔ (a % b * 2 > b) := by
    rw [Nat.mul_right_comm]; exact nat_mul_lt_mul_right_iff hc
  have g2 : (a % b * c * 2 = b * c) ↔ (a % b * 2 = b) := by
    rw [Nat.mul_right_comm]; exact Nat.mul_right_cancel_iff hc
  have g3 : (a % b * c * 2 ≥ b * c) ↔ (a % b * 2 ≥ b) := by
    rw [Nat.mul_right_comm]; exact Nat.mul_le_mul_right_iff hc
  cases mode <;>
    simp only [roundQuotient, roundQuotientTiesToEven, roundQuotientHalfAwayFromZero, hq, hr, g1,
      g2, g3]

/-- Exact quotients are returned unchanged. -/
theorem roundQuotient_exact (mode : RoundingMode) (S c : Nat) (hc : 0 < c) :
    roundQuotient mode (S * c) c = S := by
  have hq : S * c / c = S := Nat.mul_div_cancel S hc
  have hr : S * c % c = 0 := Nat.mul_mod_left S c
  cases mode <;>
    simp only [roundQuotient, roundQuotientTiesToEven, roundQuotientHalfAwayFromZero, hq, hr] <;>
    simp only [Nat.zero_mul] <;> split <;> omega

/-- **Scale invariance of `roundRatioBits`**. -/
theorem roundRatioBits_mul (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (n d c : Nat)
    (hc : 0 < c) : roundRatioBits mode f neg (n * c) (d * c) = roundRatioBits mode f neg n d := by
  have hd : (d * c = 0) ↔ d = 0 := by
    constructor
    · intro h; rcases Nat.mul_eq_zero.mp h with h | h <;> omega
    · intro h; simp [h]
  have hn : (n * c = 0) ↔ n = 0 := by
    constructor
    · intro h; rcases Nat.mul_eq_zero.mp h with h | h <;> omega
    · intro h; simp [h]
  unfold roundRatioBits
  simp only [hd, hn, ratioExponent_mul n d c hc, powScale_mul, roundQuotient_mul mode _ _ c hc]

/-- **Rational congruence of `roundRatioBits`**: equal rationals round
identically. -/
theorem roundRatioBits_congr (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (n₁ d₁ n₂ d₂ : Nat)
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h : n₁ * d₂ = n₂ * d₁) :
    roundRatioBits mode f neg n₁ d₁ = roundRatioBits mode f neg n₂ d₂ := by
  rw [← roundRatioBits_mul mode f neg n₁ d₁ d₂ h₂, ← roundRatioBits_mul mode f neg n₂ d₂ d₁ h₁, h,
    Nat.mul_comm d₁ d₂]

theorem powScale_snd_pos (S : Nat) (t : Int) : 0 < (powScale S 1 t).2 := by
  cases t <;> simp [powScale, Nat.two_pow_pos]

theorem powScale_fst_pos (S d : Nat) (t : Int) (hS : 0 < S) : 0 < (powScale S d t).1 := by
  cases t with
  | ofNat k => exact Nat.mul_pos hS (Nat.two_pow_pos k)
  | negSucc k => exact hS

/-- `roundQuotient` undoes the scaling `powScale (powScale S 1 t) (-t)`. -/
theorem roundQuotient_powScale_neg (mode : RoundingMode) (S : Nat) (t : Int) :
    roundQuotient mode (powScale (powScale S 1 t).1 (powScale S 1 t).2 (-t)).1
      (powScale (powScale S 1 t).1 (powScale S 1 t).2 (-t)).2 = S := by
  match t with
  | .ofNat 0 =>
    simp only [powScale, Nat.pow_zero, Nat.mul_one]
    exact roundQuotient_exact mode S 1 (by decide) |>.trans rfl |> fun h => by simpa using h
  | .ofNat (k + 1) =>
    show roundQuotient mode (powScale (S * 2 ^ (k + 1)) 1 (Int.negSucc k)).1
      (powScale (S * 2 ^ (k + 1)) 1 (Int.negSucc k)).2 = S
    simp only [powScale, Nat.one_mul]
    exact roundQuotient_exact mode S _ (Nat.two_pow_pos _)
  | .negSucc k =>
    show roundQuotient mode (powScale S (1 * 2 ^ (k + 1)) (Int.ofNat (k + 1))).1
      (powScale S (1 * 2 ^ (k + 1)) (Int.ofNat (k + 1))).2 = S
    simp only [powScale, Nat.one_mul]
    exact roundQuotient_exact mode S _ (Nat.two_pow_pos _)

/-- `ratioExponent` of `powScale S 1 t` is `log2 S + t`. -/
theorem ratioExponent_powScale (S : Nat) (t : Int) (hS : 0 < S) :
    ratioExponent (powScale S 1 t).1 (powScale S 1 t).2 = (Nat.log2 S : Int) + t := by
  cases t with
  | ofNat k =>
    simp only [powScale]
    rw [ratioExponent_mul_pow S k hS, Int.ofNat_eq_natCast]; omega
  | negSucc k =>
    simp only [powScale, Nat.one_mul]
    rw [ratioExponent_div_pow S (k + 1) hS]; omega

theorem IeeeFormat.fb_le_bias (f : IeeeFormat) : f.fractionBits + 1 ≤ f.bias := by
  cases f <;> decide

theorem IeeeFormat.one_le_fb (f : IeeeFormat) : 1 ≤ f.fractionBits := by
  cases f <;> decide

/-- **Exactness (normal)**: a value `S * 2^t` with a normal significand
`2^fb ≤ S < 2^(fb+1)` and in-range exponent `t + fb` is encoded exactly, in
every rounding mode. -/
theorem roundRatioBits_normal (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (S : Nat)
    (t : Int)
    (hS1 : 2 ^ f.fractionBits ≤ S) (hS2 : S < 2 ^ (f.fractionBits + 1))
    (hE1 : f.minExponent ≤ t + f.fractionBits) (hE2 : t + f.fractionBits ≤ f.maxExponent) :
    roundRatioBits mode f neg (powScale S 1 t).1 (powScale S 1 t).2 =
      encodeBits f neg (t + f.fractionBits + f.bias).toNat (S - 2 ^ f.fractionBits) := by
  have hSpos : 0 < S := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hS1
  have hlog : Nat.log2 S = f.fractionBits := nat_log2_eq_of_bounds S _ hS1 hS2
  have hd : (powScale S 1 t).2 ≠ 0 := Nat.pos_iff_ne_zero.mp (powScale_snd_pos S t)
  have hn : (powScale S 1 t).1 ≠ 0 := Nat.pos_iff_ne_zero.mp (powScale_fst_pos S 1 t hSpos)
  have hre := ratioExponent_powScale S t hSpos
  rw [hlog] at hre
  have hmax : max (ratioExponent (powScale S 1 t).1 (powScale S 1 t).2) f.minExponent =
      t + f.fractionBits := by rw [hre]; omega
  have hsc : (f.fractionBits : Int) - (t + f.fractionBits) = -t := by omega
  have hsig := roundQuotient_powScale_neg mode S t
  have hcarry : ¬ (2 ^ (f.fractionBits + 1) ≤ S) := Nat.not_le.mpr hS2
  have hlt : ¬ (S < 2 ^ f.fractionBits) := Nat.not_lt.mpr hS1
  have hgt : ¬ (t + f.fractionBits > f.maxExponent) := by omega
  unfold roundRatioBits
  simp only [hd, hn, hmax, hsc, hsig, hcarry, hlt, hgt, decide_false, Bool.false_eq_true, ite_false]

/-- **Exactness (subnormal)**: `S * 2^(minExp - fb)` with `0 < S < 2^fb` is
encoded as the subnormal `(0, S)`, in every rounding mode. -/
theorem roundRatioBits_subnormal (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (S : Nat)
    (hS0 : 0 < S) (hS : S < 2 ^ f.fractionBits) :
    roundRatioBits mode f neg (powScale S 1 (f.minExponent - f.fractionBits)).1
        (powScale S 1 (f.minExponent - f.fractionBits)).2 =
      encodeBits f neg 0 S := by
  have hlogS : Nat.log2 S < f.fractionBits := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp hS0)).mpr hS
  have hfb := IeeeFormat.fb_le_bias f
  have hd : (powScale S 1 (f.minExponent - f.fractionBits)).2 ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (powScale_snd_pos S _)
  have hn : (powScale S 1 (f.minExponent - f.fractionBits)).1 ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (powScale_fst_pos S 1 _ hS0)
  have hre := ratioExponent_powScale S (f.minExponent - f.fractionBits) hS0
  have hmax : max (ratioExponent (powScale S 1 (f.minExponent - f.fractionBits)).1
      (powScale S 1 (f.minExponent - f.fractionBits)).2) f.minExponent = f.minExponent := by
    rw [hre]; simp only [IeeeFormat.minExponent] at *; omega
  have hsc : (f.fractionBits : Int) - f.minExponent = -(f.minExponent - f.fractionBits) := by omega
  have hsig := roundQuotient_powScale_neg mode S (f.minExponent - f.fractionBits)
  have hcarry : ¬ (2 ^ (f.fractionBits + 1) ≤ S) := by
    have : 2 ^ f.fractionBits < 2 ^ (f.fractionBits + 1) :=
      two_pow_lt_two_pow (by omega)
    omega
  have hgt : ¬ (f.minExponent > f.maxExponent) := by
    simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent]; omega
  unfold roundRatioBits
  simp only [hd, hn, hmax, hsc, hsig, hcarry, hS, hgt, decide_false, Bool.false_eq_true, ite_false,
    ite_true]

/-- Decoding of explicitly encoded fields. -/
theorem decodeBits_encodeBits (f : IeeeFormat) (neg : Bool) (E F : Nat)
    (hE : E < 2 ^ f.exponentBits) (hF : F < 2 ^ f.fractionBits) :
    decodeBits f (encodeBits f neg E F) =
      if E = 2 ^ f.exponentBits - 1 then
        (if F = 0 then .inf neg
         else .nan neg (Nat.beq ((F / 2 ^ (f.fractionBits - 1)) % 2) 1) F)
      else if E = 0 then
        (if F = 0 then .zero neg
         else .finite neg (powScale F 1 (f.minExponent - f.fractionBits)).1
           (powScale F 1 (f.minExponent - f.fractionBits)).2)
      else .finite neg (powScale (2 ^ f.fractionBits + F) 1 ((E : Int) - f.bias - f.fractionBits)).1
        (powScale (2 ^ f.fractionBits + F) 1 ((E : Int) - f.bias - f.fractionBits)).2 := by
  unfold decodeBits
  rw [unpackBits_encodeBits f neg E F hE hF]

/-- Re-encoding the unpacked fields reproduces the bit pattern. -/
theorem encodeBits_unpackBits (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    encodeBits f (unpackBits f bits).neg (unpackBits f bits).exponent (unpackBits f bits).fraction =
      bits := by
  cases f
  · simp only [IeeeFormat.width, Nat.reducePow] at h
    simp only [encodeBits, zeroBits, unpackBits, IeeeFormat.width, IeeeFormat.fractionBits,
      IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub, nat_beq_eq_decide]
    by_cases hb : bits / 2147483648 % 2 = 1
    · simp only [hb, decide_true, ite_true]; omega
    · simp only [hb, decide_false, Bool.false_eq_true, ite_false]; omega
  · simp only [IeeeFormat.width, Nat.reducePow] at h
    simp only [encodeBits, zeroBits, unpackBits, IeeeFormat.width, IeeeFormat.fractionBits,
      IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub, nat_beq_eq_decide]
    by_cases hb : bits / 9223372036854775808 % 2 = 1
    · simp only [hb, decide_true, ite_true]; omega
    · simp only [hb, decide_false, Bool.false_eq_true, ite_false]; omega

theorem unpackBits_exponent_lt (f : IeeeFormat) (bits : Nat) :
    (unpackBits f bits).exponent < 2 ^ f.exponentBits := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem unpackBits_fraction_lt (f : IeeeFormat) (bits : Nat) :
    (unpackBits f bits).fraction < 2 ^ f.fractionBits := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem IeeeFormat.two_bias_lt (f : IeeeFormat) : 2 * f.bias < 2 ^ f.exponentBits - 1 := by
  cases f <;> decide

theorem IeeeFormat.max_exp_ne_zero (f : IeeeFormat) : ¬ ((0 : Nat) = 2 ^ f.exponentBits - 1) := by
  cases f <;> decide

/-- Decoding a correctly rounded normal value recovers it exactly. -/
theorem decodeBits_roundRatio_normal (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (S : Nat)
    (t : Int) (hS1 : 2 ^ f.fractionBits ≤ S) (hS2 : S < 2 ^ (f.fractionBits + 1))
    (hE1 : f.minExponent ≤ t + f.fractionBits) (hE2 : t + f.fractionBits ≤ f.maxExponent) :
    decodeBits f (roundRatioBits mode f neg (powScale S 1 t).1 (powScale S 1 t).2) =
      .finite neg (powScale S 1 t).1 (powScale S 1 t).2 := by
  rw [roundRatioBits_normal mode f neg S t hS1 hS2 hE1 hE2]
  have hb := IeeeFormat.two_bias_lt f
  simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hE1 hE2
  have hEnn : 0 ≤ t + f.fractionBits + f.bias := by omega
  have hE : ((t + f.fractionBits + f.bias).toNat : Int) = t + f.fractionBits + f.bias :=
    Int.toNat_of_nonneg hEnn
  have hEub : (t + f.fractionBits + f.bias).toNat < 2 ^ f.exponentBits := by omega
  have hEne : ¬ ((t + f.fractionBits + f.bias).toNat = 2 ^ f.exponentBits - 1) := by omega
  have hE0 : ¬ ((t + f.fractionBits + f.bias).toNat = 0) := by omega
  have hF : S - 2 ^ f.fractionBits < 2 ^ f.fractionBits := by
    have : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by rw [Nat.pow_succ]; omega
    omega
  rw [decodeBits_encodeBits f neg _ _ hEub hF, if_neg' hEne, if_neg' hE0,
    Nat.add_sub_cancel' hS1]
  have ht : (((t + f.fractionBits + f.bias).toNat : Nat) : Int) - f.bias - f.fractionBits = t := by
    omega
  rw [ht]

/-- Decoding a correctly rounded subnormal value recovers it exactly. -/
theorem decodeBits_roundRatio_subnormal (mode : RoundingMode) (f : IeeeFormat) (neg : Bool)
    (S : Nat) (hS0 : 0 < S) (hS : S < 2 ^ f.fractionBits) :
    decodeBits f (roundRatioBits mode f neg (powScale S 1 (f.minExponent - f.fractionBits)).1
        (powScale S 1 (f.minExponent - f.fractionBits)).2) =
      .finite neg (powScale S 1 (f.minExponent - f.fractionBits)).1
        (powScale S 1 (f.minExponent - f.fractionBits)).2 := by
  rw [roundRatioBits_subnormal mode f neg S hS0 hS,
    decodeBits_encodeBits f neg 0 S (Nat.two_pow_pos _) hS, if_neg' (IeeeFormat.max_exp_ne_zero f),
    if_pos' rfl, if_neg' (by omega)]

/-- Shifting the significand by `2^j` and the exponent by `-j` preserves the
rational value (cross-multiplication form). -/
theorem powScale_shift_cross (S j : Nat) (t : Int) :
    (powScale (S * 2 ^ j) 1 (t - j)).1 * (powScale S 1 t).2 =
      (powScale S 1 t).1 * (powScale (S * 2 ^ j) 1 (t - j)).2 := by
  have key : ∀ (S' : Nat) (u : Int), powScale S' 1 u =
      if 0 ≤ u then (S' * 2 ^ u.toNat, 1) else (S', 2 ^ (-u).toNat) := by
    intro S' u
    cases u with
    | ofNat k => simp [powScale]
    | negSucc k =>
      simp only [powScale, Nat.one_mul]
      have : ¬ (0 ≤ Int.negSucc k) := by omega
      rw [if_neg' this]
      simp [Int.neg_negSucc]
  rw [key S t, key (S * 2 ^ j) (t - j)]
  by_cases h2 : 0 ≤ t
  · by_cases h1 : 0 ≤ t - (j : Int)
    · rw [if_pos' h1, if_pos' h2]
      simp only [Nat.mul_one, Nat.mul_assoc, pow_mul_pow]
      congr 2; omega
    · rw [if_neg' h1, if_pos' h2]
      simp only [Nat.mul_one, Nat.mul_assoc, pow_mul_pow]
      congr 2; omega
  · have h1 : ¬ (0 ≤ t - (j : Int)) := by omega
    rw [if_neg' h1, if_neg' h2]
    simp only [Nat.mul_assoc, pow_mul_pow]
    congr 2; omega

/-- `k` denotes exactly the integer `v`. -/
def floatKindDenotesInt : FloatKind → Int → Prop
  | .zero neg, v => v = 0 ∧ neg = false
  | .finite neg n d, v => 0 < d ∧ n = v.natAbs * d ∧ neg = decide (v < 0)
  | _, _ => False

theorem IeeeFormat.fb_add_bias_lt (f : IeeeFormat) :
    f.fractionBits + f.bias < 2 ^ f.exponentBits - 1 := by
  cases f <;> decide

/-- **Exactness on representable integers**: every integer `v` with
`|v| < 2^(fb+1)` (in particular every `i32` / `u32` into `binary64`) converts
exactly. -/
theorem evalIntToFloatRoundTiesToEven_exact (signed : Bool) (w bits : Nat) (dst : IeeeFormat)
    (h : (intValueOfBits signed w bits).natAbs < 2 ^ (dst.fractionBits + 1)) :
    floatKindDenotesInt (decodeBits dst (evalIntToFloatRoundTiesToEven signed w bits dst))
      (intValueOfBits signed w bits) := by
  rw [evalIntToFloatRoundTiesToEven_eq_roundRatioBits]
  generalize intValueOfBits signed w bits = v at h ⊢
  by_cases hv : v = 0
  · subst hv
    have hz : roundRatioBits .tiesToEven dst (decide ((0 : Int) < 0)) (Int.natAbs 0) 1 =
        encodeBits dst false 0 0 := by
      simp [roundRatioBits, zeroBits, encodeBits]
    rw [hz, decodeBits_encodeBits dst false 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _),
      if_neg' (IeeeFormat.max_exp_ne_zero dst), if_pos' rfl, if_pos' rfl]
    exact ⟨rfl, rfl⟩
  · have hm : 0 < v.natAbs := by omega
    generalize hmv : v.natAbs = m at hm h
    have hL1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hm)
    have hL2 := Nat.lt_log2_self (n := m)
    generalize hLv : Nat.log2 m = L at hL1 hL2
    have hLfb : L ≤ dst.fractionBits := by
      have := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp hm)).mpr h
      omega
    have hfb := IeeeFormat.fb_le_bias dst
    have hS1 : 2 ^ dst.fractionBits ≤ m * 2 ^ (dst.fractionBits - L) := by
      have := Nat.mul_le_mul_right (2 ^ (dst.fractionBits - L)) hL1
      rwa [pow_mul_pow, Nat.add_sub_cancel' hLfb] at this
    have hS2 : m * 2 ^ (dst.fractionBits - L) < 2 ^ (dst.fractionBits + 1) := by
      have := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos (dst.fractionBits - L))
      rwa [pow_mul_pow, show L + 1 + (dst.fractionBits - L) = dst.fractionBits + 1 by omega] at this
    have hcross := powScale_shift_cross m (dst.fractionBits - L) 0
    have h0 : powScale m 1 0 = (m, 1) := by simp [powScale]
    rw [h0] at hcross
    simp only [Nat.mul_one] at hcross
    have hcong : roundRatioBits .tiesToEven dst (decide (v < 0)) m 1 =
        roundRatioBits .tiesToEven dst (decide (v < 0))
          (powScale (m * 2 ^ (dst.fractionBits - L)) 1
            (0 - ((dst.fractionBits - L : Nat) : Int))).1
          (powScale (m * 2 ^ (dst.fractionBits - L)) 1
            (0 - ((dst.fractionBits - L : Nat) : Int))).2 :=
      roundRatioBits_congr _ _ _ _ _ _ _ (by decide) (powScale_snd_pos _ _)
        (by rw [Nat.mul_one]; exact hcross.symm)
    rw [hcong, decodeBits_roundRatio_normal _ _ _ _ _ hS1 hS2
      (by simp only [IeeeFormat.minExponent]; omega) (by simp only [IeeeFormat.maxExponent]; omega)]
    refine ⟨powScale_snd_pos _ _, ?_, rfl⟩
    rw [hmv]; exact hcross

/-- Every `i32` / `u32` converts to `binary64` exactly. -/
theorem evalIntToFloat_i32_u32_to_f64_exact (signed : Bool) (bits : Nat) :
    floatKindDenotesInt
      (decodeBits .binary64 (evalIntToFloatRoundTiesToEven signed 32 bits .binary64))
      (intValueOfBits signed 32 bits) := by
  apply evalIntToFloatRoundTiesToEven_exact
  simp only [intValueOfBits, IeeeFormat.fractionBits, Nat.reducePow, Nat.reduceSub]
  have := Nat.mod_lt bits (show 0 < 4294967296 by decide)
  split <;> omega

/-- Two decoded values are the same extended real (same sign; equal
rationals). -/
def floatKindSameValue : FloatKind → FloatKind → Prop
  | .zero n₁, .zero n₂ => n₁ = n₂
  | .finite s₁ a₁ b₁, .finite s₂ a₂ b₂ => s₁ = s₂ ∧ a₁ * b₂ = a₂ * b₁ ∧ 0 < b₁ ∧ 0 < b₂
  | .inf n₁, .inf n₂ => n₁ = n₂
  | _, _ => False

theorem zeroBits_eq_encodeBits (f : IeeeFormat) (neg : Bool) :
    zeroBits f neg = encodeBits f neg 0 0 := by
  simp [encodeBits]

/-- Normal `binary64` side conditions as hypotheses (avoids multi-line nested
`by`). -/
theorem f64_encode_lt (neg : Bool) (E F : Nat) (hE : E < 2048) (hF : F < 4503599627370496) :
    encodeBits .binary64 neg E F < 2 ^ 64 := encodeBits_lt .binary64 neg E F hE hF

theorem convertFloatBits_of_zero (mode : RoundingMode) (src dst : IeeeFormat) (bits : Nat)
    (neg : Bool) (h : decodeBits src bits = .zero neg) :
    convertFloatBits mode src dst bits = zeroBits dst neg := by
  unfold convertFloatBits; rw [h]

theorem convertFloatBits_of_inf (mode : RoundingMode) (src dst : IeeeFormat) (bits : Nat)
    (neg : Bool) (h : decodeBits src bits = .inf neg) :
    convertFloatBits mode src dst bits = infBits dst neg := by
  unfold convertFloatBits; rw [h]

theorem convertFloatBits_of_finite (mode : RoundingMode) (src dst : IeeeFormat) (bits : Nat)
    (neg : Bool) (n d : Nat) (h : decodeBits src bits = .finite neg n d) :
    convertFloatBits mode src dst bits = roundRatioBits mode dst neg n d := by
  unfold convertFloatBits; rw [h]

theorem isNaNBits_of_nan (f : IeeeFormat) (bits : Nat) (neg q : Bool) (p : Nat)
    (h : decodeBits f bits = .nan neg q p) : isNaNBits f bits = true := by
  unfold isNaNBits; rw [h]

/-- Round-trip obligation for one `binary32` bit pattern. -/
def F32RoundTrip (b : Nat) : Prop :=
  ∃ W, W < 2 ^ 64 ∧
    convertFloatBits .tiesToEven .binary32 .binary64 b = W ∧
    floatKindSameValue (decodeBits .binary64 W) (decodeBits .binary32 b) ∧
    convertFloatBits .tiesToEven .binary64 .binary32 W = b

theorem f32_rt_inf (neg : Bool) : F32RoundTrip (encodeBits .binary32 neg 255 0) := by
  have hdec32 : decodeBits .binary32 (encodeBits .binary32 neg 255 0) = .inf neg := by
    rw [decodeBits_encodeBits .binary32 neg 255 0 (by decide) (by decide)]
    simp [IeeeFormat.exponentBits]
  have hd64 : decodeBits .binary64 (infBits .binary64 neg) = .inf neg := by
    simp only [infBits]
    rw [decodeBits_encodeBits .binary64 neg _ 0 (by decide) (by decide)]
    simp
  have hback : infBits .binary32 neg = encodeBits .binary32 neg 255 0 := by
    simp [infBits, IeeeFormat.exponentBits]
  refine ⟨infBits .binary64 neg, f64_encode_lt neg _ _ (by decide) (by decide), ?_, ?_, ?_⟩
  · exact convertFloatBits_of_inf _ _ _ _ _ hdec32
  · rw [hd64, hdec32]; exact rfl
  · rw [convertFloatBits_of_inf _ _ _ _ _ hd64]; exact hback

theorem f32_rt_zero (neg : Bool) : F32RoundTrip (encodeBits .binary32 neg 0 0) := by
  have hdec32 : decodeBits .binary32 (encodeBits .binary32 neg 0 0) = .zero neg := by
    rw [decodeBits_encodeBits .binary32 neg 0 0 (by decide) (by decide)]
    simp [IeeeFormat.exponentBits]
  have hd64 : decodeBits .binary64 (zeroBits .binary64 neg) = .zero neg := by
    rw [zeroBits_eq_encodeBits, decodeBits_encodeBits .binary64 neg 0 0 (by decide) (by decide)]
    simp [IeeeFormat.exponentBits]
  have hz64 : zeroBits .binary64 neg < 2 ^ 64 := by
    rw [zeroBits_eq_encodeBits]; exact f64_encode_lt neg 0 0 (by decide) (by decide)
  refine ⟨zeroBits .binary64 neg, hz64, ?_, ?_, ?_⟩
  · exact convertFloatBits_of_zero _ _ _ _ _ hdec32
  · rw [hd64, hdec32]; exact rfl
  · rw [convertFloatBits_of_zero _ _ _ _ _ hd64]; exact zeroBits_eq_encodeBits .binary32 neg

theorem f32_rt_subnormal (neg : Bool) (F : Nat) (hF0 : F ≠ 0) (hFl : F < 8388608) :
    F32RoundTrip (encodeBits .binary32 neg 0 F) := by
  have hdec := decodeBits_encodeBits .binary32 neg 0 F (by decide) hFl
  have hdec32 : decodeBits .binary32 (encodeBits .binary32 neg 0 F) =
      .finite neg
        (powScale F 1 (IeeeFormat.binary32.minExponent - IeeeFormat.binary32.fractionBits)).1
        (powScale F 1 (IeeeFormat.binary32.minExponent - IeeeFormat.binary32.fractionBits)).2 := by
    rw [hdec]; simp [hF0, IeeeFormat.exponentBits, IeeeFormat.fractionBits, IeeeFormat.bias,
      IeeeFormat.minExponent]
  have hFpos : 0 < F := Nat.pos_of_ne_zero hF0
  have hL1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hFpos)
  have hL2 := Nat.lt_log2_self (n := F)
  generalize hLv : Nat.log2 F = L at hL1 hL2
  have hL23 : L < 23 := by
    have := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp hFpos)).mpr (show F < 2 ^ 23 from hFl)
    omega
  have hS1 : 2 ^ IeeeFormat.binary64.fractionBits ≤ F * 2 ^ (52 - L) := by
    have := Nat.mul_le_mul_right (2 ^ (52 - L)) hL1
    rwa [pow_mul_pow, show L + (52 - L) = 52 by omega] at this
  have hS2 : F * 2 ^ (52 - L) < 2 ^ (IeeeFormat.binary64.fractionBits + 1) := by
    have := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos (52 - L))
    rwa [pow_mul_pow, show L + 1 + (52 - L) = 52 + 1 by omega] at this
  generalize ht : (IeeeFormat.binary32.minExponent - IeeeFormat.binary32.fractionBits : Int) = t
    at hdec32
  have htv : t = -149 := by
    rw [← ht]; simp [IeeeFormat.minExponent, IeeeFormat.fractionBits, IeeeFormat.bias]
  have hcross := powScale_shift_cross F (52 - L) t
  have hE1 : IeeeFormat.binary64.minExponent ≤
      t - ((52 - L : Nat) : Int) + IeeeFormat.binary64.fractionBits := by
    simp only [IeeeFormat.minExponent, IeeeFormat.fractionBits, IeeeFormat.bias]; omega
  have hE2 : t - ((52 - L : Nat) : Int) + IeeeFormat.binary64.fractionBits ≤
      IeeeFormat.binary64.maxExponent := by
    simp only [IeeeFormat.maxExponent, IeeeFormat.fractionBits, IeeeFormat.bias]; omega
  have hcong := fun f => roundRatioBits_congr .tiesToEven f neg
    (powScale F 1 t).1 (powScale F 1 t).2
    (powScale (F * 2 ^ (52 - L)) 1 (t - ((52 - L : Nat) : Int))).1
    (powScale (F * 2 ^ (52 - L)) 1 (t - ((52 - L : Nat) : Int))).2
    (powScale_snd_pos _ _) (powScale_snd_pos _ _) hcross.symm
  have hn64 := roundRatioBits_normal .tiesToEven .binary64 neg _ _ hS1 hS2 hE1 hE2
  have hd64 := decodeBits_roundRatio_normal .tiesToEven .binary64 neg _ _ hS1 hS2 hE1 hE2
  have hsub32 := roundRatioBits_subnormal .tiesToEven .binary32 neg F hFpos hFl
  rw [ht] at hsub32
  have hWlt : encodeBits .binary64 neg
      (t - ((52 - L : Nat) : Int) + IeeeFormat.binary64.fractionBits +
        IeeeFormat.binary64.bias).toNat
      (F * 2 ^ (52 - L) - 2 ^ IeeeFormat.binary64.fractionBits) < 2 ^ 64 := by
    apply f64_encode_lt
    · simp only [IeeeFormat.fractionBits, IeeeFormat.bias]; omega
    · simp only [IeeeFormat.fractionBits] at hS1 hS2 ⊢
      simp only [Nat.reducePow, Nat.reduceAdd] at hS1 hS2 ⊢
      omega
  refine ⟨roundRatioBits .tiesToEven .binary64 neg (powScale F 1 t).1 (powScale F 1 t).2,
    ?_, ?_, ?_, ?_⟩
  · rw [hcong, hn64]; exact hWlt
  · exact convertFloatBits_of_finite _ _ _ _ _ _ _ hdec32
  · rw [hcong, hd64, hdec32]
    exact ⟨rfl, hcross, powScale_snd_pos _ _, powScale_snd_pos _ _⟩
  · rw [hcong, convertFloatBits_of_finite _ _ _ _ _ _ _ hd64, ← hcong .binary32]
    exact hsub32

theorem f32_rt_normal (neg : Bool) (E F : Nat) (hE255 : ¬ E = 255) (hE0 : ¬ E = 0) (hEl : E < 256)
    (hFl : F < 8388608) : F32RoundTrip (encodeBits .binary32 neg E F) := by
  have hdec := decodeBits_encodeBits .binary32 neg E F hEl hFl
  have hdec32 : decodeBits .binary32 (encodeBits .binary32 neg E F) =
      .finite neg (powScale (2 ^ IeeeFormat.binary32.fractionBits + F) 1
          ((E : Int) - IeeeFormat.binary32.bias - IeeeFormat.binary32.fractionBits)).1
        (powScale (2 ^ IeeeFormat.binary32.fractionBits + F) 1
          ((E : Int) - IeeeFormat.binary32.bias - IeeeFormat.binary32.fractionBits)).2 := by
    rw [hdec]
    have h1 : ¬ (E = 2 ^ IeeeFormat.binary32.exponentBits - 1) := by
      simp only [IeeeFormat.exponentBits]; omega
    rw [if_neg' h1, if_neg' hE0]
  generalize hS : 2 ^ IeeeFormat.binary32.fractionBits + F = S at hdec32
  generalize ht : ((E : Int) - IeeeFormat.binary32.bias - IeeeFormat.binary32.fractionBits) = t
    at hdec32
  have hSv : S = 8388608 + F := by rw [← hS]; rfl
  have htv : t = (E : Int) - 150 := by
    rw [← ht]; simp [IeeeFormat.bias, IeeeFormat.fractionBits]; omega
  have hS1 : 2 ^ IeeeFormat.binary32.fractionBits ≤ S := by
    simp only [IeeeFormat.fractionBits, Nat.reducePow]; omega
  have hS2 : S < 2 ^ (IeeeFormat.binary32.fractionBits + 1) := by
    simp only [IeeeFormat.fractionBits, Nat.reducePow, Nat.reduceAdd]; omega
  have hT1 : 2 ^ IeeeFormat.binary64.fractionBits ≤ S * 2 ^ 29 := by
    simp only [IeeeFormat.fractionBits, Nat.reducePow]; omega
  have hT2 : S * 2 ^ 29 < 2 ^ (IeeeFormat.binary64.fractionBits + 1) := by
    simp only [IeeeFormat.fractionBits, Nat.reducePow, Nat.reduceAdd]; omega
  have hcross := powScale_shift_cross S 29 t
  have hE1 : IeeeFormat.binary64.minExponent ≤
      t - ((29 : Nat) : Int) + IeeeFormat.binary64.fractionBits := by
    simp only [IeeeFormat.minExponent, IeeeFormat.fractionBits, IeeeFormat.bias]; omega
  have hE2 : t - ((29 : Nat) : Int) + IeeeFormat.binary64.fractionBits ≤
      IeeeFormat.binary64.maxExponent := by
    simp only [IeeeFormat.maxExponent, IeeeFormat.fractionBits, IeeeFormat.bias]; omega
  have hF1 : IeeeFormat.binary32.minExponent ≤ t + IeeeFormat.binary32.fractionBits := by
    simp only [IeeeFormat.minExponent, IeeeFormat.fractionBits, IeeeFormat.bias]; omega
  have hF2 : t + IeeeFormat.binary32.fractionBits ≤ IeeeFormat.binary32.maxExponent := by
    simp only [IeeeFormat.maxExponent, IeeeFormat.fractionBits, IeeeFormat.bias]; omega
  have hcong := fun f => roundRatioBits_congr .tiesToEven f neg
    (powScale S 1 t).1 (powScale S 1 t).2
    (powScale (S * 2 ^ 29) 1 (t - ((29 : Nat) : Int))).1
    (powScale (S * 2 ^ 29) 1 (t - ((29 : Nat) : Int))).2
    (powScale_snd_pos _ _) (powScale_snd_pos _ _) hcross.symm
  have hn64 := roundRatioBits_normal .tiesToEven .binary64 neg _ _ hT1 hT2 hE1 hE2
  have hd64 := decodeBits_roundRatio_normal .tiesToEven .binary64 neg _ _ hT1 hT2 hE1 hE2
  have hn32 := roundRatioBits_normal .tiesToEven .binary32 neg S t hS1 hS2 hF1 hF2
  have hWlt : encodeBits .binary64 neg
      (t - ((29 : Nat) : Int) + IeeeFormat.binary64.fractionBits + IeeeFormat.binary64.bias).toNat
      (S * 2 ^ 29 - 2 ^ IeeeFormat.binary64.fractionBits) < 2 ^ 64 := by
    apply f64_encode_lt
    · simp only [IeeeFormat.fractionBits, IeeeFormat.bias]; omega
    · simp only [IeeeFormat.fractionBits, Nat.reducePow]; omega
  refine ⟨roundRatioBits .tiesToEven .binary64 neg (powScale S 1 t).1 (powScale S 1 t).2,
    ?_, ?_, ?_, ?_⟩
  · rw [hcong, hn64]; exact hWlt
  · exact convertFloatBits_of_finite _ _ _ _ _ _ _ hdec32
  · rw [hcong, hd64, hdec32]
    exact ⟨rfl, hcross, powScale_snd_pos _ _, powScale_snd_pos _ _⟩
  · rw [hcong, convertFloatBits_of_finite _ _ _ _ _ _ _ hd64, ← hcong .binary32, hn32]
    have hEeq : (t + IeeeFormat.binary32.fractionBits + IeeeFormat.binary32.bias).toNat = E := by
      simp only [IeeeFormat.fractionBits, IeeeFormat.bias]; omega
    have hFeq : S - 2 ^ IeeeFormat.binary32.fractionBits = F := by
      simp only [IeeeFormat.fractionBits, Nat.reducePow]; omega
    rw [hEeq, hFeq]

/-- Per-case witness for the `f32 → f64 → f32` round trip. -/
theorem f32_roundtrip_core (x : F32Bits) (hx : isNaNBits .binary32 x.toNat = false) :
    F32RoundTrip x.toNat := by
  have hxlt := x.isLt
  have henc := encodeBits_unpackBits .binary32 x.toNat hxlt
  have hEl := unpackBits_exponent_lt .binary32 x.toNat
  have hFl := unpackBits_fraction_lt .binary32 x.toNat
  generalize unpackBits .binary32 x.toNat = c at henc hEl hFl
  obtain ⟨neg, E, F⟩ := c
  simp only at henc hEl hFl
  rw [← henc] at hx ⊢
  simp only [IeeeFormat.exponentBits, IeeeFormat.fractionBits, Nat.reducePow] at hEl hFl
  by_cases hE255 : E = 255
  · subst hE255
    by_cases hF0 : F = 0
    · subst hF0; exact f32_rt_inf neg
    · have hdec32 : decodeBits .binary32 (encodeBits .binary32 neg 255 F) =
          .nan neg (Nat.beq ((F / 2 ^ 22) % 2) 1) F := by
        rw [decodeBits_encodeBits .binary32 neg 255 F (by decide) hFl]
        simp [hF0, IeeeFormat.exponentBits, IeeeFormat.fractionBits]
      rw [isNaNBits_of_nan _ _ _ _ _ hdec32] at hx
      exact Bool.noConfusion hx
  · by_cases hE0 : E = 0
    · subst hE0
      by_cases hF0 : F = 0
      · subst hF0; exact f32_rt_zero neg
      · exact f32_rt_subnormal neg F hF0 hFl
    · exact f32_rt_normal neg E F hE255 hE0 hEl hFl

/-- **`f32 → f64` exact rational preservation and `f64ToF32 (f32ToF64 x) = x`**
for every non-NaN `F32Bits`. -/
theorem f32ToF64_exact_and_roundtrip (x : F32Bits) (hx : isNaNBits .binary32 x.toNat = false) :
    floatKindSameValue (decodeBits .binary64 (f32ToF64 x).toNat) (decodeBits .binary32 x.toNat) ∧
    f64ToF32 (f32ToF64 x) = x := by
  obtain ⟨W, hW, hw, hsame, hn⟩ := f32_roundtrip_core x hx
  have hwide : (f32ToF64 x).toNat = W := by
    simp only [f32ToF64, ← convertFloatBits_tiesToEven, BitVec.toNat_ofNat, hw]
    exact Nat.mod_eq_of_lt hW
  refine ⟨by rw [hwide]; exact hsame, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [f64ToF32, ← convertFloatBits_tiesToEven, BitVec.toNat_ofNat, hwide, hn]
  exact Nat.mod_eq_of_lt x.isLt

theorem isQuietNaNBits_of_nan (f : IeeeFormat) (bits : Nat) (neg q : Bool) (p : Nat)
    (h : decodeBits f bits = .nan neg q p) : isQuietNaNBits f bits = q := by
  unfold isQuietNaNBits; rw [h]

/-- **Universal quiet-NaN guarantee**: every NaN input converts to a *quiet* NaN
in every direction (`f32 → f64`, `f64 → f32`, and same-format). -/
theorem convertFloatBits_nan_quiet (mode : RoundingMode) (src dst : IeeeFormat) (bits : Nat)
    (h : isNaNBits src bits = true) :
    isNaNBits dst (convertFloatBits mode src dst bits) = true ∧
      isQuietNaNBits dst (convertFloatBits mode src dst bits) = true := by
  have hFl := unpackBits_fraction_lt src bits
  have hdecNaN : ∃ neg q, decodeBits src bits = .nan neg q (unpackBits src bits).fraction := by
    unfold isNaNBits at h
    unfold decodeBits at h ⊢
    simp only at h ⊢
    by_cases hE : (unpackBits src bits).exponent = 2 ^ src.exponentBits - 1
    · by_cases hF : (unpackBits src bits).fraction = 0
      · rw [if_pos' hE, if_pos' hF] at h; simp at h
      · rw [if_pos' hE, if_neg' hF]
        exact ⟨_, _, rfl⟩
    · rw [if_neg' hE] at h
      by_cases hZ : (unpackBits src bits).exponent = 0
      · rw [if_pos' hZ] at h
        by_cases hF : (unpackBits src bits).fraction = 0
        · rw [if_pos' hF] at h; simp at h
        · rw [if_neg' hF] at h; simp at h
      · rw [if_neg' hZ] at h; simp at h
  obtain ⟨neg, q, hdec⟩ := hdecNaN
  generalize (unpackBits src bits).fraction = F at hFl hdec
  have hconv : convertFloatBits mode src dst bits =
      encodeBits dst neg (2 ^ dst.exponentBits - 1)
        (Nat.lor (if src.fractionBits ≤ dst.fractionBits then
            Nat.lor F (2 ^ (src.fractionBits - 1)) * 2 ^ (dst.fractionBits - src.fractionBits)
          else Nat.lor F (2 ^ (src.fractionBits - 1)) / 2 ^ (src.fractionBits - dst.fractionBits))
          (2 ^ (dst.fractionBits - 1))) := by
    unfold convertFloatBits; rw [hdec]
  have hs1 := IeeeFormat.one_le_fb src
  have hd1 := IeeeFormat.one_le_fb dst
  have hq : Nat.lor F (2 ^ (src.fractionBits - 1)) < 2 ^ src.fractionBits :=
    Nat.or_lt_two_pow hFl (two_pow_lt_two_pow (by omega))
  have hp : (if src.fractionBits ≤ dst.fractionBits then
            Nat.lor F (2 ^ (src.fractionBits - 1)) * 2 ^ (dst.fractionBits - src.fractionBits)
          else Nat.lor F (2 ^ (src.fractionBits - 1)) / 2 ^ (src.fractionBits - dst.fractionBits)) <
        2 ^ dst.fractionBits := by
    split
    · rename_i hle
      have := Nat.mul_lt_mul_of_pos_right hq (Nat.two_pow_pos (dst.fractionBits - src.fractionBits))
      rwa [pow_mul_pow, Nat.add_sub_cancel' hle] at this
    · rename_i hle
      apply nat_div_lt_of_lt_mul
      rw [pow_mul_pow,
        show src.fractionBits - dst.fractionBits + dst.fractionBits = src.fractionBits by omega]
      exact hq
  generalize (if src.fractionBits ≤ dst.fractionBits then
            Nat.lor F (2 ^ (src.fractionBits - 1)) * 2 ^ (dst.fractionBits - src.fractionBits)
          else
            Nat.lor F (2 ^ (src.fractionBits - 1)) / 2 ^ (src.fractionBits - dst.fractionBits)) =
      p at hp hconv
  have hP : Nat.lor p (2 ^ (dst.fractionBits - 1)) < 2 ^ dst.fractionBits :=
    Nat.or_lt_two_pow hp (two_pow_lt_two_pow (by omega))
  have hbit : (Nat.lor p (2 ^ (dst.fractionBits - 1))).testBit (dst.fractionBits - 1) = true := by
    show (p ||| 2 ^ (dst.fractionBits - 1)).testBit (dst.fractionBits - 1) = true
    rw [Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true]
  have hP0 : Nat.lor p (2 ^ (dst.fractionBits - 1)) ≠ 0 := by
    intro h0; rw [h0] at hbit; simp at hbit
  have hqbit :
      Nat.beq ((Nat.lor p (2 ^ (dst.fractionBits - 1)) / 2 ^ (dst.fractionBits - 1)) % 2) 1 =
        true := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at hbit
    have := of_decide_eq_true hbit
    rw [this]; rfl
  have hE : 2 ^ dst.exponentBits - 1 < 2 ^ dst.exponentBits :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have hdec' := decodeBits_encodeBits dst neg (2 ^ dst.exponentBits - 1) _ hE hP
  rw [if_pos' rfl, if_neg' hP0] at hdec'
  rw [hconv]
  exact ⟨isNaNBits_of_nan _ _ _ _ _ hdec',
    by rw [isQuietNaNBits_of_nan _ _ _ _ _ hdec']; exact hqbit⟩

/-! ### ½-ULP and unreachable `inconsistentRounding` in `roundRatioBits` -/

theorem powScale_snd_pos_gen (n d : Nat) (hd : 0 < d) (t : Int) : 0 < (powScale n d t).2 := by
  cases t with
  | ofNat _ => exact hd
  | negSucc k => exact Nat.mul_pos hd (Nat.two_pow_pos (k + 1))

theorem powScale_diff_cross (n d : Nat) (a b : Int) (hab : a ≤ b) :
    (powScale n d a).1 * (powScale n d b).2 * 2 ^ (b - a).toNat =
      (powScale n d b).1 * (powScale n d a).2 := by
  have key : ∀ (u : Int), powScale n d u =
      if 0 ≤ u then (n * 2 ^ u.toNat, d) else (n, d * 2 ^ (-u).toNat) := by
    intro u
    cases u with
    | ofNat k => simp [powScale]
    | negSucc k =>
      simp only [powScale]
      have : ¬ (0 ≤ Int.negSucc k) := by omega
      rw [if_neg' this]
      simp [Int.neg_negSucc]
  rw [key a, key b]
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := by omega
    rw [if_pos' ha, if_pos' hb]
    simp only [Nat.mul_right_comm _ d, Nat.mul_assoc, pow_mul_pow]
    congr 3; omega
  · by_cases hb : 0 ≤ b
    · rw [if_neg' ha, if_pos' hb]
      simp only
      rw [← Nat.mul_assoc (n * 2 ^ b.toNat), Nat.mul_right_comm n (2 ^ b.toNat) d,
        Nat.mul_assoc (n * d), pow_mul_pow]
      congr 2; omega
    · rw [if_neg' ha, if_neg' hb]
      simp only [Nat.mul_assoc, pow_mul_pow]
      congr 3; omega

theorem powScale_neg_ratioExponent_bounds (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    (powScale n d (- ratioExponent n d)).2 ≤ (powScale n d (- ratioExponent n d)).1 ∧
    (powScale n d (- ratioExponent n d)).1 < 2 * (powScale n d (- ratioExponent n d)).2 := by
  unfold ratioExponent
  by_cases hdn : d ≤ n
  · rw [if_pos' hdn]
    have hq : n / d ≠ 0 := by
      have : 1 ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
      omega
    have hL1 : d * 2 ^ (n / d).log2 ≤ n := by
      rw [Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le hd).mp (Nat.log2_self_le hq)
    have hL2 : n < 2 * (d * 2 ^ (n / d).log2) := by
      have := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_log2_self (n := n / d))
      rw [Nat.pow_succ, Nat.mul_right_comm (2 ^ (n / d).log2) 2 d, Nat.mul_comm _ 2,
        Nat.mul_comm (2 ^ (n / d).log2) d] at this
      exact this
    cases hL : (n / d).log2 with
    | zero =>
      rw [hL] at hL1 hL2
      simp only [Int.natCast_zero, Int.neg_zero, powScale, Nat.pow_zero, Nat.mul_one] at hL1 hL2 ⊢
      exact ⟨hL1, hL2⟩
    | succ m =>
      rw [hL] at hL1 hL2
      have hneg : -(((m + 1 : Nat) : Int)) = Int.negSucc m := rfl
      rw [hneg]
      simp only [powScale]
      exact ⟨hL1, hL2⟩
  · rw [if_neg' hdn]
    have hq : d / n ≠ 0 := by
      have : 1 ≤ d / n := (Nat.le_div_iff_mul_le hn).mpr (by omega)
      omega
    have hk1 : n * 2 ^ (d / n).log2 ≤ d := by
      rw [Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le hn).mp (Nat.log2_self_le hq)
    have hk2 : d < n * 2 ^ ((d / n).log2 + 1) := by
      rw [Nat.mul_comm]
      exact (Nat.div_lt_iff_lt_mul hn).mp (Nat.lt_log2_self (n := d / n))
    generalize (d / n).log2 = k at hk1 hk2
    by_cases hle : d ≤ n * 2 ^ k
    · rw [if_pos' hle, Int.neg_neg]
      have hof : ((k : Nat) : Int) = Int.ofNat k := rfl
      rw [hof]
      simp only [powScale]
      exact ⟨hle, by omega⟩
    · rw [if_neg' hle]
      have hneg : -(-((k : Int) + 1)) = ((k + 1 : Nat) : Int) := by omega
      rw [hneg]
      have hof : ((k + 1 : Nat) : Int) = Int.ofNat (k + 1) := rfl
      rw [hof]
      simp only [powScale]
      have hlt : n * 2 ^ (k + 1) < 2 * d := by
        rw [Nat.pow_succ, ← Nat.mul_assoc]; omega
      exact ⟨Nat.le_of_lt hk2, hlt⟩

theorem scale_lo_helper {A1 A2 B1 B2 F : Nat} (hd : 0 < A2) (hb1 : A2 ≤ A1)
    (hc : A1 * B2 * F = B1 * A2) : F * B2 ≤ B1 := by
  apply (Nat.mul_le_mul_right_iff hd).mp
  have h1 : A2 * (F * B2) ≤ A1 * (F * B2) := Nat.mul_le_mul_right (F * B2) hb1
  have h2 : A2 * (F * B2) = F * B2 * A2 := Nat.mul_comm _ _
  have h3 : A1 * (F * B2) = A1 * B2 * F := by
    rw [Nat.mul_comm F B2, ← Nat.mul_assoc]
  omega

theorem scale_hi_helper {A1 A2 B1 B2 F : Nat} (hd : 0 < A2) (hb2 : A1 < 2 * A2)
    (hdse : 0 < B2) (hc : A1 * B2 * F = B1 * A2) (hF : 0 < F) : B1 < F * 2 * B2 := by
  apply (nat_mul_lt_mul_right_iff hd).mp
  have h1 : A1 * B2 * F < 2 * A2 * B2 * F :=
    Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hb2 hdse) hF
  have h2 : 2 * A2 * B2 * F = F * 2 * B2 * A2 := by
    rw [Nat.mul_right_comm (2 * A2) B2 F, Nat.mul_right_comm 2 A2 F,
      Nat.mul_right_comm (2 * F) A2 B2, Nat.mul_comm 2 F]
  omega

theorem scale_sub_helper {S1 S2 B1 B2 F P : Nat} (hdse : 0 < B2) (hP : 2 ≤ P)
    (hc : S1 * B2 * P = B1 * S2) (hhi : B1 < F * 2 * B2) (hS2 : 0 < S2) : S1 < F * S2 := by
  apply (nat_mul_lt_mul_right_iff hdse).mp
  have h1 : S1 * B2 * 2 ≤ S1 * B2 * P := Nat.mul_le_mul_left (S1 * B2) hP
  have h2 : B1 * S2 < F * 2 * B2 * S2 := Nat.mul_lt_mul_of_pos_right hhi hS2
  have h3 : F * 2 * B2 * S2 = F * S2 * B2 * 2 := by
    rw [Nat.mul_right_comm (F * 2) B2 S2, Nat.mul_right_comm F 2 S2,
      Nat.mul_assoc (F * S2) 2 B2, Nat.mul_comm 2 B2, ← Nat.mul_assoc]
  have h4 : S1 * B2 * 2 < F * S2 * B2 * 2 := by omega
  exact (nat_mul_lt_mul_right_iff (by decide : 0 < 2)).mp h4

theorem powScale_roundRatio_scaled_bounds (f : IeeeFormat) (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    let e := ratioExponent n d
    let exponent := max e f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    scaled.1 < 2 ^ (f.fractionBits + 1) * scaled.2 ∧
      (f.minExponent ≤ e → 2 ^ f.fractionBits * scaled.2 ≤ scaled.1) ∧
      (e < f.minExponent → scaled.1 < 2 ^ f.fractionBits * scaled.2) := by
  intro e exponent scaled
  obtain ⟨hb1, hb2⟩ := powScale_neg_ratioExponent_bounds n d hn hd
  have hde : 0 < (powScale n d (-e)).2 := powScale_snd_pos_gen n d hd (-e)
  have hdse : 0 < (powScale n d ((f.fractionBits : Int) - e)).2 :=
    powScale_snd_pos_gen n d hd ((f.fractionBits : Int) - e)
  have hcross1 := powScale_diff_cross n d (-e) ((f.fractionBits : Int) - e) (by omega)
  have hto1 : (((f.fractionBits : Int) - e) - (-e)).toNat = f.fractionBits := by omega
  rw [hto1] at hcross1
  have hse_lo : 2 ^ f.fractionBits * (powScale n d ((f.fractionBits : Int) - e)).2 ≤
      (powScale n d ((f.fractionBits : Int) - e)).1 :=
    scale_lo_helper hde hb1 hcross1
  have hse_hi : (powScale n d ((f.fractionBits : Int) - e)).1 <
      2 ^ (f.fractionBits + 1) * (powScale n d ((f.fractionBits : Int) - e)).2 := by
    rw [Nat.pow_succ]
    exact scale_hi_helper hde hb2 hdse hcross1 (Nat.two_pow_pos _)
  by_cases hme : f.minExponent ≤ e
  · have hexp : exponent = e := by simp only [exponent]; omega
    have hsc : scaled = powScale n d ((f.fractionBits : Int) - e) := by
      simp only [scaled, hexp]
    refine ⟨by rw [hsc]; exact hse_hi, fun _ => by rw [hsc]; exact hse_lo, fun hlt => by omega⟩
  · have hexp : exponent = f.minExponent := by simp only [exponent]; omega
    have hcross2 := powScale_diff_cross n d ((f.fractionBits : Int) - exponent)
      ((f.fractionBits : Int) - e) (by omega)
    have hge1 : 1 ≤ (((f.fractionBits : Int) - e) - ((f.fractionBits : Int) - exponent)).toNat := by
      omega
    have hpow2 :
        2 ≤ 2 ^ (((f.fractionBits : Int) - e) - ((f.fractionBits : Int) - exponent)).toNat :=
      two_pow_le_two_pow hge1
    have hse_hi' : (powScale n d ((f.fractionBits : Int) - e)).1 <
        2 ^ f.fractionBits * 2 * (powScale n d ((f.fractionBits : Int) - e)).2 := by
      rwa [Nat.pow_succ] at hse_hi
    have hlt_fb : scaled.1 < 2 ^ f.fractionBits * scaled.2 :=
      scale_sub_helper hdse hpow2 hcross2 hse_hi' (powScale_snd_pos_gen n d hd _)
    have hlt_fb1 : scaled.1 < 2 ^ (f.fractionBits + 1) * scaled.2 := by
      have : 2 ^ (f.fractionBits + 1) * scaled.2 =
          2 ^ f.fractionBits * scaled.2 + 2 ^ f.fractionBits * scaled.2 := by
        rw [Nat.pow_succ, Nat.mul_right_comm, Nat.mul_two]
      omega
    exact ⟨hlt_fb1, fun hge => by omega, fun _ => hlt_fb⟩

theorem roundQuotient_bounds (mode : RoundingMode) (a b : Nat) :
    a / b ≤ roundQuotient mode a b ∧ roundQuotient mode a b ≤ a / b + 1 := by
  cases mode <;>
    simp only [roundQuotient, roundQuotientTiesToEven, roundQuotientHalfAwayFromZero] <;>
    split <;>
    first | exact ⟨Nat.le_succ _, Nat.le_refl _⟩ | exact ⟨Nat.le_refl _, Nat.le_succ _⟩

theorem roundQuotient_le_of_lt_mul (mode : RoundingMode) (a b M : Nat) (_hb : 0 < b)
    (h : a < M * b) : roundQuotient mode a b ≤ M := by
  have hdiv : a / b < M := nat_div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
  have := (roundQuotient_bounds mode a b).2
  omega

theorem roundQuotient_ge_of_mul_le (mode : RoundingMode) (a b M : Nat) (hb : 0 < b)
    (h : M * b ≤ a) : M ≤ roundQuotient mode a b := by
  have hdiv : M ≤ a / b := (Nat.le_div_iff_mul_le hb).mpr h
  have := (roundQuotient_bounds mode a b).1
  omega

theorem int_le_max_right (a b : Int) : b ≤ max a b := by omega

theorem int_max_eq_right {a b : Int} (h : ¬ b ≤ a) : max a b = b := by omega

/-- **Unreachability of `inconsistentRounding` (`preferredNaNBits`) in
`roundRatioBits`**: for every rounding mode, format `f`, sign `neg`, numerator
`n`, and positive denominator `0 < d`, `roundRatioBits mode f neg n d` is an
in-width bit pattern (`< 2 ^ f.width`) that never decodes to NaN
(`isNaNBits = false`). -/
theorem roundRatioBits_valid_and_not_nan (mode : RoundingMode) (f : IeeeFormat) (neg : Bool)
    (n d : Nat) (hd : 0 < d) :
    roundRatioBits mode f neg n d < 2 ^ f.width ∧
      isNaNBits f (roundRatioBits mode f neg n d) = false := by
  have hd0 : d ≠ 0 := by omega
  have hmaxE := IeeeFormat.two_bias_lt f
  have hnez := IeeeFormat.max_exp_ne_zero f
  by_cases hn0 : n = 0
  · subst hn0
    have hz : roundRatioBits mode f neg 0 d = encodeBits f neg 0 0 := by
      simp [roundRatioBits, hd0, zeroBits, encodeBits]
    rw [hz]
    refine ⟨encodeBits_lt f neg 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _), ?_⟩
    unfold isNaNBits
    rw [decodeBits_encodeBits f neg 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _),
      if_neg' hnez, if_pos' rfl, if_pos' rfl]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    obtain ⟨hhi, hlo_ge, hlt_sub⟩ := powScale_roundRatio_scaled_bounds f n d hn hd
    clear hlt_sub
    generalize hexp : max (ratioExponent n d) f.minExponent = exponent at hhi hlo_ge
    generalize hsc : powScale n d ((f.fractionBits : Int) - exponent) = scaled at hhi hlo_ge
    have hds : 0 < scaled.2 := by rw [← hsc]; exact powScale_snd_pos_gen n d hd _
    have hsig_le : roundQuotient mode scaled.1 scaled.2 ≤ 2 ^ (f.fractionBits + 1) :=
      roundQuotient_le_of_lt_mul mode scaled.1 scaled.2 _ hds hhi
    unfold roundRatioBits
    simp only [hd0, hn0, ↓reduceIte, hexp, hsc]
    have hinf_lt : infBits f neg < 2 ^ f.width := by
      simp only [infBits]
      have hE : 2 ^ f.exponentBits - 1 < 2 ^ f.exponentBits :=
        Nat.sub_lt (Nat.two_pow_pos _) (by decide)
      exact encodeBits_lt f neg _ 0 hE (Nat.two_pow_pos _)
    have hinf_nan : isNaNBits f (infBits f neg) = false := by
      simp only [infBits, isNaNBits]
      have hE : 2 ^ f.exponentBits - 1 < 2 ^ f.exponentBits :=
        Nat.sub_lt (Nat.two_pow_pos _) (by decide)
      rw [decodeBits_encodeBits f neg _ 0 hE (Nat.two_pow_pos _), if_pos' rfl, if_pos' rfl]
    by_cases hov1 : exponent > f.maxExponent
    · rw [if_pos' hov1]; exact ⟨hinf_lt, hinf_nan⟩
    · rw [if_neg' hov1]
      generalize hsig : roundQuotient mode scaled.1 scaled.2 = sig at hsig_le
      have hmin_le : f.minExponent ≤ exponent := by
        rw [← hexp]; exact int_le_max_right _ _
      by_cases hcarry : 2 ^ (f.fractionBits + 1) ≤ sig
      · clear hlo_ge hexp hsc hsig
        have hsig_eq : sig = 2 ^ (f.fractionBits + 1) := by omega
        have hdiv2 : sig / 2 = 2 ^ f.fractionBits := by
          rw [hsig_eq, Nat.pow_succ]; omega
        simp only [hcarry, decide_true, ↓reduceIte, hdiv2]
        by_cases hov2 : exponent + 1 > f.maxExponent
        · rw [if_pos' hov2]; exact ⟨hinf_lt, hinf_nan⟩
        · rw [if_neg' hov2]
          have hlt_false : ¬ (2 ^ f.fractionBits < 2 ^ f.fractionBits) := Nat.lt_irrefl _
          have hge_false : ¬ (2 ^ (f.fractionBits + 1) ≤ 2 ^ f.fractionBits) := by
            have := two_pow_lt_two_pow (Nat.lt_succ_self f.fractionBits); omega
          rw [if_neg' hlt_false, if_neg' hge_false, Nat.sub_self]
          simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hmin_le hov2
          have hE : (exponent + 1 + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by omega
          have hEne : ¬ ((exponent + 1 + (f.bias : Int)).toNat = 2 ^ f.exponentBits - 1) := by omega
          have hE0 : ¬ ((exponent + 1 + (f.bias : Int)).toNat = 0) := by omega
          refine ⟨encodeBits_lt f neg _ 0 hE (Nat.two_pow_pos _), ?_⟩
          unfold isNaNBits
          rw [decodeBits_encodeBits f neg _ 0 hE (Nat.two_pow_pos _), if_neg' hEne, if_neg' hE0]
      · simp only [hcarry, decide_false, Bool.false_eq_true, ↓reduceIte, hov1]
        by_cases hsub : sig < 2 ^ f.fractionBits
        · rw [if_pos' hsub]
          have hexp_min : exponent = f.minExponent := by
            by_cases hge : f.minExponent ≤ ratioExponent n d
            · have hge_sig : 2 ^ f.fractionBits ≤ sig := by
                rw [← hsig]
                exact roundQuotient_ge_of_mul_le mode scaled.1 scaled.2 _ hds (hlo_ge hge)
              clear hlo_ge hexp hsc hsig; omega
            · rw [← hexp]; exact int_max_eq_right hge
          rw [if_pos' hexp_min]
          refine ⟨encodeBits_lt f neg 0 sig (Nat.two_pow_pos _) hsub, ?_⟩
          unfold isNaNBits
          rw [decodeBits_encodeBits f neg 0 sig (Nat.two_pow_pos _) hsub, if_neg' hnez, if_pos' rfl]
          by_cases hsig0 : sig = 0 <;> simp [hsig0]
        · clear hlo_ge hexp hsc hsig
          rw [if_neg' hsub]
          simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hmin_le hov1
          have hE : (exponent + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by omega
          have hEne : ¬ ((exponent + (f.bias : Int)).toNat = 2 ^ f.exponentBits - 1) := by omega
          have hE0 : ¬ ((exponent + (f.bias : Int)).toNat = 0) := by omega
          have hF : sig - 2 ^ f.fractionBits < 2 ^ f.fractionBits := by
            have : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by
              rw [Nat.pow_succ]; omega
            omega
          refine ⟨encodeBits_lt f neg _ _ hE hF, ?_⟩
          unfold isNaNBits
          rw [decodeBits_encodeBits f neg _ _ hE hF, if_neg' hEne, if_neg' hE0]

/-- **Float-level `<= 0.5 ULP` + even-tie theorem for `roundRatioTiesToEven`**:
for every format `f`, sign `neg`, and positive rational `n / d` (`0 < n`,
`0 < d`), let `exponent := max (ratioExponent n d) f.minExponent`,
`scaled := powScale n d ((f.fractionBits : Int) - exponent)` (so
`scaled.1 / scaled.2 = (n / d) / 2 ^ (exponent - f.fractionBits)`), and
`sig := roundQuotientTiesToEven scaled.1 scaled.2`. Then:
1. `sig` is within `0.5` ULP of `n / d` at quantum
   `2 ^ (exponent - f.fractionBits)`:
   `2 * |sig * scaled.2 - scaled.1| ≤ scaled.2`, with `sig % 2 = 0` on ties;
2. Whenever `roundRatioTiesToEven f neg n d` does not overflow to `.inf neg`,
   the decoded float `decodeBits f (roundRatioTiesToEven f neg n d)` has the
   exact rational value `(-1)^neg * sig * 2 ^ (exponent - f.fractionBits)`
   (across normal, subnormal, gradual-underflow-to-zero, and
   carry-out-to-`exponent + 1` regimes). -/
theorem roundRatioTiesToEven_float_half_ulp (f : IeeeFormat) (neg : Bool) (n d : Nat)
    (hn : 0 < n) (hd : 0 < d) :
    let exponent := max (ratioExponent n d) f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    let sig := roundQuotientTiesToEven scaled.1 scaled.2
    2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2 ∧
      (2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs = scaled.2 →
        sig % 2 = 0) ∧
      (decodeBits f (roundRatioTiesToEven f neg n d) ≠ .inf neg →
        floatKindSameValue (decodeBits f (roundRatioTiesToEven f neg n d))
          (if sig = 0 then .zero neg
           else .finite neg (powScale sig 1 (exponent - f.fractionBits)).1
             (powScale sig 1 (exponent - f.fractionBits)).2)) := by
  dsimp only
  have hd0 : d ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hmaxE := IeeeFormat.two_bias_lt f
  have hnez := IeeeFormat.max_exp_ne_zero f
  obtain ⟨hhi, hlo_ge, hlt_sub⟩ := powScale_roundRatio_scaled_bounds f n d hn hd
  clear hlt_sub
  generalize hexp : max (ratioExponent n d) f.minExponent = exponent at hhi hlo_ge
  generalize hsc : powScale n d ((f.fractionBits : Int) - exponent) = scaled at hhi hlo_ge
  have hds : 0 < scaled.2 := by rw [← hsc]; exact powScale_snd_pos_gen n d hd _
  have hsig_le : roundQuotient .tiesToEven scaled.1 scaled.2 ≤ 2 ^ (f.fractionBits + 1) :=
    roundQuotient_le_of_lt_mul .tiesToEven scaled.1 scaled.2 _ hds hhi
  simp only [roundQuotient] at hsig_le
  refine ⟨roundQuotientTiesToEven_half_ulp scaled.1 scaled.2 hds,
    roundQuotientTiesToEven_tie_even scaled.1 scaled.2 hds, ?_⟩
  intro hno_inf
  have hinf_dec : decodeBits f (infBits f neg) = .inf neg := by
    simp only [infBits]
    have hE : 2 ^ f.exponentBits - 1 < 2 ^ f.exponentBits :=
      Nat.sub_lt (Nat.two_pow_pos _) (by decide)
    rw [decodeBits_encodeBits f neg _ 0 hE (Nat.two_pow_pos _), if_pos' rfl, if_pos' rfl]
  rw [← roundRatioBits_tiesToEven] at hno_inf ⊢
  unfold roundRatioBits at hno_inf ⊢
  simp only [hd0, hn0, ↓reduceIte, hexp, hsc, roundQuotient] at hno_inf ⊢
  by_cases hov1 : exponent > f.maxExponent
  · rw [if_pos' hov1, hinf_dec] at hno_inf; exact absurd rfl hno_inf
  · rw [if_neg' hov1] at hno_inf ⊢
    generalize hsig : roundQuotientTiesToEven scaled.1 scaled.2 = sig at hsig_le hno_inf ⊢
    have hmin_le : f.minExponent ≤ exponent := by
      rw [← hexp]; exact int_le_max_right _ _
    by_cases hcarry : 2 ^ (f.fractionBits + 1) ≤ sig
    · clear hlo_ge hexp hsc hsig
      have hsig_eq : sig = 2 ^ (f.fractionBits + 1) := by clear hno_inf; omega
      have hsig_nz : sig ≠ 0 := by
        have := Nat.two_pow_pos (f.fractionBits + 1); clear hno_inf; omega
      have hdiv2 : sig / 2 = 2 ^ f.fractionBits := by
        rw [hsig_eq, Nat.pow_succ]; clear hno_inf; omega
      simp only [hcarry, decide_true, ↓reduceIte, hdiv2] at hno_inf ⊢
      by_cases hov2 : exponent + 1 > f.maxExponent
      · rw [if_pos' hov2, hinf_dec] at hno_inf; exact absurd rfl hno_inf
      · clear hno_inf
        rw [if_neg' hov2]
        have hlt_false : ¬ (2 ^ f.fractionBits < 2 ^ f.fractionBits) := Nat.lt_irrefl _
        have hge_false : ¬ (2 ^ (f.fractionBits + 1) ≤ 2 ^ f.fractionBits) := by
          have := two_pow_lt_two_pow (Nat.lt_succ_self f.fractionBits); omega
        rw [if_neg' hlt_false, if_neg' hge_false, Nat.sub_self, if_neg' hsig_nz]
        simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hmin_le hov2
        have hE : (exponent + 1 + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by omega
        have hEne : ¬ ((exponent + 1 + (f.bias : Int)).toNat = 2 ^ f.exponentBits - 1) := by omega
        have hE0 : ¬ ((exponent + 1 + (f.bias : Int)).toNat = 0) := by omega
        rw [decodeBits_encodeBits f neg _ 0 hE (Nat.two_pow_pos _), if_neg' hEne, if_neg' hE0,
          Nat.add_zero]
        have ht : (((exponent + 1 + (f.bias : Int)).toNat : Nat) : Int) - f.bias - f.fractionBits =
            exponent + 1 - f.fractionBits := by omega
        rw [ht]
        have hcross := powScale_shift_cross (2 ^ f.fractionBits) 1 (exponent + 1 - f.fractionBits)
        have hmul : 2 ^ f.fractionBits * 2 ^ 1 = sig := by rw [hsig_eq, Nat.pow_succ]; rfl
        have hsub : exponent + 1 - (f.fractionBits : Int) - ((1 : Nat) : Int) =
            exponent - f.fractionBits := by omega
        rw [hmul, hsub] at hcross
        exact ⟨rfl, hcross.symm, powScale_snd_pos _ _, powScale_snd_pos _ _⟩
    · clear hno_inf
      simp only [hcarry, decide_false, Bool.false_eq_true, ↓reduceIte, hov1]
      by_cases hsub : sig < 2 ^ f.fractionBits
      · rw [if_pos' hsub]
        have hexp_min : exponent = f.minExponent := by
          by_cases hge : f.minExponent ≤ ratioExponent n d
          · have hge_sig : 2 ^ f.fractionBits ≤ sig := by
              rw [← hsig]
              exact roundQuotient_ge_of_mul_le .tiesToEven scaled.1 scaled.2 _ hds (hlo_ge hge)
            clear hlo_ge hexp hsc hsig; omega
          · rw [← hexp]; exact int_max_eq_right hge
        rw [if_pos' hexp_min, decodeBits_encodeBits f neg 0 sig (Nat.two_pow_pos _) hsub,
          if_neg' hnez, if_pos' rfl]
        by_cases hsig0 : sig = 0
        · rw [if_pos' hsig0, if_pos' hsig0]; rfl
        · rw [if_neg' hsig0, if_neg' hsig0, hexp_min]
          exact ⟨rfl, rfl, powScale_snd_pos _ _, powScale_snd_pos _ _⟩
      · clear hlo_ge hexp hsc hsig
        rw [if_neg' hsub]
        have hsig_ge : 2 ^ f.fractionBits ≤ sig := Nat.le_of_not_lt hsub
        have hsig_nz : sig ≠ 0 := by have := Nat.two_pow_pos f.fractionBits; omega
        rw [if_neg' hsig_nz]
        simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hmin_le hov1
        have hE : (exponent + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by omega
        have hEne : ¬ ((exponent + (f.bias : Int)).toNat = 2 ^ f.exponentBits - 1) := by omega
        have hE0 : ¬ ((exponent + (f.bias : Int)).toNat = 0) := by omega
        have hF : sig - 2 ^ f.fractionBits < 2 ^ f.fractionBits := by
          have : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by
            rw [Nat.pow_succ]; omega
          omega
        rw [decodeBits_encodeBits f neg _ _ hE hF, if_neg' hEne, if_neg' hE0,
          Nat.add_sub_cancel' hsig_ge]
        have ht : (((exponent + (f.bias : Int)).toNat : Nat) : Int) - f.bias - f.fractionBits =
            exponent - f.fractionBits := by omega
        rw [ht]
        exact ⟨rfl, rfl, powScale_snd_pos _ _, powScale_snd_pos _ _⟩

/-- **Correct rounding of `roundRatioTiesToEven`** (strengthens
`roundRatioTiesToEven_float_half_ulp` by pinning the rounding quantum to the
IEEE-754 ULP): for `0 < n`, `0 < d`, with `e := ratioExponent n d`,
`exponent := max e minExponent`, `scaled := powScale n d (fb - exponent)`
(`scaled.1 / scaled.2 = (n/d) / 2^(exponent - fb)`) and
`sig := roundQuotientTiesToEven scaled.1 scaled.2`:
1. `e = ⌊log2 (n/d)⌋`, i.e. `1 ≤ (n/d) / 2^e < 2`;
2. the quantum `2^(exponent - fb)` is the ULP of the binade of `n/d`:
   `scaled < 2^(fb+1)`, and `2^fb ≤ scaled` whenever `n/d` is in the normal
   range (`minExponent ≤ e`; otherwise `exponent = minExponent` is the subnormal
   quantum);
3. `sig` is within `½` of `scaled`, resolving exact ties to an even significand;
4. unless the result overflows to `±∞`, it decodes to exactly
   `(-1)^neg * sig * 2^(exponent - fb)`. -/
theorem roundRatioTiesToEven_correctly_rounded (f : IeeeFormat) (neg : Bool) (n d : Nat)
    (hn : 0 < n) (hd : 0 < d) :
    let e := ratioExponent n d
    let exponent := max e f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    let sig := roundQuotientTiesToEven scaled.1 scaled.2
    ((powScale n d (-e)).2 ≤ (powScale n d (-e)).1 ∧
      (powScale n d (-e)).1 < 2 * (powScale n d (-e)).2) ∧
    scaled.1 < 2 ^ (f.fractionBits + 1) * scaled.2 ∧
    (f.minExponent ≤ e → 2 ^ f.fractionBits * scaled.2 ≤ scaled.1) ∧
    2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2 ∧
    (2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs = scaled.2 → sig % 2 = 0) ∧
    (decodeBits f (roundRatioTiesToEven f neg n d) ≠ .inf neg →
      floatKindSameValue (decodeBits f (roundRatioTiesToEven f neg n d))
        (if sig = 0 then .zero neg
         else .finite neg (powScale sig 1 (exponent - f.fractionBits)).1
           (powScale sig 1 (exponent - f.fractionBits)).2)) := by
  intro e exponent scaled sig
  have hb := powScale_roundRatio_scaled_bounds f n d hn hd
  have hh := roundRatioTiesToEven_float_half_ulp f neg n d hn hd
  exact ⟨powScale_neg_ratioExponent_bounds n d hn hd, hb.1, hb.2.1, hh.1, hh.2.1, hh.2.2⟩

/-- **Overflow to `±∞`** (sufficiency): `roundRatioTiesToEven` returns `±∞` when
the exact value's binade exceeds `maxExponent`, or when it lies in the top
binade and rounds up to `2^(fb+1) * 2^(maxExponent - fb) = 2^(maxExponent + 1)`
(carry-out past the largest finite value, e.g. the `binary32` tie
`2^128 - 2^103`). -/
theorem roundRatioTiesToEven_overflow_of (f : IeeeFormat) (neg : Bool) (n d : Nat)
    (hn : 0 < n) (hd : 0 < d)
    (h : f.maxExponent < max (ratioExponent n d) f.minExponent ∨
      (max (ratioExponent n d) f.minExponent = f.maxExponent ∧
        roundQuotientTiesToEven
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).1
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).2 =
          2 ^ (f.fractionBits + 1))) :
    roundRatioTiesToEven f neg n d = infBits f neg := by
  have hd0 : d ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  rw [← roundRatioBits_tiesToEven]
  unfold roundRatioBits
  simp only [hd0, hn0, ↓reduceIte, roundQuotient]
  generalize hexp : max (ratioExponent n d) f.minExponent = exponent at h ⊢
  generalize hsc : powScale n d ((f.fractionBits : Int) - exponent) = scaled at h ⊢
  rcases h with h | ⟨he, hs⟩
  · rw [if_pos' h]
  · have hnot : ¬ (exponent > f.maxExponent) := by omega
    have hov : exponent + 1 > f.maxExponent := by omega
    rw [if_neg' hnot]
    simp only [hs, Nat.le_refl, decide_true, ↓reduceIte, if_pos' hov]

theorem decodeBits_zeroBits (f : IeeeFormat) (neg : Bool) :
    decodeBits f (zeroBits f neg) = .zero neg := by
  rw [zeroBits_eq_encodeBits,
    decodeBits_encodeBits f neg 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _),
    if_neg' (IeeeFormat.max_exp_ne_zero f), if_pos' rfl, if_pos' rfl]

theorem decodeBits_infBits (f : IeeeFormat) (neg : Bool) :
    decodeBits f (infBits f neg) = .inf neg := by
  simp only [infBits]
  have hE : 2 ^ f.exponentBits - 1 < 2 ^ f.exponentBits :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  rw [decodeBits_encodeBits f neg _ 0 hE (Nat.two_pow_pos _), if_pos' rfl, if_pos' rfl]

/-- **Necessary and sufficient (`↔`) overflow characterization for
`roundRatioTiesToEven`** (strengthens `roundRatioTiesToEven_overflow_of` to a
full biconditional): for `0 < n` and `0 < d`, `roundRatioTiesToEven f neg n d`
equals `infBits f neg` (and equivalently decodes to `.inf neg`) **if and only
if** the clamped binade `exponent := max (ratioExponent n d) f.minExponent`
exceeds `f.maxExponent`, or `exponent = f.maxExponent` and the rounded
significand carries out to `2 ^ (f.fractionBits + 1)`. -/
theorem roundRatioTiesToEven_overflow_iff (f : IeeeFormat) (neg : Bool) (n d : Nat)
    (hn : 0 < n) (hd : 0 < d) :
    let exponent := max (ratioExponent n d) f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    let sig := roundQuotientTiesToEven scaled.1 scaled.2
    (roundRatioTiesToEven f neg n d = infBits f neg ↔
      (f.maxExponent < exponent ∨ (exponent = f.maxExponent ∧ sig = 2 ^ (f.fractionBits + 1)))) ∧
    (decodeBits f (roundRatioTiesToEven f neg n d) = .inf neg ↔
      roundRatioTiesToEven f neg n d = infBits f neg) := by
  dsimp only
  have hnot_inf_of_not_ov :
      ¬ (f.maxExponent < max (ratioExponent n d) f.minExponent) →
      ¬ (max (ratioExponent n d) f.minExponent = f.maxExponent ∧
          roundQuotientTiesToEven
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).1
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).2 =
          2 ^ (f.fractionBits + 1)) →
      decodeBits f (roundRatioTiesToEven f neg n d) ≠ .inf neg := by
    intro hno1 hno2 hdec
    have hd0 : d ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have hmaxE := IeeeFormat.two_bias_lt f
    have hnez := IeeeFormat.max_exp_ne_zero f
    obtain ⟨hhi, hlo_ge, hlt_sub⟩ := powScale_roundRatio_scaled_bounds f n d hn hd
    clear hlt_sub
    generalize hexp : max (ratioExponent n d) f.minExponent = exponent at hhi hlo_ge hno1 hno2
    generalize hsc : powScale n d ((f.fractionBits : Int) - exponent) = scaled at hhi hlo_ge hno2
    have hds : 0 < scaled.2 := by rw [← hsc]; exact powScale_snd_pos_gen n d hd _
    have hsig_le : roundQuotient .tiesToEven scaled.1 scaled.2 ≤ 2 ^ (f.fractionBits + 1) :=
      roundQuotient_le_of_lt_mul .tiesToEven scaled.1 scaled.2 _ hds hhi
    simp only [roundQuotient] at hsig_le
    rw [← roundRatioBits_tiesToEven] at hdec
    unfold roundRatioBits at hdec
    simp only [hd0, hn0, ↓reduceIte, hexp, hsc, roundQuotient] at hdec
    rw [if_neg' hno1] at hdec
    generalize hsig : roundQuotientTiesToEven scaled.1 scaled.2 = sig at hsig_le hno2 hdec
    have hmin_le : f.minExponent ≤ exponent := by
      rw [← hexp]; exact int_le_max_right _ _
    by_cases hcarry : 2 ^ (f.fractionBits + 1) ≤ sig
    · clear hlo_ge hexp hsc hsig
      have hsig_eq : sig = 2 ^ (f.fractionBits + 1) := by clear hno2 hdec; omega
      have hexp_ne : exponent ≠ f.maxExponent := fun he => hno2 ⟨he, hsig_eq⟩
      clear hno2
      have hov2 : ¬ (exponent + 1 > f.maxExponent) := by clear hdec; omega
      have hdiv2 : sig / 2 = 2 ^ f.fractionBits := by rw [hsig_eq, Nat.pow_succ]; clear hdec; omega
      simp only [hcarry, decide_true, ↓reduceIte, hdiv2] at hdec
      rw [if_neg' hov2] at hdec
      have hlt_false : ¬ (2 ^ f.fractionBits < 2 ^ f.fractionBits) := Nat.lt_irrefl _
      have hge_false : ¬ (2 ^ (f.fractionBits + 1) ≤ 2 ^ f.fractionBits) := by
        have := two_pow_lt_two_pow (Nat.lt_succ_self f.fractionBits); clear hdec; omega
      rw [if_neg' hlt_false, if_neg' hge_false, Nat.sub_self] at hdec
      simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hmin_le hov2
      have hE : (exponent + 1 + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by clear hdec; omega
      have hEne : ¬ ((exponent + 1 + (f.bias : Int)).toNat = 2 ^ f.exponentBits - 1) := by
        clear hdec; omega
      have hE0 : ¬ ((exponent + 1 + (f.bias : Int)).toNat = 0) := by clear hdec; omega
      rw [decodeBits_encodeBits f neg _ 0 hE (Nat.two_pow_pos _), if_neg' hEne, if_neg' hE0] at hdec
      cases hdec
    · clear hno2
      simp only [hcarry, decide_false, Bool.false_eq_true, ↓reduceIte, hno1] at hdec
      by_cases hsub : sig < 2 ^ f.fractionBits
      · rw [if_pos' hsub] at hdec
        have hexp_min : exponent = f.minExponent := by
          by_cases hge : f.minExponent ≤ ratioExponent n d
          · have hge_sig : 2 ^ f.fractionBits ≤ sig := by
              rw [← hsig]
              exact roundQuotient_ge_of_mul_le .tiesToEven scaled.1 scaled.2 _ hds (hlo_ge hge)
            clear hlo_ge hexp hsc hsig hdec; omega
          · rw [← hexp]; exact int_max_eq_right hge
        rw [if_pos' hexp_min, decodeBits_encodeBits f neg 0 sig (Nat.two_pow_pos _) hsub,
          if_neg' hnez, if_pos' rfl] at hdec
        by_cases hsig0 : sig = 0 <;> simp [hsig0] at hdec
      · clear hlo_ge hexp hsc hsig
        rw [if_neg' hsub] at hdec
        simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hmin_le hno1
        have hE : (exponent + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by clear hdec; omega
        have hEne : ¬ ((exponent + (f.bias : Int)).toNat = 2 ^ f.exponentBits - 1) := by
          clear hdec; omega
        have hE0 : ¬ ((exponent + (f.bias : Int)).toNat = 0) := by clear hdec; omega
        have hF : sig - 2 ^ f.fractionBits < 2 ^ f.fractionBits := by
          have : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by
            rw [Nat.pow_succ]; clear hdec; omega
          clear hdec; omega
        rw [decodeBits_encodeBits f neg _ _ hE hF, if_neg' hEne, if_neg' hE0] at hdec
        cases hdec
  have hiff1 : roundRatioTiesToEven f neg n d = infBits f neg ↔
      (f.maxExponent < max (ratioExponent n d) f.minExponent ∨
        (max (ratioExponent n d) f.minExponent = f.maxExponent ∧
          roundQuotientTiesToEven
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).1
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).2 =
          2 ^ (f.fractionBits + 1))) := by
    constructor
    · intro heq
      have hdec : decodeBits f (roundRatioTiesToEven f neg n d) = .inf neg := by
        rw [heq, decodeBits_infBits]
      by_cases hov1 : f.maxExponent < max (ratioExponent n d) f.minExponent
      · exact Or.inl hov1
      · by_cases hov2 : max (ratioExponent n d) f.minExponent = f.maxExponent ∧
            roundQuotientTiesToEven
              (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).1
              (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).2 =
            2 ^ (f.fractionBits + 1)
        · exact Or.inr hov2
        · exact absurd hdec (hnot_inf_of_not_ov hov1 hov2)
    · exact roundRatioTiesToEven_overflow_of f neg n d hn hd
  refine ⟨hiff1, ?_⟩
  constructor
  · intro hdec
    apply hiff1.mpr
    by_cases hov1 : f.maxExponent < max (ratioExponent n d) f.minExponent
    · exact Or.inl hov1
    · by_cases hov2 : max (ratioExponent n d) f.minExponent = f.maxExponent ∧
          roundQuotientTiesToEven
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).1
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).2 =
          2 ^ (f.fractionBits + 1)
      · exact Or.inr hov2
      · exact absurd hdec (hnot_inf_of_not_ov hov1 hov2)
  · intro heq
    rw [heq, decodeBits_infBits]

/-- **Universal signed-zero & gradual-underflow sign preservation**:
1. `roundRatioBits mode f neg 0 d = zeroBits f neg` (decoding to `.zero neg`)
   for every `0 < d`;
2. Whenever `0 < n`, `0 < d`, and `roundQuotient mode scaled.1 scaled.2 = 0`
   (gradual underflow past the smallest subnormal),
   `roundRatioBits mode f neg n d = zeroBits f neg` and
   `decodeBits f (roundRatioBits mode f neg n d) = .zero neg` (preserving `-0.0`
   when `neg = true`);
3. `evalFloatToFloatRoundTiesToEven` preserves `.zero neg` and `.inf neg`
   (including their sign `neg`) across all source and destination formats;
4. Concrete negative-finite gradual-underflow canary: `-2^-150`
   (`0xB690_0000_0000_0000 : f64`) narrows to `-0.0` (`0x8000_0000 : f32`, never
   `+0.0`), while `-(2^-150 + 2^-202)` (`0xB690_0000_0000_0001 : f64`) narrows
   to negative smallest subnormal `0x8000_0001 : f32`. -/
theorem roundRatioBits_sign_and_underflow_zero_preserved :
    (∀ (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (d : Nat), 0 < d →
      roundRatioBits mode f neg 0 d = zeroBits f neg ∧
        decodeBits f (roundRatioBits mode f neg 0 d) = .zero neg) ∧
    (∀ (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (n d : Nat), 0 < n → 0 < d →
      let exponent := max (ratioExponent n d) f.minExponent
      let scaled := powScale n d ((f.fractionBits : Int) - exponent)
      roundQuotient mode scaled.1 scaled.2 = 0 →
      roundRatioBits mode f neg n d = zeroBits f neg ∧
        decodeBits f (roundRatioBits mode f neg n d) = .zero neg) ∧
    (∀ (src dst : IeeeFormat) (bits : Nat) (neg : Bool),
      decodeBits src bits = .zero neg →
      decodeBits dst (evalFloatToFloatRoundTiesToEven src dst bits) = .zero neg) ∧
    (∀ (src dst : IeeeFormat) (bits : Nat) (neg : Bool),
      decodeBits src bits = .inf neg →
      decodeBits dst (evalFloatToFloatRoundTiesToEven src dst bits) = .inf neg) ∧
    f64ToF32 0xB690000000000000#64 = 0x80000000#32 ∧
    f64ToF32 0xB690000000000001#64 = 0x80000001#32 := by
  refine ⟨?_, ?_, ?_, ?_, by decide +kernel, by decide +kernel⟩
  · intro mode f neg d hd
    have hd0 : d ≠ 0 := by omega
    have hz : roundRatioBits mode f neg 0 d = zeroBits f neg := by
      simp [roundRatioBits, hd0]
    rw [hz]
    exact ⟨rfl, decodeBits_zeroBits f neg⟩
  · intro mode f neg n d hn hd
    dsimp only
    intro hsig0
    have hd0 : d ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have hlo_ge := (powScale_roundRatio_scaled_bounds f n d hn hd).2.1
    generalize hexp : max (ratioExponent n d) f.minExponent = exponent at hlo_ge hsig0
    generalize hsc : powScale n d ((f.fractionBits : Int) - exponent) = scaled at hlo_ge hsig0
    have hds : 0 < scaled.2 := by rw [← hsc]; exact powScale_snd_pos_gen n d hd _
    have hexp_min : exponent = f.minExponent := by
      by_cases hge : f.minExponent ≤ ratioExponent n d
      · have hge_sig : 2 ^ f.fractionBits ≤ roundQuotient mode scaled.1 scaled.2 :=
          roundQuotient_ge_of_mul_le mode scaled.1 scaled.2 _ hds (hlo_ge hge)
        rw [hsig0] at hge_sig
        have := Nat.two_pow_pos f.fractionBits
        clear hlo_ge hexp hsc hds; omega
      · rw [← hexp]; exact int_max_eq_right hge
    have hov1 : ¬ (exponent > f.maxExponent) := by
      rw [hexp_min]
      cases f <;> decide
    have hcarry : ¬ (2 ^ (f.fractionBits + 1) ≤ 0) := by
      cases f <;> decide
    have hsub : 0 < 2 ^ f.fractionBits := Nat.two_pow_pos _
    have hr : roundRatioBits mode f neg n d = zeroBits f neg := by
      unfold roundRatioBits
      simp only [hd0, hn0, ↓reduceIte, hexp, hsc]
      rw [if_neg' hov1]
      simp only [hsig0, hcarry, decide_false, Bool.false_eq_true, ↓reduceIte, hov1]
      rw [if_pos' hsub, if_pos' hexp_min, ← zeroBits_eq_encodeBits]
    rw [hr]
    exact ⟨rfl, decodeBits_zeroBits f neg⟩
  · intro src dst bits neg h
    rw [← convertFloatBits_tiesToEven, convertFloatBits_of_zero _ _ _ _ _ h,
      decodeBits_zeroBits]
  · intro src dst bits neg h
    rw [← convertFloatBits_tiesToEven, convertFloatBits_of_inf _ _ _ _ _ h,
      decodeBits_infBits]

theorem floatToIntValue_of_denotesInt (k : FloatKind) (v lo hi : Int)
    (hlo : lo ≤ v) (hhi : v ≤ hi) (hd : floatKindDenotesInt k v) :
    floatToIntValue k lo hi = v := by
  cases k with
  | zero neg =>
    obtain ⟨rfl, _⟩ := hd
    rfl
  | finite neg n d =>
    obtain ⟨hd_pos, hn, hneg⟩ := hd
    have hdiv : n / d = v.natAbs := by
      rw [hn, Nat.mul_div_cancel _ hd_pos]
    simp only [floatToIntValue, truncRatio, clampInt, hdiv, hneg]
    by_cases hv : v < 0
    · simp only [hv, decide_true, ↓reduceIte]; omega
    · simp only [hv, decide_false, Bool.false_eq_true, ↓reduceIte]; omega
  | inf _ => cases hd
  | nan _ _ _ => cases hd

theorem encodeTwosComplement_intValueOfBits (signed : Bool) (w bits : Nat)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128) (hbits : bits < 2 ^ w) :
    (if signed = true then -((2 ^ (w - 1) : Nat) : Int) else 0) ≤ intValueOfBits signed w bits ∧
    intValueOfBits signed w bits ≤
      (if signed = true then ((2 ^ (w - 1) : Nat) : Int) - 1 else ((2 ^ w : Nat) : Int) - 1) ∧
    encodeTwosComplement w (intValueOfBits signed w bits) = bits := by
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> cases signed <;>
    simp only [intValueOfBits, encodeTwosComplement, Nat.reducePow, Nat.reduceSub,
      Bool.false_eq_true, ite_false, ite_true, true_and, false_and] at hbits ⊢ <;>
    (repeat' apply And.intro) <;>
    (try split) <;> omega

/-- **Universal `IntToFloat → FloatToInt` exact round-trip**:
1. For every integer target `t : FloatIntTarget`, pointer width
   `pw : FloatPtrWidth`, format `f`, and in-width bit pattern
   `bits < 2 ^ (t.bitWidth pw)`, whenever the integer value
   `v := intValueOfBits t.isSigned (t.bitWidth pw) bits` is exactly
   representable in `f` (`v.natAbs < 2 ^ (f.fractionBits + 1)`), casting `bits`
   to `f` via `evalIntToFloatRoundTiesToEven` and then back to `t` via
   `evalFloatToIntSaturating` recovers the exact original `ScalarInt`
   `⟨bits, (t.bitWidth pw) / 8⟩`;
2. In particular, for `f = .binary64` and `t = .signed .i32` or `.unsigned .u32`
   (32-bit signed and unsigned integers), `evalFloatToIntSaturating` is an
   unconditional left inverse of `evalIntToFloatRoundTiesToEven` on all
   `bits < 2 ^ 32`. -/
theorem evalFloatToIntSaturating_roundtrip_of_intToFloat :
    (∀ (t : FloatIntTarget) (pw : FloatPtrWidth) (f : IeeeFormat) (bits : Nat),
      bits < 2 ^ (t.bitWidth pw) →
      (intValueOfBits t.isSigned (t.bitWidth pw) bits).natAbs < 2 ^ (f.fractionBits + 1) →
      evalFloatToIntSaturating f
          (evalIntToFloatRoundTiesToEven t.isSigned (t.bitWidth pw) bits f) t pw =
        ⟨bits, (t.bitWidth pw) / 8⟩) ∧
    (∀ (pw : FloatPtrWidth) (bits : Nat), bits < 2 ^ 32 →
      evalFloatToIntSaturating .binary64
          (evalIntToFloatRoundTiesToEven true 32 bits .binary64) (.signed .i32) pw =
        ⟨bits, 4⟩ ∧
      evalFloatToIntSaturating .binary64
          (evalIntToFloatRoundTiesToEven false 32 bits .binary64) (.unsigned .u32) pw =
        ⟨bits, 4⟩) := by
  have hmain : ∀ (t : FloatIntTarget) (pw : FloatPtrWidth) (f : IeeeFormat) (bits : Nat),
      bits < 2 ^ (t.bitWidth pw) →
      (intValueOfBits t.isSigned (t.bitWidth pw) bits).natAbs < 2 ^ (f.fractionBits + 1) →
      evalFloatToIntSaturating f
          (evalIntToFloatRoundTiesToEven t.isSigned (t.bitWidth pw) bits f) t pw =
        ⟨bits, (t.bitWidth pw) / 8⟩ := by
    intro t pw f bits hbits hrep
    have hw := FloatIntTarget.bitWidth_cases t pw
    obtain ⟨hlo, hhi, henc⟩ :=
      encodeTwosComplement_intValueOfBits t.isSigned (t.bitWidth pw) bits hw hbits
    have hden := evalIntToFloatRoundTiesToEven_exact t.isSigned (t.bitWidth pw) bits f hrep
    have hf2i := floatToIntValue_of_denotesInt
      (decodeBits f (evalIntToFloatRoundTiesToEven t.isSigned (t.bitWidth pw) bits f))
      (intValueOfBits t.isSigned (t.bitWidth pw) bits) (t.minValue pw) (t.maxValue pw)
      (by unfold FloatIntTarget.minValue; exact hlo)
      (by unfold FloatIntTarget.maxValue; exact hhi) hden
    unfold evalFloatToIntSaturating
    dsimp only
    rw [hf2i, henc]
  refine ⟨hmain, fun pw bits hbits => ?_⟩
  have h1 := hmain (.signed .i32) pw .binary64 bits
    (by cases pw <;> exact hbits)
    (by
      simp only [FloatIntTarget.isSigned, FloatIntTarget.bitWidth, IntTy.bitWidth, intValueOfBits,
        IeeeFormat.fractionBits, Nat.reducePow, Nat.reduceSub, true_and]
      split <;> omega)
  have h2 := hmain (.unsigned .u32) pw .binary64 bits
    (by cases pw <;> exact hbits)
    (by
      simp only [FloatIntTarget.isSigned, FloatIntTarget.bitWidth, UintTy.bitWidth, intValueOfBits,
        IeeeFormat.fractionBits, Nat.reducePow, Nat.reduceSub, Bool.false_eq_true, false_and,
        ↓reduceIte]
      omega)
  cases pw <;> exact ⟨h1, h2⟩

theorem clampInt_monotone (lo hi v₁ v₂ : Int) (hv : v₁ ≤ v₂) :
    clampInt lo hi v₁ ≤ clampInt lo hi v₂ := by
  unfold clampInt; omega

theorem truncRatio_monotone_nonneg {n₁ d₁ n₂ d₂ : Nat} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hle : n₁ * d₂ ≤ n₂ * d₁) : n₁ / d₁ ≤ n₂ / d₂ := by
  have h1 : (n₁ / d₁) * d₁ ≤ n₁ := Nat.div_mul_le_self n₁ d₁
  have h2 : (n₁ / d₁) * d₁ * d₂ ≤ n₂ * d₁ :=
    Nat.le_trans (Nat.mul_le_mul_right d₂ h1) hle
  have h3 : (n₁ / d₁) * d₂ * d₁ ≤ n₂ * d₁ := by
    rwa [Nat.mul_right_comm (n₁ / d₁) d₁ d₂] at h2
  have h4 : (n₁ / d₁) * d₂ ≤ n₂ := (Nat.mul_le_mul_right_iff hd₁).mp h3
  exact (Nat.le_div_iff_mul_le hd₂).mpr h4

/-- **Universal monotonicity of `floatToIntValue` & `clampInt`**:
1. `clampInt lo hi` is monotone
   (`v₁ ≤ v₂ → clampInt lo hi v₁ ≤ clampInt lo hi v₂`);
2. For any two finite rationals `(-1)^neg₁ * (n₁ / d₁)` and
   `(-1)^neg₂ * (n₂ / d₂)` (`0 < d₁`, `0 < d₂`) ordered in the rational order
   (`neg₁ = true ∧ neg₂ = false`, or
   `neg₁ = false ∧ neg₂ = false ∧ n₁ * d₂ ≤ n₂ * d₁`, or
   `neg₁ = true ∧ neg₂ = true ∧ n₂ * d₁ ≤ n₁ * d₂`), both `truncRatio` and
   `floatToIntValue` are monotone
   (`truncRatio neg₁ n₁ d₁ ≤ truncRatio neg₂ n₂ d₂` and
   `floatToIntValue (.finite neg₁ n₁ d₁) lo hi ≤`
   `floatToIntValue (.finite neg₂ n₂ d₂) lo hi`);
3. For every non-NaN `k : FloatKind` and `lo ≤ 0 ≤ hi`,
   `floatToIntValue (.inf true) lo hi ≤ floatToIntValue k lo hi` and
   `floatToIntValue k lo hi ≤ floatToIntValue (.inf false) lo hi`. -/
theorem floatToIntValue_monotone :
    (∀ (lo hi v₁ v₂ : Int), v₁ ≤ v₂ → clampInt lo hi v₁ ≤ clampInt lo hi v₂) ∧
    (∀ (lo hi : Int) (neg₁ neg₂ : Bool) (n₁ d₁ n₂ d₂ : Nat),
      0 < d₁ → 0 < d₂ →
      ((neg₁ = true ∧ neg₂ = false) ∨
       (neg₁ = false ∧ neg₂ = false ∧ n₁ * d₂ ≤ n₂ * d₁) ∨
       (neg₁ = true ∧ neg₂ = true ∧ n₂ * d₁ ≤ n₁ * d₂)) →
      truncRatio neg₁ n₁ d₁ ≤ truncRatio neg₂ n₂ d₂ ∧
      floatToIntValue (.finite neg₁ n₁ d₁) lo hi ≤
        floatToIntValue (.finite neg₂ n₂ d₂) lo hi) ∧
    (∀ (lo hi : Int) (k : FloatKind),
      lo ≤ 0 → 0 ≤ hi →
      (match k with | .nan _ _ _ => false | _ => true) = true →
      floatToIntValue (.inf true) lo hi ≤ floatToIntValue k lo hi ∧
      floatToIntValue k lo hi ≤ floatToIntValue (.inf false) lo hi) := by
  refine ⟨clampInt_monotone, ?_, ?_⟩
  · intro lo hi neg₁ neg₂ n₁ d₁ n₂ d₂ hd₁ hd₂ hord
    have htr : truncRatio neg₁ n₁ d₁ ≤ truncRatio neg₂ n₂ d₂ := by
      rcases hord with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hle⟩ | ⟨rfl, rfl, hle⟩
      · simp only [truncRatio, ↓reduceIte, Bool.false_eq_true]
        have hq1 : 0 ≤ ((n₁ / d₁ : Nat) : Int) := Int.natCast_nonneg _
        have hq2 : 0 ≤ ((n₂ / d₂ : Nat) : Int) := Int.natCast_nonneg _
        omega
      · simp only [truncRatio, Bool.false_eq_true, ↓reduceIte]
        have := truncRatio_monotone_nonneg hd₁ hd₂ hle; omega
      · simp only [truncRatio, ↓reduceIte]
        have := truncRatio_monotone_nonneg hd₂ hd₁ hle; omega
    exact ⟨htr, clampInt_monotone lo hi _ _ htr⟩
  · intro lo hi k h0 h1 hnotnan
    obtain ⟨hlo, hhi⟩ := floatToIntValue_mem k lo hi h0 h1
    simp only [floatToIntValue, ↓reduceIte, Bool.false_eq_true]
    exact ⟨hlo, hhi⟩

/-! ### Soundness bundles -/

/-- **`evalIntToFloatRoundTiesToEven_sound`**: (1) every representable integer
`|v| < 2^(fb+1)` converts exactly (universal); (2) every `i32` / `u32` converts
to `binary64` losslessly (universal); (3) the `roundTiesToEven` core of
`roundRatioTiesToEven` is within `½` ULP of the exact quotient and resolves
exact ties to an even significand, and at the float level `roundRatioTiesToEven`
never produces NaN (`inconsistentRounding` is unreachable) and every
non-overflowing result decodes to `sig * 2 ^ (exponent - fb)` within `½` ULP;
(4) `u128::MAX` and the exact tie `2^128 - 2^103` overflow to `+∞` in
`binary32`, while `2^128 - 2^103 - 1` rounds down to `f32::MAX`; (5) every
int-to-float cast *is* `roundRatioTiesToEven` of the exact integer (so
`roundRatioTiesToEven_correctly_rounded` applies verbatim). -/
theorem evalIntToFloatRoundTiesToEven_sound :
    (∀ (signed : Bool) (w bits : Nat) (dst : IeeeFormat),
      (intValueOfBits signed w bits).natAbs < 2 ^ (dst.fractionBits + 1) →
      floatKindDenotesInt (decodeBits dst (evalIntToFloatRoundTiesToEven signed w bits dst))
        (intValueOfBits signed w bits)) ∧
    (∀ (signed : Bool) (bits : Nat),
      floatKindDenotesInt
        (decodeBits .binary64 (evalIntToFloatRoundTiesToEven signed 32 bits .binary64))
        (intValueOfBits signed 32 bits)) ∧
    (∀ n d : Nat, 0 < d →
      2 * (((roundQuotientTiesToEven n d * d : Nat) : Int) - (n : Int)).natAbs ≤ d) ∧
    (∀ n d : Nat, 0 < d →
      2 * (((roundQuotientTiesToEven n d * d : Nat) : Int) - (n : Int)).natAbs = d →
      roundQuotientTiesToEven n d % 2 = 0) ∧
    (∀ (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (n d : Nat), 0 < d →
      roundRatioBits mode f neg n d < 2 ^ f.width ∧
        isNaNBits f (roundRatioBits mode f neg n d) = false) ∧
    (∀ (f : IeeeFormat) (neg : Bool) (n d : Nat), 0 < n → 0 < d →
      let exponent := max (ratioExponent n d) f.minExponent
      let scaled := powScale n d ((f.fractionBits : Int) - exponent)
      let sig := roundQuotientTiesToEven scaled.1 scaled.2
      2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2 ∧
        (2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs = scaled.2 →
          sig % 2 = 0) ∧
        (decodeBits f (roundRatioTiesToEven f neg n d) ≠ .inf neg →
          floatKindSameValue (decodeBits f (roundRatioTiesToEven f neg n d))
            (if sig = 0 then .zero neg
             else .finite neg (powScale sig 1 (exponent - f.fractionBits)).1
               (powScale sig 1 (exponent - f.fractionBits)).2))) ∧
    (∀ (signed : Bool) (w bits : Nat) (dst : IeeeFormat),
      evalIntToFloatRoundTiesToEven signed w bits dst =
        roundRatioTiesToEven dst (decide (intValueOfBits signed w bits < 0))
          (intValueOfBits signed w bits).natAbs 1) ∧
    evalIntToFloatRoundTiesToEven false 128 (2 ^ 128 - 1) .binary32 = 0x7F800000 ∧
    evalIntToFloatRoundTiesToEven false 128 (2 ^ 128 - 2 ^ 103) .binary32 = 0x7F800000 ∧
    evalIntToFloatRoundTiesToEven false 128 (2 ^ 128 - 2 ^ 103 - 1) .binary32 = 0x7F7FFFFF :=
  ⟨evalIntToFloatRoundTiesToEven_exact, evalIntToFloat_i32_u32_to_f64_exact,
   roundQuotientTiesToEven_half_ulp, roundQuotientTiesToEven_tie_even,
   roundRatioBits_valid_and_not_nan, roundRatioTiesToEven_float_half_ulp,
   fun _ _ _ _ => rfl,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **`evalFloatToFloatRoundTiesToEven_sound`**: (1) `f32 → f64` preserves the
exact value of, and round-trips, every non-NaN `F32Bits`; (2) every NaN input
converts to a quiet NaN in every direction; (3) the signaling-NaN quietization
canary (`0x7FF0_0000_0000_0001 ↦ 0x7FC0_0000`, never `+∞`); (4) `f64 → f32`
narrowing of `-0.0`, gradual underflow to `+0`, the smallest subnormal at the
half-way boundary, and overflow to `+∞` at the exact tie; (5) every finite
nonzero input converts to `roundRatioTiesToEven` of its exact rational value (so
`roundRatioTiesToEven_correctly_rounded` applies verbatim to `f64 → f32`
narrowing). -/
theorem evalFloatToFloatRoundTiesToEven_sound :
    (∀ x : F32Bits, isNaNBits .binary32 x.toNat = false →
      floatKindSameValue (decodeBits .binary64 (f32ToF64 x).toNat) (decodeBits .binary32 x.toNat) ∧
      f64ToF32 (f32ToF64 x) = x) ∧
    (∀ (src dst : IeeeFormat) (bits : Nat), isNaNBits src bits = true →
      isNaNBits dst (evalFloatToFloatRoundTiesToEven src dst bits) = true ∧
        isQuietNaNBits dst (evalFloatToFloatRoundTiesToEven src dst bits) = true) ∧
    (f64ToF32 0x7FF0000000000001#64 = 0x7FC00000#32 ∧
      f64ToF32 0x7FF0000000000001#64 ≠ 0x7F800000#32) ∧
    f64ToF32 0x8000000000000000#64 = 0x80000000#32 ∧
    f64ToF32 0x3690000000000000#64 = 0x00000000#32 ∧
    f64ToF32 0x3690000000000001#64 = 0x00000001#32 ∧
    f64ToF32 0x47EFFFFFF0000000#64 = 0x7F800000#32 ∧
    (∀ (src dst : IeeeFormat) (bits : Nat) (neg : Bool) (n d : Nat),
      decodeBits src bits = .finite neg n d →
      evalFloatToFloatRoundTiesToEven src dst bits = roundRatioTiesToEven dst neg n d) :=
  ⟨f32ToF64_exact_and_roundtrip,
   fun src dst bits h => by
     rw [← convertFloatBits_tiesToEven]
     exact convertFloatBits_nan_quiet .tiesToEven src dst bits h,
   ⟨f64ToF32_signaling_nan_quietized.1, f64ToF32_signaling_nan_quietized.2.1⟩,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   fun src dst bits neg n d h => by
     rw [← convertFloatBits_tiesToEven, ← roundRatioBits_tiesToEven]
     exact convertFloatBits_of_finite .tiesToEven src dst bits neg n d h⟩

end Theorems

/-! ## §4b. Bridge lemmas to `lean-miri`'s `Miri.Interpreter.FloatBits`

`lean-miri/vendor/Miri/Interpreter/Float.lean` runs the same exact-rational pipeline
as `MirSemantics/Scalars.lean`, but through `private` helpers written in a `Bool` /
`Int.ofNat` style (`ratioExponent`, `powScale`, `roundQuotientEven`, `encode`,
`signedNumerator`) inside `Except`, with `throw`s for a zero denominator and for
"inconsistent rounding". The lemmas below

* restate the trusted helpers in that literal formulation
  (`ratioExponent_eq_miri`, `powScale_eq_miri`, `roundQuotientTiesToEven_eq_miri`,
  `floatToIntValue_eq_miri`), so `LeanMiriSpec.FloatCastLM` identifies each
  vendored helper with its trusted counterpart;
* pin `ratioExponent` to the integer logarithm (`ratioExponent_floor_log2`) and prove
  that both `inconsistentRounding` throws are unreachable
  (`roundRatioTiesToEven_consistent`);
* bound every encoder and every cast result below `2 ^ width` on **all** inputs
  (`zeroBits_lt`, `infBits_lt`, `preferredNaNBits_lt`, `roundRatioTiesToEven_lt`,
  `evalIntToFloatRoundTiesToEven_lt`, `evalFloatToFloatRoundTiesToEven_lt`,
  `evalFloatToIntSaturating_bits_lt`), characterize decoded finite values and NaN
  payloads (`decodeBits_finite_den_pos`, `decodeBits_nan_payload`) and NaN
  conversion (`evalFloatToFloatRoundTiesToEven_of_nan`,
  `decodeBits_evalFloatToFloatRoundTiesToEven_of_nan`); and
* relate the two's-complement helpers to `BitVec`
  (`encodeTwosComplement_eq_toNat_ofInt`, `intValueOfBits_true_eq_toInt`,
  `intValueOfBits_false_eq_toNat`, `intValueOfBits_encodeTwosComplement`).

Everything here depends only on `propext` / `Quot.sound` (see §5). -/

section MiriBridge

/-! ### Literal `Miri.Interpreter.FloatBits` formulations -/

/-- `ratioExponent` is literally `Miri.Interpreter.FloatBits.ratioExponent`
(`Float.lean:85-89`): `Int.ofNat (n / d).log2` when `n ≥ d`, otherwise `-(Int.ofNat k)`
or `-(Int.ofNat k + 1)` for `k := (d / n).log2`. -/
theorem ratioExponent_eq_miri (n d : Nat) :
    ratioExponent n d =
      if n ≥ d then Int.ofNat (n / d).log2
      else
        let k := (d / n).log2
        if n * 2 ^ k ≥ d then -(Int.ofNat k) else -(Int.ofNat k + 1) := rfl

/-- `powScale` is literally `Miri.Interpreter.FloatBits.powScale` (`Float.lean:47-49`). -/
theorem powScale_eq_miri (n d : Nat) (e : Int) :
    powScale n d e = if e ≥ 0 then (n * 2 ^ e.toNat, d) else (n, d * 2 ^ (-e).toNat) := by
  cases e with
  | ofNat _ => rfl
  | negSucc _ => rfl

/-- `roundQuotientTiesToEven` is literally `Miri.Interpreter.FloatBits.roundQuotientEven`
(`Float.lean:90-93`), whose tie test is a `Bool` formula. -/
theorem roundQuotientTiesToEven_eq_miri (n d : Nat) :
    roundQuotientTiesToEven n d =
      (let q := n / d
       let remainder := n % d
       if remainder * 2 > d || (remainder * 2 == d && q % 2 == 1) then q + 1 else q) := by
  unfold roundQuotientTiesToEven
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]

/-- `floatToIntValue` in the literal `Miri.Interpreter.FloatBits.toInteger`
formulation (`Float.lean:232-240`) on the Miri decoding `floatKindToMiri`: a NaN gives
`0`, an infinity the bound of its sign, and a finite value (including a zero, which
Miri decodes as `.finite 0 _`) clamps `signedNumerator neg (n / d)` with
`max lo (min hi ·)`, for any bounds `lo ≤ 0 ≤ hi`. -/
theorem floatToIntValue_eq_miri (f : IeeeFormat) (k : FloatKind) (lo hi : Int)
    (h0 : lo ≤ 0) (h1 : 0 ≤ hi) :
    floatToIntValue k lo hi =
      match (floatKindToMiri f k).value with
      | .nan _ => 0
      | .infinite => if (floatKindToMiri f k).negative then lo else hi
      | .finite n d =>
        max lo (min hi
          (if (floatKindToMiri f k).negative then -(Int.ofNat (n / d)) else Int.ofNat (n / d))) := by
  cases k with
  | zero neg =>
    simp only [floatToIntValue, floatKindToMiri, Nat.zero_div]
    cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have h : max lo (min hi (Int.ofNat 0)) = 0 := by
        have h' : Int.ofNat 0 = 0 := rfl
        rw [h']; omega
      exact h.symm
    · simp only [↓reduceIte]
      have h : max lo (min hi (-(Int.ofNat 0))) = 0 := by
        have h' : -(Int.ofNat 0) = 0 := rfl
        rw [h']; omega
      exact h.symm
  | finite neg n d => rfl
  | inf neg => rfl
  | nan neg q p => rfl

/-! ### Integer logarithm and rounding consistency -/

/-- `ratioExponent n d` is `⌊log₂ (n / d)⌋` for positive `n`, `d`: a nonnegative
`e` satisfies `d * 2 ^ e ≤ n < d * 2 ^ (e + 1)`, and a negative `e` satisfies
`d ≤ n * 2 ^ (-e) < 2 * d`. -/
theorem ratioExponent_floor_log2 (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    (0 ≤ ratioExponent n d →
      d * 2 ^ (ratioExponent n d).toNat ≤ n ∧ n < d * 2 ^ ((ratioExponent n d).toNat + 1)) ∧
    (ratioExponent n d < 0 →
      d ≤ n * 2 ^ (-ratioExponent n d).toNat ∧ n * 2 ^ (-ratioExponent n d).toNat < 2 * d) := by
  obtain ⟨hlo, hhi⟩ := powScale_neg_ratioExponent_bounds n d hn hd
  rw [powScale_eq_miri] at hlo hhi
  generalize ratioExponent n d = e at hlo hhi ⊢
  refine ⟨fun he => ?_, fun he => ?_⟩
  · by_cases hz : -e ≥ 0
    · rw [if_pos' hz] at hlo hhi
      have he0 : e = 0 := by omega
      subst he0
      simp only [Int.neg_zero, Int.toNat_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add,
        Nat.pow_one] at hlo hhi ⊢
      refine ⟨hlo, ?_⟩
      rw [Nat.mul_comm]; exact hhi
    · rw [if_neg' hz] at hlo hhi
      simp only [Int.neg_neg] at hlo hhi
      refine ⟨hlo, ?_⟩
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (d * 2 ^ e.toNat) 2]
      exact hhi
  · have hz : -e ≥ 0 := by omega
    rw [if_pos' hz] at hlo hhi
    exact ⟨hlo, hhi⟩

/-- **Rounding consistency** (`Miri.Interpreter.FloatBits.roundRatio`'s two
`throw .inconsistentRounding` branches are unreachable): for positive `n`, `d`, with
`exponent := max (ratioExponent n d) f.minExponent`,
`scaled := powScale n d (f.fractionBits - exponent)`, and
`sig := roundQuotientTiesToEven scaled.1 scaled.2`, the rounded significand never
exceeds `2 ^ (fractionBits + 1)` (so after a carry it is exactly `2 ^ fractionBits`),
and a significand below `2 ^ fractionBits` only occurs at `exponent = minExponent`. -/
theorem roundRatioTiesToEven_consistent (f : IeeeFormat) (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    let exponent := max (ratioExponent n d) f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    let sig := roundQuotientTiesToEven scaled.1 scaled.2
    sig ≤ 2 ^ (f.fractionBits + 1) ∧ (sig < 2 ^ f.fractionBits → exponent = f.minExponent) := by
  intro exponent scaled sig
  obtain ⟨hhi, hlo_ge, _⟩ := powScale_roundRatio_scaled_bounds f n d hn hd
  have hds : 0 < scaled.2 := powScale_snd_pos_gen n d hd _
  refine ⟨roundQuotient_le_of_lt_mul .tiesToEven scaled.1 scaled.2 _ hds hhi, fun hsub => ?_⟩
  by_cases hge : f.minExponent ≤ ratioExponent n d
  · have hge_sig : 2 ^ f.fractionBits ≤ sig :=
      roundQuotient_ge_of_mul_le .tiesToEven scaled.1 scaled.2 _ hds (hlo_ge hge)
    exact absurd hsub (Nat.not_lt.mpr hge_sig)
  · exact int_max_eq_right hge

/-! ### Width bounds and decoded shapes -/

theorem zeroBits_lt (f : IeeeFormat) (neg : Bool) : zeroBits f neg < 2 ^ f.width := by
  rw [zeroBits_eq_encodeBits]
  exact encodeBits_lt f neg 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _)

theorem infBits_lt (f : IeeeFormat) (neg : Bool) : infBits f neg < 2 ^ f.width :=
  encodeBits_lt f neg _ 0 (Nat.sub_lt (Nat.two_pow_pos _) (by decide)) (Nat.two_pow_pos _)

theorem preferredNaNBits_lt (f : IeeeFormat) : preferredNaNBits f < 2 ^ f.width := by
  cases f <;> decide

/-- `roundRatioTiesToEven` always produces an in-width bit pattern. -/
theorem roundRatioTiesToEven_lt (f : IeeeFormat) (neg : Bool) (n d : Nat) (hd : 0 < d) :
    roundRatioTiesToEven f neg n d < 2 ^ f.width :=
  (roundRatioBits_valid_and_not_nan .tiesToEven f neg n d hd).1

/-- Every int-to-float cast result is an in-width `dst` bit pattern. -/
theorem evalIntToFloatRoundTiesToEven_lt (signed : Bool) (w bits : Nat) (dst : IeeeFormat) :
    evalIntToFloatRoundTiesToEven signed w bits dst < 2 ^ dst.width :=
  roundRatioTiesToEven_lt dst _ _ 1 Nat.one_pos

/-- Every float-to-int cast result is canonical for its byte width. -/
theorem evalFloatToIntSaturating_bits_lt (src : IeeeFormat) (bits : Nat) (t : FloatIntTarget)
    (pw : FloatPtrWidth) :
    (evalFloatToIntSaturating src bits t pw).bits < 2 ^ t.bitWidth pw ∧
      (evalFloatToIntSaturating src bits t pw).sizeBytes = t.bitWidth pw / 8 := by
  obtain ⟨_, hlt, _, _, _⟩ := evalFloatToIntSaturating_sound src bits t pw
  have hw := FloatIntTarget.bitWidth_cases t pw
  obtain ⟨hmod, _⟩ := scalarModulus_div8 _ hw
  have hsz : (evalFloatToIntSaturating src bits t pw).sizeBytes = t.bitWidth pw / 8 := rfl
  rw [hsz, hmod] at hlt
  exact ⟨hlt, hsz⟩

/-- A decoded finite value has a positive (power-of-two) denominator. -/
theorem decodeBits_finite_den_pos (f : IeeeFormat) (bits : Nat) (neg : Bool) (n d : Nat)
    (h : decodeBits f bits = .finite neg n d) : 0 < d := by
  unfold decodeBits at h
  simp only at h
  split at h
  · split at h <;> cases h
  · split at h
    · split at h
      · cases h
      · injection h with _ _ hd
        rw [← hd]; exact powScale_snd_pos _ _
    · injection h with _ _ hd
      rw [← hd]; exact powScale_snd_pos _ _

/-- A decoded NaN carries the full, nonzero fraction field as its payload. -/
theorem decodeBits_nan_payload (f : IeeeFormat) (bits : Nat) (neg q : Bool) (payload : Nat)
    (h : decodeBits f bits = .nan neg q payload) :
    payload = bits % 2 ^ f.fractionBits ∧ payload ≠ 0 ∧ payload < 2 ^ f.fractionBits ∧
      q = Nat.beq ((payload / 2 ^ (f.fractionBits - 1)) % 2) 1 := by
  unfold decodeBits at h
  simp only at h
  split at h
  · split at h
    · cases h
    · rename_i hF
      injection h with _ hq hp
      subst hp
      exact ⟨rfl, hF, unpackBits_fraction_lt f bits, hq.symm⟩
  · split at h
    · split at h <;> cases h
    · cases h

/-- The quieted, precision-shifted NaN payload of `evalFloatToFloatRoundTiesToEven`
(with the `dst` quiet bit forced) fits in the `dst` fraction field. -/
theorem convertNaNPayload_lt (src dst : IeeeFormat) (payload : Nat)
    (hp : payload < 2 ^ src.fractionBits) :
    Nat.lor
        (if src.fractionBits ≤ dst.fractionBits then
          Nat.lor payload (2 ^ (src.fractionBits - 1)) * 2 ^ (dst.fractionBits - src.fractionBits)
        else Nat.lor payload (2 ^ (src.fractionBits - 1)) / 2 ^ (src.fractionBits - dst.fractionBits))
        (2 ^ (dst.fractionBits - 1)) < 2 ^ dst.fractionBits := by
  have hq : Nat.lor payload (2 ^ (src.fractionBits - 1)) < 2 ^ src.fractionBits :=
    Nat.or_lt_two_pow hp (two_pow_lt_two_pow (Nat.sub_lt (IeeeFormat.one_le_fb src) (by decide)))
  apply Nat.or_lt_two_pow _ (two_pow_lt_two_pow (Nat.sub_lt (IeeeFormat.one_le_fb dst) (by decide)))
  generalize Nat.lor payload (2 ^ (src.fractionBits - 1)) = quiet at hq
  cases src <;> cases dst <;>
    simp only [IeeeFormat.fractionBits, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff,
      ↓reduceIte, Nat.pow_zero, Nat.mul_one] at hq ⊢ <;> omega

/-- NaN conversion: a NaN input keeps its sign and gets the quieted,
precision-shifted payload with the `dst` quiet bit forced, exactly as
`Miri.Interpreter.FloatBits.convert` (`Float.lean:122-128`). -/
theorem evalFloatToFloatRoundTiesToEven_of_nan (src dst : IeeeFormat) (bits : Nat) (neg q : Bool)
    (payload : Nat) (h : decodeBits src bits = .nan neg q payload) :
    evalFloatToFloatRoundTiesToEven src dst bits =
      encodeBits dst neg (2 ^ dst.exponentBits - 1)
        (Nat.lor
          (if src.fractionBits ≤ dst.fractionBits then
            Nat.lor payload (2 ^ (src.fractionBits - 1)) * 2 ^ (dst.fractionBits - src.fractionBits)
          else Nat.lor payload (2 ^ (src.fractionBits - 1)) / 2 ^ (src.fractionBits - dst.fractionBits))
          (2 ^ (dst.fractionBits - 1))) := by
  unfold evalFloatToFloatRoundTiesToEven
  rw [h]

/-- The converted NaN decodes back to a quiet NaN of the input's sign whose payload
is exactly the converted fraction field. -/
theorem decodeBits_evalFloatToFloatRoundTiesToEven_of_nan (src dst : IeeeFormat) (bits : Nat)
    (neg q : Bool) (payload : Nat) (h : decodeBits src bits = .nan neg q payload) :
    decodeBits dst (evalFloatToFloatRoundTiesToEven src dst bits) =
      .nan neg true (Nat.lor
        (if src.fractionBits ≤ dst.fractionBits then
          Nat.lor payload (2 ^ (src.fractionBits - 1)) * 2 ^ (dst.fractionBits - src.fractionBits)
        else Nat.lor payload (2 ^ (src.fractionBits - 1)) / 2 ^ (src.fractionBits - dst.fractionBits))
        (2 ^ (dst.fractionBits - 1))) := by
  obtain ⟨_, _, hp, _⟩ := decodeBits_nan_payload src bits neg q payload h
  have hlt := convertNaNPayload_lt src dst payload hp
  generalize hpay : Nat.lor
      (if src.fractionBits ≤ dst.fractionBits then
        Nat.lor payload (2 ^ (src.fractionBits - 1)) * 2 ^ (dst.fractionBits - src.fractionBits)
      else Nat.lor payload (2 ^ (src.fractionBits - 1)) / 2 ^ (src.fractionBits - dst.fractionBits))
      (2 ^ (dst.fractionBits - 1)) = payload' at hlt
  have hge : 2 ^ (dst.fractionBits - 1) ≤ payload' := by
    rw [← hpay]; exact Nat.right_le_or
  have hE : 2 ^ dst.exponentBits - 1 < 2 ^ dst.exponentBits :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  rw [evalFloatToFloatRoundTiesToEven_of_nan src dst bits neg q payload h, hpay,
    decodeBits_encodeBits dst neg _ _ hE hlt, if_pos' rfl]
  have hpos := Nat.two_pow_pos (dst.fractionBits - 1)
  have hne : ¬ (payload' = 0) := by
    intro h0
    rw [h0] at hge
    omega
  rw [if_neg' hne]
  have hsplit : 2 ^ dst.fractionBits = 2 * 2 ^ (dst.fractionBits - 1) := by
    cases dst <;> decide
  have hdiv1 : payload' / 2 ^ (dst.fractionBits - 1) = 1 := by
    apply Nat.le_antisymm
    · have hlt2 : payload' / 2 ^ (dst.fractionBits - 1) < 2 :=
        nat_div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hsplit]; exact hlt)
      have hne2 : ¬ (payload' / 2 ^ (dst.fractionBits - 1) = 0) := by
        intro h0
        have := (Nat.le_div_iff_mul_le hpos).mpr (by rw [Nat.one_mul]; exact hge)
        omega
      omega
    · exact (Nat.le_div_iff_mul_le hpos).mpr (by rw [Nat.one_mul]; exact hge)
  rw [hdiv1]
  rfl

/-- Every float-to-float cast result is an in-width `dst` bit pattern, on **every**
`src` bit pattern (zeros, subnormals, normals, infinities, and every quiet or
signaling NaN payload). -/
theorem evalFloatToFloatRoundTiesToEven_lt (src dst : IeeeFormat) (bits : Nat) :
    evalFloatToFloatRoundTiesToEven src dst bits < 2 ^ dst.width := by
  cases hdec : decodeBits src bits with
  | zero neg =>
    rw [← convertFloatBits_tiesToEven, convertFloatBits_of_zero _ _ _ _ _ hdec]
    exact zeroBits_lt dst neg
  | finite neg n d =>
    rw [← convertFloatBits_tiesToEven, convertFloatBits_of_finite _ _ _ _ _ _ _ hdec]
    exact roundRatioTiesToEven_lt dst neg n d (decodeBits_finite_den_pos src bits neg n d hdec)
  | inf neg =>
    rw [← convertFloatBits_tiesToEven, convertFloatBits_of_inf _ _ _ _ _ hdec]
    exact infBits_lt dst neg
  | nan neg q payload =>
    obtain ⟨_, _, hp, _⟩ := decodeBits_nan_payload src bits neg q payload hdec
    rw [evalFloatToFloatRoundTiesToEven_of_nan src dst bits neg q payload hdec]
    exact encodeBits_lt dst neg _ _ (Nat.sub_lt (Nat.two_pow_pos _) (by decide))
      (convertNaNPayload_lt src dst payload hp)

/-- A float-to-float cast produces a NaN exactly when its input is a NaN (finite,
zero, and infinite inputs never round to a NaN). -/
theorem isNaNBits_evalFloatToFloatRoundTiesToEven (src dst : IeeeFormat) (bits : Nat) :
    isNaNBits dst (evalFloatToFloatRoundTiesToEven src dst bits) = isNaNBits src bits := by
  have hsrc : ∀ k, decodeBits src bits = k → isNaNBits src bits = (match k with
      | .nan _ _ _ => true
      | _ => false) := by
    intro k hk; unfold isNaNBits; rw [hk]
  have hE : 2 ^ dst.exponentBits - 1 < 2 ^ dst.exponentBits :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  cases hdec : decodeBits src bits with
  | zero neg =>
    rw [hsrc _ hdec, ← convertFloatBits_tiesToEven, convertFloatBits_of_zero _ _ _ _ _ hdec,
      zeroBits_eq_encodeBits]
    unfold isNaNBits
    rw [decodeBits_encodeBits dst neg 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _),
      if_neg' (IeeeFormat.max_exp_ne_zero dst), if_pos' rfl, if_pos' rfl]
  | finite neg n d =>
    rw [hsrc _ hdec, ← convertFloatBits_tiesToEven, convertFloatBits_of_finite _ _ _ _ _ _ _ hdec]
    exact (roundRatioBits_valid_and_not_nan .tiesToEven dst neg n d
      (decodeBits_finite_den_pos src bits neg n d hdec)).2
  | inf neg =>
    rw [hsrc _ hdec, ← convertFloatBits_tiesToEven, convertFloatBits_of_inf _ _ _ _ _ hdec]
    unfold isNaNBits infBits
    rw [decodeBits_encodeBits dst neg _ 0 hE (Nat.two_pow_pos _), if_pos' rfl, if_pos' rfl]
  | nan neg q payload =>
    rw [hsrc _ hdec]
    unfold isNaNBits
    rw [decodeBits_evalFloatToFloatRoundTiesToEven_of_nan src dst bits neg q payload hdec]

/-! ### Two's complement and `BitVec` -/

/-- `encodeTwosComplement` is `BitVec.ofInt` read back as a natural number. -/
theorem encodeTwosComplement_eq_toNat_ofInt (w : Nat) (v : Int) :
    encodeTwosComplement w v = (BitVec.ofInt w v).toNat := by
  rw [BitVec.toNat_ofInt]
  rfl

/-- Signed `intValueOfBits` is `BitVec.toInt` of the truncated pattern. -/
theorem intValueOfBits_true_eq_toInt (w bits : Nat) :
    intValueOfBits true w bits = (BitVec.ofNat w bits).toInt := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  unfold intValueOfBits
  simp only [true_and]
  generalize hb : bits % 2 ^ w = b
  have hblt : b < 2 ^ w := by rw [← hb]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  cases w with
  | zero =>
    have hb0 : b = 0 := by simp only [Nat.pow_zero] at hblt; omega
    subst hb0
    rfl
  | succ w =>
    have hsplit : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
    simp only [Nat.add_sub_cancel]
    by_cases hge : 2 ^ w ≤ b
    · have hn : ¬ (2 * b < 2 ^ (w + 1)) := by omega
      rw [if_pos' hge, if_neg' hn]
    · have hy : 2 * b < 2 ^ (w + 1) := by omega
      rw [if_neg' hge, if_pos' hy]

/-- Unsigned `intValueOfBits` is `BitVec.toNat` of the truncated pattern. -/
theorem intValueOfBits_false_eq_toNat (w bits : Nat) :
    intValueOfBits false w bits = ((BitVec.ofNat w bits).toNat : Int) := by
  rw [BitVec.toNat_ofNat]
  unfold intValueOfBits
  simp only [Bool.false_eq_true, false_and, ↓reduceIte]

/-- Two's-complement round trip at every Rust integer width: decoding the canonical
encoding of any in-range value recovers it, and the encoding is in width. -/
theorem intValueOfBits_encodeTwosComplement (signed : Bool) (w : Nat)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128) (v : Int)
    (hlo : (if signed = true then -((2 ^ (w - 1) : Nat) : Int) else 0) ≤ v)
    (hhi : v ≤
      (if signed = true then ((2 ^ (w - 1) : Nat) : Int) - 1 else ((2 ^ w : Nat) : Int) - 1)) :
    intValueOfBits signed w (encodeTwosComplement w v) = v ∧ encodeTwosComplement w v < 2 ^ w :=
  twos_roundtrip signed w hw v hlo hhi

/-- **Uniqueness of integer-logarithm exponent selection**: for positive `n`, `d`,
`ratioExponent n d` is the unique integer `e` scaling `n / d` by `2 ^ (-e)` into `[1, 2)`. -/
theorem ratioExponent_eq_of_powScale_bounds (n d : Nat) (e : Int) (hn : 0 < n) (hd : 0 < d)
    (hlo : (powScale n d (-e)).2 ≤ (powScale n d (-e)).1)
    (hhi : (powScale n d (-e)).1 < 2 * (powScale n d (-e)).2) :
    ratioExponent n d = e := by
  obtain ⟨rlo, rhi⟩ := powScale_neg_ratioExponent_bounds n d hn hd
  generalize ratioExponent n d = r at rlo rhi ⊢
  have hno_lt : ∀ (a b : Int), a < b →
      (powScale n d (-b)).2 ≤ (powScale n d (-b)).1 →
      (powScale n d (-a)).1 < 2 * (powScale n d (-a)).2 → False := by
    intro a b hab hblo ha_hi
    have hcross := powScale_diff_cross n d (-b) (-a) (by omega)
    have hdb : 0 < (powScale n d (-b)).2 := powScale_snd_pos_gen n d hd (-b)
    have hda : 0 < (powScale n d (-a)).2 := powScale_snd_pos_gen n d hd (-a)
    have hk : 1 ≤ ((-a) - (-b)).toNat := by omega
    have hpow2 : 2 ≤ 2 ^ ((-a) - (-b)).toNat := two_pow_le_two_pow hk
    have hmul1 : (powScale n d (-b)).2 * (powScale n d (-a)).2 * 2 ≤
        (powScale n d (-b)).1 * (powScale n d (-a)).2 * 2 ^ ((-a) - (-b)).toNat :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hblo) hpow2
    rw [hcross] at hmul1
    have hmul2 : (powScale n d (-a)).1 * (powScale n d (-b)).2 <
        2 * (powScale n d (-a)).2 * (powScale n d (-b)).2 :=
      (nat_mul_lt_mul_right_iff hdb).mpr ha_hi
    have hcomm : (powScale n d (-b)).2 * (powScale n d (-a)).2 * 2 =
        2 * (powScale n d (-a)).2 * (powScale n d (-b)).2 := by
      rw [Nat.mul_comm ((powScale n d (-b)).2) ((powScale n d (-a)).2),
        Nat.mul_comm _ 2, Nat.mul_assoc]
    omega
  by_cases hlt : e < r
  · exact False.elim (hno_lt e r hlt rlo hhi)
  · by_cases hgt : r < e
    · exact False.elim (hno_lt r e hgt hlo rhi)
    · omega

/-- Exact characterization of `ratioExponent n d` as `⌊log₂ (n / d)⌋` via `powScale`. -/
theorem ratioExponent_eq_iff_powScale_bounds (n d : Nat) (e : Int) (hn : 0 < n) (hd : 0 < d) :
    ratioExponent n d = e ↔
      (powScale n d (-e)).2 ≤ (powScale n d (-e)).1 ∧
        (powScale n d (-e)).1 < 2 * (powScale n d (-e)).2 := by
  constructor
  · rintro rfl
    exact powScale_neg_ratioExponent_bounds n d hn hd
  · rintro ⟨hlo, hhi⟩
    exact ratioExponent_eq_of_powScale_bounds n d e hn hd hlo hhi

/-- Adding `b < 2 ^ k` to a multiple of `2 ^ k` is a bitwise `or` (no carries). -/
theorem mul_two_pow_add_eq_lor (a b k : Nat) (hb : b < 2 ^ k) :
    a * 2 ^ k + b = Nat.lor (a * 2 ^ k) b := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (a * 2 ^ k + b).testBit i = ((a * 2 ^ k) ||| b).testBit i
  rw [Nat.mul_comm a (2 ^ k), Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_or,
    Nat.testBit_two_pow_mul]
  by_cases hi : i < k
  · have hge : ¬ (k ≤ i) := by omega
    rw [if_pos' hi]
    simp [hge]
  · have hge : k ≤ i := by omega
    have hb_false : b.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (two_pow_le_two_pow hge))
    rw [if_neg' hi]
    simp [hge, hb_false]

/-- Same-format `evalFloatToFloatRoundTiesToEven f f bits` on an in-width pattern is the
identity on every non-NaN and every quiet NaN, and sets only the quiet bit on a signaling NaN. -/
theorem evalFloatToFloatRoundTiesToEven_self_eq (f : IeeeFormat) (bits : Nat)
    (hbits : bits < 2 ^ f.width) :
    evalFloatToFloatRoundTiesToEven f f bits =
      match decodeBits f bits with
      | .nan _ false _ => Nat.lor bits (2 ^ (f.fractionBits - 1))
      | _ => bits := by
  have henc := encodeBits_unpackBits f bits hbits
  have hEl := unpackBits_exponent_lt f bits
  have hFl := unpackBits_fraction_lt f bits
  by_cases hnan : isNaNBits f bits = true
  · have hdec : ∃ neg q payload, decodeBits f bits = .nan neg q payload := by
      unfold isNaNBits at hnan
      cases hd : decodeBits f bits with
      | nan neg q payload => exact ⟨neg, q, payload, rfl⟩
      | _ => rw [hd] at hnan; cases hnan
    obtain ⟨neg, q, payload, hd⟩ := hdec
    obtain ⟨hp_eq, _, hp_lt, hq_eq⟩ := decodeBits_nan_payload f bits neg q payload hd
    rw [evalFloatToFloatRoundTiesToEven_of_nan f f bits neg q payload hd, hd]
    have hsame :
        (if f.fractionBits ≤ f.fractionBits then
          Nat.lor payload (2 ^ (f.fractionBits - 1)) * 2 ^ (f.fractionBits - f.fractionBits)
        else Nat.lor payload (2 ^ (f.fractionBits - 1)) / 2 ^ (f.fractionBits - f.fractionBits)) =
          Nat.lor payload (2 ^ (f.fractionBits - 1)) := by
      rw [if_pos' (Nat.le_refl _), Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    have hlor_idem : ∀ a b : Nat, Nat.lor (Nat.lor a b) b = Nat.lor a b := by
      intro a b; change (a ||| b) ||| b = a ||| b; rw [Nat.or_assoc, Nat.or_self]
    rw [hsame, hlor_idem]
    have hexp_max : (unpackBits f bits).exponent = 2 ^ f.exponentBits - 1 := by
      unfold decodeBits at hd
      simp only at hd
      by_cases hE : (unpackBits f bits).exponent = 2 ^ f.exponentBits - 1
      · exact hE
      · rw [if_neg' hE] at hd
        by_cases hZ : (unpackBits f bits).exponent = 0
        · rw [if_pos' hZ] at hd
          by_cases hFZ : (unpackBits f bits).fraction = 0
          · rw [if_pos' hFZ] at hd; cases hd
          · rw [if_neg' hFZ] at hd; cases hd
        · rw [if_neg' hZ] at hd; cases hd
    have hsign_eq : (unpackBits f bits).neg = neg := by
      unfold decodeBits at hd
      rw [if_pos' hexp_max] at hd
      by_cases hFZ : (unpackBits f bits).fraction = 0
      · rw [if_pos' hFZ] at hd; cases hd
      · rw [if_neg' hFZ] at hd; injection hd
    have hfrac_eq : (unpackBits f bits).fraction = payload := by
      unfold unpackBits; exact hp_eq.symm
    cases q with
    | false =>
      have hhi_shift :
          encodeBits f neg (2 ^ f.exponentBits - 1) (Nat.lor payload (2 ^ (f.fractionBits - 1))) =
            Nat.lor (encodeBits f neg (2 ^ f.exponentBits - 1) payload) (2 ^ (f.fractionBits - 1)) := by
        have hlt2 : payload / 2 ^ (f.fractionBits - 1) < 2 := by
          have hsp : 2 ^ f.fractionBits = 2 ^ (f.fractionBits - 1) * 2 := by
            cases f <;> decide
          exact nat_div_lt_of_lt_mul (by rw [← hsp]; exact hp_lt)
        have hne1 : (payload / 2 ^ (f.fractionBits - 1)) % 2 ≠ 1 := by
          intro h1
          have hb1 : Nat.beq ((payload / 2 ^ (f.fractionBits - 1)) % 2) 1 = true :=
            (nat_beq_eq_decide _ _).trans (decide_eq_true h1)
          rw [hb1] at hq_eq
          cases hq_eq
        have hdiv0 : payload / 2 ^ (f.fractionBits - 1) = 0 := by
          rcases h01 : payload / 2 ^ (f.fractionBits - 1) with _ | _ | k
          · rfl
          · rw [h01] at hne1; exact absurd rfl hne1
          · omega
        have hlt_half : payload < 2 ^ (f.fractionBits - 1) := by
          by_cases hge : 2 ^ (f.fractionBits - 1) ≤ payload
          · have hge1 : 1 ≤ payload / 2 ^ (f.fractionBits - 1) :=
              (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by rw [Nat.one_mul]; exact hge)
            omega
          · omega
        have hor_p : Nat.lor payload (2 ^ (f.fractionBits - 1)) =
            payload + 2 ^ (f.fractionBits - 1) := by
          have h := mul_two_pow_add_eq_lor 1 payload (f.fractionBits - 1) hlt_half
          rw [Nat.one_mul, Nat.add_comm] at h
          change payload ||| 2 ^ (f.fractionBits - 1) = _
          rw [Nat.or_comm]
          exact h.symm
        have hor_add : ∀ base : Nat,
            Nat.lor (base * 2 ^ f.fractionBits + payload) (2 ^ (f.fractionBits - 1)) =
              base * 2 ^ f.fractionBits + (payload + 2 ^ (f.fractionBits - 1)) := by
          intro base
          have h1 := mul_two_pow_add_eq_lor base payload f.fractionBits hp_lt
          have hsum_lt : payload + 2 ^ (f.fractionBits - 1) < 2 ^ f.fractionBits := by
            have hsp : 2 ^ f.fractionBits = 2 * 2 ^ (f.fractionBits - 1) := by
              cases f <;> decide
            omega
          have h3 := mul_two_pow_add_eq_lor base (payload + 2 ^ (f.fractionBits - 1)) f.fractionBits
            hsum_lt
          change (base * 2 ^ f.fractionBits + payload) ||| 2 ^ (f.fractionBits - 1) = _
          change _ = (base * 2 ^ f.fractionBits) ||| payload at h1
          change _ = (base * 2 ^ f.fractionBits) ||| (payload + 2 ^ (f.fractionBits - 1)) at h3
          change (payload ||| 2 ^ (f.fractionBits - 1)) = _ at hor_p
          rw [h1, Nat.or_assoc, hor_p, ← h3]
        unfold encodeBits zeroBits
        have hexp_base :
            ∀ x : Nat,
              (if neg = true then 2 ^ (f.width - 1) else 0) + (2 ^ f.exponentBits - 1) * 2 ^ f.fractionBits + x =
                ((if neg = true then 2 ^ f.exponentBits else 0) + (2 ^ f.exponentBits - 1)) * 2 ^ f.fractionBits + x := by
          intro x
          cases f <;> cases neg <;>
            simp [IeeeFormat.width, IeeeFormat.exponentBits, IeeeFormat.fractionBits] <;> omega
        rw [hexp_base (Nat.lor payload (2 ^ (f.fractionBits - 1))), hexp_base payload, hor_p, hor_add]
      rw [hhi_shift, ← hsign_eq, ← hexp_max, ← hfrac_eq, henc]
    | true =>
      have hlor_id : Nat.lor payload (2 ^ (f.fractionBits - 1)) = payload := by
        have h1 : (payload / 2 ^ (f.fractionBits - 1)) % 2 = 1 :=
          of_decide_eq_true ((nat_beq_eq_decide _ _).symm.trans hq_eq.symm)
        have htest : payload.testBit (f.fractionBits - 1) = true := by
          rw [Nat.testBit_eq_decide_div_mod_eq]
          exact decide_eq_true h1
        apply Nat.eq_of_testBit_eq
        intro i
        change (payload ||| 2 ^ (f.fractionBits - 1)).testBit i = payload.testBit i
        rw [Nat.testBit_or, Nat.testBit_two_pow]
        by_cases hi : f.fractionBits - 1 = i
        · subst hi; simp [htest]
        · simp [hi]
      rw [hlor_id, ← hsign_eq, ← hexp_max, ← hfrac_eq, henc]
  · have hnot_nan : isNaNBits f bits = false := Bool.eq_false_iff.mpr hnan
    have hmatch : (match decodeBits f bits with
        | .nan _ false _ => Nat.lor bits (2 ^ (f.fractionBits - 1))
        | _ => bits) = bits := by
      unfold isNaNBits at hnot_nan
      cases hd : decodeBits f bits with
      | nan _ _ _ => rw [hd] at hnot_nan; cases hnot_nan
      | _ => rfl
    rw [hmatch, ← convertFloatBits_tiesToEven]
    generalize hc : unpackBits f bits = c at henc hEl hFl
    rcases c with ⟨neg, E, F⟩
    dsimp only at henc hEl hFl
    rw [← henc] at hnot_nan ⊢
    by_cases hEmax : E = 2 ^ f.exponentBits - 1
    · subst hEmax
      by_cases hF0 : F = 0
      · subst hF0
        have hd : decodeBits f (encodeBits f neg (2 ^ f.exponentBits - 1) 0) = .inf neg := by
          rw [decodeBits_encodeBits f neg _ 0 hEl hFl, if_pos' rfl, if_pos' rfl]
        rw [convertFloatBits_of_inf _ _ _ _ _ hd]; rfl
      · have hd : decodeBits f (encodeBits f neg (2 ^ f.exponentBits - 1) F) =
            .nan neg (Nat.beq ((F / 2 ^ (f.fractionBits - 1)) % 2) 1) F := by
          rw [decodeBits_encodeBits f neg _ F hEl hFl, if_pos' rfl, if_neg' hF0]
        rw [isNaNBits_of_nan _ _ _ _ _ hd] at hnot_nan
        cases hnot_nan
    · by_cases hE0 : E = 0
      · subst hE0
        by_cases hF0 : F = 0
        · subst hF0
          have hd : decodeBits f (encodeBits f neg 0 0) = .zero neg := by
            rw [decodeBits_encodeBits f neg 0 0 hEl hFl, if_neg' (IeeeFormat.max_exp_ne_zero f),
              if_pos' rfl, if_pos' rfl]
          rw [convertFloatBits_of_zero _ _ _ _ _ hd, zeroBits_eq_encodeBits]
        · have hd : decodeBits f (encodeBits f neg 0 F) =
              .finite neg (powScale F 1 (f.minExponent - f.fractionBits)).1
                (powScale F 1 (f.minExponent - f.fractionBits)).2 := by
            rw [decodeBits_encodeBits f neg 0 F hEl hFl, if_neg' hEmax, if_pos' rfl, if_neg' hF0]
          rw [convertFloatBits_of_finite _ _ _ _ _ _ _ hd,
            roundRatioBits_subnormal .tiesToEven f neg F (Nat.pos_of_ne_zero hF0) hFl]
      · have hd : decodeBits f (encodeBits f neg E F) =
            .finite neg (powScale (2 ^ f.fractionBits + F) 1 ((E : Int) - f.bias - f.fractionBits)).1
              (powScale (2 ^ f.fractionBits + F) 1 ((E : Int) - f.bias - f.fractionBits)).2 := by
          rw [decodeBits_encodeBits f neg E F hEl hFl, if_neg' hEmax, if_neg' hE0]
        have hS1 : 2 ^ f.fractionBits ≤ 2 ^ f.fractionBits + F := Nat.le_add_right _ _
        have hS2 : 2 ^ f.fractionBits + F < 2 ^ (f.fractionBits + 1) := by
          have : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by rw [Nat.pow_succ]; omega
          omega
        have hE1 : f.minExponent ≤ ((E : Int) - f.bias - f.fractionBits) + f.fractionBits := by
          unfold IeeeFormat.minExponent; omega
        have hE2 : ((E : Int) - f.bias - f.fractionBits) + f.fractionBits ≤ f.maxExponent := by
          unfold IeeeFormat.maxExponent IeeeFormat.bias at *; cases f <;>
            simp [IeeeFormat.exponentBits] at hEl hEmax ⊢ <;> omega
        rw [convertFloatBits_of_finite _ _ _ _ _ _ _ hd,
          roundRatioBits_normal .tiesToEven f neg _ _ hS1 hS2 hE1 hE2]
        have hE_rec : ((((E : Int) - f.bias - f.fractionBits) + f.fractionBits + f.bias).toNat) = E := by
          omega
        have hF_rec : (2 ^ f.fractionBits + F) - 2 ^ f.fractionBits = F :=
          Nat.add_sub_cancel_left _ _
        rw [hE_rec, hF_rec]

/-- **Universal `f32 → f64 → f32` round trip across all `2 ^ 32` bit patterns** (zeros,
subnormals, normals, infinities, quiet NaNs, and signaling NaNs): widening `f32 → f64`
and narrowing back `f64 → f32` equals `evalFloatToFloatRoundTiesToEven .binary32 .binary32 bits`
(identical to `bits` on every non-sNaN, and setting only the quiet bit on sNaNs). -/
theorem evalFloatToFloatRoundTiesToEven_f32_f64_f32_eq_self (bits : Nat) (hbits : bits < 2 ^ 32) :
    evalFloatToFloatRoundTiesToEven .binary64 .binary32
        (evalFloatToFloatRoundTiesToEven .binary32 .binary64 bits) =
      evalFloatToFloatRoundTiesToEven .binary32 .binary32 bits := by
  by_cases hnan : isNaNBits .binary32 bits = true
  · have hdec : ∃ neg q payload, decodeBits .binary32 bits = .nan neg q payload := by
      unfold isNaNBits at hnan
      cases hd : decodeBits .binary32 bits with
      | nan neg q payload => exact ⟨neg, q, payload, rfl⟩
      | _ => rw [hd] at hnan; cases hnan
    obtain ⟨neg, q, payload, hd⟩ := hdec
    obtain ⟨_, _, hp_lt, _⟩ := decodeBits_nan_payload .binary32 bits neg q payload hd
    have hd64 := decodeBits_evalFloatToFloatRoundTiesToEven_of_nan .binary32 .binary64 bits neg q
      payload hd
    rw [evalFloatToFloatRoundTiesToEven_of_nan .binary64 .binary32 _ neg true _ hd64,
      evalFloatToFloatRoundTiesToEven_of_nan .binary32 .binary32 bits neg q payload hd]
    congr 1
    simp only [IeeeFormat.fractionBits, Nat.reduceSub, Nat.reduceLeDiff, ↓reduceIte, Nat.pow_zero,
      Nat.mul_one, Nat.reducePow]
    generalize hq_val : Nat.lor payload 4194304 = quiet
    have hlor_hi : Nat.lor (quiet * 536870912) 2251799813685248 = quiet * 536870912 := by
      have htest_q : quiet.testBit 22 = true := by
        rw [← hq_val]
        change (payload ||| 2 ^ 22).testBit 22 = true
        rw [Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true]
      apply Nat.eq_of_testBit_eq
      intro i
      change ((quiet * 2 ^ 29) ||| 2 ^ 51).testBit i = (quiet * 2 ^ 29).testBit i
      rw [Nat.testBit_or, Nat.testBit_two_pow]
      by_cases hi : 51 = i
      · subst hi
        have hmul_bit : (quiet * 2 ^ 29).testBit 51 = quiet.testBit 22 := by
          rw [Nat.mul_comm, Nat.testBit_two_pow_mul]
          simp
        simp [hmul_bit, htest_q]
      · simp [hi]
    rw [hlor_hi, hlor_hi, Nat.mul_div_cancel quiet (show 0 < 536870912 by decide)]
  · have hnot_nan : isNaNBits .binary32 bits = false := Bool.eq_false_iff.mpr hnan
    let x : F32Bits := BitVec.ofNat 32 bits
    have hx_nat : x.toNat = bits := by
      dsimp [x]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hbits
    have hx_nn : isNaNBits .binary32 x.toNat = false := by rw [hx_nat]; exact hnot_nan
    obtain ⟨W, _, hw, _, hn⟩ := f32_roundtrip_core x hx_nn
    rw [hx_nat, convertFloatBits_tiesToEven] at hw
    rw [hx_nat, convertFloatBits_tiesToEven] at hn
    rw [hw, hn, evalFloatToFloatRoundTiesToEven_self_eq .binary32 bits hbits]
    unfold isNaNBits at hnot_nan
    cases hd : decodeBits .binary32 bits with
    | nan _ _ _ => rw [hd] at hnot_nan; cases hnot_nan
    | _ => rfl

/-! ### Extended `BitVec` (`BitVec w`, `BitVec 32`, `BitVec 64`, `BitVec 128`) conversions -/

/-- `BitVec.ofNat w` of `encodeTwosComplement w v` is identically `BitVec.ofInt w v`. -/
theorem bitVec_ofNat_encodeTwosComplement (w : Nat) (v : Int) :
    BitVec.ofNat w (encodeTwosComplement w v) = BitVec.ofInt w v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, encodeTwosComplement_eq_toNat_ofInt, Nat.mod_eq_of_lt (BitVec.isLt _)]

/-- Encoding `b.toInt` in two's complement at width `w` recovers `b.toNat`
(`Classical.choice`-free). -/
theorem encodeTwosComplement_bitVec_toInt (w : Nat) (b : BitVec w) :
    encodeTwosComplement w b.toInt = b.toNat := by
  unfold encodeTwosComplement
  rw [BitVec.toInt_eq_toNat_cond]
  have hlt := b.isLt
  by_cases h : 2 * b.toNat < 2 ^ w
  · rw [if_pos' h, Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hlt),
      Int.toNat_natCast]
  · rw [if_neg' h]
    have hsub : (b.toNat : Int) - ((2 ^ w : Nat) : Int) =
        (b.toNat : Int) + ((2 ^ w : Nat) : Int) * (-1) := by omega
    rw [hsub, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hlt), Int.toNat_natCast]

/-- Reading `b : BitVec w` through `intValueOfBits signed w` yields `b.toInt` when `signed`
and `(b.toNat : Int)` when unsigned. -/
theorem intValueOfBits_bitVec_toNat (signed : Bool) (w : Nat) (b : BitVec w) :
    intValueOfBits signed w b.toNat = if signed then b.toInt else (b.toNat : Int) := by
  cases signed with
  | false =>
    rw [intValueOfBits_false_eq_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl
  | true =>
    rw [intValueOfBits_true_eq_toInt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl

/-- Signed `intValueOfBits true w bits` always lies in `[-2^(w-1), 2^(w-1))` for `0 < w`. -/
theorem intValueOfBits_signed_bounds (w bits : Nat) (hw : 0 < w) :
    -((2 ^ (w - 1) : Nat) : Int) ≤ intValueOfBits true w bits ∧
      intValueOfBits true w bits < ((2 ^ (w - 1) : Nat) : Int) := by
  rw [intValueOfBits_true_eq_toInt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  generalize hb : bits % 2 ^ w = b
  have hmod : b < 2 ^ w := by rw [← hb]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  cases w with
  | zero => omega
  | succ k =>
    simp only [Nat.add_sub_cancel]
    have hsplit : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases hlt : 2 * b < 2 ^ (k + 1)
    · rw [if_pos' hlt]; exact ⟨by omega, by omega⟩
    · rw [if_neg' hlt]; exact ⟨by omega, by omega⟩

/-- `(BitVec.ofInt w v).toInt = v` whenever `0 < w` and `v ∈ [-2^(w-1), 2^(w-1))`. -/
theorem bitVec_toInt_ofInt_in_bounds (w : Nat) (hw : 0 < w) (v : Int)
    (hlo : -((2 ^ (w - 1) : Nat) : Int) ≤ v)
    (hhi : v < ((2 ^ (w - 1) : Nat) : Int)) :
    (BitVec.ofInt w v).toInt = v := by
  rw [← bitVec_ofNat_encodeTwosComplement, ← intValueOfBits_true_eq_toInt]
  unfold intValueOfBits encodeTwosComplement
  cases w with
  | zero => omega
  | succ k =>
    simp only [true_and, Nat.add_sub_cancel] at hlo hhi ⊢
    have hsplit : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases hneg : v < 0
    · have hadd_nn : 0 ≤ v + ((2 ^ (k + 1) : Nat) : Int) := by omega
      have hadd_lt : v + ((2 ^ (k + 1) : Nat) : Int) < ((2 ^ (k + 1) : Nat) : Int) := by omega
      have hmod_eq : v % ((2 ^ (k + 1) : Nat) : Int) = v + ((2 ^ (k + 1) : Nat) : Int) := by
        have hrew : v = (v + ((2 ^ (k + 1) : Nat) : Int)) + ((2 ^ (k + 1) : Nat) : Int) * (-1) := by
          omega
        conv => lhs; rw [hrew]
        rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hadd_nn hadd_lt]
      rw [hmod_eq]
      have hnat_lt : (v + ((2 ^ (k + 1) : Nat) : Int)).toNat < 2 ^ (k + 1) := by omega
      rw [Nat.mod_eq_of_lt hnat_lt]
      have hge : 2 ^ k ≤ (v + ((2 ^ (k + 1) : Nat) : Int)).toNat := by omega
      rw [if_pos' hge]
      omega
    · have hnn : 0 ≤ v := by omega
      have hlt_w : v < ((2 ^ (k + 1) : Nat) : Int) := by omega
      rw [Int.emod_eq_of_lt hnn hlt_w]
      have hlt_full : v.toNat < 2 ^ (k + 1) := by omega
      rw [Nat.mod_eq_of_lt hlt_full]
      have hnge : ¬ (2 ^ k ≤ v.toNat) := by omega
      rw [if_neg' hnge]
      omega

/-- Sign-extending a `w`-bit signed integer (`0 < w ≤ 128`) into `BitVec 128` preserves its
`Int` value (`Miri.Interpreter.Cast.intLikeValue`'s `U128` signed intermediate). -/
theorem bitVec128_ofInt_intValueOfBits_toInt (w bits : Nat) (hw0 : 0 < w) (hw128 : w ≤ 128) :
    (BitVec.ofInt 128 (intValueOfBits true w bits)).toInt = intValueOfBits true w bits := by
  obtain ⟨hlo, hhi⟩ := intValueOfBits_signed_bounds w bits hw0
  have hle : 2 ^ (w - 1) ≤ 2 ^ 127 := two_pow_le_two_pow (by omega)
  exact bitVec_toInt_ofInt_in_bounds 128 (by decide) _ (by omega) (by omega)

/-- Zero-extending a `w`-bit unsigned pattern (`w ≤ 128`) into `BitVec 128` recovers
`intValueOfBits false w bits` (`Miri.Interpreter.Cast.intLikeValue`'s unsigned intermediate). -/
theorem bitVec128_ofNat_intValueOfBits_toNat (w bits : Nat) (hw128 : w ≤ 128) :
    ((BitVec.ofNat 128 (bits % 2 ^ w)).toNat : Int) = intValueOfBits false w bits := by
  rw [BitVec.toNat_ofNat]
  have hlt : bits % 2 ^ w < 2 ^ 128 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (two_pow_le_two_pow hw128)
  rw [Nat.mod_eq_of_lt hlt]
  unfold intValueOfBits
  simp only [Bool.false_eq_true, false_and, ↓reduceIte]

/-- `BitVec`-level view of `evalFloatToIntSaturating`: at target width `t.bitWidth pw`,
its bit pattern is `BitVec.ofInt (t.bitWidth pw) (floatToIntValue ...)`. -/
theorem evalFloatToIntSaturating_bitVec_eq (src : IeeeFormat) (bits : Nat)
    (t : FloatIntTarget) (pw : FloatPtrWidth) :
    BitVec.ofNat (t.bitWidth pw) (evalFloatToIntSaturating src bits t pw).bits =
      BitVec.ofInt (t.bitWidth pw)
        (floatToIntValue (decodeBits src bits) (t.minValue pw) (t.maxValue pw)) :=
  bitVec_ofNat_encodeTwosComplement (t.bitWidth pw) _

/-- Zero-extending an in-width `BitVec f.width` (`BitVec 32` / `BitVec 64`) to `BitVec 128`
agrees with `BitVec.ofNat 128 bits`. -/
theorem bitVec_zeroExtend128_of_lt_width (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    (BitVec.ofNat f.width bits).setWidth 128 = BitVec.ofNat 128 bits := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `f32ToF64` (`BitVec 32 → BitVec 64`) zero-extended to `BitVec 128` matches
`evalFloatToFloatRoundTiesToEven .binary32 .binary64` on **every** `x : BitVec 32`
(including NaNs). -/
theorem f32ToF64_setWidth128 (x : F32Bits) :
    (f32ToF64 x).setWidth 128 =
      BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven .binary32 .binary64 x.toNat) :=
  bitVec_zeroExtend128_of_lt_width .binary64 _
    (evalFloatToFloatRoundTiesToEven_lt .binary32 .binary64 x.toNat)

/-- `f64ToF32` (`BitVec 64 → BitVec 32`) zero-extended to `BitVec 128` matches
`evalFloatToFloatRoundTiesToEven .binary64 .binary32` on **every** `x : BitVec 64`
(including NaNs). -/
theorem f64ToF32_setWidth128 (x : F64Bits) :
    (f64ToF32 x).setWidth 128 =
      BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven .binary64 .binary32 x.toNat) :=
  bitVec_zeroExtend128_of_lt_width .binary32 _
    (evalFloatToFloatRoundTiesToEven_lt .binary64 .binary32 x.toNat)

/-! ### Saturation endpoints of `evalFloatToIntSaturating` (`±∞`, `±0.0`, `MIN` / `MAX`) -/

/-- `floatToIntValue` saturates `+∞` to `hi` and `-∞` to `lo`. -/
theorem floatToIntValue_inf (neg : Bool) (lo hi : Int) :
    floatToIntValue (.inf neg) lo hi = if neg then lo else hi := rfl

/-- `floatToIntValue` sends both zeros (in particular `-0.0`) to `0`. -/
theorem floatToIntValue_zero (neg : Bool) (lo hi : Int) :
    floatToIntValue (.zero neg) lo hi = 0 := rfl

/-- Two's-complement encoding of the target minimum: `2 ^ (w - 1)` for signed targets and `0`
for unsigned targets (`w = t.bitWidth pw`). -/
theorem encodeTwosComplement_minValue (t : FloatIntTarget) (pw : FloatPtrWidth) :
    encodeTwosComplement (t.bitWidth pw) (t.minValue pw) =
      if t.isSigned then 2 ^ (t.bitWidth pw - 1) else 0 := by
  unfold FloatIntTarget.minValue
  have hw := FloatIntTarget.bitWidth_cases t pw
  generalize t.bitWidth pw = w at hw ⊢
  cases t.isSigned <;> rcases hw with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Two's-complement encoding of the target maximum: `2 ^ (w - 1) - 1` for signed targets and
`2 ^ w - 1` for unsigned targets (`w = t.bitWidth pw`). -/
theorem encodeTwosComplement_maxValue (t : FloatIntTarget) (pw : FloatPtrWidth) :
    encodeTwosComplement (t.bitWidth pw) (t.maxValue pw) =
      if t.isSigned then 2 ^ (t.bitWidth pw - 1) - 1 else 2 ^ t.bitWidth pw - 1 := by
  unfold FloatIntTarget.maxValue
  have hw := FloatIntTarget.bitWidth_cases t pw
  generalize t.bitWidth pw = w at hw ⊢
  cases t.isSigned <;> rcases hw with rfl | rfl | rfl | rfl | rfl <;> decide

/-- **`+∞ ↦ MAX`, `-∞ ↦ MIN`**: `evalFloatToIntSaturating` on `infBits src neg` is the
two's-complement encoding of the target's `minValue` (`-∞`) or `maxValue` (`+∞`), i.e.
`2 ^ (w - 1)` / `0` for `-∞` and `2 ^ (w - 1) - 1` / `2 ^ w - 1` for `+∞` (signed / unsigned),
across all twelve integer targets (including `isize` / `usize` at either pointer width). -/
theorem evalFloatToIntSaturating_infBits (src : IeeeFormat) (neg : Bool) (t : FloatIntTarget)
    (pw : FloatPtrWidth) :
    (evalFloatToIntSaturating src (infBits src neg) t pw).bits =
      if neg then (if t.isSigned then 2 ^ (t.bitWidth pw - 1) else 0)
      else (if t.isSigned then 2 ^ (t.bitWidth pw - 1) - 1 else 2 ^ t.bitWidth pw - 1) := by
  simp only [evalFloatToIntSaturating, decodeBits_infBits, floatToIntValue]
  cases neg
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact encodeTwosComplement_maxValue t pw
  · simp only [↓reduceIte]; exact encodeTwosComplement_minValue t pw

/-- **`±0.0 ↦ 0`**: `evalFloatToIntSaturating` maps both zero encodings (`zeroBits src neg`, in
particular `-0.0`) to the all-zero target pattern, dropping the sign. -/
theorem evalFloatToIntSaturating_zeroBits (src : IeeeFormat) (neg : Bool) (t : FloatIntTarget)
    (pw : FloatPtrWidth) :
    (evalFloatToIntSaturating src (zeroBits src neg) t pw).bits = 0 := by
  simp only [evalFloatToIntSaturating, decodeBits_zeroBits, floatToIntValue, encodeTwosComplement,
    Int.zero_emod]
  rfl

/-- The target width of `evalFloatToIntSaturating` is `t.bitWidth pw / 8` bytes. -/
theorem evalFloatToIntSaturating_sizeBytes (src : IeeeFormat) (bits : Nat) (t : FloatIntTarget)
    (pw : FloatPtrWidth) :
    (evalFloatToIntSaturating src bits t pw).sizeBytes = t.bitWidth pw / 8 := rfl

/-- **Finite upper saturation (`truncRatio ≥ maxValue ↦ MAX`)**: when `bits` decodes to a
finite rational whose truncated integer value meets or exceeds `t.maxValue pw`,
`evalFloatToIntSaturating` saturates to the target maximum's two's-complement bit pattern. -/
theorem evalFloatToIntSaturating_of_ge_maxValue (src : IeeeFormat) (bits : Nat) (neg : Bool)
    (n d : Nat) (t : FloatIntTarget) (pw : FloatPtrWidth)
    (hdec : decodeBits src bits = .finite neg n d)
    (hge : t.maxValue pw ≤ truncRatio neg n d) :
    (evalFloatToIntSaturating src bits t pw).bits =
      if t.isSigned then 2 ^ (t.bitWidth pw - 1) - 1 else 2 ^ t.bitWidth pw - 1 := by
  have hp1 : 1 ≤ 2 ^ (t.bitWidth pw - 1) := Nat.one_le_two_pow
  have hp2 : 1 ≤ 2 ^ t.bitWidth pw := Nat.one_le_two_pow
  have hle : t.minValue pw ≤ t.maxValue pw := by
    unfold FloatIntTarget.minValue FloatIntTarget.maxValue
    cases t.isSigned <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hclamp : clampInt (t.minValue pw) (t.maxValue pw) (truncRatio neg n d) = t.maxValue pw := by
    unfold clampInt
    rw [Int.min_eq_left hge, Int.max_eq_right hle]
  simp only [evalFloatToIntSaturating, hdec, floatToIntValue, hclamp]
  exact encodeTwosComplement_maxValue t pw

/-- **Finite lower saturation (`truncRatio ≤ minValue ↦ MIN`)**: when `bits` decodes to a
finite rational whose truncated integer value is at or below `t.minValue pw` (including all
negative finite floats on unsigned targets, where `minValue = 0`),
`evalFloatToIntSaturating` saturates to the target minimum's two's-complement bit pattern. -/
theorem evalFloatToIntSaturating_of_le_minValue (src : IeeeFormat) (bits : Nat) (neg : Bool)
    (n d : Nat) (t : FloatIntTarget) (pw : FloatPtrWidth)
    (hdec : decodeBits src bits = .finite neg n d)
    (hle_min : truncRatio neg n d ≤ t.minValue pw) :
    (evalFloatToIntSaturating src bits t pw).bits =
      if t.isSigned then 2 ^ (t.bitWidth pw - 1) else 0 := by
  have hp1 : 1 ≤ 2 ^ (t.bitWidth pw - 1) := Nat.one_le_two_pow
  have hp2 : 1 ≤ 2 ^ t.bitWidth pw := Nat.one_le_two_pow
  have hle : t.minValue pw ≤ t.maxValue pw := by
    unfold FloatIntTarget.minValue FloatIntTarget.maxValue
    cases t.isSigned <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hclamp : clampInt (t.minValue pw) (t.maxValue pw) (truncRatio neg n d) = t.minValue pw := by
    unfold clampInt
    rw [Int.min_eq_right (Int.le_trans hle_min hle), Int.max_eq_left hle_min]
  simp only [evalFloatToIntSaturating, hdec, floatToIntValue, hclamp]
  exact encodeTwosComplement_minValue t pw

/-- **Finite in-range truncation (no saturation)**: when `bits` decodes to a finite rational
whose truncation toward zero lies in `[minValue, maxValue]`, `evalFloatToIntSaturating` is exactly
the two's-complement encoding of the truncated value (complementing the saturating cases
`evalFloatToIntSaturating_of_ge_maxValue` / `evalFloatToIntSaturating_of_le_minValue`). -/
theorem evalFloatToIntSaturating_of_in_range (src : IeeeFormat) (bits : Nat) (neg : Bool)
    (n d : Nat) (t : FloatIntTarget) (pw : FloatPtrWidth)
    (hdec : decodeBits src bits = .finite neg n d)
    (hlo : t.minValue pw ≤ truncRatio neg n d) (hhi : truncRatio neg n d ≤ t.maxValue pw) :
    (evalFloatToIntSaturating src bits t pw).bits =
      encodeTwosComplement (t.bitWidth pw) (truncRatio neg n d) := by
  have hclamp : clampInt (t.minValue pw) (t.maxValue pw) (truncRatio neg n d) =
      truncRatio neg n d := by
    unfold clampInt
    rw [Int.min_eq_right hhi, Int.max_eq_right hlo]
  simp only [evalFloatToIntSaturating, hdec, floatToIntValue, hclamp]

/-- **Signed zero preservation in `floatToFloat`**: `zeroBits src neg` maps to `zeroBits dst neg`
(preserving `-0.0` vs `+0.0`, in contrast to `evalFloatToIntSaturating_zeroBits`). -/
theorem evalFloatToFloatRoundTiesToEven_zeroBits (src dst : IeeeFormat) (neg : Bool) :
    evalFloatToFloatRoundTiesToEven src dst (zeroBits src neg) = zeroBits dst neg := by
  simp only [evalFloatToFloatRoundTiesToEven, decodeBits_zeroBits]

/-- **Signed infinity preservation in `floatToFloat`**: `infBits src neg` maps to
`infBits dst neg`. -/
theorem evalFloatToFloatRoundTiesToEven_infBits (src dst : IeeeFormat) (neg : Bool) :
    evalFloatToFloatRoundTiesToEven src dst (infBits src neg) = infBits dst neg := by
  simp only [evalFloatToFloatRoundTiesToEven, decodeBits_infBits]

/-- **Complete finite-case trichotomy for `evalFloatToIntSaturating`**: on any finite
`decodeBits src bits = .finite neg n d`, `evalFloatToIntSaturating` yields `MIN` when
`truncRatio neg n d ≤ minValue`, `MAX` when `maxValue ≤ truncRatio neg n d`, and the exact
two's-complement encoding `encodeTwosComplement` strictly in between. -/
theorem evalFloatToIntSaturating_finite_eq (src : IeeeFormat) (bits : Nat) (neg : Bool)
    (n d : Nat) (t : FloatIntTarget) (pw : FloatPtrWidth)
    (hdec : decodeBits src bits = .finite neg n d) :
    (evalFloatToIntSaturating src bits t pw).bits =
      if truncRatio neg n d ≤ t.minValue pw then
        if t.isSigned then 2 ^ (t.bitWidth pw - 1) else 0
      else if t.maxValue pw ≤ truncRatio neg n d then
        if t.isSigned then 2 ^ (t.bitWidth pw - 1) - 1 else 2 ^ t.bitWidth pw - 1
      else
        encodeTwosComplement (t.bitWidth pw) (truncRatio neg n d) := by
  by_cases hlo : truncRatio neg n d ≤ t.minValue pw
  · simp only [hlo, ↓reduceIte]
    exact evalFloatToIntSaturating_of_le_minValue src bits neg n d t pw hdec hlo
  · simp only [hlo, ↓reduceIte]
    by_cases hhi : t.maxValue pw ≤ truncRatio neg n d
    · simp only [hhi, ↓reduceIte]
      exact evalFloatToIntSaturating_of_ge_maxValue src bits neg n d t pw hdec hhi
    · simp only [hhi, ↓reduceIte]
      exact evalFloatToIntSaturating_of_in_range src bits neg n d t pw hdec
        (by omega) (by omega)

/-- **Zero integer to `+0.0` in `intToFloat`**: for every signedness `signed`, bit-width `w`, and
destination format `dst`, `0` maps to positive zero `zeroBits dst false` (`0`). -/
theorem evalIntToFloatRoundTiesToEven_zero (signed : Bool) (w : Nat) (dst : IeeeFormat) :
    evalIntToFloatRoundTiesToEven signed w 0 dst = zeroBits dst false := by
  have hiv : intValueOfBits signed w 0 = 0 := by
    unfold intValueOfBits
    dsimp only
    rw [if_neg']
    · simp only [Nat.zero_mod, Int.natCast_zero]
    · rintro ⟨_, hle⟩
      have hp : 1 ≤ 2 ^ (w - 1) := Nat.one_le_two_pow
      rw [Nat.zero_mod] at hle
      omega
  unfold evalIntToFloatRoundTiesToEven roundRatioTiesToEven
  rw [hiv]
  rfl

/-- Unsigned `intValueOfBits` is the canonical residue modulo `2 ^ w`. -/
theorem intValueOfBits_unsigned_eq_mod (w bits : Nat) :
    intValueOfBits false w bits = ((bits % 2 ^ w : Nat) : Int) := by
  unfold intValueOfBits
  dsimp only
  rw [if_neg' (fun ⟨h, _⟩ => Bool.noConfusion h)]

/-- Signed `intValueOfBits` at the sign bit `2 ^ (w - 1)` (`0 < w`) is `-2 ^ (w - 1)` (`iN::MIN`). -/
theorem intValueOfBits_signed_min (w : Nat) (hw : 0 < w) :
    intValueOfBits true w (2 ^ (w - 1)) = -((2 ^ (w - 1) : Nat) : Int) := by
  have hlt : 2 ^ (w - 1) < 2 ^ w := two_pow_lt_two_pow (by omega)
  have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
    have h1 : w = (w - 1) + 1 := by omega
    conv => lhs; rw [h1]
    rw [Nat.pow_succ, Nat.mul_comm]
  unfold intValueOfBits
  dsimp only
  rw [if_pos' ⟨rfl, by rw [Nat.mod_eq_of_lt hlt]; exact Nat.le_refl _⟩]
  rw [Nat.mod_eq_of_lt hlt, hpow]
  omega

/-- Signed `intValueOfBits` at all-ones `2 ^ w - 1` (`0 < w`) is `-1`. -/
theorem intValueOfBits_signed_neg_one (w : Nat) (hw : 0 < w) :
    intValueOfBits true w (2 ^ w - 1) = -1 := by
  have hp1 : 1 ≤ 2 ^ (w - 1) := Nat.one_le_two_pow
  have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
    have h1 : w = (w - 1) + 1 := by omega
    conv => lhs; rw [h1]
    rw [Nat.pow_succ, Nat.mul_comm]
  have hlt : 2 ^ w - 1 < 2 ^ w := by omega
  unfold intValueOfBits
  dsimp only
  rw [if_pos' ⟨rfl, by rw [Nat.mod_eq_of_lt hlt]; omega⟩]
  rw [Nat.mod_eq_of_lt hlt]
  omega

end MiriBridge

/-! ## §5. Axiom guards

Every headline theorem (and every `rfl` bridge to the trusted primitives) is
pinned to the standard axioms (`propext` / `Quot.sound`, or none): `#guard_msgs`
fails the build if a proof ever starts depending on `Classical.choice`,
`Lean.ofReduceBool`, `Lean.trustCompiler`, or any other non-standard axiom
(including placeholder proofs). -/

section AxiomGuards

/--
info: 'Anneal.Mir.IeeeFloatCast.pack_unpack_f32'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pack_unpack_f32

/--
info: 'Anneal.Mir.IeeeFloatCast.unpack_pack_f32'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unpack_pack_f32

/--
info: 'Anneal.Mir.IeeeFloatCast.pack_unpack_f64'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pack_unpack_f64

/--
info: 'Anneal.Mir.IeeeFloatCast.unpack_pack_f64'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unpack_pack_f64

/--
info: 'Anneal.Mir.IeeeFloatCast.decodeBits_agrees_miriDecode'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms decodeBits_agrees_miriDecode

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_sound'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_sound

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_nan'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_nan

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_canaries'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_canaries

/--
info: 'Anneal.Mir.IeeeFloatCast.roundQuotientTiesToEven_half_ulp'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundQuotientTiesToEven_half_ulp

/--
info: 'Anneal.Mir.IeeeFloatCast.roundQuotientTiesToEven_tie_even'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundQuotientTiesToEven_tie_even

/--
info: 'Anneal.Mir.IeeeFloatCast.roundRatioBits_congr'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioBits_congr

/--
info: 'Anneal.Mir.IeeeFloatCast.roundRatioBits_normal'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioBits_normal

/--
info: 'Anneal.Mir.IeeeFloatCast.roundRatioBits_subnormal'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioBits_subnormal

/--
info: 'Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_exact'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalIntToFloatRoundTiesToEven_exact

/--
info: 'Anneal.Mir.IeeeFloatCast.evalIntToFloat_i32_u32_to_f64_exact'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalIntToFloat_i32_u32_to_f64_exact

/--
info: 'Anneal.Mir.IeeeFloatCast.b585733184_ties_to_even_separation'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms b585733184_ties_to_even_separation

/--
info: 'Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_canaries'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms evalIntToFloatRoundTiesToEven_canaries

/--
info: 'Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_sound'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalIntToFloatRoundTiesToEven_sound

/--
info: 'Anneal.Mir.IeeeFloatCast.f32ToF64_exact_and_roundtrip'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms f32ToF64_exact_and_roundtrip

/--
info: 'Anneal.Mir.IeeeFloatCast.convertFloatBits_nan_quiet'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms convertFloatBits_nan_quiet

/--
info: 'Anneal.Mir.IeeeFloatCast.f64ToF32_signaling_nan_quietized'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms f64ToF32_signaling_nan_quietized

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_canaries'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToFloatRoundTiesToEven_canaries

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_sound'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToFloatRoundTiesToEven_sound

/--
info: 'Anneal.Mir.IeeeFloatCast.f64ToF32_subnormal_and_double_rounding_canaries'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms f64ToF32_subnormal_and_double_rounding_canaries

/--
info: 'Anneal.Mir.IeeeFloatCast.roundRatioBits_valid_and_not_nan'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioBits_valid_and_not_nan

/--
info: 'Anneal.Mir.IeeeFloatCast.roundRatioTiesToEven_float_half_ulp'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioTiesToEven_float_half_ulp

/--
info: 'Anneal.Mir.IeeeFloatCast.roundRatioTiesToEven_correctly_rounded'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioTiesToEven_correctly_rounded

/--
info: 'Anneal.Mir.IeeeFloatCast.roundRatioTiesToEven_overflow_of'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioTiesToEven_overflow_of

/--
info: 'Anneal.Mir.IeeeFloatCast.roundRatioTiesToEven_overflow_iff'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioTiesToEven_overflow_iff

/--
info: 'Anneal.Mir.IeeeFloatCast.roundRatioBits_sign_and_underflow_zero_preserved'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioBits_sign_and_underflow_zero_preserved

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_roundtrip_of_intToFloat'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_roundtrip_of_intToFloat

/--
info: 'Anneal.Mir.IeeeFloatCast.floatToIntValue_monotone'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatToIntValue_monotone

/--
info: 'Anneal.Mir.IeeeFloatCast.roundQuotient_tiesToEven'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms roundQuotient_tiesToEven

/--
info: 'Anneal.Mir.IeeeFloatCast.roundRatioBits_tiesToEven'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioBits_tiesToEven

/--
info: 'Anneal.Mir.IeeeFloatCast.convertFloatBits_tiesToEven'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms convertFloatBits_tiesToEven

/--
info: 'Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_eq_roundRatioBits'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms evalIntToFloatRoundTiesToEven_eq_roundRatioBits

/--
info: 'Anneal.Mir.IeeeFloatCast.ratioExponent_eq_miri' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms ratioExponent_eq_miri

/--
info: 'Anneal.Mir.IeeeFloatCast.powScale_eq_miri' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms powScale_eq_miri

/--
info: 'Anneal.Mir.IeeeFloatCast.roundQuotientTiesToEven_eq_miri' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundQuotientTiesToEven_eq_miri

/--
info: 'Anneal.Mir.IeeeFloatCast.floatToIntValue_eq_miri' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatToIntValue_eq_miri

/--
info: 'Anneal.Mir.IeeeFloatCast.ratioExponent_floor_log2' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ratioExponent_floor_log2

/--
info: 'Anneal.Mir.IeeeFloatCast.roundRatioTiesToEven_consistent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioTiesToEven_consistent

/--
info: 'Anneal.Mir.IeeeFloatCast.zeroBits_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms zeroBits_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.infBits_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms infBits_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.preferredNaNBits_lt' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms preferredNaNBits_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.roundRatioTiesToEven_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioTiesToEven_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalIntToFloatRoundTiesToEven_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_bits_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_bits_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.decodeBits_finite_den_pos' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms decodeBits_finite_den_pos

/--
info: 'Anneal.Mir.IeeeFloatCast.decodeBits_nan_payload' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms decodeBits_nan_payload

/--
info: 'Anneal.Mir.IeeeFloatCast.convertNaNPayload_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms convertNaNPayload_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_of_nan' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToFloatRoundTiesToEven_of_nan

/--
info: 'Anneal.Mir.IeeeFloatCast.decodeBits_evalFloatToFloatRoundTiesToEven_of_nan' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms decodeBits_evalFloatToFloatRoundTiesToEven_of_nan

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToFloatRoundTiesToEven_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.isNaNBits_evalFloatToFloatRoundTiesToEven' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isNaNBits_evalFloatToFloatRoundTiesToEven

/--
info: 'Anneal.Mir.IeeeFloatCast.encodeTwosComplement_eq_toNat_ofInt' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms encodeTwosComplement_eq_toNat_ofInt

/--
info: 'Anneal.Mir.IeeeFloatCast.intValueOfBits_true_eq_toInt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms intValueOfBits_true_eq_toInt

/--
info: 'Anneal.Mir.IeeeFloatCast.intValueOfBits_false_eq_toNat' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms intValueOfBits_false_eq_toNat

/--
info: 'Anneal.Mir.IeeeFloatCast.intValueOfBits_encodeTwosComplement' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms intValueOfBits_encodeTwosComplement

/--
info: 'Anneal.Mir.IeeeFloatCast.ratioExponent_eq_of_powScale_bounds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ratioExponent_eq_of_powScale_bounds

/--
info: 'Anneal.Mir.IeeeFloatCast.ratioExponent_eq_iff_powScale_bounds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ratioExponent_eq_iff_powScale_bounds

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_self_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToFloatRoundTiesToEven_self_eq

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_f32_f64_f32_eq_self' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToFloatRoundTiesToEven_f32_f64_f32_eq_self

/--
info: 'Anneal.Mir.IeeeFloatCast.bitVec_ofNat_encodeTwosComplement' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms bitVec_ofNat_encodeTwosComplement

/--
info: 'Anneal.Mir.IeeeFloatCast.encodeTwosComplement_bitVec_toInt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms encodeTwosComplement_bitVec_toInt

/--
info: 'Anneal.Mir.IeeeFloatCast.intValueOfBits_bitVec_toNat' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms intValueOfBits_bitVec_toNat

/--
info: 'Anneal.Mir.IeeeFloatCast.intValueOfBits_signed_bounds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms intValueOfBits_signed_bounds

/--
info: 'Anneal.Mir.IeeeFloatCast.bitVec_toInt_ofInt_in_bounds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bitVec_toInt_ofInt_in_bounds

/--
info: 'Anneal.Mir.IeeeFloatCast.bitVec128_ofInt_intValueOfBits_toInt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bitVec128_ofInt_intValueOfBits_toInt

/--
info: 'Anneal.Mir.IeeeFloatCast.bitVec128_ofNat_intValueOfBits_toNat' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms bitVec128_ofNat_intValueOfBits_toNat

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_bitVec_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_bitVec_eq

/--
info: 'Anneal.Mir.IeeeFloatCast.bitVec_zeroExtend128_of_lt_width' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms bitVec_zeroExtend128_of_lt_width

/--
info: 'Anneal.Mir.IeeeFloatCast.f32ToF64_setWidth128' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms f32ToF64_setWidth128

/--
info: 'Anneal.Mir.IeeeFloatCast.f64ToF32_setWidth128' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms f64ToF32_setWidth128

/--
info: 'Anneal.Mir.IeeeFloatCast.mul_two_pow_add_eq_lor' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mul_two_pow_add_eq_lor

/--
info: 'Anneal.Mir.IeeeFloatCast.floatToIntValue_inf' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms floatToIntValue_inf

/--
info: 'Anneal.Mir.IeeeFloatCast.floatToIntValue_zero' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms floatToIntValue_zero

/--
info: 'Anneal.Mir.IeeeFloatCast.encodeTwosComplement_minValue' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms encodeTwosComplement_minValue

/--
info: 'Anneal.Mir.IeeeFloatCast.encodeTwosComplement_maxValue' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms encodeTwosComplement_maxValue

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_infBits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_infBits

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_zeroBits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_zeroBits

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_sizeBytes' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_sizeBytes

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_of_ge_maxValue' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_of_ge_maxValue

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_of_le_minValue' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_of_le_minValue

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_zeroBits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToFloatRoundTiesToEven_zeroBits

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_infBits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToFloatRoundTiesToEven_infBits

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_of_in_range' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_of_in_range

/--
info: 'Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_finite_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_finite_eq

/--
info: 'Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalIntToFloatRoundTiesToEven_zero

/--
info: 'Anneal.Mir.IeeeFloatCast.intValueOfBits_unsigned_eq_mod' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms intValueOfBits_unsigned_eq_mod

/--
info: 'Anneal.Mir.IeeeFloatCast.intValueOfBits_signed_min' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms intValueOfBits_signed_min

/--
info: 'Anneal.Mir.IeeeFloatCast.intValueOfBits_signed_neg_one' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms intValueOfBits_signed_neg_one

/-! Axiom guards for the remaining (helper) theorems: together with the guards above,
all theorems of this file are pinned to `⊆ {propext, Quot.sound}` (no `Classical.choice`). -/

/--
info: 'Anneal.Mir.IeeeFloatCast.if_pos'' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.if_pos'

/--
info: 'Anneal.Mir.IeeeFloatCast.if_neg'' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.if_neg'

/--
info: 'Anneal.Mir.IeeeFloatCast.two_pow_le_two_pow' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.two_pow_le_two_pow

/--
info: 'Anneal.Mir.IeeeFloatCast.two_pow_lt_two_pow' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.two_pow_lt_two_pow

/--
info: 'Anneal.Mir.IeeeFloatCast.lt_of_two_pow_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.lt_of_two_pow_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.nat_mul_lt_mul_right_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.nat_mul_lt_mul_right_iff

/--
info: 'Anneal.Mir.IeeeFloatCast.nat_beq_eq_decide' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.nat_beq_eq_decide

/--
info: 'Anneal.Mir.IeeeFloatCast.nat_div_lt_of_lt_mul' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.nat_div_lt_of_lt_mul

/--
info: 'Anneal.Mir.IeeeFloatCast.unpackBits_encodeBits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.unpackBits_encodeBits

/--
info: 'Anneal.Mir.IeeeFloatCast.encodeBits_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.encodeBits_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.powScale_zero_fst' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.powScale_zero_fst

/--
info: 'Anneal.Mir.IeeeFloatCast.nat_beq_op_eq_decide' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.nat_beq_op_eq_decide

/--
info: 'Anneal.Mir.IeeeFloatCast.floatToIntValue_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.floatToIntValue_mem

/--
info: 'Anneal.Mir.IeeeFloatCast.twos_roundtrip' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.twos_roundtrip

/--
info: 'Anneal.Mir.IeeeFloatCast.FloatIntTarget.bitWidth_cases' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.FloatIntTarget.bitWidth_cases

/--
info: 'Anneal.Mir.IeeeFloatCast.scalarModulus_div8' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.scalarModulus_div8

/--
info: 'Anneal.Mir.IeeeFloatCast.nat_log2_eq_of_bounds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.nat_log2_eq_of_bounds

/--
info: 'Anneal.Mir.IeeeFloatCast.nat_log2_two_pow' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.nat_log2_two_pow

/--
info: 'Anneal.Mir.IeeeFloatCast.pow_mul_pow' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.pow_mul_pow

/--
info: 'Anneal.Mir.IeeeFloatCast.ratioExponent_mul_pow' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.ratioExponent_mul_pow

/--
info: 'Anneal.Mir.IeeeFloatCast.ratioExponent_div_pow' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.ratioExponent_div_pow

/--
info: 'Anneal.Mir.IeeeFloatCast.ratioExponent_mul' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.ratioExponent_mul

/--
info: 'Anneal.Mir.IeeeFloatCast.powScale_mul' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.powScale_mul

/--
info: 'Anneal.Mir.IeeeFloatCast.roundQuotient_mul' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.roundQuotient_mul

/--
info: 'Anneal.Mir.IeeeFloatCast.roundQuotient_exact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.roundQuotient_exact

/--
info: 'Anneal.Mir.IeeeFloatCast.roundRatioBits_mul' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.roundRatioBits_mul

/--
info: 'Anneal.Mir.IeeeFloatCast.powScale_snd_pos' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.powScale_snd_pos

/--
info: 'Anneal.Mir.IeeeFloatCast.powScale_fst_pos' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.powScale_fst_pos

/--
info: 'Anneal.Mir.IeeeFloatCast.roundQuotient_powScale_neg' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.roundQuotient_powScale_neg

/--
info: 'Anneal.Mir.IeeeFloatCast.ratioExponent_powScale' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.ratioExponent_powScale

/--
info: 'Anneal.Mir.IeeeFloatCast.IeeeFormat.fb_le_bias' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.IeeeFormat.fb_le_bias

/--
info: 'Anneal.Mir.IeeeFloatCast.IeeeFormat.one_le_fb' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.IeeeFormat.one_le_fb

/--
info: 'Anneal.Mir.IeeeFloatCast.decodeBits_encodeBits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.decodeBits_encodeBits

/--
info: 'Anneal.Mir.IeeeFloatCast.encodeBits_unpackBits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.encodeBits_unpackBits

/--
info: 'Anneal.Mir.IeeeFloatCast.unpackBits_exponent_lt' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.unpackBits_exponent_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.unpackBits_fraction_lt' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.unpackBits_fraction_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.IeeeFormat.two_bias_lt' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.IeeeFormat.two_bias_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.IeeeFormat.max_exp_ne_zero' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.IeeeFormat.max_exp_ne_zero

/--
info: 'Anneal.Mir.IeeeFloatCast.decodeBits_roundRatio_normal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.decodeBits_roundRatio_normal

/--
info: 'Anneal.Mir.IeeeFloatCast.decodeBits_roundRatio_subnormal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.decodeBits_roundRatio_subnormal

/--
info: 'Anneal.Mir.IeeeFloatCast.powScale_shift_cross' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.powScale_shift_cross

/--
info: 'Anneal.Mir.IeeeFloatCast.IeeeFormat.fb_add_bias_lt' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.IeeeFormat.fb_add_bias_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.zeroBits_eq_encodeBits' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.zeroBits_eq_encodeBits

/--
info: 'Anneal.Mir.IeeeFloatCast.f64_encode_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.f64_encode_lt

/--
info: 'Anneal.Mir.IeeeFloatCast.convertFloatBits_of_zero' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.convertFloatBits_of_zero

/--
info: 'Anneal.Mir.IeeeFloatCast.convertFloatBits_of_inf' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.convertFloatBits_of_inf

/--
info: 'Anneal.Mir.IeeeFloatCast.convertFloatBits_of_finite' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.convertFloatBits_of_finite

/--
info: 'Anneal.Mir.IeeeFloatCast.isNaNBits_of_nan' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.isNaNBits_of_nan

/--
info: 'Anneal.Mir.IeeeFloatCast.f32_rt_inf' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.f32_rt_inf

/--
info: 'Anneal.Mir.IeeeFloatCast.f32_rt_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.f32_rt_zero

/--
info: 'Anneal.Mir.IeeeFloatCast.f32_rt_subnormal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.f32_rt_subnormal

/--
info: 'Anneal.Mir.IeeeFloatCast.f32_rt_normal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.f32_rt_normal

/--
info: 'Anneal.Mir.IeeeFloatCast.f32_roundtrip_core' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.f32_roundtrip_core

/--
info: 'Anneal.Mir.IeeeFloatCast.isQuietNaNBits_of_nan' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.isQuietNaNBits_of_nan

/--
info: 'Anneal.Mir.IeeeFloatCast.powScale_snd_pos_gen' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.powScale_snd_pos_gen

/--
info: 'Anneal.Mir.IeeeFloatCast.powScale_diff_cross' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.powScale_diff_cross

/--
info: 'Anneal.Mir.IeeeFloatCast.powScale_neg_ratioExponent_bounds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.powScale_neg_ratioExponent_bounds

/--
info: 'Anneal.Mir.IeeeFloatCast.scale_lo_helper' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.scale_lo_helper

/--
info: 'Anneal.Mir.IeeeFloatCast.scale_hi_helper' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.scale_hi_helper

/--
info: 'Anneal.Mir.IeeeFloatCast.scale_sub_helper' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.scale_sub_helper

/--
info: 'Anneal.Mir.IeeeFloatCast.powScale_roundRatio_scaled_bounds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.powScale_roundRatio_scaled_bounds

/--
info: 'Anneal.Mir.IeeeFloatCast.roundQuotient_bounds' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.roundQuotient_bounds

/--
info: 'Anneal.Mir.IeeeFloatCast.roundQuotient_le_of_lt_mul' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.roundQuotient_le_of_lt_mul

/--
info: 'Anneal.Mir.IeeeFloatCast.roundQuotient_ge_of_mul_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.roundQuotient_ge_of_mul_le

/--
info: 'Anneal.Mir.IeeeFloatCast.int_le_max_right' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.int_le_max_right

/--
info: 'Anneal.Mir.IeeeFloatCast.int_max_eq_right' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.int_max_eq_right

/--
info: 'Anneal.Mir.IeeeFloatCast.decodeBits_zeroBits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.decodeBits_zeroBits

/--
info: 'Anneal.Mir.IeeeFloatCast.decodeBits_infBits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.decodeBits_infBits

/--
info: 'Anneal.Mir.IeeeFloatCast.floatToIntValue_of_denotesInt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.floatToIntValue_of_denotesInt

/--
info: 'Anneal.Mir.IeeeFloatCast.encodeTwosComplement_intValueOfBits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.encodeTwosComplement_intValueOfBits

/--
info: 'Anneal.Mir.IeeeFloatCast.clampInt_monotone' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.clampInt_monotone

/--
info: 'Anneal.Mir.IeeeFloatCast.truncRatio_monotone_nonneg' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.IeeeFloatCast.truncRatio_monotone_nonneg

end AxiomGuards

end Anneal.Mir.IeeeFloatCast
