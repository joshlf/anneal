/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Mir.IeeeFloatCast
import LeanMiriSpec.Correspondence.SimLM3_1
import LeanMiriSpec.Correspondence.WitLM1_2
import Miri.Interpreter.Float
import Miri.Interpreter.FloatOps
import Miri.Interpreter.Cast
import Miri.Interpreter.Step

/-!
# IEEE-754 float-cast correspondence (`LeanMiriSpec.FloatCastLM`)

Kernel-checked correspondence between Anneal's trusted float-cast semantics
(`Trusted.Rustc.V2026_06_01.MirSemantics`: `decodeBits`, `roundRatioTiesToEven`,
`evalFloatToIntSaturating`, `evalIntToFloatRoundTiesToEven`,
`evalFloatToFloatRoundTiesToEven`, `evalFloatCast`, `evalRvalue`, `stepMirFn`) and the
vendored `lean-miri` interpreter (`Miri.Interpreter.FloatBits.{decode, roundRatio,
toInteger, fromInteger, convert, nanChoices}`, `Miri.Interpreter.FloatOps.{readBits,
adjustNaN}`, `Miri.Interpreter.Cast.{cast, castFromIntLike}`,
`Miri.Interpreter.Step.step`) for Rust `as` casts `CastKind.floatToInt`,
`CastKind.intToFloat`, and `CastKind.floatToFloat` on `f32` / `f64`. No shadow
evaluator is defined: every headline theorem relates the trusted definitions directly to
the vendored ones.

1. **Private-helper bridges** (`miri_private%`, `miri_powScale_eq`,
   `miri_ratioExponent_eq`, `miri_roundQuotientEven_eq`, `miri_encode_eq`): the vendored
   `private` helpers of `Float.lean` are identified with the trusted primitives through
   the `Classical.choice`-free literal formulations of `Anneal.Mir.IeeeFloatCast`
   (`ratioExponent_eq_miri`, `powScale_eq_miri`, `roundQuotientTiesToEven_eq_miri`).
2. **Formats and decoding**: `ieeeFormatToMiri` / `miriFormatToIeee?` (matching width,
   exponent/fraction bits, bias, exponent range, size); `floatBits_decode_eq` (exact
   agreement on every `bits < 2 ^ width`) and `floatBits_decode_error`
   (`.encodingExceedsWidth` beyond the width).
3. **Rounding and primitive casts**: `floatBits_roundRatio_eq` (Miri never throws for
   `d ≠ 0`; the two `inconsistentRounding` throws are unreachable),
   `floatBits_fromInteger_eq`, `floatBits_toInteger_eq` (every integer target),
   `floatBits_convert_eq` (every bit pattern, including signaling and payload NaNs).
4. **NaN choices**: `floatBits_nanChoices_deterministic` (`[preferredNaN]`),
   `floatBits_nanChoices_nondet_eq` (`preferredNaN` at index `0` and the `convert`
   result at index `2`), `floatOps_adjustNaN_convert_refine` (the index-`2` refinement
   witness reproduces the trusted conversion on every input), and
   `floatOps_adjustNaN_deterministic` (deterministic mode maps NaNs to `preferredNaN`).
5. **Conservative hook overlay** (following `WideSliceDstLM`, leaving `Translate.lean`
   untouched): `castTypeInfoOfEncodedTyIdFloat` (`31 ↦ binary32`, `32 ↦ binary64`,
   `30` / `33` keep failing closed), `annealFloatOpsHooks`, `annealCastHooksFloat`,
   `annealRvalueHooksFloat`, `annealStepHooksFloat`, and the conservative-extension
   theorems `evalStatement_float_eq_of_stmtFree` /
   `step_float_eq_annealStepHooks_of_bodyFree`.
6. **`Cast.cast` simulation**: `cast_floatToFloat_eq`, `cast_floatToInt_eq`,
   `cast_intToFloat_eq`, `cast_floatCast_uninit`, unified as `floatCast_result_spec`
   over `FloatCastSig`.
7. **Real-step simulation** over `StateRelLM3_1` / `StepRelLM3_1`:
   `step_cast_float_copy_simulation`, `step_cast_float_move_simulation`, and
   `step_cast_float_constant_simulation` (NaN refinement witness: dead / uninitialized
   sources are UB in both machines; initialized sources of every bit pattern step in
   bit-exact lockstep), generalized to both NaN modes (`FloatNaNModeOk`) by the `_mode`
   variants, where the deterministic mode needs `FloatCastDetAgrees` (non-NaN input or a
   quieted conversion equal to `preferredNaNBits`).
8. **Deterministic NaN mode and boundaries**: `cast_floatToFloat_deterministic_eq`,
   `cast_floatToFloat_deterministic_agrees`, `evalFloatCast_intToFloat_bool_char_none`,
   `evalFloatCast_f16_f128_none`, and concrete edge-case witnesses
   (`u128::MAX as f32 = +∞`, `i128::MIN as f32`, `-0.0` casts, signaling-NaN
   quieting).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## Part 0. Vendored private helpers -/

open Lean Elab Term in
/-- `miri_private% M D` elaborates to the declaration `D` that the vendored module `M`
declares `private` (name resolution only: no axioms, no new definitions). -/
elab "miri_private% " mod:ident decl:ident : term => do
  let n := Lean.mkPrivateNameCore mod.getId.eraseMacroScopes decl.getId.eraseMacroScopes
  unless (← getEnv).contains n do
    throwError "miri_private%: unknown private declaration {decl.getId} of {mod.getId}"
  Lean.Meta.mkConstWithFreshMVarLevels n

/-- Vendored `Miri.Interpreter.FloatBits.powScale` (`private`, `Float.lean:47-49`). -/
local macro "miriPowScale" : term =>
  `(miri_private% Miri.Interpreter.Float Miri.Interpreter.FloatBits.powScale)
/-- Vendored `Miri.Interpreter.FloatBits.encode` (`private`, `Float.lean:50-51`). -/
local macro "miriEncode" : term =>
  `(miri_private% Miri.Interpreter.Float Miri.Interpreter.FloatBits.encode)
/-- Vendored `Miri.Interpreter.FloatBits.ratioExponent` (`private`, `Float.lean:85-89`). -/
local macro "miriRatioExponent" : term =>
  `(miri_private% Miri.Interpreter.Float Miri.Interpreter.FloatBits.ratioExponent)
/-- Vendored `Miri.Interpreter.FloatBits.roundQuotientEven` (`private`, `Float.lean:90-93`). -/
local macro "miriRoundQuotientEven" : term =>
  `(miri_private% Miri.Interpreter.Float Miri.Interpreter.FloatBits.roundQuotientEven)
/-- Vendored `Miri.Interpreter.FloatBits.signedNumerator` (`private`, `Float.lean:153-154`). -/
local macro "miriSignedNumerator" : term =>
  `(miri_private% Miri.Interpreter.Float Miri.Interpreter.FloatBits.signedNumerator)

/-- Vendored `Miri.Interpreter.FloatOps.engine` (`private`, `FloatOps.lean:20-21`). -/
local macro "miriFloatOpsEngine" : term =>
  `(miri_private% Miri.Interpreter.FloatOps Miri.Interpreter.FloatOps.engine)

/-- `FloatOps.engine` lifts a successful float-engine result. -/
theorem floatOps_engine_ok {S A : Type} (v : A) :
    (miriFloatOpsEngine (Except.ok v : Except Miri.Interpreter.FloatError A) :
      Miri.Interpreter.RvalueM S A) = pure v := rfl

/-- The vendored `powScale` is the trusted `powScale`. -/
theorem miri_powScale_eq (n d : Nat) (e : Int) : miriPowScale n d e = powScale n d e :=
  (Anneal.Mir.IeeeFloatCast.powScale_eq_miri n d e).symm

/-- The vendored `ratioExponent` is the trusted `ratioExponent` (definitionally). -/
theorem miri_ratioExponent_eq (n d : Nat) : miriRatioExponent n d = ratioExponent n d :=
  (Anneal.Mir.IeeeFloatCast.ratioExponent_eq_miri n d).symm

/-- The vendored `roundQuotientEven` is the trusted `roundQuotientTiesToEven`. -/
theorem miri_roundQuotientEven_eq (n d : Nat) :
    miriRoundQuotientEven n d = roundQuotientTiesToEven n d :=
  (Anneal.Mir.IeeeFloatCast.roundQuotientTiesToEven_eq_miri n d).symm

/-- The vendored `signedNumerator` (truncation sign of `toInteger`). -/
theorem miri_signedNumerator_eq (neg : Bool) (n : Nat) :
    miriSignedNumerator neg n = if neg then -(Int.ofNat n) else Int.ofNat n := rfl

/-! ## Part 1. Formats and decoding -/

/-- Translate an IEEE format of Anneal's float-cast model to `lean-miri`'s. -/
def ieeeFormatToMiri : IeeeFormat → Miri.Interpreter.FloatFormat
  | .binary32 => .binary32
  | .binary64 => .binary64

/-- Partial inverse of `ieeeFormatToMiri` (`binary16` / `binary128` are unmodeled). -/
def miriFormatToIeee? : Miri.Interpreter.FloatFormat → Option IeeeFormat
  | .binary32 => some .binary32
  | .binary64 => some .binary64
  | _ => none

@[simp] theorem ieeeFormatToMiri_width (f : IeeeFormat) :
    (ieeeFormatToMiri f).width = f.width := by cases f <;> rfl
@[simp] theorem ieeeFormatToMiri_exponentBits (f : IeeeFormat) :
    (ieeeFormatToMiri f).exponentBits = f.exponentBits := by cases f <;> rfl
@[simp] theorem ieeeFormatToMiri_fractionBits (f : IeeeFormat) :
    (ieeeFormatToMiri f).fractionBits = f.fractionBits := by cases f <;> rfl
@[simp] theorem ieeeFormatToMiri_bias (f : IeeeFormat) :
    (ieeeFormatToMiri f).bias = f.bias := by cases f <;> rfl
@[simp] theorem ieeeFormatToMiri_minExponent (f : IeeeFormat) :
    (ieeeFormatToMiri f).minExponent = f.minExponent := by cases f <;> rfl
@[simp] theorem ieeeFormatToMiri_maxExponent (f : IeeeFormat) :
    (ieeeFormatToMiri f).maxExponent = f.maxExponent := by cases f <;> rfl
theorem ieeeFormatToMiri_size (f : IeeeFormat) :
    (ieeeFormatToMiri f).size = translateSizeBytes f.byteWidth := by cases f <;> rfl

theorem miriFormatToIeee?_ieeeFormatToMiri (f : IeeeFormat) :
    miriFormatToIeee? (ieeeFormatToMiri f) = some f := by cases f <;> rfl

theorem ieeeFormatToMiri_of_miriFormatToIeee? {g : Miri.Interpreter.FloatFormat} {f : IeeeFormat}
    (h : miriFormatToIeee? g = some f) : ieeeFormatToMiri f = g := by
  cases g <;> cases f <;> first | rfl | (simp [miriFormatToIeee?] at h)

theorem ieeeFormatToMiri_injective {f g : IeeeFormat}
    (h : ieeeFormatToMiri f = ieeeFormatToMiri g) : f = g := by
  cases f <;> cases g <;> first | rfl | cases h

/-- `lean-miri`'s `FloatClass` / `FloatDecoded` view of a Miri-shaped decoding. -/
def miriDecodedToVendored (x : Anneal.Mir.IeeeFloatCast.MiriFloatDecoded) :
    Miri.Interpreter.FloatDecoded :=
  ⟨x.negative,
    match x.value with
    | .finite n d => .finite n d
    | .infinite => .infinite
    | .nan p => .nan p⟩

/-- The `lean-miri` decoding of a trusted `FloatKind` (zeros as `.finite 0 den`). -/
def floatKindToMiriDecoded (f : IeeeFormat) (k : FloatKind) : Miri.Interpreter.FloatDecoded :=
  miriDecodedToVendored (Anneal.Mir.IeeeFloatCast.floatKindToMiri f k)

theorem width_lt_128 (f : IeeeFormat) : 2 ^ f.width ≤ 2 ^ 128 := by
  cases f <;> decide

theorem bitVec128_toNat_of_lt_width {f : IeeeFormat} {bits : Nat} (h : bits < 2 ^ f.width) :
    (BitVec.ofNat 128 bits).toNat = bits := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (width_lt_128 f))

theorem floatBits_decode_eq_miriDecode (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ 128) :
    Miri.Interpreter.FloatBits.decode ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩ =
      match Anneal.Mir.IeeeFloatCast.miriDecode f bits with
      | some r => .ok (miriDecodedToVendored r)
      | none => .error .encodingExceedsWidth := by
  have h128 : (BitVec.ofNat 128 bits).toNat = bits := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h
  unfold Miri.Interpreter.FloatBits.decode Anneal.Mir.IeeeFloatCast.miriDecode
  simp only [h128, ieeeFormatToMiri_width, ieeeFormatToMiri_fractionBits,
    ieeeFormatToMiri_exponentBits, ieeeFormatToMiri_minExponent, ieeeFormatToMiri_bias,
    miri_powScale_eq]
  by_cases hge : bits ≥ 2 ^ f.width
  · simp only [hge, ↓reduceIte]
    rfl
  · simp only [hge, ↓reduceIte]
    split
    · split <;> rfl
    · rfl

/-- The vendored `encode` is the trusted `encodeBits`, zero-extended to 128 bits. -/
theorem miri_encode_eq (f : IeeeFormat) (neg : Bool) (e fr : Nat) :
    miriEncode (ieeeFormatToMiri f) neg e fr =
      ⟨ieeeFormatToMiri f, BitVec.ofNat 128 (encodeBits f neg e fr)⟩ := by
  cases f <;> rfl

/-- `FloatBits.zero` is `zeroBits`. -/
theorem floatBits_zero_eq (f : IeeeFormat) (neg : Bool) :
    Miri.Interpreter.FloatBits.zero (ieeeFormatToMiri f) neg =
      ⟨ieeeFormatToMiri f, BitVec.ofNat 128 (zeroBits f neg)⟩ := by
  rw [Anneal.Mir.IeeeFloatCast.zeroBits_eq_encodeBits]
  exact miri_encode_eq f neg 0 0

/-- `FloatBits.infinity` is `infBits`. -/
theorem floatBits_infinity_eq (f : IeeeFormat) (neg : Bool) :
    Miri.Interpreter.FloatBits.infinity (ieeeFormatToMiri f) neg =
      ⟨ieeeFormatToMiri f, BitVec.ofNat 128 (infBits f neg)⟩ := by
  cases f <;> rfl

/-- `FloatBits.preferredNaN` is `preferredNaNBits`. -/
theorem floatBits_preferredNaN_eq (f : IeeeFormat) :
    Miri.Interpreter.FloatBits.preferredNaN (ieeeFormatToMiri f) =
      ⟨ieeeFormatToMiri f, BitVec.ofNat 128 (preferredNaNBits f)⟩ := by
  cases f <;> rfl

/-- **Decode equivalence**: on every in-width bit pattern, `FloatBits.decode` is the
`lean-miri` view of `decodeBits` (zeros as `.finite 0 den`, NaNs with their full
payload). -/
theorem floatBits_decode_eq (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    Miri.Interpreter.FloatBits.decode ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩ =
      .ok (floatKindToMiriDecoded f (decodeBits f bits)) := by
  rw [floatBits_decode_eq_miriDecode f bits (Nat.lt_of_lt_of_le h (width_lt_128 f)),
    Anneal.Mir.IeeeFloatCast.decodeBits_agrees_miriDecode f bits h]
  rfl

/-- Out-of-width encodings are rejected with `.encodingExceedsWidth`. -/
theorem floatBits_decode_error (f : IeeeFormat) (bits : Nat) (h1 : 2 ^ f.width ≤ bits)
    (h2 : bits < 2 ^ 128) :
    Miri.Interpreter.FloatBits.decode ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩ =
      .error .encodingExceedsWidth := by
  rw [floatBits_decode_eq_miriDecode f bits h2]
  have hge : bits ≥ 2 ^ f.width := h1
  simp only [Anneal.Mir.IeeeFloatCast.miriDecode, hge, ↓reduceIte]

/-! ## Part 2. Rounding and primitive casts -/

theorem floatBits_roundRatio_zeroDenominator (g : Miri.Interpreter.FloatFormat) (neg : Bool)
    (n : Nat) :
    Miri.Interpreter.FloatBits.roundRatio g neg n 0 = .error .zeroDenominator := rfl

/-- **Rounding equivalence**: for every format, sign, numerator, and nonzero
denominator, `FloatBits.roundRatio` succeeds (neither `.zeroDenominator` nor
`.inconsistentRounding` is thrown) with exactly `roundRatioTiesToEven`. -/
theorem floatBits_roundRatio_eq (f : IeeeFormat) (neg : Bool) (n d : Nat) (hd : d ≠ 0) :
    Miri.Interpreter.FloatBits.roundRatio (ieeeFormatToMiri f) neg n d =
      .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128 (roundRatioTiesToEven f neg n d)⟩ := by
  have hd0 : (d == 0) = false := by simp [hd]
  unfold Miri.Interpreter.FloatBits.roundRatio roundRatioTiesToEven
  simp only [hd0, hd, Bool.false_eq_true, ↓reduceIte, miri_ratioExponent_eq, miri_powScale_eq,
    miri_roundQuotientEven_eq, ieeeFormatToMiri_minExponent, ieeeFormatToMiri_maxExponent,
    ieeeFormatToMiri_fractionBits, ieeeFormatToMiri_bias]
  by_cases hn : n = 0
  · subst hn
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [floatBits_zero_eq]
    rfl
  · have hn0 : (n == 0) = false := by simp [hn]
    simp only [hn0, hn, Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_natCast]
    obtain ⟨hle, hsub⟩ := Anneal.Mir.IeeeFloatCast.roundRatioTiesToEven_consistent f n d
      (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hd)
    generalize max (ratioExponent n d) f.minExponent = E at hle hsub ⊢
    generalize roundQuotientTiesToEven (powScale n d ((f.fractionBits : Int) - E)).fst
      (powScale n d ((f.fractionBits : Int) - E)).snd = S at hle hsub ⊢
    by_cases hov : E > f.maxExponent
    · simp only [hov, ↓reduceIte, floatBits_infinity_eq]
      rfl
    · simp only [hov, ↓reduceIte]
      by_cases hc : 2 ^ (f.fractionBits + 1) ≤ S
      · have hS : S = 2 ^ (f.fractionBits + 1) := Nat.le_antisymm hle hc
        have hS2 : S / 2 = 2 ^ f.fractionBits := by rw [hS, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
        have hlt : ¬ (2 ^ f.fractionBits < 2 ^ f.fractionBits) := Nat.lt_irrefl _
        have hge : ¬ (2 ^ (f.fractionBits + 1) ≤ 2 ^ f.fractionBits) := by
          have := Anneal.Mir.IeeeFloatCast.two_pow_lt_two_pow (Nat.lt_succ_self f.fractionBits)
          omega
        simp only [ge_iff_le, hc, decide_true, ↓reduceIte, hS2, hlt, hge]
        by_cases hov2 : E + 1 > f.maxExponent
        · simp only [hov2, ↓reduceIte, floatBits_infinity_eq]
          rfl
        · simp only [hov2, ↓reduceIte, miri_encode_eq]
          rfl
      · have hlt1 : S < 2 ^ (f.fractionBits + 1) := Nat.lt_of_not_le hc
        simp only [ge_iff_le, hc, decide_false, Bool.false_eq_true, ↓reduceIte, hov]
        by_cases hs : S < 2 ^ f.fractionBits
        · have hE : E = f.minExponent := hsub hs
          simp only [hs, ↓reduceIte, hE, bne_self_eq_false, Bool.false_eq_true, miri_encode_eq]
          rfl
        · simp only [hs, ↓reduceIte, miri_encode_eq]
          rfl

/-- `FloatBits.fromInteger` is `roundRatioTiesToEven` of the exact integer. -/
theorem floatBits_fromInteger_eq (f : IeeeFormat) (v : Int) :
    Miri.Interpreter.FloatBits.fromInteger (ieeeFormatToMiri f) v =
      .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128 (roundRatioTiesToEven f (decide (v < 0)) v.natAbs 1)⟩ :=
  floatBits_roundRatio_eq f _ _ 1 Nat.one_ne_zero

/-- `FloatBits.fromInteger` of a decoded integer bit pattern is
`evalIntToFloatRoundTiesToEven`. -/
theorem floatBits_fromInteger_intValueOfBits (signed : Bool) (w bits : Nat) (f : IeeeFormat) :
    Miri.Interpreter.FloatBits.fromInteger (ieeeFormatToMiri f) (intValueOfBits signed w bits) =
      .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128 (evalIntToFloatRoundTiesToEven signed w bits f)⟩ :=
  floatBits_fromInteger_eq f _

/-- Integer-target bounds in `lean-miri`'s `Int` power formulation. -/
theorem floatIntTarget_bounds (t : FloatIntTarget) (pw : FloatPtrWidth) :
    t.minValue pw = (if t.isSigned = true then -(2 : Int) ^ (t.bitWidth pw - 1) else 0) ∧
    t.maxValue pw = (if t.isSigned = true then (2 : Int) ^ (t.bitWidth pw - 1) - 1
      else (2 : Int) ^ t.bitWidth pw - 1) := by
  unfold FloatIntTarget.minValue FloatIntTarget.maxValue
  constructor <;> split <;> simp [Int.natCast_pow]

/-- **Float-to-int equivalence**: for every in-width bit pattern and every integer
target, `FloatBits.toInteger` returns `floatToIntValue` (NaN ↦ `0`, `±∞` ↦ max/min,
`-0.0` ↦ `0`, finite values truncate and saturate). -/
theorem floatBits_toInteger_eq (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width)
    (t : FloatIntTarget) (pw : FloatPtrWidth) :
    Miri.Interpreter.FloatBits.toInteger ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩
        (t.bitWidth pw) t.isSigned =
      .ok (floatToIntValue (decodeBits f bits) (t.minValue pw) (t.maxValue pw)) := by
  have hw := Anneal.Mir.IeeeFloatCast.FloatIntTarget.bitWidth_cases t pw
  have hvalid : (t.bitWidth pw == 0 || decide (t.bitWidth pw > 128)) = false := by
    rcases hw with h | h | h | h | h <;> simp [h]
  obtain ⟨hmin, hmax⟩ := floatIntTarget_bounds t pw
  have hp1 : 1 ≤ 2 ^ (t.bitWidth pw - 1) := Nat.one_le_two_pow
  have hp2 : 1 ≤ 2 ^ t.bitWidth pw := Nat.one_le_two_pow
  have h0 : t.minValue pw ≤ 0 := by
    unfold FloatIntTarget.minValue; split <;> omega
  have h1 : 0 ≤ t.maxValue pw := by
    unfold FloatIntTarget.maxValue; split <;> omega
  rw [Anneal.Mir.IeeeFloatCast.floatToIntValue_eq_miri f _ _ _ h0 h1]
  unfold Miri.Interpreter.FloatBits.toInteger
  simp only [hvalid, Bool.false_eq_true, ↓reduceIte, floatBits_decode_eq f bits h]
  rw [hmin, hmax]
  cases decodeBits f bits <;> rfl

/-- **Float-to-float equivalence**: `FloatBits.convert` agrees bit-exactly with
`evalFloatToFloatRoundTiesToEven` on **every** in-width source bit pattern (zeros,
subnormals, normals, infinities, and every quiet / signaling / payload NaN). -/
theorem floatBits_convert_eq (src dst : IeeeFormat) (bits : Nat) (h : bits < 2 ^ src.width) :
    Miri.Interpreter.FloatBits.convert ⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩
        (ieeeFormatToMiri dst) =
      .ok ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩ := by
  unfold Miri.Interpreter.FloatBits.convert
  rw [floatBits_decode_eq src bits h]
  cases hk : decodeBits src bits with
  | zero neg =>
    have hden : (powScale 0 1 (src.minExponent - (src.fractionBits : Int))).2 ≠ 0 :=
      Nat.ne_of_gt (Anneal.Mir.IeeeFloatCast.powScale_snd_pos _ _)
    have hz : roundRatioTiesToEven dst neg 0
        (powScale 0 1 (src.minExponent - (src.fractionBits : Int))).2 = zeroBits dst neg := by
      unfold roundRatioTiesToEven; simp [hden]
    show Miri.Interpreter.FloatBits.roundRatio (ieeeFormatToMiri dst) neg 0
        (powScale 0 1 (src.minExponent - (src.fractionBits : Int))).2 = _
    rw [floatBits_roundRatio_eq dst neg 0 _ hden, hz, ← Anneal.Mir.IeeeFloatCast.convertFloatBits_tiesToEven,
      Anneal.Mir.IeeeFloatCast.convertFloatBits_of_zero _ _ _ _ _ hk]
  | finite neg n d =>
    have hd := Anneal.Mir.IeeeFloatCast.decodeBits_finite_den_pos src bits neg n d hk
    show Miri.Interpreter.FloatBits.roundRatio (ieeeFormatToMiri dst) neg n d = _
    rw [floatBits_roundRatio_eq dst neg n d (Nat.ne_of_gt hd), ← Anneal.Mir.IeeeFloatCast.convertFloatBits_tiesToEven,
      Anneal.Mir.IeeeFloatCast.convertFloatBits_of_finite _ _ _ _ _ _ _ hk]
    rfl
  | inf neg =>
    show (pure (Miri.Interpreter.FloatBits.infinity (ieeeFormatToMiri dst) neg) :
      Except Miri.Interpreter.FloatError Miri.Interpreter.FloatBits) = _
    rw [floatBits_infinity_eq, ← Anneal.Mir.IeeeFloatCast.convertFloatBits_tiesToEven,
      Anneal.Mir.IeeeFloatCast.convertFloatBits_of_inf _ _ _ _ _ hk]
    rfl
  | nan neg q payload =>
    rw [Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_of_nan src dst bits neg q payload hk]
    simp only [floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri,
      ieeeFormatToMiri_fractionBits, ieeeFormatToMiri_exponentBits, ge_iff_le, miri_encode_eq]
    rfl

/-! ## Part 3. NaN classification and NaN choices -/

theorem floatBits_isNaN_eq (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    Miri.Interpreter.FloatBits.isNaN ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩ =
      .ok (Anneal.Mir.IeeeFloatCast.isNaNBits f bits) := by
  unfold Miri.Interpreter.FloatBits.isNaN Anneal.Mir.IeeeFloatCast.isNaNBits
  rw [floatBits_decode_eq f bits h]
  cases decodeBits f bits <;> rfl

/-- The quiet bit of an in-width NaN payload is clear exactly when the payload is
below `2 ^ (fractionBits - 1)` (Miri's `isSignaling` test). -/
theorem quietBit_eq_not_lt (f : IeeeFormat) (payload : Nat) (hp : payload < 2 ^ f.fractionBits) :
    Nat.beq ((payload / 2 ^ (f.fractionBits - 1)) % 2) 1 = !decide (payload < 2 ^ (f.fractionBits - 1)) := by
  have hsplit : 2 ^ f.fractionBits = 2 * 2 ^ (f.fractionBits - 1) := by cases f <;> decide
  have hpos := Nat.two_pow_pos (f.fractionBits - 1)
  by_cases hlt : payload < 2 ^ (f.fractionBits - 1)
  · have h0 : payload / 2 ^ (f.fractionBits - 1) = 0 := Nat.div_eq_of_lt hlt
    rw [h0]; simp only [hlt, decide_true, Bool.not_true]; rfl
  · have h1 : payload / 2 ^ (f.fractionBits - 1) = 1 := by
      apply Nat.le_antisymm
      · have : payload / 2 ^ (f.fractionBits - 1) < 2 :=
          (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
        omega
      · exact (Nat.le_div_iff_mul_le hpos).mpr (by omega)
    rw [h1]; simp only [hlt, decide_false, Bool.not_false]; rfl

/-- `FloatBits.isSignaling` holds exactly on NaNs with a clear quiet bit. -/
theorem floatBits_isSignaling_eq (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    Miri.Interpreter.FloatBits.isSignaling ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩ =
      .ok (match decodeBits f bits with
        | .nan _ q _ => !q
        | _ => false) := by
  unfold Miri.Interpreter.FloatBits.isSignaling
  rw [floatBits_decode_eq f bits h]
  cases hk : decodeBits f bits with
  | nan neg q payload =>
    obtain ⟨_, _, hp, hq⟩ := Anneal.Mir.IeeeFloatCast.decodeBits_nan_payload f bits neg q payload hk
    show Except.ok (decide (payload < 2 ^ ((ieeeFormatToMiri f).fractionBits - 1))) = _
    rw [ieeeFormatToMiri_fractionBits, hq, quietBit_eq_not_lt f payload hp]
    simp only [Bool.not_not]
  | _ => rfl

/-- `FloatBits.negate` flips the sign bit of an in-width pattern. -/
theorem floatBits_negate_eq (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    Miri.Interpreter.FloatBits.negate ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩ =
      .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128
        (if (floatKindToMiriDecoded f (decodeBits f bits)).negative then bits - 2 ^ (f.width - 1)
         else bits + 2 ^ (f.width - 1))⟩ := by
  unfold Miri.Interpreter.FloatBits.negate
  rw [floatBits_decode_eq f bits h]
  simp only [bitVec128_toNat_of_lt_width h, ieeeFormatToMiri_width]
  rfl

/-- Deterministic `nanChoices` is exactly `[preferredNaN]`. -/
theorem floatBits_nanChoices_deterministic (g : Miri.Interpreter.FloatFormat)
    (inputs : List Miri.Interpreter.FloatBits) :
    Miri.Interpreter.FloatBits.nanChoices g inputs false = .ok [Miri.Interpreter.FloatBits.preferredNaN g] :=
  rfl

/-- **NaN-choice membership**: for every NaN input, nondeterministic `nanChoices`
succeeds with `preferredNaN` at index `0` and the `convert` result (the trusted
quieting conversion) at index `2`. -/
theorem floatBits_nanChoices_nondet_eq (src dst : IeeeFormat) (bits : Nat) (h : bits < 2 ^ src.width)
    (neg q : Bool) (payload : Nat) (hnan : decodeBits src bits = .nan neg q payload) :
    ∃ candidates,
      Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
          [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] true = .ok candidates ∧
      candidates[0]? = some (Miri.Interpreter.FloatBits.preferredNaN (ieeeFormatToMiri dst)) ∧
      candidates[2]? =
        some ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩ := by
  have hnanb : Anneal.Mir.IeeeFloatCast.isNaNBits src bits = true :=
    Anneal.Mir.IeeeFloatCast.isNaNBits_of_nan src bits neg q payload hnan
  have hconvlt := Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst bits
  obtain ⟨_, _, hp, _⟩ := Anneal.Mir.IeeeFloatCast.decodeBits_nan_payload src bits neg q payload hnan
  obtain ⟨payload', hplt, hdk⟩ : ∃ p', p' < 2 ^ dst.fractionBits ∧
      decodeBits dst (evalFloatToFloatRoundTiesToEven src dst bits) = .nan neg true p' :=
    ⟨_, Anneal.Mir.IeeeFloatCast.convertNaNPayload_lt src dst payload hp,
      Anneal.Mir.IeeeFloatCast.decodeBits_evalFloatToFloatRoundTiesToEven_of_nan src dst bits neg q
        payload hnan⟩
  have hdecc := floatBits_decode_eq dst _ hconvlt
  rw [hdk] at hdecc
  have hlow : payload' % 2 ^ (dst.fractionBits - 1) < 2 ^ dst.fractionBits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Anneal.Mir.IeeeFloatCast.two_pow_le_two_pow (Nat.sub_le _ _))
  have hnp := floatBits_negate_eq dst _ (Anneal.Mir.IeeeFloatCast.preferredNaNBits_lt dst)
  have hnc := floatBits_negate_eq dst _ hconvlt
  have hns := floatBits_negate_eq dst _
    (Anneal.Mir.IeeeFloatCast.encodeBits_lt dst neg (2 ^ dst.exponentBits - 1)
      (payload' % 2 ^ (dst.fractionBits - 1)) (Nat.sub_lt (Nat.two_pow_pos _) (by decide)) hlow)
  unfold Miri.Interpreter.FloatBits.nanChoices
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.forIn_cons, List.forIn_nil,
    floatBits_isNaN_eq src bits h, hnanb, floatBits_convert_eq src dst bits h,
    floatBits_isSignaling_eq src bits h, hnan, hdecc, floatBits_preferredNaN_eq, hnp,
    bind, Except.bind, pure, Except.pure, List.nil_append,
    floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri,
    ieeeFormatToMiri_fractionBits, ieeeFormatToMiri_exponentBits, miri_encode_eq]
  cases q
  · by_cases hl : (payload' % 2 ^ (dst.fractionBits - 1) != 0) = true
    · simp only [Bool.not_false, ↓reduceIte, hl, List.forIn_cons, List.forIn_nil, hnc, hns, bind,
        Except.bind, pure, Except.pure, List.nil_append, List.cons_append]
      exact ⟨_, rfl, rfl, rfl⟩
    · simp only [Bool.not_false, ↓reduceIte, hl, Bool.false_eq_true, List.forIn_cons,
        List.forIn_nil, hnc, bind, Except.bind, pure, Except.pure, List.nil_append, List.cons_append]
      exact ⟨_, rfl, rfl, rfl⟩
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.forIn_cons, List.forIn_nil, hnc,
      bind, Except.bind, pure, Except.pure, List.nil_append, List.cons_append]
    exact ⟨_, rfl, rfl, rfl⟩

/-- `FloatOps.adjustNaN` on a non-NaN converted value returns it unchanged, for any
hooks (`floatNondeterministic` and `chooseNaN` are never consulted). -/
theorem floatOps_adjustNaN_of_not_nan {P S C : Type} (h : Miri.Interpreter.FloatOpsHooks P S C)
    (choice : C) (f : IeeeFormat) (bits : Nat) (hlt : bits < 2 ^ f.width)
    (hn : Anneal.Mir.IeeeFloatCast.isNaNBits f bits = false)
    (inputs : List Miri.Interpreter.FloatBits) (st : S) :
    Miri.Interpreter.FloatOps.adjustNaN h choice ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩ inputs st =
      .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩ st := by
  unfold Miri.Interpreter.FloatOps.adjustNaN
  simp only [floatBits_isNaN_eq f bits hlt, hn]
  rfl

/-- **NaN refinement witness**: with `floatNondeterministic := true` and a `chooseNaN`
that always selects index `2`, `FloatOps.adjustNaN` returns exactly the quieting
conversion `evalFloatToFloatRoundTiesToEven src dst bits`, on every `src` bit pattern
(non-NaN inputs pass through; a NaN input selects `nanChoices`' candidate `2`, which is
the `convert` result). -/
theorem floatOps_adjustNaN_convert_refine {P S C : Type} (h : Miri.Interpreter.FloatOpsHooks P S C)
    (choice : C) (hnd : h.floatNondeterministic = true)
    (hchoose : ∀ c l, h.chooseNaN c l = pure 2)
    (src dst : IeeeFormat) (bits : Nat) (hlt : bits < 2 ^ src.width) (st : S) :
    Miri.Interpreter.FloatOps.adjustNaN h choice
        ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩
        [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] st =
      .ok ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩ st := by
  have hclt := Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst bits
  have hiff := Anneal.Mir.IeeeFloatCast.isNaNBits_evalFloatToFloatRoundTiesToEven src dst bits
  cases hsn : Anneal.Mir.IeeeFloatCast.isNaNBits src bits with
  | false =>
    rw [hsn] at hiff
    exact floatOps_adjustNaN_of_not_nan h choice dst _ hclt hiff _ st
  | true =>
    rw [hsn] at hiff
    have hdec : ∃ neg q payload, decodeBits src bits = .nan neg q payload := by
      unfold Anneal.Mir.IeeeFloatCast.isNaNBits at hsn
      split at hsn
      · rename_i neg q payload hk; exact ⟨neg, q, payload, hk⟩
      · cases hsn
    obtain ⟨neg, q, payload, hk⟩ := hdec
    obtain ⟨cands, hc, _, h2⟩ := floatBits_nanChoices_nondet_eq src dst bits hlt neg q payload hk
    unfold Miri.Interpreter.FloatOps.adjustNaN
    simp only [floatBits_isNaN_eq dst _ hclt, hiff, hnd, hc, hchoose, floatOps_engine_ok, pure_bind,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, h2]
    rfl

/-- With `floatNondeterministic := false`, `FloatOps.adjustNaN` maps every NaN result to
`preferredNaN` and passes every non-NaN result through. -/
theorem floatOps_adjustNaN_deterministic {P S C : Type} (h : Miri.Interpreter.FloatOpsHooks P S C)
    (choice : C) (hnd : h.floatNondeterministic = false)
    (src dst : IeeeFormat) (bits : Nat) (st : S) :
    Miri.Interpreter.FloatOps.adjustNaN h choice
        ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩
        [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] st =
      .ok (if Anneal.Mir.IeeeFloatCast.isNaNBits src bits then
          ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (preferredNaNBits dst)⟩
        else ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩) st := by
  have hclt := Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst bits
  have hiff := Anneal.Mir.IeeeFloatCast.isNaNBits_evalFloatToFloatRoundTiesToEven src dst bits
  cases hsn : Anneal.Mir.IeeeFloatCast.isNaNBits src bits with
  | false =>
    rw [hsn] at hiff
    exact floatOps_adjustNaN_of_not_nan h choice dst _ hclt hiff _ st
  | true =>
    rw [hsn] at hiff
    unfold Miri.Interpreter.FloatOps.adjustNaN
    simp only [floatBits_isNaN_eq dst _ hclt, hiff, hnd, floatBits_nanChoices_deterministic,
      floatBits_preferredNaN_eq, floatOps_engine_ok, pure_bind, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte]
    rfl

/-! ## Part 4. Float-cast hook overlay -/

/-- Encoded `TyId` of an `IeeeFormat` (`encodeTyId` of `f32` / `f64`). -/
def floatTyIdOf : IeeeFormat → Miri.MIR.TyId
  | .binary32 => 31
  | .binary64 => 32

/-- `CastTypeInfo` classification extending `castTypeInfoOfEncodedTyId` with `f32`
(`31` ↦ `.floating .binary32`) and `f64` (`32` ↦ `.floating .binary64`); `f16` (`30`)
and `f128` (`33`) keep failing closed with `StepError.unsupported`, matching
`ieeeFormatOfTy?`. -/
def castTypeInfoOfEncodedTyIdFloat (tyId : Miri.MIR.TyId) :
    Except Miri.Interpreter.StepError Miri.Interpreter.CastTypeInfo :=
  if tyId == 31 then .ok (.floating .binary32)
  else if tyId == 32 then .ok (.floating .binary64)
  else castTypeInfoOfEncodedTyId tyId

/-- `FloatFormat` of an encoded float `TyId` (`f32` / `f64` only). -/
def floatFormatOfEncodedTyId (tyId : Miri.MIR.TyId) :
    Except Miri.Interpreter.StepError Miri.Interpreter.FloatFormat :=
  if tyId == 31 then .ok .binary32
  else if tyId == 32 then .ok .binary64
  else .error (.unsupported s!"floatOps.formatOf: TyId {tyId} is not f32/f64")

/-- The NaN-choice refinement witness: always pick `nanChoices`' candidate `2`,
the `convert` (quieting NaN propagation) result. -/
def annealChooseQuietedNaN : Unit → List Miri.Interpreter.FloatBits →
    Miri.Interpreter.RvalueM AnnealStepState Nat :=
  fun _ _ => pure 2

/-- `FloatOpsHooks` for Anneal's machine. -/
def annealFloatOpsHooks (nondet : Bool := true)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat := annealChooseQuietedNaN) :
    Miri.Interpreter.FloatOpsHooks AnnealProv AnnealStepState Unit where
  integerKindOf := fun _ tyId => annealIntegerKindOf tyId
  formatOf := fun _ tyId =>
    match floatFormatOfEncodedTyId tyId with
    | .ok f => pure f
    | .error err => throw err
  boolLayout := fun _ => pure (translateTy { kind := .bool, layoutIdx := 0 })
  floatNondeterministic := nondet
  chooseNaN := chooseNaN

/-- `CastHooks` overlay over `annealCastHooks` with float classification and float ops. -/
def annealCastHooksFloat (layouts : LayoutTable := emptyLayoutTable) (nondet : Bool := true)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat := annealChooseQuietedNaN) :
    Miri.Interpreter.CastHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealCastHooks layouts with
    typeInfo := fun _ tyId =>
      match castTypeInfoOfEncodedTyIdFloat tyId with
      | .ok info => pure info
      | .error err => throw err
    floatOps := annealFloatOpsHooks nondet chooseNaN }

/-- `ieeeFormatOfTy?` succeeds exactly on `f32` / `f64`. -/
theorem ieeeFormatOfTy?_kind {ty : Ty} {f : IeeeFormat} (h : ieeeFormatOfTy? ty = some f) :
    (ty.kind = .float .f32 ∧ f = .binary32) ∨ (ty.kind = .float .f64 ∧ f = .binary64) := by
  rcases ty with ⟨kind, li⟩
  unfold ieeeFormatOfTy? at h
  dsimp only at h ⊢
  split at h
  · exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  · exact Or.inr ⟨rfl, (Option.some.inj h).symm⟩
  · cases h

/-- Layout of an `f32` / `f64` type. -/
theorem translateTy_of_ieeeFormatOfTy? {ty : Ty} {f : IeeeFormat} (h : ieeeFormatOfTy? ty = some f)
    (layouts : LayoutTable) :
    translateTy ty layouts = { ty := floatTyIdOf f, layout := floatLayoutData f.byteWidth } := by
  rcases ieeeFormatOfTy?_kind h with ⟨hk, rfl⟩ | ⟨hk, rfl⟩ <;>
    simp only [translateTy, encodeTyId, hk] <;> rfl

/-- Float classification of `f32` / `f64` TyIds. -/
theorem castTypeInfoOfEncodedTyIdFloat_floatTyIdOf (f : IeeeFormat) :
    castTypeInfoOfEncodedTyIdFloat (floatTyIdOf f) = .ok (.floating (ieeeFormatToMiri f)) := by
  cases f <;> rfl

theorem floatFormatOfEncodedTyId_floatTyIdOf (f : IeeeFormat) :
    floatFormatOfEncodedTyId (floatTyIdOf f) = .ok (ieeeFormatToMiri f) := by
  cases f <;> rfl

theorem floatLayoutData_size (f : IeeeFormat) :
    (floatLayoutData f.byteWidth).size = (ieeeFormatToMiri f).size := by
  cases f <;> rfl

theorem scalarModulus_byteWidth (f : IeeeFormat) : scalarModulus f.byteWidth = 2 ^ f.width := by
  cases f <;> decide

theorem validScalarBytes_byteWidth (f : IeeeFormat) : ValidScalarBytes f.byteWidth := by
  cases f
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem translateSizeBytes_byteWidth (f : IeeeFormat) :
    translateSizeBytes f.byteWidth = (ieeeFormatToMiri f).size := by
  cases f <;> rfl

/-! ## Part 5. `Cast.cast` simulation -/

/-- Vendored `Miri.Interpreter.Cast.liftResult` (`private`, `Cast.lean:70-71`). -/
local macro "miriCastLiftResult" : term =>
  `(miri_private% Miri.Interpreter.Cast Miri.Interpreter.Cast.liftResult)
/-- Vendored `Miri.Interpreter.FloatOps.readScalarBits` (`private`, `FloatOps.lean:27-32`). -/
local macro "miriReadScalarBits" : term =>
  `(miri_private% Miri.Interpreter.FloatOps Miri.Interpreter.FloatOps.readScalarBits)
/-- Vendored `Miri.Interpreter.FloatOps.liftResult` (`private`, `FloatOps.lean:18-19`). -/
local macro "miriFloatOpsLiftResult" : term =>
  `(miri_private% Miri.Interpreter.FloatOps Miri.Interpreter.FloatOps.liftResult)

theorem cast_liftResult_ok {S A : Type} (v : A) :
    (miriCastLiftResult (Except.ok v : Except Miri.Interpreter.StepError A) :
      Miri.Interpreter.RvalueM S A) = pure v := rfl

theorem cast_liftResult_error {S A : Type} (e : Miri.Interpreter.StepError) :
    (miriCastLiftResult (Except.error e : Except Miri.Interpreter.StepError A) :
      Miri.Interpreter.RvalueM S A) = throw e := rfl

theorem floatOps_liftResult_ok {S A : Type} (v : A) :
    (miriFloatOpsLiftResult (Except.ok v : Except Miri.Interpreter.StepError A) :
      Miri.Interpreter.RvalueM S A) = pure v := rfl

theorem annealReadImmediate_scalar (s : Miri.Memory.Scalar AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    annealReadImmediate ⟨.immediate (.scalar s), lay⟩ = pure ⟨.scalar s, lay⟩ := rfl

theorem floatOps_readScalarBits_unfold {P S C : Type} [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.FloatOpsHooks P S C) (choice : C)
    (value : Miri.Interpreter.RvalueImmTy P) (scalar : Miri.Memory.Scalar P) :
    miriReadScalarBits h choice value scalar = (do
      let format ← h.formatOf choice value.layout.ty
      if value.layout.layout.size != format.size then
        throw (Miri.Interpreter.StepError.invalidProgram "float operand layout size mismatch")
      let bits ← miriFloatOpsLiftResult
        (scalar.toBits format.size |>.mapError Miri.Interpreter.ScalarOps.scalarError)
      return ⟨format, bits⟩) := rfl

theorem floatOps_readBits_annealFloat (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (f : IeeeFormat) {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : sc.sizeBytes = f.byteWidth) :
    Miri.Interpreter.FloatOps.readBits (annealFloatOpsHooks nondet chooseNaN) ()
        ⟨.scalar (.fromScalarInt msc), ⟨floatTyIdOf f, floatLayoutData f.byteWidth⟩⟩ =
      pure ⟨ieeeFormatToMiri f, BitVec.ofNat 128 sc.bits⟩ := by
  have htoBits : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBits
      (ieeeFormatToMiri f).size = .ok (BitVec.ofNat 128 sc.bits) := by
    rw [← translateSizeBytes_byteWidth, ← hsz]; exact scalar_fromScalarInt_toBits_eq hrel
  unfold Miri.Interpreter.FloatOps.readBits
  simp only [floatOps_readScalarBits_unfold, Miri.Interpreter.Immediate.toScalar, Except.mapError,
    floatOps_liftResult_ok, pure_bind, annealFloatOpsHooks, floatFormatOfEncodedTyId_floatTyIdOf, floatLayoutData_size,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, htoBits, Except.mapError, pure_bind]

theorem floatOps_adjustNaN_annealFloat_refine (src dst : IeeeFormat) (bits : Nat)
    (hlt : bits < 2 ^ src.width) :
    Miri.Interpreter.FloatOps.adjustNaN (annealFloatOpsHooks true annealChooseQuietedNaN) ()
        ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩
        [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] =
      pure ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩ := by
  funext st
  exact floatOps_adjustNaN_convert_refine _ () rfl (fun _ _ => rfl) src dst bits hlt st

/-- **`Cast.cast .FloatToFloat` simulation** (refinement witness): an initialized
immediate `f32` / `f64` source of any bit pattern writes the `ScalarRel`-related
`evalFloatToFloatRoundTiesToEven` result. -/
theorem cast_floatToFloat_eq (layouts : LayoutTable) {srcTy targetTy : Ty} {src dst : IeeeFormat}
    (hsrc : ieeeFormatOfTy? srcTy = some src) (hdst : ieeeFormatOfTy? targetTy = some dst)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : sc.sizeBytes = src.byteWidth) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    ∃ msc', ScalarRel ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩ msc' ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩ .FloatToFloat
          (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨destRef, translateTy targetTy layouts⟩ := by
  have hbits : sc.bits < 2 ^ src.width := by
    have := hrel.canonical; rwa [hsz, scalarModulus_byteWidth] at this
  have hclt := Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst sc.bits
  obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec
    (validScalarBytes_byteWidth dst) (caseVal := evalFloatToFloatRoundTiesToEven src dst sc.bits)
    (by rw [scalarModulus_byteWidth]; exact hclt)
  refine ⟨msc', hrel', ?_⟩
  have htoBits : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBits
      (ieeeFormatToMiri src).size = .ok (BitVec.ofNat 128 sc.bits) := by
    rw [← translateSizeBytes_byteWidth, ← hsz]; exact scalar_fromScalarInt_toBits_eq hrel
  have hsrcT := translateTy_of_ieeeFormatOfTy? hsrc layouts
  have hdstT := translateTy_of_ieeeFormatOfTy? hdst layouts
  have henc : encodeTyId targetTy = floatTyIdOf dst := congrArg (·.ty) hdstT
  rw [translateSizeBytes_byteWidth] at hfrom
  rw [hsrcT, hdstT, henc]
  unfold Miri.Interpreter.Cast.cast
  simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true,
    ↓reduceIte, castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true,
    annealReadImmediate_scalar, floatOps_readBits_annealFloat true annealChooseQuietedNaN src hrel hsz,
    floatBits_convert_eq src dst sc.bits hbits, Except.mapError, cast_liftResult_ok,
    floatOps_adjustNaN_annealFloat_refine src dst sc.bits hbits, floatLayoutData_size,
    bne_self_eq_false, hfrom]

/-! ### Integer targets -/

/-- Encoded `TyId` of an integer target (`encodeTyId` of `i8..isize` / `u8..usize`). -/
def floatIntTargetTyId : FloatIntTarget → Miri.MIR.TyId
  | .signed .i8 => 10
  | .signed .i16 => 11
  | .signed .i32 => 12
  | .signed .i64 => 13
  | .signed .i128 => 14
  | .signed .isize => 15
  | .unsigned .u8 => 20
  | .unsigned .u16 => 21
  | .unsigned .u32 => 22
  | .unsigned .u64 => 23
  | .unsigned .u128 => 24
  | .unsigned .usize => 25

/-- `lean-miri` integer kind of an integer target (64-bit `isize` / `usize`). -/
def floatIntTargetKind : FloatIntTarget → Miri.MIR.IntegerKind
  | .signed it => translateIntTy it
  | .unsigned ut => translateUintTy ut

theorem floatIntTargetOfTy?_kind {ty : Ty} {t : FloatIntTarget} (h : floatIntTargetOfTy? ty = some t) :
    (∃ it, ty.kind = .int it ∧ t = .signed it) ∨ (∃ ut, ty.kind = .uint ut ∧ t = .unsigned ut) := by
  rcases ty with ⟨kind, li⟩
  unfold floatIntTargetOfTy? at h
  dsimp only at h ⊢
  split at h
  · exact Or.inl ⟨_, rfl, (Option.some.inj h).symm⟩
  · exact Or.inr ⟨_, rfl, (Option.some.inj h).symm⟩
  · cases h

theorem translateTy_of_floatIntTargetOfTy? {ty : Ty} {t : FloatIntTarget}
    (h : floatIntTargetOfTy? ty = some t) (layouts : LayoutTable) :
    translateTy ty layouts =
      { ty := floatIntTargetTyId t, layout := scalarLayoutData (t.bitWidth .bits64 / 8) t.isSigned } := by
  rcases floatIntTargetOfTy?_kind h with ⟨it, hk, rfl⟩ | ⟨ut, hk, rfl⟩
  · cases it <;> simp only [translateTy, encodeTyId, hk] <;> rfl
  · cases ut <;> simp only [translateTy, encodeTyId, hk] <;> rfl

theorem castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId (t : FloatIntTarget) :
    castTypeInfoOfEncodedTyIdFloat (floatIntTargetTyId t) = .ok (.integer (floatIntTargetKind t)) := by
  cases t <;> rename_i w <;> cases w <;> rfl

theorem floatIntTargetKind_signed (t : FloatIntTarget) : (floatIntTargetKind t).signed = t.isSigned := by
  cases t <;> rename_i w <;> cases w <;> rfl

theorem scalarLayoutData_floatIntTarget_size (t : FloatIntTarget) (s : Bool) :
    (scalarLayoutData (t.bitWidth .bits64 / 8) s).size = translateSizeBytes (t.bitWidth .bits64 / 8) := by
  cases t <;> rename_i w <;> cases w <;> rfl

theorem scalarLayoutData_floatIntTarget_bitsNat (t : FloatIntTarget) (s : Bool) :
    (scalarLayoutData (t.bitWidth .bits64 / 8) s).size.bitsNat = .ok (t.bitWidth .bits64) := by
  cases t <;> rename_i w <;> cases w <;> rfl

theorem translateSizeBytes_floatIntTarget_bitsNat (t : FloatIntTarget) :
    (translateSizeBytes (t.bitWidth .bits64 / 8)).bitsNat = .ok (t.bitWidth .bits64) := by
  cases t <;> rename_i w <;> cases w <;> rfl

theorem scalarLayoutData_floatIntTarget_isSigned (t : FloatIntTarget) (s : Bool) :
    (scalarLayoutData (t.bitWidth .bits64 / 8) s).backendRepr.isSigned = .ok s := by
  cases t <;> rename_i w <;> cases w <;> cases s <;> rfl

theorem validScalarBytes_floatIntTarget (t : FloatIntTarget) :
    ValidScalarBytes (t.bitWidth .bits64 / 8) := by
  cases t <;> rename_i w <;> cases w <;> simp [ValidScalarBytes, FloatIntTarget.bitWidth,
    IntTy.bitWidth, UintTy.bitWidth, FloatPtrWidth.bits]

theorem floatIntTarget_bitWidth_eq (t : FloatIntTarget) :
    8 * (t.bitWidth .bits64 / 8) = t.bitWidth .bits64 := by
  cases t <;> rename_i w <;> cases w <;> rfl

/-- `annealFloatOpsHooks.integerKindOf` is wired on all twelve encoded integer TyIds
(`10..15` ↦ `i8..i128, isize`, `20..25` ↦ `u8..u128, usize`, 64-bit target). -/
theorem annealFloatOpsHooks_integerKindOf (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (t : FloatIntTarget) :
    (annealFloatOpsHooks nondet chooseNaN).integerKindOf () (floatIntTargetTyId t) =
      pure (floatIntTargetKind t) := by
  cases t <;> rename_i w <;> cases w <;> rfl

/-- `annealFloatOpsHooks.formatOf` resolves `f32` / `f64` TyIds. -/
theorem annealFloatOpsHooks_formatOf (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (f : IeeeFormat) :
    (annealFloatOpsHooks nondet chooseNaN).formatOf () (floatTyIdOf f) = pure (ieeeFormatToMiri f) := by
  cases f <;> rfl

/-- `Scalar.fromInt` succeeds on every value of a signed integer range, producing the
canonical two's-complement scalar. -/
theorem scalar_fromInt_spec {sz : Nat} (hsz : ValidScalarBytes sz) (v : Int)
    (hlo : -(2 : Int) ^ (8 * sz - 1) ≤ v) (hhi : v < (2 : Int) ^ (8 * sz - 1)) :
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.Scalar.fromInt (Prov := AnnealProv) v (translateSizeBytes sz) =
        .ok (.fromScalarInt msc) ∧
      ScalarRel ⟨(v % (2 : Int) ^ (8 * sz)).toNat, sz⟩ msc := by
  have ⟨hw128, hw0⟩ := validScalarBytes_bits_le_128 hsz
  have hp127 : (2 : Int) ^ (8 * sz - 1) ≤ 2 ^ 127 := by
    rcases hsz with rfl | rfl | rfl | rfl | rfl <;> decide
  have hi128 : (BitVec.ofInt 128 v).toInt = v :=
    bitVec_toInt_ofInt_eq_of_in_i128 (by omega) (by omega)
  obtain ⟨msc, htr, hrel⟩ := truncateFromInt_ofInt_translateSizeBytes_spec hsz v
  simp only [hi128] at htr
  have hpos : (0 : Int) < (2 : Int) ^ (8 * sz) := Int.pow_pos (by decide)
  have hr_nonneg : 0 ≤ v % (2 : Int) ^ (8 * sz) := Int.emod_nonneg v (Int.ne_of_gt hpos)
  have hr_lt : (v % (2 : Int) ^ (8 * sz)).toNat < 2 ^ (8 * sz) := by
    have := Int.emod_lt_of_pos v hpos
    have h2 : ((2 ^ (8 * sz) : Nat) : Int) = (2 : Int) ^ (8 * sz) := by push_cast; rfl
    omega
  obtain ⟨hD1, hD2, hDmod⟩ := decodeBitsInt_signed_window hsz hr_lt
  have hsplit : (2 : Int) ^ (8 * sz) = 2 * (2 : Int) ^ (8 * sz - 1) := by
    rcases hsz with rfl | rfl | rfl | rfl | rfl <;> decide
  have hdec : decodeBitsInt true sz (v % (2 : Int) ^ (8 * sz)).toNat = v := by
    apply eq_of_emod_eq_of_window hpos (lo := -(2 : Int) ^ (8 * sz - 1)) hD1 (by omega) hlo
      (by omega)
    rw [hDmod, Int.toNat_of_nonneg hr_nonneg]
  rw [hdec, bne_self_eq_false] at htr
  refine ⟨msc, ?_, hrel⟩
  unfold Miri.Memory.Scalar.fromInt Miri.Memory.ScalarInt.tryFromInt
  simp only [htr, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte,
    Except.mapError]

/-- `Scalar.fromUInt (BitVec.ofInt 128 v)` succeeds on every value of an unsigned range. -/
theorem scalar_fromUInt_ofInt_spec {sz : Nat} (hsz : ValidScalarBytes sz) (v : Int)
    (hlo : 0 ≤ v) (hhi : v < (2 : Int) ^ (8 * sz)) :
    ∃ msc : Miri.Memory.ScalarInt,
      Miri.Memory.Scalar.fromUInt (Prov := AnnealProv) (BitVec.ofInt 128 v) (translateSizeBytes sz) =
        .ok (.fromScalarInt msc) ∧
      ScalarRel ⟨v.toNat, sz⟩ msc := by
  have hofInt : BitVec.ofInt 128 v = BitVec.ofNat 128 v.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    have ⟨hw128, _⟩ := validScalarBytes_bits_le_128 hsz
    have h128 : v < ((2 ^ 128 : Nat) : Int) := by
      have : (2 : Int) ^ (8 * sz) ≤ 2 ^ 128 := by
        rcases hsz with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [Int.natCast_pow]; exact Int.lt_of_lt_of_le hhi this
    rw [Int.emod_eq_of_lt hlo h128]
    have hlt : v.toNat < 2 ^ 128 := by omega
    exact (Nat.mod_eq_of_lt hlt).symm
  rw [hofInt]
  apply scalar_fromUInt_translateSizeBytes_spec hsz
  rw [scalarModulus_eq_two_pow]
  have h2 : ((2 ^ (8 * sz) : Nat) : Int) = (2 : Int) ^ (8 * sz) := by push_cast; rfl
  omega

/-- The float-to-int result scalar of `Cast.cast` (`Scalar.fromInt` / `Scalar.fromUInt` of
`toInteger`) is `ScalarRel`-related to `evalFloatToIntSaturating`. -/
theorem floatToInt_scalar_spec (src : IeeeFormat) (bits : Nat) (t : FloatIntTarget) :
    ∃ msc : Miri.Memory.ScalarInt,
      (if t.isSigned then
          Miri.Memory.Scalar.fromInt (Prov := AnnealProv)
            (floatToIntValue (decodeBits src bits) (t.minValue .bits64) (t.maxValue .bits64))
            (translateSizeBytes (t.bitWidth .bits64 / 8))
        else
          Miri.Memory.Scalar.fromUInt (Prov := AnnealProv)
            (BitVec.ofInt 128
              (floatToIntValue (decodeBits src bits) (t.minValue .bits64) (t.maxValue .bits64)))
            (translateSizeBytes (t.bitWidth .bits64 / 8))) = .ok (.fromScalarInt msc) ∧
      ScalarRel (evalFloatToIntSaturating src bits t .bits64) msc := by
  have hv := validScalarBytes_floatIntTarget t
  have hw8 := floatIntTarget_bitWidth_eq t
  obtain ⟨_, _, _, hlo, hhi⟩ := Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_sound src bits t .bits64
  obtain ⟨hmin, hmax⟩ := floatIntTarget_bounds t .bits64
  have hval := (Anneal.Mir.IeeeFloatCast.evalFloatToIntSaturating_sound src bits t .bits64).2.2.1
  generalize hV : floatToIntValue (decodeBits src bits) (t.minValue .bits64) (t.maxValue .bits64) = V
    at hval
  rw [hval] at hlo hhi
  have hlo' : t.minValue .bits64 ≤ V := hlo
  have hhi' : V ≤ t.maxValue .bits64 := hhi
  rw [hmin] at hlo'
  rw [hmax] at hhi'
  have henc : (evalFloatToIntSaturating src bits t .bits64) =
      ⟨encodeTwosComplement (t.bitWidth .bits64) V, t.bitWidth .bits64 / 8⟩ := by
    unfold evalFloatToIntSaturating; rw [hV]
  rw [henc]
  cases hs : t.isSigned
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hlo' hhi' ⊢
    obtain ⟨msc, hfrom, hrel⟩ := scalar_fromUInt_ofInt_spec hv V hlo' (by rw [hw8]; omega)
    refine ⟨msc, hfrom, ?_⟩
    have hencV : encodeTwosComplement (t.bitWidth .bits64) V = V.toNat := by
      unfold encodeTwosComplement
      have h2 : ((2 ^ t.bitWidth .bits64 : Nat) : Int) = (2 : Int) ^ t.bitWidth .bits64 := by
        push_cast; rfl
      rw [h2, Int.emod_eq_of_lt hlo' (by omega)]
    rw [hencV]; exact hrel
  · simp only [hs, ↓reduceIte] at hlo' hhi' ⊢
    obtain ⟨msc, hfrom, hrel⟩ := scalar_fromInt_spec hv V (by rw [hw8]; exact hlo')
      (by rw [hw8]; omega)
    refine ⟨msc, hfrom, ?_⟩
    have hencV : encodeTwosComplement (t.bitWidth .bits64) V =
        (V % (2 : Int) ^ (8 * (t.bitWidth .bits64 / 8))).toNat := by
      unfold encodeTwosComplement
      rw [hw8]
      have h2 : ((2 ^ t.bitWidth .bits64 : Nat) : Int) = (2 : Int) ^ t.bitWidth .bits64 := by
        push_cast; rfl
      rw [h2]
    rw [hencV]; exact hrel

/-- **`Cast.cast .FloatToInt` simulation** (any NaN mode): writes the
`ScalarRel`-related `evalFloatToIntSaturating` result for every integer target. -/
theorem cast_floatToInt_eq (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {srcTy targetTy : Ty} {src : IeeeFormat} {t : FloatIntTarget}
    (hsrc : ieeeFormatOfTy? srcTy = some src) (hdst : floatIntTargetOfTy? targetTy = some t)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : sc.sizeBytes = src.byteWidth) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    ∃ msc', ScalarRel (evalFloatToIntSaturating src sc.bits t .bits64) msc' ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩ .FloatToInt
          (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨destRef, translateTy targetTy layouts⟩ := by
  have hbits : sc.bits < 2 ^ src.width := by
    have := hrel.canonical; rwa [hsz, scalarModulus_byteWidth] at this
  obtain ⟨msc', hfrom, hrel'⟩ := floatToInt_scalar_spec src sc.bits t
  refine ⟨msc', hrel', ?_⟩
  have hsrcT := translateTy_of_ieeeFormatOfTy? hsrc layouts
  have hdstT := translateTy_of_floatIntTargetOfTy? hdst layouts
  have henc : encodeTyId targetTy = floatIntTargetTyId t := congrArg (·.ty) hdstT
  rw [hsrcT, hdstT, henc]
  unfold Miri.Interpreter.Cast.cast
  simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
    castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId,
    pure_bind, Bool.false_eq_true, annealReadImmediate_scalar,
    floatOps_readBits_annealFloat nondet chooseNaN src hrel hsz,
    scalarLayoutData_floatIntTarget_size, translateSizeBytes_floatIntTarget_bitsNat, Except.mapError,
    cast_liftResult_ok, floatIntTargetKind_signed, floatBits_toInteger_eq src sc.bits hbits t .bits64]
  cases hs : t.isSigned
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hfrom ⊢
    simp only [hfrom, cast_liftResult_ok, pure_bind]
  · simp only [hs, ↓reduceIte] at hfrom ⊢
    simp only [hfrom, cast_liftResult_ok, pure_bind]

/-- Vendored `Miri.Interpreter.Cast.scalarOf` (`private`, `Cast.lean:72-73`). -/
local macro "miriCastScalarOf" : term =>
  `(miri_private% Miri.Interpreter.Cast Miri.Interpreter.Cast.scalarOf)

theorem cast_scalarOf_scalar (s : Miri.Memory.Scalar AnnealProv) (lay : Miri.Interpreter.LocalLayout) :
    (miriCastScalarOf (⟨.scalar s, lay⟩ : Miri.Interpreter.RvalueImmTy AnnealProv) :
      Miri.Interpreter.RvalueM AnnealStepState (Miri.Memory.Scalar AnnealProv)) = pure s := rfl

theorem decodeBitsInt_true_eq_intValueOfBits {sz bits : Nat} (hb : bits < 2 ^ (8 * sz)) :
    decodeBitsInt true sz bits = intValueOfBits true (8 * sz) bits := by
  unfold decodeBitsInt intValueOfBits
  simp only [↓reduceIte, true_and, Nat.mod_eq_of_lt hb]
  by_cases hlt : bits < 2 ^ (8 * sz - 1)
  · have hn : ¬ (2 ^ (8 * sz - 1) ≤ bits) := Nat.not_le.mpr hlt
    simp only [hlt, hn, ↓reduceIte]
  · have hy : 2 ^ (8 * sz - 1) ≤ bits := Nat.le_of_not_lt hlt
    simp only [hlt, hy, ↓reduceIte]

/-- The exact source integer that `Cast.castFromIntLike` feeds to `FloatBits.fromInteger`
is `intValueOfBits` of the source scalar. -/
theorem intLike_integer_eq {t : FloatIntTarget} {sc : MirAst.ScalarInt}
    (hsz : sc.sizeBytes = t.bitWidth .bits64 / 8) (hcan : sc.bits < scalarModulus sc.sizeBytes) :
    (if t.isSigned then
        (BitVec.ofInt 128 (decodeBitsInt true sc.sizeBytes sc.bits)).toInt
      else Int.ofNat (BitVec.ofNat 128 sc.bits).toNat) =
      intValueOfBits t.isSigned (t.bitWidth .bits64) sc.bits := by
  have hv := validScalarBytes_floatIntTarget t
  rw [← hsz] at hv
  have hw8 := floatIntTarget_bitWidth_eq t
  rw [← hsz] at hw8
  have hb : sc.bits < 2 ^ (8 * sc.sizeBytes) := by rw [← scalarModulus_eq_two_pow]; exact hcan
  cases hs : t.isSigned
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [bitVec_ofNat_toNat_of_valid hv hcan]
    unfold intValueOfBits
    simp only [Bool.false_eq_true, false_and, ↓reduceIte]
    rw [← hw8, Nat.mod_eq_of_lt hb]
    rfl
  · simp only [↓reduceIte]
    obtain ⟨h1, h2, _⟩ := decodeBitsInt_signed_window hv hb
    have ⟨hw128, _⟩ := validScalarBytes_bits_le_128 hv
    have hp127 : (2 : Int) ^ (8 * sc.sizeBytes - 1) ≤ 2 ^ 127 := by
      rcases hv with h | h | h | h | h <;> rw [h] <;> decide
    rw [bitVec_toInt_ofInt_eq_of_in_i128 (by omega) (by omega), ← hw8]
    exact decodeBitsInt_true_eq_intValueOfBits hb

/-- **`Cast.cast .IntToFloat` simulation** (any NaN mode): an integer source of
every width and signedness writes the `ScalarRel`-related
`evalIntToFloatRoundTiesToEven` result through `Cast.castFromIntLike`. -/
theorem cast_intToFloat_eq (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {srcTy targetTy : Ty} {t : FloatIntTarget} {dst : IeeeFormat}
    (hsrc : floatIntTargetOfTy? srcTy = some t) (hdst : ieeeFormatOfTy? targetTy = some dst)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : sc.sizeBytes * 8 = t.bitWidth .bits64)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    ∃ msc', ScalarRel
        ⟨evalIntToFloatRoundTiesToEven t.isSigned (t.bitWidth .bits64) sc.bits dst, dst.byteWidth⟩ msc' ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩ .IntToFloat
          (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨destRef, translateTy targetTy layouts⟩ := by
  have hsz8 : sc.sizeBytes = t.bitWidth .bits64 / 8 := by
    have := floatIntTarget_bitWidth_eq t; omega
  have hclt := Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_lt t.isSigned
    (t.bitWidth .bits64) sc.bits dst
  obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec
    (validScalarBytes_byteWidth dst)
    (caseVal := evalIntToFloatRoundTiesToEven t.isSigned (t.bitWidth .bits64) sc.bits dst)
    (by rw [scalarModulus_byteWidth]; exact hclt)
  rw [translateSizeBytes_byteWidth] at hfrom
  refine ⟨msc', hrel', ?_⟩
  have hsrcT := translateTy_of_floatIntTargetOfTy? hsrc layouts
  have hdstT := translateTy_of_ieeeFormatOfTy? hdst layouts
  have henc : encodeTyId targetTy = floatTyIdOf dst := congrArg (·.ty) hdstT
  have hsize : translateSizeBytes (t.bitWidth .bits64 / 8) = translateSizeBytes sc.sizeBytes := by
    rw [hsz8]
  have htoInt := scalar_fromScalarInt_toInt_eq (Prov := AnnealProv) hrel
  have htoBits := scalar_fromScalarInt_toBits_eq (Prov := AnnealProv) hrel
  have hint := intLike_integer_eq hsz8 hrel.canonical
  rw [hsrcT, hdstT, henc]
  unfold Miri.Interpreter.Cast.cast
  simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
    castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId,
    pure_bind, Bool.false_eq_true, annealReadImmediate_scalar, cast_scalarOf_scalar]
  unfold Miri.Interpreter.Cast.castFromIntLike Miri.Interpreter.Cast.intLikeValue
  simp only [scalarLayoutData_floatIntTarget_isSigned, castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId,
    castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, floatIntTargetKind_signed, pure_bind,
    scalarLayoutData_floatIntTarget_size, hsize, htoInt, Miri.Memory.Scalar.toUInt, htoBits,
    Except.mapError, cast_liftResult_ok]
  cases hs : t.isSigned
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hint hfrom ⊢
    simp only [pure_bind, hint, floatBits_fromInteger_intValueOfBits, cast_liftResult_ok,
      floatLayoutData_size, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hfrom]
  · simp only [hs, ↓reduceIte] at hint hfrom ⊢
    simp only [pure_bind, hint, floatBits_fromInteger_intValueOfBits, cast_liftResult_ok,
      floatLayoutData_size, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hfrom]

/-! ## Part 6. Rvalue and step overlay, conservative extension -/

/-- `RvalueHooks` overlay over `annealRvalueHooks` dispatching casts to
`Miri.Interpreter.Cast.cast` under `annealCastHooksFloat`. -/
def annealRvalueHooksFloat (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) (nondet : Bool := true)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat := annealChooseQuietedNaN) :
    Miri.Interpreter.RvalueHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealRvalueHooks localDecls layouts with
    cast := fun c src kind ty dest =>
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) c 16 src kind ty dest }

/-- `true` exactly on the three float `CastKind`s. -/
def isFloatCastKind : Miri.MIR.CastKind → Bool
  | .FloatToInt | .FloatToFloat | .IntToFloat => true
  | _ => false

/-- `true` exactly on `Rvalue.Cast` with a float `CastKind`. -/
def isFloatCastRvalue : Miri.MIR.Rvalue → Bool
  | .Cast kind _ _ => isFloatCastKind kind
  | _ => false

/-- Conservative `StepHooks` overlay: float-cast assignments run through
`annealRvalueHooksFloat`; every other statement and every terminator is delegated to
`annealStepHooks` unchanged. -/
def annealStepHooksFloat (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) (nondet : Bool := true)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat := annealChooseQuietedNaN) :
    Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealStepHooks localDecls layouts
  { base with
    assign := fun choice place rvalue state =>
      if isFloatCastRvalue rvalue then
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooksFloat localDecls layouts nondet chooseNaN) choice rvalue place)
          state
      else base.assign choice place rvalue state }

/-- Whether a `Miri.MIR.Statement` is outside the float-cast `assign` overlay. -/
def stmtFreeOfFloatCast (stmt : Miri.MIR.Statement) : Prop :=
  match stmt.kind with
  | .Assign _ rvalue => isFloatCastRvalue rvalue = false
  | _ => True

/-- **Conservative extension** at the statement level. -/
theorem evalStatement_float_eq_of_stmtFree {localDecls : List LocalDecl} {layouts : LayoutTable}
    {nondet : Bool}
    {chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat}
    {stmt : Miri.MIR.Statement} (hfree : stmtFreeOfFloatCast stmt)
    (choice : Unit) (state : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooksFloat localDecls layouts nondet chooseNaN)
        choice stmt state =
      Miri.Interpreter.Step.evalStatement (annealStepHooks localDecls layouts) choice stmt state := by
  rcases stmt with ⟨si, kind⟩
  cases kind with
  | Assign place rvalue =>
      dsimp [stmtFreeOfFloatCast] at hfree
      simp [Miri.Interpreter.Step.evalStatement, annealStepHooksFloat, hfree]
  | SetDiscriminant _ _ | StorageLive _ | StorageDead _ | Intrinsic _ | PlaceMention _
  | ConstEvalCounter | FakeRead _ | AscribeUserType _ _ | Coverage _
  | Nop | BackwardIncompatibleDropHint _ _ =>
      rfl

/-- Whether every statement of every basic block of `body` is outside the overlay. -/
def BodyFreeOfFloatCast (body : Miri.MIR.Body) : Prop :=
  ∀ bb ∈ body.basicBlocks.toList, ∀ stmt ∈ bb.statements.toList, stmtFreeOfFloatCast stmt

/-- **Conservative extension**: on a body without float-cast assignments
`annealStepHooksFloat` steps exactly as `annealStepHooks` (terminators are never
intercepted). -/
theorem step_float_eq_annealStepHooks_of_bodyFree {localDecls : List LocalDecl}
    {layouts : LayoutTable} {nondet : Bool}
    {chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat}
    {state : AnnealStepState}
    (hfree : ∀ frame, state.stack.currentFrame? = some frame → BodyFreeOfFloatCast frame.body)
    (choice : Unit) :
    Miri.Interpreter.Step.step (annealStepHooksFloat localDecls layouts nondet chooseNaN) choice state =
      Miri.Interpreter.Step.step (annealStepHooks localDecls layouts) choice state := by
  unfold Miri.Interpreter.Step.step
  cases hcf : state.stack.currentFrame? with
  | none => rfl
  | some frame =>
      dsimp only [Id.run]
      cases hloc : frame.location with
      | unwinding _ => rfl
      | mir loc =>
          dsimp only
          cases hbb : frame.body.basicBlocks[loc.block]? with
          | none => rfl
          | some bb =>
              have hbb_mem : bb ∈ frame.body.basicBlocks.toList := by
                obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hbb
                exact Array.getElem_mem_toList hlt
              dsimp only
              cases hst : bb.statements[loc.statementIndex]? with
              | none => rfl
              | some stmt =>
                  have hst_mem : stmt ∈ bb.statements.toList := by
                    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hst
                    exact Array.getElem_mem_toList hlt
                  dsimp only
                  rw [evalStatement_float_eq_of_stmtFree (hfree frame hcf bb hbb_mem stmt hst_mem)]

/-- Integer and pointer `TyId`s classify identically under both cast hooks. -/
theorem castTypeInfoOfEncodedTyIdFloat_eq_of_ne {tyId : Miri.MIR.TyId} (h31 : tyId ≠ 31)
    (h32 : tyId ≠ 32) : castTypeInfoOfEncodedTyIdFloat tyId = castTypeInfoOfEncodedTyId tyId := by
  unfold castTypeInfoOfEncodedTyIdFloat
  simp [h31, h32]

/-- `f16` and `f128` keep failing closed under the float overlay. -/
theorem castTypeInfoOfEncodedTyIdFloat_f16_f128 :
    (∃ msg, castTypeInfoOfEncodedTyIdFloat 30 = .error (.unsupported msg)) ∧
    (∃ msg, castTypeInfoOfEncodedTyIdFloat 33 = .error (.unsupported msg)) :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- Statement-level reduction of a float-cast assignment under `annealStepHooksFloat`. -/
theorem evalStatement_assign_floatCast_eq (ld : List LocalDecl) (ly : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (dst : Place) (kind : CastKind) (hk : isFloatCastKind (translateCastKind kind) = true)
    (op : MirAst.Operand) (castTy : Ty) (span : String) (m : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooksFloat ld ly nondet chooseNaN) ()
      (translateStmt ⟨.assign dst (.cast kind op castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (do
          let destPlace ← annealEvalPlace ld ly (translatePlace dst)
          let src ← annealEvalOperand ld ly (translateOperand op) none
          Miri.Interpreter.Cast.cast (annealCastHooksFloat ly nondet chooseNaN) () 16 src
            (translateCastKind kind) (encodeTyId castTy) destPlace) m := by
  unfold Miri.Interpreter.Step.evalStatement translateStmt
  dsimp only [translateStmtKind, translateRvalue, annealStepHooksFloat, isFloatCastRvalue]
  simp only [hk, ↓reduceIte]
  apply runRvalue_eq_of_eq
  unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooksFloat annealRvalueHooks
  dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt, pure, EStateM.pure, bind, EStateM.bind]

/-! ### Deterministic NaN mode (`Cast.cast` level) -/

theorem floatOps_adjustNaN_annealFloat_deterministic
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (src dst : IeeeFormat) (bits : Nat) :
    Miri.Interpreter.FloatOps.adjustNaN (annealFloatOpsHooks false chooseNaN) ()
        ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩
        [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] =
      pure (if Anneal.Mir.IeeeFloatCast.isNaNBits src bits then
          ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (preferredNaNBits dst)⟩
        else ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩) := by
  funext st
  exact floatOps_adjustNaN_deterministic _ () rfl src dst bits st

/-- **Deterministic NaN mode** (`floatNondeterministic := false`): `Cast.cast
.FloatToFloat` writes `preferredNaN` for every NaN input and the trusted conversion
for every non-NaN input. -/
theorem cast_floatToFloat_deterministic_eq (layouts : LayoutTable)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {srcTy targetTy : Ty} {src dst : IeeeFormat}
    (hsrc : ieeeFormatOfTy? srcTy = some src) (hdst : ieeeFormatOfTy? targetTy = some dst)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : sc.sizeBytes = src.byteWidth) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    ∃ msc', ScalarRel
        ⟨if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
          else evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩ msc' ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts false chooseNaN) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩ .FloatToFloat
          (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨destRef, translateTy targetTy layouts⟩ := by
  have hbits : sc.bits < 2 ^ src.width := by
    have := hrel.canonical; rwa [hsz, scalarModulus_byteWidth] at this
  have hsrcT := translateTy_of_ieeeFormatOfTy? hsrc layouts
  have hdstT := translateTy_of_ieeeFormatOfTy? hdst layouts
  have henc : encodeTyId targetTy = floatTyIdOf dst := congrArg (·.ty) hdstT
  have hres_lt : (if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
      else evalFloatToFloatRoundTiesToEven src dst sc.bits) < 2 ^ dst.width := by
    split
    · exact Anneal.Mir.IeeeFloatCast.preferredNaNBits_lt dst
    · exact Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst sc.bits
  obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec
    (validScalarBytes_byteWidth dst) (by rw [scalarModulus_byteWidth]; exact hres_lt)
  rw [translateSizeBytes_byteWidth] at hfrom
  refine ⟨msc', hrel', ?_⟩
  rw [hsrcT, hdstT, henc]
  unfold Miri.Interpreter.Cast.cast
  simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true,
    ↓reduceIte, castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true,
    annealReadImmediate_scalar, floatOps_readBits_annealFloat false chooseNaN src hrel hsz,
    floatBits_convert_eq src dst sc.bits hbits, Except.mapError, cast_liftResult_ok,
    floatOps_adjustNaN_annealFloat_deterministic, floatLayoutData_size, bne_self_eq_false]
  cases hn : Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits <;>
    simp only [hn, Bool.false_eq_true, ↓reduceIte] at hfrom ⊢ <;>
    simp only [hfrom, cast_liftResult_ok, pure_bind]

/-- In deterministic NaN mode `Cast.cast .FloatToFloat` agrees bit-exactly with the
trusted conversion on every non-NaN input and on every NaN input whose quieted
conversion already is `preferredNaNBits`. -/
theorem cast_floatToFloat_deterministic_agrees (layouts : LayoutTable)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {srcTy targetTy : Ty} {src dst : IeeeFormat}
    (hsrc : ieeeFormatOfTy? srcTy = some src) (hdst : ieeeFormatOfTy? targetTy = some dst)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : sc.sizeBytes = src.byteWidth) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv)
    (hagree : Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = false ∨
      evalFloatToFloatRoundTiesToEven src dst sc.bits = preferredNaNBits dst) :
    ∃ msc', ScalarRel ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩ msc' ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts false chooseNaN) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩ .FloatToFloat
          (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨destRef, translateTy targetTy layouts⟩ := by
  obtain ⟨msc', hrel', hcast⟩ :=
    cast_floatToFloat_deterministic_eq layouts chooseNaN hsrc hdst hrel hsz destRef
  have hval : (if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
      else evalFloatToFloatRoundTiesToEven src dst sc.bits) =
      evalFloatToFloatRoundTiesToEven src dst sc.bits := by
    rcases hagree with h | h
    · simp [h]
    · split <;> simp [h]
  rw [hval] at hrel'
  exact ⟨msc', hrel', hcast⟩

/-! ## Part 7. Unified float-cast signature and results -/

/-- The three modeled float casts with their source / target types: `f32`/`f64` ↔
`f32`/`f64` (`floatToFloat`), `f32`/`f64` → integer (`floatToInt`), and integer →
`f32`/`f64` (`intToFloat`). -/
inductive FloatCastSig : CastKind → Ty → Ty → Prop where
  | floatToFloat {srcTy castTy : Ty} {src dst : IeeeFormat} :
      ieeeFormatOfTy? srcTy = some src → ieeeFormatOfTy? castTy = some dst →
      FloatCastSig .floatToFloat srcTy castTy
  | floatToInt {srcTy castTy : Ty} {src : IeeeFormat} {t : FloatIntTarget} :
      ieeeFormatOfTy? srcTy = some src → floatIntTargetOfTy? castTy = some t →
      FloatCastSig .floatToInt srcTy castTy
  | intToFloat {srcTy castTy : Ty} {t : FloatIntTarget} {dst : IeeeFormat} :
      floatIntTargetOfTy? srcTy = some t → ieeeFormatOfTy? castTy = some dst →
      FloatCastSig .intToFloat srcTy castTy

/-- A type that `translateTy` lays out as a float or integer scalar. -/
def IsFloatCastScalarTy (ty : Ty) : Prop :=
  (∃ f, ieeeFormatOfTy? ty = some f) ∨ (∃ t, floatIntTargetOfTy? ty = some t)

theorem FloatCastSig.src_scalar {kind : CastKind} {srcTy castTy : Ty}
    (h : FloatCastSig kind srcTy castTy) : IsFloatCastScalarTy srcTy := by
  cases h with
  | floatToFloat hs _ => exact Or.inl ⟨_, hs⟩
  | floatToInt hs _ => exact Or.inl ⟨_, hs⟩
  | intToFloat hs _ => exact Or.inr ⟨_, hs⟩

theorem FloatCastSig.cast_scalar {kind : CastKind} {srcTy castTy : Ty}
    (h : FloatCastSig kind srcTy castTy) : IsFloatCastScalarTy castTy := by
  cases h with
  | floatToFloat _ hd => exact Or.inl ⟨_, hd⟩
  | floatToInt _ hd => exact Or.inr ⟨_, hd⟩
  | intToFloat _ hd => exact Or.inl ⟨_, hd⟩

theorem FloatCastSig.isFloatCastKind {kind : CastKind} {srcTy castTy : Ty}
    (h : FloatCastSig kind srcTy castTy) : isFloatCastKind (translateCastKind kind) = true := by
  cases h <;> rfl

theorem IsFloatCastScalarTy.translateTy_eq {ty₁ ty₂ : Ty} (h : IsFloatCastScalarTy ty₂)
    (hk : ty₁.kind = ty₂.kind) (layouts : LayoutTable) :
    translateTy ty₁ layouts = translateTy ty₂ layouts := by
  rcases h with ⟨f, hf⟩ | ⟨t, ht⟩
  · have hf₁ : ieeeFormatOfTy? ty₁ = some f := by unfold ieeeFormatOfTy? at hf ⊢; rw [hk]; exact hf
    rw [translateTy_of_ieeeFormatOfTy? hf layouts, translateTy_of_ieeeFormatOfTy? hf₁ layouts]
  · have ht₁ : floatIntTargetOfTy? ty₁ = some t := by
      unfold floatIntTargetOfTy? at ht ⊢; rw [hk]; exact ht
    rw [translateTy_of_floatIntTargetOfTy? ht layouts, translateTy_of_floatIntTargetOfTy? ht₁ layouts]

theorem IsFloatCastScalarTy.not_bool_char {ty : Ty} (h : IsFloatCastScalarTy ty) :
    ty.kind ≠ .bool ∧ ty.kind ≠ .char := by
  rcases h with ⟨f, hf⟩ | ⟨t, ht⟩
  · rcases ieeeFormatOfTy?_kind hf with ⟨hk, _⟩ | ⟨hk, _⟩ <;> rw [hk] <;>
      exact ⟨nofun, nofun⟩
  · rcases floatIntTargetOfTy?_kind ht with ⟨_, hk, _⟩ | ⟨_, hk, _⟩ <;> rw [hk] <;>
      exact ⟨nofun, nofun⟩

theorem IsFloatCastScalarTy.size_ne_zero {ty : Ty} (h : IsFloatCastScalarTy ty)
    (layouts : LayoutTable) : (translateTy ty layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
  rcases h with ⟨f, hf⟩ | ⟨t, ht⟩
  · rw [translateTy_of_ieeeFormatOfTy? hf layouts]; cases f <;> decide
  · rw [translateTy_of_floatIntTargetOfTy? ht layouts]
    cases t <;> rename_i w <;> cases w <;> decide

theorem IsFloatCastScalarTy.not_aggregate {ty : Ty} (h : IsFloatCastScalarTy ty) :
    ¬ ((∃ ts, ty.kind = .tuple ts) ∨ (∃ p a, ty.kind = .adt p a)) := by
  rintro (⟨ts, hts⟩ | ⟨p, a, hpa⟩)
  · rcases h with ⟨f, hf⟩ | ⟨t, ht⟩
    · rcases ieeeFormatOfTy?_kind hf with ⟨hk, _⟩ | ⟨hk, _⟩ <;> rw [hk] at hts <;> cases hts
    · rcases floatIntTargetOfTy?_kind ht with ⟨_, hk, _⟩ | ⟨_, hk, _⟩ <;> rw [hk] at hts <;>
        cases hts
  · rcases h with ⟨f, hf⟩ | ⟨t, ht⟩
    · rcases ieeeFormatOfTy?_kind hf with ⟨hk, _⟩ | ⟨hk, _⟩ <;> rw [hk] at hpa <;> cases hpa
    · rcases floatIntTargetOfTy?_kind ht with ⟨_, hk, _⟩ | ⟨_, hk, _⟩ <;> rw [hk] at hpa <;>
        cases hpa

theorem IsFloatCastScalarTy.not_rawPtr {ty : Ty} (h : IsFloatCastScalarTy ty) (mu : Mutability)
    (pk : RigidTy) : ty.kind ≠ .rawPtr mu pk := by
  intro hk
  rcases h with ⟨f, hf⟩ | ⟨t, ht⟩
  · rcases ieeeFormatOfTy?_kind hf with ⟨hk', _⟩ | ⟨hk', _⟩ <;> rw [hk'] at hk <;> cases hk
  · rcases floatIntTargetOfTy?_kind ht with ⟨_, hk', _⟩ | ⟨_, hk', _⟩ <;> rw [hk'] at hk <;> cases hk

/-- Exhaustive case split for an immediate float- or integer-typed local related by
`LocalRelLM3_1`: it is `.dead`, `.uninit`, or an initialized `ScalarRel`-related scalar
of the type's byte width. -/
theorem LocalRelLM3_1.floatCast_immediate_cases
    {mach : AnnealMachine} {allocMap : List AllocMapEntry} {decl : LocalDecl}
    {layouts : LayoutTable} (hty : IsFloatCastScalarTy decl.ty)
    {slot : LocalSlot} {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (hloc : LocalRelLM3_1 mach allocMap decl layouts slot mls)
    (hnot_ind : ∀ mp, mls.value ≠ .live (.indirect mp)) :
    (slot = .dead ∧ mls.value = .dead) ∨
    (slot = .uninit ∧ mls.value = .live (.immediate .uninit)) ∨
    (∃ sc msc, slot = .init (.scalar sc) ∧ ScalarRel sc msc ∧
      (translateTy decl.ty layouts).layout.size = translateSizeBytes sc.sizeBytes ∧
      mls.value = .live (.immediate (.scalar (.fromScalarInt msc)))) := by
  cases hloc with
  | rawPtr _ _ _ mu pk _ hk _ => exact absurd hk (hty.not_rawPtr mu pk)
  | base hb =>
    cases hb with
    | indirect _ mp _ _ _ _ => exact absurd rfl (hnot_ind mp)
    | dead _ _ => exact Or.inl ⟨rfl, rfl⟩
    | immediate _ _ _ _ hv =>
      rcases hv with ⟨rfl, rfl⟩ | ⟨v, rfl, himm⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · cases himm with
        | unit hz => exact absurd hz (hty.size_ne_zero layouts)
        | scalarPair _ _ _ _ _ _ hk _ => exact absurd hk hty.not_aggregate
        | scalar sc msc hrel hsz _ _ =>
          exact Or.inr (Or.inr ⟨sc, msc, rfl, hrel, hsz, rfl⟩)

theorem floatPtrWidthOfLayouts_of_ptr8 {layouts : LayoutTable}
    (h : layoutPointerBytes layouts = 8) : floatPtrWidthOfLayouts layouts = .bits64 := by
  unfold floatPtrWidthOfLayouts; rw [h]

theorem sizeBytes_of_float_layout {f : IeeeFormat} {sc : MirAst.ScalarInt}
    (hv : ValidScalarBytes sc.sizeBytes)
    (h : (floatLayoutData f.byteWidth).size = translateSizeBytes sc.sizeBytes) :
    sc.sizeBytes = f.byteWidth := by
  have h' : translateSizeBytes f.byteWidth = translateSizeBytes sc.sizeBytes := by
    rw [← h]; cases f <;> rfl
  exact (translateSizeBytes_inj (validScalarBytes_byteWidth f) hv h').symm

theorem sizeBytes_of_int_layout {t : FloatIntTarget} {s : Bool} {sc : MirAst.ScalarInt}
    (hv : ValidScalarBytes sc.sizeBytes)
    (h : (scalarLayoutData (t.bitWidth .bits64 / 8) s).size = translateSizeBytes sc.sizeBytes) :
    sc.sizeBytes * 8 = t.bitWidth .bits64 := by
  rw [scalarLayoutData_floatIntTarget_size] at h
  have := translateSizeBytes_inj (validScalarBytes_floatIntTarget t) hv h
  have h8 := floatIntTarget_bitWidth_eq t
  omega

/-- Agreement side condition of the deterministic NaN mode on a source bit pattern: a
`floatToFloat` cast must not see a NaN input whose quieted conversion differs from
`preferredNaNBits` (vacuous for `floatToInt` / `intToFloat`). -/
def FloatCastDetAgrees (kind : CastKind) (srcTy castTy : Ty) (bits : Nat) : Prop :=
  ∀ src dst, kind = .floatToFloat → ieeeFormatOfTy? srcTy = some src →
    ieeeFormatOfTy? castTy = some dst →
    Anneal.Mir.IeeeFloatCast.isNaNBits src bits = false ∨
      evalFloatToFloatRoundTiesToEven src dst bits = preferredNaNBits dst

/-- The NaN modes covered by the lockstep theorems: the refinement witness
(`floatNondeterministic := true`, `chooseNaN := annealChooseQuietedNaN`) and the
deterministic mode (`floatNondeterministic := false`, any `chooseNaN`). -/
def FloatNaNModeOk (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat) :
    Prop :=
  (nondet = true ∧ chooseNaN = annealChooseQuietedNaN) ∨ nondet = false

/-- **Unified float-cast result (both NaN modes)**: for every modeled float cast and
every `ScalarRel`-related source scalar of the source width, Anneal's `evalFloatCast` and
`lean-miri`'s `Cast.cast` produce `ScalarRel`-related scalars of the target width, under
the refinement witness unconditionally and in deterministic mode whenever
`FloatCastDetAgrees` holds. -/
theorem floatCast_result_spec_mode (layouts : LayoutTable)
    (hpw : floatPtrWidthOfLayouts layouts = .bits64) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {kind : CastKind} {srcTy castTy : Ty} (hsig : FloatCastSig kind srcTy castTy)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : (translateTy srcTy layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hagree : nondet = false → FloatCastDetAgrees kind srcTy castTy sc.bits)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    ∃ sc' msc', evalFloatCast kind (some srcTy) castTy layouts (.scalar sc) = some (.scalar sc') ∧
      ScalarRel sc' msc' ∧
      (translateTy castTy layouts).layout.size = translateSizeBytes sc'.sizeBytes ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩
          (translateCastKind kind) (encodeTyId castTy) ⟨destRef, translateTy castTy layouts⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨destRef, translateTy castTy layouts⟩ := by
  cases hsig with
  | @floatToFloat _ _ src dst hs hd =>
    rw [translateTy_of_ieeeFormatOfTy? hs layouts] at hsz
    have hb := sizeBytes_of_float_layout hrel.validBytes hsz
    have hev : evalFloatCast .floatToFloat (some srcTy) castTy layouts (.scalar sc) =
        some (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩) := by
      simp only [evalFloatCast, hs, hd, hb, Nat.beq_refl]
    have htsz : (translateTy castTy layouts).layout.size = translateSizeBytes dst.byteWidth := by
      rw [translateTy_of_ieeeFormatOfTy? hd layouts, translateSizeBytes_byteWidth, floatLayoutData_size]
    rcases hmode with ⟨rfl, rfl⟩ | rfl
    · obtain ⟨msc', hrel', hcast⟩ := cast_floatToFloat_eq layouts hs hd hrel hb destRef
      exact ⟨_, msc', hev, hrel', htsz, hcast⟩
    · obtain ⟨msc', hrel', hcast⟩ := cast_floatToFloat_deterministic_agrees layouts chooseNaN hs hd
        hrel hb destRef (hagree rfl src dst rfl hs hd)
      exact ⟨_, msc', hev, hrel', htsz, hcast⟩
  | @floatToInt _ _ src t hs hd =>
    rw [translateTy_of_ieeeFormatOfTy? hs layouts] at hsz
    have hb := sizeBytes_of_float_layout hrel.validBytes hsz
    obtain ⟨msc', hrel', hcast⟩ := cast_floatToInt_eq layouts nondet chooseNaN hs hd hrel hb destRef
    refine ⟨_, msc', ?_, hrel', ?_, hcast⟩
    · simp only [evalFloatCast, hs, hd, hb, Nat.beq_refl, hpw]
    · rw [translateTy_of_floatIntTargetOfTy? hd layouts, scalarLayoutData_floatIntTarget_size]
      rfl
  | @intToFloat _ _ t dst hs hd =>
    rw [translateTy_of_floatIntTargetOfTy? hs layouts] at hsz
    have hb := sizeBytes_of_int_layout hrel.validBytes hsz
    obtain ⟨msc', hrel', hcast⟩ := cast_intToFloat_eq layouts nondet chooseNaN hs hd hrel hb destRef
    refine ⟨_, msc', ?_, hrel', ?_, hcast⟩
    · simp only [evalFloatCast, hs, hd, hpw, Nat.mul_eq, hb, Nat.beq_refl]
    · rw [translateTy_of_ieeeFormatOfTy? hd layouts, translateSizeBytes_byteWidth, floatLayoutData_size]

/-- **Unified float-cast result** under the NaN refinement witness (no side condition). -/
theorem floatCast_result_spec (layouts : LayoutTable)
    (hpw : floatPtrWidthOfLayouts layouts = .bits64)
    {kind : CastKind} {srcTy castTy : Ty} (hsig : FloatCastSig kind srcTy castTy)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : (translateTy srcTy layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    ∃ sc' msc', evalFloatCast kind (some srcTy) castTy layouts (.scalar sc) = some (.scalar sc') ∧
      ScalarRel sc' msc' ∧
      (translateTy castTy layouts).layout.size = translateSizeBytes sc'.sizeBytes ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩
          (translateCastKind kind) (encodeTyId castTy) ⟨destRef, translateTy castTy layouts⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨destRef, translateTy castTy layouts⟩ :=
  floatCast_result_spec_mode layouts hpw true annealChooseQuietedNaN (Or.inl ⟨rfl, rfl⟩) hsig hrel hsz
    (fun h => absurd h (by decide)) destRef

/-! ## Part 8. Real-step simulation (`StateRelLM3_1` / `StepRelLM3_1`) -/

theorem estate_throw_bind_float {ε σ α β : Type} (e : ε) (f : α → EStateM ε σ β) :
    (throw e >>= f : EStateM ε σ β) = throw e := rfl

theorem annealReadImmediate_uninit_eq (lay : Miri.Interpreter.LocalLayout) :
    annealReadImmediate (⟨.immediate .uninit, lay⟩ : Miri.Interpreter.OpTy AnnealProv) =
      throw (.undefinedBehavior "read of uninitialized local") := rfl

/-- Every modeled float cast of an uninitialized immediate source reports
`read of uninitialized local` UB (after the source-validity type check succeeds). -/
theorem cast_floatCast_uninit (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {kind : CastKind} {srcTy castTy : Ty} (hsig : FloatCastSig kind srcTy castTy)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
        ⟨.immediate .uninit, translateTy srcTy layouts⟩ (translateCastKind kind) (encodeTyId castTy)
        ⟨destRef, translateTy castTy layouts⟩ =
      throw (.undefinedBehavior "read of uninitialized local") := by
  cases hsig with
  | @floatToFloat _ _ src dst hs hd =>
    rw [translateTy_of_ieeeFormatOfTy? hs layouts, translateTy_of_ieeeFormatOfTy? hd layouts,
      show encodeTyId castTy = floatTyIdOf dst from congrArg (·.ty) (translateTy_of_ieeeFormatOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
      castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true,
      annealReadImmediate_uninit_eq, estate_throw_bind_float, translateCastKind]
  | @floatToInt _ _ src t hs hd =>
    rw [translateTy_of_ieeeFormatOfTy? hs layouts, translateTy_of_floatIntTargetOfTy? hd layouts,
      show encodeTyId castTy = floatIntTargetTyId t from
        congrArg (·.ty) (translateTy_of_floatIntTargetOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
      castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true,
      annealReadImmediate_uninit_eq, estate_throw_bind_float, translateCastKind]
  | @intToFloat _ _ t dst hs hd =>
    rw [translateTy_of_floatIntTargetOfTy? hs layouts, translateTy_of_ieeeFormatOfTy? hd layouts,
      show encodeTyId castTy = floatTyIdOf dst from congrArg (·.ty) (translateTy_of_ieeeFormatOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
      castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId, pure_bind, Bool.false_eq_true,
      annealReadImmediate_uninit_eq, estate_throw_bind_float, translateCastKind]

theorem operandTy_copy_local {ld : List LocalDecl} {ly : LayoutTable} {idx : Local}
    {decl : LocalDecl} (hdecl : get? ld idx = some decl) :
    operandTy ld ly (.copy ⟨idx, .nil⟩) = some decl.ty := by
  unfold operandTy placeTy; simp only [hdecl]

theorem operandTy_move_local {ld : List LocalDecl} {ly : LayoutTable} {idx : Local}
    {decl : LocalDecl} (hdecl : get? ld idx = some decl) :
    operandTy ld ly (.move ⟨idx, .nil⟩) = some decl.ty := by
  unfold operandTy placeTy; simp only [hdecl]

/-- `evalRvalue` of a float cast reads its operand and applies `evalFloatCast` at the
operand's static type. -/
theorem evalRvalue_floatCast_eq {kind : CastKind} {srcTy castTy : Ty}
    (hsig : FloatCastSig kind srcTy castTy) (locals : List LocalSlot) (mem : Memory)
    (ld : List LocalDecl) (ly : LayoutTable) (op : MirAst.Operand) :
    evalRvalue locals (.cast kind op castTy) mem ld ly =
      evalFloatCastRvalue locals kind op castTy mem ld ly := by
  cases hsig <;> rfl

/-- Hook-generic version of `SimLM3_1`'s `finish_write_immediate_from_mid`: the shared
post-operand write step into an immediate local `dstIdx` from an operand-updated
`StateRelLM3_1` mid-state `(s_mid, tf_mid)`, for **any** `StepHooks` whose statement
evaluation reduces to the final `annealWriteImmediate` (here `annealStepHooksFloat`). -/
theorem finish_write_immediate_from_mid_hooks
    (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv))
    {body : CapturedMir} {s s_mid : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    {tf tf_mid : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (hbody : tf.body = translateBody body)
    (hloc : tf.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hstate_mid : StateRelLM3_1 body s_mid { m with stack := ⟨#[tf_mid]⟩ } allocMap)
    (hs_frame_eq : s_mid = { s with frame := { s.frame with locals := s_mid.frame.locals } })
    {bb : BasicBlockData} {dstIdx : Local} {dstDecl : LocalDecl} {rv : Rvalue} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (himm_dst_mid : IsImmediateFrameLocal tf_mid dstIdx)
    {val : Value} {newImm : Miri.Interpreter.Immediate AnnealProv}
    (hrv_anneal : evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
      .ok val s_mid.frame.locals s.memory)
    (hm_write : Miri.Interpreter.Step.evalStatement
        hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate newImm
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tf_mid]⟩ })
    (hnew_rel : ∀ cachedLay,
      (∀ l, cachedLay = some l → l = translateTy dstDecl.ty body.layouts) →
      LocalRelLM3_1 m.machine allocMap dstDecl body.layouts (.init val)
        ⟨.live (.immediate newImm), cachedLay⟩) :
    StepRelLM3_1 body m allocMap
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
      (Miri.Interpreter.Step.step hooks () m) := by
  have hfr_m := hstate_mid.frame_rel_singleton rfl
  obtain ⟨_, _, _, _, _, hcal_m, hstack_m, hprot_m, hcaller_m, hbor_m, _, _⟩ := id hstate_mid
  obtain ⟨slot_dm, mls_dm, hlt_af_dm, hlt_dm, hslot_dm, hmls_dm, hmls_dm_eq, hloc_dm⟩ :=
    hfr_m.lookup_local hdecl_dst
  have hs_mem : s_mid.memory = s.memory := by rw [hs_frame_eq]
  have hb_eq : s_mid.frame.blockIdx = s.frame.blockIdx := by rw [hs_frame_eq]
  have hsi_eq : s_mid.frame.stmtIdx = s.frame.stmtIdx := by rw [hs_frame_eq]
  have hd_dead_helper : slot_dm = .dead → mls_dm.value = .dead →
      StepRelLM3_1 body m allocMap
        (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
        (Miri.Interpreter.Step.step hooks () m) := by
    intro hsd_dead hmd_dead
    have hdm_dead : tf_mid.locals[dstIdx]? = some ⟨.dead, mls_dm.layout⟩ := by
      rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_dead; subst hmd_dead; rfl
    have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_dead
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hslot_dm, hsd_dead]
    have hm_err : Miri.Interpreter.Step.evalStatement
        hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
        ({ m with stack := ⟨#[tf_mid]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
      rw [hm_write]; unfold Miri.Interpreter.runRvalue
      rw [annealWriteImmediate_dead (m := { m with stack := ⟨#[tf_mid]⟩ })
        (id0 := tf.localsIdentity) rfl hget_dm]
    rw [ha_ub, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]
    exact .ub _ _
  have hd_live_helper : ∀ oldImm, mls_dm.value = .live (.immediate oldImm) →
      slot_dm ≠ .dead →
      StepRelLM3_1 body m allocMap
        (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
        (Miri.Interpreter.Step.step hooks () m) := by
    intro oldImm hmd_imm hsd_ne
    have hnot_dst : ∀ d ∈ allocMap, d.localIdx ≠ dstIdx :=
      hstate_mid.immediate_not_in_allocMap rfl hslot_dm hsd_ne himm_dst_mid
    have hbor_s : s.memory.borrows = allocMap.map AllocMapEntry.toBorrowEntry := by
      rw [← hs_mem]; exact hbor_m
    have hprot_s : s.memory.activeProtectors = .nil := by
      rw [← hs_mem]; exact hprot_m
    have hstack_s : s.memory.callStack = .nil := by
      rw [← hs_mem]; exact hstack_m
    have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor_s dstIdx none hnot_dst
    have hdm_live : tf_mid.locals[dstIdx]? =
        some ⟨.live (.immediate oldImm), mls_dm.layout⟩ := by
      rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
    have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_live
    have hw_ok := annealWriteImmediate_live (val := newImm)
      (m := { m with stack := ⟨#[tf_mid]⟩ }) (id0 := tf.localsIdentity)
      (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dm hget_dm
    have hm_ok : Miri.Interpreter.Step.evalStatement
        hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
        ({ m with stack := ⟨#[{ tf_mid with
            locals := tf_mid.locals.set dstIdx
              { tf_mid.locals[dstIdx]'hlt_dm with value := .live (.immediate newImm) }
              hlt_dm }]⟩ }, .ok ()) := by
      rw [hm_write]; unfold Miri.Interpreter.runRvalue; rw [hw_ok]
    have hloc_mid : tf_mid.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
      have hl := hfr_m.location_eq
      rw [hb_eq, hsi_eq] at hl
      exact hl
    rw [miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc_mid]
    have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
        MirStepNode.step
          (advanceStmt s_mid (s_mid.frame.locals.set dstIdx (.init val)) s_mid.memory) := by
      have hadv_eq : advanceStmt s (s_mid.frame.locals.set dstIdx (.init val)) s.memory =
          advanceStmt s_mid (s_mid.frame.locals.set dstIdx (.init val)) s_mid.memory := by
        rw [hs_frame_eq]; rfl
      rw [← hadv_eq]
      unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hstack_s, hslot_dm]
      cases slot_dm with
      | dead => exact absurd rfl hsd_ne
      | uninit =>
        simp only [set?_eq_some_set hlt_af_dm, length, List.length_nil, hprot_s, hbor_inv]
        congr 2; generalize s.memory = mem at hstack_s hprot_s ⊢
        cases mem; dsimp at hstack_s hprot_s ⊢; subst hstack_s hprot_s; rfl
      | init _ =>
        simp only [set?_eq_some_set hlt_af_dm, length, List.length_nil, hprot_s, hbor_inv]
        congr 2; generalize s.memory = mem at hstack_s hprot_s ⊢
        cases mem; dsimp at hstack_s hprot_s ⊢; subst hstack_s hprot_s; rfl
    rw [ha_ok]
    refine .step _ _ ?_
    have hnew_d : LocalRelLM3_1 m.machine (allocMap.map id) dstDecl body.layouts (.init val)
        { tf_mid.locals[dstIdx]'hlt_dm with value := .live (.immediate newImm) } := by
      rw [List.map_id]
      exact hnew_rel (tf_mid.locals[dstIdx]'hlt_dm).layout
        (by rw [hmls_dm_eq]; exact hloc_dm.cachedLayout_eq)
    have hstep_rel := hstate_mid.advance_write_immediate_perm_map rfl id
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hdecl_dst hnot_dst (by rw [hmls_dm_eq]; exact hmd_imm) hnew_d
      hcal_m hstack_m hprot_m hcaller_m (by rw [List.map_id]; exact hbor_m) rfl
    rw [List.map_id, hb_eq, hsi_eq] at hstep_rel
    exact hstep_rel
  cases hloc_dm with
  | rawPtr _ _ _ _ _ _ _ _ => exact hd_live_helper _ rfl (by simp)
  | base hb =>
    cases hb with
    | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst_mid _ hmls_dm mp)
    | dead _ _ => exact hd_dead_helper rfl rfl
    | immediate _ oldImm _ _ hvd =>
      exact hd_live_helper oldImm rfl (by rcases hvd with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> simp)

/-- **Copy-operand real-step simulation** for every modeled float cast
(`_d = copy _s as T` with `CastKind.floatToFloat` / `floatToInt` / `intToFloat`) in either
NaN mode (`FloatNaNModeOk`): from any `StateRelLM3_1`-related state with immediate `_s`,
`_d`, Anneal's `stepMirFn` and `lean-miri`'s `Step.step` under `annealStepHooksFloat` step
in lockstep under `StepRelLM3_1` on every source state: `.dead` and `.uninit` sources are
UB in both machines, and an initialized source writes `ScalarRel`-related results (or UB
in both if `_d` is dead); deterministic mode additionally needs `FloatCastDetAgrees`. -/
theorem step_cast_float_copy_simulation_mode
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hagree : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.copy ⟨srcIdx, .nil⟩) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := himm_s.cache_layout hlt_d _
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
  · -- `_s` is dead: UB in both machines.
    subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt
      dsimp only []
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand
      dsimp only []
      rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- `_s` is uninitialized: UB in both machines.
    subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt
      dsimp only []
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand
      dsimp only []
      rw [hslot_s]
    have hcast_un := cast_floatCast_uninit body.layouts nondet chooseNaN hsig
      (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast_un
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_dst, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok]
      rw [hcast_un]
      rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- `_s` holds a scalar: both machines write related cast results.
    subst hss
    obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
      (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
      (fun h => hagree h sc hslot_s) (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast hsz'
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hrv_a : evalRvalue s.frame.locals (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts = .ok (.scalar sc') s.frame.locals s.memory := by
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) s.frame.locals := by
        unfold evalOperand readProjectedValue; dsimp only []; rw [hslot_s]
      rw [hop]
      dsimp only []
      rw [operandTy_copy_local hdecl_src, hev]
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok]
      rw [hcast]
    refine finish_write_immediate_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_b rfl hbb hstmt hdecl_dst
      ((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _) hrv_a hm_write (fun cachedLay hc => ?_)
    obtain ⟨hnb, hnc⟩ := hsig.cast_scalar.not_bool_char
    exact .base (.immediate (.init (.scalar sc')) (.scalar (.fromScalarInt msc')) cachedLay hc
      (Or.inr ⟨.scalar sc', rfl,
        .scalar sc' msc' hrel' hsz'
          (fun h => absurd (h ▸ hdst_ty).symm hnb) (fun h => absurd (h ▸ hdst_ty).symm hnc)⟩))

/-- **Move-operand real-step simulation** for every modeled float cast
(`_d = move _s as T`), in either NaN mode: as `step_cast_float_copy_simulation_mode`, and
additionally both
machines deinitialize the moved-from `_s` (Anneal `LocalSlot.uninit`, `lean-miri`
`.live (.immediate .uninit)`) before writing `_d`; `.dead` / `.uninit` sources are UB in
both machines. -/
theorem step_cast_float_move_simulation_mode
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (hagree : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.move ⟨srcIdx, .nil⟩) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := himm_s.cache_layout hlt_d _
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ := rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
  · -- `_s` is dead: UB in both machines.
    subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt
      dsimp only []
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand
      dsimp only []
      rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- `_s` is uninitialized: UB in both machines.
    subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt
      dsimp only []
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand
      dsimp only []
      rw [hslot_s]
    have hcast_un := cast_floatCast_uninit body.layouts nondet chooseNaN hsig
      (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast_un
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_dst, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_un]
      rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- `_s` holds a scalar: both machines deinitialize `_s` and write related results.
    subst hss
    obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
      (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
      (fun h => hagree h sc hslot_s) (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast hsz'
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have himm_sb := (himm_s.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)).cache_layout
      hlt_sa (translateTy srcDecl.ty body.layouts)
    have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hslot_s (by simp) himm_sb hlt_sb
    obtain ⟨hlt_af_s, _⟩ := List.getElem?_eq_some_iff.mp
      (by rw [← get?_eq_getElem?]; exact hslot_s)
    have hrv_a : evalRvalue s.frame.locals (.cast kind (.move ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts =
        .ok (.scalar sc') (s.frame.locals.set srcIdx .uninit) s.memory := by
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) (s.frame.locals.set srcIdx .uninit) := by
        unfold evalOperand; dsimp only []; rw [hslot_s, set?_eq_some_set hlt_af_s]
      rw [hop]
      dsimp only []
      rw [operandTy_move_local hdecl_src, hev]
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
    refine finish_write_immediate_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_mid rfl hbb hstmt hdecl_dst
      (((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb) hrv_a hm_write
      (fun cachedLay hc => ?_)
    obtain ⟨hnb, hnc⟩ := hsig.cast_scalar.not_bool_char
    exact .base (.immediate (.init (.scalar sc')) (.scalar (.fromScalarInt msc')) cachedLay hc
      (Or.inr ⟨.scalar sc', rfl,
        .scalar sc' msc' hrel' hsz'
          (fun h => absurd (h ▸ hdst_ty).symm hnb) (fun h => absurd (h ▸ hdst_ty).symm hnc)⟩))

theorem layoutOfEncodedTyId_floatCastScalar {ty : Ty} (h : IsFloatCastScalarTy ty)
    (layouts : LayoutTable) : layoutOfEncodedTyId (encodeTyId ty) layouts = translateTy ty layouts := by
  rcases h with ⟨f, hf⟩ | ⟨t, ht⟩
  · rw [show encodeTyId ty = floatTyIdOf f from congrArg (·.ty) (translateTy_of_ieeeFormatOfTy? hf layouts),
      translateTy_of_ieeeFormatOfTy? hf layouts]
    cases f <;> rfl
  · rw [show encodeTyId ty = floatIntTargetTyId t from
        congrArg (·.ty) (translateTy_of_floatIntTargetOfTy? ht layouts),
      translateTy_of_floatIntTargetOfTy? ht layouts]
    cases t <;> rename_i w <;> cases w <;> rfl

/-- **Constant-operand real-step simulation** for every modeled float cast
(`_d = const c as T` with a scalar constant `c : srcTy` of the source width), in either
NaN mode. -/
theorem step_cast_float_constant_simulation_mode
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hmode : FloatNaNModeOk nondet chooseNaN)
    {bb : BasicBlockData} {dstIdx : Local} {kind : CastKind} {c : ConstOperand} {castTy : Ty}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hsig : FloatCastSig kind c.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hagree : nondet = false → FloatCastDetAgrees kind c.ty castTy sc.bits)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have himm_d := himm tf hframes
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hsig.isFloatCastKind (.constant c) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
  have hsrc_ok : annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c)) none
      { m with stack := ⟨#[tfa]⟩ } =
      .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } := by
    with_unfolding_all
      unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
      dsimp only
      rw [hval]
      simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
        EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        stack_currentFrame?_singleton { m with stack := ⟨#[tfa]⟩ }.stack tfa rfl, Option.isNone_some,
        Bool.false_eq_true, ↓reduceIte, htry,
        layoutOfEncodedTyId_floatCastScalar hsig.src_scalar body.layouts]
  obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
    (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hlaysz hagree
    (.local 0 dstIdx none tf.localsIdentity)
  rw [← hdstT] at hcast hsz'
  have hrv_a : evalRvalue s.frame.locals (.cast kind (.constant c) castTy) s.memory
      body.localDecls body.layouts = .ok (.scalar sc') s.frame.locals s.memory := by
    rw [evalRvalue_floatCast_eq hsig]
    unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]
    dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl, hev]
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tfa]⟩ } := by
    rw [hm_stmt, htr_dst]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  refine finish_write_immediate_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
    hstate_a rfl hbb hstmt hdecl_dst (himm_d.cache_layout hlt_d _) hrv_a hm_write
    (fun cachedLay hc => ?_)
  obtain ⟨hnb, hnc⟩ := hsig.cast_scalar.not_bool_char
  exact .base (.immediate (.init (.scalar sc')) (.scalar (.fromScalarInt msc')) cachedLay hc
    (Or.inr ⟨.scalar sc', rfl,
      .scalar sc' msc' hrel' hsz'
        (fun h => absurd (h ▸ hdst_ty).symm hnb) (fun h => absurd (h ▸ hdst_ty).symm hnc)⟩))


/-- **Copy-operand real-step simulation under the NaN refinement witness**
(`floatNondeterministic := true`, `chooseNaN := annealChooseQuietedNaN`): unconditional
bit-exact lockstep on **every** `f32` / `f64` / integer source state and bit pattern,
including every quiet, signaling, signed, or payload NaN. -/
theorem step_cast_float_copy_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_copy_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) himm hptr8

/-- **Move-operand real-step simulation under the NaN refinement witness**. -/
theorem step_cast_float_move_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsig : FloatCastSig kind srcDecl.ty castTy)
    (hdst_ty : dstDecl.ty.kind = castTy.kind)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_move_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) himm hptr8

/-- **Constant-operand real-step simulation under the NaN refinement witness**. -/
theorem step_cast_float_constant_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {kind : CastKind} {c : ConstOperand} {castTy : Ty}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hsig : FloatCastSig kind c.ty castTy) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_constant_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hsig hdst_ty hval hsz hcan hlaysz
    (fun h => absurd h (by decide)) himm hptr8

/-! ## Part 9. Boundaries -/

/-- **`bool` / `char` source boundary of `CastKind.intToFloat`**: Anneal's
`evalFloatCast` models only integer sources (`floatIntTargetOfTy?`), so a `bool` or
`char` source fails closed (`none`, hence `RvalueEvalResult.unsupported`), whereas
`lean-miri`'s `Cast.cast .IntToFloat` accepts `.boolean` / `.character` (rustc never
emits such a cast: `bool as f32` and `char as f32` are rejected by type checking). -/
theorem evalFloatCast_intToFloat_bool_char_none {srcTy castTy : Ty} (layouts : LayoutTable)
    (v : Value) (hsrc : srcTy.kind = .bool ∨ srcTy.kind = .char) :
    evalFloatCast .intToFloat (some srcTy) castTy layouts v = none := by
  have hnone : floatIntTargetOfTy? srcTy = none := by
    unfold floatIntTargetOfTy?; rcases hsrc with h | h <;> rw [h]
  unfold evalFloatCast
  cases v <;> simp [hnone]

/-- `f16` and `f128` sources and targets fail closed in Anneal's `evalFloatCast`
(matching the overlay, where `castTypeInfoOfEncodedTyIdFloat` rejects TyIds `30` / `33`
with `StepError.unsupported`). -/
theorem evalFloatCast_f16_f128_none (kind : CastKind) {fTy : Ty} (otherTy : Ty)
    (layouts : LayoutTable) (v : Value)
    (hf : fTy.kind = .float .f16 ∨ fTy.kind = .float .f128) :
    evalFloatCast kind (some fTy) otherTy layouts v = none ∧
      evalFloatCast kind (some otherTy) fTy layouts v = none := by
  have hnone : ieeeFormatOfTy? fTy = none := by
    unfold ieeeFormatOfTy?; rcases hf with h | h <;> rw [h]
  have hnoneI : floatIntTargetOfTy? fTy = none := by
    unfold floatIntTargetOfTy?; rcases hf with h | h <;> rw [h]
  constructor <;> unfold evalFloatCast <;> cases kind <;> cases v <;> simp [hnone, hnoneI]

/-! ## Part 10. Concrete edge-case witnesses -/

/-- `u128::MAX as f32` rounds up past `f32::MAX` (carry-out) to `+∞` in both machines. -/
theorem miri_u128_max_to_f32_inf :
    Miri.Interpreter.FloatBits.fromInteger .binary32 (2 ^ 128 - 1) =
      .ok ⟨.binary32, BitVec.ofNat 128 0x7F800000⟩ ∧
    evalIntToFloatRoundTiesToEven false 128 (2 ^ 128 - 1) .binary32 = 0x7F800000 := by
  have h := floatBits_fromInteger_intValueOfBits false 128 (2 ^ 128 - 1) .binary32
  have hv : intValueOfBits false 128 (2 ^ 128 - 1) = 2 ^ 128 - 1 := by decide
  have he : evalIntToFloatRoundTiesToEven false 128 (2 ^ 128 - 1) .binary32 = 0x7F800000 := by
    decide +kernel
  rw [hv, he] at h
  exact ⟨h, he⟩

/-- `i128::MIN as f32` is exactly `-2^127` (`0xFF000000`) in both machines. -/
theorem miri_i128_min_to_f32_exact :
    Miri.Interpreter.FloatBits.fromInteger .binary32 (-(2 ^ 127)) =
      .ok ⟨.binary32, BitVec.ofNat 128 0xFF000000⟩ ∧
    evalIntToFloatRoundTiesToEven true 128 (2 ^ 127) .binary32 = 0xFF000000 := by
  have h := floatBits_fromInteger_intValueOfBits true 128 (2 ^ 127) .binary32
  have hv : intValueOfBits true 128 (2 ^ 127) = -(2 ^ 127) := by decide
  have he : evalIntToFloatRoundTiesToEven true 128 (2 ^ 127) .binary32 = 0xFF000000 := by
    decide +kernel
  rw [hv, he] at h
  exact ⟨h, he⟩

/-- `-0.0f64 as f32` keeps its sign (`0x80000000`), while `-0.0f64 as i32` is `0`, in
both machines. -/
theorem miri_neg_zero_cast_witnesses :
    Miri.Interpreter.FloatBits.convert ⟨.binary64, BitVec.ofNat 128 0x8000000000000000⟩ .binary32 =
      .ok ⟨.binary32, BitVec.ofNat 128 0x80000000⟩ ∧
    Miri.Interpreter.FloatBits.toInteger ⟨.binary64, BitVec.ofNat 128 0x8000000000000000⟩ 32 true =
      .ok 0 := by
  have h1 := floatBits_convert_eq .binary64 .binary32 0x8000000000000000 (by decide)
  have he : evalFloatToFloatRoundTiesToEven .binary64 .binary32 0x8000000000000000 = 0x80000000 := by
    decide +kernel
  rw [he] at h1
  have h2 := floatBits_toInteger_eq .binary64 0x8000000000000000 (by decide) (.signed .i32) .bits64
  have hz : floatToIntValue (decodeBits .binary64 0x8000000000000000)
      ((FloatIntTarget.signed .i32).minValue .bits64) ((FloatIntTarget.signed .i32).maxValue .bits64) = 0 := by
    decide +kernel
  rw [hz] at h2
  exact ⟨h1, h2⟩

/-- The signaling NaN `0x7FF0_0000_0000_0001` (`f64`) converts to the quiet `f32` NaN
`0x7FC0_0000` (the low payload bit is dropped) in both machines. -/
theorem miri_snan_f64_to_f32_quietized :
    Miri.Interpreter.FloatBits.convert ⟨.binary64, BitVec.ofNat 128 0x7FF0000000000001⟩ .binary32 =
      .ok ⟨.binary32, BitVec.ofNat 128 0x7FC00000⟩ := by
  have h1 := floatBits_convert_eq .binary64 .binary32 0x7FF0000000000001 (by decide)
  have he : evalFloatToFloatRoundTiesToEven .binary64 .binary32 0x7FF0000000000001 = 0x7FC00000 := by
    decide +kernel
  rw [he] at h1
  exact h1

/-! ## Part 11. Non-vacuity of the real-step hypotheses

`fn f() -> i32 { -2.5_f64 as i32 }` (`_0 = const 0xC004_0000_0000_0000_f64 as i32`): every
premise of `step_cast_float_constant_simulation` holds on entry, so the real-step theorems
are not vacuous (Episode 2 instantiates the copy / move variants on full witnesses). -/

section NonVacuity

open LeanMiriSpec.Correspondence.Witness

/-- `i32`. -/
def floatWitI32Ty : Ty := { kind := .int .i32, layoutIdx := 0 }
/-- `_0 : i32`. -/
def floatWitI32Decl : LocalDecl := { mutability := .mut, ty := floatWitI32Ty, debugName := none }
/-- `f64`. -/
def floatWitF64Ty : Ty := { kind := .float .f64, layoutIdx := 0 }
/-- The constant `-2.5_f64` (`0xC004_0000_0000_0000`). -/
def floatWitConst : ConstOperand :=
  { ty := floatWitF64Ty, val := .scalar (.int ⟨0xC004000000000000, 8⟩) }

/-- MIR of `fn f() -> i32 { -2.5_f64 as i32 }`. -/
def floatWitBody : CapturedMir where
  defPath := "float_cast_lm_witness::f2i"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [floatWitI32Decl]
  basicBlocks := [
    { statements :=
        [mkStmt (.assign (local_ 0) (.cast .floatToInt (.constant floatWitConst) floatWitI32Ty))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm12FnAbi lm12I32Layout
  layouts := emptyLayoutTable
  allocations := []

theorem floatWit_stateRel :
    StateRelLM3_1 floatWitBody (initMachineState floatWitBody [])
      (lm12MiriInit floatWitBody floatWitI32Ty) [] :=
  (lm12_stateRel_init _ floatWitI32Decl rfl rfl rfl rfl rfl rfl rfl).toLM3_1

/-- Every premise of `step_cast_float_constant_simulation` holds on entry to
`floatWitBody`, so both machines step `-2.5_f64 as i32` in lockstep. -/
theorem floatWit_step_applies :
    StepRelLM3_1 floatWitBody (lm12MiriInit floatWitBody floatWitI32Ty) []
      (stepMirFn floatWitBody (initMachineState floatWitBody []))
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat floatWitBody.localDecls floatWitBody.layouts) ()
        (lm12MiriInit floatWitBody floatWitI32Ty)) :=
  step_cast_float_constant_simulation floatWit_stateRel (fun _ h => nomatch h) rfl rfl rfl
    (.floatToInt rfl rfl) rfl rfl (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide) rfl
    (fun tf htf => by rw [lm12_frames_eq htf]; exact lm12Frame_immediate _ _ 0)

/-- Anneal's step stores `-2.5_f64 as i32 = -2` (`0xFFFF_FFFE`). -/
theorem floatWit_anneal_result :
    evalFloatCast .floatToInt (some floatWitF64Ty) floatWitI32Ty emptyLayoutTable
        (.scalar ⟨0xC004000000000000, 8⟩) = some (.scalar ⟨0xFFFFFFFE, 4⟩) := by
  rfl

end NonVacuity

/-! ## Axiom guards

Every headline theorem depends only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`): `#guard_msgs` fails the build if a proof ever starts
depending on `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or any other axiom. -/

section AxiomGuards

/--
info: 'LeanMiriSpec.Correspondence.ieeeFormatToMiri_injective' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms ieeeFormatToMiri_injective

/--
info: 'LeanMiriSpec.Correspondence.miriFormatToIeee?_ieeeFormatToMiri' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms miriFormatToIeee?_ieeeFormatToMiri

/--
info: 'LeanMiriSpec.Correspondence.miri_powScale_eq' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_powScale_eq

/--
info: 'LeanMiriSpec.Correspondence.miri_ratioExponent_eq' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_ratioExponent_eq

/--
info: 'LeanMiriSpec.Correspondence.miri_roundQuotientEven_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_roundQuotientEven_eq

/--
info: 'LeanMiriSpec.Correspondence.miri_encode_eq' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_encode_eq

/--
info: 'LeanMiriSpec.Correspondence.floatBits_decode_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_decode_eq

/--
info: 'LeanMiriSpec.Correspondence.floatBits_decode_error' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_decode_error

/--
info: 'LeanMiriSpec.Correspondence.floatBits_roundRatio_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_roundRatio_eq

/--
info: 'LeanMiriSpec.Correspondence.floatBits_fromInteger_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_fromInteger_eq

/--
info: 'LeanMiriSpec.Correspondence.floatBits_fromInteger_intValueOfBits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_fromInteger_intValueOfBits

/--
info: 'LeanMiriSpec.Correspondence.floatBits_toInteger_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_toInteger_eq

/--
info: 'LeanMiriSpec.Correspondence.floatBits_convert_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_convert_eq

/--
info: 'LeanMiriSpec.Correspondence.floatBits_isNaN_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_isNaN_eq

/--
info: 'LeanMiriSpec.Correspondence.floatBits_isSignaling_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_isSignaling_eq

/--
info: 'LeanMiriSpec.Correspondence.floatBits_nanChoices_deterministic' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_nanChoices_deterministic

/--
info: 'LeanMiriSpec.Correspondence.floatBits_nanChoices_nondet_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_nanChoices_nondet_eq

/--
info: 'LeanMiriSpec.Correspondence.floatOps_adjustNaN_convert_refine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatOps_adjustNaN_convert_refine

/--
info: 'LeanMiriSpec.Correspondence.floatOps_adjustNaN_deterministic' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatOps_adjustNaN_deterministic

/--
info: 'LeanMiriSpec.Correspondence.scalar_fromInt_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms scalar_fromInt_spec

/--
info: 'LeanMiriSpec.Correspondence.scalar_fromUInt_ofInt_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms scalar_fromUInt_ofInt_spec

/--
info: 'LeanMiriSpec.Correspondence.floatToInt_scalar_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatToInt_scalar_spec

/--
info: 'LeanMiriSpec.Correspondence.cast_floatToFloat_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cast_floatToFloat_eq

/--
info: 'LeanMiriSpec.Correspondence.cast_floatToInt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cast_floatToInt_eq

/--
info: 'LeanMiriSpec.Correspondence.cast_intToFloat_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cast_intToFloat_eq

/--
info: 'LeanMiriSpec.Correspondence.cast_floatCast_uninit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cast_floatCast_uninit

/--
info: 'LeanMiriSpec.Correspondence.floatCast_result_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatCast_result_spec

/--
info: 'LeanMiriSpec.Correspondence.evalStatement_float_eq_of_stmtFree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalStatement_float_eq_of_stmtFree

/--
info: 'LeanMiriSpec.Correspondence.step_float_eq_annealStepHooks_of_bodyFree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_float_eq_annealStepHooks_of_bodyFree

/--
info: 'LeanMiriSpec.Correspondence.castTypeInfoOfEncodedTyIdFloat_eq_of_ne' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms castTypeInfoOfEncodedTyIdFloat_eq_of_ne

/--
info: 'LeanMiriSpec.Correspondence.castTypeInfoOfEncodedTyIdFloat_f16_f128' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms castTypeInfoOfEncodedTyIdFloat_f16_f128

/--
info: 'LeanMiriSpec.Correspondence.evalStatement_assign_floatCast_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalStatement_assign_floatCast_eq

/--
info: 'LeanMiriSpec.Correspondence.LocalRelLM3_1.floatCast_immediate_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalRelLM3_1.floatCast_immediate_cases

/--
info: 'LeanMiriSpec.Correspondence.finish_write_immediate_from_mid_hooks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms finish_write_immediate_from_mid_hooks

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_copy_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_copy_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_move_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_move_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_constant_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_constant_simulation

/--
info: 'LeanMiriSpec.Correspondence.cast_floatToFloat_deterministic_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cast_floatToFloat_deterministic_eq

/--
info: 'LeanMiriSpec.Correspondence.cast_floatToFloat_deterministic_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cast_floatToFloat_deterministic_agrees

/--
info: 'LeanMiriSpec.Correspondence.evalFloatCast_intToFloat_bool_char_none' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatCast_intToFloat_bool_char_none

/--
info: 'LeanMiriSpec.Correspondence.evalFloatCast_f16_f128_none' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatCast_f16_f128_none

/--
info: 'LeanMiriSpec.Correspondence.miri_u128_max_to_f32_inf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_u128_max_to_f32_inf

/--
info: 'LeanMiriSpec.Correspondence.miri_i128_min_to_f32_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_i128_min_to_f32_exact

/--
info: 'LeanMiriSpec.Correspondence.miri_neg_zero_cast_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_neg_zero_cast_witnesses

/--
info: 'LeanMiriSpec.Correspondence.miri_snan_f64_to_f32_quietized' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_snan_f64_to_f32_quietized

/--
info: 'LeanMiriSpec.Correspondence.floatCast_result_spec_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatCast_result_spec_mode

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_copy_simulation_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_copy_simulation_mode

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_move_simulation_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_move_simulation_mode

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_constant_simulation_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_constant_simulation_mode

/--
info: 'LeanMiriSpec.Correspondence.annealFloatOpsHooks_integerKindOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms annealFloatOpsHooks_integerKindOf
/--
info: 'LeanMiriSpec.Correspondence.floatWit_step_applies' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatWit_step_applies

end AxiomGuards

end LeanMiriSpec.Correspondence
