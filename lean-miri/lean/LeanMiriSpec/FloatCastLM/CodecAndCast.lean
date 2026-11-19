/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Mir.IeeeFloatCast
import LeanMiriSpec.Correspondence.SimLM1_2
import LeanMiriSpec.Correspondence.PtrLM3_1
import Miri.Interpreter.Float
import Miri.Interpreter.FloatOps
import Miri.Interpreter.Cast
import Miri.Interpreter.Step

/-!
# Float-cast codec and `Cast.cast` simulation (`LeanMiriSpec.FloatCastLM.CodecAndCast`)

First layer (Parts 0–7) of the IEEE-754 float-cast correspondence; see the umbrella module
`LeanMiriSpec.FloatCastLM` for the architectural overview and the submodule map.

* **Part 0. Vendored private helpers**: the `miri_private%` term elaborator and the bridges
  identifying the vendored `private` helpers of `Miri.Interpreter.Float` with the trusted
  primitives (`miri_powScale_eq`, `miri_ratioExponent_eq`, `miri_roundQuotientEven_eq`,
  `miri_signedNumerator_eq`, `miri_encode_eq`).
* **Parts 1–3. Formats, rounding, and NaNs**: `ieeeFormatToMiri` / `miriFormatToIeee?`,
  `floatBits_decode_eq`, `floatBits_roundRatio_eq`, `floatBits_fromInteger_eq`,
  `floatBits_toInteger_eq`, `floatBits_convert_eq`, the `floatBits_nanChoices_*` candidate-list
  theorems, the `floatOps_adjustNaN_*` selector theorems, and `floatToFloatPureIndexBits`.
* **Part 4. Float-cast hook overlay**: `castTypeInfoOfEncodedTyIdFloat`, `annealFloatOpsHooks`,
  `annealCastHooksFloat`.
* **Part 5. `Cast.cast` simulation**: `cast_floatToFloat_eq`, `cast_floatToInt_eq`,
  `cast_intToFloat_eq`, and the typed `Miri.Interpreter.FloatOps` cast adapters.
* **Part 6. Rvalue and step overlay, conservative extension**: `annealRvalueHooksFloat`,
  `annealStepHooksFloat`, `step_float_eq_annealStepHooks_of_bodyFree`,
  `step_float_eq_annealStepHooks_at_stmt`, `step_float_eq_annealStepHooks_at_terminator`,
  `cast_intToInt_ptrToPtr_floatHooks_eq`, and the deterministic NaN mode at `Cast.cast` level.
* **Part 7. Unified float-cast signature and results**: `FloatCastSig`, `IsFloatCastScalarTy`,
  `FloatCastDetAgrees`, `FloatNaNModeOk`, `floatCast_result_spec_mode`, `floatCast_result_spec`.

The `local macro` abbreviations for vendored private helpers (`miriPowScale`, `miriEncode`,
`miriCastLiftResult`, ...) are declared and used only in this module; `miri_private%` itself is
exported to importers.
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

/-- **Unified `preferredNaN` membership & deterministic uniqueness**: for every NaN input
`bits < 2 ^ src.width` and either `nondet : Bool` mode, `FloatBits.nanChoices` succeeds with
`FloatBits.preferredNaN (ieeeFormatToMiri dst) ∈ candidates` (and `candidates` is the
singleton `[preferredNaN]` when `nondet = false`). -/
theorem floatBits_preferredNaN_mem_nanChoices (src dst : IeeeFormat) (bits : Nat)
    (h : bits < 2 ^ src.width) (neg q : Bool) (payload : Nat)
    (hnan : decodeBits src bits = .nan neg q payload) (nondet : Bool) :
    ∃ candidates,
      Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
          [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] nondet = .ok candidates ∧
      Miri.Interpreter.FloatBits.preferredNaN (ieeeFormatToMiri dst) ∈ candidates ∧
      (nondet = false →
        candidates = [Miri.Interpreter.FloatBits.preferredNaN (ieeeFormatToMiri dst)]) := by
  cases nondet with
  | false =>
    exact ⟨[Miri.Interpreter.FloatBits.preferredNaN (ieeeFormatToMiri dst)], rfl,
      List.Mem.head _, fun _ => rfl⟩
  | true =>
    obtain ⟨candidates, hc, h0, _⟩ := floatBits_nanChoices_nondet_eq src dst bits h neg q payload hnan
    exact ⟨candidates, hc, List.mem_of_getElem? h0, fun hf => absurd hf Bool.noConfusion⟩

/-- **Nondeterministic `convert` membership**: for every NaN input `bits < 2 ^ src.width`,
the quieted conversion `evalFloatToFloatRoundTiesToEven src dst bits` belongs to
`nanChoices (ieeeFormatToMiri dst) [bits] true` (at index `2`, alongside `preferredNaN` at
index `0`). -/
theorem floatBits_convert_mem_nanChoices_nondet (src dst : IeeeFormat) (bits : Nat)
    (h : bits < 2 ^ src.width) (neg q : Bool) (payload : Nat)
    (hnan : decodeBits src bits = .nan neg q payload) :
    ∃ candidates,
      Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
          [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] true = .ok candidates ∧
      Miri.Interpreter.FloatBits.preferredNaN (ieeeFormatToMiri dst) ∈ candidates ∧
      ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩ ∈
        candidates ∧
      candidates[0]? = some (Miri.Interpreter.FloatBits.preferredNaN (ieeeFormatToMiri dst)) ∧
      candidates[2]? =
        some ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩ := by
  obtain ⟨candidates, hc, h0, h2⟩ := floatBits_nanChoices_nondet_eq src dst bits h neg q payload hnan
  exact ⟨candidates, hc, List.mem_of_getElem? h0, List.mem_of_getElem? h2, h0, h2⟩

/-- **Exact 4-vs-6 candidate-list characterization of `FloatBits.nanChoices` (`nondet = true`)**,
capturing Miri's signaling-NaN payload truncation rule (`Float.lean:139-147`):
* Let `convBits := evalFloatToFloatRoundTiesToEven src dst bits` and
  `lower := (convBits % 2 ^ dst.fractionBits) % 2 ^ (dst.fractionBits - 1)`.
* When `q = false` (signaling NaN input) **and** `lower ≠ 0` (the precision-scaled low
  payload bits do not vanish), `nanChoices` returns **6** candidates, with the `dst`
  signaling NaN `encodeBits dst neg (2 ^ dst.exponentBits - 1) lower` at index `4`
  (satisfying `FloatBits.isSignaling = .ok true`; see `floatBits_nanChoices_nondet_list_eq`
  for the odd sign-negated entries at indices `1`, `3`, `5`).
* When `q = true` (quiet NaN input) **or** `lower = 0` (e.g. `f64 → f32` on a signaling NaN
  whose payload bits lie strictly below bit `29`, where encoding `lower = 0` with maximum
  exponent would collide with `±∞` instead of a NaN), `nanChoices` suppresses the signaling
  candidate and returns **4** candidates (`[preferredNaN, -preferredNaN, converted, -converted]`). -/
theorem floatBits_nanChoices_nondet_exact (src dst : IeeeFormat) (bits : Nat)
    (h : bits < 2 ^ src.width) (neg q : Bool) (payload : Nat)
    (hnan : decodeBits src bits = .nan neg q payload) :
    let convBits := evalFloatToFloatRoundTiesToEven src dst bits
    let lower := (convBits % 2 ^ dst.fractionBits) % 2 ^ (dst.fractionBits - 1)
    ∃ candidates,
      Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
          [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] true = .ok candidates ∧
      candidates[0]? = some (Miri.Interpreter.FloatBits.preferredNaN (ieeeFormatToMiri dst)) ∧
      candidates[2]? = some ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 convBits⟩ ∧
      (if q = false ∧ lower ≠ 0 then
          candidates.length = 6 ∧
          candidates[4]? =
            some ⟨ieeeFormatToMiri dst,
              BitVec.ofNat 128 (encodeBits dst neg (2 ^ dst.exponentBits - 1) lower)⟩ ∧
          Miri.Interpreter.FloatBits.isSignaling
              ⟨ieeeFormatToMiri dst,
                BitVec.ofNat 128 (encodeBits dst neg (2 ^ dst.exponentBits - 1) lower)⟩ =
            .ok true
        else
          candidates.length = 4) := by
  dsimp only
  have hnanb : Anneal.Mir.IeeeFloatCast.isNaNBits src bits = true :=
    Anneal.Mir.IeeeFloatCast.isNaNBits_of_nan src bits neg q payload hnan
  have hconvlt := Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst bits
  obtain ⟨_, _, hp, _⟩ := Anneal.Mir.IeeeFloatCast.decodeBits_nan_payload src bits neg q payload hnan
  have hdk :=
    Anneal.Mir.IeeeFloatCast.decodeBits_evalFloatToFloatRoundTiesToEven_of_nan src dst bits neg q payload hnan
  obtain ⟨hpay_mod, _, hplt, _⟩ :=
    Anneal.Mir.IeeeFloatCast.decodeBits_nan_payload dst
      (evalFloatToFloatRoundTiesToEven src dst bits) neg true _ hdk
  rw [hpay_mod] at hdk hplt
  have hdecc := floatBits_decode_eq dst (evalFloatToFloatRoundTiesToEven src dst bits) hconvlt
  rw [hdk] at hdecc
  have hlow_half :
      evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
          2 ^ (dst.fractionBits - 1) <
        2 ^ (dst.fractionBits - 1) :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hlow :
      evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
          2 ^ (dst.fractionBits - 1) <
        2 ^ dst.fractionBits :=
    Nat.lt_of_lt_of_le hlow_half (Anneal.Mir.IeeeFloatCast.two_pow_le_two_pow (Nat.sub_le _ _))
  have hsnan_lt :
      encodeBits dst neg (2 ^ dst.exponentBits - 1)
        (evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
          2 ^ (dst.fractionBits - 1)) < 2 ^ dst.width :=
    Anneal.Mir.IeeeFloatCast.encodeBits_lt dst neg (2 ^ dst.exponentBits - 1) _
      (Nat.sub_lt (Nat.two_pow_pos _) (by decide)) hlow
  have hnp := floatBits_negate_eq dst _ (Anneal.Mir.IeeeFloatCast.preferredNaNBits_lt dst)
  have hnc := floatBits_negate_eq dst _ hconvlt
  have hns := floatBits_negate_eq dst _ hsnan_lt
  unfold Miri.Interpreter.FloatBits.nanChoices
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.forIn_cons, List.forIn_nil,
    floatBits_isNaN_eq src bits h, hnanb, floatBits_convert_eq src dst bits h,
    floatBits_isSignaling_eq src bits h, hnan, hdecc, floatBits_preferredNaN_eq, hnp,
    bind, Except.bind, pure, Except.pure, List.nil_append,
    floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri,
    ieeeFormatToMiri_fractionBits, ieeeFormatToMiri_exponentBits, miri_encode_eq]
  cases q with
  | false =>
    by_cases hl0 :
        evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
          2 ^ (dst.fractionBits - 1) = 0
    · have hne_f :
          (evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
            2 ^ (dst.fractionBits - 1) != 0) = false := by simp [hl0]
      simp only [Bool.not_false, ↓reduceIte, hne_f, Bool.false_eq_true, List.forIn_cons,
        List.forIn_nil, hnc, bind, Except.bind, pure, Except.pure, List.nil_append,
        List.cons_append]
      refine ⟨_, rfl, rfl, rfl, ?_⟩
      simp [hl0]
    · have hne_t :
          (evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
            2 ^ (dst.fractionBits - 1) != 0) = true := by simp [hl0]
      simp only [Bool.not_false, ↓reduceIte, hne_t, List.forIn_cons, List.forIn_nil, hnc, hns,
        bind, Except.bind, pure, Except.pure, List.nil_append, List.cons_append]
      refine ⟨_, rfl, rfl, rfl, ?_⟩
      simp only [hl0, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      refine ⟨rfl, rfl, ?_⟩
      rw [floatBits_isSignaling_eq dst _ hsnan_lt]
      have hdec_s := Anneal.Mir.IeeeFloatCast.decodeBits_encodeBits dst neg
        (2 ^ dst.exponentBits - 1) _ (Nat.sub_lt (Nat.two_pow_pos _) (by decide)) hlow
      simp only [↓reduceIte, hl0] at hdec_s
      rw [hdec_s, quietBit_eq_not_lt dst _ hlow]
      simp [hlow_half]
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.forIn_cons, List.forIn_nil, hnc,
      bind, Except.bind, pure, Except.pure, List.nil_append, List.cons_append]
    refine ⟨_, rfl, rfl, rfl, ?_⟩
    simp

/-- Flipping the sign bit of `encodeBits f neg E F` (`E < 2 ^ f.exponentBits`,
`F < 2 ^ f.fractionBits`) produces `encodeBits f (!neg) E F`. -/
theorem flipSignBits_encodeBits (f : IeeeFormat) (neg : Bool) (E F : Nat)
    (hE : E < 2 ^ f.exponentBits) (hF : F < 2 ^ f.fractionBits) :
    (if neg then encodeBits f neg E F - 2 ^ (f.width - 1)
     else encodeBits f neg E F + 2 ^ (f.width - 1)) =
      encodeBits f (!neg) E F := by
  cases f <;> cases neg <;>
    simp only [encodeBits, zeroBits, IeeeFormat.width, IeeeFormat.exponentBits,
      IeeeFormat.fractionBits, Nat.reducePow, Nat.reduceSub, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte] at hE hF ⊢ <;> omega

/-- Every `encodeBits f neg (2 ^ f.exponentBits - 1) F` with `F ≠ 0` and `F < 2 ^ f.fractionBits`
is an in-width NaN (`< 2 ^ f.width`, `isNaNBits = true`, `FloatBits.isNaN = .ok true`). -/
theorem isNaNBits_encodeBits_maxExp (f : IeeeFormat) (neg : Bool) (F : Nat)
    (hF_ne : F ≠ 0) (hF_lt : F < 2 ^ f.fractionBits) :
    let b := encodeBits f neg (2 ^ f.exponentBits - 1) F
    b < 2 ^ f.width ∧
      Anneal.Mir.IeeeFloatCast.isNaNBits f b = true ∧
      Miri.Interpreter.FloatBits.isNaN ⟨ieeeFormatToMiri f, BitVec.ofNat 128 b⟩ = .ok true := by
  dsimp only
  have hE : 2 ^ f.exponentBits - 1 < 2 ^ f.exponentBits :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have hlt := Anneal.Mir.IeeeFloatCast.encodeBits_lt f neg _ F hE hF_lt
  have hdec := Anneal.Mir.IeeeFloatCast.decodeBits_encodeBits f neg _ F hE hF_lt
  simp only [↓reduceIte, hF_ne] at hdec
  have hnan : Anneal.Mir.IeeeFloatCast.isNaNBits f (encodeBits f neg (2 ^ f.exponentBits - 1) F) = true :=
    Anneal.Mir.IeeeFloatCast.isNaNBits_of_nan f _ neg _ F hdec
  refine ⟨hlt, hnan, ?_⟩
  rw [floatBits_isNaN_eq f _ hlt, hnan]

/-- `FloatBits.negate` on `encodeBits f neg (2 ^ f.exponentBits - 1) F` (`F ≠ 0`,
`F < 2 ^ f.fractionBits`) produces `encodeBits f (!neg) (2 ^ f.exponentBits - 1) F`. -/
theorem floatBits_negate_encodeBits_nan (f : IeeeFormat) (neg : Bool) (F : Nat)
    (hF_ne : F ≠ 0) (hF_lt : F < 2 ^ f.fractionBits) :
    Miri.Interpreter.FloatBits.negate
        ⟨ieeeFormatToMiri f, BitVec.ofNat 128 (encodeBits f neg (2 ^ f.exponentBits - 1) F)⟩ =
      .ok ⟨ieeeFormatToMiri f, BitVec.ofNat 128 (encodeBits f (!neg) (2 ^ f.exponentBits - 1) F)⟩ := by
  have hE : 2 ^ f.exponentBits - 1 < 2 ^ f.exponentBits :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have hlt := Anneal.Mir.IeeeFloatCast.encodeBits_lt f neg _ F hE hF_lt
  have hdec := Anneal.Mir.IeeeFloatCast.decodeBits_encodeBits f neg _ F hE hF_lt
  simp only [↓reduceIte, hF_ne] at hdec
  rw [floatBits_negate_eq f _ hlt, hdec]
  have hflip := flipSignBits_encodeBits f neg _ F hE hF_lt
  cases neg <;>
    simp only [floatKindToMiriDecoded, miriDecodedToVendored,
      Anneal.Mir.IeeeFloatCast.floatKindToMiri, Bool.false_eq_true, ↓reduceIte] at hflip ⊢ <;>
    rw [hflip]

/-- **Complete list equality for `FloatBits.nanChoices` (`nondet = true`)**, pinning every
even AND odd (sign-negated) entry:
* indices `0, 1`: `preferredNaNBits dst` and its sign-negation
  `encodeBits dst true (2 ^ dst.exponentBits - 1) (2 ^ (dst.fractionBits - 1))`;
* indices `2, 3`: `convBits = encodeBits dst neg (2 ^ dst.exponentBits - 1) (convBits % 2 ^ dst.fractionBits)`
  and its sign-negation `encodeBits dst (!neg) (2 ^ dst.exponentBits - 1) (convBits % 2 ^ dst.fractionBits)`;
* indices `4, 5` (present iff `q = false ∧ lower ≠ 0`): the `dst` signaling NaN
  `encodeBits dst neg (2 ^ dst.exponentBits - 1) lower` and its sign-negation
  `encodeBits dst (!neg) (2 ^ dst.exponentBits - 1) lower`. -/
theorem floatBits_nanChoices_nondet_list_eq (src dst : IeeeFormat) (bits : Nat)
    (h : bits < 2 ^ src.width) (neg q : Bool) (payload : Nat)
    (hnan : decodeBits src bits = .nan neg q payload) :
    let convBits := evalFloatToFloatRoundTiesToEven src dst bits
    let convPay := convBits % 2 ^ dst.fractionBits
    let lower := convPay % 2 ^ (dst.fractionBits - 1)
    let mkFb (b : Nat) : Miri.Interpreter.FloatBits := ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 b⟩
    let prefPos := mkFb (preferredNaNBits dst)
    let prefNeg := mkFb (encodeBits dst true (2 ^ dst.exponentBits - 1) (2 ^ (dst.fractionBits - 1)))
    let convPos := mkFb convBits
    let convNeg := mkFb (encodeBits dst (!neg) (2 ^ dst.exponentBits - 1) convPay)
    let snanPos := mkFb (encodeBits dst neg (2 ^ dst.exponentBits - 1) lower)
    let snanNeg := mkFb (encodeBits dst (!neg) (2 ^ dst.exponentBits - 1) lower)
    Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
        [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] true =
      .ok (if q = false ∧ lower ≠ 0 then
          [prefPos, prefNeg, convPos, convNeg, snanPos, snanNeg]
        else
          [prefPos, prefNeg, convPos, convNeg]) := by
  dsimp only
  have hnanb : Anneal.Mir.IeeeFloatCast.isNaNBits src bits = true :=
    Anneal.Mir.IeeeFloatCast.isNaNBits_of_nan src bits neg q payload hnan
  have hconvlt := Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst bits
  have hdk :=
    Anneal.Mir.IeeeFloatCast.decodeBits_evalFloatToFloatRoundTiesToEven_of_nan src dst bits neg q payload hnan
  obtain ⟨hpay_mod, hcp_ne, hplt, _⟩ :=
    Anneal.Mir.IeeeFloatCast.decodeBits_nan_payload dst
      (evalFloatToFloatRoundTiesToEven src dst bits) neg true _ hdk
  rw [hpay_mod] at hdk hcp_ne hplt
  have hconv_enc : evalFloatToFloatRoundTiesToEven src dst bits =
      encodeBits dst neg (2 ^ dst.exponentBits - 1)
        (evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits) := by
    conv =>
      lhs
      rw [Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_of_nan src dst bits neg q payload hnan,
        hpay_mod]
  have hdecc := floatBits_decode_eq dst (evalFloatToFloatRoundTiesToEven src dst bits) hconvlt
  rw [hdk] at hdecc
  have hnp : Miri.Interpreter.FloatBits.negate
      ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (preferredNaNBits dst)⟩ =
      .ok ⟨ieeeFormatToMiri dst,
        BitVec.ofNat 128 (encodeBits dst true (2 ^ dst.exponentBits - 1) (2 ^ (dst.fractionBits - 1)))⟩ := by
    cases dst <;> rfl
  have hnc : Miri.Interpreter.FloatBits.negate
      ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩ =
      .ok ⟨ieeeFormatToMiri dst,
        BitVec.ofNat 128 (encodeBits dst (!neg) (2 ^ dst.exponentBits - 1)
          (evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits))⟩ := by
    conv => lhs; rw [hconv_enc]
    exact floatBits_negate_encodeBits_nan dst neg _ hcp_ne hplt
  unfold Miri.Interpreter.FloatBits.nanChoices
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.forIn_cons, List.forIn_nil,
    floatBits_isNaN_eq src bits h, hnanb, floatBits_convert_eq src dst bits h,
    floatBits_isSignaling_eq src bits h, hnan, hdecc, floatBits_preferredNaN_eq, hnp,
    bind, Except.bind, pure, Except.pure, List.nil_append,
    floatKindToMiriDecoded, miriDecodedToVendored, Anneal.Mir.IeeeFloatCast.floatKindToMiri,
    ieeeFormatToMiri_fractionBits, ieeeFormatToMiri_exponentBits, miri_encode_eq]
  cases q with
  | false =>
    by_cases hl0 :
        evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
          2 ^ (dst.fractionBits - 1) = 0
    · have hne_f :
          (evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
            2 ^ (dst.fractionBits - 1) != 0) = false := by simp [hl0]
      simp only [Bool.not_false, ↓reduceIte, hne_f, Bool.false_eq_true, List.forIn_cons,
        List.forIn_nil, hnc, bind, Except.bind, pure, Except.pure, List.nil_append,
        List.cons_append]
      simp [hl0]
    · have hne_t :
          (evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
            2 ^ (dst.fractionBits - 1) != 0) = true := by simp [hl0]
      have hlow :
          evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
              2 ^ (dst.fractionBits - 1) <
            2 ^ dst.fractionBits :=
        Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Anneal.Mir.IeeeFloatCast.two_pow_le_two_pow (Nat.sub_le _ _))
      have hns := floatBits_negate_encodeBits_nan dst neg _ hl0 hlow
      simp only [Bool.not_false, ↓reduceIte, hne_t, List.forIn_cons, List.forIn_nil, hnc, hns,
        bind, Except.bind, pure, Except.pure, List.nil_append, List.cons_append]
      simp [hl0]
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.forIn_cons, List.forIn_nil, hnc,
      bind, Except.bind, pure, Except.pure, List.nil_append, List.cons_append]
    simp

/-- **Universal NaN soundness of `FloatBits.nanChoices`**: in **either** `nondet : Bool` mode,
`nanChoices` on any NaN input `bits < 2 ^ src.width` succeeds with a non-empty list, and
**every** candidate `fb ∈ candidates` is an in-width `dst` NaN (`fb.format = ieeeFormatToMiri dst`,
`fb.bits.toNat < 2 ^ dst.width`, `isNaNBits dst fb.bits.toNat = true`, `fb.isNaN = .ok true`). -/
theorem floatBits_mem_nanChoices_isNaN (src dst : IeeeFormat) (bits : Nat)
    (h : bits < 2 ^ src.width) (neg q : Bool) (payload : Nat)
    (hnan : decodeBits src bits = .nan neg q payload) (nondet : Bool) :
    ∃ candidates,
      Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
          [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] nondet = .ok candidates ∧
      candidates ≠ [] ∧
      ∀ fb ∈ candidates,
        fb.format = ieeeFormatToMiri dst ∧
        fb.bits.toNat < 2 ^ dst.width ∧
        Anneal.Mir.IeeeFloatCast.isNaNBits dst fb.bits.toNat = true ∧
        fb.isNaN = .ok true := by
  have hmk : ∀ b, b < 2 ^ dst.width →
      Anneal.Mir.IeeeFloatCast.isNaNBits dst b = true →
      (⟨ieeeFormatToMiri dst, BitVec.ofNat 128 b⟩ : Miri.Interpreter.FloatBits).format =
          ieeeFormatToMiri dst ∧
        (⟨ieeeFormatToMiri dst, BitVec.ofNat 128 b⟩ : Miri.Interpreter.FloatBits).bits.toNat <
          2 ^ dst.width ∧
        Anneal.Mir.IeeeFloatCast.isNaNBits dst
          (⟨ieeeFormatToMiri dst, BitVec.ofNat 128 b⟩ : Miri.Interpreter.FloatBits).bits.toNat = true ∧
        (⟨ieeeFormatToMiri dst, BitVec.ofNat 128 b⟩ : Miri.Interpreter.FloatBits).isNaN = .ok true := by
    intro b hblt hbnan
    have hto : (BitVec.ofNat 128 b).toNat = b := bitVec128_toNat_of_lt_width hblt
    refine ⟨rfl, ?_, ?_, ?_⟩
    · dsimp only []; rw [hto]; exact hblt
    · dsimp only []; rw [hto]; exact hbnan
    · rw [floatBits_isNaN_eq dst b hblt, hbnan]
  have hpref_lt : preferredNaNBits dst < 2 ^ dst.width :=
    Anneal.Mir.IeeeFloatCast.preferredNaNBits_lt dst
  have hpref_nan : Anneal.Mir.IeeeFloatCast.isNaNBits dst (preferredNaNBits dst) = true := by
    cases dst <;> rfl
  cases nondet with
  | false =>
    refine ⟨[Miri.Interpreter.FloatBits.preferredNaN (ieeeFormatToMiri dst)], rfl,
      List.cons_ne_nil _ _, ?_⟩
    intro fb hfb
    rcases List.mem_singleton.mp hfb with rfl
    rw [floatBits_preferredNaN_eq]
    exact hmk _ hpref_lt hpref_nan
  | true =>
    have hlist := floatBits_nanChoices_nondet_list_eq src dst bits h neg q payload hnan
    dsimp only at hlist
    have hpneg := isNaNBits_encodeBits_maxExp dst true (2 ^ (dst.fractionBits - 1))
      (Nat.ne_of_gt (Nat.two_pow_pos _))
      (by cases dst <;> decide)
    have hconv_lt := Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst bits
    have hconv_nan : Anneal.Mir.IeeeFloatCast.isNaNBits dst
        (evalFloatToFloatRoundTiesToEven src dst bits) = true := by
      rw [Anneal.Mir.IeeeFloatCast.isNaNBits_evalFloatToFloatRoundTiesToEven]
      exact Anneal.Mir.IeeeFloatCast.isNaNBits_of_nan src bits neg q payload hnan
    have hdk :=
      Anneal.Mir.IeeeFloatCast.decodeBits_evalFloatToFloatRoundTiesToEven_of_nan src dst bits neg q payload hnan
    obtain ⟨hpay_mod, hcp_ne, hplt, _⟩ :=
      Anneal.Mir.IeeeFloatCast.decodeBits_nan_payload dst
        (evalFloatToFloatRoundTiesToEven src dst bits) neg true _ hdk
    rw [hpay_mod] at hcp_ne hplt
    have hcneg := isNaNBits_encodeBits_maxExp dst (!neg) _ hcp_ne hplt
    by_cases hcond : q = false ∧
        evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
          2 ^ (dst.fractionBits - 1) ≠ 0
    · rcases hcond with ⟨hq_f, hne0⟩
      simp only [hq_f, hne0, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at hlist
      have hlow :
          evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
              2 ^ (dst.fractionBits - 1) <
            2 ^ dst.fractionBits :=
        Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Anneal.Mir.IeeeFloatCast.two_pow_le_two_pow (Nat.sub_le _ _))
      have hspos := isNaNBits_encodeBits_maxExp dst neg _ hne0 hlow
      have hsneg := isNaNBits_encodeBits_maxExp dst (!neg) _ hne0 hlow
      refine ⟨_, hlist, List.cons_ne_nil _ _, ?_⟩
      intro fb hfb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hfb
      rcases hfb with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hmk _ hpref_lt hpref_nan
      · exact hmk _ hpneg.1 hpneg.2.1
      · exact hmk _ hconv_lt hconv_nan
      · exact hmk _ hcneg.1 hcneg.2.1
      · exact hmk _ hspos.1 hspos.2.1
      · exact hmk _ hsneg.1 hsneg.2.1
    · simp only [hcond, ↓reduceIte] at hlist
      refine ⟨_, hlist, List.cons_ne_nil _ _, ?_⟩
      intro fb hfb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hfb
      rcases hfb with rfl | rfl | rfl | rfl
      · exact hmk _ hpref_lt hpref_nan
      · exact hmk _ hpneg.1 hpneg.2.1
      · exact hmk _ hconv_lt hconv_nan
      · exact hmk _ hcneg.1 hcneg.2.1

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

/-- **Soundness of `FloatOps.adjustNaN` for any valid `chooseNaN` selector**: whenever, in
nondeterministic mode, `h.chooseNaN choice cs` returns an in-bounds index `idx < cs.length`
without mutating `st` on every candidate list of length `≥ 4` (the only lists `nanChoices`
produces: `floatBits_nanChoices_nondet_list_eq`; satisfied by every constant selector `pure i`
with `i < 4`, in particular the refinement witness `annealChooseQuietedNaN`), `adjustNaN` returns
the exact `evalFloatToFloatRoundTiesToEven` bits on non-NaN inputs and some in-width `dst` NaN
(`outBits < 2 ^ dst.width`, `isNaNBits dst outBits = true`, equal to `preferredNaNBits dst` when
`h.floatNondeterministic = false`, where `chooseNaN` is never consulted) on NaN inputs. -/
theorem floatOps_adjustNaN_any_chooseNaN {P S C : Type} (h : Miri.Interpreter.FloatOpsHooks P S C)
    (choice : C) (src dst : IeeeFormat) (bits : Nat) (hlt : bits < 2 ^ src.width) (st : S)
    (hchoose : h.floatNondeterministic = true → ∀ cs : List Miri.Interpreter.FloatBits,
      4 ≤ cs.length → ∃ idx < cs.length, h.chooseNaN choice cs st = .ok idx st) :
    ∃ outBits < 2 ^ dst.width,
      Miri.Interpreter.FloatOps.adjustNaN h choice
          ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩
          [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] st =
        .ok ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 outBits⟩ st ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src bits = false →
        outBits = evalFloatToFloatRoundTiesToEven src dst bits) ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src bits = true →
        Anneal.Mir.IeeeFloatCast.isNaNBits dst outBits = true ∧
          (h.floatNondeterministic = false → outBits = preferredNaNBits dst)) := by
  have hclt := Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst bits
  have hiff := Anneal.Mir.IeeeFloatCast.isNaNBits_evalFloatToFloatRoundTiesToEven src dst bits
  cases hsn : Anneal.Mir.IeeeFloatCast.isNaNBits src bits with
  | false =>
    rw [hsn] at hiff
    exact ⟨_, hclt, floatOps_adjustNaN_of_not_nan h choice dst _ hclt hiff _ st,
      fun _ => rfl, fun hf => absurd hf Bool.noConfusion⟩
  | true =>
    rw [hsn] at hiff
    have hdec : ∃ neg q payload, decodeBits src bits = .nan neg q payload := by
      unfold Anneal.Mir.IeeeFloatCast.isNaNBits at hsn
      split at hsn
      · rename_i neg q payload hk; exact ⟨neg, q, payload, hk⟩
      · cases hsn
    obtain ⟨neg, q, payload, hk⟩ := hdec
    cases hnd : h.floatNondeterministic with
    | false =>
      have hadj := floatOps_adjustNaN_deterministic h choice hnd src dst bits st
      rw [hsn] at hadj; simp only [↓reduceIte] at hadj
      have hp_lt := Anneal.Mir.IeeeFloatCast.preferredNaNBits_lt dst
      have hp_nan : Anneal.Mir.IeeeFloatCast.isNaNBits dst (preferredNaNBits dst) = true := by
        cases dst <;> rfl
      exact ⟨preferredNaNBits dst, hp_lt, hadj, fun hf => absurd hf Bool.noConfusion,
        fun _ => ⟨hp_nan, fun _ => rfl⟩⟩
    | true =>
      obtain ⟨cs, hcs, _, hall⟩ :=
        floatBits_mem_nanChoices_isNaN src dst bits hlt neg q payload hk true
      have hlen : 4 ≤ cs.length := by
        have hl := floatBits_nanChoices_nondet_list_eq src dst bits hlt neg q payload hk
        dsimp only at hl
        rw [hl] at hcs
        injection hcs with hcs'
        rw [← hcs']
        split <;> simp
      obtain ⟨idx, hidx_lt, hsel⟩ := hchoose hnd cs hlen
      have hget : cs[idx]? = some (cs[idx]'hidx_lt) := List.getElem?_eq_getElem hidx_lt
      have hmem : (cs[idx]'hidx_lt) ∈ cs := List.getElem_mem hidx_lt
      obtain ⟨hfmt, hblt, hbnan, _⟩ := hall _ hmem
      have hfb_eq : (cs[idx]'hidx_lt) =
          ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (cs[idx]'hidx_lt).bits.toNat⟩ := by
        generalize hcand : cs[idx]'hidx_lt = cand at hfmt hblt
        rcases cand with ⟨fmt0, b0⟩
        dsimp only at hfmt hblt ⊢
        subst hfmt
        congr 1
        have hb128 : b0.toNat < 2 ^ 128 := by
          have : 2 ^ dst.width ≤ 2 ^ 128 := by cases dst <;> decide
          omega
        exact (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb128])).symm
      refine ⟨(cs[idx]'hidx_lt).bits.toNat, hblt, ?_, fun hf => absurd hf Bool.noConfusion,
        fun _ => ⟨hbnan, fun hf => absurd hf Bool.noConfusion⟩⟩
      have hadj_fn : Miri.Interpreter.FloatOps.adjustNaN h choice
          ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩
          [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] =
          (h.chooseNaN choice cs >>= fun index =>
            match cs[index]? with
            | some chosen => pure chosen
            | _ => throw (.invalidProgram "invalid floating NaN choice index")) := by
        unfold Miri.Interpreter.FloatOps.adjustNaN
        simp only [floatBits_isNaN_eq dst _ hclt, hiff, hnd, hcs, floatOps_engine_ok, pure_bind,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rfl
      rw [congrFun hadj_fn st, EStateM.bind_eq_ok hsel, hget, ← hfb_eq]
      rfl

/-- **Exact constant-index NaN choice**: in nondeterministic mode with a state-preserving
constant selector returning index `i < 4`, `FloatOps.adjustNaN` on a NaN input returns exactly
the `i`-th `nanChoices` candidate: `preferredNaNBits dst` (`i = 0`), its sign-negation (`i = 1`),
the quieted conversion `evalFloatToFloatRoundTiesToEven src dst bits` (`i = 2`, the refinement
witness), or its sign-negation (`i = 3`). The first four candidates do not depend on the
signaling-NaN extension (`floatBits_nanChoices_nondet_list_eq`). -/
theorem floatOps_adjustNaN_pure_index {P S C : Type} (h : Miri.Interpreter.FloatOpsHooks P S C)
    (choice : C) (hnd : h.floatNondeterministic = true) (i : Nat) (hi : i < 4)
    (hsel : ∀ cs st, h.chooseNaN choice cs st = .ok i st)
    (src dst : IeeeFormat) (bits : Nat) (hlt : bits < 2 ^ src.width) (neg q : Bool)
    (payload : Nat) (hnan : decodeBits src bits = .nan neg q payload) (st : S) :
    Miri.Interpreter.FloatOps.adjustNaN h choice
        ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩
        [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] st =
      .ok ⟨ieeeFormatToMiri dst, BitVec.ofNat 128
        ([preferredNaNBits dst,
          encodeBits dst true (2 ^ dst.exponentBits - 1) (2 ^ (dst.fractionBits - 1)),
          evalFloatToFloatRoundTiesToEven src dst bits,
          encodeBits dst (!neg) (2 ^ dst.exponentBits - 1)
            (evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits)][i]'
          (by simpa using hi))⟩ st := by
  have hclt := Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst bits
  have hsn : Anneal.Mir.IeeeFloatCast.isNaNBits src bits = true :=
    Anneal.Mir.IeeeFloatCast.isNaNBits_of_nan src bits neg q payload hnan
  have hiff := Anneal.Mir.IeeeFloatCast.isNaNBits_evalFloatToFloatRoundTiesToEven src dst bits
  rw [hsn] at hiff
  have hl := floatBits_nanChoices_nondet_list_eq src dst bits hlt neg q payload hnan
  dsimp only at hl
  obtain ⟨cs, hcs, hidx⟩ : ∃ cs : List Miri.Interpreter.FloatBits,
      Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
        [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] true = .ok cs ∧
      cs[i]? = some ⟨ieeeFormatToMiri dst, BitVec.ofNat 128
        ([preferredNaNBits dst,
          encodeBits dst true (2 ^ dst.exponentBits - 1) (2 ^ (dst.fractionBits - 1)),
          evalFloatToFloatRoundTiesToEven src dst bits,
          encodeBits dst (!neg) (2 ^ dst.exponentBits - 1)
            (evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits)][i]'
          (by simpa using hi))⟩ := by
    refine ⟨_, hl, ?_⟩
    obtain _ | _ | _ | _ | i := i
    · split <;> rfl
    · split <;> rfl
    · split <;> rfl
    · split <;> rfl
    · omega
  have hfn : Miri.Interpreter.FloatOps.adjustNaN h choice
      ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩
      [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] =
      (h.chooseNaN choice cs >>= fun index =>
        match cs[index]? with
        | some chosen => pure chosen
        | _ => throw (.invalidProgram "invalid floating NaN choice index")) := by
    unfold Miri.Interpreter.FloatOps.adjustNaN
    simp only [floatBits_isNaN_eq dst _ hclt, hiff, hnd, hcs, floatOps_engine_ok, pure_bind,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [congrFun hfn st, EStateM.bind_eq_ok (hsel _ st), hidx]
  rfl

/-- Closed-form `dst` bit pattern produced by `FloatOps.adjustNaN` in nondeterministic mode
when `chooseNaN` deterministically selects candidate index `i`:
* on non-NaN inputs, `evalFloatToFloatRoundTiesToEven src dst bits`;
* on NaN inputs (`decodeBits src bits = .nan neg q payload`), the `i`-th entry of
  `[preferredNaNBits dst, -preferredNaNBits dst, convBits, -convBits]` for `i < 4`, plus on
  signaling NaNs with non-zero scaled lower payload (`q = false ∧ lower ≠ 0`) the positive (`i = 4`)
  and negated (`i = 5`) `dst` signaling-NaN candidates of `FloatBits.nanChoices`. -/
def floatToFloatPureIndexBits (src dst : IeeeFormat) (bits i : Nat) : Nat :=
  let convBits := evalFloatToFloatRoundTiesToEven src dst bits
  match decodeBits src bits with
  | .nan neg q _ =>
    let lower := convBits % 2 ^ dst.fractionBits % 2 ^ (dst.fractionBits - 1)
    let negPref := encodeBits dst true (2 ^ dst.exponentBits - 1) (2 ^ (dst.fractionBits - 1))
    let negConv := encodeBits dst (!neg) (2 ^ dst.exponentBits - 1) (convBits % 2 ^ dst.fractionBits)
    match i with
    | 0 => preferredNaNBits dst
    | 1 => negPref
    | 2 => convBits
    | 3 => negConv
    | 4 => if !q && (lower != 0) then encodeBits dst neg (2 ^ dst.exponentBits - 1) lower else negConv
    | _ => if !q && (lower != 0) then encodeBits dst (!neg) (2 ^ dst.exponentBits - 1) lower else negConv
  | _ => convBits

theorem floatToFloatPureIndexBits_lt (src dst : IeeeFormat) (bits i : Nat) :
    floatToFloatPureIndexBits src dst bits i < 2 ^ dst.width := by
  unfold floatToFloatPureIndexBits
  dsimp only
  split
  · rename_i neg q payload hnan
    have hdk :=
      Anneal.Mir.IeeeFloatCast.decodeBits_evalFloatToFloatRoundTiesToEven_of_nan src dst bits neg q payload hnan
    obtain ⟨hpay_mod, _, hplt, _⟩ :=
      Anneal.Mir.IeeeFloatCast.decodeBits_nan_payload dst
        (evalFloatToFloatRoundTiesToEven src dst bits) neg true _ hdk
    rw [hpay_mod] at hplt
    have hE : 2 ^ dst.exponentBits - 1 < 2 ^ dst.exponentBits :=
      Nat.sub_lt (Nat.two_pow_pos _) (by decide)
    have hlow_lt :
        evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
          2 ^ (dst.fractionBits - 1) < 2 ^ dst.fractionBits :=
      Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_lt_pow_right (by decide) (by cases dst <;> decide))
    split
    · exact Anneal.Mir.IeeeFloatCast.preferredNaNBits_lt dst
    · exact Anneal.Mir.IeeeFloatCast.encodeBits_lt dst true _ _ hE (by cases dst <;> decide)
    · exact Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst bits
    · exact Anneal.Mir.IeeeFloatCast.encodeBits_lt dst (!neg) _ _ hE hplt
    · split
      · exact Anneal.Mir.IeeeFloatCast.encodeBits_lt dst neg _ _ hE hlow_lt
      · exact Anneal.Mir.IeeeFloatCast.encodeBits_lt dst (!neg) _ _ hE hplt
    · split
      · exact Anneal.Mir.IeeeFloatCast.encodeBits_lt dst (!neg) _ _ hE hlow_lt
      · exact Anneal.Mir.IeeeFloatCast.encodeBits_lt dst (!neg) _ _ hE hplt
  · exact Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst bits

/-- **`floatToFloatPureIndexBits` is `lean-miri`'s own `i`-th candidate, not an independent
semantics**: on a NaN input it is exactly the `i`-th entry (`i < 4`) of the list that
`FloatBits.nanChoices` itself returns, and on a non-NaN input it is the trusted conversion,
which `FloatOps.adjustNaN` returns unchanged (`floatOps_adjustNaN_of_not_nan`). -/
theorem floatToFloatPureIndexBits_spec (src dst : IeeeFormat) (bits : Nat)
    (h : bits < 2 ^ src.width) (i : Nat) (hi : i < 4) :
    (Anneal.Mir.IeeeFloatCast.isNaNBits src bits = false →
      floatToFloatPureIndexBits src dst bits i = evalFloatToFloatRoundTiesToEven src dst bits) ∧
    (Anneal.Mir.IeeeFloatCast.isNaNBits src bits = true →
      ∃ cs, Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
          [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] true = .ok cs ∧
        cs[i]? = some ⟨ieeeFormatToMiri dst,
          BitVec.ofNat 128 (floatToFloatPureIndexBits src dst bits i)⟩) := by
  constructor
  · intro hn
    unfold floatToFloatPureIndexBits
    dsimp only
    unfold Anneal.Mir.IeeeFloatCast.isNaNBits at hn
    split
    · rename_i neg q payload hk; rw [hk] at hn; cases hn
    · rfl
  · intro hn
    have hdec : ∃ neg q payload, decodeBits src bits = .nan neg q payload := by
      unfold Anneal.Mir.IeeeFloatCast.isNaNBits at hn
      split at hn
      · rename_i neg q payload hk; exact ⟨neg, q, payload, hk⟩
      · cases hn
    obtain ⟨neg, q, payload, hk⟩ := hdec
    have hl := floatBits_nanChoices_nondet_list_eq src dst bits h neg q payload hk
    dsimp only at hl
    refine ⟨_, hl, ?_⟩
    unfold floatToFloatPureIndexBits
    dsimp only
    simp only [hk]
    obtain _ | _ | _ | _ | i := i
    · split <;> rfl
    · split <;> rfl
    · split <;> rfl
    · split <;> rfl
    · omega

/-- **Full 6-index signaling-NaN specification of `floatToFloatPureIndexBits` (`i < 6`)**: on a
signaling NaN input (`q = false`) whose scaled lower payload bits do not vanish (`lower ≠ 0`),
`FloatBits.nanChoices` produces a 6-element list and `floatToFloatPureIndexBits src dst bits i`
is literally its `i`-th entry across **all six** indices `0 ≤ i < 6` (including the positive and
negated `dst` signaling NaNs at `i = 4` and `i = 5`). -/
theorem floatToFloatPureIndexBits_snan_spec (src dst : IeeeFormat) (bits : Nat)
    (h : bits < 2 ^ src.width) (neg : Bool) (payload : Nat)
    (hnan : decodeBits src bits = .nan neg false payload)
    (hlow_ne : evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
      2 ^ (dst.fractionBits - 1) ≠ 0)
    (i : Nat) (hi : i < 6) :
    ∃ cs, Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
        [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] true = .ok cs ∧
      cs.length = 6 ∧
      cs[i]? = some ⟨ieeeFormatToMiri dst,
        BitVec.ofNat 128 (floatToFloatPureIndexBits src dst bits i)⟩ := by
  have hl := floatBits_nanChoices_nondet_list_eq src dst bits h neg false payload hnan
  dsimp only at hl
  simp only [hlow_ne, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at hl
  have hbn : (evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
      2 ^ (dst.fractionBits - 1) != 0) = true := bne_iff_ne.mpr hlow_ne
  refine ⟨_, hl, rfl, ?_⟩
  unfold floatToFloatPureIndexBits
  dsimp only
  simp only [hnan, Bool.not_false, Bool.true_and, hbn, ↓reduceIte]
  obtain _ | _ | _ | _ | _ | _ | i := i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · omega

/-- **Exact constant-index NaN choice across all inputs (`i < 4`)**: extends
`floatOps_adjustNaN_pure_index` from NaN-only inputs to **every** `bits < 2 ^ src.width`
(both finite/infinite and NaN). -/
theorem floatOps_adjustNaN_pure_index_all {P S C : Type} (h : Miri.Interpreter.FloatOpsHooks P S C)
    (choice : C) (hnd : h.floatNondeterministic = true) (i : Nat) (hi : i < 4)
    (hsel : ∀ cs st, h.chooseNaN choice cs st = .ok i st)
    (src dst : IeeeFormat) (bits : Nat) (hlt : bits < 2 ^ src.width) (st : S) :
    Miri.Interpreter.FloatOps.adjustNaN h choice
        ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩
        [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] st =
      .ok ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (floatToFloatPureIndexBits src dst bits i)⟩ st := by
  have hclt := Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst bits
  have hiff := Anneal.Mir.IeeeFloatCast.isNaNBits_evalFloatToFloatRoundTiesToEven src dst bits
  unfold floatToFloatPureIndexBits
  dsimp only
  cases hk : decodeBits src bits with
  | nan neg q payload =>
    have hp := floatOps_adjustNaN_pure_index h choice hnd i hi hsel src dst bits hlt neg q payload hk st
    obtain _ | _ | _ | _ | i := i
    · exact hp
    · exact hp
    · exact hp
    · exact hp
    · omega
  | zero _ | inf _ | finite _ _ _ =>
    have hsn : Anneal.Mir.IeeeFloatCast.isNaNBits src bits = false := by
      unfold Anneal.Mir.IeeeFloatCast.isNaNBits; rw [hk]
    rw [hsn] at hiff
    exact floatOps_adjustNaN_of_not_nan h choice dst _ hclt hiff _ st

/-- **Signaling-NaN 6-candidate constant-index choice (`i < 6`)**: on a signaling NaN input
(`q = false`) whose scaled lower payload bits do not vanish (`lower ≠ 0`), `nanChoices` has all
6 candidates (`floatBits_nanChoices_nondet_list_eq`), so a constant selector returning any
`i < 6` succeeds — with `i = 4` and `i = 5` selecting the positive/negated `dst` **signaling**
NaNs (`FloatBits.isSignaling = .ok true`). -/
theorem floatOps_adjustNaN_pure_snan_index {P S C : Type} (h : Miri.Interpreter.FloatOpsHooks P S C)
    (choice : C) (hnd : h.floatNondeterministic = true) (i : Nat) (hi : i < 6)
    (hsel : ∀ cs st, h.chooseNaN choice cs st = .ok i st)
    (src dst : IeeeFormat) (bits : Nat) (hlt : bits < 2 ^ src.width) (neg : Bool)
    (payload : Nat) (hnan : decodeBits src bits = .nan neg false payload)
    (hlow_ne : evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
      2 ^ (dst.fractionBits - 1) ≠ 0) (st : S) :
    let convBits := evalFloatToFloatRoundTiesToEven src dst bits
    let convPay := convBits % 2 ^ dst.fractionBits
    let lower := convPay % 2 ^ (dst.fractionBits - 1)
    let outBits :=
      [preferredNaNBits dst,
       encodeBits dst true (2 ^ dst.exponentBits - 1) (2 ^ (dst.fractionBits - 1)),
       convBits,
       encodeBits dst (!neg) (2 ^ dst.exponentBits - 1) convPay,
       encodeBits dst neg (2 ^ dst.exponentBits - 1) lower,
       encodeBits dst (!neg) (2 ^ dst.exponentBits - 1) lower][i]'(by simpa using hi)
    Miri.Interpreter.FloatOps.adjustNaN h choice
        ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 convBits⟩
        [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] st =
      .ok ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 outBits⟩ st ∧
    (i = 4 ∨ i = 5 →
      Miri.Interpreter.FloatBits.isSignaling ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 outBits⟩ =
        .ok true) := by
  dsimp only
  have hclt := Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst bits
  have hsn : Anneal.Mir.IeeeFloatCast.isNaNBits src bits = true :=
    Anneal.Mir.IeeeFloatCast.isNaNBits_of_nan src bits neg false payload hnan
  have hiff := Anneal.Mir.IeeeFloatCast.isNaNBits_evalFloatToFloatRoundTiesToEven src dst bits
  rw [hsn] at hiff
  have hl := floatBits_nanChoices_nondet_list_eq src dst bits hlt neg false payload hnan
  dsimp only at hl
  simp only [hlow_ne, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at hl
  obtain ⟨cs, hcs, hidx⟩ : ∃ cs : List Miri.Interpreter.FloatBits,
      Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
        [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] true = .ok cs ∧
      cs[i]? = some ⟨ieeeFormatToMiri dst, BitVec.ofNat 128
        ([preferredNaNBits dst,
          encodeBits dst true (2 ^ dst.exponentBits - 1) (2 ^ (dst.fractionBits - 1)),
          evalFloatToFloatRoundTiesToEven src dst bits,
          encodeBits dst (!neg) (2 ^ dst.exponentBits - 1)
            (evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits),
          encodeBits dst neg (2 ^ dst.exponentBits - 1)
            (evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
              2 ^ (dst.fractionBits - 1)),
          encodeBits dst (!neg) (2 ^ dst.exponentBits - 1)
            (evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
              2 ^ (dst.fractionBits - 1))][i]'(by simpa using hi))⟩ := by
    refine ⟨_, hl, ?_⟩
    obtain _ | _ | _ | _ | _ | _ | i := i <;> first | rfl | omega
  have hfn : Miri.Interpreter.FloatOps.adjustNaN h choice
      ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩
      [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] =
      (h.chooseNaN choice cs >>= fun index =>
        match cs[index]? with
        | some chosen => pure chosen
        | _ => throw (.invalidProgram "invalid floating NaN choice index")) := by
    unfold Miri.Interpreter.FloatOps.adjustNaN
    simp only [floatBits_isNaN_eq dst _ hclt, hiff, hnd, hcs, floatOps_engine_ok, pure_bind,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hlow_half :
      evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
          2 ^ (dst.fractionBits - 1) <
        2 ^ (dst.fractionBits - 1) :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hlow_lt :
      evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
          2 ^ (dst.fractionBits - 1) <
        2 ^ dst.fractionBits :=
    Nat.lt_of_lt_of_le hlow_half (Anneal.Mir.IeeeFloatCast.two_pow_le_two_pow (Nat.sub_le _ _))
  have hsig_enc : ∀ sgn : Bool,
      Miri.Interpreter.FloatBits.isSignaling
        ⟨ieeeFormatToMiri dst, BitVec.ofNat 128
          (encodeBits dst sgn (2 ^ dst.exponentBits - 1)
            (evalFloatToFloatRoundTiesToEven src dst bits % 2 ^ dst.fractionBits %
              2 ^ (dst.fractionBits - 1)))⟩ = .ok true := by
    intro sgn
    have hE : 2 ^ dst.exponentBits - 1 < 2 ^ dst.exponentBits :=
      Nat.sub_lt (Nat.two_pow_pos _) (by decide)
    have helt := Anneal.Mir.IeeeFloatCast.encodeBits_lt dst sgn _ _ hE hlow_lt
    rw [floatBits_isSignaling_eq dst _ helt]
    have hdec_s := Anneal.Mir.IeeeFloatCast.decodeBits_encodeBits dst sgn _ _ hE hlow_lt
    simp only [↓reduceIte, hlow_ne] at hdec_s
    rw [hdec_s, quietBit_eq_not_lt dst _ hlow_lt]
    simp [hlow_half]
  refine ⟨?_, ?_⟩
  · rw [congrFun hfn st, EStateM.bind_eq_ok (hsel _ st), hidx]
    rfl
  · rintro (rfl | rfl)
    · exact hsig_enc neg
    · exact hsig_enc (!neg)

/-- **Out-of-range constant selectors make `lean-miri` fail**: in nondeterministic mode, if a
state-preserving constant selector returns an index `i` at or beyond the length of the candidate
list that `FloatBits.nanChoices` produces for a NaN input (e.g. `i ≥ 4` on a quiet NaN, whose list
has 4 entries), `FloatOps.adjustNaN` throws `.invalidProgram "invalid floating NaN choice index"`.
Hence the selector-validity premises of the NaN-choice theorems (`hchoose`, `i < 4`, `i < 6`)
cannot be dropped. -/
theorem floatOps_adjustNaN_pure_out_of_range {P S C : Type}
    (h : Miri.Interpreter.FloatOpsHooks P S C)
    (choice : C) (hnd : h.floatNondeterministic = true) (i : Nat)
    (hsel : ∀ cs st, h.chooseNaN choice cs st = .ok i st)
    (src dst : IeeeFormat) (bits : Nat) (neg q : Bool) (payload : Nat)
    (hnan : decodeBits src bits = .nan neg q payload)
    {cs : List Miri.Interpreter.FloatBits}
    (hcs : Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
      [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] true = .ok cs)
    (hi : cs.length ≤ i) (st : S) :
    Miri.Interpreter.FloatOps.adjustNaN h choice
        ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩
        [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] st =
      .error (.invalidProgram "invalid floating NaN choice index") st := by
  have hclt := Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst bits
  have hsn : Anneal.Mir.IeeeFloatCast.isNaNBits src bits = true :=
    Anneal.Mir.IeeeFloatCast.isNaNBits_of_nan src bits neg q payload hnan
  have hiff := Anneal.Mir.IeeeFloatCast.isNaNBits_evalFloatToFloatRoundTiesToEven src dst bits
  rw [hsn] at hiff
  have hfn : Miri.Interpreter.FloatOps.adjustNaN h choice
      ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst bits)⟩
      [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] =
      (h.chooseNaN choice cs >>= fun index =>
        match cs[index]? with
        | some chosen => pure chosen
        | _ => throw (.invalidProgram "invalid floating NaN choice index")) := by
    unfold Miri.Interpreter.FloatOps.adjustNaN
    simp only [floatBits_isNaN_eq dst _ hclt, hiff, hnd, hcs, floatOps_engine_ok, pure_bind,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [congrFun hfn st, EStateM.bind_eq_ok (hsel _ st), List.getElem?_eq_none hi]
  rfl

/-- On a quiet NaN input the nondeterministic `nanChoices` list has exactly 4 entries
(`floatBits_nanChoices_nondet_list_eq`), so every constant selector `pure i` with `i ≥ 4` is out
of range. -/
theorem floatBits_nanChoices_quiet_length (src dst : IeeeFormat) (bits : Nat)
    (h : bits < 2 ^ src.width) (neg : Bool) (payload : Nat)
    (hnan : decodeBits src bits = .nan neg true payload) :
    ∃ cs, Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
        [⟨ieeeFormatToMiri src, BitVec.ofNat 128 bits⟩] true = .ok cs ∧ cs.length = 4 := by
  have hl := floatBits_nanChoices_nondet_list_eq src dst bits h neg true payload hnan
  dsimp only at hl
  refine ⟨_, hl, ?_⟩
  simp

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

/-! ### `Miri.Interpreter.FloatOps` typed cast adapters (`FloatOps.lean:75-108`) -/

/-- Vendored `Miri.Interpreter.FloatOps.scalarResult` (`private`, `FloatOps.lean:22-25`). -/
local macro "miriFloatOpsScalarResult" : term =>
  `(miri_private% Miri.Interpreter.FloatOps Miri.Interpreter.FloatOps.scalarResult)

theorem floatOps_scalarResult_unfold {P S : Type} (bits : Miri.Interpreter.FloatBits)
    (layout : Miri.ABI.TyAndLayout Miri.MIR.TyId) :
    (miriFloatOpsScalarResult bits layout :
      Miri.Interpreter.RvalueM S (Miri.Interpreter.RvalueImmTy P)) = (do
      if layout.layout.size != bits.format.size then
        throw (.invalidProgram "float result layout size mismatch")
      let scalar ← miriFloatOpsLiftResult
        (Miri.Memory.Scalar.fromUInt bits.bits bits.format.size
          |>.mapError Miri.Interpreter.ScalarOps.scalarError)
      return ⟨.scalar scalar, layout⟩) := rfl

theorem floatOps_scalarResult_eq (f : IeeeFormat) {ty : Ty} (hf : ieeeFormatOfTy? ty = some f)
    (layouts : LayoutTable) (bits : Nat) {msc : Miri.Memory.ScalarInt}
    (hfrom : Miri.Memory.Scalar.fromUInt (Prov := AnnealProv) (BitVec.ofNat 128 bits)
      (ieeeFormatToMiri f).size = .ok (.fromScalarInt msc)) :
    (miriFloatOpsScalarResult ⟨ieeeFormatToMiri f, BitVec.ofNat 128 bits⟩ (translateTy ty layouts) :
      Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RvalueImmTy AnnealProv)) =
      pure ⟨.scalar (.fromScalarInt msc), translateTy ty layouts⟩ := by
  have hT := translateTy_of_ieeeFormatOfTy? hf layouts
  rw [floatOps_scalarResult_unfold, hT]
  simp only [floatLayoutData_size, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hfrom,
    Except.mapError, floatOps_liftResult_ok, pure_bind]

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

/-- **`FloatOps.castFloatToFloat` equivalence** (refinement witness): agrees bit-exactly
with `evalFloatToFloatRoundTiesToEven` on every `f32` / `f64` bit pattern. -/
theorem floatOps_castFloatToFloat_refine_eq (layouts : LayoutTable) {srcTy targetTy : Ty}
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcTy = some src)
    (hdst : ieeeFormatOfTy? targetTy = some dst)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : sc.sizeBytes = src.byteWidth) :
    ∃ msc', ScalarRel ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩ msc' ∧
      Miri.Interpreter.FloatOps.castFloatToFloat
          (annealFloatOpsHooks true annealChooseQuietedNaN) ()
          ⟨.scalar (.fromScalarInt msc), translateTy srcTy layouts⟩
          (translateTy targetTy layouts) =
        pure ⟨.scalar (.fromScalarInt msc'), translateTy targetTy layouts⟩ := by
  have hbits : sc.bits < 2 ^ src.width := by
    have := hrel.canonical; rwa [hsz, scalarModulus_byteWidth] at this
  have hclt := Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst sc.bits
  obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec
    (validScalarBytes_byteWidth dst)
    (caseVal := evalFloatToFloatRoundTiesToEven src dst sc.bits)
    (by rw [scalarModulus_byteWidth]; exact hclt)
  rw [translateSizeBytes_byteWidth] at hfrom
  refine ⟨msc', hrel', ?_⟩
  have hsrcT := translateTy_of_ieeeFormatOfTy? hsrc layouts
  have hdstT := translateTy_of_ieeeFormatOfTy? hdst layouts
  unfold Miri.Interpreter.FloatOps.castFloatToFloat
  rw [hsrcT]
  simp only [floatOps_readBits_annealFloat true annealChooseQuietedNaN src hrel hsz, pure_bind,
    show (translateTy targetTy layouts).ty = floatTyIdOf dst from congrArg (·.ty) hdstT,
    annealFloatOpsHooks_formatOf, floatBits_convert_eq src dst sc.bits hbits, floatOps_engine_ok,
    floatOps_adjustNaN_annealFloat_refine src dst sc.bits hbits,
    floatOps_scalarResult_eq dst hdst layouts _ hfrom]

/-- **`FloatOps.castFloatToFloat` deterministic-mode equivalence**: maps every NaN input to
`preferredNaNBits dst` and agrees with `evalFloatToFloatRoundTiesToEven` on non-NaNs. -/
theorem floatOps_castFloatToFloat_deterministic_eq (layouts : LayoutTable)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {srcTy targetTy : Ty} {src dst : IeeeFormat}
    (hsrc : ieeeFormatOfTy? srcTy = some src) (hdst : ieeeFormatOfTy? targetTy = some dst)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : sc.sizeBytes = src.byteWidth) :
    ∃ msc', ScalarRel
        ⟨if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
          else evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩ msc' ∧
      Miri.Interpreter.FloatOps.castFloatToFloat (annealFloatOpsHooks false chooseNaN) ()
          ⟨.scalar (.fromScalarInt msc), translateTy srcTy layouts⟩
          (translateTy targetTy layouts) =
        pure ⟨.scalar (.fromScalarInt msc'), translateTy targetTy layouts⟩ := by
  have hbits : sc.bits < 2 ^ src.width := by
    have := hrel.canonical; rwa [hsz, scalarModulus_byteWidth] at this
  have hres_lt : (if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
      else evalFloatToFloatRoundTiesToEven src dst sc.bits) < 2 ^ dst.width := by
    split
    · exact Anneal.Mir.IeeeFloatCast.preferredNaNBits_lt dst
    · exact Anneal.Mir.IeeeFloatCast.evalFloatToFloatRoundTiesToEven_lt src dst sc.bits
  obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec
    (validScalarBytes_byteWidth dst) (by rw [scalarModulus_byteWidth]; exact hres_lt)
  rw [translateSizeBytes_byteWidth] at hfrom
  refine ⟨msc', hrel', ?_⟩
  have hsrcT := translateTy_of_ieeeFormatOfTy? hsrc layouts
  have hdstT := translateTy_of_ieeeFormatOfTy? hdst layouts
  unfold Miri.Interpreter.FloatOps.castFloatToFloat
  rw [hsrcT]
  simp only [floatOps_readBits_annealFloat false chooseNaN src hrel hsz, pure_bind,
    show (translateTy targetTy layouts).ty = floatTyIdOf dst from congrArg (·.ty) hdstT,
    annealFloatOpsHooks_formatOf, floatBits_convert_eq src dst sc.bits hbits, floatOps_engine_ok,
    floatOps_adjustNaN_annealFloat_deterministic]
  cases hn : Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits <;>
    simp only [hn, Bool.false_eq_true, ↓reduceIte] at hfrom ⊢ <;>
    exact floatOps_scalarResult_eq dst hdst layouts _ hfrom

/-- **`FloatOps.castFloatToInt` equivalence** across all 12 integer `TyId`s (`10..15` signed
`i8..isize`, `20..25` unsigned `u8..usize`), directly exercising
`annealFloatOpsHooks.integerKindOf`. -/
theorem floatOps_castFloatToInt_eq (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {srcTy targetTy : Ty} {src : IeeeFormat} {t : FloatIntTarget}
    (hsrc : ieeeFormatOfTy? srcTy = some src) (hdst : floatIntTargetOfTy? targetTy = some t)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : sc.sizeBytes = src.byteWidth) :
    ∃ msc', ScalarRel (evalFloatToIntSaturating src sc.bits t .bits64) msc' ∧
      Miri.Interpreter.FloatOps.castFloatToInt (annealFloatOpsHooks nondet chooseNaN) ()
          ⟨.scalar (.fromScalarInt msc), translateTy srcTy layouts⟩
          (translateTy targetTy layouts) =
        pure ⟨.scalar (.fromScalarInt msc'), translateTy targetTy layouts⟩ := by
  have hbits : sc.bits < 2 ^ src.width := by
    have := hrel.canonical; rwa [hsz, scalarModulus_byteWidth] at this
  obtain ⟨msc', hfrom, hrel'⟩ := floatToInt_scalar_spec src sc.bits t
  refine ⟨msc', hrel', ?_⟩
  have hsrcT := translateTy_of_ieeeFormatOfTy? hsrc layouts
  have hdstT := translateTy_of_floatIntTargetOfTy? hdst layouts
  unfold Miri.Interpreter.FloatOps.castFloatToInt
  rw [hsrcT, hdstT]
  simp only [floatOps_readBits_annealFloat nondet chooseNaN src hrel hsz, pure_bind,
    annealFloatOpsHooks_integerKindOf, floatIntTargetKind_signed,
    scalarLayoutData_floatIntTarget_size, translateSizeBytes_floatIntTarget_bitsNat,
    Except.mapError, floatOps_liftResult_ok,
    floatBits_toInteger_eq src sc.bits hbits t .bits64, floatOps_engine_ok]
  cases hs : t.isSigned <;>
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at hfrom ⊢ <;>
    simp only [hfrom, floatOps_liftResult_ok, pure_bind]

/-- **`FloatOps.castIntToFloat` equivalence** across all 12 integer `TyId`s (`10..15` signed
`i8..isize`, `20..25` unsigned `u8..usize`), directly exercising
`annealFloatOpsHooks.integerKindOf` and `annealFloatOpsHooks.formatOf`. -/
theorem floatOps_castIntToFloat_eq (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {srcTy targetTy : Ty} {t : FloatIntTarget} {dst : IeeeFormat}
    (hsrc : floatIntTargetOfTy? srcTy = some t) (hdst : ieeeFormatOfTy? targetTy = some dst)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : sc.sizeBytes * 8 = t.bitWidth .bits64) :
    ∃ msc', ScalarRel
        ⟨evalIntToFloatRoundTiesToEven t.isSigned (t.bitWidth .bits64) sc.bits dst, dst.byteWidth⟩ msc' ∧
      Miri.Interpreter.FloatOps.castIntToFloat (annealFloatOpsHooks nondet chooseNaN) ()
          ⟨.scalar (.fromScalarInt msc), translateTy srcTy layouts⟩
          (translateTy targetTy layouts) =
        pure ⟨.scalar (.fromScalarInt msc'), translateTy targetTy layouts⟩ := by
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
  have hsize : translateSizeBytes (t.bitWidth .bits64 / 8) = translateSizeBytes sc.sizeBytes := by
    rw [hsz8]
  have htoInt := scalar_fromScalarInt_toInt_eq (Prov := AnnealProv) hrel
  have htoBits := scalar_fromScalarInt_toBits_eq (Prov := AnnealProv) hrel
  have hint := intLike_integer_eq hsz8 hrel.canonical
  have hsc_toInt_eq : decodeBitsInt true sc.sizeBytes sc.bits =
      intValueOfBits true (t.bitWidth .bits64) sc.bits := by
    have hb : sc.bits < 2 ^ (8 * sc.sizeBytes) := by
      rw [← scalarModulus_eq_two_pow]; exact hrel.canonical
    have hw8 := floatIntTarget_bitWidth_eq t
    rw [← hsz8] at hw8
    rw [← hw8]
    exact decodeBitsInt_true_eq_intValueOfBits hb
  have hsc_toUInt_eq : Int.ofNat (BitVec.ofNat 128 sc.bits).toNat =
      intValueOfBits false (t.bitWidth .bits64) sc.bits := by
    have hv := validScalarBytes_floatIntTarget t
    rw [← hsz8] at hv
    have hb : sc.bits < 2 ^ (8 * sc.sizeBytes) := by
      rw [← scalarModulus_eq_two_pow]; exact hrel.canonical
    have hw8 := floatIntTarget_bitWidth_eq t
    rw [← hsz8] at hw8
    rw [bitVec_ofNat_toNat_of_valid hv hrel.canonical, ← hw8]
    unfold intValueOfBits
    simp [Nat.mod_eq_of_lt hb]
  unfold Miri.Interpreter.FloatOps.castIntToFloat
  rw [hsrcT]
  simp only [annealFloatOpsHooks_integerKindOf, floatIntTargetKind_signed,
    Miri.Interpreter.Immediate.toScalar, Except.mapError, floatOps_liftResult_ok, pure_bind,
    scalarLayoutData_floatIntTarget_size, hsize, htoInt, Miri.Memory.Scalar.toUInt, htoBits,
    show (translateTy targetTy layouts).ty = floatTyIdOf dst from congrArg (·.ty) hdstT,
    annealFloatOpsHooks_formatOf]
  cases hs : t.isSigned
  · rw [hs] at hfrom
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, hsc_toUInt_eq,
      floatBits_fromInteger_intValueOfBits, floatOps_engine_ok]
    exact floatOps_scalarResult_eq dst hdst layouts _ hfrom
  · rw [hs] at hfrom
    simp only [↓reduceIte, pure_bind, hsc_toInt_eq,
      floatBits_fromInteger_intValueOfBits, floatOps_engine_ok]
    exact floatOps_scalarResult_eq dst hdst layouts _ hfrom

/-- Unlike `Cast.cast .IntToFloat` (which delegates to `Cast.castFromIntLike` and accepts
`.boolean` / `.character`), `FloatOps.castIntToFloat` queries `integerKindOf` directly and
rejects `bool` / `char` sources with `StepError.invalidProgram`, matching Anneal's
`floatIntTargetOfTy? = none`. -/
theorem floatOps_castIntToFloat_bool_char_err (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {srcTy targetTy : Ty} (hsrc : srcTy.kind = .bool ∨ srcTy.kind = .char)
    (imm : Miri.Interpreter.Immediate AnnealProv) (st : AnnealStepState) :
    ∃ msg, Miri.Interpreter.FloatOps.castIntToFloat (annealFloatOpsHooks nondet chooseNaN) ()
        ⟨imm, translateTy srcTy layouts⟩ (translateTy targetTy layouts) st =
      .error (.invalidProgram msg) st := by
  rcases hsrc with hk | hk
  · have hty : (translateTy srcTy layouts).ty = 1 := by unfold translateTy encodeTyId; rw [hk]
    unfold Miri.Interpreter.FloatOps.castIntToFloat
    rw [hty]
    exact ⟨_, rfl⟩
  · have hty : (translateTy srcTy layouts).ty = 2 := by unfold translateTy encodeTyId; rw [hk]
    unfold Miri.Interpreter.FloatOps.castIntToFloat
    rw [hty]
    exact ⟨_, rfl⟩

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

/-- **Statement-targeted conservative extension of `Step.step`**: in any `StateRelLM3_1`
state whose current statement `stmt` is not a float-cast assignment
(`stmtFreeOfFloatCast (translateStmt stmt)`), `annealStepHooksFloat` steps `m` identically
to `annealStepHooks` even when other statements in the same body ARE float casts. -/
theorem step_float_eq_annealStepHooks_at_stmt {body : CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {stmt : MirAst.Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hfree : stmtFreeOfFloatCast (translateStmt stmt)) :
    Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  unfold Miri.Interpreter.Step.step
  rw [stack_currentFrame?_singleton m.stack tf hframes]
  dsimp only [Id.run]
  rw [hfr.location_eq, hfr.body_eq]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map]
  rw [translateBasicBlockData_statements_getElem?, hstmt]
  dsimp only [Option.map]
  rw [evalStatement_float_eq_of_stmtFree hfree]

/-- **Terminator-targeted conservative extension of `Step.step`**: at the end of any basic
block (`get? bb.statements s.frame.stmtIdx = none`), `annealStepHooksFloat` steps every
terminator identically to `annealStepHooks`. -/
theorem step_float_eq_annealStepHooks_at_terminator {body : CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = none) :
    Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  unfold Miri.Interpreter.Step.step
  rw [stack_currentFrame?_singleton m.stack tf hframes]
  dsimp only [Id.run]
  rw [hfr.location_eq, hfr.body_eq]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map]
  rw [translateBasicBlockData_statements_getElem?, hstmt]
  rfl

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

/-- Vendored `Miri.Interpreter.Cast.readPointer` (`private`, `Cast.lean:74-78`). -/
local macro "miriCastReadPointer" : term =>
  `(miri_private% Miri.Interpreter.Cast Miri.Interpreter.Cast.readPointer)

theorem annealCastHooksFloat_typeInfo_eq (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {tyId : Miri.MIR.TyId} (h31 : tyId ≠ 31) (h32 : tyId ≠ 32) :
    (annealCastHooksFloat layouts nondet chooseNaN).typeInfo () tyId =
      (annealCastHooks layouts).typeInfo () tyId := by
  dsimp only [annealCastHooksFloat, annealCastHooks]
  rw [castTypeInfoOfEncodedTyIdFloat_eq_of_ne h31 h32]
  cases castTypeInfoOfEncodedTyId tyId <;> rfl

theorem intLikeValue_floatHooks_eq (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (scalar : Miri.Memory.Scalar AnnealProv) (source : Miri.ABI.TyAndLayout Miri.MIR.TyId)
    (hs31 : source.ty ≠ 31) (hs32 : source.ty ≠ 32) :
    Miri.Interpreter.Cast.intLikeValue (annealCastHooksFloat layouts nondet chooseNaN) ()
        scalar source =
      Miri.Interpreter.Cast.intLikeValue (annealCastHooks layouts) () scalar source := by
  unfold Miri.Interpreter.Cast.intLikeValue
  cases source.layout.backendRepr.isSigned with
  | error _ => rfl
  | ok _ =>
    dsimp only [pure_bind]
    rw [annealCastHooksFloat_typeInfo_eq layouts nondet chooseNaN hs31 hs32]

theorem castFromIntLike_floatHooks_eq (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (scalar : Miri.Memory.Scalar AnnealProv) (source target : Miri.ABI.TyAndLayout Miri.MIR.TyId)
    (hs31 : source.ty ≠ 31) (hs32 : source.ty ≠ 32)
    (ht31 : target.ty ≠ 31) (ht32 : target.ty ≠ 32) :
    Miri.Interpreter.Cast.castFromIntLike (annealCastHooksFloat layouts nondet chooseNaN) ()
        scalar source target =
      Miri.Interpreter.Cast.castFromIntLike (annealCastHooks layouts) () scalar source target := by
  unfold Miri.Interpreter.Cast.castFromIntLike
  rw [intLikeValue_floatHooks_eq layouts nondet chooseNaN scalar source hs31 hs32]
  congr 1
  funext ⟨bits, signed⟩
  rw [annealCastHooksFloat_typeInfo_eq layouts nondet chooseNaN ht31 ht32]

theorem ptrToPtr_floatHooks_eq (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (source : Miri.Interpreter.RvalueImmTy AnnealProv) (target : Miri.ABI.TyAndLayout Miri.MIR.TyId)
    (hs31 : source.layout.ty ≠ 31) (hs32 : source.layout.ty ≠ 32)
    (ht31 : target.ty ≠ 31) (ht32 : target.ty ≠ 32) :
    Miri.Interpreter.Cast.ptrToPtr (annealCastHooksFloat layouts nondet chooseNaN) ()
        source target =
      Miri.Interpreter.Cast.ptrToPtr (annealCastHooks layouts) () source target := by
  unfold Miri.Interpreter.Cast.ptrToPtr
  rw [annealCastHooksFloat_typeInfo_eq layouts nondet chooseNaN hs31 hs32]
  congr 1
  funext sKind
  cases sKind <;>
    (try rfl) <;>
    (dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind];
     rw [annealCastHooksFloat_typeInfo_eq layouts nondet chooseNaN ht31 ht32];
     rfl)

theorem pointerExposeProvenance_floatHooks_eq (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (source : Miri.Interpreter.RvalueImmTy AnnealProv) (target : Miri.ABI.TyAndLayout Miri.MIR.TyId)
    (hs31 : source.layout.ty ≠ 31) (hs32 : source.layout.ty ≠ 32)
    (ht31 : target.ty ≠ 31) (ht32 : target.ty ≠ 32) :
    Miri.Interpreter.Cast.pointerExposeProvenance (annealCastHooksFloat layouts nondet chooseNaN) ()
        source target =
      Miri.Interpreter.Cast.pointerExposeProvenance (annealCastHooks layouts) () source target := by
  unfold Miri.Interpreter.Cast.pointerExposeProvenance
  rw [annealCastHooksFloat_typeInfo_eq layouts nondet chooseNaN hs31 hs32]
  congr 1
  funext sKind
  cases sKind <;> try rfl
  all_goals
    dsimp only [pure_bind]
    rw [annealCastHooksFloat_typeInfo_eq layouts nondet chooseNaN ht31 ht32]
    congr 1
    funext tKind
    cases tKind <;> try rfl
    dsimp only []
    congr 1
    funext sc
    congr 1
    funext ptr
    cases ptr.provenance with
    | none =>
      dsimp only [pure_bind]
      exact castFromIntLike_floatHooks_eq layouts nondet chooseNaN sc source.layout target
        hs31 hs32 ht31 ht32
    | some _ =>
      congr 1

local macro "miriCastInvalid" : term =>
  `(miri_private% Miri.Interpreter.Cast Miri.Interpreter.Cast.invalid)

/-- **Cast-hook conservative extension on `CastKind.IntToInt` / `CastKind.PtrToPtr` /
`CastKind.FnPtrToPtr` / `CastKind.PointerExposeProvenance`**:
for any operand and destination whose encoded `TyId`s are not `f32`/`f64`
(`∉ {31, 32}`), `Miri.Interpreter.Cast.cast` under `annealCastHooksFloat` reduces
identically to `Miri.Interpreter.Cast.cast` under `annealCastHooks`. -/
theorem cast_intToInt_ptrToPtr_floatHooks_eq (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (src : Miri.Interpreter.OpTy AnnealProv) (kind : Miri.MIR.CastKind)
    (hk : kind = .IntToInt ∨ kind = .PtrToPtr ∨ kind = .FnPtrToPtr ∨ kind = .PointerExposeProvenance)
    (castTy : Miri.MIR.TyId) (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (hsrc_lay : ∀ st v st', annealReadImmediate src st = .ok v st' → v.layout = src.layout)
    (hdest_ty : dest.layout.ty = castTy)
    (hs31 : src.layout.ty ≠ 31) (hs32 : src.layout.ty ≠ 32)
    (ht31 : castTy ≠ 31) (ht32 : castTy ≠ 32) :
    Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
        src kind castTy dest =
      Miri.Interpreter.Cast.cast (annealCastHooks layouts) () 16 src kind castTy dest := by
  have htype_s := annealCastHooksFloat_typeInfo_eq layouts nondet chooseNaN hs31 hs32
  have hdl1 : (annealCastHooksFloat layouts nondet chooseNaN).destLayout dest = dest.layout := rfl
  have hdl2 : (annealCastHooks layouts).destLayout dest = dest.layout := rfl
  have hev1 : ∀ l, (annealCastHooksFloat layouts nondet chooseNaN).enforceValidity () l = pure true :=
    fun _ => rfl
  have hev2 : ∀ l, (annealCastHooks layouts).enforceValidity () l = pure true := fun _ => rfl
  have hri1 : (annealCastHooksFloat layouts nondet chooseNaN).readImmediate () = annealReadImmediate := rfl
  have hri2 : (annealCastHooks layouts).readImmediate () = annealReadImmediate := rfl
  have hwi1 : (annealCastHooksFloat layouts nondet chooseNaN).writeImmediate () = annealWriteImmediate := rfl
  have hwi2 : (annealCastHooks layouts).writeImmediate () = annealWriteImmediate := rfl
  have hdp : (annealCastHooksFloat layouts nondet chooseNaN).derefPointer () =
      (annealCastHooks layouts).derefPointer () := rfl
  have hcfp : (annealCastHooksFloat layouts nondet chooseNaN).checkFunctionPointer () =
      (annealCastHooks layouts).checkFunctionPointer () := rfl
  have hrp : miriCastReadPointer (annealCastHooksFloat layouts nondet chooseNaN) () =
      miriCastReadPointer (annealCastHooks layouts) () := rfl
  have hread_eq : ∀ (f₁ f₂ : Miri.Interpreter.RvalueImmTy AnnealProv →
      Miri.Interpreter.RvalueM AnnealStepState Unit),
      (∀ v, v.layout = src.layout → f₁ v = f₂ v) →
      (annealReadImmediate src >>= f₁) = (annealReadImmediate src >>= f₂) := by
    intro f₁ f₂ hf
    funext st
    cases hr : annealReadImmediate src st with
    | error e st' => rw [EStateM.bind_eq_error hr, EStateM.bind_eq_error hr]
    | ok v st' =>
      rw [EStateM.bind_eq_ok hr, EStateM.bind_eq_ok hr, hf v (hsrc_lay st v st' hr)]
  unfold Miri.Interpreter.Cast.cast
  rcases hk with rfl | rfl | rfl | rfl
  · have hcont :
        (do
          let value ← annealReadImmediate src
          let sourceKind ← (annealCastHooksFloat layouts nondet chooseNaN).typeInfo () value.layout.ty
          match sourceKind with
          | .integer _ | .boolean | .character => pure ()
          | _ => miriCastInvalid "IntToInt/IntToFloat source type is not integer-like"
          match ← (annealCastHooksFloat layouts nondet chooseNaN).typeInfo () castTy with
          | .integer _ | .floating _ | .character => pure ()
          | _ => miriCastInvalid "IntToInt/IntToFloat destination type is not integer/float/char"
          let result ← Miri.Interpreter.Cast.castFromIntLike
            (annealCastHooksFloat layouts nondet chooseNaN) () (← miriCastScalarOf value) value.layout dest.layout
          annealWriteImmediate result.imm dest) =
        (do
          let value ← annealReadImmediate src
          let sourceKind ← (annealCastHooks layouts).typeInfo () value.layout.ty
          match sourceKind with
          | .integer _ | .boolean | .character => pure ()
          | _ => miriCastInvalid "IntToInt/IntToFloat source type is not integer-like"
          match ← (annealCastHooks layouts).typeInfo () castTy with
          | .integer _ | .floating _ | .character => pure ()
          | _ => miriCastInvalid "IntToInt/IntToFloat destination type is not integer/float/char"
          let result ← Miri.Interpreter.Cast.castFromIntLike
            (annealCastHooks layouts) () (← miriCastScalarOf value) value.layout dest.layout
          annealWriteImmediate result.imm dest) := by
      apply hread_eq; intro v hv
      rw [annealCastHooksFloat_typeInfo_eq layouts nondet chooseNaN (hv ▸ hs31) (hv ▸ hs32),
        annealCastHooksFloat_typeInfo_eq layouts nondet chooseNaN ht31 ht32]
      congr 1; funext sKind; cases sKind <;> try rfl
      all_goals
        dsimp only [pure_bind]
        congr 1; funext tKind; cases tKind <;> try rfl
        all_goals
          dsimp only []
          congr 1; funext sc
          rw [castFromIntLike_floatHooks_eq layouts nondet chooseNaN sc v.layout dest.layout
            (hv ▸ hs31) (hv ▸ hs32) (hdest_ty ▸ ht31) (hdest_ty ▸ ht32)]
    simp only at hcont
    simp only [hdl1, hdl2, hdest_ty, beq_self_eq_true, ↓reduceIte, pure_bind, Bool.false_eq_true,
      hev1, hev2, htype_s, hri1, hri2, hwi1, hwi2, hdp, hcfp, hrp]
    congr 1; funext sInfo
    cases sInfo with
    | rawPointer _ =>
      cases src.layout.layout.backendRepr with
      | ScalarPair =>
        simp only [↓reduceIte]; exact congrArg _ (funext fun _ => hcont)
      | Scalar _ | SimdScalableVector | SimdVector | Memory =>
        simp only [Bool.false_eq_true, ↓reduceIte]; exact hcont
    | fnPointer =>
      dsimp only [pure_bind]
      exact congrArg _ (funext fun _ => congrArg _ (funext fun _ => hcont))
    | closure _ _ upvars =>
      dsimp only [pure_bind]
      cases (upvars != 0)
      · exact hcont
      · funext st; rfl
    | integer _ | floating _ | boolean | character | fnDefinition _ _ =>
      dsimp only [pure_bind]; exact hcont
    | reference _ | adt _ | pattern _ _ | dynamic _ | slice _ | array _ _ =>
      funext st; rfl
  · have hcont :
        (annealReadImmediate src >>= fun value => do
          let result ← Miri.Interpreter.Cast.ptrToPtr
            (annealCastHooksFloat layouts nondet chooseNaN) () value dest.layout
          annealWriteImmediate result.imm dest) =
        (annealReadImmediate src >>= fun value => do
          let result ← Miri.Interpreter.Cast.ptrToPtr
            (annealCastHooks layouts) () value dest.layout
          annealWriteImmediate result.imm dest) := by
      apply hread_eq; intro v hv
      rw [ptrToPtr_floatHooks_eq layouts nondet chooseNaN v dest.layout
        (hv ▸ hs31) (hv ▸ hs32) (hdest_ty ▸ ht31) (hdest_ty ▸ ht32)]
    simp only [hdl1, hdl2, hdest_ty, beq_self_eq_true, ↓reduceIte, pure_bind, Bool.false_eq_true,
      hev1, hev2, htype_s, hri1, hri2, hwi1, hwi2, hdp, hcfp, hrp, hcont]
  · have hcont :
        (annealReadImmediate src >>= fun value => do
          let result ← Miri.Interpreter.Cast.ptrToPtr
            (annealCastHooksFloat layouts nondet chooseNaN) () value dest.layout
          annealWriteImmediate result.imm dest) =
        (annealReadImmediate src >>= fun value => do
          let result ← Miri.Interpreter.Cast.ptrToPtr
            (annealCastHooks layouts) () value dest.layout
          annealWriteImmediate result.imm dest) := by
      apply hread_eq; intro v hv
      rw [ptrToPtr_floatHooks_eq layouts nondet chooseNaN v dest.layout
        (hv ▸ hs31) (hv ▸ hs32) (hdest_ty ▸ ht31) (hdest_ty ▸ ht32)]
    simp only [hdl1, hdl2, hdest_ty, beq_self_eq_true, ↓reduceIte, pure_bind, Bool.false_eq_true,
      hev1, hev2, htype_s, hri1, hri2, hwi1, hwi2, hdp, hcfp, hrp, hcont]
  · have hcont :
        (annealReadImmediate src >>= fun value => do
          let result ← Miri.Interpreter.Cast.pointerExposeProvenance
            (annealCastHooksFloat layouts nondet chooseNaN) () value dest.layout
          annealWriteImmediate result.imm dest) =
        (annealReadImmediate src >>= fun value => do
          let result ← Miri.Interpreter.Cast.pointerExposeProvenance
            (annealCastHooks layouts) () value dest.layout
          annealWriteImmediate result.imm dest) := by
      apply hread_eq; intro v hv
      rw [pointerExposeProvenance_floatHooks_eq layouts nondet chooseNaN v dest.layout
        (hv ▸ hs31) (hv ▸ hs32) (hdest_ty ▸ ht31) (hdest_ty ▸ ht32)]
    simp only [hdl1, hdl2, hdest_ty, beq_self_eq_true, ↓reduceIte, pure_bind, Bool.false_eq_true,
      hev1, hev2, htype_s, hri1, hri2, hwi1, hwi2, hdp, hcfp, hrp, hcont]

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

/-- **`Cast.cast .FloatToFloat` under any valid `chooseNaN` selector**: for either `nondet : Bool`
mode and **any** state-preserving valid index selector `chooseNaN` (`nondet = true → ∀ cs,
4 ≤ cs.length → ∃ idx < cs.length, chooseNaN () cs st = .ok idx st`; vacuous in deterministic
mode, and satisfied by every constant selector `pure i`, `i < 4`), `Cast.cast .FloatToFloat`
succeeds on every `f32` / `f64` bit pattern:
* when `isNaNBits src sc.bits = false`, it writes the bit-exact trusted conversion
  `evalFloatToFloatRoundTiesToEven src dst sc.bits`;
* when `isNaNBits src sc.bits = true`, it writes an in-width `dst` NaN (`outBits < 2 ^ dst.width`,
  `isNaNBits dst outBits = true`), equal to `preferredNaNBits dst` when `nondet = false`. -/
theorem cast_floatToFloat_any_chooseNaN_spec (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {srcTy targetTy : Ty} {src dst : IeeeFormat}
    (hsrc : ieeeFormatOfTy? srcTy = some src) (hdst : ieeeFormatOfTy? targetTy = some dst)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : sc.sizeBytes = src.byteWidth) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv)
    (st : AnnealStepState)
    (hchoose : nondet = true → ∀ cs : List Miri.Interpreter.FloatBits,
      4 ≤ cs.length → ∃ idx < cs.length, chooseNaN () cs st = .ok idx st) :
    ∃ outBits < 2 ^ dst.width, ∃ msc',
      ScalarRel ⟨outBits, dst.byteWidth⟩ msc' ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = false →
        outBits = evalFloatToFloatRoundTiesToEven src dst sc.bits) ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = true →
        Anneal.Mir.IeeeFloatCast.isNaNBits dst outBits = true ∧
          (nondet = false → outBits = preferredNaNBits dst)) ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩ .FloatToFloat
          (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ st =
        annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨destRef, translateTy targetTy layouts⟩ st := by
  have hbits : sc.bits < 2 ^ src.width := by
    have := hrel.canonical; rwa [hsz, scalarModulus_byteWidth] at this
  obtain ⟨outBits, hout_lt, hadj, hnot_nan, h_nan⟩ :=
    floatOps_adjustNaN_any_chooseNaN (annealFloatOpsHooks nondet chooseNaN) ()
      src dst sc.bits hbits st hchoose
  obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec
    (validScalarBytes_byteWidth dst) (caseVal := outBits)
    (by rw [scalarModulus_byteWidth]; exact hout_lt)
  rw [translateSizeBytes_byteWidth] at hfrom
  refine ⟨outBits, hout_lt, msc', hrel', hnot_nan, h_nan, ?_⟩
  have hsrcT := translateTy_of_ieeeFormatOfTy? hsrc layouts
  have hdstT := translateTy_of_ieeeFormatOfTy? hdst layouts
  have henc : encodeTyId targetTy = floatTyIdOf dst := congrArg (·.ty) hdstT
  have hcast_fn :
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩ .FloatToFloat
          (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ =
        (Miri.Interpreter.FloatOps.adjustNaN (annealFloatOpsHooks nondet chooseNaN) ()
          ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst sc.bits)⟩
          [⟨ieeeFormatToMiri src, BitVec.ofNat 128 sc.bits⟩] >>= fun converted =>
          miriCastLiftResult
            (Miri.Memory.Scalar.fromUInt converted.bits (ieeeFormatToMiri dst).size |>.mapError
              Miri.Interpreter.ScalarOps.scalarError) >>= fun scalar =>
            annealWriteImmediate (.scalar scalar) ⟨destRef, translateTy targetTy layouts⟩) := by
    rw [hsrcT, hdstT, henc]
    unfold Miri.Interpreter.Cast.cast
    simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
      castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true,
      annealReadImmediate_scalar, floatOps_readBits_annealFloat nondet chooseNaN src hrel hsz,
      floatBits_convert_eq src dst sc.bits hbits, Except.mapError, cast_liftResult_ok,
      floatLayoutData_size, bne_self_eq_false]
  rw [congrFun hcast_fn st, EStateM.bind_eq_ok hadj]
  simp only [hfrom, Except.mapError, cast_liftResult_ok, pure_bind]

/-- **`Cast.cast .FloatToFloat` under a constant selector `pure i` (`i < 4`)**: writes the
**exact** `ScalarRel`-related `floatToFloatPureIndexBits src dst sc.bits i`. -/
theorem cast_floatToFloat_pure_index_eq (layouts : LayoutTable)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (i : Nat) (hi : i < 4) (hsel : ∀ cs st, chooseNaN () cs st = .ok i st)
    {srcTy targetTy : Ty} {src dst : IeeeFormat}
    (hsrc : ieeeFormatOfTy? srcTy = some src) (hdst : ieeeFormatOfTy? targetTy = some dst)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : sc.sizeBytes = src.byteWidth) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    ∃ msc', ScalarRel ⟨floatToFloatPureIndexBits src dst sc.bits i, dst.byteWidth⟩ msc' ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts true chooseNaN) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩ .FloatToFloat
          (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨destRef, translateTy targetTy layouts⟩ := by
  have hbits : sc.bits < 2 ^ src.width := by
    have := hrel.canonical; rwa [hsz, scalarModulus_byteWidth] at this
  have hout_lt := floatToFloatPureIndexBits_lt src dst sc.bits i
  obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec
    (validScalarBytes_byteWidth dst) (caseVal := floatToFloatPureIndexBits src dst sc.bits i)
    (by rw [scalarModulus_byteWidth]; exact hout_lt)
  rw [translateSizeBytes_byteWidth] at hfrom
  refine ⟨msc', hrel', ?_⟩
  funext st
  have hadj := floatOps_adjustNaN_pure_index_all (annealFloatOpsHooks true chooseNaN) () rfl i hi
    hsel src dst sc.bits hbits st
  have hsrcT := translateTy_of_ieeeFormatOfTy? hsrc layouts
  have hdstT := translateTy_of_ieeeFormatOfTy? hdst layouts
  have henc : encodeTyId targetTy = floatTyIdOf dst := congrArg (·.ty) hdstT
  have hcast_fn :
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts true chooseNaN) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩ .FloatToFloat
          (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ =
        (Miri.Interpreter.FloatOps.adjustNaN (annealFloatOpsHooks true chooseNaN) ()
          ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst sc.bits)⟩
          [⟨ieeeFormatToMiri src, BitVec.ofNat 128 sc.bits⟩] >>= fun converted =>
          miriCastLiftResult
            (Miri.Memory.Scalar.fromUInt converted.bits (ieeeFormatToMiri dst).size |>.mapError
              Miri.Interpreter.ScalarOps.scalarError) >>= fun scalar =>
            annealWriteImmediate (.scalar scalar) ⟨destRef, translateTy targetTy layouts⟩) := by
    rw [hsrcT, hdstT, henc]
    unfold Miri.Interpreter.Cast.cast
    simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
      castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true,
      annealReadImmediate_scalar, floatOps_readBits_annealFloat true chooseNaN src hrel hsz,
      floatBits_convert_eq src dst sc.bits hbits, Except.mapError, cast_liftResult_ok,
      floatLayoutData_size, bne_self_eq_false]
  rw [congrFun hcast_fn st, EStateM.bind_eq_ok hadj]
  simp only [hfrom, Except.mapError, cast_liftResult_ok, pure_bind]

/-- **`Cast.cast .FloatToFloat` fails under an out-of-range constant selector**: on a NaN input
whose nondeterministic `nanChoices` list has length `≤ i`, `Cast.cast` throws
`.invalidProgram "invalid floating NaN choice index"` (`floatOps_adjustNaN_pure_out_of_range`). -/
theorem cast_floatToFloat_pure_out_of_range (layouts : LayoutTable)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (i : Nat) (hsel : ∀ cs st, chooseNaN () cs st = .ok i st)
    {srcTy targetTy : Ty} {src dst : IeeeFormat}
    (hsrc : ieeeFormatOfTy? srcTy = some src) (hdst : ieeeFormatOfTy? targetTy = some dst)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : sc.sizeBytes = src.byteWidth) {neg q : Bool} {payload : Nat}
    (hnan : decodeBits src sc.bits = .nan neg q payload)
    {cs : List Miri.Interpreter.FloatBits}
    (hcs : Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
      [⟨ieeeFormatToMiri src, BitVec.ofNat 128 sc.bits⟩] true = .ok cs)
    (hi : cs.length ≤ i) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv)
    (st : AnnealStepState) :
    Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts true chooseNaN) () 16
        ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩ .FloatToFloat
        (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ st =
      .error (.invalidProgram "invalid floating NaN choice index") st := by
  have hbits : sc.bits < 2 ^ src.width := by
    have := hrel.canonical; rwa [hsz, scalarModulus_byteWidth] at this
  have hadj := floatOps_adjustNaN_pure_out_of_range (annealFloatOpsHooks true chooseNaN) () rfl i
    hsel src dst sc.bits neg q payload hnan hcs hi st
  have hsrcT := translateTy_of_ieeeFormatOfTy? hsrc layouts
  have hdstT := translateTy_of_ieeeFormatOfTy? hdst layouts
  have henc : encodeTyId targetTy = floatTyIdOf dst := congrArg (·.ty) hdstT
  have hcast_fn :
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts true chooseNaN) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩ .FloatToFloat
          (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ =
        (Miri.Interpreter.FloatOps.adjustNaN (annealFloatOpsHooks true chooseNaN) ()
          ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalFloatToFloatRoundTiesToEven src dst sc.bits)⟩
          [⟨ieeeFormatToMiri src, BitVec.ofNat 128 sc.bits⟩] >>= fun converted =>
          miriCastLiftResult
            (Miri.Memory.Scalar.fromUInt converted.bits (ieeeFormatToMiri dst).size |>.mapError
              Miri.Interpreter.ScalarOps.scalarError) >>= fun scalar =>
            annealWriteImmediate (.scalar scalar) ⟨destRef, translateTy targetTy layouts⟩) := by
    rw [hsrcT, hdstT, henc]
    unfold Miri.Interpreter.Cast.cast
    simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
      castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true,
      annealReadImmediate_scalar, floatOps_readBits_annealFloat true chooseNaN src hrel hsz,
      floatBits_convert_eq src dst sc.bits hbits, Except.mapError, cast_liftResult_ok,
      floatLayoutData_size, bne_self_eq_false]
  rw [congrFun hcast_fn st, EStateM.bind_eq_error hadj]

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

theorem IsFloatCastScalarTy.of_kind_eq {ty₁ ty₂ : Ty} (h : IsFloatCastScalarTy ty₂)
    (hk : ty₁.kind = ty₂.kind) : IsFloatCastScalarTy ty₁ := by
  rcases h with ⟨f, hf⟩ | ⟨t, ht⟩
  · exact Or.inl ⟨f, by unfold ieeeFormatOfTy? at hf ⊢; rw [hk]; exact hf⟩
  · exact Or.inr ⟨t, by unfold floatIntTargetOfTy? at ht ⊢; rw [hk]; exact ht⟩

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

end LeanMiriSpec.Correspondence
