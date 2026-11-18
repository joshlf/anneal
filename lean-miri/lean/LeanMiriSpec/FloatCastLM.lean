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
adjustNaN, castFloatToFloat, castFloatToInt, castIntToFloat}`,
`Miri.Interpreter.Cast.{cast, castFromIntLike}`, `Miri.Interpreter.Step.step`) for Rust
`as` casts `CastKind.floatToInt`, `CastKind.intToFloat`, and `CastKind.floatToFloat` on
`f32` / `f64` and all 12 integer widths (`i8`..`i128`, `isize`, `u8`..`u128`, `usize`).
No shadow evaluator is defined: every headline theorem relates the trusted definitions
directly to the vendored ones.

1. **Private-helper bridges** (`miri_private%`, `miri_powScale_eq`,
   `miri_ratioExponent_eq`, `miri_roundQuotientEven_eq`, `miri_encode_eq`): the vendored
   `private` helpers of `Float.lean` are identified with the trusted primitives through
   the `Classical.choice`-free formulations of `Anneal.Mir.IeeeFloatCast`
   (`ratioExponent_eq_miri`, `powScale_eq_miri`, `roundQuotientTiesToEven_eq_miri`,
   `ratioExponent_eq_iff_powScale_bounds`, and `BitVec` / round-trip bridges).
2. **Formats and decoding**: `ieeeFormatToMiri` / `miriFormatToIeee?` (matching width,
   exponent/fraction bits, bias, exponent range, size); `floatBits_decode_eq` (exact
   agreement on every `bits < 2 ^ width`) and `floatBits_decode_error`
   (`.encodingExceedsWidth` beyond the width).
3. **Rounding and primitive casts**: `floatBits_roundRatio_eq` (Miri never throws for
   `d ≠ 0`; the two `inconsistentRounding` throws are unreachable),
   `floatBits_fromInteger_eq`, `floatBits_toInteger_eq` (every integer target),
   `floatBits_convert_eq` (every bit pattern, including signaling and payload NaNs).
4. **NaN choices, 4-vs-6 sNaN rule, and arbitrary `chooseNaN` soundness**:
   `floatBits_nanChoices_deterministic` (`[preferredNaN]`), `floatBits_nanChoices_nondet_eq`
   (`preferredNaN` at index `0` and the `convert` result at index `2`),
   `floatBits_preferredNaN_mem_nanChoices` and `floatBits_convert_mem_nanChoices_nondet`
   (`∈` membership), `floatBits_nanChoices_nondet_exact` and
   `floatBits_nanChoices_nondet_list_eq` (exact 4-element vs 6-element candidate list
   pinning all even and odd sign-negated entries), `floatBits_mem_nanChoices_isNaN`
   (every candidate in either mode is a valid `dst` NaN),
   `floatOps_adjustNaN_convert_refine`, `floatOps_adjustNaN_deterministic`,
   `floatOps_adjustNaN_any_chooseNaN` (any valid selector: `nondet = true →` in-bounds index on
   every list of length `≥ 4`, satisfied by every `pure i`, `i < 4`: `chooseNaN_pure_valid`,
   `annealChooseQuietedNaN_valid`), `floatOps_adjustNaN_pure_index` /
   `floatOps_adjustNaN_pure_index_all` (`floatToFloatPureIndexBits` across all inputs for `i < 4`
   and all 6 signaling-NaN candidates for `i < 6`; `floatToFloatPureIndexBits_spec` and
   `floatToFloatPureIndexBits_snan_spec` pin it to the trusted conversion on non-NaN inputs and to
   the `i`-th entry of `lean-miri`'s own `nanChoices` list on quiet and signaling NaN inputs, so it
   is no independent semantics), and `floatOps_adjustNaN_pure_snan_index` (`i < 6` sNaN candidates
   `4, 5`).
5. **Conservative hook overlay** (following `WideSliceDstLM`, leaving `Translate.lean`
   untouched): `castTypeInfoOfEncodedTyIdFloat` (`31 ↦ binary32`, `32 ↦ binary64`,
   `30` / `33` keep failing closed), `annealFloatOpsHooks` (`annealFloatOpsHooks_integerKindOf`),
   `annealCastHooksFloat`, `annealRvalueHooksFloat`, `annealStepHooksFloat`, body-level and
   per-step conservative extension (`step_float_eq_annealStepHooks_of_bodyFree`,
   `step_float_eq_annealStepHooks_at_stmt`, `step_float_eq_annealStepHooks_at_terminator`),
   and `Cast.cast` conservative extension (`cast_intToInt_ptrToPtr_floatHooks_eq`).
6. **`FloatOps` and `Cast.cast` simulation**: `floatOps_castFloatToFloat_refine_eq`,
   `floatOps_castFloatToFloat_deterministic_eq`, `floatOps_castFloatToInt_eq`,
   `floatOps_castIntToFloat_eq`, `floatOps_castIntToFloat_bool_char_err` (exercising
   `h.integerKindOf`), and `cast_floatToFloat_eq`, `cast_floatToFloat_any_chooseNaN_spec`,
   `cast_floatToFloat_pure_index_eq`, `cast_floatToInt_eq`, `cast_intToFloat_eq`,
   `cast_floatCast_uninit`, unified as `floatCast_result_spec_mode`; an out-of-range constant
   selector makes `Cast.cast` throw `.invalidProgram` (`cast_floatToFloat_pure_out_of_range`,
   via `floatOps_adjustNaN_pure_out_of_range` and `floatBits_nanChoices_quiet_length`).
7. **Real-step simulation over immediate, promoted (`allocMap`), and indirect locals**
   (`StateRelLM3_1` / `StepRelLM3_1`):
   - Immediate-local simulation: `step_cast_float_{copy,move,constant}_simulation{_mode}`;
   - Promoted (`allocMap`) & immediate-local simulation with `updateAllocMapOnWrite`
     Tree Borrows invalidation: `step_cast_float_{copy,move,constant}_anyLocal_simulation{_mode}`
     plus `FloatStepPreservesImm` multi-step chaining lemmas
     `step_cast_float_{copy,move,constant}_anyLocal_preserves` (with
     `StateRelLM3_1.not_mem_allocMap_of_ieeeFormatOfTy?` proving `f32`/`f64` locals are
     never promoted into `allocMap`);
   - Stack-allocated `LocalRel.indirect` float source reads/moves AND unpromoted indirect
     destination writes (`f32`/`f64` and integer targets):
     `annealReadMemoryPlace_floatCastScalar_zero_offset_eq`,
     `annealWriteMemoryPlace_floatCastScalar_zero_offset_ok`,
     `StateRelLM3_1.advance_write_unpromoted_indirect_scalar`,
     `step_cast_float_{copy,move}_indirect_float_simulation{_mode}`,
     `step_cast_float_{copy,move,constant}_indirect_dst_simulation{_mode}`, and the
     `hnot_dst`-free float-destination specializations
     `step_cast_float_{copy,move,constant}_indirect_floatDst_simulation{_mode}`;
   - Full NaN-choice refinement and exact constant-index step simulation:
     `step_cast_floatToFloat_{constant,copy,move}_nanChoice_simulation` (either NaN mode, any
     valid selector) and `step_cast_floatToFloat_{copy,constant,move}_pure_index_simulation`
     (exact `floatToFloatPureIndexBits` in `_d` for any `pure i`, `i < 4`; value-split finisher
     `finish_write_immediate_split_hooks`);
   - Deterministic-mode (`floatNondeterministic := false`) step-level NaN canonicalization:
     `step_cast_floatToFloat_{constant,copy,move}_deterministic_spec` and the full
     simulations modulo NaN canonicalization
     `step_cast_floatToFloat_{constant,copy,move}_deterministic_simulation` (corollaries of the
     NaN-choice simulations);
   - Tightness of the side conditions:
     `step_cast_floatToFloat_{copy,move,constant}_deterministic_lockstep_iff` (deterministic
     lockstep holds **iff** the input is not a NaN or its quieted conversion already is
     `preferredNaNBits`, so `FloatCastDetAgrees` is necessary) and
     `step_cast_floatToFloat_constant_pure_out_of_range` (an out-of-range selector makes
     `lean-miri` fail with `.invalidProgram` while Anneal steps, so the selector-validity premise
     is necessary).
8. **Boundaries and end-to-end multi-step witnesses**: two-sided `bool` / `char`
   (`evalFloatCast_intToFloat_bool_char_none` vs `cast_intToFloat_{bool,char}_miri_ok`) and
   `f16` / `f128` (`evalFloatCast_f16_f128_none`, `cast_f16_f128_unsupported`,
   `step_cast_f16_f128_source_fail_closed`, `step_cast_f16_f128_target_copy_fail_closed`,
   `step_cast_f16_f128_constant_fail_closed`, the sharp `.copy` source-vs-target uninitialized
   contrast `step_cast_f16_f128_uninit_source_divergence` vs
   `step_cast_f16_f128_uninit_target_ub_lockstep`, and the full `.move` source/target
   trichotomy & dichotomy `step_cast_f16_f128_move_source_boundary` /
   `step_cast_f16_f128_move_target_boundary`) characterizations; concrete
   subnormal/tie/overflow, `isize`/`usize`, and 4-vs-6 sNaN witnesses; and three end-to-end
   `Step.step`/`stepMirFn` witnesses (`floatWit_copy_move_isize_and_ub`,
   `floatWit_promoted_allocMap_pipeline`, `div_floatToFloat_deterministic_payloadNaN_step`), plus
   `div_floatToFloat_deterministic_payloadNaN_exact`, `floatWit_nanChoice_pure1_step`, and
   `floatWit_nanChoice_pure1_exact` (pinning `0xFFF8_0000_0000_0000` under `pure 1`); and
   memory-backed-local non-vacuity witnesses built from hand-constructed `StateRelLM3_1` states
   with a force-allocated (`LocalRel.indirect`, unpromoted) `f64` local at `AllocId 1`:
   `floatWit_indirect_dst_step` (`_0 = const 7_i32 as f64` written into memory) and
   `floatWit_indirect_src_step` (`_0 = copy _1 as f32` read from memory holding `2.5_f64`); and
   `floatWit_nanChoice_pure4_out_of_range` (selector `pure 4` on a quiet NaN: `lean-miri` fails,
   Anneal steps, no `StepRelLM3_1`).

Every public theorem of this file carries a `#guard_msgs (whitespace := lax) in #print axioms`
guard (standard axioms only: `propext`, `Classical.choice`, `Quot.sound`).
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

/-- **`OpTy`-generic error propagation in `Cast.cast`** (both `.immediate` and `.indirect`
operands): for any modeled float cast (`FloatCastSig`), if `annealReadImmediate` on the
source operand fails with `err` (e.g. `.immediate .uninit` or `.indirect mp` reading
uninitialized / dead / OOB / misaligned memory), `Cast.cast` fails with the exact same
error and state. -/
theorem cast_floatCast_of_readImmediate_err (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {kind : CastKind} {srcTy castTy : Ty} (hsig : FloatCastSig kind srcTy castTy)
    (srcOperand : Miri.Interpreter.Operand AnnealProv)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv)
    {st st' : AnnealStepState} {err : Miri.Interpreter.StepError}
    (herr : annealReadImmediate ⟨srcOperand, translateTy srcTy layouts⟩ st = .error err st') :
    Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
        ⟨srcOperand, translateTy srcTy layouts⟩ (translateCastKind kind) (encodeTyId castTy)
        ⟨destRef, translateTy castTy layouts⟩ st =
      .error err st' := by
  cases hsig with
  | @floatToFloat _ _ src dst hs hd =>
    rw [translateTy_of_ieeeFormatOfTy? hs layouts] at herr ⊢
    rw [translateTy_of_ieeeFormatOfTy? hd layouts,
      show encodeTyId castTy = floatTyIdOf dst from
        congrArg (·.ty) (translateTy_of_ieeeFormatOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
    simp only [beq_self_eq_true, ↓reduceIte, castTypeInfoOfEncodedTyIdFloat_floatTyIdOf,
      pure_bind, Bool.false_eq_true]
    exact EStateM.bind_eq_error herr
  | @floatToInt _ _ src t hs hd =>
    rw [translateTy_of_ieeeFormatOfTy? hs layouts] at herr ⊢
    rw [translateTy_of_floatIntTargetOfTy? hd layouts,
      show encodeTyId castTy = floatIntTargetTyId t from
        congrArg (·.ty) (translateTy_of_floatIntTargetOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
    simp only [beq_self_eq_true, ↓reduceIte, castTypeInfoOfEncodedTyIdFloat_floatTyIdOf,
      pure_bind, Bool.false_eq_true]
    exact EStateM.bind_eq_error herr
  | @intToFloat _ _ t dst hs hd =>
    rw [translateTy_of_floatIntTargetOfTy? hs layouts] at herr ⊢
    rw [translateTy_of_ieeeFormatOfTy? hd layouts,
      show encodeTyId castTy = floatTyIdOf dst from
        congrArg (·.ty) (translateTy_of_ieeeFormatOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
    simp only [beq_self_eq_true, ↓reduceIte, castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId,
      pure_bind, Bool.false_eq_true]
    exact EStateM.bind_eq_error herr

/-- **`OpTy`-generic scalar reduction in `Cast.cast`** (both `.immediate` and `.indirect`
operands): whenever `annealReadImmediate` reads `⟨.scalar s, translateTy srcTy layouts⟩`
from `srcOperand` (such as a memory-backed `LocalRel.indirect` / promoted `allocMap` local
or a dereferenced `*ptr` place), `Cast.cast` reduces identically to `Cast.cast` on
`⟨.immediate (.scalar s), translateTy srcTy layouts⟩`. -/
theorem cast_floatCast_of_readImmediate_scalar (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {kind : CastKind} {srcTy castTy : Ty} (hsig : FloatCastSig kind srcTy castTy)
    (srcOperand : Miri.Interpreter.Operand AnnealProv)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv)
    {st st' : AnnealStepState} (s : Miri.Memory.Scalar AnnealProv)
    (hok : annealReadImmediate ⟨srcOperand, translateTy srcTy layouts⟩ st =
      .ok ⟨.scalar s, translateTy srcTy layouts⟩ st') :
    Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
        ⟨srcOperand, translateTy srcTy layouts⟩ (translateCastKind kind) (encodeTyId castTy)
        ⟨destRef, translateTy castTy layouts⟩ st =
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
        ⟨.immediate (.scalar s), translateTy srcTy layouts⟩ (translateCastKind kind)
        (encodeTyId castTy) ⟨destRef, translateTy castTy layouts⟩ st' := by
  cases hsig with
  | @floatToFloat _ _ src dst hs hd =>
    rw [translateTy_of_ieeeFormatOfTy? hs layouts] at hok ⊢
    rw [translateTy_of_ieeeFormatOfTy? hd layouts,
      show encodeTyId castTy = floatTyIdOf dst from
        congrArg (·.ty) (translateTy_of_ieeeFormatOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
    simp only [beq_self_eq_true, ↓reduceIte, castTypeInfoOfEncodedTyIdFloat_floatTyIdOf,
      pure_bind, Bool.false_eq_true]
    rw [EStateM.bind_eq_ok hok]
    rfl
  | @floatToInt _ _ src t hs hd =>
    rw [translateTy_of_ieeeFormatOfTy? hs layouts] at hok ⊢
    rw [translateTy_of_floatIntTargetOfTy? hd layouts,
      show encodeTyId castTy = floatIntTargetTyId t from
        congrArg (·.ty) (translateTy_of_floatIntTargetOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
    simp only [beq_self_eq_true, ↓reduceIte, castTypeInfoOfEncodedTyIdFloat_floatTyIdOf,
      pure_bind, Bool.false_eq_true]
    rw [EStateM.bind_eq_ok hok]
    rfl
  | @intToFloat _ _ t dst hs hd =>
    rw [translateTy_of_floatIntTargetOfTy? hs layouts] at hok ⊢
    rw [translateTy_of_ieeeFormatOfTy? hd layouts,
      show encodeTyId castTy = floatTyIdOf dst from
        congrArg (·.ty) (translateTy_of_ieeeFormatOfTy? hd layouts)]
    unfold Miri.Interpreter.Cast.cast
    dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
    simp only [beq_self_eq_true, ↓reduceIte, castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId,
      pure_bind, Bool.false_eq_true]
    rw [EStateM.bind_eq_ok hok]
    rfl

/-- `annealReadImmediate` on an `.indirect` memory place of any float-cast scalar type
(`f32`, `f64`, or `i8..isize` / `u8..usize`) delegates directly to `annealReadMemoryPlace`. -/
theorem annealReadImmediate_indirect_floatCastScalar_eq {ty : Ty} {ly : LayoutTable}
    (hty : IsFloatCastScalarTy ty) (mp : Miri.Interpreter.MemPlace AnnealProv) :
    annealReadImmediate ⟨.indirect mp, translateTy ty ly⟩ =
      annealReadMemoryPlace mp (translateTy ty ly) := by
  have hf : (translateTy ty ly).layout.fields = .Primitive := by
    rcases hty with ⟨f, hf⟩ | ⟨t, ht⟩
    · rw [translateTy_of_ieeeFormatOfTy? hf ly]; cases f <;> rfl
    · rw [translateTy_of_floatIntTargetOfTy? ht ly]
      cases t <;> rename_i w <;> cases w <;> rfl
  funext st
  unfold annealReadImmediate
  dsimp only
  rw [hf]

theorem IsFloatCastScalarTy.validateScalar_true {ty : Ty} {ly : LayoutTable}
    (hty : IsFloatCastScalarTy ty) (msc : Miri.Memory.ScalarInt) :
    annealValidateScalarForTyId (translateTy ty ly).ty (.fromScalarInt msc) = true := by
  rcases hty with ⟨f, hf⟩ | ⟨t, ht⟩
  · rw [translateTy_of_ieeeFormatOfTy? hf ly]; cases f <;> rfl
  · rw [translateTy_of_floatIntTargetOfTy? ht ly]
    cases t <;> rename_i w <;> cases w <;> rfl

/-- Zero-offset memory read of a stack allocation for **any** `IsFloatCastScalarTy`
(`f32`, `f64`, and all 12 integer types, extending `SimLM3_1.annealReadMemoryPlace_zero_offset_eq`
beyond `IsPrimScalarTy` to floats). -/
theorem annealReadMemoryPlace_floatCastScalar_zero_offset_eq {ty : Ty} {ly : LayoutTable}
    (hty : IsFloatCastScalarTy ty)
    {allocId : Miri.Memory.AllocId} {borTag : Miri.Memory.BorTag}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    {st : AnnealStepState}
    (hid : allocId.value.toNat < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : st.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hsz_eq : localAlloc.allocation.byteSize = (translateTy ty ly).layout.size) :
    annealReadMemoryPlace
        ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId),
          some (.concrete allocId borTag)⟩, .none, none⟩
        (translateTy ty ly) st =
      match localAlloc.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy ty ly).layout.size) false with
      | .ok sc =>
        if annealValidateScalarForTyId (translateTy ty ly).ty sc then
          .ok ⟨.scalar sc, translateTy ty ly⟩ st
        else
          .error (.undefinedBehavior "reading invalid value") st
      | .error (.invalidUninitBytes _) =>
        .error (.undefinedBehavior "read of uninitialized memory") st
      | .error (.readPointerAsInt _) | .error (.readPartialPointer _) =>
        .error (.unsupported "pointer-bytes-as-int memory read in scalar/pointer fragment") st
      | .error _ => .error (.invalidProgram "memory read error") st := by
  have hmeta :
      Miri.Memory.sizeAsI64 (translateTy ty ly).layout.size =
        .ok ((translateTy ty ly).layout.size.bytes.toNat : Int) ∧
      0 < (translateTy ty ly).layout.size.bytes.toNat ∧
      ((translateTy ty ly).layout.size.bytes.toNat : Int) < 2 ^ 63 ∧
      annealScalarReadProvenance (translateTy ty ly).layout.backendRepr = some false := by
    rcases hty with ⟨f, hf⟩ | ⟨t, ht⟩
    · rw [translateTy_of_ieeeFormatOfTy? hf ly]
      cases f <;> exact ⟨rfl, by decide, by decide, rfl⟩
    · rw [translateTy_of_floatIntTargetOfTy? ht ly]
      cases t <;> rename_i w <;> cases w <;> exact ⟨rfl, by decide, by decide, rfl⟩
  obtain ⟨hsz, hgt0, hlt63, hprov_flag⟩ := hmeta
  have hinb : 0 + (translateTy ty ly).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat := by
    rw [Nat.zero_add, hsz_eq]; exact Nat.le_refl _
  have hchk := checkAndDerefPtr_live_inbounds_ok allocId borTag 0
    (translateTy ty ly).layout.size.bytes.toNat localAlloc .memoryAccess
    hid (by show 0 < 2 ^ 32; decide) hbase hfind hgt0 hlt63 hinb
  have hoff0_sz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
  rw [hoff0_sz, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at hchk
  exact annealReadMemoryPlace_of_check_ok_aligned _ _ _ false st allocId Miri.ABI.Size.ZERO
    localAlloc _ hsz hchk hprov_flag rfl rfl hfind

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

/-! ### Part 8b. Promoted (`allocMap`) & stack-allocated (`LocalRel.indirect`) real-step simulation

In `StateRelLM3_1`, taking the raw address of an integer local (`_p = &raw (const|mut) _i`)
promotes `_i` into `allocMap` (`topFrame.locals[_i]? = some ⟨.live (.indirect (stackAllocPlace
e.allocId)), _⟩`), violating `IsImmediateFrameLocal`. Moreover, writing a `floatToInt` result
directly into promoted `_i` updates its backing stack allocation in `lean-miri` AND invalidates
conflicting Tree Borrows tags in Anneal (`updateAllocMapOnWrite allocMap dstIdx none`).
Similarly, `forceAllocation_preserves_StateRel` can promote `f32` / `f64` locals to
`LocalRel.indirect` stack allocations. The theorems below remove the `IsImmediateFrameLocal`
restriction across all three operand forms (`copy`, `move`, `constant`). -/

/-- Unified post-operand write finisher for **any** destination local `dstIdx` that is either
immediate (`IsImmediateFrameLocal tf_mid dstIdx`, where `updateAllocMapOnWrite` is the
identity) or promoted in `allocMap` (`∃ e₀ ∈ allocMap, e₀.localIdx = dstIdx`, where
`annealWriteMemoryPlace` overwrites `e₀.allocId`'s stack allocation and Anneal invalidates
conflicting Tree Borrows tags via `updateAllocMapOnWrite allocMap dstIdx none`). -/
theorem finish_write_anyLocal_from_mid_hooks
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
    (hdst_scalar : IsFloatCastScalarTy dstDecl.ty)
    (hdst_loc : IsImmediateFrameLocal tf_mid dstIdx ∨ (∃ e₀ ∈ allocMap, e₀.localIdx = dstIdx))
    {sc' : MirAst.ScalarInt} {msc' : Miri.Memory.ScalarInt}
    (hrel' : ScalarRel sc' msc')
    (hsz' : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes sc'.sizeBytes)
    (hrv_anneal : evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
      .ok (.scalar sc') s_mid.frame.locals s.memory)
    (hm_write : Miri.Interpreter.Step.evalStatement
        hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tf_mid]⟩ }) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
      (Miri.Interpreter.Step.step hooks () m) := by
  have hfr_m := hstate_mid.frame_rel_singleton rfl
  obtain ⟨_, _, _, _, _, hcal_m, hstack_m, hprot_m, hcaller_m, hbor_m, halloc_m, _⟩ :=
    id hstate_mid
  obtain ⟨slot_dm, mls_dm, hlt_af_dm, hlt_dm, hslot_dm, hmls_dm, hmls_dm_eq, hloc_dm⟩ :=
    hfr_m.lookup_local hdecl_dst
  have hs_mem : s_mid.memory = s.memory := by rw [hs_frame_eq]
  have hb_eq : s_mid.frame.blockIdx = s.frame.blockIdx := by rw [hs_frame_eq]
  have hsi_eq : s_mid.frame.stmtIdx = s.frame.stmtIdx := by rw [hs_frame_eq]
  by_cases hsd_dead : slot_dm = .dead
  · subst hsd_dead
    have hmd_dead : mls_dm.value = .dead := by
      cases hloc_dm with
      | base hb =>
        cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
        | indirect _ _ _ _ hne _ => exact absurd rfl hne
    have hdm_dead : tf_mid.locals[dstIdx]? = some ⟨.dead, mls_dm.layout⟩ := by
      rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_dead; subst hmd_dead; rfl
    have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_dead
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hslot_dm]
    have hm_err : Miri.Interpreter.Step.evalStatement
        hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
        ({ m with stack := ⟨#[tf_mid]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
      rw [hm_write]; unfold Miri.Interpreter.runRvalue
      rw [annealWriteImmediate_dead (m := { m with stack := ⟨#[tf_mid]⟩ })
        (id0 := tf.localsIdentity) rfl hget_dm]
    rw [ha_ub, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]
    exact .ub _ _
  · rcases hdst_loc with himm_dst_mid | ⟨e₀, he₀, he₀_loc⟩
    · have hnot_dst : ∀ d ∈ allocMap, d.localIdx ≠ dstIdx :=
        hstate_mid.immediate_not_in_allocMap rfl hslot_dm hsd_dead himm_dst_mid
      rw [updateAllocMapOnWrite_eq_of_not_mem allocMap dstIdx none hnot_dst]
      obtain ⟨hnb, hnc⟩ := hdst_scalar.not_bool_char
      exact finish_write_immediate_from_mid_hooks hooks hframes hbody hloc hstate_mid
        hs_frame_eq hbb hstmt hdecl_dst himm_dst_mid hrv_anneal hm_write
        (fun cachedLay hc =>
          .base (.immediate (.init (.scalar sc')) (.scalar (.fromScalarInt msc')) cachedLay hc
            (Or.inr ⟨.scalar sc', rfl,
              .scalar sc' msc' hrel' hsz' (fun h => absurd h hnb) (fun h => absurd h hnc)⟩)))
    · subst he₀_loc
      obtain ⟨d₀, hd₀, hd₀_prim⟩ := halloc_m.target_decl e₀ he₀
      have hdst_prim : IsPrimScalarTy dstDecl.ty := by
        rw [hdecl_dst] at hd₀; cases hd₀; exact hd₀_prim
      obtain ⟨⟨lay_e, hlay_e⟩, _, hsh_e⟩ :=
        (halloc_m.local_alloc_sync tf_mid rfl e₀ he₀).1 slot_dm hslot_dm hsd_dead
      obtain ⟨localAlloc, hfind_la, hkind_la, halign_la, hshape_la⟩ := hsh_e dstDecl hdecl_dst
      obtain ⟨hid_lt, _, hbase_e⟩ := halloc_m.base_addr_valid e₀ he₀
      obtain ⟨hnb, hnc⟩ := hdst_scalar.not_bool_char
      have hbool_val : dstDecl.ty.kind = .bool → sc'.sizeBytes = 1 ∧ (sc'.bits = 0 ∨ sc'.bits = 1) :=
        fun h => absurd h hnb
      have hchar_val : dstDecl.ty.kind = .char → sc'.sizeBytes = 4 ∧ isValidCharCode sc'.bits = true :=
        fun h => absurd h hnc
      have hshape_sc : StackScalarAllocShape (translateSizeBytes sc'.sizeBytes)
          localAlloc.allocation := hsz' ▸ hshape_la
      obtain ⟨alloc', hw_alloc, halign_alloc', hshape_alloc', hinit_alloc', hread_alloc'⟩ :=
        hshape_sc.writeScalar_readScalar hrel'
      have hmsc_sz : msc'.size = (translateTy dstDecl.ty body.layouts).layout.size := by
        rw [hrel'.size_eq, ← hsz']
      have hw_alloc_lay : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy dstDecl.ty body.layouts).layout.size)
          (.fromScalarInt msc') localAlloc.allocation = .ok () alloc' := by
        rw [← hmsc_sz]; exact hw_alloc
      have hval_sc : annealValidateScalarForTyId (translateTy dstDecl.ty body.layouts).ty
          (.fromScalarInt msc') = true :=
        annealValidateScalarForTyId_of_scalarRel hdst_prim hrel' hbool_val hchar_val
      have hget_dm := frame_getLocal_of_getElem? tf_mid e₀.localIdx _ hlay_e
      have hw_ind := annealWriteImmediate_indirect
        (val := .scalar (.fromScalarInt msc'))
        (m := { m with stack := ⟨#[tf_mid]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hget_dm
      have hw_m := annealWriteMemoryPlace_zero_offset_scalar_ok hdst_prim hid_lt hbase_e hfind_la
        hshape_la.mutability_eq hshape_la.byteSize_eq hmsc_sz hval_sc hw_alloc_lay
        (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tf_mid]⟩ })
      have hm_ok : Miri.Interpreter.Step.evalStatement
          hooks ()
          (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ rv, span⟩) m =
          ({ stack := ⟨#[tf_mid]⟩
             machine := { m.machine with
               memory := { m.machine.memory with
                 live := (m.machine.memory.live.filter (fun x => x.1 != e₀.allocId)).push
                   (e₀.allocId, ⟨localAlloc.kind, alloc'⟩) } } }, .ok ()) := by
        rw [hm_write]; unfold Miri.Interpreter.runRvalue
        rw [hw_ind, stackAllocPlace, hw_m]
      have hloc_mid : tf_mid.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
        have hl := hfr_m.location_eq
        rw [hb_eq, hsi_eq] at hl
        exact hl
      rw [miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc_mid]
      have hbor_s : s.memory.borrows = allocMap.map AllocMapEntry.toBorrowEntry := by
        rw [← hs_mem]; exact hbor_m
      have hprot_s : s.memory.activeProtectors = .nil := by
        rw [← hs_mem]; exact hprot_m
      have hstack_s : s.memory.callStack = .nil := by
        rw [← hs_mem]; exact hstack_m
      have ha_ok : evalStmt s ⟨.assign ⟨e₀.localIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
          MirStepNode.step
            (advanceStmt s_mid (s_mid.frame.locals.set e₀.localIdx (.init (.scalar sc')))
              { s_mid.memory with
                borrows := (updateAllocMapOnWrite allocMap e₀.localIdx none).map
                  AllocMapEntry.toBorrowEntry }) := by
        have hadv_eq :
            advanceStmt s (s_mid.frame.locals.set e₀.localIdx (.init (.scalar sc')))
              { s.memory with
                borrows := (updateAllocMapOnWrite allocMap e₀.localIdx none).map
                  AllocMapEntry.toBorrowEntry } =
            advanceStmt s_mid (s_mid.frame.locals.set e₀.localIdx (.init (.scalar sc')))
              { s_mid.memory with
                borrows := (updateAllocMapOnWrite allocMap e₀.localIdx none).map
                  AllocMapEntry.toBorrowEntry } := by
          rw [hs_frame_eq]; rfl
        rw [← hadv_eq]
        unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hstack_s, hslot_dm]
        cases slot_dm with
        | dead => exact absurd rfl hsd_dead
        | uninit =>
          simp only [set?_eq_some_set hlt_af_dm, length, List.length_nil, hprot_s, hbor_s,
            invalidateConflictingBorrows_map_toBorrowEntry]
        | init _ =>
          simp only [set?_eq_some_set hlt_af_dm, length, List.length_nil, hprot_s, hbor_s,
            invalidateConflictingBorrows_map_toBorrowEntry]
      rw [ha_ok]
      refine .step _ _ ?_
      have hstep_rel := hstate_mid.advance_write_deref_scalar rfl
        (fun x => x.updateOnWrite e₀.localIdx none)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        he₀ hdecl_dst hdst_prim hslot_dm hsd_dead hfind_la hkind_la halign_la
        hrel' hsz' hbool_val hchar_val halign_alloc' hshape_alloc' hinit_alloc' hread_alloc'
      rw [hb_eq, hsi_eq] at hstep_rel
      exact hstep_rel

theorem IsFloatCastScalarTy.of_kind_eq {ty₁ ty₂ : Ty} (h : IsFloatCastScalarTy ty₂)
    (hk : ty₁.kind = ty₂.kind) : IsFloatCastScalarTy ty₁ := by
  rcases h with ⟨f, hf⟩ | ⟨t, ht⟩
  · exact Or.inl ⟨f, by unfold ieeeFormatOfTy? at hf ⊢; rw [hk]; exact hf⟩
  · exact Or.inr ⟨t, by unfold floatIntTargetOfTy? at ht ⊢; rw [hk]; exact ht⟩

/-- Compositional frame-immediacy & `nextAllocId` preservation across a Miri step:
whenever the step succeeds with `(m', .ok true)`, `nextAllocId` is unchanged (float casts
never allocate stack slots) and every local that satisfied `IsImmediateFrameLocal` before
the step still satisfies `IsImmediateFrameLocal` after the step. This closes the multi-step
compositionality gap where `StepRelLM3_1` alone would forget `IsImmediateFrameLocal`. -/
def FloatStepPreservesImm (m : AnnealStepState)
    (mStep : AnnealStepState × Except Miri.Interpreter.StepError Bool) : Prop :=
  ∀ m', mStep = (m', .ok true) →
    m'.machine.memory.nextAllocId = m.machine.memory.nextAllocId ∧
    ∀ tf₀ tf', m.stack.frames = #[tf₀] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf₀ k → IsImmediateFrameLocal tf' k

private theorem floatCast_set_immediate
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Local} (hlt : dstIdx < tf.locals.size)
    (val : Miri.Interpreter.Immediate AnnealProv) (lay : Option Miri.Interpreter.LocalLayout)
    (loc' : Miri.Interpreter.FrameLocation) :
    ∀ {k}, IsImmediateFrameLocal tf k →
      IsImmediateFrameLocal
        { tf with locals := tf.locals.set dstIdx ⟨.live (.immediate val), lay⟩ hlt, location := loc' }
        k := by
  intro k hk mls hmls mp hmp
  dsimp only at hmls
  rw [Array.getElem?_set] at hmls
  by_cases hkd : dstIdx = k
  · simp only [hkd, ↓reduceIte] at hmls
    injection hmls with hm; rw [← hm] at hmp; cases hmp
  · simp only [hkd, ↓reduceIte] at hmls
    exact hk mls hmls mp hmp

theorem finish_write_anyLocal_preserves
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
    (himm_mid : ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf_mid k)
    {bb : BasicBlockData} {dstIdx : Local} {dstDecl : LocalDecl} {rv : Rvalue} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_scalar : IsFloatCastScalarTy dstDecl.ty)
    (hdst_loc : IsImmediateFrameLocal tf_mid dstIdx ∨ (∃ e₀ ∈ allocMap, e₀.localIdx = dstIdx))
    {sc' : MirAst.ScalarInt} {msc' : Miri.Memory.ScalarInt}
    (hrel' : ScalarRel sc' msc')
    (hsz' : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes sc'.sizeBytes)
    (hm_write : Miri.Interpreter.Step.evalStatement
        hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tf_mid]⟩ }) :
    FloatStepPreservesImm m (Miri.Interpreter.Step.step hooks () m) := by
  have hfr_m := hstate_mid.frame_rel_singleton rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc_m, _⟩ := id hstate_mid
  obtain ⟨slot_dm, mls_dm, _, hlt_dm, hslot_dm, hmls_dm, _, hloc_dm⟩ :=
    hfr_m.lookup_local hdecl_dst
  have hb_eq : s_mid.frame.blockIdx = s.frame.blockIdx := by rw [hs_frame_eq]
  have hsi_eq : s_mid.frame.stmtIdx = s.frame.stmtIdx := by rw [hs_frame_eq]
  have hloc_mid : tf_mid.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
    have hl := hfr_m.location_eq; rw [hb_eq, hsi_eq] at hl; exact hl
  by_cases hsd_dead : slot_dm = .dead
  · subst hsd_dead
    have hmd_dead : mls_dm.value = .dead := by
      cases hloc_dm with
      | base hb =>
        cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
        | indirect _ _ _ _ hne _ => exact absurd rfl hne
    have hdm_dead : tf_mid.locals[dstIdx]? = some ⟨.dead, mls_dm.layout⟩ := by
      rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_dead; subst hmd_dead; rfl
    have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_dead
    have hm_err : Miri.Interpreter.Step.evalStatement
        hooks () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
        ({ m with stack := ⟨#[tf_mid]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
      rw [hm_write]; unfold Miri.Interpreter.runRvalue
      rw [annealWriteImmediate_dead (m := { m with stack := ⟨#[tf_mid]⟩ })
        (id0 := tf.localsIdentity) rfl hget_dm]
    rw [miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]
    exact fun _ h => nomatch h
  · rcases hdst_loc with himm_dst_mid | ⟨e₀, he₀, he₀_loc⟩
    · have hold_imm : ∃ oldImm, mls_dm.value = .live (.immediate oldImm) := by
        cases hloc_dm with
        | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
        | base hb =>
          cases hb with
          | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst_mid _ hmls_dm mp)
          | dead _ _ => exact absurd rfl hsd_dead
          | immediate _ oldImm _ _ _ => exact ⟨oldImm, rfl⟩
      obtain ⟨oldImm, hmd_imm⟩ := hold_imm
      have hdm_live : tf_mid.locals[dstIdx]? =
          some ⟨.live (.immediate oldImm), mls_dm.layout⟩ := by
        rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
      have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_live
      have hw_ok := annealWriteImmediate_live (val := .scalar (.fromScalarInt msc'))
        (m := { m with stack := ⟨#[tf_mid]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dm hget_dm
      have hm_ok : Miri.Interpreter.Step.evalStatement
          hooks () (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
          ({ m with stack := ⟨#[{ tf_mid with
              locals := tf_mid.locals.set dstIdx
                { tf_mid.locals[dstIdx]'hlt_dm with value := .live (.immediate (.scalar (.fromScalarInt msc'))) }
                hlt_dm }]⟩ }, .ok ()) := by
        rw [hm_write]; unfold Miri.Interpreter.runRvalue; rw [hw_ok]
      rw [miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc_mid]
      intro m' hm'
      injection hm' with hm'_eq _
      subst hm'_eq
      refine ⟨rfl, ?_⟩
      intro tf₀ tf' htf₀ htf' k hk
      rw [hframes] at htf₀
      injection htf₀ with h0; injection h0 with h0'; subst h0'
      injection htf' with h1; injection h1 with h1'; subst h1'
      exact floatCast_set_immediate hlt_dm (.scalar (.fromScalarInt msc'))
        (tf_mid.locals[dstIdx]'hlt_dm).layout _ (himm_mid k hk)
    · subst he₀_loc
      obtain ⟨d₀, hd₀, hd₀_prim⟩ := halloc_m.target_decl e₀ he₀
      have hdst_prim : IsPrimScalarTy dstDecl.ty := by
        rw [hdecl_dst] at hd₀; cases hd₀; exact hd₀_prim
      obtain ⟨⟨lay_e, hlay_e⟩, _, hsh_e⟩ :=
        (halloc_m.local_alloc_sync tf_mid rfl e₀ he₀).1 slot_dm hslot_dm hsd_dead
      obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh_e dstDecl hdecl_dst
      obtain ⟨hid_lt, _, hbase_e⟩ := halloc_m.base_addr_valid e₀ he₀
      obtain ⟨hnb, hnc⟩ := hdst_scalar.not_bool_char
      have hshape_sc : StackScalarAllocShape (translateSizeBytes sc'.sizeBytes)
          localAlloc.allocation := hsz' ▸ hshape_la
      obtain ⟨alloc', hw_alloc, _, _, _, _⟩ := hshape_sc.writeScalar_readScalar hrel'
      have hmsc_sz : msc'.size = (translateTy dstDecl.ty body.layouts).layout.size := by
        rw [hrel'.size_eq, ← hsz']
      have hw_alloc_lay : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy dstDecl.ty body.layouts).layout.size)
          (.fromScalarInt msc') localAlloc.allocation = .ok () alloc' := by
        rw [← hmsc_sz]; exact hw_alloc
      have hval_sc : annealValidateScalarForTyId (translateTy dstDecl.ty body.layouts).ty
          (.fromScalarInt msc') = true :=
        annealValidateScalarForTyId_of_scalarRel hdst_prim hrel'
          (fun h => absurd h hnb) (fun h => absurd h hnc)
      have hget_dm := frame_getLocal_of_getElem? tf_mid e₀.localIdx _ hlay_e
      have hw_ind := annealWriteImmediate_indirect
        (val := .scalar (.fromScalarInt msc'))
        (m := { m with stack := ⟨#[tf_mid]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hget_dm
      have hw_m := annealWriteMemoryPlace_zero_offset_scalar_ok hdst_prim hid_lt hbase_e hfind_la
        hshape_la.mutability_eq hshape_la.byteSize_eq hmsc_sz hval_sc hw_alloc_lay
        (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tf_mid]⟩ })
      have hm_ok : Miri.Interpreter.Step.evalStatement
          hooks () (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ rv, span⟩) m =
          ({ stack := ⟨#[tf_mid]⟩
             machine := { m.machine with
               memory := { m.machine.memory with
                 live := (m.machine.memory.live.filter (fun x => x.1 != e₀.allocId)).push
                   (e₀.allocId, ⟨localAlloc.kind, alloc'⟩) } } }, .ok ()) := by
        rw [hm_write]; unfold Miri.Interpreter.runRvalue
        rw [hw_ind, stackAllocPlace, hw_m]
      rw [miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc_mid]
      intro m' hm'
      injection hm' with hm'_eq _
      subst hm'_eq
      refine ⟨rfl, ?_⟩
      intro tf₀ tf' htf₀ htf' k hk mls hmls mp hmp
      rw [hframes] at htf₀
      injection htf₀ with h0; injection h0 with h0'; subst h0'
      injection htf' with h1; injection h1 with h1'; subst h1'
      exact himm_mid k hk mls hmls mp hmp

/-- **Copy-operand real-step simulation across immediate AND promoted (`allocMap`) locals**
(`_d = copy _s as T` in either NaN mode): both `_s` and `_d` may be either immediate
(`IsImmediateFrameLocal`) or address-taken / promoted in `allocMap` (`∃ e ∈ allocMap,
e.localIdx = _`). Dead or uninitialized sources (including uninitialized memory-backed
stack allocations) report UB in both machines; initialized sources write `ScalarRel`-related
cast results and update `allocMap` via `updateAllocMapOnWrite allocMap dstIdx none` (which
is the identity when `_d` is immediate and invalidates conflicting Tree Borrows tags when
`_d` is promoted). -/
theorem step_cast_float_copy_anyLocal_simulation_mode
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
    (hsrc_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame srcIdx ∨ (∃ es ∈ allocMap, es.localIdx = srcIdx))
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
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
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have hdst_tfb : IsImmediateFrameLocal tfb dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
    rcases hdst_loc tf hframes with himm_d | hed
    · exact Or.inl ((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _)
    · exact Or.inr hed
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  by_cases hss_dead : slot_s = .dead
  · subst hss_dead
    have hms : mls_s.value = .dead := by
      cases hloc_s with
      | base hb =>
        cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
        | indirect _ _ _ _ hne _ => exact absurd rfl hne
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · rcases hsrc_loc tf hframes with himm_s | ⟨es, hes, hes_loc⟩
    · have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := himm_s.cache_layout hlt_d _
      rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
        ⟨hss, _⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
      · exact absurd hss hss_dead
      · subst hss
        have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
          rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
        have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
          (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
        have ha_ub : evalStmt s
            ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
          unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
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
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_un]
          rfl
        rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        exact .ub _ _
      · subst hss
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
          rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
          have hop : evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows
              s.memory.globals body.layouts s.memory.callerLocals body.localDecls
              s.memory.callStack = .ok (.scalar sc) s.frame.locals := by
            unfold evalOperand readProjectedValue; dsimp only []; rw [hslot_s]
          rw [hop]; dsimp only []; rw [operandTy_copy_local hdecl_src, hev]
        have hm_write : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
            Miri.Interpreter.runRvalue
              (annealWriteImmediate (.scalar (.fromScalarInt msc'))
                ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
        exact finish_write_anyLocal_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
          hstate_b rfl hbb hstmt hdecl_dst hdst_scalar hdst_tfb hrel' hsz' hrv_a hm_write
    · -- `_s` is promoted in `allocMap` (`es.localIdx = srcIdx`).
      subst hes_loc
      obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc_a, _⟩ := id hstate_a
      obtain ⟨⟨lay_s, hlay_s⟩, hsc_only, hsh_s⟩ :=
        (halloc_a.local_alloc_sync tfa rfl es hes).1 slot_s hslot_s hss_dead
      obtain ⟨localAlloc_s, hfind_s, _, _, hshape_s⟩ := hsh_s srcDecl hdecl_src
      obtain ⟨hid_lt_s, _, hbase_s⟩ := halloc_a.base_addr_valid es hes
      have hmls_s_ind : mls_s = ⟨.live (.indirect (stackAllocPlace es.allocId)), lay_s⟩ := by
        rw [hmls_s] at hlay_s; exact Option.some.inj hlay_s
      have hmls_s' : tfa.locals[es.localIdx]'hlt_sa =
          ⟨.live (.indirect (stackAllocPlace es.allocId)), lay_s⟩ := by
        rw [hmls_s_eq]; exact hmls_s_ind
      have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' (by rw [hmls_s_ind] at hcache_s; exact hcache_s)
      obtain ⟨hun_s, hsc_s⟩ := hloc_s.indirect_stackAllocPlace_spec hmls_s_ind hbase_s hfind_s
        (halloc_a.live_key_unique es hes) (hsig.src_scalar.size_ne_zero body.layouts)
      have hread_mem := annealReadMemoryPlace_floatCastScalar_zero_offset_eq hsig.src_scalar
        hid_lt_s hbase_s hfind_s hshape_s.byteSize_eq
        (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tfb]⟩ })
      cases hss : slot_s with
      | dead => exact absurd hss hss_dead
      | uninit =>
        obtain ⟨_, hread_err⟩ := hshape_s.uninit_readScalar_err (hun_s hss) false
        have hri_err : annealReadImmediate
            ⟨.indirect (stackAllocPlace es.allocId), translateTy srcDecl.ty body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } =
            .error (.undefinedBehavior "read of uninitialized memory")
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
            hread_mem, hread_err]
        have hcast_err := cast_floatCast_of_readImmediate_err body.layouts nondet chooseNaN hsig
          (.indirect (stackAllocPlace es.allocId)) (.local 0 dstIdx none tf.localsIdentity) hri_err
        rw [← hdstT] at hcast_err
        have ha_ub : evalStmt s
            ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨es.localIdx, .nil⟩) castTy), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
          unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s, hss]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨es.localIdx, .nil⟩) castTy), span⟩) m =
            ({ m with stack := ⟨#[tfb]⟩ },
              .error (.undefinedBehavior "read of uninitialized memory")) := by
          rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
        rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        exact .ub _ _
      | init vs =>
        obtain ⟨sc, rfl⟩ := hsc_only vs hss
        obtain ⟨hsz, _, _, msc, hrel, hread_ok⟩ := hsc_s sc hss
        have hri_ok : annealReadImmediate
            ⟨.indirect (stackAllocPlace es.allocId), translateTy srcDecl.ty body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } =
            .ok ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
            hread_mem, hread_ok]
          dsimp only []
          rw [hsig.src_scalar.validateScalar_true msc]
          rfl
        have hcast_red := cast_floatCast_of_readImmediate_scalar body.layouts nondet chooseNaN hsig
          (.indirect (stackAllocPlace es.allocId)) (.local 0 dstIdx none tf.localsIdentity)
          (.fromScalarInt msc) hri_ok
        obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
          (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
          (fun h => hagree h sc (hss ▸ hslot_s)) (.local 0 dstIdx none tf.localsIdentity)
        have hcast_ind :
            Miri.Interpreter.Cast.cast (annealCastHooksFloat body.layouts nondet chooseNaN) () 16
              ⟨.indirect (stackAllocPlace es.allocId), translateTy srcDecl.ty body.layouts⟩
              (translateCastKind kind) (encodeTyId castTy)
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
              { m with stack := ⟨#[tfb]⟩ } =
            annealWriteImmediate (.scalar (.fromScalarInt msc'))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [hdstT]; exact hcast_red.trans (congrFun hcast _)
        rw [← hdstT] at hsz'
        have hrv_a : evalRvalue s.frame.locals (.cast kind (.copy ⟨es.localIdx, .nil⟩) castTy) s.memory
            body.localDecls body.layouts = .ok (.scalar sc') s.frame.locals s.memory := by
          rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
          have hop : evalOperand s.frame.locals (.copy ⟨es.localIdx, .nil⟩) s.memory.borrows
              s.memory.globals body.layouts s.memory.callerLocals body.localDecls
              s.memory.callStack = .ok (.scalar sc) s.frame.locals := by
            unfold evalOperand readProjectedValue; dsimp only []; rw [hslot_s, hss]
          rw [hop]; dsimp only []; rw [operandTy_copy_local hdecl_src, hev]
        have hm_write : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨es.localIdx, .nil⟩) castTy), span⟩) m =
            Miri.Interpreter.runRvalue
              (annealWriteImmediate (.scalar (.fromScalarInt msc'))
                ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_ind]
        exact finish_write_anyLocal_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
          hstate_b rfl hbb hstmt hdecl_dst hdst_scalar hdst_tfb hrel' hsz' hrv_a hm_write

/-- **Copy-operand real-step simulation across immediate AND promoted (`allocMap`) locals**
under the NaN refinement witness (`floatNondeterministic := true`,
`chooseNaN := annealChooseQuietedNaN`). -/
theorem step_cast_float_copy_anyLocal_simulation
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
    (hsrc_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame srcIdx ∨ (∃ es ∈ allocMap, es.localIdx = srcIdx))
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_copy_anyLocal_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) hsrc_loc hdst_loc hptr8

/-- **Move-operand real-step simulation into immediate OR promoted (`allocMap`) `_d`**
(`_d = move _s as T` in either NaN mode): deinitializes immediate `_s` in both machines and
writes into either an immediate `_d` or a promoted `allocMap` local `_d`. -/
theorem step_cast_float_move_anyLocal_simulation_mode
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
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have himm_s := himm_src tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
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
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hcast_un := cast_floatCast_uninit body.layouts nondet chooseNaN hsig
      (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast_un
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_un]
      rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · subst hss
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
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) (s.frame.locals.set srcIdx .uninit) := by
        unfold evalOperand; dsimp only []; rw [hslot_s, set?_eq_some_set hlt_af_s]
      rw [hop]; dsimp only []; rw [operandTy_move_local hdecl_src, hev]
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
    have hdst_mid : IsImmediateFrameLocal (deinitFrameLocal tfb srcIdx hlt_sb) dstIdx ∨
        (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
      rcases hdst_loc tf hframes with himm_d | hed
      · exact Or.inl (((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb)
      · exact Or.inr hed
    exact finish_write_anyLocal_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_mid rfl hbb hstmt hdecl_dst hdst_scalar hdst_mid hrel' hsz' hrv_a hm_write

/-- **Move-operand real-step simulation into immediate OR promoted (`allocMap`) `_d`**
under the NaN refinement witness. -/
theorem step_cast_float_move_anyLocal_simulation
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
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_move_anyLocal_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) himm_src hdst_loc hptr8

/-- **Constant-operand real-step simulation into immediate OR promoted (`allocMap`) `_d`**
(`_d = const c as T` in either NaN mode). -/
theorem step_cast_float_constant_anyLocal_simulation_mode
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
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
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
    rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]; dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl, hev]
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tfa]⟩ } := by
    rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
  have hdst_tfa : IsImmediateFrameLocal tfa dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
    rcases hdst_loc tf hframes with himm_d | hed
    · exact Or.inl (himm_d.cache_layout hlt_d _)
    · exact Or.inr hed
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  exact finish_write_anyLocal_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
    hstate_a rfl hbb hstmt hdecl_dst hdst_scalar hdst_tfa hrel' hsz' hrv_a hm_write

/-- **Constant-operand real-step simulation into immediate OR promoted (`allocMap`) `_d`**
under the NaN refinement witness. -/
theorem step_cast_float_constant_anyLocal_simulation
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
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_constant_anyLocal_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hsig hdst_ty hval hsz hcan hlaysz
    (fun h => absurd h (by decide)) hdst_loc hptr8

/-- **Multi-step compositionality (`FloatStepPreservesImm`) for `constant` float casts**:
any successful `_d = const c as T` step preserves `IsImmediateFrameLocal` for every local
and leaves `nextAllocId` unchanged. -/
theorem step_cast_float_constant_anyLocal_preserves
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
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
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    FloatStepPreservesImm m
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
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
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
  have hsrc_ok : annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c)) none
      { m with stack := ⟨#[tfa]⟩ } =
      .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } := by
    with_unfolding_all
      unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
      dsimp only; rw [hval]
      simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
        EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        stack_currentFrame?_singleton { m with stack := ⟨#[tfa]⟩ }.stack tfa rfl, Option.isNone_some,
        Bool.false_eq_true, ↓reduceIte, htry,
        layoutOfEncodedTyId_floatCastScalar hsig.src_scalar body.layouts]
  obtain ⟨sc', msc', _, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
    (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hlaysz hagree
    (.local 0 dstIdx none tf.localsIdentity)
  rw [← hdstT] at hcast hsz'
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tfa]⟩ } := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
  have hdst_tfa : IsImmediateFrameLocal tfa dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
    rcases hdst_loc tf hframes with himm_d | hed
    · exact Or.inl (himm_d.cache_layout hlt_d _)
    · exact Or.inr hed
  exact finish_write_anyLocal_preserves _ hframes hfr.body_eq hfr.location_eq hstate_a rfl
    (fun _ hk => hk.cache_layout hlt_d _) hbb hstmt hdecl_dst hdst_scalar hdst_tfa
    hrel' hsz' hm_write

/-- **Multi-step compositionality (`FloatStepPreservesImm`) for `copy` float casts**:
any successful `_d = copy _s as T` step (from immediate or promoted `_s` into immediate or
promoted `_d`) preserves `IsImmediateFrameLocal` for every local and leaves `nextAllocId`
unchanged. -/
theorem step_cast_float_copy_anyLocal_preserves
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
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
    (hsrc_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame srcIdx ∨ (∃ es ∈ allocMap, es.localIdx = srcIdx))
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    FloatStepPreservesImm m
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
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
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have hdst_tfb : IsImmediateFrameLocal tfb dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
    rcases hdst_loc tf hframes with himm_d | hed
    · exact Or.inl ((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _)
    · exact Or.inr hed
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
  by_cases hss_dead : slot_s = .dead
  · subst hss_dead
    have hms : mls_s.value = .dead := by
      cases hloc_s with
      | base hb =>
        cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
        | indirect _ _ _ _ hne _ => exact absurd rfl hne
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact fun _ h => nomatch h
  · rcases hsrc_loc tf hframes with himm_s | ⟨es, hes, hes_loc⟩
    · have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := himm_s.cache_layout hlt_d _
      rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
        ⟨hss, _⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
      · exact absurd hss hss_dead
      · subst hss
        have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
          rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
        have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
          (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
        have hcast_un := cast_floatCast_uninit body.layouts nondet chooseNaN hsig
          (.local 0 dstIdx none tf.localsIdentity)
        rw [← hdstT] at hcast_un
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
            ({ m with stack := ⟨#[tfb]⟩ },
              .error (.undefinedBehavior "read of uninitialized local")) := by
          rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_un]; rfl
        rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        exact fun _ h => nomatch h
      · subst hss
        obtain ⟨sc', msc', _, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
          (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
          (fun h => hagree h sc hslot_s) (.local 0 dstIdx none tf.localsIdentity)
        rw [← hdstT] at hcast hsz'
        have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
            ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
          rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
        have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
          (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
        have hm_write : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
            Miri.Interpreter.runRvalue
              (annealWriteImmediate (.scalar (.fromScalarInt msc'))
                ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
        exact finish_write_anyLocal_preserves _ hframes hfr.body_eq hfr.location_eq hstate_b rfl
          (fun _ hk => (hk.cache_layout hlt_d _).cache_layout hlt_sa _)
          hbb hstmt hdecl_dst hdst_scalar hdst_tfb hrel' hsz' hm_write
    · subst hes_loc
      obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc_a, _⟩ := id hstate_a
      obtain ⟨⟨lay_s, hlay_s⟩, hsc_only, hsh_s⟩ :=
        (halloc_a.local_alloc_sync tfa rfl es hes).1 slot_s hslot_s hss_dead
      obtain ⟨localAlloc_s, hfind_s, _, _, hshape_s⟩ := hsh_s srcDecl hdecl_src
      obtain ⟨hid_lt_s, _, hbase_s⟩ := halloc_a.base_addr_valid es hes
      have hmls_s_ind : mls_s = ⟨.live (.indirect (stackAllocPlace es.allocId)), lay_s⟩ := by
        rw [hmls_s] at hlay_s; exact Option.some.inj hlay_s
      have hmls_s' : tfa.locals[es.localIdx]'hlt_sa =
          ⟨.live (.indirect (stackAllocPlace es.allocId)), lay_s⟩ := by
        rw [hmls_s_eq]; exact hmls_s_ind
      have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' (by rw [hmls_s_ind] at hcache_s; exact hcache_s)
      obtain ⟨hun_s, hsc_s⟩ := hloc_s.indirect_stackAllocPlace_spec hmls_s_ind hbase_s hfind_s
        (halloc_a.live_key_unique es hes) (hsig.src_scalar.size_ne_zero body.layouts)
      have hread_mem := annealReadMemoryPlace_floatCastScalar_zero_offset_eq hsig.src_scalar
        hid_lt_s hbase_s hfind_s hshape_s.byteSize_eq
        (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tfb]⟩ })
      cases hss : slot_s with
      | dead => exact absurd hss hss_dead
      | uninit =>
        obtain ⟨_, hread_err⟩ := hshape_s.uninit_readScalar_err (hun_s hss) false
        have hri_err : annealReadImmediate
            ⟨.indirect (stackAllocPlace es.allocId), translateTy srcDecl.ty body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } =
            .error (.undefinedBehavior "read of uninitialized memory")
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
            hread_mem, hread_err]
        have hcast_err := cast_floatCast_of_readImmediate_err body.layouts nondet chooseNaN hsig
          (.indirect (stackAllocPlace es.allocId)) (.local 0 dstIdx none tf.localsIdentity) hri_err
        rw [← hdstT] at hcast_err
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨es.localIdx, .nil⟩) castTy), span⟩) m =
            ({ m with stack := ⟨#[tfb]⟩ },
              .error (.undefinedBehavior "read of uninitialized memory")) := by
          rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
        rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        exact fun _ h => nomatch h
      | init vs =>
        obtain ⟨sc, rfl⟩ := hsc_only vs hss
        obtain ⟨hsz, _, _, msc, hrel, hread_ok⟩ := hsc_s sc hss
        have hri_ok : annealReadImmediate
            ⟨.indirect (stackAllocPlace es.allocId), translateTy srcDecl.ty body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } =
            .ok ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
            hread_mem, hread_ok]
          dsimp only []
          rw [hsig.src_scalar.validateScalar_true msc]; rfl
        have hcast_red := cast_floatCast_of_readImmediate_scalar body.layouts nondet chooseNaN hsig
          (.indirect (stackAllocPlace es.allocId)) (.local 0 dstIdx none tf.localsIdentity)
          (.fromScalarInt msc) hri_ok
        obtain ⟨sc', msc', _, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
          (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
          (fun h => hagree h sc (hss ▸ hslot_s)) (.local 0 dstIdx none tf.localsIdentity)
        have hcast_ind :
            Miri.Interpreter.Cast.cast (annealCastHooksFloat body.layouts nondet chooseNaN) () 16
              ⟨.indirect (stackAllocPlace es.allocId), translateTy srcDecl.ty body.layouts⟩
              (translateCastKind kind) (encodeTyId castTy)
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
              { m with stack := ⟨#[tfb]⟩ } =
            annealWriteImmediate (.scalar (.fromScalarInt msc'))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [hdstT]; exact hcast_red.trans (congrFun hcast _)
        rw [← hdstT] at hsz'
        have hm_write : Miri.Interpreter.Step.evalStatement
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨es.localIdx, .nil⟩) castTy), span⟩) m =
            Miri.Interpreter.runRvalue
              (annealWriteImmediate (.scalar (.fromScalarInt msc'))
                ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
              { m with stack := ⟨#[tfb]⟩ } := by
          rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_ind]
        exact finish_write_anyLocal_preserves _ hframes hfr.body_eq hfr.location_eq hstate_b rfl
          (fun _ hk => (hk.cache_layout hlt_d _).cache_layout hlt_sa _)
          hbb hstmt hdecl_dst hdst_scalar hdst_tfb hrel' hsz' hm_write

/-- **Multi-step compositionality (`FloatStepPreservesImm`) for `move` float casts**:
any successful `_d = move _s as T` step (deinitializing immediate `_s` and writing into
immediate or promoted `_d`) preserves `IsImmediateFrameLocal` for every local and leaves
`nextAllocId` unchanged. -/
theorem step_cast_float_move_anyLocal_preserves
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
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
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    FloatStepPreservesImm m
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  have himm_s := himm_src tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
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
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact fun _ h => nomatch h
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hcast_un := cast_floatCast_uninit body.layouts nondet chooseNaN hsig
      (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast_un
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_un]; rfl
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact fun _ h => nomatch h
  · subst hss
    obtain ⟨sc', msc', _, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
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
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
    have hdst_mid : IsImmediateFrameLocal (deinitFrameLocal tfb srcIdx hlt_sb) dstIdx ∨
        (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
      rcases hdst_loc tf hframes with himm_d | hed
      · exact Or.inl (((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb)
      · exact Or.inr hed
    exact finish_write_anyLocal_preserves _ hframes hfr.body_eq hfr.location_eq hstate_mid rfl
      (fun _ hk => ((hk.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb)
      hbb hstmt hdecl_dst hdst_scalar hdst_mid hrel' hsz' hm_write

/-- **Copy-operand real-step simulation for stack-allocated (`LocalRel.indirect`) `f32`/`f64`
and integer locals** (such as locals promoted via `forceAllocation_preserves_StateRel`, even
when absent from `allocMap`): both `.uninit` (`"read of uninitialized memory"` UB) and
initialized scalar values step in `StepRelLM3_1` lockstep into any immediate or promoted `_d`. -/
theorem step_cast_float_copy_indirect_float_simulation_mode
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
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (huniq : ∀ la₁ la₂, (allocId, la₁) ∈ m.machine.memory.live.toList →
      (allocId, la₂) ∈ m.machine.memory.live.toList → la₁ = la₂)
    (hshape : StackScalarAllocShape (translateTy srcDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_src : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[srcIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hsc_src : ∀ v, get? s.frame.locals srcIdx = some (.init v) → ∃ sc, v = .scalar sc)
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨lay_0, hlay_0⟩ := hind_src tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
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
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have hdst_tfb : IsImmediateFrameLocal tfb dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
    rcases hdst_loc tf hframes with himm_d | hed
    · exact Or.inl ((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _)
    · exact Or.inr hed
  have hlay_tfa : ∃ lay_s, tfa.locals[srcIdx]? =
      some ⟨.live (.indirect (stackAllocPlace allocId)), lay_s⟩ := by
    dsimp [tfa, cacheFrameLocalLayout]
    rw [Array.getElem?_set]
    by_cases hds : dstIdx = srcIdx
    · subst hds
      simp only [↓reduceIte, Array.getElem?_eq_getElem hlt_d] at hlay_0 ⊢
      injection hlay_0 with hm0
      rw [hm0]
      exact ⟨_, rfl⟩
    · simp only [hds, ↓reduceIte]
      exact ⟨lay_0, hlay_0⟩
  obtain ⟨lay_s, hlay_s⟩ := hlay_tfa
  have hmls_s_ind : mls_s = ⟨.live (.indirect (stackAllocPlace allocId)), lay_s⟩ := by
    rw [hmls_s] at hlay_s; exact Option.some.inj hlay_s
  have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
      ⟨.live (.indirect (stackAllocPlace allocId)), lay_s⟩ := by
    rw [hmls_s_eq]; exact hmls_s_ind
  have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
    (known := none) rfl hlt_sa hdecl_src hmls_s' (by rw [hmls_s_ind] at hcache_s; exact hcache_s)
  let dummyEntry : AllocMapEntry :=
    { tag := 0, localIdx := srcIdx, allocId := allocId, perm := .active }
  have hmls_dummy : mls_s = ⟨.live (.indirect (stackAllocPlace dummyEntry.allocId)), lay_s⟩ :=
    hmls_s_ind
  obtain ⟨hun_s, hsc_s⟩ := hloc_s.indirect_stackAllocPlace_spec (e := dummyEntry)
    hmls_dummy hbase hfind huniq (hsig.src_scalar.size_ne_zero body.layouts)
  have hread_mem := annealReadMemoryPlace_floatCastScalar_zero_offset_eq hsig.src_scalar
    hid_lt hbase hfind hshape.byteSize_eq
    (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tfb]⟩ })
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  cases hss : slot_s with
  | dead =>
    have hnd : slot_s ≠ .dead := by
      cases hloc_s with
      | rawPtr _ _ _ _ _ _ _ _ => cases hmls_s_ind
      | base hb =>
        cases hb with
        | dead _ _ => cases hmls_s_ind
        | immediate _ _ _ _ _ => cases hmls_s_ind
        | indirect _ _ _ _ hne _ => exact hne
    exact absurd hss hnd
  | uninit =>
    obtain ⟨_, hread_err⟩ := hshape.uninit_readScalar_err (hun_s hss) false
    have hri_err : annealReadImmediate
        ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } =
        .error (.undefinedBehavior "read of uninitialized memory")
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
        hread_mem, hread_err]
    have hcast_err := cast_floatCast_of_readImmediate_err body.layouts nondet chooseNaN hsig
      (.indirect (stackAllocPlace allocId)) (.local 0 dstIdx none tf.localsIdentity) hri_err
    rw [← hdstT] at hcast_err
    have ha_ub : evalStmt s
        ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s, hss]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ },
          .error (.undefinedBehavior "read of uninitialized memory")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  | init vs =>
    obtain ⟨sc, rfl⟩ := hsc_src vs (hss ▸ hslot_s)
    obtain ⟨hsz, _, _, msc, hrel, hread_ok⟩ := hsc_s sc hss
    have hri_ok : annealReadImmediate
        ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
        hread_mem, hread_ok]
      dsimp only []
      rw [hsig.src_scalar.validateScalar_true msc]
      rfl
    have hcast_red := cast_floatCast_of_readImmediate_scalar body.layouts nondet chooseNaN hsig
      (.indirect (stackAllocPlace allocId)) (.local 0 dstIdx none tf.localsIdentity)
      (.fromScalarInt msc) hri_ok
    obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
      (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
      (fun h => hagree h sc (hss ▸ hslot_s)) (.local 0 dstIdx none tf.localsIdentity)
    have hcast_ind :
        Miri.Interpreter.Cast.cast (annealCastHooksFloat body.layouts nondet chooseNaN) () 16
          ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty body.layouts⟩
          (translateCastKind kind) (encodeTyId castTy)
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } =
        annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [hdstT]; exact hcast_red.trans (congrFun hcast _)
    rw [← hdstT] at hsz'
    have hrv_a : evalRvalue s.frame.locals (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts = .ok (.scalar sc') s.frame.locals s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows
          s.memory.globals body.layouts s.memory.callerLocals body.localDecls
          s.memory.callStack = .ok (.scalar sc) s.frame.locals := by
        unfold evalOperand readProjectedValue; dsimp only []; rw [hslot_s, hss]
      rw [hop]; dsimp only []; rw [operandTy_copy_local hdecl_src, hev]
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_ind]
    exact finish_write_anyLocal_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_b rfl hbb hstmt hdecl_dst hdst_scalar hdst_tfb hrel' hsz' hrv_a hm_write

/-- Refinement-witness specialization of `step_cast_float_copy_indirect_float_simulation_mode`. -/
theorem step_cast_float_copy_indirect_float_simulation
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
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (huniq : ∀ la₁ la₂, (allocId, la₁) ∈ m.machine.memory.live.toList →
      (allocId, la₂) ∈ m.machine.memory.live.toList → la₁ = la₂)
    (hshape : StackScalarAllocShape (translateTy srcDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_src : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[srcIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hsc_src : ∀ v, get? s.frame.locals srcIdx = some (.init v) → ∃ sc, v = .scalar sc)
    (hdst_loc : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_copy_indirect_float_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) hid_lt hbase hfind huniq hshape hind_src hsc_src hdst_loc hptr8

/-- **Float-typed locals are never promoted into `allocMap`**: every `e ∈ allocMap` targets an
`IsPrimScalarTy` (`bool`, `char`, integer) local (`AllocMapRel.target_decl`), so any `f32`/`f64`
local (`ieeeFormatOfTy? decl.ty = some f`) is disjoint from `allocMap`. -/
theorem StateRelLM3_1.not_mem_allocMap_of_ieeeFormatOfTy?
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {idx : Local} {decl : LocalDecl} {f : IeeeFormat}
    (hdecl : get? body.localDecls idx = some decl)
    (hf : ieeeFormatOfTy? decl.ty = some f) :
    ∀ e ∈ allocMap, e.localIdx ≠ idx := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc, _⟩ := id hstate
  intro e he heq
  subst heq
  obtain ⟨d₀, hd₀, hprim⟩ := halloc.target_decl e he
  rw [hdecl] at hd₀; injection hd₀ with hd_eq; subst hd_eq
  rcases ieeeFormatOfTy?_kind hf with ⟨hk, _⟩ | ⟨hk, _⟩ <;>
    rcases hprim with hb | hb | ⟨_, hb⟩ | ⟨_, hb⟩ <;>
    (rw [hk] at hb; cases hb)

/-- **Deinitializing any unpromoted live local (`∀ e ∈ allocMap, e.localIdx ≠ srcIdx`)** —
whether `IsImmediateFrameLocal` or stack-allocated `LocalRel.indirect` — preserves
`StateRelLM3_1` when `annealEvalOperand (.Move ...)` replaces `tf.locals[srcIdx]` with
`.live (.immediate .uninit)`. (By contrast, moving out of a promoted `e ∈ allocMap` local would
break `AllocMapRel.local_alloc_sync`, which requires `tf.locals[e.localIdx]` to remain
`.indirect (stackAllocPlace e.allocId)`.) -/
theorem StateRelLM3_1.deinit_unpromoted_local
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {srcIdx : Local} {srcDecl : LocalDecl}
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hnot_src : ∀ e ∈ allocMap, e.localIdx ≠ srcIdx)
    (hlt_s : srcIdx < tf.locals.size) :
    StateRelLM3_1 body
      { s with frame := { s.frame with locals := s.frame.locals.set srcIdx .uninit } }
      { m with stack := ⟨#[deinitFrameLocal tf srcIdx hlt_s]⟩ }
      allocMap := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁; injection h₁ with htf; subst htf
  obtain ⟨_, mls_s, _, _, _, _, hmls_s_eq, hloc_s⟩ := hfr.lookup_local hdecl_src
  have hnew_s : LocalRelLM3_1 m.machine allocMap srcDecl body.layouts .uninit
      { tf.locals[srcIdx]'hlt_s with value := .live (.immediate .uninit) } :=
    .base (.immediate .uninit .uninit (tf.locals[srcIdx]'hlt_s).layout
      (by rw [hmls_s_eq]; exact hloc_s.cachedLayout_eq)
      (Or.inl ⟨rfl, rfl⟩))
  have hfr' := hfr.update_local hdecl_src .uninit (.live (.immediate .uninit)) hnew_s
  refine .mk (deinitFrameLocal tf srcIdx hlt_s) rfl hretCont hretPlace hfr'
    hcal hstack hprot hcaller hbor ?_ ?_
  · refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro tf' htf' e he
    injection htf' with h₁; injection h₁ with h₂; subst h₂
    have hne_s : srcIdx ≠ e.localIdx := Ne.symm (hnot_src e he)
    obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync tf hframes e he
    have hget_ne :
        get? (s.frame.locals.set srcIdx .uninit) e.localIdx =
          get? s.frame.locals e.localIdx := by
      rw [get?_eq_getElem?, List.getElem?_set_ne hne_s, ← get?_eq_getElem?]
    refine ⟨fun slot' hslot' hne_d => ?_, fun hdead' => ?_⟩
    · dsimp only [] at hslot'
      rw [hget_ne] at hslot'
      obtain ⟨⟨lay, hlay⟩, hsc, hshape⟩ := hlive_e slot' hslot' hne_d
      refine ⟨⟨lay, ?_⟩, hsc, hshape⟩
      dsimp only [deinitFrameLocal]
      rw [Array.getElem?_set_ne _ hne_s]
      exact hlay
    · dsimp only [] at hdead'
      rw [hget_ne] at hdead'
      exact hdead_e hdead'
  · apply MemoryAllocDisjoint.mono_immediate hdisj
    intro k
    by_cases hk : k = srcIdx
    · subst hk
      right
      refine ⟨.uninit, (tf.locals[k]'hlt_s).layout, ?_⟩
      dsimp only [deinitFrameLocal]
      rw [Array.getElem?_set_self]
    · left
      dsimp only [deinitFrameLocal]
      rw [Array.getElem?_set_ne _ (Ne.symm hk)]

/-- **Move-operand real-step simulation from an unpromoted stack-allocated `LocalRel.indirect`
local** (`_d = move _s as T` in either NaN mode, e.g. force-allocated `f32` / `f64` or unpromoted
integer locals where `∀ e ∈ allocMap, e.localIdx ≠ srcIdx`):
* `annealEvalOperand (.Move ...)` replaces `tf.locals[srcIdx]` with `.live (.immediate .uninit)`
  while returning `.indirect (stackAllocPlace allocId)`, which `Cast.cast` then reads from
  `m.machine.memory` (`StepRelLM3_1.ub` if `_s` was `.uninit`, normal lockstep if initialized);
* handles **both** distinct destinations (`dstIdx ≠ srcIdx`, immediate or promoted in `allocMap`)
  and self-moves (`dstIdx = srcIdx`, where `_s` transitions cleanly from `.indirect` to
  `.immediate` before `annealWriteImmediate` writes the cast result!). -/
theorem step_cast_float_move_indirect_float_simulation_mode
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
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (huniq : ∀ la₁ la₂, (allocId, la₁) ∈ m.machine.memory.live.toList →
      (allocId, la₂) ∈ m.machine.memory.live.toList → la₁ = la₂)
    (hshape : StackScalarAllocShape (translateTy srcDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_src : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[srcIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hnot_src : ∀ e ∈ allocMap, e.localIdx ≠ srcIdx)
    (hsc_src : ∀ v, get? s.frame.locals srcIdx = some (.init v) → ∃ sc, v = .scalar sc)
    (hdst_loc : dstIdx ≠ srcIdx → ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨lay_0, hlay_0⟩ := hind_src tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
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
  obtain ⟨slot_s, mls_s, hlt_af_s, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  let tfc := deinitFrameLocal tfb srcIdx hlt_sb
  have hdst_tfc : IsImmediateFrameLocal tfc dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx) := by
    by_cases hds : dstIdx = srcIdx
    · subst hds
      left
      intro mls hmls mp hmp
      dsimp only [tfc, deinitFrameLocal] at hmls
      rw [Array.getElem?_set_self] at hmls
      injection hmls with hm
      rw [← hm] at hmp
      cases hmp
    · rcases hdst_loc hds tf hframes with himm_d | hed
      · exact Or.inl (((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb)
      · exact Or.inr hed
  have hlay_tfa : ∃ lay_s, tfa.locals[srcIdx]? =
      some ⟨.live (.indirect (stackAllocPlace allocId)), lay_s⟩ := by
    dsimp [tfa, cacheFrameLocalLayout]
    rw [Array.getElem?_set]
    by_cases hds : dstIdx = srcIdx
    · subst hds
      simp only [↓reduceIte, Array.getElem?_eq_getElem hlt_d] at hlay_0 ⊢
      injection hlay_0 with hm0
      rw [hm0]
      exact ⟨_, rfl⟩
    · simp only [hds, ↓reduceIte]
      exact ⟨lay_0, hlay_0⟩
  obtain ⟨lay_s, hlay_s⟩ := hlay_tfa
  have hmls_s_ind : mls_s = ⟨.live (.indirect (stackAllocPlace allocId)), lay_s⟩ := by
    rw [hmls_s] at hlay_s; exact Option.some.inj hlay_s
  have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
      ⟨.live (.indirect (stackAllocPlace allocId)), lay_s⟩ := by
    rw [hmls_s_eq]; exact hmls_s_ind
  have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
    (known := none) rfl hlt_sa hdecl_src hmls_s' (by rw [hmls_s_ind] at hcache_s; exact hcache_s)
  let dummyEntry : AllocMapEntry :=
    { tag := 0, localIdx := srcIdx, allocId := allocId, perm := .active }
  have hmls_dummy : mls_s = ⟨.live (.indirect (stackAllocPlace dummyEntry.allocId)), lay_s⟩ :=
    hmls_s_ind
  obtain ⟨hun_s, hsc_s⟩ := hloc_s.indirect_stackAllocPlace_spec (e := dummyEntry)
    hmls_dummy hbase hfind huniq (hsig.src_scalar.size_ne_zero body.layouts)
  have hread_mem := annealReadMemoryPlace_floatCastScalar_zero_offset_eq hsig.src_scalar
    hid_lt hbase hfind hshape.byteSize_eq
    (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tfc]⟩ })
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ := rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  cases hss : slot_s with
  | dead =>
    have hnd : slot_s ≠ .dead := by
      cases hloc_s with
      | rawPtr _ _ _ _ _ _ _ _ => cases hmls_s_ind
      | base hb =>
        cases hb with
        | dead _ _ => cases hmls_s_ind
        | immediate _ _ _ _ _ => cases hmls_s_ind
        | indirect _ _ _ _ hne _ => exact hne
    exact absurd hss hnd
  | uninit =>
    obtain ⟨_, hread_err⟩ := hshape.uninit_readScalar_err (hun_s hss) false
    have hri_err : annealReadImmediate
        ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfc]⟩ } =
        .error (.undefinedBehavior "read of uninitialized memory")
          { m with stack := ⟨#[tfc]⟩ } := by
      rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
        hread_mem, hread_err]
    have hcast_err := cast_floatCast_of_readImmediate_err body.layouts nondet chooseNaN hsig
      (.indirect (stackAllocPlace allocId)) (.local 0 dstIdx none tf.localsIdentity) hri_err
    rw [← hdstT] at hcast_err
    have ha_ub : evalStmt s
        ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s, hss]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfc]⟩ },
          .error (.undefinedBehavior "read of uninitialized memory")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  | init vs =>
    obtain ⟨sc, rfl⟩ := hsc_src vs (hss ▸ hslot_s)
    obtain ⟨hsz, _, _, msc, hrel, hread_ok⟩ := hsc_s sc hss
    have hri_ok : annealReadImmediate
        ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfc]⟩ } =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfc]⟩ } := by
      rw [annealReadImmediate_indirect_floatCastScalar_eq hsig.src_scalar, stackAllocPlace,
        hread_mem, hread_ok]
      dsimp only []
      rw [hsig.src_scalar.validateScalar_true msc]
      rfl
    have hcast_red := cast_floatCast_of_readImmediate_scalar body.layouts nondet chooseNaN hsig
      (.indirect (stackAllocPlace allocId)) (.local 0 dstIdx none tf.localsIdentity)
      (.fromScalarInt msc) hri_ok
    obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
      (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
      (fun h => hagree h sc (hss ▸ hslot_s)) (.local 0 dstIdx none tf.localsIdentity)
    have hcast_ind :
        Miri.Interpreter.Cast.cast (annealCastHooksFloat body.layouts nondet chooseNaN) () 16
          ⟨.indirect (stackAllocPlace allocId), translateTy srcDecl.ty body.layouts⟩
          (translateCastKind kind) (encodeTyId castTy)
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfc]⟩ } =
        annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfc]⟩ } := by
      rw [hdstT]; exact hcast_red.trans (congrFun hcast _)
    rw [← hdstT] at hsz'
    have hstate_mid := hstate_b.deinit_unpromoted_local rfl hdecl_src hnot_src hlt_sb
    have hrv_a : evalRvalue s.frame.locals (.cast kind (.move ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts =
        .ok (.scalar sc') (s.frame.locals.set srcIdx .uninit) s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) s.memory.borrows
          s.memory.globals body.layouts s.memory.callerLocals body.localDecls
          s.memory.callStack = .ok (.scalar sc) (s.frame.locals.set srcIdx .uninit) := by
        unfold evalOperand; dsimp only []; rw [hslot_s, hss, set?_eq_some_set hlt_af_s]
      rw [hop]; dsimp only []; rw [operandTy_move_local hdecl_src, hev]
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfc]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_ind]
    exact finish_write_anyLocal_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_mid rfl hbb hstmt hdecl_dst hdst_scalar hdst_tfc hrel' hsz' hrv_a hm_write

/-- Refinement-witness specialization of `step_cast_float_move_indirect_float_simulation_mode`. -/
theorem step_cast_float_move_indirect_float_simulation
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
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (huniq : ∀ la₁ la₂, (allocId, la₁) ∈ m.machine.memory.live.toList →
      (allocId, la₂) ∈ m.machine.memory.live.toList → la₁ = la₂)
    (hshape : StackScalarAllocShape (translateTy srcDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_src : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[srcIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hnot_src : ∀ e ∈ allocMap, e.localIdx ≠ srcIdx)
    (hsc_src : ∀ v, get? s.frame.locals srcIdx = some (.init v) → ∃ sc, v = .scalar sc)
    (hdst_loc : dstIdx ≠ srcIdx → ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∨ (∃ ed ∈ allocMap, ed.localIdx = dstIdx))
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_move_indirect_float_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) hid_lt hbase hfind huniq hshape hind_src hnot_src hsc_src
    hdst_loc hptr8

private theorem float_list_filter_ne_find? {β : Type}
    (l : List (Miri.Memory.AllocId × β)) {id₀ id₁ : Miri.Memory.AllocId}
    (hne : id₀ ≠ id₁) :
    (l.filter (fun x => x.1 != id₀)).find? (fun x => x.1 == id₁) =
      l.find? (fun x => x.1 == id₁) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    by_cases hk : k = id₁
    · subst hk
      have hne' : (k != id₀) = true := bne_iff_ne.mpr (Ne.symm hne)
      simp [List.filter, List.find?, hne']
    · have hk' : (k == id₁) = false := beq_false_of_ne hk
      by_cases hk0 : (k != id₀) = true
      · simp [List.filter, List.find?, hk0, hk', ih]
      · simp [List.filter, List.find?, hk0, hk', ih]

private theorem float_live_find_filter_push_ne {β : Type}
    (live : Array (Miri.Memory.AllocId × β))
    {id₀ id : Miri.Memory.AllocId} (hne : id₀ ≠ id) (newLa : β) :
    ((live.filter (fun x => x.1 != id₀)).push (id₀, newLa)).find? (fun x => x.1 == id) =
      live.find? (fun x => x.1 == id) := by
  rw [Array.find?_push, ← Array.find?_toList, Array.toList_filter,
    float_list_filter_ne_find? live.toList hne, Array.find?_toList]
  cases live.find? (fun x => x.1 == id) with
  | some _ => rfl
  | none => simp [beq_false_of_ne hne]

theorem IsFloatCastScalarTy.align_pow2_le_29 {ty : Ty} (hty : IsFloatCastScalarTy ty)
    (ly : LayoutTable) :
    (translateTy ty ly).layout.align.abi.pow2 ≤ 29 := by
  rcases hty with ⟨f, hf⟩ | ⟨t, ht⟩
  · rw [translateTy_of_ieeeFormatOfTy? hf ly]; cases f <;> decide
  · rw [translateTy_of_floatIntTargetOfTy? ht ly]
    cases t <;> rename_i w <;> cases w <;> decide

/-- Zero-offset memory write into a stack allocation for **any** `IsFloatCastScalarTy`
(`f32`, `f64`, and all 12 integer widths, extending `SimLM3_1.annealWriteMemoryPlace_zero_offset_scalar_ok`
beyond `IsPrimScalarTy` to floats). -/
theorem annealWriteMemoryPlace_floatCastScalar_zero_offset_ok
    {ty : Ty} {ly : LayoutTable} (hty : IsFloatCastScalarTy ty)
    {allocId : Miri.Memory.AllocId} {borTag : Miri.Memory.BorTag}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    {st : AnnealStepState}
    (hid : allocId.value.toNat < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : st.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hmut : localAlloc.allocation.mutability = .Mut)
    (hsz_eq : localAlloc.allocation.byteSize = (translateTy ty ly).layout.size)
    {msc : Miri.Memory.ScalarInt}
    (hmsc_sz : msc.size = (translateTy ty ly).layout.size)
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hw : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy ty ly).layout.size)
      (.fromScalarInt msc) localAlloc.allocation = .ok () alloc') :
    annealWriteMemoryPlace (.scalar (.fromScalarInt msc))
        ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId),
          some (.concrete allocId borTag)⟩, .none, none⟩
        (translateTy ty ly) st =
      .ok () { st with machine := { st.machine with
        memory := { st.machine.memory with
          live := (st.machine.memory.live.filter (fun x => x.1 != allocId)).push
            (allocId, ⟨localAlloc.kind, alloc'⟩) } } } := by
  have hmeta :
      Miri.Memory.sizeAsI64 (translateTy ty ly).layout.size =
        .ok ((translateTy ty ly).layout.size.bytes.toNat : Int) ∧
      0 < (translateTy ty ly).layout.size.bytes.toNat ∧
      ((translateTy ty ly).layout.size.bytes.toNat : Int) < 2 ^ 63 := by
    rcases hty with ⟨f, hf⟩ | ⟨t, ht⟩
    · rw [translateTy_of_ieeeFormatOfTy? hf ly]
      cases f <;> exact ⟨rfl, by decide, by decide⟩
    · rw [translateTy_of_floatIntTargetOfTy? ht ly]
      cases t <;> rename_i w <;> cases w <;> exact ⟨rfl, by decide, by decide⟩
  obtain ⟨hsz, hgt0, hlt63⟩ := hmeta
  have hinb : 0 + (translateTy ty ly).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat := by
    rw [Nat.zero_add, hsz_eq]; exact Nat.le_refl _
  have hchk := checkAndDerefPtr_live_inbounds_ok allocId borTag 0
    (translateTy ty ly).layout.size.bytes.toNat localAlloc .memoryAccess
    hid (by show 0 < 2 ^ 32; decide) hbase hfind hgt0 hlt63 hinb
  have hoff0_sz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
  rw [hoff0_sz, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at hchk
  have hset := Miri.Memory.MemoryState.setLiveAllocation_of_find
    st.machine.memory allocId localAlloc alloc' hfind
  have hsc_sz : ((Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).size !=
      (translateTy ty ly).layout.size) = false := by
    rw [Miri.Memory.Scalar.fromScalarInt_size, hmsc_sz, bne_self_eq_false]
  have hmut_bne : (localAlloc.allocation.mutability != Miri.Memory.Mutability.Mut) = false := by
    rw [hmut]; rfl
  exact annealWriteMemoryPlace_of_check_ok_scalar _ _ _ st allocId localAlloc _ _ alloc' _
    hsz hchk hmut_bne rfl hfind hsc_sz (hty.validateScalar_true msc) hw hset

/-- **Overwriting an unpromoted `LocalRel.indirect` stack local (`∀ e ∈ allocMap, e.localIdx ≠ dstIdx`)
preserves `StateRelLM3_1`**: covers force-allocated `f32`/`f64` destinations (where
`StateRelLM3_1.not_mem_allocMap_of_ieeeFormatOfTy?` discharges `hnot_dst` automatically) as well
as unpromoted indirect integer destinations. -/
theorem StateRelLM3_1.advance_write_unpromoted_indirect_scalar
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {dstIdx : Local} {dstDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_scalar : IsFloatCastScalarTy dstDecl.ty)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {slot_d : LocalSlot} (hslot_d : get? s.frame.locals dstIdx = some slot_d)
    {allocId : Miri.Memory.AllocId}
    {lay_d : Option Miri.Interpreter.LocalLayout}
    (hlay_d : tf.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay_d⟩)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) =
      some (allocId, localAlloc))
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel_sc : ScalarRel sc msc)
    (hsz_dst : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hshape_alloc' : StackScalarAllocShape (translateSizeBytes sc.sizeBytes) alloc')
    (hinit_alloc' : alloc'.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) = .ok (.ok ()))
    (hread_alloc' : alloc'.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
      .ok (.fromScalarInt msc)) :
    StateRelLM3_1 body
      (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar sc))) s.memory)
      { stack := ⟨#[{ tf with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }]⟩
        machine := { m.machine with
          memory := { m.machine.memory with
            live := (m.machine.memory.live.filter (fun x => x.1 != allocId)).push
              (allocId, ⟨localAlloc.kind, alloc'⟩) } } }
      allocMap := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  let newLive := (m.machine.memory.live.filter (fun x => x.1 != allocId)).push
    (allocId, ⟨localAlloc.kind, alloc'⟩)
  let newMem : AnnealMemory := { m.machine.memory with live := newLive }
  let mach' : AnnealMachine := { m.machine with memory := newMem }
  have hset_mem : m.machine.memory.setLiveAllocation allocId alloc' = .ok newMem :=
    Miri.Memory.MemoryState.setLiveAllocation_of_find m.machine.memory allocId localAlloc
      alloc' hfind_la
  have hpow_d := hdst_scalar.align_pow2_le_29 body.layouts
  obtain ⟨hnb, hnc⟩ := hdst_scalar.not_bool_char
  have hlt_af_d : dstIdx < s.frame.locals.length := by
    cases h : s.frame.locals[dstIdx]? with
    | none => rw [get?_eq_getElem?, h] at hslot_d; cases hslot_d
    | some _ => exact (List.getElem?_eq_some_iff.mp h).1
  have hloc_d0 := hfr.locals_rel dstIdx dstDecl slot_d
    ⟨.live (.indirect (stackAllocPlace allocId)), lay_d⟩ hdecl_dst hslot_d hlay_d
  have hnew_mp : MemPlaceRel mach' dstDecl.ty body.layouts (some (.scalar sc))
      (stackAllocPlace allocId) := by
    refine .mk allocId Miri.Memory.BorTag.one (annealStackBaseAddr allocId)
      Miri.ABI.Size.ZERO ⟨localAlloc.kind, alloc'⟩
      rfl rfl rfl ?_ hbase ?_ ?_ hshape_alloc'.mutability_eq ?_ ?_ ?_ ?_ ?_
      (fun _ _ _ _ hs => nomatch hs)
    · exact Array.mem_toList_iff.mpr (Array.mem_push_self ..)
    · simp only [Miri.ABI.Size.ZERO, UInt64.toNat_zero, Nat.add_zero]
      exact (annealStackBaseAddr allocId).toBitVec.isLt
    · simp [stackAllocPlace, Miri.ABI.Size.ZERO]
    · exact annealStackBaseAddr_isAligned allocId _ hpow_d
    · simp [Miri.ABI.Size.ZERO, hshape_alloc'.byteSize_eq, hsz_dst]
    · intro h; cases h
    · intros; rw [hsz_dst]; exact hinit_alloc'
    · intro sc' hs'
      injection hs' with hv
      injection hv with hsc_eq
      subst hsc_eq
      exact ⟨hsz_dst, fun h => absurd h hnb, fun h => absurd h hnc,
        msc, hrel_sc, hsz_dst ▸ hread_alloc'⟩
  have hnew_d : LocalRelLM3_1 mach' allocMap dstDecl body.layouts (.init (.scalar sc))
      ⟨.live (.indirect (stackAllocPlace allocId)), lay_d⟩ :=
    .base (.indirect (.init (.scalar sc)) (stackAllocPlace allocId) lay_d
      hloc_d0.cachedLayout_eq (by simp) hnew_mp)
  have hfr' : FrameRelLM3_1 body mach' allocMap
      { s.frame with locals := s.frame.locals.set dstIdx (.init (.scalar sc)) } tf := by
    refine ⟨hfr.body_eq, hfr.location_eq, by rw [List.length_set, hfr.af_locals_len],
      hfr.mf_locals_size, ?_⟩
    intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    by_cases h_eq : dstIdx = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af_d, Option.some.injEq] at hslot_i
      have hdecl_eq : decl_i = dstDecl := by
        rw [hdecl_dst] at hdecl_i; exact Option.some.inj hdecl_i.symm
      have hmls_eq : mls_i = ⟨.live (.indirect (stackAllocPlace allocId)), lay_d⟩ := by
        rw [hlay_d] at hmls_i; exact Option.some.inj hmls_i.symm
      subst hdecl_eq hslot_i hmls_eq
      exact hnew_d
    · simp only [h_eq, ↓reduceIte] at hslot_i
      rw [← get?_eq_getElem?] at hslot_i
      have hloc_i := hfr.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
      apply hloc_i.of_setLiveAllocation_ne hfind_la hset_mem
      intro mp hv
      have hmls_ind : tf.locals[i]? = some ⟨.live (.indirect mp), mls_i.layout⟩ := by
        rcases mls_i with ⟨v0, l0⟩; dsimp only at hv; subst hv; exact hmls_i
      have hd := hdisj dstIdx i (stackAllocPlace allocId) mp lay_d mls_i.layout h_eq
        hlay_d hmls_ind
      exact fun heq => hd (by simpa [stackAllocPlace, Option.bind,
        Miri.Memory.Provenance.getAllocId] using heq.symm)
  have halloc_ne : ∀ x ∈ allocMap, allocId ≠ x.allocId := by
    intro x hx ha_eq
    have hx_ne : dstIdx ≠ x.localIdx := Ne.symm (hnot_dst x hx)
    obtain ⟨hlive_x, hdead_x⟩ := halloc.local_alloc_sync tf hframes x hx
    obtain ⟨_, _, _, _, hslot_x, _, _, _⟩ := hfr.lookup_local
      (Classical.choose_spec (halloc.target_decl x hx)).1
    by_cases hxd : get? s.frame.locals x.localIdx = some .dead
    · rw [hslot_x] at hxd; injection hxd with hxd'
      have hnone := hdead_x (hslot_x.trans (congrArg some hxd'))
      rw [← ha_eq, hfind_la] at hnone; cases hnone
    · have hsx_ne : _ ≠ LocalSlot.dead := fun h => hxd (hslot_x.trans (congrArg some h))
      obtain ⟨⟨lay_x, hlay_x⟩, _, _⟩ := hlive_x _ hslot_x hsx_ne
      have hd := hdisj dstIdx x.localIdx (stackAllocPlace allocId) (stackAllocPlace x.allocId)
        lay_d lay_x hx_ne hlay_d hlay_x
      exact hd (by simp [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ha_eq])
  refine .mk _ rfl hretCont hretPlace hfr'.advance hcal hstack hprot hcaller hbor ?_ hdisj
  refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
    halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, ?_, ?_⟩
  · intro x hx la₁ la₂ hla₁ hla₂
    have ha_ne : x.allocId ≠ allocId := (halloc_ne x hx).symm
    dsimp only [] at hla₁ hla₂
    simp only [Array.toList_push, List.mem_append, List.mem_singleton,
      Array.toList_filter, List.mem_filter] at hla₁ hla₂
    rcases hla₁ with ⟨hl₁, _⟩ | h1
    · rcases hla₂ with ⟨hl₂, _⟩ | h2
      · exact halloc.live_key_unique x hx la₁ la₂ hl₁ hl₂
      · exact absurd (Prod.mk.inj h2).1 ha_ne
    · exact absurd (Prod.mk.inj h1).1 ha_ne
  · intro tf' htf' x hx
    injection htf' with h₁; injection h₁ with h₂; subst h₂
    have hx_ne : x.localIdx ≠ dstIdx := hnot_dst x hx
    have ha_ne : allocId ≠ x.allocId := halloc_ne x hx
    obtain ⟨hlive_x, hdead_x⟩ := halloc.local_alloc_sync tf hframes x hx
    have hget_ne :
        get? (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar sc))) s.memory).frame.locals
          x.localIdx = get? s.frame.locals x.localIdx := by
      dsimp only [advanceStmt]
      rw [get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hx_ne), ← get?_eq_getElem?]
    have hfind_ne := float_live_find_filter_push_ne m.machine.memory.live ha_ne
      (⟨localAlloc.kind, alloc'⟩ : Miri.Memory.LocalAllocation AnnealProv
        (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind)
    refine ⟨fun slot' hslot' hne_d => ?_, fun hdead' => ?_⟩
    · rw [hget_ne] at hslot'
      obtain ⟨⟨lay_x, hlay_x⟩, hsc_x, hsh_x⟩ := hlive_x slot' hslot' hne_d
      refine ⟨⟨lay_x, hlay_x⟩, hsc_x, fun decl_x hdecl_x => ?_⟩
      obtain ⟨la_x, hf_x, hk_x, hal_x, hs_x⟩ := hsh_x decl_x hdecl_x
      exact ⟨la_x, hfind_ne.trans hf_x, hk_x, hal_x, hs_x⟩
    · rw [hget_ne] at hdead'
      exact hfind_ne.trans (hdead_x hdead')

/-- Post-operand write finisher for any unpromoted stack-allocated `LocalRel.indirect`
destination `dstIdx` (`∀ e ∈ allocMap, e.localIdx ≠ dstIdx`). -/
theorem finish_write_unpromoted_indirect_from_mid_hooks
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
    (hdst_scalar : IsFloatCastScalarTy dstDecl.ty)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {allocId : Miri.Memory.AllocId}
    {lay_d : Option Miri.Interpreter.LocalLayout}
    (hlay_d : tf_mid.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay_d⟩)
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    {sc' : MirAst.ScalarInt} {msc' : Miri.Memory.ScalarInt}
    (hrel' : ScalarRel sc' msc')
    (hsz' : (translateTy dstDecl.ty body.layouts).layout.size = translateSizeBytes sc'.sizeBytes)
    (hrv_anneal : evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
      .ok (.scalar sc') s_mid.frame.locals s.memory)
    (hm_write : Miri.Interpreter.Step.evalStatement
        hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tf_mid]⟩ }) :
    StepRelLM3_1 body m allocMap
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
      (Miri.Interpreter.Step.step hooks () m) := by
  have hfr_m := hstate_mid.frame_rel_singleton rfl
  obtain ⟨_, _, _, _, _, _, hstack_m, hprot_m, _, hbor_m, _, _⟩ := id hstate_mid
  obtain ⟨slot_dm, mls_dm, hlt_af_dm, _, hslot_dm, hmls_dm, _, hloc_dm⟩ :=
    hfr_m.lookup_local hdecl_dst
  have hs_mem : s_mid.memory = s.memory := by rw [hs_frame_eq]
  have hb_eq : s_mid.frame.blockIdx = s.frame.blockIdx := by rw [hs_frame_eq]
  have hsi_eq : s_mid.frame.stmtIdx = s.frame.stmtIdx := by rw [hs_frame_eq]
  have hsd_ne_dead : slot_dm ≠ .dead := by
    intro hdead; subst hdead
    have hmd_dead : mls_dm.value = .dead := by
      cases hloc_dm with
      | base hb =>
        cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
        | indirect _ _ _ _ hne _ => exact absurd rfl hne
    rw [hlay_d] at hmls_dm; injection hmls_dm with hm_eq; subst hm_eq
    cases hmd_dead
  have hshape_sc : StackScalarAllocShape (translateSizeBytes sc'.sizeBytes)
      localAlloc.allocation := hsz' ▸ hshape_la
  obtain ⟨alloc', hw_alloc, _, hshape_alloc', hinit_alloc', hread_alloc'⟩ :=
    hshape_sc.writeScalar_readScalar hrel'
  have hmsc_sz : msc'.size = (translateTy dstDecl.ty body.layouts).layout.size := by
    rw [hrel'.size_eq, ← hsz']
  have hw_alloc_lay : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO
        (translateTy dstDecl.ty body.layouts).layout.size)
      (.fromScalarInt msc') localAlloc.allocation = .ok () alloc' := by
    rw [← hmsc_sz]; exact hw_alloc
  have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hlay_d
  have hw_ind := annealWriteImmediate_indirect
    (val := .scalar (.fromScalarInt msc'))
    (m := { m with stack := ⟨#[tf_mid]⟩ }) (id0 := tf.localsIdentity)
    (dstLay := translateTy dstDecl.ty body.layouts) rfl hget_dm
  have hw_m := annealWriteMemoryPlace_floatCastScalar_zero_offset_ok hdst_scalar hid_lt hbase
    hfind_la hshape_la.mutability_eq hshape_la.byteSize_eq hmsc_sz hw_alloc_lay
    (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tf_mid]⟩ })
  have hm_ok : Miri.Interpreter.Step.evalStatement
      hooks ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      ({ stack := ⟨#[tf_mid]⟩
         machine := { m.machine with
           memory := { m.machine.memory with
             live := (m.machine.memory.live.filter (fun x => x.1 != allocId)).push
               (allocId, ⟨localAlloc.kind, alloc'⟩) } } }, .ok ()) := by
    rw [hm_write]; unfold Miri.Interpreter.runRvalue
    rw [hw_ind, stackAllocPlace, hw_m]
  have hloc_mid : tf_mid.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
    have hl := hfr_m.location_eq; rw [hb_eq, hsi_eq] at hl; exact hl
  rw [miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc_mid]
  have hbor_s : s.memory.borrows = allocMap.map AllocMapEntry.toBorrowEntry := by
    rw [← hs_mem]; exact hbor_m
  have hprot_s : s.memory.activeProtectors = .nil := by
    rw [← hs_mem]; exact hprot_m
  have hstack_s : s.memory.callStack = .nil := by
    rw [← hs_mem]; exact hstack_m
  have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor_s dstIdx none hnot_dst
  have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s_mid (s_mid.frame.locals.set dstIdx (.init (.scalar sc')))
        s_mid.memory) := by
    have hadv_eq :
        advanceStmt s (s_mid.frame.locals.set dstIdx (.init (.scalar sc'))) s.memory =
        advanceStmt s_mid (s_mid.frame.locals.set dstIdx (.init (.scalar sc'))) s_mid.memory := by
      rw [hs_frame_eq]; rfl
    rw [← hadv_eq]
    unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hstack_s, hslot_dm]
    cases slot_dm with
    | dead => exact absurd rfl hsd_ne_dead
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
  have hstep_rel := hstate_mid.advance_write_unpromoted_indirect_scalar rfl hdecl_dst hdst_scalar
    hnot_dst hslot_dm hlay_d hbase hfind_la hrel' hsz' hshape_alloc' hinit_alloc' hread_alloc'
  rw [hb_eq, hsi_eq] at hstep_rel
  exact hstep_rel

/-- **Constant-operand real-step simulation into a stack-allocated (`LocalRel.indirect`)
unpromoted destination `_d`** (in particular force-allocated `f32`/`f64` destinations, where
`StateRelLM3_1.not_mem_allocMap_of_ieeeFormatOfTy?` discharges `hnot_dst` automatically). -/
theorem step_cast_float_constant_indirect_dst_simulation_mode
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
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨lay_0, hlay_0⟩ := hind_dst tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
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
  have hlay_tfa : tfa.locals[dstIdx]? =
      some ⟨.live (.indirect (stackAllocPlace allocId)),
        some (translateTy dstDecl.ty body.layouts)⟩ := by
    dsimp [tfa, cacheFrameLocalLayout]
    rw [Array.getElem?_set_self hlt_d]
    rw [Array.getElem?_eq_getElem hlt_d] at hlay_0
    injection hlay_0 with hm0
    rw [hm0]
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
    rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]; dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl, hev]
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tfa]⟩ } := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  exact finish_write_unpromoted_indirect_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
    hstate_a rfl hbb hstmt hdecl_dst hdst_scalar hnot_dst hlay_tfa hid_lt hbase hfind_la hshape_la
    hrel' hsz' hrv_a hm_write

/-- Refinement-witness specialization of `step_cast_float_constant_indirect_dst_simulation_mode`. -/
theorem step_cast_float_constant_indirect_dst_simulation
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
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_constant_indirect_dst_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hsig hdst_ty hval hsz hcan hlaysz
    (fun h => absurd h (by decide)) hnot_dst hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-- **Copy-operand real-step simulation into a stack-allocated (`LocalRel.indirect`) unpromoted
destination `_d`** from an immediate source `_s` (`_d = copy _s as castTy`). -/
theorem step_cast_float_copy_indirect_dst_simulation_mode
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
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨lay_0, hlay_0⟩ := hind_dst tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
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
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := (himm_src tf hframes).cache_layout hlt_d _
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have hlay_tfb : ∃ lay_d, tfb.locals[dstIdx]? =
      some ⟨.live (.indirect (stackAllocPlace allocId)), lay_d⟩ := by
    have hlay_tfa : tfa.locals[dstIdx]? =
        some ⟨.live (.indirect (stackAllocPlace allocId)),
          some (translateTy dstDecl.ty body.layouts)⟩ := by
      dsimp [tfa, cacheFrameLocalLayout]
      rw [Array.getElem?_set_self hlt_d]
      rw [Array.getElem?_eq_getElem hlt_d] at hlay_0
      injection hlay_0 with hm0; rw [hm0]
    dsimp [tfb, cacheFrameLocalLayout]
    rw [Array.getElem?_set]
    by_cases hsd : srcIdx = dstIdx
    · subst hsd
      simp only [↓reduceIte]
      have hget : tfa.locals[srcIdx]'hlt_sa =
          ⟨.live (.indirect (stackAllocPlace allocId)),
            some (translateTy dstDecl.ty body.layouts)⟩ := by
        rw [Array.getElem?_eq_getElem hlt_sa] at hlay_tfa
        exact Option.some.inj hlay_tfa
      rw [hget]
      exact ⟨_, rfl⟩
    · simp only [hsd, ↓reduceIte]; exact ⟨_, hlay_tfa⟩
  obtain ⟨lay_db, hlay_db⟩ := hlay_tfb
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hcast_un := cast_floatCast_uninit body.layouts nondet chooseNaN hsig
      (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast_un
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_un]; rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · subst hss
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
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) s.frame.locals := by
        unfold evalOperand readProjectedValue; dsimp only []; rw [hslot_s]
      rw [hop]; dsimp only []; rw [operandTy_copy_local hdecl_src, hev]
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
    exact finish_write_unpromoted_indirect_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_b rfl hbb hstmt hdecl_dst hdst_scalar hnot_dst hlay_db hid_lt hbase hfind_la hshape_la
      hrel' hsz' hrv_a hm_write

/-- Refinement-witness specialization of `step_cast_float_copy_indirect_dst_simulation_mode`. -/
theorem step_cast_float_copy_indirect_dst_simulation
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
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_copy_indirect_dst_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) himm_src hnot_dst hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-- **Move-operand real-step simulation into a stack-allocated (`LocalRel.indirect`) unpromoted
destination `_d`** from an immediate source `_s` (`dstIdx ≠ srcIdx`; self-move `dstIdx = srcIdx`
is already covered by `step_cast_float_move_indirect_float_simulation`, where `annealEvalOperand`
transitions `_d` to `.immediate`). -/
theorem step_cast_float_move_indirect_dst_simulation_mode
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
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hne_ds : dstIdx ≠ srcIdx)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨lay_0, hlay_0⟩ := hind_dst tf hframes
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
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
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := (himm_src tf hframes).cache_layout hlt_d _
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have hlay_dc : (deinitFrameLocal tfb srcIdx hlt_sb).locals[dstIdx]? =
      some ⟨.live (.indirect (stackAllocPlace allocId)),
        some (translateTy dstDecl.ty body.layouts)⟩ := by
    dsimp [deinitFrameLocal]
    rw [Array.getElem?_set_ne _ hne_ds.symm]
    dsimp [tfb, cacheFrameLocalLayout]
    rw [Array.getElem?_set_ne _ hne_ds.symm]
    dsimp [tfa, cacheFrameLocalLayout]
    rw [Array.getElem?_set_self hlt_d]
    rw [Array.getElem?_eq_getElem hlt_d] at hlay_0
    injection hlay_0 with hm0; rw [hm0]
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ := rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hrel, hsz, hms⟩
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · subst hss
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue evalOperand; dsimp only []; rw [hslot_s]
    have hcast_un := cast_floatCast_uninit body.layouts nondet chooseNaN hsig
      (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast_un
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_un]; rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · subst hss
    obtain ⟨sc', msc', hev, hrel', hsz', hcast⟩ := floatCast_result_spec_mode body.layouts
      (floatPtrWidthOfLayouts_of_ptr8 hptr8) nondet chooseNaN hmode hsig hrel hsz
      (fun h => hagree h sc hslot_s) (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast hsz'
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have himm_sb := (himm_s_tfa).cache_layout hlt_sa (translateTy srcDecl.ty body.layouts)
    have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hslot_s (by simp) himm_sb hlt_sb
    obtain ⟨hlt_af_s, _⟩ := List.getElem?_eq_some_iff.mp
      (by rw [← get?_eq_getElem?]; exact hslot_s)
    have hrv_a : evalRvalue s.frame.locals (.cast kind (.move ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts =
        .ok (.scalar sc') (s.frame.locals.set srcIdx .uninit) s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) (s.frame.locals.set srcIdx .uninit) := by
        unfold evalOperand; dsimp only []; rw [hslot_s, set?_eq_some_set hlt_af_s]
      rw [hop]; dsimp only []; rw [operandTy_move_local hdecl_src, hev]
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast]
    exact finish_write_unpromoted_indirect_from_mid_hooks _ hframes hfr.body_eq hfr.location_eq
      hstate_mid rfl hbb hstmt hdecl_dst hdst_scalar hnot_dst hlay_dc hid_lt hbase hfind_la
      hshape_la hrel' hsz' hrv_a hm_write

/-- Refinement-witness specialization of `step_cast_float_move_indirect_dst_simulation_mode`. -/
theorem step_cast_float_move_indirect_dst_simulation
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
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hne_ds : dstIdx ≠ srcIdx)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_move_indirect_dst_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty
    (fun h => absurd h (by decide)) himm_src hne_ds hnot_dst hid_lt hbase hfind_la hshape_la
    hind_dst hptr8

/-- **`hnot_dst`-free indirect-destination simulation (`_d = const c as castTy`) for float
targets (`ieeeFormatOfTy? castTy = some dstFmt`)**: because `AllocMapRel.target_decl` restricts
`allocMap` to `IsPrimScalarTy` locals, `f32`/`f64` destinations (`floatToFloat` and `intToFloat`)
are automatically disjoint from `allocMap` (`StateRelLM3_1.not_mem_allocMap_of_ieeeFormatOfTy?`),
eliminating the `hnot_dst` premise completely. -/
theorem step_cast_float_constant_indirect_floatDst_simulation_mode
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
    {dstFmt : IeeeFormat} (hdst_fmt : ieeeFormatOfTy? castTy = some dstFmt)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hagree : nondet = false → FloatCastDetAgrees kind c.ty castTy sc.bits)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  have hdst_fmt' : ieeeFormatOfTy? dstDecl.ty = some dstFmt := by
    unfold ieeeFormatOfTy? at hdst_fmt ⊢; rw [hdst_ty]; exact hdst_fmt
  exact step_cast_float_constant_indirect_dst_simulation_mode hstate hphase nondet chooseNaN hmode
    hbb hstmt hdecl_dst hsig hdst_ty hval hsz hcan hlaysz hagree
    (hstate.not_mem_allocMap_of_ieeeFormatOfTy? hdecl_dst hdst_fmt')
    hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-- Refinement-witness specialization of `step_cast_float_constant_indirect_floatDst_simulation_mode`. -/
theorem step_cast_float_constant_indirect_floatDst_simulation
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
    {dstFmt : IeeeFormat} (hdst_fmt : ieeeFormatOfTy? castTy = some dstFmt)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_constant_indirect_floatDst_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hsig hdst_ty hdst_fmt hval hsz hcan hlaysz
    (fun h => absurd h (by decide)) hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-- **`hnot_dst`-free indirect-destination simulation (`_d = copy _s as castTy`) for float
targets (`ieeeFormatOfTy? castTy = some dstFmt`)**. -/
theorem step_cast_float_copy_indirect_floatDst_simulation_mode
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
    {dstFmt : IeeeFormat} (hdst_fmt : ieeeFormatOfTy? castTy = some dstFmt)
    (hagree : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  have hdst_fmt' : ieeeFormatOfTy? dstDecl.ty = some dstFmt := by
    unfold ieeeFormatOfTy? at hdst_fmt ⊢; rw [hdst_ty]; exact hdst_fmt
  exact step_cast_float_copy_indirect_dst_simulation_mode hstate hphase nondet chooseNaN hmode
    hbb hstmt hdecl_dst hdecl_src hsig hdst_ty hagree himm_src
    (hstate.not_mem_allocMap_of_ieeeFormatOfTy? hdecl_dst hdst_fmt')
    hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-- Refinement-witness specialization of `step_cast_float_copy_indirect_floatDst_simulation_mode`. -/
theorem step_cast_float_copy_indirect_floatDst_simulation
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
    {dstFmt : IeeeFormat} (hdst_fmt : ieeeFormatOfTy? castTy = some dstFmt)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_copy_indirect_floatDst_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty hdst_fmt
    (fun h => absurd h (by decide)) himm_src hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-- **`hnot_dst`-free indirect-destination simulation (`_d = move _s as castTy`) for float
targets (`ieeeFormatOfTy? castTy = some dstFmt`)**. -/
theorem step_cast_float_move_indirect_floatDst_simulation_mode
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
    {dstFmt : IeeeFormat} (hdst_fmt : ieeeFormatOfTy? castTy = some dstFmt)
    (hagree : nondet = false → ∀ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc)) →
      FloatCastDetAgrees kind srcDecl.ty castTy sc.bits)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hne_ds : dstIdx ≠ srcIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  have hdst_fmt' : ieeeFormatOfTy? dstDecl.ty = some dstFmt := by
    unfold ieeeFormatOfTy? at hdst_fmt ⊢; rw [hdst_ty]; exact hdst_fmt
  exact step_cast_float_move_indirect_dst_simulation_mode hstate hphase nondet chooseNaN hmode
    hbb hstmt hdecl_dst hdecl_src hsig hdst_ty hagree himm_src hne_ds
    (hstate.not_mem_allocMap_of_ieeeFormatOfTy? hdecl_dst hdst_fmt')
    hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-- Refinement-witness specialization of `step_cast_float_move_indirect_floatDst_simulation_mode`. -/
theorem step_cast_float_move_indirect_floatDst_simulation
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
    {dstFmt : IeeeFormat} (hdst_fmt : ieeeFormatOfTy? castTy = some dstFmt)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hne_ds : dstIdx ≠ srcIdx)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hid_lt : allocId.value.toNat < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hshape_la : StackScalarAllocShape (translateTy dstDecl.ty body.layouts).layout.size
      localAlloc.allocation)
    (hind_dst : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ lay, topFrame.locals[dstIdx]? = some ⟨.live (.indirect (stackAllocPlace allocId)), lay⟩)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksFloat body.localDecls body.layouts) () m) :=
  step_cast_float_move_indirect_floatDst_simulation_mode hstate hphase true annealChooseQuietedNaN
    (Or.inl ⟨rfl, rfl⟩) hbb hstmt hdecl_dst hdecl_src hsig hdst_ty hdst_fmt
    (fun h => absurd h (by decide)) himm_src hne_ds hid_lt hbase hfind_la hshape_la hind_dst hptr8

/-! ### Part 8c. Real-step characterization of deterministic NaN mode (`floatNondeterministic := false`) -/

/-- **Real-step deterministic NaN characterization (`_d = const c as dstTy`)** across **every**
`f32` / `f64` bit pattern (without assuming `FloatCastDetAgrees`):
* Anneal's `stepMirFn` steps normally, storing `evalFloatToFloatRoundTiesToEven src dst sc.bits`
  into `_d`.
* `lean-miri`'s `Step.step` under `annealStepHooksFloat ... false chooseNaN` steps normally,
  storing `preferredNaNBits dst` when `isNaNBits src sc.bits = true` and
  `evalFloatToFloatRoundTiesToEven src dst sc.bits` when `isNaNBits src sc.bits = false`.
In particular, the two machines agree bit-exactly iff `isNaNBits src sc.bits = false` or
`evalFloatToFloatRoundTiesToEven src dst sc.bits = preferredNaNBits dst`, and otherwise step
normally to distinct IEEE NaN payloads (`div_floatToFloat_deterministic_payloadNaN_step`). -/
theorem step_cast_floatToFloat_constant_deterministic_spec
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? c.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : sc.sizeBytes = src.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    let annealBits := evalFloatToFloatRoundTiesToEven src dst sc.bits
    let miriBits :=
      if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst else annealBits
    ∃ m' tf' msc',
      ScalarRel ⟨miriBits, dst.byteWidth⟩ msc' ∧
      stepMirFn body s =
        MirStepNode.step
          (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar ⟨annealBits, dst.byteWidth⟩)))
            s.memory) ∧
      Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc')))) := by
  dsimp only
  obtain ⟨tf, hframes, _, _, hfr, hcal, hstack, hprot, _, hbor, _, _⟩ := id hstate
  have himm_d := himm_dst tf hframes
  have hsig : FloatCastSig .floatToFloat c.ty castTy := .floatToFloat hsrc hdst
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts false
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.constant c) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hsd_ne : slot_d ≠ .dead := fun h => hlive_dst (h ▸ hslot_d)
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have hv_bytes : ValidScalarBytes sc.sizeBytes := hsz ▸ validScalarBytes_byteWidth src
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hv_bytes hcan
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
  obtain ⟨msc', hrel', hcast⟩ := cast_floatToFloat_deterministic_eq body.layouts chooseNaN
    hsrc hdst hrel hsz (.local 0 dstIdx none tf.localsIdentity)
  rw [← hdstT] at hcast
  have himm_d_tfa : IsImmediateFrameLocal tfa dstIdx := himm_d.cache_layout hlt_d _
  obtain ⟨slot_da, mls_da, _, hlt_da, hslot_da, hmls_da, _, hloc_da⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_dst
  have hsda_eq : slot_da = slot_d := by
    rw [hslot_d] at hslot_da; exact Option.some.inj hslot_da.symm
  subst slot_da
  have hold_imm : ∃ oldImm, mls_da.value = .live (.immediate oldImm) := by
    cases hloc_da with
    | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm_d_tfa _ hmls_da mp)
      | dead _ _ => exact absurd rfl hsd_ne
      | immediate _ oldImm _ _ _ => exact ⟨oldImm, rfl⟩
  obtain ⟨oldImm, hmd_imm⟩ := hold_imm
  have hda_live : tfa.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_da.layout⟩ := by
    rw [hmls_da]; rcases mls_da with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
  have hget_da := frame_getLocal_of_getElem? tfa dstIdx _ hda_live
  have hw_ok := annealWriteImmediate_live (val := .scalar (.fromScalarInt msc'))
    (m := { m with stack := ⟨#[tfa]⟩ }) (id0 := tf.localsIdentity)
    (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_da hget_da
  have hm_ok : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩) m =
      ({ m with stack := ⟨#[{ tfa with
          locals := tfa.locals.set dstIdx
            { tfa.locals[dstIdx]'hlt_da with value := .live (.immediate (.scalar (.fromScalarInt msc'))) }
            hlt_da }]⟩ }, .ok ()) := by
    rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
      show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast, hw_ok]
  have hloc_a : tfa.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
    (hstate_a.frame_rel_singleton rfl).location_eq
  have hm_step := miri_step_at_statement_ok
    (annealStepHooksFloat body.localDecls body.layouts false chooseNaN)
    hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl hloc_a
  have hnot_dst : ∀ d ∈ allocMap, d.localIdx ≠ dstIdx :=
    hstate_a.immediate_not_in_allocMap rfl hslot_d hsd_ne himm_d_tfa
  have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor dstIdx none hnot_dst
  have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.constant c) castTy) s.memory
      body.localDecls body.layouts =
      .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
        s.frame.locals s.memory := by
    rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]; dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl]
    simp only [evalFloatCast, hsrc, hdst, hsz, Nat.beq_refl]
  have ha_step : stepMirFn body s =
      MirStepNode.step
        (advanceStmt s
          (s.frame.locals.set dstIdx
            (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt; dsimp only []; rw [hrv_a]; dsimp only []; rw [hstack, hslot_d]
    cases slot_d with
    | dead => exact absurd rfl hsd_ne
    | uninit =>
      simp only [set?_eq_some_set hlt_af_d, length, List.length_nil, hprot, hbor_inv]
      congr 2; generalize s.memory = mem at hstack hprot ⊢
      cases mem; dsimp at hstack hprot ⊢; subst hstack hprot; rfl
    | init _ =>
      simp only [set?_eq_some_set hlt_af_d, length, List.length_nil, hprot, hbor_inv]
      congr 2; generalize s.memory = mem at hstack hprot ⊢
      cases mem; dsimp at hstack hprot ⊢; subst hstack hprot; rfl
  refine ⟨_, _, msc', hrel', ha_step, hm_step, rfl, ?_⟩
  simp [Array.getElem?_set_self]

/-- **Real-step deterministic NaN characterization (`_d = copy _s as dstTy`)** across **every**
initialized immediate `f32` / `f64` local `_s` (without assuming `FloatCastDetAgrees`):
* Anneal's `stepMirFn` steps normally, storing `evalFloatToFloatRoundTiesToEven src dst sc.bits`.
* `lean-miri`'s `Step.step` under `annealStepHooksFloat ... false chooseNaN` steps normally,
  storing `preferredNaNBits dst` when `isNaNBits src sc.bits = true` and
  `evalFloatToFloatRoundTiesToEven src dst sc.bits` when `isNaNBits src sc.bits = false`. -/
theorem step_cast_floatToFloat_copy_deterministic_spec
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    let annealBits := evalFloatToFloatRoundTiesToEven src dst sc.bits
    let miriBits :=
      if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst else annealBits
    ∃ m' tf' msc',
      ScalarRel ⟨miriBits, dst.byteWidth⟩ msc' ∧
      stepMirFn body s =
        MirStepNode.step
          (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar ⟨annealBits, dst.byteWidth⟩)))
            s.memory) ∧
      Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc')))) := by
  dsimp only
  obtain ⟨tf, hframes, _, _, hfr, hcal, hstack, hprot, _, hbor, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts false
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.copy ⟨srcIdx, .nil⟩) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, _, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hsd_ne : slot_d ≠ .dead := fun h => hlive_dst (h ▸ hslot_d)
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
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz_lay, hms⟩
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s
    injection hslot_s with hv_eq; injection hv_eq with hsc_eq; injection hsc_eq with hsc_eq'
    subst hsc_eq'
    have hsz : sc.sizeBytes = src.byteWidth :=
      sizeBytes_of_float_layout hrel.validBytes
        ((congrArg (·.layout.size) (translateTy_of_ieeeFormatOfTy? hsrc body.layouts)).symm.trans hsz_lay)
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    obtain ⟨msc', hrel', hcast⟩ := cast_floatToFloat_deterministic_eq body.layouts chooseNaN
      hsrc hdst hrel hsz (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast
    have himm_d_tfb : IsImmediateFrameLocal tfb dstIdx :=
      (himm_d.cache_layout hlt_d _).cache_layout hlt_sa _
    obtain ⟨slot_db, mls_db, _, hlt_db, hslot_db, hmls_db, _, hloc_db⟩ :=
      hstate_b.frame_rel_singleton rfl |>.lookup_local hdecl_dst
    have hsdb_eq : slot_db = slot_d := by
      rw [hslot_d] at hslot_db; exact Option.some.inj hslot_db.symm
    subst slot_db
    have hold_imm : ∃ oldImm, mls_db.value = .live (.immediate oldImm) := by
      cases hloc_db with
      | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
      | base hb =>
        cases hb with
        | indirect _ mp _ _ _ _ => exact absurd rfl (himm_d_tfb _ hmls_db mp)
        | dead _ _ => exact absurd rfl hsd_ne
        | immediate _ oldImm _ _ _ => exact ⟨oldImm, rfl⟩
    obtain ⟨oldImm, hmd_imm⟩ := hold_imm
    have hdb_live : tfb.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_db.layout⟩ := by
      rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
    have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_live
    have hw_ok := annealWriteImmediate_live (val := .scalar (.fromScalarInt msc'))
      (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
      (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
    have hm_ok : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[{ tfb with
            locals := tfb.locals.set dstIdx
              { tfb.locals[dstIdx]'hlt_db with value := .live (.immediate (.scalar (.fromScalarInt msc'))) }
              hlt_db }]⟩ }, .ok ()) := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast, hw_ok]
    have hloc_b : tfb.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
      (hstate_b.frame_rel_singleton rfl).location_eq
    have hm_step := miri_step_at_statement_ok
      (annealStepHooksFloat body.localDecls body.layouts false chooseNaN)
      hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl hloc_b
    have hnot_dst : ∀ d ∈ allocMap, d.localIdx ≠ dstIdx :=
      hstate_b.immediate_not_in_allocMap rfl hslot_d hsd_ne himm_d_tfb
    have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor dstIdx none hnot_dst
    have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts =
        .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
          s.frame.locals s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) s.frame.locals := by
        unfold evalOperand readProjectedValue; dsimp only []; rw [hinit_src]
      rw [hop]; dsimp only []; rw [operandTy_copy_local hdecl_src]
      simp only [evalFloatCast, hsrc, hdst, hsz]; cases src <;> rfl
    have ha_step : stepMirFn body s =
        MirStepNode.step
          (advanceStmt s
            (s.frame.locals.set dstIdx
              (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
            s.memory) := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]
      unfold evalStmt; dsimp only []; rw [hrv_a]; dsimp only []; rw [hstack, hslot_d]
      cases slot_d with
      | dead => exact absurd rfl hsd_ne
      | uninit =>
        simp only [set?_eq_some_set hlt_af_d, length, List.length_nil, hprot, hbor_inv]
        congr 2; generalize s.memory = mem at hstack hprot ⊢
        cases mem; dsimp at hstack hprot ⊢; subst hstack hprot; rfl
      | init _ =>
        simp only [set?_eq_some_set hlt_af_d, length, List.length_nil, hprot, hbor_inv]
        congr 2; generalize s.memory = mem at hstack hprot ⊢
        cases mem; dsimp at hstack hprot ⊢; subst hstack hprot; rfl
    refine ⟨_, _, msc', hrel', ha_step, hm_step, rfl, ?_⟩
    simp [Array.getElem?_set_self]

/-! ### Part 8c (cont.). Deterministic NaN mode as a simulation modulo NaN canonicalization

The `_deterministic_spec` theorems above pin only the destination value of each machine. The
theorems below upgrade them to full `StepRelLM3_1` simulations: `lean-miri`'s deterministic
step (`floatNondeterministic := false`, any `chooseNaN`) is simulated by the Anneal successor
that stores the **canonicalized** result (`preferredNaNBits dst` on NaN inputs, the trusted
conversion otherwise), while Anneal itself stores the trusted (payload-preserving) conversion.
Hence `lean-miri`'s deterministic mode is exactly Anneal with canonicalized NaN payloads, and
the two machines diverge on precisely the destination bits. -/

/-- **Value-split write finisher** (live immediate destination): like
`finish_write_immediate_from_mid_hooks`, but decoupling the value Anneal's `evalRvalue`
computes (`valA`) from the value `valM` that `lean-miri`'s write is related to. Anneal's
statement steps to the successor storing `valA`, and `lean-miri`'s `Step.step` is
`StepRelLM3_1`-simulated by the Anneal successor storing `valM`. -/
theorem finish_write_immediate_split_hooks
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
    (hlive_dst : get? s_mid.frame.locals dstIdx ≠ some .dead)
    {valA valM : Value} {newImm : Miri.Interpreter.Immediate AnnealProv}
    (hrv_anneal : evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
      .ok valA s_mid.frame.locals s.memory)
    (hm_write : Miri.Interpreter.Step.evalStatement hooks ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate newImm
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tf_mid]⟩ })
    (hnew_rel : ∀ cachedLay,
      (∀ l, cachedLay = some l → l = translateTy dstDecl.ty body.layouts) →
      LocalRelLM3_1 m.machine allocMap dstDecl body.layouts (.init valM)
        ⟨.live (.immediate newImm), cachedLay⟩) :
    evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
        MirStepNode.step (advanceStmt s (s_mid.frame.locals.set dstIdx (.init valA)) s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s_mid.frame.locals.set dstIdx (.init valM)) s.memory))
        (Miri.Interpreter.Step.step hooks () m) := by
  have hfr_m := hstate_mid.frame_rel_singleton rfl
  obtain ⟨_, _, _, _, _, hcal_m, hstack_m, hprot_m, hcaller_m, hbor_m, _, _⟩ := id hstate_mid
  obtain ⟨slot_dm, mls_dm, hlt_af_dm, hlt_dm, hslot_dm, hmls_dm, hmls_dm_eq, hloc_dm⟩ :=
    hfr_m.lookup_local hdecl_dst
  have hs_mem : s_mid.memory = s.memory := by rw [hs_frame_eq]
  have hb_eq : s_mid.frame.blockIdx = s.frame.blockIdx := by rw [hs_frame_eq]
  have hsi_eq : s_mid.frame.stmtIdx = s.frame.stmtIdx := by rw [hs_frame_eq]
  have hsd_ne : slot_dm ≠ .dead := fun h => hlive_dst (h ▸ hslot_dm)
  have hold_imm : ∃ oldImm, mls_dm.value = .live (.immediate oldImm) := by
    cases hloc_dm with
    | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst_mid _ hmls_dm mp)
      | dead _ _ => exact absurd rfl hsd_ne
      | immediate _ oldImm _ _ _ => exact ⟨oldImm, rfl⟩
  obtain ⟨oldImm, hmd_imm⟩ := hold_imm
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
  have hm_ok : Miri.Interpreter.Step.evalStatement hooks ()
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
  have hadv_eq : ∀ v : Value,
      advanceStmt s (s_mid.frame.locals.set dstIdx (.init v)) s.memory =
        advanceStmt s_mid (s_mid.frame.locals.set dstIdx (.init v)) s_mid.memory := by
    intro v; rw [hs_frame_eq]; rfl
  refine ⟨?_, ?_⟩
  · unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hstack_s, hslot_dm]
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
  · rw [miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc_mid, hadv_eq]
    refine .step _ _ ?_
    have hnew_d : LocalRelLM3_1 m.machine (allocMap.map id) dstDecl body.layouts (.init valM)
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

/-- `LocalRelLM3_1` for a freshly written float-cast scalar destination. -/
theorem floatCast_dst_localRel {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {dstDecl : LocalDecl} {layouts : LayoutTable} (hdst_scalar : IsFloatCastScalarTy dstDecl.ty)
    {sc' : MirAst.ScalarInt} {msc' : Miri.Memory.ScalarInt} (hrel' : ScalarRel sc' msc')
    (hsz' : (translateTy dstDecl.ty layouts).layout.size = translateSizeBytes sc'.sizeBytes)
    (cachedLay : Option Miri.Interpreter.LocalLayout)
    (hc : ∀ l, cachedLay = some l → l = translateTy dstDecl.ty layouts) :
    LocalRelLM3_1 mach allocMap dstDecl layouts (.init (.scalar sc'))
      ⟨.live (.immediate (.scalar (.fromScalarInt msc'))), cachedLay⟩ := by
  obtain ⟨hnb, hnc⟩ := hdst_scalar.not_bool_char
  exact .base (.immediate (.init (.scalar sc')) (.scalar (.fromScalarInt msc')) cachedLay hc
    (Or.inr ⟨.scalar sc', rfl,
      .scalar sc' msc' hrel' hsz' (fun h => absurd h hnb) (fun h => absurd h hnc)⟩))

/-- Destination layout size of a `floatToFloat` cast into `dst`. -/
theorem floatToFloat_dst_size {dstDecl : LocalDecl} {castTy : Ty} {dst : IeeeFormat}
    (layouts : LayoutTable) (hdst : ieeeFormatOfTy? castTy = some dst)
    (hdst_ty : dstDecl.ty.kind = castTy.kind) (bits : Nat) :
    (translateTy dstDecl.ty layouts).layout.size =
      translateSizeBytes (⟨bits, dst.byteWidth⟩ : MirAst.ScalarInt).sizeBytes := by
  have hdst' : ieeeFormatOfTy? dstDecl.ty = some dst := by
    unfold ieeeFormatOfTy? at hdst ⊢; rw [hdst_ty]; exact hdst
  rw [translateTy_of_ieeeFormatOfTy? hdst' layouts, translateSizeBytes_byteWidth,
    floatLayoutData_size]

/-- **Non-vacuity of the `hchoose` selector hypothesis**: every constant selector `pure i` with
`i < 4` is a valid state-preserving NaN selector on every candidate list `nanChoices` produces
(lengths `4` / `6`, `floatBits_nanChoices_nondet_list_eq`). -/
theorem chooseNaN_pure_valid (i : Nat) (hi : i < 4) :
    ∀ (st : AnnealStepState) (cs : List Miri.Interpreter.FloatBits), 4 ≤ cs.length →
      ∃ idx < cs.length,
        (fun (_ : Unit) (_ : List Miri.Interpreter.FloatBits) =>
          (pure i : Miri.Interpreter.RvalueM AnnealStepState Nat)) () cs st = .ok idx st :=
  fun _ _ hcs => ⟨i, by omega, rfl⟩

/-- The refinement witness `annealChooseQuietedNaN` (index `2`) is a valid NaN selector, so the
any-`chooseNaN` theorems specialize to it. -/
theorem annealChooseQuietedNaN_valid :
    ∀ (st : AnnealStepState) (cs : List Miri.Interpreter.FloatBits), 4 ≤ cs.length →
      ∃ idx < cs.length, annealChooseQuietedNaN () cs st = .ok idx st :=
  fun _ _ hcs => ⟨2, by omega, rfl⟩

/-- **Full NaN-choice refinement at the step level (`_d = copy _s as T`, `floatToFloat`)**:
for **either** NaN mode and **any** valid state-preserving `chooseNaN` selector (`hchoose`;
vacuous in deterministic mode, satisfied by every `pure i` with `i < 4`, in particular the
refinement witness `annealChooseQuietedNaN`), Anneal's `stepMirFn` stores the trusted conversion
while `lean-miri`'s `Step.step` is `StepRelLM3_1`-simulated by the **same** Anneal successor with
`_d` replaced by some `outBits` that equals the trusted conversion on non-NaN inputs and is a
`dst` NaN (exactly `preferredNaNBits dst` in deterministic mode) on NaN inputs: every
`lean-miri` NaN choice is an Anneal execution up to the NaN payload of `_d`. -/
theorem step_cast_floatToFloat_copy_nanChoice_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hchoose : nondet = true → ∀ (st : AnnealStepState) (cs : List Miri.Interpreter.FloatBits),
      4 ≤ cs.length → ∃ idx < cs.length, chooseNaN () cs st = .ok idx st)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    ∃ outBits, outBits < 2 ^ dst.width ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = false →
        outBits = evalFloatToFloatRoundTiesToEven src dst sc.bits) ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = true →
        Anneal.Mir.IeeeFloatCast.isNaNBits dst outBits = true ∧
          (nondet = false → outBits = preferredNaNBits dst)) ∧
    stepMirFn body s =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨outBits, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.copy ⟨srcIdx, .nil⟩) castTy span m
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
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz_lay, hms⟩
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s
    cases hslot_s
    have hsz : sc.sizeBytes = src.byteWidth :=
      sizeBytes_of_float_layout hrel.validBytes
        ((congrArg (·.layout.size) (translateTy_of_ieeeFormatOfTy? hsrc body.layouts)).symm.trans
          hsz_lay)
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    obtain ⟨outBits, hout_lt, msc', hrel', hnn, hn, hcast⟩ :=
      cast_floatToFloat_any_chooseNaN_spec body.layouts nondet chooseNaN hsrc hdst hrel hsz
        (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfb]⟩ }
        (fun hnd => hchoose hnd _)
    rw [← hdstT] at hcast
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
    have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy)
        s.memory body.localDecls body.layouts =
        .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
          s.frame.locals s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows
          s.memory.globals body.layouts s.memory.callerLocals body.localDecls
          s.memory.callStack = .ok (.scalar sc) s.frame.locals := by
        unfold evalOperand readProjectedValue; dsimp only []; rw [hinit_src]
      rw [hop]; dsimp only []; rw [operandTy_copy_local hdecl_src]
      simp only [evalFloatCast, hsrc, hdst, hsz]; cases src <;> rfl
    obtain ⟨hev, hsim⟩ := finish_write_immediate_split_hooks _ hframes hfr.body_eq
      hfr.location_eq hstate_b rfl hbb hstmt hdecl_dst
      ((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _) hlive_dst hrv_a hm_write
      (floatCast_dst_localRel hdst_scalar hrel'
        (floatToFloat_dst_size body.layouts hdst hdst_ty _))
    refine ⟨outBits, hout_lt, hnn, hn, ?_, hsim⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    exact hev

/-- **Full NaN-choice refinement at the step level (`_d = const c as T`, `floatToFloat`)**:
for **either** NaN mode and **any** valid state-preserving `chooseNaN` selector (`hchoose`;
vacuous in deterministic mode, satisfied by every `pure i` with `i < 4`, in particular the
refinement witness `annealChooseQuietedNaN`), Anneal's `stepMirFn` stores the trusted conversion
while `lean-miri`'s `Step.step` is `StepRelLM3_1`-simulated by the **same** Anneal successor with
`_d` replaced by some `outBits` that equals the trusted conversion on non-NaN inputs and is a
`dst` NaN (exactly `preferredNaNBits dst` in deterministic mode) on NaN inputs: every
`lean-miri` NaN choice is an Anneal execution up to the NaN payload of `_d`. -/
theorem step_cast_floatToFloat_constant_nanChoice_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hchoose : nondet = true → ∀ (st : AnnealStepState) (cs : List Miri.Interpreter.FloatBits),
      4 ≤ cs.length → ∃ idx < cs.length, chooseNaN () cs st = .ok idx st)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? c.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : sc.sizeBytes = src.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    ∃ outBits, outBits < 2 ^ dst.width ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = false →
        outBits = evalFloatToFloatRoundTiesToEven src dst sc.bits) ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = true →
        Anneal.Mir.IeeeFloatCast.isNaNBits dst outBits = true ∧
          (nondet = false → outBits = preferredNaNBits dst)) ∧
    stepMirFn body s =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨outBits, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have himm_d := himm_dst tf hframes
  have hsig : FloatCastSig .floatToFloat c.ty castTy := .floatToFloat hsrc hdst
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.constant c) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have hv_bytes : ValidScalarBytes sc.sizeBytes := hsz ▸ validScalarBytes_byteWidth src
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hv_bytes hcan
  have hsrc_ok : annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
      none { m with stack := ⟨#[tfa]⟩ } =
      .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } := by
    with_unfolding_all
      unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
      dsimp only
      rw [hval]
      simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
        EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        stack_currentFrame?_singleton { m with stack := ⟨#[tfa]⟩ }.stack tfa rfl,
        Option.isNone_some, Bool.false_eq_true, ↓reduceIte, htry,
        layoutOfEncodedTyId_floatCastScalar hsig.src_scalar body.layouts]
  obtain ⟨outBits, hout_lt, msc', hrel', hnn, hn, hcast⟩ :=
    cast_floatToFloat_any_chooseNaN_spec body.layouts nondet chooseNaN hsrc hdst hrel hsz
      (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfa]⟩ }
      (fun hnd => hchoose hnd _)
  rw [← hdstT] at hcast
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tfa]⟩ } := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
      show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
  have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.constant c) castTy) s.memory
      body.localDecls body.layouts =
      .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
        s.frame.locals s.memory := by
    rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]; dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl]
    simp only [evalFloatCast, hsrc, hdst, hsz, Nat.beq_refl]
  obtain ⟨hev, hsim⟩ := finish_write_immediate_split_hooks _ hframes hfr.body_eq
    hfr.location_eq hstate_a rfl hbb hstmt hdecl_dst (himm_d.cache_layout hlt_d _) hlive_dst
    hrv_a hm_write
    (floatCast_dst_localRel hdst_scalar hrel' (floatToFloat_dst_size body.layouts hdst hdst_ty _))
  refine ⟨outBits, hout_lt, hnn, hn, ?_, hsim⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  exact hev

/-- **Full NaN-choice refinement at the step level (`_d = move _s as T`, `floatToFloat`)**:
for **either** NaN mode and **any** valid state-preserving `chooseNaN` selector (`hchoose`;
vacuous in deterministic mode, satisfied by every `pure i` with `i < 4`, in particular the
refinement witness `annealChooseQuietedNaN`), Anneal's `stepMirFn` stores the trusted conversion
while `lean-miri`'s `Step.step` is `StepRelLM3_1`-simulated by the **same** Anneal successor with
`_d` replaced by some `outBits` that equals the trusted conversion on non-NaN inputs and is a
`dst` NaN (exactly `preferredNaNBits dst` in deterministic mode) on NaN inputs: every
`lean-miri` NaN choice is an Anneal execution up to the NaN payload of `_d`. -/
theorem step_cast_floatToFloat_move_nanChoice_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (hchoose : nondet = true → ∀ (st : AnnealStepState) (cs : List Miri.Interpreter.FloatBits),
      4 ≤ cs.length → ∃ idx < cs.length, chooseNaN () cs st = .ok idx st)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    ∃ outBits, outBits < 2 ^ dst.width ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = false →
        outBits = evalFloatToFloatRoundTiesToEven src dst sc.bits) ∧
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = true →
        Anneal.Mir.IeeeFloatCast.isNaNBits dst outBits = true ∧
          (nondet = false → outBits = preferredNaNBits dst)) ∧
    stepMirFn body s =
        MirStepNode.step (advanceStmt s ((s.frame.locals.set srcIdx .uninit).set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s ((s.frame.locals.set srcIdx .uninit).set dstIdx
          (.init (.scalar ⟨outBits, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.move ⟨srcIdx, .nil⟩) castTy span m
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
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz_lay, hms⟩
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s
    cases hslot_s
    have hsz : sc.sizeBytes = src.byteWidth :=
      sizeBytes_of_float_layout hrel.validBytes
        ((congrArg (·.layout.size) (translateTy_of_ieeeFormatOfTy? hsrc body.layouts)).symm.trans
          hsz_lay)
    obtain ⟨outBits, hout_lt, msc', hrel', hnn, hn, hcast⟩ :=
      cast_floatToFloat_any_chooseNaN_spec body.layouts nondet chooseNaN hsrc hdst hrel hsz
        (.local 0 dstIdx none tf.localsIdentity)
        { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } (fun hnd => hchoose hnd _)
    rw [← hdstT] at hcast
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have himm_sb := (himm_s.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)).cache_layout
      hlt_sa (translateTy srcDecl.ty body.layouts)
    have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hinit_src (by simp) himm_sb
      hlt_sb
    obtain ⟨hlt_af_s, _⟩ := List.getElem?_eq_some_iff.mp
      (by rw [← get?_eq_getElem?]; exact hinit_src)
    have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy)
        s.memory body.localDecls body.layouts =
        .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
          (s.frame.locals.set srcIdx .uninit) s.memory := by
      rw [evalRvalue_floatCast_eq hsig]
      unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) s.memory.borrows
          s.memory.globals body.layouts s.memory.callerLocals body.localDecls
          s.memory.callStack = .ok (.scalar sc) (s.frame.locals.set srcIdx .uninit) := by
        unfold evalOperand; dsimp only []; rw [hinit_src, set?_eq_some_set hlt_af_s]
      rw [hop]
      dsimp only []
      rw [operandTy_move_local hdecl_src]
      simp only [evalFloatCast, hsrc, hdst, hsz]; cases src <;> rfl
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
    have hlive_mid : get? (s.frame.locals.set srcIdx .uninit) dstIdx ≠ some .dead := by
      by_cases hds : srcIdx = dstIdx
      · subst hds
        rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_s]
        simp
      · rw [get?_eq_getElem?, List.getElem?_set_ne hds, ← get?_eq_getElem?]
        exact hlive_dst
    obtain ⟨hev, hsim⟩ := finish_write_immediate_split_hooks _ hframes hfr.body_eq
      hfr.location_eq hstate_mid rfl hbb hstmt hdecl_dst
      (((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb) hlive_mid
      hrv_a hm_write
      (floatCast_dst_localRel hdst_scalar hrel'
        (floatToFloat_dst_size body.layouts hdst hdst_ty _))
    refine ⟨outBits, hout_lt, hnn, hn, ?_, hsim⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    exact hev

/-- **Deterministic NaN mode = Anneal with canonicalized NaNs (`_d = copy _s as T`,
`floatToFloat`)**: for **every** initialized immediate `f32` / `f64` source bit pattern (NaN or
not, no `FloatCastDetAgrees` side condition) and **any** `chooseNaN`, Anneal's `stepMirFn` steps
to the successor storing the trusted conversion, while `lean-miri`'s `Step.step` under
`annealStepHooksFloat … false chooseNaN` is `StepRelLM3_1`-simulated by the same successor with
the destination replaced by the canonicalized result (`preferredNaNBits dst` on NaN inputs). -/
theorem step_cast_floatToFloat_copy_deterministic_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    stepMirFn body s =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
            else evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m) := by
  obtain ⟨outBits, _, hnn, hn, ha, hsim⟩ :=
    step_cast_floatToFloat_copy_nanChoice_simulation hstate hphase false chooseNaN
      (fun h => absurd h (by decide)) hbb hstmt hdecl_dst hdecl_src hsrc hdst hdst_ty hinit_src
      hlive_dst himm
  have hout : outBits = if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
      else evalFloatToFloatRoundTiesToEven src dst sc.bits := by
    cases h : Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hnn h
    · simp only [↓reduceIte]; exact (hn h).2 rfl
  rw [← hout]
  exact ⟨ha, hsim⟩

/-- **Deterministic NaN mode = Anneal with canonicalized NaNs (`_d = const c as T`,
`floatToFloat`)**: `lean-miri`'s deterministic step is `StepRelLM3_1`-simulated by Anneal's
successor with the destination canonicalized, for every constant bit pattern. -/
theorem step_cast_floatToFloat_constant_deterministic_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? c.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : sc.sizeBytes = src.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    stepMirFn body s =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
            else evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m) := by
  obtain ⟨outBits, _, hnn, hn, ha, hsim⟩ :=
    step_cast_floatToFloat_constant_nanChoice_simulation hstate hphase false chooseNaN
      (fun h => absurd h (by decide)) hbb hstmt hdecl_dst hsrc hdst hdst_ty hval hsz hcan
      hlive_dst himm_dst
  have hout : outBits = if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
      else evalFloatToFloatRoundTiesToEven src dst sc.bits := by
    cases h : Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hnn h
    · simp only [↓reduceIte]; exact (hn h).2 rfl
  rw [← hout]
  exact ⟨ha, hsim⟩

/-- **Deterministic NaN mode = Anneal with canonicalized NaNs (`_d = move _s as T`,
`floatToFloat`)**: both machines deinitialize `_s`; Anneal stores the trusted conversion while
`lean-miri`'s deterministic step is `StepRelLM3_1`-simulated by the Anneal successor storing
the canonicalized result. -/
theorem step_cast_floatToFloat_move_deterministic_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    stepMirFn body s =
        MirStepNode.step (advanceStmt s ((s.frame.locals.set srcIdx .uninit).set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s ((s.frame.locals.set srcIdx .uninit).set dstIdx
          (.init (.scalar ⟨if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
            else evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m) := by
  obtain ⟨outBits, _, hnn, hn, ha, hsim⟩ :=
    step_cast_floatToFloat_move_nanChoice_simulation hstate hphase false chooseNaN
      (fun h => absurd h (by decide)) hbb hstmt hdecl_dst hdecl_src hsrc hdst hdst_ty hinit_src
      hlive_dst himm
  have hout : outBits = if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst
      else evalFloatToFloatRoundTiesToEven src dst sc.bits := by
    cases h : Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hnn h
    · simp only [↓reduceIte]; exact (hn h).2 rfl
  rw [← hout]
  exact ⟨ha, hsim⟩

/-- **Exact step-level constant-index NaN-choice simulation (`_d = copy _s as T`, `floatToFloat`)**:
for any state-preserving constant selector `chooseNaN` returning `i < 4` (`hsel`), `lean-miri`'s
`Step.step` under `annealStepHooksFloat ... true chooseNaN` is `StepRelLM3_1`-simulated by the
Anneal successor storing the **exact** `floatToFloatPureIndexBits src dst sc.bits i` (eliminating
the existential `outBits` of `step_cast_floatToFloat_copy_nanChoice_simulation`). -/
theorem step_cast_floatToFloat_copy_pure_index_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (i : Nat) (hi : i < 4) (hsel : ∀ cs st, chooseNaN () cs st = .ok i st)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    stepMirFn body s =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨floatToFloatPureIndexBits src dst sc.bits i, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts true
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.copy ⟨srcIdx, .nil⟩) castTy span m
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
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz_lay, hms⟩
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
    have hsz : sc.sizeBytes = src.byteWidth :=
      sizeBytes_of_float_layout hrel.validBytes
        ((congrArg (·.layout.size) (translateTy_of_ieeeFormatOfTy? hsrc body.layouts)).symm.trans
          hsz_lay)
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    obtain ⟨msc', hrel', hcast⟩ :=
      cast_floatToFloat_pure_index_eq body.layouts chooseNaN i hi hsel hsrc hdst hrel hsz
        (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfb]⟩ } := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
    have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy)
        s.memory body.localDecls body.layouts =
        .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
          s.frame.locals s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) s.frame.locals := by
        unfold evalOperand readProjectedValue; dsimp only []; rw [hinit_src]
      rw [hop]; dsimp only []; rw [operandTy_copy_local hdecl_src]
      simp only [evalFloatCast, hsrc, hdst, hsz]; cases src <;> rfl
    obtain ⟨hev, hsim⟩ := finish_write_immediate_split_hooks _ hframes hfr.body_eq
      hfr.location_eq hstate_b rfl hbb hstmt hdecl_dst
      ((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _) hlive_dst hrv_a hm_write
      (floatCast_dst_localRel hdst_scalar hrel'
        (floatToFloat_dst_size body.layouts hdst hdst_ty _))
    refine ⟨?_, hsim⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; exact hev

/-- **Exact step-level constant-index NaN-choice simulation (`_d = const c as T`, `floatToFloat`)**:
stores `floatToFloatPureIndexBits src dst sc.bits i` for any `pure i` (`i < 4`). -/
theorem step_cast_floatToFloat_constant_pure_index_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (i : Nat) (hi : i < 4) (hsel : ∀ cs st, chooseNaN () cs st = .ok i st)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? c.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : sc.sizeBytes = src.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    stepMirFn body s =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨floatToFloatPureIndexBits src dst sc.bits i, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have himm_d := himm_dst tf hframes
  have hsig : FloatCastSig .floatToFloat c.ty castTy := .floatToFloat hsrc hdst
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts true
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.constant c) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have hv_bytes : ValidScalarBytes sc.sizeBytes := hsz ▸ validScalarBytes_byteWidth src
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hv_bytes hcan
  have hsrc_ok : annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
      none { m with stack := ⟨#[tfa]⟩ } =
      .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } := by
    with_unfolding_all
      unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
      dsimp only
      rw [hval]
      simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
        EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        stack_currentFrame?_singleton { m with stack := ⟨#[tfa]⟩ }.stack tfa rfl,
        Option.isNone_some, Bool.false_eq_true, ↓reduceIte, htry,
        layoutOfEncodedTyId_floatCastScalar hsig.src_scalar body.layouts]
  obtain ⟨msc', hrel', hcast⟩ :=
    cast_floatToFloat_pure_index_eq body.layouts chooseNaN i hi hsel hsrc hdst hrel hsz
      (.local 0 dstIdx none tf.localsIdentity)
  rw [← hdstT] at hcast
  have hm_write : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tfa]⟩ } := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
      show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
  have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.constant c) castTy) s.memory
      body.localDecls body.layouts =
      .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
        s.frame.locals s.memory := by
    rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]; dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl]
    simp only [evalFloatCast, hsrc, hdst, hsz, Nat.beq_refl]
  obtain ⟨hev, hsim⟩ := finish_write_immediate_split_hooks _ hframes hfr.body_eq
    hfr.location_eq hstate_a rfl hbb hstmt hdecl_dst (himm_d.cache_layout hlt_d _) hlive_dst
    hrv_a hm_write
    (floatCast_dst_localRel hdst_scalar hrel' (floatToFloat_dst_size body.layouts hdst hdst_ty _))
  refine ⟨?_, hsim⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; exact hev

/-- **Exact step-level constant-index NaN-choice simulation (`_d = move _s as T`, `floatToFloat`)**:
deinitializes `_s` and stores `floatToFloatPureIndexBits src dst sc.bits i` for any `pure i`
(`i < 4`). -/
theorem step_cast_floatToFloat_move_pure_index_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (i : Nat) (hi : i < 4) (hsel : ∀ cs st, chooseNaN () cs st = .ok i st)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    stepMirFn body s =
        MirStepNode.step (advanceStmt s ((s.frame.locals.set srcIdx .uninit).set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      StepRelLM3_1 body m allocMap
        (MirStepNode.step (advanceStmt s ((s.frame.locals.set srcIdx .uninit).set dstIdx
          (.init (.scalar ⟨floatToFloatPureIndexBits src dst sc.bits i, dst.byteWidth⟩))) s.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf hframes
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  have hdst_scalar : IsFloatCastScalarTy dstDecl.ty := hsig.cast_scalar.of_kind_eq hdst_ty
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts true
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.move ⟨srcIdx, .nil⟩) castTy span m
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
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz_lay, hms⟩
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
    have hsz : sc.sizeBytes = src.byteWidth :=
      sizeBytes_of_float_layout hrel.validBytes
        ((congrArg (·.layout.size) (translateTy_of_ieeeFormatOfTy? hsrc body.layouts)).symm.trans
          hsz_lay)
    obtain ⟨msc', hrel', hcast⟩ :=
      cast_floatToFloat_pure_index_eq body.layouts chooseNaN i hi hsel hsrc hdst hrel hsz
        (.local 0 dstIdx none tf.localsIdentity)
    rw [← hdstT] at hcast
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have himm_sb := (himm_s.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)).cache_layout
      hlt_sa (translateTy srcDecl.ty body.layouts)
    have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hinit_src (by simp) himm_sb
      hlt_sb
    obtain ⟨hlt_af_s, _⟩ := List.getElem?_eq_some_iff.mp
      (by rw [← get?_eq_getElem?]; exact hinit_src)
    have hrv_a : evalRvalue s.frame.locals (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy)
        s.memory body.localDecls body.layouts =
        .ok (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
          (s.frame.locals.set srcIdx .uninit) s.memory := by
      rw [evalRvalue_floatCast_eq hsig]; unfold evalFloatCastRvalue
      have hop : evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
          .ok (.scalar sc) (s.frame.locals.set srcIdx .uninit) := by
        unfold evalOperand; dsimp only []; rw [hinit_src, set?_eq_some_set hlt_af_s]
      rw [hop]; dsimp only []; rw [operandTy_move_local hdecl_src]
      simp only [evalFloatCast, hsrc, hdst, hsz]; cases src <;> rfl
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
    have hlive_mid : get? (s.frame.locals.set srcIdx .uninit) dstIdx ≠ some .dead := by
      by_cases hds : srcIdx = dstIdx
      · subst hds; rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_s]; simp
      · rw [get?_eq_getElem?, List.getElem?_set_ne hds, ← get?_eq_getElem?]; exact hlive_dst
    obtain ⟨hev, hsim⟩ := finish_write_immediate_split_hooks _ hframes hfr.body_eq
      hfr.location_eq hstate_mid rfl hbb hstmt hdecl_dst
      (((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _).deinit_local hlt_sb) hlive_mid
      hrv_a hm_write
      (floatCast_dst_localRel hdst_scalar hrel'
        (floatToFloat_dst_size body.layouts hdst hdst_ty _))
    refine ⟨?_, hsim⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]; simp only [hbb, hstmt]; exact hev

/-- **Tightness of the selector-validity premise at the step level (`_d = const c as T`,
`floatToFloat`)**: under `floatNondeterministic := true` with a state-preserving constant selector
whose index lies at or beyond the length of the NaN candidate list (e.g. `pure 4` on a quiet NaN),
Anneal steps normally while `lean-miri`'s `Step.step` fails with
`.invalidProgram "invalid floating NaN choice index"`, so no `StepRelLM3_1` relates the two steps:
the `hchoose` / `i < 4` premises of the NaN-choice simulations are necessary. -/
theorem step_cast_floatToFloat_constant_pure_out_of_range
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (i : Nat) (hsel : ∀ cs st, chooseNaN () cs st = .ok i st)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? c.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : sc.sizeBytes = src.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    {neg q : Bool} {payload : Nat} (hnan : decodeBits src sc.bits = .nan neg q payload)
    {cs : List Miri.Interpreter.FloatBits}
    (hcs : Miri.Interpreter.FloatBits.nanChoices (ieeeFormatToMiri dst)
      [⟨ieeeFormatToMiri src, BitVec.ofNat 128 sc.bits⟩] true = .ok cs)
    (hi : cs.length ≤ i)
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    stepMirFn body s =
        MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) ∧
      (∃ m', Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) () m =
        (m', .error (.invalidProgram "invalid floating NaN choice index"))) ∧
      ¬ StepRelLM3_1 body m allocMap (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) () m) := by
  have ha := (step_cast_floatToFloat_constant_deterministic_simulation hstate hphase chooseNaN
    hbb hstmt hdecl_dst hsrc hdst hdst_ty hval hsz hcan hlive_dst himm_dst).1
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  have hsig : FloatCastSig .floatToFloat c.ty castTy := .floatToFloat hsrc hdst
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts true
    chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.constant c) castTy span m
  have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
    hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hv_bytes : ValidScalarBytes sc.sizeBytes := hsz ▸ validScalarBytes_byteWidth src
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hv_bytes hcan
  have hsrc_ok : annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
      none { m with stack := ⟨#[tfa]⟩ } =
      .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } := by
    with_unfolding_all
      unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
      dsimp only
      rw [hval]
      simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
        EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        stack_currentFrame?_singleton { m with stack := ⟨#[tfa]⟩ }.stack tfa rfl,
        Option.isNone_some, Bool.false_eq_true, ↓reduceIte, htry,
        layoutOfEncodedTyId_floatCastScalar hsig.src_scalar body.layouts]
  have hcast_err := cast_floatToFloat_pure_out_of_range body.layouts chooseNaN i hsel hsrc hdst
    hrel hsz hnan hcs hi (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfa]⟩ }
  rw [← hdstT] at hcast_err
  have hm_err : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts true chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩) m =
      ({ m with stack := ⟨#[tfa]⟩ },
        .error (.invalidProgram "invalid floating NaN choice index")) := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
      show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast_err]
  have hm_step := miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
    hm_err
  refine ⟨ha, ⟨_, hm_step⟩, fun hrel => ?_⟩
  rw [ha, hm_step] at hrel
  cases hrel

/-! ### Part 8d. Tightness of `FloatCastDetAgrees`: deterministic lockstep iff agreement

The `_mode` step theorems need `FloatCastDetAgrees` in deterministic NaN mode. The theorems
below show the side condition is not merely sufficient but **necessary**: on an initialized
`f32` / `f64` source, `StepRelLM3_1` lockstep between `stepMirFn` and `Step.step` under
`annealStepHooksFloat … false chooseNaN` holds **if and only if** the source is not a NaN or
its quieted conversion already is `preferredNaNBits dst`. -/

/-- Two `ScalarRel` relations sharing one `lean-miri` scalar and one byte width pin the same
Anneal bit pattern (`ScalarRel` is functional in the `lean-miri` → Anneal direction). -/
theorem ScalarRel.bits_eq_of_same_msc {a b w : Nat} {msc : Miri.Memory.ScalarInt}
    (ha : ScalarRel ⟨a, w⟩ msc) (hb : ScalarRel ⟨b, w⟩ msc) : a = b := by
  have hmod : scalarModulus w ≤ 2 ^ 128 := by
    rcases ha.validBytes with h | h | h | h | h <;> (dsimp only at h; subst h; decide)
  have ha_lt : a < 2 ^ 128 := Nat.lt_of_lt_of_le ha.canonical hmod
  have hb_lt : b < 2 ^ 128 := Nat.lt_of_lt_of_le hb.canonical hmod
  have hd : BitVec.ofNat 128 a = BitVec.ofNat 128 b := ha.data_eq.symm.trans hb.data_eq
  have hn := congrArg BitVec.toNat hd
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
    Nat.mod_eq_of_lt hb_lt] at hn

/-- `Scalar.fromScalarInt` is injective. -/
theorem scalar_fromScalarInt_inj {a b : Miri.Memory.ScalarInt}
    (h : (Miri.Memory.Scalar.fromScalarInt a : Miri.Memory.Scalar AnnealProv) =
      Miri.Memory.Scalar.fromScalarInt b) : a = b := by
  unfold Miri.Memory.Scalar.fromScalarInt at h
  injection h with h₁
  injection h₁

/-- Reading back the destination of a deterministic step: if `StateRelLM3_1` relates the
Anneal successor storing `⟨A, w⟩` into `_d` to a `lean-miri` state whose `_d` immediately
holds `fromScalarInt msc` with `ScalarRel ⟨M, w⟩ msc`, then `A = M`. -/
theorem stateRel_dst_scalar_bits_eq {body : CapturedMir} {s : MachineState}
    {locals₀ : List LocalSlot}
    {m' : AnnealStepState} {allocMap : List AllocMapEntry}
    {tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Local} {dstDecl : LocalDecl} {A M w : Nat} {msc : Miri.Memory.ScalarInt}
    (hst : StateRelLM3_1 body
      (advanceStmt s (locals₀.set dstIdx (.init (.scalar ⟨A, w⟩))) s.memory) m' allocMap)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_scalar : IsFloatCastScalarTy dstDecl.ty)
    (htf' : m'.stack.frames = #[tf'])
    (hval : (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
      some (.live (.immediate (.scalar (.fromScalarInt msc)))))
    (hrelM : ScalarRel ⟨M, w⟩ msc) :
    A = M := by
  have hfr := hst.frame_rel_singleton htf'
  obtain ⟨slot, mls, hlt_af, _, hslot, hmls, _, hloc⟩ := hfr.lookup_local hdecl_dst
  have hslot_eq : slot = .init (.scalar ⟨A, w⟩) := by
    have hlt : dstIdx < locals₀.length := by
      have h := hlt_af
      simp only [advanceStmt, List.length_set] at h
      exact h
    have h := hslot
    simp only [advanceStmt] at h
    rw [get?_eq_getElem?, List.getElem?_set_self hlt] at h
    exact (Option.some.inj h).symm
  have hmls_val : mls.value = .live (.immediate (.scalar (.fromScalarInt msc))) := by
    rw [hmls] at hval
    exact Option.some.inj hval
  rcases hloc.floatCast_immediate_cases hdst_scalar
      (fun mp h => by rw [hmls_val] at h; cases h) with
    ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨sc₀, msc₀, hs, hrel₀, _, hm₀⟩
  · rw [hslot_eq] at hs; cases hs
  · rw [hslot_eq] at hs; cases hs
  · rw [hslot_eq] at hs
    injection hs with hs₁; injection hs₁ with hs₂; subst hs₂
    rw [hmls_val] at hm₀
    injection hm₀ with hm₁; injection hm₁ with hm₂; injection hm₂ with hm₃
    rw [← scalar_fromScalarInt_inj hm₃] at hrel₀
    exact ScalarRel.bits_eq_of_same_msc hrel₀ hrelM

/-- The `if`-canonicalized deterministic result equals the trusted conversion exactly when
the input is not a NaN or the quieted conversion already is `preferredNaNBits`. -/
theorem detBits_eq_iff_agrees (src dst : IeeeFormat) (bits : Nat) :
    evalFloatToFloatRoundTiesToEven src dst bits =
        (if Anneal.Mir.IeeeFloatCast.isNaNBits src bits then preferredNaNBits dst
          else evalFloatToFloatRoundTiesToEven src dst bits) ↔
      (Anneal.Mir.IeeeFloatCast.isNaNBits src bits = false ∨
        evalFloatToFloatRoundTiesToEven src dst bits = preferredNaNBits dst) := by
  cases hn : Anneal.Mir.IeeeFloatCast.isNaNBits src bits <;> simp

/-- **Tightness of `FloatCastDetAgrees` (`_d = copy _s as T`, `floatToFloat`)**: in
deterministic NaN mode (`floatNondeterministic := false`, **any** `chooseNaN`), on an
initialized immediate `f32` / `f64` source `_s` and a live immediate `_d`, `stepMirFn` and
`Step.step` step in `StepRelLM3_1` lockstep **if and only if** the source is not a NaN or its
quieted conversion already is `preferredNaNBits dst`. -/
theorem step_cast_floatToFloat_copy_deterministic_lockstep_iff
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m) ↔
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = false ∨
        evalFloatToFloatRoundTiesToEven src dst sc.bits = preferredNaNBits dst) := by
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  constructor
  · intro hrel
    obtain ⟨m', tf', msc', hrelM, ha, hm, htf', hval⟩ :=
      step_cast_floatToFloat_copy_deterministic_spec hstate hphase chooseNaN hbb hstmt
        hdecl_dst hdecl_src hsrc hdst hdst_ty hinit_src hlive_dst himm
    rw [ha, hm] at hrel
    have hst : StateRelLM3_1 body
        (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) m' allocMap := by
      cases hrel with
      | step _ _ h => exact h
    exact (detBits_eq_iff_agrees src dst sc.bits).mp
      (stateRel_dst_scalar_bits_eq hst hdecl_dst (hsig.cast_scalar.of_kind_eq hdst_ty) htf'
        hval hrelM)
  · intro hag
    refine step_cast_float_copy_simulation_mode hstate hphase false chooseNaN (Or.inr rfl)
      hbb hstmt hdecl_dst hdecl_src hsig hdst_ty ?_ himm hptr8
    intro _ sc' hsc' src' dst' _ hsrc' hdst'
    rw [hinit_src] at hsc'
    cases hsc'
    rw [hsrc] at hsrc'; rw [hdst] at hdst'
    injection hsrc' with h₁; injection hdst' with h₂; subst h₁ h₂
    exact hag

/-- **Tightness of `FloatCastDetAgrees` (`_d = const c as T`, `floatToFloat`)**: in
deterministic NaN mode (**any** `chooseNaN`), `stepMirFn` and `Step.step` step in
`StepRelLM3_1` lockstep **if and only if** the constant is not a NaN or its quieted
conversion already is `preferredNaNBits dst`. -/
theorem step_cast_floatToFloat_constant_deterministic_lockstep_iff
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl} (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? c.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : sc.sizeBytes = src.byteWidth) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m) ↔
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = false ∨
        evalFloatToFloatRoundTiesToEven src dst sc.bits = preferredNaNBits dst) := by
  have hsig : FloatCastSig .floatToFloat c.ty castTy := .floatToFloat hsrc hdst
  constructor
  · intro hrel
    obtain ⟨m', tf', msc', hrelM, ha, hm, htf', hval'⟩ :=
      step_cast_floatToFloat_constant_deterministic_spec hstate hphase chooseNaN hbb hstmt
        hdecl_dst hsrc hdst hdst_ty hval hsz hcan hlive_dst himm_dst
    rw [ha, hm] at hrel
    have hst : StateRelLM3_1 body
        (advanceStmt s (s.frame.locals.set dstIdx
          (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) m' allocMap := by
      cases hrel with
      | step _ _ h => exact h
    exact (detBits_eq_iff_agrees src dst sc.bits).mp
      (stateRel_dst_scalar_bits_eq hst hdecl_dst (hsig.cast_scalar.of_kind_eq hdst_ty) htf'
        hval' hrelM)
  · intro hag
    refine step_cast_float_constant_simulation_mode hstate hphase false chooseNaN (Or.inr rfl)
      hbb hstmt hdecl_dst hsig hdst_ty hval (hsz ▸ validScalarBytes_byteWidth src) hcan ?_ ?_
      himm_dst hptr8
    · rw [hsz, translateTy_of_ieeeFormatOfTy? hsrc body.layouts, translateSizeBytes_byteWidth,
        floatLayoutData_size]
    · intro _ src' dst' _ hsrc' hdst'
      rw [hsrc] at hsrc'; rw [hdst] at hdst'
      injection hsrc' with h₁; injection hdst' with h₂; subst h₁ h₂
      exact hag

/-- **Real-step deterministic NaN characterization (`_d = move _s as dstTy`)** across **every**
initialized immediate `f32` / `f64` source `_s` (without assuming `FloatCastDetAgrees`),
completing the `{constant, copy, move}` triad alongside
`step_cast_floatToFloat_{constant,copy}_deterministic_spec`. -/
theorem step_cast_floatToFloat_move_deterministic_spec
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    let annealBits := evalFloatToFloatRoundTiesToEven src dst sc.bits
    let miriBits :=
      if Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits then preferredNaNBits dst else annealBits
    ∃ m' tf' msc',
      ScalarRel ⟨miriBits, dst.byteWidth⟩ msc' ∧
      stepMirFn body s =
        MirStepNode.step
          (advanceStmt s
            ((s.frame.locals.set srcIdx .uninit).set dstIdx
              (.init (.scalar ⟨annealBits, dst.byteWidth⟩)))
            s.memory) ∧
      Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc')))) := by
  dsimp only
  obtain ⟨ha, _⟩ := step_cast_floatToFloat_move_deterministic_simulation hstate hphase
    chooseNaN hbb hstmt hdecl_dst hdecl_src hsrc hdst hdst_ty hinit_src hlive_dst himm
  obtain ⟨tf₀, hframes₀, _⟩ := id hstate
  obtain ⟨himm_d, himm_s⟩ := himm tf₀ hframes₀
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  obtain ⟨_, mls0_d, _, hlt0_d, _, _, hmls0_d_eq, hloc0_d⟩ :=
    (hstate.frame_rel_singleton hframes₀).lookup_local hdecl_dst
  have hcache0_d : ∀ l, (tf₀.locals[dstIdx]'hlt0_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls0_d_eq]; exact hloc0_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes₀ hlt0_d hdecl_dst hcache0_d
  let tfa := cacheFrameLocalLayout tf₀ dstIdx hlt0_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes₀ hdecl_dst hlt0_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := himm_s.cache_layout hlt0_d _
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  rcases hloc_s.floatCast_immediate_cases hsig.src_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz_lay, hms⟩
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s; cases hslot_s
  · rw [hss, hinit_src] at hslot_s
    cases hslot_s
    have hsz : sc.sizeBytes = src.byteWidth :=
      sizeBytes_of_float_layout hrel.validBytes
        ((congrArg (·.layout.size) (translateTy_of_ieeeFormatOfTy? hsrc body.layouts)).symm.trans
          hsz_lay)
    obtain ⟨msc', hrel', hcast⟩ := cast_floatToFloat_deterministic_eq body.layouts chooseNaN
      hsrc hdst hrel hsz (.local 0 dstIdx none tf₀.localsIdentity)
    have hdstT : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts :=
      hsig.cast_scalar.translateTy_eq hdst_ty body.layouts
    rw [← hdstT] at hcast
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts false
      chooseNaN ⟨dstIdx, .nil⟩ .floatToFloat rfl (.move ⟨srcIdx, .nil⟩) castTy span m
    let tfc := deinitFrameLocal tfb srcIdx hlt_sb
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate (.scalar (.fromScalarInt msc'))
            ⟨.local 0 dstIdx none tf₀.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tfc]⟩ } := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        show translateCastKind .floatToFloat = .FloatToFloat from rfl, hcast]
    have himm_sb := (himm_s.cache_layout hlt0_d (translateTy dstDecl.ty body.layouts)).cache_layout
      hlt_sa (translateTy srcDecl.ty body.layouts)
    have hstate_mid := (hstate_a.cache_layout rfl hdecl_src hlt_sa).deinit_immediate_local rfl
      hdecl_src hinit_src (by simp) himm_sb hlt_sb
    have himm_d_tfc : IsImmediateFrameLocal tfc dstIdx :=
      (((himm_d.cache_layout hlt0_d (translateTy dstDecl.ty body.layouts)).cache_layout hlt_sa
        (translateTy srcDecl.ty body.layouts)).deinit_local hlt_sb)
    obtain ⟨slot_dc, mls_dc, _, hlt_dc, hslot_dc, hmls_dc, _, hloc_dc⟩ :=
      hstate_mid.frame_rel_singleton rfl |>.lookup_local hdecl_dst
    obtain ⟨hlt_af_s, _⟩ := List.getElem?_eq_some_iff.mp
      (by rw [← get?_eq_getElem?]; exact hinit_src)
    have hlive_mid : slot_dc ≠ .dead := by
      intro hdead; subst hdead
      by_cases hds : srcIdx = dstIdx
      · subst hds; rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_s] at hslot_dc; cases hslot_dc
      · rw [get?_eq_getElem?, List.getElem?_set_ne hds, ← get?_eq_getElem?] at hslot_dc
        exact hlive_dst hslot_dc
    have hold_imm : ∃ oldImm, mls_dc.value = .live (.immediate oldImm) := by
      cases hloc_dc with
      | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
      | base hb =>
        cases hb with
        | indirect _ mp _ _ _ _ => exact absurd rfl (himm_d_tfc _ hmls_dc mp)
        | dead _ _ => exact absurd rfl hlive_mid
        | immediate _ oldImm _ _ _ => exact ⟨oldImm, rfl⟩
    obtain ⟨oldImm, hmd_imm⟩ := hold_imm
    have hdc_live : tfc.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_dc.layout⟩ := by
      rw [hmls_dc]; rcases mls_dc with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
    have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_live
    have hw_ok := annealWriteImmediate_live (val := .scalar (.fromScalarInt msc'))
      (m := { m with stack := ⟨#[tfc]⟩ }) (id0 := tf₀.localsIdentity)
      (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dc hget_dc
    have hm_ok : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[{ tfc with
            locals := tfc.locals.set dstIdx
              { tfc.locals[dstIdx]'hlt_dc with
                value := .live (.immediate (.scalar (.fromScalarInt msc'))) }
              hlt_dc }]⟩ }, .ok ()) := by
      rw [hm_write]; unfold Miri.Interpreter.runRvalue; rw [hw_ok]
    have hloc_c : tfc.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
      (hstate_mid.frame_rel_singleton rfl).location_eq
    have hm_step := miri_step_at_statement_ok
      (annealStepHooksFloat body.localDecls body.layouts false chooseNaN)
      hframes₀ (hstate.frame_rel_singleton hframes₀).body_eq
      (hstate.frame_rel_singleton hframes₀).location_eq hbb hstmt hm_ok rfl hloc_c
    refine ⟨_, _, msc', hrel', ha, hm_step, rfl, ?_⟩
    simp [Array.getElem?_set_self]

/-- **Tightness of `FloatCastDetAgrees` (`_d = move _s as T`, `floatToFloat`)**: in
deterministic NaN mode (`floatNondeterministic := false`, **any** `chooseNaN`), on an
initialized immediate `f32` / `f64` source `_s` and a live immediate `_d`, `stepMirFn` and
`Step.step` step in `StepRelLM3_1` lockstep **if and only if** the source is not a NaN or its
quieted conversion already is `preferredNaNBits dst` (covering both `srcIdx ≠ dstIdx` and
self-move `srcIdx = dstIdx`). -/
theorem step_cast_floatToFloat_move_deterministic_lockstep_iff
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .floatToFloat (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {src dst : IeeeFormat} (hsrc : ieeeFormatOfTy? srcDecl.ty = some src)
    (hdst : ieeeFormatOfTy? castTy = some dst) (hdst_ty : dstDecl.ty.kind = castTy.kind)
    {sc : MirAst.ScalarInt} (hinit_src : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hlive_dst : get? s.frame.locals dstIdx ≠ some .dead)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts false chooseNaN) () m) ↔
      (Anneal.Mir.IeeeFloatCast.isNaNBits src sc.bits = false ∨
        evalFloatToFloatRoundTiesToEven src dst sc.bits = preferredNaNBits dst) := by
  have hsig : FloatCastSig .floatToFloat srcDecl.ty castTy := .floatToFloat hsrc hdst
  constructor
  · intro hrel
    obtain ⟨m', tf', msc', hrelM, ha, hm, htf', hval⟩ :=
      step_cast_floatToFloat_move_deterministic_spec hstate hphase chooseNaN hbb hstmt
        hdecl_dst hdecl_src hsrc hdst hdst_ty hinit_src hlive_dst himm
    rw [ha, hm] at hrel
    have hst : StateRelLM3_1 body
        (advanceStmt s
          ((s.frame.locals.set srcIdx .uninit).set dstIdx
            (.init (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)))
          s.memory) m' allocMap := by
      cases hrel with
      | step _ _ h => exact h
    exact (detBits_eq_iff_agrees src dst sc.bits).mp
      (stateRel_dst_scalar_bits_eq hst hdecl_dst (hsig.cast_scalar.of_kind_eq hdst_ty) htf'
        hval hrelM)
  · intro hag
    refine step_cast_float_move_simulation_mode hstate hphase false chooseNaN (Or.inr rfl)
      hbb hstmt hdecl_dst hdecl_src hsig hdst_ty ?_ himm hptr8
    intro _ sc' hsc' src' dst' _ hsrc' hdst'
    rw [hinit_src] at hsc'
    cases hsc'
    rw [hsrc] at hsrc'; rw [hdst] at hdst'
    injection hsrc' with h₁; injection hdst' with h₂; subst h₁ h₂
    exact hag

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

/-- Vendored `Miri.Memory.ScalarInt.isUnicodeScalar` (`private`, `ScalarInt.lean:197-198`). -/
local macro "miriIsUnicodeScalar" : term =>
  `(miri_private% Miri.Memory.ScalarInt Miri.Memory.ScalarInt.isUnicodeScalar)

theorem scalar_fromBool_toBool (b : Bool) :
    (Miri.Memory.Scalar.fromBool (Prov := AnnealProv) b).toBool = .ok b := by
  cases b <;> rfl

theorem scalar_fromChar_toChar (ch : Char) :
    (Miri.Memory.Scalar.fromChar (Prov := AnnealProv) ch).toChar = .ok ch := by
  rcases ch with ⟨v, hv⟩
  have hv_lt : v.toNat < 4294967296 := v.toBitVec.isLt
  have hu32 : UInt32.ofNat v.toNat = v := UInt32.ofNat_toNat
  have hbv : (BitVec.ofNat 128 v.toNat).toNat = v.toNat := Nat.mod_eq_of_lt (by omega)
  have his : miriIsUnicodeScalar v.toNat = true := by
    change (decide (v.toNat ≤ 0x10ffff) &&
        !(decide (0xd800 ≤ v.toNat) && decide (v.toNat ≤ 0xdfff))) = true
    unfold UInt32.isValidChar Nat.isValidChar at hv
    rcases hv with h1 | ⟨h1, h2⟩ <;> simp <;> omega
  unfold Miri.Memory.Scalar.fromChar Miri.Memory.Scalar.toChar
    Miri.Memory.Scalar.toScalarInt Miri.Memory.Scalar.tryToScalarInt
    Miri.Memory.Scalar.fromScalarInt Miri.Memory.ScalarInt.ofChar
    Miri.Memory.ScalarInt.ofUInt32 Miri.Memory.ScalarInt.toChar
    Miri.Memory.ScalarInt.toUInt32 Miri.Memory.ScalarInt.toUInt
    Miri.Memory.ScalarInt.toBits Char.toNat
  dsimp only [bind, Except.bind, pure, Except.pure, Except.mapError]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hu32, hbv, his, Bool.not_true]
  congr 1
  unfold Char.ofNat
  have hvn : v.toNat.isValidChar := hv
  simp only [hvn, ↓reduceDIte]
  congr 1

/-- **Miri side of the `bool` `IntToFloat` boundary**: while Anneal's `evalFloatCast`
returns `none` and `FloatOps.castIntToFloat` throws `.invalidProgram`, `Cast.cast .IntToFloat`
routes through `Cast.castFromIntLike` (`Cast.lean:98, 115`) and maps `false ↦ +0.0`,
`true ↦ 1.0`. -/
theorem cast_intToFloat_bool_miri_ok (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {srcTy targetTy : Ty} {dst : IeeeFormat}
    (hsrc : srcTy.kind = .bool) (hdst : ieeeFormatOfTy? targetTy = some dst)
    (b : Bool) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    ∃ msc',
      ScalarRel ⟨evalIntToFloatRoundTiesToEven false 8 (if b then 1 else 0) dst, dst.byteWidth⟩ msc' ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨.immediate (.scalar (.fromBool b)), translateTy srcTy layouts⟩ .IntToFloat
          (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨destRef, translateTy targetTy layouts⟩ := by
  have hclt := Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_lt false 8
    (if b then 1 else 0) dst
  obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec
    (validScalarBytes_byteWidth dst)
    (caseVal := evalIntToFloatRoundTiesToEven false 8 (if b then 1 else 0) dst)
    (by rw [scalarModulus_byteWidth]; exact hclt)
  rw [translateSizeBytes_byteWidth] at hfrom
  refine ⟨msc', hrel', ?_⟩
  have hsrcT : translateTy srcTy layouts =
      { ty := 1, layout := scalarLayoutData 1 false 0 1 } := by
    unfold translateTy encodeTyId; rw [hsrc]
  have hdstT := translateTy_of_ieeeFormatOfTy? hdst layouts
  have henc : encodeTyId targetTy = floatTyIdOf dst := congrArg (·.ty) hdstT
  rw [hsrcT, hdstT, henc]
  unfold Miri.Interpreter.Cast.cast
  have hfi0 : Miri.Interpreter.FloatBits.fromInteger (ieeeFormatToMiri dst)
      (Int.ofNat (0 : BitVec 128).toNat) =
      .ok ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalIntToFloatRoundTiesToEven false 8 0 dst)⟩ :=
    floatBits_fromInteger_intValueOfBits false 8 0 dst
  have hfi1 : Miri.Interpreter.FloatBits.fromInteger (ieeeFormatToMiri dst)
      (Int.ofNat (1 : BitVec 128).toNat) =
      .ok ⟨ieeeFormatToMiri dst, BitVec.ofNat 128 (evalIntToFloatRoundTiesToEven false 8 1 dst)⟩ :=
    floatBits_fromInteger_intValueOfBits false 8 1 dst
  have htb := scalar_fromBool_toBool b
  cases b <;>
  · simp only [↓reduceIte, Bool.false_eq_true] at hfrom htb ⊢
    simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
      pure_bind, annealReadImmediate_scalar, cast_scalarOf_scalar,
      show castTypeInfoOfEncodedTyIdFloat 1 = .ok .boolean from rfl,
      castTypeInfoOfEncodedTyIdFloat_floatTyIdOf]
    unfold Miri.Interpreter.Cast.castFromIntLike Miri.Interpreter.Cast.intLikeValue
    simp only [show (scalarLayoutData 1 false 0 1).backendRepr.isSigned = .ok false from rfl,
      show castTypeInfoOfEncodedTyIdFloat 1 = .ok .boolean from rfl,
      castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true, ↓reduceIte,
      htb, hfi0, hfi1, hfrom, Except.mapError, cast_liftResult_ok, floatLayoutData_size,
      bne_self_eq_false]

/-- **Miri side of the `char` `IntToFloat` boundary**: while Anneal's `evalFloatCast`
returns `none` and `FloatOps.castIntToFloat` throws `.invalidProgram`, `Cast.cast .IntToFloat`
routes through `Cast.castFromIntLike` (`Cast.lean:99, 115`) and converts `ch.toNat`
(as a 32-bit unsigned Unicode scalar value) to `dst` via `roundTiesToEven`. -/
theorem cast_intToFloat_char_miri_ok (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {srcTy targetTy : Ty} {dst : IeeeFormat}
    (hsrc : srcTy.kind = .char) (hdst : ieeeFormatOfTy? targetTy = some dst)
    (ch : Char) (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    ∃ msc',
      ScalarRel ⟨evalIntToFloatRoundTiesToEven false 32 ch.toNat dst, dst.byteWidth⟩ msc' ∧
      Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨.immediate (.scalar (.fromChar ch)), translateTy srcTy layouts⟩ .IntToFloat
          (encodeTyId targetTy) ⟨destRef, translateTy targetTy layouts⟩ =
        annealWriteImmediate (.scalar (.fromScalarInt msc'))
          ⟨destRef, translateTy targetTy layouts⟩ := by
  have hch_lt32 : ch.toNat < 2 ^ 32 := ch.val.toBitVec.isLt
  have hch_lt128 : ch.toNat < 2 ^ 128 := by omega
  have hclt := Anneal.Mir.IeeeFloatCast.evalIntToFloatRoundTiesToEven_lt false 32 ch.toNat dst
  obtain ⟨msc', hfrom, hrel'⟩ := scalar_fromUInt_translateSizeBytes_spec
    (validScalarBytes_byteWidth dst)
    (caseVal := evalIntToFloatRoundTiesToEven false 32 ch.toNat dst)
    (by rw [scalarModulus_byteWidth]; exact hclt)
  rw [translateSizeBytes_byteWidth] at hfrom
  refine ⟨msc', hrel', ?_⟩
  have hsrcT : translateTy srcTy layouts =
      { ty := 2, layout := scalarLayoutData 4 false 0 0x10FFFF } := by
    unfold translateTy encodeTyId; rw [hsrc]
  have hdstT := translateTy_of_ieeeFormatOfTy? hdst layouts
  have henc : encodeTyId targetTy = floatTyIdOf dst := congrArg (·.ty) hdstT
  have hfi := floatBits_fromInteger_intValueOfBits false 32 ch.toNat dst
  have hiv : intValueOfBits false 32 ch.toNat = Int.ofNat (BitVec.ofNat 128 ch.toNat).toNat := by
    unfold intValueOfBits
    simp [Nat.mod_eq_of_lt hch_lt32, Nat.mod_eq_of_lt hch_lt128]
  rw [hiv] at hfi
  rw [hsrcT, hdstT, henc]
  unfold Miri.Interpreter.Cast.cast
  simp only [annealCastHooksFloat, annealCastHooks, beq_self_eq_true, ↓reduceIte,
    pure_bind, Bool.false_eq_true, annealReadImmediate_scalar, cast_scalarOf_scalar,
    show castTypeInfoOfEncodedTyIdFloat 2 = .ok .character from rfl,
    castTypeInfoOfEncodedTyIdFloat_floatTyIdOf]
  unfold Miri.Interpreter.Cast.castFromIntLike Miri.Interpreter.Cast.intLikeValue
  simp only [show (scalarLayoutData 4 false 0 0x10FFFF).backendRepr.isSigned = .ok false from rfl,
    show castTypeInfoOfEncodedTyIdFloat 2 = .ok .character from rfl,
    castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true, ↓reduceIte,
    scalar_fromChar_toChar ch, hfi, hfrom, Except.mapError, cast_liftResult_ok,
    floatLayoutData_size, bne_self_eq_false]

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

/-- **Miri side of `f16` / `f128` fail-closed correspondence (`Cast.cast`)**:
1. When `srcTy` is `f16` (`TyId 30`) or `f128` (`TyId 33`), `Cast.cast` rejects the source
   in `h.typeInfo` with `StepError.unsupported` for **any** `srcOp` (even before reading it).
2. When `srcTy` is a modeled float or integer (`IsFloatCastScalarTy srcTy`) holding an
   initialized scalar `msc` of matching byte width and `castTy` is `f16` or `f128`,
   `Cast.cast` rejects `castTy` in `h.typeInfo` with `StepError.unsupported`. -/
theorem cast_f16_f128_unsupported (layouts : LayoutTable) (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    (destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv) (st : AnnealStepState) :
    (∀ {kind : CastKind} {fTy castTy : Ty}
      (_hk : isFloatCastKind (translateCastKind kind) = true)
      (_hf : fTy.kind = .float .f16 ∨ fTy.kind = .float .f128)
      (srcOp : Miri.Interpreter.Operand AnnealProv),
      ∃ msg, Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨srcOp, translateTy fTy layouts⟩ (translateCastKind kind) (encodeTyId castTy)
          ⟨destRef, translateTy castTy layouts⟩ st =
        .error (.unsupported msg) st) ∧
    (∀ {kind : CastKind} {srcTy fTy : Ty} {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
      (_hk : isFloatCastKind (translateCastKind kind) = true)
      (_hsrc : (kind = .intToFloat ∧ ∃ t, floatIntTargetOfTy? srcTy = some t) ∨
        ((kind = .floatToFloat ∨ kind = .floatToInt) ∧ ∃ f, ieeeFormatOfTy? srcTy = some f))
      (_hrel : ScalarRel sc msc)
      (_hsz : (translateTy srcTy layouts).layout.size = translateSizeBytes sc.sizeBytes)
      (_hf : fTy.kind = .float .f16 ∨ fTy.kind = .float .f128),
      ∃ msg, Miri.Interpreter.Cast.cast (annealCastHooksFloat layouts nondet chooseNaN) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩
          (translateCastKind kind) (encodeTyId fTy)
          ⟨destRef, translateTy fTy layouts⟩ st =
        .error (.unsupported msg) st) := by
  refine ⟨?_, ?_⟩
  · intro kind fTy castTy hk hf srcOp
    have hty_err : ∃ msg, castTypeInfoOfEncodedTyIdFloat (translateTy fTy layouts).ty =
        .error (.unsupported msg) := by
      rcases hf with h | h <;> (unfold translateTy encodeTyId; rw [h]; exact ⟨_, rfl⟩)
    obtain ⟨msg, hmsg⟩ := hty_err
    have hdst_ty : (translateTy castTy layouts).ty = encodeTyId castTy := rfl
    cases kind <;> simp only [translateCastKind, isFloatCastKind, Bool.false_eq_true] at hk <;>
    · unfold Miri.Interpreter.Cast.cast
      dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
      simp only [hdst_ty, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, pure_bind,
        hmsg, estate_throw_bind_float]
      exact ⟨msg, rfl⟩
  · intro kind srcTy fTy sc msc _hk hsrc hrel hsz hf
    have hty_err : ∃ msg, castTypeInfoOfEncodedTyIdFloat (encodeTyId fTy) =
        .error (.unsupported msg) := by
      rcases hf with h | h <;> (unfold encodeTyId; rw [h]; exact ⟨_, rfl⟩)
    obtain ⟨msg, hmsg⟩ := hty_err
    have hdst_ty : (translateTy fTy layouts).ty = encodeTyId fTy := rfl
    rcases hsrc with ⟨rfl, t, ht⟩ | ⟨hfk, f, hfmt⟩
    · rw [translateTy_of_floatIntTargetOfTy? ht layouts] at hsz ⊢
      unfold Miri.Interpreter.Cast.cast
      dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
      simp only [hdst_ty, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
        castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId, pure_bind, annealReadImmediate_scalar,
        hmsg, estate_throw_bind_float]
      exact ⟨msg, rfl⟩
    · rw [translateTy_of_ieeeFormatOfTy? hfmt layouts] at hsz ⊢
      have hb := sizeBytes_of_float_layout hrel.validBytes hsz
      rcases hfk with rfl | rfl <;>
      · unfold Miri.Interpreter.Cast.cast
        dsimp only [annealCastHooksFloat, annealCastHooks, translateCastKind]
        simp only [hdst_ty, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
          castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, annealReadImmediate_scalar,
          floatOps_readBits_annealFloat nondet chooseNaN f hrel hb,
          hmsg, estate_throw_bind_float]
        exact ⟨msg, rfl⟩

/-- **Two-machine real-step fail-closed theorem on `f16` / `f128` sources**: on any
initialized `f16` or `f128` local `_s`, BOTH Anneal's `stepMirFn` (`MirStepNode.unsupported`)
and `lean-miri`'s `Step.step` under `annealStepHooksFloat` (`.error (.unsupported msg)`)
fail closed! -/
theorem step_cast_f16_f128_source_fail_closed
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hk : isFloatCastKind (translateCastKind kind) = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hf : srcDecl.ty.kind = .float .f16 ∨ srcDecl.ty.kind = .float .f128)
    (hdst_enc : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts)
    {v : Value} (hinit : get? s.frame.locals srcIdx = some (.init v)) :
    stepMirFn body s = MirStepNode.unsupported ∧
      ∃ m' msg,
        Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
          (m', .error (.unsupported msg)) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, _, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  rw [hinit] at hslot_s; injection hslot_s with hs_eq; subst hs_eq
  have hlive_s : ∃ opVal, mls_s.value = .live opVal := by
    cases hloc_s with
    | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
    | base hb =>
      cases hb with
      | immediate _ _ _ _ _ => exact ⟨_, rfl⟩
      | indirect _ _ _ _ _ _ => exact ⟨_, rfl⟩
  obtain ⟨opVal, hms_live⟩ := hlive_s
  have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live opVal, mls_s.layout⟩ := by
    rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_live; subst hms_live; rfl
  have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
    (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  obtain ⟨msg, hcast_err⟩ := (cast_f16_f128_unsupported body.layouts nondet chooseNaN
    (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfb]⟩ }).1 hk hf opVal
  rw [← hdst_enc] at hcast_err
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hk (.copy ⟨srcIdx, .nil⟩) castTy span m
  have hm_err : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
      ({ m with stack := ⟨#[tfb]⟩ }, .error (.unsupported msg)) := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
      show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
  have ha_unsup : stepMirFn body s = MirStepNode.unsupported := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt
    have hrv_eq : evalRvalue s.frame.locals (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts =
        evalFloatCastRvalue s.frame.locals kind (.copy ⟨srcIdx, .nil⟩) castTy s.memory
          body.localDecls body.layouts := by
      cases kind <;> first | rfl | cases hk
    dsimp only []; rw [hrv_eq]
    unfold evalFloatCastRvalue evalOperand readProjectedValue
    dsimp only []; rw [hinit]; dsimp only []
    rw [operandTy_copy_local hdecl_src,
      (evalFloatCast_f16_f128_none kind castTy body.layouts v hf).1]
  exact ⟨ha_unsup, _, msg,
    miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

/-- **`f16` / `f128` uninitialized-source failure-kind divergence**: on `_d = copy _s as T` with
an *uninitialized* `f16` / `f128` local `_s`, Anneal reports UB (`evalOperand` rejects the
uninitialized read before `evalFloatCast` is consulted), whereas `lean-miri` evaluates the
operand successfully and `Cast.cast` checks the source `typeInfo` (`enforceValidity`) before
reading it, failing closed with `StepError.unsupported`. Both machines fail, but no
`StepRelLM3_1` constructor relates `.fail .ub` to `.unsupported`, so the initialization premise
of `step_cast_f16_f128_source_fail_closed` cannot be dropped. -/
theorem step_cast_f16_f128_uninit_source_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hk : isFloatCastKind (translateCastKind kind) = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hf : srcDecl.ty.kind = .float .f16 ∨ srcDecl.ty.kind = .float .f128)
    (hdst_enc : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts)
    (huninit : get? s.frame.locals srcIdx = some .uninit) :
    stepMirFn body s = MirStepNode.fail .ub ∧
      (∃ m' msg,
        Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
          (m', .error (.unsupported msg))) ∧
      ¬ StepRelLM3_1 body m allocMap (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, _, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  rw [huninit] at hslot_s; injection hslot_s with hs_eq; subst hs_eq
  have hlive_s : ∃ opVal, mls_s.value = .live opVal := by
    cases hloc_s with
    | base hb =>
      cases hb with
      | immediate _ _ _ _ _ => exact ⟨_, rfl⟩
      | indirect _ _ _ _ _ _ => exact ⟨_, rfl⟩
  obtain ⟨opVal, hms_live⟩ := hlive_s
  have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live opVal, mls_s.layout⟩ := by
    rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_live; subst hms_live; rfl
  have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
    (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  obtain ⟨msg, hcast_err⟩ := (cast_f16_f128_unsupported body.layouts nondet chooseNaN
    (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfb]⟩ }).1 hk hf opVal
  rw [← hdst_enc] at hcast_err
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hk (.copy ⟨srcIdx, .nil⟩) castTy span m
  have hm_err : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
      ({ m with stack := ⟨#[tfb]⟩ }, .error (.unsupported msg)) := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
      show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
  have hm_step := miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
    hm_err
  have ha_ub : stepMirFn body s = MirStepNode.fail .ub := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt
    have hrv_eq : evalRvalue s.frame.locals (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts =
        evalFloatCastRvalue s.frame.locals kind (.copy ⟨srcIdx, .nil⟩) castTy s.memory
          body.localDecls body.layouts := by
      cases kind <;> first | rfl | cases hk
    dsimp only []; rw [hrv_eq]
    unfold evalFloatCastRvalue evalOperand
    dsimp only []; rw [huninit]
  refine ⟨ha_ub, ⟨_, msg, hm_step⟩, fun hrel => ?_⟩
  rw [ha_ub, hm_step] at hrel
  cases hrel

/-- **Target `f16` / `f128` real-step fail-closed theorem (`_d = copy _s as castTy`)**: when
`_s` is an initialized immediate local of a modeled `f32`/`f64`/integer type matching `kind` and
`castTy` is `f16` or `f128`, BOTH Anneal (`MirStepNode.unsupported`) and `lean-miri`
(`.error (.unsupported msg)`) fail closed! -/
theorem step_cast_f16_f128_target_copy_fail_closed
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hk : isFloatCastKind (translateCastKind kind) = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_kind : (kind = .intToFloat ∧ ∃ t, floatIntTargetOfTy? srcDecl.ty = some t) ∨
      ((kind = .floatToFloat ∨ kind = .floatToInt) ∧ ∃ f, ieeeFormatOfTy? srcDecl.ty = some f))
    (hf : castTy.kind = .float .f16 ∨ castTy.kind = .float .f128)
    (hdst_enc : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts)
    {sc : MirAst.ScalarInt} (hinit : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx) :
    stepMirFn body s = MirStepNode.unsupported ∧
      ∃ m' msg,
        Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
          (m', .error (.unsupported msg)) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
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
  have hsrc_scalar : IsFloatCastScalarTy srcDecl.ty := by
    rcases hsrc_kind with ⟨_, t, ht⟩ | ⟨_, f, hfmt⟩
    · exact Or.inr ⟨t, ht⟩
    · exact Or.inl ⟨f, hfmt⟩
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := (himm_src tf hframes).cache_layout hlt_d _
  rcases hloc_s.floatCast_immediate_cases hsrc_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz, hms⟩
  · rw [hss, hinit] at hslot_s; cases hslot_s
  · rw [hss, hinit] at hslot_s; cases hslot_s
  · rw [hss, hinit] at hslot_s; cases hslot_s
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
    obtain ⟨msg, hcast_err⟩ := (cast_f16_f128_unsupported body.layouts nondet chooseNaN
      (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfb]⟩ }).2
      hk hsrc_kind hrel hsz hf
    rw [← hdst_enc] at hcast_err
    have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
      chooseNaN ⟨dstIdx, .nil⟩ kind hk (.copy ⟨srcIdx, .nil⟩) castTy span m
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.unsupported msg)) := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
    have ha_unsup : stepMirFn body s = MirStepNode.unsupported := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]
      unfold evalStmt
      have hrv_eq : evalRvalue s.frame.locals (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
          body.localDecls body.layouts =
          evalFloatCastRvalue s.frame.locals kind (.copy ⟨srcIdx, .nil⟩) castTy s.memory
            body.localDecls body.layouts := by
        cases kind <;> first | rfl | cases hk
      dsimp only []; rw [hrv_eq]
      unfold evalFloatCastRvalue evalOperand readProjectedValue
      dsimp only []; rw [hinit]; dsimp only []
      rw [operandTy_copy_local hdecl_src,
        (evalFloatCast_f16_f128_none kind srcDecl.ty body.layouts (.scalar sc) hf).2]
    exact ⟨ha_unsup, _, msg,
      miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

/-- **Source-vs-target evaluation-order contrast on uninitialized `_s` (`_d = copy _s as f16/f128`)**:
unlike `step_cast_f16_f128_uninit_source_divergence` (where an uninitialized `f16`/`f128` **source**
diverges because `Cast.cast` checks `h.typeInfo choice source.layout.ty` before reading), when the
**source** `_s` has a modeled `f32`/`f64`/integer type (`IsFloatCastScalarTy srcDecl.ty`) and the
**target** `castTy` is `f16` or `f128`, `Cast.cast` calls `h.readImmediate choice source`
(`annealReadImmediate`) **before** `h.typeInfo choice target.ty` across all three cast kinds
(`.floatToFloat`, `.floatToInt`, `.intToFloat`), so **both** machines report UB and
`StepRelLM3_1.ub` **holds**! -/
theorem step_cast_f16_f128_uninit_target_ub_lockstep
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hk : isFloatCastKind (translateCastKind kind) = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_scalar : IsFloatCastScalarTy srcDecl.ty)
    (_hf : castTy.kind = .float .f16 ∨ castTy.kind = .float .f128)
    (hdst_enc : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts)
    (huninit : get? s.frame.locals srcIdx = some .uninit)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx) :
    stepMirFn body s = MirStepNode.fail .ub ∧
      StepRelLM3_1 body m allocMap (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
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
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := (himm_src tf hframes).cache_layout hlt_d _
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hdst_ty_id : (translateTy castTy body.layouts).ty = encodeTyId castTy := rfl
  rcases hloc_s.floatCast_immediate_cases hsrc_scalar (himm_s_tfa mls_s hmls_s) with
    ⟨hss, _⟩ | ⟨hss, hms⟩ | ⟨_, _, hss, _⟩
  · rw [hss, huninit] at hslot_s; cases hslot_s
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hcast_ub : Miri.Interpreter.Cast.cast
        (annealCastHooksFloat body.layouts nondet chooseNaN) () 16
        ⟨.immediate .uninit, translateTy srcDecl.ty body.layouts⟩
        (translateCastKind kind) (encodeTyId castTy)
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩ =
        throw (.undefinedBehavior "read of uninitialized local") := by
      rw [hdst_enc]
      rcases hsrc_scalar with ⟨f, hfmt⟩ | ⟨t, ht⟩
      · rw [translateTy_of_ieeeFormatOfTy? hfmt body.layouts]
        cases kind <;> simp only [translateCastKind, isFloatCastKind, Bool.false_eq_true] at hk <;>
        · unfold Miri.Interpreter.Cast.cast
          simp only [annealCastHooksFloat, annealCastHooks, hdst_ty_id, beq_self_eq_true, ↓reduceIte,
            castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true,
            annealReadImmediate_uninit_eq, estate_throw_bind_float, translateCastKind]
      · rw [translateTy_of_floatIntTargetOfTy? ht body.layouts]
        cases kind <;> simp only [translateCastKind, isFloatCastKind, Bool.false_eq_true] at hk <;>
        · unfold Miri.Interpreter.Cast.cast
          simp only [annealCastHooksFloat, annealCastHooks, hdst_ty_id, beq_self_eq_true, ↓reduceIte,
            castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId, pure_bind, Bool.false_eq_true,
            annealReadImmediate_uninit_eq, estate_throw_bind_float, translateCastKind]
    have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
      chooseNaN ⟨dstIdx, .nil⟩ kind hk (.copy ⟨srcIdx, .nil⟩) castTy span m
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_ub]; rfl
    have ha_ub : stepMirFn body s = MirStepNode.fail .ub := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt
      have hrv_eq : evalRvalue s.frame.locals (.cast kind (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
          body.localDecls body.layouts =
          evalFloatCastRvalue s.frame.locals kind (.copy ⟨srcIdx, .nil⟩) castTy s.memory
            body.localDecls body.layouts := by cases kind <;> first | rfl | cases hk
      dsimp only []; rw [hrv_eq]; unfold evalFloatCastRvalue evalOperand
      dsimp only []; rw [huninit]
    refine ⟨ha_ub, ?_⟩
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · rw [hss, huninit] at hslot_s; cases hslot_s

/-- **Constant-operand `f16` / `f128` real-step fail-closed theorem (`_d = const c as castTy`)**:
whenever either `c.ty` is `f16` / `f128` or `c.ty` is a modeled float/integer scalar matching `kind`
and `castTy` is `f16` / `f128`, `evalMirConstImmediate` evaluates `c` (because `layoutOfEncodedTyId`
handles `TyId` `30`/`33` as well as all modeled scalar `TyId`s), and BOTH Anneal
(`MirStepNode.unsupported`) and `lean-miri` (`.error (.unsupported msg)`) fail closed! -/
theorem step_cast_f16_f128_constant_fail_closed
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx : Local} {kind : CastKind} {c : ConstOperand} {castTy : Ty}
    {span : String}
    (hk : isFloatCastKind (translateCastKind kind) = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩)
    {dstDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_enc : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts)
    {sc : MirAst.ScalarInt} (hval : c.val = .scalar (.int sc))
    (hsz : ValidScalarBytes sc.sizeBytes) (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hlaysz : (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hboundary : (c.ty.kind = .float .f16 ∨ c.ty.kind = .float .f128) ∨
      (((kind = .intToFloat ∧ ∃ t, floatIntTargetOfTy? c.ty = some t) ∨
        ((kind = .floatToFloat ∨ kind = .floatToInt) ∧ ∃ f, ieeeFormatOfTy? c.ty = some f)) ∧
        (castTy.kind = .float .f16 ∨ castTy.kind = .float .f128))) :
    stepMirFn body s = MirStepNode.unsupported ∧
      ∃ m' msg,
        Miri.Interpreter.Step.step
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
          (m', .error (.unsupported msg)) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
  have hlay_c : layoutOfEncodedTyId (encodeTyId c.ty) body.layouts = translateTy c.ty body.layouts := by
    rcases hboundary with (hf | hf) | ⟨(⟨_, t, ht⟩ | ⟨_, f, hfmt⟩), _⟩
    · cases hty : c.ty; rw [hty] at hf; dsimp only at hf; subst hf; rfl
    · cases hty : c.ty; rw [hty] at hf; dsimp only at hf; subst hf; rfl
    · exact layoutOfEncodedTyId_floatCastScalar (Or.inr ⟨t, ht⟩) body.layouts
    · exact layoutOfEncodedTyId_floatCastScalar (Or.inl ⟨f, hfmt⟩) body.layouts
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
        Bool.false_eq_true, ↓reduceIte, htry, hlay_c]
  have hcast_both : ∃ msg,
      Miri.Interpreter.Cast.cast (annealCastHooksFloat body.layouts nondet chooseNaN) () 16
        ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        (translateCastKind kind) (encodeTyId castTy)
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } =
      .error (.unsupported msg) { m with stack := ⟨#[tfa]⟩ } := by
    rw [hdst_enc]
    rcases hboundary with hf_src | ⟨hsrc_kind, hf_dst⟩
    · exact (cast_f16_f128_unsupported body.layouts nondet chooseNaN
        (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfa]⟩ }).1 hk hf_src _
    · exact (cast_f16_f128_unsupported body.layouts nondet chooseNaN
        (.local 0 dstIdx none tf.localsIdentity) { m with stack := ⟨#[tfa]⟩ }).2
        hk hsrc_kind hrel hlaysz hf_dst
  obtain ⟨msg, hcast_err⟩ := hcast_both
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hk (.constant c) castTy span m
  have hm_err : Miri.Interpreter.Step.evalStatement
      (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.constant c) castTy), span⟩) m =
      ({ m with stack := ⟨#[tfa]⟩ }, .error (.unsupported msg)) := by
    rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
  have ha_unsup : stepMirFn body s = MirStepNode.unsupported := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt
    have hrv_eq : evalRvalue s.frame.locals (.cast kind (.constant c) castTy) s.memory
        body.localDecls body.layouts =
        evalFloatCastRvalue s.frame.locals kind (.constant c) castTy s.memory
          body.localDecls body.layouts := by
      cases kind <;> first | rfl | cases hk
    dsimp only []; rw [hrv_eq]
    unfold evalFloatCastRvalue
    have hop : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals body.localDecls s.memory.callStack =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [hop]; dsimp only []
    rw [show operandTy body.localDecls body.layouts (.constant c) = some c.ty from rfl]
    rcases hboundary with hf_src | ⟨_, hf_dst⟩
    · rw [(evalFloatCast_f16_f128_none kind castTy body.layouts (.scalar sc) hf_src).1]
    · rw [(evalFloatCast_f16_f128_none kind c.ty body.layouts (.scalar sc) hf_dst).2]
  exact ⟨ha_unsup, _, msg,
    miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

/-- **Move-operand source `f16` / `f128` 3-way step boundary (`_d = move _s as castTy`)**:
complete trichotomy over the `LocalSlot` state of an `f16` / `f128` source `_s`:
1. `.init v`: BOTH Anneal (`MirStepNode.unsupported`) and `lean-miri` (`.error (.unsupported msg)`)
   fail closed;
2. `.uninit`: Anneal reports UB (`MirStepNode.fail .ub`) whereas `lean-miri` deinitializes `_s` and
   checks `Cast.cast` source `typeInfo` before `readImmediate`, failing closed with
   `.error (.unsupported msg)` (`¬ StepRelLM3_1`);
3. `.dead`: `annealEvalOperand_move_dead` fires *before* `Cast.cast`, so BOTH Anneal and `lean-miri`
   report UB in lockstep (`StepRelLM3_1.ub`)! -/
theorem step_cast_f16_f128_move_source_boundary
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hk : isFloatCastKind (translateCastKind kind) = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hf : srcDecl.ty.kind = .float .f16 ∨ srcDecl.ty.kind = .float .f128)
    (hdst_enc : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts) :
    ((∃ v, get? s.frame.locals srcIdx = some (.init v)) →
      stepMirFn body s = MirStepNode.unsupported ∧
        ∃ m' msg,
          Miri.Interpreter.Step.step
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
            (m', .error (.unsupported msg))) ∧
    (get? s.frame.locals srcIdx = some .uninit →
      stepMirFn body s = MirStepNode.fail .ub ∧
        (∃ m' msg,
          Miri.Interpreter.Step.step
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
            (m', .error (.unsupported msg))) ∧
        ¬ StepRelLM3_1 body m allocMap (stepMirFn body s)
          (Miri.Interpreter.Step.step
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m)) ∧
    (get? s.frame.locals srcIdx = some .dead →
      stepMirFn body s = MirStepNode.fail .ub ∧
        StepRelLM3_1 body m allocMap (stepMirFn body s)
          (Miri.Interpreter.Step.step
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m)) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, _, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hk (.move ⟨srcIdx, .nil⟩) castTy span m
  refine ⟨fun ⟨v, hinit⟩ => ?_, fun huninit => ?_, fun hdead => ?_⟩
  · rw [hinit] at hslot_s; injection hslot_s with hs_eq; subst hs_eq
    have hlive_s : ∃ opVal, mls_s.value = .live opVal := by
      cases hloc_s with
      | rawPtr _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
      | base hb =>
        cases hb with
        | immediate _ _ _ _ _ => exact ⟨_, rfl⟩
        | indirect _ _ _ _ _ _ => exact ⟨_, rfl⟩
    obtain ⟨opVal, hms_live⟩ := hlive_s
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live opVal, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_live; subst hms_live; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    obtain ⟨msg, hcast_err⟩ := (cast_f16_f128_unsupported body.layouts nondet chooseNaN
      (.local 0 dstIdx none tf.localsIdentity)
      { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ }).1 hk hf opVal
    rw [← hdst_enc] at hcast_err
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
          .error (.unsupported msg)) := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
    obtain ⟨hlt_af_s, _⟩ := List.getElem?_eq_some_iff.mp
      (by rw [← get?_eq_getElem?]; exact hinit)
    have ha_unsup : stepMirFn body s = MirStepNode.unsupported := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt
      have hrv_eq : evalRvalue s.frame.locals (.cast kind (.move ⟨srcIdx, .nil⟩) castTy) s.memory
          body.localDecls body.layouts =
          evalFloatCastRvalue s.frame.locals kind (.move ⟨srcIdx, .nil⟩) castTy s.memory
            body.localDecls body.layouts := by cases kind <;> first | rfl | cases hk
      dsimp only []; rw [hrv_eq]; unfold evalFloatCastRvalue evalOperand
      dsimp only []; rw [hinit, set?_eq_some_set hlt_af_s]; dsimp only []
      rw [operandTy_move_local hdecl_src,
        (evalFloatCast_f16_f128_none kind castTy body.layouts v hf).1]
    exact ⟨ha_unsup, _, msg,
      miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩
  · rw [huninit] at hslot_s; injection hslot_s with hs_eq; subst hs_eq
    have hlive_s : ∃ opVal, mls_s.value = .live opVal := by
      cases hloc_s with
      | base hb =>
        cases hb with
        | immediate _ _ _ _ _ => exact ⟨_, rfl⟩
        | indirect _ _ _ _ _ _ => exact ⟨_, rfl⟩
    obtain ⟨opVal, hms_live⟩ := hlive_s
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live opVal, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_live; subst hms_live; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    obtain ⟨msg, hcast_err⟩ := (cast_f16_f128_unsupported body.layouts nondet chooseNaN
      (.local 0 dstIdx none tf.localsIdentity)
      { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ }).1 hk hf opVal
    rw [← hdst_enc] at hcast_err
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
          .error (.unsupported msg)) := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
    have hm_step := miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
      hm_err
    have ha_ub : stepMirFn body s = MirStepNode.fail .ub := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt
      have hrv_eq : evalRvalue s.frame.locals (.cast kind (.move ⟨srcIdx, .nil⟩) castTy) s.memory
          body.localDecls body.layouts =
          evalFloatCastRvalue s.frame.locals kind (.move ⟨srcIdx, .nil⟩) castTy s.memory
            body.localDecls body.layouts := by cases kind <;> first | rfl | cases hk
      dsimp only []; rw [hrv_eq]; unfold evalFloatCastRvalue evalOperand
      dsimp only []; rw [huninit]
    refine ⟨ha_ub, ⟨_, msg, hm_step⟩, fun hrel => ?_⟩
    rw [ha_ub, hm_step] at hrel
    cases hrel
  · rw [hdead] at hslot_s; injection hslot_s with hs_eq; subst hs_eq
    have hdead_s : mls_s.value = .dead := by
      cases hloc_s with
      | base hb =>
        cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨hs, _⟩ | ⟨_, hs, _⟩ <;> cases hs
        | indirect _ _ _ _ hnd _ => exact absurd rfl hnd
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hdead_s; subst hdead_s; rfl
    have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
        show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    have ha_ub : stepMirFn body s = MirStepNode.fail .ub := by
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]; unfold evalStmt
      have hrv_eq : evalRvalue s.frame.locals (.cast kind (.move ⟨srcIdx, .nil⟩) castTy) s.memory
          body.localDecls body.layouts =
          evalFloatCastRvalue s.frame.locals kind (.move ⟨srcIdx, .nil⟩) castTy s.memory
            body.localDecls body.layouts := by cases kind <;> first | rfl | cases hk
      dsimp only []; rw [hrv_eq]; unfold evalFloatCastRvalue evalOperand
      dsimp only []; rw [hdead]
    refine ⟨ha_ub, ?_⟩
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _

/-- **Move-operand target `f16` / `f128` step boundary (`_d = move _s as f16/f128`)**: on an
immediate modeled `f32`/`f64`/integer source `_s` matching `kind` and target `f16` / `f128`,
1. when `_s` holds an initialized scalar, BOTH Anneal (`MirStepNode.unsupported`) and `lean-miri`
   (`.error (.unsupported msg)`) fail closed;
2. when `_s` is `.uninit` or `.dead`, BOTH Anneal (`MirStepNode.fail .ub`) and `lean-miri` report
   UB in lockstep (`StepRelLM3_1.ub`) because `Cast.cast` reads the source immediate *before*
   consulting `h.typeInfo choice target.ty`! -/
theorem step_cast_f16_f128_move_target_boundary
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    (nondet : Bool)
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits → Miri.Interpreter.RvalueM AnnealStepState Nat)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {kind : CastKind} {castTy : Ty} {span : String}
    (hk : isFloatCastKind (translateCastKind kind) = true)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_kind : (kind = .intToFloat ∧ ∃ t, floatIntTargetOfTy? srcDecl.ty = some t) ∨
      ((kind = .floatToFloat ∨ kind = .floatToInt) ∧ ∃ f, ieeeFormatOfTy? srcDecl.ty = some f))
    (hf : castTy.kind = .float .f16 ∨ castTy.kind = .float .f128)
    (hdst_enc : translateTy dstDecl.ty body.layouts = translateTy castTy body.layouts)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx) :
    ((∃ sc, get? s.frame.locals srcIdx = some (.init (.scalar sc))) →
      stepMirFn body s = MirStepNode.unsupported ∧
        ∃ m' msg,
          Miri.Interpreter.Step.step
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m =
            (m', .error (.unsupported msg))) ∧
    ((get? s.frame.locals srcIdx = some .uninit ∨ get? s.frame.locals srcIdx = some .dead) →
      stepMirFn body s = MirStepNode.fail .ub ∧
        StepRelLM3_1 body m allocMap (stepMirFn body s)
          (Miri.Interpreter.Step.step
            (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) () m)) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
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
  have hsrc_scalar : IsFloatCastScalarTy srcDecl.ty := by
    rcases hsrc_kind with ⟨_, t, ht⟩ | ⟨_, f, hfmt⟩
    · exact Or.inr ⟨t, ht⟩
    · exact Or.inl ⟨f, hfmt⟩
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := (himm_src tf hframes).cache_layout hlt_d _
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hdst_ty_id : (translateTy castTy body.layouts).ty = encodeTyId castTy := rfl
  have hm_stmt := evalStatement_assign_floatCast_eq body.localDecls body.layouts nondet
    chooseNaN ⟨dstIdx, .nil⟩ kind hk (.move ⟨srcIdx, .nil⟩) castTy span m
  have hrv_eq : evalRvalue s.frame.locals (.cast kind (.move ⟨srcIdx, .nil⟩) castTy) s.memory
      body.localDecls body.layouts =
      evalFloatCastRvalue s.frame.locals kind (.move ⟨srcIdx, .nil⟩) castTy s.memory
        body.localDecls body.layouts := by cases kind <;> first | rfl | cases hk
  refine ⟨fun ⟨sc, hinit⟩ => ?_, fun hbad => ?_⟩
  · rcases hloc_s.floatCast_immediate_cases hsrc_scalar (himm_s_tfa mls_s hmls_s) with
      ⟨hss, _⟩ | ⟨hss, _⟩ | ⟨sc₀, msc, hss, hrel, hsz, hms⟩
    · rw [hss, hinit] at hslot_s; cases hslot_s
    · rw [hss, hinit] at hslot_s; cases hslot_s
    · rw [hss, hinit] at hslot_s; cases hslot_s
      have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
          ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
        rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
      have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
      obtain ⟨msg, hcast_err⟩ := (cast_f16_f128_unsupported body.layouts nondet chooseNaN
        (.local 0 dstIdx none tf.localsIdentity)
        { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ }).2
        hk hsrc_kind hrel hsz hf
      rw [← hdst_enc] at hcast_err
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
            .error (.unsupported msg)) := by
        rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
          show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_err]
      obtain ⟨hlt_af_s, _⟩ := List.getElem?_eq_some_iff.mp
        (by rw [← get?_eq_getElem?]; exact hinit)
      have ha_unsup : stepMirFn body s = MirStepNode.unsupported := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]; unfold evalStmt
        dsimp only []; rw [hrv_eq]; unfold evalFloatCastRvalue evalOperand
        dsimp only []; rw [hinit, set?_eq_some_set hlt_af_s]; dsimp only []
        rw [operandTy_move_local hdecl_src,
          (evalFloatCast_f16_f128_none kind srcDecl.ty body.layouts (.scalar sc) hf).2]
      exact ⟨ha_unsup, _, msg,
        miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩
  · rcases hloc_s.floatCast_immediate_cases hsrc_scalar (himm_s_tfa mls_s hmls_s) with
      ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨_, _, hss, _⟩
    · subst hss
      have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
        rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
      have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
          show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
      have ha_ub : stepMirFn body s = MirStepNode.fail .ub := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]; unfold evalStmt
        dsimp only []; rw [hrv_eq]; unfold evalFloatCastRvalue evalOperand
        dsimp only []; rw [hslot_s]
      refine ⟨ha_ub, ?_⟩
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      exact .ub _ _
    · subst hss
      have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
        rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
      have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have hcast_ub : Miri.Interpreter.Cast.cast
          (annealCastHooksFloat body.layouts nondet chooseNaN) () 16
          ⟨.immediate .uninit, translateTy srcDecl.ty body.layouts⟩
          (translateCastKind kind) (encodeTyId castTy)
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩ =
          throw (.undefinedBehavior "read of uninitialized local") := by
        rw [hdst_enc]
        rcases hsrc_scalar with ⟨f, hfmt⟩ | ⟨t, ht⟩
        · rw [translateTy_of_ieeeFormatOfTy? hfmt body.layouts]
          cases kind <;> simp only [translateCastKind, isFloatCastKind, Bool.false_eq_true] at hk <;>
          · unfold Miri.Interpreter.Cast.cast
            simp only [annealCastHooksFloat, annealCastHooks, hdst_ty_id, beq_self_eq_true, ↓reduceIte,
              castTypeInfoOfEncodedTyIdFloat_floatTyIdOf, pure_bind, Bool.false_eq_true,
              annealReadImmediate_uninit_eq, estate_throw_bind_float, translateCastKind]
        · rw [translateTy_of_floatIntTargetOfTy? ht body.layouts]
          cases kind <;> simp only [translateCastKind, isFloatCastKind, Bool.false_eq_true] at hk <;>
          · unfold Miri.Interpreter.Cast.cast
            simp only [annealCastHooksFloat, annealCastHooks, hdst_ty_id, beq_self_eq_true, ↓reduceIte,
              castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId, pure_bind, Bool.false_eq_true,
              annealReadImmediate_uninit_eq, estate_throw_bind_float, translateCastKind]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooksFloat body.localDecls body.layouts nondet chooseNaN) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast kind (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
            .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_stmt, show translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ from rfl,
          show translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ from rfl]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_ub]; rfl
      have ha_ub : stepMirFn body s = MirStepNode.fail .ub := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]; unfold evalStmt
        dsimp only []; rw [hrv_eq]; unfold evalFloatCastRvalue evalOperand
        dsimp only []; rw [hslot_s]
      refine ⟨ha_ub, ?_⟩
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      exact .ub _ _
    · rw [hss] at hslot_s
      rcases hbad with hun | hd
      · rw [hun] at hslot_s; cases hslot_s
      · rw [hd] at hslot_s; cases hslot_s

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

/-- **Subnormal `f64 → f32` ties-to-even & tie-overflow witnesses**:
1. `0x36A8_0000_0000_0000_f64` (`1.5 × 2⁻¹⁴⁹`, exact subnormal tie at odd `1`) rounds UP to
   even `2 × 2⁻¹⁴⁹` (`0x0000_0002_f32`) in both machines.
2. `0x36B4_0000_0000_0000_f64` (`2.5 × 2⁻¹⁴⁹`, exact subnormal tie at even `2`) rounds DOWN
   to even `2 × 2⁻¹⁴⁹` (`0x0000_0002_f32`) in both machines.
3. `0x47EF_FFFF_F000_0000_f64` (`f32::MAX + ½ ulp`) overflows to `+∞` (`0x7F80_0000_f32`)
   in both machines. -/
theorem miri_f64_to_f32_subnormal_ties_and_overflow_witnesses :
    (Miri.Interpreter.FloatBits.convert
        ⟨.binary64, BitVec.ofNat 128 0x36A8000000000000⟩ .binary32 =
      .ok ⟨.binary32, BitVec.ofNat 128 0x00000002⟩ ∧
      evalFloatToFloatRoundTiesToEven .binary64 .binary32 0x36A8000000000000 = 0x00000002) ∧
    (Miri.Interpreter.FloatBits.convert
        ⟨.binary64, BitVec.ofNat 128 0x36B4000000000000⟩ .binary32 =
      .ok ⟨.binary32, BitVec.ofNat 128 0x00000002⟩ ∧
      evalFloatToFloatRoundTiesToEven .binary64 .binary32 0x36B4000000000000 = 0x00000002) ∧
    (Miri.Interpreter.FloatBits.convert
        ⟨.binary64, BitVec.ofNat 128 0x47EFFFFFF0000000⟩ .binary32 =
      .ok ⟨.binary32, BitVec.ofNat 128 0x7F800000⟩ ∧
      evalFloatToFloatRoundTiesToEven .binary64 .binary32 0x47EFFFFFF0000000 = 0x7F800000) := by
  have h1 := floatBits_convert_eq .binary64 .binary32 0x36A8000000000000 (by decide)
  have he1 : evalFloatToFloatRoundTiesToEven .binary64 .binary32 0x36A8000000000000 = 0x00000002 := rfl
  rw [he1] at h1
  have h2 := floatBits_convert_eq .binary64 .binary32 0x36B4000000000000 (by decide)
  have he2 : evalFloatToFloatRoundTiesToEven .binary64 .binary32 0x36B4000000000000 = 0x00000002 := rfl
  rw [he2] at h2
  have h3 := floatBits_convert_eq .binary64 .binary32 0x47EFFFFFF0000000 (by decide)
  have he3 : evalFloatToFloatRoundTiesToEven .binary64 .binary32 0x47EFFFFFF0000000 = 0x7F800000 := rfl
  rw [he3] at h3
  exact ⟨⟨h1, he1⟩, ⟨h2, he2⟩, ⟨h3, he3⟩⟩

/-- **`isize` (`TyId 15`) and `usize` (`TyId 25`) 64-bit pointer-width witnesses** across
saturating `floatToInt` (`±∞`, `NaN`) and `roundTiesToEven` `intToFloat` (`usize::MAX`,
`isize::MIN`). -/
theorem miri_isize_usize_cast_witnesses :
    Miri.Interpreter.FloatBits.toInteger
        ⟨.binary64, BitVec.ofNat 128 0x7FF0000000000000⟩ 64 true = .ok (2 ^ 63 - 1) ∧
    Miri.Interpreter.FloatBits.toInteger
        ⟨.binary64, BitVec.ofNat 128 0xFFF0000000000000⟩ 64 true = .ok (-(2 ^ 63)) ∧
    Miri.Interpreter.FloatBits.toInteger
        ⟨.binary64, BitVec.ofNat 128 0x7FF0000000000000⟩ 64 false = .ok (2 ^ 64 - 1) ∧
    Miri.Interpreter.FloatBits.toInteger
        ⟨.binary64, BitVec.ofNat 128 0x7FF8000000000000⟩ 64 false = .ok 0 ∧
    Miri.Interpreter.FloatBits.fromInteger .binary64 (2 ^ 64 - 1) =
      .ok ⟨.binary64, BitVec.ofNat 128 0x43F0000000000000⟩ ∧
    Miri.Interpreter.FloatBits.fromInteger .binary32 (-(2 ^ 63)) =
      .ok ⟨.binary32, BitVec.ofNat 128 0xDF000000⟩ := by
  have h1 := floatBits_toInteger_eq .binary64 0x7FF0000000000000 (by decide) (.signed .isize) .bits64
  have he1 : floatToIntValue (decodeBits .binary64 0x7FF0000000000000)
      ((FloatIntTarget.signed .isize).minValue .bits64)
      ((FloatIntTarget.signed .isize).maxValue .bits64) = 2 ^ 63 - 1 := rfl
  rw [he1] at h1
  have h2 := floatBits_toInteger_eq .binary64 0xFFF0000000000000 (by decide) (.signed .isize) .bits64
  have he2 : floatToIntValue (decodeBits .binary64 0xFFF0000000000000)
      ((FloatIntTarget.signed .isize).minValue .bits64)
      ((FloatIntTarget.signed .isize).maxValue .bits64) = -(2 ^ 63) := rfl
  rw [he2] at h2
  have h3 := floatBits_toInteger_eq .binary64 0x7FF0000000000000 (by decide) (.unsigned .usize) .bits64
  have he3 : floatToIntValue (decodeBits .binary64 0x7FF0000000000000)
      ((FloatIntTarget.unsigned .usize).minValue .bits64)
      ((FloatIntTarget.unsigned .usize).maxValue .bits64) = 2 ^ 64 - 1 := rfl
  rw [he3] at h3
  have h4 := floatBits_toInteger_eq .binary64 0x7FF8000000000000 (by decide) (.unsigned .usize) .bits64
  have he4 : floatToIntValue (decodeBits .binary64 0x7FF8000000000000)
      ((FloatIntTarget.unsigned .usize).minValue .bits64)
      ((FloatIntTarget.unsigned .usize).maxValue .bits64) = 0 := rfl
  rw [he4] at h4
  have h5 := floatBits_fromInteger_intValueOfBits false 64 (2 ^ 64 - 1) .binary64
  have hv5 : intValueOfBits false 64 (2 ^ 64 - 1) = 2 ^ 64 - 1 := rfl
  have he5 : evalIntToFloatRoundTiesToEven false 64 (2 ^ 64 - 1) .binary64 = 0x43F0000000000000 := rfl
  rw [hv5, he5] at h5
  have h6 := floatBits_fromInteger_intValueOfBits true 64 (2 ^ 63) .binary32
  have hv6 : intValueOfBits true 64 (2 ^ 63) = -(2 ^ 63) := rfl
  have he6 : evalIntToFloatRoundTiesToEven true 64 (2 ^ 63) .binary32 = 0xDF000000 := rfl
  rw [hv6, he6] at h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **4-vs-6 candidate-list witness for signaling-NaN narrowing (`f64 → f32`)**:
* `0x7FF0_0000_0000_0001_f64` (`lower = 0`): `nanChoices` returns **4** candidates
  (suppressing `encode .binary32 false 255 0 = +∞`).
* `0x7FF0_0000_2000_0000_f64` (`lower = 1`): `nanChoices` returns **6** candidates, with the
  signaling `f32` NaN `0x7F80_0001` at index `4` (`isSignaling = .ok true`). -/
theorem miri_snan_f64_to_f32_nanChoices_4_vs_6 :
    (∃ c4,
      Miri.Interpreter.FloatBits.nanChoices .binary32
        [⟨.binary64, BitVec.ofNat 128 0x7FF0000000000001⟩] true = .ok c4 ∧
      c4.length = 4) ∧
    (∃ c6,
      Miri.Interpreter.FloatBits.nanChoices .binary32
        [⟨.binary64, BitVec.ofNat 128 0x7FF0000020000000⟩] true = .ok c6 ∧
      c6.length = 6 ∧
      c6[4]? = some ⟨.binary32, BitVec.ofNat 128 0x7F800001⟩ ∧
      Miri.Interpreter.FloatBits.isSignaling ⟨.binary32, BitVec.ofNat 128 0x7F800001⟩ = .ok true) := by
  have hd4 : decodeBits .binary64 0x7FF0000000000001 = .nan false false 1 := rfl
  have he4 : evalFloatToFloatRoundTiesToEven .binary64 .binary32 0x7FF0000000000001 = 0x7FC00000 := rfl
  obtain ⟨c4, hc4, _, _, hlen4⟩ := floatBits_nanChoices_nondet_exact .binary64 .binary32
    0x7FF0000000000001 (by decide) false false 1 hd4
  rw [he4] at hlen4
  simp only [show (0x7FC00000 % 2 ^ IeeeFormat.binary32.fractionBits) %
      2 ^ (IeeeFormat.binary32.fractionBits - 1) = 0 from rfl,
    ne_eq, not_true_eq_false, and_false, ↓reduceIte] at hlen4
  have hd6 : decodeBits .binary64 0x7FF0000020000000 = .nan false false 0x20000000 := rfl
  have he6 : evalFloatToFloatRoundTiesToEven .binary64 .binary32 0x7FF0000020000000 = 0x7FC00001 := rfl
  obtain ⟨c6, hc6, _, _, hlen6⟩ := floatBits_nanChoices_nondet_exact .binary64 .binary32
    0x7FF0000020000000 (by decide) false false 0x20000000 hd6
  rw [he6] at hlen6
  have hlow6 : (0x7FC00001 % 2 ^ IeeeFormat.binary32.fractionBits) %
      2 ^ (IeeeFormat.binary32.fractionBits - 1) = 1 := rfl
  have henc6 : encodeBits .binary32 false (2 ^ IeeeFormat.binary32.exponentBits - 1) 1 = 0x7F800001 := rfl
  rw [hlow6, henc6] at hlen6
  simp only [ne_eq, Nat.one_ne_zero, not_false_eq_true, and_self, ↓reduceIte] at hlen6
  exact ⟨⟨c4, hc4, hlen4⟩, ⟨c6, hc6, hlen6⟩⟩

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

/-! ### Multi-step `copy` + `move` + `isize`/`usize` + use-after-move `.ub` witness -/

private theorem floatWit_step_of_stepRel
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {s' : MachineState}
    (hsim : StepRelLM3_1 body m allocMap aRes mRes)
    (ha : aRes = .step s') :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM3_1 body s' m' allocMap := by
  cases hsim with
  | step _ m' hrel =>
    cases ha
    exact ⟨m', rfl, hrel⟩
  | retRoot _ _ _ _ _ _ _ _ _ => cases ha
  | ub _ _ => cases ha

private theorem floatWit_ub_of_stepRel
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (hsim : StepRelLM3_1 body m allocMap aRes mRes)
    (ha : aRes = .fail .ub) :
    ∃ m' msg, mRes = (m', .error (.undefinedBehavior msg)) := by
  cases hsim with
  | ub m' msg => exact ⟨m', msg, rfl⟩
  | step _ _ _ => cases ha
  | retRoot _ _ _ _ _ _ _ _ _ => cases ha

def floatWitUsizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
def floatWitIsizeTy : Ty := { kind := .int .isize, layoutIdx := 0 }
def floatWitF32Ty : Ty := { kind := .float .f32, layoutIdx := 0 }
def floatWitUsizeDecl : LocalDecl := { mutability := .mut, ty := floatWitUsizeTy, debugName := none }
def floatWitIsizeDecl : LocalDecl := { mutability := .mut, ty := floatWitIsizeTy, debugName := none }
def floatWitF64Decl : LocalDecl := { mutability := .mut, ty := floatWitF64Ty, debugName := none }
def floatWitF32Decl : LocalDecl := { mutability := .mut, ty := floatWitF32Ty, debugName := none }

def floatWitU64Layout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def floatWitNeg42IsizeConst : ConstOperand :=
  { ty := floatWitIsizeTy, val := .scalar (.int ⟨0xFFFFFFFFFFFFFFD6, 8⟩) }

/-- 4-statement `Runtime(PostCleanup)` body exercising all 3 float-cast kinds, `isize` (`TyId 15`)
and `usize` (`TyId 25`), `.constant` / `.copy` / `.move`, multi-step chaining, AND use-after-move
`.ub` lockstep:
0. `_2 = const (-42_isize) as f64` (`intToFloat` → `0xC045000000000000`);
1. `_3 = copy _2 as f32` (`floatToFloat` → `0xC2280000`, keeping `_2` initialized);
2. `_1 = move _3 as isize` (`floatToInt` → `-42_isize`, deinitializing `_3` to `.uninit`);
3. `_0 = copy _3 as usize` (`floatToInt` on moved `.uninit` `_3` → UB in BOTH machines!). -/
def floatWitPipelineBody : CapturedMir where
  defPath := "float_cast_lm_witness::pipeline"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [floatWitUsizeDecl, floatWitIsizeDecl, floatWitF64Decl, floatWitF32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.cast .intToFloat (.constant floatWitNeg42IsizeConst) floatWitF64Ty)),
        mkStmt (.assign (local_ 3) (.cast .floatToFloat (.copy (local_ 2)) floatWitF32Ty)),
        mkStmt (.assign (local_ 1) (.cast .floatToInt (.move (local_ 3)) floatWitIsizeTy)),
        mkStmt (.assign (local_ 0) (.cast .floatToInt (.copy (local_ 3)) floatWitUsizeTy))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm12FnAbi floatWitU64Layout
  layouts := emptyLayoutTable
  allocations := []

def floatWitPipelineAnnealPre : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit, .uninit, .uninit] }
    memory := (initMachineState floatWitPipelineBody []).memory }

def floatWitPipelineMiriFramePre :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody floatWitPipelineBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy floatWitUsizeTy) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def floatWitPipelineMiriPre : AnnealStepState :=
  { stack := ⟨#[floatWitPipelineMiriFramePre]⟩, machine := AnnealMachine.empty }

theorem floatWitPipeline_stateRel_pre :
    StateRelLM3_1 floatWitPipelineBody floatWitPipelineAnnealPre floatWitPipelineMiriPre [] := by
  refine (StateRel.mk floatWitPipelineMiriFramePre rfl rfl ⟨translateTy floatWitUsizeTy, rfl⟩ ?_
    rfl rfl rfl rfl rfl (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | _ + 4 => rintro ⟨⟩)).toLM3_1
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i _ slot mls hdecl hslot hmls
  match i with
  | 0 | 1 | 2 | 3 =>
    have hs : slot = .uninit := by simpa [floatWitPipelineAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [floatWitPipelineMiriFramePre] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 4 => simp [floatWitPipelineBody, get?] at hdecl

theorem floatWitPipeline_all_imm_pre :
    ∀ tf, floatWitPipelineMiriPre.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁; injection h₁ with h₂; subst h₂
  match k with
  | 0 | 1 | 2 | 3 =>
    simp [floatWitPipelineMiriFramePre] at hmls; subst hmls; cases hmp
  | _ + 4 => simp [floatWitPipelineMiriFramePre] at hmls

private def floatWitPipelineS1 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 1,
               locals := [.uninit, .uninit, .init (.scalar ⟨0xC045000000000000, 8⟩), .uninit] }
    memory := floatWitPipelineAnnealPre.memory }

private def floatWitPipelineS2 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 2,
               locals := [.uninit, .uninit, .init (.scalar ⟨0xC045000000000000, 8⟩),
                          .init (.scalar ⟨0xC2280000, 4⟩)] }
    memory := floatWitPipelineAnnealPre.memory }

private def floatWitPipelineS3 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 3,
               locals := [.uninit, .init (.scalar ⟨0xFFFFFFFFFFFFFFD6, 8⟩),
                          .init (.scalar ⟨0xC045000000000000, 8⟩), .uninit] }
    memory := floatWitPipelineAnnealPre.memory }

set_option maxRecDepth 200000 in
private theorem floatWitPipeline_steps :
    stepMirFn floatWitPipelineBody floatWitPipelineAnnealPre = .step floatWitPipelineS1 ∧
    stepMirFn floatWitPipelineBody floatWitPipelineS1 = .step floatWitPipelineS2 ∧
    stepMirFn floatWitPipelineBody floatWitPipelineS2 = .step floatWitPipelineS3 ∧
    stepMirFn floatWitPipelineBody floatWitPipelineS3 = .fail .ub :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **4-step chained non-vacuity witness** instantiating `step_cast_float_constant_simulation`,
`step_cast_float_copy_simulation`, `step_cast_float_move_simulation` across `isize` (`TyId 15`)
and `usize` (`TyId 25`), AND culminating in a 4th-step use-after-move `.ub` lockstep proof! -/
theorem floatWit_copy_move_isize_and_ub :
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState) (ubMsg : String),
      let b := floatWitPipelineBody
      let hooks := annealStepHooksFloat b.localDecls b.layouts
      stepMirFn b floatWitPipelineAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () floatWitPipelineMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [] ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨0xC045000000000000, 8⟩)) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [] ∧
      get? s₂.frame.locals 3 = some (.init (.scalar ⟨0xC2280000, 4⟩)) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [] ∧
      get? s₃.frame.locals 1 = some (.init (.scalar ⟨0xFFFFFFFFFFFFFFD6, 8⟩)) ∧
      get? s₃.frame.locals 3 = some .uninit ∧
      stepMirFn b s₃ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .error (.undefinedBehavior ubMsg)) := by
  have hphase : ∀ p, floatWitPipelineBody.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨hs₁, hs₂, hs₃, hs₄⟩ := floatWitPipeline_steps
  -- Step 1: `_2 = const (-42_isize) as f64`
  have hr₁ := step_cast_float_constant_simulation floatWitPipeline_stateRel_pre hphase
    rfl rfl rfl (.intToFloat (t := .signed .isize) rfl rfl) rfl rfl
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide) rfl
    (fun tf htf => floatWitPipeline_all_imm_pre tf htf 2)
  obtain ⟨m₁, hm₁, hrel₁⟩ := floatWit_step_of_stepRel hr₁ hs₁
  have hp₁ := step_cast_float_constant_anyLocal_preserves floatWitPipeline_stateRel_pre
    true annealChooseQuietedNaN (Or.inl ⟨rfl, rfl⟩)
    rfl rfl rfl (.intToFloat (t := .signed .isize) rfl rfl) rfl rfl
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide) rfl
    (fun h => nomatch h)
    (fun tf htf => Or.inl (floatWitPipeline_all_imm_pre tf htf 2)) rfl m₁ hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k => hp₁.2 _ tf₁ rfl htf₁ k (floatWitPipeline_all_imm_pre _ rfl k)
  -- Step 2: `_3 = copy _2 as f32`
  have hr₂ := step_cast_float_copy_simulation hrel₁ hphase rfl rfl rfl rfl
    (.floatToFloat rfl rfl) rfl
    (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3, himm₁ tf₁ htf₁ 2⟩)
  obtain ⟨m₂, hm₂, hrel₂⟩ := floatWit_step_of_stepRel hr₂ hs₂
  obtain ⟨tf₁_w, htf₁_w, _⟩ := id hrel₁
  have hp₂ := step_cast_float_copy_anyLocal_preserves hrel₁
    true annealChooseQuietedNaN (Or.inl ⟨rfl, rfl⟩)
    rfl rfl rfl rfl (.floatToFloat rfl rfl) rfl
    (fun h => nomatch h)
    (fun tf₁ htf₁ => Or.inl (himm₁ tf₁ htf₁ 2))
    (fun tf₁ htf₁ => Or.inl (himm₁ tf₁ htf₁ 3)) rfl m₂ hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, IsImmediateFrameLocal tf₂ k :=
    fun tf₂ htf₂ k => hp₂.2 tf₁_w tf₂ htf₁_w htf₂ k (himm₁ tf₁_w htf₁_w k)
  -- Step 3: `_1 = move _3 as isize`
  have hr₃ := step_cast_float_move_simulation hrel₂ hphase rfl rfl rfl rfl
    (.floatToInt (t := .signed .isize) rfl rfl) rfl
    (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 1, himm₂ tf₂ htf₂ 3⟩)
  obtain ⟨m₃, hm₃, hrel₃⟩ := floatWit_step_of_stepRel hr₃ hs₃
  obtain ⟨tf₂_w, htf₂_w, _⟩ := id hrel₂
  have hp₃ := step_cast_float_move_anyLocal_preserves hrel₂
    true annealChooseQuietedNaN (Or.inl ⟨rfl, rfl⟩)
    rfl rfl rfl rfl (.floatToInt (t := .signed .isize) rfl rfl) rfl
    (fun h => nomatch h)
    (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 3)
    (fun tf₂ htf₂ => Or.inl (himm₂ tf₂ htf₂ 1)) rfl m₃ hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, IsImmediateFrameLocal tf₃ k :=
    fun tf₃ htf₃ k => hp₃.2 tf₂_w tf₃ htf₂_w htf₃ k (himm₂ tf₂_w htf₂_w k)
  -- Step 4: `_0 = copy _3 as usize` (use-after-move `.ub` on `.uninit` `_3`!)
  have hr₄ := step_cast_float_copy_simulation hrel₃ hphase rfl rfl rfl rfl
    (.floatToInt (t := .unsigned .usize) rfl rfl) rfl
    (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 0, himm₃ tf₃ htf₃ 3⟩)
  obtain ⟨m₄, ubMsg, hm₄⟩ := floatWit_ub_of_stepRel hr₄ hs₄
  exact ⟨floatWitPipelineS1, floatWitPipelineS2, floatWitPipelineS3, m₁, m₂, m₃, m₄, ubMsg,
    hs₁, hm₁, hrel₁, rfl,
    hs₂, hm₂, hrel₂, rfl,
    hs₃, hm₃, hrel₃, rfl, rfl,
    hs₄, hm₄⟩

/-! ### Promoted (`allocMap`) memory-backed local + float-cast pipeline witness -/

def floatWitRawPtrMutI32Ty : Ty := { kind := .rawPtr .mut (.int .i32), layoutIdx := 0 }
def floatWitRawPtrMutI32Decl : LocalDecl :=
  { mutability := .mut, ty := floatWitRawPtrMutI32Ty, debugName := none }

def floatWitF64Layout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def floatWitAllocId1 : Miri.Memory.AllocId := ⟨1, by decide⟩

def floatWitScalar7I32 : Miri.Memory.ScalarInt := .ofUInt32 7

theorem floatWit_scalarRel7 : ScalarRel ⟨7, 4⟩ floatWitScalar7I32 :=
  ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩

/-- 3-statement `Runtime(PostCleanup)` body exercising mixed pointer promotion + memory-backed
float-cast reads AND memory-backed float-cast writes + Tree Borrows invalidation under a
single uniform `annealStepHooksFloat`:
0. `_2 = &raw mut _1` (promotes `_1 = 7_i32` into `allocMap = [e₁]` at `AllocId 1`);
1. `_0 = copy _1 as f64` (`step_cast_float_copy_anyLocal_simulation` reads memory-backed `_1`,
   producing `7.0_f64 = 0x401C000000000000` in `_0`);
2. `_1 = move _0 as i32` (`step_cast_float_move_anyLocal_simulation` writes directly into
   memory-backed `_1` and invalidates `e₁` via `updateAllocMapOnWrite [e₁] 1 none`, setting
   `e₁.perm` from `.active` to `.disabled`). -/
def floatWitPromotedBody : CapturedMir where
  defPath := "float_cast_lm_witness::promoted"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [floatWitF64Decl, floatWitI32Decl, floatWitRawPtrMutI32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 0) (.cast .intToFloat (.copy (local_ 1)) floatWitF64Ty)),
        mkStmt (.assign (local_ 1) (.cast .floatToInt (.move (local_ 0)) floatWitI32Ty))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm12FnAbi floatWitF64Layout
  layouts := emptyLayoutTable
  allocations := []

def floatWitPromotedAnnealPre : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.scalar ⟨7, 4⟩), .uninit] }
    memory := (initMachineState floatWitPromotedBody []).memory }

def floatWitPromotedMiriFramePre :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody floatWitPromotedBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy floatWitF64Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt floatWitScalar7I32))),
        layout := some (translateTy floatWitI32Ty) },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def floatWitPromotedMiriPre : AnnealStepState :=
  { stack := ⟨#[floatWitPromotedMiriFramePre]⟩, machine := AnnealMachine.empty }

theorem floatWitPromoted_stateRel_pre :
    StateRelLM3_1 floatWitPromotedBody floatWitPromotedAnnealPre floatWitPromotedMiriPre [] := by
  refine (StateRel.mk floatWitPromotedMiriFramePre rfl rfl ⟨translateTy floatWitF64Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | _ + 3 => rintro ⟨⟩)).toLM3_1
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 2 =>
    have hs : slot = .uninit := by simpa [floatWitPromotedAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [floatWitPromotedMiriFramePre] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = floatWitI32Decl := by simpa [floatWitPromotedBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨7, 4⟩) := by
      simpa [floatWitPromotedAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt floatWitScalar7I32))),
          layout := some (translateTy floatWitI32Ty) } := by
      simpa [floatWitPromotedMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy floatWitI32Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ floatWit_scalarRel7 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | _ + 3 => simp [floatWitPromotedBody, get?] at hdecl

theorem floatWitPromoted_all_imm_pre :
    ∀ tf, floatWitPromotedMiriPre.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁; injection h₁ with h₂; subst h₂
  match k with
  | 0 | 1 | 2 =>
    simp [floatWitPromotedMiriFramePre] at hmls; subst hmls; cases hmp
  | _ + 3 => simp [floatWitPromotedMiriFramePre] at hmls

private abbrev floatWitPromotedE1 : AllocMapEntry :=
  rawPtrAllocMapEntry floatWitPromotedBody.localDecls floatWitPromotedBody.layouts
    .mut 1 1 floatWitAllocId1

private def floatWitPromotedS1 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 1,
               locals := [.uninit, .init (.scalar ⟨7, 4⟩),
                          .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
    memory := { floatWitPromotedAnnealPre.memory with
                  borrows := [floatWitPromotedE1.toBorrowEntry], nextTag := 2 } }

private def floatWitPromotedS2 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 2,
               locals := [.init (.scalar ⟨0x401C000000000000, 8⟩), .init (.scalar ⟨7, 4⟩),
                          .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
    memory := floatWitPromotedS1.memory }

private def floatWitPromotedMap3 : List AllocMapEntry :=
  updateAllocMapOnWrite [floatWitPromotedE1] 1 none

private def floatWitPromotedS3 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 3,
               locals := [.uninit, .init (.scalar ⟨7, 4⟩),
                          .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
    memory := { floatWitPromotedS2.memory with
                  borrows := floatWitPromotedMap3.map AllocMapEntry.toBorrowEntry } }

set_option maxRecDepth 200000 in
private theorem floatWitPromoted_steps :
    stepMirFn floatWitPromotedBody floatWitPromotedAnnealPre = .step floatWitPromotedS1 ∧
    stepMirFn floatWitPromotedBody floatWitPromotedS1 = .step floatWitPromotedS2 ∧
    stepMirFn floatWitPromotedBody floatWitPromotedS2 = .step floatWitPromotedS3 :=
  ⟨rfl, rfl, rfl⟩

/-- **End-to-end 3-step promoted-local (`allocMap`) float-cast witness** under uniform
`annealStepHooksFloat`, exercising `step_float_eq_annealStepHooks_at_stmt`,
`step_cast_float_copy_anyLocal_simulation` (memory-backed read), and
`step_cast_float_move_anyLocal_simulation` (memory-backed write + `updateAllocMapOnWrite`
borrow invalidation). -/
theorem floatWit_promoted_allocMap_pipeline :
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let b := floatWitPromotedBody
      let hooks := annealStepHooksFloat b.localDecls b.layouts
      let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 floatWitAllocId1
      let map₃ := updateAllocMapOnWrite [e₁] 1 none
      stepMirFn b floatWitPromotedAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () floatWitPromotedMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [e₁] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [e₁] ∧
      get? s₂.frame.locals 0 = some (.init (.scalar ⟨0x401C000000000000, 8⟩)) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ map₃ ∧
      get? s₃.frame.locals 1 = some (.init (.scalar ⟨7, 4⟩)) ∧
      map₃ = [{ e₁ with perm := .disabled, allocDead := false }] := by
  have hphase : ∀ p, floatWitPromotedBody.phase ≠ .other p := fun _ h => nomatch h
  obtain ⟨hs₁, hs₂, hs₃⟩ := floatWitPromoted_steps
  have himm₀ : ∀ tf, floatWitPromotedMiriPre.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨floatWitPromoted_all_imm_pre tf htf 2, floatWitPromoted_all_imm_pre tf htf 1⟩
  -- Step 1: `_2 = &raw mut _1` (under `annealStepHooksFloat` via `step_float_eq_annealStepHooks_at_stmt`)
  have hm_eq₁ := step_float_eq_annealStepHooks_at_stmt floatWitPromoted_stateRel_pre
    true annealChooseQuietedNaN rfl rfl rfl
  have hr₁ := step_rawPtr_addrOf_lm3_1_simulation floatWitPromoted_stateRel_pre hphase
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inl ⟨.i32, rfl⟩))) (by decide) himm₀
    AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁_base, hrel₁⟩ := floatWit_step_of_stepRel hr₁ hs₁
  have hm₁ : Miri.Interpreter.Step.step
      (annealStepHooksFloat floatWitPromotedBody.localDecls floatWitPromotedBody.layouts) ()
      floatWitPromotedMiriPre = (m₁, .ok true) := hm_eq₁.trans hm₁_base
  have htag₀ : floatWitPromotedAnnealPre.memory.nextTag = 1 := rfl
  have hid₀ : (⟨floatWitPromotedMiriPre.machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = floatWitAllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ :=
    step_rawPtr_addrOf_preserves_supply floatWitPromoted_stateRel_pre
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inl ⟨.i32, rfl⟩))) (by decide) himm₀
      AllocIdSupplyReady.empty (by decide) (fun h => nomatch h) hm₁_base
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne => himm₁_step _ tf₁ rfl htf₁ k hne (floatWitPromoted_all_imm_pre _ rfl k)
  -- Step 2: `_0 = copy _1 as f64` (reads promoted `_1` in `allocMap = [e₁]`)
  have hmap₂_eq : updateAllocMapOnWrite [floatWitPromotedE1] 0 none = [floatWitPromotedE1] := rfl
  have hr₂ := step_cast_float_copy_anyLocal_simulation hrel₁ hphase rfl rfl rfl rfl
    (.intToFloat (t := .signed .i32) rfl rfl) rfl
    (fun _ _ => Or.inr ⟨floatWitPromotedE1, .head _, rfl⟩)
    (fun tf₁ htf₁ => Or.inl (himm₁ tf₁ htf₁ 0 (by decide)))
  rw [hmap₂_eq] at hr₂
  obtain ⟨m₂, hm₂, hrel₂⟩ := floatWit_step_of_stepRel hr₂ hs₂
  obtain ⟨tf₁_w, htf₁_w, _⟩ := id hrel₁
  have hp₂ := step_cast_float_copy_anyLocal_preserves hrel₁
    true annealChooseQuietedNaN (Or.inl ⟨rfl, rfl⟩)
    rfl rfl rfl rfl (.intToFloat (t := .signed .i32) rfl rfl) rfl
    (fun h => nomatch h)
    (fun _ _ => Or.inr ⟨floatWitPromotedE1, .head _, rfl⟩)
    (fun tf₁ htf₁ => Or.inl (himm₁ tf₁ htf₁ 0 (by decide))) rfl m₂ hm₂
  have himm₂_0 : ∀ tf₂, m₂.stack.frames = #[tf₂] → IsImmediateFrameLocal tf₂ 0 :=
    fun tf₂ htf₂ => hp₂.2 tf₁_w tf₂ htf₁_w htf₂ 0 (himm₁ tf₁_w htf₁_w 0 (by decide))
  -- Step 3: `_1 = move _0 as i32` (writes into promoted `_1`, invalidating `e₁`!)
  have hr₃ := step_cast_float_move_anyLocal_simulation hrel₂ hphase rfl rfl rfl rfl
    (.floatToInt (t := .signed .i32) rfl rfl) rfl
    himm₂_0
    (fun _ _ => Or.inr ⟨floatWitPromotedE1, .head _, rfl⟩)
  obtain ⟨m₃, hm₃, hrel₃⟩ := floatWit_step_of_stepRel hr₃ hs₃
  exact ⟨floatWitPromotedS1, floatWitPromotedS2, floatWitPromotedS3, m₁, m₂, m₃,
    hs₁, hm₁, hrel₁,
    hs₂, hm₂, hrel₂, rfl,
    hs₃, hm₃, hrel₃, rfl, rfl⟩

/-! ### Real-step deterministic-NaN (`floatNondeterministic := false`) divergence witness -/

def floatWitPayloadNaNF32Const : ConstOperand :=
  { ty := floatWitF32Ty, val := .scalar (.int ⟨0x7FC00001, 4⟩) }

def floatWitDetNaNBody : CapturedMir where
  defPath := "float_cast_lm_witness::det_nan"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [floatWitF64Decl]
  basicBlocks := [
    { statements :=
        [mkStmt (.assign (local_ 0)
          (.cast .floatToFloat (.constant floatWitPayloadNaNF32Const) floatWitF64Ty))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm12FnAbi floatWitF64Layout
  layouts := emptyLayoutTable
  allocations := []

/-- **Real-step deterministic-mode NaN divergence vs nondeterministic refinement witness**:
on `_0 = const (0x7FC0_0001_f32) as f64` (quiet `f32` NaN with payload bit `0` set):
1. Anneal's `stepMirFn` steps normally to `0x7FF8_0000_2000_0000` (payload preserved);
2. Under `floatNondeterministic := false`, `lean-miri`'s `Step.step` steps normally to
   `preferredNaNBits .binary64 = 0x7FF8_0000_0000_0000` (`0x7FF8000000000000 ≠ 0x7FF8000020000000`);
3. Under `floatNondeterministic := true` with `annealChooseQuietedNaN`, `StepRelLM3_1` holds
   and both machines agree on `0x7FF8_0000_2000_0000`. -/
theorem div_floatToFloat_deterministic_payloadNaN_step :
    let b := floatWitDetNaNBody
    let s₀ := initMachineState b []
    let m₀ := lm12MiriInit b floatWitF64Ty
    (∃ m' tf' msc',
      ScalarRel ⟨0x7FF8000000000000, 8⟩ msc' ∧
      stepMirFn b s₀ =
        MirStepNode.step
          (advanceStmt s₀ (s₀.frame.locals.set 0 (.init (.scalar ⟨0x7FF8000020000000, 8⟩)))
            s₀.memory) ∧
      Miri.Interpreter.Step.step
          (annealStepHooksFloat b.localDecls b.layouts false annealChooseQuietedNaN) () m₀ =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[0]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc'))))) ∧
    StepRelLM3_1 b m₀ []
      (stepMirFn b s₀)
      (Miri.Interpreter.Step.step (annealStepHooksFloat b.localDecls b.layouts) () m₀) := by
  have hrel₀ : StateRelLM3_1 floatWitDetNaNBody (initMachineState floatWitDetNaNBody [])
      (lm12MiriInit floatWitDetNaNBody floatWitF64Ty) [] :=
    (lm12_stateRel_init _ floatWitF64Decl rfl rfl rfl rfl rfl rfl rfl).toLM3_1
  have himm₀ : ∀ tf, (lm12MiriInit floatWitDetNaNBody floatWitF64Ty).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 :=
    fun tf htf => by rw [lm12_frames_eq htf]; exact lm12Frame_immediate _ _ 0
  refine ⟨?_, ?_⟩
  · have hdet := step_cast_floatToFloat_constant_deterministic_spec hrel₀
      (fun _ h => nomatch h) annealChooseQuietedNaN rfl rfl rfl rfl rfl rfl rfl rfl
      (by decide) (fun h => nomatch h) himm₀
    have hev : evalFloatToFloatRoundTiesToEven .binary32 .binary64 0x7FC00001 =
        0x7FF8000020000000 := rfl
    have hnan : Anneal.Mir.IeeeFloatCast.isNaNBits .binary32 0x7FC00001 = true := rfl
    have hpref : preferredNaNBits .binary64 = 0x7FF8000000000000 := rfl
    dsimp only at hdet
    simp only [hev, hnan, ↓reduceIte, hpref] at hdet
    exact hdet
  · exact step_cast_float_constant_simulation hrel₀ (fun _ h => nomatch h) rfl rfl rfl
      (.floatToFloat rfl rfl) rfl rfl (Or.inr (Or.inr (Or.inl rfl))) (by decide) rfl himm₀

/-- **Deterministic-mode divergence is exactly NaN canonicalization** on
`_0 = const (0x7FC0_0001_f32) as f64`, for **every** `chooseNaN`:
1. no `StepRelLM3_1` relates Anneal's real step to `lean-miri`'s deterministic step
   (`step_cast_floatToFloat_constant_deterministic_lockstep_iff`: the quieted conversion
   `0x7FF8_0000_2000_0000` differs from `preferredNaNBits .binary64`), so the
   `FloatCastDetAgrees` side condition of the `_mode` theorems cannot be dropped; yet
2. `lean-miri`'s deterministic step is `StepRelLM3_1`-simulated by the Anneal successor storing
   the canonical `0x7FF8_0000_0000_0000`
   (`step_cast_floatToFloat_constant_deterministic_simulation`). -/
theorem div_floatToFloat_deterministic_payloadNaN_exact
    (chooseNaN : Unit → List Miri.Interpreter.FloatBits →
      Miri.Interpreter.RvalueM AnnealStepState Nat) :
    let b := floatWitDetNaNBody
    let s₀ := initMachineState b []
    let m₀ := lm12MiriInit b floatWitF64Ty
    let hooks := annealStepHooksFloat b.localDecls b.layouts false chooseNaN
    ¬ StepRelLM3_1 b m₀ [] (stepMirFn b s₀) (Miri.Interpreter.Step.step hooks () m₀) ∧
      StepRelLM3_1 b m₀ []
        (MirStepNode.step (advanceStmt s₀
          (s₀.frame.locals.set 0 (.init (.scalar ⟨0x7FF8000000000000, 8⟩))) s₀.memory))
        (Miri.Interpreter.Step.step hooks () m₀) := by
  have hrel₀ : StateRelLM3_1 floatWitDetNaNBody (initMachineState floatWitDetNaNBody [])
      (lm12MiriInit floatWitDetNaNBody floatWitF64Ty) [] :=
    (lm12_stateRel_init _ floatWitF64Decl rfl rfl rfl rfl rfl rfl rfl).toLM3_1
  have himm₀ : ∀ tf, (lm12MiriInit floatWitDetNaNBody floatWitF64Ty).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 :=
    fun tf htf => by rw [lm12_frames_eq htf]; exact lm12Frame_immediate _ _ 0
  have hnan : Anneal.Mir.IeeeFloatCast.isNaNBits .binary32 0x7FC00001 = true := rfl
  have hev : evalFloatToFloatRoundTiesToEven .binary32 .binary64 0x7FC00001 =
      0x7FF8000020000000 := rfl
  have hpref : preferredNaNBits .binary64 = 0x7FF8000000000000 := rfl
  refine ⟨fun hstep => ?_, ?_⟩
  · have hag := (step_cast_floatToFloat_constant_deterministic_lockstep_iff hrel₀
      (fun _ h => nomatch h) chooseNaN rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
      (fun h => nomatch h) himm₀).mp hstep
    dsimp only at hag
    rw [hnan, hev, hpref] at hag
    rcases hag with h | h
    · cases h
    · exact absurd h (by decide)
  · have hsim := (step_cast_floatToFloat_constant_deterministic_simulation hrel₀
      (fun _ h => nomatch h) chooseNaN rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
      (fun h => nomatch h) himm₀).2
    dsimp only at hsim
    simp only [hnan, hpref, ↓reduceIte] at hsim
    exact hsim

/-- **Non-vacuity of the step-level NaN-choice refinement with a non-refinement selector**: on
`_0 = const (0x7FC0_0001_f32) as f64` with `floatNondeterministic := true` and the selector
`pure 1` (`lean-miri` picks the sign-negated preferred NaN rather than the quieted conversion),
`step_cast_floatToFloat_constant_nanChoice_simulation` applies: `lean-miri`'s step is
`StepRelLM3_1`-simulated by the Anneal successor storing some `f64` NaN, while Anneal itself
stores the quieted conversion `0x7FF8_0000_2000_0000`. -/
theorem floatWit_nanChoice_pure1_step :
    let b := floatWitDetNaNBody
    let s₀ := initMachineState b []
    let m₀ := lm12MiriInit b floatWitF64Ty
    ∃ outBits, Anneal.Mir.IeeeFloatCast.isNaNBits .binary64 outBits = true ∧
      stepMirFn b s₀ =
        MirStepNode.step (advanceStmt s₀
          (s₀.frame.locals.set 0 (.init (.scalar ⟨0x7FF8000020000000, 8⟩))) s₀.memory) ∧
      StepRelLM3_1 b m₀ []
        (MirStepNode.step (advanceStmt s₀
          (s₀.frame.locals.set 0 (.init (.scalar ⟨outBits, 8⟩))) s₀.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat b.localDecls b.layouts true (fun _ _ => pure 1)) () m₀) := by
  have hrel₀ : StateRelLM3_1 floatWitDetNaNBody (initMachineState floatWitDetNaNBody [])
      (lm12MiriInit floatWitDetNaNBody floatWitF64Ty) [] :=
    (lm12_stateRel_init _ floatWitF64Decl rfl rfl rfl rfl rfl rfl rfl).toLM3_1
  have himm₀ : ∀ tf, (lm12MiriInit floatWitDetNaNBody floatWitF64Ty).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 :=
    fun tf htf => by rw [lm12_frames_eq htf]; exact lm12Frame_immediate _ _ 0
  obtain ⟨outBits, _, _, hn, ha, hsim⟩ := step_cast_floatToFloat_constant_nanChoice_simulation
    hrel₀ (fun _ h => nomatch h) true (fun _ _ => pure 1)
    (fun _ => chooseNaN_pure_valid 1 (by decide)) rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
    (fun h => nomatch h) himm₀
  exact ⟨outBits, (hn rfl).1, ha, hsim⟩

/-- **Exact bit-pattern strengthening of `floatWit_nanChoice_pure1_step`**: instantiating
`step_cast_floatToFloat_constant_pure_index_simulation` on `_0 = const (0x7FC0_0001_f32) as f64`
with selector `pure 1` pins `lean-miri`'s output bit-for-bit to the negative preferred `f64` NaN
`0xFFF8_0000_0000_0000` (while Anneal stores `0x7FF8_0000_2000_0000`), with zero existential! -/
theorem floatWit_nanChoice_pure1_exact :
    let b := floatWitDetNaNBody
    let s₀ := initMachineState b []
    let m₀ := lm12MiriInit b floatWitF64Ty
    stepMirFn b s₀ =
        MirStepNode.step (advanceStmt s₀
          (s₀.frame.locals.set 0 (.init (.scalar ⟨0x7FF8000020000000, 8⟩))) s₀.memory) ∧
      StepRelLM3_1 b m₀ []
        (MirStepNode.step (advanceStmt s₀
          (s₀.frame.locals.set 0 (.init (.scalar ⟨0xFFF8000000000000, 8⟩))) s₀.memory))
        (Miri.Interpreter.Step.step
          (annealStepHooksFloat b.localDecls b.layouts true (fun _ _ => pure 1)) () m₀) := by
  have hrel₀ : StateRelLM3_1 floatWitDetNaNBody (initMachineState floatWitDetNaNBody [])
      (lm12MiriInit floatWitDetNaNBody floatWitF64Ty) [] :=
    (lm12_stateRel_init _ floatWitF64Decl rfl rfl rfl rfl rfl rfl rfl).toLM3_1
  have himm₀ : ∀ tf, (lm12MiriInit floatWitDetNaNBody floatWitF64Ty).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 :=
    fun tf htf => by rw [lm12_frames_eq htf]; exact lm12Frame_immediate _ _ 0
  exact step_cast_floatToFloat_constant_pure_index_simulation
    hrel₀ (fun _ h => nomatch h) (fun _ _ => pure 1) 1 (by decide) (fun _ _ => rfl)
    rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (fun h => nomatch h) himm₀

/-! ### Force-allocated (`LocalRel.indirect`, unpromoted) `f64` destination witness

The `*_indirect_dst_simulation` theorems demand a live stack allocation of
`StackScalarAllocShape`, a cached base address, and an `.indirect (stackAllocPlace id)`
destination local outside `allocMap`. The witness below builds such a `StateRelLM3_1` state from
scratch (`_0 : f64` memory-backed at `AllocId 1`, holding `0.0`) and steps
`_0 = const 7_i32 as f64` through `step_cast_float_constant_indirect_dst_simulation`, so these
hypotheses are jointly satisfiable. -/

/-- Initialized all-zero 8-byte stack allocation (`0.0_f64`), built with `Allocation.fromBytes`. -/
def floatWitIndAlloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (extractExceptOk
    (Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) #[0, 0, 0, 0, 0, 0, 0, 0]
      Miri.ABI.Align.ONE .Mut)
    (by decide)).withExtra none

/-- `lean-miri` machine with `floatWitIndAlloc` live at `AllocId 1` and its stack base address
`annealStackBaseAddr 1` cached. -/
def floatWitIndMachine : AnnealMachine :=
  { memory := { (Miri.Memory.MemoryState.empty : AnnealMemory) with
      nextAllocId := 2
      live := #[(floatWitAllocId1, { kind := .stack, allocation := floatWitIndAlloc })] }
    addresses :=
      { provenanceMode := .default
        addressMode := .managed
        generation := none
        baseAddr := #[{ allocId := floatWitAllocId1, address := annealStackBaseAddr floatWitAllocId1 }] }
    borrowTracker := none }

/-- The constant `7_i32`. -/
def floatWitSevenI32Const : ConstOperand :=
  { ty := floatWitI32Ty, val := .scalar (.int ⟨7, 4⟩) }

/-- MIR of `_0 = const 7_i32 as f64; return` with `_0 : f64`. -/
def floatWitIndBody : CapturedMir where
  defPath := "float_cast_lm_witness::indirect_dst"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [floatWitF64Decl]
  basicBlocks := [
    { statements :=
        [mkStmt (.assign (local_ 0) (.cast .intToFloat (.constant floatWitSevenI32Const)
          floatWitF64Ty))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm12FnAbi floatWitF64Layout
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal's state before the cast: `_0 = 0.0_f64`. -/
def floatWitIndAnnealPre : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init (.scalar ⟨0, 8⟩)] }
    memory := (initMachineState floatWitIndBody []).memory }

/-- Anneal's state after the cast: `_0 = 7.0_f64` (`0x401C_0000_0000_0000`). -/
def floatWitIndAnnealPost : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 1, locals := [.init (.scalar ⟨0x401C000000000000, 8⟩)] }
    memory := floatWitIndAnnealPre.memory }

/-- `lean-miri` frame whose return local `_0` is memory-backed at `stackAllocPlace 1`. -/
def floatWitIndMiriFramePre :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody floatWitIndBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy floatWitF64Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[{ value := .live (.indirect (stackAllocPlace floatWitAllocId1)), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def floatWitIndMiriPre : AnnealStepState :=
  { stack := ⟨#[floatWitIndMiriFramePre]⟩, machine := floatWitIndMachine }

theorem floatWitIndAlloc_shape :
    StackScalarAllocShape (translateTy floatWitF64Ty emptyLayoutTable).layout.size
      floatWitIndAlloc :=
  ⟨by decide, by decide, by decide, rfl, ⟨true, rfl⟩⟩

theorem floatWitInd_stateRel_pre :
    StateRelLM3_1 floatWitIndBody floatWitIndAnnealPre floatWitIndMiriPre [] := by
  refine (StateRel.mk floatWitIndMiriFramePre rfl rfl ⟨translateTy floatWitF64Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl ?_).toLM3_1
  · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 =>
      have hd : decl = floatWitF64Decl := by simpa [floatWitIndBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨0, 8⟩) := by
        simpa [floatWitIndAnnealPre, get?] using hslot.symm
      have hm : mls =
          { value := .live (.indirect (stackAllocPlace floatWitAllocId1)), layout := none } := by
        simpa [floatWitIndMiriFramePre] using hmls.symm
      subst hd hs hm
      refine .indirect (.init (.scalar ⟨0, 8⟩)) (stackAllocPlace floatWitAllocId1) none
        (fun _ h => nomatch h) nofun ?_
      refine MemPlaceRel.mk floatWitAllocId1 Miri.Memory.BorTag.one
        (annealStackBaseAddr floatWitAllocId1) Miri.ABI.Size.ZERO
        { kind := .stack, allocation := floatWitIndAlloc }
        rfl rfl rfl (List.Mem.head _) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (fun h _ => nomatch h) (fun _ _ _ => by decide) ?_
        (fun _ _ _ _ h => nomatch h)
      intro sc h
      injection h with hv
      injection hv with hsc
      subst hsc
      exact ⟨by decide, (fun hb => nomatch hb), (fun hc => nomatch hc),
        extractExceptOk (translateScalarInt ⟨0, 8⟩) (by decide),
        ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, by decide, by decide⟩,
        by with_unfolding_all rfl⟩
    | _ + 1 => simp [floatWitIndBody, get?] at hdecl
  · intro i j mp_i mp_j lay_i lay_j hij hi hj
    have hi0 : i = 0 := by
      match i, hi with
      | 0, _ => rfl
      | _ + 1, h => simp [floatWitIndMiriFramePre] at h
    have hj0 : j = 0 := by
      match j, hj with
      | 0, _ => rfl
      | _ + 1, h => simp [floatWitIndMiriFramePre] at h
    exact absurd (hi0.trans hj0.symm) hij

set_option maxRecDepth 200000 in
private theorem floatWitInd_anneal_step :
    stepMirFn floatWitIndBody floatWitIndAnnealPre = .step floatWitIndAnnealPost := rfl

/-- **Non-vacuity of the indirect-destination step theorems**: in a `StateRelLM3_1` state
whose `f64` return local `_0` is force-allocated (`LocalRel.indirect`, backed by a
`StackScalarAllocShape` stack allocation at `AllocId 1` holding `0.0`),
`step_cast_float_constant_indirect_floatDst_simulation` applies directly (without any `hnot_dst`
premise) to `_0 = const 7_i32 as f64`: both machines step, Anneal stores `7.0_f64`, `lean-miri`
overwrites the stack allocation, and the successors are `StateRelLM3_1`-related. -/
theorem floatWit_indirect_dst_step :
    ∃ m₁, Miri.Interpreter.Step.step
        (annealStepHooksFloat floatWitIndBody.localDecls floatWitIndBody.layouts) ()
        floatWitIndMiriPre = (m₁, .ok true) ∧
      stepMirFn floatWitIndBody floatWitIndAnnealPre = .step floatWitIndAnnealPost ∧
      StateRelLM3_1 floatWitIndBody floatWitIndAnnealPost m₁ [] := by
  have hr := step_cast_float_constant_indirect_floatDst_simulation floatWitInd_stateRel_pre
    (fun _ h => nomatch h) rfl rfl rfl (.intToFloat (t := .signed .i32) rfl rfl) rfl rfl rfl
    (Or.inr (Or.inr (Or.inl rfl))) (by decide) rfl
    (allocId := floatWitAllocId1) (localAlloc := { kind := .stack, allocation := floatWitIndAlloc })
    (by decide) (by decide) rfl floatWitIndAlloc_shape
    (fun tf htf => ⟨none, by
      injection htf with h₁; injection h₁ with h₂; subst h₂; rfl⟩)
  obtain ⟨m₁, hm₁, hrel₁⟩ := floatWit_step_of_stepRel hr floatWitInd_anneal_step
  exact ⟨m₁, hm₁, floatWitInd_anneal_step, hrel₁⟩
/-! ### Force-allocated (`LocalRel.indirect`, unpromoted) `f64` source witness -/

/-- Initialized 8-byte stack allocation holding `2.5_f64` (`0x4004_0000_0000_0000`,
little-endian). -/
def floatWitIndSrcAlloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (extractExceptOk
    (Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) #[0, 0, 0, 0, 0, 0, 4, 64]
      Miri.ABI.Align.ONE .Mut)
    (by decide)).withExtra none

/-- `lean-miri` machine with `floatWitIndSrcAlloc` live at `AllocId 1` and its stack base address
cached. -/
def floatWitIndSrcMachine : AnnealMachine :=
  { memory := { (Miri.Memory.MemoryState.empty : AnnealMemory) with
      nextAllocId := 2
      live := #[(floatWitAllocId1, { kind := .stack, allocation := floatWitIndSrcAlloc })] }
    addresses :=
      { provenanceMode := .default
        addressMode := .managed
        generation := none
        baseAddr := #[{ allocId := floatWitAllocId1, address := annealStackBaseAddr floatWitAllocId1 }] }
    borrowTracker := none }

/-- MIR of `_0 = copy _1 as f32; return` with `_0 : f32` and `_1 : f64`. -/
def floatWitIndSrcBody : CapturedMir where
  defPath := "float_cast_lm_witness::indirect_src"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [floatWitF32Decl, floatWitF64Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.cast .floatToFloat (.copy (local_ 1)) floatWitF32Ty))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm12FnAbi floatWitF64Layout
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal's state before the cast: `_0` uninitialized, `_1 = 2.5_f64`. -/
def floatWitIndSrcAnnealPre : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨0x4004000000000000, 8⟩)] }
    memory := (initMachineState floatWitIndSrcBody []).memory }

/-- Anneal's state after the cast: `_0 = 2.5_f32` (`0x4020_0000`). -/
def floatWitIndSrcAnnealPost : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 1
        locals := [.init (.scalar ⟨0x40200000, 4⟩), .init (.scalar ⟨0x4004000000000000, 8⟩)] }
    memory := floatWitIndSrcAnnealPre.memory }

/-- `lean-miri` frame with immediate `_0` and `_1` memory-backed at `stackAllocPlace 1`. -/
def floatWitIndSrcMiriFramePre :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody floatWitIndSrcBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy floatWitF32Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.indirect (stackAllocPlace floatWitAllocId1)), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def floatWitIndSrcMiriPre : AnnealStepState :=
  { stack := ⟨#[floatWitIndSrcMiriFramePre]⟩, machine := floatWitIndSrcMachine }

theorem floatWitIndSrcAlloc_shape :
    StackScalarAllocShape (translateTy floatWitF64Ty emptyLayoutTable).layout.size
      floatWitIndSrcAlloc :=
  ⟨by decide, by decide, by decide, rfl, ⟨true, rfl⟩⟩

theorem floatWitIndSrc_stateRel_pre :
    StateRelLM3_1 floatWitIndSrcBody floatWitIndSrcAnnealPre floatWitIndSrcMiriPre [] := by
  refine (StateRel.mk floatWitIndSrcMiriFramePre rfl rfl ⟨translateTy floatWitF32Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl ?_).toLM3_1
  · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 =>
      have hs : slot = .uninit := by simpa [floatWitIndSrcAnnealPre, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [floatWitIndSrcMiriFramePre] using hmls.symm
      subst hs hm
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 1 =>
      have hd : decl = floatWitF64Decl := by simpa [floatWitIndSrcBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨0x4004000000000000, 8⟩) := by
        simpa [floatWitIndSrcAnnealPre, get?] using hslot.symm
      have hm : mls =
          { value := .live (.indirect (stackAllocPlace floatWitAllocId1)), layout := none } := by
        simpa [floatWitIndSrcMiriFramePre] using hmls.symm
      subst hd hs hm
      refine .indirect (.init (.scalar ⟨0x4004000000000000, 8⟩)) (stackAllocPlace floatWitAllocId1)
        none (fun _ h => nomatch h) nofun ?_
      refine MemPlaceRel.mk floatWitAllocId1 Miri.Memory.BorTag.one
        (annealStackBaseAddr floatWitAllocId1) Miri.ABI.Size.ZERO
        { kind := .stack, allocation := floatWitIndSrcAlloc }
        rfl rfl rfl (List.Mem.head _) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (fun h _ => nomatch h) (fun _ _ _ => by decide) ?_
        (fun _ _ _ _ h => nomatch h)
      intro sc h
      injection h with hv
      injection hv with hsc
      subst hsc
      exact ⟨by decide, (fun hb => nomatch hb), (fun hc => nomatch hc),
        extractExceptOk (translateScalarInt ⟨0x4004000000000000, 8⟩) (by decide),
        ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, by decide, by decide⟩,
        by with_unfolding_all rfl⟩
    | _ + 2 => simp [floatWitIndSrcBody, get?] at hdecl
  · intro i j mp_i mp_j lay_i lay_j hij hi hj
    have hi1 : i = 1 := by
      match i, hi with
      | 1, _ => rfl
      | 0, h => simp [floatWitIndSrcMiriFramePre] at h
      | _ + 2, h => simp [floatWitIndSrcMiriFramePre] at h
    have hj1 : j = 1 := by
      match j, hj with
      | 1, _ => rfl
      | 0, h => simp [floatWitIndSrcMiriFramePre] at h
      | _ + 2, h => simp [floatWitIndSrcMiriFramePre] at h
    exact absurd (hi1.trans hj1.symm) hij

set_option maxRecDepth 200000 in
private theorem floatWitIndSrc_anneal_step :
    stepMirFn floatWitIndSrcBody floatWitIndSrcAnnealPre = .step floatWitIndSrcAnnealPost := rfl

/-- **Non-vacuity of the indirect-source step theorems**: in a `StateRelLM3_1` state whose
`f64` local `_1` is force-allocated (`LocalRel.indirect`, backed by a `StackScalarAllocShape`
stack allocation at `AllocId 1` holding `2.5_f64`),
`step_cast_float_copy_indirect_float_simulation` applies to `_0 = copy _1 as f32`: `lean-miri`
reads the operand from memory, both machines store `2.5_f32` into `_0`, and the successors are
`StateRelLM3_1`-related. -/
theorem floatWit_indirect_src_step :
    ∃ m₁, Miri.Interpreter.Step.step
        (annealStepHooksFloat floatWitIndSrcBody.localDecls floatWitIndSrcBody.layouts) ()
        floatWitIndSrcMiriPre = (m₁, .ok true) ∧
      stepMirFn floatWitIndSrcBody floatWitIndSrcAnnealPre = .step floatWitIndSrcAnnealPost ∧
      StateRelLM3_1 floatWitIndSrcBody floatWitIndSrcAnnealPost m₁ [] := by
  have hr := step_cast_float_copy_indirect_float_simulation floatWitIndSrc_stateRel_pre
    (fun _ h => nomatch h) rfl rfl rfl rfl (.floatToFloat rfl rfl) rfl
    (allocId := floatWitAllocId1)
    (localAlloc := { kind := .stack, allocation := floatWitIndSrcAlloc })
    (by decide) (by decide) rfl
    (fun la₁ la₂ h₁ h₂ => by
      have e₁ := List.mem_singleton.mp h₁
      have e₂ := List.mem_singleton.mp h₂
      rw [(Prod.mk.inj e₁).2, (Prod.mk.inj e₂).2])
    floatWitIndSrcAlloc_shape
    (fun tf htf => ⟨none, by
      injection htf with h₁; injection h₁ with h₂; subst h₂; rfl⟩)
    (fun v hv => ⟨⟨0x4004000000000000, 8⟩, by
      simpa [floatWitIndSrcAnnealPre, get?] using hv.symm⟩)
    (fun tf htf => Or.inl (by
      injection htf with h₁; injection h₁ with h₂; subst h₂
      intro mls hmls mp hmp
      simp [floatWitIndSrcMiriFramePre] at hmls
      subst hmls
      cases hmp))
  obtain ⟨m₁, hm₁, hrel₁⟩ := floatWit_step_of_stepRel hr floatWitIndSrc_anneal_step
  exact ⟨m₁, hm₁, floatWitIndSrc_anneal_step, hrel₁⟩

/-- **Non-vacuity of the selector-validity tightness**: on `_0 = const (0x7FC0_0001_f32) as f64`
(a quiet `f32` NaN, whose nondeterministic candidate list has 4 entries), the out-of-range
selector `pure 4` makes `lean-miri`'s `Step.step` fail with `.invalidProgram` while Anneal steps
normally, so no `StepRelLM3_1` relates them (`step_cast_floatToFloat_constant_pure_out_of_range`). -/
theorem floatWit_nanChoice_pure4_out_of_range :
    let b := floatWitDetNaNBody
    let s₀ := initMachineState b []
    let m₀ := lm12MiriInit b floatWitF64Ty
    let hooks := annealStepHooksFloat b.localDecls b.layouts true (fun _ _ => pure 4)
    (∃ m', Miri.Interpreter.Step.step hooks () m₀ =
        (m', .error (.invalidProgram "invalid floating NaN choice index"))) ∧
      ¬ StepRelLM3_1 b m₀ [] (stepMirFn b s₀) (Miri.Interpreter.Step.step hooks () m₀) := by
  have hrel₀ : StateRelLM3_1 floatWitDetNaNBody (initMachineState floatWitDetNaNBody [])
      (lm12MiriInit floatWitDetNaNBody floatWitF64Ty) [] :=
    (lm12_stateRel_init _ floatWitF64Decl rfl rfl rfl rfl rfl rfl rfl).toLM3_1
  have himm₀ : ∀ tf, (lm12MiriInit floatWitDetNaNBody floatWitF64Ty).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 :=
    fun tf htf => by rw [lm12_frames_eq htf]; exact lm12Frame_immediate _ _ 0
  have hnan : decodeBits .binary32 0x7FC00001 = .nan false true 0x400001 := rfl
  obtain ⟨cs, hcs, hlen⟩ :=
    floatBits_nanChoices_quiet_length .binary32 .binary64 0x7FC00001 (by decide) false 0x400001 hnan
  obtain ⟨_, hm, hnot⟩ := step_cast_floatToFloat_constant_pure_out_of_range hrel₀
    (fun _ h => nomatch h) (fun _ _ => pure 4) 4 (fun _ _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) hnan hcs (by omega) (fun h => nomatch h) himm₀
  exact ⟨hm, hnot⟩

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

/--
info: 'LeanMiriSpec.Correspondence.floatBits_preferredNaN_mem_nanChoices' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_preferredNaN_mem_nanChoices

/--
info: 'LeanMiriSpec.Correspondence.floatBits_convert_mem_nanChoices_nondet' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_convert_mem_nanChoices_nondet

/--
info: 'LeanMiriSpec.Correspondence.floatBits_nanChoices_nondet_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_nanChoices_nondet_exact

/--
info: 'LeanMiriSpec.Correspondence.floatOps_castFloatToFloat_refine_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatOps_castFloatToFloat_refine_eq

/--
info: 'LeanMiriSpec.Correspondence.floatOps_castFloatToFloat_deterministic_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatOps_castFloatToFloat_deterministic_eq

/--
info: 'LeanMiriSpec.Correspondence.floatOps_castFloatToInt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatOps_castFloatToInt_eq

/--
info: 'LeanMiriSpec.Correspondence.floatOps_castIntToFloat_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatOps_castIntToFloat_eq

/--
info: 'LeanMiriSpec.Correspondence.floatOps_castIntToFloat_bool_char_err' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatOps_castIntToFloat_bool_char_err

/--
info: 'LeanMiriSpec.Correspondence.step_float_eq_annealStepHooks_at_stmt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_float_eq_annealStepHooks_at_stmt

/--
info: 'LeanMiriSpec.Correspondence.step_float_eq_annealStepHooks_at_terminator' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_float_eq_annealStepHooks_at_terminator

/--
info: 'LeanMiriSpec.Correspondence.cast_intToInt_ptrToPtr_floatHooks_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cast_intToInt_ptrToPtr_floatHooks_eq

/--
info: 'LeanMiriSpec.Correspondence.annealReadMemoryPlace_floatCastScalar_zero_offset_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms annealReadMemoryPlace_floatCastScalar_zero_offset_eq

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_copy_anyLocal_simulation_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_copy_anyLocal_simulation_mode

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_copy_anyLocal_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_copy_anyLocal_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_move_anyLocal_simulation_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_move_anyLocal_simulation_mode

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_move_anyLocal_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_move_anyLocal_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_constant_anyLocal_simulation_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_constant_anyLocal_simulation_mode

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_constant_anyLocal_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_constant_anyLocal_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_copy_indirect_float_simulation_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_copy_indirect_float_simulation_mode

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_copy_indirect_float_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_copy_indirect_float_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_constant_anyLocal_preserves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_constant_anyLocal_preserves

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_copy_anyLocal_preserves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_copy_anyLocal_preserves

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_move_anyLocal_preserves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_move_anyLocal_preserves

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_constant_deterministic_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_constant_deterministic_spec

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_copy_deterministic_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_copy_deterministic_spec

/--
info: 'LeanMiriSpec.Correspondence.cast_intToFloat_bool_miri_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cast_intToFloat_bool_miri_ok

/--
info: 'LeanMiriSpec.Correspondence.cast_intToFloat_char_miri_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cast_intToFloat_char_miri_ok

/--
info: 'LeanMiriSpec.Correspondence.cast_f16_f128_unsupported' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cast_f16_f128_unsupported

/--
info: 'LeanMiriSpec.Correspondence.step_cast_f16_f128_source_fail_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_f16_f128_source_fail_closed

/--
info: 'LeanMiriSpec.Correspondence.miri_f64_to_f32_subnormal_ties_and_overflow_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_f64_to_f32_subnormal_ties_and_overflow_witnesses

/--
info: 'LeanMiriSpec.Correspondence.miri_isize_usize_cast_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_isize_usize_cast_witnesses

/--
info: 'LeanMiriSpec.Correspondence.miri_snan_f64_to_f32_nanChoices_4_vs_6' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_snan_f64_to_f32_nanChoices_4_vs_6

/--
info: 'LeanMiriSpec.Correspondence.floatWit_copy_move_isize_and_ub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatWit_copy_move_isize_and_ub

/--
info: 'LeanMiriSpec.Correspondence.floatWit_promoted_allocMap_pipeline' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatWit_promoted_allocMap_pipeline

/--
info: 'LeanMiriSpec.Correspondence.div_floatToFloat_deterministic_payloadNaN_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms div_floatToFloat_deterministic_payloadNaN_step

/--
info: 'LeanMiriSpec.Correspondence.finish_write_immediate_split_hooks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms finish_write_immediate_split_hooks

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_copy_deterministic_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_copy_deterministic_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_constant_deterministic_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_constant_deterministic_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_move_deterministic_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_move_deterministic_simulation

/--
info: 'LeanMiriSpec.Correspondence.ScalarRel.bits_eq_of_same_msc' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms ScalarRel.bits_eq_of_same_msc

/--
info: 'LeanMiriSpec.Correspondence.stateRel_dst_scalar_bits_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stateRel_dst_scalar_bits_eq

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_copy_deterministic_lockstep_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_copy_deterministic_lockstep_iff

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_constant_deterministic_lockstep_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_constant_deterministic_lockstep_iff

/--
info: 'LeanMiriSpec.Correspondence.div_floatToFloat_deterministic_payloadNaN_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms div_floatToFloat_deterministic_payloadNaN_exact

/--
info: 'LeanMiriSpec.Correspondence.floatBits_nanChoices_nondet_list_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_nanChoices_nondet_list_eq

/--
info: 'LeanMiriSpec.Correspondence.floatBits_mem_nanChoices_isNaN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatBits_mem_nanChoices_isNaN

/--
info: 'LeanMiriSpec.Correspondence.floatOps_adjustNaN_any_chooseNaN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatOps_adjustNaN_any_chooseNaN

/--
info: 'LeanMiriSpec.Correspondence.cast_floatToFloat_any_chooseNaN_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cast_floatToFloat_any_chooseNaN_spec

/--
info: 'LeanMiriSpec.Correspondence.StateRelLM3_1.not_mem_allocMap_of_ieeeFormatOfTy?' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms StateRelLM3_1.not_mem_allocMap_of_ieeeFormatOfTy?

/--
info: 'LeanMiriSpec.Correspondence.StateRelLM3_1.deinit_unpromoted_local' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms StateRelLM3_1.deinit_unpromoted_local

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_move_indirect_float_simulation_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_move_indirect_float_simulation_mode

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_move_indirect_float_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_move_indirect_float_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_move_deterministic_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_move_deterministic_spec

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_move_deterministic_lockstep_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_move_deterministic_lockstep_iff

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_copy_nanChoice_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_copy_nanChoice_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_constant_nanChoice_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_constant_nanChoice_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_move_nanChoice_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_move_nanChoice_simulation

/--
info: 'LeanMiriSpec.Correspondence.chooseNaN_pure_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms chooseNaN_pure_valid

/--
info: 'LeanMiriSpec.Correspondence.annealChooseQuietedNaN_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms annealChooseQuietedNaN_valid

/--
info: 'LeanMiriSpec.Correspondence.floatWit_nanChoice_pure1_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatWit_nanChoice_pure1_step

/--
info: 'LeanMiriSpec.Correspondence.floatOps_adjustNaN_pure_index' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatOps_adjustNaN_pure_index

/--
info: 'LeanMiriSpec.Correspondence.step_cast_f16_f128_uninit_source_divergence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_f16_f128_uninit_source_divergence

/--
info: 'LeanMiriSpec.Correspondence.floatOps_adjustNaN_pure_index_all' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatOps_adjustNaN_pure_index_all

/--
info: 'LeanMiriSpec.Correspondence.floatOps_adjustNaN_pure_snan_index' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatOps_adjustNaN_pure_snan_index

/--
info: 'LeanMiriSpec.Correspondence.cast_floatToFloat_pure_index_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cast_floatToFloat_pure_index_eq

/--
info: 'LeanMiriSpec.Correspondence.annealWriteMemoryPlace_floatCastScalar_zero_offset_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms annealWriteMemoryPlace_floatCastScalar_zero_offset_ok

/--
info: 'LeanMiriSpec.Correspondence.StateRelLM3_1.advance_write_unpromoted_indirect_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms StateRelLM3_1.advance_write_unpromoted_indirect_scalar

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_copy_indirect_dst_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_copy_indirect_dst_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_move_indirect_dst_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_move_indirect_dst_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_constant_indirect_dst_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_constant_indirect_dst_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_copy_pure_index_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_copy_pure_index_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_constant_pure_index_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_constant_pure_index_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_move_pure_index_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_floatToFloat_move_pure_index_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_f16_f128_target_copy_fail_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_f16_f128_target_copy_fail_closed

/--
info: 'LeanMiriSpec.Correspondence.step_cast_f16_f128_uninit_target_ub_lockstep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_f16_f128_uninit_target_ub_lockstep

/--
info: 'LeanMiriSpec.Correspondence.floatWit_nanChoice_pure1_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatWit_nanChoice_pure1_exact

/--
info: 'LeanMiriSpec.Correspondence.floatToFloatPureIndexBits_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatToFloatPureIndexBits_spec

/--
info: 'LeanMiriSpec.Correspondence.floatWitInd_stateRel_pre' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatWitInd_stateRel_pre

/--
info: 'LeanMiriSpec.Correspondence.floatWit_indirect_dst_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatWit_indirect_dst_step

/--
info: 'LeanMiriSpec.Correspondence.floatWitIndSrc_stateRel_pre' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatWitIndSrc_stateRel_pre

/--
info: 'LeanMiriSpec.Correspondence.floatWit_indirect_src_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatWit_indirect_src_step

/--
info: 'LeanMiriSpec.Correspondence.floatToFloatPureIndexBits_snan_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms floatToFloatPureIndexBits_snan_spec

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_constant_indirect_floatDst_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_constant_indirect_floatDst_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_copy_indirect_floatDst_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_copy_indirect_floatDst_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_move_indirect_floatDst_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_float_move_indirect_floatDst_simulation

/--
info: 'LeanMiriSpec.Correspondence.step_cast_f16_f128_constant_fail_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_f16_f128_constant_fail_closed

/--
info: 'LeanMiriSpec.Correspondence.step_cast_f16_f128_move_source_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_f16_f128_move_source_boundary

/--
info: 'LeanMiriSpec.Correspondence.step_cast_f16_f128_move_target_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_cast_f16_f128_move_target_boundary

/-! Axiom guards for the remaining public theorems (helpers, `_mode` variants, and witnesses): together
with the guards above, every public theorem of this file is pinned to the standard axioms. -/

/--
info: 'LeanMiriSpec.Correspondence.floatOps_engine_ok' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatOps_engine_ok

/--
info: 'LeanMiriSpec.Correspondence.miri_signedNumerator_eq' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.miri_signedNumerator_eq

/--
info: 'LeanMiriSpec.Correspondence.ieeeFormatToMiri_size' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.ieeeFormatToMiri_size

/--
info: 'LeanMiriSpec.Correspondence.ieeeFormatToMiri_of_miriFormatToIeee?' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.ieeeFormatToMiri_of_miriFormatToIeee?

/--
info: 'LeanMiriSpec.Correspondence.width_lt_128' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.width_lt_128

/--
info: 'LeanMiriSpec.Correspondence.bitVec128_toNat_of_lt_width' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.bitVec128_toNat_of_lt_width

/--
info: 'LeanMiriSpec.Correspondence.floatBits_decode_eq_miriDecode' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatBits_decode_eq_miriDecode

/--
info: 'LeanMiriSpec.Correspondence.floatBits_zero_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatBits_zero_eq

/--
info: 'LeanMiriSpec.Correspondence.floatBits_infinity_eq' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatBits_infinity_eq

/--
info: 'LeanMiriSpec.Correspondence.floatBits_preferredNaN_eq' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatBits_preferredNaN_eq

/--
info: 'LeanMiriSpec.Correspondence.floatBits_roundRatio_zeroDenominator' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatBits_roundRatio_zeroDenominator

/--
info: 'LeanMiriSpec.Correspondence.floatIntTarget_bounds' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatIntTarget_bounds

/--
info: 'LeanMiriSpec.Correspondence.quietBit_eq_not_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.quietBit_eq_not_lt

/--
info: 'LeanMiriSpec.Correspondence.floatBits_negate_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatBits_negate_eq

/--
info: 'LeanMiriSpec.Correspondence.flipSignBits_encodeBits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.flipSignBits_encodeBits

/--
info: 'LeanMiriSpec.Correspondence.isNaNBits_encodeBits_maxExp' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.isNaNBits_encodeBits_maxExp

/--
info: 'LeanMiriSpec.Correspondence.floatBits_negate_encodeBits_nan' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatBits_negate_encodeBits_nan

/--
info: 'LeanMiriSpec.Correspondence.floatOps_adjustNaN_of_not_nan' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatOps_adjustNaN_of_not_nan

/--
info: 'LeanMiriSpec.Correspondence.floatToFloatPureIndexBits_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatToFloatPureIndexBits_lt

/--
info: 'LeanMiriSpec.Correspondence.ieeeFormatOfTy?_kind' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.ieeeFormatOfTy?_kind

/--
info: 'LeanMiriSpec.Correspondence.translateTy_of_ieeeFormatOfTy?' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.translateTy_of_ieeeFormatOfTy?

/--
info: 'LeanMiriSpec.Correspondence.castTypeInfoOfEncodedTyIdFloat_floatTyIdOf' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.castTypeInfoOfEncodedTyIdFloat_floatTyIdOf

/--
info: 'LeanMiriSpec.Correspondence.floatFormatOfEncodedTyId_floatTyIdOf' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatFormatOfEncodedTyId_floatTyIdOf

/--
info: 'LeanMiriSpec.Correspondence.floatLayoutData_size' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatLayoutData_size

/--
info: 'LeanMiriSpec.Correspondence.scalarModulus_byteWidth' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.scalarModulus_byteWidth

/--
info: 'LeanMiriSpec.Correspondence.validScalarBytes_byteWidth' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.validScalarBytes_byteWidth

/--
info: 'LeanMiriSpec.Correspondence.translateSizeBytes_byteWidth' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.translateSizeBytes_byteWidth

/--
info: 'LeanMiriSpec.Correspondence.cast_liftResult_ok' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.cast_liftResult_ok

/--
info: 'LeanMiriSpec.Correspondence.cast_liftResult_error' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.cast_liftResult_error

/--
info: 'LeanMiriSpec.Correspondence.floatOps_liftResult_ok' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatOps_liftResult_ok

/--
info: 'LeanMiriSpec.Correspondence.annealReadImmediate_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.annealReadImmediate_scalar

/--
info: 'LeanMiriSpec.Correspondence.floatOps_readScalarBits_unfold' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatOps_readScalarBits_unfold

/--
info: 'LeanMiriSpec.Correspondence.floatOps_readBits_annealFloat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatOps_readBits_annealFloat

/--
info: 'LeanMiriSpec.Correspondence.floatOps_adjustNaN_annealFloat_refine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatOps_adjustNaN_annealFloat_refine

/--
info: 'LeanMiriSpec.Correspondence.floatIntTargetOfTy?_kind' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatIntTargetOfTy?_kind

/--
info: 'LeanMiriSpec.Correspondence.translateTy_of_floatIntTargetOfTy?' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.translateTy_of_floatIntTargetOfTy?

/--
info: 'LeanMiriSpec.Correspondence.castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.castTypeInfoOfEncodedTyIdFloat_floatIntTargetTyId

/--
info: 'LeanMiriSpec.Correspondence.floatIntTargetKind_signed' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatIntTargetKind_signed

/--
info: 'LeanMiriSpec.Correspondence.scalarLayoutData_floatIntTarget_size' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.scalarLayoutData_floatIntTarget_size

/--
info: 'LeanMiriSpec.Correspondence.scalarLayoutData_floatIntTarget_bitsNat' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.scalarLayoutData_floatIntTarget_bitsNat

/--
info: 'LeanMiriSpec.Correspondence.translateSizeBytes_floatIntTarget_bitsNat' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.translateSizeBytes_floatIntTarget_bitsNat

/--
info: 'LeanMiriSpec.Correspondence.scalarLayoutData_floatIntTarget_isSigned' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.scalarLayoutData_floatIntTarget_isSigned

/--
info: 'LeanMiriSpec.Correspondence.validScalarBytes_floatIntTarget' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.validScalarBytes_floatIntTarget

/--
info: 'LeanMiriSpec.Correspondence.floatIntTarget_bitWidth_eq' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatIntTarget_bitWidth_eq

/--
info: 'LeanMiriSpec.Correspondence.annealFloatOpsHooks_formatOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.annealFloatOpsHooks_formatOf

/--
info: 'LeanMiriSpec.Correspondence.cast_scalarOf_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.cast_scalarOf_scalar

/--
info: 'LeanMiriSpec.Correspondence.decodeBitsInt_true_eq_intValueOfBits' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.decodeBitsInt_true_eq_intValueOfBits

/--
info: 'LeanMiriSpec.Correspondence.intLike_integer_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.intLike_integer_eq

/--
info: 'LeanMiriSpec.Correspondence.floatOps_scalarResult_unfold' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatOps_scalarResult_unfold

/--
info: 'LeanMiriSpec.Correspondence.floatOps_scalarResult_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatOps_scalarResult_eq

/--
info: 'LeanMiriSpec.Correspondence.floatOps_adjustNaN_annealFloat_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatOps_adjustNaN_annealFloat_deterministic

/--
info: 'LeanMiriSpec.Correspondence.annealCastHooksFloat_typeInfo_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.annealCastHooksFloat_typeInfo_eq

/--
info: 'LeanMiriSpec.Correspondence.intLikeValue_floatHooks_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.intLikeValue_floatHooks_eq

/--
info: 'LeanMiriSpec.Correspondence.castFromIntLike_floatHooks_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.castFromIntLike_floatHooks_eq

/--
info: 'LeanMiriSpec.Correspondence.ptrToPtr_floatHooks_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.ptrToPtr_floatHooks_eq

/--
info: 'LeanMiriSpec.Correspondence.pointerExposeProvenance_floatHooks_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.pointerExposeProvenance_floatHooks_eq

/--
info: 'LeanMiriSpec.Correspondence.FloatCastSig.src_scalar' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.FloatCastSig.src_scalar

/--
info: 'LeanMiriSpec.Correspondence.FloatCastSig.cast_scalar' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.FloatCastSig.cast_scalar

/--
info: 'LeanMiriSpec.Correspondence.FloatCastSig.isFloatCastKind' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.FloatCastSig.isFloatCastKind

/--
info: 'LeanMiriSpec.Correspondence.IsFloatCastScalarTy.translateTy_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.IsFloatCastScalarTy.translateTy_eq

/--
info: 'LeanMiriSpec.Correspondence.IsFloatCastScalarTy.not_bool_char' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.IsFloatCastScalarTy.not_bool_char

/--
info: 'LeanMiriSpec.Correspondence.IsFloatCastScalarTy.size_ne_zero' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.IsFloatCastScalarTy.size_ne_zero

/--
info: 'LeanMiriSpec.Correspondence.IsFloatCastScalarTy.not_aggregate' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.IsFloatCastScalarTy.not_aggregate

/--
info: 'LeanMiriSpec.Correspondence.IsFloatCastScalarTy.not_rawPtr' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.IsFloatCastScalarTy.not_rawPtr

/--
info: 'LeanMiriSpec.Correspondence.floatPtrWidthOfLayouts_of_ptr8' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatPtrWidthOfLayouts_of_ptr8

/--
info: 'LeanMiriSpec.Correspondence.sizeBytes_of_float_layout' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.sizeBytes_of_float_layout

/--
info: 'LeanMiriSpec.Correspondence.sizeBytes_of_int_layout' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.sizeBytes_of_int_layout

/--
info: 'LeanMiriSpec.Correspondence.estate_throw_bind_float' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.estate_throw_bind_float

/--
info: 'LeanMiriSpec.Correspondence.annealReadImmediate_uninit_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.annealReadImmediate_uninit_eq

/--
info: 'LeanMiriSpec.Correspondence.cast_floatCast_of_readImmediate_err' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.cast_floatCast_of_readImmediate_err

/--
info: 'LeanMiriSpec.Correspondence.cast_floatCast_of_readImmediate_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.cast_floatCast_of_readImmediate_scalar

/--
info: 'LeanMiriSpec.Correspondence.annealReadImmediate_indirect_floatCastScalar_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.annealReadImmediate_indirect_floatCastScalar_eq

/--
info: 'LeanMiriSpec.Correspondence.IsFloatCastScalarTy.validateScalar_true' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.IsFloatCastScalarTy.validateScalar_true

/--
info: 'LeanMiriSpec.Correspondence.operandTy_copy_local' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.operandTy_copy_local

/--
info: 'LeanMiriSpec.Correspondence.operandTy_move_local' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.operandTy_move_local

/--
info: 'LeanMiriSpec.Correspondence.evalRvalue_floatCast_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.evalRvalue_floatCast_eq

/--
info: 'LeanMiriSpec.Correspondence.layoutOfEncodedTyId_floatCastScalar' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.layoutOfEncodedTyId_floatCastScalar

/--
info: 'LeanMiriSpec.Correspondence.finish_write_anyLocal_from_mid_hooks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.finish_write_anyLocal_from_mid_hooks

/--
info: 'LeanMiriSpec.Correspondence.IsFloatCastScalarTy.of_kind_eq' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.IsFloatCastScalarTy.of_kind_eq

/--
info: 'LeanMiriSpec.Correspondence.finish_write_anyLocal_preserves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.finish_write_anyLocal_preserves

/--
info: 'LeanMiriSpec.Correspondence.IsFloatCastScalarTy.align_pow2_le_29' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.IsFloatCastScalarTy.align_pow2_le_29

/--
info: 'LeanMiriSpec.Correspondence.finish_write_unpromoted_indirect_from_mid_hooks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.finish_write_unpromoted_indirect_from_mid_hooks

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_constant_indirect_dst_simulation_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.step_cast_float_constant_indirect_dst_simulation_mode

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_copy_indirect_dst_simulation_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.step_cast_float_copy_indirect_dst_simulation_mode

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_move_indirect_dst_simulation_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.step_cast_float_move_indirect_dst_simulation_mode

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_constant_indirect_floatDst_simulation_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.step_cast_float_constant_indirect_floatDst_simulation_mode

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_copy_indirect_floatDst_simulation_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.step_cast_float_copy_indirect_floatDst_simulation_mode

/--
info: 'LeanMiriSpec.Correspondence.step_cast_float_move_indirect_floatDst_simulation_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.step_cast_float_move_indirect_floatDst_simulation_mode

/--
info: 'LeanMiriSpec.Correspondence.floatCast_dst_localRel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatCast_dst_localRel

/--
info: 'LeanMiriSpec.Correspondence.floatToFloat_dst_size' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatToFloat_dst_size

/--
info: 'LeanMiriSpec.Correspondence.scalar_fromScalarInt_inj' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.scalar_fromScalarInt_inj

/--
info: 'LeanMiriSpec.Correspondence.detBits_eq_iff_agrees' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.detBits_eq_iff_agrees

/--
info: 'LeanMiriSpec.Correspondence.scalar_fromBool_toBool' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.scalar_fromBool_toBool

/--
info: 'LeanMiriSpec.Correspondence.scalar_fromChar_toChar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.scalar_fromChar_toChar

/--
info: 'LeanMiriSpec.Correspondence.floatWit_stateRel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatWit_stateRel

/--
info: 'LeanMiriSpec.Correspondence.floatWit_anneal_result' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatWit_anneal_result

/--
info: 'LeanMiriSpec.Correspondence.floatWitPipeline_stateRel_pre' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatWitPipeline_stateRel_pre

/--
info: 'LeanMiriSpec.Correspondence.floatWitPipeline_all_imm_pre' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatWitPipeline_all_imm_pre

/--
info: 'LeanMiriSpec.Correspondence.floatWit_scalarRel7' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatWit_scalarRel7

/--
info: 'LeanMiriSpec.Correspondence.floatWitPromoted_stateRel_pre' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatWitPromoted_stateRel_pre

/--
info: 'LeanMiriSpec.Correspondence.floatWitPromoted_all_imm_pre' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatWitPromoted_all_imm_pre

/--
info: 'LeanMiriSpec.Correspondence.floatWitIndAlloc_shape' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatWitIndAlloc_shape

/--
info: 'LeanMiriSpec.Correspondence.floatWitIndSrcAlloc_shape' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatWitIndSrcAlloc_shape

/--
info: 'LeanMiriSpec.Correspondence.floatOps_adjustNaN_pure_out_of_range' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatOps_adjustNaN_pure_out_of_range

/--
info: 'LeanMiriSpec.Correspondence.floatBits_nanChoices_quiet_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatBits_nanChoices_quiet_length

/--
info: 'LeanMiriSpec.Correspondence.cast_floatToFloat_pure_out_of_range' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.cast_floatToFloat_pure_out_of_range

/--
info: 'LeanMiriSpec.Correspondence.step_cast_floatToFloat_constant_pure_out_of_range' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.step_cast_floatToFloat_constant_pure_out_of_range

/--
info: 'LeanMiriSpec.Correspondence.floatWit_nanChoice_pure4_out_of_range' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.floatWit_nanChoice_pure4_out_of_range

end AxiomGuards

end LeanMiriSpec.Correspondence
