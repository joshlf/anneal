/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.FloatCastLM.CodecAndCast
import LeanMiriSpec.FloatCastLM.RealStepDirect
import LeanMiriSpec.FloatCastLM.RealStepIndirect
import LeanMiriSpec.FloatCastLM.DetModeAndBoundaries
import LeanMiriSpec.FloatCastLM.WitnessesAndAxioms

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

Every public theorem of this development carries a
`#guard_msgs (whitespace := lax) in #print axioms` guard (standard axioms only: `propext`,
`Classical.choice`, `Quot.sound`) in `LeanMiriSpec.FloatCastLM.WitnessesAndAxioms`.

## Submodule map

This module is an umbrella: it declares nothing itself and re-exports the development, which is
split into a 4-layer acyclic diamond DAG of submodules with minimal per-layer imports
(`SimLM3_1` is deferred to `RealStepDirect`, `WitLM1_2` to `WitnessesAndAxioms`, and
`RealStepIndirect` and `DetModeAndBoundaries` are independent siblings over `RealStepDirect`) so
that no single translation unit elaborates the whole development and per-file elaboration memory
stays bounded. Every declaration lives in `namespace LeanMiriSpec.Correspondence`, so declaration
names do not depend on the submodule layout, and `import LeanMiriSpec.FloatCastLM` provides all of
them while preserving the full baseline transitive import closure (`Anneal.Mir.IeeeFloatCast`,
`LeanMiriSpec.Correspondence.SimLM3_1`, `LeanMiriSpec.Correspondence.WitLM1_2` / `Witness` via
`WitnessesAndAxioms`, and `Miri.Interpreter.{Float,FloatOps,Cast,Step}`) relied on by downstream
importers such as `LeanMiriSpec.WitFloatCastLM`.

1. `LeanMiriSpec.FloatCastLM.CodecAndCast` (Parts 0–7; imports `SimLM1_2`, `PtrLM3_1`,
   `IeeeFloatCast`, `Miri.Interpreter.{Float,FloatOps,Cast,Step}`): vendored private-helper bridges,
   formats and decoding, rounding and primitive casts, NaN classification and NaN choices, the
   float-cast hook overlay, `Cast.cast` simulation, the rvalue / step overlay with conservative
   extension, and the unified float-cast signature and results.
2. `LeanMiriSpec.FloatCastLM.RealStepDirect` (Part 8; imports `CodecAndCast`, `SimLM3_1`):
   immediate-local real-step simulation in `StateRelLM3_1` / `StepRelLM3_1`.
3. `LeanMiriSpec.FloatCastLM.RealStepIndirect` (Part 8b; imports `RealStepDirect`): promoted
   (`allocMap`) and stack-allocated (`LocalRel.indirect`) real-step simulation.
4. `LeanMiriSpec.FloatCastLM.DetModeAndBoundaries` (Parts 8c, 8d, 9; imports `RealStepDirect`):
   deterministic NaN mode, NaN-choice refinement, tightness of `FloatCastDetAgrees`, and the
   `bool` / `char` and `f16` / `f128` boundaries.
5. `LeanMiriSpec.FloatCastLM.WitnessesAndAxioms` (Parts 10, 11, axiom guards; imports
   `RealStepIndirect`, `DetModeAndBoundaries`, `WitLM1_2`): concrete edge-case witnesses,
   real-step non-vacuity witnesses, and all `#print axioms` guards.
-/
