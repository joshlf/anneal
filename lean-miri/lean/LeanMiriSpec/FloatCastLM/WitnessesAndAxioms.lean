/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.FloatCastLM.DetModeAndBoundaries

/-!
# Float-cast witnesses and axiom guards (`LeanMiriSpec.FloatCastLM.WitnessesAndAxioms`)

Final layer (Parts 10 and 11 and the axiom guards) of the IEEE-754 float-cast correspondence;
see the umbrella module `LeanMiriSpec.FloatCastLM` for the architectural overview and the
submodule map.

* **Part 10. Concrete edge-case witnesses**: subnormal / tie / overflow, `isize` / `usize`, and
  4-vs-6 signaling-NaN candidate witnesses (`miri_u128_max_to_f32_inf`, ...,
  `miri_snan_f64_to_f32_nanChoices_4_vs_6`).
* **Part 11. Non-vacuity of the real-step hypotheses**: end-to-end `Step.step` / `stepMirFn`
  witnesses (`floatWit_copy_move_isize_and_ub`, `floatWit_promoted_allocMap_pipeline`,
  `div_floatToFloat_deterministic_payloadNaN_step`, `floatWit_nanChoice_pure1_step`,
  `floatWit_indirect_dst_step`, `floatWit_indirect_src_step`,
  `floatWit_nanChoice_pure4_out_of_range`).
* **Axiom guards**: the `#guard_msgs (whitespace := lax) in #print axioms` guards for every
  public theorem of `LeanMiriSpec.FloatCastLM` (all submodules; "this file" in the guard-section
  prose refers to that whole development), pinned to the standard axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

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
