/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Trusted.Rustc.V2026_08_01.MirSemantics.Places
import Anneal.Mir.IeeeFloatArith
import MiniRustSpec.FloatArithMR

/-!
# Episode 2 IEEE-754 Float Arithmetic & `ucg#630` `Ptr2IntTransmutePolicy` Dual-Authority Tests

End-to-end verification suite and cross-root kernel bridge across ALL THREE engines
(`Trusted.Rustc.{V2026_06_01,V2026_08_01}.MirSemantics`, pinned `MiniRustSpec`, and vendored
`lean-miri`):

1. **Direct Root-Lake Witnesses (`W1`–`W6` & `V2026_06_01` <-> `V2026_08_01` Dialect Parity)**:
   - `W1`: finite `1.0 + 2.0 = 3.0`, subnormal `0x00000001 + 0x00000001 = 0x00000002`, overflow
     `f32::MAX + f32::MAX = +Inf` & ties-to-even boundaries, signed-zero sums/products, exact
     `rem`, and `w1_mr_finite_subnormal_overflow`;
   - `W2`: IEEE-754 comparisons (`-0.0 == +0.0`, `qNaN != qNaN`, `!(sNaN < 1.0)`), `cl/1023458250`
     sNaN-payload-preserving unary negation (`f32`/`f64`), and `w2_mr_cmp_and_snan_neg_xor_carrier`;
   - `W3`: `miri#5643` `nanChoices` `.deterministic` vs. `.nondeterministic` mode sensitivity
     (`1` vs. `4` on qNaN, `1` vs. `6` on sNaN), `.sub` vs. `.add` candidate-list order difference
     on `1.0 - qNaN(0x7FC0002A)`, and `w3_mr_nanChoices_det_vs_nondet`;
   - `W4`: uninit float local UB, UB-free `1.0 / +0.0 = +Inf` vs. integer `1 / 0` UB, `f16`/`f128`
     & float `bitXor` fail-closed `.unsupported`, and MiniRust no-float-local comparison rejection
     (`w4_mr_uninit_divzero_and_no_float_local_rejection`);
   - `W5`: `ucg#630` vs. `reference#1752` `Ptr2IntTransmutePolicy` flip-direction witness across
     scalar `*const T -> usize` and composite `(*const u8, *const u8) -> (*const u8, usize)` /
     `struct Mixed` (`.strictUcg630Ub` faults `.ub` while `.stripProvenance` preserves pointer
     provenance and strips integer slots, matching `Mach` & `MachTB` + `MachTB.wfLive`), plus
     provenance-free `f32 <-> u32` agreement under both policies;
   - `W6`: shared no-forgery (`usize -> &u8`) and uninit-byte transmute UB under BOTH policies;
   - `V2026_06_01` <-> `V2026_08_01` universal + concrete lockstep on `evalFloatNeg`,
     `evalFloatCmp`, `evalFloatBinOp`, `EvalFloatBinOpRel`, `nanChoices`, and `policyRejectsProv`.
2. **Cross-Root Dual-Authority Kernel Bridge (`run_cmd`)**:
   Loads BOTH `.lake/build/lib/lean` (`Anneal.Mir.IeeeFloatArith`, `MiniRustSpec.FloatArithMR`)
   and `examples/.lake/build/lib/lean` (`LeanMiriSpec.FloatArithLM`) into a fresh Lean kernel
   environment and verifies:
   - 6 kernel-checked dual witness theorems (`w1_dual` .. `w6_dual`) and master
     `unifiedFloatArithAndUcg630DualBundle` conjoining all `W1`–`W6` MR/LM witnesses plus
     general correspondence/step-simulation theorems from both authorities;
   - 5 well-typed negative controls verified to be REJECTED by the Lean kernel;
   - Exhaustive zero-host-`Float`, constructive (`[propext, Quot.sound]`) axiom audit on
     `Anneal.Mir.IeeeFloatArith`, standard-axiom & non-triviality audit on `FloatArithMR` +
     `FloatArithLM` + cross-root theorems, module-import isolation (zero `MiniRustSpec.*`
     imports in `LeanMiriSpec.FloatArithLM`), and self-tests for `sorryAx` / `Lean.ofReduceBool` /
     `isTrivialProp`;
   - Transitive constant reachability from `unifiedFloatArithAndUcg630DualBundle` to `Trusted`,
     `MiniRustSpec.Interp`, and vendored `Miri.Interpreter`.
3. **Local Test-Module Axiom Audit**:
   Verifies every declaration in `tests/mir/FloatArithAndUcg630Tests.lean` uses only standard
   Lean axioms with zero `sorryAx`, zero `Lean.ofReduceBool`, and zero host `Float`.
-/

namespace Anneal.Mir.FloatArithAndUcg630Tests

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.Mir.IeeeFloatArith
open MiniRustSpec.FloatArithMR

/-! ## §1. Direct Root-Lake End-to-End Witnesses (`Trusted` + `IeeeFloatArith` + `FloatArithMR`) -/

private abbrev tF32Ty : Ty := { kind := .float .f32, layoutIdx := 0 }
private abbrev tF32LayoutTy : Ty := { kind := .float .f32, layoutIdx := 1 }
private abbrev tF16Ty : Ty := { kind := .float .f16, layoutIdx := 0 }
private abbrev tF128Ty : Ty := { kind := .float .f128, layoutIdx := 0 }
private abbrev tU32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
private abbrev tUsizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
private abbrev tPtrU8Ty : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }
private abbrev tRefU8Ty : Ty := { kind := .ref .not (.uint .u8), layoutIdx := 0 }

private abbrev mkFConst (ty : Ty) (bits sizeBytes : Nat) : Operand :=
  .constant { ty := ty, val := .scalar (.int ⟨bits, sizeBytes⟩) }

private def tFloatLayouts : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [ { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .arbitrary [] [],
          variants := .single 0, isUninhabited := false },
        { size := ⟨4⟩, align := ⟨4⟩,
          backendRepr := .scalar (.initialized (.float 32) ⟨0, 0xFFFFFFFF⟩),
          fields := .primitive, variants := .single 0, isUninhabited := false } ] }

/-- **`W1` End-to-End Witness (Root Lake)**: finite `1.0 + 2.0 = 3.0`, subnormal doubling,
`f32::MAX` overflow & ties-to-even boundary, signed-zero sums & products, exact IEEE-754 `rem`,
and MiniRust `w1_mr_finite_subnormal_overflow`. -/
theorem w1_finite_subnormal_overflow_signed_zero_and_rem :
    evalFloatArithBase .add .binary32 0x3F800000 0x40000000 = .some 0x40400000 ∧
    evalFloatArithBase .add .binary32 0x00000001 0x00000001 = .some 0x00000002 ∧
    evalFloatArithBase .add .binary32 0x7F7FFFFF 0x7F7FFFFF = .some 0x7F800000 ∧
    evalFloatBinOp .add .binary32 0x7F7FFFFF 0x73000000 = .some ⟨0x7F800000, 4⟩ ∧
    evalFloatArithBase .add .binary32 0x80000000 0x80000000 = .some 0x80000000 ∧
    evalFloatArithBase .add .binary32 0x80000000 0x00000000 = .some 0x00000000 ∧
    evalFloatArithBase .mul .binary32 0x80000000 0x00000000 = .some 0x80000000 ∧
    evalFloatArithBase .rem .binary32 0x40B00000 0x40000000 = .some 0x3FC00000 ∧
    evalFloatArithBase .rem .binary32 0xC0B00000 0x40000000 = .some 0xBFC00000 ∧
    evalRvalue .nil
      (.binaryOp .add (mkFConst tF32Ty 0x3F800000 4) (mkFConst tF32Ty 0x40000000 4)) =
      .ok (.scalar ⟨0x40400000, 4⟩) .nil emptyMemory := by
  obtain ⟨hSub32, _, _, hOvTie, _⟩ := w1_mr_finite_subnormal_overflow
  have _ := @evalFloatArithBase_rem_finite_exact
  exact ⟨by decide +kernel, hSub32, by decide +kernel, hOvTie,
    by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl⟩

/-- **`W2` End-to-End Witness (Root Lake)**: IEEE-754 comparisons (`-0.0 == +0.0`, `qNaN != qNaN`,
`!(sNaN < 1.0)`), `cl/1023458250` sNaN-payload-preserving bitwise unary negation (`f32`/`f64`),
and MiniRust `w2_mr_cmp_and_snan_neg_xor_carrier`. -/
theorem w2_cmp_and_snan_payload_preserving_neg :
    evalFloatCmp .eq .binary32 0x80000000 0x00000000 = .some true ∧
    evalFloatCmp .eq .binary32 0x7FC00000 0x7FC00000 = .some false ∧
    evalFloatCmp .ne .binary32 0x7FC00000 0x7FC00000 = .some true ∧
    evalFloatCmp .lt .binary32 0x7FA00001 0x3F800000 = .some false ∧
    evalFloatNeg .binary32 0x7FA00001 = 0xFFA00001 ∧
    isSignalingNaNBits .binary32 0x7FA00001 = true ∧
    isSignalingNaNBits .binary32 0xFFA00001 = true ∧
    evalFloatNeg .binary64 0x7FF0000000000001 = 0xFFF0000000000001 ∧
    isSignalingNaNBits .binary64 0xFFF0000000000001 = true ∧
    evalRvalue .nil (.unaryOp .neg (mkFConst tF32Ty 0x7FA00001 4)) =
      .ok (.scalar ⟨0xFFA00001, 4⟩) .nil emptyMemory := by
  obtain ⟨hZeroEq, hQnanEq, hQnanNe, _, _, _, _, _, _, _, hSnan64After, hNeg64, _⟩ :=
    w2_mr_cmp_and_snan_neg_xor_carrier
  rw [hNeg64] at hSnan64After
  exact ⟨hZeroEq, hQnanEq, hQnanNe, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    hNeg64, hSnan64After, rfl⟩

/-- **`W3` End-to-End Witness (Root Lake)**: `miri#5643` `nanChoices` mode sensitivity
(`.deterministic` length `1` vs. `.nondeterministic` length `4` on qNaN `0x7FC00001` and
length `6` on sNaN `0x7FA00001`), `.sub` vs. `.add` candidate-list order difference on
`1.0 - qNaN(0x7FC0002A)`, and MiniRust `w3_mr_nanChoices_det_vs_nondet`. -/
theorem w3_nanChoices_mode_sensitivity_and_sub_order :
    (nanChoices .binary32 [(.binary32, 0x7FC00001)] .deterministic).length = 1 ∧
    (nanChoices .binary32 [(.binary32, 0x7FC00001)] .nondeterministic).length = 4 ∧
    (nanChoices .binary32 [(.binary32, 0x7FA00001)] .deterministic).length = 1 ∧
    (nanChoices .binary32 [(.binary32, 0x7FA00001)] .nondeterministic).length = 6 ∧
    nanChoices .binary32 [(.binary32, 0x7FA00001), (.binary32, 0x3F800000)] .deterministic =
      [0x7FC00000] ∧
    nanChoices .binary32 [(.binary32, 0x7FA00001), (.binary32, 0x3F800000)] .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0x7FE00001, 0xFFE00001, 0x7FA00001, 0xFFA00001] ∧
    nanChoices .binary32 [(.binary32, 0x3F800000), (.binary32, 0x7FC0002A)] .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0x7FC0002A, 0xFFC0002A] ∧
    nanChoices .binary32 [(.binary32, 0x3F800000), (.binary32, evalFloatNeg .binary32 0x7FC0002A)]
        .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0xFFC0002A, 0x7FC0002A] ∧
    nanChoices .binary32 [(.binary32, 0x3F800000), (.binary32, 0x7FC0002A)] .nondeterministic ≠
      nanChoices .binary32 [(.binary32, 0x3F800000), (.binary32, evalFloatNeg .binary32 0x7FC0002A)]
        .nondeterministic := by
  obtain ⟨hLen4, _, hDetPair, hNondetPair, _⟩ := w3_mr_nanChoices_det_vs_nondet
  have _ := @nanChoices_sub_vs_add_neg_order_witness
  exact ⟨by decide +kernel, hLen4, by decide +kernel, by decide +kernel,
    hDetPair, hNondetPair, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **`W4` End-to-End Witness (Root Lake)**: uninit float local UB, UB-free `1.0 / +0.0 = +Inf`
vs. integer `1 / 0` UB, `f16`/`f128` & float `bitXor` fail-closed `.unsupported`, and MiniRust
no-float-local comparison rejection (`w4_mr_uninit_divzero_and_no_float_local_rejection`). -/
theorem w4_uninit_divzero_f16_bitxor_and_mr_no_float_local_rejection :
    evalRvalue [.uninit] (.unaryOp .neg (.copy ⟨0, .nil⟩)) emptyMemory
        [⟨.not, tF32Ty, .none⟩] emptyLayoutTable = .ub ∧
    evalFloatArithBase .div .binary32 0x3F800000 0x00000000 = .some 0x7F800000 ∧
    evalScalarBinOp .div ⟨1, 4⟩ ⟨0, 4⟩ [] emptyMemory true = .ub ∧
    evalRvalue .nil (.unaryOp .neg (mkFConst tF16Ty 0x3C00 2)) = .unsupported ∧
    evalRvalue .nil (.unaryOp .neg (mkFConst tF128Ty 0 16)) = .unsupported ∧
    evalFloatBinOp .bitXor .binary32 0x3F800000 0x40000000 = .none ∧
    evalRvalue .nil
      (.binaryOp .bitXor (mkFConst tF32Ty 0x3F800000 4) (mkFConst tF32Ty 0x40000000 4)) =
      .unsupported ∧
    (MiniRustSpec.Correspondence.translateLocals faConstCmpOneNegZeroBody.layouts 0
      faConstCmpOneNegZeroBody.localDecls).isSome = true ∧
    MiniRustSpec.Correspondence.translateFn faConstCmpOneNegZeroBody = none ∧
    MiniRustSpec.Correspondence.inFragment faConstCmpOneNegZeroBody = false ∧
    MiniRustSpec.Correspondence.progInFragmentWithIntrinsics faConstCmpOneNegZeroBody [] = false := by
  obtain ⟨_, _, hDivInf, _, _, _, _, _, _, hTL, hTF, hInF, hProgInF, _⟩ :=
    w4_mr_uninit_divzero_and_no_float_local_rejection
  exact ⟨rfl, hDivInf, rfl, finding1_f16_f128_fail_closed.1, finding1_f16_f128_fail_closed.2.1,
    rfl, rfl, hTL, hTF, hInF, hProgInF⟩

/-- **`W5` End-to-End Witness (Root Lake)**: `ucg#630` vs. `reference#1752`
`Ptr2IntTransmutePolicy` flip-direction across scalar `*const u8 -> usize` and composite
`(*const u8, *const u8) -> (*const u8, usize)` / `struct Mixed` (matching MiniRust `Mach` &
`MachTB` + `MachTB.wfLive`), plus provenance-free `f32 <-> u32` agreement under BOTH policies. -/
theorem w5_ptr2int_policy_flip_and_float_bits_agreement :
    let ptrLocals : List LocalSlot := [.init (.ptr { allocId := 1, offsetBytes := 0x1000 } 8)]
    let ptrDecls : List LocalDecl := [⟨.not, tPtrU8Ty, .none⟩]
    let pA : ProvenancePtr := { allocId := 7, offsetBytes := 0x1000 }
    let pB : ProvenancePtr := { allocId := 9, offsetBytes := 0x2000 }
    let tupLocals : List LocalSlot := [.init (.aggregate 0 [.ptr pA 8, .ptr pB 8])]
    let tupDecls : List LocalDecl := [⟨.mut, faPolPtrPtrTupTy, .none⟩]
    let f32Locals : List LocalSlot := [.init (.scalar ⟨0x7FA00001, 4⟩)]
    -- Scalar *const u8 -> usize policy flip
    evalByteCast ptrLocals (.copy ⟨0, .nil⟩) tUsizeTy emptyMemory ptrDecls emptyLayoutTable
        .strictUcg630Ub = .ub ∧
    evalByteCast ptrLocals (.copy ⟨0, .nil⟩) tUsizeTy emptyMemory ptrDecls emptyLayoutTable
        .stripProvenance = .ok (.scalar ⟨0x1000, 8⟩) ptrLocals emptyMemory ∧
    -- Composite (*const u8, *const u8) -> (*const u8, usize) & struct Mixed selective flip
    evalByteCast tupLocals (.copy ⟨0, .nil⟩) faPolPtrUsizeTupTy emptyMemory tupDecls
        faPolicyLayouts .strictUcg630Ub = .ub ∧
    evalByteCast tupLocals (.copy ⟨0, .nil⟩) faPolPtrUsizeTupTy emptyMemory tupDecls
        faPolicyLayouts .stripProvenance =
      .ok (.aggregate 0 [.ptr pA 8, .scalar ⟨0x2000, 8⟩]) tupLocals emptyMemory ∧
    evalByteCast tupLocals (.copy ⟨0, .nil⟩) faPolMixedStructTy emptyMemory tupDecls
        faPolicyLayouts .strictUcg630Ub = .ub ∧
    evalByteCast tupLocals (.copy ⟨0, .nil⟩) faPolMixedStructTy emptyMemory tupDecls
        faPolicyLayouts .stripProvenance =
      .ok (.aggregate 0 [.ptr pA 8, .scalar ⟨0x2000, 8⟩]) tupLocals emptyMemory ∧
    -- Provenance-free f32 <-> u32 agreement under BOTH policies (sNaN payload preserved)
    (∀ policy,
      evalByteCast f32Locals (.copy ⟨0, .nil⟩) tU32Ty emptyMemory
          [⟨.not, tF32LayoutTy, .none⟩] tFloatLayouts policy =
        .ok (.scalar ⟨0x7FA00001, 4⟩) f32Locals emptyMemory ∧
      evalByteCast f32Locals (.copy ⟨0, .nil⟩) tF32LayoutTy emptyMemory
          [⟨.not, tU32Ty, .none⟩] tFloatLayouts policy =
        .ok (.scalar ⟨0x7FA00001, 4⟩) f32Locals emptyMemory) := by
  obtain ⟨_, _, _, _, _, _, hTupStrict, hTupStrip, hMixStrict, hMixStrip, _⟩ :=
    w5_mr_ptr2int_policy_flip_mach_and_machTB
  have _ := @transmute_ptr_to_usize_policy_separation_witness
  have _ := @evalByteCast_composite_policy_separation_witness
  have _ := @transmute_float_bits_witness
  have _ := @evalByteCast_eq_of_provFree
  exact ⟨rfl, rfl, hTupStrict, hTupStrip, hMixStrict, hMixStrip,
    fun policy => by cases policy <;> exact ⟨rfl, rfl⟩⟩

/-- **`W6` End-to-End Witness (Root Lake)**: shared no-forgery (`usize -> &u8`) and
uninitialized-byte transmute UB under BOTH `.strictUcg630Ub` and `.stripProvenance`, paired with
`w6_mr_no_forge_ref_uninit`. -/
theorem w6_shared_no_forgery_and_uninit_ub_both_policies :
    (∀ policy,
      evalByteCast [.init (.scalar ⟨0x1000, 8⟩)] (.copy ⟨0, .nil⟩) tRefU8Ty emptyMemory
          [⟨.not, tUsizeTy, .none⟩] emptyLayoutTable policy = .ub) ∧
    (∀ policy,
      evalByteCast [.uninit] (.copy ⟨0, .nil⟩) tUsizeTy emptyMemory
          [⟨.not, tUsizeTy, .none⟩] emptyLayoutTable policy = .ub) ∧
    (∀ mode policy,
      evalByteCast [.init (.scalar ⟨256, 8⟩)] (.copy ⟨0, .nil⟩) faPolRefU8Ty emptyMemory
          [⟨.mut, faPolUsizeTy, .none⟩] faPolicyLayouts policy = .ub ∧
      EvalRvalueFloatRel mode policy [.init (.scalar ⟨256, 8⟩)]
          (.cast .transmute (.copy ⟨0, .nil⟩) faPolRefU8Ty) emptyMemory
          [⟨.mut, faPolUsizeTy, .none⟩] faPolicyLayouts .ub) ∧
    (∀ policy,
      decodeTypedValueFromBytes defaultCodecFuel faPolicyLayouts faPolU64Ty
        (List.replicate 8 .uninit) policy = none) := by
  obtain ⟨hMrForge, _, _, _, _, _, _, _, hMrUninit, _⟩ := w6_mr_no_forge_ref_uninit
  have _ := @evalByteCastRichWithPolicy_struct_ref_no_forge
  exact ⟨fun policy => by cases policy <;> rfl,
    fun policy => by cases policy <;> rfl,
    hMrForge, hMrUninit⟩

/-- **Dialect Lockstep (`V2026_06_01` <-> `V2026_08_01`)**: universal and concrete parity
across both trusted rustc MIR dialects on `evalFloatNeg`, `evalFloatCmp`, `evalFloatBinOp`,
`EvalFloatBinOpRel`, `nanChoices`, and `policyRejectsProv` / `Ptr2IntTransmutePolicy`. -/
theorem dialect_v2026_06_01_v2026_08_01_lockstep :
    -- Universal cross-dialect parity
    (∀ f bits, Trusted.Rustc.V2026_08_01.MirSemantics.evalFloatNeg (fmt08 f) bits =
      evalFloatNeg f bits) ∧
    (∀ op f a b,
      Trusted.Rustc.V2026_08_01.MirSemantics.evalFloatCmp (binOp08 op) (fmt08 f) a b =
        evalFloatCmp op f a b) ∧
    (∀ op f a b,
      Trusted.Rustc.V2026_08_01.MirSemantics.evalFloatBinOp (binOp08 op) (fmt08 f) a b =
        Option.map scalarInt08 (evalFloatBinOp op f a b)) ∧
    (∀ mode op f a b out,
      Trusted.Rustc.V2026_08_01.MirSemantics.EvalFloatBinOpRel
          (mode08 mode) (binOp08 op) (fmt08 f) a b (scalarInt08 out) ↔
        EvalFloatBinOpRel mode op f a b out) ∧
    (∀ t inputs mode,
      Trusted.Rustc.V2026_08_01.MirSemantics.nanChoices
          (fmt08 t) (inputs.map nanInput08) (mode08 mode) =
        nanChoices t inputs mode) ∧
    (∀ policy bs,
      Trusted.Rustc.V2026_08_01.MirSemantics.policyRejectsProv
          (policy08 policy) (bs.map abstractByte08) =
        policyRejectsProv policy bs) ∧
    -- Concrete V2026_08_01 <-> V2026_06_01 witnesses
    (Trusted.Rustc.V2026_08_01.MirSemantics.evalFloatNeg .binary32 0x7FA00001 = 0xFFA00001 ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.evalFloatBinOp .add .binary32 0x3F800000 0x40000000 =
        .some ⟨0x40400000, 4⟩ ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.nanChoices
          .binary32 [(.binary32, 0x7FA00001)] .nondeterministic =
        nanChoices .binary32 [(.binary32, 0x7FA00001)] .nondeterministic ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.policyRejectsProv
          .strictUcg630Ub [.init 0 (.some (1, 0))] = true ∧
      Trusted.Rustc.V2026_08_01.MirSemantics.policyRejectsProv
          .stripProvenance [.init 0 (.some (1, 0))] = false) :=
  ⟨evalFloatNeg_parity, evalFloatCmp_parity, evalFloatBinOp_parity, EvalFloatBinOpRel_parity,
    nanChoices_parity, policyRejectsProv_parity,
    ⟨by decide +kernel,
      (evalFloatBinOp_parity .add .binary32 0x3F800000 0x40000000).trans (by
        have h : evalFloatArithBase .add .binary32 0x3F800000 0x40000000 = .some 0x40400000 := by
          decide +kernel
        unfold evalFloatBinOp; dsimp only [evalFloatCmp]; rw [h]; rfl),
      nanChoices_parity .binary32 [(.binary32, 0x7FA00001)] .nondeterministic,
      rfl, rfl⟩⟩

/-! ## §2. Cross-Root Dual-Authority Kernel Bridge (`IeeeFloatArith` + `FloatArithMR` + `FloatArithLM`) -/

open Lean Elab Command Meta in
run_cmd do
  let opts := (← getOptions).setBool `Elab.async false
  let sp : SearchPath := [System.FilePath.mk ".lake/build/lib/lean",
                          System.FilePath.mk "examples/.lake/build/lib/lean"]
  initSearchPath (← findSysroot) sp
  let baseEnv ← importModules
    #[{ module := `Anneal.Mir.IeeeFloatArith },
      { module := `MiniRustSpec.FloatArithMR },
      { module := `LeanMiriSpec.FloatArithLM }]
    {} 0
  let ns := `Anneal.Mir.FloatArithAndUcg630Tests.CrossRoot
  let ieeeNs := `Anneal.Mir.IeeeFloatArith
  let mrNs := `MiniRustSpec.FloatArithMR
  let lmNs := `LeanMiriSpec.FloatArithLM
  let tSem := `Trusted.Rustc.V2026_06_01.MirSemantics
  let tAst := `Trusted.Rustc.V2026_06_01.MirAst
  let act : CoreM (Nat × Nat × Nat × Nat × Nat × Nat × Array Name) := do
    let addThm (name : Name) (ty pf : Expr) : CoreM Unit := do
      addDecl <| .thmDecl { name, levelParams := [], type := ty, value := pf }
    let mkThmRef (n : Name) : CoreM (Expr × Expr) := do
      let env ← getEnv
      let some ci := env.find? n | throwError "cross-root: missing constant {n}"
      let lvls := ci.levelParams.map (fun _ => Level.zero)
      let c := mkConst n lvls
      let ty ← MetaM.run' <| inferType c
      return (ty, c)
    let conjoinAll (names : List Name) : CoreM (Expr × Expr) := do
      match names with
      | [] => throwError "cross-root: empty theorem conjunction"
      | n :: rest =>
        let mut (accTy, accPf) ← mkThmRef n
        for m in rest do
          let (mTy, mPf) ← mkThmRef m
          accPf := mkApp4 (mkConst ``And.intro []) accTy mTy accPf mPf
          accTy := mkApp2 (mkConst ``And []) accTy mTy
        return (accTy, accPf)

    -- 1. Construct and kernel-check the 6 unified cross-root `W1`–`W6` dual witness theorems
    --    and master `unifiedFloatArithAndUcg630DualBundle`.
    let dualPairs : List (Name × Name × Name) :=
      [ (`w1_dual, mrNs ++ `w1_mr_finite_subnormal_overflow, lmNs ++ `w1_lm_finite_subnormal_overflow),
        (`w2_dual, mrNs ++ `w2_mr_cmp_and_snan_neg_xor_carrier, lmNs ++ `w2_lm_cmp_and_snan_neg),
        (`w3_dual, mrNs ++ `w3_mr_nanChoices_det_vs_nondet, lmNs ++ `w3_lm_nan_choices_and_sub_order),
        (`w4_dual, mrNs ++ `w4_mr_uninit_divzero_and_no_float_local_rejection, lmNs ++ `w4_lm_uninit_divzero_and_f16_boundary),
        (`w5_dual, mrNs ++ `w5_mr_ptr2int_policy_flip_mach_and_machTB, lmNs ++ `w5_lm_ptr2int_policy_flip),
        (`w6_dual, mrNs ++ `w6_mr_no_forge_ref_uninit, lmNs ++ `w6_lm_no_forge_ref_uninit) ]
    let mut added : Array Name := #[]
    let mut dualNames : List Name := []
    for (tag, mrThm, lmThm) in dualPairs do
      let outName := ns ++ tag
      let (ty, pf) ← conjoinAll [mrThm, lmThm]
      addThm outName ty pf
      added := added.push outName
      dualNames := dualNames ++ [outName]

    let generalLmThms : List Name :=
      [ lmNs ++ `step_float_unaryNeg_copy_simulation,
        lmNs ++ `step_float_cmp_copy_copy_simulation,
        lmNs ++ `step_float_arith_copy_copy_deterministic_simulation,
        lmNs ++ `step_float_arith_copy_copy_nondet_soundness,
        lmNs ++ `step_float_arith_copy_copy_nondet_completeness,
        lmNs ++ `alloc_readScalar_strip_runtime,
        lmNs ++ `alloc_readScalar_ctfe_rejects_prov,
        lmNs ++ `miri_transmute_ref_no_forge_ub,
        lmNs ++ `miri_transmute_uninit_ub ]
    let generalMrThms : List Name :=
      [ mrNs ++ `fa_no_fragment_admits_float_arith_or_cmp,
        mrNs ++ `fa_sym_mr_negXor_f32_lockstep,
        mrNs ++ `fa_sym_mr_negXor_f64_lockstep,
        mrNs ++ `fa_bridge_evalFloatBinOpRel_mach_steps,
        mrNs ++ `fa_ptr2int_live_mach_and_machTB_wfLive,
        mrNs ++ `fa_composite_tuple_struct_policy_correspondence,
        mrNs ++ `fa_no_forge_ref_and_uninit_live_mach_and_machTB_wfLive ]

    let masterName := ns ++ `unifiedFloatArithAndUcg630DualBundle
    let (masterTy, masterPf) ← conjoinAll (dualNames ++ generalLmThms ++ generalMrThms)
    addThm masterName masterTy masterPf
    added := added.push masterName

    -- 2. Negative controls on scratch copies of the kernel environment:
    --    first verify every semantic LHS is well-typed (so rejection is semantic, never a typo),
    --    then assert the Lean kernel REJECTS all 5 forged theorems!
    let natTy := mkConst ``Nat
    let boolTy := mkConst ``Bool
    let boolTrue := mkConst ``Bool.true
    let boolFalse := mkConst ``Bool.false
    let optBoolTy := mkApp (mkConst ``Option [0]) boolTy
    let someTrue := mkApp2 (mkConst ``Option.some [0]) boolTy boolTrue
    let listNatTy := mkApp (mkConst ``List [0]) natTy
    let fmtTy := mkConst (tSem ++ `IeeeFormat)
    let fmtNatTy := mkApp2 (mkConst ``Prod [0, 0]) fmtTy natTy
    let natPairTy := mkApp2 (mkConst ``Prod [0, 0]) natTy natTy
    let abTy := mkConst (tSem ++ `AbstractByte)

    let nanCmpLhs := mkApp4 (mkConst (tSem ++ `evalFloatCmp))
      (mkConst (tAst ++ `BinOp.eq)) (mkConst (tSem ++ `IeeeFormat.binary32))
      (mkNatLit 0x7FC00000) (mkNatLit 0x7FC00000)
    let snanNegLhs := mkApp2 (mkConst (tSem ++ `evalFloatNeg))
      (mkConst (tSem ++ `IeeeFormat.binary32)) (mkNatLit 0x7FA00001)
    let snanIn := mkApp4 (mkConst ``Prod.mk [0, 0]) fmtTy natTy
      (mkConst (tSem ++ `IeeeFormat.binary32)) (mkNatLit 0x7FA00001)
    let snanList := mkApp3 (mkConst ``List.cons [0]) fmtNatTy snanIn
      (mkApp (mkConst ``List.nil [0]) fmtNatTy)
    let nanChoicesLhs := mkApp3 (mkConst (tSem ++ `nanChoices))
      (mkConst (tSem ++ `IeeeFormat.binary32)) snanList
      (mkConst (tSem ++ `FloatArithMode.nondeterministic))
    let detOnlyList := mkApp3 (mkConst ``List.cons [0]) natTy (mkNatLit 0x7FC00000)
      (mkApp (mkConst ``List.nil [0]) natTy)
    let provVal := mkApp2 (mkConst ``Option.some [0]) natPairTy
      (mkApp4 (mkConst ``Prod.mk [0, 0]) natTy natTy (mkNatLit 1) (mkNatLit 0))
    let provByte := mkApp2 (mkConst (tSem ++ `AbstractByte.init))
      (mkApp (mkConst ``UInt8.ofNat) (mkNatLit 0)) provVal
    let provBytes := mkApp3 (mkConst ``List.cons [0]) abTy provByte
      (mkApp (mkConst ``List.nil [0]) abTy)
    let polLhs := mkApp2 (mkConst (tSem ++ `policyRejectsProv))
      (mkConst (tSem ++ `Ptr2IntTransmutePolicy.strictUcg630Ub)) provBytes

    -- Positive well-typedness guard on every semantic negative-control LHS
    for (tag, lhs, expTy) in
        [ ("nanCmpLhs", nanCmpLhs, optBoolTy),
          ("snanNegLhs", snanNegLhs, natTy),
          ("nanChoicesLhs", nanChoicesLhs, listNatTy),
          ("polLhs", polLhs, boolTy) ] do
      let okTy ← MetaM.run' do
        check lhs
        isDefEq (← inferType lhs) expTy
      unless okTy do
        throwError "cross-root: negative-control LHS {tag} is ill-typed"

    let saved ← getEnv
    let rejects (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure false catch _ => pure true
      setEnv saved
      return r
    let forged : List (String × Declaration) :=
      [ ("ill-typed 0 = 1 theorem", .thmDecl {
          name := ns ++ `forged.zeroEqOne, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 0) (mkNatLit 1),
          value := mkApp2 (mkConst ``Eq.refl [1]) natTy (mkNatLit 0) }),
        ("forged NaN equality (evalFloatCmp .eq qNaN qNaN = some true)", .thmDecl {
          name := ns ++ `forged.nanEqTrue, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) optBoolTy nanCmpLhs someTrue,
          value := mkApp2 (mkConst ``Eq.refl [1]) optBoolTy someTrue }),
        ("forged sNaN-quieting negation (evalFloatNeg 0x7FA00001 = 0xFFE00001)", .thmDecl {
          name := ns ++ `forged.snanNegQuiets, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) natTy snanNegLhs (mkNatLit 0xFFE00001),
          value := mkApp2 (mkConst ``Eq.refl [1]) natTy (mkNatLit 0xFFE00001) }),
        ("forged nondet nanChoices collapse to [0x7FC00000]", .thmDecl {
          name := ns ++ `forged.nanChoicesCollapse, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) listNatTy nanChoicesLhs detOnlyList,
          value := mkApp2 (mkConst ``Eq.refl [1]) listNatTy detOnlyList }),
        ("forged policy-inverted strictUcg630Ub on provenance byte", .thmDecl {
          name := ns ++ `forged.policyInverted, levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) boolTy polLhs boolFalse,
          value := mkApp2 (mkConst ``Eq.refl [1]) boolTy boolFalse }) ]
    let mut rejected : Nat := 0
    for (what, d) in forged do
      unless ← rejects d do
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1

    -- 3. Exhaustive axiom, non-triviality, host-Float-absence, & import-isolation audits
    let env ← getEnv
    let isConstructiveAx (a : Name) : Bool :=
      a == ``propext || a == ``Quot.sound
    let isStdAx (a : Name) : Bool :=
      a == ``propext || a == ``Classical.choice || a == ``Quot.sound
    let isHostFloat (d : Name) : Bool :=
      d == ``Float || (`Float).isPrefixOf d || d == ``Float32 || (`Float32).isPrefixOf d
    let rec isTrivialProp : Expr → Bool
      | .forallE _ _ body _ => isTrivialProp body
      | .letE _ _ _ body _ => isTrivialProp body
      | e =>
        if e.isConstOf ``True then true
        else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
        else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
        else false

    -- Self-tests: auditor MUST detect sorryAx, Lean.ofReduceBool, and trivial theorems!
    unless !(← collectAxioms ``sorryAx).all isStdAx do
      throwError "cross-root self-test: sorryAx was not detected"
    unless !(← collectAxioms ``Lean.ofReduceBool).all isStdAx do
      throwError "cross-root self-test: Lean.ofReduceBool was not detected"
    let trivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 1)
    let nonTrivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 2)
    unless isTrivialProp (mkConst ``True) && isTrivialProp trivEq && !isTrivialProp nonTrivEq do
      throwError "cross-root self-test: trivial theorem detector failed"

    -- Module-import isolation: LeanMiriSpec.FloatArithLM has ZERO direct or transitive
    -- MiniRustSpec.* module imports!
    unless (env.getModuleIdx? lmNs).isSome do
      throwError "cross-root: module {lmNs} not found in environment header"
    let mut visitedMods : NameSet := {}
    let mut modTodo : Array Name := #[lmNs]
    while !modTodo.isEmpty do
      let m := modTodo.back!
      modTodo := modTodo.pop
      if visitedMods.contains m then continue
      visitedMods := visitedMods.insert m
      if (`MiniRustSpec).isPrefixOf m then
        throwError "cross-root isolation failure: {lmNs} transitively imports {m}"
      if let some idx := env.getModuleIdx? m then
        for imp in env.header.moduleData[idx.toNat]!.imports do
          if !visitedMods.contains imp.module then
            modTodo := modTodo.push imp.module

    -- Collect and audit ALL constants in `Anneal.Mir.IeeeFloatArith`, `MiniRustSpec.FloatArithMR`,
    -- `LeanMiriSpec.FloatArithLM`, and the newly added cross-root declarations.
    let targetDecls : Array (Name × ConstantInfo) := env.constants.fold (init := #[]) fun acc n ci =>
      let u := privateToUserName n
      if ieeeNs.isPrefixOf u || mrNs.isPrefixOf u || lmNs.isPrefixOf u || ns.isPrefixOf u then
        acc.push (n, ci)
      else
        acc
    let mut ieeeThms : Nat := 0
    let mut mrThms : Nat := 0
    let mut lmThms : Nat := 0
    let mut crAxioms : NameSet := {}
    for (n, ci) in targetDecls do
      for d in ci.getUsedConstantsAsSet do
        if isHostFloat d then
          throwError "cross-root host-Float audit FAILED: {n} references {d}"
      let u := privateToUserName n
      match ci with
      | .thmInfo v =>
        if !n.isInternalDetail && isTrivialProp v.type then
          throwError "cross-root non-triviality audit FAILED: {n} has trivial type"
        let axs ← collectAxioms n
        if ieeeNs.isPrefixOf u then
          for a in axs do
            unless isConstructiveAx a do
              throwError "cross-root constructive audit FAILED: {n} depends on {a}"
            crAxioms := crAxioms.insert a
          ieeeThms := ieeeThms + 1
        else
          for a in axs do
            unless isStdAx a do
              throwError "cross-root standard-axiom audit FAILED: {n} depends on {a}"
            crAxioms := crAxioms.insert a
          if mrNs.isPrefixOf u then mrThms := mrThms + 1
          else if lmNs.isPrefixOf u then lmThms := lmThms + 1
      | _ => pure ()

    -- Explicitly audit the module-level `axiomAudit_*` bundles as well
    for b in [ieeeNs ++ `axiomAudit_scalars, ieeeNs ++ `axiomAudit_places,
              ieeeNs ++ `axiomAudit_cmp_identity, ieeeNs ++ `axiomAudit_ep2_bridges] do
      for a in ← collectAxioms b do
        unless isConstructiveAx a do
          throwError "cross-root constructive bundle audit FAILED: {b} depends on {a}"
    for b in [mrNs ++ `axiomAudit_choiceFree] do
      for a in ← collectAxioms b do
        unless isConstructiveAx a do
          throwError "cross-root choice-free MR bundle audit FAILED: {b} depends on {a}"
    for b in [mrNs ++ `axiomAudit_machine, lmNs ++ `axiomAudit_floatArithLM] do
      for a in ← collectAxioms b do
        unless isStdAx a do
          throwError "cross-root standard bundle audit FAILED: {b} depends on {a}"

    -- 4. Transitive constant reachability closure from `unifiedFloatArithAndUcg630DualBundle`
    --    across ALL THREE engines (Trusted + MiniRustSpec + vendored Miri)!
    let mut reach : NameSet := {}
    let mut todo : Array Name := #[masterName]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if reach.contains n then continue
      reach := reach.insert n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          if !reach.contains d then todo := todo.push d
    let requiredReach : List Name :=
      [ `Trusted.Rustc.V2026_06_01.MirSemantics.evalFloatArithBase,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalFloatCmp,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalFloatNeg,
        `Trusted.Rustc.V2026_06_01.MirSemantics.nanChoices,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalFloatBinOp,
        `Trusted.Rustc.V2026_06_01.MirSemantics.EvalFloatBinOpRel,
        `Trusted.Rustc.V2026_06_01.MirSemantics.EvalRvalueFloatRel,
        `Trusted.Rustc.V2026_06_01.MirSemantics.decodeScalarLayoutBytesNoForge,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalByteCast,
        `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
        `MiniRustSpec.Interp.steps,
        `MiniRustSpec.Interp.stepsTB,
        `MiniRustSpec.Interp.transmuteM,
        `Miri.Interpreter.FloatBits.arithmetic,
        `Miri.Interpreter.FloatBits.comparison,
        `Miri.Interpreter.FloatBits.negate,
        `Miri.Interpreter.FloatBits.nanChoices,
        `Miri.Interpreter.FloatOps.binary,
        `Miri.Interpreter.FloatOps.unary,
        `Miri.Interpreter.Step.step,
        `Miri.Interpreter.Cast.cast ]
    for req in requiredReach do
      unless reach.contains req do
        throwError "cross-root reachability failure: unifiedFloatArithAndUcg630DualBundle does not reach {req}"

    return (added.size, rejected, ieeeThms, mrThms, lmThms, requiredReach.length, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<ep2-float-arith-cross-root>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let ((addedCount, rejectedCount, ieeeThms, mrThms, lmThms, reachedCount, crAxioms), _) ←
    liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount == 7 && rejectedCount == 5 && ieeeThms ≥ 300 && mrThms ≥ 50 && lmThms ≥ 45 && reachedCount == 21 do
    throwError "cross-root: unexpected counts (added={addedCount}, rejected={rejectedCount}, ieee={ieeeThms}, mr={mrThms}, lm={lmThms}, reached={reachedCount})"
  logInfo m!"ep2 float-arith cross-root kernel bridge: added {addedCount} dual theorems, rejected {rejectedCount} forged controls, audited {ieeeThms} constructive IeeeFloatArith + {mrThms} MR + {lmThms} LM theorems (0 host Float, 0 MiniRustSpec imports in LM), reached all {reachedCount} Trusted+MiniRust+Miri constants, axioms {crAxioms}"

/-! ## §3. Local Test-Module Axiom & Host-`Float` Audit -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (c, ci) in env.constants.map₂.toList do
    for d in ci.getUsedConstantsAsSet do
      if d == ``Float || (`Float).isPrefixOf d || d == ``Float32 || (`Float32).isPrefixOf d then
        throwError "test audit failure: {c} references host float {d}"
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "test audit failure: {c} uses sorryAx"
      if a == ``Lean.ofReduceBool then throwError "test audit failure: {c} uses Lean.ofReduceBool"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "test audit failure: {c} uses non-standard axiom {a}"
    checked := checked + 1
  if checked == 0 then
    throwError "test audit failure: found 0 local declarations"
  logInfo m!"ep2 float-arith test audit: verified {checked} local declarations (standard axioms only, 0 sorryAx, 0 ofReduceBool, 0 host Float)"

end Anneal.Mir.FloatArithAndUcg630Tests
