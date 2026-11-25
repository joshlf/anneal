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
     `evalFloatCmp`, `evalFloatBinOp`, `EvalFloatBinOpRel`, `nanChoices`, and `policyRejectsProv`;
   - Round-1 hardening (`W7`–`W11`): `binary64` witnesses (`f64` subnormal / overflow / `rem`, sNaN
     negation `0x7FF4000000000001 -> 0xFFF4000000000001`, 6-element `f64` `nanChoices` sNaN set,
     `f64 <-> u64` transmute under both policies, `V2026_08_01` lockstep); the `miri#5643` finding
     that NEITHER authority negates the rhs before `nanChoices` for `.sub` (`W8`); pointer-destination,
     array-composite, and pointer-width scope of `Ptr2IntTransmutePolicy` (`W9`); MiniRust rejection
     of float operands reached only through pointer dereferences (`W10`); and `binary64`
     `EvalFloatBinOpRel` outcomes on `MachTB` + `MachTB.wfLive` (`W11`).
2. **Cross-Root Dual-Authority Kernel Bridge (`run_cmd`)**:
   Loads BOTH `.lake/build/lib/lean` (`Anneal.Mir.IeeeFloatArith`, `MiniRustSpec.FloatArithMR`)
   and `examples/.lake/build/lib/lean` (`LeanMiriSpec.FloatArithLM`) into a fresh Lean kernel
   environment and verifies:
   - 6 kernel-checked dual witness theorems (`w1_dual` .. `w6_dual`) and master
     `unifiedFloatArithAndUcg630DualBundle` conjoining all `W1`–`W6` MR/LM witnesses plus
     general correspondence/step-simulation theorems from both authorities and the
     `V2026_06_01` <-> `V2026_08_01` dialect-parity theorems;
   - 10 well-typed negative controls verified to be REJECTED by the Lean kernel, 9 of them paired
     with a positive control (the TRUE right-hand side for the same left-hand side is ACCEPTED), so
     a rejection is never an artifact of a stuck or failing kernel reduction;
   - Structural inspection of the MiniRust `Gen.Type` / `Gen.Value` / operator inductives (no float
     constructor) and automated `axiomAudit_*` bundle coverage of every public `FloatArithMR` /
     `FloatArithLM` theorem;
   - Exhaustive zero-host-`Float`, constructive (`[propext, Quot.sound]`) axiom audit on
     `Anneal.Mir.IeeeFloatArith`, standard-axiom & non-triviality audit on `FloatArithMR` +
     `FloatArithLM` + cross-root theorems, module-import isolation (zero `MiniRustSpec.*`
     imports in `LeanMiriSpec.FloatArithLM`), and self-tests for `sorryAx` / `Lean.ofReduceBool` /
     `isTrivialProp` (recursive over `∀`, `∧`, `∨`, `↔`, so `True ∧ True` or `x = x ∧ y = y` cannot
     evade the non-triviality audit);
   - Transitive constant reachability from `unifiedFloatArithAndUcg630DualBundle` to `Trusted`
     (BOTH `V2026_06_01` and `V2026_08_01`), `MiniRustSpec` (`Interp` + translation gates), and
     vendored `Miri.Interpreter` / `Miri.Memory`.
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

/-! ### §1.1 Round-1 Hardening: `binary64` Witnesses, `.sub` NaN-Candidate Order, Pointer-Width Scope -/

private abbrev tU64Ty : Ty := { kind := .uint .u64, layoutIdx := 0 }
private abbrev tF64LayoutTy : Ty := { kind := .float .f64, layoutIdx := 1 }
private abbrev tPtrMutU16Ty : Ty := { kind := .rawPtr .mut (.uint .u16), layoutIdx := 0 }
private abbrev tUsize32Ty : Ty := { kind := .uint .usize, layoutIdx := 1 }
private abbrev tPtr32Ty : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 2 }
private abbrev tU32At1Ty : Ty := { kind := .uint .u32, layoutIdx := 1 }
private abbrev tPtrArr2Ty : Ty := { kind := .array (.rawPtr .not (.uint .u8)) 2, layoutIdx := 3 }
private abbrev tUsizeArr2Ty : Ty := { kind := .array (.uint .usize) 2, layoutIdx := 4 }

/-- 64-bit table whose entry `1` is `f64` (mirrors `tFloatLayouts` for `binary64`). -/
private def tFloat64Layouts : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [ { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .arbitrary [] [],
          variants := .single 0, isUninhabited := false },
        { size := ⟨8⟩, align := ⟨8⟩,
          backendRepr := .scalar (.initialized (.float 64) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
          fields := .primitive, variants := .single 0, isUninhabited := false } ] }

/-- A well-formed 32-bit capture: entry `1` is a 4-byte `usize` / `u32`, entry `2` a 4-byte thin
pointer. -/
private def tPtr32Layouts : LayoutTable :=
  { pointerBits := 32
    isLittleEndian := true
    entries :=
      [ { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .arbitrary [] [],
          variants := .single 0, isUninhabited := false },
        { size := ⟨4⟩, align := ⟨4⟩,
          backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
          fields := .primitive, variants := .single 0, isUninhabited := false },
        { size := ⟨4⟩, align := ⟨4⟩,
          backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 0xFFFFFFFF⟩),
          fields := .primitive, variants := .single 0, isUninhabited := false } ] }

/-- 64-bit table with `[*const u8; 2]` (entry `3`) and `[usize; 2]` (entry `4`) arrays. -/
private def tPtrArrayLayouts : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [ { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .arbitrary [] [],
          variants := .single 0, isUninhabited := false },
        { size := ⟨8⟩, align := ⟨8⟩,
          backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
          fields := .primitive, variants := .single 0, isUninhabited := false },
        { size := ⟨8⟩, align := ⟨8⟩,
          backendRepr := .scalar (.initialized (.int 64 false) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
          fields := .primitive, variants := .single 0, isUninhabited := false },
        { size := ⟨16⟩, align := ⟨8⟩, backendRepr := .memory, fields := .array ⟨8⟩ 2,
          variants := .single 0, isUninhabited := false, fieldLayouts := [1] },
        { size := ⟨16⟩, align := ⟨8⟩, backendRepr := .memory, fields := .array ⟨8⟩ 2,
          variants := .single 0, isUninhabited := false, fieldLayouts := [2] } ] }

/-- **`W7` End-to-End Witness (Root Lake, `binary64`)**: the `f64` counterparts of `W1`–`W3` and
`W5` — subnormal / finite / overflow / `1.0 / +0.0` / exact `rem` / signed-zero arithmetic, IEEE-754
comparisons, sNaN-payload-preserving negation `0x7FF4000000000001 -> 0xFFF4000000000001`,
`nanChoices` (`1` deterministic vs. the 6-element nondeterministic sNaN set), `V2026_08_01`
lockstep on the same bit patterns, and provenance-free `f64 <-> u64` transmutes (plus fail-closed
`f64 -> u32` size mismatch) under BOTH `Ptr2IntTransmutePolicy` values. -/
theorem w7_f64_dual_authority_witnesses :
    (evalFloatArithBase .add .binary64 0x0000000000000001 0x0000000000000001 = .some 0x0000000000000002 ∧
     evalFloatArithBase .add .binary64 0x3FF0000000000000 0x4000000000000000 = .some 0x4008000000000000 ∧
     evalFloatArithBase .sub .binary64 0x4008000000000000 0x3FF0000000000000 = .some 0x4000000000000000 ∧
     evalFloatArithBase .add .binary64 0x7FEFFFFFFFFFFFFF 0x7FEFFFFFFFFFFFFF = .some 0x7FF0000000000000 ∧
     evalFloatArithBase .div .binary64 0x3FF0000000000000 0x0000000000000000 = .some 0x7FF0000000000000 ∧
     evalFloatArithBase .rem .binary64 0x4016000000000000 0x4000000000000000 = .some 0x3FF8000000000000 ∧
     evalFloatArithBase .mul .binary64 0x8000000000000000 0x0000000000000000 = .some 0x8000000000000000 ∧
     evalFloatCmp .eq .binary64 0x8000000000000000 0x0000000000000000 = .some true ∧
     evalFloatCmp .eq .binary64 0x7FF8000000000000 0x7FF8000000000000 = .some false ∧
     evalFloatCmp .lt .binary64 0x7FF4000000000001 0x3FF0000000000000 = .some false ∧
     evalFloatNeg .binary64 0x7FF4000000000001 = 0xFFF4000000000001 ∧
     isSignalingNaNBits .binary64 0x7FF4000000000001 = true ∧
     isSignalingNaNBits .binary64 0xFFF4000000000001 = true ∧
     nanChoices .binary64 [(.binary64, 0x7FF4000000000001), (.binary64, 0x3FF0000000000000)] .deterministic =
       [0x7FF8000000000000] ∧
     nanChoices .binary64 [(.binary64, 0x7FF4000000000001), (.binary64, 0x3FF0000000000000)] .nondeterministic =
       [0x7FF8000000000000, 0xFFF8000000000000, 0x7FFC000000000001, 0xFFFC000000000001,
        0x7FF4000000000001, 0xFFF4000000000001] ∧
     Trusted.Rustc.V2026_08_01.MirSemantics.evalFloatNeg .binary64 0x7FF4000000000001 = 0xFFF4000000000001 ∧
     Trusted.Rustc.V2026_08_01.MirSemantics.evalFloatArithBase .add .binary64 0x3FF0000000000000
       0x4000000000000000 = .some 0x4008000000000000 ∧
     Trusted.Rustc.V2026_08_01.MirSemantics.nanChoices .binary64
         [(.binary64, 0x7FF4000000000001), (.binary64, 0x3FF0000000000000)] .nondeterministic =
       [0x7FF8000000000000, 0xFFF8000000000000, 0x7FFC000000000001, 0xFFFC000000000001,
        0x7FF4000000000001, 0xFFF4000000000001]) ∧
    (∀ policy,
      evalByteCast [.init (.scalar ⟨0x7FF4000000000001, 8⟩)] (.copy ⟨0, .nil⟩) tU64Ty emptyMemory
          [⟨.not, tF64LayoutTy, .none⟩] tFloat64Layouts policy =
        .ok (.scalar ⟨0x7FF4000000000001, 8⟩) [.init (.scalar ⟨0x7FF4000000000001, 8⟩)] emptyMemory ∧
      evalByteCast [.init (.scalar ⟨0x7FF4000000000001, 8⟩)] (.copy ⟨0, .nil⟩) tF64LayoutTy emptyMemory
          [⟨.not, tU64Ty, .none⟩] tFloat64Layouts policy =
        .ok (.scalar ⟨0x7FF4000000000001, 8⟩) [.init (.scalar ⟨0x7FF4000000000001, 8⟩)] emptyMemory ∧
      evalByteCast [.init (.scalar ⟨0x7FF4000000000001, 8⟩)] (.copy ⟨0, .nil⟩) tU32Ty emptyMemory
          [⟨.not, tF64LayoutTy, .none⟩] tFloat64Layouts policy = .unsupported) :=
  ⟨by decide +kernel, fun policy => by cases policy <;> exact ⟨rfl, rfl, rfl⟩⟩

/-- **`W8` Witness (`miri#5643` `.sub` candidate order — round-1 finding)**: NEITHER authority
negates the right operand before building the NaN candidate list. `Trusted`'s `EvalFloatBinOpRel`
uses `nanChoices f [(f, a), (f, b)]` for `.sub` exactly as for `.add` / `.mul` / `.div` / `.rem`
(only `exactSumFloat` negates `b` internally), and vendored `FloatOps.binary` passes
`[leftBits, rightBits]` to `adjustNaN` for all five operators (`FloatArithLM`:
`floatOps_binary_arith_pure_index_exact`, `w7_lm_f64_and_sub_index_exact`). Hence for
`1.0 - qNaN(0x…2A)` candidate index `2` is the UN-NEGATED quieted rhs; the negated-rhs list has the
same members in a different order. NaN-producing subtraction of non-NaN operands (`∞ - ∞`) has
exactly the two preferred candidates, so a constant selector index `2` is out of range there. -/
theorem w8_sub_nanChoices_unnegated_rhs_and_two_candidate_lists :
    (∀ mode f a b out,
      EvalFloatBinOpRel mode .sub f a b out ↔
        ∃ baseBits, evalFloatArithBase .sub f a b = .some baseBits ∧
          ((isNaNBits f baseBits = true ∧
              ∃ cand, cand ∈ nanChoices f [(f, a), (f, b)] mode ∧ out = ⟨cand, f.byteWidth⟩) ∨
           (isNaNBits f baseBits = false ∧ out = ⟨baseBits, f.byteWidth⟩))) ∧
    ((nanChoices .binary32 [(.binary32, 0x3F800000), (.binary32, 0x7FC0002A)] .nondeterministic)[2]? =
       some 0x7FC0002A ∧
     (nanChoices .binary32 [(.binary32, 0x3F800000), (.binary32, evalFloatNeg .binary32 0x7FC0002A)]
       .nondeterministic)[2]? = some 0xFFC0002A ∧
     nanChoices .binary64 [(.binary64, 0x3FF0000000000000), (.binary64, 0x7FF800000000002A)] .nondeterministic =
       [0x7FF8000000000000, 0xFFF8000000000000, 0x7FF800000000002A, 0xFFF800000000002A] ∧
     nanChoices .binary64 [(.binary64, 0x3FF0000000000000),
         (.binary64, evalFloatNeg .binary64 0x7FF800000000002A)] .nondeterministic =
       [0x7FF8000000000000, 0xFFF8000000000000, 0xFFF800000000002A, 0x7FF800000000002A] ∧
     evalFloatArithBase .sub .binary32 0x7F800000 0x7F800000 = .some 0x7FC00000 ∧
     nanChoices .binary32 [(.binary32, 0x7F800000), (.binary32, 0x7F800000)] .nondeterministic =
       [0x7FC00000, 0xFFC00000] ∧
     (nanChoices .binary32 [(.binary32, 0x7F800000), (.binary32, 0x7F800000)] .nondeterministic)[2]? = none ∧
     evalFloatArithBase .sub .binary64 0x7FF0000000000000 0x7FF0000000000000 = .some 0x7FF8000000000000 ∧
     nanChoices .binary64 [(.binary64, 0x7FF0000000000000), (.binary64, 0x7FF0000000000000)]
       .nondeterministic = [0x7FF8000000000000, 0xFFF8000000000000]) ∧
    EvalFloatBinOpRel .nondeterministic .sub .binary32 0x3F800000 0x7FC0002A ⟨0x7FC0002A, 4⟩ ∧
    EvalFloatBinOpRel .nondeterministic .sub .binary32 0x3F800000 0x7FC0002A ⟨0xFFC0002A, 4⟩ ∧
    EvalFloatBinOpRel .nondeterministic .sub .binary64 0x3FF0000000000000 0x7FF800000000002A
      ⟨0x7FF800000000002A, 8⟩ :=
  ⟨fun mode f a b out => EvalFloatBinOpRel_arith_iff mode .sub f a b out rfl,
    by decide +kernel,
    (EvalFloatBinOpRel_arith_iff .nondeterministic .sub .binary32 0x3F800000 0x7FC0002A ⟨0x7FC0002A, 4⟩ rfl).mpr
      ⟨0x7FC00000, by decide +kernel, Or.inl ⟨by decide +kernel, 0x7FC0002A, by decide +kernel, rfl⟩⟩,
    (EvalFloatBinOpRel_arith_iff .nondeterministic .sub .binary32 0x3F800000 0x7FC0002A ⟨0xFFC0002A, 4⟩ rfl).mpr
      ⟨0x7FC00000, by decide +kernel, Or.inl ⟨by decide +kernel, 0xFFC0002A, by decide +kernel, rfl⟩⟩,
    (EvalFloatBinOpRel_arith_iff .nondeterministic .sub .binary64 0x3FF0000000000000 0x7FF800000000002A
        ⟨0x7FF800000000002A, 8⟩ rfl).mpr
      ⟨0x7FF8000000000000, by decide +kernel,
        Or.inl ⟨by decide +kernel, 0x7FF800000000002A, by decide +kernel, rfl⟩⟩⟩

/-- **`W9` Witness (`Ptr2IntTransmutePolicy` scope: pointer destinations, arrays, pointer width)**:
1. `*const u8 -> *mut u16` keeps pointer provenance under BOTH policies (the policy only governs
   non-pointer destinations), and a `*const u8 -> u32` size mismatch fails closed `.unsupported`;
2. `*const u8 -> f64` flips exactly like `*const u8 -> usize` (`.ub` vs. the stripped address);
3. composite `[*const u8; 2] -> [usize; 2]` is `.ub` under `.strictUcg630Ub` and strips BOTH elements
   under `.stripProvenance`, while `[*const u8; 2] -> [*const u8; 2]` is preserved under both;
4. **Round-1 finding (`Trusted` pointer-width scope, outside this workstream's editable files)**:
   `tyByteSize` fixes `usize` and thin pointers at 8 bytes even for a `pointerBits := 32` table with
   4-byte layout entries, so on a 32-bit capture `*const u8 -> usize` is `.ub` under BOTH policies
   (no policy flip) and `*const u8 -> u32` is `.unsupported`: the byte-cast model — and therefore
   the `Ptr2IntTransmutePolicy` correspondence — is 64-bit only, matching MiniRust's `x86_64`. -/
theorem w9_ptr2int_pointer_width_scope_and_ptr_to_ptr_preservation :
    let p : ProvenancePtr := { allocId := 1, offsetBytes := 0x1000 }
    let arr : Value := .aggregate 0 [.ptr { allocId := 7, offsetBytes := 0x1000 } 8,
      .ptr { allocId := 9, offsetBytes := 0x2000 } 8]
    (∀ policy,
      evalByteCast [.init (.ptr p 8)] (.copy ⟨0, .nil⟩) tPtrMutU16Ty emptyMemory
          [⟨.not, tPtrU8Ty, .none⟩] emptyLayoutTable policy =
        .ok (.ptr p 8) [.init (.ptr p 8)] emptyMemory ∧
      evalByteCast [.init (.ptr p 8)] (.copy ⟨0, .nil⟩) tU32Ty emptyMemory
          [⟨.not, tPtrU8Ty, .none⟩] emptyLayoutTable policy = .unsupported ∧
      evalByteCast [.init arr] (.copy ⟨0, .nil⟩) tPtrArr2Ty emptyMemory
          [⟨.not, tPtrArr2Ty, .none⟩] tPtrArrayLayouts policy = .ok arr [.init arr] emptyMemory) ∧
    evalByteCast [.init (.ptr p 8)] (.copy ⟨0, .nil⟩) tF64LayoutTy emptyMemory
        [⟨.not, tPtrU8Ty, .none⟩] tFloat64Layouts .strictUcg630Ub = .ub ∧
    evalByteCast [.init (.ptr p 8)] (.copy ⟨0, .nil⟩) tF64LayoutTy emptyMemory
        [⟨.not, tPtrU8Ty, .none⟩] tFloat64Layouts .stripProvenance =
      .ok (.scalar ⟨0x1000, 8⟩) [.init (.ptr p 8)] emptyMemory ∧
    evalByteCast [.init arr] (.copy ⟨0, .nil⟩) tUsizeArr2Ty emptyMemory
        [⟨.not, tPtrArr2Ty, .none⟩] tPtrArrayLayouts .strictUcg630Ub = .ub ∧
    evalByteCast [.init arr] (.copy ⟨0, .nil⟩) tUsizeArr2Ty emptyMemory
        [⟨.not, tPtrArr2Ty, .none⟩] tPtrArrayLayouts .stripProvenance =
      .ok (.aggregate 0 [.scalar ⟨0x1000, 8⟩, .scalar ⟨0x2000, 8⟩]) [.init arr] emptyMemory ∧
    tyByteSize [] tPtr32Layouts tUsize32Ty = some 8 ∧
    tyByteSize [] tPtr32Layouts tPtr32Ty = some 8 ∧
    (∀ policy,
      evalByteCast [.init (.ptr p 4)] (.copy ⟨0, .nil⟩) tUsize32Ty emptyMemory
          [⟨.not, tPtr32Ty, .none⟩] tPtr32Layouts policy = .ub ∧
      evalByteCast [.init (.ptr p 4)] (.copy ⟨0, .nil⟩) tU32At1Ty emptyMemory
          [⟨.not, tPtr32Ty, .none⟩] tPtr32Layouts policy = .unsupported) := by
  dsimp only
  exact ⟨fun policy => by cases policy <;> exact ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl,
    fun policy => by cases policy <;> exact ⟨rfl, rfl⟩⟩

/-! ### §1.2 Round-1 Hardening: MiniRust Projected-Float-Operand Gates & `binary64` `MachTB` Carriers -/

section MiniRustRound1

open MiniRustSpec MiniRustSpec.LibSpecr MiniRustSpec.Interp MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness MiniRustSpec.Correspondence.PointerWitness
open MiniRustSpec.Correspondence.RefWitness MiniRustSpec.Correspondence.FloatCastMR

/-- `*const f32` local (admitted by `translateLocals`: raw pointers record only pointee metadata). -/
private def tPtrF32Decl : Trusted.Rustc.V2026_06_01.MirAst.LocalDecl :=
  { mutability := .mut, ty := { kind := .rawPtr .not (.float .f32), layoutIdx := 12 }, debugName := none }
/-- `&f64` local (rejected by `translateLocals`: no `PointeeInfo` for a float pointee). -/
private def tRefF64Decl : Trusted.Rustc.V2026_06_01.MirAst.LocalDecl :=
  { mutability := .mut, ty := { kind := .ref .not (.float .f64), layoutIdx := 12 }, debugName := none }
/-- `*const u32` local (integer-pointee differential control). -/
private def tPtrU32Decl : Trusted.Rustc.V2026_06_01.MirAst.LocalDecl :=
  { mutability := .mut, ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 12 }, debugName := none }

/-- `_0 = Lt(copy (*_1), copy (*_2))`. -/
private def tDerefCmpStmt : Trusted.Rustc.V2026_06_01.MirAst.Statement :=
  mkStmt (.assign (local_ 0) (.binaryOp .lt (.copy ⟨1, [.deref]⟩) (.copy ⟨2, [.deref]⟩)))
/-- `_0 = Neg(copy (*_1))`. -/
private def tDerefNegStmt : Trusted.Rustc.V2026_06_01.MirAst.Statement :=
  mkStmt (.assign (local_ 0) (.unaryOp .neg (.copy ⟨1, [.deref]⟩)))
/-- `_0 = Add(copy (*_1), copy (*_2))`. -/
private def tDerefAddStmt : Trusted.Rustc.V2026_06_01.MirAst.Statement :=
  mkStmt (.assign (local_ 0) (.binaryOp .add (.copy ⟨1, [.deref]⟩) (.copy ⟨2, [.deref]⟩)))

/-- `fn f(p: *const f32, q: *const f32) -> bool { *p < *q }`: ZERO float-typed locals and ZERO
float constants. -/
private def tDerefFloatCmpBody : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir :=
  faBody2 "w10::deref_f32_lt" [boolDecl, tPtrF32Decl, tPtrF32Decl]
    [.assign (local_ 0) (.binaryOp .lt (.copy ⟨1, [.deref]⟩) (.copy ⟨2, [.deref]⟩))]

/-- **`W10` Witness (round-1 gap: projected float operands)**:
`fa_no_fragment_admits_float_arith_or_cmp` covers float-typed locals and float constants only. A
body whose float operands are reached exclusively through a pointer dereference (`*p < *q`,
`-(*p)`, `*p + *q` with `p, q : *const f32`) declares NO float local and NO float constant, and
`translateLocals` ADMITS its `*const f32` locals — yet every statement-level MiniRust gate
(`translateStatement`, `statementOk`, `statementOkWithIntrinsics`) and the function-level gates
(`translateFn`, `inFragment`) still reject it, because `derefPointeeTy` has no MiniRust type for a
float pointee. Differential control: the SAME comparison statement over `*const u32` pointees
translates. References to floats (`&f64`) are rejected one level earlier, by `translateLocals`. -/
theorem w10_mr_projected_float_operand_gates :
    (translateLocals fcLayouts 0 [boolDecl, tPtrF32Decl, tPtrF32Decl]).isSome = true ∧
    (translateLocals fcLayouts 0 [boolDecl, tRefF64Decl, tRefF64Decl]).isNone = true ∧
    (translateStatement [boolDecl, tPtrF32Decl, tPtrF32Decl] tDerefCmpStmt fcLayouts).isNone = true ∧
    (translateStatement [boolDecl, tPtrF32Decl, tPtrF32Decl] tDerefNegStmt fcLayouts).isNone = true ∧
    (translateStatement [boolDecl, tPtrF32Decl, tPtrF32Decl] tDerefAddStmt fcLayouts).isNone = true ∧
    statementOk [boolDecl, tPtrF32Decl, tPtrF32Decl] tDerefCmpStmt fcLayouts = false ∧
    statementOkWithIntrinsics [boolDecl, tPtrF32Decl, tPtrF32Decl] tDerefCmpStmt fcLayouts = false ∧
    (translateStatement [boolDecl, tPtrU32Decl, tPtrU32Decl] tDerefCmpStmt fcLayouts).isSome = true ∧
    (translateFn tDerefFloatCmpBody).isNone = true ∧
    inFragment tDerefFloatCmpBody = false := by
  decide +kernel

/-- **`W11` Witness (`binary64` `EvalFloatBinOpRel` outcomes on `MachTB`)**: every member of the
6-element nondeterministic `nanChoices` set of `sNaN(0x7FF4000000000001) + 1.0` is an
`EvalFloatBinOpRel .nondeterministic .add .binary64` outcome, and each such outcome — as well as the
finite `1.0 + 2.0 = 3.0` image — round-trips bit-for-bit through MiniRust's 64-bit carrier on
`TreeBorrowsMemory` (`Interp.stepsTB`), complementing the `BasicMemory` (`Interp.steps`) statement
`fa_bridge_evalFloatBinOpRel_mach_steps`. -/
theorem w11_mr_f64_nan_candidates_machTB_carrier :
    (∀ cand ∈ [0x7FF8000000000000, 0xFFF8000000000000, 0x7FFC000000000001, 0xFFFC000000000001,
        0x7FF4000000000001, 0xFFF4000000000001],
      EvalFloatBinOpRel .nondeterministic .add .binary64 0x7FF4000000000001 0x3FF0000000000000
        ⟨cand, 8⟩) ∧
    fcRetAfterTB8 fcCarrier64Body [.scalar ⟨0x7FF8000000000000, 8⟩] 3 = tbRetU64 0x7FF8000000000000 ∧
    fcRetAfterTB8 fcCarrier64Body [.scalar ⟨0xFFF8000000000000, 8⟩] 3 = tbRetU64 0xFFF8000000000000 ∧
    fcRetAfterTB8 fcCarrier64Body [.scalar ⟨0x7FFC000000000001, 8⟩] 3 = tbRetU64 0x7FFC000000000001 ∧
    fcRetAfterTB8 fcCarrier64Body [.scalar ⟨0xFFFC000000000001, 8⟩] 3 = tbRetU64 0xFFFC000000000001 ∧
    fcRetAfterTB8 fcCarrier64Body [.scalar ⟨0x7FF4000000000001, 8⟩] 3 = tbRetU64 0x7FF4000000000001 ∧
    fcRetAfterTB8 fcCarrier64Body [.scalar ⟨0xFFF4000000000001, 8⟩] 3 = tbRetU64 0xFFF4000000000001 ∧
    fcRetAfterTB8 fcCarrier64Body [.scalar ⟨0x4008000000000000, 8⟩] 3 = tbRetU64 0x4008000000000000 := by
  have hlist : nanChoices .binary64 [(.binary64, 0x7FF4000000000001), (.binary64, 0x3FF0000000000000)]
      .nondeterministic = [0x7FF8000000000000, 0xFFF8000000000000, 0x7FFC000000000001,
        0xFFFC000000000001, 0x7FF4000000000001, 0xFFF4000000000001] := by decide +kernel
  exact ⟨fun cand hc =>
      (EvalFloatBinOpRel_arith_iff .nondeterministic .add .binary64 0x7FF4000000000001
        0x3FF0000000000000 ⟨cand, 8⟩ rfl).mpr
        ⟨0x7FF8000000000000, by decide +kernel,
          Or.inl ⟨by decide +kernel, cand, by rw [hlist]; exact hc, rfl⟩⟩,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

private theorem tb_wfLive_of_stepsTB_isOk (m : Mach) (n : Nat)
    (h : (Interp.stepsTB n (liftMachToTB m)).isOk = true) :
    ∃ m0 m', some (liftMachToTB m) = some m0 ∧
      Interp.stepsTB n m0 = .ok m' ∧ MachTB.wfLive m' := by
  cases hs : Interp.stepsTB n (liftMachToTB m) with
  | error e => simp [hs, Except.isOk, Except.toBool] at h
  | ok m' => exact ⟨liftMachToTB m, m', rfl, hs, TbWitness.liftMachToTB_stepsTB_wfLive hs⟩

/-- **`W11` companion (`MachTB.wfLive`)**: the 64-bit carrier run of the sign-flipped quieted `f64`
sNaN candidate `0xFFFC000000000001` preserves `MachTB.wfLive` (isolated from `W11` so that a
`TreeBorrowsMemory` well-formedness regression is reported separately). -/
theorem w11_mr_f64_nan_candidate_machTB_wfLive :
    ∃ m0 m', fcStartMachineTB8 fcCarrier64Body [.scalar ⟨0xFFFC000000000001, 8⟩] = some m0 ∧
      Interp.stepsTB 3 m0 = .ok m' ∧ MachTB.wfLive m' := by
  simp only [fcStartMachineTB8, fcStartMachine8, fc_translateFn_carrier64, Option.map]
  exact tb_wfLive_of_stepsTB_isOk
    (machineWithCtx fcCtx8 fcCarrier64Body fcCarrier64Fn
      (initMachineState fcCarrier64Body [.scalar ⟨0xFFFC000000000001, 8⟩]).frame.locals
      fcCarrier64Fn.start)
    3 (by decide +kernel)

end MiniRustRound1

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
  let act : CoreM (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Array Name) := do
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
        lmNs ++ `miri_transmute_uninit_ub,
        -- Round-1 repairs: valid default binary NaN selector, index-exact nondeterministic
        -- correspondence, pinned `miriTransmuteScalarCheck` policy arms, and `W7`.
        lmNs ++ `annealChooseBinaryNaN_valid,
        lmNs ++ `annealChooseQuietedNaN_not_validBinary,
        lmNs ++ `floatOps_binary_arith_pure_index_exact,
        lmNs ++ `step_float_arith_copy_copy_nondet_index_exact,
        lmNs ++ `miriTransmuteScalarCheck_ptr_policy_arms,
        lmNs ++ `w7_lm_f64_and_sub_index_exact ]
    let generalMrThms : List Name :=
      [ mrNs ++ `fa_no_fragment_admits_float_arith_or_cmp,
        mrNs ++ `fa_sym_mr_negXor_f32_lockstep,
        mrNs ++ `fa_sym_mr_negXor_f64_lockstep,
        mrNs ++ `fa_bridge_evalFloatBinOpRel_mach_steps,
        mrNs ++ `fa_ptr2int_live_mach_and_machTB_wfLive,
        mrNs ++ `fa_composite_tuple_struct_policy_correspondence,
        mrNs ++ `fa_no_forge_ref_and_uninit_live_mach_and_machTB_wfLive ]
    -- `V2026_06_01` <-> `V2026_08_01` dialect parity (so BOTH trusted dialects are reachable).
    let dialectParityThms : List Name :=
      [ ieeeNs ++ `evalFloatNeg_parity,
        ieeeNs ++ `evalFloatCmp_parity,
        ieeeNs ++ `evalFloatBinOp_parity,
        ieeeNs ++ `EvalFloatBinOpRel_parity,
        ieeeNs ++ `nanChoices_parity,
        ieeeNs ++ `policyRejectsProv_parity ]

    let masterName := ns ++ `unifiedFloatArithAndUcg630DualBundle
    let (masterTy, masterPf) ←
      conjoinAll (dualNames ++ generalLmThms ++ generalMrThms ++ dialectParityThms)
    addThm masterName masterTy masterPf
    added := added.push masterName

    -- 2. Paired positive / negative kernel controls on scratch copies of the kernel environment.
    --    For every semantic left-hand side: (a) it is well-typed, (b) the kernel ACCEPTS the TRUE
    --    equation `lhs = trueRhs` by `Eq.refl` (so the kernel really evaluates `lhs`), and (c) the
    --    kernel REJECTS the forged equation `lhs = forgedRhs`. Without (b), a rejection could be an
    --    artifact of a stuck reduction or a mis-built term rather than a semantic refutation.
    let natTy := mkConst ``Nat
    let boolTy := mkConst ``Bool
    let boolTrue := mkConst ``Bool.true
    let boolFalse := mkConst ``Bool.false
    let optBoolTy := mkApp (mkConst ``Option [0]) boolTy
    let someTrue := mkApp2 (mkConst ``Option.some [0]) boolTy boolTrue
    let someFalse := mkApp2 (mkConst ``Option.some [0]) boolTy boolFalse
    let listNatTy := mkApp (mkConst ``List [0]) natTy
    let fmtTy := mkConst (tSem ++ `IeeeFormat)
    let fmtNatTy := mkApp2 (mkConst ``Prod [0, 0]) fmtTy natTy
    let natPairTy := mkApp2 (mkConst ``Prod [0, 0]) natTy natTy
    let abTy := mkConst (tSem ++ `AbstractByte)
    let f32 := mkConst (tSem ++ `IeeeFormat.binary32)
    let f64 := mkConst (tSem ++ `IeeeFormat.binary64)
    let nondet := mkConst (tSem ++ `FloatArithMode.nondeterministic)
    let mkNatList (xs : List Nat) : Expr :=
      xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natTy (mkNatLit x) acc)
        (mkApp (mkConst ``List.nil [0]) natTy)
    let mkNanInputs (xs : List (Expr × Nat)) : Expr :=
      xs.foldr (fun (f, b) acc =>
          mkApp3 (mkConst ``List.cons [0]) fmtNatTy
            (mkApp4 (mkConst ``Prod.mk [0, 0]) fmtTy natTy f (mkNatLit b)) acc)
        (mkApp (mkConst ``List.nil [0]) fmtNatTy)
    let mkCmp (f : Expr) (a b : Nat) : Expr :=
      mkApp4 (mkConst (tSem ++ `evalFloatCmp)) (mkConst (tAst ++ `BinOp.eq)) f (mkNatLit a) (mkNatLit b)
    let mkNeg (f : Expr) (a : Nat) : Expr := mkApp2 (mkConst (tSem ++ `evalFloatNeg)) f (mkNatLit a)
    let mkChoices (f : Expr) (xs : List (Expr × Nat)) : Expr :=
      mkApp3 (mkConst (tSem ++ `nanChoices)) f (mkNanInputs xs) nondet
    let provVal := mkApp2 (mkConst ``Option.some [0]) natPairTy
      (mkApp4 (mkConst ``Prod.mk [0, 0]) natTy natTy (mkNatLit 1) (mkNatLit 0))
    let provByte := mkApp2 (mkConst (tSem ++ `AbstractByte.init))
      (mkApp (mkConst ``UInt8.ofNat) (mkNatLit 0)) provVal
    let provBytes := mkApp3 (mkConst ``List.cons [0]) abTy provByte
      (mkApp (mkConst ``List.nil [0]) abTy)
    let mkPol (p : Name) : Expr :=
      mkApp2 (mkConst (tSem ++ `policyRejectsProv)) (mkConst (tSem ++ p)) provBytes
    -- (description, type, LHS, TRUE RHS, FORGED RHS)
    let controls : List (String × Expr × Expr × Expr × Expr) :=
      [ ("f32 qNaN == qNaN", optBoolTy, mkCmp f32 0x7FC00000 0x7FC00000, someFalse, someTrue),
        ("f64 -0.0 == +0.0", optBoolTy, mkCmp f64 0x8000000000000000 0, someTrue, someFalse),
        ("f32 sNaN negation keeps the signaling payload", natTy, mkNeg f32 0x7FA00001,
          mkNatLit 0xFFA00001, mkNatLit 0xFFE00001),
        ("f64 sNaN negation keeps the signaling payload", natTy, mkNeg f64 0x7FF4000000000001,
          mkNatLit 0xFFF4000000000001, mkNatLit 0xFFFC000000000001),
        ("f32 nondet nanChoices 6-element sNaN set", listNatTy, mkChoices f32 [(f32, 0x7FA00001)],
          mkNatList [0x7FC00000, 0xFFC00000, 0x7FE00001, 0xFFE00001, 0x7FA00001, 0xFFA00001],
          mkNatList [0x7FC00000]),
        ("f64 nondet nanChoices 6-element sNaN set", listNatTy,
          mkChoices f64 [(f64, 0x7FF4000000000001), (f64, 0x3FF0000000000000)],
          mkNatList [0x7FF8000000000000, 0xFFF8000000000000, 0x7FFC000000000001, 0xFFFC000000000001,
            0x7FF4000000000001, 0xFFF4000000000001],
          mkNatList [0x7FF8000000000000, 0xFFF8000000000000, 0x7FFC000000000001, 0xFFFC000000000001]),
        ("`.sub` candidate order uses the UN-NEGATED rhs input", listNatTy,
          mkChoices f32 [(f32, 0x3F800000), (f32, 0x7FC0002A)],
          mkNatList [0x7FC00000, 0xFFC00000, 0x7FC0002A, 0xFFC0002A],
          mkNatList [0x7FC00000, 0xFFC00000, 0xFFC0002A, 0x7FC0002A]),
        ("strictUcg630Ub rejects a provenance byte", boolTy,
          mkPol `Ptr2IntTransmutePolicy.strictUcg630Ub, boolTrue, boolFalse),
        ("stripProvenance admits a provenance byte", boolTy,
          mkPol `Ptr2IntTransmutePolicy.stripProvenance, boolFalse, boolTrue) ]

    let saved ← getEnv
    let mkEqDecl (name : Name) (ty lhs rhs : Expr) : Declaration := .thmDecl {
      name, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) ty lhs rhs,
      value := mkApp2 (mkConst ``Eq.refl [1]) ty rhs }
    let kernelAccepts (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure true catch _ => pure false
      setEnv saved
      return r
    if ← kernelAccepts (mkEqDecl (ns ++ `forged.zeroEqOne) natTy (mkNatLit 0) (mkNatLit 1)) then
      throwError "cross-root negative control FAILED: kernel accepted 0 = 1"
    let mut rejected : Nat := 1
    let mut accepted : Nat := 0
    for (what, ty, lhs, trueRhs, forgedRhs) in controls do
      let okTy ← MetaM.run' do
        check lhs
        isDefEq (← inferType lhs) ty
      unless okTy do
        throwError "cross-root: control LHS ({what}) is ill-typed"
      unless ← kernelAccepts (mkEqDecl (ns ++ `control.accepted) ty lhs trueRhs) do
        throwError "cross-root positive control FAILED: kernel rejected the TRUE equation for {what}"
      accepted := accepted + 1
      if ← kernelAccepts (mkEqDecl (ns ++ `forged.rejected) ty lhs forgedRhs) then
        throwError "cross-root negative control FAILED: kernel accepted the forged equation for {what}"
      rejected := rejected + 1

    -- 3. Exhaustive axiom, non-triviality, host-Float-absence, & import-isolation audits
    let env ← getEnv
    let isConstructiveAx (a : Name) : Bool :=
      a == ``propext || a == ``Quot.sound
    let isStdAx (a : Name) : Bool :=
      a == ``propext || a == ``Classical.choice || a == ``Quot.sound
    let isHostFloat (d : Name) : Bool :=
      d == ``Float || (`Float).isPrefixOf d || d == ``Float32 || (`Float32).isPrefixOf d
    -- Recursive over binders, `∧`, `∨`, and `↔`: a conjunction is trivial iff BOTH conjuncts are,
    -- so `True ∧ True`, `x = x ∧ y = y`, or `(x = x ∧ True) ∧ y = y` cannot evade detection.
    let rec isTrivialProp : Expr → Bool
      | .forallE _ _ body _ => isTrivialProp body
      | .letE _ _ _ body _ => isTrivialProp body
      | .mdata _ e => isTrivialProp e
      | e =>
        if e.isConstOf ``True then true
        else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
        else if e.isAppOfArity ``HEq 4 then e.appFn!.appFn!.appArg! == e.appArg!
        else if e.isAppOfArity ``Iff 2 then
          e.appFn!.appArg! == e.appArg! || (isTrivialProp e.appFn!.appArg! && isTrivialProp e.appArg!)
        else if e.isAppOfArity ``And 2 then isTrivialProp e.appFn!.appArg! && isTrivialProp e.appArg!
        else if e.isAppOfArity ``Or 2 then isTrivialProp e.appFn!.appArg! || isTrivialProp e.appArg!
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
    let mkAnd (a b : Expr) : Expr := mkApp2 (mkConst ``And) a b
    let mkOr (a b : Expr) : Expr := mkApp2 (mkConst ``Or) a b
    let bvarEq := mkApp3 (mkConst ``Eq [1]) natTy (mkBVar 0) (mkBVar 0)
    unless isTrivialProp (mkAnd (mkConst ``True) (mkConst ``True))
        && isTrivialProp (mkAnd trivEq (mkAnd trivEq (mkConst ``True)))
        && isTrivialProp (mkAnd (mkAnd trivEq trivEq) trivEq)
        && isTrivialProp (.forallE `n natTy (mkAnd bvarEq (mkConst ``True)) .default)
        && isTrivialProp (mkOr nonTrivEq trivEq)
        && isTrivialProp (.mdata {} (mkAnd trivEq trivEq))
        && isTrivialProp (mkApp2 (mkConst ``Iff) (mkAnd trivEq trivEq) (mkConst ``True))
        && !isTrivialProp (mkAnd trivEq nonTrivEq)
        && !isTrivialProp (mkAnd nonTrivEq (mkConst ``True))
        && !isTrivialProp (mkOr nonTrivEq nonTrivEq)
        && !isTrivialProp (.forallE `n natTy (mkAnd bvarEq nonTrivEq) .default) do
      throwError "cross-root self-test: recursive And/Or/Iff trivial-conjunction detector failed"

    -- Structural MiniRust no-float inspection: the pinned MiniRust `Type`, `Value`, `Constant`, and
    -- operator inductives have NO float constructor (and `Type` / `Value` have exactly the pinned
    -- constructor lists), while Anneal's `RigidTy` does model floats.
    let mrGen := `MiniRustSpec.Gen
    let ctorShortNames (ind : Name) : CoreM (List String) := do
      match env.find? ind with
      | some (.inductInfo v) =>
        return v.ctors.map fun c => match c with | .str _ s => s | _ => ""
      | _ => throwError "cross-root: {ind} is not an inductive type in the kernel environment"
    let hasFloatName (s : String) : Bool := (s.toLower.splitOn "float").length > 1
    let mrTypeName := Name.mkStr mrGen "Type"
    for ind in [mrTypeName, mrGen ++ `Value, mrGen ++ `Constant, mrGen ++ `BinOp, mrGen ++ `UnOp,
                mrGen ++ `IntBinOp, mrGen ++ `IntUnOp, mrGen ++ `CastOp, mrGen ++ `RelOp] do
      let indCtors ← ctorShortNames ind
      for c in indCtors do
        if hasFloatName c then
          throwError "cross-root MiniRust no-float audit FAILED: {ind} has float constructor {c}"
    let mrTypeCtors ← ctorShortNames mrTypeName
    unless mrTypeCtors ==
        ["Int", "Bool", "Ptr", "Tuple", "Array", "Slice", "Union", "Enum", "TraitObject"] do
      throwError "cross-root MiniRust no-float audit FAILED: unexpected Gen.Type constructors {mrTypeCtors}"
    let mrValueCtors ← ctorShortNames (mrGen ++ `Value)
    unless mrValueCtors == ["Int", "Bool", "Ptr", "Tuple", "Variant", "Union"] do
      throwError "cross-root MiniRust no-float audit FAILED: unexpected Gen.Value constructors {mrValueCtors}"
    unless hasFloatName "Float" && !hasFloatName "Int" do
      throwError "cross-root self-test: float-constructor name detector failed"
    unless env.contains `Trusted.Rustc.V2026_06_01.MirAst.RigidTy.float do
      throwError "cross-root: Anneal RigidTy.float constructor not found"

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

    -- Automated bundle coverage: EVERY public theorem declared directly in `FloatArithMR` /
    -- `FloatArithLM` must be referenced by that module's `axiomAudit_*` bundle(s), so a public
    -- theorem can never silently escape the `#guard_msgs` `#print axioms` guards.
    let usedBy (b : Name) : CoreM NameSet := do
      let some ci := env.find? b | throwError "cross-root: missing audit bundle {b}"
      return ci.getUsedConstantsAsSet
    let lmBundle ← usedBy (lmNs ++ `axiomAudit_floatArithLM)
    let mrBundleCF ← usedBy (mrNs ++ `axiomAudit_choiceFree)
    let mrBundleM ← usedBy (mrNs ++ `axiomAudit_machine)
    let mut lmPublic : Nat := 0
    let mut mrPublic : Nat := 0
    for (n, ci) in targetDecls do
      match ci with
      | .thmInfo _ =>
        if !isPrivateName n && !n.isInternalDetail then
          if n.getPrefix == lmNs then
            unless lmBundle.contains n do
              throwError "cross-root bundle-coverage audit FAILED: public theorem {n} is missing from axiomAudit_floatArithLM"
            lmPublic := lmPublic + 1
          else if n.getPrefix == mrNs then
            unless mrBundleCF.contains n || mrBundleM.contains n do
              throwError "cross-root bundle-coverage audit FAILED: public theorem {n} is missing from axiomAudit_choiceFree / axiomAudit_machine"
            mrPublic := mrPublic + 1
      | _ => pure ()

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
        `Miri.Interpreter.Cast.cast,
        -- Round-1 additions: second trusted dialect, MiniRust translation gates, vendored
        -- `Allocation.readScalar` / `adjustNaN` / CTFE provenance, and the repaired LM overlays.
        `Trusted.Rustc.V2026_08_01.MirSemantics.evalFloatNeg,
        `Trusted.Rustc.V2026_08_01.MirSemantics.evalFloatCmp,
        `Trusted.Rustc.V2026_08_01.MirSemantics.evalFloatBinOp,
        `Trusted.Rustc.V2026_08_01.MirSemantics.evalFloatArithBase,
        `Trusted.Rustc.V2026_08_01.MirSemantics.EvalFloatBinOpRel,
        `Trusted.Rustc.V2026_08_01.MirSemantics.nanChoices,
        `Trusted.Rustc.V2026_08_01.MirSemantics.policyRejectsProv,
        `MiniRustSpec.Correspondence.translateFn,
        `MiniRustSpec.Correspondence.progInFragment,
        `Miri.Memory.Allocation.readScalar,
        `Miri.Memory.CtfeProvenance.fromAllocId,
        `Miri.Interpreter.FloatOps.adjustNaN,
        `LeanMiriSpec.FloatArithLM.miriTransmuteScalarCheck,
        `LeanMiriSpec.FloatArithLM.annealChooseBinaryNaN ]
    for req in requiredReach do
      unless reach.contains req do
        throwError "cross-root reachability failure: unifiedFloatArithAndUcg630DualBundle does not reach {req}"

    return (added.size, rejected, accepted, ieeeThms, mrThms, lmThms, mrPublic, lmPublic,
      requiredReach.length, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<ep2-float-arith-cross-root>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let ((addedCount, rejectedCount, acceptedCount, ieeeThms, mrThms, lmThms, mrPublic, lmPublic,
      reachedCount, crAxioms), _) ←
    liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount == 7 && rejectedCount == 10 && acceptedCount == 9 && ieeeThms ≥ 300 &&
      mrThms ≥ 100 && lmThms ≥ 95 && mrPublic ≥ 62 && lmPublic ≥ 56 && reachedCount == 35 do
    throwError "cross-root: unexpected counts (added={addedCount}, rejected={rejectedCount}, accepted={acceptedCount}, ieee={ieeeThms}, mr={mrThms}, lm={lmThms}, mrPublic={mrPublic}, lmPublic={lmPublic}, reached={reachedCount})"
  logInfo m!"ep2 float-arith cross-root kernel bridge: added {addedCount} dual theorems, rejected {rejectedCount} forged controls (paired with {acceptedCount} accepted positive controls), audited {ieeeThms} constructive IeeeFloatArith + {mrThms} MR + {lmThms} LM theorems (0 host Float, 0 MiniRustSpec imports in LM, {mrPublic} MR + {lmPublic} LM public theorems all covered by axiomAudit bundles, MiniRust Gen.Type has no float constructor), reached all {reachedCount} Trusted(06+08)+MiniRust+Miri constants, axioms {crAxioms}"

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
