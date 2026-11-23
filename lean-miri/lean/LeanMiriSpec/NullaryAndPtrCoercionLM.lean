/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import LeanMiriSpec.DropBinderAndSubtypeLM

/-!
# Episode 2 Dual-Authority Correspondence (`LeanMiriSpec` Authority):
# NullaryOp, PointerCoercion, FnPtrToPtr & UnwrapUnsafeBinder

Conservative hook extension (`annealStepHooksNullaryPtr`, strictly extending
`annealStepHooksDropBinderSubtype`), concrete positive / UB / boundary /
mode-sensitivity witnesses stepped through unmodified vendored
`Miri.Interpreter.Step.step` (`runMiriSteps`), and the executable authority-typed
`npLmObserve` for 4 already-trusted MIR variants:

1. **`V1` (`Rvalue.nullaryOp`)** —
   * `.ubChecks` / `.contractChecks` are translated by unmodified
     `Translate.translateRvalue` to `.Use (.RuntimeChecks _) .No`. The overlay
     supplies the `runtimeChecks` / `boolLayout` operand leaves
     (`npRuntimeChecks`, `npBoolLayout`) and combines them exactly as vendored
     `OperandMachine.evalOperand`'s `.RuntimeChecks` arm does
     (`npEvalRuntimeChecksOperand`), so `UbChecks` evaluates to `true` and
     `ContractChecks` / `OverflowChecks` fail closed with `StepError.unsupported`;
   * `.sizeOf` / `.alignOf` / `.offsetOf` have no counterpart in the pinned rustc
     MIR: the base translation maps them to `untranslatableConstOperand`
     (`StepError.unsupported`, `lm_np_v1_base_translate_boundary`), and
     `lowerNullaryMirBody` mirrors rustc's const-evaluation by replacing every
     layout query that Trusted `evalNullaryOp` resolves with a `usize` constant
     (`lowerNullaryRvalue_resolved` / `lowerNullaryRvalue_unresolved`).
2. **`V2` (`CastKind.pointerCoercion`)** — the five non-`Unsize` coercions reuse
   the `C8` cast leaves unchanged (`np_rvalueHooks_cast_eq_unwind_on_c6_c8`);
   `Unsize` (array-to-slice raw pointers) is stepped through unmodified vendored
   `Miri.Interpreter.Cast.cast` -> `unsizeInto` -> `unsizeIntoPointer` with the
   `lockstepTails` / `typeInfo` / `validatePlace` leaves of
   `annealCastHooksNullaryPtr`.
3. **`V3` (`CastKind.fnPtrToPtr`)** — reuses the `C6` cast leaf unchanged, with
   concrete positive, dead / uninit / dangling / nonzero-offset / non-function
   allocation UB witnesses, and the `rust-intrinsic` ABI divergence.
4. **`V4` (`ProjectionElem.unwrapUnsafeBinder`)** — reuses the `C9` place and
   operand leaves; when `treeBorrows = true`, an assignment through an
   `UnwrapUnsafeBinder` place rooted in a memory-backed local is first applied as a
   Tree Borrows write to the local's byte range (`npTreeBorrowsWriteApply`, backed
   by `ep2ApplyTreeBorrowsWrite` and bridged to vendored
   `BorrowTree.performBorrowAccessRange` by
   `np_unwrap_write_tb_conflict_bridges_vendored`).

Scope of the universal results in this module: the overlay's conservativity
(`step_nullaryPtr_overlay_eq_ep2_of_free`), the leaf coincidence with the `C6` /
`C8` / `C9` overlay, the `RuntimeChecks` operand law, and the lowering laws are
proved for every input. Per-variant execution claims are concrete witnesses on
the 16 frozen fixtures (plus a few auxiliary bodies); the universal Trusted-vs-Miri
step simulations for `FnPtrToPtr`, the non-`Unsize` coercions and
`UnwrapUnsafeBinder` remain the `C6` / `C8` / `C9` theorems of
`LeanMiriSpec.UnwindSetDiscrAndFnPtrLM`, stated over the leaves this overlay
reuses.

Strict import isolation: this module NEVER imports `MiniRustSpec.*` (verified
by the trailing `#assert_nullary_ptr_coercion_lm_audit` command).
-/

namespace LeanMiriSpec.NullaryAndPtrCoercionLM

set_option Elab.async false
set_option linter.unusedSimpArgs false

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence
open LeanMiriSpec.UnwindSetDiscrAndFnPtrLM
open LeanMiriSpec.DropBinderAndSubtypeLM

/-! ## §0. Shared Layouts, Types & 16 `CapturedMir` Fixtures (Frozen Cross-Root Interface) -/

def npPaddedU8U32MirLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩,
    backendRepr := .scalarPair
      (.initialized (.int 8 false) ⟨0, 255⟩)
      (.initialized (.int 32 false) ⟨0, 0xffffffff⟩),
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1],
    variants := .single 0, isUninhabited := false }

def npZstClosureMirLayout : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

def npLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [binderU32MirLayout, binderU32MirLayout, nonZeroU8MirLayout,
                npPaddedU8U32MirLayout, npZstClosureMirLayout] }

@[reducible] def npTuple16MirTy : Ty :=
  { kind := .tuple [.uint .u64, .uint .u32, .uint .u32], layoutIdx := 0 }
@[reducible] def npPaddedMirTy : Ty :=
  { kind := .adt "np::PaddedU8U32" [], layoutIdx := 3 }
@[reducible] def npBinderU32MirTy : Ty :=
  { kind := .adt "np::BinderU32" [], layoutIdx := 1 }
@[reducible] def npBinderNzU8MirTy : Ty :=
  { kind := .adt "np::BinderNonZeroU8" [], layoutIdx := 2 }
@[reducible] def npFnDefMirTy : Ty :=
  { kind := .fnDef "np::fn_u32" [], layoutIdx := 0 }
@[reducible] def npZstClosMirTy : Ty :=
  { kind := .closure "np::clos_u32" [], layoutIdx := 4 }
@[reducible] def npSafeFnPtrMirTy : Ty :=
  { kind := .fnPtr [.uint .u32] (.uint .u32) .safe .rust, layoutIdx := 0 }
@[reducible] def npUnsafeFnPtrMirTy : Ty :=
  { kind := .fnPtr [.uint .u32] (.uint .u32) .unsafe_ .rust, layoutIdx := 0 }
@[reducible] def npArr3U32MirTy : Ty :=
  { kind := .array (.uint .u32) 3, layoutIdx := 0 }
@[reducible] def npRawConstArr3U32MirTy : Ty :=
  { kind := .rawPtr .not (.array (.uint .u32) 3), layoutIdx := 0 }
@[reducible] def npRawMutU8MirTy : Ty :=
  { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }

-- V1: Rvalue.nullaryOp fixtures
def v1NullaryTupleMir : CapturedMir :=
  mkMirBody "np::v1_nullary_tuple"
    [mkDecl usizeMirTy, mkDecl usizeMirTy, mkDecl usizeMirTy, mkDecl usizeMirTy, mkDecl usizeMirTy] 0
    [mkBb [mkSt (.assign (locPlace 1) (.nullaryOp .sizeOf npTuple16MirTy)),
           mkSt (.assign (locPlace 2) (.nullaryOp .alignOf npTuple16MirTy)),
           mkSt (.assign (locPlace 3) (.nullaryOp (.offsetOf [(0, 2)]) npTuple16MirTy)),
           mkSt (.assign (locPlace 4) (.binaryOp .add (.copy (locPlace 1)) (.copy (locPlace 2)))),
           mkSt (.assign (locPlace 0) (.binaryOp .add (.copy (locPlace 4)) (.copy (locPlace 3))))]
      .return_]

def v1NullaryUbChecksMir : CapturedMir :=
  mkMirBody "np::v1_nullary_ub_checks"
    [mkDecl boolMirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.nullaryOp .ubChecks boolMirTy))] .return_]

def v1NullaryUbBranchMir : CapturedMir :=
  mkMirBody "np::v1_nullary_ub_branch"
    [mkDecl u32MirTy, mkDecl boolMirTy] 0
    [mkBb [mkSt (.assign (locPlace 1) (.nullaryOp .ubChecks boolMirTy))]
       (.switchInt (.copy (locPlace 1)) { branches := [(1, 1)], otherwise := 2 }),
     mkBb [] .unreachable,
     mkBb [mkSt (.assign (locPlace 0) (.use (constU32 0)))] .return_]

def v1NullaryPaddedOffsetMir : CapturedMir :=
  mkMirBody "np::v1_nullary_padded_offset"
    [mkDecl usizeMirTy, mkDecl npPaddedMirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.nullaryOp (.offsetOf [(0, 1)]) npPaddedMirTy))] .return_]
    npLayouts

-- V2: CastKind.pointerCoercion fixtures
def v2CalleeU32Mir : CapturedMir :=
  mkMirBody "np::fn_u32" [mkDecl u32MirTy, mkDecl u32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1))))] .return_]

def v2PtrCoerceFnPipelineMir : CapturedMir :=
  mkMirBody "np::v2_ptr_coerce_fn_pipeline"
    [mkDecl npUnsafeFnPtrMirTy, mkDecl npSafeFnPtrMirTy] 0
    [mkBb [mkSt (.assign (locPlace 1)
             (.cast (.pointerCoercion "ReifyFnPointer")
               (.constant { ty := npFnDefMirTy, val := .zeroSized }) npSafeFnPtrMirTy)),
           mkSt (.assign (locPlace 0)
             (.cast (.pointerCoercion "UnsafeFnPointer") (.copy (locPlace 1)) npUnsafeFnPtrMirTy))]
      .return_]

def v2PtrCoerceUnsizeSliceMir : CapturedMir :=
  mkMirBody "np::v2_ptr_coerce_unsize_slice"
    [mkDecl usizeMirTy, mkDecl npRawConstArr3U32MirTy, mkDecl rawConstSliceU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 2)
             (.cast (.pointerCoercion "Unsize") (.copy (locPlace 1)) rawConstSliceU32MirTy)),
           mkSt (.assign (locPlace 0) (.unaryOp .ptrMetadata (.copy (locPlace 2))))]
      .return_]

def v2PtrCoerceDeadUbMir : CapturedMir :=
  mkMirBody "np::v2_ptr_coerce_dead_ub"
    [mkDecl rawConstU32MirTy, mkDecl rawMutU32MirTy] 1
    [mkBb [mkSt (.storageDead 1),
           mkSt (.assign (locPlace 0)
             (.cast (.pointerCoercion "MutToConstPointer") (.copy (locPlace 1)) rawConstU32MirTy))]
      .return_]

def v2PtrCoerceArrayToPtrMir : CapturedMir :=
  mkMirBody "np::v2_ptr_coerce_array_to_ptr"
    [mkDecl rawConstU32MirTy, mkDecl npRawConstArr3U32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0)
             (.cast (.pointerCoercion "ArrayToPointer") (.copy (locPlace 1)) rawConstU32MirTy))]
      .return_]

-- V3: CastKind.fnPtrToPtr fixtures
def v3FnPtrToPtrConstMir : CapturedMir :=
  mkMirBody "np::v3_fn_ptr_to_ptr_const"
    [mkDecl rawConstUnitMirTy, mkDecl npSafeFnPtrMirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .fnPtrToPtr (.copy (locPlace 1)) rawConstUnitMirTy))]
      .return_]

def v3FnPtrToPtrMutChainMir : CapturedMir :=
  mkMirBody "np::v3_fn_ptr_to_ptr_mut_chain"
    [mkDecl rawConstU32MirTy, mkDecl npSafeFnPtrMirTy, mkDecl npRawMutU8MirTy] 1
    [mkBb [mkSt (.assign (locPlace 2) (.cast .fnPtrToPtr (.copy (locPlace 1)) npRawMutU8MirTy)),
           mkSt (.assign (locPlace 0) (.cast .ptrToPtr (.copy (locPlace 2)) rawConstU32MirTy))]
      .return_]

def v3FnPtrToPtrDeadUbMir : CapturedMir :=
  mkMirBody "np::v3_fn_ptr_to_ptr_dead_ub"
    [mkDecl rawConstUnitMirTy, mkDecl npSafeFnPtrMirTy] 1
    [mkBb [mkSt (.storageDead 1),
           mkSt (.assign (locPlace 0) (.cast .fnPtrToPtr (.copy (locPlace 1)) rawConstUnitMirTy))]
      .return_]

-- V4: ProjectionElem.unwrapUnsafeBinder fixtures
def v4UnwrapBinderRoundtripMir : CapturedMir :=
  mkMirBody "np::v4_unwrap_binder_roundtrip"
    [mkDecl u32MirTy, mkDecl u32MirTy, mkDecl npBinderU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 2) (.wrapUnsafeBinder (.copy (locPlace 1)) npBinderU32MirTy)),
           mkSt (.assign (locPlace 2 [.unwrapUnsafeBinder u32MirTy]) (.use (constU32 73))),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 2 [.unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npLayouts

def v4UnwrapBinderNzU8Mir : CapturedMir :=
  mkMirBody "np::v4_unwrap_binder_nzu8"
    [mkDecl u8MirTy, mkDecl u8MirTy, mkDecl npBinderNzU8MirTy] 1
    [mkBb [mkSt (.assign (locPlace 2) (.wrapUnsafeBinder (.copy (locPlace 1)) npBinderNzU8MirTy)),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 2 [.unwrapUnsafeBinder u8MirTy]))))]
      .return_]
    npLayouts

def v4UnwrapBinderDeadUbMir : CapturedMir :=
  mkMirBody "np::v4_unwrap_binder_dead_ub"
    [mkDecl u32MirTy, mkDecl npBinderU32MirTy] 1
    [mkBb [mkSt (.storageDead 1),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npLayouts

def v4UnwrapBinderProtectedMir : CapturedMir :=
  mkMirBody "np::v4_unwrap_binder_protected"
    [mkDecl u32MirTy, mkDecl npBinderU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 1 [.unwrapUnsafeBinder u32MirTy]) (.use (constU32 42))),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npLayouts

/-! ## §1. Conservative Hook Overlay (`annealStepHooksNullaryPtr`) -/

/-- `runtimeChecks` operand leaf (the `ExecutionLeaves.Operand.runtimeChecks` /
`OperandMachine.Hooks.runtimeChecks` slot): Anneal evaluates with UB checks
enabled, so `UbChecks` is `true` (matching Trusted `evalNullaryOp .ubChecks`);
the contract-check and overflow-check session flags are not modeled and fail
closed with `StepError.unsupported`. -/
def npRuntimeChecks (_c : Unit) (checks : Miri.MIR.RuntimeChecks) :
    Miri.Interpreter.RvalueM AnnealStepState Bool :=
  match checks with
  | .UbChecks => pure true
  | .ContractChecks => throw (.unsupported "ContractChecks runtime flag is not modeled")
  | .OverflowChecks => throw (.unsupported "OverflowChecks runtime flag is not modeled")

/-- `boolLayout` operand leaf (the `ExecutionLeaves.Operand.boolLayout` slot). -/
def npBoolLayout (layouts : LayoutTable) (_c : Unit) :
    Miri.Interpreter.RvalueM AnnealStepState Miri.Interpreter.LocalLayout :=
  pure (translateTyOverlay boolMirTy layouts)

/-- `Operand.RuntimeChecks` evaluation, combining the `runtimeChecks` and
`boolLayout` leaves exactly as vendored `OperandMachine.evalOperand`'s
`.RuntimeChecks` arm does (`value ← runtimeChecks; layout ← boolLayout;
⟨.immediate (.scalar (.fromBool value)), layout⟩`). -/
def npEvalRuntimeChecksOperand (layouts : LayoutTable) (c : Unit)
    (checks : Miri.MIR.RuntimeChecks) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  let value ← npRuntimeChecks c checks
  let layout ← npBoolLayout layouts c
  return ⟨.immediate (.scalar (Miri.Memory.Scalar.fromBool value)), layout⟩

/-- **Universal `RuntimeChecks` operand law**: for EVERY layout table and state,
`UbChecks` evaluates to the `bool` immediate `true` without touching the state,
and `ContractChecks` / `OverflowChecks` fail closed with `StepError.unsupported`. -/
theorem np_runtimeChecks_operand_universal (layouts : LayoutTable) (st : AnnealStepState) :
    npEvalRuntimeChecksOperand layouts () .UbChecks st =
      .ok ⟨.immediate (.scalar (Miri.Memory.Scalar.fromBool true)),
           translateTyOverlay boolMirTy layouts⟩ st ∧
    npEvalRuntimeChecksOperand layouts () .ContractChecks st =
      .error (.unsupported "ContractChecks runtime flag is not modeled") st ∧
    npEvalRuntimeChecksOperand layouts () .OverflowChecks st =
      .error (.unsupported "OverflowChecks runtime flag is not modeled") st :=
  ⟨rfl, rfl, rfl⟩

/-- Synthetic `Miri.MIR.TyId` naming the array pointee tail of the source of an
active array-to-slice `Unsize` coercion. `encodeTyId` collapses every
`*const/*mut [T; N]` to `TyId 40`, which cannot carry `N`; the id is produced only
by `annealCastHooksNullaryPtr.lockstepTails` and consumed only by its `typeInfo`
inside vendored `Cast.unsizeIntoPointer`. -/
def npUnsizeArrayTailTyId : Miri.MIR.TyId := 3500

/-- Mirror of the **type-level** component of Trusted `MirSemantics.unsizeArrayLen?`
(called with its default `borrows := []`, `tag := 0`), and equivalently the
64-bit-bounded slice of Trusted `MirSemantics.unsizeArrayToSliceSpec?` (which
Trusted `evalUnsizeCoercion` dispatches through): extracts `(elemTy, len)`
exactly when `ck = "Unsize"` and `(opTy, targetKind)` is a valid Rust
array-to-slice unsizing (`&[T; n] -> &[T]`, `&mut [T; n] -> &mut [T]`,
`&mut [T; n] -> &[T]`, `&[T; n] -> *const [T]`, `&mut [T; n] -> *mut/*const [T]`,
`*const [T; n] -> *const [T]`, `*mut [T; n] -> *mut/*const [T]`) with compatible
mutability (`unsizeMutabilityCompatible`), identical element type (`rigidTyEq`),
and 64-bit `usize` length (`n < scalarModulus 8`). Rejects mutability upgrades
(`*const -> *mut`, `& -> &mut`, `& -> *mut`), raw-to-ref upgrades
(`*const/*mut -> &/&mut`), element mismatches (`[u32; 3] -> [u8]`), and
`n ≥ 2^64` length overflow (preventing silent `UInt64.ofNat` truncation).

When `treeBorrows = true`, `annealCastHooksNullaryPtr` additionally enforces the
live Tree Borrows tag-permission check (`npCheckUnsizeTreeBorrowsPerm` /
`npUnsizeTreeBorrowsPermCheck`), rejecting `.Disabled` tags for every slice
target and `.Frozen` tags for mutable slice targets (`&mut [T]` / `*mut [T]`),
and accepting a tag that is not registered in the borrow tree, matching Trusted
`unsizeBorrowPermCompatible` and
`evalUnsizeCoercion`'s inline `borrowValid` check
(`npUnsizeTreeBorrowsPermCheck_eq_trusted_universal`,
`lm_np_v2_unsize_tb_perm_agreement_and_mode_sensitivity_witness`). -/
def npUnsizeArraySpec? (ck : String) (opTy : Option Ty) (targetKind : RigidTy) :
    Option (RigidTy × Nat) :=
  match unsizeArrayLen? ck opTy targetKind with
  | some n =>
    match targetKind with
    | .ref _ (.slice dstElem) | .rawPtr _ (.slice dstElem) => some (dstElem, n)
    | _ => none
  | none => none

/-- **Agreement between `npUnsizeArraySpec?` and Trusted
`MirSemantics.unsizeArrayLen?` at the empty borrow table** (`borrows := []`,
`tag := 0`) across EVERY coercion tag, operand type, and target type. -/
theorem npUnsizeArraySpec?_snd_eq_unsizeArrayLen? (ck : String) (opTy : Option Ty)
    (targetKind : RigidTy) :
    (npUnsizeArraySpec? ck opTy targetKind).map Prod.snd =
      unsizeArrayLen? ck opTy targetKind := by
  unfold npUnsizeArraySpec?
  cases hU : unsizeArrayLen? ck opTy targetKind with
  | none => rfl
  | some n =>
    cases targetKind with
    | ref _ pt =>
      cases pt with
      | slice _ => rfl
      | _ => unfold unsizeArrayLen? at hU; split at hU <;> simp at hU
    | rawPtr _ pt =>
      cases pt with
      | slice _ => rfl
      | _ => unfold unsizeArrayLen? at hU; split at hU <;> simp at hU
    | _ => unfold unsizeArrayLen? at hU; split at hU <;> simp at hU

/-- **Exact Universal Alignment Between `npUnsizeArraySpec?` and Trusted
`MirSemantics.unsizeArrayToSliceSpec?` (Dispatched by `evalUnsizeCoercion`)**:
for EVERY source type `srcTy` and target `targetKind`, `npUnsizeArraySpec?`
extracts the exact length of `unsizeArrayToSliceSpec? srcTy.kind targetKind`
restricted to 64-bit `usize` lengths (`n < scalarModulus 8`). For `n ≥ 2^64`,
`unsizeArrayToSliceSpec?` still returns `some n` (producing a non-canonical
`Scalar` in `evalUnsizeCoercion`), whereas `npUnsizeArraySpec?` /
`unsizeArrayLen?` reject the overflow cleanly to prevent `UInt64.ofNat`
truncation. -/
theorem npUnsizeArraySpec?_snd_eq_unsizeArrayToSliceSpec?_of_lt (srcTy : Ty)
    (targetKind : RigidTy) :
    (npUnsizeArraySpec? "Unsize" (some srcTy) targetKind).map Prod.snd =
      (unsizeArrayToSliceSpec? srcTy.kind targetKind).bind
        (fun n => if n < scalarModulus 8 then some n else none) := by
  rw [npUnsizeArraySpec?_snd_eq_unsizeArrayLen?]
  rcases srcTy with ⟨srcKind, li⟩
  have hStr : stringEq "Unsize" "Unsize" = true := by decide
  have hPerm : unsizeBorrowPermCompatible [] 0 targetKind = true := rfl
  unfold unsizeArrayLen? unsizeArrayToSliceSpec?
  simp only [hStr, hPerm, Bool.and_true]
  cases targetKind with
  | ref dstMut dstPt =>
    cases dstPt with
    | slice dstElem =>
      cases srcKind with
      | ref srcMut srcPt =>
        cases srcPt with
        | array srcElem n =>
          cases srcMut <;> cases dstMut <;>
            cases hEq : rigidTyEq srcElem dstElem <;>
            cases hBlt : Nat.blt n (scalarModulus 8)
          all_goals (try (have hLt : n < scalarModulus 8 := Nat.blt_eq.mp hBlt
                          simp [unsizeMutabilityCompatible, mutabilityEq, hEq, hBlt, hLt]))
          all_goals (try (have hNotLt : ¬ n < scalarModulus 8 := fun h => by
                            have hT := Nat.blt_eq.mpr h; rw [hT] at hBlt; cases hBlt
                          simp [unsizeMutabilityCompatible, mutabilityEq, hEq, hBlt, hNotLt]))
        | _ => cases srcMut <;> cases dstMut <;> rfl
      | rawPtr srcMut srcPt => cases srcMut <;> cases dstMut <;> cases srcPt <;> rfl
      | _ => rfl
    | _ =>
      cases srcKind with
      | ref srcMut srcPt => cases srcMut <;> cases dstMut <;> cases srcPt <;> rfl
      | rawPtr srcMut srcPt => cases srcMut <;> cases dstMut <;> cases srcPt <;> rfl
      | _ => rfl
  | rawPtr dstMut dstPt =>
    cases dstPt with
    | slice dstElem =>
      cases srcKind with
      | ref srcMut srcPt =>
        cases srcPt with
        | array srcElem n =>
          cases srcMut <;> cases dstMut <;>
            cases hEq : rigidTyEq srcElem dstElem <;>
            cases hBlt : Nat.blt n (scalarModulus 8)
          all_goals (try (have hLt : n < scalarModulus 8 := Nat.blt_eq.mp hBlt
                          simp [unsizeMutabilityCompatible, mutabilityEq, hEq, hBlt, hLt]))
          all_goals (try (have hNotLt : ¬ n < scalarModulus 8 := fun h => by
                            have hT := Nat.blt_eq.mpr h; rw [hT] at hBlt; cases hBlt
                          simp [unsizeMutabilityCompatible, mutabilityEq, hEq, hBlt, hNotLt]))
        | _ => cases srcMut <;> cases dstMut <;> rfl
      | rawPtr srcMut srcPt =>
        cases srcPt with
        | array srcElem n =>
          cases srcMut <;> cases dstMut <;>
            cases hEq : rigidTyEq srcElem dstElem <;>
            cases hBlt : Nat.blt n (scalarModulus 8)
          all_goals (try (have hLt : n < scalarModulus 8 := Nat.blt_eq.mp hBlt
                          simp [unsizeMutabilityCompatible, mutabilityEq, hEq, hBlt, hLt]))
          all_goals (try (have hNotLt : ¬ n < scalarModulus 8 := fun h => by
                            have hT := Nat.blt_eq.mpr h; rw [hT] at hBlt; cases hBlt
                          simp [unsizeMutabilityCompatible, mutabilityEq, hEq, hBlt, hNotLt]))
        | _ => cases srcMut <;> cases dstMut <;> rfl
      | _ => rfl
    | _ =>
      cases srcKind with
      | ref srcMut srcPt => cases srcMut <;> cases dstMut <;> cases srcPt <;> rfl
      | rawPtr srcMut srcPt => cases srcMut <;> cases dstMut <;> cases srcPt <;> rfl
      | _ => rfl
  | _ =>
    cases srcKind with
    | ref srcMut srcPt => cases srcMut <;> cases srcPt <;> rfl
    | rawPtr srcMut srcPt => cases srcMut <;> cases srcPt <;> rfl
    | _ => rfl

/-- **Universal `Unsize` Coercion Specification Laws**:
1. exact agreement with Trusted `unsizeArrayLen?`;
2. mutability upgrades (`*const -> *mut`, `& -> &mut`, `& -> *mut`) are ALWAYS
   rejected (`none`);
3. raw-to-reference upgrades (`*const/*mut -> &/&mut`) are ALWAYS rejected;
4. element type mismatches (`rigidTyEq srcElem dstElem = false`) are ALWAYS
   rejected;
5. 64-bit `usize` length overflows (`scalarModulus 8 ≤ n`) are ALWAYS rejected;
6. all 9 valid `(srcPtr, dstPtr)` combinations with `n < scalarModulus 8` and
   `rigidTyEq elem elem = true` succeed with `some (elem, n)`. -/
theorem np_v2_unsize_spec_laws :
    (∀ ck opTy targetKind,
      (npUnsizeArraySpec? ck opTy targetKind).map Prod.snd = unsizeArrayLen? ck opTy targetKind) ∧
    (∀ (elem : RigidTy) (n li : Nat),
      npUnsizeArraySpec? "Unsize" (some { kind := .rawPtr .not (.array elem n), layoutIdx := li })
        (.rawPtr .mut (.slice elem)) = none ∧
      npUnsizeArraySpec? "Unsize" (some { kind := .ref .not (.array elem n), layoutIdx := li })
        (.ref .mut (.slice elem)) = none ∧
      npUnsizeArraySpec? "Unsize" (some { kind := .ref .not (.array elem n), layoutIdx := li })
        (.rawPtr .mut (.slice elem)) = none) ∧
    (∀ (srcMut dstMut : Mutability) (elem : RigidTy) (n li : Nat),
      npUnsizeArraySpec? "Unsize" (some { kind := .rawPtr srcMut (.array elem n), layoutIdx := li })
        (.ref dstMut (.slice elem)) = none) ∧
    (∀ (srcMut dstMut : Mutability) (srcElem dstElem : RigidTy) (n li : Nat),
      rigidTyEq srcElem dstElem = false →
      npUnsizeArraySpec? "Unsize" (some { kind := .rawPtr srcMut (.array srcElem n), layoutIdx := li })
        (.rawPtr dstMut (.slice dstElem)) = none ∧
      npUnsizeArraySpec? "Unsize" (some { kind := .ref srcMut (.array srcElem n), layoutIdx := li })
        (.ref dstMut (.slice dstElem)) = none ∧
      npUnsizeArraySpec? "Unsize" (some { kind := .ref srcMut (.array srcElem n), layoutIdx := li })
        (.rawPtr dstMut (.slice dstElem)) = none) ∧
    (∀ (srcMut dstMut : Mutability) (elem : RigidTy) (n li : Nat),
      scalarModulus 8 ≤ n →
      npUnsizeArraySpec? "Unsize" (some { kind := .rawPtr srcMut (.array elem n), layoutIdx := li })
        (.rawPtr dstMut (.slice elem)) = none ∧
      npUnsizeArraySpec? "Unsize" (some { kind := .ref srcMut (.array elem n), layoutIdx := li })
        (.ref dstMut (.slice elem)) = none ∧
      npUnsizeArraySpec? "Unsize" (some { kind := .ref srcMut (.array elem n), layoutIdx := li })
        (.rawPtr dstMut (.slice elem)) = none) ∧
    (∀ (srcMut dstMut : Mutability) (elem : RigidTy) (n li : Nat),
      unsizeMutabilityCompatible srcMut dstMut = true →
      rigidTyEq elem elem = true →
      n < scalarModulus 8 →
      npUnsizeArraySpec? "Unsize" (some { kind := .rawPtr srcMut (.array elem n), layoutIdx := li })
        (.rawPtr dstMut (.slice elem)) = some (elem, n) ∧
      npUnsizeArraySpec? "Unsize" (some { kind := .ref srcMut (.array elem n), layoutIdx := li })
        (.ref dstMut (.slice elem)) = some (elem, n) ∧
      npUnsizeArraySpec? "Unsize" (some { kind := .ref srcMut (.array elem n), layoutIdx := li })
        (.rawPtr dstMut (.slice elem)) = some (elem, n)) := by
  have hStr : stringEq "Unsize" "Unsize" = true := by decide
  refine ⟨npUnsizeArraySpec?_snd_eq_unsizeArrayLen?, ?_, ?_, ?_, ?_, ?_⟩
  · intro elem n li
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [npUnsizeArraySpec?, unsizeArrayLen?, hStr, unsizeBorrowPermCompatible, lookupBorrow,
            unsizeMutabilityCompatible, mutabilityEq]
  · intro srcMut dstMut elem n li
    simp [npUnsizeArraySpec?, unsizeArrayLen?, hStr, unsizeBorrowPermCompatible, lookupBorrow]
  · intro srcMut dstMut srcElem dstElem n li hNe
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [npUnsizeArraySpec?, unsizeArrayLen?, hStr, unsizeBorrowPermCompatible, lookupBorrow, hNe]
  · intro srcMut dstMut elem n li hGe
    have hBlt : Nat.blt n (scalarModulus 8) = false := by
      cases h : Nat.blt n (scalarModulus 8) with
      | false => rfl
      | true => exact absurd (Nat.blt_eq.mp h) (Nat.not_lt.mpr hGe)
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [npUnsizeArraySpec?, unsizeArrayLen?, hStr, unsizeBorrowPermCompatible, lookupBorrow, hBlt]
  · intro srcMut dstMut elem n li hMut hEq hLt
    have hBlt : Nat.blt n (scalarModulus 8) = true := Nat.blt_eq.mpr hLt
    refine ⟨?_, ?_, ?_⟩ <;>
      (unfold npUnsizeArraySpec? unsizeArrayLen?
       simp [hStr, hBlt, hMut, hEq, unsizeBorrowPermCompatible, lookupBorrow])

/-- Diagnostic boolean for the cross-root kernel bridge negative control:
`true` iff `npUnsizeArraySpec?` erroneously accepts a mutability upgrade
(`*const [u32; 3] -> *mut [u32]`) or element mismatch
(`*const [u32; 3] -> *const [u8]`). Guaranteed `false`. -/
def npIllTypedUnsizeAccepted : Bool :=
  (npUnsizeArraySpec? "Unsize" (some npRawConstArr3U32MirTy) (.rawPtr .mut (.slice (.uint .u32)))).isSome ||
  (npUnsizeArraySpec? "Unsize" (some npRawConstArr3U32MirTy) (.rawPtr .not (.slice (.uint .u8)))).isSome

/-- Recover `(elem, len)` of the source array pointee when the statement at the
current PC of `currentBody` is a valid Rust array-to-slice `PointerCoercion(Unsize)`
(`npUnsizeArraySpec?` / Trusted `unsizeArrayLen?`), covering both raw pointers
and safe references while rejecting mutability upgrades, raw-to-ref upgrades,
element mismatches, and `n ≥ 2^64` length overflows. -/
def npActiveUnsizeArrayInfo? (currentBody : CapturedMir) (st : AnnealStepState) :
    Option (RigidTy × Nat) :=
  match st.stack.currentFrame? with
  | some frame =>
    match frame.location with
    | .mir loc =>
      match get? currentBody.basicBlocks loc.block with
      | some bb =>
        match get? bb.statements loc.statementIndex with
        | some { kind := .assign _ (.cast (.pointerCoercion ck) op targetTy), .. } =>
          npUnsizeArraySpec? ck (operandTy currentBody.localDecls currentBody.layouts op) targetTy.kind
        | _ => none
      | none => none
    | .unwinding _ => none
  | none => none

/-- Detect when the statement at the current PC is an array-to-slice
`PointerCoercion("Unsize")` that failed `npUnsizeArraySpec?` (ill-typed
mutability upgrade, raw-to-ref upgrade, element mismatch, or `n ≥ 2^64`), so
`lockstepTails` reports `StepError.invalidProgram` matching vendored
`Cast.unsizeInto`, distinct from non-array `Unsize` (`StepError.unsupported`). -/
def npIsIllTypedArrayToSliceUnsize (currentBody : CapturedMir) (st : AnnealStepState) : Bool :=
  match st.stack.currentFrame? with
  | some frame =>
    match frame.location with
    | .mir loc =>
      match get? currentBody.basicBlocks loc.block with
      | some bb =>
        match get? bb.statements loc.statementIndex with
        | some { kind := .assign _ (.cast (.pointerCoercion ck) op targetTy), .. } =>
          if stringEq ck "Unsize" then
            let opTy := operandTy currentBody.localDecls currentBody.layouts op
            let isArrToSlice : Bool :=
              match opTy, targetTy.kind with
              | some { kind := .rawPtr _ (.array _ _), .. }, .rawPtr _ (.slice _)
              | some { kind := .rawPtr _ (.array _ _), .. }, .ref _ (.slice _)
              | some { kind := .ref _ (.array _ _), .. }, .ref _ (.slice _)
              | some { kind := .ref _ (.array _ _), .. }, .rawPtr _ (.slice _) => true
              | _, _ => false
            isArrToSlice && (npUnsizeArraySpec? ck opTy targetTy.kind).isNone
          else false
        | _ => false
      | none => false
    | .unwinding _ => false
  | none => false

/-- Extract the target slice pointer mutability (`some true` for `&mut [T]` /
`*mut [T]`, `some false` for `&[T]` / `*const [T]`) of an active
`PointerCoercion(Unsize)` assignment at the current PC. -/
def npActiveUnsizeTargetMut? (currentBody : CapturedMir) (st : AnnealStepState) :
    Option Bool :=
  match st.stack.currentFrame? with
  | some frame =>
    match frame.location with
    | .mir loc =>
      match get? currentBody.basicBlocks loc.block with
      | some bb =>
        match get? bb.statements loc.statementIndex with
        | some { kind := .assign _ (.cast (.pointerCoercion _) _ targetTy), .. } =>
          match targetTy.kind with
          | .ref .mut (.slice _) | .rawPtr .mut (.slice _) => some true
          | .ref .not (.slice _) | .rawPtr .not (.slice _) => some false
          | _ => none
        | _ => none
      | none => none
    | .unwinding _ => none
  | none => none

/-- Check whether `tag` in `tree` has sufficient Tree Borrows permission for an
`Unsize` coercion of a pointer at byte offset `startNat` whose slice spans
`spanBytes` bytes (`isMutTarget = true` for `&mut [T]` / `*mut [T]`, `false` for
`&[T]` / `*const [T]`), mirroring Trusted `unsizeBorrowPermCompatible` /
`evalUnsizeCoercion.borrowValid`:
* a tag that is not registered in `tree` passes, exactly as Trusted accepts a
  pointer whose tag has no `BorrowEntry` (`lookupBorrow … = none`); a cast is not
  a memory access, so the vendored `.MissingTag` access error does not apply;
* `.Disabled` permission at any probed segment -> UB for every target;
* `.Frozen` permission at any probed segment when `isMutTarget = true` -> UB;
* `.Frozen` for const targets and `.Unique` / `.ReservedFrz _` / `.ReservedIM` /
  `.Cell` for all targets -> `.ok ()`.

The probed window is `[startNat, startNat + spanBytes)`. Trusted's check does
not depend on the slice length, so a zero-length coercion (`[T; 0]`, or a
zero-sized element type) still probes one byte: the byte at `startNat`, or, for
a pointer strictly one past the end of the tracked range (`startNat = trackedEnd`),
the last tracked byte (`trackedEnd - 1`). Strictly out-of-bounds offsets
(`startNat > trackedEnd`) are NOT clamped into `[0, trackedEnd)` (preserving the
honest Miri-vs-Trusted OOB raw-pointer boundary:
`np_vendored_borrowTree_zero_size_and_oob_boundary`). A tracked allocation of
size zero has `locations.entries = #[]` (and vendored `BorrowTree.new` stores
`defaultInitialPermission = .Disabled` even on the live root tag), so the check
passes there (`np_vendored_borrowTree_zero_size_and_oob_boundary`). -/
def npUnsizeTreeBorrowsPermCheck (tree : Miri.TreeBorrows.BorrowTree)
    (tag : Miri.Memory.BorTag) (startNat spanBytes : Nat) (isMutTarget : Bool) :
    Except Miri.Interpreter.StepError Unit :=
  match tree.tagMapping.get tag with
  | none => .ok ()
  | some tagIdx =>
    let trackedEnd : Nat :=
      tree.locations.entries.foldl
        (fun (acc : Nat)
            (seg : Miri.DataStructures.RangeMapSegment Miri.TreeBorrows.LocationTree) =>
          max acc seg.range.stop.toNat) 0
    let probeStart : Nat :=
      if spanBytes = 0 ∧ startNat = trackedEnd ∧ 0 < trackedEnd then trackedEnd - 1
      else startNat
    let endNat := probeStart + max 1 spanBytes
    let checkSeg (_ : Unit)
        (seg : Miri.DataStructures.RangeMapSegment Miri.TreeBorrows.LocationTree) :
        Except Miri.Interpreter.StepError Unit :=
      let s0 := seg.range.start.toNat
      let s1 := seg.range.stop.toNat
      if s0 < endNat && probeStart < s1 then
        let locSt? : Option Miri.TreeBorrows.Tree.LocationState :=
          match seg.data.perms.get tagIdx with
          | some ls => some ls
          | none => (tree.nodes.get tagIdx).map (·.defaultLocationState)
        match locSt? with
        | some ls =>
          match ls.permission, isMutTarget with
          | .Disabled, _ =>
            .error (.undefinedBehavior "Tree Borrows disabled tag on Unsize pointer coercion")
          | .Frozen, true =>
            .error (.undefinedBehavior "Tree Borrows frozen tag on mutable Unsize pointer coercion")
          | _, _ => .ok ()
        | none => .ok ()
      else .ok ()
    tree.locations.entries.foldlM checkSeg ()

/-- Live Tree Borrows tag-permission check executed on `PointerCoercion(Unsize)`
in `treeBorrows = true` mode before committing the unsized wide slice pointer to
the destination. Untracked allocations, machines without a borrow tracker, and
non-concrete provenances are left untouched. -/
def npCheckUnsizeTreeBorrowsPerm (currentBody : CapturedMir) (st : AnnealStepState)
    (val : Miri.Interpreter.Immediate AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState Unit :=
  match val, npActiveUnsizeArrayInfo? currentBody st, npActiveUnsizeTargetMut? currentBody st with
  | .scalarPair dataSc _, some (elem, n), some isMutTarget =>
    match dataSc.toPointer annealTargetDataLayout with
    | .ok ptr =>
      match ptr.provenance with
      | some (.concrete aid tag) =>
        match st.machine.borrowTracker,
              st.machine.memory.live.find? (fun e => e.1 == aid),
              ep2RelOffset? st.machine aid ptr.offset.bytes with
        | some _, some (_, liveAlloc), some rel =>
          match liveAlloc.allocation.extra with
          | some tree =>
            let elemSz :=
              (tyByteSize currentBody.localDecls currentBody.layouts
                { kind := elem, layoutIdx := 0 }).getD 1
            match npUnsizeTreeBorrowsPermCheck tree tag rel.toNat (n * elemSz) isMutTarget with
            | .ok () => pure ()
            | .error e => throw e
          | none => pure ()
        | _, _, _ => pure ()
      | _ => pure ()
    | .error _ => pure ()
  | _, _, _ => pure ()

/-- `CastHooks` overlay for `PointerCoercion(Unsize)` on array raw pointers and
safe references, extending `annealCastHooksUnwindFnPtrClosure` with the leaves
vendored `Cast.cast` -> `unsizeInto` -> `unsizeIntoPointer` invokes:
* `lockstepTails`: for a valid array-to-slice coercion (`npActiveUnsizeArrayInfo?`),
  the source tail is `npUnsizeArrayTailTyId` and the target tail is unchanged; an
  ill-typed array-to-slice coercion fails closed with `StepError.invalidProgram`,
  and every non-array unsizing (`dyn Trait`, struct tails) fails closed with
  `StepError.unsupported`;
* `typeInfo`: classifies `npUnsizeArrayTailTyId` as `.array elem len` (guarded by
  `n < 2^64` via `unsizeArrayLen?`);
* `writeImmediate`: when `treeBorrows = true`, enforces
  `npCheckUnsizeTreeBorrowsPerm` against the live allocation's `BorrowTree`
  before committing the wide slice pointer (matching Trusted
  `evalUnsizeCoercion.borrowValid` / `unsizeBorrowPermCompatible`);
* `validatePlace`: wide raw pointers (`*const/*mut [T]`) have no extra validity
  invariant (`pure ()`), while safe wide slice references (`&/&mut [T]`) run
  `annealValidateSafeWideSliceRef` (catching null, dangling, undersized,
  `SliceTooBig`, or misaligned safe slice references as UB). -/
def annealCastHooksNullaryPtr (currentBody : CapturedMir) (fnPtrs : List FnPtrEntry := .nil)
    (treeBorrows : Bool := false) :
    Miri.Interpreter.CastHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealCastHooksUnwindFnPtrClosure currentBody fnPtrs
  { base with
    typeInfo := fun c tyId => do
      let st ← get
      match npActiveUnsizeArrayInfo? currentBody st with
      | some (elem, n) =>
        if tyId == npUnsizeArrayTailTyId then
          pure (Miri.Interpreter.CastTypeInfo.array
            (encodeTyIdOverlay { kind := elem, layoutIdx := 0 }) (UInt64.ofNat n))
        else base.typeInfo c tyId
      | none => base.typeInfo c tyId
    lockstepTails := fun _ _ dstTail => do
      let st ← get
      match npActiveUnsizeArrayInfo? currentBody st with
      | some _ => pure (npUnsizeArrayTailTyId, dstTail)
      | none =>
        if npIsIllTypedArrayToSliceUnsize currentBody st then
          throw (.invalidProgram "ill-typed array-to-slice unsizing")
        else
          throw (.unsupported "Unsize outside the array-to-slice fragment")
    writeImmediate := fun c val dest => do
      if treeBorrows then
        let st ← get
        npCheckUnsizeTreeBorrowsPerm currentBody st val
      base.writeImmediate c val dest
    validatePlace := fun _ dest _ _ => do
      if isWideSafeRefTyId dest.layout.ty then
        let st ← get
        let some frame := st.stack.currentFrame? | throw (.stack .emptyStack)
        let op : Miri.Interpreter.Operand AnnealProv ←
          match dest.ref with
          | .local _ localId none _ =>
            match frame.getLocalOperand localId with
            | .ok opVal => pure opVal
            | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
            | .error e => throw (.stack e)
          | .memory mp => pure (.indirect mp)
          | .local _ _ (some _) _ =>
            throw (.unsupported "projected local safe wide slice ref validation")
        let imm ← annealReadImmediateOverlay ⟨op, dest.layout⟩
        annealValidateSafeWideSliceRef currentBody.layouts imm (nullFirst := false)
      else
        pure () }

/-- Whether `place` starts with a `.Deref` followed by at least one `.Field`
projection (covering `(*ptr).field.unwrapUnsafeBinder` and `(*ptr).field` on
dereferenced struct pointers). -/
def npIsDerefFieldPlace (place : Miri.MIR.Place) : Bool :=
  match place.projection.toList with
  | .Deref :: rest =>
    rest.any (fun e => match e with | .Field _ _ => true | _ => false)
  | _ => false

/-- Whether `place` contains any `.Field` projection (for sub-range Tree Borrows
write checks on both `_1.field` and `(*ptr).field`). -/
def npHasFieldProj (place : Miri.MIR.Place) : Bool :=
  place.projection.toList.any (fun e => match e with | .Field _ _ => true | _ => false)

/-- Whether an `Rvalue` reads a dereferenced struct-field place
(`(*ptr).field...`). -/
def npRvalueHasDerefField : Miri.MIR.Rvalue → Bool
  | .Use (.Copy p) _ | .Use (.Move p) _ => npIsDerefFieldPlace p
  | _ => false

private def npFindDeclTyForKind : List LocalDecl → RigidTy → Option Ty
  | [], _ => none
  | d :: ds, pt => if rigidTyEq d.ty.kind pt then some d.ty else npFindDeclTyForKind ds pt

/-- Resolve the pointee `LocalLayout` when dereferencing a raw pointer or safe
reference to a struct/ADT whose layout is declared in `localDecls` / `layouts`. -/
def npDerefStructPointeeLayout? (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId : Miri.MIR.LocalId) : Option Miri.Interpreter.LocalLayout :=
  match get? localDecls localId with
  | some decl =>
    match decl.ty.kind with
    | .rawPtr _ pt | .ref _ pt =>
      (npFindDeclTyForKind localDecls pt).map (fun ptTy => translateTyOverlay ptTy layouts)
    | _ => none
  | none => none

private def npDerefImmediateToMemPlace (imm : Miri.Interpreter.Immediate AnnealProv)
    (ptLay : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  let sc ← match imm.toScalar with
    | .ok s => pure s
    | .error e => throw (Miri.Interpreter.ScalarOps.immediateError e)
  let ptr ← match sc.toPointer annealTargetDataLayout with
    | .ok p => pure p
    | .error e => throw (Miri.Interpreter.ScalarOps.scalarError e)
  let mismatch ← match annealOffsetMisalignment ptr.offset ptLay.layout.align.abi with
    | .ok m => pure m
    | .error e => throw (.invalidProgram (toString e))
  return ⟨.indirect ⟨ptr, .none, mismatch⟩, ptLay⟩

/-- `PlaceProjectionHooks` extending `annealPlaceProjectionHooksOverlay` so
dereferencing a struct pointer (`(*ptr).field...`) resolves the pointee's
declared `LocalLayout` before running unmodified vendored
`Miri.Interpreter.PlaceDynamic.evalPlace`. -/
def npPlaceProjectionHooksNullaryPtr (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Miri.Interpreter.PlaceProjectionHooks AnnealProv AnnealStepState Unit Unit :=
  let baseHooks := annealPlaceProjectionHooksOverlay localDecls layouts
  { baseHooks with
    place := { baseHooks.place with
      deref := fun c base skipValidity =>
        match base.ref with
        | .local _ localId none _ =>
          match npDerefStructPointeeLayout? localDecls layouts localId with
          | some ptLay => do
            let st ← get
            let some frame := st.stack.currentFrame? | throw (.stack .emptyStack)
            let opVal ← match frame.getLocalOperand localId with
              | .ok v => pure v
              | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
              | .error e => throw (.stack e)
            let imm ← annealReadImmediate ⟨opVal, base.layout⟩
            let derefed ← npDerefImmediateToMemPlace imm.imm ptLay
            match derefed.op with
            | .indirect mp => return ⟨.memory mp, derefed.layout⟩
            | .immediate _ => throw (.invalidProgram "deref produced immediate")
          | none => baseHooks.place.deref c base skipValidity
        | _ => baseHooks.place.deref c base skipValidity } }

/-- Place evaluator extending `annealEvalPlaceOverlay` with struct-pointer
dereference + field projections (`(*ptr).field[.unwrapUnsafeBinder]`). -/
def npEvalPlaceNullaryPtr (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.MIR.Place) (skipValidity : Bool := false) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RuntimePlace AnnealProv) :=
  if npIsDerefFieldPlace place then
    Miri.Interpreter.PlaceDynamic.evalPlace
      (npPlaceProjectionHooksNullaryPtr localDecls layouts) () place skipValidity
  else
    annealEvalPlaceOverlay localDecls layouts place skipValidity

/-- Operand evaluator extending `annealEvalOperandOverlay` with reads through
`(*ptr).field[.unwrapUnsafeBinder]`. -/
def npEvalOperandNullaryPtr (localDecls : List LocalDecl) (layouts : LayoutTable)
    (op : Miri.MIR.Operand) (known : Option Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  match op with
  | .Copy place | .Move place =>
    if npIsDerefFieldPlace place then
      match place.projection.toList with
      | .Deref :: rest =>
        match npDerefStructPointeeLayout? localDecls layouts place.localId with
        | some ptLay =>
          let (frame', layout) ←
            annealResolveAndCacheLocalLayoutOverlay localDecls layouts place.localId known
          let operand ← match frame'.getLocalOperand place.localId with
            | .ok opVal => pure opVal
            | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
            | .error e => throw (.stack e)
          let imm ← annealReadImmediate ⟨operand, layout⟩
          let derefed ← npDerefImmediateToMemPlace imm.imm ptLay
          annealEvalUnwrapChainOp localDecls layouts place.localId frame' derefed rest
        | none => annealEvalOperandOverlay localDecls layouts op known
      | _ => annealEvalOperandOverlay localDecls layouts op known
    else annealEvalOperandOverlay localDecls layouts op known
  | _ => annealEvalOperandOverlay localDecls layouts op known

/-- State-transitioning Tree Borrows `.Read` through `tag` on
`[startNat, startNat + sizeBytes)` for an allocation whose vendored borrow tree
is `tree`:
* zero-sized reads (`sizeBytes = 0`) are a no-op before tag lookup (Miri's
  memory hooks only run for non-zero accesses);
* fails closed (`none`) when `tag` is unregistered in `tree` (matching vendored
  `BorrowTree.performBorrowAccessRange`'s `.MissingTag`) or when any overlapping
  segment/node transition via unmodified vendored
  `Miri.TreeBorrows.Tree.LocationState.performAccess` (`.Read`) does not return
  `.Success` (rejecting reads through `.Disabled` and foreign reads over a
  protected accessed `.Unique` tag);
* splits any partially-overlapping range segment so ONLY
  `[startNat, startNat + sizeBytes)` transitions (e.g., demoting an unprotected
  foreign `.Unique` child to `.Frozen` or marking a protected `ReservedFrz false`
  child conflicted `ReservedFrz true` ONLY on the read bytes, leaving sibling
  bytes untouched) and returns the updated `BorrowTree` for persistence via
  `Allocation.setExtra`. -/
def npApplyTreeBorrowsRead (protectedTags : Miri.TreeBorrows.ProtectedTags)
    (tree : Miri.TreeBorrows.BorrowTree) (tag : Miri.Memory.BorTag)
    (startNat sizeBytes : Nat) : Option Miri.TreeBorrows.BorrowTree :=
  if sizeBytes = 0 then some tree else
  match tree.tagMapping.get tag with
  | none => none
  | some srcIdx =>
    let endNat := startNat + sizeBytes
    let fuel := tree.nodes.data.size + 1
    let updateLocTree (lt : Miri.TreeBorrows.LocationTree) : Option Miri.TreeBorrows.LocationTree :=
      tree.tagMapping.mapping.foldlM (init := lt) fun acc (otherTag, otherIdx) =>
        let relPos : Miri.TreeBorrows.AccessRelatedness :=
          if ep2IsAncestor tree otherIdx srcIdx fuel then .LocalAccess else .ForeignAccess
        let isProt : Bool := protectedTags.get otherTag == some .StrongProtector
        let locSt? : Option Miri.TreeBorrows.Tree.LocationState :=
          match acc.perms.get otherIdx with
          | some ls => some ls
          | none => (tree.nodes.get otherIdx).map (·.defaultLocationState)
        match locSt? with
        | some ls =>
          match Miri.TreeBorrows.Tree.LocationState.performAccess ls .Read relPos isProt with
          | .Success nextLs _ => some { acc with perms := acc.perms.insert otherIdx nextLs }
          | _ => none
        | none => some acc
    let pushDedupSeg (out : Array (Miri.DataStructures.RangeMapSegment Miri.TreeBorrows.LocationTree))
        (seg : Miri.DataStructures.RangeMapSegment Miri.TreeBorrows.LocationTree) :
        Array (Miri.DataStructures.RangeMapSegment Miri.TreeBorrows.LocationTree) :=
      match out.back? with
      | some prev =>
        if prev.range.stop == seg.range.start && prev.data == seg.data then
          out.pop.push ⟨⟨prev.range.start, seg.range.stop⟩, prev.data⟩
        else out.push seg
      | none => out.push seg
    let stepSeg (out : Array (Miri.DataStructures.RangeMapSegment Miri.TreeBorrows.LocationTree))
        (seg : Miri.DataStructures.RangeMapSegment Miri.TreeBorrows.LocationTree) :
        Option (Array (Miri.DataStructures.RangeMapSegment Miri.TreeBorrows.LocationTree)) :=
      let s0 := seg.range.start.toNat
      let s1 := seg.range.stop.toNat
      if s0 < endNat && startNat < s1 then
        match updateLocTree seg.data with
        | none => none
        | some lt' =>
          if lt' = seg.data then some (pushDedupSeg out seg) else
          let oStart := max s0 startNat
          let oStop := min s1 endNat
          let out1 := if s0 < oStart then
              pushDedupSeg out ⟨⟨seg.range.start, UInt64.ofNat oStart⟩, seg.data⟩
            else out
          let out2 := pushDedupSeg out1 ⟨⟨UInt64.ofNat oStart, UInt64.ofNat oStop⟩, lt'⟩
          let out3 := if oStop < s1 then
              pushDedupSeg out2 ⟨⟨UInt64.ofNat oStop, seg.range.stop⟩, seg.data⟩
            else out2
          some out3
      else
        some (pushDedupSeg out seg)
    (tree.locations.entries.foldlM stepSeg #[]).map fun entries' =>
      { tree with locations := { entries := entries' } }

/-- Boolean permission predicate backed directly by `npApplyTreeBorrowsRead`. -/
def npTreeBorrowsReadPermitted (protectedTags : Miri.TreeBorrows.ProtectedTags)
    (tree : Miri.TreeBorrows.BorrowTree) (tag : Miri.Memory.BorTag)
    (startNat sizeBytes : Nat) : Bool :=
  (npApplyTreeBorrowsRead protectedTags tree tag startNat sizeBytes).isSome

/-- Apply a Tree Borrows `.Read` to the byte range `[absAddr - baseAddr, +size)`
of the live allocation referenced by `prov` via `npApplyTreeBorrowsRead`,
persisting the transitioned borrow tree with `Allocation.setExtra` and rejecting
conflicts or offset overflows as `StepError.undefinedBehavior`. Zero-sized reads
are a no-op decided before any allocation, offset, or tag lookup. -/
def npApplyTreeBorrowsReadAt (prov : Option AnnealProv) (absAddr : UInt64)
    (size : Miri.ABI.Size) (state : AnnealStepState) :
    Except Miri.Interpreter.StepError AnnealStepState :=
  if size.bytes.toNat = 0 then .ok state else
  match prov with
  | some (.concrete aid tag) =>
    match state.machine.memory.live.findIdx? (fun e => e.1 == aid),
          ep2RelOffset? state.machine aid absAddr with
    | some lIdx, some rel =>
      if rel.toNat + size.bytes.toNat ≥ 2 ^ 64 then
        .error (.undefinedBehavior "Tree Borrows read offset overflow on dereferenced field place")
      else
      match state.machine.memory.live[lIdx]? with
      | some (_, liveAlloc) =>
        match state.machine.borrowTracker, liveAlloc.allocation.extra with
        | some bt, some tree =>
          match npApplyTreeBorrowsRead bt.global.protectedTags tree tag rel.toNat
              size.bytes.toNat with
          | some tree' =>
            .ok { state with
                  machine := updateAllocMachine state.machine lIdx aid liveAlloc.kind
                    (liveAlloc.allocation.setExtra (some tree')) }
          | none =>
            .error (.undefinedBehavior "Tree Borrows read conflict on dereferenced field place")
        | _, _ => .ok state
      | none => .ok state
    | _, _ => .ok state
  | _ => .ok state

/-- **Zero-sized deref-field reads never reach the borrow tracker**: for EVERY
provenance (including an unregistered tag), address, and state,
`npApplyTreeBorrowsReadAt` with `size = 0` returns the state unchanged. -/
theorem npApplyTreeBorrowsReadAt_zst_noop (prov : Option AnnealProv) (absAddr : UInt64)
    (size : Miri.ABI.Size) (state : AnnealStepState) (hZst : size.bytes.toNat = 0) :
    npApplyTreeBorrowsReadAt prov absAddr size state = .ok state := by
  unfold npApplyTreeBorrowsReadAt
  simp only [hZst, ↓reduceIte]

/-- Tree Borrows read application for a dereferenced struct-field place
(`(*ptr).field[.unwrapUnsafeBinder]`): resolves `place` with
`npEvalPlaceNullaryPtr`, transitions and persists the borrow tree on the exact
byte range read. A place that fails to resolve is left to the read itself, which
reports the error. -/
def npTreeBorrowsReadApply (currentBody : CapturedMir) (place : Miri.MIR.Place)
    (state : AnnealStepState) : Except Miri.Interpreter.StepError AnnealStepState :=
  match npEvalPlaceNullaryPtr currentBody.localDecls currentBody.layouts place true state with
  | .error _ _ => .ok state
  | .ok rp _ =>
    match rp.ref with
    | .memory mp =>
      npApplyTreeBorrowsReadAt mp.ptr.provenance mp.ptr.offset.bytes rp.layout.layout.size state
    | .local _ _ _ _ => .ok state

/-- `npTreeBorrowsReadApply` lifted into `RvalueM AnnealStepState`, persisting
the transitioned borrow tree into the monadic state. -/
def npTreeBorrowsReadGate (currentBody : CapturedMir) (op : Miri.MIR.Operand) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  match op with
  | .Copy place | .Move place =>
    let st ← get
    match npTreeBorrowsReadApply currentBody place st with
    | .ok st' => set st'
    | .error e => throw e
  | _ => pure ()

/-- `npEvalOperandNullaryPtr` preceded, in `treeBorrows = true` mode, by the
state-transitioning Tree Borrows `.Read` gate on the dereferenced struct-field
place (persisting foreign-read demotions such as `.Unique -> .Frozen` and
protected `ReservedFrz false -> ReservedFrz true` via `Allocation.setExtra`). -/
def npEvalOperandNullaryPtrTb (currentBody : CapturedMir) (treeBorrows : Bool)
    (op : Miri.MIR.Operand) (known : Option Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  if treeBorrows then
    npTreeBorrowsReadGate currentBody op
  npEvalOperandNullaryPtr currentBody.localDecls currentBody.layouts op known

/-- Syntactic predicate for `Assign` rvalues routed through the overlay's own
`RvalueHooks`: `Operand.RuntimeChecks` uses and `PointerCoercion(Unsize)` casts. -/
def isNullaryPtrRvalue : Miri.MIR.Rvalue → Bool
  | .Use (.RuntimeChecks _) _ => true
  | .Cast (.PointerCoercion .Unsize _) _ _ => true
  | _ => false

/-- `RvalueHooks` overlay extending `annealRvalueHooksDropBinderSubtype` with the
`Operand.RuntimeChecks` operand arm, the `PointerCoercion(Unsize)` cast arm
(vendored `Cast.cast` over `annealCastHooksNullaryPtr`, threading `treeBorrows`
for live BorrowTree permission checks and targeting the destination's own
wide-pointer `TyId`), and struct-pointer dereference + field projections
(`(*ptr).field[.unwrapUnsafeBinder]`), whose reads run the Tree Borrows read
gate `npTreeBorrowsReadGate` when `treeBorrows = true`. Every other operand
and cast is delegated unchanged. -/
def annealRvalueHooksNullaryPtr (currentBody : CapturedMir) (fnPtrs : List FnPtrEntry := .nil)
    (treeBorrows : Bool := false) :
    Miri.Interpreter.RvalueHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealRvalueHooksDropBinderSubtype currentBody fnPtrs
  { base with
    evalPlace := fun _ p skipValidity =>
      npEvalPlaceNullaryPtr currentBody.localDecls currentBody.layouts p skipValidity
    evalOperand := fun c op known =>
      match op with
      | .RuntimeChecks checks => npEvalRuntimeChecksOperand currentBody.layouts c checks
      | _ =>
        if match op with | .Copy p | .Move p => npIsDerefFieldPlace p | _ => false then
          npEvalOperandNullaryPtrTb currentBody treeBorrows op known
        else base.evalOperand c op known
    evalOperandAt := fun c path op known =>
      match op with
      | .RuntimeChecks checks => npEvalRuntimeChecksOperand currentBody.layouts c checks
      | _ =>
        if match op with | .Copy p | .Move p => npIsDerefFieldPlace p | _ => false then
          npEvalOperandNullaryPtrTb currentBody treeBorrows op known
        else base.evalOperandAt c path op known
    evalPlaceToOp := fun c p known =>
      if npIsDerefFieldPlace p then
        npEvalOperandNullaryPtrTb currentBody treeBorrows (.Copy p) known
      else base.evalPlaceToOp c p known
    cast := fun c src kind ty dest =>
      match kind with
      | .PointerCoercion .Unsize _ =>
          Miri.Interpreter.Cast.cast
            (annealCastHooksNullaryPtr currentBody fnPtrs treeBorrows) c 16 src kind
            dest.layout.ty dest
      | _ => base.cast c src kind ty dest }

/-- Whether an assignment to `place` is subject to the Tree Borrows write check:
in `treeBorrows` mode, through an `UnwrapUnsafeBinder` place or a projected
field / dereferenced struct-field place. -/
def npTbWriteGate (treeBorrows : Bool) (place : Miri.MIR.Place) : Bool :=
  treeBorrows && (hasRealUnwrapUnsafeBinder place || npHasFieldProj place)

/-- Apply a Tree Borrows write to the byte range `[absAddr - baseAddr, +size)`
of the live allocation referenced by `prov` via `ep2ApplyTreeBorrowsWrite`
(unmodified vendored `Tree.LocationState.performAccess` per node with the
vendored global protected-tag table), persisting the transitioned borrow tree
with `Allocation.setExtra` and rejecting conflicts or offset overflows as
`StepError.undefinedBehavior`. Untracked allocations and non-concrete
provenances are left untouched.

A zero-sized write (`size = 0`, for example a ZST binder `unsafe<'a> ()`) is a
no-op decided BEFORE any allocation, offset, or tag lookup: Miri's memory hooks
run only for accesses of non-zero size, so a zero-sized write must not fault
even through a tag that is not registered in the allocation's borrow tree
(`ep2ApplyTreeBorrowsWrite` alone would report such a tag as a conflict, because
it resolves the tag before testing the size). -/
def npApplyTreeBorrowsWriteAt (prov : Option AnnealProv) (absAddr : UInt64)
    (size : Miri.ABI.Size) (state : AnnealStepState) :
    Except Miri.Interpreter.StepError AnnealStepState :=
  if size.bytes.toNat = 0 then .ok state else
  match prov with
  | some (.concrete aid tag) =>
    match state.machine.memory.live.findIdx? (fun e => e.1 == aid),
          ep2RelOffset? state.machine aid absAddr with
    | some lIdx, some rel =>
      if rel.toNat + size.bytes.toNat ≥ 2 ^ 64 then
        .error (.undefinedBehavior "Tree Borrows write offset overflow on unwrapUnsafeBinder place")
      else
      match state.machine.memory.live[lIdx]? with
      | some (_, liveAlloc) =>
        match state.machine.borrowTracker, liveAlloc.allocation.extra with
        | some bt, some tree =>
          match ep2ApplyTreeBorrowsWrite bt.global.protectedTags tree tag
              (Miri.ABI.Size.ofBytes rel) size with
          | some tree' =>
            .ok { state with
                  machine := updateAllocMachine state.machine lIdx aid liveAlloc.kind
                    (liveAlloc.allocation.setExtra (some tree')) }
          | none =>
            .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place")
        | _, _ => .ok state
      | none => .ok state
    | _, _ => .ok state
  | _ => .ok state

/-- Tree Borrows write through a resolved `UnwrapUnsafeBinder` destination
place. Resolves `place` with canonical `annealEvalPlaceOverlay`
(`Miri.Interpreter.PlaceDynamic.evalPlace`) so that BOTH:
* memory-backed locals (whole local `_1.unwrapUnsafeBinder` AND projected
  sub-places `(_1.unwrapUnsafeBinder).field(k)` using exact sub-place offset
  `off` and size `rp.layout.layout.size`, preserving sibling bytes), AND
* dereferenced pointer places (`(*_1).unwrapUnsafeBinder` and
  `*(_1.unwrapUnsafeBinder)` where `_1` is an immediate or indirect pointer to a
  memory-backed allocation carrying a borrow tree, yielding `.memory mp`)
apply `ep2ApplyTreeBorrowsWrite` to the exact target allocation, byte offset,
and written byte range. Immediate non-dereferenced locals, untracked allocations,
and place-resolution errors (which immediately surface from the subsequent
`evalRvalueIntoPlace` step) are left untouched. -/
def npTreeBorrowsWriteApply (currentBody : CapturedMir) (place : Miri.MIR.Place)
    (state : AnnealStepState) : Except Miri.Interpreter.StepError AnnealStepState :=
  match npEvalPlaceNullaryPtr currentBody.localDecls currentBody.layouts place true state with
  | .error _ _ => .ok state
  | .ok rp _ =>
    match rp.ref with
    | .memory mp =>
      npApplyTreeBorrowsWriteAt mp.ptr.provenance mp.ptr.offset.bytes rp.layout.layout.size state
    | .local _ localId offOpt _ =>
      match state.stack.currentFrame? with
      | none => .ok state
      | some frame =>
        match frame.getLocal localId with
        | .ok { value := .live (.indirect mp), .. } =>
          let relInLocal := (offOpt.getD Miri.ABI.Size.ZERO).bytes
          if mp.ptr.offset.bytes.toNat + relInLocal.toNat ≥ 2 ^ 64 then
            .error (.undefinedBehavior "Tree Borrows write offset overflow on unwrapUnsafeBinder place")
          else
            npApplyTreeBorrowsWriteAt mp.ptr.provenance (mp.ptr.offset.bytes + relInLocal)
              rp.layout.layout.size state
        | _ => .ok state

/-- The dereferenced struct-field place read by a `Use (Copy p)` / `Use (Move p)`
rvalue, if any (`npRvalueHasDerefField` as an `Option`). -/
def npRvalueDerefFieldSrc? : Miri.MIR.Rvalue → Option Miri.MIR.Place
  | .Use (.Copy p) _ | .Use (.Move p) _ => if npIsDerefFieldPlace p then some p else none
  | _ => none

/-- Tree Borrows accesses of an assignment whose destination is subject to the
write check, in the order in which Miri performs them: first the read of the
source place `src?` (when the rvalue copies a dereferenced struct-field place),
then the write of `place`. Trusted orders the two the same way (`evalRvalue`,
then the place write). -/
def npTreeBorrowsReadThenWriteApply (currentBody : CapturedMir) (place : Miri.MIR.Place)
    (src? : Option Miri.MIR.Place) (state : AnnealStepState) :
    Except Miri.Interpreter.StepError AnnealStepState :=
  match src? with
  | some src =>
    match npTreeBorrowsReadApply currentBody src state with
    | .ok state' => npTreeBorrowsWriteApply currentBody place state'
    | .error e => .error e
  | none => npTreeBorrowsWriteApply currentBody place state

/-- Gated Tree Borrows write check run before an assignment. When the rvalue
also reads a dereferenced struct-field place `src?`, that read is applied first
(`npTreeBorrowsReadThenWriteApply`). -/
def npTreeBorrowsWriteCheck (currentBody : CapturedMir) (treeBorrows : Bool)
    (place : Miri.MIR.Place) (state : AnnealStepState)
    (src? : Option Miri.MIR.Place := none) :
    Except Miri.Interpreter.StepError AnnealStepState :=
  if npTbWriteGate treeBorrows place then
    npTreeBorrowsReadThenWriteApply currentBody place src? state
  else .ok state

/-- Outside `treeBorrows` mode the write check never changes the state. -/
theorem npTreeBorrowsWriteCheck_basic_mode (currentBody : CapturedMir)
    (place : Miri.MIR.Place) (state : AnnealStepState) :
    npTreeBorrowsWriteCheck currentBody false place state = .ok state := rfl

/-- **Zero-sized `UnwrapUnsafeBinder` writes never reach the borrow tracker**:
for EVERY provenance (including a tag that is not registered in the
allocation's borrow tree), address, and state, `npApplyTreeBorrowsWriteAt` with
`size = 0` returns the state unchanged. -/
theorem npApplyTreeBorrowsWriteAt_zst_noop (prov : Option AnnealProv) (absAddr : UInt64)
    (size : Miri.ABI.Size) (state : AnnealStepState) (hZst : size.bytes.toNat = 0) :
    npApplyTreeBorrowsWriteAt prov absAddr size state = .ok state := by
  unfold npApplyTreeBorrowsWriteAt
  simp only [hZst, ↓reduceIte]

/-- Conservative `StepHooks` overlay extending `annealStepHooksDropBinderSubtype`:
* assignments first run `npTreeBorrowsWriteCheck` (a no-op unless
  `treeBorrows = true` and the destination is an `UnwrapUnsafeBinder` or field
  place); when the same statement also copies a dereferenced struct-field place,
  the Tree Borrows read of that source is applied before the write, as Miri
  does, and is not applied a second time while the rvalue is evaluated (that
  rvalue is a `Use`, so no `Unsize` check is skipped);
* `Operand.RuntimeChecks` uses and `PointerCoercion(Unsize)` casts
  (`isNullaryPtrRvalue`) run unmodified vendored `evalRvalueIntoPlace` over
  `annealRvalueHooksNullaryPtr` (threading `treeBorrows` so `Unsize` enforces
  live `BorrowTree` tag permissions when `treeBorrows = true`);
* every other assignment, every other statement, and every terminator is delegated
  unchanged. -/
def annealStepHooksNullaryPtr (currentBody : CapturedMir)
    (treeBorrows : Bool := false)
    (callees : List CapturedMir := .nil)
    (poppedFrame : Miri.TreeBorrows.FrameState := {})
    (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealStepHooksDropBinderSubtype currentBody treeBorrows callees poppedFrame fnPtrs
  { base with
    assign := fun choice place rvalue state =>
      match npTreeBorrowsWriteCheck currentBody treeBorrows place state
          (npRvalueDerefFieldSrc? rvalue) with
      | .error e => (state, .error e)
      | .ok state' =>
        if isNullaryPtrRvalue rvalue || npIsDerefFieldPlace place || npRvalueHasDerefField rvalue then
          Miri.Interpreter.runRvalue
            (Miri.Interpreter.evalRvalueIntoPlace
              (annealRvalueHooksNullaryPtr currentBody fnPtrs
                (treeBorrows &&
                  !(npTbWriteGate treeBorrows place && npRvalueHasDerefField rvalue)))
              choice rvalue place)
            state'
        else
          base.assign choice place rvalue state' }

/-- State-indexed `annealStepHooksNullaryPtr` at `(rootBody, s)`. -/
def annealStepHooksNullaryPtrForState (rootBody : CapturedMir) (s : MachineState)
    (treeBorrows : Bool := false) :
    Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  annealStepHooksNullaryPtr (activeMirBody rootBody s) treeBorrows s.memory.callees
    (annealPoppedFrameState s) s.memory.fnPtrs

/-- Syntactic predicate for statements untouched by the overlay: an `Assign` whose
rvalue and place are not routed through `annealRvalueHooksNullaryPtr` and whose
destination is not subject to the Tree Borrows write check. -/
def stmtFreeOfNullaryPtrOverlay (treeBorrows : Bool) (stmt : Miri.MIR.Statement) : Prop :=
  match stmt.kind with
  | .Assign place rvalue =>
      isNullaryPtrRvalue rvalue = false ∧ npIsDerefFieldPlace place = false ∧
      npRvalueHasDerefField rvalue = false ∧ npTbWriteGate treeBorrows place = false
  | _ => True

/-- **Conservative Extension Theorem (`step_nullaryPtr_overlay_eq_ep2_of_free`)**:
for EVERY `treeBorrows` mode, whenever the active frame's statements avoid the
overlay (`stmtFreeOfNullaryPtrOverlay`), `Miri.Interpreter.Step.step` under
`annealStepHooksNullaryPtr` is **identically equal** to `Miri.Interpreter.Step.step`
under `annealStepHooksDropBinderSubtype`. Terminators are never affected. -/
theorem step_nullaryPtr_overlay_eq_ep2_of_free {currentBody : CapturedMir}
    {callees : List CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState}
    {fnPtrs : List FnPtrEntry} {state : AnnealStepState} (choice : Unit) (treeBorrows : Bool)
    (hfree : ∀ frame, state.stack.currentFrame? = some frame →
      ∀ bb ∈ frame.body.basicBlocks.toList, ∀ stmt ∈ bb.statements.toList,
        stmtFreeOfNullaryPtrOverlay treeBorrows stmt) :
    Miri.Interpreter.Step.step
      (annealStepHooksNullaryPtr currentBody treeBorrows callees poppedFrame fnPtrs) choice state =
    Miri.Interpreter.Step.step
      (annealStepHooksDropBinderSubtype currentBody treeBorrows callees poppedFrame fnPtrs)
      choice state := by
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
        obtain ⟨hlt_b, hbb_eq⟩ := Array.getElem?_eq_some_iff.mp hbb
        have hbbFree := (hfree frame hcf) bb (hbb_eq ▸ Array.getElem_mem_toList hlt_b)
        dsimp only
        cases hst : bb.statements[loc.statementIndex]? with
        | some stmt =>
          obtain ⟨hlt_s, hst_eq⟩ := Array.getElem?_eq_some_iff.mp hst
          have hs := hbbFree stmt (hst_eq ▸ Array.getElem_mem_toList hlt_s)
          rcases stmt with ⟨si, kind⟩
          cases kind with
          | Assign place rvalue =>
            dsimp only [stmtFreeOfNullaryPtrOverlay] at hs
            have hAssign :
                (annealStepHooksNullaryPtr currentBody treeBorrows callees poppedFrame fnPtrs).assign
                  choice place rvalue state =
                (annealStepHooksDropBinderSubtype currentBody treeBorrows callees poppedFrame fnPtrs).assign
                  choice place rvalue state := by
              simp only [annealStepHooksNullaryPtr, npTreeBorrowsWriteCheck,
                         hs.1, hs.2.1, hs.2.2.1, hs.2.2.2,
                         Bool.or_self, Bool.false_eq_true, ↓reduceIte]
            have hEval :
                Miri.Interpreter.Step.evalStatement
                  (annealStepHooksNullaryPtr currentBody treeBorrows callees poppedFrame fnPtrs)
                  choice { sourceInfo := si, kind := .Assign place rvalue } state =
                Miri.Interpreter.Step.evalStatement
                  (annealStepHooksDropBinderSubtype currentBody treeBorrows callees poppedFrame fnPtrs)
                  choice { sourceInfo := si, kind := .Assign place rvalue } state := by
              unfold Miri.Interpreter.Step.evalStatement
              dsimp only
              exact hAssign
            dsimp only
            rw [hEval]
          | SetDiscriminant _ _ | PlaceMention _ | StorageLive _ | StorageDead _
          | Intrinsic _ | ConstEvalCounter | FakeRead _ | AscribeUserType _ _
          | Coverage _ | Nop | BackwardIncompatibleDropHint _ _ =>
            rfl
        | none => rfl

/-- **Leaf coincidence with the `C6` / `C8` overlay**: on `FnPtrToPtr` and on all
five non-`Unsize` pointer coercions, the overlay's `cast` leaf IS
`annealRvalueHooksUnwindFnPtrClosure`'s, for every source, target and destination.
Hence the universal `C6` / `C8` simulations of
`LeanMiriSpec.UnwindSetDiscrAndFnPtrLM` speak about the very cast this overlay
executes. -/
theorem np_rvalueHooks_cast_eq_unwind_on_c6_c8 (body : CapturedMir) (fnPtrs : List FnPtrEntry)
    (c : Unit) (src : Miri.Interpreter.OpTy AnnealProv) (ty : Miri.MIR.TyId)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    (annealRvalueHooksNullaryPtr body fnPtrs).cast c src .FnPtrToPtr ty dest =
      (annealRvalueHooksUnwindFnPtrClosure body fnPtrs).cast c src .FnPtrToPtr ty dest ∧
    (∀ cs, (annealRvalueHooksNullaryPtr body fnPtrs).cast c src
        (.PointerCoercion .UnsafeFnPointer cs) ty dest =
      (annealRvalueHooksUnwindFnPtrClosure body fnPtrs).cast c src
        (.PointerCoercion .UnsafeFnPointer cs) ty dest) ∧
    (∀ cs, (annealRvalueHooksNullaryPtr body fnPtrs).cast c src
        (.PointerCoercion .MutToConstPointer cs) ty dest =
      (annealRvalueHooksUnwindFnPtrClosure body fnPtrs).cast c src
        (.PointerCoercion .MutToConstPointer cs) ty dest) ∧
    (∀ cs, (annealRvalueHooksNullaryPtr body fnPtrs).cast c src
        (.PointerCoercion .ArrayToPointer cs) ty dest =
      (annealRvalueHooksUnwindFnPtrClosure body fnPtrs).cast c src
        (.PointerCoercion .ArrayToPointer cs) ty dest) ∧
    (∀ sf cs, (annealRvalueHooksNullaryPtr body fnPtrs).cast c src
        (.PointerCoercion (.ClosureFnPointer sf) cs) ty dest =
      (annealRvalueHooksUnwindFnPtrClosure body fnPtrs).cast c src
        (.PointerCoercion (.ClosureFnPointer sf) cs) ty dest) ∧
    (∀ sf cs, (annealRvalueHooksNullaryPtr body fnPtrs).cast c src
        (.PointerCoercion (.ReifyFnPointer sf) cs) ty dest =
      (annealRvalueHooksUnwindFnPtrClosure body fnPtrs).cast c src
        (.PointerCoercion (.ReifyFnPointer sf) cs) ty dest) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **Leaf coincidence with the `C9` overlay**: on every `Copy` / `Move` / `Constant`
operand (in particular every `UnwrapUnsafeBinder` place read), the overlay's
operand leaf IS `annealRvalueHooksUnwindFnPtrClosure`'s. -/
theorem np_rvalueHooks_evalOperandAt_eq_unwind_on_places (body : CapturedMir)
    (fnPtrs : List FnPtrEntry) (c : Unit) (path : Miri.Interpreter.OperandPath)
    (known : Option Miri.Interpreter.LocalLayout) :
    (∀ p, npIsDerefFieldPlace p = false →
      (annealRvalueHooksNullaryPtr body fnPtrs).evalOperandAt c path (.Copy p) known =
      (annealRvalueHooksUnwindFnPtrClosure body fnPtrs).evalOperandAt c path (.Copy p) known) ∧
    (∀ p, npIsDerefFieldPlace p = false →
      (annealRvalueHooksNullaryPtr body fnPtrs).evalOperandAt c path (.Move p) known =
      (annealRvalueHooksUnwindFnPtrClosure body fnPtrs).evalOperandAt c path (.Move p) known) ∧
    (∀ k, (annealRvalueHooksNullaryPtr body fnPtrs).evalOperandAt c path (.Constant k) known =
      (annealRvalueHooksUnwindFnPtrClosure body fnPtrs).evalOperandAt c path (.Constant k) known) := by
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun _ => rfl⟩
  · simp only [annealRvalueHooksNullaryPtr, hp, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp only [annealRvalueHooksNullaryPtr, hp, Bool.false_eq_true, ↓reduceIte]; rfl

/-- **`Unsize` dispatch**: for EVERY source, coercion source tag, target and
destination, the overlay's `cast` leaf on `PointerCoercion(Unsize)` is unmodified
vendored `Miri.Interpreter.Cast.cast` over `annealCastHooksNullaryPtr`, targeting
the destination's own (wide) `TyId`. -/
theorem np_rvalueHooks_cast_unsize_dispatch (body : CapturedMir) (fnPtrs : List FnPtrEntry)
    (c : Unit) (src : Miri.Interpreter.OpTy AnnealProv) (ty : Miri.MIR.TyId)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    ∀ cs, (annealRvalueHooksNullaryPtr body fnPtrs).cast c src (.PointerCoercion .Unsize cs) ty dest =
      Miri.Interpreter.Cast.cast (annealCastHooksNullaryPtr body fnPtrs) c 16 src
        (.PointerCoercion .Unsize cs) dest.layout.ty dest :=
  fun _ => rfl

/-! ## §2. `Rvalue.nullaryOp` Lowering (rustc Const-Evaluation of Layout Queries) -/

@[reducible] def constUsize (n : Nat) : Operand :=
  .constant { ty := usizeMirTy, val := .scalar (.int ⟨n, 8⟩) }

/-- Whether `op` is a compile-time layout query (`SizeOf` / `AlignOf` / `OffsetOf`),
which the pinned rustc const-evaluates away, as opposed to a runtime-flag query
(`UbChecks` / `ContractChecks`), which it lowers to `Operand::RuntimeChecks`. -/
def npNullOpIsLayoutQuery : NullOp → Bool
  | .sizeOf | .alignOf | .offsetOf _ => true
  | .ubChecks | .contractChecks => false

/-- Lower one rvalue: a layout query that Trusted `evalNullaryOp` resolves (from the
body's own `localDecls` / `layouts`) becomes the `usize` constant holding exactly
that scalar; an unresolved layout query, a runtime-flag query, and every other
rvalue are left unchanged (so an unresolved query still translates to
`untranslatableConstOperand` and steps to `StepError.unsupported`). -/
def lowerNullaryRvalue (decls : List LocalDecl) (layouts : LayoutTable) : Rvalue → Rvalue
  | .nullaryOp op argTy =>
    if npNullOpIsLayoutQuery op then
      match evalNullaryOp [] op argTy emptyMemory decls layouts with
      | .ok (.scalar sc) _ _ => .use (.constant { ty := usizeMirTy, val := .scalar (.int sc) })
      | _ => .nullaryOp op argTy
    else .nullaryOp op argTy
  | rv => rv

def lowerNullaryStmt (decls : List LocalDecl) (layouts : LayoutTable)
    (st : MirAst.Statement) : MirAst.Statement :=
  match st.kind with
  | .assign place rv => { st with kind := .assign place (lowerNullaryRvalue decls layouts rv) }
  | _ => st

/-- Mirror of rustc `14210df0`'s const-lowering of `NullOp::{SizeOf, AlignOf,
OffsetOf}` over a whole captured body (types, layouts, locals, terminators and the
block structure are untouched). -/
def lowerNullaryMirBody (body : CapturedMir) : CapturedMir :=
  { body with
    basicBlocks := body.basicBlocks.map fun bb =>
      { bb with statements := bb.statements.map (lowerNullaryStmt body.localDecls body.layouts) } }

/-- **`V1` Base-Translation Boundary**: for EVERY type and field path, unmodified
`Translate.translateRvalue` maps the three layout queries to
`untranslatableConstOperand` (which `evalMirConstImmediate` rejects with
`StepError.unsupported`), and the two runtime-flag queries to
`Operand.RuntimeChecks`. -/
theorem lm_np_v1_base_translate_boundary (ty : Ty) (fields : List (VariantIdx × FieldIdx)) :
    translateRvalue (.nullaryOp .sizeOf ty) =
      .Use (.Constant (untranslatableConstOperand ty)) .No ∧
    translateRvalue (.nullaryOp .alignOf ty) =
      .Use (.Constant (untranslatableConstOperand ty)) .No ∧
    translateRvalue (.nullaryOp (.offsetOf fields) ty) =
      .Use (.Constant (untranslatableConstOperand ty)) .No ∧
    translateRvalue (.nullaryOp .ubChecks ty) = .Use (.RuntimeChecks .UbChecks) .No ∧
    translateRvalue (.nullaryOp .contractChecks ty) = .Use (.RuntimeChecks .ContractChecks) .No :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Lowering law (resolved)**: for EVERY layout query that Trusted `evalNullaryOp`
resolves to a scalar `sc`, the lowered rvalue is the `usize` constant `sc`. -/
theorem lowerNullaryRvalue_resolved (decls : List LocalDecl) (layouts : LayoutTable)
    (op : NullOp) (argTy : Ty) (sc : MirAst.ScalarInt) (locals' : List LocalSlot) (mem' : Memory)
    (hq : npNullOpIsLayoutQuery op = true)
    (hev : evalNullaryOp [] op argTy emptyMemory decls layouts = .ok (.scalar sc) locals' mem') :
    lowerNullaryRvalue decls layouts (.nullaryOp op argTy) =
      .use (.constant { ty := usizeMirTy, val := .scalar (.int sc) }) := by
  simp only [lowerNullaryRvalue, hq, hev, ↓reduceIte]

/-- **Lowering law (unresolved)**: for EVERY layout query that Trusted
`evalNullaryOp` leaves `.unsupported`, lowering changes nothing, so the query keeps
its base translation (`untranslatableConstOperand`, `StepError.unsupported`). -/
theorem lowerNullaryRvalue_unresolved (decls : List LocalDecl) (layouts : LayoutTable)
    (op : NullOp) (argTy : Ty)
    (hq : npNullOpIsLayoutQuery op = true)
    (hev : evalNullaryOp [] op argTy emptyMemory decls layouts = .unsupported) :
    lowerNullaryRvalue decls layouts (.nullaryOp op argTy) = .nullaryOp op argTy := by
  simp only [lowerNullaryRvalue, hq, hev, ↓reduceIte]

/-- Runtime-flag queries are never lowered: they keep their native
`Operand.RuntimeChecks` translation. -/
theorem lowerNullaryRvalue_runtime_flags (decls : List LocalDecl) (layouts : LayoutTable)
    (ty : Ty) :
    translateRvalue (lowerNullaryRvalue decls layouts (.nullaryOp .ubChecks ty)) =
      .Use (.RuntimeChecks .UbChecks) .No ∧
    translateRvalue (lowerNullaryRvalue decls layouts (.nullaryOp .contractChecks ty)) =
      .Use (.RuntimeChecks .ContractChecks) .No :=
  ⟨rfl, rfl⟩

/-- **Lowered fixtures**: `size_of::<(u64, u32, u32)>() = 16`, `align_of = 8`,
`offset_of!(.., 2) = 12`, and `offset_of!(PaddedU8U32, 1) = 4` (past the 3 padding
bytes) become `usize` constants; the two `ubChecks` fixtures are unchanged. -/
theorem lowerNullaryMirBody_fixtures :
    lowerNullaryMirBody v1NullaryTupleMir =
      mkMirBody "np::v1_nullary_tuple"
        [mkDecl usizeMirTy, mkDecl usizeMirTy, mkDecl usizeMirTy, mkDecl usizeMirTy,
         mkDecl usizeMirTy] 0
        [mkBb [mkSt (.assign (locPlace 1) (.use (constUsize 16))),
               mkSt (.assign (locPlace 2) (.use (constUsize 8))),
               mkSt (.assign (locPlace 3) (.use (constUsize 12))),
               mkSt (.assign (locPlace 4) (.binaryOp .add (.copy (locPlace 1)) (.copy (locPlace 2)))),
               mkSt (.assign (locPlace 0) (.binaryOp .add (.copy (locPlace 4)) (.copy (locPlace 3))))]
          .return_] ∧
    lowerNullaryMirBody v1NullaryPaddedOffsetMir =
      mkMirBody "np::v1_nullary_padded_offset"
        [mkDecl usizeMirTy, mkDecl npPaddedMirTy] 0
        [mkBb [mkSt (.assign (locPlace 0) (.use (constUsize 4)))] .return_]
        npLayouts ∧
    lowerNullaryMirBody v1NullaryUbChecksMir = v1NullaryUbChecksMir ∧
    lowerNullaryMirBody v1NullaryUbBranchMir = v1NullaryUbBranchMir :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §3. Shared LeanMiri Execution, State & Observation Helpers -/

/-- Authority-typed LeanMiri observation, decoded from the `_0`
`Miri.Interpreter.LocalValue AnnealProv` (or `Miri.Interpreter.StepError`) returned
by stepping unmodified vendored `Miri.Interpreter.Step.step`. -/
inductive NullaryPtrLmObs : Type where
  | u32Val (bits : Nat)
  | u8Val (bits : Nat)
  | usizeVal (bits : Nat)
  | ptrAlloc (allocId : Nat)
  | ub
  | unsupported
  deriving DecidableEq, Repr

/-- Decode a vendored scalar: a pointer with concrete provenance is observed by its
allocation id; an integer by its width (1 / 4 / 8 bytes) and bits. -/
def npDecodeScalar (sc : Miri.Memory.Scalar AnnealProv) : NullaryPtrLmObs :=
  if sc.isPointer then
    match sc.toPointer annealTargetDataLayout with
    | .ok p =>
      match p.provenance with
      | some (.concrete aid _) => .ptrAlloc aid.value.toNat
      | _ => .unsupported
    | .error _ => .unsupported
  else
    match sc.toScalarInt with
    | .ok msc =>
      if msc.size == Miri.ABI.Size.ofBytes 1 then .u8Val msc.data.toNat
      else if msc.size == Miri.ABI.Size.ofBytes 4 then .u32Val msc.data.toNat
      else if msc.size == Miri.ABI.Size.ofBytes 8 then .usizeVal msc.data.toNat
      else .unsupported
    | .error _ => .unsupported

/-- Decode a `runMiriSteps` result into `NullaryPtrLmObs`. -/
def npToObs (res : Except Miri.Interpreter.StepError
    (AnnealStepState × Option (Miri.Interpreter.LocalValue AnnealProv))) : NullaryPtrLmObs :=
  match res with
  | .ok (_, some (.live (.immediate (.scalar sc)))) => npDecodeScalar sc
  | .ok _ => .unsupported
  | .error (.undefinedBehavior _) => .ub
  | .error _ => .unsupported

private def npIsUnsupportedErr {α : Type} (res : Except Miri.Interpreter.StepError α) : Bool :=
  match res with
  | .error (.unsupported _) => true
  | _ => false

private def npIsInvalidProgErr {α : Type} (res : Except Miri.Interpreter.StepError α) : Bool :=
  match res with
  | .error (.invalidProgram _) => true
  | _ => false

private def npMkState (body : CapturedMir) (retTy : Ty)
    (locs : Array (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout))
    (mach : AnnealMachine := AnnealMachine.empty) : AnnealStepState :=
  { stack := { frames := #[{
      body := translateBody body,
      bodyIdentity := .ofCanonicalIndex 0,
      functionInstance := { kind := .Item 0, args := #[] },
      extra := (), returnContinuation := .stop false,
      returnPlace := .frameLocal 0 0 none (translateTyOverlay retTy body.layouts) (.ofAllocationToken 0),
      localsIdentity := .ofAllocationToken 0, locals := locs, vaList := #[],
      trackCallerArg := none, location := .mir ⟨0, 0⟩ }] },
    machine := mach }

private def npScalarUInt (bits : Nat) (szBytes : UInt64) : Miri.Memory.Scalar AnnealProv :=
  match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 bits) (Miri.ABI.Size.ofBytes szBytes) with
  | .ok s => s
  | .error _ => Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨.ZERO, .wildcard⟩

private def npAllocId (n : Nat) (hn : UInt64.ofNat n ≠ 0) : Miri.Memory.AllocId :=
  ⟨UInt64.ofNat n, hn⟩

private def npAid1 : Miri.Memory.AllocId := npAllocId 1 (by decide)
private def npAid5 : Miri.Memory.AllocId := npAllocId 5 (by decide)
private def npFnAid : Miri.Memory.AllocId := npAllocId 65536 (by decide)
private def npFnAid2 : Miri.Memory.AllocId := npAllocId 65537 (by decide)

private def npBase1 : UInt64 := 256
private def npBase5 : UInt64 := 1024
private def npFnBase : UInt64 := annealStackBaseAddr npFnAid
private def npFnBase2 : UInt64 := annealStackBaseAddr npFnAid2

private def npPtrScalarTagged (aid : Miri.Memory.AllocId) (base : UInt64)
    (tag : Miri.Memory.BorTag) : Miri.Memory.Scalar AnnealProv :=
  Miri.Memory.Scalar.fromPointer annealTargetDataLayout
    ⟨Miri.ABI.Size.ofBytes base, .concrete aid tag⟩

private def npPtrScalar (aid : Miri.Memory.AllocId) (base : UInt64) :
    Miri.Memory.Scalar AnnealProv :=
  npPtrScalarTagged aid base .one

private def npAddrMachine (entries : Array Miri.Memory.AllocAddresses.BaseAddressEntry) :
    AnnealMachine :=
  { AnnealMachine.empty with
    addresses := { AnnealMachine.empty.addresses with baseAddr := entries } }

private def npUninit (lay : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
  ⟨.live (.immediate .uninit), some lay⟩

private def npScalarLocal (sc : Miri.Memory.Scalar AnnealProv) (lay : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout :=
  ⟨.live (.immediate (.scalar sc)), some lay⟩

private def npLocalVal? (st : AnnealStepState) (idx : Nat) :
    Option (Miri.Interpreter.LocalValue AnnealProv) :=
  st.stack.frames[0]?.bind (fun f => f.locals[idx]?.map (·.value))

private def npFnMachine : AnnealMachine := npAddrMachine #[⟨npFnAid, npFnBase⟩]
private def npFnMachine2 : AnnealMachine := npAddrMachine #[⟨npFnAid2, npFnBase2⟩]
private def npMachine5 : AnnealMachine := npAddrMachine #[⟨npAid5, npBase5⟩]

/-! ### `V1` states -/

private def npStV1TupleUnlowered : AnnealStepState :=
  let lay := translateTyOverlay usizeMirTy emptyLayoutTable
  npMkState v1NullaryTupleMir usizeMirTy
    #[npUninit lay, npUninit lay, npUninit lay, npUninit lay, npUninit lay]

private def npStV1Tuple : AnnealStepState :=
  let lay := translateTyOverlay usizeMirTy emptyLayoutTable
  npMkState (lowerNullaryMirBody v1NullaryTupleMir) usizeMirTy
    #[npUninit lay, npUninit lay, npUninit lay, npUninit lay, npUninit lay]

private def npStV1UbChecks : AnnealStepState :=
  npMkState v1NullaryUbChecksMir boolMirTy
    #[npUninit (translateTyOverlay boolMirTy emptyLayoutTable)]

private def npStV1UbBranch : AnnealStepState :=
  npMkState v1NullaryUbBranchMir u32MirTy
    #[npUninit (translateTyOverlay u32MirTy emptyLayoutTable),
      npUninit (translateTyOverlay boolMirTy emptyLayoutTable)]

private def npStV1PaddedUnlowered : AnnealStepState :=
  npMkState v1NullaryPaddedOffsetMir usizeMirTy
    #[npUninit (translateTyOverlay usizeMirTy npLayouts),
      npUninit (translateTyOverlay npPaddedMirTy npLayouts)]

private def npStV1Padded : AnnealStepState :=
  npMkState (lowerNullaryMirBody v1NullaryPaddedOffsetMir) usizeMirTy
    #[npUninit (translateTyOverlay usizeMirTy npLayouts),
      npUninit (translateTyOverlay npPaddedMirTy npLayouts)]

private def npContractChecksMir : CapturedMir :=
  mkMirBody "np::w_contract_checks" [mkDecl boolMirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.nullaryOp .contractChecks boolMirTy))] .return_]

private def npStContractChecks : AnnealStepState :=
  npMkState npContractChecksMir boolMirTy
    #[npUninit (translateTyOverlay boolMirTy emptyLayoutTable)]

/-! ### `V2` states -/

private def npStV2Pipeline : AnnealStepState :=
  npMkState v2PtrCoerceFnPipelineMir npUnsafeFnPtrMirTy
    #[npUninit (translateTyOverlay npUnsafeFnPtrMirTy emptyLayoutTable),
      npUninit (translateTyOverlay npSafeFnPtrMirTy emptyLayoutTable)]
    npFnMachine

private def npStV2Unsize (src : Miri.Interpreter.LocalValue AnnealProv) : AnnealStepState :=
  npMkState v2PtrCoerceUnsizeSliceMir usizeMirTy
    #[npUninit (translateTyOverlay usizeMirTy emptyLayoutTable),
      ⟨src, some (translateTyOverlay npRawConstArr3U32MirTy emptyLayoutTable)⟩,
      npUninit (translateTyOverlay rawConstSliceU32MirTy emptyLayoutTable)]
    npMachine5

private def npStV2DeadUb : AnnealStepState :=
  npMkState v2PtrCoerceDeadUbMir rawConstU32MirTy
    #[npUninit (translateTyOverlay rawConstU32MirTy emptyLayoutTable),
      npScalarLocal (npPtrScalar npAid5 npBase5) (translateTyOverlay rawMutU32MirTy emptyLayoutTable)]
    npMachine5

private def npStV2ArrayToPtr : AnnealStepState :=
  npMkState v2PtrCoerceArrayToPtrMir rawConstU32MirTy
    #[npUninit (translateTyOverlay rawConstU32MirTy emptyLayoutTable),
      npScalarLocal (npPtrScalar npAid5 npBase5)
        (translateTyOverlay npRawConstArr3U32MirTy emptyLayoutTable)]
    npMachine5

private def npClosureFnPtrMir : CapturedMir :=
  mkMirBody "np::w_closure_fn_pointer" [mkDecl npSafeFnPtrMirTy, mkDecl npZstClosMirTy] 1
    [mkBb [mkSt (.assign (locPlace 0)
             (.cast (.pointerCoercion "ClosureFnPointer(Safe)") (.copy (locPlace 1)) npSafeFnPtrMirTy))]
      .return_]
    npLayouts

private def npStClosureFnPtr : AnnealStepState :=
  npMkState npClosureFnPtrMir npSafeFnPtrMirTy
    #[npUninit (translateTyOverlay npSafeFnPtrMirTy npLayouts),
      npUninit (translateTyOverlay npZstClosMirTy npLayouts)]
    npFnMachine

private def npMutToConstThinMir : CapturedMir :=
  mkMirBody "np::w_mut_to_const_thin" [mkDecl rawConstU32MirTy, mkDecl rawMutU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0)
             (.cast (.pointerCoercion "MutToConstPointer") (.copy (locPlace 1)) rawConstU32MirTy))]
      .return_]

private def npStMutToConstThin : AnnealStepState :=
  npMkState npMutToConstThinMir rawConstU32MirTy
    #[npUninit (translateTyOverlay rawConstU32MirTy emptyLayoutTable),
      npScalarLocal (npPtrScalar npAid5 npBase5) (translateTyOverlay rawMutU32MirTy emptyLayoutTable)]
    npMachine5

@[reducible] def npRawMutDynMirTy : Ty :=
  { kind := .rawPtr .mut (.dynamic "np::Trait"), layoutIdx := 0 }
@[reducible] def npRawConstDynMirTy : Ty :=
  { kind := .rawPtr .not (.dynamic "np::Trait"), layoutIdx := 0 }

private def npMutToConstDynMir : CapturedMir :=
  mkMirBody "np::w_mut_to_const_dyn" [mkDecl npRawConstDynMirTy, mkDecl npRawMutDynMirTy] 1
    [mkBb [mkSt (.assign (locPlace 0)
             (.cast (.pointerCoercion "MutToConstPointer") (.copy (locPlace 1)) npRawConstDynMirTy))]
      .return_]

private def npStMutToConstDyn : AnnealStepState :=
  npMkState npMutToConstDynMir npRawConstDynMirTy
    #[npUninit (translateTyOverlay npRawConstDynMirTy emptyLayoutTable),
      ⟨.live (.immediate (.scalarPair (npPtrScalar npFnAid npFnBase) (npPtrScalar npFnAid2 npFnBase2))),
       some (translateTyOverlay npRawMutDynMirTy emptyLayoutTable)⟩]
    (npAddrMachine #[⟨npFnAid, npFnBase⟩, ⟨npFnAid2, npFnBase2⟩])

/-! ### `V3` states -/

private def npStV3Const (src : Miri.Interpreter.LocalValue AnnealProv)
    (mach : AnnealMachine := npFnMachine) : AnnealStepState :=
  npMkState v3FnPtrToPtrConstMir rawConstUnitMirTy
    #[npUninit (translateTyOverlay rawConstUnitMirTy emptyLayoutTable),
      ⟨src, some (translateTyOverlay npSafeFnPtrMirTy emptyLayoutTable)⟩]
    mach

private def npStV3MutChain : AnnealStepState :=
  npMkState v3FnPtrToPtrMutChainMir rawConstU32MirTy
    #[npUninit (translateTyOverlay rawConstU32MirTy emptyLayoutTable),
      npScalarLocal (npPtrScalar npFnAid2 npFnBase2)
        (translateTyOverlay npSafeFnPtrMirTy emptyLayoutTable),
      npUninit (translateTyOverlay npRawMutU8MirTy emptyLayoutTable)]
    npFnMachine2

private def npStV3DeadUb : AnnealStepState :=
  npMkState v3FnPtrToPtrDeadUbMir rawConstUnitMirTy
    #[npUninit (translateTyOverlay rawConstUnitMirTy emptyLayoutTable),
      npScalarLocal (npPtrScalar npFnAid npFnBase)
        (translateTyOverlay npSafeFnPtrMirTy emptyLayoutTable)]
    npFnMachine

@[reducible] def npIntrFnPtrMirTy : Ty :=
  { kind := .fnPtr .nil (.tuple .nil) .safe .rustIntrinsic, layoutIdx := 0 }

private def npFnPtrToPtrIntrMir : CapturedMir :=
  mkMirBody "np::w_fn_ptr_to_ptr_intrinsic" [mkDecl rawConstUnitMirTy, mkDecl npIntrFnPtrMirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .fnPtrToPtr (.copy (locPlace 1)) rawConstUnitMirTy))]
      .return_]

private def npIntrFnPtrs : List FnPtrEntry :=
  [{ allocId := 65536, defPath := "np::intr_fn", typeArgs := .nil,
     fnSig := some npIntrFnPtrMirTy.kind }]

private def npStFnPtrToPtrIntr : AnnealStepState :=
  npMkState npFnPtrToPtrIntrMir rawConstUnitMirTy
    #[npUninit (translateTyOverlay rawConstUnitMirTy emptyLayoutTable),
      npScalarLocal (npPtrScalar npFnAid npFnBase)
        (translateTyOverlay npIntrFnPtrMirTy emptyLayoutTable)]
    npFnMachine

private def npIntrTrustedState : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.ptr ⟨65536, 0⟩ 8)] },
    memory := { emptyMemory with fnPtrs := npIntrFnPtrs } }

private def npFnPtrToPtrRawSrcMir : CapturedMir :=
  mkMirBody "np::w_fn_ptr_to_ptr_raw_src" [mkDecl rawConstUnitMirTy, mkDecl rawMutU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .fnPtrToPtr (.copy (locPlace 1)) rawConstUnitMirTy))]
      .return_]

private def npStFnPtrToPtrRawSrc : AnnealStepState :=
  npMkState npFnPtrToPtrRawSrcMir rawConstUnitMirTy
    #[npUninit (translateTyOverlay rawConstUnitMirTy emptyLayoutTable),
      npScalarLocal (npPtrScalar npAid5 npBase5) (translateTyOverlay rawMutU32MirTy emptyLayoutTable)]
    npMachine5

/-! ### `V4` states -/

private def npStV4Roundtrip : AnnealStepState :=
  npMkState v4UnwrapBinderRoundtripMir u32MirTy
    #[npUninit (translateTyOverlay u32MirTy npLayouts),
      npScalarLocal (npScalarUInt 11 4) (translateTyOverlay u32MirTy npLayouts),
      npUninit (translateTyOverlay npBinderU32MirTy npLayouts)]

private def npStV4NzU8 (n : Nat) : AnnealStepState :=
  npMkState v4UnwrapBinderNzU8Mir u8MirTy
    #[npUninit (translateTyOverlay u8MirTy npLayouts),
      npScalarLocal (npScalarUInt n 1) (translateTyOverlay u8MirTy npLayouts),
      npUninit (translateTyOverlay npBinderNzU8MirTy npLayouts)]

private def npStV4DeadUb : AnnealStepState :=
  npMkState v4UnwrapBinderDeadUbMir u32MirTy
    #[npUninit (translateTyOverlay u32MirTy npLayouts),
      npScalarLocal (npScalarUInt 11 4) (translateTyOverlay npBinderU32MirTy npLayouts)]

/-- Two-node vendored Tree Borrows tree over the 4 bytes of a `u32`-sized binder:
root `retagParentTag` (`Unique`) with an accessed `Unique` child `retagChildTag`
(`hooksTwoNodeTree .unique`, restricted to `[0, 4)`). -/
private def npU32ChildTree : Miri.TreeBorrows.BorrowTree :=
  { hooksTwoNodeTree .unique with
    locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 4) (hooksLocTree .unique) }

private def npExtractOk {ε α : Type} : (r : Except ε α) → r.isOk = true → α
  | .ok a, _ => a
  | .error _, h => nomatch h

private def npAlign4 : Miri.ABI.Align := ⟨2⟩

private def npUninit4Alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (npExtractOk
    (Miri.Memory.Allocation.tryNew (Prov := AnnealProv) (Miri.ABI.Size.ofBytes 4) npAlign4 .Uninit
      (fun _ _ => some #[0, 0, 0, 0]))
    (by decide +kernel)).withExtra none

private def npU32Alloc11 : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) #[11, 0, 0, 0] npAlign4 .Mut with
  | .ok al => al.withExtra (some npU32ChildTree)
  | .error _ => npUninit4Alloc

/-- Initial Miri state in which `_1 : np::BinderU32 = 11` is **memory-backed** at
allocation `npAid1` (base `256`) carrying `npU32ChildTree`, and is accessed through
the root tag `retagParentTag`. The borrow tracker's global protected-tag table
protects the child `retagChildTag` with a `StrongProtector` iff `childProtected`. -/
private def mkNpTbUnwrapState (body : CapturedMir) (childProtected : Bool) : AnnealStepState :=
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with live := #[(npAid1, ⟨.stack, npU32Alloc11⟩)] },
      addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨npAid1, npBase1⟩] },
      borrowTracker := some
        { global := { protectedTags := (hooksForChildProtected childProtected).protectedTags },
          retagMode := .Default } }
  let mp : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Miri.ABI.Size.ofBytes npBase1, some (.concrete npAid1 retagParentTag)⟩, .none, none⟩
  npMkState body u32MirTy
    #[npUninit (translateTyOverlay u32MirTy npLayouts),
      ⟨.live (.indirect mp), some (translateTyOverlay npBinderU32MirTy npLayouts)⟩] mach

/-! ### `V2` `Unsize` fidelity & `V4` deref / sub-place Tree Borrows fixtures -/

@[reducible] private def npRawMutArr3U32MirTy : Ty :=
  { kind := .rawPtr .mut (.array (.uint .u32) 3), layoutIdx := 0 }
@[reducible] private def npRawMutSliceU32MirTy : Ty :=
  { kind := .rawPtr .mut (.slice (.uint .u32)), layoutIdx := 0 }
@[reducible] private def npRawConstSliceU8MirTy : Ty :=
  { kind := .rawPtr .not (.slice (.uint .u8)), layoutIdx := 0 }
@[reducible] private def npRawConstArrOverflowU32MirTy : Ty :=
  { kind := .rawPtr .not (.array (.uint .u32) (scalarModulus 8 + 3)), layoutIdx := 0 }
@[reducible] private def npRefArr3U32MirTy : Ty :=
  { kind := .ref .not (.array (.uint .u32) 3), layoutIdx := 0 }
@[reducible] private def npRefMutArr3U32MirTy : Ty :=
  { kind := .ref .mut (.array (.uint .u32) 3), layoutIdx := 0 }
@[reducible] private def npRefSliceU32MirTy : Ty :=
  { kind := .ref .not (.slice (.uint .u32)), layoutIdx := 0 }
@[reducible] private def npRefMutSliceU32MirTy : Ty :=
  { kind := .ref .mut (.slice (.uint .u32)), layoutIdx := 0 }

private def mkNpUnsizeMir (name : String) (srcTy dstTy : Ty) : CapturedMir :=
  mkMirBody name [mkDecl usizeMirTy, mkDecl srcTy, mkDecl dstTy] 1
    [mkBb [mkSt (.assign (locPlace 2) (.cast (.pointerCoercion "Unsize") (.copy (locPlace 1)) dstTy)),
           mkSt (.assign (locPlace 0) (.unaryOp .ptrMetadata (.copy (locPlace 2))))]
      .return_]

private def npUnsizeMutToConstMir : CapturedMir :=
  mkNpUnsizeMir "np::w_unsize_mut_to_const" npRawMutArr3U32MirTy rawConstSliceU32MirTy
private def npUnsizeMutToMutMir : CapturedMir :=
  mkNpUnsizeMir "np::w_unsize_mut_to_mut" npRawMutArr3U32MirTy npRawMutSliceU32MirTy
private def npUnsizeRefConstMir : CapturedMir :=
  mkNpUnsizeMir "np::w_unsize_ref_const" npRefArr3U32MirTy npRefSliceU32MirTy
private def npUnsizeRefMutToConstMir : CapturedMir :=
  mkNpUnsizeMir "np::w_unsize_ref_mut_to_const" npRefMutArr3U32MirTy npRefSliceU32MirTy
private def npUnsizeRefMutToMutMir : CapturedMir :=
  mkNpUnsizeMir "np::w_unsize_ref_mut_to_mut" npRefMutArr3U32MirTy npRefMutSliceU32MirTy
private def npUnsizeRefToRawMir : CapturedMir :=
  mkNpUnsizeMir "np::w_unsize_ref_to_raw" npRefArr3U32MirTy rawConstSliceU32MirTy
private def npUnsizeBadMutUpgradeMir : CapturedMir :=
  mkNpUnsizeMir "np::w_unsize_bad_mut_upgrade" npRawConstArr3U32MirTy npRawMutSliceU32MirTy
private def npUnsizeBadElemMismatchMir : CapturedMir :=
  mkNpUnsizeMir "np::w_unsize_bad_elem_mismatch" npRawConstArr3U32MirTy npRawConstSliceU8MirTy
private def npUnsizeBadLenOverflowMir : CapturedMir :=
  mkNpUnsizeMir "np::w_unsize_bad_len_overflow" npRawConstArrOverflowU32MirTy rawConstSliceU32MirTy
private def npUnsizeBadRawToRefMir : CapturedMir :=
  mkNpUnsizeMir "np::w_unsize_bad_raw_to_ref" npRawConstArr3U32MirTy npRefSliceU32MirTy
private def npUnsizeBadRefMutUpgradeMir : CapturedMir :=
  mkNpUnsizeMir "np::w_unsize_bad_ref_mut_upgrade" npRefArr3U32MirTy npRefMutSliceU32MirTy

/-- Two-node vendored Tree Borrows tree over the 12 bytes of a `[u32; 3]` array
allocation: root `retagParentTag` (`Unique`) with child `retagChildTag` carrying
`annealPermToMiri perm` across `[0, 12)`. -/
def npArr3U32Tree (perm : TreeBorrowPerm) : Miri.TreeBorrows.BorrowTree :=
  { hooksTwoNodeTree perm with
    locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 12) (hooksLocTree perm) }

private def npArr3U32Alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.fromBytes (Prov := AnnealProv)
      #[1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0] npAlign4 .Mut with
  | .ok al => al.withExtra none
  | .error _ => npUninit4Alloc

private def npArr3U32AllocTree (perm : TreeBorrowPerm) :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  npArr3U32Alloc.setExtra (some (npArr3U32Tree perm))

private def npMachine5Live : AnnealMachine :=
  { memory := { AnnealMachine.empty.memory with live := #[(npAid5, ⟨.stack, npArr3U32Alloc⟩)] },
    addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨npAid5, npBase5⟩] } }

private def npMachine5Tree (perm : TreeBorrowPerm) : AnnealMachine :=
  { memory := { AnnealMachine.empty.memory with live := #[(npAid5, ⟨.stack, npArr3U32AllocTree perm⟩)] },
    addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨npAid5, npBase5⟩] },
    borrowTracker := some { global := {}, retagMode := .Default } }

private def mkNpUnsizeState (body : CapturedMir) (srcTy dstTy : Ty)
    (src : Miri.Interpreter.LocalValue AnnealProv)
    (mach : AnnealMachine := npMachine5) : AnnealStepState :=
  npMkState body usizeMirTy
    #[npUninit (translateTyOverlay usizeMirTy emptyLayoutTable),
      ⟨src, some (translateTyOverlay srcTy emptyLayoutTable)⟩,
      npUninit (translateTyOverlay dstTy emptyLayoutTable)]
    mach

private def npV4DerefUnwrapProtectedMir : CapturedMir :=
  mkMirBody "np::w_v4_deref_unwrap_protected"
    [mkDecl u32MirTy, mkDecl rawMutU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 1 [.deref, .unwrapUnsafeBinder u32MirTy]) (.use (constU32 42))),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.deref, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]

private def npV4UnwrapDerefProtectedMir : CapturedMir :=
  mkMirBody "np::w_v4_unwrap_deref_protected"
    [mkDecl u32MirTy, mkDecl rawMutU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 1 [.unwrapUnsafeBinder rawMutU32MirTy, .deref]) (.use (constU32 42))),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.unwrapUnsafeBinder rawMutU32MirTy, .deref]))))]
      .return_]

private def mkNpTbDerefUnwrapState (body : CapturedMir) (childProtected : Bool) : AnnealStepState :=
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with live := #[(npAid1, ⟨.stack, npU32Alloc11⟩)] },
      addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨npAid1, npBase1⟩] },
      borrowTracker := some
        { global := { protectedTags := (hooksForChildProtected childProtected).protectedTags },
          retagMode := .Default } }
  npMkState body u32MirTy
    #[npUninit (translateTyOverlay u32MirTy emptyLayoutTable),
      npScalarLocal (npPtrScalarTagged npAid1 npBase1 retagParentTag)
        (translateTyOverlay rawMutU32MirTy emptyLayoutTable)]
    mach

private def npPaddedAlloc8 : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.fromBytes (Prov := AnnealProv)
      #[7, 0, 0, 0, 11, 0, 0, 0] npAlign4 .Mut with
  | .ok al => al.withExtra (some (hooksTwoNodeTree .unique))
  | .error _ => npUninit4Alloc

private def npV4FieldUnwrapMir : CapturedMir :=
  mkMirBody "np::w_v4_field_unwrap_subrange"
    [mkDecl u32MirTy, mkDecl npPaddedMirTy] 1
    [mkBb [mkSt (.assign (locPlace 1 [.unwrapUnsafeBinder npPaddedMirTy, .field 1 u32MirTy])
             (.use (constU32 42))),
           mkSt (.assign (locPlace 0)
             (.use (.copy (locPlace 1 [.unwrapUnsafeBinder npPaddedMirTy, .field 1 u32MirTy]))))]
      .return_]
    npLayouts

private def mkNpTbFieldUnwrapState (childProtected : Bool) : AnnealStepState :=
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with live := #[(npAid1, ⟨.stack, npPaddedAlloc8⟩)] },
      addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨npAid1, npBase1⟩] },
      borrowTracker := some
        { global := { protectedTags := (hooksForChildProtected childProtected).protectedTags },
          retagMode := .Default } }
  let mp : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Miri.ABI.Size.ofBytes npBase1, some (.concrete npAid1 retagParentTag)⟩, .none, none⟩
  npMkState npV4FieldUnwrapMir u32MirTy
    #[npUninit (translateTyOverlay u32MirTy npLayouts),
      ⟨.live (.indirect mp), some (translateTyOverlay npPaddedMirTy npLayouts)⟩]
    mach

/-! ## §4. Per-Variant Concrete Witnesses (`V1`–`V4`) -/

/-- **`V1` (`Rvalue.nullaryOp`) Boundary & Lowered Witness**:
1. unlowered layout queries (`v1NullaryTupleMir`, `v1NullaryPaddedOffsetMir`) step
   to `StepError.unsupported` under the overlay itself (honest pinned-rustc removal
   boundary);
2. without the overlay's `runtimeChecks` leaf, `annealStepHooksDropBinderSubtype`
   rejects `Operand.RuntimeChecks` with `StepError.unsupported`;
3. the lowered tuple body returns `16 + 8 + 12 = 36`, and the lowered padded
   `offset_of!` body returns `4`;
4. `ubChecks` returns the `bool` `true` (`1`) natively, and the `ubChecks`-guarded
   branch reaches `Unreachable` (UB);
5. `contractChecks` fails closed (`unsupported`). -/
theorem lm_np_v1_nullaryOp_boundary_and_lowered_witness :
    npIsUnsupportedErr (Miri.Interpreter.Step.step
      (annealStepHooksNullaryPtr v1NullaryTupleMir) () npStV1TupleUnlowered).2 = true ∧
    npIsUnsupportedErr (Miri.Interpreter.Step.step
      (annealStepHooksNullaryPtr v1NullaryPaddedOffsetMir) () npStV1PaddedUnlowered).2 = true ∧
    npIsUnsupportedErr (Miri.Interpreter.Step.step
      (annealStepHooksDropBinderSubtype v1NullaryUbChecksMir) () npStV1UbChecks).2 = true ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr (lowerNullaryMirBody v1NullaryTupleMir)) 12
      npStV1Tuple) = .usizeVal 36 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr (lowerNullaryMirBody v1NullaryPaddedOffsetMir)) 8
      npStV1Padded) = .usizeVal 4 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v1NullaryUbChecksMir) 8 npStV1UbChecks) =
      .u8Val 1 ∧
    (runMiriSteps (annealStepHooksNullaryPtr v1NullaryUbBranchMir) 8 npStV1UbBranch).map (·.2) =
      .error (.undefinedBehavior "Unreachable") ∧
    npIsUnsupportedErr (runMiriSteps (annealStepHooksNullaryPtr npContractChecksMir) 8
      npStContractChecks) = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **`V2` (`CastKind.pointerCoercion`) Six-Subkind Witness** (each run steps
unmodified vendored `Miri.Interpreter.Step.step` to the final `Return`):
1. `ReifyFnPointer` -> `UnsafeFnPointer` pipeline returns function allocation `65536`;
2. `ClosureFnPointer(Safe)` of a zero-capture closure returns function allocation `65536`;
3. thin `MutToConstPointer` preserves allocation `5`;
4. wide `dyn Trait` `MutToConstPointer` preserves BOTH the data pointer (`65536`)
   and the vtable pointer (`65537`);
5. `ArrayToPointer` preserves allocation `5`;
6. `Unsize` of `*const [u32; 3]` to `*const [u32]` yields metadata `3`, while a dead
   or uninitialized source pointer is UB. -/
theorem lm_np_v2_pointerCoercion_six_subkinds_witness :
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v2PtrCoerceFnPipelineMir false [v2CalleeU32Mir])
      8 npStV2Pipeline) = .ptrAlloc 65536 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npClosureFnPtrMir) 8 npStClosureFnPtr) =
      .ptrAlloc 65536 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npMutToConstThinMir) 8 npStMutToConstThin) =
      .ptrAlloc 5 ∧
    (match Miri.Interpreter.Step.step (annealStepHooksNullaryPtr npMutToConstDynMir) ()
        npStMutToConstDyn with
      | (st', .ok true) =>
        (match npLocalVal? st' 0 with
          | some (.live (.immediate (.scalarPair a b))) =>
            decide (npDecodeScalar a = .ptrAlloc 65536) && decide (npDecodeScalar b = .ptrAlloc 65537)
          | _ => false)
      | _ => false) = true ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v2PtrCoerceArrayToPtrMir) 8 npStV2ArrayToPtr) =
      .ptrAlloc 5 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v2PtrCoerceUnsizeSliceMir) 8
      (npStV2Unsize (.live (.immediate (.scalar (npPtrScalar npAid5 npBase5)))))) = .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v2PtrCoerceUnsizeSliceMir) 8
      (npStV2Unsize .dead)) = .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v2PtrCoerceUnsizeSliceMir) 8
      (npStV2Unsize (.live (.immediate .uninit)))) = .ub := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **`V2` `Unsize` Base Boundary**: without the overlay's `lockstepTails` /
`typeInfo` leaves, `annealStepHooksDropBinderSubtype` cannot step
`PointerCoercion(Unsize)` and never reports it as undefined behavior. -/
theorem lm_np_v2_unsize_base_boundary :
    (match (Miri.Interpreter.Step.step (annealStepHooksDropBinderSubtype v2PtrCoerceUnsizeSliceMir) ()
        (npStV2Unsize (.live (.immediate (.scalar (npPtrScalar npAid5 npBase5)))))).2 with
      | .ok _ => false
      | .error (.undefinedBehavior _) => false
      | .error _ => true) = true := by
  decide +kernel

/-- **`V2` `Unsize` Coercion Fidelity, Safe-Reference Validation, & Ill-Typed
Negative Controls (Stepped Through Unmodified Vendored `Step.step` + Trusted
Parity)**:
1. Valid positive cases (`*mut [u32; 3] -> *const [u32]`, `*mut -> *mut`,
   `&[u32; 3] -> &[u32]`, `&mut [u32; 3] -> &[u32]`, `&[u32; 3] -> *const [u32]`)
   all step cleanly to `.usizeVal 3` and agree with Trusted `evalUnsizeCoercion`;
2. Post-cast safe-reference validation (`validatePlace` ->
   `annealValidateSafeWideSliceRef`) catches BOTH a null `&[u32; 3] -> &[u32]`
   and a dangling `&[u32; 3] -> &[u32]` as `.ub`;
3. Ill-typed array-to-slice coercions — mutability upgrade
   (`*const [u32; 3] -> *mut [u32]`, `&[u32; 3] -> &mut [u32]`), element
   mismatch (`*const [u32; 3] -> *const [u8]`), raw-to-ref upgrade
   (`*const [u32; 3] -> &[u32]`), and 64-bit `usize` length overflow
   (`*const [u32; 2^64 + 3] -> *const [u32]`) — are ALL rejected cleanly
   (`StepError.invalidProgram`, never silently coerced), matching Trusted
   `evalUnsizeCoercion` / `unsizeArrayLen?`! -/
theorem lm_np_v2_unsize_fidelity_and_negative_witness :
    let okPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npPtrScalar npAid5 npBase5)))
    let nullPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npScalarUInt 0 8)))
    let tLocs : List LocalSlot := [.uninit, .init (.ptr ⟨5, 0⟩ 8), .uninit]
    -- Positive stepped witnesses
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeMutToConstMir) 8
      (mkNpUnsizeState npUnsizeMutToConstMir npRawMutArr3U32MirTy rawConstSliceU32MirTy okPtr)) =
      .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeMutToMutMir) 8
      (mkNpUnsizeState npUnsizeMutToMutMir npRawMutArr3U32MirTy npRawMutSliceU32MirTy okPtr)) =
      .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeRefConstMir) 8
      (mkNpUnsizeState npUnsizeRefConstMir npRefArr3U32MirTy npRefSliceU32MirTy okPtr npMachine5Live)) =
      .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeRefMutToConstMir) 8
      (mkNpUnsizeState npUnsizeRefMutToConstMir npRefMutArr3U32MirTy npRefSliceU32MirTy okPtr npMachine5Live)) =
      .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeRefToRawMir) 8
      (mkNpUnsizeState npUnsizeRefToRawMir npRefArr3U32MirTy rawConstSliceU32MirTy okPtr)) =
      .usizeVal 3 ∧
    -- Safe-reference post-cast UB controls (null and dangling)
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeRefConstMir) 8
      (mkNpUnsizeState npUnsizeRefConstMir npRefArr3U32MirTy npRefSliceU32MirTy nullPtr npMachine5Live)) =
      .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeRefConstMir) 8
      (mkNpUnsizeState npUnsizeRefConstMir npRefArr3U32MirTy npRefSliceU32MirTy okPtr npMachine5)) =
      .ub ∧
    -- Rejected ill-typed array-to-slice coercions (mutability, element, overflow, raw-to-ref)
    npIsInvalidProgErr (runMiriSteps (annealStepHooksNullaryPtr npUnsizeBadMutUpgradeMir) 8
      (mkNpUnsizeState npUnsizeBadMutUpgradeMir npRawConstArr3U32MirTy npRawMutSliceU32MirTy okPtr)) =
      true ∧
    npIsInvalidProgErr (runMiriSteps (annealStepHooksNullaryPtr npUnsizeBadElemMismatchMir) 8
      (mkNpUnsizeState npUnsizeBadElemMismatchMir npRawConstArr3U32MirTy npRawConstSliceU8MirTy okPtr)) =
      true ∧
    npIsInvalidProgErr (runMiriSteps (annealStepHooksNullaryPtr npUnsizeBadLenOverflowMir) 8
      (mkNpUnsizeState npUnsizeBadLenOverflowMir npRawConstArrOverflowU32MirTy rawConstSliceU32MirTy okPtr)) =
      true ∧
    npIsInvalidProgErr (runMiriSteps (annealStepHooksNullaryPtr npUnsizeBadRawToRefMir) 8
      (mkNpUnsizeState npUnsizeBadRawToRefMir npRawConstArr3U32MirTy npRefSliceU32MirTy okPtr npMachine5Live)) =
      true ∧
    npIsInvalidProgErr (runMiriSteps (annealStepHooksNullaryPtr npUnsizeBadRefMutUpgradeMir) 8
      (mkNpUnsizeState npUnsizeBadRefMutUpgradeMir npRefArr3U32MirTy npRefMutSliceU32MirTy okPtr npMachine5Live)) =
      true ∧
    -- Trusted-side parity
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) rawConstSliceU32MirTy emptyMemory
      npUnsizeMutToConstMir.localDecls emptyLayoutTable =
      .ok (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨3, 8⟩]) tLocs emptyMemory ∧
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) npRefSliceU32MirTy emptyMemory
      npUnsizeRefConstMir.localDecls emptyLayoutTable =
      .ok (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨3, 8⟩]) tLocs emptyMemory ∧
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) npRawMutSliceU32MirTy emptyMemory
      npUnsizeBadMutUpgradeMir.localDecls emptyLayoutTable = .ub ∧
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) npRawConstSliceU8MirTy emptyMemory
      npUnsizeBadElemMismatchMir.localDecls emptyLayoutTable = .ub ∧
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) npRefSliceU32MirTy emptyMemory
      npUnsizeBadRawToRefMir.localDecls emptyLayoutTable = .ub ∧
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) npRefMutSliceU32MirTy emptyMemory
      npUnsizeBadRefMutUpgradeMir.localDecls emptyLayoutTable = .ub ∧
    unsizeArrayLen? "Unsize" (some npRawConstArrOverflowU32MirTy) (.rawPtr .not (.slice (.uint .u32))) =
      none ∧
    npIllTypedUnsizeAccepted = false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl⟩

/-- **Universal Tree Borrows Permission Correspondence on `Unsize`**: across
ALL 6 `TreeBorrowPerm` states (`.cell`, `.reservedFrz false`, `.reservedFrz true`,
`.reservedIM`, `.unique`, `.frozen`, `.disabled`) and BOTH target mutabilities
(`*const [u32]` vs. `*mut [u32]`), `npUnsizeTreeBorrowsPermCheck` on the 12-byte
vendored `BorrowTree` (`npArr3U32Tree perm`) agrees identically with Trusted
`unsizeBorrowPermCompatible`. -/
theorem npUnsizeTreeBorrowsPermCheck_eq_trusted_universal (perm : TreeBorrowPerm)
    (isMutTarget : Bool) :
    (npUnsizeTreeBorrowsPermCheck (npArr3U32Tree perm) retagChildTag 0 12 isMutTarget).isOk =
      unsizeBorrowPermCompatible
        [{ tag := 5, targetLocal := 3, targetProjection := [], perm := perm,
           targetFrameDepth := 0 }]
        5 (if isMutTarget then .rawPtr .mut (.slice (.uint .u32))
           else .rawPtr .not (.slice (.uint .u32))) := by
  cases perm with
  | reservedFrz b => cases b <;> cases isMutTarget <;> decide +kernel
  | _ => cases isMutTarget <;> decide +kernel

/-- **`V2` `Unsize` Tree Borrows Permission Agreement, Mode Sensitivity, &
`unsizeArrayToSliceSpec?` Overflow Boundary**:
1. Exact `unsizeArrayToSliceSpec?` vs. `unsizeArrayLen?` / `npUnsizeArraySpec?`
   64-bit length overflow boundary (`n = 2^64 + 3` is accepted by
   `unsizeArrayToSliceSpec?` but rejected by `unsizeArrayLen?` and
   `npUnsizeArraySpec?` to prevent `UInt64.ofNat` truncation);
2. Trusted `evalUnsizeCoercion` rejects `.disabled -> *const [u32]`,
   `.frozen -> *mut [u32]`, and `.frozen -> &mut [u32]` with `.ub`, and accepts
   `.frozen -> *const [u32]` and `.unique -> *mut [u32]` over a live 3-element
   `[u32; 3]` backing array;
3. Stepped through unmodified vendored `Miri.Interpreter.Step.step` over live
   `BorrowTree` allocations (`npMachine5Tree`), `annealStepHooksNullaryPtr` in
   `treeBorrows = true` mode achieves **2-way UB agreement** with Trusted on
   `.disabled -> *const [u32]`, `.frozen -> *mut [u32]`, and
   `.frozen -> &mut [u32]`, and **2-way positive agreement** (`3`) on
   `.frozen -> *const [u32]`, `.unique -> *mut [u32]`, `.unique -> &mut [u32]`,
   and a tag (`⟨999⟩`) that is not registered in the borrow tree (Trusted accepts
   a pointer whose tag has no `BorrowEntry`);
4. Genuine `treeBorrows = false` vs. `true` mode sensitivity on `Unsize`: in
   basic mode (`treeBorrows = false`), `.disabled -> *const [u32]`,
   `.frozen -> *mut [u32]`, and `.frozen -> &mut [u32]` all return `.usizeVal 3`,
   while `treeBorrows = true` faults `.ub`. -/
theorem lm_np_v2_unsize_tb_perm_agreement_and_mode_sensitivity_witness :
    let eDisabled : BorrowEntry :=
      { tag := 5, targetLocal := 3, targetProjection := [], perm := .disabled,
        targetFrameDepth := 0 }
    let eFrozen : BorrowEntry :=
      { tag := 5, targetLocal := 3, targetProjection := [], perm := .frozen,
        targetFrameDepth := 0 }
    let eUnique : BorrowEntry :=
      { tag := 5, targetLocal := 3, targetProjection := [], perm := .unique,
        targetFrameDepth := 0 }
    let tLocs : List LocalSlot :=
      [.uninit, .init (.ptr ⟨5, 0⟩ 8), .uninit,
       .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩])]
    let childPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npPtrScalarTagged npAid5 npBase5 retagChildTag)))
    let unregTag : Miri.Memory.BorTag := ⟨999, by decide⟩
    let unregPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npPtrScalarTagged npAid5 npBase5 unregTag)))
    -- 1. Trusted `unsizeArrayToSliceSpec?` vs `unsizeArrayLen?` / `npUnsizeArraySpec?` overflow boundary
    unsizeArrayToSliceSpec? npRawConstArrOverflowU32MirTy.kind (.rawPtr .not (.slice (.uint .u32))) =
      some (scalarModulus 8 + 3) ∧
    npUnsizeArraySpec? "Unsize" (some npRawConstArrOverflowU32MirTy) (.rawPtr .not (.slice (.uint .u32))) =
      none ∧
    unsizeBorrowPermCompatible [eDisabled] 5 (.rawPtr .not (.slice (.uint .u32))) = false ∧
    unsizeBorrowPermCompatible [eFrozen] 5 (.rawPtr .mut (.slice (.uint .u32))) = false ∧
    unsizeBorrowPermCompatible [eFrozen] 5 (.ref .mut (.slice (.uint .u32))) = false ∧
    unsizeBorrowPermCompatible [eFrozen] 5 (.rawPtr .not (.slice (.uint .u32))) = true ∧
    unsizeBorrowPermCompatible [eUnique] 5 (.rawPtr .mut (.slice (.uint .u32))) = true ∧
    -- 2. Trusted `evalUnsizeCoercion` (live backing array in local 3)
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) rawConstSliceU32MirTy
      { emptyMemory with borrows := [eDisabled] } npUnsizeMutToConstMir.localDecls
      emptyLayoutTable = .ub ∧
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) npRawMutSliceU32MirTy
      { emptyMemory with borrows := [eFrozen] } npUnsizeMutToMutMir.localDecls
      emptyLayoutTable = .ub ∧
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) npRefMutSliceU32MirTy
      { emptyMemory with borrows := [eFrozen] } npUnsizeRefMutToMutMir.localDecls
      emptyLayoutTable = .ub ∧
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) rawConstSliceU32MirTy
      { emptyMemory with borrows := [eFrozen] } npUnsizeMutToConstMir.localDecls
      emptyLayoutTable =
      .ok (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨3, 8⟩]) tLocs
        { emptyMemory with borrows := [eFrozen] } ∧
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) npRawMutSliceU32MirTy
      { emptyMemory with borrows := [eUnique] } npUnsizeMutToMutMir.localDecls
      emptyLayoutTable =
      .ok (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨3, 8⟩]) tLocs
        { emptyMemory with borrows := [eUnique] } ∧
    -- 3. LeanMiri `treeBorrows = true` 2-way UB agreement on live `BorrowTree` allocations
    (runMiriSteps (annealStepHooksNullaryPtr npUnsizeMutToConstMir true) 8
      (mkNpUnsizeState npUnsizeMutToConstMir npRawMutArr3U32MirTy rawConstSliceU32MirTy
        childPtr (npMachine5Tree .disabled))).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows disabled tag on Unsize pointer coercion") ∧
    (runMiriSteps (annealStepHooksNullaryPtr npUnsizeMutToMutMir true) 8
      (mkNpUnsizeState npUnsizeMutToMutMir npRawMutArr3U32MirTy npRawMutSliceU32MirTy
        childPtr (npMachine5Tree .frozen))).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows frozen tag on mutable Unsize pointer coercion") ∧
    (runMiriSteps (annealStepHooksNullaryPtr npUnsizeRefMutToMutMir true) 8
      (mkNpUnsizeState npUnsizeRefMutToMutMir npRefMutArr3U32MirTy npRefMutSliceU32MirTy
        childPtr (npMachine5Tree .frozen))).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows frozen tag on mutable Unsize pointer coercion") ∧
    -- 4. LeanMiri `treeBorrows = true` 2-way positive agreement
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeMutToConstMir true) 8
      (mkNpUnsizeState npUnsizeMutToConstMir npRawMutArr3U32MirTy rawConstSliceU32MirTy
        unregPtr (npMachine5Tree .unique))) = .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeMutToConstMir true) 8
      (mkNpUnsizeState npUnsizeMutToConstMir npRawMutArr3U32MirTy rawConstSliceU32MirTy
        childPtr (npMachine5Tree .frozen))) = .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeMutToMutMir true) 8
      (mkNpUnsizeState npUnsizeMutToMutMir npRawMutArr3U32MirTy npRawMutSliceU32MirTy
        childPtr (npMachine5Tree .unique))) = .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeRefMutToMutMir true) 8
      (mkNpUnsizeState npUnsizeRefMutToMutMir npRefMutArr3U32MirTy npRefMutSliceU32MirTy
        childPtr (npMachine5Tree .unique))) = .usizeVal 3 ∧
    -- 5. Genuine `treeBorrows = false` vs. `true` mode sensitivity on `Unsize`
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeMutToConstMir false) 8
      (mkNpUnsizeState npUnsizeMutToConstMir npRawMutArr3U32MirTy rawConstSliceU32MirTy
        childPtr (npMachine5Tree .disabled))) = .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeMutToMutMir false) 8
      (mkNpUnsizeState npUnsizeMutToMutMir npRawMutArr3U32MirTy npRawMutSliceU32MirTy
        childPtr (npMachine5Tree .frozen))) = .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeRefMutToMutMir false) 8
      (mkNpUnsizeState npUnsizeRefMutToMutMir npRefMutArr3U32MirTy npRefMutSliceU32MirTy
        childPtr (npMachine5Tree .frozen))) = .usizeVal 3 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Zero-Length `Unsize` Tree Borrows Permission Correspondence**: for a
zero-length coercion (`spanBytes = 0`) of a pointer in the interior (offset `4`)
and one past the end (offset `12`) of the 12-byte tracked range, across ALL
`TreeBorrowPerm` states and BOTH target mutabilities,
`npUnsizeTreeBorrowsPermCheck` agrees with Trusted `unsizeBorrowPermCompatible`
(whose verdict does not depend on the slice length). -/
theorem npUnsizeTreeBorrowsPermCheck_zero_len_eq_trusted_universal (perm : TreeBorrowPerm)
    (isMutTarget : Bool) :
    (npUnsizeTreeBorrowsPermCheck (npArr3U32Tree perm) retagChildTag 4 0 isMutTarget).isOk =
      unsizeBorrowPermCompatible
        [{ tag := 5, targetLocal := 3, targetProjection := [], perm := perm,
           targetFrameDepth := 0 }]
        5 (if isMutTarget then .rawPtr .mut (.slice (.uint .u32))
           else .rawPtr .not (.slice (.uint .u32))) ∧
    (npUnsizeTreeBorrowsPermCheck (npArr3U32Tree perm) retagChildTag 12 0 isMutTarget).isOk =
      unsizeBorrowPermCompatible
        [{ tag := 5, targetLocal := 3, targetProjection := [], perm := perm,
           targetFrameDepth := 0 }]
        5 (if isMutTarget then .rawPtr .mut (.slice (.uint .u32))
           else .rawPtr .not (.slice (.uint .u32))) := by
  cases perm with
  | reservedFrz b => cases b <;> cases isMutTarget <;> decide +kernel
  | _ => cases isMutTarget <;> decide +kernel

@[reducible] private def npRawMutArr0U32MirTy : Ty :=
  { kind := .rawPtr .mut (.array (.uint .u32) 0), layoutIdx := 0 }

private def npUnsizeZeroLenMir : CapturedMir :=
  mkNpUnsizeMir "np::w_unsize_zero_len" npRawMutArr0U32MirTy rawConstSliceU32MirTy

/-- **`V2` `Unsize` Tree Borrows Permission Edge Cases (pure check vs. Trusted)**:
1. a tag that is not registered in the borrow tree passes the check, and Trusted
   accepts the same coercion when the pointer's tag has no `BorrowEntry` (here
   the only entry is a `.disabled` borrow under a different tag);
2. a zero-length coercion of a pointer one past the end of the tracked range
   through a `.disabled` tag is rejected by the check and by Trusted
   `evalUnsizeCoercion` on `*mut [u32; 0] -> *const [u32]`;
3. a provenance-free integer pointer (`4096`) is accepted by Trusted for a raw
   slice target whatever the borrow table holds (the check never runs for a
   pointer without concrete provenance, `npCheckUnsizeTreeBorrowsPerm`);
4. residual boundary: on a tracked allocation of size zero the check passes
   even for a tree whose only child permission is `.disabled`, because a
   zero-sized allocation has no location states; Trusted's permission is per
   borrow entry and still rejects (conjunct 2 does not depend on the size of
   the borrowed local). -/
theorem lm_np_v2_unsize_tb_perm_edge_cases_witness :
    let eDisabled5 : BorrowEntry :=
      { tag := 5, targetLocal := 3, targetProjection := [], perm := .disabled,
        targetFrameDepth := 0 }
    let eDisabled6 : BorrowEntry :=
      { tag := 6, targetLocal := 3, targetProjection := [], perm := .disabled,
        targetFrameDepth := 0 }
    let unregTag : Miri.Memory.BorTag := ⟨999, by decide⟩
    let arr : LocalSlot :=
      .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩])
    let tLocs : List LocalSlot := [.uninit, .init (.ptr ⟨5, 0⟩ 8), .uninit, arr]
    let tLocsEnd : List LocalSlot := [.uninit, .init (.ptr ⟨5, 12⟩ 8), .uninit, arr]
    let tLocsInt : List LocalSlot := [.uninit, .init (.scalar ⟨4096, 8⟩), .uninit, arr]
    -- 1. Unregistered tag
    (npUnsizeTreeBorrowsPermCheck (npArr3U32Tree .disabled) unregTag 0 12 true).isOk = true ∧
    unsizeBorrowPermCompatible [eDisabled6] 5 (.rawPtr .mut (.slice (.uint .u32))) = true ∧
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) rawConstSliceU32MirTy
      { emptyMemory with borrows := [eDisabled6] } npUnsizeMutToConstMir.localDecls
      emptyLayoutTable =
      .ok (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨3, 8⟩]) tLocs
        { emptyMemory with borrows := [eDisabled6] } ∧
    -- 2. Zero-length coercion one past the end through a `.disabled` tag
    (npUnsizeTreeBorrowsPermCheck (npArr3U32Tree .disabled) retagChildTag 12 0 false).isOk =
      false ∧
    evalUnsizeCoercion tLocsEnd (.copy (locPlace 1)) rawConstSliceU32MirTy
      { emptyMemory with borrows := [eDisabled5] } npUnsizeZeroLenMir.localDecls
      emptyLayoutTable = .ub ∧
    -- 3. Provenance-free integer pointer
    evalUnsizeCoercion tLocsInt (.copy (locPlace 1)) rawConstSliceU32MirTy
      { emptyMemory with borrows := [eDisabled5] } npUnsizeMutToConstMir.localDecls
      emptyLayoutTable =
      .ok
        (.aggregate 0 [.scalar ⟨wrapScalarBits 4096 (scalarModulus 8), 8⟩, .scalar ⟨3, 8⟩])
        tLocsInt { emptyMemory with borrows := [eDisabled5] } ∧
    -- 4. Zero-sized tracked allocation (residual boundary)
    (npUnsizeTreeBorrowsPermCheck
      { hooksTwoNodeTree .disabled with
        locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 0)
          (hooksLocTree .disabled) }
      retagChildTag 0 0 false).isOk = true := by
  refine ⟨by decide +kernel, rfl, rfl, by decide +kernel, rfl, rfl, by decide +kernel⟩

/-- **`V2` `Unsize` Tree Borrows Edge Cases, Stepped** through unmodified vendored
`Miri.Interpreter.Step.step` under `annealStepHooksNullaryPtr`:
1. in `treeBorrows = true` mode a provenance-free integer pointer
   (`0x1000 as *mut [u32; 3] as *const [u32]`) is unsized to length `3` even
   though the machine's tracked allocation has a `.disabled` child tag (the
   pointer carries no tag to check);
2. a zero-length `*mut [u32; 0] -> *const [u32]` coercion of a pointer one past
   the end of the 12-byte allocation is UB in `treeBorrows = true` mode through
   a `.disabled` tag, returns length `0` through a `.unique` tag, and returns
   length `0` in basic mode. -/
theorem lm_np_v2_unsize_tb_edge_cases_stepped_witness :
    let intPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npScalarUInt 0x1000 8)))
    let endPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npPtrScalarTagged npAid5 (npBase5 + 12) retagChildTag)))
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeMutToConstMir true) 8
      (mkNpUnsizeState npUnsizeMutToConstMir npRawMutArr3U32MirTy rawConstSliceU32MirTy
        intPtr (npMachine5Tree .disabled))) = .usizeVal 3 ∧
    (runMiriSteps (annealStepHooksNullaryPtr npUnsizeZeroLenMir true) 8
      (mkNpUnsizeState npUnsizeZeroLenMir npRawMutArr0U32MirTy rawConstSliceU32MirTy
        endPtr (npMachine5Tree .disabled))).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows disabled tag on Unsize pointer coercion") ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeZeroLenMir true) 8
      (mkNpUnsizeState npUnsizeZeroLenMir npRawMutArr0U32MirTy rawConstSliceU32MirTy
        endPtr (npMachine5Tree .unique))) = .usizeVal 0 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeZeroLenMir false) 8
      (mkNpUnsizeState npUnsizeZeroLenMir npRawMutArr0U32MirTy rawConstSliceU32MirTy
        endPtr (npMachine5Tree .disabled))) = .usizeVal 0 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **`V2` `Unsize` Zero-Size Vendored `BorrowTree` Representation Boundary &
Strict OOB Offset Boundary (`np_vendored_borrowTree_zero_size_and_oob_boundary`)**:
1. **Zero-size tracked allocation representation**: in vendored
   `Miri.TreeBorrows.BorrowTree.new retagParentTag Size.ZERO`, `locations.entries`
   is empty (`#[]`) and the live root node STILL carries
   `defaultInitialPermission = .Disabled` (representing out-of-bounds default
   permissions). Hence `npUnsizeTreeBorrowsPermCheck` MUST NOT fall back to
   `defaultInitialPermission` when `locations.entries` is empty (doing so would
   falsely reject the valid root tag of every zero-sized allocation!), and
   accepts the live root tag cleanly.
2. **Strictly out-of-bounds offset (`startNat = 20 > trackedEnd = 12`)**:
   clamping in `npUnsizeTreeBorrowsPermCheck` is restricted strictly to exact
   one-past-the-end (`startNat = trackedEnd`), so an OOB zero-length raw pointer
   at offset `20` is NOT over-clamped to byte `11` (passing `npUnsizeTreeBorrowsPermCheck`
   and stepping to `.usizeVal 0` in LeanMiri), while Trusted `evalUnsizeCoercion`
   rejects offset `20` as `.ub` in `stackTargetValid` for BOTH `.disabled` and
   `.unique` tags (strict fail-closed direction). -/
theorem np_vendored_borrowTree_zero_size_and_oob_boundary :
    let zTree := Miri.TreeBorrows.BorrowTree.new retagParentTag Miri.ABI.Size.ZERO
    let eDisabled5 : BorrowEntry :=
      { tag := 5, targetLocal := 3, targetProjection := [], perm := .disabled,
        targetFrameDepth := 0 }
    let eUnique5 : BorrowEntry :=
      { tag := 5, targetLocal := 3, targetProjection := [], perm := .unique,
        targetFrameDepth := 0 }
    let arr : LocalSlot :=
      .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩])
    let tLocsOob : List LocalSlot := [.uninit, .init (.ptr ⟨5, 20⟩ 8), .uninit, arr]
    let oobPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npPtrScalarTagged npAid5 (npBase5 + 20) retagChildTag)))
    -- 1. Vendored `BorrowTree.new _ Size.ZERO` structure & live root tag acceptance
    zTree.locations.entries.isEmpty = true ∧
    (zTree.nodes.get ⟨0⟩).map (·.defaultInitialPermission) = some .Disabled ∧
    (npUnsizeTreeBorrowsPermCheck zTree retagParentTag 0 0 true).isOk = true ∧
    -- 2. Strict OOB (`20 > 12`) not over-clamped to byte `11` vs. Trusted fail-closed UB
    (npUnsizeTreeBorrowsPermCheck (npArr3U32Tree .disabled) retagChildTag 20 0 false).isOk = true ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeZeroLenMir true) 8
      (mkNpUnsizeState npUnsizeZeroLenMir npRawMutArr0U32MirTy rawConstSliceU32MirTy
        oobPtr (npMachine5Tree .disabled))) = .usizeVal 0 ∧
    evalUnsizeCoercion tLocsOob (.copy (locPlace 1)) rawConstSliceU32MirTy
      { emptyMemory with borrows := [eDisabled5] } npUnsizeZeroLenMir.localDecls
      emptyLayoutTable = .ub ∧
    evalUnsizeCoercion tLocsOob (.copy (locPlace 1)) rawConstSliceU32MirTy
      { emptyMemory with borrows := [eUnique5] } npUnsizeZeroLenMir.localDecls
      emptyLayoutTable = .ub := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, rfl, rfl⟩

/-- **`V2` Stepped `ReservedIM` & `Cell` `Unsize` Parity Witness (LeanMiri +
Trusted)**: completes stepped execution coverage for the two interior-mutable
Tree Borrows permissions (`.reservedIM` and `.cell`) across BOTH `*mut [u32; 3]
-> *const [u32]` and `*mut [u32; 3] -> *mut [u32]` in `treeBorrows = true` mode,
agreeing with Trusted `evalUnsizeCoercion` (`.usizeVal 3` / `[ptr, 3]`). -/
theorem lm_np_v2_unsize_reservedIM_cell_stepped_witness :
    let taggedPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npPtrScalarTagged npAid5 npBase5 retagChildTag)))
    let arr : LocalSlot :=
      .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩])
    let tLocs : List LocalSlot := [.uninit, .init (.ptr ⟨5, 0⟩ 8), .uninit, arr]
    let eRim : BorrowEntry :=
      { tag := 5, targetLocal := 3, targetProjection := [], perm := .reservedIM,
        targetFrameDepth := 0 }
    let eCell : BorrowEntry :=
      { tag := 5, targetLocal := 3, targetProjection := [], perm := .cell,
        targetFrameDepth := 0 }
    -- 1. LeanMiri stepped `treeBorrows = true` under `.reservedIM` and `.cell`
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeMutToConstMir true) 8
      (mkNpUnsizeState npUnsizeMutToConstMir npRawMutArr3U32MirTy rawConstSliceU32MirTy
        taggedPtr (npMachine5Tree .reservedIM))) = .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeMutToMutMir true) 8
      (mkNpUnsizeState npUnsizeMutToMutMir npRawMutArr3U32MirTy npRawMutSliceU32MirTy
        taggedPtr (npMachine5Tree .reservedIM))) = .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeMutToConstMir true) 8
      (mkNpUnsizeState npUnsizeMutToConstMir npRawMutArr3U32MirTy rawConstSliceU32MirTy
        taggedPtr (npMachine5Tree .cell))) = .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npUnsizeMutToMutMir true) 8
      (mkNpUnsizeState npUnsizeMutToMutMir npRawMutArr3U32MirTy npRawMutSliceU32MirTy
        taggedPtr (npMachine5Tree .cell))) = .usizeVal 3 ∧
    -- 2. Trusted `evalUnsizeCoercion` parity
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) rawConstSliceU32MirTy
      { emptyMemory with borrows := [eRim] } npUnsizeMutToConstMir.localDecls emptyLayoutTable =
      .ok (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨3, 8⟩]) tLocs
        { emptyMemory with borrows := [eRim] } ∧
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) npRawMutSliceU32MirTy
      { emptyMemory with borrows := [eRim] } npUnsizeMutToMutMir.localDecls emptyLayoutTable =
      .ok (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨3, 8⟩]) tLocs
        { emptyMemory with borrows := [eRim] } ∧
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) rawConstSliceU32MirTy
      { emptyMemory with borrows := [eCell] } npUnsizeMutToConstMir.localDecls emptyLayoutTable =
      .ok (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨3, 8⟩]) tLocs
        { emptyMemory with borrows := [eCell] } ∧
    evalUnsizeCoercion tLocs (.copy (locPlace 1)) npRawMutSliceU32MirTy
      { emptyMemory with borrows := [eCell] } npUnsizeMutToMutMir.localDecls emptyLayoutTable =
      .ok (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨3, 8⟩]) tLocs
        { emptyMemory with borrows := [eCell] } := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          rfl, rfl, rfl, rfl⟩

private def npMutToConstSliceMir : CapturedMir :=
  mkMirBody "np::w_mut_to_const_slice"
    [mkDecl usizeMirTy, mkDecl npRawMutSliceU32MirTy, mkDecl rawConstSliceU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 2)
             (.cast (.pointerCoercion "MutToConstPointer") (.copy (locPlace 1))
               rawConstSliceU32MirTy)),
           mkSt (.assign (locPlace 0) (.unaryOp .ptrMetadata (.copy (locPlace 2))))]
      .return_]

private def npStMutToConstSlice (src : Miri.Interpreter.LocalValue AnnealProv) :
    AnnealStepState :=
  npMkState npMutToConstSliceMir usizeMirTy
    #[npUninit (translateTyOverlay usizeMirTy emptyLayoutTable),
      ⟨src, some (translateTyOverlay npRawMutSliceU32MirTy emptyLayoutTable)⟩,
      npUninit (translateTyOverlay rawConstSliceU32MirTy emptyLayoutTable)]
    npMachine5

/-- **`V2` Wide-Slice `MutToConstPointer` (`*mut [u32] -> *const [u32]`) Witness**,
completing the three `MutToConstPointer` shapes (thin and wide `dyn Trait` are
covered by `lm_np_v2_pointerCoercion_six_subkinds_witness`):
1. one vendored `Miri.Interpreter.Step.step` copies BOTH the data pointer
   (allocation `5`) and the slice length metadata (`3`) into the destination;
2. the full run then reads the length back with `PtrMetadata` (`3`), in basic
   and in `treeBorrows = true` mode;
3. a dead source local is UB;
4. Trusted `evalRvalue` returns the same wide pointer `(⟨5, 0⟩, 3)` unchanged. -/
theorem lm_np_v2_mutToConstPointer_wide_slice_witness :
    let widePtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalarPair (npPtrScalar npAid5 npBase5) (npScalarUInt 3 8)))
    let tLocs : List LocalSlot :=
      [.uninit, .init (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨3, 8⟩]), .uninit]
    (match Miri.Interpreter.Step.step (annealStepHooksNullaryPtr npMutToConstSliceMir) ()
        (npStMutToConstSlice widePtr) with
      | (st', .ok true) =>
        (match npLocalVal? st' 2 with
          | some (.live (.immediate (.scalarPair a b))) =>
            decide (npDecodeScalar a = .ptrAlloc 5) && decide (npDecodeScalar b = .usizeVal 3)
          | _ => false)
      | _ => false) = true ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npMutToConstSliceMir) 8
      (npStMutToConstSlice widePtr)) = .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npMutToConstSliceMir true) 8
      (npStMutToConstSlice widePtr)) = .usizeVal 3 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npMutToConstSliceMir) 8
      (npStMutToConstSlice .dead)) = .ub ∧
    evalRvalue tLocs
      (.cast (.pointerCoercion "MutToConstPointer") (.copy (locPlace 1)) rawConstSliceU32MirTy)
      emptyMemory npMutToConstSliceMir.localDecls emptyLayoutTable =
      .ok (.aggregate 0 [.ptr ⟨5, 0⟩ 8, .scalar ⟨3, 8⟩]) tLocs emptyMemory := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩

/-- **`V3` (`CastKind.fnPtrToPtr`) UB & Divergence Witness** on `v3FnPtrToPtrConstMir`:
1. a function pointer at a nonzero offset into its function allocation is UB;
2. a pointer into a non-function (stack) allocation carrying a borrow tag is UB;
3. a dangling integer address is UB;
4. the `rust-intrinsic` ABI divergence: LeanMiri accepts the cast and returns the
   function allocation;
5. a non-function-pointer (`*mut u32`) source is never reported as undefined
   behavior by LeanMiri (vendored `Cast.cast` shares the `FnPtrToPtr` / `PtrToPtr`
   arm). -/
theorem lm_np_v3_fnPtrToPtr_ub_and_divergence_witness :
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v3FnPtrToPtrConstMir) 8
      (npStV3Const (.live (.immediate (.scalar (npPtrScalar npFnAid (npFnBase + 4))))))) = .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v3FnPtrToPtrConstMir) 8
      (npStV3Const (.live (.immediate (.scalar (npPtrScalarTagged npAid5 npBase5 retagChildTag))))
        npMachine5)) = .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v3FnPtrToPtrConstMir) 8
      (npStV3Const (.live (.immediate (.scalar (npScalarUInt 0x2000 8)))))) = .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npFnPtrToPtrIntrMir (fnPtrs := npIntrFnPtrs)) 8
      npStFnPtrToPtrIntr) = .ptrAlloc 65536 ∧
    (match runMiriSteps (annealStepHooksNullaryPtr npFnPtrToPtrRawSrcMir) 8 npStFnPtrToPtrRawSrc with
      | .error (.undefinedBehavior _) => false
      | _ => true) = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel⟩

/-- **`V4` Tree Borrows bridge**: on the EXACT tree of `mkNpTbUnwrapState`
(`npU32ChildTree`, `[0, 4)`), a write through the root tag `retagParentTag`
conflicts iff the child is protected; and on `hooksTwoNodeTree .unique` (`[0, 8)`)
unmodified vendored `BorrowTree.performBorrowAccessRange` (`.Write`) completes iff
the child is unprotected (`ep2ProtectorConflict_agrees_with_vendored_tree_borrows`). -/
theorem np_unwrap_write_tb_conflict_bridges_vendored (isProtected : Bool) :
    ep2ProtectorConflict (hooksForChildProtected isProtected).protectedTags
        npU32ChildTree retagParentTag Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4) = isProtected ∧
    (((hooksTwoNodeTree .unique).performBorrowAccessRange (.concrete retagParentTag)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) .Write
        (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed).status = .Completed ↔
      isProtected = false) :=
  ⟨by cases isProtected <;> decide +kernel,
   (ep2ProtectorConflict_agrees_with_vendored_tree_borrows isProtected).2.1⟩

/-- **`V4` (`ProjectionElem.unwrapUnsafeBinder`) Witness**:
1. wrap -> write-through-unwrap (`73`) -> read-through-unwrap round-trip returns `73`
   in both modes;
2. `BinderNonZeroU8` wrap of `7` reads back `7`, while wrapping `0` is UB (validity
   range of the binder);
3. reading through `unwrapUnsafeBinder` of a dead local is UB;
4. data-driven Tree Borrows mode sensitivity on a memory-backed `_1` whose
   allocation's vendored borrow tree has a `Unique` child: with `treeBorrows = false`
   the write-through-unwrap returns `42` even when the child is protected; with
   `treeBorrows = true` it is UB iff the child is protected (unprotected control
   returns `42`);
5. persistence: after the unprotected `treeBorrows = true` run, the allocation's
   persisted borrow tree rejects a write through the (now disabled) child tag,
   whereas the initial tree accepted it. -/
theorem lm_np_v4_unwrapUnsafeBinder_witness :
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v4UnwrapBinderRoundtripMir false) 8
      npStV4Roundtrip) = .u32Val 73 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v4UnwrapBinderRoundtripMir true) 8
      npStV4Roundtrip) = .u32Val 73 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v4UnwrapBinderNzU8Mir) 8 (npStV4NzU8 7)) =
      .u8Val 7 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v4UnwrapBinderNzU8Mir) 8 (npStV4NzU8 0)) = .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v4UnwrapBinderDeadUbMir) 8 npStV4DeadUb) = .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v4UnwrapBinderProtectedMir false) 8
      (mkNpTbUnwrapState v4UnwrapBinderProtectedMir true)) = .u32Val 42 ∧
    (runMiriSteps (annealStepHooksNullaryPtr v4UnwrapBinderProtectedMir true) 8
      (mkNpTbUnwrapState v4UnwrapBinderProtectedMir true)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v4UnwrapBinderProtectedMir true) 8
      (mkNpTbUnwrapState v4UnwrapBinderProtectedMir false)) = .u32Val 42 ∧
    ep2ProtectorConflict {} npU32ChildTree retagChildTag Miri.ABI.Size.ZERO
      (Miri.ABI.Size.ofBytes 4) = false ∧
    (match runMiriSteps (annealStepHooksNullaryPtr v4UnwrapBinderProtectedMir true) 8
        (mkNpTbUnwrapState v4UnwrapBinderProtectedMir false) with
      | .ok (st, _) =>
        (match st.machine.memory.live[0]? with
          | some (_, la) =>
            match la.allocation.extra with
            | some t => ep2ProtectorConflict {} t retagChildTag Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4)
            | none => false
          | none => false)
      | _ => false) = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel⟩

/-- **`V4` Deref & Projected Sub-Place `UnwrapUnsafeBinder` Tree Borrows Witness**:
1. **`(*_1).unwrapUnsafeBinder`** (`npV4DerefUnwrapProtectedMir`) where `_1 : *mut u32`
   is an **immediate** pointer scalar pointing to memory-backed `npAid1` carrying
   `npU32ChildTree`: `treeBorrows = false` returns `42` even when the child is
   protected; `treeBorrows = true` rejects the protected child with a Tree Borrows
   write conflict, accepts the unprotected child (`42`), and persists the disabled
   child permission in `npAid1`'s borrow tree;
2. **`*(_1.unwrapUnsafeBinder)`** (`npV4UnwrapDerefProtectedMir`): likewise enforces
   the protector on `npAid1` when `treeBorrows = true` and returns `42` when
   unprotected;
3. **Projected sub-place `(_1.unwrapUnsafeBinder).field(1)`** (`npV4FieldUnwrapMir`)
   on an 8-byte memory-backed `np::PaddedU8U32` carrying 8-byte
   `hooksTwoNodeTree .unique`: rejects a protected child, and when unprotected
   returns `42` while transitioning ONLY `[4, 8)` (disabling `retagChildTag` on
   field 1 while preserving `retagChildTag`'s `Unique` permission on untouched
   sibling bytes `[0, 4)`!). -/
theorem lm_np_v4_deref_and_subplace_unwrap_tb_witness :
    -- 1. (*_1).unwrapUnsafeBinder with immediate pointer local _1
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4DerefUnwrapProtectedMir false) 8
      (mkNpTbDerefUnwrapState npV4DerefUnwrapProtectedMir true)) = .u32Val 42 ∧
    (runMiriSteps (annealStepHooksNullaryPtr npV4DerefUnwrapProtectedMir true) 8
      (mkNpTbDerefUnwrapState npV4DerefUnwrapProtectedMir true)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4DerefUnwrapProtectedMir true) 8
      (mkNpTbDerefUnwrapState npV4DerefUnwrapProtectedMir false)) = .u32Val 42 ∧
    (match runMiriSteps (annealStepHooksNullaryPtr npV4DerefUnwrapProtectedMir true) 8
        (mkNpTbDerefUnwrapState npV4DerefUnwrapProtectedMir false) with
      | .ok (st, _) =>
        (match st.machine.memory.live[0]? with
          | some (_, la) =>
            match la.allocation.extra with
            | some t => ep2ProtectorConflict {} t retagChildTag Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4)
            | none => false
          | none => false)
      | _ => false) = true ∧
    -- 2. *(_1.unwrapUnsafeBinder) with immediate pointer local _1
    (runMiriSteps (annealStepHooksNullaryPtr npV4UnwrapDerefProtectedMir true) 8
      (mkNpTbDerefUnwrapState npV4UnwrapDerefProtectedMir true)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4UnwrapDerefProtectedMir true) 8
      (mkNpTbDerefUnwrapState npV4UnwrapDerefProtectedMir false)) = .u32Val 42 ∧
    -- 3. (_1.unwrapUnsafeBinder).field(1) sub-range precision ([4, 8) disabled, [0, 4) preserved)
    (runMiriSteps (annealStepHooksNullaryPtr npV4FieldUnwrapMir true) 8
      (mkNpTbFieldUnwrapState true)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4FieldUnwrapMir true) 8
      (mkNpTbFieldUnwrapState false)) = .u32Val 42 ∧
    (match runMiriSteps (annealStepHooksNullaryPtr npV4FieldUnwrapMir true) 8
        (mkNpTbFieldUnwrapState false) with
      | .ok (st, _) =>
        (match st.machine.memory.live[0]? with
          | some (_, la) =>
            match la.allocation.extra with
            | some t =>
              ep2ProtectorConflict {} t retagChildTag (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 4) &&
              !(ep2ProtectorConflict {} t retagChildTag Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4))
            | none => false
          | none => false)
      | _ => false) = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel⟩

private def npV4NestedFieldUnwrapMir : CapturedMir :=
  mkMirBody "np::w_v4_nested_field_unwrap"
    [mkDecl u32MirTy, mkDecl npPaddedMirTy] 1
    [mkBb [mkSt (.assign (locPlace 1 [.field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy])
             (.use (constU32 99))),
           mkSt (.assign (locPlace 0)
             (.use (.copy (locPlace 1 [.field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npLayouts

/-- Two-node borrow tree over 8 bytes in which the child tag `retagChildTag` has
an accessed `.Unique` location state on only one 4-byte half (`[0, 4)` when
`childOnFst = true`, `[4, 8)` otherwise) and no location state on the other
half (it never accessed those bytes). -/
private def npSplitChildTree (childOnFst : Bool) : Miri.TreeBorrows.BorrowTree :=
  let rootOnly : Miri.TreeBorrows.LocationTree :=
    { perms := ⟨#[some ⟨.Unique, true, .None⟩, none]⟩
      exposedCache := {} }
  { hooksTwoNodeTree .unique with
    locations :=
      ⟨#[⟨⟨0, 4⟩, if childOnFst then hooksLocTree .unique else rootOnly⟩,
         ⟨⟨4, 8⟩, if childOnFst then rootOnly else hooksLocTree .unique⟩]⟩ }

private def mkNpTbNestedFieldUnwrapState
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (childProtected : Bool) : AnnealStepState :=
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with live := #[(npAid1, ⟨.stack, alloc⟩)] },
      addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨npAid1, npBase1⟩] },
      borrowTracker := some
        { global := { protectedTags := (hooksForChildProtected childProtected).protectedTags },
          retagMode := .Default } }
  let mp : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Miri.ABI.Size.ofBytes npBase1, some (.concrete npAid1 retagParentTag)⟩, .none, none⟩
  npMkState npV4NestedFieldUnwrapMir u32MirTy
    #[npUninit (translateTyOverlay u32MirTy npLayouts),
      ⟨.live (.indirect mp), some (translateTyOverlay npPaddedMirTy npLayouts)⟩]
    mach

/-- **`V4` Nested Projection `(_1.1).unwrapUnsafeBinder` & Sub-Range Tree Borrows
Disjointness** (`Field` then `UnwrapUnsafeBinder`, the reverse of the
`(_1.unwrapUnsafeBinder).field(1)` order of
`lm_np_v4_deref_and_subplace_unwrap_tb_witness`). The outer struct is the frozen
8-byte `np::PaddedU8U32` (`u8` at offset `0`, `u32` at offset `4`), memory-backed
at `npAid1`; the write `(_1.1).unwrapUnsafeBinder = 99` covers bytes `[4, 8)`:
1. basic mode returns `99`;
2. `treeBorrows = true`, protected child tag that accessed only `[0, 4)`: the
   write to the disjoint bytes `[4, 8)` is accepted and returns `99`;
3. `treeBorrows = true`, protected child tag that accessed only `[4, 8)`: the
   same write is a Tree Borrows conflict (UB);
4. `treeBorrows = true`, protected child tag over the whole `[0, 8)`: UB;
5. `treeBorrows = true`, unprotected child tag that accessed only `[4, 8)`:
   returns `99`. -/
theorem lm_np_v4_nested_field_unwrap_disjoint_tb_witness :
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4NestedFieldUnwrapMir false) 8
      (mkNpTbNestedFieldUnwrapState npPaddedAlloc8 true)) = .u32Val 99 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4NestedFieldUnwrapMir true) 8
      (mkNpTbNestedFieldUnwrapState (npPaddedAlloc8.setExtra (some (npSplitChildTree true)))
        true)) = .u32Val 99 ∧
    (runMiriSteps (annealStepHooksNullaryPtr npV4NestedFieldUnwrapMir true) 8
      (mkNpTbNestedFieldUnwrapState (npPaddedAlloc8.setExtra (some (npSplitChildTree false)))
        true)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    (runMiriSteps (annealStepHooksNullaryPtr npV4NestedFieldUnwrapMir true) 8
      (mkNpTbNestedFieldUnwrapState npPaddedAlloc8 true)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4NestedFieldUnwrapMir true) 8
      (mkNpTbNestedFieldUnwrapState (npPaddedAlloc8.setExtra (some (npSplitChildTree false)))
        false)) = .u32Val 99 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel⟩

/-! ### `V4` Sub-Range Tree Borrows Disjointness on `{ fst: u32, snd: BinderU32 }` & `(*ptr).field.unwrapUnsafeBinder` -/

/-- 8-byte layout for `np::PairU32Binder { fst: u32, snd: BinderU32 }`:
`fst` at `[0, 4)`, `snd` at `[4, 8)`. -/
def npPairU32BinderMirLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩,
    backendRepr := .scalarPair
      (.initialized (.int 32 false) ⟨0, 0xffffffff⟩)
      (.initialized (.int 32 false) ⟨0, 0xffffffff⟩),
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1],
    fieldLayouts := [0, 1],
    variants := .single 0, isUninhabited := false }

def npSubrangeLayouts : LayoutTable :=
  { npLayouts with entries := npLayouts.entries ++ [npPairU32BinderMirLayout] }

@[reducible] def npPairU32BinderMirTy : Ty :=
  { kind := .adt "np::PairU32Binder" [], layoutIdx := 5 }

@[reducible] def npRawMutPairU32BinderMirTy : Ty :=
  { kind := .rawPtr .mut npPairU32BinderMirTy.kind, layoutIdx := 0 }

private def npV4PairLocalSndUnwrapMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_local_snd_unwrap"
    [mkDecl u32MirTy, mkDecl npPairU32BinderMirTy] 1
    [mkBb [mkSt (.assign (locPlace 1 [.field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy])
             (.use (constU32 99))),
           mkSt (.assign (locPlace 0)
             (.use (.copy (locPlace 1 [.field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npSubrangeLayouts

private def npV4PairLocalFstMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_local_fst"
    [mkDecl u32MirTy, mkDecl npPairU32BinderMirTy] 1
    [mkBb [mkSt (.assign (locPlace 1 [.field 0 u32MirTy, .unwrapUnsafeBinder u32MirTy])
             (.use (constU32 99))),
           mkSt (.assign (locPlace 0)
             (.use (.copy (locPlace 1 [.field 0 u32MirTy, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npSubrangeLayouts

private def npV4PairDerefSndUnwrapMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_deref_snd_unwrap"
    [mkDecl u32MirTy, mkDecl npRawMutPairU32BinderMirTy, mkDecl npPairU32BinderMirTy] 1
    [mkBb [mkSt (.assign (locPlace 1 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy])
             (.use (constU32 99))),
           mkSt (.assign (locPlace 0)
             (.use (.copy (locPlace 1 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npSubrangeLayouts

private def npV4PairDerefFstMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_deref_fst"
    [mkDecl u32MirTy, mkDecl npRawMutPairU32BinderMirTy, mkDecl npPairU32BinderMirTy] 1
    [mkBb [mkSt (.assign (locPlace 1 [.deref, .field 0 u32MirTy]) (.use (constU32 99))),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.deref, .field 0 u32MirTy]))))]
      .return_]
    npSubrangeLayouts

private def mkNpPairLocalTbState (body : CapturedMir) (childOnFst childProtected : Bool) :
    AnnealStepState :=
  let alloc := npPaddedAlloc8.setExtra (some (npSplitChildTree childOnFst))
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with live := #[(npAid1, ⟨.stack, alloc⟩)] },
      addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨npAid1, npBase1⟩] },
      borrowTracker := some
        { global := { protectedTags := (hooksForChildProtected childProtected).protectedTags },
          retagMode := .Default } }
  let mp : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Miri.ABI.Size.ofBytes npBase1, some (.concrete npAid1 retagParentTag)⟩, .none, none⟩
  npMkState body u32MirTy
    #[npUninit (translateTyOverlay u32MirTy npSubrangeLayouts),
      ⟨.live (.indirect mp), some (translateTyOverlay npPairU32BinderMirTy npSubrangeLayouts)⟩]
    mach

private def mkNpPairDerefTbState (body : CapturedMir) (childOnFst childProtected : Bool) :
    AnnealStepState :=
  let alloc := npPaddedAlloc8.setExtra (some (npSplitChildTree childOnFst))
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with live := #[(npAid1, ⟨.stack, alloc⟩)] },
      addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨npAid1, npBase1⟩] },
      borrowTracker := some
        { global := { protectedTags := (hooksForChildProtected childProtected).protectedTags },
          retagMode := .Default } }
  npMkState body u32MirTy
    #[npUninit (translateTyOverlay u32MirTy npSubrangeLayouts),
      npScalarLocal (npPtrScalarTagged npAid1 npBase1 retagParentTag)
        (translateTyOverlay npRawMutPairU32BinderMirTy npSubrangeLayouts),
      npUninit (translateTyOverlay npPairU32BinderMirTy npSubrangeLayouts)]
    mach

/-- **`V4` Sub-Range Tree Borrows Disjointness on `{ fst: u32, snd: BinderU32 }`
for BOTH Local (`(_1.1).unwrapUnsafeBinder`, `_1.0`) AND Dereferenced
(`(*ptr).1.unwrapUnsafeBinder`, `(*ptr).0`) Places (LeanMiri)**:
with a `StrongProtector` covering ONLY `[0, 4)` (`fst`, `childOnFst = true`):
1. `(_1.1).unwrapUnsafeBinder = 99` (`[4, 8)`) succeeds (`99`) in `treeBorrows = true`,
   and faults UB when the protector covers `[4, 8)` (`childOnFst = false`);
2. `(*ptr).1.unwrapUnsafeBinder = 99` (`[4, 8)` through an immediate raw pointer)
   succeeds (`99`) in basic mode, succeeds (`99`) in `treeBorrows = true` with
   protected `[0, 4)`, faults UB with protected `[4, 8)`, and succeeds (`99`)
   when unprotected `[4, 8)`;
3. writing the protected field `[0, 4)` via `_1.0 = 99` OR `(*ptr).0 = 99`
   faults UB in `treeBorrows = true` when `[0, 4)` is protected, and succeeds
   (`99`) in basic mode and when only `[4, 8)` is protected. -/
theorem lm_np_v4_pair_subrange_disjoint_and_deref_field_tb_witness :
    -- 1. Local `(_1.1).unwrapUnsafeBinder` at `[4, 8)`
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairLocalSndUnwrapMir true) 8
      (mkNpPairLocalTbState npV4PairLocalSndUnwrapMir true true)) = .u32Val 99 ∧
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairLocalSndUnwrapMir true) 8
      (mkNpPairLocalTbState npV4PairLocalSndUnwrapMir false true)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    -- 2. Deref `(*ptr).1.unwrapUnsafeBinder` at `[4, 8)`
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndUnwrapMir false) 8
      (mkNpPairDerefTbState npV4PairDerefSndUnwrapMir false true)) = .u32Val 99 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndUnwrapMir true) 8
      (mkNpPairDerefTbState npV4PairDerefSndUnwrapMir true true)) = .u32Val 99 ∧
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndUnwrapMir true) 8
      (mkNpPairDerefTbState npV4PairDerefSndUnwrapMir false true)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndUnwrapMir true) 8
      (mkNpPairDerefTbState npV4PairDerefSndUnwrapMir false false)) = .u32Val 99 ∧
    -- 3. Protected `[0, 4)` writes (`_1.0` and `(*ptr).0`): UB when `[0, 4)` protected, ok otherwise
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairLocalFstMir true) 8
      (mkNpPairLocalTbState npV4PairLocalFstMir true true)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairLocalFstMir true) 8
      (mkNpPairLocalTbState npV4PairLocalFstMir false true)) = .u32Val 99 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairLocalFstMir false) 8
      (mkNpPairLocalTbState npV4PairLocalFstMir true true)) = .u32Val 99 ∧
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefFstMir true) 8
      (mkNpPairDerefTbState npV4PairDerefFstMir true true)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefFstMir true) 8
      (mkNpPairDerefTbState npV4PairDerefFstMir false true)) = .u32Val 99 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefFstMir false) 8
      (mkNpPairDerefTbState npV4PairDerefFstMir true true)) = .u32Val 99 := by
  refine ⟨by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ### `V4` `(*ptr).field`: invalid pointers and `Frozen` / `Disabled` / `Cell` tags -/

private def npV4PairDerefSndReadMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_deref_snd_read"
    [mkDecl u32MirTy, mkDecl npRawMutPairU32BinderMirTy, mkDecl npPairU32BinderMirTy] 1
    [mkBb [mkSt (.assign (locPlace 0)
             (.use (.copy (locPlace 1 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npSubrangeLayouts

/-- State for the `(*_1).field` fixtures with an arbitrary pointer local `ptr`
and borrow tree `tree` on the 8-byte pointee allocation `npAid1` (bytes
`fst = 7`, `snd = 11`); `retagChildTag` is protected iff `childProtected`. -/
private def mkNpPairDerefPtrState (body : CapturedMir) (tree : Miri.TreeBorrows.BorrowTree)
    (ptr : Miri.Interpreter.LocalValue AnnealProv) (childProtected : Bool) : AnnealStepState :=
  let alloc := npPaddedAlloc8.setExtra (some tree)
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with live := #[(npAid1, ⟨.stack, alloc⟩)] },
      addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨npAid1, npBase1⟩] },
      borrowTracker := some
        { global := { protectedTags := (hooksForChildProtected childProtected).protectedTags },
          retagMode := .Default } }
  npMkState body u32MirTy
    #[npUninit (translateTyOverlay u32MirTy npSubrangeLayouts),
      ⟨ptr, some (translateTyOverlay npRawMutPairU32BinderMirTy npSubrangeLayouts)⟩,
      npUninit (translateTyOverlay npPairU32BinderMirTy npSubrangeLayouts)]
    mach

/-- **`V4` `(*ptr).1.unwrapUnsafeBinder` Through an Invalid Pointer Is UB**
(write `(*ptr).1.unwrapUnsafeBinder = 99` and read `_0 = (*ptr).1.unwrapUnsafeBinder`,
stepped through unmodified vendored `Miri.Interpreter.Step.step`):
1. a dead pointer local is UB on write and on read (also in `treeBorrows = true`);
2. an uninitialized pointer local is UB on write and on read;
3. a null integer pointer (write) and a dangling integer pointer `0x2000` (read)
   are UB;
4. a pointer one past the end of the 8-byte pointee (field at `[12, 16)`) is UB
   on write and on read (also on write in `treeBorrows = true`);
5. control: a valid pointer reads `11`, in basic and in `treeBorrows = true` mode. -/
theorem lm_np_v4_deref_field_bad_pointer_ub_witness :
    let uninitPtr : Miri.Interpreter.LocalValue AnnealProv := .live (.immediate .uninit)
    let nullPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npScalarUInt 0 8)))
    let danglingPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npScalarUInt 0x2000 8)))
    let endPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npPtrScalarTagged npAid1 (npBase1 + 8) retagParentTag)))
    let okPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npPtrScalarTagged npAid1 npBase1 retagParentTag)))
    -- 1. Dead pointer local
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndUnwrapMir) 8
      (mkNpPairDerefPtrState npV4PairDerefSndUnwrapMir (hooksTwoNodeTree .unique) .dead false)) =
      .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir) 8
      (mkNpPairDerefPtrState npV4PairDerefSndReadMir (hooksTwoNodeTree .unique) .dead false)) =
      .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir true) 8
      (mkNpPairDerefPtrState npV4PairDerefSndReadMir (hooksTwoNodeTree .unique) .dead false)) =
      .ub ∧
    -- 2. Uninitialized pointer local
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndUnwrapMir) 8
      (mkNpPairDerefPtrState npV4PairDerefSndUnwrapMir (hooksTwoNodeTree .unique) uninitPtr
        false)) = .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir) 8
      (mkNpPairDerefPtrState npV4PairDerefSndReadMir (hooksTwoNodeTree .unique) uninitPtr
        false)) = .ub ∧
    -- 3. Null and dangling integer pointers
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndUnwrapMir) 8
      (mkNpPairDerefPtrState npV4PairDerefSndUnwrapMir (hooksTwoNodeTree .unique) nullPtr
        false)) = .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir) 8
      (mkNpPairDerefPtrState npV4PairDerefSndReadMir (hooksTwoNodeTree .unique) danglingPtr
        false)) = .ub ∧
    -- 4. Out-of-bounds (one past the end) pointer
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndUnwrapMir) 8
      (mkNpPairDerefPtrState npV4PairDerefSndUnwrapMir (hooksTwoNodeTree .unique) endPtr
        false)) = .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir) 8
      (mkNpPairDerefPtrState npV4PairDerefSndReadMir (hooksTwoNodeTree .unique) endPtr
        false)) = .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndUnwrapMir true) 8
      (mkNpPairDerefPtrState npV4PairDerefSndUnwrapMir (hooksTwoNodeTree .unique) endPtr
        false)) = .ub ∧
    -- 5. Control: valid pointer
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir) 8
      (mkNpPairDerefPtrState npV4PairDerefSndReadMir (hooksTwoNodeTree .unique) okPtr
        false)) = .u32Val 11 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir true) 8
      (mkNpPairDerefPtrState npV4PairDerefSndReadMir (hooksTwoNodeTree .unique) okPtr
        false)) = .u32Val 11 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **`V4` `(*ptr).0` Through a Misaligned Pointer Is UB**: the pointee
`np::PairU32Binder` requires 4-byte alignment; a pointer at address `257` into
the 8-byte allocation at `256` keeps field `0` in bounds (`[257, 261)`), and the
write `(*ptr).0 = 99` is UB, in basic and in `treeBorrows = true` mode. -/
theorem lm_np_v4_deref_field_misaligned_ub_witness :
    let oddPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npPtrScalarTagged npAid1 (npBase1 + 1) retagParentTag)))
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefFstMir) 8
      (mkNpPairDerefPtrState npV4PairDerefFstMir (hooksTwoNodeTree .unique) oddPtr false)) =
      .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefFstMir true) 8
      (mkNpPairDerefPtrState npV4PairDerefFstMir (hooksTwoNodeTree .unique) oddPtr false)) =
      .ub := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- **Tree Borrows Read Check on the 8-Byte Two-Node Tree** (`hooksTwoNodeTree perm`:
root `retagParentTag`, child `retagChildTag` with accessed permission `perm` on
`[0, 8)`), for the read of bytes `[4, 8)`:
1. a read through the child tag is permitted for every permission except
   `.disabled`, exactly as Trusted rejects a dereferencing read only through a
   `.disabled` borrow;
2. a read through the parent tag is a foreign read for the child: it is
   rejected when the child is a protected `.unique` tag, and permitted when the
   child is unprotected `.unique`, protected `.frozen`, or protected `.cell`;
3. a tag that is not registered in the tree is rejected, and a zero-sized read
   is permitted even through such a tag. -/
theorem npTreeBorrowsReadPermitted_perm_table (perm : TreeBorrowPerm) :
    npTreeBorrowsReadPermitted {} (hooksTwoNodeTree perm) retagChildTag 4 4 =
      (match perm with
       | .disabled => false
       | _ => true) ∧
    npTreeBorrowsReadPermitted (hooksForChildProtected true).protectedTags
      (hooksTwoNodeTree .unique) retagParentTag 4 4 = false ∧
    npTreeBorrowsReadPermitted {} (hooksTwoNodeTree .unique) retagParentTag 4 4 = true ∧
    npTreeBorrowsReadPermitted (hooksForChildProtected true).protectedTags
      (hooksTwoNodeTree .frozen) retagParentTag 4 4 = true ∧
    npTreeBorrowsReadPermitted (hooksForChildProtected true).protectedTags
      (hooksTwoNodeTree .cell) retagParentTag 4 4 = true ∧
    npTreeBorrowsReadPermitted {} (hooksTwoNodeTree .unique) ⟨999, by decide⟩ 4 4 = false ∧
    npTreeBorrowsReadPermitted {} (hooksTwoNodeTree .unique) ⟨999, by decide⟩ 4 0 = true := by
  cases perm with
  | reservedFrz b => cases b <;> decide +kernel
  | _ => decide +kernel

/-- **`V4` `(*ptr).1.unwrapUnsafeBinder` Under `Frozen` / `Disabled` / `Cell` Tags**
(8-byte `hooksTwoNodeTree perm` on the pointee, stepped through unmodified
vendored `Miri.Interpreter.Step.step`; `ptr` carries the child tag unless noted):
1. `.frozen`: in `treeBorrows = true` the write is UB and the read returns `11`;
2. `.disabled`: in `treeBorrows = true` the read is UB (the read check added to
   the `(*ptr).field` operand path) and the write is UB; in basic mode the read
   returns `11`;
3. `.cell`: in `treeBorrows = true` a write through the child tag is accepted
   and read back (`99`);
4. foreign write through the parent tag over a protected child: accepted (`99`)
   when the child is `.cell` (interior mutability does not disable the protected
   tag), UB when the child is `.unique`;
5. foreign read through the parent tag: UB when the child is a protected
   `.unique` tag, `11` when it is unprotected. -/
theorem lm_np_v4_deref_field_tb_frozen_disabled_cell_witness :
    let childPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npPtrScalarTagged npAid1 npBase1 retagChildTag)))
    let parentPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npPtrScalarTagged npAid1 npBase1 retagParentTag)))
    -- 1. `.frozen` child tag
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndUnwrapMir true) 8
      (mkNpPairDerefPtrState npV4PairDerefSndUnwrapMir (hooksTwoNodeTree .frozen) childPtr
        false)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir true) 8
      (mkNpPairDerefPtrState npV4PairDerefSndReadMir (hooksTwoNodeTree .frozen) childPtr
        false)) = .u32Val 11 ∧
    -- 2. `.disabled` child tag
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir true) 8
      (mkNpPairDerefPtrState npV4PairDerefSndReadMir (hooksTwoNodeTree .disabled) childPtr
        false)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows read conflict on dereferenced field place") ∧
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndUnwrapMir true) 8
      (mkNpPairDerefPtrState npV4PairDerefSndUnwrapMir (hooksTwoNodeTree .disabled) childPtr
        false)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir false) 8
      (mkNpPairDerefPtrState npV4PairDerefSndReadMir (hooksTwoNodeTree .disabled) childPtr
        false)) = .u32Val 11 ∧
    -- 3. `.cell` child tag: child write accepted
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndUnwrapMir true) 8
      (mkNpPairDerefPtrState npV4PairDerefSndUnwrapMir (hooksTwoNodeTree .cell) childPtr
        false)) = .u32Val 99 ∧
    -- 4. Foreign write through the parent tag over a protected child
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndUnwrapMir true) 8
      (mkNpPairDerefPtrState npV4PairDerefSndUnwrapMir (hooksTwoNodeTree .cell) parentPtr
        true)) = .u32Val 99 ∧
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndUnwrapMir true) 8
      (mkNpPairDerefPtrState npV4PairDerefSndUnwrapMir (hooksTwoNodeTree .unique) parentPtr
        true)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    -- 5. Foreign read through the parent tag
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir true) 8
      (mkNpPairDerefPtrState npV4PairDerefSndReadMir (hooksTwoNodeTree .unique) parentPtr
        true)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows read conflict on dereferenced field place") ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir true) 8
      (mkNpPairDerefPtrState npV4PairDerefSndReadMir (hooksTwoNodeTree .unique) parentPtr
        false)) = .u32Val 11 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel⟩

/-! ### `V4` Misaligned `(*ptr).field` Read UB & Persisted Tree Borrows `.Read` State Transitions -/

private def npV4PairDerefFstReadMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_deref_fst_read"
    [mkDecl u32MirTy, mkDecl npRawMutPairU32BinderMirTy, mkDecl npPairU32BinderMirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.deref, .field 0 u32MirTy]))))]
      .return_]
    npSubrangeLayouts

/-- State backed by the 12-byte allocation `npArr3U32AllocTree .unique` at
`npBase1` (`[256, 268)`), so a misaligned pointer `npBase1 + 1` keeps BOTH
field `0` (`[257, 261)`) AND field `1` (`[261, 265)`) strictly in-bounds. -/
private def mkNpPairDeref12State (body : CapturedMir)
    (ptr : Miri.Interpreter.LocalValue AnnealProv) : AnnealStepState :=
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with live := #[(npAid1, ⟨.stack, npArr3U32AllocTree .unique⟩)] },
      addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨npAid1, npBase1⟩] },
      borrowTracker := some { global := {}, retagMode := .Default } }
  npMkState body u32MirTy
    #[npUninit (translateTyOverlay u32MirTy npSubrangeLayouts),
      ⟨ptr, some (translateTyOverlay npRawMutPairU32BinderMirTy npSubrangeLayouts)⟩,
      npUninit (translateTyOverlay npPairU32BinderMirTy npSubrangeLayouts)]
    mach

/-- **`V4` Misaligned `(*ptr).field` & `(*ptr).1.unwrapUnsafeBinder` Read Is UB
(LeanMiri + Trusted Parity)**: on an odd-aligned pointer (`257`), BOTH reading
`(*ptr).0` (in-bounds `[257, 261)` of the 8-byte allocation) AND reading
`(*ptr).1.unwrapUnsafeBinder` (in-bounds `[261, 265)` of the 12-byte allocation)
report the exact `"misaligned pointer dereference"` UB in basic and
`treeBorrows = true` modes (while the aligned control reads `2`), matching
Trusted `stepMirFn = .fail .ub`. -/
theorem lm_np_v4_deref_field_misaligned_read_ub_witness :
    let oddPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npPtrScalarTagged npAid1 (npBase1 + 1) retagParentTag)))
    let okPtr : Miri.Interpreter.LocalValue AnnealProv :=
      .live (.immediate (.scalar (npPtrScalarTagged npAid1 npBase1 retagParentTag)))
    let tMisState : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0,
                   locals := [.uninit, .init (.ptr ⟨1, 1⟩ 8),
                              .init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨11, 4⟩])] },
        memory := { emptyMemory with
          borrows := [{ tag := 1, targetLocal := 2, targetProjection := [], perm := .unique,
                        targetFrameDepth := 0 }] } }
    -- 1. Misaligned `(*oddPtr).0` read (8-byte alloc, `[257, 261)` in bounds)
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefFstReadMir false) 8
      (mkNpPairDerefPtrState npV4PairDerefFstReadMir (hooksTwoNodeTree .unique) oddPtr false)).map (·.2) =
      .error (.undefinedBehavior "misaligned pointer dereference") ∧
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefFstReadMir true) 8
      (mkNpPairDerefPtrState npV4PairDerefFstReadMir (hooksTwoNodeTree .unique) oddPtr false)).map (·.2) =
      .error (.undefinedBehavior "misaligned pointer dereference") ∧
    -- 2. Misaligned `(*oddPtr).1.unwrapUnsafeBinder` read (12-byte alloc, `[261, 265)` in bounds)
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir false) 8
      (mkNpPairDeref12State npV4PairDerefSndReadMir oddPtr)).map (·.2) =
      .error (.undefinedBehavior "misaligned pointer dereference") ∧
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir true) 8
      (mkNpPairDeref12State npV4PairDerefSndReadMir oddPtr)).map (·.2) =
      .error (.undefinedBehavior "misaligned pointer dereference") ∧
    -- 3. Aligned control on the same 12-byte allocation reads `2`
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairDerefSndReadMir true) 8
      (mkNpPairDeref12State npV4PairDerefSndReadMir okPtr)) = .u32Val 2 ∧
    -- 4. Trusted `stepMirFn` parity on misaligned offset `1`
    stepMirFn npV4PairDerefSndReadMir tMisState = .fail .ub ∧
    stepMirFn npV4PairDerefFstReadMir tMisState = .fail .ub := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, rfl, rfl⟩

/-- Two-pointer MIR fixture testing persisted Tree Borrows `.Read` transitions:
1. `_4 = (*_1).1.unwrapUnsafeBinder` (foreign read on `[4, 8)` via `parentPtr`),
2. `(*_2).1.unwrapUnsafeBinder = 55` (write on `[4, 8)` via `childPtr`),
3. `_0 = (*_2).1.unwrapUnsafeBinder`. -/
private def npV4PairForeignReadThenChildWriteMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_foreign_read_then_child_write"
    [mkDecl u32MirTy, mkDecl npRawMutPairU32BinderMirTy, mkDecl npRawMutPairU32BinderMirTy,
     mkDecl npPairU32BinderMirTy, mkDecl u32MirTy] 2
    [mkBb [mkSt (.assign (locPlace 4)
             (.use (.copy (locPlace 1 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy])))),
           mkSt (.assign (locPlace 2 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy])
             (.use (constU32 55))),
           mkSt (.assign (locPlace 0)
             (.use (.copy (locPlace 2 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npSubrangeLayouts

/-- Sub-range precision companion: foreign read on `[4, 8)` (`(*_1).1.unwrapUnsafeBinder`),
followed by a child write to the DISJOINT `[0, 4)` field (`(*_2).0 = 55`). -/
private def npV4PairForeignReadSndThenChildWriteFstMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_foreign_read_snd_then_child_write_fst"
    [mkDecl u32MirTy, mkDecl npRawMutPairU32BinderMirTy, mkDecl npRawMutPairU32BinderMirTy,
     mkDecl npPairU32BinderMirTy, mkDecl u32MirTy] 2
    [mkBb [mkSt (.assign (locPlace 4)
             (.use (.copy (locPlace 1 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy])))),
           mkSt (.assign (locPlace 2 [.deref, .field 0 u32MirTy]) (.use (constU32 55))),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 2 [.deref, .field 0 u32MirTy]))))]
      .return_]
    npSubrangeLayouts

private def mkNpPairTwoPtrState (body : CapturedMir) (tree : Miri.TreeBorrows.BorrowTree)
    (childProtected : Bool) : AnnealStepState :=
  let alloc := npPaddedAlloc8.setExtra (some tree)
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with live := #[(npAid1, ⟨.stack, alloc⟩)] },
      addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨npAid1, npBase1⟩] },
      borrowTracker := some
        { global := { protectedTags := (hooksForChildProtected childProtected).protectedTags },
          retagMode := .Default } }
  let rawPtrLay := translateTyOverlay npRawMutPairU32BinderMirTy npSubrangeLayouts
  npMkState body u32MirTy
    #[npUninit (translateTyOverlay u32MirTy npSubrangeLayouts),
      npScalarLocal (npPtrScalarTagged npAid1 npBase1 retagParentTag) rawPtrLay,
      npScalarLocal (npPtrScalarTagged npAid1 npBase1 retagChildTag) rawPtrLay,
      npUninit (translateTyOverlay npPairU32BinderMirTy npSubrangeLayouts),
      npUninit (translateTyOverlay u32MirTy npSubrangeLayouts)]
    mach

/-- **`V4` Persisted Tree Borrows `.Read` State Transitions (Stepped 2-Statement
Witness)**: proves `npEvalOperandNullaryPtrTb` / `npApplyTreeBorrowsReadAt`
genuinely persists `.Read` transitions back into the allocation's `BorrowTree`
via `Allocation.setExtra` with exact sub-range precision:
1. **Unprotected `.Unique` -> `.Frozen` demotion**: statement 0's foreign read
   `(*parentPtr).1.unwrapUnsafeBinder` persists `.Unique -> .Frozen` on `[4, 8)`,
   causing statement 1's child write `(*childPtr).1.unwrapUnsafeBinder = 55` to
   fault UB in `treeBorrows = true` while returning `55` in `treeBorrows = false`;
2. **Sub-range precision**: the same foreign read of `[4, 8)` freezes ONLY
   `[4, 8)`, leaving `childPtr` `.Unique` on `[0, 4)` so `(*childPtr).0 = 55`
   returns `55` even in `treeBorrows = true`;
3. **Protected `ReservedFrz false` -> `ReservedFrz true` (conflicted) transition**:
   statement 0's foreign read persists `conflicted := true` on `[4, 8)`, causing
   statement 1's child write `(*childPtr).1.unwrapUnsafeBinder = 55` to fault UB
   under `StrongProtector`, while returning `55` when unprotected AND returning
   `55` on the disjoint `[0, 4)` write `(*childPtr).0 = 55` even when protected;
4. **`.Cell` control**: a foreign read leaves protected `.Cell` unchanged, so
   the child write returns `55`. -/
theorem lm_np_v4_deref_field_read_persistence_witness :
    -- 1. Unprotected `.Unique` child frozen on `[4, 8)` by foreign read -> child write UB
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairForeignReadThenChildWriteMir true) 8
      (mkNpPairTwoPtrState npV4PairForeignReadThenChildWriteMir (hooksTwoNodeTree .unique)
        false)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairForeignReadThenChildWriteMir false) 8
      (mkNpPairTwoPtrState npV4PairForeignReadThenChildWriteMir (hooksTwoNodeTree .unique)
        false)) = .u32Val 55 ∧
    -- 2. Sub-range precision: foreign read on `[4, 8)` leaves `[0, 4)` `.Unique`
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairForeignReadSndThenChildWriteFstMir true) 8
      (mkNpPairTwoPtrState npV4PairForeignReadSndThenChildWriteFstMir (hooksTwoNodeTree .unique)
        false)) = .u32Val 55 ∧
    -- 3. Protected `ReservedFrz false` -> `ReservedFrz true` on `[4, 8)` -> child write UB
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairForeignReadThenChildWriteMir true) 8
      (mkNpPairTwoPtrState npV4PairForeignReadThenChildWriteMir (hooksTwoNodeTree (.reservedFrz false))
        true)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairForeignReadThenChildWriteMir true) 8
      (mkNpPairTwoPtrState npV4PairForeignReadThenChildWriteMir (hooksTwoNodeTree (.reservedFrz false))
        false)) = .u32Val 55 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairForeignReadSndThenChildWriteFstMir true) 8
      (mkNpPairTwoPtrState npV4PairForeignReadSndThenChildWriteFstMir (hooksTwoNodeTree (.reservedFrz false))
        true)) = .u32Val 55 ∧
    -- 4. Protected `.Cell` control: foreign read leaves `.Cell` writable
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PairForeignReadThenChildWriteMir true) 8
      (mkNpPairTwoPtrState npV4PairForeignReadThenChildWriteMir (hooksTwoNodeTree .cell)
        true)) = .u32Val 55 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel⟩

/-- Single-statement copy between two dereferenced struct-field places, reading
through `_1` and writing through `_2`:
`(*_2).1.unwrapUnsafeBinder = copy (*_1).1.unwrapUnsafeBinder`, then
`_0 = (*_2).1.unwrapUnsafeBinder`. -/
private def npV4PairCopyParentToChildMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_copy_parent_to_child"
    [mkDecl u32MirTy, mkDecl npRawMutPairU32BinderMirTy, mkDecl npRawMutPairU32BinderMirTy,
     mkDecl npPairU32BinderMirTy, mkDecl u32MirTy] 2
    [mkBb [mkSt (.assign (locPlace 2 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy])
             (.use (.copy (locPlace 1 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy])))),
           mkSt (.assign (locPlace 0)
             (.use (.copy (locPlace 2 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npSubrangeLayouts

/-- The reverse copy, reading through `_2` and writing through `_1`:
`(*_1).1.unwrapUnsafeBinder = copy (*_2).1.unwrapUnsafeBinder`, then
`_0 = (*_1).1.unwrapUnsafeBinder`. -/
private def npV4PairCopyChildToParentMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_copy_child_to_parent"
    [mkDecl u32MirTy, mkDecl npRawMutPairU32BinderMirTy, mkDecl npRawMutPairU32BinderMirTy,
     mkDecl npPairU32BinderMirTy, mkDecl u32MirTy] 2
    [mkBb [mkSt (.assign (locPlace 1 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy])
             (.use (.copy (locPlace 2 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy])))),
           mkSt (.assign (locPlace 0)
             (.use (.copy (locPlace 1 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npSubrangeLayouts

/-- **`V4` Single-Statement Copy Between Aliasing `(*ptr).field` Places: Read
Before Write.** Miri evaluates the source operand (a read access) before it
writes the destination, and Trusted does the same (`evalRvalue`, then the place
write). For one statement that both reads a dereferenced struct-field place and
writes a gated place, the overlay applies the Tree Borrows read of the source
before the Tree Borrows write of the destination
(`npTreeBorrowsReadThenWriteApply`). In `mkNpPairTwoPtrState`, `_1` carries the
parent tag and `_2` the child tag of the 8-byte `hooksTwoNodeTree .unique`
(child unprotected):
1. `(*child).1.unwrapUnsafeBinder = copy (*parent).1.unwrapUnsafeBinder`: the
   foreign read through the parent freezes the child on `[4, 8)`, so the write
   through the child is UB in `treeBorrows = true` (applying the write first
   would accept the statement); in basic mode the statement is not UB;
2. `(*parent).1.unwrapUnsafeBinder = copy (*child).1.unwrapUnsafeBinder`: the
   read through the child precedes the parent write that disables the child, so
   the run is not UB in `treeBorrows = true` (applying the write first would
   report a read through a disabled tag). -/
theorem lm_np_v4_deref_field_copy_read_before_write_witness :
    (runMiriSteps (annealStepHooksNullaryPtr npV4PairCopyParentToChildMir true) 8
      (mkNpPairTwoPtrState npV4PairCopyParentToChildMir (hooksTwoNodeTree .unique)
        false)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on unwrapUnsafeBinder place") ∧
    (match runMiriSteps (annealStepHooksNullaryPtr npV4PairCopyParentToChildMir false) 8
        (mkNpPairTwoPtrState npV4PairCopyParentToChildMir (hooksTwoNodeTree .unique) false) with
      | .error (.undefinedBehavior _) => false
      | _ => true) = true ∧
    (match runMiriSteps (annealStepHooksNullaryPtr npV4PairCopyChildToParentMir true) 8
        (mkNpPairTwoPtrState npV4PairCopyChildToParentMir (hooksTwoNodeTree .unique) false) with
      | .error (.undefinedBehavior _) => false
      | _ => true) = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **`V4` Zero-Sized (`()`) `UnwrapUnsafeBinder` Write 3-Layer Boundary
(`DIV-LM-UNWRAP-ZST-WRITE`)**: separates the exact semantics across all three
layers on a zero-sized (`Size.ZERO`) write through `.unwrapUnsafeBinder`:
1. **Miri memory-hook layer (`npApplyTreeBorrowsWriteAt`)**: short-circuits on
   `size = 0` BEFORE any allocation, offset, or tag lookup — returning `.ok st`
   even for an unregistered tag (`⟨999⟩`) or a protected tree
   (`npApplyTreeBorrowsWriteAt_zst_noop`);
2. **Vendored `BorrowTree.performBorrowAccessRange` layer**: checks tag
   membership BEFORE iterating the empty `[0, 0)` range — returning `.Completed`
   for registered `retagParentTag` even under a `StrongProtector`, and
   `.MissingTag ⟨999⟩` for an unregistered tag;
3. **Trusted `MirSemantics.evalStmt` layer** (`evalPlaceWrite` /
   `writePlaceValue`): checks `.disabled` deref borrow permissions and active
   protectors BEFORE checking value size, rejecting BOTH `(*_1).unwrapUnsafeBinder = ()`
   through a `.disabled` tag AND `_1.unwrapUnsafeBinder = ()` under an active
   protector with `.fail .ub` (strictly stricter / fail-closed). -/
theorem lm_np_v4_zst_unwrap_write_boundary_witness :
    let unregTag : Miri.Memory.BorTag := ⟨999, by decide⟩
    let stProt : AnnealStepState := mkNpTbUnwrapState v4UnwrapBinderProtectedMir true
    let unitConst : MirAst.Operand := .constant { ty := unitMirTy, val := .zeroSized }
    let zstDerefStmt : MirAst.Statement :=
      mkSt (.assign (locPlace 1 [.deref, .unwrapUnsafeBinder unitMirTy]) (.use unitConst))
    let zstDerefDecls : List LocalDecl :=
      [mkDecl unitMirTy, mkDecl { kind := .rawPtr .mut (.tuple []), layoutIdx := 0 }, mkDecl unitMirTy]
    let tStDisabled : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0,
                   locals := [.uninit, .init (.ptr ⟨5, 0⟩ 8), .init .unit] },
        memory := { emptyMemory with
          borrows := [{ tag := 5, targetLocal := 2, targetProjection := [],
                        perm := .disabled, targetFrameDepth := 0 }] } }
    let zstLocalStmt : MirAst.Statement :=
      mkSt (.assign (locPlace 1 [.unwrapUnsafeBinder unitMirTy]) (.use unitConst))
    let zstLocalDecls : List LocalDecl := [mkDecl unitMirTy, mkDecl unitMirTy]
    let tStProt : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init .unit] },
        memory := { emptyMemory with
          borrows := [{ tag := 1, targetLocal := 1, targetProjection := [],
                        perm := .unique, protector := some 1, targetFrameDepth := 0 }],
          activeProtectors := [1] } }
    -- 1. Miri memory-hook layer (`npApplyTreeBorrowsWriteAt` skips tracker on size = 0)
    npApplyTreeBorrowsWriteAt (some (.concrete npAid1 unregTag)) npBase1 Miri.ABI.Size.ZERO stProt =
      .ok stProt ∧
    npApplyTreeBorrowsWriteAt (some (.concrete npAid1 retagParentTag)) npBase1 Miri.ABI.Size.ZERO stProt =
      .ok stProt ∧
    -- 2. Vendored `BorrowTree.performBorrowAccessRange` layer at `size = 0`
    (npU32ChildTree.performBorrowAccessRange (.concrete retagParentTag)
      Miri.ABI.Size.ZERO Miri.ABI.Size.ZERO .Write (hooksForChildProtected true).protectedTags
      .VisitChildrenOfAccessed).status = .Completed ∧
    (npU32ChildTree.performBorrowAccessRange (.concrete unregTag)
      Miri.ABI.Size.ZERO Miri.ABI.Size.ZERO .Write {} .VisitChildrenOfAccessed).status =
      .MissingTag unregTag ∧
    -- 3. Trusted `evalStmt` layer (strictly stricter / fail-closed on disabled & protected ZST writes)
    evalStmt tStDisabled zstDerefStmt zstDerefDecls emptyLayoutTable = MirStepNode.fail .ub ∧
    evalStmt tStProt zstLocalStmt zstLocalDecls emptyLayoutTable = MirStepNode.fail .ub :=
  ⟨npApplyTreeBorrowsWriteAt_zst_noop _ _ _ _ rfl,
   npApplyTreeBorrowsWriteAt_zst_noop _ _ _ _ rfl,
   by decide +kernel,
   by decide +kernel,
   rfl,
   rfl⟩

/-! ### Explicit `StorageLive` -> `Assign` -> `StorageDead` Post-Cleanup Lifecycle Fixtures -/

private inductive NpLmTrustedRunState where
  | running (s : MachineState)
  | done (o : NullaryPtrLmObs)

private def npLmTrustedValObs : MirSemantics.Value → NullaryPtrLmObs
  | .scalar ⟨bits, 4⟩ => .u32Val bits
  | .scalar ⟨bits, 1⟩ => .u8Val bits
  | .scalar ⟨bits, 8⟩ => .usizeVal bits
  | .ptr p _ => .ptrAlloc p.allocId
  | _ => .unsupported

private def npLmTrustedStep (body : CapturedMir) : NpLmTrustedRunState → NpLmTrustedRunState
  | .done o => .done o
  | .running s =>
    match stepMirFn body s with
    | .tau (.running s') => .running s'
    | .vis (.inr (.inl (.emit _))) k =>
      match k PUnit.unit with
      | .running s' => .running s'
      | _ => .done .unsupported
    | .ret (.normal r) => .done (npLmTrustedValObs r.1)
    | .vis (.inl (.fail .ub)) _ => .done .ub
    | .vis (.inl (.fail .unsupported)) _ => .done .unsupported
    | _ => .done .unsupported

private def npLmRunTrusted (body : CapturedMir) (fuel : Nat) (s : MachineState) : NullaryPtrLmObs :=
  match Nat.repeat (npLmTrustedStep body) fuel (.running s) with
  | .done o => o
  | .running _ => .unsupported

private def npV1StorageLifecycleMir : CapturedMir :=
  mkMirBody "np::w_v1_storage_lifecycle" [mkDecl usizeMirTy, mkDecl usizeMirTy] 0
    [mkBb [mkSt (.storageLive 1),
           mkSt (.assign (locPlace 1) (.nullaryOp .sizeOf npTuple16MirTy)),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1)))),
           mkSt (.storageDead 1)]
      .return_]

private def npV1PostStorageDeadUbMir : CapturedMir :=
  mkMirBody "np::w_v1_post_storage_dead_ub" [mkDecl usizeMirTy, mkDecl usizeMirTy] 0
    [mkBb [mkSt (.storageLive 1),
           mkSt (.assign (locPlace 1) (.nullaryOp .sizeOf npTuple16MirTy)),
           mkSt (.storageDead 1),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1))))]
      .return_]

private def npV4StorageLifecycleMir : CapturedMir :=
  mkMirBody "np::w_v4_storage_lifecycle"
    [mkDecl u32MirTy, mkDecl u32MirTy, mkDecl npBinderU32MirTy] 1
    [mkBb [mkSt (.storageLive 2),
           mkSt (.assign (locPlace 2) (.wrapUnsafeBinder (.copy (locPlace 1)) npBinderU32MirTy)),
           mkSt (.assign (locPlace 2 [.unwrapUnsafeBinder u32MirTy]) (.use (constU32 73))),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 2 [.unwrapUnsafeBinder u32MirTy])))),
           mkSt (.storageDead 2)]
      .return_]
    npLayouts

private def npV4PostStorageDeadUbMir : CapturedMir :=
  mkMirBody "np::w_v4_post_storage_dead_ub"
    [mkDecl u32MirTy, mkDecl u32MirTy, mkDecl npBinderU32MirTy] 1
    [mkBb [mkSt (.storageLive 2),
           mkSt (.assign (locPlace 2) (.wrapUnsafeBinder (.copy (locPlace 1)) npBinderU32MirTy)),
           mkSt (.assign (locPlace 2 [.unwrapUnsafeBinder u32MirTy]) (.use (constU32 73))),
           mkSt (.storageDead 2),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 2 [.unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npLayouts

/-- **Explicit `StorageLive` -> `Assign` -> `StorageDead` Post-Cleanup MIR
Lifecycle Witness (Trusted `initMachineState` + LeanMiri)**:
starting from standard post-cleanup initial states where non-argument locals
begin **`.dead`** (`initMachineState`, never pre-livened):
1. `V1` (`size_of`): `StorageLive _1 -> _1 = size_of(Tuple16) -> _0 = _1 -> StorageDead _1 -> Return`
   returns `.usizeVal 16` on BOTH Trusted (`initMachineState`) and LeanMiri
   (in both `treeBorrows` modes), while reading `_1` after `StorageDead _1`
   faults `.ub` on both;
2. `V4` (`wrapUnsafeBinder` / `unwrapUnsafeBinder`): `StorageLive _2 -> wrap -> write 73 -> read 73 -> StorageDead _2 -> Return`
   returns `.u32Val 73` on BOTH Trusted (`initMachineState`) and LeanMiri (in
   both `treeBorrows` modes), while reading `_2.unwrapUnsafeBinder` after
   `StorageDead _2` faults `.ub` on both. -/
theorem lm_np_storage_lifecycle_witness :
    let usizeLay := translateTyOverlay usizeMirTy emptyLayoutTable
    let u32Lay := translateTyOverlay u32MirTy npLayouts
    let binderLay := translateTyOverlay npBinderU32MirTy npLayouts
    let v1LowOk := lowerNullaryMirBody npV1StorageLifecycleMir
    let v1LowUb := lowerNullaryMirBody npV1PostStorageDeadUbMir
    let stV1Ok := npMkState v1LowOk usizeMirTy #[npUninit usizeLay, ⟨.dead, some usizeLay⟩]
    let stV1Ub := npMkState v1LowUb usizeMirTy #[npUninit usizeLay, ⟨.dead, some usizeLay⟩]
    let stV4Ok := npMkState npV4StorageLifecycleMir u32MirTy
      #[npUninit u32Lay, npScalarLocal (npScalarUInt 10 4) u32Lay, ⟨.dead, some binderLay⟩]
    let stV4Ub := npMkState npV4PostStorageDeadUbMir u32MirTy
      #[npUninit u32Lay, npScalarLocal (npScalarUInt 10 4) u32Lay, ⟨.dead, some binderLay⟩]
    -- 1. V1 StorageLive -> nullaryOp -> StorageDead (Trusted `initMachineState` + LeanMiri)
    npLmRunTrusted npV1StorageLifecycleMir 16 (initMachineState npV1StorageLifecycleMir []) =
      .usizeVal 16 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v1LowOk false) 12 stV1Ok) = .usizeVal 16 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v1LowOk true) 12 stV1Ok) = .usizeVal 16 ∧
    npLmRunTrusted npV1PostStorageDeadUbMir 16 (initMachineState npV1PostStorageDeadUbMir []) = .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v1LowUb false) 12 stV1Ub) = .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr v1LowUb true) 12 stV1Ub) = .ub ∧
    -- 2. V4 StorageLive -> wrap/unwrap -> StorageDead (Trusted `initMachineState` + LeanMiri)
    npLmRunTrusted npV4StorageLifecycleMir 16
      (initMachineState npV4StorageLifecycleMir [.scalar ⟨10, 4⟩]) = .u32Val 73 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4StorageLifecycleMir false) 12 stV4Ok) =
      .u32Val 73 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4StorageLifecycleMir true) 12 stV4Ok) =
      .u32Val 73 ∧
    npLmRunTrusted npV4PostStorageDeadUbMir 16
      (initMachineState npV4PostStorageDeadUbMir [.scalar ⟨10, 4⟩]) = .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PostStorageDeadUbMir false) 12 stV4Ub) =
      .ub ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr npV4PostStorageDeadUbMir true) 12 stV4Ub) =
      .ub := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ### `V1` Multi-Hop Nested `offset_of!`, Enum Variant `offset_of!`, & Fail-Closed `.unsupported` Boundaries -/

/-- 12-byte outer struct `{ tag: u8, inner: PaddedU8U32 }` (`tag` at `0`, 3
padding bytes, `inner` at `4` with `fieldLayouts[1] = 1` pointing to
`npPaddedU8U32MirLayout` whose field `1` is at offset `4`). -/
def npOuterNestedMirLayout : TypeLayout :=
  { size := ⟨12⟩, align := ⟨4⟩, backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1],
    fieldLayouts := [0, 1],
    variants := .single 0, isUninhabited := false }

/-- 12-byte 2-variant enum layout: variant `0` is unit (`[]`), variant `1` has
two fields at offsets `4` and `8`. -/
def npEnumMirLayout : TypeLayout :=
  { size := ⟨12⟩, align := ⟨4⟩, backendRepr := .memory,
    fields := .arbitrary [⟨0⟩] [0],
    variants := .multiple (.initialized (.int 8 false) ⟨0, 1⟩) 0
      [.arbitrary [] [], .arbitrary [⟨4⟩, ⟨8⟩] [0, 1]],
    isUninhabited := false }

def npNestedLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [binderU32MirLayout, npPaddedU8U32MirLayout, npOuterNestedMirLayout, npEnumMirLayout] }

@[reducible] def npOuterNestedMirTy : Ty :=
  { kind := .adt "np::OuterNested" [], layoutIdx := 2 }

@[reducible] def npEnumMirTy : Ty :=
  { kind := .adt "np::EnumTwoVar" [], layoutIdx := 3 }

@[reducible] def npUnresolvedAdtMirTy : Ty :=
  { kind := .adt "np::UnresolvedAdt" [], layoutIdx := 0 }

private def npV1MultiHopOffsetMir : CapturedMir :=
  mkMirBody "np::w_v1_multihop_offset" [mkDecl usizeMirTy, mkDecl npOuterNestedMirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.nullaryOp (.offsetOf [(0, 1), (0, 1)]) npOuterNestedMirTy))]
      .return_]
    npNestedLayouts

private def npV1EnumOffsetMir : CapturedMir :=
  mkMirBody "np::w_v1_enum_offset" [mkDecl usizeMirTy, mkDecl npEnumMirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.nullaryOp (.offsetOf [(1, 1)]) npEnumMirTy))] .return_]
    npNestedLayouts

private def npV1OobOffsetMir : CapturedMir :=
  mkMirBody "np::w_v1_oob_offset" [mkDecl usizeMirTy, mkDecl npPaddedMirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.nullaryOp (.offsetOf [(0, 99)]) npPaddedMirTy))] .return_]
    npLayouts

private def npV1UnsizedSizeOfMir (ty : Ty) (name : String) : CapturedMir :=
  mkMirBody name [mkDecl usizeMirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.nullaryOp .sizeOf ty))] .return_]

private def npV1UnresolvedLayoutMir : CapturedMir :=
  mkMirBody "np::w_v1_unresolved_layout" [mkDecl usizeMirTy, mkDecl npUnresolvedAdtMirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.nullaryOp .sizeOf npUnresolvedAdtMirTy))] .return_]

/-- **`V1` Multi-Hop Nested `offset_of!`, Multi-Variant Enum `offset_of!`, &
Fail-Closed `.unsupported` Boundary Parity (Trusted + `lowerNullaryMirBody`/LeanMiri)**:
1. Multi-hop nested struct `offset_of!([(0, 1), (0, 1)]) = 4 + 4 = 8` agrees
   across Trusted `evalNullaryOp` / `stepMirFn` AND `lowerNullaryMirBody` +
   LeanMiri `runMiriSteps` (in both `treeBorrows` modes);
2. Multi-variant enum `offset_of!([(1, 1)]) = 8` agrees across Trusted AND
   `lowerNullaryMirBody` + LeanMiri;
3. Fail-closed `.unsupported` boundary parity across Trusted AND
   `lowerNullaryMirBody`/LeanMiri for:
   (a) out-of-bounds `offset_of!` field index (`[(0, 99)]`, unit variant
       `[(0, 0)]`, out-of-range variant `[(2, 0)]`),
   (b) unsized types (`[u32]`, `str`, `dyn Trait`) in `sizeOf` / `alignOf`,
   (c) `NullOp.contractChecks`, and
   (d) unresolved ADT layout index (`layoutIdx := 0` in `emptyLayoutTable`). -/
theorem lm_np_v1_multihop_offsetof_and_failclosed_unsupported_witness :
    let usizeNestedLay := translateTyOverlay usizeMirTy npNestedLayouts
    let outerLay := translateTyOverlay npOuterNestedMirTy npNestedLayouts
    let enumLay := translateTyOverlay npEnumMirTy npNestedLayouts
    let usizeEmptyLay := translateTyOverlay usizeMirTy emptyLayoutTable
    let usizeNpLay := translateTyOverlay usizeMirTy npLayouts
    let paddedLay := translateTyOverlay npPaddedMirTy npLayouts
    let unresLay := translateTyOverlay npUnresolvedAdtMirTy emptyLayoutTable
    let dynTy : Ty := { kind := .dynamic "np::Tr", layoutIdx := 0 }
    let lowMulti := lowerNullaryMirBody npV1MultiHopOffsetMir
    let lowEnum := lowerNullaryMirBody npV1EnumOffsetMir
    let lowOob := lowerNullaryMirBody npV1OobOffsetMir
    let lowSlice := lowerNullaryMirBody (npV1UnsizedSizeOfMir sliceU32MirTy "np::w_v1_unsized_slice")
    let lowStr := lowerNullaryMirBody (npV1UnsizedSizeOfMir strMirTy "np::w_v1_unsized_str")
    let lowDyn := lowerNullaryMirBody (npV1UnsizedSizeOfMir dynTy "np::w_v1_unsized_dyn")
    let lowUnres := lowerNullaryMirBody npV1UnresolvedLayoutMir
    -- 1. Multi-hop nested struct `offset_of!([(0, 1), (0, 1)]) = 8`
    evalNullaryOp [] (.offsetOf [(0, 1), (0, 1)]) npOuterNestedMirTy emptyMemory
      npV1MultiHopOffsetMir.localDecls npNestedLayouts = .ok (.scalar ⟨8, 8⟩) [] emptyMemory ∧
    npLmRunTrusted npV1MultiHopOffsetMir 8 (initMachineState npV1MultiHopOffsetMir []) = .usizeVal 8 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr lowMulti false) 8
      (npMkState lowMulti usizeMirTy #[npUninit usizeNestedLay, npUninit outerLay])) = .usizeVal 8 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr lowMulti true) 8
      (npMkState lowMulti usizeMirTy #[npUninit usizeNestedLay, npUninit outerLay])) = .usizeVal 8 ∧
    -- 2. Multi-variant enum `offset_of!([(1, 1)]) = 8`
    evalNullaryOp [] (.offsetOf [(1, 1)]) npEnumMirTy emptyMemory
      npV1EnumOffsetMir.localDecls npNestedLayouts = .ok (.scalar ⟨8, 8⟩) [] emptyMemory ∧
    npLmRunTrusted npV1EnumOffsetMir 8 (initMachineState npV1EnumOffsetMir []) = .usizeVal 8 ∧
    npToObs (runMiriSteps (annealStepHooksNullaryPtr lowEnum false) 8
      (npMkState lowEnum usizeMirTy #[npUninit usizeNestedLay, npUninit enumLay])) = .usizeVal 8 ∧
    -- 3a. Out-of-bounds `offset_of!` fails closed with `.unsupported`
    evalNullaryOp [] (.offsetOf [(0, 99)]) npPaddedMirTy emptyMemory
      npV1OobOffsetMir.localDecls npLayouts = .unsupported ∧
    evalNullaryOp [] (.offsetOf [(0, 0)]) npEnumMirTy emptyMemory
      npV1EnumOffsetMir.localDecls npNestedLayouts = .unsupported ∧
    evalNullaryOp [] (.offsetOf [(2, 0)]) npEnumMirTy emptyMemory
      npV1EnumOffsetMir.localDecls npNestedLayouts = .unsupported ∧
    npIsUnsupportedErr (Miri.Interpreter.Step.step (annealStepHooksNullaryPtr lowOob) ()
      (npMkState lowOob usizeMirTy #[npUninit usizeNpLay, npUninit paddedLay])).2 = true ∧
    -- 3b. Unsized types (`[u32]`, `str`, `dyn Trait`) fail closed with `.unsupported`
    evalNullaryOp [] .sizeOf sliceU32MirTy emptyMemory [] emptyLayoutTable = .unsupported ∧
    evalNullaryOp [] .alignOf strMirTy emptyMemory [] emptyLayoutTable = .unsupported ∧
    evalNullaryOp [] .sizeOf dynTy emptyMemory [] emptyLayoutTable = .unsupported ∧
    npIsUnsupportedErr (Miri.Interpreter.Step.step (annealStepHooksNullaryPtr lowSlice) ()
      (npMkState lowSlice usizeMirTy #[npUninit usizeEmptyLay])).2 = true ∧
    npIsUnsupportedErr (Miri.Interpreter.Step.step (annealStepHooksNullaryPtr lowStr) ()
      (npMkState lowStr usizeMirTy #[npUninit usizeEmptyLay])).2 = true ∧
    npIsUnsupportedErr (Miri.Interpreter.Step.step (annealStepHooksNullaryPtr lowDyn) ()
      (npMkState lowDyn usizeMirTy #[npUninit usizeEmptyLay])).2 = true ∧
    -- 3c. `contractChecks` fails closed with `.unsupported`
    evalNullaryOp [] .contractChecks boolMirTy emptyMemory [] emptyLayoutTable = .unsupported ∧
    npIsUnsupportedErr (runMiriSteps (annealStepHooksNullaryPtr npContractChecksMir) 8
      npStContractChecks) = true ∧
    -- 3d. Unresolved ADT layout index fails closed with `.unsupported`
    evalNullaryOp [] .sizeOf npUnresolvedAdtMirTy emptyMemory
      npV1UnresolvedLayoutMir.localDecls emptyLayoutTable = .unsupported ∧
    evalNullaryOp [] (.offsetOf [(0, 0)]) npUnresolvedAdtMirTy emptyMemory
      npV1UnresolvedLayoutMir.localDecls emptyLayoutTable = .unsupported ∧
    npIsUnsupportedErr (Miri.Interpreter.Step.step (annealStepHooksNullaryPtr lowUnres) ()
      (npMkState lowUnres usizeMirTy #[npUninit usizeEmptyLay, npUninit unresLay])).2 = true := by
  refine ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel,
          rfl, by decide +kernel, by decide +kernel,
          rfl, rfl, rfl, by decide +kernel,
          rfl, rfl, rfl, by decide +kernel, by decide +kernel, by decide +kernel,
          rfl, by decide +kernel,
          rfl, rfl, by decide +kernel⟩

/-- **Trusted-side anchors** (`Trusted.Rustc.V2026_06_01.MirSemantics`):
1. the constants produced by `lowerNullaryMirBody` are exactly Trusted
   `evalNullaryOp`'s results on the fixtures (`16`, `8`, `12`, `4`), `ubChecks` is the
   `bool` `true`, and `contractChecks` is `.unsupported`;
2. the `rust-intrinsic` ABI divergence of `V3`: Trusted `stepMirFn` rejects the
   `FnPtrToPtr` cast with `.ub`, which LeanMiri accepts
   (`lm_np_v3_fnPtrToPtr_ub_and_divergence_witness`). -/
theorem lm_np_trusted_side_witness :
    evalNullaryOp [] .sizeOf npTuple16MirTy = .ok (.scalar ⟨16, 8⟩) [] emptyMemory ∧
    evalNullaryOp [] .alignOf npTuple16MirTy = .ok (.scalar ⟨8, 8⟩) [] emptyMemory ∧
    evalNullaryOp [] (.offsetOf [(0, 2)]) npTuple16MirTy = .ok (.scalar ⟨12, 8⟩) [] emptyMemory ∧
    evalNullaryOp [] (.offsetOf [(0, 1)]) npPaddedMirTy emptyMemory
      v1NullaryPaddedOffsetMir.localDecls npLayouts = .ok (.scalar ⟨4, 8⟩) [] emptyMemory ∧
    evalNullaryOp [] .ubChecks boolMirTy = .ok (.scalar ⟨1, 1⟩) [] emptyMemory ∧
    evalNullaryOp [] .contractChecks boolMirTy = .unsupported ∧
    stepMirFn npFnPtrToPtrIntrMir npIntrTrustedState = .fail .ub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §5. Canonical Executable LeanMiri Corpus Observation (`npLmObserve`) -/

/-- Direct vendored `Miri.Interpreter.Step.step` observation for EVERY
`(treeBorrows, variantIdx, caseIdx)` key across the 4 MIR variants
(`variantIdx ∈ 0..3`, `caseIdx ∈ 0..3`). Zero shadow evaluators: every entry runs
`runMiriSteps` -> `Miri.Interpreter.Step.step` under `annealStepHooksNullaryPtr`
and decodes the returned `_0` (or `StepError`) with `npToObs`. -/
def npLmObserve (treeBorrows : Bool) (variantIdx : Nat) (caseIdx : Nat) : NullaryPtrLmObs :=
  match variantIdx, caseIdx with
  -- 0: nullaryOp
  | 0, 0 =>
    npToObs <| runMiriSteps
      (annealStepHooksNullaryPtr (lowerNullaryMirBody v1NullaryTupleMir) treeBorrows) 12 npStV1Tuple
  | 0, 1 =>
    npToObs <| runMiriSteps (annealStepHooksNullaryPtr v1NullaryUbChecksMir treeBorrows) 8
      npStV1UbChecks
  | 0, 2 =>
    npToObs <| runMiriSteps (annealStepHooksNullaryPtr v1NullaryUbBranchMir treeBorrows) 8
      npStV1UbBranch
  | 0, 3 =>
    npToObs <| runMiriSteps
      (annealStepHooksNullaryPtr (lowerNullaryMirBody v1NullaryPaddedOffsetMir) treeBorrows) 8
      npStV1Padded
  -- 1: pointerCoercion
  | 1, 0 =>
    npToObs <| runMiriSteps
      (annealStepHooksNullaryPtr v2PtrCoerceFnPipelineMir treeBorrows [v2CalleeU32Mir]) 8
      npStV2Pipeline
  | 1, 1 =>
    npToObs <| runMiriSteps (annealStepHooksNullaryPtr v2PtrCoerceUnsizeSliceMir treeBorrows) 8
      (npStV2Unsize (.live (.immediate (.scalar (npPtrScalar npAid5 npBase5)))))
  | 1, 2 =>
    npToObs <| runMiriSteps (annealStepHooksNullaryPtr v2PtrCoerceDeadUbMir treeBorrows) 8
      npStV2DeadUb
  | 1, 3 =>
    npToObs <| runMiriSteps (annealStepHooksNullaryPtr v2PtrCoerceArrayToPtrMir treeBorrows) 8
      npStV2ArrayToPtr
  -- 2: fnPtrToPtr
  | 2, 0 =>
    npToObs <| runMiriSteps (annealStepHooksNullaryPtr v3FnPtrToPtrConstMir treeBorrows) 8
      (npStV3Const (.live (.immediate (.scalar (npPtrScalar npFnAid npFnBase)))))
  | 2, 1 =>
    npToObs <| runMiriSteps (annealStepHooksNullaryPtr v3FnPtrToPtrMutChainMir treeBorrows) 8
      npStV3MutChain
  | 2, 2 =>
    npToObs <| runMiriSteps (annealStepHooksNullaryPtr v3FnPtrToPtrDeadUbMir treeBorrows) 8
      npStV3DeadUb
  | 2, 3 =>
    npToObs <| runMiriSteps (annealStepHooksNullaryPtr v3FnPtrToPtrConstMir treeBorrows) 8
      (npStV3Const (.live (.immediate .uninit)))
  -- 3: unwrapUnsafeBinder (genuine treeBorrows sensitivity at caseIdx = 3)
  | 3, 0 =>
    npToObs <| runMiriSteps (annealStepHooksNullaryPtr v4UnwrapBinderRoundtripMir treeBorrows) 8
      npStV4Roundtrip
  | 3, 1 =>
    npToObs <| runMiriSteps (annealStepHooksNullaryPtr v4UnwrapBinderNzU8Mir treeBorrows) 8
      (npStV4NzU8 7)
  | 3, 2 =>
    npToObs <| runMiriSteps (annealStepHooksNullaryPtr v4UnwrapBinderDeadUbMir treeBorrows) 8
      npStV4DeadUb
  | 3, 3 =>
    npToObs <| runMiriSteps (annealStepHooksNullaryPtr v4UnwrapBinderProtectedMir treeBorrows) 8
      (mkNpTbUnwrapState v4UnwrapBinderProtectedMir true)
  | _, _ => .unsupported

theorem npLmObserve_v1_nullaryOp_table (tb : Bool) :
    npLmObserve tb 0 0 = .usizeVal 36 ∧ npLmObserve tb 0 1 = .u8Val 1 ∧
    npLmObserve tb 0 2 = .ub ∧ npLmObserve tb 0 3 = .usizeVal 4 := by
  cases tb <;>
    refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem npLmObserve_v2_pointerCoercion_table (tb : Bool) :
    npLmObserve tb 1 0 = .ptrAlloc 65536 ∧ npLmObserve tb 1 1 = .usizeVal 3 ∧
    npLmObserve tb 1 2 = .ub ∧ npLmObserve tb 1 3 = .ptrAlloc 5 := by
  cases tb <;>
    refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem npLmObserve_v3_fnPtrToPtr_table (tb : Bool) :
    npLmObserve tb 2 0 = .ptrAlloc 65536 ∧ npLmObserve tb 2 1 = .ptrAlloc 65537 ∧
    npLmObserve tb 2 2 = .ub ∧ npLmObserve tb 2 3 = .ub := by
  cases tb <;>
    refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem npLmObserve_v4_unwrapUnsafeBinder_table (tb : Bool) :
    npLmObserve tb 3 0 = .u32Val 73 ∧ npLmObserve tb 3 1 = .u8Val 7 ∧
    npLmObserve tb 3 2 = .ub ∧
    npLmObserve tb 3 3 = (if tb then NullaryPtrLmObs.ub else NullaryPtrLmObs.u32Val 42) := by
  cases tb <;>
    refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Exhaustive 32-key table**: for BOTH `treeBorrows` modes and all 16
`(variantIdx, caseIdx)` keys, `npLmObserve` reduces (kernel `decide`) to the frozen
cross-root expectation. The only mode-sensitive key is `(3, 3)`. -/
theorem npLmObserve_all_32_table (tb : Bool) :
    (npLmObserve tb 0 0 = .usizeVal 36 ∧ npLmObserve tb 0 1 = .u8Val 1 ∧
     npLmObserve tb 0 2 = .ub ∧ npLmObserve tb 0 3 = .usizeVal 4) ∧
    (npLmObserve tb 1 0 = .ptrAlloc 65536 ∧ npLmObserve tb 1 1 = .usizeVal 3 ∧
     npLmObserve tb 1 2 = .ub ∧ npLmObserve tb 1 3 = .ptrAlloc 5) ∧
    (npLmObserve tb 2 0 = .ptrAlloc 65536 ∧ npLmObserve tb 2 1 = .ptrAlloc 65537 ∧
     npLmObserve tb 2 2 = .ub ∧ npLmObserve tb 2 3 = .ub) ∧
    (npLmObserve tb 3 0 = .u32Val 73 ∧ npLmObserve tb 3 1 = .u8Val 7 ∧
     npLmObserve tb 3 2 = .ub ∧
     npLmObserve tb 3 3 = (if tb then NullaryPtrLmObs.ub else NullaryPtrLmObs.u32Val 42)) :=
  ⟨npLmObserve_v1_nullaryOp_table tb, npLmObserve_v2_pointerCoercion_table tb,
   npLmObserve_v3_fnPtrToPtr_table tb, npLmObserve_v4_unwrapUnsafeBinder_table tb⟩

/-- Mode sensitivity certified directly on `npLmObserve`: `unwrapUnsafeBinder`'s
`(3, 3)` key (memory-backed `_1` whose vendored borrow tree has a protected `Unique`
child) returns `42` with `treeBorrows = false` and faults `.ub` with
`treeBorrows = true` (vendored Tree Borrows write conflict). -/
theorem npLmObserve_unwrap_mode_sensitivity :
    npLmObserve false 3 3 = .u32Val 42 ∧ npLmObserve true 3 3 = .ub :=
  ⟨by decide +kernel, by decide +kernel⟩

/-! ## §6. Exhaustive Axiom, Non-Triviality, & Import-Isolation Audit -/

section AxiomAudit
open Lean Elab Command

elab "#assert_nullary_ptr_coercion_lm_audit" : command => do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`MiniRustSpec).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported in LeanMiriSpec"
  let rec isTrivialProp : Expr → Bool
    | .forallE _ _ body _ => isTrivialProp body
    | .letE _ _ _ body _ => isTrivialProp body
    | e =>
      if e.isConstOf ``True then true
      else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
      else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
      else false
  let mut checked : Nat := 0
  for (c, ci) in env.constants.map₂.toList do
    if let .thmInfo v := ci then
      let u := (Lean.privateToUserName? c).getD c
      if !u.isInternal && isTrivialProp v.type then
        throwError "{c} is a trivial theorem"
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
  if checked == 0 then
    throwError "LeanMiriSpec.NullaryAndPtrCoercionLM: 0 declarations found"
  logInfo m!"LeanMiriSpec.NullaryAndPtrCoercionLM: verified {checked} declarations (sorry_free=true, import_isolated=true, 0 trivial, 0 ofReduceBool)"

#assert_nullary_ptr_coercion_lm_audit

end AxiomAudit

end LeanMiriSpec.NullaryAndPtrCoercionLM
