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

/-- Mirror of Trusted `MirSemantics.unsizeArrayLen?`: extracts `(elemTy, len)`
exactly when `ck = "Unsize"` and `(opTy, targetKind)` is a valid Rust
array-to-slice unsizing (`&[T; n] -> &[T]`, `&mut [T; n] -> &mut [T]`,
`&mut [T; n] -> &[T]`, `&[T; n] -> *const [T]`, `&mut [T; n] -> *mut/*const [T]`,
`*const [T; n] -> *const [T]`, `*mut [T; n] -> *mut/*const [T]`) with compatible
mutability (`unsizeMutabilityCompatible`), identical element type (`rigidTyEq`),
and 64-bit `usize` length (`n < scalarModulus 8`). Rejects mutability upgrades
(`*const -> *mut`, `& -> &mut`, `& -> *mut`), raw-to-ref upgrades
(`*const/*mut -> &/&mut`), element mismatches (`[u32; 3] -> [u8]`), and
`n ≥ 2^64` length overflow (preventing silent `UInt64.ofNat` truncation). -/
def npUnsizeArraySpec? (ck : String) (opTy : Option Ty) (targetKind : RigidTy) :
    Option (RigidTy × Nat) :=
  match unsizeArrayLen? ck opTy targetKind with
  | some n =>
    match targetKind with
    | .ref _ (.slice dstElem) | .rawPtr _ (.slice dstElem) => some (dstElem, n)
    | _ => none
  | none => none

/-- **Exact 1-to-1 agreement between `npUnsizeArraySpec?` and Trusted
`MirSemantics.unsizeArrayLen?`** across EVERY coercion tag, operand type, and
target type. -/
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

/-- `CastHooks` overlay for `PointerCoercion(Unsize)` on array raw pointers and
safe references, extending `annealCastHooksUnwindFnPtrClosure` with exactly the
three leaves that vendored `Cast.cast` -> `unsizeInto` -> `unsizeIntoPointer` needs:
* `lockstepTails`: for a valid array-to-slice coercion (`npActiveUnsizeArrayInfo?`),
  the source tail is `npUnsizeArrayTailTyId` and the target tail is unchanged; an
  ill-typed array-to-slice coercion fails closed with `StepError.invalidProgram`,
  and every non-array unsizing (`dyn Trait`, struct tails) fails closed with
  `StepError.unsupported`;
* `typeInfo`: classifies `npUnsizeArrayTailTyId` as `.array elem len` (guarded by
  `n < 2^64` via `unsizeArrayLen?`);
* `validatePlace`: wide raw pointers (`*const/*mut [T]`) have no extra validity
  invariant (`pure ()`), while safe wide slice references (`&/&mut [T]`) run
  `annealValidateSafeWideSliceRef` (catching null, dangling, undersized,
  `SliceTooBig`, or misaligned safe slice references as UB). -/
def annealCastHooksNullaryPtr (currentBody : CapturedMir) (fnPtrs : List FnPtrEntry := .nil) :
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

/-- Syntactic predicate for `Assign` rvalues routed through the overlay's own
`RvalueHooks`: `Operand.RuntimeChecks` uses and `PointerCoercion(Unsize)` casts. -/
def isNullaryPtrRvalue : Miri.MIR.Rvalue → Bool
  | .Use (.RuntimeChecks _) _ => true
  | .Cast (.PointerCoercion .Unsize _) _ _ => true
  | _ => false

/-- `RvalueHooks` overlay extending `annealRvalueHooksDropBinderSubtype` with the
`Operand.RuntimeChecks` operand arm and the `PointerCoercion(Unsize)` cast arm
(vendored `Cast.cast` over `annealCastHooksNullaryPtr`, targeting the destination's
own wide-pointer `TyId`). Every other operand and cast is delegated unchanged. -/
def annealRvalueHooksNullaryPtr (currentBody : CapturedMir) (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.RvalueHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealRvalueHooksDropBinderSubtype currentBody fnPtrs
  { base with
    evalOperand := fun c op known =>
      match op with
      | .RuntimeChecks checks => npEvalRuntimeChecksOperand currentBody.layouts c checks
      | _ => base.evalOperand c op known
    evalOperandAt := fun c path op known =>
      match op with
      | .RuntimeChecks checks => npEvalRuntimeChecksOperand currentBody.layouts c checks
      | _ => base.evalOperandAt c path op known
    cast := fun c src kind ty dest =>
      match kind with
      | .PointerCoercion .Unsize _ =>
          Miri.Interpreter.Cast.cast (annealCastHooksNullaryPtr currentBody fnPtrs) c 16 src kind
            dest.layout.ty dest
      | _ => base.cast c src kind ty dest }

/-- Whether an assignment to `place` is subject to the Tree Borrows write check:
only in `treeBorrows` mode and only through an `UnwrapUnsafeBinder` place. -/
def npTbWriteGate (treeBorrows : Bool) (place : Miri.MIR.Place) : Bool :=
  treeBorrows && hasRealUnwrapUnsafeBinder place

/-- Apply a Tree Borrows write to the byte range `[absAddr - baseAddr, +size)`
of the live allocation referenced by `prov` via `ep2ApplyTreeBorrowsWrite`
(unmodified vendored `Tree.LocationState.performAccess` per node with the
vendored global protected-tag table), persisting the transitioned borrow tree
with `Allocation.setExtra` and rejecting conflicts or offset overflows as
`StepError.undefinedBehavior`. Untracked allocations and non-concrete
provenances are left untouched. -/
def npApplyTreeBorrowsWriteAt (prov : Option AnnealProv) (absAddr : UInt64)
    (size : Miri.ABI.Size) (state : AnnealStepState) :
    Except Miri.Interpreter.StepError AnnealStepState :=
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
  match annealEvalPlaceOverlay currentBody.localDecls currentBody.layouts place true state with
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

/-- Gated Tree Borrows write check run before an assignment. -/
def npTreeBorrowsWriteCheck (currentBody : CapturedMir) (treeBorrows : Bool)
    (place : Miri.MIR.Place) (state : AnnealStepState) :
    Except Miri.Interpreter.StepError AnnealStepState :=
  if npTbWriteGate treeBorrows place then
    npTreeBorrowsWriteApply currentBody place state
  else .ok state

/-- Outside `treeBorrows` mode the write check never changes the state. -/
theorem npTreeBorrowsWriteCheck_basic_mode (currentBody : CapturedMir)
    (place : Miri.MIR.Place) (state : AnnealStepState) :
    npTreeBorrowsWriteCheck currentBody false place state = .ok state := rfl

/-- Conservative `StepHooks` overlay extending `annealStepHooksDropBinderSubtype`:
* assignments first run `npTreeBorrowsWriteCheck` (a no-op unless
  `treeBorrows = true` and the destination is an `UnwrapUnsafeBinder` place);
* `Operand.RuntimeChecks` uses and `PointerCoercion(Unsize)` casts
  (`isNullaryPtrRvalue`) run unmodified vendored `evalRvalueIntoPlace` over
  `annealRvalueHooksNullaryPtr`;
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
      match npTreeBorrowsWriteCheck currentBody treeBorrows place state with
      | .error e => (state, .error e)
      | .ok state' =>
        if isNullaryPtrRvalue rvalue then
          Miri.Interpreter.runRvalue
            (Miri.Interpreter.evalRvalueIntoPlace
              (annealRvalueHooksNullaryPtr currentBody fnPtrs) choice rvalue place)
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
rvalue is not routed through `annealRvalueHooksNullaryPtr` and whose destination is
not subject to the Tree Borrows write check. -/
def stmtFreeOfNullaryPtrOverlay (treeBorrows : Bool) (stmt : Miri.MIR.Statement) : Prop :=
  match stmt.kind with
  | .Assign place rvalue =>
      isNullaryPtrRvalue rvalue = false ∧ npTbWriteGate treeBorrows place = false
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
              simp only [annealStepHooksNullaryPtr, npTreeBorrowsWriteCheck, hs.1, hs.2,
                         Bool.false_eq_true, ↓reduceIte]
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
    (∀ p, (annealRvalueHooksNullaryPtr body fnPtrs).evalOperandAt c path (.Copy p) known =
      (annealRvalueHooksUnwindFnPtrClosure body fnPtrs).evalOperandAt c path (.Copy p) known) ∧
    (∀ p, (annealRvalueHooksNullaryPtr body fnPtrs).evalOperandAt c path (.Move p) known =
      (annealRvalueHooksUnwindFnPtrClosure body fnPtrs).evalOperandAt c path (.Move p) known) ∧
    (∀ k, (annealRvalueHooksNullaryPtr body fnPtrs).evalOperandAt c path (.Constant k) known =
      (annealRvalueHooksUnwindFnPtrClosure body fnPtrs).evalOperandAt c path (.Constant k) known) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

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

private def npArr3U32Alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.fromBytes (Prov := AnnealProv)
      #[1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0] npAlign4 .Mut with
  | .ok al => al.withExtra none
  | .error _ => npUninit4Alloc

private def npMachine5Live : AnnealMachine :=
  { memory := { AnnealMachine.empty.memory with live := #[(npAid5, ⟨.stack, npArr3U32Alloc⟩)] },
    addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨npAid5, npBase5⟩] } }

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
