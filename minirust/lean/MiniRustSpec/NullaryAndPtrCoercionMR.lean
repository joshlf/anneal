/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import MiniRustSpec.DropBinderAndSubtypeMR

/-!
# Episode 2 Dual-Authority Correspondence (`MiniRustSpec` Authority):
# `Rvalue.nullaryOp`, `CastKind.pointerCoercion`, `CastKind.fnPtrToPtr`, `ProjectionElem.unwrapUnsafeBinder`

Universal operational laws, fault-equivalence, fail-closed boundary theorems,
and kernel-checked concrete witnesses relating
`Trusted.Rustc.V2026_06_01.MirSemantics.{evalNullaryOp, evalReifyFnPointer,
evalFnPtrToPtr, evalRvalue, stepMirFn}` directly to `MiniRustSpec.Interp` across
**both `Mach` (`BasicMemory<x86_64>`) and `MachTB` (`TreeBorrowsMemory<x86_64>`,
preserving `MachTB.wfLive`)** for 4 already-trusted MIR variants:

1. **`V1` (`Rvalue.nullaryOp`)** — `.sizeOf`, `.alignOf`, `.offsetOf`, and
   `.ubChecks` agree with the intrinsic layout queries, with MiniRust
   `Type.layout` (`LayoutStrategy.Sized`), `Tuple` field offsets,
   `UnOp.ComputeSize` / `UnOp.ComputeAlign`, and the lowered constant `Assign`;
   `.contractChecks` and unsized types (`[u32]`, `str`, `dyn Trait`) are
   fail-closed `.unsupported`.
2. **`V2` (`CastKind.pointerCoercion`)** — all 6 coercions (`"ReifyFnPointer"`,
   `"ClosureFnPointer"`, `"UnsafeFnPointer"`, `"MutToConstPointer"`,
   `"ArrayToPointer"`, `"Unsize"`), plus a `dyn Trait` unsizing / wide-pointer
   bridge exercising Episode 1's `MiniRustSpec.Interp.{vtableFromPtrM,
   checkPtrM, evalUnOpM}` (`GetMetadata`, `ComputeSize`, `ComputeAlign`,
   `VTableMethodLookup`) on `Mach` and `MachTB`.
3. **`V3` (`CastKind.fnPtrToPtr`)** — universal lockstep and UB fault
   characterization (dead, uninit, non-zero offset, stack borrow tag,
   `rustIntrinsic` ABI).
4. **`V4` (`ProjectionElem.unwrapUnsafeBinder`)** — transparent read/write
   projection on scalars and single-field `binderStructLayout?` structs, the
   `wrapUnsafeBinder -> unwrapUnsafeBinder` round-trip, dead/uninit UB, and
   genuine `Mach` vs. `MachTB` active-protector write-conflict mode
   sensitivity.

The trailing corpus interface (`npTrustedObserve`, `npMrObserve`,
`npMrObserveClass`) executes `stepMirFn` and `MiniRustSpec.Interp.{steps,
stepsTB}` directly (no shadow evaluator) and exports kernel-checked 32-key
table lemmas consumed by `Anneal.Mir.NullaryAndPtrCoercionBundle`.

Strict import isolation: this module NEVER imports `Anneal.*`,
`MiniRustSpec.Correspondence.DeinitBridge`, or
`MiniRustSpec.Correspondence.IntrinsicBoundary` (verified by the trailing
`#assert_nullary_ptr_coercion_mr_audit` check).
-/

namespace MiniRustSpec.NullaryAndPtrCoercionMR

set_option Elab.async false
set_option linter.unusedSimpArgs false

open Trusted.Effect Trusted.ITree Trusted.Sequence
open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness hiding constU32
open MiniRustSpec.Correspondence.PointerWitness MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.Correspondence.TbWitness
open MiniRustSpec.Correspondence.WideSliceDst hiding usizeMirTy
open MiniRustSpec.UnwindSetDiscrAndFnPtrMR
open MiniRustSpec.DropBinderAndSubtypeMR

/-! ## §0. Frozen Cross-Root Layouts, Types, and `CapturedMir` Fixtures

Every definition in this section is shared verbatim with
`LeanMiriSpec.NullaryAndPtrCoercionLM`; the cross-root kernel bridge in
`tests/mir/NullaryAndPtrCoercionCorrTests.lean` locks each fixture by `Eq.refl`. -/

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

@[reducible] def npTuple16MirTy : MirAst.Ty :=
  { kind := .tuple [.uint .u64, .uint .u32, .uint .u32], layoutIdx := 0 }
@[reducible] def npPaddedMirTy : MirAst.Ty :=
  { kind := .adt "np::PaddedU8U32" [], layoutIdx := 3 }
@[reducible] def npBinderU32MirTy : MirAst.Ty :=
  { kind := .adt "np::BinderU32" [], layoutIdx := 1 }
@[reducible] def npBinderNzU8MirTy : MirAst.Ty :=
  { kind := .adt "np::BinderNonZeroU8" [], layoutIdx := 2 }
@[reducible] def npFnDefMirTy : MirAst.Ty :=
  { kind := .fnDef "np::fn_u32" [], layoutIdx := 0 }
@[reducible] def npZstClosMirTy : MirAst.Ty :=
  { kind := .closure "np::clos_u32" [], layoutIdx := 4 }
@[reducible] def npSafeFnPtrMirTy : MirAst.Ty :=
  { kind := .fnPtr [.uint .u32] (.uint .u32) .safe .rust, layoutIdx := 0 }
@[reducible] def npUnsafeFnPtrMirTy : MirAst.Ty :=
  { kind := .fnPtr [.uint .u32] (.uint .u32) .unsafe_ .rust, layoutIdx := 0 }
@[reducible] def npArr3U32MirTy : MirAst.Ty :=
  { kind := .array (.uint .u32) 3, layoutIdx := 0 }
@[reducible] def npRawConstArr3U32MirTy : MirAst.Ty :=
  { kind := .rawPtr .not (.array (.uint .u32) 3), layoutIdx := 0 }
@[reducible] def npRawMutU8MirTy : MirAst.Ty :=
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

/-! ## §1. Corpus Keys and the Direct Trusted `stepMirFn` Runner -/

/-- The 4 already-trusted MIR variants of this correspondence. -/
inductive NullaryPtrVariant : Type where
  | nullaryOp
  | pointerCoercion
  | fnPtrToPtr
  | unwrapUnsafeBinder
  deriving DecidableEq, Repr

/-- Corpus test case selector within each of the 4 variants. -/
inductive NullaryPtrCase : Type where
  /-- Primary positive normal-return case. -/
  | okPrimary
  /-- Secondary positive normal-return case. -/
  | okSecondary
  /-- Primary UB fault case. -/
  | ubFault
  /-- Mode-sensitive case on `unwrapUnsafeBinder` (`BasicMemory` returns vs.
      `TreeBorrows` protector UB); a further normal-return or UB check elsewhere. -/
  | modeCase
  deriving DecidableEq, Repr

/-- Normalized authority-typed observation of one bounded Trusted
`stepMirFn` execution. -/
inductive NullaryPtrTrustedObs : Type where
  | u32Val (bits : Nat)
  | u8Val (bits : Nat)
  | usizeVal (bits : Nat)
  | ptrAlloc (allocId : Nat)
  | ub
  | unsupported
  /-- Out of fuel, a pending interaction, or a return value outside the
      observable domain. -/
  | stuck
  deriving DecidableEq, Repr

/-- Observe a Trusted return `MirSemantics.Value`. A single-field binder
struct value (`.aggregate 0 [scalar]`) is observed as its transparent field. -/
def npTrustedValueObs : MirSemantics.Value → NullaryPtrTrustedObs
  | .scalar ⟨bits, 1⟩ => .u8Val bits
  | .scalar ⟨bits, 4⟩ => .u32Val bits
  | .scalar ⟨bits, 8⟩ => .usizeVal bits
  | .ptr p 8 => .ptrAlloc p.allocId
  | .aggregate 0 [.scalar ⟨bits, 1⟩] => .u8Val bits
  | .aggregate 0 [.scalar ⟨bits, 4⟩] => .u32Val bits
  | _ => .stuck

/-- State of a bounded Trusted `stepMirFn` execution. -/
inductive NpTrustedRunState : Type where
  | running (s : MachineState)
  | done (o : NullaryPtrTrustedObs)

/-- One `stepMirFn` step of the bounded Trusted runner. -/
def npTrustedRunStep (body : CapturedMir) : NpTrustedRunState → NpTrustedRunState
  | .done o => .done o
  | .running s =>
    match stepMirFn body s with
    | .tau (.running s') => .running s'
    | .vis (.inr (.inl (.emit _))) k =>
      match k PUnit.unit with
      | .running s' => .running s'
      | _ => .done .stuck
    | .ret (.normal r) => .done (npTrustedValueObs r.1)
    | .vis (.inl (.fail .ub)) _ => .done .ub
    | .vis (.inl (.fail .unsupported)) _ => .done .unsupported
    | _ => .done .stuck

/-- Execute `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` directly for up
to `fuel` steps and return the normalized observation. -/
def npRunTrusted (body : CapturedMir) (fuel : Nat) (s : MachineState) : NullaryPtrTrustedObs :=
  match Nat.repeat (npTrustedRunStep body) fuel (.running s) with
  | .done o => o
  | .running _ => .stuck

/-- Initialize a Trusted `MachineState` with all declared frame locals live
(`.uninit` for `_0` and temporaries, `.init v` for arguments), matching
`LeanMiriSpec` `npMkState` (`npUninit`) and `MiniRustSpec` `mkMrMach` stack
allocations on post-cleanup MIR fixtures without explicit `StorageLive`. -/
def npInitLiveState (body : CapturedMir) (args : List Value) : MachineState :=
  let base := initMachineState body args
  { base with
    frame := { base.frame with
      locals := base.frame.locals.map fun
        | .dead => .uninit
        | slot => slot } }

def npInitLiveStateWithCallees (body : CapturedMir) (args : List Value)
    (callees : List CapturedMir) : MachineState :=
  let base := initMachineStateWithCallees body args callees
  { base with
    frame := { base.frame with
      locals := base.frame.locals.map fun
        | .dead => .uninit
        | slot => slot } }

/-- Initial Trusted state for `v2PtrCoerceFnPipelineMir`: the callee body
`v2CalleeU32Mir` is available for `checkCalleeSig`, and `nextAllocId` starts at
`fnPtrAllocBase` (`65536`). -/
def npFnPipelineInitState : MachineState :=
  let base := npInitLiveStateWithCallees v2PtrCoerceFnPipelineMir [] [v2CalleeU32Mir]
  { base with memory := { base.memory with nextAllocId := 65536 } }

/-- Initial Trusted state for `v3FnPtrToPtrConstMir` with an uninitialized
function-pointer operand `_1`. -/
def npUninitFnPtrState : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] },
    memory := (initMachineState v3FnPtrToPtrConstMir []).memory }

/-- Initial Trusted state for `v4UnwrapBinderProtectedMir`: `_1` holds the
binder struct `BinderU32(11)`, and borrow tag `1` on local `1` carries an
active protector exactly when `protectedMode = true` (matching MiniRust
`Validate _ true` under `TreeBorrowsMemory`). -/
def v4UnwrapBinderProtectedInitState (protectedMode : Bool) : MachineState :=
  let base := initMachineState v4UnwrapBinderProtectedMir [.aggregate 0 [.scalar ⟨11, 4⟩]]
  let bEntry : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetProjection := [], perm := .active,
      rangeOffset := 0, rangeLen := 4, protector := if protectedMode then some 1 else none,
      parentTag := none, targetFrameDepth := 0, allocDead := false }
  { base with
    memory := { base.memory with
      borrows := [bEntry],
      activeProtectors := if protectedMode then [1] else [] } }

/-- The `CapturedMir` fixture executed for each `(variant, case)` key. -/
def npTrustedFixture : NullaryPtrVariant → NullaryPtrCase → CapturedMir
  | .nullaryOp, .okPrimary => v1NullaryTupleMir
  | .nullaryOp, .okSecondary => v1NullaryUbChecksMir
  | .nullaryOp, .ubFault => v1NullaryUbBranchMir
  | .nullaryOp, .modeCase => v1NullaryPaddedOffsetMir
  | .pointerCoercion, .okPrimary => v2PtrCoerceFnPipelineMir
  | .pointerCoercion, .okSecondary => v2PtrCoerceUnsizeSliceMir
  | .pointerCoercion, .ubFault => v2PtrCoerceDeadUbMir
  | .pointerCoercion, .modeCase => v2PtrCoerceArrayToPtrMir
  | .fnPtrToPtr, .okPrimary => v3FnPtrToPtrConstMir
  | .fnPtrToPtr, .okSecondary => v3FnPtrToPtrMutChainMir
  | .fnPtrToPtr, .ubFault => v3FnPtrToPtrDeadUbMir
  | .fnPtrToPtr, .modeCase => v3FnPtrToPtrConstMir
  | .unwrapUnsafeBinder, .okPrimary => v4UnwrapBinderRoundtripMir
  | .unwrapUnsafeBinder, .okSecondary => v4UnwrapBinderNzU8Mir
  | .unwrapUnsafeBinder, .ubFault => v4UnwrapBinderDeadUbMir
  | .unwrapUnsafeBinder, .modeCase => v4UnwrapBinderProtectedMir

/-- The initial Trusted `MachineState` for each `(protectedMode, variant, case)` key. -/
def npTrustedInit (protectedMode : Bool) : NullaryPtrVariant → NullaryPtrCase → MachineState
  | .nullaryOp, .okPrimary => npInitLiveState v1NullaryTupleMir []
  | .nullaryOp, .okSecondary => npInitLiveState v1NullaryUbChecksMir []
  | .nullaryOp, .ubFault => npInitLiveState v1NullaryUbBranchMir []
  | .nullaryOp, .modeCase => npInitLiveState v1NullaryPaddedOffsetMir []
  | .pointerCoercion, .okPrimary => npFnPipelineInitState
  | .pointerCoercion, .okSecondary =>
    npInitLiveState v2PtrCoerceUnsizeSliceMir [.ptr { allocId := 5, offsetBytes := 0 } 8]
  | .pointerCoercion, .ubFault =>
    npInitLiveState v2PtrCoerceDeadUbMir [.ptr { allocId := 5, offsetBytes := 0 } 8]
  | .pointerCoercion, .modeCase =>
    npInitLiveState v2PtrCoerceArrayToPtrMir [.ptr { allocId := 5, offsetBytes := 0 } 8]
  | .fnPtrToPtr, .okPrimary =>
    npInitLiveState v3FnPtrToPtrConstMir [.ptr { allocId := 65536, offsetBytes := 0 } 8]
  | .fnPtrToPtr, .okSecondary =>
    npInitLiveState v3FnPtrToPtrMutChainMir [.ptr { allocId := 65537, offsetBytes := 0 } 8]
  | .fnPtrToPtr, .ubFault =>
    npInitLiveState v3FnPtrToPtrDeadUbMir [.ptr { allocId := 65536, offsetBytes := 0 } 8]
  | .fnPtrToPtr, .modeCase => npUninitFnPtrState
  | .unwrapUnsafeBinder, .okPrimary =>
    npInitLiveState v4UnwrapBinderRoundtripMir [.scalar ⟨10, 4⟩]
  | .unwrapUnsafeBinder, .okSecondary =>
    npInitLiveState v4UnwrapBinderNzU8Mir [.scalar ⟨7, 1⟩]
  | .unwrapUnsafeBinder, .ubFault =>
    npInitLiveState v4UnwrapBinderDeadUbMir [.aggregate 0 [.scalar ⟨11, 4⟩]]
  | .unwrapUnsafeBinder, .modeCase => v4UnwrapBinderProtectedInitState protectedMode

/-- Step budget of every Trusted corpus execution (the longest fixture runs 5
statements and one terminator). -/
def npTrustedFuel : Nat := 16

/-- Direct Trusted observation for every `(protectedMode, variant, case)` key:
runs `stepMirFn` on the actual `CapturedMir` fixture from its initial state. -/
def npTrustedObserve (protectedMode : Bool) (v : NullaryPtrVariant) (c : NullaryPtrCase) :
    NullaryPtrTrustedObs :=
  npRunTrusted (npTrustedFixture v c) npTrustedFuel (npTrustedInit protectedMode v c)

/-- The frozen 32-key Trusted observation table. -/
def npTrustedExpected (protectedMode : Bool) :
    NullaryPtrVariant → NullaryPtrCase → NullaryPtrTrustedObs
  | .nullaryOp, .okPrimary => .usizeVal 36
  | .nullaryOp, .okSecondary => .u8Val 1
  | .nullaryOp, .ubFault => .ub
  | .nullaryOp, .modeCase => .usizeVal 4
  | .pointerCoercion, .okPrimary => .ptrAlloc 65536
  | .pointerCoercion, .okSecondary => .usizeVal 3
  | .pointerCoercion, .ubFault => .ub
  | .pointerCoercion, .modeCase => .ptrAlloc 5
  | .fnPtrToPtr, .okPrimary => .ptrAlloc 65536
  | .fnPtrToPtr, .okSecondary => .ptrAlloc 65537
  | .fnPtrToPtr, .ubFault => .ub
  | .fnPtrToPtr, .modeCase => .ub
  | .unwrapUnsafeBinder, .okPrimary => .u32Val 73
  | .unwrapUnsafeBinder, .okSecondary => .u8Val 7
  | .unwrapUnsafeBinder, .ubFault => .ub
  | .unwrapUnsafeBinder, .modeCase =>
    match protectedMode with
    | false => .u32Val 42
    | true => .ub

/-- **Kernel-checked Trusted table**: on all 32 keys, executing `stepMirFn` on
the fixture yields exactly the frozen observation. -/
theorem npTrustedObserve_table (protectedMode : Bool) (v : NullaryPtrVariant)
    (c : NullaryPtrCase) :
    npTrustedObserve protectedMode v c = npTrustedExpected protectedMode v c := by
  cases protectedMode <;> cases v <;> cases c <;> decide +kernel

/-! ## §2 (`V1`): `Rvalue.nullaryOp` (`Mach` & `MachTB`) -/

/-- **V1 Dispatch (`np_v1_evalRvalue_nullaryOp_eq`)**: `evalRvalue` evaluates
`Rvalue.nullaryOp` exactly by `evalNullaryOp`. -/
theorem np_v1_evalRvalue_nullaryOp_eq (locals : List LocalSlot) (op : NullOp) (ty : MirAst.Ty)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (.nullaryOp op ty) mem decls layouts =
      evalNullaryOp locals op ty mem decls layouts := rfl

/-- **V1 Fail-Closed Boundary (`.contractChecks`)**: unconditionally
`.unsupported`, for every type, state, and layout table. -/
theorem np_v1_nullary_contractChecks_unsupported (locals : List LocalSlot) (ty : MirAst.Ty)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) :
    evalNullaryOp locals .contractChecks ty mem decls layouts = .unsupported := rfl

/-- **V1 Universal `.ubChecks` Law**: on a `bool` result type `ub_checks`
evaluates to `true` leaving locals and memory unchanged; on a non-`bool`
result type it is fail-closed `.unsupported`. -/
theorem np_v1_nullary_ubChecks_universal (locals : List LocalSlot) (li : Nat)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) :
    evalNullaryOp locals .ubChecks { kind := .bool, layoutIdx := li } mem decls layouts =
      .ok (.scalar (boolToScalar true)) locals mem ∧
    evalNullaryOp locals .ubChecks u32MirTy mem decls layouts = .unsupported ∧
    evalNullaryOp locals .ubChecks usizeMirTy mem decls layouts = .unsupported :=
  ⟨rfl, rfl, rfl⟩

/-- **V1 Universal `.sizeOf` Law**: whenever the intrinsic layout query
resolves the byte size within `isize::MAX`, `size_of` returns exactly that
size as a pointer-width scalar and leaves locals and memory unchanged. -/
theorem np_v1_nullary_sizeOf_of_intrinsic (locals : List LocalSlot) (ty : MirAst.Ty)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (sz : Nat)
    (hSz : intrinsicRigidTyByteSize decls layouts ty.kind = .some sz)
    (hLe : Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes layouts)) 2) 1) = true) :
    evalNullaryOp locals .sizeOf ty mem decls layouts =
      .ok (.scalar ⟨sz, layoutPointerBytes layouts⟩) locals mem := by
  unfold evalNullaryOp
  first | simp only [hSz, hLe] | simp [hSz, hLe]

/-- **V1 Universal Unresolved-Size Boundary**: whenever the intrinsic layout
query does not resolve a byte size (every unsized type), `size_of`,
`align_of`, and `offset_of!` are all fail-closed `.unsupported`. -/
theorem np_v1_nullary_unsupported_of_unresolved_size (locals : List LocalSlot) (ty : MirAst.Ty)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (fields : List (VariantIdx × FieldIdx))
    (hSz : intrinsicRigidTyByteSize decls layouts ty.kind = .none) :
    evalNullaryOp locals .sizeOf ty mem decls layouts = .unsupported ∧
    evalNullaryOp locals .alignOf ty mem decls layouts = .unsupported ∧
    evalNullaryOp locals (.offsetOf fields) ty mem decls layouts = .unsupported := by
  refine ⟨?_, ?_, ?_⟩
  · unfold evalNullaryOp
    first | simp only [hSz] | simp [hSz]
  · unfold evalNullaryOp
    cases hAl : intrinsicRigidTyAlign decls layouts ty.kind <;>
      first | simp only [hSz] | simp [hSz]
  · unfold evalNullaryOp
    first | simp only [hSz] | simp [hSz]

/-- **V1 Universal `.alignOf` Law**: whenever the intrinsic queries resolve a
size within `isize::MAX` and a power-of-two alignment below the pointer
modulus, `align_of` returns exactly that alignment. -/
theorem np_v1_nullary_alignOf_of_intrinsic (locals : List LocalSlot) (ty : MirAst.Ty)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (sz al : Nat)
    (hSz : intrinsicRigidTyByteSize decls layouts ty.kind = .some sz)
    (hAl : intrinsicRigidTyAlign decls layouts ty.kind = .some al)
    (hOk : Bool.and
      (Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes layouts)) 2) 1))
      (Bool.and (Trusted.Rustc.V2026_06_01.Layout.Align.isPowerOfTwoBytes ⟨al⟩)
        (Nat.blt al (scalarModulus (layoutPointerBytes layouts)))) = true) :
    evalNullaryOp locals .alignOf ty mem decls layouts =
      .ok (.scalar ⟨al, layoutPointerBytes layouts⟩) locals mem := by
  unfold evalNullaryOp
  first | simp only [hSz, hAl, hOk] | simp [hSz, hAl, hOk]

/-- **V1 Universal `.offsetOf` Law**: whenever the size resolves and
`resolveOffsetOfPath` resolves the field path to an offset within the object,
`offset_of!` returns exactly that offset. -/
theorem np_v1_nullary_offsetOf_of_intrinsic (locals : List LocalSlot) (ty : MirAst.Ty)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (fields : List (VariantIdx × FieldIdx)) (sz off : Nat)
    (hSz : intrinsicRigidTyByteSize decls layouts ty.kind = .some sz)
    (hOff : resolveOffsetOfPath layouts
      (intrinsicRigidTyByteSize decls layouts)
      (intrinsicRigidTyAlign decls layouts)
      (findDeclLayoutForRigidTy decls layouts)
      (.some ty.kind)
      (findDeclLayoutForRigidTy decls layouts ty.kind)
      fields = .some off)
    (hOk : Bool.and
      (Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes layouts)) 2) 1))
      (Nat.ble off sz) = true) :
    evalNullaryOp locals (.offsetOf fields) ty mem decls layouts =
      .ok (.scalar ⟨off, layoutPointerBytes layouts⟩) locals mem := by
  unfold evalNullaryOp
  first | simp only [hSz, hOff, hOk] | simp [hSz, hOff, hOk]

/-- MiniRust `(u64, u32, u32)` tuple type (size 16, align 8, fields at
offsets 0, 8, 12), the lowering of `npTuple16MirTy`. -/
@[reducible] def npTuple16MrTy : Gen.Type :=
  .Tuple [(⟨0⟩, u64MrTy), (⟨8⟩, u32MrTy), (⟨12⟩, u32MrTy)] ⟨⟨16⟩, ⟨8⟩, none⟩ none

/-- MiniRust `PaddedU8U32 { u8, u32 }` struct type (size 8, align 4, fields at
offsets 0 and 4), the lowering of `npPaddedMirTy`. -/
@[reducible] def npPaddedU8U32MrTy : Gen.Type :=
  .Tuple [(⟨0⟩, u8MrTy), (⟨4⟩, u32MrTy)] ⟨⟨8⟩, ⟨4⟩, none⟩ none

/-- The byte offset MiniRust assigns to field `i` of a `Tuple` type. -/
def npTupleFieldOffset : Gen.Type → Nat → Option Nat
  | .Tuple fields _ _, i => (fields[i]?).map (fun f => f.1.bytes)
  | _, _ => none

/-- **V1 Universal Agreement on the `(u64, u32, u32)` Tuple (all `locals`,
all `mem`)**: `size_of = 16`, `align_of = 8`, and `offset_of!(.2) = 12`,
never touching locals or memory. -/
theorem np_v1_nullary_tuple16_universal (locals : List LocalSlot) (mem : MirSemantics.Memory) :
    evalNullaryOp locals .sizeOf npTuple16MirTy mem [] emptyLayoutTable =
      .ok (.scalar ⟨16, 8⟩) locals mem ∧
    evalNullaryOp locals .alignOf npTuple16MirTy mem [] emptyLayoutTable =
      .ok (.scalar ⟨8, 8⟩) locals mem ∧
    evalNullaryOp locals (.offsetOf [(0, 2)]) npTuple16MirTy mem [] emptyLayoutTable =
      .ok (.scalar ⟨12, 8⟩) locals mem :=
  ⟨np_v1_nullary_sizeOf_of_intrinsic locals npTuple16MirTy mem [] emptyLayoutTable 16
     (by decide +kernel) (by decide +kernel),
   np_v1_nullary_alignOf_of_intrinsic locals npTuple16MirTy mem [] emptyLayoutTable 16 8
     (by decide +kernel) (by decide +kernel) (by decide +kernel),
   np_v1_nullary_offsetOf_of_intrinsic locals npTuple16MirTy mem [] emptyLayoutTable [(0, 2)] 16 12
     (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

/-- **V1 Universal Agreement on the Padded `{ u8, u32 }` Struct (all
`locals`, all `mem`)**: with the compiler layout recorded in `npLayouts`,
`offset_of!(.1) = 4` (3 padding bytes after the `u8`). -/
theorem np_v1_nullary_padded_offset_universal (locals : List LocalSlot)
    (mem : MirSemantics.Memory) :
    evalNullaryOp locals (.offsetOf [(0, 1)]) npPaddedMirTy mem
      [mkDecl usizeMirTy, mkDecl npPaddedMirTy] npLayouts =
      .ok (.scalar ⟨4, 8⟩) locals mem :=
  np_v1_nullary_offsetOf_of_intrinsic locals npPaddedMirTy mem
    [mkDecl usizeMirTy, mkDecl npPaddedMirTy] npLayouts [(0, 1)] 8 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **V1 Fail-Closed Boundary on Unsized Types (all `locals`, all `mem`)**:
`size_of`, `align_of`, and `offset_of!` on `[u32]`, `str`, and `dyn Trait`
are `.unsupported`. -/
theorem np_v1_nullary_unsized_unsupported (locals : List LocalSlot) (mem : MirSemantics.Memory)
    (fields : List (VariantIdx × FieldIdx)) :
    (evalNullaryOp locals .sizeOf sliceU32MirTy mem [] emptyLayoutTable = .unsupported ∧
     evalNullaryOp locals .alignOf sliceU32MirTy mem [] emptyLayoutTable = .unsupported ∧
     evalNullaryOp locals (.offsetOf fields) sliceU32MirTy mem [] emptyLayoutTable = .unsupported) ∧
    (evalNullaryOp locals .sizeOf strMirTy mem [] emptyLayoutTable = .unsupported ∧
     evalNullaryOp locals .alignOf strMirTy mem [] emptyLayoutTable = .unsupported ∧
     evalNullaryOp locals (.offsetOf fields) strMirTy mem [] emptyLayoutTable = .unsupported) ∧
    (evalNullaryOp locals .sizeOf { kind := .dynamic "np::Tr", layoutIdx := 0 } mem []
       emptyLayoutTable = .unsupported ∧
     evalNullaryOp locals .alignOf { kind := .dynamic "np::Tr", layoutIdx := 0 } mem []
       emptyLayoutTable = .unsupported ∧
     evalNullaryOp locals (.offsetOf fields) { kind := .dynamic "np::Tr", layoutIdx := 0 } mem []
       emptyLayoutTable = .unsupported) :=
  ⟨np_v1_nullary_unsupported_of_unresolved_size locals sliceU32MirTy mem [] emptyLayoutTable fields
     (by decide +kernel),
   np_v1_nullary_unsupported_of_unresolved_size locals strMirTy mem [] emptyLayoutTable fields
     (by decide +kernel),
   np_v1_nullary_unsupported_of_unresolved_size locals
     { kind := .dynamic "np::Tr", layoutIdx := 0 } mem [] emptyLayoutTable fields
     (by decide +kernel)⟩

/-- **V1 MiniRust Layout & Field-Offset Agreement**: MiniRust `Type.layout`
(`LayoutStrategy.Sized`) and `Tuple` field offsets of the lowered types carry
exactly the numbers `evalNullaryOp` returns (`16`/`8`/`12` and `8`/`4`/`4`). -/
theorem np_v1_minirust_layout_and_offset_agreement :
    Type.layout npTuple16MrTy = .ok (.Sized ⟨16⟩ ⟨8⟩) ∧
    npTupleFieldOffset npTuple16MrTy 2 = some 12 ∧
    Type.layout npPaddedU8U32MrTy = .ok (.Sized ⟨8⟩ ⟨4⟩) ∧
    npTupleFieldOffset npPaddedU8U32MrTy 1 = some 4 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **V1 MiniRust `UnOp.ComputeSize` / `UnOp.ComputeAlign` Law (`Mach` &
`MachTB`)**: MiniRust computes sizes and alignments from a type and its
pointer metadata (Episode 1); for a sized type the metadata is `()` and the
result is the type's static size and alignment, for a slice it is scaled by
the element count. -/
abbrev np_v1_minirust_metadata_sized_boundary := @evalUnOpM_rawPtr_meta_size_align

/-- MiniRust machine for `v1NullaryTupleMir`: `size_of` and `align_of` are
`UnOp.ComputeSize` / `UnOp.ComputeAlign` on `npTuple16MrTy` with unit
metadata, `offset_of!(.2)` is the constant field offset of `npTuple16MrTy`,
and the two additions are `BinOp.Int Add`. -/
def v1NullaryTupleMach : Mach :=
  let fn := mkMrFn
    [(localName 0, usizeMrTy), (localName 1, usizeMrTy), (localName 2, usizeMrTy),
     (localName 3, usizeMrTy), (localName 4, usizeMrTy)] [] (localName 0)
    [(bbName 0, ⟨[
        .Assign (.Local (localName 1)) (.UnOp (.ComputeSize npTuple16MrTy) (.Tuple [] unitType)),
        .Assign (.Local (localName 2)) (.UnOp (.ComputeAlign npTuple16MrTy) (.Tuple [] unitType)),
        .Assign (.Local (localName 3))
          (.Constant (.Int (((npTupleFieldOffset npTuple16MrTy 2).getD 0 : Nat) : Int)) usizeMrTy),
        .Assign (.Local (localName 4))
          (.BinOp (.Int .Add) (.Load (.Local (localName 1))) (.Load (.Local (localName 2)))),
        .Assign (.Local (localName 0))
          (.BinOp (.Int .Add) (.Load (.Local (localName 4))) (.Load (.Local (localName 3))))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 256 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 384 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 512 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 640 (List.replicate 8 .Uninit) 8]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }),
       (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) }),
       (localName 3, { addr := 512, provenance := some (⟨3⟩, ()) }),
       (localName 4, { addr := 640, provenance := some (⟨4⟩, ()) })]]

/-- MiniRust machine for `v1NullaryUbChecksMir` (`ub_checks` lowered to the
constant `true`). -/
def v1NullaryUbChecksMach : Mach :=
  let fn := mkMrFn [(localName 0, .Bool)] [] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0)) (.Constant (.Bool true) .Bool)],
                 .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) [mkStackAlloc 128 (List.replicate 1 .Uninit) 1]
    [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]]

/-- MiniRust machine for `v1NullaryUbBranchMir`: the `ub_checks` flag (the
integer value `1` of `true`) is the `Switch` scrutinee selecting the
`Unreachable` block. -/
def v1NullaryUbBranchMach : Mach :=
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, u8MrTy)] [] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 1)) (.Constant (.Int 1) u8MrTy)],
                 .Switch (.Load (.Local (localName 1))) ⟨[((1 : Int), bbName 1)]⟩ (bbName 2),
                 .Regular⟩),
     (bbName 1, ⟨[], .Unreachable, .Regular⟩),
     (bbName 2, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 0) u32MrTy)],
                 .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (List.replicate 1 .Uninit) 1]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]

/-- MiniRust machine for `v1NullaryPaddedOffsetMir`: `offset_of!(.1)` is the
constant field offset of `npPaddedU8U32MrTy`. -/
def v1NullaryPaddedOffsetMach : Mach :=
  let fn := mkMrFn [(localName 0, usizeMrTy)] [] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0))
        (.Constant (.Int (((npTupleFieldOffset npPaddedU8U32MrTy 1).getD 0 : Nat) : Int)) usizeMrTy)],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) [mkStackAlloc 128 (List.replicate 8 .Uninit) 8]
    [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]]

/-- **V1 Concrete Three-Way Witness (Trusted, `Mach`, `MachTB` with
`MachTB.wfLive`)**: `16 + 8 + 12 = 36` (with the three MiniRust intermediate
results `ComputeSize = 16`, `ComputeAlign = 8`, field offset `12`),
`ub_checks = true`, the `ub_checks` branch into `Unreachable` UB, and the
padded field offset `4`. -/
theorem np_v1_nullaryOp_three_way_witness :
    npRunTrusted v1NullaryTupleMir 16 (npInitLiveState v1NullaryTupleMir []) = .usizeVal 36 ∧
    (∃ m5, Interp.steps 5 v1NullaryTupleMach = .ok m5 ∧
      ([1, 2, 3, 0].map (fun i => m5.mem.memory.allocations[i]?.map (·.data))) =
        [some (scalarBytes IntType.usize_ty 16), some (scalarBytes IntType.usize_ty 8),
         some (scalarBytes IntType.usize_ty 12), some (scalarBytes IntType.usize_ty 36)]) ∧
    (∃ m5, Interp.stepsTB 5 (liftMachToTB v1NullaryTupleMach) = .ok m5 ∧ MachTB.wfLive m5 ∧
      m5.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes IntType.usize_ty 36).map (projByteTB ∘ liftByteTB))) ∧
    npRunTrusted v1NullaryUbChecksMir 16 (npInitLiveState v1NullaryUbChecksMir []) = .u8Val 1 ∧
    (∃ m1, Interp.step v1NullaryUbChecksMach = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some ([.Init 1 none] : List Byte)) ∧
    (∃ m1, Interp.stepTB (liftMachToTB v1NullaryUbChecksMach) = .ok m1 ∧ MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ([.initNoProv 1] : List TBByteOutcome)) ∧
    npRunTrusted v1NullaryUbBranchMir 16 (npInitLiveState v1NullaryUbBranchMir []) = .ub ∧
    Interp.steps 3 v1NullaryUbBranchMach = .error (.ub "reached unreachable code") ∧
    Interp.stepsTB 3 (liftMachToTB v1NullaryUbBranchMach) =
      .error (.ub "reached unreachable code") ∧
    npRunTrusted v1NullaryPaddedOffsetMir 16 (npInitLiveState v1NullaryPaddedOffsetMir []) =
      .usizeVal 4 ∧
    (∃ m1, Interp.step v1NullaryPaddedOffsetMach = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes IntType.usize_ty 4)) ∧
    (∃ m1, Interp.stepTB (liftMachToTB v1NullaryPaddedOffsetMach) = .ok m1 ∧ MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes IntType.usize_ty 4).map (projByteTB ∘ liftByteTB))) :=
  ⟨by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepTB_wfLive (by decide +kernel),
   by decide +kernel,
   eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel),
   by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepTB_wfLive (by decide +kernel)⟩

/-! ## §3 (`V2`): `CastKind.pointerCoercion` — all 6 coercions (`Mach` & `MachTB`) -/

/-- **V2 Universal Dispatch Law**: `evalRvalue` evaluates every
`CastKind.pointerCoercion ck` by `evalReifyFnPointer … ck`; `"Unsize"`
dispatches to `evalUnsizeCoercion`, `"UnsafeFnPointer"` to
`evalUnsafeFnPointer`, and an unknown coercion kind is fail-closed
`.unsupported`. -/
theorem np_v2_pointerCoercion_dispatch (locals : List LocalSlot) (op : MirAst.Operand)
    (ty : MirAst.Ty) (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl)
    (layouts : LayoutTable) :
    (∀ ck, evalRvalue locals (.cast (.pointerCoercion ck) op ty) mem decls layouts =
      evalReifyFnPointer locals op ty mem decls layouts ck) ∧
    evalReifyFnPointer locals op ty mem decls layouts "Unsize" =
      evalUnsizeCoercion locals op ty mem decls layouts ∧
    evalReifyFnPointer locals op ty mem decls layouts "UnsafeFnPointer" =
      evalUnsafeFnPointer locals op ty mem decls layouts ∧
    evalReifyFnPointer locals op ty mem decls layouts "np::UnknownCoercion" = .unsupported :=
  ⟨fun _ => rfl, rfl, rfl, rfl⟩

/-- **V2 Fragment Boundary**: `Translate.translateRvalue` returns `none` on
every `CastKind.pointerCoercion`. -/
abbrev np_v2_translateRvalue_pointerCoercion_none := @translateRvalue_pointerCoercion_none

/-- **V2.1 & V2.2 (`"ReifyFnPointer"` & `"ClosureFnPointer"`) Universal
Two-Sided Lockstep (`Mach` & `MachTB`)**. -/
abbrev np_v2_reify_and_closure_fnPointer_lockstep := @reify_and_closure_fnPointer_lockstep_M

/-- **V2.1 Cached Reification & `fnFromPtrM` Round-Trip (`Mach` & `MachTB`)**. -/
abbrev np_v2_reify_cached_and_fnFromPtrM_roundtrip := @reify_cached_and_fnFromPtrM_roundtrip

/-- **V2.3 (`"UnsafeFnPointer"`) Universal Ground Truth & Divergences**. -/
abbrev np_v2_unsafeFnPointer_ground_truth_and_divergences :=
  @unsafeFnPointer_ground_truth_and_divergences

/-- **V2.3 (`"UnsafeFnPointer"`) Pointer & Signature UB Law**. -/
abbrev np_v2_unsafeFnPointer_ptr_and_sig_ub := @unsafeFnPointer_ptr_and_sig_ub

/-- **V2.4 (`"MutToConstPointer"`) Universal Shape Preservation across all 6
runtime pointer shapes (thin, wide slice, AND wide `dyn Trait` data + vtable
pointers) on `Mach` & `MachTB`**: the universal `dyn Trait` wide-pointer
bridge. -/
abbrev np_v2_mutToConstPointer_all_shapes_and_ub := @mutToConstPointer_all_shapes_and_ub

/-- **V2.5 (`"ArrayToPointer"`) Universal Global / Stack / Scalar Law & UB**. -/
abbrev np_v2_arrayToPointer_global_stack_scalar_and_ub :=
  @arrayToPointer_global_stack_scalar_and_ub

/-- **V2 Composition (`Reify -> UnsafeFnPointer -> fnPtrToPtr`)**. -/
abbrev np_v2_reify_unsafe_fnPtrToPtr_pipeline := @reify_unsafe_fnPtrToPtr_pipeline

/-- **V2 End-to-End Witness over the 5 non-`Unsize` coercions (Trusted,
`Mach`, `MachTB`)**. -/
abbrev np_v2_all_five_pointer_coercions_three_way_witness :=
  @c8_all_five_pointer_coercions_three_way_witness

/-- MiniRust function for `v2PtrCoerceFnPipelineMir`: `ReifyFnPointer` is the
constant `FnPointer`, `UnsafeFnPointer` the identity `Transmute`. -/
def v2FnPipelineMrFn : Gen.Function :=
  mkMrFn [(localName 0, thinRawPtrTy), (localName 1, thinRawPtrTy)] [] (localName 0)
    [(bbName 0, ⟨[
        .Assign (.Local (localName 1)) (.Constant (.FnPointer (fnName 1)) thinRawPtrTy),
        .Assign (.Local (localName 0))
          (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 1))))],
      .Return, .Regular⟩)]

/-- MiniRust machine for `v2PtrCoerceFnPipelineMir`. Allocation `0` is the
target function (at `4096`), `1` the return local, `2` local `_1`. -/
def v2FnPipelineMach : Mach :=
  let targetFn := mkMrFn [] [] (localName 0) [(bbName 0, ⟨[], .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, v2FnPipelineMrFn), (fnName 1, targetFn)])
    [mkFnAlloc 4096,
     mkStackAlloc 128 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 256 (List.replicate 8 .Uninit) 8]
    [mkRootFrame v2FnPipelineMrFn
      [(localName 0, { addr := 128, provenance := some (⟨1⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨2⟩, ()) })]]
    [(fnName 1, { addr := 4096, provenance := some (⟨0⟩, ()) })]

/-- MiniRust machine for `v2PtrCoerceDeadUbMir` (`StorageDead _1`, then the
`MutToConstPointer` `Transmute` loads the dead local). -/
def v2DeadUbMach : Mach :=
  let fn := mkMrFn [(localName 0, thinRawPtrTy), (localName 1, thinRawPtrTy)] [] (localName 0)
    [(bbName 0, ⟨[
        .StorageDead (localName 1),
        .Assign (.Local (localName 0))
          (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 1))))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 256 (ptrBytes 1024 (some (⟨2⟩, ()))) 8,
     mkStackAlloc 1024 (List.replicate 12 .Uninit) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]

/-- MiniRust machine for `v2PtrCoerceArrayToPtrMir`: `ArrayToPointer` is the
`Transmute` of the thin `*const [u32; 3]` (to allocation `2`, the 12-byte
array at `1024`) to the thin `*const u32`. -/
def v2ArrayToPtrMach : Mach :=
  let fn := mkMrFn [(localName 0, thinRawPtrTy), (localName 1, thinRawPtrTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .Assign (.Local (localName 0))
          (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 1))))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 256 (ptrBytes 1024 (some (⟨2⟩, ()))) 8,
     mkStackAlloc 1024 (scalarBytes u32 10 ++ scalarBytes u32 20 ++ scalarBytes u32 30) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]

/-- **V2 Concrete Three-Way Witness on the Corpus Fixtures (Trusted, `Mach`,
`MachTB` with `MachTB.wfLive`)**:
1. `ReifyFnPointer -> UnsafeFnPointer` yields the function pointer
   (Trusted allocation `65536`; MiniRust function allocation `0` at `4096`);
2. `Unsize` `*const [u32; 3] -> *const [u32]` then `PtrMetadata` yields `3`
   (MiniRust: the wide pointer built from `(data, 3)`, then Episode 1's
   `UnOp.GetMetadata`);
3. `MutToConstPointer` on a dead local is UB;
4. `ArrayToPointer` preserves the pointer provenance. -/
theorem np_v2_pointerCoercion_three_way_witness :
    npRunTrusted v2PtrCoerceFnPipelineMir 16 npFnPipelineInitState = .ptrAlloc 65536 ∧
    (∃ m2, Interp.steps 2 v2FnPipelineMach = .ok m2 ∧
      ([2, 1].map (fun i => m2.mem.memory.allocations[i]?.map (·.data))) =
        [some (ptrBytes 4096 (some (⟨0⟩, ()))), some (ptrBytes 4096 (some (⟨0⟩, ())))]) ∧
    (∃ m2, Interp.stepsTB 2 (liftMachToTB v2FnPipelineMach) = .ok m2 ∧ MachTB.wfLive m2 ∧
      m2.mem.memory.mem.allocations[1]?.map (fun a => a.data.map projByteTB) =
        some ((ptrBytes 4096 (some (⟨0⟩, ()))).map (projByteTB ∘ liftByteTB))) ∧
    npRunTrusted v2PtrCoerceUnsizeSliceMir 16
      (npInitLiveState v2PtrCoerceUnsizeSliceMir [.ptr { allocId := 5, offsetBytes := 0 } 8]) =
      .usizeVal 3 ∧
    (∃ m4, Interp.steps 4 (v7RawPtrWideMach u32MrTy 3) = .ok m4 ∧
      m4.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes IntType.usize_ty 3)) ∧
    (∃ m4, Interp.stepsTB 4 (liftMachToTB (v7RawPtrWideMach u32MrTy 3)) = .ok m4 ∧
      MachTB.wfLive m4 ∧
      m4.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes IntType.usize_ty 3).map (projByteTB ∘ liftByteTB))) ∧
    npRunTrusted v2PtrCoerceDeadUbMir 16
      (initMachineState v2PtrCoerceDeadUbMir [.ptr { allocId := 5, offsetBytes := 0 } 8]) = .ub ∧
    Interp.steps 2 v2DeadUbMach = .error (.ub "access to a dead local") ∧
    Interp.stepsTB 2 (liftMachToTB v2DeadUbMach) = .error (.ub "access to a dead local") ∧
    npRunTrusted v2PtrCoerceArrayToPtrMir 16
      (initMachineState v2PtrCoerceArrayToPtrMir [.ptr { allocId := 5, offsetBytes := 0 } 8]) =
      .ptrAlloc 5 ∧
    (∃ m1, Interp.step v2ArrayToPtrMach = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some (ptrBytes 1024 (some (⟨2⟩, ())))) ∧
    (∃ m1, Interp.stepTB (liftMachToTB v2ArrayToPtrMach) = .ok m1 ∧ MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((ptrBytes 1024 (some (⟨2⟩, ()))).map (projByteTB ∘ liftByteTB))) :=
  ⟨by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   by decide +kernel,
   eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel),
   by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepTB_wfLive (by decide +kernel)⟩

/-! ### `dyn Trait` Unsizing / Wide-Pointer Bridge (`Mach` & `MachTB`)

`MiniRustSpec.Interp` keeps `BinOp.ConstructWidePointer` fail-closed
(`.unsupported`), so the unsizing coercion `*const T -> *const dyn Trait` is
lowered the way Episode 1 builds trait-object pointers: the raw 16-byte pair
`(data pointer, vtable pointer)` is written into the wide-pointer local. Every
later `Load` of that local runs `Machine::vtable_from_ptr` and the trait check
of `check_ptr` (`vtableFromPtrM`, `checkPtrM`); `UnOp.GetMetadata` extracts the
vtable pointer, and `UnOp.ComputeSize`, `UnOp.ComputeAlign`, and
`UnOp.VTableMethodLookup` read the vtable (`evalUnOpM`). -/

/-- MiniRust `dyn Trait0` type. -/
@[reducible] def npDynTraitMrTy : Gen.Type := .TraitObject (traitNameOf 0)

/-- MiniRust function unsizing the thin data pointer `_1` to the
`*const dyn Trait0` local `_2`, then reading its vtable-backed size (`_0`),
alignment (`_3`), and method `0` (`_4`). -/
def npDynUnsizeMrFn : Gen.Function :=
  mkMrFn
    [(localName 0, usizeMrTy), (localName 1, thinRawPtrTy), (localName 2, wideDynPtrMrTy 0),
     (localName 3, usizeMrTy), (localName 4, thinRawPtrTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .Assign (.Deref (.AddrOf (.Local (localName 2)) (.Raw .None)) rawDynPairMrTy)
          (.Tuple [.Load (.Local (localName 1)),
            .UnOp .GetThinPointer
              (.Constant (.VTablePointer ⟨⟨0⟩⟩) (.Ptr (.VTablePtr (traitNameOf 0))))]
            rawDynPairMrTy),
        .Assign (.Local (localName 0))
          (.UnOp (.ComputeSize npDynTraitMrTy) (.UnOp .GetMetadata (.Load (.Local (localName 2))))),
        .Assign (.Local (localName 3))
          (.UnOp (.ComputeAlign npDynTraitMrTy) (.UnOp .GetMetadata (.Load (.Local (localName 2))))),
        .Assign (.Local (localName 4))
          (.UnOp (.VTableMethodLookup dynDispatchMethod)
            (.UnOp .GetMetadata (.Load (.Local (localName 2)))))],
      .Return, .Regular⟩)]

/-- MiniRust machine for the `dyn Trait` unsizing bridge. Allocation `0` is
function `1` (at `4096`), `1` the `usize` return local, `2` the thin data
pointer local, `3` the vtable of trait `0` (size `4`, alignment `4`, registered
at `8192`), `4` the 4-byte data object at `640`, `5` the wide-pointer local,
`6` the alignment local, and `7` the method-pointer local. -/
def npDynUnsizeMach : Mach :=
  let prog : Gen.Program :=
    { functions := ⟨[(fnName 0, npDynUnsizeMrFn), (fnName 1, dynDispatchCallee)]⟩,
      start := fnName 0, globals := ⟨[]⟩,
      traits := ⟨[(traitNameOf 0, ⟨[dynDispatchMethod]⟩)]⟩,
      vtables := ⟨[(⟨⟨0⟩⟩, dynDispatchVTable)]⟩ }
  let vtPtr : Ptr := { addr := 8192, provenance := some (⟨3⟩, ()) }
  let base := mkMrMach prog
    [mkFnAlloc 4096,
     mkStackAlloc 128 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 256 (ptrBytes 640 (some (⟨4⟩, ()))) 8,
     mkVTableAlloc 8192,
     mkHeapAlloc 640 (scalarBytes u32 5) 4,
     mkStackAlloc 384 (List.replicate 16 .Uninit) 8,
     mkStackAlloc 512 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 768 (List.replicate 8 .Uninit) 8]
    [mkRootFrame npDynUnsizeMrFn
      [(localName 0, { addr := 128, provenance := some (⟨1⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨2⟩, ()) }),
       (localName 2, { addr := 384, provenance := some (⟨5⟩, ()) }),
       (localName 3, { addr := 512, provenance := some (⟨6⟩, ()) }),
       (localName 4, { addr := 768, provenance := some (⟨7⟩, ()) })]]
    [(fnName 1, { addr := 4096, provenance := some (⟨0⟩, ()) })]
  { base with vtable_ptrs := ⟨[(⟨⟨0⟩⟩, vtPtr)]⟩ }

/-- **V2 Concrete `dyn Trait` Unsizing / Wide-Pointer Bridge (`Mach` &
`MachTB` with `MachTB.wfLive`)**: after 4 steps the wide-pointer local holds
`(data 640, vtable 8192)`, `ComputeSize(GetMetadata) = 4`,
`ComputeAlign(GetMetadata) = 4`, and `VTableMethodLookup(GetMetadata)` is the
function pointer of the vtable's method `0`. -/
theorem np_v2_dyn_unsize_wide_pointer_bridge_witness :
    (∃ m4, Interp.steps 4 npDynUnsizeMach = .ok m4 ∧
      ([5, 1, 6, 7].map (fun i => m4.mem.memory.allocations[i]?.map (·.data))) =
        [some (ptrBytes 640 (some (⟨4⟩, ())) ++ ptrBytes 8192 (some (⟨3⟩, ()))),
         some (scalarBytes IntType.usize_ty 4),
         some (scalarBytes IntType.usize_ty 4),
         some (ptrBytes 4096 (some (⟨0⟩, ())))]) ∧
    (∃ m4, Interp.stepsTB 4 (liftMachToTB npDynUnsizeMach) = .ok m4 ∧ MachTB.wfLive m4 ∧
      ([5, 1, 6, 7].map (fun i =>
        m4.mem.memory.mem.allocations[i]?.map (fun a => a.data.map projByteTB))) =
        [some ((ptrBytes 640 (some (⟨4⟩, ())) ++ ptrBytes 8192 (some (⟨3⟩, ()))).map
           (projByteTB ∘ liftByteTB)),
         some ((scalarBytes IntType.usize_ty 4).map (projByteTB ∘ liftByteTB)),
         some ((scalarBytes IntType.usize_ty 4).map (projByteTB ∘ liftByteTB)),
         some ((ptrBytes 4096 (some (⟨0⟩, ()))).map (projByteTB ∘ liftByteTB))]) :=
  ⟨ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel)⟩

/-- **V2 `dyn Trait` Dispatch & Invalid-Vtable UB (`Mach` & `MachTB`)**: the
Episode 1 witness that a wide trait-object pointer with registered vtable
metadata dispatches, while metadata that is not a vtable address, or the
vtable of another trait, is UB as soon as the pointer is loaded. -/
abbrev np_v2_dyn_dispatch_and_invalid_vtable_ub_witness :=
  @dynDispatch_call_mach_and_machTB_witness

/-- **V2 `dyn Trait` Pointer Memory Round-Trip & Misaligned Place (`Mach` &
`MachTB`)**. -/
abbrev np_v2_dyn_ptr_memory_roundtrip_witness :=
  @dynPtr_memory_roundtrip_and_misaligned_place_witness

/-! ## §4 (`V3`): `CastKind.fnPtrToPtr` (`Mach` & `MachTB`) -/

/-- **V3 Dispatch**: `evalRvalue` evaluates `CastKind.fnPtrToPtr` exactly by
`evalFnPtrToPtr`. -/
theorem np_v3_evalRvalue_fnPtrToPtr_eq (locals : List LocalSlot) (op : MirAst.Operand)
    (ty : MirAst.Ty) (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl)
    (layouts : LayoutTable) :
    evalRvalue locals (.cast .fnPtrToPtr op ty) mem decls layouts =
      evalFnPtrToPtr locals op ty mem decls layouts := rfl

/-- **V3 Fragment Boundary**: `Translate.translateRvalue` returns `none` on
`CastKind.fnPtrToPtr`. -/
abbrev np_v3_translateRvalue_fnPtrToPtr_none := @translateRvalue_fnPtrToPtr_none

/-- **V3 Universal Lockstep (`Mach` & `MachTB`)**: Trusted `evalFnPtrToPtr`
and MiniRust `Transmute` agree on every interned function pointer. -/
abbrev np_v3_fnPtrToPtr_lockstep_mach_and_tb := @fnPtrToPtr_lockstep_mach_and_tb

/-- **V3 Universal UB Fault Characterization**: non-zero offset, a stack
borrow tag, an unregistered or signature-mismatched allocation, a non-thin
target, and a scalar operand are all Trusted `.ub`. -/
abbrev np_v3_fnPtrToPtr_extra_checks_divergence := @fnPtrToPtr_extra_checks_divergence

/-- **V3 Concrete Three-Way Witness of the Shared Body Shape**. -/
abbrev np_v3_c6_fnPtrToPtr_three_way_and_ub_witness := @c6_fnPtrToPtr_three_way_and_ub_witness

/-- **V3 Trusted Step & UB Faults on the Corpus Fixture**: the cast preserves
the function pointer's `ProvenancePtr`; a dead operand, an uninitialized
operand, and a non-zero offset each fault with UB. -/
theorem np_v3_fnPtrToPtr_trusted_step_and_ub_witness :
    let fnPtr : ProvenancePtr := { allocId := fnPtrAllocBase, offsetBytes := 0 }
    let sOk := initMachineState v3FnPtrToPtrConstMir [.ptr fnPtr 8]
    let sDead : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .dead] },
        memory := (initMachineState v3FnPtrToPtrConstMir []).memory }
    let sNonzero :=
      initMachineState v3FnPtrToPtrConstMir [.ptr { allocId := fnPtrAllocBase, offsetBytes := 1 } 8]
    (match stepMirFn v3FnPtrToPtrConstMir sOk with
     | .tau (.running s1) => get? s1.frame.locals 0 = some (.init (.ptr fnPtr 8))
     | _ => False) ∧
    stepMirFn v3FnPtrToPtrConstMir sDead = MirStepNode.fail .ub ∧
    stepMirFn v3FnPtrToPtrConstMir npUninitFnPtrState = MirStepNode.fail .ub ∧
    stepMirFn v3FnPtrToPtrConstMir sNonzero = MirStepNode.fail .ub :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **V3 `rustIntrinsic` ABI UB**: casting a function pointer whose known
operand type has the `rustIntrinsic` calling convention is Trusted `.ub`. -/
theorem np_v3_fnPtrToPtr_rustIntrinsic_abi_ub :
    evalFnPtrToPtr [.uninit, .init (.ptr { allocId := fnPtrAllocBase, offsetBytes := 0 } 8)]
      (.copy (locPlace 1)) rawConstUnitMirTy emptyMemory
      [mkDecl rawConstUnitMirTy, mkDecl fnPtrIntrinsicU32MirTy] emptyLayoutTable = .ub := rfl

/-- MiniRust function for `v3FnPtrToPtrMutChainMir`: `fnPtrToPtr` then
`ptrToPtr`, both `Transmute` at the thin raw pointer type. -/
def v3MutChainMrFn : Gen.Function :=
  mkMrFn [(localName 0, thinRawPtrTy), (localName 1, thinRawPtrTy), (localName 2, thinRawPtrTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .Assign (.Local (localName 2))
          (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 1)))),
        .Assign (.Local (localName 0))
          (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 2))))],
      .Return, .Regular⟩)]

/-- MiniRust machine for `v3FnPtrToPtrMutChainMir`. Allocations `0` and `1`
are functions `1` (at `4096`) and `2` (at `8192`); local `_1` holds the
pointer to function `2`, the second interned function pointer. -/
def v3MutChainMach : Mach :=
  let targetFn := mkMrFn [] [] (localName 0) [(bbName 0, ⟨[], .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, v3MutChainMrFn), (fnName 1, targetFn), (fnName 2, targetFn)])
    [mkFnAlloc 4096, mkFnAlloc 8192,
     mkStackAlloc 128 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 256 (ptrBytes 8192 (some (⟨1⟩, ()))) 8,
     mkStackAlloc 384 (List.replicate 8 .Uninit) 8]
    [mkRootFrame v3MutChainMrFn
      [(localName 0, { addr := 128, provenance := some (⟨2⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨3⟩, ()) }),
       (localName 2, { addr := 384, provenance := some (⟨4⟩, ()) })]]
    [(fnName 1, { addr := 4096, provenance := some (⟨0⟩, ()) }),
     (fnName 2, { addr := 8192, provenance := some (⟨1⟩, ()) })]

/-- **V3 Concrete Three-Way Witness on the Corpus Fixtures (Trusted, `Mach`,
`MachTB` with `MachTB.wfLive`)**: the `*const ()` cast, the
`*mut u8 -> *const u32` chain on the second function pointer, and dead /
uninitialized operand UB. -/
theorem np_v3_fnPtrToPtr_three_way_witness :
    npRunTrusted v3FnPtrToPtrConstMir 16
      (initMachineState v3FnPtrToPtrConstMir [.ptr { allocId := 65536, offsetBytes := 0 } 8]) =
      .ptrAlloc 65536 ∧
    (∃ m1, Interp.step (c6FnPtrMach true) = .ok m1 ∧
      m1.mem.memory.allocations[1]?.map (·.data) = some (ptrBytes 4096 (some (⟨0⟩, ())))) ∧
    npRunTrusted v3FnPtrToPtrMutChainMir 16
      (npInitLiveState v3FnPtrToPtrMutChainMir [.ptr { allocId := 65537, offsetBytes := 0 } 8]) =
      .ptrAlloc 65537 ∧
    (∃ m2, Interp.steps 2 v3MutChainMach = .ok m2 ∧
      ([4, 2].map (fun i => m2.mem.memory.allocations[i]?.map (·.data))) =
        [some (ptrBytes 8192 (some (⟨1⟩, ()))), some (ptrBytes 8192 (some (⟨1⟩, ())))]) ∧
    (∃ m2, Interp.stepsTB 2 (liftMachToTB v3MutChainMach) = .ok m2 ∧ MachTB.wfLive m2 ∧
      m2.mem.memory.mem.allocations[2]?.map (fun a => a.data.map projByteTB) =
        some ((ptrBytes 8192 (some (⟨1⟩, ()))).map (projByteTB ∘ liftByteTB))) ∧
    npRunTrusted v3FnPtrToPtrDeadUbMir 16
      (initMachineState v3FnPtrToPtrDeadUbMir [.ptr { allocId := 65536, offsetBytes := 0 } 8]) =
      .ub ∧
    Interp.step (c6FnPtrMach false) = .error (.ub "access to a dead local") ∧
    Interp.stepTB (liftMachToTB (c6FnPtrMach false)) = .error (.ub "access to a dead local") ∧
    npRunTrusted v3FnPtrToPtrConstMir 16 npUninitFnPtrState = .ub ∧
    (interpUbMsg (Interp.step (c6FnPtrMach true false))).isSome = true ∧
    (interpUbMsg (Interp.stepTB (liftMachToTB (c6FnPtrMach true false)))).isSome = true :=
  ⟨by decide +kernel,
   ok_of_map_toOption (by decide +kernel),
   by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   by decide +kernel,
   eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel),
   by decide +kernel,
   by decide +kernel, by decide +kernel⟩

/-! ## §5 (`V4`): `ProjectionElem.unwrapUnsafeBinder` (`Mach` & `MachTB`) -/

/-- **V4 Fragment Boundary**: `Translate.translatePlace` returns `none` on
`ProjectionElem.unwrapUnsafeBinder`. -/
abbrev np_v4_translatePlace_unwrapUnsafeBinder_none := @translatePlace_unwrapUnsafeBinder_none

/-- **V4 Trusted Universal Transparency**: `.unwrapUnsafeBinder` is
transparent across projected reads, writes, union-aware reads, and
`Rvalue.len`. -/
abbrev np_v4_trusted_unwrapUnsafeBinder_transparent := @trusted_unwrapUnsafeBinder_transparent

/-- **V4 MiniRust Binder Wrapper Codec (`Mach` & `MachTB`)**: the single-field
wrapper `Transmute` on `u32` and thin pointers. -/
abbrev np_v4_transmuteM_binderWrapper_u32_and_thinPtr := @transmuteM_binderWrapper_u32_and_thinPtr

/-- **V4 MiniRust Field-0 Place Projection of the Binder Wrapper (`Mach` &
`MachTB`)**. -/
abbrev np_v4_minirust_evalPlaceM_binderWrapper_field0 := @minirust_evalPlaceM_binderWrapper_field0

/-- **V4 Universal Coupled `Assign` Lockstep through `.unwrapUnsafeBinder`
(`Mach` & `MachTB`, preserving `MachTB.wfLive`)**. -/
abbrev np_v4_unwrapUnsafeBinder_assign_coupled_lockstep_and_wfLive :=
  @unwrapUnsafeBinder_assign_coupled_lockstep_and_wfLive

/-- **V4 Uninitialized-Wrapper `Assign` & `Move` Laws**. -/
abbrev np_v4_unwrapUnsafeBinder_uninit_assign_and_move := @unwrapUnsafeBinder_uninit_assign_and_move

/-- **V4 `wrapUnsafeBinder` Universal Simulation (transparent targets and
single-field `binderStructLayout?` structs)**. -/
abbrev np_v4_wrapUnsafeBinder_universal_sim := @v5_wrapUnsafeBinder_universal_sim

/-- **V4 `wrapUnsafeBinder` Single-Field `NonZeroU8` Struct Coupled
Simulation (`Mach` & `MachTB`)**. -/
abbrev np_v4_wrapUnsafeBinder_struct_nonZero_coupled_sim :=
  @v5_wrapUnsafeBinder_struct_nonZero_coupled_valRel_sim

/-- **V4 Concrete Read / Write / `Move` / Deref / `Rvalue.len` Witness of the
transparent projection**. -/
abbrev np_v4_c9_unwrapUnsafeBinder_three_way_witness :=
  @c9_unwrapUnsafeBinder_three_way_len_and_ub_witness

/-- MiniRust machine for `v4UnwrapBinderRoundtripMir`: wrap `_1` into the
single-field wrapper `_2`, overwrite the wrapped field with `73`, read it back. -/
def v4RoundtripMach : Mach :=
  let wrapTy := mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, u32MrTy), (localName 2, wrapTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .Assign (.Local (localName 2)) (.Tuple [.Load (.Local (localName 1))] wrapTy),
        .Assign (.Field (.Local (localName 2)) 0) (.Constant (.Int 73) u32MrTy),
        .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 2)) 0))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (scalarBytes u32 10) 4,
     mkStackAlloc 384 (List.replicate 4 .Uninit) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }),
       (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })]]

/-- MiniRust machine for `v4UnwrapBinderDeadUbMir` (`StorageDead _1`, then
read the wrapped field of the dead wrapper local). -/
def v4DeadUbMach : Mach :=
  let wrapTy := mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, wrapTy)] [] (localName 0)
    [(bbName 0, ⟨[
        .StorageDead (localName 1),
        .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 0))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (scalarBytes u32 11) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]

/-- MiniRust machine for `v4UnwrapBinderProtectedMir` (genuine `Mach` vs.
`MachTB` mode sensitivity): `Validate (.Local _2) true` installs a Tree
Borrows protector on the `&u32` in `_2` pointing at the wrapped field of `_1`.
`BasicMemory` ignores `Validate`, so the write through the unwrapped field
succeeds and `42` is read back; `TreeBorrowsMemory` enforces the protector, so
that write is a protector conflict. -/
def v4ProtectedMach : Mach :=
  let wrapTy := mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, wrapTy), (localName 2, refTy .not u32)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .Validate (.Local (localName 2)) true,
        .Assign (.Field (.Local (localName 1)) 0) (.Constant (.Int 42) u32MrTy),
        .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 0))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (scalarBytes u32 11) 4,
     mkStackAlloc 384 (ptrBytes 256 (some (⟨1⟩, ()))) 8]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }),
       (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })]]

/-- **V4 Concrete Three-Way Witness on the Corpus Fixtures (Trusted, `Mach`,
`MachTB` with `MachTB.wfLive`)**:
1. `wrapUnsafeBinder -> unwrapUnsafeBinder` write/read round-trip (`73`);
2. `NonZeroU8` binder struct read through the transparent projection (`7`);
3. dead-local UB;
4. active-protector write conflict: Trusted `basic` and `Mach` return `42`,
   Trusted `protectedTB` and `MachTB` fault with UB. -/
theorem np_v4_unwrapUnsafeBinder_three_way_witness :
    npRunTrusted v4UnwrapBinderRoundtripMir 16
      (npInitLiveState v4UnwrapBinderRoundtripMir [.scalar ⟨10, 4⟩]) = .u32Val 73 ∧
    (∃ m3, Interp.steps 3 v4RoundtripMach = .ok m3 ∧
      m3.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 73)) ∧
    (∃ m3, Interp.stepsTB 3 (liftMachToTB v4RoundtripMach) = .ok m3 ∧ MachTB.wfLive m3 ∧
      m3.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 73).map (projByteTB ∘ liftByteTB))) ∧
    npRunTrusted v4UnwrapBinderNzU8Mir 16
      (npInitLiveState v4UnwrapBinderNzU8Mir [.scalar ⟨7, 1⟩]) = .u8Val 7 ∧
    (∃ m1, Interp.step (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 7 none] 1) = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some ([.Init 7 none] : List Byte)) ∧
    npRunTrusted v4UnwrapBinderDeadUbMir 16
      (initMachineState v4UnwrapBinderDeadUbMir [.aggregate 0 [.scalar ⟨11, 4⟩]]) = .ub ∧
    Interp.steps 2 v4DeadUbMach = .error (.ub "access to a dead local") ∧
    Interp.stepsTB 2 (liftMachToTB v4DeadUbMach) = .error (.ub "access to a dead local") ∧
    npRunTrusted v4UnwrapBinderProtectedMir 16 (v4UnwrapBinderProtectedInitState false) =
      .u32Val 42 ∧
    npRunTrusted v4UnwrapBinderProtectedMir 16 (v4UnwrapBinderProtectedInitState true) = .ub ∧
    (∃ m3, Interp.steps 3 v4ProtectedMach = .ok m3 ∧
      m3.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 42)) ∧
    (interpUbMsg (Interp.stepsTB 3 (liftMachToTB v4ProtectedMach))).isSome = true :=
  ⟨by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   by decide +kernel,
   ok_of_map_toOption (by decide +kernel),
   by decide +kernel,
   eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel),
   by decide +kernel, by decide +kernel,
   ok_of_map_toOption (by decide +kernel),
   by decide +kernel⟩

/-! ## §6. Canonical Executable MiniRust Corpus Observation Interface

Directly executes `MiniRustSpec.Interp.{steps, stepsTB}` for all 4 MIR
variants (normal returns, UB faults, and `Mach` vs. `MachTB` mode
sensitivity) without any shadow evaluator, so
`Anneal.Mir.NullaryAndPtrCoercionBundle` can wire `MiniRustSpec.Interp`
directly into `DualCorrespondenceBundle`. -/

/-- MiniRust execution mode: `BasicMemory` (`Mach`) versus `TreeBorrowsMemory` (`MachTB`). -/
inductive NullaryPtrMrMode : Type where
  | basicMemory
  | treeBorrows
  deriving DecidableEq, Repr

/-- Raw authority-typed observation produced directly by `MiniRustSpec.Interp`:
the bytes (with provenance) of the return allocation, or the fault class. -/
inductive NullaryPtrMrObs : Type where
  | retBytes (bs : List TBByteOutcome)
  | ub
  | unsupported
  deriving DecidableEq

/-- Run `n` steps of `MiniRustSpec.Interp` in mode `mode` and extract allocation
`allocIdx`'s observable bytes (`projByteTB`), or `.ub` / `.unsupported`. -/
def npRunMrObs (mode : NullaryPtrMrMode) (n : Nat) (allocIdx : Nat) (m : Mach) : NullaryPtrMrObs :=
  match mode with
  | .basicMemory =>
    match Interp.steps n m with
    | .ok m' =>
      match m'.mem.memory.allocations[allocIdx]? with
      | some a => .retBytes (a.data.map (projByteTB ∘ liftByteTB))
      | none => .unsupported
    | .error (.ub _) => .ub
    | .error _ => .unsupported
  | .treeBorrows =>
    match Interp.stepsTB n (liftMachToTB m) with
    | .ok m' =>
      match m'.mem.memory.mem.allocations[allocIdx]? with
      | some a => .retBytes (a.data.map projByteTB)
      | none => .unsupported
    | .error (.ub _) => .ub
    | .error _ => .unsupported

/-- Direct `MiniRustSpec.Interp` observation for every `(mode, variant, case)`
key. Every entry executes the actual MiniRust interpreter (`Interp.steps` or
`Interp.stepsTB`) on a concrete `Mach` / `MachTB` machine. -/
def npMrObserve (mode : NullaryPtrMrMode) (v : NullaryPtrVariant) (c : NullaryPtrCase) :
    NullaryPtrMrObs :=
  match v, c with
  | .nullaryOp, .okPrimary => npRunMrObs mode 5 0 v1NullaryTupleMach
  | .nullaryOp, .okSecondary => npRunMrObs mode 1 0 v1NullaryUbChecksMach
  | .nullaryOp, .ubFault => npRunMrObs mode 3 0 v1NullaryUbBranchMach
  | .nullaryOp, .modeCase => npRunMrObs mode 1 0 v1NullaryPaddedOffsetMach
  | .pointerCoercion, .okPrimary => npRunMrObs mode 2 1 v2FnPipelineMach
  | .pointerCoercion, .okSecondary => npRunMrObs mode 4 0 (v7RawPtrWideMach u32MrTy 3)
  | .pointerCoercion, .ubFault => npRunMrObs mode 2 0 v2DeadUbMach
  | .pointerCoercion, .modeCase => npRunMrObs mode 1 0 v2ArrayToPtrMach
  | .fnPtrToPtr, .okPrimary => npRunMrObs mode 1 1 (c6FnPtrMach true)
  | .fnPtrToPtr, .okSecondary => npRunMrObs mode 2 2 v3MutChainMach
  | .fnPtrToPtr, .ubFault => npRunMrObs mode 1 1 (c6FnPtrMach false)
  | .fnPtrToPtr, .modeCase => npRunMrObs mode 1 1 (c6FnPtrMach true false)
  | .unwrapUnsafeBinder, .okPrimary => npRunMrObs mode 3 0 v4RoundtripMach
  | .unwrapUnsafeBinder, .okSecondary =>
    npRunMrObs mode 1 0 (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 7 none] 1)
  | .unwrapUnsafeBinder, .ubFault => npRunMrObs mode 2 0 v4DeadUbMach
  | .unwrapUnsafeBinder, .modeCase => npRunMrObs mode 3 0 v4ProtectedMach

/-- Mode sensitivity certified directly on `npMrObserve`:
`unwrapUnsafeBinder.modeCase` returns `42` under `BasicMemory` (`Mach`) and
faults `.ub` under `TreeBorrowsMemory` (`MachTB`). -/
theorem npMrObserve_unwrap_mode_sensitivity :
    npMrObserve .basicMemory .unwrapUnsafeBinder .modeCase =
      .retBytes ((scalarBytes u32 42).map (projByteTB ∘ liftByteTB)) ∧
    npMrObserve .treeBorrows .unwrapUnsafeBinder .modeCase = .ub :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- The raw observation of a `BasicMemory` byte list. -/
def npMrBytesObs (bs : List Byte) : NullaryPtrMrObs :=
  .retBytes (bs.map (projByteTB ∘ liftByteTB))

/-- The frozen dictionary of distinct raw MiniRust observations of the corpus.
The class of an observation is its index in this list:

| class | raw observation                                   |
|------:|---------------------------------------------------|
| 0     | `usize` `36`                                      |
| 1     | `bool` `true`                                     |
| 2     | `usize` `4`                                       |
| 3     | pointer to function allocation `0` (at `4096`)    |
| 4     | `usize` `3`                                       |
| 5     | pointer to the array allocation `2` (at `1024`)   |
| 6     | pointer to function allocation `1` (at `8192`)    |
| 7     | `u32` `73`                                        |
| 8     | `u8` `7`                                          |
| 9     | `u32` `42`                                        |
| 10    | undefined behavior                                |
| 11    | unsupported                                       | -/
def npMrObsDict : List NullaryPtrMrObs :=
  [ npMrBytesObs (scalarBytes IntType.usize_ty 36),
    npMrBytesObs [.Init 1 none],
    npMrBytesObs (scalarBytes IntType.usize_ty 4),
    npMrBytesObs (ptrBytes 4096 (some (⟨0⟩, ()))),
    npMrBytesObs (scalarBytes IntType.usize_ty 3),
    npMrBytesObs (ptrBytes 1024 (some (⟨2⟩, ()))),
    npMrBytesObs (ptrBytes 8192 (some (⟨1⟩, ()))),
    npMrBytesObs (scalarBytes u32 73),
    npMrBytesObs [.Init 7 none],
    npMrBytesObs (scalarBytes u32 42),
    .ub,
    .unsupported ]

/-- Index of the first entry of `dict` equal to `o`, counting from `i`. -/
def npMrObsClassAux (o : NullaryPtrMrObs) : List NullaryPtrMrObs → Nat → Option Nat
  | [], _ => none
  | d :: ds, i => if d = o then some i else npMrObsClassAux o ds (i + 1)

/-- The class of a raw observation: its index in `npMrObsDict` (`none` for an
observation outside the dictionary, which fails every downstream check). -/
def npMrObsClass (o : NullaryPtrMrObs) : Option Nat :=
  npMrObsClassAux o npMrObsDict 0

/-- The class of the direct `MiniRustSpec.Interp` observation of a key. -/
def npMrObserveClass (mode : NullaryPtrMrMode) (v : NullaryPtrVariant) (c : NullaryPtrCase) :
    Option Nat :=
  npMrObsClass (npMrObserve mode v c)

/-- Boolean check that `npMrObsDict` has no duplicate entries and that every
entry's class is its own index. -/
def npMrObsDictDistinct : Bool :=
  (List.range npMrObsDict.length).all fun i =>
    decide ((npMrObsDict[i]?).bind npMrObsClass = some i) &&
    (List.range npMrObsDict.length).all fun j =>
      decide (i = j) || decide (npMrObsDict[i]? ≠ npMrObsDict[j]?)

/-- **Kernel-checked injectivity of the class dictionary**: distinct classes
are distinct raw byte observations, and classification is exact on the
dictionary. -/
theorem npMrObsDict_distinct : npMrObsDictDistinct = true := by
  decide +kernel

/-- The frozen 32-key MiniRust observation-class table. -/
def npMrExpectedClass (mode : NullaryPtrMrMode) : NullaryPtrVariant → NullaryPtrCase → Nat
  | .nullaryOp, .okPrimary => 0
  | .nullaryOp, .okSecondary => 1
  | .nullaryOp, .ubFault => 10
  | .nullaryOp, .modeCase => 2
  | .pointerCoercion, .okPrimary => 3
  | .pointerCoercion, .okSecondary => 4
  | .pointerCoercion, .ubFault => 10
  | .pointerCoercion, .modeCase => 5
  | .fnPtrToPtr, .okPrimary => 3
  | .fnPtrToPtr, .okSecondary => 6
  | .fnPtrToPtr, .ubFault => 10
  | .fnPtrToPtr, .modeCase => 10
  | .unwrapUnsafeBinder, .okPrimary => 7
  | .unwrapUnsafeBinder, .okSecondary => 8
  | .unwrapUnsafeBinder, .ubFault => 10
  | .unwrapUnsafeBinder, .modeCase =>
    match mode with
    | .basicMemory => 9
    | .treeBorrows => 10

/-- **Kernel-checked MiniRust table**: on all 32 keys, executing
`MiniRustSpec.Interp.{steps, stepsTB}` yields a raw observation of exactly the
frozen class. -/
theorem npMrObserveClass_table (mode : NullaryPtrMrMode) (v : NullaryPtrVariant)
    (c : NullaryPtrCase) :
    npMrObserveClass mode v c = some (npMrExpectedClass mode v c) := by
  cases mode <;> cases v <;> cases c <;> decide +kernel

/-! ## §7. Exhaustive Axiom, Import-Isolation, & `Classical.choice`-Free Codec Audit -/

section AxiomAudit
open Lean Elab Command

/-- Exhaustively verify that:
1. This module obeys `[IMPORT-ISOLATION]` (zero `Anneal.*`, zero `DeinitBridge`,
   zero `IntrinsicBoundary` imports).
2. Every declaration defined in `MiniRustSpec.NullaryAndPtrCoercionMR` depends
   ONLY on standard Lean axioms (`propext`, `Quot.sound`, `Classical.choice`)
   with zero `sorryAx` and zero `Lean.ofReduceBool` / `Lean.trustCompiler`.
3. All executable observers, class codecs, and kernel-checked table theorems
   in this module are strictly `Classical.choice`-free. -/
elab "#assert_nullary_ptr_coercion_mr_audit" : command => do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`Anneal).isPrefixOf modName ||
        modName == `MiniRustSpec.Correspondence.DeinitBridge ||
        modName == `MiniRustSpec.Correspondence.IntrinsicBoundary then
      throwError "import-isolation violation: {modName} must not be imported"
  let mut checked : Nat := 0
  for (c, _) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
  if checked == 0 then
    throwError "MiniRustSpec.NullaryAndPtrCoercionMR: 0 declarations found"
  let choiceFreeCodecs : List Lean.Name := [
    ``npTrustedValueObs,
    ``npRunTrusted,
    ``npTrustedObserve,
    ``npTrustedObserve_table,
    ``npRunMrObs,
    ``npMrObserve,
    ``npMrObsClass,
    ``npMrObserveClass,
    ``npMrObsDict_distinct,
    ``npMrObserveClass_table,
    ``npMrObserve_unwrap_mode_sensitivity
  ]
  for c in choiceFreeCodecs do
    let axs ← liftCoreM <| Lean.collectAxioms c
    if axs.contains ``Classical.choice then
      throwError "MR codec/def {c} unexpectedly depends on Classical.choice"
  logInfo m!"MiniRustSpec.NullaryAndPtrCoercionMR: verified {checked} declarations (sorry_free=true, import_isolated=true, choice_free_codecs={choiceFreeCodecs.length})"

#assert_nullary_ptr_coercion_mr_audit

end AxiomAudit

end MiniRustSpec.NullaryAndPtrCoercionMR
