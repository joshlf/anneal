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

private theorem np_scalarModulus_8 : scalarModulus 8 = 2 ^ (8 * 8) := by decide

private theorem np_bool_and_eq_true {a b : Bool} (h : Bool.and a b = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [Bool.and]

private theorem np_set?_get?_eq {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : set? xs i v = some xs') : get? xs' i = some v := by
  unfold set? at h
  split at h
  · rename_i hlt
    cases h
    unfold get?
    exact List.getElem?_set_self hlt
  · cases h

private theorem np_encodeM_u8_one {M : Type} [Gen.Memory M] :
    Type.encodeM (M := M) u8MrTy (.Int 1) = .ok [.Init 1 none] := by
  have hEnc : Endianness.encode x86_64.ENDIANNESS .Unsigned ⟨1⟩ 1 = some [1] := by decide
  unfold u8MrTy Type.encodeM Type.encodeIntM
  dsimp only
  rw [hEnc]; rfl

private theorem np_v1_evalValueM_computeSize {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (mrTy : Gen.Type) (sz : Nat) (al : LibSpecr.Align)
    (hMeta : Type.meta_kind mrTy = .None)
    (hLay : Type.layout mrTy = .ok (.Sized ⟨sz⟩ al)) :
    evalValueM m (.UnOp (.ComputeSize mrTy) (.Tuple [] unitType)) =
      .ok ((.Int (Int.ofNat sz), usizeMrTy), m) := by
  have hUn : evalUnOpM (.ComputeSize mrTy) (.Tuple [], unitType) (some m) =
      .ok (.Int (Int.ofNat sz), usizeMrTy) := by
    unfold evalUnOpM
    dsimp only
    rw [hMeta]
    simp only [PointerMetaKind.decode_valueM, bind, Except.bind, pure, Except.pure]
    rw [hLay]
    simp only [computeSizeM, LayoutStrategy.compute_size_and_align,
      bind, Except.bind, pure, Except.pure, usizeMrTy]; rfl
  unfold evalValueM
  rw [show evalValueM m (.Tuple [] unitType) = .ok ((.Tuple [], unitType), m) from rfl]
  simp only [hUn, bind, Except.bind, pure, Except.pure]

private theorem np_v1_evalValueM_computeAlign {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (mrTy : Gen.Type) (sz : LibSpecr.Size) (al : Nat)
    (hMeta : Type.meta_kind mrTy = .None)
    (hLay : Type.layout mrTy = .ok (.Sized sz ⟨al⟩)) :
    evalValueM m (.UnOp (.ComputeAlign mrTy) (.Tuple [] unitType)) =
      .ok ((.Int (Int.ofNat al), usizeMrTy), m) := by
  have hUn : evalUnOpM (.ComputeAlign mrTy) (.Tuple [], unitType) (some m) =
      .ok (.Int (Int.ofNat al), usizeMrTy) := by
    unfold evalUnOpM
    dsimp only
    rw [hMeta]
    simp only [PointerMetaKind.decode_valueM, bind, Except.bind, pure, Except.pure]
    rw [hLay]
    simp only [computeAlignM, LayoutStrategy.compute_size_and_align,
      bind, Except.bind, pure, Except.pure, usizeMrTy]; rfl
  unfold evalValueM
  rw [show evalValueM m (.Tuple [] unitType) = .ok ((.Tuple [], unitType), m) from rfl]
  simp only [hUn, bind, Except.bind, pure, Except.pure]

/-- Generic single-statement `stepM` lifting lemma (parallel to
`stepM_of_evalTerminatorM`), factoring `Interp.step` (`M = BM`, via
`stepM_bm_eq`) and `Interp.stepTB` (`M = TBM`, preserving `MachTB.wfLive`
via `stepTB_wfLive`) across any statement evaluation. -/
theorem np_stepM_of_evalStatementM {M : Type} [Gen.Memory M] [MemoryOps M]
    {m m1 mAfter : Machine M} (fr : StackFrame M) (blk : Gen.BasicBlock) (stmt : Gen.Statement)
    (hEn : m.threads.any (fun th => decide (th.state = .Enabled)) = true)
    (hPick : pickActiveThreadM { m with mem := { m.mem with accesses := [] } } = .ok m.active_thread)
    (hCur : curFrameM { m with mem := { m.mem with accesses := [] } } = .ok fr)
    (hBlk : mapIndex fr.func.blocks fr.next_block "frame.func.blocks[frame.next_block]" = .ok blk)
    (hNe : fr.next_stmt ≠ (blk.statements.length : Int))
    (hStmt : listIndex blk.statements fr.next_stmt "block.statements[frame.next_stmt]" = .ok stmt)
    (hEval : evalStatementM { m with mem := { m.mem with accesses := [] } } stmt = .ok m1)
    (hMut : mutateCurFrameM m1 (fun f => { f with next_stmt := f.next_stmt + 1 }) = .ok mAfter)
    (hRace : ConcurrentMemory.check_data_races mAfter.mem mAfter.active_thread
      (setInsert m.synchronized_threads m.active_thread, m.mem.accesses) = .ok ()) :
    stepM m = .ok mAfter := by
  unfold stepM
  simp only [hEn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, resetDataRaceTrackingM,
    hPick, hCur, hBlk, hNe, hStmt, hEval, hMut, hRace, bind, Except.bind, pure, Except.pure]

/-- Generic single-statement `stepM` error-propagation lemma. -/
theorem np_stepM_error_of_evalStatementM {M : Type} [Gen.Memory M] [MemoryOps M]
    {m : Machine M} {e : Stop} (fr : StackFrame M) (blk : Gen.BasicBlock) (stmt : Gen.Statement)
    (hEn : m.threads.any (fun th => decide (th.state = .Enabled)) = true)
    (hPick : pickActiveThreadM { m with mem := { m.mem with accesses := [] } } = .ok m.active_thread)
    (hCur : curFrameM { m with mem := { m.mem with accesses := [] } } = .ok fr)
    (hBlk : mapIndex fr.func.blocks fr.next_block "frame.func.blocks[frame.next_block]" = .ok blk)
    (hNe : fr.next_stmt ≠ (blk.statements.length : Int))
    (hStmt : listIndex blk.statements fr.next_stmt "block.statements[frame.next_stmt]" = .ok stmt)
    (hEval : evalStatementM { m with mem := { m.mem with accesses := [] } } stmt = .error e) :
    stepM m = .error e := by
  unfold stepM
  simp only [hEn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, resetDataRaceTrackingM,
    hPick, hCur, hBlk, hNe, hStmt, hEval, bind, Except.bind]

/-- **V1 Universal Value-Coupled (`Ep2ValRel`) Evaluation Law (`Mach` & `MachTB`)**:
for EVERY `M ∈ {BM, TBM}`, EVERY layout table with 64-bit pointers, EVERY state
`(locals, mem, m)`, and EVERY `NullOp ∈ {.sizeOf, .alignOf, .offsetOf fields, .ubChecks}`,
Trusted `evalRvalue (.nullaryOp op argTy)` and MiniRust `evalValueM m mrSrc` produce
values coupled by `Ep2ValRel allocBase provAllocId` (preserving both `locals`/`mem`
and `m`), covering `UnOp.ComputeSize`, `UnOp.ComputeAlign`, constant `usize`,
`u8` `Switch`-scrutinee `1`, and native `Bool` `true` (with identical byte encoding
`[.Init 1 none]`). -/
theorem np_v1_evalValueM_nullaryOp_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (allocBase : Nat → Nat) (provAllocId : Gen.Memory.Provenance M → Nat)
    (locals : List LocalSlot) (mem : MirSemantics.Memory)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (m : Machine M)
    (hPtr8 : layoutPointerBytes layouts = 8) :
    (∀ (ty : MirAst.Ty) (mrTy : Gen.Type) (sz : Nat) (al : LibSpecr.Align),
      intrinsicRigidTyByteSize decls layouts ty.kind = .some sz →
      Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes layouts)) 2) 1) = true →
      Type.meta_kind mrTy = .None →
      Type.layout mrTy = .ok (.Sized ⟨sz⟩ al) →
      evalRvalue locals (.nullaryOp .sizeOf ty) mem decls layouts =
        .ok (.scalar ⟨sz, 8⟩) locals mem ∧
      evalValueM m (.UnOp (.ComputeSize mrTy) (.Tuple [] unitType)) =
        .ok ((.Int (Int.ofNat sz), usizeMrTy), m) ∧
      evalValueM m (.Constant (.Int (Int.ofNat sz)) usizeMrTy) =
        .ok ((.Int (Int.ofNat sz), usizeMrTy), m) ∧
      Ep2ValRel allocBase provAllocId (.scalar ⟨sz, 8⟩) (.Int (Int.ofNat sz))) ∧
    (∀ (ty : MirAst.Ty) (mrTy : Gen.Type) (sz al : Nat) (szMr : LibSpecr.Size),
      intrinsicRigidTyByteSize decls layouts ty.kind = .some sz →
      intrinsicRigidTyAlign decls layouts ty.kind = .some al →
      Bool.and
        (Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes layouts)) 2) 1))
        (Bool.and (Trusted.Rustc.V2026_06_01.Layout.Align.isPowerOfTwoBytes ⟨al⟩)
          (Nat.blt al (scalarModulus (layoutPointerBytes layouts)))) = true →
      Type.meta_kind mrTy = .None →
      Type.layout mrTy = .ok (.Sized szMr ⟨al⟩) →
      evalRvalue locals (.nullaryOp .alignOf ty) mem decls layouts =
        .ok (.scalar ⟨al, 8⟩) locals mem ∧
      evalValueM m (.UnOp (.ComputeAlign mrTy) (.Tuple [] unitType)) =
        .ok ((.Int (Int.ofNat al), usizeMrTy), m) ∧
      evalValueM m (.Constant (.Int (Int.ofNat al)) usizeMrTy) =
        .ok ((.Int (Int.ofNat al), usizeMrTy), m) ∧
      Ep2ValRel allocBase provAllocId (.scalar ⟨al, 8⟩) (.Int (Int.ofNat al))) ∧
    (∀ (ty : MirAst.Ty) (fields : List (VariantIdx × FieldIdx)) (sz off : Nat),
      intrinsicRigidTyByteSize decls layouts ty.kind = .some sz →
      resolveOffsetOfPath layouts
        (intrinsicRigidTyByteSize decls layouts)
        (intrinsicRigidTyAlign decls layouts)
        (findDeclLayoutForRigidTy decls layouts)
        (.some ty.kind)
        (findDeclLayoutForRigidTy decls layouts ty.kind)
        fields = .some off →
      Bool.and
        (Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes layouts)) 2) 1))
        (Nat.ble off sz) = true →
      evalRvalue locals (.nullaryOp (.offsetOf fields) ty) mem decls layouts =
        .ok (.scalar ⟨off, 8⟩) locals mem ∧
      evalValueM m (.Constant (.Int (Int.ofNat off)) usizeMrTy) =
        .ok ((.Int (Int.ofNat off), usizeMrTy), m) ∧
      Ep2ValRel allocBase provAllocId (.scalar ⟨off, 8⟩) (.Int (Int.ofNat off))) ∧
    (∀ (li : Nat),
      evalRvalue locals (.nullaryOp .ubChecks { kind := .bool, layoutIdx := li }) mem decls layouts =
        .ok (.scalar (boolToScalar true)) locals mem ∧
      evalValueM m (.Constant (.Int 1) u8MrTy) = .ok ((.Int 1, u8MrTy), m) ∧
      evalValueM m (.Constant (.Bool true) .Bool) = .ok ((.Bool true, .Bool), m) ∧
      Ep2ValRel allocBase provAllocId (.scalar (boolToScalar true)) (.Int 1) ∧
      Type.encodeM (M := M) .Bool (.Bool true) = .ok [.Init 1 none] ∧
      Type.encodeM (M := M) u8MrTy (.Int 1) = .ok [.Init 1 none]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ty mrTy sz al hSz hLe hMeta hLay
    have hEv := np_v1_nullary_sizeOf_of_intrinsic locals ty mem decls layouts sz hSz hLe
    rw [hPtr8] at hEv hLe
    have hBound : sz < 2 ^ (8 * 8) :=
      Nat.lt_of_le_of_lt (Nat.ble_eq.mp hLe) (by decide)
    exact ⟨hEv, np_v1_evalValueM_computeSize m mrTy sz al hMeta hLay, rfl,
      .scalar sz 8 hBound⟩
  · intro ty mrTy sz al szMr hSz hAl hOk hMeta hLay
    have hEv := np_v1_nullary_alignOf_of_intrinsic locals ty mem decls layouts sz al hSz hAl hOk
    rw [hPtr8] at hEv hOk
    have hBlt : Nat.blt al (scalarModulus 8) = true :=
      (np_bool_and_eq_true (np_bool_and_eq_true hOk).2).2
    have hBound : al < 2 ^ (8 * 8) := by
      have hLt := Nat.blt_eq.mp hBlt
      rw [np_scalarModulus_8] at hLt
      exact hLt
    exact ⟨hEv, np_v1_evalValueM_computeAlign m mrTy szMr al hMeta hLay, rfl,
      .scalar al 8 hBound⟩
  · intro ty fields sz off hSz hOff hOk
    have hEv := np_v1_nullary_offsetOf_of_intrinsic locals ty mem decls layouts fields sz off
      hSz hOff hOk
    rw [hPtr8] at hEv hOk
    have hAnd := np_bool_and_eq_true hOk
    have hBound : off < 2 ^ (8 * 8) :=
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.ble_eq.mp hAnd.2) (Nat.ble_eq.mp hAnd.1)) (by decide)
    exact ⟨hEv, rfl, .scalar off 8 hBound⟩
  · intro li
    exact ⟨rfl, rfl, rfl, .scalar 1 1 (by decide), rfl, np_encodeM_u8_one⟩

/-- Single-statement execution context for a MiniRust
`Statement.Assign (.Local mrDst) mrSrc` step on `Machine M` (`Mach` or `MachTB`).
Carries NO assumption on `evalValueM` or `Ep2ValRel` — those are derived directly
by the `V1` simulation theorems for each `NullOp`. -/
structure NpMrAssignFrame {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 mAfter : Machine M) (mrDst : Gen.LocalName) (mrSrc : Gen.ValueExpr)
    (mv : Gen.Value M) (dstTy : Gen.Type) where
  fr : StackFrame M
  blk : Gen.BasicBlock
  place : Gen.Place M
  hEn : m.threads.any (fun th => decide (th.state = .Enabled)) = true
  hPick : pickActiveThreadM { m with mem := { m.mem with accesses := [] } } = .ok m.active_thread
  hCur : curFrameM { m with mem := { m.mem with accesses := [] } } = .ok fr
  hBlk : mapIndex fr.func.blocks fr.next_block "frame.func.blocks[frame.next_block]" = .ok blk
  hNe : fr.next_stmt ≠ (blk.statements.length : Int)
  hStmt : listIndex blk.statements fr.next_stmt "block.statements[frame.next_stmt]" =
    .ok (.Assign (.Local mrDst) mrSrc)
  hp : evalPlaceM { m with mem := { m.mem with accesses := [] } } (.Local mrDst) =
    .ok ((place, dstTy), { m with mem := { m.mem with accesses := [] } })
  hst : placeStoreM { m with mem := { m.mem with accesses := [] } } place mv dstTy = .ok m1
  hMut : mutateCurFrameM m1 (fun f => { f with next_stmt := f.next_stmt + 1 }) = .ok mAfter
  hRace : ConcurrentMemory.check_data_races mAfter.mem mAfter.active_thread
    (setInsert m.synchronized_threads m.active_thread, m.mem.accesses) = .ok ()

/-- Single-statement execution context for a MiniRust `Assign (.Local mrDst) mrSrc`
whose destination local `mrDst` is dead (`mapGet fr.locals mrDst = none`). -/
structure NpMrDeadAssignFrame {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (mrDst : Gen.LocalName) (mrSrc : Gen.ValueExpr) where
  fr : StackFrame M
  blk : Gen.BasicBlock
  dstTy : Gen.Type
  hEn : m.threads.any (fun th => decide (th.state = .Enabled)) = true
  hPick : pickActiveThreadM { m with mem := { m.mem with accesses := [] } } = .ok m.active_thread
  hCur : curFrameM { m with mem := { m.mem with accesses := [] } } = .ok fr
  hBlk : mapIndex fr.func.blocks fr.next_block "frame.func.blocks[frame.next_block]" = .ok blk
  hNe : fr.next_stmt ≠ (blk.statements.length : Int)
  hStmt : listIndex blk.statements fr.next_stmt "block.statements[frame.next_stmt]" =
    .ok (.Assign (.Local mrDst) mrSrc)
  hDecl : mapIndex fr.func.locals mrDst "self.cur_frame().func.locals[name]" = .ok dstTy
  hDead : mapGet fr.locals mrDst = none

private theorem np_v1_trusted_assign_step (body : CapturedMir) (bb : BasicBlockData)
    (s : MachineState) (dstLoc : Nat) (op : NullOp) (argTy : MirAst.Ty) (span : String)
    (tv : MirSemantics.Value) (slot : LocalSlot) (locals2 : List LocalSlot)
    (hPhase : (s.memory.activeCallee.getD body).phase = .runtimePostCleanup)
    (hBb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx = some bb)
    (hSt : get? bb.statements s.frame.stmtIdx =
      some { kind := .assign (locPlace dstLoc) (.nullaryOp op argTy), span := span })
    (hNull : evalNullaryOp s.frame.locals op argTy s.memory
      (s.memory.activeCallee.getD body).localDecls (s.memory.activeCallee.getD body).layouts =
      .ok tv s.frame.locals s.memory)
    (hLive : slot ≠ .dead)
    (hGet : get? s.frame.locals dstLoc = some slot)
    (hSet : set? s.frame.locals dstLoc (.init tv) = some locals2)
    (hProt : s.memory.activeProtectors = []) :
    let s' := advanceStmt s locals2 { s.memory with
      borrows := invalidateConflictingBorrows s.memory.borrows dstLoc .none (length s.memory.callStack) }
    evalStmt s { kind := .assign (locPlace dstLoc) (.nullaryOp op argTy), span := span }
        (s.memory.activeCallee.getD body).localDecls (s.memory.activeCallee.getD body).layouts =
      MirStepNode.step s' ∧
    stepMirFn body s = .tau (.running s') ∧
    get? s'.frame.locals dstLoc = some (.init tv) := by
  intro s'
  have hEv : evalStmt s { kind := .assign (locPlace dstLoc) (.nullaryOp op argTy), span := span }
      (s.memory.activeCallee.getD body).localDecls (s.memory.activeCallee.getD body).layouts =
      MirStepNode.step s' := by
    cases slot with
    | dead => exact absurd rfl hLive
    | uninit | init _ =>
      simp only [evalStmt, evalRvalue, hNull, locPlace, hGet, hSet, hProt, s']
  have hStep : stepMirFn body s = .tau (.running s') := by
    unfold stepMirFn
    dsimp only
    rw [hPhase, hBb]
    dsimp only
    rw [hSt]
    exact hEv
  exact ⟨hEv, hStep, np_set?_get?_eq hSet⟩

private theorem np_v1_mr_assign_stepM {M : Type} [Gen.Memory M] [MemoryOps M]
    {m m1 mAfter : Machine M} {mrDst : Gen.LocalName} {mrSrc : Gen.ValueExpr}
    {mv : Gen.Value M} {dstTy srcTy : Gen.Type}
    (w : NpMrAssignFrame m m1 mAfter mrDst mrSrc mv dstTy)
    (hv : evalValueM { m with mem := { m.mem with accesses := [] } } mrSrc =
      .ok ((mv, srcTy), { m with mem := { m.mem with accesses := [] } })) :
    evalStatementM { m with mem := { m.mem with accesses := [] } }
        (.Assign (.Local mrDst) mrSrc) = .ok m1 ∧
    stepM m = .ok mAfter := by
  have hEv : evalStatementM { m with mem := { m.mem with accesses := [] } }
      (.Assign (.Local mrDst) mrSrc) = .ok m1 := by
    dsimp only [evalStatementM]
    rw [w.hp, ok_bind, hv, ok_bind]
    exact w.hst
  exact ⟨hEv, np_stepM_of_evalStatementM w.fr w.blk (.Assign (.Local mrDst) mrSrc)
    w.hEn w.hPick w.hCur w.hBlk w.hNe w.hStmt hEv w.hMut w.hRace⟩

/-- **V1 Universal Value-Coupled (`Ep2ValRel`) Full-Step Simulation across
Trusted `evalStmt`/`stepMirFn`, MiniRust `Interp.step` (`Mach`), and MiniRust
`Interp.stepTB` (`MachTB`, preserving `MachTB.wfLive`)**:
covers all 4 supported `Rvalue.nullaryOp` variants —
1. `.sizeOf` (lowered to `UnOp.ComputeSize mrTy ()`),
2. `.alignOf` (lowered to `UnOp.ComputeAlign mrTy ()`),
3. `.offsetOf fields` (lowered to `Constant (.Int off) usizeMrTy`), and
4. `.ubChecks` (lowered BOTH to `Constant (.Int 1) u8MrTy` with direct `Ep2ValRel`
   agreement AND to `Constant (.Bool true) .Bool` with identical encoded byte
   representation `[.Init 1 none]`).
Every conjunct derives `evalNullaryOp`, `evalValueM`, destination-local updates,
`MachTB.wfLive` preservation, and `Ep2ValRel` directly from the operational
semantics without taking any evaluation or value-relation hypothesis. -/
theorem np_v1_nullaryOp_coupled_step_sim_all_four
    (allocBaseBM : Nat → Nat) (provAllocIdBM : Gen.Memory.Provenance BM → Nat)
    (allocBaseTB : Nat → Nat) (provAllocIdTB : Gen.Memory.Provenance TBM → Nat)
    (body : CapturedMir) (bb : BasicBlockData) (s : MachineState) (dstLoc : Nat) (span : String)
    (slot : LocalSlot) (mrDst : Gen.LocalName)
    (hPhase : (s.memory.activeCallee.getD body).phase = .runtimePostCleanup)
    (hBb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx = some bb)
    (hPtr8 : layoutPointerBytes (s.memory.activeCallee.getD body).layouts = 8)
    (hLive : slot ≠ .dead) (hGet : get? s.frame.locals dstLoc = some slot)
    (hProt : s.memory.activeProtectors = []) :
    let cur := s.memory.activeCallee.getD body
    -- 1. `.sizeOf` via `UnOp.ComputeSize mrTy ()`
    (∀ (ty : MirAst.Ty) (mrTy : Gen.Type) (sz : Nat) (al : LibSpecr.Align)
        (locals2 : List LocalSlot) (mBM mBM1 mBMf : Mach) (mTB mTB1 mTBf : MachTB),
      get? bb.statements s.frame.stmtIdx =
        some { kind := .assign (locPlace dstLoc) (.nullaryOp .sizeOf ty), span := span } →
      intrinsicRigidTyByteSize cur.localDecls cur.layouts ty.kind = .some sz →
      Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes cur.layouts)) 2) 1) = true →
      set? s.frame.locals dstLoc (.init (.scalar ⟨sz, 8⟩)) = some locals2 →
      Type.meta_kind mrTy = .None →
      Type.layout mrTy = .ok (.Sized ⟨sz⟩ al) →
      NpMrAssignFrame mBM mBM1 mBMf mrDst (.UnOp (.ComputeSize mrTy) (.Tuple [] unitType))
        (.Int (Int.ofNat sz)) usizeMrTy →
      MachTB.wfLive mTB →
      NpMrAssignFrame mTB mTB1 mTBf mrDst (.UnOp (.ComputeSize mrTy) (.Tuple [] unitType))
        (.Int (Int.ofNat sz)) usizeMrTy →
      let s' := advanceStmt s locals2 { s.memory with
        borrows := invalidateConflictingBorrows s.memory.borrows dstLoc .none (length s.memory.callStack) }
      evalStmt s { kind := .assign (locPlace dstLoc) (.nullaryOp .sizeOf ty), span := span }
          cur.localDecls cur.layouts = MirStepNode.step s' ∧
      stepMirFn body s = .tau (.running s') ∧
      get? s'.frame.locals dstLoc = some (.init (.scalar ⟨sz, 8⟩)) ∧
      Interp.evalStatement { mBM with mem := { mBM.mem with accesses := [] } }
          (.Assign (.Local mrDst) (.UnOp (.ComputeSize mrTy) (.Tuple [] unitType))) = .ok mBM1 ∧
      Interp.step mBM = .ok mBMf ∧
      evalStatementM { mTB with mem := { mTB.mem with accesses := [] } }
          (.Assign (.Local mrDst) (.UnOp (.ComputeSize mrTy) (.Tuple [] unitType))) = .ok mTB1 ∧
      Interp.stepTB mTB = .ok mTBf ∧ MachTB.wfLive mTBf ∧
      Ep2ValRel allocBaseBM provAllocIdBM (.scalar ⟨sz, 8⟩) (.Int (Int.ofNat sz)) ∧
      Ep2ValRel allocBaseTB provAllocIdTB (.scalar ⟨sz, 8⟩) (.Int (Int.ofNat sz))) ∧
    -- 2. `.alignOf` via `UnOp.ComputeAlign mrTy ()`
    (∀ (ty : MirAst.Ty) (mrTy : Gen.Type) (sz al : Nat) (szMr : LibSpecr.Size)
        (locals2 : List LocalSlot) (mBM mBM1 mBMf : Mach) (mTB mTB1 mTBf : MachTB),
      get? bb.statements s.frame.stmtIdx =
        some { kind := .assign (locPlace dstLoc) (.nullaryOp .alignOf ty), span := span } →
      intrinsicRigidTyByteSize cur.localDecls cur.layouts ty.kind = .some sz →
      intrinsicRigidTyAlign cur.localDecls cur.layouts ty.kind = .some al →
      Bool.and
        (Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes cur.layouts)) 2) 1))
        (Bool.and (Trusted.Rustc.V2026_06_01.Layout.Align.isPowerOfTwoBytes ⟨al⟩)
          (Nat.blt al (scalarModulus (layoutPointerBytes cur.layouts)))) = true →
      set? s.frame.locals dstLoc (.init (.scalar ⟨al, 8⟩)) = some locals2 →
      Type.meta_kind mrTy = .None →
      Type.layout mrTy = .ok (.Sized szMr ⟨al⟩) →
      NpMrAssignFrame mBM mBM1 mBMf mrDst (.UnOp (.ComputeAlign mrTy) (.Tuple [] unitType))
        (.Int (Int.ofNat al)) usizeMrTy →
      MachTB.wfLive mTB →
      NpMrAssignFrame mTB mTB1 mTBf mrDst (.UnOp (.ComputeAlign mrTy) (.Tuple [] unitType))
        (.Int (Int.ofNat al)) usizeMrTy →
      let s' := advanceStmt s locals2 { s.memory with
        borrows := invalidateConflictingBorrows s.memory.borrows dstLoc .none (length s.memory.callStack) }
      evalStmt s { kind := .assign (locPlace dstLoc) (.nullaryOp .alignOf ty), span := span }
          cur.localDecls cur.layouts = MirStepNode.step s' ∧
      stepMirFn body s = .tau (.running s') ∧
      get? s'.frame.locals dstLoc = some (.init (.scalar ⟨al, 8⟩)) ∧
      Interp.evalStatement { mBM with mem := { mBM.mem with accesses := [] } }
          (.Assign (.Local mrDst) (.UnOp (.ComputeAlign mrTy) (.Tuple [] unitType))) = .ok mBM1 ∧
      Interp.step mBM = .ok mBMf ∧
      evalStatementM { mTB with mem := { mTB.mem with accesses := [] } }
          (.Assign (.Local mrDst) (.UnOp (.ComputeAlign mrTy) (.Tuple [] unitType))) = .ok mTB1 ∧
      Interp.stepTB mTB = .ok mTBf ∧ MachTB.wfLive mTBf ∧
      Ep2ValRel allocBaseBM provAllocIdBM (.scalar ⟨al, 8⟩) (.Int (Int.ofNat al)) ∧
      Ep2ValRel allocBaseTB provAllocIdTB (.scalar ⟨al, 8⟩) (.Int (Int.ofNat al))) ∧
    -- 3. `.offsetOf fields` via `Constant (.Int off) usizeMrTy`
    (∀ (ty : MirAst.Ty) (fields : List (VariantIdx × FieldIdx)) (sz off : Nat)
        (locals2 : List LocalSlot) (mBM mBM1 mBMf : Mach) (mTB mTB1 mTBf : MachTB),
      get? bb.statements s.frame.stmtIdx =
        some { kind := .assign (locPlace dstLoc) (.nullaryOp (.offsetOf fields) ty), span := span } →
      intrinsicRigidTyByteSize cur.localDecls cur.layouts ty.kind = .some sz →
      resolveOffsetOfPath cur.layouts
        (intrinsicRigidTyByteSize cur.localDecls cur.layouts)
        (intrinsicRigidTyAlign cur.localDecls cur.layouts)
        (findDeclLayoutForRigidTy cur.localDecls cur.layouts)
        (.some ty.kind)
        (findDeclLayoutForRigidTy cur.localDecls cur.layouts ty.kind)
        fields = .some off →
      Bool.and
        (Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes cur.layouts)) 2) 1))
        (Nat.ble off sz) = true →
      set? s.frame.locals dstLoc (.init (.scalar ⟨off, 8⟩)) = some locals2 →
      NpMrAssignFrame mBM mBM1 mBMf mrDst (.Constant (.Int (Int.ofNat off)) usizeMrTy)
        (.Int (Int.ofNat off)) usizeMrTy →
      MachTB.wfLive mTB →
      NpMrAssignFrame mTB mTB1 mTBf mrDst (.Constant (.Int (Int.ofNat off)) usizeMrTy)
        (.Int (Int.ofNat off)) usizeMrTy →
      let s' := advanceStmt s locals2 { s.memory with
        borrows := invalidateConflictingBorrows s.memory.borrows dstLoc .none (length s.memory.callStack) }
      evalStmt s { kind := .assign (locPlace dstLoc) (.nullaryOp (.offsetOf fields) ty), span := span }
          cur.localDecls cur.layouts = MirStepNode.step s' ∧
      stepMirFn body s = .tau (.running s') ∧
      get? s'.frame.locals dstLoc = some (.init (.scalar ⟨off, 8⟩)) ∧
      Interp.evalStatement { mBM with mem := { mBM.mem with accesses := [] } }
          (.Assign (.Local mrDst) (.Constant (.Int (Int.ofNat off)) usizeMrTy)) = .ok mBM1 ∧
      Interp.step mBM = .ok mBMf ∧
      evalStatementM { mTB with mem := { mTB.mem with accesses := [] } }
          (.Assign (.Local mrDst) (.Constant (.Int (Int.ofNat off)) usizeMrTy)) = .ok mTB1 ∧
      Interp.stepTB mTB = .ok mTBf ∧ MachTB.wfLive mTBf ∧
      Ep2ValRel allocBaseBM provAllocIdBM (.scalar ⟨off, 8⟩) (.Int (Int.ofNat off)) ∧
      Ep2ValRel allocBaseTB provAllocIdTB (.scalar ⟨off, 8⟩) (.Int (Int.ofNat off))) ∧
    -- 4a. `.ubChecks` via `u8` `Switch`-scrutinee lowering (`Constant (.Int 1) u8MrTy`)
    (∀ (li : Nat) (locals2 : List LocalSlot) (mBM mBM1 mBMf : Mach) (mTB mTB1 mTBf : MachTB),
      get? bb.statements s.frame.stmtIdx =
        some { kind := .assign (locPlace dstLoc) (.nullaryOp .ubChecks { kind := .bool, layoutIdx := li }), span := span } →
      set? s.frame.locals dstLoc (.init (.scalar (boolToScalar true))) = some locals2 →
      NpMrAssignFrame mBM mBM1 mBMf mrDst (.Constant (.Int 1) u8MrTy) (.Int 1) u8MrTy →
      MachTB.wfLive mTB →
      NpMrAssignFrame mTB mTB1 mTBf mrDst (.Constant (.Int 1) u8MrTy) (.Int 1) u8MrTy →
      let s' := advanceStmt s locals2 { s.memory with
        borrows := invalidateConflictingBorrows s.memory.borrows dstLoc .none (length s.memory.callStack) }
      evalStmt s { kind := .assign (locPlace dstLoc) (.nullaryOp .ubChecks { kind := .bool, layoutIdx := li }), span := span }
          cur.localDecls cur.layouts = MirStepNode.step s' ∧
      stepMirFn body s = .tau (.running s') ∧
      get? s'.frame.locals dstLoc = some (.init (.scalar (boolToScalar true))) ∧
      Interp.evalStatement { mBM with mem := { mBM.mem with accesses := [] } }
          (.Assign (.Local mrDst) (.Constant (.Int 1) u8MrTy)) = .ok mBM1 ∧
      Interp.step mBM = .ok mBMf ∧
      evalStatementM { mTB with mem := { mTB.mem with accesses := [] } }
          (.Assign (.Local mrDst) (.Constant (.Int 1) u8MrTy)) = .ok mTB1 ∧
      Interp.stepTB mTB = .ok mTBf ∧ MachTB.wfLive mTBf ∧
      Ep2ValRel allocBaseBM provAllocIdBM (.scalar (boolToScalar true)) (.Int 1) ∧
      Ep2ValRel allocBaseTB provAllocIdTB (.scalar (boolToScalar true)) (.Int 1)) ∧
    -- 4b. `.ubChecks` via native `.Bool` lowering (`Constant (.Bool true) .Bool`)
    (∀ (li : Nat) (locals2 : List LocalSlot) (mBM mBM1 mBMf : Mach) (mTB mTB1 mTBf : MachTB),
      get? bb.statements s.frame.stmtIdx =
        some { kind := .assign (locPlace dstLoc) (.nullaryOp .ubChecks { kind := .bool, layoutIdx := li }), span := span } →
      set? s.frame.locals dstLoc (.init (.scalar (boolToScalar true))) = some locals2 →
      NpMrAssignFrame mBM mBM1 mBMf mrDst (.Constant (.Bool true) .Bool) (.Bool true) .Bool →
      MachTB.wfLive mTB →
      NpMrAssignFrame mTB mTB1 mTBf mrDst (.Constant (.Bool true) .Bool) (.Bool true) .Bool →
      let s' := advanceStmt s locals2 { s.memory with
        borrows := invalidateConflictingBorrows s.memory.borrows dstLoc .none (length s.memory.callStack) }
      evalStmt s { kind := .assign (locPlace dstLoc) (.nullaryOp .ubChecks { kind := .bool, layoutIdx := li }), span := span }
          cur.localDecls cur.layouts = MirStepNode.step s' ∧
      stepMirFn body s = .tau (.running s') ∧
      get? s'.frame.locals dstLoc = some (.init (.scalar (boolToScalar true))) ∧
      Interp.evalStatement { mBM with mem := { mBM.mem with accesses := [] } }
          (.Assign (.Local mrDst) (.Constant (.Bool true) .Bool)) = .ok mBM1 ∧
      Interp.step mBM = .ok mBMf ∧
      evalStatementM { mTB with mem := { mTB.mem with accesses := [] } }
          (.Assign (.Local mrDst) (.Constant (.Bool true) .Bool)) = .ok mTB1 ∧
      Interp.stepTB mTB = .ok mTBf ∧ MachTB.wfLive mTBf ∧
      Type.encodeM (M := BM) .Bool (.Bool true) = .ok [.Init 1 none] ∧
      Type.encodeM (M := TBM) .Bool (.Bool true) = .ok [.Init 1 none]) := by
  intro cur
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ty mrTy sz al locals2 mBM mBM1 mBMf mTB mTB1 mTBf hSt hSz hLe hSet hMeta hLay wBM hwfTB wTB
    have hVBM := (np_v1_evalValueM_nullaryOp_M allocBaseBM provAllocIdBM s.frame.locals s.memory
      cur.localDecls cur.layouts { mBM with mem := { mBM.mem with accesses := [] } } hPtr8).1
      ty mrTy sz al hSz hLe hMeta hLay
    have hVTB := (np_v1_evalValueM_nullaryOp_M allocBaseTB provAllocIdTB s.frame.locals s.memory
      cur.localDecls cur.layouts { mTB with mem := { mTB.mem with accesses := [] } } hPtr8).1
      ty mrTy sz al hSz hLe hMeta hLay
    have hTr := np_v1_trusted_assign_step body bb s dstLoc .sizeOf ty span (.scalar ⟨sz, 8⟩)
      slot locals2 hPhase hBb hSt hVBM.1 hLive hGet hSet hProt
    have hBM := np_v1_mr_assign_stepM wBM hVBM.2.1
    have hTB := np_v1_mr_assign_stepM wTB hVTB.2.1
    exact ⟨hTr.1, hTr.2.1, hTr.2.2,
      by rw [← evalStatementM_bm_eq]; exact hBM.1,
      by rw [← stepM_bm_eq]; exact hBM.2,
      hTB.1, hTB.2, stepTB_wfLive hwfTB hTB.2,
      hVBM.2.2.2, hVTB.2.2.2⟩
  · intro ty mrTy sz al szMr locals2 mBM mBM1 mBMf mTB mTB1 mTBf hSt hSz hAl hOk hSet hMeta hLay wBM hwfTB wTB
    have hVBM := (np_v1_evalValueM_nullaryOp_M allocBaseBM provAllocIdBM s.frame.locals s.memory
      cur.localDecls cur.layouts { mBM with mem := { mBM.mem with accesses := [] } } hPtr8).2.1
      ty mrTy sz al szMr hSz hAl hOk hMeta hLay
    have hVTB := (np_v1_evalValueM_nullaryOp_M allocBaseTB provAllocIdTB s.frame.locals s.memory
      cur.localDecls cur.layouts { mTB with mem := { mTB.mem with accesses := [] } } hPtr8).2.1
      ty mrTy sz al szMr hSz hAl hOk hMeta hLay
    have hTr := np_v1_trusted_assign_step body bb s dstLoc .alignOf ty span (.scalar ⟨al, 8⟩)
      slot locals2 hPhase hBb hSt hVBM.1 hLive hGet hSet hProt
    have hBM := np_v1_mr_assign_stepM wBM hVBM.2.1
    have hTB := np_v1_mr_assign_stepM wTB hVTB.2.1
    exact ⟨hTr.1, hTr.2.1, hTr.2.2,
      by rw [← evalStatementM_bm_eq]; exact hBM.1,
      by rw [← stepM_bm_eq]; exact hBM.2,
      hTB.1, hTB.2, stepTB_wfLive hwfTB hTB.2,
      hVBM.2.2.2, hVTB.2.2.2⟩
  · intro ty fields sz off locals2 mBM mBM1 mBMf mTB mTB1 mTBf hSt hSz hOff hOk hSet wBM hwfTB wTB
    have hVBM := (np_v1_evalValueM_nullaryOp_M allocBaseBM provAllocIdBM s.frame.locals s.memory
      cur.localDecls cur.layouts { mBM with mem := { mBM.mem with accesses := [] } } hPtr8).2.2.1
      ty fields sz off hSz hOff hOk
    have hVTB := (np_v1_evalValueM_nullaryOp_M allocBaseTB provAllocIdTB s.frame.locals s.memory
      cur.localDecls cur.layouts { mTB with mem := { mTB.mem with accesses := [] } } hPtr8).2.2.1
      ty fields sz off hSz hOff hOk
    have hTr := np_v1_trusted_assign_step body bb s dstLoc (.offsetOf fields) ty span (.scalar ⟨off, 8⟩)
      slot locals2 hPhase hBb hSt hVBM.1 hLive hGet hSet hProt
    have hBM := np_v1_mr_assign_stepM wBM hVBM.2.1
    have hTB := np_v1_mr_assign_stepM wTB hVTB.2.1
    exact ⟨hTr.1, hTr.2.1, hTr.2.2,
      by rw [← evalStatementM_bm_eq]; exact hBM.1,
      by rw [← stepM_bm_eq]; exact hBM.2,
      hTB.1, hTB.2, stepTB_wfLive hwfTB hTB.2,
      hVBM.2.2, hVTB.2.2⟩
  · intro li locals2 mBM mBM1 mBMf mTB mTB1 mTBf hSt hSet wBM hwfTB wTB
    have hVBM := (np_v1_evalValueM_nullaryOp_M allocBaseBM provAllocIdBM s.frame.locals s.memory
      cur.localDecls cur.layouts { mBM with mem := { mBM.mem with accesses := [] } } hPtr8).2.2.2 li
    have hVTB := (np_v1_evalValueM_nullaryOp_M allocBaseTB provAllocIdTB s.frame.locals s.memory
      cur.localDecls cur.layouts { mTB with mem := { mTB.mem with accesses := [] } } hPtr8).2.2.2 li
    have hTr := np_v1_trusted_assign_step body bb s dstLoc .ubChecks { kind := .bool, layoutIdx := li }
      span (.scalar (boolToScalar true)) slot locals2 hPhase hBb hSt hVBM.1 hLive hGet hSet hProt
    have hBM := np_v1_mr_assign_stepM wBM hVBM.2.1
    have hTB := np_v1_mr_assign_stepM wTB hVTB.2.1
    exact ⟨hTr.1, hTr.2.1, hTr.2.2,
      by rw [← evalStatementM_bm_eq]; exact hBM.1,
      by rw [← stepM_bm_eq]; exact hBM.2,
      hTB.1, hTB.2, stepTB_wfLive hwfTB hTB.2,
      hVBM.2.2.2.1, hVTB.2.2.2.1⟩
  · intro li locals2 mBM mBM1 mBMf mTB mTB1 mTBf hSt hSet wBM hwfTB wTB
    have hVBM := (np_v1_evalValueM_nullaryOp_M allocBaseBM provAllocIdBM s.frame.locals s.memory
      cur.localDecls cur.layouts { mBM with mem := { mBM.mem with accesses := [] } } hPtr8).2.2.2 li
    have hVTB := (np_v1_evalValueM_nullaryOp_M allocBaseTB provAllocIdTB s.frame.locals s.memory
      cur.localDecls cur.layouts { mTB with mem := { mTB.mem with accesses := [] } } hPtr8).2.2.2 li
    have hTr := np_v1_trusted_assign_step body bb s dstLoc .ubChecks { kind := .bool, layoutIdx := li }
      span (.scalar (boolToScalar true)) slot locals2 hPhase hBb hSt hVBM.1 hLive hGet hSet hProt
    have hBM := np_v1_mr_assign_stepM wBM hVBM.2.2.1
    have hTB := np_v1_mr_assign_stepM wTB hVTB.2.2.1
    exact ⟨hTr.1, hTr.2.1, hTr.2.2,
      by rw [← evalStatementM_bm_eq]; exact hBM.1,
      by rw [← stepM_bm_eq]; exact hBM.2,
      hTB.1, hTB.2, stepTB_wfLive hwfTB hTB.2,
      hVBM.2.2.2.2.1, hVTB.2.2.2.2.1⟩

/-- **V1 Universal Dead-Destination UB Lockstep (`Mach` & `MachTB`)**:
whenever a `Rvalue.nullaryOp` evaluates cleanly (`evalNullaryOp = .ok tv ...`)
and the destination local is dead on BOTH Trusted (`get? locals dstLoc = some .dead`)
and MiniRust (`mapGet fr.locals mrDst = none`), Trusted `evalStmt`/`stepMirFn`,
MiniRust `Interp.step` (`Mach`), and MiniRust `Interp.stepTB` (`MachTB`) ALL
fault with `.ub`. -/
theorem np_v1_nullaryOp_dead_dst_ub_lockstep (body : CapturedMir) (bb : BasicBlockData)
    (s : MachineState) (dstLoc : Nat) (op : NullOp) (argTy : MirAst.Ty) (span : String)
    (tv : MirSemantics.Value) (mrDst : Gen.LocalName) (mrSrc : Gen.ValueExpr)
    (mBM : Mach) (mTB : MachTB)
    (hPhase : (s.memory.activeCallee.getD body).phase = .runtimePostCleanup)
    (hBb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx = some bb)
    (hSt : get? bb.statements s.frame.stmtIdx =
      some { kind := .assign (locPlace dstLoc) (.nullaryOp op argTy), span := span })
    (hNull : evalNullaryOp s.frame.locals op argTy s.memory
      (s.memory.activeCallee.getD body).localDecls (s.memory.activeCallee.getD body).layouts =
      .ok tv s.frame.locals s.memory)
    (hDeadT : get? s.frame.locals dstLoc = some .dead)
    (wBM : NpMrDeadAssignFrame mBM mrDst mrSrc)
    (wTB : NpMrDeadAssignFrame mTB mrDst mrSrc) :
    let cur := s.memory.activeCallee.getD body
    evalStmt s { kind := .assign (locPlace dstLoc) (.nullaryOp op argTy), span := span }
        cur.localDecls cur.layouts = MirStepNode.fail .ub ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    Interp.evalStatement { mBM with mem := { mBM.mem with accesses := [] } }
        (.Assign (.Local mrDst) mrSrc) = .error (.ub "access to a dead local") ∧
    Interp.step mBM = .error (.ub "access to a dead local") ∧
    evalStatementM { mTB with mem := { mTB.mem with accesses := [] } }
        (.Assign (.Local mrDst) mrSrc) = .error (.ub "access to a dead local") ∧
    Interp.stepTB mTB = .error (.ub "access to a dead local") := by
  have hEvT : evalStmt s { kind := .assign (locPlace dstLoc) (.nullaryOp op argTy), span := span }
      (s.memory.activeCallee.getD body).localDecls (s.memory.activeCallee.getD body).layouts =
      MirStepNode.fail .ub := by
    simp only [evalStmt, evalRvalue, hNull, locPlace, hDeadT]
  have hStepT : stepMirFn body s = MirStepNode.fail .ub := by
    unfold stepMirFn
    dsimp only
    rw [hPhase, hBb]
    dsimp only
    rw [hSt]
    exact hEvT
  have hMrDead : ∀ {M : Type} [Gen.Memory M] [MemoryOps M] {m : Machine M}
      (w : NpMrDeadAssignFrame m mrDst mrSrc),
      evalStatementM { m with mem := { m.mem with accesses := [] } }
          (.Assign (.Local mrDst) mrSrc) = .error (.ub "access to a dead local") ∧
      stepM m = .error (.ub "access to a dead local") := by
    intro M _ _ m w
    have hPl : evalPlaceM { m with mem := { m.mem with accesses := [] } } (.Local mrDst) =
        .error (.ub "access to a dead local") := by
      unfold evalPlaceM
      simp only [w.hCur, w.hDecl, w.hDead, bind, Except.bind, Interp.ub]
    have hEv : evalStatementM { m with mem := { m.mem with accesses := [] } }
        (.Assign (.Local mrDst) mrSrc) = .error (.ub "access to a dead local") := by
      dsimp only [evalStatementM]
      rw [hPl]; rfl
    exact ⟨hEv, np_stepM_error_of_evalStatementM w.fr w.blk (.Assign (.Local mrDst) mrSrc)
      w.hEn w.hPick w.hCur w.hBlk w.hNe w.hStmt hEv⟩
  have hBM := hMrDead wBM
  have hTB := hMrDead wTB
  exact ⟨hEvT, hStepT,
    by rw [← evalStatementM_bm_eq]; exact hBM.1,
    by rw [← stepM_bm_eq]; exact hBM.2,
    hTB.1, hTB.2⟩

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

/-! ### `V1` Kernel-Checked Inhabitation & Non-Vacuity of `NpMrAssignFrame` / `NpMrDeadAssignFrame` -/

private theorem np_evalPlaceM_local_of_ok {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (mrDst : Gen.LocalName) (fr : StackFrame M) (dstTy : Gen.Type)
    (ptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (hCur : curFrameM m = .ok fr)
    (hDecl : mapIndex fr.func.locals mrDst "self.cur_frame().func.locals[name]" = .ok dstTy)
    (hLive : mapGet fr.locals mrDst = some ptr) :
    evalPlaceM m (.Local mrDst) =
      .ok (({ ptr := ThinPointer.widen ptr none, aligned := true }, dstTy), m) := by
  unfold evalPlaceM
  simp only [hCur, hDecl, hLive, bind, Except.bind, pure, Except.pure]

/-- Pure `Bool` checker for the frame, live-local, memory-store, PC-increment,
and data-race side-conditions of `NpMrAssignFrame` (decidable with zero
`DecidableEq` on `Statement`/`Type`). -/
private def npCheckAssignStepSideOk {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (mrDst : Gen.LocalName) (mv : Gen.Value M) (dstTy : Gen.Type) : Bool :=
  let m0 : Machine M := { m with mem := { m.mem with accesses := [] } }
  match m.threads.any (fun th => decide (th.state = .Enabled)) with
  | false => false
  | true =>
    match pickActiveThreadM m0 with
    | .error _ => false
    | .ok tid =>
      match decide (tid = m.active_thread) with
      | false => false
      | true =>
        match curFrameM m0 with
        | .error _ => false
        | .ok fr =>
          match mapIndex fr.func.blocks fr.next_block "frame.func.blocks[frame.next_block]" with
          | .error _ => false
          | .ok blk =>
            match decide (fr.next_stmt = (blk.statements.length : Int)) with
            | true => false
            | false =>
              match mapGet fr.locals mrDst with
              | none => false
              | some ptr =>
                let pl : Gen.Place M := { ptr := ThinPointer.widen ptr none, aligned := true }
                match placeStoreM m0 pl mv dstTy with
                | .error _ => false
                | .ok m1 =>
                  match mutateCurFrameM m1 (fun f => { f with next_stmt := f.next_stmt + 1 }) with
                  | .error _ => false
                  | .ok mAfter =>
                    match ConcurrentMemory.check_data_races mAfter.mem mAfter.active_thread
                        (setInsert m.synchronized_threads m.active_thread, m.mem.accesses) with
                    | .ok () => true
                    | .error _ => false

private theorem np_assign_frame_of_check {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (mrDst : Gen.LocalName) (mrSrc : Gen.ValueExpr)
    (mv : Gen.Value M) (dstTy : Gen.Type)
    (hOk : npCheckAssignStepSideOk m mrDst mv dstTy = true)
    (hStmt : (do
      let fr ← curFrameM { m with mem := { m.mem with accesses := [] } }
      let blk ← mapIndex fr.func.blocks fr.next_block "frame.func.blocks[frame.next_block]"
      listIndex blk.statements fr.next_stmt "block.statements[frame.next_stmt]") =
      .ok (.Assign (.Local mrDst) mrSrc))
    (hDecl : (do
      let fr ← curFrameM { m with mem := { m.mem with accesses := [] } }
      mapIndex fr.func.locals mrDst "self.cur_frame().func.locals[name]") = .ok dstTy) :
    ∃ m1 mAfter, Nonempty (NpMrAssignFrame m m1 mAfter mrDst mrSrc mv dstTy) := by
  unfold npCheckAssignStepSideOk at hOk
  dsimp only at hOk
  cases hEn : m.threads.any (fun th => decide (th.state = .Enabled)) with
  | false => simp [hEn] at hOk
  | true =>
    simp only [hEn] at hOk
    cases hPick : pickActiveThreadM { m with mem := { m.mem with accesses := [] } } with
    | error _ => simp [hPick] at hOk
    | ok tid =>
      simp only [hPick] at hOk
      cases hTid : decide (tid = m.active_thread) with
      | false => simp [hTid] at hOk
      | true =>
        simp only [hTid] at hOk
        have hTidEq : tid = m.active_thread := of_decide_eq_true hTid
        subst hTidEq
        cases hCur : curFrameM { m with mem := { m.mem with accesses := [] } } with
        | error _ => simp [hCur] at hOk
        | ok fr =>
          simp only [hCur] at hOk
          cases hBlk : mapIndex fr.func.blocks fr.next_block "frame.func.blocks[frame.next_block]" with
          | error _ => simp [hBlk] at hOk
          | ok blk =>
            simp only [hBlk] at hOk
            cases hEqLen : decide (fr.next_stmt = (blk.statements.length : Int)) with
            | true => simp [hEqLen] at hOk
            | false =>
              simp only [hEqLen] at hOk
              have hNe : fr.next_stmt ≠ (blk.statements.length : Int) := of_decide_eq_false hEqLen
              cases hPtr : mapGet fr.locals mrDst with
              | none => simp [hPtr] at hOk
              | some ptr =>
                simp only [hPtr] at hOk
                cases hSt : placeStoreM { m with mem := { m.mem with accesses := [] } }
                    { ptr := ThinPointer.widen ptr none, aligned := true } mv dstTy with
                | error _ => simp [hSt] at hOk
                | ok m1 =>
                  simp only [hSt] at hOk
                  cases hMut : mutateCurFrameM m1 (fun f => { f with next_stmt := f.next_stmt + 1 }) with
                  | error _ => simp [hMut] at hOk
                  | ok mAfter =>
                    simp only [hMut] at hOk
                    cases hRace : ConcurrentMemory.check_data_races mAfter.mem mAfter.active_thread
                        (setInsert m.synchronized_threads m.active_thread, m.mem.accesses) with
                    | error _ => simp [hRace] at hOk
                    | ok u =>
                      cases u
                      simp only [hCur, hBlk, bind, Except.bind] at hStmt
                      simp only [hCur, bind, Except.bind] at hDecl
                      exact ⟨m1, mAfter, ⟨{
                        fr := fr, blk := blk,
                        place := { ptr := ThinPointer.widen ptr none, aligned := true },
                        hEn := hEn, hPick := hPick, hCur := hCur, hBlk := hBlk,
                        hNe := hNe, hStmt := hStmt,
                        hp := np_evalPlaceM_local_of_ok _ mrDst fr dstTy ptr hCur hDecl hPtr,
                        hst := hSt, hMut := hMut, hRace := hRace }⟩⟩

/-- Pure `Bool` checker for the frame and dead-local side-conditions of
`NpMrDeadAssignFrame`. -/
private def npCheckDeadAssignSideOk {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (mrDst : Gen.LocalName) : Bool :=
  let m0 : Machine M := { m with mem := { m.mem with accesses := [] } }
  match m.threads.any (fun th => decide (th.state = .Enabled)) with
  | false => false
  | true =>
    match pickActiveThreadM m0 with
    | .error _ => false
    | .ok tid =>
      match decide (tid = m.active_thread) with
      | false => false
      | true =>
        match curFrameM m0 with
        | .error _ => false
        | .ok fr =>
          match mapIndex fr.func.blocks fr.next_block "frame.func.blocks[frame.next_block]" with
          | .error _ => false
          | .ok blk =>
            match decide (fr.next_stmt = (blk.statements.length : Int)) with
            | true => false
            | false =>
              match mapGet fr.locals mrDst with
              | none => true
              | some _ => false

private theorem np_dead_assign_frame_of_check {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (mrDst : Gen.LocalName) (mrSrc : Gen.ValueExpr) (dstTy : Gen.Type)
    (hOk : npCheckDeadAssignSideOk m mrDst = true)
    (hStmt : (do
      let fr ← curFrameM { m with mem := { m.mem with accesses := [] } }
      let blk ← mapIndex fr.func.blocks fr.next_block "frame.func.blocks[frame.next_block]"
      listIndex blk.statements fr.next_stmt "block.statements[frame.next_stmt]") =
      .ok (.Assign (.Local mrDst) mrSrc))
    (hDecl : (do
      let fr ← curFrameM { m with mem := { m.mem with accesses := [] } }
      mapIndex fr.func.locals mrDst "self.cur_frame().func.locals[name]") = .ok dstTy) :
    Nonempty (NpMrDeadAssignFrame m mrDst mrSrc) := by
  unfold npCheckDeadAssignSideOk at hOk
  dsimp only at hOk
  cases hEn : m.threads.any (fun th => decide (th.state = .Enabled)) with
  | false => simp [hEn] at hOk
  | true =>
    simp only [hEn] at hOk
    cases hPick : pickActiveThreadM { m with mem := { m.mem with accesses := [] } } with
    | error _ => simp [hPick] at hOk
    | ok tid =>
      simp only [hPick] at hOk
      cases hTid : decide (tid = m.active_thread) with
      | false => simp [hTid] at hOk
      | true =>
        simp only [hTid] at hOk
        have hTidEq : tid = m.active_thread := of_decide_eq_true hTid
        subst hTidEq
        cases hCur : curFrameM { m with mem := { m.mem with accesses := [] } } with
        | error _ => simp [hCur] at hOk
        | ok fr =>
          simp only [hCur] at hOk
          cases hBlk : mapIndex fr.func.blocks fr.next_block "frame.func.blocks[frame.next_block]" with
          | error _ => simp [hBlk] at hOk
          | ok blk =>
            simp only [hBlk] at hOk
            cases hEqLen : decide (fr.next_stmt = (blk.statements.length : Int)) with
            | true => simp [hEqLen] at hOk
            | false =>
              simp only [hEqLen] at hOk
              have hNe : fr.next_stmt ≠ (blk.statements.length : Int) := of_decide_eq_false hEqLen
              cases hDead : mapGet fr.locals mrDst with
              | some _ => simp [hDead] at hOk
              | none =>
                simp only [hCur, hBlk, bind, Except.bind] at hStmt
                simp only [hCur, bind, Except.bind] at hDecl
                exact ⟨{
                  fr := fr, blk := blk, dstTy := dstTy,
                  hEn := hEn, hPick := hPick, hCur := hCur, hBlk := hBlk,
                  hNe := hNe, hStmt := hStmt, hDecl := hDecl, hDead := hDead }⟩

/-- Standalone `align_of` MIR fixture (stmt 0 is `.nullaryOp .alignOf npTuple16MirTy`)
for direct `NpMrAssignFrame` inhabitation. -/
def v1AlignOfOnlyMir : CapturedMir :=
  mkMirBody "np::v1_align_of_only" [mkDecl usizeMirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.nullaryOp .alignOf npTuple16MirTy))] .return_]

/-- MiniRust machine for `v1AlignOfOnlyMir`. -/
def v1AlignOfOnlyMach : Mach :=
  let fn := mkMrFn [(localName 0, usizeMrTy)] [] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0))
        (.UnOp (.ComputeAlign npTuple16MrTy) (.Tuple [] unitType))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) [mkStackAlloc 128 (List.replicate 8 .Uninit) 8]
    [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]]

/-- Dead-destination `nullaryOp` MIR fixture (initialized via standard
`initMachineState`, where non-argument local `_1` begins `.dead`) for direct
`NpMrDeadAssignFrame` inhabitation. -/
def v1DeadDstMir : CapturedMir :=
  mkMirBody "np::v1_dead_dst" [mkDecl usizeMirTy, mkDecl usizeMirTy] 0
    [mkBb [mkSt (.assign (locPlace 1) (.nullaryOp .sizeOf npTuple16MirTy))] .return_]

/-- MiniRust machine for `v1DeadDstMir` (`localName 1` is declared in `fn.locals`
as `usizeMrTy` but absent from `fr.locals`). -/
def v1DeadDstMach : Mach :=
  let fn := mkMrFn [(localName 0, usizeMrTy), (localName 1, usizeMrTy)] [] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 1))
        (.UnOp (.ComputeSize npTuple16MrTy) (.Tuple [] unitType))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) [mkStackAlloc 128 (List.replicate 8 .Uninit) 8]
    [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]]

/-- **Kernel-Checked Inhabitation & Non-Vacuity of `NpMrAssignFrame` and
`NpMrDeadAssignFrame` (Instantiating `np_v1_nullaryOp_coupled_step_sim_all_four`
and `np_v1_nullaryOp_dead_dst_ub_lockstep` on BOTH `Mach` and `MachTB`)**:
explicitly constructs `NpMrAssignFrame` inhabitants on BOTH `Mach` and `MachTB`
for all 5 arms of `np_v1_nullaryOp_coupled_step_sim_all_four` (`.sizeOf`,
`.alignOf`, `.offsetOf`, `.ubChecks` via `u8` `Switch` lowering, and `.ubChecks`
via native `.Bool` lowering) plus `NpMrDeadAssignFrame` inhabitants on BOTH
`Mach` and `MachTB` for `np_v1_nullaryOp_dead_dst_ub_lockstep`, and derives
every single operational step, `MachTB.wfLive` preservation, `Ep2ValRel`
agreement, and dead-local UB lockstep directly by instantiating those two
universal theorems. -/
theorem np_v1_nullaryOp_frame_inhabitation_and_nonvacuity :
    -- 1. `.sizeOf` on `v1NullaryTupleMir` / `v1NullaryTupleMach` (Mach & MachTB)
    ((∃ s', stepMirFn v1NullaryTupleMir (npInitLiveState v1NullaryTupleMir []) = .tau (.running s') ∧
        get? s'.frame.locals 1 = some (.init (.scalar ⟨16, 8⟩))) ∧
      (∃ mBMf, Interp.step v1NullaryTupleMach = .ok mBMf) ∧
      (∃ mTBf, Interp.stepTB (liftMachToTB v1NullaryTupleMach) = .ok mTBf ∧ MachTB.wfLive mTBf) ∧
      Ep2ValRel (M := BM) (fun _ => 0) (fun _ => 0) (.scalar ⟨16, 8⟩) (.Int (Int.ofNat 16))) ∧
    -- 2. `.alignOf` on `v1AlignOfOnlyMir` / `v1AlignOfOnlyMach` (Mach & MachTB)
    ((∃ s', stepMirFn v1AlignOfOnlyMir (npInitLiveState v1AlignOfOnlyMir []) = .tau (.running s') ∧
        get? s'.frame.locals 0 = some (.init (.scalar ⟨8, 8⟩))) ∧
      (∃ mBMf, Interp.step v1AlignOfOnlyMach = .ok mBMf) ∧
      (∃ mTBf, Interp.stepTB (liftMachToTB v1AlignOfOnlyMach) = .ok mTBf ∧ MachTB.wfLive mTBf) ∧
      Ep2ValRel (M := BM) (fun _ => 0) (fun _ => 0) (.scalar ⟨8, 8⟩) (.Int (Int.ofNat 8))) ∧
    -- 3. `.offsetOf [(0, 1)]` on `v1NullaryPaddedOffsetMir` / `v1NullaryPaddedOffsetMach`
    ((∃ s', stepMirFn v1NullaryPaddedOffsetMir (npInitLiveState v1NullaryPaddedOffsetMir []) =
        .tau (.running s') ∧
        get? s'.frame.locals 0 = some (.init (.scalar ⟨4, 8⟩))) ∧
      (∃ mBMf, Interp.step v1NullaryPaddedOffsetMach = .ok mBMf) ∧
      (∃ mTBf, Interp.stepTB (liftMachToTB v1NullaryPaddedOffsetMach) = .ok mTBf ∧
        MachTB.wfLive mTBf) ∧
      Ep2ValRel (M := BM) (fun _ => 0) (fun _ => 0) (.scalar ⟨4, 8⟩) (.Int (Int.ofNat 4))) ∧
    -- 4a. `.ubChecks` (`u8` lowering) on `v1NullaryUbBranchMir` / `v1NullaryUbBranchMach`
    ((∃ s', stepMirFn v1NullaryUbBranchMir (npInitLiveState v1NullaryUbBranchMir []) =
        .tau (.running s') ∧
        get? s'.frame.locals 1 = some (.init (.scalar (boolToScalar true)))) ∧
      (∃ mBMf, Interp.step v1NullaryUbBranchMach = .ok mBMf) ∧
      (∃ mTBf, Interp.stepTB (liftMachToTB v1NullaryUbBranchMach) = .ok mTBf ∧
        MachTB.wfLive mTBf) ∧
      Ep2ValRel (M := BM) (fun _ => 0) (fun _ => 0) (.scalar (boolToScalar true)) (.Int 1)) ∧
    -- 4b. `.ubChecks` (native `.Bool` lowering) on `v1NullaryUbChecksMir` / `v1NullaryUbChecksMach`
    ((∃ s', stepMirFn v1NullaryUbChecksMir (npInitLiveState v1NullaryUbChecksMir []) =
        .tau (.running s') ∧
        get? s'.frame.locals 0 = some (.init (.scalar (boolToScalar true)))) ∧
      (∃ mBMf, Interp.step v1NullaryUbChecksMach = .ok mBMf) ∧
      (∃ mTBf, Interp.stepTB (liftMachToTB v1NullaryUbChecksMach) = .ok mTBf ∧
        MachTB.wfLive mTBf) ∧
      Type.encodeM (M := BM) .Bool (.Bool true) = .ok [.Init 1 none]) ∧
    -- 5. Dead-destination UB lockstep via `NpMrDeadAssignFrame` on `v1DeadDstMir` / `v1DeadDstMach`
    (stepMirFn v1DeadDstMir (initMachineState v1DeadDstMir []) = MirStepNode.fail .ub ∧
      Interp.step v1DeadDstMach = .error (.ub "access to a dead local") ∧
      Interp.stepTB (liftMachToTB v1DeadDstMach) = .error (.ub "access to a dead local")) := by
  have hNeDead : LocalSlot.uninit ≠ .dead := fun h => nomatch h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. `.sizeOf`
    obtain ⟨mBM1, mBMf, ⟨wBM⟩⟩ := np_assign_frame_of_check (M := BM) v1NullaryTupleMach (localName 1)
      (.UnOp (.ComputeSize npTuple16MrTy) (.Tuple [] unitType)) (.Int (Int.ofNat 16)) usizeMrTy
      (by decide +kernel) rfl rfl
    obtain ⟨mTB1, mTBf, ⟨wTB⟩⟩ := np_assign_frame_of_check (M := TBM)
      (liftMachToTB v1NullaryTupleMach) (localName 1)
      (.UnOp (.ComputeSize npTuple16MrTy) (.Tuple [] unitType)) (.Int (Int.ofNat 16)) usizeMrTy
      (by decide +kernel) rfl rfl
    have hSim := (np_v1_nullaryOp_coupled_step_sim_all_four
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      v1NullaryTupleMir ((get? v1NullaryTupleMir.basicBlocks 0).getD (mkBb [] .return_))
      (npInitLiveState v1NullaryTupleMir []) 1 dummySpan .uninit (localName 1)
      rfl rfl rfl hNeDead rfl rfl).1
      npTuple16MirTy npTuple16MrTy 16 ⟨8⟩
      ((set? (npInitLiveState v1NullaryTupleMir []).frame.locals 1 (.init (.scalar ⟨16, 8⟩))).getD [])
      v1NullaryTupleMach mBM1 mBMf (liftMachToTB v1NullaryTupleMach) mTB1 mTBf
      rfl (by decide +kernel) (by decide +kernel) rfl
      rfl np_v1_minirust_layout_and_offset_agreement.1 wBM (liftMachToTB_wfLive v1NullaryTupleMach) wTB
    exact ⟨⟨_, hSim.2.1, hSim.2.2.1⟩, ⟨mBMf, hSim.2.2.2.2.1⟩,
      ⟨mTBf, hSim.2.2.2.2.2.2.1, hSim.2.2.2.2.2.2.2.1⟩, hSim.2.2.2.2.2.2.2.2.1⟩
  · -- 2. `.alignOf`
    obtain ⟨mBM1, mBMf, ⟨wBM⟩⟩ := np_assign_frame_of_check (M := BM) v1AlignOfOnlyMach (localName 0)
      (.UnOp (.ComputeAlign npTuple16MrTy) (.Tuple [] unitType)) (.Int (Int.ofNat 8)) usizeMrTy
      (by decide +kernel) rfl rfl
    obtain ⟨mTB1, mTBf, ⟨wTB⟩⟩ := np_assign_frame_of_check (M := TBM)
      (liftMachToTB v1AlignOfOnlyMach) (localName 0)
      (.UnOp (.ComputeAlign npTuple16MrTy) (.Tuple [] unitType)) (.Int (Int.ofNat 8)) usizeMrTy
      (by decide +kernel) rfl rfl
    have hSim := (np_v1_nullaryOp_coupled_step_sim_all_four
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      v1AlignOfOnlyMir ((get? v1AlignOfOnlyMir.basicBlocks 0).getD (mkBb [] .return_))
      (npInitLiveState v1AlignOfOnlyMir []) 0 dummySpan .uninit (localName 0)
      rfl rfl rfl hNeDead rfl rfl).2.1
      npTuple16MirTy npTuple16MrTy 16 8 ⟨16⟩
      ((set? (npInitLiveState v1AlignOfOnlyMir []).frame.locals 0 (.init (.scalar ⟨8, 8⟩))).getD [])
      v1AlignOfOnlyMach mBM1 mBMf (liftMachToTB v1AlignOfOnlyMach) mTB1 mTBf
      rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
      rfl np_v1_minirust_layout_and_offset_agreement.1 wBM (liftMachToTB_wfLive v1AlignOfOnlyMach) wTB
    exact ⟨⟨_, hSim.2.1, hSim.2.2.1⟩, ⟨mBMf, hSim.2.2.2.2.1⟩,
      ⟨mTBf, hSim.2.2.2.2.2.2.1, hSim.2.2.2.2.2.2.2.1⟩, hSim.2.2.2.2.2.2.2.2.1⟩
  · -- 3. `.offsetOf [(0, 1)]`
    obtain ⟨mBM1, mBMf, ⟨wBM⟩⟩ := np_assign_frame_of_check (M := BM) v1NullaryPaddedOffsetMach (localName 0)
      (.Constant (.Int (Int.ofNat 4)) usizeMrTy) (.Int (Int.ofNat 4)) usizeMrTy
      (by decide +kernel) rfl rfl
    obtain ⟨mTB1, mTBf, ⟨wTB⟩⟩ := np_assign_frame_of_check (M := TBM)
      (liftMachToTB v1NullaryPaddedOffsetMach) (localName 0)
      (.Constant (.Int (Int.ofNat 4)) usizeMrTy) (.Int (Int.ofNat 4)) usizeMrTy
      (by decide +kernel) rfl rfl
    have hSim := (np_v1_nullaryOp_coupled_step_sim_all_four
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      v1NullaryPaddedOffsetMir ((get? v1NullaryPaddedOffsetMir.basicBlocks 0).getD (mkBb [] .return_))
      (npInitLiveState v1NullaryPaddedOffsetMir []) 0 dummySpan .uninit (localName 0)
      rfl rfl rfl hNeDead rfl rfl).2.2.1
      npPaddedMirTy [(0, 1)] 8 4
      ((set? (npInitLiveState v1NullaryPaddedOffsetMir []).frame.locals 0 (.init (.scalar ⟨4, 8⟩))).getD [])
      v1NullaryPaddedOffsetMach mBM1 mBMf (liftMachToTB v1NullaryPaddedOffsetMach) mTB1 mTBf
      rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
      wBM (liftMachToTB_wfLive v1NullaryPaddedOffsetMach) wTB
    exact ⟨⟨_, hSim.2.1, hSim.2.2.1⟩, ⟨mBMf, hSim.2.2.2.2.1⟩,
      ⟨mTBf, hSim.2.2.2.2.2.2.1, hSim.2.2.2.2.2.2.2.1⟩, hSim.2.2.2.2.2.2.2.2.1⟩
  · -- 4a. `.ubChecks` (`u8` `Switch` lowering)
    obtain ⟨mBM1, mBMf, ⟨wBM⟩⟩ := np_assign_frame_of_check (M := BM) v1NullaryUbBranchMach (localName 1)
      (.Constant (.Int 1) u8MrTy) (.Int 1) u8MrTy
      (by decide +kernel) rfl rfl
    obtain ⟨mTB1, mTBf, ⟨wTB⟩⟩ := np_assign_frame_of_check (M := TBM)
      (liftMachToTB v1NullaryUbBranchMach) (localName 1)
      (.Constant (.Int 1) u8MrTy) (.Int 1) u8MrTy
      (by decide +kernel) rfl rfl
    have hSim := (np_v1_nullaryOp_coupled_step_sim_all_four
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      v1NullaryUbBranchMir ((get? v1NullaryUbBranchMir.basicBlocks 0).getD (mkBb [] .return_))
      (npInitLiveState v1NullaryUbBranchMir []) 1 dummySpan .uninit (localName 1)
      rfl rfl rfl hNeDead rfl rfl).2.2.2.1
      0 ((set? (npInitLiveState v1NullaryUbBranchMir []).frame.locals 1
          (.init (.scalar (boolToScalar true)))).getD [])
      v1NullaryUbBranchMach mBM1 mBMf (liftMachToTB v1NullaryUbBranchMach) mTB1 mTBf
      rfl rfl wBM (liftMachToTB_wfLive v1NullaryUbBranchMach) wTB
    exact ⟨⟨_, hSim.2.1, hSim.2.2.1⟩, ⟨mBMf, hSim.2.2.2.2.1⟩,
      ⟨mTBf, hSim.2.2.2.2.2.2.1, hSim.2.2.2.2.2.2.2.1⟩, hSim.2.2.2.2.2.2.2.2.1⟩
  · -- 4b. `.ubChecks` (native `.Bool` lowering)
    obtain ⟨mBM1, mBMf, ⟨wBM⟩⟩ := np_assign_frame_of_check (M := BM) v1NullaryUbChecksMach (localName 0)
      (.Constant (.Bool true) .Bool) (.Bool true) .Bool
      (by decide +kernel) rfl rfl
    obtain ⟨mTB1, mTBf, ⟨wTB⟩⟩ := np_assign_frame_of_check (M := TBM)
      (liftMachToTB v1NullaryUbChecksMach) (localName 0)
      (.Constant (.Bool true) .Bool) (.Bool true) .Bool
      (by decide +kernel) rfl rfl
    have hSim := (np_v1_nullaryOp_coupled_step_sim_all_four
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      v1NullaryUbChecksMir ((get? v1NullaryUbChecksMir.basicBlocks 0).getD (mkBb [] .return_))
      (npInitLiveState v1NullaryUbChecksMir []) 0 dummySpan .uninit (localName 0)
      rfl rfl rfl hNeDead rfl rfl).2.2.2.2
      0 ((set? (npInitLiveState v1NullaryUbChecksMir []).frame.locals 0
          (.init (.scalar (boolToScalar true)))).getD [])
      v1NullaryUbChecksMach mBM1 mBMf (liftMachToTB v1NullaryUbChecksMach) mTB1 mTBf
      rfl rfl wBM (liftMachToTB_wfLive v1NullaryUbChecksMach) wTB
    exact ⟨⟨_, hSim.2.1, hSim.2.2.1⟩, ⟨mBMf, hSim.2.2.2.2.1⟩,
      ⟨mTBf, hSim.2.2.2.2.2.2.1, hSim.2.2.2.2.2.2.2.1⟩, hSim.2.2.2.2.2.2.2.2.1⟩
  · -- 5. Dead-destination UB lockstep (`NpMrDeadAssignFrame`)
    obtain ⟨wDeadBM⟩ := np_dead_assign_frame_of_check (M := BM) v1DeadDstMach (localName 1)
      (.UnOp (.ComputeSize npTuple16MrTy) (.Tuple [] unitType)) usizeMrTy
      (by decide +kernel) rfl rfl
    obtain ⟨wDeadTB⟩ := np_dead_assign_frame_of_check (M := TBM)
      (liftMachToTB v1DeadDstMach) (localName 1)
      (.UnOp (.ComputeSize npTuple16MrTy) (.Tuple [] unitType)) usizeMrTy
      (by decide +kernel) rfl rfl
    have hNull : evalNullaryOp (initMachineState v1DeadDstMir []).frame.locals .sizeOf
        npTuple16MirTy (initMachineState v1DeadDstMir []).memory
        ((initMachineState v1DeadDstMir []).memory.activeCallee.getD v1DeadDstMir).localDecls
        ((initMachineState v1DeadDstMir []).memory.activeCallee.getD v1DeadDstMir).layouts =
        .ok (.scalar ⟨16, 8⟩) (initMachineState v1DeadDstMir []).frame.locals
          (initMachineState v1DeadDstMir []).memory :=
      np_v1_nullary_sizeOf_of_intrinsic (initMachineState v1DeadDstMir []).frame.locals
        npTuple16MirTy (initMachineState v1DeadDstMir []).memory
        v1DeadDstMir.localDecls v1DeadDstMir.layouts 16 (by decide +kernel) (by decide +kernel)
    have hDead := np_v1_nullaryOp_dead_dst_ub_lockstep v1DeadDstMir
      ((get? v1DeadDstMir.basicBlocks 0).getD (mkBb [] .return_))
      (initMachineState v1DeadDstMir []) 1 .sizeOf npTuple16MirTy dummySpan
      (.scalar ⟨16, 8⟩) (localName 1)
      (.UnOp (.ComputeSize npTuple16MrTy) (.Tuple [] unitType))
      v1DeadDstMach (liftMachToTB v1DeadDstMach)
      rfl rfl rfl hNull rfl wDeadBM wDeadTB
    exact ⟨hDead.2.1, hDead.2.2.2.1, hDead.2.2.2.2.2⟩

/-! ### Multi-Hop Nested `offset_of!`, Multi-Variant Enum `offset_of!`, & Fail-Closed `.unsupported` Parity (`V1`) -/

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

/-- MiniRust `OuterNested { u8, PaddedU8U32 }` tuple type (size 12, align 4). -/
@[reducible] def npOuterNestedMrTy : Gen.Type :=
  .Tuple [(⟨0⟩, u8MrTy), (⟨4⟩, npPaddedU8U32MrTy)] ⟨⟨12⟩, ⟨4⟩, none⟩ none

/-- MiniRust variant table for `npEnumMrTy`: variant `0` is unit, variant `1`
places its two `u32` fields at offsets `4` and `8`. -/
def npEnumVariants : Map Int Gen.Variant :=
  ⟨[(0, ⟨.Tuple [] ⟨⟨12⟩, ⟨4⟩, none⟩ none, ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, 0))]⟩⟩),
    (1, ⟨.Tuple [(⟨4⟩, u32MrTy), (⟨8⟩, u32MrTy)] ⟨⟨12⟩, ⟨4⟩, none⟩ none,
         ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, 1))]⟩⟩)]⟩

/-- MiniRust 2-variant `Enum` type matching `npEnumMirLayout` (size 12, align 4). -/
@[reducible] def npEnumMrTy : Gen.Type :=
  .Enum npEnumVariants ⟨.Unsigned, ⟨1⟩⟩
    (.Branch ⟨0⟩ ⟨.Unsigned, ⟨1⟩⟩ .Invalid ⟨[((0, 1), .Known 0), ((1, 2), .Known 1)]⟩)
    ⟨12⟩ ⟨4⟩

/-- Multi-hop `(variantIdx, fieldIdx)` byte-offset query on MiniRust `Tuple` and
`Enum` types, failing closed with `none` on out-of-range variants or fields. -/
def npOffsetOfMrPath : Gen.Type → List (Nat × Nat) → Option Nat
  | _, [] => some 0
  | .Tuple fields _ _, (0, i) :: rest =>
    match fields[i]? with
    | some (off, fTy) => (npOffsetOfMrPath fTy rest).map (fun tail => off.bytes + tail)
    | none => none
  | .Enum variants _ _ _ _, (v, i) :: rest =>
    match mapGet variants (Int.ofNat v) with
    | some var =>
      match var.ty with
      | .Tuple fields _ _ =>
        match fields[i]? with
        | some (off, fTy) => (npOffsetOfMrPath fTy rest).map (fun tail => off.bytes + tail)
        | none => none
      | _ => none
    | none => none
  | _, _ :: _ => none

def npV1MultiHopOffsetMir : CapturedMir :=
  mkMirBody "np::w_v1_multihop_offset" [mkDecl usizeMirTy, mkDecl npOuterNestedMirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.nullaryOp (.offsetOf [(0, 1), (0, 1)]) npOuterNestedMirTy))]
      .return_]
    npNestedLayouts

def npV1EnumOffsetMir : CapturedMir :=
  mkMirBody "np::w_v1_enum_offset" [mkDecl usizeMirTy, mkDecl npEnumMirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.nullaryOp (.offsetOf [(1, 1)]) npEnumMirTy))] .return_]
    npNestedLayouts

def npV1OobOffsetMir : CapturedMir :=
  mkMirBody "np::w_v1_oob_offset" [mkDecl usizeMirTy, mkDecl npPaddedMirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.nullaryOp (.offsetOf [(0, 99)]) npPaddedMirTy))] .return_]
    npLayouts

def npV1UnresolvedLayoutMir : CapturedMir :=
  mkMirBody "np::w_v1_unresolved_layout" [mkDecl usizeMirTy, mkDecl npUnresolvedAdtMirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.nullaryOp .sizeOf npUnresolvedAdtMirTy))] .return_]

/-- Lowered MiniRust machine for `npV1MultiHopOffsetMir` / `npV1EnumOffsetMir`
(assigning the const-evaluated `usize` `8`). -/
def npV1Offset8Mach : Mach :=
  let fn := mkMrFn [(localName 0, usizeMrTy)] [] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 8) usizeMrTy)],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 8]
    [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]]

/-- Runtime MiniRust machine loading `(_1.1).1` of `npOuterNestedMrTy`, proving
that MiniRust's `evalPlaceM` computes byte offset `4 + 4 = 8` (reading `55` at
bytes `[8, 12)` of allocation `1`). -/
def npV1MultiHopRuntimeLoadMach : Mach :=
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, npOuterNestedMrTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .Assign (.Local (localName 0)) (.Load (.Field (.Field (.Local (localName 1)) 1) 1))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256
       (([.Init 1 none, .Uninit, .Uninit, .Uninit,
          .Init 2 none, .Uninit, .Uninit, .Uninit] : List Byte) ++ scalarBytes u32 55) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]

/-- Runtime MiniRust machine loading `(_1 as Variant1).1` of `npEnumMrTy`,
proving that MiniRust's `evalPlaceM` `.Downcast 1` -> `.Field 1` computes byte
offset `8` (reading `77` at bytes `[8, 12)` of allocation `1`). -/
def npV1EnumRuntimeLoadMach : Mach :=
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, npEnumMrTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .Assign (.Local (localName 0)) (.Load (.Field (.Downcast (.Local (localName 1)) 1) 1))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256
       (([.Init 1 none, .Uninit, .Uninit, .Uninit] : List Byte) ++
        scalarBytes u32 33 ++ scalarBytes u32 77) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]

/-- **`V1` Multi-Hop Nested `offset_of!`, Multi-Variant Enum `offset_of!`, &
Fail-Closed `.unsupported` Boundary Parity (Trusted + MiniRust `Mach` & `MachTB`
with `MachTB.wfLive`)**:
1. Multi-hop nested struct `offset_of!([(0, 1), (0, 1)]) = 4 + 4 = 8` agrees
   across Trusted `evalNullaryOp` / `npRunTrusted` (from `initMachineState`),
   MiniRust `Type.layout` + `npOffsetOfMrPath`, lowered `Mach` / `MachTB`, AND
   runtime `evalPlaceM` nested `.Field (.Field _ 1) 1` load (`55` from offset `8`);
2. Multi-variant enum `offset_of!([(1, 1)]) = 8` agrees across Trusted
   `evalNullaryOp` / `npRunTrusted`, MiniRust `Type.layout` + `npOffsetOfMrPath`,
   lowered `Mach` / `MachTB`, AND runtime `.Downcast 1 -> .Field 1` load (`77`
   from offset `8`);
3. Fail-closed `.unsupported` boundary parity for:
   (a) OOB `offset_of!` (`[(0, 99)]`, unit variant `[(0, 0)]`, out-of-range
       variant `[(2, 0)]`) + `npOffsetOfMrPath = none`,
   (b) unsized `[u32]`, `str`, `dyn Trait` in Trusted `evalNullaryOp`, MiniRust
       `LayoutStrategy.is_sized = false`, and `evalUnOpM (.ComputeSize _)`
       rejecting empty metadata `()`,
   (c) `NullOp.contractChecks = .unsupported`, and
   (d) unresolved ADT layout index (`layoutIdx := 0` in `emptyLayoutTable`). -/
theorem np_v1_multihop_offsetof_and_failclosed_unsupported_three_way_witness :
    -- 1. Multi-hop nested struct `offset_of!([(0, 1), (0, 1)]) = 8`
    evalNullaryOp [] (.offsetOf [(0, 1), (0, 1)]) npOuterNestedMirTy emptyMemory
      npV1MultiHopOffsetMir.localDecls npNestedLayouts = .ok (.scalar ⟨8, 8⟩) [] emptyMemory ∧
    npRunTrusted npV1MultiHopOffsetMir 8 (initMachineState npV1MultiHopOffsetMir []) = .usizeVal 8 ∧
    Type.layout npOuterNestedMrTy = .ok (.Sized ⟨12⟩ ⟨4⟩) ∧
    npOffsetOfMrPath npOuterNestedMrTy [(0, 1), (0, 1)] = some 8 ∧
    (∃ m1, Interp.steps 1 npV1Offset8Mach = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes IntType.usize_ty 8)) ∧
    (∃ m1, Interp.stepsTB 1 (liftMachToTB npV1Offset8Mach) = .ok m1 ∧ MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes IntType.usize_ty 8).map (projByteTB ∘ liftByteTB))) ∧
    (∃ m1, Interp.steps 1 npV1MultiHopRuntimeLoadMach = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 55)) ∧
    (∃ m1, Interp.stepsTB 1 (liftMachToTB npV1MultiHopRuntimeLoadMach) = .ok m1 ∧
      MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 55).map (projByteTB ∘ liftByteTB))) ∧
    -- 2. Multi-variant enum `offset_of!([(1, 1)]) = 8`
    evalNullaryOp [] (.offsetOf [(1, 1)]) npEnumMirTy emptyMemory
      npV1EnumOffsetMir.localDecls npNestedLayouts = .ok (.scalar ⟨8, 8⟩) [] emptyMemory ∧
    npRunTrusted npV1EnumOffsetMir 8 (initMachineState npV1EnumOffsetMir []) = .usizeVal 8 ∧
    Type.layout npEnumMrTy = .ok (.Sized ⟨12⟩ ⟨4⟩) ∧
    npOffsetOfMrPath npEnumMrTy [(1, 1)] = some 8 ∧
    (∃ m1, Interp.steps 1 npV1EnumRuntimeLoadMach = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 77)) ∧
    (∃ m1, Interp.stepsTB 1 (liftMachToTB npV1EnumRuntimeLoadMach) = .ok m1 ∧
      MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 77).map (projByteTB ∘ liftByteTB))) ∧
    -- 3a. OOB `offset_of!` fails closed
    evalNullaryOp [] (.offsetOf [(0, 99)]) npPaddedMirTy emptyMemory
      npV1OobOffsetMir.localDecls npLayouts = .unsupported ∧
    evalNullaryOp [] (.offsetOf [(0, 0)]) npEnumMirTy emptyMemory
      npV1EnumOffsetMir.localDecls npNestedLayouts = .unsupported ∧
    evalNullaryOp [] (.offsetOf [(2, 0)]) npEnumMirTy emptyMemory
      npV1EnumOffsetMir.localDecls npNestedLayouts = .unsupported ∧
    npRunTrusted npV1OobOffsetMir 8 (initMachineState npV1OobOffsetMir []) = .unsupported ∧
    npOffsetOfMrPath npPaddedU8U32MrTy [(0, 99)] = none ∧
    npOffsetOfMrPath npEnumMrTy [(0, 0)] = none ∧
    npOffsetOfMrPath npEnumMrTy [(2, 0)] = none ∧
    -- 3b. Unsized `[u32]`, `str`, `dyn Trait` fail closed in Trusted & reject `()` metadata in MiniRust
    evalNullaryOp [] .sizeOf sliceU32MirTy emptyMemory [] emptyLayoutTable = .unsupported ∧
    evalNullaryOp [] .alignOf strMirTy emptyMemory [] emptyLayoutTable = .unsupported ∧
    evalNullaryOp [] .sizeOf { kind := .dynamic "np::Tr", layoutIdx := 0 } emptyMemory []
      emptyLayoutTable = .unsupported ∧
    (Type.layout (.Slice u32MrTy)).toOption.map LayoutStrategy.is_sized = some false ∧
    (Type.layout (.Slice u8MrTy)).toOption.map LayoutStrategy.is_sized = some false ∧
    (Type.layout (.TraitObject (traitNameOf 0))).toOption.map LayoutStrategy.is_sized = some false ∧
    (evalUnOpM (M := BM) (.ComputeSize (.Slice u32MrTy)) (.Tuple [], unitType) none).toOption.isNone =
      true ∧
    (evalUnOpM (M := BM) (.ComputeSize (.Slice u8MrTy)) (.Tuple [], unitType) none).toOption.isNone =
      true ∧
    (evalUnOpM (M := BM) (.ComputeSize (.TraitObject (traitNameOf 0)))
      (.Tuple [], unitType) none).toOption.isNone = true ∧
    -- 3c. `contractChecks` fails closed
    evalNullaryOp [] .contractChecks boolMirTy emptyMemory [] emptyLayoutTable = .unsupported ∧
    -- 3d. Unresolved ADT layout index fails closed
    evalNullaryOp [] .sizeOf npUnresolvedAdtMirTy emptyMemory
      npV1UnresolvedLayoutMir.localDecls emptyLayoutTable = .unsupported ∧
    evalNullaryOp [] (.offsetOf [(0, 0)]) npUnresolvedAdtMirTy emptyMemory
      npV1UnresolvedLayoutMir.localDecls emptyLayoutTable = .unsupported ∧
    npRunTrusted npV1UnresolvedLayoutMir 8 (initMachineState npV1UnresolvedLayoutMir []) =
      .unsupported :=
  ⟨rfl, by decide +kernel, rfl, rfl,
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   rfl, by decide +kernel, rfl, rfl,
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   rfl, rfl, rfl, by decide +kernel, rfl, rfl, rfl,
   rfl, rfl, rfl,
   by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel,
   rfl,
   rfl, rfl, by decide +kernel⟩

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

/-! ### Wide-slice `MutToConstPointer` (`Mach` & `MachTB`)

`np_v2_mutToConstPointer_all_shapes_and_ub` couples Trusted `evalRvalue` with the
MiniRust `Transmute` lowering on every runtime value shape. The witness below
steps the wide-slice shape (`*mut [u32] -> *const [u32]`) end to end. -/

/-- Trusted fixture: `_2 = _1 as *const [u32]` (`MutToConstPointer` of the wide
`*mut [u32]` local `_1`), then `_0 = PtrMetadata(_2)`. -/
def npMutToConstSliceMir : CapturedMir :=
  mkMirBody "np::w_mut_to_const_slice"
    [mkDecl usizeMirTy, mkDecl rawMutSliceU32MirTy, mkDecl rawConstSliceU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 2)
             (.cast (.pointerCoercion "MutToConstPointer") (.copy (locPlace 1))
               rawConstSliceU32MirTy)),
           mkSt (.assign (locPlace 0) (.unaryOp .ptrMetadata (.copy (locPlace 2))))]
      .return_]

/-- MiniRust machine for `npMutToConstSliceMir`: local `_1` holds the wide
pointer `(data 1024, len 3)` into allocation `3` (the 12-byte array at `1024`);
`MutToConstPointer` is the `Transmute` at the wide slice pointer type into
`_2`, and `PtrMetadata` is `UnOp.GetMetadata`. -/
def npMutToConstSliceMach : Mach :=
  let fn := mkMrFn
    [(localName 0, usizeMrTy), (localName 1, wideSlicePtrMrTy), (localName 2, wideSlicePtrMrTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .Assign (.Local (localName 2))
          (.UnOp (.Cast (.Transmute wideSlicePtrMrTy)) (.Load (.Local (localName 1)))),
        .Assign (.Local (localName 0)) (.UnOp .GetMetadata (.Load (.Local (localName 2))))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 8,
     mkStackAlloc 256 (ptrBytes 1024 (some (⟨3⟩, ())) ++ scalarBytes IntType.usize_ty 3) 8,
     mkStackAlloc 512 (List.replicate 16 .Uninit) 8,
     mkStackAlloc 1024 (scalarBytes u32 10 ++ scalarBytes u32 20 ++ scalarBytes u32 30) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }),
       (localName 2, { addr := 512, provenance := some (⟨2⟩, ()) })]]

/-- **V2 Wide-Slice `MutToConstPointer` Three-Way Witness (Trusted, `Mach`,
`MachTB` with `MachTB.wfLive`)**, completing the three `MutToConstPointer`
shapes (thin, wide slice, wide `dyn Trait`):
1. one Trusted `stepMirFn` step copies the wide pointer `(⟨5, 0⟩, 3)` unchanged
   into `_2`, and the full run reads the length `3` back with `PtrMetadata`;
2. on `Mach`, the `Transmute` writes the same 16 bytes (data pointer with its
   provenance, then the length `3`) into `_2`, and `GetMetadata` returns `3`;
3. on `MachTB` the same run returns `3` and preserves `MachTB.wfLive`. -/
theorem np_v2_mutToConstPointer_wide_slice_three_way_witness :
    (match stepMirFn npMutToConstSliceMir
        (npInitLiveState npMutToConstSliceMir
          [.aggregate 0 [.ptr { allocId := 5, offsetBytes := 0 } 8, .scalar ⟨3, 8⟩]]) with
     | .tau (.running s1) =>
       get? s1.frame.locals 2 =
         some (.init (.aggregate 0 [.ptr { allocId := 5, offsetBytes := 0 } 8, .scalar ⟨3, 8⟩]))
     | _ => False) ∧
    npRunTrusted npMutToConstSliceMir 16
      (npInitLiveState npMutToConstSliceMir
        [.aggregate 0 [.ptr { allocId := 5, offsetBytes := 0 } 8, .scalar ⟨3, 8⟩]]) =
      .usizeVal 3 ∧
    (∃ m2, Interp.steps 2 npMutToConstSliceMach = .ok m2 ∧
      ([2, 0].map (fun i => m2.mem.memory.allocations[i]?.map (·.data))) =
        [some (ptrBytes 1024 (some (⟨3⟩, ())) ++ scalarBytes IntType.usize_ty 3),
         some (scalarBytes IntType.usize_ty 3)]) ∧
    (∃ m2, Interp.stepsTB 2 (liftMachToTB npMutToConstSliceMach) = .ok m2 ∧ MachTB.wfLive m2 ∧
      m2.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes IntType.usize_ty 3).map (projByteTB ∘ liftByteTB))) :=
  ⟨rfl, by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel)⟩

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

/-! ### `V2` universal `dyn Trait` wide-pointer bridge (every `Machine M`)

The witnesses above run one registered vtable on `Mach` and `MachTB`. The
results below hold on EVERY memory model `M` (`BasicMemory`, Tree Borrows, or
any other `Gen.Memory` instance), for every machine `m`, trait `tr`, vtable
`vt`, vtable pointer `vtThin`, and thin data pointer `dataThin`. -/

/-- **V2 Universal `GetMetadata` on a `dyn Trait` Wide Raw Pointer (`Machine M`)**:
whenever the vtable pointer `vtThin` passes `check_ptr` at
`PtrType::VTablePtr(tr)`, `UnOp::GetMetadata` on the wide pointer
`(dataThin, vtThin)` returns exactly `vtThin` at
`Type::Ptr(PtrType::VTablePtr(tr))`, independently of the data pointer. -/
theorem np_v2_dyn_getMetadata_vtable_universal_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (tr : Gen.TraitName)
    (dataThin vtThin : Gen.ThinPointer (Gen.Memory.Provenance M))
    (hChk : checkPtrM (ThinPointer.widen vtThin none) (.VTablePtr tr) (some m) = .ok ()) :
    evalUnOpM (M := M) .GetMetadata
        (.Ptr (ThinPointer.widen dataThin (some (.VTablePointer vtThin))),
         .Ptr (.Raw (.VTablePointer tr))) (some m) =
      .ok (.Ptr (ThinPointer.widen vtThin none), .Ptr (.VTablePtr tr)) := by
  have hChk' : checkValueM (M := M) (.Ptr (ThinPointer.widen vtThin none))
      (.Ptr (.VTablePtr tr)) (some m) = .ok () := by
    rw [checkValueM]; exact hChk
  first
    | (rw [evalUnOpM]
       simp only [ThinPointer.widen, PtrType.meta_kind, PointerMetaKind.encode_as_valueM,
         PointerMetaKind.ty, bind, Except.bind, pure, Except.pure] at hChk' ⊢
       rw [hChk'])
    | (rw [evalUnOpM_getMetadata_eq_sanity _ _ _ (Or.inr ⟨m, rfl⟩)]
       simp only [ThinPointer.widen, PtrType.meta_kind, PointerMetaKind.encode_as_valueM,
         PointerMetaKind.ty, getMetadataSanity, bind, Except.bind, pure, Except.pure] at hChk' ⊢
       rw [hChk'])

/-- **V2 Universal `dyn Trait` Wide-Pointer / Vtable Bridge (`Machine M`)**:
when `m.vtable_ptrs` registers `vtThin` under `vtName` and
`m.prog.vtables[vtName] = vt` is a vtable of trait `tr`, then on every memory
model `M`:
1. `Machine::vtable_from_ptr` and `Machine::vtable_lookup` both resolve
   `vtThin` to `vt`, and `vtThin` passes `check_ptr` at `PtrType::VTablePtr(tr)`;
2. `check_ptr` of the safe wide pointer `(dataThin, vtThin)` at
   `&dyn tr` / `&mut dyn tr` / `Box<dyn tr>` IS `check_ptr` of the thin pointer
   `dataThin` at the sized layout `(vt.size, vt.align)`, so its verdict is
   exactly the address, `isize::MAX`, non-null, `vt.align` alignment,
   `pointee.inhabited`, and `Memory::dereferenceable … dataThin vt.size` checks
   (specialized below by `np_v2_dyn_checkPtrM_traitObject_*`);
3. `UnOp::ComputeSize(TraitObject tr)` and `UnOp::ComputeAlign(TraitObject tr)`
   on `vtThin` return `vt.size.bytes` and `vt.align.bytes`;
4. `UnOp::VTableMethodLookup(meth)` on `vtThin` returns the `Constant::FnPointer`
   value of `vt.methods[meth]`, read from `m.fn_ptrs`. -/
theorem np_v2_dyn_wide_ptr_vtable_ops_universal_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (tr : Gen.TraitName) (vt : Gen.VTable) (vtName : Gen.VTableName)
    (dataThin vtThin vp : Gen.ThinPointer (Gen.Memory.Provenance M))
    (hFind : m.vtable_ptrs.entries.find?
      (fun (_, (vtablePtr : Gen.ThinPointer (Gen.Memory.Provenance M))) =>
        decide (vtablePtr = vtThin)) = some (vtName, vp))
    (hVt : mapIndex m.prog.vtables vtName "self.prog.vtables[vtable_name]" = .ok vt)
    (hTrait : vt.trait_name = tr)
    (hVAddr : inBounds vtThin.addr .Unsigned x86_64.PTR_SIZE = true) :
    vtableFromPtrM m vtThin = .ok vt ∧
    vtableLookupM m vtThin = .ok vt ∧
    checkPtrM (ThinPointer.widen vtThin none) (.VTablePtr tr) (some m) = .ok () ∧
    (∀ (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo),
      ((∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box) →
      pointee.layout = .TraitObject tr →
      checkPtrM (ThinPointer.widen dataThin (some (.VTablePointer vtThin))) (mk pointee) (some m) =
        checkPtrM (ThinPointer.widen dataThin none)
          (mk { pointee with layout := .Sized vt.size vt.align }) (some m)) ∧
    (∀ (opTy : Gen.Type),
      evalUnOpM (.ComputeSize (.TraitObject tr)) (.Ptr (ThinPointer.widen vtThin none), opTy)
          (some m) =
        .ok (.Int (vt.size.bytes : Int), .Int IntType.usize_ty) ∧
      evalUnOpM (.ComputeAlign (.TraitObject tr)) (.Ptr (ThinPointer.widen vtThin none), opTy)
          (some m) =
        .ok (.Int (vt.align.bytes : Int), .Int IntType.usize_ty)) ∧
    (∀ (ty : Gen.PtrType) (meth : Gen.TraitMethodName) (fnName : Gen.FnName),
      mapIndex vt.methods meth "vtable.methods[method]" = .ok fnName →
      evalUnOpM (.VTableMethodLookup meth) (.Ptr (ThinPointer.widen vtThin none), .Ptr ty)
          (some m) =
        (do
          let fnPtr ← evalConstantM m (.FnPointer fnName)
          pure (fnPtr, .Ptr .FnPtr))) := by
  have hFrom : vtableFromPtrM m vtThin = .ok vt :=
    (vtableFromPtrM_eq_mapIndex_of_find m vtThin vtName vp hFind).trans hVt
  have hLookup : vtableLookupM m vtThin = .ok vt :=
    (vtableFromPtrM_ok_iff_vtableLookupM_ok m vtThin vt).mp hFrom
  refine ⟨hFrom, hLookup, checkPtrM_vtablePtr_ok vtThin tr m vt hVAddr hFrom hTrait, ?_, ?_, ?_⟩
  · intro mk pointee hMk hLayout
    exact checkPtrM_traitObject_eq_sized dataThin vtThin mk pointee tr m vt hMk hLayout hVAddr
      hFrom hTrait
  · intro opTy
    constructor
    · first
        | (have h : evalUnOpM (.ComputeSize (.TraitObject tr))
               (.Ptr (ThinPointer.widen vtThin none), opTy) (some m) =
               (computeSizeM m (.TraitObject tr) (some (.VTablePointer vtThin)) >>= fun size =>
                 pure (.Int (size.bytes : Int), .Int IntType.usize_ty)) := rfl
           rw [h]; unfold computeSizeM; rw [compute_size_and_align_traitObject, hLookup]; rfl)
        | simp [evalUnOpM, Type.meta_kind, PointerMetaKind.decode_valueM, ThinPointer.widen,
            Type.layout, computeSizeM, LayoutStrategy.compute_size_and_align, hLookup,
            bind, Except.bind, pure, Except.pure]
    · first
        | (have h : evalUnOpM (.ComputeAlign (.TraitObject tr))
               (.Ptr (ThinPointer.widen vtThin none), opTy) (some m) =
               (computeAlignM m (.TraitObject tr) (some (.VTablePointer vtThin)) >>= fun align =>
                 pure (.Int (align.bytes : Int), .Int IntType.usize_ty)) := rfl
           rw [h]; unfold computeAlignM; rw [compute_size_and_align_traitObject, hLookup]; rfl)
        | simp [evalUnOpM, Type.meta_kind, PointerMetaKind.decode_valueM, ThinPointer.widen,
            Type.layout, computeAlignM, LayoutStrategy.compute_size_and_align, hLookup,
            bind, Except.bind, pure, Except.pure]
  · intro ty meth fnName hfn
    exact evalUnOpM_vtableMethodLookup_eq_fnPointer m vtThin ty meth vt fnName hLookup hfn

/-- **V2 Universal `check_ptr` Acceptance on a `dyn Trait` Safe Wide Pointer
(`Machine M`)**: the polymorphic Episode 1 law specializing conjunct 2 of
`np_v2_dyn_wide_ptr_vtable_ops_universal_M`. The pointer is accepted when the
data pointer is non-null, `vt.align`-aligned, inhabited, and
`Memory::dereferenceable` for `vt.size` bytes. -/
abbrev np_v2_dyn_checkPtrM_traitObject_ok := @checkPtrM_traitObject_ok

/-- **V2 Universal Misaligned `dyn Trait` Safe Wide Pointer UB (`Machine M`)**:
a data pointer that is not `vt.align`-aligned is UB. -/
abbrev np_v2_dyn_checkPtrM_traitObject_unaligned_ub := @checkPtrM_traitObject_unaligned_ub

/-- **V2 Universal Uninhabited `dyn Trait` Safe Wide Pointer UB (`Machine M`)**:
a safe pointer whose pointee is uninhabited is UB. -/
abbrev np_v2_dyn_checkPtrM_traitObject_uninhabited_ub := @checkPtrM_traitObject_uninhabited_ub

/-- **V2 Universal Non-Dereferenceable `dyn Trait` Safe Wide Pointer UB
(`Machine M`)**: a data pointer that `Memory::dereferenceable` rejects for
`vt.size` bytes is UB. -/
abbrev np_v2_dyn_checkPtrM_traitObject_nonDereferenceable_ub :=
  @checkPtrM_traitObject_nonDereferenceable_ub

/-- **V2 ZST `dyn Trait` Safe Wide Pointer (`Mach`)**: with `vt.size = ⟨0⟩` the
pointer passes `check_ptr` at every non-null, `vt.align`-aligned address without
provenance or a live data allocation. `Memory::dereferenceable` of a zero-sized
range is a property of the memory model, so this is stated per model rather
than for an abstract `M`. -/
abbrev np_v2_dyn_checkPtr_traitObject_zst_ok_mach := @checkPtr_traitObject_zst_ok

/-- **V2 ZST `dyn Trait` Safe Wide Pointer (`MachTB`)**: the Tree Borrows
counterpart of `np_v2_dyn_checkPtr_traitObject_zst_ok_mach`. -/
abbrev np_v2_dyn_checkPtrM_traitObject_zst_ok_tb := @checkPtrM_traitObject_zst_tb_ok

/-- **Non-Vacuity of `np_v2_dyn_wide_ptr_vtable_ops_universal_M` (`Mach` &
`MachTB`)**: its four hypotheses hold on BOTH `npDynUnsizeMach` (`M = BM`) AND
`liftMachToTB npDynUnsizeMach` (`M = TBM`, with `MachTB.wfLive`), where the
universal theorem resolves the trait-`0` vtable pointer at `8192` to
`dynDispatchVTable` on both memory models. -/
theorem np_v2_dyn_wide_ptr_vtable_ops_universal_M_nonvacuous :
    let vtBM : Ptr := { addr := 8192, provenance := some (⟨3⟩, ()) }
    let mTB : MachTB := liftMachToTB npDynUnsizeMach
    let vtTB : Gen.ThinPointer (Gen.Memory.Provenance TBM) := liftThinPtrTB vtBM
    vtableFromPtrM npDynUnsizeMach vtBM = .ok dynDispatchVTable ∧
    vtableLookupM npDynUnsizeMach vtBM = .ok dynDispatchVTable ∧
    MachTB.wfLive mTB ∧
    vtableFromPtrM mTB vtTB = .ok dynDispatchVTable ∧
    vtableLookupM mTB vtTB = .ok dynDispatchVTable :=
  have hBM := np_v2_dyn_wide_ptr_vtable_ops_universal_M (M := BM) npDynUnsizeMach (traitNameOf 0)
    dynDispatchVTable ⟨⟨0⟩⟩ ({ addr := 640, provenance := some (⟨4⟩, ()) } : Ptr)
    ({ addr := 8192, provenance := some (⟨3⟩, ()) } : Ptr)
    ({ addr := 8192, provenance := some (⟨3⟩, ()) } : Ptr)
    (by first | rfl | decide +kernel) (by first | rfl | decide +kernel)
    (by first | rfl | decide +kernel) (by first | rfl | decide +kernel)
  have hTB := np_v2_dyn_wide_ptr_vtable_ops_universal_M (M := TBM)
    (liftMachToTB npDynUnsizeMach) (traitNameOf 0)
    dynDispatchVTable ⟨⟨0⟩⟩
    (liftThinPtrTB ({ addr := 640, provenance := some (⟨4⟩, ()) } : Ptr))
    (liftThinPtrTB ({ addr := 8192, provenance := some (⟨3⟩, ()) } : Ptr))
    (liftThinPtrTB ({ addr := 8192, provenance := some (⟨3⟩, ()) } : Ptr))
    (by first | rfl | decide +kernel) (by first | rfl | decide +kernel)
    (by first | rfl | decide +kernel) (by first | rfl | decide +kernel)
  ⟨hBM.1, hBM.2.1, liftMachToTB_wfLive npDynUnsizeMach, hTB.1, hTB.2.1⟩

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

/-- **V3 Trusted Boundary Witnesses for Every `evalFnPtrToPtr` Pointer Check**
(concrete instances of the universal `np_v3_fnPtrToPtr_extra_checks_divergence`,
each differing from the accepted control in exactly one attribute):
1. control: a function pointer at offset `0` with a non-intrinsic source type is
   cast unchanged;
2. (a) a non-zero offset into the function allocation is `.ub`;
3. (b) the same pointer is `.ub` once its tag is a stack borrow in `mem.borrows`;
4. (c) a provenance-free integer (`Value.scalar`), an `AllocId` below
   `fnPtrAllocBase` with no reified table, and an `AllocId` missing from a
   non-empty `mem.fnPtrs` table are each `.ub`;
5. (d) the `rustIntrinsic` ABI check has two independent sources: the operand's
   declared type (`np_v3_fnPtrToPtr_rustIntrinsic_abi_ub`) and the reified
   signature `FnPtrEntry.fnSig`; an entry with the `rustIntrinsic` ABI is `.ub`
   even when the declared source type is a plain `fn(u32) -> u32`, while the
   same entry with the `rust` ABI is accepted.

MiniRust has no counterpart of these checks at the cast: `check_ptr` at
`PtrType::FnPtr` and at a thin raw pointer validates only the address range, and
the `Transmute` lowering is the identity on every pointer
(`np_v3_fnPtrToPtr_extra_checks_divergence`, `c6FnPtrMach true true 4097`), so
MiniRust raises UB for such a pointer only when it is called
(`Machine::fn_from_ptr`). Trusted is strictly stricter here. -/
theorem np_v3_fnPtrToPtr_trusted_boundary_ub_witness :
    let fnPtr : ProvenancePtr := { allocId := fnPtrAllocBase, offsetBytes := 0 }
    let okLocals : List LocalSlot := [.uninit, .init (.ptr fnPtr 8)]
    let srcDecls : List MirAst.LocalDecl := [mkDecl rawConstUnitMirTy, mkDecl npSafeFnPtrMirTy]
    let stackBorrow : BorrowEntry :=
      { tag := 65536, targetLocal := 0, targetProjection := [], perm := .active,
        targetFrameDepth := 0 }
    (match evalFnPtrToPtr okLocals (.copy (locPlace 1)) rawConstUnitMirTy emptyMemory srcDecls
        emptyLayoutTable with
     | .ok v _ _ => v = .ptr fnPtr 8
     | _ => False) ∧
    evalFnPtrToPtr [.uninit, .init (.ptr { allocId := fnPtrAllocBase, offsetBytes := 1 } 8)]
      (.copy (locPlace 1)) rawConstUnitMirTy emptyMemory srcDecls emptyLayoutTable = .ub ∧
    evalFnPtrToPtr okLocals (.copy (locPlace 1)) rawConstUnitMirTy
      { emptyMemory with borrows := [stackBorrow] } srcDecls emptyLayoutTable = .ub ∧
    evalFnPtrToPtr [.uninit, .init (.scalar ⟨4096, 8⟩)] (.copy (locPlace 1)) rawConstUnitMirTy
      emptyMemory srcDecls emptyLayoutTable = .ub ∧
    evalFnPtrToPtr [.uninit, .init (.ptr { allocId := 7, offsetBytes := 0 } 8)]
      (.copy (locPlace 1)) rawConstUnitMirTy emptyMemory srcDecls emptyLayoutTable = .ub ∧
    evalFnPtrToPtr okLocals (.copy (locPlace 1)) rawConstUnitMirTy
      { emptyMemory with fnPtrs :=
          [{ allocId := 65537, defPath := "np::other_fn", typeArgs := .nil,
             fnSig := some (.fnPtr [.uint .u32] (.uint .u32) .safe .rust) }] }
      srcDecls emptyLayoutTable = .ub ∧
    evalFnPtrToPtr okLocals (.copy (locPlace 1)) rawConstUnitMirTy
      { emptyMemory with fnPtrs :=
          [{ allocId := 65536, defPath := "np::intr_fn", typeArgs := .nil,
             fnSig := some (.fnPtr [.uint .u32] (.uint .u32) .safe .rustIntrinsic) }] }
      srcDecls emptyLayoutTable = .ub ∧
    (match evalFnPtrToPtr okLocals (.copy (locPlace 1)) rawConstUnitMirTy
        { emptyMemory with fnPtrs :=
            [{ allocId := 65536, defPath := "np::rust_fn", typeArgs := .nil,
               fnSig := some (.fnPtr [.uint .u32] (.uint .u32) .safe .rust) }] }
        srcDecls emptyLayoutTable with
     | .ok v _ _ => v = .ptr fnPtr 8
     | _ => False) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-! ### Explicit `StorageLive` -> `Assign` -> `StorageDead` Post-Cleanup Lifecycle Fixtures -/

/-- `V1` (`size_of`) post-cleanup MIR fixture with explicit `StorageLive _1` /
`StorageDead _1`, executed from standard `initMachineState` (where non-argument
local `_1` starts `.dead`). -/
def npV1StorageLifecycleMir : CapturedMir :=
  mkMirBody "np::w_v1_storage_lifecycle" [mkDecl usizeMirTy, mkDecl usizeMirTy] 0
    [mkBb [mkSt (.storageLive 1),
           mkSt (.assign (locPlace 1) (.nullaryOp .sizeOf npTuple16MirTy)),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1)))),
           mkSt (.storageDead 1)]
      .return_]

/-- `V1` post-`StorageDead` UB fixture: reads `_1` after `StorageDead _1`. -/
def npV1PostStorageDeadUbMir : CapturedMir :=
  mkMirBody "np::w_v1_post_storage_dead_ub" [mkDecl usizeMirTy, mkDecl usizeMirTy] 0
    [mkBb [mkSt (.storageLive 1),
           mkSt (.assign (locPlace 1) (.nullaryOp .sizeOf npTuple16MirTy)),
           mkSt (.storageDead 1),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1))))]
      .return_]

/-- MiniRust machine for `npV1StorageLifecycleMir`: `localName 1` starts dead
(omitted from `fr.locals`), is allocated by `StorageLive`, receives
`ComputeSize npTuple16MrTy = 16`, is copied into `_0`, and is deallocated by
`StorageDead`. -/
def npV1StorageLifecycleMach : Mach :=
  let fn := mkMrFn [(localName 0, usizeMrTy), (localName 1, usizeMrTy)] [] (localName 0)
    [(bbName 0, ⟨[
        .StorageLive (localName 1),
        .Assign (.Local (localName 1)) (.UnOp (.ComputeSize npTuple16MrTy) (.Tuple [] unitType)),
        .Assign (.Local (localName 0)) (.Load (.Local (localName 1))),
        .StorageDead (localName 1)],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 8]
    [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]]

/-- MiniRust machine for `npV1PostStorageDeadUbMir`: loads `localName 1` after
`StorageDead (localName 1)`. -/
def npV1PostStorageDeadUbMach : Mach :=
  let fn := mkMrFn [(localName 0, usizeMrTy), (localName 1, usizeMrTy)] [] (localName 0)
    [(bbName 0, ⟨[
        .StorageLive (localName 1),
        .Assign (.Local (localName 1)) (.UnOp (.ComputeSize npTuple16MrTy) (.Tuple [] unitType)),
        .StorageDead (localName 1),
        .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 8]
    [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]]

/-- `V4` (`wrapUnsafeBinder` / `unwrapUnsafeBinder`) post-cleanup MIR fixture
with explicit `StorageLive _2` / `StorageDead _2`, executed from standard
`initMachineState` (where `_2` starts `.dead`). -/
def npV4StorageLifecycleMir : CapturedMir :=
  mkMirBody "np::w_v4_storage_lifecycle"
    [mkDecl u32MirTy, mkDecl u32MirTy, mkDecl npBinderU32MirTy] 1
    [mkBb [mkSt (.storageLive 2),
           mkSt (.assign (locPlace 2) (.wrapUnsafeBinder (.copy (locPlace 1)) npBinderU32MirTy)),
           mkSt (.assign (locPlace 2 [.unwrapUnsafeBinder u32MirTy]) (.use (constU32 73))),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 2 [.unwrapUnsafeBinder u32MirTy])))),
           mkSt (.storageDead 2)]
      .return_]
    npLayouts

/-- `V4` post-`StorageDead` UB fixture: reads `_2.unwrapUnsafeBinder` after
`StorageDead _2`. -/
def npV4PostStorageDeadUbMir : CapturedMir :=
  mkMirBody "np::w_v4_post_storage_dead_ub"
    [mkDecl u32MirTy, mkDecl u32MirTy, mkDecl npBinderU32MirTy] 1
    [mkBb [mkSt (.storageLive 2),
           mkSt (.assign (locPlace 2) (.wrapUnsafeBinder (.copy (locPlace 1)) npBinderU32MirTy)),
           mkSt (.assign (locPlace 2 [.unwrapUnsafeBinder u32MirTy]) (.use (constU32 73))),
           mkSt (.storageDead 2),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 2 [.unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npLayouts

/-- MiniRust machine for `npV4StorageLifecycleMir`: `localName 2` starts dead
(omitted from `fr.locals`). -/
def npV4StorageLifecycleMach : Mach :=
  let wrapTy := mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, u32MrTy), (localName 2, wrapTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .StorageLive (localName 2),
        .Assign (.Local (localName 2)) (.Tuple [.Load (.Local (localName 1))] wrapTy),
        .Assign (.Field (.Local (localName 2)) 0) (.Constant (.Int 73) u32MrTy),
        .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 2)) 0)),
        .StorageDead (localName 2)],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (scalarBytes u32 10) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]

/-- MiniRust machine for `npV4PostStorageDeadUbMir`. -/
def npV4PostStorageDeadUbMach : Mach :=
  let wrapTy := mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, u32MrTy), (localName 2, wrapTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .StorageLive (localName 2),
        .Assign (.Local (localName 2)) (.Tuple [.Load (.Local (localName 1))] wrapTy),
        .Assign (.Field (.Local (localName 2)) 0) (.Constant (.Int 73) u32MrTy),
        .StorageDead (localName 2),
        .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 2)) 0))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (scalarBytes u32 10) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]

/-- **Explicit `StorageLive` -> `Assign` -> `StorageDead` Post-Cleanup MIR
Lifecycle Three-Way Witness (Trusted `initMachineState`, `Mach`, and `MachTB`
with `MachTB.wfLive`)**:
starting from standard `initMachineState` (non-argument temporaries begin
`.dead`, never pre-livened via `npInitLiveState`):
1. `V1` (`size_of`): `StorageLive _1 -> _1 = size_of(Tuple16) -> _0 = _1 -> StorageDead _1`
   returns `16` across Trusted, `Mach`, and `MachTB` (preserving `MachTB.wfLive`),
   and reading `_1` after `StorageDead _1` faults UB across all three;
2. `V4` (`wrapUnsafeBinder` / `unwrapUnsafeBinder`): `StorageLive _2 -> wrap -> write 73 -> read 73 -> StorageDead _2`
   returns `73` across Trusted, `Mach`, and `MachTB` (preserving `MachTB.wfLive`),
   and reading `_2.unwrapUnsafeBinder` after `StorageDead _2` faults UB across
   all three. -/
theorem np_storage_lifecycle_three_way_witness :
    -- 1. V1 StorageLive -> nullaryOp -> StorageDead
    npRunTrusted npV1StorageLifecycleMir 16 (initMachineState npV1StorageLifecycleMir []) =
      .usizeVal 16 ∧
    (∃ m4, Interp.steps 4 npV1StorageLifecycleMach = .ok m4 ∧
      (m4.mem.memory.allocations[0]?.map (·.data), m4.mem.memory.allocations[1]?.map (·.live)) =
        (some (scalarBytes IntType.usize_ty 16), some false)) ∧
    (∃ m4, Interp.stepsTB 4 (liftMachToTB npV1StorageLifecycleMach) = .ok m4 ∧ MachTB.wfLive m4 ∧
      (m4.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB),
       m4.mem.memory.mem.allocations[1]?.map (·.live)) =
        (some ((scalarBytes IntType.usize_ty 16).map (projByteTB ∘ liftByteTB)), some false)) ∧
    npRunTrusted npV1PostStorageDeadUbMir 16 (initMachineState npV1PostStorageDeadUbMir []) = .ub ∧
    Interp.steps 4 npV1PostStorageDeadUbMach = .error (.ub "access to a dead local") ∧
    Interp.stepsTB 4 (liftMachToTB npV1PostStorageDeadUbMach) =
      .error (.ub "access to a dead local") ∧
    -- 2. V4 StorageLive -> wrap/unwrap -> StorageDead
    npRunTrusted npV4StorageLifecycleMir 16
      (initMachineState npV4StorageLifecycleMir [.scalar ⟨10, 4⟩]) = .u32Val 73 ∧
    (∃ m5, Interp.steps 5 npV4StorageLifecycleMach = .ok m5 ∧
      (m5.mem.memory.allocations[0]?.map (·.data), m5.mem.memory.allocations[2]?.map (·.live)) =
        (some (scalarBytes u32 73), some false)) ∧
    (∃ m5, Interp.stepsTB 5 (liftMachToTB npV4StorageLifecycleMach) = .ok m5 ∧ MachTB.wfLive m5 ∧
      (m5.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB),
       m5.mem.memory.mem.allocations[2]?.map (·.live)) =
        (some ((scalarBytes u32 73).map (projByteTB ∘ liftByteTB)), some false)) ∧
    npRunTrusted npV4PostStorageDeadUbMir 16
      (initMachineState npV4PostStorageDeadUbMir [.scalar ⟨10, 4⟩]) = .ub ∧
    Interp.steps 5 npV4PostStorageDeadUbMach = .error (.ub "access to a dead local") ∧
    Interp.stepsTB 5 (liftMachToTB npV4PostStorageDeadUbMach) =
      .error (.ub "access to a dead local") :=
  ⟨by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   by decide +kernel,
   eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel),
   by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   by decide +kernel,
   eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-! ### Nested projection `(_1.1).unwrapUnsafeBinder` (`Mach` & `MachTB`) -/

/-- Trusted fixture writing `99` to, then reading, the nested place
`(_1.1).unwrapUnsafeBinder` (`Field` then `UnwrapUnsafeBinder`) of the 8-byte
`np::PaddedU8U32` (`u8` at offset `0`, `u32` at offset `4`). -/
def npV4NestedFieldUnwrapMir : CapturedMir :=
  mkMirBody "np::w_v4_nested_field_unwrap"
    [mkDecl u32MirTy, mkDecl npPaddedMirTy] 1
    [mkBb [mkSt (.assign (locPlace 1 [.field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy])
             (.use (constU32 99))),
           mkSt (.assign (locPlace 0)
             (.use (.copy (locPlace 1 [.field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npLayouts

/-- MiniRust machine for `npV4NestedFieldUnwrapMir`: the binder projection is
transparent, so the nested place is the field place `_1.1` of
`npPaddedU8U32MrTy` at byte offset `4`. Allocation `1` is `_1`, holding the
`u8` `7`, three padding bytes, and the `u32` `11`. -/
def npV4NestedFieldUnwrapMach : Mach :=
  let fn := mkMrFn [(localName 0, u32MrTy), (localName 1, npPaddedU8U32MrTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .Assign (.Field (.Local (localName 1)) 1) (.Constant (.Int 99) u32MrTy),
        .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 1))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256
       (([.Init 7 none, .Uninit, .Uninit, .Uninit] : List Byte) ++ scalarBytes u32 11) 4]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]

/-- **V4 Nested `(_1.1).unwrapUnsafeBinder` on Trusted**: the write through
`Field` then `UnwrapUnsafeBinder` replaces only field `1`, and the read through
the same nested place returns `99`. -/
theorem np_v4_nested_field_unwrap_trusted_witness :
    npRunTrusted npV4NestedFieldUnwrapMir 16
      (npInitLiveState npV4NestedFieldUnwrapMir
        [.aggregate 0 [.scalar ⟨7, 1⟩, .scalar ⟨11, 4⟩]]) = .u32Val 99 := by
  decide +kernel

/-- **V4 Nested `(_1.1).unwrapUnsafeBinder` on `Mach` & `MachTB` (with
`MachTB.wfLive`)**: the store at byte offset `4` writes exactly bytes `[4, 8)`
of `_1` (the `u8` field and the padding bytes `[0, 4)` are unchanged), and the
load returns `99`. -/
theorem np_v4_nested_field_unwrap_mach_and_tb_witness :
    (∃ m2, Interp.steps 2 npV4NestedFieldUnwrapMach = .ok m2 ∧
      ([1, 0].map (fun i => m2.mem.memory.allocations[i]?.map (·.data))) =
        [some (([.Init 7 none, .Uninit, .Uninit, .Uninit] : List Byte) ++ scalarBytes u32 99),
         some (scalarBytes u32 99)]) ∧
    (∃ m2, Interp.stepsTB 2 (liftMachToTB npV4NestedFieldUnwrapMach) = .ok m2 ∧
      MachTB.wfLive m2 ∧
      m2.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 99).map (projByteTB ∘ liftByteTB))) :=
  ⟨ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel)⟩

/-! ### Sub-Range Tree Borrows Disjointness on `{ fst: u32, snd: BinderU32 }` & `(*ptr).field.unwrapUnsafeBinder` -/

/-- 8-byte layout for `np::PairU32Binder { fst: u32, snd: BinderU32 }`:
`fst` at `[0, 4)`, `snd` at `[4, 8)` (shared verbatim with `NullaryAndPtrCoercionLM`). -/
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

/-- MiniRust `{ fst: u32, snd: BinderU32 }` tuple type (size 8, align 4). -/
@[reducible] def npPairU32BinderMrTy : Gen.Type :=
  .Tuple [(⟨0⟩, u32MrTy), (⟨4⟩, mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩)] ⟨⟨8⟩, ⟨4⟩, none⟩ none

def npV4PairLocalSndUnwrapMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_local_snd_unwrap"
    [mkDecl u32MirTy, mkDecl npPairU32BinderMirTy] 1
    [mkBb [mkSt (.assign (locPlace 1 [.field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy])
             (.use (constU32 99))),
           mkSt (.assign (locPlace 0)
             (.use (.copy (locPlace 1 [.field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npSubrangeLayouts

def npV4PairLocalFstMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_local_fst"
    [mkDecl u32MirTy, mkDecl npPairU32BinderMirTy] 1
    [mkBb [mkSt (.assign (locPlace 1 [.field 0 u32MirTy, .unwrapUnsafeBinder u32MirTy])
             (.use (constU32 99))),
           mkSt (.assign (locPlace 0)
             (.use (.copy (locPlace 1 [.field 0 u32MirTy, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npSubrangeLayouts

def npV4PairDerefSndUnwrapMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_deref_snd_unwrap"
    [mkDecl u32MirTy, mkDecl npRawMutPairU32BinderMirTy, mkDecl npPairU32BinderMirTy] 1
    [mkBb [mkSt (.assign (locPlace 1 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy])
             (.use (constU32 99))),
           mkSt (.assign (locPlace 0)
             (.use (.copy (locPlace 1 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npSubrangeLayouts

def npV4PairDerefFstMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_deref_fst"
    [mkDecl u32MirTy, mkDecl npRawMutPairU32BinderMirTy, mkDecl npPairU32BinderMirTy] 1
    [mkBb [mkSt (.assign (locPlace 1 [.deref, .field 0 u32MirTy]) (.use (constU32 99))),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.deref, .field 0 u32MirTy]))))]
      .return_]
    npSubrangeLayouts

/-- Trusted initial state for local pair fixtures: `_1` holds `{ fst: 7, snd: 11 }`
and borrow tag `1` protects ONLY `_1.0` (`[0, 4)`) when `protectedMode = true`. -/
def npPairLocalTrustedInit (body : CapturedMir) (protectedMode : Bool) : MachineState :=
  let base := initMachineState body [.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨11, 4⟩]]
  let bProt : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetProjection := [.field 0 u32MirTy], perm := .unique,
      rangeOffset := 0, rangeLen := 4,
      protector := if protectedMode then some 1 else none,
      parentTag := none, targetFrameDepth := 0, allocDead := false }
  { base with
    memory := { base.memory with
      borrows := [bProt],
      activeProtectors := if protectedMode then [1] else [] } }

/-- Trusted initial state for deref pair fixtures: `_1` holds `*mut PairU32Binder`
with tag `1` targeting `_2 = { fst: 7, snd: 11 }`, and child borrow tag `2`
protects ONLY `_2.0` (`[0, 4)`) when `protectedMode = true`. -/
def npPairDerefTrustedInit (body : CapturedMir) (protectedMode : Bool) : MachineState :=
  let bPtr : BorrowEntry :=
    { tag := 1, targetLocal := 2, targetProjection := [], perm := .unique,
      rangeOffset := 0, rangeLen := 0, protector := none, parentTag := none,
      targetFrameDepth := 0, allocDead := false }
  let bProt : BorrowEntry :=
    { tag := 2, targetLocal := 2, targetProjection := [.field 0 u32MirTy], perm := .unique,
      rangeOffset := 0, rangeLen := 4,
      protector := if protectedMode then some 1 else none,
      parentTag := some 1, targetFrameDepth := 0, allocDead := false }
  { frame := { blockIdx := 0, stmtIdx := 0,
               locals := [.uninit, .init (.ptr ⟨1, 0⟩ 8),
                          .init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨11, 4⟩])] },
    memory := { (initMachineState body []).memory with
      borrows := [bPtr, bProt],
      activeProtectors := if protectedMode then [1] else [] } }

/-- MiniRust machine for `(_1.1).unwrapUnsafeBinder = 99` (`[4, 8)`) while `_2 : &u32`
holds a function-entry protector (`Validate _2 true`) covering ONLY `_1.0` (`[0, 4)`). -/
def npV4PairLocalSndDisjointMach : Mach :=
  let fn := mkMrFn
    [(localName 0, u32MrTy), (localName 1, npPairU32BinderMrTy), (localName 2, refTy .not u32)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .Validate (.Local (localName 2)) true,
        .Assign (.Field (.Field (.Local (localName 1)) 1) 0) (.Constant (.Int 99) u32MrTy),
        .Assign (.Local (localName 0)) (.Load (.Field (.Field (.Local (localName 1)) 1) 0))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (scalarBytes u32 7 ++ scalarBytes u32 11) 4,
     mkStackAlloc 384 (ptrBytes 256 (some (⟨1⟩, ()))) 8]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }),
       (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })]]

/-- MiniRust machine for `(*_3).1.unwrapUnsafeBinder = 99` (`[4, 8)` through
raw pointer `_3`) while `_2 : &u32` holds a function-entry protector covering
ONLY `[0, 4)` of allocation `1`. -/
def npV4PairDerefSndDisjointMach : Mach :=
  let fn := mkMrFn
    [(localName 0, u32MrTy), (localName 1, npPairU32BinderMrTy),
     (localName 2, refTy .not u32), (localName 3, thinRawPtrTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .Validate (.Local (localName 2)) true,
        .Assign (.Field (.Field (.Deref (.Load (.Local (localName 3))) npPairU32BinderMrTy) 1) 0)
          (.Constant (.Int 99) u32MrTy),
        .Assign (.Local (localName 0))
          (.Load (.Field (.Field (.Deref (.Load (.Local (localName 3))) npPairU32BinderMrTy) 1) 0))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (scalarBytes u32 7 ++ scalarBytes u32 11) 4,
     mkStackAlloc 384 (ptrBytes 256 (some (⟨1⟩, ()))) 8,
     mkStackAlloc 512 (ptrBytes 256 (some (⟨1⟩, ()))) 8]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }),
       (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) }),
       (localName 3, { addr := 512, provenance := some (⟨3⟩, ()) })]]

/-- MiniRust machine writing the protected field `_1.0 = 99` (`[0, 4)`):
returns `99` on `Mach` (`BasicMemory`), faults UB on `MachTB` (`TreeBorrowsMemory`). -/
def npV4PairLocalFstConflictMach : Mach :=
  let fn := mkMrFn
    [(localName 0, u32MrTy), (localName 1, npPairU32BinderMrTy), (localName 2, refTy .not u32)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .Validate (.Local (localName 2)) true,
        .Assign (.Field (.Local (localName 1)) 0) (.Constant (.Int 99) u32MrTy),
        .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 0))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (scalarBytes u32 7 ++ scalarBytes u32 11) 4,
     mkStackAlloc 384 (ptrBytes 256 (some (⟨1⟩, ()))) 8]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }),
       (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })]]

/-- MiniRust machine writing the protected field through raw pointer `(*_3).0 = 99`
(`[0, 4)`): returns `99` on `Mach`, faults UB on `MachTB`. -/
def npV4PairDerefFstConflictMach : Mach :=
  let fn := mkMrFn
    [(localName 0, u32MrTy), (localName 1, npPairU32BinderMrTy),
     (localName 2, refTy .not u32), (localName 3, thinRawPtrTy)]
    [localName 1] (localName 0)
    [(bbName 0, ⟨[
        .Validate (.Local (localName 2)) true,
        .Assign (.Field (.Deref (.Load (.Local (localName 3))) npPairU32BinderMrTy) 0)
          (.Constant (.Int 99) u32MrTy),
        .Assign (.Local (localName 0))
          (.Load (.Field (.Deref (.Load (.Local (localName 3))) npPairU32BinderMrTy) 0))],
      .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4,
     mkStackAlloc 256 (scalarBytes u32 7 ++ scalarBytes u32 11) 4,
     mkStackAlloc 384 (ptrBytes 256 (some (⟨1⟩, ()))) 8,
     mkStackAlloc 512 (ptrBytes 256 (some (⟨1⟩, ()))) 8]
    [mkRootFrame fn
      [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }),
       (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) }),
       (localName 3, { addr := 512, provenance := some (⟨3⟩, ()) })]]

/-- Execute the two body statements (`write` + `read into _0`) via `stepMirFn`
before frame-teardown `return_` (isolating statement-level sub-range protector
checks from `DIV-MR-TB-FNENTRY-LOCAL-DEALLOC` on same-frame borrows). -/
def npRunTrustedTwoStmtsLoc0 (body : CapturedMir) (s : MachineState) : NullaryPtrTrustedObs :=
  match stepMirFn body s with
  | .tau (.running s1) =>
    match stepMirFn body s1 with
    | .tau (.running s2) =>
      match get? s2.frame.locals 0 with
      | some (.init v) => npTrustedValueObs v
      | _ => .stuck
    | .vis (.inl (.fail .ub)) _ => .ub
    | .vis (.inl (.fail .unsupported)) _ => .unsupported
    | _ => .stuck
  | .vis (.inl (.fail .ub)) _ => .ub
  | .vis (.inl (.fail .unsupported)) _ => .unsupported
  | _ => .stuck

/-- **`V4` Sub-Range Tree Borrows Disjointness on `{ fst: u32, snd: BinderU32 }`
Across Trusted, `Mach`, and `MachTB` (with `MachTB.wfLive`)** for BOTH local
(`(_1.1).unwrapUnsafeBinder`, `_1.0`) AND dereferenced
(`(*ptr).1.unwrapUnsafeBinder`, `(*ptr).0`) places (completing 3-authority parity
with `lm_np_v4_pair_subrange_disjoint_and_deref_field_tb_witness`):
with a function-entry protector covering ONLY `[0, 4)` (`fst`):
1. `(_1.1).unwrapUnsafeBinder = 99` (`[4, 8)`) succeeds (`99`, preserving `[0, 4) = 7`)
   on protected Trusted, `Mach`, AND `MachTB` (preserving `MachTB.wfLive`);
2. `(*ptr).1.unwrapUnsafeBinder = 99` (`[4, 8)`) likewise succeeds (`99`, preserving
   `[0, 4) = 7`) on protected Trusted, `Mach`, AND `MachTB` (preserving `MachTB.wfLive`);
3. conflicting writes to the protected `[0, 4)` field via `_1.0 = 99` OR
   `(*ptr).0 = 99` return `99` on unprotected Trusted & `Mach` (`BasicMemory`),
   and fault `.ub` on protected Trusted & `MachTB` (`TreeBorrowsMemory`). -/
theorem np_v4_pair_subrange_disjoint_and_deref_field_three_way_witness :
    -- 1. Disjoint local `(_1.1).unwrapUnsafeBinder` at `[4, 8)` with protected `[0, 4)`
    npRunTrustedTwoStmtsLoc0 npV4PairLocalSndUnwrapMir
      (npPairLocalTrustedInit npV4PairLocalSndUnwrapMir true) = .u32Val 99 ∧
    (∃ m3, Interp.steps 3 npV4PairLocalSndDisjointMach = .ok m3 ∧
      ([0, 1].map (fun i => m3.mem.memory.allocations[i]?.map (·.data))) =
        [some (scalarBytes u32 99 : List Byte),
         some ((scalarBytes u32 7 ++ scalarBytes u32 99) : List Byte)]) ∧
    (∃ m3, Interp.stepsTB 3 (liftMachToTB npV4PairLocalSndDisjointMach) = .ok m3 ∧
      MachTB.wfLive m3 ∧
      ([0, 1].map (fun i => m3.mem.memory.mem.allocations[i]?.map (fun a => a.data.map projByteTB))) =
        [some ((scalarBytes u32 99).map (projByteTB ∘ liftByteTB)),
         some ((scalarBytes u32 7 ++ scalarBytes u32 99).map (projByteTB ∘ liftByteTB))]) ∧
    -- 2. Disjoint deref `(*ptr).1.unwrapUnsafeBinder` at `[4, 8)` with protected `[0, 4)`
    npRunTrustedTwoStmtsLoc0 npV4PairDerefSndUnwrapMir
      (npPairDerefTrustedInit npV4PairDerefSndUnwrapMir true) = .u32Val 99 ∧
    (∃ m3, Interp.steps 3 npV4PairDerefSndDisjointMach = .ok m3 ∧
      ([0, 1].map (fun i => m3.mem.memory.allocations[i]?.map (·.data))) =
        [some (scalarBytes u32 99 : List Byte),
         some ((scalarBytes u32 7 ++ scalarBytes u32 99) : List Byte)]) ∧
    (∃ m3, Interp.stepsTB 3 (liftMachToTB npV4PairDerefSndDisjointMach) = .ok m3 ∧
      MachTB.wfLive m3 ∧
      ([0, 1].map (fun i => m3.mem.memory.mem.allocations[i]?.map (fun a => a.data.map projByteTB))) =
        [some ((scalarBytes u32 99).map (projByteTB ∘ liftByteTB)),
         some ((scalarBytes u32 7 ++ scalarBytes u32 99).map (projByteTB ∘ liftByteTB))]) ∧
    -- 3. Conflicting local `_1.0` at protected `[0, 4)`
    npRunTrusted npV4PairLocalFstMir 16
      (npPairLocalTrustedInit npV4PairLocalFstMir false) = .u32Val 99 ∧
    npRunTrustedTwoStmtsLoc0 npV4PairLocalFstMir
      (npPairLocalTrustedInit npV4PairLocalFstMir true) = .ub ∧
    (∃ m3, Interp.steps 3 npV4PairLocalFstConflictMach = .ok m3 ∧
      m3.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 99)) ∧
    (interpUbMsg (Interp.stepsTB 3 (liftMachToTB npV4PairLocalFstConflictMach))).isSome = true ∧
    -- 4. Conflicting deref `(*ptr).0` at protected `[0, 4)`
    npRunTrusted npV4PairDerefFstMir 16
      (npPairDerefTrustedInit npV4PairDerefFstMir false) = .u32Val 99 ∧
    npRunTrustedTwoStmtsLoc0 npV4PairDerefFstMir
      (npPairDerefTrustedInit npV4PairDerefFstMir true) = .ub ∧
    (∃ m3, Interp.steps 3 npV4PairDerefFstConflictMach = .ok m3 ∧
      m3.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 99)) ∧
    (interpUbMsg (Interp.stepsTB 3 (liftMachToTB npV4PairDerefFstConflictMach))).isSome = true :=
  ⟨by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   by decide +kernel,
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   by decide +kernel, by decide +kernel,
   ok_of_map_toOption (by decide +kernel), by decide +kernel,
   by decide +kernel, by decide +kernel,
   ok_of_map_toOption (by decide +kernel), by decide +kernel⟩

/-! ### `(*ptr).field` through `Frozen` / `Disabled` / `Cell` tags, and a caller-frame pointee -/

/-- Trusted fixture reading the nested place: `_0 = (*_1).1.unwrapUnsafeBinder`. -/
def npV4PairDerefSndReadMir : CapturedMir :=
  mkMirBody "np::w_v4_pair_deref_snd_read"
    [mkDecl u32MirTy, mkDecl npRawMutPairU32BinderMirTy, mkDecl npPairU32BinderMirTy] 1
    [mkBb [mkSt (.assign (locPlace 0)
             (.use (.copy (locPlace 1 [.deref, .field 1 u32MirTy, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]
    npSubrangeLayouts

/-- `npPairDerefTrustedInit` with the permission of the pointer's own borrow
(tag `1`) and of the child borrow on `_2.0` (tag `2`, `[0, 4)`) as parameters;
`npPairDerefTrustedInitPerms body .unique .unique p` is `npPairDerefTrustedInit body p`. -/
def npPairDerefTrustedInitPerms (body : CapturedMir) (ptrPerm childPerm : TreeBorrowPerm)
    (protectedMode : Bool) : MachineState :=
  let bPtr : BorrowEntry :=
    { tag := 1, targetLocal := 2, targetProjection := [], perm := ptrPerm,
      rangeOffset := 0, rangeLen := 0, protector := none, parentTag := none,
      targetFrameDepth := 0, allocDead := false }
  let bProt : BorrowEntry :=
    { tag := 2, targetLocal := 2, targetProjection := [.field 0 u32MirTy], perm := childPerm,
      rangeOffset := 0, rangeLen := 4,
      protector := if protectedMode then some 1 else none,
      parentTag := some 1, targetFrameDepth := 0, allocDead := false }
  { frame := { blockIdx := 0, stmtIdx := 0,
               locals := [.uninit, .init (.ptr ⟨1, 0⟩ 8),
                          .init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨11, 4⟩])] },
    memory := { (initMachineState body []).memory with
      borrows := [bPtr, bProt],
      activeProtectors := if protectedMode then [1] else [] } }

/-- **V4 `(*ptr).field` Under `Frozen` / `Disabled` / `Cell` Borrows on Trusted**:
1. pointer borrow `.frozen`: the write `(*ptr).0 = 99` is `.ub`, the read
   `(*ptr).1.unwrapUnsafeBinder` returns `11`;
2. pointer borrow `.disabled`: the read and the write are both `.ub`;
3. protected child borrow on `[0, 4)`: the foreign write `(*ptr).0 = 99` through
   the parent pointer is accepted (`99`) when the child is `.cell` (interior
   mutability), and `.ub` when the child is `.unique`. -/
theorem np_v4_deref_field_frozen_disabled_cell_trusted_witness :
    npRunTrustedTwoStmtsLoc0 npV4PairDerefFstMir
      (npPairDerefTrustedInitPerms npV4PairDerefFstMir .frozen .unique false) = .ub ∧
    npRunTrusted npV4PairDerefSndReadMir 16
      (npPairDerefTrustedInitPerms npV4PairDerefSndReadMir .frozen .unique false) = .u32Val 11 ∧
    npRunTrusted npV4PairDerefSndReadMir 16
      (npPairDerefTrustedInitPerms npV4PairDerefSndReadMir .disabled .unique false) = .ub ∧
    npRunTrustedTwoStmtsLoc0 npV4PairDerefFstMir
      (npPairDerefTrustedInitPerms npV4PairDerefFstMir .disabled .unique false) = .ub ∧
    npRunTrustedTwoStmtsLoc0 npV4PairDerefFstMir
      (npPairDerefTrustedInitPerms npV4PairDerefFstMir .unique .cell true) = .u32Val 99 ∧
    npRunTrustedTwoStmtsLoc0 npV4PairDerefFstMir
      (npPairDerefTrustedInitPerms npV4PairDerefFstMir .unique .unique true) = .ub :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel⟩

/-- **MiniRust Tree Borrows Ground Truth for `Frozen` / `Disabled` (Episode 1)**:
on `TreeBorrowsMemory`, a local write through a `Frozen` tag and a local read
through a `Disabled` tag are UB. This is a memory-model statement; it is not
stepped through an `unwrapUnsafeBinder` place. -/
abbrev np_tb_frozen_write_and_disabled_read_ub_minirust :=
  @MiniRustSpec.Correspondence.RefWitness.treeBorrowsFrozenAndDisabledUb

/-- **Protected `UnsafeCell` Interior Mutability, Three-Way (Episode 1)**: under
a function-entry protector on `&UnsafeCell<u32>`, an interior write through a
raw pointer returns `77` on Trusted (with `MirNoUBTree`), `Mach`, and `MachTB`.
The fixture writes through a raw pointer to the cell's field, not through an
`unwrapUnsafeBinder` place. -/
abbrev np_tb_protected_unsafeCell_interior_mut_three_way :=
  @MiniRustSpec.Correspondence.TbWitness.unsafeCellProtectedInteriorMut_simulation

/-- Caller body for the caller-frame pointee fixture: `_1` is the pointee
`np::PairU32Binder`, `_0` receives the callee's return value, and block `1`
(the call's return target) returns `_0`. Block `0` stands for the call site,
which has already executed when the callee state starts. -/
def npPairCallerMir : CapturedMir :=
  mkMirBody "np::w_pair_caller" [mkDecl u32MirTy, mkDecl npPairU32BinderMirTy] 0
    [mkBb [] .return_, mkBb [] .return_]
    npSubrangeLayouts

/-- Trusted callee state at frame depth `1` whose pointee lives in the suspended
caller frame (depth `0`, caller local `_1 = { fst: 7, snd: 11 }`): the callee's
`_1` holds a pointer with tag `1` to the caller's `_1`, and child borrow tag `2`
protects only the caller's `_1.0` (`[0, 4)`) when `protectedMode = true`. Both
borrows record `targetFrameDepth := 0`. -/
def npPairDerefCallerFrameTrustedInit (body : CapturedMir) (protectedMode : Bool) :
    MachineState :=
  let callerSaved : SavedCallerFrame :=
    { callerBody := npPairCallerMir,
      frame := { blockIdx := 0, stmtIdx := 0,
                 locals := [.uninit, .init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨11, 4⟩])] },
      destination := locPlace 0, returnTarget := 1 }
  let bPtr : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique,
      rangeOffset := 0, rangeLen := 0, protector := none, parentTag := none,
      targetFrameDepth := 0, allocDead := false }
  let bProt : BorrowEntry :=
    { tag := 2, targetLocal := 1, targetProjection := [.field 0 u32MirTy], perm := .unique,
      rangeOffset := 0, rangeLen := 4,
      protector := if protectedMode then some 1 else none,
      parentTag := some 1, targetFrameDepth := 0, allocDead := false }
  { frame := { blockIdx := 0, stmtIdx := 0,
               locals := [.uninit, .init (.ptr ⟨1, 0⟩ 8), .uninit] },
    memory := { (initMachineState body []).memory with
      callStack := [callerSaved],
      borrows := [bPtr, bProt],
      activeProtectors := if protectedMode then [1] else [] } }

/-- **V4 Caller-Frame Pointee: Full Run Through `TerminatorKind.return_`**. With
the pointee in the suspended caller frame (`targetFrameDepth = 0`, active depth
`1`), the callee's `return_` deallocates only depth-`1` locals, so the protected
`[0, 4)` borrow does not block it; control returns to the caller, which returns
the value:
1. `(*ptr).1.unwrapUnsafeBinder = 99` (disjoint `[4, 8)`) runs to `99`, with and
   without the protector;
2. `(*ptr).0 = 99` (the protected `[0, 4)`) is `.ub` with the protector and
   runs to `99` without it;
3. contrast (`DIV-MR-TB-FNENTRY-LOCAL-DEALLOC`): with the pointee in the
   returning frame itself (`npPairDerefTrustedInit`), the same disjoint write
   succeeds but the full run is `.ub` at `return_`, which is why
   `np_v4_pair_subrange_disjoint_and_deref_field_three_way_witness` observes the
   two statements only. -/
theorem np_v4_pair_deref_caller_frame_full_return_witness :
    npRunTrusted npV4PairDerefSndUnwrapMir 16
      (npPairDerefCallerFrameTrustedInit npV4PairDerefSndUnwrapMir true) = .u32Val 99 ∧
    npRunTrusted npV4PairDerefSndUnwrapMir 16
      (npPairDerefCallerFrameTrustedInit npV4PairDerefSndUnwrapMir false) = .u32Val 99 ∧
    npRunTrusted npV4PairDerefFstMir 16
      (npPairDerefCallerFrameTrustedInit npV4PairDerefFstMir true) = .ub ∧
    npRunTrusted npV4PairDerefFstMir 16
      (npPairDerefCallerFrameTrustedInit npV4PairDerefFstMir false) = .u32Val 99 ∧
    npRunTrusted npV4PairDerefSndUnwrapMir 16
      (npPairDerefTrustedInit npV4PairDerefSndUnwrapMir true) = .ub :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
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
