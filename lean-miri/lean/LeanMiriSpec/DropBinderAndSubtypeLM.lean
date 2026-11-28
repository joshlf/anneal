/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import LeanMiriSpec.UnwindSetDiscrAndFnPtrLM

/-!
# Episode 2 Dual-Authority Correspondence (`LeanMiriSpec` Authority):
# Drop, Unsafe Binders, ShallowInitBox, Subtype, RawPtr, Closures, Coverage & Drop Hints

Two-sided step simulations (`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`
vs. unmodified vendored `Miri.Interpreter.Step.step`), conservative hook
extension (`step_ep2_overlay_eq_unwind_of_free`), concrete positive / UB /
boundary / mode-sensitivity witnesses, and executable authority-typed
`ep2LmObserve` for all 8 already-trusted MIR variants:

1. **`V1` (`StatementKind.coverage`)** — native `Miri.Interpreter.Step.evalStatement`
   `.Coverage` no-op, lockstep PC advance, and UB-after-coverage equivalence.
2. **`V2` (`StatementKind.backwardIncompatibleDropHint`)** — native
   `.BackwardIncompatibleDropHint` no-op (never faulting even on dead/uninit/OOB
   places) and subsequent dead-place read UB contrast.
3. **`V3` (`TerminatorKind.drop`)** — whole-local drop, dead-local UB,
   memory-backed whole-local and projected sub-place drop (layout-derived byte
   ranges, allocation-relative offsets) via vendored
   `Miri.Memory.Allocation.writeUninit` preserving sibling bytes, data-driven
   Tree Borrows mode sensitivity (when `treeBorrows = true`, the drop is applied as
   a write access to the dropped byte range of the allocation's own vendored borrow
   tree via `ep2ApplyTreeBorrowsWrite` — per-node vendored
   `Tree.LocationState.performAccess` with exact ancestry and the vendored global
   protected-tag table — and the transitioned tree is persisted via
   `Allocation.setExtra`; bridged to vendored `BorrowTree.performBorrowAccessRange`
   by `ep2ProtectorConflict_agrees_with_vendored_tree_borrows`),
   cleanup-block unwind/post-drop
   transitions, and explicit witnessed characterization of post-elaboration
   no-glue drop deinit vs. canonical runtime-nop (`canonNoGlueDropHooks`).
4. **`V4` (`Rvalue.shallowInitBox`)** — honest base-translation boundary
   (`translateRvalue (.shallowInitBox ..) = .Use untranslatableConstOperand .No`
   -> `StepError.unsupported`), plus lowered `.Cast .Transmute` stepping
   through unmodified vendored `Miri.Interpreter.Step.step` -> `Cast.cast`
   preserving provenance without touching uninitialized pointee memory,
   dead/uninit operand UB equivalence, and Trusted `.unsupported` boundaries.
5. **`V5` (`Rvalue.wrapUnsafeBinder`)** — unmodified vendored
   `Miri.Interpreter.evalRvalueIntoPlace` `.WrapUnsafeBinder` routing through
   `annealCopyAllowTransmuteOverlay` for both transparent targets (`bool`,
   `u32`) and single-field `binderStructLayout?` wrapper structs (`BinderU32`,
   `BinderNonZeroU8`), scalar validity-range UB, identity, unknown-operand
   `.unsupported`, and full round-trip with `ProjectionElem.unwrapUnsafeBinder`.
6. **`V6` (`CastKind.subtype`)** — exact definitional equivalence
   `CastKind.Subtype = CastKind.Transmute` in BOTH Trusted and vendored
   `Miri.Interpreter.Cast.cast`, scalars, pointers, validity-range UB, dead/uninit
   UB, and size-mismatch `.unsupported`.
7. **`V7` (`AggregateKind.rawPtr`)** — unmodified vendored
   `Miri.Interpreter.writeAggregate` `.RawPtr` arm handling BOTH thin `()`
   metadata (`MemPlaceMeta.none` -> `.scalar`) and wide `[u32]`/`str` `usize`
   metadata (`MemPlaceMeta.metadata` -> `.scalarPair`), plus `UnaryOp.PtrMetadata`
   round-trip and dead/uninit operand UB for both data and metadata operands.
8. **`V8` (`AggregateKind.closure`)** — 0-capture ZST and 2-capture
   `(u32, *const u32)` closures with left-to-right operand evaluation and
   dead/uninit upvar UB propagation.

Strict import isolation: this module NEVER imports `MiniRustSpec.*` (verified
by the trailing `#assert_drop_binder_subtype_lm_audit` command).
-/

namespace LeanMiriSpec.DropBinderAndSubtypeLM

set_option Elab.async false
set_option linter.unusedSimpArgs false

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence
open LeanMiriSpec.UnwindSetDiscrAndFnPtrLM

/-! ## §0. Exact Fixture Parity Helpers (Locked by Cross-Root Kernel Bridge) -/

/-- Exact `i8Layout` matching `MiniRustSpec.Correspondence.Witness.i8Layout` for
definitional `rfl` cross-root fixture locks. -/
def ep2I8Layout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false }

@[reducible] def ep2DummySpan : String := "ep2.rs:1:1"
@[reducible] def mkSt (k : StatementKind) : MirAst.Statement := { kind := k, span := ep2DummySpan }
@[reducible] def mkTm (k : TerminatorKind) : MirAst.Terminator := { kind := k, span := ep2DummySpan }
@[reducible] def mkBb (stmts : List MirAst.Statement) (term : TerminatorKind) (isCleanup : Bool := false) :
    MirAst.BasicBlockData :=
  { statements := stmts, terminator := mkTm term, isCleanup }
@[reducible] def mkDecl (ty : Ty) : LocalDecl := { mutability := .mut, ty, debugName := none }
@[reducible] def locPlace (i : Nat) (proj : List ProjectionElem := []) : Place :=
  { local_ := i, projection := proj }

def mkMirBody (defPath : String) (decls : List LocalDecl) (argCount : Nat)
    (blocks : List BasicBlockData) (layouts : LayoutTable := emptyLayoutTable) : CapturedMir :=
  { defPath, phase := .runtimePostCleanup, role := .subject, argCount, localDecls := decls,
    basicBlocks := blocks, layouts, allocations := [],
    fnAbi := { args := [], ret := { layout := ep2I8Layout, mode := .direct },
               conv := .rust, canUnwind := true } }

@[reducible] def u8MirTy : Ty := { kind := .uint .u8, layoutIdx := 0 }
@[reducible] def u32MirTy : Ty := { kind := .uint .u32, layoutIdx := 0 }
@[reducible] def i32MirTy : Ty := { kind := .int .i32, layoutIdx := 0 }
@[reducible] def u64MirTy : Ty := { kind := .uint .u64, layoutIdx := 0 }
@[reducible] def usizeMirTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
@[reducible] def boolMirTy : Ty := { kind := .bool, layoutIdx := 0 }
@[reducible] def unitMirTy : Ty := { kind := .tuple [], layoutIdx := 0 }
@[reducible] def pairU32MirTy : Ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 }
@[reducible] def rawConstUnitMirTy : Ty := { kind := .rawPtr .not (.tuple []), layoutIdx := 0 }
@[reducible] def rawConstU32MirTy : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }
@[reducible] def rawMutU32MirTy : Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }
@[reducible] def rawMutU8MirTy : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }
@[reducible] def boxU32MirTy : Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }
@[reducible] def boxU64MirTy : Ty := { kind := .rawPtr .mut (.uint .u64), layoutIdx := 0 }
@[reducible] def sliceU32MirTy : Ty := { kind := .slice (.uint .u32), layoutIdx := 0 }
@[reducible] def strMirTy : Ty := { kind := .str, layoutIdx := 0 }
@[reducible] def rawConstSliceU32MirTy : Ty := { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 0 }
@[reducible] def rawConstStrMirTy : Ty := { kind := .rawPtr .not .str, layoutIdx := 0 }
@[reducible] def closureZstMirTy (dp : String) : Ty := { kind := .closure dp [], layoutIdx := 0 }
@[reducible] def closureCapMirTy (dp : String) : Ty :=
  { kind := .closure dp [.uint .u32, .rawPtr .not (.uint .u32)], layoutIdx := 0 }

@[reducible] def constU32 (n : Nat) : Operand :=
  .constant { ty := u32MirTy, val := .scalar (.int ⟨n, 4⟩) }

def nonZeroU8MirLayout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .scalar (.initialized (.int 8 false) ⟨1, 255⟩),
    fields := .arbitrary [⟨0⟩] [0], variants := .single 0, isUninhabited := false }

def nonZeroU8Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [nonZeroU8MirLayout] }

@[reducible] def nonZeroU8MirTy : Ty :=
  { kind := .adt "core::num::nonzero::NonZero" [.uint .u8], layoutIdx := 0 }

def binderU32MirLayout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xffffffff⟩),
    fields := .arbitrary [⟨0⟩] [0], variants := .single 0, isUninhabited := false }

def boolScalarMirLayout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def ep2BinderLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [binderU32MirLayout, binderU32MirLayout, nonZeroU8MirLayout, boolScalarMirLayout] }

@[reducible] def binderU32MirTy : Ty := { kind := .adt "ep2::BinderU32" [], layoutIdx := 1 }
@[reducible] def binderNzU8MirTy : Ty := { kind := .adt "ep2::BinderNonZeroU8" [], layoutIdx := 2 }
@[reducible] def binderBoolMirTy : Ty := { kind := .bool, layoutIdx := 3 }

/-- Exact 8-variant `CapturedMir` fixtures (locked by `rfl` to MR & Bundle in cross-root bridge). -/
def v1CoverageOkMir : CapturedMir :=
  mkMirBody "ep2::c4_coverage" [mkDecl u32MirTy] 0
    [mkBb [mkSt .coverage, mkSt (.assign (locPlace 0) (.use (constU32 17)))] .return_]

def v1CoverageUbMir : CapturedMir :=
  mkMirBody "ep2::v1_coverage_ub" [mkDecl u32MirTy] 0
    [mkBb [mkSt .coverage] .unreachable]

def v2DropHintOkMir : CapturedMir :=
  mkMirBody "ep2::c5_drop_hint" [mkDecl u32MirTy, mkDecl rawMutU32MirTy] 0
    [mkBb [mkSt (.storageDead 1), mkSt .coverage,
           mkSt (.backwardIncompatibleDropHint (locPlace 1 [.deref])),
           mkSt (.backwardIncompatibleDropHint (locPlace 99)),
           mkSt (.backwardIncompatibleDropHint (locPlace 0)),
           mkSt (.assign (locPlace 0) (.use (constU32 23)))] .return_]

def v2DropHintDeadReadUbMir : CapturedMir :=
  mkMirBody "ep2::v2_drophint_ub" [mkDecl u32MirTy, mkDecl u32MirTy] 0
    [mkBb [mkSt (.storageDead 1),
           mkSt (.backwardIncompatibleDropHint (locPlace 1)),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1))))] .return_]

def v3DropWholeOkMir : CapturedMir :=
  mkMirBody "ep2::v3_drop_whole_ok" [mkDecl u32MirTy, mkDecl u32MirTy] 1
    [mkBb [] (.drop (locPlace 1) 1 .continue_),
     mkBb [mkSt (.assign (locPlace 0) (.use (constU32 42)))] .return_]

def v3DropProjSiblingOkMir : CapturedMir :=
  mkMirBody "ep2::v3_drop_proj_sibling_ok" [mkDecl u32MirTy, mkDecl pairU32MirTy] 1
    [mkBb [] (.drop (locPlace 1 [.field 0 u32MirTy]) 1 .continue_),
     mkBb [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.field 1 u32MirTy]))))] .return_]

def v3DropProjReadDroppedUbMir : CapturedMir :=
  mkMirBody "ep2::v3_drop_proj_read_dropped_ub" [mkDecl u32MirTy, mkDecl pairU32MirTy] 1
    [mkBb [] (.drop (locPlace 1 [.field 0 u32MirTy]) 1 .continue_),
     mkBb [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.field 0 u32MirTy]))))] .return_]

def v3DropDeadUbMir : CapturedMir :=
  mkMirBody "ep2::v3_drop_dead_ub" [mkDecl u32MirTy, mkDecl u32MirTy] 1
    [mkBb [mkSt (.storageDead 1)] (.drop (locPlace 1) 1 .continue_),
     mkBb [mkSt (.assign (locPlace 0) (.use (constU32 42)))] .return_]

def v3DropPostReadMir : CapturedMir :=
  mkMirBody "ep2::v3_drop_post_read" [mkDecl u32MirTy, mkDecl u32MirTy] 1
    [mkBb [] (.drop (locPlace 1) 1 .continue_),
     mkBb [mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1))))] .return_]

def v3DropProtectedMir : CapturedMir := v3DropWholeOkMir

def v4ShallowInitBoxOkMir : CapturedMir :=
  mkMirBody "ep2::v4_shallow_init_box_ok" [mkDecl boxU32MirTy, mkDecl rawMutU8MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.shallowInitBox (.copy (locPlace 1)) u32MirTy))] .return_]

def v4ShallowInitBoxDistinctOkMir : CapturedMir :=
  mkMirBody "ep2::v4_shallow_init_box_distinct_ok" [mkDecl boxU64MirTy, mkDecl rawMutU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.shallowInitBox (.copy (locPlace 1)) u64MirTy))] .return_]

def v4ShallowInitBoxNonPtrUnsupMir : CapturedMir :=
  mkMirBody "ep2::v4_shallow_init_box_nonptr_unsup" [mkDecl boxU32MirTy, mkDecl u64MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.shallowInitBox (.copy (locPlace 1)) u32MirTy))] .return_]

def v5WrapTransparentRoundtripMir : CapturedMir :=
  mkMirBody "ep2::v5_wrap_transparent_rt" [mkDecl u32MirTy, mkDecl u32MirTy, mkDecl u32MirTy] 1
    [mkBb [mkSt (.storageLive 2),
           mkSt (.assign (locPlace 2) (.wrapUnsafeBinder (.copy (locPlace 1)) u32MirTy)),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 2 [.unwrapUnsafeBinder u32MirTy]))))]
      .return_]

def v5WrapStructRoundtripMir : CapturedMir :=
  mkMirBody "ep2::v5_wrap_struct_rt" [mkDecl u32MirTy, mkDecl u32MirTy, mkDecl binderU32MirTy] 1
    [mkBb [mkSt (.storageLive 2),
           mkSt (.assign (locPlace 2) (.wrapUnsafeBinder (.copy (locPlace 1)) binderU32MirTy)),
           mkSt (.assign (locPlace 0) (.use (.copy (locPlace 2 [.unwrapUnsafeBinder binderU32MirTy, .field 0 u32MirTy]))))]
      .return_]
    ep2BinderLayouts

def v5WrapNzU8Mir : CapturedMir :=
  mkMirBody "ep2::v5_wrap_nzu8" [mkDecl binderNzU8MirTy, mkDecl u8MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.wrapUnsafeBinder (.copy (locPlace 1)) binderNzU8MirTy))] .return_]
    ep2BinderLayouts

def v5WrapBoolMir : CapturedMir :=
  mkMirBody "ep2::v5_wrap_bool" [mkDecl binderBoolMirTy, mkDecl u8MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.wrapUnsafeBinder (.copy (locPlace 1)) binderBoolMirTy))] .return_]
    ep2BinderLayouts

def v6SubtypeU32ToI32Mir : CapturedMir :=
  mkMirBody "ep2::c7_subtype_u32_i32" [mkDecl i32MirTy, mkDecl u32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .subtype (.copy (locPlace 1)) i32MirTy))] .return_]

def v6SubtypeU8ToBoolMir : CapturedMir :=
  mkMirBody "ep2::c7_subtype_u8_bool" [mkDecl boolMirTy, mkDecl u8MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .subtype (.copy (locPlace 1)) boolMirTy))] .return_]

def v6SubtypeU8ToNzMir : CapturedMir :=
  mkMirBody "ep2::c7_subtype_u8_nz" [mkDecl nonZeroU8MirTy, mkDecl u8MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .subtype (.copy (locPlace 1)) nonZeroU8MirTy))] .return_]
    nonZeroU8Layouts

def v6SubtypePtrMir : CapturedMir :=
  mkMirBody "ep2::c7_subtype_ptr" [mkDecl rawConstU32MirTy, mkDecl rawMutU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .subtype (.copy (locPlace 1)) rawConstU32MirTy))] .return_]

def v7RawPtrThinMir : CapturedMir :=
  mkMirBody "ep2::v7_rawptr_thin" [mkDecl rawConstU32MirTy, mkDecl rawConstUnitMirTy, mkDecl unitMirTy] 2
    [mkBb [mkSt (.assign (locPlace 0) (.aggregate (.rawPtr u32MirTy .not) [.copy (locPlace 1), .copy (locPlace 2)]))] .return_]

def v7RawPtrWideSliceMetaMir : CapturedMir :=
  mkMirBody "ep2::v7_rawptr_wide_slice" [mkDecl usizeMirTy, mkDecl rawConstUnitMirTy, mkDecl usizeMirTy, mkDecl rawConstSliceU32MirTy] 2
    [mkBb [mkSt (.storageLive 3),
           mkSt (.assign (locPlace 3) (.aggregate (.rawPtr sliceU32MirTy .not) [.copy (locPlace 1), .copy (locPlace 2)])),
           mkSt (.assign (locPlace 0) (.unaryOp .ptrMetadata (.copy (locPlace 3))))] .return_]

def v7RawPtrWideStrMetaMir : CapturedMir :=
  mkMirBody "ep2::v7_rawptr_wide_str" [mkDecl usizeMirTy, mkDecl rawConstUnitMirTy, mkDecl usizeMirTy, mkDecl rawConstStrMirTy] 2
    [mkBb [mkSt (.storageLive 3),
           mkSt (.assign (locPlace 3) (.aggregate (.rawPtr strMirTy .not) [.copy (locPlace 1), .copy (locPlace 2)])),
           mkSt (.assign (locPlace 0) (.unaryOp .ptrMetadata (.copy (locPlace 3))))] .return_]

def v8ClosureZstMir : CapturedMir :=
  mkMirBody "ep2::v8_closure_zst" [mkDecl (closureZstMirTy "ep2::zst")] 0
    [mkBb [mkSt (.assign (locPlace 0) (.aggregate (.closure "ep2::zst") []))] .return_]

def ep2ZstClosureLayout : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

def ep2U32FieldLayout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xffffffff⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def ep2PtrFieldLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 0xffffffffffffffff⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def ep2ClosureCapLayout : TypeLayout :=
  { size := ⟨16⟩, align := ⟨8⟩,
    backendRepr := .scalarPair
      (.initialized (.int 32 false) ⟨0, 0xffffffff⟩)
      (.initialized (.pointer 0) ⟨0, 0xffffffffffffffff⟩),
    fields := .arbitrary [⟨0⟩, ⟨8⟩] [0, 1],
    fieldLayouts := [2, 3],
    variants := .single 0, isUninhabited := false }

def ep2ClosureCapLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [ep2ZstClosureLayout, ep2ClosureCapLayout, ep2U32FieldLayout, ep2PtrFieldLayout] }

@[reducible] def v8ClosureCapMirTy : Ty :=
  { kind := .closure "ep2::cap" [.uint .u32, .rawPtr .not (.uint .u32)], layoutIdx := 1 }

def v8ClosureCapMir : CapturedMir :=
  mkMirBody "ep2::v8_closure_cap"
    [mkDecl v8ClosureCapMirTy, mkDecl u32MirTy, mkDecl rawConstU32MirTy] 2
    [mkBb [mkSt (.assign (locPlace 0) (.aggregate (.closure "ep2::cap") [.move (locPlace 1), .copy (locPlace 2)]))]
      .return_]
    ep2ClosureCapLayouts

/-! ## §1. Conservative Hook Overlay (`annealStepHooksDropBinderSubtype`) -/

/-- `AggregateHooks` overlay extending `annealAggregateHooksUnwindFnPtrClosure`
with `readPointer` and `readScalar` so vendored `Miri.Interpreter.writeAggregate`
executes `AggregateKind.RawPtr` (thin `()` and wide `[u32]`/`str` `usize`) natively! -/
def annealAggregateHooksDropBinderSubtype (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.AggregateHooks AnnealProv AnnealStepState Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealAggregateHooksUnwindFnPtrClosure localDecls layouts with
    readPointer := fun _ op => do
      let imm ← annealReadImmediateOverlay op
      let sc ← match imm.imm.toScalar with
        | .ok s => pure s
        | .error e => throw (Miri.Interpreter.ScalarOps.immediateError e)
      match sc.toPointer annealTargetDataLayout with
      | .ok p => pure p
      | .error e => throw (Miri.Interpreter.ScalarOps.scalarError e)
    readScalar := fun _ op => do
      let imm ← annealReadImmediateOverlay op
      match imm.imm.toScalar with
      | .ok s => pure s
      | .error e => throw (Miri.Interpreter.ScalarOps.immediateError e) }

/-- Syntactic predicate for `Assign` rvalues routed through the Episode 2 overlay
(strictly extending `isUnwindFnPtrClosureAssign` with `.WrapUnsafeBinder`,
`.Aggregate (.RawPtr ..)`, `.Cast .Transmute`, and `.UnaryOp .PtrMetadata`). -/
def isDropBinderSubtypeAssign (localDecls : List LocalDecl) (place : Miri.MIR.Place)
    (rvalue : Miri.MIR.Rvalue) : Bool :=
  isUnwindFnPtrClosureAssign localDecls place rvalue ||
  match rvalue with
  | .WrapUnsafeBinder _ _ => true
  | .Aggregate (.RawPtr ..) _ => true
  | .Cast .Transmute _ _ => true
  | .UnaryOp .PtrMetadata _ => true
  | _ => false

/-- `RvalueHooks` overlay extending `annealRvalueHooksUnwindFnPtrClosure` for
`Rvalue.WrapUnsafeBinder`, `AggregateKind.RawPtr`, `CastKind.Transmute`
(lowered `ShallowInitBox`), and `UnaryOp.PtrMetadata` on wide raw pointers. -/
def annealRvalueHooksDropBinderSubtype (currentBody : CapturedMir) (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.RvalueHooks AnnealProv AnnealStepState Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let decls := currentBody.localDecls
  let layouts := currentBody.layouts
  let base := annealRvalueHooksUnwindFnPtrClosure currentBody fnPtrs
  { base with
    writeAggregate := fun c k os d =>
      match k with
      | .RawPtr .. =>
          Miri.Interpreter.writeAggregate (annealAggregateHooksDropBinderSubtype decls layouts) c k os d
      | _ => base.writeAggregate c k os d
    cast := fun c src kind ty dest =>
      match kind with
      | .Transmute =>
          Miri.Interpreter.Cast.cast (annealCastHooksUnwindFnPtrClosure currentBody fnPtrs) c 16 src .Transmute ty dest
      | _ => base.cast c src kind ty dest }

/-- Allocation-relative byte offset of absolute address `addr` inside allocation
`aid`, read from the machine's vendored `AllocAddresses` base-address table
(`none` if `aid` has no recorded base or `addr` lies below it). -/
def ep2RelOffset? (mach : AnnealMachine) (aid : Miri.Memory.AllocId) (addr : UInt64) : Option UInt64 :=
  match mach.addresses.baseAddr.find? (fun e => e.allocId == aid) with
  | some e => if e.address ≤ addr then some (addr - e.address) else none
  | none => none

/-- Byte range `(offsetWithinLocal, size)` of field `idx` of local `localId`,
derived (never hardcoded) from the local's vendored Miri layout
(`FieldsShape.Arbitrary` offsets) and:
1. First, the recorded `LayoutTable` field layout (`tl.fieldLayouts[idx]?` → `fl.size.bytes`),
   handling structs/ADTs and fields with non-zero `layoutIdx`;
2. Falling back to `MirSemantics.tyByteSize` on tuple/closure component types when
   no `fieldLayouts` table entry is attached (e.g., `emptyLayoutTable`).
Fails closed (`none`) for any other shape. -/
def ep2FieldByteRange? (decls : List LocalDecl) (layouts : LayoutTable) (localId : Nat)
    (lay? : Option Miri.Interpreter.LocalLayout) (idx : Nat) : Option (UInt64 × Nat) :=
  match lay?, get? decls localId with
  | some lay, some decl =>
    match lay.layout.fields with
    | .Arbitrary offs _ =>
      match offs[idx]? with
      | some off =>
        let layoutSz? : Option Nat :=
          match resolvedTyLayout? decls layouts decl.ty with
          | some tl =>
            match get? tl.fieldLayouts idx with
            | some flIdx =>
              if isUnresolvedLayoutIdx layouts flIdx then none
              else (layouts.lookup flIdx).map (·.size.bytes)
            | none => none
          | none => none
        let sz? : Option Nat :=
          match layoutSz? with
          | some sz => some sz
          | none =>
            let fieldKind? : Option RigidTy :=
              match decl.ty.kind with
              | .tuple tys => get? tys idx
              | .closure _ tys => get? tys idx
              | _ => none
            fieldKind?.bind (fun fk => tyByteSize decls layouts { kind := fk, layoutIdx := 0 })
        sz?.map (fun sz => (off.bytes, sz))
      | none => none
    | _ => none
  | _, _ => none

/-- **Field-range layout resolution regression (B2)**: the local's recorded
layout is resolved through Trusted `resolvedTyLayout?` / `isUnresolvedLayoutIdx`
(index `0` is the reserved unresolved slot), so a `(u32, u32)` local with
`layoutIdx := 0` in a table whose dummy entry `0` carries `fieldLayouts := [1, 1]`
(pointing at an 8-byte layout) still drops exactly 4 bytes per field (A1 read the
dummy entry and would have deinitialized the sibling too); while a resolved closure
local (`v8ClosureCapMirTy`, `layoutIdx := 1`) takes its field sizes (`u32` = 4,
`*const u32` = 8) from the recorded `fieldLayouts` at the vendored offsets. -/
theorem ep2FieldByteRange?_layout_resolution :
    let pairLay : Miri.Interpreter.LocalLayout :=
      { ty := encodeTyIdOverlay pairU32MirTy,
        layout := {
          fields := .Arbitrary #[Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 4] #[0, 1],
          variants := .Single 0,
          backendRepr := .Memory (sized := true),
          largestNiche := none, uninhabited := false,
          align := ⟨⟨2⟩⟩, size := Miri.ABI.Size.ofBytes 8,
          maxReprAlign := none, unadjustedAbiAlign := ⟨2⟩,
          reprC := false, randomizationSeed := 0 } }
    let dummy0 : TypeLayout :=
      { size := ⟨8⟩, align := ⟨4⟩, backendRepr := .memory,
        fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], fieldLayouts := [1, 1],
        variants := .single 0, isUninhabited := false }
    let big1 : TypeLayout :=
      { size := ⟨8⟩, align := ⟨8⟩, backendRepr := .memory,
        fields := .primitive, variants := .single 0, isUninhabited := false }
    let lays : LayoutTable := { pointerBits := 64, isLittleEndian := true, entries := [dummy0, big1] }
    let decls := [mkDecl u32MirTy, mkDecl pairU32MirTy]
    ep2FieldByteRange? decls lays 1 (some pairLay) 0 = some (0, 4) ∧
    ep2FieldByteRange? decls lays 1 (some pairLay) 1 = some (4, 4) ∧
    ep2FieldByteRange? v8ClosureCapMir.localDecls ep2ClosureCapLayouts 0
      (some (translateTyOverlay v8ClosureCapMirTy ep2ClosureCapLayouts)) 0 = some (0, 4) ∧
    ep2FieldByteRange? v8ClosureCapMir.localDecls ep2ClosureCapLayouts 0
      (some (translateTyOverlay v8ClosureCapMirTy ep2ClosureCapLayouts)) 1 = some (8, 8) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Walk parent pointers in vendored `BorrowTree.nodes` (bounded by `fuel`) to test
whether `anc` is an ancestor of (or equal to) `cur` in the borrow tree. -/
def ep2IsAncestor (tree : Miri.TreeBorrows.BorrowTree) (anc : Miri.TreeBorrows.UniIndex) :
    Miri.TreeBorrows.UniIndex → Nat → Bool
  | _, 0 => false
  | cur, fuel + 1 =>
    if cur == anc then true
    else
      match tree.nodes.get cur with
      | some node =>
        match node.parent with
        | some p => ep2IsAncestor tree anc p fuel
        | none => false
      | none => false

/-- State-transitioning Tree Borrows `.Write` through `tag` on `[start, start + size)`
for an allocation whose vendored borrow tree is `tree`:
* fails closed (`none`) when `tag` is unregistered in `tree` (matching vendored
  `BorrowTree.performBorrowAccessRange`'s `.MissingTag`) or when any overlapping
  segment/node transition via unmodified vendored
  `Miri.TreeBorrows.Tree.LocationState.performAccess` does not return `.Success`;
* splits any partially-overlapping range segment so ONLY `[start, start + size)`
  transitions while sibling bytes keep their original permissions;
* writes every updated `LocationState` (e.g., disabling an unprotected foreign child
  tag from `.Unique` to `.Disabled`!) back into the returned `BorrowTree` so
  subsequent accesses observe exact post-drop permissions rather than stale state! -/
def ep2ApplyTreeBorrowsWrite (protectedTags : Miri.TreeBorrows.ProtectedTags)
    (tree : Miri.TreeBorrows.BorrowTree) (tag : Miri.Memory.BorTag)
    (start size : Miri.ABI.Size) : Option Miri.TreeBorrows.BorrowTree :=
  let startNat := start.bytes.toNat
  let endNat := startNat + size.bytes.toNat
  let fuel := tree.nodes.data.size + 1
  match tree.tagMapping.get tag with
  | none => none
  | some srcIdx =>
    -- Zero-sized accesses never reach the borrow tracker (vendored
    -- `DedupRangeMap.iterMutWithClone` returns no positions when `len = 0`, so
    -- `performBorrowAccessRange` completes with the tree unchanged).
    if size.bytes.toNat = 0 then some tree else
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
          match Miri.TreeBorrows.Tree.LocationState.performAccess ls .Write relPos isProt with
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

/-- Boolean conflict predicate backed directly by `ep2ApplyTreeBorrowsWrite`. -/
def ep2ProtectorConflict (protectedTags : Miri.TreeBorrows.ProtectedTags)
    (tree : Miri.TreeBorrows.BorrowTree) (tag : Miri.Memory.BorTag)
    (start size : Miri.ABI.Size) : Bool :=
  (ep2ApplyTreeBorrowsWrite protectedTags tree tag start size).isNone

/-- Two-node vendored Tree Borrows tree over the 4 bytes of a `u32` local: root
`retagParentTag` (`Unique`) with an accessed `Unique` child `retagChildTag`
(`hooksTwoNodeTree .unique`, restricted to `[0, 4)`). -/
private def lmU32ChildTree : Miri.TreeBorrows.BorrowTree :=
  { hooksTwoNodeTree .unique with
    locations := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 4) (hooksLocTree .unique) }

/-- Bridge to unmodified vendored Tree Borrows:
1. On `hooksTwoNodeTree .unique` (`[0, 8)`), `ep2ProtectorConflict` for a write
   through root `retagParentTag` agrees identically with unmodified vendored
   `BorrowTree.performBorrowAccessRange` (`.Write` over `[0, 8)`) for BOTH
   `isProtected ∈ {false, true}`;
2. On `lmU32ChildTree` (`[0, 4)` — the EXACT tree in `mkTbDropMiriState`),
   `ep2ProtectorConflict` returns `isProtected`;
3. Child write through `retagChildTag` with protected parent `retagParentTag`
   does NOT conflict (`false`), matching Tree Borrows ancestry semantics;
4. Disjoint byte range `[4, 8)` on `lmU32ChildTree` does NOT conflict (`false`);
5. Interior-mutable protected child (`hooksTwoNodeTree .cell`) does NOT conflict
   on a foreign write (`ep2ProtectorConflict = false` AND `performBorrowAccessRange`
   `.Completed`)!
6. A write through a tag absent from the tree (`BorTag 3`) conflicts (fail closed,
   as vendored `.MissingTag`), even with no protectors at all. -/
theorem ep2ProtectorConflict_agrees_with_vendored_tree_borrows (isProtected : Bool) :
    let parentProt : Miri.TreeBorrows.ProtectedTags :=
      ({} : Miri.TreeBorrows.ProtectedTags).insert retagParentTag .StrongProtector
    ep2ProtectorConflict (hooksForChildProtected isProtected).protectedTags
        (hooksTwoNodeTree .unique) retagParentTag Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) = isProtected ∧
    (((hooksTwoNodeTree .unique).performBorrowAccessRange (.concrete retagParentTag)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) .Write
        (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed).status = .Completed ↔
      isProtected = false) ∧
    ep2ProtectorConflict (hooksForChildProtected isProtected).protectedTags
        lmU32ChildTree retagParentTag Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4) = isProtected ∧
    ep2ProtectorConflict parentProt
        lmU32ChildTree retagChildTag Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4) = false ∧
    ep2ProtectorConflict (hooksForChildProtected true).protectedTags
        lmU32ChildTree retagParentTag (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 4) = false ∧
    ep2ProtectorConflict (hooksForChildProtected true).protectedTags
        (hooksTwoNodeTree .cell) retagParentTag Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) = false ∧
    ep2ProtectorConflict {} lmU32ChildTree ⟨3, by decide⟩ Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4) = true := by
  refine ⟨by cases isProtected <;> decide +kernel, ?_,
          by cases isProtected <;> decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have h := (borrowTree_performBorrowAccessRange_simulation .write .foreignAccess .unique isProtected).1
  refine h.trans ?_
  cases isProtected <;> decide +kernel

/-- **Post-Drop Tree Borrows State Transition & Sub-Range Split Regression (A2)**:
1. Writing through root `retagParentTag` on unprotected `lmU32ChildTree` succeeds
   (`some tree'`) AND disables `retagChildTag` (`Unique → Disabled`), so a subsequent
   write through `retagChildTag` on `tree'` NOW CONFLICTS (`true`, ruling out stale
   pre-drop permissions!);
2. Writing through root `retagParentTag` on the first 4 bytes `[0, 4)` of the 8-byte
   unprotected `hooksTwoNodeTree .unique` splits `[0, 8)` into `[0, 4)` (child disabled)
   and `[4, 8)` (child still `Unique`), so a subsequent write through `retagChildTag`
   conflicts on `[0, 4)` (`true`) while sibling `[4, 8)` STILL SUCCEEDS (`false`)! -/
theorem ep2ApplyTreeBorrowsWrite_disables_unprotected_child_and_splits_subrange :
    (match ep2ApplyTreeBorrowsWrite {} lmU32ChildTree retagParentTag
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4) with
      | some tree' =>
        ep2ProtectorConflict {} tree' retagChildTag Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4)
      | none => false) = true ∧
    (match ep2ApplyTreeBorrowsWrite {} (hooksTwoNodeTree .unique) retagParentTag
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4) with
      | some tree' =>
        ep2ProtectorConflict {} tree' retagChildTag Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4) &&
        !(ep2ProtectorConflict {} tree' retagChildTag (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 4))
      | none => false) = true :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **Zero-sized-access & persistence regressions (B3)**:
1. A zero-sized write strictly inside a segment (`[4, 4)` of the 8-byte
   `hooksTwoNodeTree .unique`) is a no-op returning the IDENTICAL tree, even with the
   child protected (vendored `iterMutWithClone` skips `len = 0`; A2 applied the write
   transition there, so a ZST drop under a protector was spuriously UB, and an
   unprotected one inserted an empty `[4, 4)` segment);
2. a write that changes no permission (child write through `retagChildTag` on
   `[0, 4)` of `lmU32ChildTree`, already `Unique`/accessed) returns the identical,
   unsplit tree (no redundant segments).
(End-to-end persistence through `runMiriSteps`: `lm_v3_drop_tb_tree_persisted`.) -/
theorem ep2ApplyTreeBorrowsWrite_zero_size_noop_and_persistence :
    ep2ApplyTreeBorrowsWrite (hooksForChildProtected true).protectedTags (hooksTwoNodeTree .unique)
      retagParentTag (Miri.ABI.Size.ofBytes 4) Miri.ABI.Size.ZERO = some (hooksTwoNodeTree .unique) ∧
    ep2ApplyTreeBorrowsWrite {} (hooksTwoNodeTree .unique)
      retagParentTag (Miri.ABI.Size.ofBytes 4) Miri.ABI.Size.ZERO = some (hooksTwoNodeTree .unique) ∧
    ep2ApplyTreeBorrowsWrite {} lmU32ChildTree
      retagChildTag Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4) = some lmU32ChildTree ∧
    ep2ApplyTreeBorrowsWrite {} lmU32ChildTree
      ⟨3, by decide⟩ Miri.ABI.Size.ZERO Miri.ABI.Size.ZERO = none := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Adjacent Segment Coalescing & `len` Overflow Guard Regressions (A3)**:
1. Dropping `[0, 4)` then `[4, 8)` on 8-byte `hooksTwoNodeTree .unique` coalesces the
   two newly-equal adjacent segments back into ONE canonical `[0, 8)` segment, matching
   a single `[0, 8)` write identically (preserving `DedupRangeMap`'s dedup invariant);
2. `ep2DeinitIndirect` guards `base.toNat + relInLocal.toNat + len ≥ 2 ^ 64`, so a
   pathological `len = 2 ^ 64` faults `"drop offset overflow"` instead of wrapping
   `UInt64.ofNat len` to `0` and silently becoming a no-op! -/
theorem ep2ApplyTreeBorrowsWrite_coalesces_adjacent_segments :
    (ep2ApplyTreeBorrowsWrite {} (hooksTwoNodeTree .unique) retagParentTag
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4) >>= fun t1 =>
      ep2ApplyTreeBorrowsWrite {} t1 retagParentTag
        (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 4)) =
    ep2ApplyTreeBorrowsWrite {} (hooksTwoNodeTree .unique) retagParentTag
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) := by
  decide +kernel

/-- Deinitialize `len` bytes at `relInLocal` inside the memory-backed local `mp`
and jump to `target`:
* the allocation-relative start is `mp`'s address minus the allocation's recorded
  base address (`ep2RelOffset?`), guarded against `UInt64` overflow of
  `base + relInLocal + len` (preventing `UInt64.ofNat len` wraparound to `0`);
* when `treeBorrows = true` and the allocation carries a borrow tree and the
  machine a borrow tracker, `ep2ApplyTreeBorrowsWrite` validates AND transitions
  the borrow tree on `[start, start + size)` through unmodified vendored
  `Miri.TreeBorrows.Tree.LocationState.performAccess`, writing the updated tree
  back into the allocation's `extra` field via `Allocation.setExtra`;
* the bytes are then cleared by unmodified vendored `Allocation.writeUninit`. -/
def ep2DeinitIndirect (treeBorrows : Bool) (mp : Miri.Interpreter.MemPlace AnnealProv)
    (relInLocal : UInt64) (len : Nat) (target : Miri.MIR.BasicBlockId)
    (state : AnnealStepState) : Miri.Interpreter.StepResult AnnealStepState Unit :=
  match mp.ptr.provenance with
  | some (.concrete aid tag) =>
    match state.machine.memory.live.findIdx? (fun e => e.1 == aid),
          ep2RelOffset? state.machine aid mp.ptr.offset.bytes with
    | some lIdx, some base =>
      if base.toNat + relInLocal.toNat + len ≥ 2 ^ 64 then
        (state, .error (.undefinedBehavior "drop offset overflow"))
      else
      match state.machine.memory.live[lIdx]? with
      | some (_, liveAlloc) =>
        let start := Miri.ABI.Size.ofBytes (base + relInLocal)
        let size := Miri.ABI.Size.ofBytes (UInt64.ofNat len)
        let tbRes : Option (Option Miri.TreeBorrows.BorrowTree) :=
          match treeBorrows, state.machine.borrowTracker, liveAlloc.allocation.extra with
          | true, some bt, some tree =>
            (ep2ApplyTreeBorrowsWrite bt.global.protectedTags tree tag start size).map some
          | _, _, ext => some ext
        match tbRes with
        | none =>
          (state, .error (.undefinedBehavior "Tree Borrows write conflict on drop"))
        | some extra' =>
          match Miri.Memory.Allocation.writeUninit (Miri.Memory.allocRange start size)
              (Miri.ABI.Size.ofBytes 8) liveAlloc.allocation with
          | .ok () alloc' =>
            let mach' := updateAllocMachine state.machine lIdx aid liveAlloc.kind (alloc'.setExtra extra')
            Miri.Interpreter.ControlFlow.goToBlock target { state with machine := mach' }
          | .error _ _ => (state, .error (.undefinedBehavior "drop out of bounds"))
      | none => (state, .error (.undefinedBehavior "drop on dangling allocation"))
    | _, _ => (state, .error (.undefinedBehavior "drop on dangling allocation"))
  | _ => (state, .error (.unsupported "drop without concrete provenance"))

/-- Episode 2 `Drop` overlay. Memory-backed (`.indirect`) locals are deinitialized
in memory (whole local: the local's full layout size; `[.Field idx _]`: the field's
layout-derived byte range) through `ep2DeinitIndirect`, with the Tree Borrows
write check enabled by `treeBorrows`. Every other case — no frame, dead local,
immediate local (which has no memory and hence no borrow tree or protector),
lookup errors — is delegated verbatim to `annealEvalDropLM4_1`. -/
def annealEvalDropOverlay (decls : List LocalDecl) (layouts : LayoutTable)
    (treeBorrows : Bool) (place : Miri.MIR.Place)
    (target : Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (state : AnnealStepState) : Miri.Interpreter.StepResult AnnealStepState Unit :=
  match state.stack.currentFrame? with
  | none => annealEvalDropLM4_1 place target unwind state
  | some frame =>
    match frame.getLocal place.localId with
    | .ok { value := .live (.indirect mp), layout := lay? } =>
      match place.projection.toList with
      | [] =>
        match lay? with
        | some lay => ep2DeinitIndirect treeBorrows mp 0 lay.layout.size.bytes.toNat target state
        | none => (state, .error (.unsupported "indirect drop without layout"))
      | [.Field idx _] =>
        match ep2FieldByteRange? decls layouts place.localId lay? idx with
        | some (off, sz) => ep2DeinitIndirect treeBorrows mp off sz target state
        | none => (state, .error (.unsupported "projected drop: field byte range not derivable"))
      | _ => (state, .error (.unsupported "projected drop terminator"))
    | _ => annealEvalDropLM4_1 place target unwind state

/-- The Episode 2 drop overlay coincides with the base `annealEvalDropLM4_1`
whenever the dropped local is not memory-backed. -/
theorem annealEvalDropOverlay_eq_base_of_not_indirect (decls : List LocalDecl) (layouts : LayoutTable)
    (treeBorrows : Bool) (place : Miri.MIR.Place) (target : Miri.MIR.BasicBlockId)
    (unwind : Miri.MIR.UnwindAction) (state : AnnealStepState)
    (h : ∀ frame, state.stack.currentFrame? = some frame →
      ∀ mp lay?, frame.getLocal place.localId ≠ .ok ⟨.live (.indirect mp), lay?⟩) :
    annealEvalDropOverlay decls layouts treeBorrows place target unwind state =
      annealEvalDropLM4_1 place target unwind state := by
  unfold annealEvalDropOverlay
  cases hcf : state.stack.currentFrame? with
  | none => rfl
  | some frame =>
    dsimp only
    cases hgl : frame.getLocal place.localId with
    | error _ => rfl
    | ok ls =>
      rcases ls with ⟨value, lay?⟩
      cases value with
      | dead => rfl
      | live op =>
        cases op with
        | immediate _ => rfl
        | indirect mp => exact absurd hgl (h frame hcf mp lay?)

/-- Predicate detecting root-frame return places whose layout is a `ScalarPair`
with a pointer second field (e.g., 2-capture closure `(u32, *const u32)`),
where upstream `annealReadIndirectImmediate` hardcodes `readProvenance := false`
and `bOffset` without checking `fields`. -/
def isPtrScalarPairReturnPlace (rp : Miri.Interpreter.RuntimeStackPlace AnnealProv) : Bool :=
  match rp with
  | .frameLocal _ _ none retLay _ =>
    match retLay.layout.backendRepr with
    | .ScalarPair (b := .Initialized (value := .Pointer _)) => true
    | _ => false
  | _ => false

/-- Return-copy overlay extending `annealCopyReturnLM4_1` to validate indirect
pointer-containing `ScalarPair` root-frame returns via unmodified vendored
`Miri.Memory.Allocation.readScalar` (`readProvenance := true` on the pointer
field at its layout field offset). Definitionally equal to
`annealCopyReturnLM4_1` whenever `isPtrScalarPairReturnPlace returnPlace = false`. -/
def annealCopyReturnEp2
    (retOp : Miri.Interpreter.Operand AnnealProv)
    (returnPlace : Miri.Interpreter.RuntimeStackPlace AnnealProv)
    (state : AnnealStepState) :
    Miri.Interpreter.StepResult AnnealStepState Unit :=
  if isPtrScalarPairReturnPlace returnPlace then
    match retOp, returnPlace, state.stack.currentFrame? with
    | .indirect srcMp, .frameLocal _ _ none retLay _, none =>
      match srcMp.ptr.provenance, retLay.layout.fields, retLay.layout.backendRepr with
      | some (.concrete aid _), .Arbitrary offs _, .ScalarPair (a := a) (b := b) =>
        match state.machine.memory.live.toList.find? (fun e => e.1 == aid), offs[0]?, offs[1]? with
        | some (_, liveAlloc), some off0, some off1 =>
          let szA := (a.size annealRuntimeDataLayout).toOption.getD Miri.ABI.Size.ZERO
          let szB := (b.size annealRuntimeDataLayout).toOption.getD Miri.ABI.Size.ZERO
          match liveAlloc.allocation.readScalar annealTargetDataLayout (Miri.Memory.allocRange off0 szA) false,
                liveAlloc.allocation.readScalar annealTargetDataLayout (Miri.Memory.allocRange off1 szB) true with
          | .ok _, .ok _ => (state, .ok ())
          | .error (.invalidUninitBytes _), _ | _, .error (.invalidUninitBytes _) =>
            (state, .error (.undefinedBehavior "read of uninitialized scalarPair field"))
          | _, _ => (state, .error (.undefinedBehavior "invalid indirect scalarPair return read"))
        | _, _, _ => annealCopyReturnLM4_1 retOp returnPlace state
      | _, _, _ => annealCopyReturnLM4_1 retOp returnPlace state
    | _, _, _ => annealCopyReturnLM4_1 retOp returnPlace state
  else
    annealCopyReturnLM4_1 retOp returnPlace state

/-- Conservative `StepHooks` overlay extending `annealStepHooksUnwindFnPtrClosure`
with Episode 2's `.WrapUnsafeBinder`, `.Aggregate (.RawPtr ..)`, `.Cast .Transmute`,
`annealCopyReturnEp2` (for indirect pointer-`ScalarPair` returns), and
`annealEvalDropOverlay` (parameterized by `treeBorrows : Bool`, enabling the vendored
Tree Borrows write-access check on memory-backed drops — the LeanMiri analogue of
MiniRust's `BasicMemory` vs. `TreeBorrowsMemory` split). -/
def annealStepHooksDropBinderSubtype (currentBody : CapturedMir)
    (treeBorrows : Bool := false)
    (callees : List CapturedMir := .nil)
    (poppedFrame : Miri.TreeBorrows.FrameState := {})
    (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealStepHooksUnwindFnPtrClosure currentBody callees poppedFrame fnPtrs
  let termHooksBase := annealTerminatorHooksLM4_1 currentBody callees poppedFrame fnPtrs
  let ctrlHooksEp2 :=
    { termHooksBase.toControlHooks with
      copyReturn := fun _ retOp returnPlace st => annealCopyReturnEp2 retOp returnPlace st }
  let termHooksEp2 :=
    { termHooksBase with
      toControlHooks := ctrlHooksEp2
      drop := fun _ place target unwind st =>
        annealEvalDropOverlay currentBody.localDecls currentBody.layouts treeBorrows
          place target unwind st }
  { base with
    assign := fun choice place rvalue state =>
      if isDropBinderSubtypeAssign currentBody.localDecls place rvalue then
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooksDropBinderSubtype currentBody fnPtrs) choice rvalue place)
          state
      else
        base.assign choice place rvalue state
    terminator := fun choice term state =>
      Miri.Interpreter.ControlFlow.evalTerminator termHooksEp2 choice term state }

/-- Canonical post-elaboration no-glue `Drop` hooks (`drop` is a pure jump
`ControlFlow.goToBlock target`, witnessing the exact phase boundary against
Anneal's deinitializing `TerminatorKind.drop`). -/
def canonNoGlueDropHooks (currentBody : CapturedMir) :
    Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealStepHooksUnwindFnPtrClosure currentBody
  let termHooks :=
    { annealTerminatorHooksLM4_1 currentBody with
      drop := fun _ _ target _ st => Miri.Interpreter.ControlFlow.goToBlock target st }
  { base with
    terminator := fun choice term state =>
      Miri.Interpreter.ControlFlow.evalTerminator termHooks choice term state }

/-- Syntactic predicate for statements untouched by the Episode 2 overlay. -/
def stmtFreeOfEp2Overlay (localDecls : List LocalDecl) (stmt : Miri.MIR.Statement) : Prop :=
  match stmt.kind with
  | .Assign place rvalue =>
      isDropBinderSubtypeAssign localDecls place rvalue = false
  | _ => True

/-- A terminator is untouched by the Episode 2 overlay in frame `frame` unless it
drops a memory-backed (`.indirect`) local of that frame (projected drops of
immediate locals, and drops in any `treeBorrows` mode, are all covered). -/
def termFreeOfEp2Overlay
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (term : Miri.MIR.Terminator) : Prop :=
  match term.kind with
  | .Drop place .. => ∀ mp lay?, frame.getLocal place.localId ≠ .ok ⟨.live (.indirect mp), lay?⟩
  | _ => True

private theorem returnFromCurrentFrame_congr_copyReturn
    (h : Miri.Interpreter.ControlHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.Operand AnnealProv))
    (cr1 cr2 : Unit → Miri.Interpreter.Operand AnnealProv →
      Miri.Interpreter.RuntimeStackPlace AnnealProv → AnnealStepState →
      Miri.Interpreter.StepResult AnnealStepState Unit)
    (choice : Unit) (state : AnnealStepState)
    (hcopy : ∀ val st1 st2 fr,
      h.returnOperand choice state = (st1, .ok val) →
      h.popFrame choice st1 = (st2, .ok fr) →
      cr1 choice val fr.returnPlace st2 = cr2 choice val fr.returnPlace st2) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame { h with copyReturn := cr1 } choice false state =
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame { h with copyReturn := cr2 } choice false state := by
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame
  dsimp only [Id.run]
  cases state.stack.currentFrame? with
  | none => rfl
  | some frame =>
    dsimp only
    cases frame.location with
    | unwinding _ => rfl
    | mir loc =>
      dsimp only
      cases frame.body.basicBlocks[loc.block]? with
      | none => rfl
      | some block =>
        dsimp only
        cases block.cleanup with
        | true => rfl
        | false =>
          cases hretOp : h.returnOperand choice state with
          | mk st1 res1 =>
            cases res1 with
            | error _ =>
              simp only [Id.run, pure, Pure.pure, bind, Bind.bind, bne, beq_self_eq_true,
                         Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.false_and, hretOp]
            | ok val =>
              cases hpop : h.popFrame choice st1 with
              | mk st2 res2 =>
                cases res2 with
                | error _ =>
                  simp only [Id.run, pure, Pure.pure, bind, Bind.bind, bne, beq_self_eq_true,
                             Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.false_and, hretOp, hpop]
                | ok fr =>
                  simp only [Id.run, pure, Pure.pure, bind, Bind.bind, bne, beq_self_eq_true,
                             Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
                             Bool.not_false, hretOp, hpop, hcopy val st1 st2 fr hretOp hpop]

private theorem annealReturnOperandLM4_1_fst_eq (decls : List LocalDecl) (lays : LayoutTable)
    (state : AnnealStepState) :
    (annealReturnOperandLM4_1 decls lays state).1 = state := by
  unfold annealReturnOperandLM4_1
  cases state.stack.currentFrame? with
  | none => rfl
  | some f =>
    dsimp only
    cases f.getLocal 0 with
    | error _ => rfl
    | ok ls =>
      dsimp only
      cases ls.value with
      | dead => rfl
      | live op =>
        cases op with
        | indirect _ => rfl
        | immediate imm =>
          cases imm with
          | scalar _ | scalarPair _ _ => rfl
          | uninit =>
            dsimp only
            cases lookupLocalDeclLayout decls lays 0 with
            | none => rfl
            | some lay =>
              dsimp only
              split
              · rfl
              · cases f.location with
                | unwinding _ => rfl
                | mir l =>
                  dsimp only
                  cases f.body.basicBlocks[l.block]? with
                  | none => rfl
                  | some b =>
                    dsimp only
                    split <;> rfl

private theorem annealPopFrameLM4_1_frame_eq (pf : Miri.TreeBorrows.FrameState)
    (state : AnnealStepState) (frame fr : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (st2 : AnnealStepState)
    (hcf : state.stack.currentFrame? = some frame)
    (hpop : annealPopFrameLM4_1 pf state = (st2, .ok fr)) :
    fr = frame := by
  unfold annealPopFrameLM4_1 at hpop
  unfold Miri.Interpreter.Stack.popFrame at hpop
  unfold Miri.Interpreter.Stack.currentFrame? at hcf
  rw [hcf] at hpop
  dsimp only [pure, Except.pure] at hpop
  injection hpop with _ hok
  injection hok with hfr
  exact hfr.symm

/-- **Conservative Extension Theorem (`step_ep2_overlay_eq_unwind_of_free`)**:
For EVERY `treeBorrows` mode: when the active frame is not returning an indirect
pointer-`ScalarPair` (`isPtrScalarPairReturnPlace frame.returnPlace = false`),
the body's statements avoid the new Episode 2 assignment arms
(`.WrapUnsafeBinder`, `.Aggregate (.RawPtr ..)`, `.Cast .Transmute`,
`.UnaryOp .PtrMetadata`), and its `.Drop` terminators only drop locals that are not
memory-backed in the active frame (whole or projected, any protector state),
`Miri.Interpreter.Step.step` under `annealStepHooksDropBinderSubtype` is
**identically equal** to `Miri.Interpreter.Step.step` under
`annealStepHooksUnwindFnPtrClosure`. -/
theorem step_ep2_overlay_eq_unwind_of_free {currentBody : CapturedMir}
    {callees : List CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState}
    {fnPtrs : List FnPtrEntry} {state : AnnealStepState} (choice : Unit)
    (hret : ∀ frame, state.stack.currentFrame? = some frame →
      isPtrScalarPairReturnPlace frame.returnPlace = false)
    (hfree : ∀ frame, state.stack.currentFrame? = some frame →
      (∀ bb ∈ frame.body.basicBlocks.toList,
        (∀ stmt ∈ bb.statements.toList, stmtFreeOfEp2Overlay currentBody.localDecls stmt) ∧
        termFreeOfEp2Overlay frame bb.terminator)) (treeBorrows : Bool) :
    Miri.Interpreter.Step.step
      (annealStepHooksDropBinderSubtype currentBody treeBorrows callees poppedFrame fnPtrs) choice state =
    Miri.Interpreter.Step.step
      (annealStepHooksUnwindFnPtrClosure currentBody callees poppedFrame fnPtrs) choice state := by
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
          have hs := hbbFree.1 stmt (hst_eq ▸ Array.getElem_mem_toList hlt_s)
          rcases stmt with ⟨si, kind⟩
          cases kind with
          | Assign place rvalue =>
            dsimp only [stmtFreeOfEp2Overlay] at hs
            have hUnw : isUnwindFnPtrClosureAssign currentBody.localDecls place rvalue = false := by
              unfold isDropBinderSubtypeAssign at hs
              cases hU : isUnwindFnPtrClosureAssign currentBody.localDecls place rvalue <;> simp [hU] at hs ⊢
            simp [Miri.Interpreter.Step.evalStatement, annealStepHooksDropBinderSubtype,
                  annealStepHooksUnwindFnPtrClosure, hs, hUnw]
          | SetDiscriminant _ _ | PlaceMention _ | StorageLive _ | StorageDead _
          | Intrinsic _ | ConstEvalCounter | FakeRead _ | AscribeUserType _ _
          | Coverage _ | Nop | BackwardIncompatibleDropHint _ _ =>
            rfl
        | none =>
          have ht := hbbFree.2
          rcases htk : bb.terminator with ⟨si, tkind⟩
          rw [htk] at ht
          cases tkind with
          | Drop place target unwind replace asyncDrop =>
            dsimp only [termFreeOfEp2Overlay] at ht
            dsimp only [annealStepHooksDropBinderSubtype, annealStepHooksUnwindFnPtrClosure,
                        annealStepHooksLM4_1, Miri.Interpreter.ControlFlow.evalTerminator, Id.run]
            cases asyncDrop with
            | some _ => rfl
            | none =>
              have hbt : (annealStepHooks currentBody.localDecls currentBody.layouts).beforeTerminator
                  choice state = (state, .ok ()) := rfl
              rw [hbt]
              dsimp only
              rw [annealEvalDropOverlay_eq_base_of_not_indirect _ _ _ _ _ _ _
                (fun fr hfr => by rw [hcf] at hfr; cases hfr; exact ht)]
              rfl
          | Return =>
            have hretF := hret frame hcf
            dsimp only [annealStepHooksDropBinderSubtype, annealStepHooksUnwindFnPtrClosure,
                        annealStepHooksLM4_1, Miri.Interpreter.ControlFlow.evalTerminator, Id.run]
            have hbt : (annealStepHooks currentBody.localDecls currentBody.layouts).beforeTerminator choice state = (state, .ok ()) := rfl
            rw [hbt]
            dsimp only
            let ch := (annealTerminatorHooksLM4_1 currentBody callees poppedFrame fnPtrs).toControlHooks
            have hcr :
                Miri.Interpreter.ControlFlow.returnFromCurrentFrame
                  { ch with copyReturn := fun _ retOp returnPlace st => annealCopyReturnEp2 retOp returnPlace st } choice false state =
                Miri.Interpreter.ControlFlow.returnFromCurrentFrame ch choice false state := by
              have hcr' := returnFromCurrentFrame_congr_copyReturn ch
                (fun _ retOp returnPlace st => annealCopyReturnEp2 retOp returnPlace st)
                ch.copyReturn choice state (by
                  intro val st1 st2 fr hro hpop
                  have hst1 : st1 = state := by
                    have h1 := annealReturnOperandLM4_1_fst_eq currentBody.localDecls currentBody.layouts state
                    change annealReturnOperandLM4_1 currentBody.localDecls currentBody.layouts state = (st1, .ok val) at hro
                    rw [hro] at h1; exact h1
                  subst st1
                  have hfr : fr = frame := annealPopFrameLM4_1_frame_eq poppedFrame state frame fr st2 hcf hpop
                  subst fr
                  dsimp only [annealCopyReturnEp2]
                  rw [hretF]
                  rfl)
              exact hcr'
            rw [hcr]
          | Goto _ _ | SwitchInt _ _ | UnwindResume | UnwindTerminate _
          | Unreachable | Call _ _ _ _ _ _ _ | TailCall _ _ _ | Assert _ _ _ _ _ | Yield _ _ _ _
          | CoroutineDrop | FalseEdge _ _ | FalseUnwind _ _ | InlineAsm _ =>
            rfl

/-! ## §2. Shared LeanMiri Execution & State Helpers -/

private def mkLmMiriState (body : CapturedMir) (retTy : Ty)
    (locs : Array (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout))
    (mach : AnnealMachine := AnnealMachine.empty)
    (miriBodyOverride : Option Miri.MIR.Body := none) : AnnealStepState :=
  { stack := { frames := #[{
      body := miriBodyOverride.getD (translateBody body),
      bodyIdentity := .ofCanonicalIndex 0,
      functionInstance := { kind := .Item 0, args := #[] },
      extra := (), returnContinuation := .stop false,
      returnPlace := .frameLocal 0 0 none (translateTyOverlay retTy body.layouts) (.ofAllocationToken 0),
      localsIdentity := .ofAllocationToken 0, locals := locs, vaList := #[],
      trackCallerArg := none, location := .mir ⟨0, 0⟩ }] },
    machine := mach }

private def lmScalarUInt (bits : Nat) (szBytes : UInt64) : Miri.Memory.Scalar AnnealProv :=
  match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 bits) (Miri.ABI.Size.ofBytes szBytes) with
  | .ok s => s
  | .error _ => Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨.ZERO, .wildcard⟩

private def lmAllocId (n : Nat) (hn : UInt64.ofNat n ≠ 0) : Miri.Memory.AllocId :=
  ⟨UInt64.ofNat n, hn⟩

private def lmAid1 : Miri.Memory.AllocId := lmAllocId 1 (by decide)
private def lmAid2 : Miri.Memory.AllocId := lmAllocId 2 (by decide)
private def lmAid5 : Miri.Memory.AllocId := lmAllocId 5 (by decide)

private def lmBase1 : UInt64 := 256
private def lmBase2 : UInt64 := 384
private def lmBase5 : UInt64 := 1024

private def lmPtrScalar (aid : Miri.Memory.AllocId) (base : UInt64) : Miri.Memory.Scalar AnnealProv :=
  Miri.Memory.Scalar.fromPointer annealTargetDataLayout
    ⟨Miri.ABI.Size.ofBytes base, .concrete aid .one⟩

private def lmAddrMachine (entries : Array Miri.Memory.AllocAddresses.BaseAddressEntry) : AnnealMachine :=
  { AnnealMachine.empty with
    addresses := { AnnealMachine.empty.addresses with baseAddr := entries } }

/-- Multi-step execution of unmodified vendored `Miri.Interpreter.Step.step` for up to
`fuel` steps, capturing either the return local value (`_0`) when the root frame pops
or the exact `Miri.Interpreter.StepError`. -/
def runMiriSteps (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv))
    (fuel : Nat) (st : AnnealStepState) :
    Except Miri.Interpreter.StepError (AnnealStepState × Option (Miri.Interpreter.LocalValue AnnealProv)) :=
  match fuel with
  | 0 => .error (.unsupported "out of fuel")
  | n + 1 =>
    let lastRet := st.stack.frames[0]?.bind (fun f => f.locals[0]?.map (·.value))
    let (st', res) := Miri.Interpreter.Step.step hooks () st
    match res with
    | .error e => .error e
    | .ok true =>
      if st'.stack.frames.isEmpty then .ok (st, lastRet)
      else runMiriSteps hooks n st'
    | .ok false => .ok (st', st'.stack.frames[0]?.bind (fun f => f.locals[0]?.map (·.value)))

/-! ## §3. Per-Variant Universal Laws & Concrete Witnesses (`V1`–`V8`) -/

/-- **V1 (`StatementKind.coverage`) & V2 (`StatementKind.backwardIncompatibleDropHint`)**:
Re-exports `UnwindSetDiscrAndFnPtrLM` universal simulations and witnesses exact lockstep
on `v1CoverageOkMir`, `v1CoverageUbMir`, `v2DropHintOkMir`, and `v2DropHintDeadReadUbMir`. -/
theorem lm_v1_v2_coverage_and_dropHint_witness :
    let u32Lay := some (translateTyOverlay u32MirTy emptyLayoutTable)
    let rawMutU32Lay := some (translateTyOverlay rawMutU32MirTy emptyLayoutTable)
    let m1Ok := mkLmMiriState v1CoverageOkMir u32MirTy #[⟨.live (.immediate .uninit), u32Lay⟩]
    let m1Ub := mkLmMiriState v1CoverageUbMir u32MirTy #[⟨.live (.immediate .uninit), u32Lay⟩]
    let m2Ok := mkLmMiriState v2DropHintOkMir u32MirTy #[⟨.live (.immediate .uninit), u32Lay⟩, ⟨.live (.immediate .uninit), rawMutU32Lay⟩]
    let m2Ub := mkLmMiriState v2DropHintDeadReadUbMir u32MirTy #[⟨.live (.immediate .uninit), u32Lay⟩, ⟨.live (.immediate .uninit), u32Lay⟩]
    (runMiriSteps (annealStepHooksDropBinderSubtype v1CoverageOkMir) 8 m1Ok).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 17 4))))) ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v1CoverageUbMir) 8 m1Ub).map (·.2) =
      .error (.undefinedBehavior "Unreachable") ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v2DropHintOkMir) 12 m2Ok).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 23 4))))) ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v2DropHintDeadReadUbMir) 8 m2Ub).map (·.2) =
      .error (.undefinedBehavior "read of dead local") := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

private def lmExtractOk {ε α : Type} : (r : Except ε α) → r.isOk = true → α
  | .ok a, _ => a
  | .error _, h => nomatch h

private def lmAlign4 : Miri.ABI.Align := ⟨2⟩
private def lmAlign8 : Miri.ABI.Align := ⟨3⟩

private def lmUninit4Alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (lmExtractOk
    (Miri.Memory.Allocation.tryNew (Prov := AnnealProv) (Miri.ABI.Size.ofBytes 4) lmAlign4 .Uninit
      (fun _ _ => some #[0, 0, 0, 0]))
    (by decide +kernel)).withExtra none

private def lmUninit8Alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (lmExtractOk
    (Miri.Memory.Allocation.tryNew (Prov := AnnealProv) (Miri.ABI.Size.ofBytes 8) lmAlign8 .Uninit
      (fun _ _ => some #[0, 0, 0, 0, 0, 0, 0, 0]))
    (by decide +kernel)).withExtra none

private def mkPairU32Alloc (a b : Nat) : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  let rawBytes : Array UInt8 :=
    #[UInt8.ofNat (a % 256), UInt8.ofNat ((a / 256) % 256), UInt8.ofNat ((a / 65536) % 256), UInt8.ofNat ((a / 16777216) % 256),
      UInt8.ofNat (b % 256), UInt8.ofNat ((b / 256) % 256), UInt8.ofNat ((b / 65536) % 256), UInt8.ofNat ((b / 16777216) % 256)]
  match Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) rawBytes lmAlign4 .Mut with
  | .ok al => al.withExtra none
  | .error _ => lmUninit4Alloc

/-- Helper building an indirect 8-byte `(u32, u32)` stack allocation `[a, b]` in
`AnnealMachine` for projected sub-place `TerminatorKind.drop` (`V3`). -/
private def mkPairU32IndirectState (body : CapturedMir) (a b : Nat) : AnnealStepState :=
  let pairLay : Miri.Interpreter.LocalLayout :=
    { ty := encodeTyIdOverlay pairU32MirTy,
      layout := {
        fields := .Arbitrary #[Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 4] #[0, 1],
        variants := .Single 0,
        backendRepr := .Memory (sized := true),
        largestNiche := none, uninhabited := false,
        align := ⟨lmAlign4⟩, size := Miri.ABI.Size.ofBytes 8,
        maxReprAlign := none, unadjustedAbiAlign := lmAlign4,
        reprC := false, randomizationSeed := 0 } }
  let alloc0 := mkPairU32Alloc a b
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with live := #[(lmAid1, ⟨.stack, alloc0⟩)] },
      addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨lmAid1, lmBase1⟩] },
      borrowTracker := none }
  let mp : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Miri.ABI.Size.ofBytes lmBase1, some (.concrete lmAid1 .one)⟩, .none, none⟩
  mkLmMiriState body u32MirTy
    #[⟨.live (.immediate .uninit), some (translateTyOverlay u32MirTy emptyLayoutTable)⟩,
      ⟨.live (.indirect mp), some pairLay⟩] mach

private def lmU32Alloc11 : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) #[11, 0, 0, 0] lmAlign4 .Mut with
  | .ok al => al.withExtra (some lmU32ChildTree)
  | .error _ => lmUninit4Alloc

/-- Initial Miri state in which `_1 : u32 = 11` is **memory-backed** at allocation
`lmAid1` (base `256`) carrying `lmU32ChildTree`, and is accessed through the root tag
`retagParentTag`. The borrow tracker's global protected-tag table protects the
child `retagChildTag` with a `StrongProtector` iff `childProtected` (mirroring
Trusted's protected `Unique` borrow entry on `_1` in `v3DropProtectedInitState` and
MiniRust's `Validate _ true`). Whether the drop conflicts is decided entirely by
vendored `BorrowTree.performBorrowAccessRange` on this data. -/
private def mkTbDropMiriState (body : CapturedMir) (childProtected : Bool) : AnnealStepState :=
  let u32Lay := some (translateTyOverlay u32MirTy emptyLayoutTable)
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with live := #[(lmAid1, ⟨.stack, lmU32Alloc11⟩)] },
      addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨lmAid1, lmBase1⟩] },
      borrowTracker := some
        { global := { protectedTags := (hooksForChildProtected childProtected).protectedTags },
          retagMode := .Default } }
  let mp : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Miri.ABI.Size.ofBytes lmBase1, some (.concrete lmAid1 retagParentTag)⟩, .none, none⟩
  mkLmMiriState body u32MirTy
    #[⟨.live (.immediate .uninit), u32Lay⟩, ⟨.live (.indirect mp), u32Lay⟩] mach

/-- **V3 (`TerminatorKind.drop`) Comprehensive Witness Suite**:
1. Whole-local drop -> returns `42`;
2. Projected sub-place drop `_1.0` on indirect `(u32, u32)` via vendored
   `Miri.Memory.Allocation.writeUninit`: reading surviving sibling `_1.1`
   returns `99`, while reading dropped `_1.0` faults UB (`uninitialized`)!
3. Dead-local drop -> UB (`drop of dead local`);
4. Data-driven Tree Borrows mode sensitivity on a memory-backed `_1` whose
   allocation's vendored borrow tree has a `Unique` child: with `treeBorrows = false`
   the drop returns `42` even when the child is protected; with `treeBorrows = true`
   it faults UB iff the child is protected in the vendored global protected-tag
   table (unprotected control returns `42`); and the in-memory deinitialization
   makes a post-drop read of `_1` UB;
5. Explicit post-elaboration no-glue phase boundary: deinit drop (`annealStepHooksDropBinderSubtype`)
   faults UB on reading `_1` after `drop(_1)` (matching Trusted), whereas
   canonical no-glue `canonNoGlueDropHooks` returns `11`! -/
theorem lm_v3_drop_comprehensive_witness :
    let u32Lay := some (translateTyOverlay u32MirTy emptyLayoutTable)
    let mWhole := mkLmMiriState v3DropWholeOkMir u32MirTy
      #[⟨.live (.immediate .uninit), u32Lay⟩, ⟨.live (.immediate (.scalar (lmScalarUInt 11 4))), u32Lay⟩]
    let mDead := mkLmMiriState v3DropDeadUbMir u32MirTy
      #[⟨.live (.immediate .uninit), u32Lay⟩, ⟨.live (.immediate (.scalar (lmScalarUInt 11 4))), u32Lay⟩]
    let mPost := mkLmMiriState v3DropPostReadMir u32MirTy
      #[⟨.live (.immediate .uninit), u32Lay⟩, ⟨.live (.immediate (.scalar (lmScalarUInt 11 4))), u32Lay⟩]
    let mProjOk := mkPairU32IndirectState v3DropProjSiblingOkMir 11 99
    let mProjUb := mkPairU32IndirectState v3DropProjReadDroppedUbMir 11 99
    -- 1. Whole-local drop
    (runMiriSteps (annealStepHooksDropBinderSubtype v3DropWholeOkMir false) 8 mWhole).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 42 4))))) ∧
    -- 2. Projected drop: sibling read returns 99, dropped field read faults UB
    (runMiriSteps (annealStepHooksDropBinderSubtype v3DropProjSiblingOkMir false) 8 mProjOk).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 99 4))))) ∧
    (match runMiriSteps (annealStepHooksDropBinderSubtype v3DropProjReadDroppedUbMir false) 8 mProjUb with
      | .error (.undefinedBehavior _) => true | _ => false) = true ∧
    -- 3. Dead-local drop UB
    (runMiriSteps (annealStepHooksDropBinderSubtype v3DropDeadUbMir false) 8 mDead).map (·.2) =
      .error (.undefinedBehavior "drop of dead local") ∧
    -- 4. Mode sensitivity decided by vendored Tree Borrows on the dropped allocation
    (runMiriSteps (annealStepHooksDropBinderSubtype v3DropProtectedMir false) 8
        (mkTbDropMiriState v3DropProtectedMir true)).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 42 4))))) ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v3DropProtectedMir true) 8
        (mkTbDropMiriState v3DropProtectedMir true)).map (·.2) =
      .error (.undefinedBehavior "Tree Borrows write conflict on drop") ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v3DropProtectedMir true) 8
        (mkTbDropMiriState v3DropProtectedMir false)).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 42 4))))) ∧
    (match runMiriSteps (annealStepHooksDropBinderSubtype v3DropPostReadMir true) 8
        (mkTbDropMiriState v3DropPostReadMir false) with
      | .error (.undefinedBehavior _) => true | _ => false) = true ∧
    -- 5. Phase boundary: deinit drop faults UB on post-drop read vs. canonical no-glue returns 11
    (runMiriSteps (annealStepHooksDropBinderSubtype v3DropPostReadMir false) 8 mPost).map (·.2) =
      .error (.undefinedBehavior "read of uninitialized local") ∧
    (runMiriSteps (canonNoGlueDropHooks v3DropPostReadMir) 8 mPost).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 11 4))))) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel⟩

/-- **End-to-end Tree Borrows persistence (B3)**: running the whole drop body
`v3DropProtectedMir` through vendored `Miri.Interpreter.Step.step` under
`treeBorrows = true` with an UNPROTECTED child returns `42`, and the state just before
the final return still holds `_1`'s allocation whose persisted vendored borrow tree
(stored by `ep2DeinitIndirect` via `Allocation.setExtra`) now rejects a write through
the child tag `retagChildTag` (disabled by the drop's foreign write), whereas the
initial tree accepted it. -/
theorem lm_v3_drop_tb_tree_persisted :
    ep2ProtectorConflict {} lmU32ChildTree retagChildTag Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4) = false ∧
    (match runMiriSteps (annealStepHooksDropBinderSubtype v3DropProtectedMir true) 8
        (mkTbDropMiriState v3DropProtectedMir false) with
      | .ok (st, some ret) =>
        decide (ret = .live (.immediate (.scalar (lmScalarUInt 42 4)))) &&
        (match st.machine.memory.live[0]? with
          | some (_, la) =>
            match la.allocation.extra with
            | some t => ep2ProtectorConflict {} t retagChildTag Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4)
            | none => false
          | none => false)
      | _ => false) = true := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- **V4 (`Rvalue.shallowInitBox`) Lowered Miri Body**: lowers `Rvalue.shallowInitBox op contentTy`
to `Miri.MIR.Rvalue.Cast .Transmute (translateOperand op) (encodeTyId boxU32MirTy)`
so unmodified vendored `Miri.Interpreter.Step.step` -> `Cast.cast .Transmute` preserves
pointer provenance without reading or writing the uninitialized pointee allocation. -/
def v4ShallowInitBoxLoweredMiriBody : Miri.MIR.Body :=
  let base := translateBody v4ShallowInitBoxOkMir
  { base with
    basicBlocks := #[{
      statements := #[{
        sourceInfo := defaultSourceInfo,
        kind := .Assign ⟨0, #[]⟩ (.Cast .Transmute (.Copy ⟨1, #[]⟩) (encodeTyId boxU32MirTy)) }],
      terminator := { sourceInfo := defaultSourceInfo, kind := .Return },
      cleanup := false }] }

/-- **V4 (`Rvalue.shallowInitBox`) Distinct Secondary Lowered Miri Body**: lowers
`v4ShallowInitBoxDistinctOkMir` (`*mut u32 → Box<u64>`) to `.Cast .Transmute` targeting
`boxU64MirTy` on an 8-byte uninitialized allocation (`lmAid5` at `1024`), producing a
genuinely distinct `okSecondary` outcome (`lmObsPtr5 ≠ lmObsPtr2`). -/
def v4ShallowInitBoxDistinctLoweredMiriBody : Miri.MIR.Body :=
  let base := translateBody v4ShallowInitBoxDistinctOkMir
  { base with
    basicBlocks := #[{
      statements := #[{
        sourceInfo := defaultSourceInfo,
        kind := .Assign ⟨0, #[]⟩ (.Cast .Transmute (.Copy ⟨1, #[]⟩) (encodeTyId boxU64MirTy)) }],
      terminator := { sourceInfo := defaultSourceInfo, kind := .Return },
      cleanup := false }] }

/-- **V4 (`Rvalue.shallowInitBox`) Base-Translation Boundary & Lowered Transmute Witness**:
1. Unmodified `translateRvalue (.shallowInitBox ..)` emits `untranslatableConstOperand`,
   causing unmodified `Miri.Interpreter.Step.step` under `annealStepHooksLM4_1` to report
   `StepError.unsupported` (honest pinned-rustc removal boundary);
2. Lowered `.Cast .Transmute` executes through unmodified `Miri.Interpreter.Step.step` ->
   `Cast.cast .Transmute`, preserving exact pointer provenance `lmAid2` without touching
   the completely uninitialized pointee allocation `lmAid2`;
3. Dead-local and uninitialized-operand UB equivalence against Trusted;
4. Trusted fail-closed `.unsupported` on non-raw-ptr (`u64`) and wrong-width (`sz = 4`) operands. -/
theorem lm_v4_shallowInitBox_boundary_and_lowered_witness :
    let mach : AnnealMachine :=
      { memory := { AnnealMachine.empty.memory with live := #[(lmAid2, ⟨.stack, lmUninit4Alloc⟩)] },
        addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨lmAid2, lmBase2⟩] },
        borrowTracker := none }
    let boxLay := some (translateTyOverlay boxU32MirTy emptyLayoutTable)
    let rawLay := some (translateTyOverlay rawMutU8MirTy emptyLayoutTable)
    let ptrSc := lmPtrScalar lmAid2 lmBase2
    let mBase := mkLmMiriState v4ShallowInitBoxOkMir boxU32MirTy
      #[⟨.live (.immediate .uninit), boxLay⟩, ⟨.live (.immediate (.scalar ptrSc)), rawLay⟩] mach
    let mLowOk := mkLmMiriState v4ShallowInitBoxOkMir boxU32MirTy
      #[⟨.live (.immediate .uninit), boxLay⟩, ⟨.live (.immediate (.scalar ptrSc)), rawLay⟩] mach
      (some v4ShallowInitBoxLoweredMiriBody)
    let mLowDead := mkLmMiriState v4ShallowInitBoxOkMir boxU32MirTy
      #[⟨.live (.immediate .uninit), boxLay⟩, ⟨.dead, rawLay⟩] mach
      (some v4ShallowInitBoxLoweredMiriBody)
    let mLowUninit := mkLmMiriState v4ShallowInitBoxOkMir boxU32MirTy
      #[⟨.live (.immediate .uninit), boxLay⟩, ⟨.live (.immediate .uninit), rawLay⟩] mach
      (some v4ShallowInitBoxLoweredMiriBody)
    -- 1. Honest base-translation boundary: unmodified translateRvalue -> StepError.unsupported
    (match (Miri.Interpreter.Step.step (annealStepHooksLM4_1 v4ShallowInitBoxOkMir) () mBase).2 with
      | .error (.unsupported _) => true | _ => false) = true ∧
    -- 2. Lowered .Cast .Transmute preserves pointer provenance without reading/writing uninit pointee
    (runMiriSteps (annealStepHooksDropBinderSubtype v4ShallowInitBoxOkMir) 8 mLowOk).map (·.2) =
      .ok (some (.live (.immediate (.scalar ptrSc)))) ∧
    -- 3. Dead & uninit operand UB equivalence
    (runMiriSteps (annealStepHooksDropBinderSubtype v4ShallowInitBoxOkMir) 8 mLowDead).map (·.2) =
      .error (.undefinedBehavior "read of dead local") ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v4ShallowInitBoxOkMir) 8 mLowUninit).map (·.2) =
      .error (.undefinedBehavior "read of uninitialized local") ∧
    -- 4. Trusted fail-closed .unsupported on u64 / wrong width
    stepMirFn v4ShallowInitBoxNonPtrUnsupMir
      (initMachineState v4ShallowInitBoxNonPtrUnsupMir [.scalar ⟨384, 8⟩]) = .unsupported ∧
    stepMirFn v4ShallowInitBoxOkMir
      (initMachineState v4ShallowInitBoxOkMir [.ptr { allocId := 2, offsetBytes := 0 } 4]) = .unsupported := by
  refine ⟨by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, rfl, rfl⟩

/-- **V5 (`Rvalue.wrapUnsafeBinder`) Comprehensive Witness Suite**:
Exercises unmodified vendored `Miri.Interpreter.evalRvalueIntoPlace` `.WrapUnsafeBinder`
on:
1. Transparent `u32` wrap + `unwrapUnsafeBinder` round-trip (`73`);
2. Single-field `binderStructLayout?` wrapper struct `BinderU32` wrap + `unwrapUnsafeBinder` + `.field 0` (`73`);
3. Single-field `BinderNonZeroU8` (`7` succeeds, `0` faults UB);
4. Transparent `bool` target (`1` succeeds, `2` faults UB)! -/
theorem lm_v5_wrapUnsafeBinder_comprehensive_witness :
    let u32Lay := some (translateTyOverlay u32MirTy emptyLayoutTable)
    let u32BLay := some (translateTyOverlay u32MirTy ep2BinderLayouts)
    let bndU32Lay := some (translateTyOverlay binderU32MirTy ep2BinderLayouts)
    let bndNzLay := some (translateTyOverlay binderNzU8MirTy ep2BinderLayouts)
    let bndBoolLay := some (translateTyOverlay binderBoolMirTy ep2BinderLayouts)
    let u8BLay := some (translateTyOverlay u8MirTy ep2BinderLayouts)
    let mTrans := mkLmMiriState v5WrapTransparentRoundtripMir u32MirTy
      #[⟨.live (.immediate .uninit), u32Lay⟩,
        ⟨.live (.immediate (.scalar (lmScalarUInt 73 4))), u32Lay⟩,
        ⟨.dead, u32Lay⟩]
    let mStruct := mkLmMiriState v5WrapStructRoundtripMir u32MirTy
      #[⟨.live (.immediate .uninit), u32BLay⟩,
        ⟨.live (.immediate (.scalar (lmScalarUInt 73 4))), u32BLay⟩,
        ⟨.dead, bndU32Lay⟩]
    let mNz7 := mkLmMiriState v5WrapNzU8Mir binderNzU8MirTy
      #[⟨.live (.immediate .uninit), bndNzLay⟩,
        ⟨.live (.immediate (.scalar (lmScalarUInt 7 1))), u8BLay⟩]
    let mNz0 := mkLmMiriState v5WrapNzU8Mir binderNzU8MirTy
      #[⟨.live (.immediate .uninit), bndNzLay⟩,
        ⟨.live (.immediate (.scalar (lmScalarUInt 0 1))), u8BLay⟩]
    let mBool1 := mkLmMiriState v5WrapBoolMir binderBoolMirTy
      #[⟨.live (.immediate .uninit), bndBoolLay⟩,
        ⟨.live (.immediate (.scalar (lmScalarUInt 1 1))), u8BLay⟩]
    let mBool2 := mkLmMiriState v5WrapBoolMir binderBoolMirTy
      #[⟨.live (.immediate .uninit), bndBoolLay⟩,
        ⟨.live (.immediate (.scalar (lmScalarUInt 2 1))), u8BLay⟩]
    (runMiriSteps (annealStepHooksDropBinderSubtype v5WrapTransparentRoundtripMir) 8 mTrans).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 73 4))))) ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v5WrapStructRoundtripMir) 8 mStruct).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 73 4))))) ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v5WrapNzU8Mir) 8 mNz7).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 7 1))))) ∧
    (match runMiriSteps (annealStepHooksDropBinderSubtype v5WrapNzU8Mir) 8 mNz0 with
      | .error (.undefinedBehavior _) => true | _ => false) = true ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v5WrapBoolMir) 8 mBool1).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 1 1))))) ∧
    (match runMiriSteps (annealStepHooksDropBinderSubtype v5WrapBoolMir) 8 mBool2 with
      | .error (.undefinedBehavior _) => true | _ => false) = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **V6 (`CastKind.subtype`) Exact Definitional Identity with `CastKind.Transmute`**
in vendored `Miri.Interpreter.Cast.cast` AND concrete positive/UB witnesses! -/
theorem miri_cast_subtype_eq_transmute {Prov S C V : Type} [Miri.Memory.PointerProvenance Prov]
    (h : Miri.Interpreter.CastHooks Prov S C V) (choice : C) (fuel : Nat)
    (src : Miri.Interpreter.OpTy Prov) (ty : Miri.MIR.TyId) (dest : V) :
    Miri.Interpreter.Cast.cast h choice fuel src .Subtype ty dest =
    Miri.Interpreter.Cast.cast h choice fuel src .Transmute ty dest := by
  cases fuel <;> rfl

theorem lm_v6_castSubtype_comprehensive_witness :
    let u32Lay := some (translateTyOverlay u32MirTy emptyLayoutTable)
    let i32Lay := some (translateTyOverlay i32MirTy emptyLayoutTable)
    let u8Lay := some (translateTyOverlay u8MirTy emptyLayoutTable)
    let boolLay := some (translateTyOverlay boolMirTy emptyLayoutTable)
    let nzLay := some (translateTyOverlay nonZeroU8MirTy nonZeroU8Layouts)
    let u8NzLay := some (translateTyOverlay u8MirTy nonZeroU8Layouts)
    let mU32 := mkLmMiriState v6SubtypeU32ToI32Mir i32MirTy
      #[⟨.live (.immediate .uninit), i32Lay⟩,
        ⟨.live (.immediate (.scalar (lmScalarUInt 4294967295 4))), u32Lay⟩]
    let mNz7 := mkLmMiriState v6SubtypeU8ToNzMir nonZeroU8MirTy
      #[⟨.live (.immediate .uninit), nzLay⟩,
        ⟨.live (.immediate (.scalar (lmScalarUInt 7 1))), u8NzLay⟩]
    let mBool2 := mkLmMiriState v6SubtypeU8ToBoolMir boolMirTy
      #[⟨.live (.immediate .uninit), boolLay⟩,
        ⟨.live (.immediate (.scalar (lmScalarUInt 2 1))), u8Lay⟩]
    let mNz0 := mkLmMiriState v6SubtypeU8ToNzMir nonZeroU8MirTy
      #[⟨.live (.immediate .uninit), nzLay⟩,
        ⟨.live (.immediate (.scalar (lmScalarUInt 0 1))), u8NzLay⟩]
    (runMiriSteps (annealStepHooksDropBinderSubtype v6SubtypeU32ToI32Mir) 8 mU32).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 4294967295 4))))) ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v6SubtypeU8ToNzMir) 8 mNz7).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 7 1))))) ∧
    (match runMiriSteps (annealStepHooksDropBinderSubtype v6SubtypeU8ToBoolMir) 8 mBool2 with
      | .error (.undefinedBehavior _) => true | _ => false) = true ∧
    (match runMiriSteps (annealStepHooksDropBinderSubtype v6SubtypeU8ToNzMir) 8 mNz0 with
      | .error (.undefinedBehavior _) => true | _ => false) = true := by
  refine ⟨by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel⟩

/-- **V7 (`AggregateKind.rawPtr`) Comprehensive Witness Suite**:
Exercises unmodified vendored `Miri.Interpreter.writeAggregate` `.RawPtr` arm on:
1. Thin `*const u32` with `()` ZST metadata (`MemPlaceMeta.none` -> `.scalar` preserving `lmAid3`);
2. Wide `*const [u32]` with `usize` element-count `5` + `UnaryOp.PtrMetadata` round-trip (`5`);
3. Wide `*const str` with `usize` byte-count `5` + `UnaryOp.PtrMetadata` round-trip (`5`);
4. Dead data-pointer operand UB and uninitialized metadata operand UB! -/
theorem lm_v7_aggregateRawPtr_comprehensive_witness :
    let mach := lmAddrMachine #[⟨lmAid5, lmBase5⟩]
    let ptrSc := lmPtrScalar lmAid5 lmBase5
    let rawU32Lay := some (translateTyOverlay rawConstU32MirTy emptyLayoutTable)
    let rawUnitLay := some (translateTyOverlay rawConstUnitMirTy emptyLayoutTable)
    let unitLay := some (translateTyOverlay unitMirTy emptyLayoutTable)
    let usizeLay := some (translateTyOverlay usizeMirTy emptyLayoutTable)
    let wideSliceLay := some (translateTyOverlay rawConstSliceU32MirTy emptyLayoutTable)
    let wideStrLay := some (translateTyOverlay rawConstStrMirTy emptyLayoutTable)
    let mThinOk := mkLmMiriState v7RawPtrThinMir rawConstU32MirTy
      #[⟨.live (.immediate .uninit), rawU32Lay⟩,
        ⟨.live (.immediate (.scalar ptrSc)), rawUnitLay⟩,
        ⟨.live (.immediate .uninit), unitLay⟩] mach
    let mWideSliceOk := mkLmMiriState v7RawPtrWideSliceMetaMir usizeMirTy
      #[⟨.live (.immediate .uninit), usizeLay⟩,
        ⟨.live (.immediate (.scalar ptrSc)), rawUnitLay⟩,
        ⟨.live (.immediate (.scalar (lmScalarUInt 5 8))), usizeLay⟩,
        ⟨.dead, wideSliceLay⟩] mach
    let mWideStrOk := mkLmMiriState v7RawPtrWideStrMetaMir usizeMirTy
      #[⟨.live (.immediate .uninit), usizeLay⟩,
        ⟨.live (.immediate (.scalar ptrSc)), rawUnitLay⟩,
        ⟨.live (.immediate (.scalar (lmScalarUInt 5 8))), usizeLay⟩,
        ⟨.dead, wideStrLay⟩] mach
    let mThinDead := mkLmMiriState v7RawPtrThinMir rawConstU32MirTy
      #[⟨.live (.immediate .uninit), rawU32Lay⟩,
        ⟨.dead, rawUnitLay⟩,
        ⟨.live (.immediate .uninit), unitLay⟩] mach
    let mWideMetaUninit := mkLmMiriState v7RawPtrWideSliceMetaMir usizeMirTy
      #[⟨.live (.immediate .uninit), usizeLay⟩,
        ⟨.live (.immediate (.scalar ptrSc)), rawUnitLay⟩,
        ⟨.live (.immediate .uninit), usizeLay⟩,
        ⟨.dead, wideSliceLay⟩] mach
    (runMiriSteps (annealStepHooksDropBinderSubtype v7RawPtrThinMir) 8 mThinOk).map (·.2) =
      .ok (some (.live (.immediate (.scalar ptrSc)))) ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v7RawPtrWideSliceMetaMir) 8 mWideSliceOk).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 5 8))))) ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v7RawPtrWideStrMetaMir) 8 mWideStrOk).map (·.2) =
      .ok (some (.live (.immediate (.scalar (lmScalarUInt 5 8))))) ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v7RawPtrThinMir) 8 mThinDead).map (·.2) =
      .error (.undefinedBehavior "read of dead local") ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v7RawPtrWideSliceMetaMir) 8 mWideMetaUninit).map (·.2) =
      .error (.undefinedBehavior "read of uninitialized local") := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel⟩

/-- **V8 (`AggregateKind.closure`) Comprehensive Witness Suite**:
0-capture ZST closure, 2-capture `(u32, *const u32)` closure, dead upvar UB, and
uninitialized upvar UB executed through vendored `Miri.Interpreter.Step.step`! -/
private def lmUninit16Alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (lmExtractOk
    (Miri.Memory.Allocation.tryNew (Prov := AnnealProv) (Miri.ABI.Size.ofBytes 16) Miri.ABI.Align.EIGHT .Uninit
      (fun _ _ => some #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))
    (by decide +kernel)).withExtra none

private def mkV8ClosureCapState (u32Val : Miri.Interpreter.LocalValue AnnealProv) : AnnealStepState :=
  let ptrSc := lmPtrScalar lmAid1 lmBase1
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with live := #[(lmAid2, ⟨.stack, lmUninit16Alloc⟩)] },
      addresses := { AnnealMachine.empty.addresses with
        baseAddr := #[⟨lmAid2, lmBase2⟩, ⟨lmAid1, lmBase1⟩] },
      borrowTracker := none }
  let mp0 : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Miri.ABI.Size.ofBytes lmBase2, some (.concrete lmAid2 .one)⟩, .none, none⟩
  let capLay := some (translateTyOverlay v8ClosureCapMirTy ep2ClosureCapLayouts)
  let u32Lay := some (translateTyOverlay u32MirTy ep2ClosureCapLayouts)
  let rawU32Lay := some (translateTyOverlay rawConstU32MirTy ep2ClosureCapLayouts)
  mkLmMiriState v8ClosureCapMir v8ClosureCapMirTy
    #[⟨.live (.indirect mp0), capLay⟩,
      ⟨u32Val, u32Lay⟩,
      ⟨.live (.immediate (.scalar ptrSc)), rawU32Lay⟩] mach

private def readIndirectPairU32Ptr (st : AnnealStepState) (mp : Miri.Interpreter.MemPlace AnnealProv) :
    Option (Miri.Memory.Scalar AnnealProv × Miri.Memory.Scalar AnnealProv) :=
  match mp.ptr.provenance with
  | some (.concrete aid _) =>
    match st.machine.memory.live.toList.find? (fun e => e.1 == aid) with
    | some (_, liveAlloc) =>
      match liveAlloc.allocation.readScalar annealTargetDataLayout
              (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4)) false,
            liveAlloc.allocation.readScalar annealTargetDataLayout
              (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 8) (Miri.ABI.Size.ofBytes 8)) true with
      | .ok s0, .ok s1 => some (s0, s1)
      | _, _ => none
    | none => none
  | _ => none

private def lmMsc7 : Miri.Memory.ScalarInt :=
  (lmExtractOk
    (Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofNat 128 7) (Miri.ABI.Size.ofBytes 4))
    (by decide +kernel)).1

private theorem lmScalarUInt_7_eq_fromScalarInt :
    lmScalarUInt 7 4 = Miri.Memory.Scalar.fromScalarInt lmMsc7 := by
  decide +kernel

private theorem runMiriSteps_v8ClosureCap_ok (treeBorrows : Bool) :
    let mCapOk := mkV8ClosureCapState (.live (.immediate (.scalar (lmScalarUInt 7 4))))
    (match runMiriSteps (annealStepHooksDropBinderSubtype v8ClosureCapMir treeBorrows) 8 mCapOk with
      | .ok (st', some (.live (.indirect mp))) => readIndirectPairU32Ptr st' mp
      | _ => none) = some (lmScalarUInt 7 4, lmPtrScalar lmAid1 lmBase1) := by
  intro mCapOk
  let hooks := annealStepHooksDropBinderSubtype v8ClosureCapMir treeBorrows
  let mach : AnnealMachine :=
    { memory := { AnnealMachine.empty.memory with live := #[(lmAid2, ⟨.stack, lmUninit16Alloc⟩)] },
      addresses := { AnnealMachine.empty.addresses with
        baseAddr := #[⟨lmAid2, lmBase2⟩, ⟨lmAid1, lmBase1⟩] },
      borrowTracker := none }
  let mp0 : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Miri.ABI.Size.ofBytes lmBase2, some (.concrete lmAid2 .one)⟩, .none, none⟩
  let sCap0 : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 0,
                 locals := [.uninit, .init (.scalar ⟨7, 4⟩), .init (.ptr ⟨1, 0⟩ 8)] },
      memory := emptyMemory }
  let f0Lay :=
    (lmExtractOk
      (annealProjectFieldPlace ep2ClosureCapLayouts none
        ⟨.local 0 0 none (.ofAllocationToken 0), translateTy v8ClosureCapMirTy ep2ClosureCapLayouts⟩ 0)
      (by decide +kernel)).layout
  let f1Lay :=
    (lmExtractOk
      (annealProjectFieldPlace ep2ClosureCapLayouts none
        ⟨.local 0 0 none (.ofAllocationToken 0), translateTy v8ClosureCapMirTy ep2ClosureCapLayouts⟩ 1)
      (by decide +kernel)).layout
  have hstep_sim :=
    step_aggregate_closure_twoCapture_simulation
      (body := v8ClosureCapMir) (s := sCap0) (m := mCapOk)
      (dstIdx := 0) (op0Idx := 1) (op1Idx := 2)
      (f0Lay := f0Lay) (f1Lay := f1Lay)
      (mpDst := mp0) (allocId := lmAid2) (tagDst := .one) (baseDst := lmBase2)
      (alloc0 := lmUninit16Alloc) (words0 := initWordsFalse (Miri.ABI.Size.ofBytes 16))
      (uIdx := 0) (sc0 := ⟨7, 4⟩) (msc0 := lmMsc7)
      (ptr1 := ⟨1, 0⟩) (mptr1 := ⟨Miri.ABI.Size.ofBytes lmBase1, .concrete lmAid1 .one⟩)
      rfl rfl rfl (fun _ h => by cases h) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun _ _ h => by cases h) (fun _ h => by cases h)
      (by decide +kernel) (by decide +kernel)
      ⟨by decide +kernel, by decide +kernel⟩ ⟨by decide +kernel, by decide +kernel⟩
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      rfl (fun h => by cases h) rfl rfl
      ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, by decide +kernel, by decide +kernel⟩
      rfl rfl (by simp [mCapOk, mkV8ClosureCapState, mkLmMiriState, lmScalarUInt_7_eq_fromScalarInt]; rfl) rfl
      (fun _ h => Option.some.inj h.symm)
      (fun _ h => Option.some.inj h.symm)
      (fun _ h => Option.some.inj h.symm)
      rfl (by decide +kernel) rfl (by decide) (by decide) (by decide +kernel) rfl
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by rw [show lmUninit16Alloc.initializationMask = Miri.Memory.InitMask.new (Miri.ABI.Size.ofBytes 16) false from by decide +kernel]; exact initMaskWordRel_new_false)
      (by decide +kernel)
  obtain ⟨_, tf', alloc2, _, _, _, _, _, _, _, hm_step, hm_body, hm_sz, hm_loc,
          _, _, hm_l0, _, _, _, _, _, hm_r0, hm_r1⟩ := hstep_sim
  dsimp only [sCap0, Option.getD] at hm_body hm_loc
  have hstep1_eq : Miri.Interpreter.Step.step hooks () mCapOk =
      ({ stack := ⟨#[tf']⟩, machine := updateAllocMachine mach 0 lmAid2 .stack alloc2 }, .ok true) := by
    have hsame : Miri.Interpreter.Step.step hooks () mCapOk =
        Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure v8ClosureCapMir) () mCapOk := by
      cases treeBorrows <;> rfl
    rw [hsame]
    exact hm_step
  have htf_stack_eq :
      (Miri.Interpreter.Step.step hooks () mCapOk).1.stack.frames[0]?.map
        (fun f => (f.returnContinuation, f.returnPlace, f.locals.size)) =
      some (.stop false,
        .frameLocal 0 0 none (translateTyOverlay v8ClosureCapMirTy ep2ClosureCapLayouts) (.ofAllocationToken 0),
        3) := by
    cases treeBorrows <;> decide +kernel
  rw [hstep1_eq] at htf_stack_eq
  simp only [Array.getElem?_eq_getElem (show 0 < #[tf'].size from Nat.zero_lt_one),
             Array.getElem_singleton, Option.map_some] at htf_stack_eq
  injection htf_stack_eq with htuple
  have htf_rc : tf'.returnContinuation = .stop false := congrArg (fun t => t.1) htuple
  have htf_rp : tf'.returnPlace =
      .frameLocal 0 0 none (translateTyOverlay v8ClosureCapMirTy ep2ClosureCapLayouts) (.ofAllocationToken 0) :=
    congrArg (fun t => t.2.1) htuple
  have htf_l0_v : tf'.getLocal 0 = .ok ⟨.live (.indirect mp0), some (translateTy v8ClosureCapMirTy ep2ClosureCapLayouts)⟩ := by
    have hlt0 : 0 < tf'.locals.size := by rw [hm_sz]; decide
    have h0 : tf'.locals[0]'hlt0 = ⟨.live (.indirect mp0), some (translateTy v8ClosureCapMirTy ep2ClosureCapLayouts)⟩ :=
      Option.some.inj ((Array.getElem?_eq_getElem hlt0).symm.trans hm_l0)
    unfold Miri.Interpreter.Frame.getLocal
    simp only [hlt0, ↓reduceDIte, h0, pure, Except.pure]
  let st1 : AnnealStepState := { stack := ⟨#[tf']⟩, machine := updateAllocMachine mach 0 lmAid2 .stack alloc2 }
  have hlive_find : st1.machine.memory.live.toList.find? (fun e => e.1 == lmAid2) =
      some (lmAid2, ⟨.stack, alloc2⟩) := by
    dsimp only [st1, updateAllocMachine, mach]
    simp [Array.set, beq_self_eq_true]
  have hm_r0' : alloc2.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4)) false = .ok (lmScalarUInt 7 4) := by
    rw [lmScalarUInt_7_eq_fromScalarInt]; exact hm_r0
  have hstep2_eq :
      let (st2, res2) := Miri.Interpreter.Step.step hooks () st1
      res2 = .ok true ∧ st2.stack.frames.isEmpty = true := by
    cases hbb : (translateBody v8ClosureCapMir).basicBlocks[0]? with
    | none =>
      exfalso
      have hs : (translateBody v8ClosureCapMir).basicBlocks[0]?.isSome = true := by decide +kernel
      rw [hbb] at hs; cases hs
    | some blk =>
      have hst1_none : blk.statements[1]? = none := by
        have hs : ((translateBody v8ClosureCapMir).basicBlocks[0]?.bind (fun b => b.statements[1]?)).isNone = true := by
          decide +kernel
        rw [hbb] at hs
        exact Option.isNone_iff_eq_none.mp hs
      have hterm_ret : blk.terminator.kind = .Return := by
        have hs : (translateBody v8ClosureCapMir).basicBlocks[0]?.map (fun b => b.terminator.kind) = some .Return := by
          decide +kernel
        rw [hbb] at hs
        exact Option.some.inj hs
      have hcln : blk.cleanup = false := by
        have hs : (translateBody v8ClosureCapMir).basicBlocks[0]?.map (·.cleanup) = some false := by
          decide +kernel
        rw [hbb] at hs
        exact Option.some.inj hs
      have hstep2_body :
          Miri.Interpreter.Step.step hooks () st1 =
          (let r := Miri.Interpreter.ControlFlow.returnFromCurrentFrame
              { (annealTerminatorHooksLM4_1 v8ClosureCapMir).toControlHooks with
                copyReturn := fun _ retOp returnPlace st => annealCopyReturnEp2 retOp returnPlace st }
              () false st1
           match r.2 with
           | .ok () => (r.1, .ok true)
           | .error e => (r.1, .error e)) := by
        unfold Miri.Interpreter.Step.step
        have hcf1 : st1.stack.currentFrame? = some tf' := rfl
        rw [hcf1]
        dsimp only [Id.run]
        rw [hm_loc, hm_body]
        dsimp only
        rw [hbb]
        dsimp only
        rw [hst1_none]
        dsimp only
        rcases htm : blk.terminator with ⟨si, tk⟩
        rw [htm] at hterm_ret
        dsimp only at hterm_ret
        subst hterm_ret
        cases treeBorrows <;> (
          dsimp only [hooks, annealStepHooksDropBinderSubtype, annealStepHooksUnwindFnPtrClosure,
                      annealStepHooksLM4_1, annealStepHooks, Miri.Interpreter.ControlFlow.evalTerminator,
                      Id.run, pure, Pure.pure]
          cases Miri.Interpreter.ControlFlow.returnFromCurrentFrame
            { (annealTerminatorHooksLM4_1 v8ClosureCapMir).toControlHooks with
              copyReturn := fun _ retOp returnPlace st => annealCopyReturnEp2 retOp returnPlace st }
            () false st1 with
          | mk _ resR => cases resR <;> rfl)
      rw [hstep2_body]
      unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      have hcf1 : st1.stack.currentFrame? = some tf' := rfl
      rw [hcf1]
      dsimp only [Id.run]
      rw [hm_loc, hm_body]
      dsimp only
      rw [hbb]
      dsimp only
      have hretOp : annealReturnOperandLM4_1 v8ClosureCapMir.localDecls v8ClosureCapMir.layouts st1 =
          (st1, .ok (.indirect mp0)) := by
        unfold annealReturnOperandLM4_1
        rw [hcf1]
        dsimp only
        rw [htf_l0_v]
      have hpop : annealPopFrameLM4_1 {} st1 =
          ({ stack := ⟨#[]⟩, machine := st1.machine }, .ok tf') := rfl
      have hcopy : annealCopyReturnEp2 (.indirect mp0) tf'.returnPlace
          { stack := ⟨#[]⟩, machine := st1.machine } =
          ({ stack := ⟨#[]⟩, machine := st1.machine }, .ok ()) := by
        rw [htf_rp]
        unfold annealCopyReturnEp2
        have hisPtr : isPtrScalarPairReturnPlace
            (.frameLocal 0 0 none (translateTyOverlay v8ClosureCapMirTy ep2ClosureCapLayouts) (.ofAllocationToken 0)) = true := by
          decide +kernel
        rw [hisPtr]
        simp only [↓reduceIte, Miri.Interpreter.Stack.currentFrame?, Array.back?, Array.getElem?_empty, mp0]
        have hfields : (translateTyOverlay v8ClosureCapMirTy ep2ClosureCapLayouts).layout.fields =
            .Arbitrary #[Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 8] #[0, 1] := by decide +kernel
        have hrepr : (translateTyOverlay v8ClosureCapMirTy ep2ClosureCapLayouts).layout.backendRepr =
            .ScalarPair
              (a := .Initialized (value := .Int .I32 false) (validRange := ⟨0, 0xffffffff⟩))
              (b := .Initialized (value := .Pointer ⟨0⟩) (validRange := ⟨0, 0xffffffffffffffff⟩))
              (bOffset := Miri.ABI.Size.ofBytes 4) := by decide +kernel
        rw [hfields, hrepr]
        dsimp only
        rw [hlive_find,
            show (#[Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 8])[0]? = some Miri.ABI.Size.ZERO from rfl,
            show (#[Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 8])[1]? = some (Miri.ABI.Size.ofBytes 8) from rfl]
        dsimp only
        have hszA : ((Miri.ABI.Scalar.Initialized (value := .Int .I32 false) (validRange := ⟨0, 0xffffffff⟩)).size
            annealRuntimeDataLayout).toOption.getD Miri.ABI.Size.ZERO = Miri.ABI.Size.ofBytes 4 := by decide +kernel
        have hszB : ((Miri.ABI.Scalar.Initialized (value := .Pointer ⟨0⟩) (validRange := ⟨0, 0xffffffffffffffff⟩)).size
            annealRuntimeDataLayout).toOption.getD Miri.ABI.Size.ZERO = Miri.ABI.Size.ofBytes 8 := by decide +kernel
        rw [hszA, hszB, hm_r0', hm_r1]
      have hclean :
          Miri.Interpreter.Stack.cleanupStackFrame ⟨#[]⟩ st1.machine.memory
            (annealStackLifecycleHooksLM4_1 v8ClosureCapMir.localDecls v8ClosureCapMir.layouts)
            false tf' = ⟨⟨#[]⟩, st1.machine.memory, .ok .noCleanup⟩ := by
        unfold Miri.Interpreter.Stack.cleanupStackFrame
        rw [htf_rc]
        rfl
      dsimp only [annealTerminatorHooksLM4_1, annealControlHooksLM4_1]
      simp only [hcln, bne, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                 Bool.false_and, Bool.not_false, hretOp, hpop, hcopy, hclean,
                 Array.isEmpty_empty, Bool.or_false,
                 pure, Pure.pure, bind, Bind.bind, and_self]
  show (match runMiriSteps hooks 8 mCapOk with
        | .ok (st', some (.live (.indirect mp))) => readIndirectPairU32Ptr st' mp
        | _ => none) = _
  unfold runMiriSteps
  rw [hstep1_eq]
  have hne1 : (#[tf']).isEmpty = false := by simp
  simp only [hne1, Bool.false_eq_true, ↓reduceIte]
  unfold runMiriSteps
  cases hs2 : Miri.Interpreter.Step.step hooks () st1 with
  | mk st2 res2 =>
    rw [hs2] at hstep2_eq
    rcases hstep2_eq with ⟨hres2, hemp2⟩
    subst hres2
    have hret_st1 : st1.stack.frames[0]?.bind (fun f => f.locals[0]?.map (·.value)) =
        some (.live (.indirect mp0)) := by
      dsimp only [st1]
      simp [hm_l0]
    dsimp only
    simp only [hemp2, ↓reduceIte]
    rw [show ({ stack := { frames := #[tf'] },
                machine := updateAllocMachine mach 0 lmAid2 .stack alloc2 } : AnnealStepState).stack.frames[0]?.bind
              (fun f => f.locals[0]?.map (·.value)) =
            some (.live (.indirect mp0)) from hret_st1]
    dsimp only [readIndirectPairU32Ptr, mp0]
    rw [show ({ stack := { frames := #[tf'] },
                machine := updateAllocMachine mach 0 lmAid2 .stack alloc2 } : AnnealStepState).machine.memory.live.toList.find?
              (fun e => e.1 == lmAid2) =
            some (lmAid2, ⟨.stack, alloc2⟩) from hlive_find]
    dsimp only
    rw [hm_r0', hm_r1]
    rfl

theorem lm_v8_aggregateClosure_comprehensive_witness :
    let mach := lmAddrMachine #[⟨lmAid1, lmBase1⟩]
    let ptrSc := lmPtrScalar lmAid1 lmBase1
    let zstLay := some ({ ty := encodeTyIdOverlay (closureZstMirTy "ep2::zst"),
                          layout := zstLayoutData } : Miri.Interpreter.LocalLayout)
    let mZst := mkLmMiriState v8ClosureZstMir (closureZstMirTy "ep2::zst")
      #[⟨.live (.immediate .uninit), zstLay⟩] mach
    let mCapOk := mkV8ClosureCapState (.live (.immediate (.scalar (lmScalarUInt 7 4))))
    let mCapDead := mkV8ClosureCapState .dead
    let mCapUninit := mkV8ClosureCapState (.live (.immediate .uninit))
    (runMiriSteps (annealStepHooksDropBinderSubtype v8ClosureZstMir) 8 mZst).map (·.2) =
      .ok (some (.live (.immediate .uninit))) ∧
    (match runMiriSteps (annealStepHooksDropBinderSubtype v8ClosureCapMir) 8 mCapOk with
      | .ok (st', some (.live (.indirect mp))) => readIndirectPairU32Ptr st' mp
      | _ => none) = some (lmScalarUInt 7 4, ptrSc) ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v8ClosureCapMir) 8 mCapDead).map (·.2) =
      .error (.undefinedBehavior "read of dead local") ∧
    (runMiriSteps (annealStepHooksDropBinderSubtype v8ClosureCapMir) 8 mCapUninit).map (·.2) =
      .error (.undefinedBehavior "read of uninitialized local") := by
  refine ⟨by decide +kernel, runMiriSteps_v8ClosureCap_ok false,
          by decide +kernel, by decide +kernel⟩

/-! ## §3b. Universal Trusted ↔ Vendored LeanMiri Step & Lowering Theorems (`V1`–`V8`) -/

/-- **V1 & V2 Universal Simulation under `annealStepHooksDropBinderSubtype`**:
for EVERY `CapturedMir` body, `treeBorrows : Bool`, `StateRel`-coupled state `(s, m)`,
`StatementKind.coverage` and `StatementKind.backwardIncompatibleDropHint` step in
lockstep between Trusted `stepMirFn` and vendored `Miri.Interpreter.Step.step` under
`annealStepHooksDropBinderSubtype`. -/
theorem lm_v1_v2_overlay_universal_sim {body : CapturedMir} (treeBorrows : Bool)
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m) (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) :
    (stmt.kind = .coverage →
      StepRel body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksDropBinderSubtype body treeBorrows) () m)) ∧
    (∀ place, stmt.kind = .backwardIncompatibleDropHint place →
      StepRel body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksDropBinderSubtype body treeBorrows) () m)) :=
  ⟨fun hk => step_coverage_simulation (annealStepHooksDropBinderSubtype body treeBorrows) hstate hphase hbb hstmt hk,
   fun place hk => step_backwardIncompatibleDropHint_simulation (annealStepHooksDropBinderSubtype body treeBorrows) hstate hphase place hbb hstmt hk⟩

/-- **V3 Universal Dead-Local `TerminatorKind.drop` UB Equivalence under `annealEvalDropOverlay`**:
for EVERY `decls`, `layouts`, `treeBorrows : Bool`, `place`, `target`, `unwind`, and
`state` whose active frame maps `place.localId` to `.dead`, `annealEvalDropOverlay`
faults with `.undefinedBehavior "drop of dead local"` (matching Trusted `evalTerminator`). -/
theorem lm_v3_drop_dead_ub_overlay_universal (decls : List LocalDecl) (layouts : LayoutTable)
    (treeBorrows : Bool) (place : Miri.MIR.Place) (target : Miri.MIR.BasicBlockId)
    (unwind : Miri.MIR.UnwindAction) (state : AnnealStepState)
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (lay? : Option Miri.Interpreter.LocalLayout)
    (hcf : state.stack.currentFrame? = some frame)
    (hdead : frame.getLocal place.localId = .ok ⟨.dead, lay?⟩) :
    annealEvalDropOverlay decls layouts treeBorrows place target unwind state =
      (state, .error (.undefinedBehavior "drop of dead local")) := by
  unfold annealEvalDropOverlay annealEvalDropLM4_1
  simp only [hcf, hdead, ite_self]

private theorem resolveTyWithLocalDecls_kind_lm (decls : List LocalDecl)
    (layouts : LayoutTable) (ty : Ty) :
    (resolveTyWithLocalDecls decls layouts ty).kind = ty.kind := by
  unfold resolveTyWithLocalDecls
  split
  · rfl
  · split
    · rfl
    · split
      · split <;> rfl
      · rfl

private theorem lookup_emptyLayoutTable_lm (k : Nat) :
    LayoutTable.lookup emptyLayoutTable k = none := by
  cases k <;> rfl

/-- **V4 Trusted Lowering Justification (`trusted_shallowInitBox_eq_transmute_on_rawPtr`)**:
justifies LeanMiri's `.Cast .Transmute` lowering of `Rvalue.shallowInitBox` directly in
Trusted `MirSemantics.evalRvalue`! For EVERY `locals`, `op`, `mem`, `decls`, `aid`,
`contentTy`, `srcInt`, and `boxInt` (with zero redundant layout-resolution hypotheses!),
whenever `op` evaluates to a base pointer `{ allocId := aid, offsetBytes := 0 }` of width 8
and static raw-pointer type `*mut <srcInt>`, `evalRvalue ... (.shallowInitBox op contentTy)`
is IDENTICALLY EQUAL to `evalRvalue ... (.cast .transmute op (*mut <boxInt>))`! -/
theorem trusted_shallowInitBox_eq_transmute_on_rawPtr
    (locals locals' : List LocalSlot) (op : Operand) (mem : Memory)
    (decls : List LocalDecl) (contentTy : Ty) (srcInt boxInt : UintTy) (aid : Nat) :
    let srcTy : Ty := { kind := .rawPtr .mut (.uint srcInt), layoutIdx := 0 }
    let boxTy : Ty := { kind := .rawPtr .mut (.uint boxInt), layoutIdx := 0 }
    let p : ProvenancePtr := { allocId := aid, offsetBytes := 0 }
    evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls mem.callStack =
      .ok (.ptr p 8) locals' →
    evalUseRvalue locals op mem decls emptyLayoutTable = .ok (.ptr p 8) locals' mem →
    operandTy decls emptyLayoutTable op = some srcTy →
    evalRvalue locals (.shallowInitBox op contentTy) mem decls emptyLayoutTable =
      evalRvalue locals (.cast .transmute op boxTy) mem decls emptyLayoutTable := by
  intro srcTy boxTy p hOp hUse hSrcTy
  have hKind := resolveTyWithLocalDecls_kind_lm decls emptyLayoutTable
  have hRawSz : ∀ (u : UintTy) (k : Nat),
      tyByteSize decls emptyLayoutTable { kind := .rawPtr .mut (.uint u), layoutIdx := k } = some 8 := by
    intro u k
    unfold tyByteSize tyByteSizeAndAlignAux
    have hk : (resolveTyWithLocalDecls decls emptyLayoutTable { kind := .rawPtr .mut (.uint u), layoutIdx := k }).kind =
        .rawPtr .mut (.uint u) := hKind _
    cases hr : resolveTyWithLocalDecls decls emptyLayoutTable { kind := .rawPtr .mut (.uint u), layoutIdx := k } with
    | mk kd li =>
      rw [hr] at hk; dsimp only at hk; subst hk
      simp only [rigidTyByteSize, lookup_emptyLayoutTable_lm, layoutPointerBytes, emptyLayoutTable]
  have hShallow : evalRvalue locals (.shallowInitBox op contentTy) mem decls emptyLayoutTable =
      .ok (.ptr p 8) locals' mem := by
    show evalShallowInitBox locals op contentTy mem decls emptyLayoutTable = _
    unfold evalShallowInitBox
    simp only [hUse, hSrcTy, srcTy, layoutPointerBytes, emptyLayoutTable]
  have hTrans : evalRvalue locals (.cast .transmute op boxTy) mem decls emptyLayoutTable =
      .ok (.ptr p 8) locals' mem := by
    have hrBoxK : (resolveTyWithLocalDecls decls emptyLayoutTable boxTy).kind = .rawPtr .mut (.uint boxInt) := hKind boxTy
    have hrSrcK : (resolveTyWithLocalDecls decls emptyLayoutTable srcTy).kind = .rawPtr .mut (.uint srcInt) := hKind srcTy
    have hDstSz : tyByteSize decls emptyLayoutTable (resolveTyWithLocalDecls decls emptyLayoutTable boxTy) = some 8 := by
      cases hr : resolveTyWithLocalDecls decls emptyLayoutTable boxTy with
      | mk kd li => rw [hr] at hrBoxK; dsimp only at hrBoxK; subst hrBoxK; exact hRawSz boxInt li
    have hSrcTySz : tyByteSize decls emptyLayoutTable (resolveTyWithLocalDecls decls emptyLayoutTable srcTy) = some 8 := by
      cases hr : resolveTyWithLocalDecls decls emptyLayoutTable srcTy with
      | mk kd li => rw [hr] at hrSrcK; dsimp only at hrSrcK; subst hrSrcK; exact hRawSz srcInt li
    have hSrcSz : resolveByteCastSrcTyAndSize decls emptyLayoutTable op srcTy =
        some (resolveTyWithLocalDecls decls emptyLayoutTable srcTy, 8) := by
      unfold resolveByteCastSrcTyAndSize; dsimp only; rw [hSrcTySz]
    have hEnc : encodeByteCastSourceBytes emptyLayoutTable
        (resolveTyWithLocalDecls decls emptyLayoutTable srcTy) (.ptr p 8) =
        some (encodeLittleEndianBytes 0 8 (some (p.allocId, p.tag))) := by
      cases hr : resolveTyWithLocalDecls decls emptyLayoutTable srcTy with
      | mk kd li =>
        rw [hr] at hrSrcK; dsimp only at hrSrcK; subst hrSrcK
        unfold encodeByteCastSourceBytes encodeTypedValueToBytes normalizeCodecTy encodeValueToBytes
        simp only [lookup_emptyLayoutTable_lm]; rfl
    have hLen : length (encodeLittleEndianBytes 0 8 (some (p.allocId, p.tag))) = 8 := rfl
    have hDec : decodeTypedValueFromBytes defaultCodecFuel emptyLayoutTable
        (resolveTyWithLocalDecls decls emptyLayoutTable boxTy)
        (encodeLittleEndianBytes 0 8 (some (p.allocId, p.tag))) = some (.ptr p 8) := by
      cases hr : resolveTyWithLocalDecls decls emptyLayoutTable boxTy with
      | mk kd li =>
        rw [hr] at hrBoxK; dsimp only at hrBoxK; subst hrBoxK
        unfold decodeTypedValueFromBytes
        simp only [normalizeCodecTy, defaultCodecFuel, decodePtrBytesNoForge,
          encodeLittleEndianBytes, encodePtrBytes, encodePtrBytesAux,
          decodeLittleEndianBits, abstractBytesCoherentPtrProv?,
          abstractBytesCoherentPtrProvAux, layoutPointerBytes, emptyLayoutTable,
          normPtrByteOffset, length, Nat.beq_refl, Bool.true_and, Bool.and_true, Bool.and_self]
        rfl
    show evalByteCast locals op boxTy mem decls emptyLayoutTable = _
    unfold evalByteCast
    dsimp only
    rw [hOp]; dsimp only
    rw [hDstSz]; dsimp only
    rw [hSrcTy]; dsimp only
    rw [hSrcSz]; dsimp only
    rw [hEnc]; dsimp only
    rw [hLen]; dsimp only
    rw [hDec]
  rw [hShallow, hTrans]

/-- **V4 Base-Translator Removal Boundary (`lm_v4_base_translate_unsupported`)**:
unmodified `LeanMiriSpec.Translate.translateRvalue` maps EVERY `Rvalue.shallowInitBox`
to `.Use (.Constant (untranslatableConstOperand contentTy)) .No`, documenting the
pinned-rustc MIR removal boundary before lowering to `.Cast .Transmute`. -/
theorem lm_v4_base_translate_unsupported (op : Operand) (contentTy : Ty) :
    translateRvalue (.shallowInitBox op contentTy) =
      .Use (.Constant (untranslatableConstOperand contentTy)) .No := rfl

/-- **V5 Universal `Rvalue.WrapUnsafeBinder` Unfolding (`lm_v5_wrapUnsafeBinder_evalRvalue_universal`)**:
for EVERY `RvalueHooks`, `choice`, `operand`, `ty`, and `place`, unmodified vendored
`Miri.Interpreter.evalRvalueIntoPlace` evaluates `.WrapUnsafeBinder` strictly via
`evalPlace _ _ true`, `evalOperandAt`, and `copyOpAllowTransmute` (matching Trusted's
layout-preserving transmute + validity range check). -/
theorem lm_v5_wrapUnsafeBinder_evalRvalue_universal {P S C V : Type} [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.RvalueHooks P S C V) (choice : C)
    (operand : Miri.MIR.Operand) (ty : Miri.MIR.TyId) (place : Miri.MIR.Place) :
    Miri.Interpreter.evalRvalueIntoPlace h choice (.WrapUnsafeBinder operand ty) place =
      (do
        let dest ← h.evalPlace choice place true
        let op ← h.evalOperandAt choice (Miri.Interpreter.OperandPath.rvalue "operand") operand none
        h.copyOpAllowTransmute choice op dest) := rfl

/-- **V7 Universal `AggregateKind.RawPtr` Behavioral Step Law (`lm_v7_writeAggregate_rawPtr_universal`)**:
for EVERY `AggregateHooks`, `choice`, `pointee`, `mut_`, `dataOp`, `metaOp`, `dest`, and
state `st`, unmodified vendored `Miri.Interpreter.writeAggregate` on `.RawPtr` evaluates
`dataOp` -> `readPointer`, evaluates `metaOp` -> thin (`MemPlaceMeta.none` when
`isZst = true`) vs. wide (`.metadata (← readScalar ...)` when `isZst = false`),
constructs the pointer via `Immediate.newPointerWithMeta`, and commits via `copyOp`! -/
theorem lm_v7_writeAggregate_rawPtr_universal {P S C V : Type} [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.AggregateHooks P S C V) (choice : C)
    (pointee : Miri.MIR.TyId) (mut_ : Miri.MIR.Mutability)
    (dataOp metaOp : Miri.MIR.Operand) (dest : V) (st st1 st2 st3 st4 : S)
    (dOpTy mOpTy : Miri.Interpreter.OpTy P) (ptr : Miri.Memory.Pointer (Option P))
    (imm : Miri.Interpreter.Immediate P)
    (hEvalD : h.evalOperandAt choice (Miri.Interpreter.OperandPath.aggregate 0) dataOp none st = .ok dOpTy st1)
    (hReadP : h.readPointer choice dOpTy st1 = .ok ptr st2)
    (hEvalM : h.evalOperandAt choice (Miri.Interpreter.OperandPath.aggregate 1) metaOp none st2 = .ok mOpTy st3) :
    (mOpTy.layout.layout.isZst = true →
      Miri.Interpreter.Immediate.newPointerWithMeta ptr Miri.Interpreter.MemPlaceMeta.none h.target = .ok imm →
      Miri.Interpreter.writeAggregate h choice (.RawPtr pointee mut_) #[dataOp, metaOp] dest st =
        h.copyOp choice ⟨.immediate imm, h.placeLayout dest⟩ dest st3) ∧
    (∀ sc, mOpTy.layout.layout.isZst = false →
      h.readScalar choice mOpTy st3 = .ok sc st4 →
      Miri.Interpreter.Immediate.newPointerWithMeta ptr (.metadata sc) h.target = .ok imm →
      Miri.Interpreter.writeAggregate h choice (.RawPtr pointee mut_) #[dataOp, metaOp] dest st =
        h.copyOp choice ⟨.immediate imm, h.placeLayout dest⟩ dest st4) := by
  have hsz : ((#[dataOp, metaOp]).size != 2) = false := rfl
  have h0 : (#[dataOp, metaOp])[0]? = some dataOp := rfl
  have h1 : (#[dataOp, metaOp])[1]? = some metaOp := rfl
  refine ⟨?_, ?_⟩
  · intro hZst hNew
    unfold Miri.Interpreter.writeAggregate
    simp only [hsz, h0, h1, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure,
               hEvalD, hReadP, hEvalM, hZst, hNew]
    cases h.copyOp choice ⟨.immediate imm, h.placeLayout dest⟩ dest st3 with
    | ok u s => cases u; rfl
    | error e s => rfl
  · intro sc hNz hReadS hNew
    unfold Miri.Interpreter.writeAggregate
    simp only [hsz, h0, h1, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure,
               hEvalD, hReadP, hEvalM, hNz, hReadS, hNew]
    cases h.copyOp choice ⟨.immediate imm, h.placeLayout dest⟩ dest st4 with
    | ok u s => cases u; rfl
    | error e s => rfl

/-- **V8 Universal `AggregateKind.Closure` Overlay Simulation (`lm_v8_closure_overlay_universal`)**:
directly lifts `c10_closure_rvalue_and_writeAggregate_simulation` to Episode 2's
`annealRvalueHooksDropBinderSubtype`: Trusted `evalRvalue ... (.aggregate (.closure dp) ops)`
and vendored `Miri.Interpreter.writeAggregate` on `.Closure` coincide with `.Tuple` under
`annealAggregateHooksUnwindFnPtrClosure` and succeed on ZST closures. -/
theorem lm_v8_closure_overlay_universal (body : CapturedMir) (fnPtrs : List FnPtrEntry)
    (locals : List LocalSlot) (defPath : DefPath) (ops : List Operand) (mem : Memory)
    (defId : Miri.MIR.DefId) (args : Array Miri.MIR.GenericArg) (mops : Array Miri.MIR.Operand)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (st : AnnealStepState)
    (hfields : dest.layout.layout.fields = .Arbitrary #[] #[])
    (hmem : ∀ f l o id, dest.ref = .local f l o id →
      ∃ tf ov, st.stack.currentFrame? = some tf ∧ tf.getLocalOperand l = .ok ov) :
    (annealRvalueHooksDropBinderSubtype body fnPtrs).writeAggregate () (.Closure defId args) mops dest =
      Miri.Interpreter.writeAggregate (annealAggregateHooksUnwindFnPtrClosure body.localDecls body.layouts)
        () .Tuple mops dest ∧
    (annealRvalueHooksDropBinderSubtype body fnPtrs).writeAggregate () (.Closure defId args) #[] dest st =
      .ok () st := by
  have h := c10_closure_rvalue_and_writeAggregate_simulation locals defPath ops mem
    body.localDecls body.layouts defId args mops dest st hfields hmem
  dsimp only [annealRvalueHooksDropBinderSubtype, annealRvalueHooksUnwindFnPtrClosure]
  exact ⟨h.2.1, h.2.2⟩

/-! ## §4. Canonical Executable LeanMiri Corpus Observation (`ep2LmObserve`) -/

/-- Authority-typed LeanMiri observation produced directly by stepping unmodified
vendored `Miri.Interpreter.Step.step` (`runMiriSteps`), preserving exact vendored
`Miri.Interpreter.LocalValue AnnealProv` return values and distinguishing UB vs.
unsupported errors. -/
inductive Ep2LmObs : Type where
  | retVal (val : Miri.Interpreter.LocalValue AnnealProv)
  | ub
  | unsupported
  deriving DecidableEq

private def toLmObs (res : Except Miri.Interpreter.StepError
    (AnnealStepState × Option (Miri.Interpreter.LocalValue AnnealProv))) : Ep2LmObs :=
  match res with
  | .ok (st', some (.live (.indirect mp))) =>
    match readIndirectPairU32Ptr st' mp with
    | some (s0, s1) => .retVal (.live (.immediate (.scalarPair s0 s1)))
    | none => .retVal (.live (.indirect mp))
  | .ok (_, some v) => .retVal v
  | .error (.undefinedBehavior _) => .ub
  | _ => .unsupported

/-- Canonical return-value observations for `ObsAuthority.denote` in the cross-root
kernel bridge (pure vendored `Miri.Interpreter.LocalValue AnnealProv` values!). -/
def lmObsU32 (n : Nat) : Ep2LmObs := .retVal (.live (.immediate (.scalar (lmScalarUInt n 4))))
def lmObsU8 (n : Nat) : Ep2LmObs := .retVal (.live (.immediate (.scalar (lmScalarUInt n 1))))
def lmObsUsize (n : Nat) : Ep2LmObs := .retVal (.live (.immediate (.scalar (lmScalarUInt n 8))))
def lmObsPtr2 : Ep2LmObs := .retVal (.live (.immediate (.scalar (lmPtrScalar lmAid2 lmBase2))))
def lmObsPtr5 : Ep2LmObs := .retVal (.live (.immediate (.scalar (lmPtrScalar lmAid5 lmBase5))))
def lmObsZst : Ep2LmObs := .retVal (.live (.immediate .uninit))
def lmObsClosureCap7_1 : Ep2LmObs :=
  .retVal (.live (.immediate (.scalarPair (lmScalarUInt 7 4) (lmPtrScalar lmAid1 lmBase1))))

/-- Direct vendored `Miri.Interpreter.Step.step` observation for EVERY
`(treeBorrows, variantIdx, caseIdx)` key across all 8 Episode 2 MIR variants
(`variantIdx ∈ 0..7`, `caseIdx ∈ 0..3`). Zero shadow evaluators: every entry runs
`runMiriSteps` -> `Miri.Interpreter.Step.step`! -/
def ep2LmObserve (treeBorrows : Bool) (variantIdx : Nat) (caseIdx : Nat) : Ep2LmObs :=
  let u32Lay := some (translateTyOverlay u32MirTy emptyLayoutTable)
  let i32Lay := some (translateTyOverlay i32MirTy emptyLayoutTable)
  let u8Lay := some (translateTyOverlay u8MirTy emptyLayoutTable)
  let boolLay := some (translateTyOverlay boolMirTy emptyLayoutTable)
  let usizeLay := some (translateTyOverlay usizeMirTy emptyLayoutTable)
  let unitLay := some (translateTyOverlay unitMirTy emptyLayoutTable)
  let rawU32Lay := some (translateTyOverlay rawConstU32MirTy emptyLayoutTable)
  let rawUnitLay := some (translateTyOverlay rawConstUnitMirTy emptyLayoutTable)
  let wideSliceLay := some (translateTyOverlay rawConstSliceU32MirTy emptyLayoutTable)
  match variantIdx, caseIdx with
  -- 0: coverage
  | 0, 0 | 0, 1 | 0, 3 =>
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v1CoverageOkMir treeBorrows) 8
      (mkLmMiriState v1CoverageOkMir u32MirTy #[⟨.live (.immediate .uninit), u32Lay⟩])
  | 0, 2 =>
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v1CoverageUbMir treeBorrows) 8
      (mkLmMiriState v1CoverageUbMir u32MirTy #[⟨.live (.immediate .uninit), u32Lay⟩])
  -- 1: backwardIncompatibleDropHint
  | 1, 0 | 1, 1 | 1, 3 =>
    let rawMutU32Lay := some (translateTyOverlay rawMutU32MirTy emptyLayoutTable)
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v2DropHintOkMir treeBorrows) 12
      (mkLmMiriState v2DropHintOkMir u32MirTy #[⟨.live (.immediate .uninit), u32Lay⟩, ⟨.live (.immediate .uninit), rawMutU32Lay⟩])
  | 1, 2 =>
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v2DropHintDeadReadUbMir treeBorrows) 8
      (mkLmMiriState v2DropHintDeadReadUbMir u32MirTy #[⟨.live (.immediate .uninit), u32Lay⟩, ⟨.live (.immediate .uninit), u32Lay⟩])
  -- 2: dropTerminator (genuine treeBorrows sensitivity at caseIdx = 3!)
  | 2, 0 =>
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v3DropWholeOkMir treeBorrows) 8
      (mkLmMiriState v3DropWholeOkMir u32MirTy
        #[⟨.live (.immediate .uninit), u32Lay⟩, ⟨.live (.immediate (.scalar (lmScalarUInt 11 4))), u32Lay⟩])
  | 2, 1 =>
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v3DropProjSiblingOkMir treeBorrows) 8
      (mkPairU32IndirectState v3DropProjSiblingOkMir 11 99)
  | 2, 2 =>
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v3DropDeadUbMir treeBorrows) 8
      (mkLmMiriState v3DropDeadUbMir u32MirTy
        #[⟨.live (.immediate .uninit), u32Lay⟩, ⟨.live (.immediate (.scalar (lmScalarUInt 11 4))), u32Lay⟩])
  | 2, 3 =>
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v3DropProtectedMir treeBorrows) 8
      (mkTbDropMiriState v3DropProtectedMir true)
  -- 3: shallowInitBox (lowered .Cast .Transmute on uninit pointee allocation; distinct okPrimary vs. okSecondary!)
  | 3, 0 =>
    let mach : AnnealMachine :=
      { memory := { AnnealMachine.empty.memory with live := #[(lmAid2, ⟨.stack, lmUninit4Alloc⟩)] },
        addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨lmAid2, lmBase2⟩] },
        borrowTracker := none }
    let boxLay := some (translateTyOverlay boxU32MirTy emptyLayoutTable)
    let rawLay := some (translateTyOverlay rawMutU8MirTy emptyLayoutTable)
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v4ShallowInitBoxOkMir treeBorrows) 8
      (mkLmMiriState v4ShallowInitBoxOkMir boxU32MirTy
        #[⟨.live (.immediate .uninit), boxLay⟩,
          ⟨.live (.immediate (.scalar (lmPtrScalar lmAid2 lmBase2))), rawLay⟩]
        mach (some v4ShallowInitBoxLoweredMiriBody))
  | 3, 1 =>
    let mach : AnnealMachine :=
      { memory := { AnnealMachine.empty.memory with live := #[(lmAid5, ⟨.stack, lmUninit8Alloc⟩)] },
        addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨lmAid5, lmBase5⟩] },
        borrowTracker := none }
    let boxLay := some (translateTyOverlay boxU64MirTy emptyLayoutTable)
    let rawLay := some (translateTyOverlay rawMutU32MirTy emptyLayoutTable)
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v4ShallowInitBoxDistinctOkMir treeBorrows) 8
      (mkLmMiriState v4ShallowInitBoxDistinctOkMir boxU64MirTy
        #[⟨.live (.immediate .uninit), boxLay⟩,
          ⟨.live (.immediate (.scalar (lmPtrScalar lmAid5 lmBase5))), rawLay⟩]
        mach (some v4ShallowInitBoxDistinctLoweredMiriBody))
  | 3, 2 =>
    let boxLay := some (translateTyOverlay boxU32MirTy emptyLayoutTable)
    let rawLay := some (translateTyOverlay rawMutU8MirTy emptyLayoutTable)
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v4ShallowInitBoxOkMir treeBorrows) 8
      (mkLmMiriState v4ShallowInitBoxOkMir boxU32MirTy
        #[⟨.live (.immediate .uninit), boxLay⟩, ⟨.dead, rawLay⟩]
        AnnealMachine.empty (some v4ShallowInitBoxLoweredMiriBody))
  | 3, 3 =>
    let boxLay := some (translateTyOverlay boxU32MirTy emptyLayoutTable)
    let rawLay := some (translateTyOverlay rawMutU8MirTy emptyLayoutTable)
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v4ShallowInitBoxOkMir treeBorrows) 8
      (mkLmMiriState v4ShallowInitBoxOkMir boxU32MirTy
        #[⟨.live (.immediate .uninit), boxLay⟩, ⟨.live (.immediate .uninit), rawLay⟩]
        AnnealMachine.empty (some v4ShallowInitBoxLoweredMiriBody))
  -- 4: wrapUnsafeBinder
  | 4, 0 =>
    let u32BLay := some (translateTyOverlay u32MirTy ep2BinderLayouts)
    let bndU32Lay := some (translateTyOverlay binderU32MirTy ep2BinderLayouts)
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v5WrapStructRoundtripMir treeBorrows) 8
      (mkLmMiriState v5WrapStructRoundtripMir u32MirTy
        #[⟨.live (.immediate .uninit), u32BLay⟩,
          ⟨.live (.immediate (.scalar (lmScalarUInt 73 4))), u32BLay⟩,
          ⟨.dead, bndU32Lay⟩])
  | 4, 1 =>
    let bndNzLay := some (translateTyOverlay binderNzU8MirTy ep2BinderLayouts)
    let u8BLay := some (translateTyOverlay u8MirTy ep2BinderLayouts)
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v5WrapNzU8Mir treeBorrows) 8
      (mkLmMiriState v5WrapNzU8Mir binderNzU8MirTy
        #[⟨.live (.immediate .uninit), bndNzLay⟩,
          ⟨.live (.immediate (.scalar (lmScalarUInt 7 1))), u8BLay⟩])
  | 4, 2 =>
    let bndNzLay := some (translateTyOverlay binderNzU8MirTy ep2BinderLayouts)
    let u8BLay := some (translateTyOverlay u8MirTy ep2BinderLayouts)
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v5WrapNzU8Mir treeBorrows) 8
      (mkLmMiriState v5WrapNzU8Mir binderNzU8MirTy
        #[⟨.live (.immediate .uninit), bndNzLay⟩,
          ⟨.live (.immediate (.scalar (lmScalarUInt 0 1))), u8BLay⟩])
  | 4, 3 =>
    let bndBoolLay := some (translateTyOverlay binderBoolMirTy ep2BinderLayouts)
    let u8BLay := some (translateTyOverlay u8MirTy ep2BinderLayouts)
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v5WrapBoolMir treeBorrows) 8
      (mkLmMiriState v5WrapBoolMir binderBoolMirTy
        #[⟨.live (.immediate .uninit), bndBoolLay⟩,
          ⟨.live (.immediate (.scalar (lmScalarUInt 2 1))), u8BLay⟩])
  -- 5: castSubtype
  | 5, 0 =>
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v6SubtypeU32ToI32Mir treeBorrows) 8
      (mkLmMiriState v6SubtypeU32ToI32Mir i32MirTy
        #[⟨.live (.immediate .uninit), i32Lay⟩,
          ⟨.live (.immediate (.scalar (lmScalarUInt 4294967295 4))), u32Lay⟩])
  | 5, 1 =>
    let nzLay := some (translateTyOverlay nonZeroU8MirTy nonZeroU8Layouts)
    let u8NzLay := some (translateTyOverlay u8MirTy nonZeroU8Layouts)
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v6SubtypeU8ToNzMir treeBorrows) 8
      (mkLmMiriState v6SubtypeU8ToNzMir nonZeroU8MirTy
        #[⟨.live (.immediate .uninit), nzLay⟩,
          ⟨.live (.immediate (.scalar (lmScalarUInt 7 1))), u8NzLay⟩])
  | 5, 2 =>
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v6SubtypeU8ToBoolMir treeBorrows) 8
      (mkLmMiriState v6SubtypeU8ToBoolMir boolMirTy
        #[⟨.live (.immediate .uninit), boolLay⟩,
          ⟨.live (.immediate (.scalar (lmScalarUInt 2 1))), u8Lay⟩])
  | 5, 3 =>
    let nzLay := some (translateTyOverlay nonZeroU8MirTy nonZeroU8Layouts)
    let u8NzLay := some (translateTyOverlay u8MirTy nonZeroU8Layouts)
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v6SubtypeU8ToNzMir treeBorrows) 8
      (mkLmMiriState v6SubtypeU8ToNzMir nonZeroU8MirTy
        #[⟨.live (.immediate .uninit), nzLay⟩,
          ⟨.live (.immediate (.scalar (lmScalarUInt 0 1))), u8NzLay⟩])
  -- 6: aggregateRawPtr
  | 6, 0 =>
    let mach := lmAddrMachine #[⟨lmAid5, lmBase5⟩]
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v7RawPtrThinMir treeBorrows) 8
      (mkLmMiriState v7RawPtrThinMir rawConstU32MirTy
        #[⟨.live (.immediate .uninit), rawU32Lay⟩,
          ⟨.live (.immediate (.scalar (lmPtrScalar lmAid5 lmBase5))), rawUnitLay⟩,
          ⟨.live (.immediate .uninit), unitLay⟩] mach)
  | 6, 1 =>
    let mach := lmAddrMachine #[⟨lmAid5, lmBase5⟩]
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v7RawPtrWideSliceMetaMir treeBorrows) 8
      (mkLmMiriState v7RawPtrWideSliceMetaMir usizeMirTy
        #[⟨.live (.immediate .uninit), usizeLay⟩,
          ⟨.live (.immediate (.scalar (lmPtrScalar lmAid5 lmBase5))), rawUnitLay⟩,
          ⟨.live (.immediate (.scalar (lmScalarUInt 5 8))), usizeLay⟩,
          ⟨.dead, wideSliceLay⟩] mach)
  | 6, 2 =>
    let mach := lmAddrMachine #[⟨lmAid5, lmBase5⟩]
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v7RawPtrThinMir treeBorrows) 8
      (mkLmMiriState v7RawPtrThinMir rawConstU32MirTy
        #[⟨.live (.immediate .uninit), rawU32Lay⟩,
          ⟨.dead, rawUnitLay⟩,
          ⟨.live (.immediate .uninit), unitLay⟩] mach)
  | 6, 3 =>
    let mach := lmAddrMachine #[⟨lmAid5, lmBase5⟩]
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v7RawPtrWideSliceMetaMir treeBorrows) 8
      (mkLmMiriState v7RawPtrWideSliceMetaMir usizeMirTy
        #[⟨.live (.immediate .uninit), usizeLay⟩,
          ⟨.live (.immediate (.scalar (lmPtrScalar lmAid5 lmBase5))), rawUnitLay⟩,
          ⟨.live (.immediate .uninit), usizeLay⟩,
          ⟨.dead, wideSliceLay⟩] mach)
  -- 7: aggregateClosure
  | 7, 0 =>
    let mach := lmAddrMachine #[⟨lmAid1, lmBase1⟩]
    let zstLay := some ({ ty := encodeTyIdOverlay (closureZstMirTy "ep2::zst"),
                          layout := zstLayoutData } : Miri.Interpreter.LocalLayout)
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v8ClosureZstMir treeBorrows) 8
      (mkLmMiriState v8ClosureZstMir (closureZstMirTy "ep2::zst")
        #[⟨.live (.immediate .uninit), zstLay⟩] mach)
  | 7, 1 =>
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v8ClosureCapMir treeBorrows) 8
      (mkV8ClosureCapState (.live (.immediate (.scalar (lmScalarUInt 7 4)))))
  | 7, 2 =>
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v8ClosureCapMir treeBorrows) 8
      (mkV8ClosureCapState .dead)
  | 7, 3 =>
    toLmObs <| runMiriSteps (annealStepHooksDropBinderSubtype v8ClosureCapMir treeBorrows) 8
      (mkV8ClosureCapState (.live (.immediate .uninit)))
  | _, _ => .unsupported

/-- Mode sensitivity certified directly on `ep2LmObserve`: `dropTerminator.modeCase`
(`variantIdx = 2, caseIdx = 3`, memory-backed `_1` whose vendored borrow tree has a
protected `Unique` child) returns `42` with `treeBorrows = false` and faults `.ub`
with `treeBorrows = true` (vendored Tree Borrows write conflict). -/
theorem ep2LmObserve_drop_mode_sensitivity :
    ep2LmObserve false 2 3 = lmObsU32 42 ∧ ep2LmObserve true 2 3 = .ub :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- Exact symbolic reduction for the 2-capture `(u32, *const u32)` closure case
(`variantIdx = 7, caseIdx = 1`) through vendored `Miri.Interpreter.Step.step`,
`writeAggregate`, `Allocation.writeScalar` (`ProvenanceMap.insertPtr_new`), and
`Allocation.readScalar ... true` (`ProvenanceMap.read_exact_pointer`). -/
theorem ep2LmObserve_v8_cap (treeBorrows : Bool) :
    ep2LmObserve treeBorrows 7 1 = lmObsClosureCap7_1 := by
  have h := runMiriSteps_v8ClosureCap_ok treeBorrows
  dsimp only at h
  change toLmObs (runMiriSteps (annealStepHooksDropBinderSubtype v8ClosureCapMir treeBorrows) 8
      (mkV8ClosureCapState (.live (.immediate (.scalar (lmScalarUInt 7 4)))))) = lmObsClosureCap7_1
  unfold toLmObs lmObsClosureCap7_1
  cases hrun : runMiriSteps (annealStepHooksDropBinderSubtype v8ClosureCapMir treeBorrows) 8
      (mkV8ClosureCapState (.live (.immediate (.scalar (lmScalarUInt 7 4))))) with
  | error e => rw [hrun] at h; cases h
  | ok pair =>
    rcases pair with ⟨st', ret⟩
    rw [hrun] at h
    cases ret with
    | none => cases h
    | some v =>
      cases v with
      | dead => cases h
      | live op =>
        cases op with
        | immediate _ => cases h
        | indirect mp =>
          dsimp only at h ⊢
          rw [h]

/-! ## §5. Exhaustive Axiom, Non-Triviality, & Import-Isolation Audit -/

section AxiomAudit
open Lean Elab Command

elab "#assert_drop_binder_subtype_lm_audit" : command => do
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
    throwError "LeanMiriSpec.DropBinderAndSubtypeLM: 0 declarations found"
  logInfo m!"LeanMiriSpec.DropBinderAndSubtypeLM: verified {checked} declarations (sorry_free=true, import_isolated=true, 0 trivial, 0 ofReduceBool)"

#assert_drop_binder_subtype_lm_audit

end AxiomAudit

end LeanMiriSpec.DropBinderAndSubtypeLM
