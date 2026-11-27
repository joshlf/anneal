/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Miri.Interpreter.DynamicLayout
import Miri.Interpreter.Projection
import Miri.Interpreter.PointerOffset
import Miri.Interpreter.ValidityMachine
import Miri.Memory.Validity
import LeanMiriSpec.HeapAllocAndWidePtrLM
import LeanMiriSpec.Correspondence.Translate

/-!
# Episode 1 LeanMiri Authority: Wide-Slice / Trailing-Slice DSTs, `MaybeUninit<T>` /
# `ManuallyDrop<T>` Byte Transport, Multi-Step Pointer-Offset Chains, and Non-Null `FnPtr`
# Validity (`LeanMiriSpec.WideDstAndMaybeUninitLM`)

The vendored LeanMiri (`lean-miri/vendor/`, unmodified) side of the frozen 24-case (`0..23`) ×
2-mode matrix shared with `MiniRustSpec.WideDstAndMaybeUninitMR`:

* `D1` (`0..7`): `[u32]` wide places through vendored `Projection.projectIndex` / `OpTy.len`
  (bounds UB), and `size_of_val` / `align_of_val` through vendored
  `DynamicLayout.sizeAndAlignFromMeta` on `.slice` / `.str` and on the `#[repr(C)]`
  trailing-slice structs (`.adt false`, tail padding, `InvalidMeta(SliceTooBig)` /
  `InvalidMeta(TooBig)` overflow).
* `D2` (`8..13`): whole-union copies through vendored `Allocation.copy` (raw bytes, `InitMask`,
  provenance), typed reads through `Allocation.readScalar` (uninit UB) and
  `Validity.checkPrimitive .boolean` (`kani#5205` / `#5196` byte `2` UB).
* `D3` (`14..19`): `ptrOffsetInbounds` / `Pointer.wrappingSignedOffset` chains over a live
  harness allocation, and the Tree Borrows mode-sensitive write through a protected `Frozen`
  reborrow (vendored `RetagPipeline.retagPointerValue` + `MachineMemoryHooks.beforeMemoryWrite`).
* `D4` (`20..23`): `Validity.checkScalar` on the `pointerLayoutData true` valid range
  `[1, 2^64-1]` (function pointers) vs `pointerLayoutData false` (raw pointers), with
  `ValidityMachine.scalarMayBeNull`.

The memory harness (`lmAllocate`, `lmStore`, `lmLoad`, `lmRetag`, `lmTreeAccess`) is the one of
`LeanMiriSpec.HeapAllocAndWidePtrLM`: every state change is a vendored definition.

`section StepDriver` additionally executes the shared `CapturedMir` fixtures of cases `11`,
`14`–`18`, `19` (no borrow tracker), and `20`–`23` directly through vendored
`Miri.Interpreter.Step.step` (over `LeanMiriSpec.Correspondence.translateBody` and the
`annealStepHooksLM2_2` adapter, with a documented harness cast-hook overlay), bundled in
`ep1_lean_miri_step_driver_capstone`. The adapter's limits are pinned exactly: whole-union copies
(`D2` cases `8`–`10`, `12`, `13`) are `.unsupported` / a false uninit-local UB there, and the
`D1` `constantIndex` fixtures (`0`, `5`) do not translate, so those cells rest on the harness path.

The `CapturedMir` fixtures of §0 are textually identical to those of
`MiniRustSpec.WideDstAndMaybeUninitMR`, so Episode 2's cross-root bridge can lock them by
`Eq.refl`.

Root isolation: zero `Anneal.*` and zero `MiniRustSpec.*` imports (trailing `run_cmd` audit).
-/

namespace LeanMiriSpec.WideDstAndMaybeUninitLM

set_option Elab.async false

/-! ## §0. Frozen Observation Interface, Kernel Helpers, and Shared `CapturedMir` Fixtures -/

/-- Frozen cross-authority observation domain (constructor order shared identically with
`MiniRustSpec.WideDstAndMaybeUninitMR.MrWdObs`). -/
inductive LmWdObs : Type where
  /-- Normal termination with a scalar result. -/
  | okScalar (val : Nat)
  /-- Normal termination with a dynamic `(size, align)` pair. -/
  | okSizeAlign (sizeBytes : Nat) (alignBytes : Nat)
  /-- Whole-value byte transport with `byteCount` bytes, `initCount` of them initialized. -/
  | okUninitPreserved (byteCount : Nat) (initCount : Nat)
  /-- A pointer accepted by validity: function identifier (non-null) or address `0`. -/
  | okFnPtr (addrOrId : Nat)
  /-- Undefined behavior. -/
  | ub
  /-- Fail-closed unsupported construct or out-of-range case. -/
  | unsupported
  /-- Specification panic (unused on the LeanMiri side; kept for interface parity). -/
  | specPanic
  deriving DecidableEq, Repr

/-- Number of canonical cases (`0..23`, 48 mode cells). -/
def lmWdCaseCount : Nat := 24

/-- Close an equality goal via kernel definitional reduction (`Eq.refl`, zero `Lean.ofReduceBool`). -/
local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq?
    | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

/-- Combine the two halves of a two-query case: agreement is required, otherwise fail closed. -/
def wdCombine (a b : LmWdObs) : LmWdObs := if a = b then a else .unsupported

/-! ### Shared `CapturedMir` fixtures

Every definition in this section is shared verbatim (same text, same opened namespaces) with
`MiniRustSpec.WideDstAndMaybeUninitMR`, so Episode 2's cross-root bridge can lock each fixture
by `Eq.refl`. -/

section Fixtures

open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst Trusted.Rustc.V2026_06_01.Layout

@[reducible] def wdSpan : String := "wd.rs:1:1"
@[reducible] def wdSt (k : StatementKind) : Statement := { kind := k, span := wdSpan }
@[reducible] def wdBb (stmts : List StatementKind) (term : TerminatorKind) : BasicBlockData :=
  { statements := stmts.map wdSt, terminator := { kind := term, span := wdSpan }, isCleanup := false }
@[reducible] def wdDecl (ty : Ty) : LocalDecl := { mutability := .mut, ty, debugName := none }
@[reducible] def wdLoc (i : Nat) (proj : List ProjectionElem := []) : Place :=
  { local_ := i, projection := proj }

@[reducible] def wdU8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }
@[reducible] def wdU16Ty : Ty := { kind := .uint .u16, layoutIdx := 0 }
@[reducible] def wdU32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
@[reducible] def wdU64Ty : Ty := { kind := .uint .u64, layoutIdx := 0 }
@[reducible] def wdUsizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
@[reducible] def wdIsizeTy : Ty := { kind := .int .isize, layoutIdx := 0 }
@[reducible] def wdBoolTy : Ty := { kind := .bool, layoutIdx := 0 }
@[reducible] def wdArr3U32Ty : Ty := { kind := .array (.uint .u32) 3, layoutIdx := 0 }
@[reducible] def wdSizeAlignTy : Ty := { kind := .tuple [.uint .usize, .uint .usize], layoutIdx := 0 }
@[reducible] def wdRawU8Ty : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }
@[reducible] def wdRawU32Ty : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }
@[reducible] def wdRawMutU32Ty : Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }
@[reducible] def wdRawArr3Ty : Ty := { kind := .rawPtr .not (.array (.uint .u32) 3), layoutIdx := 0 }
@[reducible] def wdRawMutArr3Ty : Ty := { kind := .rawPtr .mut (.array (.uint .u32) 3), layoutIdx := 0 }
@[reducible] def wdFnPtrTy : Ty := { kind := .fnPtr [] (.uint .u32) .safe .rust, layoutIdx := 0 }

/-- Unsized pointee `RigidTy`s: `[u32]`, `str`, `[()]`, and the two `#[repr(C)]` trailing-slice
DST structs `HeaderSlice { tag: u8, data: [u32] }` / `Align8TailU16 { hdr: u64, tail: [u16] }`. -/
@[reducible] def wdSliceU32Rigid : RigidTy := .slice (.uint .u32)
@[reducible] def wdSliceUnitRigid : RigidTy := .slice (.tuple [])
@[reducible] def wdHeaderSliceRigid : RigidTy := .adt "wd::HeaderSlice" []
@[reducible] def wdAlign8TailU16Rigid : RigidTy := .adt "wd::Align8TailU16" []

@[reducible] def wdConstU8 (n : Nat) : Operand := .constant { ty := wdU8Ty, val := .scalar (.int ⟨n, 1⟩) }
@[reducible] def wdConstU32 (n : Nat) : Operand := .constant { ty := wdU32Ty, val := .scalar (.int ⟨n, 4⟩) }
@[reducible] def wdConstUsize (n : Nat) : Operand := .constant { ty := wdUsizeTy, val := .scalar (.int ⟨n, 8⟩) }
@[reducible] def wdConstIsize (n : Int) : Operand :=
  .constant { ty := wdIsizeTy, val := .scalar (.int ⟨(n % (2 ^ 64 : Int)).toNat, 8⟩) }
@[reducible] def wdIntrinsicOp (name : String) (tys : List RigidTy) : Operand :=
  .constant { ty := { kind := .fnDef name tys, layoutIdx := 0 }, val := .zeroSized }

/-- Layout table shared by the `D1` DST-struct and `D2` union / transparent-wrapper fixtures:
`0 = u8`, `1 = u32`, `2 = ()`, `3 = MaybeUninit<u32>` (`union { uninit: (), value: u32, byte: u8 }`),
`4 = bool`, `5 = MaybeUninit<bool>` (`union { uninit: (), value: bool, byte: u8 }`),
`6 = ManuallyDrop<u32>` (transparent single-field struct `FieldsShape.arbitrary [0] [0]`). -/
def wdU8Layout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 255 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wdU32Layout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wdUnitLayout : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }
def wdMaybeUninitU32Layout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory,
    fields := .union 3, variants := .single 0, isUninhabited := false, fieldLayouts := [2, 1, 0] }
def wdBoolLayout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 1 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wdMaybeUninitBoolLayout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .union 3, variants := .single 0, isUninhabited := false, fieldLayouts := [2, 4, 0] }
def wdManuallyDropU32Layout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 }),
    fields := .arbitrary [⟨0⟩] [0], variants := .single 0, isUninhabited := false,
    fieldLayouts := [1] }

def wdLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [wdU8Layout, wdU32Layout, wdUnitLayout, wdMaybeUninitU32Layout, wdBoolLayout,
                wdMaybeUninitBoolLayout, wdManuallyDropU32Layout] }

@[reducible] def wdUnitTy : Ty := { kind := .tuple [], layoutIdx := 2 }
@[reducible] def wdMuU32Ty : Ty := { kind := .adt "core::mem::MaybeUninit<u32>" [], layoutIdx := 3 }
@[reducible] def wdMuBoolTy : Ty := { kind := .adt "core::mem::MaybeUninit<bool>" [], layoutIdx := 5 }
@[reducible] def wdMdU32Ty : Ty := { kind := .adt "core::mem::ManuallyDrop<u32>" [], layoutIdx := 6 }

def wdFnAbi : FnAbi :=
  { args := [], ret := { layout := wdU32Layout, mode := .direct }, conv := .rust, canUnwind := false }

def wdBody (name : String) (argCount : Nat) (decls : List Ty) (blocks : List BasicBlockData) :
    CapturedMir :=
  { defPath := name, phase := .runtimePostCleanup, role := .subject, argCount,
    localDecls := decls.map wdDecl, basicBlocks := blocks, fnAbi := wdFnAbi,
    layouts := wdLayouts, allocations := [] }

/-- `_2 = &raw const (_1[0])`, `_3 = *const [T] from_raw_parts(_2, len)` for a slice of `elem`. -/
@[reducible] def wdFromRawParts (elem : RigidTy) (len : Nat) : List StatementKind :=
  [.assign (wdLoc 2) (.rawPtr .not (wdLoc 1 [.constantIndex 0 3 false])),
   .assign (wdLoc 3) (.aggregate (.rawPtr { kind := elem, layoutIdx := 0 } .not)
     [.copy (wdLoc 2), wdConstUsize len])]

/-- Size / align query fixture: `(size_of_val(_3), align_of_val(_3))` on a wide pointer `_3`
assembled by `ptr::from_raw_parts(&raw const _1[0], len)` with pointee `pointee`. -/
def wdSizeAlignMir (name : String) (pointee : RigidTy) (len : Nat) : CapturedMir :=
  wdBody name 1
    [wdSizeAlignTy, wdArr3U32Ty, wdRawU32Ty, { kind := .rawPtr .not pointee, layoutIdx := 0 },
     wdUsizeTy, wdUsizeTy]
    [wdBb (wdFromRawParts pointee len)
       (.call (wdIntrinsicOp "core::intrinsics::size_of_val" [pointee]) [.copy (wdLoc 3)]
         (wdLoc 4) (some 1) .continue_),
     wdBb [] (.call (wdIntrinsicOp "core::intrinsics::align_of_val" [pointee]) [.copy (wdLoc 3)]
         (wdLoc 5) (some 2) .continue_),
     wdBb [.assign (wdLoc 0) (.aggregate .tuple [.copy (wdLoc 4), .copy (wdLoc 5)])] .return_]

/-- Case 0: `[u32]` `from_raw_parts` + `ptr::metadata` + `Rvalue.len` + `(*s)[meta - len + 1]`. -/
def wdCase0Mir : CapturedMir :=
  wdBody "wd::case0_slice_meta_len_index" 1
    [wdU32Ty, wdArr3U32Ty, wdRawU32Ty, { kind := .rawPtr .not wdSliceU32Rigid, layoutIdx := 0 },
     wdUsizeTy, wdUsizeTy, wdUsizeTy, wdUsizeTy]
    [wdBb (wdFromRawParts wdSliceU32Rigid 3 ++
       [.assign (wdLoc 4) (.unaryOp .ptrMetadata (.copy (wdLoc 3))),
        .assign (wdLoc 5) (.len (wdLoc 3 [.deref])),
        .assign (wdLoc 6) (.binaryOp .sub (.copy (wdLoc 4)) (.copy (wdLoc 5))),
        .assign (wdLoc 7) (.binaryOp .add (.copy (wdLoc 6)) (wdConstUsize 1)),
        .assign (wdLoc 0) (.use (.copy (wdLoc 3 [.deref, .index 7])))]) .return_]

def wdCase1Mir : CapturedMir := wdSizeAlignMir "wd::case1_slice_u32_size_align" wdSliceU32Rigid 3
def wdCase2Mir : CapturedMir := wdSizeAlignMir "wd::case2_zst_slice_size_align" wdSliceUnitRigid 5
def wdCase2StrMir : CapturedMir := wdSizeAlignMir "wd::case2_empty_str_size_align" .str 0
def wdCase3Mir : CapturedMir :=
  wdSizeAlignMir "wd::case3_isize_max_boundary" wdSliceU32Rigid 2305843009213693951
def wdCase4Mir : CapturedMir :=
  wdSizeAlignMir "wd::case4_isize_max_overflow" wdSliceU32Rigid 2305843009213693952

/-- Case 5: `[u32]` (`len = 2`) checked indexing `(*s)[2]` out of bounds. -/
def wdCase5Mir : CapturedMir :=
  wdBody "wd::case5_slice_index_oob" 1
    [wdU32Ty, wdArr3U32Ty, wdRawU32Ty, { kind := .rawPtr .not wdSliceU32Rigid, layoutIdx := 0 },
     wdUsizeTy]
    [wdBb (wdFromRawParts wdSliceU32Rigid 2 ++
       [.assign (wdLoc 4) (.use (wdConstUsize 2)),
        .assign (wdLoc 0) (.use (.copy (wdLoc 3 [.deref, .index 4])))]) .return_]

def wdCase6Mir : CapturedMir := wdSizeAlignMir "wd::case6_header_slice_dst" wdHeaderSliceRigid 3
def wdCase7Mir : CapturedMir := wdSizeAlignMir "wd::case7_align8_tail_u16_dst" wdAlign8TailU16Rigid 3

/-- Union copy fixture: `_1 = U { <field> }` (or left `uninit()`), `_2 = copy _1`, `_0 = move _2`. -/
def wdUnionCopyMir (name : String) (uTy : Ty) (init : List StatementKind) : CapturedMir :=
  { wdBody name 0 [uTy, uTy, uTy]
      [wdBb (init ++ [.assign (wdLoc 2) (.use (.copy (wdLoc 1))),
                      .assign (wdLoc 0) (.use (.move (wdLoc 2)))]) .return_] with
    fnAbi := { wdFnAbi with ret := { layout := wdMaybeUninitU32Layout, mode := .direct } } }

/-- Case 8: `MaybeUninit::<u32>::uninit()` whole-union copy. -/
def wdCase8Mir : CapturedMir :=
  wdUnionCopyMir "wd::case8_maybe_uninit_copy" wdMuU32Ty
    [.assign (wdLoc 1) (.aggregate (.adt "core::mem::MaybeUninit<u32>" 0 (some 0))
      [.constant { ty := wdUnitTy, val := .zeroSized }])]

/-- Case 9: partially initialized union (`byte = 0x2A`, 3 trailing uninit bytes) whole copy. -/
def wdCase9Mir : CapturedMir :=
  wdUnionCopyMir "wd::case9_partial_union_copy" wdMuU32Ty
    [.assign (wdLoc 1) (.aggregate (.adt "core::mem::MaybeUninit<u32>" 0 (some 2)) [wdConstU8 42])]

/-- Typed-read union fixture: `_1 = U { <field> }`, `_2 = copy _1`, `_0 = copy (_2.<f> : T)`. -/
def wdUnionReadMir (name : String) (uTy : Ty) (adtName : String) (initField : Nat)
    (initOp : Operand) (readField : Nat) (readTy : Ty) (retTy : Ty) : CapturedMir :=
  wdBody name 0 [retTy, uTy, uTy]
    [wdBb [.assign (wdLoc 1) (.aggregate (.adt adtName 0 (some initField)) [initOp]),
           .assign (wdLoc 2) (.use (.copy (wdLoc 1))),
           .assign (wdLoc 0) (.use (.copy (wdLoc 2 [.field readField readTy])))] .return_]

/-- Case 10: `MaybeUninit<u32>` write `0x12345678`, whole copy, `assume_init` read. -/
def wdCase10Mir : CapturedMir :=
  wdUnionReadMir "wd::case10_maybe_uninit_roundtrip" wdMuU32Ty "core::mem::MaybeUninit<u32>"
    1 (wdConstU32 305419896) 1 wdU32Ty wdU32Ty

/-- Case 11: `ManuallyDrop<u32>` write `77`, copy, field read. -/
def wdCase11Mir : CapturedMir :=
  wdBody "wd::case11_manually_drop_roundtrip" 0 [wdU32Ty, wdMdU32Ty, wdMdU32Ty]
    [wdBb [.assign (wdLoc 1) (.aggregate (.adt "core::mem::ManuallyDrop<u32>" 0 none) [wdConstU32 77]),
           .assign (wdLoc 2) (.use (.copy (wdLoc 1))),
           .assign (wdLoc 0) (.use (.copy (wdLoc 2 [.field 0 wdU32Ty])))] .return_]

/-- Case 12: `MaybeUninit::<u32>::uninit().assume_init()` (typed `u32` read of uninit bytes). -/
def wdCase12Mir : CapturedMir :=
  wdUnionReadMir "wd::case12_maybe_uninit_read_uninit" wdMuU32Ty "core::mem::MaybeUninit<u32>"
    0 (.constant { ty := wdUnitTy, val := .zeroSized }) 1 wdU32Ty wdU32Ty

/-- Case 13: `MaybeUninit<bool>` holding raw byte `2` (`kani#5205`/`#5196`), typed `bool` read. -/
def wdCase13Mir : CapturedMir :=
  wdUnionReadMir "wd::case13_maybe_uninit_bool_invalid" wdMuBoolTy "core::mem::MaybeUninit<bool>"
    2 (wdConstU8 2) 1 wdBoolTy wdBoolTy

/-- Case 13 companion: the SAME union holding byte `2` is copied whole WITHOUT UB. -/
def wdCase13CopyMir : CapturedMir :=
  { wdUnionCopyMir "wd::case13_maybe_uninit_bool_copy" wdMuBoolTy
      [.assign (wdLoc 1) (.aggregate (.adt "core::mem::MaybeUninit<bool>" 0 (some 2)) [wdConstU8 2])] with
    fnAbi := { wdFnAbi with ret := { layout := wdMaybeUninitBoolLayout, mode := .direct } } }

/-- `D3` prologue: `_2 = &raw const _1` (`*const [u32; 3]`), `_3 = _2 as *const u8`. -/
@[reducible] def wdArrBytePtr : List StatementKind :=
  [.assign (wdLoc 2) (.rawPtr .not (wdLoc 1)),
   .assign (wdLoc 3) (.cast .ptrToPtr (.copy (wdLoc 2)) wdRawU8Ty)]

@[reducible] def wdArithOffsetCall (elem : RigidTy) (src : Nat) (delta : Int) (dst next : Nat) :
    TerminatorKind :=
  .call (wdIntrinsicOp "core::intrinsics::arith_offset" [elem]) [.copy (wdLoc src), wdConstIsize delta]
    (wdLoc dst) (some next) .continue_

@[reducible] def wdD3Decls : List Ty :=
  [wdU32Ty, wdArr3U32Ty, wdRawArr3Ty, wdRawU8Ty, wdRawU8Ty, wdRawU32Ty, wdRawU32Ty, wdRawU32Ty]

/-- Case 14: `*const [u32;3] -> *const u8 -> +4 -> *const u32 -> +1 -> -1 -> *p` (`arr[1]`). -/
def wdCase14Mir : CapturedMir :=
  wdBody "wd::case14_cast_offset_chain" 1 wdD3Decls
    [wdBb (wdArrBytePtr ++
       [.assign (wdLoc 4) (.binaryOp .offset (.copy (wdLoc 3)) (wdConstIsize 4)),
        .assign (wdLoc 5) (.cast .ptrToPtr (.copy (wdLoc 4)) wdRawU32Ty),
        .assign (wdLoc 6) (.binaryOp .offset (.copy (wdLoc 5)) (wdConstIsize 1)),
        .assign (wdLoc 7) (.binaryOp .offset (.copy (wdLoc 6)) (wdConstIsize (-1))),
        .assign (wdLoc 0) (.use (.copy (wdLoc 7 [.deref])))]) .return_]

/-- Case 15: wrapping `arith_offset(+100)` out of bounds, `arith_offset(-96)` back, `*p` (`arr[1]`). -/
def wdCase15Mir : CapturedMir :=
  wdBody "wd::case15_wrapping_oob_and_back" 1 wdD3Decls
    [wdBb wdArrBytePtr (wdArithOffsetCall (.uint .u8) 3 100 4 1),
     wdBb [] (wdArithOffsetCall (.uint .u8) 4 (-96) 3 2),
     wdBb [.assign (wdLoc 5) (.cast .ptrToPtr (.copy (wdLoc 3)) wdRawU32Ty),
           .assign (wdLoc 0) (.use (.copy (wdLoc 5 [.deref])))] .return_]

/-- Case 16: in-bounds `offset(+100)` past the 12-byte array (no dereference). -/
def wdCase16Mir : CapturedMir :=
  wdBody "wd::case16_inbounds_offset_oob" 1 wdD3Decls
    [wdBb (wdArrBytePtr ++
       [.assign (wdLoc 4) (.binaryOp .offset (.copy (wdLoc 3)) (wdConstIsize 100)),
        .assign (wdLoc 0) (.use (wdConstU32 0))]) .return_]

/-- Case 17: wrapping `arith_offset(+100)` out of bounds followed by a dereference. -/
def wdCase17Mir : CapturedMir :=
  wdBody "wd::case17_wrapping_oob_deref" 1 wdD3Decls
    [wdBb wdArrBytePtr (wdArithOffsetCall (.uint .u8) 3 100 4 1),
     wdBb [.assign (wdLoc 5) (.cast .ptrToPtr (.copy (wdLoc 4)) wdRawU32Ty),
           .assign (wdLoc 0) (.use (.copy (wdLoc 5 [.deref])))] .return_]

/-- Case 18: zero-offset chain `offset(0)` + `arith_offset(0)` + `*p` (`arr[0]`). -/
def wdCase18Mir : CapturedMir :=
  wdBody "wd::case18_zero_offset_chain" 1 wdD3Decls
    [wdBb (wdArrBytePtr ++
       [.assign (wdLoc 4) (.binaryOp .offset (.copy (wdLoc 3)) (wdConstIsize 0))])
       (wdArithOffsetCall (.uint .u8) 4 0 3 1),
     wdBb [.assign (wdLoc 5) (.cast .ptrToPtr (.copy (wdLoc 3)) wdRawU32Ty),
           .assign (wdLoc 0) (.use (.copy (wdLoc 5 [.deref])))] .return_]

/-- Case 19 (mode-sensitive): write `999` through `(&raw mut _1 as *mut u32).offset(1)` while the
borrow tag on `_1` is protected (`FnEntry`) in Tree Borrows mode, then read it back. -/
def wdCase19Mir : CapturedMir :=
  wdBody "wd::case19_protected_offset_write" 1
    [wdU32Ty, wdArr3U32Ty, wdRawMutArr3Ty, wdRawMutU32Ty, wdRawMutU32Ty]
    [wdBb [.assign (wdLoc 2) (.rawPtr .mut (wdLoc 1)),
           .assign (wdLoc 3) (.cast .ptrToPtr (.copy (wdLoc 2)) wdRawMutU32Ty),
           .assign (wdLoc 4) (.binaryOp .offset (.copy (wdLoc 3)) (wdConstIsize 1)),
           .assign (wdLoc 4 [.deref]) (.use (wdConstU32 999)),
           .assign (wdLoc 0) (.use (.copy (wdLoc 4 [.deref])))] .return_]

/-- Case 20: valid reified function pointer `fn() -> u32` round-tripped through a byte-level
`transmute::<fn() -> u32, fn() -> u32>` (validity re-check of the decoded pointer). -/
def wdCase20Mir : CapturedMir :=
  wdBody "wd::case20_fn_ptr_valid" 1 [wdFnPtrTy, wdFnPtrTy]
    [wdBb [.assign (wdLoc 0) (.cast .transmute (.copy (wdLoc 1)) wdFnPtrTy)] .return_]

/-- Cases 21/22: `transmute::<usize, fn() -> u32>(0)` (null function pointer). -/
def wdCase21Mir : CapturedMir :=
  wdBody "wd::case21_null_fn_ptr" 1 [wdFnPtrTy, wdUsizeTy]
    [wdBb [.assign (wdLoc 0) (.cast .transmute (.copy (wdLoc 1)) wdFnPtrTy)] .return_]

/-- Case 23: `transmute::<usize, *const u8>(0)` (null raw pointer contrast). -/
def wdCase23Mir : CapturedMir :=
  wdBody "wd::case23_null_raw_ptr" 1 [wdRawU8Ty, wdUsizeTy]
    [wdBb [.assign (wdLoc 0) (.cast .transmute (.copy (wdLoc 1)) wdRawU8Ty)] .return_]

end Fixtures

/-! ## §1. The LeanMiri Harness over Vendored Definitions -/

section Harness

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
open LeanMiriSpec.HeapAllocAndWidePtrLM
open LeanMiriSpec.Correspondence (scalarLayoutData pointerLayoutData zstLayoutData translateAlignBytes)

/-- A typed failure: the exact vendored error value that stopped a case. -/
inductive LmWdFail where
  /-- A memory-harness failure (`LeanMiriSpec.HeapAllocAndWidePtrLM.LmFailure`). -/
  | mem (f : LmFailure)
  /-- A vendored `RvalueM` step error (e.g. `DynamicLayout.sizeAndAlignFromMeta`). -/
  | step (e : StepError)
  /-- A vendored place projection error (`Projection.projectIndex` / `OpTy.len`). -/
  | proj (e : ProjectionError)
  /-- A vendored `ptrOffsetInbounds` error. -/
  | offset (e : PointerOffsetError)
  /-- A vendored wrapping pointer arithmetic error. -/
  | pointer (e : PointerError)
  /-- A vendored validity error (`Validity.checkScalar` / `Validity.checkPrimitive`). -/
  | validity (e : ValidityError Unit)
  /-- The harness was used outside its domain. -/
  | harness (msg : String)

/-- The harness monad. -/
abbrev LmWdM := Except LmWdFail

/-- Classify a vendored step error. -/
def lmWdObsOfStep (e : StepError) : LmWdObs :=
  match lmObsOfStep e with
  | .ub => .ub
  | _ => .unsupported

/-- Classify a typed failure as UB or fail-closed unsupported. -/
def lmWdObsOfFail : LmWdFail → LmWdObs
  | .mem f => match lmObsOfFailure f with
    | .ub => .ub
    | _ => .unsupported
  | .step e => lmWdObsOfStep e
  | .proj (.bounds _ _) => .ub
  | .proj .pointerArithOverflow => .ub
  | .proj (.machineError e) => lmWdObsOfStep e
  | .proj _ => .unsupported
  | .offset (.access e) => lmWdObsOfStep (MemoryErrors.access e)
  | .offset (.pointer _) => .unsupported
  | .pointer _ => .unsupported
  | .validity (.failure _) => .ub
  | .validity (.pathFailure _ _) => .ub
  | .validity _ => .unsupported
  | .harness _ => .unsupported

/-- Observe a case result. -/
def lmWdRun (r : LmWdM LmWdObs) : LmWdObs :=
  match r with
  | .ok o => o
  | .error f => lmWdObsOfFail f

/-- Lift a memory-harness result. -/
def lmWdMem {A : Type} (r : Except LmFailure A) : LmWdM A := r.mapError .mem

/-! ### `D1` type identities and layouts -/

def lmWdTyU8 : Miri.MIR.TyId := 4001
def lmWdTyU16 : Miri.MIR.TyId := 4002
def lmWdTyU32 : Miri.MIR.TyId := 4003
def lmWdTyU64 : Miri.MIR.TyId := 4004
def lmWdTyUnit : Miri.MIR.TyId := 4005
def lmWdTySliceU32 : Miri.MIR.TyId := 4010
def lmWdTySliceUnit : Miri.MIR.TyId := 4011
def lmWdTyStr : Miri.MIR.TyId := 4012
def lmWdTySliceU16 : Miri.MIR.TyId := 4013
/-- `#[repr(C)] struct HeaderSlice { tag: u8, data: [u32] }`. -/
def lmWdTyHeaderSlice : Miri.MIR.TyId := 4020
/-- `#[repr(C)] struct Align8TailU16 { hdr: u64, tail: [u16] }`. -/
def lmWdTyAlign8TailU16 : Miri.MIR.TyId := 4021
/-- `core::mem::ManuallyDrop<u32>` (transparent single-field wrapper `FieldsShape.Arbitrary #[0] #[0]`). -/
def lmWdTyMdU32 : Miri.MIR.TyId := 4030
/-- `fn() -> u32` function pointer type identity (`pointerLayoutData true`). -/
def lmWdTyFnPtr : Miri.MIR.TyId := 4031

def lmWdU8Lay : LayoutData := scalarLayoutData 1 false
def lmWdU16Lay : LayoutData := scalarLayoutData 2 false
def lmWdU32Lay : LayoutData := scalarLayoutData 4 false
def lmWdU64Lay : LayoutData := scalarLayoutData 8 false

/-- `ManuallyDrop<u32>` transparent single-field struct layout (`FieldsShape.Arbitrary #[0] #[0]`). -/
def lmWdMdU32Lay : LayoutData :=
  { lmWdU32Lay with fields := .Arbitrary #[Size.ZERO] #[0] }

/-- The unsized `[T]` layout (`FieldsShape.Array stride 0`, `BackendRepr.Memory (sized := false)`). -/
def lmWdSliceLay (elem : LayoutData) : LayoutData :=
  { fields := .Array elem.size 0
    variants := .Single 0
    backendRepr := .Memory (sized := false)
    largestNiche := none
    uninhabited := false
    align := elem.align
    size := Size.ZERO
    maxReprAlign := none
    unadjustedAbiAlign := elem.unadjustedAbiAlign
    reprC := false
    randomizationSeed := 0 }

/-- The unsized `#[repr(C)]` two-field struct layout with its tail at `tailOffset` (rustc
`univariant`: sized prefix size `tailOffset`, struct alignment `alignBytes`). -/
def lmWdDstStructLay (tailOffset alignBytes : Nat) : LayoutData :=
  { fields := .Arbitrary #[Size.ZERO, Size.ofBytes (UInt64.ofNat tailOffset)] #[0, 1]
    variants := .Single 0
    backendRepr := .Memory (sized := false)
    largestNiche := none
    uninhabited := false
    align := ⟨translateAlignBytes alignBytes⟩
    size := Size.ofBytes (UInt64.ofNat tailOffset)
    maxReprAlign := none
    unadjustedAbiAlign := translateAlignBytes alignBytes
    reprC := true
    randomizationSeed := 0 }

def lmWdSliceU32Lay : LayoutData := lmWdSliceLay lmWdU32Lay
def lmWdSliceUnitLay : LayoutData := lmWdSliceLay zstLayoutData
def lmWdStrLay : LayoutData := lmWdSliceLay lmWdU8Lay
def lmWdSliceU16Lay : LayoutData := lmWdSliceLay lmWdU16Lay
/-- `HeaderSlice`: `tag` at `0`, `data: [u32]` at `4`, align `4`. -/
def lmWdHeaderSliceLay : LayoutData := lmWdDstStructLay 4 4
/-- `Align8TailU16`: `hdr` at `0`, `tail: [u16]` at `8`, align `8`. -/
def lmWdAlign8TailU16Lay : LayoutData := lmWdDstStructLay 8 8

/-- The compiler's field query (`TyAndLayout::field`) on the fragment's types. -/
def lmWdField (l : TyAndLayout Miri.MIR.TyId) (i : Nat) : Except StepError (TyAndLayout Miri.MIR.TyId) :=
  if l.ty == lmWdTySliceU32 && i == 0 then .ok ⟨lmWdTyU32, lmWdU32Lay⟩
  else if l.ty == lmWdTySliceUnit && i == 0 then .ok ⟨lmWdTyUnit, zstLayoutData⟩
  else if l.ty == lmWdTyStr && i == 0 then .ok ⟨lmWdTyU8, lmWdU8Lay⟩
  else if l.ty == lmWdTySliceU16 && i == 0 then .ok ⟨lmWdTyU16, lmWdU16Lay⟩
  else if l.ty == lmWdTyHeaderSlice && i == 0 then .ok ⟨lmWdTyU8, lmWdU8Lay⟩
  else if l.ty == lmWdTyHeaderSlice && i == 1 then .ok ⟨lmWdTySliceU32, lmWdSliceU32Lay⟩
  else if l.ty == lmWdTyAlign8TailU16 && i == 0 then .ok ⟨lmWdTyU64, lmWdU64Lay⟩
  else if l.ty == lmWdTyAlign8TailU16 && i == 1 then .ok ⟨lmWdTySliceU16, lmWdSliceU16Lay⟩
  else if l.ty == lmWdTyMdU32 && i == 0 then .ok ⟨lmWdTyU32, lmWdU32Lay⟩
  else .error (.invalidProgram "field query outside the fragment")

/-- The compiler's type classification (`ty.kind()`) on the fragment's unsized types. -/
def lmWdClassify (ty : Miri.MIR.TyId) : Except StepError DynamicTypeKind :=
  if ty == lmWdTyHeaderSlice || ty == lmWdTyAlign8TailU16 then .ok (.adt false)
  else if ty == lmWdTyStr then .ok .str
  else if ty == lmWdTySliceU32 || ty == lmWdTySliceUnit || ty == lmWdTySliceU16 then .ok .slice
  else .error (.unsupported "unsized type outside the fragment")

/-- Lift a compiler query into `RvalueM`. -/
def lmWdLift {A : Type} (r : Except StepError A) : RvalueM Unit A :=
  match r with
  | .ok a => pure a
  | .error e => throw e

/-- `isize::MAX` as a `Size` (`max_size_of_val` on a 64-bit target). -/
def lmWdMaxSize : Size := Size.ofBytes (UInt64.ofNat lmIsizeMax)

/-- The compiler hooks of vendored `DynamicLayout.sizeAndAlignFromMeta`. -/
def lmWdDynHooks : DynamicLayoutHooks Provenance Unit Unit where
  target := lmLayout
  maxSizeOfVal := lmWdMaxSize
  classify := fun _ ty => lmWdLift (lmWdClassify ty)
  field := fun _ l i => lmWdLift (lmWdField l i)
  packedAlign := fun _ _ => pure none
  vtableSizeAndAlign := fun _ _ _ => throw (.unsupported "no trait objects in this fragment")

/-- A `usize` scalar (`ptr::metadata` of a slice pointer). -/
def lmWdUsize (n : Nat) : LmWdM (Scalar Provenance) :=
  (Scalar.fromUInt (BitVec.ofNat 128 n) (Size.ofBytes 8)).mapError (fun e => .mem (.scalar e))

/-- `(size_of_val, align_of_val)` of a pointee `⟨ty, lay⟩` with slice metadata `len`, through
vendored `DynamicLayout.sizeAndAlignFromMeta`. -/
def lmWdSizeAlign (ty : Miri.MIR.TyId) (lay : LayoutData) (len : Nat) : LmWdM LmWdObs := do
  let m ← lmWdUsize len
  match lmRun (DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () 4 (.metadata m) ⟨ty, lay⟩) with
  | .error e => .error (.step e)
  | .ok none => .error (.harness "extern type")
  | .ok (some (size, align)) =>
    match align.bytes with
    | .ok a => .ok (.okSizeAlign size.bytes.toNat a.toNat)
    | .error _ => .error (.harness "alignment")

/-! ### Memory helpers -/

/-- Wrapping byte offset (vendored `Pointer.wrappingOffset`). -/
def lmWdOff (p : Pointer (Option Provenance)) (k : Nat) : LmWdM (Pointer (Option Provenance)) :=
  (p.wrappingOffset (Size.ofBytes (UInt64.ofNat k)) lmPtrArith).mapError .pointer

/-- In-bounds signed byte offset (vendored `ptrOffsetInbounds`, live allocation lookup). -/
def lmWdInb (st : LmState) (p : Pointer (Option Provenance)) (k : Int64) :
    LmWdM (Pointer (Option Provenance)) :=
  (ptrOffsetInbounds lmPtrArith p k lmResolvePure st.mem.getAllocInfo).mapError .offset

/-- Wrapping signed byte offset (vendored `Pointer.wrappingSignedOffset`, `arith_offset`). -/
def lmWdWrap (p : Pointer (Option Provenance)) (k : Int64) : LmWdM (Pointer (Option Provenance)) :=
  (p.wrappingSignedOffset k lmPtrArith).mapError .pointer

/-- A live `[u32; 3]` allocation holding `[a, b, c]`. -/
def lmWdArray (tb : Bool) (a b c : Nat) : LmWdM (Pointer (Option Provenance) × LmState) := do
  let (p, st) ← lmWdMem (lmAllocate (lmInit tb) 12 4)
  let st ← lmWdMem (lmStore st p 4 a)
  let q ← lmWdOff p 4
  let st ← lmWdMem (lmStore st q 4 b)
  let r ← lmWdOff p 8
  let st ← lmWdMem (lmStore st r 4 c)
  pure (p, st)

/-- The projection context of vendored `Projection`: memory offsets go through vendored
`projectionMemoryOffset` over the harness's live allocations. -/
def lmWdProjCx (st : LmState) : ProjectionCx Provenance where
  target := lmLayout
  maxSizeOfVal := lmWdMaxSize
  isSliceOrStr := fun ty => .ok (ty == lmWdTySliceU32 || ty == lmWdTyStr || ty == lmWdTySliceUnit ||
    ty == lmWdTySliceU16)
  field := fun l i => (lmWdField l i).mapError .machineError
  variant := fun _ _ => .error (.invariant "no variants in this fragment")
  dynamicAlign := fun _ _ => .error (.invariant "no dynamic alignment in this fragment")
  packedAlign := fun _ => .ok none
  immediateOffset := projectionImmediateOffset (fun _ _ => .ok ())
  memoryOffset := projectionMemoryOffset lmPtrArith lmResolvePure st.mem.getAllocInfo
  subsliceLayout := fun _ _ => .error (.invariant "no subslices in this fragment")
  layoutOf := fun _ => .error (.invariant "no layoutOf in this fragment")
  deref := fun _ => .error (.invariant "no deref in this fragment")
  localIndex := fun _ => .error (.invariant "no locals in this fragment")

/-- Cases `0` / `5`: a `*const [u32]` wide place `(&raw const arr[0], len)` over `[11, 22, 33]`;
`ptr::metadata` (`Scalar.toTargetUsize`), `Rvalue.len` (vendored `OpTy.len`), and the checked
index `(*s)[i]` (vendored `projectIndex`, `i = meta - len + 1` when `index = none`). -/
def lmWdSliceIndex (tb : Bool) (len : Nat) (index : Option Nat) : LmWdM LmWdObs := do
  let (p, st) ← lmWdArray tb 11 22 33
  let m ← lmWdUsize len
  let base : OpTy Provenance := ⟨.indirect ⟨p, .metadata m, none⟩, ⟨lmWdTySliceU32, lmWdSliceU32Lay⟩⟩
  let md ← (m.toTargetUsize (Size.ofBytes 8)).mapError (fun e => .mem (.scalar e))
  let l ← (base.len (lmWdProjCx st)).mapError .proj
  let i : UInt64 := match index with
    | some i => UInt64.ofNat i
    | none => md - l + 1
  let elem ← (projectIndex (lmWdProjCx st) base i).mapError .proj
  match elem.op with
  | .indirect place =>
    let (v, _) ← lmWdMem (lmLoad st place.ptr 4)
    pure (.okScalar v)
  | .immediate _ => .error (.harness "immediate element")

/-! ### `D2` union transport -/

/-- Whole-union `copy` of a `size`-byte union local into a second `size`-byte local in the same
live allocation: Tree Borrows read of the source and write of the destination, then vendored
`Allocation.copy` (raw bytes + `InitMask` + provenance). `init = some (width, bits)` first
initializes the leading `width` bytes of the source with `bits`. -/
def lmWdUnionCopy (tb : Bool) (size : Nat) (init : Option (Nat × Nat)) :
    LmWdM (Pointer (Option Provenance) × LmState) := do
  let (src, st) ← lmWdMem (lmAllocate (lmInit tb) (2 * size) size)
  let st ← match init with
    | none => pure st
    | some (width, bits) => lmWdMem (lmStore st src (UInt64.ofNat width) bits)
  let dst ← lmWdOff src size
  let (id, off, prov, alloc) ← lmWdMem (lmAccessTarget st src (UInt64.ofNat size))
  let st ← lmWdMem (lmTreeAccess st false alloc src id prov ⟨off, Size.ofBytes (UInt64.ofNat size)⟩)
  let (id', off', prov', alloc') ← lmWdMem (lmAccessTarget st dst (UInt64.ofNat size))
  let st ← lmWdMem (lmTreeAccess st true alloc' dst id' prov' ⟨off', Size.ofBytes (UInt64.ofNat size)⟩)
  match st.mem.live.find? (fun e => e.1 == id) with
  | none => .error (.harness "dead union allocation")
  | some (_, entry) =>
    match Allocation.copy entry.allocation ⟨off, Size.ofBytes (UInt64.ofNat size)⟩ off'
        (Size.ofBytes 8) (id == id') true entry.allocation with
    | .error e _ => .error (.mem (.allocation e))
    | .ok () copied =>
      match st.mem.setLiveAllocation id copied with
      | .error e => .error (.mem (.access (.allocationLookup e)))
      | .ok mem => pure (dst, { st with mem := mem })

/-- The number of initialized bytes (vendored `InitMask.get`) among the `size` bytes at `dst`. -/
def lmWdInitCount (st : LmState) (dst : Pointer (Option Provenance)) (size : Nat) : LmWdM Nat := do
  let (id, off, _, _) ← lmWdMem (lmAccessTarget st dst (UInt64.ofNat size))
  match st.mem.live.find? (fun e => e.1 == id) with
  | none => .error (.harness "dead union allocation")
  | some (_, entry) =>
    pure ((List.range size).filter (fun i =>
      match entry.allocation.initializationMask.get (Size.ofBytes (off.bytes + UInt64.ofNat i)) with
      | .ok true => true
      | _ => false)).length

/-- A whole-union copy observed as `okUninitPreserved size initCount`. -/
def lmWdUnionCopyObs (tb : Bool) (size : Nat) (init : Option (Nat × Nat)) : LmWdM LmWdObs := do
  let (dst, st) ← lmWdUnionCopy tb size init
  let n ← lmWdInitCount st dst size
  pure (.okUninitPreserved size n)

/-- A whole-union copy followed by a typed `u32` read of the copy (`Allocation.readScalar`). -/
def lmWdUnionReadU32 (tb : Bool) (init : Option (Nat × Nat)) : LmWdM LmWdObs := do
  let (dst, st) ← lmWdUnionCopy tb 4 init
  let (v, _) ← lmWdMem (lmLoad st dst 4)
  pure (.okScalar v)

/-- Case `11`: `ManuallyDrop<u32>` transparent single-field wrapper write `val`, copy through
vendored `Allocation.copy`, project field `0` through vendored `Projection.projectField`
(`FieldsShape.Arbitrary #[0] #[0]`), then load the inner `u32`. -/
def lmWdManuallyDropReadU32 (tb : Bool) (val : Nat) : LmWdM LmWdObs := do
  let (dst, st) ← lmWdUnionCopy tb 4 (some (4, val))
  let base : OpTy Provenance := ⟨.indirect ⟨dst, .none, none⟩, ⟨lmWdTyMdU32, lmWdMdU32Lay⟩⟩
  let fld ← (projectField (lmWdProjCx st) base 0).mapError .proj
  match fld.op with
  | .indirect place =>
    let (v, _) ← lmWdMem (lmLoad st place.ptr 4)
    pure (.okScalar v)
  | .immediate _ => .error (.harness "immediate ManuallyDrop field")

/-- `bool`'s scalar validity layout (`valid_range = 0..=1`). -/
def lmWdBoolValidity : ScalarValidityLayout :=
  ⟨Size.ofBytes 1, { start := BitVec.ofNat 128 0, «end» := BitVec.ofNat 128 1 }⟩

/-- Case `13`: `MaybeUninit<bool>` holding raw byte `2`, copied whole, then read at `bool`:
`Allocation.readScalar` followed by vendored `Validity.checkPrimitive .boolean`. -/
def lmWdUnionReadBool (tb : Bool) : LmWdM LmWdObs := do
  let (dst, st) ← lmWdUnionCopy tb 1 (some (1, 2))
  let (v, _) ← lmWdMem (lmLoad st dst 1)
  let s ← (Scalar.fromUInt (Prov := Provenance) (BitVec.ofNat 128 v) (Size.ofBytes 1)).mapError
    (fun e => .mem (.scalar e))
  match Validity.checkPrimitive (MachineError := Unit) (HookState := Unit) .boolean lmWdBoolValidity s
      (fun _ st => .error () st) () with
  | .ok _ _ => pure (.okScalar v)
  | .error e _ => .error (.validity e)

/-! ### `D3` pointer-offset chains -/

/-- Load `u32` through `p`. -/
def lmWdLoadObs (st : LmState) (p : Pointer (Option Provenance)) : LmWdM LmWdObs := do
  let (v, _) ← lmWdMem (lmLoad st p 4)
  pure (.okScalar v)

/-- Case `14`: `+4` bytes, `+1` `u32`, `-1` `u32` (all in-bounds), then `*p` (`arr[1]`). -/
def lmWdCase14 (tb : Bool) : LmWdM LmWdObs := do
  let (p, st) ← lmWdArray tb 100 200 300
  let q ← lmWdInb st p 4
  let r ← lmWdInb st q 4
  let s ← lmWdInb st r (-4)
  lmWdLoadObs st s

/-- Case `15`: wrapping `+100` (out of bounds), wrapping `-96` (back in bounds), `*p` (`arr[1]`). -/
def lmWdCase15 (tb : Bool) : LmWdM LmWdObs := do
  let (p, st) ← lmWdArray tb 100 200 300
  let q ← lmWdWrap p 100
  let r ← lmWdWrap q (-96)
  lmWdLoadObs st r

/-- Case `16`: in-bounds `offset(+100)` past the 12-byte array (no dereference). -/
def lmWdCase16 (tb : Bool) : LmWdM LmWdObs := do
  let (p, st) ← lmWdArray tb 100 200 300
  let _ ← lmWdInb st p 100
  pure (.okScalar 0)

/-- Case `17`: wrapping `+100` followed by a dereference. -/
def lmWdCase17 (tb : Bool) : LmWdM LmWdObs := do
  let (p, st) ← lmWdArray tb 100 200 300
  let q ← lmWdWrap p 100
  lmWdLoadObs st q

/-- Case `18`: `offset(0)` + `arith_offset(0)` + `*p` (`arr[0]`). -/
def lmWdCase18 (tb : Bool) : LmWdM LmWdObs := do
  let (p, st) ← lmWdArray tb 100 200 300
  let q ← lmWdInb st p 0
  let r ← lmWdWrap q 0
  lmWdLoadObs st r

/-- Case `19` (mode-sensitive): `&arr` retagged on function entry (`FnEntry`, protected shared
`Frozen` reborrow) through vendored `RetagPipeline.retagPointerValue`, cast to `*mut u32`,
`offset(1)`, write `999` (vendored `beforeMemoryWrite` under Tree Borrows), read back. -/
def lmWdCase19 (tb : Bool) : LmWdM LmWdObs := do
  let (p, st) ← lmWdArray tb 100 200 300
  let (child, st) ← lmWdMem (lmRetag st p .reference lmFrozenFacts .Shared .FnEntry true)
  let q ← lmWdInb st child 4
  let st ← lmWdMem (lmStore st q 4 999)
  lmWdLoadObs st q

/-! ### `D4` pointer validity -/

/-- The scalar validity layout of an 8-byte pointer (`pointerLayoutData nonNull`). -/
def lmWdPtrValidity (nonNull : Bool) : LmWdM ScalarValidityLayout :=
  match (pointerLayoutData nonNull).backendRepr with
  | .Scalar (.Initialized (validRange := vr) ..) => pure ⟨Size.ofBytes 8, vr⟩
  | _ => .error (.harness "pointer layout")

/-- Vendored `Validity.checkScalar` (`visit_scalar`) of a pointer scalar. The machine callback
is never consulted for Miri's absolute-address provenance (`offsetIsAddr`); it fails closed. -/
def lmWdCheckPtr (nonNull : Bool) (s : Scalar Provenance) : LmWdM Unit := do
  let lay ← lmWdPtrValidity nonNull
  match Validity.checkScalar (MachineError := Unit) (HookState := Unit) lay s
      (fun _ st => .error () st) () with
  | .ok () _ => pure ()
  | .error e _ => .error (.validity e)

/-- Byte-level transmute of an 8-byte scalar through a live allocation (`Allocation.writeScalar`
followed by `Allocation.readScalar` with provenance, plus Tree Borrows write/read hooks and
vendored `Validity.checkScalar` at `pointerLayoutData nonNull`). -/
def lmWdTransmutePtrOn (st : LmState) (sIn : Scalar Provenance) (nonNull : Bool) :
    LmWdM (Scalar Provenance) := do
  let (slot, st) ← lmWdMem (lmAllocate st 8 8)
  let (id, off, prov, alloc) ← lmWdMem (lmAccessTarget st slot 8)
  let range : AllocRange := ⟨off, Size.ofBytes 8⟩
  let st ← lmWdMem (lmTreeAccess st true alloc slot id prov range)
  let st ← match st.mem.live.find? (fun e => e.1 == id) with
    | none => .error (.harness "dead transmute slot")
    | some (_, entry) =>
      match Allocation.writeScalar lmLayout range sIn entry.allocation with
      | .error e _ => .error (.mem (.allocation e))
      | .ok () updated =>
        match st.mem.setLiveAllocation id updated with
        | .error e => .error (.mem (.access (.allocationLookup e)))
        | .ok mem => pure { st with mem := mem }
  let (id', off', prov', alloc') ← lmWdMem (lmAccessTarget st slot 8)
  let st ← lmWdMem (lmTreeAccess st false alloc' slot id' prov' ⟨off', Size.ofBytes 8⟩)
  let sOut ← match st.mem.live.find? (fun e => e.1 == id') with
    | none => .error (.harness "dead transmute slot")
    | some (_, entry) =>
      match entry.allocation.readScalar lmLayout ⟨off', Size.ofBytes 8⟩ true with
      | .error e => .error (.mem (.allocation e))
      | .ok s => pure s
  lmWdCheckPtr nonNull sOut
  pure sOut

/-- Case `20`: a reified function pointer into a live allocation, transmuted through vendored
`OpTy.transmute` / `projectionImmediateOffset` at `pointerLayoutData true` (`fn() -> u32`),
validated via vendored `Validity.checkScalar`, and checked for intact concrete provenance. -/
def lmWdCase20 (tb : Bool) : LmWdM LmWdObs := do
  let (p, st) ← lmWdMem (lmAllocate (lmInit tb) 1 1)
  let sIn ← (Scalar.fromMaybePointer lmLayout p).mapError (fun e => .mem (.scalar e))
  let fnLay : TyAndLayout Miri.MIR.TyId := ⟨lmWdTyFnPtr, pointerLayoutData true⟩
  let base : OpTy Provenance := ⟨.immediate (.scalar sIn), fnLay⟩
  let out ← (base.transmute (lmWdProjCx st) fnLay).mapError .proj
  match out.op with
  | .immediate (.scalar sOut) =>
    lmWdCheckPtr true sOut
    let pOut ← (sOut.toPointer lmLayout).mapError (fun e => .mem (.scalar e))
    match pOut.provenance with
    | some (.concrete id _) => pure (.okFnPtr id.value.toNat)
    | _ => .error (.harness "function pointer lost provenance across transmute")
  | _ => .error (.harness "transmuted function pointer not scalar immediate")

/-- Cases `21`–`23`: `transmute::<usize, P>(0)` via real byte round-trip (`Allocation.writeScalar`
+ `Allocation.readScalar`) validated at `P` (`nonNull = true` for `fn() -> u32`, `false` for raw). -/
def lmWdNullPtr (tb : Bool) (nonNull : Bool) : LmWdM LmWdObs := do
  let sIn ← lmWdUsize 0
  let sOut ← lmWdTransmutePtrOn (lmInit tb) sIn nonNull
  let a ← (sOut.toTargetUsize (Size.ofBytes 8)).mapError (fun e => .mem (.scalar e))
  pure (.okFnPtr a.toNat)

/-! ### The observer -/

/-- The LeanMiri run of case `idx` (`none` for `idx ≥ 24`). -/
def lmWdCase (tb : Bool) : Nat → Option LmWdObs
  | 0 => some (lmWdRun (lmWdSliceIndex tb 3 none))
  | 1 => some (lmWdRun (lmWdSizeAlign lmWdTySliceU32 lmWdSliceU32Lay 3))
  | 2 => some (wdCombine (lmWdRun (lmWdSizeAlign lmWdTySliceUnit lmWdSliceUnitLay 5))
      (lmWdRun (lmWdSizeAlign lmWdTyStr lmWdStrLay 0)))
  | 3 => some (lmWdRun (lmWdSizeAlign lmWdTySliceU32 lmWdSliceU32Lay 2305843009213693951))
  | 4 => some (lmWdRun (lmWdSizeAlign lmWdTySliceU32 lmWdSliceU32Lay 2305843009213693952))
  | 5 => some (lmWdRun (lmWdSliceIndex tb 2 (some 2)))
  | 6 => some (lmWdRun (lmWdSizeAlign lmWdTyHeaderSlice lmWdHeaderSliceLay 3))
  | 7 => some (lmWdRun (lmWdSizeAlign lmWdTyAlign8TailU16 lmWdAlign8TailU16Lay 3))
  | 8 => some (lmWdRun (lmWdUnionCopyObs tb 4 none))
  | 9 => some (lmWdRun (lmWdUnionCopyObs tb 4 (some (1, 42))))
  | 10 => some (lmWdRun (lmWdUnionReadU32 tb (some (4, 305419896))))
  | 11 => some (lmWdRun (lmWdManuallyDropReadU32 tb 77))
  | 12 => some (lmWdRun (lmWdUnionReadU32 tb none))
  | 13 => some (lmWdRun (lmWdUnionReadBool tb))
  | 14 => some (lmWdRun (lmWdCase14 tb))
  | 15 => some (lmWdRun (lmWdCase15 tb))
  | 16 => some (lmWdRun (lmWdCase16 tb))
  | 17 => some (lmWdRun (lmWdCase17 tb))
  | 18 => some (lmWdRun (lmWdCase18 tb))
  | 19 => some (lmWdRun (lmWdCase19 tb))
  | 20 => some (lmWdRun (lmWdCase20 tb))
  | 21 => some (lmWdRun (lmWdNullPtr tb true))
  | 22 => some (lmWdRun (lmWdNullPtr tb true))
  | 23 => some (lmWdRun (lmWdNullPtr tb false))
  | _ => none

/-- **Real LeanMiri observer** (fail-closed `.unsupported` for `idx ≥ 24`). -/
def lmWdObserve (tb : Bool) (idx : Nat) : LmWdObs :=
  match lmWdCase tb idx with
  | some o => o
  | none => .unsupported

end Harness

/-! ### Evaluable twins (while-loop unrolling of the vendored memory code) -/

section Twins
open LeanMiriSpec.HeapAllocAndWidePtrLM

unroll_loops lmWdArrayU := lmWdArray fuel 0 with lmAllocateU, lmStoreU
unroll_loops lmWdProjCxU := lmWdProjCx fuel 0 with getAllocInfoU
unroll_loops lmWdInbU := lmWdInb fuel 0 with getAllocInfoU
unroll_loops lmWdSliceIndexU := lmWdSliceIndex fuel 0 with lmWdArrayU, lmWdProjCxU, lmLoadU
unroll_loops lmWdUnionCopyU := lmWdUnionCopy fuel 0
  with lmAllocateU, lmStoreU, lmAccessTargetU, lmTreeAccessU
unroll_loops lmWdInitCountU := lmWdInitCount fuel 0 with lmAccessTargetU
unroll_loops lmWdUnionCopyObsU := lmWdUnionCopyObs fuel 0 with lmWdUnionCopyU, lmWdInitCountU
unroll_loops lmWdUnionReadU32U := lmWdUnionReadU32 fuel 0 with lmWdUnionCopyU, lmLoadU
unroll_loops lmWdManuallyDropReadU32U := lmWdManuallyDropReadU32 fuel 0
  with lmWdUnionCopyU, lmWdProjCxU, lmLoadU
unroll_loops lmWdUnionReadBoolU := lmWdUnionReadBool fuel 0 with lmWdUnionCopyU, lmLoadU
unroll_loops lmWdLoadObsU := lmWdLoadObs fuel 0 with lmLoadU
unroll_loops lmWdCase14U := lmWdCase14 fuel 0 with lmWdArrayU, lmWdInbU, lmWdLoadObsU
unroll_loops lmWdCase15U := lmWdCase15 fuel 0 with lmWdArrayU, lmWdLoadObsU
unroll_loops lmWdCase16U := lmWdCase16 fuel 0 with lmWdArrayU, lmWdInbU
unroll_loops lmWdCase17U := lmWdCase17 fuel 0 with lmWdArrayU, lmWdLoadObsU
unroll_loops lmWdCase18U := lmWdCase18 fuel 0 with lmWdArrayU, lmWdInbU, lmWdLoadObsU
unroll_loops lmWdCase19U := lmWdCase19 fuel 0 with lmWdArrayU, lmRetagU, lmWdInbU, lmStoreU, lmWdLoadObsU
unroll_loops lmWdTransmutePtrOnU := lmWdTransmutePtrOn fuel 0
  with lmAllocateU, lmAccessTargetU, lmTreeAccessU
unroll_loops lmWdCase20U := lmWdCase20 fuel 0 with lmAllocateU, lmWdProjCxU
unroll_loops lmWdNullPtrU := lmWdNullPtr fuel 0 with lmWdTransmutePtrOnU
unroll_loops lmWdCaseU := lmWdCase fuel 0
  with lmWdSliceIndexU, lmWdUnionCopyObsU, lmWdUnionReadU32U, lmWdManuallyDropReadU32U,
    lmWdUnionReadBoolU, lmWdCase14U, lmWdCase15U, lmWdCase16U, lmWdCase17U, lmWdCase18U,
    lmWdCase19U, lmWdCase20U, lmWdNullPtrU
unroll_loops lmWdObserveU := lmWdObserve fuel 0 with lmWdCaseU

end Twins

/-- Frozen expected LeanMiri table for `tb = false` (no borrow tracker). -/
def lmWdExpectedBasic : List LmWdObs :=
  [.okScalar 22, .okSizeAlign 12 4, .okSizeAlign 0 1, .okSizeAlign 9223372036854775804 4, .ub, .ub,
   .okSizeAlign 16 4, .okSizeAlign 16 8,
   .okUninitPreserved 4 0, .okUninitPreserved 4 1, .okScalar 305419896, .okScalar 77, .ub, .ub,
   .okScalar 200, .okScalar 200, .ub, .ub, .okScalar 100, .okScalar 999,
   .okFnPtr 1, .ub, .ub, .okFnPtr 0]

/-- Frozen expected LeanMiri table for `tb = true` (Tree Borrows; only case `19` differs). -/
def lmWdExpectedTb : List LmWdObs :=
  [.okScalar 22, .okSizeAlign 12 4, .okSizeAlign 0 1, .okSizeAlign 9223372036854775804 4, .ub, .ub,
   .okSizeAlign 16 4, .okSizeAlign 16 8,
   .okUninitPreserved 4 0, .okUninitPreserved 4 1, .okScalar 305419896, .okScalar 77, .ub, .ub,
   .okScalar 200, .okScalar 200, .ub, .ub, .okScalar 100, .ub,
   .okFnPtr 1, .ub, .ub, .okFnPtr 0]

/-- **Kernel-checked 48-cell LeanMiri table** (`24` cases × no borrow tracker / Tree Borrows),
every cell executed by the vendored definitions and closed by `decide +kernel` on the
loop-unrolled twin (`lmWdObserveU.eq_src`, itself a kernel-checked theorem). -/
theorem lmWdObserve_table :
    (List.range lmWdCaseCount).map (lmWdObserve false) = lmWdExpectedBasic ∧
    (List.range lmWdCaseCount).map (lmWdObserve true) = lmWdExpectedTb := by
  rw [lmWdObserveU.eq_src]
  refine ⟨?_, ?_⟩ <;> decide +kernel


/-- Out-of-range cases are fail-closed `.unsupported` in both modes. -/
theorem lmWdObserve_out_of_range (tb : Bool) (idx : Nat) (h : lmWdCaseCount ≤ idx) :
    lmWdObserve tb idx = .unsupported := by
  unfold lmWdCaseCount at h
  have hNone : lmWdCase tb idx = none := by
    unfold lmWdCase
    split <;> first | rfl | omega
  unfold lmWdObserve
  rw [hNone]

/-- Exact mode-sensitivity predicate: only case `19` flips between the modes. -/
def lmWdCaseModeSensitive : Nat → Bool
  | 19 => true
  | _ => false

/-- **Exact LeanMiri Tree Borrows mode-sensitivity `↔`**: no borrow tracker and Tree Borrows
disagree on `idx < 24` if and only if `idx = 19`. -/
theorem lmWdObserve_mode_sensitivity :
    lmWdObserve false 19 = .okScalar 999 ∧
    lmWdObserve true 19 = .ub ∧
    (∀ idx, idx < lmWdCaseCount →
      (lmWdObserve false idx ≠ lmWdObserve true idx ↔ lmWdCaseModeSensitive idx = true)) := by
  have hB := lmWdObserve_table.1
  have hT := lmWdObserve_table.2
  have hAll : ((List.range lmWdCaseCount).all fun idx =>
      decide ((lmWdExpectedBasic[idx]? ≠ lmWdExpectedTb[idx]?) ↔
        lmWdCaseModeSensitive idx = true)) = true := by decide
  have cellB : ∀ idx, idx < lmWdCaseCount →
      some (lmWdObserve false idx) = lmWdExpectedBasic[idx]? := by
    intro idx hi
    have h' := congrArg (fun l => l[idx]?) hB
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  have cellT : ∀ idx, idx < lmWdCaseCount →
      some (lmWdObserve true idx) = lmWdExpectedTb[idx]? := by
    intro idx hi
    have h' := congrArg (fun l => l[idx]?) hT
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  refine ⟨Option.some.inj (cellB 19 (by decide)), Option.some.inj (cellT 19 (by decide)), ?_⟩
  intro idx hi
  have hIff := of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr hi))
  rw [← cellB idx hi, ← cellT idx hi] at hIff
  simpa [Option.some.injEq] using hIff

/-! ## §2. Exact Vendored Failure Diagnostics and the Case `13` Companion -/

section Diagnostics
open Miri.ABI Miri.Memory Miri.Interpreter LeanMiriSpec.HeapAllocAndWidePtrLM

/-- `InvalidMeta(SliceTooBig)` from vendored `sizeAndAlignFromMeta` (`.slice` arm). -/
def lmWdIsSliceTooBig : LmWdM LmWdObs → Bool
  | .error (.step (.undefinedBehavior "InvalidMeta(SliceTooBig)")) => true
  | _ => false
/-- `InvalidMeta(TooBig)` from vendored `sizeAndAlignFromMeta` (`.adt` arm). -/
def lmWdIsTooBig : LmWdM LmWdObs → Bool
  | .error (.step (.undefinedBehavior "InvalidMeta(TooBig)")) => true
  | _ => false
/-- `ProjectionError.bounds 2 2` from vendored `projectIndex`. -/
def lmWdIsIndexOOB : LmWdM LmWdObs → Bool
  | .error (.proj (.bounds 2 2)) => true
  | _ => false
/-- `AllocError.invalidUninitBytes` from vendored `Allocation.readScalar`. -/
def lmWdIsUninitRead : LmWdM LmWdObs → Bool
  | .error (.mem (.allocation (.invalidUninitBytes _))) => true
  | _ => false
/-- `ValidityFailure.invalidBool 2` from vendored `Validity.checkPrimitive`. -/
def lmWdIsInvalidBool : LmWdM LmWdObs → Bool
  | .error (.validity (.failure (.invalidBool 2))) => true
  | _ => false
/-- `AccessError.pointerOutOfBounds` from vendored `ptrOffsetInbounds`. -/
def lmWdIsInboundsOOB : LmWdM LmWdObs → Bool
  | .error (.offset (.access (.pointerOutOfBounds ..))) => true
  | _ => false
/-- `AccessError.pointerOutOfBounds` from vendored `getPtrAccess` on a load. -/
def lmWdIsDerefOOB : LmWdM LmWdObs → Bool
  | .error (.mem (.access (.pointerOutOfBounds ..))) => true
  | _ => false
/-- A Tree Borrows access rejection from vendored `MachineMemoryHooks`. -/
def lmWdIsTreeAccessUb : LmWdM LmWdObs → Bool
  | .error (.mem (.treeAccess _)) => true
  | _ => false
/-- `ValidityFailure.invalidScalarBits` from vendored `Validity.checkScalar`. -/
def lmWdIsInvalidScalar : LmWdM LmWdObs → Bool
  | .error (.validity (.failure (.invalidScalarBits ..))) => true
  | _ => false

/-- **Exact vendored diagnostics of every `.ub` cell**: each faults for its genuine root cause. -/
theorem lm_wd_exact_ub_diagnostics :
    lmWdIsSliceTooBig (lmWdSizeAlign lmWdTySliceU32 lmWdSliceU32Lay 2305843009213693952) = true ∧
    lmWdIsIndexOOB (lmWdSliceIndex false 2 (some 2)) = true ∧
    lmWdIsIndexOOB (lmWdSliceIndex true 2 (some 2)) = true ∧
    lmWdIsUninitRead (lmWdUnionReadU32 false none) = true ∧
    lmWdIsUninitRead (lmWdUnionReadU32 true none) = true ∧
    lmWdIsInvalidBool (lmWdUnionReadBool false) = true ∧
    lmWdIsInvalidBool (lmWdUnionReadBool true) = true ∧
    lmWdIsInboundsOOB (lmWdCase16 false) = true ∧
    lmWdIsInboundsOOB (lmWdCase16 true) = true ∧
    lmWdIsDerefOOB (lmWdCase17 false) = true ∧
    lmWdIsDerefOOB (lmWdCase17 true) = true ∧
    lmWdIsTreeAccessUb (lmWdCase19 true) = true ∧
    lmWdIsInvalidScalar (lmWdNullPtr false true) = true ∧
    lmWdIsInvalidScalar (lmWdNullPtr true true) = true ∧
    lmWdIsTooBig (lmWdSizeAlign lmWdTyHeaderSlice lmWdHeaderSliceLay 2305843009213693951) = true := by
  rw [lmWdSliceIndexU.eq_src, lmWdUnionReadU32U.eq_src, lmWdUnionReadBoolU.eq_src,
    lmWdCase16U.eq_src, lmWdCase17U.eq_src, lmWdCase19U.eq_src, lmWdNullPtrU.eq_src]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **Case `13` companion (`kani#5205` / `#5196`)**: copying the whole `MaybeUninit<bool>` that
holds the invalid byte `2` succeeds in both modes and preserves that initialized byte; only the
typed `bool` read (case `13`) is UB. -/
theorem lm_case13_union_copy_of_invalid_bool_byte_ok :
    lmWdRun (lmWdUnionCopyObs false 1 (some (1, 2))) = .okUninitPreserved 1 1 ∧
    lmWdRun (lmWdUnionCopyObs true 1 (some (1, 2))) = .okUninitPreserved 1 1 ∧
    lmWdObserve false 13 = .ub ∧ lmWdObserve true 13 = .ub := by
  rw [lmWdUnionCopyObsU.eq_src, lmWdObserveU.eq_src]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Diagnostics

/-! ## §3. Universal Laws of the Vendored Definitions (`D1`–`D4`) -/

section UniversalLaws
open Miri.ABI Miri.Memory Miri.Interpreter LeanMiriSpec.HeapAllocAndWidePtrLM
open LeanMiriSpec.Correspondence (scalarLayoutData zstLayoutData translateAlignBytes)

/-- `D1` (vendored fast path): every sized layout's dynamic size/align is its static one, for all hooks, fuel, and metadata. -/
theorem lm_sizeAndAlign_sized {P S C : Type} [PointerProvenance P] (h : DynamicLayoutHooks P S C)
    (c : C) (n : Nat) (md : MemPlaceMeta P) (l : TyAndLayout Miri.MIR.TyId)
    (hs : l.layout.isSized = true) :
    DynamicLayout.sizeAndAlignFromMeta h c n md l = pure (some (l.layout.size, l.layout.align.abi)) := by
  unfold DynamicLayout.sizeAndAlignFromMeta
  simp [hs]

/-- `D1` **universal `[u32]` law** of vendored `sizeAndAlignFromMeta` (`.slice` arm): for every metadata scalar of length `len`, `size_of_val = 4 * len` when `4 * len ≤ isize::MAX`, and `InvalidMeta(SliceTooBig)` UB otherwise. -/
theorem lm_sizeAndAlign_sliceU32 (n : Nat) (s : Scalar Provenance) (len : UInt64)
    (hs : s.toTargetUsize (Size.fromBits lmLayout.pointerWidth.bits) = .ok len) :
    lmRun (DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 1) (.metadata s)
        ⟨lmWdTySliceU32, lmWdSliceU32Lay⟩) =
      if 4 * len.toNat ≤ lmIsizeMax then
        .ok (some (Size.ofBytes (UInt64.ofNat (4 * len.toNat)), lmWdU32Lay.align.abi))
      else .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") := by
  have h4 : lmWdU32Lay.size.bytes.toNat = 4 := rfl
  have hm : lmWdMaxSize.bytes = 9223372036854775807 := rfl
  have hkey : (9223372036854775807 : UInt64) <
      (Size.ofBytes (UInt64.ofNat (min (4 * len.toNat) 18446744073709551615))).bytes ↔
      ¬ 4 * len.toNat ≤ lmIsizeMax := by
    show (9223372036854775807 : UInt64) < UInt64.ofNat (min (4 * len.toNat) 18446744073709551615) ↔ _
    rw [UInt64.lt_iff_toNat_lt]
    simp
    unfold lmIsizeMax
    omega
  have hmin : 4 * len.toNat ≤ lmIsizeMax → min (4 * len.toNat) 18446744073709551615 = 4 * len.toNat := by
    unfold lmIsizeMax; omega
  unfold DynamicLayout.sizeAndAlignFromMeta
  simp [lmRun, lmWdDynHooks, lmWdClassify, lmWdField, lmWdLift, lmWdSliceU32Lay, lmWdSliceLay,
    lmWdTySliceU32, lmWdTyHeaderSlice, lmWdTyAlign8TailU16, lmWdTyStr, lmWdTySliceUnit, lmWdTySliceU16,
    LayoutData.isSized, BackendRepr.isSized, BackendRepr.isUnsized, lmLayout]
  have hs' : s.toTargetUsize (Size.fromBits PointerWidth.w64.bits) = .ok len := hs
  simp only [bind, EStateM.bind, pure]
  split
  next a st heq =>
    split at heq
    next x s1 hm =>
      cases hm
      rw [hs'] at heq
      simp only [Except.mapError] at heq
      split at heq
      next b s2 hl =>
        cases hl
        rw [h4, hm] at heq
        by_cases hc : 4 * len.toNat ≤ lmIsizeMax
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => (hkey.mp h) hc)), hmin hc] at heq
          cases heq
          rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
          simp
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (hkey.mpr hc))] at heq
          cases heq
      next e s2 hl => cases hl
    next e s1 hm => cases hm
  next e st heq =>
    split at heq
    next x s1 hm =>
      cases hm
      rw [hs'] at heq
      simp only [Except.mapError] at heq
      split at heq
      next b s2 hl =>
        cases hl
        rw [h4, hm] at heq
        by_cases hc : 4 * len.toNat ≤ lmIsizeMax
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => (hkey.mp h) hc))] at heq
          cases heq
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (hkey.mpr hc))] at heq
          cases heq
          rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      next e s2 hl => cases hl
    next e s1 hm => cases hm

/-- `D1` **universal `str` law** of vendored `sizeAndAlignFromMeta` (`.str` arm): for every
metadata scalar of length `len`, `size_of_val = len` (`align = 1`) when `len ≤ isize::MAX`, and
`InvalidMeta(SliceTooBig)` UB otherwise. -/
theorem lm_sizeAndAlign_str (n : Nat) (s : Scalar Provenance) (len : UInt64)
    (hs : s.toTargetUsize (Size.fromBits lmLayout.pointerWidth.bits) = .ok len) :
    lmRun (DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 1) (.metadata s)
        ⟨lmWdTyStr, lmWdStrLay⟩) =
      if len.toNat ≤ lmIsizeMax then
        .ok (some (Size.ofBytes len, lmWdU8Lay.align.abi))
      else .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") := by
  have h1 : lmWdU8Lay.size.bytes.toNat = 1 := rfl
  have hm : lmWdMaxSize.bytes = 9223372036854775807 := rfl
  have hlt : len.toNat ≤ 18446744073709551615 := by have := len.toNat_lt; omega
  have hmin : min (1 * len.toNat) 18446744073709551615 = len.toNat := by omega
  have hkey : (9223372036854775807 : UInt64) < len ↔ ¬ len.toNat ≤ lmIsizeMax := by
    rw [UInt64.lt_iff_toNat_lt]; unfold lmIsizeMax; simp
  unfold DynamicLayout.sizeAndAlignFromMeta
  simp [lmRun, lmWdDynHooks, lmWdClassify, lmWdField, lmWdLift, lmWdStrLay, lmWdSliceLay,
    lmWdTySliceU32, lmWdTyHeaderSlice, lmWdTyAlign8TailU16, lmWdTyStr, lmWdTySliceUnit, lmWdTySliceU16,
    LayoutData.isSized, BackendRepr.isSized, BackendRepr.isUnsized, lmLayout]
  have hs' : s.toTargetUsize (Size.fromBits PointerWidth.w64.bits) = .ok len := hs
  simp only [bind, EStateM.bind, pure]
  split
  next a st heq =>
    split at heq
    next x s1 h_m =>
      cases h_m
      rw [hs'] at heq
      simp only [Except.mapError] at heq
      split at heq
      next b s2 hl =>
        cases hl
        rw [h1, hm, hmin, UInt64.ofNat_toNat] at heq
        by_cases hc : len.toNat ≤ lmIsizeMax
        · have hnot : ¬ ((9223372036854775807 : UInt64) < len) := fun h => (hkey.mp h) hc
          simp only [Size.ofBytes, hnot, ↓reduceIte] at heq
          cases heq
          simp [hc, Size.ofBytes]
        · have hbig : (9223372036854775807 : UInt64) < len := hkey.mpr hc
          simp only [Size.ofBytes, hbig, ↓reduceIte] at heq
          cases heq
      next e s2 hl => cases hl
    next e s1 h_m => cases h_m
  next e st heq =>
    split at heq
    next x s1 h_m =>
      cases h_m
      rw [hs'] at heq
      simp only [Except.mapError] at heq
      split at heq
      next b s2 hl =>
        cases hl
        rw [h1, hm, hmin, UInt64.ofNat_toNat] at heq
        by_cases hc : len.toNat ≤ lmIsizeMax
        · have hnot : ¬ ((9223372036854775807 : UInt64) < len) := fun h => (hkey.mp h) hc
          simp only [Size.ofBytes, hnot, ↓reduceIte] at heq
          cases heq
        · have hbig : (9223372036854775807 : UInt64) < len := hkey.mpr hc
          simp only [Size.ofBytes, hbig, ↓reduceIte] at heq
          cases heq
          simp [hc]
      next e s2 hl => cases hl
    next e s1 h_m => cases h_m

/-- `D1` **universal ZST `[()]` law**: vendored `sizeAndAlignFromMeta` on `[()]` ALWAYS returns
`(Size.ZERO, Align.ONE)` for EVERY 64-bit length `len` (never overflows `isize::MAX`). -/
theorem lm_sizeAndAlign_sliceUnit (n : Nat) (s : Scalar Provenance) (len : UInt64)
    (hs : s.toTargetUsize (Size.fromBits lmLayout.pointerWidth.bits) = .ok len) :
    lmRun (DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 1) (.metadata s)
        ⟨lmWdTySliceUnit, lmWdSliceUnitLay⟩) = .ok (some (Size.ZERO, Align.ONE)) := by
  have h0 : zstLayoutData.size.bytes.toNat = 0 := rfl
  have ha : zstLayoutData.align.abi = Align.ONE := rfl
  have hm : lmWdMaxSize.bytes = 9223372036854775807 := rfl
  unfold DynamicLayout.sizeAndAlignFromMeta
  simp [lmRun, lmWdDynHooks, lmWdClassify, lmWdField, lmWdLift, lmWdSliceUnitLay, lmWdSliceLay,
    lmWdTySliceU32, lmWdTyHeaderSlice, lmWdTyAlign8TailU16, lmWdTyStr, lmWdTySliceUnit, lmWdTySliceU16,
    LayoutData.isSized, BackendRepr.isSized, BackendRepr.isUnsized, lmLayout]
  have hs' : s.toTargetUsize (Size.fromBits PointerWidth.w64.bits) = .ok len := hs
  simp only [bind, EStateM.bind, pure]
  split
  next a st heq =>
    split at heq
    next x s1 h_m =>
      cases h_m; rw [hs'] at heq; simp only [Except.mapError] at heq
      split at heq
      next b s2 hl =>
        cases hl; simp [h0, ha, hm, Size.ofBytes] at heq; cases heq; rfl
      next e s2 hl => cases hl
    next e s1 h_m => cases h_m
  next e st heq =>
    split at heq
    next x s1 h_m =>
      cases h_m; rw [hs'] at heq; simp only [Except.mapError] at heq
      split at heq
      next b s2 hl =>
        cases hl; simp [h0, hm, Size.ofBytes, EStateM.pure] at heq
      next e s2 hl => cases hl
    next e s1 h_m => cases h_m

private theorem lm_sizeAndAlign_sliceU16 (n : Nat) (s : Scalar Provenance) (len : UInt64)
    (hs : s.toTargetUsize (Size.fromBits lmLayout.pointerWidth.bits) = .ok len) :
    lmRun (DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 1) (.metadata s)
        ⟨lmWdTySliceU16, lmWdSliceU16Lay⟩) =
      if 2 * len.toNat ≤ lmIsizeMax then
        .ok (some (Size.ofBytes (UInt64.ofNat (2 * len.toNat)), lmWdU16Lay.align.abi))
      else .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") := by
  have h2 : lmWdU16Lay.size.bytes.toNat = 2 := rfl
  have hm : lmWdMaxSize.bytes = 9223372036854775807 := rfl
  have hkey : (9223372036854775807 : UInt64) <
      (Size.ofBytes (UInt64.ofNat (min (2 * len.toNat) 18446744073709551615))).bytes ↔
      ¬ 2 * len.toNat ≤ lmIsizeMax := by
    show (9223372036854775807 : UInt64) < UInt64.ofNat (min (2 * len.toNat) 18446744073709551615) ↔ _
    rw [UInt64.lt_iff_toNat_lt]; simp; unfold lmIsizeMax; omega
  have hmin : 2 * len.toNat ≤ lmIsizeMax → min (2 * len.toNat) 18446744073709551615 = 2 * len.toNat := by
    unfold lmIsizeMax; omega
  unfold DynamicLayout.sizeAndAlignFromMeta
  simp [lmRun, lmWdDynHooks, lmWdClassify, lmWdField, lmWdLift, lmWdSliceU16Lay, lmWdSliceLay,
    lmWdTySliceU32, lmWdTyHeaderSlice, lmWdTyAlign8TailU16, lmWdTyStr, lmWdTySliceUnit, lmWdTySliceU16,
    LayoutData.isSized, BackendRepr.isSized, BackendRepr.isUnsized, lmLayout]
  have hs' : s.toTargetUsize (Size.fromBits PointerWidth.w64.bits) = .ok len := hs
  simp only [bind, EStateM.bind, pure]
  split
  next a st heq =>
    split at heq
    next x s1 h_m =>
      cases h_m; rw [hs'] at heq; simp only [Except.mapError] at heq
      split at heq
      next b s2 hl =>
        cases hl; rw [h2, hm] at heq
        by_cases hc : 2 * len.toNat ≤ lmIsizeMax
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => (hkey.mp h) hc)), hmin hc] at heq
          cases heq; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]; simp
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (hkey.mpr hc))] at heq; cases heq
      next e s2 hl => cases hl
    next e s1 h_m => cases h_m
  next e st heq =>
    split at heq
    next x s1 h_m =>
      cases h_m; rw [hs'] at heq; simp only [Except.mapError] at heq
      split at heq
      next b s2 hl =>
        cases hl; rw [h2, hm] at heq
        by_cases hc : 2 * len.toNat ≤ lmIsizeMax
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => (hkey.mp h) hc))] at heq; cases heq
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (hkey.mpr hc))] at heq
          cases heq; rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      next e s2 hl => cases hl
    next e s1 h_m => cases h_m

private theorem u64_land_clear_low2 (x : Nat) (hx : x < 2 ^ 64) :
    UInt64.land (UInt64.ofNat x) (~~~(3 : UInt64)) = UInt64.ofNat (x / 4 * 4) := by
  apply UInt64.toNat_inj.mp
  change ((UInt64.ofNat x) &&& (~~~(3 : UInt64))).toNat = (UInt64.ofNat (x / 4 * 4)).toNat
  rw [UInt64.toNat_and]
  have hx1 : (UInt64.ofNat x).toNat = x := by simp [Nat.mod_eq_of_lt hx]
  have hx2 : (UInt64.ofNat (x / 4 * 4)).toNat = x / 4 * 4 := by
    simp [Nat.mod_eq_of_lt (by omega : x / 4 * 4 < 2 ^ 64)]
  rw [hx1, hx2]
  have hm : (~~~(3 : UInt64)).toNat = 18446744073709551612 := by decide
  rw [hm]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and]
  have h1 : (x / 4 * 4).testBit k = (decide (2 ≤ k) && x.testBit k) := by
    rw [Nat.mul_comm, show (4 : Nat) = 2 ^ 2 from rfl, Nat.testBit_two_pow_mul]
    by_cases hk : 2 ≤ k
    · rw [decide_eq_true hk, show x / 4 = x / 2 ^ 2 from rfl,
        Nat.testBit_div_two_pow, Nat.sub_add_cancel hk, Bool.true_and]
    · simp [hk]
  rw [h1]
  by_cases hk2 : k < 2
  · have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · have hb0 : (18446744073709551612 : Nat).testBit 0 = false := by decide
      simp [hb0]
    · have hb1 : (18446744073709551612 : Nat).testBit 1 = false := by decide
      simp [hb1]
  · by_cases hk64 : k < 64
    · have hb : (18446744073709551612 : Nat).testBit k = true := by
        have hmul : (18446744073709551612 : Nat) = 2 ^ 2 * (2 ^ 62 - 1) := by decide
        rw [hmul, Nat.testBit_two_pow_mul]
        have hge : 2 ≤ k := by omega
        rw [decide_eq_true hge, Bool.true_and, Nat.testBit_two_pow_sub_one]
        exact decide_eq_true (by omega)
      simp [hb, show 2 ≤ k by omega]
    · have hxk : x.testBit k = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hxk]

private theorem u64_land_clear_low3 (x : Nat) (hx : x < 2 ^ 64) :
    UInt64.land (UInt64.ofNat x) (~~~(7 : UInt64)) = UInt64.ofNat (x / 8 * 8) := by
  apply UInt64.toNat_inj.mp
  change ((UInt64.ofNat x) &&& (~~~(7 : UInt64))).toNat = (UInt64.ofNat (x / 8 * 8)).toNat
  rw [UInt64.toNat_and]
  have hx1 : (UInt64.ofNat x).toNat = x := by simp [Nat.mod_eq_of_lt hx]
  have hx2 : (UInt64.ofNat (x / 8 * 8)).toNat = x / 8 * 8 := by
    simp [Nat.mod_eq_of_lt (by omega : x / 8 * 8 < 2 ^ 64)]
  rw [hx1, hx2]
  have hm : (~~~(7 : UInt64)).toNat = 18446744073709551608 := by decide
  rw [hm]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and]
  have h1 : (x / 8 * 8).testBit k = (decide (3 ≤ k) && x.testBit k) := by
    rw [Nat.mul_comm, show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_two_pow_mul]
    by_cases hk : 3 ≤ k
    · rw [decide_eq_true hk, show x / 8 = x / 2 ^ 3 from rfl,
        Nat.testBit_div_two_pow, Nat.sub_add_cancel hk, Bool.true_and]
    · simp [hk]
  rw [h1]
  by_cases hk3 : k < 3
  · have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl
    · have hb0 : (18446744073709551608 : Nat).testBit 0 = false := by decide
      simp [hb0]
    · have hb1 : (18446744073709551608 : Nat).testBit 1 = false := by decide
      simp [hb1]
    · have hb2 : (18446744073709551608 : Nat).testBit 2 = false := by decide
      simp [hb2]
  · by_cases hk64 : k < 64
    · have hb : (18446744073709551608 : Nat).testBit k = true := by
        have hmul : (18446744073709551608 : Nat) = 2 ^ 3 * (2 ^ 61 - 1) := by decide
        rw [hmul, Nat.testBit_two_pow_mul]
        have hge : 3 ≤ k := by omega
        rw [decide_eq_true hge, Bool.true_and, Nat.testBit_two_pow_sub_one]
        exact decide_eq_true (by omega)
      simp [hb, show 3 ≤ k by omega]
    · have hxk : x.testBit k = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hxk]

private theorem size_alignTo4_eq (x : Nat) (hx : x + 3 < 2 ^ 64) :
    Size.alignTo (Size.ofBytes (UInt64.ofNat x)) ⟨2⟩ = .ok (Size.ofBytes (UInt64.ofNat ((x + 3) / 4 * 4))) := by
  have hb : Align.bytes ⟨2⟩ = .ok (4 : UInt64) := rfl
  have h3 : (4 : UInt64) - 1 = 3 := rfl
  have hadd : UInt64.ofNat x + (3 : UInt64) = UInt64.ofNat (x + 3) :=
    UInt64.toNat_inj.mp (by simp)
  have hlt : ¬ (UInt64.ofNat (x + 3) < UInt64.ofNat x) := by
    rw [UInt64.lt_iff_toNat_lt]; simp; omega
  unfold Size.alignTo
  simp only [hb, Size.ofBytes, bind, Except.bind, pure, Except.pure, h3]
  rw [hadd]
  simp only [hlt, ↓reduceIte]
  exact congrArg (Except.ok ∘ Size.mk) (u64_land_clear_low2 (x + 3) hx)

private theorem size_alignTo8_eq (x : Nat) (hx : x + 7 < 2 ^ 64) :
    Size.alignTo (Size.ofBytes (UInt64.ofNat x)) ⟨3⟩ = .ok (Size.ofBytes (UInt64.ofNat ((x + 7) / 8 * 8))) := by
  have hb : Align.bytes ⟨3⟩ = .ok (8 : UInt64) := rfl
  have h7 : (8 : UInt64) - 1 = 7 := rfl
  have hadd : UInt64.ofNat x + (7 : UInt64) = UInt64.ofNat (x + 7) :=
    UInt64.toNat_inj.mp (by simp)
  have hlt : ¬ (UInt64.ofNat (x + 7) < UInt64.ofNat x) := by
    rw [UInt64.lt_iff_toNat_lt]; simp; omega
  unfold Size.alignTo
  simp only [hb, Size.ofBytes, bind, Except.bind, pure, Except.pure, h7]
  rw [hadd]
  simp only [hlt, ↓reduceIte]
  exact congrArg (Except.ok ∘ Size.mk) (u64_land_clear_low3 (x + 7) hx)

private theorem size_add_ofNat_eq (a b : Nat) (hab : a + b < 2 ^ 64) :
    Size.add (Size.ofBytes (UInt64.ofNat a)) (Size.ofBytes (UInt64.ofNat b)) =
      .ok (Size.ofBytes (UInt64.ofNat (a + b))) := by
  have hadd : UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b) :=
    UInt64.toNat_inj.mp (by simp)
  have hlt : ¬ (UInt64.ofNat (a + b) < UInt64.ofNat a) := by
    rw [UInt64.lt_iff_toNat_lt]; simp; omega
  unfold Size.add
  simp only [Size.ofBytes, hadd, hlt, ↓reduceIte]

section DynPrivUnfold
open Lean Elab Tactic Meta in
/-- Delta-unfold the vendored `DynamicLayout` private `addSize` / `alignTo` / `liftResult`
wrappers in a local hypothesis (pure definitional unfolding, zero axioms). -/
local elab "unfold_dyn_priv" "at" h:ident : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let env ← getEnv
    let mut privs : Array Name := #[]
    for target in [`Miri.Interpreter.DynamicLayout.addSize,
                   `Miri.Interpreter.DynamicLayout.alignTo,
                   `Miri.Interpreter.DynamicLayout.liftResult] do
      for (c, _) in env.constants.map₁.toList do
        if privateToUserName? c == some target then
          privs := privs.push c
    let lctx ← getLCtx
    let some ldecl := lctx.findFromUserName? h.getId
      | throwError "unknown local hypothesis {h}"
    let mut ty := ldecl.type
    for p in privs do
      ty := (← Lean.Meta.unfold ty p).expr
    let mvarId' ← mvarId.replaceLocalDeclDefEq ldecl.fvarId ty
    replaceMainGoal [mvarId']

/-- `D1` **TRUE UNIVERSAL `HeaderSlice` law** (`#[repr(C)] struct HeaderSlice { tag: u8, data: [u32] }`):
for EVERY 64-bit `len` (not just `n < 32`!), vendored `sizeAndAlignFromMeta` (`.adt false` arm)
computes `size = 4 + 4 * len`, `align = 4` when `4 + 4 * len ≤ isize::MAX`,
`InvalidMeta(TooBig)` when the struct header pushes `4 + 4 * len` past `isize::MAX`, and
`InvalidMeta(SliceTooBig)` when `4 * len > isize::MAX`. -/
theorem lm_sizeAndAlign_headerSlice (n : Nat) (s : Scalar Provenance) (len : UInt64)
    (hs : s.toTargetUsize (Size.fromBits lmLayout.pointerWidth.bits) = .ok len) :
    lmRun (DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 2) (.metadata s)
        ⟨lmWdTyHeaderSlice, lmWdHeaderSliceLay⟩) =
      if 4 * len.toNat ≤ lmIsizeMax then
        if 4 + 4 * len.toNat ≤ lmIsizeMax then
          .ok (some (Size.ofBytes (UInt64.ofNat (4 + 4 * len.toNat)), ⟨2⟩))
        else .error (.undefinedBehavior "InvalidMeta(TooBig)")
      else .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") := by
  have hTail := lm_sizeAndAlign_sliceU32 n s len hs
  have hAlignU32 : lmWdU32Lay.align.abi = ⟨2⟩ := rfl
  have hTailRaw :
      DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 1) (.metadata s)
          ⟨lmWdTySliceU32, lmWdSliceU32Lay⟩ () =
        if 4 * len.toNat ≤ lmIsizeMax then
          .ok (some (Size.ofBytes (UInt64.ofNat (4 * len.toNat)), ⟨2⟩)) ()
        else .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") () := by
    unfold lmRun at hTail
    rw [hAlignU32] at hTail
    cases hr : DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 1) (.metadata s)
        ⟨lmWdTySliceU32, lmWdSliceU32Lay⟩ () with
    | ok v u =>
      cases u; rw [hr] at hTail
      by_cases h4 : 4 * len.toNat ≤ lmIsizeMax
      · simp only [h4, ↓reduceIte, Except.ok.injEq] at hTail; simp [h4, hTail]
      · simp [h4] at hTail
    | error e u =>
      cases u; rw [hr] at hTail
      by_cases h4 : 4 * len.toNat ≤ lmIsizeMax
      · simp [h4] at hTail
      · simp only [h4, ↓reduceIte, Except.error.injEq] at hTail; simp [h4, hTail]
  have hAlignOff : Size.alignTo (Size.ofBytes 4) ⟨2⟩ = .ok (Size.ofBytes 4) := by decide
  have hmax : lmWdMaxSize.bytes = 9223372036854775807 := rfl
  unfold lmRun
  by_cases h4 : 4 * len.toNat ≤ lmIsizeMax
  · have hTailOk :
        DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 1) (.metadata s)
            ⟨lmWdTySliceU32, lmWdSliceU32Lay⟩ () =
          .ok (some (Size.ofBytes (UInt64.ofNat (4 * len.toNat)), ⟨2⟩)) () := by
      simpa [h4] using hTailRaw
    have h4lt : 4 + 4 * len.toNat + 3 < 2 ^ 64 := by unfold lmIsizeMax at h4; omega
    have hAdd : Size.add (Size.ofBytes 4) (Size.ofBytes (UInt64.ofNat (4 * len.toNat))) =
        .ok (Size.ofBytes (UInt64.ofNat (4 + 4 * len.toNat))) :=
      size_add_ofNat_eq 4 (4 * len.toNat) (by omega)
    have hAlignFull : Size.alignTo (Size.ofBytes (UInt64.ofNat (4 + 4 * len.toNat))) ⟨2⟩ =
        .ok (Size.ofBytes (UInt64.ofNat (4 + 4 * len.toNat))) := by
      rw [size_alignTo4_eq (4 + 4 * len.toNat) h4lt]
      have hdiv : (4 + 4 * len.toNat + 3) / 4 * 4 = 4 + 4 * len.toNat := by omega
      rw [hdiv]
    have hExec :
        DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 2) (.metadata s)
            ⟨lmWdTyHeaderSlice, lmWdHeaderSliceLay⟩ () =
          if (Size.ofBytes (UInt64.ofNat (4 + 4 * len.toNat))).bytes > lmWdMaxSize.bytes then
            .error (.undefinedBehavior "InvalidMeta(TooBig)") ()
          else .ok (some (Size.ofBytes (UInt64.ofNat (4 + 4 * len.toNat)), ⟨2⟩)) () := by
      have hSized : lmWdHeaderSliceLay.isSized = false := rfl
      have hCls : lmWdDynHooks.classify () lmWdTyHeaderSlice = pure (.adt false) := rfl
      have hCnt : lmWdHeaderSliceLay.fields.count = 2 := rfl
      have h20 : ((2 : Nat) == 0) = false := rfl
      have hOff : lmWdHeaderSliceLay.fields.offset (2 - 1) = .ok (Size.ofBytes 4) := rfl
      have hFld : lmWdDynHooks.field () ⟨lmWdTyHeaderSlice, lmWdHeaderSliceLay⟩ (2 - 1) =
          pure ⟨lmWdTySliceU32, lmWdSliceU32Lay⟩ := rfl
      have hPack : lmWdDynHooks.packedAlign () lmWdTyHeaderSlice = pure none := rfl
      have hAbi : lmWdHeaderSliceLay.align.abi = ⟨2⟩ := rfl
      unfold DynamicLayout.sizeAndAlignFromMeta
      simp only [hSized, Bool.false_eq_true, ↓reduceIte, hCls, hCnt, h20, hOff, hFld, hPack, hAbi,
        Except.mapError, bind, EStateM.bind, pure, EStateM.pure]
      split
      next a s1 hl =>
        cases hl
        rw [hTailOk]
        simp only [EStateM.bind, EStateM.pure]
        split
        next adj s2 hl1 =>
          unfold_dyn_priv at hl1; rw [hAlignOff] at hl1
          simp only [Except.mapError, pure, EStateM.pure] at hl1; cases hl1
          split
          next sum1 s3 hl2 =>
            unfold_dyn_priv at hl2; rw [hAdd] at hl2
            simp only [Except.mapError, pure, EStateM.pure] at hl2; cases hl2
            split
            next fs s4 hl3 =>
              unfold_dyn_priv at hl3
              have hMax22 : Align.max ⟨2⟩ ⟨2⟩ = ⟨2⟩ := rfl
              rw [hMax22, hAlignFull] at hl3
              simp only [Except.mapError, pure, EStateM.pure] at hl3; cases hl3
              split
              next sum2 s5 hl4 =>
                unfold_dyn_priv at hl4; rw [hAdd] at hl4
                simp only [Except.mapError, pure, EStateM.pure] at hl4; cases hl4
                split
                next cs s6 hl5 =>
                  unfold_dyn_priv at hl5; rw [hMax22, hAlignFull] at hl5
                  simp only [Except.mapError, pure, EStateM.pure] at hl5; cases hl5
                  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
                  by_cases hgt : (Size.ofBytes (UInt64.ofNat (4 + 4 * len.toNat))).bytes > lmWdMaxSize.bytes
                  · have hgt' : (Size.ofBytes (UInt64.ofNat (4 + 4 * len.toNat))).bytes >
                        lmWdDynHooks.maxSizeOfVal.bytes := hgt
                    simp only [hgt, hgt', ↓reduceIte]; rfl
                  · have hgt' : ¬ ((Size.ofBytes (UInt64.ofNat (4 + 4 * len.toNat))).bytes >
                        lmWdDynHooks.maxSizeOfVal.bytes) := hgt
                    simp only [hgt, hgt', ↓reduceIte]; rfl
                next e s6 hl5 =>
                  unfold_dyn_priv at hl5; rw [hMax22, hAlignFull] at hl5
                  simp only [Except.mapError, pure, EStateM.pure] at hl5; cases hl5
              next e s5 hl4 =>
                unfold_dyn_priv at hl4; rw [hAdd] at hl4
                simp only [Except.mapError, pure, EStateM.pure] at hl4; cases hl4
            next e s4 hl3 =>
              unfold_dyn_priv at hl3
              have hMax22 : Align.max ⟨2⟩ ⟨2⟩ = ⟨2⟩ := rfl
              rw [hMax22, hAlignFull] at hl3
              simp only [Except.mapError, pure, EStateM.pure] at hl3; cases hl3
          next e s3 hl2 =>
            unfold_dyn_priv at hl2; rw [hAdd] at hl2
            simp only [Except.mapError, pure, EStateM.pure] at hl2; cases hl2
        next e s2 hl1 =>
          unfold_dyn_priv at hl1; rw [hAlignOff] at hl1
          simp only [Except.mapError, pure, EStateM.pure] at hl1; cases hl1
      next e s1 hl => cases hl
    rw [hExec]
    have hcmp : (9223372036854775807 : UInt64) < UInt64.ofNat (4 + 4 * len.toNat) ↔
        ¬ (4 + 4 * len.toNat ≤ lmIsizeMax) := by
      rw [UInt64.lt_iff_toNat_lt]; unfold lmIsizeMax; simp; omega
    simp only [h4, ↓reduceIte, Size.ofBytes, hmax, gt_iff_lt]
    by_cases hfull : 4 + 4 * len.toNat ≤ lmIsizeMax
    · have hnot : ¬ ((9223372036854775807 : UInt64) < UInt64.ofNat (4 + 4 * len.toNat)) :=
        fun h => (hcmp.mp h) hfull
      simp only [hfull, ↓reduceIte, hnot]
    · have hgt : (9223372036854775807 : UInt64) < UInt64.ofNat (4 + 4 * len.toNat) := hcmp.mpr hfull
      simp only [hfull, ↓reduceIte, hgt]
  · have hTailErr :
        DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 1) (.metadata s)
            ⟨lmWdTySliceU32, lmWdSliceU32Lay⟩ () =
          .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") () := by
      simpa [h4] using hTailRaw
    have hExec :
        DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 2) (.metadata s)
            ⟨lmWdTyHeaderSlice, lmWdHeaderSliceLay⟩ () =
          .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") () := by
      have hSized : lmWdHeaderSliceLay.isSized = false := rfl
      have hCls : lmWdDynHooks.classify () lmWdTyHeaderSlice = pure (.adt false) := rfl
      have hCnt : lmWdHeaderSliceLay.fields.count = 2 := rfl
      have h20 : ((2 : Nat) == 0) = false := rfl
      have hOff : lmWdHeaderSliceLay.fields.offset (2 - 1) = .ok (Size.ofBytes 4) := rfl
      have hFld : lmWdDynHooks.field () ⟨lmWdTyHeaderSlice, lmWdHeaderSliceLay⟩ (2 - 1) =
          pure ⟨lmWdTySliceU32, lmWdSliceU32Lay⟩ := rfl
      unfold DynamicLayout.sizeAndAlignFromMeta
      simp only [hSized, Bool.false_eq_true, ↓reduceIte, hCls, hCnt, h20, hOff, hFld,
        Except.mapError, bind, EStateM.bind, pure, EStateM.pure]
      split
      next a s1 hl => cases hl; simp [hTailErr]
      next e s1 hl => cases hl
    simp [hExec, h4]

/-- `D1` **TRUE UNIVERSAL `Align8TailU16` law** (`#[repr(C)] struct Align8TailU16 { hdr: u64, tail: [u16] }`):
for EVERY 64-bit `len` (not just `n < 32`!), vendored `sizeAndAlignFromMeta` (`.adt false` arm)
computes the exact struct-alignment tail padding `size = align_to(8 + 2 * len, 8)`, `align = 8`
when `align_to(8 + 2 * len, 8) ≤ isize::MAX`, `InvalidMeta(TooBig)` in the tail-padding overflow
window, and `InvalidMeta(SliceTooBig)` when `2 * len > isize::MAX`. -/
theorem lm_sizeAndAlign_align8TailU16 (n : Nat) (s : Scalar Provenance) (len : UInt64)
    (hs : s.toTargetUsize (Size.fromBits lmLayout.pointerWidth.bits) = .ok len) :
    lmRun (DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 2) (.metadata s)
        ⟨lmWdTyAlign8TailU16, lmWdAlign8TailU16Lay⟩) =
      if 2 * len.toNat ≤ lmIsizeMax then
        if (8 + 2 * len.toNat + 7) / 8 * 8 ≤ lmIsizeMax then
          .ok (some (Size.ofBytes (UInt64.ofNat ((8 + 2 * len.toNat + 7) / 8 * 8)), ⟨3⟩))
        else .error (.undefinedBehavior "InvalidMeta(TooBig)")
      else .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") := by
  have hTail := lm_sizeAndAlign_sliceU16 n s len hs
  have hAlignU16 : lmWdU16Lay.align.abi = ⟨1⟩ := rfl
  have hTailRaw :
      DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 1) (.metadata s)
          ⟨lmWdTySliceU16, lmWdSliceU16Lay⟩ () =
        if 2 * len.toNat ≤ lmIsizeMax then
          .ok (some (Size.ofBytes (UInt64.ofNat (2 * len.toNat)), ⟨1⟩)) ()
        else .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") () := by
    unfold lmRun at hTail
    rw [hAlignU16] at hTail
    cases hr : DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 1) (.metadata s)
        ⟨lmWdTySliceU16, lmWdSliceU16Lay⟩ () with
    | ok v u =>
      cases u; rw [hr] at hTail
      by_cases h2 : 2 * len.toNat ≤ lmIsizeMax
      · simp only [h2, ↓reduceIte, Except.ok.injEq] at hTail; simp [h2, hTail]
      · simp [h2] at hTail
    | error e u =>
      cases u; rw [hr] at hTail
      by_cases h2 : 2 * len.toNat ≤ lmIsizeMax
      · simp [h2] at hTail
      · simp only [h2, ↓reduceIte, Except.error.injEq] at hTail; simp [h2, hTail]
  have hAlignOff : Size.alignTo (Size.ofBytes 8) ⟨1⟩ = .ok (Size.ofBytes 8) := by decide
  have hmax : lmWdMaxSize.bytes = 9223372036854775807 := rfl
  unfold lmRun
  by_cases h2 : 2 * len.toNat ≤ lmIsizeMax
  · have hTailOk :
        DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 1) (.metadata s)
            ⟨lmWdTySliceU16, lmWdSliceU16Lay⟩ () =
          .ok (some (Size.ofBytes (UInt64.ofNat (2 * len.toNat)), ⟨1⟩)) () := by
      simpa [h2] using hTailRaw
    have h8lt : 8 + 2 * len.toNat + 7 < 2 ^ 64 := by unfold lmIsizeMax at h2; omega
    have hAdd : Size.add (Size.ofBytes 8) (Size.ofBytes (UInt64.ofNat (2 * len.toNat))) =
        .ok (Size.ofBytes (UInt64.ofNat (8 + 2 * len.toNat))) :=
      size_add_ofNat_eq 8 (2 * len.toNat) (by omega)
    have hAlignFull : Size.alignTo (Size.ofBytes (UInt64.ofNat (8 + 2 * len.toNat))) ⟨3⟩ =
        .ok (Size.ofBytes (UInt64.ofNat ((8 + 2 * len.toNat + 7) / 8 * 8))) :=
      size_alignTo8_eq (8 + 2 * len.toNat) h8lt
    have hExec :
        DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 2) (.metadata s)
            ⟨lmWdTyAlign8TailU16, lmWdAlign8TailU16Lay⟩ () =
          if (Size.ofBytes (UInt64.ofNat ((8 + 2 * len.toNat + 7) / 8 * 8))).bytes > lmWdMaxSize.bytes then
            .error (.undefinedBehavior "InvalidMeta(TooBig)") ()
          else .ok (some (Size.ofBytes (UInt64.ofNat ((8 + 2 * len.toNat + 7) / 8 * 8)), ⟨3⟩)) () := by
      have hSized : lmWdAlign8TailU16Lay.isSized = false := rfl
      have hCls : lmWdDynHooks.classify () lmWdTyAlign8TailU16 = pure (.adt false) := rfl
      have hCnt : lmWdAlign8TailU16Lay.fields.count = 2 := rfl
      have h20 : ((2 : Nat) == 0) = false := rfl
      have hOff : lmWdAlign8TailU16Lay.fields.offset (2 - 1) = .ok (Size.ofBytes 8) := rfl
      have hFld : lmWdDynHooks.field () ⟨lmWdTyAlign8TailU16, lmWdAlign8TailU16Lay⟩ (2 - 1) =
          pure ⟨lmWdTySliceU16, lmWdSliceU16Lay⟩ := rfl
      have hPack : lmWdDynHooks.packedAlign () lmWdTyAlign8TailU16 = pure none := rfl
      have hAbi : lmWdAlign8TailU16Lay.align.abi = ⟨3⟩ := rfl
      unfold DynamicLayout.sizeAndAlignFromMeta
      simp only [hSized, Bool.false_eq_true, ↓reduceIte, hCls, hCnt, h20, hOff, hFld, hPack, hAbi,
        Except.mapError, bind, EStateM.bind, pure, EStateM.pure]
      split
      next a s1 hl =>
        cases hl
        rw [hTailOk]
        simp only [EStateM.bind, EStateM.pure]
        split
        next adj s2 hl1 =>
          unfold_dyn_priv at hl1; rw [hAlignOff] at hl1
          simp only [Except.mapError, pure, EStateM.pure] at hl1; cases hl1
          split
          next sum1 s3 hl2 =>
            unfold_dyn_priv at hl2; rw [hAdd] at hl2
            simp only [Except.mapError, pure, EStateM.pure] at hl2; cases hl2
            split
            next fs s4 hl3 =>
              unfold_dyn_priv at hl3
              have hMax31 : Align.max ⟨3⟩ ⟨1⟩ = ⟨3⟩ := rfl
              rw [hMax31, hAlignFull] at hl3
              simp only [Except.mapError, pure, EStateM.pure] at hl3; cases hl3
              split
              next sum2 s5 hl4 =>
                unfold_dyn_priv at hl4; rw [hAdd] at hl4
                simp only [Except.mapError, pure, EStateM.pure] at hl4; cases hl4
                split
                next cs s6 hl5 =>
                  unfold_dyn_priv at hl5; rw [hMax31, hAlignFull] at hl5
                  simp only [Except.mapError, pure, EStateM.pure] at hl5; cases hl5
                  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
                  by_cases hgt : (Size.ofBytes (UInt64.ofNat ((8 + 2 * len.toNat + 7) / 8 * 8))).bytes >
                      lmWdMaxSize.bytes
                  · have hgt' : (Size.ofBytes (UInt64.ofNat ((8 + 2 * len.toNat + 7) / 8 * 8))).bytes >
                        lmWdDynHooks.maxSizeOfVal.bytes := hgt
                    simp only [hgt, hgt', ↓reduceIte]; rfl
                  · have hgt' : ¬ ((Size.ofBytes (UInt64.ofNat ((8 + 2 * len.toNat + 7) / 8 * 8))).bytes >
                        lmWdDynHooks.maxSizeOfVal.bytes) := hgt
                    simp only [hgt, hgt', ↓reduceIte]; rfl
                next e s6 hl5 =>
                  unfold_dyn_priv at hl5; rw [hMax31, hAlignFull] at hl5
                  simp only [Except.mapError, pure, EStateM.pure] at hl5; cases hl5
              next e s5 hl4 =>
                unfold_dyn_priv at hl4; rw [hAdd] at hl4
                simp only [Except.mapError, pure, EStateM.pure] at hl4; cases hl4
            next e s4 hl3 =>
              unfold_dyn_priv at hl3
              have hMax31 : Align.max ⟨3⟩ ⟨1⟩ = ⟨3⟩ := rfl
              rw [hMax31, hAlignFull] at hl3
              simp only [Except.mapError, pure, EStateM.pure] at hl3; cases hl3
          next e s3 hl2 =>
            unfold_dyn_priv at hl2; rw [hAdd] at hl2
            simp only [Except.mapError, pure, EStateM.pure] at hl2; cases hl2
        next e s2 hl1 =>
          unfold_dyn_priv at hl1; rw [hAlignOff] at hl1
          simp only [Except.mapError, pure, EStateM.pure] at hl1; cases hl1
      next e s1 hl => cases hl
    rw [hExec]
    have hcmp : (9223372036854775807 : UInt64) < UInt64.ofNat ((8 + 2 * len.toNat + 7) / 8 * 8) ↔
        ¬ ((8 + 2 * len.toNat + 7) / 8 * 8 ≤ lmIsizeMax) := by
      rw [UInt64.lt_iff_toNat_lt]; unfold lmIsizeMax; simp; omega
    simp only [h2, ↓reduceIte, Size.ofBytes, hmax, gt_iff_lt]
    by_cases hfull : (8 + 2 * len.toNat + 7) / 8 * 8 ≤ lmIsizeMax
    · have hnot : ¬ ((9223372036854775807 : UInt64) < UInt64.ofNat ((8 + 2 * len.toNat + 7) / 8 * 8)) :=
        fun h => (hcmp.mp h) hfull
      simp only [hfull, ↓reduceIte, hnot]
    · have hgt : (9223372036854775807 : UInt64) < UInt64.ofNat ((8 + 2 * len.toNat + 7) / 8 * 8) := hcmp.mpr hfull
      simp only [hfull, ↓reduceIte, hgt]
  · have hTailErr :
        DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 1) (.metadata s)
            ⟨lmWdTySliceU16, lmWdSliceU16Lay⟩ () =
          .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") () := by
      simpa [h2] using hTailRaw
    have hExec :
        DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 2) (.metadata s)
            ⟨lmWdTyAlign8TailU16, lmWdAlign8TailU16Lay⟩ () =
          .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") () := by
      have hSized : lmWdAlign8TailU16Lay.isSized = false := rfl
      have hCls : lmWdDynHooks.classify () lmWdTyAlign8TailU16 = pure (.adt false) := rfl
      have hCnt : lmWdAlign8TailU16Lay.fields.count = 2 := rfl
      have h20 : ((2 : Nat) == 0) = false := rfl
      have hOff : lmWdAlign8TailU16Lay.fields.offset (2 - 1) = .ok (Size.ofBytes 8) := rfl
      have hFld : lmWdDynHooks.field () ⟨lmWdTyAlign8TailU16, lmWdAlign8TailU16Lay⟩ (2 - 1) =
          pure ⟨lmWdTySliceU16, lmWdSliceU16Lay⟩ := rfl
      unfold DynamicLayout.sizeAndAlignFromMeta
      simp only [hSized, Bool.false_eq_true, ↓reduceIte, hCls, hCnt, h20, hOff, hFld,
        Except.mapError, bind, EStateM.bind, pure, EStateM.pure]
      split
      next a s1 hl => cases hl; simp [hTailErr]
      next e s1 hl => cases hl
    simp [hExec, h2]

end DynPrivUnfold

/-- `D2` **universal `InitMask` uninit-byte query law**: every byte of a fresh uninitialized
`InitMask` reads `false` via `InitMask.get`. -/
theorem lm_initMask_uninit_get (size idx : Size) :
    (InitMask.new size false).get idx = .ok false :=
  InitMask.lazy_get size idx false

/-- `D2` **universal `InitMask` uninit-range law**: every in-bounds range in a fresh uninitialized
`InitMask` reports uninitialized (`isRangeInitialized = .ok (.error range)`). -/
theorem lm_initMask_uninit_isRangeInitialized (size finish : Size) (range : AllocRange)
    (hEnd : range.endExclusive = .ok finish) (hIn : finish.bytes ≤ size.bytes) :
    (InitMask.new size false).isRangeInitialized range = .ok (.error range) :=
  InitMask.lazy_uninitialized_query size range finish hEnd hIn

/-- `D2` **universal `InitMask.applyCopy` uninit-preservation law**: applying a single-run
uninitialized copy (`InitCopy ⟨false, #[n]⟩`, `n ≠ 0`, `noBytesInit = true`) over a full
destination `InitMask` (even one that was previously initialized!) succeeds and leaves the
destination lazily uninitialized (`InitMask.new finish false`), preserving uninit bytes without UB. -/
theorem lm_initMask_applyCopy_uninit_preserves (size finish : Size) (oldState : Bool)
    (range : AllocRange) (n : UInt64)
    (hNonZero : n ≠ 0)
    (hEnd : range.endExclusive = .ok finish)
    (hStart : range.start.bytes = 0)
    (hFull : size.bytes ≤ finish.bytes) :
    (InitMask.new size oldState).applyCopy ⟨false, #[n]⟩ range 1 =
      .ok (InitMask.new finish false) ∧
    InitCopy.noBytesInit ⟨false, #[n]⟩ = true := by
  have hMul : Size.mul range.size 1 = .ok range.size := by
    have h1 : range.size.bytes * 1 = range.size.bytes := UInt64.mul_one _
    have hd : range.size.bytes / 1 = range.size.bytes := UInt64.div_one
    simp [Size.mul, h1, hd, Size.ofBytes]
  have hEmpty : (#[n] : Array UInt64).isEmpty = false := rfl
  have hSize : (#[n] : Array UInt64).size = 1 := rfl
  have hNotAny : (#[n].any (fun a => a == 0) 0 1) = false := by
    simp [hNonZero]
  have hRangeEq : allocRange range.start range.size = range := by
    cases range; rfl
  refine ⟨?_, rfl⟩
  unfold InitMask.applyCopy
  simp only [hEmpty, Bool.false_or, hSize, Nat.le_refl, hMul, Except.mapError, bind, Except.bind,
    hRangeEq, hNotAny, Bool.false_eq_true, ↓reduceIte]
  exact InitMask.full_overwrite_stays_lazy size finish oldState false range hEnd hStart hFull

section MemCopyUniversal
open Lean Elab Tactic Meta in
/-- Delta-unfold private `InitMask` / `ProvenanceMap` / `Allocation` helpers in the goal
(pure definitional unfolding, zero axioms). -/
local elab "unfold_mem_priv" : tactic => do
  let mut mvarId ← getMainGoal
  for target in [`Miri.Memory.sizeBytes,
                 `Miri.Memory.InitMask.collectChunksAux,
                 `Miri.Memory.ProvenanceMap.rangeEnd,
                 `Miri.Memory.ProvenanceMap.adjustedStart,
                 `Miri.Memory.ProvenanceMap.rangeEntries,
                 `Miri.Memory.ProvenanceMap.subtractSize,
                 `Miri.Memory.Allocation.prepareForOverwrite,
                 `Miri.Memory.Allocation.checkedSlice,
                 `Miri.Memory.Allocation.setInitialization,
                 `Miri.Memory.Allocation.runProvenanceMutation] do
    let env ← getEnv
    let mut privs : Array Name := #[]
    for (c, _) in env.constants.map₁.toList do
      if privateToUserName? c == some target then
        privs := privs.push c
    for p in privs do
      let (ty, r) ← mvarId.withContext do
        let ty ← mvarId.getType
        let r ← Lean.Meta.unfold ty p
        pure (ty, r)
      if r.expr != ty then
        mvarId ← mvarId.withContext do
          match r.proof? with
          | some pf => mvarId.replaceTargetEq r.expr pf
          | none => mvarId.replaceTargetDefEq r.expr
  replaceMainGoal [mvarId]

private theorem allocRange_endExclusive_props (range : AllocRange) (finish : Size)
    (hEnd : range.endExclusive = .ok finish) :
    range.start.bytes + range.size.bytes = finish.bytes ∧
    range.start.bytes.toNat + range.size.bytes.toNat = finish.bytes.toNat ∧
    range.start.bytes ≤ finish.bytes ∧
    finish.bytes - range.start.bytes = range.size.bytes := by
  unfold AllocRange.endExclusive AllocRange.end Size.add at hEnd
  simp only [Except.mapError, Size.ofBytes] at hEnd
  by_cases hlt : range.start.bytes + range.size.bytes < range.start.bytes
  · simp only [hlt, ↓reduceIte] at hEnd; cases hEnd
  · simp only [hlt, ↓reduceIte, Except.ok.injEq] at hEnd
    rw [UInt64.lt_iff_toNat_lt] at hlt
    have hsum : (range.start.bytes + range.size.bytes).toNat =
        range.start.bytes.toNat + range.size.bytes.toNat := by
      have ha := range.start.bytes.toNat_lt
      have hb := range.size.bytes.toNat_lt
      rw [UInt64.toNat_add] at hlt ⊢
      by_cases hov : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64
      · exact Nat.mod_eq_of_lt hov
      · have hmod : (range.start.bytes.toNat + range.size.bytes.toNat) % 2 ^ 64 =
            range.start.bytes.toNat + range.size.bytes.toNat - 2 ^ 64 := by
          have : range.start.bytes.toNat + range.size.bytes.toNat < 2 * 2 ^ 64 := by omega
          omega
        omega
    have hEq : finish.bytes = range.start.bytes + range.size.bytes := by rw [← hEnd]
    refine ⟨hEq.symm, by rw [hEq, hsum], ?_, ?_⟩
    · rw [hEq, UInt64.le_iff_toNat_le, hsum]; omega
    · apply UInt64.toNat_inj.mp
      rw [hEq, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hsum]; omega), hsum]
      omega

/-- `D2` **TRUE UNIVERSAL `InitMask.prepareCopy` law**: for EVERY `srcSize` and EVERY non-empty
in-bounds `range`, `prepareCopy` on a lazy-uninitialized `InitMask` succeeds and produces the
single-run uninitialized `InitCopy` (`noBytesInit = true`). -/
theorem lm_initMask_prepareCopy_lazy_uninit (srcSize : Size) (range : AllocRange) (finish : Size)
    (hNe : range.size.bytes ≠ 0)
    (hEnd : range.endExclusive = .ok finish)
    (hIn : finish.bytes ≤ srcSize.bytes) :
    (InitMask.new srcSize false).prepareCopy range = .ok ⟨false, #[range.size.bytes]⟩ := by
  obtain ⟨_, hNatSum, hLe, hSub⟩ := allocRange_endExclusive_props range finish hEnd
  have hPosNat : 0 < range.size.bytes.toNat := by
    cases h : range.size.bytes.toNat with
    | zero =>
      exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hNe
    | succ k => omega
  have hStartLt : range.start.bytes < finish.bytes := by
    rw [UInt64.lt_iff_toNat_lt]; omega
  have hNotGt : ¬ srcSize.bytes < finish.bytes := UInt64.not_lt.mpr hIn
  have hNotStartGt : ¬ finish.bytes < range.start.bytes := UInt64.not_lt.mpr hLe
  have hNotFinishLe : ¬ finish.bytes ≤ range.start.bytes := UInt64.not_le.mpr hStartLt
  have hRangeIter : (InitMask.new srcSize false).rangeAsInitChunks range =
      .ok ⟨InitMask.new srcSize false, false, range.start, finish⟩ := by
    unfold InitMask.rangeAsInitChunks
    simp only [hEnd, InitMask.new, bind, Except.bind, pure, Except.pure, gt_iff_lt, hNotGt,
      ↓reduceIte, hStartLt]
    rfl
  let iter0 : InitChunkIter := ⟨InitMask.new srcSize false, false, range.start, finish⟩
  let iter1 : InitChunkIter := ⟨InitMask.new srcSize false, true, finish, finish⟩
  have hNext0 : iter0.next? = .ok (some (.Uninit range.start finish, iter1)) := by
    unfold InitChunkIter.next?
    unfold_mem_priv
    have hge : ¬ (finish.bytes.toNat ≤ range.start.bytes.toNat) := by omega
    simp only [iter0, iter1, InitMask.new, gt_iff_lt, hNotStartGt, hNotGt, decide_false,
      Bool.or_self, Bool.false_eq_true, ↓reduceIte, ge_iff_le, hge, bne_self_eq_false,
      hNotFinishLe, bind, Except.bind, pure, Except.pure, Bool.not_false]
  have hNext1 : iter1.next? = .ok none := by
    unfold InitChunkIter.next?
    unfold_mem_priv
    have hnl : ¬ finish.bytes < finish.bytes := UInt64.lt_irrefl _
    simp only [iter1, InitMask.new, gt_iff_lt, hnl, hNotGt, decide_false, Bool.or_self,
      Bool.false_eq_true, ↓reduceIte, ge_iff_le, Nat.le_refl, pure, Except.pure]
  have hFuel1 : finish.bytes.toNat - range.start.bytes.toNat =
      (finish.bytes.toNat - range.start.bytes.toNat - 1) + 1 := by omega
  have hCollect : InitMask.collectChunks ⟨InitMask.new srcSize false, false, range.start, finish⟩ =
      .ok #[.Uninit range.start finish] := by
    change InitMask.collectChunks iter0 = .ok #[.Uninit range.start finish]
    unfold InitMask.collectChunks
    unfold_mem_priv
    simp only [hNext0, bind, Except.bind]
    have hFuel1' : iter0.finish.bytes.toNat - iter0.start.bytes.toNat =
        (finish.bytes.toNat - range.start.bytes.toNat - 1) + 1 := hFuel1
    rw [hFuel1']
    unfold_mem_priv
    simp only [hNext1, bind, Except.bind, pure, Except.pure]
    rfl
  have hFromEnd : AllocRange.fromEndpoints range.start finish = .ok ⟨range.start, range.size⟩ := by
    unfold AllocRange.fromEndpoints Size.sub
    simp only [hNotStartGt, ↓reduceIte, hSub, Except.mapError, Size.ofBytes, bind, Except.bind,
      pure, Except.pure]
  have hBeqFalse : (range.size.bytes == 0) = false := beq_false_of_ne hNe
  unfold InitMask.prepareCopy
  simp only [hBeqFalse, Bool.false_eq_true, ↓reduceIte, hRangeIter, hCollect,
    bind, Except.bind, pure, Except.pure]
  have hGet0 : (#[InitChunk.Uninit range.start finish])[0]? =
      some (InitChunk.Uninit range.start finish) := rfl
  rw [hGet0]
  simp [InitChunk.isInit, InitChunk.range, hFromEnd, bind, Except.bind, pure, Except.pure]

/-- `D2` **universal `ProvenanceMap.prepareCopy` law on empty provenance**: preparing a copy from
an allocation with `ProvenanceMap.new` always returns an empty `ProvenanceCopy`. -/
theorem lm_provenanceMap_prepareCopy_new {Prov : Type} (range : AllocRange) (finish : Size)
    (data : Array UInt8) (pointerSize : Size)
    (hPos : pointerSize.bytes ≠ 0)
    (hEnd : range.endExclusive = .ok finish) :
    (ProvenanceMap.new (Prov := Prov)).prepareCopy range data pointerSize = .ok ⟨#[], #[]⟩ := by
  obtain ⟨_, hNatSum, _, _⟩ := allocRange_endExclusive_props range finish hEnd
  have hPosBeq : (pointerSize.bytes == 0) = false := beq_false_of_ne hPos
  have hRangePtrsEmpty : ∀ r fin, r.endExclusive = .ok fin →
      (ProvenanceMap.new (Prov := Prov)).rangePtrs r pointerSize = .ok #[] := by
    intro r fin hr
    unfold ProvenanceMap.rangePtrs
    unfold_mem_priv
    simp only [ProvenanceMap.new, hPosBeq, Bool.false_eq_true, ↓reduceIte, hr,
      Except.mapError, bind, Except.bind, pure, Except.pure]
    rfl
  have hStartZero : (allocRange range.start Size.ZERO).endExclusive = .ok range.start := by
    cases range.start with | mk b =>
    unfold AllocRange.endExclusive AllocRange.end allocRange Size.ZERO Size.add Size.ofBytes
    have h0 : b + 0 = b := UInt64.add_zero b
    have hlt : ¬ b < b := UInt64.lt_irrefl b
    simp [Except.mapError, h0, hlt]
  have hFinZero : (allocRange finish Size.ZERO).endExclusive = .ok finish := by
    cases finish with | mk b =>
    unfold AllocRange.endExclusive AllocRange.end allocRange Size.ZERO Size.add Size.ofBytes
    have h0 : b + 0 = b := UInt64.add_zero b
    have hlt : ¬ b < b := UInt64.lt_irrefl b
    simp [Except.mapError, h0, hlt]
  have hEmptyFilter : ∀ (a b : Size),
      (Array.filter (fun (entry : Size × Prov) => decide (a.bytes ≤ entry.1.bytes) &&
        decide (entry.1.bytes < b.bytes)) #[]) = #[] := fun _ _ => rfl
  have hRp1 := hRangePtrsEmpty _ _ hStartZero
  have hRp2 := hRangePtrsEmpty _ _ hFinZero
  unfold ProvenanceMap.new at hRp1 hRp2
  unfold ProvenanceMap.prepareCopy
  unfold_mem_priv
  simp only [hPosBeq, Bool.false_eq_true, ↓reduceIte, hEnd, Except.mapError,
    bind, Except.bind, pure, Except.pure]
  by_cases hge : pointerSize.bytes ≤ range.size.bytes
  · have hSubOk : ¬ finish.bytes < pointerSize.bytes - 1 := by
      rw [UInt64.lt_iff_toNat_lt]
      have h1 : 0 < pointerSize.bytes.toNat := by
        cases h : pointerSize.bytes.toNat with
        | zero => exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hPos
        | succ k => omega
      have hle : pointerSize.bytes.toNat ≤ range.size.bytes.toNat :=
        UInt64.le_iff_toNat_le.mp hge
      have hsub : (pointerSize.bytes - 1).toNat = pointerSize.bytes.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
        simp
      omega
    have hEmptyP : (ProvenanceMap.new (Prov := Prov)).ptrs = #[] := rfl
    simp only [ge_iff_le, hge, ↓reduceIte, Size.sub, Size.ofBytes, hSubOk, hEmptyP, hEmptyFilter]
    simp [ProvenanceMap.new, hRp1, hRp2, pure, Except.pure]
  · simp [ge_iff_le, hge, ProvenanceMap.new, hRp1, hRp2]

/-- `D2` **universal `readScalar` UB law**: vendored `Allocation.readScalar` faults with `invalidUninitBytes` whenever the `InitMask` reports an uninitialized sub-range, for every allocation, layout, and range. -/
theorem lm_readScalar_uninit_ub {Prov Extra : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (a : Allocation Prov Extra) (layout : TargetDataLayout) (range : AllocRange) (rp : Bool)
    (bad : AllocRange) (h : a.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    a.readScalar layout range rp = .error (.invalidUninitBytes (some ⟨range, bad⟩)) := by
  unfold Allocation.initializationMask at h
  simp only [Allocation.readScalar, h]
  rfl

/-- `D2` **TRUE UNIVERSAL `Allocation.copy` uninit-propagation law**: for EVERY allocation size
`n > 0`, EVERY provenance/extra type, EVERY lazy-uninitialized source `src`, EVERY in-bounds
`sourceRange` of size `dst.byteSize`, and EVERY mutable provenance-free destination `dst` (even
one that was previously initialized!), vendored `Allocation.copy` succeeds WITHOUT UB and leaves
the destination lazily uninitialized (`InitMask.new dst.byteSize false`), so every in-bounds
subrange reports uninitialized and every typed `Allocation.readScalar` faults with
`invalidUninitBytes`. -/
theorem lm_allocation_copy_uninit_preserves {Prov Extra : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (src dst : Allocation Prov Extra) (sourceRange : AllocRange) (srcEnd : Size)
    (ptrSize : Size) (sameAlloc nonoverlapping : Bool) (oldInit : Bool)
    (hSrcLen : src.len = src.byteSize.bytes.toNat)
    (hSrcInit : src.initializationMask = InitMask.new src.byteSize false)
    (hSrcProv : src.provenanceMap = ProvenanceMap.new)
    (hSrcEnd : sourceRange.endExclusive = .ok srcEnd)
    (hSrcIn : srcEnd.bytes ≤ src.byteSize.bytes)
    (hSizeEq : sourceRange.size = dst.byteSize)
    (hNonZero : dst.byteSize.bytes ≠ 0)
    (hDstLen : dst.len = dst.byteSize.bytes.toNat)
    (hDstMut : dst.mutability = .Mut)
    (hDstInit : dst.initializationMask = InitMask.new dst.byteSize oldInit)
    (hDstProv : dst.provenanceMap = ProvenanceMap.new)
    (hPtrPos : ptrSize.bytes ≠ 0) :
    ∃ dst',
      Allocation.copy src sourceRange Size.ZERO ptrSize sameAlloc nonoverlapping dst = .ok () dst' ∧
      dst'.byteSize = dst.byteSize ∧
      dst'.initializationMask = InitMask.new dst.byteSize false ∧
      (∀ r fin, r.endExclusive = .ok fin → fin.bytes ≤ dst'.byteSize.bytes →
        dst'.initializationMask.isRangeInitialized r = .ok (.error r)) ∧
      (∀ layout r fin rp, r.endExclusive = .ok fin → fin.bytes ≤ dst'.byteSize.bytes →
        dst'.readScalar layout r rp = .error (.invalidUninitBytes (some ⟨r, r⟩))) := by
  obtain ⟨_, _, hSrcLe, _⟩ := allocRange_endExclusive_props sourceRange srcEnd hSrcEnd
  have hSrcNe : sourceRange.size.bytes ≠ 0 := by rw [hSizeEq]; exact hNonZero
  have hMul1 : Size.mul dst.byteSize 1 = .ok dst.byteSize := by
    have h1 : dst.byteSize.bytes * 1 = dst.byteSize.bytes := UInt64.mul_one _
    have hd : dst.byteSize.bytes / 1 = dst.byteSize.bytes := UInt64.div_one
    simp [Size.mul, h1, hd, Size.ofBytes]
  have hDstEnd : (allocRange Size.ZERO dst.byteSize).endExclusive = .ok dst.byteSize := by
    cases h : dst.byteSize with | mk b =>
    unfold AllocRange.endExclusive AllocRange.end allocRange Size.ZERO Size.add Size.ofBytes
    have h0 : (0 : UInt64) + b = b := UInt64.zero_add b
    have hlt : ¬ b < 0 := UInt64.not_lt_zero
    simp [Except.mapError, h0, hlt]
  have hNotSrcGt : ¬ srcEnd.bytes < sourceRange.start.bytes := UInt64.not_lt.mpr hSrcLe
  have hNotSrcIn : ¬ src.byteSize.bytes < srcEnd.bytes := UInt64.not_lt.mpr hSrcIn
  have hSrcInitCopy : src.initializationMask.prepareCopy sourceRange =
      .ok ⟨false, #[sourceRange.size.bytes]⟩ := by
    rw [hSrcInit]
    exact lm_initMask_prepareCopy_lazy_uninit src.byteSize sourceRange srcEnd hSrcNe hSrcEnd hSrcIn
  have hDstSetFalse : (InitMask.new dst.byteSize true).setRange (allocRange Size.ZERO dst.byteSize) false =
      .ok (InitMask.new dst.byteSize false) :=
    InitMask.full_overwrite_stays_lazy dst.byteSize dst.byteSize true false
      (allocRange Size.ZERO dst.byteSize) hDstEnd rfl (UInt64.le_refl _)
  have hNonZeroBeq : (dst.byteSize.bytes == 0) = false := beq_false_of_ne hNonZero
  have hCopy : ∃ dst',
      Allocation.copy src sourceRange Size.ZERO ptrSize sameAlloc nonoverlapping dst = .ok () dst' ∧
      dst'.byteSize = dst.byteSize ∧
      dst'.initializationMask = InitMask.new dst.byteSize false := by
    have hSrcProvRaw : ∀ raw, src.provenanceMap.prepareCopy sourceRange raw ptrSize = .ok ⟨#[], #[]⟩ := by
      intro raw; rw [hSrcProv]
      exact lm_provenanceMap_prepareCopy_new sourceRange srcEnd raw ptrSize hPtrPos hSrcEnd
    have hDstClearRaw : ∀ raw, ProvenanceMap.clear (allocRange Size.ZERO dst.byteSize) raw ptrSize
        dst.provenanceMap = .ok () ProvenanceMap.new := by
      intro raw; rw [hDstProv]
      exact ProvenanceMap.clear_new (allocRange Size.ZERO dst.byteSize) raw ptrSize dst.byteSize hPtrPos hDstEnd
    have hClearNew : ∀ raw, ProvenanceMap.clear (allocRange Size.ZERO dst.byteSize) raw ptrSize
        (ProvenanceMap.new (Prov := Prov)) = .ok () ProvenanceMap.new := by
      intro raw
      exact ProvenanceMap.clear_new (allocRange Size.ZERO dst.byteSize) raw ptrSize dst.byteSize hPtrPos hDstEnd
    have hDstSetTrue : dst.initializationMask.setRange (allocRange Size.ZERO dst.byteSize) true =
        .ok (InitMask.new dst.byteSize true) := by
      rw [hDstInit]
      exact InitMask.full_overwrite_stays_lazy dst.byteSize dst.byteSize oldInit true
        (allocRange Size.ZERO dst.byteSize) hDstEnd rfl (UInt64.le_refl _)
    have hNotZeroGt : ¬ dst.byteSize.bytes < 0 := UInt64.not_lt_zero
    have hNotSelfLt : ¬ dst.byteSize.bytes < dst.byteSize.bytes := UInt64.lt_irrefl _
    refine ⟨?dst', ?hOk, ?hSz, ?hMask⟩
    case hOk =>
      unfold Allocation.copy Allocation.copyRepeatedly Allocation.writeUninit
      unfold_mem_priv
      dsimp only [Allocation.len, Allocation.byteSize, Allocation.initializationMask, Allocation.provenanceMap, allocRange, Size.ZERO, Size.ofBytes] at hSrcLen hDstLen hDstInit hDstProv hSrcInitCopy hSrcProvRaw hDstClearRaw hClearNew hDstSetTrue hDstSetFalse hSizeEq hNonZeroBeq hNotZeroGt hNotSelfLt hNotSrcIn hDstEnd hMul1
      simp only [Id.run, hSrcLen, hDstLen, hDstMut, bne_self_eq_false, Bool.false_eq_true,
        ↓reduceIte, hSrcEnd, hNotSrcGt, hNotSrcIn, decide_false, Bool.or_self, gt_iff_lt,
        hSizeEq, hMul1, hDstEnd, hNotZeroGt, hNotSelfLt, hSrcProvRaw, hSrcInitCopy,
        InitCopy.noBytesInit, Bool.not_false, hNonZeroBeq,
        hDstSetTrue, hDstSetFalse, hDstClearRaw, hClearNew, Except.mapError, bind, Except.bind,
        pure, Except.pure, allocRange, Size.ZERO]
      rfl
    case hSz => rfl
    case hMask => rfl
  obtain ⟨dst', hOk, hSz, hMask⟩ := hCopy
  refine ⟨dst', hOk, hSz, hMask, ?_, ?_⟩
  · intro r fin hEnd hIn
    rw [hMask]
    rw [hSz] at hIn
    exact InitMask.lazy_uninitialized_query dst.byteSize r fin hEnd hIn
  · intro layout r fin rp hEnd hIn
    apply lm_readScalar_uninit_ub dst' layout r rp r
    rw [hMask]
    rw [hSz] at hIn
    exact InitMask.lazy_uninitialized_query dst.byteSize r fin hEnd hIn

/-- `D2` concrete non-vacuity witness for `lm_allocation_copy_uninit_preserves`: copying a fresh
4-byte `Allocation.tryNew .Uninit` into an already-initialized 4-byte `Allocation.tryNew .Zero`
succeeds and turns the destination lazily uninitialized. -/
theorem lm_allocation_copy_uninit_witness :
    ∃ src dst dst' : Allocation Provenance Unit,
      Allocation.tryNew (Size.ofBytes 4) ⟨2⟩ .Uninit
        (fun sz _ => some (Array.replicate sz.bytes.toNat 0)) = .ok src ∧
      Allocation.tryNew (Size.ofBytes 4) ⟨2⟩ .Zero
        (fun sz _ => some (Array.replicate sz.bytes.toNat 0)) = .ok dst ∧
      Allocation.copy src (allocRange Size.ZERO (Size.ofBytes 4)) Size.ZERO
        (Size.ofBytes 8) false true dst = .ok () dst' ∧
      dst'.initializationMask = InitMask.new (Size.ofBytes 4) false := by
  have hSrcOk : (Allocation.tryNew (Prov := Provenance) (Size.ofBytes 4) ⟨2⟩ .Uninit
      (fun sz _ => some (Array.replicate sz.bytes.toNat 0))).toBool = true := by decide +kernel
  have hDstOk : (Allocation.tryNew (Prov := Provenance) (Size.ofBytes 4) ⟨2⟩ .Zero
      (fun sz _ => some (Array.replicate sz.bytes.toNat 0))).toBool = true := by decide +kernel
  cases hs : Allocation.tryNew (Prov := Provenance) (Size.ofBytes 4) ⟨2⟩ .Uninit
      (fun sz _ => some (Array.replicate sz.bytes.toNat 0)) with
  | error _ => rw [hs] at hSrcOk; cases hSrcOk
  | ok src =>
    cases hd : Allocation.tryNew (Prov := Provenance) (Size.ofBytes 4) ⟨2⟩ .Zero
        (fun sz _ => some (Array.replicate sz.bytes.toNat 0)) with
    | error _ => rw [hd] at hDstOk; cases hDstOk
    | ok dst =>
      have hSrcProp : src.len = src.byteSize.bytes.toNat ∧
          src.byteSize = Size.ofBytes 4 ∧
          src.initializationMask = InitMask.new src.byteSize false ∧
          src.provenanceMap = ProvenanceMap.new := by
        have hCheck : (do
            let s ← Allocation.tryNew (Prov := Provenance) (Size.ofBytes 4) ⟨2⟩ .Uninit
              (fun sz _ => some (Array.replicate sz.bytes.toNat 0))
            pure (s.len == s.byteSize.bytes.toNat && s.byteSize == Size.ofBytes 4 &&
              s.initializationMask == InitMask.new s.byteSize false &&
              s.provenanceMap == ProvenanceMap.new)) = .ok true := by decide +kernel
        rw [hs] at hCheck
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          Bool.and_eq_true, beq_iff_eq] at hCheck
        exact ⟨hCheck.1.1.1, hCheck.1.1.2, hCheck.1.2, hCheck.2⟩
      have hDstProp : dst.len = dst.byteSize.bytes.toNat ∧
          dst.byteSize = Size.ofBytes 4 ∧
          dst.mutability = Miri.Memory.Mutability.Mut ∧
          dst.initializationMask = InitMask.new dst.byteSize true ∧
          dst.provenanceMap = ProvenanceMap.new := by
        have hCheck : (do
            let d ← Allocation.tryNew (Prov := Provenance) (Size.ofBytes 4) ⟨2⟩ .Zero
              (fun sz _ => some (Array.replicate sz.bytes.toNat 0))
            pure (d.len == d.byteSize.bytes.toNat && d.byteSize == Size.ofBytes 4 &&
              d.mutability == Miri.Memory.Mutability.Mut &&
              d.initializationMask == InitMask.new d.byteSize true &&
              d.provenanceMap == ProvenanceMap.new)) = .ok true := by decide +kernel
        rw [hd] at hCheck
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          Bool.and_eq_true, beq_iff_eq] at hCheck
        exact ⟨hCheck.1.1.1.1, hCheck.1.1.1.2, hCheck.1.1.2, hCheck.1.2, hCheck.2⟩
      obtain ⟨dst', hCopy, _, hMask, _, _⟩ := lm_allocation_copy_uninit_preserves
        src dst (allocRange Size.ZERO (Size.ofBytes 4)) (Size.ofBytes 4) (Size.ofBytes 8)
        false true true
        hSrcProp.1 hSrcProp.2.2.1 hSrcProp.2.2.2 (by decide)
        (by rw [hSrcProp.2.1]; exact UInt64.le_refl _)
        hDstProp.2.1.symm (by rw [hDstProp.2.1]; decide)
        hDstProp.1 hDstProp.2.2.1 hDstProp.2.2.2.1 hDstProp.2.2.2.2 (by decide)
      exact ⟨src, dst, dst', rfl, rfl, hCopy, by rw [hMask, hDstProp.2.1]⟩

end MemCopyUniversal

/-- `D2` **universal `bool` validity law** (`kani#5205` / `#5196`): vendored `Validity.checkPrimitive .boolean` rejects every scalar whose `toBool` reports `invalidBool v`. -/
theorem lm_checkPrimitive_bool_invalid {Prov ME HS : Type} [PointerProvenance Prov]
    (lay : ScalarValidityLayout) (s : Scalar Prov) (cb : Scalar Prov → HS → EStateM.Result ME HS Bool)
    (st : HS) (v : UInt8) (h : s.toBool = .error (.scalarInt (.invalidBool v))) :
    Validity.checkPrimitive .boolean lay s cb st = .error (.failure (.invalidBool v)) st := by
  simp [Validity.checkPrimitive, h]

/-- `D3` **universal law**: a successful vendored `ptrOffsetInbounds` is exactly the wrapping offset (`Pointer.wrappingSignedOffset`). -/
theorem lm_ptrOffsetInbounds_eq_wrapping {Prov PE : Type} (t : PointerArithmetic)
    (p q : Pointer (Option Prov)) (o : Int64) (r : PointerResolver Prov PE) (l : LiveAllocationLookup)
    (h : ptrOffsetInbounds t p o r l = .ok q) : p.wrappingSignedOffset o t = .ok q := by
  unfold ptrOffsetInbounds at h
  cases hc : checkPtrAccessSigned t p o .inboundsPointerArithmetic r l <;>
    simp [hc, Except.mapError, bind, Except.bind] at h
  cases hw : p.wrappingSignedOffset o t <;> simp_all

/-- `D3`: on the 64-bit target, vendored `truncateToTargetUsize` is the identity. -/
theorem lm_truncate64 (v : UInt64) : lmPtrArith.truncateToTargetUsize v = .ok v := by
  simp [PointerArithmetic.truncateToTargetUsize, lmPtrArith, Size.truncate, bind, Except.bind]
  have h64 : ((Size.ofBytes 8).bytes * 8).toNat - 1 + 1 = 64 := rfl
  have hv := v.toNat_lt
  split <;> rename_i hh <;> cases hh
  show (if (BitVec.setWidth 128 (BitVec.ofNat _ (v.toNat % 340282366920938463463374607431768211456))).toNat < 2 ^ 64
    then Except.ok (UInt64.ofNat (BitVec.setWidth 128 (BitVec.ofNat _ (v.toNat % 340282366920938463463374607431768211456))).toNat)
    else Except.error PointerError.unsignedConversionOverflow) = _
  rw [h64]
  simp [Nat.mod_eq_of_lt (by omega : v.toNat < 340282366920938463463374607431768211456)]
  omega

/-- `D4` **universal law**: vendored `ValidityMachine.scalarMayBeNull` on an integer scalar is `ScalarInt.isNull`, in every machine state. -/
theorem lm_scalarMayBeNull_int {K User : Type} (i : ScalarInt) :
    ValidityMachine.scalarMayBeNull (K := K) (User := User) (Scalar.fromScalarInt i) = pure i.isNull := rfl

/-- `D4`: `pointerLayoutData true` (function pointers) has valid range `[1, 2^64-1]`, `pointerLayoutData false` (raw pointers) `[0, 2^64-1]`. -/
theorem lm_fnptr_validity_range :
    lmWdPtrValidity true = .ok ⟨Size.ofBytes 8, ⟨BitVec.ofNat 128 1, BitVec.ofNat 128 (2 ^ 64 - 1)⟩⟩ ∧
    lmWdPtrValidity false = .ok ⟨Size.ofBytes 8, ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 (2 ^ 64 - 1)⟩⟩ :=
  ⟨rfl, rfl⟩

/-- `D4` **universal law**: the function-pointer valid range contains exactly the non-null 64-bit values. -/
theorem lm_fnptr_range_contains_iff (v : U128) :
    WrappingRange.contains ⟨BitVec.ofNat 128 1, BitVec.ofNat 128 (2 ^ 64 - 1)⟩ v = true ↔
      1 ≤ v.toNat ∧ v.toNat ≤ 2 ^ 64 - 1 := by
  simp [WrappingRange.contains]

/-- `D4` **universal law**: the raw-pointer valid range contains every 64-bit value, including `0`. -/
theorem lm_rawptr_range_contains (v : U128) (hv : v.toNat < 2 ^ 64) :
    WrappingRange.contains ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 (2 ^ 64 - 1)⟩ v = true := by
  simp [WrappingRange.contains]; omega

/-- `D3` **universal multi-step composition law**: two wrapping offsets compose to one wrapping offset by the sum (64-bit target). -/
theorem lm_wrapping_compose (p : Pointer (Option Provenance)) (a b : Int64) :
    (p.wrappingSignedOffset a lmPtrArith >>= fun q => q.wrappingSignedOffset b lmPtrArith) =
      p.wrappingSignedOffset (a + b) lmPtrArith := by
  simp [Pointer.wrappingSignedOffset, Pointer.wrappingOffset, lm_truncate64, bind, Except.bind]
  simp only [pure, Except.pure]
  simp [Size.ofBytes, UInt64.add_assoc]

/-- `D1` `HeaderSlice` padding formula `size = 4 + 4n`, `align = 4` (vendored `.adt false` arm, `n < 32`). -/
theorem lm_headerSlice_layout_formula :
    (List.range 32).all (fun n => lmWdRun (lmWdSizeAlign lmWdTyHeaderSlice lmWdHeaderSliceLay n) ==
      .okSizeAlign (4 + 4 * n) 4) = true := by decide +kernel
/-- `D1` `Align8TailU16` padding formula `size = align_to(8 + 2n, 8)`, `align = 8` (vendored `.adt false` arm, `n < 32`). -/
theorem lm_align8TailU16_layout_formula :
    (List.range 32).all (fun n => lmWdRun (lmWdSizeAlign lmWdTyAlign8TailU16 lmWdAlign8TailU16Lay n) ==
      .okSizeAlign ((8 + 2 * n + 7) / 8 * 8) 8) = true := by decide +kernel
/-- `D1` exact `isize::MAX` boundaries of both trailing-slice structs: the last valid length and the first `InvalidMeta(TooBig)` one. -/
theorem lm_dst_struct_isize_boundaries :
    lmWdRun (lmWdSizeAlign lmWdTyHeaderSlice lmWdHeaderSliceLay 2305843009213693950) =
      .okSizeAlign 9223372036854775804 4 ∧
    lmWdRun (lmWdSizeAlign lmWdTyHeaderSlice lmWdHeaderSliceLay 2305843009213693951) = .ub ∧
    lmWdRun (lmWdSizeAlign lmWdTyAlign8TailU16 lmWdAlign8TailU16Lay 4611686018427387896) =
      .okSizeAlign 9223372036854775800 8 ∧
    lmWdRun (lmWdSizeAlign lmWdTyAlign8TailU16 lmWdAlign8TailU16Lay 4611686018427387897) = .ub := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel


/-- `D1` companion: `ptr::metadata` (`Scalar.toTargetUsize` / `OpTy.len`) on a null/provenance-free
wide raw pointer `(0, 77)` succeeds without dereferencing memory. -/
theorem lm_null_dangling_ptr_metadata_ok :
    (do
      let m ← lmWdUsize 77
      let base : OpTy Provenance :=
        ⟨.indirect ⟨Pointer.withoutProvenance 0, .metadata m, none⟩,
          ⟨lmWdTySliceU32, lmWdSliceU32Lay⟩⟩
      let l ← (base.len (lmWdProjCx (lmInit false))).mapError .proj
      pure l.toNat) = (.ok 77 : LmWdM Nat) := by
  kernel_rfl

/-- `D1` non-vacuity witness for `lm_sizeAndAlign_sized`: `u32` is sized (`4`, align `4`). -/
theorem lm_sizeAndAlign_sized_u32_witness :
    lmWdU32Lay.isSized = true ∧
    lmRun (DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () 1 .none ⟨lmWdTyU32, lmWdU32Lay⟩) =
      .ok (some (lmWdU32Lay.size, lmWdU32Lay.align.abi)) :=
  ⟨rfl, by rw [lm_sizeAndAlign_sized lmWdDynHooks () 1 .none ⟨lmWdTyU32, lmWdU32Lay⟩ rfl]; rfl⟩

/-- `D2` non-vacuity witness for `lm_readScalar_uninit_ub` and `lm_initMask_prepareCopy_lazy_uninit`:
a fresh 4-byte uninitialized allocation reports `isRangeInitialized = .ok (.error range)` and
`prepareCopy = .ok ⟨false, #[4]⟩` (`noBytesInit = true`), so `readScalar` faults with
`invalidUninitBytes`. -/
theorem lm_readScalar_uninit_witness :
    let r : AllocRange := ⟨Size.ZERO, Size.ofBytes 4⟩
    (InitMask.new (Size.ofBytes 4) false).prepareCopy r = .ok ⟨false, #[4]⟩ ∧
    (InitMask.new (Size.ofBytes 4) false).isRangeInitialized r = .ok (.error r) := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- `D3` non-vacuity witness for `lm_ptrOffsetInbounds_eq_wrapping`: in-bounds `+4` on a live
12-byte allocation succeeds and equals `wrappingSignedOffset`. -/
theorem lm_ptrOffsetInbounds_ok_witness :
    (do
      let (p, st) ← lmWdArray false 100 200 300
      let q ← lmWdInb st p 4
      let q' ← lmWdWrap p 4
      pure (decide (q = q'))) = (.ok true : LmWdM Bool) := by
  rw [lmWdArrayU.eq_src, lmWdInbU.eq_src]
  kernel_rfl

/-- `D2` non-vacuity: the byte `2` is not a `bool` (vendored `Scalar.toBool`). -/
theorem lm_scalar_two_not_bool :
    ((Scalar.fromUInt (Prov := Provenance) (BitVec.ofNat 128 2) (Size.ofBytes 1)).bind
      Scalar.toBool) = .error (.scalarInt (.invalidBool 2)) := by
  kernel_rfl

/-- `D4` non-vacuity: vendored `ValidityMachine.scalarMayBeNull` reports the `0usize` scalar of
cases `21`–`23` as null. -/
theorem lm_scalarMayBeNull_zero_usize :
    match lmWdUsize 0 with
    | .ok s => ValidityMachine.scalarMayBeNull (K := Unit) (User := Unit) s = pure true
    | .error _ => False := by
  exact rfl

/-- `D4` **universal vendored validity law for function pointers**: `Validity.checkScalar` at the
`pointerLayoutData true` valid range accepts an 8-byte integer scalar iff its bits are non-null,
and otherwise faults with exactly `invalidScalarBits` (every scalar, every hook state). -/
theorem lm_checkScalar_fnptr_int {HS : Type} (i : ScalarInt) (bits : U128)
    (hb : i.toBits (Size.ofBytes 8) = .ok bits)
    (cb : Scalar Provenance → HS → EStateM.Result Unit HS Bool) (st : HS) :
    Validity.checkScalar
        ⟨Size.ofBytes 8, ⟨BitVec.ofNat 128 1, BitVec.ofNat 128 (2 ^ 64 - 1)⟩⟩
        (Scalar.fromScalarInt (Prov := Provenance) i) cb st =
      if 1 ≤ bits.toNat ∧ bits.toNat ≤ 2 ^ 64 - 1 then .ok () st
      else .error (.failure (.invalidScalarBits bits
        ⟨Size.ofBytes 8, ⟨BitVec.ofNat 128 1, BitVec.ofNat 128 (2 ^ 64 - 1)⟩⟩)) st := by
  simp only [Validity.checkScalar]
  split
  next x c hc =>
    have htry : (Scalar.fromScalarInt (Prov := Provenance) i).tryToScalarInt = .ok (.integer i) := rfl
    simp only [htry, hb]
    by_cases h : 1 ≤ bits.toNat ∧ bits.toNat ≤ 2 ^ 64 - 1
    · have hc' : WrappingRange.contains ⟨BitVec.ofNat 128 1, BitVec.ofNat 128 (2 ^ 64 - 1)⟩ bits = true :=
        (lm_fnptr_range_contains_iff bits).mpr h
      simp [hc', h]
    · have hc' : WrappingRange.contains ⟨BitVec.ofNat 128 1, BitVec.ofNat 128 (2 ^ 64 - 1)⟩ bits = false := by
        cases hh : WrappingRange.contains ⟨BitVec.ofNat 128 1, BitVec.ofNat 128 (2 ^ 64 - 1)⟩ bits
        · rfl
        · exact absurd ((lm_fnptr_range_contains_iff bits).mp hh) h
      simp [hc', h]
  next e he => cases he

/-- `D4` concrete non-vacuity witnesses for `lm_checkScalar_fnptr_int`: `0usize` is rejected with
`invalidScalarBits 0` while non-null `4096usize` is accepted at `pointerLayoutData true`. -/
theorem lm_checkScalar_fnptr_int_witnesses :
    let lay : ScalarValidityLayout :=
      ⟨Size.ofBytes 8, ⟨BitVec.ofNat 128 1, BitVec.ofNat 128 (2 ^ 64 - 1)⟩⟩
    let cb : Scalar Provenance → Unit → EStateM.Result Unit Unit Bool := fun _ st => .error () st
    (∃ i0 : ScalarInt, i0.toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 0) ∧
      Validity.checkScalar lay (Scalar.fromScalarInt (Prov := Provenance) i0) cb () =
        .error (.failure (.invalidScalarBits (BitVec.ofNat 128 0) lay)) ()) ∧
    (∃ i1 : ScalarInt, i1.toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 4096) ∧
      Validity.checkScalar lay (Scalar.fromScalarInt (Prov := Provenance) i1) cb () =
        .ok () ()) := by
  have h0ok : (ScalarInt.tryFromUInt (BitVec.ofNat 128 0) (Size.ofBytes 8)).toOption.join.isSome = true := by
    decide +kernel
  have h1ok : (ScalarInt.tryFromUInt (BitVec.ofNat 128 4096) (Size.ofBytes 8)).toOption.join.isSome = true := by
    decide +kernel
  cases h0 : (ScalarInt.tryFromUInt (BitVec.ofNat 128 0) (Size.ofBytes 8)).toOption.join with
  | none => rw [h0] at h0ok; cases h0ok
  | some i0 =>
    cases h1 : (ScalarInt.tryFromUInt (BitVec.ofNat 128 4096) (Size.ofBytes 8)).toOption.join with
    | none => rw [h1] at h1ok; cases h1ok
    | some i1 =>
      have hb0 : i0.toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 0) := by
        have hc : ((ScalarInt.tryFromUInt (BitVec.ofNat 128 0) (Size.ofBytes 8)).toOption.join.map
            (fun i => i.toBits (Size.ofBytes 8))) = some (.ok (BitVec.ofNat 128 0)) := by
          decide +kernel
        rw [h0] at hc; simpa using hc
      have hb1 : i1.toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 4096) := by
        have hc : ((ScalarInt.tryFromUInt (BitVec.ofNat 128 4096) (Size.ofBytes 8)).toOption.join.map
            (fun i => i.toBits (Size.ofBytes 8))) = some (.ok (BitVec.ofNat 128 4096)) := by
          decide +kernel
        rw [h1] at hc; simpa using hc
      refine ⟨⟨i0, hb0, ?_⟩, ⟨i1, hb1, ?_⟩⟩
      · have h := lm_checkScalar_fnptr_int i0 (BitVec.ofNat 128 0) hb0 (fun _ st => .error () st) ()
        simpa using h
      · have h := lm_checkScalar_fnptr_int i1 (BitVec.ofNat 128 4096) hb1 (fun _ st => .error () st) ()
        simpa using h

/-- `D2` concrete non-vacuity witness for `lm_checkPrimitive_bool_invalid`: byte `2` fails
`Validity.checkPrimitive .boolean` with `invalidBool 2`. -/
theorem lm_checkPrimitive_bool_invalid_witness :
    ∃ s : Scalar Provenance,
      Scalar.fromUInt (Prov := Provenance) (BitVec.ofNat 128 2) (Size.ofBytes 1) = .ok s ∧
      Validity.checkPrimitive (MachineError := Unit) (HookState := Unit)
        .boolean lmWdBoolValidity s (fun _ st => .error () st) () =
        .error (.failure (.invalidBool 2)) () := by
  have hok : (Scalar.fromUInt (Prov := Provenance) (BitVec.ofNat 128 2) (Size.ofBytes 1)).toBool = true := by
    decide +kernel
  cases hs : Scalar.fromUInt (Prov := Provenance) (BitVec.ofNat 128 2) (Size.ofBytes 1) with
  | error _ => rw [hs] at hok; cases hok
  | ok s =>
    have htb : s.toBool = .error (.scalarInt (.invalidBool 2)) := by
      have h := lm_scalar_two_not_bool
      rw [hs] at h; simpa [Except.bind] using h
    exact ⟨s, rfl, lm_checkPrimitive_bool_invalid lmWdBoolValidity s (fun _ st => .error () st) () 2 htb⟩

/-- `D1` concrete non-vacuity witnesses for `lm_sizeAndAlign_str` (valid `len = 0` and overflow
`len = 2^63`) and `lm_sizeAndAlign_sliceUnit` (ZST `[()]` never overflows even at `u64::MAX`). -/
theorem lm_sizeAndAlign_str_and_unit_witnesses :
    lmWdRun (lmWdSizeAlign lmWdTyStr lmWdStrLay 0) = .okSizeAlign 0 1 ∧
    lmWdRun (lmWdSizeAlign lmWdTyStr lmWdStrLay 9223372036854775808) = .ub ∧
    lmWdRun (lmWdSizeAlign lmWdTySliceUnit lmWdSliceUnitLay 5) = .okSizeAlign 0 1 ∧
    lmWdRun (lmWdSizeAlign lmWdTySliceUnit lmWdSliceUnitLay 18446744073709551615) = .okSizeAlign 0 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end UniversalLaws

/-! ## §3b. Direct Vendored `Miri.Interpreter.Step.step` Execution on Shared `CapturedMir` Fixtures -/

section StepDriver
open Miri.ABI Miri.Memory Miri.Interpreter LeanMiriSpec.Correspondence

/-- Harness-provided `CastHooks` adapter over `annealCastHooksLM2_2`:
1. `typeInfo 40 := .rawPointer 51` bridges `Translate.lean`'s aggregate-pointee thin raw-pointer
   encoding (`*const [u32; 3]`, `TyId = 40`, which `castTypeInfoOfEncodedTyId` leaves unwired) to
   vendored `Miri.Interpreter.Cast.ptrToPtr`;
2. `copyAllowTransmute` bridges `CastKind.Transmute` directly to unmodified vendored
   `Miri.Memory.Validity.checkScalar` against the target layout's `validRange`
   (`pointerLayoutData true` for `fn() -> u32`, `pointerLayoutData false` for `*const u8`).
Both hooks are thin harness adapters; every layout, cast, and validity decision is performed by the
vendored `Miri` functions. -/
def wdCastHooks (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable) :
    Miri.Interpreter.CastHooks
      AnnealProv AnnealStepState Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealCastHooksLM2_2 layouts with
    typeInfo := fun _ tyId =>
      if tyId == 40 then pure (.rawPointer 51)
      else match castTypeInfoOfEncodedTyId tyId with
      | .ok info => pure info
      | .error err => throw err
    copyAllowTransmute := fun _ src dest => do
      let imm ← annealReadImmediateLM2_2 src
      match imm.imm, dest.layout.layout.backendRepr with
      | .scalar s, .Scalar (.Initialized (validRange := vr) ..) =>
        let lay : ScalarValidityLayout := ⟨dest.layout.layout.size, vr⟩
        match Validity.checkScalar (MachineError := Unit) (HookState := Unit)
            lay s (fun _ st => .error () st) () with
        | .ok () _ => annealWriteImmediateLM2_2 imm.imm dest
        | .error _ _ => throw (.undefinedBehavior "invalid scalar value in transmute")
      | _, _ => annealWriteImmediateLM2_2 imm.imm dest }

/-- `StepHooks` over `annealStepHooksLM2_2` using `wdCastHooks` for `CastKind.Transmute` /
`*const [u32; 3] -> *const u8` and `toRef` for `&raw const _1` (`Rvalue.RawPtr`). -/
def wdStepHooks (body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir) :
    Miri.Interpreter.StepHooks
      AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let rvHooks := { annealRvalueHooksLM2_2 body.localDecls body.layouts with
    toRef := fun _ mp =>
      match mp.metadata with
      | .none =>
        match Scalar.fromMaybePointer annealTargetDataLayout mp.ptr with
        | .ok sc => pure (.scalar sc)
        | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)
      | .metadata m =>
        match Scalar.fromMaybePointer annealTargetDataLayout mp.ptr with
        | .ok sc => pure (.scalarPair sc m)
        | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)
    cast := fun c src kind ty dest =>
      Miri.Interpreter.Cast.cast (wdCastHooks body.layouts) c 16 src kind ty dest }
  { annealStepHooksLM2_2 body.localDecls body.layouts with
    assign := fun choice place rvalue state =>
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace rvHooks choice rvalue place) state }

/-- Multi-step execution of unmodified vendored `Miri.Interpreter.Step.step` directly over a
translated `CapturedMir` body. -/
def wdRunMiriSteps
    (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine
      Unit (Miri.Interpreter.RuntimePlace AnnealProv))
    (steps : Nat) (st : AnnealStepState) :
    Except StepError (Option (Miri.Interpreter.LocalValue AnnealProv)) :=
  match steps with
  | 0 => .error (.unsupported "out of fuel")
  | n + 1 =>
    let lastRet := st.stack.frames[0]?.bind (fun f => f.locals[0]?.map (·.value))
    let (st', res) := Miri.Interpreter.Step.step hooks () st
    match res with
    | .error e => .error e
    | .ok true =>
      if st'.stack.frames.isEmpty then .ok lastRet
      else wdRunMiriSteps hooks n st'
    | .ok false => .ok (st'.stack.frames[0]?.bind (fun f => f.locals[0]?.map (·.value)))

/-- Build the initial `AnnealStepState` for a shared `CapturedMir` fixture via `translateBody`. -/
def wdMkStepState (body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir)
    (retTy : Trusted.Rustc.V2026_06_01.MirAst.Ty)
    (locs : Array (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout))
    (mach : AnnealMachine := AnnealMachine.empty) : AnnealStepState :=
  { stack := { frames := #[{
      body := translateBody body,
      bodyIdentity := .ofCanonicalIndex 0,
      functionInstance := { kind := .Item 0, args := #[] },
      extra := (), returnContinuation := .stop false,
      returnPlace := .frameLocal 0 0 none (translateTy retTy body.layouts) (.ofAllocationToken 0),
      localsIdentity := .ofAllocationToken 0, locals := locs, vaList := #[],
      trackCallerArg := none, location := .mir ⟨0, 0⟩ }] },
    machine := mach }

private def wdStepAid1 : AllocId := ⟨1, by decide⟩
private def wdStepBase1 : UInt64 := 4294967296

private def wdStepUInt (bits : Nat) (sz : UInt64) : Scalar AnnealProv :=
  match Scalar.fromUInt (BitVec.ofNat 128 bits) (Size.ofBytes sz) with
  | .ok s => s
  | .error _ => Scalar.fromPointer annealTargetDataLayout ⟨.ZERO, .wildcard⟩

private def wdStepFnPtr1 : Scalar AnnealProv :=
  Scalar.fromPointer annealTargetDataLayout
    ⟨Size.ofBytes wdStepBase1, .concrete wdStepAid1 .one⟩

private def wdStepArr3Mach : AnnealMachine :=
  match Allocation.fromBytes (Prov := AnnealProv)
      #[100, 0, 0, 0, 200, 0, 0, 0, 44, 1, 0, 0] ⟨2⟩ .Mut with
  | .ok a =>
    { AnnealMachine.empty with
      memory := { (MemoryState.empty : AnnealMemory) with live := #[(wdStepAid1, ⟨.stack, a.withExtra none⟩)] },
      addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨wdStepAid1, wdStepBase1⟩] } }
  | .error _ => AnnealMachine.empty

private def wdStepD3Locals (body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir) :
    Array (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :=
  let lays := body.localDecls.map (fun d => some (translateTy d.ty body.layouts))
  let arrMp : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Size.ofBytes wdStepBase1, some (.concrete wdStepAid1 .one)⟩, .none, none⟩
  (lays.zipIdx.map fun (l, idx) =>
    if idx == 1 then ⟨.live (.indirect arrMp), l⟩
    else ⟨.live (.immediate .uninit), l⟩).toArray

/-- Run exactly `n` iterations of `Miri.Interpreter.Step.step` (returning the intermediate state),
used to observe intermediate local values (such as `_4 = base + 100` right after `arith_offset`). -/
private def wdRunMiriStepsState
    (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine
      Unit (Miri.Interpreter.RuntimePlace AnnealProv))
    (steps : Nat) (st : AnnealStepState) : Except StepError AnnealStepState :=
  match steps with
  | 0 => .ok st
  | n + 1 =>
    let (st', res) := Miri.Interpreter.Step.step hooks () st
    match res with
    | .error e => .error e
    | .ok _ => wdRunMiriStepsState hooks n st'

private def wdStepAid2 : AllocId := ⟨2, by decide⟩
private def wdStepBase2 : UInt64 := 8589934592

private def wdStepD2Mach : AnnealMachine :=
  match Allocation.tryNew (Prov := AnnealProv) (Size.ofBytes 4) ⟨2⟩ .Uninit
      (fun sz _ => some (Array.replicate sz.bytes.toNat 0)) with
  | .ok a =>
    { AnnealMachine.empty with
      memory := { (MemoryState.empty : AnnealMemory) with
        live := #[(wdStepAid1, ⟨.stack, a.withExtra none⟩),
                  (wdStepAid2, ⟨.stack, a.withExtra none⟩)] },
      addresses := { AnnealMachine.empty.addresses with
        baseAddr := #[⟨wdStepAid1, wdStepBase1⟩, ⟨wdStepAid2, wdStepBase2⟩] } }
  | .error _ => AnnealMachine.empty

private def wdStepD2Locals (body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir) :
    Array (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :=
  let lays := body.localDecls.map (fun d => some (translateTy d.ty body.layouts))
  let mp1 : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Size.ofBytes wdStepBase1, some (.concrete wdStepAid1 .one)⟩, .none, none⟩
  let mp2 : Miri.Interpreter.MemPlace AnnealProv :=
    ⟨⟨Size.ofBytes wdStepBase2, some (.concrete wdStepAid2 .one)⟩, .none, none⟩
  (lays.zipIdx.map fun (l, idx) =>
    if idx == 1 then ⟨.live (.indirect mp1), l⟩
    else if idx == 2 then ⟨.live (.indirect mp2), l⟩
    else ⟨.live (.immediate .uninit), l⟩).toArray

/-- `D2` **direct `Miri.Interpreter.Step.step` execution of shared `wdCase11Mir`**: stepping
`ManuallyDrop<u32>` write `77`, copy, and field-`0` projection read through unmodified
`Miri.Interpreter.Step.step` returns `77`, matching `lmWdObserve _ 11`. -/
theorem lm_step_wdCase11_manually_drop_ok :
    wdRunMiriSteps (wdStepHooks wdCase11Mir) 16
      (wdMkStepState wdCase11Mir wdU32Ty (wdStepD2Locals wdCase11Mir) wdStepD2Mach) =
      .ok (some (.live (.immediate (.scalar (wdStepUInt 77 4))))) := by
  decide +kernel

/-- `D3` **direct `Miri.Interpreter.Step.step` execution of shared `wdCase14Mir`**: stepping the
translated `CapturedMir` fixture (`*const [u32;3] -> *const u8 -> +4 -> *const u32 -> +1 -> -1 -> *p`)
through unmodified `Miri.Interpreter.Step.step` + `ptrOffsetInbounds` returns `u32` `200`, matching
`lmWdObserve _ 14 = .okScalar 200`. -/
theorem lm_step_wdCase14_ok :
    wdRunMiriSteps (wdStepHooks wdCase14Mir) 16
      (wdMkStepState wdCase14Mir wdU32Ty (wdStepD3Locals wdCase14Mir) wdStepArr3Mach) =
      .ok (some (.live (.immediate (.scalar (wdStepUInt 200 4))))) := by
  decide +kernel

/-- `D3` **direct `Miri.Interpreter.Step.step` execution of shared `wdCase15Mir`**: stepping
`arith_offset(+100)` out of bounds and `arith_offset(-96)` back in bounds through unmodified
`Miri.Interpreter.Step.step` -> `Call.evalCallTerminator` -> `Intrinsics.eval` (`"arith_offset"`)
-> `Pointer.wrappingSignedOffset` returns `arr[1] = 200`, matching `lmWdObserve _ 15 = .okScalar 200`. -/
theorem lm_step_wdCase15_wrapping_oob_and_back_ok :
    wdRunMiriSteps (wdStepHooks wdCase15Mir) 16
      (wdMkStepState wdCase15Mir wdU32Ty (wdStepD3Locals wdCase15Mir) wdStepArr3Mach) =
      .ok (some (.live (.immediate (.scalar (wdStepUInt 200 4))))) := by
  decide +kernel

/-- `D3` **direct `Miri.Interpreter.Step.step` execution of shared `wdCase16Mir`**: stepping the
translated `CapturedMir` fixture (`offset(+100)` past the 12-byte array, no deref) through
unmodified `Miri.Interpreter.Step.step` + `ptrOffsetInbounds` faults with exact
`"pointer Offset out of bounds"` UB, matching `lmWdObserve _ 16 = .ub`. -/
theorem lm_step_wdCase16_oob_ub :
    wdRunMiriSteps (wdStepHooks wdCase16Mir) 16
      (wdMkStepState wdCase16Mir wdU32Ty (wdStepD3Locals wdCase16Mir) wdStepArr3Mach) =
      .error (.undefinedBehavior "pointer Offset out of bounds") := by
  decide +kernel

/-- `D3` **direct `Miri.Interpreter.Step.step` execution of shared `wdCase17Mir`**: proves BOTH:
1. After 3 steps (`&raw const _1`, `as *const u8`, `arith_offset(+100)`), local `_4` holds the
   exact concrete OOB pointer `wdStepBase1 + 100` (proving `arith_offset` genuinely executed via
   `Call.evalCallTerminator` -> `Intrinsics.eval`, NOT an uninitialized local!), AND
2. Dereferencing `_5 = _4 as *const u32` at offset `100` in the 12-byte allocation faults because
   `Allocation.readScalar` checks `InitMask.isRangeInitialized [100, 104)` (`finish > 12` returns
   `.error [12, 104)`), surfacing `.error (.undefinedBehavior "read of uninitialized memory field")`
   through `annealReadIndirectImmediate`, matching `lmWdObserve _ 17 = .ub`. -/
theorem lm_step_wdCase17_wrapping_oob_deref_ub :
    let oobPtr : Scalar AnnealProv :=
      Scalar.fromPointer annealTargetDataLayout
        ⟨Size.ofBytes (wdStepBase1 + 100), .concrete wdStepAid1 .one⟩
    (wdRunMiriStepsState (wdStepHooks wdCase17Mir) 3
        (wdMkStepState wdCase17Mir wdU32Ty (wdStepD3Locals wdCase17Mir) wdStepArr3Mach)).map
        (fun st => st.stack.frames[0]?.bind fun f => f.locals[4]?.map (·.value)) =
      .ok (some (.live (.immediate (.scalar oobPtr)))) ∧
    wdRunMiriSteps (wdStepHooks wdCase17Mir) 16
      (wdMkStepState wdCase17Mir wdU32Ty (wdStepD3Locals wdCase17Mir) wdStepArr3Mach) =
      .error (.undefinedBehavior "read of uninitialized memory field") := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- `D3` **direct `Miri.Interpreter.Step.step` execution of shared `wdCase18Mir`**: stepping
`offset(0)` + `arith_offset(0)` + `*p` through unmodified `Miri.Interpreter.Step.step` returns
`arr[0] = 100`, matching `lmWdObserve _ 18 = .okScalar 100`. -/
theorem lm_step_wdCase18_zero_offset_chain_ok :
    wdRunMiriSteps (wdStepHooks wdCase18Mir) 16
      (wdMkStepState wdCase18Mir wdU32Ty (wdStepD3Locals wdCase18Mir) wdStepArr3Mach) =
      .ok (some (.live (.immediate (.scalar (wdStepUInt 100 4))))) := by
  decide +kernel

/-- `D4` **direct `Miri.Interpreter.Step.step` execution of shared `wdCase20Mir`**: stepping
`transmute::<fn() -> u32, fn() -> u32>` on a live non-null function pointer through unmodified
`Miri.Interpreter.Step.step` + `Cast.cast` + `Validity.checkScalar` preserves the concrete
function-pointer scalar, matching `lmWdObserve _ 20 = .okFnPtr 1`. -/
theorem lm_step_wdCase20_fnptr_ok :
    let fnLay := some (translateTy wdFnPtrTy wdCase20Mir.layouts)
    wdRunMiriSteps (wdStepHooks wdCase20Mir) 8
      (wdMkStepState wdCase20Mir wdFnPtrTy
        #[⟨.live (.immediate .uninit), fnLay⟩, ⟨.live (.immediate (.scalar wdStepFnPtr1)), fnLay⟩]) =
      .ok (some (.live (.immediate (.scalar wdStepFnPtr1)))) := by
  decide +kernel

/-- `D4` **direct `Miri.Interpreter.Step.step` execution of shared `wdCase21Mir`**: stepping
`transmute::<usize, fn() -> u32>(0)` through unmodified `Miri.Interpreter.Step.step` + `Cast.cast`
+ `Validity.checkScalar` at `pointerLayoutData true` faults with `.undefinedBehavior`, matching
`lmWdObserve _ 21 = .ub`. -/
theorem lm_step_wdCase21_null_fnptr_ub :
    let fnLay := some (translateTy wdFnPtrTy wdCase21Mir.layouts)
    let usLay := some (translateTy wdUsizeTy wdCase21Mir.layouts)
    wdRunMiriSteps (wdStepHooks wdCase21Mir) 8
      (wdMkStepState wdCase21Mir wdFnPtrTy
        #[⟨.live (.immediate .uninit), fnLay⟩,
          ⟨.live (.immediate (.scalar (wdStepUInt 0 8))), usLay⟩]) =
      .error (.undefinedBehavior "invalid scalar value in transmute") := by
  decide +kernel

/-- `D4` **direct `Miri.Interpreter.Step.step` execution of shared `wdCase23Mir`**: stepping
`transmute::<usize, *const u8>(0)` through unmodified `Miri.Interpreter.Step.step` + `Cast.cast`
+ `Validity.checkScalar` at `pointerLayoutData false` accepts `0usize`, matching
`lmWdObserve _ 23 = .okFnPtr 0`. -/
theorem lm_step_wdCase23_null_raw_ok :
    let rawLay := some (translateTy wdRawU8Ty wdCase23Mir.layouts)
    let usLay := some (translateTy wdUsizeTy wdCase23Mir.layouts)
    wdRunMiriSteps (wdStepHooks wdCase23Mir) 8
      (wdMkStepState wdCase23Mir wdRawU8Ty
        #[⟨.live (.immediate .uninit), rawLay⟩,
          ⟨.live (.immediate (.scalar (wdStepUInt 0 8))), usLay⟩]) =
      .ok (some (.live (.immediate (.scalar (wdStepUInt 0 8))))) := by
  decide +kernel

/-- The little-endian `u32` elements of the Step-driver backing allocation of `[100, 200, 300]`,
read back through vendored `Allocation.readScalar` (byte `300` does not fit `UInt8`: it is
`44, 1`). -/
private def wdStepArr3Elems : List (Option Nat) :=
  match wdStepArr3Mach.memory.live[0]? with
  | some (_, entry) =>
    [0, 4, 8].map fun off =>
      match entry.allocation.readScalar annealTargetDataLayout ⟨Size.ofBytes off, Size.ofBytes 4⟩ false with
      | .ok sc => match sc.toBits (Size.ofBytes 4) with
        | .ok b => some b.toNat
        | .error _ => none
      | .error _ => none
  | none => []

/-- The Step-driver memory really holds `[100u32, 200, 300]` (the same array as the harness
and as the Trusted / MiniRust `D3` fixtures). -/
theorem lm_step_arr3_backing_is_100_200_300 : wdStepArr3Elems = [some 100, some 200, some 300] := by
  decide +kernel

/-- `D3` mode-free (`treeBorrows = false`) **direct `Miri.Interpreter.Step.step` execution of shared
`wdCase19Mir`**: without a borrow tracker, writing `999` through `(&raw mut _1 as *mut u32).offset(1)`
and reading it back returns `999`, matching `lmWdObserve false 19 = .okScalar 999`. -/
theorem lm_step_wdCase19_basic_ok :
    wdRunMiriSteps (wdStepHooks wdCase19Mir) 16
      (wdMkStepState wdCase19Mir wdU32Ty (wdStepD3Locals wdCase19Mir) wdStepArr3Mach) =
      .ok (some (.live (.immediate (.scalar (wdStepUInt 999 4))))) := by
  decide +kernel

/-- `D4` case `22` executes the SAME shared fixture as case `21` (`wdCase21Mir`): LeanMiri's
`Step.step` rejects the null `fn()` with exact `"invalid scalar value in transmute"` regardless of
MiniRust's pinned `checkPtr` (the pin delta). -/
theorem lm_step_wdCase22_null_fnptr_ub :
    let fnLay := some (translateTy wdFnPtrTy wdCase21Mir.layouts)
    let usLay := some (translateTy wdUsizeTy wdCase21Mir.layouts)
    wdRunMiriSteps (wdStepHooks wdCase21Mir) 8
      (wdMkStepState wdCase21Mir wdFnPtrTy
        #[⟨.live (.immediate .uninit), fnLay⟩,
          ⟨.live (.immediate (.scalar (wdStepUInt 0 8))), usLay⟩]) =
      .error (.undefinedBehavior "invalid scalar value in transmute") := by
  decide +kernel

/-- **Step-driver capstone**: every direct `Miri.Interpreter.Step.step` execution of a shared
`CapturedMir` fixture (cases `11`, `14`, `15`, `16`, `17`, `18`, `19` without a borrow tracker,
`20`, `21`, `22`, `23` — 11 shared fixtures covering `ManuallyDrop`, ALL `D3` pointer-offset &
`arith_offset` chains, and ALL `D4` `FnPtr`/raw transmutes!) agrees with the harness table, over
a backing allocation that really holds `[100, 200, 300]`, with exact UB messages. -/
theorem ep1_lean_miri_step_driver_capstone :
    type_of% lm_step_arr3_backing_is_100_200_300 ∧
    type_of% lm_step_wdCase11_manually_drop_ok ∧ type_of% lm_step_wdCase14_ok ∧
    type_of% lm_step_wdCase15_wrapping_oob_and_back_ok ∧ type_of% lm_step_wdCase16_oob_ub ∧
    type_of% lm_step_wdCase17_wrapping_oob_deref_ub ∧ type_of% lm_step_wdCase18_zero_offset_chain_ok ∧
    type_of% lm_step_wdCase19_basic_ok ∧ type_of% lm_step_wdCase20_fnptr_ok ∧
    type_of% lm_step_wdCase21_null_fnptr_ub ∧ type_of% lm_step_wdCase22_null_fnptr_ub ∧
    type_of% lm_step_wdCase23_null_raw_ok ∧
    lmWdObserve false 11 = .okScalar 77 ∧ lmWdObserve false 14 = .okScalar 200 ∧
    lmWdObserve false 15 = .okScalar 200 ∧ lmWdObserve false 16 = .ub ∧
    lmWdObserve false 17 = .ub ∧ lmWdObserve false 18 = .okScalar 100 ∧
    lmWdObserve false 19 = .okScalar 999 ∧ lmWdObserve false 20 = .okFnPtr 1 ∧
    lmWdObserve false 21 = .ub ∧ lmWdObserve false 22 = .ub ∧ lmWdObserve false 23 = .okFnPtr 0 := by
  refine ⟨lm_step_arr3_backing_is_100_200_300, lm_step_wdCase11_manually_drop_ok, lm_step_wdCase14_ok,
    lm_step_wdCase15_wrapping_oob_and_back_ok, lm_step_wdCase16_oob_ub,
    lm_step_wdCase17_wrapping_oob_deref_ub, lm_step_wdCase18_zero_offset_chain_ok,
    lm_step_wdCase19_basic_ok, lm_step_wdCase20_fnptr_ok, lm_step_wdCase21_null_fnptr_ub,
    lm_step_wdCase22_null_fnptr_ub, lm_step_wdCase23_null_raw_ok,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [lmWdObserveU.eq_src]; decide +kernel

/-! ### Documented `Step.step` adapter limits for `D2` union transport

The `LeanMiriSpec.Correspondence` step adapter (`annealReadImmediateLM2_2`) reads only scalar
immediates out of memory, so whole-union copies of `MaybeUninit<T>` cannot be executed through
`Step.step` on the shared fixtures. These theorems pin that boundary exactly (so a future adapter
upgrade breaks them and flags the cells for promotion); the `D2` authority for cases `8`–`10`,
`12`, `13` is the harness path (vendored `Allocation.copy` / `InitMask` / `readScalar` /
`Validity.checkPrimitive`) of `lmWdObserve`. In particular case `8`'s adapter result is a FALSE
`read of uninitialized local` UB (Miri copies an uninitialized union without UB), which is why it
is NOT used as a witness. -/

/-- 1-byte uninitialized stack-local backing for `MaybeUninit<bool>` (`wdCase13Mir` / `wdCase13CopyMir`). -/
private def wdStepD2Mach1 : AnnealMachine :=
  match Allocation.tryNew (Prov := AnnealProv) (Size.ofBytes 1) ⟨0⟩ .Uninit
      (fun sz _ => some (Array.replicate sz.bytes.toNat 0)) with
  | .ok a =>
    { AnnealMachine.empty with
      memory := { (MemoryState.empty : AnnealMemory) with
        live := #[(wdStepAid1, ⟨.stack, a.withExtra none⟩),
                  (wdStepAid2, ⟨.stack, a.withExtra none⟩)] },
      addresses := { AnnealMachine.empty.addresses with
        baseAddr := #[⟨wdStepAid1, wdStepBase1⟩, ⟨wdStepAid2, wdStepBase2⟩] } }
  | .error _ => AnnealMachine.empty

/-- Adapter limit: the whole-union copies of cases `9`, `10` (4-byte `MaybeUninit<u32>`) and
`13` / `13` companion (1-byte `MaybeUninit<bool>`) are `.unsupported` under `Step.step`
(non-scalar indirect read). -/
theorem lm_step_union_copy_adapter_unsupported :
    wdRunMiriSteps (wdStepHooks wdCase9Mir) 16
        (wdMkStepState wdCase9Mir wdMuU32Ty (wdStepD2Locals wdCase9Mir) wdStepD2Mach) =
      .error (.unsupported "indirect non-scalar readImmediate") ∧
    wdRunMiriSteps (wdStepHooks wdCase10Mir) 16
        (wdMkStepState wdCase10Mir wdU32Ty (wdStepD2Locals wdCase10Mir) wdStepD2Mach) =
      .error (.unsupported "indirect non-scalar readImmediate") ∧
    wdRunMiriSteps (wdStepHooks wdCase13Mir) 16
        (wdMkStepState wdCase13Mir wdBoolTy (wdStepD2Locals wdCase13Mir) wdStepD2Mach1) =
      .error (.unsupported "indirect non-scalar readImmediate") ∧
    wdRunMiriSteps (wdStepHooks wdCase13CopyMir) 16
        (wdMkStepState wdCase13CopyMir wdMuBoolTy (wdStepD2Locals wdCase13CopyMir) wdStepD2Mach1) =
      .error (.unsupported "indirect non-scalar readImmediate") := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Adapter limit (`D1` `constantIndex` wide-slice fixtures): `wdCase0Mir` and `wdCase5Mir` use
`ProjectionElem.constantIndex` on `[u32; 3]` (`layoutIdx = 0`), which `Translate.lean` maps to
the 1-byte `wdLayouts[0]` scalar layout rather than a `.Array` layout, so `Step.step` stops at
`invalidProgram "len on non-array"` (and those cells rest on `lmWdObserve`'s vendored `OpTy.len`
/ `projectIndex` / `projectionMemoryOffset` path). -/
theorem lm_step_wide_slice_adapter_boundary :
    wdRunMiriSteps (wdStepHooks wdCase0Mir) 16
        (wdMkStepState wdCase0Mir wdU32Ty (wdStepD3Locals wdCase0Mir) wdStepArr3Mach) =
      .error (.invalidProgram "len on non-array") ∧
    wdRunMiriSteps (wdStepHooks wdCase5Mir) 16
        (wdMkStepState wdCase5Mir wdU32Ty (wdStepD3Locals wdCase5Mir) wdStepArr3Mach) =
      .error (.invalidProgram "len on non-array") := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- Adapter divergence (pinned, NOT a witness): the adapter faults case `8`'s uninitialized
`MaybeUninit<u32>` copy (and case `12` before its typed read) with `read of uninitialized local`,
whereas vendored `Allocation.copy` (the `lmWdObserve` authority) preserves the 4 uninit bytes. -/
theorem lm_step_uninit_union_adapter_divergence :
    wdRunMiriSteps (wdStepHooks wdCase8Mir) 16
        (wdMkStepState wdCase8Mir wdMuU32Ty (wdStepD2Locals wdCase8Mir) wdStepD2Mach) =
      .error (.undefinedBehavior "read of uninitialized local") ∧
    wdRunMiriSteps (wdStepHooks wdCase12Mir) 16
        (wdMkStepState wdCase12Mir wdU32Ty (wdStepD2Locals wdCase12Mir) wdStepD2Mach) =
      .error (.undefinedBehavior "read of uninitialized local") ∧
    lmWdObserve false 8 = .okUninitPreserved 4 0 ∧ lmWdObserve true 8 = .okUninitPreserved 4 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · rw [lmWdObserveU.eq_src]; decide +kernel
  · rw [lmWdObserveU.eq_src]; decide +kernel

end StepDriver

/-! ## §4. Capstone -/

/-- **Episode 1 LeanMiri capstone**: the 48-cell table, fail-closed range, exact mode
sensitivity, and the universal `D1`–`D4` laws of the vendored definitions (including the
universal `∀ len` trailing-slice DST struct laws and `InitMask.prepareCopy` uninit preservation). -/
theorem ep1_lean_miri_widedst_maybeuninit_capstone :
    ((List.range lmWdCaseCount).map (lmWdObserve false) = lmWdExpectedBasic ∧
      (List.range lmWdCaseCount).map (lmWdObserve true) = lmWdExpectedTb) ∧
    (∀ tb idx, lmWdCaseCount ≤ idx → lmWdObserve tb idx = .unsupported) ∧
    (∀ idx, idx < lmWdCaseCount →
      (lmWdObserve false idx ≠ lmWdObserve true idx ↔ lmWdCaseModeSensitive idx = true)) ∧
    (∀ (n : Nat) (s : Miri.Memory.Scalar Miri.Memory.Provenance) (len : UInt64),
      s.toTargetUsize (Miri.ABI.Size.fromBits LeanMiriSpec.HeapAllocAndWidePtrLM.lmLayout.pointerWidth.bits) = .ok len →
      LeanMiriSpec.HeapAllocAndWidePtrLM.lmRun
          (Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 1) (.metadata s)
            ⟨lmWdTySliceU32, lmWdSliceU32Lay⟩) =
        if 4 * len.toNat ≤ LeanMiriSpec.HeapAllocAndWidePtrLM.lmIsizeMax then
          .ok (some (Miri.ABI.Size.ofBytes (UInt64.ofNat (4 * len.toNat)), lmWdU32Lay.align.abi))
        else .error (.undefinedBehavior "InvalidMeta(SliceTooBig)")) ∧
    (∀ (n : Nat) (s : Miri.Memory.Scalar Miri.Memory.Provenance) (len : UInt64),
      s.toTargetUsize (Miri.ABI.Size.fromBits LeanMiriSpec.HeapAllocAndWidePtrLM.lmLayout.pointerWidth.bits) = .ok len →
      LeanMiriSpec.HeapAllocAndWidePtrLM.lmRun
          (Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 2) (.metadata s)
            ⟨lmWdTyHeaderSlice, lmWdHeaderSliceLay⟩) =
        if 4 * len.toNat ≤ LeanMiriSpec.HeapAllocAndWidePtrLM.lmIsizeMax then
          if 4 + 4 * len.toNat ≤ LeanMiriSpec.HeapAllocAndWidePtrLM.lmIsizeMax then
            .ok (some (Miri.ABI.Size.ofBytes (UInt64.ofNat (4 + 4 * len.toNat)), ⟨2⟩))
          else .error (.undefinedBehavior "InvalidMeta(TooBig)")
        else .error (.undefinedBehavior "InvalidMeta(SliceTooBig)")) ∧
    (∀ (n : Nat) (s : Miri.Memory.Scalar Miri.Memory.Provenance) (len : UInt64),
      s.toTargetUsize (Miri.ABI.Size.fromBits LeanMiriSpec.HeapAllocAndWidePtrLM.lmLayout.pointerWidth.bits) = .ok len →
      LeanMiriSpec.HeapAllocAndWidePtrLM.lmRun
          (Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta lmWdDynHooks () (n + 2) (.metadata s)
            ⟨lmWdTyAlign8TailU16, lmWdAlign8TailU16Lay⟩) =
        if 2 * len.toNat ≤ LeanMiriSpec.HeapAllocAndWidePtrLM.lmIsizeMax then
          if (8 + 2 * len.toNat + 7) / 8 * 8 ≤ LeanMiriSpec.HeapAllocAndWidePtrLM.lmIsizeMax then
            .ok (some (Miri.ABI.Size.ofBytes (UInt64.ofNat ((8 + 2 * len.toNat + 7) / 8 * 8)), ⟨3⟩))
          else .error (.undefinedBehavior "InvalidMeta(TooBig)")
        else .error (.undefinedBehavior "InvalidMeta(SliceTooBig)")) ∧
    (∀ (p : Miri.Memory.Pointer (Option Miri.Memory.Provenance)) (a b : Int64),
      (p.wrappingSignedOffset a LeanMiriSpec.HeapAllocAndWidePtrLM.lmPtrArith >>= fun q =>
          q.wrappingSignedOffset b LeanMiriSpec.HeapAllocAndWidePtrLM.lmPtrArith) =
        p.wrappingSignedOffset (a + b) LeanMiriSpec.HeapAllocAndWidePtrLM.lmPtrArith) ∧
    (∀ v : Miri.ABI.U128, Miri.ABI.WrappingRange.contains
        ⟨BitVec.ofNat 128 1, BitVec.ofNat 128 (2 ^ 64 - 1)⟩ v = true ↔
      1 ≤ v.toNat ∧ v.toNat ≤ 2 ^ 64 - 1) ∧
    (lmWdRun (lmWdUnionCopyObs false 1 (some (1, 2))) = .okUninitPreserved 1 1 ∧
      lmWdRun (lmWdUnionCopyObs true 1 (some (1, 2))) = .okUninitPreserved 1 1 ∧
      lmWdObserve false 13 = .ub ∧ lmWdObserve true 13 = .ub) :=
  ⟨lmWdObserve_table, lmWdObserve_out_of_range, lmWdObserve_mode_sensitivity.2.2,
   lm_sizeAndAlign_sliceU32, lm_sizeAndAlign_headerSlice, lm_sizeAndAlign_align8TailU16,
   lm_wrapping_compose, lm_fnptr_range_contains_iff, lm_case13_union_copy_of_invalid_bool_byte_ok⟩

/-- **Episode 1 LeanMiri universal-laws, non-vacuity witnesses & Step-driver capstone** (symmetric
with `MiniRustSpec.WideDstAndMaybeUninitMR.ep1_minirust_universal_laws_capstone`): bundles the
remaining universal `D1`–`D4` laws (`str` / ZST `[()]`, `InitMask.prepareCopy` / `Allocation.copy`,
`readScalar` uninit UB, `checkPrimitive .boolean`, `ptrOffsetInbounds`, `scalarMayBeNull`,
`Validity.checkScalar` at `pointerLayoutData true`), all concrete non-vacuity witnesses, the
11-fixture `Step.step` capstone, and the pinned `Step.step` adapter boundary theorems. -/
theorem ep1_lean_miri_universal_laws_capstone :
    type_of% lm_sizeAndAlign_str ∧
    type_of% lm_sizeAndAlign_sliceUnit ∧
    type_of% lm_sizeAndAlign_str_and_unit_witnesses ∧
    type_of% lm_initMask_prepareCopy_lazy_uninit ∧
    type_of% @lm_allocation_copy_uninit_preserves ∧
    type_of% lm_allocation_copy_uninit_witness ∧
    type_of% lm_checkPrimitive_bool_invalid_witness ∧
    type_of% @lm_ptrOffsetInbounds_eq_wrapping ∧
    type_of% lm_ptrOffsetInbounds_ok_witness ∧
    type_of% @lm_scalarMayBeNull_int ∧
    type_of% @lm_checkScalar_fnptr_int ∧
    type_of% lm_checkScalar_fnptr_int_witnesses ∧
    type_of% ep1_lean_miri_step_driver_capstone ∧
    type_of% lm_step_union_copy_adapter_unsupported ∧
    type_of% lm_step_uninit_union_adapter_divergence ∧
    type_of% lm_step_wide_slice_adapter_boundary :=
  ⟨lm_sizeAndAlign_str, lm_sizeAndAlign_sliceUnit, lm_sizeAndAlign_str_and_unit_witnesses,
   lm_initMask_prepareCopy_lazy_uninit, @lm_allocation_copy_uninit_preserves,
   lm_allocation_copy_uninit_witness, lm_checkPrimitive_bool_invalid_witness,
   @lm_ptrOffsetInbounds_eq_wrapping, lm_ptrOffsetInbounds_ok_witness,
   @lm_scalarMayBeNull_int, @lm_checkScalar_fnptr_int, lm_checkScalar_fnptr_int_witnesses,
   ep1_lean_miri_step_driver_capstone, lm_step_union_copy_adapter_unsupported,
   lm_step_uninit_union_adapter_divergence, lm_step_wide_slice_adapter_boundary⟩

section AxiomAudit
open Lean Elab Command

run_cmd do
  let env ← getEnv
  -- 1. Strict root isolation: ZERO `MiniRustSpec.*` and ZERO `Anneal.*` imports, even transitively!
  for modName in env.header.moduleNames do
    if (`MiniRustSpec).isPrefixOf modName || (`Anneal).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported by LeanMiriSpec.WideDstAndMaybeUninitLM"
  let ns := `LeanMiriSpec.WideDstAndMaybeUninitLM
  -- 2. Bridge-reality audit: our theorems transitively reach the real vendored Miri constants.
  let bridgeReq : List (Lean.Name × Lean.Name) :=
    [ (ns ++ `lmWdObserve_table, `Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta),
      (ns ++ `lmWdObserve_table, `Miri.Interpreter.projectIndex),
      (ns ++ `lmWdObserve_table, `Miri.Interpreter.projectField),
      (ns ++ `lmWdObserve_table, `Miri.Interpreter.OpTy.transmute),
      (ns ++ `lmWdObserve_table, `Miri.Interpreter.OpTy.len),
      (ns ++ `lmWdObserve_table, `Miri.Interpreter.projectionMemoryOffset),
      (ns ++ `lmWdObserve_table, `Miri.Memory.Allocation.copy),
      (ns ++ `lmWdObserve_table, `Miri.Memory.Allocation.writeScalar),
      (ns ++ `lmWdObserve_table, `Miri.Memory.Allocation.readScalar),
      (ns ++ `lmWdObserve_table, `Miri.Memory.InitMask.get),
      (ns ++ `lmWdObserve_table, `Miri.Interpreter.ptrOffsetInbounds),
      (ns ++ `lmWdObserve_table, `Miri.Memory.Pointer.wrappingSignedOffset),
      (ns ++ `lmWdObserve_table, `Miri.Memory.Validity.checkScalar),
      (ns ++ `lmWdObserve_table, `Miri.Memory.Validity.checkPrimitive),
      (ns ++ `lmWdObserve_table, `LeanMiriSpec.Correspondence.pointerLayoutData),
      (ns ++ `lmWdObserve_table, `LeanMiriSpec.HeapAllocAndWidePtrLM.lmRetag),
      (ns ++ `lmWdObserve_table, `LeanMiriSpec.HeapAllocAndWidePtrLM.lmLoad),
      (ns ++ `lmWdObserve_table, `LeanMiriSpec.HeapAllocAndWidePtrLM.lmTreeAccess),
      (ns ++ `lm_initMask_applyCopy_uninit_preserves, `Miri.Memory.InitMask.applyCopy),
      (ns ++ `lm_initMask_prepareCopy_lazy_uninit, `Miri.Memory.InitMask.prepareCopy),
      (ns ++ `lm_allocation_copy_uninit_preserves, `Miri.Memory.Allocation.copy),
      (ns ++ `lm_step_wdCase14_ok, `Miri.Interpreter.Step.step),
      (ns ++ `lm_step_wdCase21_null_fnptr_ub, `Miri.Interpreter.Step.step),
      (ns ++ `lm_step_wdCase21_null_fnptr_ub, `Miri.Memory.Validity.checkScalar),
      (ns ++ `lm_scalarMayBeNull_int, `Miri.Interpreter.ValidityMachine.scalarMayBeNull),
      (ns ++ `lm_readScalar_uninit_ub, `Miri.Memory.Allocation.readScalar),
      (ns ++ `lm_checkScalar_fnptr_int, `Miri.Memory.Validity.checkScalar) ]
  for (thm, req) in bridgeReq do
    let some ci := env.find? thm | throwError "bridge audit: {thm} missing"
    let mut seen : NameSet := {}
    let mut todo : Array Lean.Name := ci.type.getUsedConstants
    if let .defnInfo v := ci then
      todo := todo ++ v.value.getUsedConstants
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      if n == req then break
      if ns.isPrefixOf n then
        if let some (.defnInfo v) := env.find? n then
          todo := todo ++ v.value.getUsedConstants
    unless seen.contains req do
      throwError "shadow-evaluator audit: {thm} does not reach real {req}"
  -- 3. Standard-3-axiom purity & non-vacuous theorem count floor.
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    for a in ← liftCoreM <| Lean.collectAxioms c do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "{c} depends on forbidden axiom {a}"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    if ns.isPrefixOf c && !c.isInternal then
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 57 then
    throwError "axiom audit vacuous: only {theorems} theorems seen"

end AxiomAudit

end LeanMiriSpec.WideDstAndMaybeUninitLM
