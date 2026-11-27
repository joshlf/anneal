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

/-- `D2` **universal `readScalar` UB law**: vendored `Allocation.readScalar` faults with `invalidUninitBytes` whenever the `InitMask` reports an uninitialized sub-range, for every allocation, layout, and range. -/
theorem lm_readScalar_uninit_ub {Prov Extra : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (a : Allocation Prov Extra) (layout : TargetDataLayout) (range : AllocRange) (rp : Bool)
    (bad : AllocRange) (h : a.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    a.readScalar layout range rp = .error (.invalidUninitBytes (some ⟨range, bad⟩)) := by
  unfold Allocation.initializationMask at h
  simp only [Allocation.readScalar, h]
  rfl

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

end UniversalLaws

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
      (ns ++ `lm_readScalar_uninit_witness, `Miri.Memory.InitMask.prepareCopy),
      (ns ++ `lm_scalarMayBeNull_int, `Miri.Interpreter.ValidityMachine.scalarMayBeNull),
      (ns ++ `lm_readScalar_uninit_ub, `Miri.Memory.Allocation.readScalar) ]
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
  if theorems < 20 then
    throwError "axiom audit vacuous: only {theorems} theorems seen"

end AxiomAudit

end LeanMiriSpec.WideDstAndMaybeUninitLM
