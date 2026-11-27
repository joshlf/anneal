/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Trusted
import MiniRustSpec.Interp
import MiniRustSpec.CrossFrameRefAndPanicMR

/-!
# Episode 1 MiniRust Authority: Wide-Slice / Trailing-Slice DSTs, `MaybeUninit<T>` /
# `ManuallyDrop<T>` Byte Transport, Multi-Step Pointer-Offset Chains, and the `minirust#300`
# Non-Null `FnPtr` Delta (`MiniRustSpec.WideDstAndMaybeUninitMR`)

Operational correspondence between unmodified MiniRust `d821c6e3` (`MiniRustSpec.Interp` over
both `BasicMemory<x86_64>` `Mach` and `TreeBorrowsMemory<x86_64>` `MachTB`) and unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics` (`stepMirFn`) on the frozen 24-case (`0..23`) × 2-mode
matrix shared with `LeanMiriSpec.WideDstAndMaybeUninitLM`:

* `D1` (`0..7`): `[T]` / `str` wide raw pointers (`AggregateKind.rawPtr`, `UnOp.ptrMetadata`,
  `Rvalue.len`, checked indexing), `size_of_val` / `align_of_val` on `[u32]`, ZST `[()]`, empty
  `str`, the exact `isize::MAX` boundary, and the `#[repr(C)]` trailing-slice DST structs
  `HeaderSlice { tag: u8, data: [u32] }` / `Align8TailU16 { hdr: u64, tail: [u16] }`
  (`LayoutStrategy.compute_size_and_align (.Tuple head (.Slice ..))`), paired with the honest
  Trusted `intrinsicWidePointeeStep` `.unsupported` boundary for custom unsized ADTs.
* `D2` (`8..13`): whole-union copies of `MaybeUninit<u32>` / `MaybeUninit<bool>` preserving
  uninitialized and invalid bytes (`Type.Union`), `ManuallyDrop<u32>` transport, and read-time
  typed validity UB (`kani#5205` / `#5196`).
* `D3` (`14..19`): multi-step cast + in-bounds / wrapping pointer-offset chains, OOB faults, and
  the unique Tree Borrows mode-sensitive case `19` (write through a `Frozen`-derived pointer).
* `D4` (`20..23`): the pinned `d821c6e3` `checkPtr` accepts a null `FnPtr` while Trusted
  (`decodePtrBytesNoForge true`) rejects it; the post-`minirust#300` predicate
  `checkPtrFnNonNull` / `checkPtrFnNonNullM` is defined HERE (zero edits to `Interp.lean`) and
  coincides with `checkPtr` everywhere except null function pointers.

Every MiniRust cell executes a real `Program` through `bootProgramM` / `runToStopM` (`stepM`),
and every Trusted cell executes a real `CapturedMir` fixture through `stepMirFn`.

Root isolation: imports strictly `Lean`, `Trusted`, `MiniRustSpec.Interp`, and
`MiniRustSpec.CrossFrameRefAndPanicMR` (zero `Anneal.*`, `Miri.*`, or `LeanMiriSpec.*`; verified by
the trailing `run_cmd` audit).
-/

namespace MiniRustSpec.WideDstAndMaybeUninitMR

set_option Elab.async false

/-! ## §0. Frozen Observation Interface, Kernel Helpers, and Shared `CapturedMir` Fixtures -/

/-- Frozen cross-authority observation domain (constructor order shared identically with
`LeanMiriSpec.WideDstAndMaybeUninitLM.LmWdObs`). -/
inductive MrWdObs : Type where
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
  /-- MiniRust well-formedness specification panic. -/
  | specPanic
  deriving DecidableEq, Repr

/-- Number of canonical cases (`0..23`, 48 mode cells). -/
def mrWdCaseCount : Nat := 24

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
def wdCombine (a b : MrWdObs) : MrWdObs := if a = b then a else .unsupported

/-! ### Shared `CapturedMir` fixtures

Every definition in this section is shared verbatim (same text, same opened namespaces) with
`LeanMiriSpec.WideDstAndMaybeUninitLM`, so Episode 2's cross-root bridge can lock each fixture
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

/-! ## §1. Direct Trusted `stepMirFn` Execution (`mrTrustedWdObserve`) -/

section TrustedRunner

open Trusted.Effect Trusted.ITree Trusted.Sequence
open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics Trusted.Rustc.V2026_06_01.Layout

/-- How the return value of a fixture is observed. -/
inductive WdRetKind : Type where
  /-- A scalar result (`.scalar ⟨bits, _⟩`). -/
  | scalar
  /-- A `(usize, usize)` tuple `(size_of_val, align_of_val)`. -/
  | sizeAlign
  /-- A whole union value, re-encoded by the Trusted codec `encodeTypedValueToBytes`. -/
  | unionBytes (ty : Ty)
  /-- A pointer validated by Trusted (`.ptr p 8` with intact provenance, or provenance-free `0`). -/
  | fnPtr

/-- Whether a Trusted `AbstractByte` is initialized. -/
def wdTrustedByteInit : AbstractByte → Bool
  | .uninit => false
  | _ => true

/-- Observe a Trusted return value under the fixture's return kind. -/
def wdTrustedRetObs : WdRetKind → MirSemantics.Value → MrWdObs
  | .scalar, .scalar ⟨bits, _⟩ => .okScalar bits
  | .sizeAlign, .aggregate 0 [.scalar ⟨s, 8⟩, .scalar ⟨a, 8⟩] => .okSizeAlign s a
  | .unionBytes ty, v =>
    match encodeTypedValueToBytes wdLayouts ty v with
    | some bs => .okUninitPreserved bs.length (bs.filter wdTrustedByteInit).length
    | none => .unsupported
  | .fnPtr, .ptr p 8 => .okFnPtr p.allocId
  | .fnPtr, .scalar ⟨0, 8⟩ => .okFnPtr 0
  | _, _ => .unsupported

/-- State of a bounded Trusted `stepMirFn` execution. -/
inductive WdTrustedRun : Type where
  | running (s : MachineState)
  | done (o : MrWdObs)

/-- One `stepMirFn` step of the bounded Trusted runner (no shadow evaluation: every transition is
read off `stepMirFn`'s own `MirStepNode`). -/
def wdTrustedStep (k : WdRetKind) (body : CapturedMir) : WdTrustedRun → WdTrustedRun
  | .done o => .done o
  | .running s =>
    match stepMirFn body s with
    | .tau (.running s') => .running s'
    | .vis (.inr (.inl (.emit _))) cont =>
      match cont PUnit.unit with
      | .running s' => .running s'
      | _ => .done .unsupported
    | .ret (.normal r) => .done (wdTrustedRetObs k r.1)
    | .vis (.inl (.fail .ub)) _ => .done .ub
    | .vis (.inl (.fail .unsupported)) _ => .done .unsupported
    | _ => .done .unsupported

/-- Execute `stepMirFn` for up to `fuel` steps (fail-closed `.unsupported` on fuel exhaustion). -/
def wdRunTrusted (k : WdRetKind) (body : CapturedMir) (fuel : Nat) (s : MachineState) : MrWdObs :=
  match Nat.repeat (wdTrustedStep k body) fuel (.running s) with
  | .done o => o
  | .running _ => .unsupported

/-- Initial Trusted state with every declared local live (`.uninit` temporaries, `.init` args). -/
def wdLiveState (body : CapturedMir) (args : List MirSemantics.Value) : MachineState :=
  let base := initMachineState body args
  { base with
    frame := { base.frame with
      locals := base.frame.locals.map fun
        | .dead => .uninit
        | slot => slot } }

/-- `[11, 22, 33] : [u32; 3]` (`D1` backing array). -/
def wdArrD1 : MirSemantics.Value := .aggregate 0 [.scalar ⟨11, 4⟩, .scalar ⟨22, 4⟩, .scalar ⟨33, 4⟩]
/-- `[100, 200, 300] : [u32; 3]` (`D3` backing array). -/
def wdArrD3 : MirSemantics.Value :=
  .aggregate 0 [.scalar ⟨100, 4⟩, .scalar ⟨200, 4⟩, .scalar ⟨300, 4⟩]

/-- Case `19` initial Trusted state: borrow tag `1` on `_1` (`[0, 12)`) carries an active
`FnEntry` protector exactly in Tree Borrows mode (`tb = true`), matching MiniRust's
`Validate(_, true)` under `TreeBorrowsMemory`. -/
def wdCase19TrustedInit (tb : Bool) : MachineState :=
  let base := wdLiveState wdCase19Mir [wdArrD3]
  let bEntry : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetProjection := [], perm := .active,
      rangeOffset := 0, rangeLen := 12, protector := if tb then some 1 else none,
      parentTag := none, targetFrameDepth := 0, allocDead := false }
  { base with
    memory := { base.memory with
      borrows := [bEntry]
      activeProtectors := if tb then [1] else [] } }

/-- Step budget of every Trusted execution. -/
def wdTrustedFuel : Nat := 40

/-- The Trusted run of case `idx` (primary query). -/
def wdTrustedPrimary (tb : Bool) : Nat → Option MrWdObs
  | 0 => some (wdRunTrusted .scalar wdCase0Mir wdTrustedFuel (wdLiveState wdCase0Mir [wdArrD1]))
  | 1 => some (wdRunTrusted .sizeAlign wdCase1Mir wdTrustedFuel (wdLiveState wdCase1Mir [wdArrD1]))
  | 2 => some (wdRunTrusted .sizeAlign wdCase2Mir wdTrustedFuel (wdLiveState wdCase2Mir [wdArrD1]))
  | 3 => some (wdRunTrusted .sizeAlign wdCase3Mir wdTrustedFuel (wdLiveState wdCase3Mir [wdArrD1]))
  | 4 => some (wdRunTrusted .sizeAlign wdCase4Mir wdTrustedFuel (wdLiveState wdCase4Mir [wdArrD1]))
  | 5 => some (wdRunTrusted .scalar wdCase5Mir wdTrustedFuel (wdLiveState wdCase5Mir [wdArrD1]))
  | 6 => some (wdRunTrusted .sizeAlign wdCase6Mir wdTrustedFuel (wdLiveState wdCase6Mir [wdArrD1]))
  | 7 => some (wdRunTrusted .sizeAlign wdCase7Mir wdTrustedFuel (wdLiveState wdCase7Mir [wdArrD1]))
  | 8 => some (wdRunTrusted (.unionBytes wdMuU32Ty) wdCase8Mir wdTrustedFuel (wdLiveState wdCase8Mir []))
  | 9 => some (wdRunTrusted (.unionBytes wdMuU32Ty) wdCase9Mir wdTrustedFuel (wdLiveState wdCase9Mir []))
  | 10 => some (wdRunTrusted .scalar wdCase10Mir wdTrustedFuel (wdLiveState wdCase10Mir []))
  | 11 => some (wdRunTrusted .scalar wdCase11Mir wdTrustedFuel (wdLiveState wdCase11Mir []))
  | 12 => some (wdRunTrusted .scalar wdCase12Mir wdTrustedFuel (wdLiveState wdCase12Mir []))
  | 13 => some (wdRunTrusted .scalar wdCase13Mir wdTrustedFuel (wdLiveState wdCase13Mir []))
  | 14 => some (wdRunTrusted .scalar wdCase14Mir wdTrustedFuel (wdLiveState wdCase14Mir [wdArrD3]))
  | 15 => some (wdRunTrusted .scalar wdCase15Mir wdTrustedFuel (wdLiveState wdCase15Mir [wdArrD3]))
  | 16 => some (wdRunTrusted .scalar wdCase16Mir wdTrustedFuel (wdLiveState wdCase16Mir [wdArrD3]))
  | 17 => some (wdRunTrusted .scalar wdCase17Mir wdTrustedFuel (wdLiveState wdCase17Mir [wdArrD3]))
  | 18 => some (wdRunTrusted .scalar wdCase18Mir wdTrustedFuel (wdLiveState wdCase18Mir [wdArrD3]))
  | 19 => some (wdRunTrusted .scalar wdCase19Mir wdTrustedFuel (wdCase19TrustedInit tb))
  | 20 => some (wdRunTrusted .fnPtr wdCase20Mir wdTrustedFuel
      (wdLiveState wdCase20Mir [.ptr { allocId := 1, offsetBytes := 0 } 8]))
  | 21 => some (wdRunTrusted .fnPtr wdCase21Mir wdTrustedFuel
      (wdLiveState wdCase21Mir [.scalar ⟨0, 8⟩]))
  | 22 => some (wdRunTrusted .fnPtr wdCase21Mir wdTrustedFuel
      (wdLiveState wdCase21Mir [.scalar ⟨0, 8⟩]))
  | 23 => some (wdRunTrusted .fnPtr wdCase23Mir wdTrustedFuel
      (wdLiveState wdCase23Mir [.scalar ⟨0, 8⟩]))
  | _ => none

/-- The Trusted run of the secondary query of a two-query case (`2`: empty `str`). -/
def wdTrustedSecondary : Nat → Option MrWdObs
  | 2 => some (wdRunTrusted .sizeAlign wdCase2StrMir wdTrustedFuel (wdLiveState wdCase2StrMir [wdArrD1]))
  | _ => none

/-- **Real Trusted observer**: executes `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` on
the frozen `CapturedMir` fixture of each case (fail-closed `.unsupported` for `idx ≥ 24`). -/
def mrTrustedWdObserve (tb : Bool) (idx : Nat) : MrWdObs :=
  match wdTrustedPrimary tb idx with
  | none => .unsupported
  | some o =>
    match wdTrustedSecondary idx with
    | none => o
    | some o' => wdCombine o o'

end TrustedRunner

/-- Frozen expected Trusted table for `tb = false`. -/
def mrTrustedExpectedBasic : List MrWdObs :=
  [.okScalar 22, .okSizeAlign 12 4, .okSizeAlign 0 1, .okSizeAlign 9223372036854775804 4, .ub, .ub,
   .unsupported, .unsupported,
   .okUninitPreserved 4 0, .okUninitPreserved 4 1, .okScalar 305419896, .okScalar 77, .ub, .ub,
   .okScalar 200, .okScalar 200, .ub, .ub, .okScalar 100, .okScalar 999,
   .okFnPtr 1, .ub, .ub, .okFnPtr 0]

/-- Frozen expected Trusted table for `tb = true` (only case `19` differs). -/
def mrTrustedExpectedTb : List MrWdObs :=
  [.okScalar 22, .okSizeAlign 12 4, .okSizeAlign 0 1, .okSizeAlign 9223372036854775804 4, .ub, .ub,
   .unsupported, .unsupported,
   .okUninitPreserved 4 0, .okUninitPreserved 4 1, .okScalar 305419896, .okScalar 77, .ub, .ub,
   .okScalar 200, .okScalar 200, .ub, .ub, .okScalar 100, .ub,
   .okFnPtr 1, .ub, .ub, .okFnPtr 0]

/-- **Kernel-checked 48-cell Trusted table**: every cell executes `stepMirFn` on its fixture. -/
theorem mrTrustedWdObserve_table :
    (List.range mrWdCaseCount).map (mrTrustedWdObserve false) = mrTrustedExpectedBasic ∧
    (List.range mrWdCaseCount).map (mrTrustedWdObserve true) = mrTrustedExpectedTb := by
  constructor <;> kernel_rfl

/-- Out-of-range Trusted cases are fail-closed `.unsupported`. -/
theorem mrTrustedWdObserve_out_of_range (tb : Bool) (idx : Nat) (h : mrWdCaseCount ≤ idx) :
    mrTrustedWdObserve tb idx = .unsupported := by
  unfold mrWdCaseCount at h
  have hNone : wdTrustedPrimary tb idx = none := by
    unfold wdTrustedPrimary
    split <;> first | rfl | omega
  unfold mrTrustedWdObserve
  rw [hNone]

/-- **Case `13` Trusted companion (`kani#5205` / `#5196`)**: copying the whole `MaybeUninit<bool>`
holding raw byte `2` (`wdCase13CopyMir`) succeeds under real `stepMirFn` and preserves the 1
initialized byte, while the typed `bool` read (case `13`) is `.ub` in both modes. -/
theorem mrTrusted_case13_union_copy_of_invalid_bool_byte_ok :
    wdRunTrusted (.unionBytes wdMuBoolTy) wdCase13CopyMir wdTrustedFuel
        (wdLiveState wdCase13CopyMir []) = .okUninitPreserved 1 1 ∧
    mrTrustedWdObserve false 13 = .ub ∧ mrTrustedWdObserve true 13 = .ub := by
  refine ⟨?_, ?_, ?_⟩ <;> kernel_rfl

/-- **Exact Trusted Tree Borrows mode-sensitivity `↔`**: `mrTrustedWdObserve` disagrees between
`tb = false` and `tb = true` on `idx < 24` if and only if `idx = 19`. -/
theorem mrTrustedWdObserve_mode_sensitivity :
    mrTrustedWdObserve false 19 = .okScalar 999 ∧
    mrTrustedWdObserve true 19 = .ub ∧
    (∀ idx, idx < mrWdCaseCount →
      (mrTrustedWdObserve false idx ≠ mrTrustedWdObserve true idx ↔ idx = 19)) := by
  have hB := mrTrustedWdObserve_table.1
  have hT := mrTrustedWdObserve_table.2
  have hAll : ((List.range mrWdCaseCount).all fun idx =>
      decide ((mrTrustedExpectedBasic[idx]? ≠ mrTrustedExpectedTb[idx]?) ↔ idx = 19)) = true := by
    decide
  have cellB : ∀ idx, idx < mrWdCaseCount →
      some (mrTrustedWdObserve false idx) = mrTrustedExpectedBasic[idx]? := by
    intro idx hi
    have h' := congrArg (fun l => l[idx]?) hB
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  have cellT : ∀ idx, idx < mrWdCaseCount →
      some (mrTrustedWdObserve true idx) = mrTrustedExpectedTb[idx]? := by
    intro idx hi
    have h' := congrArg (fun l => l[idx]?) hT
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  refine ⟨Option.some.inj (cellB 19 (by decide)), Option.some.inj (cellT 19 (by decide)), ?_⟩
  intro idx hi
  have hIff := of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr hi))
  rw [← cellB idx hi, ← cellT idx hi] at hIff
  simpa [Option.some.injEq] using hIff


/-! ### Trusted root causes of the documented `D1` / `D4` cells -/

section TrustedRootCauses

open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst Trusted.Rustc.V2026_06_01.MirSemantics

/-- `D4` **Trusted root cause (universal)**: a provenance-free pointer image never decodes at a
function-pointer type (`decodeTypedValueFromBytes` routes `.fnPtr` to
`decodePtrBytesNoForge true`), so the null `fn()` of cases `21` / `22` is UB in Trusted. -/
theorem trusted_decodePtrBytesNoForge_fnptr_provless (ptrBytes : Nat) (bytes : List AbstractByte)
    (sv : ScalarVal) (hdec : decodeScalarBytes bytes false = some (sv, none)) :
    decodePtrBytesNoForge true (.tuple []) ptrBytes bytes = none := by
  unfold decodePtrBytesNoForge
  simp only [hdec]
  split <;> (try split) <;> simp_all

/-- `D4` **Trusted raw-pointer contrast (universal)**: the same provenance-free image decodes to
its address at a raw `*const u8` (`decodePtrBytesNoForge false`), as in case `23`. -/
theorem trusted_decodePtrBytesNoForge_raw_provless (pointee : RigidTy) (ptrBytes : Nat)
    (bytes : List AbstractByte) (sv : ScalarVal)
    (hthin : pointee = .uint .u8)
    (hlen : Trusted.Sequence.length bytes = ptrBytes) (hdec : decodeScalarBytes bytes false = some (sv, none)) :
    decodePtrBytesNoForge false pointee ptrBytes bytes = some (.scalar ⟨sv.bits, ptrBytes⟩) := by
  subst hthin
  unfold decodePtrBytesNoForge
  simp only [hdec]
  split <;> (try split) <;> simp_all

/-- `D4` **Trusted root cause at `decodeTypedValueFromBytes` (universal)**: for EVERY function
pointer signature and layout table, decoding any provenance-free byte image fails (`none` -> UB),
explaining cases `21` and `22` directly from `decodeTypedValueFromBytes`. -/
theorem trusted_decodeTypedValueFromBytes_fnPtr_provless (fuel : Nat) (layouts : Layout.LayoutTable)
    (inputs : List RigidTy) (output : RigidTy) (safety : Safety) (abi : Layout.CallConv)
    (layoutIdx : Nat) (bytes : List AbstractByte) (sv : ScalarVal)
    (hdec : decodeScalarBytes bytes false = some (sv, none)) :
    decodeTypedValueFromBytes (fuel + 1) layouts
      ⟨.fnPtr inputs output safety abi, layoutIdx⟩ bytes = none := by
  unfold decodeTypedValueFromBytes normalizeCodecTy
  exact trusted_decodePtrBytesNoForge_fnptr_provless (layoutPointerBytes layouts) bytes sv hdec

/-- `D4` **Trusted raw-pointer contrast at `decodeTypedValueFromBytes` (universal)**: for EVERY
mutability and layout table, the same provenance-free byte image of pointer width decodes to
`.scalar ⟨sv.bits, layoutPointerBytes layouts⟩` at `*const u8` / `*mut u8`, explaining case `23`. -/
theorem trusted_decodeTypedValueFromBytes_rawU8_provless (fuel : Nat) (layouts : Layout.LayoutTable)
    (m : Mutability) (layoutIdx : Nat) (bytes : List AbstractByte) (sv : ScalarVal)
    (hlen : Trusted.Sequence.length bytes = layoutPointerBytes layouts)
    (hdec : decodeScalarBytes bytes false = some (sv, none)) :
    decodeTypedValueFromBytes (fuel + 1) layouts
      ⟨.rawPtr m (.uint .u8), layoutIdx⟩ bytes =
      some (.scalar ⟨sv.bits, layoutPointerBytes layouts⟩) := by
  unfold decodeTypedValueFromBytes normalizeCodecTy
  exact trusted_decodePtrBytesNoForge_raw_provless (.uint .u8) (layoutPointerBytes layouts)
    bytes sv rfl hlen hdec

/-- `D4` non-vacuity witness for `trusted_decodeTypedValueFromBytes_{fnPtr,rawU8}_provless`:
8 initialized zero bytes without provenance fail at `wdFnPtrTy` and decode to `0usize` at
`wdRawU8Ty`. -/
theorem trusted_decodeTypedValueFromBytes_null_witness :
    decodeTypedValueFromBytes 8 wdLayouts wdFnPtrTy (List.replicate 8 (.init 0 none)) = none ∧
    decodeTypedValueFromBytes 8 wdLayouts wdRawU8Ty (List.replicate 8 (.init 0 none)) =
      some (.scalar ⟨0, 8⟩) :=
  ⟨trusted_decodeTypedValueFromBytes_fnPtr_provless 7 wdLayouts [] (.uint .u32) .safe .rust 0
      (List.replicate 8 (.init 0 none)) ⟨0, 8⟩ rfl,
   trusted_decodeTypedValueFromBytes_rawU8_provless 7 wdLayouts .not 0
      (List.replicate 8 (.init 0 none)) ⟨0, 8⟩ rfl rfl⟩

/-- `D1` **universal honest Trusted boundary**: `intrinsicWidePointeeStep` returns `.unsupported`
on EVERY custom ADT pointee (not only the two concrete DST structs). -/
theorem trusted_intrinsicWidePointeeStep_adt_unsupported (name : DefPath) (args : List RigidTy) :
    intrinsicWidePointeeStep (.adt name args) = .unsupported := rfl

/-- `D1` **honest Trusted boundary** (concrete instances for cases `6` and `7`). -/
theorem trusted_intrinsicWidePointeeStep_dst_unsupported :
    intrinsicWidePointeeStep wdHeaderSliceRigid = .unsupported ∧
    intrinsicWidePointeeStep wdAlign8TailU16Rigid = .unsupported :=
  ⟨trusted_intrinsicWidePointeeStep_adt_unsupported "wd::HeaderSlice" [],
   trusted_intrinsicWidePointeeStep_adt_unsupported "wd::Align8TailU16" []⟩

end TrustedRootCauses

/-! ## §2. Post-`minirust#300` Non-Null `FnPtr` Validity Predicate (Defined Here, Zero
`Interp.lean` Edits)

Upstream `minirust#300` (`374bf855`) adds a non-null check for function pointers to
`Machine::check_ptr`; the pinned `d821c6e3` `checkPtr` / `checkPtrM` predate it and accept a
null `FnPtr`. `checkPtrFnNonNull` / `checkPtrFnNonNullM` add exactly that check and delegate to
the unmodified pinned predicate in every other situation. -/

section FnPtrNonNull

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp

/-- Post-`#300` `check_ptr` on `Mach` (`BasicMemory<x86_64>`). -/
def checkPtrFnNonNull (ptr : Pointer Prov) (ptrTy : PtrType) (m : Option Mach := none) :
    Interp Unit :=
  match ptrTy with
  | .FnPtr => do
    ensureElseUb (ptr.thin_pointer.addr != 0) "Value::Ptr: null function pointer"
    checkPtr ptr ptrTy m
  | _ => checkPtr ptr ptrTy m

/-- Post-`#300` `check_ptr`, polymorphic over every memory model (`Mach` and `MachTB`). -/
def checkPtrFnNonNullM {M : Type} [Memory M] [MemoryOps M] (ptr : Pointer (Memory.Provenance M))
    (ptrTy : PtrType) (m : Option (Machine M) := none) : Interp Unit :=
  match ptrTy with
  | .FnPtr => do
    ensureElseUb (ptr.thin_pointer.addr != 0) "Value::Ptr: null function pointer"
    checkPtrM ptr ptrTy m
  | _ => checkPtrM ptr ptrTy m

end FnPtrNonNull

/-! ## §3. Canonical 24-Case MiniRust Program Suite on `Mach` and `MachTB` (`mrWdObserve`)

Root programs store `(kind, a, b)` in locals `(0, 1, 2)` before `Intrinsic.Exit`:
`kind = 0 ⇒ okScalar a`, `1 ⇒ okSizeAlign a b`, `2 ⇒ okUninitPreserved` read off the bytes of
the union local `_4` (`Value.Union` chunk data), and `3 / 4 / 5 ⇒ okFnPtr` read off the pointer
in `_4` (function name via `fn_ptrs`, or address `0`) after re-validating it with, respectively,
the pinned `d821c6e3` `checkPtrM _ .FnPtr`, the post-`#300` `checkPtrFnNonNullM _ .FnPtr`, and
the post-`#300` `checkPtrFnNonNullM _ (.Raw .None)` (raw `*const u8`). -/

section MiniRustPrograms

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
open MiniRustSpec.CrossFrameRefAndPanicMR

/-! ### MiniRust types and builders -/
@[reducible] def mrU8IntTy : IntType := ⟨.Unsigned, ⟨1⟩⟩
@[reducible] def mrU16IntTy : IntType := ⟨.Unsigned, ⟨2⟩⟩
@[reducible] def mrU64IntTy : IntType := ⟨.Unsigned, ⟨8⟩⟩
@[reducible] def mrU8Ty : «Type» := .Int mrU8IntTy
@[reducible] def mrU16Ty : «Type» := .Int mrU16IntTy
@[reducible] def mrU64Ty : «Type» := .Int mrU64IntTy
@[reducible] def mrUsizeTy : «Type» := .Int IntType.usize_ty
@[reducible] def mrArr3Ty : «Type» := .Array u32Ty 3
@[reducible] def mrWideRawTy : «Type» := .Ptr (.Raw .ElementCount)
@[reducible] def mrPairTy : «Type» :=
  .Tuple [(⟨0⟩, rawThinTy), (⟨8⟩, mrUsizeTy)] ⟨⟨16⟩, ⟨8⟩, none⟩ none
@[reducible] def mrSliceU32Ty : «Type» := .Slice u32Ty
@[reducible] def mrSliceUnitTy : «Type» := .Slice unitType
@[reducible] def mrStrTy : «Type» := .Slice mrU8Ty
@[reducible] def mrHeaderSliceTy : «Type» :=
  .Tuple [(⟨0⟩, mrU8Ty)] ⟨⟨1⟩, ⟨1⟩, none⟩ (some (.Slice u32Ty))
@[reducible] def mrAlign8TailU16Ty : «Type» :=
  .Tuple [(⟨0⟩, mrU64Ty)] ⟨⟨8⟩, ⟨8⟩, none⟩ (some (.Slice mrU16Ty))
@[reducible] def mrSliceU32Pointee : PointeeInfo :=
  { layout := .Slice ⟨4⟩ ⟨4⟩, inhabited := true, unsafe_cells := .Slice [], freeze := true,
    unpin := true }
@[reducible] def mrSliceU32RefTy : «Type» := .Ptr (.Ref .Immutable mrSliceU32Pointee)
@[reducible] def mrMuU32Ty : «Type» :=
  .Union [(⟨0⟩, unitType), (⟨0⟩, u32Ty), (⟨0⟩, mrU8Ty)] [(⟨0⟩, ⟨4⟩)] ⟨4⟩ ⟨4⟩
@[reducible] def mrMuBoolTy : «Type» :=
  .Union [(⟨0⟩, unitType), (⟨0⟩, .Bool), (⟨0⟩, mrU8Ty)] [(⟨0⟩, ⟨1⟩)] ⟨1⟩ ⟨1⟩
@[reducible] def mrMdU32Ty : «Type» := .Tuple [(⟨0⟩, u32Ty)] ⟨⟨4⟩, ⟨4⟩, none⟩ none
@[reducible] def mrArr3Pointee : PointeeInfo :=
  { layout := .Sized ⟨12⟩ ⟨4⟩, inhabited := true, unsafe_cells := .Sized [], freeze := true,
    unpin := true }
@[reducible] def mrShrRefArr3Ty : «Type» := .Ptr (.Ref .Immutable mrArr3Pointee)

@[reducible] def wdCU64 (n : Int) : ValueExpr := .Constant (.Int n) mrU64Ty
@[reducible] def wdCUsize (n : Int) : ValueExpr := .Constant (.Int n) mrUsizeTy
@[reducible] def wdCU8 (n : Int) : ValueExpr := .Constant (.Int n) mrU8Ty
@[reducible] def wdToU64 (e : ValueExpr) : ValueExpr := .UnOp (.Cast (.IntToInt mrU64IntTy)) e
@[reducible] def wdLd (i : Nat) : ValueExpr := .Load (.Local (locId i))
@[reducible] def wdLc (i : Nat) : PlaceExpr := .Local (locId i)

/-- Observation epilogue: `(kind, a, b)` into locals `(0, 1, 2)`. -/
def wdFinish (kind : Int) (a b : ValueExpr) : List Statement :=
  [.StorageLive (locId 1), .StorageLive (locId 2),
   .Assign (.Local (locId 0)) (cU32 kind),
   .Assign (.Local (locId 1)) a,
   .Assign (.Local (locId 2)) b]

def wdLive (n : Nat) : List Statement := (List.range n).map fun i => .StorageLive (locId (i + 3))

def wdMain (extra : List «Type») (body : List Statement) : Function :=
  mkFn ([(locId 0, u32Ty), (locId 1, mrU64Ty), (locId 2, mrU64Ty)] ++
      (extra.zipIdx.map fun (t, i) => (locId (i + 3), t))) [] (locId 0)
    [(bbId 0, ⟨wdLive extra.length ++ body, exitTerm, .Regular⟩)]

def wdProg (extra : List «Type») (body : List Statement) : Program :=
  mkProg [(fnId 0, wdMain extra body)]

def wdWide (len : Int) : List Statement :=
  [.Assign (wdLc 3) (.Tuple [cU32 11, cU32 22, cU32 33] mrArr3Ty),
   .Assign (wdLc 4) (.AddrOf (wdLc 3) (.Raw .None)),
   .Assign (wdLc 5) (.UnOp (.Cast (.Transmute mrWideRawTy)) (.Tuple [wdLd 4, wdCUsize len] mrPairTy))]

def mrWdSizeAlignProg (pointee : «Type») (len : Int) : Program :=
  wdProg [mrArr3Ty, rawThinTy, mrWideRawTy, mrUsizeTy, mrUsizeTy, mrUsizeTy]
    (wdWide len ++
     [.Assign (wdLc 6) (.UnOp .GetMetadata (wdLd 5)),
      .Assign (wdLc 7) (.UnOp (.ComputeSize pointee) (wdLd 6)),
      .Assign (wdLc 8) (.UnOp (.ComputeAlign pointee) (wdLd 6))] ++
     wdFinish 1 (wdToU64 (wdLd 7)) (wdToU64 (wdLd 8)))

def mrWdProg0 : Program :=
  wdProg [mrArr3Ty, rawThinTy, mrWideRawTy, mrUsizeTy, mrUsizeTy, mrUsizeTy]
    (wdWide 3 ++
     [.Assign (wdLc 6) (.UnOp .GetMetadata (wdLd 5)),
      .Assign (wdLc 7) (.UnOp .GetMetadata (wdLd 5)),
      .Assign (wdLc 8) (.BinOp (.Int .Add) (.BinOp (.Int .Sub) (wdLd 6) (wdLd 7)) (wdCUsize 1))] ++
     wdFinish 0 (wdToU64 (.Load (.Index (.Deref (wdLd 5) mrSliceU32Ty) (wdLd 8)))) (wdCU64 0))

def mrWdProg1 : Program := mrWdSizeAlignProg mrSliceU32Ty 3
def mrWdProg2 : Program := mrWdSizeAlignProg mrSliceUnitTy 5
def mrWdProg2Str : Program := mrWdSizeAlignProg mrStrTy 0
def mrWdProg3 : Program := mrWdSizeAlignProg mrSliceU32Ty 2305843009213693951
def mrWdProg4 : Program :=
  wdProg [mrArr3Ty, rawThinTy, mrWideRawTy, mrUsizeTy, mrUsizeTy, mrUsizeTy, mrSliceU32RefTy]
    (wdWide 2305843009213693952 ++
     [.Assign (wdLc 6) (.UnOp .GetMetadata (wdLd 5)),
      .Assign (wdLc 7) (.UnOp (.ComputeSize mrSliceU32Ty) (wdLd 6)),
      .Assign (wdLc 8) (.UnOp (.ComputeAlign mrSliceU32Ty) (wdLd 6)),
      .Assign (wdLc 9) (.UnOp (.Cast (.Transmute mrSliceU32RefTy)) (wdLd 5))] ++
     wdFinish 1 (wdToU64 (wdLd 7)) (wdToU64 (wdLd 8)))
def mrWdProg5 : Program :=
  wdProg [mrArr3Ty, rawThinTy, mrWideRawTy, mrUsizeTy]
    (wdWide 2 ++
     [.Assign (wdLc 6) (wdCUsize 2)] ++
     wdFinish 0 (wdToU64 (.Load (.Index (.Deref (wdLd 5) mrSliceU32Ty) (wdLd 6)))) (wdCU64 0))
def mrWdProg6 : Program := mrWdSizeAlignProg mrHeaderSliceTy 3
def mrWdProg7 : Program := mrWdSizeAlignProg mrAlign8TailU16Ty 3

def mrWdProg8 : Program := wdProg [mrMuU32Ty, mrMuU32Ty] ([.Assign (wdLc 4) (wdLd 3)] ++ wdFinish 2 (wdCU64 0) (wdCU64 0))
def mrWdProg9 : Program :=
  wdProg [mrMuU32Ty, mrMuU32Ty]
    ([.Assign (.Field (wdLc 3) 2) (wdCU8 42), .Assign (wdLc 4) (wdLd 3)] ++ wdFinish 2 (wdCU64 0) (wdCU64 0))
def mrWdProg10 : Program :=
  wdProg [mrMuU32Ty, mrMuU32Ty]
    ([.Assign (.Field (wdLc 3) 1) (cU32 305419896), .Assign (wdLc 4) (wdLd 3)] ++
     wdFinish 0 (wdToU64 (.Load (.Field (wdLc 4) 1))) (wdCU64 0))
def mrWdProg11 : Program :=
  wdProg [mrMdU32Ty, mrMdU32Ty]
    ([.Assign (wdLc 3) (.Tuple [cU32 77] mrMdU32Ty), .Assign (wdLc 4) (wdLd 3)] ++
     wdFinish 0 (wdToU64 (.Load (.Field (wdLc 4) 0))) (wdCU64 0))
def mrWdProg12 : Program :=
  wdProg [mrMuU32Ty, mrMuU32Ty]
    ([.Assign (wdLc 4) (wdLd 3)] ++ wdFinish 0 (wdToU64 (.Load (.Field (wdLc 4) 1))) (wdCU64 0))
def mrWdProg13 : Program :=
  wdProg [mrMuBoolTy, mrMuBoolTy, .Bool]
    ([.Assign (.Field (wdLc 3) 2) (wdCU8 2), .Assign (wdLc 4) (wdLd 3),
      .Assign (wdLc 5) (.Load (.Field (wdLc 4) 1))] ++ wdFinish 0 (wdCU64 0) (wdCU64 0))
def mrWdProg13Copy : Program :=
  wdProg [mrMuBoolTy, mrMuBoolTy]
    ([.Assign (.Field (wdLc 3) 2) (wdCU8 2), .Assign (wdLc 4) (wdLd 3)] ++ wdFinish 2 (wdCU64 0) (wdCU64 0))

@[reducible] def wdArrInit : Statement :=
  .Assign (wdLc 3) (.Tuple [cU32 100, cU32 200, cU32 300] mrArr3Ty)
@[reducible] def wdDerefU32 (i : Nat) : ValueExpr := .Load (.Deref (wdLd i) u32Ty)

def mrWdProg14 : Program :=
  wdProg [mrArr3Ty, rawThinTy, rawThinTy, rawThinTy, rawThinTy]
    ([wdArrInit, .Assign (wdLc 4) (.AddrOf (wdLc 3) (.Raw .None)),
      .Assign (wdLc 5) (ptrOff true (wdLd 4) 4),
      .Assign (wdLc 6) (ptrOff true (wdLd 5) 4),
      .Assign (wdLc 7) (ptrOff true (wdLd 6) (-4))] ++ wdFinish 0 (wdToU64 (wdDerefU32 7)) (wdCU64 0))
def mrWdProg15 : Program :=
  wdProg [mrArr3Ty, rawThinTy, rawThinTy, rawThinTy]
    ([wdArrInit, .Assign (wdLc 4) (.AddrOf (wdLc 3) (.Raw .None)),
      .Assign (wdLc 5) (ptrOff false (wdLd 4) 100),
      .Assign (wdLc 6) (ptrOff false (wdLd 5) (-96))] ++ wdFinish 0 (wdToU64 (wdDerefU32 6)) (wdCU64 0))
def mrWdProg16 : Program :=
  wdProg [mrArr3Ty, rawThinTy, rawThinTy]
    ([wdArrInit, .Assign (wdLc 4) (.AddrOf (wdLc 3) (.Raw .None)),
      .Assign (wdLc 5) (ptrOff true (wdLd 4) 100)] ++ wdFinish 0 (wdCU64 0) (wdCU64 0))
def mrWdProg17 : Program :=
  wdProg [mrArr3Ty, rawThinTy, rawThinTy]
    ([wdArrInit, .Assign (wdLc 4) (.AddrOf (wdLc 3) (.Raw .None)),
      .Assign (wdLc 5) (ptrOff false (wdLd 4) 100)] ++ wdFinish 0 (wdToU64 (wdDerefU32 5)) (wdCU64 0))
def mrWdProg18 : Program :=
  wdProg [mrArr3Ty, rawThinTy, rawThinTy, rawThinTy]
    ([wdArrInit, .Assign (wdLc 4) (.AddrOf (wdLc 3) (.Raw .None)),
      .Assign (wdLc 5) (ptrOff true (wdLd 4) 0),
      .Assign (wdLc 6) (ptrOff false (wdLd 5) 0)] ++ wdFinish 0 (wdToU64 (wdDerefU32 6)) (wdCU64 0))
def mrWdProg19 : Program :=
  let callee := mkFn [(locId 0, u32Ty), (locId 1, mrShrRefArr3Ty), (locId 2, rawThinTy)]
    [locId 1] (locId 0)
    [(bbId 0, ⟨[
      .Validate (wdLc 1) true,
      .StorageLive (locId 2),
      .Assign (wdLc 2) (ptrOff true (asRawPtr (wdLd 1)) 4),
      .Assign (.Deref (wdLd 2) u32Ty) (cU32 999),
      .Assign (wdLc 0) (wdDerefU32 2)
    ], .Return, .Regular⟩)]
  let main := mkFn [(locId 0, u32Ty), (locId 1, mrU64Ty), (locId 2, mrU64Ty), (locId 3, mrArr3Ty),
      (locId 4, u32Ty)] [] (locId 0)
    [(bbId 0, ⟨[.StorageLive (locId 3), .StorageLive (locId 4), wdArrInit],
       .Call (cFn 1) .Rust [.ByValue (.AddrOf (wdLc 3) (.Ref .Immutable mrArr3Pointee))]
         (wdLc 4) (some (bbId 1)) none, .Regular⟩),
     (bbId 1, ⟨wdFinish 0 (wdToU64 (wdLd 4)) (wdCU64 0), exitTerm, .Regular⟩)]
  mkProg [(fnId 0, main), (fnId 1, callee)]

def mrWdFnTarget : Function :=
  mkFn [(locId 0, u32Ty)] [] (locId 0) [(bbId 0, ⟨[.Assign (wdLc 0) (cU32 7)], .Return, .Regular⟩)]
def mrWdProg20 : Program :=
  mkProg [(fnId 0, wdMain [fnPtrTy, fnPtrTy]
    ([.Assign (wdLc 3) (cFn 1), .Assign (wdLc 4) (.UnOp (.Cast (.Transmute fnPtrTy)) (wdLd 3))] ++
     wdFinish 3 (wdCU64 0) (wdCU64 0))), (fnId 1, mrWdFnTarget)]
def mrWdNullPtrProg (kind : Int) (target : «Type») : Program :=
  wdProg [mrUsizeTy, target]
    ([.Assign (wdLc 3) (wdCUsize 0), .Assign (wdLc 4) (.UnOp (.Cast (.Transmute target)) (wdLd 3))] ++
     wdFinish kind (wdCU64 0) (wdCU64 0))
def mrWdProg21 : Program := mrWdNullPtrProg 4 fnPtrTy
def mrWdProg22 : Program := mrWdNullPtrProg 3 fnPtrTy
def mrWdProg23 : Program := mrWdNullPtrProg 5 rawThinTy

/-! ### Observer -/
def wdReadLocalM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (loc : Nat) :
    Option (Value M) :=
  match evalPlaceM m (.Local (locId loc)) with
  | .ok ((place, ty), m1) =>
    match placeLoadM m1 place ty with
    | .ok (v, _) => some v
    | .error _ => none
  | .error _ => none

def wdReadNatM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (loc : Nat) : Option Nat :=
  match wdReadLocalM m loc with
  | some (.Int i) => if 0 ≤ i then some i.toNat else none
  | _ => none

def wdByteIsInit {P : Type} : AbstractByte P → Bool
  | .Init _ _ => true
  | _ => false

def wdObsOfStop : Stop → MrWdObs
  | .ub _ => .ub
  | .specPanic _ => .specPanic
  | _ => .unsupported

def wdFnIdOfPtrM {M : Type} [Memory M] [MemoryOps M] (m : Machine M)
    (ptr : Pointer (Memory.Provenance M)) : Option Nat :=
  if ptr.thin_pointer.addr = 0 then some 0
  else (m.fn_ptrs.entries.find? fun e => decide (e.2.addr = ptr.thin_pointer.addr)).map
    fun e => e.1.1.1

/-- Observe a pointer `p` re-validated by `chk` (`check_ptr`): its function identifier (or
address `0`) on success, the stop class on failure. -/
def wdCheckedPtrObsM {M : Type} [Memory M] [MemoryOps M] (m : Machine M)
    (p : Pointer (Memory.Provenance M)) (chk : Interp Unit) : MrWdObs :=
  match chk with
  | .ok () => match wdFnIdOfPtrM m p with | some n => .okFnPtr n | none => .unsupported
  | .error s => wdObsOfStop s

def wdDecodeObsM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) : MrWdObs :=
  match wdReadNatM m 0 with
  | some 0 => match wdReadNatM m 1 with | some a => .okScalar a | none => .unsupported
  | some 1 => match wdReadNatM m 1, wdReadNatM m 2 with
    | some a, some b => .okSizeAlign a b
    | _, _ => .unsupported
  | some 2 => match wdReadLocalM m 4 with
    | some (.Union chunks) =>
      .okUninitPreserved chunks.flatten.length (chunks.flatten.filter wdByteIsInit).length
    | _ => .unsupported
  | some 3 => match wdReadLocalM m 4 with
    | some (.Ptr p) => wdCheckedPtrObsM m p (checkPtrM p .FnPtr (some m))
    | _ => .unsupported
  | some 4 => match wdReadLocalM m 4 with
    | some (.Ptr p) => wdCheckedPtrObsM m p (checkPtrFnNonNullM p .FnPtr (some m))
    | _ => .unsupported
  | some 5 => match wdReadLocalM m 4 with
    | some (.Ptr p) => wdCheckedPtrObsM m p (checkPtrFnNonNullM p (.Raw .None) (some m))
    | _ => .unsupported
  | _ => .unsupported

def wdRunM {M : Type} [Memory M] [MemoryOps M] (params : Memory.Params M) (prog : Program)
    (fuel : Nat := 120) : MrWdObs :=
  match bootProgramM (M := M) params prog with
  | .error s => wdObsOfStop s
  | .ok m0 =>
    match runToStopM fuel m0 with
    | .error (.machineStop, mF) => wdDecodeObsM mF
    | .error (s, _) => wdObsOfStop s
    | .ok _ => .unsupported

def wdRun (tb : Bool) (prog : Program) : MrWdObs :=
  if tb then wdRunM (M := TBM) ({ implicit_writes := true } : TreeBorrowsParams) prog
  else wdRunM (M := BM) () prog


/-- Primary MiniRust program of each case (`none` for `idx ≥ 24`). -/
def mrWdProg? : Nat → Option Program
  | 0 => some mrWdProg0
  | 1 => some mrWdProg1
  | 2 => some mrWdProg2
  | 3 => some mrWdProg3
  | 4 => some mrWdProg4
  | 5 => some mrWdProg5
  | 6 => some mrWdProg6
  | 7 => some mrWdProg7
  | 8 => some mrWdProg8
  | 9 => some mrWdProg9
  | 10 => some mrWdProg10
  | 11 => some mrWdProg11
  | 12 => some mrWdProg12
  | 13 => some mrWdProg13
  | 14 => some mrWdProg14
  | 15 => some mrWdProg15
  | 16 => some mrWdProg16
  | 17 => some mrWdProg17
  | 18 => some mrWdProg18
  | 19 => some mrWdProg19
  | 20 => some mrWdProg20
  | 21 => some mrWdProg21
  | 22 => some mrWdProg22
  | 23 => some mrWdProg23
  | _ => none

/-- Secondary program of the two-query case `2` (empty `str`, `len = 0`). -/
def mrWdAuxProg? : Nat → Option Program
  | 2 => some mrWdProg2Str
  | _ => none

/-- **Real MiniRust observer**: `tb = false` runs on `Mach` (`BasicMemory<x86_64>`), `tb = true`
on `MachTB` (`TreeBorrowsMemory<x86_64>`, `implicit_writes = true`); fail-closed `.unsupported`
for `idx ≥ 24`. -/
def mrWdObserve (tb : Bool) (idx : Nat) : MrWdObs :=
  match mrWdProg? idx with
  | none => .unsupported
  | some p =>
    match mrWdAuxProg? idx with
    | none => wdRun tb p
    | some q => wdCombine (wdRun tb p) (wdRun tb q)

/-- Frozen expected MiniRust table for `tb = false` (`Mach`). -/
def mrWdExpectedBasic : List MrWdObs :=
  [.okScalar 22, .okSizeAlign 12 4, .okSizeAlign 0 1, .okSizeAlign 9223372036854775804 4, .ub, .ub,
   .okSizeAlign 16 4, .okSizeAlign 16 8,
   .okUninitPreserved 4 0, .okUninitPreserved 4 1, .okScalar 305419896, .okScalar 77, .ub, .ub,
   .okScalar 200, .okScalar 200, .ub, .ub, .okScalar 100, .okScalar 999,
   .okFnPtr 1, .ub, .okFnPtr 0, .okFnPtr 0]

/-- Frozen expected MiniRust table for `tb = true` (`MachTB`; only case `19` differs). -/
def mrWdExpectedTb : List MrWdObs :=
  [.okScalar 22, .okSizeAlign 12 4, .okSizeAlign 0 1, .okSizeAlign 9223372036854775804 4, .ub, .ub,
   .okSizeAlign 16 4, .okSizeAlign 16 8,
   .okUninitPreserved 4 0, .okUninitPreserved 4 1, .okScalar 305419896, .okScalar 77, .ub, .ub,
   .okScalar 200, .okScalar 200, .ub, .ub, .okScalar 100, .ub,
   .okFnPtr 1, .ub, .okFnPtr 0, .okFnPtr 0]

/-- **Kernel-checked 48-cell MiniRust table** (`24` cases × `Mach` / `MachTB`), every cell
executed by `bootProgramM` / `runToStopM` (`stepM`) and closed purely by kernel reduction. -/
theorem mrWdObserve_table :
    (List.range mrWdCaseCount).map (mrWdObserve false) = mrWdExpectedBasic ∧
    (List.range mrWdCaseCount).map (mrWdObserve true) = mrWdExpectedTb := by
  constructor <;> kernel_rfl

/-- Out-of-range cases are fail-closed `.unsupported` in both modes. -/
theorem mrWdObserve_out_of_range (tb : Bool) (idx : Nat) (h : mrWdCaseCount ≤ idx) :
    mrWdObserve tb idx = .unsupported := by
  unfold mrWdCaseCount at h
  have hNone : mrWdProg? idx = none := by
    unfold mrWdProg?
    split <;> first | rfl | omega
  unfold mrWdObserve
  rw [hNone]

/-- Exact mode-sensitivity predicate: only case `19` flips between `Mach` and `MachTB`. -/
def mrWdCaseModeSensitive : Nat → Bool
  | 19 => true
  | _ => false

/-- **Exact MiniRust Tree Borrows mode-sensitivity `↔`**: `Mach` and `MachTB` disagree on
`idx < 24` if and only if `idx = 19`. -/
theorem mrWdObserve_mode_sensitivity :
    mrWdObserve false 19 = .okScalar 999 ∧
    mrWdObserve true 19 = .ub ∧
    (∀ idx, idx < mrWdCaseCount →
      (mrWdObserve false idx ≠ mrWdObserve true idx ↔ mrWdCaseModeSensitive idx = true)) := by
  have hB := mrWdObserve_table.1
  have hT := mrWdObserve_table.2
  have hAll : ((List.range mrWdCaseCount).all fun idx =>
      decide ((mrWdExpectedBasic[idx]? ≠ mrWdExpectedTb[idx]?) ↔
        mrWdCaseModeSensitive idx = true)) = true := by decide
  have cellB : ∀ idx, idx < mrWdCaseCount →
      some (mrWdObserve false idx) = mrWdExpectedBasic[idx]? := by
    intro idx hi
    have h' := congrArg (fun l => l[idx]?) hB
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  have cellT : ∀ idx, idx < mrWdCaseCount →
      some (mrWdObserve true idx) = mrWdExpectedTb[idx]? := by
    intro idx hi
    have h' := congrArg (fun l => l[idx]?) hT
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  refine ⟨Option.some.inj (cellB 19 (by decide)), Option.some.inj (cellT 19 (by decide)), ?_⟩
  intro idx hi
  have hIff := of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr hi))
  rw [← cellB idx hi, ← cellT idx hi] at hIff
  simpa [Option.some.injEq] using hIff

/-- **`MachTB.wfLive` preservation across all canonical programs**: every booted and executed
`MachTB` run preserves the live-allocation Tree Borrows invariant (at stop and at fuel end). -/
theorem mrWdProg_tb_wfLive (idx : Nat) (prog : Program) (m0 : MachTB)
    (_hProg : mrWdProg? idx = some prog ∨ mrWdAuxProg? idx = some prog)
    (hBoot : bootProgramM (M := TBM) ({ implicit_writes := true } : TreeBorrowsParams) prog = .ok m0)
    (fuel : Nat) :
    match runToStopM fuel m0 with
    | .ok mEnd => MiniRustSpec.Correspondence.MachTB.wfLive mEnd
    | .error (_, mStop) => MiniRustSpec.Correspondence.MachTB.wfLive mStop :=
  runToStopM_tb_wfLive fuel
    (bootProgramM_tb_wfLive ({ implicit_writes := true } : TreeBorrowsParams) prog m0 hBoot)

/-- **Exact UB diagnostics on `Mach` and `MachTB`**: every `.ub` cell faults for its genuine
root cause (safe-slice `isize::MAX` overflow, OOB slice index, invalid load of uninit / invalid
`bool` bytes, OOB pointer arithmetic / dereference, and — on `MachTB` only — the `Frozen`
write of case `19`). -/
theorem mr_wd_exact_ub_diagnostics :
    runStopMsgBasic mrWdProg4 = some "Value::Ptr: total size exeeds isize::MAX" ∧
    runStopMsgTB mrWdProg4 = some "Value::Ptr: total size exeeds isize::MAX" ∧
    runStopMsgBasic mrWdProg5 = some "access to out-of-bounds index" ∧
    runStopMsgTB mrWdProg5 = some "access to out-of-bounds index" ∧
    runStopMsgBasic mrWdProg12 =
      some "load at type but the data in memory violates the language invariant" ∧
    runStopMsgTB mrWdProg12 =
      some "load at type but the data in memory violates the language invariant" ∧
    runStopMsgBasic mrWdProg13 =
      some "load at type but the data in memory violates the language invariant" ∧
    runStopMsgTB mrWdProg13 =
      some "load at type but the data in memory violates the language invariant" ∧
    runStopMsgBasic mrWdProg16 = some "dereferencing pointer outside the bounds of its allocation" ∧
    runStopMsgTB mrWdProg16 = some "dereferencing pointer outside the bounds of its allocation" ∧
    runStopMsgBasic mrWdProg17 = some "dereferencing pointer outside the bounds of its allocation" ∧
    runStopMsgTB mrWdProg17 = some "dereferencing pointer outside the bounds of its allocation" ∧
    runStopMsgBasic mrWdProg19 = none ∧
    runStopMsgTB mrWdProg19 = some "Tree Borrows: local write of Frozen reference" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- **Case `13` companion (`kani#5205` / `#5196`)**: copying the whole `MaybeUninit<bool>` that
holds the invalid byte `2` succeeds in BOTH memory models and preserves that initialized byte;
only the typed `bool` read (case `13`) is UB. -/
theorem mr_case13_union_copy_of_invalid_bool_byte_ok :
    wdRun false mrWdProg13Copy = .okUninitPreserved 1 1 ∧
    wdRun true mrWdProg13Copy = .okUninitPreserved 1 1 ∧
    mrWdObserve false 13 = .ub ∧ mrWdObserve true 13 = .ub := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- `D1` companion: `ptr::metadata` (`UnOp.GetMetadata`) on a null/provenance-free wide raw
pointer `(0, 77)` succeeds in BOTH `Mach` and `MachTB` without dereferencing memory. -/
def mrWdProgNullMeta : Program :=
  wdProg [rawThinTy, mrWideRawTy, mrUsizeTy]
    ([.Assign (wdLc 3) (.Constant (.PointerWithoutProvenance 0) rawThinTy),
      .Assign (wdLc 4) (.UnOp (.Cast (.Transmute mrWideRawTy))
        (.Tuple [wdLd 3, wdCUsize 77] mrPairTy)),
      .Assign (wdLc 5) (.UnOp .GetMetadata (wdLd 4))] ++
     wdFinish 0 (wdToU64 (wdLd 5)) (wdCU64 0))

theorem mr_null_dangling_ptr_metadata_ok :
    wdRun false mrWdProgNullMeta = .okScalar 77 ∧
    wdRun true mrWdProgNullMeta = .okScalar 77 := by
  constructor <;> kernel_rfl

/-- Non-vacuity witness for `mrWdProg_tb_wfLive`: `mrWdProg19` boots cleanly on `MachTB`. -/
theorem mr_wdProg19_boot_tb_ok :
    ∃ m0 : MachTB,
      bootProgramM (M := TBM) ({ implicit_writes := true } : TreeBorrowsParams) mrWdProg19 = .ok m0 := by
  have hne : (bootProgramM (M := TBM) ({ implicit_writes := true } : TreeBorrowsParams) mrWdProg19).toBool = true := by
    kernel_rfl
  cases h : bootProgramM (M := TBM) ({ implicit_writes := true } : TreeBorrowsParams) mrWdProg19 with
  | ok m0 => exact ⟨m0, rfl⟩
  | error e => rw [h] at hne; cases hne

end MiniRustPrograms

/-! ## §4. Universal Laws of the Unmodified MiniRust Interpreter (`D1`–`D4`) -/

/-! The `D1` trailing-slice layouts are `TupleHeadLayout::full_size_and_align`
(`spec/lang/types.md`):
> "pub fn full_size_and_align(self, tail_size: Size, tail_align: Align) -> (Size, Align) {
>     let capped_tail_align = self.capped_tail_align(tail_align);
>     let align = capped_tail_align.max(self.align);
>     let tail_offset = self.tail_offset(tail_align);
>     let end = tail_offset + tail_size;
>     let size = end.align_to(align);
>     (size, align)
> }"
and safe pointers bound the total size by `isize::MAX` in `check_ptr`
(`spec/lang/representation.md`):
> "ensure_else_ub(size.bytes().in_bounds(Signed, M::T::PTR_SIZE), \"Value::Ptr: total size exeeds isize::MAX\")?;" -/

/-! The `D2` union decode is a verbatim chunk copy (`spec/lang/representation.md`):
> "fn decode<M: Memory>(Type::Union { size, chunks, .. }: Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
>         if bytes.len() != size.bytes() { panic!(\"decode of Type::Union with invalid length\"); }" -/

/-! The pinned `d821c6e3` `check_ptr` (`spec/lang/representation.md`) has no function-pointer
arm, so a null `fn()` passes:
> "fn check_ptr(&self, ptr: Pointer<M::Provenance>, ptr_ty: PtrType) -> Result {
>         ensure_else_ub(ptr.thin_pointer.addr.in_bounds(Unsigned, M::T::PTR_SIZE), \"Value::Ptr: pointer out-of-bounds\")?;" -/

section UniversalLaws

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp

/-- `D1` **universal `[T]` layout law**: `compute_size_and_align (.Slice e a) (ElementCount n) = (n * e, a)` for every element size, alignment, and `n ≥ 0`. -/
theorem mr_compute_size_and_align_slice {P : Type} (vt : ThinPointer P → Interp VTable)
    (e : Size) (a : Align) (n : Int) (hn : 0 ≤ n) :
    LayoutStrategy.compute_size_and_align vt (.Slice e a) (some (.ElementCount n)) =
      pure (⟨(n * (e.bytes : Int)).toNat⟩, a) := by
  simp [LayoutStrategy.compute_size_and_align, Int.mul_nonneg hn (Int.natCast_nonneg _)]

/-- `D1` **universal trailing-slice layout law**: a `Tuple head (.Slice e a)` DST is laid out by `head.full_size_and_align (n * e) a`. -/
theorem mr_compute_size_and_align_tuple_slice {P : Type} (vt : ThinPointer P → Interp VTable)
    (head : TupleHeadLayout) (e : Size) (a : Align) (n : Int) (hn : 0 ≤ n) :
    LayoutStrategy.compute_size_and_align vt (.Tuple head (.Slice e a)) (some (.ElementCount n)) =
      pure (TupleHeadLayout.full_size_and_align head ⟨(n * (e.bytes : Int)).toNat⟩ a) := by
  simp [LayoutStrategy.compute_size_and_align, Int.mul_nonneg hn (Int.natCast_nonneg _)]

/-- `D1` `HeaderSlice { tag: u8, data: [u32] }`: `full_size(n) = 4 + 4n`, `align = 4`, for every `n`. -/
theorem mr_header_slice_full_size (n : Nat) :
    TupleHeadLayout.full_size_and_align ⟨⟨1⟩, ⟨1⟩, none⟩ ⟨4 * n⟩ ⟨4⟩ = (⟨4 + 4 * n⟩, ⟨4⟩) := by
  simp [TupleHeadLayout.full_size_and_align, TupleHeadLayout.capped_tail_align,
    TupleHeadLayout.tail_offset, Size.align_to]
  omega

/-- `D1` `Align8TailU16 { hdr: u64, tail: [u16] }`: `full_size(n) = align_to(8 + 2n, 8)`, `align = 8`, for every `n`. -/
theorem mr_align8_tail_u16_full_size (n : Nat) :
    TupleHeadLayout.full_size_and_align ⟨⟨8⟩, ⟨8⟩, none⟩ ⟨2 * n⟩ ⟨2⟩ =
      (⟨(8 + 2 * n + 7) / 8 * 8⟩, ⟨8⟩) := by
  simp [TupleHeadLayout.full_size_and_align, TupleHeadLayout.capped_tail_align,
    TupleHeadLayout.tail_offset, Size.align_to]

/-- `D1` the `check_ptr` `isize::MAX` test: `inBounds i .Signed PTR_SIZE` iff `-2^63 ≤ i ≤ 2^63 - 1`. -/
theorem mr_inBounds_signed_ptr (i : Int) :
    inBounds i .Signed x86_64.PTR_SIZE = true ↔ -9223372036854775808 ≤ i ∧ i ≤ 9223372036854775807 := by
  simp only [inBounds, Size.bits, x86_64.PTR_SIZE, Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := of_decide_eq_true h1
    have h2' := of_decide_eq_true h2
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩

private theorem ensureElseUb_true (msg : String) : ensureElseUb true msg = pure () := rfl
private theorem ensureElseUb_false (msg : String) : ensureElseUb false msg = ub msg := rfl
private theorem interp_bind_ok {α β : Type} (a : α) (f : α → Interp β) :
    (pure a >>= f) = f a := rfl
private theorem interp_bind_err {α β : Type} (e : Stop) (f : α → Interp β) :
    ((Except.error e : Interp α) >>= f) = Except.error e := rfl

/-- `D1` **universal `checkPtrM` `isize::MAX` overflow UB law**: for EVERY safe slice pointer
(`&[T]`, `&mut [T]`, `Box<[T]>`) with in-bounds unsigned address and element count `n ≥ 0` whose
total size exceeds `isize::MAX`, `checkPtrM` rejects with `"Value::Ptr: total size exeeds isize::MAX"`. -/
theorem mr_checkPtrM_slice_isize_overflow_ub {M : Type} [Memory M] [MemoryOps M]
    (tp : ThinPointer (Memory.Provenance M)) (ptrTy : PtrType) (pointee : PointeeInfo)
    (e : Size) (a : Align) (n : Int) (m : Option (Machine M))
    (hAddr : inBounds tp.addr .Unsigned x86_64.PTR_SIZE = true)
    (hMetaKind : PtrType.meta_kind ptrTy = .ElementCount)
    (hSafe : PtrType.safe_pointee ptrTy = some pointee)
    (hLay : pointee.layout = .Slice e a)
    (hN0 : 0 ≤ n) (hNBound : inBounds n .Unsigned x86_64.PTR_SIZE = true)
    (hBig : 9223372036854775807 < n * (e.bytes : Int)) :
    checkPtrM ⟨tp, some (.ElementCount n)⟩ ptrTy m =
      ub "Value::Ptr: total size exeeds isize::MAX" := by
  have hSign : inBounds ((n * (e.bytes : Int)).toNat : Int) .Signed x86_64.PTR_SIZE = false :=
    Bool.eq_false_iff.mpr fun h => by
      have h' := (mr_inBounds_signed_ptr _).mp h
      omega
  have hRep : IntType.can_represent IntType.usize_ty n = true := by
    rw [IntType.can_represent, IntType.usize_ty]
    exact hNBound
  have hMeta : checkPtrMetadataM (Provenance := Memory.Provenance M) (some (.ElementCount n))
      .ElementCount (m.map (vtableFromPtrM ·)) = pure () := by
    simp only [checkPtrMetadataM, hRep, ensureElseUb_true]
  rw [checkPtrM.eq_def, hAddr, ensureElseUb_true, interp_bind_ok, hMetaKind, hMeta,
    interp_bind_ok, hSafe]
  dsimp only
  rw [hLay, mr_compute_size_and_align_slice _ e a n hN0, interp_bind_ok]
  dsimp only
  rw [hSign, ensureElseUb_false]
  exact interp_bind_err _ _

/-- `D1` **universal `checkPtrM` trailing-slice DST `isize::MAX` overflow UB law**: for EVERY
safe pointer to a trailing-slice struct (`Tuple head (.Slice e a)`) whose aligned total size
exceeds `isize::MAX`, `checkPtrM` rejects with `"Value::Ptr: total size exeeds isize::MAX"`. -/
theorem mr_checkPtrM_tuple_slice_isize_overflow_ub {M : Type} [Memory M] [MemoryOps M]
    (tp : ThinPointer (Memory.Provenance M)) (ptrTy : PtrType) (pointee : PointeeInfo)
    (head : TupleHeadLayout) (e : Size) (a : Align) (n : Int) (m : Option (Machine M))
    (hAddr : inBounds tp.addr .Unsigned x86_64.PTR_SIZE = true)
    (hMetaKind : PtrType.meta_kind ptrTy = .ElementCount)
    (hSafe : PtrType.safe_pointee ptrTy = some pointee)
    (hLay : pointee.layout = .Tuple head (.Slice e a))
    (hN0 : 0 ≤ n) (hNBound : inBounds n .Unsigned x86_64.PTR_SIZE = true)
    (hBig : 9223372036854775807 <
      (TupleHeadLayout.full_size_and_align head ⟨(n * (e.bytes : Int)).toNat⟩ a).1.bytes) :
    checkPtrM ⟨tp, some (.ElementCount n)⟩ ptrTy m =
      ub "Value::Ptr: total size exeeds isize::MAX" := by
  have hSign :
      inBounds ((TupleHeadLayout.full_size_and_align head ⟨(n * (e.bytes : Int)).toNat⟩ a).1.bytes : Int)
        .Signed x86_64.PTR_SIZE = false :=
    Bool.eq_false_iff.mpr fun h => by
      have h' := (mr_inBounds_signed_ptr _).mp h
      omega
  have hRep : IntType.can_represent IntType.usize_ty n = true := by
    rw [IntType.can_represent, IntType.usize_ty]
    exact hNBound
  have hMeta : checkPtrMetadataM (Provenance := Memory.Provenance M) (some (.ElementCount n))
      .ElementCount (m.map (vtableFromPtrM ·)) = pure () := by
    simp only [checkPtrMetadataM, hRep, ensureElseUb_true]
  rw [checkPtrM.eq_def, hAddr, ensureElseUb_true, interp_bind_ok, hMetaKind, hMeta,
    interp_bind_ok, hSafe]
  dsimp only
  rw [hLay, mr_compute_size_and_align_tuple_slice _ head e a n hN0, interp_bind_ok]
  rw [hSign, ensureElseUb_false]
  exact interp_bind_err _ _

/-- `D3` **universal multi-step composition law** of wrapping pointer offsets (every provenance type). -/
theorem mr_ptrOffsetWrappingM_compose {P : Type} (ptr : ThinPointer P) (a b : Int) :
    ptrOffsetWrappingM (ptrOffsetWrappingM ptr a) b = ptrOffsetWrappingM ptr (a + b) := by
  cases ptr with
  | mk addr prov =>
    simp [ptrOffsetWrappingM, ThinPointer.wrapping_offsetM, bringInBounds, Size.bits, x86_64.PTR_SIZE]
    rw [Int.add_assoc]

/-- `D3` **universal `ptrOffsetInboundsM` coincidence law**: whenever in-bounds pointer offset
succeeds on `Mach` or `MachTB`, the result equals `ptrOffsetWrappingM ptr offset` (with exact
signed offset and unsigned address bounds). -/
theorem mr_ptrOffsetInboundsM_ok_eq_wrapping {M : Type} [Memory M] [MemoryOps M]
    (m : Machine M) (ptr q : ThinPointer (Memory.Provenance M)) (offset : Int)
    (h : ptrOffsetInboundsM m ptr offset = .ok q) :
    q = { ptr with addr := ptr.addr + offset } ∧
    q = ptrOffsetWrappingM ptr offset ∧
    inBounds offset .Signed x86_64.PTR_SIZE = true ∧
    inBounds (ptr.addr + offset) .Unsigned x86_64.PTR_SIZE = true := by
  unfold ptrOffsetInboundsM at h
  cases hd : ConcurrentMemory.signed_dereferenceable m.mem ptr offset with
  | error e => simp [hd, bind, Except.bind] at h
  | ok u =>
    cases u
    simp only [hd, bind, Except.bind] at h
    cases ho : inBounds offset .Signed x86_64.PTR_SIZE with
    | false => simp [ho, specPanic] at h
    | true =>
      cases ha : inBounds (ptr.addr + offset) .Unsigned x86_64.PTR_SIZE with
      | false => simp [ho, ha, specPanic] at h
      | true =>
        simp only [ho, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
          Except.ok.injEq] at h
        have hWrap : ptrOffsetWrappingM ptr offset = { ptr with addr := ptr.addr + offset } := by
          simp only [inBounds, Size.bits, x86_64.PTR_SIZE, Bool.and_eq_true] at ha
          have h1 := of_decide_eq_true ha.1
          have h2 := of_decide_eq_true ha.2
          cases ptr with
          | mk addr prov =>
            simp only [ptrOffsetWrappingM, ThinPointer.wrapping_offsetM, bringInBounds, Size.bits,
              x86_64.PTR_SIZE]
            congr 1
            exact Int.emod_eq_of_lt h1 h2
        exact ⟨h.symm, h.symm.trans hWrap.symm, rfl, rfl⟩

/-- `D3` **universal `ptrOffsetInboundsM` OOB UB law**: any UB from `signed_dereferenceable`
propagates directly out of `ptrOffsetInboundsM`. -/
theorem mr_ptrOffsetInboundsM_oob_ub {M : Type} [Memory M] [MemoryOps M]
    (m : Machine M) (ptr : ThinPointer (Memory.Provenance M)) (offset : Int) (msg : String)
    (h : ConcurrentMemory.signed_dereferenceable m.mem ptr offset = .error (.ub msg)) :
    ptrOffsetInboundsM m ptr offset = .error (.ub msg) := by
  simp [ptrOffsetInboundsM, h, bind, Except.bind]

/-- `D3` **universal `evalPtrOffsetM` multi-step wrapping composition**: two wrapping `PtrOffset`
operations compose to a single wrapping `PtrOffset` by `a + b`, preserving the left pointer type. -/
theorem mr_evalPtrOffsetM_wrapping_compose {M : Type} [Memory M] [MemoryOps M]
    (m : Machine M) (ptr : ThinPointer (Memory.Provenance M)) (lTy rTy : «Type») (a b : Int) :
    (evalPtrOffsetM m false (.Ptr ⟨ptr, none⟩, lTy) (.Int a, rTy) >>= fun mid =>
      evalPtrOffsetM m false mid (.Int b, rTy)) =
      evalPtrOffsetM m false (.Ptr ⟨ptr, none⟩, lTy) (.Int (a + b), rTy) := by
  simp [evalPtrOffsetM, ThinPointer.widen, mr_ptrOffsetWrappingM_compose]

/-- `D4` **pre-`#300` pin delta**: pinned `d821c6e3` `checkPtr` ACCEPTS the null pointer at `PtrType.FnPtr` (with or without a machine). -/
theorem mr_checkPtr_null_fnptr_ok (m : Option Mach) :
    checkPtr (⟨⟨0, none⟩, none⟩ : Pointer Prov) .FnPtr m = .ok () := by
  rfl

/-- `D4` **pre-`#300` pin delta** for the polymorphic `checkPtrM` (`Mach` and `MachTB`). -/
theorem mr_checkPtrM_null_fnptr_ok {M : Type} [Memory M] [MemoryOps M] (m : Option (Machine M)) :
    checkPtrM (⟨⟨0, none⟩, none⟩ : Pointer (Memory.Provenance M)) .FnPtr m = .ok () := by
  rfl

/-- `D4`: `checkPtrFnNonNull` coincides with pinned `checkPtr` on every `PtrType` other than `FnPtr`. -/
theorem checkPtrFnNonNull_ne_fnptr (ptr : Pointer Prov) (ptrTy : PtrType) (m : Option Mach)
    (h : ptrTy ≠ .FnPtr) : checkPtrFnNonNull ptr ptrTy m = checkPtr ptr ptrTy m := by
  cases ptrTy <;> first | rfl | exact absurd rfl h

/-- `D4`: `checkPtrFnNonNull` coincides with pinned `checkPtr` on non-null function pointers. -/
theorem checkPtrFnNonNull_fnptr_nonnull (ptr : Pointer Prov) (m : Option Mach)
    (h : ptr.thin_pointer.addr ≠ 0) : checkPtrFnNonNull ptr .FnPtr m = checkPtr ptr .FnPtr m := by
  simp [checkPtrFnNonNull, ensureElseUb, h]

/-- `D4`: `checkPtrFnNonNull` rejects every null function pointer with exactly the `#300` UB. -/
theorem checkPtrFnNonNull_fnptr_null (ptr : Pointer Prov) (m : Option Mach)
    (h : ptr.thin_pointer.addr = 0) :
    checkPtrFnNonNull ptr .FnPtr m = ub "Value::Ptr: null function pointer" := by
  simp [checkPtrFnNonNull, ensureElseUb, h, ub]

/-- `D4` (`Mach` and `MachTB`): `checkPtrFnNonNullM` coincides with `checkPtrM` off `FnPtr`. -/
theorem checkPtrFnNonNullM_ne_fnptr {M : Type} [Memory M] [MemoryOps M]
    (ptr : Pointer (Memory.Provenance M)) (ptrTy : PtrType) (m : Option (Machine M))
    (h : ptrTy ≠ .FnPtr) : checkPtrFnNonNullM ptr ptrTy m = checkPtrM ptr ptrTy m := by
  cases ptrTy <;> first | rfl | exact absurd rfl h

/-- `D4` (`Mach` and `MachTB`): `checkPtrFnNonNullM` coincides with `checkPtrM` on non-null function pointers. -/
theorem checkPtrFnNonNullM_fnptr_nonnull {M : Type} [Memory M] [MemoryOps M]
    (ptr : Pointer (Memory.Provenance M)) (m : Option (Machine M))
    (h : ptr.thin_pointer.addr ≠ 0) : checkPtrFnNonNullM ptr .FnPtr m = checkPtrM ptr .FnPtr m := by
  simp [checkPtrFnNonNullM, ensureElseUb, h]

/-- `D4` (`Mach` and `MachTB`): `checkPtrFnNonNullM` rejects every null function pointer. -/
theorem checkPtrFnNonNullM_fnptr_null {M : Type} [Memory M] [MemoryOps M]
    (ptr : Pointer (Memory.Provenance M)) (m : Option (Machine M))
    (h : ptr.thin_pointer.addr = 0) :
    checkPtrFnNonNullM ptr .FnPtr m = ub "Value::Ptr: null function pointer" := by
  simp [checkPtrFnNonNullM, ensureElseUb, h, ub]

/-- `D2` (`kani#5205` / `#5196`): decoding any initialized byte other than `0` / `1` at `bool` yields no value (an invalid load). -/
theorem mr_decodeM_bool_invalid {M : Type} [Memory M] [MemoryOps M] (b : UInt8) (p : Option (ProvenanceFrag (Memory.Provenance M)))
    (hb : b ≠ 0) (hb1 : b ≠ 1) :
    Type.decodeM (M := M) .Bool [.Init b p] = pure none := by
  simp only [Type.decodeM, List.length_singleton, ne_eq, not_true_eq_false, ↓reduceIte]
  split <;> simp_all

/-- `D2`: decoding an uninitialized byte at `bool` yields no value (an invalid load). -/
theorem mr_decodeM_bool_uninit {M : Type} [Memory M] [MemoryOps M] :
    Type.decodeM (M := M) .Bool [.Uninit] = pure none := by
  simp [Type.decodeM]

/-- `D2` **universal uninit-preserving union decode**: a single-chunk union decodes EVERY byte list of its size verbatim (uninitialized bytes, invalid bytes, provenance), on every memory model. -/
theorem mr_decodeM_union_single_chunk {M : Type} [Memory M] [MemoryOps M]
    (fs : List (Offset × «Type»)) (n : Nat) (al : Align)
    (bytes : List (AbstractByte (Memory.Provenance M))) (h : bytes.length = n) :
    Type.decodeM (M := M) (.Union fs [(⟨0⟩, ⟨n⟩)] ⟨n⟩ al) bytes = pure (some (.Union [bytes])) := by
  subst h
  simp [Type.decodeM, subsliceWithLength]

/-- `D2` **universal uninit-preserving union encode**: encoding a single-chunk union restores the
exact byte list (preserving `.Uninit`, invalid `bool` bytes, and provenance). -/
theorem mr_encodeM_union_single_chunk {M : Type} [Memory M] [MemoryOps M]
    (fs : List (Offset × «Type»)) (n : Nat) (al : Align)
    (bytes : List (AbstractByte (Memory.Provenance M))) (h : bytes.length = n) :
    Type.encodeM (M := M) (.Union fs [(⟨0⟩, ⟨n⟩)] ⟨n⟩ al) (.Union [bytes]) = pure bytes := by
  subst h
  simp [Type.encodeM, Type.encodeUnionChunksM, writeSubsliceAtIndex]

/-- `D2` **universal `Type.Union` decode → encode round-trip**: decoding and re-encoding any byte
sequence of length `n` through a single-chunk union is the identity, preserving uninitialized bytes
and invalid-bit payloads without UB. -/
theorem mr_union_single_chunk_decode_encode_roundtrip {M : Type} [Memory M] [MemoryOps M]
    (fs : List (Offset × «Type»)) (n : Nat) (al : Align)
    (bytes : List (AbstractByte (Memory.Provenance M))) (h : bytes.length = n) :
    (do
      match ← Type.decodeM (M := M) (.Union fs [(⟨0⟩, ⟨n⟩)] ⟨n⟩ al) bytes with
      | some v => Type.encodeM (M := M) (.Union fs [(⟨0⟩, ⟨n⟩)] ⟨n⟩ al) v
      | none => ub "unexpected union decode failure") = pure bytes := by
  rw [mr_decodeM_union_single_chunk fs n al bytes h]
  exact mr_encodeM_union_single_chunk fs n al bytes h

/-- `D2` **universal read-time UB law**: decoding bytes with any uninitialized byte at an integer type yields no value (an invalid load), on every memory model. -/
theorem mr_decodeM_int_uninit_none {M : Type} [Memory M] [MemoryOps M] (t : IntType)
    (bytes : List (AbstractByte (Memory.Provenance M))) (hl : bytes.length = t.size.bytes)
    (hu : bytes.mapM AbstractByte.dataM = none) :
    Type.decodeM (M := M) (.Int t) bytes = pure none := by
  cases t
  simp_all [Type.decodeM, Type.decodeIntM]

/-- `D2` non-vacuity witness for `mr_decodeM_int_uninit_none`: 4 uninitialized bytes fail `u32` decode. -/
theorem mr_decodeM_u32_uninit_witness :
    (List.replicate 4 (.Uninit : AbstractByte Prov)).length = (⟨.Unsigned, ⟨4⟩⟩ : IntType).size.bytes ∧
    (List.replicate 4 (.Uninit : AbstractByte Prov)).mapM AbstractByte.dataM = none ∧
    Type.decodeM (M := BM) (.Int ⟨.Unsigned, ⟨4⟩⟩) (List.replicate 4 .Uninit) = pure none :=
  ⟨rfl, rfl, mr_decodeM_int_uninit_none (M := BM) ⟨.Unsigned, ⟨4⟩⟩ _ rfl rfl⟩

/-- `D3` non-vacuity witness for `mr_ptrOffsetInboundsM_oob_ub`: offsetting a provenance-free
pointer by `100` fails `signed_dereferenceable` with UB, propagating directly through
`ptrOffsetInboundsM`. -/
theorem mr_ptrOffsetInboundsM_oob_witness :
    ∃ m0 : Mach,
      MiniRustSpec.CrossFrameRefAndPanicMR.bootProgramM (M := BM) () mrWdProg16 = .ok m0 ∧
      ptrOffsetInboundsM m0 ⟨0, none⟩ 100 =
        .error (.ub "dereferencing pointer without provenance") := by
  have hok : (MiniRustSpec.CrossFrameRefAndPanicMR.bootProgramM (M := BM) () mrWdProg16).toBool = true := by
    kernel_rfl
  cases h : MiniRustSpec.CrossFrameRefAndPanicMR.bootProgramM (M := BM) () mrWdProg16 with
  | ok m0 =>
    refine ⟨m0, rfl, mr_ptrOffsetInboundsM_oob_ub m0 ⟨0, none⟩ 100 _ ?_⟩
    simp [ConcurrentMemory.signed_dereferenceable, MemoryOps.signed_dereferenceable,
      BM.signed_dereferenceable, BM.dereferenceable, BM.check_ptr, ub]
  | error e => rw [h] at hok; cases hok


/-- `D3` **Case `19` faithfulness (universal `BasicMemory` no-op retag)**: on `BasicMemory` (`Mach`),
`MemoryOps.retag_ptr` and `ConcurrentMemory.retag_ptr` are universally the identity regardless of
`fnEntry` (`Validate(_, true)` installs no protector under `Mach`, matching Trusted's `tb = false`
no-protector state and LeanMiri's `treeBorrows = false` mode, whereas `MachTB` delegates to
`TreeBorrowsMemory.retag_ptr` and installs the `FnEntry` protector that rejects case `19`'s write). -/
theorem mr_basic_retag_ptr_noop (m : BM) (fe : Memory.FrameExtra BM)
    (ptr : Pointer (Memory.Provenance BM)) (ptrTy : PtrType)
    (fnEntry fnImplicitWrites : Bool) (vtableLookup : ThinPointer (Memory.Provenance BM) → Interp VTable) :
    MemoryOps.retag_ptr m fe ptr ptrTy fnEntry fnImplicitWrites vtableLookup =
      .ok (ptr, m, fe) := rfl

/-- `D3` **Case `19` faithfulness (`ConcurrentMemory.retag_ptr` on `BM`)**: lifts
`mr_basic_retag_ptr_noop` through `ConcurrentMemory.retag_ptr`, proving that `mrWdProg19`'s
`.Validate (wdLc 1) true` is universally a no-op under `Mach`. -/
theorem mr_concurrent_basic_retag_ptr_noop (cm : ConcurrentMemory BM) (fe : Memory.FrameExtra BM)
    (ptr : Pointer (Memory.Provenance BM)) (ptrTy : PtrType)
    (fnEntry fnImplicitWrites : Bool) (vtableLookup : ThinPointer (Memory.Provenance BM) → Interp VTable) :
    ConcurrentMemory.retag_ptr cm fe ptr ptrTy fnEntry fnImplicitWrites vtableLookup =
      .ok (ptr, cm, fe) := rfl

/-- `D1` concrete non-vacuity witnesses for `mr_checkPtrM_slice_isize_overflow_ub` and
`mr_checkPtrM_tuple_slice_isize_overflow_ub` at the exact `isize::MAX` boundaries of `[u32]`,
`HeaderSlice`, and `Align8TailU16`. -/
theorem mr_checkPtrM_overflow_witnesses :
    let headerPt : PointeeInfo :=
      { layout := .Tuple ⟨⟨1⟩, ⟨1⟩, none⟩ (.Slice ⟨4⟩ ⟨4⟩), inhabited := true,
        unsafe_cells := .Sized [], freeze := true, unpin := true }
    let align8Pt : PointeeInfo :=
      { layout := .Tuple ⟨⟨8⟩, ⟨8⟩, none⟩ (.Slice ⟨2⟩ ⟨2⟩), inhabited := true,
        unsafe_cells := .Sized [], freeze := true, unpin := true }
    checkPtrM (M := BM) ⟨⟨4096, none⟩, some (.ElementCount 2305843009213693952)⟩
      (.Ref .Immutable mrSliceU32Pointee) none =
        ub "Value::Ptr: total size exeeds isize::MAX" ∧
    checkPtrM (M := BM) ⟨⟨4096, none⟩, some (.ElementCount 2305843009213693951)⟩
      (.Ref .Immutable headerPt) none =
        ub "Value::Ptr: total size exeeds isize::MAX" ∧
    checkPtrM (M := BM) ⟨⟨4096, none⟩, some (.ElementCount 4611686018427387897)⟩
      (.Ref .Immutable align8Pt) none =
        ub "Value::Ptr: total size exeeds isize::MAX" := by
  refine ⟨?_, ?_, ?_⟩
  · exact mr_checkPtrM_slice_isize_overflow_ub (M := BM) ⟨4096, none⟩
      (.Ref .Immutable mrSliceU32Pointee) mrSliceU32Pointee ⟨4⟩ ⟨4⟩ 2305843009213693952 none
      (by decide) rfl rfl rfl (by omega) (by decide) (by decide)
  · exact mr_checkPtrM_tuple_slice_isize_overflow_ub (M := BM) ⟨4096, none⟩
      (.Ref .Immutable _) _ ⟨⟨1⟩, ⟨1⟩, none⟩ ⟨4⟩ ⟨4⟩ 2305843009213693951 none
      (by decide) rfl rfl rfl (by omega) (by decide) (by decide)
  · exact mr_checkPtrM_tuple_slice_isize_overflow_ub (M := BM) ⟨4096, none⟩
      (.Ref .Immutable _) _ ⟨⟨8⟩, ⟨8⟩, none⟩ ⟨2⟩ ⟨2⟩ 4611686018427387897 none
      (by decide) rfl rfl rfl (by omega) (by decide) (by decide)

/-- `D2` concrete non-vacuity witnesses for `mr_union_single_chunk_decode_encode_roundtrip`
(partially initialized `[0x2A, uninit, uninit, uninit]`) and `mr_decodeM_bool_invalid` (byte `2`). -/
theorem mr_union_roundtrip_and_bool_invalid_witnesses :
    let partialBytes : List (AbstractByte Prov) := [.Init 42 none, .Uninit, .Uninit, .Uninit]
    (do
      match ← Type.decodeM (M := BM) mrMuU32Ty partialBytes with
      | some v => Type.encodeM (M := BM) mrMuU32Ty v
      | none => ub "unexpected union decode failure") = pure partialBytes ∧
    Type.decodeM (M := BM) .Bool [.Init 2 none] = pure none :=
  ⟨mr_union_single_chunk_decode_encode_roundtrip (M := BM)
      [(⟨0⟩, unitType), (⟨0⟩, CrossFrameRefAndPanicMR.u32Ty), (⟨0⟩, mrU8Ty)]
      4 ⟨4⟩ [.Init 42 none, .Uninit, .Uninit, .Uninit] rfl,
   mr_decodeM_bool_invalid (M := BM) 2 none (by decide) (by decide)⟩

/-- `D3` non-vacuity witness for `mr_ptrOffsetInboundsM_ok_eq_wrapping`: offsetting a valid
in-bounds address `0` by `0` succeeds on `Mach` (`signed_dereferenceable` on size `0` requires only
in-bounds address) and agrees with `ptrOffsetWrappingM`. -/
theorem mr_ptrOffsetInboundsM_ok_witness :
    ∃ m0 : Mach,
      MiniRustSpec.CrossFrameRefAndPanicMR.bootProgramM (M := BM) () mrWdProg14 = .ok m0 ∧
      ptrOffsetInboundsM m0 ⟨0, none⟩ 0 = pure (ptrOffsetWrappingM ⟨0, none⟩ 0) := by
  have hok : (MiniRustSpec.CrossFrameRefAndPanicMR.bootProgramM (M := BM) () mrWdProg14).toBool = true := by
    kernel_rfl
  cases h : MiniRustSpec.CrossFrameRefAndPanicMR.bootProgramM (M := BM) () mrWdProg14 with
  | ok m0 =>
    refine ⟨m0, rfl, ?_⟩
    have hRes : ptrOffsetInboundsM m0 ⟨0, none⟩ 0 = pure ⟨0, none⟩ := by
      simp [ptrOffsetInboundsM, ConcurrentMemory.signed_dereferenceable,
        MemoryOps.signed_dereferenceable, BM.signed_dereferenceable, BM.dereferenceable,
        BM.check_ptr, inBounds, Size.bits, x86_64.PTR_SIZE]
    have hEq := (mr_ptrOffsetInboundsM_ok_eq_wrapping m0 ⟨0, none⟩ ⟨0, none⟩ 0 hRes).2.1
    exact hRes.trans (congrArg pure hEq)
  | error e => rw [h] at hok; cases hok

/-- **`minirust#300` flip canary**: this theorem holds exactly while the pin predates upstream
`374bf855`. Bumping the pin past `#300` makes pinned `checkPtrM` reject the null `fn()` and breaks
this statement (and the case `22` table cell), flagging that `checkPtrFnNonNull` /
`checkPtrFnNonNullM` must then be retired in favor of the upstream check. -/
theorem mr_minirust300_flip_canary :
    checkPtr (⟨⟨0, none⟩, none⟩ : Pointer Prov) .FnPtr none = .ok () ∧
    checkPtrFnNonNull (⟨⟨0, none⟩, none⟩ : Pointer Prov) .FnPtr none =
      ub "Value::Ptr: null function pointer" ∧
    mrWdObserve false 22 = .okFnPtr 0 ∧ mrWdObserve true 22 = .okFnPtr 0 ∧
    mrWdObserve false 21 = .ub ∧ mrWdObserve true 21 = .ub ∧
    mrTrustedWdObserve false 22 = .ub ∧ mrTrustedWdObserve true 22 = .ub :=
  ⟨mr_checkPtr_null_fnptr_ok none, checkPtrFnNonNull_fnptr_null _ none rfl,
   by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

end UniversalLaws

/-! ## §5. Capstone -/

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp in
/-- **Episode 1 MiniRust capstone**: both 48-cell tables (MiniRust on `Mach` / `MachTB` and
Trusted `stepMirFn`), fail-closed ranges, exact mode sensitivity, cross-authority agreement
outside the documented cells (`6`, `7`: Trusted `.unsupported`; `22`: pin delta), and the
universal `D1`–`D4` laws. -/
theorem ep1_minirust_widedst_maybeuninit_capstone :
    ((List.range mrWdCaseCount).map (mrWdObserve false) = mrWdExpectedBasic ∧
      (List.range mrWdCaseCount).map (mrWdObserve true) = mrWdExpectedTb) ∧
    ((List.range mrWdCaseCount).map (mrTrustedWdObserve false) = mrTrustedExpectedBasic ∧
      (List.range mrWdCaseCount).map (mrTrustedWdObserve true) = mrTrustedExpectedTb) ∧
    (∀ tb idx, mrWdCaseCount ≤ idx → mrWdObserve tb idx = .unsupported) ∧
    (∀ tb idx, mrWdCaseCount ≤ idx → mrTrustedWdObserve tb idx = .unsupported) ∧
    (∀ idx, idx < mrWdCaseCount →
      (mrWdObserve false idx ≠ mrWdObserve true idx ↔ mrWdCaseModeSensitive idx = true)) ∧
    ((List.range mrWdCaseCount).all (fun idx =>
        idx == 6 || idx == 7 || idx == 22 ||
          (mrWdObserve false idx == mrTrustedWdObserve false idx &&
           mrWdObserve true idx == mrTrustedWdObserve true idx)) = true) ∧
    (∀ (e : Size) (a : Align) (n : Int), 0 ≤ n →
      LayoutStrategy.compute_size_and_align (fun (_ : ThinPointer Prov) => (unsupported "vt" : Interp VTable))
          (.Slice e a) (some (.ElementCount n)) = pure (⟨(n * (e.bytes : Int)).toNat⟩, a)) ∧
    (∀ n : Nat, TupleHeadLayout.full_size_and_align ⟨⟨1⟩, ⟨1⟩, none⟩ ⟨4 * n⟩ ⟨4⟩ = (⟨4 + 4 * n⟩, ⟨4⟩)) ∧
    (∀ (ptr : ThinPointer Prov) (a b : Int),
      ptrOffsetWrappingM (ptrOffsetWrappingM ptr a) b = ptrOffsetWrappingM ptr (a + b)) ∧
    (∀ (ptr : Pointer Prov) (m : Option Mach), ptr.thin_pointer.addr = 0 →
      checkPtrFnNonNull ptr .FnPtr m = ub "Value::Ptr: null function pointer") ∧
    (∀ (ptr : Pointer Prov) (ty : PtrType) (m : Option Mach), ty ≠ .FnPtr →
      checkPtrFnNonNull ptr ty m = checkPtr ptr ty m) := by
  refine ⟨mrWdObserve_table, mrTrustedWdObserve_table, mrWdObserve_out_of_range,
    mrTrustedWdObserve_out_of_range, mrWdObserve_mode_sensitivity.2.2, ?_,
    fun e a n hn => mr_compute_size_and_align_slice _ e a n hn, mr_header_slice_full_size,
    mr_ptrOffsetWrappingM_compose, fun ptr m h => checkPtrFnNonNull_fnptr_null ptr m h,
    fun ptr ty m h => checkPtrFnNonNull_ne_fnptr ptr ty m h⟩
  decide +kernel

/-- **Episode 1 MiniRust universal-laws & witnesses capstone**: bundles the remaining universal
`D1`–`D4` laws (`Align8TailU16`, `checkPtrM` `isize::MAX` overflow, `Type.Union` decode→encode
round-trip, `bool` invalid byte, `ptrOffsetInboundsM`, Case 19 `BasicMemory` no-op retag,
Trusted `decodeTypedValueFromBytes` / `intrinsicWidePointeeStep`, and the `#300` flip canary)
together with their concrete non-vacuity witnesses. -/
theorem ep1_minirust_universal_laws_capstone :
    type_of% mr_align8_tail_u16_full_size ∧
    type_of% mr_checkPtrM_overflow_witnesses ∧
    type_of% mr_union_roundtrip_and_bool_invalid_witnesses ∧
    type_of% mr_ptrOffsetInboundsM_ok_witness ∧
    type_of% mr_ptrOffsetInboundsM_oob_witness ∧
    type_of% mr_basic_retag_ptr_noop ∧
    type_of% mr_concurrent_basic_retag_ptr_noop ∧
    type_of% trusted_decodeTypedValueFromBytes_null_witness ∧
    type_of% trusted_intrinsicWidePointeeStep_adt_unsupported ∧
    type_of% mrTrusted_case13_union_copy_of_invalid_bool_byte_ok ∧
    type_of% mrTrustedWdObserve_mode_sensitivity ∧
    type_of% mr_minirust300_flip_canary :=
  ⟨mr_align8_tail_u16_full_size, mr_checkPtrM_overflow_witnesses,
   mr_union_roundtrip_and_bool_invalid_witnesses, mr_ptrOffsetInboundsM_ok_witness,
   mr_ptrOffsetInboundsM_oob_witness, mr_basic_retag_ptr_noop,
   mr_concurrent_basic_retag_ptr_noop, trusted_decodeTypedValueFromBytes_null_witness,
   trusted_intrinsicWidePointeeStep_adt_unsupported, mrTrusted_case13_union_copy_of_invalid_bool_byte_ok,
   mrTrustedWdObserve_mode_sensitivity, mr_minirust300_flip_canary⟩

section AxiomAudit
open Lean Elab Command

run_cmd do
  let env ← getEnv
  -- 1. Strict root isolation: ZERO `Miri.*`, `LeanMiriSpec.*`, or `Anneal.*` imports!
  for modName in env.header.moduleNames do
    if (`Miri).isPrefixOf modName || (`LeanMiriSpec).isPrefixOf modName ||
        (`Anneal).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported by MiniRustSpec.WideDstAndMaybeUninitMR"
  let ns := `MiniRustSpec.WideDstAndMaybeUninitMR
  -- 2. Bridge-reality audit: our theorems transitively reach the real interpreters.
  let bridgeReq : List (Lean.Name × Lean.Name) :=
    [ (ns ++ `mrWdObserve_table, `MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM),
      (ns ++ `mrWdObserve_table, `MiniRustSpec.CrossFrameRefAndPanicMR.bootProgramM),
      (ns ++ `mrWdObserve_table, `MiniRustSpec.Interp.checkPtrM),
      (ns ++ `mrWdObserve_table, `MiniRustSpec.Interp.placeLoadM),
      (ns ++ `mrTrustedWdObserve_table, `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (ns ++ `mrTrustedWdObserve_table, `Trusted.Rustc.V2026_06_01.MirSemantics.encodeTypedValueToBytes),
      (ns ++ `mr_compute_size_and_align_slice, `MiniRustSpec.Interp.LayoutStrategy.compute_size_and_align),
      (ns ++ `mr_header_slice_full_size, `MiniRustSpec.Interp.TupleHeadLayout.full_size_and_align),
      (ns ++ `mr_checkPtr_null_fnptr_ok, `MiniRustSpec.Interp.checkPtr),
      (ns ++ `mr_ptrOffsetWrappingM_compose, `MiniRustSpec.Interp.ptrOffsetWrappingM),
      (ns ++ `mr_ptrOffsetInboundsM_ok_eq_wrapping, `MiniRustSpec.Interp.ptrOffsetInboundsM),
      (ns ++ `mr_evalPtrOffsetM_wrapping_compose, `MiniRustSpec.Interp.evalPtrOffsetM),
      (ns ++ `mr_decodeM_union_single_chunk, `MiniRustSpec.Interp.Type.decodeM),
      (ns ++ `trusted_decodePtrBytesNoForge_fnptr_provless, `Trusted.Rustc.V2026_06_01.MirSemantics.decodePtrBytesNoForge),
      (ns ++ `trusted_decodeTypedValueFromBytes_fnPtr_provless, `Trusted.Rustc.V2026_06_01.MirSemantics.decodeTypedValueFromBytes),
      (ns ++ `trusted_intrinsicWidePointeeStep_adt_unsupported, `Trusted.Rustc.V2026_06_01.MirSemantics.intrinsicWidePointeeStep),
      (ns ++ `mr_concurrent_basic_retag_ptr_noop, `MiniRustSpec.Interp.ConcurrentMemory.retag_ptr),
      (ns ++ `mr_encodeM_union_single_chunk, `MiniRustSpec.Interp.Type.encodeM) ]
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
  if theorems < 52 then
    throwError "axiom audit vacuous: only {theorems} theorems seen"

end AxiomAudit

end MiniRustSpec.WideDstAndMaybeUninitMR
