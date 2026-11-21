/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Anneal.TcbCoreMemPtrIntrinsicsPrototype
import MiniRustSpec.Interp

namespace Anneal.TcbCoreMemPtrIntrinsicsProtoTests

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.TcbCoreMemPtrIntrinsicsPrototype

/-!
# Kernel-Checked Test Suite & Dual-Alignment Audit for 8 Core Memory/Pointer Intrinsics

Every theorem in this module is checked purely by the Lean 4 kernel (`rfl`,
`decide`, and structural/tactical proofs — zero `sorry`, zero `native_decide`),
covering positive witnesses, negative/UB edge cases, `LeanMiri` + `MiniRustSpec`
dual-alignment witnesses, non-vacuity witnesses for every quantified prototype
theorem, and a trailing mechanical MetaM axiom audit verifying that every
declaration in `Anneal.TcbCoreMemPtrIntrinsicsPrototype` and the aggregate test
conjunction depend strictly on Lean's standard axioms
`{propext, Classical.choice, Quot.sound}`.
-/

/-! ## Shared Test Fixtures -/

def mkDecl (ty : Ty) : LocalDecl := { mutability := .mut, ty := ty, debugName := .none }
def mkTarget (dp : DefPath) (tys : List RigidTy := .nil) : ResolvedCallTarget :=
  { defPath := dp, typeArgs := tys, fnSig := .none, isIndirect := false }

def unitTy : Ty := { kind := .tuple .nil, layoutIdx := 0 }
def boolTy : Ty := { kind := .bool, layoutIdx := 0 }
def u8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }
def u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
def i32Ty : Ty := { kind := .int .i32, layoutIdx := 0 }
def u64Ty : Ty := { kind := .uint .u64, layoutIdx := 0 }
def usizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
def isizeTy : Ty := { kind := .int .isize, layoutIdx := 0 }
def rawConstU8Ty : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }
def rawConstU32Ty : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }
def rawMutU32Ty : Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }
def arrU32x4Ty : Ty := { kind := .array (.uint .u32) 4, layoutIdx := 0 }
def arrU32x2Ty : Ty := { kind := .array (.uint .u32) 2, layoutIdx := 0 }
def arrU8x4Ty : Ty := { kind := .array (.uint .u8) 4, layoutIdx := 0 }
def arrPtrU32x2Ty : Ty := { kind := .array (.rawPtr .not (.uint .u32)) 2, layoutIdx := 0 }

/-- Layout table with:
- idx 0: `u32` (size 4, align 4)
- idx 1: padded struct `(u8, u32)` (size 8, align 4, field offsets `[0, 4]`, padding bytes `1..3`)
- idx 2: `MaybeUninit<u32>` union (size 4, align 4, `FieldsShape.union 2`)
- idx 3: `u8` (size 1, align 1)
- idx 4: unpadded struct `(u32, u32)` (size 8, align 4, field offsets `[0, 4]`)
- idx 5: `[u8; 16]` with align 8 (`#[repr(align(8))]` buffer wrapper)
-/
def protoLayouts : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [ { size := ⟨4⟩, align := ⟨4⟩, fields := .primitive, variants := .single 0,
          backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
          isUninhabited := false },
        { size := ⟨8⟩, align := ⟨4⟩,
          fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1],
          variants := .single 0,
          backendRepr := .memory,
          fieldLayouts := [3, 0],
          isUninhabited := false },
        { size := ⟨4⟩, align := ⟨4⟩,
          fields := .union 2,
          variants := .single 0,
          backendRepr := .memory,
          isUninhabited := false },
        { size := ⟨1⟩, align := ⟨1⟩, fields := .primitive, variants := .single 0,
          backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
          isUninhabited := false },
        { size := ⟨8⟩, align := ⟨4⟩,
          fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1],
          variants := .single 0,
          backendRepr := .memory,
          fieldLayouts := [0, 0],
          isUninhabited := false },
        { size := ⟨16⟩, align := ⟨8⟩,
          fields := .arbitrary [⟨0⟩] [0],
          variants := .single 0,
          backendRepr := .memory,
          isUninhabited := false } ] }

def paddedPairTy : Ty := { kind := .tuple [.uint .u8, .uint .u32], layoutIdx := 1 }
def unpaddedPairTy : Ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 4 }
def maybeUninitU32Ty : Ty := { kind := .adt "core::mem::maybe_uninit::MaybeUninit" [.uint .u32], layoutIdx := 2 }
def aligned16BufTy : Ty := { kind := .adt "tests::Aligned16" .nil, layoutIdx := 5 }

def mkState (locals : List LocalSlot) (borrows : List BorrowEntry := .nil)
    (activeProtectors : List Nat := .nil) (globals : List CapturedAllocation := .nil) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
    memory := { emptyMemory with borrows := borrows, activeProtectors := activeProtectors, globals := globals } }

def dstLocal0 : Place := { local_ := 0, projection := .nil }

def stepLocals? : MirStepNode → Option (List LocalSlot)
  | .tau (.running s') => .some s'.frame.locals
  | _ => .none

def stepState? : MirStepNode → Option MachineState
  | .tau (.running s') => .some s'
  | _ => .none

def isUbNode : MirStepNode → Bool
  | .vis (.inl (.fail .ub)) _ => true
  | _ => false

def isUnsupportedNode : MirStepNode → Bool
  | .vis (.inl (.fail .unsupported)) _ => true
  | _ => false

def mkU32 (n : Nat) : Value := .scalar ⟨n, 4⟩
def mkU8 (n : Nat) : Value := .scalar ⟨n, 1⟩
def mkUsize (n : Nat) : Value := .scalar ⟨n, 8⟩

/-! ## Section 1: Classification & Non-Wrapper Discipline -/

theorem classify_all_8_core_intrinsics :
    classifyRustIntrinsicProto? "core::intrinsics::copy" = .some .copy ∧
    classifyRustIntrinsicProto? "core::intrinsics::compare_bytes" = .some .compareBytes ∧
    classifyRustIntrinsicProto? "core::intrinsics::raw_eq" = .some .rawEq ∧
    classifyRustIntrinsicProto? "core::intrinsics::typed_swap_nonoverlapping" = .some .typedSwapNonOverlapping ∧
    classifyRustIntrinsicProto? "core::intrinsics::ptr_offset_from" = .some .ptrOffsetFrom ∧
    classifyRustIntrinsicProto? "core::intrinsics::ptr_offset_from_unsigned" = .some .ptrOffsetFromUnsigned ∧
    classifyRustIntrinsicProto? "core::intrinsics::ptr_mask" = .some .ptrMask ∧
    classifyRustIntrinsicProto? "core::intrinsics::black_box" = .some .blackBox := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem classify_preserves_existing_and_rejects_wrappers :
    classifyRustIntrinsicProto? "core::intrinsics::copy_nonoverlapping" = .some (.base .copyNonOverlapping) ∧
    classifyRustIntrinsicProto? "core::intrinsics::write_bytes" = .some (.base .writeBytes) ∧
    classifyRustIntrinsicProto? "core::ptr::copy" = .none ∧
    classifyRustIntrinsicProto? "core::mem::swap" = .none ∧
    classifyRustIntrinsicProto? "core::hint::black_box" = .none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 2: `core::intrinsics::copy` (Overlapping `memmove`) -/

/-- 2(a1): Non-overlapping copy of `[u32; 2]` between distinct stack locals. -/
theorem copy_nonoverlapping_u32_array :
    let decls := [mkDecl unitTy, mkDecl arrU32x2Ty, mkDecl arrU32x2Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 100, mkU32 200]),
                   .init (.aggregate 0 [mkU32 0, mkU32 0])]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .unique }
    let s := mkState locals [b1, b2]
    let res := evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u32]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8, mkUsize 2]
      locals dstLocal0 (.some 1)
    stepLocals? res = .some
      [.init .unit, .init (.aggregate 0 [mkU32 100, mkU32 200]),
       .init (.aggregate 0 [mkU32 100, mkU32 200])] := rfl

/-- 2(a2): Non-overlapping copy of `[*const u32; 2]` preserves pointer `allocId` and Tree Borrows `tag`. -/
theorem copy_preserves_ptr_provenance_and_tag :
    let decls := [mkDecl unitTy, mkDecl arrPtrU32x2Ty, mkDecl arrPtrU32x2Ty]
    let pA : ProvenancePtr := { allocId := 77, offsetBytes := 12 }
    let pB : ProvenancePtr := { allocId := 88, offsetBytes := 4 }
    let locals := [.uninit,
                   .init (.aggregate 0 [.ptr pA 8, .ptr pB 8]),
                   .uninit]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .unique }
    let s := mkState locals [b1, b2]
    let res := evalCopyProto s (mkTarget "core::intrinsics::copy" [.rawPtr .not (.uint .u32)]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8, mkUsize 2]
      locals dstLocal0 (.some 1)
    stepLocals? res = .some
      [.init .unit,
       .init (.aggregate 0 [.ptr pA 8, .ptr pB 8]),
       .init (.aggregate 0 [.ptr pA 8, .ptr pB 8])] := rfl

/-- 2(a3): Non-overlapping copy from `MaybeUninit<u32>` with `.uninit` bytes to `MaybeUninit<u32>`
preserves uninitialized union state without UB. -/
theorem copy_preserves_uninit_maybe_uninit :
    let decls := [mkDecl unitTy, mkDecl maybeUninitU32Ty, mkDecl maybeUninitU32Ty]
    let locals := [.uninit, .init (.aggregate 0 [.unit]), .init (.aggregate 0 [.unit, mkU32 99])]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .unique }
    let s := mkState locals [b1, b2]
    let res := evalCopyProto s (mkTarget "core::intrinsics::copy" [maybeUninitU32Ty.kind]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8, mkUsize 1]
      locals dstLocal0 (.some 1)
    stepLocals? res = .some
      [.init .unit, .init (.aggregate 0 [.unit]), .init (.aggregate 0 [.unit])] := rfl

/-- 2(b1): Overlapping FORWARD shift (`dst > src`) on `[10, 20, 30, 40]` copying 3 elements
from index 0 to index 1 produces `[10, 10, 20, 30]` (not clobbered `[10, 10, 10, 10]`). -/
theorem copy_overlapping_forward_shift :
    let decls := [mkDecl unitTy, mkDecl arrU32x4Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 10, mkU32 20, mkU32 30, mkU32 40])]
    let b : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [b]
    let res := evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u32]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 1, offsetBytes := 4 } 8, mkUsize 3]
      locals dstLocal0 (.some 1)
    stepLocals? res = .some
      [.init .unit, .init (.aggregate 0 [mkU32 10, mkU32 10, mkU32 20, mkU32 30])] := rfl

/-- 2(b2): Overlapping BACKWARD shift (`dst < src`) on `[10, 20, 30, 40]` copying 3 elements
from index 1 to index 0 produces `[20, 30, 40, 40]`. -/
theorem copy_overlapping_backward_shift :
    let decls := [mkDecl unitTy, mkDecl arrU32x4Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 10, mkU32 20, mkU32 30, mkU32 40])]
    let b : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [b]
    let res := evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u32]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 4 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8, mkUsize 3]
      locals dstLocal0 (.some 1)
    stepLocals? res = .some
      [.init .unit, .init (.aggregate 0 [mkU32 20, mkU32 30, mkU32 40, mkU32 40])] := rfl

/-- 2(b3): Identical self-copy (`src == dst`) succeeds as identity with shared mutable tag. -/
theorem copy_self_identical_succeeds :
    let decls := [mkDecl unitTy, mkDecl arrU32x2Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 7, mkU32 8])]
    let b : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [b]
    let res := evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u32]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8, mkUsize 2]
      locals dstLocal0 (.some 1)
    stepLocals? res = .some [.init .unit, .init (.aggregate 0 [mkU32 7, mkU32 8])] := rfl

/-- 2(c): `count == 0`: aligned non-null dangling integer pointer succeeds as a no-op,
while misaligned (`offset 2` for `u32`) or null (`0`) faults `.ub` even at zero bytes! -/
theorem copy_zero_count_aligned_vs_misaligned_and_null :
    let decls := [mkDecl unitTy, mkDecl arrU32x2Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 1, mkU32 2])]
    let b : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [b]
    let okDangling := evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u32]) decls protoLayouts []
      [mkUsize 4096, mkUsize 4100, mkUsize 0] locals dstLocal0 (.some 1)
    let ubMisaligned := evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u32]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 2 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8, mkUsize 0]
      locals dstLocal0 (.some 1)
    let ubNull := evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u32]) decls protoLayouts []
      [mkUsize 0, mkUsize 4096, mkUsize 0] locals dstLocal0 (.some 1)
    stepLocals? okDangling = .some [.init .unit, .init (.aggregate 0 [mkU32 1, mkU32 2])] ∧
    isUbNode ubMisaligned = true ∧
    isUbNode ubNull = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- 2(d): `elemSize * count > isize::MAX` overflow (`4 * 2^61 = 2^63 > isize::MAX`) faults `.ub`. -/
theorem copy_total_bytes_overflow_ub :
    let decls := [mkDecl unitTy, mkDecl arrU32x2Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 1, mkU32 2])]
    let b : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [b]
    let hugeCount : Nat := 2305843009213693952 -- 2^61; 4 * 2^61 = 2^63 > isize::MAX
    let res := evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u32]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8, mkUsize hugeCount]
      locals dstLocal0 (.some 1)
    isUbNode res = true := rfl

/-- 2(e): Tree Borrows UB: (1) writing to a `.frozen` tag faults `.ub`;
(2) exact read-then-write order: reading through sibling `.unique` tag 1 freezes
sibling `.unique` tag 2, causing Phase B write through tag 2 to fault `.ub`! -/
theorem copy_tree_borrows_frozen_and_read_then_write_ub :
    let decls := [mkDecl unitTy, mkDecl arrU32x2Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 1, mkU32 2])]
    let bSrc : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let bFrozen : BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := .frozen }
    let bSibUnique : BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := .unique }
    let sFrozen := mkState locals [bSrc, bFrozen]
    let sSibling := mkState locals [bSrc, bSibUnique]
    let resFrozen := evalCopyProto sFrozen (mkTarget "core::intrinsics::copy" [.uint .u32]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 4 } 8, mkUsize 1]
      locals dstLocal0 (.some 1)
    let resSibling := evalCopyProto sSibling (mkTarget "core::intrinsics::copy" [.uint .u32]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 4 } 8, mkUsize 1]
      locals dstLocal0 (.some 1)
    isUbNode resFrozen = true ∧ isUbNode resSibling = true := by
  refine ⟨rfl, rfl⟩

/-- 2(f): Statement-level `evalCopyStmtProto` executes overlapping forward shift identically. -/
theorem copy_stmt_wrapper_overlapping_forward :
    let decls := [mkDecl unitTy, mkDecl arrU32x4Ty, mkDecl rawConstU32Ty, mkDecl rawMutU32Ty]
    let locals := [.uninit,
                   .init (.aggregate 0 [mkU32 10, mkU32 20, mkU32 30, mkU32 40]),
                   .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
                   .init (.ptr { allocId := 1, offsetBytes := 4 } 8)]
    let b : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [b]
    let countOp : Operand := .constant { ty := usizeTy, val := .scalar (.int ⟨3, 8⟩) }
    let res := evalCopyStmtProto s (.copy { local_ := 2, projection := [] })
      (.copy { local_ := 3, projection := [] }) countOp decls protoLayouts [.uint .u32]
    stepLocals? res = .some
      [.uninit,
       .init (.aggregate 0 [mkU32 10, mkU32 10, mkU32 20, mkU32 30]),
       .init (.ptr { allocId := 1, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 1, offsetBytes := 4 } 8)] := rfl

/-! ## Section 3: `core::intrinsics::compare_bytes` (`memcmp`) -/

/-- 3(a): Equal -> `0`, `<` -> `-1` (`4294967295 : i32`), `>` -> `1`. -/
theorem compare_bytes_eq_lt_gt :
    let decls := [mkDecl i32Ty, mkDecl arrU8x4Ty, mkDecl arrU8x4Ty]
    let locals := [.uninit,
                   .init (.aggregate 0 [mkU8 1, mkU8 2, mkU8 3, mkU8 4]),
                   .init (.aggregate 0 [mkU8 1, mkU8 2, mkU8 5, mkU8 4])]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .frozen }
    let s := mkState locals [b1, b2]
    let rEq := evalCompareBytesProto s decls protoLayouts
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8, mkUsize 2]
      locals dstLocal0 (.some 1)
    let rLt := evalCompareBytesProto s decls protoLayouts
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8, mkUsize 4]
      locals dstLocal0 (.some 1)
    let rGt := evalCompareBytesProto s decls protoLayouts
      [.ptr { allocId := 2, offsetBytes := 0 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8, mkUsize 4]
      locals dstLocal0 (.some 1)
    (stepLocals? rEq).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨0, 4⟩)) ∧
    (stepLocals? rLt).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨4294967295, 4⟩)) ∧
    (stepLocals? rGt).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨1, 4⟩)) := by
  refine ⟨rfl, rfl, rfl⟩

/-- 3(b): High-bit UNSIGNED byte comparison: `0x80 > 0x7f` (returns `+1`, NOT signed `i8` `-1`). -/
theorem compare_bytes_unsigned_high_bit :
    let decls := [mkDecl i32Ty, mkDecl u8Ty, mkDecl u8Ty]
    let locals := [.uninit, .init (mkU8 128), .init (mkU8 127)]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .frozen }
    let s := mkState locals [b1, b2]
    let rGt := evalCompareBytesProto s decls protoLayouts
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8, mkUsize 1]
      locals dstLocal0 (.some 1)
    let rLt := evalCompareBytesProto s decls protoLayouts
      [.ptr { allocId := 2, offsetBytes := 0 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8, mkUsize 1]
      locals dstLocal0 (.some 1)
    (stepLocals? rGt).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨1, 4⟩)) ∧
    (stepLocals? rLt).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨4294967295, 4⟩)) := by
  refine ⟨rfl, rfl⟩

/-- 3(c): `.uninit` byte at index 0 AND `.uninit` byte at index `k > 0` AFTER an earlier byte
mismatch (`0x01 != 0x02`) BOTH fault `.ub` (eager full-slice read matching Miri). -/
theorem compare_bytes_uninit_idx0_and_eager_tail_ub :
    let decls := [mkDecl i32Ty, mkDecl arrU8x4Ty, mkDecl arrU8x4Ty]
    let localsIdx0 := [.uninit,
                       .init (.aggregate 0 [.uninit, mkU8 2, mkU8 3, mkU8 4]),
                       .init (.aggregate 0 [mkU8 1, mkU8 2, mkU8 3, mkU8 4])]
    let localsTail := [.uninit,
                       .init (.aggregate 0 [mkU8 1, mkU8 2, .uninit, mkU8 4]),
                       .init (.aggregate 0 [mkU8 9, mkU8 2, mkU8 3, mkU8 4])]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .frozen }
    let rIdx0 := evalCompareBytesProto (mkState localsIdx0 [b1, b2]) decls protoLayouts
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8, mkUsize 4]
      localsIdx0 dstLocal0 (.some 1)
    let rTailLeft := evalCompareBytesProto (mkState localsTail [b1, b2]) decls protoLayouts
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8, mkUsize 4]
      localsTail dstLocal0 (.some 1)
    let rTailRight := evalCompareBytesProto (mkState localsTail [b1, b2]) decls protoLayouts
      [.ptr { allocId := 2, offsetBytes := 0 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8, mkUsize 4]
      localsTail dstLocal0 (.some 1)
    isUbNode rIdx0 = true ∧ isUbNode rTailLeft = true ∧ isUbNode rTailRight = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- 3(d) & 3(e): `bytes == 0` with non-null pointers returns `0`, with null faults `.ub`,
and provenance-carrying pointer bytes fail closed with `.unsupported`. -/
theorem compare_bytes_zero_and_provenance_unsupported :
    let decls := [mkDecl i32Ty, mkDecl rawConstU32Ty, mkDecl rawConstU32Ty]
    let locals := [.uninit,
                   .init (.ptr { allocId := 5, offsetBytes := 0 } 8),
                   .init (.ptr { allocId := 6, offsetBytes := 0 } 8)]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .frozen }
    let s := mkState locals [b1, b2]
    let rZero := evalCompareBytesProto s decls protoLayouts
      [mkUsize 16, mkUsize 32, mkUsize 0] locals dstLocal0 (.some 1)
    let rZeroNull := evalCompareBytesProto s decls protoLayouts
      [mkUsize 0, mkUsize 32, mkUsize 0] locals dstLocal0 (.some 1)
    let rProv := evalCompareBytesProto s decls protoLayouts
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8, mkUsize 8]
      locals dstLocal0 (.some 1)
    (stepLocals? rZero).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨0, 4⟩)) ∧
    isUbNode rZeroNull = true ∧
    isUnsupportedNode rProv = true := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## Section 4: `core::intrinsics::raw_eq` -/

/-- 4(a): Equal and unequal initialized unpadded structs `(u32, u32)` return `true` / `false`. -/
theorem raw_eq_initialized_struct_true_and_false :
    let decls := [mkDecl boolTy, mkDecl unpaddedPairTy, mkDecl unpaddedPairTy, mkDecl unpaddedPairTy]
    let locals := [.uninit,
                   .init (.aggregate 0 [mkU32 11, mkU32 22]),
                   .init (.aggregate 0 [mkU32 11, mkU32 22]),
                   .init (.aggregate 0 [mkU32 11, mkU32 99])]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .frozen }
    let b3 : BorrowEntry := { tag := 3, targetLocal := 3, targetProjection := [], perm := .frozen }
    let s := mkState locals [b1, b2, b3]
    let rTrue := evalRawEqProto s (mkTarget "core::intrinsics::raw_eq" [unpaddedPairTy.kind]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8]
      locals dstLocal0 (.some 1)
    let rFalse := evalRawEqProto s (mkTarget "core::intrinsics::raw_eq" [unpaddedPairTy.kind]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 3, offsetBytes := 0 } 8]
      locals dstLocal0 (.some 1)
    (stepLocals? rTrue).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨1, 1⟩)) ∧
    (stepLocals? rFalse).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨0, 1⟩)) := by
  refine ⟨rfl, rfl⟩

/-- 4(b): Struct `(u8, u32)` with `.uninit` padding bytes (`1..3`) faults `.ub` even when all
fields match identically! -/
theorem raw_eq_padded_struct_uninit_padding_ub :
    let decls := [mkDecl boolTy, mkDecl paddedPairTy, mkDecl paddedPairTy]
    let locals := [.uninit,
                   .init (.aggregate 0 [mkU8 7, mkU32 42]),
                   .init (.aggregate 0 [mkU8 7, mkU32 42])]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .frozen }
    let s := mkState locals [b1, b2]
    let res := evalRawEqProto s (mkTarget "core::intrinsics::raw_eq" [paddedPairTy.kind]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8]
      locals dstLocal0 (.some 1)
    isUbNode res = true := rfl

/-- 4(c), 4(d), 4(e): Misaligned pointer -> `.ub`; ZST `()` -> `true` (null ZST -> `.ub`);
unsized `[u8]` -> fail-closed `.unsupported`. -/
theorem raw_eq_misaligned_zst_and_unsized :
    let decls := [mkDecl boolTy, mkDecl arrU32x2Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 1, mkU32 2])]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let s := mkState locals [b1]
    let rMisaligned := evalRawEqProto s (mkTarget "core::intrinsics::raw_eq" [.uint .u32]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 2 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8]
      locals dstLocal0 (.some 1)
    let rZst := evalRawEqProto s (mkTarget "core::intrinsics::raw_eq" [.tuple .nil]) decls protoLayouts []
      [mkUsize 1, mkUsize 2] locals dstLocal0 (.some 1)
    let rZstNull := evalRawEqProto s (mkTarget "core::intrinsics::raw_eq" [.tuple .nil]) decls protoLayouts []
      [mkUsize 0, mkUsize 1] locals dstLocal0 (.some 1)
    let rUnsized := evalRawEqProto s (mkTarget "core::intrinsics::raw_eq" [.slice (.uint .u8)]) decls protoLayouts []
      [mkUsize 8, mkUsize 8] locals dstLocal0 (.some 1)
    isUbNode rMisaligned = true ∧
    (stepLocals? rZst).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨1, 1⟩)) ∧
    isUbNode rZstNull = true ∧
    isUnsupportedNode rUnsized = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 5: `core::intrinsics::typed_swap_nonoverlapping` -/

/-- 5(a): Disjoint stack locals swap pointer values preserving `allocId` and `tag`. -/
theorem typed_swap_disjoint_ptrs_preserves_provenance :
    let decls := [mkDecl unitTy, mkDecl rawConstU32Ty, mkDecl rawConstU32Ty]
    let pA : ProvenancePtr := { allocId := 11, offsetBytes := 8 }
    let pB : ProvenancePtr := { allocId := 22, offsetBytes := 16 }
    let locals := [.uninit, .init (.ptr pA 8), .init (.ptr pB 8)]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .unique }
    let s := mkState locals [b1, b2]
    let res := evalTypedSwapNonOverlappingProto s
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [.rawPtr .not (.uint .u32)])
      decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8]
      locals dstLocal0 (.some 1)
    stepLocals? res = .some [.init .unit, .init (.ptr pB 8), .init (.ptr pA 8)] := rfl

/-- 5(b): **Same-allocation, SAME-TAG disjoint array elements** (`a[0]` and `a[1]` under one
provenance tag `1`) succeed via container-first byte-interval disjointness! -/
theorem typed_swap_same_alloc_same_tag_disjoint_elements :
    let decls := [mkDecl unitTy, mkDecl arrU32x2Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 11, mkU32 22])]
    let b : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [b]
    let res := evalTypedSwapNonOverlappingProto s
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [.uint .u32])
      decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 1, offsetBytes := 4 } 8]
      locals dstLocal0 (.some 1)
    stepLocals? res = .some [.init .unit, .init (.aggregate 0 [mkU32 22, mkU32 11])] := rfl

/-- 5(c): Overlapping / identical non-ZST pointers fault `.ub`, while inhabited ZST `()` succeeds
even when `x == y` (and uninhabited `!` faults `.ub`). -/
theorem typed_swap_overlap_ub_and_zst_semantics :
    let decls := [mkDecl unitTy, mkDecl arrU32x2Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 11, mkU32 22])]
    let b : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [b]
    let rOverlap := evalTypedSwapNonOverlappingProto s
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [.uint .u32])
      decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8]
      locals dstLocal0 (.some 1)
    let rZst := evalTypedSwapNonOverlappingProto s
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [.tuple .nil])
      decls protoLayouts []
      [mkUsize 8, mkUsize 8] locals dstLocal0 (.some 1)
    let rNever := evalTypedSwapNonOverlappingProto s
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [.never])
      decls protoLayouts []
      [mkUsize 8, mkUsize 16] locals dstLocal0 (.some 1)
    isUbNode rOverlap = true ∧
    stepLocals? rZst = .some [.init .unit, .init (.aggregate 0 [mkU32 11, mkU32 22])] ∧
    isUbNode rNever = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- 5(d): Typed validity enforcement (`kani#5205`):
- `.uninit` scalar `u32` faults `.ub`;
- invalid `bool` bit pattern `2` faults `.ub`;
- `MaybeUninit<u32>` with `.uninit` bytes SUCCEEDS;
- padded struct `(u8, u32)` with `.uninit` padding SUCCEEDS! -/
theorem typed_swap_validity_uninit_bool_maybeuninit_and_padded :
    let declsU32 := [mkDecl unitTy, mkDecl u32Ty, mkDecl u32Ty]
    let locUninit := [.uninit, .uninit, .init (mkU32 5)]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .unique }
    let rUninitU32 := evalTypedSwapNonOverlappingProto (mkState locUninit [b1, b2])
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [.uint .u32]) declsU32 protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8]
      locUninit dstLocal0 (.some 1)
    let declsBool := [mkDecl unitTy, mkDecl boolTy, mkDecl boolTy]
    let locBadBool := [.uninit, .init (.scalar ⟨2, 1⟩), .init (.scalar ⟨1, 1⟩)]
    let rBadBool := evalTypedSwapNonOverlappingProto (mkState locBadBool [b1, b2])
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [.bool]) declsBool protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8]
      locBadBool dstLocal0 (.some 1)
    let declsMu := [mkDecl unitTy, mkDecl maybeUninitU32Ty, mkDecl maybeUninitU32Ty]
    let locMu := [.uninit, .init (.aggregate 0 [.unit]), .init (.aggregate 0 [.unit, mkU32 42])]
    let rMu := evalTypedSwapNonOverlappingProto (mkState locMu [b1, b2])
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [maybeUninitU32Ty.kind]) declsMu protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8]
      locMu dstLocal0 (.some 1)
    let declsPad := [mkDecl unitTy, mkDecl paddedPairTy, mkDecl paddedPairTy]
    let locPad := [.uninit, .init (.aggregate 0 [mkU8 1, mkU32 10]), .init (.aggregate 0 [mkU8 2, mkU32 20])]
    let rPad := evalTypedSwapNonOverlappingProto (mkState locPad [b1, b2])
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [paddedPairTy.kind]) declsPad protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8]
      locPad dstLocal0 (.some 1)
    isUbNode rUninitU32 = true ∧
    isUbNode rBadBool = true ∧
    (stepLocals? rMu).isSome = true ∧
    stepLocals? rPad = .some
      [.init .unit, .init (.aggregate 0 [mkU8 2, mkU32 20]), .init (.aggregate 0 [mkU8 1, mkU32 10])] := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- 5(e): Tree Borrows conflict (`.frozen` endpoint) faults `.ub`, and unsized `T` fails closed. -/
theorem typed_swap_tree_borrows_and_unsized :
    let decls := [mkDecl unitTy, mkDecl u32Ty, mkDecl u32Ty]
    let locals := [.uninit, .init (mkU32 1), .init (mkU32 2)]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .frozen }
    let rFrozen := evalTypedSwapNonOverlappingProto (mkState locals [b1, b2])
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [.uint .u32]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8]
      locals dstLocal0 (.some 1)
    let rUnsized := evalTypedSwapNonOverlappingProto (mkState locals [b1, b2])
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [.slice (.uint .u32)]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8]
      locals dstLocal0 (.some 1)
    isUbNode rFrozen = true ∧ isUnsupportedNode rUnsized = true := by
  refine ⟨rfl, rfl⟩

/-! ## Section 6: `ptr_offset_from` & `ptr_offset_from_unsigned` -/

/-- 6(a) & 6(b): Positive, negative (`isize` two's complement), zero, one-past-the-end, AND
unaligned endpoints whose byte difference IS divisible by `size_of::<T>()` all succeed! -/
theorem ptr_offset_from_pos_neg_zero_end_and_unaligned_divisible :
    let decls := [mkDecl isizeTy, mkDecl arrU32x4Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 1, mkU32 2, mkU32 3, mkU32 4])]
    let b : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let s := mkState locals [b]
    let rPos := evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from" [.uint .u32])
      decls protoLayouts [] [.ptr { allocId := 1, offsetBytes := 12 } 8, .ptr { allocId := 1, offsetBytes := 4 } 8]
      locals dstLocal0 (.some 1) false
    let rNeg := evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from" [.uint .u32])
      decls protoLayouts [] [.ptr { allocId := 1, offsetBytes := 4 } 8, .ptr { allocId := 1, offsetBytes := 12 } 8]
      locals dstLocal0 (.some 1) false
    let rZero := evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from_unsigned" [.uint .u32])
      decls protoLayouts [] [.ptr { allocId := 1, offsetBytes := 4 } 8, .ptr { allocId := 1, offsetBytes := 4 } 8]
      locals dstLocal0 (.some 1) true
    let rOnePastEnd := evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from_unsigned" [.uint .u32])
      decls protoLayouts [] [.ptr { allocId := 1, offsetBytes := 16 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8]
      locals dstLocal0 (.some 1) true
    -- Unaligned offsets 9 and 1 (both ≡ 1 mod 4), distance 8 divisible by 4 -> 2!
    let rUnaligned := evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from" [.uint .u32])
      decls protoLayouts [] [.ptr { allocId := 1, offsetBytes := 9 } 8, .ptr { allocId := 1, offsetBytes := 1 } 8]
      locals dstLocal0 (.some 1) false
    (stepLocals? rPos).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨2, 8⟩)) ∧
    (stepLocals? rNeg).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨18446744073709551614, 8⟩)) ∧
    (stepLocals? rZero).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨0, 8⟩)) ∧
    (stepLocals? rOnePastEnd).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨4, 8⟩)) ∧
    (stepLocals? rUnaligned).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨2, 8⟩)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- 6(c)–(g): Non-divisible distance, cross-allocation (even at equal offset 0), unsigned
underflow (`lhs < rhs`), ZST `size_of::<T>() == 0`, out-of-bounds endpoint, and
`distance == isize::MIN` ALL fault `.ub`! -/
theorem ptr_offset_from_all_ub_cases :
    let decls := [mkDecl isizeTy, mkDecl arrU32x4Ty, mkDecl arrU32x4Ty]
    let locals := [.uninit,
                   .init (.aggregate 0 [mkU32 1, mkU32 2, mkU32 3, mkU32 4]),
                   .init (.aggregate 0 [mkU32 5, mkU32 6, mkU32 7, mkU32 8])]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .frozen }
    let s := mkState locals [b1, b2]
    let rNonDiv := evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from" [.uint .u32])
      decls protoLayouts [] [.ptr { allocId := 1, offsetBytes := 6 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8]
      locals dstLocal0 (.some 1) false
    let rCrossAlloc := evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from" [.uint .u32])
      decls protoLayouts [] [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8]
      locals dstLocal0 (.some 1) false
    let rUnsignedUnderflow := evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from_unsigned" [.uint .u32])
      decls protoLayouts [] [.ptr { allocId := 1, offsetBytes := 4 } 8, .ptr { allocId := 1, offsetBytes := 8 } 8]
      locals dstLocal0 (.some 1) true
    let rZst := evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from" [.tuple .nil])
      decls protoLayouts [] [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8]
      locals dstLocal0 (.some 1) false
    let rOob := evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from" [.uint .u32])
      decls protoLayouts [] [.ptr { allocId := 1, offsetBytes := 20 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8]
      locals dstLocal0 (.some 1) false
    let rIsizeMinSigned := evalPtrOffsetFromDistanceProto 0 (signedHalfModulus 8) 1 8 false
    let rIsizeMinUnsigned := evalPtrOffsetFromDistanceProto 0 (signedHalfModulus 8) 1 8 true
    isUbNode rNonDiv = true ∧
    isUbNode rCrossAlloc = true ∧
    isUbNode rUnsignedUnderflow = true ∧
    isUbNode rZst = true ∧
    isUbNode rOob = true ∧
    rIsizeMinSigned = .none ∧
    rIsizeMinUnsigned = .none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 6(h): Equal provenance-free integer pointers return `0`, unequal fault `.ub`. -/
theorem ptr_offset_from_provenance_free_eq_vs_neq :
    let decls := [mkDecl isizeTy]
    let locals := [.uninit]
    let s := mkState locals
    let rEq := evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from" [.uint .u32])
      decls protoLayouts [] [mkUsize 4096, mkUsize 4096] locals dstLocal0 (.some 1) false
    let rNeq := evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from" [.uint .u32])
      decls protoLayouts [] [mkUsize 4100, mkUsize 4096] locals dstLocal0 (.some 1) false
    (stepLocals? rEq).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨0, 8⟩)) ∧
    isUbNode rNeq = true := by
  refine ⟨rfl, rfl⟩

/-! ## Section 7: `core::intrinsics::ptr_mask` (Strict Provenance) -/

/-- 7(a)–(d):
- (a) `zerocopy`-style low-bit alignment mask `!(7 : usize)` on 8-byte aligned local masks
  offset `13` to `8` while preserving `allocId` and `tag`;
- (b) Concrete base-address masking (`baseAddr = 0x10000`) masks arbitrary base-preserving mask
  `0x10008` to offset `8` while preserving `allocId` and `tag`;
- (c) Symbolic base fails closed with `.unsupported` when `mask` clears bits `≥ allocAlign`
  (e.g. `!(8 : usize)` on `align = 8`);
- (d) Non-exposure of provenance: `exposedAllocIds` remains `.nil` across all cases! -/
theorem ptr_mask_symbolic_concrete_failclosed_and_nonexposure :
    let decls := [mkDecl rawConstU8Ty, mkDecl aligned16BufTy]
    let locals := [.uninit, .init .unit]
    let b : BorrowEntry := { tag := 7, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [b]
    let maskAlign8 : Nat := 18446744073709551608 -- !7usize = 2^64 - 8
    let maskClearsBit3 : Nat := 18446744073709551607 -- !8usize = 2^64 - 9 (touches bit 3!)
    let ptr13 : ProvenancePtr := { allocId := 7, offsetBytes := 13 }
    let rSym := evalPtrMaskProto s decls protoLayouts [.ptr ptr13 8, mkUsize maskAlign8]
      locals dstLocal0 (.some 1) .none
    let rConcrete := evalPtrMaskProto s decls protoLayouts [.ptr ptr13 8, mkUsize 65544] -- 0x10008
      locals dstLocal0 (.some 1) (.some 65536) -- base 0x10000
    let rSymFail := evalPtrMaskProto s decls protoLayouts [.ptr ptr13 8, mkUsize maskClearsBit3]
      locals dstLocal0 (.some 1) .none
    let rIntPtr := evalPtrMaskProto s decls protoLayouts [mkUsize 4671, mkUsize maskAlign8] -- 0x123f & !7 = 0x1238 = 4664
      locals dstLocal0 (.some 1) .none
    (stepLocals? rSym).bind (fun ls => get? ls 0) =
      .some (.init (.ptr { allocId := 7, offsetBytes := 8 } 8)) ∧
    (stepState? rSym).map (fun s' => s'.memory.exposedAllocIds) = .some .nil ∧
    (stepLocals? rConcrete).bind (fun ls => get? ls 0) =
      .some (.init (.ptr { allocId := 7, offsetBytes := 8 } 8)) ∧
    (stepState? rConcrete).map (fun s' => s'.memory.exposedAllocIds) = .some .nil ∧
    isUnsupportedNode rSymFail = true ∧
    (stepLocals? rIntPtr).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨4664, 8⟩)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 8: `core::intrinsics::black_box` -/

/-- 8(a)–(e): Scalar identity, pointer provenance/tag preservation, compound struct preservation,
invalid/uninit scalar UB preservation, `MaybeUninit` union preservation, and diverging `target = none` UB. -/
theorem black_box_identity_provenance_compound_validity_and_diverging :
    let p : ProvenancePtr := { allocId := 42, offsetBytes := 12 }
    let sSc := mkState [.uninit]
    let rScalar := evalBlackBoxProto sSc (mkTarget "core::intrinsics::black_box" [.uint .u32])
      [mkDecl u32Ty] protoLayouts [] [mkU32 1234] [.uninit] dstLocal0 (.some 1)
    let rPtr := evalBlackBoxProto sSc (mkTarget "core::intrinsics::black_box" [.rawPtr .not (.uint .u32)])
      [mkDecl rawConstU32Ty] protoLayouts [] [.ptr p 8] [.uninit] dstLocal0 (.some 1)
    let compoundVal : Value := .aggregate 0 [mkU8 5, mkU32 99]
    let rCompound := evalBlackBoxProto sSc (mkTarget "core::intrinsics::black_box" [paddedPairTy.kind])
      [mkDecl paddedPairTy] protoLayouts [] [compoundVal] [.uninit] dstLocal0 (.some 1)
    let rUninitUb := evalBlackBoxProto sSc (mkTarget "core::intrinsics::black_box" [.uint .u32])
      [mkDecl u32Ty] protoLayouts [] [.uninit] [.uninit] dstLocal0 (.some 1)
    let rBadBoolUb := evalBlackBoxProto sSc (mkTarget "core::intrinsics::black_box" [.bool])
      [mkDecl boolTy] protoLayouts [] [.scalar ⟨2, 1⟩] [.uninit] dstLocal0 (.some 1)
    let rMaybeUninitOk := evalBlackBoxProto sSc (mkTarget "core::intrinsics::black_box" [maybeUninitU32Ty.kind])
      [mkDecl maybeUninitU32Ty] protoLayouts [] [.aggregate 0 [.unit]] [.uninit] dstLocal0 (.some 1)
    let rDivergingUb := evalBlackBoxProto sSc (mkTarget "core::intrinsics::black_box" [.uint .u32])
      [mkDecl u32Ty] protoLayouts [] [mkU32 1] [.uninit] dstLocal0 .none
    stepLocals? rScalar = .some [.init (mkU32 1234)] ∧
    stepLocals? rPtr = .some [.init (.ptr p 8)] ∧
    stepLocals? rCompound = .some [.init compoundVal] ∧
    isUbNode rUninitUb = true ∧
    isUbNode rBadBoolUb = true ∧
    stepLocals? rMaybeUninitOk = .some [.init (.aggregate 0 [.unit])] ∧
    isUbNode rDivergingUb = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 9: Dual Alignment — Direct `MiniRustSpec.Interp` + `LeanMiri` Theorems -/

section MiniRustDualAlignment

open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Gen
open MiniRustSpec.Interp

/-- Construct a minimal `MiniRustSpec.Interp.Mach` backed by explicit live allocations `allocs`. -/
def mkMiniRustMach (allocs : List (Gen.Allocation Unit Unit)) : Mach :=
  { prog :=
      { functions := ⟨[]⟩
        start := ⟨⟨0⟩⟩
        globals := ⟨[]⟩
        traits := ⟨[]⟩
        vtables := ⟨[]⟩ }
    mem := { memory := { allocations := allocs, _phantom := {} }, accesses := [] }
    intptrcast := { exposed := ⟨[]⟩ }
    threads := []
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

def mrInitBytes (bs : List UInt8) : List Byte :=
  bs.map (fun b => Gen.AbstractByte.Init b none)

def mrRawPtrTy : Gen.Type := .Ptr (.Raw .None)
def mrRefU32Ty : Gen.Type :=
  .Ptr (.Ref .Immutable
    { layout := .Sized ⟨4⟩ ⟨4⟩, inhabited := true, unsafe_cells := .Sized [], freeze := true, unpin := true })
def mrRefPaddedTy : Gen.Type :=
  .Ptr (.Ref .Immutable
    { layout := .Sized ⟨8⟩ ⟨4⟩, inhabited := true, unsafe_cells := .Sized [], freeze := true, unpin := true })
def mrRefZstTy : Gen.Type :=
  .Ptr (.Ref .Immutable
    { layout := .Sized ⟨0⟩ ⟨1⟩, inhabited := true, unsafe_cells := .Sized [], freeze := true, unpin := true })

/--
**Direct `MiniRustSpec.Interp` Dual-Alignment Theorem (`ptr_offset_from` & `ptr_offset_from_unsigned`)**:
On two live 16-byte allocations at bases `0x1000` (alloc 0) and `0x2000` (alloc 1),
`MiniRustSpec.Interp.evalPtrOffsetFrom` agrees identically with `evalPtrOffsetFromProto` on:
1. positive in-bounds offset (`+8` bytes -> `2` `u32` elements);
2. negative in-bounds signed offset (`-8` bytes -> `-2` `u32` elements);
3. unsigned underflow UB (`nonneg = true`, `-8` bytes -> `.error (.ub _)`);
4. cross-allocation UB (alloc 0 vs alloc 1 -> `.error (.ub _)`);
5. equal provenance-free dangling pointers (`0x1000 - 0x1000 = 0`).
-/
theorem minirust_ptr_offset_from_dual_alignment :
    let alloc0 : Gen.Allocation Unit Unit :=
      { data := List.replicate 16 (.Init 0 none), addr := 4096, align := ⟨4⟩, kind := .Stack, live := true, extra := () }
    let alloc1 : Gen.Allocation Unit Unit :=
      { data := List.replicate 16 (.Init 0 none), addr := 8192, align := ⟨4⟩, kind := .Stack, live := true, extra := () }
    let m := mkMiniRustMach [alloc0, alloc1]
    let p0_4 : Val := .Ptr ⟨⟨4100, some (⟨0⟩, ())⟩, none⟩
    let p0_12 : Val := .Ptr ⟨⟨4108, some (⟨0⟩, ())⟩, none⟩
    let p1_0 : Val := .Ptr ⟨⟨8192, some (⟨1⟩, ())⟩, none⟩
    let pDangling : Val := .Ptr ⟨⟨4096, none⟩, none⟩
    (evalPtrOffsetFrom m true false (p0_12, mrRawPtrTy) (p0_4, mrRawPtrTy) =
      .ok (.Int 8, .Int ⟨.Signed, x86_64.PTR_SIZE⟩)) ∧
    (evalPtrOffsetFrom m true false (p0_4, mrRawPtrTy) (p0_12, mrRawPtrTy) =
      .ok (.Int (-8), .Int ⟨.Signed, x86_64.PTR_SIZE⟩)) ∧
    (match evalPtrOffsetFrom m true true (p0_4, mrRawPtrTy) (p0_12, mrRawPtrTy) with
      | .error (.ub _) => true | _ => false) = true ∧
    (match evalPtrOffsetFrom m true false (p0_4, mrRawPtrTy) (p1_0, mrRawPtrTy) with
      | .error (.ub _) => true | _ => false) = true ∧
    (evalPtrOffsetFrom m true false (pDangling, mrRawPtrTy) (pDangling, mrRawPtrTy) =
      .ok (.Int 0, .Int ⟨.Signed, x86_64.PTR_SIZE⟩)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

def mrBoolVal? : Val → Option Bool
  | .Bool b => .some b
  | _ => .none

/--
**Direct `MiniRustSpec.Interp` Dual-Alignment Theorem (`raw_eq`)**:
`MiniRustSpec.Interp.evalIntrinsic ... .RawEq` agrees identically with `evalRawEqProto` on:
1. equal initialized `u32` allocations -> `true`;
2. unequal initialized `u32` allocations -> `false`;
3. struct with uninitialized padding bytes (`[7, Uninit, Uninit, Uninit, 42, 0, 0, 0]`) -> `.error (.ub _)`;
4. ZST `&()` -> `true`.
-/
theorem minirust_raw_eq_dual_alignment :
    let allocEq1 : Gen.Allocation Unit Unit :=
      { data := mrInitBytes [42, 0, 0, 0], addr := 4096, align := ⟨4⟩, kind := .Stack, live := true, extra := () }
    let allocEq2 : Gen.Allocation Unit Unit :=
      { data := mrInitBytes [42, 0, 0, 0], addr := 4100, align := ⟨4⟩, kind := .Stack, live := true, extra := () }
    let allocNeq : Gen.Allocation Unit Unit :=
      { data := mrInitBytes [99, 0, 0, 0], addr := 4104, align := ⟨4⟩, kind := .Stack, live := true, extra := () }
    let paddedBytes : List Byte :=
      [.Init 7 none, .Uninit, .Uninit, .Uninit, .Init 42 none, .Init 0 none, .Init 0 none, .Init 0 none]
    let allocPad1 : Gen.Allocation Unit Unit :=
      { data := paddedBytes, addr := 4112, align := ⟨4⟩, kind := .Stack, live := true, extra := () }
    let allocPad2 : Gen.Allocation Unit Unit :=
      { data := paddedBytes, addr := 4120, align := ⟨4⟩, kind := .Stack, live := true, extra := () }
    let m := mkMiniRustMach [allocEq1, allocEq2, allocNeq, allocPad1, allocPad2]
    let p0 : Val := .Ptr ⟨⟨4096, some (⟨0⟩, ())⟩, none⟩
    let p1 : Val := .Ptr ⟨⟨4100, some (⟨1⟩, ())⟩, none⟩
    let p2 : Val := .Ptr ⟨⟨4104, some (⟨2⟩, ())⟩, none⟩
    let p3 : Val := .Ptr ⟨⟨4112, some (⟨3⟩, ())⟩, none⟩
    let p4 : Val := .Ptr ⟨⟨4120, some (⟨4⟩, ())⟩, none⟩
    let pZst : Val := .Ptr ⟨⟨1, none⟩, none⟩
    ((evalIntrinsic m .RawEq [(p0, mrRefU32Ty), (p1, mrRefU32Ty)] .Bool).toOption.bind
        (fun r => mrBoolVal? r.1) = .some true) ∧
    ((evalIntrinsic m .RawEq [(p0, mrRefU32Ty), (p2, mrRefU32Ty)] .Bool).toOption.bind
        (fun r => mrBoolVal? r.1) = .some false) ∧
    (match evalIntrinsic m .RawEq [(p3, mrRefPaddedTy), (p4, mrRefPaddedTy)] .Bool with
      | .error (.ub _) => true | _ => false) = true ∧
    ((evalIntrinsic m .RawEq [(pZst, mrRefZstTy), (pZst, mrRefZstTy)] .Bool).toOption.bind
        (fun r => mrBoolVal? r.1) = .some true) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

end MiniRustDualAlignment

/-! ## Section 10: Non-Vacuity Witnesses & Mechanical Standard-Axiom Gate -/

/--
Non-vacuity witness instantiating EVERY universally quantified theorem in
`Anneal.TcbCoreMemPtrIntrinsicsPrototype` with concrete, satisfiable inputs:
1. `compareUnsignedBytesProto_eq_miriBytesCompareSpec` on `[0x80]` vs `[0x7f]`;
2. `ptrMask_baseAddr_invariant` on 64-bit `m = 3` (`align = 8`), `baseAddr = 0x10000`, `relOff = 13`, `mask = !7`;
3. `evalPtrMaskValueProto_preserves_provenance` and `evalPtrMaskValueProto_symbolic_eq_concrete`
   on concrete stack borrow tag `7` with `baseAddr = 0x10000` and `baseAddr = 0x20008`!
4. `evalPtrOffsetFromDistanceProto_zst_ub`, `_unsigned_underflow_ub`, `_isizeMin_ub`;
5. `evalBlackBoxProto_valid_direct_dest` on `u32 = 42`.
-/
theorem non_vacuity_all_quantified_theorems :
    (compareUnsignedBytesProto [128] [127] = miriBytesCompareSpec [128] [127]) ∧
    (bitwiseAndBits 64 (65536 + 13) 18446744073709551608 =
      65536 + bitwiseAndBits 64 13 18446744073709551608) ∧
    (∃ newOff,
      evalPtrMaskValueProto
        (mkState [.uninit, .init .unit] [{ tag := 7, targetLocal := 1, targetProjection := [], perm := .unique }])
        [.uninit, .init .unit] [mkDecl rawConstU8Ty, mkDecl aligned16BufTy] protoLayouts
        (.prov { allocId := 7, offsetBytes := 13 }) ⟨18446744073709551608, 8⟩ .none =
        .ok (.ptr { allocId := 7, offsetBytes := newOff } 8)) ∧
    (evalPtrMaskValueProto
        (mkState [.uninit, .init .unit] [{ tag := 7, targetLocal := 1, targetProjection := [], perm := .unique }])
        [.uninit, .init .unit] [mkDecl rawConstU8Ty, mkDecl aligned16BufTy] protoLayouts
        (.prov { allocId := 7, offsetBytes := 13 }) ⟨18446744073709551608, 8⟩ (.some 131080) =
      .ok (.ptr { allocId := 7, offsetBytes := 8 } 8)) ∧
    (evalPtrOffsetFromDistanceProto 4 0 0 8 false = .none) ∧
    (evalPtrOffsetFromDistanceProto 4 8 4 8 true = .none) ∧
    (evalPtrOffsetFromDistanceProto 0 (signedHalfModulus 8) 1 8 false = .none) ∧
    (evalBlackBoxProto (mkState [.uninit]) (mkTarget "core::intrinsics::black_box" [.uint .u32])
        [mkDecl u32Ty] protoLayouts [] [mkU32 42] [.uninit] dstLocal0 (.some 1) =
      MirStepNode.step {
        frame := { blockIdx := 1, stmtIdx := 0, locals := [.init (mkU32 42)] }
        memory := emptyMemory }) := by
  refine ⟨compareUnsignedBytesProto_eq_miriBytesCompareSpec [128] [127], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ptrMask_baseAddr_invariant 64 3 65536 13 18446744073709551608
      (by decide) (by decide) (by decide) (by decide)
  · rcases evalPtrMaskValueProto_preserves_provenance
      (mkState [.uninit, .init .unit] [{ tag := 7, targetLocal := 1, targetProjection := [], perm := .unique }])
      [.uninit, .init .unit] [mkDecl rawConstU8Ty, mkDecl aligned16BufTy] protoLayouts
      { allocId := 7, offsetBytes := 13 } ⟨18446744073709551608, 8⟩ .none
      (.ptr { allocId := 7, offsetBytes := 8 } 8) rfl with ⟨newOff, hEq⟩
    exact ⟨newOff, hEq ▸ rfl⟩
  · exact evalPtrMaskValueProto_symbolic_eq_concrete
      (mkState [.uninit, .init .unit] [{ tag := 7, targetLocal := 1, targetProjection := [], perm := .unique }])
      [.uninit, .init .unit] [mkDecl rawConstU8Ty, mkDecl aligned16BufTy] protoLayouts
      { allocId := 7, offsetBytes := 13 } ⟨18446744073709551608, 8⟩ 8 0 131080
      (.ptr { allocId := 7, offsetBytes := 8 } 8)
      rfl rfl ⟨3, rfl⟩ (by decide) (by decide) rfl
  · exact evalPtrOffsetFromDistanceProto_zst_ub 4 0 8 false
  · exact evalPtrOffsetFromDistanceProto_unsigned_underflow_ub 4 8 4 8 (by decide)
  · exact evalPtrOffsetFromDistanceProto_isizeMin_ub 1 8 (by decide) false
  · exact evalBlackBoxProto_valid_direct_dest (mkState [.uninit])
      (mkTarget "core::intrinsics::black_box" [.uint .u32])
      [mkDecl u32Ty] protoLayouts [] (mkU32 42) [.uninit] [.init (mkU32 42)] 0 1
      rfl rfl rfl rfl

/-- Aggregate conjunction linking every prototype and test theorem for axiom auditing. -/
theorem all_proto_and_test_theorems :
    (classifyRustIntrinsicProto? "core::intrinsics::copy" = .some .copy) ∧
    (∀ xs ys, compareUnsignedBytesProto xs ys = miriBytesCompareSpec xs ys) ∧
    (∀ W m baseAddr relOff mask,
      baseAddr % 2 ^ m = 0 → mask < 2 ^ W → (2 ^ W - 1) - mask < 2 ^ m →
      baseAddr + relOff < 2 ^ W →
      bitwiseAndBits W (baseAddr + relOff) mask = baseAddr + bitwiseAndBits W relOff mask) ∧
    True := by
  have _ := classify_all_8_core_intrinsics
  have _ := classify_preserves_existing_and_rejects_wrappers
  have _ := copy_nonoverlapping_u32_array
  have _ := copy_preserves_ptr_provenance_and_tag
  have _ := copy_preserves_uninit_maybe_uninit
  have _ := copy_overlapping_forward_shift
  have _ := copy_overlapping_backward_shift
  have _ := copy_self_identical_succeeds
  have _ := copy_zero_count_aligned_vs_misaligned_and_null
  have _ := copy_total_bytes_overflow_ub
  have _ := copy_tree_borrows_frozen_and_read_then_write_ub
  have _ := copy_stmt_wrapper_overlapping_forward
  have _ := compare_bytes_eq_lt_gt
  have _ := compare_bytes_unsigned_high_bit
  have _ := compare_bytes_uninit_idx0_and_eager_tail_ub
  have _ := compare_bytes_zero_and_provenance_unsupported
  have _ := raw_eq_initialized_struct_true_and_false
  have _ := raw_eq_padded_struct_uninit_padding_ub
  have _ := raw_eq_misaligned_zst_and_unsized
  have _ := typed_swap_disjoint_ptrs_preserves_provenance
  have _ := typed_swap_same_alloc_same_tag_disjoint_elements
  have _ := typed_swap_overlap_ub_and_zst_semantics
  have _ := typed_swap_validity_uninit_bool_maybeuninit_and_padded
  have _ := typed_swap_tree_borrows_and_unsized
  have _ := ptr_offset_from_pos_neg_zero_end_and_unaligned_divisible
  have _ := ptr_offset_from_all_ub_cases
  have _ := ptr_offset_from_provenance_free_eq_vs_neq
  have _ := ptr_mask_symbolic_concrete_failclosed_and_nonexposure
  have _ := black_box_identity_provenance_compound_validity_and_diverging
  have _ := minirust_ptr_offset_from_dual_alignment
  have _ := minirust_raw_eq_dual_alignment
  have _ := non_vacuity_all_quantified_theorems
  exact ⟨rfl, compareUnsignedBytesProto_eq_miriBytesCompareSpec, ptrMask_baseAddr_invariant, trivial⟩

section MechanicalAxiomAudit

open Lean Elab Command

/--
Mechanical standard-axiom and safety audit: fails compilation unless EVERY
declaration in `Anneal.TcbCoreMemPtrIntrinsicsPrototype` AND every listed test
theorem in `Anneal.TcbCoreMemPtrIntrinsicsProtoTests` is `!isUnsafe` and depends
strictly on Lean's standard axioms `{propext, Classical.choice, Quot.sound}`
(zero `sorryAx`, zero `Lean.ofReduceBool` / `native_decide`, zero custom axioms).
-/
elab "#assert_proto_standard_axioms " ids:ident* : command => do
  let env ← getEnv
  let protoMod := `Anneal.TcbCoreMemPtrIntrinsicsPrototype
  let some idx := env.getModuleIdx? protoMod
    | throwError "[PROTO-AXIOM-AUDIT] {protoMod} is not imported"
  let mut union : Array Name := #[]
  let protoConsts := env.header.moduleData[idx.toNat]!.constNames
  for c in protoConsts do
    if let some ci := env.find? c then
      if ci.isUnsafe then
        throwError "[PROTO-AXIOM-AUDIT] unsafe declaration {c} in {protoMod}"
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "[PROTO-AXIOM-AUDIT] {c} (in {protoMod}) depends on non-standard axiom {a}"
      unless union.contains a do
        union := union.push a
  let mut seen : Lean.NameSet := {}
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    if seen.contains n then
      throwError "[PROTO-AXIOM-AUDIT] duplicate declaration {n}"
    seen := seen.insert n
    if let some ci := env.find? n then
      if ci.isUnsafe then
        throwError "[PROTO-AXIOM-AUDIT] unsafe test declaration {n}"
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "[PROTO-AXIOM-AUDIT] {n} depends on non-standard axiom {a}"
      unless union.contains a do
        union := union.push a
  logInfo m!"[PROTO-AXIOM-AUDIT] proto_decls={protoConsts.size} test_theorems={ids.size} axioms={union.toList} unsafe_free=true sorry_free=true ok=true"

#assert_proto_standard_axioms
  classify_all_8_core_intrinsics
  classify_preserves_existing_and_rejects_wrappers
  copy_nonoverlapping_u32_array
  copy_preserves_ptr_provenance_and_tag
  copy_preserves_uninit_maybe_uninit
  copy_overlapping_forward_shift
  copy_overlapping_backward_shift
  copy_self_identical_succeeds
  copy_zero_count_aligned_vs_misaligned_and_null
  copy_total_bytes_overflow_ub
  copy_tree_borrows_frozen_and_read_then_write_ub
  copy_stmt_wrapper_overlapping_forward
  compare_bytes_eq_lt_gt
  compare_bytes_unsigned_high_bit
  compare_bytes_uninit_idx0_and_eager_tail_ub
  compare_bytes_zero_and_provenance_unsupported
  raw_eq_initialized_struct_true_and_false
  raw_eq_padded_struct_uninit_padding_ub
  raw_eq_misaligned_zst_and_unsized
  typed_swap_disjoint_ptrs_preserves_provenance
  typed_swap_same_alloc_same_tag_disjoint_elements
  typed_swap_overlap_ub_and_zst_semantics
  typed_swap_validity_uninit_bool_maybeuninit_and_padded
  typed_swap_tree_borrows_and_unsized
  ptr_offset_from_pos_neg_zero_end_and_unaligned_divisible
  ptr_offset_from_all_ub_cases
  ptr_offset_from_provenance_free_eq_vs_neq
  ptr_mask_symbolic_concrete_failclosed_and_nonexposure
  black_box_identity_provenance_compound_validity_and_diverging
  minirust_ptr_offset_from_dual_alignment
  minirust_raw_eq_dual_alignment
  non_vacuity_all_quantified_theorems
  all_proto_and_test_theorems

end MechanicalAxiomAudit

end Anneal.TcbCoreMemPtrIntrinsicsProtoTests
