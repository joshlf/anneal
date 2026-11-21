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
# Kernel-Checked Test Suite & Alignment Audit for 8 Core Memory/Pointer Intrinsics

Every theorem in this module is checked purely by the Lean 4 kernel (`rfl`,
`decide`, and structural/tactical proofs — zero `sorry`, zero `native_decide`),
covering positive witnesses, negative/UB edge cases, `MiniRustSpec.Interp`
agreement theorems that run one scenario in both semantics and equate the
observations, instantiations of the universally quantified `lean-miri` mirror
theorems, non-vacuity witnesses for every quantified prototype theorem, and a
trailing mechanical MetaM axiom audit verifying that every declaration in
`Anneal.TcbCoreMemPtrIntrinsicsPrototype` and every declaration of this module
depends strictly on Lean's standard axioms
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

/-- 2(c): `count == 0`: alignment is still checked (misaligned offset `2` for `u32` faults `.ub`),
but validity is not required for a zero-byte copy ("`src` must be [valid] for reads of
`count * size_of::<T>()` bytes or that number must be 0"): an aligned dangling integer pointer and
a null pointer both succeed as a no-op. -/
theorem copy_zero_count_alignment_checked_validity_not_required :
    let decls := [mkDecl unitTy, mkDecl arrU32x2Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 1, mkU32 2])]
    let b : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [b]
    let okDangling := evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u32]) decls protoLayouts []
      [mkUsize 4096, mkUsize 4100, mkUsize 0] locals dstLocal0 (.some 1)
    let ubMisaligned := evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u32]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 2 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8, mkUsize 0]
      locals dstLocal0 (.some 1)
    let okNull := evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u32]) decls protoLayouts []
      [mkUsize 0, mkUsize 4096, mkUsize 0] locals dstLocal0 (.some 1)
    stepLocals? okDangling = .some [.init .unit, .init (.aggregate 0 [mkU32 1, mkU32 2])] ∧
    isUbNode ubMisaligned = true ∧
    stepLocals? okNull = .some [.init .unit, .init (.aggregate 0 [mkU32 1, mkU32 2])] := by
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

/-- 3(d) & 3(e): `bytes == 0` with non-null pointers returns `0`; with a null pointer it faults
`.ub` (both pointers must be "[valid] for reads of `bytes` bytes" and a null pointer "is *never*
valid for reads/writes"; `lean-miri` skips the zero-sized check and returns `0`); and
provenance-carrying pointer bytes fail closed with `.unsupported`. -/
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

/-! ## Section 9: Zero-Sized Access, Null, and Same-Address Semantics -/

/-- 9(a): the documented null / zero-size matrix across the raw-pointer intrinsics.
- `copy` with zero total bytes requires no validity (`ptr::copy`: "or that number must be 0"),
  so null pointers succeed, for `count == 0` and for a ZST pointee with `count > 0`, in both the
  integer and the unbacked `allocId = 0` pointer encodings; misalignment is still `.ub`.
- A null pointer with non-zero total bytes is `.ub` on the source and on the destination side.
- `compare_bytes` and `typed_swap_nonoverlapping` require pointers "[valid] for reads" /
  "[valid] for both reads and writes", and a null pointer "is *never* valid for reads/writes":
  null is `.ub` even for zero bytes / a ZST, while dangling non-null pointers succeed. -/
theorem zero_size_null_matrix :
    let decls := [mkDecl unitTy, mkDecl arrU32x2Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 1, mkU32 2])]
    let b : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [b]
    let copyU32 := mkTarget "core::intrinsics::copy" [.uint .u32]
    let copyZst := mkTarget "core::intrinsics::copy" [.tuple .nil]
    let live (o : Nat) : Value := .ptr { allocId := 1, offsetBytes := o } 8
    let okCopyNullInt := evalCopyProto s copyU32 decls protoLayouts []
      [mkUsize 0, mkUsize 0, mkUsize 0] locals dstLocal0 (.some 1)
    let okCopyNullPtr := evalCopyProto s copyU32 decls protoLayouts []
      [.ptr { allocId := 0, offsetBytes := 0 } 8, .ptr { allocId := 0, offsetBytes := 0 } 8, mkUsize 0]
      locals dstLocal0 (.some 1)
    let okCopyNullZstElems := evalCopyProto s copyZst decls protoLayouts []
      [mkUsize 0, mkUsize 0, mkUsize 7] locals dstLocal0 (.some 1)
    let ubCopyMisalignedInt := evalCopyProto s copyU32 decls protoLayouts []
      [mkUsize 4098, mkUsize 4096, mkUsize 0] locals dstLocal0 (.some 1)
    let ubCopyNullSrc := evalCopyProto s copyU32 decls protoLayouts []
      [mkUsize 0, live 0, mkUsize 1] locals dstLocal0 (.some 1)
    let ubCopyNullDst := evalCopyProto s copyU32 decls protoLayouts []
      [live 0, mkUsize 0, mkUsize 1] locals dstLocal0 (.some 1)
    let ubCmpNull := evalCompareBytesProto s decls protoLayouts
      [mkUsize 0, mkUsize 0, mkUsize 0] locals dstLocal0 (.some 1)
    let okCmpDangling := evalCompareBytesProto s decls protoLayouts
      [mkUsize 1, mkUsize 1, mkUsize 0] locals dstLocal0 (.some 1)
    let ubSwapNullZst := evalTypedSwapNonOverlappingProto s
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [.tuple .nil]) decls protoLayouts []
      [mkUsize 0, mkUsize 8] locals dstLocal0 (.some 1)
    stepLocals? okCopyNullInt = .some [.init .unit, .init (.aggregate 0 [mkU32 1, mkU32 2])] ∧
    stepLocals? okCopyNullPtr = .some [.init .unit, .init (.aggregate 0 [mkU32 1, mkU32 2])] ∧
    stepLocals? okCopyNullZstElems = .some [.init .unit, .init (.aggregate 0 [mkU32 1, mkU32 2])] ∧
    isUbNode ubCopyMisalignedInt = true ∧
    isUbNode ubCopyNullSrc = true ∧
    isUbNode ubCopyNullDst = true ∧
    isUbNode ubCmpNull = true ∧
    (stepLocals? okCmpDangling).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨0, 4⟩)) ∧
    isUbNode ubSwapNullZst = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 9(b): `ptr_offset_from` on pointers that "point to the same address" needs no liveness or
bounds (`checkSignedAccess _ 0` performs no check):
- the same dangling pointer into a DEAD allocation yields `0`;
- the same out-of-bounds pointer into a live allocation yields `0`, also under two distinct tags
  with equal effective offsets;
- an unbacked `allocId = 0` pointer and the integer pointer with the same address yield `0`;
while a non-zero distance still needs a live allocation with both endpoints in bounds:
- the same dead tag at two offsets is `.ub`; a live and a dead pointer are `.ub`;
- an out-of-bounds endpoint at non-zero distance is `.ub`;
- two distinct dead tags of one root local (storage generation unknown) fail closed. -/
theorem ptr_offset_from_same_address_needs_no_liveness_or_bounds :
    let decls := [mkDecl isizeTy, mkDecl arrU32x4Ty, mkDecl arrU32x4Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 1, mkU32 2, mkU32 3, mkU32 4]), .dead]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := .frozen }
    let b3 : BorrowEntry :=
      { tag := 3, targetLocal := 2, targetProjection := [], perm := .frozen, allocDead := true }
    let b4 : BorrowEntry :=
      { tag := 4, targetLocal := 2, targetProjection := [], perm := .frozen, allocDead := true }
    let s := mkState locals [b1, b2, b3, b4]
    let run (a b : Value) : MirStepNode :=
      evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from" [.uint .u32])
        decls protoLayouts [] [a, b] locals dstLocal0 (.some 1) false
    let p (tag off : Nat) : Value := .ptr { allocId := tag, offsetBytes := off } 8
    let result (n : MirStepNode) : Option LocalSlot := (stepLocals? n).bind (fun ls => get? ls 0)
    result (run (p 3 8) (p 3 8)) = .some (.init (.scalar ⟨0, 8⟩)) ∧
    result (run (p 1 400) (p 1 400)) = .some (.init (.scalar ⟨0, 8⟩)) ∧
    result (run (p 1 400) (p 2 400)) = .some (.init (.scalar ⟨0, 8⟩)) ∧
    result (run (p 0 4096) (mkUsize 4096)) = .some (.init (.scalar ⟨0, 8⟩)) ∧
    result (run (p 1 8) (p 2 0)) = .some (.init (.scalar ⟨2, 8⟩)) ∧
    isUbNode (run (p 3 8) (p 3 4)) = true ∧
    isUbNode (run (p 1 8) (p 3 8)) = true ∧
    isUbNode (run (p 1 400) (p 2 396)) = true ∧
    isUbNode (run (p 0 4096) (mkUsize 4100)) = true ∧
    isUnsupportedNode (run (p 3 8) (p 4 8)) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 10: Exact Byte Images, Typed Validity from Layouts, and Global Allocations -/

/-- Layout table for layout-directed byte images and typed validity:
- idx 0: `u32`; idx 1: `u8`; idx 2: `bool` (valid range `0..=1`);
- idx 3: padded struct `Inner { a: u8, b: u32 }` (size 8, offsets `[0, 4]`, padding `1..3`);
- idx 4: `Outer { inner: Inner }` (size 8), field layouts `[3]`;
- idx 5: `Two<A, B> { second: B, first: A }` instantiated as `Two<u8, bool>` (size 2, offsets
  `[0, 1]`): field layouts `[2, 1]` are `(bool, u8)`, the REVERSE of its generic arguments;
- idx 6: `[bool; 2]`, element layout `[2]`; idx 7: `Flags { bits: [bool; 2] }`;
- idx 8: non-null thin pointer (valid range `1..=usize::MAX`); idx 9: `NonNullU8<u8> { p: *const u8 }`;
- idx 10: `MaybeUninit<[u8; 4]>` union (size 4, align 1). -/
def exactLayouts : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [ { size := ⟨4⟩, align := ⟨4⟩, fields := .primitive, variants := .single 0,
          backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
          isUninhabited := false },
        { size := ⟨1⟩, align := ⟨1⟩, fields := .primitive, variants := .single 0,
          backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
          isUninhabited := false },
        { size := ⟨1⟩, align := ⟨1⟩, fields := .primitive, variants := .single 0,
          backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
          isUninhabited := false },
        { size := ⟨8⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], variants := .single 0,
          backendRepr := .memory, fieldLayouts := [1, 0], isUninhabited := false },
        { size := ⟨8⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩] [0], variants := .single 0,
          backendRepr := .memory, fieldLayouts := [3], isUninhabited := false },
        { size := ⟨2⟩, align := ⟨1⟩, fields := .arbitrary [⟨0⟩, ⟨1⟩] [0, 1], variants := .single 0,
          backendRepr := .memory, fieldLayouts := [2, 1], isUninhabited := false },
        { size := ⟨2⟩, align := ⟨1⟩, fields := .array ⟨1⟩ 2, variants := .single 0,
          backendRepr := .memory, fieldLayouts := [2], isUninhabited := false },
        { size := ⟨2⟩, align := ⟨1⟩, fields := .arbitrary [⟨0⟩] [0], variants := .single 0,
          backendRepr := .memory, fieldLayouts := [6], isUninhabited := false },
        { size := ⟨8⟩, align := ⟨8⟩, fields := .primitive, variants := .single 0,
          backendRepr := .scalar (.initialized (.pointer 0) ⟨1, 18446744073709551615⟩),
          isUninhabited := false },
        { size := ⟨8⟩, align := ⟨8⟩, fields := .arbitrary [⟨0⟩] [0], variants := .single 0,
          backendRepr := .memory, fieldLayouts := [8], isUninhabited := false },
        { size := ⟨4⟩, align := ⟨1⟩, fields := .union 2, variants := .single 0,
          backendRepr := .memory, isUninhabited := false } ] }

def outerTy : Ty := { kind := .adt "tests::Outer" .nil, layoutIdx := 4 }
def twoU8BoolTy : Ty := { kind := .adt "tests::Two" [.uint .u8, .bool], layoutIdx := 5 }
def flagsTy : Ty := { kind := .adt "tests::Flags" .nil, layoutIdx := 7 }
def nonNullU8Ty : Ty := { kind := .adt "tests::NonNullU8" [.uint .u8], layoutIdx := 9 }
def maybeUninitBufTy : Ty :=
  { kind := .adt "core::mem::maybe_uninit::MaybeUninit" [.array (.uint .u8) 4], layoutIdx := 10 }

/-- Continue with `next` from the state reached by a successful step. -/
def andThen (n : MirStepNode) (next : MachineState → MirStepNode) : MirStepNode :=
  match n with
  | .tau (.running s') => next s'
  | other => other

/-- Typed swap of two locals of type `ty` holding `x` and `y`. -/
def swapLocals (ty : Ty) (x y : Value) : MirStepNode :=
  let decls := [mkDecl unitTy, mkDecl ty, mkDecl ty]
  let locals : List LocalSlot := [.uninit, .init x, .init y]
  let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
  let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .unique }
  evalTypedSwapNonOverlappingProto (mkState locals [b1, b2])
    (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [ty.kind]) decls exactLayouts []
    [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8]
    locals dstLocal0 (.some 1)

/-- 10(a): the byte image of a nested padded struct keeps its padding.
`Outer { inner: Inner { a: u8 = 1, b: u32 = 2 } }` occupies `[01, U, U, U, 02, 00, 00, 00]`:
- comparing 5 bytes reads padding byte `1` and is `.ub` (an encoder that lays `inner` out back to
  back would instead compare `[01, 02, 00, 00, 00]` and return `0`);
- comparing only byte `0` returns `0`;
- comparing the 4 bytes of `b` at offset `4` returns `0` (not `.ub` from misplaced padding);
- `raw_eq` over the whole struct is `.ub` (padding). -/
theorem byte_image_of_nested_padded_struct_is_exact :
    let decls := [mkDecl i32Ty, mkDecl outerTy, mkDecl outerTy]
    let v : Value := .aggregate 0 [.aggregate 0 [mkU8 1, mkU32 2]]
    let locals := [.uninit, .init v, .init v]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .frozen }
    let s := mkState locals [b1, b2]
    let cmp (off n : Nat) : MirStepNode :=
      evalCompareBytesProto s decls exactLayouts
        [.ptr { allocId := 1, offsetBytes := off } 8, .ptr { allocId := 2, offsetBytes := off } 8, mkUsize n]
        locals dstLocal0 (.some 1)
    let rawEq := evalRawEqProto s (mkTarget "core::intrinsics::raw_eq" [outerTy.kind]) decls exactLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8]
      locals dstLocal0 (.some 1)
    isUbNode (cmp 0 5) = true ∧
    (stepLocals? (cmp 0 1)).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨0, 4⟩)) ∧
    (stepLocals? (cmp 4 4)).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨0, 4⟩)) ∧
    isUbNode rawEq = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- 10(b): typed validity of an ADT comes from its layout, not from its generic arguments.
`Two<u8, bool>` stores `(second: bool, first: u8)`:
- `(second = 2, first = 1)` holds an invalid `bool` and is `.ub` (validating the fields as the
  generic arguments `(u8, bool)` would accept it);
- `(second = 1, first = 2)` is a valid value, so the swap is NOT `.ub` (the same mistake would
  reject it);
- a `bool = 2` inside an array field (`Flags { bits: [bool; 2] }`) is `.ub`, and valid flags swap;
- a null pointer in a non-null pointer field (`NonNullU8`) is `.ub`. -/
theorem typed_swap_validity_follows_layout_not_generic_args :
    isUbNode (swapLocals twoU8BoolTy
      (.aggregate 0 [.scalar ⟨2, 1⟩, mkU8 1]) (.aggregate 0 [.scalar ⟨1, 1⟩, mkU8 9])) = true ∧
    isUbNode (swapLocals twoU8BoolTy
      (.aggregate 0 [.scalar ⟨1, 1⟩, mkU8 2]) (.aggregate 0 [.scalar ⟨0, 1⟩, mkU8 9])) = false ∧
    isUbNode (swapLocals flagsTy
      (.aggregate 0 [.aggregate 0 [.scalar ⟨2, 1⟩, .scalar ⟨1, 1⟩]])
      (.aggregate 0 [.aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨1, 1⟩]])) = true ∧
    stepLocals? (swapLocals flagsTy
      (.aggregate 0 [.aggregate 0 [.scalar ⟨1, 1⟩, .scalar ⟨1, 1⟩]])
      (.aggregate 0 [.aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨1, 1⟩]])) =
      .some [.init .unit,
        .init (.aggregate 0 [.aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨1, 1⟩]]),
        .init (.aggregate 0 [.aggregate 0 [.scalar ⟨1, 1⟩, .scalar ⟨1, 1⟩]])] ∧
    isUbNode (swapLocals nonNullU8Ty
      (.aggregate 0 [.scalar ⟨0, 8⟩]) (.aggregate 0 [.scalar ⟨4096, 8⟩])) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- 10(c): a non-pointer scalar whose bytes carry pointer provenance fails closed (a typed copy
would strip the provenance and leave address bits that have no concrete value here), an
uninitialized byte is still `.ub`, and pointer-typed bytes keep their provenance. -/
theorem typed_validity_scalar_provenance_fails_closed :
    let provByte : AbstractByte := .init 1 (.some (7, 7))
    let plainByte : AbstractByte := .init 1 .none
    validateTypedBytesProto 8 [] protoLayouts (.uint .u64) (List.replicate 8 provByte) = .unsupported ∧
    validateTypedBytesProto 8 [] protoLayouts (.uint .u64) (List.replicate 8 plainByte) = .valid ∧
    validateTypedBytesProto 8 [] protoLayouts (.uint .u64)
      (provByte :: List.replicate 7 .uninit) = .ub ∧
    validateTypedBytesProto 8 [] protoLayouts .bool [provByte] = .unsupported ∧
    validateTypedBytesProto 8 [] protoLayouts (.rawPtr .not (.uint .u8))
      (List.replicate 8 provByte) = .valid := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- 10(d): a decoded value is stored only if re-encoding it reproduces the written bytes.
- `abstractBytesRefineProto` accepts equal bytes and bytes demoted to `.uninit`, and rejects a
  changed value, a dropped provenance, and an `.uninit` promoted to an initialized byte;
- copying the 8 bytes of a pointer into a `u64` local (provenance cannot be kept by an integer
  slot) fails closed instead of storing the bare offset. -/
theorem commit_round_trip_guard :
    let a : AbstractByte := .init 5 .none
    let ap : AbstractByte := .init 5 (.some (3, 3))
    abstractBytesRefineProto [a, .uninit] [a, a] = true ∧
    abstractBytesRefineProto [a, a] [a, a] = true ∧
    abstractBytesRefineProto [a, a] [a, .uninit] = false ∧
    abstractBytesRefineProto [a] [ap] = false ∧
    abstractBytesRefineProto [.init 6 .none] [a] = false ∧
    (let decls := [mkDecl unitTy, mkDecl rawConstU32Ty, mkDecl u64Ty]
     let locals := [.uninit, .init (.ptr { allocId := 9, offsetBytes := 4 } 8), .init (.scalar ⟨0, 8⟩)]
     let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
     let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .unique }
     isUnsupportedNode
       (evalCopyProto (mkState locals [b1, b2]) (mkTarget "core::intrinsics::copy" [.uint .u8])
         decls protoLayouts []
         [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8, mkUsize 8]
         locals dstLocal0 (.some 1))) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def roGlobal : CapturedAllocation :=
  { allocId := 50, bytes := [.some 1, .some 2, .some 3, .none], relocations := [],
    align := ⟨1⟩, mutability := .not }
def rwGlobal : CapturedAllocation :=
  { allocId := 51, bytes := [.some 9, .some 9, .some 9, .some 9], relocations := [],
    align := ⟨1⟩, mutability := .mut }

def globalBytes? (n : MirStepNode) (idx : Nat) : Option (List (Option UInt8)) :=
  (stepState? n).bind (fun s' => (get? s'.memory.globals idx).map (fun g => g.bytes))

/-- 10(e): global allocations.
- `copy` from an immutable global into a stack array copies the bytes, including an
  uninitialized byte; an out-of-bounds source tail is `.ub`;
- `copy` into an immutable global is `.ub`; into a `static mut` it updates the allocation, also
  for an overlapping copy inside the same global (`memmove`);
- `compare_bytes` reads global bytes: equal prefix `0`, `<` `-1`; an uninitialized global byte
  at index 3 is `.ub` although byte 2 already differs, and so is an out-of-bounds tail
  (`bytes = 5` on 4-byte allocations) although byte 0 already differs. -/
theorem global_allocation_copy_and_compare :
    let decls := [mkDecl i32Ty, mkDecl arrU8x4Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU8 1, mkU8 2, mkU8 7, mkU8 4])]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [b1] [] [roGlobal, rwGlobal]
    let copyU8 := mkTarget "core::intrinsics::copy" [.uint .u8]
    let ro (o : Nat) : Value := .ptr { allocId := 50, offsetBytes := o } 8
    let rw (o : Nat) : Value := .ptr { allocId := 51, offsetBytes := o } 8
    let loc (o : Nat) : Value := .ptr { allocId := 1, offsetBytes := o } 8
    let copy (src dst : Value) (n : Nat) : MirStepNode :=
      evalCopyProto s copyU8 decls protoLayouts [] [src, dst, mkUsize n] locals dstLocal0 (.some 1)
    let cmp (l r : Value) (n : Nat) : MirStepNode :=
      evalCompareBytesProto s decls protoLayouts [l, r, mkUsize n] locals dstLocal0 (.some 1)
    let ret (n : MirStepNode) : Option LocalSlot := (stepLocals? n).bind (fun ls => get? ls 0)
    stepLocals? (copy (ro 0) (loc 1) 3) =
      .some [.init .unit, .init (.aggregate 0 [mkU8 1, mkU8 1, mkU8 2, mkU8 3])] ∧
    stepLocals? (copy (ro 2) (loc 0) 2) =
      .some [.init .unit, .init (.aggregate 0 [mkU8 3, .uninit, mkU8 7, mkU8 4])] ∧
    isUbNode (copy (ro 2) (loc 0) 3) = true ∧
    isUbNode (copy (loc 0) (ro 0) 2) = true ∧
    globalBytes? (copy (loc 0) (rw 1) 2) 1 = .some [.some 9, .some 1, .some 2, .some 9] ∧
    globalBytes? (copy (rw 0) (rw 1) 3) 1 = .some [.some 9, .some 9, .some 9, .some 9] ∧
    ret (cmp (ro 0) (loc 0) 2) = .some (.init (.scalar ⟨0, 4⟩)) ∧
    ret (cmp (ro 0) (loc 0) 3) = .some (.init (.scalar ⟨4294967295, 4⟩)) ∧
    isUbNode (cmp (loc 0) (ro 0) 4) = true ∧
    isUbNode (cmp (loc 0) (rw 0) 5) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 10(f): `typed_swap_nonoverlapping` is a typed copy, so the padding of each stored value is
uninitialized even in global allocations, which keep raw bytes. Two `static mut` `(u8, u32)`
globals with INITIALIZED padding bytes (`0xAA` / `0xBB` at offsets `1..3`):
- swapping them exchanges the fields and leaves padding uninitialized in both;
- swapping a global with a stack local stores the local's value with uninitialized padding;
- a global whose `u32` field has an uninitialized byte is an invalid value: `.ub`. -/
theorem typed_swap_resets_padding_in_global_allocations :
    let mkG (id : Nat) (bytes : List (Option UInt8)) : CapturedAllocation :=
      { allocId := id, bytes := bytes, relocations := [], align := ⟨4⟩, mutability := .mut }
    let gA := mkG 60 [.some 1, .some 170, .some 170, .some 170, .some 10, .some 0, .some 0, .some 0]
    let gB := mkG 61 [.some 2, .some 187, .some 187, .some 187, .some 20, .some 0, .some 0, .some 0]
    let gBad := mkG 62 [.some 2, .some 187, .some 187, .some 187, .some 20, .none, .some 0, .some 0]
    let decls := [mkDecl unitTy, mkDecl paddedPairTy]
    let locals := [.uninit, .init (.aggregate 0 [mkU8 7, mkU32 70])]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [b1] [] [gA, gB, gBad]
    let swap (x y : Nat) : MirStepNode :=
      evalTypedSwapNonOverlappingProto s
        (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [paddedPairTy.kind]) decls protoLayouts []
        [.ptr { allocId := x, offsetBytes := 0 } 8, .ptr { allocId := y, offsetBytes := 0 } 8]
        locals dstLocal0 (.some 1)
    globalBytes? (swap 60 61) 0 =
      .some [.some 2, .none, .none, .none, .some 20, .some 0, .some 0, .some 0] ∧
    globalBytes? (swap 60 61) 1 =
      .some [.some 1, .none, .none, .none, .some 10, .some 0, .some 0, .some 0] ∧
    globalBytes? (swap 60 1) 0 =
      .some [.some 7, .none, .none, .none, .some 70, .some 0, .some 0, .some 0] ∧
    stepLocals? (swap 60 1) = .some [.init .unit, .init (.aggregate 0 [mkU8 1, mkU32 10])] ∧
    isUbNode (swap 60 62) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- 10(g): a `MaybeUninit<[u8; 4]>` byte buffer keeps the bytes copied into it. After `copy`ing 4
initialized bytes from an array into the uninitialized union local:
- `compare_bytes` between the union and the source returns `0`;
- `copy`ing the union back into a second array reproduces `[1, 2, 3, 4]`.
The union's array-shaped payload has an exact byte image, so the round-trip guard accepts it. -/
theorem maybe_uninit_byte_buffer_round_trip :
    let decls := [mkDecl i32Ty, mkDecl arrU8x4Ty, mkDecl maybeUninitBufTy, mkDecl arrU8x4Ty]
    let src : Value := .aggregate 0 [mkU8 1, mkU8 2, mkU8 3, mkU8 4]
    let locals := [.uninit, .init src, .init (.aggregate 0 [.unit]),
      .init (.aggregate 0 [mkU8 0, mkU8 0, mkU8 0, mkU8 0])]
    let unique (n : Nat) : BorrowEntry :=
      { tag := n, targetLocal := n, targetProjection := [], perm := .unique }
    let s := mkState locals [unique 1, unique 2, unique 3]
    let copyU8 := mkTarget "core::intrinsics::copy" [.uint .u8]
    let p (tag : Nat) : Value := .ptr { allocId := tag, offsetBytes := 0 } 8
    let filled := evalCopyProto s copyU8 decls exactLayouts [] [p 1, p 2, mkUsize 4] locals dstLocal0 (.some 1)
    let compared := andThen filled (fun s' =>
      evalCompareBytesProto s' decls exactLayouts [p 2, p 1, mkUsize 4] s'.frame.locals dstLocal0 (.some 1))
    let copiedBack := andThen filled (fun s' =>
      evalCopyProto s' copyU8 decls exactLayouts [] [p 2, p 3, mkUsize 4] s'.frame.locals dstLocal0 (.some 1))
    (stepLocals? compared).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨0, 4⟩)) ∧
    (stepLocals? copiedBack).bind (fun ls => get? ls 3) = .some (.init src) := by
  refine ⟨rfl, rfl⟩

/-! ## Section 11: Dispatcher Coverage -/

/-- 11(a): for EVERY machine state, type arguments, operands, destination, and target,
`evalDirectRustIntrinsicProto?` routes each of the 8 canonical paths to its evaluator, and a
wrapper path (`core::ptr::copy`) is not an intrinsic (`.none`, an ordinary callee). -/
theorem dispatcher_routes_all_8_intrinsics
    (s : MachineState) (body : Option CapturedMir) (tys : List RigidTy)
    (decls : List LocalDecl) (layouts : LayoutTable) (argOps : List Operand) (argVals : List Value)
    (locals' : List LocalSlot) (dest : Place) (targetOpt : Option BasicBlockIdx) (unwind : UnwindAction) :
    evalDirectRustIntrinsicProto? s body (mkTarget "core::intrinsics::copy" tys) decls layouts argOps
        argVals locals' dest targetOpt unwind =
      .some (evalCopyProto s (mkTarget "core::intrinsics::copy" tys) decls layouts argOps argVals
        locals' dest targetOpt) ∧
    evalDirectRustIntrinsicProto? s body (mkTarget "core::intrinsics::compare_bytes" tys) decls layouts
        argOps argVals locals' dest targetOpt unwind =
      .some (evalCompareBytesProto s decls layouts argVals locals' dest targetOpt) ∧
    evalDirectRustIntrinsicProto? s body (mkTarget "core::intrinsics::raw_eq" tys) decls layouts argOps
        argVals locals' dest targetOpt unwind =
      .some (evalRawEqProto s (mkTarget "core::intrinsics::raw_eq" tys) decls layouts argOps argVals
        locals' dest targetOpt) ∧
    evalDirectRustIntrinsicProto? s body (mkTarget "core::intrinsics::typed_swap_nonoverlapping" tys)
        decls layouts argOps argVals locals' dest targetOpt unwind =
      .some (evalTypedSwapNonOverlappingProto s
        (mkTarget "core::intrinsics::typed_swap_nonoverlapping" tys) decls layouts argOps argVals
        locals' dest targetOpt) ∧
    evalDirectRustIntrinsicProto? s body (mkTarget "core::intrinsics::ptr_offset_from" tys) decls
        layouts argOps argVals locals' dest targetOpt unwind =
      .some (evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from" tys) decls layouts
        argOps argVals locals' dest targetOpt false) ∧
    evalDirectRustIntrinsicProto? s body (mkTarget "core::intrinsics::ptr_offset_from_unsigned" tys)
        decls layouts argOps argVals locals' dest targetOpt unwind =
      .some (evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from_unsigned" tys)
        decls layouts argOps argVals locals' dest targetOpt true) ∧
    evalDirectRustIntrinsicProto? s body (mkTarget "core::intrinsics::ptr_mask" tys) decls layouts
        argOps argVals locals' dest targetOpt unwind =
      .some (evalPtrMaskProto s decls layouts argVals locals' dest targetOpt) ∧
    evalDirectRustIntrinsicProto? s body (mkTarget "core::intrinsics::black_box" tys) decls layouts
        argOps argVals locals' dest targetOpt unwind =
      .some (evalBlackBoxProto s (mkTarget "core::intrinsics::black_box" tys) decls layouts argOps
        argVals locals' dest targetOpt) ∧
    evalDirectRustIntrinsicProto? s body (mkTarget "core::ptr::copy" tys) decls layouts argOps
        argVals locals' dest targetOpt unwind = .none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 11(b): end-to-end through the dispatcher: a `ptr_offset_from_unsigned` call returns `2`, an
existing base intrinsic (`core::intrinsics::wrapping_add`) is forwarded to
`Terminators.evalDirectRustIntrinsic?` unchanged, and a diverging call (`target = none`) to a
returning base intrinsic is `.ub`. -/
theorem dispatcher_end_to_end_and_base_passthrough :
    let decls := [mkDecl usizeTy, mkDecl arrU32x4Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 1, mkU32 2, mkU32 3, mkU32 4])]
    let b : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let s := mkState locals [b]
    let offs := evalDirectRustIntrinsicProto? s .none
      (mkTarget "core::intrinsics::ptr_offset_from_unsigned" [.uint .u32]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 12 } 8, .ptr { allocId := 1, offsetBytes := 4 } 8]
      locals dstLocal0 (.some 1) .continue_
    let addTarget := mkTarget "core::intrinsics::wrapping_add" [.uint .u32]
    let addArgs := [mkU32 4294967295, mkU32 2]
    (offs.bind stepLocals?).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨2, 8⟩)) ∧
    evalDirectRustIntrinsicProto? s .none addTarget decls protoLayouts [] addArgs locals dstLocal0
        (.some 1) .continue_ =
      evalDirectRustIntrinsic? s .none addTarget decls protoLayouts [] addArgs locals dstLocal0 1
        .continue_ ∧
    (evalDirectRustIntrinsicProto? s .none addTarget decls protoLayouts [] addArgs locals dstLocal0
        .none .continue_).map isUbNode = .some true := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## Section 12: `MiniRustSpec.Interp` Agreement Theorems -/

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


/-- Observation of a `MiniRustSpec` `PtrOffsetFrom` outcome: `some (some d)` for the byte
distance `d`, `some none` for UB, `none` for anything else. -/
def mrOffsetObs : Interp (Val × Gen.Type) → Option (Option Int)
  | .ok (.Int d, _) => .some (.some d)
  | .error (.ub _) => .some .none
  | _ => .none

/-- Observation of a `MiniRustSpec` `RawEq` outcome, in the same shape. -/
def mrBoolObs : Interp (Val × Mach) → Option (Option Bool)
  | .ok (.Bool b, _) => .some (.some b)
  | .error (.ub _) => .some .none
  | _ => .none

/-- Observation of a prototype step whose destination `_0` receives a `ptrBytes = 8` signed
integer: `some (some d)` for the two's-complement value `d`, `some none` for UB. -/
def protoIsizeObs (n : MirStepNode) : Option (Option Int) :=
  match isUbNode n with
  | true => .some .none
  | false =>
    match (stepLocals? n).bind (fun ls => get? ls 0) with
    | .some (.init (.scalar sc)) =>
      match Nat.blt sc.bits 9223372036854775808 with
      | true => .some (.some (Int.ofNat sc.bits))
      | false => .some (.some (Int.ofNat sc.bits - 18446744073709551616))
    | _ => .none

/-- Observation of a prototype step whose destination `_0` receives a `bool`. -/
def protoBoolObs (n : MirStepNode) : Option (Option Bool) :=
  match isUbNode n with
  | true => .some .none
  | false =>
    match (stepLocals? n).bind (fun ls => get? ls 0) with
    | .some (.init (.scalar sc)) => .some (.some (Nat.beq sc.bits 1))
    | _ => .none

/--
**`MiniRustSpec.Interp` Agreement Theorem (`ptr_offset_from` / `ptr_offset_from_unsigned`)**:
the SAME scenario is run in both semantics and the two observations are equal.

`MiniRustSpec`: three 16-byte allocations (alloc 0 at `0x1000` and alloc 1 at `0x2000` live,
alloc 2 at `0x3000` dead). Prototype: `[u32; 4]` locals `_1` (tag 1), `_2` (tag 2) live and `_3`
(tag 3) dead, with pointee `u8` so both report a byte distance.

1. `+8` bytes; 2. `-8` bytes; 3. unsigned underflow (UB); 4. cross-allocation (UB);
5. equal provenance-free addresses (`0`); 6. unequal provenance-free addresses (UB);
7. one-past-the-end (`16`); 8. out-of-bounds endpoint at non-zero distance (UB);
9. the same dangling pointer into the dead allocation (`0`: zero-sized checks pass in both);
10. two different offsets into the dead allocation (UB).
-/
theorem minirust_ptr_offset_from_agreement :
    let mk (addr : Nat) (live : Bool) : Gen.Allocation Unit Unit :=
      { data := List.replicate 16 (.Init 0 none), addr := addr, align := ⟨4⟩, kind := .Stack,
        live := live, extra := () }
    let m := mkMiniRustMach [mk 4096 true, mk 8192 true, mk 12288 false]
    let mp (alloc off : Nat) : Val × Gen.Type :=
      (.Ptr ⟨⟨4096 * (alloc + 1) + off, some (⟨alloc⟩, ())⟩, none⟩, mrRawPtrTy)
    let mi (addr : Nat) : Val × Gen.Type := (.Ptr ⟨⟨addr, none⟩, none⟩, mrRawPtrTy)
    let decls := [mkDecl isizeTy, mkDecl arrU32x4Ty, mkDecl arrU32x4Ty, mkDecl arrU32x4Ty]
    let arr : LocalSlot := .init (.aggregate 0 [mkU32 0, mkU32 0, mkU32 0, mkU32 0])
    let locals := [.uninit, arr, arr, .dead]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let b2 : BorrowEntry := { tag := 2, targetLocal := 2, targetProjection := [], perm := .frozen }
    let b3 : BorrowEntry :=
      { tag := 3, targetLocal := 3, targetProjection := [], perm := .frozen, allocDead := true }
    let s := mkState locals [b1, b2, b3]
    let pp (tag off : Nat) : Value := .ptr { allocId := tag, offsetBytes := off } 8
    let proto (unsigned : Bool) (a b : Value) : Option (Option Int) :=
      protoIsizeObs (evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from" [.uint .u8])
        decls protoLayouts [] [a, b] locals dstLocal0 (.some 1) unsigned)
    let mr (nonneg : Bool) (a b : Val × Gen.Type) : Option (Option Int) :=
      mrOffsetObs (evalPtrOffsetFrom m true nonneg a b)
    (mr false (mp 0 12) (mp 0 4) = proto false (pp 1 12) (pp 1 4) ∧
      proto false (pp 1 12) (pp 1 4) = .some (.some 8)) ∧
    (mr false (mp 0 4) (mp 0 12) = proto false (pp 1 4) (pp 1 12) ∧
      proto false (pp 1 4) (pp 1 12) = .some (.some (-8))) ∧
    (mr true (mp 0 4) (mp 0 12) = proto true (pp 1 4) (pp 1 12) ∧
      proto true (pp 1 4) (pp 1 12) = .some .none) ∧
    (mr false (mp 0 4) (mp 1 0) = proto false (pp 1 4) (pp 2 0) ∧
      proto false (pp 1 4) (pp 2 0) = .some .none) ∧
    (mr false (mi 4096) (mi 4096) = proto false (mkUsize 4096) (mkUsize 4096) ∧
      proto false (mkUsize 4096) (mkUsize 4096) = .some (.some 0)) ∧
    (mr false (mi 4100) (mi 4096) = proto false (mkUsize 4100) (mkUsize 4096) ∧
      proto false (mkUsize 4100) (mkUsize 4096) = .some .none) ∧
    (mr true (mp 0 16) (mp 0 0) = proto true (pp 1 16) (pp 1 0) ∧
      proto true (pp 1 16) (pp 1 0) = .some (.some 16)) ∧
    (mr false (mp 0 20) (mp 0 0) = proto false (pp 1 20) (pp 1 0) ∧
      proto false (pp 1 20) (pp 1 0) = .some .none) ∧
    (mr false (mp 2 8) (mp 2 8) = proto false (pp 3 8) (pp 3 8) ∧
      proto false (pp 3 8) (pp 3 8) = .some (.some 0)) ∧
    (mr false (mp 2 8) (mp 2 4) = proto false (pp 3 8) (pp 3 4) ∧
      proto false (pp 3 8) (pp 3 4) = .some .none) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/--
**`MiniRustSpec.Interp` Agreement Theorem (`raw_eq`)**: the SAME scenario is run in both
semantics and the two observations are equal.

1. equal initialized `u32` values (`true`); 2. unequal initialized `u32` values (`false`);
3. a `(u8, u32)` struct with uninitialized padding bytes `1..3` and equal fields (UB);
4. a ZST (`true`).
-/
theorem minirust_raw_eq_agreement :
    let mk (addr : Nat) (data : List Byte) : Gen.Allocation Unit Unit :=
      { data := data, addr := addr, align := ⟨4⟩, kind := .Stack, live := true, extra := () }
    let paddedBytes : List Byte :=
      [.Init 7 none, .Uninit, .Uninit, .Uninit, .Init 42 none, .Init 0 none, .Init 0 none, .Init 0 none]
    let m := mkMiniRustMach
      [mk 4096 (mrInitBytes [42, 0, 0, 0]), mk 4100 (mrInitBytes [42, 0, 0, 0]),
       mk 4104 (mrInitBytes [99, 0, 0, 0]), mk 4112 paddedBytes, mk 4120 paddedBytes]
    let mp (alloc addr : Nat) : Val := .Ptr ⟨⟨addr, some (⟨alloc⟩, ())⟩, none⟩
    let mZst : Val := .Ptr ⟨⟨1, none⟩, none⟩
    let mr (ty : Gen.Type) (a b : Val) : Option (Option Bool) :=
      mrBoolObs (evalIntrinsic m .RawEq [(a, ty), (b, ty)] .Bool)
    let decls := [mkDecl boolTy, mkDecl u32Ty, mkDecl u32Ty, mkDecl u32Ty, mkDecl paddedPairTy,
      mkDecl paddedPairTy]
    let locals := [.uninit, .init (mkU32 42), .init (mkU32 42), .init (mkU32 99),
      .init (.aggregate 0 [mkU8 7, mkU32 42]), .init (.aggregate 0 [mkU8 7, mkU32 42])]
    let frozen (n : Nat) : BorrowEntry :=
      { tag := n, targetLocal := n, targetProjection := [], perm := .frozen }
    let s := mkState locals [frozen 1, frozen 2, frozen 3, frozen 4, frozen 5]
    let pp (tag : Nat) : Value := .ptr { allocId := tag, offsetBytes := 0 } 8
    let proto (ty : RigidTy) (a b : Value) : Option (Option Bool) :=
      protoBoolObs (evalRawEqProto s (mkTarget "core::intrinsics::raw_eq" [ty]) decls protoLayouts []
        [a, b] locals dstLocal0 (.some 1))
    (mr mrRefU32Ty (mp 0 4096) (mp 1 4100) = proto (.uint .u32) (pp 1) (pp 2) ∧
      proto (.uint .u32) (pp 1) (pp 2) = .some (.some true)) ∧
    (mr mrRefU32Ty (mp 0 4096) (mp 2 4104) = proto (.uint .u32) (pp 1) (pp 3) ∧
      proto (.uint .u32) (pp 1) (pp 3) = .some (.some false)) ∧
    (mr mrRefPaddedTy (mp 3 4112) (mp 4 4120) = proto paddedPairTy.kind (pp 4) (pp 5) ∧
      proto paddedPairTy.kind (pp 4) (pp 5) = .some .none) ∧
    (mr mrRefZstTy mZst mZst = proto (.tuple .nil) (mkUsize 1) (mkUsize 1) ∧
      proto (.tuple .nil) (mkUsize 1) (mkUsize 1) = .some (.some true)) := by
  refine ⟨⟨by decide +kernel, rfl⟩, ⟨by decide +kernel, rfl⟩, ⟨by decide +kernel, rfl⟩,
    ⟨by decide +kernel, rfl⟩⟩

end MiniRustDualAlignment

/-! ## Section 13: Non-Vacuity Witnesses & Mechanical Standard-Axiom Gate -/

/--
Non-vacuity witness instantiating EVERY universally quantified theorem in
`Anneal.TcbCoreMemPtrIntrinsicsPrototype` with concrete, satisfiable inputs:
1. `compareUnsignedBytesProto_eq_miriBytesCompareSpec` on `[0x80]` vs `[0x7f]`;
2. `ptrMask_baseAddr_invariant` on 64-bit `m = 3` (`align = 8`), `baseAddr = 0x10000`, `relOff = 13`, `mask = !7`;
3. `evalPtrMaskValueProto_preserves_provenance` and `evalPtrMaskValueProto_symbolic_eq_concrete`
   on concrete stack borrow tag `7` with `baseAddr = 0x10000` and `baseAddr = 0x20008`!
4. `evalPtrOffsetFromDistanceProto_zst_ub`, `_unsigned_underflow_ub`, `_isizeMin_ub`;
5. `evalBlackBoxProto_valid_direct_dest` on `u32 = 42`;
6. the `lean-miri` mirror theorems `evalPtrOffsetFromDistanceProto_eq_miriSpec`,
   `miriPtrOffsetFromDistanceSpec_eq_checkedDistanceProto`, and
   `ptrOffsetFromExactDivProto_eq_miriSpec` on 64-bit offsets `4` and `12` over `u32`
   (`-8` bytes, `-2` elements), with the mirror itself evaluated on the `isize::MIN`, unsigned
   underflow, inexact-division, and ZST cases so its UB branches are reachable;
7. `evalPtrOffsetFromDistanceProto_same_offset`, `resolvePtrOffsetFromOffsetsProto_same_pointer`
   (on a dead-allocation pointer), and `abstractBytesRefineProto_refl`.
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
        memory := emptyMemory }) ∧
    (evalPtrOffsetFromDistanceProto 4 12 4 8 false =
      (match miriPtrOffsetFromDistanceSpec 4 12 (scalarModulus 8) false with
       | .none => .none
       | .some distance => miriPtrOffsetFromExactDivSpec distance 4 8)) ∧
    (miriPtrOffsetFromDistanceSpec 4 12 (scalarModulus 8) false =
      ptrOffsetFromCheckedDistanceProto 4 12 8 false) ∧
    (ptrOffsetFromExactDivProto (-8) 4 8 false = miriPtrOffsetFromExactDivSpec (-8) 4 8) ∧
    (miriPtrOffsetFromDistanceSpec 4 12 (scalarModulus 8) false = .some (-8)) ∧
    (miriPtrOffsetFromExactDivSpec (-8) 4 8 = .some ⟨18446744073709551614, 8⟩) ∧
    (miriPtrOffsetFromDistanceSpec 0 9223372036854775808 (scalarModulus 8) false = .none) ∧
    (miriPtrOffsetFromDistanceSpec 4 12 (scalarModulus 8) true = .none) ∧
    (miriPtrOffsetFromExactDivSpec 6 4 8 = .none) ∧
    (miriPtrOffsetFromExactDivSpec 0 0 8 = .none) ∧
    (evalPtrOffsetFromDistanceProto 400 400 4 8 true = .some ⟨0, 8⟩) ∧
    (∃ off,
      resolvePtrOffsetFromOffsetsProto
        (mkState [.uninit, .dead]
          [{ tag := 3, targetLocal := 1, targetProjection := [], perm := .frozen, allocDead := true }])
        [.uninit, .dead] [mkDecl isizeTy, mkDecl arrU32x4Ty] protoLayouts
        (.prov { allocId := 3, offsetBytes := 8 }) (.prov { allocId := 3, offsetBytes := 8 }) =
        .ok (off, off)) ∧
    (abstractBytesRefineProto [.init 5 (.some (3, 3)), .uninit] [.init 5 (.some (3, 3)), .uninit] =
      true) := by
  refine ⟨compareUnsignedBytesProto_eq_miriBytesCompareSpec [128] [127], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
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
  · exact evalPtrOffsetFromDistanceProto_eq_miriSpec 4 12 4 8 false (by decide) (by decide) (by decide)
  · exact miriPtrOffsetFromDistanceSpec_eq_checkedDistanceProto 4 12 8 false
      (by decide) (by decide) (by decide)
  · exact ptrOffsetFromExactDivProto_eq_miriSpec (-8) 4 8 false (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact evalPtrOffsetFromDistanceProto_same_offset 400 4 8 true (by decide)
  · exact resolvePtrOffsetFromOffsetsProto_same_pointer _ _ _ _ _
  · exact abstractBytesRefineProto_refl _

/-- Aggregate conjunction linking every prototype and test theorem for axiom auditing. -/
theorem all_proto_and_test_theorems :
    (classifyRustIntrinsicProto? "core::intrinsics::copy" = .some .copy) ∧
    (∀ xs ys, compareUnsignedBytesProto xs ys = miriBytesCompareSpec xs ys) ∧
    (∀ W m baseAddr relOff mask,
      baseAddr % 2 ^ m = 0 → mask < 2 ^ W → (2 ^ W - 1) - mask < 2 ^ m →
      baseAddr + relOff < 2 ^ W →
      bitwiseAndBits W (baseAddr + relOff) mask = baseAddr + bitwiseAndBits W relOff mask) ∧
    (∀ aOff bOff elemSize ptrBytes unsigned,
      0 < ptrBytes → aOff < scalarModulus ptrBytes → bOff < scalarModulus ptrBytes →
      evalPtrOffsetFromDistanceProto aOff bOff elemSize ptrBytes unsigned =
        (match miriPtrOffsetFromDistanceSpec aOff bOff (scalarModulus ptrBytes) unsigned with
         | .none => .none
         | .some distance => miriPtrOffsetFromExactDivSpec distance elemSize ptrBytes)) ∧
    True := by
  have _ := classify_all_8_core_intrinsics
  have _ := classify_preserves_existing_and_rejects_wrappers
  have _ := copy_nonoverlapping_u32_array
  have _ := copy_preserves_ptr_provenance_and_tag
  have _ := copy_preserves_uninit_maybe_uninit
  have _ := copy_overlapping_forward_shift
  have _ := copy_overlapping_backward_shift
  have _ := copy_self_identical_succeeds
  have _ := copy_zero_count_alignment_checked_validity_not_required
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
  have _ := zero_size_null_matrix
  have _ := ptr_offset_from_same_address_needs_no_liveness_or_bounds
  have _ := byte_image_of_nested_padded_struct_is_exact
  have _ := typed_swap_validity_follows_layout_not_generic_args
  have _ := typed_validity_scalar_provenance_fails_closed
  have _ := commit_round_trip_guard
  have _ := global_allocation_copy_and_compare
  have _ := typed_swap_resets_padding_in_global_allocations
  have _ := maybe_uninit_byte_buffer_round_trip
  have _ := dispatcher_routes_all_8_intrinsics
  have _ := dispatcher_end_to_end_and_base_passthrough
  have _ := minirust_ptr_offset_from_agreement
  have _ := minirust_raw_eq_agreement
  have _ := non_vacuity_all_quantified_theorems
  exact ⟨rfl, compareUnsignedBytesProto_eq_miriBytesCompareSpec, ptrMask_baseAddr_invariant,
    evalPtrOffsetFromDistanceProto_eq_miriSpec, trivial⟩

section MechanicalAxiomAudit

open Lean Elab Command

/--
Mechanical standard-axiom and safety audit: fails compilation unless EVERY
declaration in `Anneal.TcbCoreMemPtrIntrinsicsPrototype` AND EVERY declaration
of this test module (definitions, theorems, and their auxiliary constants) is
`!isUnsafe` and depends strictly on Lean's standard axioms
`{propext, Classical.choice, Quot.sound}` (zero `sorryAx`, zero
`Lean.ofReduceBool` / `native_decide`, zero custom axioms).

The explicit theorem list must be COMPLETE: the audit enumerates the theorems
declared directly in `Anneal.TcbCoreMemPtrIntrinsicsProtoTests` and fails if any
of them is missing from the list, so a test theorem cannot escape the audit by
being left out.
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
  -- Every constant declared in this test module (not only the listed theorems).
  let testNs := `Anneal.TcbCoreMemPtrIntrinsicsProtoTests
  let localConsts : Array (Name × ConstantInfo) :=
    env.constants.map₂.foldl (init := #[]) fun acc n ci => acc.push (n, ci)
  let mut localTheorems : Nat := 0
  for (n, ci) in localConsts do
    if ci.isUnsafe then
      throwError "[PROTO-AXIOM-AUDIT] unsafe test-module declaration {n}"
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "[PROTO-AXIOM-AUDIT] test-module declaration {n} depends on non-standard axiom {a}"
      unless union.contains a do
        union := union.push a
    if let .thmInfo _ := ci then
      if n.getPrefix == testNs && !n.isInternalDetail then
        localTheorems := localTheorems + 1
        unless seen.contains n do
          throwError "[PROTO-AXIOM-AUDIT] test theorem {n} is missing from the audit list"
  unless localTheorems == ids.size do
    throwError "[PROTO-AXIOM-AUDIT] audit list has {ids.size} entries but the module declares {localTheorems} test theorems"
  logInfo m!"[PROTO-AXIOM-AUDIT] proto_decls={protoConsts.size} test_theorems={ids.size} test_module_decls={localConsts.size} axioms={union.toList} unsafe_free=true sorry_free=true list_complete=true ok=true"

#assert_proto_standard_axioms
  classify_all_8_core_intrinsics
  classify_preserves_existing_and_rejects_wrappers
  copy_nonoverlapping_u32_array
  copy_preserves_ptr_provenance_and_tag
  copy_preserves_uninit_maybe_uninit
  copy_overlapping_forward_shift
  copy_overlapping_backward_shift
  copy_self_identical_succeeds
  copy_zero_count_alignment_checked_validity_not_required
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
  zero_size_null_matrix
  ptr_offset_from_same_address_needs_no_liveness_or_bounds
  byte_image_of_nested_padded_struct_is_exact
  typed_swap_validity_follows_layout_not_generic_args
  typed_validity_scalar_provenance_fails_closed
  commit_round_trip_guard
  global_allocation_copy_and_compare
  typed_swap_resets_padding_in_global_allocations
  maybe_uninit_byte_buffer_round_trip
  dispatcher_routes_all_8_intrinsics
  dispatcher_end_to_end_and_base_passthrough
  minirust_ptr_offset_from_agreement
  minirust_raw_eq_agreement
  non_vacuity_all_quantified_theorems
  all_proto_and_test_theorems

end MechanicalAxiomAudit

end Anneal.TcbCoreMemPtrIntrinsicsProtoTests
