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

/-- `protoLayouts` with the `MaybeUninit<u32>` entry (idx 2) carrying its compiler
`fieldLayouts := [6, 0]` (fields `()` at idx 6 and `u32` at idx 0) alongside the
scalar-union ABI. Every byte of `u32` is a data byte, so a typed copy preserves
all four bytes without relying on an unsound field-layout-less `.scalar (.union _)` guess. -/
def unionAbiLayouts : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      protoLayouts.entries.take 2 ++
      [ { size := ⟨4⟩, align := ⟨4⟩,
          fields := .union 2,
          variants := .single 0,
          backendRepr := .scalar (.union (.int 32 false)),
          fieldLayouts := [6, 0],
          isUninhabited := false } ] ++
      protoLayouts.entries.drop 3 ++
      [ -- idx 6: `()` (size 0, align 1)
        { size := ⟨0⟩, align := ⟨1⟩,
          fields := .arbitrary [] [],
          variants := .single 0,
          backendRepr := .memory,
          isUninhabited := false } ] }
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
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [maybeUninitU32Ty.kind]) declsMu unionAbiLayouts []
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
- `(second = 1, first = 2)` swaps cleanly and round-trips via `decodeValueAtLayoutIdxProto`
  (not merely non-UB);
- a `bool = 2` inside an array field (`Flags { bits: [bool; 2] }`) is `.ub`, and valid flags swap;
- a null pointer in a non-null pointer field (`NonNullU8`) is `.ub`, while valid provenance
  pointers swap preserving `allocId`/`offsetBytes`. -/
theorem typed_swap_validity_follows_layout_not_generic_args :
    let pA : ProvenancePtr := { allocId := 11, offsetBytes := 4 }
    let pB : ProvenancePtr := { allocId := 22, offsetBytes := 8 }
    isUbNode (swapLocals twoU8BoolTy
      (.aggregate 0 [.scalar ⟨2, 1⟩, mkU8 1]) (.aggregate 0 [.scalar ⟨1, 1⟩, mkU8 9])) = true ∧
    stepLocals? (swapLocals twoU8BoolTy
      (.aggregate 0 [.scalar ⟨1, 1⟩, mkU8 2]) (.aggregate 0 [.scalar ⟨0, 1⟩, mkU8 9])) =
      .some [.init .unit,
        .init (.aggregate 0 [.scalar ⟨0, 1⟩, mkU8 9]),
        .init (.aggregate 0 [.scalar ⟨1, 1⟩, mkU8 2])] ∧
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
      (.aggregate 0 [.scalar ⟨0, 8⟩]) (.aggregate 0 [.scalar ⟨4096, 8⟩])) = true ∧
    stepLocals? (swapLocals nonNullU8Ty
      (.aggregate 0 [.ptr pA 8]) (.aggregate 0 [.ptr pB 8])) =
      .some [.init .unit,
        .init (.aggregate 0 [.ptr pB 8]),
        .init (.aggregate 0 [.ptr pA 8])] ∧
    stepLocals? (swapLocals outerTy
      (.aggregate 0 [.aggregate 0 [mkU8 1, mkU32 10]])
      (.aggregate 0 [.aggregate 0 [mkU8 2, mkU32 20]])) =
      .some [.init .unit,
        .init (.aggregate 0 [.aggregate 0 [mkU8 2, mkU32 20]]),
        .init (.aggregate 0 [.aggregate 0 [mkU8 1, mkU32 10]])] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-! ## Section 13: Pass A1 Soundness Hardening & Regression Witnesses -/

/-- 13(a): Ranged borrows (`split_at_mut`-style disjoint byte slices) do NOT over-invalidate
disjoint siblings when accessing a sub-range `[accessOff, accessOff + accessLen)`:
- root borrow tag `1` spans `[0, 16)`, protected sibling tag `2` spans `[8, 16)`;
- `copy` / `compare_bytes` / `typed_swap_nonoverlapping` on `[0, 4)` (or `[0, 4)` vs `[4, 8)`)
  through tag `1` SUCCEEDS without tripping the protector on `[8, 16)`;
- accessing `[4, 12)` (overlapping `[8, 16)`) STILL faults `.ub`! -/
theorem ranged_borrow_split_at_mut_no_over_invalidation :
    let decls := [mkDecl unitTy, mkDecl arrU32x4Ty]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 10, mkU32 20, mkU32 30, mkU32 40])]
    let bRoot : BorrowEntry :=
      { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique,
        rangeOffset := 0, rangeLen := 16 }
    let bRightProt : BorrowEntry :=
      { tag := 2, targetLocal := 1, targetProjection := [], perm := .unique,
        protector := .some 99, rangeOffset := 8, rangeLen := 8 }
    let s := mkState locals [bRoot, bRightProt] [99]
    let p (o : Nat) : Value := .ptr { allocId := 1, offsetBytes := o } 8
    let rCopyDisjoint := evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u32])
      decls protoLayouts [] [p 0, p 4, mkUsize 1] locals dstLocal0 (.some 1)
    let rSwapDisjoint := evalTypedSwapNonOverlappingProto s
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [.uint .u32])
      decls protoLayouts [] [p 0, p 4] locals dstLocal0 (.some 1)
    let rCmpDisjoint := evalCompareBytesProto s decls protoLayouts [p 0, p 4, mkUsize 4]
      locals dstLocal0 (.some 1)
    let rCopyOverlapProt := evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u32])
      decls protoLayouts [] [p 0, p 4, mkUsize 2] locals dstLocal0 (.some 1)
    stepLocals? rCopyDisjoint =
      .some [.init .unit, .init (.aggregate 0 [mkU32 10, mkU32 10, mkU32 30, mkU32 40])] ∧
    stepLocals? rSwapDisjoint =
      .some [.init .unit, .init (.aggregate 0 [mkU32 20, mkU32 10, mkU32 30, mkU32 40])] ∧
    (stepLocals? rCmpDisjoint).bind (fun ls => get? ls 0) =
      .some (.init (.scalar ⟨4294967295, 4⟩)) ∧
    isUbNode rCopyOverlapProt = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- 13(b): `typed_swap_nonoverlapping` resets padding bytes on **stack byte-buffer locals**
(`#[repr(C, align(4))] struct AlignedBytes16([u8; 16])`) as well as globals, faults `.ub` on an
under-aligned `[u8; 16]` (align 1) local, AND supports `MaybeUninit<u32>` in mutable global
allocations:
- swapping two `(u8, u32)` values inside a 4-byte-aligned stack byte buffer whose padding bytes
  `1..3` and `9..11` were initialized (`0xAA`/`0xBB`) resets bytes `1..3` and `9..11` to
  `Value.uninit`, so a subsequent `compare_bytes` reading byte `1` faults `.ub`;
- swapping two `(u8, u32)` values inside a plain `[u8; 16]` (align 1) faults `.ub` (known
  symbolic alignment `1 < 4`, matching Miri `-Zmiri-symbolic-alignment-check`);
- swapping two `MaybeUninit<u32>` global allocations containing `.uninit` bytes SUCCEEDS and
  exchanges their exact raw byte masks. -/
theorem typed_swap_resets_padding_in_stack_byte_buffer_and_union_global :
    let bufLayouts : LayoutTable :=
      { pointerBits := 64
        isLittleEndian := true
        entries :=
          protoLayouts.entries ++
          [ -- idx 6: `[u8; 16]` (size 16, align 1, array of u8 at idx 3)
            { size := ⟨16⟩, align := ⟨1⟩, fields := .array ⟨1⟩ 16, variants := .single 0,
              backendRepr := .memory, fieldLayouts := [3], isUninhabited := false },
            -- idx 7: `#[repr(C, align(4))] struct AlignedBytes16([u8; 16])` (size 16, align 4)
            { size := ⟨16⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩] [0], variants := .single 0,
              backendRepr := .memory, fieldLayouts := [6], isUninhabited := false } ] }
    let alignedBytes16Ty : Ty := { kind := .adt "tests::AlignedBytes16" .nil, layoutIdx := 7 }
    let unalignedBytes16Ty : Ty := { kind := .array (.uint .u8) 16, layoutIdx := 6 }
    let decls := [mkDecl unitTy, mkDecl alignedBytes16Ty, mkDecl paddedPairTy]
    let declsUnaligned := [mkDecl unitTy, mkDecl unalignedBytes16Ty, mkDecl paddedPairTy]
    let initBytes : List Value :=
      [mkU8 1, mkU8 170, mkU8 170, mkU8 170, mkU8 10, mkU8 0, mkU8 0, mkU8 0,
       mkU8 2, mkU8 187, mkU8 187, mkU8 187, mkU8 20, mkU8 0, mkU8 0, mkU8 0]
    let locals := [.uninit, .init (.aggregate 0 [.aggregate 0 initBytes]), .uninit]
    let localsUnaligned := [.uninit, .init (.aggregate 0 initBytes), .uninit]
    let b1 : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [b1]
    let p (o : Nat) : Value := .ptr { allocId := 1, offsetBytes := o } 8
    let swapped := evalTypedSwapNonOverlappingProto s
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [paddedPairTy.kind])
      decls bufLayouts [] [p 0, p 8] locals dstLocal0 (.some 1)
    let cmpPadAfter := andThen swapped (fun s' =>
      evalCompareBytesProto s' decls bufLayouts [p 0, p 8, mkUsize 2] s'.frame.locals dstLocal0 (.some 1))
    let rUnderAligned := evalTypedSwapNonOverlappingProto (mkState localsUnaligned [b1])
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [paddedPairTy.kind])
      declsUnaligned bufLayouts [] [p 0, p 8] localsUnaligned dstLocal0 (.some 1)
    let expectedBytes : List Value :=
      [mkU8 2, .uninit, .uninit, .uninit, mkU8 20, mkU8 0, mkU8 0, mkU8 0,
       mkU8 1, .uninit, .uninit, .uninit, mkU8 10, mkU8 0, mkU8 0, mkU8 0]
    -- Union (`MaybeUninit<u32>`) in global allocations:
    let gMu1 : CapturedAllocation :=
      { allocId := 70, bytes := [.some 7, .none, .some 9, .none], relocations := [], align := ⟨4⟩, mutability := .mut }
    let gMu2 : CapturedAllocation :=
      { allocId := 71, bytes := [.none, .some 3, .none, .some 5], relocations := [], align := ⟨4⟩, mutability := .mut }
    let declsMu := [mkDecl unitTy, mkDecl maybeUninitU32Ty]
    let sMu := mkState [.uninit, .uninit] [] [] [gMu1, gMu2]
    let rMuGlobal := evalTypedSwapNonOverlappingProto sMu
      (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [maybeUninitU32Ty.kind])
      declsMu unionAbiLayouts []
      [.ptr { allocId := 70, offsetBytes := 0 } 8, .ptr { allocId := 71, offsetBytes := 0 } 8]
      [.uninit, .uninit] dstLocal0 (.some 1)
    stepLocals? swapped = .some [.init .unit, .init (.aggregate 0 [.aggregate 0 expectedBytes]), .uninit] ∧
    isUbNode cmpPadAfter = true ∧
    isUbNode rUnderAligned = true ∧
    globalBytes? rMuGlobal 0 = .some [.none, .some 3, .none, .some 5] ∧
    globalBytes? rMuGlobal 1 = .some [.some 7, .none, .some 9, .none] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- 13(c): `black_box` nested validity & fail-closed guarantees:
- `[MaybeUninit<u8>; 2]` and `(u32, MaybeUninit<u32>)` containing `.uninit` inside the union
  SUCCEED (previously false UB from recursive `valueContainsUninit`);
- `(bool=2, u32)`, `[bool=2; 2]`, null wide `&[u8]`, null `fn()`, `Two<u8, bool>` with invalid
  `bool = 2`, and `NonNullU8` with null pointer ALL fault `.ub`;
- valid wide `&[u8]`, valid `fn()`, and valid `Two<u8, bool>` SUCCEED;
- pointer value at `u64`, unsized `[u8]`, and missing type `tyOpt = .none` fail closed `.unsupported`. -/
theorem black_box_nested_maybeuninit_wide_ref_fnptr_and_adt_validity :
    let arrMuTy : RigidTy := .array maybeUninitU32Ty.kind 2
    let pairMuTy : RigidTy := .tuple [.uint .u32, maybeUninitU32Ty.kind]
    let wideRefU8Ty : RigidTy := .ref .not (.slice (.uint .u8))
    let fnPtrTy : RigidTy := .fnPtr .nil (.tuple .nil) .safe .rust
    let s0 := mkState [.uninit]
    let bb (decls : List LocalDecl) (layouts : LayoutTable) (ty : RigidTy) (v : Value) : MirStepNode :=
      evalBlackBoxProto s0 (mkTarget "core::intrinsics::black_box" [ty]) decls layouts [] [v]
        [.uninit] dstLocal0 (.some 1)
    let arrMuVal : Value := .aggregate 0 [.aggregate 0 [.uninit], .aggregate 0 [mkU32 7]]
    let pairMuVal : Value := .aggregate 0 [mkU32 9, .aggregate 0 [.uninit]]
    let declsMu := [mkDecl unitTy, mkDecl maybeUninitU32Ty]
    let declsExact := [mkDecl unitTy, mkDecl twoU8BoolTy, mkDecl nonNullU8Ty]
    stepLocals? (bb declsMu protoLayouts arrMuTy arrMuVal) = .some [.init arrMuVal] ∧
    stepLocals? (bb declsMu protoLayouts pairMuTy pairMuVal) = .some [.init pairMuVal] ∧
    isUbNode (bb [mkDecl unitTy] protoLayouts (.tuple [.bool, .uint .u32])
      (.aggregate 0 [.scalar ⟨2, 1⟩, mkU32 1])) = true ∧
    isUbNode (bb [mkDecl unitTy] protoLayouts (.array .bool 2)
      (.aggregate 0 [.scalar ⟨1, 1⟩, .scalar ⟨2, 1⟩])) = true ∧
    isUbNode (bb [mkDecl unitTy] protoLayouts wideRefU8Ty
      (.aggregate 0 [mkUsize 0, mkUsize 4])) = true ∧
    stepLocals? (bb [mkDecl unitTy] protoLayouts wideRefU8Ty
      (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0 } 8, mkUsize 4])) =
      .some [.init (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0 } 8, mkUsize 4])] ∧
    isUbNode (bb [mkDecl unitTy] protoLayouts fnPtrTy (mkUsize 0)) = true ∧
    stepLocals? (bb [mkDecl unitTy] protoLayouts fnPtrTy (mkUsize 4096)) =
      .some [.init (mkUsize 4096)] ∧
    isUbNode (bb declsExact exactLayouts twoU8BoolTy.kind
      (.aggregate 0 [.scalar ⟨2, 1⟩, mkU8 1])) = true ∧
    stepLocals? (bb declsExact exactLayouts twoU8BoolTy.kind
      (.aggregate 0 [.scalar ⟨1, 1⟩, mkU8 2])) =
      .some [.init (.aggregate 0 [.scalar ⟨1, 1⟩, mkU8 2])] ∧
    isUbNode (bb declsExact exactLayouts nonNullU8Ty.kind
      (.aggregate 0 [mkUsize 0])) = true ∧
    isUnsupportedNode (bb [mkDecl u64Ty] protoLayouts (.uint .u64)
      (.ptr { allocId := 7, offsetBytes := 0 } 8)) = true ∧
    isUnsupportedNode (bb [mkDecl unitTy] protoLayouts (.slice (.uint .u8)) .unit) = true ∧
    isUnsupportedNode (evalBlackBoxProto s0 (mkTarget "core::intrinsics::black_box" [])
      [] protoLayouts [] [mkU32 1] [.uninit] dstLocal0 (.some 1)) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 13(d): `ptr_mask` hardening:
- `concreteBaseAddr? = .some 0` is rejected (`.unsupported`), preventing `ptr_mask(p, 0)` from
  turning a live pointer into a bogus offset-0 dereferenceable pointer;
- identity mask `usize::MAX` (`2^64 - 1`) succeeds on an opaque ADT local (unknown `allocAlign`)
  AND on a dead tracked pointer, preserving `allocId`/`tag`;
- wide pointer `.aggregate 0 [data, len]` fails closed `.unsupported` rather than false `.ub`. -/
theorem ptr_mask_zero_base_rejected_identity_mask_and_wide_ptr :
    let opaqueAdtTy : Ty := { kind := .adt "tests::Opaque" .nil, layoutIdx := 99 }
    let decls := [mkDecl rawConstU8Ty, mkDecl aligned16BufTy, mkDecl opaqueAdtTy]
    let locals := [.uninit, .init .unit, .init .unit]
    let bAligned : BorrowEntry := { tag := 7, targetLocal := 1, targetProjection := [], perm := .unique }
    let bOpaque : BorrowEntry := { tag := 8, targetLocal := 2, targetProjection := [], perm := .unique }
    let bDead : BorrowEntry :=
      { tag := 9, targetLocal := 1, targetProjection := [], perm := .frozen, allocDead := true }
    let s := mkState locals [bAligned, bOpaque, bDead]
    let allOnes : Nat := 18446744073709551615
    let rZeroBase := evalPtrMaskProto s decls protoLayouts
      [.ptr { allocId := 7, offsetBytes := 0 } 8, mkUsize 0] locals dstLocal0 (.some 1) (.some 0)
    let rOpaqueId := evalPtrMaskProto s decls protoLayouts
      [.ptr { allocId := 8, offsetBytes := 5 } 8, mkUsize allOnes] locals dstLocal0 (.some 1) .none
    let rDeadMask := evalPtrMaskProto s decls protoLayouts
      [.ptr { allocId := 9, offsetBytes := 13 } 8, mkUsize 18446744073709551608] locals dstLocal0 (.some 1) .none
    let rWidePtr := evalPtrMaskProto s decls protoLayouts
      [.aggregate 0 [.ptr { allocId := 7, offsetBytes := 13 } 8, mkUsize 4], mkUsize 18446744073709551608]
      locals dstLocal0 (.some 1) .none
    isUnsupportedNode rZeroBase = true ∧
    (stepLocals? rOpaqueId).bind (fun ls => get? ls 0) =
      .some (.init (.ptr { allocId := 8, offsetBytes := 5 } 8)) ∧
    (stepLocals? rDeadMask).bind (fun ls => get? ls 0) =
      .some (.init (.ptr { allocId := 9, offsetBytes := 8 } 8)) ∧
    isUnsupportedNode rWidePtr = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- 13(e): `writeIntrinsicReturnProto` forwards `bodyLocalDecls`/`bodyLayouts` on `.deref`
destinations: writing `black_box(42u32)` to `*p` updates the target local, while writing through
a `.frozen` tag faults `.ub`, and writing to a direct destination protected by an active protector
also faults `.ub`. -/
theorem write_intrinsic_return_deref_and_protector_enforcement :
    let decls := [mkDecl rawMutU32Ty, mkDecl u32Ty]
    let pMut : Value := .ptr { allocId := 1, offsetBytes := 0 } 8
    let locals := [.init pMut, .init (mkU32 5)]
    let derefDst : Place := { local_ := 0, projection := [.deref] }
    let bUnique : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let bFrozen : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let bProt : BorrowEntry :=
      { tag := 2, targetLocal := 1, targetProjection := [], perm := .unique, protector := .some 77 }
    let rDerefOk := evalBlackBoxProto (mkState locals [bUnique])
      (mkTarget "core::intrinsics::black_box" [.uint .u32]) decls protoLayouts []
      [mkU32 42] locals derefDst (.some 1)
    let rDerefFrozenUb := evalBlackBoxProto (mkState locals [bFrozen])
      (mkTarget "core::intrinsics::black_box" [.uint .u32]) decls protoLayouts []
      [mkU32 42] locals derefDst (.some 1)
    let rDirectProtUb := evalBlackBoxProto (mkState locals [bProt] [77])
      (mkTarget "core::intrinsics::black_box" [.uint .u32]) decls protoLayouts []
      [mkU32 42] locals { local_ := 1, projection := .nil } (.some 1)
    stepLocals? rDerefOk = .some [.init pMut, .init (mkU32 42)] ∧
    isUbNode rDerefFrozenUb = true ∧
    isUbNode rDirectProtUb = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- 13(f): `raw_eq` uninhabited non-ZST UB, 32-bit wide `*const [u8]` width (`2 * ptrBytes = 8`),
layout-less multi-field tuple fail-closed, and reordered `.scalarPair` (`memoryIndex = [1, 0]`)
validation. -/
theorem raw_eq_uninhabited_32bit_wide_rawptr_tuple_and_reordered_scalarpair :
    let layouts32 : LayoutTable := { pointerBits := 32, isLittleEndian := true, entries := [] }
    let extraLayouts : LayoutTable :=
      { pointerBits := 64
        isLittleEndian := true
        entries :=
          [ -- idx 0: uninhabited non-ZST struct (size 4, align 4, isUninhabited = true)
            { size := ⟨4⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩] [0], variants := .single 0,
              backendRepr := .memory, isUninhabited := true },
            -- idx 1: reordered `ScalarPair` struct `{ first: bool@4, second: u32@0 }`,
            -- offsets `[4, 0]`, `memoryIndex = [1, 0]`, `backendRepr = .scalarPair u32 bool`, NO `fieldLayouts`!
            { size := ⟨8⟩, align := ⟨4⟩, fields := .arbitrary [⟨4⟩, ⟨0⟩] [1, 0], variants := .single 0,
              backendRepr := .scalarPair
                (.initialized (.int 32 false) ⟨0, 4294967295⟩)
                (.initialized (.int 8 false) ⟨0, 1⟩),
              isUninhabited := false } ] }
    let uninhabNonZstTy : Ty := { kind := .adt "tests::UninhabNonZst" .nil, layoutIdx := 0 }
    let declsU := [mkDecl boolTy, mkDecl uninhabNonZstTy]
    let gInit4 : CapturedAllocation :=
      { allocId := 80, bytes := [.some 1, .some 2, .some 3, .some 4], relocations := [],
        align := ⟨4⟩, mutability := .not }
    let rRawEqUninhab := evalRawEqProto (mkState [.uninit, .uninit] [] [] [gInit4])
      (mkTarget "core::intrinsics::raw_eq" [uninhabNonZstTy.kind]) declsU extraLayouts []
      [.ptr { allocId := 80, offsetBytes := 0 } 8, .ptr { allocId := 80, offsetBytes := 0 } 8]
      [.uninit, .uninit] dstLocal0 (.some 1)
    let plain8 := List.replicate 8 (AbstractByte.init 1 .none)
    let plain16 := List.replicate 16 (AbstractByte.init 1 .none)
    -- Reordered `ScalarPair`: bytes 0..3 = u32(5), byte 4 = bool(1 or 2), bytes 5..7 = padding
    let validPairBytes : List AbstractByte :=
      [.init 5 .none, .init 0 .none, .init 0 .none, .init 0 .none, .init 1 .none, .uninit, .uninit, .uninit]
    let badPairBytes : List AbstractByte :=
      [.init 5 .none, .init 0 .none, .init 0 .none, .init 0 .none, .init 2 .none, .uninit, .uninit, .uninit]
    -- Unbacked `allocId = 0, offsetBytes = 0` inside `&u32` bytes -> `.ub`:
    let unbackedZeroPtrBytes : List AbstractByte := List.replicate 8 (.init 0 (.some (0, 0)))
    isUbNode rRawEqUninhab = true ∧
    validateTypedBytesProto 8 [] layouts32 (.rawPtr .not (.slice (.uint .u8))) plain8 = .valid ∧
    validateTypedBytesProto 8 [] layouts32 (.rawPtr .not (.slice (.uint .u8))) plain16 = .ub ∧
    validateTypedBytesProto 8 [] protoLayouts (.tuple [.uint .u8, .uint .u32]) plain8 = .unsupported ∧
    decodePartialUninitValueProto 8 [] protoLayouts { kind := .tuple [.uint .u8, .uint .u32], layoutIdx := 99 } plain8 = .none ∧
    validateTypedBytesForLayoutIdxProto 8 extraLayouts 1 validPairBytes = .valid ∧
    validateTypedBytesForLayoutIdxProto 8 extraLayouts 1 badPairBytes = .ub ∧
    validateTypedBytesProto 8 [] protoLayouts (.ref .not (.uint .u32)) unbackedZeroPtrBytes = .ub := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 13(g): Unknown container alignment fails closed `.unsupported` (and still catches guaranteed
misalignment `.ub` at `offset % reqAlign != 0`), and diverging `const_eval_select` (`target = none`)
fails closed `.unsupported` rather than falsely faulting `.ub`. -/
theorem unknown_alignment_fail_closed_and_diverging_const_eval_select :
    let opaqueAdtTy : Ty := { kind := .adt "tests::Opaque" .nil, layoutIdx := 99 }
    let decls := [mkDecl unitTy, mkDecl opaqueAdtTy]
    let locals := [.uninit, .init .unit]
    let bOpaque : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let s := mkState locals [bOpaque]
    let copyU32 := mkTarget "core::intrinsics::copy" [.uint .u32]
    let rOpaqueZeroOff0 := evalCopyProto s copyU32 decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, mkUsize 4096, mkUsize 0] locals dstLocal0 (.some 1)
    let rOpaqueZeroOff2 := evalCopyProto s copyU32 decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 2 } 8, mkUsize 4096, mkUsize 0] locals dstLocal0 (.some 1)
    let rUnknownZeroOff0 := evalCopyProto s copyU32 decls protoLayouts []
      [.ptr { allocId := 999, offsetBytes := 0 } 8, mkUsize 4096, mkUsize 0] locals dstLocal0 (.some 1)
    let rUnknownZeroOff2 := evalCopyProto s copyU32 decls protoLayouts []
      [.ptr { allocId := 999, offsetBytes := 2 } 8, mkUsize 4096, mkUsize 0] locals dstLocal0 (.some 1)
    let rUnknownNonZero := evalCopyProto s copyU32 decls protoLayouts []
      [.ptr { allocId := 999, offsetBytes := 0 } 8, mkUsize 4096, mkUsize 1] locals dstLocal0 (.some 1)
    let rConstEvalDiv := evalDirectRustIntrinsicProto? s .none
      (mkTarget "core::intrinsics::const_eval_select" []) decls protoLayouts [] [] locals dstLocal0 .none .continue_
    let rWriteBytesDivUnsup := evalDirectRustIntrinsicProto? s .none
      (mkTarget "core::intrinsics::write_bytes" [opaqueAdtTy.kind]) decls protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, mkU8 0, mkUsize 1] locals dstLocal0 .none .continue_
    let sU32 := mkState [.uninit, .init (mkU32 0)]
      [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }]
    let rWriteBytesDivRetUb := evalDirectRustIntrinsicProto? sU32 .none
      (mkTarget "core::intrinsics::write_bytes" [.uint .u32]) [mkDecl unitTy, mkDecl u32Ty] protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, mkU8 0, mkUsize 0]
      [.uninit, .init (mkU32 0)] dstLocal0 .none .continue_
    isUnsupportedNode rOpaqueZeroOff0 = true ∧
    isUbNode rOpaqueZeroOff2 = true ∧
    isUnsupportedNode rUnknownZeroOff0 = true ∧
    isUbNode rUnknownZeroOff2 = true ∧
    isUbNode rUnknownNonZero = true ∧
    rConstEvalDiv.map isUnsupportedNode = .some true ∧
    rWriteBytesDivUnsup.map isUnsupportedNode = .some true ∧
    rWriteBytesDivRetUb.map isUbNode = .some true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 14: Tag Windows, Union Data Ranges, Uninitialized Aggregates, and Exact Alignment -/

/-- 14(a): an access must stay inside the place (or byte range) of the borrow it goes through.
`_1 : (u32, u32)` with tag `1` borrowing field `0` and tag `2` borrowing field `1` (both `.unique`):
- writing field `1`'s bytes through tag `1` (`copy` to offset `4`) fails closed. Tree Borrows
  permits it, but it is a foreign write to tag `2`; with one permission per tag and
  projection-based overlap the write would leave tag `2` `.unique` (missed UB on its next use);
- reading field `1`'s bytes through tag `1` fails closed for the same reason;
- copying field `0` to field `1` through their own tags succeeds, and both stay `.unique`;
- an access that leaves the allocation is still `.ub`.
A ranged borrow behaves the same way: `[0, 8)` of a `[u32; 4]` under tag `1`, `[8, 16)` under tag `2`:
- comparing `[0, 8)` with `[8, 16)` through their own tags succeeds;
- `[4, 12)` through tag `1` leaves its range but not the allocation: `.unsupported` (not `.ub`);
- `[12, 20)` leaves the allocation: `.ub`. -/
theorem tree_borrows_access_outside_borrowed_place_fails_closed :
    let decls := [mkDecl i32Ty, mkDecl unpaddedPairTy]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 11, mkU32 22])]
    let bA : BorrowEntry :=
      { tag := 1, targetLocal := 1, targetProjection := [.field 0 u32Ty], perm := .unique }
    let bB : BorrowEntry :=
      { tag := 2, targetLocal := 1, targetProjection := [.field 1 u32Ty], perm := .unique }
    let s := mkState locals [bA, bB]
    let copyU32 := mkTarget "core::intrinsics::copy" [.uint .u32]
    let p (tag off : Nat) : Value := .ptr { allocId := tag, offsetBytes := off } 8
    let rOutOfPlaceWrite := evalCopyProto s copyU32 decls protoLayouts []
      [p 1 0, p 1 4, mkUsize 1] locals dstLocal0 (.some 1)
    let rOutOfPlaceRead := evalCompareBytesProto s decls protoLayouts
      [p 1 4, p 2 0, mkUsize 4] locals dstLocal0 (.some 1)
    let rInPlace := evalCopyProto s copyU32 decls protoLayouts []
      [p 1 0, p 2 0, mkUsize 1] locals dstLocal0 (.some 1)
    let rPastAllocation := evalCopyProto s copyU32 decls protoLayouts []
      [p 1 0, p 2 4, mkUsize 1] locals dstLocal0 (.some 1)
    let arrDecls := [mkDecl i32Ty, mkDecl arrU32x4Ty]
    let arrLocals := [.uninit, .init (.aggregate 0 [mkU32 10, mkU32 20, mkU32 30, mkU32 40])]
    let bLeft : BorrowEntry :=
      { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique,
        rangeOffset := 0, rangeLen := 8 }
    let bRight : BorrowEntry :=
      { tag := 2, targetLocal := 1, targetProjection := [], perm := .unique,
        rangeOffset := 8, rangeLen := 8 }
    let sArr := mkState arrLocals [bLeft, bRight]
    let cmp (a b : Value) (n : Nat) : MirStepNode :=
      evalCompareBytesProto sArr arrDecls protoLayouts [a, b, mkUsize n] arrLocals dstLocal0 (.some 1)
    isUnsupportedNode rOutOfPlaceWrite = true ∧
    isUnsupportedNode rOutOfPlaceRead = true ∧
    stepLocals? rInPlace = .some [.init .unit, .init (.aggregate 0 [mkU32 11, mkU32 11])] ∧
    (stepState? rInPlace).map (fun s' => s'.memory.borrows.map (fun b => b.perm)) =
      .some [.unique, .unique] ∧
    isUbNode rPastAllocation = true ∧
    (stepLocals? (cmp (p 1 0) (p 2 8) 8)).bind (fun ls => get? ls 0) =
      .some (.init (.scalar ⟨4294967295, 4⟩)) ∧
    isUnsupportedNode (cmp (p 1 4) (p 2 8) 8) = true ∧
    isUbNode (cmp (p 1 12) (p 2 8) 8) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Layout table for union data ranges and alignment through an opaque root:
- idx 0: `u32`; idx 1: `u8`; idx 2: `()`; idx 3: padded `(u8, u32)` (size 8, padding `1..3`);
- idx 4: `MaybeUninit<(u8, u32)>` with field layouts `[(), (u8, u32)]`;
- idx 5: the same union WITHOUT field layouts (data range unknown);
- idx 6: `#[repr(packed)] struct Packed { x: u32 }` (size 4, align 1). -/
def unionRangeLayouts : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [ { size := ⟨4⟩, align := ⟨4⟩, fields := .primitive, variants := .single 0,
          backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
          isUninhabited := false },
        { size := ⟨1⟩, align := ⟨1⟩, fields := .primitive, variants := .single 0,
          backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
          isUninhabited := false },
        { size := ⟨0⟩, align := ⟨1⟩, fields := .arbitrary [] [], variants := .single 0,
          backendRepr := .memory, isUninhabited := false },
        { size := ⟨8⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], variants := .single 0,
          backendRepr := .memory, fieldLayouts := [1, 0], isUninhabited := false },
        { size := ⟨8⟩, align := ⟨4⟩, fields := .union 2, variants := .single 0,
          backendRepr := .memory, fieldLayouts := [2, 3], isUninhabited := false },
        { size := ⟨8⟩, align := ⟨4⟩, fields := .union 2, variants := .single 0,
          backendRepr := .memory, isUninhabited := false },
        { size := ⟨4⟩, align := ⟨1⟩, fields := .arbitrary [⟨0⟩] [0], variants := .single 0,
          backendRepr := .memory, fieldLayouts := [0], isUninhabited := false } ] }

def maybeUninitPairTy : Ty :=
  { kind := .adt "core::mem::maybe_uninit::MaybeUninit" [.tuple [.uint .u8, .uint .u32]], layoutIdx := 4 }
def opaqueUnionTy : Ty := { kind := .adt "tests::OpaqueUnion" .nil, layoutIdx := 5 }
def packedU32Ty : Ty := { kind := .adt "tests::Packed" .nil, layoutIdx := 6 }

/-- 14(b): a typed copy keeps exactly a union's DATA RANGE: the bytes that are data in at least
one field. `MaybeUninit<(u8, u32)>` has fields `()` and `(u8, u32)`, so bytes `1..3` are padding
in every field and are reset, while an uninitialized data byte stays uninitialized. Swapping two
`static mut` unions `A = [01, AA, AA, AA, 0A, 00, 00, 00]` and `B = [U, BB, U, U, 14, U, 00, 00]`:
- `A` receives `B` with bytes `1..3` reset: `[U, U, U, U, 14, U, 00, 00]`;
- `B` receives `A` with bytes `1..3` reset: `[01, U, U, U, 0A, 00, 00, 00]`;
- a union whose field layouts are not recorded fails closed (its common padding is unknown). -/
theorem typed_swap_union_keeps_data_range_and_resets_common_padding :
    let mkG (id : Nat) (bytes : List (Option UInt8)) : CapturedAllocation :=
      { allocId := id, bytes := bytes, relocations := [], align := ⟨4⟩, mutability := .mut }
    let gA := mkG 60 [.some 1, .some 170, .some 170, .some 170, .some 10, .some 0, .some 0, .some 0]
    let gB := mkG 61 [.none, .some 187, .none, .none, .some 20, .none, .some 0, .some 0]
    let s := mkState [.uninit] [] [] [gA, gB]
    let swap (ty : Ty) : MirStepNode :=
      evalTypedSwapNonOverlappingProto s
        (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [ty.kind])
        [mkDecl unitTy, mkDecl ty] unionRangeLayouts []
        [.ptr { allocId := 60, offsetBytes := 0 } 8, .ptr { allocId := 61, offsetBytes := 0 } 8]
        [.uninit] dstLocal0 (.some 1)
    globalBytes? (swap maybeUninitPairTy) 0 =
      .some [.none, .none, .none, .none, .some 20, .none, .some 0, .some 0] ∧
    globalBytes? (swap maybeUninitPairTy) 1 =
      .some [.some 1, .none, .none, .none, .some 10, .some 0, .some 0, .some 0] ∧
    isUnsupportedNode (swap opaqueUnionTy) = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- 14(c): `black_box` accepts a wholly uninitialized sub-value exactly at the types that permit
it: `[MaybeUninit<u32>; 2]`, a tuple field of that type, `((), MaybeUninit<u32>)`, and
`MaybeUninit<(u8, u32)>` are valid when uninitialized; an uninitialized `u32` field and an
uninitialized `[u8; 2]` are `.ub`. -/
theorem black_box_uninit_valid_exactly_where_type_permits :
    let arrMuTy : RigidTy := .array maybeUninitU32Ty.kind 2
    let s0 := mkState [.uninit]
    let bb (decls : List LocalDecl) (layouts : LayoutTable) (ty : RigidTy) (v : Value) : MirStepNode :=
      evalBlackBoxProto s0 (mkTarget "core::intrinsics::black_box" [ty]) decls layouts [] [v]
        [.uninit] dstLocal0 (.some 1)
    let declsMu := [mkDecl unitTy, mkDecl maybeUninitU32Ty]
    stepLocals? (bb declsMu protoLayouts arrMuTy .uninit) = .some [.init .uninit] ∧
    stepLocals? (bb declsMu protoLayouts (.tuple [.uint .u32, arrMuTy])
      (.aggregate 0 [mkU32 9, .uninit])) = .some [.init (.aggregate 0 [mkU32 9, .uninit])] ∧
    stepLocals? (bb declsMu protoLayouts (.tuple [.tuple [], maybeUninitU32Ty.kind])
      (.aggregate 0 [.uninit, .uninit])) = .some [.init (.aggregate 0 [.uninit, .uninit])] ∧
    stepLocals? (bb [mkDecl unitTy, mkDecl maybeUninitPairTy] unionRangeLayouts
      maybeUninitPairTy.kind .uninit) = .some [.init .uninit] ∧
    isUbNode (bb declsMu protoLayouts (.tuple [.uint .u32, .uint .u32])
      (.aggregate 0 [mkU32 9, .uninit])) = true ∧
    isUbNode (bb declsMu protoLayouts (.array (.uint .u8) 2) .uninit) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 14(d): alignment is decided from the root allocation's alignment and the total byte offset,
never from an enclosing container alone. A pointer to field `0` (a `#[repr(packed)]` struct of
alignment `1`) of a local whose own layout is unknown may or may not be 4-aligned depending on
that unknown layout: the zero-byte `copy::<u32>` fails closed with `.unsupported`, at offset `0`
and at offset `2` (the total offset is unknown, so neither is known to be misaligned). -/
theorem alignment_undetermined_under_opaque_root_fails_closed :
    let opaqueAdtTy : Ty := { kind := .adt "tests::Opaque" .nil, layoutIdx := 99 }
    let decls := [mkDecl unitTy, mkDecl opaqueAdtTy]
    let locals := [.uninit, .init .unit]
    let b1 : BorrowEntry :=
      { tag := 1, targetLocal := 1, targetProjection := [.field 0 packedU32Ty], perm := .unique }
    let s := mkState locals [b1]
    let copyU32 := mkTarget "core::intrinsics::copy" [.uint .u32]
    let run (off : Nat) : MirStepNode :=
      evalCopyProto s copyU32 decls unionRangeLayouts []
        [.ptr { allocId := 1, offsetBytes := off } 8, mkUsize 4096, mkUsize 0] locals dstLocal0 (.some 1)
    isUnsupportedNode (run 0) = true ∧ isUnsupportedNode (run 2) = true := by
  refine ⟨rfl, rfl⟩

/-- A bare endpoint with the given offsets, used to instantiate the tag-window theorems. -/
def mkEndpoint (effOffset allocSize lower upper : Nat) (windowKnown : Bool) : ResolvedMemEndpointProto :=
  { key := .global 0
    effOffset := effOffset
    allocSize := allocSize
    accessLower := lower
    accessUpper := upper
    tagWindowKnown := windowKnown
    writable := true
    borrowInfo? := .none
    targetDecls := .nil
    targetLayouts := protoLayouts
    rootTyOpt := .none
    rootSlot? := .none
    globalAlloc? := .none }

/-- 14(e): non-vacuity of the tag-window and padding-reset theorems: an access inside the window
is accepted, one outside the window (or with an unknown window) is `.unsupported`, one outside the
allocation is `.ub`, and a reset byte list refines the original. -/
theorem tag_window_and_padding_reset_theorems_non_vacuous :
    endpointAccessCheckProto (mkEndpoint 4 16 4 8 true) 4 = .ok () ∧
    endpointAccessCheckProto (mkEndpoint 4 16 4 8 true) 8 = .unsupported ∧
    endpointAccessCheckProto (mkEndpoint 4 16 4 8 false) 4 = .unsupported ∧
    endpointAccessCheckProto (mkEndpoint 4 16 4 8 true) 16 = .ub ∧
    abstractBytesRefineProto
      (applyDataMaskProto [true, false] [.init 5 (.some (3, 3)), .init 6 .none])
      [.init 5 (.some (3, 3)), .init 6 .none] = true ∧
    applyDataMaskProto [true, false] [.init 5 (.some (3, 3)), .init 6 .none] =
      [.init 5 (.some (3, 3)), .uninit] := by
  refine ⟨?_, rfl, rfl, ?_, ?_, rfl⟩
  · exact (endpointAccessCheckProto_ok_iff (mkEndpoint 4 16 4 8 true) 4).mpr
      ⟨by decide, rfl, by decide, by decide⟩
  · exact (endpointAccessCheckProto_ub_iff (mkEndpoint 4 16 4 8 true) 16).mpr (by decide)
  · exact applyDataMaskProto_refines [true, false] [.init 5 (.some (3, 3)), .init 6 .none] rfl

/-! ## Section 15: Pass A2 Regression & Soundness Witnesses -/

/-- 15(a): Union-field Tree Borrows aliasing (`borrowsAfter{Read,Write}AccessProto` +
`writeIntrinsicReturnProto` direct union destination):
On `union U { a: u32, b: u32 }` with `tag 1` borrowing `u.a` (`[.field 0]`) and `tag 2`
borrowing `u.b` (`[.field 1]`), both tags have window `[0, 4)`:
- writing `u.a` through `tag 1` (`copy`) disables sibling `tag 2` on `u.b` (previously left `.unique`),
  and faults `.ub` when `tag 2` has an active protector;
- reading `u.a` through `tag 1` (`compare_bytes`) freezes sibling `tag 2` on `u.b` (previously left
  `.unique`), and faults `.ub` when `tag 2` is a protected `.unique` borrow;
- returning `black_box(42u32)` directly to `u.a` disables sibling `tag 2` on `u.b`. -/
theorem union_field_tree_borrows_and_direct_union_dest_invalidation :
    let unionU32Layouts : LayoutTable :=
      { pointerBits := 64
        isLittleEndian := true
        entries :=
          [ { size := ⟨4⟩, align := ⟨4⟩, fields := .primitive, variants := .single 0,
              backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
              isUninhabited := false },
            { size := ⟨4⟩, align := ⟨4⟩, fields := .union 2, variants := .single 0,
              backendRepr := .memory, fieldLayouts := [0, 0], isUninhabited := false } ] }
    let unionU32Ty : Ty := { kind := .adt "tests::UnionU32" .nil, layoutIdx := 1 }
    let u32L0 : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let decls := [mkDecl i32Ty, mkDecl unionU32Ty, mkDecl u32L0]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 10, .uninit]), .init (mkU32 99)]
    let bA : BorrowEntry :=
      { tag := 1, targetLocal := 1, targetProjection := [.field 0 u32L0], perm := .unique }
    let bB : BorrowEntry :=
      { tag := 2, targetLocal := 1, targetProjection := [.field 1 u32L0], perm := .unique }
    let bBProt : BorrowEntry := { bB with protector := .some 55 }
    let bSrc : BorrowEntry := { tag := 3, targetLocal := 2, targetProjection := [], perm := .frozen }
    let p (tag : Nat) : Value := .ptr { allocId := tag, offsetBytes := 0 } 8
    let rWrite := evalCopyProto (mkState locals [bA, bB, bSrc])
      (mkTarget "core::intrinsics::copy" [.uint .u32]) decls unionU32Layouts []
      [p 3, p 1, mkUsize 1] locals dstLocal0 (.some 1)
    let rWriteProtUb := evalCopyProto (mkState locals [bA, bBProt, bSrc] [55])
      (mkTarget "core::intrinsics::copy" [.uint .u32]) decls unionU32Layouts []
      [p 3, p 1, mkUsize 1] locals dstLocal0 (.some 1)
    let rRead := evalCompareBytesProto (mkState locals [bA, bB, bSrc]) decls unionU32Layouts
      [p 1, p 3, mkUsize 4] locals dstLocal0 (.some 1)
    let rReadProtUb := evalCompareBytesProto (mkState locals [bA, bBProt, bSrc] [55]) decls unionU32Layouts
      [p 1, p 3, mkUsize 4] locals dstLocal0 (.some 1)
    let rDirectDest := evalBlackBoxProto (mkState locals [bA, bB])
      (mkTarget "core::intrinsics::black_box" [.uint .u32]) decls unionU32Layouts []
      [mkU32 42] locals { local_ := 1, projection := [.field 0 u32L0] } (.some 1)
    (stepState? rWrite).map (fun s' => s'.memory.borrows.map (fun b => b.perm)) =
      .some [.unique, .disabled, .frozen] ∧
    isUbNode rWriteProtUb = true ∧
    (stepState? rRead).map (fun s' => s'.memory.borrows.map (fun b => b.perm)) =
      .some [.unique, .frozen, .frozen] ∧
    isUbNode rReadProtUb = true ∧
    (stepState? rDirectDest).map (fun s' => s'.memory.borrows.map (fun b => b.perm)) =
      .some [.disabled, .disabled] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- 15(b): Ranged-projected tag-window intersection AND layout-carrying ADT sub-place size:
- `tag 1` with BOTH `rangeOffset := 0, rangeLen := 8` AND `targetProjection := [.field 0 u32Ty]` on
  `_1 : (u32, u32)` has intersected tag window `[0, 4)`: writing offset `4` (`.field 1`) through
  `tag 1` fails closed `.unsupported` (closing the ranged-projected Tree Borrows conflict leak against
  unranged sibling `tag 2` on `.field 1`), while writing offset `0` succeeds and keeps `tag 2` `.unique`;
- borrowing `&s.inner` where `Inner` is ONLY in `Outer`'s `fieldLayouts` (no standalone `LocalDecl`
  for `Inner` in `bodyLocalDecls`) resolves `placeSize` from `placeTy.layoutIdx` and succeeds! -/
theorem ranged_projected_tag_window_intersection_and_field_layout_size :
    let decls := [mkDecl unitTy, mkDecl unpaddedPairTy]
    let locals := [.uninit, .init (.aggregate 0 [mkU32 11, mkU32 22])]
    let bRangedProj : BorrowEntry :=
      { tag := 1, targetLocal := 1, targetProjection := [.field 0 u32Ty], perm := .unique,
        rangeOffset := 0, rangeLen := 8 }
    let bSib : BorrowEntry :=
      { tag := 2, targetLocal := 1, targetProjection := [.field 1 u32Ty], perm := .unique }
    let s := mkState locals [bRangedProj, bSib]
    let p (tag off : Nat) : Value := .ptr { allocId := tag, offsetBytes := off } 8
    let copyU32 := mkTarget "core::intrinsics::copy" [.uint .u32]
    let rEscape := evalCopyProto s copyU32 decls protoLayouts []
      [p 1 0, p 1 4, mkUsize 1] locals dstLocal0 (.some 1)
    let rInWindow := evalCopyProto s copyU32 decls protoLayouts []
      [p 1 0, p 1 0, mkUsize 1] locals dstLocal0 (.some 1)
    -- `Outer { inner: Inner }` where `Inner` has NO standalone `LocalDecl` in `outerDecls`:
    let fieldOnlyLayouts : LayoutTable :=
      { pointerBits := 64
        isLittleEndian := true
        entries :=
          [ { size := ⟨4⟩, align := ⟨4⟩, fields := .primitive, variants := .single 0,
              backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
              isUninhabited := false },
            { size := ⟨4⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩] [0], variants := .single 0,
              backendRepr := .memory, fieldLayouts := [0], isUninhabited := false },
            { size := ⟨4⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩] [0], variants := .single 0,
              backendRepr := .memory, fieldLayouts := [1], isUninhabited := false } ] }
    let outerTy : Ty := { kind := .adt "tests::OuterOnly" .nil, layoutIdx := 2 }
    let innerUnresTy : Ty := { kind := .adt "tests::InnerOnly" .nil, layoutIdx := 99 }
    let outerDecls := [mkDecl i32Ty, mkDecl outerTy]
    let outerLocals := [.uninit, .init (.aggregate 0 [.aggregate 0 [mkU32 77]])]
    let bInner : BorrowEntry :=
      { tag := 1, targetLocal := 1, targetProjection := [.field 0 innerUnresTy], perm := .frozen }
    let rInnerCmp := evalCompareBytesProto (mkState outerLocals [bInner]) outerDecls fieldOnlyLayouts
      [p 1 0, p 1 0, mkUsize 4] outerLocals dstLocal0 (.some 1)
    isUnsupportedNode rEscape = true ∧
    stepLocals? rInWindow = .some [.init .unit, .init (.aggregate 0 [mkU32 11, mkU32 22])] ∧
    (stepState? rInWindow).map (fun s' => s'.memory.borrows.map (fun b => b.perm)) =
      .some [.unique, .unique] ∧
    (stepLocals? rInnerCmp).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨0, 4⟩)) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- 15(c): `.scalar (.union _)` without `fieldLayouts` fails closed AND inhabited union with
uninhabited field preserves its data range:
- `#[repr(C, align(4))] union PadUnion { a: (), b: (u8, u16) }` with `backendRepr = .scalar (.union I32)`
  and `fieldLayouts = []` fails closed `.unsupported` on `typed_swap_nonoverlapping` (never keeping
  common padding byte `1`!);
- with `fieldLayouts = [(), (u8, u16)]`, `PadUnion` swaps cleanly and resets common padding byte `1`
  to `.none` (`AbstractByte.uninit`);
- inhabited `union U { a: u32, b: ! }` (with uninhabited field `!`) swaps cleanly and preserves
  all 4 data bytes of `u32` (aligned with `lean-miri` `unionRanges`). -/
theorem scalar_union_without_field_layouts_fails_closed_and_uninhabited_union_field :
    let uLayouts : LayoutTable :=
      { pointerBits := 64
        isLittleEndian := true
        entries :=
          [ -- idx 0: u8; idx 1: u16; idx 2: (); idx 3: (u8, u16) size 4 pad byte 1
            { size := ⟨1⟩, align := ⟨1⟩, fields := .primitive, variants := .single 0,
              backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩), isUninhabited := false },
            { size := ⟨2⟩, align := ⟨2⟩, fields := .primitive, variants := .single 0,
              backendRepr := .scalar (.initialized (.int 16 false) ⟨0, 65535⟩), isUninhabited := false },
            { size := ⟨0⟩, align := ⟨1⟩, fields := .arbitrary [] [], variants := .single 0,
              backendRepr := .memory, isUninhabited := false },
            { size := ⟨4⟩, align := ⟨2⟩, fields := .arbitrary [⟨0⟩, ⟨2⟩] [0, 1], variants := .single 0,
              backendRepr := .memory, fieldLayouts := [0, 1], isUninhabited := false },
            -- idx 4: `PadUnion` WITHOUT `fieldLayouts` (`backendRepr = .scalar (.union I32)`)
            { size := ⟨4⟩, align := ⟨4⟩, fields := .union 2, variants := .single 0,
              backendRepr := .scalar (.union (.int 32 false)), isUninhabited := false },
            -- idx 5: `PadUnion` WITH `fieldLayouts := [2, 3]`
            { size := ⟨4⟩, align := ⟨4⟩, fields := .union 2, variants := .single 0,
              backendRepr := .scalar (.union (.int 32 false)), fieldLayouts := [2, 3], isUninhabited := false },
            -- idx 6: u32; idx 7: `!` (uninhabited); idx 8: `union U { a: u32, b: ! }`
            { size := ⟨4⟩, align := ⟨4⟩, fields := .primitive, variants := .single 0,
              backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩), isUninhabited := false },
            { size := ⟨0⟩, align := ⟨1⟩, fields := .primitive, variants := .empty,
              backendRepr := .memory, isUninhabited := true },
            { size := ⟨4⟩, align := ⟨4⟩, fields := .union 2, variants := .single 0,
              backendRepr := .memory, fieldLayouts := [6, 7], isUninhabited := false } ] }
    let padUnionNoFl : Ty := { kind := .adt "tests::PadUnionNoFl" .nil, layoutIdx := 4 }
    let padUnionFl : Ty := { kind := .adt "tests::PadUnionFl" .nil, layoutIdx := 5 }
    let unionWithNever : Ty := { kind := .adt "tests::UnionWithNever" .nil, layoutIdx := 8 }
    let mkG (id : Nat) (bs : List (Option UInt8)) : CapturedAllocation :=
      { allocId := id, bytes := bs, relocations := [], align := ⟨4⟩, mutability := .mut }
    let gA := mkG 90 [.some 1, .some 170, .some 10, .some 0]
    let gB := mkG 91 [.some 2, .some 187, .some 20, .some 0]
    let s := mkState [.uninit] [] [] [gA, gB]
    let swap (ty : Ty) : MirStepNode :=
      evalTypedSwapNonOverlappingProto s
        (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [ty.kind])
        [mkDecl unitTy, mkDecl ty] uLayouts []
        [.ptr { allocId := 90, offsetBytes := 0 } 8, .ptr { allocId := 91, offsetBytes := 0 } 8]
        [.uninit] dstLocal0 (.some 1)
    isUnsupportedNode (swap padUnionNoFl) = true ∧
    globalBytes? (swap padUnionFl) 0 = .some [.some 2, .none, .some 20, .some 0] ∧
    globalBytes? (swap padUnionFl) 1 = .some [.some 1, .none, .some 10, .some 0] ∧
    globalBytes? (swap unionWithNever) 0 = .some [.some 2, .some 187, .some 20, .some 0] ∧
    globalBytes? (swap unionWithNever) 1 = .some [.some 1, .some 170, .some 10, .some 0] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- 15(d): `ScalarPair` trailing-ZST separation & newtype aggregate fail-closed:
- `#[repr(C, align(4))] struct PairThenZst { a: (u8, bool), z: () }` (`size = 4`, `offsets = [0, 2]`,
  `memIdx = [0, 1]`, `backendRepr = .scalarPair u8 bool`, `fieldLayouts = []`):
  `validateTypedBytesForLayoutIdxProto`, `resetTypedPaddingForLayoutIdxProto`, and
  `validateValueAtLayoutIdxProto` (`black_box`) ALL fail closed instead of mistaking ZST offset `2`
  for the `bool` field at byte `1`;
- `struct Outer(Inner(u32))` without `fieldLayouts` (`offsets = [0]`, `backendRepr = .scalar u32`):
  `black_box` on `.aggregate 0 [.aggregate 0 [mkU32 7]]` fails closed `.unsupported` (not false `.ub`). -/
theorem scalar_pair_trailing_zst_and_newtype_aggregate_fail_closed :
    let spLayouts : LayoutTable :=
      { pointerBits := 64
        isLittleEndian := true
        entries :=
          [ -- idx 0: `PairThenZst { a: (u8, bool), z: () }` without `fieldLayouts`
            { size := ⟨4⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩, ⟨2⟩] [0, 1], variants := .single 0,
              backendRepr := .scalarPair
                (.initialized (.int 8 false) ⟨0, 255⟩)
                (.initialized (.int 8 false) ⟨0, 1⟩),
              isUninhabited := false },
            -- idx 1: `struct Outer(Inner(u32))` without `fieldLayouts`
            { size := ⟨4⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩] [0], variants := .single 0,
              backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
              isUninhabited := false } ] }
    let pairZstTy : Ty := { kind := .adt "tests::PairThenZst" .nil, layoutIdx := 0 }
    let outerNewtypeTy : Ty := { kind := .adt "tests::OuterNewtype" .nil, layoutIdx := 1 }
    let bytesWithBadBool : List AbstractByte := [.init 5 .none, .init 2 .none, .init 0 .none, .uninit]
    let rBbPairZst := evalBlackBoxProto (mkState [.uninit])
      (mkTarget "core::intrinsics::black_box" [pairZstTy.kind])
      [mkDecl unitTy, mkDecl pairZstTy] spLayouts []
      [.aggregate 0 [.aggregate 0 [mkU8 5, .scalar ⟨1, 1⟩], .unit]]
      [.uninit] dstLocal0 (.some 1)
    let rBbNewtype := evalBlackBoxProto (mkState [.uninit])
      (mkTarget "core::intrinsics::black_box" [outerNewtypeTy.kind])
      [mkDecl unitTy, mkDecl outerNewtypeTy] spLayouts []
      [.aggregate 0 [.aggregate 0 [mkU32 7]]]
      [.uninit] dstLocal0 (.some 1)
    validateTypedBytesForLayoutIdxProto 8 spLayouts 0 bytesWithBadBool = .unsupported ∧
    resetTypedPaddingForLayoutIdxProto 8 spLayouts 0 bytesWithBadBool = .none ∧
    isUnsupportedNode rBbPairZst = true ∧
    isUnsupportedNode rBbNewtype = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- 15(e): Global allocation commit round-trip guard:
- copying 4 bytes of an 8-byte tracked pointer (`copy::<u8>`) into a mutable global fails closed
  `.unsupported` rather than silently stripping provenance from the partial pointer;
- copying a 4-byte tracked pointer on a 32-bit `LayoutTable` (`pointerBits = 32`) into an 8-byte
  mutable global fails closed `.unsupported` rather than bleeding an 8-byte relocation into bytes `4..7`;
- copying a full 8-byte tracked pointer on 64-bit into a mutable global succeeds and preserves its
  exact relocation `(0, { allocId := 77, offsetBytes := 12 })`. -/
theorem global_commit_round_trip_guard_rejects_partial_ptr_and_32bit_reloc :
    let p77 : ProvenancePtr := { allocId := 77, offsetBytes := 12 }
    let gMut8 : CapturedAllocation :=
      { allocId := 50, bytes := List.replicate 8 (.some 0), relocations := [], align := ⟨8⟩, mutability := .mut }
    let decls64 := [mkDecl unitTy, mkDecl rawConstU8Ty]
    let loc64 := [.uninit, .init (.ptr p77 8)]
    let bPtr : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen }
    let s64 := mkState loc64 [bPtr] [] [gMut8]
    let rPartial := evalCopyProto s64 (mkTarget "core::intrinsics::copy" [.uint .u8])
      decls64 protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 50, offsetBytes := 0 } 8, mkUsize 4]
      loc64 dstLocal0 (.some 1)
    let rFull64 := evalCopyProto s64 (mkTarget "core::intrinsics::copy" [.uint .u8])
      decls64 protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 0 } 8, .ptr { allocId := 50, offsetBytes := 0 } 8, mkUsize 8]
      loc64 dstLocal0 (.some 1)
    let layouts32 : LayoutTable := { pointerBits := 32, isLittleEndian := true, entries := [] }
    let loc32 := [.uninit, .init (.ptr p77 4)]
    let s32 := mkState loc32 [bPtr] [] [gMut8]
    let r32Bit := evalCopyProto s32 (mkTarget "core::intrinsics::copy" [.uint .u8])
      decls64 layouts32 []
      [.ptr { allocId := 1, offsetBytes := 0 } 4, .ptr { allocId := 50, offsetBytes := 0 } 4, .scalar ⟨4, 4⟩]
      loc32 dstLocal0 (.some 1)
    isUnsupportedNode rPartial = true ∧
    isUnsupportedNode r32Bit = true ∧
    (stepState? rFull64).bind (fun s' => (get? s'.memory.globals 0).map (fun a => a.relocations)) =
      .some [(0, p77)] := by
  refine ⟨rfl, rfl, rfl⟩

/-- 15(f): Uninhabited-pointee references `&!` AND wide-pointer metadata UB in both byte validation
(`typed_swap_nonoverlapping`) and value validation (`black_box`):
- `&!` (`Ref .not .never`) faults `.ub` in `typed_swap_nonoverlapping` and `black_box` even when
  non-null and aligned; `&[!; 0]` and empty `&[!]` remain inhabited and valid;
- `raw_eq::<&!>` is NOT UB (pass B3 correction): its arguments are valid `&&!` references to the
  layout-inhabited `&!`, whose pointer bytes are compared without validating `T`;
- null vtable (`0`) on BOTH `*const dyn Trait` and `&dyn Trait` faults `.ub` in byte and value
  validation (matching `Miri/Interpreter/ValidityVisitor.lean:191-194, 326`); non-null vtable succeeds;
- oversized `&[u32]` (`len * 4 > isize::MAX`) and `&str` (`len > isize::MAX`) fault `.ub`, while
  provenance-carrying slice length on `&[u8]` fails closed `.unsupported`. -/
theorem uninhabited_ref_and_wide_ptr_metadata_ub_in_bytes_and_black_box :
    let refNeverTy : RigidTy := .ref .not .never
    let refEmptyNeverArrTy : RigidTy := .ref .not (.array .never 0)
    let refNeverSliceTy : RigidTy := .ref .not (.slice .never)
    let rawDynTy : RigidTy := .rawPtr .not (.dynamic "tests::Trait")
    let refDynTy : RigidTy := .ref .not (.dynamic "tests::Trait")
    let refSliceU32Ty : RigidTy := .ref .not (.slice (.uint .u32))
    let refSliceU8Ty : RigidTy := .ref .not (.slice (.uint .u8))
    let refStrTy : RigidTy := .ref .not .str
    let s0 := mkState [.uninit]
    let bb (ty : RigidTy) (v : Value) : MirStepNode :=
      evalBlackBoxProto s0 (mkTarget "core::intrinsics::black_box" [ty])
        [mkDecl unitTy] protoLayouts [] [v] [.uninit] dstLocal0 (.some 1)
    let nonNullBytes : List AbstractByte := [.init 1 .none] ++ List.replicate 7 (.init 0 .none)
    let nullBytes : List AbstractByte := List.replicate 8 (.init 0 .none)
    let hugeLenBytes : List AbstractByte := List.replicate 8 (.init 255 .none)
    let provLenBytes : List AbstractByte := List.replicate 8 (.init 4 (.some (7, 7)))
    let gPtr : CapturedAllocation :=
      { allocId := 95, bytes := [.some 1, .some 0, .some 0, .some 0, .some 0, .some 0, .some 0, .some 0],
        relocations := [], align := ⟨8⟩, mutability := .mut }
    let rRawEqRefNever := evalRawEqProto (mkState [.uninit] [] [] [gPtr])
      (mkTarget "core::intrinsics::raw_eq" [refNeverTy]) [mkDecl boolTy] protoLayouts []
      [.ptr { allocId := 95, offsetBytes := 0 } 8, .ptr { allocId := 95, offsetBytes := 0 } 8]
      [.uninit] dstLocal0 (.some 1)
    isUbNode (bb refNeverTy (mkUsize 4096)) = true ∧
    (stepLocals? rRawEqRefNever).bind (fun ls => get? ls 0) = .some (.init (.scalar (boolToScalar true))) ∧
    validateTypedBytesProto 8 [] protoLayouts refNeverTy nonNullBytes = .ub ∧
    stepLocals? (bb refEmptyNeverArrTy (mkUsize 4096)) = .some [.init (mkUsize 4096)] ∧
    stepLocals? (bb refNeverSliceTy (.aggregate 0 [mkUsize 4096, mkUsize 0])) =
      .some [.init (.aggregate 0 [mkUsize 4096, mkUsize 0])] ∧
    isUbNode (bb rawDynTy (.aggregate 0 [mkUsize 4096, mkUsize 0])) = true ∧
    isUbNode (bb refDynTy (.aggregate 0 [mkUsize 4096, mkUsize 0])) = true ∧
    stepLocals? (bb rawDynTy (.aggregate 0 [mkUsize 0, mkUsize 8192])) =
      .some [.init (.aggregate 0 [mkUsize 0, mkUsize 8192])] ∧
    validateTypedBytesProto 8 [] protoLayouts rawDynTy (nonNullBytes ++ nullBytes) = .ub ∧
    validateTypedBytesProto 8 [] protoLayouts refDynTy (nonNullBytes ++ nullBytes) = .ub ∧
    validateTypedBytesProto 8 [] protoLayouts refDynTy (nonNullBytes ++ nonNullBytes) = .valid ∧
    isUbNode (bb refSliceU32Ty (.aggregate 0 [mkUsize 4096, mkUsize 4611686018427387904])) = true ∧
    isUbNode (bb refStrTy (.aggregate 0 [mkUsize 4096, mkUsize 9223372036854775808])) = true ∧
    validateTypedBytesProto 8 [] protoLayouts refSliceU32Ty (nonNullBytes ++ hugeLenBytes) = .ub ∧
    validateTypedBytesProto 8 [] protoLayouts refSliceU8Ty (nonNullBytes ++ provLenBytes) = .unsupported ∧
    isUnsupportedNode (bb refSliceU8Ty (.aggregate 0 [mkUsize 4096, .ptr { allocId := 7, offsetBytes := 4 } 8])) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 15(g): Untyped padded caller referent fails closed (no false UB from `valueDefaultByteSize`),
`black_box` preserves resolved field `layoutIdx` when `target.typeArgs = []`, and `ptr_offset_from`
on two distinct dead tags of one local faults `.ub` when their effective offsets differ (while equal
offsets stay `.unsupported`). -/
theorem untyped_padded_caller_referent_black_box_field_layout_and_dead_tags_diff_offset :
    -- 1. Untyped caller-owned referent holding padded `(u8, u32)` (`targetLocal = 1`,
    --    past `locals` / `bodyLocalDecls`, backed by `callerLocals[1]` with `rootTyOpt = .none`):
    let callerVal : Value := .aggregate 0 [mkU8 1, mkU32 10]
    let bCaller : BorrowEntry :=
      { tag := 1, targetLocal := 1, targetFrameDepth := 0, targetProjection := [], perm := .frozen }
    let sCaller : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
        memory :=
          { emptyMemory with
            borrows := [bCaller]
            callerLocals := [.uninit, .init callerVal] } }
    let rCallerCmp := evalCompareBytesProto sCaller [mkDecl i32Ty] protoLayouts
      [.ptr { allocId := 1, offsetBytes := 4 } 8, .ptr { allocId := 1, offsetBytes := 4 } 8, mkUsize 4]
      [.uninit] dstLocal0 (.some 1)
    let rCallerOff := evalPtrOffsetFromProto sCaller (mkTarget "core::intrinsics::ptr_offset_from" [.uint .u8])
      [mkDecl isizeTy] protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 8 } 8, .ptr { allocId := 1, offsetBytes := 0 } 8]
      [.uninit] dstLocal0 (.some 1) false
    -- 2. `black_box(s.inner)` with `target.typeArgs = []` where `Inner` has only a `fieldLayouts` entry:
    let flLayouts : LayoutTable :=
      { pointerBits := 64
        isLittleEndian := true
        entries :=
          [ { size := ⟨1⟩, align := ⟨1⟩, fields := .primitive, variants := .single 0,
              backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩), isUninhabited := false },
            { size := ⟨1⟩, align := ⟨1⟩, fields := .arbitrary [⟨0⟩] [0], variants := .single 0,
              backendRepr := .memory, fieldLayouts := [0], isUninhabited := false },
            { size := ⟨1⟩, align := ⟨1⟩, fields := .arbitrary [⟨0⟩] [0], variants := .single 0,
              backendRepr := .memory, fieldLayouts := [1], isUninhabited := false } ] }
    let outerBoolTy : Ty := { kind := .adt "tests::OuterBool" .nil, layoutIdx := 2 }
    let innerBoolUnres : Ty := { kind := .adt "tests::InnerBool" .nil, layoutIdx := 99 }
    let opInner : Operand := .copy { local_ := 1, projection := [.field 0 innerBoolUnres] }
    let rBbFieldOk := evalBlackBoxProto (mkState [.uninit, .init (.aggregate 0 [.aggregate 0 [.scalar ⟨1, 1⟩]])])
      (mkTarget "core::intrinsics::black_box" [])
      [mkDecl innerBoolUnres, mkDecl outerBoolTy] flLayouts [opInner]
      [.aggregate 0 [.scalar ⟨1, 1⟩]] [.uninit, .init (.aggregate 0 [.aggregate 0 [.scalar ⟨1, 1⟩]])]
      dstLocal0 (.some 1)
    let rBbFieldUb := evalBlackBoxProto (mkState [.uninit, .init (.aggregate 0 [.aggregate 0 [.scalar ⟨2, 1⟩]])])
      (mkTarget "core::intrinsics::black_box" [])
      [mkDecl innerBoolUnres, mkDecl outerBoolTy] flLayouts [opInner]
      [.aggregate 0 [.scalar ⟨2, 1⟩]] [.uninit, .init (.aggregate 0 [.aggregate 0 [.scalar ⟨2, 1⟩]])]
      dstLocal0 (.some 1)
    -- 3. `ptr_offset_from` on two distinct dead tags of the same local: diff offsets -> `.ub`, eq offsets -> `.unsupported`:
    let bDead1 : BorrowEntry :=
      { tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen, allocDead := true }
    let bDead2 : BorrowEntry :=
      { tag := 2, targetLocal := 1, targetProjection := [], perm := .frozen, allocDead := true }
    let sDead := mkState [.uninit, .dead] [bDead1, bDead2]
    let rDeadDiff := evalPtrOffsetFromProto sDead (mkTarget "core::intrinsics::ptr_offset_from" [.uint .u32])
      [mkDecl isizeTy, mkDecl arrU32x4Ty] protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 4 } 8, .ptr { allocId := 2, offsetBytes := 0 } 8]
      [.uninit, .dead] dstLocal0 (.some 1) false
    let rDeadEq := evalPtrOffsetFromProto sDead (mkTarget "core::intrinsics::ptr_offset_from" [.uint .u32])
      [mkDecl isizeTy, mkDecl arrU32x4Ty] protoLayouts []
      [.ptr { allocId := 1, offsetBytes := 4 } 8, .ptr { allocId := 2, offsetBytes := 4 } 8]
      [.uninit, .dead] dstLocal0 (.some 1) false
    isUnsupportedNode rCallerCmp = true ∧
    isUnsupportedNode rCallerOff = true ∧
    (stepLocals? rBbFieldOk).bind (fun ls => get? ls 0) = .some (.init (.aggregate 0 [.scalar ⟨1, 1⟩])) ∧
    isUbNode rBbFieldUb = true ∧
    isUbNode rDeadDiff = true ∧
    isUnsupportedNode rDeadEq = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 16: Pass B3 Regression & Soundness Witnesses -/

/-- Layout fixtures for pass B3:
- idx 0: `u32`; idx 1: thin reference / pointer (8 bytes); idx 2: wide pointer `(data, len)`
  (16 bytes, `ScalarPair`); idx 3: `u8`. -/
def dstLayouts : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [ { size := ⟨4⟩, align := ⟨4⟩, fields := .primitive, variants := .single 0,
          backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩), isUninhabited := false },
        { size := ⟨8⟩, align := ⟨8⟩, fields := .primitive, variants := .single 0,
          backendRepr := .scalar (.initialized (.pointer 0) ⟨1, 18446744073709551615⟩),
          isUninhabited := false },
        { size := ⟨16⟩, align := ⟨8⟩, fields := .arbitrary [⟨0⟩, ⟨8⟩] [0, 1], variants := .single 0,
          backendRepr := .scalarPair (.initialized (.pointer 0) ⟨1, 18446744073709551615⟩)
            (.initialized (.int 64 false) ⟨0, 18446744073709551615⟩),
          isUninhabited := false },
        { size := ⟨1⟩, align := ⟨1⟩, fields := .primitive, variants := .single 0,
          backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩), isUninhabited := false } ] }

/-- `struct Packet { hdr: Hdr, body: [u8] }` (a custom DST: pointers to it are wide). -/
def packetK : RigidTy := .adt "tests::Packet" []
/-- `struct Hdr { .. }` (sized: pointers to it are thin). -/
def hdrK : RigidTy := .adt "tests::Hdr" []
/-- A local of type `&Packet` whose compiler layout records the 16-byte wide pointer. -/
def refPacketTy : Ty := { kind := .ref .not packetK, layoutIdx := 2 }
/-- A local of type `&Hdr` whose compiler layout records the 8-byte thin pointer. -/
def refHdrTy : Ty := { kind := .ref .not hdrK, layoutIdx := 1 }

/-- 16(a): pointer-to-uninhabited vs uninhabited pointee (fixes a false UB of pass A2).
`&!` is layout-INHABITED (a non-null pointer scalar), so only a reference whose own pointee is
layout-uninhabited is invalid:
- `black_box` rejects `&!` and `&(u8, !)` but accepts `&&!` and `&(u8, &!)`;
- `raw_eq::<&!>` compares the pointer bytes behind its valid `&&!` arguments (`true` on equal bytes,
  `false` on different ones), while `raw_eq::<!>` is UB (its `&!` arguments are invalid);
- `typed_swap_nonoverlapping` swaps `&&!` and `*const &!` values but rejects `&!` values. -/
theorem uninhabited_pointee_vs_pointer_to_uninhabited :
    let s0 := mkState [.uninit]
    let bb (ty : RigidTy) (v : Value) : MirStepNode :=
      evalBlackBoxProto s0 (mkTarget "core::intrinsics::black_box" [ty])
        [mkDecl unitTy] protoLayouts [] [v] [.uninit] dstLocal0 (.some 1)
    let mkG (id b : Nat) : CapturedAllocation :=
      { allocId := id, bytes := [.some (UInt8.ofNat b), .some 0, .some 0, .some 0, .some 0, .some 0, .some 0, .some 0],
        relocations := [], align := ⟨8⟩, mutability := .mut }
    let sg := mkState [.uninit] [] [] [mkG 95 1, mkG 96 2]
    let pg (id : Nat) : Value := .ptr { allocId := id, offsetBytes := 0 } 8
    let rawEq (ty : RigidTy) (a b : Nat) : MirStepNode :=
      evalRawEqProto sg (mkTarget "core::intrinsics::raw_eq" [ty]) [mkDecl boolTy] protoLayouts []
        [pg a, pg b] [.uninit] dstLocal0 (.some 1)
    let swap (ty : RigidTy) : MirStepNode :=
      evalTypedSwapNonOverlappingProto sg (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [ty])
        [mkDecl unitTy] protoLayouts [] [pg 95, pg 96] [.uninit] dstLocal0 (.some 1)
    let ret (n : MirStepNode) : Option LocalSlot := (stepLocals? n).bind (fun ls => get? ls 0)
    isUbNode (bb (.ref .not .never) (mkUsize 4096)) = true ∧
    isUbNode (bb (.ref .not (.tuple [.uint .u8, .never])) (mkUsize 4096)) = true ∧
    ret (bb (.ref .not (.ref .not .never)) (mkUsize 4096)) = .some (.init (mkUsize 4096)) ∧
    ret (bb (.ref .not (.tuple [.uint .u8, .ref .not .never])) (mkUsize 4096)) = .some (.init (mkUsize 4096)) ∧
    ret (rawEq (.ref .not .never) 95 95) = .some (.init (.scalar (boolToScalar true))) ∧
    ret (rawEq (.ref .not .never) 95 96) = .some (.init (.scalar (boolToScalar false))) ∧
    isUbNode (rawEq .never 95 95) = true ∧
    globalBytes? (swap (.ref .not (.ref .not .never))) 0 =
      .some [.some 2, .some 0, .some 0, .some 0, .some 0, .some 0, .some 0, .some 0] ∧
    globalBytes? (swap (.rawPtr .not (.ref .not .never))) 1 =
      .some [.some 1, .some 0, .some 0, .some 0, .some 0, .some 0, .some 0, .some 0] ∧
    isUbNode (swap (.ref .not .never)) = true ∧
    isUninhabitedRigidTyProto [] protoLayouts 8 (.ref .not .never) = false ∧
    referenceToUninhabitedProto [] protoLayouts .never = true ∧
    referenceToUninhabitedProto [] protoLayouts (.ref .not .never) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 16(b): an in-range surrogate in a `char`-SHAPED layout scalar (`Int(I32, false)` with a
non-wrapping range inside `0..=0x10FFFF`) fails closed: by layout alone it may be a `char`
(invalid) or a `u32` pattern type such as `CodePointInner` (valid). Previously the surrogate was
accepted as valid (missed UB for `struct S(char)` in `typed_swap_nonoverlapping` / `black_box`):
- layout idx 1 (`struct S(char)`): `0xD800` / `0xDFFF` are `.unsupported`, `'A'` and `0xE000` are
  valid, `0x110000` is `.ub` (out of range);
- a full-range `u32` field (idx 3) still accepts `0xD800`; the `RigidTy` path (`.char`) still
  rejects it exactly with `.ub`;
- `black_box::<S>` is `.unsupported` on a surrogate, `.ub` above `0x10FFFF`, and passes `'A'`. -/
theorem char_shaped_surrogate_fails_closed_in_layout_validation :
    let cL : LayoutTable :=
      { pointerBits := 64
        isLittleEndian := true
        entries :=
          [ { size := ⟨4⟩, align := ⟨4⟩, fields := .primitive, variants := .single 0,
              backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 1114111⟩), isUninhabited := false },
            { size := ⟨4⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩] [0], variants := .single 0,
              backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 1114111⟩), fieldLayouts := [0],
              isUninhabited := false },
            { size := ⟨4⟩, align := ⟨4⟩, fields := .primitive, variants := .single 0,
              backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩), isUninhabited := false },
            { size := ⟨4⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩] [0], variants := .single 0,
              backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩), fieldLayouts := [2],
              isUninhabited := false } ] }
    let b (n : Nat) : List AbstractByte :=
      [.init (UInt8.ofNat (n % 256)) .none, .init (UInt8.ofNat ((n / 256) % 256)) .none,
       .init (UInt8.ofNat ((n / 65536) % 256)) .none, .init (UInt8.ofNat ((n / 16777216) % 256)) .none]
    let charS : Ty := { kind := .adt "tests::CharS" .nil, layoutIdx := 1 }
    let bb (v : Value) : MirStepNode :=
      evalBlackBoxProto (mkState [.uninit]) (mkTarget "core::intrinsics::black_box" [charS.kind])
        [mkDecl unitTy, mkDecl charS] cL [] [v] [.uninit] dstLocal0 (.some 1)
    validateTypedBytesForLayoutIdxProto 8 cL 1 (b 55296) = .unsupported ∧
    validateTypedBytesForLayoutIdxProto 8 cL 1 (b 57343) = .unsupported ∧
    validateTypedBytesForLayoutIdxProto 8 cL 1 (b 65) = .valid ∧
    validateTypedBytesForLayoutIdxProto 8 cL 1 (b 57344) = .valid ∧
    validateTypedBytesForLayoutIdxProto 8 cL 1 (b 1114112) = .ub ∧
    validateTypedBytesForLayoutIdxProto 8 cL 3 (b 55296) = .valid ∧
    validateTypedBytesProto 8 [] cL .char (b 55296) = .ub ∧
    isUnsupportedNode (bb (.aggregate 0 [mkU32 55296])) = true ∧
    isUbNode (bb (.aggregate 0 [mkU32 1114112])) = true ∧
    stepLocals? (bb (.aggregate 0 [mkU32 65])) = .some [.init (.aggregate 0 [mkU32 65])] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 16(c): custom-DST pointers and target-dependent widths fail closed instead of being scaled by
the 64-bit structural sizes (`rigidTyLayoutDeterminedProto`):
- `copy`, `raw_eq`, `typed_swap_nonoverlapping` and `ptr_offset_from` at `T = &Packet` (a wide
  16-byte pointer that `RigidTy.adt` cannot reveal) are `.unsupported`, also when a local's layout
  records the wide width; previously they copied / compared / swapped / divided by 8 bytes;
- the same intrinsics at `T = &Hdr` work once a local of type `&Hdr` confirms the thin width
  (`copy` copies 8 bytes, `ptr_offset_from` divides by 8);
- a stack root of type `&Packet` has no trusted extent: `compare_bytes` through it is
  `.unsupported`;
- `black_box` on a wide value at `&Packet` / `*const Packet` is `.unsupported` (was `.ub`), while a
  wide value at `&u32` stays `.ub`;
- on a 32-bit table `black_box::<usize>` accepts a 4-byte value (was `.ub`) and rejects an 8-byte
  one; `copy::<u64>` is `.unsupported` (target-dependent alignment) while `copy::<u32>` copies. -/
theorem custom_dst_pointer_and_target_width_fail_closed :
    let g (id : Nat) (bs : List Nat) : CapturedAllocation :=
      { allocId := id, bytes := bs.map (fun x => .some (UInt8.ofNat x)), relocations := [],
        align := ⟨8⟩, mutability := .mut }
    let s := mkState [.uninit] [] []
      [g 90 [1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], g 91 [3, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0]]
    let pg (id off : Nat) : Value := .ptr { allocId := id, offsetBytes := off } 8
    let cp (decls : List LocalDecl) (ty : RigidTy) : MirStepNode :=
      evalCopyProto s (mkTarget "core::intrinsics::copy" [ty]) decls dstLayouts []
        [pg 90 0, pg 91 0, mkUsize 1] [.uninit] dstLocal0 (.some 1)
    let off (decls : List LocalDecl) (ty : RigidTy) : MirStepNode :=
      evalPtrOffsetFromProto s (mkTarget "core::intrinsics::ptr_offset_from" [ty]) decls dstLayouts []
        [pg 90 8, pg 90 0] [.uninit] dstLocal0 (.some 1) false
    let sw (decls : List LocalDecl) (ty : RigidTy) : MirStepNode :=
      evalTypedSwapNonOverlappingProto s (mkTarget "core::intrinsics::typed_swap_nonoverlapping" [ty])
        decls dstLayouts [] [pg 90 0, pg 91 0] [.uninit] dstLocal0 (.some 1)
    let req (decls : List LocalDecl) (ty : RigidTy) : MirStepNode :=
      evalRawEqProto s (mkTarget "core::intrinsics::raw_eq" [ty]) decls dstLayouts []
        [pg 90 0, pg 91 0] [.uninit] dstLocal0 (.some 1)
    let hdrDecls := [mkDecl unitTy, mkDecl refHdrTy]
    -- stack root of type `&Packet`
    let rootDecls := [mkDecl unitTy, mkDecl refPacketTy]
    let rootLocals : List LocalSlot := [.uninit, .init (.aggregate 0 [mkUsize 4096, mkUsize 3])]
    let bRoot : BorrowEntry := { tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }
    let rRootCmp := evalCompareBytesProto (mkState rootLocals [bRoot]) rootDecls dstLayouts
      [pg 1 0, pg 1 0, mkUsize 8] rootLocals dstLocal0 (.some 1)
    let bb (L : LayoutTable) (ty : RigidTy) (v : Value) : MirStepNode :=
      evalBlackBoxProto (mkState [.uninit]) (mkTarget "core::intrinsics::black_box" [ty])
        [mkDecl unitTy] L [] [v] [.uninit] dstLocal0 (.some 1)
    let wide : Value := .aggregate 0 [mkUsize 4096, mkUsize 3]
    let layouts32 : LayoutTable := { pointerBits := 32, isLittleEndian := true, entries := [] }
    let p32 (id : Nat) : Value := .ptr { allocId := id, offsetBytes := 0 } 4
    let cp32 (ty : RigidTy) : MirStepNode :=
      evalCopyProto s (mkTarget "core::intrinsics::copy" [ty]) [mkDecl unitTy] layouts32 []
        [p32 90, p32 91, .scalar ⟨1, 4⟩] [.uninit] dstLocal0 (.some 1)
    isUnsupportedNode (cp [mkDecl unitTy] (.ref .not packetK)) = true ∧
    isUnsupportedNode (cp [mkDecl unitTy, mkDecl refPacketTy] (.ref .not packetK)) = true ∧
    isUnsupportedNode (cp [mkDecl unitTy] (.array (.ref .not packetK) 2)) = true ∧
    isUnsupportedNode (req [mkDecl boolTy] (.ref .not packetK)) = true ∧
    isUnsupportedNode (sw [mkDecl unitTy] (.ref .not packetK)) = true ∧
    isUnsupportedNode (off [mkDecl isizeTy] (.ref .not packetK)) = true ∧
    globalBytes? (cp hdrDecls (.ref .not hdrK)) 1 =
      .some ([.some 1] ++ List.replicate 7 (.some 0) ++ [.some 4] ++ List.replicate 7 (.some 0)) ∧
    (stepLocals? (off hdrDecls (.ref .not hdrK))).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨1, 8⟩)) ∧
    (stepLocals? (req (mkDecl boolTy :: hdrDecls.tail) (.ref .not hdrK))).bind (fun ls => get? ls 0) =
      .some (.init (.scalar (boolToScalar false))) ∧
    globalBytes? (sw hdrDecls (.ref .not hdrK)) 0 =
      .some ([.some 3] ++ List.replicate 7 (.some 0) ++ [.some 2] ++ List.replicate 7 (.some 0)) ∧
    isUnsupportedNode rRootCmp = true ∧
    isUnsupportedNode (bb dstLayouts (.ref .not packetK) wide) = true ∧
    isUnsupportedNode (bb dstLayouts (.rawPtr .not packetK) wide) = true ∧
    isUbNode (bb dstLayouts (.ref .not (.uint .u32)) wide) = true ∧
    stepLocals? (bb layouts32 (.uint .usize) (.scalar ⟨5, 4⟩)) = .some [.init (.scalar ⟨5, 4⟩)] ∧
    isUbNode (bb layouts32 (.uint .usize) (.scalar ⟨5, 8⟩)) = true ∧
    isUnsupportedNode (cp32 (.uint .u64)) = true ∧
    globalBytes? (cp32 (.uint .u32)) 1 =
      .some ([.some 1, .some 0, .some 0, .some 0, .some 0, .some 0, .some 0, .some 0, .some 4] ++
        List.replicate 7 (.some 0)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 16(d): a `usize` operand that carries pointer provenance (a pointer transmuted to `usize`)
has no modeled integer value, because allocations have no concrete base address: `copy`'s count,
`compare_bytes`'s length and `ptr_mask`'s mask fail closed `.unsupported` (previously `.ub`). A
non-integer mask such as `()` stays `.ub`. -/
theorem provenance_carrying_usize_operands_fail_closed :
    let decls := [mkDecl unitTy, mkDecl u64Ty, mkDecl u64Ty]
    let locals : List LocalSlot := [.uninit, .init (mkUsize 7), .init (mkUsize 9)]
    let b (t l : Nat) : BorrowEntry := { tag := t, targetLocal := l, targetProjection := [], perm := .unique }
    let s := mkState locals [b 1 1, b 2 2]
    let p (tag : Nat) : Value := .ptr { allocId := tag, offsetBytes := 0 } 8
    isUnsupportedNode (evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u8]) decls protoLayouts []
      [p 1, p 2, p 1] locals dstLocal0 (.some 1)) = true ∧
    isUnsupportedNode (evalCompareBytesProto s decls protoLayouts [p 1, p 2, p 1] locals dstLocal0 (.some 1)) = true ∧
    isUnsupportedNode (evalPtrMaskProto s decls protoLayouts [p 1, p 2] locals dstLocal0 (.some 1)) = true ∧
    isUbNode (evalPtrMaskProto s decls protoLayouts [p 1, .unit] locals dstLocal0 (.some 1)) = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- 16(e): `layoutDataMaskProto` scalar-array fast path & padding-preservation soundness:
- `union X { a: [E; 2], b: () }` where `E` is an unpadded initialized scalar (`size = stride = 2`,
  `.scalar (.initialized I16 _)`): hits the fast path -> `[true, true, true, true]`;
- `union UArr { a: [OpaqueScalarUnion; 2], b: () }` where `OpaqueScalarUnion` is a field-layout-less
  `.scalar (.union I16)` union: MUST NOT bypass the fail-closed guard -> `.none` (matching bare union);
- `[PaddedU8; 2]` (`#[repr(C, align(4))] struct PaddedU8(u8)`, `size = 4`, `.scalar (.initialized I8 _)`):
  MUST NOT mark trailing padding bytes `1..3, 5..7` as data -> `[true, false, false, false, true, false, false, false]`;
- stride-padded scalar array (`elemSize = 1, stride = 2, count = 2, size = 4`): MUST keep stride padding
  at bytes `1, 3` (`[true, false, true, false]`), never packing data to the front;
- `union Y { a: [(u8, u16); 2], b: () }`: element padding bytes `1, 5` stay padding. -/
theorem union_scalar_array_fast_path_data_mask :
    let mL : LayoutTable :=
      { pointerBits := 64
        isLittleEndian := true
        entries :=
          [ -- idx 0: `()`
            { size := ⟨0⟩, align := ⟨1⟩, fields := .arbitrary [] [], variants := .single 0,
              backendRepr := .memory, isUninhabited := false },
            -- idx 1: `E`, unpadded initialized scalar (e.g. `u16` or full-width initialized union)
            { size := ⟨2⟩, align := ⟨2⟩, fields := .union 2, variants := .single 0,
              backendRepr := .scalar (.initialized (.int 16 false) ⟨0, 65535⟩), isUninhabited := false },
            -- idx 2: `[E; 2]`
            { size := ⟨4⟩, align := ⟨2⟩, fields := .array ⟨2⟩ 2, variants := .single 0,
              backendRepr := .memory, fieldLayouts := [1], isUninhabited := false },
            -- idx 3: `union X { a: [E; 2], b: () }`
            { size := ⟨4⟩, align := ⟨2⟩, fields := .union 2, variants := .single 0,
              backendRepr := .memory, fieldLayouts := [2, 0], isUninhabited := false },
            -- idx 4: `(u8, u16)` (byte 1 is padding); idx 5: `u8`; idx 6: `u16`
            { size := ⟨4⟩, align := ⟨2⟩, fields := .arbitrary [⟨0⟩, ⟨2⟩] [0, 1], variants := .single 0,
              backendRepr := .memory, fieldLayouts := [5, 6], isUninhabited := false },
            { size := ⟨1⟩, align := ⟨1⟩, fields := .primitive, variants := .single 0,
              backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩), isUninhabited := false },
            { size := ⟨2⟩, align := ⟨2⟩, fields := .primitive, variants := .single 0,
              backendRepr := .scalar (.initialized (.int 16 false) ⟨0, 65535⟩), isUninhabited := false },
            -- idx 7: `[(u8, u16); 2]`; idx 8: `union Y { a: [(u8, u16); 2], b: () }`
            { size := ⟨8⟩, align := ⟨2⟩, fields := .array ⟨4⟩ 2, variants := .single 0,
              backendRepr := .memory, fieldLayouts := [4], isUninhabited := false },
            { size := ⟨8⟩, align := ⟨2⟩, fields := .union 2, variants := .single 0,
              backendRepr := .memory, fieldLayouts := [7, 0], isUninhabited := false },
            -- idx 9: `OpaqueScalarUnion` (`.scalar (.union I16)` without `fieldLayouts`)
            { size := ⟨2⟩, align := ⟨2⟩, fields := .union 2, variants := .single 0,
              backendRepr := .scalar (.union (.int 16 false)), isUninhabited := false },
            -- idx 10: `[OpaqueScalarUnion; 2]`; idx 11: `union UArr { a: [OpaqueScalarUnion; 2], b: () }`
            { size := ⟨4⟩, align := ⟨2⟩, fields := .array ⟨2⟩ 2, variants := .single 0,
              backendRepr := .memory, fieldLayouts := [9], isUninhabited := false },
            { size := ⟨4⟩, align := ⟨2⟩, fields := .union 2, variants := .single 0,
              backendRepr := .memory, fieldLayouts := [10, 0], isUninhabited := false },
            -- idx 12: `#[repr(C, align(4))] struct PaddedU8(u8)` (size 4, scalar width 1!)
            { size := ⟨4⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩] [0], variants := .single 0,
              backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩), isUninhabited := false },
            -- idx 13: `[PaddedU8; 2]`
            { size := ⟨8⟩, align := ⟨4⟩, fields := .array ⟨4⟩ 2, variants := .single 0,
              backendRepr := .memory, fieldLayouts := [12], isUninhabited := false },
            -- idx 14: stride-padded array (`elemSize = 1, stride = 2, count = 2, size = 4`)
            { size := ⟨4⟩, align := ⟨2⟩, fields := .array ⟨2⟩ 2, variants := .single 0,
              backendRepr := .memory, fieldLayouts := [5], isUninhabited := false } ] }
    layoutDataMaskProto 8 mL 3 = .some [true, true, true, true] ∧
    layoutDataMaskProto 8 mL 8 = .some [true, false, true, true, true, false, true, true] ∧
    layoutDataMaskProto 8 mL 10 = .none ∧
    layoutDataMaskProto 8 mL 11 = .none ∧
    layoutDataMaskProto 8 mL 13 = .some [true, false, false, false, true, false, false, false] ∧
    layoutDataMaskProto 8 mL 14 = .some [true, false, true, false] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 16(f): non-vacuity witnesses for the pass-B3 universally quantified prototype theorems
(`isUninhabitedRigidTyProto_pointer_false`, `charShapedSurrogateProto_not_valid_char` with a
satisfiable premise, and `rigidTyLayoutDeterminedProto_non64_pointer_false` with a satisfiable
32-bit width premise). -/
theorem b3_universal_theorems_non_vacuous :
    (isUninhabitedRigidTyProto [] protoLayouts 8 (.ref .not .never) = false ∧
      isUninhabitedRigidTyProto [] protoLayouts 8 (.rawPtr .not .never) = false) ∧
    charShapedSurrogateProto (.int 32 false) ⟨0, 1114111⟩ 55296 = true ∧
    isValidCharCode 55296 = false ∧
    (rigidTyLayoutDeterminedProto [] { pointerBits := 32, isLittleEndian := true, entries := [] }
        true (7 + 1) (.ref .not (.uint .u8)) = false ∧
      rigidTyLayoutDeterminedProto [] { pointerBits := 32, isLittleEndian := true, entries := [] }
        true (7 + 1) (.rawPtr .not (.uint .u8)) = false ∧
      rigidTyLayoutDeterminedProto [] { pointerBits := 32, isLittleEndian := true, entries := [] }
        true (7 + 1) (.uint .usize) = false ∧
      rigidTyLayoutDeterminedProto [] { pointerBits := 32, isLittleEndian := true, entries := [] }
        true (7 + 1) (.int .isize) = false) := by
  refine ⟨isUninhabitedRigidTyProto_pointer_false [] protoLayouts 8 .not .never, rfl,
    charShapedSurrogateProto_not_valid_char (.int 32 false) ⟨0, 1114111⟩ 55296 rfl,
    rigidTyLayoutDeterminedProto_non64_pointer_false [] { pointerBits := 32, isLittleEndian := true, entries := [] }
      true 7 .not (.uint .u8) rfl⟩

/-! ## Section 17: Pass A3 Adversarial Critique-and-Fix Regression Tests -/

/-- 17(a): 32-bit tag-window sub-place sizing & non-64-bit root alignment (`exactTyByteSizeProto?`
and `exactRootAllocAlignProto?`):
- On a 32-bit `LayoutTable`, borrowing `&s.len` (`usize`, field 0) of `struct S { len: usize, x: u32 }`
  gives tag window `[0, 4)` (NOT `[0, 8)` from 64-bit `Bytes.rigidTyByteSize`!), so writing/reading
  `[4, 8)` (`s.x`) through `&s.len` fails closed `.unsupported` instead of escaping into sibling `s.x`,
  while reading `[0, 4)` succeeds;
- On a 32-bit `LayoutTable`, a `u64` local WITHOUT an explicit layout entry has undetermined alignment:
  `checkPtrArgAlignedProto` at `reqAlign = 8` returns `.unsupported` and `ptr_mask(p_off_5, !7)` fails
  closed `.unsupported` (previously assumed 8-byte alignment);
- WITH an explicit 32-bit `i686` layout (`size = 8, align = 4`), `checkPtrArgAlignedProto` at
  `reqAlign = 8` deterministically faults `.ub` (`4 < 8`), `ptr_mask(p_off_5, !3)` succeeds with
  offset `4`, and `ptr_mask(p_off_5, !7)` fails closed `.unsupported`. -/
theorem tag_window_and_root_align_on_32bit_table :
    let l32 : LayoutTable :=
      { pointerBits := 32
        isLittleEndian := true
        entries :=
          [ -- idx 0: `()`
            { size := ⟨0⟩, align := ⟨1⟩, fields := .arbitrary [] [], variants := .single 0,
              backendRepr := .memory, isUninhabited := false },
            -- idx 1: `struct S32 { len: usize, x: u32 }` (size 8, align 4, offsets [0, 4])
            { size := ⟨8⟩, align := ⟨4⟩, fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], variants := .single 0,
              backendRepr := .memory, fieldLayouts := [2, 3], isUninhabited := false },
            -- idx 2: 32-bit `usize` (size 4, align 4)
            { size := ⟨4⟩, align := ⟨4⟩, fields := .primitive, variants := .single 0,
              backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩), isUninhabited := false },
            -- idx 3: `u32` (size 4, align 4)
            { size := ⟨4⟩, align := ⟨4⟩, fields := .primitive, variants := .single 0,
              backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩), isUninhabited := false },
            -- idx 4: 32-bit `i686` `u64` (size 8, align 4!)
            { size := ⟨8⟩, align := ⟨4⟩, fields := .primitive, variants := .single 0,
              backendRepr := .scalar (.initialized (.int 64 false) ⟨0, 18446744073709551615⟩), isUninhabited := false } ] }
    let s32Ty : Ty := { kind := .adt "tests::S32" [.uint .usize, .uint .u32], layoutIdx := 1 }
    let s32Decls := [mkDecl i32Ty, mkDecl s32Ty]
    let s32Locals : List LocalSlot := [.uninit, .init (.aggregate 0 [.scalar ⟨11, 4⟩, mkU32 22])]
    let bLen : BorrowEntry :=
      { tag := 1, targetLocal := 1, targetProjection := [.field 0 { kind := .uint .usize, layoutIdx := 0 }],
        perm := .unique }
    let s32State := mkState s32Locals [bLen]
    -- Reading [0, 4) through `&s.len` succeeds; reading [4, 8) (`s.x`) through `&s.len` fails closed!
    let rInWin := evalCompareBytesProto s32State s32Decls l32
      [.ptr { allocId := 1, offsetBytes := 0 } 4, .ptr { allocId := 1, offsetBytes := 0 } 4, .scalar ⟨4, 4⟩]
      s32Locals dstLocal0 (.some 1)
    let rEscapeSibling := evalCompareBytesProto s32State s32Decls l32
      [.ptr { allocId := 1, offsetBytes := 4 } 4, .ptr { allocId := 1, offsetBytes := 4 } 4, .scalar ⟨4, 4⟩]
      s32Locals dstLocal0 (.some 1)
    -- 32-bit `u64` local without explicit layout (`layoutIdx = 0`) vs explicit `i686` layout (`layoutIdx = 4`):
    let u64NoLayoutDecls := [mkDecl rawConstU8Ty, mkDecl u64Ty]
    let u64I686Ty : Ty := { kind := .uint .u64, layoutIdx := 4 }
    let u64I686Decls := [mkDecl rawConstU8Ty, mkDecl u64I686Ty]
    let u64Locals : List LocalSlot := [.uninit, .init (.scalar ⟨99, 8⟩)]
    let bU64 : BorrowEntry := { tag := 5, targetLocal := 1, targetProjection := [], perm := .unique }
    let sU64 := mkState u64Locals [bU64]
    let pU64Off0 : PtrArgProto := .prov { allocId := 5, offsetBytes := 0 }
    let pU64Off5 : Value := .ptr { allocId := 5, offsetBytes := 5 } 4
    let maskNot3_32 : Value := .scalar ⟨4294967292, 4⟩
    let maskNot7_32 : Value := .scalar ⟨4294967288, 4⟩
    (stepLocals? rInWin).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨0, 4⟩)) ∧
    isUnsupportedNode rEscapeSibling = true ∧
    (match checkPtrArgAlignedProto sU64 u64Locals u64NoLayoutDecls l32 pU64Off0 8 with
     | .unsupported => true | _ => false) = true ∧
    isUnsupportedNode (evalPtrMaskProto sU64 u64NoLayoutDecls l32 [pU64Off5, maskNot7_32] u64Locals dstLocal0 (.some 1)) = true ∧
    (match checkPtrArgAlignedProto sU64 u64Locals u64I686Decls l32 pU64Off0 8 with
     | .ub => true | _ => false) = true ∧
    (stepLocals? (evalPtrMaskProto sU64 u64I686Decls l32 [pU64Off5, maskNot3_32] u64Locals dstLocal0 (.some 1))).bind
      (fun ls => get? ls 0) = .some (.init (.ptr { allocId := 5, offsetBytes := 4 } 4)) ∧
    isUnsupportedNode (evalPtrMaskProto sU64 u64I686Decls l32 [pU64Off5, maskNot7_32] u64Locals dstLocal0 (.some 1)) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 17(b): `decodeUsizeArgProto?` closes B3's wildcard `.ptr` UB-masking regression, handles
unbacked `allocId = 0` integer counts/masks, and completes ZST copies with provenance counts:
- malformed pointer arguments (`.unit`) and null pointers in `compare_bytes` STILL fault `.ub`
  even when `count`/`mask` carries real pointer provenance;
- wrong-width `.ptr _ 4` mask on 64-bit faults `.ub`;
- unbacked `allocId = 0` `.ptr` counts/masks decode to their wrapped integer offsets (`copy` count 0,
  `compare_bytes` count 0, `ptr_mask` with `!7`);
- `copy::<()>` (ZST) with real provenance `count` succeeds (`0 * count = 0`), whereas misaligned
  `copy::<u32>(addr=1, dst, prov_count)` still faults `.ub`. -/
theorem decode_usize_arg_malformed_ptr_ub_unbacked_zero_and_zst_prov :
    let decls := [mkDecl unitTy, mkDecl aligned16BufTy, mkDecl aligned16BufTy]
    let locals : List LocalSlot := [.uninit, .init .unit, .init .unit]
    let b (t l : Nat) : BorrowEntry := { tag := t, targetLocal := l, targetProjection := [], perm := .unique }
    let s := mkState locals [b 1 1, b 2 2]
    let p (tag off : Nat) : Value := .ptr { allocId := tag, offsetBytes := off } 8
    let zeroProv (off : Nat) : Value := .ptr { allocId := 0, offsetBytes := off } 8
    isUbNode (evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u8]) decls protoLayouts []
      [.unit, p 2 0, p 1 0] locals dstLocal0 (.some 1)) = true ∧
    isUbNode (evalCompareBytesProto s decls protoLayouts [.unit, p 2 0, p 1 0] locals dstLocal0 (.some 1)) = true ∧
    isUbNode (evalCompareBytesProto s decls protoLayouts [mkUsize 0, p 2 0, p 1 0] locals dstLocal0 (.some 1)) = true ∧
    isUbNode (evalPtrMaskProto s decls protoLayouts [.unit, p 1 0] locals dstLocal0 (.some 1)) = true ∧
    isUbNode (evalPtrMaskProto s decls protoLayouts [p 1 0, .ptr { allocId := 1, offsetBytes := 0 } 4] locals dstLocal0 (.some 1)) = true ∧
    (stepLocals? (evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u8]) decls protoLayouts []
      [p 1 0, p 2 0, zeroProv 0] locals dstLocal0 (.some 1))).bind (fun ls => get? ls 0) = .some (.init .unit) ∧
    (stepLocals? (evalCompareBytesProto s [mkDecl i32Ty, mkDecl aligned16BufTy, mkDecl aligned16BufTy] protoLayouts
      [p 1 0, p 2 0, zeroProv 0] locals dstLocal0 (.some 1))).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨0, 4⟩)) ∧
    (stepLocals? (evalPtrMaskProto s [mkDecl rawConstU8Ty, mkDecl aligned16BufTy, mkDecl aligned16BufTy] protoLayouts
      [p 1 13, zeroProv 18446744073709551608] locals dstLocal0 (.some 1))).bind (fun ls => get? ls 0) =
      .some (.init (.ptr { allocId := 1, offsetBytes := 8 } 8)) ∧
    (stepLocals? (evalCopyProto s (mkTarget "core::intrinsics::copy" [.tuple []]) decls protoLayouts []
      [p 1 0, p 2 0, p 1 0] locals dstLocal0 (.some 1))).bind (fun ls => get? ls 0) = .some (.init .unit) ∧
    isUbNode (evalCopyProto s (mkTarget "core::intrinsics::copy" [.uint .u32]) decls protoLayouts []
      [mkUsize 1, p 2 0, p 1 0] locals dstLocal0 (.some 1)) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 17(c): custom-DST / wide-tuple validation & target-aware slice metadata sizing:
- `ptrPointeeMayBeUnsizedProto` recurses through tuple tails with `.param`/`.alias` (`(u8, T)` -> `true`);
- `black_box` and `validateTypedBytesProto` reject a thin 8-byte pointer for confirmed-wide `&Packet`
  and for known-wide `&(u8, [u8])` as `.ub` (previously `.valid`!), fail closed `.unsupported` on
  unconfirmed thin `&Packet`, reject null wide `&Packet` and null wide `&(u8, [u8])` as `.ub`
  (previously `.unsupported`!), accept thin `&Hdr` when confirmed by `refHdrTy`, and accept valid raw
  wide `*const (u8, [u8])`;
- 32-bit `&[usize]` slice metadata uses `elemSize = 4` (so `len = 2^28` is `.valid`, NOT false UB
  from 64-bit `elemSize = 8`, while `len = 2^29` is `.ub`), and 64-bit `&[&Packet]` uses `elemSize = 16`
  when `refPacketTy` is present (so `len = 2^59` is `.ub`, NOT missed UB from `elemSize = 8`, and
  unconfirmed `&[&Packet]` fails closed `.unsupported`). -/
theorem custom_dst_wide_tuple_and_32bit_slice_meta_validity :
    let s0 := mkState [.uninit]
    let bb (decls : List LocalDecl) (L : LayoutTable) (ty : RigidTy) (v : Value) : MirStepNode :=
      evalBlackBoxProto s0 (mkTarget "core::intrinsics::black_box" [ty]) decls L [] [v] [.uninit] dstLocal0 (.some 1)
    let pktDecls := [mkDecl unitTy, mkDecl refPacketTy]
    let hdrDecls := [mkDecl unitTy, mkDecl refHdrTy]
    let wideTupleK : RigidTy := .tuple [.uint .u8, .slice (.uint .u8)]
    let layouts32 : LayoutTable := { pointerBits := 32, isLittleEndian := true, entries := [] }
    let nonNull4 : List AbstractByte := [.init 1 .none, .init 0 .none, .init 0 .none, .init 0 .none]
    let len2Pow28Bytes : List AbstractByte := [.init 0 .none, .init 0 .none, .init 0 .none, .init 16 .none]
    let len2Pow29Bytes : List AbstractByte := [.init 0 .none, .init 0 .none, .init 0 .none, .init 32 .none]
    let nonNull8 : List AbstractByte := [.init 1 .none] ++ List.replicate 7 (.init 0 .none)
    let null8 : List AbstractByte := List.replicate 8 (.init 0 .none)
    ptrPointeeMayBeUnsizedProto (.tuple [.uint .u8, .param 0 "T"]) = true ∧
    ptrPointeeMayBeUnsizedProto (.tuple [.uint .u8, .alias "Item" []]) = true ∧
    isUbNode (bb pktDecls dstLayouts (.ref .not packetK) (mkUsize 4096)) = true ∧
    isUnsupportedNode (bb [mkDecl unitTy] dstLayouts (.ref .not packetK) (mkUsize 4096)) = true ∧
    isUbNode (bb pktDecls dstLayouts (.ref .not packetK) (.aggregate 0 [mkUsize 0, mkUsize 3])) = true ∧
    stepLocals? (bb hdrDecls dstLayouts (.ref .not hdrK) (mkUsize 4096)) = .some [.init (mkUsize 4096)] ∧
    isUbNode (bb [mkDecl unitTy] protoLayouts (.ref .not wideTupleK) (mkUsize 4096)) = true ∧
    isUbNode (bb [mkDecl unitTy] protoLayouts (.ref .not wideTupleK) (.aggregate 0 [mkUsize 0, mkUsize 3])) = true ∧
    isUbNode (bb [mkDecl unitTy] protoLayouts (.ref .not wideTupleK)
      (.aggregate 0 [mkUsize 4096, mkUsize 9223372036854775808])) = true ∧
    stepLocals? (bb [mkDecl unitTy] protoLayouts (.rawPtr .not wideTupleK) (.aggregate 0 [mkUsize 0, mkUsize 3])) =
      .some [.init (.aggregate 0 [mkUsize 0, mkUsize 3])] ∧
    validateTypedBytesProto 8 pktDecls dstLayouts (.ref .not packetK) nonNull8 = .ub ∧
    validateTypedBytesProto 8 pktDecls dstLayouts (.ref .not packetK) (null8 ++ nonNull8) = .ub ∧
    validateTypedBytesProto 8 pktDecls dstLayouts (.ref .not packetK) (nonNull8 ++ nonNull8) = .unsupported ∧
    validateTypedBytesProto 8 [] protoLayouts (.ref .not wideTupleK) nonNull8 = .ub ∧
    validateTypedBytesProto 8 [] protoLayouts (.ref .not wideTupleK) (null8 ++ nonNull8) = .ub ∧
    stepLocals? (bb [mkDecl unitTy] layouts32 (.ref .not (.slice (.uint .usize)))
      (.aggregate 0 [.scalar ⟨4096, 4⟩, .scalar ⟨268435456, 4⟩])) =
      .some [.init (.aggregate 0 [.scalar ⟨4096, 4⟩, .scalar ⟨268435456, 4⟩])] ∧
    isUbNode (bb [mkDecl unitTy] layouts32 (.ref .not (.slice (.uint .usize)))
      (.aggregate 0 [.scalar ⟨4096, 4⟩, .scalar ⟨536870912, 4⟩])) = true ∧
    validateTypedBytesProto 8 [] layouts32 (.ref .not (.slice (.uint .usize))) (nonNull4 ++ len2Pow28Bytes) = .valid ∧
    validateTypedBytesProto 8 [] layouts32 (.ref .not (.slice (.uint .usize))) (nonNull4 ++ len2Pow29Bytes) = .ub ∧
    isUbNode (bb pktDecls dstLayouts (.ref .not (.slice (.ref .not packetK)))
      (.aggregate 0 [mkUsize 4096, mkUsize 576460752303423488])) = true ∧
    isUnsupportedNode (bb [mkDecl unitTy] dstLayouts (.ref .not (.slice (.ref .not packetK)))
      (.aggregate 0 [mkUsize 4096, mkUsize 576460752303423488])) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 17(d): `ptr_offset_from::<u64>` precision on 32-bit targets (`withAlign := false`) AND
`const_eval_select` runtime dispatch to all 8 new core memory & pointer intrinsics (verifying
`evalDirectRustIntrinsicProto?` routes `const_eval_select` to every new intrinsic instead of
falling through to `MirStepNode.extCall`, including pointee-`T` inference from `ARG`). -/
theorem ptr_offset_from_u64_on_32bit_and_const_eval_select_all_8_intrinsics :
    let layouts32 : LayoutTable := { pointerBits := 32, isLittleEndian := true, entries := [] }
    let g16 : CapturedAllocation :=
      { allocId := 80, bytes := List.replicate 16 (.some 0), relocations := [], align := ⟨8⟩, mutability := .mut }
    let s32 := mkState [.uninit] [] [] [g16]
    let p32 (off : Nat) : Value := .ptr { allocId := 80, offsetBytes := off } 4
    let rOff32Signed := evalPtrOffsetFromProto s32 (mkTarget "core::intrinsics::ptr_offset_from" [.uint .u64])
      [mkDecl isizeTy] layouts32 [] [p32 8, p32 0] [.uninit] dstLocal0 (.some 1) false
    let rOff32Unsigned := evalPtrOffsetFromProto s32 (mkTarget "core::intrinsics::ptr_offset_from_unsigned" [.uint .u64])
      [mkDecl usizeTy] layouts32 [] [p32 8, p32 0] [.uninit] dstLocal0 (.some 1) true
    let rOff32Usize := evalPtrOffsetFromProto s32 (mkTarget "core::intrinsics::ptr_offset_from" [.uint .usize])
      [mkDecl isizeTy] layouts32 [] [p32 4, p32 0] [.uninit] dstLocal0 (.some 1) false
    -- `const_eval_select` runtime dispatch to all 8 new intrinsics:
    let gA : CapturedAllocation :=
      { allocId := 90, bytes := [.some 10, .some 0, .some 0, .some 0, .some 20, .some 0, .some 0, .some 0],
        relocations := [], align := ⟨4⟩, mutability := .mut }
    let gB : CapturedAllocation :=
      { allocId := 91, bytes := [.some 30, .some 0, .some 0, .some 0, .some 40, .some 0, .some 0, .some 0],
        relocations := [], align := ⟨4⟩, mutability := .mut }
    let sg := mkState [.uninit] [] [] [gA, gB]
    let pg (id off : Nat) : Value := .ptr { allocId := id, offsetBytes := off } 8
    let callSelect (argTys : List RigidTy) (rtPath : DefPath) (rtTypeArgs : List RigidTy)
        (args : List Value) (dstDecl : LocalDecl) : Option MirStepNode :=
      let argTupleTy : RigidTy := .tuple argTys
      let rtFnTy : RigidTy := .fnDef rtPath rtTypeArgs
      let ctFnTy : RigidTy := .fnDef "tests::ct_fn" []
      let target := mkTarget "core::intrinsics::const_eval_select" [argTupleTy, ctFnTy, rtFnTy, dstDecl.ty.kind]
      let rtOp : Operand := .constant { ty := { kind := rtFnTy, layoutIdx := 0 }, val := .zeroSized }
      let ctOp : Operand := .constant { ty := { kind := ctFnTy, layoutIdx := 0 }, val := .zeroSized }
      let tupOp : Operand := .constant { ty := { kind := argTupleTy, layoutIdx := 0 }, val := .zeroSized }
      evalDirectRustIntrinsicProto? sg .none target [dstDecl] protoLayouts
        [tupOp, ctOp, rtOp] [.aggregate 0 args, .unit, .unit] [.uninit] dstLocal0 (.some 1) .continue_
    -- 1. copy<u32> (typeArg inferred from `*const u32` via `isPtrPointeeIntrinsicProtoKind`)
    let rSelCopy := callSelect [.rawPtr .not (.uint .u32), .rawPtr .mut (.uint .u32), .uint .usize]
      "core::intrinsics::copy" [] [pg 90 0, pg 91 0, mkUsize 1] (mkDecl unitTy)
    -- 2. compare_bytes
    let rSelCmp := callSelect [.rawPtr .not (.uint .u8), .rawPtr .not (.uint .u8), .uint .usize]
      "core::intrinsics::compare_bytes" [] [pg 90 0, pg 91 0, mkUsize 4] (mkDecl i32Ty)
    -- 3. raw_eq<u32> (typeArg inferred from `&u32`)
    let rSelRawEq := callSelect [.ref .not (.uint .u32), .ref .not (.uint .u32)]
      "core::intrinsics::raw_eq" [] [pg 90 0, pg 90 0] (mkDecl boolTy)
    -- 4. typed_swap_nonoverlapping<u32> (typeArg inferred from `*mut u32`)
    let rSelSwap := callSelect [.rawPtr .mut (.uint .u32), .rawPtr .mut (.uint .u32)]
      "core::intrinsics::typed_swap_nonoverlapping" [] [pg 90 0, pg 91 0] (mkDecl unitTy)
    -- 5. ptr_offset_from<u32>
    let rSelOffS := callSelect [.rawPtr .not (.uint .u32), .rawPtr .not (.uint .u32)]
      "core::intrinsics::ptr_offset_from" [] [pg 90 4, pg 90 0] (mkDecl isizeTy)
    -- 6. ptr_offset_from_unsigned<u32>
    let rSelOffU := callSelect [.rawPtr .not (.uint .u32), .rawPtr .not (.uint .u32)]
      "core::intrinsics::ptr_offset_from_unsigned" [] [pg 90 4, pg 90 0] (mkDecl usizeTy)
    -- 7. ptr_mask<u8>
    let rSelMask := callSelect [.rawPtr .not (.uint .u8), .uint .usize]
      "core::intrinsics::ptr_mask" [] [pg 90 7, mkUsize 18446744073709551612] (mkDecl rawConstU8Ty)
    -- 8. black_box<u32>
    let rSelBb := callSelect [.uint .u32]
      "core::intrinsics::black_box" [] [mkU32 42] (mkDecl u32Ty)
    (stepLocals? rOff32Signed).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨1, 4⟩)) ∧
    (stepLocals? rOff32Unsigned).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨1, 4⟩)) ∧
    isUnsupportedNode rOff32Usize = true ∧
    (rSelCopy.bind (fun n => globalBytes? n 1)) =
      .some [.some 10, .some 0, .some 0, .some 0, .some 40, .some 0, .some 0, .some 0] ∧
    (rSelCmp.bind stepLocals?).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨4294967295, 4⟩)) ∧
    (rSelRawEq.bind stepLocals?).bind (fun ls => get? ls 0) = .some (.init (.scalar (boolToScalar true))) ∧
    (rSelSwap.bind (fun n => globalBytes? n 0)) =
      .some [.some 30, .some 0, .some 0, .some 0, .some 20, .some 0, .some 0, .some 0] ∧
    (rSelOffS.bind stepLocals?).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨1, 8⟩)) ∧
    (rSelOffU.bind stepLocals?).bind (fun ls => get? ls 0) = .some (.init (.scalar ⟨1, 8⟩)) ∧
    (rSelMask.bind stepLocals?).bind (fun ls => get? ls 0) = .some (.init (pg 90 4)) ∧
    (rSelBb.bind stepLocals?).bind (fun ls => get? ls 0) = .some (.init (mkU32 42)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 17(e): non-vacuity witnesses for the pass-A3 universally quantified prototype theorems
(`decodeUsizeArgProto?_unbacked_zero_ok_and_prov_unsupported`,
`layoutDataMaskProto_scalar_array_exact`, and `layoutDataMaskProto_array_union_no_fields_none`). -/
theorem a3_universal_theorems_non_vacuous :
    let mProv : Memory :=
      { emptyMemory with borrows := [{ tag := 7, targetLocal := 1, targetProjection := [], perm := .unique }] }
    let elemInit : TypeLayout :=
      { size := ⟨2⟩, align := ⟨2⟩, fields := .primitive, variants := .single 0,
        backendRepr := .scalar (.initialized (.int 16 false) ⟨0, 65535⟩), isUninhabited := false }
    let arrInit : TypeLayout :=
      { size := ⟨4⟩, align := ⟨2⟩, fields := .array ⟨2⟩ 2, variants := .single 0,
        backendRepr := .memory, fieldLayouts := [0], isUninhabited := false }
    let elemUnion : TypeLayout :=
      { size := ⟨2⟩, align := ⟨2⟩, fields := .union 2, variants := .single 0,
        backendRepr := .scalar (.union (.int 16 false)), isUninhabited := false }
    let arrUnion : TypeLayout :=
      { size := ⟨4⟩, align := ⟨2⟩, fields := .array ⟨2⟩ 2, variants := .single 0,
        backendRepr := .memory, fieldLayouts := [2], isUninhabited := false }
    let lTab : LayoutTable :=
      { pointerBits := 64, isLittleEndian := true, entries := [elemInit, arrInit, elemUnion, arrUnion] }
    decodeUsizeArgProto? emptyMemory 8 (.ptr { allocId := 0, offsetBytes := 12 } 8) = .ok 12 ∧
    decodeUsizeArgProto? mProv 8 (.ptr { allocId := 7, offsetBytes := 0 } 8) = .unsupported ∧
    decodeUsizeArgProto? mProv 8 (.ptr { allocId := 7, offsetBytes := 0 } 4) = .ub ∧
    layoutDataMaskProto 2 lTab 1 = .some [true, true, true, true] ∧
    layoutDataMaskProto 3 lTab 3 = .none := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (decodeUsizeArgProto?_unbacked_zero_ok_and_prov_unsupported
      emptyMemory 8 8 { allocId := 0, offsetBytes := 12 }).1 rfl
  · exact (decodeUsizeArgProto?_unbacked_zero_ok_and_prov_unsupported
      { emptyMemory with borrows := [{ tag := 7, targetLocal := 1, targetProjection := [], perm := .unique }] }
      8 8 { allocId := 7, offsetBytes := 0 }).2.1 rfl
  · exact (decodeUsizeArgProto?_unbacked_zero_ok_and_prov_unsupported
      { emptyMemory with borrows := [{ tag := 7, targetLocal := 1, targetProjection := [], perm := .unique }] }
      8 4 { allocId := 7, offsetBytes := 0 }).2.2 (by decide)
  · exact layoutDataMaskProto_scalar_array_exact 1 _ 1 0 0 0 2
      { size := ⟨4⟩, align := ⟨2⟩, fields := .array ⟨2⟩ 2, variants := .single 0,
        backendRepr := .memory, fieldLayouts := [0], isUninhabited := false }
      { size := ⟨2⟩, align := ⟨2⟩, fields := .primitive, variants := .single 0,
        backendRepr := .scalar (.initialized (.int 16 false) ⟨0, 65535⟩), isUninhabited := false }
      ⟨2⟩ (.int 16 false) ⟨0, 65535⟩
      rfl rfl rfl (by decide) rfl rfl rfl rfl rfl (by decide) rfl rfl
  · exact layoutDataMaskProto_array_union_no_fields_none 1 _ 3 2 0 0 2 2
      { size := ⟨4⟩, align := ⟨2⟩, fields := .array ⟨2⟩ 2, variants := .single 0,
        backendRepr := .memory, fieldLayouts := [2], isUninhabited := false }
      { size := ⟨2⟩, align := ⟨2⟩, fields := .union 2, variants := .single 0,
        backendRepr := .scalar (.union (.int 16 false)), isUninhabited := false }
      ⟨2⟩ (.int 16 false)
      rfl rfl rfl (by decide) rfl rfl rfl rfl rfl rfl

/-! ## Section 18: Non-Vacuity Witnesses & Mechanical Standard-Axiom Gate -/

/--
Non-vacuity witness instantiating EVERY universally quantified theorem in
`Anneal.TcbCoreMemPtrIntrinsicsPrototype` with concrete, satisfiable inputs:
1. `compareUnsignedBytesProto_eq_miriBytesCompareSpec` on `[0x80]` vs `[0x7f]`;
2. `ptrMask_baseAddr_invariant` on 64-bit `m = 3` (`align = 8`), `baseAddr = 0x10000`, `relOff = 13`, `mask = !7`;
3. `evalPtrMaskValueProto_preserves_provenance`, `evalPtrMaskValueProto_allOnes_identity`, and
   `evalPtrMaskValueProto_symbolic_eq_concrete` on concrete stack borrow tag `7` with `baseAddr = 0x20008`;
4. `evalPtrOffsetFromDistanceProto_zst_ub`, `_unsigned_underflow_ub`, `_isizeMin_ub`;
5. `evalBlackBoxProto_valid_direct_dest` on `u32 = 42`;
6. the `lean-miri` mirror theorems `evalPtrOffsetFromDistanceProto_eq_miriSpec`,
   `miriPtrOffsetFromDistanceSpec_eq_checkedDistanceProto`, and
   `ptrOffsetFromExactDivProto_eq_miriSpec` on 64-bit offsets `4` and `12` over `u32`
   (`-8` bytes, `-2` elements), with the mirror itself evaluated on the `isize::MIN`, unsigned
   underflow, inexact-division, and ZST cases so its UB branches are reachable;
7. `evalPtrOffsetFromDistanceProto_same_offset`, `resolvePtrOffsetFromOffsetsProto_same_pointer`
   (on a dead-allocation pointer), and `abstractBytesRefineProto_refl`;
8. `misaligned_offset_has_misaligned_placement` on `(a = 1, r = 2, off = 2)` and
   `evalDirectRustIntrinsicProto?_constEvalSelect_diverging_not_ub`.
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
    (evalPtrMaskValueProto
        (mkState [.uninit, .init .unit] [{ tag := 7, targetLocal := 1, targetProjection := [], perm := .unique }])
        [.uninit, .init .unit] [mkDecl rawConstU8Ty, mkDecl aligned16BufTy] protoLayouts
        (.prov { allocId := 7, offsetBytes := 13 }) ⟨scalarModulus 8 - 1, 8⟩ .none =
      .ok (.ptr { allocId := 7, offsetBytes := 13 } 8)) ∧
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
      true) ∧
    (∃ base, 0 < base ∧ base % 2 ^ 1 = 0 ∧ (base + 2) % 2 ^ 2 ≠ 0) ∧
    (evalDirectRustIntrinsicProto? (mkState [.uninit]) .none
      (mkTarget "core::intrinsics::const_eval_select" []) [mkDecl unitTy] protoLayouts [] []
      [.uninit] dstLocal0 .none .continue_ = .some MirStepNode.unsupported) ∧
    (abstractBytesRefineProto
      [.init 1 .none, .uninit, .uninit, .uninit, .init 10 .none, .init 0 .none, .init 0 .none, .init 0 .none]
      [.init 1 .none, .init 170 .none, .init 170 .none, .init 170 .none,
       .init 10 .none, .init 0 .none, .init 0 .none, .init 0 .none] = true) ∧
    (1 ≤ ((1 + 4 - 1) / 4) * 4 ∧ ((1 + 4 - 1) / 4) * 4 < 1 + 4 ∧ 1 + 4 ≤ ((1 + 4 - 1) / 4) * 4 + 4) := by
  refine ⟨compareUnsignedBytesProto_eq_miriBytesCompareSpec [128] [127], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      rfl rfl ⟨3, rfl⟩ (by decide) (by decide) (by decide) rfl
  · exact evalPtrMaskValueProto_allOnes_identity
      (mkState [.uninit, .init .unit] [{ tag := 7, targetLocal := 1, targetProjection := [], perm := .unique }])
      [.uninit, .init .unit] [mkDecl rawConstU8Ty, mkDecl aligned16BufTy] protoLayouts
      { allocId := 7, offsetBytes := 13 } rfl (by decide)
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
  · exact misaligned_offset_has_misaligned_placement 1 2 2 (by decide)
  · exact evalDirectRustIntrinsicProto?_constEvalSelect_diverging_not_ub
      (mkState [.uninit]) .none [] [mkDecl unitTy] protoLayouts [] [] [.uninit] dstLocal0 .continue_
  · exact resetTypedPaddingForLayoutIdxProto_refines 8 protoLayouts 1
      [.init 1 .none, .init 170 .none, .init 170 .none, .init 170 .none,
       .init 10 .none, .init 0 .none, .init 0 .none, .init 0 .none]
      [.init 1 .none, .uninit, .uninit, .uninit, .init 10 .none, .init 0 .none, .init 0 .none, .init 0 .none]
      rfl
  · exact scalarPair_bOffset_lt_sum_and_separates_trailing_zst 1 4 4 (by decide) (by decide)

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
    (∀ a r off, off % 2 ^ r ≠ 0 → ∃ base, 0 < base ∧ base % 2 ^ a = 0 ∧ (base + off) % 2 ^ r ≠ 0) ∧
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
  have _ := ranged_borrow_split_at_mut_no_over_invalidation
  have _ := typed_swap_resets_padding_in_stack_byte_buffer_and_union_global
  have _ := black_box_nested_maybeuninit_wide_ref_fnptr_and_adt_validity
  have _ := ptr_mask_zero_base_rejected_identity_mask_and_wide_ptr
  have _ := write_intrinsic_return_deref_and_protector_enforcement
  have _ := raw_eq_uninhabited_32bit_wide_rawptr_tuple_and_reordered_scalarpair
  have _ := unknown_alignment_fail_closed_and_diverging_const_eval_select
  have _ := tree_borrows_access_outside_borrowed_place_fails_closed
  have _ := typed_swap_union_keeps_data_range_and_resets_common_padding
  have _ := black_box_uninit_valid_exactly_where_type_permits
  have _ := alignment_undetermined_under_opaque_root_fails_closed
  have _ := tag_window_and_padding_reset_theorems_non_vacuous
  have _ := union_field_tree_borrows_and_direct_union_dest_invalidation
  have _ := ranged_projected_tag_window_intersection_and_field_layout_size
  have _ := scalar_union_without_field_layouts_fails_closed_and_uninhabited_union_field
  have _ := scalar_pair_trailing_zst_and_newtype_aggregate_fail_closed
  have _ := global_commit_round_trip_guard_rejects_partial_ptr_and_32bit_reloc
  have _ := uninhabited_ref_and_wide_ptr_metadata_ub_in_bytes_and_black_box
  have _ := untyped_padded_caller_referent_black_box_field_layout_and_dead_tags_diff_offset
  have _ := uninhabited_pointee_vs_pointer_to_uninhabited
  have _ := char_shaped_surrogate_fails_closed_in_layout_validation
  have _ := custom_dst_pointer_and_target_width_fail_closed
  have _ := provenance_carrying_usize_operands_fail_closed
  have _ := union_scalar_array_fast_path_data_mask
  have _ := b3_universal_theorems_non_vacuous
  have _ := tag_window_and_root_align_on_32bit_table
  have _ := decode_usize_arg_malformed_ptr_ub_unbacked_zero_and_zst_prov
  have _ := custom_dst_wide_tuple_and_32bit_slice_meta_validity
  have _ := ptr_offset_from_u64_on_32bit_and_const_eval_select_all_8_intrinsics
  have _ := a3_universal_theorems_non_vacuous
  have _ := non_vacuity_all_quantified_theorems
  exact ⟨rfl, compareUnsignedBytesProto_eq_miriBytesCompareSpec, ptrMask_baseAddr_invariant,
    evalPtrOffsetFromDistanceProto_eq_miriSpec, misaligned_offset_has_misaligned_placement, trivial⟩

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
  ranged_borrow_split_at_mut_no_over_invalidation
  typed_swap_resets_padding_in_stack_byte_buffer_and_union_global
  black_box_nested_maybeuninit_wide_ref_fnptr_and_adt_validity
  ptr_mask_zero_base_rejected_identity_mask_and_wide_ptr
  write_intrinsic_return_deref_and_protector_enforcement
  raw_eq_uninhabited_32bit_wide_rawptr_tuple_and_reordered_scalarpair
  unknown_alignment_fail_closed_and_diverging_const_eval_select
  tree_borrows_access_outside_borrowed_place_fails_closed
  typed_swap_union_keeps_data_range_and_resets_common_padding
  black_box_uninit_valid_exactly_where_type_permits
  alignment_undetermined_under_opaque_root_fails_closed
  tag_window_and_padding_reset_theorems_non_vacuous
  union_field_tree_borrows_and_direct_union_dest_invalidation
  ranged_projected_tag_window_intersection_and_field_layout_size
  scalar_union_without_field_layouts_fails_closed_and_uninhabited_union_field
  scalar_pair_trailing_zst_and_newtype_aggregate_fail_closed
  global_commit_round_trip_guard_rejects_partial_ptr_and_32bit_reloc
  uninhabited_ref_and_wide_ptr_metadata_ub_in_bytes_and_black_box
  untyped_padded_caller_referent_black_box_field_layout_and_dead_tags_diff_offset
  uninhabited_pointee_vs_pointer_to_uninhabited
  char_shaped_surrogate_fails_closed_in_layout_validation
  custom_dst_pointer_and_target_width_fail_closed
  provenance_carrying_usize_operands_fail_closed
  union_scalar_array_fast_path_data_mask
  b3_universal_theorems_non_vacuous
  tag_window_and_root_align_on_32bit_table
  decode_usize_arg_malformed_ptr_ub_unbacked_zero_and_zst_prov
  custom_dst_wide_tuple_and_32bit_slice_meta_validity
  ptr_offset_from_u64_on_32bit_and_const_eval_select_all_8_intrinsics
  a3_universal_theorems_non_vacuous
  non_vacuity_all_quantified_theorems
  all_proto_and_test_theorems

end MechanicalAxiomAudit

end Anneal.TcbCoreMemPtrIntrinsicsProtoTests
