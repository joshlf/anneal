-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

import Trusted.MirSemantics

namespace Anneal.Mir.VolatileUnalignedPtrTests

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-!
# Concrete Kernel-Checked MIR Tests for Unaligned & Volatile Raw-Pointer Operations

Every theorem in this suite is proved by kernel definitional reduction (`rfl`) with zero
`sorry`, zero `native_decide`, and only Lean's standard axioms (`[propext]`). It exercises the 7 `core::intrinsics::*`
volatile memory intrinsics and the 4 unlinked `core::ptr::*` helpers (`read_unaligned`,
`write_unaligned`, `read_volatile`, `write_volatile`), including all alignment, provenance,
byte-granular Tree Borrows, `allocDead`, uninhabited-type, ZST, overlap/memmove, and MMIO
semantics.
-/

-- ============================================================================
-- Shared 64-bit little-endian layout fixtures
-- ============================================================================

private def lU8 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 0xFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lU32 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lU64 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.int 64 false) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lBool : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lF32 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.float 32) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lPtr : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lUnit : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

private def lNever : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .primitive, variants := .empty, isUninhabited := true }

private def lZstAlign4 : TypeLayout :=
  { size := ⟨0⟩, align := ⟨4⟩,
    backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

private def lArrU8_8 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .array ⟨1⟩ 8, variants := .single 0, isUninhabited := false,
    fieldLayouts := [0] }

private def lArrU8_4 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .array ⟨1⟩ 4, variants := .single 0, isUninhabited := false,
    fieldLayouts := [0] }

private def lPackedU8U32 : TypeLayout :=
  { size := ⟨5⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨1⟩] [0, 1], variants := .single 0, isUninhabited := false,
    fieldLayouts := [0, 1] }

private def lAlign4BytesAndU32 : TypeLayout :=
  -- #[repr(C)] struct S { a: u8 (0), b: [u8; 3] (1), c: u32 (4) }
  { size := ⟨8⟩, align := ⟨4⟩,
    backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨1⟩, ⟨4⟩] [0, 1, 2], variants := .single 0, isUninhabited := false,
    fieldLayouts := [0, 13, 1] }

private def lArrU8_3 : TypeLayout :=
  { size := ⟨3⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .array ⟨1⟩ 3, variants := .single 0, isUninhabited := false,
    fieldLayouts := [0] }

private def lPairU32 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩,
    backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], variants := .single 0, isUninhabited := false,
    fieldLayouts := [1, 1] }

private def lPairBoolU8 : TypeLayout :=
  { size := ⟨2⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨1⟩] [0, 1], variants := .single 0, isUninhabited := false,
    fieldLayouts := [3, 0] }

private def lNonZeroU32 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨1, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def lArrU32_0 : TypeLayout :=
  { size := ⟨0⟩, align := ⟨4⟩,
    backendRepr := .memory,
    fields := .array ⟨4⟩ 0, variants := .single 0, isUninhabited := false,
    fieldLayouts := [1] }

private def lPairUnit : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨0⟩] [0, 1], variants := .single 0, isUninhabited := false,
    fieldLayouts := [6, 6] }

private def tbl : LayoutTable :=
  { pointerBits := 64,
    isLittleEndian := true,
    entries := [
      lU8,               -- 0
      lU32,              -- 1
      lU64,              -- 2
      lBool,             -- 3
      lF32,              -- 4
      lPtr,              -- 5
      lUnit,             -- 6
      lNever,            -- 7
      lZstAlign4,        -- 8
      lArrU8_8,          -- 9
      lArrU8_4,          -- 10
      lPackedU8U32,      -- 11
      lAlign4BytesAndU32,-- 12
      lArrU8_3,          -- 13
      lPairU32,          -- 14
      lPairBoolU8,       -- 15
      lNonZeroU32,       -- 16
      lArrU32_0,         -- 17
      lPairUnit          -- 18
    ] }

private def tyU8 : Ty := ⟨.uint .u8, 0⟩
private def tyU32 : Ty := ⟨.uint .u32, 1⟩
private def tyUsize : Ty := ⟨.uint .usize, 2⟩
private def tyBool : Ty := ⟨.bool, 3⟩
private def tyF32 : Ty := ⟨.float .f32, 4⟩
private def tyPtrConstU32 : Ty := ⟨.rawPtr .not (.uint .u32), 5⟩
private def tyPtrMutU32 : Ty := ⟨.rawPtr .mut (.uint .u32), 5⟩
private def tyPtrConstU8 : Ty := ⟨.rawPtr .not (.uint .u8), 5⟩
private def tyPtrMutU8 : Ty := ⟨.rawPtr .mut (.uint .u8), 5⟩
private def tyRefU32 : Ty := ⟨.ref .not (.uint .u32), 5⟩
private def tyUnit : Ty := ⟨.tuple [], 6⟩
private def tyNever : Ty := ⟨.never, 7⟩
private def tyZstAlign4 : Ty := ⟨.adt "Zst4" [], 8⟩
private def tyArrU8_8 : Ty := ⟨.array (.uint .u8) 8, 9⟩
private def tyArrU8_4 : Ty := ⟨.array (.uint .u8) 4, 10⟩
private def tyPacked : Ty := ⟨.adt "Packed" [], 11⟩
private def tyAlign4S : Ty := ⟨.adt "Align4S" [], 12⟩
private def tyArrU8_3 : Ty := ⟨.array (.uint .u8) 3, 13⟩
private def tyPairU32 : Ty := ⟨.tuple [.uint .u32, .uint .u32], 14⟩
private def tyPairBoolU8 : Ty := ⟨.tuple [.bool, .uint .u8], 15⟩
private def tyNonZeroU32 : Ty := ⟨.adt "NonZeroU32" [], 16⟩
private def tyArrU32_0 : Ty := ⟨.array (.uint .u32) 0, 17⟩
private def tyPairUnit : Ty := ⟨.tuple [.tuple [], .tuple []], 18⟩

private def mkDecl (ty : Ty) : LocalDecl :=
  { mutability := .mut, ty := ty, debugName := .none }

private def u8Val (b : Nat) : Value := .scalar ⟨b, 1⟩
private def u32Val (v : Nat) : Value := .scalar ⟨v, 4⟩
private def usizeVal (v : Nat) : Value := .scalar ⟨v, 8⟩
private def ptrVal (tag off : Nat) : Value := .ptr ⟨tag, off⟩ 8

private def tgtWith (defPath : String) (ty : Ty) : ResolvedCallTarget :=
  { defPath := defPath, typeArgs := [ty.kind], isIndirect := false }

-- ============================================================================
-- 1. Unaligned read/write across byte offset 1 in [u8; 8] and #[repr(packed)]
-- ============================================================================

private def arr8BytesVal : Value :=
  .aggregate 0 [u8Val 0xAA, u8Val 0x78, u8Val 0x56, u8Val 0x34, u8Val 0x12,
                u8Val 0xBB, u8Val 0xCC, u8Val 0xDD]

private def arr8Entry (tag : Nat) : BorrowEntry :=
  { tag := tag, targetLocal := 1, targetProjection := [], perm := .active,
    targetFrameDepth := 0, allocDead := false }

/-- `read_unaligned::<u32>` at byte offset 1 of `[u8; 8]` decodes `0x12345678` little-endian. -/
theorem read_unaligned_offset1_u32_ok :
    rawPtrLoadAction false false [arr8Entry 10] [] [] []
      (tgtWith "core::ptr::read_unaligned" tyU32)
      [mkDecl tyU32, mkDecl tyArrU8_8] tbl [] [ptrVal 10 1]
      [.uninit, .init arr8BytesVal] =
    .retBorrows [arr8Entry 10] (u32Val 0x12345678) := rfl

/-- `unaligned_volatile_load::<u32>` at byte offset 1 of `[u8; 8]` decodes `0x12345678`. -/
theorem unaligned_volatile_load_offset1_u32_ok :
    rawPtrLoadAction true false [arr8Entry 10] [] [] []
      (tgtWith "core::intrinsics::unaligned_volatile_load" tyU32)
      [mkDecl tyU32, mkDecl tyArrU8_8] tbl [] [ptrVal 10 1]
      [.uninit, .init arr8BytesVal] =
    .retBorrows [arr8Entry 10] (u32Val 0x12345678) := rfl

/-- `volatile_load::<u32>` at byte offset 1 of `[u8; 8]` (align 1 < 4) faults `.ub`. -/
theorem volatile_load_offset1_u32_misaligned_ub :
    rawPtrLoadAction true true [arr8Entry 10] [] [] []
      (tgtWith "core::intrinsics::volatile_load" tyU32)
      [mkDecl tyU32, mkDecl tyArrU8_8] tbl [] [ptrVal 10 1]
      [.uninit, .init arr8BytesVal] =
    .fault .ub := rfl

/-- `write_unaligned::<u32>` at byte offset 1 of `[u8; 8]` splices only bytes 1..5. -/
theorem write_unaligned_offset1_u32_ok :
    rawPtrStoreAction false false [arr8Entry 10] [] [] [] []
      (tgtWith "core::ptr::write_unaligned" tyU32)
      [mkDecl tyUnit, mkDecl tyArrU8_8] tbl [] [ptrVal 10 1, u32Val 0x04030201]
      [.uninit, .init arr8BytesVal] =
    .retStack [arr8Entry 10]
      [.uninit, .init (.aggregate 0 [u8Val 0xAA, u8Val 0x01, u8Val 0x02, u8Val 0x03, u8Val 0x04,
                                     u8Val 0xBB, u8Val 0xCC, u8Val 0xDD])]
      [] [] .unit := rfl

/-- `unaligned_volatile_store::<u32>` on a `#[repr(packed)]` field (field 1 at offset 1) succeeds. -/
private def packedFieldEntry : BorrowEntry :=
  { tag := 11, targetLocal := 1, targetProjection := [.field 1 tyU32], perm := .active,
    targetFrameDepth := 0, allocDead := false }

theorem unaligned_volatile_store_packed_field_ok :
    rawPtrStoreAction true false [packedFieldEntry] [] [] [] []
      (tgtWith "core::intrinsics::unaligned_volatile_store" tyU32)
      [mkDecl tyUnit, mkDecl tyPacked] tbl [] [ptrVal 11 0, u32Val 0xDEADBEEF]
      [.uninit, .init (.aggregate 0 [u8Val 7, u32Val 42])] =
    .retStack [packedFieldEntry]
      [.uninit, .init (.aggregate 0 [u8Val 7, u32Val 0xDEADBEEF])]
      [] [] .unit := rfl

-- ============================================================================
-- 2. Alignment edge cases: offset-back-to-aligned, .untracked, .global align=0
-- ============================================================================

/-- Pointer `(&raw const s.b).add(3)` inside `#[repr(C)] struct Align4S` (`relOff = 1`,
`ptr.offsetBytes = 3`) has total offset `4 % 4 == 0` in an `align(4)` allocation, so
`rawPtrTargetAligned?` returns `some true` (not a false `.ub`!). -/
private def align4FieldBEntry : BorrowEntry :=
  { tag := 12, targetLocal := 1, targetProjection := [.field 1 tyArrU8_3], perm := .active,
    targetFrameDepth := 0, allocDead := false }

theorem rawPtrTargetAligned_offset_back_to_aligned_ok :
    rawPtrTargetAligned? [] [.uninit, .init (.aggregate 0 [u8Val 1, .aggregate 0 [u8Val 2, u8Val 3, u8Val 4], u32Val 99])]
      [mkDecl tyU32, mkDecl tyAlign4S] tbl 4 (.prov ⟨12, 3⟩) (.stack ⟨12, 3⟩ align4FieldBEntry) =
    .some true := rfl

/-- `.untracked` provenance pointer with `reqAlign = 4` and odd `offsetBytes = 1` returns
`.fault .unsupported` (unknown base alignment), NEVER `.fault .ub`. -/
theorem volatile_load_untracked_odd_offset_unsupported :
    rawPtrLoadAction true true [] [] [] []
      (tgtWith "core::intrinsics::volatile_load" tyU32)
      [mkDecl tyU32] tbl [] [ptrVal 999 1] [.uninit] =
    .fault .unsupported := rfl

/-- `.global` allocation with unknown alignment (`align = 0`) and odd `offsetBytes = 1` returns
`.fault .unsupported`, NEVER `.fault .ub`. -/
private def unknownAlignGlobal : CapturedAllocation :=
  { allocId := 50, bytes := [.some 1, .some 2, .some 3, .some 4, .some 5, .some 6],
    relocations := [], align := ⟨0⟩, mutability := .not }

theorem volatile_load_global_zero_align_unsupported :
    rawPtrLoadAction true true [] [unknownAlignGlobal] [] []
      (tgtWith "core::intrinsics::volatile_load" tyU32)
      [mkDecl tyU32] tbl [] [ptrVal 50 1] [.uninit] =
    .fault .unsupported := rfl

-- ============================================================================
-- 3. MMIO outside Rust allocations, ZST null volatile vs non-volatile, align(4) ZST
-- ============================================================================

/-- Aligned volatile load from provenance-less MMIO `0x1000` is `.unsupported` (not `.ub`). -/
theorem volatile_load_mmio_aligned_unsupported :
    rawPtrLoadAction true true [] [] [] []
      (tgtWith "core::intrinsics::volatile_load" tyU32)
      [mkDecl tyU32] tbl [] [usizeVal 0x1000] [.uninit] =
    .fault .unsupported := rfl

/-- Aligned volatile store to provenance-less MMIO `0x1000` is `.unsupported` (not `.ub`). -/
theorem volatile_store_mmio_aligned_unsupported :
    rawPtrStoreAction true true [] [] [] [] []
      (tgtWith "core::intrinsics::volatile_store" tyU32)
      [mkDecl tyUnit] tbl [] [usizeVal 0x1000, u32Val 7] [.uninit] =
    .fault .unsupported := rfl

/-- Misaligned volatile load from MMIO `0x1001` is `.ub`. -/
theorem volatile_load_mmio_misaligned_ub :
    rawPtrLoadAction true true [] [] [] []
      (tgtWith "core::intrinsics::volatile_load" tyU32)
      [mkDecl tyU32] tbl [] [usizeVal 0x1001] [.uninit] =
    .fault .ub := rfl

/-- Misaligned volatile load of an `align(4)` ZST at `0x1001` is `.ub` even though size = 0. -/
theorem volatile_load_zst_align4_misaligned_ub :
    rawPtrLoadAction true true [] [] [] []
      (tgtWith "core::intrinsics::volatile_load" tyZstAlign4)
      [mkDecl tyZstAlign4] tbl [] [usizeVal 0x1001] [.uninit] =
    .fault .ub := rfl

/-- Volatile load of `()` through null (`0`) succeeds with `.unit`. -/
theorem volatile_load_null_zst_ok :
    rawPtrLoadAction true true [] [] [] []
      (tgtWith "core::intrinsics::volatile_load" tyUnit)
      [mkDecl tyUnit] tbl [] [usizeVal 0] [.uninit] =
    .ret .unit := rfl

/-- Non-volatile `read_unaligned::<()>` and `write_unaligned::<()>` through null (`0`) are `.ub`. -/
theorem nonvolatile_null_zst_ub :
    rawPtrLoadAction false false [] [] [] []
      (tgtWith "core::ptr::read_unaligned" tyUnit)
      [mkDecl tyUnit] tbl [] [usizeVal 0] [.uninit] = .fault .ub ∧
    rawPtrStoreAction false false [] [] [] [] []
      (tgtWith "core::ptr::write_unaligned" tyUnit)
      [mkDecl tyUnit] tbl [] [usizeVal 0, .unit] [.uninit] = .fault .ub :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- 4. Uninhabited `!`, nested value validity, NonZeroU32, canonical ZST values
-- ============================================================================

/-- Both volatile load and volatile store at `!` (`Never`) fault `.ub`. -/
theorem uninhabited_load_and_store_ub :
    rawPtrLoadAction true true [] [] [] []
      (tgtWith "core::intrinsics::volatile_load" tyNever)
      [mkDecl tyNever] tbl [] [usizeVal 0x1000] [.uninit] = .fault .ub ∧
    rawPtrStoreAction true true [] [] [] [] []
      (tgtWith "core::intrinsics::volatile_store" tyNever)
      [mkDecl tyUnit] tbl [] [usizeVal 0x1000, .unit] [.uninit] = .fault .ub :=
  ⟨rfl, rfl⟩

/-- Storing a tuple `(bool, u8)` with invalid nested `bool = 2` faults `.ub`. -/
theorem store_nested_invalid_bool_ub :
    rawPtrStoreAction true false [] [] [] [] []
      (tgtWith "core::intrinsics::unaligned_volatile_store" tyPairBoolU8)
      [mkDecl tyUnit, mkDecl tyPairBoolU8] tbl [] [usizeVal 0x1000, .aggregate 0 [u8Val 2, u8Val 5]]
      [.uninit, .uninit] =
    .fault .ub := rfl

/-- Storing a null `&u32` faults `.ub`. -/
theorem store_null_ref_ub :
    rawPtrStoreAction true false [] [] [] [] []
      (tgtWith "core::intrinsics::unaligned_volatile_store" tyRefU32)
      [mkDecl tyUnit] tbl [] [usizeVal 0x1000, usizeVal 0] [.uninit] =
    .fault .ub := rfl

/-- Storing `NonZeroU32` with `0` faults `.ub`, while `1` is valid (and reaches MMIO `.unsupported`). -/
theorem store_nonzero_u32_validity :
    rawPtrStoreAction true true [] [] [] [] []
      (tgtWith "core::intrinsics::volatile_store" tyNonZeroU32)
      [mkDecl tyUnit, mkDecl tyNonZeroU32] tbl [] [usizeVal 0x1000, u32Val 0] [.uninit, .uninit] =
      .fault .ub ∧
    rawPtrStoreAction true true [] [] [] [] []
      (tgtWith "core::intrinsics::volatile_store" tyNonZeroU32)
      [mkDecl tyUnit, mkDecl tyNonZeroU32] tbl [] [usizeVal 0x1000, u32Val 1] [.uninit, .uninit] =
      .fault .unsupported :=
  ⟨rfl, rfl⟩

/-- Canonical ZST values: `[u32; 0]` decodes to `.aggregate 0 []` and `((), ())` to
`.aggregate 0 [.unit, .unit]` (matching `Rvalue.repeat` and `readProjectedValue`). -/
theorem rawPtrZstValue_canonical :
    rawPtrZstValue? tbl tyArrU32_0 = .some (.aggregate 0 []) ∧
    rawPtrZstValue? tbl tyPairUnit = .some (.aggregate 0 [.unit, .unit]) :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- 5. Provenance preservation, no pointer forgery, and global f32 read
-- ============================================================================

private def ptrSlotEntry : BorrowEntry :=
  { tag := 20, targetLocal := 1, targetProjection := [], perm := .active,
    targetFrameDepth := 0, allocDead := false }

/-- Reading provenance-carrying pointer bytes as `usize` fails closed `.unsupported` (NEVER `0`). -/
theorem load_ptr_bytes_as_usize_unsupported :
    rawPtrLoadAction true true [ptrSlotEntry] [] [] []
      (tgtWith "core::intrinsics::volatile_load" tyUsize)
      [mkDecl tyUsize, mkDecl tyPtrConstU32] tbl [] [ptrVal 20 0]
      [.uninit, .init (ptrVal 77 16)] =
    .fault .unsupported := rfl

/-- Reading plain integer `0x10000` bytes as `*const u32` preserves provenance-less `.scalar`
(NEVER forges `allocId := 1`). -/
private def u64SlotEntry : BorrowEntry :=
  { tag := 21, targetLocal := 1, targetProjection := [], perm := .active,
    targetFrameDepth := 0, allocDead := false }

theorem load_int_bytes_as_raw_ptr_no_forge :
    rawPtrLoadAction true true [u64SlotEntry] [] [] []
      (tgtWith "core::intrinsics::volatile_load" tyPtrConstU32)
      [mkDecl tyPtrConstU32, mkDecl tyUsize] tbl [] [ptrVal 21 0]
      [.uninit, .init (usizeVal 0x10000)] =
    .retBorrows [u64SlotEntry] (usizeVal 0x10000) := rfl

/-- Reading a global `f32` (`1.0f32` = `0x3F800000`) via `volatile_load` succeeds (NEVER `.ub`). -/
private def globalF32 : CapturedAllocation :=
  { allocId := 60, bytes := [.some 0x00, .some 0x00, .some 0x80, .some 0x3F],
    relocations := [], align := ⟨4⟩, mutability := .not }

theorem volatile_load_global_f32_ok :
    rawPtrLoadAction true true [] [globalF32] [] []
      (tgtWith "core::intrinsics::volatile_load" tyF32)
      [mkDecl tyF32] tbl [] [ptrVal 60 0] [.uninit] =
    .ret (u32Val 0x3F800000) := rfl

-- ============================================================================
-- 6. volatile_copy_nonoverlapping_memory & volatile_copy_memory
-- ============================================================================

private def srcEntry (tag : Nat) (dead : Bool := false) : BorrowEntry :=
  { tag := tag, targetLocal := 1, targetProjection := [], perm := .active,
    targetFrameDepth := 0, allocDead := dead }

private def dstEntry (tag : Nat) (dead : Bool := false) : BorrowEntry :=
  { tag := tag, targetLocal := 2, targetProjection := [], perm := .active,
    targetFrameDepth := 0, allocDead := dead }

/-- `(dst, src, count)` argument order: copies `_1` (`src`, `0x11223344`) into `_2` (`dst`). -/
theorem volatile_copy_nonoverlapping_dst_src_order :
    let borrows := [srcEntry 30, dstEntry 31]
    let decls := [mkDecl tyUnit, mkDecl tyU32, mkDecl tyU32]
    let locals := [.uninit, .init (u32Val 0x11223344), .init (u32Val 0x99887766)]
    volatileCopyPlan borrows [] [] (tgtWith "core::intrinsics::volatile_copy_nonoverlapping_memory" tyU32)
      decls tbl [] [ptrVal 31 0, ptrVal 30 0, usizeVal 1] locals =
    .copyStack ⟨30, 0⟩ ⟨31, 0⟩ (srcEntry 30) (dstEntry 31) tyU32 1 4 ∧
    volatileCopyStackAction true borrows [] [] [] decls tbl locals
      ⟨30, 0⟩ ⟨31, 0⟩ (srcEntry 30) (dstEntry 31) tyU32 1 4 =
    .retStack borrows [.uninit, .init (u32Val 0x11223344), .init (u32Val 0x11223344)] [] [] .unit :=
  ⟨rfl, rfl⟩

/-- `allocDead = true` on `src` or `dst` in `volatileCopyStackAction` faults `.ub`. -/
theorem volatile_copy_allocDead_ub :
    let decls := [mkDecl tyUnit, mkDecl tyU32, mkDecl tyU32]
    let locals := [.uninit, .init (u32Val 1), .init (u32Val 2)]
    volatileCopyStackAction true [srcEntry 30 true, dstEntry 31 false] [] [] [] decls tbl locals
      ⟨30, 0⟩ ⟨31, 0⟩ (srcEntry 30 true) (dstEntry 31 false) tyU32 1 4 = .fault .ub ∧
    volatileCopyStackAction true [srcEntry 30 false, dstEntry 31 true] [] [] [] decls tbl locals
      ⟨30, 0⟩ ⟨31, 0⟩ (srcEntry 30 false) (dstEntry 31 true) tyU32 1 4 = .fault .ub :=
  ⟨rfl, rfl⟩

/-- Disjoint same-tag ranges (`[0..4)` -> `[4..8)`) in `volatile_copy_nonoverlapping_memory`
succeed (same tag is NOT UB when byte ranges are disjoint). -/
theorem volatile_copy_nonoverlapping_same_tag_disjoint_ok :
    let e := arr8Entry 32
    let decls := [mkDecl tyUnit, mkDecl tyArrU8_8]
    let locals := [.uninit, .init (.aggregate 0 [u8Val 1, u8Val 2, u8Val 3, u8Val 4,
                                                 u8Val 9, u8Val 9, u8Val 9, u8Val 9])]
    volatileCopyStackAction true [e] [] [] [] decls tbl locals
      ⟨32, 0⟩ ⟨32, 4⟩ e e tyU8 4 4 =
    .retStack [e] [.uninit, .init (.aggregate 0 [u8Val 1, u8Val 2, u8Val 3, u8Val 4,
                                                 u8Val 1, u8Val 2, u8Val 3, u8Val 4])] [] [] .unit := rfl

/-- Overlapping ranges (`[0..4)` -> `[2..6)`) in `volatile_copy_nonoverlapping_memory` fault `.ub`. -/
theorem volatile_copy_nonoverlapping_overlap_ub :
    let e := arr8Entry 32
    let decls := [mkDecl tyUnit, mkDecl tyArrU8_8]
    let locals := [.uninit, .init arr8BytesVal]
    volatileCopyStackAction true [e] [] [] [] decls tbl locals
      ⟨32, 0⟩ ⟨32, 2⟩ e e tyU8 4 4 = .fault .ub := rfl

/-- Forward-overlapping (`[0..3)` -> `[1..4)`) and backward-overlapping (`[1..4)` -> `[0..3)`)
`volatile_copy_memory` preserve exact `memmove` bytes without clobbering. -/
private def arr4Entry (tag : Nat) : BorrowEntry :=
  { tag := tag, targetLocal := 1, targetProjection := [], perm := .active,
    targetFrameDepth := 0, allocDead := false }

theorem volatile_copy_memory_overlapping_memmove_ok :
    let e := arr4Entry 33
    let decls := [mkDecl tyUnit, mkDecl tyArrU8_4]
    let locals := [.uninit, .init (.aggregate 0 [u8Val 10, u8Val 20, u8Val 30, u8Val 40])]
    volatileCopyStackAction false [e] [] [] [] decls tbl locals ⟨33, 0⟩ ⟨33, 1⟩ e e tyU8 3 3 =
      .retStack [e] [.uninit, .init (.aggregate 0 [u8Val 10, u8Val 10, u8Val 20, u8Val 30])]
        [] [] .unit ∧
    volatileCopyStackAction false [e] [] [] [] decls tbl locals ⟨33, 1⟩ ⟨33, 0⟩ e e tyU8 3 3 =
      .retStack [e] [.uninit, .init (.aggregate 0 [u8Val 20, u8Val 30, u8Val 40, u8Val 40])]
        [] [] .unit :=
  ⟨rfl, rfl⟩

/-- `T = u8, count = 1` on `u32` copies ONLY byte 0 (NOT all 4 bytes of the container). -/
theorem volatile_copy_u8_count1_into_u32_copies_one_byte :
    let borrows := [srcEntry 34, dstEntry 35]
    let decls := [mkDecl tyUnit, mkDecl tyU32, mkDecl tyU32]
    let locals := [.uninit, .init (u32Val 0xAABBCCDD), .init (u32Val 0x11223344)]
    volatileCopyStackAction true borrows [] [] [] decls tbl locals
      ⟨34, 0⟩ ⟨35, 0⟩ (srcEntry 34) (dstEntry 35) tyU8 1 1 =
    .retStack borrows [.uninit, .init (u32Val 0xAABBCCDD), .init (u32Val 0x112233DD)] [] [] .unit := rfl

/-- `count * size > isize::MAX` faults `.ub` in both `volatileCopyPlan` and `volatileSetPlan`. -/
theorem volatile_copy_set_isize_overflow_ub :
    let huge := usizeVal 0x4000000000000000 -- * 4 = 2^64 >= 2^63 = isize::MAX + 1
    volatileCopyPlan [] [] [] (tgtWith "core::intrinsics::volatile_copy_memory" tyU32)
      [mkDecl tyUnit] tbl [] [usizeVal 0x1000, usizeVal 0x2000, huge] [.uninit] = .fault .ub ∧
    volatileSetPlan [] [] [] (tgtWith "core::intrinsics::volatile_set_memory" tyU32)
      [mkDecl tyUnit] tbl [] [usizeVal 0x1000, u8Val 0, huge] [.uninit] = .fault .ub :=
  ⟨rfl, rfl⟩

/-- Out-of-bounds global `src` and immutable global `dst` in `volatileCopyPlan` both fault `.ub`. -/
theorem volatile_copy_global_oob_and_immut_ub :
    volatileCopyPlan [dstEntry 35] [globalF32] []
      (tgtWith "core::intrinsics::volatile_copy_memory" tyU32)
      [mkDecl tyUnit, mkDecl tyU32, mkDecl tyU32] tbl []
      [ptrVal 35 0, ptrVal 60 4, usizeVal 1] [.uninit, .init (u32Val 0), .init (u32Val 0)] =
      .fault .ub ∧
    volatileCopyPlan [srcEntry 34] [globalF32] []
      (tgtWith "core::intrinsics::volatile_copy_memory" tyU32)
      [mkDecl tyUnit, mkDecl tyU32, mkDecl tyU32] tbl []
      [ptrVal 60 0, ptrVal 34 0, usizeVal 1] [.uninit, .init (u32Val 0), .init (u32Val 0)] =
      .fault .ub :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- 7. volatile_set_memory
-- ============================================================================

/-- `volatileSetStackAction` fills multi-element `[u8; 4]` (full and interior slice) and rejects
`allocDead = true` with `.ub`. -/
theorem volatile_set_memory_stack_and_dead :
    let e := arr4Entry 40
    let eDead : BorrowEntry := { e with allocDead := true }
    let decls := [mkDecl tyUnit, mkDecl tyArrU8_4]
    let locals := [.uninit, .init (.aggregate 0 [u8Val 1, u8Val 2, u8Val 3, u8Val 4])]
    volatileSetStackAction [e] [] [] [] decls tbl locals ⟨40, 0⟩ e 0xAB 4 =
      .retStack [e] [.uninit, .init (.aggregate 0 [u8Val 0xAB, u8Val 0xAB, u8Val 0xAB, u8Val 0xAB])]
        [] [] .unit ∧
    volatileSetStackAction [e] [] [] [] decls tbl locals ⟨40, 1⟩ e 0xFF 2 =
      .retStack [e] [.uninit, .init (.aggregate 0 [u8Val 1, u8Val 0xFF, u8Val 0xFF, u8Val 4])]
        [] [] .unit ∧
    volatileSetStackAction [eDead] [] [] [] decls tbl locals ⟨40, 0⟩ eDead 0xFF 2 =
      .fault .ub :=
  ⟨rfl, rfl, rfl⟩

/-- `volatile_set_memory` writing invalid `bool` byte `0x2A` into a `bool` local is `.unsupported`
(NOT `.ub` on the set itself). -/
theorem volatile_set_invalid_bool_byte_unsupported :
    let e : BorrowEntry :=
      { tag := 41, targetLocal := 1, targetProjection := [], perm := .active,
        targetFrameDepth := 0, allocDead := false }
    volatileSetStackAction [e] [] [] [] [mkDecl tyUnit, mkDecl tyBool] tbl
      [.uninit, .init (u8Val 0)] ⟨41, 0⟩ e 0x2A 1 = .fault .unsupported := rfl

-- ============================================================================
-- 8. Byte-granular Tree Borrows & protected ReservedFrz conflicts
-- ============================================================================

/-- Writing `[0..4)` of `(u32, u32)` via whole-local pointer leaves a protected foreign borrow at
`[Field 1]` (`[4..8)`) untouched (NO false `.ub`), while an unaligned write at `[2..6)` overlaps
`[4..8)` and triggers the protected foreign conflict (`.ub`). -/
theorem byte_granular_tree_borrows_disjoint_vs_overlap :
    let wholeEntry : BorrowEntry :=
      { tag := 50, targetLocal := 1, targetProjection := [], perm := .active,
        targetFrameDepth := 0, allocDead := false }
    let field1Prot : BorrowEntry :=
      { tag := 51, targetLocal := 1, targetProjection := [.field 1 tyU32], perm := .active,
        protector := .some 7, parentTag := .some 50, targetFrameDepth := 0, allocDead := false }
    let borrows := [wholeEntry, field1Prot]
    let decls := [mkDecl tyUnit, mkDecl tyPairU32]
    let locals := [.uninit, .init (.aggregate 0 [u32Val 10, u32Val 20])]
    -- Disjoint [0..4) write succeeds and preserves field1Prot active:
    rawPtrStoreAction true true borrows [] [] [] [7]
      (tgtWith "core::intrinsics::volatile_store" tyU32)
      decls tbl [] [ptrVal 50 0, u32Val 99] locals =
      .retStack borrows [.uninit, .init (.aggregate 0 [u32Val 99, u32Val 20])] [] [] .unit ∧
    -- Overlapping [2..6) unaligned write hits protected field1Prot [4..8) -> .ub:
    rawPtrStoreAction true false borrows [] [] [] [7]
      (tgtWith "core::intrinsics::unaligned_volatile_store" tyU32)
      decls tbl [] [ptrVal 50 2, u32Val 99] locals =
      .fault .ub :=
  ⟨rfl, rfl⟩

/-- Overlapping `volatile_copy_memory` where `dst` is protected `.reservedFrz true`: the source
read (foreign to `dst`) freezes `dst` to `.frozen`, and then the destination write (child on
`.frozen`) faults `.ub`! -/
theorem volatile_copy_memory_protected_reservedFrz_ub :
    let srcE : BorrowEntry :=
      { tag := 60, targetLocal := 1, targetProjection := [], perm := .frozen,
        targetFrameDepth := 0, allocDead := false }
    let dstE : BorrowEntry :=
      { tag := 61, targetLocal := 1, targetProjection := [], perm := .reservedFrz true,
        protector := .some 9, targetFrameDepth := 0, allocDead := false }
    let decls := [mkDecl tyUnit, mkDecl tyU32]
    let locals := [.uninit, .init (u32Val 42)]
    volatileCopyStackAction false [srcE, dstE] [] [] [9] decls tbl locals
      ⟨60, 0⟩ ⟨61, 0⟩ srcE dstE tyU32 1 4 = .fault .ub := rfl

-- ============================================================================
-- 9. End-to-end `evalTerminator` dispatch for unlinked `core::ptr::*` & intrinsics
-- ============================================================================

private def mkCallState (locals : List LocalSlot)
    (borrows : List BorrowEntry) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals },
    memory := { borrows := borrows } }

private def mkCallBody (decls : List LocalDecl) : CapturedMir :=
  { defPath := "test::caller",
    phase := .runtimePostCleanup,
    role := .subject,
    argCount := 0,
    localDecls := decls,
    basicBlocks := [],
    fnAbi := { args := [], ret := { layout := lUnit, mode := .ignore },
               conv := .rust, canUnwind := false },
    layouts := tbl,
    allocations := [] }

/-- End-to-end `evalTerminator` call to unlinked `core::ptr::read_unaligned::<u32>` steps and
writes the decoded value into `_0` (`bb1`). -/
theorem evalTerminator_unlinked_read_unaligned_steps :
    let decls := [mkDecl tyU32, mkDecl tyArrU8_8, mkDecl tyPtrConstU32]
    let borrows := [arr8Entry 70]
    let s := mkCallState [.uninit, .init arr8BytesVal, .init (ptrVal 70 1)] borrows
    let fnOp : Operand := .constant
      { ty := ⟨.fnDef "core::ptr::read_unaligned" [.uint .u32], 6⟩,
        val := .zeroSized }
    let term : Terminator :=
      { kind := .call fnOp [.copy ⟨2, []⟩] ⟨0, []⟩ (.some 1) .continue_, span := "" }
    evalTerminator s term (.some (mkCallBody decls)) =
    MirStepNode.step
      { frame := { blockIdx := 1, stmtIdx := 0,
                   locals := [.init (u32Val 0x12345678), .init arr8BytesVal, .init (ptrVal 70 1)] },
        memory := { borrows := borrows } } := rfl

/-- End-to-end `evalTerminator` call to unlinked `core::ptr::write_volatile::<u32>` on an aligned
MMIO address `0x1000` fails closed with `MirStepNode.unsupported` (NEVER `.fail .ub`). -/
theorem evalTerminator_unlinked_write_volatile_mmio_unsupported :
    let decls := [mkDecl tyUnit, mkDecl tyPtrMutU32, mkDecl tyU32]
    let s := mkCallState [.uninit, .init (usizeVal 0x1000), .init (u32Val 0xCAFEBABE)] []
    let fnOp : Operand := .constant
      { ty := ⟨.fnDef "core::ptr::write_volatile" [.uint .u32], 6⟩,
        val := .zeroSized }
    let term : Terminator :=
      { kind := .call fnOp [.copy ⟨1, []⟩, .copy ⟨2, []⟩] ⟨0, []⟩ (.some 1) .continue_, span := "" }
    evalTerminator s term (.some (mkCallBody decls)) = MirStepNode.unsupported := rfl

/-- End-to-end `evalTerminator` call to `core::intrinsics::volatile_copy_memory::<u8>` performs
overlapping forward `memmove` (`[0..3)` -> `[1..4)`) in `(dst, src, count)` argument order. -/
theorem evalTerminator_volatile_copy_memory_memmove_steps :
    let decls := [mkDecl tyUnit, mkDecl tyArrU8_4, mkDecl tyPtrMutU8, mkDecl tyPtrConstU8, mkDecl tyUsize]
    let borrows := [arr4Entry 72]
    let s := mkCallState
      [.uninit, .init (.aggregate 0 [u8Val 10, u8Val 20, u8Val 30, u8Val 40]),
       .init (ptrVal 72 1), .init (ptrVal 72 0), .init (usizeVal 3)]
      borrows
    let fnOp : Operand := .constant
      { ty := ⟨.fnDef "core::intrinsics::volatile_copy_memory" [.uint .u8], 6⟩,
        val := .zeroSized }
    let term : Terminator :=
      { kind := .call fnOp [.copy ⟨2, []⟩, .copy ⟨3, []⟩, .copy ⟨4, []⟩] ⟨0, []⟩ (.some 1) .continue_,
        span := "" }
    evalTerminator s term (.some (mkCallBody decls)) =
    MirStepNode.step
      { frame := { blockIdx := 1, stmtIdx := 0,
                   locals := [.init .unit,
                              .init (.aggregate 0 [u8Val 10, u8Val 10, u8Val 20, u8Val 30]),
                              .init (ptrVal 72 1), .init (ptrVal 72 0), .init (usizeVal 3)] },
        memory := { borrows := borrows } } := rfl

/-- End-to-end `evalTerminator` call to `core::intrinsics::volatile_set_memory::<u8>` steps and
writes `()` into `_0` while updating `_1` (`bb1`). -/
theorem evalTerminator_volatile_set_memory_steps :
    let decls := [mkDecl tyUnit, mkDecl tyArrU8_4, mkDecl tyPtrMutU8, mkDecl tyU8, mkDecl tyUsize]
    let borrows := [arr4Entry 71]
    let s := mkCallState
      [.uninit, .init (.aggregate 0 [u8Val 1, u8Val 2, u8Val 3, u8Val 4]),
       .init (ptrVal 71 0), .init (u8Val 0x5A), .init (usizeVal 4)]
      borrows
    let fnOp : Operand := .constant
      { ty := ⟨.fnDef "core::intrinsics::volatile_set_memory" [.uint .u8], 6⟩,
        val := .zeroSized }
    let term : Terminator :=
      { kind := .call fnOp [.copy ⟨2, []⟩, .copy ⟨3, []⟩, .copy ⟨4, []⟩] ⟨0, []⟩ (.some 1) .continue_,
        span := "" }
    evalTerminator s term (.some (mkCallBody decls)) =
    MirStepNode.step
      { frame := { blockIdx := 1, stmtIdx := 0,
                   locals := [.init .unit,
                              .init (.aggregate 0 [u8Val 0x5A, u8Val 0x5A, u8Val 0x5A, u8Val 0x5A]),
                              .init (ptrVal 71 0), .init (u8Val 0x5A), .init (usizeVal 4)] },
        memory := { borrows := borrows } } := rfl

/-- info: 'Anneal.Mir.VolatileUnalignedPtrTests.read_unaligned_offset1_u32_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms read_unaligned_offset1_u32_ok

/-- info: 'Anneal.Mir.VolatileUnalignedPtrTests.byte_granular_tree_borrows_disjoint_vs_overlap' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms byte_granular_tree_borrows_disjoint_vs_overlap

/-- info: 'Anneal.Mir.VolatileUnalignedPtrTests.evalTerminator_unlinked_read_unaligned_steps' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalTerminator_unlinked_read_unaligned_steps

/-- info: 'Anneal.Mir.VolatileUnalignedPtrTests.evalTerminator_volatile_set_memory_steps' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalTerminator_volatile_set_memory_steps

end Anneal.Mir.VolatileUnalignedPtrTests
