/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.SepLogicLenses
import Anneal.MirLiftCore
import Anneal.PureLift.V2026_06_01Bridge
import Lean.Elab.Command

/-!
# Unsized DST Pointer Metadata Lenses, `from_raw_parts` / `to_raw_parts`, & Dynamic Layout Intrinsics

Concrete kernel-checked witnesses and negative boundary canaries for Episode 1
(`ep1-unsized-dst-ptr-metadata-lenses-and-pure-lift-bridge`) across:
1. `Anneal.MirLiftCore` (`UnsizedDstMetadataLifters`: Rvalue / intrinsic / `stepMirFn` lifters,
   `stepMirFn`-level `.ub` faults, sized lifters, and protector-aware assignment lifters),
2. `Anneal.SepLogicLenses` (`PtrMetadataOf`, `UnsizedSliceDstBacking`, `UnsizedSliceDstAt`,
   `UnsizedStrDstAt`, with live global-image / borrow / empty-window backings and frame rules),
3. `Anneal.PureLift.V2026_06_01Bridge` (`WideSliceDstBridge`: `stdWideSliceVal`,
   `StdValRefines.wideSlice`, and `spatialPinnedBlockHolds` / `spatialBindingsHold` framing for
   `copy` / `move` operands, `[T]` and `str`).
-/

namespace Anneal.UnsizedDstMetadataLensTests

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.SepLogicLenses
open Anneal.MirLiftCore
open Anneal.PureLift
open Anneal.PureLift.MirLiftCoreInterop
open Anneal.PureLift.V2026_06_01Bridge
open Anneal.Rustc.V2026_06_01.SymbolicEval (wpMirExecSym)

/-! ## 1. Symbolic `simp` normal forms on `WidePtrVal` (`.1` / `.2` projections, zero `Prod.casesOn`) -/

theorem widePtr_dataVal_metaVal_symbolic_simp (ptrBytes : Nat) (p : ProvenancePtr)
    (len n k : Nat) :
    WidePtrVal.dataVal ptrBytes (WidePtrVal.mk p len) = .ptr p ptrBytes ∧
    WidePtrVal.metaVal ptrBytes (WidePtrVal.mk p len) = .scalar ⟨len, ptrBytes⟩ ∧
    WidePtrVal.dataVal ptrBytes (WidePtrVal.takeElems (WidePtrVal.mk p len) k) = .ptr p ptrBytes ∧
    WidePtrVal.metaVal ptrBytes (WidePtrVal.takeElems (WidePtrVal.mk p len) k) =
      .scalar ⟨k, ptrBytes⟩ ∧
    WidePtrVal.dataVal ptrBytes (WidePtrVal.dropElems (WidePtrVal.mk p len) n k) =
      .ptr (WidePtrVal.elemPtr (p, len) n k) ptrBytes ∧
    WidePtrVal.metaVal ptrBytes (WidePtrVal.dropElems (WidePtrVal.mk p len) n k) =
      .scalar ⟨len - k, ptrBytes⟩ ∧
    WidePtrVal.toValue ptrBytes (WidePtrVal.mk p len) =
      .aggregate 0 [WidePtrVal.dataVal ptrBytes (WidePtrVal.mk p len),
                    WidePtrVal.metaVal ptrBytes (WidePtrVal.mk p len)] :=
  ⟨WidePtrVal.dataVal_mk ptrBytes p len,
   WidePtrVal.metaVal_mk ptrBytes p len,
   (WidePtrVal.dataVal_takeElems ptrBytes (WidePtrVal.mk p len) k).trans
     (WidePtrVal.dataVal_mk ptrBytes p len),
   WidePtrVal.metaVal_takeElems ptrBytes (WidePtrVal.mk p len) k,
   WidePtrVal.dataVal_dropElems ptrBytes (WidePtrVal.mk p len) n k,
   WidePtrVal.metaVal_dropElems ptrBytes (WidePtrVal.mk p len) n k,
   WidePtrVal.toValue_eq_dataVal_metaVal ptrBytes (WidePtrVal.mk p len)⟩

/-- **Symbolic `simp` normal forms on an arbitrary `wide : WidePtrVal`** (no `WidePtrVal.mk`
constructor is exposed, so no pair pattern / `Prod.casesOn` can fire): the `@[simp]` `.1` / `.2`
lens lemmas normalize sub-slice data pointers, metadata, provenance, and fat-pointer values by
`simp only`. -/
theorem widePtr_symbolic_simp_on_arbitrary_wide (ptrBytes n k : Nat) (wide : WidePtrVal) :
    WidePtrVal.dataVal ptrBytes (WidePtrVal.takeElems wide k) = .ptr wide.1 ptrBytes ∧
    WidePtrVal.metaVal ptrBytes (WidePtrVal.takeElems wide k) = .scalar ⟨k, ptrBytes⟩ ∧
    WidePtrVal.dataVal ptrBytes (WidePtrVal.dropElems wide n k) =
      .ptr (WidePtrVal.elemPtr wide n k) ptrBytes ∧
    WidePtrVal.metaVal ptrBytes (WidePtrVal.dropElems wide n k) =
      .scalar ⟨wide.2 - k, ptrBytes⟩ ∧
    (WidePtrVal.dropElems wide n k).1.allocId = wide.1.allocId ∧
    (WidePtrVal.takeElems wide k).1 = wide.1 ∧
    WidePtrVal.toValue ptrBytes wide =
      .aggregate 0 [WidePtrVal.dataVal ptrBytes wide, WidePtrVal.metaVal ptrBytes wide] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

/-! ## 2. Concrete layouts, allocations, and `[u32]` / `str` / empty / ZST `UnsizedSliceDstAt` views -/

def u32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def fatLayout64 : TypeLayout :=
  { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def fatLayout32 : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def layouts64 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [u32Layout, fatLayout64] }

def layouts32 : LayoutTable :=
  { pointerBits := 32, isLittleEndian := true, entries := [u32Layout, fatLayout32] }

def arrAlloc16 : CapturedAllocation := {
  allocId := 9
  bytes := [some 1, some 0, some 0, some 0, some 2, some 0, some 0, some 0,
            some 3, some 0, some 0, some 0, some 4, some 0, some 0, some 0]
  relocations := []
  align := { bytes := 4 }
  mutability := .mut }

def strAlloc5 : CapturedAllocation := {
  allocId := 10
  bytes := [some 104, some 101, some 108, some 108, some 111]
  relocations := []
  align := { bytes := 1 }
  mutability := .not }

def mem0 : Memory := { globals := [arrAlloc16, strAlloc5] }

def p9 : ProvenancePtr := ⟨9, 0⟩
def p10 : ProvenancePtr := ⟨10, 0⟩
def wide4 : WidePtrVal := WidePtrVal.mk p9 4
def wideStr5 : WidePtrVal := WidePtrVal.mk p10 5
def wideEmpty : WidePtrVal := WidePtrVal.mk p9 0
def wideZst1000 : WidePtrVal := WidePtrVal.mk p9 1000

def bytes16 : ByteMem := globalAllocByteMem arrAlloc16
def bytesStr5 : ByteMem := globalAllocByteMem strAlloc5

abbrev U32 : Type := {v : Nat // v < 256 ^ 4}
def u (v : Nat) (h : v < 256 ^ 4 := by decide) : U32 := ⟨v, h⟩
def xs4 : List U32 := [u 1, u 2, u 3, u 4]
def helloBytes : List UInt8 := [104, 101, 108, 108, 111]

theorem arr_sliceTypedAt : SliceTypedAt ByteLensCodec.u32LE wide4 xs4 bytes16 := by
  refine ⟨rfl, by decide, ?_⟩
  intro i hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | k + 4, hi => exact absurd hi (by simp [xs4])

theorem str_sliceTypedAt : SliceTypedAt ByteLensCodec.u8 wideStr5 helloBytes bytesStr5 := by
  refine ⟨rfl, by decide, ?_⟩
  intro i hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | k + 5, hi => exact absurd hi (by simp [helloBytes])

/-- `bytes16` / `bytesStr5` are the live images of the captured globals `9` / `10` in `mem0`. -/
theorem arr_liveImage : LiveSliceImage mem0 wide4 bytes16 := ⟨arrAlloc16, rfl, rfl⟩
theorem str_liveImage : LiveSliceImage mem0 wideStr5 bytesStr5 := ⟨strAlloc5, rfl, rfl⟩

theorem arr_unsizedDst64 :
    UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) mem0 wide4
      (WidePtrVal.toValue 8 wide4) xs4 bytes16 :=
  UnsizedSliceDstAt.of_sliceTypedAt 8 (.uint .u32) mem0 arr_sliceTypedAt arr_liveImage

theorem arr_typedAt_array4 :
    TypedAt (ByteLensCodec.u32LE.array 4) p9.offsetBytes ⟨xs4, rfl⟩ bytes16 := by
  rw [typedAt_iff]
  exact ⟨by decide, rfl⟩

/-- `PointerCoercion("Unsize")` (`*const [u32; 4] -> *const [u32]`) directly produces
`UnsizedSliceDstAt` via `TypedAt.unsize_array_to_unsizedSliceDstAt`. -/
theorem arr_unsize_to_unsizedDst64 :
    let arrPtrTy : Ty := { kind := .rawPtr .not (.array (.uint .u32) 4), layoutIdx := 0 }
    let decls : List LocalDecl :=
      [{ mutability := .not, ty := arrPtrTy, debugName := some "arr_ptr" }]
    let locs : List LocalSlot := [.init (.ptr p9 8)]
    evalRvalue locs (.cast (.pointerCoercion "Unsize") (.copy { local_ := 0, projection := [] })
        { kind := slicePtrKind false .not (.uint .u32), layoutIdx := 1 }) mem0 decls layouts64 =
      .ok (WidePtrVal.toValue 8 wide4) locs mem0 ∧
    UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) mem0 wide4
      (WidePtrVal.toValue 8 wide4) xs4 bytes16 :=
  TypedAt.unsize_array_to_unsizedSliceDstAt [.init (.ptr p9 8)] [.init (.ptr p9 8)]
    (.copy { local_ := 0, projection := [] }) mem0
    [{ mutability := .not, ty := { kind := .rawPtr .not (.array (.uint .u32) 4), layoutIdx := 0 },
       debugName := some "arr_ptr" }]
    layouts64 false .not (.uint .u32) 1
    { kind := .rawPtr .not (.array (.uint .u32) 4), layoutIdx := 0 } p9
    rfl rfl rfl rfl rfl (fun h => nomatch h) rfl rfl arr_typedAt_array4

theorem arr_unsizedDst32 :
    UnsizedSliceDstAt ByteLensCodec.u32LE 4 (.slice (.uint .u32)) mem0 wide4
      (WidePtrVal.toValue 4 wide4) xs4 bytes16 :=
  UnsizedSliceDstAt.of_sliceTypedAt 4 (.uint .u32) mem0 arr_sliceTypedAt arr_liveImage

theorem str_unsizedDst64 :
    UnsizedStrDstAt 8 mem0 wideStr5 (WidePtrVal.toValue 8 wideStr5) helloBytes bytesStr5 :=
  UnsizedSliceDstAt.of_str_sliceTypedAt 8 mem0 str_sliceTypedAt str_liveImage

theorem empty_and_zst_unsizedDst_witnesses :
    UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) mem0 wideEmpty
      (WidePtrVal.toValue 8 wideEmpty) [] bytes16 ∧
    UnsizedStrDstAt 8 mem0 (WidePtrVal.mk p10 0)
      (WidePtrVal.toValue 8 (WidePtrVal.mk p10 0)) [] bytesStr5 ∧
    UnsizedSliceDstAt ByteLensCodec.unit 8 (.slice (.tuple [])) mem0 wideZst1000
      (WidePtrVal.toValue 8 wideZst1000) (List.replicate 1000 ()) bytes16 :=
  ⟨UnsizedSliceDstAt.empty_slice ByteLensCodec.u32LE 8 (.uint .u32) mem0 p9 bytes16 (by decide),
   UnsizedSliceDstAt.empty_str 8 mem0 p10 bytesStr5 (by decide),
   UnsizedSliceDstAt.zst_unit_replicate 8 (.tuple []) mem0 p9 1000 bytes16 (by decide)⟩

/-- **Memory backing is not vacuous**: the same `[u32]` view over `bytes16` is *not* an
`UnsizedSliceDstAt` lens in a `Memory` with no captured global `9`, no live borrow, and a
non-empty (`4 * 4 = 16`-byte) window, while it is one in `mem0` (`arr_unsizedDst64`). -/
theorem unsizedDst_requires_live_backing :
    ¬ UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) ({} : Memory) wide4
      (WidePtrVal.toValue 8 wide4) xs4 bytes16 := by
  intro h
  rcases h.image_or_activeBorrow_or_zeroSized with ⟨_, hA, _⟩ | ⟨_, _, hL, _, _⟩ | hZ
  · cases hA
  · cases hL
  · exact absurd hZ (by decide)

theorem unsizedDst_projections_split_and_unique :
    xs4.length = wide4.2 ∧
    WidePtrVal.toValue 8 wide4 =
      .aggregate 0 [WidePtrVal.dataVal 8 wide4, .scalar ⟨xs4.length, 8⟩] ∧
    WidePtrVal.metaVal 8 wide4 = .scalar ⟨xs4.length, 8⟩ ∧
    PtrMetadataOf 8 (WidePtrVal.toValue 8 wide4) (.scalar ⟨xs4.length, 8⟩) ∧
    PtrMetadataOf 8 (WidePtrVal.toValue 8 (WidePtrVal.mk p9 4)) (.scalar ⟨4, 8⟩) ∧
    (∀ ys, UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) mem0 wide4
      (WidePtrVal.toValue 8 wide4) ys bytes16 → ys = xs4) ∧
    (∀ m₁ m₂, PtrMetadataOf 8 (WidePtrVal.toValue 8 wide4) m₁ →
      PtrMetadataOf 8 (WidePtrVal.toValue 8 wide4) m₂ → m₁ = m₂) ∧
    isUnsizedRawPtrPointee { kind := .slice (.uint .u32), layoutIdx := 0 } = true ∧
    UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) mem0 wide4
      (WidePtrVal.toValue 8 wide4) (xs4.take 2 ++ xs4.drop 2) bytes16 ∧
    UnsizedSliceDstBacking 4 mem0 wide4 bytes16 ∧
    UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) mem0 wide4
      (WidePtrVal.toValue 8 wide4) (xs4.take 2 ++ xs4.drop 2) bytes16 := by
  obtain ⟨hL, hR, _⟩ := arr_unsizedDst64.splitAt (k := 2) (by decide)
  exact ⟨arr_unsizedDst64.length_eq,
    arr_unsizedDst64.ptr_eq,
    arr_unsizedDst64.meta_eq,
    arr_unsizedDst64.meta_of_length,
    PtrMetadataOf.wide_mk 8 p9 4,
    fun ys h => UnsizedSliceDstAt.unique h arr_unsizedDst64,
    fun _ _ h1 h2 => PtrMetadataOf.unique h1 h2,
    arr_unsizedDst64.dst_ty.isUnsizedRawPtrPointee_eq_true 0,
    UnsizedSliceDstAt.of_splitAt (k := 2) (by decide) hL hR arr_unsizedDst64.backing,
    UnsizedSliceDstBacking.of_splitAt_pos (k := 2) (by decide) (by decide) (by decide)
      hL.backing hR.backing,
    UnsizedSliceDstAt.of_splitAt_pos (k := 2) (by decide) (by decide) (by decide) hL hR⟩

/-! ## 3. `UnOp.ptrMetadata`, `AggregateKind.rawPtr` (`from_raw_parts`), and `to_raw_parts` -/

def dstDecls : List LocalDecl := [
  { mutability := .mut, ty := { kind := .uint .usize, layoutIdx := 0 }, debugName := some "_0" },
  { mutability := .not, ty := { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 1 },
    debugName := some "const_sl" },
  { mutability := .not, ty := { kind := .rawPtr .mut (.slice (.uint .u32)), layoutIdx := 1 },
    debugName := some "mut_sl" },
  { mutability := .not, ty := { kind := .ref .not (.slice (.uint .u32)), layoutIdx := 1 },
    debugName := some "ref_sl" },
  { mutability := .not, ty := { kind := .ref .not .str, layoutIdx := 1 },
    debugName := some "ref_str" },
  { mutability := .not, ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 },
    debugName := some "thin_ptr" },
  { mutability := .not, ty := { kind := .tuple [], layoutIdx := 0 },
    debugName := some "unit_val" }]

def dstLocals (pb : Nat) : List LocalSlot :=
  [.uninit,
   .init (WidePtrVal.toValue pb wide4),
   .init (WidePtrVal.toValue pb wide4),
   .init (WidePtrVal.toValue pb wide4),
   .init (WidePtrVal.toValue pb wideStr5),
   .init (.ptr p9 pb),
   .init .unit]

def ptrU32Ty : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }
def usizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
def sliceU32Ty : Ty := { kind := .slice (.uint .u32), layoutIdx := 0 }
def strPointeeTy : Ty := { kind := .str, layoutIdx := 0 }

/-- `UnOp.ptrMetadata` on `*const [u32]`, `*mut [u32]`, `&[u32]`, `&str` (64-bit & 32-bit),
and thin `*const u32` (`.unit`). -/
theorem ptrMetadata_wide_and_thin_witnesses :
    (evalRvalue (dstLocals 8) (.unaryOp .ptrMetadata (.copy { local_ := 1, projection := [] }))
      mem0 dstDecls layouts64 = .ok (.scalar ⟨4, 8⟩) (dstLocals 8) mem0 ∧
     UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) mem0 wide4
       (WidePtrVal.toValue 8 wide4) xs4 bytes16) ∧
    evalRvalue (dstLocals 8) (.unaryOp .ptrMetadata (.copy { local_ := 2, projection := [] }))
      mem0 dstDecls layouts64 = .ok (.scalar ⟨4, 8⟩) (dstLocals 8) mem0 ∧
    evalRvalue (dstLocals 4) (.unaryOp .ptrMetadata (.copy { local_ := 3, projection := [] }))
      mem0 dstDecls layouts32 = .ok (.scalar ⟨4, 4⟩) (dstLocals 4) mem0 ∧
    (evalRvalue (dstLocals 8) (.unaryOp .ptrMetadata (.copy { local_ := 4, projection := [] }))
      mem0 dstDecls layouts64 = .ok (.scalar ⟨5, 8⟩) (dstLocals 8) mem0 ∧
     UnsizedStrDstAt 8 mem0 wideStr5 (WidePtrVal.toValue 8 wideStr5) helloBytes bytesStr5) ∧
    evalRvalue (dstLocals 8) (.unaryOp .ptrMetadata (.copy { local_ := 5, projection := [] }))
      mem0 dstDecls layouts64 = .ok .unit (dstLocals 8) mem0 ∧
    evalRvalue (dstLocals 4) (.unaryOp .ptrMetadata (.copy { local_ := 5, projection := [] }))
      mem0 dstDecls layouts32 = .ok .unit (dstLocals 4) mem0 :=
  ⟨arr_unsizedDst64.evalRvalue_ptrMetadata (dstLocals 8) (dstLocals 8)
     (.copy { local_ := 1, projection := [] }) dstDecls layouts64 rfl,
   evalRvalue_unaryOp_ptrMetadata_wide (dstLocals 8) (dstLocals 8)
     (.copy { local_ := 2, projection := [] }) mem0 dstDecls layouts64 p9 4 rfl,
   (arr_unsizedDst32.evalRvalue_ptrMetadata (dstLocals 4) (dstLocals 4)
     (.copy { local_ := 3, projection := [] }) dstDecls layouts32 rfl).1,
   str_unsizedDst64.evalRvalue_ptrMetadata (dstLocals 8) (dstLocals 8)
     (.copy { local_ := 4, projection := [] }) dstDecls layouts64 rfl,
   (PtrMetadataOf.thin p9).evalRvalue_ptrMetadata (layouts := layouts64) rfl,
   evalRvalue_unaryOp_ptrMetadata_thin (dstLocals 4) (dstLocals 4)
     (.copy { local_ := 5, projection := [] }) mem0 dstDecls layouts32 p9 rfl⟩

/-- The brief's named forms `evalRvalue_unaryOp_ptrMetadata_slice` and
`evalRvalue_aggregate_rawPtr_slice_roundtrip` on `*mut [u32]` (`_2`). -/
theorem brief_named_slice_metadata_and_roundtrip :
    evalRvalue (dstLocals 8) (.unaryOp .ptrMetadata (.copy { local_ := 2, projection := [] }))
        mem0 dstDecls layouts64 = .ok (.scalar ⟨4, 8⟩) (dstLocals 8) mem0 ∧
    evalRvalue (dstLocals 8)
        (.aggregate (.rawPtr sliceU32Ty .mut)
          [.copy { local_ := 2, projection := [.field 0 ptrU32Ty] },
           .copy { local_ := 2, projection := [.field 1 usizeTy] }])
        mem0 dstDecls layouts64 = .ok (WidePtrVal.toValue 8 wide4) (dstLocals 8) mem0 :=
  ⟨evalRvalue_unaryOp_ptrMetadata_slice _ _ (.copy { local_ := 2, projection := [] }) mem0
      dstDecls layouts64 wide4 rfl,
    evalRvalue_aggregate_rawPtr_slice_roundtrip _ 2 (.uint .u32) 0 ptrU32Ty usizeTy .mut mem0
      dstDecls layouts64 wide4 rfl rfl rfl⟩

/-- Backing 4-element `[u32; 4]` local `_0` and borrow-backed wide pointer `_1`
at tag `77`. -/
def backingArrLocals : List LocalSlot :=
  [.init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]),
   .init (WidePtrVal.toValue 8 (WidePtrVal.mk ⟨77, 0⟩ 4))]

def mutEntry77 : BorrowEntry :=
  { tag := 77, targetLocal := 0, targetProjection := [], perm := .unique,
    rangeOffset := 0, rangeLen := 16 }

theorem mutLens77 :
    ActiveTypedSliceMutBorrow ByteLensCodec.u32LE [mutEntry77] 77
      (WidePtrVal.mk ⟨77, 0⟩ 4) xs4 (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) :=
  ⟨sliceTypedAt_encodeElems ByteLensCodec.u32LE 77 xs4,
   mutEntry77, rfl, ⟨Nat.le_refl 0, Nat.le_refl 16⟩, TreeBorrowPerm.permitsUniqueWrite_unique⟩

/-- `AggregateKind.rawPtr` (`from_raw_parts`) on `[u32]`, `str`, and thin `u32`,
plus decomposed `(data, meta)` `.field 0/1` + `rawPtr` round-trip preserving
`UnsizedSliceDstAt` and followed by a borrow-backed write (with the proof body
also exercising `of_invalidateConflictingBorrows_ne` on `ActiveTypedSliceBorrow`
and `ActiveTypedSliceMutBorrow`). -/
theorem rawPtr_from_raw_parts_and_roundtrip_with_borrow_write :
    evalRvalue (dstLocals 8)
        (.aggregate (.rawPtr sliceU32Ty .not)
          [.copy { local_ := 1, projection := [.field 0 ptrU32Ty] },
           .copy { local_ := 1, projection := [.field 1 usizeTy] }])
        mem0 dstDecls layouts64 = .ok (WidePtrVal.toValue 8 wide4) (dstLocals 8) mem0 ∧
    evalRvalue (dstLocals 8)
        (.aggregate (.rawPtr strPointeeTy .not)
          [.copy { local_ := 4, projection := [.field 0 ptrU32Ty] },
           .copy { local_ := 4, projection := [.field 1 usizeTy] }])
        mem0 dstDecls layouts64 = .ok (WidePtrVal.toValue 8 wideStr5) (dstLocals 8) mem0 ∧
    evalRvalue (dstLocals 8)
        (.aggregate (.rawPtr { kind := .uint .u32, layoutIdx := 0 } .not)
          [.copy { local_ := 5, projection := [] },
           .copy { local_ := 6, projection := [] }])
        mem0 dstDecls layouts64 = .ok (.ptr p9 8) (dstLocals 8) mem0 ∧
    (let memB : Memory := { borrows := [mutEntry77] }
     let wide77 : WidePtrVal := WidePtrVal.mk ⟨77, 0⟩ 4
     (evalRvalue backingArrLocals
        (.aggregate (.rawPtr sliceU32Ty .mut)
          [.copy { local_ := 1, projection := [.field 0 ptrU32Ty] },
           .copy { local_ := 1, projection := [.field 1 usizeTy] }])
        memB [] layouts64 = .ok (WidePtrVal.toValue 8 wide77) backingArrLocals memB ∧
      UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) memB wide77
        (WidePtrVal.toValue 8 wide77) xs4
        (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4)) ∧
     writePlaceValue backingArrLocals memB.borrows
        { local_ := 1, projection := [.deref, .constantIndex 2 0 false] }
        (.scalar ⟨99, 4⟩) [] layouts64 =
       .ok (backingArrLocals.set 0
         (.init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨99, 4⟩, .scalar ⟨4, 4⟩])))) := by
  refine ⟨evalRvalue_aggregate_rawPtr_slice (dstLocals 8) (dstLocals 8) (dstLocals 8)
      (.uint .u32) 0 .not
      (.copy { local_ := 1, projection := [.field 0 ptrU32Ty] })
      (.copy { local_ := 1, projection := [.field 1 usizeTy] })
      mem0 dstDecls layouts64 p9 4 rfl rfl,
    evalRvalue_aggregate_rawPtr_str (dstLocals 8) (dstLocals 8) (dstLocals 8)
      0 .not
      (.copy { local_ := 4, projection := [.field 0 ptrU32Ty] })
      (.copy { local_ := 4, projection := [.field 1 usizeTy] })
      mem0 dstDecls layouts64 p10 5 rfl rfl,
    evalRvalue_aggregate_rawPtr_thin (dstLocals 8) (dstLocals 8) (dstLocals 8)
      { kind := .uint .u32, layoutIdx := 0 } .not
      (.copy { local_ := 5, projection := [] })
      (.copy { local_ := 6, projection := [] })
      mem0 dstDecls layouts64 p9 rfl rfl rfl,
    ?_⟩
  intro memB wide77
  have hNe77_1 : ∀ e, lookupBorrow memB.borrows 77 = some e → e.targetLocal ≠ 1 := by
    intro e hlk
    cases Option.some.inj hlk
    decide
  have hShared77 : ActiveTypedSliceBorrow ByteLensCodec.u32LE memB.borrows 77 wide77 xs4
      (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) :=
    mutLens77.toShared
  have _ : ActiveTypedSliceBorrow ByteLensCodec.u32LE
      (invalidateConflictingBorrows memB.borrows 1 .none 0) 77 wide77 xs4
      (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) :=
    hShared77.of_invalidateConflictingBorrows_ne .none 0 hNe77_1
  have _ : ActiveTypedSliceMutBorrow ByteLensCodec.u32LE
      (invalidateConflictingBorrows memB.borrows 1 .none 0) 77 wide77 xs4
      (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) :=
    mutLens77.of_invalidateConflictingBorrows_ne .none 0 hNe77_1
  have _ : UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) memB wide77
      (WidePtrVal.toValue 8 wide77) xs4
      (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) :=
    UnsizedSliceDstAt.of_borrow 8 (IsUnsizedSliceDstTy.slice (.uint .u32) 4) hShared77
  have hDst77 : UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) memB wide77
      (WidePtrVal.toValue 8 wide77) xs4
      (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) :=
    UnsizedSliceDstAt.of_mutBorrow 8 (IsUnsizedSliceDstTy.slice (.uint .u32) 4) mutLens77
  have _ := hDst77.evalRvalue_len_and_ptrMetadata_borrow backingArrLocals backingArrLocals
    { local_ := 1, projection := [.deref] } (.copy { local_ := 1, projection := [] })
    dstDecls layouts64 [] (.uint .u32) 0 mutEntry77
    [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩] 0
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) (Or.inl rfl)
  have _ := hDst77.evalOperand_field0 backingArrLocals 1 ptrU32Ty [] layouts64 rfl rfl
  have _ := hDst77.evalOperand_field1 backingArrLocals 1 usizeTy [] layouts64 rfl rfl
  refine ⟨hDst77.evalRvalue_aggregate_rawPtr_roundtrip backingArrLocals 1 0 ptrU32Ty usizeTy .mut
      [] layouts64 rfl rfl rfl,
    rfl⟩

/-! ## 4. `size_of_val` and `align_of_val` on `[u32]`, `str`, empty `[u32]`, ZST `[()]`, and sized `u32` -/

def sizeOfValFn (tys : List RigidTy) : Operand :=
  .constant { ty := { kind := .fnDef "core::intrinsics::size_of_val" tys, layoutIdx := 0 }
              val := .zeroSized }

def alignOfValFn (tys : List RigidTy) : Operand :=
  .constant { ty := { kind := .fnDef "core::intrinsics::align_of_val" tys, layoutIdx := 0 }
              val := .zeroSized }

def retBlock (stmts : List Statement) : BasicBlockData :=
  { statements := stmts, terminator := { kind := .return_, span := "ret" }, isCleanup := false }

def sizeAlignSliceCallerMir (elemTy : RigidTy) : CapturedMir :=
  { (Anneal.MirLoops.mkMirBody "test::size_align_slice" 1
      [{ mutability := .mut, ty := { kind := .tuple [.uint .usize, .uint .usize], layoutIdx := 1 },
         debugName := some "_0" },
       { mutability := .not, ty := { kind := .rawPtr .not (.slice elemTy), layoutIdx := 1 },
         debugName := some "ptr" },
       { mutability := .mut, ty := usizeTy, debugName := some "sz" },
       { mutability := .mut, ty := usizeTy, debugName := some "al" }]
      [{ statements := []
         terminator :=
           { kind := .call (sizeOfValFn [.slice elemTy])
               [.copy { local_ := 1, projection := [] }]
               { local_ := 2, projection := [] } (some 1) .continue_
             span := "call_size_of_val" }
         isCleanup := false },
       { statements := []
         terminator :=
           { kind := .call (alignOfValFn [])
               [.copy { local_ := 1, projection := [] }]
               { local_ := 3, projection := [] } (some 2) .continue_
             span := "call_align_of_val_fallback" }
         isCleanup := false },
       retBlock
         [{ kind := .assign { local_ := 0, projection := [] }
              (.aggregate .tuple
                [.copy { local_ := 2, projection := [] },
                 .copy { local_ := 3, projection := [] }])
            span := "mk_layout_tuple" }]]) with
    layouts := layouts64 }

def sizeAlignStrCallerMir : CapturedMir :=
  { (Anneal.MirLoops.mkMirBody "test::size_align_str" 1
      [{ mutability := .mut, ty := { kind := .tuple [.uint .usize, .uint .usize], layoutIdx := 1 },
         debugName := some "_0" },
       { mutability := .not, ty := { kind := .ref .not .str, layoutIdx := 1 },
         debugName := some "s" },
       { mutability := .mut, ty := usizeTy, debugName := some "sz" },
       { mutability := .mut, ty := usizeTy, debugName := some "al" }]
      [{ statements := []
         terminator :=
           { kind := .call (sizeOfValFn [.str])
               [.copy { local_ := 1, projection := [] }]
               { local_ := 2, projection := [] } (some 1) .continue_
             span := "call_size_of_val_str" }
         isCleanup := false },
       { statements := []
         terminator :=
           { kind := .call (alignOfValFn [])
               [.copy { local_ := 1, projection := [] }]
               { local_ := 3, projection := [] } (some 2) .continue_
             span := "call_align_of_val_str_fallback" }
         isCleanup := false },
       retBlock
         [{ kind := .assign { local_ := 0, projection := [] }
              (.aggregate .tuple
                [.copy { local_ := 2, projection := [] },
                 .copy { local_ := 3, projection := [] }])
            span := "mk_layout_tuple" }]]) with
    layouts := layouts64 }

theorem pointee_resolution_typeArgs_and_operand_fallbacks :
    let bodySl := sizeAlignSliceCallerMir (.uint .u32)
    let bodyStr := sizeAlignStrCallerMir
    resolveIntrinsicPointeeTy?
        { defPath := "core::intrinsics::size_of_val", typeArgs := [.slice (.uint .u32)],
          fnSig := none, isIndirect := false }
        bodySl.localDecls bodySl.layouts [.copy { local_ := 1, projection := [] }] =
      some (.slice (.uint .u32)) ∧
    resolveIntrinsicPointeeTy?
        { defPath := "core::intrinsics::align_of_val", typeArgs := [],
          fnSig := none, isIndirect := false }
        bodySl.localDecls bodySl.layouts [.copy { local_ := 1, projection := [] }] =
      some (.slice (.uint .u32)) ∧
    resolveIntrinsicPointeeTy?
        { defPath := "core::intrinsics::align_of_val", typeArgs := [],
          fnSig := none, isIndirect := false }
        bodyStr.localDecls bodyStr.layouts [.copy { local_ := 1, projection := [] }] =
      some .str :=
  ⟨resolveIntrinsicPointeeTy?_of_typeArgs _ _ _ _ (.slice (.uint .u32)) [] rfl,
   resolveIntrinsicPointeeTy?_of_rawPtr_operand _ _ _ _ [] .not (.slice (.uint .u32)) 1 rfl rfl,
   resolveIntrinsicPointeeTy?_of_ref_operand _ _ _ _ [] .not .str 1 rfl rfl⟩

/-- Concrete positive witnesses for `[u32]` (`len = 4 → size = 16, align = 4`),
`str` (`len = 5 → size = 5, align = 1`), empty `[u32]` (`len = 0 → size = 0`),
ZST `[(); 1000]` (`elemSz = 0 → size = 0, align = 1`), and sized `u32`
(`size = 4, align = 4`). -/
theorem size_and_align_positive_witnesses :
    let bodyU32 := sizeAlignSliceCallerMir (.uint .u32)
    let bodyZst := sizeAlignSliceCallerMir (.tuple [])
    let bodyStr := sizeAlignStrCallerMir
    let sU32_0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0,
                   locals := [.uninit, .init (WidePtrVal.toValue 8 wide4), .uninit, .uninit] }
        memory := { mem0 with borrows := [mutEntry77] } }
    let sU32_1 : MachineState :=
      { frame := { blockIdx := 1, stmtIdx := 0,
                   locals := [.uninit, .init (WidePtrVal.toValue 8 wide4),
                              .init (.scalar ⟨16, 8⟩), .uninit] }
        memory := { mem0 with borrows := [mutEntry77] } }
    let sU32_2 : MachineState :=
      { frame := { blockIdx := 2, stmtIdx := 0,
                   locals := [.uninit, .init (WidePtrVal.toValue 8 wide4),
                              .init (.scalar ⟨16, 8⟩), .init (.scalar ⟨4, 8⟩)] }
        memory := { mem0 with borrows := [mutEntry77] } }
    let sStr_0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0,
                   locals := [.uninit, .init (WidePtrVal.toValue 8 wideStr5), .uninit, .uninit] }
        memory := mem0 }
    let sStr_1 : MachineState :=
      { frame := { blockIdx := 1, stmtIdx := 0,
                   locals := [.uninit, .init (WidePtrVal.toValue 8 wideStr5),
                              .init (.scalar ⟨5, 8⟩), .uninit] }
        memory := mem0 }
    let sStr_2 : MachineState :=
      { frame := { blockIdx := 2, stmtIdx := 0,
                   locals := [.uninit, .init (WidePtrVal.toValue 8 wideStr5),
                              .init (.scalar ⟨5, 8⟩), .init (.scalar ⟨1, 8⟩)] }
        memory := mem0 }
    let sEmpty_0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0,
                   locals := [.uninit, .init (WidePtrVal.toValue 8 wideEmpty), .uninit, .uninit] }
        memory := mem0 }
    let sZst_0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0,
                   locals := [.uninit, .init (WidePtrVal.toValue 8 wideZst1000), .uninit, .uninit] }
        memory := mem0 }
    let sEmpty_1 : MachineState :=
      { frame := { blockIdx := 1, stmtIdx := 0,
                   locals := [.uninit, .init (WidePtrVal.toValue 8 wideEmpty),
                              .init (.scalar ⟨0, 8⟩), .uninit] }
        memory := mem0 }
    let sZst_1 : MachineState :=
      { frame := { blockIdx := 1, stmtIdx := 0,
                   locals := [.uninit, .init (WidePtrVal.toValue 8 wideZst1000),
                              .init (.scalar ⟨0, 8⟩), .uninit] }
        memory := mem0 }
    let sZst_2 : MachineState :=
      { frame := { blockIdx := 2, stmtIdx := 0,
                   locals := [.uninit, .init (WidePtrVal.toValue 8 wideZst1000),
                              .init (.scalar ⟨0, 8⟩), .init (.scalar ⟨1, 8⟩)] }
        memory := mem0 }
    evalSliceSizeOfVal 0 ⟨1000, 8⟩ = some ⟨0, 8⟩ ∧
    evalSliceSizeOfVal 4 ⟨0, 8⟩ = some ⟨0, 8⟩ ∧
    (PureMirExec.mirStep bodyU32 sU32_0 = .cont sU32_1 ∧
     ActiveTypedSliceMutBorrow ByteLensCodec.u32LE sU32_1.memory.borrows 77
       (WidePtrVal.mk ⟨77, 0⟩ 4) xs4 (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) ∧
     ActiveTypedSliceBorrow ByteLensCodec.u32LE sU32_1.memory.borrows 77
       (WidePtrVal.mk ⟨77, 0⟩ 4) xs4 (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4)) ∧
    (PureMirExec.mirStep bodyU32 sU32_1 = .cont sU32_2 ∧
     ActiveTypedSliceMutBorrow ByteLensCodec.u32LE sU32_2.memory.borrows 77
       (WidePtrVal.mk ⟨77, 0⟩ 4) xs4 (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) ∧
     ActiveTypedSliceBorrow ByteLensCodec.u32LE sU32_2.memory.borrows 77
       (WidePtrVal.mk ⟨77, 0⟩ 4) xs4 (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4)) ∧
    PureMirExec.mirStep bodyStr sStr_0 = .cont sStr_1 ∧
    PureMirExec.mirStep bodyStr sStr_1 = .cont sStr_2 ∧
    PureMirExec.mirStep bodyU32 sEmpty_0 = .cont sEmpty_1 ∧
    PureMirExec.mirStep bodyZst sZst_0 = .cont sZst_1 ∧
    PureMirExec.mirStep bodyZst sZst_1 = .cont sZst_2 ∧
    evalNonSelectIntrinsicCall .sizeOfVal sStr_0
      { defPath := "core::intrinsics::size_of_val", typeArgs := [.uint .u32],
        fnSig := none, isIndirect := false }
      bodyU32.localDecls bodyU32.layouts [] [.ptr p9 8] sStr_0.frame.locals
      { local_ := 2, projection := [] } 1 =
      writeIntrinsicReturn sStr_0 sStr_0.frame.locals { local_ := 2, projection := [] } 1
        (.scalar ⟨4, 8⟩) ∧
    evalNonSelectIntrinsicCall .alignOfVal sStr_0
      { defPath := "core::intrinsics::align_of_val", typeArgs := [.uint .u32],
        fnSig := none, isIndirect := false }
      bodyU32.localDecls bodyU32.layouts [] [.ptr p9 8] sStr_0.frame.locals
      { local_ := 3, projection := [] } 1 =
      writeIntrinsicReturn sStr_0 sStr_0.frame.locals { local_ := 3, projection := [] } 1
        (.scalar ⟨4, 8⟩) := by
  intro bodyU32 bodyZst bodyStr sU32_0 sU32_1 sU32_2 sStr_0 sStr_1 sStr_2 sEmpty_0 sZst_0
    sEmpty_1 sZst_1 sZst_2
  have hDisj2 : ∀ e ∈ sU32_0.memory.borrows, e.targetLocal ≠ 2 := by
    intro e he
    cases he with
    | head => decide
    | tail _ h => cases h
  have hDisj3 : ∀ e ∈ sU32_1.memory.borrows, e.targetLocal ≠ 3 := by
    intro e he
    cases he with
    | head => decide
    | tail _ h => cases h
  have hInv2 : invalidateDirectDestWriteBorrows sU32_0.memory sU32_0.frame.locals
      { local_ := 2, projection := [] } = sU32_0.memory :=
    invalidateDirectDestWriteBorrows_eq_self_of_forall_ne sU32_0.memory sU32_0.frame.locals 2 hDisj2
  have hInv3 : invalidateDirectDestWriteBorrows sU32_1.memory sU32_1.frame.locals
      { local_ := 3, projection := [] } = sU32_1.memory :=
    invalidateDirectDestWriteBorrows_eq_self_of_forall_ne sU32_1.memory sU32_1.frame.locals 3 hDisj3
  have hNe77_2 : ∀ e, lookupBorrow sU32_0.memory.borrows 77 = some e → e.targetLocal ≠ 2 := by
    intro e hlk
    cases Option.some.inj hlk
    decide
  have hNe77_3 : ∀ e, lookupBorrow sU32_1.memory.borrows 77 = some e → e.targetLocal ≠ 3 := by
    intro e hlk
    cases Option.some.inj hlk
    decide
  obtain ⟨_, hMirU32_1, hDstU32_1, hShU32_1, hMutU32_1⟩ :=
    evalIntrinsic_sizeOfValRaw_slice (body := bodyU32) (cur := bodyU32) (s := sU32_0)
      (arr_unsizedDst64.of_frame rfl (fun _ h => by cases h))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  have hStep1 : PureMirExec.mirStep bodyU32 sU32_0 = .cont sU32_1 := by
    rw [hInv2] at hMirU32_1
    exact hMirU32_1
  have hMut1 := hMutU32_1 77 mutLens77 hNe77_2
  have hSh1 := hShU32_1 77 mutLens77.toShared hNe77_2
  rw [hInv2] at hMut1 hSh1
  obtain ⟨_, hMirU32_2, _, hShU32_2, hMutU32_2⟩ :=
    evalIntrinsic_alignOfValRaw_slice (body := bodyU32) (cur := bodyU32) (s := sU32_1)
      (alignBytes := 4)
      (arr_unsizedDst64.of_frame rfl (fun _ h => by cases h))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  have hStep2 : PureMirExec.mirStep bodyU32 sU32_1 = .cont sU32_2 := by
    rw [hInv3] at hMirU32_2
    exact hMirU32_2
  have hMut2 := hMutU32_2 77 mutLens77 hNe77_3
  have hSh2 := hShU32_2 77 mutLens77.toShared hNe77_3
  rw [hInv3] at hMut2 hSh2
  obtain ⟨_, hMirStr_1, hDstStr_1⟩ :=
    evalIntrinsic_sizeOfValRaw_str (body := bodyStr) (cur := bodyStr) (s := sStr_0)
      str_unsizedDst64 rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  obtain ⟨_, hMirStr_2, _⟩ :=
    evalIntrinsic_alignOfValRaw_str (body := bodyStr) (cur := bodyStr) (s := sStr_1)
      (hDstStr_1 (fun _ h => by cases h)) rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl
      (by decide) rfl rfl rfl
  obtain ⟨_, hMirEmpty, _, _, _⟩ :=
    evalIntrinsic_sizeOfValRaw_slice (body := bodyU32) (cur := bodyU32) (s := sEmpty_0)
      (locals' := sEmpty_0.frame.locals) (updatedLocals := sEmpty_1.frame.locals)
      empty_and_zst_unsizedDst_witnesses.1
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  obtain ⟨_, hMirZst, _, _⟩ :=
    evalIntrinsic_sizeOfValRaw_slice_wide (body := bodyZst) (cur := bodyZst) (s := sZst_0)
      (locals' := sZst_0.frame.locals) (updatedLocals := sZst_1.frame.locals)
      empty_and_zst_unsizedDst_witnesses.2.2
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  -- ZST `align_of_val::<[()]>` (`operandTy` fallback) writes `1`.
  obtain ⟨_, hMirZstAl, _, _, _⟩ :=
    evalIntrinsic_alignOfValRaw_slice (body := bodyZst) (cur := bodyZst) (s := sZst_1)
      (alignBytes := 1) (locals' := sZst_1.frame.locals) (updatedLocals := sZst_2.frame.locals)
      empty_and_zst_unsizedDst_witnesses.2.2
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  exact ⟨evalSliceSizeOfVal_zst 1000,
    evalSliceSizeOfVal_empty 4,
    ⟨hStep1, hMut1, hSh1⟩,
    ⟨hStep2, hMut2, hSh2⟩,
    hMirStr_1,
    hMirStr_2,
    hMirEmpty,
    hMirZst,
    hMirZstAl,
    evalNonSelectIntrinsicCall_sizeOfVal_sized sStr_0 _ bodyU32.localDecls bodyU32.layouts []
      sStr_0.frame.locals { local_ := 2, projection := [] } 1 (.uint .u32) 4 p9
      rfl rfl rfl rfl (by decide),
    evalNonSelectIntrinsicCall_alignOfVal_sized sStr_0 _ bodyU32.localDecls bodyU32.layouts []
      sStr_0.frame.locals { local_ := 3, projection := [] } 1 (.uint .u32) 4 p9
      rfl rfl rfl rfl⟩

/-- `let (data, len) = (p.cast::<()>(), ptr::metadata(p)); let q = ptr::from_raw_parts(data, len)`
exactly as rustc lowers `to_raw_parts` / `from_raw_parts` (`PtrToPtr` cast, `PtrMetadata`,
`AggregateKind.rawPtr`), not via field projections. -/
def rawPartsBody : CapturedMir :=
  { (Anneal.MirLoops.mkMirBody "test::to_raw_parts_from_raw_parts" 1
      [{ mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 }, debugName := some "_0" },
       { mutability := .not, ty := { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 1 },
         debugName := some "p" },
       { mutability := .mut, ty := { kind := .rawPtr .not (.tuple []), layoutIdx := 0 },
         debugName := some "data" },
       { mutability := .mut, ty := usizeTy, debugName := some "len" },
       { mutability := .mut, ty := { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 1 },
         debugName := some "q" }]
      [retBlock
        [{ kind := .assign { local_ := 2, projection := [] }
             (.cast .ptrToPtr (.copy { local_ := 1, projection := [] })
               { kind := .rawPtr .not (.tuple []), layoutIdx := 0 })
           span := "p_cast_unit" },
         { kind := .assign { local_ := 3, projection := [] }
             (.unaryOp .ptrMetadata (.copy { local_ := 1, projection := [] }))
           span := "ptr_metadata" },
         { kind := .assign { local_ := 4, projection := [] }
             (.aggregate (.rawPtr sliceU32Ty .not)
               [.copy { local_ := 2, projection := [] }, .copy { local_ := 3, projection := [] }])
           span := "from_raw_parts" }]]) with
    layouts := layouts64 }

def rawPartsLocals0 : List LocalSlot :=
  [.init .unit, .init (WidePtrVal.toValue 8 wide4), .uninit, .uninit, .uninit]

def rawPartsLocals1 : List LocalSlot :=
  [.init .unit, .init (WidePtrVal.toValue 8 wide4), .init (.ptr p9 8), .uninit, .uninit]

def rawPartsLocals2 : List LocalSlot :=
  [.init .unit, .init (WidePtrVal.toValue 8 wide4), .init (.ptr p9 8), .init (.scalar ⟨4, 8⟩),
   .uninit]

def rawPartsLocals3 : List LocalSlot :=
  [.init .unit, .init (WidePtrVal.toValue 8 wide4), .init (.ptr p9 8), .init (.scalar ⟨4, 8⟩),
   .init (WidePtrVal.toValue 8 wide4)]

/-- **Realistic `to_raw_parts` / `from_raw_parts` round trip (rustc lowering)** on the
global-backed `*const [u32]` `_1` (no borrow at `p9`'s tag): `_2 = copy _1 as *const ()`
(`PtrToPtr`, the data half), `_3 = PtrMetadata(copy _1)`, and
`_4 = *const [u32] from (copy _2, copy _3)` step through the lifters and rebuild `_1`'s wide pointer
exactly, the global-backed `UnsizedSliceDstAt` lens still holds in the final memory, and a
`*const [u32] as *mut [u32]` cast keeps the wide pointer unchanged. -/
theorem realistic_to_raw_parts_from_raw_parts_roundtrip :
    let s0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := rawPartsLocals0 }, memory := mem0 }
    ∃ s1 s2 s3,
      PureMirExec.mirStep rawPartsBody s0 = .cont s1 ∧
      PureMirExec.mirStep rawPartsBody s1 = .cont s2 ∧
      PureMirExec.mirStep rawPartsBody s2 = .cont s3 ∧
      s3.frame.locals = rawPartsLocals3 ∧
      get? s3.frame.locals 4 = get? s0.frame.locals 1 ∧
      UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) s3.memory wide4
        (WidePtrVal.toValue 8 wide4) xs4 bytes16 ∧
      evalRvalue rawPartsLocals0
          (.cast .ptrToPtr (.copy { local_ := 1, projection := [] })
            { kind := .rawPtr .mut (.slice (.uint .u32)), layoutIdx := 1 })
          mem0 rawPartsBody.localDecls layouts64 =
        .ok (WidePtrVal.toValue 8 wide4) rawPartsLocals0 mem0 := by
  intro s0
  let s1 : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 1, locals := rawPartsLocals1 }, memory := mem0 }
  let s2 : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 2, locals := rawPartsLocals2 }, memory := mem0 }
  let s3 : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 3, locals := rawPartsLocals3 }, memory := mem0 }
  obtain ⟨_, h1, _, _⟩ := mirStep_assign_cast_ptrToPtr_wide_to_thin (body := rawPartsBody)
    (cur := rawPartsBody) (s := s0) (dstLoc := 2) (q := p9) (len := 4)
    (locals₁ := rawPartsLocals0) (locals₂ := rawPartsLocals1)
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have _ := evalRvalue_cast_ptrToPtr_wide_to_thin rawPartsLocals0 rawPartsLocals0
    (.copy { local_ := 1, projection := [] })
    { kind := .rawPtr .not (.tuple []), layoutIdx := 0 } mem0 rawPartsBody.localDecls layouts64
    p9 4 rfl rfl rfl
  have _ := arr_unsizedDst64.evalRvalue_cast_ptrToPtr_to_thin_global rawPartsLocals0 rawPartsLocals0
    (.copy { local_ := 1, projection := [] })
    { kind := .rawPtr .not (.tuple []), layoutIdx := 0 } rawPartsBody.localDecls layouts64
    rfl rfl rfl
  have _ := arr_unsizedDst64.evalRvalue_cast_ptrToPtr_wide_to_wide rawPartsLocals0 rawPartsLocals0
    (.copy { local_ := 1, projection := [] })
    { kind := .rawPtr .mut (.slice (.uint .u32)), layoutIdx := 1 } rawPartsBody.localDecls
    layouts64 rfl rfl rfl
  obtain ⟨_, h2, _, _⟩ := mirStep_assign_local (body := rawPartsBody) (cur := rawPartsBody)
    (s := s1) (dstLoc := 3) (val := .scalar ⟨4, 8⟩) (locals₁ := rawPartsLocals1) (mem₁ := mem0)
    (locals₂ := rawPartsLocals2) rfl (Or.inl rfl) rfl rfl
    (evalRvalue_unaryOp_ptrMetadata_slice rawPartsLocals1 rawPartsLocals1
      (.copy { local_ := 1, projection := [] }) mem0 rawPartsBody.localDecls layouts64 wide4 rfl)
    rfl rfl rfl rfl
  obtain ⟨_, h3, _, _⟩ := mirStep_assign_local (body := rawPartsBody) (cur := rawPartsBody)
    (s := s2) (dstLoc := 4) (val := WidePtrVal.toValue 8 wide4) (locals₁ := rawPartsLocals2)
    (mem₁ := mem0) (locals₂ := rawPartsLocals3) rfl (Or.inl rfl) rfl rfl
    (evalRvalue_aggregate_rawPtr_slice rawPartsLocals2 rawPartsLocals2 rawPartsLocals2 (.uint .u32)
      0 .not (.copy { local_ := 2, projection := [] }) (.copy { local_ := 3, projection := [] })
      mem0 rawPartsBody.localDecls layouts64 p9 4 rfl rfl)
    rfl rfl rfl rfl
  exact ⟨s1, s2, s3, h1, h2, h3, rfl, rfl, arr_unsizedDst64,
    evalRvalue_cast_ptrToPtr_wide_to_wide rawPartsLocals0 rawPartsLocals0
      (.copy { local_ := 1, projection := [] }) _ mem0 rawPartsBody.localDecls layouts64 p9 4
      rfl rfl rfl⟩

/-- Subslice-backed borrow entry (`targetProjection = [.subslice 0 4 false]`) on `backingArrLocals`. -/
def subsliceEntry77 : BorrowEntry :=
  { tag := 77, targetLocal := 0, targetProjection := [.subslice 0 4 false], perm := .unique,
    rangeOffset := 0, rangeLen := 16 }

/-- **Borrow-backed `CastKind.ptrToPtr` (`p as *const ()`) characterization**:
1. When the borrow entry already ends with `.subslice 0 4 false` (`subsliceEntry77`),
   `evalRvalue_cast_ptrToPtr_wide_to_thin_already_subslice` returns `.ok (.ptr ⟨77, 0⟩ 8)` with
   `mem` **unchanged** (`alreadySubslice = true`), so `(p as *const (), PtrMetadata(p))` +
   `AggregateKind.rawPtr` is the exact identity even on borrow-backed slice pointers!
2. When the borrow entry targets the whole array with `targetProjection = []` (`mutEntry77`),
   `evalRvalue_cast_ptrToPtr_wide_to_thin_fresh_subslice` allocates a fresh narrowed subslice
   borrow entry at `mem.nextTag = 78` (`targetProjection = [.subslice 0 4 false]`). -/
theorem borrow_backed_ptrToPtr_already_subslice_and_fresh_subslice :
    let unitPtrTy : Ty := { kind := .rawPtr .not (.tuple []), layoutIdx := 0 }
    let memSub : Memory := { borrows := [subsliceEntry77], nextTag := 78 }
    let memArr : Memory := { borrows := [mutEntry77], nextTag := 78 }
    let child78 : BorrowEntry :=
      { tag := 78, targetLocal := 0, targetProjection := [.subslice 0 4 false], perm := .unique }
    evalRvalue backingArrLocals (.cast .ptrToPtr (.copy { local_ := 1, projection := [] }) unitPtrTy)
        memSub [] layouts64 = .ok (.ptr ⟨77, 0⟩ 8) backingArrLocals memSub ∧
    evalRvalue backingArrLocals (.cast .ptrToPtr (.copy { local_ := 1, projection := [] }) unitPtrTy)
        memArr [] layouts64 =
      .ok (.ptr ⟨78, 0⟩ 8) backingArrLocals
        { memArr with borrows := child78 :: memArr.borrows, nextTag := 79 } := by
  intro unitPtrTy memSub memArr child78
  exact ⟨evalRvalue_cast_ptrToPtr_wide_to_thin_already_subslice backingArrLocals backingArrLocals
      (.copy { local_ := 1, projection := [] }) unitPtrTy memSub [] layouts64 ⟨77, 0⟩ 4
      subsliceEntry77 (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩])
      [.subslice 0 4 false] 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩] 0
      rfl rfl rfl (fun h => by cases h) rfl rfl rfl rfl rfl,
    evalRvalue_cast_ptrToPtr_wide_to_thin_fresh_subslice backingArrLocals backingArrLocals
      (.copy { local_ := 1, projection := [] }) unitPtrTy memArr [] layouts64 ⟨77, 0⟩ 4
      mutEntry77 (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩])
      [] 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩] 0
      rfl rfl rfl (fun h => by cases h) rfl rfl rfl rfl rfl⟩

/-! ## 5. End-to-End `MirWpConverges` & `PureLift.V2026_06_01Bridge` Spatial-Pin Preservation -/

def tagOfLoan (lid : LoanId) : Nat := lid + 77

def pinCodec : SpatialCodec StdVal := u32SpatialCodec layouts64

/-- The pinned place `_2 : [u32; 4]` (element layout `u32Layout`). -/
def pinArrTy : Ty := { kind := .array (.uint .u32) 4, layoutIdx := 0 }

/-- `[1u32, 2, 3, 4]`. -/
def pinArrVal : Value :=
  .aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]

/-- `*const [u32]` raw slice pointer `(&raw const _2) as *const [u32]` carrying borrow tag `77`
(`= tagOfLoan 0`) over the pinned array's `16` bytes. -/
def wide77 : WidePtrVal := WidePtrVal.mk ⟨77, 0⟩ 4

/-- Callee body (run with an active protector, which the `activeProtectors = []`-only lifters
could not step): `_4 = PtrMetadata(copy _1)`, `_5 = from_raw_parts(copy (_1.0), move _4)`,
`_6 = size_of_val::<[u32]>(copy _5)`, `_7 = align_of_val::<[u32]>(move _5)`,
`_0 = (move _6, move _7)` (`Layout::for_value_raw`). -/
def pinBody : CapturedMir :=
  { (Anneal.MirLoops.mkMirBody "test::dst_metadata_layout_with_pinned_array" 1
      [{ mutability := .mut, ty := { kind := .tuple [.uint .usize, .uint .usize], layoutIdx := 1 },
         debugName := some "_0" },
       { mutability := .not, ty := { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 1 },
         debugName := some "raw_sl" },
       { mutability := .mut, ty := pinArrTy, debugName := some "pinned_arr" },
       { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 0 },
         debugName := some "bound_u32" },
       { mutability := .mut, ty := usizeTy, debugName := some "meta_len" },
       { mutability := .mut, ty := { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 1 },
         debugName := some "rebuilt_sl" },
       { mutability := .mut, ty := usizeTy, debugName := some "sz" },
       { mutability := .mut, ty := usizeTy, debugName := some "al" }]
      [{ statements :=
           [{ kind := .assign { local_ := 4, projection := [] }
                (.unaryOp .ptrMetadata (.copy { local_ := 1, projection := [] }))
              span := "stmt_ptr_metadata" },
            { kind := .assign { local_ := 5, projection := [] }
                (.aggregate (.rawPtr sliceU32Ty .not)
                  [.copy { local_ := 1, projection := [.field 0 ptrU32Ty] },
                   .move { local_ := 4, projection := [] }])
              span := "stmt_from_raw_parts" }]
         terminator :=
           { kind := .call (sizeOfValFn [.slice (.uint .u32)])
               [.copy { local_ := 5, projection := [] }]
               { local_ := 6, projection := [] } (some 1) .continue_
             span := "term_size_of_val" }
         isCleanup := false },
       { statements := []
         terminator :=
           { kind := .call (alignOfValFn [.slice (.uint .u32)])
               [.move { local_ := 5, projection := [] }]
               { local_ := 7, projection := [] } (some 2) .continue_
             span := "term_align_of_val" }
         isCleanup := false },
       retBlock
         [{ kind := .assign { local_ := 0, projection := [] }
              (.aggregate .tuple
                [.move { local_ := 6, projection := [] },
                 .move { local_ := 7, projection := [] }])
            span := "stmt_layout_tuple" }]]) with
    layouts := layouts64 }

/-- Tag `77`: unique borrow of the whole pinned array `_2` (`16` bytes); tag `78`: unique borrow
of the bound `_3 : u32`. -/
def pinBorrows : List BorrowEntry :=
  [{ tag := 77, targetLocal := 2, targetProjection := [], perm := .unique,
     rangeOffset := 0, rangeLen := 16 },
   { tag := 78, targetLocal := 3, targetProjection := [], perm := .unique,
     rangeOffset := 0, rangeLen := 4 }]

def pinSt : SymState StdVal :=
  ⟨[⟨stdWideSliceVal 0 4, .unborrowed⟩, ⟨.nat 42, .mutLocked 0⟩, ⟨.nat 99, .mutLocked 1⟩],
   [⟨0, .spatialPinned 0 pinCodec, ⟨.nat 42, .unborrowed⟩, .direct (.localReg 1) []⟩,
    ⟨1, .activeMut, ⟨.nat 99, .unborrowed⟩, .direct (.localReg 2) []⟩],
   [], [],
   [⟨0, 0, .readWrite, 0, 0,
     [.rawByte 1, .rawByte 0, .rawByte 0, .rawByte 0, .rawByte 2, .rawByte 0, .rawByte 0, .rawByte 0,
      .rawByte 3, .rawByte 0, .rawByte 0, .rawByte 0, .rawByte 4, .rawByte 0, .rawByte 0,
      .rawByte 0]⟩],
   1⟩

def pinMs0 : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0,
        locals :=
          [.uninit,
           .init (WidePtrVal.toValue 8 wide77),
           .init pinArrVal,
           .init (.scalar ⟨99, 4⟩),
           .uninit, .uninit, .uninit, .uninit] }
    memory := { borrows := pinBorrows, activeProtectors := [5] } }

theorem pinMs0_pinned_and_bound :
    spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] pinSt pinMs0 ∧
    spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt pinMs0 ∧
    mirStateRel tagOfLoan [(1, 3, [])] pinSt pinMs0 := by
  have hPin : spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] pinSt pinMs0 :=
    ⟨_, _, [], _, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      ⟨_, rfl, rfl, rfl, rfl⟩⟩
  have hBind : spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt pinMs0 :=
    ⟨⟨trivial, trivial⟩,
      ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩
  have hLoc : mirLocalsRel tagOfLoan pinSt pinMs0 :=
    mirLocalsRel_of_localsRefine
      (And.intro
        (fun _ => ⟨_, rfl, StdValRefines.wideSlice8 tagOfLoan 0 wide77 rfl rfl (by decide)⟩)
        (And.intro (fun h => nomatch h) (And.intro (fun h => nomatch h) trivial)))
  exact ⟨hPin, hBind, hBind, hLoc⟩

/-- **Coherence**: the pinned block's bytes, the live MIR byte window of `_2 : [u32; 4]`, and the
`SliceTypedAt` image of the raw slice pointer `wide77` are the same `16` bytes. -/
theorem pinned_window_eq_slice_image :
    placeByteWindow? layouts64 pinArrTy pinMs0 2 [] =
      some (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) := rfl

/-- The raw slice pointer `wide77` is a live `&mut [u32]`-style lens through tag `77` covering
the pinned array's `16` bytes. -/
theorem pinMutLens77 :
    ActiveTypedSliceMutBorrow ByteLensCodec.u32LE pinMs0.memory.borrows 77 wide77 xs4
      (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) :=
  ⟨sliceTypedAt_encodeElems ByteLensCodec.u32LE 77 xs4, _, rfl,
    ⟨Nat.le_refl 0, Nat.le_refl 16⟩, TreeBorrowPerm.permitsUniqueWrite_unique⟩

/-- `UnsizedSliceDstAt` for `wide77`, backed by the live borrow `77` in `pinMs0.memory`. -/
theorem pinDst77 :
    UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) pinMs0.memory wide77
      (WidePtrVal.toValue 8 wide77) xs4 (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) :=
  UnsizedSliceDstAt.of_mutBorrow 8 (IsUnsizedSliceDstTy.slice (.uint .u32) 4) pinMutLens77

/-- **Borrow-tag pinning soundness canary**: even though `pinMs0.memory` has a live borrow `77`
covering `16` bytes, a wide pointer `WidePtrVal.mk ⟨999, 0⟩ 4` carrying a bogus/dead provenance tag
`999` is *not* an `UnsizedSliceDstAt` lens in `pinMs0.memory` (cannot hijack borrow `77`). -/
theorem unsizedDst_rejects_unrelated_borrow_tag :
    let wideBogus : WidePtrVal := WidePtrVal.mk ⟨999, 0⟩ 4
    ¬ UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) pinMs0.memory wideBogus
      (WidePtrVal.toValue 8 wideBogus) xs4
      (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) := by
  intro wideBogus h
  rcases h.image_or_activeBorrow_or_zeroSized with ⟨_, hA, _⟩ | ⟨_, _, hL, _, _⟩ | hZ
  · cases hA
  · cases hL
  · exact absurd hZ (by decide)

/-- From `∀ e ∈ borrows, e.targetLocal ≠ d` (decidable on concrete tables) to the lookup form
consumed by the `UnsizedSliceDstAt` frame rules. -/
theorem lookupBorrow_targetLocal_ne_of_forall_mem {borrows : List BorrowEntry} {d : Local}
    (h : ∀ e ∈ borrows, e.targetLocal ≠ d) (tag : Nat) :
    ∀ e, lookupBorrow borrows tag = some e → e.targetLocal ≠ d :=
  fun e he => h e (lookupBorrow_mem_and_tag he).1

/-- **Wide-slice `StdValRefines` constructor, field projections, inversion, and round-trip**. -/
theorem wideSlice_stdValRefines_witnesses :
    stdValAlg.getField 0 (stdWideSliceVal 0 4) = some (.refVal 0 []) ∧
    stdValAlg.getField 1 (stdWideSliceVal 0 4) = some (.nat 4) ∧
    StdValRefines tagOfLoan (stdWideSliceVal 0 4) (WidePtrVal.toValue 8 wide77) ∧
    (StdValRefines tagOfLoan (.refVal 0 []) (WidePtrVal.dataVal 8 wide77) ∧
     StdValRefines tagOfLoan (.nat 4) (WidePtrVal.metaVal 8 wide77)) ∧
    (wide77.1.allocId = tagOfLoan 0 ∧ wide77.1.offsetBytes = 0 ∧ wide77.2 = 4 ∧ 4 < 256 ^ 8) ∧
    StdValRefines tagOfLoan (stdWideSliceVal 0 xs4.length) (WidePtrVal.toValue 8 wide77) ∧
    (evalRvalue pinMs0.frame.locals (.unaryOp .ptrMetadata (.copy { local_ := 1, projection := [] }))
       pinMs0.memory pinBody.localDecls layouts64 =
       .ok (.scalar ⟨xs4.length, 8⟩) pinMs0.frame.locals pinMs0.memory ∧
     StdValRefines tagOfLoan (.nat xs4.length) (.scalar ⟨xs4.length, 8⟩)) ∧
    (evalRvalue pinMs0.frame.locals
       (.aggregate (.rawPtr sliceU32Ty .not)
         [.copy { local_ := 1, projection := [.field 0 ptrU32Ty] },
          .copy { local_ := 1, projection := [.field 1 usizeTy] }])
       pinMs0.memory pinBody.localDecls layouts64 =
       .ok (WidePtrVal.toValue 8 wide77) pinMs0.frame.locals pinMs0.memory ∧
     StdValRefines tagOfLoan (stdWideSliceVal 0 xs4.length) (WidePtrVal.toValue 8 wide77) ∧
     UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32))
       pinMs0.memory wide77 (WidePtrVal.toValue 8 wide77) xs4
       (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4)) := by
  have hRef8 : StdValRefines tagOfLoan (stdWideSliceVal 0 4) (WidePtrVal.toValue 8 wide77) :=
    StdValRefines.wideSlice8 tagOfLoan 0 wide77 rfl rfl (by decide)
  exact ⟨stdWideSliceVal_getField_zero 0 4,
    stdWideSliceVal_getField_one 0 4,
    hRef8,
    StdValRefines.wideSlice_data_and_meta tagOfLoan 0 8 wide77 rfl rfl (by decide),
    hRef8.wideSlice_toValue_inv,
    StdValRefines.of_unsizedSliceDstAt tagOfLoan 0 pinDst77 rfl rfl (by decide),
    StdValRefines.wideSlice_ptrMetadata_refines tagOfLoan pinMs0.frame.locals pinMs0.frame.locals
      (.copy { local_ := 1, projection := [] }) pinBody.localDecls layouts64 pinDst77 (by decide)
      rfl,
    StdValRefines.wideSlice_from_raw_parts_roundtrip tagOfLoan 0 pinMs0.frame.locals 1 0
      ptrU32Ty usizeTy .not pinBody.localDecls layouts64 pinDst77
      (StdValRefines.of_unsizedSliceDstAt tagOfLoan 0 pinDst77 rfl rfl (by decide))
      rfl rfl rfl⟩

/-- Locals after `_4 = PtrMetadata(copy _1)`. -/
def pinLocals1 : List LocalSlot :=
  [.uninit, .init (WidePtrVal.toValue 8 wide77), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
   .init (.scalar ⟨4, 8⟩), .uninit, .uninit, .uninit]

/-- Locals after evaluating `[copy (_1.0), move _4]` (`_4` moved out). -/
def pinLocals1Moved : List LocalSlot :=
  [.uninit, .init (WidePtrVal.toValue 8 wide77), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
   .uninit, .uninit, .uninit, .uninit]

/-- Locals after `_5 = from_raw_parts(copy (_1.0), move _4)`. -/
def pinLocals2 : List LocalSlot :=
  [.uninit, .init (WidePtrVal.toValue 8 wide77), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
   .uninit, .init (WidePtrVal.toValue 8 wide77), .uninit, .uninit]

/-- Locals after `_6 = size_of_val(copy _5)`. -/
def pinLocals3 : List LocalSlot :=
  [.uninit, .init (WidePtrVal.toValue 8 wide77), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
   .uninit, .init (WidePtrVal.toValue 8 wide77), .init (.scalar ⟨16, 8⟩), .uninit]

/-- Locals after evaluating `[move _5]` (`_5` moved out). -/
def pinLocals3Moved : List LocalSlot :=
  [.uninit, .init (WidePtrVal.toValue 8 wide77), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
   .uninit, .uninit, .init (.scalar ⟨16, 8⟩), .uninit]

/-- Locals after `_7 = align_of_val(move _5)`. -/
def pinLocals4 : List LocalSlot :=
  [.uninit, .init (WidePtrVal.toValue 8 wide77), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
   .uninit, .uninit, .init (.scalar ⟨16, 8⟩), .init (.scalar ⟨4, 8⟩)]

/-- Locals after evaluating `[move _6]` and then `[move _7]`. -/
def pinLocals4Moved6 : List LocalSlot :=
  [.uninit, .init (WidePtrVal.toValue 8 wide77), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
   .uninit, .uninit, .uninit, .init (.scalar ⟨4, 8⟩)]

def pinLocals4Moved : List LocalSlot :=
  [.uninit, .init (WidePtrVal.toValue 8 wide77), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
   .uninit, .uninit, .uninit, .uninit]

/-- Locals after `_0 = (move _6, move _7)`. -/
def pinLocals5 : List LocalSlot :=
  [.init (.aggregate 0 [.scalar ⟨16, 8⟩, .scalar ⟨4, 8⟩]),
   .init (WidePtrVal.toValue 8 wide77), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
   .uninit, .uninit, .uninit, .uninit]

/-- Non-trivial per-block `extra` invariant for `mirCfgStateRel` carrying both the spatial pin on
`_2 : [u32; 4]` and the borrow-backed `UnsizedSliceDstAt` lens of `wide77`. -/
def pinCfgExtra (_ : Nat) (st : SymState StdVal) (ms : MachineState) : Prop :=
  spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] st ms ∧
    UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) ms.memory wide77
      (WidePtrVal.toValue 8 wide77) xs4 (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4)

/-- **End-to-end multi-step `MirWpConverges` + spatial-pin + unsized-lens preservation** with an
active protector (`activeProtectors = [5]`): steps across
`UnOp.ptrMetadata`, `AggregateKind.rawPtr` (`from_raw_parts`, with a `move` metadata operand),
`core::intrinsics::size_of_val`, `core::intrinsics::align_of_val` (with a `move` argument), and
`Layout::for_value_raw` `(size, align)` tuple assembly (`move` operands), proving
`MirWpConverges` to `(16usize, 4usize)` *compositionally* (chaining the per-step
`MirWpConverges` transports of the `*_preserves_spatialPin` lemmas into the final `return`), that
the spatial pin on `_2 : [u32; 4]`, the loan binding on `_3` (`mirStateRel` at the exit), and the
borrow-backed `UnsizedSliceDstAt` lens of the raw slice pointer into the pinned array remain
intact after every step (`ms1..ms5`), with `ActiveTypedSliceMutBorrow` also checked at `ms4` after
both intrinsic calls, and that both `bb0` (3-step multi-statement + `size_of_val` block) and `bb1`
(`align_of_val` block) are `BlockCfg` segments re-establishing `mirCfgStateRel` with the
non-trivial `pinCfgExtra` invariant. -/
theorem dst_metadata_and_layout_converges_preserving_spatialPin :
    Anneal.MirFuelFree.MirWpConverges pinBody pinMs0
      (fun out =>
        ∃ mem',
          out = .normal (.aggregate 0 [.scalar ⟨16, 8⟩, .scalar ⟨4, 8⟩], mem')) ∧
    ∃ ms1 ms2 ms3 ms4 ms5,
      PureMirExec.mirStep pinBody pinMs0 = .cont ms1 ∧
      spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] pinSt ms1 ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt ms1 ∧
      UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) ms1.memory wide77
        (WidePtrVal.toValue 8 wide77) xs4 (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) ∧
      PureMirExec.mirStep pinBody ms1 = .cont ms2 ∧
      spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] pinSt ms2 ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt ms2 ∧
      UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) ms2.memory wide77
        (WidePtrVal.toValue 8 wide77) xs4 (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) ∧
      PureMirExec.mirStep pinBody ms2 = .cont ms3 ∧
      spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] pinSt ms3 ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt ms3 ∧
      UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) ms3.memory wide77
        (WidePtrVal.toValue 8 wide77) xs4 (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) ∧
      PureMirExec.StepsTo (PureMirExec.mirStep pinBody) pinMs0
        (mirCfgStateRel tagOfLoan (fun _ => [(1, 3, [])]) id pinCfgExtra
          ⟨some, 1, pinSt, 0⟩) ∧
      PureMirExec.mirStep pinBody ms3 = .cont ms4 ∧
      spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] pinSt ms4 ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt ms4 ∧
      UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) ms4.memory wide77
        (WidePtrVal.toValue 8 wide77) xs4 (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE ms4.memory.borrows 77 wide77 xs4
        (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) ∧
      PureMirExec.StepsTo (PureMirExec.mirStep pinBody) ms3
        (mirCfgStateRel tagOfLoan (fun _ => [(1, 3, [])]) id pinCfgExtra
          ⟨some, 2, pinSt, 0⟩) ∧
      PureMirExec.mirStep pinBody ms4 = .cont ms5 ∧
      spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] pinSt ms5 ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt ms5 ∧
      mirStateRel tagOfLoan [(1, 3, [])] pinSt ms5 ∧
      UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) ms5.memory wide77
        (WidePtrVal.toValue 8 wide77) xs4 (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) := by
  obtain ⟨hPin0, hBind0, hRel0⟩ := pinMs0_pinned_and_bound
  have hNeBind : ∀ d, d ≠ 3 → ∀ b, b ∈ [(1, 3, ([] : SubPath))] → b.2.1 ≠ d := by
    intro d hd b hb
    cases hb with
    | head => exact fun h => hd h.symm
    | tail _ h => cases h
  have hUnbPin : ∀ (d : Local) (ls msLs : List LocalSlot), 1 ≠ d → ls[1]? = msLs[1]? →
      ∀ (i : Nat) (c : PlaceCell StdVal),
        pinSt.locals[i]? = some c → getPathPerm [] c.perm = .unborrowed →
        i + 1 ≠ d ∧ ls[i + 1]? = msLs[i + 1]? := by
    intro d ls msLs h1 hSlot i c hc hU
    match i, hc with
    | 0, _ => exact ⟨h1, hSlot⟩
    | 1, hc =>
      injection hc with hc
      subst hc
      exact nomatch hU
    | 2, hc =>
      injection hc with hc
      subst hc
      exact nomatch hU
    | _ + 3, hc => exact nomatch hc
  -- Step 1: `_4 = PtrMetadata(copy _1)` (protector `5` active; no borrow targets `_4`).
  obtain ⟨hS1, hPin1, hBind1, hW1⟩ :=
    mirStep_assign_ptrMetadata_preserves_spatialPin tagOfLoan (body := pinBody) (cur := pinBody)
      (ms := pinMs0) (dstLoc := 4) (locals₁ := pinMs0.frame.locals) (locals₂ := pinLocals1)
      hPin0 hBind0 (by decide) (hNeBind 4 (by decide))
      rfl (Or.inl rfl) rfl rfl (PtrMetadataOf.wide wide77) rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      (hasProtectedWriteConflict_eq_false_of_forall_ne _ _ _ _ _ _ _ _ (by decide))
      rfl rfl rfl
  have ⟨_, hRel1⟩ := mirStateRel_and_spatialPin_of_assign_write tagOfLoan .none 0 hPin0 hRel0
    (l := 2) (dstLoc := 4) (locals₁ := pinMs0.frame.locals) (v := .init (.scalar ⟨4, 8⟩))
    (ms' := { frame := { blockIdx := 0, stmtIdx := 1, locals := pinLocals1 },
              memory := { pinMs0.memory with
                borrows := invalidateConflictingBorrows pinMs0.memory.borrows 4 .none 0 } })
    (by decide) (hNeBind 4 (by decide)) rfl
    (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
    (hUnbPin 4 _ _ (by decide) rfl) rfl rfl rfl
  have hDst1 := pinDst77.of_invalidateConflictingBorrows (dstLoc := 4) .none 0
    (lookupBorrow_targetLocal_ne_of_forall_mem (by decide) _)
  -- Step 2: `_5 = from_raw_parts(copy (_1.0), move _4)`.
  obtain ⟨hS2, hPin2, hBind2, hW2⟩ :=
    mirStep_assign_aggregate_rawPtr_preserves_spatialPin tagOfLoan (body := pinBody)
      (cur := pinBody) (dstLoc := 5) (p := ⟨77, 0⟩) (len := 4) (locals₁ := pinLocals1)
      (locals₂ := pinLocals1Moved) (locals₃ := pinLocals2) hPin1 hBind1 (by decide)
      (hNeBind 5 (by decide))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      rfl rfl rfl rfl
  have ⟨_, hRel2⟩ := mirStateRel_and_spatialPin_of_assign_write tagOfLoan .none 0 hPin1 hRel1
    (l := 2) (dstLoc := 5) (locals₁ := pinLocals1Moved) (v := .init (WidePtrVal.toValue 8 wide77))
    (ms' := { frame := { blockIdx := 0, stmtIdx := 2, locals := pinLocals2 },
              memory := { pinMs0.memory with
                borrows := invalidateConflictingBorrows
                  (invalidateConflictingBorrows pinMs0.memory.borrows 4 .none 0) 5 .none 0 } })
    (by decide) (hNeBind 5 (by decide)) rfl
    (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
    (hUnbPin 5 _ _ (by decide) rfl) rfl rfl rfl
  have hDst2 := hDst1.of_invalidateConflictingBorrows (dstLoc := 5) .none 0
    (lookupBorrow_targetLocal_ne_of_forall_mem (by decide) _)
  -- Step 3: `_6 = size_of_val::<[u32]>(copy _5)`.
  obtain ⟨hS3, hPin3, hBind3, hW3⟩ :=
    mirStep_call_sizeOfVal_slice_preserves_spatialPin tagOfLoan (body := pinBody) (cur := pinBody)
      (dstLoc := 6) (p := ⟨77, 0⟩) (len := 4) (locals' := pinLocals2)
      (updatedLocals := pinLocals3) hPin2 hBind2 (by decide) (hNeBind 6 (by decide))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      rfl rfl rfl (by decide) rfl rfl rfl
  have ⟨_, hRel3⟩ := mirStateRel_and_spatialPin_of_intrinsic_write tagOfLoan hPin2 hRel2
    (l := 2) (dstLoc := 6) (locals' := pinLocals2) (v := .init (.scalar ⟨16, 8⟩))
    (ms' := { frame := { blockIdx := 1, stmtIdx := 0, locals := pinLocals3 },
              memory := invalidateDirectDestWriteBorrows
                { pinMs0.memory with
                  borrows := invalidateConflictingBorrows
                    (invalidateConflictingBorrows pinMs0.memory.borrows 4 .none 0) 5 .none 0 }
                pinLocals2 { local_ := 6, projection := [] } })
    (by decide) (hNeBind 6 (by decide)) rfl
    (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
    (hUnbPin 6 _ _ (by decide) rfl) rfl rfl
  have hDst3 := hDst2.of_invalidateDirectDestWriteBorrows (dstLoc := 6) pinLocals2
    (lookupBorrow_targetLocal_ne_of_forall_mem (by decide) _)
  -- Step 4: `_7 = align_of_val::<[u32]>(move _5)`.
  obtain ⟨hS4, hPin4, hBind4, hW4⟩ :=
    mirStep_call_alignOfVal_slice_preserves_spatialPin tagOfLoan (body := pinBody) (cur := pinBody)
      (dstLoc := 7) (p := ⟨77, 0⟩) (len := 4) (locals' := pinLocals3Moved)
      (updatedLocals := pinLocals4) hPin3 hBind3 (by decide) (hNeBind 7 (by decide))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      rfl rfl rfl rfl (by decide) rfl rfl rfl
  have hLoc4 := mirLocalsRel_of_set?_preserved tagOfLoan hRel3.2
    (locals_in := pinLocals3Moved) (dstLoc := 7) (v := .init (.scalar ⟨4, 8⟩))
    (ms' := { frame := { blockIdx := 2, stmtIdx := 0, locals := pinLocals4 },
              memory := invalidateDirectDestWriteBorrows
                (invalidateDirectDestWriteBorrows
                  { pinMs0.memory with
                    borrows := invalidateConflictingBorrows
                      (invalidateConflictingBorrows pinMs0.memory.borrows 4 .none 0) 5 .none 0 }
                  pinLocals2 { local_ := 6, projection := [] })
                pinLocals3Moved { local_ := 7, projection := [] } })
    rfl (hUnbPin 7 _ _ (by decide) rfl)
  have hDst4 := hDst3.of_invalidateDirectDestWriteBorrows (dstLoc := 7) pinLocals3Moved
    (lookupBorrow_targetLocal_ne_of_forall_mem (by decide) _)
  -- Step 5: `_0 = (move _6, move _7)`.
  obtain ⟨hS5, hPin5, hBind5, hW5⟩ :=
    mirStep_assign_layout_tuple_preserves_spatialPin tagOfLoan (body := pinBody) (cur := pinBody)
      (dstLoc := 0) (vSize := .scalar ⟨16, 8⟩) (vAlign := .scalar ⟨4, 8⟩)
      (locals₁ := pinLocals4Moved6) (locals₂ := pinLocals4Moved) (locals₃ := pinLocals5)
      hPin4 hBind4 (by decide) (hNeBind 0 (by decide))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      rfl rfl rfl rfl
  have hLoc5 := mirLocalsRel_of_set?_preserved tagOfLoan hLoc4
    (locals_in := pinLocals4Moved) (dstLoc := 0)
    (v := .init (.aggregate 0 [.scalar ⟨16, 8⟩, .scalar ⟨4, 8⟩]))
    (ms' := { frame := { blockIdx := 2, stmtIdx := 1, locals := pinLocals5 },
              memory := { (invalidateDirectDestWriteBorrows
                (invalidateDirectDestWriteBorrows
                  { pinMs0.memory with
                    borrows := invalidateConflictingBorrows
                      (invalidateConflictingBorrows pinMs0.memory.borrows 4 .none 0) 5 .none 0 }
                  pinLocals2 { local_ := 6, projection := [] })
                pinLocals3Moved { local_ := 7, projection := [] }) with
                borrows := invalidateConflictingBorrows
                  (invalidateDirectDestWriteBorrows
                    (invalidateDirectDestWriteBorrows
                      { pinMs0.memory with
                        borrows := invalidateConflictingBorrows
                          (invalidateConflictingBorrows pinMs0.memory.borrows 4 .none 0) 5 .none 0 }
                      pinLocals2 { local_ := 6, projection := [] })
                    pinLocals3Moved { local_ := 7, projection := [] }).borrows 0 .none 0 } })
    rfl (hUnbPin 0 _ _ (by decide) rfl)
  have hRel5 : mirStateRel tagOfLoan [(1, 3, [])] pinSt _ := ⟨hBind5, hLoc5⟩
  have hDst5 := hDst4.of_invalidateConflictingBorrows (dstLoc := 0) .none 0
    (lookupBorrow_targetLocal_ne_of_forall_mem (by decide) _)
  -- `MirWpConverges` composed from the five lifted steps and the final `return` (no `wpMirSym`
  -- evaluation by computation over the whole run).
  have hConv : Anneal.MirFuelFree.MirWpConverges pinBody pinMs0
      (fun out =>
        ∃ mem', out = .normal (.aggregate 0 [.scalar ⟨16, 8⟩, .scalar ⟨4, 8⟩], mem')) :=
    hW1 _ (hW2 _ (hW3 _ (hW4 _ (hW5 _
      (Anneal.MirFuelFree.MirWpConverges.ret_of_step rfl ⟨_, rfl⟩)))))
  exact ⟨hConv, _, _, _, _, _,
    hS1, hPin1, hBind1, hDst1,
    hS2, hPin2, hBind2, hDst2,
    hS3, hPin3, hBind3, hDst3,
    mirCfgStateRel_stepsTo_of_steps tagOfLoan (bb := 0) (nextBb := 1)
      (by unfold mirCfgStateRel; exact ⟨subIdWrap_some, rfl, rfl, hRel0, hPin0, pinDst77⟩)
      (.step hS1 (.step hS2 (.step hS3 (.refl rfl)))) rfl rfl hRel3 ⟨hPin3, hDst3⟩,
    hS4, hPin4, hBind4, hDst4, pinMutLens77,
    mirCfgStateRel_stepsTo_of_intrinsic_write tagOfLoan (bb := 1) (nextBb := 2)
      (locals' := pinLocals3Moved) (updatedLocals := pinLocals4) (dstLoc := 7)
      (v := .init (.scalar ⟨4, 8⟩))
      (by unfold mirCfgStateRel; exact ⟨subIdWrap_some, rfl, rfl, hRel3, hPin3, hDst3⟩) hS4 rfl
      (hNeBind 7 (by decide))
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      (hUnbPin 7 _ _ (by decide) rfl) rfl ⟨hPin4, hDst4⟩,
    hS5, hPin5, hBind5, hRel5, hDst5⟩

/-! ## 6. Negative UB-Rejection Canaries & Metadata-Without-Deref Contrast -/

abbrev lenMaxOk : Nat := 2 ^ 61 - 1
abbrev lenOverflow : Nat := 2 ^ 61
abbrev strOverflow : Nat := 2 ^ 63

/-- Exact `isize` (`signedHalfModulus 8 = 2^63`) boundary canaries:
- For `[u32]` (`elemSz = 4`), `len = 2^61 - 1` (`len * 4 = 2^63 - 4 < 2^63`) succeeds with
  `lenMaxOk * 4`, whereas `len = 2^61` (`len * 4 = 2^63 = signedHalfModulus 8`) faults `.ub` in BOTH
  `size_of_val` and `align_of_val`!
- For `str` (`elemSz = 1`), `len = 2^63` faults `.ub` in both `size_of_val` and `align_of_val`.
- Passing a thin pointer `.ptr p9 8` or a 32-bit pointer `ptrSz = 4` for `.slice (.uint .u32)` or
  `.str` faults `.ub`. -/
theorem size_and_align_negative_ub_canaries :
    let bodyU32 := sizeAlignSliceCallerMir (.uint .u32)
    let tgtU32 : ResolvedCallTarget :=
      { defPath := "core::intrinsics::size_of_val", typeArgs := [.slice (.uint .u32)],
        fnSig := none, isIndirect := false }
    let tgtStr : ResolvedCallTarget :=
      { defPath := "core::intrinsics::size_of_val", typeArgs := [.str],
        fnSig := none, isIndirect := false }
    evalSliceSizeOfVal 4 ⟨lenMaxOk, 8⟩ = some ⟨lenMaxOk * 4, 8⟩ ∧
    evalSliceSizeOfVal 4 ⟨lenOverflow, 8⟩ = none ∧
    evalSliceSizeOfVal 4 ⟨4, 4⟩ = none ∧
    evalNonSelectIntrinsicCall .sizeOfVal pinMs0 tgtU32 bodyU32.localDecls bodyU32.layouts []
      [.aggregate 0 [.ptr p9 8, .scalar ⟨lenOverflow, 8⟩]] pinMs0.frame.locals
      { local_ := 2, projection := [] } 1 = MirStepNode.fail .ub ∧
    evalNonSelectIntrinsicCall .alignOfVal pinMs0 tgtU32 bodyU32.localDecls bodyU32.layouts []
      [.aggregate 0 [.ptr p9 8, .scalar ⟨lenOverflow, 8⟩]] pinMs0.frame.locals
      { local_ := 3, projection := [] } 1 = MirStepNode.fail .ub ∧
    evalNonSelectIntrinsicCall .sizeOfVal pinMs0 tgtStr bodyU32.localDecls bodyU32.layouts []
      [.aggregate 0 [.ptr p10 8, .scalar ⟨strOverflow, 8⟩]] pinMs0.frame.locals
      { local_ := 2, projection := [] } 1 = MirStepNode.fail .ub ∧
    evalNonSelectIntrinsicCall .alignOfVal pinMs0 tgtStr bodyU32.localDecls bodyU32.layouts []
      [.aggregate 0 [.ptr p10 8, .scalar ⟨strOverflow, 8⟩]] pinMs0.frame.locals
      { local_ := 3, projection := [] } 1 = MirStepNode.fail .ub ∧
    (evalNonSelectIntrinsicCall .sizeOfVal pinMs0 tgtU32 bodyU32.localDecls bodyU32.layouts []
       [.ptr p9 8] pinMs0.frame.locals { local_ := 2, projection := [] } 1 = MirStepNode.fail .ub ∧
     evalNonSelectIntrinsicCall .alignOfVal pinMs0 tgtU32 bodyU32.localDecls bodyU32.layouts []
       [.ptr p9 8] pinMs0.frame.locals { local_ := 2, projection := [] } 1 = MirStepNode.fail .ub) ∧
    (evalNonSelectIntrinsicCall .sizeOfVal pinMs0 tgtStr bodyU32.localDecls bodyU32.layouts []
       [.ptr p10 8] pinMs0.frame.locals { local_ := 2, projection := [] } 1 = MirStepNode.fail .ub ∧
     evalNonSelectIntrinsicCall .alignOfVal pinMs0 tgtStr bodyU32.localDecls bodyU32.layouts []
       [.ptr p10 8] pinMs0.frame.locals { local_ := 2, projection := [] } 1 = MirStepNode.fail .ub) ∧
    (evalNonSelectIntrinsicCall .sizeOfVal pinMs0 tgtU32 bodyU32.localDecls bodyU32.layouts []
       [.aggregate 0 [.ptr p9 4, .scalar ⟨4, 4⟩]] pinMs0.frame.locals
       { local_ := 2, projection := [] } 1 = MirStepNode.fail .ub ∧
     evalNonSelectIntrinsicCall .alignOfVal pinMs0 tgtU32 bodyU32.localDecls bodyU32.layouts []
       [.aggregate 0 [.ptr p9 4, .scalar ⟨4, 4⟩]] pinMs0.frame.locals
       { local_ := 2, projection := [] } 1 = MirStepNode.fail .ub) := by
  intro bodyU32 tgtU32 tgtStr
  have hThin := evalNonSelectIntrinsicCall_unsized_thinPtr_ub pinMs0 tgtU32
    bodyU32.localDecls bodyU32.layouts [] pinMs0.frame.locals { local_ := 2, projection := [] }
    1 (.uint .u32) p9 8
  have hThinStr := evalNonSelectIntrinsicCall_unsized_thinPtr_ub pinMs0 tgtStr
    bodyU32.localDecls bodyU32.layouts [] pinMs0.frame.locals { local_ := 2, projection := [] }
    1 (.uint .u32) p10 8
  exact ⟨evalSliceSizeOfVal_eq_some 4 lenMaxOk (by decide),
    evalSliceSizeOfVal_eq_none_of_le 4 lenOverflow (by decide) (by decide),
    evalSliceSizeOfVal_eq_none_of_sizeBytes_ne 4 ⟨4, 4⟩ (by decide),
    evalNonSelectIntrinsicCall_sizeOfVal_slice_overflow_ub pinMs0 tgtU32
      bodyU32.localDecls bodyU32.layouts [] pinMs0.frame.locals { local_ := 2, projection := [] }
      1 (.uint .u32) 4 p9 lenOverflow rfl rfl (by decide) (by decide),
    evalNonSelectIntrinsicCall_alignOfVal_slice_overflow_ub pinMs0 tgtU32
      bodyU32.localDecls bodyU32.layouts [] pinMs0.frame.locals { local_ := 3, projection := [] }
      1 (.uint .u32) 4 4 p9 lenOverflow rfl rfl rfl (by decide) (by decide),
    evalNonSelectIntrinsicCall_sizeOfVal_str_overflow_ub pinMs0 tgtStr
      bodyU32.localDecls bodyU32.layouts [] pinMs0.frame.locals { local_ := 2, projection := [] }
      1 p10 strOverflow rfl (by decide) (by decide),
    evalNonSelectIntrinsicCall_alignOfVal_str_overflow_ub pinMs0 tgtStr
      bodyU32.localDecls bodyU32.layouts [] pinMs0.frame.locals { local_ := 3, projection := [] }
      1 p10 strOverflow rfl (by decide) (by decide),
    hThin.1 rfl,
    hThinStr.2 rfl,
    evalNonSelectIntrinsicCall_slice_ptrSz_ne_ub pinMs0 tgtU32
      bodyU32.localDecls bodyU32.layouts [] pinMs0.frame.locals { local_ := 2, projection := [] }
      1 (.uint .u32) p9 4 ⟨4, 4⟩ rfl (by decide)⟩

/-- Negative `UnOp.ptrMetadata` and `AggregateKind.rawPtr` width/kind mismatch canaries. -/
theorem ptrMetadata_and_rawPtr_negative_canaries :
    evalRvalue (dstLocals 4) (.unaryOp .ptrMetadata (.copy { local_ := 1, projection := [] }))
      mem0 dstDecls layouts64 = .ub ∧
    evalRvalue (dstLocals 4) (.unaryOp .ptrMetadata (.copy { local_ := 5, projection := [] }))
      mem0 dstDecls layouts64 = .ub ∧
    evalRvalue (dstLocals 8)
      (.aggregate (.rawPtr { kind := .uint .u32, layoutIdx := 0 } .not)
        [.copy { local_ := 5, projection := [] },
         .copy { local_ := 1, projection := [.field 1 usizeTy] }])
      mem0 dstDecls layouts64 = .ub ∧
    evalRvalue (dstLocals 8)
      (.aggregate (.rawPtr sliceU32Ty .not)
        [.copy { local_ := 5, projection := [] },
         .copy { local_ := 6, projection := [] }])
      mem0 dstDecls layouts64 = .ub ∧
    evalRvalue (dstLocals 4)
      (.aggregate (.rawPtr sliceU32Ty .not)
        [.copy { local_ := 5, projection := [] },
         .copy { local_ := 1, projection := [.field 1 usizeTy] }])
      mem0 dstDecls layouts64 = .ub ∧
    evalRvalue (dstLocals 8) (.aggregate (.rawPtr sliceU32Ty .not) [])
      mem0 dstDecls layouts64 = .unsupported :=
  ⟨evalRvalue_unaryOp_ptrMetadata_wide_width_mismatch_ub (dstLocals 4) (dstLocals 4)
     (.copy { local_ := 1, projection := [] }) mem0 dstDecls layouts64 p9 4 ⟨4, 4⟩ rfl rfl,
   evalRvalue_unaryOp_ptrMetadata_thin_width_mismatch_ub (dstLocals 4) (dstLocals 4)
     (.copy { local_ := 5, projection := [] }) mem0 dstDecls layouts64 p9 4 rfl rfl,
   evalRvalue_aggregate_rawPtr_sized_wideMeta_ub (dstLocals 8) (dstLocals 8) (dstLocals 8)
     { kind := .uint .u32, layoutIdx := 0 } .not
     (.copy { local_ := 5, projection := [] })
     (.copy { local_ := 1, projection := [.field 1 usizeTy] })
     mem0 dstDecls layouts64 p9 8 ⟨4, 8⟩ rfl rfl rfl,
   evalRvalue_aggregate_rawPtr_unsized_unitMeta_ub (dstLocals 8) (dstLocals 8) (dstLocals 8)
     sliceU32Ty .not
     (.copy { local_ := 5, projection := [] })
     (.copy { local_ := 6, projection := [] })
     mem0 dstDecls layouts64 p9 8 rfl rfl rfl,
   evalRvalue_aggregate_rawPtr_wide_width_mismatch_ub (dstLocals 4) (dstLocals 4) (dstLocals 4)
     sliceU32Ty .not
     (.copy { local_ := 5, projection := [] })
     (.copy { local_ := 1, projection := [.field 1 usizeTy] })
     mem0 dstDecls layouts64 p9 4 ⟨4, 4⟩ rfl rfl rfl rfl,
   evalRvalue_aggregate_rawPtr_nil_unsupported (dstLocals 8) sliceU32Ty .not
     mem0 dstDecls layouts64⟩

/-- **Metadata-without-deref OOB contrast**:
A wide raw pointer `*const [u32]` with out-of-bounds length `5` (`5 * 4 = 20 > 16` bytes on the
16-byte global `arrAlloc16`) faults with `.ub` when dereferenced by `Rvalue.len (*_1)`, yet
`UnOp.ptrMetadata(_1)` and `size_of_val_raw(_1)` (`5 * 4 = 20 < 2^63`) succeed without
dereferencing memory! -/
theorem metadata_without_deref_oob_contrast :
    let wideOob5 : WidePtrVal := WidePtrVal.mk p9 5
    let localsOob : List LocalSlot := (dstLocals 8).set 1 (.init (WidePtrVal.toValue 8 wideOob5))
    let bodyU32 := sizeAlignSliceCallerMir (.uint .u32)
    let tgtU32 : ResolvedCallTarget :=
      { defPath := "core::intrinsics::size_of_val", typeArgs := [.slice (.uint .u32)],
        fnSig := none, isIndirect := false }
    evalRvalue localsOob (.len { local_ := 1, projection := [.deref] })
      mem0 dstDecls layouts64 = .ub ∧
    evalRvalue localsOob (.unaryOp .ptrMetadata (.copy { local_ := 1, projection := [] }))
      mem0 dstDecls layouts64 = .ok (.scalar ⟨5, 8⟩) localsOob mem0 ∧
    evalNonSelectIntrinsicCall .sizeOfVal pinMs0 tgtU32 bodyU32.localDecls bodyU32.layouts []
      [WidePtrVal.toValue 8 wideOob5] localsOob { local_ := 2, projection := [] } 1 =
      writeIntrinsicReturn pinMs0 localsOob { local_ := 2, projection := [] } 1
        (.scalar ⟨20, 8⟩) := by
  intro wideOob5 localsOob bodyU32 tgtU32
  obtain ⟨hLenUb, hMetaOk⟩ :=
    WidePtrVal.evalRvalue_len_oob_global_ub_and_ptrMetadata_ok localsOob localsOob
      { local_ := 1, projection := [.deref] } (.copy { local_ := 1, projection := [] })
      mem0 dstDecls layouts64 [] (.uint .u32) 0 arrAlloc16 4 wideOob5
      rfl rfl rfl rfl rfl rfl rfl (by decide)
  exact ⟨hLenUb, hMetaOk,
    evalNonSelectIntrinsicCall_sizeOfVal_slice pinMs0 _ _ _ [] _
      { local_ := 2, projection := [] } 1 (.uint .u32) 4 p9 5 rfl rfl (by decide)⟩

/-- A `sizeAlignSliceCallerMir` state at block `bb` with `_1 := v` over `mem0`. -/
def ubState (v : Value) (bb : Nat) : MachineState :=
  { frame := { blockIdx := bb, stmtIdx := 0, locals := [.uninit, .init v, .uninit, .uninit] }
    memory := mem0 }

/-- **`stepMirFn`-level exact `isize` boundary** on the live `[u32]` and `str` caller bodies:
`size_of_val` with `len = 2^61 - 1` steps to `bb1` writing `(2^61 - 1) * 4 = 2^63 - 4`, while
`len = 2^61` (`len * 4 = 2^63 = signedHalfModulus 8`) on `[u32]`, `len = 2^63` on `str`, a thin
pointer passed for `[u32]` or `str`, and a 32-bit pointer `ptrSz = 4` on 64-bit all fault
`MirStepNode.fail .ub` (`mirStep` `.fault`) for both `size_of_val` and `align_of_val`. -/
theorem size_and_align_stepMirFn_boundary_canaries :
    let bodyU32 := sizeAlignSliceCallerMir (.uint .u32)
    let bodyStr := sizeAlignStrCallerMir
    let okLocals : List LocalSlot :=
      [.uninit, .init (.aggregate 0 [.ptr p9 8, .scalar ⟨lenMaxOk, 8⟩]),
       .init (.scalar ⟨lenMaxOk * 4, 8⟩), .uninit]
    (∃ s', PureMirExec.mirStep bodyU32
        (ubState (.aggregate 0 [.ptr p9 8, .scalar ⟨lenMaxOk, 8⟩]) 0) = .cont s' ∧
      s'.frame.locals = okLocals ∧ s'.frame.blockIdx = 1) ∧
    (stepMirFn bodyU32 (ubState (.aggregate 0 [.ptr p9 8, .scalar ⟨lenOverflow, 8⟩]) 0) =
        MirStepNode.fail .ub ∧
      PureMirExec.mirStep bodyU32
        (ubState (.aggregate 0 [.ptr p9 8, .scalar ⟨lenOverflow, 8⟩]) 0) = .fault) ∧
    (stepMirFn bodyU32 (ubState (.aggregate 0 [.ptr p9 8, .scalar ⟨lenOverflow, 8⟩]) 1) =
        MirStepNode.fail .ub ∧
      PureMirExec.mirStep bodyU32
        (ubState (.aggregate 0 [.ptr p9 8, .scalar ⟨lenOverflow, 8⟩]) 1) = .fault) ∧
    (stepMirFn bodyStr (ubState (.aggregate 0 [.ptr p10 8, .scalar ⟨strOverflow, 8⟩]) 0) =
        MirStepNode.fail .ub ∧
      PureMirExec.mirStep bodyStr
        (ubState (.aggregate 0 [.ptr p10 8, .scalar ⟨strOverflow, 8⟩]) 0) = .fault) ∧
    (stepMirFn bodyStr (ubState (.aggregate 0 [.ptr p10 8, .scalar ⟨strOverflow, 8⟩]) 1) =
        MirStepNode.fail .ub ∧
      PureMirExec.mirStep bodyStr
        (ubState (.aggregate 0 [.ptr p10 8, .scalar ⟨strOverflow, 8⟩]) 1) = .fault) ∧
    (stepMirFn bodyU32 (ubState (.ptr p9 8) 0) = MirStepNode.fail .ub ∧
      PureMirExec.mirStep bodyU32 (ubState (.ptr p9 8) 0) = .fault) ∧
    (stepMirFn bodyU32 (ubState (.ptr p9 8) 1) = MirStepNode.fail .ub ∧
      PureMirExec.mirStep bodyU32 (ubState (.ptr p9 8) 1) = .fault) ∧
    (stepMirFn bodyU32 (ubState (.aggregate 0 [.ptr p9 4, .scalar ⟨4, 4⟩]) 0) =
        MirStepNode.fail .ub ∧
      PureMirExec.mirStep bodyU32 (ubState (.aggregate 0 [.ptr p9 4, .scalar ⟨4, 4⟩]) 0) =
        .fault) ∧
    (stepMirFn bodyU32 (ubState (.aggregate 0 [.ptr p9 4, .scalar ⟨4, 4⟩]) 1) =
        MirStepNode.fail .ub ∧
      PureMirExec.mirStep bodyU32 (ubState (.aggregate 0 [.ptr p9 4, .scalar ⟨4, 4⟩]) 1) =
        .fault) := by
  intro bodyU32 bodyStr okLocals
  obtain ⟨_, hOk, _, _⟩ := mirStep_call_sizeOfVal_slice (body := bodyU32) (cur := bodyU32)
    (s := ubState (.aggregate 0 [.ptr p9 8, .scalar ⟨lenMaxOk, 8⟩]) 0)
    (p := p9) (len := lenMaxOk)
    (locals' := (ubState (.aggregate 0 [.ptr p9 8, .scalar ⟨lenMaxOk, 8⟩]) 0).frame.locals)
    (updatedLocals := okLocals)
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  exact ⟨⟨_, hOk, rfl, rfl⟩,
    mirStep_call_sizeOfVal_slice_overflow_ub (body := bodyU32) (cur := bodyU32)
      (s := ubState (.aggregate 0 [.ptr p9 8, .scalar ⟨lenOverflow, 8⟩]) 0)
      (p := p9) (len := lenOverflow)
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide),
    mirStep_call_alignOfVal_slice_overflow_ub (body := bodyU32) (cur := bodyU32)
      (s := ubState (.aggregate 0 [.ptr p9 8, .scalar ⟨lenOverflow, 8⟩]) 1)
      (p := p9) (len := lenOverflow)
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide),
    mirStep_call_sizeOfVal_str_overflow_ub (body := bodyStr) (cur := bodyStr)
      (s := ubState (.aggregate 0 [.ptr p10 8, .scalar ⟨strOverflow, 8⟩]) 0)
      (p := p10) (len := strOverflow)
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide),
    mirStep_call_alignOfVal_str_overflow_ub (body := bodyStr) (cur := bodyStr)
      (s := ubState (.aggregate 0 [.ptr p10 8, .scalar ⟨strOverflow, 8⟩]) 1)
      (p := p10) (len := strOverflow)
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide),
    mirStep_call_sizeOfVal_unsized_thinPtr_ub (body := bodyU32) (cur := bodyU32)
      (s := ubState (.ptr p9 8) 0) (dstTy := .slice (.uint .u32)) (p := p9) (ptrSz := 8)
      (Or.inl ⟨_, rfl⟩) rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl,
    mirStep_call_alignOfVal_unsized_thinPtr_ub (body := bodyU32) (cur := bodyU32)
      (s := ubState (.ptr p9 8) 1) (dstTy := .slice (.uint .u32)) (p := p9) (ptrSz := 8)
      (Or.inl ⟨_, rfl⟩) rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl,
    mirStep_call_sizeOfVal_slice_ptrSz_ne_ub (body := bodyU32) (cur := bodyU32)
      (s := ubState (.aggregate 0 [.ptr p9 4, .scalar ⟨4, 4⟩]) 0) (elemTy := .uint .u32)
      (p := p9) (ptrSz := 4) (lenSc := ⟨4, 4⟩)
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl (by decide),
    mirStep_call_alignOfVal_slice_ptrSz_ne_ub (body := bodyU32) (cur := bodyU32)
      (s := ubState (.aggregate 0 [.ptr p9 4, .scalar ⟨4, 4⟩]) 1) (elemTy := .uint .u32)
      (p := p9) (ptrSz := 4) (lenSc := ⟨4, 4⟩)
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl (by decide)⟩

/-- **Provenance-free (dangling) wide and thin pointers, `.aggregate 0 []` unit metadata, and
remaining fail-closed shapes**:
- `ptr::slice_from_raw_parts(ptr::without_provenance(4), 0)` (`AggregateKind.rawPtr` from an
  integer address) builds the provenance-free empty slice `.aggregate 0 [.scalar ⟨4, 8⟩,
  .scalar ⟨0, 8⟩]`, `to_raw_parts` + `from_raw_parts` round-trips it identically, and
  `UnOp.ptrMetadata` reads its length `0` without touching memory;
- `AggregateKind.rawPtr` on sized `u32` accepts both `.unit` and `.aggregate 0 []` (`Tuple([])`)
  metadata for both provenance-carrying `.ptr p9 8` and provenance-free `.scalar ⟨4, 8⟩` data
  pointers, and `UnOp.ptrMetadata` on `.scalar ⟨4, 8⟩` returns `.unit` when typed as `*const u32`
  while faulting `.ub` when typed as `*const [u32]`;
- Stage-1 conservative divergence: the trusted `size_of_val::<[u32]>` and
  `align_of_val::<[u32]>` fault `.ub` on a provenance-free wide pointer at
  `stepMirFn` level because Stage-1 requires a provenance-carrying `.ptr _ 8`
  data pointer even when `len = 0` (whereas Rust/Miri/MiniRust allow aligned
  provenance-free zero-byte layout queries);
- `from_raw_parts::<[u32]>` with vtable-pointer metadata fails closed with `.ub`;
- a 32-bit (`ptrSz = 4`) data pointer in a `&str` faults `.ub` for both `size_of_val` and
  `align_of_val` at `stepMirFn` level. -/
theorem provenanceFree_and_failClosed_canaries :
    let bodyU32 := sizeAlignSliceCallerMir (.uint .u32)
    let bodyStr := sizeAlignStrCallerMir
    let addrLocals : List LocalSlot :=
      [.init (.scalar ⟨4, 8⟩), .init (.scalar ⟨0, 8⟩), .init (.aggregate 0 []), .init (.ptr p9 8)]
    let danglingVal : Value := .aggregate 0 [.scalar ⟨4, 8⟩, .scalar ⟨0, 8⟩]
    let danglingLocals : List LocalSlot := (dstLocals 8).set 1 (.init danglingVal)
    let scalarAsWideLocals : List LocalSlot := (dstLocals 8).set 1 (.init (.scalar ⟨4, 8⟩))
    let scalarAsThinLocals : List LocalSlot := (dstLocals 8).set 5 (.init (.scalar ⟨4, 8⟩))
    let str32 : Value := .aggregate 0 [.ptr p10 4, .scalar ⟨5, 4⟩]
    evalRvalue addrLocals
        (.aggregate (.rawPtr sliceU32Ty .not)
          [.copy { local_ := 0, projection := [] }, .copy { local_ := 1, projection := [] }])
        mem0 [] layouts64 = .ok danglingVal addrLocals mem0 ∧
    evalRvalue danglingLocals
        (.aggregate (.rawPtr sliceU32Ty .not)
          [.copy { local_ := 1, projection := [.field 0 ptrU32Ty] },
           .copy { local_ := 1, projection := [.field 1 usizeTy] }])
        mem0 dstDecls layouts64 = .ok danglingVal danglingLocals mem0 ∧
    evalRvalue danglingLocals (.unaryOp .ptrMetadata (.copy { local_ := 1, projection := [] }))
        mem0 dstDecls layouts64 = .ok (.scalar ⟨0, 8⟩) danglingLocals mem0 ∧
    evalRvalue addrLocals
        (.aggregate (.rawPtr { kind := .uint .u32, layoutIdx := 0 } .not)
          [.copy { local_ := 3, projection := [] }, .copy { local_ := 2, projection := [] }])
        mem0 [] layouts64 = .ok (.ptr p9 8) addrLocals mem0 ∧
    evalRvalue addrLocals
        (.aggregate (.rawPtr { kind := .uint .u32, layoutIdx := 0 } .not)
          [.copy { local_ := 0, projection := [] }, .copy { local_ := 2, projection := [] }])
        mem0 [] layouts64 = .ok (.scalar ⟨4, 8⟩) addrLocals mem0 ∧
    evalRvalue scalarAsThinLocals (.unaryOp .ptrMetadata (.copy { local_ := 5, projection := [] }))
        mem0 dstDecls layouts64 = .ok .unit scalarAsThinLocals mem0 ∧
    evalRvalue scalarAsWideLocals (.unaryOp .ptrMetadata (.copy { local_ := 1, projection := [] }))
        mem0 dstDecls layouts64 = .ub ∧
    (stepMirFn bodyU32 (ubState danglingVal 0) = MirStepNode.fail .ub ∧
      PureMirExec.mirStep bodyU32 (ubState danglingVal 0) = .fault) ∧
    (stepMirFn bodyU32 (ubState danglingVal 1) = MirStepNode.fail .ub ∧
      PureMirExec.mirStep bodyU32 (ubState danglingVal 1) = .fault) ∧
    evalRvalue (dstLocals 8)
        (.aggregate (.rawPtr sliceU32Ty .not)
          [.copy { local_ := 5, projection := [] }, .copy { local_ := 5, projection := [] }])
        mem0 dstDecls layouts64 = .ub ∧
    (stepMirFn bodyStr (ubState str32 0) = MirStepNode.fail .ub ∧
      PureMirExec.mirStep bodyStr (ubState str32 0) = .fault) ∧
    (stepMirFn bodyStr (ubState str32 1) = MirStepNode.fail .ub ∧
      PureMirExec.mirStep bodyStr (ubState str32 1) = .fault) := by
  intro bodyU32 bodyStr addrLocals danglingVal danglingLocals scalarAsWideLocals scalarAsThinLocals
    str32
  exact ⟨evalRvalue_aggregate_rawPtr_wide_scalarAddr_of_lt addrLocals addrLocals addrLocals
      sliceU32Ty .not (.copy { local_ := 0, projection := [] })
      (.copy { local_ := 1, projection := [] }) mem0 [] layouts64 4 0 rfl (by decide) (by decide)
      rfl rfl,
    evalRvalue_aggregate_rawPtr_to_raw_parts_roundtrip_scalarAddr danglingLocals 1 sliceU32Ty
      ptrU32Ty usizeTy .not mem0 dstDecls layouts64 4 0 rfl (by decide) (by decide) rfl rfl rfl,
    evalRvalue_unaryOp_ptrMetadata_wide_scalarAddr_of_lt danglingLocals danglingLocals
      (.copy { local_ := 1, projection := [] }) mem0 dstDecls layouts64 4 0 rfl (by decide) rfl,
    evalRvalue_aggregate_rawPtr_thin_of_isThinMeta addrLocals addrLocals addrLocals
      { kind := .uint .u32, layoutIdx := 0 } .not (.copy { local_ := 3, projection := [] })
      (.copy { local_ := 2, projection := [] }) mem0 [] layouts64 p9 (.aggregate 0 []) rfl
      (Or.inr rfl) rfl rfl,
    evalRvalue_aggregate_rawPtr_thin_scalarAddr addrLocals addrLocals addrLocals
      { kind := .uint .u32, layoutIdx := 0 } .not (.copy { local_ := 0, projection := [] })
      (.copy { local_ := 2, projection := [] }) mem0 [] layouts64 4 (.aggregate 0 []) rfl
      (by decide) (Or.inr rfl) rfl rfl,
    evalRvalue_unaryOp_ptrMetadata_thin_scalarAddr scalarAsThinLocals scalarAsThinLocals
      (.copy { local_ := 5, projection := [] }) mem0 dstDecls layouts64 4 rfl rfl,
    evalRvalue_unaryOp_ptrMetadata_scalar_wideTy_ub scalarAsWideLocals scalarAsWideLocals
      (.copy { local_ := 1, projection := [] }) mem0 dstDecls layouts64 ⟨4, 8⟩ rfl rfl,
    mirStep_call_sizeOfVal_unsized_scalarAddr_ub (body := bodyU32) (cur := bodyU32)
      (s := ubState danglingVal 0) (dstTy := .slice (.uint .u32)) (addrSc := ⟨4, 8⟩)
      (lenSc := ⟨0, 8⟩) (Or.inl ⟨_, rfl⟩) rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl,
    mirStep_call_alignOfVal_unsized_scalarAddr_ub (body := bodyU32) (cur := bodyU32)
      (s := ubState danglingVal 1) (dstTy := .slice (.uint .u32)) (addrSc := ⟨4, 8⟩)
      (lenSc := ⟨0, 8⟩) (Or.inl ⟨_, rfl⟩) rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl,
    evalRvalue_aggregate_rawPtr_wide_vtableMeta_ub (dstLocals 8) (dstLocals 8) (dstLocals 8)
      sliceU32Ty .not (.copy { local_ := 5, projection := [] })
      (.copy { local_ := 5, projection := [] }) mem0 dstDecls layouts64 p9 p9 8 8 rfl rfl rfl,
    mirStep_call_sizeOfVal_str_ptrSz_ne_ub (body := bodyStr) (cur := bodyStr)
      (s := ubState str32 0) (p := p10) (ptrSz := 4) (lenSc := ⟨5, 4⟩)
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl (by decide),
    mirStep_call_alignOfVal_str_ptrSz_ne_ub (body := bodyStr) (cur := bodyStr)
      (s := ubState str32 1) (p := p10) (ptrSz := 4) (lenSc := ⟨5, 4⟩)
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl (by decide)⟩

/-- **Bounded symbolic `wpMirExecSym` composes with the lifters**: the `size_of_val::<[u32]>` step
of the live caller body shifts `wpMirExecSym` fuel by exactly one. -/
theorem sizeOfVal_step_shifts_wpMirExecSym_fuel :
    let bodyU32 := sizeAlignSliceCallerMir (.uint .u32)
    let s0 := ubState (WidePtrVal.toValue 8 wide4) 0
    let s1 : MachineState :=
      { frame := { blockIdx := 1, stmtIdx := 0,
                   locals := [.uninit, .init (WidePtrVal.toValue 8 wide4),
                              .init (.scalar ⟨16, 8⟩), .uninit] }
        memory := mem0 }
    ∀ fuel post,
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym (fuel + 1) bodyU32 (.running s0) post ↔
        Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel bodyU32 (.running s1) post := by
  intro bodyU32 s0 s1
  obtain ⟨hStep, _, _, _⟩ := mirStep_call_sizeOfVal_slice (body := bodyU32) (cur := bodyU32)
    (s := s0) (p := p9) (len := 4) (locals' := s0.frame.locals)
    (updatedLocals := s1.frame.locals)
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  exact (mirWpConverges_of_stepMirFn_step hStep).2

/-! ## 7. Sized `size_of_val` / `align_of_val` Lifters, Protectors, and `str` Spatial Pins -/

/-- `size_of_val::<u32>(copy _1)` (explicit `typeArgs`) and `align_of_val(copy _1)` (`operandTy`
fallback on `*const u32`) on a thin pointer, then `_4 = PtrMetadata(copy _1)` (`.unit`),
`_1 = from_raw_parts::<u32>(copy _1, move _4)`, and `_0 = (copy _2, copy _3)`. -/
def sizedCallerMir : CapturedMir :=
  { (Anneal.MirLoops.mkMirBody "test::size_align_sized" 1
      [{ mutability := .mut, ty := { kind := .tuple [.uint .usize, .uint .usize], layoutIdx := 1 },
         debugName := some "_0" },
       { mutability := .mut, ty := ptrU32Ty, debugName := some "p" },
       { mutability := .mut, ty := usizeTy, debugName := some "sz" },
       { mutability := .mut, ty := usizeTy, debugName := some "al" },
       { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 },
         debugName := some "thin_meta" },
       { mutability := .mut, ty := pinArrTy, debugName := some "pinned_arr" },
       { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 0 },
         debugName := some "bound_u32" }]
      [{ statements := []
         terminator :=
           { kind := .call (sizeOfValFn [.uint .u32])
               [.copy { local_ := 1, projection := [] }]
               { local_ := 2, projection := [] } (some 1) .continue_
             span := "call_size_of_val_sized" }
         isCleanup := false },
       { statements := []
         terminator :=
           { kind := .call (alignOfValFn [])
               [.copy { local_ := 1, projection := [] }]
               { local_ := 3, projection := [] } (some 2) .continue_
             span := "call_align_of_val_sized_fallback" }
         isCleanup := false },
       retBlock
         [{ kind := .assign { local_ := 4, projection := [] }
              (.unaryOp .ptrMetadata (.copy { local_ := 1, projection := [] }))
            span := "stmt_thin_ptr_metadata" },
          { kind := .assign { local_ := 1, projection := [] }
              (.aggregate (.rawPtr { kind := .uint .u32, layoutIdx := 0 } .not)
                [.copy { local_ := 1, projection := [] },
                 .move { local_ := 4, projection := [] }])
            span := "stmt_thin_from_raw_parts" },
          { kind := .assign { local_ := 0, projection := [] }
              (.aggregate .tuple
                [.copy { local_ := 2, projection := [] },
                 .copy { local_ := 3, projection := [] }])
            span := "mk_layout_tuple" }]]) with
    layouts := layouts64 }

def sizedPinBorrows : List BorrowEntry :=
  [{ tag := 77, targetLocal := 5, targetProjection := [], perm := .unique,
     rangeOffset := 0, rangeLen := 16 },
   { tag := 78, targetLocal := 6, targetProjection := [], perm := .unique,
     rangeOffset := 0, rangeLen := 4 }]

/-- Sized `size_of_val::<u32>` (`4`), `align_of_val::<u32>` (`4`), `mirStep_assign_ptrMetadata_thin`
(`.unit`), and `mirStep_assign_aggregate_rawPtr_thin` one-step lifters, plus their `PureLift`
spatial-pin preserving counterparts (`mirStep_call_sizeOfVal_sized_preserves_spatialPin`,
`mirStep_call_alignOfVal_sized_preserves_spatialPin`, and
`mirStep_assign_aggregate_rawPtr_thin_preserves_spatialPin`). -/
theorem size_and_align_sized_lifters :
    let m0 : Memory := { mem0 with borrows := sizedPinBorrows }
    let s0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0,
                   locals := [.uninit, .init (.ptr p9 8), .uninit, .uninit, .uninit,
                              .init pinArrVal, .init (.scalar ⟨99, 4⟩)] }
        memory := m0 }
    let s1 : MachineState :=
      { frame := { blockIdx := 1, stmtIdx := 0,
                   locals := [.uninit, .init (.ptr p9 8), .init (.scalar ⟨4, 8⟩), .uninit, .uninit,
                              .init pinArrVal, .init (.scalar ⟨99, 4⟩)] }
        memory := m0 }
    let s2 : MachineState :=
      { frame := { blockIdx := 2, stmtIdx := 0,
                   locals := [.uninit, .init (.ptr p9 8), .init (.scalar ⟨4, 8⟩),
                              .init (.scalar ⟨4, 8⟩), .uninit,
                              .init pinArrVal, .init (.scalar ⟨99, 4⟩)] }
        memory := m0 }
    let s3 : MachineState :=
      { frame := { blockIdx := 2, stmtIdx := 1,
                   locals := [.uninit, .init (.ptr p9 8), .init (.scalar ⟨4, 8⟩),
                              .init (.scalar ⟨4, 8⟩), .init .unit,
                              .init pinArrVal, .init (.scalar ⟨99, 4⟩)] }
        memory := m0 }
    let s4 : MachineState :=
      { frame := { blockIdx := 2, stmtIdx := 2,
                   locals := [.uninit, .init (.ptr p9 8), .init (.scalar ⟨4, 8⟩),
                              .init (.scalar ⟨4, 8⟩), .uninit,
                              .init pinArrVal, .init (.scalar ⟨99, 4⟩)] }
        memory := m0 }
    PureMirExec.mirStep sizedCallerMir s0 = .cont s1 ∧
    PureMirExec.mirStep sizedCallerMir s1 = .cont s2 ∧
    PureMirExec.mirStep sizedCallerMir s2 = .cont s3 ∧
    PureMirExec.mirStep sizedCallerMir s3 = .cont s4 ∧
    spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 5 [] pinSt s4 ∧
    spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 6, [])] pinSt s4 := by
  intro m0 s0 s1 s2 s3 s4
  have hPin0 : spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 5 [] pinSt s0 :=
    ⟨_, _, [], _, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      ⟨_, rfl, rfl, rfl, rfl⟩⟩
  have hBind0 : spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 6, [])] pinSt s0 :=
    ⟨⟨trivial, trivial⟩,
      ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩
  have hNeBind : ∀ d, d ≠ 6 → ∀ b, b ∈ [(1, 6, ([] : SubPath))] → b.2.1 ≠ d := by
    intro d hd b hb
    cases hb with
    | head => exact fun h => hd h.symm
    | tail _ h => cases h
  obtain ⟨_, h1, _, _⟩ := mirStep_call_sizeOfVal_sized (body := sizedCallerMir)
    (cur := sizedCallerMir) (s := s0) (p := p9) (locals' := s0.frame.locals)
    (updatedLocals := s1.frame.locals)
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  obtain ⟨_, hPin1, hBind1, _⟩ :=
    mirStep_call_sizeOfVal_sized_preserves_spatialPin tagOfLoan (body := sizedCallerMir)
      (cur := sizedCallerMir) (ms := s0) (dstLoc := 2) (p := p9)
      (locals' := s0.frame.locals) (updatedLocals := s1.frame.locals)
      hPin0 hBind0 (by decide) (hNeBind 2 (by decide))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  obtain ⟨_, h2, _, _⟩ := mirStep_call_alignOfVal_sized (body := sizedCallerMir)
    (cur := sizedCallerMir) (s := s1) (p := p9) (locals' := s1.frame.locals)
    (updatedLocals := s2.frame.locals)
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨_, hPin2, hBind2, _⟩ :=
    mirStep_call_alignOfVal_sized_preserves_spatialPin tagOfLoan (body := sizedCallerMir)
      (cur := sizedCallerMir) (dstLoc := 3) (p := p9)
      (locals' := s1.frame.locals) (updatedLocals := s2.frame.locals)
      hPin1 hBind1 (by decide) (hNeBind 3 (by decide))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨_, h3, _, _⟩ := mirStep_assign_ptrMetadata_thin (body := sizedCallerMir)
    (cur := sizedCallerMir) (s := s2) (p := p9) (locals₁ := s2.frame.locals)
    (locals₂ := s3.frame.locals)
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨_, hPin3, hBind3, _⟩ :=
    mirStep_assign_ptrMetadata_preserves_spatialPin tagOfLoan (body := sizedCallerMir)
      (cur := sizedCallerMir) (dstLoc := 4) (locals₁ := s2.frame.locals)
      (locals₂ := s3.frame.locals) hPin2 hBind2 (by decide) (hNeBind 4 (by decide))
      rfl (Or.inl rfl) rfl rfl (PtrMetadataOf.thin p9) rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      rfl rfl rfl rfl
  obtain ⟨_, h4, _, _⟩ := mirStep_assign_aggregate_rawPtr_thin (body := sizedCallerMir)
    (cur := sizedCallerMir) (s := s3) (p := p9) (locals₁ := s3.frame.locals)
    (locals₂ := s2.frame.locals) (locals₃ := s4.frame.locals)
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨_, hPin4, hBind4, _⟩ :=
    mirStep_assign_aggregate_rawPtr_thin_preserves_spatialPin tagOfLoan (body := sizedCallerMir)
      (cur := sizedCallerMir) (dstLoc := 1) (p := p9) (locals₁ := s3.frame.locals)
      (locals₂ := s2.frame.locals) (locals₃ := s4.frame.locals)
      hPin3 hBind3 (by decide) (hNeBind 1 (by decide))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      rfl rfl rfl rfl
  exact ⟨h1, h2, h3, h4, hPin4, hBind4⟩

/-- Callee memory in which the borrow `77` of `_2` is protected by the active protector `5`. -/
def protMem : Memory :=
  { borrows := [{ tag := 77, targetLocal := 2, targetProjection := [], perm := .unique,
                  rangeOffset := 0, rangeLen := 16, protector := some 5 }]
    activeProtectors := [5] }

/-- **Protector side condition is exact**: with the borrow `77` of `_2` protected by the active
protector `5`, `_4 = PtrMetadata(copy _1)` steps (no borrow targets the fresh temporary `_4`),
whereas a write to the protected array `_2` itself is a protected write conflict. -/
theorem ptrMetadata_step_under_active_protector :
    (∃ s', PureMirExec.mirStep pinBody { pinMs0 with memory := protMem } = .cont s') ∧
    hasProtectedWriteConflict protMem.borrows protMem.activeProtectors 2 .none .nil 0 0 0 =
      true := by
  obtain ⟨_, hMir, _, _⟩ := mirStep_assign_ptrMetadata_wide (body := pinBody) (cur := pinBody)
    (s := { pinMs0 with memory := protMem }) (p := ⟨77, 0⟩) (len := 4)
    (locals₁ := pinMs0.frame.locals)
    (locals₂ := pinLocals1)
    rfl (Or.inl rfl) rfl rfl rfl
    (hasProtectedWriteConflict_eq_false_of_forall_ne _ _ _ _ _ _ _ _ (by decide)) rfl rfl rfl
  exact ⟨⟨_, hMir⟩, rfl⟩

/-- `size_of_val::<str>(copy _1)` and `align_of_val(move _1)` (`operandTy` fallback on `&str`)
inside the protected callee with the pinned array `_2` and bound `_3`. -/
def pinStrBody : CapturedMir :=
  { (Anneal.MirLoops.mkMirBody "test::str_layout_with_pinned_array" 1
      [{ mutability := .mut, ty := { kind := .tuple [.uint .usize, .uint .usize], layoutIdx := 1 },
         debugName := some "_0" },
       { mutability := .not, ty := { kind := .ref .not .str, layoutIdx := 1 },
         debugName := some "s" },
       { mutability := .mut, ty := pinArrTy, debugName := some "pinned_arr" },
       { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 0 },
         debugName := some "bound_u32" },
       { mutability := .mut, ty := usizeTy, debugName := some "sz" },
       { mutability := .mut, ty := usizeTy, debugName := some "al" }]
      [{ statements := []
         terminator :=
           { kind := .call (sizeOfValFn [.str])
               [.copy { local_ := 1, projection := [] }]
               { local_ := 4, projection := [] } (some 1) .continue_
             span := "call_size_of_val_str" }
         isCleanup := false },
       { statements := []
         terminator :=
           { kind := .call (alignOfValFn [])
               [.move { local_ := 1, projection := [] }]
               { local_ := 5, projection := [] } (some 2) .continue_
             span := "call_align_of_val_str" }
         isCleanup := false },
       retBlock
         [{ kind := .assign { local_ := 0, projection := [] }
              (.aggregate .tuple
                [.copy { local_ := 4, projection := [] },
                 .copy { local_ := 5, projection := [] }])
            span := "mk_layout_tuple" }]]) with
    layouts := layouts64 }

def pinStrMs0 : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0,
        locals :=
          [.uninit, .init (WidePtrVal.toValue 8 wideStr5), .init pinArrVal,
           .init (.scalar ⟨99, 4⟩), .uninit, .uninit] }
    memory := { mem0 with borrows := pinBorrows, activeProtectors := [5] } }

def pinStrLocals1 : List LocalSlot :=
  [.uninit, .init (WidePtrVal.toValue 8 wideStr5), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
   .init (.scalar ⟨5, 8⟩), .uninit]

def pinStrLocals1Moved : List LocalSlot :=
  [.uninit, .uninit, .init pinArrVal, .init (.scalar ⟨99, 4⟩), .init (.scalar ⟨5, 8⟩), .uninit]

def pinStrLocals2 : List LocalSlot :=
  [.uninit, .uninit, .init pinArrVal, .init (.scalar ⟨99, 4⟩), .init (.scalar ⟨5, 8⟩),
   .init (.scalar ⟨1, 8⟩)]

/-- **`str` dynamic layout queries preserve the spatial pin and the global-backed `str` lens**:
`size_of_val::<str>` (`5`) and `align_of_val::<str>` (`1`, with a `move` argument) step while the
pinned array `_2`, the loan binding on `_3`, and `UnsizedStrDstAt` over the captured global
`"hello"` all stay intact. -/
theorem str_size_align_preserving_spatialPin :
    ∃ ms1 ms2,
      PureMirExec.mirStep pinStrBody pinStrMs0 = .cont ms1 ∧
      spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] pinSt ms1 ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt ms1 ∧
      UnsizedStrDstAt 8 ms1.memory wideStr5 (WidePtrVal.toValue 8 wideStr5) helloBytes
        bytesStr5 ∧
      PureMirExec.mirStep pinStrBody ms1 = .cont ms2 ∧
      spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] pinSt ms2 ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt ms2 ∧
      UnsizedStrDstAt 8 ms2.memory wideStr5 (WidePtrVal.toValue 8 wideStr5) helloBytes
        bytesStr5 := by
  have hPin0 :
      spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] pinSt pinStrMs0 :=
    ⟨_, _, [], _, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      ⟨_, rfl, rfl, rfl, rfl⟩⟩
  have hBind0 : spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt pinStrMs0 :=
    ⟨⟨trivial, trivial⟩,
      ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩
  have hNeBind : ∀ d, d ≠ 3 → ∀ b, b ∈ [(1, 3, ([] : SubPath))] → b.2.1 ≠ d := by
    intro d hd b hb
    cases hb with
    | head => exact fun h => hd h.symm
    | tail _ h => cases h
  have hStr0 : UnsizedStrDstAt 8 pinStrMs0.memory wideStr5 (WidePtrVal.toValue 8 wideStr5)
      helloBytes bytesStr5 :=
    str_unsizedDst64.of_frame rfl (fun _ h => by cases h)
  obtain ⟨hS1, hPin1, hBind1, hW1⟩ :=
    mirStep_call_sizeOfVal_str_preserves_spatialPin tagOfLoan (body := pinStrBody)
      (cur := pinStrBody) (ms := pinStrMs0) (dstLoc := 4) (p := p10) (len := 5)
      (locals' := pinStrMs0.frame.locals) (updatedLocals := pinStrLocals1) hPin0 hBind0
      (by decide) (hNeBind 4 (by decide))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      rfl rfl (by decide) rfl rfl rfl
  have hStr1 := hStr0.of_invalidateDirectDestWriteBorrows (dstLoc := 4) pinStrMs0.frame.locals
    (lookupBorrow_targetLocal_ne_of_forall_mem (by decide) _)
  obtain ⟨hS2, hPin2, hBind2, hW2⟩ :=
    mirStep_call_alignOfVal_str_preserves_spatialPin tagOfLoan (body := pinStrBody)
      (cur := pinStrBody) (dstLoc := 5) (p := p10) (len := 5)
      (locals' := pinStrLocals1Moved) (updatedLocals := pinStrLocals2) hPin1 hBind1
      (by decide) (hNeBind 5 (by decide))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      rfl rfl (by decide) rfl rfl rfl
  have hStr2 := hStr1.of_invalidateDirectDestWriteBorrows (dstLoc := 5) pinStrLocals1Moved
    (lookupBorrow_targetLocal_ne_of_forall_mem (by decide) _)
  exact ⟨_, _, hS1, hPin1, hBind1, hStr1, hS2, hPin2, hBind2, hStr2⟩

/-- Borrow `77` of the backing array `_0` after it has been disabled (e.g. by a conflicting
foreign write). -/
def disabledMem : Memory :=
  { borrows := [{ tag := 77, targetLocal := 0, targetProjection := [], perm := .disabled,
                  rangeOffset := 0, rangeLen := 16 }] }

def disabledLocals : List LocalSlot :=
  [.init pinArrVal, .init (WidePtrVal.toValue 8 wide77), .uninit, .uninit]

/-- MIR body building a provenance-free empty slice via `AggregateKind.rawPtr`
and extracting its `UnOp.ptrMetadata` while `_2 : [u32; 4]` is spatially pinned. -/
def danglingPinBody : CapturedMir :=
  { (Anneal.MirLoops.mkMirBody "test::dangling_slice_metadata_with_pinned_array" 1
      [{ mutability := .mut, ty := usizeTy, debugName := some "_0" },
       { mutability := .not, ty := usizeTy, debugName := some "addr" },
       { mutability := .mut, ty := pinArrTy, debugName := some "pinned_arr" },
       { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 0 },
         debugName := some "bound_u32" },
       { mutability := .mut, ty := usizeTy, debugName := some "zero_len" },
       { mutability := .mut, ty := { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 1 },
         debugName := some "dang_sl" }]
      [retBlock
         [{ kind := .assign { local_ := 5, projection := [] }
              (.aggregate (.rawPtr sliceU32Ty .not)
                [.copy { local_ := 1, projection := [] },
                 .copy { local_ := 4, projection := [] }])
            span := "stmt_dangling_from_raw_parts" },
          { kind := .assign { local_ := 0, projection := [] }
              (.unaryOp .ptrMetadata (.copy { local_ := 5, projection := [] }))
            span := "stmt_dangling_ptr_metadata" }]]) with
    layouts := layouts64 }

/-- **Metadata-without-deref under a disabled tag**: once borrow `77` behind
raw `*const [u32]` `_1` is `.disabled`, dereferencing `Rvalue.len (*_1)` faults
`.ub` (`WidePtrVal.evalRvalue_len_disabled_ub_and_ptrMetadata_ok`), while
`UnOp.ptrMetadata(_1)` still yields `4` and the live `size_of_val::<[u32]>(_1)`
step still writes `16` (neither consults `mem.borrows`). Also steps
`danglingPinBody` across `mirStep_assign_aggregate_rawPtr_wide_scalarAddr_preserves_spatialPin`
and `mirStep_assign_ptrMetadata_wide_scalarAddr_preserves_spatialPin` while
`_2 : [u32; 4]` remains spatially pinned. -/
theorem metadata_without_deref_disabled_tag_contrast :
    let bodyU32 := sizeAlignSliceCallerMir (.uint .u32)
    let s0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := disabledLocals }, memory := disabledMem }
    let s1 : MachineState :=
      { frame := { blockIdx := 1, stmtIdx := 0,
                   locals := disabledLocals.set 2 (.init (.scalar ⟨16, 8⟩)) }
        memory := disabledMem }
    let dLocals0 : List LocalSlot :=
      [.uninit, .init (.scalar ⟨4, 8⟩), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
       .init (.scalar ⟨0, 8⟩), .uninit]
    let dMs0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := dLocals0 }
        memory := { borrows := pinBorrows } }
    evalRvalue disabledLocals (.len { local_ := 1, projection := [.deref] }) disabledMem dstDecls
        layouts64 = .ub ∧
    evalRvalue disabledLocals (.unaryOp .ptrMetadata (.copy { local_ := 1, projection := [] }))
        disabledMem dstDecls layouts64 = .ok (.scalar ⟨4, 8⟩) disabledLocals disabledMem ∧
    PureMirExec.mirStep bodyU32 s0 = .cont s1 ∧
    (∃ dMs1 dMs2,
      PureMirExec.mirStep danglingPinBody dMs0 = .cont dMs1 ∧
      PureMirExec.mirStep danglingPinBody dMs1 = .cont dMs2 ∧
      spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] pinSt dMs2 ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt dMs2) := by
  intro bodyU32 s0 s1 dLocals0 dMs0
  let dLocals1 : List LocalSlot :=
    [.uninit, .init (.scalar ⟨4, 8⟩), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
     .init (.scalar ⟨0, 8⟩), .init (.aggregate 0 [.scalar ⟨4, 8⟩, .scalar ⟨0, 8⟩])]
  let dLocals2 : List LocalSlot :=
    [.init (.scalar ⟨0, 8⟩), .init (.scalar ⟨4, 8⟩), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
     .init (.scalar ⟨0, 8⟩), .init (.aggregate 0 [.scalar ⟨4, 8⟩, .scalar ⟨0, 8⟩])]
  obtain ⟨hLenUb, hMetaOk⟩ :=
    WidePtrVal.evalRvalue_len_disabled_ub_and_ptrMetadata_ok disabledLocals disabledLocals
      { local_ := 1, projection := [.deref] } (.copy { local_ := 1, projection := [] })
      disabledMem dstDecls layouts64 [] (.uint .u32) 0
      { tag := 77, targetLocal := 0, targetProjection := [], perm := .disabled,
        rangeOffset := 0, rangeLen := 16 }
      wide77 rfl rfl rfl rfl rfl rfl
  obtain ⟨_, hMir, _, _⟩ := mirStep_call_sizeOfVal_slice (body := bodyU32) (cur := bodyU32)
    (s := s0) (p := ⟨77, 0⟩) (len := 4) (locals' := disabledLocals)
    (updatedLocals := s1.frame.locals)
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  have hPin0 : spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] pinSt dMs0 :=
    ⟨_, _, [], _, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      ⟨_, rfl, rfl, rfl, rfl⟩⟩
  have hBind0 : spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt dMs0 :=
    ⟨⟨trivial, trivial⟩,
      ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩
  have hNeBind : ∀ d, d ≠ 3 → ∀ b, b ∈ [(1, 3, ([] : SubPath))] → b.2.1 ≠ d := by
    intro d hd b hb
    cases hb with
    | head => exact fun h => hd h.symm
    | tail _ h => cases h
  obtain ⟨hD1, hPin1, hBind1, _⟩ :=
    mirStep_assign_aggregate_rawPtr_wide_scalarAddr_preserves_spatialPin tagOfLoan
      (body := danglingPinBody) (cur := danglingPinBody) (ms := dMs0) (dstLoc := 5)
      (addr := 4) (len := 0) (locals₁ := dLocals0) (locals₂ := dLocals0) (locals₃ := dLocals1)
      hPin0 hBind0 (by decide) (hNeBind 5 (by decide))
      rfl (Or.inl rfl) rfl rfl rfl (by decide) (by decide) rfl rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      rfl rfl rfl rfl
  obtain ⟨hD2, hPin2, hBind2, _⟩ :=
    mirStep_assign_ptrMetadata_wide_scalarAddr_preserves_spatialPin tagOfLoan
      (body := danglingPinBody) (cur := danglingPinBody) (dstLoc := 0)
      (addr := 4) (len := 0) (locals₁ := dLocals1) (locals₂ := dLocals2)
      hPin1 hBind1 (by decide) (hNeBind 0 (by decide))
      rfl (Or.inl rfl) rfl rfl rfl (by decide) rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      rfl rfl rfl rfl
  exact ⟨hLenUb, hMetaOk, hMir, _, _, hD1, hD2, hPin2, hBind2⟩

/-- MIR body executing `_4 = copy _1 as *const ()` (`CastKind.ptrToPtr` wide-to-thin) and
`_5 = copy _1 as *mut [u32]` (`CastKind.ptrToPtr` wide-to-wide) while `_2 : [u32; 4]` is spatially
pinned and `_3 : u32` holds an active loan binding. -/
def ptrToPtrPinBody : CapturedMir :=
  { (Anneal.MirLoops.mkMirBody "test::ptrToPtr_with_pinned_array" 1
      [{ mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 }, debugName := some "_0" },
       { mutability := .not, ty := { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 1 },
         debugName := some "p" },
       { mutability := .mut, ty := pinArrTy, debugName := some "pinned_arr" },
       { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 0 },
         debugName := some "bound_u32" },
       { mutability := .mut, ty := { kind := .rawPtr .not (.tuple []), layoutIdx := 0 },
         debugName := some "data_ptr" },
       { mutability := .mut, ty := { kind := .rawPtr .mut (.slice (.uint .u32)), layoutIdx := 1 },
         debugName := some "mut_sl" }]
      [retBlock
         [{ kind := .assign { local_ := 4, projection := [] }
              (.cast .ptrToPtr (.copy { local_ := 1, projection := [] })
                { kind := .rawPtr .not (.tuple []), layoutIdx := 0 })
            span := "stmt_cast_wide_to_thin" },
          { kind := .assign { local_ := 5, projection := [] }
              (.cast .ptrToPtr (.copy { local_ := 1, projection := [] })
                { kind := .rawPtr .mut (.slice (.uint .u32)), layoutIdx := 1 })
            span := "stmt_cast_wide_to_wide" }]]) with
    layouts := layouts64 }

/-- **`CastKind.ptrToPtr` spatial-pin lifters, provenance-free casts, and negative `.ub` canaries**:
- `mirStep_assign_cast_ptrToPtr_wide_to_thin_preserves_spatialPin`,
  `mirStep_assign_cast_ptrToPtr_wide_to_wide`, and
  `mirStep_assign_cast_ptrToPtr_wide_to_wide_preserves_spatialPin` step across `p as *const ()`
  and `p as *mut [u32]` while `_2 : [u32; 4]` remains spatially pinned and `_3 : u32` remains bound;
- `evalRvalue_cast_ptrToPtr_wide_scalarAddr_to_thin` and
  `evalRvalue_cast_ptrToPtr_wide_scalarAddr_to_wide` cast provenance-free wide pointers;
- Stage-1 conservative divergence: `evalRvalue_cast_ptrToPtr_wide_to_thin_disabled_ub`
  faults `.ub` when casting a `.disabled` borrow-backed wide pointer to a thin
  pointer because Stage-1 eagerly narrows borrow provenance in `deriveStackElemThinPtr`
  (whereas Rust/Miri/MiniRust pointer-to-pointer casts do not dereference or
  check borrow liveness, and Stage-1 `UnOp.ptrMetadata` likewise succeeds);
- `evalRvalue_cast_ptrToPtr_thin_to_wide_ub` and `evalRvalue_cast_ptrToPtr_wide_slice_to_dyn_ub`
  fault `.ub` on thin-to-wide and slice-to-`dyn` `CastKind.ptrToPtr` casts. -/
theorem ptrToPtr_spatialPin_scalarAddr_and_negative_canaries :
    let unitPtrTy : Ty := { kind := .rawPtr .not (.tuple []), layoutIdx := 0 }
    let mutSlicePtrTy : Ty := { kind := .rawPtr .mut (.slice (.uint .u32)), layoutIdx := 1 }
    let dynPtrTy : Ty := { kind := .rawPtr .not (.dynamic "core::fmt::Debug"), layoutIdx := 1 }
    let danglingVal : Value := .aggregate 0 [.scalar ⟨4, 8⟩, .scalar ⟨0, 8⟩]
    let danglingLocals : List LocalSlot := (dstLocals 8).set 1 (.init danglingVal)
    let cLocals0 : List LocalSlot :=
      [.init .unit, .init (WidePtrVal.toValue 8 wide4), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
       .uninit, .uninit]
    let cMs0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := cLocals0 }
        memory := { mem0 with borrows := pinBorrows } }
    (∃ cMs1 cMs2,
      PureMirExec.mirStep ptrToPtrPinBody cMs0 = .cont cMs1 ∧
      PureMirExec.mirStep ptrToPtrPinBody cMs1 = .cont cMs2 ∧
      spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] pinSt cMs2 ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt cMs2) ∧
    evalRvalue danglingLocals (.cast .ptrToPtr (.copy { local_ := 1, projection := [] }) unitPtrTy)
        mem0 dstDecls layouts64 = .ok (.scalar ⟨4, 8⟩) danglingLocals mem0 ∧
    evalRvalue danglingLocals
        (.cast .ptrToPtr (.copy { local_ := 1, projection := [] }) mutSlicePtrTy)
        mem0 dstDecls layouts64 = .ok danglingVal danglingLocals mem0 ∧
    evalRvalue disabledLocals (.cast .ptrToPtr (.copy { local_ := 1, projection := [] }) unitPtrTy)
        disabledMem dstDecls layouts64 = .ub ∧
    evalRvalue (dstLocals 8)
        (.cast .ptrToPtr (.copy { local_ := 5, projection := [] }) mutSlicePtrTy)
        mem0 dstDecls layouts64 = .ub ∧
    evalRvalue (dstLocals 8)
        (.cast .ptrToPtr (.copy { local_ := 1, projection := [] }) dynPtrTy)
        mem0 dstDecls layouts64 = .ub := by
  intro unitPtrTy mutSlicePtrTy dynPtrTy danglingVal danglingLocals cLocals0 cMs0
  let cLocals1 : List LocalSlot :=
    [.init .unit, .init (WidePtrVal.toValue 8 wide4), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
     .init (.ptr p9 8), .uninit]
  let cLocals2 : List LocalSlot :=
    [.init .unit, .init (WidePtrVal.toValue 8 wide4), .init pinArrVal, .init (.scalar ⟨99, 4⟩),
     .init (.ptr p9 8), .init (WidePtrVal.toValue 8 wide4)]
  have hPin0 : spatialPinnedBlockHolds tagOfLoan layouts64 pinArrTy 0 0 pinCodec 2 [] pinSt cMs0 :=
    ⟨_, _, [], _, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      ⟨_, rfl, rfl, rfl, rfl⟩⟩
  have hBind0 : spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt cMs0 :=
    ⟨⟨trivial, trivial⟩,
      ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩
  have hNeBind : ∀ d, d ≠ 3 → ∀ b, b ∈ [(1, 3, ([] : SubPath))] → b.2.1 ≠ d := by
    intro d hd b hb
    cases hb with
    | head => exact fun h => hd h.symm
    | tail _ h => cases h
  obtain ⟨hC1, hPin1, hBind1, _⟩ :=
    mirStep_assign_cast_ptrToPtr_wide_to_thin_preserves_spatialPin tagOfLoan
      (body := ptrToPtrPinBody) (cur := ptrToPtrPinBody) (ms := cMs0) (dstLoc := 4)
      (p := p9) (len := 4) (locals₁ := cLocals0) (locals₂ := cLocals1)
      hPin0 hBind0 (by decide) (hNeBind 4 (by decide))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      rfl rfl rfl rfl
  have _ := mirStep_assign_cast_ptrToPtr_wide_to_wide (body := ptrToPtrPinBody)
    (cur := ptrToPtrPinBody)
    (s := { frame := { blockIdx := 0, stmtIdx := 1, locals := cLocals1 },
            memory := { cMs0.memory with
              borrows := invalidateConflictingBorrows cMs0.memory.borrows 4 .none 0 } })
    (dstLoc := 5) (q := p9) (len := 4) (locals₁ := cLocals1) (locals₂ := cLocals2)
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨hC2, hPin2, hBind2, _⟩ :=
    mirStep_assign_cast_ptrToPtr_wide_to_wide_preserves_spatialPin tagOfLoan
      (body := ptrToPtrPinBody) (cur := ptrToPtrPinBody) (dstLoc := 5)
      (p := p9) (len := 4) (locals₁ := cLocals1) (locals₂ := cLocals2)
      hPin1 hBind1 (by decide) (hNeBind 5 (by decide))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl
      (by intro b hb; cases hb with | head => rfl | tail _ h => cases h)
      rfl rfl rfl rfl
  exact ⟨⟨_, _, hC1, hC2, hPin2, hBind2⟩,
    evalRvalue_cast_ptrToPtr_wide_scalarAddr_to_thin danglingLocals danglingLocals
      (.copy { local_ := 1, projection := [] }) unitPtrTy mem0 dstDecls layouts64 4 0
      rfl (by decide) rfl,
    evalRvalue_cast_ptrToPtr_wide_scalarAddr_to_wide danglingLocals danglingLocals
      (.copy { local_ := 1, projection := [] }) mutSlicePtrTy mem0 dstDecls layouts64 4 0
      rfl rfl (by decide) (by decide) rfl,
    evalRvalue_cast_ptrToPtr_wide_to_thin_disabled_ub disabledLocals disabledLocals
      (.copy { local_ := 1, projection := [] }) unitPtrTy disabledMem dstDecls layouts64
      ⟨77, 0⟩ 4
      { tag := 77, targetLocal := 0, targetProjection := [], perm := .disabled,
        rangeOffset := 0, rangeLen := 16 }
      rfl rfl rfl rfl,
    evalRvalue_cast_ptrToPtr_thin_to_wide_ub (dstLocals 8) (dstLocals 8)
      (.copy { local_ := 5, projection := [] }) mutSlicePtrTy mem0 dstDecls layouts64 p9 rfl rfl,
    evalRvalue_cast_ptrToPtr_wide_slice_to_dyn_ub (dstLocals 8) (dstLocals 8)
      (.copy { local_ := 1, projection := [] }) dynPtrTy mem0 dstDecls layouts64 p9 4
      rfl rfl rfl rfl⟩

/-! ## 8. Automated `run_cmd` Axiom & Reachability Audit -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let constructive : List Name := [``propext, ``Quot.sound]
  let mut audited : Nat := 0
  let mut theorems : Nat := 0
  let mut auditedThms : Array Name := #[]
  let mut modIdxs : Array ModuleIdx := #[]
  for (modName, anchor, minCount) in
      [(`Anneal.MirLiftCore, ``Anneal.MirLiftCore.updateBorrowPerm_tag, 100),
       (`Anneal.SepLogicLenses, ``Anneal.SepLogicLenses.WidePtrVal.dataVal, 60),
       (`Anneal.PureLift.V2026_06_01Bridge, ``Anneal.PureLift.V2026_06_01Bridge.stdWideSliceVal, 40)] do
    let some modIdx := env.getModuleIdx? modName | throwError "module {modName} not imported"
    modIdxs := modIdxs.push modIdx
    let some anchorRange ← findDeclarationRanges? anchor | throwError "no range for {anchor}"
    let startLine := anchorRange.range.pos.line
    let mut count : Nat := 0
    for (n, ci) in env.constants.map₁.toList do
      if env.getModuleIdxFor? n == some modIdx then
        if let some r ← findDeclarationRanges? n then
          if r.range.pos.line ≥ startLine then
            if ci.isUnsafe then throwError "unsafe declaration: {n}"
            let axs ← collectAxioms n
            for a in axs do
              unless constructive.contains a do
                let mut culprits : List Name := []
                for sub in ci.getUsedConstantsAsSet do
                  let subAxs ← collectAxioms sub
                  if subAxs.contains a then
                    culprits := sub :: culprits
                throwError "{n} depends on non-constructive or disallowed axiom {a} via {culprits}"
            -- Projection discipline (§2.4): neither new definitions (nor their transitive matcher
            -- closures) nor new theorem statements (`ci.type`) may reach `Prod.casesOn` /
            -- `Prod.rec` / `Prod.recOn`.
            for bad in [``Prod.casesOn, ``Prod.rec, ``Prod.recOn] do
              if ci.type.getUsedConstantsAsSet.contains bad then
                throwError "projection discipline violated in statement type of {n}: reaches {bad}"
            if ci matches .defnInfo _ then
              let mut toCheck : Array Name := #[n]
              let mut seen : NameSet := ({} : NameSet).insert n
              let mut idx : Nat := 0
              while idx < toCheck.size do
                let d := toCheck[idx]!
                idx := idx + 1
                if let some dci := env.find? d then
                  for bad in [``Prod.casesOn, ``Prod.rec, ``Prod.recOn] do
                    if dci.getUsedConstantsAsSet.contains bad then
                      throwError "projection discipline violated: {n} reaches {bad} via {d}"
                  for c in dci.getUsedConstantsAsSet do
                    if Lean.Meta.isMatcherCore env c && !seen.contains c then
                      seen := seen.insert c
                      toCheck := toCheck.push c
            count := count + 1
            if ci matches .thmInfo _ then
              theorems := theorems + 1
              auditedThms := auditedThms.push n
    if count < minCount then
      throwError "{modName}: audited only {count} declarations (expected ≥ {minCount})"
    audited := audited + count
  let inMods : Name → Bool := fun c =>
    match env.getModuleIdxFor? c with
    | some i => modIdxs.contains i
    | none => false
  let mut reached : NameSet := {}
  let mut work : Array Name := #[]
  for (n, ci) in env.constants.map₂.toList do
    if (`Anneal.UnsizedDstMetadataLensTests).isPrefixOf n then
      if ci.isUnsafe then throwError "unsafe declaration: {n}"
      let axs ← collectAxioms n
      for a in axs do
        unless allowed.contains a do
          throwError "{n} depends on disallowed axiom {a}"
      audited := audited + 1
      for c in ci.getUsedConstantsAsSet do
        if inMods c && !reached.contains c then
          reached := reached.insert c
          work := work.push c
  while !work.isEmpty do
    let c := work.back!
    work := work.pop
    if let some ci := env.find? c then
      for d in ci.getUsedConstantsAsSet do
        if inMods d && !reached.contains d then
          reached := reached.insert d
          work := work.push d
  let unreached := auditedThms.filter (fun n => !reached.contains n)
  unless unreached.isEmpty do
    throwError "theorems not transitively reached by any test declaration: {unreached.toList}"
  logInfo m!"axiom & reachability audit passed: {audited} declarations ({theorems} module theorems, \
    all constructive and transitively reached by test declarations; no Prod.casesOn/Prod.rec)"

end Anneal.UnsizedDstMetadataLensTests
