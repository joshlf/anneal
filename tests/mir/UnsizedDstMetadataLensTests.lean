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
1. `Anneal.MirLiftCore` (`UnsizedDstMetadataLifters`),
2. `Anneal.SepLogicLenses` (`PtrMetadataOf`, `UnsizedSliceDstAt`, `UnsizedStrDstAt`),
3. `Anneal.PureLift.V2026_06_01Bridge` (`WideSliceDstBridge`: `stdWideSliceVal`,
   `StdValRefines.wideSlice`, and `spatialPinnedBlockHolds` / `spatialBindingsHold` framing).
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

theorem arr_unsizedDst64 :
    UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) mem0 wide4
      (WidePtrVal.toValue 8 wide4) xs4 bytes16 :=
  UnsizedSliceDstAt.of_sliceTypedAt 8 (.uint .u32) mem0 arr_sliceTypedAt

theorem arr_unsizedDst32 :
    UnsizedSliceDstAt ByteLensCodec.u32LE 4 (.slice (.uint .u32)) mem0 wide4
      (WidePtrVal.toValue 4 wide4) xs4 bytes16 :=
  UnsizedSliceDstAt.of_sliceTypedAt 4 (.uint .u32) mem0 arr_sliceTypedAt

theorem str_unsizedDst64 :
    UnsizedStrDstAt 8 mem0 wideStr5 (WidePtrVal.toValue 8 wideStr5) helloBytes bytesStr5 :=
  UnsizedSliceDstAt.of_str_sliceTypedAt 8 mem0 str_sliceTypedAt

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

theorem unsizedDst_projections_split_and_unique :
    xs4.length = wide4.2 ∧
    WidePtrVal.dataVal 8 wide4 = .ptr wide4.1 8 ∧
    WidePtrVal.metaVal 8 wide4 = .scalar ⟨xs4.length, 8⟩ ∧
    PtrMetadataOf 8 (WidePtrVal.toValue 8 wide4) (.scalar ⟨xs4.length, 8⟩) ∧
    PtrMetadataOf 8 (WidePtrVal.toValue 8 (WidePtrVal.mk p9 4)) (.scalar ⟨4, 8⟩) ∧
    (∀ ys, UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32)) mem0 wide4
      (WidePtrVal.toValue 8 wide4) ys bytes16 → ys = xs4) ∧
    (∀ m₁ m₂, PtrMetadataOf 8 (WidePtrVal.toValue 8 wide4) m₁ →
      PtrMetadataOf 8 (WidePtrVal.toValue 8 wide4) m₂ → m₁ = m₂) ∧
    isUnsizedRawPtrPointee { kind := .slice (.uint .u32), layoutIdx := 0 } = true ∧
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
    UnsizedSliceDstAt.of_splitAt (k := 2) (by decide) hL hR⟩

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

/-- `AggregateKind.rawPtr` (`from_raw_parts`) on `[u32]`, `str`, and thin `u32`, plus
`to_raw_parts` round-trip preserving `UnsizedSliceDstAt`, `ActiveTypedSliceBorrow`, and
`ActiveTypedSliceMutBorrow`, followed by a borrow-backed write! -/
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
`str` (`len = 5 → size = 5, align = 1`), empty `[u32]` (`len = 0 → size = 0, align = 4`),
ZST `[(); 1000]` (`elemSz = 0 → size = 0, align = 1`), and sized `u32` (`size = 4, align = 4`). -/
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
    (∃ sEmpty_1, PureMirExec.mirStep bodyU32 sEmpty_0 = .cont sEmpty_1) ∧
    (∃ sZst_1, PureMirExec.mirStep bodyZst sZst_0 = .cont sZst_1) ∧
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
      (arr_unsizedDst64.of_mem_change sU32_0.memory)
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
      (arr_unsizedDst64.of_mem_change sU32_1.memory)
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
      hDstStr_1 rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  obtain ⟨_, hMirEmpty, _, _, _⟩ :=
    evalIntrinsic_sizeOfValRaw_slice (body := bodyU32) (cur := bodyU32) (s := sEmpty_0)
      empty_and_zst_unsizedDst_witnesses.1
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  obtain ⟨_, hMirZst, _, _, _⟩ :=
    evalIntrinsic_sizeOfValRaw_slice (body := bodyZst) (cur := bodyZst) (s := sZst_0)
      empty_and_zst_unsizedDst_witnesses.2.2
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  exact ⟨evalSliceSizeOfVal_zst 1000,
    evalSliceSizeOfVal_empty 4,
    ⟨hStep1, hMut1, hSh1⟩,
    ⟨hStep2, hMut2, hSh2⟩,
    hMirStr_1,
    hMirStr_2,
    ⟨_, hMirEmpty⟩,
    ⟨_, hMirZst⟩,
    evalNonSelectIntrinsicCall_sizeOfVal_sized sStr_0 _ bodyU32.localDecls bodyU32.layouts []
      sStr_0.frame.locals { local_ := 2, projection := [] } 1 (.uint .u32) 4 p9
      rfl rfl rfl rfl (by decide),
    evalNonSelectIntrinsicCall_alignOfVal_sized sStr_0 _ bodyU32.localDecls bodyU32.layouts []
      sStr_0.frame.locals { local_ := 3, projection := [] } 1 (.uint .u32) 4 p9
      rfl rfl rfl rfl⟩

/-! ## 5. End-to-End `MirWpConverges` & `PureLift.V2026_06_01Bridge` Spatial-Pin Preservation -/

def tagOfLoan (lid : LoanId) : Nat := lid + 77

def pinCodec : SpatialCodec StdVal := u32SpatialCodec layouts64

def pinBody : CapturedMir :=
  { (Anneal.MirLoops.mkMirBody "test::dst_metadata_layout_with_pinned_borrow" 1
      [{ mutability := .mut, ty := { kind := .tuple [.uint .usize, .uint .usize], layoutIdx := 1 },
         debugName := some "_0" },
       { mutability := .not, ty := { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 1 },
         debugName := some "raw_sl" },
       { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 0 },
         debugName := some "pinned_u32" },
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
                   .copy { local_ := 4, projection := [] }])
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
               [.copy { local_ := 5, projection := [] }]
               { local_ := 7, projection := [] } (some 2) .continue_
             span := "term_align_of_val" }
         isCleanup := false },
       retBlock
         [{ kind := .assign { local_ := 0, projection := [] }
              (.aggregate .tuple
                [.copy { local_ := 6, projection := [] },
                 .copy { local_ := 7, projection := [] }])
            span := "stmt_layout_tuple" }]]) with
    layouts := layouts64 }

def pinBorrows : List BorrowEntry :=
  [{ tag := 77, targetLocal := 2, targetProjection := [], perm := .unique,
     rangeOffset := 0, rangeLen := 4 },
   { tag := 78, targetLocal := 3, targetProjection := [], perm := .unique,
     rangeOffset := 0, rangeLen := 4 }]

def pinSt : SymState StdVal :=
  ⟨[⟨.nat 42, .mutLocked 0⟩, ⟨.nat 99, .mutLocked 1⟩],
   [⟨0, .spatialPinned 0 pinCodec, ⟨.nat 42, .unborrowed⟩, .direct (.localReg 0) []⟩,
    ⟨1, .activeMut, ⟨.nat 99, .unborrowed⟩, .direct (.localReg 1) []⟩],
   [], [],
   [⟨0, 0, .readWrite, 0, 0, [.rawByte 42, .rawByte 0, .rawByte 0, .rawByte 0]⟩],
   1⟩

def pinMs0 : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0,
        locals :=
          [.uninit,
           .init (WidePtrVal.toValue 8 (WidePtrVal.mk ⟨77, 0⟩ 4)),
           .init (.scalar ⟨42, 4⟩),
           .init (.scalar ⟨99, 4⟩),
           .uninit, .uninit, .uninit, .uninit] }
    memory := { borrows := pinBorrows } }

theorem pinMs0_pinned_and_bound :
    spatialPinnedBlockHolds tagOfLoan layouts64 u32Ty 0 0 pinCodec 2 [] pinSt pinMs0 ∧
    spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt pinMs0 :=
  ⟨⟨_, _, [], _, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨_, rfl, rfl, rfl, rfl⟩⟩,
   ⟨⟨trivial, trivial⟩,
    ⟨⟨rfl, ⟨_, rfl, .nat (by decide)⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩, trivial⟩⟩⟩

/-- **Wide-slice `StdValRefines` constructor, field projections, inversion, and round-trip**. -/
theorem wideSlice_stdValRefines_witnesses :
    let wide77 : WidePtrVal := WidePtrVal.mk ⟨77, 0⟩ 4
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
       pinMs0.memory wide77 (WidePtrVal.toValue 8 wide77) xs4 bytes16) := by
  intro wide77
  let hDst77 : UnsizedSliceDstAt ByteLensCodec.u32LE 8 (.slice (.uint .u32))
      pinMs0.memory wide77 (WidePtrVal.toValue 8 wide77) xs4 bytes16 :=
    UnsizedSliceDstAt.of_sliceTypedAt 8 (.uint .u32) pinMs0.memory arr_sliceTypedAt
  have hRef8 : StdValRefines tagOfLoan (stdWideSliceVal 0 4) (WidePtrVal.toValue 8 wide77) :=
    StdValRefines.wideSlice8 tagOfLoan 0 wide77 rfl rfl (by decide)
  exact ⟨stdWideSliceVal_getField_zero 0 4,
    stdWideSliceVal_getField_one 0 4,
    hRef8,
    StdValRefines.wideSlice_data_and_meta tagOfLoan 0 8 wide77 rfl rfl (by decide),
    hRef8.wideSlice_toValue_inv,
    StdValRefines.of_unsizedSliceDstAt tagOfLoan 0 hDst77 rfl rfl (by decide),
    StdValRefines.wideSlice_ptrMetadata_refines tagOfLoan pinMs0.frame.locals pinMs0.frame.locals
      (.copy { local_ := 1, projection := [] }) pinBody.localDecls layouts64 hDst77 (by decide) rfl,
    StdValRefines.wideSlice_from_raw_parts_roundtrip tagOfLoan 0 pinMs0.frame.locals 1 0
      ptrU32Ty usizeTy .not pinBody.localDecls layouts64 hDst77
      (StdValRefines.of_unsizedSliceDstAt tagOfLoan 0 hDst77 rfl rfl (by decide))
      rfl rfl rfl⟩

def pinLocals1 : List LocalSlot :=
  [.uninit,
   .init (WidePtrVal.toValue 8 (WidePtrVal.mk ⟨77, 0⟩ 4)),
   .init (.scalar ⟨42, 4⟩),
   .init (.scalar ⟨99, 4⟩),
   .init (.scalar ⟨4, 8⟩),
   .uninit, .uninit, .uninit]

def pinLocals2 : List LocalSlot :=
  [.uninit,
   .init (WidePtrVal.toValue 8 (WidePtrVal.mk ⟨77, 0⟩ 4)),
   .init (.scalar ⟨42, 4⟩),
   .init (.scalar ⟨99, 4⟩),
   .init (.scalar ⟨4, 8⟩),
   .init (WidePtrVal.toValue 8 (WidePtrVal.mk ⟨77, 0⟩ 4)),
   .uninit, .uninit]

def pinLocals3 : List LocalSlot :=
  [.uninit,
   .init (WidePtrVal.toValue 8 (WidePtrVal.mk ⟨77, 0⟩ 4)),
   .init (.scalar ⟨42, 4⟩),
   .init (.scalar ⟨99, 4⟩),
   .init (.scalar ⟨4, 8⟩),
   .init (WidePtrVal.toValue 8 (WidePtrVal.mk ⟨77, 0⟩ 4)),
   .init (.scalar ⟨16, 8⟩),
   .uninit]

def pinLocals4 : List LocalSlot :=
  [.uninit,
   .init (WidePtrVal.toValue 8 (WidePtrVal.mk ⟨77, 0⟩ 4)),
   .init (.scalar ⟨42, 4⟩),
   .init (.scalar ⟨99, 4⟩),
   .init (.scalar ⟨4, 8⟩),
   .init (WidePtrVal.toValue 8 (WidePtrVal.mk ⟨77, 0⟩ 4)),
   .init (.scalar ⟨16, 8⟩),
   .init (.scalar ⟨4, 8⟩)]

def pinLocals5 : List LocalSlot :=
  [.init (.aggregate 0 [.scalar ⟨16, 8⟩, .scalar ⟨4, 8⟩]),
   .init (WidePtrVal.toValue 8 (WidePtrVal.mk ⟨77, 0⟩ 4)),
   .init (.scalar ⟨42, 4⟩),
   .init (.scalar ⟨99, 4⟩),
   .init (.scalar ⟨4, 8⟩),
   .init (WidePtrVal.toValue 8 (WidePtrVal.mk ⟨77, 0⟩ 4)),
   .init (.scalar ⟨16, 8⟩),
   .init (.scalar ⟨4, 8⟩)]

/-- **End-to-end multi-step `MirWpConverges` + `spatialPinnedBlockHolds` preservation**:
steps across `UnOp.ptrMetadata`, `AggregateKind.rawPtr` (`from_raw_parts`),
`core::intrinsics::size_of_val`, `core::intrinsics::align_of_val`, and `Layout::for_value_raw`
`(size, align)` tuple assembly, proving both `MirWpConverges` to `(16usize, 4usize)` and
that the spatial pin on `_2` and loan binding on `_3` remain intact throughout without unpinning! -/
theorem dst_metadata_and_layout_converges_preserving_spatialPin :
    Anneal.MirFuelFree.MirWpConverges pinBody pinMs0
      (fun out =>
        ∃ mem',
          out = .normal (.aggregate 0 [.scalar ⟨16, 8⟩, .scalar ⟨4, 8⟩], mem')) ∧
    ∃ ms1 ms2 ms3 ms4 ms5,
      PureMirExec.mirStep pinBody pinMs0 = .cont ms1 ∧
      spatialPinnedBlockHolds tagOfLoan layouts64 u32Ty 0 0 pinCodec 2 [] pinSt ms1 ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt ms1 ∧
      PureMirExec.mirStep pinBody ms1 = .cont ms2 ∧
      spatialPinnedBlockHolds tagOfLoan layouts64 u32Ty 0 0 pinCodec 2 [] pinSt ms2 ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt ms2 ∧
      PureMirExec.mirStep pinBody ms2 = .cont ms3 ∧
      spatialPinnedBlockHolds tagOfLoan layouts64 u32Ty 0 0 pinCodec 2 [] pinSt ms3 ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt ms3 ∧
      PureMirExec.mirStep pinBody ms3 = .cont ms4 ∧
      spatialPinnedBlockHolds tagOfLoan layouts64 u32Ty 0 0 pinCodec 2 [] pinSt ms4 ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt ms4 ∧
      PureMirExec.mirStep pinBody ms4 = .cont ms5 ∧
      spatialPinnedBlockHolds tagOfLoan layouts64 u32Ty 0 0 pinCodec 2 [] pinSt ms5 ∧
      spatialBindingsHold (mirSpatialModel tagOfLoan) [(1, 3, [])] pinSt ms5 := by
  obtain ⟨hPin0, hBind0⟩ := pinMs0_pinned_and_bound
  have hNeBind4 : ∀ b, b ∈ [(1, 3, ([] : SubPath))] → b.2.1 ≠ 4 := by
    intro b hb; cases hb with | head => decide | tail _ h => cases h
  have hNeBind5 : ∀ b, b ∈ [(1, 3, ([] : SubPath))] → b.2.1 ≠ 5 := by
    intro b hb; cases hb with | head => decide | tail _ h => cases h
  have hNeBind6 : ∀ b, b ∈ [(1, 3, ([] : SubPath))] → b.2.1 ≠ 6 := by
    intro b hb; cases hb with | head => decide | tail _ h => cases h
  have hNeBind7 : ∀ b, b ∈ [(1, 3, ([] : SubPath))] → b.2.1 ≠ 7 := by
    intro b hb; cases hb with | head => decide | tail _ h => cases h
  have hNeBind0 : ∀ b, b ∈ [(1, 3, ([] : SubPath))] → b.2.1 ≠ 0 := by
    intro b hb; cases hb with | head => decide | tail _ h => cases h
  obtain ⟨hS1, hPin1, hBind1⟩ :=
    mirStep_assign_ptrMetadata_preserves_spatialPin tagOfLoan (body := pinBody) (cur := pinBody)
      (ms := pinMs0) (dstLoc := 4) (locals₂ := pinLocals1) hPin0 hBind0 (by decide) hNeBind4
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨hS2, hPin2, hBind2⟩ :=
    mirStep_assign_aggregate_rawPtr_preserves_spatialPin tagOfLoan (body := pinBody) (cur := pinBody)
      (dstLoc := 5) (locals₃ := pinLocals2) hPin1 hBind1 (by decide) hNeBind5
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨hS3, hPin3, hBind3⟩ :=
    mirStep_call_sizeOfVal_slice_preserves_spatialPin tagOfLoan (body := pinBody) (cur := pinBody)
      (dstLoc := 6) (updatedLocals := pinLocals3) hPin2 hBind2 (by decide) hNeBind6
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  obtain ⟨hS4, hPin4, hBind4⟩ :=
    mirStep_call_alignOfVal_slice_preserves_spatialPin tagOfLoan (body := pinBody) (cur := pinBody)
      (dstLoc := 7) (updatedLocals := pinLocals4) hPin3 hBind3 (by decide) hNeBind7
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
  obtain ⟨hS5, hPin5, hBind5⟩ :=
    mirStep_assign_layout_tuple_preserves_spatialPin tagOfLoan (body := pinBody) (cur := pinBody)
      (dstLoc := 0) (vSize := .scalar ⟨16, 8⟩) (vAlign := .scalar ⟨4, 8⟩)
      (locals₃ := pinLocals5) hPin4 hBind4 (by decide) hNeBind0
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl
  have hConv : Anneal.MirFuelFree.MirWpConverges pinBody pinMs0
      (fun out =>
        ∃ mem', out = .normal (.aggregate 0 [.scalar ⟨16, 8⟩, .scalar ⟨4, 8⟩], mem')) :=
    ⟨6, ⟨_, rfl⟩⟩
  exact ⟨hConv, _, _, _, _, _,
    hS1, hPin1, hBind1,
    hS2, hPin2, hBind2,
    hS3, hPin3, hBind3,
    hS4, hPin4, hBind4,
    hS5, hPin5, hBind5⟩

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

/-- **Metadata-without-deref contrast**:
A wide raw pointer `*const [u32]` with out-of-bounds length `5` (`5 * 4 = 20 > 16` bytes on the
16-byte global `arrAlloc16`) faults with `.ub` when dereferenced by `Rvalue.len (*_1)`, yet
`UnOp.ptrMetadata(_1)` and `size_of_val_raw(_1)` (`5 * 4 = 20 < 2^63`) succeed without
dereferencing memory! -/
theorem metadata_without_deref_oob_and_disabled_contrast :
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
        (.scalar ⟨20, 8⟩) :=
  ⟨rfl,
   evalRvalue_unaryOp_ptrMetadata_wide _ _ (.copy { local_ := 1, projection := [] })
     mem0 dstDecls layouts64 p9 5 rfl,
   evalNonSelectIntrinsicCall_sizeOfVal_slice pinMs0 _ _ _ [] _
     { local_ := 2, projection := [] } 1 (.uint .u32) 4 p9 5 rfl rfl (by decide)⟩

/-! ## 7. Automated `run_cmd` Axiom & Reachability Audit -/

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
      [(`Anneal.MirLiftCore, ``Anneal.MirLiftCore.updateBorrowPerm_tag, 35),
       (`Anneal.SepLogicLenses, ``Anneal.SepLogicLenses.WidePtrVal.dataVal, 25),
       (`Anneal.PureLift.V2026_06_01Bridge, ``Anneal.PureLift.V2026_06_01Bridge.stdWideSliceVal, 20)] do
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
    throwError "theorems not instantiated by any witness: {unreached.toList}"
  logInfo m!"axiom & reachability audit passed: {audited} declarations ({theorems} module theorems, \
    all constructive and instantiated by witnesses)"

end Anneal.UnsizedDstMetadataLensTests
