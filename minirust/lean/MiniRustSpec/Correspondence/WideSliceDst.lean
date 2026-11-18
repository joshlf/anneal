/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.TbWitness
import MiniRustSpec.Correspondence.ProvenanceWitness
import MiniRustSpec.Correspondence.IntrinsicFallback

/-!
# Wide-Slice and Unsized DST Pointer-Metadata Correspondence (`MiniRustSpec`)

Operational correspondence between Anneal's trusted MIR semantics
(`Trusted.Rustc.V2026_06_01.MirSemantics`) and MiniRust's operational semantics
(`MiniRustSpec.Interp` over both `BasicMemory<x86_64>` (`Mach`) and
`TreeBorrowsMemory<x86_64>` (`MachTB`)) for wide-slice (`[T]`) and string-slice (`str`)
unsized DST pointer-metadata operations:

1. **Symbolic Wide-Slice Value, Layout, Encoding & Metadata Correspondence**:
   - Anneal's wide-pointer representation `.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]` (and
     provenance-free `.aggregate 0 [.scalar ⟨addr, 8⟩, .scalar ⟨len, 8⟩]`) over `.slice elemTy`
     and `.str` corresponds to MiniRust's `Value.Ptr ⟨thin, some (.ElementCount len)⟩` at
     16-byte, 8-byte-aligned `Type.Ptr (.Raw .ElementCount)` / `Type.Ptr (.Ref mutbl sliceInfo)`,
     whose representation relation (`encodeWidePtr` / `decodeWidePtr`) is byte-identical to the
     16-byte 2-field tuple `PtrType.as_wide_pair` (`[(0, *const ()), (8, usize)]`).
2. **Symbolic Lockstep Correspondence (`UnOp.ptrMetadata`, `AggregateKind.rawPtr`, `to_raw_parts`)**:
   - `UnOp.ptrMetadata`: Anneal `evalRvalue ... (.unaryOp .ptrMetadata op)` and MiniRust
     `PointerMetaKind.encode_as_value` extract `.scalar ⟨len, 8⟩` / `.Int len` on wide `[T]` and
     `str` pointers (including provenance-free, dangling, out-of-bounds, and `.disabled`-borrow
     pointers, without dereferencing memory!) and `.unit` / `.Tuple []` (`unit_value()`) on thin
     pointers.
   - `to_raw_parts` (`CastKind.ptrToPtr` wide-to-thin `p as *const ()` $\mapsto$
     `UnOp.GetThinPointer`, and wide-to-wide `*const [T] as *mut [T]` / `*const str as *const [u8]`
     $\mapsto$ identity) and `AggregateKind.rawPtr` (`ptr::from_raw_parts(_mut)` /
     `ptr::slice_from_raw_parts(_mut)`) round-trip preserving provenance (`allocId`, Tree Borrows
     `tag`), byte offset, and element count in lockstep across Anneal, `Mach`, and `MachTB`.
3. **Symbolic Lockstep Correspondence (`core::intrinsics::size_of_val` & `align_of_val`)**:
   - Anneal's `evalSliceSizeOfVal elemSz ⟨len, 8⟩` (`Nat.blt (len * elemSz) (signedHalfModulus 8)`)
     and `evalNonSelectIntrinsicCall` (`.sizeOfVal` / `.alignOfVal`) match MiniRust's
     `LayoutStrategy.compute_size_and_align` (`Machine::compute_size` / `compute_align`) on every
     in-bounds length across `[T]`, `str` (`elemSz = 1, align = 1`), empty slices (`len = 0`), and
     ZST slices (`elemSz = 0`).
   - **Honest UB locus (§6)**: MiniRust's `UnOp::ComputeSize` / `ComputeAlign` are *total* (no
     `isize::MAX` check, `computeSize_computeAlign_slice_total`); MiniRust's `isize::MAX` bound
     (`x86_64.valid_size`, `inBounds size .Signed x86_64.PTR_SIZE`) is enforced only by
     `check_ptr` on *safe* pointers (`&[T]` / `&mut [T]` / `&str`). Anneal's `.ub` at
     `len * elemSz ≥ 2^63` therefore agrees with MiniRust for references
     (`sliceSizeOverflow_minirust_ub_locus`) and is strictly more restrictive (fail-closed, like
     Miri's `InvalidMeta(SliceTooBig)`) for raw `*const [T]` pointers
     (`div_rawSliceSizeOfVal_isizeMax_anneal_ub_vs_minirust_total`). The executable Lean
     `MiniRustSpec.Interp` does not implement `GetMetadata` / `ComputeSize` / `ComputeAlign`
     (`minirust_interp_metadata_unops_unsupported`), so the MiniRust side of those operations is
     stated against the spec functions they denote (`PointerMetaKind.encode_as_value`,
     `computeSize`, `computeAlign`) or lowered via `Transmute` to `mrWidePairTupleTy`.
4. **Symbolic & Concrete `slice::from_raw_parts(_mut)` (`&*p` / `&mut *p`), `Rvalue.len (*s)`,
   Checked Slice Indexing `(*s)[i]`, and Tree Borrows `Frozen` / `Unique` / `Disabled` UB**:
   - Reborrowing `*wide_raw_ptr` to `&[T]` / `&mut [T]`, reading `Rvalue.len (*s)` and `(*s)[i]`,
     writing `(*s)[i] = v`, out-of-bounds indexing `i ≥ len` UB, and Tree Borrows `Disabled`
     parent-write invalidation (contrasted with `UnOp.ptrMetadata(s)` succeeding without deref).
5. **Concrete Multi-Way Execution Witnesses & Negative/Divergence Canaries**:
   - Kernel-checked (`rfl` / `decide +kernel`, zero `native_decide`) 3-way witnesses across
     Anneal, `Mach`, and `MachTB`, including the exact `isize::MAX` (`len = 2^61 - 1` vs.
     `len = 2^61` for `[u32]`) boundary and the documented Stage-1 `Trusted` fail-closed
     provenance-free `.scalar`-address `size_of_val` divergence on empty slices (`len = 0`).
   - **Aliasing-model divergence (§6)**: on the *faithful* MiniRust translation of the
     raw-pointer parent-write program (`&raw mut _2[0]` + `slice_from_raw_parts_mut`, direct
     write to `_2`, read `(*_4)[0]`), Anneal's Stacked-Borrows-style borrow tracker faults while
     both `Mach` and `MachTB` return `1` (Tree Borrows raw pointers inherit the parent tag, and
     `BasicMemory` has no aliasing model); Tree Borrows `Disabled` UB is only reachable through a
     retagged `&mut` reference (`wideSliceParentWrite_aliasingDivergence_and_metadata_three_way`).
-/

namespace MiniRustSpec.Correspondence.WideSliceDst

set_option Elab.async false
set_option linter.unusedSimpArgs false

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec
open MiniRustSpec.Gen
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness
open MiniRustSpec.Correspondence.PointerWitness
open MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.Correspondence.TbWitness

/-! ## 1. Wide-Slice Value, Layout, Encoding & Metadata Correspondence -/

/-- Anneal runtime representation of a wide `[T]` or `str` pointer/reference
`.aggregate 0 [.ptr p ptrBytes, .scalar ⟨len, ptrBytes⟩]`. -/
@[reducible]
def annealWidePtrVal (p : ProvenancePtr) (len : Nat) (ptrBytes : Nat := 8) : MirSemantics.Value :=
  .aggregate 0 [.ptr p ptrBytes, .scalar ⟨len, ptrBytes⟩]

/-- Anneal runtime representation of a provenance-free (integer-address) wide `[T]` or `str`
pointer `.aggregate 0 [.scalar ⟨addr, ptrBytes⟩, .scalar ⟨len, ptrBytes⟩]`. -/
@[reducible]
def annealWideScalarPtrVal (addr len : Nat) (ptrBytes : Nat := 8) : MirSemantics.Value :=
  .aggregate 0 [.scalar ⟨addr, ptrBytes⟩, .scalar ⟨len, ptrBytes⟩]

/-- MiniRust (`BasicMemory`) wide slice/str pointer value
`Value::Ptr(thin.widen(Some(PointerMeta::ElementCount(len))))`. -/
@[reducible]
def mrWidePtrVal (thin : Ptr) (len : Int) : Val :=
  .Ptr (ThinPointer.widen thin (some (.ElementCount len)))

/-- Polymorphic MiniRust (`Machine<M>`) wide slice/str pointer value. -/
@[reducible]
def mrWidePtrValM {M : Type} [Gen.Memory M]
    (thin : ThinPointer (Gen.Memory.Provenance M)) (len : Int) : Gen.Value M :=
  .Ptr (ThinPointer.widen thin (some (.ElementCount len)))

/-- MiniRust 2-field tuple value `(Value::Ptr(thin.widen(None)), Value::Int(len))` matching
`PtrType::as_wide_pair` for `PointerMetaKind::ElementCount`. -/
@[reducible]
def mrWidePairTupleVal (thin : Ptr) (len : Int) : Val :=
  .Tuple [.Ptr (ThinPointer.widen thin none), .Int len]

/-- Polymorphic MiniRust 2-field tuple value `(Value::Ptr(thin.widen(None)), Value::Int(len))`
for `Machine<M>`. -/
@[reducible]
def mrWidePairTupleValM {M : Type} [Gen.Memory M]
    (thin : ThinPointer (Gen.Memory.Provenance M)) (len : Int) : Gen.Value M :=
  .Tuple [.Ptr (ThinPointer.widen thin none), .Int len]

/-- The 16-byte, 8-byte-aligned 2-field tuple type `[(0, *const ()), (8, usize)]` returned by
`PtrType.as_wide_pair` for any pointer type with `PointerMetaKind::ElementCount`. -/
@[reducible]
def mrWidePairTupleTy : Gen.Type :=
  .Tuple [(⟨0⟩, .Ptr (.Raw .None)), (x86_64.PTR_SIZE, .Int IntType.usize_ty)]
    ⟨⟨2 * x86_64.PTR_SIZE.bytes⟩, x86_64.PTR_ALIGN, none⟩ none

/-- MiniRust `PointeeInfo` for an unsized slice `[T]` (or `str` when `elemSize = ⟨1⟩`,
`elemAlign = ⟨1⟩`). -/
@[reducible]
def slicePointeeInfo (elemSize : LibSpecr.Size) (elemAlign : LibSpecr.Align)
    (freeze : Bool := true) : Gen.PointeeInfo :=
  { layout := .Slice elemSize elemAlign
    inhabited := true
    unsafe_cells := .Slice []
    freeze := freeze
    unpin := true }

/-- MiniRust reference pointer type `&[T]` / `&mut [T]` (or `&str` when `elemSize = ⟨1⟩`,
`elemAlign = ⟨1⟩`). -/
@[reducible]
def sliceRefPtrType (mutbl : MirAst.Mutability) (elemSize : LibSpecr.Size)
    (elemAlign : LibSpecr.Align) (freeze : Bool := true) : Gen.PtrType :=
  .Ref (translateMutbl mutbl) (slicePointeeInfo elemSize elemAlign freeze)

/-- Both raw wide slice pointers (`PtrType.Raw .ElementCount`) and safe slice references
(`sliceRefPtrType mutbl elemSize elemAlign freeze`) have `meta_kind = .ElementCount` and expand to
the exact same 16-byte `mrWidePairTupleTy` under `PtrType.as_wide_pair`. -/
theorem mrWideRawPtr_as_wide_pair_eq (mutbl : MirAst.Mutability) (elemSize : LibSpecr.Size)
    (elemAlign : LibSpecr.Align) (freeze : Bool) :
    PtrType.meta_kind (.Raw .ElementCount) = .ElementCount ∧
    PtrType.meta_kind (sliceRefPtrType mutbl elemSize elemAlign freeze) = .ElementCount ∧
    PtrType.as_wide_pair (.Raw .ElementCount) = some mrWidePairTupleTy ∧
    PtrType.as_wide_pair (sliceRefPtrType mutbl elemSize elemAlign freeze) =
      some mrWidePairTupleTy :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Every wide slice pointer type (`*const [T]`, `*mut [T]`, `*const str`, `&[T]`, `&mut [T]`,
`&str`) has `Type.layout = .ok (.Sized ⟨16⟩ ⟨8⟩)` in MiniRust, matching Anneal's `2 * 8 = 16`-byte
wide pointer representation on 64-bit targets (`layoutPointerBytes emptyLayoutTable = 8`), while
the `as_wide_pair` tuple `mrWidePairTupleTy` also has `Type.layout = .ok (.Sized ⟨16⟩ ⟨8⟩)`. -/
theorem mrWidePtr_type_layout_eq (mutbl : MirAst.Mutability) (elemSize : LibSpecr.Size)
    (elemAlign : LibSpecr.Align) (freeze : Bool) :
    Type.layout (.Ptr (.Raw .ElementCount)) = .ok (.Sized ⟨16⟩ ⟨8⟩) ∧
    Type.layout (.Ptr (sliceRefPtrType mutbl elemSize elemAlign freeze)) = .ok (.Sized ⟨16⟩ ⟨8⟩) ∧
    Type.layout mrWidePairTupleTy = .ok (.Sized ⟨16⟩ ⟨8⟩) ∧
    2 * layoutPointerBytes emptyLayoutTable = 16 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `Type.layout` on `Type.Slice`: for `u32` elements (`size = 4, align = 4`) and `u8` / `str`
elements (`size = 1, align = 1`), `Type.layout (.Slice ...)` returns `.ok (.Slice elemSize elemAlign)`,
which is unsized (`LayoutStrategy.is_sized = false`). -/
theorem mrSlice_type_layout_eq :
    let u8It : IntType := ⟨.Unsigned, ⟨1⟩⟩
    Type.layout (.Slice (.Int u32)) = .ok (.Slice ⟨4⟩ ⟨4⟩) ∧
    Type.layout (.Slice (.Int u8It)) = .ok (.Slice ⟨1⟩ ⟨1⟩) ∧
    LayoutStrategy.is_sized (.Slice ⟨4⟩ ⟨4⟩) = false ∧
    LayoutStrategy.is_sized (.Slice ⟨1⟩ ⟨1⟩) = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Representation-relation identity (`encodeWidePtr` vs. `encodePtr ++ encodeInt`)**:
`Type.encode (.Ptr (.Raw .ElementCount)) (mrWidePtrVal thin len)` (and `Type.encode` at any
`sliceRefPtrType`) equals `encodeWidePtr .ElementCount (ThinPointer.widen thin (some (.ElementCount len)))`,
which concatenates `encodePtr thin` (`8` bytes carrying `thin.provenance`) and
`Type.encodeInt IntType.usize_ty (.Int len)` (`8` bytes of little-endian `usize`), and decodes back
under `decodeWidePtr .ElementCount` and `Type.decode mrWidePairTupleTy`. -/
theorem encodeWidePtr_eq_encode_widePairTuple (thin : Ptr) (len : Int)
    (mutbl : MirAst.Mutability) (elemSize : LibSpecr.Size) (elemAlign : LibSpecr.Align)
    (freeze : Bool) :
    Type.encode (.Ptr (.Raw .ElementCount)) (mrWidePtrVal thin len) =
      encodeWidePtr .ElementCount (ThinPointer.widen thin (some (.ElementCount len))) ∧
    Type.encode (.Ptr (sliceRefPtrType mutbl elemSize elemAlign freeze))
        (mrWidePtrVal thin len) =
      encodeWidePtr .ElementCount (ThinPointer.widen thin (some (.ElementCount len))) ∧
    encodeWidePtr .ElementCount (ThinPointer.widen thin (some (.ElementCount len))) =
      (do
        let thinBytes ← encodePtr thin
        let metaBytes ← Type.encodeInt IntType.usize_ty (.Int len)
        pure (thinBytes ++ metaBytes)) :=
  ⟨rfl, rfl, rfl⟩

/-- **`checkPtrMetadata` correspondence with Anneal `usize` bounds (`scalarModulus 8 = 2^64`)**:
`checkPtrMetadata (some (.ElementCount (Int.ofNat len))) .ElementCount` succeeds in MiniRust iff
`len < scalarModulus 8` (`2^64`), and fails closed with `.error (.ub "Value::Int: invalid integer value")`
when `scalarModulus 8 ≤ len`; mismatched metadata/kind pairs fail closed with
`.error (.ub "Value::Ptr: invalid metadata")`. -/
theorem checkPtrMetadata_elementCount_iff_anneal_usize (len : Nat) :
    (checkPtrMetadata (some (.ElementCount (Int.ofNat len))) .ElementCount = .ok () ↔
      len < scalarModulus 8) ∧
    (scalarModulus 8 ≤ len →
      checkPtrMetadata (some (.ElementCount (Int.ofNat len))) .ElementCount =
        .error (.ub "Value::Int: invalid integer value")) ∧
    checkPtrMetadata none .ElementCount = .error (.ub "Value::Ptr: invalid metadata") ∧
    checkPtrMetadata (some (.ElementCount (Int.ofNat len))) .None =
      .error (.ub "Value::Ptr: invalid metadata") := by
  have hMod : (2 : Int) ^ (8 * x86_64.PTR_SIZE.bytes) = ((scalarModulus 8 : Nat) : Int) := by
    decide
  have hCanRep : IntType.can_represent IntType.usize_ty (Int.ofNat len) =
      decide (len < scalarModulus 8) := by
    unfold IntType.can_represent IntType.usize_ty inBounds Size.bits
    rw [hMod]
    have h1 : decide ((0 : Int) ≤ Int.ofNat len) = true :=
      decide_eq_true (Int.natCast_nonneg len)
    have h2 : decide (Int.ofNat len < ((scalarModulus 8 : Nat) : Int)) =
        decide (len < scalarModulus 8) := by
      change decide ((len : Int) < ((scalarModulus 8 : Nat) : Int)) = decide (len < scalarModulus 8)
      by_cases h : len < scalarModulus 8
      · rw [decide_eq_true h]
        exact decide_eq_true (by omega)
      · rw [decide_eq_false h]
        exact decide_eq_false (by omega)
    rw [h1, h2, Bool.true_and]
  refine ⟨?_, ?_, rfl, rfl⟩
  · unfold checkPtrMetadata ensureElseUb
    dsimp only
    rw [hCanRep]
    by_cases hLt : len < scalarModulus 8
    · simp [hLt]
    · simp [hLt, ub]
  · intro hGe
    have hNotLt : ¬ len < scalarModulus 8 := Nat.not_lt.mpr hGe
    unfold checkPtrMetadata ensureElseUb
    dsimp only
    rw [hCanRep, decide_eq_false hNotLt]
    rfl

/-! ## 2. Symbolic Lockstep Correspondence: `UnOp.ptrMetadata`, `AggregateKind.rawPtr` & `to_raw_parts` -/

/-- **`UnOp.ptrMetadata` symbolic lockstep (`ptrMetadata_wide_and_thin_lockstep`)**:
1. On any wide `[T]` or `str` pointer (`annealWidePtrVal p len 8` and `mrWidePtrVal thin (Int.ofNat len)`),
   Anneal's `evalRvalue locals (.unaryOp .ptrMetadata op) mem localDecls emptyLayoutTable` returns
   `.ok (.scalar ⟨len, 8⟩) locals' mem` and MiniRust's `PointerMetaKind.encode_as_value .ElementCount`
   returns `.ok (.Int (Int.ofNat len))` — without inspecting `mem.borrows` or `mem.globals`!
2. On a provenance-free scalar-address wide pointer (`annealWideScalarPtrVal addr len 8`,
   `len < scalarModulus 8`), Anneal's `evalRvalue` returns `.ok (.scalar ⟨len, 8⟩) locals' mem` and
   MiniRust returns `.ok (.Int (Int.ofNat len))`.
3. On a thin pointer (`.ptr p 8` and `ThinPointer.widen thin none`), Anneal returns
   `.ok .unit locals' mem` and MiniRust returns `.ok (.Tuple [])` (`unit_value()`). -/
theorem ptrMetadata_wide_and_thin_lockstep
    (locals locals' : List LocalSlot) (wideOp scalarWideOp thinOp : Operand)
    (mem : MirSemantics.Memory) (localDecls : List LocalDecl)
    (p : ProvenancePtr) (thin : Ptr) (addr len : Nat)
    (hWideOp : evalOperand locals wideOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (annealWidePtrVal p len 8) locals')
    (hScalarTy : isNonWidePtrAggregateTy (operandTy localDecls emptyLayoutTable scalarWideOp) =
      false)
    (hLen : len < scalarModulus 8)
    (hScalarOp : evalOperand locals scalarWideOp mem.borrows mem.globals emptyLayoutTable
      mem.callerLocals localDecls mem.callStack = .ok (annealWideScalarPtrVal addr len 8) locals')
    (hThinOp : evalOperand locals thinOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (.ptr p 8) locals') :
    (evalRvalue locals (.unaryOp .ptrMetadata wideOp) mem localDecls emptyLayoutTable =
       .ok (.scalar ⟨len, 8⟩) locals' mem ∧
     PointerMetaKind.encode_as_value .ElementCount
         (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len)))).metadata =
       .ok (.Int (Int.ofNat len))) ∧
    (evalRvalue locals (.unaryOp .ptrMetadata scalarWideOp) mem localDecls emptyLayoutTable =
       .ok (.scalar ⟨len, 8⟩) locals' mem ∧
     PointerMetaKind.encode_as_value .ElementCount (some (.ElementCount (Int.ofNat len))) =
       .ok (.Int (Int.ofNat len))) ∧
    (evalRvalue locals (.unaryOp .ptrMetadata thinOp) mem localDecls emptyLayoutTable =
       .ok .unit locals' mem ∧
     PointerMetaKind.encode_as_value .None none = .ok (.Tuple [])) := by
  have hWrap : wrapScalarBits len (scalarModulus 8) = len := by
    unfold wrapScalarBits
    cases hb : Nat.ble (scalarModulus 8) len with
    | false => rfl
    | true => exact False.elim (Nat.not_le.mpr hLen (Nat.le_of_ble_eq_true hb))
  refine ⟨⟨?_, rfl⟩, ⟨?_, rfl⟩, ⟨?_, rfl⟩⟩
  · show evalUnaryPtrMetadata locals wideOp mem localDecls emptyLayoutTable = _
    unfold evalUnaryPtrMetadata
    simp only [hWideOp, annealWidePtrVal, layoutPointerBytes, emptyLayoutTable, Nat.beq_refl,
      Bool.and_self]
  · show evalUnaryPtrMetadata locals scalarWideOp mem localDecls emptyLayoutTable = _
    unfold evalUnaryPtrMetadata
    simp only [hScalarOp, annealWideScalarPtrVal, hScalarTy, layoutPointerBytes, emptyLayoutTable,
      Nat.beq_refl, Bool.and_self, hWrap]
  · show evalUnaryPtrMetadata locals thinOp mem localDecls emptyLayoutTable = _
    unfold evalUnaryPtrMetadata
    simp only [hThinOp, layoutPointerBytes, emptyLayoutTable, Nat.beq_refl]

/-- **`Translate.translateRvalue` on `CastKind.ptrToPtr` for wide `[T]` and `str` raw pointers**:
- Casting a wide `.slice elem` (with `isMonoRigidTy elem = true`) or `.str` raw pointer local to
  any sized raw pointer (`rawPtrMetaOf thinCastTy = some .None`, e.g., `*const ()` or `*const T`)
  translates via `minimize` to `some (.UnOp .GetThinPointer (.Load (.Local (localName i))))`.
- Casting between wide `.slice elem` / `.str` raw pointer types (`rawPtrMetaOf wideCastTy =
  some .ElementCount`, e.g., `*const [T] as *mut [T]` or `*const str as *const [u8]`) translates to
  the identity `some (.Load (.Local (localName i)))`. -/
theorem translateRvalue_cast_ptrToPtr_wide_to_thin_and_wide
    (layouts : LayoutTable) (decls : List LocalDecl) (i : Nat) (d : LocalDecl)
    (thinCastTy wideCastTy : Ty)
    (hDecl : decls[i]? = some d)
    (hSrcMeta : rawPtrMetaOf d.ty = some .ElementCount)
    (hThinMeta : rawPtrMetaOf thinCastTy = some .None)
    (hWideMeta : rawPtrMetaOf wideCastTy = some .ElementCount) :
    translateRvalue layouts decls none (.cast .ptrToPtr (.copy (local_ i)) thinCastTy) =
      some (.UnOp .GetThinPointer (.Load (.Local (localName i)))) ∧
    translateRvalue layouts decls none (.cast .ptrToPtr (.copy (local_ i)) wideCastTy) =
      some (.Load (.Local (localName i))) := by
  have hOp : translateOperand decls (.copy (local_ i)) = some (.Load (.Local (localName i))) := by
    simp [translateOperand, translatePlace, local_, hDecl]
  have hOpMeta : operandRawPtrMeta decls (.copy (local_ i)) = some .ElementCount := by
    simp [operandRawPtrMeta, local_, hDecl, hSrcMeta]
  refine ⟨?_, ?_⟩
  · unfold translateRvalue
    simp [hOp, hOpMeta, hThinMeta]
  · unfold translateRvalue
    simp [hOp, hOpMeta, hWideMeta]

/-- **`to_raw_parts` (`CastKind.ptrToPtr` wide-to-thin & wide-to-wide) symbolic lockstep** across
Anneal, `Machine<BasicMemory>` (`BM`), and `Machine<TreeBorrowsMemory>` (`TBM`):
1. **Wide-to-thin (`p as *const U` $\leftrightarrow$ `UnOp.GetThinPointer`)**:
   - When `p` is global-backed (`lookupBorrow mem.borrows p.tag = none`), Anneal's
     `evalRvalue locals (.cast .ptrToPtr op thinTargetTy) mem localDecls emptyLayoutTable` returns
     `.ok (.ptr p 8) locals' mem`;
   - In MiniRust, `evalUnOp .GetThinPointer` on `BM` and `evalUnOpM .GetThinPointer` on `TBM` both
     return `.ok (.Ptr (ThinPointer.widen thin none), .Ptr (.Raw .None))`, preserving `thin.addr`
     and `thin.provenance` (`allocId` and Tree Borrows `tag`) identically!
2. **Wide-to-wide (`*const [T] as *mut [T]`, `*const str as *const [u8]`)**:
   - Anneal's `evalRvalue locals (.cast .ptrToPtr op wideTargetTy) mem localDecls emptyLayoutTable`
     returns `.ok (annealWidePtrVal p len 8) locals' mem` (for both global-backed and borrow-backed
     pointers!), matching MiniRust's identity translation on `mrWidePtrVal thin (Int.ofNat len)` and
     `mrWidePtrValM thinTB (Int.ofNat len)`. -/
theorem ptrToPtr_wide_to_thin_and_wide_to_wide_lockstep
    (locals locals' : List LocalSlot) (op : Operand) (thinTargetTy wideTargetTy : Ty)
    (mem : MirSemantics.Memory) (localDecls : List LocalDecl)
    (p : ProvenancePtr) (len : Nat) (thin : Ptr)
    (thinTB : ThinPointer TreeBorrowsProvenance) (ptrTy : PtrType)
    (hThin : isThinRawPtrTy thinTargetTy = true)
    (hNotThin : isThinRawPtrTy wideTargetTy = false)
    (hWide : wideRawPtrIsDyn? wideTargetTy = some false)
    (hOp : evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (annealWidePtrVal p len 8) locals') :
    ((lookupBorrow mem.borrows p.tag = none →
        evalRvalue locals (.cast .ptrToPtr op thinTargetTy) mem localDecls emptyLayoutTable =
          .ok (.ptr p 8) locals' mem) ∧
     evalUnOp .GetThinPointer (mrWidePtrVal thin (Int.ofNat len), .Ptr ptrTy) =
       .ok (.Ptr (ThinPointer.widen thin none), .Ptr (.Raw .None)) ∧
     evalUnOpM (M := TBM) .GetThinPointer (mrWidePtrValM thinTB (Int.ofNat len), .Ptr ptrTy) =
       .ok (.Ptr (ThinPointer.widen thinTB none), .Ptr (.Raw .None))) ∧
    evalRvalue locals (.cast .ptrToPtr op wideTargetTy) mem localDecls emptyLayoutTable =
      .ok (annealWidePtrVal p len 8) locals' mem := by
  refine ⟨⟨?_, rfl, rfl⟩, ?_⟩
  · intro hNoBorrow
    show evalCastPtrToPtr locals op thinTargetTy mem localDecls emptyLayoutTable = _
    unfold evalCastPtrToPtr
    simp only [hOp, annealWidePtrVal, layoutPointerBytes, emptyLayoutTable, Nat.beq_refl,
      Bool.and_self, hThin, hNoBorrow]
  · show evalCastPtrToPtr locals op wideTargetTy mem localDecls emptyLayoutTable = _
    unfold evalCastPtrToPtr
    simp only [hOp, annealWidePtrVal, layoutPointerBytes, emptyLayoutTable, Nat.beq_refl,
      Bool.and_self, hNotThin, hWide]

/-- **Borrow-backed `CastKind.ptrToPtr` (`alreadySubslice = true`) lockstep**: when a stack-borrow
wide slice pointer's `BorrowEntry` already ends with a `.subslice` covering `[0 .. length elems)` at
offset `0`, Anneal's `evalCastPtrToPtr` returns `.ok (.ptr p 8) locals' mem` with `mem` unchanged
(no fresh tag allocated), matching MiniRust's `evalUnOp .GetThinPointer` and `evalUnOpM .GetThinPointer`
returning `ThinPointer.widen thin none` with the exact same borrow provenance tag! -/
theorem ptrToPtr_wide_to_thin_already_subslice_lockstep
    (locals locals' : List LocalSlot) (op : Operand) (thinTargetTy : Ty)
    (mem : MirSemantics.Memory) (localDecls : List LocalDecl)
    (p : ProvenancePtr) (len : Nat) (parentEntry : BorrowEntry) (rootVal : MirSemantics.Value)
    (containerProj : List ProjectionElem) (baseIdx : Nat) (elems : List MirSemantics.Value)
    (rawElemOffset : Nat) (thin : Ptr) (thinTB : ThinPointer TreeBorrowsProvenance)
    (ptrTy : PtrType)
    (hThin : isThinRawPtrTy thinTargetTy = true)
    (hOp : evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (annealWidePtrVal p len 8) locals')
    (hBorrow : lookupBorrow mem.borrows p.tag = some parentEntry)
    (hPerm : parentEntry.perm ≠ .disabled)
    (hRoot : activeFrameSlot? locals' mem.callStack parentEntry.targetFrameDepth
      parentEntry.targetLocal = some (.init rootVal))
    (hRead : readSliceBackingAggregate? locals' rootVal
      (normalizeSubsliceProjections (stripTransparentProjections parentEntry.targetProjection))
      len = some (containerProj, baseIdx, elems))
    (hOff : byteOffsetToElemIdx? p.offsetBytes (inferElemListByteStride elems) =
      some rawElemOffset)
    (hBound : Nat.ble (Nat.add (Nat.add rawElemOffset baseIdx) len) (length elems) = true)
    (hAlready : Bool.and (endsWithSubslice containerProj)
      (Bool.and (Nat.beq (Nat.add rawElemOffset baseIdx) 0) (Nat.beq len (length elems))) =
        true) :
    evalRvalue locals (.cast .ptrToPtr op thinTargetTy) mem localDecls emptyLayoutTable =
      .ok (.ptr p 8) locals' mem ∧
    evalUnOp .GetThinPointer (mrWidePtrVal thin (Int.ofNat len), .Ptr ptrTy) =
      .ok (.Ptr (ThinPointer.widen thin none), .Ptr (.Raw .None)) ∧
    evalUnOpM (M := TBM) .GetThinPointer (mrWidePtrValM thinTB (Int.ofNat len), .Ptr ptrTy) =
      .ok (.Ptr (ThinPointer.widen thinTB none), .Ptr (.Raw .None)) := by
  refine ⟨?_, rfl, rfl⟩
  show evalCastPtrToPtr locals op thinTargetTy mem localDecls emptyLayoutTable = _
  unfold evalCastPtrToPtr
  simp only [hOp, annealWidePtrVal, layoutPointerBytes, emptyLayoutTable, Nat.beq_refl,
    Bool.and_self, hThin, hBorrow]
  unfold deriveStackElemThinPtr
  rcases parentEntry with ⟨tag, tLoc, tProj, perm, rOff, rLen, prot, pTag, tDepth, aDead⟩
  dsimp only at hPerm hRoot hRead ⊢
  cases perm
  all_goals first
    | exact absurd rfl hPerm
    | (simp only [hRoot, hRead, hOff, hBound, hAlready] <;> rfl)

/-- **`AggregateKind.rawPtr` (`ptr::from_raw_parts(_mut)` / `ptr::slice_from_raw_parts(_mut)`) &
`to_raw_parts` round-trip lockstep**:
Assembling `Rvalue.aggregate (.rawPtr pointeeTy mutability) [dataOp, metaOp]` for `.slice elemTy` or
`.str` (`wideAggregatePointeeIsDyn? pointeeTy = some false`) from `.ptr p 8` and `.scalar ⟨len, 8⟩`
yields `.ok (annealWidePtrVal p len 8) locals₂ mem`, and decomposing via `to_raw_parts` (either via
`CastKind.ptrToPtr` + `UnOp.ptrMetadata` or field projections `.field 0` + `.field 1`) and
reassembling via `AggregateKind.rawPtr` is the exact identity on `annealWidePtrVal p len 8`,
matching MiniRust's `ThinPointer.widen thin (some (.ElementCount (Int.ofNat len)))` round-trip with
`evalUnOp .GetThinPointer` and `PointerMetaKind.encode_as_value` on both `BM` and `TBM`! -/
theorem aggregate_rawPtr_and_to_raw_parts_roundtrip_lockstep
    (locals locals₁ locals₂ : List LocalSlot) (pointeeTy : Ty) (mutability : MirAst.Mutability)
    (dataOp metaOp : Operand) (mem : MirSemantics.Memory) (localDecls : List LocalDecl)
    (p : ProvenancePtr) (len : Nat) (thin : Ptr) (thinTB : ThinPointer TreeBorrowsProvenance)
    (hWide : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (hData : evalOperand locals dataOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (.ptr p 8) locals₁)
    (hMeta : evalOperand locals₁ metaOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (.scalar ⟨len, 8⟩) locals₂) :
    evalRvalue locals (.aggregate (.rawPtr pointeeTy mutability) [dataOp, metaOp]) mem localDecls
        emptyLayoutTable =
      .ok (annealWidePtrVal p len 8) locals₂ mem ∧
    (do
      let (thinVal, _) ← evalUnOp .GetThinPointer
        (mrWidePtrVal thin (Int.ofNat len), .Ptr (.Raw .ElementCount))
      let metaVal ← PointerMetaKind.encode_as_value .ElementCount
        (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len)))).metadata
      let decodedMeta ← PointerMetaKind.decode_value .ElementCount metaVal
      match thinVal with
      | .Ptr ⟨thin', none⟩ => pure (Value.Ptr (ThinPointer.widen thin' decodedMeta))
      | _ => specPanic "expected thin pointer") =
      .ok (mrWidePtrVal thin (Int.ofNat len)) ∧
    (do
      let (thinValTB, _) ← evalUnOpM (M := TBM) .GetThinPointer
        (mrWidePtrValM thinTB (Int.ofNat len), .Ptr (.Raw .ElementCount))
      match thinValTB with
      | .Ptr ⟨thinTB', none⟩ => pure (mrWidePtrValM thinTB' (Int.ofNat len))
      | _ => specPanic "expected thin pointer") =
      .ok (mrWidePtrValM thinTB (Int.ofNat len)) := by
  refine ⟨?_, rfl, rfl⟩
  show evalAggregateRawPtr locals pointeeTy [dataOp, metaOp] mem localDecls emptyLayoutTable = _
  unfold evalAggregateRawPtr evalOperands
  rw [hData]
  dsimp only [evalOperands]
  rw [hMeta]
  dsimp only [evalOperands]
  simp only [hWide, layoutPointerBytes, emptyLayoutTable, Nat.beq_refl, Bool.and_self,
    annealWidePtrVal]

/-! ## 3. Symbolic Lockstep Correspondence: `core::intrinsics::size_of_val` & `align_of_val` -/

private theorem nat_ble_eq_false_of_lt {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases hb : Nat.ble a b with
  | false => rfl
  | true => exact False.elim (Nat.not_le.mpr h (Nat.le_of_ble_eq_true hb))

private theorem nat_ble_eq_true_of_le : ∀ {a b : Nat}, a ≤ b → Nat.ble a b = true
  | 0, _, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | a + 1, b + 1, h => @nat_ble_eq_true_of_le a b (Nat.pred_le_pred h)

/-- **`size_of_val` and `align_of_val` symbolic lockstep on `.slice elemTy`
(`sizeOfVal_and_alignOfVal_slice_lockstep`)**:
For any slice element byte size `elemSz`, alignment `elemAlign`, and element count `len < scalarModulus 8`:
1. MiniRust's `LayoutStrategy.compute_size_and_align vtables (.Slice ⟨elemSz⟩ ⟨elemAlign⟩)
   (some (.ElementCount (Int.ofNat len)))` returns `.ok (⟨len * elemSz⟩, ⟨elemAlign⟩)`.
2. MiniRust's `x86_64.valid_size ⟨len * elemSz⟩` (`inBounds (len * elemSz) .Signed x86_64.PTR_SIZE`,
   checking `len * elemSz ≤ isize::MAX = 2^63 - 1`) equals `decide (len * elemSz < signedHalfModulus 8)`
   (`2^63`) — matching the boolean condition of Anneal's `evalSliceSizeOfVal elemSz ⟨len, 8⟩`.
   NOTE: MiniRust evaluates this bound only in `check_ptr` on *safe* pointers (`&[T]`) and in
   allocation; its `ComputeSize` / `ComputeAlign` (`computeSize` / `computeAlign`) are total and
   never consult it (`computeSize_computeAlign_slice_total`).
3. **Normal agreement (`len * elemSz < signedHalfModulus 8`)**:
   `x86_64.valid_size ⟨len * elemSz⟩ = true`, `evalSliceSizeOfVal elemSz ⟨len, 8⟩ = some ⟨len * elemSz, 8⟩`,
   Anneal's `evalNonSelectIntrinsicCall .sizeOfVal` writes `.scalar ⟨len * elemSz, 8⟩`, and
   Anneal's `evalNonSelectIntrinsicCall .alignOfVal` writes `.scalar ⟨elemAlign, 8⟩`.
4. **Overflow (`signedHalfModulus 8 ≤ len * elemSz`)**:
   `x86_64.valid_size ⟨len * elemSz⟩ = false`, `evalSliceSizeOfVal elemSz ⟨len, 8⟩ = none`, and
   BOTH Anneal's `evalNonSelectIntrinsicCall .sizeOfVal` and `evalNonSelectIntrinsicCall .alignOfVal`
   fault with `MirStepNode.fail .ub`. MiniRust raises the matching UB only when the wide pointer is
   (or is retagged as) a safe reference (`sliceSizeOverflow_minirust_ub_locus`); for raw pointers
   Anneal is strictly more restrictive (`div_rawSliceSizeOfVal_isizeMax_anneal_ub_vs_minirust_total`). -/
theorem sizeOfVal_and_alignOfVal_slice_lockstep
    (s : MachineState) (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : MirAst.Place) (targetBb : BasicBlockIdx)
    (elemTy : RigidTy) (elemSz elemAlign : Nat) (p : ProvenancePtr) (len : Nat)
    (vtables : Ptr → Interp VTable)
    (hPt : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps =
      some (.slice elemTy))
    (hSz : intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy = some elemSz)
    (hAlign : intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy = some elemAlign)
    (hLen : len < scalarModulus 8) :
    LayoutStrategy.compute_size_and_align vtables (.Slice ⟨elemSz⟩ ⟨elemAlign⟩)
        (some (.ElementCount (Int.ofNat len))) =
      .ok (⟨len * elemSz⟩, ⟨elemAlign⟩) ∧
    x86_64.valid_size ⟨len * elemSz⟩ = decide (len * elemSz < signedHalfModulus 8) ∧
    (len * elemSz < signedHalfModulus 8 →
      x86_64.valid_size ⟨len * elemSz⟩ = true ∧
      evalSliceSizeOfVal elemSz ⟨len, 8⟩ = some ⟨len * elemSz, 8⟩ ∧
      evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb =
        writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨len * elemSz, 8⟩) ∧
      evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb =
        writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨elemAlign, 8⟩)) ∧
    (signedHalfModulus 8 ≤ len * elemSz →
      x86_64.valid_size ⟨len * elemSz⟩ = false ∧
      evalSliceSizeOfVal elemSz ⟨len, 8⟩ = none ∧
      evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb = MirStepNode.fail .ub ∧
      evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb = MirStepNode.fail .ub) := by
  have hProdNonneg : (0 : Int) ≤ Int.ofNat len * (elemSz : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg len) (Int.natCast_nonneg elemSz)
  have hToNat : (Int.ofNat len * (elemSz : Int)).toNat = len * elemSz := rfl
  have hComp :
      LayoutStrategy.compute_size_and_align vtables (.Slice ⟨elemSz⟩ ⟨elemAlign⟩)
          (some (.ElementCount (Int.ofNat len))) =
        .ok (⟨len * elemSz⟩, ⟨elemAlign⟩) := by
    unfold LayoutStrategy.compute_size_and_align
    dsimp only
    rw [ite_eq_left_iff.mpr (fun h => absurd hProdNonneg h), hToNat]
    rfl
  have hHalf : (2 : Int) ^ (8 * x86_64.PTR_SIZE.bytes - 1) =
      ((signedHalfModulus 8 : Nat) : Int) := by
    decide
  have hValidEq :
      x86_64.valid_size ⟨len * elemSz⟩ = decide (len * elemSz < signedHalfModulus 8) := by
    unfold x86_64.valid_size inBounds Size.bits
    rw [hHalf]
    have h1 : decide (-((signedHalfModulus 8 : Nat) : Int) ≤ ((len * elemSz : Nat) : Int)) =
        true :=
      decide_eq_true (Int.le_trans (by decide : -((signedHalfModulus 8 : Nat) : Int) ≤ 0)
        (Int.natCast_nonneg (len * elemSz)))
    have h2 : decide (((len * elemSz : Nat) : Int) < ((signedHalfModulus 8 : Nat) : Int)) =
        decide (len * elemSz < signedHalfModulus 8) := by
      by_cases h : len * elemSz < signedHalfModulus 8
      · rw [decide_eq_true h]
        exact decide_eq_true (by omega)
      · rw [decide_eq_false h]
        exact decide_eq_false (by omega)
    rw [h1, h2, Bool.true_and]
  have hWrap : wrapScalarBits len (scalarModulus 8) = len := by
    unfold wrapScalarBits
    rw [nat_ble_eq_false_of_lt hLen]
  have hMulComm : Nat.mul elemSz len = len * elemSz := Nat.mul_comm elemSz len
  refine ⟨hComp, hValidEq, ?_, ?_⟩
  · intro hLt
    have hBle : Nat.ble (signedHalfModulus 8) ( len * elemSz ) = false :=
      nat_ble_eq_false_of_lt hLt
    have hEvSlice : evalSliceSizeOfVal elemSz ⟨len, 8⟩ = some ⟨len * elemSz, 8⟩ := by
      unfold evalSliceSizeOfVal
      simp only [Nat.beq_refl, hWrap, hMulComm, hBle]
    refine ⟨hValidEq.trans (decide_eq_true hLt), hEvSlice, ?_, ?_⟩
    · unfold evalNonSelectIntrinsicCall writeIntrinsicScalarResult
      simp only [annealWidePtrVal, hPt, Nat.beq_refl, hSz, hEvSlice]
    · unfold evalNonSelectIntrinsicCall writeIntrinsicScalarResult
      simp only [annealWidePtrVal, hPt, Nat.beq_refl, hSz, hEvSlice, hAlign]
  · intro hGe
    have hBleT : Nat.ble (signedHalfModulus 8) (len * elemSz) = true :=
      nat_ble_eq_true_of_le hGe
    have hEvNone : evalSliceSizeOfVal elemSz ⟨len, 8⟩ = none := by
      unfold evalSliceSizeOfVal
      simp only [Nat.beq_refl, hWrap, hMulComm, hBleT]
    refine ⟨hValidEq.trans (decide_eq_false (Nat.not_lt.mpr hGe)), hEvNone, ?_, ?_⟩
    · unfold evalNonSelectIntrinsicCall
      simp only [annealWidePtrVal, hPt, Nat.beq_refl, hSz, hEvNone]
    · unfold evalNonSelectIntrinsicCall
      simp only [annealWidePtrVal, hPt, Nat.beq_refl, hSz, hAlign, hEvNone]

/-- **`size_of_val` and `align_of_val` symbolic lockstep on `str`, empty slices (`len = 0`), and
ZST slices (`elemSz = 0`)**:
1. For `str` (`LayoutStrategy.Slice ⟨1⟩ ⟨1⟩`), `compute_size_and_align` returns `(⟨len⟩, ⟨1⟩)`;
   when `len < signedHalfModulus 8`, Anneal writes `len` for `size_of_val` and `1` for
   `align_of_val`, and when `signedHalfModulus 8 ≤ len` (`len < scalarModulus 8`), both fault `.ub`.
2. For an empty slice (`len = 0`), `0 * elemSz = 0 < signedHalfModulus 8` for every `elemSz`, so
   `evalSliceSizeOfVal elemSz ⟨0, 8⟩ = some ⟨0, 8⟩` and `compute_size_and_align` returns
   `(⟨0⟩, ⟨elemAlign⟩)`.
3. For a ZST slice (`elemSz = 0`), `len * 0 = 0 < signedHalfModulus 8` for every
   `len < scalarModulus 8` (even when `signedHalfModulus 8 ≤ len`!), so both Anneal and MiniRust
   succeed with byte size `0` and alignment `elemAlign`. -/
theorem sizeOfVal_and_alignOfVal_str_empty_zst_lockstep
    (s : MachineState) (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : MirAst.Place) (targetBb : BasicBlockIdx)
    (p : ProvenancePtr) (len elemSz elemAlign : Nat) (vtables : Ptr → Interp VTable)
    (hPtStr : resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = some .str)
    (hLen : len < scalarModulus 8) :
    LayoutStrategy.compute_size_and_align vtables (.Slice ⟨1⟩ ⟨1⟩)
        (some (.ElementCount (Int.ofNat len))) =
      .ok (⟨len⟩, ⟨1⟩) ∧
    (len < signedHalfModulus 8 →
      evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb =
        writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨len, 8⟩) ∧
      evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb =
        writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨1, 8⟩)) ∧
    (signedHalfModulus 8 ≤ len →
      evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb = MirStepNode.fail .ub ∧
      evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts argOps
          [annealWidePtrVal p len 8] locals' destination targetBb = MirStepNode.fail .ub) ∧
    (evalSliceSizeOfVal elemSz ⟨0, 8⟩ = some ⟨0, 8⟩ ∧
     LayoutStrategy.compute_size_and_align vtables (.Slice ⟨elemSz⟩ ⟨elemAlign⟩)
         (some (.ElementCount 0)) =
       .ok (⟨0⟩, ⟨elemAlign⟩)) ∧
    (evalSliceSizeOfVal 0 ⟨len, 8⟩ = some ⟨0, 8⟩ ∧
     LayoutStrategy.compute_size_and_align vtables (.Slice ⟨0⟩ ⟨elemAlign⟩)
         (some (.ElementCount (Int.ofNat len))) =
       .ok (⟨0⟩, ⟨elemAlign⟩)) := by
  have hWrap : wrapScalarBits len (scalarModulus 8) = len := by
    unfold wrapScalarBits
    cases hb : Nat.ble (scalarModulus 8) len with
    | false => rfl
    | true => exact False.elim (Nat.not_le.mpr hLen (Nat.le_of_ble_eq_true hb))
  have hCompStr :
      LayoutStrategy.compute_size_and_align vtables (.Slice ⟨1⟩ ⟨1⟩)
          (some (.ElementCount (Int.ofNat len))) =
        .ok (⟨len⟩, ⟨1⟩) := by
    unfold LayoutStrategy.compute_size_and_align
    dsimp only
    have hPos : (0 : Int) ≤ Int.ofNat len * ((1 : Nat) : Int) :=
      Int.mul_nonneg (Int.natCast_nonneg len) (Int.natCast_nonneg 1)
    have hToNat1 : (Int.ofNat len * ((1 : Nat) : Int)).toNat = len := Nat.mul_one len
    rw [ite_eq_left_iff.mpr (fun h => absurd hPos h), hToNat1]
    rfl
  have hCompZst :
      LayoutStrategy.compute_size_and_align vtables (.Slice ⟨0⟩ ⟨elemAlign⟩)
          (some (.ElementCount (Int.ofNat len))) =
        .ok (⟨0⟩, ⟨elemAlign⟩) := by
    unfold LayoutStrategy.compute_size_and_align
    simp [Pure.pure, Except.pure]
  have hMulZero : Nat.mul 0 len = 0 := Nat.zero_mul len
  have hZstSlice : evalSliceSizeOfVal 0 ⟨len, 8⟩ = some ⟨0, 8⟩ := by
    unfold evalSliceSizeOfVal
    simp only [Nat.beq_refl, hWrap, hMulZero]
    rfl
  have hCompEmpty :
      LayoutStrategy.compute_size_and_align vtables (.Slice ⟨elemSz⟩ ⟨elemAlign⟩)
          (some (.ElementCount 0)) =
        .ok (⟨0⟩, ⟨elemAlign⟩) := by
    unfold LayoutStrategy.compute_size_and_align
    simp [Pure.pure, Except.pure]
  have hMulOne : Nat.mul 1 len = len := Nat.one_mul len
  refine ⟨hCompStr, ?_, ?_, ⟨rfl, hCompEmpty⟩, ⟨hZstSlice, hCompZst⟩⟩
  · intro hLt
    have hBle : Nat.ble (signedHalfModulus 8) len = false := nat_ble_eq_false_of_lt hLt
    have hEvStr : evalSliceSizeOfVal 1 ⟨len, 8⟩ = some ⟨len, 8⟩ := by
      unfold evalSliceSizeOfVal
      simp only [Nat.beq_refl, hWrap, hMulOne, hBle]
    refine ⟨?_, ?_⟩
    · unfold evalNonSelectIntrinsicCall writeIntrinsicScalarResult
      simp only [annealWidePtrVal, hPtStr, Nat.beq_refl, hEvStr]
    · unfold evalNonSelectIntrinsicCall writeIntrinsicScalarResult
      simp only [annealWidePtrVal, hPtStr, Nat.beq_refl, hEvStr]
  · intro hGe
    have hBleT : Nat.ble (signedHalfModulus 8) len = true := nat_ble_eq_true_of_le hGe
    have hEvNone : evalSliceSizeOfVal 1 ⟨len, 8⟩ = none := by
      unfold evalSliceSizeOfVal
      simp only [Nat.beq_refl, hWrap, hMulOne, hBleT]
    refine ⟨?_, ?_⟩
    · unfold evalNonSelectIntrinsicCall
      simp only [annealWidePtrVal, hPtStr, Nat.beq_refl, hEvNone]
    · unfold evalNonSelectIntrinsicCall
      simp only [annealWidePtrVal, hPtStr, Nat.beq_refl, hEvNone]

/-! ## 4. Symbolic & Concrete `slice::from_raw_parts(_mut)`, `Rvalue.len (*s)`, Checked Indexing & Tree Borrows -/

/-- **Symbolic `Rvalue.len (*place)` on a `.disabled` wide slice pointer vs. `UnOp.ptrMetadata`**:
When `entry.perm = .disabled`, `evalRvalue locals (.len place)` faults with `.ub`, whereas
`evalRvalue locals (.unaryOp .ptrMetadata ptrOp)` STILL succeeds with
`.ok (.scalar ⟨len, 8⟩) locals' mem`! -/
theorem evalRvalue_len_wide_slice_borrow_and_disabled_contrast
    (locals locals' : List LocalSlot) (place : MirAst.Place) (ptrOp : Operand)
    (mem : MirSemantics.Memory) (localDecls : List LocalDecl)
    (initProj : List ProjectionElem) (elem : RigidTy) (lIdx : LayoutIdx)
    (entry : BorrowEntry) (p : ProvenancePtr) (len : Nat)
    (hTy : placeTy localDecls emptyLayoutTable place =
      some { kind := .slice elem, layoutIdx := lIdx })
    (hSplit : splitLastDeref? place.projection = some initProj)
    (hRead : evalPlaceRead locals { local_ := place.local_, projection := initProj } mem.borrows
      mem.globals emptyLayoutTable mem.callerLocals localDecls mem.callStack =
        .ok (annealWidePtrVal p len 8) locals')
    (hOp : evalOperand locals ptrOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (annealWidePtrVal p len 8) locals')
    (hBorrow : lookupBorrow mem.borrows p.tag = some entry)
    (hDis : entry.perm = .disabled) :
    evalRvalue locals (.len place) mem localDecls emptyLayoutTable = .ub ∧
    evalRvalue locals (.unaryOp .ptrMetadata ptrOp) mem localDecls emptyLayoutTable =
      .ok (.scalar ⟨len, 8⟩) locals' mem := by
  refine ⟨?_, ?_⟩
  · show evalPlaceLen locals place mem localDecls emptyLayoutTable = .ub
    unfold evalPlaceLen
    dsimp (config := { zeta := true }) only
    rw [hTy]
    dsimp only
    rw [hSplit]
    dsimp only
    rw [hRead]
    simp only [annealWidePtrVal, layoutPointerBytes, emptyLayoutTable, Nat.beq_refl, Bool.and_self,
      hBorrow, hDis]
    rfl
  · show evalUnaryPtrMetadata locals ptrOp mem localDecls emptyLayoutTable = _
    unfold evalUnaryPtrMetadata
    simp only [hOp, annealWidePtrVal, layoutPointerBytes, emptyLayoutTable, Nat.beq_refl,
      Bool.and_self]

theorem dropValues_eq_drop : ∀ (n : Nat) (xs : List MirSemantics.Value), dropValues n xs = xs.drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: xs => dropValues_eq_drop k xs

theorem takeValues_eq_take : ∀ (n : Nat) (xs : List MirSemantics.Value), takeValues n xs = xs.take n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => congrArg (x :: ·) (takeValues_eq_take k xs)

/-- **Symbolic borrow-backed `Rvalue.len (*s)` and `.frozen` mutable-reborrow UB lockstep**:
1. When `sIdx` holds a borrow-backed wide slice pointer (`lookupBorrow mem.borrows p.tag = some entry`,
   `entry.perm ≠ .disabled`):
   * In-bounds (`rawElemOffset + baseIdx + len ≤ elems.length`): Anneal's
     `evalRvalue locals (.len ⟨sIdx, [.deref]⟩)` returns `.ok (.scalar ⟨len, 8⟩) locals' mem`
     in lockstep with MiniRust `PointerMetaKind.encode_as_value .ElementCount (some (.ElementCount len)) = .ok (.Int len)`.
   * Out-of-bounds (`elems.length < rawElemOffset + baseIdx + len`): Anneal's
     `evalRvalue locals (.len ⟨sIdx, [.deref]⟩)` faults `.ub`.
2. When `entry.perm = .frozen`, mutable reborrowing `&mut (*s)` (`slice::from_raw_parts_mut`
   over a frozen parent borrow) faults `.ub` in Anneal (`evalRvalueRefDeref` → `evalSliceFatPtrDerefBorrow`). -/
theorem evalRvalue_len_and_frozen_mut_reborrow_wide_slice_lockstep
    (locals locals' : List LocalSlot) (mem : MirSemantics.Memory)
    (localDecls : List LocalDecl) (sIdx : Local) (elem : RigidTy) (lIdx : LayoutIdx)
    (entry : BorrowEntry) (rootVal : MirSemantics.Value)
    (containerProj : List ProjectionElem) (baseIdx rawElemOffset : Nat)
    (elems : List MirSemantics.Value) (p : ProvenancePtr) (len : Nat)
    (hTy : placeTy localDecls emptyLayoutTable ⟨sIdx, [.deref]⟩ =
      some { kind := .slice elem, layoutIdx := lIdx })
    (hRead : evalPlaceRead locals ⟨sIdx, []⟩ mem.borrows mem.globals emptyLayoutTable
      mem.callerLocals localDecls mem.callStack = .ok (annealWidePtrVal p len 8) locals')
    (hBorrow : lookupBorrow mem.borrows p.tag = some entry)
    (hSlot : activeFrameSlot? locals' mem.callStack entry.targetFrameDepth entry.targetLocal =
      some (.init rootVal))
    (hBacking : readSliceBackingAggregate? locals' rootVal entry.targetProjection len
      (tyByteSize localDecls emptyLayoutTable { kind := elem, layoutIdx := unresolvedLayoutIdx emptyLayoutTable }) =
      some (containerProj, baseIdx, elems))
    (hOff : byteOffsetToElemIdx? p.offsetBytes (inferElemListByteStride elems) = some rawElemOffset) :
    PointerMetaKind.encode_as_value .ElementCount (some (.ElementCount (Int.ofNat len))) =
      .ok (.Int (Int.ofNat len)) ∧
    (entry.perm ≠ .disabled → rawElemOffset + baseIdx + len ≤ elems.length →
      evalRvalue locals (.len ⟨sIdx, [.deref]⟩) mem localDecls emptyLayoutTable =
        .ok (.scalar ⟨len, 8⟩) locals' mem) ∧
    (entry.perm ≠ .disabled → elems.length < rawElemOffset + baseIdx + len →
      evalRvalue locals (.len ⟨sIdx, [.deref]⟩) mem localDecls emptyLayoutTable = .ub) ∧
    (entry.perm = .frozen →
      get? locals sIdx = some (.init (annealWidePtrVal p len 8)) →
      evalRvalue locals (.ref (.mut false) ⟨sIdx, [.deref]⟩) mem localDecls emptyLayoutTable =
        .ub) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro hNotDis hIn
    have hBle : Nat.ble (Nat.add (Nat.add rawElemOffset baseIdx) len) (length elems) = true := by
      change Nat.ble (rawElemOffset + baseIdx + len) elems.length = true
      rw [Nat.ble_eq]
      exact hIn
    cases hp : entry.perm <;>
      try exact False.elim (hNotDis hp)
    all_goals
      simp only [evalRvalue, evalPlaceLen, splitLastDeref?, annealWidePtrVal,
        layoutPointerBytes, emptyLayoutTable, hTy, hRead, hBorrow, hp, hSlot, hBacking, hOff,
        hBle, Nat.beq_refl, Bool.and_self]
  · intro hNotDis hOob
    have hBle : Nat.ble (Nat.add (Nat.add rawElemOffset baseIdx) len) (length elems) = false := by
      change Nat.ble (rawElemOffset + baseIdx + len) elems.length = false
      rw [Bool.eq_false_iff, Ne, Nat.ble_eq]
      omega
    cases hp : entry.perm <;>
      try exact False.elim (hNotDis hp)
    all_goals
      simp only [evalRvalue, evalPlaceLen, splitLastDeref?, annealWidePtrVal,
        layoutPointerBytes, emptyLayoutTable, hTy, hRead, hBorrow, hp, hSlot, hBacking, hOff,
        hBle, Nat.beq_refl, Bool.and_self, Bool.false_and, Bool.and_false]
  · intro hFrozen hSlSlot
    have hPtr8 : layoutPointerBytes emptyLayoutTable = 8 := rfl
    unfold annealWidePtrVal at hSlSlot
    unfold evalRvalue evalRvalueRefDeref
    dsimp (config := { zeta := true }) only
    rw [hSlSlot]
    simp only []
    generalize Bool.and _ _ = g
    cases g
    · rfl
    · simp only [evalSliceFatPtrDerefBorrow, hPtr8, Nat.beq_refl, Bool.and_self,
        stripTransparentProjections, resolveBorrowProjectionElems,
        normalizeSubsliceProjections, hBorrow, hFrozen]

/-- **Symbolic full borrow-backed wide-slice `(*s)[idx]` lockstep against MiniRust slice `Index`**:
Runs Anneal's real `evalPlaceRead locals ⟨sIdx, [.deref, .index idxLocal]⟩`
(`evalSliceFatPtrDerefRead` → `takeValues len (dropValues (rawElemOffset + baseIdx) elems)`
→ `readProjectedValue`) alongside MiniRust's `PlaceExpr.Index` slice bounds guard
(`MiniRustSpec/Interp.lean:3518`: `if idx < 0 ∨ idx ≥ count then ub "access to out-of-bounds index"`):
1. **Out-of-bounds (`len ≤ idx`)**: Anneal's `evalPlaceRead` faults `.ub` (proved directly
   from `len ≤ idx` with NO unlinked `get? = none` assumption, even when
   `rawElemOffset + baseIdx + idx < elems.length`!) AND MiniRust's slice index guard triggers
   `decide ((Int.ofNat idx) < 0 ∨ (Int.ofNat len) ≤ (Int.ofNat idx)) = true`.
2. **In-bounds (`idx < len`)**: Anneal's `evalPlaceRead` returns `.ok elemVal locals` where
   `get? elems (rawElemOffset + baseIdx + idx) = some elemVal` AND MiniRust's slice index guard
   passes (`decide ((Int.ofNat idx) < 0 ∨ (Int.ofNat len) ≤ (Int.ofNat idx)) = false`). -/
theorem evalPlaceRead_index_wide_slice_borrowBacked_lockstep
    (locals : List LocalSlot) (mem : MirSemantics.Memory)
    (localDecls : List LocalDecl) (sIdx idxLocal : Local)
    (elemKind : RigidTy) (lIdx : LayoutIdx)
    (p : ProvenancePtr) (len idx szIdx : Nat)
    (entry : BorrowEntry) (rootVal : MirSemantics.Value)
    (containerProj : List ProjectionElem) (baseIdx rawElemOffset : Nat)
    (elems : List MirSemantics.Value)
    (hPointeeTy : placeTyResolved localDecls emptyLayoutTable ⟨sIdx, [.deref]⟩ =
      some { kind := .slice elemKind, layoutIdx := lIdx })
    (hSlSlot : get? locals sIdx = some (.init (annealWidePtrVal p len 8)))
    (hAlignDeref : checkDerefAlign localDecls emptyLayoutTable
      (some { kind := .slice elemKind, layoutIdx := lIdx }) p.offsetBytes = true)
    (hBorrow : lookupBorrow mem.borrows p.tag = some entry)
    (hPerm : entry.perm ≠ .disabled)
    (hSlot : activeFrameSlot? locals mem.callStack entry.targetFrameDepth entry.targetLocal =
      some (.init rootVal))
    (hAlignTarget : checkTargetPlaceAlign localDecls emptyLayoutTable
      (some { kind := .slice elemKind, layoutIdx := lIdx })
      entry p (some rootVal) emptyLayoutTable localDecls = true)
    (hBacking : readSliceBackingAggregate? locals rootVal entry.targetProjection len
      (rigidTyKindByteSize elemKind) = some (containerProj, baseIdx, elems))
    (hOff : byteOffsetToElemIdx? p.offsetBytes
      ((rigidTyKindByteSize elemKind).getD (inferElemListByteStride elems)) = some rawElemOffset)
    (hInBacking : rawElemOffset + baseIdx + len ≤ elems.length)
    (hIdxSlot : get? locals idxLocal = some (.init (.scalar ⟨idx, szIdx⟩))) :
    -- (1) Out-of-bounds (`len ≤ idx`): Anneal `.ub` & MiniRust bounds guard triggers UB
    (len ≤ idx →
      evalPlaceRead locals ⟨sIdx, [.deref, .index idxLocal]⟩ mem.borrows mem.globals
        emptyLayoutTable mem.callerLocals localDecls mem.callStack = .ub ∧
      decide ((Int.ofNat idx) < 0 ∨ (Int.ofNat len) ≤ (Int.ofNat idx)) = true) ∧
    -- (2) In-bounds (`idx < len`): Anneal `.ok elemVal locals` & MiniRust bounds guard passes
    (∀ elemVal,
      idx < len →
      get? elems (rawElemOffset + baseIdx + idx) = some elemVal →
      validateValueForTy? emptyLayoutTable
        (placeTyResolved localDecls emptyLayoutTable ⟨sIdx, [.deref, .index idxLocal]⟩) elemVal = true →
      evalPlaceRead locals ⟨sIdx, [.deref, .index idxLocal]⟩ mem.borrows mem.globals
        emptyLayoutTable mem.callerLocals localDecls mem.callStack = .ok elemVal locals ∧
      decide ((Int.ofNat idx) < 0 ∨ (Int.ofNat len) ≤ (Int.ofNat idx)) = false) := by
  have hRemBle :
      Nat.ble len (length (dropValues (Nat.add rawElemOffset baseIdx) elems)) = true := by
    change Nat.ble len (dropValues (rawElemOffset + baseIdx) elems).length = true
    rw [dropValues_eq_drop, List.length_drop, Nat.ble_eq]
    omega
  constructor
  · intro hOob
    have hGetNone :
        get? (takeValues len (dropValues (Nat.add rawElemOffset baseIdx) elems)) idx = none := by
      change (takeValues len (dropValues (rawElemOffset + baseIdx) elems))[idx]? = none
      rw [takeValues_eq_take, dropValues_eq_drop, List.getElem?_eq_none]
      rw [List.length_take, List.length_drop]
      omega
    refine ⟨?_, decide_eq_true (Or.inr (Int.ofNat_le.mpr hOob))⟩
    have hPtr8 : layoutPointerBytes emptyLayoutTable = 8 := rfl
    cases hSzOpt : rigidTyKindByteSize elemKind <;>
      simp only [hSzOpt, Option.getD] at hOff hBacking
    all_goals
      cases hp : entry.perm <;>
        try exact False.elim (hPerm hp)
      all_goals
        simp only [evalPlaceRead, evalSliceFatPtrDerefRead, annealWidePtrVal, hPtr8,
          hSlSlot, hPointeeTy, hAlignDeref, hBorrow, hp, hSlot, hAlignTarget,
          hBacking, hSzOpt, hOff, hRemBle, readProjectedValue, hIdxSlot, hGetNone,
          Nat.beq_refl, Bool.and_self]
  · intro elemVal hLt hGetElem hValid
    have hGetSome :
        get? (takeValues len (dropValues (Nat.add rawElemOffset baseIdx) elems)) idx =
          some elemVal := by
      change (takeValues len (dropValues (rawElemOffset + baseIdx) elems))[idx]? = some elemVal
      rw [takeValues_eq_take, dropValues_eq_drop, List.getElem?_take_of_lt hLt,
        List.getElem?_drop]
      exact hGetElem
    have hMrOk : decide ((Int.ofNat idx) < 0 ∨ (Int.ofNat len) ≤ (Int.ofNat idx)) = false :=
      decide_eq_false (fun h =>
        h.elim
          (fun hneg => absurd hneg (Int.not_lt.mpr (Int.natCast_nonneg idx)))
          (fun hge => Nat.not_lt.mpr (Int.ofNat_le.mp hge) hLt))
    have hPtr8 : layoutPointerBytes emptyLayoutTable = 8 := rfl
    refine ⟨?_, hMrOk⟩
    cases hSzOpt : rigidTyKindByteSize elemKind <;>
      simp only [hSzOpt, Option.getD] at hOff hBacking
    all_goals
      cases hp : entry.perm <;>
        try exact False.elim (hPerm hp)
      all_goals
        simp only [evalPlaceRead, evalSliceFatPtrDerefRead, annealWidePtrVal, hPtr8,
          hSlSlot, hPointeeTy, hAlignDeref, hBorrow, hp, hSlot, hAlignTarget,
          hBacking, hSzOpt, hOff, hRemBle, readProjectedValue, hIdxSlot, hGetSome, hValid,
          Nat.beq_refl, Bool.and_self]

/-- **Symbolic null rejection vs. zero-byte (`len = 0` & ZST `elemSz = 0`) dangling acceptance on
safe wide slice references (`&[T]` / `&mut [T]`)**:
1. **Null wide safe reference (`addr = 0`)**: For ANY `len < scalarModulus 8` with
   `x86_64.valid_size ⟨len * elemSz⟩ = true` (including `len = 0` and ZST `elemSz = 0`!) and any
   `m : Option Mach`, MiniRust's `checkPtr` on `sliceRefPtrType mutbl ⟨elemSz⟩ ⟨elemAlign⟩ freeze`
   rejects `{ addr := 0, provenance := prov }` with `.error (.ub "Value::Ptr: null safe pointer")`;
   and in Anneal, `evalRvalue locals (.ref .shared ⟨sIdx, [.deref]⟩) emptyMemory localDecls
   emptyLayoutTable = .ub` both when `sIdx` holds the null `ProvenancePtr`
   `annealWidePtrVal { allocId := 0, offsetBytes := 0 } 0 8` (`Places.lean:16260-16262`) and when
   `sIdx` holds the provenance-free null `annealWideScalarPtrVal 0 0 8`.
2. **Non-null aligned zero-byte wide safe reference (`len = 0` or ZST `elemSz = 0`)**: For ANY
   `m : Option Mach` (`none` or `some mach`, exercising `CM.dereferenceable mach.mem thin ⟨0⟩ = .ok ()`),
   any in-bounds non-null aligned `thin` (including `thin.provenance = none`, i.e. `NonNull::dangling()`)
   passes `checkPtr` both at `len = 0` (arbitrary `elemSz`) and at ZST `elemSz = 0` (arbitrary
   `len < scalarModulus 8`). -/
theorem checkPtr_sliceRef_null_vs_dangling_zero_bytes_lockstep
    (thin : Ptr) (prov : Option Prov) (mutbl : MirAst.Mutability)
    (elemSz elemAlign len : Nat) (freeze : Bool) (m : Option Mach)
    (localsNullProv localsNullSc : List LocalSlot)
    (localDecls : List LocalDecl) (sIdx : Local)
    (hLen : len < scalarModulus 8)
    (hNullProvSlot :
      get? localsNullProv sIdx = some (.init (annealWidePtrVal { allocId := 0, offsetBytes := 0 } 0 8)))
    (hNullScSlot :
      get? localsNullSc sIdx = some (.init (annealWideScalarPtrVal 0 0 8))) :
    -- (1a) MiniRust `checkPtr` rejects `addr = 0` on `&[T]` / `&mut [T]` whenever `valid_size` holds
    (x86_64.valid_size ⟨len * elemSz⟩ = true →
      checkPtr (ThinPointer.widen { addr := 0, provenance := prov } (some (.ElementCount (Int.ofNat len))))
        (sliceRefPtrType mutbl ⟨elemSz⟩ ⟨elemAlign⟩ freeze) m =
        .error (.ub "Value::Ptr: null safe pointer")) ∧
    -- (1b) Anneal `evalRvalue (.ref .shared (*s))` rejects both null wide representations at `len = 0`
    evalRvalue localsNullProv (.ref .shared ⟨sIdx, [.deref]⟩) emptyMemory localDecls emptyLayoutTable = .ub ∧
    evalRvalue localsNullSc (.ref .shared ⟨sIdx, [.deref]⟩) emptyMemory localDecls emptyLayoutTable = .ub ∧
    -- (2) Non-null aligned zero-byte (`len = 0` or ZST `elemSz = 0`) passes `checkPtr` for any `m : Option Mach`
    (inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true →
      (thin.addr != 0) = true →
      Align.is_aligned ⟨elemAlign⟩ thin.addr = true →
      checkPtr (ThinPointer.widen thin (some (.ElementCount 0)))
        (sliceRefPtrType mutbl ⟨elemSz⟩ ⟨elemAlign⟩ freeze) m = .ok () ∧
      checkPtr (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len))))
        (sliceRefPtrType mutbl ⟨0⟩ ⟨elemAlign⟩ freeze) m = .ok ()) := by
  have hMetaLen :
      checkPtrMetadata (some (.ElementCount (Int.ofNat len))) .ElementCount = Except.ok () :=
    (checkPtrMetadata_elementCount_iff_anneal_usize len).1.mpr hLen
  have hMeta0 :
      checkPtrMetadata (some (.ElementCount 0)) .ElementCount = Except.ok () :=
    (checkPtrMetadata_elementCount_iff_anneal_usize 0).1.mpr (by decide)
  have hex_ok : ∀ {α β : Type} (x : α) (f : α → Except Stop β),
      (Bind.bind (Except.ok x) f) = f x := fun _ _ => rfl
  have hex_err : ∀ {α β : Type} (e : Stop) (f : α → Except Stop β),
      (Bind.bind (Except.error e) f) = Except.error e := fun _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hValidSz
    have hZeroInB :
        ensureElseUb (inBounds (0 : Int) .Unsigned x86_64.PTR_SIZE)
          "Value::Ptr: pointer out-of-bounds" = Except.ok () := by
      have h0 : inBounds (0 : Int) .Unsigned x86_64.PTR_SIZE = true := by decide
      unfold ensureElseUb; rw [h0]; rfl
    have hProdNonneg : (0 : Int) ≤ Int.ofNat len * (elemSz : Int) :=
      Int.mul_nonneg (Int.natCast_nonneg len) (Int.natCast_nonneg elemSz)
    have hToNat : (Int.ofNat len * (elemSz : Int)).toNat = len * elemSz := rfl
    have hComp : ∀ (lookup : Ptr → Interp VTable),
        LayoutStrategy.compute_size_and_align lookup (.Slice ⟨elemSz⟩ ⟨elemAlign⟩)
            (some (.ElementCount (Int.ofNat len))) =
          Except.ok (⟨len * elemSz⟩, ⟨elemAlign⟩) := by
      intro lookup
      unfold LayoutStrategy.compute_size_and_align
      dsimp only
      rw [ite_eq_left_iff.mpr (fun h => absurd hProdNonneg h), hToNat]
      rfl
    have hSzOk :
        ensureElseUb (inBounds ((len * elemSz : Nat) : Int) .Signed x86_64.PTR_SIZE)
          "Value::Ptr: total size exeeds isize::MAX" = Except.ok () := by
      have hInB : inBounds ((len * elemSz : Nat) : Int) .Signed x86_64.PTR_SIZE = true := hValidSz
      unfold ensureElseUb; rw [hInB]; rfl
    have hNullErr :
        ensureElseUb (((0 : Int) != 0)) "Value::Ptr: null safe pointer" =
          Except.error (.ub "Value::Ptr: null safe pointer") := rfl
    unfold checkPtr sliceRefPtrType ThinPointer.widen PtrType.meta_kind
      LayoutStrategy.meta_kind PtrType.safe_pointee
    dsimp only
    rw [hZeroInB, hex_ok, hMetaLen, hex_ok, hComp, hex_ok]
    dsimp only
    rw [hSzOk, hex_ok, hNullErr, hex_err]
  · have hPtr8 : layoutPointerBytes emptyLayoutTable = 8 := rfl
    unfold annealWidePtrVal at hNullProvSlot
    unfold evalRvalue evalRvalueRefDeref
    dsimp (config := { zeta := true }) only
    rw [hNullProvSlot]
    simp only []
    generalize Bool.and _ _ = g
    cases g
    · rfl
    · simp only [evalSliceFatPtrDerefBorrow, emptyMemory, lookupBorrow, lookupGlobalAlloc,
        hPtr8, Nat.beq_refl, Bool.and_self, Bool.not_true, Bool.and_false, Bool.false_and,
        stripTransparentProjections, resolveBorrowProjectionElems, normalizeSubsliceProjections]
  · unfold annealWideScalarPtrVal at hNullScSlot
    unfold evalRvalue evalRvalueRefDeref
    dsimp (config := { zeta := true }) only
    rw [hNullScSlot]
    rfl
  · intro hAddr hNonNull hAligned
    have hAddrOk :
        ensureElseUb (inBounds thin.addr .Unsigned x86_64.PTR_SIZE)
          "Value::Ptr: pointer out-of-bounds" = Except.ok () := by
      unfold ensureElseUb; rw [hAddr]; rfl
    have hSize0Ok :
        ensureElseUb (inBounds ((0 : Nat) : Int) .Signed x86_64.PTR_SIZE)
          "Value::Ptr: total size exeeds isize::MAX" = Except.ok () := by
      have hInB : inBounds ((0 : Nat) : Int) .Signed x86_64.PTR_SIZE = true := by decide
      unfold ensureElseUb; rw [hInB]; rfl
    have hNonNullOk :
        ensureElseUb (thin.addr != 0) "Value::Ptr: null safe pointer" = Except.ok () := by
      unfold ensureElseUb; rw [hNonNull]; rfl
    have hAlignOk :
        ensureElseUb (Align.is_aligned ⟨elemAlign⟩ thin.addr)
          "Value::Ptr: unaligned safe pointer" = Except.ok () := by
      unfold ensureElseUb; rw [hAligned]; rfl
    have hComp0 : ∀ (lookup : Ptr → Interp VTable),
        LayoutStrategy.compute_size_and_align lookup (.Slice ⟨elemSz⟩ ⟨elemAlign⟩)
            (some (.ElementCount 0)) =
          Except.ok (⟨0⟩, ⟨elemAlign⟩) := by
      intro lookup
      unfold LayoutStrategy.compute_size_and_align
      simp [Pure.pure, Except.pure]
    have hCompZst : ∀ (lookup : Ptr → Interp VTable),
        LayoutStrategy.compute_size_and_align lookup (.Slice ⟨0⟩ ⟨elemAlign⟩)
            (some (.ElementCount (Int.ofNat len))) =
          Except.ok (⟨0⟩, ⟨elemAlign⟩) := by
      intro lookup
      unfold LayoutStrategy.compute_size_and_align
      simp [Pure.pure, Except.pure]
    constructor
    · unfold checkPtr sliceRefPtrType ThinPointer.widen PtrType.meta_kind
        LayoutStrategy.meta_kind PtrType.safe_pointee
      dsimp only
      rw [hAddrOk, hex_ok, hMeta0, hex_ok, hComp0, hex_ok]
      dsimp only
      rw [hSize0Ok, hex_ok, hNonNullOk, hex_ok, hAlignOk, hex_ok]
      cases m <;> rfl
    · unfold checkPtr sliceRefPtrType ThinPointer.widen PtrType.meta_kind
        LayoutStrategy.meta_kind PtrType.safe_pointee
      dsimp only
      rw [hAddrOk, hex_ok, hMetaLen, hex_ok, hCompZst, hex_ok]
      dsimp only
      rw [hSize0Ok, hex_ok, hNonNullOk, hex_ok, hAlignOk, hex_ok]
      cases m <;> rfl

/-- **Symbolic wide-slice element `writeProjectedValue` and `fromEnd` subslice reborrow lockstep**:
1. **Element write (`(*s)[idx] = newVal` on sliced window `takeValues len (dropValues ... elems)`)**:
   * Out-of-bounds (`len ≤ idx`): `writeProjectedValue` faults `.ub` AND MiniRust's slice index
     bounds guard triggers (`decide ((Int.ofNat idx) < 0 ∨ (Int.ofNat len) ≤ (Int.ofNat idx)) = true`).
   * In-bounds (`idx < len`): `writeProjectedValue` updates index `idx` within the `len`-element
     slice window (`set?`) AND MiniRust's slice index bounds guard passes (`= false`).
2. **Borrow-backed `fromEnd` subslice reborrow (`&(*s)[fromIdx..toIdx]` with `fromEnd = true`)**:
   * Out-of-bounds (`len < fromIdx + toIdx`): `evalSliceFatPtrDerefBorrow` faults `.ub`.
   * In-bounds (`fromIdx + toIdx ≤ len`): `evalSliceFatPtrDerefBorrow` mints fresh tag
     `mem.nextTag` with subslice length `len - toIdx - fromIdx`. -/
theorem writeProjectedValue_and_subslice_reborrow_wide_slice_lockstep
    (locals : List LocalSlot) (mem : MirSemantics.Memory)
    (localDecls : List LocalDecl) (idxLocal : Local)
    (p : ProvenancePtr) (len idx szIdx fromIdx toIdx : Nat)
    (perm : TreeBorrowPerm) (isMut : Bool) (elemKind : RigidTy)
    (entry : BorrowEntry) (rootVal newVal : MirSemantics.Value)
    (containerProj : List ProjectionElem) (baseIdx rawElemOffset : Nat)
    (elems : List MirSemantics.Value)
    (hIdxSlot : get? locals idxLocal = some (.init (.scalar ⟨idx, szIdx⟩)))
    (hBorrow : lookupBorrow mem.borrows p.tag = some entry)
    (hPerm : perm ≠ .disabled)
    (hParentPerm : entry.perm = .active)
    (hSlot : activeFrameSlot? locals mem.callStack entry.targetFrameDepth entry.targetLocal =
      some (.init rootVal))
    (hBacking : readSliceBackingAggregate? locals rootVal entry.targetProjection len
      (tyByteSize .nil emptyLayoutTable { kind := elemKind, layoutIdx := 0 }) =
      some (containerProj, baseIdx, elems))
    (hOff : byteOffsetToElemIdx? p.offsetBytes (inferElemListByteStride elems) = some rawElemOffset)
    (hInBacking : rawElemOffset + baseIdx + len ≤ elems.length) :
    let window := takeValues len (dropValues (Nat.add rawElemOffset baseIdx) elems)
    let slicePointeeTy : Ty := { kind := .slice elemKind, layoutIdx := 0 }
    -- (1a) OOB index write (`len ≤ idx`) faults `.ub`
    (len ≤ idx →
      writeProjectedValue locals (.aggregate 0 window) [.index idxLocal] newVal = .ub ∧
      decide ((Int.ofNat idx) < 0 ∨ (Int.ofNat len) ≤ (Int.ofNat idx)) = true) ∧
    -- (1b) In-bounds index write (`idx < len`) updates `window` via `set?`
    (∀ oldElem updatedWindow,
      idx < len →
      get? window idx = some oldElem →
      set? window idx newVal = some updatedWindow →
      writeProjectedValue locals (.aggregate 0 window) [.index idxLocal] newVal =
        .ok (.aggregate 0 updatedWindow) ∧
      decide ((Int.ofNat idx) < 0 ∨ (Int.ofNat len) ≤ (Int.ofNat idx)) = false) ∧
    -- (2a) OOB `fromEnd = true` subslice reborrow (`len < fromIdx + toIdx`) faults `.ub`
    (len < fromIdx + toIdx →
      evalSliceFatPtrDerefBorrow locals mem p 8 ⟨len, 8⟩ [.subslice fromIdx toIdx true]
        perm isMut (some slicePointeeTy) emptyLayoutTable true localDecls none false = .ub) ∧
    -- (2b) In-bounds `fromEnd = true` subslice reborrow (`fromIdx + toIdx ≤ len`) mints `len - toIdx - fromIdx`
    (fromIdx + toIdx ≤ len →
      ∃ mem',
        evalSliceFatPtrDerefBorrow locals mem p 8 ⟨len, 8⟩ [.subslice fromIdx toIdx true]
          perm isMut (some slicePointeeTy) emptyLayoutTable true localDecls none false =
          .ok (annealWidePtrVal { allocId := mem.nextTag, offsetBytes := 0 }
                (len - toIdx - fromIdx) 8) locals mem' ∧
        mem'.nextTag = mem.nextTag + 1) := by
  intro window slicePointeeTy
  have hInBle : Nat.ble (Nat.add (Nat.add rawElemOffset baseIdx) len) elems.length = true := by
    change Nat.ble (rawElemOffset + baseIdx + len) elems.length = true
    rw [Nat.ble_eq]
    exact hInBacking
  have hLenSeq : length elems = elems.length := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hOob
    have hGetNone : get? window idx = none := by
      change (takeValues len (dropValues (rawElemOffset + baseIdx) elems))[idx]? = none
      rw [takeValues_eq_take, dropValues_eq_drop]
      exact List.getElem?_eq_none (by rw [List.length_take, List.length_drop]; omega)
    refine ⟨?_, decide_eq_true (Or.inr (Int.ofNat_le.mpr hOob))⟩
    simp only [writeProjectedValue, hIdxSlot, hGetNone]
  · intro oldElem updatedWindow hLt hGetSome hSetSome
    have hMrOk : decide ((Int.ofNat idx) < 0 ∨ (Int.ofNat len) ≤ (Int.ofNat idx)) = false :=
      decide_eq_false (fun h =>
        h.elim
          (fun hneg => absurd hneg (Int.not_lt.mpr (Int.natCast_nonneg idx)))
          (fun hge => Nat.not_lt.mpr (Int.ofNat_le.mp hge) hLt))
    refine ⟨?_, hMrOk⟩
    simp only [writeProjectedValue, hIdxSlot, hGetSome, hSetSome]
  · intro hSubOob
    have hPtr8 : layoutPointerBytes emptyLayoutTable = 8 := rfl
    have hLookup0 : LayoutTable.lookup emptyLayoutTable 0 = none := rfl
    have hUnres0 : unresolvedLayoutIdx emptyLayoutTable = 0 := rfl
    have hToOrFrom :
        Nat.ble toIdx len = false ∨
        (Nat.ble toIdx len = true ∧ Nat.ble fromIdx (Nat.sub len toIdx) = false) := by
      by_cases hTo : toIdx ≤ len
      · right
        refine ⟨Nat.ble_eq.mpr hTo, ?_⟩
        change Nat.ble fromIdx (len - toIdx) = false
        rw [Bool.eq_false_iff, Ne, Nat.ble_eq]
        omega
      · left
        rw [Bool.eq_false_iff, Ne, Nat.ble_eq]
        exact hTo
    unfold evalSliceFatPtrDerefBorrow
    dsimp (config := { zeta := true }) only [slicePointeeTy]
    cases isMut <;>
      (rcases hToOrFrom with hToF | ⟨hToT, hFromF⟩
       · simp only [hPtr8, hLenSeq, hLookup0, hUnres0, Nat.beq_refl, Bool.and_self,
           stripTransparentProjections, resolveBorrowProjectionElems,
           normalizeSubsliceProjections, normalizeSubsliceProjectionsAux,
           hBorrow, hParentPerm, hSlot, hBacking, hOff, hInBle, hToF]
       · simp only [hPtr8, hLenSeq, hLookup0, hUnres0, Nat.beq_refl, Bool.and_self,
           stripTransparentProjections, resolveBorrowProjectionElems,
           normalizeSubsliceProjections, normalizeSubsliceProjectionsAux,
           hBorrow, hParentPerm, hSlot, hBacking, hOff, hInBle, hToT, hFromF])
  · intro hSubIn
    have hPtr8 : layoutPointerBytes emptyLayoutTable = 8 := rfl
    have hLookup0 : LayoutTable.lookup emptyLayoutTable 0 = none := rfl
    have hUnres0 : unresolvedLayoutIdx emptyLayoutTable = 0 := rfl
    have hToBle : Nat.ble toIdx len = true := Nat.ble_eq.mpr (by omega)
    have hFromBle : Nat.ble fromIdx (Nat.sub len toIdx) = true := by
      change Nat.ble fromIdx (len - toIdx) = true
      rw [Nat.ble_eq]
      omega
    have hSubEq : Nat.sub (Nat.sub len toIdx) fromIdx = len - toIdx - fromIdx := rfl
    let _ := hPerm
    unfold evalSliceFatPtrDerefBorrow
    dsimp (config := { zeta := true }) only [slicePointeeTy]
    cases isMut <;>
    · simp only [hPtr8, hLenSeq, hLookup0, hUnres0, Nat.beq_refl, Bool.and_self,
        stripTransparentProjections, resolveBorrowProjectionElems,
        normalizeSubsliceProjections, normalizeSubsliceProjectionsAux,
        hBorrow, hParentPerm, hSlot, hBacking, hOff, hInBle, hToBle, hFromBle, hSubEq,
        annealWidePtrVal]
      exact ⟨_, rfl, rfl⟩

/-! ## 5. Concrete Multi-Way Execution Witnesses & Negative/Divergence Canaries -/

/-- `u32` array `[u32; 4]` MIR type and declaration. -/
def arrU32_4Ty : Ty := { kind := .array (.uint .u32) 4, layoutIdx := 0 }
def arrU32_4Decl : LocalDecl := { mutability := .mut, ty := arrU32_4Ty, debugName := some "arr" }

/-- Raw wide slice pointer `*const [u32]` and `*mut [u32]` MIR types and declarations. -/
def rawConstSliceU32Ty : Ty := { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 0 }
def rawMutSliceU32Ty : Ty := { kind := .rawPtr .mut (.slice (.uint .u32)), layoutIdx := 0 }
def rawConstSliceU8Ty : Ty := { kind := .rawPtr .not (.slice (.uint .u8)), layoutIdx := 0 }
def rawConstStrTy : Ty := { kind := .rawPtr .not .str, layoutIdx := 0 }
def rawConstUnitTy : Ty := { kind := .rawPtr .not (.tuple []), layoutIdx := 0 }
def usizeMirTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
def sliceU32PointeeTy : Ty := { kind := .slice (.uint .u32), layoutIdx := 0 }
def strPointeeMirTy : Ty := { kind := .str, layoutIdx := 0 }

def rawConstSliceU32Decl : LocalDecl :=
  { mutability := .mut, ty := rawConstSliceU32Ty, debugName := some "const_sl" }
def rawMutSliceU32Decl : LocalDecl :=
  { mutability := .mut, ty := rawMutSliceU32Ty, debugName := some "mut_sl" }
def rawConstUnitDecl : LocalDecl :=
  { mutability := .mut, ty := rawConstUnitTy, debugName := some "data_ptr" }
def usizeMirDecl : LocalDecl :=
  { mutability := .mut, ty := usizeMirTy, debugName := some "len_usize" }

def constUsize (n : Nat) : Operand :=
  .constant { ty := usizeMirTy, val := .scalar (.int ⟨n, 8⟩) }

/-- Extract the stop reason (`Option Stop`, which has `DecidableEq`) after `n` `Mach` steps. -/
def stopAfterM (m : Mach) (n : Nat) : Option Stop :=
  match Interp.steps n m with
  | .error e => some e
  | .ok _ => none

/-- Extract the stop reason (`Option Stop`, which has `DecidableEq`) after `n` `MachTB` steps. -/
def stopAfterTB (m : MachTB) (n : Nat) : Option Stop :=
  match Interp.stepsTB n m with
  | .error e => some e
  | .ok _ => none

/-- **Witness 1 (`wideSliceFromRawPartsMetadataRoundTrip_three_way`)**:
Concrete 3-way witness across Anneal (`mirTree`), MiniRust `Machine<BasicMemory>` (`Mach`), and
MiniRust `Machine<TreeBorrowsMemory>` (`MachTB`) for:
1. Initializing `_2 : [u32; 4] = [_1, 20, 30, 40]` (`_1 = 42`) and taking a raw element pointer
   `_3 = &raw mut (_2[0])`,
2. Assembling a wide raw slice pointer `_4 = ptr::slice_from_raw_parts_mut(_3, 4)`
   (`AggregateKind.rawPtr` in Anneal; `Transmute` from `mrWidePairTupleTy` to
   `Type.Ptr (.Raw .ElementCount)` in MiniRust),
3. Casting wide-to-wide `_5 = _4 as *const [u32]` (`CastKind.ptrToPtr` $\mapsto$ identity),
4. Decomposing via `to_raw_parts`: `_6 = _5 as *const ()` (`CastKind.ptrToPtr` $\mapsto$
   `UnOp.GetThinPointer`) and `_7 = PtrMetadata(_5)`,
5. Reassembling `_8 = ptr::slice_from_raw_parts(_6, _7)` and reading `(*_8)[0] + (_7 as u32) = 42 + 4 = 46`! -/
def wideRawPartsMir : CapturedMir :=
  ptrBody "witness::wide_raw_parts_round_trip"
    [u32Decl, u32Decl, arrU32_4Decl, ptrMutU32Decl, rawMutSliceU32Decl, rawConstSliceU32Decl,
     rawConstUnitDecl, usizeMirDecl, rawConstSliceU32Decl, usizeMirDecl, u32Decl, u32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .storageLive 6, .storageLive 7, .storageLive 8, .storageLive 9,
     .storageLive 10, .storageLive 11,
     .assign (local_ 2)
       (.aggregate (.array u32Ty) [.copy (local_ 1), constU32 20, constU32 30, constU32 40]),
     .assign (local_ 3)
       (.rawPtr .mut { local_ := 2, projection := [.constantIndex 0 4 false] }),
     .assign (local_ 4)
       (.aggregate (.rawPtr sliceU32PointeeTy .mut)
         [.copy (local_ 3), constUsize 4]),
     .assign (local_ 5) (.cast .ptrToPtr (.copy (local_ 4)) rawConstSliceU32Ty),
     .assign (local_ 6) (.cast .ptrToPtr (.copy (local_ 5)) rawConstUnitTy),
     .assign (local_ 7) (.unaryOp .ptrMetadata (.copy (local_ 5))),
     .assign (local_ 8)
       (.aggregate (.rawPtr sliceU32PointeeTy .not)
         [.copy (local_ 6), .copy (local_ 7)]),
     .assign (local_ 9) (.use (constUsize 0)),
     .assign (local_ 10)
       (.use (.copy { local_ := 8, projection := [.deref, .index 9] })),
     .assign (local_ 11) (.cast .intToInt (.copy (local_ 7)) u32Ty),
     .assign (local_ 0) (.binaryOp .add (.copy (local_ 10)) (.copy (local_ 11)))]

def wideRawPartsFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, .Array (.Int u32) 4),
    (localName 3, .Ptr (.Raw .None)),
    (localName 4, .Ptr (.Raw .ElementCount)),
    (localName 5, .Ptr (.Raw .ElementCount)),
    (localName 6, .Ptr (.Raw .None)),
    (localName 7, .Int IntType.usize_ty),
    (localName 8, .Ptr (sliceRefPtrType .not ⟨4⟩ ⟨4⟩)),
    (localName 9, .Int IntType.usize_ty),
    (localName 10, .Int u32),
    (localName 11, .Int u32),
    (localName 12, mrWidePairTupleTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3), .StorageLive (localName 4),
      .StorageLive (localName 5), .StorageLive (localName 6), .StorageLive (localName 7),
      .StorageLive (localName 8), .StorageLive (localName 9), .StorageLive (localName 10),
      .StorageLive (localName 11), .StorageLive (localName 12),
      .Assign (.Local (localName 2))
        (.Tuple [.Load (.Local (localName 1)), .Constant (.Int 20) (.Int u32),
                 .Constant (.Int 30) (.Int u32), .Constant (.Int 40) (.Int u32)]
          (.Array (.Int u32) 4)),
      .Assign (.Local (localName 3)) (.AddrOf (.Local (localName 2)) (.Raw .None)),
      .Assign (.Local (localName 4))
        (.UnOp (.Cast (.Transmute (.Ptr (.Raw .ElementCount))))
          (.Tuple [.Load (.Local (localName 3)), .Constant (.Int 4) (.Int IntType.usize_ty)]
            mrWidePairTupleTy)),
      .Assign (.Local (localName 5)) (.Load (.Local (localName 4))),
      .Assign (.Local (localName 6)) (.UnOp .GetThinPointer (.Load (.Local (localName 5)))),
      .Assign (.Local (localName 12))
        (.UnOp (.Cast (.Transmute mrWidePairTupleTy)) (.Load (.Local (localName 5)))),
      .Assign (.Local (localName 7)) (.Load (.Field (.Local (localName 12)) 1)),
      .Assign (.Local (localName 8))
        (.UnOp (.Cast (.Transmute (.Ptr (sliceRefPtrType .not ⟨4⟩ ⟨4⟩))))
          (.Tuple [.Load (.Local (localName 6)), .Load (.Local (localName 7))]
            mrWidePairTupleTy)),
      .Assign (.Local (localName 9)) (.Constant (.Int 0) (.Int IntType.usize_ty)),
      .Assign (.Local (localName 10))
        (.Load (.Index (.Deref (.Load (.Local (localName 8))) (.Slice (.Int u32)))
          (.Load (.Local (localName 9))))),
      .Assign (.Local (localName 11)) (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 7)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 10))) (.Load (.Local (localName 11))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

def wideRawPartsS0 : MachineState := initMachineState wideRawPartsMir [.scalar ⟨42, 4⟩]
def wideRawPartsMInit : Mach :=
  machine wideRawPartsMir wideRawPartsFn wideRawPartsS0.frame.locals wideRawPartsFn.start
def wideRawPartsTBInit : MachTB := liftMachToTB wideRawPartsMInit

/-- **Three-way lockstep agreement (`wideSliceFromRawPartsMetadataRoundTrip_three_way`)**:
Anneal (`mirTree`), MiniRust `Machine<BasicMemory>` (`Interp.steps 25`), and MiniRust
`Machine<TreeBorrowsMemory>` (`Interp.stepsTB 25`) all execute the wide-slice
`from_raw_parts` $\rightarrow$ `PtrToPtr` wide-to-wide $\rightarrow$ `to_raw_parts`
(`PtrToPtr` wide-to-thin / `GetThinPointer` + `PtrMetadata`) $\rightarrow$ `from_raw_parts`
round-trip and return `42 + 4 = 46` without UB! -/
theorem wideSliceFromRawPartsMetadataRoundTrip_three_way :
    (∃ mem, ReachesRet (mirTree wideRawPartsMir wideRawPartsS0) []
      (.normal (.scalar ⟨46, 4⟩, mem))) ∧
    MirNoUBTree (mirTree wideRawPartsMir wideRawPartsS0) ∧
    (Interp.steps 25 wideRawPartsMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 46 }, [1]) ∧
    (Interp.stepsTB 25 wideRawPartsTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 46 := by
  refine ⟨⟨_, runA_sound wideRawPartsMir 40 _ _ _ rfl⟩,
    runA_noUB wideRawPartsMir 40 _ _ _ rfl,
    by decide +kernel,
    by decide +kernel⟩

/-- **Witness 2 (`wideSliceIndexReadWriteAndOobUb_three_way`)**:
Concrete 3-way witness for `slice::from_raw_parts_mut` (`&mut *ptr::slice_from_raw_parts_mut`):
1. Initializes `[u32; 4] = [10, 20, 30, 40]`,
2. Forms a wide mutable slice pointer (`len = 4`),
3. Reads element `(*s)[2] = 30`, writes `(*s)[1] = 99`, reads `(*s)[1] = 99` and `Rvalue.len(*s) = 4`,
   and returns `30 + 99 + 4 = 133` across Anneal, `Mach`, and `MachTB`!
4. Out-of-bounds index `(*s)[4]` (`idx = 4 ≥ len = 4`) faults with `.ub` in Anneal and
   `some (.ub "access to out-of-bounds index")` in both `Mach` and `MachTB`! -/
def wideSliceIdxReadWriteMir : CapturedMir :=
  ptrBody "witness::wide_slice_idx_read_write"
    [u32Decl, u32Decl, arrU32_4Decl, ptrMutU32Decl, rawMutSliceU32Decl,
     usizeMirDecl, usizeMirDecl, u32Decl, u32Decl, usizeMirDecl, u32Decl, u32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .storageLive 6, .storageLive 7, .storageLive 8, .storageLive 9, .storageLive 10, .storageLive 11,
     .assign (local_ 2)
       (.aggregate (.array u32Ty) [constU32 10, constU32 20, constU32 30, constU32 40]),
     .assign (local_ 3)
       (.rawPtr .mut { local_ := 2, projection := [.constantIndex 0 4 false] }),
     .assign (local_ 4)
       (.aggregate (.rawPtr sliceU32PointeeTy .mut) [.copy (local_ 3), constUsize 4]),
     .assign (local_ 5) (.use (constUsize 2)),
     .assign (local_ 6) (.use (constUsize 1)),
     .assign (local_ 7)
       (.use (.copy { local_ := 4, projection := [.deref, .index 5] })),
     .assign { local_ := 4, projection := [.deref, .index 6] } (.use (constU32 99)),
     .assign (local_ 8)
       (.use (.copy { local_ := 4, projection := [.deref, .index 6] })),
     .assign (local_ 9) (.len (derefPlace 4)),
     .assign (local_ 10) (.cast .intToInt (.copy (local_ 9)) u32Ty),
     .assign (local_ 11) (.binaryOp .add (.copy (local_ 7)) (.copy (local_ 8))),
     .assign (local_ 0) (.binaryOp .add (.copy (local_ 11)) (.copy (local_ 10)))]

def wideSliceIdxReadWriteFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, .Array (.Int u32) 4),
    (localName 3, .Ptr (.Raw .None)),
    (localName 4, .Ptr (sliceRefPtrType .mut ⟨4⟩ ⟨4⟩)),
    (localName 5, .Int IntType.usize_ty),
    (localName 6, .Int IntType.usize_ty),
    (localName 7, .Int u32),
    (localName 8, .Int u32),
    (localName 9, .Int IntType.usize_ty),
    (localName 10, .Int u32),
    (localName 11, .Int u32),
    (localName 12, mrWidePairTupleTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3), .StorageLive (localName 4),
      .StorageLive (localName 5), .StorageLive (localName 6), .StorageLive (localName 7),
      .StorageLive (localName 8), .StorageLive (localName 9), .StorageLive (localName 10),
      .StorageLive (localName 11), .StorageLive (localName 12),
      .Assign (.Local (localName 2))
        (.Tuple [.Constant (.Int 10) (.Int u32), .Constant (.Int 20) (.Int u32),
                 .Constant (.Int 30) (.Int u32), .Constant (.Int 40) (.Int u32)]
          (.Array (.Int u32) 4)),
      .Assign (.Local (localName 3)) (.AddrOf (.Local (localName 2)) (.Raw .None)),
      .Assign (.Local (localName 4))
        (.UnOp (.Cast (.Transmute (.Ptr (sliceRefPtrType .mut ⟨4⟩ ⟨4⟩))))
          (.Tuple [.Load (.Local (localName 3)), .Constant (.Int 4) (.Int IntType.usize_ty)]
            mrWidePairTupleTy)),
      .Assign (.Local (localName 5)) (.Constant (.Int 2) (.Int IntType.usize_ty)),
      .Assign (.Local (localName 6)) (.Constant (.Int 1) (.Int IntType.usize_ty)),
      .Assign (.Local (localName 7))
        (.Load (.Index (.Deref (.Load (.Local (localName 4))) (.Slice (.Int u32)))
          (.Load (.Local (localName 5))))),
      .Assign
        (.Index (.Deref (.Load (.Local (localName 4))) (.Slice (.Int u32)))
          (.Load (.Local (localName 6))))
        (.Constant (.Int 99) (.Int u32)),
      .Assign (.Local (localName 8))
        (.Load (.Index (.Deref (.Load (.Local (localName 4))) (.Slice (.Int u32)))
          (.Load (.Local (localName 6))))),
      .Assign (.Local (localName 12))
        (.UnOp (.Cast (.Transmute mrWidePairTupleTy)) (.Load (.Local (localName 4)))),
      .Assign (.Local (localName 9)) (.Load (.Field (.Local (localName 12)) 1)),
      .Assign (.Local (localName 10)) (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 9)))),
      .Assign (.Local (localName 11))
        (.BinOp (.Int .Add) (.Load (.Local (localName 7))) (.Load (.Local (localName 8)))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 11))) (.Load (.Local (localName 10))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

/-- Out-of-bounds wide-slice indexing companion (`idx = 4` on `len = 4`). -/
def wideSliceIdxOobMir : CapturedMir :=
  ptrBody "witness::wide_slice_idx_oob_ub"
    [u32Decl, u32Decl, arrU32_4Decl, ptrMutU32Decl, rawMutSliceU32Decl, usizeMirDecl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .assign (local_ 2)
       (.aggregate (.array u32Ty) [constU32 10, constU32 20, constU32 30, constU32 40]),
     .assign (local_ 3)
       (.rawPtr .mut { local_ := 2, projection := [.constantIndex 0 4 false] }),
     .assign (local_ 4)
       (.aggregate (.rawPtr sliceU32PointeeTy .mut) [.copy (local_ 3), constUsize 4]),
     .assign (local_ 5) (.use (constUsize 4)),
     .assign (local_ 0)
       (.use (.copy { local_ := 4, projection := [.deref, .index 5] }))]

def wideSliceIdxOobFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, .Array (.Int u32) 4),
    (localName 3, .Ptr (.Raw .None)),
    (localName 4, .Ptr (sliceRefPtrType .mut ⟨4⟩ ⟨4⟩)),
    (localName 5, .Int IntType.usize_ty)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5),
      .Assign (.Local (localName 2))
        (.Tuple [.Constant (.Int 10) (.Int u32), .Constant (.Int 20) (.Int u32),
                 .Constant (.Int 30) (.Int u32), .Constant (.Int 40) (.Int u32)]
          (.Array (.Int u32) 4)),
      .Assign (.Local (localName 3)) (.AddrOf (.Local (localName 2)) (.Raw .None)),
      .Assign (.Local (localName 4))
        (.UnOp (.Cast (.Transmute (.Ptr (sliceRefPtrType .mut ⟨4⟩ ⟨4⟩))))
          (.Tuple [.Load (.Local (localName 3)), .Constant (.Int 4) (.Int IntType.usize_ty)]
            mrWidePairTupleTy)),
      .Assign (.Local (localName 5)) (.Constant (.Int 4) (.Int IntType.usize_ty)),
      .Assign (.Local (localName 0))
        (.Load (.Index (.Deref (.Load (.Local (localName 4))) (.Slice (.Int u32)))
          (.Load (.Local (localName 5)))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

def wideSliceIdxReadWriteS0 : MachineState :=
  initMachineState wideSliceIdxReadWriteMir [.scalar ⟨0, 4⟩]
def wideSliceIdxReadWriteMInit : Mach :=
  machine wideSliceIdxReadWriteMir wideSliceIdxReadWriteFn
    wideSliceIdxReadWriteS0.frame.locals wideSliceIdxReadWriteFn.start
def wideSliceIdxReadWriteTBInit : MachTB := liftMachToTB wideSliceIdxReadWriteMInit

def wideSliceIdxOobS0 : MachineState := initMachineState wideSliceIdxOobMir [.scalar ⟨0, 4⟩]
def wideSliceIdxOobMInit : Mach :=
  machine wideSliceIdxOobMir wideSliceIdxOobFn wideSliceIdxOobS0.frame.locals wideSliceIdxOobFn.start
def wideSliceIdxOobTBInit : MachTB := liftMachToTB wideSliceIdxOobMInit

/-- **Three-way lockstep agreement (`wideSliceIndexReadWriteAndOobUb_three_way`)**:
1. In-bounds wide-slice indexing `(*_4)[2]` read (`30`), `(*_4)[1] = 99` write, `(*_4)[1]` read
   (`99`), and `Rvalue.len(*_4)` (`4`) return `133` in Anneal (`mirTree`), `Mach` (`steps 26`),
   and `MachTB` (`stepsTB 26`).
2. Out-of-bounds wide-slice indexing `(*_4)[4]` (`4 ≥ 4`) faults with UB in Anneal (`FaultNow`),
   `Mach` (`"access to out-of-bounds index"`), and `MachTB` (`"access to out-of-bounds index"`). -/
theorem wideSliceIndexReadWriteAndOobUb_three_way :
    (∃ mem, ReachesRet (mirTree wideSliceIdxReadWriteMir wideSliceIdxReadWriteS0) []
      (.normal (.scalar ⟨133, 4⟩, mem))) ∧
    MirNoUBTree (mirTree wideSliceIdxReadWriteMir wideSliceIdxReadWriteS0) ∧
    (Interp.steps 26 wideSliceIdxReadWriteMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 133 }, [1]) ∧
    (Interp.stepsTB 26 wideSliceIdxReadWriteTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 133 ∧
    (∃ tr u, Reaches (mirTree wideSliceIdxOobMir wideSliceIdxOobS0) tr u ∧ FaultNow u) ∧
    stopAfterM wideSliceIdxOobMInit 10 = some (.ub "access to out-of-bounds index") ∧
    stopAfterTB wideSliceIdxOobTBInit 10 = some (.ub "access to out-of-bounds index") := by
  refine ⟨⟨_, runA_sound wideSliceIdxReadWriteMir 40 _ _ _ rfl⟩,
    runA_noUB wideSliceIdxReadWriteMir 40 _ _ _ rfl,
    by decide +kernel,
    by decide +kernel,
    faultsA_sound wideSliceIdxOobMir 30 _ rfl,
    by decide +kernel,
    by decide +kernel⟩

/-- `PointeeInfo` for `[u32; 4]` (`size = 16, align = 4`). -/
@[reducible]
def arrU32_4PointeeInfo : Gen.PointeeInfo :=
  { layout := .Sized ⟨16⟩ ⟨4⟩
    inhabited := true
    unsafe_cells := .Sized []
    freeze := true
    unpin := true }

/-- **Witness 3 (`wideSliceTreeBorrowsDisabledVsMetadataOk_three_way`)**:
Borrow-invalidation UB on dereferencing a wide slice pointer after a conflicting parent write,
contrasted with `UnOp.ptrMetadata` succeeding without dereferencing:
1. Anneal (`wideSliceDisabledDerefUbMir`): `_3 = &raw mut _2[0]`, `_4 = slice_from_raw_parts_mut(_3, 4)`,
   direct write `_2 = [1, 2, 3, 4]` (disables `_4`'s borrow tag), then `(*_4)[0]` faults with UB.
2. MiniRust `MachTB` (`wideSliceDisabledDerefUbFn`) runs a *different*, reference-based program:
   `_3 = &mut _2` (retagged `Reserved`), `_4 = transmute((_3 as *mut (), 4)) : &mut [u32]`, an
   activating write `(*_4)[0] = 77` (`Reserved -> Unique`), the parent write (`Foreign Write ->
   Disabled`), then the read faults with `"Tree Borrows: local read of Disabled reference"`.
   The *faithful* raw-pointer translation of the Anneal program does NOT fault in `MachTB` (nor in
   `Mach`); that aliasing-model divergence, `Mach`'s behaviour on this program, and the
   `Mach` / `MachTB` executions of the metadata companion are witnessed by
   `wideSliceParentWrite_aliasingDivergence_and_metadata_three_way` (§6).
3. Extracting `UnOp.ptrMetadata(_4)` after the parent write (`wideSliceMetadataAfterParentWriteMir`)
   succeeds and returns `4` in Anneal (MiniRust `Mach` / `MachTB` agreement: §6). -/
def wideSliceDisabledDerefUbMir : CapturedMir :=
  ptrBody "witness::wide_slice_disabled_deref_ub"
    [u32Decl, u32Decl, arrU32_4Decl, ptrMutU32Decl, rawMutSliceU32Decl, usizeMirDecl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .assign (local_ 2)
       (.aggregate (.array u32Ty) [constU32 10, constU32 20, constU32 30, constU32 40]),
     .assign (local_ 3)
       (.rawPtr .mut { local_ := 2, projection := [.constantIndex 0 4 false] }),
     .assign (local_ 4)
       (.aggregate (.rawPtr sliceU32PointeeTy .mut) [.copy (local_ 3), constUsize 4]),
     -- Direct write to `_2` disables the borrow tag carried by `_4`!
     .assign (local_ 2)
       (.aggregate (.array u32Ty) [constU32 1, constU32 2, constU32 3, constU32 4]),
     .assign (local_ 5) (.use (constUsize 0)),
     .assign (local_ 0)
       (.use (.copy { local_ := 4, projection := [.deref, .index 5] }))]

def wideSliceDisabledDerefUbFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, .Array (.Int u32) 4),
    (localName 3, .Ptr (.Ref .Mutable arrU32_4PointeeInfo)),
    (localName 4, .Ptr (sliceRefPtrType .mut ⟨4⟩ ⟨4⟩)),
    (localName 5, .Int IntType.usize_ty)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5),
      .Assign (.Local (localName 2))
        (.Tuple [.Constant (.Int 10) (.Int u32), .Constant (.Int 20) (.Int u32),
                 .Constant (.Int 30) (.Int u32), .Constant (.Int 40) (.Int u32)]
          (.Array (.Int u32) 4)),
      .Assign (.Local (localName 3))
        (.AddrOf (.Local (localName 2)) (.Ref .Mutable arrU32_4PointeeInfo)),
      .Assign (.Local (localName 4))
        (.UnOp (.Cast (.Transmute (.Ptr (sliceRefPtrType .mut ⟨4⟩ ⟨4⟩))))
          (.Tuple [.UnOp (.Cast (.Transmute (.Ptr (.Raw .None)))) (.Load (.Local (localName 3))),
                   .Constant (.Int 4) (.Int IntType.usize_ty)]
            mrWidePairTupleTy)),
      -- Activate `Reserved -> Unique` on `_4` by writing element 0, then overwrite `_2` directly
      -- (`Foreign Write -> Disabled`), then read `(*_4)[0]` (`local read of Disabled reference`)!
      .Assign (.Local (localName 5)) (.Constant (.Int 0) (.Int IntType.usize_ty)),
      .Assign
        (.Index (.Deref (.Load (.Local (localName 4))) (.Slice (.Int u32)))
          (.Load (.Local (localName 5))))
        (.Constant (.Int 77) (.Int u32)),
      .Assign (.Local (localName 2))
        (.Tuple [.Constant (.Int 1) (.Int u32), .Constant (.Int 2) (.Int u32),
                 .Constant (.Int 3) (.Int u32), .Constant (.Int 4) (.Int u32)]
          (.Array (.Int u32) 4)),
      .Assign (.Local (localName 0))
        (.Load (.Index (.Deref (.Load (.Local (localName 4))) (.Slice (.Int u32)))
          (.Load (.Local (localName 5)))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

/-- Companion that extracts `UnOp.ptrMetadata(_4)` after the parent write disables `_4`'s borrow tag. -/
def wideSliceMetadataAfterParentWriteMir : CapturedMir :=
  ptrBody "witness::wide_slice_metadata_after_parent_write"
    [u32Decl, u32Decl, arrU32_4Decl, ptrMutU32Decl, rawMutSliceU32Decl, usizeMirDecl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .assign (local_ 2)
       (.aggregate (.array u32Ty) [constU32 10, constU32 20, constU32 30, constU32 40]),
     .assign (local_ 3)
       (.rawPtr .mut { local_ := 2, projection := [.constantIndex 0 4 false] }),
     .assign (local_ 4)
       (.aggregate (.rawPtr sliceU32PointeeTy .mut) [.copy (local_ 3), constUsize 4]),
     -- Direct write to `_2` disables `_4`'s borrow tag, yet `PtrMetadata(_4)` does not dereference!
     .assign (local_ 2)
       (.aggregate (.array u32Ty) [constU32 1, constU32 2, constU32 3, constU32 4]),
     .assign (local_ 5) (.unaryOp .ptrMetadata (.copy (local_ 4))),
     .assign (local_ 0) (.cast .intToInt (.copy (local_ 5)) u32Ty)]

def wideSliceDisabledDerefUbS0 : MachineState :=
  initMachineState wideSliceDisabledDerefUbMir [.scalar ⟨0, 4⟩]
def wideSliceDisabledDerefUbMInit : Mach :=
  machine wideSliceDisabledDerefUbMir wideSliceDisabledDerefUbFn
    wideSliceDisabledDerefUbS0.frame.locals wideSliceDisabledDerefUbFn.start
def wideSliceDisabledDerefUbTBInit : MachTB := liftMachToTB wideSliceDisabledDerefUbMInit

def wideSliceMetadataAfterParentWriteS0 : MachineState :=
  initMachineState wideSliceMetadataAfterParentWriteMir [.scalar ⟨0, 4⟩]

theorem wideSliceTreeBorrowsDisabledVsMetadataOk_three_way :
    (∃ tr u, Reaches (mirTree wideSliceDisabledDerefUbMir wideSliceDisabledDerefUbS0) tr u ∧
      FaultNow u) ∧
    stopAfterTB wideSliceDisabledDerefUbTBInit 12 =
      some (.ub "Tree Borrows: local read of Disabled reference") ∧
    (∃ mem, ReachesRet
      (mirTree wideSliceMetadataAfterParentWriteMir wideSliceMetadataAfterParentWriteS0) []
      (.normal (.scalar ⟨4, 4⟩, mem))) ∧
    MirNoUBTree
      (mirTree wideSliceMetadataAfterParentWriteMir wideSliceMetadataAfterParentWriteS0) := by
  refine ⟨faultsA_sound wideSliceDisabledDerefUbMir 30 _ rfl,
    by decide +kernel,
    ⟨_, runA_sound wideSliceMetadataAfterParentWriteMir 30 _ _ _ rfl⟩,
    runA_noUB wideSliceMetadataAfterParentWriteMir 30 _ _ _ rfl⟩

/-- **Witness 4 (`wideSliceSizeAndAlignOfVal_u32_str_empty_zst_witnesses`)**:
Concrete ground-truth agreement between Anneal (`stepMirFn` / `evalNonSelectIntrinsicCall`) and
MiniRust's `Machine::compute_size` / `compute_align` (`computeSize` / `computeAlign`, the spec
functions behind `UnOp::ComputeSize` / `ComputeAlign`, which the executable `Interp` leaves
`unsupported` — see `minirust_interp_metadata_unops_unsupported`) on:
1. `[u32]` (`len = 4`, `elemSz = 4`, `elemAlign = 4` $\mapsto$ `size = 16, align = 4`),
2. `str` (`len = 5` $\mapsto$ `size = 5, align = 1`),
3. empty `[u32]` (`len = 0` $\mapsto$ `size = 0, align = 4`), and
4. ZST `[()]` (`len = 1000, elemSz = 0, elemAlign = 1` $\mapsto$ `size = 0, align = 1`). -/
def sizeOfValCalleeOp (tys : List RigidTy) : Operand :=
  .constant { ty := { kind := .fnDef "core::intrinsics::size_of_val" tys, layoutIdx := 0 }
              val := .zeroSized }

def alignOfValCalleeOp (tys : List RigidTy) : Operand :=
  .constant { ty := { kind := .fnDef "core::intrinsics::align_of_val" tys, layoutIdx := 0 }
              val := .zeroSized }

def wideSliceSizeAlignMir (elemTy : RigidTy) (len : Nat) : CapturedMir where
  defPath := "witness::wide_slice_size_align"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, ptrMutU32Decl,
    { mutability := .mut, ty := { kind := .rawPtr .not (.slice elemTy), layoutIdx := 0 },
      debugName := some "sl_ptr" },
    usizeMirDecl, usizeMirDecl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2), mkStmt (.storageLive 3),
        mkStmt (.storageLive 4), mkStmt (.storageLive 5),
        mkStmt (.storageLive 6), mkStmt (.storageLive 7),
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3)
          (.aggregate (.rawPtr { kind := .slice elemTy, layoutIdx := 0 } .not)
            [.copy (local_ 2), constUsize len]))],
      terminator := mkTerm
        (.call (sizeOfValCalleeOp [.slice elemTy]) [.copy (local_ 3)] (local_ 4) (some 1)
          .continue_),
      isCleanup := false },
    { statements := [],
      terminator := mkTerm
        (.call (alignOfValCalleeOp [.slice elemTy]) [.copy (local_ 3)] (local_ 5) (some 2)
          .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 6) (.cast .intToInt (.copy (local_ 4)) u32Ty)),
        mkStmt (.assign (local_ 7) (.cast .intToInt (.copy (local_ 5)) u32Ty)),
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 6)) (.copy (local_ 7))))],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

def wideStrSizeAlignMir (len : Nat) : CapturedMir where
  defPath := "witness::wide_str_size_align"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, ptrMutU32Decl,
    { mutability := .mut, ty := rawConstStrTy, debugName := some "str_ptr" },
    usizeMirDecl, usizeMirDecl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2), mkStmt (.storageLive 3),
        mkStmt (.storageLive 4), mkStmt (.storageLive 5),
        mkStmt (.storageLive 6), mkStmt (.storageLive 7),
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3)
          (.aggregate (.rawPtr strPointeeMirTy .not)
            [.copy (local_ 2), constUsize len]))],
      terminator := mkTerm
        (.call (sizeOfValCalleeOp [.str]) [.copy (local_ 3)] (local_ 4) (some 1) .continue_),
      isCleanup := false },
    { statements := [],
      terminator := mkTerm
        (.call (alignOfValCalleeOp [.str]) [.copy (local_ 3)] (local_ 5) (some 2) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 6) (.cast .intToInt (.copy (local_ 4)) u32Ty)),
        mkStmt (.assign (local_ 7) (.cast .intToInt (.copy (local_ 5)) u32Ty)),
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 6)) (.copy (local_ 7))))],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

private theorem except_bind_ok {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl

private theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

/-- **`checkPtr` symbolic overflow UB on safe slice references (`&[T]` / `&mut [T]`)**:
For any in-bounds thin pointer `thin` and element count `len < scalarModulus 8` whose total byte
size `len * elemSz` overflows `isize::MAX` (`x86_64.valid_size ⟨len * elemSz⟩ = false`, i.e.,
`signedHalfModulus 8 ≤ len * elemSz`), MiniRust's `checkPtr` on `&[T]` / `&mut [T]` faults with
`.error (.ub "Value::Ptr: total size exeeds isize::MAX")` before inspecting alignment or memory. -/
theorem checkPtr_sliceRef_overflow_ub
    (thin : Ptr) (mutbl : MirAst.Mutability) (elemSz elemAlign : Nat) (freeze : Bool)
    (len : Nat) (m : Option Mach)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hLen : len < scalarModulus 8)
    (hOverflow : x86_64.valid_size ⟨len * elemSz⟩ = false) :
    checkPtr (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len))))
      (sliceRefPtrType mutbl ⟨elemSz⟩ ⟨elemAlign⟩ freeze) m =
      .error (.ub "Value::Ptr: total size exeeds isize::MAX") := by
  have hAddrOk :
      ensureElseUb (inBounds thin.addr .Unsigned x86_64.PTR_SIZE)
        "Value::Ptr: pointer out-of-bounds" = Except.ok () := by
    unfold ensureElseUb
    rw [hAddr]
    rfl
  have hMeta :
      checkPtrMetadata (some (.ElementCount (Int.ofNat len))) .ElementCount = Except.ok () :=
    (checkPtrMetadata_elementCount_iff_anneal_usize len).1.mpr hLen
  have hProdNonneg : (0 : Int) ≤ Int.ofNat len * (elemSz : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg len) (Int.natCast_nonneg elemSz)
  have hToNat : (Int.ofNat len * (elemSz : Int)).toNat = len * elemSz := rfl
  have hComp : ∀ (lookup : Ptr → Interp VTable),
      LayoutStrategy.compute_size_and_align lookup (.Slice ⟨elemSz⟩ ⟨elemAlign⟩)
          (some (.ElementCount (Int.ofNat len))) =
        Except.ok (⟨len * elemSz⟩, ⟨elemAlign⟩) := by
    intro lookup
    unfold LayoutStrategy.compute_size_and_align
    dsimp only
    rw [ite_eq_left_iff.mpr (fun h => absurd hProdNonneg h), hToNat]
    rfl
  have hSizeErr :
      ensureElseUb (inBounds ((len * elemSz : Nat) : Int) .Signed x86_64.PTR_SIZE)
        "Value::Ptr: total size exeeds isize::MAX" =
        Except.error (.ub "Value::Ptr: total size exeeds isize::MAX") := by
    have hInB : inBounds ((len * elemSz : Nat) : Int) .Signed x86_64.PTR_SIZE = false := hOverflow
    unfold ensureElseUb
    rw [hInB]
    rfl
  unfold checkPtr sliceRefPtrType ThinPointer.widen PtrType.meta_kind
    LayoutStrategy.meta_kind PtrType.safe_pointee
  dsimp only
  rw [hAddrOk, except_bind_ok, hMeta, except_bind_ok, hComp, except_bind_ok,
    hSizeErr, except_bind_error]

set_option maxHeartbeats 800000 in
theorem wideSliceSizeAndAlignOfVal_u32_str_empty_zst_witnesses :
    let u32SlMir := wideSliceSizeAlignMir (.uint .u32) 4
    let emptySlMir := wideSliceSizeAlignMir (.uint .u32) 0
    let zstSlMir := wideSliceSizeAlignMir (.tuple []) 1000
    let strMir := wideStrSizeAlignMir 5
    -- `[u32]` (`len = 4`): `size = 16, align = 4`, sum `= 20`
    (∃ mem, ReachesRet (mirTree u32SlMir (initMachineState u32SlMir [.scalar ⟨0, 4⟩])) []
      (.normal (.scalar ⟨20, 4⟩, mem))) ∧
    computeSize wideRawPartsMInit (.Slice ⟨4⟩ ⟨4⟩) (some (.ElementCount 4)) = .ok ⟨16⟩ ∧
    computeAlign wideRawPartsMInit (.Slice ⟨4⟩ ⟨4⟩) (some (.ElementCount 4)) = .ok ⟨4⟩ ∧
    -- `str` (`len = 5`): `size = 5, align = 1`, sum `= 6`
    (∃ mem, ReachesRet (mirTree strMir (initMachineState strMir [.scalar ⟨0, 4⟩])) []
      (.normal (.scalar ⟨6, 4⟩, mem))) ∧
    computeSize wideRawPartsMInit (.Slice ⟨1⟩ ⟨1⟩) (some (.ElementCount 5)) = .ok ⟨5⟩ ∧
    computeAlign wideRawPartsMInit (.Slice ⟨1⟩ ⟨1⟩) (some (.ElementCount 5)) = .ok ⟨1⟩ ∧
    -- empty `[u32]` (`len = 0`): `size = 0, align = 4`, sum `= 4`
    (∃ mem, ReachesRet (mirTree emptySlMir (initMachineState emptySlMir [.scalar ⟨0, 4⟩])) []
      (.normal (.scalar ⟨4, 4⟩, mem))) ∧
    computeSize wideRawPartsMInit (.Slice ⟨4⟩ ⟨4⟩) (some (.ElementCount 0)) = .ok ⟨0⟩ ∧
    computeAlign wideRawPartsMInit (.Slice ⟨4⟩ ⟨4⟩) (some (.ElementCount 0)) = .ok ⟨4⟩ ∧
    -- ZST `[(); 1000]` (`elemSz = 0, align = 1`): `size = 0, align = 1`, sum `= 1`
    (∃ mem, ReachesRet (mirTree zstSlMir (initMachineState zstSlMir [.scalar ⟨0, 4⟩])) []
      (.normal (.scalar ⟨1, 4⟩, mem))) ∧
    computeSize wideRawPartsMInit (.Slice ⟨0⟩ ⟨1⟩) (some (.ElementCount 1000)) = .ok ⟨0⟩ ∧
    computeAlign wideRawPartsMInit (.Slice ⟨0⟩ ⟨1⟩) (some (.ElementCount 1000)) = .ok ⟨1⟩ := by
  intro u32SlMir emptySlMir zstSlMir strMir
  exact ⟨⟨_, runA_sound u32SlMir 16 _ _ _ rfl⟩, rfl, rfl,
    ⟨_, runA_sound strMir 16 _ _ _ rfl⟩, rfl, rfl,
    ⟨_, runA_sound emptySlMir 16 _ _ _ rfl⟩, rfl, rfl,
    ⟨_, runA_sound zstSlMir 16 _ _ _ rfl⟩, rfl, rfl⟩

/-- **`checkPtr` symbolic agreement on provenance-free empty safe slice references (`&[T]`, `len = 0`)**:
When `len = 0`, total byte size is `0 * elemSz = 0 ≤ isize::MAX`, so for any non-null aligned
in-bounds thin pointer `thin` (even with `thin.provenance = none`, e.g., `NonNull::dangling()`),
MiniRust's `checkPtr` on `&[T]` / `&mut [T]` with `m = none` succeeds with `.ok ()`. -/
theorem checkPtr_sliceRef_empty_ok
    (thin : Ptr) (mutbl : MirAst.Mutability) (elemSz elemAlign : Nat) (freeze : Bool)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hNonNull : (thin.addr != 0) = true)
    (hAligned : Align.is_aligned ⟨elemAlign⟩ thin.addr = true) :
    checkPtr (ThinPointer.widen thin (some (.ElementCount 0)))
      (sliceRefPtrType mutbl ⟨elemSz⟩ ⟨elemAlign⟩ freeze) none =
      .ok () := by
  have hAddrOk :
      ensureElseUb (inBounds thin.addr .Unsigned x86_64.PTR_SIZE)
        "Value::Ptr: pointer out-of-bounds" = Except.ok () := by
    unfold ensureElseUb; rw [hAddr]; rfl
  have hMeta :
      checkPtrMetadata (some (.ElementCount 0)) .ElementCount = Except.ok () :=
    (checkPtrMetadata_elementCount_iff_anneal_usize 0).1.mpr (by decide)
  have hComp : ∀ (lookup : Ptr → Interp VTable),
      LayoutStrategy.compute_size_and_align lookup (.Slice ⟨elemSz⟩ ⟨elemAlign⟩)
          (some (.ElementCount 0)) =
        Except.ok (⟨0⟩, ⟨elemAlign⟩) := by
    intro lookup
    unfold LayoutStrategy.compute_size_and_align
    simp [Pure.pure, Except.pure]
  have hSizeOk :
      ensureElseUb (inBounds ((0 : Nat) : Int) .Signed x86_64.PTR_SIZE)
        "Value::Ptr: total size exeeds isize::MAX" = Except.ok () := by
    have hInB : inBounds ((0 : Nat) : Int) .Signed x86_64.PTR_SIZE = true := by decide
    unfold ensureElseUb; rw [hInB]; rfl
  have hNonNullOk :
      ensureElseUb (thin.addr != 0) "Value::Ptr: null safe pointer" = Except.ok () := by
    unfold ensureElseUb; rw [hNonNull]; rfl
  have hAlignOk :
      ensureElseUb (Align.is_aligned ⟨elemAlign⟩ thin.addr)
        "Value::Ptr: unaligned safe pointer" = Except.ok () := by
    unfold ensureElseUb; rw [hAligned]; rfl
  unfold checkPtr sliceRefPtrType ThinPointer.widen PtrType.meta_kind
    LayoutStrategy.meta_kind PtrType.safe_pointee
  dsimp only
  rw [hAddrOk, except_bind_ok, hMeta, except_bind_ok, hComp, except_bind_ok]
  dsimp only
  rw [hSizeOk, except_bind_ok, hNonNullOk, except_bind_ok, hAlignOk, except_bind_ok]
  rfl

/-- Maximum `[u32]` element count whose byte size `len * 4 = 2^63 - 4` fits in `isize::MAX`. -/
abbrev u32SliceMaxOkLen : Nat := 2 ^ 61 - 1

/-- Minimal `[u32]` element count whose byte size `len * 4 = 2^63` overflows `isize::MAX`. -/
abbrev u32SliceOverflowLen : Nat := 2 ^ 61

/-- Concrete MIR program calling `size_of_val::<[u32]>` at `len = 2^61` (`u32SliceOverflowLen`). -/
def u32SliceOverflowMir : CapturedMir := wideSliceSizeAlignMir (.uint .u32) u32SliceOverflowLen

/-- Provenance-free aligned empty slice pointer `(addr = 4, provenance = none, len = 0)`. -/
def danglingEmptyU32SlicePtr : Pointer Prov :=
  ThinPointer.widen { addr := 4, provenance := none } (some (.ElementCount 0))

/-- Overflowing `[u32]` slice pointer `(addr = 256, len = 2^61)`. -/
def overflowingU32SlicePtr : Pointer Prov :=
  ThinPointer.widen { addr := 256, provenance := some (⟨1⟩, ()) }
    (some (.ElementCount (Int.ofNat u32SliceOverflowLen)))

/-- Direct call target for `core::intrinsics::size_of_val::<[u32]>`. -/
def sizeOfValSliceU32Target : ResolvedCallTarget :=
  { defPath := "core::intrinsics::size_of_val", typeArgs := [.slice (.uint .u32)],
    fnSig := none, isIndirect := false }

set_option maxHeartbeats 800000 in
/-- **Witness 5 (`wideSliceIsizeMaxBoundary_and_scalarAddrDivergence_canaries`)**:
1. **Exact `isize::MAX` (`2^63 - 1`) boundary on `[u32]` (`elemSz = 4`)**:
   - At `len = 2^61 - 1` (`len * 4 = 2^63 - 4 < 2^63 = signedHalfModulus 8`), Anneal's
     `evalSliceSizeOfVal 4 ⟨2^61 - 1, 8⟩ = some ⟨2^63 - 4, 8⟩` and MiniRust's
     `x86_64.valid_size ⟨(2^61 - 1) * 4⟩ = true`.
   - At `len = 2^61` (`len * 4 = 2^63 = signedHalfModulus 8`), Anneal's
     `wideSliceSizeAlignMir (.uint .u32) (2^61)` faults with UB (`FaultNow`), and MiniRust's
     `x86_64.valid_size ⟨2^61 * 4⟩ = false` and `checkPtr` on `&[u32]` with `len = 2^61` returns
     `.error (.ub "Value::Ptr: total size exeeds isize::MAX")` (MiniRust's only `isize::MAX` check;
     on a raw `*const [u32]` MiniRust is total — see
     `div_rawSliceSizeOfVal_isizeMax_anneal_ub_vs_minirust_total`).
2. **Provenance-free empty slice (`ptr::slice_from_raw_parts(4 as *const u32, 0)`)**:
   - MiniRust `checkPtr` on `&[u32]` with `addr = 4, provenance = none, len = 0` (`size = 0`)
     succeeds without UB (the matching Anneal / MiniRust `ptr::metadata` agreement on this
     provenance-free pointer is `div_rawSliceSizeOfVal_isizeMax_anneal_ub_vs_minirust_total`).
   - **Documented Stage-1 `Trusted` fail-closed divergence**: while MiniRust's `computeSize` and
     `checkPtr` on `&[u32]` (`len = 0`) accept `provenance = none` (`size = 0`), Stage-1 `Trusted`
     (`evalNonSelectIntrinsicCall`) requires a provenance-carrying `.ptr p 8` data pointer for
     `size_of_val` / `align_of_val` and fails closed with `MirStepNode.fail .ub` on
     `annealWideScalarPtrVal 4 0 8`. -/
theorem wideSliceIsizeMaxBoundary_and_scalarAddrDivergence_canaries :
    -- (1) `len = 2^61 - 1` succeeds; `len = 2^61` faults `.ub` in Anneal and in MiniRust's
    -- `&[u32]` validity check (`checkPtr`)
    evalSliceSizeOfVal 4 ⟨u32SliceMaxOkLen, 8⟩ = some ⟨u32SliceMaxOkLen * 4, 8⟩ ∧
    x86_64.valid_size ⟨u32SliceMaxOkLen * 4⟩ = true ∧
    evalSliceSizeOfVal 4 ⟨u32SliceOverflowLen, 8⟩ = none ∧
    x86_64.valid_size ⟨u32SliceOverflowLen * 4⟩ = false ∧
    (∃ tr u, Reaches
      (mirTree u32SliceOverflowMir (initMachineState u32SliceOverflowMir [.scalar ⟨0, 4⟩])) tr u ∧
      FaultNow u) ∧
    checkPtr overflowingU32SlicePtr (sliceRefPtrType .not ⟨4⟩ ⟨4⟩) (some wideRawPartsMInit) =
      .error (.ub "Value::Ptr: total size exeeds isize::MAX") ∧
    -- (2) Provenance-free empty slice (`addr = 4, len = 0`): `checkPtr` and `ptrMetadata` succeed,
    -- while Stage-1 `Trusted` `size_of_val` fails closed with `.fail .ub` on `.scalar` data ptr
    checkPtr danglingEmptyU32SlicePtr (sliceRefPtrType .not ⟨4⟩ ⟨4⟩) none = .ok () ∧
    evalNonSelectIntrinsicCall .sizeOfVal wideRawPartsS0 sizeOfValSliceU32Target
        wideRawPartsMir.localDecls emptyLayoutTable [] [annealWideScalarPtrVal 4 0 8]
        wideRawPartsS0.frame.locals (local_ 0) 1 =
      MirStepNode.fail .ub := by
  refine ⟨rfl, by decide, rfl, by decide,
    faultsA_sound u32SliceOverflowMir 12 _ (by decide +kernel),
    checkPtr_sliceRef_overflow_ub { addr := 256, provenance := some (⟨1⟩, ()) }
      .not 4 4 true u32SliceOverflowLen (some wideRawPartsMInit)
      (by decide) (by decide) (by decide),
    checkPtr_sliceRef_empty_ok { addr := 4, provenance := none } .not 4 4 true
      (by decide) (by decide) (by decide),
    rfl⟩

/-! ## 6. Honest MiniRust Fragment Boundaries & Divergence Canaries

The executable Lean `MiniRustSpec.Interp` implements `UnOp::{Int, Cast, GetThinPointer}` only, so
`UnOp::GetMetadata`, `UnOp::ComputeSize`, and `UnOp::ComputeAlign` — the MiniRust lowering of
`ptr::metadata`, `size_of_val`, and `align_of_val` — are `unsupported` there. The MiniRust side of
§2–§3 is therefore stated against the spec functions those operators denote
(`PointerMetaKind.encode_as_value`, `Machine::compute_size` / `compute_align`), and this section
pins down exactly where MiniRust's `isize::MAX` UB lives (only `check_ptr` on safe pointers), plus
the aliasing-model divergence on the faithful raw-pointer translation of Witness 3. -/

/-- `LayoutStrategy::compute_size_and_align` on a slice layout is total: for every vtable lookup,
element size, alignment, and element count, it returns `(len * elemSz, elemAlign)` — with NO
`isize::MAX` (`x86_64.valid_size`) check. -/
theorem compute_size_and_align_slice_eq (lookup : Ptr → Interp VTable)
    (elemSz elemAlign len : Nat) :
    LayoutStrategy.compute_size_and_align lookup (.Slice ⟨elemSz⟩ ⟨elemAlign⟩)
        (some (.ElementCount (Int.ofNat len))) =
      .ok (⟨len * elemSz⟩, ⟨elemAlign⟩) := by
  have hProdNonneg : (0 : Int) ≤ Int.ofNat len * (elemSz : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg len) (Int.natCast_nonneg elemSz)
  have hToNat : (Int.ofNat len * (elemSz : Int)).toNat = len * elemSz := rfl
  unfold LayoutStrategy.compute_size_and_align
  dsimp only
  rw [ite_eq_left_iff.mpr (fun h => absurd hProdNonneg h), hToNat]
  rfl

/-- MiniRust's `x86_64::valid_size` on a natural byte count is exactly Anneal's
`n < signedHalfModulus 8` (`2^63 = isize::MAX + 1`) bound. -/
theorem x86_64_valid_size_nat_eq (n : Nat) :
    x86_64.valid_size ⟨n⟩ = decide (n < signedHalfModulus 8) := by
  have hHalf : (2 : Int) ^ (8 * x86_64.PTR_SIZE.bytes - 1) =
      ((signedHalfModulus 8 : Nat) : Int) := by
    decide
  unfold x86_64.valid_size inBounds Size.bits
  rw [hHalf]
  have h1 : decide (-((signedHalfModulus 8 : Nat) : Int) ≤ ((n : Nat) : Int)) = true :=
    decide_eq_true (Int.le_trans (by decide : -((signedHalfModulus 8 : Nat) : Int) ≤ 0)
      (Int.natCast_nonneg n))
  have h2 : decide (((n : Nat) : Int) < ((signedHalfModulus 8 : Nat) : Int)) =
      decide (n < signedHalfModulus 8) := by
    by_cases h : n < signedHalfModulus 8
    · rw [decide_eq_true h]
      exact decide_eq_true (by omega)
    · rw [decide_eq_false h]
      exact decide_eq_false (by omega)
  rw [h1, h2, Bool.true_and]

/-- **MiniRust `Machine::compute_size` / `compute_align` are total on slices
(`computeSize_computeAlign_slice_total`)**: for every machine and every element count — including
counts whose byte size exceeds `isize::MAX` — MiniRust's `UnOp::ComputeSize` / `ComputeAlign`
semantics return `len * elemSz` / `elemAlign` without raising UB. -/
theorem computeSize_computeAlign_slice_total (m : Mach) (elemSz elemAlign len : Nat) :
    computeSize m (.Slice ⟨elemSz⟩ ⟨elemAlign⟩) (some (.ElementCount (Int.ofNat len))) =
      .ok ⟨len * elemSz⟩ ∧
    computeAlign m (.Slice ⟨elemSz⟩ ⟨elemAlign⟩) (some (.ElementCount (Int.ofNat len))) =
      .ok ⟨elemAlign⟩ := by
  refine ⟨?_, ?_⟩
  · unfold computeSize
    rw [compute_size_and_align_slice_eq]
    rfl
  · unfold computeAlign
    rw [compute_size_and_align_slice_eq]
    rfl

/-- MiniRust's `check_ptr` accepts every in-bounds raw wide slice pointer (`*const [T]` /
`*mut [T]` / `*const str`) whose element count is a valid `usize`, regardless of the pointee's
total byte size and of provenance: raw pointers carry no dereferenceability or size obligation. -/
theorem checkPtr_rawSlice_ok (thin : Ptr) (len : Nat) (m : Option Mach)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hLen : len < scalarModulus 8) :
    checkPtr (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len)))) (.Raw .ElementCount)
        m =
      .ok () := by
  have hAddrOk :
      ensureElseUb (inBounds thin.addr .Unsigned x86_64.PTR_SIZE)
        "Value::Ptr: pointer out-of-bounds" = Except.ok () := by
    unfold ensureElseUb; rw [hAddr]; rfl
  have hMeta :
      checkPtrMetadata (some (.ElementCount (Int.ofNat len))) .ElementCount = Except.ok () :=
    (checkPtrMetadata_elementCount_iff_anneal_usize len).1.mpr hLen
  simp only [checkPtr, ThinPointer.widen, PtrType.meta_kind, PtrType.safe_pointee, hAddrOk, hMeta]
  rfl

/-- **Where MiniRust's `size_of_val` `isize::MAX` UB lives (`sliceSizeOverflow_minirust_ub_locus`)**:
whenever `signedHalfModulus 8 ≤ len * elemSz` (the exact condition under which Anneal's
`size_of_val` / `align_of_val` fault, `sizeOfVal_and_alignOfVal_slice_lockstep`):
1. MiniRust's `check_ptr` on the safe reference `&[T]` / `&mut [T]` faults with
   `"Value::Ptr: total size exeeds isize::MAX"` — agreeing with Anneal's `.ub`;
2. yet `check_ptr` on the raw pointer `*const [T]` succeeds, and
3. MiniRust's `compute_size` / `compute_align` still return `len * elemSz` / `elemAlign`.
So for raw wide pointers Anneal's fault is strictly stricter than MiniRust (fail-closed, and the
same verdict as vendored Miri's `InvalidMeta(SliceTooBig)` in `LeanMiriSpec`). -/
theorem sliceSizeOverflow_minirust_ub_locus (m : Mach) (thin : Ptr) (mutbl : MirAst.Mutability)
    (elemSz elemAlign : Nat) (freeze : Bool) (len : Nat)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hLen : len < scalarModulus 8)
    (hOverflow : signedHalfModulus 8 ≤ len * elemSz) :
    checkPtr (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len))))
        (sliceRefPtrType mutbl ⟨elemSz⟩ ⟨elemAlign⟩ freeze) (some m) =
      .error (.ub "Value::Ptr: total size exeeds isize::MAX") ∧
    checkPtr (ThinPointer.widen thin (some (.ElementCount (Int.ofNat len)))) (.Raw .ElementCount)
        (some m) = .ok () ∧
    computeSize m (.Slice ⟨elemSz⟩ ⟨elemAlign⟩) (some (.ElementCount (Int.ofNat len))) =
      .ok ⟨len * elemSz⟩ ∧
    computeAlign m (.Slice ⟨elemSz⟩ ⟨elemAlign⟩) (some (.ElementCount (Int.ofNat len))) =
      .ok ⟨elemAlign⟩ := by
  have hValid : x86_64.valid_size ⟨len * elemSz⟩ = false := by
    rw [x86_64_valid_size_nat_eq]
    exact decide_eq_false (Nat.not_lt.mpr hOverflow)
  exact ⟨checkPtr_sliceRef_overflow_ub thin mutbl elemSz elemAlign freeze len (some m) hAddr hLen
      hValid,
    checkPtr_rawSlice_ok thin len (some m) hAddr hLen,
    computeSize_computeAlign_slice_total m elemSz elemAlign len⟩

/-- **Fragment-boundary canary (`minirust_interp_metadata_unops_unsupported`)**: the executable
Lean MiniRust interpreter (`evalUnOp` on `BasicMemory`, `evalUnOpM` on `TreeBorrowsMemory`) does
not implement `UnOp::GetMetadata`, `UnOp::ComputeSize`, or `UnOp::ComputeAlign`. This is why the
witnesses lower `ptr::metadata` via `Transmute` to `mrWidePairTupleTy` + `.Field 1` and state
`size_of_val` / `align_of_val` against `computeSize` / `computeAlign`; the canary breaks (and
forces those statements to be revisited) as soon as upstream adds executable support. -/
theorem minirust_interp_metadata_unops_unsupported (sty ty : Gen.Type) (v : Val)
    (m : Option Mach) (vTB : Gen.Value TBM) (mTB : Option MachTB) :
    evalUnOp .GetMetadata (v, ty) m =
      unsupported "eval_un_op for an operator outside UnOp::{Int, Cast, GetThinPointer}" ∧
    evalUnOp (.ComputeSize sty) (v, ty) m =
      unsupported "eval_un_op for an operator outside UnOp::{Int, Cast, GetThinPointer}" ∧
    evalUnOp (.ComputeAlign sty) (v, ty) m =
      unsupported "eval_un_op for an operator outside UnOp::{Int, Cast, GetThinPointer}" ∧
    evalUnOpM (M := TBM) .GetMetadata (vTB, ty) mTB =
      unsupported "eval_un_op for an operator outside UnOp::{Int, Cast, GetThinPointer}" ∧
    evalUnOpM (M := TBM) (.ComputeSize sty) (vTB, ty) mTB =
      unsupported "eval_un_op for an operator outside UnOp::{Int, Cast, GetThinPointer}" ∧
    evalUnOpM (M := TBM) (.ComputeAlign sty) (vTB, ty) mTB =
      unsupported "eval_un_op for an operator outside UnOp::{Int, Cast, GetThinPointer}" :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 800000 in
/-- **Divergence canary `DIV-MR-RAW-SLICE-SIZE-OF-VAL-ISIZE-MAX`
(`div_rawSliceSizeOfVal_isizeMax_anneal_ub_vs_minirust_total`)**:
1. At `len = 2^61` on `[u32]` (`len * 4 = 2^63`), Anneal's `size_of_val::<[u32]>` program faults
   with UB, while MiniRust's `compute_size` returns `2^63`, `compute_align` returns `4`, and
   `check_ptr` accepts the raw `*const [u32]` — MiniRust raises the `isize::MAX` UB only for the
   safe reference `&[u32]`. Anneal is fail-closed (stricter) on raw wide pointers.
2. On the provenance-free empty slice `ptr::slice_from_raw_parts(4 as *const u32, 0)`, Anneal's
   `UnOp.ptrMetadata` / wide-to-thin `CastKind.ptrToPtr` and MiniRust's metadata encoding /
   `UnOp::GetThinPointer` agree (`0` and address `4`) without touching memory. -/
theorem div_rawSliceSizeOfVal_isizeMax_anneal_ub_vs_minirust_total :
    (∃ tr u, Reaches
      (mirTree u32SliceOverflowMir (initMachineState u32SliceOverflowMir [.scalar ⟨0, 4⟩])) tr u ∧
      FaultNow u) ∧
    computeSize wideRawPartsMInit (.Slice ⟨4⟩ ⟨4⟩)
        (some (.ElementCount (Int.ofNat u32SliceOverflowLen))) = .ok ⟨2 ^ 63⟩ ∧
    computeAlign wideRawPartsMInit (.Slice ⟨4⟩ ⟨4⟩)
        (some (.ElementCount (Int.ofNat u32SliceOverflowLen))) = .ok ⟨4⟩ ∧
    checkPtr overflowingU32SlicePtr (.Raw .ElementCount) (some wideRawPartsMInit) = .ok () ∧
    checkPtr overflowingU32SlicePtr (sliceRefPtrType .not ⟨4⟩ ⟨4⟩) (some wideRawPartsMInit) =
      .error (.ub "Value::Ptr: total size exeeds isize::MAX") ∧
    evalRvalue [.uninit, .init (annealWideScalarPtrVal 4 0 8)]
        (.unaryOp .ptrMetadata (.copy (local_ 1))) emptyMemory
        [u32Decl, rawConstSliceU32Decl] emptyLayoutTable =
      .ok (.scalar ⟨0, 8⟩) [.uninit, .init (annealWideScalarPtrVal 4 0 8)] emptyMemory ∧
    PointerMetaKind.encode_as_value .ElementCount danglingEmptyU32SlicePtr.metadata =
      .ok (.Int 0) ∧
    evalRvalue [.uninit, .init (annealWideScalarPtrVal 4 0 8)]
        (.cast .ptrToPtr (.copy (local_ 1)) rawConstUnitTy) emptyMemory
        [u32Decl, rawConstSliceU32Decl] emptyLayoutTable =
      .ok (.scalar ⟨4, 8⟩) [.uninit, .init (annealWideScalarPtrVal 4 0 8)] emptyMemory ∧
    evalUnOp .GetThinPointer (Value.Ptr danglingEmptyU32SlicePtr, .Ptr (.Raw .ElementCount)) =
      .ok (Value.Ptr (ThinPointer.widen { addr := 4, provenance := none } none),
        .Ptr (.Raw .None)) := by
  refine ⟨faultsA_sound u32SliceOverflowMir 12 _ (by decide +kernel), rfl, rfl,
    checkPtr_rawSlice_ok _ _ _ (by decide) (by decide),
    (sliceSizeOverflow_minirust_ub_locus wideRawPartsMInit { addr := 256, provenance := some (⟨1⟩, ()) }
      .not 4 4 true u32SliceOverflowLen (by decide) (by decide) (by decide)).1,
    rfl, rfl, rfl, rfl⟩

/-- Faithful MiniRust translation of `wideSliceDisabledDerefUbMir`: a raw element pointer
`_3 = &raw mut _2` (no retag), a raw wide pointer `_4 = transmute((_3, 4)) : *mut [u32]`, the
direct parent write `_2 = [1, 2, 3, 4]`, and the read `_0 = (*_4)[0]`. -/
def wideSliceRawParentWriteFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, .Array (.Int u32) 4),
    (localName 3, .Ptr (.Raw .None)),
    (localName 4, .Ptr (.Raw .ElementCount)),
    (localName 5, .Int IntType.usize_ty)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5),
      .Assign (.Local (localName 2))
        (.Tuple [.Constant (.Int 10) (.Int u32), .Constant (.Int 20) (.Int u32),
                 .Constant (.Int 30) (.Int u32), .Constant (.Int 40) (.Int u32)]
          (.Array (.Int u32) 4)),
      .Assign (.Local (localName 3)) (.AddrOf (.Local (localName 2)) (.Raw .None)),
      .Assign (.Local (localName 4))
        (.UnOp (.Cast (.Transmute (.Ptr (.Raw .ElementCount))))
          (.Tuple [.Load (.Local (localName 3)), .Constant (.Int 4) (.Int IntType.usize_ty)]
            mrWidePairTupleTy)),
      .Assign (.Local (localName 2))
        (.Tuple [.Constant (.Int 1) (.Int u32), .Constant (.Int 2) (.Int u32),
                 .Constant (.Int 3) (.Int u32), .Constant (.Int 4) (.Int u32)]
          (.Array (.Int u32) 4)),
      .Assign (.Local (localName 5)) (.Constant (.Int 0) (.Int IntType.usize_ty)),
      .Assign (.Local (localName 0))
        (.Load (.Index (.Deref (.Load (.Local (localName 4))) (.Slice (.Int u32)))
          (.Load (.Local (localName 5)))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

def wideSliceRawParentWriteMInit : Mach :=
  machine wideSliceDisabledDerefUbMir wideSliceRawParentWriteFn
    wideSliceDisabledDerefUbS0.frame.locals wideSliceRawParentWriteFn.start
def wideSliceRawParentWriteTBInit : MachTB := liftMachToTB wideSliceRawParentWriteMInit

/-- MiniRust translation of `wideSliceMetadataAfterParentWriteMir`, lowering
`_5 = PtrMetadata(_4)` (no executable `UnOp::GetMetadata`) to `_6 = transmute(_4) :
mrWidePairTupleTy; _5 = _6.1`. -/
def wideSliceMetadataAfterParentWriteFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, .Array (.Int u32) 4),
    (localName 3, .Ptr (.Raw .None)),
    (localName 4, .Ptr (.Raw .ElementCount)),
    (localName 5, .Int IntType.usize_ty),
    (localName 6, mrWidePairTupleTy)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5), .StorageLive (localName 6),
      .Assign (.Local (localName 2))
        (.Tuple [.Constant (.Int 10) (.Int u32), .Constant (.Int 20) (.Int u32),
                 .Constant (.Int 30) (.Int u32), .Constant (.Int 40) (.Int u32)]
          (.Array (.Int u32) 4)),
      .Assign (.Local (localName 3)) (.AddrOf (.Local (localName 2)) (.Raw .None)),
      .Assign (.Local (localName 4))
        (.UnOp (.Cast (.Transmute (.Ptr (.Raw .ElementCount))))
          (.Tuple [.Load (.Local (localName 3)), .Constant (.Int 4) (.Int IntType.usize_ty)]
            mrWidePairTupleTy)),
      .Assign (.Local (localName 2))
        (.Tuple [.Constant (.Int 1) (.Int u32), .Constant (.Int 2) (.Int u32),
                 .Constant (.Int 3) (.Int u32), .Constant (.Int 4) (.Int u32)]
          (.Array (.Int u32) 4)),
      .Assign (.Local (localName 6))
        (.UnOp (.Cast (.Transmute mrWidePairTupleTy)) (.Load (.Local (localName 4)))),
      .Assign (.Local (localName 5)) (.Load (.Field (.Local (localName 6)) 1)),
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 5))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

def wideSliceMetadataAfterParentWriteMInit : Mach :=
  machine wideSliceMetadataAfterParentWriteMir wideSliceMetadataAfterParentWriteFn
    wideSliceMetadataAfterParentWriteS0.frame.locals wideSliceMetadataAfterParentWriteFn.start
def wideSliceMetadataAfterParentWriteTBInit : MachTB :=
  liftMachToTB wideSliceMetadataAfterParentWriteMInit

/-- **Aliasing-model divergence + metadata agreement
(`wideSliceParentWrite_aliasingDivergence_and_metadata_three_way`)**, completing Witness 3:
1. **Faithful raw-pointer program** (`DIV-MR-RAW-PARENT-WRITE-SB-VS-TB`): Anneal's
   Stacked-Borrows-style tracker disables `_4`'s borrow on the direct write to `_2` and faults on
   `(*_4)[0]`, whereas MiniRust returns `1` on BOTH `Mach` (no aliasing model) and `MachTB` (Tree
   Borrows raw pointers inherit the parent tag, so the parent write does not disable them).
   Anneal is fail-closed (stricter) here.
2. **Reference-based program** (`wideSliceDisabledDerefUbFn`): `MachTB` faults with
   `"Tree Borrows: local read of Disabled reference"` while `Mach` returns `1`.
3. **Metadata after the parent write**: Anneal, `Mach`, and `MachTB` all return `4` — `ptr::metadata`
   never dereferences, so the invalidated borrow is irrelevant. -/
theorem wideSliceParentWrite_aliasingDivergence_and_metadata_three_way :
    (∃ tr u, Reaches (mirTree wideSliceDisabledDerefUbMir wideSliceDisabledDerefUbS0) tr u ∧
      FaultNow u) ∧
    (Interp.steps 12 wideSliceRawParentWriteMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 1 }, [1]) ∧
    (Interp.stepsTB 12 wideSliceRawParentWriteTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 1 ∧
    (Interp.steps 13 wideSliceDisabledDerefUbMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 1 }, [1]) ∧
    stopAfterTB wideSliceDisabledDerefUbTBInit 12 =
      some (.ub "Tree Borrows: local read of Disabled reference") ∧
    (∃ mem, ReachesRet
      (mirTree wideSliceMetadataAfterParentWriteMir wideSliceMetadataAfterParentWriteS0) []
      (.normal (.scalar ⟨4, 4⟩, mem))) ∧
    MirNoUBTree
      (mirTree wideSliceMetadataAfterParentWriteMir wideSliceMetadataAfterParentWriteS0) ∧
    (Interp.steps 14 wideSliceMetadataAfterParentWriteMInit).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 4 }, [1]) ∧
    (Interp.stepsTB 14 wideSliceMetadataAfterParentWriteTBInit).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 4 := by
  refine ⟨faultsA_sound wideSliceDisabledDerefUbMir 30 _ rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨_, runA_sound wideSliceMetadataAfterParentWriteMir 30 _ _ _ rfl⟩,
    runA_noUB wideSliceMetadataAfterParentWriteMir 30 _ _ _ rfl,
    by decide +kernel, by decide +kernel⟩

/-! ## 7. Relational Pointer Correspondence (`WideSliceThinPtrRel`, `WideSliceValRel`) & `translateStatement` Grounding

Addresses two structural correspondence properties across Anneal and MiniRust:
1. **`WideSliceThinPtrRel` and `WideSliceValRel`**: ties MiniRust's `BasicMemory` thin pointer
   `thin` and `TreeBorrowsMemory` thin pointer `thinTB` directly to Anneal's `p : ProvenancePtr`
   via `ctx.ptrTargets` (`ctxWithBorrows body ctx mem.borrows`), proving that `UnOp.ptrMetadata`,
   `CastKind.ptrToPtr` (wide-to-thin and wide-to-wide), `AggregateKind.rawPtr`, `checkPtr`, and
   the `to_raw_parts` $\rightarrow$ `from_raw_parts` round-trip preserve the relational invariant
   between `p`, `thin`, and `thinTB`.
2. **`Translate.translateStatement` / `translateRvalue` / `translatePlace` Grounding**: proves that
   every standard statement of the witness bodies (`wideRawPartsMir`, `wideSliceIdxReadWriteMir`,
   `wideSliceIdxOobMir`, `wideSliceDisabledDerefUbMir`, `wideSliceMetadataAfterParentWriteMir`)
   is produced directly by `Translate.translateStatement` (`translateRvalue` / `translatePlace`),
   and characterizes the exact 4 wide-slice constructs (`(*s)[i]`, `AggregateKind.rawPtr`,
   `UnOp.ptrMetadata`, `Rvalue.len (*s)`) on which `Translate.lean` returns `none` and which the
   witness functions lower via `PlaceExpr.Index (PlaceExpr.Deref ... (.Slice _))` and
   `PtrType.as_wide_pair` (`mrWidePairTupleTy`). -/

/-- Relation tying an Anneal `ProvenancePtr` `p` to its MiniRust `BasicMemory` thin pointer
`thin` and `TreeBorrowsMemory` thin pointer `thinTB` under `ctx`:
- `ctx.ptrTargets p.allocId = some (baseAddr, prov)` maps `p.allocId` to its MiniRust target base
  address `baseAddr` and provenance `prov`,
- `thin.addr = thinTB.addr = baseAddr + p.offsetBytes < scalarModulus 8` (`2^64`),
- `thin.provenance = prov`, and
- `thinTB.provenance` pairs the same MiniRust `AllocId` with Tree Borrows path `[(p.tag : Int)]`. -/
def WideSliceThinPtrRel (ctx : Ctx) (p : ProvenancePtr) (thin : Ptr)
    (thinTB : ThinPointer TreeBorrowsProvenance) : Prop :=
  ∃ (baseAddr : Nat) (prov : Option Prov),
    ctx.ptrTargets p.allocId = some (baseAddr, prov) ∧
    baseAddr + p.offsetBytes < scalarModulus 8 ∧
    thin = { addr := ((baseAddr + p.offsetBytes : Nat) : Int), provenance := prov } ∧
    thinTB =
      { addr := ((baseAddr + p.offsetBytes : Nat) : Int)
        provenance := prov.map (fun (aid, _) => (aid, [(p.tag : Int)])) }

/-- Constructing `WideSliceThinPtrRel` from an active/frozen stack borrow `e` in `mem.borrows`
under `ctxWithBorrows body ctx borrows`: `p.allocId` resolves through `lookupBorrow borrows p.tag`
and `ptrTargetSpec` to `baseAddr = (ctx.addrs.getD e.targetLocal 0 + relOff).toNat` and
`prov = some (⟨ctx.base.length + e.targetLocal⟩, ())`. -/
theorem WideSliceThinPtrRel.of_ctxWithBorrows
    (body : CapturedMir) (ctx : Ctx) (borrows : List BorrowEntry)
    (p : ProvenancePtr) (e : BorrowEntry) (it : Gen.IntType) (relOff : Nat)
    (hlookup : lookupBorrow borrows p.tag = some e)
    (htspec : ptrTargetSpec body.layouts body.localDecls ⟨e.targetLocal, e.targetProjection⟩ =
      some (it, relOff))
    (haddr : (ctx.addrs.getD e.targetLocal 0 + (relOff : Int)).toNat + p.offsetBytes <
      scalarModulus 8) :
    let baseAddr := (ctx.addrs.getD e.targetLocal 0 + (relOff : Int)).toNat
    let aid : Gen.AllocId := ⟨((ctx.base.length + e.targetLocal : Nat) : Int)⟩
    WideSliceThinPtrRel (ctxWithBorrows body ctx borrows) p
      { addr := ((baseAddr + p.offsetBytes : Nat) : Int), provenance := some (aid, ()) }
      { addr := ((baseAddr + p.offsetBytes : Nat) : Int)
        provenance := some (aid, [(p.tag : Int)]) } := by
  refine ⟨(ctx.addrs.getD e.targetLocal 0 + (relOff : Int)).toNat,
    some (⟨((ctx.base.length + e.targetLocal : Nat) : Int)⟩, ()), ?_, haddr, rfl, rfl⟩
  simp [ctxWithBorrows, borrowTargets, ProvenancePtr.tag] at hlookup ⊢
  simp [hlookup, htspec]

/-- Every `WideSliceThinPtrRel`-related MiniRust `thin` pointer has an in-bounds unsigned 64-bit
address (`inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true`). -/
theorem WideSliceThinPtrRel.inBounds_addr {ctx : Ctx} {p : ProvenancePtr}
    {thin : Ptr} {thinTB : ThinPointer TreeBorrowsProvenance}
    (hrel : WideSliceThinPtrRel ctx p thin thinTB) :
    inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true := by
  rcases hrel with ⟨baseAddr, prov, _, hlt, rfl, _⟩
  have hMod : (2 : Int) ^ (8 * x86_64.PTR_SIZE.bytes) = ((scalarModulus 8 : Nat) : Int) := by
    decide
  unfold inBounds Size.bits
  rw [hMod]
  have h1 : decide ((0 : Int) ≤ ((baseAddr + p.offsetBytes : Nat) : Int)) = true :=
    decide_eq_true (Int.natCast_nonneg _)
  have h2 : decide (((baseAddr + p.offsetBytes : Nat) : Int) < ((scalarModulus 8 : Nat) : Int)) =
      true :=
    decide_eq_true (by omega)
  rw [h1, h2, Bool.true_and]

/-- Value-level correspondence between Anneal wide-slice `Value`s and MiniRust `BasicMemory`
(`Val`) / `TreeBorrowsMemory` (`Gen.Value TBM`) wide pointer values under `ctx`:
- `provenance`: relates `annealWidePtrVal p len 8` to `mrWidePtrVal thin (Int.ofNat len)` and
  `mrWidePtrValM thinTB (Int.ofNat len)` when `WideSliceThinPtrRel ctx p thin thinTB` and
  `len < scalarModulus 8`.
- `scalarAddr`: relates provenance-free `annealWideScalarPtrVal addr len 8` to
  `mrWidePtrVal { addr := (addr : Int), provenance := none } (Int.ofNat len)` and
  `mrWidePtrValM { addr := (addr : Int), provenance := none } (Int.ofNat len)` when
  `addr < scalarModulus 8` and `len < scalarModulus 8`. -/
inductive WideSliceValRel (ctx : Ctx) : MirSemantics.Value → Val → Gen.Value TBM → Prop where
  | provenance {p : ProvenancePtr} {len : Nat} {thin : Ptr}
      {thinTB : ThinPointer TreeBorrowsProvenance}
      (hptr : WideSliceThinPtrRel ctx p thin thinTB)
      (hlen : len < scalarModulus 8) :
      WideSliceValRel ctx
        (annealWidePtrVal p len 8)
        (mrWidePtrVal thin (Int.ofNat len))
        (mrWidePtrValM thinTB (Int.ofNat len))
  | scalarAddr {addr len : Nat}
      (haddr : addr < scalarModulus 8)
      (hlen : len < scalarModulus 8) :
      WideSliceValRel ctx
        (annealWideScalarPtrVal addr len 8)
        (mrWidePtrVal { addr := (addr : Int), provenance := none } (Int.ofNat len))
        (mrWidePtrValM { addr := (addr : Int), provenance := none } (Int.ofNat len))

/-- Every `WideSliceValRel`-related MiniRust wide pointer passes `checkPtr ... (.Raw .ElementCount)`. -/
theorem WideSliceValRel.checkPtr_rawSlice_ok {ctx : Ctx}
    {v : MirSemantics.Value} {mrVal : Val} {mrValTB : Gen.Value TBM}
    (hrel : WideSliceValRel ctx v mrVal mrValTB) (m : Option Mach) :
    ∃ widePtr,
      mrVal = .Ptr widePtr ∧
      checkPtr widePtr (.Raw .ElementCount) m = .ok () := by
  cases hrel with
  | provenance hptr hlen =>
      exact ⟨_, rfl, MiniRustSpec.Correspondence.WideSliceDst.checkPtr_rawSlice_ok
        _ _ m hptr.inBounds_addr hlen⟩
  | @scalarAddr addr len haddr hlen =>
      have hin : inBounds (addr : Int) .Unsigned x86_64.PTR_SIZE = true := by
        have hMod : (2 : Int) ^ (8 * x86_64.PTR_SIZE.bytes) = ((scalarModulus 8 : Nat) : Int) := by
          decide
        unfold inBounds Size.bits
        rw [hMod]
        have h1 : decide ((0 : Int) ≤ (addr : Int)) = true :=
          decide_eq_true (Int.natCast_nonneg _)
        have h2 : decide ((addr : Int) < ((scalarModulus 8 : Nat) : Int)) = true :=
          decide_eq_true (by omega)
        rw [h1, h2, Bool.true_and]
      exact ⟨_, rfl, MiniRustSpec.Correspondence.WideSliceDst.checkPtr_rawSlice_ok
        { addr := (addr : Int), provenance := none } len m hin hlen⟩

/-- **Relational `UnOp.ptrMetadata` lockstep (`ptrMetadata_wideSliceValRel_lockstep`)**:
For any `WideSliceValRel ctx v mrVal mrValTB` (covering both provenance-carrying and
provenance-free wide pointers), Anneal's `evalRvalue locals (.unaryOp .ptrMetadata op)` and
MiniRust's `PointerMetaKind.encode_as_value .ElementCount` extract the exact same `len < 2^64`. -/
theorem ptrMetadata_wideSliceValRel_lockstep
    {ctx : Ctx} {locals locals' : List LocalSlot} {op : Operand}
    {mem : MirSemantics.Memory} {localDecls : List LocalDecl}
    {v : MirSemantics.Value} {mrVal : Val} {mrValTB : Gen.Value TBM}
    (hNonWide : isNonWidePtrAggregateTy (operandTy localDecls emptyLayoutTable op) = false)
    (hOp : evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok v locals')
    (hrel : WideSliceValRel ctx v mrVal mrValTB) :
    ∃ (len : Nat) (widePtr : Pointer Prov),
      len < scalarModulus 8 ∧
      mrVal = .Ptr widePtr ∧
      evalRvalue locals (.unaryOp .ptrMetadata op) mem localDecls emptyLayoutTable =
        .ok (.scalar ⟨len, 8⟩) locals' mem ∧
      PointerMetaKind.encode_as_value .ElementCount widePtr.metadata =
        .ok (.Int (Int.ofNat len)) := by
  cases hrel with
  | @provenance p len thin thinTB hptr hlen =>
      refine ⟨len, _, hlen, rfl, ?_, rfl⟩
      show evalUnaryPtrMetadata locals op mem localDecls emptyLayoutTable = _
      unfold evalUnaryPtrMetadata
      simp only [hOp, annealWidePtrVal, layoutPointerBytes, emptyLayoutTable, Nat.beq_refl,
        Bool.and_self]
  | @scalarAddr addr len haddr hlen =>
      have hWrap : wrapScalarBits len (scalarModulus 8) = len := by
        unfold wrapScalarBits
        rw [nat_ble_eq_false_of_lt hlen]
      refine ⟨len, _, hlen, rfl, ?_, rfl⟩
      show evalUnaryPtrMetadata locals op mem localDecls emptyLayoutTable = _
      unfold evalUnaryPtrMetadata
      simp only [hOp, annealWideScalarPtrVal, hNonWide, layoutPointerBytes, emptyLayoutTable,
        Nat.beq_refl, Bool.and_self, hWrap]

/-- **Relational `to_raw_parts` $\leftrightarrow$ `from_raw_parts` lockstep
(`ptrToPtr_wideSliceValRel_and_to_from_raw_parts_roundtrip`)**:
Given `WideSliceThinPtrRel ctx p thin thinTB` and `len < scalarModulus 8`:
1. `AggregateKind.rawPtr` from `(.ptr p 8, .scalar ⟨len, 8⟩)` produces a triple satisfying
   `WideSliceValRel ctx (annealWidePtrVal p len 8) (mrWidePtrVal thin (Int.ofNat len))
   (mrWidePtrValM thinTB (Int.ofNat len))`;
2. Wide-to-wide `CastKind.ptrToPtr` preserves `WideSliceValRel ctx`;
3. Wide-to-thin `CastKind.ptrToPtr` (in Anneal) and `evalUnOp .GetThinPointer` /
   `evalUnOpM .GetThinPointer` (in `Mach` / `MachTB`) produce `.ptr p 8`,
   `ThinPointer.widen thin none`, and `ThinPointer.widen thinTB none` preserving
   `WideSliceThinPtrRel ctx p thin thinTB`;
4. Decomposing via `to_raw_parts` and reassembling via `AggregateKind.rawPtr` recovers the
   original `WideSliceValRel`-related wide pointer triple across Anneal, `Mach`, and `MachTB`! -/
theorem ptrToPtr_wideSliceValRel_and_to_from_raw_parts_roundtrip
    {ctx : Ctx} (locals locals₁ locals₂ : List LocalSlot)
    (wideOp dataOp metaOp : Operand) (thinTargetTy wideTargetTy pointeeTy : Ty)
    (mutability : MirAst.Mutability) (mem : MirSemantics.Memory) (localDecls : List LocalDecl)
    (p : ProvenancePtr) (len : Nat) (thin : Ptr)
    (thinTB : ThinPointer TreeBorrowsProvenance) (ptrTy : PtrType)
    (hptr : WideSliceThinPtrRel ctx p thin thinTB)
    (hlen : len < scalarModulus 8)
    (hThin : isThinRawPtrTy thinTargetTy = true)
    (hNotThin : isThinRawPtrTy wideTargetTy = false)
    (hWide : wideRawPtrIsDyn? wideTargetTy = some false)
    (hWideAgg : wideAggregatePointeeIsDyn? pointeeTy = some false)
    (hWideOp : evalOperand locals wideOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (annealWidePtrVal p len 8) locals₁)
    (hData : evalOperand locals₁ dataOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (.ptr p 8) locals₁)
    (hMeta : evalOperand locals₁ metaOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals
      localDecls mem.callStack = .ok (.scalar ⟨len, 8⟩) locals₂) :
    WideSliceValRel ctx
      (annealWidePtrVal p len 8)
      (mrWidePtrVal thin (Int.ofNat len))
      (mrWidePtrValM thinTB (Int.ofNat len)) ∧
    ((lookupBorrow mem.borrows p.tag = none →
        evalRvalue locals (.cast .ptrToPtr wideOp thinTargetTy) mem localDecls emptyLayoutTable =
          .ok (.ptr p 8) locals₁ mem ∧
        WideSliceThinPtrRel ctx p thin thinTB) ∧
     evalUnOp .GetThinPointer (mrWidePtrVal thin (Int.ofNat len), .Ptr ptrTy) =
       .ok (.Ptr (ThinPointer.widen thin none), .Ptr (.Raw .None)) ∧
     evalUnOpM (M := TBM) .GetThinPointer (mrWidePtrValM thinTB (Int.ofNat len), .Ptr ptrTy) =
       .ok (.Ptr (ThinPointer.widen thinTB none), .Ptr (.Raw .None))) ∧
    evalRvalue locals (.cast .ptrToPtr wideOp wideTargetTy) mem localDecls emptyLayoutTable =
      .ok (annealWidePtrVal p len 8) locals₁ mem ∧
    evalRvalue locals (.unaryOp .ptrMetadata wideOp) mem localDecls emptyLayoutTable =
      .ok (.scalar ⟨len, 8⟩) locals₁ mem ∧
    evalRvalue locals₁ (.aggregate (.rawPtr pointeeTy mutability) [dataOp, metaOp]) mem localDecls
        emptyLayoutTable =
      .ok (annealWidePtrVal p len 8) locals₂ mem := by
  have hcast := ptrToPtr_wide_to_thin_and_wide_to_wide_lockstep
    locals locals₁ wideOp thinTargetTy wideTargetTy mem localDecls p len thin thinTB ptrTy
    hThin hNotThin hWide hWideOp
  have hagg := aggregate_rawPtr_and_to_raw_parts_roundtrip_lockstep
    locals₁ locals₁ locals₂ pointeeTy mutability dataOp metaOp mem localDecls p len thin thinTB
    hWideAgg hData hMeta
  refine ⟨.provenance hptr hlen, ⟨fun hnb => ⟨hcast.1.1 hnb, hptr⟩, rfl, rfl⟩,
    hcast.2, ?_, hagg.1⟩
  show evalUnaryPtrMetadata locals wideOp mem localDecls emptyLayoutTable = _
  unfold evalUnaryPtrMetadata
  simp only [hWideOp, annealWidePtrVal, layoutPointerBytes, emptyLayoutTable, Nat.beq_refl,
    Bool.and_self]

/-- **Boundary theorem (`translatePlace_and_translateRvalue_wideSlice_boundary`)**:
`Translate.translatePlace` and `Translate.translateRvalue` return `none` on the 4 wide-slice
constructs outside the thin-pointer fragment:
1. Dereference-index `(*_s)[_i]` (`⟨s, [.deref, .index i]⟩`) on a wide slice pointer local `_s`,
2. `Rvalue.aggregate (.rawPtr pointeeTy mutbl) [dataOp, metaOp]`,
3. `Rvalue.unaryOp .ptrMetadata op`, and
4. `Rvalue.len (*_s)` (`⟨s, [.deref]⟩`). -/
theorem translatePlace_and_translateRvalue_wideSlice_boundary :
    let decls := wideRawPartsMir.localDecls
    translatePlace decls { local_ := 8, projection := [.deref, .index 9] } = none ∧
    translateRvalue emptyLayoutTable decls (some rawMutSliceU32Ty)
      (.aggregate (.rawPtr sliceU32PointeeTy .mut) [.copy (local_ 3), constUsize 4]) = none ∧
    translateRvalue emptyLayoutTable decls (some usizeMirTy)
      (.unaryOp .ptrMetadata (.copy (local_ 5))) = none ∧
    translateRvalue emptyLayoutTable decls (some usizeMirTy)
      (.len (derefPlace 4)) = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`Translate.translateStatement` grounding for the wide-slice witness bodies
(`wideSliceWitnesses_translateStatement_correspondence`)**:
Every non-wide-lowering statement of `wideRawPartsMir` and `wideSliceIdxReadWriteMir` — including
array aggregate initialization, wide-to-wide `CastKind.ptrToPtr` (`_4 as *const [u32]` $\mapsto$
`.Load (.Local (localName 4))`), wide-to-thin `CastKind.ptrToPtr` (`_5 as *const ()` $\mapsto$
`.UnOp .GetThinPointer (.Load (.Local (localName 5)))`), `usize` index initialization, `IntToInt`
casts, and `BinOp.Add` — is produced directly by `Translate.translateStatement`! -/
theorem wideSliceWitnesses_translateStatement_correspondence :
    let d1 := wideRawPartsMir.localDecls
    let d2 := wideSliceIdxReadWriteMir.localDecls
    -- (1) Array aggregate initialization `[local_ 1, 20, 30, 40]`
    translateStatement d1
      (mkStmt (.assign (local_ 2)
        (.aggregate (.array u32Ty) [.copy (local_ 1), constU32 20, constU32 30, constU32 40])))
      emptyLayoutTable =
      some (.Assign (.Local (localName 2))
        (.Tuple [.Load (.Local (localName 1)), .Constant (.Int 20) (.Int u32),
                 .Constant (.Int 30) (.Int u32), .Constant (.Int 40) (.Int u32)]
          (.Array (.Int u32) 4))) ∧
    -- (2) Wide-to-wide `CastKind.ptrToPtr` (`*mut [u32] as *const [u32]`)
    translateStatement d1
      (mkStmt (.assign (local_ 5) (.cast .ptrToPtr (.copy (local_ 4)) rawConstSliceU32Ty)))
      emptyLayoutTable =
      some (.Assign (.Local (localName 5)) (.Load (.Local (localName 4)))) ∧
    -- (3) Wide-to-thin `CastKind.ptrToPtr` (`*const [u32] as *const ()`)
    translateStatement d1
      (mkStmt (.assign (local_ 6) (.cast .ptrToPtr (.copy (local_ 5)) rawConstUnitTy)))
      emptyLayoutTable =
      some (.Assign (.Local (localName 6)) (.UnOp .GetThinPointer (.Load (.Local (localName 5))))) ∧
    -- (4) Index constant, `IntToInt` cast, and `BinOp.Add` in `wideRawPartsMir`
    translateStatement d1 (mkStmt (.assign (local_ 9) (.use (constUsize 0)))) emptyLayoutTable =
      some (.Assign (.Local (localName 9)) (.Constant (.Int 0) (.Int IntType.usize_ty))) ∧
    translateStatement d1
      (mkStmt (.assign (local_ 11) (.cast .intToInt (.copy (local_ 7)) u32Ty))) emptyLayoutTable =
      some (.Assign (.Local (localName 11))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 7))))) ∧
    translateStatement d1
      (mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 10)) (.copy (local_ 11)))))
      emptyLayoutTable =
      some (.Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 10))) (.Load (.Local (localName 11))))) ∧
    -- (5) Array init, index constants, `IntToInt` cast, and `BinOp.Add` in `wideSliceIdxReadWriteMir`
    translateStatement d2 (mkStmt (.assign (local_ 5) (.use (constUsize 2)))) emptyLayoutTable =
      some (.Assign (.Local (localName 5)) (.Constant (.Int 2) (.Int IntType.usize_ty))) ∧
    translateStatement d2 (mkStmt (.assign (local_ 6) (.use (constUsize 1)))) emptyLayoutTable =
      some (.Assign (.Local (localName 6)) (.Constant (.Int 1) (.Int IntType.usize_ty))) ∧
    translateStatement d2
      (mkStmt (.assign (local_ 10) (.cast .intToInt (.copy (local_ 9)) u32Ty))) emptyLayoutTable =
      some (.Assign (.Local (localName 10))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 9))))) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end MiniRustSpec.Correspondence.WideSliceDst
