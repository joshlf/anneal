/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.SepLogicLenses
import Anneal.MirLoops
import Lean.Elab.Command

/-!
# Wide-Pointer Slice Lenses & Call-Cone Narrowing: Concrete MIR Witnesses

Every theorem family added to `Anneal.SepLogicLenses` (Section 6, `WidePtrVal` /
`SliceTypedAt` / borrow lenses) and `Anneal.MirLiftCore` (`CallConeNarrowing`) is
instantiated below on concrete trusted `Trusted.Rustc.V2026_06_01` data, with every
hypothesis discharged by the kernel (`rfl` / `decide`, never `native_decide`):

* a 16-byte captured global allocation holding the `[u32; 4]` array `[1, 2, 3, 4]`,
  read through `&[u32]` / `&mut [u32]` fat pointers on 64-bit and 32-bit layout tables
  (`Rvalue.len (*s)`, `PtrMetadata(s)`, checked `(*s)[i]`, `Unsize`);
* `split_at_mut` writes on both halves with reassembly, through `SliceTypedAt` and the
  `ActiveTypedSliceMutBorrow` lens;
* empty (`len = 0`) and zero-sized (`n = 0`) slices, and out-of-bounds refutations;
* a 3-callee program (`caller -> helper1`, unused `heavyCallee2` / `heavyCallee3`) pruned
  to `[helper1]` by `CallConeClosed` (`decide`), `runCfgWithCallees_cone_narrow_of_closed`,
  `wpMirExecSym_cone_narrow_of_closed`, and `mirWpConverges_cone_narrow_of_closed`, with
  concrete runs of both tables and negative canaries (indirect calls, reification casts,
  out-of-cone calls, and duplicate-entry shadowing).

The final `run_cmd` audits every declaration added to both modules: no `unsafe`, every module
declaration constructive (axioms within `{propext, Quot.sound}`; witnesses may also use
`Classical.choice`), so no `sorryAx` and no `Lean.ofReduceBool`, and every audited module
theorem is reachable from the witnesses of this file.
-/

namespace Anneal.MirSliceWidePtrLensTests

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.SepLogicLenses
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval (wpMirExecSym)

/-! ## Concrete layouts, declarations, allocation, and locals -/

def lensU32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def lensFatLayout64 : TypeLayout :=
  { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def lensFatLayout32 : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def layouts64 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [lensU32Layout, lensFatLayout64] }

def layouts32 : LayoutTable :=
  { pointerBits := 32, isLittleEndian := true, entries := [lensU32Layout, lensFatLayout32] }

theorem ptrBytes64 : layoutPointerBytes layouts64 = 8 := rfl
theorem ptrBytes32 : layoutPointerBytes layouts32 = 4 := rfl

/-- Locals: `0 : usize`, `1 : &[u32]`, `2 : usize` (index), `3 : &[u32; 4]`,
`4 : &mut [u32]`. -/
def decls : List LocalDecl := [
  { mutability := .mut, ty := { kind := .uint .usize, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not (.slice (.uint .u32)), layoutIdx := 1 },
    debugName := none },
  { mutability := .not, ty := { kind := .uint .usize, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .ref .not (.array (.uint .u32) 4), layoutIdx := 1 },
    debugName := none },
  { mutability := .not, ty := { kind := .ref .mut (.slice (.uint .u32)), layoutIdx := 1 },
    debugName := none }]

/-- Captured mutable global `[1u32, 2, 3, 4]` (little endian) at `allocId = 9`. -/
def arrAlloc : CapturedAllocation := {
  allocId := 9
  bytes := [some 1, some 0, some 0, some 0, some 2, some 0, some 0, some 0,
            some 3, some 0, some 0, some 0, some 4, some 0, some 0, some 0]
  relocations := []
  align := { bytes := 4 }
  mutability := .mut }

def mem0 : Memory := { globals := [arrAlloc] }

def p9 : ProvenancePtr := ⟨9, 0⟩

def wide4 : WidePtrVal := WidePtrVal.mk p9 4

/-- Frame for pointer width `pb`: `_1 : &[u32]` and `_4 : &mut [u32]` hold the fat pointer
of `wide4`, `_2 = 2`, `_3 : &[u32; 4]` holds the thin array pointer. -/
def locals (pb : Nat) : List LocalSlot :=
  [.uninit, .init (WidePtrVal.toValue pb wide4), .init (.scalar ⟨2, pb⟩), .init (.ptr p9 pb),
   .init (WidePtrVal.toValue pb wide4)]

def bytes16 : ByteMem := globalAllocByteMem arrAlloc

abbrev U32 : Type := {v : Nat // v < 256 ^ 4}

def u (v : Nat) (h : v < 256 ^ 4 := by decide) : U32 := ⟨v, h⟩

def xs4 : List U32 := [u 1, u 2, u 3, u 4]

/-! ## 1. `WidePtrVal` `.1` / `.2` normal forms -/

theorem widePtr_normal_forms :
    (WidePtrVal.mk p9 4).1 = p9 ∧ (WidePtrVal.mk p9 4).2 = 4 ∧
    WidePtrVal.toValue 8 wide4 = .aggregate 0 [.ptr ⟨9, 0⟩ 8, .scalar ⟨4, 8⟩] ∧
    WidePtrVal.toValue 4 wide4 = .aggregate 0 [.ptr ⟨9, 0⟩ 4, .scalar ⟨4, 4⟩] :=
  ⟨widePtr_proj_fst _ _, widePtr_proj_snd _ _, WidePtrVal.toValue_mk _ _ _,
    WidePtrVal.toValue_mk _ _ _⟩

/-- `simp` normalizes the subslice combinators on a *symbolic* wide pointer without any
`Prod.casesOn` (`.1` / `.2` projections only). -/
theorem widePtr_simp_symbolic (p : ProvenancePtr) (len n k : Nat) :
    (WidePtrVal.dropElems (WidePtrVal.mk p len) n k).2 = len - k ∧
      (WidePtrVal.takeElems (WidePtrVal.mk p len) k).1 = p ∧
      (WidePtrVal.takeElems (WidePtrVal.mk p len) k).2 = k ∧
      (WidePtrVal.dropElems (WidePtrVal.mk p len) n k).1 = WidePtrVal.elemPtr (p, len) n k :=
  ⟨WidePtrVal.dropElems_snd _ _ _, WidePtrVal.takeElems_fst _ _, WidePtrVal.takeElems_snd _ _,
    WidePtrVal.dropElems_fst _ _ _⟩

/-- `simp` closes projection arithmetic over symbolic wide pointers. -/
theorem widePtr_simp_closes (p : ProvenancePtr) (len k : Nat) :
    (WidePtrVal.takeElems (WidePtrVal.mk p len) k).2 + (WidePtrVal.mk p len).2 = k + len := by
  simp

theorem widePtr_elemOffset_witness :
    WidePtrVal.elemOffset wide4 4 0 = 0 ∧
      WidePtrVal.elemOffset (WidePtrVal.dropElems wide4 4 2) 4 1 = WidePtrVal.elemOffset wide4 4 3 :=
  ⟨WidePtrVal.elemOffset_zero _ _, WidePtrVal.elemOffset_dropElems _ _ _ _⟩

theorem widePtr_ptr_len_elemPtr_witness :
    wide4.ptr = p9 ∧ wide4.len = 4 ∧
      (WidePtrVal.elemPtr wide4 4 2).allocId = 9 ∧
      (WidePtrVal.elemPtr wide4 4 2).tag = 9 ∧
      (WidePtrVal.elemPtr wide4 4 2).offsetBytes = 8 ∧
      WidePtrVal.elemPtr wide4 4 0 = p9 ∧
      WidePtrVal.elemPtr (WidePtrVal.dropElems wide4 4 2) 4 1 = WidePtrVal.elemPtr wide4 4 3 :=
  ⟨widePtr_ptr_eq_fst _, widePtr_len_eq_snd _,
    WidePtrVal.elemPtr_allocId _ _ _, WidePtrVal.elemPtr_tag _ _ _,
    WidePtrVal.elemPtr_offsetBytes _ _ _, WidePtrVal.elemPtr_zero _ _,
    WidePtrVal.elemPtr_dropElems _ _ _ _⟩

/-- The 64-bit and 32-bit encodings of different wide pointers are distinct. -/
theorem widePtr_toValue_injective_witness :
    WidePtrVal.toValue 8 wide4 ≠ WidePtrVal.toValue 8 (WidePtrVal.mk p9 3) := by
  intro h
  have := congrArg Prod.snd (WidePtrVal.toValue_injective h)
  exact absurd this (by decide)

/-! ## 2. The concrete slice view -/

/-- The global's 16 bytes, as read by the trusted `globalAllocSliceToAbstractBytes`. -/
theorem bytes16_eq :
    bytes16 = [.init 1 none, .init 0 none, .init 0 none, .init 0 none,
               .init 2 none, .init 0 none, .init 0 none, .init 0 none,
               .init 3 none, .init 0 none, .init 0 none, .init 0 none,
               .init 4 none, .init 0 none, .init 0 none, .init 0 none] := rfl

theorem bytes16_length : bytes16.length = 16 := globalAllocByteMem_length arrAlloc

theorem arr_sliceTypedAt : SliceTypedAt ByteLensCodec.u32LE wide4 xs4 bytes16 := by
  refine ⟨rfl, by decide, ?_⟩
  intro i hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | k + 4, hi => exact absurd hi (by simp [xs4])

/-- The view has exactly `wide4.2 = 4` elements (`SliceTypedAt.length_eq`). -/
theorem arr_length_eq : xs4.length = wide4.2 := arr_sliceTypedAt.length_eq

/-- Uniqueness: any other `u32` view of the same window is `[1, 2, 3, 4]`. -/
theorem arr_view_unique (ys : List U32) (h : SliceTypedAt ByteLensCodec.u32LE wide4 ys bytes16) :
    ys = xs4 :=
  SliceTypedAt.unique h arr_sliceTypedAt

/-- A wrong element list is not a view of the window. -/
theorem arr_wrong_view_refuted :
    ¬ SliceTypedAt ByteLensCodec.u32LE wide4 [u 1, u 2, u 9, u 4] bytes16 := by
  intro h
  have := arr_view_unique _ h
  simp [xs4, u] at this

/-! ## 3. `Rvalue.len (*s)` and `PtrMetadata(s)` through `SliceTypedAt.len_eq` -/

/-- `&[u32]` (64-bit): `Len(*_1)` and `PtrMetadata(_1)` are both `4usize`. -/
theorem len_and_ptrMetadata_shared_64 :
    evalRvalue (locals 8) (.len { local_ := 1, projection := [.deref] }) mem0 decls layouts64 =
        .ok (.scalar ⟨4, 8⟩) (locals 8) mem0 ∧
      evalRvalue (locals 8) (.unaryOp .ptrMetadata (.copy { local_ := 1, projection := [] }))
        mem0 decls layouts64 = .ok (.scalar ⟨4, 8⟩) (locals 8) mem0 :=
  SliceTypedAt.len_eq arr_sliceTypedAt (locals 8) (locals 8) { local_ := 1, projection := [.deref] }
    (.copy { local_ := 1, projection := [] }) mem0 decls layouts64 [] (.uint .u32) 0
    rfl rfl rfl rfl rfl rfl rfl

/-- `&mut [u32]` (64-bit): `Len(*_4)` and `PtrMetadata(_4)` are both `4usize`. -/
theorem len_and_ptrMetadata_mut_64 :
    evalRvalue (locals 8) (.len { local_ := 4, projection := [.deref] }) mem0 decls layouts64 =
        .ok (.scalar ⟨4, 8⟩) (locals 8) mem0 ∧
      evalRvalue (locals 8) (.unaryOp .ptrMetadata (.copy { local_ := 4, projection := [] }))
        mem0 decls layouts64 = .ok (.scalar ⟨4, 8⟩) (locals 8) mem0 :=
  SliceTypedAt.len_eq arr_sliceTypedAt (locals 8) (locals 8) { local_ := 4, projection := [.deref] }
    (.copy { local_ := 4, projection := [] }) mem0 decls layouts64 [] (.uint .u32) 0
    rfl rfl rfl rfl rfl rfl rfl

/-- `&[u32]` on a 32-bit target: the length word is `4` bytes wide. -/
theorem len_and_ptrMetadata_shared_32 :
    evalRvalue (locals 4) (.len { local_ := 1, projection := [.deref] }) mem0 decls layouts32 =
        .ok (.scalar ⟨4, 4⟩) (locals 4) mem0 ∧
      evalRvalue (locals 4) (.unaryOp .ptrMetadata (.copy { local_ := 1, projection := [] }))
        mem0 decls layouts32 = .ok (.scalar ⟨4, 4⟩) (locals 4) mem0 :=
  SliceTypedAt.len_eq arr_sliceTypedAt (locals 4) (locals 4) { local_ := 1, projection := [.deref] }
    (.copy { local_ := 1, projection := [] }) mem0 decls layouts32 [] (.uint .u32) 0
    rfl rfl rfl rfl rfl rfl rfl

/-- `WidePtrVal.evalRvalue_len` directly, on the `wide.2 = 4` fat pointer. -/
theorem evalRvalue_len_direct_64 :
    evalRvalue (locals 8) (.len { local_ := 1, projection := [.deref] }) mem0 decls layouts64 =
      .ok (.scalar ⟨wide4.2, 8⟩) (locals 8) mem0 :=
  WidePtrVal.evalRvalue_len (locals 8) (locals 8) { local_ := 1, projection := [.deref] } mem0
    decls layouts64 [] (.uint .u32) 0 arrAlloc 4 wide4 rfl rfl rfl rfl rfl rfl (by decide)

/-- Negative: a fat pointer claiming `5` elements overruns the 16-byte allocation, and the
trusted `Len(*s)` faults with `.ub`, so no `SliceTypedAt` view of 5 elements exists. -/
theorem len_oob_ub_and_no_view :
    evalRvalue ((locals 8).set 1 (.init (WidePtrVal.toValue 8 (WidePtrVal.mk p9 5))))
        (.len { local_ := 1, projection := [.deref] }) mem0 decls layouts64 = .ub ∧
      ∀ ys : List U32, ¬ SliceTypedAt ByteLensCodec.u32LE (WidePtrVal.mk p9 5) ys bytes16 := by
  refine ⟨rfl, fun ys h => ?_⟩
  have hb := h.window_le
  rw [bytes16_length] at hb
  exact absurd hb (by decide)

/-! ## 4. Checked element reads `(*s)[i]` -/

/-- Lens side: element `2` of the view is typed at byte offset `8`. -/
theorem elem_read_lens :
    ∃ x, xs4[2]? = some x ∧ TypedAt ByteLensCodec.u32LE (WidePtrVal.elemOffset wide4 4 2) x bytes16 :=
  arr_sliceTypedAt.getElem_typedAt (by decide)

/-- Trusted side: the trusted global byte read at offset `8` decodes to `3`, exactly the
lens element (via `typedAt_globalAllocByteMem_iff`). -/
theorem elem_read_trusted_bytes :
    ∃ w, globalAllocSliceToAbstractBytes arrAlloc 8 4 = some w ∧
      ByteLensCodec.u32LE.decode w = some (u 3) :=
  (typedAt_globalAllocByteMem_iff ByteLensCodec.u32LE arrAlloc 8 (u 3)).mp
    (arr_sliceTypedAt.getElem_typedAt' (i := 2) (by decide))

/-- Trusted MIR side: the place `(*_1)[_2]` (`_2 = 2`) reads the scalar `3u32`, proved via the
general ground-MIR theorem `SliceTypedAt.evalPlaceRead_index` and `decodeValueFromBytes_uintLE_chunk`. -/
theorem elem_read_mir_place :
    evalPlaceRead (locals 8) { local_ := 1, projection := [.deref, .index 2] } mem0.borrows
        mem0.globals layouts64 mem0.callerLocals decls = .ok (.scalar ⟨3, 4⟩) (locals 8) :=
  SliceTypedAt.evalPlaceRead_index arr_sliceTypedAt (fun x => .scalar ⟨x.val, 4⟩)
    (locals 8) 1 2 2 8 mem0 decls layouts64 (.uint .u32) 2 _
    (by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun chunk x hlen hdec =>
      decodeValueFromBytes_uintLE_chunk .u32 4 14 layouts64 rfl (by decide) chunk x hlen hdec)
    rfl

/-- Out-of-bounds ground-MIR place read `(*_1)[_2]` when `_2 = 4` faults with `.ub`
(`SliceTypedAt.evalPlaceRead_index_oob_ub`). -/
theorem elem_read_mir_place_oob_ub :
    evalPlaceRead ((locals 8).set 2 (.init (.scalar ⟨4, 8⟩)))
        { local_ := 1, projection := [.deref, .index 2] } mem0.borrows
        mem0.globals layouts64 mem0.callerLocals decls = .ub :=
  SliceTypedAt.evalPlaceRead_index_oob_ub arr_sliceTypedAt (fun x => .scalar ⟨x.val, 4⟩)
    ((locals 8).set 2 (.init (.scalar ⟨4, 8⟩))) 1 2 4 8 mem0 decls layouts64 (.uint .u32) 2
    _ (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun chunk x hlen hdec =>
      decodeValueFromBytes_uintLE_chunk .u32 4 14 layouts64 rfl (by decide) chunk x hlen hdec)

/-- Subslice borrow `&(*_1)[1..3]` and element borrow `&(*_1)[2]` through
`evalSliceFatPtrDerefBorrow` (`SliceTypedAt.evalSliceFatPtrDerefBorrow_subslice` and
`SliceTypedAt.evalSliceFatPtrDerefBorrow_elem`). -/
theorem slice_fatPtr_deref_borrow_subslice_and_elem :
    (evalSliceFatPtrDerefBorrow (locals 8) mem0 wide4.1 8 ⟨wide4.2, 8⟩
        [.subslice 1 3 false] .frozen false (some { kind := .slice (.uint .u32), layoutIdx := 0 })
        layouts64 true decls none false =
      .ok (WidePtrVal.toValue 8 (WidePtrVal.mk (WidePtrVal.elemPtr wide4 4 1) 2)) (locals 8) mem0 ∧
     SliceTypedAt ByteLensCodec.u32LE (WidePtrVal.mk (WidePtrVal.elemPtr wide4 4 1) 2)
        [u 2, u 3] bytes16) ∧
    (evalSliceFatPtrDerefBorrow (locals 8) mem0 wide4.1 8 ⟨wide4.2, 8⟩
        [.constantIndex 2 3 false] .frozen false (some { kind := .slice (.uint .u32), layoutIdx := 0 })
        layouts64 true decls none false =
      .ok (.ptr (WidePtrVal.elemPtr wide4 4 2) 8) (locals 8) mem0 ∧
     TypedAt ByteLensCodec.u32LE (WidePtrVal.elemOffset wide4 4 2) (u 3) bytes16) :=
  ⟨SliceTypedAt.evalSliceFatPtrDerefBorrow_subslice arr_sliceTypedAt (locals 8) mem0 .frozen false
      (.uint .u32) 0 layouts64 true decls none false 1 3 (by decide) (by decide) rfl rfl
      (fun _ => rfl) rfl,
   SliceTypedAt.evalSliceFatPtrDerefBorrow_elem arr_sliceTypedAt (locals 8) mem0 .frozen false
      (.uint .u32) 0 layouts64 true decls none false 2 3 (by decide) (by decide) rfl rfl
      (fun _ => rfl) rfl⟩

/-- The trusted window read equals the lens byte window (`globalAllocSliceToAbstractBytes_eq_window`). -/
theorem elem_window_bridge :
    globalAllocSliceToAbstractBytes arrAlloc 8 4 = some ((bytes16.drop 8).take 4) :=
  globalAllocSliceToAbstractBytes_eq_window arrAlloc 8 4 (by decide)

/-- Out-of-bounds index `4` has no element. -/
theorem elem_oob_none : xs4[4]? = none :=
  arr_sliceTypedAt.getElem?_eq_none_of_le (Nat.le_refl 4)

/-! ## 5. `[u32; 4] -> &[u32]` unsizing -/

theorem arr_typedAt_array :
    TypedAt (ByteLensCodec.u32LE.array 4) p9.offsetBytes ⟨xs4, rfl⟩ bytes16 := rfl

/-- `Unsize` of `_3 : &[u32; 4]` to `&[u32]`: the trusted evaluation returns the fat pointer
of `(p9, 4)`, and that fat pointer carries the slice view with `wide.2 = 4`. -/
theorem unsize_array_to_slice_64 :
    evalRvalue (locals 8) (.cast (.pointerCoercion "Unsize") (.copy { local_ := 3, projection := [] })
        { kind := slicePtrKind true .not (.uint .u32), layoutIdx := 1 }) mem0 decls layouts64 =
      .ok (WidePtrVal.toValue 8 (WidePtrVal.mk p9 4)) (locals 8) mem0 ∧
    SliceTypedAt ByteLensCodec.u32LE (WidePtrVal.mk p9 4) xs4 bytes16 :=
  TypedAt.unsize_array_to_slice (locals 8) (locals 8) (.copy { local_ := 3, projection := [] })
    mem0 decls layouts64 true .not (.uint .u32) 1
    { kind := .ref .not (.array (.uint .u32) 4), layoutIdx := 1 } p9
    rfl rfl rfl rfl rfl (fun h => by cases h) rfl rfl arr_typedAt_array

/-- `Unsize` to `*const [u32]` on the 32-bit table. -/
theorem unsize_array_to_rawSlice_32 :
    evalRvalue (locals 4) (.cast (.pointerCoercion "Unsize") (.copy { local_ := 3, projection := [] })
        { kind := slicePtrKind false .not (.uint .u32), layoutIdx := 1 }) mem0 decls layouts32 =
      .ok (WidePtrVal.toValue 4 (WidePtrVal.mk p9 4)) (locals 4) mem0 :=
  (TypedAt.unsize_array_to_slice (locals 4) (locals 4) (.copy { local_ := 3, projection := [] })
    mem0 decls layouts32 false .not (.uint .u32) 1
    { kind := .ref .not (.array (.uint .u32) 4), layoutIdx := 1 } p9
    rfl rfl rfl rfl rfl (fun h => by cases h) rfl rfl arr_typedAt_array).1

/-! ## 6. `split_at_mut`: disjoint writes on both halves and reassembly -/

/-- Writing `20` to element `1` (left half of `split_at_mut(2)`). -/
def bytesW1 : ByteMem :=
  [.init 1 none, .init 0 none, .init 0 none, .init 0 none,
   .init 20 none, .init 0 none, .init 0 none, .init 0 none,
   .init 3 none, .init 0 none, .init 0 none, .init 0 none,
   .init 4 none, .init 0 none, .init 0 none, .init 0 none]

/-- Then writing `30` to element `0` of the right half (absolute element `2`). -/
def bytesW2 : ByteMem :=
  [.init 1 none, .init 0 none, .init 0 none, .init 0 none,
   .init 20 none, .init 0 none, .init 0 none, .init 0 none,
   .init 30 none, .init 0 none, .init 0 none, .init 0 none,
   .init 4 none, .init 0 none, .init 0 none, .init 0 none]

theorem write1 : writeTyped ByteLensCodec.u32LE (WidePtrVal.elemOffset wide4 4 1) (u 20) bytes16 =
    some bytesW1 := rfl

theorem write2 : writeTyped ByteLensCodec.u32LE (WidePtrVal.elemOffset wide4 4 (2 + 0)) (u 30) bytesW1 =
    some bytesW2 := rfl

/-- Left-half write: left view updated, right view intact, whole view `[1, 20, 3, 4]`. -/
theorem split_left_write :
    SliceTypedAt ByteLensCodec.u32LE (WidePtrVal.takeElems wide4 2) [u 1, u 20] bytesW1 ∧
      SliceTypedAt ByteLensCodec.u32LE (WidePtrVal.dropElems wide4 4 2) [u 3, u 4] bytesW1 ∧
      SliceTypedAt ByteLensCodec.u32LE wide4 [u 1, u 20, u 3, u 4] bytesW1 :=
  SliceTypedAt.write_left_reassemble arr_sliceTypedAt (k := 2) (i := 1) (by decide) (by decide)
    (u 20) write1

/-- Right-half write on the result: final whole view `[1, 20, 30, 4]`. -/
theorem split_right_write :
    SliceTypedAt ByteLensCodec.u32LE (WidePtrVal.takeElems wide4 2) [u 1, u 20] bytesW2 ∧
      SliceTypedAt ByteLensCodec.u32LE (WidePtrVal.dropElems wide4 4 2) [u 30, u 4] bytesW2 ∧
      SliceTypedAt ByteLensCodec.u32LE wide4 [u 1, u 20, u 30, u 4] bytesW2 :=
  SliceTypedAt.write_right_reassemble split_left_write.2.2 (k := 2) (j := 0) (by decide)
    (by decide) (u 30) write2

/-- The adjacent halves' windows are disjoint (`DisjointSlice.adjacent` at `k * n = 8`). -/
theorem split_halves_disjoint :
    DisjointSlice wide4.1.offsetBytes (2 * 4) (wide4.1.offsetBytes + 2 * 4) ((wide4.2 - 2) * 4) :=
  (SliceTypedAt.splitAt arr_sliceTypedAt (k := 2) (by decide)).2.2

/-- Reassembly from independently-proved halves (`of_splitAt`) and the round trip. -/
theorem split_reassemble_roundtrip :
    SliceTypedAt ByteLensCodec.u32LE wide4 ([u 1, u 2] ++ [u 3, u 4]) bytes16 ∧
      (xs4.take 2 ++ xs4.drop 2 = xs4) :=
  ⟨SliceTypedAt.of_splitAt (by decide) (SliceTypedAt.splitAt arr_sliceTypedAt (k := 2) (by decide)).1
      (SliceTypedAt.splitAt arr_sliceTypedAt (k := 2) (by decide)).2.1,
    (SliceTypedAt.splitAt_of_splitAt arr_sliceTypedAt (k := 2) (by decide)).2⟩

/-- `append` assembles a 2-element prefix and a 2-element suffix at `p9 + 8`. -/
theorem split_append_witness :
    SliceTypedAt ByteLensCodec.u32LE (WidePtrVal.mk p9 (2 + 2)) ([u 1, u 2] ++ [u 3, u 4]) bytes16 :=
  SliceTypedAt.append (SliceTypedAt.splitAt arr_sliceTypedAt (k := 2) (by decide)).1
    (SliceTypedAt.splitAt arr_sliceTypedAt (k := 2) (by decide)).2.1

/-- Frame rule: a raw byte write strictly after the window preserves the view. -/
theorem frame_write_outside :
    SliceTypedAt ByteLensCodec.u32LE (WidePtrVal.takeElems wide4 2) [u 1, u 2]
      [.init 1 none, .init 0 none, .init 0 none, .init 0 none,
       .init 2 none, .init 0 none, .init 0 none, .init 0 none,
       .init 99 none, .init 0 none, .init 0 none, .init 0 none,
       .init 4 none, .init 0 none, .init 0 none, .init 0 none] :=
  SliceTypedAt.frame_writeBytes (SliceTypedAt.splitAt arr_sliceTypedAt (k := 2) (by decide)).1
    (off := 8) (w := [.init 99 none]) (Or.inr (Or.inr (Or.inr (by decide)))) rfl

/-- `frame_write`: a typed `u8` write at byte `12` preserves the left half. -/
theorem frame_typed_write_outside :
    SliceTypedAt ByteLensCodec.u32LE (WidePtrVal.takeElems wide4 2) [u 1, u 2]
      [.init 1 none, .init 0 none, .init 0 none, .init 0 none,
       .init 2 none, .init 0 none, .init 0 none, .init 0 none,
       .init 3 none, .init 0 none, .init 0 none, .init 0 none,
       .init 7 none, .init 0 none, .init 0 none, .init 0 none] :=
  SliceTypedAt.frame_write (SliceTypedAt.splitAt arr_sliceTypedAt (k := 2) (by decide)).1
    (c₁ := ByteLensCodec.u8) (base₁ := 12) (v₁ := 7) (Or.inr (Or.inr (Or.inr (by decide)))) rfl

/-! ### The `&mut [u32]` borrow lens -/

/-- A byte-ranged `.unique` borrow (tag `77`) covering the whole 16-byte window. -/
def slBorrows : List BorrowEntry :=
  [{ tag := 77, targetLocal := 0, targetProjection := [], perm := .unique, rangeOffset := 0,
     rangeLen := 16 }]

theorem unique_permits_write : TreeBorrowPerm.PermitsUniqueWrite .unique :=
  TreeBorrowPerm.permitsUniqueWrite_unique

theorem reservedFrz_permits_write : TreeBorrowPerm.PermitsUniqueWrite (.reservedFrz false) := by
  intro prot
  cases prot <;> rfl

/-- Negative: a frozen (shared) tag has no unique-write permission. -/
theorem frozen_not_unique_write : ¬ TreeBorrowPerm.PermitsUniqueWrite .frozen := by
  intro h
  exact absurd (h false) (fun h' => by cases h')

/-- Negative: a protected conflicted reservation has no unique-write permission. -/
theorem conflicted_not_unique_write : ¬ TreeBorrowPerm.PermitsUniqueWrite (.reservedFrz true) := by
  intro h
  exact absurd (h true) (fun h' => by cases h')

/-- Negative: a disabled tag cannot even be read through. -/
theorem disabled_not_readable : ¬ TreeBorrowPerm.PermitsRead .disabled := by
  intro h
  cases h

theorem mutLens : ActiveTypedSliceMutBorrow ByteLensCodec.u32LE slBorrows 77 wide4 xs4 bytes16 :=
  ⟨arr_sliceTypedAt, _, rfl, ⟨Nat.le_refl 0, Nat.le_refl 16⟩, unique_permits_write⟩

theorem sharedLens : ActiveTypedSliceBorrow ByteLensCodec.u32LE slBorrows 77 wide4 xs4 bytes16 :=
  mutLens.toShared

/-- `split_at_mut(2)` on the borrow lens, then a write through the left half framed by the
right half, then a write through the right half framed by the left half, then reassembly. -/
theorem mutLens_split_write_reassemble :
    ActiveTypedSliceMutBorrow ByteLensCodec.u32LE slBorrows 77 wide4 [u 1, u 20, u 30, u 4] bytesW2 := by
  obtain ⟨hL, hR, _⟩ := ActiveTypedSliceMutBorrow.splitAt mutLens (k := 2) (by decide)
  obtain ⟨hL1, hR1⟩ := ActiveTypedSliceMutBorrow.write_elem_frame hL (i := 1) (by decide)
    (u 20) write1 hR.1 (Or.inr (Or.inr (Or.inl (by decide))))
  have hR1' : ActiveTypedSliceMutBorrow ByteLensCodec.u32LE slBorrows 77
      (WidePtrVal.dropElems wide4 4 2) [u 3, u 4] bytesW1 := ⟨hR1, hR.2⟩
  have hw2 : writeTyped ByteLensCodec.u32LE (WidePtrVal.elemOffset (WidePtrVal.dropElems wide4 4 2) 4 0)
      (u 30) bytesW1 = some bytesW2 := rfl
  obtain ⟨hR2, hL2⟩ := ActiveTypedSliceMutBorrow.write_elem_frame hR1' (i := 0) (by decide)
    (u 30) hw2 hL1.1 (Or.inr (Or.inr (Or.inr (by decide))))
  have hL2' : ActiveTypedSliceMutBorrow ByteLensCodec.u32LE slBorrows 77
      (WidePtrVal.takeElems wide4 2) [u 1, u 20] bytesW2 := ⟨hL2, hL1.2⟩
  exact ActiveTypedSliceMutBorrow.of_splitAt (by decide) hL2' hR2
    ⟨_, rfl, ⟨Nat.le_refl 0, Nat.le_refl 16⟩⟩

/-- Negative: a *frozen* entry for tag `77` (a shared reborrow) admits no `&mut [u32]` lens,
although the same window is readable through it. -/
theorem frozen_entry_no_mut_lens :
    ¬ ActiveTypedSliceMutBorrow ByteLensCodec.u32LE
        [{ tag := 77, targetLocal := 0, targetProjection := [], perm := .frozen, rangeOffset := 0,
           rangeLen := 16 }] 77 wide4 xs4 bytes16 ∧
      ActiveTypedSliceBorrow ByteLensCodec.u32LE
        [{ tag := 77, targetLocal := 0, targetProjection := [], perm := .frozen, rangeOffset := 0,
           rangeLen := 16 }] 77 wide4 xs4 bytes16 := by
  refine ⟨?_, ⟨arr_sliceTypedAt, _, rfl, ⟨Nat.le_refl 0, Nat.le_refl 16⟩, rfl⟩⟩
  rintro ⟨_, entry, he, _, hp⟩
  cases he
  exact frozen_not_unique_write hp

/-- A unique entry whose byte range is only `[0, 8)`. -/
def shortBorrows : List BorrowEntry :=
  [{ tag := 77, targetLocal := 0, targetProjection := [], perm := .unique, rangeOffset := 0,
     rangeLen := 8 }]

/-- Negative: the short range does not cover the whole 16-byte window, so there is no lens on
`wide4`; it does cover (and yields a lens on) the left half `takeElems wide4 2`. -/
theorem short_range_lens :
    ¬ ActiveTypedSliceMutBorrow ByteLensCodec.u32LE shortBorrows 77 wide4 xs4 bytes16 ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE shortBorrows 77 (WidePtrVal.takeElems wide4 2)
        (xs4.take 2) bytes16 := by
  refine ⟨?_, ⟨(SliceTypedAt.splitAt arr_sliceTypedAt (k := 2) (by decide)).1, _, rfl,
    ⟨Nat.le_refl 0, Nat.le_refl 8⟩, unique_permits_write⟩⟩
  rintro ⟨_, entry, he, hc, _⟩
  cases he
  exact absurd hc.2 (by decide)

/-- Negative: a tag with no borrow entry (`78`) yields no lens at all. -/
theorem unknown_tag_no_lens :
    ¬ ActiveTypedSliceBorrow ByteLensCodec.u32LE slBorrows 78 wide4 xs4 bytes16 := by
  rintro ⟨_, entry, he, _, _⟩
  cases he

/-- Live-image binding of the lens bytes to `mem0`'s captured global. -/
theorem liveImage : LiveSliceImage mem0 wide4 bytes16 := ⟨arrAlloc, rfl, rfl⟩

/-- Child-tag `split_at_mut(2)` reborrow (`ActiveTypedSliceMutBorrow.splitAt_reborrow`) and
Tree Borrows table-transition frame preservation (`write_elem_treeBorrows_frame`,
`write_elem_conflictingBorrows_frame`, `write_elem_treeBorrows_shared_frame`), plus negative
invalidated-borrow canary (`foreign_overlapping_write_disables_borrow`). -/
def rootSlEntry : BorrowEntry :=
  { tag := 77, targetLocal := 0, targetProjection := [], perm := .unique,
    rangeOffset := 0, rangeLen := 16 }

def splitChildBorrows : List BorrowEntry :=
  reborrowSubsliceEntry rootSlEntry 79 8 ((4 - 2) * 4) ::
    reborrowSubsliceEntry rootSlEntry 78 0 (2 * 4) :: slBorrows

theorem mutLens_split_reborrow_and_treeBorrows_transitions :
    let borrowsAfterLeft :=
      invalidateTreeBorrowsAtProj splitChildBorrows splitChildBorrows 0 (some 78) [] 4 4
    let borrowsAfterConf :=
      invalidateConflictingBorrowsAtProj splitChildBorrows 0 (some 78) [] 4 4
    ActiveTypedSliceMutBorrow ByteLensCodec.u32LE borrowsAfterLeft 78
        (WidePtrVal.takeElems wide4 2) [u 1, u 20] bytesW1 ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE borrowsAfterLeft 79
        (WidePtrVal.dropElems wide4 4 2) [u 3, u 4] bytesW1 ∧
      ActiveTypedSliceBorrow ByteLensCodec.u32LE borrowsAfterLeft 79
        (WidePtrVal.dropElems wide4 4 2) [u 3, u 4] bytesW1 ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE borrowsAfterConf 78
        (WidePtrVal.takeElems wide4 2) [u 1, u 20] bytesW1 ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE borrowsAfterConf 79
        (WidePtrVal.dropElems wide4 4 2) [u 3, u 4] bytesW1 ∧
      ¬ ActiveTypedSliceBorrow ByteLensCodec.u32LE
        (invalidateTreeBorrowsAtProj slBorrows slBorrows 0 (some 99) [] 0 4) 77 wide4 xs4 bytes16 := by
  intro borrowsAfterLeft borrowsAfterConf
  obtain ⟨entry, he, hL, hR, hDisj, _, _, _, _⟩ :=
    ActiveTypedSliceMutBorrow.splitAt_reborrow mutLens (tagL := 78) (tagR := 79) (k := 2)
      (by decide) (by decide) rfl rfl
  have hEntry : entry = rootSlEntry := (Option.some.inj he).symm
  subst hEntry
  have hTight79 : ∀ e, lookupBorrow splitChildBorrows 79 = some e →
      e.rangeOffset = (WidePtrVal.dropElems wide4 4 2).1.offsetBytes ∧
        e.rangeLen = (WidePtrVal.dropElems wide4 4 2).2 * 4 ∧ 0 < e.rangeLen := by
    intro e hlk
    cases Option.some.inj hlk
    exact ⟨rfl, rfl, by decide⟩
  obtain ⟨hL_tb, hR_tb⟩ :=
    ActiveTypedSliceMutBorrow.write_elem_treeBorrows_frame 0 [] hL (i := 1) (by decide) (by decide)
      (u 20) write1 hR hTight79 hDisj
  have hR_shared : ActiveTypedSliceBorrow ByteLensCodec.u32LE splitChildBorrows 79
      (WidePtrVal.dropElems wide4 4 2) [u 3, u 4] bytes16 := hR.toShared
  obtain ⟨_, hR_sh_tb⟩ :=
    ActiveTypedSliceMutBorrow.write_elem_treeBorrows_shared_frame 0 [] hL (i := 1) (by decide)
      (by decide) (u 20) write1 hR_shared hTight79 rfl (by decide) hDisj
  obtain ⟨hL_cf, hR_cf⟩ :=
    ActiveTypedSliceMutBorrow.write_elem_conflictingBorrows_frame 0 [] hL (i := 1) (by decide)
      (by decide) (u 20) write1 hR hTight79 hDisj
  have hDis :=
    foreign_overlapping_write_disables_borrow ByteLensCodec.u32LE (borrows := slBorrows)
      (tag := 77) (wTag := 99) (entry := rootSlEntry) 0 [] 0 4 wide4 xs4 bytes16
      rfl rfl rfl (by decide) rfl ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  exact ⟨hL_tb, hR_tb, hR_sh_tb, hL_cf, hR_cf, hDis.1⟩

/-- The table after writing `20` through the left child `78` (element `1`, byte `4`). -/
def borrowsAfterL : List BorrowEntry :=
  invalidateTreeBorrowsAtProj splitChildBorrows splitChildBorrows 0 (some 78) [] 4 4

/-- The table after then writing `30` through the right child `79` (its element `0`, byte `8`). -/
def borrowsAfterLR : List BorrowEntry :=
  invalidateTreeBorrowsAtProj borrowsAfterL borrowsAfterL 0 (some 79) [] 8 4

/-- **End-to-end `split_at_mut` through the trusted Tree Borrows transitions.** Split the
`&mut [u32]` lens on root tag `77` into fresh children `78` / `79` (`splitAt_reborrow`: the
root lens survives and both children descend from it); write `20` through `78` (the sibling
`79` is framed by `write_elem_treeBorrows_frame`, the root is a local ancestor by
`descendant_write_preserves`); write `30` through `79` (now framing `78`). In the final table
both children are still live with their updated halves *and* the root lens on `77` views the
reassembled `[1, 20, 30, 4]`. -/
theorem split_at_mut_tree_borrows_end_to_end :
    ActiveTypedSliceMutBorrow ByteLensCodec.u32LE borrowsAfterLR 77 wide4
        [u 1, u 20, u 30, u 4] bytesW2 ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE borrowsAfterLR 78
        (WidePtrVal.takeElems wide4 2) [u 1, u 20] bytesW2 ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE borrowsAfterLR 79
        (WidePtrVal.dropElems wide4 4 2) [u 30, u 4] bytesW2 := by
  have hw2 : writeTyped ByteLensCodec.u32LE
      (WidePtrVal.elemOffset (WidePtrVal.dropElems wide4 4 2) 4 0) (u 30) bytesW1 =
        some bytesW2 := rfl
  obtain ⟨entry, he, hL2, hR2, hRoot2⟩ :=
    ActiveTypedSliceMutBorrow.splitAt_reborrow_write_both_reassemble 0 [] [] mutLens
      (tagL := 78) (tagR := 79) (k := 2) (i := 1) (j := 0) (vL := u 20) (vR := u 30)
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl write1 hw2
  have hEntry : entry = rootSlEntry := (Option.some.inj he).symm
  subst hEntry
  exact ⟨hRoot2, hL2, hR2⟩

/-- Full-subslice byte-range write frame (`ActiveTypedSliceMutBorrow.write_subrange_treeBorrows_frame`),
`TightBorrowRange.of_invalidateConflictingBorrowsAtProj`,
`isBorrowDescendantOrSelf_invalidateConflictingBorrowsAtProj`, foreign overlapping read freezing
(`foreign_overlapping_read_freezes_unique_borrow`), and ground-MIR `.disabled` / `.frozen` slice
deref UB refutations (`evalPlaceRead_slice_disabled_ub`, `writePlaceValue_slice_frozen_or_disabled_ub`). -/
theorem subrange_write_freeze_and_slice_deref_ub_witness :
    let borrowsSubrange :=
      invalidateTreeBorrowsAtProj splitChildBorrows splitChildBorrows 0 (some 78) [] 0 8
    let borrowsFrz :=
      freezeTreeBorrowsOnReadAtProj slBorrows slBorrows 0 (some 99) [] 0 4 []
    let borrowsDis :=
      invalidateTreeBorrowsAtProj slBorrows slBorrows 0 (some 99) [] 0 4
    let memDis : Memory := { mem0 with borrows := borrowsDis }
    let wide77 : WidePtrVal := WidePtrVal.mk ⟨77, 0⟩ 4
    let locals77 : List LocalSlot := (locals 8).set 1 (.init (WidePtrVal.toValue 8 wide77))
    ActiveTypedSliceMutBorrow ByteLensCodec.u32LE borrowsSubrange 78
        (WidePtrVal.takeElems wide4 2) [u 1, u 20] bytesW1 ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE borrowsSubrange 79
        (WidePtrVal.dropElems wide4 4 2) [u 3, u 4] bytesW1 ∧
      TightBorrowRange
        (invalidateConflictingBorrowsAtProj splitChildBorrows 0 (some 78) [] 0 8)
        79 (WidePtrVal.dropElems wide4 4 2) 4 ∧
      isBorrowDescendantOrSelf
        (invalidateConflictingBorrowsAtProj splitChildBorrows 0 (some 78) [] 0 8) 79 77 = true ∧
      ActiveTypedSliceBorrow ByteLensCodec.u32LE borrowsFrz 77 wide4 xs4 bytes16 ∧
      ¬ ActiveTypedSliceMutBorrow ByteLensCodec.u32LE borrowsFrz 77 wide4 xs4 bytes16 ∧
      evalPlaceRead locals77 { local_ := 1, projection := [.deref] }
        memDis.borrows memDis.globals layouts64 memDis.callerLocals decls = .ub ∧
      writePlaceValue locals77 borrowsFrz { local_ := 1, projection := [.deref] }
        (.scalar ⟨1, 4⟩) decls layouts64 = .ub ∧
      writePlaceValue locals77 borrowsDis { local_ := 1, projection := [.deref] }
        (.scalar ⟨1, 4⟩) decls layouts64 = .ub := by
  intro borrowsSubrange borrowsFrz borrowsDis memDis wide77 locals77
  obtain ⟨entry, he, hL, hR, hDisj, _, _, _, hDescR0⟩ :=
    ActiveTypedSliceMutBorrow.splitAt_reborrow mutLens (tagL := 78) (tagR := 79) (k := 2)
      (by decide) (by decide) rfl rfl
  have hEntry : entry = rootSlEntry := (Option.some.inj he).symm
  subst hEntry
  have hTight79 : TightBorrowRange splitChildBorrows 79 (WidePtrVal.dropElems wide4 4 2) 4 := by
    intro e hlk
    cases Option.some.inj hlk
    exact ⟨rfl, rfl, by decide⟩
  obtain ⟨hL_sub, hR_sub⟩ :=
    ActiveTypedSliceMutBorrow.write_subrange_treeBorrows_frame 0 [] 0 8 hL (i := 1)
      (by decide) (u 20) write1 (by decide) (by decide) (by decide) hR hTight79 hDisj
  have hTightConf : TightBorrowRange
      (invalidateConflictingBorrowsAtProj splitChildBorrows 0 (some 78) [] 0 8)
      79 (WidePtrVal.dropElems wide4 4 2) 4 :=
    hTight79.of_invalidateConflictingBorrowsAtProj 0 (some 78) [] 0 8
  have hDescConf : isBorrowDescendantOrSelf
      (invalidateConflictingBorrowsAtProj splitChildBorrows 0 (some 78) [] 0 8) 79 77 = true := by
    rw [isBorrowDescendantOrSelf_invalidateConflictingBorrowsAtProj]
    exact hDescR0
  obtain ⟨hFrzSh, hFrzNoMut⟩ :=
    foreign_overlapping_read_freezes_unique_borrow ByteLensCodec.u32LE 0 [] 0 4 mutLens
      (entry := rootSlEntry) (rTag := 99) rfl rfl rfl rfl rfl
  have hReadDisUb : evalPlaceRead locals77 { local_ := 1, projection := [.deref] }
      memDis.borrows memDis.globals layouts64 memDis.callerLocals decls = .ub :=
    evalPlaceRead_slice_disabled_ub locals77 1 [] wide77 8
      { rootSlEntry with perm := .disabled } memDis decls layouts64 (.uint .u32) 2
      rfl rfl rfl rfl
  have hWriteFrzUb : writePlaceValue locals77 borrowsFrz { local_ := 1, projection := [.deref] }
      (.scalar ⟨1, 4⟩) decls layouts64 = .ub :=
    writePlaceValue_slice_frozen_or_disabled_ub locals77 1 [] wide77 8
      { rootSlEntry with perm := .frozen } borrowsFrz (.scalar ⟨1, 4⟩)
      decls layouts64 rfl rfl (Or.inl rfl)
  have hWriteDisUb : writePlaceValue locals77 borrowsDis { local_ := 1, projection := [.deref] }
      (.scalar ⟨1, 4⟩) decls layouts64 = .ub :=
    writePlaceValue_slice_frozen_or_disabled_ub locals77 1 [] wide77 8
      { rootSlEntry with perm := .disabled } borrowsDis (.scalar ⟨1, 4⟩)
      decls layouts64 rfl rfl (Or.inr rfl)
  exact ⟨hL_sub, hR_sub, hTightConf, hDescConf, hFrzSh, hFrzNoMut, hReadDisUb,
    hWriteFrzUb, hWriteDisUb⟩

/-- Negative (why `splitAt_reborrow` demands fresh child tags): minting the left child on the
parent's own live tag `77` shadows the root entry, and the root `&mut [u32]` lens on the whole
16-byte window is lost. -/
theorem shadowing_child_destroys_root_lens :
    ¬ ActiveTypedSliceMutBorrow ByteLensCodec.u32LE
      (reborrowSubsliceEntry rootSlEntry 77 0 (2 * 4) :: slBorrows) 77 wide4 xs4 bytes16 := by
  rintro ⟨_, entry, he, hc, _⟩
  cases he
  exact absurd hc.2 (by decide)

/-! ### `split_at_mut` through the trusted deref-write borrow update -/

/-- Fat pointers of the two `split_at_mut` children (64-bit): `_5 : &mut [u32]` for the left
half (tag `78`, byte `0`) and `_6` for the right half (tag `79`, byte `8`). -/
def childFatL : Value := WidePtrVal.toValue 8 (WidePtrVal.mk ⟨78, 0⟩ 2)

def childFatR : Value := WidePtrVal.toValue 8 (WidePtrVal.mk ⟨79, 8⟩ 2)

def childLocals : List LocalSlot := locals 8 ++ [.init childFatL, .init childFatR]

def derefDstL : Place := { local_ := 5, projection := [.deref, .constantIndex 1 0 false] }

def derefDstR : Place := { local_ := 6, projection := [.deref, .constantIndex 0 0 false] }

/-- The borrow table after the trusted deref write `(*_5)[1] = 20`. -/
def derefBorrowsL : List BorrowEntry :=
  invalidateDerefWriteBorrows childLocals splitChildBorrows derefDstL [.constantIndex 1 0 false] []

/-- The borrow table after the trusted deref write `(*_6)[0] = 30`. -/
def derefBorrowsLR : List BorrowEntry :=
  invalidateDerefWriteBorrows childLocals derefBorrowsL derefDstR [.constantIndex 0 0 false] []

/-- **`split_at_mut` through the trusted deref-write borrow update.** The same two writes as
`split_at_mut_tree_borrows_end_to_end`, but each borrow transition is the one the trusted
assignment path performs, `invalidateDerefWriteBorrows` on the child's fat pointer (which
invalidates over the writer entry's whole range): both children stay live with their updated
halves, and the root lens on `77` views the reassembled `[1, 20, 30, 4]`. -/
theorem split_at_mut_trusted_deref_writes :
    ActiveTypedSliceMutBorrow ByteLensCodec.u32LE derefBorrowsLR 77 wide4
        [u 1, u 20, u 30, u 4] bytesW2 ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE derefBorrowsLR 78
        (WidePtrVal.takeElems wide4 2) [u 1, u 20] bytesW2 ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE derefBorrowsLR 79
        (WidePtrVal.dropElems wide4 4 2) [u 30, u 4] bytesW2 := by
  have hw2 : writeTyped ByteLensCodec.u32LE
      (WidePtrVal.elemOffset (WidePtrVal.dropElems wide4 4 2) 4 0) (u 30) bytesW1 =
        some bytesW2 := rfl
  obtain ⟨entry, he, hL2, hR2, hRoot2⟩ :=
    ActiveTypedSliceMutBorrow.splitAt_reborrow_derefWrite_both_reassemble childLocals childLocals
      derefDstL derefDstR [.constantIndex 1 0 false] [.constantIndex 0 0 false] [] []
      childFatL childFatR ⟨78, 0⟩ ⟨79, 8⟩ mutLens
      (tagL := 78) (tagR := 79) (k := 2) (i := 1) (j := 0) (vL := u 20) (vR := u 30)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl write1 hw2
  have hEntry : entry = rootSlEntry := (Option.some.inj he).symm
  subst hEntry
  exact ⟨hRoot2, hL2, hR2⟩

/-- Live backing `[u32; 4]` local `_0` so `writePlaceValue` and `evalStmt` succeed on `(*_5)[1]`
and `(*_6)[0]` (whereas `childLocals` had `_0 = .uninit`, on which `writePlaceValue` faults with
`.ub`), paired with `invalidateDerefWriteBorrowsWithLayouts` (the borrow update `evalStmt`
actually executes on deref assignments). -/
def liveChildLocals : List LocalSlot :=
  (childLocals.set 0 (.init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩])))

def derefWithLayoutsBorrowsL : List BorrowEntry :=
  invalidateDerefWriteBorrowsWithLayouts [] emptyLayoutTable liveChildLocals splitChildBorrows
    derefDstL [.constantIndex 1 0 false]

def derefWithLayoutsBorrowsLR : List BorrowEntry :=
  invalidateDerefWriteBorrowsWithLayouts [] emptyLayoutTable liveChildLocals
    derefWithLayoutsBorrowsL derefDstR [.constantIndex 0 0 false]

theorem split_at_mut_evalStmt_withLayouts_end_to_end :
    writePlaceValue childLocals splitChildBorrows derefDstL (.scalar ⟨20, 4⟩) = .ub ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE derefWithLayoutsBorrowsLR 77 wide4
        [u 1, u 20, u 30, u 4] bytesW2 ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE derefWithLayoutsBorrowsLR 78
        (WidePtrVal.takeElems wide4 2) [u 1, u 20] bytesW2 ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE derefWithLayoutsBorrowsLR 79
        (WidePtrVal.dropElems wide4 4 2) [u 30, u 4] bytesW2 ∧
      (let s₀ : MachineState :=
         { frame := { blockIdx := 0, stmtIdx := 0, locals := liveChildLocals }
           memory := { borrows := splitChildBorrows } }
       let stmtL : Statement :=
         { kind := .assign derefDstL (.use (Anneal.MirLoops.constU32 20))
           span := "write_left" }
       evalStmt s₀ stmtL =
         MirStepNode.step
           { frame :=
               { blockIdx := 0, stmtIdx := 1
                 locals := liveChildLocals.set 0
                   (.init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩])) }
             memory := { borrows := derefWithLayoutsBorrowsL } }) := by
  have hw2 : writeTyped ByteLensCodec.u32LE
      (WidePtrVal.elemOffset (WidePtrVal.dropElems wide4 4 2) 4 0) (u 30) bytesW1 =
        some bytesW2 := rfl
  obtain ⟨entry, he, hL2, hR2, hRoot2⟩ :=
    ActiveTypedSliceMutBorrow.splitAt_reborrow_derefWriteWithLayouts_both_reassemble []
      emptyLayoutTable liveChildLocals liveChildLocals derefDstL derefDstR
      [.constantIndex 1 0 false] [.constantIndex 0 0 false]
      childFatL childFatR ⟨78, 0⟩ ⟨79, 8⟩ mutLens
      (tagL := 78) (tagR := 79) (k := 2) (i := 1) (j := 0) (vL := u 20) (vR := u 30)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl write1 hw2
  have hEntry : entry = rootSlEntry := (Option.some.inj he).symm
  subst hEntry
  exact ⟨rfl, hRoot2, hL2, hR2, rfl⟩

/-! ### The connected trusted run: lens bytes = trusted image of the written backing array -/

/-- The backing array `_0` before the writes, after `(*_5)[1] = 20`, and after `(*_6)[0] = 30`. -/
def backing0 : Value := .aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]

def backingL : Value := .aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]

def backingLR : Value :=
  .aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨4, 4⟩]

def splitStmtL : Statement :=
  { kind := .assign derefDstL (.use (Anneal.MirLoops.constU32 20)), span := "write_left" }

def splitStmtR : Statement :=
  { kind := .assign derefDstR (.use (Anneal.MirLoops.constU32 30)), span := "write_right" }

/-- A MIR body executing both `split_at_mut` writes and returning the backing array `_0`. -/
def splitWriterMir : CapturedMir :=
  Anneal.MirLoops.mkMirBody "split::writer" 0 []
    [{ statements := [splitStmtL, splitStmtR], terminator := { kind := .return_, span := "ret" },
       isCleanup := false }]

/-- The post-split machine state: live backing array, child fat pointers in `_5` / `_6`, and
the split borrow table. -/
def splitRunS0 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := liveChildLocals }
    memory := { borrows := splitChildBorrows } }

/-- **Connected trusted `split_at_mut` run.** The lens facts are about the *trusted run*, not a
side buffer: the initial backing array encodes (trusted `encodeUntypedValueToBytes`) to the
initial lens buffer `bytes16`; the trusted bounded evaluator runs both writes through
`evalStmt` (data written into `_0`, borrows updated by `invalidateDerefWriteBorrowsWithLayouts`)
and returns the final backing array with final borrow table `derefWithLayoutsBorrowsLR`; that
array encodes to `bytesW2` and decodes back from it at `[u32; 4]`; and over exactly `bytesW2` in
exactly that table, the root lens views the reassembled `[1, 20, 30, 4]` while both child lenses
stay live. -/
theorem split_at_mut_trusted_run_connected :
    get? splitRunS0.frame.locals 0 = some (.init backing0) ∧
      encodeUntypedValueToBytes defaultCodecFuel backing0 = some bytes16 ∧
      evalStmt splitRunS0 splitStmtL =
        MirStepNode.step
          { frame := { blockIdx := 0, stmtIdx := 1, locals := liveChildLocals.set 0 (.init backingL) }
            memory := { borrows := derefWithLayoutsBorrowsL } } ∧
      encodeUntypedValueToBytes defaultCodecFuel backingL = some bytesW1 ∧
      Anneal.MirFuelFree.runMirExecBounded 4 splitWriterMir (.running splitRunS0) =
        some (.normal (backingLR, { borrows := derefWithLayoutsBorrowsLR })) ∧
      encodeUntypedValueToBytes defaultCodecFuel backingLR = some bytesW2 ∧
      decodeValueFromBytes defaultCodecFuel layouts64 { kind := .array (.uint .u32) 4, layoutIdx := 0 }
        bytesW2 = some backingLR ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE derefWithLayoutsBorrowsLR 77 wide4
        [u 1, u 20, u 30, u 4] bytesW2 ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE derefWithLayoutsBorrowsLR 78
        (WidePtrVal.takeElems wide4 2) [u 1, u 20] bytesW2 ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE derefWithLayoutsBorrowsLR 79
        (WidePtrVal.dropElems wide4 4 2) [u 30, u 4] bytesW2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, split_at_mut_evalStmt_withLayouts_end_to_end.2.1,
    split_at_mut_evalStmt_withLayouts_end_to_end.2.2.1,
    split_at_mut_evalStmt_withLayouts_end_to_end.2.2.2.1⟩

/-- Child wide pointers carrying their own borrow tags `78` and `79`. -/
def wideL78 : WidePtrVal := WidePtrVal.mk ⟨78, 0⟩ 2

def wideR79 : WidePtrVal := WidePtrVal.mk ⟨79, 8⟩ 2

def rootWide77 : WidePtrVal := WidePtrVal.mk ⟨77, 0⟩ 4

@[reducible]
def u32ToVal (x : U32) : Value := .scalar ⟨x.val, 4⟩

/-- Local declarations for borrow-backed slice `len` and checked index reads on `_5` (`tag = 78`)
and `_6` (`tag = 79`), with index locals `_7 = 1usize` and `_8 = 0usize`. -/
def splitDecls : List LocalDecl :=
  [{ mutability := .mut, ty := { kind := .array (.uint .u32) 4, layoutIdx := 0 }, debugName := none },
   { mutability := .not, ty := { kind := .ref .not (.slice (.uint .u32)), layoutIdx := 1 },
     debugName := none },
   { mutability := .not, ty := { kind := .uint .usize, layoutIdx := 0 }, debugName := none },
   { mutability := .not, ty := { kind := .ref .not (.array (.uint .u32) 4), layoutIdx := 1 },
     debugName := none },
   { mutability := .not, ty := { kind := .ref .mut (.slice (.uint .u32)), layoutIdx := 1 },
     debugName := none },
   { mutability := .not, ty := { kind := .ref .mut (.slice (.uint .u32)), layoutIdx := 1 },
     debugName := none },
   { mutability := .not, ty := { kind := .ref .mut (.slice (.uint .u32)), layoutIdx := 1 },
     debugName := none },
   { mutability := .not, ty := { kind := .uint .usize, layoutIdx := 0 }, debugName := none },
   { mutability := .not, ty := { kind := .uint .usize, layoutIdx := 0 }, debugName := none }]

def postSplitReadLocals : List LocalSlot :=
  (liveChildLocals.set 0 (.init backingLR)) ++ [.init (.scalar ⟨1, 8⟩), .init (.scalar ⟨0, 8⟩)]

def postSplitMem : Memory := { borrows := derefWithLayoutsBorrowsLR }

/-- **Symbolic `encodeElems`, `writePlaceValue`, `len_eq_borrow`, and `evalPlaceRead_index_borrow`
bridges** on the `split_at_mut` state (`encodeUntypedValueToBytes_uintLE`,
`encodeUntypedValueToBytes_aggregate_map`, `sliceTypedAt_encodeElems`, `writeTyped_encodeElems_set`,
`ActiveTypedSliceMutBorrow.writePlaceValue_constantIndex_encodeElems_connected`,
`ActiveTypedSliceBorrow.len_eq_borrow`, and `ActiveTypedSliceBorrow.evalPlaceRead_index_borrow`). -/
theorem split_at_mut_symbolic_encodeElems_and_borrow_bridges :
    encodeUntypedValueToBytes defaultCodecFuel (.aggregate 0 (xs4.map u32ToVal)) =
        some (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) ∧
      SliceTypedAt ByteLensCodec.u32LE wide4 xs4
        (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) ∧
      writeTyped ByteLensCodec.u32LE 4 (u 20)
          (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) =
        some (ByteLensCodec.encodeElems ByteLensCodec.u32LE (xs4.set 1 (u 20))) ∧
      writePlaceValue liveChildLocals splitChildBorrows derefDstL (u32ToVal (u 20))
          [] emptyLayoutTable =
        .ok (liveChildLocals.set 0 (.init (.aggregate 0 ((xs4.set 1 (u 20)).map u32ToVal)))) ∧
      evalRvalue postSplitReadLocals (.len { local_ := 5, projection := [.deref] })
          postSplitMem splitDecls layouts64 =
        .ok (.scalar ⟨2, 8⟩) postSplitReadLocals postSplitMem ∧
      evalRvalue postSplitReadLocals (.unaryOp .ptrMetadata (.copy { local_ := 5, projection := [] }))
          postSplitMem splitDecls layouts64 =
        .ok (.scalar ⟨2, 8⟩) postSplitReadLocals postSplitMem ∧
      evalPlaceRead postSplitReadLocals { local_ := 5, projection := [.deref, .index 7] }
          postSplitMem.borrows postSplitMem.globals layouts64 postSplitMem.callerLocals splitDecls =
        .ok (.scalar ⟨20, 4⟩) postSplitReadLocals ∧
      evalPlaceRead postSplitReadLocals { local_ := 6, projection := [.deref, .index 8] }
          postSplitMem.borrows postSplitMem.globals layouts64 postSplitMem.callerLocals splitDecls =
        .ok (.scalar ⟨30, 4⟩) postSplitReadLocals := by
  have hEncElem : ∀ x : U32,
      encodeUntypedValueToBytes 15 (u32ToVal x) = some (ByteLensCodec.u32LE.encode x) :=
    fun x => encodeUntypedValueToBytes_uintLE (sz := 4) (by decide) 14 x
  have hBytes16Eq : ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4 = bytes16 := rfl
  obtain ⟨entry0, he0, hL_reb, hR_reb, _, hRoot_reb, _, _, _⟩ :=
    ActiveTypedSliceMutBorrow.splitAt_reborrow mutLens (tagL := 78) (tagR := 79) (k := 2)
      (by decide) (by decide) rfl rfl
  have hEntry0 : entry0 = rootSlEntry := (Option.some.inj he0).symm
  subst hEntry0
  have hL0 : ActiveTypedSliceMutBorrow ByteLensCodec.u32LE splitChildBorrows 78 wideL78
      [u 1, u 2] (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) := by
    rw [hBytes16Eq]
    exact ⟨hL_reb.1, hL_reb.2⟩
  have hR0 : ActiveTypedSliceMutBorrow ByteLensCodec.u32LE splitChildBorrows 79 wideR79
      [u 3, u 4] (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) := by
    rw [hBytes16Eq]
    exact ⟨hR_reb.1, hR_reb.2⟩
  have hRoot0 : ActiveTypedSliceMutBorrow ByteLensCodec.u32LE splitChildBorrows 77 rootWide77
      xs4 (ByteLensCodec.encodeElems ByteLensCodec.u32LE xs4) := by
    rw [hBytes16Eq]
    exact ⟨hRoot_reb.1, hRoot_reb.2⟩
  have hTightL : TightBorrowRange splitChildBorrows 78 wideL78 4 := by
    intro e hlk
    have hEq : some e = some (reborrowSubsliceEntry rootSlEntry 78 0 8) := hlk.symm
    cases hEq
    exact ⟨rfl, rfl, by decide⟩
  have hTightR : TightBorrowRange splitChildBorrows 79 wideR79 4 := by
    intro e hlk
    have hEq : some e = some (reborrowSubsliceEntry rootSlEntry 79 8 8) := hlk.symm
    cases hEq
    exact ⟨rfl, rfl, by decide⟩
  have hConn :=
    ActiveTypedSliceMutBorrow.writePlaceValue_constantIndex_encodeElems_connected u32ToVal 15
      hEncElem liveChildLocals 5 1 0 (u 20) [] emptyLayoutTable none none
      (reborrowSubsliceEntry rootSlEntry 78 0 8) hL0 hTightL hR0 hTightR
      (DisjointSlice.adjacent 0 8 8) hRoot0 rfl rfl (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
  have hLPost : ActiveTypedSliceBorrow ByteLensCodec.u32LE postSplitMem.borrows wideL78.1.tag
      wideL78 [u 1, u 20] bytesW2 := by
    have hMut := split_at_mut_evalStmt_withLayouts_end_to_end.2.2.1.toShared
    exact ⟨hMut.1, hMut.2⟩
  have hRPost : ActiveTypedSliceBorrow ByteLensCodec.u32LE postSplitMem.borrows wideR79.1.tag
      wideR79 [u 30, u 4] bytesW2 := by
    have hMut := split_at_mut_evalStmt_withLayouts_end_to_end.2.2.2.1.toShared
    exact ⟨hMut.1, hMut.2⟩
  have hLenL := ActiveTypedSliceBorrow.len_eq_borrow hLPost postSplitReadLocals postSplitReadLocals
    { local_ := 5, projection := [.deref] } (.copy { local_ := 5, projection := [] })
    splitDecls layouts64 [] (.uint .u32) 0
    { (reborrowSubsliceEntry rootSlEntry 78 0 8) with perm := .unique }
    ([u 1, u 20, u 30, u 4].map u32ToVal) 0 rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
  have hReadL := ActiveTypedSliceBorrow.evalPlaceRead_index_borrow
    (backingXs := [u 1, u 20, u 30, u 4]) hLPost u32ToVal
    postSplitReadLocals 5 7 1 8 0 splitDecls layouts64 (.uint .u32) 2
    (some { kind := .uint .u32, layoutIdx := 0 })
    { (reborrowSubsliceEntry rootSlEntry 78 0 8) with perm := .unique }
    (by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl
  have hReadR := ActiveTypedSliceBorrow.evalPlaceRead_index_borrow
    (backingXs := [u 1, u 20, u 30, u 4]) hRPost u32ToVal
    postSplitReadLocals 6 8 0 8 2 splitDecls layouts64 (.uint .u32) 2
    (some { kind := .uint .u32, layoutIdx := 0 })
    { (reborrowSubsliceEntry rootSlEntry 79 8 8) with perm := .unique }
    (by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl
  exact ⟨hConn.1, sliceTypedAt_encodeElems ByteLensCodec.u32LE 9 xs4,
    writeTyped_encodeElems_set ByteLensCodec.u32LE xs4 (idx := 1) (by decide) (u 20),
    hConn.2.1, hLenL.1, hLenL.2, hReadL, hReadR⟩

/-! ### One live `&mut [u32]`: trusted write, single-entry borrow update, and lens -/

/-- One live `&mut [u32]` (tag `77`, the only borrow entry, over the whole backing array `_0`),
held in `_5` as a 64-bit fat pointer. -/
def singleFat : Value := WidePtrVal.toValue 8 (WidePtrVal.mk ⟨77, 0⟩ 4)

def singleLocals : List LocalSlot := liveChildLocals.set 5 (.init singleFat)

def singleDst : Place := { local_ := 5, projection := [.deref, .constantIndex 2 0 false] }

def singleState : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := singleLocals }
    memory := { borrows := slBorrows } }

def singleStmt : Statement :=
  { kind := .assign singleDst (.use (Anneal.MirLoops.constU32 30)), span := "single_write" }

def backingS : Value :=
  .aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨4, 4⟩]

def singleBorrowsAfter : List BorrowEntry :=
  invalidateDerefWriteBorrowsWithLayouts [] emptyLayoutTable singleLocals slBorrows singleDst
    [.constantIndex 2 0 false]

/-- **Single-borrow trusted write, connected** (the one-entry case every `2 ≤ borrows.length`
deref-write bridge excludes). The trusted `evalStmt` of `(*_5)[2] = 30u32` through the only live
`&mut [u32]` writes `30` into the backing array and updates the one-entry borrow table by
`invalidateDerefWriteBorrowsWithLayouts`; the new backing array encodes to
`encodeElems (xs4.set 2 30)`, and in the updated table the lens on tag `77` views exactly
`[1, 2, 30, 4]` over those bytes (`derefWriteWithLayouts_single`), still with unique-write
permission. -/
theorem single_borrow_trusted_write_connected :
    evalStmt singleState singleStmt =
        MirStepNode.step
          { frame := { blockIdx := 0, stmtIdx := 1, locals := singleLocals.set 0 (.init backingS) }
            memory := { borrows := singleBorrowsAfter } } ∧
      encodeUntypedValueToBytes defaultCodecFuel backingS =
        some (ByteLensCodec.encodeElems ByteLensCodec.u32LE (xs4.set 2 (u 30))) ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u32LE singleBorrowsAfter 77 wide4 (xs4.set 2 (u 30))
        (ByteLensCodec.encodeElems ByteLensCodec.u32LE (xs4.set 2 (u 30))) ∧
      (lookupBorrow singleBorrowsAfter 77).map BorrowEntry.perm = some .unique := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  have hTight : TightBorrowRange slBorrows 77 wide4 4 := by
    intro e hlk
    cases Option.some.inj hlk
    exact ⟨rfl, rfl, by decide⟩
  exact ActiveTypedSliceMutBorrow.derefWriteWithLayouts_single [] emptyLayoutTable singleLocals
    singleDst [.constantIndex 2 0 false] singleFat ⟨77, 0⟩ rfl rfl rfl mutLens hTight (i := 2)
    (by decide) (u 30) rfl

/-- 32-bit edge case (trusted-semantics observation, no trusted edit): the trusted
`writePlaceValue` accepts only 8-byte fat pointers, so on a 32-bit target the element write
`(*_5)[1] = 20u32` through a live child `&mut [u32]` (4-byte words) is `.ub`, while the same
write through the 64-bit fat pointer succeeds. -/
theorem writePlaceValue_32bit_fat_ptr_ub :
    writePlaceValue
        (liveChildLocals.set 5 (.init (WidePtrVal.toValue 4 (WidePtrVal.mk ⟨78, 0⟩ 2))))
        splitChildBorrows derefDstL (.scalar ⟨20, 4⟩) [] layouts32 = .ub ∧
      writePlaceValue liveChildLocals splitChildBorrows derefDstL (.scalar ⟨20, 4⟩) []
          emptyLayoutTable =
        .ok (liveChildLocals.set 0 (.init backingL)) :=
  ⟨rfl, rfl⟩

/-- Negative: replaying the right write on the *pre-split* table, where `79` has no entry,
leaves the borrow table untouched (`invalidateDerefWriteBorrowsWithLayouts` is the identity
without a writer entry), so the root never sees a child access through an unknown tag. -/
theorem deref_write_unknown_tag_is_identity :
    invalidateDerefWriteBorrowsWithLayouts [] emptyLayoutTable liveChildLocals
      (rootSlEntry :: { rootSlEntry with tag := 90 } :: []) derefDstR [.constantIndex 0 0 false] =
        rootSlEntry :: { rootSlEntry with tag := 90 } :: [] :=
  rfl

/-- The trusted deref write through `_5` really transitions the table (the left child's
`.reservedFrz false` is activated to `.unique`), so the theorem above is not about an identity
update. -/
theorem deref_write_activates_child :
    (lookupBorrow derefBorrowsL 78).map BorrowEntry.perm = some .unique ∧
      (lookupBorrow splitChildBorrows 78).map BorrowEntry.perm = some (.reservedFrz false) :=
  ⟨rfl, rfl⟩

/-- 32-bit edge case (trusted-semantics observation, no trusted edit): `extractDerefPtrVal?`
recognizes only 8-byte fat pointers, so on a 32-bit target a deref write through a
`&mut [u32]` fat pointer leaves the borrow table unchanged; no Tree Borrows transition is
applied to the writer, its siblings, or its ancestors. -/
theorem derefWrite_32bit_fat_ptr_skips_invalidation :
    extractDerefPtrVal? (WidePtrVal.toValue 4 (WidePtrVal.mk ⟨78, 0⟩ 2)) = none ∧
      invalidateDerefWriteBorrows
          (locals 4 ++ [.init (WidePtrVal.toValue 4 (WidePtrVal.mk ⟨78, 0⟩ 2))])
          splitChildBorrows { local_ := 5, projection := [.deref, .constantIndex 1 0 false] }
          [.constantIndex 1 0 false] [] = splitChildBorrows :=
  ⟨rfl, rfl⟩

/-! ## 7. Empty and zero-sized slices -/

/-- An empty slice one-past-the-end of the allocation. -/
theorem empty_slice_view :
    SliceTypedAt ByteLensCodec.u32LE (WidePtrVal.mk ⟨9, 16⟩ 0) [] bytes16 :=
  sliceTypedAt_empty _ _ _ (by decide)

/-- `Len(*s)` of the empty slice is `0` in the trusted semantics. -/
theorem empty_slice_len :
    evalRvalue ((locals 8).set 1 (.init (WidePtrVal.toValue 8 (WidePtrVal.mk ⟨9, 16⟩ 0))))
        (.len { local_ := 1, projection := [.deref] }) mem0 decls layouts64 =
      .ok (.scalar ⟨0, 8⟩) ((locals 8).set 1 (.init (WidePtrVal.toValue 8 (WidePtrVal.mk ⟨9, 16⟩ 0))))
        mem0 :=
  (SliceTypedAt.len_eq empty_slice_view _ _ { local_ := 1, projection := [.deref] }
    (.copy { local_ := 1, projection := [] }) mem0 decls layouts64 [] (.uint .u32) 0
    rfl rfl rfl rfl rfl rfl rfl).1

/-- Negative: an empty slice *past* the end (offset `17 > 16`) has no view. -/
theorem empty_slice_past_end_refuted :
    ¬ SliceTypedAt ByteLensCodec.u32LE (WidePtrVal.mk ⟨9, 17⟩ 0) [] bytes16 := by
  intro h
  have hb := h.window_le
  rw [bytes16_length] at hb
  exact absurd hb (by decide)

/-- A ZST slice of five `()` at the very end of the allocation (no byte consumed). -/
theorem zst_slice_view :
    SliceTypedAt ByteLensCodec.unit (WidePtrVal.mk ⟨9, 16⟩ 5) (List.replicate 5 ()) bytes16 :=
  sliceTypedAt_unit_replicate _ _ _ (by decide)

/-- ZST `split_at_mut(3)`: both halves share the same byte offset and are disjoint. -/
theorem zst_split :
    SliceTypedAt ByteLensCodec.unit (WidePtrVal.dropElems (WidePtrVal.mk ⟨9, 16⟩ 5) 0 3)
        ((List.replicate 5 ()).drop 3) bytes16 ∧
      (WidePtrVal.dropElems (WidePtrVal.mk ⟨9, 16⟩ 5) 0 3).1.offsetBytes = 16 :=
  ⟨(SliceTypedAt.splitAt zst_slice_view (k := 3) (by decide)).2.1, rfl⟩

/-- ZST element write: a zero-width write at any element is a no-op on the bytes. -/
theorem zst_write_elem :
    SliceTypedAt ByteLensCodec.unit (WidePtrVal.mk ⟨9, 16⟩ 5) ((List.replicate 5 ()).set 4 ())
      bytes16 :=
  SliceTypedAt.write_elem zst_slice_view (i := 4) (by decide) () (writeTyped_zero_width _ _ _ _)

/-- Negative: a ZST slice cannot start past the end of the allocation. -/
theorem zst_past_end_refuted :
    ¬ SliceTypedAt ByteLensCodec.unit (WidePtrVal.mk ⟨9, 17⟩ 5) (List.replicate 5 ()) bytes16 := by
  intro h
  have hb := h.window_le
  rw [bytes16_length] at hb
  exact absurd hb (by decide)

/-! ## 8. Call-cone narrowing on a 3-callee program -/

def coneU32 : Ty := { kind := .uint .u32, layoutIdx := 0 }

def retLocal : LocalDecl := { mutability := .mut, ty := coneU32, debugName := some "_0" }

def fnItem (dp : String) : Operand :=
  .constant { ty := { kind := .fnDef dp [], layoutIdx := 0 }, val := .zeroSized }

/-- `_dst = const v_u32`. -/
def assignConst (dst v : Nat) : Statement :=
  { kind := .assign { local_ := dst, projection := [] } (.use (Anneal.MirLoops.constU32 v)),
    span := "const" }

/-- `_dst = move _src`. -/
def assignMove (dst src : Nat) : Statement :=
  { kind := .assign { local_ := dst, projection := [] } (.use (.move { local_ := src, projection := [] })),
    span := "move" }

/-- A block running `stmts` then returning. -/
def retBlock (stmts : List Statement) : BasicBlockData :=
  { statements := stmts, terminator := { kind := .return_, span := "ret" }, isCleanup := false }

/-- A block calling `func()` into `_dst`, continuing at `target`. -/
def callTerm (func : Operand) (dst target : Nat) : Terminator :=
  { kind := .call func [] { local_ := dst, projection := [] } (some target) .continue_
    span := "call" }

/-- A block calling `func()` into `_dst`, continuing at `target`. -/
def callBlock (func : Operand) (dst target : Nat) : BasicBlockData :=
  { statements := [], terminator := callTerm func dst target, isCleanup := false }

/-- `helper1() -> u32 { 42 }`. -/
def helper1Mir : CapturedMir :=
  Anneal.MirLoops.mkMirBody "cone::helper1" 0 [retLocal] [retBlock [assignConst 0 42]]

/-- A shadowing duplicate entry for `cone::helper1` (an extra unused local; returns `7`). -/
def helper1ShadowMir : CapturedMir :=
  Anneal.MirLoops.mkMirBody "cone::helper1" 0
    [retLocal, { mutability := .not, ty := coneU32, debugName := some "x" }]
    [retBlock [assignConst 0 7]]

/-- A `fn() -> u32` local. -/
def fnPtrLocal : LocalDecl :=
  { mutability := .mut, ty := { kind := .fnPtr [] (.uint .u32) .safe .rust, layoutIdx := 0 },
    debugName := some "f" }

/-- `heavyCallee2`: calls through a function pointer held in `_1` (indirect). -/
def heavy2Mir : CapturedMir :=
  Anneal.MirLoops.mkMirBody "cone::heavyCallee2" 0
    [retLocal, fnPtrLocal]
    [callBlock (.move { local_ := 1, projection := [] }) 0 1, retBlock []]

/-- `heavyCallee3`: calls `heavyCallee2` (outside the cone). -/
def heavy3Mir : CapturedMir :=
  Anneal.MirLoops.mkMirBody "cone::heavyCallee3" 0 [retLocal]
    [callBlock (fnItem "cone::heavyCallee2") 0 1, retBlock []]

/-- `caller() -> u32 { let t = helper1(); t }` (`StorageLive(t)` precedes the call: the
trusted semantics initializes non-argument locals as `.dead`, and writing a callee's return
value into a dead destination is UB). -/
def callerMir : CapturedMir :=
  Anneal.MirLoops.mkMirBody "cone::caller" 0
    [retLocal, { mutability := .mut, ty := coneU32, debugName := some "t" }]
    [{ statements := [{ kind := .storageLive 1, span := "live" }],
       terminator := callTerm (fnItem "cone::helper1") 1 1, isCleanup := false },
     retBlock [assignMove 0 1]]

/-- The full callee table (the cone member is *not* first). -/
def fullCallees : CalleeEnv := [heavy2Mir, helper1Mir, heavy3Mir]

def cone1 : List DefPath := ["cone::helper1"]

theorem callConeClosed_caller : CallConeClosed cone1 callerMir fullCallees = true := rfl

theorem coneBodies_fullCallees : coneBodies cone1 fullCallees = [helper1Mir] := rfl

theorem fullCallees_ne_nil : fullCallees ≠ [] := by intro h; cases h

theorem narrowCallees_ne_nil : coneBodies cone1 fullCallees ≠ [] := by
  rw [coneBodies_fullCallees]; intro h; cases h

/-- The narrowed table agrees with the full one on the cone. -/
theorem cone_agree : calleesAgreeOn cone1 fullCallees (coneBodies cone1 fullCallees) :=
  calleesAgreeOn_coneBodies cone1 fullCallees

/-- Return value of a bounded run. -/
def retVal? : Option MirOutcome → Option Value
  | some (.normal (v, _)) => some v
  | _ => none

/-- Concrete runs: both the full and the narrowed table return `42u32`. -/
theorem runs_concrete :
    retVal? (runCfgWithCallees 8 callerMir [] emptyMemory fullCallees) = some (.scalar ⟨42, 4⟩) ∧
      retVal? (runCfgWithCallees 8 callerMir [] emptyMemory [helper1Mir]) =
        some (.scalar ⟨42, 4⟩) :=
  ⟨rfl, rfl⟩

theorem run_some_of_retVal {o : Option MirOutcome} {v : Value} (h : retVal? o = some v) :
    ∃ m, o = some (.normal (v, m)) := by
  match o, h with
  | some (.normal (v', m)), h =>
    cases h
    exact ⟨m, rfl⟩

/-- **`runCfgWithCallees_cone_narrow_of_closed`** on the 3-callee program. -/
theorem run_narrow :
    runCfgWithCallees 8 callerMir [] emptyMemory (coneBodies cone1 fullCallees) =
      (runCfgWithCallees 8 callerMir [] emptyMemory fullCallees).map
        (MirOutcome.mapMem (Memory.withCallees (coneBodies cone1 fullCallees))) :=
  runCfgWithCallees_cone_narrow_of_closed cone1 8 callerMir [] emptyMemory fullCallees_ne_nil
    narrowCallees_ne_nil cone_agree callConeClosed_caller rfl rfl

/-- Exact return-value equality, via `runCfgWithCallees_cone_narrow_normal`. -/
theorem run_narrow_normal :
    ∀ m, runCfgWithCallees 8 callerMir [] emptyMemory fullCallees = some (.normal (.scalar ⟨42, 4⟩, m)) →
      runCfgWithCallees 8 callerMir [] emptyMemory (coneBodies cone1 fullCallees) =
        some (.normal (.scalar ⟨42, 4⟩, Memory.withCallees (coneBodies cone1 fullCallees) m)) :=
  fun _ h => runCfgWithCallees_cone_narrow_normal cone1 8 callerMir [] emptyMemory fullCallees_ne_nil
    narrowCallees_ne_nil cone_agree
    (coneReach_of_closedInv callConeClosed_caller 8 _
      (closedInv_init cone1 callerMir [] emptyMemory fullCallees_ne_nil rfl rfl)) h

/-- Callee-insensitive postcondition: returns `42u32`. -/
def retIs42 : MirOutcome → Prop
  | .normal (v, _) => v = .scalar ⟨42, 4⟩
  | _ => False

theorem retIs42_insensitive (c : CalleeEnv) :
    ∀ out, retIs42 (MirOutcome.mapMem (Memory.withCallees c) out) ↔ retIs42 out := by
  intro out
  rcases out with ⟨v, m⟩ | _ | _ <;> exact Iff.rfl

theorem wp_full :
    wpMirExecSym 8 callerMir
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees callerMir []
        emptyMemory fullCallees)) retIs42 := by
  obtain ⟨m, hm⟩ := run_some_of_retVal runs_concrete.1
  exact Anneal.MirFuelFree.wpMirExecSym_of_runMirExecBounded hm rfl

/-- **`wpMirExecSym_cone_narrow_of_closed`**: the WP proved with the full table transfers to
the narrowed table. -/
theorem wp_narrowed :
    wpMirExecSym 8 callerMir
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees callerMir []
        emptyMemory (coneBodies cone1 fullCallees))) retIs42 :=
  (wpMirExecSym_cone_narrow_of_closed cone1 8 callerMir [] emptyMemory fullCallees_ne_nil
    narrowCallees_ne_nil cone_agree callConeClosed_caller rfl rfl retIs42
    (retIs42_insensitive _)).mpr wp_full

/-- **`mirWpConverges_cone_narrow_of_closed`**: the fuel-free form. -/
theorem mirWp_narrowed :
    Anneal.MirFuelFree.MirWpConverges callerMir
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees callerMir []
        emptyMemory (coneBodies cone1 fullCallees)) retIs42 :=
  (mirWpConverges_cone_narrow_of_closed cone1 callerMir [] emptyMemory fullCallees_ne_nil
    narrowCallees_ne_nil cone_agree callConeClosed_caller rfl rfl retIs42
    (retIs42_insensitive _)).mpr ⟨8, wp_full⟩

/-- The semantic step-invariant of the full execution, from the syntactic closure. -/
theorem full_coneReach (fuel : Nat) :
    ConeReach callerMir (StepConeSafe cone1 callerMir) fuel
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees callerMir []
        emptyMemory fullCallees)) :=
  coneReach_of_closedInv callConeClosed_caller fuel _
    (closedInv_init cone1 callerMir [] emptyMemory fullCallees_ne_nil rfl rfl)

/-- **`runCfgWithCallees_cone_narrow`** in its *semantic* form: the step invariant is supplied
directly (here by `full_coneReach`, but any proof of `ConeReach` works). -/
theorem run_narrow_semantic :
    runCfgWithCallees 8 callerMir [] emptyMemory [helper1Mir] =
      (runCfgWithCallees 8 callerMir [] emptyMemory fullCallees).map
        (MirOutcome.mapMem (Memory.withCallees [helper1Mir])) :=
  runCfgWithCallees_cone_narrow cone1 8 callerMir [] emptyMemory fullCallees_ne_nil
    (fun h => by cases h) (coneBodies_fullCallees ▸ cone_agree) (full_coneReach 8)

/-- **`wpMirExecSym_cone_narrow_init`** in its semantic form. -/
theorem wp_narrow_semantic :
    wpMirExecSym 8 callerMir
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees callerMir []
          emptyMemory [helper1Mir])) retIs42 ↔
      wpMirExecSym 8 callerMir
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees callerMir []
          emptyMemory fullCallees)) retIs42 :=
  wpMirExecSym_cone_narrow_init cone1 8 callerMir [] emptyMemory fullCallees_ne_nil
    (fun h => by cases h) (coneBodies_fullCallees ▸ cone_agree) retIs42 (retIs42_insensitive _)
    (full_coneReach 8)

/-- Narrowing touches only `Memory.callees`: every other field of a narrowed memory is the
original one (the `withCallees` simp set, plus the counters by `rfl`). -/
theorem withCallees_only_callees (m : Memory) :
    (Memory.withCallees [helper1Mir] m).callees = [helper1Mir] ∧
      (Memory.withCallees [helper1Mir] m).borrows = m.borrows ∧
      (Memory.withCallees [helper1Mir] m).globals = m.globals ∧
      (Memory.withCallees [helper1Mir] m).callerLocals = m.callerLocals ∧
      (Memory.withCallees [helper1Mir] m).fnPtrs = m.fnPtrs ∧
      (Memory.withCallees [helper1Mir] m).traitImpls = m.traitImpls ∧
      (Memory.withCallees [helper1Mir] m).callStack = m.callStack ∧
      (Memory.withCallees [helper1Mir] m).activeCallee = m.activeCallee ∧
      (Memory.withCallees [helper1Mir] m).activeProtectors = m.activeProtectors ∧
      (Memory.withCallees [helper1Mir] m).nextAllocId = m.nextAllocId ∧
      (Memory.withCallees [helper1Mir] m).nextTag = m.nextTag ∧
      (Memory.withCallees [helper1Mir] m).nextProtector = m.nextProtector ∧
      (Memory.withCallees [helper1Mir] m).exposedAllocIds = m.exposedAllocIds :=
  ⟨Memory.withCallees_callees _ _, Memory.withCallees_borrows _ _, Memory.withCallees_globals _ _,
    Memory.withCallees_callerLocals _ _, Memory.withCallees_fnPtrs _ _,
    Memory.withCallees_traitImpls _ _, Memory.withCallees_callStack _ _,
    Memory.withCallees_activeCallee _ _, Memory.withCallees_activeProtectors _ _, rfl, rfl, rfl, rfl⟩

/-- The narrowed initial state differs from the full one only in its memory's callee table. -/
theorem narrowed_init_state :
    (MachineState.mapMem (Memory.withCallees [helper1Mir])
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees callerMir [] emptyMemory
          fullCallees)).frame =
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees callerMir [] emptyMemory
          fullCallees).frame ∧
      (MachineState.mapMem (Memory.withCallees [helper1Mir])
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees callerMir [] emptyMemory
          fullCallees)).memory.callees = [helper1Mir] :=
  ⟨MachineState.mapMem_frame _ _,
    (congrArg Memory.callees (MachineState.mapMem_memory _ _)).trans
      (Memory.withCallees_callees _ _)⟩

/-- One-step bisimulation at the call terminator (`stepMirState_callees_cone_eq`). -/
theorem first_step_narrow :
    stepMirState callerMir (.running (MachineState.mapMem (Memory.withCallees [helper1Mir])
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees callerMir [] emptyMemory
          fullCallees))) =
      MirStepNode.mapMem (Memory.withCallees [helper1Mir])
        (stepMirState callerMir (.running
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees callerMir [] emptyMemory
            fullCallees))) :=
  stepMirState_callees_cone_eq cone1 callerMir _ [helper1Mir] cone_agree
    (full_coneReach 1).1

/-! ### Negative canaries -/

/-- An out-of-cone call (`heavyCallee3 -> heavyCallee2`) fails the closure check. -/
theorem heavy3_not_closed :
    CallConeClosed ["cone::heavyCallee3"] heavy3Mir fullCallees = false := rfl

/-- An indirect call through a function pointer fails closed even if its body is listed. -/
theorem heavy2_indirect_not_closed :
    CallConeClosed ["cone::heavyCallee2"] heavy2Mir fullCallees = false := rfl

/-- The empty cone rejects the caller (its `helper1` call is outside the cone). -/
theorem caller_empty_cone_not_closed : CallConeClosed [] callerMir fullCallees = false := rfl

/-- A function-pointer reification cast fails closed (`Statement.calleeQueryFree`). -/
theorem reify_not_calleeQueryFree :
    Statement.calleeQueryFree
      { kind := .assign { local_ := 1, projection := [] }
          (.cast (.pointerCoercion "ReifyFnPointer") (fnItem "cone::helper1")
            { kind := .fnPtr [] (.uint .u32) .safe .rust, layoutIdx := 0 }), span := "reify" } =
      false := rfl

/-- `UnsafeFnPointer` and `Unsize` casts do not consult `Memory.callees`. -/
theorem unsafeFnPtr_unsize_calleeQueryFree :
    Rvalue.calleeQueryFree (.cast (.pointerCoercion "UnsafeFnPointer") (fnItem "f")
        { kind := .fnPtr [] (.uint .u32) .unsafe_ .rust, layoutIdx := 0 }) = true ∧
      Rvalue.calleeQueryFree (.cast (.pointerCoercion "Unsize") (fnItem "f") coneU32) = true :=
  ⟨rfl, rfl⟩

/-- Duplicate shadowing: a table whose *first* `cone::helper1` entry is `helper1Mir` agrees
with `[helper1Mir]`, even though it also contains the shadowed duplicate. -/
theorem dup_shadow_agree :
    calleesAgreeOn cone1 [helper1Mir, helper1ShadowMir] [helper1Mir] := by
  intro dp hdp
  cases hdp with
  | head => rfl
  | tail _ h => cases h

/-- …but the shadowed duplicate alone does *not* agree: `findCallee?` first-match semantics
are respected, so agreement cannot be faked by a later duplicate. -/
theorem dup_shadow_disagree :
    ¬ calleesAgreeOn cone1 [helper1Mir, helper1ShadowMir] [helper1ShadowMir] := by
  intro h
  have h1 := congrArg (Option.map (fun b : CapturedMir => b.localDecls.length))
    (h "cone::helper1" (List.Mem.head _))
  exact absurd h1 (by decide)

/-- First-match duplicate handling, both directions (cited by the `calleesAgreeOn` docstring). -/
theorem calleesAgreeOn_dup_shadow_witness :
    calleesAgreeOn cone1 [helper1Mir, helper1ShadowMir] [helper1Mir] ∧
      ¬ calleesAgreeOn cone1 [helper1Mir, helper1ShadowMir] [helper1ShadowMir] :=
  ⟨dup_shadow_agree, dup_shadow_disagree⟩

/-- Narrowing to the shadowed duplicate really changes the result (`7`, not `42`): the
agreement hypothesis of the narrowing theorems is not vacuous. -/
theorem dup_shadow_changes_result :
    retVal? (runCfgWithCallees 8 callerMir [] emptyMemory [helper1ShadowMir]) =
      some (.scalar ⟨7, 4⟩) :=
  rfl

/-- `coneBodies` keeps both duplicates in order, and still agrees by first match. -/
theorem dup_coneBodies_agree :
    coneBodies cone1 [helper1Mir, heavy2Mir, helper1ShadowMir] = [helper1Mir, helper1ShadowMir] ∧
      calleesAgreeOn cone1 [helper1Mir, heavy2Mir, helper1ShadowMir]
        (coneBodies cone1 [helper1Mir, heavy2Mir, helper1ShadowMir]) :=
  ⟨rfl, calleesAgreeOn_coneBodies _ _⟩

/-- `calleesAgreeOn` algebra on the concrete tables. -/
theorem agree_algebra :
    calleesAgreeOn cone1 (coneBodies cone1 fullCallees) fullCallees ∧
      calleesAgreeOn cone1 fullCallees fullCallees ∧
      calleesAgreeOn [] fullCallees (coneBodies cone1 fullCallees) ∧
      calleesAgreeOn cone1 [helper1Mir, helper1ShadowMir] (coneBodies cone1 fullCallees) :=
  ⟨cone_agree.symm, calleesAgreeOn.refl _ _,
    calleesAgreeOn.mono cone_agree (fun _ h => by cases h),
    dup_shadow_agree.trans (by rw [coneBodies_fullCallees]; exact calleesAgreeOn.refl _ _)⟩

/-- `checkCalleeSig_nil_eq_of_findCallee_eq`, `internFnPtr_withCalleeCtx`,
`isNonSelectIntrinsicOpt_of_eq_none`, and `evalDirectRustIntrinsic?_eq_none_of_classify`
witnesses. -/
theorem callee_sig_and_fnptr_bridges (s : MachineState) (p : Place) :
    checkCalleeSig fullCallees "cone::helper1" [] (.uint .u32) .rust [] [] =
      checkCalleeSig (coneBodies cone1 fullCallees) "cone::helper1" [] (.uint .u32) .rust [] [] ∧
    internFnPtr (Memory.withCalleeCtx [helper1Mir] none [] [] emptyMemory) "cone::helper1" [] none =
      (let (aid, m') := internFnPtr emptyMemory "cone::helper1" [] none
       (aid, Memory.withCalleeCtx [helper1Mir] none [] [] m')) ∧
    isNonSelectIntrinsicOpt (classifyRustIntrinsic? "cone::helper1") = true ∧
    evalDirectRustIntrinsic? s none
        { defPath := "cone::helper1", typeArgs := [], fnSig := none, isIndirect := false }
        [] emptyLayoutTable [] [] [] p 0 .continue_ = none :=
  ⟨checkCalleeSig_nil_eq_of_findCallee_eq [] (.uint .u32) .rust []
      (cone_agree "cone::helper1" (List.Mem.head _)),
   internFnPtr_withCalleeCtx [helper1Mir] none [] [] emptyMemory "cone::helper1" [] none,
   isNonSelectIntrinsicOpt_of_eq_none rfl,
   evalDirectRustIntrinsic?_eq_none_of_classify rfl⟩

/-- Inline compiler intrinsic caller (`core::intrinsics::ub_checks`,
`classifyRustIntrinsic? = some .ubChecks`) narrowed to an *empty* callee table `c₂ = []`
(`coneBodies coneUb fullCallees = []`) via `runCfgWithCallees_cone_narrow_of_closed_wf`,
`wpMirExecSym_cone_narrow_of_closed_wf`, and `mirWpConverges_cone_narrow_of_closed_wf`, plus
negative canary for `core::intrinsics::const_eval_select`. -/
def ubBoolLocal : LocalDecl :=
  { mutability := .mut, ty := { kind := .bool, layoutIdx := 0 }, debugName := some "b" }

def intrinsicCallerMir : CapturedMir :=
  Anneal.MirLoops.mkMirBody "cone::intrinsicCaller" 0 [retLocal, ubBoolLocal]
    [{ statements := [{ kind := .storageLive 1, span := "live" }],
       terminator := callTerm (fnItem "core::intrinsics::ub_checks") 1 1,
       isCleanup := false },
     retBlock [assignConst 0 42]]

def constEvalSelectCallerMir : CapturedMir :=
  Anneal.MirLoops.mkMirBody "cone::selectCaller" 0 [retLocal]
    [callBlock (fnItem "core::intrinsics::const_eval_select") 0 1, retBlock []]

def coneUb : List DefPath := ["core::intrinsics::ub_checks"]

/-- The intrinsic really is dispatched inline: it is classified as `ubChecks`, and both the
full and the *empty* callee table run the caller to `42u32` (an external call would make
`runCfgWithCallees` return `none`), so the narrowing below is not vacuous. -/
theorem intrinsicCaller_runs_concrete :
    classifyRustIntrinsic? "core::intrinsics::ub_checks" = some .ubChecks ∧
      retVal? (runCfgWithCallees 8 intrinsicCallerMir [] emptyMemory fullCallees) =
        some (.scalar ⟨42, 4⟩) ∧
      retVal? (runCfgWithCallees 8 intrinsicCallerMir [] emptyMemory
        (coneBodies coneUb fullCallees)) = some (.scalar ⟨42, 4⟩) :=
  ⟨rfl, rfl, rfl⟩

/-- Regression canary: `core::ub_checks::check_language_ub` is *not* a trusted intrinsic path
(`classifyRustIntrinsic? = none`); with no body registered, the call is an unlinked external
call, on which the bounded runner stops (`none`). -/
def nonIntrinsicCallerMir : CapturedMir :=
  Anneal.MirLoops.mkMirBody "cone::nonIntrinsicCaller" 0 [retLocal, ubBoolLocal]
    [{ statements := [{ kind := .storageLive 1, span := "live" }],
       terminator := callTerm (fnItem "core::ub_checks::check_language_ub") 1 1,
       isCleanup := false },
     retBlock [assignConst 0 42]]

theorem non_intrinsic_path_is_external_call :
    classifyRustIntrinsic? "core::ub_checks::check_language_ub" = none ∧
      runCfgWithCallees 8 nonIntrinsicCallerMir [] emptyMemory fullCallees = none :=
  ⟨rfl, rfl⟩

theorem callConeClosed_intrinsicCaller :
    CallConeClosed coneUb intrinsicCallerMir fullCallees = true ∧
      CallConeClosed ["core::intrinsics::const_eval_select"] constEvalSelectCallerMir fullCallees =
        false ∧
      coneBodies coneUb fullCallees = [] :=
  ⟨rfl, rfl, rfl⟩

theorem intrinsicCaller_narrow_to_empty :
    runCfgWithCallees 8 intrinsicCallerMir [] emptyMemory (coneBodies coneUb fullCallees) =
      (runCfgWithCallees 8 intrinsicCallerMir [] emptyMemory fullCallees).map
        (MirOutcome.mapMem (Memory.withCallees (coneBodies coneUb fullCallees))) ∧
    (wpMirExecSym 8 intrinsicCallerMir
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          intrinsicCallerMir [] emptyMemory (coneBodies coneUb fullCallees))) retIs42 ↔
      wpMirExecSym 8 intrinsicCallerMir
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          intrinsicCallerMir [] emptyMemory fullCallees)) retIs42) ∧
    (Anneal.MirFuelFree.MirWpConverges intrinsicCallerMir
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          intrinsicCallerMir [] emptyMemory (coneBodies coneUb fullCallees)) retIs42 ↔
      Anneal.MirFuelFree.MirWpConverges intrinsicCallerMir
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          intrinsicCallerMir [] emptyMemory fullCallees) retIs42) :=
  ⟨runCfgWithCallees_cone_narrow_of_closed_wf coneUb 8 intrinsicCallerMir [] emptyMemory
      (Or.inl fullCallees_ne_nil) (Or.inr ⟨rfl, rfl⟩)
      (calleesAgreeOn_coneBodies coneUb fullCallees) rfl rfl rfl,
   wpMirExecSym_cone_narrow_of_closed_wf coneUb 8 intrinsicCallerMir [] emptyMemory
      (Or.inl fullCallees_ne_nil) (Or.inr ⟨rfl, rfl⟩)
      (calleesAgreeOn_coneBodies coneUb fullCallees) rfl rfl rfl retIs42
      (retIs42_insensitive _),
   mirWpConverges_cone_narrow_of_closed_wf coneUb intrinsicCallerMir [] emptyMemory
      (Or.inl fullCallees_ne_nil) (Or.inr ⟨rfl, rfl⟩)
      (calleesAgreeOn_coneBodies coneUb fullCallees) rfl rfl rfl retIs42
      (retIs42_insensitive _)⟩

/-- Polymorphic (`typeArgs = [.uint .u32]`) `lookupCallee_eq_of_findCallee_eq_of_no_traitImpl`,
`checkCalleeSig_eq_of_findCallee_eq_of_no_traitImpl`, `hasTraitImplForDefPath_append`,
`hasTraitImplForDefPath_flatMapTraitImpls_coneBodies`, and concrete `&[u32]` slice
`core::intrinsics::size_of_val` caller narrowed from `fullCallees` to `[]`. -/
def usizeRetLocal : LocalDecl :=
  { mutability := .mut, ty := { kind := .uint .usize, layoutIdx := 0 }, debugName := some "ret" }

def sliceArgLocal : LocalDecl :=
  { mutability := .not, ty := { kind := .ref .not (.slice (.uint .u32)), layoutIdx := 1 },
    debugName := some "s" }

def sliceSizeOfValCallerMir : CapturedMir :=
  Anneal.MirLoops.mkMirBody "cone::sliceSizeOfValCaller" 1 [usizeRetLocal, sliceArgLocal]
    [{ statements := []
       terminator :=
         { kind := .call (fnItem "core::intrinsics::size_of_val")
             [.copy { local_ := 1, projection := [] }]
             { local_ := 0, projection := [] } (some 1) .continue_
           span := "call_size_of_val" }
       isCleanup := false },
     retBlock []]

def coneSizeOfVal : List DefPath := ["core::intrinsics::size_of_val"]

theorem polymorphic_callee_and_slice_size_of_val_narrow_witness :
    lookupCallee fullCallees emptyLayoutTable "cone::helper1" [.uint .u32] [] =
      lookupCallee (coneBodies cone1 fullCallees) emptyLayoutTable "cone::helper1" [.uint .u32] [] ∧
    checkCalleeSig fullCallees "cone::helper1" [] (.uint .u32) .rust [.uint .u32] [] =
      checkCalleeSig (coneBodies cone1 fullCallees) "cone::helper1" [] (.uint .u32) .rust
        [.uint .u32] [] ∧
    hasTraitImplForDefPath ([] ++ flatMapTraitImpls (coneBodies cone1 fullCallees))
      "cone::helper1" = false ∧
    retVal? (runCfgWithCallees 8 sliceSizeOfValCallerMir [WidePtrVal.toValue 8 wide4]
      emptyMemory fullCallees) = some (.scalar ⟨16, 8⟩) ∧
    retVal? (runCfgWithCallees 8 sliceSizeOfValCallerMir [WidePtrVal.toValue 8 wide4]
      emptyMemory (coneBodies coneSizeOfVal fullCallees)) = some (.scalar ⟨16, 8⟩) ∧
    runCfgWithCallees 8 sliceSizeOfValCallerMir [WidePtrVal.toValue 8 wide4] emptyMemory
        (coneBodies coneSizeOfVal fullCallees) =
      (runCfgWithCallees 8 sliceSizeOfValCallerMir [WidePtrVal.toValue 8 wide4] emptyMemory
        fullCallees).map
        (MirOutcome.mapMem (Memory.withCallees (coneBodies coneSizeOfVal fullCallees))) := by
  have hNoTrait1 : hasTraitImplForDefPath ([] ++ flatMapTraitImpls fullCallees)
      "cone::helper1" = false := by
    rw [hasTraitImplForDefPath_append]
    rfl
  have hNoTrait2 : hasTraitImplForDefPath ([] ++ flatMapTraitImpls (coneBodies cone1 fullCallees))
      "cone::helper1" = false := by
    rw [hasTraitImplForDefPath_append]
    exact hasTraitImplForDefPath_flatMapTraitImpls_coneBodies cone1 fullCallees "cone::helper1" rfl
  refine ⟨lookupCallee_eq_of_findCallee_eq_of_no_traitImpl emptyLayoutTable [.uint .u32] []
      (cone_agree "cone::helper1" (List.Mem.head _)) hNoTrait1 hNoTrait2,
    checkCalleeSig_eq_of_findCallee_eq_of_no_traitImpl [] (.uint .u32) .rust [.uint .u32] []
      (cone_agree "cone::helper1" (List.Mem.head _)) hNoTrait1 hNoTrait2,
    hNoTrait2, rfl, rfl,
    runCfgWithCallees_cone_narrow_of_closed_wf coneSizeOfVal 8 sliceSizeOfValCallerMir
      [WidePtrVal.toValue 8 wide4] emptyMemory (Or.inl fullCallees_ne_nil) (Or.inr ⟨rfl, rfl⟩)
      (calleesAgreeOn_coneBodies coneSizeOfVal fullCallees) rfl rfl rfl⟩

/-- A generic call `cone::helper1::<u32>()` (type arguments on the function item). -/
def genericCallerMir : CapturedMir :=
  Anneal.MirLoops.mkMirBody "cone::genericCaller" 0
    [retLocal, { mutability := .mut, ty := coneU32, debugName := some "t" }]
    [{ statements := [{ kind := .storageLive 1, span := "live" }],
       terminator := callTerm
         (.constant { ty := { kind := .fnDef "cone::helper1" [.uint .u32], layoutIdx := 0 },
                      val := .zeroSized }) 1 1,
       isCleanup := false },
     retBlock [assignMove 0 1]]

/-- Negative canary for monomorphic `CallConeClosed` vs. positive polymorphic narrowing via
`CallConeClosedPoly` (`runCfgWithCallees_cone_narrow_of_closed_poly_wf`,
`wpMirExecSym_cone_narrow_of_closed_poly_wf`, `mirWpConverges_cone_narrow_of_closed_poly_wf`),
plus a true generic callee `polyIdMir` (`typeParamCount = 1`) monomorphized at runtime by
`lookupCallee` via `CapturedMir.instantiate` and a polymorphic `size_of_val::<[u32]>` intrinsic
caller. -/
theorem generic_call_fails_closed :
    CallConeClosed cone1 genericCallerMir fullCallees = false ∧
      CallConeClosedPoly cone1 genericCallerMir fullCallees = true := ⟨rfl, rfl⟩

def param0Ty : Ty := { kind := .param 0 "T", layoutIdx := 0 }

def polyIdMir : CapturedMir :=
  { (Anneal.MirLoops.mkMirBody "cone::polyId" 1
      [{ mutability := .mut, ty := param0Ty, debugName := some "_0" },
       { mutability := .not, ty := param0Ty, debugName := some "x" }]
      [retBlock [assignMove 0 1]]) with
    typeParamCount := 1
    genericParams := [{ idx := 0, name := "T" }] }

def polyIdCallerMir : CapturedMir :=
  { (Anneal.MirLoops.mkMirBody "cone::polyIdCaller" 0
      [retLocal]
      [{ statements := []
         terminator :=
           { kind := .call
               (.constant { ty := { kind := .fnDef "cone::polyId" [.uint .u32], layoutIdx := 0 }
                            val := .zeroSized })
               [Anneal.MirLoops.constU32 42]
               { local_ := 0, projection := [] } (some 1) .continue_
             span := "call_poly_id" }
         isCleanup := false },
       retBlock []]) with
    layouts := layouts64 }

def fullPolyCallees : CalleeEnv := [polyIdMir, heavy2Mir, heavy3Mir]

def conePolyId : List DefPath := ["cone::polyId"]

def polySizeOfValSliceCallerMir : CapturedMir :=
  Anneal.MirLoops.mkMirBody "cone::polySizeOfValSliceCaller" 1 [usizeRetLocal, sliceArgLocal]
    [{ statements := []
       terminator :=
         { kind := .call
             (.constant { ty := { kind := .fnDef "core::intrinsics::size_of_val" [.slice (.uint .u32)]
                                  layoutIdx := 0 }
                          val := .zeroSized })
             [.copy { local_ := 1, projection := [] }]
             { local_ := 0, projection := [] } (some 1) .continue_
           span := "call_poly_size_of_val" }
       isCleanup := false },
     retBlock []]

theorem polymorphic_cone_narrowing_end_to_end :
    retVal? (runCfgWithCallees 8 polyIdCallerMir [] emptyMemory fullPolyCallees) =
      some (.scalar ⟨42, 4⟩) ∧
    retVal? (runCfgWithCallees 8 polyIdCallerMir [] emptyMemory
      (coneBodies conePolyId fullPolyCallees)) = some (.scalar ⟨42, 4⟩) ∧
    runCfgWithCallees 8 polyIdCallerMir [] emptyMemory
        (coneBodies conePolyId fullPolyCallees) =
      (runCfgWithCallees 8 polyIdCallerMir [] emptyMemory fullPolyCallees).map
        (MirOutcome.mapMem (Memory.withCallees (coneBodies conePolyId fullPolyCallees))) ∧
    (wpMirExecSym 8 polyIdCallerMir
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          polyIdCallerMir [] emptyMemory (coneBodies conePolyId fullPolyCallees))) retIs42 ↔
      wpMirExecSym 8 polyIdCallerMir
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          polyIdCallerMir [] emptyMemory fullPolyCallees)) retIs42) ∧
    (Anneal.MirFuelFree.MirWpConverges polyIdCallerMir
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          polyIdCallerMir [] emptyMemory (coneBodies conePolyId fullPolyCallees)) retIs42 ↔
      Anneal.MirFuelFree.MirWpConverges polyIdCallerMir
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          polyIdCallerMir [] emptyMemory fullPolyCallees) retIs42) ∧
    retVal? (runCfgWithCallees 8 polySizeOfValSliceCallerMir [WidePtrVal.toValue 8 wide4]
      emptyMemory fullCallees) = some (.scalar ⟨16, 8⟩) ∧
    retVal? (runCfgWithCallees 8 polySizeOfValSliceCallerMir [WidePtrVal.toValue 8 wide4]
      emptyMemory (coneBodies coneSizeOfVal fullCallees)) = some (.scalar ⟨16, 8⟩) ∧
    runCfgWithCallees 8 polySizeOfValSliceCallerMir [WidePtrVal.toValue 8 wide4] emptyMemory
        (coneBodies coneSizeOfVal fullCallees) =
      (runCfgWithCallees 8 polySizeOfValSliceCallerMir [WidePtrVal.toValue 8 wide4] emptyMemory
        fullCallees).map
        (MirOutcome.mapMem (Memory.withCallees (coneBodies coneSizeOfVal fullCallees))) := by
  have hNoTraitPoly : ∀ dp, dp ∈ conePolyId →
      hasTraitImplForDefPath
        (polyIdCallerMir.traitImpls ++ flatMapTraitImpls (coneBodies conePolyId fullPolyCallees))
        dp = false := by
    intro dp hdp
    cases hdp with
    | head => rfl
    | tail _ h => cases h
  have hNoTraitSize : ∀ dp, dp ∈ coneSizeOfVal →
      hasTraitImplForDefPath
        (polySizeOfValSliceCallerMir.traitImpls ++
          flatMapTraitImpls (coneBodies coneSizeOfVal fullCallees)) dp = false := by
    intro dp hdp
    cases hdp with
    | head => rfl
    | tail _ h => cases h
  refine ⟨rfl, rfl,
    runCfgWithCallees_cone_narrow_of_closed_poly_wf conePolyId 8 polyIdCallerMir [] emptyMemory
      (Or.inl (fun h => by cases h)) (Or.inl (fun h => by cases h))
      (calleesAgreeOn_coneBodies conePolyId fullPolyCallees) rfl hNoTraitPoly rfl rfl,
    wpMirExecSym_cone_narrow_of_closed_poly_wf conePolyId 8 polyIdCallerMir [] emptyMemory
      (Or.inl (fun h => by cases h)) (Or.inl (fun h => by cases h))
      (calleesAgreeOn_coneBodies conePolyId fullPolyCallees) rfl hNoTraitPoly rfl rfl
      retIs42 (retIs42_insensitive _),
    mirWpConverges_cone_narrow_of_closed_poly_wf conePolyId polyIdCallerMir [] emptyMemory
      (Or.inl (fun h => by cases h)) (Or.inl (fun h => by cases h))
      (calleesAgreeOn_coneBodies conePolyId fullPolyCallees) rfl hNoTraitPoly rfl rfl
      retIs42 (retIs42_insensitive _),
    rfl, rfl,
    runCfgWithCallees_cone_narrow_of_closed_poly_wf coneSizeOfVal 8 polySizeOfValSliceCallerMir
      [WidePtrVal.toValue 8 wide4] emptyMemory (Or.inl fullCallees_ne_nil) (Or.inr ⟨rfl, rfl⟩)
      (calleesAgreeOn_coneBodies coneSizeOfVal fullCallees) rfl hNoTraitSize rfl rfl⟩

/-- **Decidable polymorphic narrowing** (`runCfgWithCallees_coneBodies_narrow_of_closed_poly`
and its `wpMirExecSym` / `MirWpConverges` forms): the generic `polyId::<u32>` caller is narrowed
to its call cone from the single `rfl`-checked `CallConeClosedPoly` fact, with no hand-proved
trait-impl side condition. -/
theorem polyId_coneBodies_narrow_decidable :
    CallConeClosedPoly conePolyId polyIdCallerMir fullPolyCallees polyIdCallerMir.traitImpls = true ∧
      runCfgWithCallees 8 polyIdCallerMir [] emptyMemory (coneBodies conePolyId fullPolyCallees) =
        (runCfgWithCallees 8 polyIdCallerMir [] emptyMemory fullPolyCallees).map
          (MirOutcome.mapMem (Memory.withCallees (coneBodies conePolyId fullPolyCallees))) ∧
      (wpMirExecSym 8 polyIdCallerMir
          (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            polyIdCallerMir [] emptyMemory (coneBodies conePolyId fullPolyCallees))) retIs42 ↔
        wpMirExecSym 8 polyIdCallerMir
          (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            polyIdCallerMir [] emptyMemory fullPolyCallees)) retIs42) ∧
      (Anneal.MirFuelFree.MirWpConverges polyIdCallerMir
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            polyIdCallerMir [] emptyMemory (coneBodies conePolyId fullPolyCallees)) retIs42 ↔
        Anneal.MirFuelFree.MirWpConverges polyIdCallerMir
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            polyIdCallerMir [] emptyMemory fullPolyCallees) retIs42) :=
  ⟨rfl,
    runCfgWithCallees_coneBodies_narrow_of_closed_poly conePolyId 8 polyIdCallerMir [] emptyMemory
      (Or.inl (fun h => by cases h)) (Or.inl (fun h => by cases h)) rfl rfl rfl,
    wpMirExecSym_coneBodies_narrow_of_closed_poly conePolyId 8 polyIdCallerMir [] emptyMemory
      (Or.inl (fun h => by cases h)) (Or.inl (fun h => by cases h)) rfl rfl rfl retIs42
      (retIs42_insensitive _),
    mirWpConverges_coneBodies_narrow_of_closed_poly conePolyId polyIdCallerMir [] emptyMemory
      (Or.inl (fun h => by cases h)) (Or.inl (fun h => by cases h)) rfl rfl rfl retIs42
      (retIs42_insensitive _)⟩

/-- A table whose `heavyCallee2` body registers a trait impl targeting `cone::polyId`. -/
def traitDispatchCallees : CalleeEnv :=
  [polyIdMir,
   { heavy2Mir with
     traitImpls := [{ traitRef := { defPath := "cone::polyId", args := [.uint .u32] },
                      implPath := "cone::PolyImpl::poly_id" }] },
   heavy3Mir]

/-- Negative canary: once a trait impl can intercept `cone::polyId`, the polymorphic closure
check fails closed (trait dispatch may resolve to a body outside the cone), even though the
direct call and the cone body are unchanged. -/
theorem trait_dispatch_fails_closed_poly :
    CallConeClosedPoly conePolyId polyIdCallerMir traitDispatchCallees
      polyIdCallerMir.traitImpls = false := rfl

/-- **2-hop transitive generic call chain** (`polyChainCallerMir -> polyWrapMir::<u32>(42) ->
polyIdMir::<T>(x)`), where `polyWrapMir` (`typeParamCount = 1`) calls `cone::polyId` with its own
generic type parameter `.param 0 "T"` (monomorphized at runtime by `lookupCallee` via
`CapturedMir.instantiate` to `.uint .u32`), plus direct polymorphic narrowing of
`polySizeOfValSliceCallerMir` (`core::intrinsics::size_of_val::<[u32]>(&s)`) to the empty callee
table `[]`, with every hypothesis discharged by `rfl`. -/
def polyWrapMir : CapturedMir :=
  { (Anneal.MirLoops.mkMirBody "cone::polyWrap" 1
      [{ mutability := .mut, ty := param0Ty, debugName := some "_0" },
       { mutability := .not, ty := param0Ty, debugName := some "x" }]
      [{ statements := []
         terminator :=
           { kind := .call
               (.constant { ty := { kind := .fnDef "cone::polyId" [.param 0 "T"], layoutIdx := 0 }
                            val := .zeroSized })
               [.move { local_ := 1, projection := [] }]
               { local_ := 0, projection := [] } (some 1) .continue_
             span := "call_poly_id_from_wrap" }
         isCleanup := false },
       retBlock []]) with
    typeParamCount := 1
    genericParams := [{ idx := 0, name := "T" }]
    layouts := layouts64 }

def polyChainCallerMir : CapturedMir :=
  { (Anneal.MirLoops.mkMirBody "cone::polyChainCaller" 0
      [retLocal]
      [{ statements := []
         terminator :=
           { kind := .call
               (.constant { ty := { kind := .fnDef "cone::polyWrap" [.uint .u32], layoutIdx := 0 }
                            val := .zeroSized })
               [Anneal.MirLoops.constU32 42]
               { local_ := 0, projection := [] } (some 1) .continue_
             span := "call_poly_wrap" }
         isCleanup := false },
       retBlock []]) with
    layouts := layouts64 }

def fullPolyChainCallees : CalleeEnv := [polyWrapMir, polyIdMir, heavy2Mir, heavy3Mir]

def conePolyChain : List DefPath := ["cone::polyWrap", "cone::polyId"]

def retIs16Usize : MirOutcome → Prop
  | .normal (v, _) => v = .scalar ⟨16, 8⟩
  | _ => False

theorem retIs16Usize_insensitive (c : CalleeEnv) :
    ∀ out, retIs16Usize (MirOutcome.mapMem (Memory.withCallees c) out) ↔ retIs16Usize out := by
  intro out
  rcases out with ⟨v, m⟩ | _ | _ <;> exact Iff.rfl

theorem polyChain_and_empty_intrinsic_narrow_clean_decidable :
    retVal? (runCfgWithCallees 12 polyChainCallerMir [] emptyMemory fullPolyChainCallees) =
        some (.scalar ⟨42, 4⟩) ∧
      retVal? (runCfgWithCallees 12 polyChainCallerMir [] emptyMemory
        (coneBodies conePolyChain fullPolyChainCallees)) = some (.scalar ⟨42, 4⟩) ∧
      runCfgWithCallees 12 polyChainCallerMir [] emptyMemory
          (coneBodies conePolyChain fullPolyChainCallees) =
        (runCfgWithCallees 12 polyChainCallerMir [] emptyMemory fullPolyChainCallees).map
          (MirOutcome.mapMem (Memory.withCallees
            (coneBodies conePolyChain fullPolyChainCallees))) ∧
      (wpMirExecSym 12 polyChainCallerMir
          (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            polyChainCallerMir [] emptyMemory
            (coneBodies conePolyChain fullPolyChainCallees))) retIs42 ↔
        wpMirExecSym 12 polyChainCallerMir
          (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            polyChainCallerMir [] emptyMemory fullPolyChainCallees)) retIs42) ∧
      (Anneal.MirFuelFree.MirWpConverges polyChainCallerMir
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            polyChainCallerMir [] emptyMemory
            (coneBodies conePolyChain fullPolyChainCallees)) retIs42 ↔
        Anneal.MirFuelFree.MirWpConverges polyChainCallerMir
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            polyChainCallerMir [] emptyMemory fullPolyChainCallees) retIs42) ∧
      runCfgWithCallees 8 polySizeOfValSliceCallerMir [WidePtrVal.toValue 8 wide4] emptyMemory [] =
        (runCfgWithCallees 8 polySizeOfValSliceCallerMir [WidePtrVal.toValue 8 wide4] emptyMemory
          fullCallees).map (MirOutcome.mapMem (Memory.withCallees [])) ∧
      (wpMirExecSym 8 polySizeOfValSliceCallerMir
          (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            polySizeOfValSliceCallerMir [WidePtrVal.toValue 8 wide4] emptyMemory []))
          retIs16Usize ↔
        wpMirExecSym 8 polySizeOfValSliceCallerMir
          (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            polySizeOfValSliceCallerMir [WidePtrVal.toValue 8 wide4] emptyMemory fullCallees))
          retIs16Usize) ∧
      (Anneal.MirFuelFree.MirWpConverges polySizeOfValSliceCallerMir
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            polySizeOfValSliceCallerMir [WidePtrVal.toValue 8 wide4] emptyMemory [])
          retIs16Usize ↔
        Anneal.MirFuelFree.MirWpConverges polySizeOfValSliceCallerMir
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            polySizeOfValSliceCallerMir [WidePtrVal.toValue 8 wide4] emptyMemory fullCallees)
          retIs16Usize) :=
  ⟨rfl, rfl,
    runCfgWithCallees_coneBodies_narrow_of_closed_poly_clean conePolyChain 12 polyChainCallerMir
      [] emptyMemory fullPolyChainCallees rfl rfl rfl rfl rfl,
    wpMirExecSym_coneBodies_narrow_of_closed_poly_clean conePolyChain 12 polyChainCallerMir
      [] emptyMemory fullPolyChainCallees rfl rfl rfl rfl rfl retIs42 (retIs42_insensitive _),
    mirWpConverges_coneBodies_narrow_of_closed_poly_clean conePolyChain polyChainCallerMir
      [] emptyMemory fullPolyChainCallees rfl rfl rfl rfl rfl retIs42 (retIs42_insensitive _),
    runCfgWithCallees_nil_narrow_of_closed_poly_clean coneSizeOfVal 8 polySizeOfValSliceCallerMir
      [WidePtrVal.toValue 8 wide4] emptyMemory fullCallees rfl rfl rfl rfl rfl rfl,
    wpMirExecSym_nil_narrow_of_closed_poly_clean coneSizeOfVal 8 polySizeOfValSliceCallerMir
      [WidePtrVal.toValue 8 wide4] emptyMemory fullCallees rfl rfl rfl rfl rfl rfl retIs16Usize
      (retIs16Usize_insensitive _),
    mirWpConverges_nil_narrow_of_closed_poly_clean coneSizeOfVal polySizeOfValSliceCallerMir
      [WidePtrVal.toValue 8 wide4] emptyMemory fullCallees rfl rfl rfl rfl rfl rfl retIs16Usize
      (retIs16Usize_insensitive _)⟩

/-! ## Kernel axiom audit -/

/-! Audits every declaration added to `Anneal.SepLogicLenses` (section `SliceWidePtrLenses`,
starting at `WidePtrVal`) and `Anneal.MirLiftCore` (section `CallConeNarrowing`, starting at
`CalleeEnv`), plus every witness in this file: no `unsafe` declaration; every module declaration
is *constructive* (axioms within `{propext, Quot.sound}`, so no `Classical.choice`), and every
witness uses only `{propext, Classical.choice, Quot.sound}` (so no `sorryAx` and no
`Lean.ofReduceBool` / `native_decide` anywhere). Fails if fewer declarations than expected are
found.

Non-vacuity: additionally fails unless *every* audited module theorem (public or private) is
reachable from the concrete witnesses of this file, following used constants through auxiliary
declarations (`match_`, `_f`, `proof_`) of both modules, so no new theorem is left
uninstantiated. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let constructive : List Name := [``propext, ``Quot.sound]
  let mut audited : Nat := 0
  let mut theorems : Nat := 0
  let mut auditedSet : NameSet := {}
  let mut auditedThms : Array Name := #[]
  let mut modIdxs : Array ModuleIdx := #[]
  for (modName, anchor, minCount) in
      [(`Anneal.SepLogicLenses, ``Anneal.SepLogicLenses.WidePtrVal, 100),
       (`Anneal.MirLiftCore, ``Anneal.MirLiftCore.CalleeEnv, 185)] do
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
                throwError "{n} depends on non-constructive or disallowed axiom {a}"
            count := count + 1
            auditedSet := auditedSet.insert n
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
    if (`Anneal.MirSliceWidePtrLensTests).isPrefixOf n then
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
  logInfo m!"axiom audit passed: {audited} declarations ({theorems} module theorems, all \
    constructive and instantiated by witnesses)"

end Anneal.MirSliceWidePtrLensTests
