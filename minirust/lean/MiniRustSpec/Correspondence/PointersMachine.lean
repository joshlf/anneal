/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.PointersLattice
import MiniRustSpec.Correspondence.PointersMachineStep

/-!
# Raw pointers and references in both semantics: `Machine<BM>` and `Mach` (MR-3.1, MR-3.2)

Third of the four modules that make up `MiniRustSpec.Correspondence.Pointers` (see its module
documentation; the split keeps every public declaration, name, and proof unchanged, with
pure `Machine<BM>` / `Mach` equivalence sub-split across `PointersMachineCodec`,
`PointersMachineExpr`, and `PointersMachineStep` to stay well inside an 8 GiB memory budget):

* the unconditional equivalence of the polymorphic `Machine<BM>` interpretation and `Mach`
  (`spec/lang/machine.md`: `evalPlaceM_bm_eq`, `evalValueM_bm_eq`, `evalStatementM_bm_eq`,
  `stepM_bm_eq`, `stepsM_bm_eq`), re-exported from `PointersMachineStep`;
* vtable pointers and trait-object safe pointers (`Machine::vtable_from_ptr`);
* `UnOp::GetMetadata` sanity checks for every metadata kind;
* ZST, null, uninhabited, `PlaceExpr::Deref`, and `ConstructWidePointer` laws.

It builds on `PointersLattice` and `PointersMachineStep`; `Pointers` concludes with the Tree
Borrows structural invariants and panic-freedom.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open Trusted.Sequence
open PointersMachineInternal

/-! ## Vtable pointers and trait-object safe pointers (`Machine::vtable_from_ptr`)

`check_ptr` (`spec/lang/representation.md`) validates a vtable pointer with
`Machine::vtable_from_ptr` (`spec/lang/machine.md`), both as a stand-alone
`PtrType::VTablePtr` and as the metadata of a trait-object pointer, and then checks a
trait-object safe pointer (`&dyn Trait`, `&mut dyn Trait`, `Box<dyn Trait>`) at the
dynamic size and alignment recorded in that vtable. The results below hold for every
machine; each is stated for `Mach` (`BasicMemory`) and for the polymorphic
`Machine M` (in particular `MachTB`, Tree Borrows). -/

/-- `Machine::vtable_from_ptr` and `Machine::vtable_lookup` find the same vtable. They
differ only in how they fail: `vtable_from_ptr` raises UB for a pointer that is not the
address of a vtable, where `vtable_lookup` unwraps (a spec panic). -/
theorem vtableFromPtr_ok_iff_vtableLookup_ok (m : Mach) (ptr : Ptr) (vt : Gen.VTable) :
    vtableFromPtr m ptr = .ok vt ↔ vtableLookup m ptr = .ok vt := by
  unfold vtableFromPtr vtableLookup
  split
  · unfold mapIndex
    split
    · exact Iff.rfl
    · constructor <;> intro h <;> cases h
  · constructor <;> intro h <;> cases h

/-- Polymorphic `vtableFromPtr_ok_iff_vtableLookup_ok`. -/
theorem vtableFromPtrM_ok_iff_vtableLookupM_ok {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (ptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (vt : Gen.VTable) :
    vtableFromPtrM m ptr = .ok vt ↔ vtableLookupM m ptr = .ok vt := by
  unfold vtableFromPtrM vtableLookupM
  split
  · unfold mapIndex
    split
    · exact Iff.rfl
    · constructor <;> intro h <;> cases h
  · constructor <;> intro h <;> cases h

/-- A pointer that is not the address of any vtable of the machine (for example a null,
dangling, or data pointer) is UB for `Machine::vtable_from_ptr`. -/
theorem vtableFromPtr_ub_of_not_mem (m : Mach) (ptr : Ptr)
    (h : ∀ e ∈ m.vtable_ptrs.entries, e.2 ≠ ptr) :
    vtableFromPtr m ptr = .error (.ub "invalid pointer for vtable lookup") := by
  have hnone : m.vtable_ptrs.entries.find?
      (fun (_, (vtablePtr : Ptr)) => decide (vtablePtr = ptr)) = none := by
    rw [List.find?_eq_none]
    intro e he
    obtain ⟨name, vp⟩ := e
    simp only [decide_eq_true_eq]
    exact h (name, vp) he
  unfold vtableFromPtr
  rw [hnone]
  rfl

/-- Polymorphic `vtableFromPtr_ub_of_not_mem`. -/
theorem vtableFromPtrM_ub_of_not_mem {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (ptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (h : ∀ e ∈ m.vtable_ptrs.entries, e.2 ≠ ptr) :
    vtableFromPtrM m ptr = .error (.ub "invalid pointer for vtable lookup") := by
  have hnone : m.vtable_ptrs.entries.find?
      (fun (_, (vtablePtr : Gen.ThinPointer (Gen.Memory.Provenance M))) =>
        decide (vtablePtr = ptr)) = none := by
    rw [List.find?_eq_none]
    intro e he
    obtain ⟨name, vp⟩ := e
    simp only [decide_eq_true_eq]
    exact h (name, vp) he
  unfold vtableFromPtrM
  rw [hnone]
  rfl

/-- **`check_ptr_metadata` on vtable metadata is `check_ptr` at `PtrType::VTablePtr`**
(`spec/lang/representation.md`):
> "(Some(PointerMeta::VTablePointer(ptr)), PointerMetaKind::VTablePointer(trait_name)) => {
>     self.check_ptr(ptr.widen(None), PtrType::VTablePtr(trait_name))?;
> }"
The branch of `checkPtrMetadata` that unrolls this recursive call equals the call. -/
theorem checkPtrMetadata_vtable_eq_checkPtr (vptr : Ptr) (traitName : Gen.TraitName) (m : Mach) :
    checkPtrMetadata (some (.VTablePointer vptr)) (.VTablePointer traitName) (some m) =
      checkPtr (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) := rfl

/-- Polymorphic `checkPtrMetadata_vtable_eq_checkPtr`, on every `Memory` `M` (in
particular on `MachTB`): the vtable lookup that `checkPtrM` passes to
`checkPtrMetadataM` is `vtableFromPtrM` of its machine. -/
theorem checkPtrMetadataM_vtable_eq_checkPtrM {M : Type} [Gen.Memory M] [MemoryOps M]
    (vptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (traitName : Gen.TraitName)
    (m : Gen.Machine M) :
    checkPtrMetadataM (some (.VTablePointer vptr)) (.VTablePointer traitName)
        (some (vtableFromPtrM m)) =
      checkPtrM (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) := rfl

/-- The polymorphic metadata check of a thin pointer passes whatever the vtable lookup
argument is. -/
theorem checkPtrMetadataM_none {Provenance : Type}
    (lookup? : Option (Gen.ThinPointer Provenance → Interp Gen.VTable)) :
    checkPtrMetadataM (none : Option (Gen.PointerMeta Provenance)) .None lookup? = .ok () := rfl

/-- `LayoutStrategy::compute_size_and_align` on a trait object reads the size and the
alignment from the vtable that the pointer metadata points to. -/
theorem compute_size_and_align_traitObject {Provenance : Type}
    (vtables : Gen.ThinPointer Provenance → Interp Gen.VTable) (traitName : Gen.TraitName)
    (vptr : Gen.ThinPointer Provenance) :
    LayoutStrategy.compute_size_and_align vtables (.TraitObject traitName)
        (some (.VTablePointer vptr)) =
      (do let vtable ← vtables vptr; pure (vtable.size, vtable.align)) := rfl

/-- `check_ptr` at `PtrType::VTablePtr` with a machine: an in-bounds stand-alone vtable
pointer is well formed exactly when it is the address of a vtable for the given trait. -/
theorem checkPtr_vtablePtr_eq (vptr : Ptr) (traitName : Gen.TraitName) (m : Mach)
    (hAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true) :
    checkPtr (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) =
      (do
        let vtable ← vtableFromPtr m vptr
        ensureElseUb (vtable.trait_name == traitName) "Value::Ptr: invalid vtable in metadata") := by
  unfold checkPtr
  dsimp only [ThinPointer.widen, PtrType.meta_kind, PtrType.safe_pointee]
  rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind]

/-- Polymorphic `checkPtr_vtablePtr_eq`. -/
theorem checkPtrM_vtablePtr_eq {M : Type} [Gen.Memory M] [MemoryOps M]
    (vptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (traitName : Gen.TraitName)
    (m : Gen.Machine M)
    (hAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true) :
    checkPtrM (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) =
      (do
        let vtable ← vtableFromPtrM m vptr
        ensureElseUb (vtable.trait_name == traitName) "Value::Ptr: invalid vtable in metadata") := by
  unfold checkPtrM
  dsimp only [ThinPointer.widen, PtrType.meta_kind, PtrType.safe_pointee]
  rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_none, ok_bind]

/-- A vtable pointer of the right trait passes `check_ptr`. -/
theorem checkPtr_vtablePtr_ok (vptr : Ptr) (traitName : Gen.TraitName) (m : Mach)
    (vt : Gen.VTable)
    (hAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtr m vptr = .ok vt) (hTrait : vt.trait_name = traitName) :
    checkPtr (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) = .ok () := by
  subst hTrait
  rw [checkPtr_vtablePtr_eq vptr _ m hAddr, hvt, ok_bind, beq_self_eq_true, ensureElseUb_true]

/-- Polymorphic `checkPtr_vtablePtr_ok`. -/
theorem checkPtrM_vtablePtr_ok {M : Type} [Gen.Memory M] [MemoryOps M]
    (vptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (traitName : Gen.TraitName)
    (m : Gen.Machine M) (vt : Gen.VTable)
    (hAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtrM m vptr = .ok vt) (hTrait : vt.trait_name = traitName) :
    checkPtrM (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) = .ok () := by
  subst hTrait
  rw [checkPtrM_vtablePtr_eq vptr _ m hAddr, hvt, ok_bind, beq_self_eq_true, ensureElseUb_true]

/-- A pointer that is not the address of a vtable (null, dangling, or unmapped) is UB at
`PtrType::VTablePtr`: `"invalid pointer for vtable lookup"`. -/
theorem checkPtr_vtablePtr_invalid_ptr_ub (vptr : Ptr) (traitName : Gen.TraitName) (m : Mach)
    (hAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hNotVTable : ∀ e ∈ m.vtable_ptrs.entries, e.2 ≠ vptr) :
    checkPtr (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) =
      .error (.ub "invalid pointer for vtable lookup") := by
  rw [checkPtr_vtablePtr_eq vptr _ m hAddr, vtableFromPtr_ub_of_not_mem m vptr hNotVTable,
    error_bind]

/-- Polymorphic `checkPtr_vtablePtr_invalid_ptr_ub`. -/
theorem checkPtrM_vtablePtr_invalid_ptr_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (vptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (traitName : Gen.TraitName)
    (m : Gen.Machine M)
    (hAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hNotVTable : ∀ e ∈ m.vtable_ptrs.entries, e.2 ≠ vptr) :
    checkPtrM (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) =
      .error (.ub "invalid pointer for vtable lookup") := by
  rw [checkPtrM_vtablePtr_eq vptr _ m hAddr, vtableFromPtrM_ub_of_not_mem m vptr hNotVTable,
    error_bind]

/-- A pointer to a vtable for the wrong trait is UB at `PtrType::VTablePtr`:
`"Value::Ptr: invalid vtable in metadata"`. -/
theorem checkPtr_vtablePtr_wrong_trait_ub (vptr : Ptr) (traitName : Gen.TraitName) (m : Mach)
    (vt : Gen.VTable)
    (hAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtr m vptr = .ok vt) (hTrait : vt.trait_name ≠ traitName) :
    checkPtr (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") := by
  rw [checkPtr_vtablePtr_eq vptr _ m hAddr, hvt, ok_bind, beq_eq_false_iff_ne.mpr hTrait,
    ensureElseUb_false]

/-- Polymorphic `checkPtr_vtablePtr_wrong_trait_ub`. -/
theorem checkPtrM_vtablePtr_wrong_trait_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (vptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (traitName : Gen.TraitName)
    (m : Gen.Machine M) (vt : Gen.VTable)
    (hAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtrM m vptr = .ok vt) (hTrait : vt.trait_name ≠ traitName) :
    checkPtrM (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") := by
  rw [checkPtrM_vtablePtr_eq vptr _ m hAddr, hvt, ok_bind, beq_eq_false_iff_ne.mpr hTrait,
    ensureElseUb_false]

/-- **`check_ptr` on a trait-object safe pointer whose vtable metadata is ill formed**
(`&dyn Trait`, `&mut dyn Trait`, `Box<dyn Trait>`; `mk` is `PtrType::Ref` at some
mutability or `PtrType::Box`): the pointer metadata is checked first, and that check is
`check_ptr` of the vtable pointer at `PtrType::VTablePtr`, so every failure of the
latter (a null, dangling, or unmapped vtable pointer, or a vtable for the wrong trait)
is the failure of the safe pointer. -/
theorem checkPtr_traitObject_metadata_error (thin vptr : Ptr)
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (m : Mach) (e : Stop)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hMeta : checkPtr (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) = .error e) :
    checkPtr (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error e := by
  obtain ⟨layout, inhabited, cells, freeze, unpin⟩ := pointee
  dsimp only at hLayout
  subst hLayout
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_vtable_eq_checkPtr, hMeta, error_bind]
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_vtable_eq_checkPtr, hMeta, error_bind]

/-- Polymorphic `checkPtr_traitObject_metadata_error`. -/
theorem checkPtrM_traitObject_metadata_error {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (m : Gen.Machine M) (e : Stop)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hMeta : checkPtrM (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) =
      .error e) :
    checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error e := by
  obtain ⟨layout, inhabited, cells, freeze, unpin⟩ := pointee
  dsimp only at hLayout
  subst hLayout
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind, Option.map]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_vtable_eq_checkPtrM, hMeta,
      error_bind]
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind, Option.map]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_vtable_eq_checkPtrM, hMeta,
      error_bind]

/-- **`check_ptr` on a trait-object safe pointer with well-formed vtable metadata**
(`&dyn Trait`, `&mut dyn Trait`, `Box<dyn Trait>`; `mk` is `PtrType::Ref` at some
mutability or `PtrType::Box`): once the vtable pointer is the address of a vtable `vt`
for the pointee's trait, the pointer is checked exactly like a thin safe pointer to a
sized pointee with the dynamic size `vt.size` and alignment `vt.align` read from that
vtable: the size fits in `isize::MAX`, the address is non-null and aligned to
`vt.align`, the pointee is inhabited, and `vt.size` bytes are dereferenceable in the
machine's memory. -/
theorem checkPtr_traitObject_eq_sized (thin vptr : Ptr) (mk : Gen.PointeeInfo → Gen.PtrType)
    (pointee : Gen.PointeeInfo) (traitName : Gen.TraitName) (m : Mach) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtr m vptr = .ok vt) (hTrait : vt.trait_name = traitName) :
    checkPtr (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      checkPtr (ThinPointer.widen thin none)
        (mk { pointee with layout := .Sized vt.size vt.align }) (some m) := by
  have hMeta : checkPtrMetadata (some (.VTablePointer vptr)) (.VTablePointer traitName) (some m) =
      .ok () := by
    rw [checkPtrMetadata_vtable_eq_checkPtr]
    exact checkPtr_vtablePtr_ok vptr traitName m vt hVAddr hvt hTrait
  have hvl : vtableLookup m vptr = .ok vt :=
    (vtableFromPtr_ok_iff_vtableLookup_ok m vptr vt).mp hvt
  obtain ⟨layout, inhabited, cells, freeze, unpin⟩ := pointee
  dsimp only at hLayout
  subst hLayout
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    refine bind_congr_right _ (fun _ => ?_)
    rw [hMeta, checkPtrMetadata_none, compute_size_and_align_traitObject, hvl,
      compute_size_and_align_sized]
    rfl
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    refine bind_congr_right _ (fun _ => ?_)
    rw [hMeta, checkPtrMetadata_none, compute_size_and_align_traitObject, hvl,
      compute_size_and_align_sized]
    rfl

/-- Polymorphic `checkPtr_traitObject_eq_sized`, on every `Memory` `M` (in particular
on `MachTB`, where dereferenceability is `TreeBorrowsMemory::dereferenceable`). -/
theorem checkPtrM_traitObject_eq_sized {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (m : Gen.Machine M) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtrM m vptr = .ok vt) (hTrait : vt.trait_name = traitName) :
    checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      checkPtrM (ThinPointer.widen thin none)
        (mk { pointee with layout := .Sized vt.size vt.align }) (some m) := by
  have hMeta : checkPtrMetadataM (some (.VTablePointer vptr)) (.VTablePointer traitName)
      (some (vtableFromPtrM m)) = .ok () := by
    rw [checkPtrMetadataM_vtable_eq_checkPtrM]
    exact checkPtrM_vtablePtr_ok vptr traitName m vt hVAddr hvt hTrait
  have hvl : vtableLookupM m vptr = .ok vt :=
    (vtableFromPtrM_ok_iff_vtableLookupM_ok m vptr vt).mp hvt
  obtain ⟨layout, inhabited, cells, freeze, unpin⟩ := pointee
  dsimp only at hLayout
  subst hLayout
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee, Option.map]
    refine bind_congr_right _ (fun _ => ?_)
    rw [hMeta, checkPtrMetadataM_none, compute_size_and_align_traitObject, hvl,
      compute_size_and_align_sized]
    rfl
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee, Option.map]
    refine bind_congr_right _ (fun _ => ?_)
    rw [hMeta, checkPtrMetadataM_none, compute_size_and_align_traitObject, hvl,
      compute_size_and_align_sized]
    rfl

/-- **A well-formed trait-object safe pointer passes `check_ptr`**: valid vtable
metadata for the pointee's trait, the dynamic size `vt.size` within `isize::MAX`, a
non-null address aligned to the dynamic alignment `vt.align`, an inhabited pointee, and
`vt.size` dereferenceable bytes (`Memory::dereferenceable`). -/
theorem checkPtr_traitObject_ok (thin vptr : Ptr) (mk : Gen.PointeeInfo → Gen.PtrType)
    (pointee : Gen.PointeeInfo) (traitName : Gen.TraitName) (m : Mach) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtr m vptr = .ok vt) (hTrait : vt.trait_name = traitName)
    (hSize : inBounds (vt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true)
    (hNonNull : (thin.addr != 0) = true)
    (hAligned : Align.is_aligned vt.align thin.addr = true)
    (hInhabited : pointee.inhabited = true)
    (hDeref : CM.dereferenceable m.mem thin vt.size = .ok ()) :
    checkPtr (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .ok () := by
  rw [checkPtr_traitObject_eq_sized thin vptr mk pointee traitName m vt hMk hLayout hVAddr hvt
    hTrait]
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hAligned, ensureElseUb_true, ok_bind,
      hInhabited, ensureElseUb_true, ok_bind, hDeref]
    rfl
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hAligned, ensureElseUb_true, ok_bind,
      hInhabited, ensureElseUb_true, ok_bind, hDeref]
    rfl

/-- Polymorphic `checkPtr_traitObject_ok` (in particular on `MachTB`). -/
theorem checkPtrM_traitObject_ok {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (m : Gen.Machine M) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtrM m vptr = .ok vt) (hTrait : vt.trait_name = traitName)
    (hSize : inBounds (vt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true)
    (hNonNull : (thin.addr != 0) = true)
    (hAligned : Align.is_aligned vt.align thin.addr = true)
    (hInhabited : pointee.inhabited = true)
    (hDeref : ConcurrentMemory.dereferenceable m.mem thin vt.size = .ok ()) :
    checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .ok () := by
  rw [checkPtrM_traitObject_eq_sized thin vptr mk pointee traitName m vt hMk hLayout hVAddr hvt
    hTrait]
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hAligned, ensureElseUb_true, ok_bind,
      hInhabited, ensureElseUb_true, ok_bind, hDeref]
    rfl
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hAligned, ensureElseUb_true, ok_bind,
      hInhabited, ensureElseUb_true, ok_bind, hDeref]
    rfl

/-- **A trait-object safe pointer whose data address is not aligned to the dynamic
alignment `vt.align` of its vtable is UB**: `"Value::Ptr: unaligned safe pointer"`. -/
theorem checkPtr_traitObject_unaligned_ub (thin vptr : Ptr)
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (m : Mach) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtr m vptr = .ok vt) (hTrait : vt.trait_name = traitName)
    (hSize : inBounds (vt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true)
    (hNonNull : (thin.addr != 0) = true)
    (hUnaligned : Align.is_aligned vt.align thin.addr = false) :
    checkPtr (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error (.ub "Value::Ptr: unaligned safe pointer") := by
  rw [checkPtr_traitObject_eq_sized thin vptr mk pointee traitName m vt hMk hLayout hVAddr hvt
    hTrait]
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hUnaligned, ensureElseUb_false, error_bind]
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hUnaligned, ensureElseUb_false, error_bind]

/-- Polymorphic `checkPtr_traitObject_unaligned_ub` (in particular on `MachTB`). -/
theorem checkPtrM_traitObject_unaligned_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (m : Gen.Machine M) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtrM m vptr = .ok vt) (hTrait : vt.trait_name = traitName)
    (hSize : inBounds (vt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true)
    (hNonNull : (thin.addr != 0) = true)
    (hUnaligned : Align.is_aligned vt.align thin.addr = false) :
    checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error (.ub "Value::Ptr: unaligned safe pointer") := by
  rw [checkPtrM_traitObject_eq_sized thin vptr mk pointee traitName m vt hMk hLayout hVAddr hvt
    hTrait]
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hUnaligned, ensureElseUb_false, error_bind]
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hUnaligned, ensureElseUb_false, error_bind]

/-- **A trait-object safe pointer whose memory is not dereferenceable for the dynamic
size `vt.size` of its vtable is UB** (an allocation smaller than `vt.size`, a dead
allocation, or a pointer without provenance):
`"Value::Ptr: non-dereferenceable safe pointer"`. -/
theorem checkPtr_traitObject_nonDereferenceable_ub (thin vptr : Ptr)
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (m : Mach) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtr m vptr = .ok vt) (hTrait : vt.trait_name = traitName)
    (hSize : inBounds (vt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true)
    (hNonNull : (thin.addr != 0) = true)
    (hAligned : Align.is_aligned vt.align thin.addr = true)
    (hInhabited : pointee.inhabited = true) (msg : String)
    (hDeref : CM.dereferenceable m.mem thin vt.size = .error (.ub msg)) :
    checkPtr (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error (.ub "Value::Ptr: non-dereferenceable safe pointer") := by
  rw [checkPtr_traitObject_eq_sized thin vptr mk pointee traitName m vt hMk hLayout hVAddr hvt
    hTrait]
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hAligned, ensureElseUb_true, ok_bind,
      hInhabited, ensureElseUb_true, ok_bind, hDeref]
    rfl
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hAligned, ensureElseUb_true, ok_bind,
      hInhabited, ensureElseUb_true, ok_bind, hDeref]
    rfl

/-- Polymorphic `checkPtr_traitObject_nonDereferenceable_ub` (in particular on `MachTB`,
where `Memory::dereferenceable` is `TreeBorrowsMemory::dereferenceable`). -/
theorem checkPtrM_traitObject_nonDereferenceable_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (m : Gen.Machine M) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtrM m vptr = .ok vt) (hTrait : vt.trait_name = traitName)
    (hSize : inBounds (vt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true)
    (hNonNull : (thin.addr != 0) = true)
    (hAligned : Align.is_aligned vt.align thin.addr = true)
    (hInhabited : pointee.inhabited = true) (msg : String)
    (hDeref : ConcurrentMemory.dereferenceable m.mem thin vt.size = .error (.ub msg)) :
    checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error (.ub "Value::Ptr: non-dereferenceable safe pointer") := by
  rw [checkPtrM_traitObject_eq_sized thin vptr mk pointee traitName m vt hMk hLayout hVAddr hvt
    hTrait]
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hAligned, ensureElseUb_true, ok_bind,
      hInhabited, ensureElseUb_true, ok_bind, hDeref]
    rfl
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hAligned, ensureElseUb_true, ok_bind,
      hInhabited, ensureElseUb_true, ok_bind, hDeref]
    rfl

/-- **Dynamic dispatch resolves to the function pointer constant**: with a machine,
`UnOp::VTableMethodLookup(method)` on a pointer to a vtable `vt` returns, at
`Type::Ptr(PtrType::FnPtr)`, exactly the value of `Constant::FnPointer` for the function
`vt.methods[method]`, the callee value that `Terminator::Call` resolves with
`Machine::fn_from_ptr`. -/
theorem evalUnOp_vtableMethodLookup_eq_fnPointer (m : Mach) (vptr : Ptr) (ty : Gen.PtrType)
    (meth : Gen.TraitMethodName) (vt : Gen.VTable) (fnName : Gen.FnName)
    (hvt : vtableLookup m vptr = .ok vt)
    (hfn : mapIndex vt.methods meth "vtable.methods[method]" = .ok fnName) :
    evalUnOp (.VTableMethodLookup meth) (.Ptr (ThinPointer.widen vptr none), .Ptr ty) (some m) =
      (do
        let fnPtr ← evalConstant m (.FnPointer fnName)
        pure (fnPtr, .Ptr .FnPtr)) := by
  have h : evalUnOp (.VTableMethodLookup meth) (.Ptr (ThinPointer.widen vptr none), .Ptr ty)
      (some m) =
      (do
        let vtable ← vtableLookup m vptr
        let fnName ← mapIndex vtable.methods meth "vtable.methods[method]"
        let fnThin ← mapIndex m.fn_ptrs fnName "self.fn_ptrs[fn_name]"
        pure (.Ptr (ThinPointer.widen fnThin none), .Ptr .FnPtr)) := rfl
  have hc : evalConstant m (.FnPointer fnName) =
      (do
        let ptr ← mapIndex m.fn_ptrs fnName "self.fn_ptrs[fn_name]"
        pure (.Ptr (ThinPointer.widen ptr none))) := rfl
  rw [h, hvt, ok_bind, hfn, ok_bind, hc]
  cases mapIndex m.fn_ptrs fnName "self.fn_ptrs[fn_name]" <;> rfl

/-- Polymorphic `evalUnOp_vtableMethodLookup_eq_fnPointer` (in particular on `MachTB`). -/
theorem evalUnOpM_vtableMethodLookup_eq_fnPointer {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (vptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (ty : Gen.PtrType)
    (meth : Gen.TraitMethodName) (vt : Gen.VTable) (fnName : Gen.FnName)
    (hvt : vtableLookupM m vptr = .ok vt)
    (hfn : mapIndex vt.methods meth "vtable.methods[method]" = .ok fnName) :
    evalUnOpM (.VTableMethodLookup meth) (.Ptr (ThinPointer.widen vptr none), .Ptr ty) (some m) =
      (do
        let fnPtr ← evalConstantM m (.FnPointer fnName)
        pure (fnPtr, .Ptr .FnPtr)) := by
  have h : evalUnOpM (.VTableMethodLookup meth) (.Ptr (ThinPointer.widen vptr none), .Ptr ty)
      (some m) =
      (do
        let vtable ← vtableLookupM m vptr
        let fnName ← mapIndex vtable.methods meth "vtable.methods[method]"
        let fnThin ← mapIndex m.fn_ptrs fnName "self.fn_ptrs[fn_name]"
        pure (.Ptr (ThinPointer.widen fnThin none), .Ptr .FnPtr)) := rfl
  have hc : evalConstantM m (.FnPointer fnName) =
      (do
        let ptr ← mapIndex m.fn_ptrs fnName "self.fn_ptrs[fn_name]"
        pure (.Ptr (ThinPointer.widen ptr none))) := rfl
  rw [h, hvt, ok_bind, hfn, ok_bind, hc]
  cases mapIndex m.fn_ptrs fnName "self.fn_ptrs[fn_name]" <;> rfl

/-- When `m.vtable_ptrs` maps `ptr` to `vtableName`, `Machine::vtable_from_ptr`
reduces directly to indexing `m.prog.vtables[vtableName]` (raising a map-index
spec panic if `m.prog.vtables` is missing that entry, never UB). -/
theorem vtableFromPtr_eq_mapIndex_of_find (m : Mach) (ptr : Ptr) (vtableName : Gen.VTableName)
    (vp : Ptr)
    (hfind : m.vtable_ptrs.entries.find?
      (fun (_, (vtablePtr : Ptr)) => decide (vtablePtr = ptr)) = some (vtableName, vp)) :
    vtableFromPtr m ptr = mapIndex m.prog.vtables vtableName "self.prog.vtables[vtable_name]" := by
  unfold vtableFromPtr
  rw [hfind]

/-- Polymorphic `vtableFromPtr_eq_mapIndex_of_find`. -/
theorem vtableFromPtrM_eq_mapIndex_of_find {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (ptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (vtableName : Gen.VTableName) (vp : Gen.ThinPointer (Gen.Memory.Provenance M))
    (hfind : m.vtable_ptrs.entries.find?
      (fun (_, (vtablePtr : Gen.ThinPointer (Gen.Memory.Provenance M))) =>
        decide (vtablePtr = ptr)) = some (vtableName, vp)) :
    vtableFromPtrM m ptr = mapIndex m.prog.vtables vtableName "self.prog.vtables[vtable_name]" := by
  unfold vtableFromPtrM
  rw [hfind]

/-- An out-of-bounds address at `PtrType::VTablePtr` is UB before metadata or
vtable lookup, with or without a machine. -/
theorem checkPtr_vtablePtr_outOfBounds_ub (ptr : Gen.Pointer Prov) (traitName : Gen.TraitName)
    (m : Option Mach)
    (hAddr : inBounds ptr.thin_pointer.addr .Unsigned x86_64.PTR_SIZE = false) :
    checkPtr ptr (.VTablePtr traitName) m = .error (.ub "Value::Ptr: pointer out-of-bounds") := by
  unfold checkPtr
  rw [hAddr, ensureElseUb_false, error_bind]

/-- Polymorphic `checkPtr_vtablePtr_outOfBounds_ub`. -/
theorem checkPtrM_vtablePtr_outOfBounds_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (ptr : Gen.Pointer (Gen.Memory.Provenance M)) (traitName : Gen.TraitName)
    (m : Option (Gen.Machine M))
    (hAddr : inBounds ptr.thin_pointer.addr .Unsigned x86_64.PTR_SIZE = false) :
    checkPtrM ptr (.VTablePtr traitName) m = .error (.ub "Value::Ptr: pointer out-of-bounds") := by
  unfold checkPtrM
  rw [hAddr, ensureElseUb_false, error_bind]

/-- Non-empty metadata on a stand-alone `PtrType::VTablePtr` is UB
(`"Value::Ptr: invalid metadata"`), with or without a machine. -/
theorem checkPtr_vtablePtr_nonNone_meta_ub (thin : Ptr) (pm : Gen.PointerMeta Prov)
    (traitName : Gen.TraitName) (m : Option Mach)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true) :
    checkPtr (ThinPointer.widen thin (some pm)) (.VTablePtr traitName) m =
      .error (.ub "Value::Ptr: invalid metadata") := by
  unfold checkPtr
  dsimp only [ThinPointer.widen, PtrType.meta_kind]
  rw [hAddr, ensureElseUb_true, ok_bind]
  cases pm <;> rfl

/-- Polymorphic `checkPtr_vtablePtr_nonNone_meta_ub`. -/
theorem checkPtrM_vtablePtr_nonNone_meta_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin : Gen.ThinPointer (Gen.Memory.Provenance M))
    (pm : Gen.PointerMeta (Gen.Memory.Provenance M))
    (traitName : Gen.TraitName) (m : Option (Gen.Machine M))
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true) :
    checkPtrM (ThinPointer.widen thin (some pm)) (.VTablePtr traitName) m =
      .error (.ub "Value::Ptr: invalid metadata") := by
  unfold checkPtrM
  dsimp only [ThinPointer.widen, PtrType.meta_kind]
  rw [hAddr, ensureElseUb_true, ok_bind]
  cases pm <;> rfl

/-- **Raw `*const dyn Trait` validity (`ucg#516`)**: even for a raw pointer
`PtrType::Raw(VTablePointer(trait_name))`, whose data pointer may be null,
unaligned, or dangling (as long as its address fits in `usize`), `check_ptr`
validates its vtable metadata identically to `PtrType::VTablePtr(trait_name)`. -/
theorem checkPtr_rawTraitObject_eq_vtablePtr (thin vptr : Ptr) (traitName : Gen.TraitName)
    (m : Mach) (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true) :
    checkPtr (ThinPointer.widen thin (some (.VTablePointer vptr)))
        (.Raw (.VTablePointer traitName)) (some m) =
      checkPtr (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) := by
  have h : checkPtr (ThinPointer.widen thin (some (.VTablePointer vptr)))
      (.Raw (.VTablePointer traitName)) (some m) =
      (do
        ensureElseUb (inBounds thin.addr .Unsigned x86_64.PTR_SIZE)
          "Value::Ptr: pointer out-of-bounds"
        checkPtrMetadata (some (.VTablePointer vptr)) (.VTablePointer traitName) (some m)
        pure ()) := rfl
  rw [h, hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_vtable_eq_checkPtr]
  cases checkPtr (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) with
  | error _ => rfl
  | ok u => cases u; rfl

/-- Polymorphic `checkPtr_rawTraitObject_eq_vtablePtr` (in particular on `MachTB`). -/
theorem checkPtrM_rawTraitObject_eq_vtablePtr {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M)) (traitName : Gen.TraitName)
    (m : Gen.Machine M) (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true) :
    checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr)))
        (.Raw (.VTablePointer traitName)) (some m) =
      checkPtrM (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) := by
  have h : checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr)))
      (.Raw (.VTablePointer traitName)) (some m) =
      (do
        ensureElseUb (inBounds thin.addr .Unsigned x86_64.PTR_SIZE)
          "Value::Ptr: pointer out-of-bounds"
        checkPtrMetadataM (some (.VTablePointer vptr)) (.VTablePointer traitName)
          (some (vtableFromPtrM m))
        pure ()) := rfl
  rw [h, hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_vtable_eq_checkPtrM]
  cases checkPtrM (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) with
  | error _ => rfl
  | ok u => cases u; rfl

/-- `LayoutStrategy::compute_size_and_align` on an unsized struct with a
trait-object tail (`LayoutStrategy::Tuple { head, tail: TraitObject(..) }`)
combines `head` (including `packed_align` capping and head alignment) with the
vtable's size and alignment via `TupleHeadLayout::full_size_and_align`. -/
theorem compute_size_and_align_tuple_traitObject {Provenance : Type}
    (vtables : Gen.ThinPointer Provenance → Interp Gen.VTable) (head : Gen.TupleHeadLayout)
    (traitName : Gen.TraitName) (vptr : Gen.ThinPointer Provenance) :
    LayoutStrategy.compute_size_and_align vtables (.Tuple head (.TraitObject traitName))
        (some (.VTablePointer vptr)) =
      (do
        let vtable ← vtables vptr
        pure (TupleHeadLayout.full_size_and_align head vtable.size vtable.align)) := by
  have h : LayoutStrategy.compute_size_and_align vtables (.Tuple head (.TraitObject traitName))
      (some (.VTablePointer vptr)) =
      (do
        let (tailSize, tailAlign) ← LayoutStrategy.compute_size_and_align vtables
          (.TraitObject traitName) (some (.VTablePointer vptr))
        pure (TupleHeadLayout.full_size_and_align head tailSize tailAlign)) := rfl
  rw [h, compute_size_and_align_traitObject]
  cases vtables vptr <;> rfl

/-- **`check_ptr` on an unsized struct with a trait-object tail whose vtable
metadata is ill formed**: metadata is checked before computing the tuple layout
or safe-pointer checks, so every `PtrType::VTablePtr` failure propagates. -/
theorem checkPtr_tuple_traitObject_metadata_error (thin vptr : Ptr)
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (head : Gen.TupleHeadLayout) (traitName : Gen.TraitName) (m : Mach) (e : Stop)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .Tuple head (.TraitObject traitName))
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hMeta : checkPtr (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) = .error e) :
    checkPtr (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error e := by
  obtain ⟨layout, inhabited, cells, freeze, unpin⟩ := pointee
  dsimp only at hLayout
  subst hLayout
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_vtable_eq_checkPtr, hMeta, error_bind]
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_vtable_eq_checkPtr, hMeta, error_bind]

/-- Polymorphic `checkPtr_tuple_traitObject_metadata_error`. -/
theorem checkPtrM_tuple_traitObject_metadata_error {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (head : Gen.TupleHeadLayout) (traitName : Gen.TraitName) (m : Gen.Machine M) (e : Stop)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .Tuple head (.TraitObject traitName))
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hMeta : checkPtrM (ThinPointer.widen vptr none) (.VTablePtr traitName) (some m) =
      .error e) :
    checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error e := by
  obtain ⟨layout, inhabited, cells, freeze, unpin⟩ := pointee
  dsimp only at hLayout
  subst hLayout
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind, Option.map]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_vtable_eq_checkPtrM, hMeta,
      error_bind]
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind, Option.map]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_vtable_eq_checkPtrM, hMeta,
      error_bind]

/-- **`check_ptr` on an unsized struct with a trait-object tail**
(`&StructWithDyn`, `&mut StructWithDyn`, `Box<StructWithDyn>`): once the vtable
metadata is validated to vtable `vt`, the safe pointer is checked identically to
a thin safe pointer whose sized layout is
`TupleHeadLayout::full_size_and_align head vt.size vt.align` (accounting for
`head.end`, `head.align`, `head.packed_align`, tail offset alignment, and
trailing padding). -/
theorem checkPtr_tuple_traitObject_eq_sized (thin vptr : Ptr)
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (head : Gen.TupleHeadLayout) (traitName : Gen.TraitName) (m : Mach) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .Tuple head (.TraitObject traitName))
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtr m vptr = .ok vt) (hTrait : vt.trait_name = traitName) :
    checkPtr (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      checkPtr (ThinPointer.widen thin none)
        (mk { pointee with
          layout := .Sized
            (TupleHeadLayout.full_size_and_align head vt.size vt.align).1
            (TupleHeadLayout.full_size_and_align head vt.size vt.align).2 }) (some m) := by
  have hMeta : checkPtrMetadata (some (.VTablePointer vptr)) (.VTablePointer traitName) (some m) =
      .ok () := by
    rw [checkPtrMetadata_vtable_eq_checkPtr]
    exact checkPtr_vtablePtr_ok vptr traitName m vt hVAddr hvt hTrait
  have hvl : vtableLookup m vptr = .ok vt :=
    (vtableFromPtr_ok_iff_vtableLookup_ok m vptr vt).mp hvt
  obtain ⟨layout, inhabited, cells, freeze, unpin⟩ := pointee
  dsimp only at hLayout
  subst hLayout
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    refine bind_congr_right _ (fun _ => ?_)
    rw [hMeta, checkPtrMetadata_none, compute_size_and_align_tuple_traitObject, hvl,
      compute_size_and_align_sized]
    rfl
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    refine bind_congr_right _ (fun _ => ?_)
    rw [hMeta, checkPtrMetadata_none, compute_size_and_align_tuple_traitObject, hvl,
      compute_size_and_align_sized]
    rfl

/-- Polymorphic `checkPtr_tuple_traitObject_eq_sized` (in particular on `MachTB`). -/
theorem checkPtrM_tuple_traitObject_eq_sized {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (head : Gen.TupleHeadLayout) (traitName : Gen.TraitName) (m : Gen.Machine M) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .Tuple head (.TraitObject traitName))
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtrM m vptr = .ok vt) (hTrait : vt.trait_name = traitName) :
    checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      checkPtrM (ThinPointer.widen thin none)
        (mk { pointee with
          layout := .Sized
            (TupleHeadLayout.full_size_and_align head vt.size vt.align).1
            (TupleHeadLayout.full_size_and_align head vt.size vt.align).2 }) (some m) := by
  have hMeta : checkPtrMetadataM (some (.VTablePointer vptr)) (.VTablePointer traitName)
      (some (vtableFromPtrM m)) = .ok () := by
    rw [checkPtrMetadataM_vtable_eq_checkPtrM]
    exact checkPtrM_vtablePtr_ok vptr traitName m vt hVAddr hvt hTrait
  have hvl : vtableLookupM m vptr = .ok vt :=
    (vtableFromPtrM_ok_iff_vtableLookupM_ok m vptr vt).mp hvt
  obtain ⟨layout, inhabited, cells, freeze, unpin⟩ := pointee
  dsimp only at hLayout
  subst hLayout
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee, Option.map]
    refine bind_congr_right _ (fun _ => ?_)
    rw [hMeta, checkPtrMetadataM_none, compute_size_and_align_tuple_traitObject, hvl,
      compute_size_and_align_sized]
    rfl
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee, Option.map]
    refine bind_congr_right _ (fun _ => ?_)
    rw [hMeta, checkPtrMetadataM_none, compute_size_and_align_tuple_traitObject, hvl,
      compute_size_and_align_sized]
    rfl

/-- **`isize::MAX` overflow UB on an unsized struct with a trait-object tail**:
when `TupleHeadLayout::full_size_and_align head vt.size vt.align` exceeds
`isize::MAX`, `check_ptr` raises `"Value::Ptr: total size exeeds isize::MAX"`
before checking non-null, alignment, inhabitedness, or dereferenceability (even
if `vt.size` alone fits in `isize::MAX`). -/
theorem checkPtr_tuple_traitObject_size_overflow_ub (thin vptr : Ptr)
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (head : Gen.TupleHeadLayout) (traitName : Gen.TraitName) (m : Mach) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .Tuple head (.TraitObject traitName))
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtr m vptr = .ok vt) (hTrait : vt.trait_name = traitName)
    (hOverflow :
      inBounds ((TupleHeadLayout.full_size_and_align head vt.size vt.align).1.bytes : Int)
        .Signed x86_64.PTR_SIZE = false) :
    checkPtr (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error (.ub "Value::Ptr: total size exeeds isize::MAX") := by
  rw [checkPtr_tuple_traitObject_eq_sized thin vptr mk pointee head traitName m vt
    hMk hLayout hVAddr hvt hTrait]
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hOverflow, ensureElseUb_false, error_bind]
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hOverflow, ensureElseUb_false, error_bind]

/-- Polymorphic `checkPtr_tuple_traitObject_size_overflow_ub`. -/
theorem checkPtrM_tuple_traitObject_size_overflow_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (head : Gen.TupleHeadLayout) (traitName : Gen.TraitName) (m : Gen.Machine M) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .Tuple head (.TraitObject traitName))
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtrM m vptr = .ok vt) (hTrait : vt.trait_name = traitName)
    (hOverflow :
      inBounds ((TupleHeadLayout.full_size_and_align head vt.size vt.align).1.bytes : Int)
        .Signed x86_64.PTR_SIZE = false) :
    checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error (.ub "Value::Ptr: total size exeeds isize::MAX") := by
  rw [checkPtrM_tuple_traitObject_eq_sized thin vptr mk pointee head traitName m vt
    hMk hLayout hVAddr hvt hTrait]
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hOverflow, ensureElseUb_false, error_bind]
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hOverflow, ensureElseUb_false, error_bind]

/-- `UnOp::ComputeSize` and `UnOp::ComputeAlign` on an unsized struct with a
trait-object tail (`Type::Tuple _ head (some (TraitObject trait_name))`) compute
`TupleHeadLayout::full_size_and_align head vt.size vt.align` with a machine. -/
theorem evalUnOp_tuple_traitObject_size_align (m : Mach) (vptr : Ptr)
    (fields : List (Gen.Offset × Gen.«Type»)) (head : Gen.TupleHeadLayout)
    (traitName : Gen.TraitName) (opTy : Gen.«Type») (vt : Gen.VTable)
    (hvt : vtableLookup m vptr = .ok vt) :
    evalUnOp (.ComputeSize (.Tuple fields head (some (.TraitObject traitName))))
        (.Ptr (ThinPointer.widen vptr none), opTy) (some m) =
      .ok (.Int ((TupleHeadLayout.full_size_and_align head vt.size vt.align).1.bytes : Int),
        .Int IntType.usize_ty) ∧
    evalUnOp (.ComputeAlign (.Tuple fields head (some (.TraitObject traitName))))
        (.Ptr (ThinPointer.widen vptr none), opTy) (some m) =
      .ok (.Int ((TupleHeadLayout.full_size_and_align head vt.size vt.align).2.bytes : Int),
        .Int IntType.usize_ty) := by
  constructor
  · have h : evalUnOp (.ComputeSize (.Tuple fields head (some (.TraitObject traitName))))
        (.Ptr (ThinPointer.widen vptr none), opTy) (some m) =
        (do
          let size ← computeSize m (.Tuple head (.TraitObject traitName))
            (some (.VTablePointer vptr))
          pure (.Int (size.bytes : Int), .Int IntType.usize_ty)) := rfl
    rw [h]
    unfold computeSize
    rw [compute_size_and_align_tuple_traitObject, hvt]
    rfl
  · have h : evalUnOp (.ComputeAlign (.Tuple fields head (some (.TraitObject traitName))))
        (.Ptr (ThinPointer.widen vptr none), opTy) (some m) =
        (do
          let align ← computeAlign m (.Tuple head (.TraitObject traitName))
            (some (.VTablePointer vptr))
          pure (.Int (align.bytes : Int), .Int IntType.usize_ty)) := rfl
    rw [h]
    unfold computeAlign
    rw [compute_size_and_align_tuple_traitObject, hvt]
    rfl

/-- Polymorphic `evalUnOp_tuple_traitObject_size_align` (in particular on `MachTB`). -/
theorem evalUnOpM_tuple_traitObject_size_align {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Gen.Machine M) (vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (fields : List (Gen.Offset × Gen.«Type»)) (head : Gen.TupleHeadLayout)
    (traitName : Gen.TraitName) (opTy : Gen.«Type») (vt : Gen.VTable)
    (hvt : vtableLookupM m vptr = .ok vt) :
    evalUnOpM (.ComputeSize (.Tuple fields head (some (.TraitObject traitName))))
        (.Ptr (ThinPointer.widen vptr none), opTy) (some m) =
      .ok (.Int ((TupleHeadLayout.full_size_and_align head vt.size vt.align).1.bytes : Int),
        .Int IntType.usize_ty) ∧
    evalUnOpM (.ComputeAlign (.Tuple fields head (some (.TraitObject traitName))))
        (.Ptr (ThinPointer.widen vptr none), opTy) (some m) =
      .ok (.Int ((TupleHeadLayout.full_size_and_align head vt.size vt.align).2.bytes : Int),
        .Int IntType.usize_ty) := by
  constructor
  · have h : evalUnOpM (.ComputeSize (.Tuple fields head (some (.TraitObject traitName))))
        (.Ptr (ThinPointer.widen vptr none), opTy) (some m) =
        (do
          let size ← computeSizeM m (.Tuple head (.TraitObject traitName))
            (some (.VTablePointer vptr))
          pure (.Int (size.bytes : Int), .Int IntType.usize_ty)) := rfl
    rw [h]
    unfold computeSizeM
    rw [compute_size_and_align_tuple_traitObject, hvt]
    rfl
  · have h : evalUnOpM (.ComputeAlign (.Tuple fields head (some (.TraitObject traitName))))
        (.Ptr (ThinPointer.widen vptr none), opTy) (some m) =
        (do
          let align ← computeAlignM m (.Tuple head (.TraitObject traitName))
            (some (.VTablePointer vptr))
          pure (.Int (align.bytes : Int), .Int IntType.usize_ty)) := rfl
    rw [h]
    unfold computeAlignM
    rw [compute_size_and_align_tuple_traitObject, hvt]
    rfl

/-! ## `UnOp::GetMetadata`: one sanity check for every metadata kind

Upstream runs `self.check_value(meta_value, meta_ty).expect(..)` for every
metadata kind (`spec/lang/step/operators.md`). `evalUnOp` and `evalUnOpM` spell
that check twice: once for vtable metadata, where it needs a machine, and once
for the other kinds. The vtable branch separates UB of `check_value`, which
`.expect(..)` turns into the sanity-check panic, from a panic inside
`check_value`, which propagates; the other branch maps every error to the
sanity-check panic. The results below show that the two branches agree:
`check_value` of the unit and `usize` metadata values succeeds or is UB, so it
has no other stop that the second branch could mask, and whenever the check
runs `GetMetadata` is the single expression `getMetadataSanity`. -/

/-- Upstream's `.expect(..)` on the `check_value` sanity check of
`UnOp::GetMetadata`: UB of the check becomes the sanity-check panic, and any
other stop (a panic inside `check_value`) propagates unchanged. -/
def getMetadataSanity {α : Type} (check : Interp Unit) (result : α) : Interp α :=
  match check with
  | .ok () => pure result
  | .error (.ub _) => specPanic "GetMetadata: sanity check, returned meta is well-formed"
  | .error e => .error e

/-- `check_value` of the metadata value of a thin or slice pointer succeeds or
is UB, with or without a machine: it never panics and never reads the machine. -/
theorem checkValue_nonVTable_meta_ok_or_ub (kind : Gen.PointerMetaKind)
    (pm : Option (Gen.PointerMeta Prov)) (m : Option Mach) (mv : Val)
    (hk : ∀ t, kind ≠ .VTablePointer t)
    (henc : PointerMetaKind.encode_as_value kind pm = .ok mv) :
    checkValue mv (PointerMetaKind.ty kind) m = .ok () ∨
      ∃ msg, checkValue mv (PointerMetaKind.ty kind) m = .error (.ub msg) := by
  cases kind with
  | VTablePointer t => exact absurd rfl (hk t)
  | None =>
    cases pm with
    | some _ => cases henc
    | none =>
      cases henc
      exact Or.inl (by rw [PointerMetaKind.ty, unitType, checkValue]; rfl)
  | ElementCount =>
    cases pm with
    | none => cases henc
    | some pmv =>
      cases pmv with
      | VTablePointer p => cases henc
      | ElementCount c =>
        cases henc
        cases hc : IntType.can_represent IntType.usize_ty c with
        | true => exact Or.inl (by rw [PointerMetaKind.ty, checkValue, ensureElseUb, hc]; rfl)
        | false => exact Or.inr ⟨_, by rw [PointerMetaKind.ty, checkValue, ensureElseUb, hc]; rfl⟩

/-- Polymorphic `checkValue_nonVTable_meta_ok_or_ub` (in particular Tree Borrows). -/
theorem checkValueM_nonVTable_meta_ok_or_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (kind : Gen.PointerMetaKind) (pm : Option (Gen.PointerMeta (Gen.Memory.Provenance M)))
    (m : Option (Gen.Machine M)) (mv : Gen.Value M)
    (hk : ∀ t, kind ≠ .VTablePointer t)
    (henc : PointerMetaKind.encode_as_valueM (M := M) kind pm = .ok mv) :
    checkValueM mv (PointerMetaKind.ty kind) m = .ok () ∨
      ∃ msg, checkValueM mv (PointerMetaKind.ty kind) m = .error (.ub msg) := by
  cases kind with
  | VTablePointer t => exact absurd rfl (hk t)
  | None =>
    cases pm with
    | some _ => cases henc
    | none =>
      cases henc
      exact Or.inl (by rw [PointerMetaKind.ty, unitType, checkValueM]; rfl)
  | ElementCount =>
    cases pm with
    | none => cases henc
    | some pmv =>
      cases pmv with
      | VTablePointer p => cases henc
      | ElementCount c =>
        cases henc
        cases hc : IntType.can_represent IntType.usize_ty c with
        | true => exact Or.inl (by rw [PointerMetaKind.ty, checkValueM, ensureElseUb, hc]; rfl)
        | false => exact Or.inr ⟨_, by rw [PointerMetaKind.ty, checkValueM, ensureElseUb, hc]; rfl⟩

/-- Whenever its sanity check runs (the metadata kind is not a vtable pointer,
or a machine is supplied), `UnOp::GetMetadata` is upstream's single expression:
`encode_as_value`, then `check_value(..).expect(..)` (`getMetadataSanity`).
The two branches of `evalUnOp` therefore differ only in the machine-free
vtable case, which stops with `unsupported` before the check. -/
theorem evalUnOp_getMetadata_eq_sanity (ptr : Gen.Pointer Prov) (ptrTy : Gen.PtrType)
    (m : Option Mach)
    (h : (∀ t, PtrType.meta_kind ptrTy ≠ .VTablePointer t) ∨ ∃ mach, m = some mach) :
    evalUnOp .GetMetadata (.Ptr ptr, .Ptr ptrTy) m =
      (PointerMetaKind.encode_as_value (PtrType.meta_kind ptrTy) ptr.metadata >>= fun mv =>
        getMetadataSanity (checkValue mv (PointerMetaKind.ty (PtrType.meta_kind ptrTy)) m)
          (mv, PointerMetaKind.ty (PtrType.meta_kind ptrTy))) := by
  rw [evalUnOp]
  dsimp only
  cases henc : PointerMetaKind.encode_as_value (PtrType.meta_kind ptrTy) ptr.metadata with
  | error e => rfl
  | ok mv =>
    simp only [bind, Except.bind]
    cases hk : PtrType.meta_kind ptrTy with
    | VTablePointer t =>
      rcases h with h | ⟨mach, rfl⟩
      · exact absurd hk (h t)
      · dsimp only
        cases checkValue mv (PointerMetaKind.ty (.VTablePointer t)) (some mach) with
        | ok u => cases u; rfl
        | error e => cases e <;> rfl
    | None =>
      rw [hk] at henc
      rcases checkValue_nonVTable_meta_ok_or_ub _ _ m mv (by intro t ht; cases ht) henc with
        hc | ⟨msg, hc⟩ <;> (dsimp only; rw [hc]; rfl)
    | ElementCount =>
      rw [hk] at henc
      rcases checkValue_nonVTable_meta_ok_or_ub _ _ m mv (by intro t ht; cases ht) henc with
        hc | ⟨msg, hc⟩ <;> (dsimp only; rw [hc]; rfl)

/-- Polymorphic `evalUnOp_getMetadata_eq_sanity` (in particular Tree Borrows). -/
theorem evalUnOpM_getMetadata_eq_sanity {M : Type} [Gen.Memory M] [MemoryOps M]
    (ptr : Gen.Pointer (Gen.Memory.Provenance M)) (ptrTy : Gen.PtrType)
    (m : Option (Gen.Machine M))
    (h : (∀ t, PtrType.meta_kind ptrTy ≠ .VTablePointer t) ∨ ∃ mach, m = some mach) :
    evalUnOpM (M := M) .GetMetadata (.Ptr ptr, .Ptr ptrTy) m =
      (PointerMetaKind.encode_as_valueM (M := M) (PtrType.meta_kind ptrTy) ptr.metadata >>=
        fun mv =>
          getMetadataSanity (checkValueM mv (PointerMetaKind.ty (PtrType.meta_kind ptrTy)) m)
            (mv, PointerMetaKind.ty (PtrType.meta_kind ptrTy))) := by
  rw [evalUnOpM]
  dsimp only
  cases henc : PointerMetaKind.encode_as_valueM (M := M) (PtrType.meta_kind ptrTy)
      ptr.metadata with
  | error e => rfl
  | ok mv =>
    simp only [bind, Except.bind]
    cases hk : PtrType.meta_kind ptrTy with
    | VTablePointer t =>
      rcases h with h | ⟨mach, rfl⟩
      · exact absurd hk (h t)
      · dsimp only
        cases checkValueM mv (PointerMetaKind.ty (.VTablePointer t)) (some mach) with
        | ok u => cases u; rfl
        | error e => cases e <;> rfl
    | None =>
      rw [hk] at henc
      rcases checkValueM_nonVTable_meta_ok_or_ub _ _ m mv (by intro t ht; cases ht) henc with
        hc | ⟨msg, hc⟩ <;> (dsimp only; rw [hc]; rfl)
    | ElementCount =>
      rw [hk] at henc
      rcases checkValueM_nonVTable_meta_ok_or_ub _ _ m mv (by intro t ht; cases ht) henc with
        hc | ⟨msg, hc⟩ <;> (dsimp only; rw [hc]; rfl)

/-- The sanity check of `UnOp::GetMetadata` on a thin or slice pointer cannot
hide a stop of `check_value`: the operator succeeds, panics in
`encode_as_value` (metadata of the wrong kind), or raises the sanity-check
panic for a slice length that is not a `usize`. Stated for the polymorphic
`evalUnOpM`, that is, for every memory model. -/
theorem evalUnOpM_getMetadata_nonVTable_ok_or_specPanic {M : Type} [Gen.Memory M] [MemoryOps M]
    (ptr : Gen.Pointer (Gen.Memory.Provenance M)) (ptrTy : Gen.PtrType)
    (m : Option (Gen.Machine M))
    (hk : ∀ t, PtrType.meta_kind ptrTy ≠ .VTablePointer t) :
    (∃ r, evalUnOpM (M := M) .GetMetadata (.Ptr ptr, .Ptr ptrTy) m = .ok r) ∨
    evalUnOpM (M := M) .GetMetadata (.Ptr ptr, .Ptr ptrTy) m =
      specPanic "PointerMeta::encode_as_value called with invalid value" ∨
    evalUnOpM (M := M) .GetMetadata (.Ptr ptr, .Ptr ptrTy) m =
      specPanic "GetMetadata: sanity check, returned meta is well-formed" := by
  rw [evalUnOpM_getMetadata_eq_sanity ptr ptrTy m (Or.inl hk)]
  cases henc : PointerMetaKind.encode_as_valueM (M := M) (PtrType.meta_kind ptrTy)
      ptr.metadata with
  | error e =>
    refine Or.inr (Or.inl ?_)
    unfold PointerMetaKind.encode_as_valueM at henc
    split at henc <;> cases henc <;> rfl
  | ok mv =>
    rcases checkValueM_nonVTable_meta_ok_or_ub _ _ m mv hk henc with hc | ⟨msg, hc⟩
    · exact Or.inl ⟨_, by simp only [bind, Except.bind, hc]; rfl⟩
    · exact Or.inr (Or.inr (by simp only [bind, Except.bind, hc]; rfl))

/-! ## ZST, null, uninhabited, `PlaceExpr::Deref`, and `ConstructWidePointer`
boundary for trait-object pointers (`Mach` & `MachTB`)

Completes the universal error-precedence and ZST characterization of
`checkPtr[M]` on `&dyn Trait`, `&mut dyn Trait`, and `Box<dyn Trait>`, proves
that Tree Borrows `retag_ptr` on a provenance-free ZST trait-object pointer is
the identity (leaving memory and protectors unchanged), characterizes
`PlaceExpr::Deref` on safe trait-object pointers, and pins the fail-closed
`BinOp::ConstructWidePointer` boundary alongside `PointerMetaKind::decode_value`
for `VTablePointer` metadata. -/

/-- **A null trait-object safe pointer is UB** (`"Value::Ptr: null safe pointer"`)
whenever its vtable metadata is valid and its dynamic size fits in `isize::MAX`,
preceding alignment, inhabitedness, and `Memory::dereferenceable`. -/
theorem checkPtr_traitObject_null_ub (thin vptr : Ptr)
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (m : Mach) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtr m vptr = .ok vt) (hTrait : vt.trait_name = traitName)
    (hSize : inBounds (vt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true)
    (hNull : thin.addr = 0) :
    checkPtr (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error (.ub "Value::Ptr: null safe pointer") := by
  rw [checkPtr_traitObject_eq_sized thin vptr mk pointee traitName m vt hMk hLayout hVAddr hvt
    hTrait]
  have hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true := by rw [hNull]; decide
  have hNonNull : (thin.addr != 0) = false := by rw [hNull]; decide
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_false, error_bind]
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_false, error_bind]

/-- Polymorphic `checkPtr_traitObject_null_ub` (in particular on `MachTB`). -/
theorem checkPtrM_traitObject_null_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (m : Gen.Machine M) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtrM m vptr = .ok vt) (hTrait : vt.trait_name = traitName)
    (hSize : inBounds (vt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true)
    (hNull : thin.addr = 0) :
    checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error (.ub "Value::Ptr: null safe pointer") := by
  rw [checkPtrM_traitObject_eq_sized thin vptr mk pointee traitName m vt hMk hLayout hVAddr hvt
    hTrait]
  have hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true := by rw [hNull]; decide
  have hNonNull : (thin.addr != 0) = false := by rw [hNull]; decide
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_false, error_bind]
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_false, error_bind]

/-- **A safe pointer to an uninhabited trait object (`pointee.inhabited = false`)
is UB** (`"Value::Ptr: safe pointer to uninhabited type"`) once vtable metadata,
size, non-nullness, and alignment pass — unconditionally, preceding
`Memory::dereferenceable` (even for ZST or dangling provenance-free pointers). -/
theorem checkPtr_traitObject_uninhabited_ub (thin vptr : Ptr)
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (m : Mach) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtr m vptr = .ok vt) (hTrait : vt.trait_name = traitName)
    (hSize : inBounds (vt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true)
    (hNonNull : (thin.addr != 0) = true)
    (hAligned : Align.is_aligned vt.align thin.addr = true)
    (hUninh : pointee.inhabited = false) :
    checkPtr (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error (.ub "Value::Ptr: safe pointer to uninhabited type") := by
  rw [checkPtr_traitObject_eq_sized thin vptr mk pointee traitName m vt hMk hLayout hVAddr hvt
    hTrait]
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hAligned, ensureElseUb_true, ok_bind,
      hUninh, ensureElseUb_false, error_bind]
  · unfold checkPtr
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadata_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hAligned, ensureElseUb_true, ok_bind,
      hUninh, ensureElseUb_false, error_bind]

/-- Polymorphic `checkPtr_traitObject_uninhabited_ub` (in particular `MachTB`). -/
theorem checkPtrM_traitObject_uninhabited_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (m : Gen.Machine M) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtrM m vptr = .ok vt) (hTrait : vt.trait_name = traitName)
    (hSize : inBounds (vt.size.bytes : Int) .Signed x86_64.PTR_SIZE = true)
    (hNonNull : (thin.addr != 0) = true)
    (hAligned : Align.is_aligned vt.align thin.addr = true)
    (hUninh : pointee.inhabited = false) :
    checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .error (.ub "Value::Ptr: safe pointer to uninhabited type") := by
  rw [checkPtrM_traitObject_eq_sized thin vptr mk pointee traitName m vt hMk hLayout hVAddr hvt
    hTrait]
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hAligned, ensureElseUb_true, ok_bind,
      hUninh, ensureElseUb_false, error_bind]
  · unfold checkPtrM
    dsimp only [ThinPointer.widen, PtrType.meta_kind, LayoutStrategy.meta_kind,
      PtrType.safe_pointee]
    rw [hAddr, ensureElseUb_true, ok_bind, checkPtrMetadataM_none, ok_bind,
      compute_size_and_align_sized, ok_bind, hSize, ensureElseUb_true, ok_bind,
      hNonNull, ensureElseUb_true, ok_bind, hAligned, ensureElseUb_true, ok_bind,
      hUninh, ensureElseUb_false, error_bind]

/-- **A ZST trait-object safe pointer (`vt.size = 0`) passes `checkPtr` without
provenance or any live data allocation** on `Mach` (`BasicMemory`), provided
its address is in bounds, non-null, and aligned to `vt.align`, and the pointee
is inhabited. -/
theorem checkPtr_traitObject_zst_ok (thin vptr : Ptr)
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (m : Mach) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtr m vptr = .ok vt) (hTrait : vt.trait_name = traitName)
    (hZero : vt.size = ⟨0⟩)
    (hNonNull : (thin.addr != 0) = true)
    (hAligned : Align.is_aligned vt.align thin.addr = true)
    (hInhabited : pointee.inhabited = true) :
    checkPtr (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee) (some m) =
      .ok () :=
  checkPtr_traitObject_ok thin vptr mk pointee traitName m vt hMk hLayout hAddr hVAddr hvt hTrait
    (by rw [hZero]; decide) hNonNull hAligned hInhabited (by rw [hZero]; rfl)

/-- **A ZST trait-object safe pointer (`vt.size = 0`) passes `checkPtrM` without
provenance or any live data allocation** on `MachTB` (`TreeBorrowsMemory`). -/
theorem checkPtrM_traitObject_zst_tb_ok
    (thin vptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (m : MachTB) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hAddr : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true)
    (hVAddr : inBounds vptr.addr .Unsigned x86_64.PTR_SIZE = true)
    (hvt : vtableFromPtrM m vptr = .ok vt) (hTrait : vt.trait_name = traitName)
    (hZero : vt.size = ⟨0⟩)
    (hNonNull : (thin.addr != 0) = true)
    (hAligned : Align.is_aligned vt.align thin.addr = true)
    (hInhabited : pointee.inhabited = true) :
    checkPtrM (M := TBM) (ThinPointer.widen thin (some (.VTablePointer vptr))) (mk pointee)
      (some m) = .ok () :=
  checkPtrM_traitObject_ok (M := TBM) thin vptr mk pointee traitName m vt hMk hLayout hAddr hVAddr
    hvt hTrait (by rw [hZero]; decide) hNonNull hAligned hInhabited (by rw [hZero]; rfl)

/-- **Tree Borrows `retag_ptr` on a provenance-free ZST trait-object pointer is
the identity**: for `&dyn Trait`, `&mut dyn Trait`, or `Box<dyn Trait>` whose
vtable has `size = 0` and `cells = []`, retagging a `provenance = none` pointer
succeeds for every `fnEntry` / `fnImplicitWrites` / `freeze` / `unpin`, leaves
memory and `frameExtra.protectors` untouched, and therefore trivially preserves
`TreeBorrowsMemory.wfLive`. -/
theorem retag_ptr_traitObject_zst_noProv
    (tbm : Gen.TreeBorrowsMemory Gen.x86_64) (frameExtra : Gen.TreeBorrowsFrameExtra)
    (thin vptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (fnEntry fnImplicitWrites : Bool)
    (vtableLookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable)
    (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hCells : pointee.unsafe_cells = .TraitObject)
    (hvt : vtableLookup vptr = .ok vt)
    (hSize : vt.size = ⟨0⟩) (hVtCells : vt.cells = [])
    (hProv : thin.provenance = none) :
    let ptr := ThinPointer.widen thin (some (.VTablePointer vptr))
    TreeBorrowsMemory.retag_ptr tbm frameExtra ptr (mk pointee) fnEntry fnImplicitWrites
        vtableLookup = .ok (ptr, tbm, frameExtra) := by
  intro ptr
  have hFreeze : UnsafeCellStrategy.freeze_mask vtableLookup .TraitObject
      (.TraitObject traitName) (some (.VTablePointer vptr)) = .ok [] := by
    unfold UnsafeCellStrategy.freeze_mask
    rw [hvt, ok_bind, hVtCells, hSize]
    rfl
  have hReb : ∀ (outside : Gen.Permission) (prot : Gen.Protected),
      TreeBorrowsMemory.reborrow tbm thin
        { inside := [], outside := outside, «protected» := prot } frameExtra =
        .ok (thin, tbm, frameExtra) := by
    intro outside prot
    unfold TreeBorrowsMemory.reborrow
    have hchk : BasicMemory.check_ptr tbm.mem thin ⟨0⟩ = .ok none := rfl
    dsimp only [List.length]
    rw [hchk, ok_bind, hProv]
    rfl
  obtain ⟨layout, inhabited, cells, freeze, unpin⟩ := pointee
  dsimp only at hLayout hCells
  subst hLayout; subst hCells
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · cases mutbl with
    | Immutable =>
      unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
      simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.false_eq_true, ↓reduceIte,
        hFreeze, ok_bind, List.mapM_nil, pure_ok, ReborrowSettings.perm]
      cases freeze <;> simp only [Bool.false_eq_true, ↓reduceIte, ok_bind, hReb]
    | Mutable =>
      cases unpin with
      | false =>
        unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
        simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.not_false, ↓reduceIte,
          pure_ok, ok_bind]
      | true =>
        unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
        simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, hFreeze, ok_bind, List.mapM_nil, pure_ok, ReborrowSettings.perm,
          Bool.and_false, hReb]
  · cases unpin with
    | false =>
      unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
      simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.not_false, ↓reduceIte,
        pure_ok, ok_bind]
    | true =>
      unfold TreeBorrowsMemory.retag_ptr ReborrowSettings.new
      simp only [ptr, ThinPointer.widen, PtrType.safe_pointee, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, hFreeze, ok_bind, List.mapM_nil, pure_ok, ReborrowSettings.perm,
        Bool.and_false, hReb]

/-- **`PlaceExpr::Deref` on a safe trait-object pointer (`Mach`)**: once the
operand evaluates to an aligned `&dyn Trait`, `&mut dyn Trait`, or
`Box<dyn Trait>`, dereferencing runs `CM.dereferenceable` for `vt.size` bytes
directly (propagating raw `BasicMemory::check_ptr` UB on dead/undersized
allocations, or succeeding on ZST `vt.size = 0` without provenance) and returns
an `aligned = true` place at `Type::TraitObject traitName`. -/
theorem evalPlace_deref_safe_traitObject (m m1 : Mach) (operand : Gen.ValueExpr)
    (thin vptr : Ptr) (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hOp : evalValue m operand =
      .ok ((.Ptr (ThinPointer.widen thin (some (.VTablePointer vptr))), .Ptr (mk pointee)), m1))
    (hvt : vtableLookup m1 vptr = .ok vt)
    (hAl : Align.is_aligned vt.align thin.addr = true) :
    evalPlace m (.Deref operand (.TraitObject traitName)) =
      (CM.dereferenceable m1.mem thin vt.size >>= fun _ =>
        pure (({ ptr := ThinPointer.widen thin (some (.VTablePointer vptr)),
                 aligned := true }, .TraitObject traitName), m1)) := by
  have hca : computeAlign m1 (.TraitObject traitName) (some (.VTablePointer vptr)) =
      .ok vt.align := by
    unfold computeAlign
    rw [compute_size_and_align_traitObject, hvt]
    rfl
  have hcs : computeSize m1 (.TraitObject traitName) (some (.VTablePointer vptr)) =
      .ok vt.size := by
    unfold computeSize
    rw [compute_size_and_align_traitObject, hvt]
    rfl
  have hlay : Type.layout (.TraitObject traitName) = .ok (.TraitObject traitName) := rfl
  unfold evalPlace
  rw [hOp, ok_bind]
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · dsimp only [ThinPointer.widen, PtrType.safe_pointee]
    rw [hLayout, hca, ok_bind, hAl]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcs, ok_bind]
    refine bind_congr_right _ (fun _ => ?_)
    rw [hlay, ok_bind, hca, ok_bind, hAl]
  · dsimp only [ThinPointer.widen, PtrType.safe_pointee]
    rw [hLayout, hca, ok_bind, hAl]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcs, ok_bind]
    refine bind_congr_right _ (fun _ => ?_)
    rw [hlay, ok_bind, hca, ok_bind, hAl]

/-- Polymorphic `evalPlace_deref_safe_traitObject` (in particular on `MachTB`). -/
theorem evalPlaceM_deref_safe_traitObject {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Gen.Machine M) (operand : Gen.ValueExpr)
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (mk : Gen.PointeeInfo → Gen.PtrType) (pointee : Gen.PointeeInfo)
    (traitName : Gen.TraitName) (vt : Gen.VTable)
    (hMk : (∃ mutbl, mk = Gen.PtrType.Ref mutbl) ∨ mk = Gen.PtrType.Box)
    (hLayout : pointee.layout = .TraitObject traitName)
    (hOp : evalValueM m operand =
      .ok ((.Ptr (ThinPointer.widen thin (some (.VTablePointer vptr))), .Ptr (mk pointee)), m1))
    (hvt : vtableLookupM m1 vptr = .ok vt)
    (hAl : Align.is_aligned vt.align thin.addr = true) :
    evalPlaceM m (.Deref operand (.TraitObject traitName)) =
      (ConcurrentMemory.dereferenceable m1.mem thin vt.size >>= fun _ =>
        pure (({ ptr := ThinPointer.widen thin (some (.VTablePointer vptr)),
                 aligned := true }, .TraitObject traitName), m1)) := by
  have hca : computeAlignM m1 (.TraitObject traitName) (some (.VTablePointer vptr)) =
      .ok vt.align := by
    unfold computeAlignM
    rw [compute_size_and_align_traitObject, hvt]
    rfl
  have hcs : computeSizeM m1 (.TraitObject traitName) (some (.VTablePointer vptr)) =
      .ok vt.size := by
    unfold computeSizeM
    rw [compute_size_and_align_traitObject, hvt]
    rfl
  have hlay : Type.layout (.TraitObject traitName) = .ok (.TraitObject traitName) := rfl
  unfold evalPlaceM
  rw [hOp, ok_bind]
  rcases hMk with ⟨mutbl, rfl⟩ | rfl
  · dsimp only [ThinPointer.widen, PtrType.safe_pointee]
    rw [hLayout, hca, ok_bind, hAl]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcs, ok_bind]
    refine bind_congr_right _ (fun _ => ?_)
    rw [hlay, ok_bind, hca, ok_bind, hAl]
  · dsimp only [ThinPointer.widen, PtrType.safe_pointee]
    rw [hLayout, hca, ok_bind, hAl]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcs, ok_bind]
    refine bind_congr_right _ (fun _ => ?_)
    rw [hlay, ok_bind, hca, ok_bind, hAl]

/-- **`BinOp::ConstructWidePointer` fail-closed boundary (`evalBinOp`)**:
`evalBinOp` fails closed with `unsupported` on `BinOp::ConstructWidePointer`. -/
theorem evalBinOp_constructWidePointer_unsupported (ptrTy : Gen.PtrType)
    (l r : Val × Gen.«Type») :
    evalBinOp (.ConstructWidePointer ptrTy) l r =
      .error (.unsupported
        "eval_bin_op for an operator outside BinOp::Int, BinOp::IntWithOverflow, and BinOp::Rel") :=
  rfl

/-- Polymorphic **`BinOp::ConstructWidePointer` fail-closed boundary
(`evalBinOpM`)** across every `Memory` `M` (including `MachTB`). -/
theorem evalBinOpM_constructWidePointer_unsupported {M : Type} [Gen.Memory M]
    (ptrTy : Gen.PtrType) (l r : Gen.Value M × Gen.«Type») :
    evalBinOpM (M := M) (.ConstructWidePointer ptrTy) l r =
      .error (.unsupported
        "eval_bin_op for an operator outside BinOp::Int, BinOp::IntWithOverflow, and BinOp::Rel") :=
  rfl

/-- Inside `evalValue`, `BinOp::ConstructWidePointer` evaluates both operands
first (propagating any operand UB or panic) and then fails closed with
`unsupported`. -/
theorem evalValue_constructWidePointer_ok_operands_unsupported (m m1 m2 : Mach)
    (ptrTy : Gen.PtrType) (left right : Gen.ValueExpr) (l r : Val × Gen.«Type»)
    (hl : evalValue m left = .ok (l, m1))
    (hr : evalValue m1 right = .ok (r, m2)) :
    evalValue m (.BinOp (.ConstructWidePointer ptrTy) left right) =
      .error (.unsupported
        "eval_bin_op for an operator outside BinOp::Int, BinOp::IntWithOverflow, and BinOp::Rel") := by
  unfold evalValue
  rw [hl, ok_bind]; dsimp only
  rw [hr, ok_bind]; dsimp only
  rw [evalBinOp_constructWidePointer_unsupported, error_bind]

/-- Polymorphic `evalValue_constructWidePointer_ok_operands_unsupported`
(in particular on `MachTB`). -/
theorem evalValueM_constructWidePointer_ok_operands_unsupported {M : Type}
    [Gen.Memory M] [MemoryOps M] (m m1 m2 : Gen.Machine M)
    (ptrTy : Gen.PtrType) (left right : Gen.ValueExpr) (l r : Gen.Value M × Gen.«Type»)
    (hl : evalValueM m left = .ok (l, m1))
    (hr : evalValueM m1 right = .ok (r, m2)) :
    evalValueM m (.BinOp (.ConstructWidePointer ptrTy) left right) =
      .error (.unsupported
        "eval_bin_op for an operator outside BinOp::Int, BinOp::IntWithOverflow, and BinOp::Rel") := by
  unfold evalValueM
  rw [hl, ok_bind]; dsimp only
  rw [hr, ok_bind]; dsimp only
  rw [evalBinOpM_constructWidePointer_unsupported, error_bind]

/-- `PointerMetaKind.decode_value` on vtable-pointer metadata followed by
`checkValue` (the core of upstream `BinOp::ConstructWidePointer` on `dyn Trait`
pointers): a thin vtable pointer decodes to `some (.VTablePointer vptr)` and
`checkValue` reduces directly to `checkPtr` on the constructed wide pointer;
any non-pointer or wide-pointer right operand panics with
`"PointerMeta::decode_value called with invalid value"`. -/
theorem decode_vtablePointer_and_checkValue_dyn (thin vptr : Ptr)
    (ptrTy : Gen.PtrType) (traitName : Gen.TraitName) (m : Option Mach)
    (hMeta : PtrType.meta_kind ptrTy = .VTablePointer traitName) :
    (PointerMetaKind.decode_value (PtrType.meta_kind ptrTy)
        (.Ptr (ThinPointer.widen vptr none)) = .ok (some (.VTablePointer vptr)) ∧
     checkValue (.Ptr (ThinPointer.widen thin (some (.VTablePointer vptr))))
        (.Ptr ptrTy) m =
      checkPtr (ThinPointer.widen thin (some (.VTablePointer vptr))) ptrTy m) ∧
    (∀ (badRight : Val), (∀ p, badRight ≠ .Ptr (ThinPointer.widen p none)) →
      PointerMetaKind.decode_value (PtrType.meta_kind ptrTy) badRight =
        specPanic "PointerMeta::decode_value called with invalid value") := by
  refine ⟨⟨by rw [hMeta]; rfl, rfl⟩, fun badRight hBad => ?_⟩
  rw [hMeta]
  cases badRight with
  | Ptr p =>
    cases p with
    | mk tp mp =>
      cases mp with
      | none => exact absurd rfl (hBad tp)
      | some _ => rfl
  | _ => rfl

/-- Polymorphic `decode_vtablePointer_and_checkValue_dyn` (in particular on
`MachTB`). -/
theorem decode_vtablePointer_and_checkValueM_dyn {M : Type} [Gen.Memory M] [MemoryOps M]
    (thin vptr : Gen.ThinPointer (Gen.Memory.Provenance M))
    (ptrTy : Gen.PtrType) (traitName : Gen.TraitName) (m : Option (Gen.Machine M))
    (hMeta : PtrType.meta_kind ptrTy = .VTablePointer traitName) :
    (PointerMetaKind.decode_valueM (M := M) (PtrType.meta_kind ptrTy)
        (.Ptr (ThinPointer.widen vptr none)) = .ok (some (.VTablePointer vptr)) ∧
     checkValueM (.Ptr (ThinPointer.widen thin (some (.VTablePointer vptr))))
        (.Ptr ptrTy) m =
      checkPtrM (ThinPointer.widen thin (some (.VTablePointer vptr))) ptrTy m) ∧
    (∀ (badRight : Gen.Value M), (∀ p, badRight ≠ .Ptr (ThinPointer.widen p none)) →
      PointerMetaKind.decode_valueM (M := M) (PtrType.meta_kind ptrTy) badRight =
        specPanic "PointerMeta::decode_value called with invalid value") := by
  refine ⟨⟨by rw [hMeta]; rfl, rfl⟩, fun badRight hBad => ?_⟩
  rw [hMeta]
  cases badRight with
  | Ptr p =>
    cases p with
    | mk tp mp =>
      cases mp with
      | none => exact absurd rfl (hBad tp)
      | some _ => rfl
  | _ => rfl

end MiniRustSpec.Correspondence
