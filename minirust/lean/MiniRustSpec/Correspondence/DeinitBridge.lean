/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Mir.AdtAndControl
import MiniRustSpec.Correspondence.AnnealEval
import MiniRustSpec.Correspondence.DeinitLemmas

/-!
# Projected `Deinit`: Anneal's `PartialShell` model and MiniRust's byte-slice `Uninit` store

`Trusted.MirSemantics.evalStmt` keeps the value of a projected `Deinit` place (it only checks that
the place is readable, `Statements.lean:2593-2600`), whereas MiniRust's `Statement::Deinit` stores
`AbstractByte::Uninit` over the place's byte slice and leaves every other byte intact.
`crates/anneal-mir`'s projected `Deinit` (formalized as
`Anneal.Mir.AdtAndControl.evalDeinitPlace`) explodes the local into a `PartialShell` whose
deinitialized part is `Uninit`. This module connects that model with MiniRust's actual memory
operation, without any flow-sensitive overwrite guard:

* `toAbstractBytes` reads Anneal's reference byte image (`ByteImage = List (Option UInt8)`:
  `none` is `Uninit`) as MiniRust abstract bytes (`Uninit` / provenance-free `Init b`);
* `toAbstractBytes_deinitBytes`: Anneal's `deinitBytes img off len` is exactly MiniRust's
  `write_subslice_at_index` of `len` `Uninit` bytes at `off` (`spliceAt`);
* `evalDeinitPlace_spec_minirust_store_simulation`: for a spec-laid-out ADT local whose MiniRust
  allocation holds the image of Anneal's initialized slot, MiniRust's `ConcurrentMemory::store` of
  the `Uninit` slice at the place's byte range (`pathRange`, which is also the synthetic sub-place
  range `subplaceAt` of `Anneal.Mir.AdtAndControl`) succeeds; its new allocation holds the image
  `deinitBytes img off len`, which represents Anneal's post-`Deinit` `PartialShell`
  (`Anneal.Mir.AdtAndControl.evalDeinitPlace_spec_bytes_simulation`), while every byte outside the
  slice is unchanged.

This is the only `MiniRustSpec` module that imports `Anneal.Mir.AdtAndControl`.
`Correspondence.IntrinsicBoundary` imports it, so `lake build MiniRustSpec` builds this module and
`Anneal.Mir.AdtAndControl` (which is not part of the default `Anneal` target), and
`MiniRustSpec.Audit` audits it: `#assert_all_minirustspec_standard_axioms` covers every declaration
of this module, and its `[DEINIT-AUDIT]` group pins its theorems, including
`subplace_audit_closure`.
-/

namespace MiniRustSpec.Correspondence.DeinitBridge

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-- Anneal's reference byte image as MiniRust abstract bytes: `none` is `Uninit`, `some b` the
provenance-free initialized byte `b`. -/
def toAbstractBytes (img : Anneal.Mir.AdtAndControl.ByteImage) : List Byte :=
  img.map fun
    | none => .Uninit
    | some b => .Init b none

theorem length_toAbstractBytes (img : Anneal.Mir.AdtAndControl.ByteImage) :
    (toAbstractBytes img).length = img.length := by
  simp [toAbstractBytes]

/-- **Anneal's `deinitBytes` is MiniRust's `Uninit` slice store (`toAbstractBytes_deinitBytes`)**:
writing `Uninit` over `[off, off + len)` of an image in Anneal's reference model is MiniRust's
`write_subslice_at_index` of `len` `Uninit` bytes at `off`. -/
theorem toAbstractBytes_deinitBytes (img : Anneal.Mir.AdtAndControl.ByteImage) (off len : Nat)
    (h : off + len ≤ img.length) :
    toAbstractBytes (Anneal.Mir.AdtAndControl.deinitBytes img off len) =
      (toAbstractBytes img).take off ++ List.replicate len .Uninit ++
        (toAbstractBytes img).drop (off + len) := by
  apply List.ext_getElem?
  intro i
  have hLA := length_toAbstractBytes img
  have hTake : ((toAbstractBytes img).take off).length = off := by
    rw [List.length_take, hLA]; omega
  have hAB : ((toAbstractBytes img).take off ++
      List.replicate len (Gen.AbstractByte.Uninit : Byte)).length = off + len := by
    rw [List.length_append, hTake, List.length_replicate]
  have hMap : ∀ j : Nat, (toAbstractBytes img)[j]? = img[j]?.map (fun
      | none => (Gen.AbstractByte.Uninit : Byte)
      | some b => .Init b none) := fun j => by simp only [toAbstractBytes, List.getElem?_map]
  by_cases hIn : off ≤ i ∧ i < off + len
  · have hD := Anneal.Mir.AdtAndControl.deinitBytes_getElem?_inside (img := img) hIn (by omega)
    have hLHS : (toAbstractBytes (Anneal.Mir.AdtAndControl.deinitBytes img off len))[i]? =
        some .Uninit := by
      simp [toAbstractBytes, hD]
    rw [hLHS, List.getElem?_append_left (by rw [hAB]; omega),
      List.getElem?_append_right (by rw [hTake]; omega), hTake, List.getElem?_replicate]
    simp [show i - off < len by omega]
  · have hD := Anneal.Mir.AdtAndControl.deinitBytes_getElem?_outside (img := img) hIn
    have hLHS : (toAbstractBytes (Anneal.Mir.AdtAndControl.deinitBytes img off len))[i]? =
        (toAbstractBytes img)[i]? := by
      rw [hMap]
      simp [toAbstractBytes, hD]
    rw [hLHS]
    rcases Nat.lt_or_ge i off with hlt | hge
    · rw [List.getElem?_append_left (by rw [hAB]; omega),
        List.getElem?_append_left (by rw [hTake]; omega), List.getElem?_take_of_lt hlt]
    · have hge' : off + len ≤ i := by omega
      rw [List.getElem?_append_right (by rw [hAB]; omega), hAB, List.getElem?_drop,
        show off + len + (i - (off + len)) = i by omega]

/-- **The `PartialShell` projected `Deinit` is MiniRust's byte-slice `Uninit` store
(`evalDeinitPlace_spec_minirust_store_simulation`)**: let an ADT local laid out by `spec` be
initialized in Anneal (`rootVal`) and represented by the byte image `img` (`SlotBytes`), and let
MiniRust's live allocation `a` for it hold `toAbstractBytes img`. For a projected place whose byte
range is `[off, off + len)` (`pathRange`, `len > 0`), Anneal's `evalDeinitPlace` and MiniRust's
`ConcurrentMemory::store` of `len` `Uninit` bytes at `a.addr + off` correspond exactly: the store
succeeds, the new allocation holds `toAbstractBytes (deinitBytes img off len)`, and that image
represents Anneal's post-`Deinit` slot, with every byte outside the slice unchanged. -/
theorem evalDeinitPlace_spec_minirust_store_simulation {ts : Bool}
    {slots slots' : List Anneal.Mir.PlaceAndRvalue.LocalSlotState} {place : Place}
    {rootVal : Value} {spec : Anneal.Mir.AdtAndControl.AdtLayoutSpec}
    (hWF : spec.WF) {v : Nat} {fs : List Anneal.Mir.AdtAndControl.FieldLayout}
    {children : List Anneal.Mir.AdtAndControl.ByteLayout} {size align : Nat}
    (hLay : Anneal.Mir.AdtAndControl.adtLayout? spec = some (size, align))
    (hVF : Anneal.Mir.AdtAndControl.variantFields spec v = some fs)
    (hPl : Anneal.Mir.AdtAndControl.SpecFieldsPlaced spec v fs)
    (hCh : Anneal.Mir.AdtAndControl.ChildrenFit fs children)
    (enc : Value → List UInt8) (img : Anneal.Mir.AdtAndControl.ByteImage)
    (hRoot : slots[place.local_]? = some (.init rootVal))
    (h : Anneal.Mir.AdtAndControl.evalDeinitPlace ts slots place = some slots')
    (hTag : ts = true ∨ Anneal.Mir.AdtAndControl.noDowncast place.projection = true)
    (hFits : size ≤ img.length)
    (hS : Anneal.Mir.AdtAndControl.SlotBytes enc img
      (.struct size (Anneal.Mir.AdtAndControl.specOffsets spec v children.length) children) 0
      (.init rootVal))
    {off len : Nat}
    (hRange : Anneal.Mir.AdtAndControl.pathRange
      (.struct size (Anneal.Mir.AdtAndControl.specOffsets spec v children.length) children) 0
      place.projection = some (off, len))
    (hLen : 0 < len)
    {cm : Gen.ConcurrentMemory BM} {p : Ptr} {id : Nat}
    (hp : p.provenance = some (⟨(id : Int)⟩, ())) {a : Gen.Allocation}
    (hA : cm.memory.allocations[id]? = some a) (hlive : a.live = true)
    (hData : a.data = toAbstractBytes img) (haddr : p.addr = a.addr + (off : Int))
    (al : Align) (hal : Align.is_aligned al p.addr = true) :
    (∃ st', slots'[place.local_]? = some st' ∧
      Anneal.Mir.AdtAndControl.SlotBytes enc (Anneal.Mir.AdtAndControl.deinitBytes img off len)
        (.struct size (Anneal.Mir.AdtAndControl.specOffsets spec v children.length) children) 0
        (Anneal.Mir.AdtAndControl.slotStateToFieldSlot st')) ∧
    CM.store cm p (List.replicate len .Uninit) al .None =
      .ok { memory := { cm.memory with
              allocations := cm.memory.allocations.set id
                { a with data := toAbstractBytes (Anneal.Mir.AdtAndControl.deinitBytes img off len) } },
            accesses := cm.accesses ++ [⟨.Store, .None, p.addr, ⟨len⟩⟩] } ∧
    ∀ i, ¬ (off ≤ i ∧ i < off + len) →
      (toAbstractBytes (Anneal.Mir.AdtAndControl.deinitBytes img off len))[i]? =
        (toAbstractBytes img)[i]? := by
  obtain ⟨hBound, st', hSt', hBytes, hOut⟩ :=
    Anneal.Mir.AdtAndControl.evalDeinitPlace_spec_bytes_simulation hWF hLay hVF hPl hCh enc img
      hRoot h hTag hFits hS hRange
  have hOI : off + len ≤ img.length := by omega
  have hne : (List.replicate len (Gen.AbstractByte.Uninit : Byte)) ≠ [] :=
    List.ne_nil_of_length_pos (by simpa using hLen)
  have hbound : off + (List.replicate len (Gen.AbstractByte.Uninit : Byte)).length ≤ a.data.length := by
    simp [hData, length_toAbstractBytes]; omega
  have hStore := CM_store_subslice_align hp hA hlive off haddr _ hne hbound al hal
  refine ⟨⟨st', hSt', hBytes⟩, ?_, fun i hi => ?_⟩
  · rw [hStore, List.length_replicate, hData, ← toAbstractBytes_deinitBytes img off len hOI]
  · simp only [toAbstractBytes, List.getElem?_map, hOut i hi]

/-- **Anneal `PartialShell` trace on `Padded(u8, u32, u16)` (`paddedDeinitSiblingReinit_anneal_shell_agreement`)**:
on `[.uninit, .init (.aggregate 0 [.scalar ⟨7, 1⟩, .scalar ⟨99, 4⟩, .scalar ⟨1541, 2⟩])]`:
1. `evalDeinitPlace` on `_1.1` explodes `_1` into the `PartialShell`
   `[.init (.scalar ⟨7, 1⟩), .uninit, .init (.scalar ⟨1541, 2⟩)]`;
2. `readPlaceState` on `_1.1` returns `.ub` while `readPlaceState` on sibling `_1.0` returns
   `.ok (.scalar ⟨7, 1⟩)`;
3. `writePlaceState` of `.scalar ⟨42, 4⟩` to `_1.1` collapses the `PartialShell` back into
   `.init (.aggregate 0 [.scalar ⟨7, 1⟩, .scalar ⟨42, 4⟩, .scalar ⟨1541, 2⟩])`, and reading `_1.1`
   then returns `.ok (.scalar ⟨42, 4⟩)`. -/
theorem paddedDeinitSiblingReinit_anneal_shell_agreement :
    let u8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }
    let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let initSlots : List Anneal.Mir.PlaceAndRvalue.LocalSlotState :=
      [.uninit, .init (.aggregate 0 [.scalar ⟨7, 1⟩, .scalar ⟨99, 4⟩, .scalar ⟨1541, 2⟩])]
    let shellSlots : List Anneal.Mir.PlaceAndRvalue.LocalSlotState :=
      [.uninit, .partialShell ⟨0, true, true,
        [.init (.scalar ⟨7, 1⟩), .uninit, .init (.scalar ⟨1541, 2⟩)]⟩]
    let finalSlots : List Anneal.Mir.PlaceAndRvalue.LocalSlotState :=
      [.uninit, .init (.aggregate 0 [.scalar ⟨7, 1⟩, .scalar ⟨42, 4⟩, .scalar ⟨1541, 2⟩])]
    Anneal.Mir.AdtAndControl.evalDeinitPlace false initSlots ⟨1, [.field 1 u32Ty]⟩ =
      some shellSlots ∧
    Anneal.Mir.PlaceAndRvalue.readPlaceState shellSlots ⟨1, [.field 1 u32Ty]⟩ = .ub ∧
    Anneal.Mir.PlaceAndRvalue.readPlaceState shellSlots ⟨1, [.field 0 u8Ty]⟩ =
      .ok (.scalar ⟨7, 1⟩) ∧
    Anneal.Mir.PlaceAndRvalue.writePlaceState (fun _ _ _ => none) shellSlots
      ⟨1, [.field 1 u32Ty]⟩ u32Ty (.scalar ⟨42, 4⟩) = .ok finalSlots ∧
    Anneal.Mir.PlaceAndRvalue.readPlaceState finalSlots ⟨1, [.field 1 u32Ty]⟩ =
      .ok (.scalar ⟨42, 4⟩) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> with_unfolding_all rfl

/-- **Axiom-audit hook for Episode 2's sub-place model (`subplace_audit_closure`)**:
`MiniRustSpec.Audit`'s `#assert_all_minirustspec_standard_axioms` checks every declaration of the
imported `MiniRustSpec.*` modules (this one included, see `IntrinsicBoundary`'s import), but not the
`Anneal.*` theorems of `Anneal.Mir.AdtAndControl` Section 4 (synthetic sub-place pointers, `Deref`
places, sub-place `CopyNonOverlapping`, `move` through `Deref`, two-level `Deref` chains, their
Stage-1 Trusted refinement and non-vacuity witnesses) and of its Stage-1 `Retag` reconciliation
(Section 2). This theorem's proof term mentions each of them, so its axioms are the union of theirs,
and `MiniRustSpec.Audit`'s `[DEINIT-AUDIT]` group fails unless every one uses only the standard
axioms (in particular no `sorryAx` and no `Lean.ofReduceBool`). -/
theorem subplace_audit_closure : True :=
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_eq_some
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_fits
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_disjoint
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_small
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_page_dvd
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_align_dvd
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_aligned
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_example_two_page_local
  let _ := @Anneal.Mir.AdtAndControl.localBaseAddr_example_overflow_none
  let _ := @Anneal.Mir.AdtAndControl.subplaceAt_sub
  let _ := @Anneal.Mir.AdtAndControl.subplaceAt_append
  let _ := @Anneal.Mir.AdtAndControl.subplaceAt_disjoint_siblings
  let _ := @Anneal.Mir.AdtAndControl.subplaceAt_of_pathRange
  let _ := @Anneal.Mir.AdtAndControl.evalSubplaceRef_dead
  let _ := @Anneal.Mir.AdtAndControl.evalSubplaceRef_eq_ok
  let _ := @Anneal.Mir.AdtAndControl.evalSubplaceRef_inbounds
  let _ := @Anneal.Mir.AdtAndControl.evalSubplaceRef_disjoint_locals
  let _ := @Anneal.Mir.AdtAndControl.evalSubplaceRef_disjoint_siblings
  let _ := @Anneal.Mir.AdtAndControl.selectSubplaceCandidate_no_guess
  let _ := @Anneal.Mir.AdtAndControl.selectSubplaceCandidate_consistent
  let _ := @Anneal.Mir.AdtAndControl.selectSubplaceCandidate_ambiguous_none
  let _ := @Anneal.Mir.AdtAndControl.selectSubplaceCandidate_singleton
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_of_prechecks
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_null
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_misaligned
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_rangeOverflow
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_dead
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_no_provenance
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_sound
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_evalSubplaceRef
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_stable
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticSubplace_noDeref
  let _ := @Anneal.Mir.AdtAndControl.resolvePlace_noDeref
  let _ := @Anneal.Mir.AdtAndControl.resolvePlace_dead
  let _ := @Anneal.Mir.AdtAndControl.resolvePlace_deref
  let _ := @Anneal.Mir.AdtAndControl.evalDerefOperand_move_deref
  let _ := @Anneal.Mir.AdtAndControl.evalDerefOperand_move_deref_slots
  let _ := @Anneal.Mir.AdtAndControl.evalDerefOperand_move_bare
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_noDeref
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_deref
  let _ := @Anneal.Mir.AdtAndControl.writePlaceState_frame
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceWrite_frame
  let _ := @Anneal.Mir.AdtAndControl.writePlaceState_get_put_init
  let _ := @Anneal.Mir.AdtAndControl.writePlaceState_put_get_init
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceWrite_put_get
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceWrite_get_put
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceWrite_read_sibling
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceDeinit_target
  let _ := @Anneal.Mir.AdtAndControl.retag_subplace_ref_dead_local
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticLocal_misses_subplace
  let _ := @Anneal.Mir.AdtAndControl.evalRetagDerefPlace_eq
  let _ := @Anneal.Mir.AdtAndControl.evalRetagDerefPlace_noDeref
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_refines_evalOperand
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_refines_evalRvalue
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceWrite_refines_writePlaceValue
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_assign_deref_refines
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_zero_count
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_overlap_none
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_zst_bulk_noop
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_dead_none
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_read_after_copy
  let _ := @Anneal.Mir.AdtAndControl.writeSubplaceSlot_frame
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_frame
  let _ := @Anneal.Mir.AdtAndControl.writeSubplaceSlot_uninit_unit_array
  let _ := @Anneal.Mir.AdtAndControl.writeSubplaceSlot_uninit_elem_init_array_none
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_refines
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_copyNonOverlapping_singleDirect
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_copyNonOverlapping_subplace_refines
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_raw_null_zero
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_raw_dangling
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_ref_null
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_ref_misaligned
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_ref_dead
  let _ := @Anneal.Mir.AdtAndControl.witness_borrow
  let _ := @Anneal.Mir.AdtAndControl.witness_deref_read
  let _ := @Anneal.Mir.AdtAndControl.witness_deref_write_put_get
  let _ := @Anneal.Mir.AdtAndControl.witness_bases
  let _ := @Anneal.Mir.AdtAndControl.witnessCtx_wf
  let _ := @Anneal.Mir.AdtAndControl.witness_resolve
  let _ := @Anneal.Mir.AdtAndControl.witnessCtxT_wf
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_deref_read
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_deref_read_typed
  let _ := @Anneal.Mir.AdtAndControl.witness_tag_disambiguates_and_rejects_mismatch
  let _ := @Anneal.Mir.AdtAndControl.witness_window_copy
  let _ := @Anneal.Mir.AdtAndControl.decodeSubplaceTag_encodeSubplaceTag_same
  let _ := @Anneal.Mir.AdtAndControl.decodeSubplaceTag_tag_one_none
  let _ := @Anneal.Mir.AdtAndControl.decodeSubplaceTag_mismatch_none
  let _ := @Anneal.Mir.AdtAndControl.evalRvalue_use_copy_of_evalOperand
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_refines_evalOperand_typed
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_refines_evalRvalue_typed
  let _ := @Anneal.Mir.AdtAndControl.tyScalarBytes_pos
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_resolve
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_raw_inbounds_fallback_unique_tag
  let _ := @Anneal.Mir.AdtAndControl.reborrowFallbackTag_unique
  let _ := @Anneal.Mir.AdtAndControl.reborrowFallbackTag_decoded
  let _ := @Anneal.Mir.AdtAndControl.reborrowFallbackTag_stale
  let _ := @Anneal.Mir.AdtAndControl.readSubplaceSlot_uninit_tail
  let _ := @Anneal.Mir.AdtAndControl.writeSubplaceSlot_init_unit_array
  let _ := @Anneal.Mir.AdtAndControl.writeSubplaceSlot_uninit_subslice_init_array_none
  let _ := @Anneal.Mir.AdtAndControl.writeSubplaceSlot_nested_field_ok
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_window_read_after_copy
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_resolved_ok
  let _ := @Anneal.Mir.AdtAndControl.evalReborrowTail_raw_inbounds_fallback_ok
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_spec_bytes_simulation
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceWrite_refines_writePlaceValue_typed
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_assign_deref_refines_typed
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_window_refines
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_copyNonOverlapping_window_refines
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_deref_write_typed
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_window_copy
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_window_same_or_disjoint_refines
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_copyNonOverlapping_window_same_or_disjoint_refines
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_refines_evalOperand_typed_proj
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_refines_evalRvalue_typed_proj
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceWrite_refines_writePlaceValue_typed_proj
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_assign_deref_refines_typed_proj
  let _ := @Anneal.Mir.AdtAndControl.witnessPairCtxT_wf
  let _ := @Anneal.Mir.AdtAndControl.witnessPairCtxT_resolve
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_deref_proj_typed
  let _ := @Anneal.Mir.AdtAndControl.witnessArrCtx_resolve_0_0
  let _ := @Anneal.Mir.AdtAndControl.witnessArrCtx_resolve_0_1
  let _ := @Anneal.Mir.AdtAndControl.witnessArrCtx_resolve_0_2
  let _ := @Anneal.Mir.AdtAndControl.witnessArrCtx_resolve_1_0
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_window_copy_resolved_and_same_local
  let _ := @Anneal.Mir.AdtAndControl.evalOperand_move_deref_eq_copy
  let _ := @Anneal.Mir.AdtAndControl.evalRvalue_use_move_deref_eq_copy
  let _ := @Anneal.Mir.AdtAndControl.evalDerefOperand_move_refines_evalOperand
  let _ := @Anneal.Mir.AdtAndControl.evalDerefOperand_move_refines_evalOperand_typed
  let _ := @Anneal.Mir.AdtAndControl.evalDerefOperand_move_refines_evalOperand_typed_proj
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_refines_evalRvalue_move
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_refines_evalRvalue_typed_move
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_refines_evalRvalue_typed_proj_move
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_deref_move_proj_typed
  let _ := @Anneal.Mir.AdtAndControl.readPlaceState_set_init_root
  let _ := @Anneal.Mir.AdtAndControl.resolvePlace_deref_deref_split
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_deref_deref
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceWrite_deref_deref
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceWrite_deref_deref_split
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceDeinit_deref_deref_split
  let _ := @Anneal.Mir.AdtAndControl.witnessChainCtx_resolve_P1
  let _ := @Anneal.Mir.AdtAndControl.witnessChainCtx_resolve_P0_ow
  let _ := @Anneal.Mir.AdtAndControl.witnessChainCtx_resolve_P0
  let _ := @Anneal.Mir.AdtAndControl.witness_deref_deref_split
  let _ := @Anneal.Mir.AdtAndControl.witness_deref_deref_write_and_deinit_split
  let _ := @resolveFieldPath_deinit_unit
  let _ := @evalStatement_deinit_fieldPath
  let _ := @spliceAt_eq_self
  let _ := @evalStmt_deinit_field
  let _ := @evalStmt_retag_field
  let _ := @paddedDeinitSiblingReinit_anneal_shell_agreement
  let _ := @Anneal.Mir.AdtAndControl.retagKeepsFrameTy_nil
  let _ := @Anneal.Mir.AdtAndControl.evalNonFnEntryRetag_of_not_ref
  let _ := @Anneal.Mir.AdtAndControl.evalFnEntryRetag_of_not_ref
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_ref_refines
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_disabled_ub
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_fat_frozen_mut_ub
  let _ := @Anneal.Mir.AdtAndControl.ValueEqUpToTag.refl
  let _ := @Anneal.Mir.AdtAndControl.SlotBelow.toUpToTag
  let _ := @Anneal.Mir.AdtAndControl.SlotsRefine.toUpToTag
  let _ := @Anneal.Mir.AdtAndControl.SlotsRefine_reborrow_upToTag
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_ref_typed_reborrow
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_ref_fnEntry_reborrow
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_ref_frozen_mut_reborrows
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_raw_refines
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_raw_rawPtr_steps
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_raw_rawPtr_refines
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_raw_global_refines
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_raw_untracked_divergence
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_raw_scalar_addr_reject
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_raw_scalar_rawPtr_conservative
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_noRef_scalar_divergence
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_noRef_scalar_agree
  let _ := @Anneal.Mir.AdtAndControl.evalRvalue_copyForDeref_of_evalOperand
  let _ := @Anneal.Mir.AdtAndControl.evalDerefPlaceRead_refines_copyForDeref
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_tree_preconditions
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_deref_read_typed_tree
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_assign_deref_tree
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_retag_u32_field
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_retag_ref_reborrow
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_retag_ref_fnEntry_and_upToTag
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_retag_ref_zst_skips_read_ub
  trivial

end MiniRustSpec.Correspondence.DeinitBridge
