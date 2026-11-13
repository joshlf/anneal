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
`subplace_audit_closure`, `call_intrinsic_audit_closure` (which bridges
`Anneal.Mir.AdtAndControl.LIntrinsicOp` / `evalLIntrinsicValue` / `LTerminator.call` to
`MiniRustSpec.Interp` and transitively audits every Episode 2 Section 5 theorem of
`Anneal.Mir.AdtAndControl`), and `adt_control_residual_audit_closure` (verified by
`#assert_adt_control_audit_coverage` / `[ADT-AUDIT-COVERAGE]` and `[ANNEAL-AXIOMS]`).
-/

namespace MiniRustSpec.Correspondence.DeinitBridge

open Trusted.Rustc.V2026_06_01
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
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_uninit_or_dead_ub
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
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_ref_typed_refines_upToTag
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_retag_ref_fnEntry_refines_upToTag
  let _ := @Anneal.Mir.AdtAndControl.witness_trusted_retag_ref_anneal
  trivial

/-! ## Lowered inline intrinsics (`LIntrinsicOp`) and `MiniRustSpec.Interp` correspondence

`Anneal.Mir.AdtAndControl.LIntrinsicOp` and `evalLIntrinsicValue` formalize `crates/anneal-mir`'s
syntax-version-independent inline intrinsic evaluator (`crates/anneal-mir/src/ir.rs` and
`crates/anneal-mir/src/lower/intrinsic.rs`), decoupled from `V2026_06_01` `DefPath` strings by
`lowerIntrinsicKind_V2026_06_01` / `lowerCallTarget_V2026_06_01`. Because this module is the sole
`MiniRustSpec` module importing `Anneal.Mir.AdtAndControl`, the theorems below connect
`LIntrinsicOp` directly to `MiniRustSpec.Interp` (`evalBinOp`, `evalPtrOffset`, `evalValue`, and
`Interp.evalTerminator .Unreachable`) and pin every Episode 2 `AdtAndControl` theorem in
`call_intrinsic_audit_closure`. -/

@[reducible] private def isSignedBool (s : LibSpecr.Signedness) : Bool :=
  match s with
  | .Unsigned => false
  | .Signed => true

/-- Every integer `RigidTy` accepted by `intTyBytes` has `GoodSize` byte width, resolves its
signedness in `intrinsicIntSignedness?`, and resolves its byte size in
`intrinsicRigidTyByteSize`. -/
theorem intTyBytes_intrinsic_props {rk : RigidTy} {s : LibSpecr.Signedness} {n : Nat}
    (h : intTyBytes rk = some (s, n)) (allowChar : Bool)
    (decls : List LocalDecl) (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable) :
    GoodSize n ∧
      intrinsicIntSignedness? allowChar rk = some (isSignedBool s) ∧
      intrinsicRigidTyByteSize decls layouts rk = some n := by
  cases rk with
  | uint u => cases u <;> cases h <;> exact ⟨by simp [GoodSize], rfl, rfl⟩
  | int i => cases i <;> cases h <;> exact ⟨by simp [GoodSize], rfl, rfl⟩
  | _ => simp [intTyBytes] at h

private theorem signedHalfModulus_eq_two_pow (sz : Nat) (hsz : sz ≠ 0) :
    signedHalfModulus sz = 2 ^ (8 * sz - 1) := by
  unfold signedHalfModulus
  obtain ⟨hM, _⟩ := two_pow_byte_split sz hsz
  rw [scalarModulus_eq, nat_div_eq_div, hM]
  omega

private theorem int_tmod_lt_bound (a b : Int) (M : Nat)
    (hb0 : b ≠ 0) (hbLo : -(M : Int) < b) (hbHi : b < (M : Int)) :
    -(M : Int) < Int.tmod a b ∧ Int.tmod a b < (M : Int) := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      simp only [Int.tmod, Int.ofNat_eq_natCast] at *
      have hn : 0 < n := by omega
      have hlt := Nat.mod_lt m hn
      omega
    | negSucc n =>
      simp only [Int.tmod, Int.ofNat_eq_natCast] at *
      have hlt := Nat.mod_lt m (Nat.succ_pos n)
      omega
  | negSucc m =>
    cases b with
    | ofNat n =>
      simp only [Int.tmod, Int.ofNat_eq_natCast] at *
      have hn : 0 < n := by omega
      have hlt := Nat.mod_lt (m + 1) hn
      generalize (m + 1) % n = r at hlt ⊢
      cases r with
      | zero => change -(M : Int) < 0 ∧ 0 < (M : Int); omega
      | succ k => change -(M : Int) < Int.negSucc k ∧ Int.negSucc k < (M : Int); omega
    | negSucc n =>
      simp only [Int.tmod, Int.ofNat_eq_natCast] at *
      have hlt := Nat.mod_lt (m + 1) (Nat.succ_pos n)
      generalize (m + 1) % (n + 1) = r at hlt ⊢
      cases r with
      | zero => change -(M : Int) < 0 ∧ 0 < (M : Int); omega
      | succ k => change -(M : Int) < Int.negSucc k ∧ Int.negSucc k < (M : Int); omega

/-- Mapping from wrapping `LIntrinsicOp` variants to `(MirAst.BinOp, Gen.IntBinOp)`. -/
def wrappingLIntrinsicPair :
    Anneal.Mir.AdtAndControl.LIntrinsicOp → Option (MirAst.BinOp × Gen.IntBinOp)
  | .wrappingAdd => some (.add, .Add)
  | .wrappingSub => some (.sub, .Sub)
  | .wrappingMul => some (.mul, .Mul)
  | _ => none

/-- **Symbolic correspondence for `wrappingAdd`, `wrappingSub`, and `wrappingMul`
(`evalLIntrinsic_wrapping_eq_minirust`)**: across every integer type `it` (`GoodSize it.size.bytes`)
and all valid operand bit patterns `x, y < 2 ^ (8 * it.size.bytes)`, `evalLIntrinsicValue` produces
the exact two's-complement bit pattern whose `intFromBits` decoding equals MiniRust's
`evalBinOp (.Int .Add / .Sub / .Mul)`. -/
theorem evalLIntrinsic_wrapping_eq_minirust
    (op : Anneal.Mir.AdtAndControl.LIntrinsicOp) (bop : MirAst.BinOp) (iop : Gen.IntBinOp)
    (hop : wrappingLIntrinsicPair op = some (bop, iop))
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (tys : List RigidTy) (decls : List LocalDecl)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    let l := intFromBits x it
    let r := intFromBits y it
    ∃ z,
      evalBinOp (.Int iop) (.Int l, .Int it) (.Int r, .Int it) =
        .ok (.Int (IntType.bring_in_bounds it z), .Int it) ∧
      IntType.bring_in_bounds it z = intFromBits (z % 2 ^ (8 * it.size.bytes)).toNat it ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue op tys decls layouts argOps
          [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag =
        some (.scalar ⟨(z % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩) := by
  dsimp only
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hbeq : Nat.beq it.size.bytes 0 = false := by
    rw [nat_beq_eq_decide, decide_eq_false hsz]
  have hxWrap : wrapScalarBits x (scalarModulus it.size.bytes) = x := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hx]
  have hyWrap : wrapScalarBits y (scalarModulus it.size.bytes) = y := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hy]
  cases op <;> simp [wrappingLIntrinsicPair] at hop
  · obtain ⟨rfl, rfl⟩ := hop
    refine ⟨intFromBits x it + intFromBits y it, rfl,
      bringInBounds_eq_intFromBits it hgood _, ?_⟩
    simp [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalWrappingAdd, hbeq, Nat.beq_refl,
      hxWrap, hyWrap, Nat.add_eq, wrap_add_intFromBits it x y hx hy]
  · obtain ⟨rfl, rfl⟩ := hop
    refine ⟨intFromBits x it - intFromBits y it, rfl,
      bringInBounds_eq_intFromBits it hgood _, ?_⟩
    have hsub := wrap_sub_intFromBits it x y hx hy
    dsimp only at hsub
    rw [hxWrap, hyWrap] at hsub
    simp only [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalWrappingSub, hbeq, Nat.beq_refl,
      Bool.not_true, Bool.or_false, hxWrap, hyWrap, Nat.sub_eq, Nat.add_eq, Option.map]
    cases hble : Nat.ble y x <;> simp only [hble] at hsub ⊢ <;> rw [hsub]
  · obtain ⟨rfl, rfl⟩ := hop
    refine ⟨intFromBits x it * intFromBits y it, rfl,
      bringInBounds_eq_intFromBits it hgood _, ?_⟩
    simp [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalWrappingMul, hbeq, Nat.beq_refl,
      hxWrap, hyWrap, Nat.mul_eq, wrap_mul_intFromBits it x y hx hy]

/-- Mapping from homogeneous unchecked arithmetic `LIntrinsicOp` variants to
`(MirAst.BinOp, Gen.IntBinOp)`. -/
def uncheckedArithLIntrinsicPair :
    Anneal.Mir.AdtAndControl.LIntrinsicOp → Option (MirAst.BinOp × Gen.IntBinOp)
  | .uncheckedAdd => some (.addUnchecked, .AddUnchecked)
  | .uncheckedSub => some (.subUnchecked, .SubUnchecked)
  | .uncheckedMul => some (.mulUnchecked, .MulUnchecked)
  | .uncheckedDiv => some (.div, .Div)
  | .uncheckedRem => some (.rem, .Rem)
  | _ => none

private theorem evalLIntrinsic_unchecked_to_scalarBinOp
    (op : Anneal.Mir.AdtAndControl.LIntrinsicOp) (bop : MirAst.BinOp) (iop : Gen.IntBinOp)
    (hop : uncheckedArithLIntrinsicPair op = some (bop, iop))
    {rk : RigidTy} {it : Gen.IntType} (hrk : intTyBytes rk = some (it.signed, it.size.bytes))
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (restTys : List RigidTy) (decls : List LocalDecl)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    (match Anneal.Mir.AdtAndControl.evalLIntrinsicValue op (rk :: restTys) decls layouts argOps
        [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag with
      | some v => RvalueEvalResult.ok v [] {}
      | none => .ub) =
      evalScalarBinOp bop ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ [] {}
        (isSignedBool it.signed) := by
  obtain ⟨hgood, hSign, _⟩ := intTyBytes_intrinsic_props hrk false decls layouts
  clear hrk
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hbeq : Nat.beq it.size.bytes 0 = false := by
    rw [nat_beq_eq_decide, decide_eq_false hsz]
  have hxWrap : wrapScalarBits x (scalarModulus it.size.bytes) = x := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hx]
  have hyWrap : wrapScalarBits y (scalarModulus it.size.bytes) = y := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hy]
  cases op <;> simp [uncheckedArithLIntrinsicPair] at hop
  · obtain ⟨rfl, rfl⟩ := hop
    simp only [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, resolveIntrinsicIsSigned, hSign,
      evalUncheckedAdd, evalScalarBinOp, hbeq, Nat.beq_refl, Bool.not_true, Bool.or_false,
      hxWrap, hyWrap]
    cases it.signed <;> dsimp only [isSignedBool]
    · cases Nat.ble (scalarModulus it.size.bytes) (Nat.add x y) <;> rfl
    · cases signedOverflowAdd x y it.size.bytes <;> rfl
  · obtain ⟨rfl, rfl⟩ := hop
    simp only [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, resolveIntrinsicIsSigned, hSign,
      evalUncheckedSub, evalScalarBinOp, hbeq, Nat.beq_refl, Bool.not_true, Bool.or_false,
      hxWrap, hyWrap]
    cases it.signed <;> dsimp only [isSignedBool]
    · cases Nat.ble y x
      · rfl
      · dsimp only
        cases Nat.ble (scalarModulus it.size.bytes) (Nat.sub x y) <;> rfl
    · cases signedOverflowSub x y it.size.bytes <;> rfl
  · obtain ⟨rfl, rfl⟩ := hop
    simp only [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, resolveIntrinsicIsSigned, hSign,
      evalUncheckedMul, evalScalarBinOp, hbeq, Nat.beq_refl, Bool.not_true, Bool.or_false,
      hxWrap, hyWrap]
    cases it.signed <;> dsimp only [isSignedBool]
    · cases Nat.ble (scalarModulus it.size.bytes) (Nat.mul x y) <;> rfl
    · cases signedOverflowMul x y it.size.bytes <;> rfl
  · obtain ⟨rfl, rfl⟩ := hop
    simp only [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, resolveIntrinsicIsSigned, hSign,
      evalUncheckedDiv, evalScalarBinOp, evalSignedDiv, hbeq, Nat.beq_refl, Bool.not_true,
      Bool.or_false, hxWrap, hyWrap]
    cases Nat.beq y 0
    · cases it.signed <;> dsimp only [isSignedBool]
      · rfl
      · cases Bool.and (Nat.beq x (scalarPow2 (Nat.sub (Nat.mul it.size.bytes 8) 1)))
            (Nat.beq y (Nat.sub (scalarModulus it.size.bytes) 1)) <;> rfl
    · rfl
  · obtain ⟨rfl, rfl⟩ := hop
    simp only [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, resolveIntrinsicIsSigned, hSign,
      evalUncheckedRem, evalScalarBinOp, evalSignedRem, hbeq, Nat.beq_refl, Bool.not_true,
      Bool.or_false, hxWrap, hyWrap]
    cases Nat.beq y 0
    · cases it.signed <;> dsimp only [isSignedBool]
      · rfl
      · cases Bool.and (Nat.beq x (scalarPow2 (Nat.sub (Nat.mul it.size.bytes 8) 1)))
            (Nat.beq y (Nat.sub (scalarModulus it.size.bytes) 1)) <;> rfl
    · rfl

/-- **Symbolic correspondence (both value-return and UB-fault) for `uncheckedAdd`, `uncheckedSub`,
`uncheckedMul`, `uncheckedDiv`, and `uncheckedRem` (`evalLIntrinsic_unchecked_binop_iff_minirust`)**:
across every integer `RigidTy` `rk` (`intTyBytes rk = some (it.signed, it.size.bytes)`) and all
valid bit patterns `x, y < 2 ^ (8 * it.size.bytes)`:
1. whenever MiniRust's `evalBinOp (.Int iop)` succeeds with `.ok (.Int res, .Int it)`,
   `evalLIntrinsicValue op` returns the corresponding two's-complement scalar; and
2. whenever MiniRust's `evalBinOp (.Int iop)` raises UB, `evalLIntrinsicValue op` returns `none`
   (which `evalLoweredTerminator` rejects and `evalTerminator` maps to `MirStepNode.fail .ub`). -/
theorem evalLIntrinsic_unchecked_binop_iff_minirust
    (op : Anneal.Mir.AdtAndControl.LIntrinsicOp) (bop : MirAst.BinOp) (iop : Gen.IntBinOp)
    (hop : uncheckedArithLIntrinsicPair op = some (bop, iop))
    {rk : RigidTy} {it : Gen.IntType} (hrk : intTyBytes rk = some (it.signed, it.size.bytes))
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (restTys : List RigidTy) (decls : List LocalDecl)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    let l := intFromBits x it
    let r := intFromBits y it
    (∀ res, evalBinOp (.Int iop) (.Int l, .Int it) (.Int r, .Int it) = .ok (.Int res, .Int it) →
      res = intFromBits (res % 2 ^ (8 * it.size.bytes)).toNat it ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue op (rk :: restTys) decls layouts argOps
          [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag =
        some (.scalar ⟨(res % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩)) ∧
    ((∃ msg, evalBinOp (.Int iop) (.Int l, .Int it) (.Int r, .Int it) = .error (.ub msg)) →
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue op (rk :: restTys) decls layouts argOps
          [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag = none) := by
  dsimp only
  obtain ⟨hgood, _, _⟩ := intTyBytes_intrinsic_props hrk false decls layouts
  have hTr : translateBinOp bop = some iop ∧ isShiftIntBinOp iop = false := by
    cases op <;> simp [uncheckedArithLIntrinsicPair] at hop <;>
      rcases hop with ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩
  have hFrag := evalScalarBinOp_frag bop iop hTr.1 it it hgood hgood (fun _ => rfl) x y hx hy [] {}
  have hSpec := evalIntBinOp_spec bop iop hTr.1 (intFromBits x it) (intFromBits y it) it
  have hBridge := evalLIntrinsic_unchecked_to_scalarBinOp op bop iop hop hrk x y hx hy
    restTys decls layouts argOps flag
  cases hIE : intBinEval iop (intFromBits x it) (intFromBits y it) it with
  | some z =>
    have hOkInt := hSpec.1 z hIE
    have hOkSc :
        evalScalarBinOp bop ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ [] {} (isSignedBool it.signed) =
          .ok (.scalar ⟨(z % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩) [] {} := hFrag.1 z hIE
    rw [hOkSc] at hBridge
    have hLVal : Anneal.Mir.AdtAndControl.evalLIntrinsicValue op (rk :: restTys) decls layouts
        argOps [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag =
        some (.scalar ⟨(z % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩) := by
      cases hE : Anneal.Mir.AdtAndControl.evalLIntrinsicValue op (rk :: restTys) decls layouts
          argOps [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag with
      | none => rw [hE] at hBridge; nomatch hBridge
      | some v => rw [hE] at hBridge; injection hBridge with hv; rw [hv]
    have hBringMod :
        IntType.bring_in_bounds it z % 2 ^ (8 * it.size.bytes) = z % 2 ^ (8 * it.size.bytes) := by
      rcases it with ⟨s, sz⟩
      unfold IntType.bring_in_bounds bringInBounds Interp.Size.bits
      dsimp only
      cases s
      · exact Int.emod_emod _ _
      · dsimp only
        split
        · exact Int.emod_emod _ _
        · rw [Int.sub_emod_right, Int.emod_emod]
    refine ⟨fun res hRes => ?_, fun ⟨msg, hErr⟩ => ?_⟩
    · simp [evalBinOp, hOkInt, Bind.bind, Except.bind, Pure.pure, Except.pure] at hRes
      subst hRes
      rw [hBringMod]
      exact ⟨bringInBounds_eq_intFromBits it hgood z, hLVal⟩
    · simp [evalBinOp, hOkInt, Bind.bind, Except.bind, Pure.pure, Except.pure] at hErr
  | none =>
    obtain ⟨msg0, hUbInt⟩ := hSpec.2 hIE
    have hUbSc :
        evalScalarBinOp bop ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ [] {} (isSignedBool it.signed) =
          .ub := hFrag.2 hIE
    rw [hUbSc] at hBridge
    have hLNone : Anneal.Mir.AdtAndControl.evalLIntrinsicValue op (rk :: restTys) decls layouts
        argOps [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag = none := by
      cases hE : Anneal.Mir.AdtAndControl.evalLIntrinsicValue op (rk :: restTys) decls layouts
          argOps [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag with
      | none => rfl
      | some v => rw [hE] at hBridge; nomatch hBridge
    refine ⟨fun res hRes => ?_, fun _ => hLNone⟩
    simp [evalBinOp, hUbInt, Bind.bind, Except.bind] at hRes

/-- **Symbolic correspondence (both value-return and UB-fault, including negative signed shift
counts) for `uncheckedShl` and `uncheckedShr` (`evalLIntrinsic_unchecked_shift_iff_minirust`)**:
for any integer types `it` (`lhsRk`) and `rhsIt` (`rhsRk`) and valid bit patterns
`x < 2 ^ (8 * it.size.bytes)` and `y < 2 ^ (8 * rhsIt.size.bytes)`, `evalLIntrinsicValue` matches
MiniRust's `evalBinOp (.Int .ShlUnchecked / .ShrUnchecked)`. -/
theorem evalLIntrinsic_unchecked_shift_iff_minirust
    (isShr : Bool)
    {lhsRk rhsRk : RigidTy} {it rhsIt : Gen.IntType}
    (hLhs : intTyBytes lhsRk = some (it.signed, it.size.bytes))
    (hRhs : intTyBytes rhsRk = some (rhsIt.signed, rhsIt.size.bytes))
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * rhsIt.size.bytes))
    (restTys : List RigidTy) (decls : List LocalDecl)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    let op : Anneal.Mir.AdtAndControl.LIntrinsicOp := if isShr then .uncheckedShr else .uncheckedShl
    let iop : Gen.IntBinOp := if isShr then .ShrUnchecked else .ShlUnchecked
    let l := intFromBits x it
    let r := intFromBits y rhsIt
    (∀ res, evalBinOp (.Int iop) (.Int l, .Int it) (.Int r, .Int rhsIt) = .ok (.Int res, .Int it) →
      res = intFromBits (res % 2 ^ (8 * it.size.bytes)).toNat it ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue op (lhsRk :: rhsRk :: restTys) decls layouts
          argOps [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, rhsIt.size.bytes⟩] flag =
        some (.scalar ⟨(res % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩)) ∧
    ((∃ msg, evalBinOp (.Int iop) (.Int l, .Int it) (.Int r, .Int rhsIt) = .error (.ub msg)) →
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue op (lhsRk :: rhsRk :: restTys) decls layouts
          argOps [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, rhsIt.size.bytes⟩] flag = none) := by
  dsimp only
  obtain ⟨hgood, hLhsSign, _⟩ := intTyBytes_intrinsic_props hLhs false decls layouts
  obtain ⟨hrhsGood, hRhsSign, _⟩ := intTyBytes_intrinsic_props hRhs false decls layouts
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hrhsSz : rhsIt.size.bytes ≠ 0 := Nat.ne_of_gt hrhsGood.pos
  have hbeq : Nat.beq it.size.bytes 0 = false := by
    rw [nat_beq_eq_decide, decide_eq_false hsz]
  have hrhsBeq : Nat.beq rhsIt.size.bytes 0 = false := by
    rw [nat_beq_eq_decide, decide_eq_false hrhsSz]
  have hxWrap : wrapScalarBits x (scalarModulus it.size.bytes) = x := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hx]
  have hyWrap : wrapScalarBits y (scalarModulus rhsIt.size.bytes) = y := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hy]
  -- Whenever `isSignedNegative y rhsIt.size.bytes = true`, `y ≥ 2^(8*rhsSz - 1) ≥ 128 ≥ 8*lhsSz`,
  -- so `Nat.ble (it.size.bytes * 8) y` already subsumes `negShift`.
  have hNegSubsumed : ∀ (rs : Bool),
      Bool.or (Bool.and rs (isSignedNegative y rhsIt.size.bytes))
        (Nat.ble (Nat.mul it.size.bytes 8) y) =
      Nat.ble (Nat.mul it.size.bytes 8) y := by
    intro rs
    have hLhsMax : it.size.bytes ≤ 16 := by
      rcases hgood with h | h | h | h | h <;> omega
    have hHalfMin : 128 ≤ 2 ^ (8 * rhsIt.size.bytes - 1) := by
      rcases hrhsGood with h | h | h | h | h <;> rw [h] <;> decide
    rw [isSignedNegative_eq y rhsIt.size.bytes hrhsSz hy, Nat.mul_eq, nat_ble_eq_decide]
    by_cases hge : 2 ^ (8 * rhsIt.size.bytes - 1) ≤ y
    · rw [decide_eq_true hge, decide_eq_true (by omega : it.size.bytes * 8 ≤ y), Bool.or_true]
    · rw [decide_eq_false hge, Bool.and_false, Bool.false_or]
  let bop : MirAst.BinOp := if isShr then .shrUnchecked else .shlUnchecked
  let iop : Gen.IntBinOp := if isShr then .ShrUnchecked else .ShlUnchecked
  have hTr : translateBinOp bop = some iop := by cases isShr <;> rfl
  have hBridge :
      (match Anneal.Mir.AdtAndControl.evalLIntrinsicValue
          (if isShr then .uncheckedShr else .uncheckedShl)
          (lhsRk :: rhsRk :: restTys) decls layouts argOps
          [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, rhsIt.size.bytes⟩] flag with
        | some v => RvalueEvalResult.ok v [] {}
        | none => .ub) =
      evalScalarBinOp bop ⟨x, it.size.bytes⟩ ⟨y, rhsIt.size.bytes⟩ [] {}
        (isSignedBool it.signed) := by
    dsimp only [bop]
    cases isShr
    · simp only [Bool.false_eq_true, ↓reduceIte, Anneal.Mir.AdtAndControl.evalLIntrinsicValue,
        resolveIntrinsicShiftSigned, hRhsSign, evalUncheckedShl, evalScalarBinOp, hbeq, hrhsBeq,
        Bool.or_self, hxWrap, hyWrap, hNegSubsumed]
      cases Nat.ble (Nat.mul it.size.bytes 8) y <;> rfl
    · simp only [↓reduceIte, Anneal.Mir.AdtAndControl.evalLIntrinsicValue,
        resolveIntrinsicIsSigned, resolveIntrinsicShiftSigned, hLhsSign, hRhsSign,
        evalUncheckedShr, evalScalarBinOp, hbeq, hrhsBeq, Bool.or_self, hxWrap, hyWrap,
        hNegSubsumed]
      cases Nat.ble (Nat.mul it.size.bytes 8) y <;> rfl
  have hFrag := evalScalarBinOp_frag bop iop hTr it rhsIt hgood hrhsGood
    (by cases isShr <;> intro h <;> nomatch h) x y hx hy [] {}
  have hSpec := evalIntBinOp_spec bop iop hTr (intFromBits x it) (intFromBits y rhsIt) it
  cases hIE : intBinEval iop (intFromBits x it) (intFromBits y rhsIt) it with
  | some z =>
    have hOkInt := hSpec.1 z hIE
    have hOkSc :
        evalScalarBinOp bop ⟨x, it.size.bytes⟩ ⟨y, rhsIt.size.bytes⟩ [] {}
          (isSignedBool it.signed) =
          .ok (.scalar ⟨(z % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩) [] {} := hFrag.1 z hIE
    rw [hOkSc] at hBridge
    have hLVal : Anneal.Mir.AdtAndControl.evalLIntrinsicValue
        (if isShr then .uncheckedShr else .uncheckedShl)
        (lhsRk :: rhsRk :: restTys) decls layouts argOps
        [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, rhsIt.size.bytes⟩] flag =
        some (.scalar ⟨(z % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩) := by
      cases hE : Anneal.Mir.AdtAndControl.evalLIntrinsicValue
          (if isShr then .uncheckedShr else .uncheckedShl)
          (lhsRk :: rhsRk :: restTys) decls layouts argOps
          [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, rhsIt.size.bytes⟩] flag with
      | none => rw [hE] at hBridge; nomatch hBridge
      | some v => rw [hE] at hBridge; injection hBridge with hv; rw [hv]
    have hBringMod :
        IntType.bring_in_bounds it z % 2 ^ (8 * it.size.bytes) = z % 2 ^ (8 * it.size.bytes) := by
      rcases it with ⟨s, sz⟩
      unfold IntType.bring_in_bounds bringInBounds Interp.Size.bits
      dsimp only
      cases s
      · exact Int.emod_emod _ _
      · dsimp only
        split
        · exact Int.emod_emod _ _
        · rw [Int.sub_emod_right, Int.emod_emod]
    refine ⟨fun res hRes => ?_, fun ⟨msg, hErr⟩ => ?_⟩
    · simp [evalBinOp, hOkInt, Bind.bind, Except.bind, Pure.pure, Except.pure, iop] at hRes
      subst hRes
      rw [hBringMod]
      exact ⟨bringInBounds_eq_intFromBits it hgood z, hLVal⟩
    · simp [evalBinOp, hOkInt, Bind.bind, Except.bind, Pure.pure, Except.pure, iop] at hErr
  | none =>
    obtain ⟨msg0, hUbInt⟩ := hSpec.2 hIE
    have hUbSc :
        evalScalarBinOp bop ⟨x, it.size.bytes⟩ ⟨y, rhsIt.size.bytes⟩ [] {}
          (isSignedBool it.signed) = .ub := hFrag.2 hIE
    rw [hUbSc] at hBridge
    have hLNone : Anneal.Mir.AdtAndControl.evalLIntrinsicValue
        (if isShr then .uncheckedShr else .uncheckedShl)
        (lhsRk :: rhsRk :: restTys) decls layouts argOps
        [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, rhsIt.size.bytes⟩] flag = none := by
      cases hE : Anneal.Mir.AdtAndControl.evalLIntrinsicValue
          (if isShr then .uncheckedShr else .uncheckedShl)
          (lhsRk :: rhsRk :: restTys) decls layouts argOps
          [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, rhsIt.size.bytes⟩] flag with
      | none => rfl
      | some v => rw [hE] at hBridge; nomatch hBridge
    refine ⟨fun res hRes => ?_, fun _ => hLNone⟩
    simp [evalBinOp, hUbInt, Bind.bind, Except.bind, iop] at hRes

/-- **Symbolic correspondence (both exact quotient and all three UB conditions) for
`LIntrinsicOp.exactDiv` (`evalLIntrinsic_exactDiv_iff_minirust`)**: across every integer `RigidTy`
`rk` (`intTyBytes rk = some (it.signed, it.size.bytes)`) and all valid bit patterns
`x, y < 2 ^ (8 * it.size.bytes)`:
1. whenever MiniRust's `evalBinOp (.Int .DivExact)` returns `.ok (.Int q, .Int it)`,
   `evalLIntrinsicValue .exactDiv` returns the matching scalar `⟨(q % 2^(8*sz)).toNat, sz⟩`; and
2. whenever MiniRust's `evalBinOp (.Int .DivExact)` raises UB (division by zero, signed `MIN / -1`
   overflow, or non-zero remainder), `evalLIntrinsicValue .exactDiv` returns `none`. -/
theorem evalLIntrinsic_exactDiv_iff_minirust
    {rk : RigidTy} {it : Gen.IntType} (hrk : intTyBytes rk = some (it.signed, it.size.bytes))
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (restTys : List RigidTy) (decls : List LocalDecl)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    let l := intFromBits x it
    let r := intFromBits y it
    (∀ q, evalBinOp (.Int .DivExact) (.Int l, .Int it) (.Int r, .Int it) = .ok (.Int q, .Int it) →
      q = intFromBits (q % 2 ^ (8 * it.size.bytes)).toNat it ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .exactDiv (rk :: restTys) decls layouts argOps
          [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag =
        some (.scalar ⟨(q % 2 ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩)) ∧
    ((∃ msg, evalBinOp (.Int .DivExact) (.Int l, .Int it) (.Int r, .Int it) = .error (.ub msg)) →
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .exactDiv (rk :: restTys) decls layouts argOps
          [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag = none) := by
  dsimp only
  obtain ⟨hgood, hSign, _⟩ := intTyBytes_intrinsic_props hrk false decls layouts
  clear hrk
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hbeq : Nat.beq it.size.bytes 0 = false := by
    rw [nat_beq_eq_decide, decide_eq_false hsz]
  have hxWrap : wrapScalarBits x (scalarModulus it.size.bytes) = x := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hx]
  have hyWrap : wrapScalarBits y (scalarModulus it.size.bytes) = y := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hy]
  -- Relate `evalExactDiv` directly to `(evalScalarBinOp .div, evalScalarBinOp .rem)`:
  have hExEq :
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .exactDiv (rk :: restTys) decls layouts argOps
          [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag =
      match evalScalarBinOp .div ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ [] {} (isSignedBool it.signed),
            evalScalarBinOp .rem ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ [] {} (isSignedBool it.signed) with
      | .ok (.scalar qSc) _ _, .ok (.scalar rSc) _ _ =>
        if rSc.bits = 0 then some (.scalar qSc) else none
      | _, _ => none := by
    simp only [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, resolveIntrinsicIsSigned, hSign,
      evalExactDiv, evalScalarBinOp, hbeq, Nat.beq_refl, Bool.not_false, Bool.and_self,
      hxWrap, hyWrap]
    by_cases hy0 : y = 0
    · subst hy0; simp
    · have hyBeq : Nat.beq y 0 = false := by rw [nat_beq_eq_decide, decide_eq_false hy0]
      simp only [hyBeq]
      rcases it with ⟨s, ⟨sz⟩⟩
      dsimp only at hgood hsz hbeq hx hy hxWrap hyWrap ⊢
      cases s
      · dsimp only
        have hqlt : x / y < 2 ^ (8 * sz) := Nat.lt_of_le_of_lt (Nat.div_le_self x y) hx
        have hrlt : x % y < 2 ^ (8 * sz) := Nat.lt_trans (Nat.mod_lt x (by omega)) hy
        simp only [nat_div_eq_div, nat_mod_eq_mod, wrapScalarBits_eq, scalarModulus_eq,
          Nat.mod_eq_of_lt hqlt, Nat.mod_eq_of_lt hrlt, nat_beq_eq_decide]
        by_cases hrm : x % y = 0 <;> simp [hrm]
      · dsimp only
        obtain ⟨hM, hH⟩ := two_pow_byte_split sz hsz
        have hHalfEq : signedHalfModulus sz = scalarPow2 (Nat.sub (Nat.mul sz 8) 1) := by
          rw [signedHalfModulus_eq_two_pow sz hsz, scalarPow2_eq, Nat.mul_eq, Nat.sub_eq,
            Nat.mul_comm sz 8]
        simp only [evalSignedDiv, evalSignedRem, hHalfEq, hxWrap, hyWrap]
        cases hOvf : Bool.and (Nat.beq x (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
            (Nat.beq y (Nat.sub (scalarModulus sz) 1))
        · dsimp only
          have hNegX : Nat.ble (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)) x =
              isSignedNegative x sz := by
            simp [isSignedNegative_eq x sz hsz hx, scalarPow2_eq, Nat.mul_eq, Nat.sub_eq,
              Nat.mul_comm sz 8, nat_ble_eq_decide]
          have hNegY : Nat.ble (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)) y =
              isSignedNegative y sz := by
            simp [isSignedNegative_eq y sz hsz hy, scalarPow2_eq, Nat.mul_eq, Nat.sub_eq,
              Nat.mul_comm sz 8, nat_ble_eq_decide]
          rw [hNegX, hNegY]
          have hCore : ∀ (a b : Nat) (sx sy : Bool),
              a ≤ 2 ^ (8 * sz - 1) → 0 < b → b ≤ 2 ^ (8 * sz - 1) →
              Option.map Value.scalar
                (match Nat.beq (Nat.mod a b) 0 with
                | false => none
                | true =>
                  some {
                    bits := match sx, sy with
                      | false, false => Nat.div a b
                      | true, true => Nat.div a b
                      | _, _ => wrapScalarBits (Nat.sub (scalarModulus sz) (Nat.div a b)) (scalarModulus sz),
                    sizeBytes := sz }) =
              (if (match Nat.beq (Nat.mod a b) 0 with
                  | true => 0
                  | false =>
                    match sx with
                    | false => wrapScalarBits (Nat.mod a b) (scalarModulus sz)
                    | true => wrapScalarBits (Nat.sub (scalarModulus sz) (Nat.mod a b)) (scalarModulus sz)) = 0
                then some (Value.scalar {
                  bits := match Nat.beq (Nat.div a b) 0 with
                    | true => 0
                    | false =>
                      match sx, sy with
                      | false, false => wrapScalarBits (Nat.div a b) (scalarModulus sz)
                      | true, true => wrapScalarBits (Nat.div a b) (scalarModulus sz)
                      | _, _ => wrapScalarBits (Nat.sub (scalarModulus sz) (Nat.div a b)) (scalarModulus sz),
                  sizeBytes := sz })
                else none) := by
            intro a b sx sy ha hb0 hb
            simp only [nat_mod_eq_mod, nat_div_eq_div, Nat.sub_eq, wrapScalarBits_eq,
              scalarModulus_eq]
            cases hMod0 : Nat.beq (a % b) 0 with
            | false =>
              dsimp only
              rw [nat_beq_eq_decide, decide_eq_false_iff_not] at hMod0
              have hRLt : a % b < 2 ^ (8 * sz) := by
                have := Nat.mod_lt a hb0; omega
              have hSubLt : 2 ^ (8 * sz) - a % b < 2 ^ (8 * sz) := by omega
              have hSubNz : 2 ^ (8 * sz) - a % b ≠ 0 := by omega
              cases sx
              · simp [Nat.mod_eq_of_lt hRLt, hMod0]
              · simp [Nat.mod_eq_of_lt hSubLt, hSubNz]
            | true =>
              dsimp only
              simp only [↓reduceIte]
              have hQLt : a / b < 2 ^ (8 * sz) := by
                have := Nat.div_le_self a b; omega
              cases hQ0 : Nat.beq (a / b) 0 with
              | true =>
                rw [nat_beq_eq_decide, decide_eq_true_eq] at hQ0
                cases sx <;> cases sy <;> simp [hQ0]
              | false =>
                cases sx <;> cases sy <;> simp [Nat.mod_eq_of_lt hQLt]
          have hxSubWrap : isSignedNegative x sz = true →
              wrapScalarBits (Nat.sub (scalarModulus sz) x) (scalarModulus sz) =
                Nat.sub (scalarModulus sz) x := by
            intro hnx
            rw [isSignedNegative_eq x sz hsz hx, decide_eq_true_eq] at hnx
            have := Nat.two_pow_pos (8 * sz - 1)
            rw [wrapScalarBits_eq, scalarModulus_eq, Nat.sub_eq,
              Nat.mod_eq_of_lt (by omega : 2 ^ (8 * sz) - x < 2 ^ (8 * sz))]
          have hySubWrap : isSignedNegative y sz = true →
              wrapScalarBits (Nat.sub (scalarModulus sz) y) (scalarModulus sz) =
                Nat.sub (scalarModulus sz) y := by
            intro hny
            rw [isSignedNegative_eq y sz hsz hy, decide_eq_true_eq] at hny
            rw [wrapScalarBits_eq, scalarModulus_eq, Nat.sub_eq,
              Nat.mod_eq_of_lt (by omega : 2 ^ (8 * sz) - y < 2 ^ (8 * sz))]
          cases hnx : isSignedNegative x sz <;> cases hny : isSignedNegative y sz
          · dsimp only
            rw [isSignedNegative_eq x sz hsz hx, decide_eq_false_iff_not] at hnx
            rw [isSignedNegative_eq y sz hsz hy, decide_eq_false_iff_not] at hny
            exact hCore x y false false (by omega) (by omega) (by omega)
          · dsimp only
            rw [hySubWrap hny]
            rw [isSignedNegative_eq x sz hsz hx, decide_eq_false_iff_not] at hnx
            rw [isSignedNegative_eq y sz hsz hy, decide_eq_true_eq] at hny
            exact hCore x (Nat.sub (scalarModulus sz) y) false true (by omega)
              (by rw [scalarModulus_eq, Nat.sub_eq]; omega)
              (by rw [scalarModulus_eq, Nat.sub_eq]; omega)
          · dsimp only
            rw [hxSubWrap hnx]
            rw [isSignedNegative_eq x sz hsz hx, decide_eq_true_eq] at hnx
            rw [isSignedNegative_eq y sz hsz hy, decide_eq_false_iff_not] at hny
            exact hCore (Nat.sub (scalarModulus sz) x) y true false
              (by rw [scalarModulus_eq, Nat.sub_eq]; omega) (by omega) (by omega)
          · dsimp only
            rw [hxSubWrap hnx, hySubWrap hny]
            rw [isSignedNegative_eq x sz hsz hx, decide_eq_true_eq] at hnx
            rw [isSignedNegative_eq y sz hsz hy, decide_eq_true_eq] at hny
            exact hCore (Nat.sub (scalarModulus sz) x) (Nat.sub (scalarModulus sz) y) true true
              (by rw [scalarModulus_eq, Nat.sub_eq]; omega)
              (by rw [scalarModulus_eq, Nat.sub_eq]; omega)
              (by rw [scalarModulus_eq, Nat.sub_eq]; omega)
        · rfl
  rw [hExEq]
  have hDivFrag := evalScalarBinOp_frag .div .Div rfl it it hgood hgood (fun _ => rfl) x y hx hy [] {}
  have hRemFrag := evalScalarBinOp_frag .rem .Rem rfl it it hgood hgood (fun _ => rfl) x y hx hy [] {}
  by_cases hr0 : intFromBits y it = 0
  · have hDivNone : intBinEval .Div (intFromBits x it) (intFromBits y it) it = none := by
      simp [intBinEval, hr0]
    have hDivNoneSc :
        evalScalarBinOp .div ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ [] {} (isSignedBool it.signed) =
          .ub := hDivFrag.2 hDivNone
    rw [hDivNoneSc]
    simp [evalBinOp, evalIntBinOp, hr0, ub]
  · by_cases hrep : IntType.can_represent it (Int.tdiv (intFromBits x it) (intFromBits y it)) = true
    · have hDivSome : intBinEval .Div (intFromBits x it) (intFromBits y it) it =
          some (Int.tdiv (intFromBits x it) (intFromBits y it)) := by
        simp [intBinEval, hr0, hrep]
      have hRemSome : intBinEval .Rem (intFromBits x it) (intFromBits y it) it =
          some (Int.tmod (intFromBits x it) (intFromBits y it)) := by
        simp [intBinEval, hr0, hrep]
      have hDivSomeSc :
          evalScalarBinOp .div ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ [] {} (isSignedBool it.signed) =
            .ok (.scalar ⟨(Int.tdiv (intFromBits x it) (intFromBits y it) % 2 ^ (8 * it.size.bytes)).toNat,
              it.size.bytes⟩) [] {} := hDivFrag.1 _ hDivSome
      have hRemSomeSc :
          evalScalarBinOp .rem ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ [] {} (isSignedBool it.signed) =
            .ok (.scalar ⟨(Int.tmod (intFromBits x it) (intFromBits y it) % 2 ^ (8 * it.size.bytes)).toNat,
              it.size.bytes⟩) [] {} := hRemFrag.1 _ hRemSome
      rw [hDivSomeSc, hRemSomeSc]
      dsimp only
      by_cases hrem : Int.tmod (intFromBits x it) (intFromBits y it) = 0
      · have hBringMod :
            IntType.bring_in_bounds it (Int.tdiv (intFromBits x it) (intFromBits y it)) %
              2 ^ (8 * it.size.bytes) =
            Int.tdiv (intFromBits x it) (intFromBits y it) % 2 ^ (8 * it.size.bytes) := by
          rcases it with ⟨s, sz⟩
          unfold IntType.bring_in_bounds bringInBounds Interp.Size.bits
          dsimp only
          cases s
          · exact Int.emod_emod _ _
          · dsimp only
            split
            · exact Int.emod_emod _ _
            · rw [Int.sub_emod_right, Int.emod_emod]
        simp only [↓reduceIte, evalBinOp, evalIntBinOp, hr0, hrep, hrem, ne_eq,
          not_true_eq_false, Bool.not_true, Bool.false_eq_true, Int.zero_emod, Int.toNat_zero]
        refine ⟨fun q hq => ?_, fun ⟨msg, hErr⟩ => ?_⟩
        · simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at hq
          subst hq
          rw [hBringMod]
          exact ⟨bringInBounds_eq_intFromBits it hgood _, rfl⟩
        · simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at hErr
      · -- Show `(tmod % 2^(8*sz)).toNat ≠ 0` when `tmod ≠ 0`:
        have hRemBitsNz :
            ((Int.tmod (intFromBits x it) (intFromBits y it) %
              2 ^ (8 * it.size.bytes)).toNat ≠ 0) := by
          have hyBound :
              -((2 ^ (8 * it.size.bytes) : Nat) : Int) < intFromBits y it ∧
                intFromBits y it < ((2 ^ (8 * it.size.bytes) : Nat) : Int) := by
            rcases it with ⟨s, ⟨sz⟩⟩
            dsimp only at hgood hsz hy hyWrap ⊢
            cases s with
            | Unsigned =>
              simp only [intFromBits]
              omega
            | Signed =>
              obtain ⟨hM, _⟩ := two_pow_byte_split sz hsz
              have hcr := canRepresent_intFromBits ⟨.Signed, ⟨sz⟩⟩ y hgood hy
              rw [canRepresent_signed sz hsz, decide_eq_true_eq] at hcr
              omega
          have hRmBound := int_tmod_lt_bound (intFromBits x it) (intFromBits y it)
            (2 ^ (8 * it.size.bytes)) hr0 hyBound.1 hyBound.2
          have hpM : (2 : Int) ^ (8 * it.size.bytes) =
              ((2 ^ (8 * it.size.bytes) : Nat) : Int) := by push_cast; rfl
          rw [hpM]
          generalize Int.tmod (intFromBits x it) (intFromBits y it) = rm at hrem hRmBound ⊢
          generalize (2 ^ (8 * it.size.bytes) : Nat) = M at hRmBound ⊢
          by_cases hrm0 : 0 ≤ rm
          · rw [Int.emod_eq_of_lt hrm0 hRmBound.2]
            omega
          · have h1 : (rm + 1 * (M : Int)) % (M : Int) = rm + 1 * (M : Int) :=
              Int.emod_eq_of_lt (by omega) (by omega)
            rw [Int.add_mul_emod_self_right] at h1
            rw [h1]
            omega
        simp [hRemBitsNz, evalBinOp, evalIntBinOp, hr0, hrep, hrem, ub, Bind.bind, Except.bind]
    · simp only [Bool.not_eq_true] at hrep
      have hDivNone : intBinEval .Div (intFromBits x it) (intFromBits y it) it = none := by
        simp [intBinEval, hr0, hrep]
      have hDivNoneSc :
          evalScalarBinOp .div ⟨x, it.size.bytes⟩ ⟨y, it.size.bytes⟩ [] {} (isSignedBool it.signed) =
            .ub := hDivFrag.2 hDivNone
      rw [hDivNoneSc]
      simp [evalBinOp, evalIntBinOp, hr0, hrep, ub, Bind.bind, Except.bind]

/-- **Symbolic correspondence for `LIntrinsicOp.saturatingAdd` and `LIntrinsicOp.saturatingSub`
(`evalLIntrinsic_saturating_eq_minirust`)**: across every integer `RigidTy` `rk`
(`intTyBytes rk = some (it.signed, it.size.bytes)`) and all valid bit patterns
`x, y < 2 ^ (8 * it.size.bytes)`, `evalLIntrinsicValue` agrees with MiniRust's
`evalBinOp (.IntWithOverflow .Add / .Sub)`: when `IntType.can_represent` holds (`ovfBit = 0`), it
returns the exact non-overflowing sum/difference `((res % 2^(8*sz)).toNat)`; when overflow occurs
(`ovfBit = 1`), it clamps to unsigned `MAX` / `0` or signed `T::MIN` / `T::MAX`. -/
theorem evalLIntrinsic_saturating_eq_minirust
    (isSub : Bool)
    {rk : RigidTy} {it : Gen.IntType} (hrk : intTyBytes rk = some (it.signed, it.size.bytes))
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (restTys : List RigidTy) (decls : List LocalDecl)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    let op : Anneal.Mir.AdtAndControl.LIntrinsicOp := if isSub then .saturatingSub else .saturatingAdd
    let cop : Gen.IntBinOpWithOverflow := if isSub then .Sub else .Add
    let l := intFromBits x it
    let r := intFromBits y it
    let res := intCheckedArith cop l r
    let clampedBits : Nat :=
      if IntType.can_represent it res then
        (res % 2 ^ (8 * it.size.bytes)).toNat
      else match it.signed with
        | .Unsigned => if isSub then 0 else 2 ^ (8 * it.size.bytes) - 1
        | .Signed =>
          if l < 0 then 2 ^ (8 * it.size.bytes - 1) else 2 ^ (8 * it.size.bytes - 1) - 1
    evalBinOp (.IntWithOverflow cop) (.Int l, .Int it) (.Int r, .Int it) =
        .ok (tupleVal it (res % 2 ^ (8 * it.size.bytes)).toNat
              (if IntType.can_represent it res then 0 else 1), intBoolTupleTy it) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue op (rk :: restTys) decls layouts argOps
          [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag =
        some (.scalar ⟨clampedBits, it.size.bytes⟩) := by
  dsimp only
  obtain ⟨hgood, hSign, _⟩ := intTyBytes_intrinsic_props hrk false decls layouts
  refine ⟨evalBinOp_intWithOverflow _ it hgood _ _, ?_⟩
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hbeq : Nat.beq it.size.bytes 0 = false := by
    rw [nat_beq_eq_decide, decide_eq_false hsz]
  have hxWrap : wrapScalarBits x (scalarModulus it.size.bytes) = x := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hx]
  have hyWrap : wrapScalarBits y (scalarModulus it.size.bytes) = y := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hy]
  have hp : (2 : Int) ^ (8 * it.size.bytes) = ((2 ^ (8 * it.size.bytes) : Nat) : Int) := by
    push_cast; rfl
  rcases it with ⟨s, ⟨sz⟩⟩
  dsimp only at hgood hsz hbeq hx hy hxWrap hyWrap hp hSign ⊢
  cases isSub
  · -- saturatingAdd
    simp only [Bool.false_eq_true, ↓reduceIte, Anneal.Mir.AdtAndControl.evalLIntrinsicValue,
      resolveIntrinsicIsSigned, hSign, evalSaturatingAdd, hbeq, Nat.beq_refl, Bool.not_true,
      Bool.or_false, hxWrap, hyWrap, intCheckedArith]
    cases s with
    | Unsigned =>
      simp only [canRepresent_unsigned sz hsz, intFromBits, scalarModulus_eq, Nat.add_eq,
        Nat.sub_eq, nat_ble_eq_decide]
      by_cases hlt : x + y < 2 ^ (8 * sz)
      · rw [decide_eq_false (by omega : ¬(2 ^ (8 * sz) ≤ x + y)),
          decide_eq_true (by omega : 0 ≤ (x : Int) + y ∧ (x : Int) + y < ((2 ^ (8 * sz) : Nat) : Int))]
        simp only [↓reduceIte, Option.map]
        have hcast : (x : Int) + (y : Int) = ((x + y : Nat) : Int) := by push_cast; rfl
        rw [hcast, hp, nat_emod_toNat_of_lt (x + y) _ hlt]
      · rw [decide_eq_true (by omega : 2 ^ (8 * sz) ≤ x + y),
          decide_eq_false (by omega : ¬(0 ≤ (x : Int) + y ∧ (x : Int) + y < ((2 ^ (8 * sz) : Nat) : Int)))]
        rfl
    | Signed =>
      simp only [signedOverflowAdd_eq x y sz hsz hx hy, Nat.add_eq]
      cases hrep : IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
          (intFromBits x ⟨.Signed, ⟨sz⟩⟩ + intFromBits y ⟨.Signed, ⟨sz⟩⟩)
      · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, Option.map,
          isSignedNegative_eq x sz hsz hx, signedHalfModulus_eq_two_pow sz hsz, Nat.sub_eq]
        by_cases hxH : x < 2 ^ (8 * sz - 1)
        · have hlNonneg : ¬(intFromBits x ⟨.Signed, ⟨sz⟩⟩ < 0) := by
            simp [intFromBits, hxH]
          rw [decide_eq_false (by omega : ¬(2 ^ (8 * sz - 1) ≤ x))]
          simp only [hlNonneg, ↓reduceIte]
        · have hlNeg : intFromBits x ⟨.Signed, ⟨sz⟩⟩ < 0 := by
            simp [intFromBits, hxH]; omega
          rw [decide_eq_true (by omega : 2 ^ (8 * sz - 1) ≤ x)]
          simp only [hlNeg, ↓reduceIte]
      · simp [wrap_add_intFromBits ⟨.Signed, ⟨sz⟩⟩ x y hx hy]
  · -- saturatingSub
    simp only [↓reduceIte, Anneal.Mir.AdtAndControl.evalLIntrinsicValue,
      resolveIntrinsicIsSigned, hSign, evalSaturatingSub, hbeq, Nat.beq_refl, Bool.not_true,
      Bool.or_false, hxWrap, hyWrap, intCheckedArith]
    cases s with
    | Unsigned =>
      simp only [canRepresent_unsigned sz hsz, intFromBits, Nat.sub_eq, nat_ble_eq_decide]
      by_cases hle : y ≤ x
      · have hlt : x - y < 2 ^ (8 * sz) := by omega
        rw [decide_eq_true hle,
          decide_eq_true (by omega : 0 ≤ (x : Int) - y ∧ (x : Int) - y < ((2 ^ (8 * sz) : Nat) : Int))]
        simp only [↓reduceIte, Option.map]
        have hcast : (x : Int) - (y : Int) = ((x - y : Nat) : Int) := by omega
        rw [hcast, hp, nat_emod_toNat_of_lt (x - y) _ hlt]
      · rw [decide_eq_false hle,
          decide_eq_false (by omega : ¬(0 ≤ (x : Int) - y ∧ (x : Int) - y < ((2 ^ (8 * sz) : Nat) : Int)))]
        rfl
    | Signed =>
      simp only [signedOverflowSub_eq x y sz hsz hx hy]
      cases hrep : IntType.can_represent ⟨.Signed, ⟨sz⟩⟩
          (intFromBits x ⟨.Signed, ⟨sz⟩⟩ - intFromBits y ⟨.Signed, ⟨sz⟩⟩)
      · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, Option.map,
          isSignedNegative_eq x sz hsz hx, signedHalfModulus_eq_two_pow sz hsz, Nat.sub_eq]
        by_cases hxH : x < 2 ^ (8 * sz - 1)
        · have hlNonneg : ¬(intFromBits x ⟨.Signed, ⟨sz⟩⟩ < 0) := by
            simp [intFromBits, hxH]
          rw [decide_eq_false (by omega : ¬(2 ^ (8 * sz - 1) ≤ x))]
          simp only [hlNonneg, ↓reduceIte]
        · have hlNeg : intFromBits x ⟨.Signed, ⟨sz⟩⟩ < 0 := by
            simp [intFromBits, hxH]; omega
          rw [decide_eq_true (by omega : 2 ^ (8 * sz - 1) ≤ x)]
          simp only [hlNeg, ↓reduceIte]
      · simp only [Bool.not_true, ↓reduceIte, Option.map]
        have hsub := wrap_sub_intFromBits ⟨.Signed, ⟨sz⟩⟩ x y hx hy
        dsimp only at hsub
        rw [hxWrap, hyWrap] at hsub
        rw [← hsub]
        simp only [wrapScalarBits_eq, scalarModulus_eq, Nat.add_eq, Nat.sub_eq, nat_ble_eq_decide]
        generalize 2 ^ (8 * sz) = M at hx hy ⊢
        by_cases hle : y ≤ x
        · rw [decide_eq_true hle]; dsimp only
          have hsplit : x + (M - y) = M + (x - y) := by omega
          rw [hsplit, Nat.add_mod_left]
        · rw [decide_eq_false hle]; dsimp only
          have hsplit : x + (M - y) = M + x - y := by omega
          rw [hsplit]

/-- **Symbolic correspondence for `LIntrinsicOp.threeWayCompare`
(`evalLIntrinsic_threeWayCompare_eq_minirust`)**: across every integer `RigidTy` `rk`
(`intTyBytes rk = some (it.signed, it.size.bytes)`) and all valid bit patterns
`x, y < 2 ^ (8 * it.size.bytes)`, `evalLIntrinsicValue .threeWayCompare` returns the 1-byte
`Ordering` scalar `⟨ordBits (cmpOf (.Int it) x y), 1⟩` matching MiniRust's `evalBinOp (.Rel .Cmp)`. -/
theorem evalLIntrinsic_threeWayCompare_eq_minirust
    {rk : RigidTy} {it : Gen.IntType} (hrk : intTyBytes rk = some (it.signed, it.size.bytes))
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (restTys : List RigidTy) (decls : List LocalDecl)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    let l := intFromBits x it
    let r := intFromBits y it
    evalBinOp (.Rel .Cmp) (.Int l, .Int it) (.Int r, .Int it) =
        .ok (evalRelOp .Cmp (intCmp l r)) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .threeWayCompare (rk :: restTys) decls layouts
          argOps [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag =
        some (.scalar ⟨ordBits (cmpOf (.Int it) x y), 1⟩) := by
  dsimp only
  obtain ⟨hgood, hSign, _⟩ := intTyBytes_intrinsic_props hrk true decls layouts
  clear hrk
  refine ⟨rfl, ?_⟩
  rcases it with ⟨s, sz⟩
  dsimp only at hgood hSign hx hy ⊢
  have hsz : sz.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hbeq : Nat.beq sz.bytes 0 = false := by
    rw [nat_beq_eq_decide, decide_eq_false hsz]
  have hxWrap : wrapScalarBits x (scalarModulus sz.bytes) = x := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hx]
  have hyWrap : wrapScalarBits y (scalarModulus sz.bytes) = y := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hy]
  have hCmp := evalScalarBinOp_cmp_int ⟨s, sz⟩ hgood x y hx hy [] {}
  simp only [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, resolveIntrinsicIsSigned, hSign,
    evalThreeWayCompare, hbeq, Nat.beq_refl, Bool.not_true, Bool.or_false, hxWrap, hyWrap]
  simp only [evalScalarBinOp, hbeq, Nat.beq_refl, hxWrap, hyWrap, u8Ty] at hCmp
  cases s <;> cases hxy : Nat.beq x y <;> simp only [hxy] at hCmp ⊢
  · cases hle : Nat.ble x y <;>
      simp only [hle] at hCmp ⊢ <;> injection hCmp with hv <;> injection hv with hsc <;>
      simp [← hsc]
  · injection hCmp with hv; injection hv with hsc; simp [← hsc]
  · cases hslt : signedLt x y sz.bytes <;>
      simp only [hslt] at hCmp ⊢ <;> injection hCmp with hv <;> injection hv with hsc <;>
      simp [← hsc]
  · injection hCmp with hv; injection hv with hsc; simp [← hsc]

/-- **Symbolic correspondence for `LIntrinsicOp.ubChecks`
(`evalLIntrinsic_ubChecks_eq_minirust`)**: `evalLIntrinsicValue .ubChecks` returns the 1-byte
boolean scalar `0` or `1` governed by `ubChecksFlag`, matching MiniRust's session-configured
`ValueExpr.Constant (.Bool flag) .Bool`. -/
theorem evalLIntrinsic_ubChecks_eq_minirust
    (flag : Bool) (m : Mach) (tys : List RigidTy) (decls : List LocalDecl)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable) (argOps : List Operand) :
    Anneal.Mir.AdtAndControl.evalLIntrinsicValue .ubChecks tys decls layouts argOps [] flag =
        some (.scalar ⟨if flag then 1 else 0, 1⟩) ∧
      Interp.evalValue m (.Constant (.Bool flag) .Bool) = .ok ((.Bool flag, .Bool), m) := by
  cases flag <;> exact ⟨rfl, rfl⟩

/-- **Symbolic correspondence for `LIntrinsicOp.arithOffset`
(`evalLIntrinsic_arithOffset_eq_minirust`)**: on any 64-bit pointer `ptrVal` (without restricting
`ptrVal.offsetBytes`, `[adv ep2-A3]`) and `isize` count `countBits < 2^64` with pointee `rk` of byte
stride `elemSz`, `evalLIntrinsicValue .arithOffset` preserves `ptrVal.allocId` provenance and
computes the exact `2^64`-wrapped byte address produced by MiniRust's `evalPtrOffset m false`
(`ptrOffsetWrapping` / `ThinPointer.wrapping_offset`). -/
theorem evalLIntrinsic_arithOffset_eq_minirust
    (m : Mach) (ptrVal : ProvenancePtr)
    (countBits : Nat) (hCnt : countBits < 2 ^ 64)
    {rk : RigidTy} {elemSz : Nat} (restTys : List RigidTy)
    (decls : List LocalDecl) (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (hElem : intrinsicRigidTyByteSize decls layouts rk = some elemSz)
    (argOps : List Operand) (flag : Bool)
    (mrPtr : Ptr) (lTy : Gen.Type) (hAddr : mrPtr.addr = (ptrVal.offsetBytes : Int)) :
    let isizeIt : Gen.IntType := ⟨.Signed, ⟨8⟩⟩
    let byteDelta : Int := intFromBits countBits isizeIt * (elemSz : Int)
    ∃ newOff,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .arithOffset (rk :: restTys) decls layouts
          argOps [.ptr ptrVal 8, .scalar ⟨countBits, 8⟩] flag =
        some (.ptr { ptrVal with offsetBytes := newOff } 8) ∧
      evalPtrOffset m false (.Ptr ⟨mrPtr, none⟩, lTy) (.Int byteDelta, .Int isizeIt) =
        .ok (.Ptr ⟨{ mrPtr with addr := (newOff : Int) }, none⟩, lTy) := by
  dsimp only
  have hCntWrap : wrapScalarBits countBits (scalarModulus 8) = countBits := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hCnt]
  simp only [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, show Nat.beq 8 8 = true from rfl,
    ↓reduceIte, hElem, evalArithOffset, Bool.and_self, hCntWrap]
  refine ⟨_, rfl, ?_⟩
  simp only [evalPtrOffset, Bool.false_eq_true, ↓reduceIte, ptrOffsetWrapping,
    ThinPointer.wrapping_offset, ThinPointer.widen, Pure.pure, Except.pure, Bind.bind,
    Except.bind, bringInBounds, x86_64.PTR_SIZE, Interp.Size.bits, hAddr]
  congr 5
  have hIsNeg := isSignedNegative_eq countBits 8 (by decide) hCnt
  rw [hIsNeg]
  simp only [wrapScalarBits_eq, scalarModulus_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, intFromBits]
  have hp64 : (2 : Int) ^ (8 * 8) = ((2 ^ 64 : Nat) : Int) := by decide
  rw [hp64]
  by_cases hlt : countBits < 2 ^ (8 * 8 - 1)
  · rw [decide_eq_false (by omega : ¬(2 ^ (8 * 8 - 1) ≤ countBits))]
    simp only [hlt, ↓reduceIte]
    have hcast : (ptrVal.offsetBytes : Int) + (countBits : Int) * (elemSz : Int) =
        ((ptrVal.offsetBytes + countBits * elemSz : Nat) : Int) := by push_cast; rfl
    rw [hcast]
    exact (Int.natCast_emod (ptrVal.offsetBytes + countBits * elemSz) (2 ^ 64)).symm
  · rw [decide_eq_true (by omega : 2 ^ (8 * 8 - 1) ≤ countBits)]
    simp only [hlt, ↓reduceIte]
    symm
    change (((ptrVal.offsetBytes + (2 ^ 64 - (((2 ^ 64 - countBits) * elemSz) % 2 ^ 64))) % 2 ^ 64 : Nat) : Int) =
      ((ptrVal.offsetBytes : Int) + ((countBits : Int) - ((2 ^ 64 : Nat) : Int)) * (elemSz : Int)) %
        ((2 ^ 64 : Nat) : Int)
    generalize hMDef : (2 ^ 64 : Nat) = M
    have hMpos : 0 < M := by rw [← hMDef]; decide
    have hCntLe : countBits ≤ M := by rw [← hMDef] at *; omega
    generalize hMagDef : M - countBits = mag
    generalize hdDef : (mag * elemSz) % M = d
    have hdLt : d < M := by rw [← hdDef]; exact Nat.mod_lt _ hMpos
    have hSubLt : M - d ≤ M := Nat.sub_le M d
    rw [Int.natCast_emod (ptrVal.offsetBytes + (M - d)) M]
    have h1 : ((ptrVal.offsetBytes + (M - d) : Nat) : Int) =
        (ptrVal.offsetBytes : Int) + (M : Int) - (d : Int) := by omega
    have hdCast : (d : Int) = ((mag * elemSz : Nat) : Int) % (M : Int) := by
      rw [← hdDef]; exact Int.natCast_emod (mag * elemSz) M
    have hMagCast : ((countBits : Int) - (M : Int)) * (elemSz : Int) =
        -((mag * elemSz : Nat) : Int) := by
      have hc : (countBits : Int) - (M : Int) = -(mag : Int) := by omega
      rw [hc]
      push_cast
      exact Int.neg_mul (mag : Int) (elemSz : Int)
    rw [h1, hdCast, hMagCast]
    have h2 : (ptrVal.offsetBytes : Int) + (M : Int) - ((mag * elemSz : Nat) : Int) % (M : Int) =
        ((ptrVal.offsetBytes : Int) - (((mag * elemSz : Nat) : Int) % (M : Int))) + 1 * (M : Int) := by
      omega
    rw [h2, Int.add_mul_emod_self_right, Int.sub_emod, Int.emod_emod, ← Int.sub_emod,
      Int.sub_eq_add_neg]

/-- **Concrete 3-way diverging correspondence (`unreachableUnchecked` vs `abort` vs `panicUnwind`,
`evalLoweredTerminator_diverging_intrinsics_correspondence`, strengthened in `[adv ep2-A3]`)**:
1. MiniRust's `Interp.evalTerminator m .Unreachable` faults with `.ub` while `Interp.evalIntrinsic m
   .Abort` halts with `.abort`;
2. `abort` terminates immediately in `evalLoweredTerminator` (`= some (.terminated 0)`) and steps to
   `MirStepNode.retOutcome .abort` in `Trusted.stepMirFn`, bypassing `UnwindAction.cleanup 1`;
3. By contrast, `panicUnwind` on the identical cleanup-equipped CFG enters `bb1` in unwinding mode
   (`some (.goto 1 [.uninit] (some 0))`), runs through `UnwindResume` to `some (.panicked 0)`, and
   refines `TrustedRun` to a state that steps to `MirStepNode.retOutcome .panic` (the last
   conjunct, stated since `[adv ep2-B4]`; see `IntrinsicBoundary` Section 9 for the fully symbolic
   `panicUnwind` vs `abort` dispatch theorem). -/
theorem evalLoweredTerminator_diverging_intrinsics_correspondence (m : Mach)
    (arguments : List (Val × Gen.Type)) (retTy : Gen.Type) :
    Interp.evalTerminator m .Unreachable = .error (.ub "reached unreachable code") ∧
      Interp.evalIntrinsic m .Abort arguments retTy = .error .abort ∧
      Anneal.Mir.AdtAndControl.evalLoweredTerminator
          Anneal.Mir.AdtAndControl.witnessDivergingEnv
          Anneal.Mir.AdtAndControl.witnessAbortCleanupBody 0 [.uninit] none =
        some (.terminated 0) ∧
      stepMirFn Anneal.Mir.AdtAndControl.witnessAbortCleanupCm
          (initMachineState Anneal.Mir.AdtAndControl.witnessAbortCleanupCm []) =
        .retOutcome .abort ∧
      Anneal.Mir.AdtAndControl.evalLoweredTerminator
          Anneal.Mir.AdtAndControl.witnessDivergingEnv
          Anneal.Mir.AdtAndControl.witnessPanicCleanupBody 0 [.uninit] none =
        some (.goto 1 [.uninit] (some 0)) ∧
      Anneal.Mir.AdtAndControl.runLoweredCfgSteps
          Anneal.Mir.AdtAndControl.witnessDivergingEnv
          Anneal.Mir.AdtAndControl.witnessPanicCleanupBody 4 0 [.uninit] none =
        some (.panicked 0) ∧
      ∃ s', Anneal.Mir.AdtAndControl.TrustedRun Anneal.Mir.AdtAndControl.witnessPanicCleanupCm
          (initMachineState Anneal.Mir.AdtAndControl.witnessPanicCleanupCm []) s' ∧
        stepMirFn Anneal.Mir.AdtAndControl.witnessPanicCleanupCm s' = .retOutcome .panic := by
  have hw := Anneal.Mir.AdtAndControl.witness_diverging_abort_vs_panicUnwind
  exact ⟨rfl, rfl, hw.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2⟩

/-- **Axiom-audit hook for Episode 2's `.call`, `LIntrinsicOp`, and `LCallTable` multi-callee model
(`call_intrinsic_audit_closure`)**: references every Episode 2 theorem of
`Anneal.Mir.AdtAndControl` (Section 3b `.call` refinement + Sections 5a–5i: `LIntrinsicOp`,
`LCallTarget`, `V2026_06_01` adapter and its Episode 1 parity, UB / fault parity,
`abort`/`panicUnwind`, call-form `write_bytes` / `copy_nonoverlapping`, projected and
`PartialShell` call destinations, `LCallTable` multi-frame linked-callee refinement with
depth-limit, abort-propagation, unwinding, and cross-frame isolation lemmas, and the concrete
non-vacuity Witness Suites 1–10), ensuring `MiniRustSpec.Audit`'s `[DEINIT-AUDIT]` and
`#assert_all_minirustspec_standard_axioms` verify standard-axiom purity (`sorry_free=true`, zero
`Lean.ofReduceBool`) across all of them transitively. The symbolic `MiniRustSpec` bridges built on
these theorems (`abort`, `unreachable_unchecked`, `*_nonzero` vs `Assume`, two-sided success
parity, and negative controls) live in `Correspondence.IntrinsicBoundary` Section 8. -/
theorem call_intrinsic_audit_closure : True :=
  let _ := @Anneal.Mir.AdtAndControl.evalOperandsState_below_refines
  let _ := @Anneal.Mir.AdtAndControl.writePlaceState_bare_below_refines
  let _ := @Anneal.Mir.AdtAndControl.resolveIntrinsicIsSigned_defPath_irrel
  let _ := @Anneal.Mir.AdtAndControl.resolveIntrinsicShiftSigned_defPath_irrel
  let _ := @Anneal.Mir.AdtAndControl.resolveIntrinsicPointeeTy?_defPath_irrel
  let _ := @Anneal.Mir.AdtAndControl.evalLIntrinsicValue_refines_evalNonSelectIntrinsicCall
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_call_refines_evalTerminator
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_refines_trusted
  let _ := @Anneal.Mir.AdtAndControl.runLoweredCfgSteps_refines_trusted
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_call_goto_sound
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_call_uninhabited_dest_none
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredIntrinsicCall_goto_cleanup_invariant
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_goto_cleanup_invariant
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_at_end_refines_trusted
  let _ := @Anneal.Mir.AdtAndControl.runLoweredCfgSteps_with_stmts_refines_trusted
  let _ := @Anneal.Mir.AdtAndControl.LIntrinsicOp.fromRustIntrinsicKind_toRustIntrinsicKind
  let _ := @Anneal.Mir.AdtAndControl.LIntrinsicOp.toRustIntrinsicKind_fromRustIntrinsicKind
  let _ := @Anneal.Mir.AdtAndControl.LIntrinsicOp.fromRustIntrinsicKind_constEvalSelect_none
  let _ := @Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01_exactDiv
  let _ := @Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01_of_classifyRustIntrinsic
  let _ := @Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01_unreachable_targets
  let _ := @Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01_abort_and_panic_targets
  let _ := @Anneal.Mir.AdtAndControl.trustedSupportsIntrinsicDefPath_of_check
  let _ := @Anneal.Mir.AdtAndControl.classifyLinkedCallTarget_V2026_06_01_linked_precedence
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_call_intrinsic_goto_sound
  let _ := @Anneal.Mir.AdtAndControl.writePlaceState_init_proj_below_refines
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_call_unreachableUnchecked_ub_parity
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_call_exactDiv_ub_parity
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_call_abort_bypasses_cleanup
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_call_panicUnwind_cleanup
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_call_panicUnwind_unreachable_ub
  let _ := @Anneal.Mir.AdtAndControl.repeatByteBits_lt_pow
  let _ := @Anneal.Mir.AdtAndControl.evalWriteBytesSubplace_zero_count
  let _ := @Anneal.Mir.AdtAndControl.evalWriteBytesSubplace_dead_none
  let _ := @Anneal.Mir.AdtAndControl.evalWriteBytesSubplace_put_get
  let _ := @Anneal.Mir.AdtAndControl.evalWriteBytesSubplace_refines_writePlaceValue
  let _ := @Anneal.Mir.AdtAndControl.initLCalleeSlots_below_initLocals
  let _ := @Anneal.Mir.AdtAndControl.CallStackCorr.length_eq
  let _ := @Anneal.Mir.AdtAndControl.stepMirFn_multi_at_end_eq_evalTerminator
  let _ := @Anneal.Mir.AdtAndControl.unwindLCallStack_refines_unwindFromCallStack
  let _ := @Anneal.Mir.AdtAndControl.stepLoweredWithCallTable_maxCallDepth
  let _ := @Anneal.Mir.AdtAndControl.stepLoweredWithCallTable_diverging_return_ub
  let _ := @Anneal.Mir.AdtAndControl.stepLoweredWithCallTable_refines_trusted
  let _ := @Anneal.Mir.AdtAndControl.runLoweredWithCallTable_refines_trusted
  let _ := @Anneal.Mir.AdtAndControl.lookupCallee_eq_none_of_findCallee_none
  let _ := @Anneal.Mir.AdtAndControl.witnessInlineIntrinsics_bodyCorr
  let _ := @Anneal.Mir.AdtAndControl.witness_inline_intrinsics_cfg_refines_trusted
  let _ := @Anneal.Mir.AdtAndControl.witnessPtrIntrinsics_bodyCorr
  let _ := @Anneal.Mir.AdtAndControl.witness_ptr_intrinsics_cfg_refines_trusted
  let _ := @Anneal.Mir.AdtAndControl.witness_call_writeBytes_and_copyNonOverlapping_subplace
  let _ := @Anneal.Mir.AdtAndControl.witness_inline_intrinsics_ub_parity
  let _ := @Anneal.Mir.AdtAndControl.witnessAbortCleanup_bodyCorr
  let _ := @Anneal.Mir.AdtAndControl.witnessPanicCleanup_bodyCorr
  let _ := @Anneal.Mir.AdtAndControl.witness_diverging_abort_vs_panicUnwind
  let _ := @Anneal.Mir.AdtAndControl.witness_multi_callee_two_deep_and_unwind
  -- `[adv ep2-B1]` Section 5f: Episode 1 adapter parity, `trustedSupportsIntrinsicDefPath`
  -- premise elimination, value-intrinsic fault parity, and Witness Suites 5–6.
  let _ := @Anneal.Mir.AdtAndControl.stringEq_eq_true_iff
  let _ := @Anneal.Mir.AdtAndControl.stringEq_eq_decide
  let _ := @Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01_eq_ep1Table
  let _ := @Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01_aliases_none
  let _ := @Anneal.Mir.AdtAndControl.trustedSupportsIntrinsicDefPath_iff_lowerIntrinsicKind
  let _ := @Anneal.Mir.AdtAndControl.LTerminator.refinable_call_of_lowerIntrinsicKind
  let _ := @Anneal.Mir.AdtAndControl.LTerminator.multiRefinable_call_of_lowerIntrinsicKind
  let _ := @Anneal.Mir.AdtAndControl.evalLIntrinsicValue_none_trusted_fault
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredIntrinsicCall_of_value
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_call_value_intrinsic_fault_parity
  let _ := @Anneal.Mir.AdtAndControl.slotsRefine_below_init_eq
  let _ := @Anneal.Mir.AdtAndControl.witnessSignWidth_bodyCorr
  let _ := @Anneal.Mir.AdtAndControl.witness_intrinsic_signedness_width_cfg_refines_trusted
  let _ := @Anneal.Mir.AdtAndControl.witness_signed_shift_overflow_ub_parity
  -- `[adv ep2-B2]` Section 5h: depth-limit checkpoints, callee-shadowing non-vacuity,
  -- concrete Trusted traces, and multi-frame unwinding / diverging linked-call witnesses.
  let _ := @Anneal.Mir.AdtAndControl.trustedIter_run
  let _ := @Anneal.Mir.AdtAndControl.terminateLCallStack_eq_some
  let _ := @Anneal.Mir.AdtAndControl.lookupCallee_none_of_lowerIntrinsicKind
  let _ := @Anneal.Mir.AdtAndControl.witness_multi_frame_unwind_and_diverging_calls
  let _ := @Anneal.Mir.AdtAndControl.witness_maxCallDepth_checkpoint
  -- `[adv ep2-A1]` Stage 1 + Section 5g: projected & `PartialShell` call destinations,
  -- exact `.ub` fault parity (`IntrinsicResolvedInBody`), target-presence boundary,
  -- `Ordering` ADT encoding (`orderingVariant?`), call-form `write_bytes` / `copy_nonoverlapping`
  -- CFG witness, and Witness Suites 7–8.
  let _ := @Anneal.Mir.AdtAndControl.FieldListBelow.set_both
  let _ := @Anneal.Mir.AdtAndControl.promoteShellToFieldSlot_below
  let _ := @Anneal.Mir.AdtAndControl.writeToFieldSlot_noExplode_below_refines
  let _ := @Anneal.Mir.AdtAndControl.writePlaceState_dest_below_refines
  let _ := @Anneal.Mir.AdtAndControl.evalLIntrinsicValue_resolved_none_eq_ub
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_call_resolved_value_intrinsic_ub_parity
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_call_nonReturning_with_target_extCall
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_call_value_without_target_extCall
  let _ := @Anneal.Mir.AdtAndControl.orderingVariant?_std_and_perm
  let _ := @Anneal.Mir.AdtAndControl.orderingVariant?_rejects_invalid
  let _ := @Anneal.Mir.AdtAndControl.evalThreeWayCompare_orderingVariant_discriminant_roundtrip
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingSubplace_single_nonzero
  let _ := @Anneal.Mir.AdtAndControl.witness_cfg_call_writeBytes_and_copyNonOverlapping_subplace
  let _ := @Anneal.Mir.AdtAndControl.witnessProjStmtCall_bodyCorr
  let _ := @Anneal.Mir.AdtAndControl.witness_projected_and_partialShell_call_destinations
  let _ := @Anneal.Mir.AdtAndControl.witnessWidePtrAndChar_bodyCorr
  let _ := @Anneal.Mir.AdtAndControl.witness_wide_ptr_char_and_bodyCorr_ub_parity
  -- `[adv ep2-A2]` Section 5i: per-projection `NoUninitExplosionOnProj`, exact outermost
  -- abort-site characterization (`terminateLCallStack_eq_some_iff`), cross-frame pointer
  -- isolation (`crossFrameValueOk_ptr_iff`), `unwindLCallStack_cleanup_exact`, multi-frame
  -- projected `Deinit` bridge, and Witness Suite 10.
  let _ := @Anneal.Mir.AdtAndControl.noUninitExplosionOnProj_of_eq_none
  let _ := @Anneal.Mir.AdtAndControl.terminateLCallStack_eq_some_iff
  let _ := @Anneal.Mir.AdtAndControl.crossFrameValueOk_ptr_iff
  let _ := @Anneal.Mir.AdtAndControl.unwindLCallStack_cleanup_exact
  let _ := @Anneal.Mir.AdtAndControl.stepMirFn_multi_deinit_projected_trustedRun
  let _ := @Anneal.Mir.AdtAndControl.witness_diverging_proj_move_cleanup_and_protectors
  trivial

/-- **Residual axiom-audit hook for the rest of `Anneal.Mir.AdtAndControl`
(`adt_control_residual_audit_closure`, `[adv ep2-B4]`)**: references every public,
user-declared theorem of `Anneal.Mir.AdtAndControl` that neither `subplace_audit_closure`,
`call_intrinsic_audit_closure`, nor any other `MiniRustSpec` declaration reaches (192 theorems of the
scalar-validity, ADT layout, place, `Deinit` / `Retag`, and lowered-CFG layers that predate
Episode 2). With those closures it puts **all 607** public theorems of `Anneal.Mir.AdtAndControl`
inside the dependency closure whose axioms `MiniRustSpec.Audit` checks, which
`#assert_adt_control_audit_coverage` (`[ADT-AUDIT-COVERAGE]`) re-verifies mechanically. -/
theorem adt_control_residual_audit_closure : True :=
  let _ := @Anneal.Mir.AdtAndControl.ScalarValidRange.contains_eq_true_iff
  let _ := @Anneal.Mir.AdtAndControl.ScalarValidRange.contains_lt_pow
  let _ := @Anneal.Mir.AdtAndControl.ScalarValidRange.contains_eq_wrappingRangeContains
  let _ := @Anneal.Mir.AdtAndControl.ScalarValidRange.full_contains
  let _ := @Anneal.Mir.AdtAndControl.ScalarValidRange.full_contains_iff
  let _ := @Anneal.Mir.AdtAndControl.ScalarValidRange.nonZero_contains_iff
  let _ := @Anneal.Mir.AdtAndControl.ScalarValidRange.nonZero_not_contains_zero
  let _ := @Anneal.Mir.AdtAndControl.ScalarValidRange.isEmpty_iff_forall_not_contains
  let _ := @Anneal.Mir.AdtAndControl.ScalarValidRange.isWrapping_contains_zero
  let _ := @Anneal.Mir.AdtAndControl.ScalarValidRange.isFull_iff_forall_contains
  let _ := @Anneal.Mir.AdtAndControl.ScalarValidRange.containsNiche_iff_exists_excluded
  let _ := @Anneal.Mir.AdtAndControl.ScalarValidRange.nonZero_containsNiche
  let _ := @Anneal.Mir.AdtAndControl.ScalarValidRange.complement_contains
  let _ := @Anneal.Mir.AdtAndControl.cOffset?_monotone
  let _ := @Anneal.Mir.AdtAndControl.resolveAdtOffsetOf_union_eq_zero
  let _ := @Anneal.Mir.AdtAndControl.resolveAdtOffsetOf_transparent_nonZst
  let _ := @Anneal.Mir.AdtAndControl.resolveAdtOffsetOf_reprC_monotone
  let _ := @Anneal.Mir.AdtAndControl.resolveAdtOffsetOfChain_bounds_and_align
  let _ := @Anneal.Mir.AdtAndControl.cOffset?_ge_start
  let _ := @Anneal.Mir.AdtAndControl.resolveAdtOffsetOf_taggedEnum_ge_tagSize
  let _ := @Anneal.Mir.AdtAndControl.evalAdtDiscriminant_uninhabited_variant_none
  let _ := @Anneal.Mir.AdtAndControl.evalAdtDiscriminant_niche_shell_none
  let _ := @Anneal.Mir.AdtAndControl.evalAdtDiscriminant_tag_apart_shell
  let _ := @Anneal.Mir.AdtAndControl.evalAdtDiscriminant_niche_init_ill_formed_none
  let _ := @Anneal.Mir.AdtAndControl.evalAdtDiscriminant_uninit
  let _ := @Anneal.Mir.AdtAndControl.placeTy_eq_none_imp_placeTyResolved_eq_none
  let _ := @Anneal.Mir.AdtAndControl.evalAdtDiscriminant_init_agrees_trusted
  let _ := @Anneal.Mir.AdtAndControl.allFieldsUninit_getElem?
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_read_root_ub
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_read_extension_ub
  let _ := @Anneal.Mir.AdtAndControl.shellFieldRead_of_allFieldsUninit
  let _ := @Anneal.Mir.AdtAndControl.readFieldSlot_init_field
  let _ := @Anneal.Mir.AdtAndControl.readFieldSlot_init_downcast_field
  let _ := @Anneal.Mir.AdtAndControl.readFieldSlot_normalizeShell_field
  let _ := @Anneal.Mir.AdtAndControl.readFieldSlot_normalizeShell_downcast_field
  let _ := @Anneal.Mir.AdtAndControl.shellFieldRead_set_ne
  let _ := @Anneal.Mir.AdtAndControl.shellFieldRead_set_self
  let _ := @Anneal.Mir.AdtAndControl.shellFieldRead_of_getElem?
  let _ := @Anneal.Mir.AdtAndControl.Diverges.cons_left
  let _ := @Anneal.Mir.AdtAndControl.deinitFieldSlot_read_diverges_eq
  let _ := @Anneal.Mir.AdtAndControl.SameScalarLocals.symm
  let _ := @Anneal.Mir.AdtAndControl.deinit_root_not_scalar
  let _ := @Anneal.Mir.AdtAndControl.UninitAt.not_scalar
  let _ := @Anneal.Mir.AdtAndControl.readPlaceState_congr_unchanged
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_read_disjoint_eq
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_root_read_other_local_eq
  let _ := @Anneal.Mir.AdtAndControl.map_init_set_set
  let _ := @Anneal.Mir.AdtAndControl.deinitFieldSlot_write_reinit
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_uninit_constantIndex_oob_none
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_uninit_subslice_oob_none
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_write_reinit
  let _ := @Anneal.Mir.AdtAndControl.deinitFieldSlot_niche_write_needs_setDiscriminant
  let _ := @Anneal.Mir.AdtAndControl.deinitFieldSlot_init_read_ok
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_deinit_root_refines
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_deinit_projected_init_refines
  let _ := @Anneal.Mir.AdtAndControl.evalStmt_deinit_projected_uninit_root_divergence
  let _ := @Anneal.Mir.AdtAndControl.length_deinitBytes
  let _ := @Anneal.Mir.AdtAndControl.fieldBytes_frame
  let _ := @Anneal.Mir.AdtAndControl.structBytes_deinit
  let _ := @Anneal.Mir.AdtAndControl.fieldSlotToLocalSlotState_toFieldSlot
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_field_shell
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_bytes_simulation
  let _ := @Anneal.Mir.AdtAndControl.specFieldLayout_eq_some
  let _ := @Anneal.Mir.AdtAndControl.reprC_layoutDisjoint
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_reprC_bytes_simulation
  let _ := @Anneal.Mir.AdtAndControl.valuesBytes_iff_slotsBytes_map_init
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_enum_field_preserves_discriminant
  let _ := @Anneal.Mir.AdtAndControl.cOffset?_isSome
  let _ := @Anneal.Mir.AdtAndControl.adtLayout?_reprC_struct
  let _ := @Anneal.Mir.AdtAndControl.reprC_struct_placed
  let _ := @Anneal.Mir.AdtAndControl.rustOffset?_isSome
  let _ := @Anneal.Mir.AdtAndControl.rustOffset?_ge_start
  let _ := @Anneal.Mir.AdtAndControl.rustOffset?_monotone
  let _ := @Anneal.Mir.AdtAndControl.resolveAdtOffsetOf_reprRust_struct
  let _ := @Anneal.Mir.AdtAndControl.reprRust_canonical_struct_placed
  let _ := @Anneal.Mir.AdtAndControl.resolveAdtOffsetOf_reprInt_enum
  let _ := @Anneal.Mir.AdtAndControl.resolveAdtOffsetOf_reprCInt_enum
  let _ := @Anneal.Mir.AdtAndControl.adtLayout?_taggedEnum_isSome
  let _ := @Anneal.Mir.AdtAndControl.taggedEnum_placed
  let _ := @Anneal.Mir.AdtAndControl.pathRange_struct_field
  let _ := @Anneal.Mir.AdtAndControl.pathRange_struct_downcast_field
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_taggedEnum_bytes_simulation
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_downcast_inactive_variant_none
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_downcast_active_variant_eq
  let _ := @Anneal.Mir.AdtAndControl.univariantEnum_present_reprRust_placed
  let _ := @Anneal.Mir.AdtAndControl.univariantEnum_absent_placed
  let _ := @Anneal.Mir.AdtAndControl.noPresentEnum_placed
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_univariantEnum_bytes_simulation
  let _ := @Anneal.Mir.AdtAndControl.union_field_uninit_bytes
  let _ := @Anneal.Mir.AdtAndControl.evalRetagPlace_dead
  let _ := @Anneal.Mir.AdtAndControl.evalRetagPlace_bad_index_false
  let _ := @Anneal.Mir.AdtAndControl.evalRetagPlace_inactive_variant_false
  let _ := @Anneal.Mir.AdtAndControl.evalRetagPlace_deref_false
  let _ := @Anneal.Mir.AdtAndControl.evalRetagPlace_uninit_ref
  let _ := @Anneal.Mir.AdtAndControl.ValueListEqUpToTag.refl
  let _ := @Anneal.Mir.AdtAndControl.retagSlotOk_enum_niche_shell_false
  let _ := @Anneal.Mir.AdtAndControl.retagValueOk_enum_niche_ill_formed_false
  let _ := @Anneal.Mir.AdtAndControl.retagVariant_rejected_false
  let _ := @Anneal.Mir.AdtAndControl.retagSlotOk_enum_variant_rejected_false
  let _ := @Anneal.Mir.AdtAndControl.retagVariantOk_eq_true
  let _ := @Anneal.Mir.AdtAndControl.retagValueOk_enum_sound
  let _ := @Anneal.Mir.AdtAndControl.projectFieldSlot_of_uninitAt_aux
  let _ := @Anneal.Mir.AdtAndControl.projectFieldSlot_of_uninitAt
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_then_retag_same_false
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlaceTyped_sound
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlaceTyped_no_union
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlaceTyped_through_init_union_none
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlaceTyped_init_union_root_none
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_union_field_divergence
  let _ := @Anneal.Mir.AdtAndControl.projectFieldSlot_uninit_ne_init
  let _ := @Anneal.Mir.AdtAndControl.deinitReachesInitUnion_uninit
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlaceTyped_uninit_eq
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlaceTyped_uninit_union_ok
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlaceTyped_nested_init_union_none
  let _ := @Anneal.Mir.AdtAndControl.deinitTailOk_indexLocalsOk
  let _ := @Anneal.Mir.AdtAndControl.deinitFieldSlot_indexLocalsOk
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_indexLocalsOk
  let _ := @Anneal.Mir.AdtAndControl.evalDeinitPlace_bad_index_none
  let _ := @Anneal.Mir.AdtAndControl.copyNonOverlappingChecks_zero_len_sound
  let _ := @Anneal.Mir.AdtAndControl.copyNonOverlappingChecks_null_src
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingWithCount_zero
  let _ := @Anneal.Mir.AdtAndControl.provenanceLocal_spec
  let _ := @Anneal.Mir.AdtAndControl.resolveSyntheticLocal_spec
  let _ := @Anneal.Mir.AdtAndControl.copyWholeLocal_spec
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingState_zero_count
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingState_dead_none
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingState_zst_bulk_noop
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingState_whole_local_copies_slot
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingState_zst_copies_uninit
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingState_same_local_non_zst_none
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingState_zst_non_whole_noop
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingState_non_whole_unsupported
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingState_whole_local_below
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingState_read_dst_bare
  let _ := @Anneal.Mir.AdtAndControl.evalCopyNonOverlappingState_read_other_bare
  let _ := @Anneal.Mir.AdtAndControl.evalCopySingleDirect_same_local_ub
  let _ := @Anneal.Mir.AdtAndControl.evalCopySingleDirect_dead_or_uninit_src_ub
  let _ := @Anneal.Mir.AdtAndControl.copyWholeLocal_live_of_not_copyTargetDead
  let _ := @Anneal.Mir.AdtAndControl.evalCopySingleDirect_whole_local_refines
  let _ := @Anneal.Mir.AdtAndControl.evalCopySingleDirect_whole_local_invalid_bool_char_divergence
  let _ := @Anneal.Mir.AdtAndControl.validPointerCoercion_no_mut_gain
  let _ := @Anneal.Mir.AdtAndControl.evalPointerCoercion_preserves
  let _ := @Anneal.Mir.AdtAndControl.evalShallowInitBox_preserves
  let _ := @Anneal.Mir.AdtAndControl.evalWrapUnsafeBinder_preserves
  let _ := @Anneal.Mir.AdtAndControl.evalWrapUnsafeBinder_rejects_niche
  let _ := @Anneal.Mir.AdtAndControl.evalAdtDiscriminant_refines_evalRvalue
  let _ := @Anneal.Mir.AdtAndControl.evalRvalue_wrapUnsafeBinder_copy
  let _ := @Anneal.Mir.AdtAndControl.evalWrapUnsafeBinder_identity_refines_evalRvalue
  let _ := @Anneal.Mir.AdtAndControl.evalWrapUnsafeBinder_wrap_vs_evalRvalue
  let _ := @Anneal.Mir.AdtAndControl.placeRuntimeAccessOk_iff
  let _ := @Anneal.Mir.AdtAndControl.runLoweredCfgSteps_zero_fuel
  let _ := @Anneal.Mir.AdtAndControl.runLoweredCfgSteps_add_fuel
  let _ := @Anneal.Mir.AdtAndControl.runLoweredCfgSteps_mono
  let _ := @Anneal.Mir.AdtAndControl.stepMirState_running
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_unreachable_ub
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_switch_invalid_none
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_switch_bad_targets_none
  let _ := @Anneal.Mir.AdtAndControl.SwitchTy.validBits_bool
  let _ := @Anneal.Mir.AdtAndControl.SwitchTy.validBits_char_iff
  let _ := @Anneal.Mir.AdtAndControl.SwitchTy.validBits_lt_two_pow
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_assert_bad_msg_none
  let _ := @Anneal.Mir.AdtAndControl.assert_unreachable_unwind_ub
  let _ := @Anneal.Mir.AdtAndControl.placeFrameAccessOk_live
  let _ := @Anneal.Mir.AdtAndControl.placeFrameAccessOk_index
  let _ := @Anneal.Mir.AdtAndControl.slotProjectionAccessOk_noDeref
  let _ := @Anneal.Mir.AdtAndControl.slotPlaceProjectionOk_noDeref
  let _ := @Anneal.Mir.AdtAndControl.slotPlaceProjectionOk_inactive_variant_false
  let _ := @Anneal.Mir.AdtAndControl.slotPlaceProjectionOk_field_oob_false
  let _ := @Anneal.Mir.AdtAndControl.slotProjectionAccessOk_of_deinitFieldSlot
  let _ := @Anneal.Mir.AdtAndControl.slotPlaceProjectionOk_of_evalDeinitPlace
  let _ := @Anneal.Mir.AdtAndControl.placeFrameAccessOk_of_evalDeinitPlace
  let _ := @Anneal.Mir.AdtAndControl.checkSlotProjectionOk_of_slotProjectionAccessOk
  let _ := @Anneal.Mir.AdtAndControl.checkPlaceSlotOk_of_slotPlaceProjectionOk
  let _ := @Anneal.Mir.AdtAndControl.checkPlaceSlotOk_of_evalDeinitPlace
  let _ := @Anneal.Mir.AdtAndControl.checkPlaceSlotOk_inactive_variant_false
  let _ := @Anneal.Mir.AdtAndControl.checkPlaceSlotOk_array_index_eq
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_drop_sound
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_drop_dead_none
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_drop_bad_index_none
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_drop_dead_agrees_trusted
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_drop_trusted_live
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_drop_bare_divergence
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_drop_projected_refines
  let _ := @Anneal.Mir.AdtAndControl.checkPlaceSlotOk_uninit
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_drop_inactive_variant_none
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_drop_index_oob_none
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_drop_deref_none
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_drop_projected_init_refines
  let _ := @Anneal.Mir.AdtAndControl.evalLoweredTerminator_drop_projected_uninit_divergence
  let _ := @Anneal.Mir.AdtAndControl.BodyCorr.toBodyCorrWithStmts
  let _ := @Anneal.Mir.AdtAndControl.stepMirFn_deinit_root_trustedRun
  let _ := @Anneal.Mir.AdtAndControl.stripUnitElems_append_unit
  trivial

end MiniRustSpec.Correspondence.DeinitBridge
