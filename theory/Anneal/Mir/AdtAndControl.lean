/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Mir.PlaceAndRvalue
import Trusted.Rustc.V2026_06_01.MirSemantics.Bytes
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine

open Trusted.Sequence
open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.Mir.PlaceAndRvalue

namespace Anneal.Mir.AdtAndControl

/-!
# ADT Layouts, Projected `Deinit`/`Retag`/`CopyNonOverlapping`, Multi-Block CFG Execution, and Synthetic Sub-Place Pointers

This module formalizes the Episode 1 semantic surface of `crates/anneal-mir`
(`ws-mir-lower-adt-deinit-retag-terminators`, and in Section 4 the synthetic sub-place pointer,
`Deref`, and `copy_nonoverlapping` surface of `ws-mir-lower-deref-subplace-and-minirust-adt-deinit`)
and relates it to `Trusted.Rustc.V2026_06_01.MirSemantics`:

1. **Section 1 — `ScalarValidRange` niches, ADT layouts, `OffsetOf`, and `Discriminant`**
   (`crates/anneal-mir/src/ir.rs`, `rvalue.rs`):
   - `ScalarValidRange` (`ir.rs`), its width-bounded wrapping/non-wrapping membership test,
     `full`/`nonZero` constructors, emptiness/fullness/niche characterizations, the
     wrapping complement partition, and exact agreement with Trusted's
     `wrappingRangeContains` (`rustc_abi::WrappingRange::contains`).
   - `AdtLayoutSpec`: `#[repr(C)]`/`#[repr(Rust)]`/`#[repr(transparent)]` structs, unions,
     explicit-tag `#[repr(Int)]`/`#[repr(C, Int)]` enums, `rustc`'s univariant tagless enums
     (absent variants are 1-ZSTs, `A1`/`B2`), zero-variant enums (`E0084`), and unspecified
     tagless layouts; `adtLayout?`, `resolveAdtOffsetOf` (`AdtDef::field_offset`), and multi-step
     `resolveAdtOffsetOfChain` (`NullOp::OffsetOf(fields)`), with
     `resolveAdtOffsetOf_bounds_and_align` and `resolveAdtOffsetOfChain_bounds_and_align` (every
     single-step and chained field projection fits in the root container and is aligned),
     `resolveAdtOffsetOf_taggedEnum_ge_tagSize` (explicit-tag enum fields sit after the tag),
     `#[repr(C)]` offset monotonicity, union zero offsets, and `#[repr(transparent)]` zero-offset
     delegation.
   - `evalAdtDiscriminant` (`Rvalue::Discriminant` on typed ADTs): absent/uninhabited variant
     rejection (`B2`), the niche-capable incomplete-shell rule (`PartialAggregate::tag_is_readable`,
     `A3`), niche-capable `Init` well-formedness (`B4`), and agreement with Trusted's
     `evalPlaceDiscriminant`.

2. **Section 2 — Projected `Deinit`, `Retag`, `CopyNonOverlapping`, `ShallowInitBox`,
   `WrapUnsafeBinder`, and `PointerCoercion`** (`rvalue.rs`):
   - `deinitFieldSlot` / `evalDeinitPlace` (`deinit_in_slot` / `deinit_place`) over the
     `FieldSlot` / `LocalSlotState` model of `Anneal.Mir.PlaceAndRvalue`, including static
     `ConstantIndex`/`Subslice` tail bounds (`deinitTailOk`), with the lens laws
     `evalDeinitPlace_read_same_ub` (Get-Deinit: every prefix and extension of the place,
     including the whole local, faults), `evalDeinitPlace_read_disjoint_eq` (Disjoint-Sibling
     and distinct-local frames), `evalDeinitPlace_write_reinit` (Put-After-Deinit re-promotion)
     and its niche counterpart `deinitFieldSlot_niche_write_needs_setDiscriminant` (`A3`).
   - A byte-level reference model (`deinitBytes` over `List (Option UInt8)`) and the simulation
     theorems `structBytes_deinit` / `evalDeinitPlace_bytes_simulation` /
     `evalDeinitPlace_reprC_bytes_simulation` (one field of a struct with disjoint field layouts,
     in particular `#[repr(C)]` via `resolveAdtOffsetOf`) and, for arbitrarily nested `Field` and
     tag-preserving `Downcast` + `Field` paths over well-formed nested layouts (`ByteLayout`,
     `SlotBytes`, `pathRange`), `deinitFieldSlot_bytes_sim` /
     `evalDeinitPlace_nested_bytes_simulation`; the nested layouts are built from the layout
     specification (`specByteLayout`: field `i` at `resolveAdtOffsetOf spec v i`, well formed by
     `specByteLayout_wf` for `#[repr(C)]` structs, canonical `#[repr(Rust)]` structs,
     explicit-tag enum variants, and univariant/no-present enum variants via
     `reprC_struct_placed` / `reprRust_canonical_struct_placed` / `taggedEnum_placed` /
     `univariantEnum_present_reprRust_placed` / `univariantEnum_absent_placed` /
     `noPresentEnum_placed`), giving `evalDeinitPlace_spec_bytes_simulation`,
     `evalDeinitPlace_taggedEnum_bytes_simulation`, and
     `evalDeinitPlace_univariantEnum_bytes_simulation` (plus active/inactive `Downcast` variant
     enforcement `evalDeinitPlace_downcast_inactive_variant_none` /
     `evalDeinitPlace_downcast_active_variant_eq`; `AdtDiscrSpec.CoherentWith` ties the
     discriminant facts to the layout): field-level `Deinit` is MiniRust's byte-range `Uninit`
     write (closing the projected-`Deinit` gap noted at
     `MiniRustSpec/Correspondence/Translate.lean:3742`).
   - The Rust-faithful typed walk `evalDeinitPlaceTyped` (with the declared types' union
     information `unionAt`) rejects a projected `Deinit` into an initialized union — at the root
     (`evalDeinitPlaceTyped_init_union_root_none`) or nested inside an initialized struct/tuple
     (`evalDeinitPlaceTyped_nested_init_union_none`, `evalDeinitPlaceTyped_through_init_union_none`:
     `UnsupportedPlaceProjection`, because a union has no per-field shell and an `Uninit` write
     over one field clobbers its overlapping siblings, `union_field_uninit_bytes`) — while
     accepting projected `Deinit` on an uninitialized union (`evalDeinitPlaceTyped_uninit_union_ok`,
     `evalDeinitPlaceTyped_uninit_eq`) and otherwise coinciding with `evalDeinitPlace`
     (`evalDeinitPlaceTyped_sound`, `evalDeinitPlaceTyped_no_union`, plus index-local validation
     `evalDeinitPlace_indexLocalsOk` / `evalDeinitPlace_bad_index_none`).
   - Step refinement against Trusted's `evalStmt` on `.deinit` under the `SlotBelow` frame
     relation (Anneal knows less than Trusted; every Anneal read is a Trusted read:
     `readPlaceState_below_refines`), and the documented divergence on projected `Deinit`
     below an uninitialized local (`evalStmt_deinit_projected_uninit_root_divergence`).
   - `evalRetagPlace` (`retag_place`: the value-dependent part of `prepare_place_access` — no
     `Deref` (`evalRetagPlace_deref_false`), the index pre-read (`evalRetagPlace_bad_index_false`),
     and `check_slot_projection` (`evalRetagPlace_inactive_variant_false`) — raw retags and recursive reference checks with the `A3`
     dangling rule, `A3` niche-shell tag readability, `B4` niche-capable `Init` well-formedness,
     `B2` rejection of out-of-range variants and variants with uninhabited fields via
     `RetagTy.inhabited`, and `Deinit`-then-`Retag` failure `evalDeinitPlace_then_retag_same_false`)
     with step refinement of Trusted's `evalStmt` on `.retag`: for both reference retags
     (`evalStmt_retag_ref_refines`) and raw-pointer retags (`evalStmt_retag_raw_refines`,
     `evalStmt_retag_raw_global_refines`) of non-union places (`placeTouchesUnion localDecls
     layouts place = false`, discharged by default for bare locals), Trusted reads and retags the
     pointer Anneal validated and steps without faulting whenever its borrow model (`active`,
     `reserved`, or non-`&mut` `frozen`) or global-allocation table grants the access (with
     `evalStmt_retag_disabled_ub`, `evalStmt_retag_ref_frozen_mut_ub`,
     `evalStmt_retag_raw_untracked_divergence`, `evalStmt_retag_raw_scalar_addr_reject`, and
     `evalStmt_retag_noRef_scalar_divergence` characterizing disabled tags, `frozen` `&mut` retags,
     untracked `.ptr` raw pointers, provenance-less `.scalar` raw-pointer addresses, and
     reference-free scalars),
     `copyNonOverlappingChecks` and the stateful `evalCopyNonOverlappingState` (agreeing with
     Trusted's `rangesDisjoint`; whole locals are resolved from the pointers themselves —
     provenance local, synthetic base address, declared element type — as `resolve_synthetic_local`
     does (`copyWholeLocal_spec`, `copyWholeLocal_live_of_not_copyTargetDead`); dead-local
     provenance rejected when the byte length is non-zero or `count = 1`; same-local non-ZST copies
     rejected as overlapping; zero-sized copies that are not whole-local copies, e.g. through
     out-of-frame provenance, are no-ops; whole-local copies copy the source state verbatim,
     including `.uninit`, with read-after-copy and frame laws
     `evalCopyNonOverlappingState_read_dst_bare` / `evalCopyNonOverlappingState_read_other_bare`
     and refinement against Trusted's `evalCopySingleDirect` for arbitrary `localDecls`, borrow
     stacks, and untyped or same-shape typed pointees whenever `validateValueForTy?` accepts the
     written root value in `evalCopySingleDirect_whole_local_refines`, alongside the documented
     invalid `bool`/`char` untyped-copy divergence
     `evalCopySingleDirect_whole_local_invalid_bool_char_divergence`),
     `evalShallowInitBox`, `evalWrapUnsafeBinder`, and `evalPointerCoercion` with their
     soundness/preservation theorems, and refinement of Trusted's `evalRvalue` for `Discriminant`
     (`evalAdtDiscriminant_refines_evalRvalue`) and identity `WrapUnsafeBinder`, with the
     documented binder-struct representation divergence.

3. **Section 3 — Multi-block terminator CFG execution** (`cfg.rs`):
   - `LTerminator` (`LoweredTerminator`, with `SwitchTy` discriminant types whose valid bit
     patterns `SwitchInt` enforces strictly and bounds within `8 * dty.bytes` bits), the single
     step `evalLoweredTerminator` (`eval_lowered_terminator`), and the fuel-bounded driver
     `runLoweredCfgSteps` (`eval_cfg_in_state`), with fuel metatheory
     (`runLoweredCfgSteps_zero_fuel`, `runLoweredCfgSteps_add_fuel`, `runLoweredCfgSteps_mono`),
     `evalSwitchTargets_eq_lookupSwitchTarget`, `Assert` panic-message validation, `Call`
     return/cleanup-unwind soundness (`evalLoweredTerminator_call_goto_sound`), the target-block
     cleanup/unwinding edge invariant (`evalLoweredTerminator_goto_cleanup_invariant`), and the
     refinement theorems `evalLoweredTerminator_refines_trusted` /
     `runLoweredCfgSteps_refines_trusted` (and their statement-bearing generalizations
     `evalLoweredTerminator_at_end_refines_trusted` /
     `runLoweredCfgSteps_with_stmts_refines_trusted` under `BodyCorrWithStmts`) against
     Trusted's `evalTerminator` / `stepMirFn` / `stepMirState` (Trusted never faults where Anneal
     succeeds), plus the projected-`Drop` refinement and the documented bare-`Drop` divergence.
   - The value-dependent part of `check_place_access` (`prepare_place_access`) for `Drop` places
     and `Call` destinations is concrete in the evaluator (`placeRuntimeAccessOk`): no `Deref`
     (`evalLoweredTerminator_drop_deref_none`), a live root local and readable `Index` operand
     locals (`placeFrameAccessOk`, `placeFrameAccessOk_of_evalDeinitPlace`), and the runtime
     value/shell projection check `check_slot_projection` (`checkSlotProjectionOk` /
     `checkPlaceSlotOk`, `rvalue.rs:6203, 6531-6856`), which subsumes `deinit_in_slot`'s path
     discipline `slotPlaceProjectionOk` (`checkPlaceSlotOk_of_slotPlaceProjectionOk`), rejects
     inactive `Downcast` variants (`evalLoweredTerminator_drop_inactive_variant_none`) and
     out-of-bounds elements of initialized arrays (`evalLoweredTerminator_drop_index_oob_none`,
     `checkPlaceSlotOk_array_index_eq`), and accepts any path below an uninitialized local
     (`checkPlaceSlotOk_uninit`); only the type-directed part (declared place type,
     `validate_projection_tail`) stays the environment's `CfgEnv.placeAccessOk`. Hence a `Drop`
     of a dead local faults in both semantics (`evalLoweredTerminator_drop_dead_agrees_trusted`),
     a successful `Drop` names a local Trusted also holds live
     (`evalLoweredTerminator_drop_trusted_live`), a successful projected `Drop` of an initialized
     local refines Trusted without any read premise
     (`evalLoweredTerminator_drop_projected_init_refines`), and a projected `Drop` below an
     uninitialized local is a documented divergence
     (`evalLoweredTerminator_drop_projected_uninit_divergence`).

4. **Section 4 — Synthetic sub-place pointers, `ProjectionElem.deref` places, and sub-place
   `CopyNonOverlapping`** (`ws-mir-lower-deref-subplace-and-minirust-adt-deinit` Episode 1,
   `rvalue.rs:8789-11129`):
   - `localBaseAddr` (`local_base_addr_for_decls`): the legacy `(local + 1) * 0x1000` whenever
     the preceding locals fit in a page (`localBaseAddr_small`), page-rounded strides and
     over-alignment for larger locals, failing closed without masking (`localBaseAddr_fits`,
     `localBaseAddr_example_overflow_none`), collision-free allocations of distinct locals
     (`localBaseAddr_disjoint`, `localBaseAddr_example_two_page_local`), and alignment
     (`localBaseAddr_page_dvd`, `localBaseAddr_align_dvd`, `localBaseAddr_aligned`).
   - Layout-offset sub-places (`subplaceAt`, `computeSubplaceByteOffset`: `Field`, forward
     `ConstantIndex`, `Downcast`) that stay inside their container and are disjoint for distinct
     siblings (`subplaceAt_sub`, `subplaceAt_disjoint_siblings`) and agree with Section 2e's
     `pathRange` (`subplaceAt_of_pathRange`); synthetic borrows `&_l.proj` / `&raw _l.proj`
     (`evalSubplaceRef`, `evalSubplaceRef_inbounds`, `evalSubplaceRef_disjoint_locals`,
     `evalSubplaceRef_disjoint_siblings`, `evalSubplaceRef_dead`); and reborrows
     `&((*p).tail)` / `&raw ((*p).tail)` (`evalReborrowTail`: resolved sub-place results
     (`evalReborrowTail_resolved_ok`), alignment and liveness for references, address-only raw
     reborrows valid at offset `0` on null, dangling, or provenance-free pointers
     (`evalReborrowTail_raw_null_zero`, `evalReborrowTail_raw_dangling`,
     `evalReborrowTail_ref_null`, `evalReborrowTail_ref_misaligned`, `evalReborrowTail_ref_dead`),
     and the in-bounds `offset_inbounds` fallback of an unresolvable raw base, whose result
     carries its target local's provenance re-tagged by `reborrowFallbackTag`
     (`evalReborrowTail_raw_inbounds_fallback_ok`; untagged for a unique candidate:
     `evalReborrowTail_raw_inbounds_fallback_unique_tag`, `reborrowFallbackTag_unique`,
     `reborrowFallbackTag_decoded`, `reborrowFallbackTag_stale`)).
   - No-guess resolution `resolveSyntheticSubplace` (`resolve_synthetic_subplace_in` /
     `select_subplace_candidate_in`): fault characterizations (`resolveSyntheticSubplace_null`,
     `_misaligned`, `_rangeOverflow`, `_dead`, `_no_provenance`), soundness
     (`resolveSyntheticSubplace_sound`), no guessing (`selectSubplaceCandidate_no_guess`,
     `selectSubplaceCandidate_ambiguous_none`), the borrow/`Deref` round trip
     (`resolveSyntheticSubplace_evalSubplaceRef`), and stability under writes
     (`resolveSyntheticSubplace_stable`).
   - `Deref` places (`derefTarget`, `resolvePlace`): `evalDerefPlaceRead`, `evalDerefPlaceWrite`
     (`PartialShell` field initialization and sibling preservation through `writePlaceState`),
     `evalDerefPlaceDeinit`, `evalDerefOperand` (Move-Deref Non-Deinit:
     `evalDerefOperand_move_deref`, `evalDerefOperand_move_deref_slots`, refining Trusted's
     `move` through `Deref`, which Trusted also evaluates as a frame-preserving read:
     `evalOperand_move_deref_eq_copy`, `evalRvalue_use_move_deref_eq_copy`,
     `evalDerefOperand_move_refines_evalOperand` and its typed / projected-typed variants,
     `evalDerefPlaceRead_refines_evalRvalue_move`,
     `evalDerefPlaceRead_refines_evalRvalue_typed_proj_move`,
     `witness_trusted_deref_move_proj_typed`), two-level chains `(**_pp).rest` resolved through
     the intermediate pointer exactly as runtime MIR's `CopyForDeref` split through a temporary
     (`resolvePlace_deref_deref_split`, `evalDerefPlaceRead_deref_deref`,
     `witness_deref_deref_split`), `evalRetagDerefPlace`
     and dangling sub-place references (`retag_subplace_ref_dead_local`), with Get-Put, Put-Get,
     and frame laws (`writePlaceState_get_put_init`, `writePlaceState_put_get_init`,
     `evalDerefPlaceWrite_get_put`, `evalDerefPlaceWrite_put_get`, `evalDerefPlaceWrite_frame`,
     `evalDerefPlaceWrite_read_sibling`, `evalDerefPlaceDeinit_target`) and step refinement of
     Trusted: reads in Trusted's untyped mode (`evalDerefPlaceRead_refines_evalOperand`,
     `evalDerefPlaceRead_refines_evalRvalue`) and scalar reads of `*_p` in its typed mode
     (non-empty `localDecls`, read through `evalStackThinPtrTypedDerefRead`:
     `evalDerefPlaceRead_refines_evalOperand_typed`, `evalDerefPlaceRead_refines_evalRvalue_typed`,
     whose extra hypotheses are Trusted's pointee-type checks — scalar width, offset `0`, target
     alignment, no union, bit validity — while Trusted's read value is derived from Anneal's;
     `evalRvalue_use_copy_of_evalOperand` lifts `evalOperand` to `Rvalue.use`), writes in untyped
     and typed modes (`evalDerefPlaceWrite_refines_writePlaceValue`,
     `evalDerefPlaceWrite_refines_writePlaceValue_typed`), and assignments in untyped and typed
     modes (`evalStmt_assign_deref_refines`, `evalStmt_assign_deref_refines_typed`).
   - Sub-place and array-window `CopyNonOverlapping` (`evalCopyNonOverlappingSubplace`,
     `readSubplaceSlot`, `writeSubplaceSlot`): Read-After-Copy
     (`evalCopyNonOverlappingSubplace_read_after_copy`,
     `evalCopyNonOverlappingSubplace_window_read_after_copy`), Disjoint-Frame for every copy shape
     (`evalCopyNonOverlappingSubplace_frame`, `writeSubplaceSlot_frame`), self-overlap rejection
     (`evalCopyNonOverlappingSubplace_overlap_none`), dead-provenance faults and zero-byte bulk
     no-ops (`evalCopyNonOverlappingSubplace_dead_none`,
     `evalCopyNonOverlappingSubplace_zst_bulk_noop`), `[T; 1]` / `[[T; 1]; 1]` deinitialization
     and promotion (`writeSubplaceSlot_uninit_unit_array`, `writeSubplaceSlot_uninit_nested_unit_array`,
     `writeSubplaceSlot_init_nested_unit_array`), fail-closed uninitialized element and subslice
     writes (`writeSubplaceSlot_uninit_elem_init_array_none`,
     `writeSubplaceSlot_uninit_subslice_init_array_none`), `PartialShell` field copy
     (`writeSubplaceSlot_nested_field_ok`), and refinement of Trusted's `evalCopySingleDirect`,
     `evalCopyNonOverlappingPermOk`, and `evalStmt` for both `count = 1` sub-place copies and
     `count ≥ 2` array-window copies (`evalCopyNonOverlappingSubplace_refines`,
     `evalStmt_copyNonOverlapping_singleDirect`, `evalStmt_copyNonOverlapping_subplace_refines`,
     `evalCopyNonOverlappingSubplace_window_refines`,
     `evalStmt_copyNonOverlapping_window_refines`).
   - A concrete frame `(u32, u32)` + `*mut u32` exercising the whole pipeline (`witnessCtx_wf`,
     `witness_borrow`, `witness_resolve`, `witness_deref_read`, `witness_deref_write_put_get`,
     `witness_bases`), and the same frame under Trusted's pointer representation discharging
     every hypothesis of the `Deref` and array-window refinements (`witnessCtxT_wf`,
     `witness_trusted_resolve`, `witness_trusted_deref_read`, `witness_trusted_deref_read_typed`,
     `witness_trusted_deref_write_typed`, `witness_trusted_window_copy`, plus
     `witness_tag_disambiguates_and_rejects_mismatch` and `witness_window_copy`).
-/

/-! ## Section 1: `ScalarValidRange` Niches -/

/-- Valid range of a scalar's bit pattern (`ScalarValidRange` in `crates/anneal-mir/src/ir.rs`,
`rustc`'s `WrappingRange`): `start..=end_`, wrapping around the scalar's modulus when
`start > end_`. -/
structure ScalarValidRange : Type where
  /-- First valid bit pattern. -/
  start : Nat
  /-- Last valid bit pattern (inclusive; below `start` for a wrapping range). -/
  end_ : Nat
  deriving DecidableEq, Repr

namespace ScalarValidRange

/-- `ScalarValidRange::contains(bits, bit_width)`: `bits` must fit in `bitWidth` bits
(`bits <= width_mask(bit_width)`, i.e. `bits < 2 ^ bitWidth`), and then lie in
`start..=end_` (non-wrapping, `start <= end_`) or in `start..` / `..=end_` (wrapping,
`start > end_`). -/
def contains (r : ScalarValidRange) (bits bitWidth : Nat) : Bool :=
  if bits < 2 ^ bitWidth then
    if r.start ≤ r.end_ then decide (r.start ≤ bits ∧ bits ≤ r.end_)
    else decide (r.start ≤ bits ∨ bits ≤ r.end_)
  else false

/-- `ScalarValidRange::full(bit_width)`: `0..=width_mask(bit_width)` (no niche). -/
def full (bitWidth : Nat) : ScalarValidRange := ⟨0, 2 ^ bitWidth - 1⟩

/-- `ScalarValidRange::non_zero(bit_width)`: `1..=width_mask(bit_width)` (the
`NonZero<T>` / `NonNull<T>` niche). -/
def nonZero (bitWidth : Nat) : ScalarValidRange := ⟨1, 2 ^ bitWidth - 1⟩

/-- `ScalarValidRange::is_wrapping`: `start > end_`. -/
def isWrapping (r : ScalarValidRange) : Bool := decide (r.end_ < r.start)

/-- `ScalarValidRange::is_empty(bit_width)`: only a non-wrapping range whose `start`
exceeds the width (`start > width_mask`, i.e. `2 ^ bitWidth ≤ start`) is empty. -/
def isEmpty (r : ScalarValidRange) (bitWidth : Nat) : Bool :=
  decide (r.start ≤ r.end_ ∧ 2 ^ bitWidth ≤ r.start)

/-- `ScalarValidRange::is_full(bit_width)`: every `bitWidth`-bit pattern is contained. -/
def isFull (r : ScalarValidRange) (bitWidth : Nat) : Bool :=
  if r.start ≤ r.end_ then decide (r.start = 0 ∧ 2 ^ bitWidth - 1 ≤ r.end_)
  else decide (2 ^ bitWidth - 1 ≤ r.end_ ∨ r.start = r.end_ + 1)

/-- A range exposes a niche (`contains_niche` for a scalar-valid-range ADT) iff it is not
full. -/
def containsNiche (r : ScalarValidRange) (bitWidth : Nat) : Bool := !r.isFull bitWidth

/-- The Trusted `WrappingRange` with the same bounds. -/
def toWrappingRange (r : ScalarValidRange) : WrappingRange := ⟨r.start, r.end_⟩

/-- The complement of a non-wrapping range `start..=end_` (`0 < start`) inside the
`bitWidth`-bit patterns: the wrapping range `(end_ + 1)..=(start - 1)`. -/
def complement (r : ScalarValidRange) : ScalarValidRange := ⟨r.end_ + 1, r.start - 1⟩

/-- Characterization of `contains` as a proposition. -/
theorem contains_eq_true_iff (r : ScalarValidRange) (bits bitWidth : Nat) :
    r.contains bits bitWidth = true ↔
      bits < 2 ^ bitWidth ∧
        ((r.start ≤ r.end_ ∧ r.start ≤ bits ∧ bits ≤ r.end_) ∨
          (r.end_ < r.start ∧ (r.start ≤ bits ∨ bits ≤ r.end_))) := by
  unfold contains
  by_cases hLt : bits < 2 ^ bitWidth
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hLt)]
    by_cases hLe : r.start ≤ r.end_
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hLe), decide_eq_true_iff]
      constructor
      · intro h; exact ⟨hLt, Or.inl ⟨hLe, h⟩⟩
      · rintro ⟨_, (⟨_, h⟩ | ⟨h, _⟩)⟩
        · exact h
        · exact absurd hLe (Nat.not_le.mpr h)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hLe), decide_eq_true_iff]
      constructor
      · intro h; exact ⟨hLt, Or.inr ⟨Nat.lt_of_not_le hLe, h⟩⟩
      · rintro ⟨_, (⟨h, _⟩ | ⟨_, h⟩)⟩
        · exact absurd h hLe
        · exact h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hLt)]
    constructor
    · intro h; exact absurd h Bool.false_ne_true
    · rintro ⟨h, _⟩; exact absurd h hLt

/-- **Width-bound soundness**: a contained bit pattern fits in `bitWidth` bits. -/
theorem contains_lt_pow {r : ScalarValidRange} {bits bitWidth : Nat}
    (h : r.contains bits bitWidth = true) : bits < 2 ^ bitWidth :=
  ((contains_eq_true_iff r bits bitWidth).mp h).1

/-- **Exact agreement with Trusted**: `contains` is the width bound conjoined with Trusted's
`wrappingRangeContains` (`rustc_abi::WrappingRange::contains`), which `ScalarLayout.initialized`
validity checks in `Trusted.Rustc.V2026_06_01.MirSemantics.Bytes` use. -/
theorem contains_eq_wrappingRangeContains (r : ScalarValidRange) (bits bitWidth : Nat) :
    r.contains bits bitWidth =
      (decide (bits < 2 ^ bitWidth) && wrappingRangeContains r.toWrappingRange bits) := by
  apply Bool.eq_iff_iff.mpr
  rw [contains_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
  unfold wrappingRangeContains toWrappingRange
  dsimp only
  by_cases hLe : r.start ≤ r.end_
  · have hB : Nat.ble r.start r.end_ = true := Nat.ble_eq.mpr hLe
    rw [hB]
    simp only [Bool.and_eq_true, Nat.ble_eq]
    constructor
    · rintro ⟨hLt, (⟨_, h1, h2⟩ | ⟨h3, _⟩)⟩
      · exact ⟨hLt, h1, h2⟩
      · exact absurd hLe (Nat.not_le.mpr h3)
    · rintro ⟨hLt, h1, h2⟩
      exact ⟨hLt, Or.inl ⟨hLe, h1, h2⟩⟩
  · have hB : Nat.ble r.start r.end_ = false := by
      cases h : Nat.ble r.start r.end_ with
      | false => rfl
      | true => exact absurd (Nat.ble_eq.mp h) hLe
    rw [hB]
    simp only [Bool.or_eq_true, Nat.ble_eq]
    constructor
    · rintro ⟨hLt, (⟨h1, _, _⟩ | ⟨_, h3⟩)⟩
      · exact absurd h1 hLe
      · exact ⟨hLt, h3⟩
    · rintro ⟨hLt, h⟩
      exact ⟨hLt, Or.inr ⟨Nat.lt_of_not_le hLe, h⟩⟩

/-- **`full` completeness**: every `bitWidth`-bit pattern is in `full bitWidth`. -/
theorem full_contains {bits bitWidth : Nat} (h : bits < 2 ^ bitWidth) :
    (full bitWidth).contains bits bitWidth = true := by
  rw [contains_eq_true_iff]
  refine ⟨h, Or.inl ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩⟩
  show bits ≤ 2 ^ bitWidth - 1
  omega

/-- `full bitWidth` contains exactly the `bitWidth`-bit patterns. -/
theorem full_contains_iff (bits bitWidth : Nat) :
    (full bitWidth).contains bits bitWidth = true ↔ bits < 2 ^ bitWidth :=
  ⟨contains_lt_pow, full_contains⟩

/-- **`nonZero` characterization**: for a positive width, `nonZero w` contains exactly the
non-zero `w`-bit patterns (the `NonZero<T>` niche excludes only `0`). -/
theorem nonZero_contains_iff {bits bitWidth : Nat} (hW : 0 < bitWidth) :
    (nonZero bitWidth).contains bits bitWidth = true ↔ 0 < bits ∧ bits < 2 ^ bitWidth := by
  have hPow : 2 ≤ 2 ^ bitWidth := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by decide) hW
    rw [Nat.pow_one] at h
    exact h
  rw [contains_eq_true_iff]
  show (bits < 2 ^ bitWidth ∧
      ((1 ≤ 2 ^ bitWidth - 1 ∧ 1 ≤ bits ∧ bits ≤ 2 ^ bitWidth - 1) ∨
        (2 ^ bitWidth - 1 < 1 ∧ (1 ≤ bits ∨ bits ≤ 2 ^ bitWidth - 1)))) ↔ _
  constructor
  · rintro ⟨hLt, (⟨_, h1, _⟩ | ⟨hBad, _⟩)⟩
    · exact ⟨h1, hLt⟩
    · omega
  · rintro ⟨hPos, hLt⟩
    exact ⟨hLt, Or.inl ⟨by omega, hPos, by omega⟩⟩

/-- For a positive width, `nonZero w` never contains `0`. (At width `0`, `nonZero 0 =
1..=0` is a wrapping range containing the only `0`-bit pattern, as in `crates/anneal-mir`.) -/
theorem nonZero_not_contains_zero {bitWidth : Nat} (hW : 0 < bitWidth) :
    (nonZero bitWidth).contains 0 bitWidth = false := by
  cases h : (nonZero bitWidth).contains 0 bitWidth with
  | false => rfl
  | true =>
    have h' := ((nonZero_contains_iff hW).mp h).1
    exact absurd h' (Nat.lt_irrefl 0)

/-- **Emptiness characterization**: `isEmpty` holds iff no bit pattern is contained. -/
theorem isEmpty_iff_forall_not_contains (r : ScalarValidRange) (bitWidth : Nat) :
    r.isEmpty bitWidth = true ↔ ∀ bits, r.contains bits bitWidth = false := by
  unfold isEmpty
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨hLe, hBig⟩ bits
    cases h : r.contains bits bitWidth with
    | false => rfl
    | true =>
      rw [contains_eq_true_iff] at h
      omega
  · intro hAll
    have hPos : 0 < 2 ^ bitWidth := Nat.two_pow_pos bitWidth
    by_cases hLe : r.start ≤ r.end_
    · refine ⟨hLe, ?_⟩
      apply Classical.byContradiction
      intro hSmall
      have hTrue : r.contains r.start bitWidth = true := by
        rw [contains_eq_true_iff]
        exact ⟨by omega, Or.inl ⟨hLe, Nat.le_refl _, hLe⟩⟩
      rw [hAll r.start] at hTrue
      nomatch hTrue
    · have hTrue : r.contains 0 bitWidth = true := by
        rw [contains_eq_true_iff]
        exact ⟨hPos, Or.inr ⟨by omega, Or.inr (Nat.zero_le _)⟩⟩
      rw [hAll 0] at hTrue
      nomatch hTrue

/-- A wrapping range always contains the zero bit pattern. -/
theorem isWrapping_contains_zero {r : ScalarValidRange} (bitWidth : Nat)
    (h : r.isWrapping = true) : r.contains 0 bitWidth = true := by
  unfold isWrapping at h
  have hGt : r.end_ < r.start := of_decide_eq_true h
  rw [contains_eq_true_iff]
  exact ⟨Nat.two_pow_pos bitWidth, Or.inr ⟨hGt, Or.inr (Nat.zero_le _)⟩⟩

/-- **Fullness characterization**: `isFull` holds iff every `bitWidth`-bit pattern is
contained. -/
theorem isFull_iff_forall_contains (r : ScalarValidRange) (bitWidth : Nat) :
    r.isFull bitWidth = true ↔ ∀ bits, bits < 2 ^ bitWidth → r.contains bits bitWidth = true := by
  have hPos : 0 < 2 ^ bitWidth := Nat.two_pow_pos bitWidth
  unfold isFull
  by_cases hLe : r.start ≤ r.end_
  · simp only [hLe, ↓reduceIte, decide_eq_true_iff]
    constructor
    · rintro ⟨h0, hEnd⟩ bits hLt
      rw [contains_eq_true_iff]
      exact ⟨hLt, Or.inl ⟨hLe, by omega, by omega⟩⟩
    · intro hAll
      have h0 := (contains_eq_true_iff r 0 bitWidth).mp (hAll 0 hPos)
      have hMax := (contains_eq_true_iff r (2 ^ bitWidth - 1) bitWidth).mp
        (hAll (2 ^ bitWidth - 1) (by omega))
      omega
  · simp only [hLe, ↓reduceIte, decide_eq_true_iff]
    constructor
    · rintro hCase bits hLt
      rw [contains_eq_true_iff]
      omega
    · intro hAll
      by_cases hEnd : 2 ^ bitWidth - 1 ≤ r.end_
      · exact Or.inl hEnd
      · right
        apply Classical.byContradiction
        intro hAdj
        -- `end_ + 1` lies strictly between `end_` and `start` and inside the width.
        have h := (contains_eq_true_iff r (r.end_ + 1) bitWidth).mp
          (hAll (r.end_ + 1) (by omega))
        omega

/-- **Niche characterization**: a range exposes a niche iff some `bitWidth`-bit pattern is
excluded. -/
theorem containsNiche_iff_exists_excluded (r : ScalarValidRange) (bitWidth : Nat) :
    r.containsNiche bitWidth = true ↔
      ∃ bits, bits < 2 ^ bitWidth ∧ r.contains bits bitWidth = false := by
  unfold containsNiche
  constructor
  · intro h
    have hNotFull : r.isFull bitWidth = false := by
      cases hF : r.isFull bitWidth with
      | false => rfl
      | true => rw [hF] at h; nomatch h
    apply Classical.byContradiction
    intro hNo
    have hAll : ∀ bits, bits < 2 ^ bitWidth → r.contains bits bitWidth = true := by
      intro bits hLt
      cases hC : r.contains bits bitWidth with
      | true => rfl
      | false => exact absurd ⟨bits, hLt, hC⟩ hNo
    rw [(isFull_iff_forall_contains r bitWidth).mpr hAll] at hNotFull
    nomatch hNotFull
  · rintro ⟨bits, hLt, hC⟩
    cases hF : r.isFull bitWidth with
    | false => rfl
    | true =>
      have h := (isFull_iff_forall_contains r bitWidth).mp hF bits hLt
      rw [hC] at h
      nomatch h

/-- `NonZero<T>`-style ranges expose a niche (the `0` pattern). -/
theorem nonZero_containsNiche {bitWidth : Nat} (hW : 0 < bitWidth) :
    (nonZero bitWidth).containsNiche bitWidth = true :=
  (containsNiche_iff_exists_excluded _ _).mpr
    ⟨0, Nat.two_pow_pos bitWidth, nonZero_not_contains_zero hW⟩

/-- **Wrapping/non-wrapping partition**: for a non-wrapping range `start..=end_` with
`0 < start`, the wrapping range `complement r = (end_ + 1)..=(start - 1)` contains exactly
the `bitWidth`-bit patterns that `r` excludes. -/
theorem complement_contains {r : ScalarValidRange} {bitWidth : Nat}
    (hLe : r.start ≤ r.end_) (hStart : 0 < r.start)
    (bits : Nat) (hLt : bits < 2 ^ bitWidth) :
    r.complement.contains bits bitWidth = !r.contains bits bitWidth := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.not_eq_true', contains_eq_true_iff]
  constructor
  · intro hC
    cases hR : r.contains bits bitWidth with
    | false => rfl
    | true =>
      rw [contains_eq_true_iff] at hR
      simp only [complement] at hC
      omega
  · intro hNot
    have hNot' : ¬ (r.start ≤ bits ∧ bits ≤ r.end_) := by
      intro ⟨h1, h2⟩
      apply Bool.false_ne_true
      rw [← hNot, contains_eq_true_iff]
      exact ⟨hLt, Or.inl ⟨hLe, h1, h2⟩⟩
    simp only [complement]
    omega

end ScalarValidRange

/-! ## Section 1b: ADT Layout Specifications, `resolveAdtOffsetOf`, and Offset Bounds -/

/-- Exact size and ABI alignment of a field type (`TyLayout` in `crates/anneal-mir/src/ir.rs`). -/
structure FieldLayout : Type where
  /-- Size in bytes. -/
  size : Nat
  /-- ABI alignment in bytes. -/
  align : Nat
  deriving DecidableEq, Repr

/-- A 1-ZST (size `0`, alignment `1`), which `#[repr(transparent)]` ignores. -/
def FieldLayout.isOneZst (f : FieldLayout) : Bool := f.size == 0 && f.align == 1

/-- Primary `#[repr(...)]` of an ADT (`AdtReprKind` in `ir.rs`). -/
inductive AdtReprKind : Type where
  | rust
  | c
  | transparent
  deriving DecidableEq, Repr

/-- Layout-relevant shape of an ADT (the decision `AdtDef::layout_info` takes in `ir.rs`):
- `struct fields` / `union fields`;
- `taggedEnum tagSize variants`: an explicit integer tag (`#[repr(Int)]` when the `repr` is
  `rust`, `#[repr(C, Int)]` when it is `c`);
- `univariantEnum present variants`: a tagless, non-`#[repr(C)]` enum whose only present
  variant is `present` (every other variant is *absent*: an uninhabited 1-ZST variant,
  `AdtDef::univariant_index`), laid out like a struct of `present`'s fields without a tag;
- `noPresentEnum variants`: an enum without variants or with only absent ones (laid out like
  `!`; `E0084` rejects zero-variant enums with a non-`Rust` repr or `repr(align)`);
- `unspecifiedEnum variants`: a tagless `#[repr(C)]` enum (C `int` tag of target-dependent size)
  or a tagless enum with several present variants (`rustc` niche/tag optimizations), whose
  layout the model leaves unspecified (`LayoutError::Unspecified`). -/
inductive AdtShape : Type where
  | struct (fields : List FieldLayout)
  | union (fields : List FieldLayout)
  | taggedEnum (tagSize : Nat) (variants : List (List FieldLayout))
  | univariantEnum (present : Nat) (variants : List (List FieldLayout))
  | noPresentEnum (variants : List (List FieldLayout))
  | unspecifiedEnum (variants : List (List FieldLayout))

/-- An ADT layout specification (`AdtDef` with its fields' layouts resolved). -/
structure AdtLayoutSpec : Type where
  /-- Layout-relevant shape. -/
  shape : AdtShape
  /-- Primary representation. -/
  repr : AdtReprKind
  /-- `#[repr(align(N))]`, if any. -/
  reprAlign : Option Nat
  /-- For `#[repr(Rust)]` field lists: whether declaration order is the order `rustc`
  keeps (the sortedness and niche-freedom conditions of `Ty::has_canonical_byte_layout`,
  which depend on field types); the padding-freedom condition is checked by
  `paddingFree`. -/
  rustOrderCanonical : Bool

/-- Maximum of `base` and the fields' alignments. -/
def maxAlign (base : Nat) : List FieldLayout → Nat
  | [] => base
  | f :: fs => maxAlign (max base f.align) fs

/-- Sum of the fields' sizes. -/
def sumSizes : List FieldLayout → Nat
  | [] => 0
  | f :: fs => f.size + sumSizes fs

/-- Maximum field size (`0` for no fields). -/
def maxSize : List FieldLayout → Nat
  | [] => 0
  | f :: fs => max f.size (maxSize fs)

/-- Maximum of a list of naturals (`0` for the empty list). -/
def maxList : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxList xs)

/-- End offset of a `#[repr(C)]` field sequence starting at `start`: each field is placed at
the next multiple of its alignment. -/
def cEnd (start : Nat) : List FieldLayout → Nat
  | [] => start
  | f :: fs => cEnd (PlaceAndRvalue.alignUp start f.align + f.size) fs

/-- Offset of field `i` of a `#[repr(C)]` field sequence starting at `start`
(`struct_like_field_offset` with `AdtReprKind::C`). -/
def cOffset? (start : Nat) : List FieldLayout → Nat → Option Nat
  | [], _ => none
  | f :: _, 0 => some (PlaceAndRvalue.alignUp start f.align)
  | f :: fs, i + 1 => cOffset? (PlaceAndRvalue.alignUp start f.align + f.size) fs i

/-- Declaration order starting at `start` has no padding: every field's prefix-sum offset is a
multiple of its alignment (`Ty::has_canonical_byte_layout`'s padding condition). -/
def paddingFree (start : Nat) : List FieldLayout → Bool
  | [] => true
  | f :: fs => (start % f.align == 0) && paddingFree (start + f.size) fs

/-- Declaration-order prefix-sum offset of field `i` starting at `start` (`rust_field_offset`). -/
def rustOffset? (start : Nat) : List FieldLayout → Nat → Option Nat
  | [], _ => none
  | _ :: _, 0 => some start
  | f :: fs, i + 1 => rustOffset? (start + f.size) fs i

/-- The fields that are not 1-ZSTs. -/
def nonOneZstFields (fs : List FieldLayout) : List FieldLayout :=
  fs.filter (fun f => !f.isOneZst)

/-- Maximum of `base` and every field alignment of every variant. -/
def variantsAlign (base : Nat) : List (List FieldLayout) → Nat
  | [] => base
  | v :: vs => variantsAlign (maxAlign base v) vs

/-- Layout `(size, align)` of a struct-like field list (`struct_like_layout`): `#[repr(C)]`
and `#[repr(Rust)]` round the (padded resp. minimal) field extent up to the alignment;
`#[repr(transparent)]` has the layout of its unique non-1-ZST field (`E0690` for several,
`E0692` with `repr(align)`). -/
def structLayout? (repr : AdtReprKind) (reprAlign : Option Nat) (fs : List FieldLayout) :
    Option (Nat × Nat) :=
  match repr with
  | .c =>
    let a := maxAlign (reprAlign.getD 1) fs
    some (PlaceAndRvalue.alignUp (cEnd 0 fs) a, a)
  | .rust =>
    let a := maxAlign (reprAlign.getD 1) fs
    some (PlaceAndRvalue.alignUp (sumSizes fs) a, a)
  | .transparent =>
    match reprAlign, nonOneZstFields fs with
    | some _, _ => none
    | none, [] => some (0, 1)
    | none, [f] => some (f.size, f.align)
    | none, _ :: _ :: _ => none

/-- Offset of field `i` of a struct-like field list (`struct_like_field_offset`):
`#[repr(C)]` declaration-order padded offsets; `#[repr(Rust)]` prefix sums when declaration
order is canonical and padding-free; `#[repr(transparent)]` places its non-1-ZST field (and,
when every field is zero-sized, all fields) at `0` and other 1-ZSTs like `#[repr(Rust)]`. -/
def structFieldOffset? (repr : AdtReprKind) (rustCanon : Bool) (fs : List FieldLayout) (i : Nat) :
    Option Nat :=
  match repr with
  | .c => cOffset? 0 fs i
  | .rust => if rustCanon && paddingFree 0 fs then rustOffset? 0 fs i else none
  | .transparent =>
    match fs[i]? with
    | none => none
    | some f =>
      if !f.isOneZst then some 0
      else if fs.all (fun g => g.size == 0) then some 0
      else if rustCanon && paddingFree 0 fs then rustOffset? 0 fs i
      else none

/-- Layout of a union: at least one field (`E0784`), all at offset `0`; alignment the `max` of
the field and `repr(align)` alignments, size the largest field rounded up to it. -/
def unionLayout? (repr : AdtReprKind) (reprAlign : Option Nat) (fs : List FieldLayout) :
    Option (Nat × Nat) :=
  match fs with
  | [] => none
  | _ :: _ =>
    if repr = .transparent ∧ (reprAlign.isSome ∨ 1 < (nonOneZstFields fs).length) then none
    else
      let a := maxAlign (reprAlign.getD 1) fs
      some (PlaceAndRvalue.alignUp (maxSize fs) a, a)

/-- Alignment of the `#[repr(C, Int)]` payload union (the `max` variant struct alignment). -/
def payloadAlign (vs : List (List FieldLayout)) : Nat := variantsAlign 1 vs

/-- Offset of the `#[repr(C, Int)]` payload union after a tag of `tagSize` bytes. -/
def payloadOffset (tagSize : Nat) (vs : List (List FieldLayout)) : Nat :=
  PlaceAndRvalue.alignUp tagSize (payloadAlign vs)

/-- Layout of an explicit-tag enum (`tagged_layout`): `#[repr(Int)]` is a `#[repr(C)]` union of
one `#[repr(C)]` struct `(tag, fields...)` per variant; `#[repr(C, Int)]` is a `#[repr(C)]`
struct `(tag, payload)` whose payload is a `#[repr(C)]` union of the variants' field structs. -/
def taggedLayout? (repr : AdtReprKind) (reprAlign : Option Nat) (tagSize : Nat)
    (vs : List (List FieldLayout)) : Option (Nat × Nat) :=
  match repr with
  | .transparent => none
  | .rust =>
    let a := variantsAlign (max (reprAlign.getD 1) tagSize) vs
    let size := maxList (vs.map (fun v => PlaceAndRvalue.alignUp (cEnd tagSize v) (maxAlign tagSize v)))
    some (PlaceAndRvalue.alignUp size a, a)
  | .c =>
    let pa := payloadAlign vs
    let ps := maxList (vs.map (fun v => PlaceAndRvalue.alignUp (cEnd 0 v) (maxAlign 1 v)))
    let a := max (max (reprAlign.getD 1) tagSize) pa
    some (PlaceAndRvalue.alignUp (payloadOffset tagSize vs + PlaceAndRvalue.alignUp ps pa) a, a)

/-- Field offset inside an explicit-tag enum (`AdtDef::field_offset`). -/
def taggedFieldOffset? (repr : AdtReprKind) (tagSize : Nat) (vs : List (List FieldLayout))
    (v i : Nat) : Option Nat :=
  match vs[v]? with
  | none => none
  | some fs =>
    match repr with
    | .transparent => none
    | .rust => cOffset? tagSize fs i
    | .c => (cOffset? 0 fs i).map (fun inner => payloadOffset tagSize vs + inner)

/-- Offset `0` of field `i` of an absent variant's (1-ZST) field list. -/
def absentFieldOffset? (fs : List FieldLayout) (i : Nat) : Option Nat :=
  if i < fs.length then some 0 else none

/-- Layout `(size, align)` of an ADT (`AdtDef::layout_info` restricted to exact layouts). -/
def adtLayout? (spec : AdtLayoutSpec) : Option (Nat × Nat) :=
  match spec.shape with
  | .struct fs => structLayout? spec.repr spec.reprAlign fs
  | .union fs => unionLayout? spec.repr spec.reprAlign fs
  | .taggedEnum tagSize vs => taggedLayout? spec.repr spec.reprAlign tagSize vs
  | .univariantEnum present vs =>
    match vs[present]? with
    | none => none
    | some fs => if spec.repr = .c then none else structLayout? spec.repr spec.reprAlign fs
  | .noPresentEnum vs =>
    match spec.repr with
    | .c => none
    | .transparent => if vs.length = 1 ∧ spec.reprAlign = none then some (0, 1) else none
    | .rust => if vs = [] ∧ spec.reprAlign.isSome then none else some (0, 1)
  | .unspecifiedEnum _ => none

/-- Field types (layouts) of variant `v` (`AdtDef::variant_fields`). -/
def variantFields (spec : AdtLayoutSpec) (v : Nat) : Option (List FieldLayout) :=
  match spec.shape with
  | .struct fs | .union fs => if v = 0 then some fs else none
  | .taggedEnum _ vs | .univariantEnum _ vs | .noPresentEnum vs | .unspecifiedEnum vs => vs[v]?

/-- `AdtDef::field_offset(variant_idx, field_idx)`: the byte offset of field `i` of variant `v`,
or `none` when the layout is ill-formed or unspecified (`resolve_offset_of`'s ADT step). -/
def resolveAdtOffsetOf (spec : AdtLayoutSpec) (v i : Nat) : Option Nat :=
  match adtLayout? spec with
  | none => none
  | some _ =>
    match spec.shape with
    | .struct fs => if v = 0 then structFieldOffset? spec.repr spec.rustOrderCanonical fs i else none
    | .union fs => if v = 0 ∧ i < fs.length then some 0 else none
    | .taggedEnum tagSize vs => taggedFieldOffset? spec.repr tagSize vs v i
    | .univariantEnum present vs =>
      match vs[v]? with
      | none => none
      | some fs =>
        if v = present then structFieldOffset? spec.repr spec.rustOrderCanonical fs i
        else absentFieldOffset? fs i
    | .noPresentEnum vs =>
      match vs[v]? with
      | none => none
      | some fs => absentFieldOffset? fs i
    | .unspecifiedEnum _ => none

/-- `n` is a power of two (every alignment in `rustc`'s layout model). -/
def IsPow2 (n : Nat) : Prop := ∃ k, n = 2 ^ k

/-- Every field of every variant of a shape. -/
def AdtShape.allFields : AdtShape → List FieldLayout
  | .struct fs | .union fs => fs
  | .taggedEnum _ vs | .univariantEnum _ vs | .noPresentEnum vs | .unspecifiedEnum vs => vs.flatten

/-- Well-formedness of a layout specification: power-of-two alignments and tag size, and
zero-sized (1-ZST) fields in absent variants (as `AdtDef::is_absent_variant` requires). -/
structure AdtLayoutSpec.WF (spec : AdtLayoutSpec) : Prop where
  fieldAlignPow2 : ∀ f ∈ spec.shape.allFields, IsPow2 f.align
  reprAlignPow2 : ∀ a, spec.reprAlign = some a → IsPow2 a
  tagPow2 : ∀ t vs, spec.shape = .taggedEnum t vs → IsPow2 t
  absentZeroSized : ∀ p vs, spec.shape = .univariantEnum p vs →
    ∀ v fs, vs[v]? = some fs → v ≠ p → ∀ f ∈ fs, f.size = 0
  noPresentZeroSized : ∀ vs, spec.shape = .noPresentEnum vs → ∀ fs ∈ vs, ∀ f ∈ fs, f.size = 0

/-! ### Arithmetic lemmas -/

theorem IsPow2.pos {n : Nat} (h : IsPow2 n) : 0 < n := by
  rcases h with ⟨k, rfl⟩
  exact Nat.two_pow_pos k

theorem IsPow2.dvd_of_le {a b : Nat} (ha : IsPow2 a) (hb : IsPow2 b) (hLe : a ≤ b) : a ∣ b := by
  rcases ha with ⟨i, rfl⟩
  rcases hb with ⟨j, rfl⟩
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide)).mp hLe)

theorem IsPow2.max {a b : Nat} (ha : IsPow2 a) (hb : IsPow2 b) : IsPow2 (max a b) := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.max_eq_right h]; exact hb
  · rw [Nat.max_eq_left h]; exact ha

theorem isPow2_one : IsPow2 1 := ⟨0, rfl⟩

theorem alignUp_dvd (x a : Nat) (hPos : 0 < a) : a ∣ PlaceAndRvalue.alignUp x a :=
  Nat.dvd_of_mod_eq_zero (PlaceAndRvalue.alignUp_mod_eq_zero x a hPos)

theorem le_maxAlign_base : ∀ (base : Nat) (fs : List FieldLayout), base ≤ maxAlign base fs
  | _, [] => Nat.le_refl _
  | base, f :: fs => Nat.le_trans (Nat.le_max_left base f.align) (le_maxAlign_base _ fs)

theorem le_maxAlign_of_mem :
    ∀ (base : Nat) (fs : List FieldLayout) (f : FieldLayout), f ∈ fs → f.align ≤ maxAlign base fs
  | _, [], _, h => nomatch h
  | base, g :: gs, f, h => by
    rcases List.mem_cons.mp h with rfl | hMem
    · exact Nat.le_trans (Nat.le_max_right base f.align) (le_maxAlign_base _ gs)
    · exact le_maxAlign_of_mem _ gs f hMem

theorem maxAlign_pow2 :
    ∀ (base : Nat) (fs : List FieldLayout), IsPow2 base → (∀ f ∈ fs, IsPow2 f.align) →
      IsPow2 (maxAlign base fs)
  | _, [], hb, _ => hb
  | _, f :: fs, hb, hfs =>
    maxAlign_pow2 _ fs (hb.max (hfs f (List.mem_cons_self ..)))
      (fun g hg => hfs g (List.mem_cons_of_mem _ hg))

theorem le_maxSize_of_mem : ∀ (fs : List FieldLayout) (f : FieldLayout), f ∈ fs → f.size ≤ maxSize fs
  | [], _, h => nomatch h
  | g :: gs, f, h => by
    rcases List.mem_cons.mp h with rfl | hMem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_maxSize_of_mem gs f hMem) (Nat.le_max_right _ _)

theorem le_maxList_of_mem : ∀ (xs : List Nat) (x : Nat), x ∈ xs → x ≤ maxList xs
  | [], _, h => nomatch h
  | y :: ys, x, h => by
    rcases List.mem_cons.mp h with rfl | hMem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_maxList_of_mem ys x hMem) (Nat.le_max_right _ _)

theorem le_variantsAlign_base :
    ∀ (base : Nat) (vs : List (List FieldLayout)), base ≤ variantsAlign base vs
  | _, [] => Nat.le_refl _
  | base, v :: vs => Nat.le_trans (le_maxAlign_base base v) (le_variantsAlign_base _ vs)

theorem le_variantsAlign_of_mem :
    ∀ (base : Nat) (vs : List (List FieldLayout)) (fs : List FieldLayout) (f : FieldLayout),
      fs ∈ vs → f ∈ fs → f.align ≤ variantsAlign base vs
  | _, [], _, _, h, _ => nomatch h
  | base, v :: vs, fs, f, hV, hF => by
    rcases List.mem_cons.mp hV with rfl | hMem
    · exact Nat.le_trans (le_maxAlign_of_mem base fs f hF) (le_variantsAlign_base _ vs)
    · exact le_variantsAlign_of_mem _ vs fs f hMem hF

theorem variantsAlign_pow2 :
    ∀ (base : Nat) (vs : List (List FieldLayout)), IsPow2 base →
      (∀ fs ∈ vs, ∀ f ∈ fs, IsPow2 f.align) → IsPow2 (variantsAlign base vs)
  | _, [], hb, _ => hb
  | base, v :: vs, hb, hvs =>
    variantsAlign_pow2 _ vs (maxAlign_pow2 base v hb (hvs v (List.mem_cons_self ..)))
      (fun fs hfs => hvs fs (List.mem_cons_of_mem _ hfs))

theorem le_cEnd : ∀ (start : Nat) (fs : List FieldLayout), start ≤ cEnd start fs
  | _, [] => Nat.le_refl _
  | start, f :: fs =>
    Nat.le_trans (Nat.le_trans (PlaceAndRvalue.alignUp_ge start f.align) (Nat.le_add_right _ _)) (le_cEnd _ fs)

/-- **`#[repr(C)]` offsets are aligned and in bounds**: field `i` exists, its offset is a
multiple of its (positive) alignment, and the field ends before the sequence's end. -/
theorem cOffset?_spec :
    ∀ (start : Nat) (fs : List FieldLayout) (i off : Nat), cOffset? start fs i = some off →
      ∃ f, fs[i]? = some f ∧ off + f.size ≤ cEnd start fs ∧ (0 < f.align → f.align ∣ off)
  | _, [], _, _, h => by simp [cOffset?] at h
  | start, f :: fs, 0, off, h => by
    simp only [cOffset?, Option.some.injEq] at h
    subst h
    exact ⟨f, rfl, le_cEnd _ fs, fun hPos => alignUp_dvd start f.align hPos⟩
  | start, f :: fs, i + 1, off, h => by
    simp only [cOffset?] at h
    rcases cOffset?_spec _ fs i off h with ⟨g, hG, hEnd, hDvd⟩
    exact ⟨g, by simpa using hG, by simpa [cEnd] using hEnd, hDvd⟩

/-- **`#[repr(C)]` offset monotonicity**: an earlier field ends at or before a later field's
offset. -/
theorem cOffset?_monotone :
    ∀ (start : Nat) (fs : List FieldLayout) (i j oi oj : Nat), i < j →
      cOffset? start fs i = some oi → cOffset? start fs j = some oj →
      ∃ fi, fs[i]? = some fi ∧ oi + fi.size ≤ oj
  | _, [], _, _, _, _, _, h, _ => by simp [cOffset?] at h
  | start, f :: fs, 0, j + 1, oi, oj, _, hi, hj => by
    simp only [cOffset?, Option.some.injEq] at hi hj
    subst hi
    refine ⟨f, rfl, ?_⟩
    -- every later offset is at least the next start `PlaceAndRvalue.alignUp start f.align + f.size`
    have hGe : ∀ (st : Nat) (gs : List FieldLayout) (k o : Nat), cOffset? st gs k = some o → st ≤ o := by
      intro st gs
      induction gs generalizing st with
      | nil => intro k o h; simp [cOffset?] at h
      | cons g gs ih =>
        intro k o h
        cases k with
        | zero =>
          simp only [cOffset?, Option.some.injEq] at h
          subst h
          exact PlaceAndRvalue.alignUp_ge st g.align
        | succ k =>
          simp only [cOffset?] at h
          exact Nat.le_trans (Nat.le_trans (PlaceAndRvalue.alignUp_ge st g.align) (Nat.le_add_right _ _)) (ih _ k o h)
    exact hGe _ fs j oj hj
  | _, _ :: _, _ + 1, 0, _, _, hLt, _, _ => absurd hLt (Nat.not_lt_zero _)
  | start, f :: fs, i + 1, j + 1, oi, oj, hLt, hi, hj => by
    simp only [cOffset?] at hi hj
    rcases cOffset?_monotone _ fs i j oi oj (by omega) hi hj with ⟨fi, hFi, hLe⟩
    exact ⟨fi, by simpa using hFi, hLe⟩

/-- **Padding-free prefix offsets are aligned and in bounds** (`#[repr(Rust)]` canonical
layouts). -/
theorem rustOffset?_spec :
    ∀ (start : Nat) (fs : List FieldLayout) (i off : Nat), rustOffset? start fs i = some off →
      paddingFree start fs = true →
      ∃ f, fs[i]? = some f ∧ off + f.size ≤ start + sumSizes fs ∧ off % f.align = 0
  | _, [], _, _, h, _ => by simp [rustOffset?] at h
  | start, f :: fs, 0, off, h, hPad => by
    simp only [rustOffset?, Option.some.injEq] at h
    subst h
    simp only [paddingFree, Bool.and_eq_true, beq_iff_eq] at hPad
    refine ⟨f, rfl, ?_, hPad.1⟩
    simp only [sumSizes]
    omega
  | start, f :: fs, i + 1, off, h, hPad => by
    simp only [rustOffset?] at h
    simp only [paddingFree, Bool.and_eq_true, beq_iff_eq] at hPad
    rcases rustOffset?_spec _ fs i off h hPad.2 with ⟨g, hG, hEnd, hMod⟩
    refine ⟨g, by simpa using hG, ?_, hMod⟩
    simp only [sumSizes]
    omega

theorem sumSizes_nonOneZstFields : ∀ (fs : List FieldLayout), sumSizes (nonOneZstFields fs) = sumSizes fs
  | [] => rfl
  | f :: fs => by
    have ih := sumSizes_nonOneZstFields fs
    unfold nonOneZstFields at ih ⊢
    rw [List.filter_cons]
    cases hZ : f.isOneZst with
    | false => simp only [Bool.not_false, ↓reduceIte, sumSizes, ih]
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih, sumSizes]
      simp only [FieldLayout.isOneZst, Bool.and_eq_true, beq_iff_eq] at hZ
      rw [hZ.1, Nat.zero_add]

theorem getElem?_mem {α : Type} {xs : List α} {i : Nat} {x : α} (h : xs[i]? = some x) : x ∈ xs :=
  List.mem_of_getElem? h

/-- **Struct-like offset bounds**: a resolved struct-like field offset lies inside the
struct-like layout and is aligned. -/
theorem structFieldOffset?_bounds (repr : AdtReprKind) (rustCanon : Bool) (reprAlign : Option Nat)
    (fs : List FieldLayout) (hPow : ∀ f ∈ fs, IsPow2 f.align)
    {i off size align : Nat}
    (hLay : structLayout? repr reprAlign fs = some (size, align))
    (hOff : structFieldOffset? repr rustCanon fs i = some off) :
    ∃ f, fs[i]? = some f ∧ off + f.size ≤ size ∧ f.align ∣ off := by
  cases repr with
  | c =>
    simp only [structLayout?, Option.some.injEq, Prod.mk.injEq] at hLay
    rcases hLay with ⟨rfl, rfl⟩
    simp only [structFieldOffset?] at hOff
    rcases cOffset?_spec 0 fs i off hOff with ⟨f, hF, hEnd, hDvd⟩
    exact ⟨f, hF, Nat.le_trans hEnd (PlaceAndRvalue.alignUp_ge _ _), hDvd (hPow f (getElem?_mem hF)).pos⟩
  | rust =>
    simp only [structLayout?, Option.some.injEq, Prod.mk.injEq] at hLay
    rcases hLay with ⟨rfl, rfl⟩
    simp only [structFieldOffset?] at hOff
    split at hOff
    · rename_i hCan
      simp only [Bool.and_eq_true] at hCan
      rcases rustOffset?_spec 0 fs i off hOff hCan.2 with ⟨f, hF, hEnd, hMod⟩
      refine ⟨f, hF, ?_, Nat.dvd_of_mod_eq_zero hMod⟩
      have := PlaceAndRvalue.alignUp_ge (sumSizes fs) (maxAlign (reprAlign.getD 1) fs)
      omega
    · nomatch hOff
  | transparent =>
    simp only [structFieldOffset?] at hOff
    cases hFi : fs[i]? with
    | none => rw [hFi] at hOff; nomatch hOff
    | some f =>
      rw [hFi] at hOff
      simp only at hOff
      refine ⟨f, rfl, ?_⟩
      have hMem : f ∈ fs := getElem?_mem hFi
      -- The struct layout is that of the unique non-1-ZST field (or `(0, 1)`).
      unfold structLayout? at hLay
      cases hRAo : reprAlign with
      | some a => rw [hRAo] at hLay; nomatch hLay
      | none =>
        cases hNZ : nonOneZstFields fs with
        | nil =>
          simp only [hRAo, hNZ, Option.some.injEq, Prod.mk.injEq] at hLay
          rcases hLay with ⟨rfl, rfl⟩
          -- every field is a 1-ZST
          have hZ : f.isOneZst = true := by
            cases hZf : f.isOneZst with
            | true => rfl
            | false =>
              have : f ∈ nonOneZstFields fs := by
                unfold nonOneZstFields; rw [List.mem_filter]; exact ⟨hMem, by simp [hZf]⟩
              rw [hNZ] at this; nomatch this
          simp only [FieldLayout.isOneZst, Bool.and_eq_true, beq_iff_eq] at hZ
          have hAll : fs.all (fun g => g.size == 0) = true := by
            rw [List.all_eq_true]
            intro g hg
            cases hZg : g.isOneZst with
            | true =>
              simp only [FieldLayout.isOneZst, Bool.and_eq_true, beq_iff_eq] at hZg
              simp [hZg.1]
            | false =>
              have : g ∈ nonOneZstFields fs := by
                unfold nonOneZstFields; rw [List.mem_filter]; exact ⟨hg, by simp [hZg]⟩
              rw [hNZ] at this; nomatch this
          have hNot : (!f.isOneZst) = false := by simp [FieldLayout.isOneZst, hZ.1, hZ.2]
          rw [hNot, hAll] at hOff
          simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hOff
          subst hOff
          exact ⟨by omega, Nat.dvd_zero _⟩
        | cons g gs =>
          cases gs with
          | cons _ _ => simp only [hRAo, hNZ, reduceCtorEq] at hLay
          | nil =>
            simp only [hRAo, hNZ, Option.some.injEq, Prod.mk.injEq] at hLay
            rcases hLay with ⟨rfl, rfl⟩
            cases hZf : f.isOneZst with
            | false =>
              -- `f` is the unique non-1-ZST field `g`, at offset `0`.
              have hfg : f ∈ nonOneZstFields fs := by
                unfold nonOneZstFields; rw [List.mem_filter]; exact ⟨hMem, by simp [hZf]⟩
              rw [hNZ, List.mem_singleton] at hfg
              subst hfg
              rw [hZf] at hOff
              simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hOff
              subst hOff
              exact ⟨by omega, Nat.dvd_zero _⟩
            | true =>
              simp only [FieldLayout.isOneZst, Bool.and_eq_true, beq_iff_eq] at hZf
              have hNot : (!f.isOneZst) = false := by simp [FieldLayout.isOneZst, hZf.1, hZf.2]
              rw [hNot] at hOff
              simp only [Bool.false_eq_true, ↓reduceIte] at hOff
              split at hOff
              · simp only [Option.some.injEq] at hOff
                subst hOff
                exact ⟨by omega, Nat.dvd_zero _⟩
              · split at hOff
                · rename_i _ hCan
                  simp only [Bool.and_eq_true] at hCan
                  rcases rustOffset?_spec 0 fs i off hOff hCan.2 with ⟨f', hF', hEnd, _⟩
                  rw [hFi, Option.some.injEq] at hF'
                  subst hF'
                  have hSum := sumSizes_nonOneZstFields fs
                  rw [hNZ] at hSum
                  simp only [sumSizes] at hSum
                  refine ⟨by omega, ?_⟩
                  rw [hZf.2]
                  exact Nat.one_dvd _
                · nomatch hOff

theorem mem_allFields_of_variant {vs : List (List FieldLayout)} {v : Nat} {fs : List FieldLayout}
    {f : FieldLayout} (hV : vs[v]? = some fs) (hF : f ∈ fs) : f ∈ vs.flatten :=
  List.mem_flatten.mpr ⟨fs, getElem?_mem hV, hF⟩

/-- **`resolveAdtOffsetOf_bounds_and_align`** (`AdtDef::field_offset`'s contract in `ir.rs`):
whenever `resolveAdtOffsetOf spec v i = some off` for a well-formed specification, variant `v`
and its field `i` exist with layout `f`, the ADT has a layout `(size, align)`, the field lies
inside the container (`off + f.size ≤ size`), and its offset is aligned (`f.align ∣ off`). -/
theorem resolveAdtOffsetOf_bounds_and_align (spec : AdtLayoutSpec) (hWF : spec.WF)
    {v i off : Nat} (h : resolveAdtOffsetOf spec v i = some off) :
    ∃ fs f size align, variantFields spec v = some fs ∧ fs[i]? = some f ∧
      adtLayout? spec = some (size, align) ∧ off + f.size ≤ size ∧ f.align ∣ off := by
  have hAll := hWF.fieldAlignPow2
  cases hL : adtLayout? spec with
  | none => simp [resolveAdtOffsetOf, hL] at h
  | some lay =>
    obtain ⟨size, align⟩ := lay
    cases hShape : spec.shape with
    | struct fs =>
      have hL' := hL
      simp only [adtLayout?, hShape] at hL'
      simp only [resolveAdtOffsetOf, hL, hShape] at h
      rw [hShape] at hAll
      split at h
      · rename_i hV
        subst hV
        rcases structFieldOffset?_bounds spec.repr spec.rustOrderCanonical spec.reprAlign fs
            hAll hL' h with ⟨f, hF, hEnd, hDvd⟩
        exact ⟨fs, f, size, align, by simp [variantFields, hShape], hF, rfl, hEnd, hDvd⟩
      · nomatch h
    | union fs =>
      have hL' := hL
      simp only [adtLayout?, hShape] at hL'
      simp only [resolveAdtOffsetOf, hL, hShape] at h
      split at h
      · rename_i hCond
        rcases hCond with ⟨rfl, hLt⟩
        simp only [Option.some.injEq] at h
        subst h
        have hF : fs[i]? = some fs[i] := List.getElem?_eq_getElem hLt
        refine ⟨fs, fs[i], size, align, by simp [variantFields, hShape], hF, rfl, ?_,
          Nat.dvd_zero _⟩
        unfold unionLayout? at hL'
        cases fs with
        | nil => nomatch hL'
        | cons g gs =>
          simp only at hL'
          split at hL'
          · nomatch hL'
          · simp only [Option.some.injEq, Prod.mk.injEq] at hL'
            rcases hL' with ⟨rfl, rfl⟩
            have := le_maxSize_of_mem (g :: gs) _ (getElem?_mem hF)
            have := PlaceAndRvalue.alignUp_ge (maxSize (g :: gs))
              (maxAlign (spec.reprAlign.getD 1) (g :: gs))
            omega
      · nomatch h
    | taggedEnum tagSize vs =>
      have hL' := hL
      simp only [adtLayout?, hShape] at hL'
      simp only [resolveAdtOffsetOf, hL, hShape] at h
      rw [hShape] at hAll
      have hTag : IsPow2 tagSize := hWF.tagPow2 tagSize vs hShape
      have hVsPow : ∀ fs ∈ vs, ∀ f ∈ fs, IsPow2 f.align := fun fs hfs f hf =>
        hAll f (List.mem_flatten.mpr ⟨fs, hfs, hf⟩)
      unfold taggedFieldOffset? at h
      cases hV : vs[v]? with
      | none => rw [hV] at h; nomatch h
      | some fs =>
        rw [hV] at h
        simp only at h
        have hFsMem : fs ∈ vs := getElem?_mem hV
        have hVF : variantFields spec v = some fs := by simp [variantFields, hShape, hV]
        cases hRepr : spec.repr with
        | transparent => rw [hRepr] at h; nomatch h
        | rust =>
          rw [hRepr] at h hL'
          simp only [taggedLayout?, Option.some.injEq, Prod.mk.injEq] at hL'
          rcases hL' with ⟨rfl, rfl⟩
          rcases cOffset?_spec tagSize fs i off h with ⟨f, hF, hEnd, hDvd⟩
          refine ⟨fs, f, _, _, hVF, hF, rfl, ?_,
            hDvd (hVsPow fs hFsMem f (getElem?_mem hF)).pos⟩
          have h1 := PlaceAndRvalue.alignUp_ge (cEnd tagSize fs) (maxAlign tagSize fs)
          have h2 := le_maxList_of_mem
            (vs.map (fun v => PlaceAndRvalue.alignUp (cEnd tagSize v) (maxAlign tagSize v)))
            (PlaceAndRvalue.alignUp (cEnd tagSize fs) (maxAlign tagSize fs))
            (List.mem_map.mpr ⟨fs, hFsMem, rfl⟩)
          have h3 := PlaceAndRvalue.alignUp_ge
            (maxList (vs.map (fun v => PlaceAndRvalue.alignUp (cEnd tagSize v) (maxAlign tagSize v))))
            (variantsAlign (max (spec.reprAlign.getD 1) tagSize) vs)
          omega
        | c =>
          rw [hRepr] at h hL'
          simp only [taggedLayout?, Option.some.injEq, Prod.mk.injEq] at hL'
          rcases hL' with ⟨rfl, rfl⟩
          cases hIn : cOffset? 0 fs i with
          | none => rw [hIn] at h; nomatch h
          | some inner =>
            rw [hIn] at h
            simp only [Option.map_some, Option.some.injEq] at h
            subst h
            rcases cOffset?_spec 0 fs i inner hIn with ⟨f, hF, hEnd, hDvd⟩
            have hFMem : f ∈ fs := getElem?_mem hF
            have hFPow := hVsPow fs hFsMem f hFMem
            have hPA : IsPow2 (payloadAlign vs) := variantsAlign_pow2 1 vs isPow2_one hVsPow
            refine ⟨fs, f, _, _, hVF, hF, rfl, ?_, ?_⟩
            · have h1 := PlaceAndRvalue.alignUp_ge (cEnd 0 fs) (maxAlign 1 fs)
              have h2 := le_maxList_of_mem
                (vs.map (fun v => PlaceAndRvalue.alignUp (cEnd 0 v) (maxAlign 1 v)))
                (PlaceAndRvalue.alignUp (cEnd 0 fs) (maxAlign 1 fs))
                (List.mem_map.mpr ⟨fs, hFsMem, rfl⟩)
              have h3 := PlaceAndRvalue.alignUp_ge
                (maxList (vs.map (fun v => PlaceAndRvalue.alignUp (cEnd 0 v) (maxAlign 1 v))))
                (payloadAlign vs)
              have h4 := PlaceAndRvalue.alignUp_ge
                (payloadOffset tagSize vs + PlaceAndRvalue.alignUp
                  (maxList (vs.map (fun v => PlaceAndRvalue.alignUp (cEnd 0 v) (maxAlign 1 v))))
                  (payloadAlign vs))
                (max (max (spec.reprAlign.getD 1) tagSize) (payloadAlign vs))
              omega
            · apply Nat.dvd_add
              · -- `f.align ∣ payloadAlign vs ∣ payloadOffset tagSize vs`
                have hLe : f.align ≤ payloadAlign vs :=
                  le_variantsAlign_of_mem 1 vs fs f hFsMem hFMem
                exact Nat.dvd_trans (hFPow.dvd_of_le hPA hLe)
                  (alignUp_dvd tagSize (payloadAlign vs) hPA.pos)
              · exact hDvd hFPow.pos
    | univariantEnum present vs =>
      have hL' := hL
      simp only [adtLayout?, hShape] at hL'
      simp only [resolveAdtOffsetOf, hL, hShape] at h
      rw [hShape] at hAll
      cases hV : vs[v]? with
      | none => rw [hV] at h; nomatch h
      | some fs =>
        rw [hV] at h
        simp only at h
        have hVF : variantFields spec v = some fs := by simp [variantFields, hShape, hV]
        split at h
        · rename_i hEq
          subst hEq
          rw [hV] at hL'
          simp only at hL'
          split at hL'
          · nomatch hL'
          · have hPow : ∀ f ∈ fs, IsPow2 f.align := fun f hf =>
              hAll f (mem_allFields_of_variant hV hf)
            rcases structFieldOffset?_bounds spec.repr spec.rustOrderCanonical spec.reprAlign
                fs hPow hL' h with ⟨f, hF, hEnd, hDvd⟩
            exact ⟨fs, f, size, align, hVF, hF, rfl, hEnd, hDvd⟩
        · rename_i hNe
          unfold absentFieldOffset? at h
          split at h
          · rename_i hLt
            simp only [Option.some.injEq] at h
            subst h
            have hF : fs[i]? = some fs[i] := List.getElem?_eq_getElem hLt
            have hZero := hWF.absentZeroSized present vs hShape v fs hV hNe fs[i]
              (getElem?_mem hF)
            exact ⟨fs, fs[i], size, align, hVF, hF, rfl, by omega, Nat.dvd_zero _⟩
          · nomatch h
    | noPresentEnum vs =>
      simp only [resolveAdtOffsetOf, hL, hShape] at h
      cases hV : vs[v]? with
      | none => rw [hV] at h; nomatch h
      | some fs =>
        rw [hV] at h
        simp only at h
        unfold absentFieldOffset? at h
        split at h
        · rename_i hLt
          simp only [Option.some.injEq] at h
          subst h
          have hF : fs[i]? = some fs[i] := List.getElem?_eq_getElem hLt
          have hZero := hWF.noPresentZeroSized vs hShape fs (getElem?_mem hV) fs[i]
            (getElem?_mem hF)
          exact ⟨fs, fs[i], size, align, by simp [variantFields, hShape, hV], hF, rfl,
            by omega, Nat.dvd_zero _⟩
        · nomatch h
    | unspecifiedEnum vs =>
      simp [resolveAdtOffsetOf, hL, hShape] at h

/-- **Union fields all sit at offset `0`.** -/
theorem resolveAdtOffsetOf_union_eq_zero {spec : AdtLayoutSpec} {fs : List FieldLayout}
    (hShape : spec.shape = .union fs) {v i off : Nat}
    (h : resolveAdtOffsetOf spec v i = some off) : off = 0 := by
  unfold resolveAdtOffsetOf at h
  cases hLay : adtLayout? spec with
  | none => rw [hLay] at h; nomatch h
  | some _ =>
    rw [hLay, hShape] at h
    simp only at h
    split at h
    · simp only [Option.some.injEq] at h
      exact h.symm
    · nomatch h

/-- **`#[repr(transparent)]` delegation**: the unique non-1-ZST field of a well-formed
transparent struct sits at offset `0`. -/
theorem resolveAdtOffsetOf_transparent_nonZst {spec : AdtLayoutSpec} {fs : List FieldLayout}
    (hShape : spec.shape = .struct fs) (hRepr : spec.repr = .transparent)
    {i : Nat} {f : FieldLayout} (hF : fs[i]? = some f) (hNZ : f.isOneZst = false)
    (hLay : (adtLayout? spec).isSome = true) :
    resolveAdtOffsetOf spec 0 i = some 0 := by
  unfold resolveAdtOffsetOf
  cases hL : adtLayout? spec with
  | none => rw [hL] at hLay; nomatch hLay
  | some _ =>
    simp only [hShape, ↓reduceIte, structFieldOffset?, hRepr, hF, hNZ, Bool.not_false]

/-- **`#[repr(C)]` struct offsets are strictly ordered**: an earlier field of a `#[repr(C)]`
struct ends at or before a later field's offset. -/
theorem resolveAdtOffsetOf_reprC_monotone {spec : AdtLayoutSpec} {fs : List FieldLayout}
    (hShape : spec.shape = .struct fs) (hRepr : spec.repr = .c)
    {i j oi oj : Nat} (hLt : i < j)
    (hi : resolveAdtOffsetOf spec 0 i = some oi) (hj : resolveAdtOffsetOf spec 0 j = some oj) :
    ∃ fi, fs[i]? = some fi ∧ oi + fi.size ≤ oj := by
  unfold resolveAdtOffsetOf at hi hj
  cases hL : adtLayout? spec with
  | none => rw [hL] at hi; nomatch hi
  | some _ =>
    rw [hL, hShape] at hi hj
    simp only [↓reduceIte, structFieldOffset?, hRepr] at hi hj
    exact cOffset?_monotone 0 fs i j oi oj hLt hi hj

/-- One `(containerSpec, variantIdx, fieldIdx)` hop in a multi-step `NullOp::OffsetOf(fields)`
projection chain (`resolve_offset_of` in `rvalue.rs`). -/
structure OffsetOfStep : Type where
  spec : AdtLayoutSpec
  variantIdx : Nat
  fieldIdx : Nat

/-- `resolve_offset_of` over a chain of nested ADT `(variantIdx, fieldIdx)` steps: sums the byte
offset of each step along the chain. -/
def resolveAdtOffsetOfChain : List OffsetOfStep → Option Nat
  | [] => some 0
  | step :: rest =>
    match resolveAdtOffsetOf step.spec step.variantIdx step.fieldIdx,
        resolveAdtOffsetOfChain rest with
    | some off, some tailOff => some (off + tailOff)
    | _, _ => none

/-- Well-formedness of a non-empty `OffsetOf` chain reaching a leaf field with layout `leaf`:
every container specification is `AdtLayoutSpec.WF`, a single-step chain resolves directly to
`leaf`, and in a multi-step chain `step :: next :: rest`, the field selected in `step` has the
exact `(size, align)` layout of `next.spec` and its alignment is a multiple of `leaf.align`. -/
inductive OffsetOfChainWF : List OffsetOfStep → FieldLayout → Prop where
  | single (step : OffsetOfStep) (fs : List FieldLayout) (leaf : FieldLayout)
      (hWF : step.spec.WF)
      (hVar : variantFields step.spec step.variantIdx = some fs)
      (hField : fs[step.fieldIdx]? = some leaf) :
      OffsetOfChainWF [step] leaf
  | cons (step next : OffsetOfStep) (rest : List OffsetOfStep)
      (fs : List FieldLayout) (mid leaf : FieldLayout)
      (hWF : step.spec.WF)
      (hVar : variantFields step.spec step.variantIdx = some fs)
      (hField : fs[step.fieldIdx]? = some mid)
      (hNextLay : adtLayout? next.spec = some (mid.size, mid.align))
      (hDvdAlign : leaf.align ∣ mid.align)
      (hTail : OffsetOfChainWF (next :: rest) leaf) :
      OffsetOfChainWF (step :: next :: rest) leaf

/-- **Multi-step `OffsetOf` cumulative bounds and alignment (`resolveAdtOffsetOfChain_bounds_and_align`)**:
for any well-formed chain `step :: rest` of nested ADT field projections (`NullOp::OffsetOf`)
reaching `leaf`, if `resolveAdtOffsetOfChain (step :: rest) = some totalOff`, then the root
container `step.spec` has a layout `(rootSize, rootAlign)`, the leaf field lies completely inside
the root container (`totalOff + leaf.size ≤ rootSize`), and the cumulative byte offset is aligned
to the leaf field's alignment (`leaf.align ∣ totalOff`). -/
theorem resolveAdtOffsetOfChain_bounds_and_align {chain : List OffsetOfStep} {leaf : FieldLayout}
    (hChain : OffsetOfChainWF chain leaf) {totalOff : Nat}
    (hRes : resolveAdtOffsetOfChain chain = some totalOff) :
    match chain with
    | [] => True
    | root :: _ =>
      ∃ rootSize rootAlign, adtLayout? root.spec = some (rootSize, rootAlign) ∧
        totalOff + leaf.size ≤ rootSize ∧ leaf.align ∣ totalOff := by
  induction hChain generalizing totalOff with
  | single step fs leaf hWF hVar hField =>
    simp only [resolveAdtOffsetOfChain] at hRes
    cases hOff : resolveAdtOffsetOf step.spec step.variantIdx step.fieldIdx with
    | none => rw [hOff] at hRes; nomatch hRes
    | some off =>
      rw [hOff] at hRes
      simp only [Option.some.injEq, Nat.add_zero] at hRes
      subst hRes
      obtain ⟨fs', f', size, align, hVF, hF', hLay, hBound, hAlign⟩ :=
        resolveAdtOffsetOf_bounds_and_align step.spec hWF hOff
      rw [hVar] at hVF
      cases hVF
      rw [hField] at hF'
      cases hF'
      exact ⟨size, align, hLay, hBound, hAlign⟩
  | cons step next rest fs mid leaf hWF hVar hField hNextLay hDvdAlign _ ih =>
    rw [resolveAdtOffsetOfChain] at hRes
    cases hOff : resolveAdtOffsetOf step.spec step.variantIdx step.fieldIdx with
    | none => rw [hOff] at hRes; nomatch hRes
    | some off =>
      rw [hOff] at hRes
      cases hTail : resolveAdtOffsetOfChain (next :: rest) with
      | none => rw [hTail] at hRes; nomatch hRes
      | some tailOff =>
        rw [hTail] at hRes
        simp only [Option.some.injEq] at hRes
        subst hRes
        obtain ⟨fs', f', rootSize, rootAlign, hVF, hF', hLay, hBound, hMidAlign⟩ :=
          resolveAdtOffsetOf_bounds_and_align step.spec hWF hOff
        rw [hVar] at hVF
        cases hVF
        rw [hField] at hF'
        cases hF'
        obtain ⟨nextSize, nextAlign, hNL, hTailBound, hTailAlign⟩ := ih hTail
        rw [hNextLay] at hNL
        cases hNL
        refine ⟨rootSize, rootAlign, hLay, by omega, ?_⟩
        exact Nat.dvd_add (Nat.dvd_trans hDvdAlign hMidAlign) hTailAlign

/-- Every `#[repr(C)]` field offset is at least the starting offset `start`. -/
theorem cOffset?_ge_start :
    ∀ (start : Nat) (fs : List FieldLayout) (i off : Nat), cOffset? start fs i = some off →
      start ≤ off
  | _, [], _, _, h => by simp [cOffset?] at h
  | start, f :: _, 0, off, h => by
    simp only [cOffset?, Option.some.injEq] at h
    subst h
    exact PlaceAndRvalue.alignUp_ge start f.align
  | start, f :: fs, i + 1, off, h => by
    simp only [cOffset?] at h
    exact Nat.le_trans
      (Nat.le_trans (PlaceAndRvalue.alignUp_ge start f.align) (Nat.le_add_right _ _))
      (cOffset?_ge_start _ fs i off h)

/-- **Explicit-tag enum fields sit after the tag (`resolveAdtOffsetOf_taggedEnum_ge_tagSize`)**:
for any explicit-tag enum (`#[repr(Int)]` or `#[repr(C, Int)]`), every resolved variant field
offset `off` satisfies `tagSize ≤ off`, so the field's byte range `[off, off + f.size)` is
disjoint from the explicit discriminant tag `[0, tagSize)` (`AdtDef::tag_survives_field_deinit`). -/
theorem resolveAdtOffsetOf_taggedEnum_ge_tagSize {spec : AdtLayoutSpec} {tagSize : Nat}
    {vs : List (List FieldLayout)} (hShape : spec.shape = .taggedEnum tagSize vs)
    {v i off : Nat} (h : resolveAdtOffsetOf spec v i = some off) : tagSize ≤ off := by
  unfold resolveAdtOffsetOf at h
  cases hL : adtLayout? spec with
  | none => rw [hL] at h; nomatch h
  | some _ =>
    rw [hL, hShape] at h
    simp only [taggedFieldOffset?] at h
    cases hV : vs[v]? with
    | none => rw [hV] at h; nomatch h
    | some fs =>
      rw [hV] at h
      simp only at h
      cases hR : spec.repr with
      | transparent => rw [hR] at h; nomatch h
      | rust =>
        rw [hR] at h
        exact cOffset?_ge_start tagSize fs i off h
      | c =>
        rw [hR] at h
        cases hIn : cOffset? 0 fs i with
        | none => rw [hIn] at h; nomatch h
        | some inner =>
          rw [hIn] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          have hP : tagSize ≤ payloadOffset tagSize vs :=
            PlaceAndRvalue.alignUp_ge tagSize (payloadAlign vs)
          omega

/-! ## Section 1c: Typed ADT `Discriminant` -/

/-- Discriminant-relevant facts of a typed ADT (`AdtDef` in `ir.rs`): whether it is an enum,
its per-variant discriminant bit patterns (`AdtDef::discriminants`) and inhabitedness, whether
a value stores a tag (`AdtDef::requires_tag_write`), whether that tag is stored apart from the
variant fields (`AdtDef::tag_survives_field_deinit`; false for niche-capable tagless enums),
and the constant variant of a tagless layout (`AdtDef::univariant_index`, `0` otherwise). -/
structure AdtDiscrSpec : Type where
  isEnum : Bool
  discriminants : List Nat
  variantInhabited : List Bool
  requiresTagWrite : Bool
  tagSurvivesFieldDeinit : Bool
  taglessVariant : Nat

/-- `PartialAggregate::tag_is_readable` (`A3`) for a typed shell of an ADT described by `spec`:
an ADT without a stored tag always has a readable variant, and otherwise the tag must have been
written by `SetDiscriminant` and be stored apart from the (possibly uninitialized) fields. -/
def tagIsReadable (spec : AdtDiscrSpec) (shell : PartialAggregate) : Bool :=
  !spec.requiresTagWrite || (shell.discriminantSet && spec.tagSurvivesFieldDeinit)

/-- `discriminant_value`: the discriminant bits of variant `v` of an enum (`none` for an
uninhabited/absent or out-of-range variant, `UninhabitedEnumVariant`), and `0` for variant `0`
of a struct or union (`rustc`'s `discriminant_ty` is `u8`). -/
def discriminantValue? (spec : AdtDiscrSpec) (v : Nat) : Option Nat :=
  if spec.isEnum then
    match spec.variantInhabited[v]?, spec.discriminants[v]? with
    | some true, some d => some d
    | _, _ => none
  else if v = 0 then some 0 else none

/-- The variant a shell is narrowed to (`0` for a tuple shell), exactly as `readFromPartialShell`
and `writeToFieldSlot` compute it. -/
def shellVariant (shell : PartialAggregate) : Nat :=
  match shell.isAdt with
  | true => shell.variantIdx
  | false => 0

/-- `Rvalue::Discriminant` on a typed ADT place holding `slot` (`eval_lowered_rvalue_in_state`
with `StatementEvalState::typed_enum_variant`), where `wf` is `check_value_well_formed`:
- a dead local faults (`DeadLocal`);
- an uninitialized place has a defined discriminant only when no tag is stored;
- an initialized value reports its variant's discriminant, except that a niche-capable enum
  (`B4`, whose tag may live in a field's niche) requires the whole value to be well formed;
- a partial shell reports its variant only when its tag is readable (`A3`). -/
def evalAdtDiscriminant (spec : AdtDiscrSpec) (wf : Value → Bool) :
    LocalSlotState → Option Nat
  | .dead => none
  | .uninit => if spec.requiresTagWrite then none else discriminantValue? spec spec.taglessVariant
  | .init (.aggregate v fields) =>
    if !spec.tagSurvivesFieldDeinit && !wf (.aggregate v fields) then none
    else discriminantValue? spec v
  | .init _ => none
  | .partialShell shell =>
    if tagIsReadable spec shell then discriminantValue? spec (shellVariant shell) else none

/-- **Absent/uninhabited variants have no discriminant (`B2`)**: reading the discriminant of an
enum value or shell narrowed to an uninhabited variant faults. -/
theorem evalAdtDiscriminant_uninhabited_variant_none (spec : AdtDiscrSpec) (wf : Value → Bool)
    (hEnum : spec.isEnum = true) {v : Nat} (hUninh : spec.variantInhabited[v]? = some false) :
    (∀ fields, evalAdtDiscriminant spec wf (.init (.aggregate v fields)) = none) ∧
    (∀ shell, shellVariant shell = v → evalAdtDiscriminant spec wf (.partialShell shell) = none) := by
  have hVal : discriminantValue? spec v = none := by
    simp [discriminantValue?, hEnum, hUninh]
  refine ⟨fun fields => ?_, fun shell hV => ?_⟩
  · simp only [evalAdtDiscriminant]
    split <;> simp_all
  · simp only [evalAdtDiscriminant, hV]
    split <;> simp_all

/-- **Niche-capable shells have no readable tag (`A3`)**: for an enum whose tag may be
niche-encoded in a variant field (`requires_tag_write` but not `tag_survives_field_deinit`),
`Discriminant` on any incomplete shell faults, even after `SetDiscriminant`. -/
theorem evalAdtDiscriminant_niche_shell_none (spec : AdtDiscrSpec) (wf : Value → Bool)
    (hTag : spec.requiresTagWrite = true) (hNiche : spec.tagSurvivesFieldDeinit = false)
    (shell : PartialAggregate) :
    evalAdtDiscriminant spec wf (.partialShell shell) = none := by
  simp [evalAdtDiscriminant, tagIsReadable, hTag, hNiche]

/-- **Tags stored apart are readable on shells**: after `SetDiscriminant` has written a tag
stored apart from the fields, `Discriminant` on the incomplete shell is the variant's
discriminant. -/
theorem evalAdtDiscriminant_tag_apart_shell (spec : AdtDiscrSpec) (wf : Value → Bool)
    (hApart : spec.tagSurvivesFieldDeinit = true) (shell : PartialAggregate)
    (hSet : shell.discriminantSet = true) :
    evalAdtDiscriminant spec wf (.partialShell shell) = discriminantValue? spec (shellVariant shell) := by
  simp [evalAdtDiscriminant, tagIsReadable, hApart, hSet]

/-- **Niche-capable values must be well formed (`B4`)**: an initialized niche-capable enum value
that is not well formed (e.g. `Some(NonZeroU32(0))`, whose bytes MiniRust decodes as `None`)
has no discriminant. -/
theorem evalAdtDiscriminant_niche_init_ill_formed_none (spec : AdtDiscrSpec) (wf : Value → Bool)
    (hNiche : spec.tagSurvivesFieldDeinit = false) {v : Nat} {fields : List Value}
    (hBad : wf (.aggregate v fields) = false) :
    evalAdtDiscriminant spec wf (.init (.aggregate v fields)) = none := by
  simp [evalAdtDiscriminant, hNiche, hBad]

/-- An uninitialized enum that stores a tag has no discriminant (`UninitializedLocal`), while a
tagless one reports its constant discriminant without reading memory. -/
theorem evalAdtDiscriminant_uninit (spec : AdtDiscrSpec) (wf : Value → Bool) :
    evalAdtDiscriminant spec wf .uninit =
      if spec.requiresTagWrite then none else discriminantValue? spec spec.taglessVariant := rfl

private theorem listByteEq_eq : ∀ (xs ys : List UInt8), listByteEq xs ys = true → xs = ys
  | [], [], _ => rfl
  | b₁ :: bs₁, b₂ :: bs₂, h => by
    unfold listByteEq at h
    cases hb : Nat.beq b₁.toBitVec.toNat b₂.toBitVec.toNat with
    | false => rw [hb] at h; nomatch h
    | true =>
      rw [hb] at h
      have hByte : b₁ = b₂ :=
        UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hb))
      rw [hByte, listByteEq_eq bs₁ bs₂ h]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

private theorem stringEq_congr_left {a b : String} (h : stringEq a b = true) (c : String) :
    stringEq a c = stringEq b c := by
  unfold stringEq at h ⊢
  rw [listByteEq_eq _ _ h]

private def isProjLeafKind : RigidTy → Bool
  | .array _ _ => false
  | .slice _ => false
  | .ref _ _ => false
  | .rawPtr _ _ => false
  | .adt _ [_] => false
  | _ => true

private theorem isProjLeafKind_spec :
    ∀ (k : RigidTy), isProjLeafKind k = true →
      (∀ e n, k ≠ .array e n) ∧ (∀ e, k ≠ .slice e) ∧
        pointeeTyOf { kind := k, layoutIdx := 0 } = none
  | .array _ _, h => nomatch h
  | .slice _, h => nomatch h
  | .ref _ _, h => nomatch h
  | .rawPtr _ _, h => nomatch h
  | .adt _ [_], h => nomatch h
  | .adt _ [], _ => ⟨(fun _ _ hc => by cases hc), (fun _ hc => by cases hc), rfl⟩
  | .adt _ (_ :: _ :: _), _ => ⟨(fun _ _ hc => by cases hc), (fun _ hc => by cases hc), rfl⟩
  | .bool, _ | .char, _ | .int _, _ | .uint _, _ | .float _, _
  | .never, _ | .str, _ | .tuple _, _ | .fnDef _ _, _ | .fnPtr _ _ _ _, _
  | .closure _ _, _ | .dynamic _, _ | .foreign _, _ | .param _ _, _
  | .alias _ _, _ | .other _, _ =>
    ⟨(fun _ _ hc => by cases hc), (fun _ hc => by cases hc), rfl⟩

private inductive ProjShapeRel : RigidTy → RigidTy → Prop where
  | refl (k : RigidTy) : ProjShapeRel k k
  | array {e₁ e₂ : RigidTy} (n₁ n₂ : Nat) :
      ProjShapeRel e₁ e₂ → ProjShapeRel (.array e₁ n₁) (.array e₂ n₂)
  | slice {e₁ e₂ : RigidTy} :
      ProjShapeRel e₁ e₂ → ProjShapeRel (.slice e₁) (.slice e₂)
  | ref {m₁ m₂ : Mutability} {p₁ p₂ : RigidTy} :
      ProjShapeRel p₁ p₂ → ProjShapeRel (.ref m₁ p₁) (.ref m₂ p₂)
  | rawPtr {m₁ m₂ : Mutability} {p₁ p₂ : RigidTy} :
      ProjShapeRel p₁ p₂ → ProjShapeRel (.rawPtr m₁ p₁) (.rawPtr m₂ p₂)
  | adtBox {d₁ d₂ : String} {p₁ p₂ : RigidTy} :
      (∀ c, stringEq d₁ c = stringEq d₂ c) →
      ProjShapeRel p₁ p₂ → ProjShapeRel (.adt d₁ [p₁]) (.adt d₂ [p₂])
  | leaf {k₁ k₂ : RigidTy} :
      (∀ e n, k₁ ≠ .array e n ∧ k₂ ≠ .array e n) →
      (∀ e, k₁ ≠ .slice e ∧ k₂ ≠ .slice e) →
      pointeeTyOf { kind := k₁, layoutIdx := 0 } = none →
      pointeeTyOf { kind := k₂, layoutIdx := 0 } = none →
      ProjShapeRel k₁ k₂

private theorem projShapeRel_of_leaf {k₁ k₂ : RigidTy}
    (h₁ : isProjLeafKind k₁ = true) (h₂ : isProjLeafKind k₂ = true) :
    ProjShapeRel k₁ k₂ := by
  obtain ⟨hA₁, hS₁, hP₁⟩ := isProjLeafKind_spec k₁ h₁
  obtain ⟨hA₂, hS₂, hP₂⟩ := isProjLeafKind_spec k₂ h₂
  exact .leaf (fun e n => ⟨hA₁ e n, hA₂ e n⟩) (fun e => ⟨hS₁ e, hS₂ e⟩) hP₁ hP₂

private theorem ProjShapeRel.trans {k₁ k₂ k₃ : RigidTy}
    (h₁ : ProjShapeRel k₁ k₂) (h₂ : ProjShapeRel k₂ k₃) : ProjShapeRel k₁ k₃ := by
  induction h₁ generalizing k₃ with
  | refl => exact h₂
  | array n₁ n₂ hp ih =>
    cases h₂ with
    | refl => exact .array n₁ n₂ hp
    | array _ n₃ hq => exact .array n₁ n₃ (ih hq)
    | leaf hArr _ _ _ => exact absurd rfl (hArr _ _).1
  | slice hp ih =>
    cases h₂ with
    | refl => exact .slice hp
    | slice hq => exact .slice (ih hq)
    | leaf _ hSl _ _ => exact absurd rfl (hSl _).1
  | ref hp ih =>
    cases h₂ with
    | refl => exact .ref hp
    | ref hq => exact .ref (ih hq)
    | leaf _ _ hPt _ => nomatch hPt
  | rawPtr hp ih =>
    cases h₂ with
    | refl => exact .rawPtr hp
    | rawPtr hq => exact .rawPtr (ih hq)
    | leaf _ _ hPt _ => nomatch hPt
  | @adtBox d₁ d₂ p₁ p₂ hStr hp ih =>
    cases h₂ with
    | refl => exact .adtBox hStr hp
    | adtBox hStr₂ hq => exact .adtBox (fun c => (hStr c).trans (hStr₂ c)) (ih hq)
    | leaf hArr₂ hSl₂ hPt₂ hPt₃ =>
      have hPt₁ : pointeeTyOf { kind := .adt d₁ [p₁], layoutIdx := 0 } = none := by
        unfold pointeeTyOf at hPt₂ ⊢
        dsimp only at hPt₂ ⊢
        rw [hStr "std::boxed::Box", hStr "alloc::boxed::Box"]
        cases hBox : Bool.or (stringEq d₂ "std::boxed::Box") (stringEq d₂ "alloc::boxed::Box") with
        | false => rfl
        | true => rw [hBox] at hPt₂; nomatch hPt₂
      exact .leaf (fun e n => ⟨(by intro hc; cases hc), (hArr₂ e n).2⟩)
        (fun e => ⟨(by intro hc; cases hc), (hSl₂ e).2⟩) hPt₁ hPt₃
  | leaf hArr₁ hSl₁ hPt₁ hPt₂ =>
    cases h₂ with
    | refl => exact .leaf hArr₁ hSl₁ hPt₁ hPt₂
    | array _ _ _ => exact absurd rfl (hArr₁ _ _).2
    | slice _ => exact absurd rfl (hSl₁ _).2
    | ref _ => nomatch hPt₂
    | rawPtr _ => nomatch hPt₂
    | @adtBox d₂ d₃ p₂ p₃ hStr₂ _ =>
      have hPt₃ : pointeeTyOf { kind := .adt d₃ [p₃], layoutIdx := 0 } = none := by
        unfold pointeeTyOf at hPt₂ ⊢
        dsimp only at hPt₂ ⊢
        rw [← hStr₂ "std::boxed::Box", ← hStr₂ "alloc::boxed::Box"]
        cases hBox : Bool.or (stringEq d₂ "std::boxed::Box") (stringEq d₂ "alloc::boxed::Box") with
        | false => rfl
        | true => rw [hBox] at hPt₂; nomatch hPt₂
      exact .leaf (fun e n => ⟨(hArr₁ e n).1, (by intro hc; cases hc)⟩)
        (fun e => ⟨(hSl₁ e).1, (by intro hc; cases hc)⟩) hPt₁ hPt₃
    | leaf hArr₂ hSl₂ _ hPt₃ =>
      exact .leaf (fun e n => ⟨(hArr₁ e n).1, (hArr₂ e n).2⟩)
        (fun e => ⟨(hSl₁ e).1, (hSl₂ e).2⟩) hPt₁ hPt₃

private theorem rigidTyEqAux_projShapeRel (fuel : Nat) :
    ∀ (a b : RigidTy), rigidTyEqAux fuel a b = true → ProjShapeRel b a := by
  induction fuel with
  | zero =>
    intro _ _ h
    unfold rigidTyEqAux at h
    nomatch h
  | succ f ih =>
    intro a b h
    cases a with
    | array e₁ n₁ =>
      cases b with
      | array e₂ n₂ =>
        unfold rigidTyEqAux at h
        simp only [Bool.and_eq_true] at h
        exact .array n₂ n₁ (ih e₁ e₂ h.2)
      | _ => nomatch h
    | slice e₁ =>
      cases b with
      | slice e₂ => exact .slice (ih e₁ e₂ h)
      | _ => nomatch h
    | ref _ p₁ =>
      cases b with
      | ref _ p₂ =>
        unfold rigidTyEqAux at h
        simp only [Bool.and_eq_true] at h
        exact .ref (ih p₁ p₂ h.2)
      | _ => nomatch h
    | rawPtr _ p₁ =>
      cases b with
      | rawPtr _ p₂ =>
        unfold rigidTyEqAux at h
        simp only [Bool.and_eq_true] at h
        exact .rawPtr (ih p₁ p₂ h.2)
      | _ => nomatch h
    | adt d₁ args₁ =>
      cases b with
      | adt d₂ args₂ =>
        unfold rigidTyEqAux at h
        simp only [Bool.and_eq_true] at h
        cases args₁ with
        | nil =>
          cases args₂ with
          | nil => exact projShapeRel_of_leaf rfl rfl
          | cons _ _ => cases f <;> nomatch h.2
        | cons p₁ rest₁ =>
          cases rest₁ with
          | nil =>
            cases f with
            | zero => nomatch h.2
            | succ f' =>
              cases args₂ with
              | nil => nomatch h.2
              | cons p₂ rest₂ =>
                unfold rigidTyListEqAux at h
                simp only [Bool.and_eq_true] at h
                cases rest₂ with
                | cons _ _ => nomatch h.2.2
                | nil =>
                  exact .adtBox (fun c => (stringEq_congr_left h.1 c).symm)
                    (ih p₁ p₂ h.2.1)
          | cons _ _ =>
            cases args₂ with
            | nil => cases f <;> nomatch h.2
            | cons _ rest₂ =>
              cases rest₂ with
              | cons _ _ => exact projShapeRel_of_leaf rfl rfl
              | nil =>
                cases f with
                | zero => nomatch h.2
                | succ _ =>
                  unfold rigidTyListEqAux at h
                  simp only [Bool.and_eq_true] at h
                  nomatch h.2.2
      | _ => nomatch h
    | _ =>
      cases b with
      | array _ _ => nomatch h
      | slice _ => nomatch h
      | ref _ _ => nomatch h
      | rawPtr _ _ => nomatch h
      | adt _ _ => nomatch h
      | _ => exact projShapeRel_of_leaf rfl rfl

private theorem findDeclTyWithKind?_rel :
    ∀ (decls : List LocalDecl) (k : RigidTy) (t : Ty),
      findDeclTyWithKind? decls k = some t → ProjShapeRel k t.kind
  | [], _, _, h => nomatch h
  | d :: rest, k, t, h => by
    unfold findDeclTyWithKind? at h
    cases heq : rigidTyEq d.ty.kind k with
    | true =>
      rw [heq] at h
      injection h with ht
      rw [← ht]
      exact rigidTyEqAux_projShapeRel defaultTyEqFuel d.ty.kind k heq
    | false =>
      rw [heq] at h
      exact findDeclTyWithKind?_rel rest k t h

private theorem findContainerElemTyWithKind?_kind :
    ∀ (layouts : LayoutTable) (decls : List LocalDecl) (k : RigidTy) (t : Ty),
      findContainerElemTyWithKind? layouts decls k = some t → t.kind = k
  | _, [], _, _, h => nomatch h
  | layouts, d :: rest, k, t, h => by
    unfold findContainerElemTyWithKind? at h
    dsimp only at h
    split at h
    · split at h
      · exact findContainerElemTyWithKind?_kind layouts rest k t h
      · split at h
        · injection h with ht; rw [← ht]
        · exact findContainerElemTyWithKind?_kind layouts rest k t h
    · exact findContainerElemTyWithKind?_kind layouts rest k t h

private theorem findDeclOrContainerElemTyWithKind?_rel
    (localDecls : List LocalDecl) (layouts : LayoutTable) (k : RigidTy) (t : Ty)
    (h : findDeclOrContainerElemTyWithKind? localDecls layouts k = some t) :
    ProjShapeRel k t.kind := by
  unfold findDeclOrContainerElemTyWithKind? at h
  cases hd : findDeclTyWithKind? localDecls k with
  | some declTy =>
    rw [hd] at h
    injection h with ht
    rw [← ht]
    exact findDeclTyWithKind?_rel localDecls k declTy hd
  | none =>
    rw [hd] at h
    rw [findContainerElemTyWithKind?_kind layouts localDecls k t h]
    exact .refl k

private theorem resolveTyWithLocalDecls_kind
    (localDecls : List LocalDecl) (layouts : LayoutTable) (ty : Ty) :
    (resolveTyWithLocalDecls localDecls layouts ty).kind = ty.kind := by
  unfold resolveTyWithLocalDecls
  split
  · rfl
  · split
    · rfl
    · split <;> try rfl
      split <;> rfl

private theorem ProjShapeRel.pointee {b₁ b₂ : Ty} (h : ProjShapeRel b₁.kind b₂.kind) :
    (pointeeTyOf b₁ = none ∧ pointeeTyOf b₂ = none) ∨
      ∃ p₁ p₂, pointeeTyOf b₁ = some { kind := p₁, layoutIdx := 0 } ∧
        pointeeTyOf b₂ = some { kind := p₂, layoutIdx := 0 } ∧ ProjShapeRel p₁ p₂ := by
  rcases b₁ with ⟨k₁, i₁⟩
  rcases b₂ with ⟨k₂, i₂⟩
  dsimp only at h
  cases h with
  | refl =>
    cases k₁ with
    | ref _ inner => exact Or.inr ⟨inner, inner, rfl, rfl, .refl inner⟩
    | rawPtr _ inner => exact Or.inr ⟨inner, inner, rfl, rfl, .refl inner⟩
    | adt d args =>
      cases args with
      | nil => exact Or.inl ⟨rfl, rfl⟩
      | cons inner rest =>
        cases rest with
        | cons _ _ => exact Or.inl ⟨rfl, rfl⟩
        | nil =>
          unfold pointeeTyOf
          dsimp only
          cases Bool.or (stringEq d "std::boxed::Box") (stringEq d "alloc::boxed::Box") with
          | false => exact Or.inl ⟨rfl, rfl⟩
          | true => exact Or.inr ⟨inner, inner, rfl, rfl, .refl inner⟩
    | _ => exact Or.inl ⟨rfl, rfl⟩
  | array _ _ _ => exact Or.inl ⟨rfl, rfl⟩
  | slice _ => exact Or.inl ⟨rfl, rfl⟩
  | ref hp => exact Or.inr ⟨_, _, rfl, rfl, hp⟩
  | rawPtr hp => exact Or.inr ⟨_, _, rfl, rfl, hp⟩
  | adtBox hStr hp =>
    unfold pointeeTyOf
    dsimp only
    rw [hStr "std::boxed::Box", hStr "alloc::boxed::Box"]
    cases Bool.or (stringEq _ "std::boxed::Box") (stringEq _ "alloc::boxed::Box") with
    | false => exact Or.inl ⟨rfl, rfl⟩
    | true => exact Or.inr ⟨_, _, rfl, rfl, hp⟩
  | leaf _ _ hP₁ hP₂ => exact Or.inl ⟨hP₁, hP₂⟩

private theorem ProjShapeRel.elem {b₁ b₂ : Ty} (h : ProjShapeRel b₁.kind b₂.kind) :
    (elemTyOf b₁ = none ∧ elemTyOf b₂ = none) ∨
      ∃ e₁ e₂, elemTyOf b₁ = some { kind := e₁, layoutIdx := 0 } ∧
        elemTyOf b₂ = some { kind := e₂, layoutIdx := 0 } ∧ ProjShapeRel e₁ e₂ := by
  rcases b₁ with ⟨k₁, i₁⟩
  rcases b₂ with ⟨k₂, i₂⟩
  dsimp only at h
  cases h with
  | refl =>
    cases k₁ with
    | array e _ => exact Or.inr ⟨e, e, rfl, rfl, .refl e⟩
    | slice e => exact Or.inr ⟨e, e, rfl, rfl, .refl e⟩
    | _ => exact Or.inl ⟨rfl, rfl⟩
  | array _ _ he => exact Or.inr ⟨_, _, rfl, rfl, he⟩
  | slice he => exact Or.inr ⟨_, _, rfl, rfl, he⟩
  | ref _ => exact Or.inl ⟨rfl, rfl⟩
  | rawPtr _ => exact Or.inl ⟨rfl, rfl⟩
  | adtBox _ _ => exact Or.inl ⟨rfl, rfl⟩
  | leaf hArr hSl _ _ =>
    have hE₁ : elemTyOf { kind := k₁, layoutIdx := i₁ } = none := by
      cases k₁ with
      | array _ _ => exact absurd rfl (hArr _ _).1
      | slice _ => exact absurd rfl (hSl _).1
      | _ => rfl
    have hE₂ : elemTyOf { kind := k₂, layoutIdx := i₂ } = none := by
      cases k₂ with
      | array _ _ => exact absurd rfl (hArr _ _).2
      | slice _ => exact absurd rfl (hSl _).2
      | _ => rfl
    exact Or.inl ⟨hE₁, hE₂⟩

private theorem resolveProjectedTy_none_imp_resolved_none
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    ∀ (proj : List ProjectionElem) (b₁ b₂ : Ty),
      ProjShapeRel b₁.kind b₂.kind →
      resolveProjectedTy layouts b₁ proj = none →
      resolveProjectedTyResolved localDecls layouts b₂ proj = none
  | [], _, _, _, hNone => nomatch hNone
  | .field fieldIdx fieldTy :: rest, _, b₂, _, hNone => by
    unfold resolveProjectedTy at hNone
    unfold resolveProjectedTyResolved
    dsimp only
    refine resolveProjectedTy_none_imp_resolved_none localDecls layouts rest fieldTy _ ?_ hNone
    split
    · exact .refl _
    · split
      · split
        · split
          · exact .refl _
          · rw [resolveTyWithLocalDecls_kind localDecls layouts fieldTy]; exact .refl _
        · rw [resolveTyWithLocalDecls_kind localDecls layouts fieldTy]; exact .refl _
      · rw [resolveTyWithLocalDecls_kind localDecls layouts fieldTy]; exact .refl _
  | .opaqueCast castTy :: rest, _, _, _, hNone => by
    unfold resolveProjectedTy at hNone
    unfold resolveProjectedTyResolved
    refine resolveProjectedTy_none_imp_resolved_none localDecls layouts rest castTy _ ?_ hNone
    rw [resolveTyWithLocalDecls_kind localDecls layouts castTy]
    exact .refl _
  | .unwrapUnsafeBinder innerTy :: rest, _, _, _, hNone => by
    unfold resolveProjectedTy at hNone
    unfold resolveProjectedTyResolved
    refine resolveProjectedTy_none_imp_resolved_none localDecls layouts rest innerTy _ ?_ hNone
    rw [resolveTyWithLocalDecls_kind localDecls layouts innerTy]
    exact .refl _
  | .downcast _ _ :: rest, b₁, b₂, hInv, hNone => by
    unfold resolveProjectedTy at hNone
    unfold resolveProjectedTyResolved
    exact resolveProjectedTy_none_imp_resolved_none localDecls layouts rest b₁ b₂ hInv hNone
  | .deref :: rest, b₁, b₂, hInv, hNone => by
    unfold resolveProjectedTy at hNone
    unfold resolveProjectedTyResolved
    rcases hInv.pointee with ⟨_, hPt₂⟩ | ⟨p₁, p₂, hPt₁, hPt₂, hRelP⟩
    · rw [hPt₂]
    · rw [hPt₁] at hNone
      rw [hPt₂]
      dsimp only
      have hInnerRel :
          ProjShapeRel p₂
            ((match findDeclOrContainerElemTyWithKind? localDecls layouts p₂ with
              | .some declTy => declTy
              | .none =>
                match LayoutTable.lookup layouts b₂.layoutIdx with
                | .some { size := pSz, fields := .primitive, fieldLayouts := flIdx :: .nil, .. } =>
                  match
                    Bool.and
                      (Nat.beq pSz.bytes (layoutPointerBytes layouts))
                      (Nat.ble (.succ flIdx) (length layouts.entries))
                  with
                  | true => { kind := p₂, layoutIdx := flIdx }
                  | false => { kind := p₂, layoutIdx := synthKindLayoutIdx layouts p₂ }
                | _ => { kind := p₂, layoutIdx := synthKindLayoutIdx layouts p₂ }) : Ty).kind := by
        cases hFind : findDeclOrContainerElemTyWithKind? localDecls layouts p₂ with
        | some declTy =>
          exact findDeclOrContainerElemTyWithKind?_rel localDecls layouts p₂ declTy hFind
        | none =>
          dsimp only
          split <;> try exact .refl p₂
          split <;> exact .refl p₂
      exact resolveProjectedTy_none_imp_resolved_none localDecls layouts rest
        { kind := p₁, layoutIdx := 0 } _ (hRelP.trans hInnerRel) hNone
  | .index _ :: rest, b₁, b₂, hInv, hNone => by
    unfold resolveProjectedTy at hNone
    unfold resolveProjectedTyResolved
    rcases hInv.elem with ⟨_, hEl₂⟩ | ⟨e₁, e₂, hEl₁, hEl₂, hRelE⟩
    · rw [hEl₂]
    · rw [hEl₁] at hNone
      rw [hEl₂]
      dsimp only
      have hElemRel :
          ProjShapeRel e₂
            ((match LayoutTable.lookup layouts b₂.layoutIdx with
              | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
                { kind := e₂, layoutIdx := flIdx }
              | _ =>
                match findDeclOrContainerElemTyWithKind? localDecls layouts e₂ with
                | .some declTy => declTy
                | .none => { kind := e₂, layoutIdx := synthKindLayoutIdx layouts e₂ }) : Ty).kind := by
        split
        · exact .refl e₂
        · cases hFind : findDeclOrContainerElemTyWithKind? localDecls layouts e₂ with
          | some declTy =>
            exact findDeclOrContainerElemTyWithKind?_rel localDecls layouts e₂ declTy hFind
          | none => exact .refl e₂
      exact resolveProjectedTy_none_imp_resolved_none localDecls layouts rest
        { kind := e₁, layoutIdx := 0 } _ (hRelE.trans hElemRel) hNone
  | .constantIndex _ _ _ :: rest, b₁, b₂, hInv, hNone => by
    unfold resolveProjectedTy at hNone
    unfold resolveProjectedTyResolved
    rcases hInv.elem with ⟨_, hEl₂⟩ | ⟨e₁, e₂, hEl₁, hEl₂, hRelE⟩
    · rw [hEl₂]
    · rw [hEl₁] at hNone
      rw [hEl₂]
      dsimp only
      have hElemRel :
          ProjShapeRel e₂
            ((match LayoutTable.lookup layouts b₂.layoutIdx with
              | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
                { kind := e₂, layoutIdx := flIdx }
              | _ =>
                match findDeclOrContainerElemTyWithKind? localDecls layouts e₂ with
                | .some declTy => declTy
                | .none => { kind := e₂, layoutIdx := synthKindLayoutIdx layouts e₂ }) : Ty).kind := by
        split
        · exact .refl e₂
        · cases hFind : findDeclOrContainerElemTyWithKind? localDecls layouts e₂ with
          | some declTy =>
            exact findDeclOrContainerElemTyWithKind?_rel localDecls layouts e₂ declTy hFind
          | none => exact .refl e₂
      exact resolveProjectedTy_none_imp_resolved_none localDecls layouts rest
        { kind := e₁, layoutIdx := 0 } _ (hRelE.trans hElemRel) hNone
  | .subslice fromIdx toIdx fromEnd :: rest, b₁, b₂, hInv, hNone => by
    rcases b₁ with ⟨k₁, i₁⟩
    rcases b₂ with ⟨k₂, i₂⟩
    dsimp only at hInv
    unfold resolveProjectedTy at hNone
    unfold resolveProjectedTyResolved
    dsimp only
    cases k₂ with
    | array ek arrLen =>
      dsimp only
      have hb₁Arr : ∃ e₁ n₁, k₁ = .array e₁ n₁ ∧ ProjShapeRel e₁ ek := by
        cases hInv with
        | refl => exact ⟨ek, arrLen, rfl, .refl ek⟩
        | array n₁ _ he => exact ⟨_, n₁, rfl, he⟩
        | leaf hArr _ _ _ => exact absurd rfl (hArr _ _).2
      obtain ⟨e₁, n₁, rfl, hRelE⟩ := hb₁Arr
      split
      · rfl
      · split
        · rfl
        · split
          · exact resolveProjectedTy_none_imp_resolved_none localDecls layouts rest _ _
              (.array n₁ arrLen hRelE) hNone
          · split
            · exact resolveProjectedTy_none_imp_resolved_none localDecls layouts _ _ _
                (.array n₁ arrLen hRelE) hNone
            · exact resolveProjectedTy_none_imp_resolved_none localDecls layouts _ _ _
                (.array n₁ arrLen hRelE) hNone
            · refine resolveProjectedTy_none_imp_resolved_none localDecls layouts _ _ _ ?_ hNone
              dsimp only
              rw [resolveTyWithLocalDecls_kind localDecls layouts _]
              exact .array n₁ _ hRelE
    | slice ek =>
      dsimp only
      split
      · rfl
      · exact resolveProjectedTy_none_imp_resolved_none localDecls layouts rest _ _ hInv hNone
    | bool | char | int _ | uint _ | float _ | never | str | tuple _ | ref _ _ | rawPtr _ _
    | adt _ _ | fnDef _ _ | fnPtr _ _ _ _ | closure _ _ | dynamic _ | foreign _ | param _ _
    | alias _ _ | other _ => rfl

/-- Whenever `placeTy localDecls layouts place = none`, `placeTyResolved localDecls layouts place`
is also `none` (`resolveProjectedTyResolved` refines layout indices and `.subslice` bounds without
ever fabricating a type along a projection chain rejected by `resolveProjectedTy`). -/
theorem placeTy_eq_none_imp_placeTyResolved_eq_none
    (localDecls : List LocalDecl) (layouts : LayoutTable) (place : Place)
    (hTy : placeTy localDecls layouts place = none) :
    placeTyResolved localDecls layouts place = none := by
  unfold placeTy at hTy
  unfold placeTyResolved
  cases hDecl : get? localDecls place.local_ with
  | none => rfl
  | some decl =>
    rw [hDecl] at hTy
    exact resolveProjectedTy_none_imp_resolved_none localDecls layouts place.projection
      decl.ty decl.ty (.refl _) hTy

/-- **Agreement with Trusted's `evalPlaceDiscriminant`**: whenever `evalAdtDiscriminant`
succeeds on an initialized aggregate, Trusted's `Rvalue.discriminant` evaluation of the same
value (with no layout information for the place) succeeds with the variant index as an 8-byte
scalar, and Anneal's result is that variant's declared discriminant (equal to the variant index
for the default sequential discriminants `0, 1, 2, …`). -/
theorem evalAdtDiscriminant_init_agrees_trusted (spec : AdtDiscrSpec) (wf : Value → Bool)
    (hEnum : spec.isEnum = true) {v : Nat} {fields : List Value} {d : Nat}
    (h : evalAdtDiscriminant spec wf (.init (.aggregate v fields)) = some d)
    (locals' : List LocalSlot) (mem : Memory) (place : Place) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (hTy : placeTy localDecls layouts place = none) :
    evalPlaceDiscriminant (.aggregate v fields) locals' mem place localDecls layouts =
        .ok (.scalar ⟨v, 8⟩) locals' mem ∧
      spec.discriminants[v]? = some d ∧
      (spec.discriminants = List.range spec.discriminants.length → d = v) := by
  have hD : spec.discriminants[v]? = some d := by
    simp only [evalAdtDiscriminant] at h
    split at h
    · nomatch h
    · simp only [discriminantValue?, hEnum, ↓reduceIte] at h
      split at h
      · rename_i d' _ hD
        simp only [Option.some.injEq] at h
        subst h
        exact hD
      · nomatch h
  have hTyRes := placeTy_eq_none_imp_placeTyResolved_eq_none localDecls layouts place hTy
  refine ⟨by simp [evalPlaceDiscriminant, hTyRes], hD, fun hSeq => ?_⟩
  have hLt : v < spec.discriminants.length := (List.getElem?_eq_some_iff.mp hD).1
  rw [hSeq, List.getElem?_range (by simpa using hLt)] at hD
  simpa using hD.symm

/-! ## Section 2: Projected `Deinit`, `Retag`, `CopyNonOverlapping`, and Pointer-Like Rvalues -/

/-! ### Section 2a: The projected `Deinit` evaluator -/

/-- Every field slot of a shell is uninitialized. -/
def allFieldsUninit : List FieldSlot → Bool
  | [] => true
  | .uninit :: rest => allFieldsUninit rest
  | .init _ :: _ => false
  | .nested _ _ _ _ :: _ => false

/-- `normalize_slot` on a shell: a complete shell is promoted to `.init` (`try_into_mir_value`);
an empty shell — no initialized field and no tag that matters (`PartialAggregate::is_empty`,
where for the untyped shells of this model only an enum shell's written tag matters) —
collapses to `.uninit`; any other shell is kept. -/
def normalizeShell (shell : PartialAggregate) : FieldSlot :=
  match shell.tryIntoValue? with
  | some v => .init v
  | none =>
    match (!shell.isAdt || !shell.discriminantSet) && allFieldsUninit shell.fields with
    | true => .uninit
    | false => shell.toFieldSlot

/-- `explode_init_slot` on an initialized aggregate: the equivalent complete shell (every field
initialized and the tag counted as written), which `normalizeShell` turns back into the value. -/
def explodeAggregate (variantIdx : Nat) (vals : List Value) : PartialAggregate :=
  ⟨variantIdx, true, true, vals.map .init⟩

/-- `validate_projection_tail` for a `Deinit` below an uninitialized part (where it changes
nothing), over this untyped model: no `Deref` (`UnsupportedPlaceProjection`), every `Downcast`
immediately followed by a `Field`, no `OpaqueCast`/`UnwrapUnsafeBinder`, every `Index` operand
an initialized scalar local (the statement's pre-read index cache), and static `ConstantIndex` /
`Subslice` bounds (`IndexOutOfBounds`). The untyped model has no array type, so the bounds of
`resolve_constant_index` / `resolve_subslice_range` are checked against `min_length` standing for
the array length (which is what `rustc` emits for arrays: `min_length` is the exact length), and
the array-length side of `Subslice` and of `Index` is not checked. -/
def deinitTailOk (locals : List LocalSlot) : List ProjectionElem → Bool
  | [] => true
  | .field _ _ :: rest => deinitTailOk locals rest
  | .downcast _ _ :: .field _ _ :: rest => deinitTailOk locals rest
  | .index i :: rest =>
    match get? locals i with
    | some (.init (.scalar _)) => deinitTailOk locals rest
    | _ => false
  | .constantIndex offset minLen fromEnd :: rest =>
    (if fromEnd then decide (1 ≤ offset ∧ offset ≤ minLen) else decide (offset < minLen)) &&
      deinitTailOk locals rest
  | .subslice from_ to_ fromEnd :: rest =>
    (fromEnd || decide (from_ ≤ to_)) && deinitTailOk locals rest
  | _ :: _ => false

/-- One `Field` step of `deinit_in_slot` on the (possibly just exploded) shell `shell`, where
`downcast` is the pending `Downcast` variant: the shell must be narrowed to the expected variant
(`InactiveVariantProjection`), the field must exist (`FieldOutOfBounds`), the child is
deinitialized by `child`, and below a `Downcast` a tag that does not survive field
deinitialization (`AdtDef::tag_survives_field_deinit`, `A3`) is forgotten
(`discriminant_set = false`). The result is normalized (`normalize_slot`). -/
def deinitShellStep (tagSurvives : Bool) (shell : PartialAggregate) (downcast : Option Nat)
    (idx : Nat) (child : FieldSlot → Option FieldSlot) : Option FieldSlot :=
  if shellVariant shell = downcast.getD 0 then
    match shell.fields[idx]? with
    | none => none
    | some c =>
      match child c with
      | none => none
      | some c' =>
        some (normalizeShell
          { shell with
            discriminantSet := shell.discriminantSet && (downcast.isNone || tagSurvives)
            fields := shell.fields.set idx c' })
  else none

/-- `deinit_in_slot`: writes "uninitialized" over the part `proj` of `slot`.
- `proj = []` makes the slot `.uninit`;
- below an uninitialized part nothing changes, but the place must be well formed
  (`deinitTailOk`);
- an initialized aggregate is exploded into a complete shell (`explode_init_slot`) and a
  `Field` (variant `0`) or `Downcast(v)` + `Field` step recurses into the field;
- a shell recurses the same way (`InactiveVariantProjection` on a variant mismatch);
- `Deref`, array projections on values or shells, a `Field` of a non-aggregate, and a
  `Downcast` not followed by a `Field` fail (`none`).
`tagSurvives` is `AdtDef::tag_survives_field_deinit` of the enum the place's `Downcast`s
narrow. -/
def deinitFieldSlot (tagSurvives : Bool) (locals : List LocalSlot) :
    FieldSlot → List ProjectionElem → Option FieldSlot
  | _, [] => some .uninit
  | .uninit, p :: rest => if deinitTailOk locals (p :: rest) then some .uninit else none
  | .init (.aggregate var vals), .field idx _ :: rest =>
    deinitShellStep tagSurvives (explodeAggregate var vals) none idx
      (fun c => deinitFieldSlot tagSurvives locals c rest)
  | .init (.aggregate var vals), .downcast _ v :: .field idx _ :: rest =>
    deinitShellStep tagSurvives (explodeAggregate var vals) (some v) idx
      (fun c => deinitFieldSlot tagSurvives locals c rest)
  | .nested var adt disc fs, .field idx _ :: rest =>
    deinitShellStep tagSurvives ⟨var, adt, disc, fs⟩ none idx
      (fun c => deinitFieldSlot tagSurvives locals c rest)
  | .nested var adt disc fs, .downcast _ v :: .field idx _ :: rest =>
    deinitShellStep tagSurvives ⟨var, adt, disc, fs⟩ (some v) idx
      (fun c => deinitFieldSlot tagSurvives locals c rest)
  | _, _ :: _ => none

/-- The `FieldSlot` view of a live local (`take_root_slot`). -/
def slotStateToFieldSlot : LocalSlotState → FieldSlot
  | .dead => .uninit
  | .uninit => .uninit
  | .partialShell shell => shell.toFieldSlot
  | .init v => .init v

/-- `StatementEvalState::deinit_place`: a dead (or missing) local faults (`DeadLocal`); the
bare local becomes `.uninit`; a projected place is deinitialized in the root slot by
`deinitFieldSlot` and the normalized slot is written back (`root_slot_state`). -/
def evalDeinitPlace (tagSurvives : Bool) (slots : List LocalSlotState) (place : Place) :
    Option (List LocalSlotState) :=
  match slots[place.local_]? with
  | none => none
  | some .dead => none
  | some st =>
    match place.projection with
    | [] => some (slots.set place.local_ .uninit)
    | p :: rest =>
      match deinitFieldSlot tagSurvives (slotsToTrustedLocals slots)
          (slotStateToFieldSlot st) (p :: rest) with
      | none => none
      | some slot' => some (slots.set place.local_ (fieldSlotToLocalSlotState slot'))

/-- Reading the part `q` of a field slot (`read_place` below the root): an uninitialized part
faults, an initialized one is read by `evalValueProjRead`, and a shell by
`readFromPartialShell`. -/
def readFieldSlot (locals : List LocalSlot) : FieldSlot → List ProjectionElem → ProjReadResult
  | .uninit, _ => .ub
  | .init v, q => evalValueProjRead locals v q
  | .nested var adt disc fs, q => readFromPartialShell locals ⟨var, adt, disc, fs⟩ q

/-- Case analysis on a `Nat.beq` test, as a decidable `if`. -/
theorem beq_cases (a b : Nat) : (Nat.beq a b = true ∧ a = b) ∨ (Nat.beq a b = false ∧ a ≠ b) := by
  cases hB : Nat.beq a b with
  | true => exact Or.inl ⟨rfl, Nat.eq_of_beq_eq_true hB⟩
  | false => exact Or.inr ⟨rfl, Nat.ne_of_beq_eq_false hB⟩

/-- `readFromPartialShell` on a `Field` step dispatches to the field's slot. -/
theorem readFromPartialShell_field (locals : List LocalSlot) (shell : PartialAggregate)
    (idx : Nat) (ty : Ty) (rest : List ProjectionElem) :
    readFromPartialShell locals shell (.field idx ty :: rest) =
      if shellVariant shell = 0 then
        match shell.fields[idx]? with
        | some c => readFieldSlot locals c rest
        | none => .ub
      else .ub := by
  obtain ⟨var, adt, disc, fs⟩ := shell
  have hFs : (match get? fs idx with
      | some (.init fieldVal) => evalValueProjRead locals fieldVal rest
      | some (.nested cVar cAdt cDisc cFields) =>
        readFromPartialShell locals ⟨cVar, cAdt, cDisc, cFields⟩ rest
      | some .uninit => ProjReadResult.ub
      | none => ProjReadResult.ub) =
      (match fs[idx]? with
      | some c => readFieldSlot locals c rest
      | none => .ub) := by
    rw [get?_eq_getElem?]
    cases fs[idx]? with
    | none => rfl
    | some c => cases c <;> rfl
  cases adt with
  | true =>
    rcases beq_cases var 0 with ⟨hB, hE⟩ | ⟨hB, hE⟩
    · subst hE
      simp only [readFromPartialShell, shellVariant, show Nat.beq 0 0 = true from rfl, ↓reduceIte]
      exact hFs
    · simp only [readFromPartialShell, shellVariant, hB, hE, ↓reduceIte]
  | false =>
    simp only [readFromPartialShell, shellVariant, show Nat.beq 0 0 = true from rfl, ↓reduceIte]
    exact hFs

/-- `readFromPartialShell` on a `Downcast(v)` + `Field` step dispatches to the field's slot of
a shell narrowed to `v`. -/
theorem readFromPartialShell_downcast_field (locals : List LocalSlot) (shell : PartialAggregate)
    (n : Option String) (v idx : Nat) (ty : Ty) (rest : List ProjectionElem) :
    readFromPartialShell locals shell (.downcast n v :: .field idx ty :: rest) =
      if shellVariant shell = v then
        match shell.fields[idx]? with
        | some c => readFieldSlot locals c rest
        | none => .ub
      else .ub := by
  obtain ⟨var, adt, disc, fs⟩ := shell
  have hFs : (match get? fs idx with
      | some (.init fieldVal) => evalValueProjRead locals fieldVal rest
      | some (.nested cVar cAdt cDisc cFields) =>
        readFromPartialShell locals ⟨cVar, cAdt, cDisc, cFields⟩ rest
      | some .uninit => ProjReadResult.ub
      | none => ProjReadResult.ub) =
      (match fs[idx]? with
      | some c => readFieldSlot locals c rest
      | none => .ub) := by
    rw [get?_eq_getElem?]
    cases fs[idx]? with
    | none => rfl
    | some c => cases c <;> rfl
  cases adt with
  | true =>
    rcases beq_cases var v with ⟨hB, hE⟩ | ⟨hB, hE⟩
    · subst hE
      simp only [readFromPartialShell, shellVariant, isFieldHead, Bool.true_and, Nat.beq_refl,
        ↓reduceIte]
      exact hFs
    · simp only [readFromPartialShell, shellVariant, isFieldHead, Bool.true_and, hB, hE,
        ↓reduceIte]
  | false =>
    rcases beq_cases 0 v with ⟨hB, hE⟩ | ⟨hB, hE⟩
    · subst hE
      simp only [readFromPartialShell, shellVariant, isFieldHead, Bool.true_and, Nat.beq_refl,
        ↓reduceIte]
      exact hFs
    · simp only [readFromPartialShell, shellVariant, isFieldHead, Bool.true_and, hB, hE,
        ↓reduceIte]

/-- `evalValueProjRead` on a `Field` step of an aggregate reads the field. -/
theorem evalValueProjRead_aggregate_field (locals : List LocalSlot) (var : Nat)
    (vals : List Value) (idx : Nat) (ty : Ty) (rest : List ProjectionElem) :
    evalValueProjRead locals (.aggregate var vals) (.field idx ty :: rest) =
      match vals[idx]? with
      | some fv => evalValueProjRead locals fv rest
      | none => .ub := by
  simp only [evalValueProjRead, ← get?_eq_getElem?]
  cases get? vals idx <;> rfl

/-- `evalValueProjRead` on a `Downcast(v)` + `Field` step of an aggregate of variant `var`
reads the field when `var = v`. -/
theorem evalValueProjRead_aggregate_downcast_field (locals : List LocalSlot) (var : Nat)
    (vals : List Value) (n : Option String) (v idx : Nat) (ty : Ty) (rest : List ProjectionElem) :
    evalValueProjRead locals (.aggregate var vals) (.downcast n v :: .field idx ty :: rest) =
      if var = v then
        match vals[idx]? with
        | some fv => evalValueProjRead locals fv rest
        | none => .ub
      else .ub := by
  rcases beq_cases var v with ⟨hB, hE⟩ | ⟨hB, hE⟩
  · simp only [evalValueProjRead, isFieldHead, Bool.true_and]
    rw [hB]
    simp only [hE, ↓reduceIte, ← get?_eq_getElem?]
    cases get? vals idx <;> rfl
  · simp only [evalValueProjRead, isFieldHead, Bool.true_and]
    rw [hB]
    simp only [hE, ↓reduceIte]

/-- `q` is a prefix or an extension of `p`: the paths a `Deinit` at `p` makes unreadable. -/
def PathComparable (p q : List ProjectionElem) : Prop :=
  (∃ s, q = p ++ s) ∨ (∃ s, p = q ++ s)

/-- Comparable non-empty paths agree on their first element. -/
theorem PathComparable.cons {a b : ProjectionElem} {p q : List ProjectionElem}
    (h : PathComparable (a :: p) (b :: q)) : b = a ∧ PathComparable p q := by
  rcases h with ⟨s, hs⟩ | ⟨s, hs⟩
  · simp only [List.cons_append, List.cons.injEq] at hs
    exact ⟨hs.1, Or.inl ⟨s, hs.2⟩⟩
  · simp only [List.cons_append, List.cons.injEq] at hs
    exact ⟨hs.1.symm, Or.inr ⟨s, hs.2⟩⟩

/-- The shape a `Deinit` at `proj` leaves behind: the slot is uninitialized along `proj`, i.e.
every node on the path is a shell narrowed to the path's variant, down to an uninitialized
part (which may also be an uninitialized ancestor). -/
def UninitAt : FieldSlot → List ProjectionElem → Prop
  | .uninit, _ => True
  | .nested var adt disc fs, .field idx _ :: rest =>
    shellVariant ⟨var, adt, disc, fs⟩ = 0 ∧ ∃ c, fs[idx]? = some c ∧ UninitAt c rest
  | .nested var adt disc fs, .downcast _ v :: .field idx _ :: rest =>
    shellVariant ⟨var, adt, disc, fs⟩ = v ∧ ∃ c, fs[idx]? = some c ∧ UninitAt c rest
  | _, _ => False

/-- An initialized slot is not uninitialized anywhere. -/
theorem UninitAt.not_init {v : Value} {p : List ProjectionElem} : ¬ UninitAt (.init v) p := by
  intro h
  cases p <;> simp only [UninitAt] at h

/-- A shell with a non-initialized field does not promote. -/
theorem tryIntoValue?_eq_none_of_getElem? {shell : PartialAggregate} {idx : Nat} {c : FieldSlot}
    (hc : shell.fields[idx]? = some c) (hNI : ∀ v, c ≠ .init v) : shell.tryIntoValue? = none := by
  cases h : shell.tryIntoValue? with
  | none => rfl
  | some out =>
    obtain ⟨_, vals, hF, _⟩ := (tryIntoValue?_eq_some_iff shell out).mp h
    rw [hF, List.getElem?_map] at hc
    cases hv : vals[idx]? with
    | none => rw [hv] at hc; nomatch hc
    | some w =>
      rw [hv] at hc
      simp only [Option.map_some, Option.some.injEq] at hc
      exact absurd hc.symm (hNI w)

/-- A shell that does not promote normalizes to `.uninit` (when empty) or stays a shell. -/
theorem normalizeShell_of_tryIntoValue?_none {shell : PartialAggregate}
    (h : shell.tryIntoValue? = none) :
    (normalizeShell shell = .uninit ∧
        ((!shell.isAdt || !shell.discriminantSet) && allFieldsUninit shell.fields) = true) ∨
      normalizeShell shell = shell.toFieldSlot := by
  unfold normalizeShell
  rw [h]
  cases hc : ((!shell.isAdt || !shell.discriminantSet) && allFieldsUninit shell.fields) with
  | true => exact Or.inl ⟨rfl, rfl⟩
  | false => exact Or.inr rfl

/-- Every field of an all-uninitialized field list is uninitialized. -/
theorem allFieldsUninit_getElem? : ∀ {fs : List FieldSlot} {i : Nat} {c : FieldSlot},
    allFieldsUninit fs = true → fs[i]? = some c → c = .uninit
  | [], _, _, _, h => by simp at h
  | .uninit :: _, 0, _, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    exact h.symm
  | .uninit :: rest, i + 1, _, hA, h =>
    allFieldsUninit_getElem? (fs := rest) hA (by simpa using h)
  | .init _ :: _, _, _, hA, _ => by simp [allFieldsUninit] at hA
  | .nested _ _ _ _ :: _, _, _, hA, _ => by simp [allFieldsUninit] at hA

/-- Inversion of a successful `deinitShellStep`. -/
theorem deinitShellStep_eq_some {ts : Bool} {shell : PartialAggregate} {dc : Option Nat}
    {idx : Nat} {child : FieldSlot → Option FieldSlot} {r : FieldSlot}
    (h : deinitShellStep ts shell dc idx child = some r) :
    shellVariant shell = dc.getD 0 ∧ ∃ c c', shell.fields[idx]? = some c ∧ child c = some c' ∧
      r = normalizeShell { shell with
        discriminantSet := shell.discriminantSet && (dc.isNone || ts)
        fields := shell.fields.set idx c' } := by
  unfold deinitShellStep at h
  split at h
  · rename_i hV
    split at h
    · nomatch h
    · rename_i c hc
      split at h
      · nomatch h
      · rename_i c' hcc
        exact ⟨hV, c, c', hc, hcc, (Option.some.inj h).symm⟩
  · nomatch h

/-- After a shell step whose child is uninitialized along `rest`, the normalized shell is
`.uninit` or the updated shell holding that child. -/
theorem normalizeShell_step_cases {shell : PartialAggregate} {idx : Nat} {c c' : FieldSlot}
    {disc' : Bool} {rest : List ProjectionElem} (hc : shell.fields[idx]? = some c)
    (hU : UninitAt c' rest) :
    normalizeShell { shell with discriminantSet := disc', fields := shell.fields.set idx c' } =
        .uninit ∨
      (normalizeShell { shell with discriminantSet := disc', fields := shell.fields.set idx c' } =
          .nested shell.variantIdx shell.isAdt disc' (shell.fields.set idx c') ∧
        (shell.fields.set idx c')[idx]? = some c') := by
  have hLt : idx < shell.fields.length := (List.getElem?_eq_some_iff.mp hc).1
  have hGet : (shell.fields.set idx c')[idx]? = some c' := by
    simp [List.getElem?_set_self hLt]
  have hNone : ({ shell with discriminantSet := disc', fields := shell.fields.set idx c' } :
      PartialAggregate).tryIntoValue? = none :=
    tryIntoValue?_eq_none_of_getElem? hGet (fun v hv => UninitAt.not_init (hv ▸ hU))
  rcases normalizeShell_of_tryIntoValue?_none hNone with ⟨h1, _⟩ | h2
  · exact Or.inl h1
  · exact Or.inr ⟨h2, hGet⟩

/-- **`Deinit` leaves its place uninitialized**: a successful `deinitFieldSlot` at `proj`
produces a slot that is uninitialized along `proj` (`UninitAt`). -/
theorem deinitFieldSlot_uninitAt (ts : Bool) (locals : List LocalSlot) (slot : FieldSlot)
    (p : List ProjectionElem) (slot' : FieldSlot)
    (h : deinitFieldSlot ts locals slot p = some slot') : UninitAt slot' p := by
  fun_induction deinitFieldSlot ts locals slot p generalizing slot' with
  | case1 => cases h; trivial
  | case2 => cases h; trivial
  | case3 => nomatch h
  | case4 var vals idx ty rest ih =>
    obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    have hU := ih c c' hcc
    rcases normalizeShell_step_cases hc hU with h1 | ⟨h2, hGet⟩
    · rw [h1]; trivial
    · rw [h2]; simp only [UninitAt]; exact ⟨hV, c', hGet, hU⟩
  | case5 var vals n v idx ty rest ih =>
    obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    have hU := ih c c' hcc
    rcases normalizeShell_step_cases hc hU with h1 | ⟨h2, hGet⟩
    · rw [h1]; trivial
    · rw [h2]; simp only [UninitAt]; exact ⟨hV, c', hGet, hU⟩
  | case6 var adt disc fs idx ty rest ih =>
    obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    have hU := ih c c' hcc
    rcases normalizeShell_step_cases hc hU with h1 | ⟨h2, hGet⟩
    · rw [h1]; trivial
    · rw [h2]; simp only [UninitAt]; exact ⟨hV, c', hGet, hU⟩
  | case7 var adt disc fs n v idx ty rest ih =>
    obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    have hU := ih c c' hcc
    rcases normalizeShell_step_cases hc hU with h1 | ⟨h2, hGet⟩
    · rw [h1]; trivial
    · rw [h2]; simp only [UninitAt]; exact ⟨hV, c', hGet, hU⟩
  | case8 => nomatch h

/-- A shell that is uninitialized along a path does not promote to a value. -/
theorem UninitAt.nested_tryIntoValue?_none {var : Nat} {adt disc : Bool} {fs : List FieldSlot}
    {p : List ProjectionElem} (h : UninitAt (.nested var adt disc fs) p) :
    (⟨var, adt, disc, fs⟩ : PartialAggregate).tryIntoValue? = none := by
  rcases p with _ | ⟨a, rest⟩
  · simp only [UninitAt] at h
  · cases a
    case field idx ty =>
      simp only [UninitAt] at h
      obtain ⟨_, c, hc, hU⟩ := h
      exact tryIntoValue?_eq_none_of_getElem? (shell := ⟨var, adt, disc, fs⟩) hc
        (fun v hv => UninitAt.not_init (hv ▸ hU))
    case downcast n v =>
      rcases rest with _ | ⟨b, rest⟩
      · simp only [UninitAt] at h
      · cases b
        case field idx ty =>
          simp only [UninitAt] at h
          obtain ⟨_, c, hc, hU⟩ := h
          exact tryIntoValue?_eq_none_of_getElem? (shell := ⟨var, adt, disc, fs⟩) hc
            (fun v hv => UninitAt.not_init (hv ▸ hU))
        all_goals simp only [UninitAt] at h
    all_goals simp only [UninitAt] at h

/-- Fuel form of `readFieldSlot_eq_ub_of_uninitAt` (induction on the path length). -/
theorem readFieldSlot_eq_ub_of_uninitAt_aux (locals : List LocalSlot) :
    ∀ (n : Nat) (p : List ProjectionElem), p.length ≤ n → ∀ (slot : FieldSlot)
      (q : List ProjectionElem), UninitAt slot p → PathComparable p q →
      readFieldSlot locals slot q = .ub := by
  intro n
  induction n with
  | zero =>
    intro p hLen slot q hU _
    have hp : p = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hLen)
    subst hp
    cases slot with
    | uninit => rfl
    | init v => exact absurd hU UninitAt.not_init
    | nested var adt disc fs => simp only [UninitAt] at hU
  | succ n ih =>
    intro p hLen slot q hU hq
    cases slot with
    | uninit => rfl
    | init v => exact absurd hU UninitAt.not_init
    | nested var adt disc fs =>
      have hNone := UninitAt.nested_tryIntoValue?_none hU
      rcases p with _ | ⟨a, rest⟩
      · simp only [UninitAt] at hU
      · simp only [List.length_cons] at hLen
        cases a
        case field idx ty =>
          simp only [UninitAt] at hU
          obtain ⟨hV, c, hc, hUc⟩ := hU
          rcases q with _ | ⟨b, q'⟩
          · simp only [readFieldSlot, readFromPartialShell, hNone]
          · obtain ⟨rfl, hq'⟩ := hq.cons
            simp only [readFieldSlot, readFromPartialShell_field, hV, ↓reduceIte, hc]
            exact ih rest (by omega) c q' hUc hq'
        case downcast nm v =>
          rcases rest with _ | ⟨b, rest⟩
          · simp only [UninitAt] at hU
          · simp only [List.length_cons] at hLen
            cases b
            case field idx ty =>
              simp only [UninitAt] at hU
              obtain ⟨hV, c, hc, hUc⟩ := hU
              rcases q with _ | ⟨b1, q'⟩
              · simp only [readFieldSlot, readFromPartialShell, hNone]
              · obtain ⟨rfl, hq1⟩ := hq.cons
                rcases q' with _ | ⟨b2, q''⟩
                · simp only [readFieldSlot, readFromPartialShell, isFieldHead, Bool.false_and]
                · obtain ⟨rfl, hq2⟩ := hq1.cons
                  simp only [readFieldSlot, readFromPartialShell_downcast_field, hV, ↓reduceIte,
                    hc]
                  exact ih rest (by omega) c q'' hUc hq2
            all_goals simp only [UninitAt] at hU
        all_goals simp only [UninitAt] at hU

/-- **Reads along a deinitialized path fault**: if `slot` is uninitialized along `p`, reading
any prefix or extension of `p` faults with `.ub`. -/
theorem readFieldSlot_eq_ub_of_uninitAt (locals : List LocalSlot) (p : List ProjectionElem)
    (slot : FieldSlot) (q : List ProjectionElem) (hU : UninitAt slot p)
    (hq : PathComparable p q) : readFieldSlot locals slot q = .ub :=
  readFieldSlot_eq_ub_of_uninitAt_aux locals p.length p (Nat.le_refl _) slot q hU hq

/-- A slot left by `Deinit` round-trips through the root-slot conversions. -/
theorem UninitAt.roundtrip {slot : FieldSlot} {p : List ProjectionElem} (h : UninitAt slot p) :
    slotStateToFieldSlot (fieldSlotToLocalSlotState slot) = slot ∧
      fieldSlotToLocalSlotState slot ≠ .dead := by
  cases slot with
  | uninit => exact ⟨rfl, by intro h; cases h⟩
  | init v => exact absurd h UninitAt.not_init
  | nested var adt disc fs =>
    have hN := UninitAt.nested_tryIntoValue?_none h
    simp only [fieldSlotToLocalSlotState, hN]
    exact ⟨rfl, by intro h; cases h⟩

/-- `readPlaceState` of a live local is `readFieldSlot` of its root slot (for a place without
`Deref`). -/
theorem readPlaceState_eq_readFieldSlot {slots : List LocalSlotState} {loc : Local}
    {st : LocalSlotState} (hSt : slots[loc]? = some st) (hLive : st ≠ .dead)
    (q : List ProjectionElem) (hNoDeref : projectionHasDeref q = false) :
    readPlaceState slots ⟨loc, q⟩ =
      readFieldSlot (slotsToTrustedLocals slots) (slotStateToFieldSlot st) q := by
  unfold readPlaceState
  simp only [hNoDeref, get?_eq_getElem?, hSt]
  cases st with
  | dead => exact absurd rfl hLive
  | uninit => rfl
  | init v => rfl
  | partialShell shell => rfl

/-- `deinitFieldSlot` at the empty path always yields `.uninit`. -/
theorem deinitFieldSlot_nil (ts : Bool) (locals : List LocalSlot) (slot : FieldSlot) :
    deinitFieldSlot ts locals slot [] = some .uninit := by
  cases slot <;> rfl

/-- Inversion of a successful `evalDeinitPlace`: the local is live and its root slot is
replaced by the result of `deinitFieldSlot` (the bare-local case is the empty path). -/
theorem evalDeinitPlace_eq_some {ts : Bool} {slots slots' : List LocalSlotState} {place : Place}
    (h : evalDeinitPlace ts slots place = some slots') :
    ∃ st, slots[place.local_]? = some st ∧ st ≠ .dead ∧
      ∃ slot', deinitFieldSlot ts (slotsToTrustedLocals slots) (slotStateToFieldSlot st)
          place.projection = some slot' ∧
        slots' = slots.set place.local_ (fieldSlotToLocalSlotState slot') := by
  unfold evalDeinitPlace at h
  split at h
  · nomatch h
  · nomatch h
  · rename_i st hNotDead hSt
    refine ⟨st, hSt, fun hD => hNotDead hD, ?_⟩
    split at h
    · rename_i hP
      refine ⟨.uninit, by rw [hP]; exact deinitFieldSlot_nil _ _ _, ?_⟩
      exact (Option.some.inj h).symm
    · rename_i p rest hP
      split at h
      · nomatch h
      · rename_i slot' hD
        refine ⟨slot', by rw [hP]; exact hD, (Option.some.inj h).symm⟩

/-- **Get-Deinit (`evalDeinitPlace_read_same_ub`)**: after a successful `Deinit` of `place`,
reading any prefix of `place` (including the whole root local `[]`) or any extension
`place.projection ++ suffix` (without `Deref`) faults with `.ub`. -/
theorem evalDeinitPlace_read_same_ub {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} (h : evalDeinitPlace ts slots place = some slots') {q : List ProjectionElem}
    (hq : PathComparable place.projection q) (hNoDeref : projectionHasDeref q = false) :
    readPlaceState slots' ⟨place.local_, q⟩ = .ub := by
  obtain ⟨st, hSt, _, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hD
  obtain ⟨hRound, hNotDead⟩ := UninitAt.roundtrip hU
  have hLt : place.local_ < slots.length := (List.getElem?_eq_some_iff.mp hSt).1
  have hGet : (slots.set place.local_ (fieldSlotToLocalSlotState slot'))[place.local_]? =
      some (fieldSlotToLocalSlotState slot') := by
    simp [List.getElem?_set_self hLt]
  rw [readPlaceState_eq_readFieldSlot hGet hNotDead q hNoDeref, hRound]
  exact readFieldSlot_eq_ub_of_uninitAt _ _ _ _ hU hq

/-- Get-Deinit, whole root local: after deinitializing any part of a local, the local as a
whole is unreadable (`tryIntoValue? = none` for its shell). -/
theorem evalDeinitPlace_read_root_ub {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} (h : evalDeinitPlace ts slots place = some slots') :
    readPlaceState slots' ⟨place.local_, []⟩ = .ub :=
  evalDeinitPlace_read_same_ub h (Or.inr ⟨place.projection, rfl⟩) rfl

/-- Get-Deinit, extensions: after `Deinit` of `place`, every `Deref`-free extension
`place.projection ++ suffix` is unreadable. -/
theorem evalDeinitPlace_read_extension_ub {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} (h : evalDeinitPlace ts slots place = some slots')
    (suffix : List ProjectionElem)
    (hNoDeref : projectionHasDeref (place.projection ++ suffix) = false) :
    readPlaceState slots' ⟨place.local_, place.projection ++ suffix⟩ = .ub :=
  evalDeinitPlace_read_same_ub h (Or.inl ⟨suffix, rfl⟩) hNoDeref

/-! ### Section 2b: Disjoint-sibling and distinct-local frames of `Deinit` -/

/-- Reading field `g` of variant `k` of a shell: the common core of `readFromPartialShell` on
`Field` (`k = 0`) and `Downcast(k)` + `Field` steps. -/
def shellFieldRead (locals : List LocalSlot) (sh : PartialAggregate) (k g : Nat)
    (q : List ProjectionElem) : ProjReadResult :=
  if shellVariant sh = k then
    match sh.fields[g]? with
    | some c => readFieldSlot locals c q
    | none => .ub
  else .ub

/-- Every field read of an all-uninitialized shell faults. -/
theorem shellFieldRead_of_allFieldsUninit {locals : List LocalSlot} {sh : PartialAggregate}
    {k g : Nat} {q : List ProjectionElem} (h : allFieldsUninit sh.fields = true) :
    shellFieldRead locals sh k g q = .ub := by
  unfold shellFieldRead
  split
  · cases hg : sh.fields[g]? with
    | none => rfl
    | some c =>
      obtain rfl := allFieldsUninit_getElem? h hg
      rfl
  · rfl

/-- Field reads of a nested shell slot. -/
theorem readFieldSlot_nested_field (locals : List LocalSlot) (var : Nat) (adt disc : Bool)
    (fs : List FieldSlot) (g : Nat) (t : Ty) (q : List ProjectionElem) :
    readFieldSlot locals (.nested var adt disc fs) (.field g t :: q) =
      shellFieldRead locals ⟨var, adt, disc, fs⟩ 0 g q := by
  simp only [readFieldSlot, readFromPartialShell_field, shellFieldRead]

/-- `Downcast(v)` + `Field` reads of a nested shell slot. -/
theorem readFieldSlot_nested_downcast_field (locals : List LocalSlot) (var : Nat)
    (adt disc : Bool) (fs : List FieldSlot) (n : Option String) (v g : Nat) (t : Ty)
    (q : List ProjectionElem) :
    readFieldSlot locals (.nested var adt disc fs) (.downcast n v :: .field g t :: q) =
      shellFieldRead locals ⟨var, adt, disc, fs⟩ v g q := by
  simp only [readFieldSlot, readFromPartialShell_downcast_field, shellFieldRead]

/-- Field reads of an initialized variant-`0` aggregate are field reads of its exploded shell. -/
theorem readFieldSlot_init_field (locals : List LocalSlot) {var : Nat} (vals : List Value)
    (hV : var = 0) (g : Nat) (t : Ty) (q : List ProjectionElem) :
    readFieldSlot locals (.init (.aggregate var vals)) (.field g t :: q) =
      shellFieldRead locals (explodeAggregate var vals) 0 g q := by
  subst hV
  simp only [readFieldSlot, evalValueProjRead_aggregate_field, shellFieldRead, explodeAggregate,
    shellVariant, ↓reduceIte, List.getElem?_map]
  cases vals[g]? <;> rfl

/-- `Downcast(v)` + `Field` reads of an initialized aggregate are reads of its exploded shell. -/
theorem readFieldSlot_init_downcast_field (locals : List LocalSlot) (var : Nat)
    (vals : List Value) (n : Option String) (v g : Nat) (t : Ty) (q : List ProjectionElem) :
    readFieldSlot locals (.init (.aggregate var vals)) (.downcast n v :: .field g t :: q) =
      shellFieldRead locals (explodeAggregate var vals) v g q := by
  simp only [readFieldSlot, evalValueProjRead_aggregate_downcast_field, shellFieldRead,
    explodeAggregate, shellVariant, List.getElem?_map]
  by_cases hv : var = v
  · simp only [hv, ↓reduceIte]
    cases vals[g]? <;> rfl
  · simp only [hv, ↓reduceIte]

/-- Field reads of a normalized, non-promoting shell are field reads of the shell (an empty
shell collapses to `.uninit`, whose reads fault like the all-uninitialized shell's). -/
theorem readFieldSlot_normalizeShell_field {locals : List LocalSlot} {sh : PartialAggregate}
    (hN : sh.tryIntoValue? = none) (g : Nat) (t : Ty) (q : List ProjectionElem) :
    readFieldSlot locals (normalizeShell sh) (.field g t :: q) = shellFieldRead locals sh 0 g q := by
  rcases normalizeShell_of_tryIntoValue?_none hN with ⟨h1, hE⟩ | h2
  · rw [h1, shellFieldRead_of_allFieldsUninit ((Bool.and_eq_true _ _).mp hE).2]
    rfl
  · rw [h2]
    exact readFieldSlot_nested_field locals sh.variantIdx sh.isAdt sh.discriminantSet sh.fields g t q

/-- `Downcast(v)` + `Field` reads of a normalized, non-promoting shell. -/
theorem readFieldSlot_normalizeShell_downcast_field {locals : List LocalSlot}
    {sh : PartialAggregate} (hN : sh.tryIntoValue? = none) (n : Option String) (v g : Nat)
    (t : Ty) (q : List ProjectionElem) :
    readFieldSlot locals (normalizeShell sh) (.downcast n v :: .field g t :: q) =
      shellFieldRead locals sh v g q := by
  rcases normalizeShell_of_tryIntoValue?_none hN with ⟨h1, hE⟩ | h2
  · rw [h1, shellFieldRead_of_allFieldsUninit ((Bool.and_eq_true _ _).mp hE).2]
    rfl
  · rw [h2]
    exact readFieldSlot_nested_downcast_field locals sh.variantIdx sh.isAdt sh.discriminantSet
      sh.fields n v g t q

/-- Sibling frame of one shell step: field `g ≠ f` reads are unchanged by updating field `f`. -/
theorem shellFieldRead_set_ne {locals : List LocalSlot} {sh : PartialAggregate} {disc' : Bool}
    {f g k : Nat} {c' : FieldSlot} {q : List ProjectionElem} (hNe : f ≠ g) :
    shellFieldRead locals { sh with discriminantSet := disc', fields := sh.fields.set f c' } k g q =
      shellFieldRead locals sh k g q := by
  unfold shellFieldRead
  dsimp only
  rw [List.getElem?_set_ne hNe]
  rfl

/-- Reading through the updated field `f` of one shell step reads the new child. -/
theorem shellFieldRead_set_self {locals : List LocalSlot} {sh : PartialAggregate} {disc' : Bool}
    {f k : Nat} {c c' : FieldSlot} {q : List ProjectionElem} (hc : sh.fields[f]? = some c) :
    shellFieldRead locals { sh with discriminantSet := disc', fields := sh.fields.set f c' } k f q =
      if shellVariant sh = k then readFieldSlot locals c' q else .ub := by
  have hLt := (List.getElem?_eq_some_iff.mp hc).1
  unfold shellFieldRead
  dsimp only
  rw [List.getElem?_set_self hLt]
  rfl

/-- Reading field `f` of a shell whose field `f` is `c`. -/
theorem shellFieldRead_of_getElem? {locals : List LocalSlot} {sh : PartialAggregate} {f k : Nat}
    {c : FieldSlot} {q : List ProjectionElem} (hc : sh.fields[f]? = some c) :
    shellFieldRead locals sh k f q = if shellVariant sh = k then readFieldSlot locals c q else .ub := by
  simp only [shellFieldRead, hc]

/-- A projection `q` diverging from the deinitialized path `p` at some field step: both paths
agree on a common prefix of `Field` / `Downcast(v)` + `Field` steps and then select distinct
fields `f ≠ g` of the same struct, tuple, or (active) enum variant. -/
inductive Diverges : List ProjectionElem → List ProjectionElem → Prop where
  | field {f g : Nat} {t t' : Ty} {p q : List ProjectionElem} (hNe : f ≠ g) :
      Diverges (.field f t :: p) (.field g t' :: q)
  | downcastField {n n' : Option String} {v f g : Nat} {t t' : Ty} {p q : List ProjectionElem}
      (hNe : f ≠ g) : Diverges (.downcast n v :: .field f t :: p) (.downcast n' v :: .field g t' :: q)
  | fieldCons {f : Nat} {t t' : Ty} {p q : List ProjectionElem} (h : Diverges p q) :
      Diverges (.field f t :: p) (.field f t' :: q)
  | downcastFieldCons {n n' : Option String} {v f : Nat} {t t' : Ty} {p q : List ProjectionElem}
      (h : Diverges p q) :
      Diverges (.downcast n v :: .field f t :: p) (.downcast n' v :: .field f t' :: q)

/-- A diverging path is non-empty. -/
theorem Diverges.cons_left {p q : List ProjectionElem} (h : Diverges p q) :
    ∃ a rest, p = a :: rest := by
  cases h <;> exact ⟨_, _, rfl⟩

/-- The stepped shell of a successful shell step whose child is uninitialized along `rest` does
not promote. -/
theorem stepped_tryIntoValue?_none {sh : PartialAggregate} {disc' : Bool} {f : Nat}
    {c c' : FieldSlot} {rest : List ProjectionElem} (hc : sh.fields[f]? = some c)
    (hU : UninitAt c' rest) :
    ({ sh with discriminantSet := disc', fields := sh.fields.set f c' } :
      PartialAggregate).tryIntoValue? = none := by
  have hLt := (List.getElem?_eq_some_iff.mp hc).1
  exact tryIntoValue?_eq_none_of_getElem? (idx := f) (c := c')
    (show (sh.fields.set f c')[f]? = some c' from List.getElem?_set_self hLt)
    (fun v hv => UninitAt.not_init (hv ▸ hU))

/-- **Disjoint-sibling frame of `deinitFieldSlot`**: deinitializing `p` does not change the
result of reading any projection `q` that diverges from `p` at a field step. -/
theorem deinitFieldSlot_read_diverges_eq (ts : Bool) (dlocals locals : List LocalSlot)
    {p q : List ProjectionElem} (hDiv : Diverges p q) :
    ∀ (slot slot' : FieldSlot), deinitFieldSlot ts dlocals slot p = some slot' →
      readFieldSlot locals slot' q = readFieldSlot locals slot q := by
  induction hDiv with
  | @field f g t t' rp rq hNe =>
    intro slot slot' h
    cases slot with
    | uninit =>
      simp only [deinitFieldSlot] at h
      split at h
      · cases h; rfl
      · nomatch h
    | init v =>
      cases v with
      | aggregate var vals =>
        simp only [deinitFieldSlot] at h
        obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
        have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
        rw [readFieldSlot_normalizeShell_field (stepped_tryIntoValue?_none hc hU),
          readFieldSlot_init_field locals vals (var := var) hV, shellFieldRead_set_ne hNe]
      | _ => nomatch h
    | nested var adt disc fs =>
      simp only [deinitFieldSlot] at h
      obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
      have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
      rw [readFieldSlot_normalizeShell_field (stepped_tryIntoValue?_none hc hU),
        readFieldSlot_nested_field, shellFieldRead_set_ne hNe]
  | @downcastField n n' v f g t t' rp rq hNe =>
    intro slot slot' h
    cases slot with
    | uninit =>
      simp only [deinitFieldSlot] at h
      split at h
      · cases h; rfl
      · nomatch h
    | init val =>
      cases val with
      | aggregate var vals =>
        simp only [deinitFieldSlot] at h
        obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
        have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
        rw [readFieldSlot_normalizeShell_downcast_field (stepped_tryIntoValue?_none hc hU),
          readFieldSlot_init_downcast_field, shellFieldRead_set_ne hNe]
      | _ => nomatch h
    | nested var adt disc fs =>
      simp only [deinitFieldSlot] at h
      obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
      have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
      rw [readFieldSlot_normalizeShell_downcast_field (stepped_tryIntoValue?_none hc hU),
        readFieldSlot_nested_downcast_field, shellFieldRead_set_ne hNe]
  | @fieldCons f t t' rp rq _ ih =>
    intro slot slot' h
    cases slot with
    | uninit =>
      simp only [deinitFieldSlot] at h
      split at h
      · cases h; rfl
      · nomatch h
    | init v =>
      cases v with
      | aggregate var vals =>
        simp only [deinitFieldSlot] at h
        obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
        have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
        rw [readFieldSlot_normalizeShell_field (stepped_tryIntoValue?_none hc hU),
          readFieldSlot_init_field locals vals (var := var) hV, shellFieldRead_set_self hc,
          shellFieldRead_of_getElem? hc, ih c c' hcc]
      | _ => nomatch h
    | nested var adt disc fs =>
      simp only [deinitFieldSlot] at h
      obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
      have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
      rw [readFieldSlot_normalizeShell_field (stepped_tryIntoValue?_none hc hU),
        readFieldSlot_nested_field, shellFieldRead_set_self hc, shellFieldRead_of_getElem? hc,
        ih c c' hcc]
  | @downcastFieldCons n n' v f t t' rp rq _ ih =>
    intro slot slot' h
    cases slot with
    | uninit =>
      simp only [deinitFieldSlot] at h
      split at h
      · cases h; rfl
      · nomatch h
    | init val =>
      cases val with
      | aggregate var vals =>
        simp only [deinitFieldSlot] at h
        obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
        have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
        rw [readFieldSlot_normalizeShell_downcast_field (stepped_tryIntoValue?_none hc hU),
          readFieldSlot_init_downcast_field, shellFieldRead_set_self hc,
          shellFieldRead_of_getElem? hc, ih c c' hcc]
      | _ => nomatch h
    | nested var adt disc fs =>
      simp only [deinitFieldSlot] at h
      obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
      have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
      rw [readFieldSlot_normalizeShell_downcast_field (stepped_tryIntoValue?_none hc hU),
        readFieldSlot_nested_downcast_field, shellFieldRead_set_self hc,
        shellFieldRead_of_getElem? hc, ih c c' hcc]

/-- `readFieldSlot` depends on the frame only through initialized scalar index locals. -/
theorem readFieldSlot_congr {locals₁ locals₂ : List LocalSlot}
    (hSame : SameScalarLocals locals₁ locals₂) (slot : FieldSlot) (q : List ProjectionElem) :
    readFieldSlot locals₁ slot q = readFieldSlot locals₂ slot q := by
  cases slot with
  | uninit => rfl
  | init v => exact evalValueProjRead_congr_scalar_locals hSame q v
  | nested var adt disc fs => exact readFromPartialShell_congr_scalar_locals hSame q _

/-- `SameScalarLocals` is symmetric. -/
theorem SameScalarLocals.symm {locals₁ locals₂ : List LocalSlot}
    (h : SameScalarLocals locals₁ locals₂) : SameScalarLocals locals₂ locals₁ :=
  fun i sc => (h i sc).symm

/-- `slotsToTrustedLocals` is a pointwise map. -/
theorem slotsToTrustedLocals_eq_map : ∀ (slots : List LocalSlotState),
    slotsToTrustedLocals slots = slots.map slotStateToTrustedLocal
  | [] => rfl
  | s :: rest => by
    simp only [slotsToTrustedLocals, List.map_cons, slotsToTrustedLocals_eq_map rest]

/-- Replacing a slot that is not an initialized scalar by another such slot preserves every
initialized scalar index local. -/
theorem sameScalarLocals_set {slots : List LocalSlotState} {i : Nat} {old new : LocalSlotState}
    (hOld : slots[i]? = some old)
    (hO : ∀ sc, slotStateToTrustedLocal old ≠ .init (.scalar sc))
    (hN : ∀ sc, slotStateToTrustedLocal new ≠ .init (.scalar sc)) :
    SameScalarLocals (slotsToTrustedLocals slots) (slotsToTrustedLocals (slots.set i new)) := by
  intro j sc
  simp only [slotsToTrustedLocals_eq_map, get?_eq_getElem?, List.getElem?_map]
  by_cases hij : i = j
  · subst hij
    have hLt := (List.getElem?_eq_some_iff.mp hOld).1
    rw [List.getElem?_set_self hLt, hOld]
    simp only [Option.map_some, Option.some.injEq]
    exact ⟨fun h => absurd h (hO sc), fun h => absurd h (hN sc)⟩
  · rw [List.getElem?_set_ne hij]

/-- A promoted shell is an aggregate. -/
theorem tryIntoValue?_aggregate {shell : PartialAggregate} {v : Value}
    (h : shell.tryIntoValue? = some v) : ∃ var vals, v = .aggregate var vals := by
  obtain ⟨_, vals, _, rfl⟩ := (tryIntoValue?_eq_some_iff shell v).mp h
  exact ⟨_, vals, rfl⟩

/-- The root of a successful projected `Deinit` is not an initialized scalar. -/
theorem deinit_root_not_scalar {ts : Bool} {locals : List LocalSlot} {st : LocalSlotState}
    {a : ProjectionElem} {rest : List ProjectionElem} {slot' : FieldSlot}
    (h : deinitFieldSlot ts locals (slotStateToFieldSlot st) (a :: rest) = some slot') :
    ∀ sc, slotStateToTrustedLocal st ≠ .init (.scalar sc) := by
  intro sc hEq
  cases st with
  | dead => simp [slotStateToTrustedLocal] at hEq
  | uninit => simp [slotStateToTrustedLocal] at hEq
  | init v =>
    simp only [slotStateToTrustedLocal, LocalSlot.init.injEq] at hEq
    subst hEq
    nomatch h
  | partialShell shell =>
    simp only [slotStateToTrustedLocal] at hEq
    split at hEq
    · rename_i v hv
      obtain ⟨_, _, rfl⟩ := tryIntoValue?_aggregate hv
      simp at hEq
    · simp at hEq

/-- The slot a `Deinit` leaves behind is not an initialized scalar. -/
theorem UninitAt.not_scalar {slot : FieldSlot} {p : List ProjectionElem} (h : UninitAt slot p) :
    ∀ sc, slotStateToTrustedLocal (fieldSlotToLocalSlotState slot) ≠ .init (.scalar sc) := by
  intro sc hEq
  cases slot with
  | uninit => simp [fieldSlotToLocalSlotState, slotStateToTrustedLocal] at hEq
  | init v => exact UninitAt.not_init h
  | nested var adt disc fs =>
    have hN := UninitAt.nested_tryIntoValue?_none h
    simp [fieldSlotToLocalSlotState, slotStateToTrustedLocal, hN] at hEq

/-- Reading a place of a local whose slot is unchanged, in frames agreeing on scalar index
locals, gives the same result. -/
theorem readPlaceState_congr_unchanged {slots slots' : List LocalSlotState} {loc : Local}
    (hGet : slots'[loc]? = slots[loc]?)
    (hSame : SameScalarLocals (slotsToTrustedLocals slots) (slotsToTrustedLocals slots'))
    (q : List ProjectionElem) :
    readPlaceState slots' ⟨loc, q⟩ = readPlaceState slots ⟨loc, q⟩ := by
  unfold readPlaceState
  cases projectionHasDeref q with
  | true => rfl
  | false =>
    simp only [get?_eq_getElem?, hGet]
    cases slots[loc]? with
    | none => rfl
    | some st =>
      cases st with
      | dead => rfl
      | uninit => rfl
      | init v => exact (evalValueProjRead_congr_scalar_locals hSame q v).symm
      | partialShell sh => exact (readFromPartialShell_congr_scalar_locals hSame q sh).symm

/-- Two places are disjoint for a `Deinit` frame: the same local with diverging projections,
or distinct locals (the deinitialized place being projected, so that no initialized scalar
index local changes). -/
def DeinitDisjoint (place place' : Place) : Prop :=
  (place'.local_ = place.local_ ∧ Diverges place.projection place'.projection) ∨
    (place'.local_ ≠ place.local_ ∧ place.projection ≠ [])

/-- **Disjoint-Sibling Frame (`evalDeinitPlace_read_disjoint_eq`)**: after a successful
`Deinit` of `place`, reading any disjoint place `place'` — a different field `g ≠ f` of the same
struct/tuple/active enum variant (below any common prefix), or a different local — yields
exactly the same result as before. -/
theorem evalDeinitPlace_read_disjoint_eq {ts : Bool} {slots slots' : List LocalSlotState}
    {place place' : Place} (h : evalDeinitPlace ts slots place = some slots')
    (hDisj : DeinitDisjoint place place') :
    readPlaceState slots' place' = readPlaceState slots place' := by
  obtain ⟨st, hSt, hLive, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hD
  have hProj : ∃ a rest, place.projection = a :: rest := by
    rcases hDisj with ⟨_, hDiv⟩ | ⟨_, hNe⟩
    · exact hDiv.cons_left
    · cases hp : place.projection with
      | nil => exact absurd hp hNe
      | cons a rest => exact ⟨a, rest, rfl⟩
  obtain ⟨a, rest, hP⟩ := hProj
  have hSame := sameScalarLocals_set hSt
    (deinit_root_not_scalar (show deinitFieldSlot ts _ _ (a :: rest) = some slot' by
      rw [← hP]; exact hD)) hU.not_scalar
  obtain ⟨loc', q⟩ := place'
  rcases hDisj with ⟨hLoc, hDiv⟩ | ⟨hNe, _⟩
  · simp only at hLoc hDiv
    subst hLoc
    obtain ⟨hRound, hNotDead⟩ := UninitAt.roundtrip hU
    have hLt : place.local_ < slots.length := (List.getElem?_eq_some_iff.mp hSt).1
    have hGet : (slots.set place.local_ (fieldSlotToLocalSlotState slot'))[place.local_]? =
        some (fieldSlotToLocalSlotState slot') := List.getElem?_set_self hLt
    cases hDeref : projectionHasDeref q with
    | true => simp only [readPlaceState, hDeref]
    | false =>
      rw [readPlaceState_eq_readFieldSlot hGet hNotDead q hDeref, hRound,
        readPlaceState_eq_readFieldSlot hSt hLive q hDeref, ← readFieldSlot_congr hSame]
      exact deinitFieldSlot_read_diverges_eq ts _ _ hDiv _ _ hD
  · exact readPlaceState_congr_unchanged (List.getElem?_set_ne (Ne.symm hNe)) hSame q

/-- Distinct-local frame of a bare-local `Deinit`: other locals read the same, provided the
deinitialized local did not hold an initialized scalar (which other places may use as an
`Index` operand). -/
theorem evalDeinitPlace_root_read_other_local_eq {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} (h : evalDeinitPlace ts slots place = some slots') {st : LocalSlotState}
    (hSt : slots[place.local_]? = some st)
    (hNotScalar : ∀ sc, slotStateToTrustedLocal st ≠ .init (.scalar sc))
    {loc' : Local} (hNe : loc' ≠ place.local_) (q : List ProjectionElem) :
    readPlaceState slots' ⟨loc', q⟩ = readPlaceState slots ⟨loc', q⟩ := by
  obtain ⟨st', hSt', _, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  rw [hSt] at hSt'
  cases hSt'
  have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hD
  exact readPlaceState_congr_unchanged (List.getElem?_set_ne (Ne.symm hNe))
    (sameScalarLocals_set hSt hNotScalar hU.not_scalar) q

/-! ### Section 2c: Put-after-`Deinit` re-promotion -/

/-- A path without `Downcast` steps (deinitializing along it never touches an enum tag). -/
def noDowncast : List ProjectionElem → Bool
  | [] => true
  | .downcast _ _ :: _ => false
  | _ :: rest => noDowncast rest

/-- A non-promoting enum/ADT shell whose tag is written normalizes to itself (it never
collapses). -/
theorem normalizeShell_eq_of_tagged {sh : PartialAggregate} (hN : sh.tryIntoValue? = none)
    (hAdt : sh.isAdt = true) (hDisc : sh.discriminantSet = true) :
    normalizeShell sh = sh.toFieldSlot := by
  unfold normalizeShell
  rw [hN]
  simp [hAdt, hDisc]

/-- A field of `vals.map .init` is an initialized field of `vals`. -/
theorem getElem?_map_init {vals : List Value} {idx : Nat} {c : FieldSlot}
    (h : (vals.map FieldSlot.init)[idx]? = some c) : ∃ cv, vals[idx]? = some cv ∧ c = .init cv := by
  rw [List.getElem?_map] at h
  cases hv : vals[idx]? with
  | none => rw [hv] at h; nomatch h
  | some cv =>
    rw [hv] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨cv, rfl, h.symm⟩

/-- Writing a field of an exploded aggregate after updating that field reassembles the
aggregate. -/
theorem map_init_set_set (vals : List Value) (idx : Nat) (c' : FieldSlot) (cv' : Value) :
    ((vals.map FieldSlot.init).set idx c').set idx (.init cv') =
      (vals.set idx cv').map FieldSlot.init := by
  rw [List.set_set, List.map_set]

/-- **Put-after-`Deinit` (`deinitFieldSlot_write_reinit`)**: deinitializing the part `p` of an
initialized value `v` and then writing `w` back to `p` restores an initialized slot, holding
exactly `v` updated at `p` with `w` (`evalValueProjWrite`), as long as the deinitialization did
not forget an enum tag (no `Downcast` on the path, or a tag stored apart from the fields). -/
theorem deinitFieldSlot_write_reinit (ts : Bool) (dlocals locals : List LocalSlot)
    (arityOf : Ty → VariantIdx → Bool → Option Nat) (w : Value) (slot : FieldSlot)
    (p : List ProjectionElem) (slot' : FieldSlot)
    (h : deinitFieldSlot ts dlocals slot p = some slot') :
    ∀ (v : Value), slot = .init v → (ts = true ∨ noDowncast p = true) → ∀ (ty : Ty),
      ∃ v', evalValueProjWrite locals v p w = .ok v' ∧
        writeToFieldSlot locals arityOf slot' ty p w = .ok (.init v') := by
  fun_induction deinitFieldSlot ts dlocals slot p generalizing slot' with
  | case1 slot =>
    intro v _ _ ty
    cases h
    exact ⟨w, by cases v <;> rfl, rfl⟩
  | case2 => intro v hv; cases hv
  | case3 => intro v hv; cases hv
  | case4 var vals idx fty rest ih =>
    intro v hv hTag ty
    cases hv
    obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    have hV' : var = 0 := hV
    subst hV'
    obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
    have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
    obtain ⟨cv', hW, hWS⟩ := ih (.init cv) c' hcc cv rfl hTag fty
    have hLt : idx < vals.length := (List.getElem?_eq_some_iff.mp hcv).1
    have hN := stepped_tryIntoValue?_none (sh := explodeAggregate 0 vals)
      (disc' := (explodeAggregate 0 vals).discriminantSet && ((none : Option Nat).isNone || ts))
      hc hU
    rw [normalizeShell_eq_of_tagged hN rfl (by simp [explodeAggregate])]
    refine ⟨.aggregate 0 (vals.set idx cv'), ?_, ?_⟩
    · simp only [evalValueProjWrite, get?_eq_getElem?, hcv, hW,
        set?_eq_some_iff.mpr ⟨hLt, rfl⟩]
    · have hLt' : idx < ((vals.map FieldSlot.init).set idx c').length := by simp [hLt]
      simp only [PartialAggregate.toFieldSlot, explodeAggregate, writeToFieldSlot,
        get?_eq_getElem?,
        List.getElem?_set_self (l := vals.map FieldSlot.init) (a := c') (by simpa using hLt),
        Nat.beq_refl, hWS,
        set?_eq_some_iff.mpr ⟨hLt', rfl⟩, map_init_set_set, promoteShellToFieldSlot]
      rw [tryIntoValue?_of_all_init _ (vals.set idx cv') rfl (Or.inr rfl)]
  | case5 var vals n v idx fty rest ih =>
    intro val hv hTag ty
    cases hv
    have hTs : ts = true := by
      rcases hTag with hT | hT
      · exact hT
      · simp [noDowncast] at hT
    obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    have hV' : var = v := hV
    subst hV'
    obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
    have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
    obtain ⟨cv', hW, hWS⟩ := ih (.init cv) c' hcc cv rfl (Or.inl hTs) fty
    have hLt : idx < vals.length := (List.getElem?_eq_some_iff.mp hcv).1
    have hN := stepped_tryIntoValue?_none (sh := explodeAggregate var vals)
      (disc' := (explodeAggregate var vals).discriminantSet && ((some var).isNone || ts))
      hc hU
    rw [normalizeShell_eq_of_tagged hN rfl (by simp [explodeAggregate, hTs])]
    refine ⟨.aggregate var (vals.set idx cv'), ?_, ?_⟩
    · simp only [evalValueProjWrite, isFieldHead, Nat.beq_refl, Bool.and_self, get?_eq_getElem?,
        hcv, hW, set?_eq_some_iff.mpr ⟨hLt, rfl⟩]
    · have hLt' : idx < ((vals.map FieldSlot.init).set idx c').length := by simp [hLt]
      simp only [PartialAggregate.toFieldSlot, explodeAggregate, writeToFieldSlot,
        get?_eq_getElem?,
        List.getElem?_set_self (l := vals.map FieldSlot.init) (a := c') (by simpa using hLt),
        Nat.beq_refl, hWS,
        set?_eq_some_iff.mpr ⟨hLt', rfl⟩, map_init_set_set, promoteShellToFieldSlot, hTs,
        Bool.and_true, Bool.or_true]
      rw [tryIntoValue?_of_all_init _ (vals.set idx cv') rfl (Or.inr rfl)]
  | case6 => intro v hv; cases hv
  | case7 => intro v hv; cases hv
  | case8 => nomatch h

/-- `deinitTailOk` paths contain no `Deref`. -/
theorem deinitTailOk_noDeref (locals : List LocalSlot) (p : List ProjectionElem)
    (h : deinitTailOk locals p = true) : projectionHasDeref p = false := by
  fun_induction deinitTailOk locals p <;> simp_all [projectionHasDeref]

/-- Out-of-bounds `ConstantIndex` in a projection tail under `.uninit` fails closed (`none`), as in
`validate_projection_tail` (with `min_length` standing for the array length, see
`deinitTailOk`). -/
theorem evalDeinitPlace_uninit_constantIndex_oob_none (ts : Bool) (slots : List LocalSlotState)
    (loc : Local) (offset minLen : Nat) (fromEnd : Bool) (rest : List ProjectionElem)
    (hRoot : slots[loc]? = some .uninit)
    (hOob : (if fromEnd then decide (1 ≤ offset ∧ offset ≤ minLen) else decide (offset < minLen)) =
      false) :
    evalDeinitPlace ts slots ⟨loc, .constantIndex offset minLen fromEnd :: rest⟩ = none := by
  simp only [evalDeinitPlace, hRoot, slotStateToFieldSlot, deinitFieldSlot, deinitTailOk, hOob,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Out-of-bounds non-`fromEnd` `Subslice` (`from_ > to_`) in a projection tail under `.uninit`
fails closed (`none`), matching `validate_projection_tail` in `rvalue.rs`. -/
theorem evalDeinitPlace_uninit_subslice_oob_none (ts : Bool) (slots : List LocalSlotState)
    (loc : Local) (from_ to_ : Nat) (rest : List ProjectionElem)
    (hRoot : slots[loc]? = some .uninit) (hOob : to_ < from_) :
    evalDeinitPlace ts slots ⟨loc, .subslice from_ to_ false :: rest⟩ = none := by
  have hFalse : decide (from_ ≤ to_) = false := decide_eq_false (by omega)
  simp only [evalDeinitPlace, hRoot, slotStateToFieldSlot, deinitFieldSlot, deinitTailOk, hFalse,
    Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- A successfully deinitialized place has no `Deref`. -/
theorem deinitFieldSlot_noDeref {ts : Bool} {locals : List LocalSlot} {slot : FieldSlot}
    {p : List ProjectionElem} {slot' : FieldSlot}
    (h : deinitFieldSlot ts locals slot p = some slot') : projectionHasDeref p = false := by
  fun_induction deinitFieldSlot ts locals slot p generalizing slot' with
  | case1 => rfl
  | case2 p rest hT => exact deinitTailOk_noDeref _ _ hT
  | case3 => nomatch h
  | case4 var vals idx ty rest ih =>
    obtain ⟨_, c, c', _, hcc, _⟩ := deinitShellStep_eq_some h
    simpa [projectionHasDeref] using ih c hcc
  | case5 var vals n v idx ty rest ih =>
    obtain ⟨_, c, c', _, hcc, _⟩ := deinitShellStep_eq_some h
    simpa [projectionHasDeref] using ih c hcc
  | case6 var adt disc fs idx ty rest ih =>
    obtain ⟨_, c, c', _, hcc, _⟩ := deinitShellStep_eq_some h
    simpa [projectionHasDeref] using ih c hcc
  | case7 var adt disc fs n v idx ty rest ih =>
    obtain ⟨_, c, c', _, hcc, _⟩ := deinitShellStep_eq_some h
    simpa [projectionHasDeref] using ih c hcc
  | case8 => nomatch h

/-- `writePlaceState` on a live local writes through its root slot with `writeToFieldSlot`. -/
theorem writePlaceState_eq {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {slots : List LocalSlotState} {place : Place} {rootTy : Ty} {w : Value} {st : LocalSlotState}
    (hSt : slots[place.local_]? = some st) (hLive : st ≠ .dead)
    (hNoDeref : projectionHasDeref place.projection = false) :
    writePlaceState arityOf slots place rootTy w =
      match writeToFieldSlot (slotsToTrustedLocals slots) arityOf (slotStateToFieldSlot st) rootTy
          place.projection w with
      | .ok next => .ok (slots.set place.local_ (fieldSlotToLocalSlotState next))
      | .ub => .ub
      | .unsupported => .unsupported := by
  unfold writePlaceState
  simp only [hNoDeref, get?_eq_getElem?, hSt]
  cases st with
  | dead => exact absurd rfl hLive
  | uninit => rfl
  | init v => rfl
  | partialShell sh => rfl

/-- **Put-After-Deinit Re-promotion (`evalDeinitPlace_write_reinit`)**: deinitializing a part
`place` of an initialized local and then writing `w` back to `place` (`writePlaceState`)
restores `.init` with the original root value updated at `place` — unless an enum tag was
forgotten on the way (see `deinitFieldSlot_niche_write_needs_setDiscriminant`). -/
theorem evalDeinitPlace_write_reinit {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} {rootVal : Value} (hRoot : slots[place.local_]? = some (.init rootVal))
    (h : evalDeinitPlace ts slots place = some slots')
    (hTag : ts = true ∨ noDowncast place.projection = true)
    (arityOf : Ty → VariantIdx → Bool → Option Nat) (rootTy : Ty) (w : Value) :
    ∃ rootVal', evalValueProjWrite (slotsToTrustedLocals slots') rootVal place.projection w =
        .ok rootVal' ∧
      writePlaceState arityOf slots' place rootTy w = .ok (slots.set place.local_ (.init rootVal')) := by
  obtain ⟨st, hSt, _, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  rw [hRoot] at hSt
  cases hSt
  have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hD
  obtain ⟨hRound, hNotDead⟩ := UninitAt.roundtrip hU
  have hLt := (List.getElem?_eq_some_iff.mp hRoot).1
  have hGet : (slots.set place.local_ (fieldSlotToLocalSlotState slot'))[place.local_]? =
      some (fieldSlotToLocalSlotState slot') := List.getElem?_set_self hLt
  obtain ⟨v', hW, hWS⟩ := deinitFieldSlot_write_reinit ts _
    (slotsToTrustedLocals (slots.set place.local_ (fieldSlotToLocalSlotState slot'))) arityOf w
    _ _ _ hD rootVal rfl hTag rootTy
  refine ⟨v', hW, ?_⟩
  rw [writePlaceState_eq hGet hNotDead (deinitFieldSlot_noDeref hD), hRound, hWS]
  simp only [fieldSlotToLocalSlotState, List.set_set]

/-- **A niche-encoded tag is lost (`A3`)**: for an enum whose tag may live in a field's niche
(`tag_survives_field_deinit = false`), deinitializing a variant field and writing it back does
not restore an initialized value: the result is a shell of that variant with an unwritten tag
(the value needs `SetDiscriminant` again), and the whole value stays unreadable. -/
theorem deinitFieldSlot_niche_write_needs_setDiscriminant (dlocals locals : List LocalSlot)
    (arityOf : Ty → VariantIdx → Bool → Option Nat) (v f : Nat) (vals : List Value)
    (n : Option String) (t ty : Ty) (w : Value) (slot' : FieldSlot)
    (h : deinitFieldSlot false dlocals (.init (.aggregate v vals)) [.downcast n v, .field f t] =
      some slot')
    (r : FieldSlot)
    (hW : writeToFieldSlot locals arityOf slot' ty [.downcast n v, .field f t] w = .ok r) :
    ∃ fs, r = .nested v true false fs ∧ readFieldSlot locals r [] = .ub := by
  simp only [deinitFieldSlot] at h
  obtain ⟨_, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
  cases hcc
  have hLt : f < vals.length := by
    have := (List.getElem?_eq_some_iff.mp hc).1
    simpa [explodeAggregate] using this
  have hN := stepped_tryIntoValue?_none (sh := explodeAggregate v vals)
    (disc' := (explodeAggregate v vals).discriminantSet && ((some v).isNone || false))
    (c' := FieldSlot.uninit) (rest := []) hc trivial
  have hRead : ∀ fs, readFieldSlot locals (.nested v true false fs) [] = .ub := by
    intro fs
    simp [readFieldSlot, readFromPartialShell, PartialAggregate.tryIntoValue?]
  rcases normalizeShell_of_tryIntoValue?_none hN with ⟨h1, _⟩ | h2
  · rw [h1] at hW
    simp only [writeToFieldSlot] at hW
    split at hW
    · rename_i cnt _
      split at hW
      · split at hW
        · rename_i fs' _
          cases hW
          refine ⟨fs', ?_, hRead fs'⟩
          simp [promoteShellToFieldSlot, PartialAggregate.tryIntoValue?, PartialAggregate.newUninit]
        · nomatch hW
      · nomatch hW
    · nomatch hW
  · rw [h2] at hW
    simp only [explodeAggregate, writeToFieldSlot, get?_eq_getElem?,
      List.getElem?_set_self (l := vals.map FieldSlot.init) (a := FieldSlot.uninit)
        (by simpa using hLt), Nat.beq_refl] at hW
    split at hW
    · rename_i fs' _
      cases hW
      refine ⟨fs', ?_, hRead fs'⟩
      simp [promoteShellToFieldSlot, PartialAggregate.tryIntoValue?]
    · nomatch hW

/-! ### Section 2d: `Deinit` refines Trusted's `evalStmt` -/

mutual
  /-- Anneal's view `slot` of a part is *below* Trusted's value `t`: Anneal knows less (an
  uninitialized part may correspond to any Trusted value), and everything Anneal knows agrees
  with Trusted (initialized parts are equal, shells have Trusted's variant and arity). -/
  def FieldSlotBelow : FieldSlot → Value → Prop
    | .uninit, _ => True
    | .init v, t => v = t
    | .nested var adt disc fs, .aggregate tv tfs =>
      shellVariant ⟨var, adt, disc, fs⟩ = tv ∧ FieldListBelow fs tfs
    | .nested _ _ _ _, _ => False

  /-- Pointwise `FieldSlotBelow` of equally long field lists. -/
  def FieldListBelow : List FieldSlot → List Value → Prop
    | [], [] => True
    | f :: fs, t :: ts => FieldSlotBelow f t ∧ FieldListBelow fs ts
    | _, _ => False
end

/-- Anneal's local state is below Trusted's local slot: dead locals agree, an uninitialized
Anneal local is uninitialized in Trusted or an aggregate there (e.g. after a projected `Deinit`
of all its fields, which Trusted does not track), and initialized/partial locals are below
Trusted's value. -/
def SlotBelow : LocalSlotState → LocalSlot → Prop
  | .dead, .dead => True
  | .uninit, .uninit => True
  | .uninit, .init (.aggregate _ _) => True
  | .init v, .init w => v = w
  | .partialShell shell, .init t => FieldSlotBelow shell.toFieldSlot t
  | _, _ => False

/-- Pointwise lookup in `FieldListBelow`. -/
theorem FieldListBelow.getElem? : ∀ {fs : List FieldSlot} {tfs : List Value} {g : Nat}
    {c : FieldSlot}, FieldListBelow fs tfs → fs[g]? = some c →
      ∃ tc, tfs[g]? = some tc ∧ FieldSlotBelow c tc
  | [], [], _, _, _, h => by simp at h
  | f :: fs, t :: ts, 0, c, hB, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨t, rfl, hB.1⟩
  | f :: fs, t :: ts, g + 1, c, hB, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact FieldListBelow.getElem? hB.2 h
  | [], _ :: _, _, _, hB, _ => by simp [FieldListBelow] at hB
  | _ :: _, [], _, _, hB, _ => by simp [FieldListBelow] at hB

/-- Updating position `g` of below-related lists with below-related elements. -/
theorem FieldListBelow.set : ∀ {fs : List FieldSlot} {tfs : List Value} (g : Nat)
    {c : FieldSlot} {tc : Value}, FieldListBelow fs tfs → tfs[g]? = some tc →
      FieldSlotBelow c tc → FieldListBelow (fs.set g c) tfs
  | [], [], _, _, _, _, h, _ => by simp at h
  | f :: fs, t :: ts, 0, c, tc, hB, h, hC => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨hC, hB.2⟩
  | f :: fs, t :: ts, g + 1, c, tc, hB, h, hC => by
    simp only [List.getElem?_cons_succ] at h
    exact ⟨hB.1, FieldListBelow.set g hB.2 h hC⟩
  | [], _ :: _, _, _, _, hB, _, _ => by simp [FieldListBelow] at hB
  | _ :: _, [], _, _, _, hB, _, _ => by simp [FieldListBelow] at hB

/-- `vals.map .init` is below `vals`. -/
theorem fieldListBelow_map_init : ∀ (vals : List Value), FieldListBelow (vals.map .init) vals
  | [] => trivial
  | _ :: vs => ⟨rfl, fieldListBelow_map_init vs⟩

/-- An all-initialized field list below `tfs` is `tfs`. -/
theorem FieldListBelow.eq_of_map_init : ∀ {vals tfs : List Value},
    FieldListBelow (vals.map .init) tfs → vals = tfs
  | [], [], _ => rfl
  | v :: vs, t :: ts, h => by
    have h1 : v = t := h.1
    rw [h1, FieldListBelow.eq_of_map_init h.2]
  | [], _ :: _, h => by simp [FieldListBelow] at h
  | _ :: _, [], h => by simp [FieldListBelow] at h

/-- A normalized shell below `t` stays below `t` (a promoted shell is exactly `t`). -/
theorem normalizeShell_below {sh : PartialAggregate} {tv : Nat} {tfs : List Value}
    (hV : shellVariant sh = tv) (hB : FieldListBelow sh.fields tfs) :
    FieldSlotBelow (normalizeShell sh) (.aggregate tv tfs) := by
  unfold normalizeShell
  cases hT : sh.tryIntoValue? with
  | some v =>
    obtain ⟨_, vals, hF, rfl⟩ := (tryIntoValue?_eq_some_iff sh v).mp hT
    rw [hF] at hB
    have := FieldListBelow.eq_of_map_init hB
    subst this
    show Value.aggregate _ vals = .aggregate tv vals
    rw [← hV]
    rfl
  | none =>
    cases (!sh.isAdt || !sh.discriminantSet) && allFieldsUninit sh.fields with
    | true => trivial
    | false => exact ⟨hV, hB⟩

/-- **`Deinit` stays below Trusted**: deinitializing a part of a slot that is below `t` yields a
slot that is still below `t` (Trusted's value is unchanged by a projected `Deinit`). -/
theorem deinitFieldSlot_below (ts : Bool) (locals : List LocalSlot) (slot : FieldSlot)
    (p : List ProjectionElem) (slot' : FieldSlot)
    (h : deinitFieldSlot ts locals slot p = some slot') :
    ∀ (t : Value), FieldSlotBelow slot t → FieldSlotBelow slot' t := by
  fun_induction deinitFieldSlot ts locals slot p generalizing slot' with
  | case1 => intro t _; cases h; trivial
  | case2 => intro t _; cases h; trivial
  | case3 => nomatch h
  | case4 var vals idx ty rest ih =>
    intro t hB
    have ht : t = .aggregate var vals := hB.symm
    subst ht
    obtain ⟨_, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
    exact normalizeShell_below rfl
      (FieldListBelow.set idx (fieldListBelow_map_init vals) hcv (ih (.init cv) c' hcc cv rfl))
  | case5 var vals n v idx ty rest ih =>
    intro t hB
    have ht : t = .aggregate var vals := hB.symm
    subst ht
    obtain ⟨_, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
    exact normalizeShell_below rfl
      (FieldListBelow.set idx (fieldListBelow_map_init vals) hcv (ih (.init cv) c' hcc cv rfl))
  | case6 var adt disc fs idx ty rest ih =>
    intro t hB
    cases t with
    | aggregate tv tfs =>
      obtain ⟨hV, hBs⟩ := hB
      obtain ⟨_, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
      obtain ⟨tc, htc, hCB⟩ := FieldListBelow.getElem? hBs hc
      exact normalizeShell_below hV (FieldListBelow.set idx hBs htc (ih c c' hcc tc hCB))
    | _ => exact absurd hB id
  | case7 var adt disc fs n v idx ty rest ih =>
    intro t hB
    cases t with
    | aggregate tv tfs =>
      obtain ⟨hV, hBs⟩ := hB
      obtain ⟨_, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
      obtain ⟨tc, htc, hCB⟩ := FieldListBelow.getElem? hBs hc
      exact normalizeShell_below hV (FieldListBelow.set idx hBs htc (ih c c' hcc tc hCB))
    | _ => exact absurd hB id
  | case8 => nomatch h

/-- Reading the whole of a slot below `t` returns exactly `t`. -/
theorem readFieldSlot_below_nil {locals : List LocalSlot} {slot : FieldSlot} {t r : Value}
    (hB : FieldSlotBelow slot t) (hR : readFieldSlot locals slot [] = .ok r) : r = t := by
  cases slot with
  | uninit => nomatch hR
  | init v =>
    have hv : v = t := hB
    simp only [readFieldSlot, evalValueProjRead] at hR
    cases hR
    exact hv
  | nested var adt disc fs =>
    cases t with
    | aggregate tv tfs =>
      obtain ⟨hV, hBs⟩ := hB
      simp only [readFieldSlot, readFromPartialShell] at hR
      split at hR
      · rename_i v hT
        cases hR
        obtain ⟨_, vals, hF, rfl⟩ := (tryIntoValue?_eq_some_iff _ _).mp hT
        simp only at hF
        subst hF
        have := FieldListBelow.eq_of_map_init hBs
        subst this
        rw [← hV]
        rfl
      · nomatch hR
    | _ => exact absurd hB id

/-- Fuel form of `readFieldSlot_below_refines`. -/
theorem readFieldSlot_below_refines_aux (locals : List LocalSlot) :
    ∀ (n : Nat) (q : List ProjectionElem), q.length ≤ n → ∀ (slot : FieldSlot) (t r : Value),
      FieldSlotBelow slot t → readFieldSlot locals slot q = .ok r →
      evalValueProjRead locals t q = .ok r := by
  intro n
  induction n with
  | zero =>
    intro q hLen slot t r hB hR
    have hq : q = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hLen)
    subst hq
    rw [readFieldSlot_below_nil hB hR]
    rfl
  | succ n ih =>
    intro q hLen slot t r hB hR
    rcases q with _ | ⟨a, q'⟩
    · rw [readFieldSlot_below_nil hB hR]
      rfl
    · simp only [List.length_cons] at hLen
      cases slot with
      | uninit => nomatch hR
      | init v =>
        have hv : v = t := hB
        subst hv
        exact hR
      | nested var adt disc fs =>
        cases t with
        | aggregate tv tfs =>
          obtain ⟨hV, hBs⟩ := hB
          cases a
          case field g ty =>
            rw [readFieldSlot_nested_field] at hR
            simp only [shellFieldRead] at hR
            split at hR
            · rename_i hV0
              cases hc : fs[g]? with
              | none => rw [hc] at hR; nomatch hR
              | some c =>
                rw [hc] at hR
                obtain ⟨tc, htc, hCB⟩ := FieldListBelow.getElem? hBs hc
                rw [evalValueProjRead_aggregate_field, htc]
                exact ih q' (by omega) c tc r hCB hR
            · nomatch hR
          case downcast nm v =>
            rcases q' with _ | ⟨b, q''⟩
            · simp [readFieldSlot, readFromPartialShell] at hR
            · cases b
              case field g ty =>
                simp only [List.length_cons] at hLen
                rw [readFieldSlot_nested_downcast_field] at hR
                simp only [shellFieldRead] at hR
                split at hR
                · rename_i hVv
                  cases hc : fs[g]? with
                  | none => rw [hc] at hR; nomatch hR
                  | some c =>
                    rw [hc] at hR
                    obtain ⟨tc, htc, hCB⟩ := FieldListBelow.getElem? hBs hc
                    rw [evalValueProjRead_aggregate_downcast_field, ← hV, hVv]
                    simp only [↓reduceIte, htc]
                    exact ih q'' (by omega) c tc r hCB hR
                · nomatch hR
              all_goals simp [readFieldSlot, readFromPartialShell, isFieldHead] at hR
          all_goals simp [readFieldSlot, readFromPartialShell] at hR
        | _ => exact absurd hB id

/-- **Reads below Trusted are Trusted reads**: every successful read of a slot below `t`
returns what Trusted's value-tree read of `t` returns. -/
theorem readFieldSlot_below_refines {locals : List LocalSlot} {slot : FieldSlot} {t r : Value}
    {q : List ProjectionElem} (hB : FieldSlotBelow slot t)
    (hR : readFieldSlot locals slot q = .ok r) : evalValueProjRead locals t q = .ok r :=
  readFieldSlot_below_refines_aux locals q.length q (Nat.le_refl _) slot t r hB hR

/-- Below-related frames agree on initialized scalar index locals. -/
theorem sameScalarLocals_of_slotBelow {slots : List LocalSlotState} {locals : List LocalSlot}
    (hRel : SlotsRefine SlotBelow slots locals) :
    SameScalarLocals (slotsToTrustedLocals slots) locals := by
  intro i sc
  rw [slotsToTrustedLocals_eq_map, get?_eq_getElem?, get?_eq_getElem?, List.getElem?_map]
  rcases SlotsRefine.get?_rel i hRel with ⟨hA, hT⟩ | ⟨a, t, hA, hT, hAT⟩
  · simp only [get?_eq_getElem?] at hA hT
    simp [hA, hT]
  · simp only [get?_eq_getElem?] at hA hT
    rw [hA, hT]
    simp only [Option.map_some, Option.some.injEq]
    cases a with
    | dead => cases t <;> simp_all [SlotBelow, slotStateToTrustedLocal]
    | uninit =>
      cases t with
      | dead => simp_all [SlotBelow]
      | uninit => simp [slotStateToTrustedLocal]
      | init w => cases w <;> simp_all [SlotBelow, slotStateToTrustedLocal]
    | init v =>
      cases t with
      | init w =>
        have hvw : v = w := hAT
        subst hvw
        simp [slotStateToTrustedLocal]
      | _ => simp_all [SlotBelow]
    | partialShell sh =>
      cases t with
      | init w =>
        have hw : ∃ tv tfs, w = .aggregate tv tfs := by
          cases w with
          | aggregate tv tfs => exact ⟨tv, tfs, rfl⟩
          | _ => exact absurd hAT id
        obtain ⟨tv, tfs, rfl⟩ := hw
        simp only [slotStateToTrustedLocal]
        split
        · rename_i v hv
          obtain ⟨_, _, rfl⟩ := tryIntoValue?_aggregate hv
          simp
        · simp
      | _ => simp_all [SlotBelow]

/-- **`readPlaceState` refines Trusted's `readProjectedValue` on below-related frames**: every
successful Anneal read (in particular every read after a projected `Deinit`) is defined in
Trusted with the same value. -/
theorem readPlaceState_below_refines {slots : List LocalSlotState} {locals : List LocalSlot}
    {place : Place} {val : Value} (hRel : SlotsRefine SlotBelow slots locals)
    (hRead : readPlaceState slots place = .ok val) :
    ∃ rootVal, get? locals place.local_ = some (.init rootVal) ∧
      readProjectedValue locals rootVal place.projection = .ok val := by
  have hSame := sameScalarLocals_of_slotBelow hRel
  cases hDeref : projectionHasDeref place.projection with
  | true => simp only [readPlaceState, hDeref] at hRead; nomatch hRead
  | false =>
    rcases SlotsRefine.get?_rel place.local_ hRel with ⟨hNoneS, _⟩ | ⟨a, t, hGetS, hGetT, hAT⟩
    · simp only [readPlaceState, hDeref, hNoneS] at hRead; nomatch hRead
    · have hLive : a ≠ .dead := by
        intro hD
        subst hD
        simp only [readPlaceState, hDeref, hGetS] at hRead
        nomatch hRead
      simp only [get?_eq_getElem?] at hGetS
      rw [readPlaceState_eq_readFieldSlot hGetS hLive _ hDeref, readFieldSlot_congr hSame] at hRead
      have hBelow : ∃ rootVal, t = .init rootVal ∧ FieldSlotBelow (slotStateToFieldSlot a) rootVal := by
        cases a with
        | dead => exact absurd rfl hLive
        | uninit =>
          cases t with
          | init w => exact ⟨w, rfl, trivial⟩
          | _ => simp [readFieldSlot, slotStateToFieldSlot] at hRead
        | init v =>
          cases t with
          | init w => exact ⟨w, rfl, hAT⟩
          | _ => exact absurd hAT id
        | partialShell sh =>
          cases t with
          | init w => exact ⟨w, rfl, hAT⟩
          | _ => exact absurd hAT id
      obtain ⟨rootVal, rfl, hB⟩ := hBelow
      exact ⟨rootVal, hGetT, evalValueProjRead_refines_readProjectedValue _ _ _ _
        (readFieldSlot_below_refines hB hRead)⟩

/-- A projected `Deinit` of an initialized value succeeds only on an aggregate. -/
theorem deinitFieldSlot_init_aggregate {ts : Bool} {locals : List LocalSlot} {v : Value}
    {a : ProjectionElem} {rest : List ProjectionElem} {slot' : FieldSlot}
    (h : deinitFieldSlot ts locals (.init v) (a :: rest) = some slot') :
    ∃ var vals, v = .aggregate var vals := by
  cases v with
  | aggregate var vals => exact ⟨var, vals, rfl⟩
  | _ => nomatch h

/-- The path of a successful `Deinit` of an initialized value is readable in that value (in any
frame: such a path has no `Index` step). -/
theorem deinitFieldSlot_init_read_ok (ts : Bool) (dlocals : List LocalSlot) (slot : FieldSlot)
    (p : List ProjectionElem) (slot' : FieldSlot)
    (h : deinitFieldSlot ts dlocals slot p = some slot') :
    ∀ (v : Value), slot = .init v → ∀ (locals : List LocalSlot),
      ∃ r, evalValueProjRead locals v p = .ok r := by
  fun_induction deinitFieldSlot ts dlocals slot p generalizing slot' with
  | case1 => intro v _ locals; exact ⟨v, by cases v <;> rfl⟩
  | case2 => intro v hv; cases hv
  | case3 => intro v hv; cases hv
  | case4 var vals idx ty rest ih =>
    intro v hv locals
    cases hv
    obtain ⟨hV, c, c', hc, hcc, _⟩ := deinitShellStep_eq_some h
    obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
    obtain ⟨r, hr⟩ := ih (.init cv) c' hcc cv rfl locals
    exact ⟨r, by rw [evalValueProjRead_aggregate_field, hcv]; exact hr⟩
  | case5 var vals n v idx ty rest ih =>
    intro val hv locals
    cases hv
    obtain ⟨hV, c, c', hc, hcc, _⟩ := deinitShellStep_eq_some h
    have hV' : var = v := hV
    obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
    obtain ⟨r, hr⟩ := ih (.init cv) c' hcc cv rfl locals
    exact ⟨r, by rw [evalValueProjRead_aggregate_downcast_field]; simp only [hV', ↓reduceIte, hcv]; exact hr⟩
  | case6 => intro v hv; cases hv
  | case7 => intro v hv; cases hv
  | case8 => nomatch h

/-- **Bare-local `Deinit` step refinement**: on below-related frames, Anneal's `Deinit` of a bare
local agrees with Trusted's `evalStmt`, which steps (never faults) to the frame with the local
uninitialized, and the frames stay related. -/
theorem evalStmt_deinit_root_refines {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} {s : MachineState} {span : String} {localDecls : List LocalDecl}
    {layouts : LayoutTable} (hRel : SlotsRefine SlotBelow slots s.frame.locals)
    (hRoot : place.projection = []) (h : evalDeinitPlace ts slots place = some slots') :
    evalStmt s ⟨.deinit place, span⟩ localDecls layouts =
        .step (advanceStmt s (s.frame.locals.set place.local_ .uninit)) ∧
      SlotsRefine SlotBelow slots' (s.frame.locals.set place.local_ .uninit) := by
  obtain ⟨st, hSt, hLive, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  rw [hRoot, deinitFieldSlot_nil] at hD
  cases hD
  rcases SlotsRefine.get?_rel place.local_ hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, hAT⟩
  · simp only [get?_eq_getElem?] at hA
    rw [hA] at hSt
    nomatch hSt
  · simp only [get?_eq_getElem?] at hA hT
    rw [hA] at hSt
    cases hSt
    have hLtT : place.local_ < s.frame.locals.length := (List.getElem?_eq_some_iff.mp hT).1
    have hTnd : t ≠ .dead := by
      intro hTd
      subst hTd
      cases st <;> simp_all [SlotBelow]
    refine ⟨?_, SlotsRefine.set (show SlotBelow .uninit .uninit from trivial) _ hRel⟩
    simp only [evalStmt, hRoot, get?_eq_getElem?, hT]
    cases t with
    | dead => exact absurd rfl hTnd
    | uninit => simp only [set?_eq_some_iff.mpr ⟨hLtT, rfl⟩]
    | init w => simp only [set?_eq_some_iff.mpr ⟨hLtT, rfl⟩]

/-- **Projected `Deinit` step refinement**: on below-related frames, whenever Anneal's projected
`Deinit` succeeds and Trusted's root holds a value in which the place is readable, Trusted's
`evalStmt` steps (never faults) with its frame unchanged, and Anneal's frame — now with the place
uninitialized — is still below it (so every later Anneal read is a Trusted read, by
`readPlaceState_below_refines`). -/
theorem evalStmt_deinit_projected_refines {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} {s : MachineState} {span : String} {localDecls : List LocalDecl}
    {layouts : LayoutTable} (hRel : SlotsRefine SlotBelow slots s.frame.locals)
    (hProj : place.projection ≠ []) (h : evalDeinitPlace ts slots place = some slots')
    {rootVal : Value} (hTRoot : s.frame.locals[place.local_]? = some (.init rootVal))
    {tv : Value} (hTRead : readProjectedValue s.frame.locals rootVal place.projection = .ok tv) :
    evalStmt s ⟨.deinit place, span⟩ localDecls layouts = .step (advanceStmt s s.frame.locals) ∧
      SlotsRefine SlotBelow slots' s.frame.locals := by
  obtain ⟨a, rest, hP⟩ : ∃ a rest, place.projection = a :: rest := by
    cases hp : place.projection with
    | nil => exact absurd hp hProj
    | cons a rest => exact ⟨a, rest, rfl⟩
  obtain ⟨st, hSt, hLive, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hD
  refine ⟨?_, ?_⟩
  · rw [hP] at hTRead
    simp only [evalStmt, hP, get?_eq_getElem?, hTRoot, hTRead]
  · rcases SlotsRefine.get?_rel place.local_ hRel with ⟨hA, _⟩ | ⟨a', t, hA, hT, hAT⟩
    · simp only [get?_eq_getElem?] at hA
      rw [hA] at hSt
      nomatch hSt
    · simp only [get?_eq_getElem?] at hA hT
      rw [hA] at hSt
      cases hSt
      rw [hTRoot] at hT
      cases hT
      have hAgg : ∃ var vals, rootVal = .aggregate var vals := by
        cases st with
        | dead => exact absurd rfl hLive
        | uninit =>
          cases rootVal with
          | aggregate var vals => exact ⟨var, vals, rfl⟩
          | _ => exact absurd hAT id
        | init v =>
          have hv : v = rootVal := hAT
          subst hv
          exact deinitFieldSlot_init_aggregate (show deinitFieldSlot ts _ (.init v) (a :: rest) =
            some slot' by rw [← hP]; exact hD)
        | partialShell sh =>
          cases rootVal with
          | aggregate var vals => exact ⟨var, vals, rfl⟩
          | _ => exact absurd hAT id
      have hB0 : FieldSlotBelow (slotStateToFieldSlot st) rootVal := by
        cases st with
        | dead => exact absurd rfl hLive
        | uninit => trivial
        | init v => exact hAT
        | partialShell sh => exact hAT
      have hB := deinitFieldSlot_below _ _ _ _ _ hD rootVal hB0
      have hSB : SlotBelow (fieldSlotToLocalSlotState slot') (.init rootVal) := by
        cases slot' with
        | uninit =>
          obtain ⟨var, vals, rfl⟩ := hAgg
          trivial
        | init v => exact absurd hU UninitAt.not_init
        | nested var adt disc fs =>
          have hN := UninitAt.nested_tryIntoValue?_none hU
          simp only [fieldSlotToLocalSlotState, hN]
          exact hB
      have hLtT : place.local_ < s.frame.locals.length := (List.getElem?_eq_some_iff.mp hTRoot).1
      have hSelf : s.frame.locals.set place.local_ (.init rootVal) = s.frame.locals := by
        have hEq : s.frame.locals[place.local_] = .init rootVal :=
          (List.getElem?_eq_some_iff.mp hTRoot).2
        rw [← hEq]
        exact List.set_getElem_self hLtT
      have := SlotsRefine.set hSB place.local_ hRel
      rwa [hSelf] at this

/-- **Projected `Deinit` of an initialized local refines Trusted unconditionally**: when the
Anneal root is initialized, Anneal's success alone implies Trusted's `evalStmt` steps with its
frame unchanged, and the frames stay related. -/
theorem evalStmt_deinit_projected_init_refines {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} {s : MachineState} {span : String} {localDecls : List LocalDecl}
    {layouts : LayoutTable} (hRel : SlotsRefine SlotBelow slots s.frame.locals)
    (hProj : place.projection ≠ []) {rootVal : Value}
    (hRoot : slots[place.local_]? = some (.init rootVal))
    (h : evalDeinitPlace ts slots place = some slots') :
    evalStmt s ⟨.deinit place, span⟩ localDecls layouts = .step (advanceStmt s s.frame.locals) ∧
      SlotsRefine SlotBelow slots' s.frame.locals := by
  obtain ⟨st, hSt, _, slot', hD, _⟩ := evalDeinitPlace_eq_some h
  rw [hRoot] at hSt
  cases hSt
  rcases SlotsRefine.get?_rel place.local_ hRel with ⟨hA, _⟩ | ⟨a', t, hA, hT, hAT⟩
  · simp only [get?_eq_getElem?] at hA
    rw [hA] at hRoot
    nomatch hRoot
  · simp only [get?_eq_getElem?] at hA hT
    rw [hA] at hRoot
    cases hRoot
    cases t with
    | init w =>
      have hw : rootVal = w := hAT
      subst hw
      obtain ⟨r, hr⟩ := deinitFieldSlot_init_read_ok _ _ _ _ _ hD rootVal rfl s.frame.locals
      exact evalStmt_deinit_projected_refines hRel hProj h hT
        (evalValueProjRead_refines_readProjectedValue _ _ _ _ hr)
    | _ => exact absurd hAT id

/-- **Documented divergence**: Trusted's projected `Deinit` requires an initialized root and
faults on an uninitialized one, whereas Anneal (like MiniRust, which writes `Uninit` bytes over
already uninitialized bytes) treats a well-formed `Deinit` below an uninitialized local as a
no-op. Anneal is therefore more permissive than Trusted here; every other `Deinit` refines
Trusted (`evalStmt_deinit_root_refines`, `evalStmt_deinit_projected_refines`). -/
theorem evalStmt_deinit_projected_uninit_root_divergence {ts : Bool}
    {slots : List LocalSlotState} {place : Place} {s : MachineState} {span : String}
    {localDecls : List LocalDecl} {layouts : LayoutTable} (hProj : place.projection ≠ [])
    (hA : slots[place.local_]? = some .uninit)
    (hTail : deinitTailOk (slotsToTrustedLocals slots) place.projection = true)
    (hT : s.frame.locals[place.local_]? = some .uninit) :
    evalDeinitPlace ts slots place = some slots ∧
      evalStmt s ⟨.deinit place, span⟩ localDecls layouts = .fail .ub := by
  obtain ⟨a, rest, hP⟩ : ∃ a rest, place.projection = a :: rest := by
    cases hp : place.projection with
    | nil => exact absurd hp hProj
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hLt : place.local_ < slots.length := (List.getElem?_eq_some_iff.mp hA).1
  refine ⟨?_, ?_⟩
  · rw [hP] at hTail
    simp only [evalDeinitPlace, hA, hP, slotStateToFieldSlot, deinitFieldSlot, hTail, ↓reduceIte,
      fieldSlotToLocalSlotState]
    have hEq : slots[place.local_] = .uninit := (List.getElem?_eq_some_iff.mp hA).2
    rw [← hEq, List.set_getElem_self hLt]
  · simp only [evalStmt, hP, get?_eq_getElem?, hT]

/-! ### Section 2e: Byte-level `Uninit` refinement (closing `Translate.lean:3742`) -/

/-- A reference byte image of a local in MiniRust's memory model: `none` is an `Uninit` byte. -/
abbrev ByteImage : Type := List (Option UInt8)

/-- MiniRust's `Deinit` of a place at byte offset `off` of size `len`: writes `Uninit` to
`[off, off + len)` and leaves every other byte unchanged. -/
def deinitBytes (img : ByteImage) (off len : Nat) : ByteImage :=
  img.mapIdx fun i b => if off ≤ i ∧ i < off + len then none else b

/-- `deinitBytes` preserves the image size. -/
theorem length_deinitBytes (img : ByteImage) (off len : Nat) :
    (deinitBytes img off len).length = img.length := by
  simp [deinitBytes]

/-- Bytes inside the deinitialized range become `Uninit`. -/
theorem deinitBytes_getElem?_inside {img : ByteImage} {off len i : Nat}
    (hIn : off ≤ i ∧ i < off + len) (hLt : i < img.length) :
    (deinitBytes img off len)[i]? = some none := by
  simp [deinitBytes, List.getElem?_mapIdx, hIn, List.getElem?_eq_getElem hLt]

/-- Bytes outside the deinitialized range are unchanged. -/
theorem deinitBytes_getElem?_outside {img : ByteImage} {off len i : Nat}
    (hOut : ¬ (off ≤ i ∧ i < off + len)) : (deinitBytes img off len)[i]? = img[i]? := by
  simp only [deinitBytes, List.getElem?_mapIdx]
  cases img[i]? with
  | none => rfl
  | some b => simp only [Option.map_some, hOut, ↓reduceIte]

/-- The bytes `[off, off + size)` of `img` represent a field slot: an uninitialized field is all
`Uninit` bytes, an initialized field is its encoding (`enc`, MiniRust's `encode`), and a nested
partially initialized shell constrains nothing at this level. -/
def FieldBytes (enc : Value → List UInt8) (img : ByteImage) (off size : Nat) : FieldSlot → Prop
  | .uninit => ∀ k, k < size → img[off + k]? = some none
  | .init v => (enc v).length = size ∧ ∀ k, k < size → img[off + k]? = ((enc v)[k]?).map some
  | .nested _ _ _ _ => True

/-- Every field of `fields`, laid out by `lay` (`offset, size`), lies inside `img` and is
represented by its bytes. -/
def StructBytes (enc : Value → List UInt8) (lay : Nat → Option (Nat × Nat)) (img : ByteImage)
    (fields : List FieldSlot) : Prop :=
  ∀ i c off size, fields[i]? = some c → lay i = some (off, size) →
    off + size ≤ img.length ∧ FieldBytes enc img off size c

/-- A field layout whose fields occupy pairwise disjoint byte ranges (structs; not unions). -/
def LayoutDisjoint (lay : Nat → Option (Nat × Nat)) : Prop :=
  ∀ i j oi si oj sj, i ≠ j → lay i = some (oi, si) → lay j = some (oj, sj) →
    oi + si ≤ oj ∨ oj + sj ≤ oi

/-- A field's byte representation only depends on its own bytes. -/
theorem fieldBytes_frame {enc : Value → List UInt8} {img img' : ByteImage} {off size : Nat}
    {c : FieldSlot} (hFrame : ∀ k, k < size → img'[off + k]? = img[off + k]?) :
    FieldBytes enc img off size c → FieldBytes enc img' off size c := by
  cases c with
  | uninit => intro h k hk; rw [hFrame k hk]; exact h k hk
  | init v =>
    intro h
    exact ⟨h.1, fun k hk => by rw [hFrame k hk]; exact h.2 k hk⟩
  | nested => intro _; trivial

/-- **Byte-level simulation of a field `Deinit`**: on a layout with pairwise disjoint fields,
uninitializing field `f` in the field-slot model corresponds exactly to MiniRust writing
`Uninit` over the field's byte range: the new image represents the updated fields. -/
theorem structBytes_deinit {enc : Value → List UInt8} {lay : Nat → Option (Nat × Nat)}
    {img : ByteImage} {fields : List FieldSlot} {f : Nat} {c : FieldSlot} {off size : Nat}
    (hS : StructBytes enc lay img fields) (hD : LayoutDisjoint lay)
    (hc : fields[f]? = some c) (hf : lay f = some (off, size)) :
    StructBytes enc lay (deinitBytes img off size) (fields.set f .uninit) := by
  intro j cj oj sj hcj hj
  have hLtF := (hS f c off size hc hf).1
  by_cases hjf : j = f
  · subst hjf
    rw [hf] at hj
    cases hj
    have hLtf : j < fields.length := (List.getElem?_eq_some_iff.mp hc).1
    rw [List.getElem?_set_self hLtf] at hcj
    cases hcj
    refine ⟨by rw [length_deinitBytes]; exact hLtF, ?_⟩
    intro k hk
    exact deinitBytes_getElem?_inside ⟨by omega, by omega⟩ (by omega)
  · rw [List.getElem?_set_ne (Ne.symm hjf)] at hcj
    obtain ⟨hLtJ, hFB⟩ := hS j cj oj sj hcj hj
    refine ⟨by rw [length_deinitBytes]; exact hLtJ, fieldBytes_frame (fun k hk => ?_) hFB⟩
    apply deinitBytes_getElem?_outside
    rcases hD j f oj sj off size hjf hj hf with h1 | h1 <;> omega

/-- A non-promoting shell converts to a partial-shell local. -/
theorem fieldSlotToLocalSlotState_toFieldSlot {sh : PartialAggregate}
    (h : sh.tryIntoValue? = none) : fieldSlotToLocalSlotState sh.toFieldSlot = .partialShell sh := by
  obtain ⟨a, b, c, d⟩ := sh
  simp only [fieldSlotToLocalSlotState, h]

/-- `Deinit` of field `f` of an initialized struct/tuple local leaves the exploded shell with
exactly field `f` uninitialized (the tag-carrying shell never collapses). -/
theorem evalDeinitPlace_field_shell {ts : Bool} {slots slots' : List LocalSlotState} {loc : Local}
    {vals : List Value} {f : Nat} {ty : Ty}
    (hRoot : slots[loc]? = some (.init (.aggregate 0 vals)))
    (h : evalDeinitPlace ts slots ⟨loc, [.field f ty]⟩ = some slots') :
    f < vals.length ∧
      slots' = slots.set loc (.partialShell ⟨0, true, true, (vals.map .init).set f .uninit⟩) := by
  obtain ⟨st, hSt, _, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  simp only at hSt hD
  rw [hRoot] at hSt
  cases hSt
  simp only [slotStateToFieldSlot, deinitFieldSlot] at hD
  obtain ⟨_, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some hD
  cases hcc
  have hLt : f < vals.length := by
    have := (List.getElem?_eq_some_iff.mp hc).1
    simpa [explodeAggregate] using this
  have hN := stepped_tryIntoValue?_none (sh := explodeAggregate 0 vals)
    (disc' := (explodeAggregate 0 vals).discriminantSet && ((none : Option Nat).isNone || ts))
    (c' := FieldSlot.uninit) (rest := []) hc trivial
  refine ⟨hLt, ?_⟩
  rw [normalizeShell_eq_of_tagged hN rfl (by simp [explodeAggregate]),
    fieldSlotToLocalSlotState_toFieldSlot hN]
  rfl

/-- **`Deinit` of a struct field is MiniRust's byte-range `Uninit` write**: if the bytes of an
initialized struct local represent its fields under a layout `lay` with disjoint fields, then
after Anneal's `Deinit` of field `f` the new shell is represented by the image in which exactly
`f`'s bytes `[off, off + size)` are `Uninit` (and every other byte is unchanged). -/
theorem evalDeinitPlace_bytes_simulation {ts : Bool} {slots slots' : List LocalSlotState}
    {loc : Local} {vals : List Value} {f : Nat} {ty : Ty} (enc : Value → List UInt8)
    (lay : Nat → Option (Nat × Nat)) (img : ByteImage)
    (hRoot : slots[loc]? = some (.init (.aggregate 0 vals)))
    (h : evalDeinitPlace ts slots ⟨loc, [.field f ty]⟩ = some slots')
    (hD : LayoutDisjoint lay) (hS : StructBytes enc lay img (vals.map .init))
    {off size : Nat} (hf : lay f = some (off, size)) :
    ∃ shell, slots'[loc]? = some (.partialShell shell) ∧
      StructBytes enc lay (deinitBytes img off size) shell.fields ∧
      ∀ i, ¬ (off ≤ i ∧ i < off + size) → (deinitBytes img off size)[i]? = img[i]? := by
  obtain ⟨hLt, rfl⟩ := evalDeinitPlace_field_shell hRoot h
  have hLoc : loc < slots.length := (List.getElem?_eq_some_iff.mp hRoot).1
  have hc : (vals.map FieldSlot.init)[f]? = some (.init vals[f]) := by
    simp [List.getElem?_map, List.getElem?_eq_getElem hLt]
  exact ⟨_, List.getElem?_set_self hLoc, structBytes_deinit hS hD hc hf,
    fun i hi => deinitBytes_getElem?_outside hi⟩

/-- The field layout `(offset, size)` an `AdtLayoutSpec` assigns to the fields `fs` of variant
`0` (`resolveAdtOffsetOf`). -/
def specFieldLayout (spec : AdtLayoutSpec) (fs : List FieldLayout) : Nat → Option (Nat × Nat) :=
  fun i =>
    match resolveAdtOffsetOf spec 0 i, fs[i]? with
    | some o, some fl => some (o, fl.size)
    | _, _ => none

/-- Inversion of `specFieldLayout`. -/
theorem specFieldLayout_eq_some {spec : AdtLayoutSpec} {fs : List FieldLayout} {i o s : Nat}
    (h : specFieldLayout spec fs i = some (o, s)) :
    resolveAdtOffsetOf spec 0 i = some o ∧ ∃ fl, fs[i]? = some fl ∧ fl.size = s := by
  unfold specFieldLayout at h
  split at h
  · rename_i o' fl hO hF
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hO, fl, hF, rfl⟩
  · nomatch h

/-- `#[repr(C)]` struct fields occupy pairwise disjoint byte ranges. -/
theorem reprC_layoutDisjoint {spec : AdtLayoutSpec} {fs : List FieldLayout}
    (hShape : spec.shape = .struct fs) (hRepr : spec.repr = .c) :
    LayoutDisjoint (specFieldLayout spec fs) := by
  intro i j oi si oj sj hNe hi hj
  obtain ⟨hoi, fli, hfli, rfl⟩ := specFieldLayout_eq_some hi
  obtain ⟨hoj, flj, hflj, rfl⟩ := specFieldLayout_eq_some hj
  rcases Nat.lt_or_gt_of_ne hNe with hlt | hgt
  · obtain ⟨fi, hfi, hle⟩ := resolveAdtOffsetOf_reprC_monotone hShape hRepr hlt hoi hoj
    rw [hfli] at hfi
    cases hfi
    exact Or.inl hle
  · obtain ⟨fj, hfj, hle⟩ := resolveAdtOffsetOf_reprC_monotone hShape hRepr hgt hoj hoi
    rw [hflj] at hfj
    cases hfj
    exact Or.inr hle

/-- **`#[repr(C)]` instance of the byte simulation** (the projected-`Deinit` bridge to
MiniRust): for a `#[repr(C)]` struct, Anneal's `Deinit` of field `f` is MiniRust's `Uninit`
write over `[resolveAdtOffsetOf f, resolveAdtOffsetOf f + size f)`, which lies inside the
struct and is aligned for the field (`resolveAdtOffsetOf_bounds_and_align`). -/
theorem evalDeinitPlace_reprC_bytes_simulation {ts : Bool} {slots slots' : List LocalSlotState}
    {loc : Local} {vals : List Value} {f : Nat} {ty : Ty} (enc : Value → List UInt8)
    (img : ByteImage) {spec : AdtLayoutSpec} {fs : List FieldLayout}
    (hShape : spec.shape = .struct fs) (hRepr : spec.repr = .c) (hWF : spec.WF)
    (hRoot : slots[loc]? = some (.init (.aggregate 0 vals)))
    (h : evalDeinitPlace ts slots ⟨loc, [.field f ty]⟩ = some slots')
    (hS : StructBytes enc (specFieldLayout spec fs) img (vals.map .init))
    {off : Nat} (hOff : resolveAdtOffsetOf spec 0 f = some off) {fl : FieldLayout}
    (hfl : fs[f]? = some fl) :
    (∃ size align, adtLayout? spec = some (size, align) ∧ off + fl.size ≤ size ∧ fl.align ∣ off) ∧
    ∃ shell, slots'[loc]? = some (.partialShell shell) ∧
      StructBytes enc (specFieldLayout spec fs) (deinitBytes img off fl.size) shell.fields ∧
      ∀ i, ¬ (off ≤ i ∧ i < off + fl.size) → (deinitBytes img off fl.size)[i]? = img[i]? := by
  have hLay : specFieldLayout spec fs f = some (off, fl.size) := by
    simp [specFieldLayout, hOff, hfl]
  refine ⟨?_, evalDeinitPlace_bytes_simulation enc _ img hRoot h
    (reprC_layoutDisjoint hShape hRepr) hS hLay⟩
  obtain ⟨fs', fl', size, align, hVF, hFl', hL, hBound, hAlign⟩ :=
    resolveAdtOffsetOf_bounds_and_align spec hWF hOff
  have hVF' : variantFields spec 0 = some fs := by simp [variantFields, hShape]
  rw [hVF'] at hVF
  cases hVF
  rw [hfl] at hFl'
  cases hFl'
  exact ⟨size, align, hL, hBound, hAlign⟩

/-! #### Nested byte layouts: arbitrary-depth field `Deinit` -/

/-- A byte layout tree: a leaf of `size` bytes, or a struct/tuple of `size` bytes whose field `i`
lies at byte offset `offsets[i]` with layout `fields[i]` (e.g. built from `resolveAdtOffsetOf`). -/
inductive ByteLayout : Type where
  | leaf (size : Nat) : ByteLayout
  | struct (size : Nat) (offsets : List Nat) (fields : List ByteLayout) : ByteLayout

/-- The byte size of a layout. -/
def ByteLayout.size : ByteLayout → Nat
  | .leaf n => n
  | .struct n _ _ => n

/-- A well-formed byte layout: every field lies inside its struct, the fields of a struct occupy
pairwise disjoint byte ranges, and every field layout is well formed. -/
inductive ByteLayout.WF : ByteLayout → Prop where
  | leaf (n : Nat) : ByteLayout.WF (.leaf n)
  | struct (n : Nat) (offs : List Nat) (ls : List ByteLayout)
      (hLen : offs.length = ls.length)
      (hFit : ∀ (i o : Nat) (l : ByteLayout), offs[i]? = some o → ls[i]? = some l →
        o + l.size ≤ n)
      (hDisj : ∀ (i j oi oj : Nat) (li lj : ByteLayout), i ≠ j → offs[i]? = some oi →
        offs[j]? = some oj → ls[i]? = some li → ls[j]? = some lj →
        oi + li.size ≤ oj ∨ oj + lj.size ≤ oi)
      (hChildren : ∀ (i : Nat) (l : ByteLayout), ls[i]? = some l → ByteLayout.WF l) :
      ByteLayout.WF (.struct n offs ls)

mutual
  /-- The bytes `[base, base + lay.size)` of `img` represent a field slot of layout `lay`: an
  uninitialized part is all `Uninit` bytes, an initialized leaf is its encoding (`enc`), and an
  initialized aggregate or a shell is represented field by field (padding is unconstrained). -/
  def SlotBytes (enc : Value → List UInt8) (img : ByteImage) :
      ByteLayout → Nat → FieldSlot → Prop
    | lay, base, .uninit => ∀ k, k < lay.size → img[base + k]? = some none
    | .leaf n, base, .init v =>
      (enc v).length = n ∧ ∀ k, k < n → img[base + k]? = ((enc v)[k]?).map some
    | .struct _ offs ls, base, .init (.aggregate _ vals) => ValuesBytes enc img offs ls base vals
    | .struct _ _ _, _, .init _ => False
    | .struct _ offs ls, base, .nested _ _ _ fs => SlotsBytes enc img offs ls base fs
    | .leaf _, _, .nested _ _ _ _ => False

  /-- Field-wise `SlotBytes` of a shell's field slots. -/
  def SlotsBytes (enc : Value → List UInt8) (img : ByteImage) :
      List Nat → List ByteLayout → Nat → List FieldSlot → Prop
    | o :: os, l :: ls, base, c :: cs =>
      SlotBytes enc img l (base + o) c ∧ SlotsBytes enc img os ls base cs
    | [], [], _, [] => True
    | _, _, _, _ => False

  /-- Field-wise `SlotBytes` of an initialized aggregate's fields. -/
  def ValuesBytes (enc : Value → List UInt8) (img : ByteImage) :
      List Nat → List ByteLayout → Nat → List Value → Prop
    | o :: os, l :: ls, base, v :: vs =>
      SlotBytes enc img l (base + o) (.init v) ∧ ValuesBytes enc img os ls base vs
    | [], [], _, [] => True
    | _, _, _, _ => False
end

/-- Pointwise characterization of `SlotsBytes`. -/
theorem slotsBytes_iff (enc : Value → List UInt8) (img : ByteImage) :
    ∀ (fs : List FieldSlot) (offs : List Nat) (ls : List ByteLayout) (base : Nat),
      SlotsBytes enc img offs ls base fs ↔
        offs.length = fs.length ∧ ls.length = fs.length ∧
        ∀ (i : Nat) (c : FieldSlot), fs[i]? = some c →
          ∃ (o : Nat) (l : ByteLayout), offs[i]? = some o ∧ ls[i]? = some l ∧
            SlotBytes enc img l (base + o) c
  | [], offs, ls, base => by
    cases offs <;> cases ls <;> simp [SlotsBytes]
  | c :: cs, offs, ls, base => by
    cases offs with
    | nil => cases ls <;> simp [SlotsBytes]
    | cons o os =>
      cases ls with
      | nil => simp [SlotsBytes]
      | cons l ls =>
        have ih := slotsBytes_iff enc img cs os ls base
        simp only [SlotsBytes, ih, List.length_cons, Nat.add_right_cancel_iff]
        constructor
        · rintro ⟨hc, hLen1, hLen2, hAll⟩
          refine ⟨hLen1, hLen2, fun i c' hi => ?_⟩
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
            subst hi
            exact ⟨o, l, rfl, rfl, hc⟩
          | succ i =>
            simp only [List.getElem?_cons_succ] at hi ⊢
            exact hAll i c' hi
        · rintro ⟨hLen1, hLen2, hAll⟩
          obtain ⟨o', l', ho, hl, hc⟩ := hAll 0 c rfl
          simp only [List.getElem?_cons_zero, Option.some.injEq] at ho hl
          subst ho hl
          refine ⟨hc, hLen1, hLen2, fun i c' hi => ?_⟩
          have := hAll (i + 1) c' (by simpa using hi)
          simpa using this

/-- Pointwise characterization of `ValuesBytes`. -/
theorem valuesBytes_iff (enc : Value → List UInt8) (img : ByteImage) :
    ∀ (vals : List Value) (offs : List Nat) (ls : List ByteLayout) (base : Nat),
      ValuesBytes enc img offs ls base vals ↔
        offs.length = vals.length ∧ ls.length = vals.length ∧
        ∀ (i : Nat) (w : Value), vals[i]? = some w →
          ∃ (o : Nat) (l : ByteLayout), offs[i]? = some o ∧ ls[i]? = some l ∧
            SlotBytes enc img l (base + o) (.init w)
  | [], offs, ls, base => by
    cases offs <;> cases ls <;> simp [ValuesBytes]
  | w :: ws, offs, ls, base => by
    cases offs with
    | nil => cases ls <;> simp [ValuesBytes]
    | cons o os =>
      cases ls with
      | nil => simp [ValuesBytes]
      | cons l ls =>
        have ih := valuesBytes_iff enc img ws os ls base
        simp only [ValuesBytes, ih, List.length_cons, Nat.add_right_cancel_iff]
        constructor
        · rintro ⟨hw, hLen1, hLen2, hAll⟩
          refine ⟨hLen1, hLen2, fun i w' hi => ?_⟩
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
            subst hi
            exact ⟨o, l, rfl, rfl, hw⟩
          | succ i =>
            simp only [List.getElem?_cons_succ] at hi ⊢
            exact hAll i w' hi
        · rintro ⟨hLen1, hLen2, hAll⟩
          obtain ⟨o', l', ho, hl, hw⟩ := hAll 0 w rfl
          simp only [List.getElem?_cons_zero, Option.some.injEq] at ho hl
          subst ho hl
          refine ⟨hw, hLen1, hLen2, fun i w' hi => ?_⟩
          have := hAll (i + 1) w' (by simpa using hi)
          simpa using this

/-- **Byte frame**: a slot's byte representation only depends on the bytes of its layout's range. -/
theorem slotBytes_frame {enc : Value → List UInt8} {img img' : ByteImage} :
    ∀ {lay : ByteLayout}, lay.WF → ∀ (base : Nat) (c : FieldSlot),
      (∀ k, k < lay.size → img'[base + k]? = img[base + k]?) →
      SlotBytes enc img lay base c → SlotBytes enc img' lay base c := by
  intro lay hWF
  induction hWF with
  | leaf n =>
    intro base c hFrame h
    cases c with
    | uninit =>
      intro k hk
      rw [hFrame k hk]
      exact h k hk
    | init v =>
      exact ⟨h.1, fun k hk => by rw [hFrame k hk]; exact h.2 k hk⟩
    | nested _ _ _ _ => exact h.elim
  | struct n offs ls hLen hFit hDisj hChildren ih =>
    intro base c hFrame h
    cases c with
    | uninit =>
      intro k hk
      rw [hFrame k hk]
      exact h k hk
    | init v =>
      cases v with
      | aggregate var vals =>
        simp only [SlotBytes] at h ⊢
        obtain ⟨hL1, hL2, hAll⟩ := (valuesBytes_iff enc img vals offs ls base).mp h
        refine (valuesBytes_iff enc img' vals offs ls base).mpr ⟨hL1, hL2, fun i w hi => ?_⟩
        obtain ⟨o, l, ho, hl, hb⟩ := hAll i w hi
        refine ⟨o, l, ho, hl, ih i l hl (base + o) (.init w) (fun k hk => ?_) hb⟩
        have := hFit i o l ho hl
        rw [Nat.add_assoc, hFrame (o + k) (by simp only [ByteLayout.size]; omega)]
      | _ => exact h.elim
    | nested var adt disc fs =>
      simp only [SlotBytes] at h ⊢
      obtain ⟨hL1, hL2, hAll⟩ := (slotsBytes_iff enc img fs offs ls base).mp h
      refine (slotsBytes_iff enc img' fs offs ls base).mpr ⟨hL1, hL2, fun i c hi => ?_⟩
      obtain ⟨o, l, ho, hl, hb⟩ := hAll i c hi
      refine ⟨o, l, ho, hl, ih i l hl (base + o) c (fun k hk => ?_) hb⟩
      have := hFit i o l ho hl
      rw [Nat.add_assoc, hFrame (o + k) (by simp only [ByteLayout.size]; omega)]

/-- The byte range `(offset, size)` of the part of a layout reached by a path of `Field` or
`Downcast(v)` + `Field` steps (`none` for any other step). -/
def pathRange : ByteLayout → Nat → List ProjectionElem → Option (Nat × Nat)
  | lay, base, [] => some (base, lay.size)
  | .struct _ offs ls, base, .field f _ :: rest =>
    match offs[f]?, ls[f]? with
    | some o, some l => pathRange l (base + o) rest
    | _, _ => none
  | .struct _ offs ls, base, .downcast _ _ :: .field f _ :: rest =>
    match offs[f]?, ls[f]? with
    | some o, some l => pathRange l (base + o) rest
    | _, _ => none
  | _, _, _ :: _ => none

/-- The byte range of a path lies inside the layout's range. -/
theorem pathRange_sub : ∀ (p : List ProjectionElem) {lay : ByteLayout} {base off len : Nat},
    lay.WF → pathRange lay base p = some (off, len) → base ≤ off ∧ off + len ≤ base + lay.size
  | [], lay, base, off, len, _, h => by
    simp only [pathRange, Option.some.injEq, Prod.mk.injEq] at h
    omega
  | a :: rest, lay, base, off, len, hWF, h => by
    cases lay with
    | leaf n =>
      cases a with
      | downcast _ _ => cases rest with | nil => simp [pathRange] at h | cons b _ => cases b <;> simp [pathRange] at h
      | _ => simp [pathRange] at h
    | struct n offs ls =>
      cases a with
      | field f ty =>
        simp only [pathRange] at h
        split at h
        · rename_i o l ho hl
          cases hWF with
          | struct _ _ _ hLen hFit hDisj hChildren =>
            have := pathRange_sub rest (hChildren f l hl) h
            have := hFit f o l ho hl
            simp only [ByteLayout.size]
            omega
        · nomatch h
      | downcast nm v =>
        rcases rest with _ | ⟨b, rest'⟩
        · simp [pathRange] at h
        · cases b with
          | field f ty =>
            simp only [pathRange] at h
            split at h
            · rename_i o l ho hl
              cases hWF with
              | struct _ _ _ hLen hFit hDisj hChildren =>
                have := pathRange_sub rest' (hChildren f l hl) h
                have := hFit f o l ho hl
                simp only [ByteLayout.size]
                omega
            · nomatch h
          | _ => simp [pathRange] at h
      | _ => simp [pathRange] at h

/-- `ValuesBytes` of an aggregate's fields is `SlotsBytes` of its exploded shell. -/
theorem valuesBytes_iff_slotsBytes_map_init (enc : Value → List UInt8) (img : ByteImage) :
    ∀ (vals : List Value) (offs : List Nat) (ls : List ByteLayout) (base : Nat),
      ValuesBytes enc img offs ls base vals ↔ SlotsBytes enc img offs ls base (vals.map .init)
  | [], offs, ls, base => by cases offs <;> cases ls <;> simp [ValuesBytes, SlotsBytes]
  | w :: ws, offs, ls, base => by
    cases offs with
    | nil => cases ls <;> simp [ValuesBytes, SlotsBytes]
    | cons o os =>
      cases ls with
      | nil => simp [ValuesBytes, SlotsBytes]
      | cons l ls =>
        simp only [ValuesBytes, SlotsBytes, List.map_cons,
          valuesBytes_iff_slotsBytes_map_init enc img ws os ls base]

/-- **Arbitrary-depth byte simulation of `Deinit`**: deinitializing the part of an initialized
value reached by a path of `Field` and (when `ts = true`) `Downcast(v)` + `Field` steps corresponds
exactly to MiniRust writing `Uninit` over that part's byte range (`pathRange`) in a well-formed
nested layout: the new slot is represented by the new image. -/
theorem deinitFieldSlot_bytes_sim (ts : Bool) (L : List LocalSlot) (enc : Value → List UInt8)
    (img : ByteImage) :
    ∀ (p : List ProjectionElem) (v : Value) (lay : ByteLayout) (base : Nat) (slot' : FieldSlot)
      (off len : Nat),
      deinitFieldSlot ts L (.init v) p = some slot' → (ts = true ∨ noDowncast p = true) →
      lay.WF → base + lay.size ≤ img.length →
      SlotBytes enc img lay base (.init v) → pathRange lay base p = some (off, len) →
      SlotBytes enc (deinitBytes img off len) lay base slot'
  | [], v, lay, base, slot', off, len, h, _, _, hFits, _, hRange => by
    rw [deinitFieldSlot_nil] at h
    cases h
    simp only [pathRange, Option.some.injEq, Prod.mk.injEq] at hRange
    obtain ⟨rfl, rfl⟩ := hRange
    simp only [SlotBytes]
    intro k hk
    exact deinitBytes_getElem?_inside ⟨by omega, by omega⟩ (by omega)
  | a :: rest, v, lay, base, slot', off, len, h, hTag, hWF, hFits, hS, hRange => by
    cases lay with
    | leaf n =>
      cases a with
      | downcast _ _ => cases rest with | nil => simp [pathRange] at hRange | cons b _ => cases b <;> simp [pathRange] at hRange
      | _ => simp [pathRange] at hRange
    | struct n offs ls =>
      cases a with
      | field f ty =>
        have hTagRest : ts = true ∨ noDowncast rest = true := by
          rcases hTag with hT | hND
          · exact Or.inl hT
          · exact Or.inr (by simpa [noDowncast] using hND)
        simp only [pathRange] at hRange
        split at hRange
        · rename_i o l ho hl
          cases hWF with
          | struct _ _ _ hLen hFit hDisj hChildren =>
            cases v with
            | aggregate var vals =>
              simp only [deinitFieldSlot] at h
              obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
              obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
              have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
              have hN := stepped_tryIntoValue?_none (sh := explodeAggregate var vals)
                (disc' := (explodeAggregate var vals).discriminantSet &&
                  ((none : Option Nat).isNone || ts)) hc hU
              rw [normalizeShell_eq_of_tagged hN rfl (by simp [explodeAggregate])]
              simp only [SlotBytes] at hS
              obtain ⟨hL1, hL2, hAll⟩ := (valuesBytes_iff enc img vals offs ls base).mp hS
              have hLtF : f < vals.length := (List.getElem?_eq_some_iff.mp hcv).1
              have hSub := pathRange_sub rest (hChildren f l hl) hRange
              have hFitF := hFit f o l ho hl
              simp only [explodeAggregate, SlotBytes]
              refine (slotsBytes_iff enc _ _ offs ls base).mpr ⟨?_, ?_, fun i ci hi => ?_⟩
              · simp [hL1]
              · simp [hL2]
              · by_cases hif : i = f
                · subst hif
                  rw [List.getElem?_set_self (by simpa using hLtF)] at hi
                  cases hi
                  obtain ⟨o', l', ho', hl', hb⟩ := hAll i cv hcv
                  rw [ho] at ho'
                  rw [hl] at hl'
                  cases ho'
                  cases hl'
                  refine ⟨o, l, ho, hl, ?_⟩
                  exact deinitFieldSlot_bytes_sim ts L enc img rest cv l (base + o) _ off len hcc
                    hTagRest (hChildren i l hl) (by simp only [ByteLayout.size] at hFits; omega)
                    hb hRange
                · rw [List.getElem?_set_ne (Ne.symm hif), List.getElem?_map] at hi
                  cases hw : vals[i]? with
                  | none => rw [hw] at hi; nomatch hi
                  | some w =>
                    rw [hw] at hi
                    simp only [Option.map_some, Option.some.injEq] at hi
                    subst hi
                    obtain ⟨oi, li, hoi, hli, hb⟩ := hAll i w hw
                    refine ⟨oi, li, hoi, hli, slotBytes_frame (hChildren i li hli) _ _
                      (fun k hk => deinitBytes_getElem?_outside ?_) hb⟩
                    rcases hDisj i f oi o li l hif hoi ho hli hl with hD | hD <;> omega
            | _ => nomatch h
        · nomatch hRange
      | downcast nm dv =>
        rcases rest with _ | ⟨b, rest'⟩
        · simp [pathRange] at hRange
        · cases b with
          | field f ty =>
            have hTs : ts = true := by
              rcases hTag with hT | hND
              · exact hT
              · simp [noDowncast] at hND
            simp only [pathRange] at hRange
            split at hRange
            · rename_i o l ho hl
              cases hWF with
              | struct _ _ _ hLen hFit hDisj hChildren =>
                cases v with
                | aggregate var vals =>
                  simp only [deinitFieldSlot] at h
                  obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
                  obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
                  have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
                  have hN := stepped_tryIntoValue?_none (sh := explodeAggregate var vals)
                    (disc' := (explodeAggregate var vals).discriminantSet &&
                      ((some dv).isNone || ts)) hc hU
                  rw [normalizeShell_eq_of_tagged hN rfl (by simp [explodeAggregate, hTs])]
                  simp only [SlotBytes] at hS
                  obtain ⟨hL1, hL2, hAll⟩ := (valuesBytes_iff enc img vals offs ls base).mp hS
                  have hLtF : f < vals.length := (List.getElem?_eq_some_iff.mp hcv).1
                  have hSub := pathRange_sub rest' (hChildren f l hl) hRange
                  have hFitF := hFit f o l ho hl
                  simp only [explodeAggregate, SlotBytes]
                  refine (slotsBytes_iff enc _ _ offs ls base).mpr ⟨?_, ?_, fun i ci hi => ?_⟩
                  · simp [hL1]
                  · simp [hL2]
                  · by_cases hif : i = f
                    · subst hif
                      rw [List.getElem?_set_self (by simpa using hLtF)] at hi
                      cases hi
                      obtain ⟨o', l', ho', hl', hb⟩ := hAll i cv hcv
                      rw [ho] at ho'
                      rw [hl] at hl'
                      cases ho'
                      cases hl'
                      refine ⟨o, l, ho, hl, ?_⟩
                      exact deinitFieldSlot_bytes_sim ts L enc img rest' cv l (base + o) _ off len
                        hcc (Or.inl hTs) (hChildren i l hl)
                        (by simp only [ByteLayout.size] at hFits; omega) hb hRange
                    · rw [List.getElem?_set_ne (Ne.symm hif), List.getElem?_map] at hi
                      cases hw : vals[i]? with
                      | none => rw [hw] at hi; nomatch hi
                      | some w =>
                        rw [hw] at hi
                        simp only [Option.map_some, Option.some.injEq] at hi
                        subst hi
                        obtain ⟨oi, li, hoi, hli, hb⟩ := hAll i w hw
                        refine ⟨oi, li, hoi, hli, slotBytes_frame (hChildren i li hli) _ _
                          (fun k hk => deinitBytes_getElem?_outside ?_) hb⟩
                        rcases hDisj i f oi o li l hif hoi ho hli hl with hD | hD <;> omega
                | _ => nomatch h
            · nomatch hRange
          | _ => simp [pathRange] at hRange
      | _ => simp [pathRange] at hRange

/-- **`Deinit` of a nested field of an initialized local is MiniRust's byte-range `Uninit`
write** (arbitrary depth, across both struct `Field` steps and tag-preserving enum `Downcast` +
`Field` steps): if the bytes of an initialized local represent its value under a well-formed
nested layout, then after Anneal's `Deinit` the local's new state is represented by the image in
which exactly the place's bytes are `Uninit`, and every other byte (including any explicit enum
tag bytes outside `[off, off + len)`) is unchanged. -/
theorem evalDeinitPlace_nested_bytes_simulation {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} {rootVal : Value} (enc : Value → List UInt8) (lay : ByteLayout)
    (img : ByteImage) (hRoot : slots[place.local_]? = some (.init rootVal))
    (h : evalDeinitPlace ts slots place = some slots')
    (hTag : ts = true ∨ noDowncast place.projection = true) (hWF : lay.WF)
    (hFits : lay.size ≤ img.length) (hS : SlotBytes enc img lay 0 (.init rootVal)) {off len : Nat}
    (hRange : pathRange lay 0 place.projection = some (off, len)) :
    ∃ st', slots'[place.local_]? = some st' ∧
      SlotBytes enc (deinitBytes img off len) lay 0 (slotStateToFieldSlot st') ∧
      ∀ i, ¬ (off ≤ i ∧ i < off + len) → (deinitBytes img off len)[i]? = img[i]? := by
  obtain ⟨st, hSt, _, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  rw [hRoot] at hSt
  cases hSt
  have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hD
  obtain ⟨hRound, _⟩ := UninitAt.roundtrip hU
  have hLt : place.local_ < slots.length := (List.getElem?_eq_some_iff.mp hRoot).1
  refine ⟨fieldSlotToLocalSlotState slot', List.getElem?_set_self hLt, ?_,
    fun i hi => deinitBytes_getElem?_outside hi⟩
  rw [hRound]
  exact deinitFieldSlot_bytes_sim ts _ enc img _ rootVal lay 0 slot' off len hD hTag hWF
    (by omega) hS hRange

/-- **Tag-apart enum field `Deinit` preserves `evalAdtDiscriminant`**: when deinitializing field
`f` of variant `v` of an initialized enum local whose tag is stored apart from its fields
(`spec.tagSurvivesFieldDeinit = true`, e.g. `#[repr(Int)]` or `#[repr(C, Int)]`), the local
transitions to a partial shell with `discriminantSet = true` whose `evalAdtDiscriminant` equals
the original initialized enum's discriminant. (The byte-level counterpart — the `Uninit` range
spares the tag bytes — is `evalDeinitPlace_taggedEnum_bytes_simulation`.) -/
theorem evalDeinitPlace_enum_field_preserves_discriminant
    {slots slots' : List LocalSlotState} {loc : Local} {v f : Nat} {vals : List Value}
    {nm : Option String} {ty : Ty} {rest : List ProjectionElem}
    (spec : AdtDiscrSpec) (wf : Value → Bool) (hApart : spec.tagSurvivesFieldDeinit = true)
    (hRoot : slots[loc]? = some (.init (.aggregate v vals)))
    (h : evalDeinitPlace true slots ⟨loc, .downcast nm v :: .field f ty :: rest⟩ = some slots') :
    ∃ sh, slots'[loc]? = some (.partialShell sh) ∧ sh.discriminantSet = true ∧
      shellVariant sh = v ∧
      evalAdtDiscriminant spec wf (.partialShell sh) =
        evalAdtDiscriminant spec wf (.init (.aggregate v vals)) := by
  obtain ⟨st, hSt, _, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  simp only at hSt hD
  rw [hRoot] at hSt
  cases hSt
  simp only [slotStateToFieldSlot, deinitFieldSlot] at hD
  obtain ⟨_, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some hD
  have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
  have hN := stepped_tryIntoValue?_none (sh := explodeAggregate v vals)
    (disc' := (explodeAggregate v vals).discriminantSet && ((some v).isNone || true)) hc hU
  have hLoc : loc < slots.length := (List.getElem?_eq_some_iff.mp hRoot).1
  refine ⟨{ explodeAggregate v vals with
      discriminantSet := (explodeAggregate v vals).discriminantSet && ((some v).isNone || true)
      fields := (explodeAggregate v vals).fields.set f c' }, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [normalizeShell_eq_of_tagged hN rfl (by simp [explodeAggregate]),
      fieldSlotToLocalSlotState_toFieldSlot hN]
    exact List.getElem?_set_self hLoc
  · simp [explodeAggregate]
  · simp [shellVariant, explodeAggregate]
  · simp [evalAdtDiscriminant, tagIsReadable, hApart, explodeAggregate, shellVariant]

/-! #### From `AdtLayoutSpec` to nested byte layouts -/

/-- Every field of a `#[repr(C)]` field sequence has an offset. -/
theorem cOffset?_isSome :
    ∀ (start : Nat) (fs : List FieldLayout) (i : Nat), i < fs.length →
      ∃ o, cOffset? start fs i = some o
  | _, [], _, h => absurd h (Nat.not_lt_zero _)
  | start, f :: _, 0, _ => ⟨PlaceAndRvalue.alignUp start f.align, rfl⟩
  | start, f :: fs, i + 1, h => by
    simp only [cOffset?]
    exact cOffset?_isSome _ fs i (by simpa using h)

/-- The byte offsets of the first `n` fields of variant `v` of `spec` (`resolveAdtOffsetOf`;
`0` stands for an unresolved offset, which `SpecFieldsPlaced` excludes). -/
def specOffsets (spec : AdtLayoutSpec) (v n : Nat) : List Nat :=
  (List.range n).map (fun i => (resolveAdtOffsetOf spec v i).getD 0)

theorem specOffsets_length (spec : AdtLayoutSpec) (v n : Nat) :
    (specOffsets spec v n).length = n := by
  simp [specOffsets]

theorem specOffsets_getElem? {spec : AdtLayoutSpec} {v n i o : Nat}
    (h : (specOffsets spec v n)[i]? = some o) :
    i < n ∧ (resolveAdtOffsetOf spec v i).getD 0 = o := by
  have hLt : i < n := by
    have := (List.getElem?_eq_some_iff.mp h).1
    simpa [specOffsets] using this
  refine ⟨hLt, ?_⟩
  simp only [specOffsets, List.getElem?_map, List.getElem?_range hLt, Option.map_some,
    Option.some.injEq] at h
  exact h

/-- The byte layout of variant `v` of an ADT laid out by `spec` whose field `i` has the byte
layout `children[i]`: a struct of the ADT's size (`adtLayout?`) whose field `i` sits at
`resolveAdtOffsetOf spec v i` (`none` when the ADT has no exact layout). This is the layout
`SlotBytes`/`pathRange` use for a local of the ADT holding variant `v`. -/
def specByteLayout (spec : AdtLayoutSpec) (v : Nat) (children : List ByteLayout) :
    Option ByteLayout :=
  match adtLayout? spec with
  | none => none
  | some (size, _) => some (.struct size (specOffsets spec v children.length) children)

/-- The byte layouts `children` describe the fields `fs`: one well-formed layout per field, of
exactly the field's size. -/
structure ChildrenFit (fs : List FieldLayout) (children : List ByteLayout) : Prop where
  length_eq : children.length = fs.length
  size_eq : ∀ (i : Nat) (l : ByteLayout) (fl : FieldLayout), children[i]? = some l →
    fs[i]? = some fl → l.size = fl.size
  wf : ∀ (i : Nat) (l : ByteLayout), children[i]? = some l → l.WF

/-- Every field of variant `v` (with fields `fs`) of `spec` has a resolved offset, and distinct
fields occupy disjoint byte ranges (true of `#[repr(C)]` structs and explicit-tag enums; false of
unions, whose fields all sit at offset `0`). -/
structure SpecFieldsPlaced (spec : AdtLayoutSpec) (v : Nat) (fs : List FieldLayout) : Prop where
  defined : ∀ i, i < fs.length → ∃ o, resolveAdtOffsetOf spec v i = some o
  disjoint : ∀ (i j oi oj : Nat) (fi fj : FieldLayout), i ≠ j →
    resolveAdtOffsetOf spec v i = some oi → resolveAdtOffsetOf spec v j = some oj →
    fs[i]? = some fi → fs[j]? = some fj → oi + fi.size ≤ oj ∨ oj + fj.size ≤ oi

/-- Inversion of `specOffsets` for placed fields: the offset of field `i` is its resolved
`resolveAdtOffsetOf`. -/
theorem specOffsets_getElem?_placed {spec : AdtLayoutSpec} {v : Nat} {fs : List FieldLayout}
    (hPl : SpecFieldsPlaced spec v fs) {n i o : Nat} (hn : n = fs.length)
    (h : (specOffsets spec v n)[i]? = some o) :
    i < fs.length ∧ resolveAdtOffsetOf spec v i = some o := by
  obtain ⟨hi, hEq⟩ := specOffsets_getElem? h
  subst hn
  obtain ⟨o', hO'⟩ := hPl.defined i hi
  rw [hO'] at hEq
  simp only [Option.getD_some] at hEq
  subst hEq
  exact ⟨hi, hO'⟩

/-- **The spec-built byte layout is well formed** (`ByteLayout.WF`): every field lies inside the
ADT (`resolveAdtOffsetOf_bounds_and_align`), distinct fields are disjoint (`SpecFieldsPlaced`),
and every child layout is well formed. -/
theorem specByteLayout_wf {spec : AdtLayoutSpec} (hWF : spec.WF) {v : Nat}
    {fs : List FieldLayout} {children : List ByteLayout} {size align : Nat}
    (hLay : adtLayout? spec = some (size, align)) (hVF : variantFields spec v = some fs)
    (hPl : SpecFieldsPlaced spec v fs) (hCh : ChildrenFit fs children) :
    specByteLayout spec v children =
        some (.struct size (specOffsets spec v children.length) children) ∧
      (ByteLayout.struct size (specOffsets spec v children.length) children).WF := by
  refine ⟨by simp [specByteLayout, hLay], ?_⟩
  refine .struct _ _ _ (specOffsets_length _ _ _) ?_ ?_ hCh.wf
  · intro i o l ho hl
    obtain ⟨hi, hO⟩ := specOffsets_getElem?_placed hPl hCh.length_eq ho
    obtain ⟨fs', fl, size', align', hVF', hFl, hLay', hBound, _⟩ :=
      resolveAdtOffsetOf_bounds_and_align spec hWF hO
    rw [hVF] at hVF'
    cases hVF'
    rw [hLay] at hLay'
    simp only [Option.some.injEq, Prod.mk.injEq] at hLay'
    obtain ⟨rfl, rfl⟩ := hLay'
    rw [hCh.size_eq i l fl hl hFl]
    exact hBound
  · intro i j oi oj li lj hNe hoi hoj hli hlj
    obtain ⟨hi, hOi⟩ := specOffsets_getElem?_placed hPl hCh.length_eq hoi
    obtain ⟨hj, hOj⟩ := specOffsets_getElem?_placed hPl hCh.length_eq hoj
    have hfi : fs[i]? = some fs[i] := List.getElem?_eq_getElem hi
    have hfj : fs[j]? = some fs[j] := List.getElem?_eq_getElem hj
    rw [hCh.size_eq i li _ hli hfi, hCh.size_eq j lj _ hlj hfj]
    exact hPl.disjoint i j oi oj _ _ hNe hOi hOj hfi hfj

/-- A `#[repr(C)]` struct always has an exact layout. -/
theorem adtLayout?_reprC_struct {spec : AdtLayoutSpec} {fs : List FieldLayout}
    (hShape : spec.shape = .struct fs) (hRepr : spec.repr = .c) :
    adtLayout? spec = some (PlaceAndRvalue.alignUp (cEnd 0 fs) (maxAlign (spec.reprAlign.getD 1) fs),
      maxAlign (spec.reprAlign.getD 1) fs) := by
  simp [adtLayout?, hShape, structLayout?, hRepr]

/-- **`#[repr(C)]` struct fields are placed**: every field has its declaration-order offset and
distinct fields are disjoint (`resolveAdtOffsetOf_reprC_monotone`). -/
theorem reprC_struct_placed {spec : AdtLayoutSpec} {fs : List FieldLayout}
    (hShape : spec.shape = .struct fs) (hRepr : spec.repr = .c) : SpecFieldsPlaced spec 0 fs where
  defined i hi := by
    obtain ⟨o, ho⟩ := cOffset?_isSome 0 fs i hi
    refine ⟨o, ?_⟩
    simp [resolveAdtOffsetOf, adtLayout?_reprC_struct hShape hRepr, hShape, structFieldOffset?,
      hRepr, ho]
  disjoint i j oi oj fi fj hNe hoi hoj hfi hfj := by
    rcases Nat.lt_or_gt_of_ne hNe with hlt | hgt
    · obtain ⟨fi', hfi', hle⟩ := resolveAdtOffsetOf_reprC_monotone hShape hRepr hlt hoi hoj
      rw [hfi] at hfi'
      cases hfi'
      exact Or.inl hle
    · obtain ⟨fj', hfj', hle⟩ := resolveAdtOffsetOf_reprC_monotone hShape hRepr hgt hoj hoi
      rw [hfj] at hfj'
      cases hfj'
      exact Or.inr hle

/-- Every field of a declaration-order field sequence has a prefix-sum offset. -/
theorem rustOffset?_isSome :
    ∀ (start : Nat) (fs : List FieldLayout) (i : Nat), i < fs.length →
      ∃ o, rustOffset? start fs i = some o
  | _, [], _, h => absurd h (Nat.not_lt_zero _)
  | start, _ :: _, 0, _ => ⟨start, rfl⟩
  | start, f :: fs, i + 1, h => by
    simp only [rustOffset?]
    exact rustOffset?_isSome _ fs i (by simpa using h)

/-- Every prefix-sum offset is at least the starting offset. -/
theorem rustOffset?_ge_start :
    ∀ (start : Nat) (fs : List FieldLayout) (i off : Nat), rustOffset? start fs i = some off →
      start ≤ off
  | _, [], _, _, h => by simp [rustOffset?] at h
  | start, _ :: _, 0, off, h => by
    simp only [rustOffset?, Option.some.injEq] at h
    omega
  | start, f :: fs, i + 1, off, h => by
    simp only [rustOffset?] at h
    have := rustOffset?_ge_start _ fs i off h
    omega

/-- **Prefix-sum offset monotonicity**: an earlier field ends at or before a later field's
offset. -/
theorem rustOffset?_monotone :
    ∀ (start : Nat) (fs : List FieldLayout) (i j oi oj : Nat), i < j →
      rustOffset? start fs i = some oi → rustOffset? start fs j = some oj →
      ∃ fi, fs[i]? = some fi ∧ oi + fi.size ≤ oj
  | _, [], _, _, _, _, _, h, _ => by simp [rustOffset?] at h
  | _, _ :: _, _, 0, _, _, hLt, _, _ => absurd hLt (Nat.not_lt_zero _)
  | start, f :: fs, 0, j + 1, oi, oj, _, hi, hj => by
    simp only [rustOffset?, Option.some.injEq] at hi hj
    subst hi
    exact ⟨f, rfl, rustOffset?_ge_start _ fs j oj hj⟩
  | start, f :: fs, i + 1, j + 1, oi, oj, hLt, hi, hj => by
    simp only [rustOffset?] at hi hj
    obtain ⟨fi, hFi, hLe⟩ := rustOffset?_monotone _ fs i j oi oj (by omega) hi hj
    exact ⟨fi, by simpa using hFi, hLe⟩

/-- Canonical `#[repr(Rust)]` struct field offsets (declaration order kept and padding-free): the
declaration-order prefix sums. -/
theorem resolveAdtOffsetOf_reprRust_struct {spec : AdtLayoutSpec} {fs : List FieldLayout}
    (hShape : spec.shape = .struct fs) (hRepr : spec.repr = .rust)
    (hCanon : spec.rustOrderCanonical = true) (hPad : paddingFree 0 fs = true) (i : Nat) :
    resolveAdtOffsetOf spec 0 i = rustOffset? 0 fs i := by
  simp [resolveAdtOffsetOf, adtLayout?, hShape, structLayout?, hRepr, structFieldOffset?, hCanon,
    hPad]

/-- **Canonical `#[repr(Rust)]` struct fields are placed** (`Ty::has_canonical_byte_layout`):
every field has its prefix-sum offset and distinct fields are disjoint. -/
theorem reprRust_canonical_struct_placed {spec : AdtLayoutSpec} {fs : List FieldLayout}
    (hShape : spec.shape = .struct fs) (hRepr : spec.repr = .rust)
    (hCanon : spec.rustOrderCanonical = true) (hPad : paddingFree 0 fs = true) :
    SpecFieldsPlaced spec 0 fs where
  defined i hi := by
    rw [resolveAdtOffsetOf_reprRust_struct hShape hRepr hCanon hPad]
    exact rustOffset?_isSome 0 fs i hi
  disjoint i j oi oj fi fj hNe hoi hoj hfi hfj := by
    rw [resolveAdtOffsetOf_reprRust_struct hShape hRepr hCanon hPad] at hoi hoj
    rcases Nat.lt_or_gt_of_ne hNe with hlt | hgt
    · obtain ⟨fi', hfi', hle⟩ := rustOffset?_monotone 0 fs i j oi oj hlt hoi hoj
      rw [hfi] at hfi'
      cases hfi'
      exact Or.inl hle
    · obtain ⟨fj', hfj', hle⟩ := rustOffset?_monotone 0 fs j i oj oi hgt hoj hoi
      rw [hfj] at hfj'
      cases hfj'
      exact Or.inr hle

/-- `#[repr(Int)]` enum field offsets: `#[repr(C)]` offsets of the variant's fields after the tag. -/
theorem resolveAdtOffsetOf_reprInt_enum {spec : AdtLayoutSpec} {tagSize : Nat}
    {vs : List (List FieldLayout)} (hShape : spec.shape = .taggedEnum tagSize vs)
    (hRepr : spec.repr = .rust) {v : Nat} {fs : List FieldLayout} (hV : vs[v]? = some fs)
    (i : Nat) : resolveAdtOffsetOf spec v i = cOffset? tagSize fs i := by
  simp [resolveAdtOffsetOf, adtLayout?, hShape, taggedLayout?, hRepr, taggedFieldOffset?, hV]

/-- `#[repr(C, Int)]` enum field offsets: the payload union's offset plus the `#[repr(C)]` offset
of the field in its variant's struct. -/
theorem resolveAdtOffsetOf_reprCInt_enum {spec : AdtLayoutSpec} {tagSize : Nat}
    {vs : List (List FieldLayout)} (hShape : spec.shape = .taggedEnum tagSize vs)
    (hRepr : spec.repr = .c) {v : Nat} {fs : List FieldLayout} (hV : vs[v]? = some fs)
    (i : Nat) :
    resolveAdtOffsetOf spec v i =
      (cOffset? 0 fs i).map (fun inner => payloadOffset tagSize vs + inner) := by
  simp [resolveAdtOffsetOf, adtLayout?, hShape, taggedLayout?, hRepr, taggedFieldOffset?, hV]

/-- An explicit-tag enum (`#[repr(Int)]` / `#[repr(C, Int)]`) always has an exact layout. -/
theorem adtLayout?_taggedEnum_isSome {spec : AdtLayoutSpec} {tagSize : Nat}
    {vs : List (List FieldLayout)} (hShape : spec.shape = .taggedEnum tagSize vs)
    (hRepr : spec.repr ≠ .transparent) : ∃ size align, adtLayout? spec = some (size, align) := by
  cases hR : spec.repr with
  | transparent => exact absurd hR hRepr
  | rust => simp [adtLayout?, hShape, taggedLayout?, hR]
  | c => simp [adtLayout?, hShape, taggedLayout?, hR]

/-- **Explicit-tag enum variant fields are placed**: every field of variant `v` has an offset and
distinct fields of the same variant are disjoint (`cOffset?_monotone`, shifted by the payload
offset for `#[repr(C, Int)]`). -/
theorem taggedEnum_placed {spec : AdtLayoutSpec} {tagSize : Nat} {vs : List (List FieldLayout)}
    (hShape : spec.shape = .taggedEnum tagSize vs) (hRepr : spec.repr ≠ .transparent)
    {v : Nat} {fs : List FieldLayout} (hV : vs[v]? = some fs) : SpecFieldsPlaced spec v fs := by
  cases hR : spec.repr with
  | transparent => exact absurd hR hRepr
  | rust =>
    refine ⟨fun i hi => ?_, fun i j oi oj fi fj hNe hoi hoj hfi hfj => ?_⟩
    · rw [resolveAdtOffsetOf_reprInt_enum hShape hR hV]
      exact cOffset?_isSome tagSize fs i hi
    · rw [resolveAdtOffsetOf_reprInt_enum hShape hR hV] at hoi hoj
      rcases Nat.lt_or_gt_of_ne hNe with hlt | hgt
      · obtain ⟨fi', hfi', hle⟩ := cOffset?_monotone tagSize fs i j oi oj hlt hoi hoj
        rw [hfi] at hfi'
        cases hfi'
        exact Or.inl hle
      · obtain ⟨fj', hfj', hle⟩ := cOffset?_monotone tagSize fs j i oj oi hgt hoj hoi
        rw [hfj] at hfj'
        cases hfj'
        exact Or.inr hle
  | c =>
    refine ⟨fun i hi => ?_, fun i j oi oj fi fj hNe hoi hoj hfi hfj => ?_⟩
    · rw [resolveAdtOffsetOf_reprCInt_enum hShape hR hV]
      obtain ⟨o, ho⟩ := cOffset?_isSome 0 fs i hi
      exact ⟨payloadOffset tagSize vs + o, by simp [ho]⟩
    · rw [resolveAdtOffsetOf_reprCInt_enum hShape hR hV] at hoi hoj
      cases hI : cOffset? 0 fs i with
      | none => rw [hI] at hoi; nomatch hoi
      | some ii =>
        cases hJ : cOffset? 0 fs j with
        | none => rw [hJ] at hoj; nomatch hoj
        | some jj =>
          rw [hI] at hoi
          rw [hJ] at hoj
          simp only [Option.map_some, Option.some.injEq] at hoi hoj
          subst hoi hoj
          rcases Nat.lt_or_gt_of_ne hNe with hlt | hgt
          · obtain ⟨fi', hfi', hle⟩ := cOffset?_monotone 0 fs i j ii jj hlt hI hJ
            rw [hfi] at hfi'
            cases hfi'
            left
            omega
          · obtain ⟨fj', hfj', hle⟩ := cOffset?_monotone 0 fs j i jj ii hgt hJ hI
            rw [hfj] at hfj'
            cases hfj'
            right
            omega

/-- The byte range of a `Field(f)` path into a struct layout lies inside field `f`'s range. -/
theorem pathRange_struct_field {n : Nat} {offs : List Nat} {ls : List ByteLayout} {base f : Nat}
    {ty : Ty} {rest : List ProjectionElem} {off len : Nat}
    (hWF : (ByteLayout.struct n offs ls).WF)
    (h : pathRange (.struct n offs ls) base (.field f ty :: rest) = some (off, len)) :
    ∃ o l, offs[f]? = some o ∧ ls[f]? = some l ∧ base + o ≤ off ∧ off + len ≤ base + o + l.size := by
  simp only [pathRange] at h
  split at h
  · rename_i o l ho hl
    cases hWF with
    | struct _ _ _ _ _ _ hChildren =>
      have := pathRange_sub rest (hChildren f l hl) h
      exact ⟨o, l, ho, hl, this.1, this.2⟩
  · nomatch h

/-- The byte range of a `Downcast(v)` + `Field(f)` path into a variant layout lies inside field
`f`'s range. -/
theorem pathRange_struct_downcast_field {n : Nat} {offs : List Nat} {ls : List ByteLayout}
    {base f : Nat} {nm : Option String} {dv : Nat} {ty : Ty} {rest : List ProjectionElem}
    {off len : Nat} (hWF : (ByteLayout.struct n offs ls).WF)
    (h : pathRange (.struct n offs ls) base (.downcast nm dv :: .field f ty :: rest) =
      some (off, len)) :
    ∃ o l, offs[f]? = some o ∧ ls[f]? = some l ∧ base + o ≤ off ∧ off + len ≤ base + o + l.size := by
  simp only [pathRange] at h
  split at h
  · rename_i o l ho hl
    cases hWF with
    | struct _ _ _ _ _ _ hChildren =>
      have := pathRange_sub rest (hChildren f l hl) h
      exact ⟨o, l, ho, hl, this.1, this.2⟩
  · nomatch h

/-- **Spec-built nested byte simulation of `Deinit`** (the `Translate.lean:3742` bridge over
`resolveAdtOffsetOf`): for an ADT laid out by `spec` whose variant-`v` fields are placed
(`SpecFieldsPlaced`: `#[repr(C)]` structs, explicit-tag enums) and described by well-formed
child layouts, the spec-built layout is well formed, and `Deinit` of a `Field` (or, when the tag
survives, `Downcast` + `Field`) path into an initialized local represented under it is MiniRust's
`Uninit` write over the path's byte range, which lies inside the ADT. -/
theorem evalDeinitPlace_spec_bytes_simulation {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} {rootVal : Value} {spec : AdtLayoutSpec} (hWF : spec.WF) {v : Nat}
    {fs : List FieldLayout} {children : List ByteLayout} {size align : Nat}
    (hLay : adtLayout? spec = some (size, align)) (hVF : variantFields spec v = some fs)
    (hPl : SpecFieldsPlaced spec v fs) (hCh : ChildrenFit fs children)
    (enc : Value → List UInt8) (img : ByteImage)
    (hRoot : slots[place.local_]? = some (.init rootVal))
    (h : evalDeinitPlace ts slots place = some slots')
    (hTag : ts = true ∨ noDowncast place.projection = true) (hFits : size ≤ img.length)
    (hS : SlotBytes enc img (.struct size (specOffsets spec v children.length) children) 0
      (.init rootVal))
    {off len : Nat}
    (hRange : pathRange (.struct size (specOffsets spec v children.length) children) 0
      place.projection = some (off, len)) :
    off + len ≤ size ∧
    ∃ st', slots'[place.local_]? = some st' ∧
      SlotBytes enc (deinitBytes img off len)
        (.struct size (specOffsets spec v children.length) children) 0 (slotStateToFieldSlot st') ∧
      ∀ i, ¬ (off ≤ i ∧ i < off + len) → (deinitBytes img off len)[i]? = img[i]? := by
  obtain ⟨_, hLWF⟩ := specByteLayout_wf hWF hLay hVF hPl hCh
  have hSub := pathRange_sub place.projection hLWF hRange
  simp only [ByteLayout.size] at hSub
  exact ⟨by omega, evalDeinitPlace_nested_bytes_simulation enc _ img hRoot h hTag hLWF
    (by simpa only [ByteLayout.size] using hFits) hS hRange⟩

/-- `AdtDef::requires_tag_write` of the ADT laid out by `spec`: explicit-tag enums and the
tagged enums whose layout the model leaves unspecified (tagless `#[repr(C)]` enums, tagless enums
with several present variants) store a tag; structs, unions, and tagless univariant/no-present
enums do not. -/
def AdtLayoutSpec.requiresTagWrite (spec : AdtLayoutSpec) : Bool :=
  match spec.shape with
  | .taggedEnum _ _ => true
  | .unspecifiedEnum vs => !vs.isEmpty
  | _ => false

/-- `AdtDef::tag_survives_field_deinit` of the ADT laid out by `spec`: an explicit tag or the C
`int` tag of a tagless `#[repr(C)]` enum is stored apart from the fields, and an ADT without a
stored tag has none to lose; a tagless `#[repr(Rust)]` enum with several present variants may
keep its tag in a field's niche, so its tag is lost. -/
def AdtLayoutSpec.tagSurvivesFieldDeinit (spec : AdtLayoutSpec) : Bool :=
  match spec.shape with
  | .unspecifiedEnum vs => spec.repr == .c || vs.isEmpty
  | _ => true

/-- The discriminant facts `dspec` (§1c) describe the ADT laid out by `spec`: they agree on
whether a tag is stored and whether it survives field deinitialization. -/
structure AdtDiscrSpec.CoherentWith (dspec : AdtDiscrSpec) (spec : AdtLayoutSpec) : Prop where
  requiresTagWrite_eq : dspec.requiresTagWrite = spec.requiresTagWrite
  tagSurvives_eq : dspec.tagSurvivesFieldDeinit = spec.tagSurvivesFieldDeinit

/-- **Explicit-tag enum field `Deinit` is a byte-range `Uninit` write that spares the tag**: for
an explicit-tag enum (`#[repr(Int)]` / `#[repr(C, Int)]`) laid out by `spec`, with discriminant
facts `dspec` coherent with it, whose initialized local holds variant `v` and is represented under
the spec-built layout of variant `v`, `Deinit` of `Downcast(v).f.rest` (evaluated with
`spec.tagSurvivesFieldDeinit`, which is `true`):
- the spec-built layout is well formed and the place's byte range `[off, off + len)` lies inside
  field `f`'s range `[o, o + size f)` with `o = resolveAdtOffsetOf spec v f`, so after the tag
  (`tagSize ≤ o ≤ off`) and inside the enum;
- the local becomes a shell represented by the image in which exactly that range is `Uninit`;
- every tag byte `k < tagSize` is unchanged, the shell's tag is still written, and the
  discriminant read from the shell is the original value's. -/
theorem evalDeinitPlace_taggedEnum_bytes_simulation
    {slots slots' : List LocalSlotState} {loc : Local} {v f : Nat} {vals : List Value}
    {nm : Option String} {ty : Ty} {rest : List ProjectionElem}
    {spec : AdtLayoutSpec} (hWF : spec.WF) {tagSize : Nat} {vs : List (List FieldLayout)}
    (hShape : spec.shape = .taggedEnum tagSize vs) (hRepr : spec.repr ≠ .transparent)
    {fs : List FieldLayout} (hV : vs[v]? = some fs) {children : List ByteLayout}
    (hCh : ChildrenFit fs children) (dspec : AdtDiscrSpec) (hCoh : dspec.CoherentWith spec)
    (wf : Value → Bool) (enc : Value → List UInt8) (img : ByteImage) {lay : ByteLayout}
    (hLay : specByteLayout spec v children = some lay)
    (hRoot : slots[loc]? = some (.init (.aggregate v vals)))
    (h : evalDeinitPlace spec.tagSurvivesFieldDeinit slots
      ⟨loc, .downcast nm v :: .field f ty :: rest⟩ = some slots')
    (hFits : lay.size ≤ img.length) (hS : SlotBytes enc img lay 0 (.init (.aggregate v vals)))
    {off len : Nat}
    (hRange : pathRange lay 0 (.downcast nm v :: .field f ty :: rest) = some (off, len)) :
    lay.WF ∧ dspec.requiresTagWrite = true ∧
    (∃ o fl, resolveAdtOffsetOf spec v f = some o ∧ fs[f]? = some fl ∧
      tagSize ≤ o ∧ o ≤ off ∧ off + len ≤ o + fl.size ∧ o + fl.size ≤ lay.size) ∧
    ∃ sh, slots'[loc]? = some (.partialShell sh) ∧
      SlotBytes enc (deinitBytes img off len) lay 0 sh.toFieldSlot ∧
      sh.discriminantSet = true ∧
      evalAdtDiscriminant dspec wf (.partialShell sh) =
        evalAdtDiscriminant dspec wf (.init (.aggregate v vals)) ∧
      (∀ k, k < tagSize → (deinitBytes img off len)[k]? = img[k]?) ∧
      ∀ i, ¬ (off ≤ i ∧ i < off + len) → (deinitBytes img off len)[i]? = img[i]? := by
  have hTS : spec.tagSurvivesFieldDeinit = true := by
    simp [AdtLayoutSpec.tagSurvivesFieldDeinit, hShape]
  have hRTW : dspec.requiresTagWrite = true := by
    rw [hCoh.requiresTagWrite_eq]
    simp [AdtLayoutSpec.requiresTagWrite, hShape]
  have hApart : dspec.tagSurvivesFieldDeinit = true := by rw [hCoh.tagSurvives_eq, hTS]
  rw [hTS] at h
  obtain ⟨size, align, hL⟩ := adtLayout?_taggedEnum_isSome hShape hRepr
  have hVF : variantFields spec v = some fs := by simp [variantFields, hShape, hV]
  have hPl := taggedEnum_placed hShape hRepr hV
  obtain ⟨hEq, hLWF⟩ := specByteLayout_wf hWF hL hVF hPl hCh
  rw [hEq] at hLay
  cases hLay
  -- the place's range lies inside field `f`'s range, which lies after the tag
  obtain ⟨o, l, ho, hl, hLo, hHi⟩ := pathRange_struct_downcast_field hLWF hRange
  obtain ⟨hfLt, hO⟩ := specOffsets_getElem?_placed hPl hCh.length_eq ho
  have hfl : fs[f]? = some fs[f] := List.getElem?_eq_getElem hfLt
  have hlSize := hCh.size_eq f l _ hl hfl
  have hTagLe : tagSize ≤ o := resolveAdtOffsetOf_taggedEnum_ge_tagSize hShape hO
  obtain ⟨fs', fl', size', align', hVF', hFl', hL', hBound, _⟩ :=
    resolveAdtOffsetOf_bounds_and_align spec hWF hO
  rw [hVF] at hVF'
  cases hVF'
  rw [hfl] at hFl'
  cases hFl'
  rw [hL] at hL'
  simp only [Option.some.injEq, Prod.mk.injEq] at hL'
  obtain ⟨rfl, rfl⟩ := hL'
  -- the shell and its discriminant
  obtain ⟨sh, hSh, hSet, _, hDisc⟩ :=
    evalDeinitPlace_enum_field_preserves_discriminant dspec wf hApart hRoot h
  -- the byte simulation
  obtain ⟨st', hSt', hBytes, hOut⟩ := evalDeinitPlace_nested_bytes_simulation enc _ img
    (place := ⟨loc, .downcast nm v :: .field f ty :: rest⟩) hRoot h (Or.inl rfl) hLWF hFits hS
    hRange
  have hSt'' : slots'[loc]? = some st' := hSt'
  rw [hSh] at hSt''
  cases hSt''
  refine ⟨hLWF, hRTW, ⟨o, fs[f], hO, hfl, hTagLe, by omega, by rw [← hlSize]; omega, hBound⟩,
    sh, hSh, hBytes, hSet, hDisc, fun k hk => hOut k (by omega), hOut⟩

/-- **Inactive `Downcast` variant fails closed (`evalDeinitPlace_downcast_inactive_variant_none`)**:
deinitializing `.downcast nm dv :: .field f ty :: rest` on an initialized aggregate of variant `v`
or a partial shell narrowed to variant `v` fails (`none`, `InactiveVariantProjection`) whenever
`dv ≠ v`. -/
theorem evalDeinitPlace_downcast_inactive_variant_none (ts : Bool) (slots : List LocalSlotState)
    (loc : Local) {v dv f : Nat} (nm : Option String) (ty : Ty) (rest : List ProjectionElem)
    (hNe : v ≠ dv) :
    (∀ vals, slots[loc]? = some (.init (.aggregate v vals)) →
      evalDeinitPlace ts slots ⟨loc, .downcast nm dv :: .field f ty :: rest⟩ = none) ∧
    (∀ sh, slots[loc]? = some (.partialShell sh) → shellVariant sh = v →
      evalDeinitPlace ts slots ⟨loc, .downcast nm dv :: .field f ty :: rest⟩ = none) := by
  refine ⟨fun vals hRoot => ?_, fun sh hRoot hVar => ?_⟩
  · simp [evalDeinitPlace, hRoot, slotStateToFieldSlot, deinitFieldSlot, deinitShellStep,
      explodeAggregate, shellVariant, hNe]
  · obtain ⟨var, adt, disc, fs⟩ := sh
    simp [evalDeinitPlace, hRoot, slotStateToFieldSlot, PartialAggregate.toFieldSlot,
      deinitFieldSlot, deinitShellStep, hVar, hNe]

/-- A successful `evalDeinitPlace` through `.downcast nm dv :: .field f ty :: rest` on an
initialized aggregate `.init (.aggregate v vals)` forces `dv = v` (`pathRange` may ignore `dv`
because `evalDeinitPlace` enforces `dv = v`). -/
theorem evalDeinitPlace_downcast_active_variant_eq {ts : Bool} {slots slots' : List LocalSlotState}
    {loc : Local} {v dv f : Nat} {vals : List Value} {nm : Option String} {ty : Ty}
    {rest : List ProjectionElem} (hRoot : slots[loc]? = some (.init (.aggregate v vals)))
    (h : evalDeinitPlace ts slots ⟨loc, .downcast nm dv :: .field f ty :: rest⟩ = some slots') :
    dv = v := by
  by_cases hEq : dv = v
  · exact hEq
  · have hNe : v ≠ dv := Ne.symm hEq
    simp [evalDeinitPlace, hRoot, slotStateToFieldSlot, deinitFieldSlot, deinitShellStep,
      explodeAggregate, shellVariant, hNe] at h

/-- **Univariant tagless enum present-variant placement (`univariantEnum_present_reprRust_placed`)**:
for a canonical padding-free `#[repr(Rust)]` univariant enum (`spec.shape = .univariantEnum present vs`),
the present variant `present` satisfies `SpecFieldsPlaced spec present fs`. -/
theorem univariantEnum_present_reprRust_placed {spec : AdtLayoutSpec} {present : Nat}
    {vs : List (List FieldLayout)} {fs : List FieldLayout}
    (hShape : spec.shape = .univariantEnum present vs) (hRepr : spec.repr = .rust)
    (hV : vs[present]? = some fs) (hCanon : spec.rustOrderCanonical = true)
    (hPad : paddingFree 0 fs = true) : SpecFieldsPlaced spec present fs where
  defined i hi := by
    have hOff : resolveAdtOffsetOf spec present i = rustOffset? 0 fs i := by
      simp [resolveAdtOffsetOf, adtLayout?, hShape, hV, hRepr, structLayout?, structFieldOffset?,
        hCanon, hPad]
    rw [hOff]
    exact rustOffset?_isSome 0 fs i hi
  disjoint i j oi oj fi fj hNe hoi hoj hfi hfj := by
    have hOff : ∀ k, resolveAdtOffsetOf spec present k = rustOffset? 0 fs k := fun k => by
      simp [resolveAdtOffsetOf, adtLayout?, hShape, hV, hRepr, structLayout?, structFieldOffset?,
        hCanon, hPad]
    rw [hOff i] at hoi
    rw [hOff j] at hoj
    rcases Nat.lt_or_gt_of_ne hNe with hlt | hgt
    · obtain ⟨fi', hfi', hle⟩ := rustOffset?_monotone 0 fs i j oi oj hlt hoi hoj
      rw [hfi] at hfi'; cases hfi'; exact Or.inl hle
    · obtain ⟨fj', hfj', hle⟩ := rustOffset?_monotone 0 fs j i oj oi hgt hoj hoi
      rw [hfj] at hfj'; cases hfj'; exact Or.inr hle

/-- **Univariant tagless enum absent-variant placement (`univariantEnum_absent_placed`)**:
every absent variant `v ≠ present` of a well-formed univariant enum with an exact layout has all
1-ZST fields (`size = 0`) at offset `0` and satisfies `SpecFieldsPlaced spec v fs`. -/
theorem univariantEnum_absent_placed {spec : AdtLayoutSpec} (hWF : spec.WF) {present v : Nat}
    {vs : List (List FieldLayout)} {fs : List FieldLayout} {size align : Nat}
    (hShape : spec.shape = .univariantEnum present vs)
    (hLay : adtLayout? spec = some (size, align))
    (hV : vs[v]? = some fs) (hNe : v ≠ present) : SpecFieldsPlaced spec v fs where
  defined i hi := ⟨0, by simp [resolveAdtOffsetOf, hLay, hShape, hV, hNe, absentFieldOffset?, hi]⟩
  disjoint i j oi oj fi fj _ hoi hoj hfi _ := by
    have hZero : fi.size = 0 :=
      hWF.absentZeroSized present vs hShape v fs hV hNe fi (getElem?_mem hfi)
    have hOi : oi = 0 := by
      simp only [resolveAdtOffsetOf, hLay, hShape, hV, hNe, ↓reduceIte, absentFieldOffset?] at hoi
      split at hoi
      · exact (Option.some.inj hoi).symm
      · nomatch hoi
    have hOj : oj = 0 := by
      simp only [resolveAdtOffsetOf, hLay, hShape, hV, hNe, ↓reduceIte, absentFieldOffset?] at hoj
      split at hoj
      · exact (Option.some.inj hoj).symm
      · nomatch hoj
    exact Or.inl (by omega)

/-- **All-absent enum placement (`noPresentEnum_placed`)**: every variant of a well-formed
`noPresentEnum` with an exact layout has all 1-ZST fields (`size = 0`) at offset `0` and satisfies
`SpecFieldsPlaced spec v fs`. -/
theorem noPresentEnum_placed {spec : AdtLayoutSpec} (hWF : spec.WF) {v : Nat}
    {vs : List (List FieldLayout)} {fs : List FieldLayout} {size align : Nat}
    (hShape : spec.shape = .noPresentEnum vs)
    (hLay : adtLayout? spec = some (size, align))
    (hV : vs[v]? = some fs) : SpecFieldsPlaced spec v fs where
  defined i hi := ⟨0, by simp [resolveAdtOffsetOf, hLay, hShape, hV, absentFieldOffset?, hi]⟩
  disjoint i j oi oj fi fj _ hoi hoj hfi _ := by
    have hZero : fi.size = 0 :=
      hWF.noPresentZeroSized vs hShape fs (getElem?_mem hV) fi (getElem?_mem hfi)
    have hOi : oi = 0 := by
      simp only [resolveAdtOffsetOf, hLay, hShape, hV, absentFieldOffset?] at hoi
      split at hoi
      · exact (Option.some.inj hoi).symm
      · nomatch hoi
    have hOj : oj = 0 := by
      simp only [resolveAdtOffsetOf, hLay, hShape, hV, absentFieldOffset?] at hoj
      split at hoj
      · exact (Option.some.inj hoj).symm
      · nomatch hoj
    exact Or.inl (by omega)

/-- **Univariant tagless enum byte simulation (`evalDeinitPlace_univariantEnum_bytes_simulation`)**:
for the present variant `present` of a canonical padding-free `#[repr(Rust)]` univariant enum
(`spec.shape = .univariantEnum present vs`) with coherent discriminant facts `dspec`, `Deinit` of
`Downcast(dv).f.rest` on an initialized local holding variant `present` forces `dv = present`,
writes `Uninit` over `[off, off + len)` inside field `f`, leaves all other bytes unchanged, and
preserves `evalAdtDiscriminant` (`dspec.requiresTagWrite = false`). -/
theorem evalDeinitPlace_univariantEnum_bytes_simulation
    {slots slots' : List LocalSlotState} {loc : Local} {present dv f : Nat} {vals : List Value}
    {nm : Option String} {ty : Ty} {rest : List ProjectionElem}
    {spec : AdtLayoutSpec} (hWF : spec.WF) {vs : List (List FieldLayout)}
    (hShape : spec.shape = .univariantEnum present vs) (hRepr : spec.repr = .rust)
    {fs : List FieldLayout} (hV : vs[present]? = some fs)
    (hCanon : spec.rustOrderCanonical = true) (hPad : paddingFree 0 fs = true)
    {children : List ByteLayout} (hCh : ChildrenFit fs children)
    (dspec : AdtDiscrSpec) (hCoh : dspec.CoherentWith spec)
    (wf : Value → Bool) (enc : Value → List UInt8) (img : ByteImage) {lay : ByteLayout}
    (hLay : specByteLayout spec present children = some lay)
    (hRoot : slots[loc]? = some (.init (.aggregate present vals)))
    (h : evalDeinitPlace spec.tagSurvivesFieldDeinit slots
      ⟨loc, .downcast nm dv :: .field f ty :: rest⟩ = some slots')
    (hFits : lay.size ≤ img.length) (hS : SlotBytes enc img lay 0 (.init (.aggregate present vals)))
    {off len : Nat}
    (hRange : pathRange lay 0 (.downcast nm dv :: .field f ty :: rest) = some (off, len)) :
    dv = present ∧ lay.WF ∧ dspec.requiresTagWrite = false ∧
    ∃ sh, slots'[loc]? = some (.partialShell sh) ∧
      SlotBytes enc (deinitBytes img off len) lay 0 sh.toFieldSlot ∧
      evalAdtDiscriminant dspec wf (.partialShell sh) =
        evalAdtDiscriminant dspec wf (.init (.aggregate present vals)) ∧
      ∀ i, ¬ (off ≤ i ∧ i < off + len) → (deinitBytes img off len)[i]? = img[i]? := by
  have hDv : present = dv := (evalDeinitPlace_downcast_active_variant_eq hRoot h).symm
  subst hDv
  have hTS : spec.tagSurvivesFieldDeinit = true := by
    simp [AdtLayoutSpec.tagSurvivesFieldDeinit, hShape]
  have hRTW : dspec.requiresTagWrite = false := by
    rw [hCoh.requiresTagWrite_eq]
    simp [AdtLayoutSpec.requiresTagWrite, hShape]
  have hApart : dspec.tagSurvivesFieldDeinit = true := by rw [hCoh.tagSurvives_eq, hTS]
  rw [hTS] at h
  have hL : adtLayout? spec = some
      (PlaceAndRvalue.alignUp (sumSizes fs) (maxAlign (spec.reprAlign.getD 1) fs),
        maxAlign (spec.reprAlign.getD 1) fs) := by
    simp [adtLayout?, hShape, hV, hRepr, structLayout?]
  have hVF : variantFields spec present = some fs := by simp [variantFields, hShape, hV]
  have hPl := univariantEnum_present_reprRust_placed hShape hRepr hV hCanon hPad
  obtain ⟨hEq, hLWF⟩ := specByteLayout_wf hWF hL hVF hPl hCh
  rw [hEq] at hLay
  cases hLay
  obtain ⟨sh, hSh, _, _, hDisc⟩ :=
    evalDeinitPlace_enum_field_preserves_discriminant dspec wf hApart hRoot h
  obtain ⟨st', hSt', hBytes, hOut⟩ := evalDeinitPlace_nested_bytes_simulation enc _ img
    (place := ⟨loc, .downcast nm present :: .field f ty :: rest⟩) hRoot h (Or.inl rfl) hLWF hFits
    hS hRange
  have hSt'' : slots'[loc]? = some st' := hSt'
  rw [hSh] at hSt''
  cases hSt''
  exact ⟨rfl, hLWF, hRTW, sh, hSh, hBytes, hDisc, hOut⟩

/-- **Union overlapping byte representation (`UnionFieldBytes`)**: in a union (`spec.shape = .union fs`),
every field `f` sits at byte offset `0` (`resolveAdtOffsetOf_union_eq_zero`), so field `f`'s
slot is represented by `[0, fl.size)`. -/
def UnionFieldBytes (enc : Value → List UInt8) (img : ByteImage) (fl : FieldLayout)
    (slot : FieldSlot) : Prop :=
  FieldBytes enc img 0 fl.size slot

/-- **Overlapping union fields at the byte level (`union_field_uninit_bytes`)**: for a well-formed
union (`spec.shape = .union fs`) with layout `(size, align)` and field `fs[f]? = some fl`, field
`f` sits at offset `0` (`fl.size ≤ size`), and an `Uninit` write over its bytes `[0, fl.size)`
(`deinitBytes img 0 fl.size`):
1. represents field `f` as `.uninit` (`UnionFieldBytes enc (deinitBytes img 0 fl.size) fl .uninit`),
2. destroys every overlapping initialized non-zero-sized sibling `g` at offset `0`
   (`¬ UnionFieldBytes enc (deinitBytes img 0 fl.size) fg (.init w)` when `0 < fl.size ∧ 0 < fg.size`),
3. preserves the trailing bytes `[fl.size, img.length)`.
This is a fact about bytes only (no `Deinit` evaluation is involved): it is why a union has no
per-field shell, and why `deinit_in_slot` rejects a projected `Deinit` into an initialized union
instead (`evalDeinitPlaceTyped_through_init_union_none`). -/
theorem union_field_uninit_bytes {spec : AdtLayoutSpec} (hWF : spec.WF)
    {fs : List FieldLayout} (hShape : spec.shape = .union fs)
    {f : Nat} {fl : FieldLayout} (hfl : fs[f]? = some fl)
    {size align : Nat} (hLay : adtLayout? spec = some (size, align))
    (enc : Value → List UInt8) (img : ByteImage) (hFits : size ≤ img.length) :
    resolveAdtOffsetOf spec 0 f = some 0 ∧
    fl.size ≤ size ∧
    UnionFieldBytes enc (deinitBytes img 0 fl.size) fl .uninit ∧
    (∀ (fg : FieldLayout) (w : Value), 0 < fl.size → 0 < fg.size →
      ¬ UnionFieldBytes enc (deinitBytes img 0 fl.size) fg (.init w)) ∧
    (∀ i, fl.size ≤ i → (deinitBytes img 0 fl.size)[i]? = img[i]?) := by
  have hLt : f < fs.length := (List.getElem?_eq_some_iff.mp hfl).1
  have hOff : resolveAdtOffsetOf spec 0 f = some 0 := by
    simp [resolveAdtOffsetOf, hLay, hShape, hLt]
  obtain ⟨fs', fl', size', align', hVF, hFl', hL', hBound, _⟩ :=
    resolveAdtOffsetOf_bounds_and_align spec hWF hOff
  have hVF0 : variantFields spec 0 = some fs := by simp [variantFields, hShape]
  rw [hVF0] at hVF; cases hVF
  rw [hfl] at hFl'; cases hFl'
  rw [hLay] at hL'; simp only [Option.some.injEq, Prod.mk.injEq] at hL'; obtain ⟨rfl, rfl⟩ := hL'
  refine ⟨hOff, by omega, ?_, ?_, fun i hi => deinitBytes_getElem?_outside (by omega)⟩
  · intro k hk
    simpa using deinitBytes_getElem?_inside (off := 0) (len := fl.size) (i := k)
      ⟨Nat.zero_le k, by omega⟩ (by omega)
  · intro fg w hFlPos hFgPos hInit
    have h0 := hInit.2 0 hFgPos
    have hUninit := deinitBytes_getElem?_inside (img := img) (off := 0) (len := fl.size) (i := 0)
      ⟨Nat.le_refl 0, by omega⟩ (by omega)
    simp only [Nat.zero_add] at h0
    rw [hUninit] at h0
    cases hE : (enc w)[0]? <;> rw [hE] at h0 <;> nomatch h0

/-! ### Section 2f: `Retag` -/

/-- What `check_retagged_reference` needs to know about a reference's pointee type: its
alignment (`none` when the layout model leaves it unspecified: `UnsupportedLayout`), whether its
size is exactly `0`, and whether it is inhabited. -/
structure RetagPointee : Type where
  align : Option Nat
  zeroSized : Bool
  inhabited : Bool

/-- The reference structure of a retagged place's type (the part `Ty::contains_ref`,
`Ty::is_inhabited_for`, and `retag_value` inspect): inhabited types without references reachable
by value (scalars, raw pointers, unions, ...), the uninhabited `!`, references `&T`/`&mut T`,
by-value tuples/structs, and enums (each variant described by a `.tuple` of its fields) that
store a tag (`requires_tag_write`) which may or may not survive field deinitialization
(`tag_survives_field_deinit`). -/
inductive RetagTy : Type where
  | noRef : RetagTy
  | never : RetagTy
  | ref (pointee : RetagPointee) : RetagTy
  | tuple (fields : List RetagTy) : RetagTy
  | enum (variants : List RetagTy) (requiresTag tagSurvives : Bool) : RetagTy

mutual
  /-- `Ty::contains_ref`. -/
  def RetagTy.containsRef : RetagTy → Bool
    | .noRef => false
    | .never => false
    | .ref _ => true
    | .tuple fs => RetagTy.listContainsRef fs
    | .enum vs _ _ => RetagTy.listContainsRef vs

  /-- Some type of the list contains a reference. -/
  def RetagTy.listContainsRef : List RetagTy → Bool
    | [] => false
    | t :: ts => t.containsRef || RetagTy.listContainsRef ts
end

mutual
  /-- `Ty::is_inhabited_for`: `!` is uninhabited, references and reference-free scalars are
  inhabited, a tuple/struct (or an enum variant) is inhabited iff all its fields are, and an enum
  iff some variant is. -/
  def RetagTy.inhabited : RetagTy → Bool
    | .noRef => true
    | .never => false
    | .ref _ => true
    | .tuple fs => RetagTy.allInhabited fs
    | .enum vs _ _ => RetagTy.anyInhabited vs

  /-- Every type of the list is inhabited. -/
  def RetagTy.allInhabited : List RetagTy → Bool
    | [] => true
    | t :: ts => t.inhabited && RetagTy.allInhabited ts

  /-- Some type of the list is inhabited. -/
  def RetagTy.anyInhabited : List RetagTy → Bool
    | [] => false
    | t :: ts => t.inhabited || RetagTy.anyInhabited ts
end

/-- The context of a `Retag` (`RetagCtx`): the target pointer width, Anneal's synthetic address
of a pointer and the local whose synthetic allocation it points into (`resolve_synthetic_local`),
the storage state of every local, and the value well-formedness check (`check_value_well_formed`,
used by `retag_value` on niche-capable enums, `B4`). -/
structure RetagCtx : Type where
  ptrBits : Nat
  addrOf : ProvenancePtr → Nat
  localOf : ProvenancePtr → Option Nat
  slots : List LocalSlotState
  wf : Value → Bool := fun _ => true

/-- The alignment check of `check_retagged_reference` (an unspecified alignment is
`UnsupportedLayout`). -/
def retagAlignOk (pt : RetagPointee) (addr : Nat) : Bool :=
  match pt.align with
  | some al => addr % al == 0
  | none => false

/-- The dangling check of `check_retagged_reference` (`A3`): a reference into the synthetic
allocation of a storage-dead local dangles unless its pointee is zero-sized. -/
def retagTargetLive (ctx : RetagCtx) (pt : RetagPointee) (p : ProvenancePtr) : Bool :=
  match ctx.localOf p with
  | some l =>
    match ctx.slots[l]? with
    | some .dead => pt.zeroSized
    | _ => true
  | none => true

/-- `check_retagged_reference`: the address is a valid `&T` bit pattern (non-null and within the
pointer width), aligned to the pointee's (specified) alignment, the pointee is inhabited, and the
reference does not dangle into a dead local (`retagTargetLive`). -/
def retagRefOk (ctx : RetagCtx) (pt : RetagPointee) (p : ProvenancePtr) : Bool :=
  (ctx.addrOf p != 0) && decide (ctx.addrOf p < 2 ^ ctx.ptrBits) &&
    retagAlignOk pt (ctx.addrOf p) && pt.inhabited && retagTargetLive ctx pt p

mutual
  /-- `retag_value`: validates every reference reachable by value in an initialized value,
  including niche-capable enum well-formedness (`B4`, `!tag_survives_field_deinit` requires
  `check_value_well_formed`) and variant inhabitedness (`B2`, `UninhabitedEnumVariant`, checked
  in `retagVariantOk`). -/
  def retagValueOk (ctx : RetagCtx) : RetagTy → Value → Bool
    | .noRef, _ => true
    | .never, _ => true
    | .ref pt, .ptr p _ => retagRefOk ctx pt p
    | .ref _, _ => false
    | .tuple fs, .aggregate _ vals => !RetagTy.listContainsRef fs || retagValuesOk ctx fs vals
    | .tuple fs, _ => !RetagTy.listContainsRef fs
    | .enum vs _ ts, .aggregate v vals =>
      !RetagTy.listContainsRef vs ||
        ((ts || ctx.wf (.aggregate v vals)) && retagVariantOk ctx vs v vals)
    | .enum vs _ _, _ => !RetagTy.listContainsRef vs

  /-- `retag_value` over the fields of a tuple/struct/variant (lengths must match). -/
  def retagValuesOk (ctx : RetagCtx) : List RetagTy → List Value → Bool
    | [], [] => true
    | t :: ts, v :: vs => retagValueOk ctx t v && retagValuesOk ctx ts vs
    | _, _ => false

  /-- `retag_value` on the fields of variant `v` of an enum: the variant must exist (a type
  mismatch otherwise) and all its fields must be inhabited (`UninhabitedEnumVariant`, `B2`). -/
  def retagVariantOk (ctx : RetagCtx) : List RetagTy → Nat → List Value → Bool
    | [], _, _ => false
    | .tuple fs :: _, 0, vals => RetagTy.allInhabited fs && retagValuesOk ctx fs vals
    | _ :: _, 0, _ => false
    | _ :: vs, v + 1, vals => retagVariantOk ctx vs v vals
end

mutual
  /-- `retag_shell` / `retag_value` on a field slot: an uninitialized part holding references is
  `UninitializedLocal`; an enum shell needs a readable tag (`tag_is_readable`, `A3`). -/
  def retagSlotOk (ctx : RetagCtx) : RetagTy → FieldSlot → Bool
    | t, .uninit => !t.containsRef
    | t, .init v => retagValueOk ctx t v
    | .tuple fs, .nested _ _ _ cfs => !RetagTy.listContainsRef fs || retagSlotsOk ctx fs cfs
    | .enum vs rt ts, .nested var _ disc cfs =>
      !RetagTy.listContainsRef vs || ((!rt || (disc && ts)) && retagVariantSlotsOk ctx vs var cfs)
    | _, .nested _ _ _ _ => false

  /-- `retag_shell` over the field slots of a shell. -/
  def retagSlotsOk (ctx : RetagCtx) : List RetagTy → List FieldSlot → Bool
    | [], [] => true
    | t :: ts, c :: cs => retagSlotOk ctx t c && retagSlotsOk ctx ts cs
    | _, _ => false

  /-- `retag_shell` on the field slots of the variant `v` of an enum shell (whose fields must all
  be inhabited, `B2`). -/
  def retagVariantSlotsOk (ctx : RetagCtx) : List RetagTy → Nat → List FieldSlot → Bool
    | [], _, _ => false
    | .tuple fs :: _, 0, cs => RetagTy.allInhabited fs && retagSlotsOk ctx fs cs
    | _ :: _, 0, _ => false
    | _ :: vs, v + 1, cs => retagVariantSlotsOk ctx vs v cs
end

/-- `project_mir_value` / `project_from_partial_shell` into a field slot: the part of `slot` at
`q` (`none` when the path is unreadable). -/
def projectFieldSlot (locals : List LocalSlot) : FieldSlot → List ProjectionElem → Option FieldSlot
  | slot, [] => some slot
  | .init v, q =>
    match evalValueProjRead locals v q with
    | .ok w => some (.init w)
    | _ => none
  | .nested var adt disc fs, .field idx _ :: rest =>
    if shellVariant ⟨var, adt, disc, fs⟩ = 0 then
      match fs[idx]? with
      | some c => projectFieldSlot locals c rest
      | none => none
    else none
  | .nested var adt disc fs, .downcast _ v :: .field idx _ :: rest =>
    if shellVariant ⟨var, adt, disc, fs⟩ = v then
      match fs[idx]? with
      | some c => projectFieldSlot locals c rest
      | none => none
    else none
  | _, _ => none

/-- The runtime value/shell projection check `check_slot_projection` (`check_value_projection` /
`check_shell_projection` in `crates/anneal-mir/src/lower/rvalue.rs:6531-6856`), which
`prepare_place_access` runs after `validate_projection_tail`:
- an uninitialized slot (`.uninit`) has no active variant or runtime array length to conflict with
  the projection (`LocalSlotState::Uninit => Ok(())`, `FieldSlot::Uninit => Ok(())`);
- an initialized value (`.init v`) must accept `evalValueProjRead` along `p` (enforcing active
  `Downcast` variants, field bounds, and dynamic `Index`/`ConstantIndex`/`Subslice` bounds on
  initialized arrays);
- a partial shell (`.nested var adt disc fs`) enforces active `Downcast`/field variants and field
  bounds, recursing into the child slot while rejecting array projections directly on a shell. -/
def checkSlotProjectionOk (locals : List LocalSlot) :
    FieldSlot → List ProjectionElem → Bool
  | .uninit, _ => true
  | .init v, p =>
    match evalValueProjRead locals v p with
    | .ok _ => true
    | _ => false
  | .nested _ _ _ _, [] => true
  | .nested var adt disc fs, .field idx _ :: rest =>
    (shellVariant ⟨var, adt, disc, fs⟩ == 0) &&
      match fs[idx]? with
      | some c => checkSlotProjectionOk locals c rest
      | none => false
  | .nested var adt disc fs, .downcast _ v :: .field idx _ :: rest =>
    (shellVariant ⟨var, adt, disc, fs⟩ == v) &&
      match fs[idx]? with
      | some c => checkSlotProjectionOk locals c rest
      | none => false
  | .nested _ _ _ _, _ :: _ => false

/-- Whole-place `check_slot_projection` (`checkPlaceSlotOk`): the root local is live and its root
slot satisfies `checkSlotProjectionOk` along `place.projection`. -/
def checkPlaceSlotOk (slots : List LocalSlotState) (place : Place) : Bool :=
  match slots[place.local_]? with
  | none | some .dead => false
  | some st =>
    checkSlotProjectionOk (slotsToTrustedLocals slots) (slotStateToFieldSlot st) place.projection

/-- The index pre-read of `prepare_place_access` (`read_index_local`): every `Index` operand local
of a projection holds an initialized scalar (`DeadLocal` / `UninitializedLocal` otherwise). -/
def indexLocalsOk (slots : List LocalSlotState) (proj : List ProjectionElem) : Bool :=
  proj.all fun e =>
    match e with
    | .index i =>
      match slots[i]? with
      | some (.init (.scalar _)) => true
      | _ => false
    | _ => true

/-- `StatementEvalState::retag_place`: first the value-dependent part of `prepare_place_access` —
a dead local faults (`DeadLocal`), a `Deref` is unsupported, every `Index` operand local must be
readable (the index pre-read, `indexLocalsOk`), and the runtime projection check
`check_slot_projection` (`checkSlotProjectionOk`: active variants, field and array bounds) must
pass; then `Retag(Raw)` requires a raw-pointer place holding an initialized pointer whose address
fits the pointer width (it may be null, unaligned, or dangling), and every other kind requires
nothing more of a place without references and otherwise validates every reference reachable in
the place's part. -/
def evalRetagPlace (ctx : RetagCtx) (kind : RetagKind) (place : Place) (ty : RetagTy)
    (rawPtrPlace : Bool) : Bool :=
  match ctx.slots[place.local_]? with
  | none => false
  | some .dead => false
  | some st =>
    !projectionHasDeref place.projection &&
    (indexLocalsOk ctx.slots place.projection &&
    (checkSlotProjectionOk (slotsToTrustedLocals ctx.slots) (slotStateToFieldSlot st)
      place.projection &&
      (match kind with
       | .raw =>
         rawPtrPlace &&
           (match readPlaceState ctx.slots place with
            | .ok (.ptr p _) => decide (ctx.addrOf p < 2 ^ ctx.ptrBits)
            | _ => false)
       | _ =>
         !ty.containsRef ||
           (match projectFieldSlot (slotsToTrustedLocals ctx.slots) (slotStateToFieldSlot st)
               place.projection with
            | some target => retagSlotOk ctx ty target
            | none => false))))

/-- `retagAlignOk` spelled out. -/
theorem retagAlignOk_iff (pt : RetagPointee) (addr : Nat) :
    retagAlignOk pt addr = true ↔ ∃ al, pt.align = some al ∧ addr % al = 0 := by
  unfold retagAlignOk
  cases pt.align <;> simp

/-- `retagTargetLive` spelled out. -/
theorem retagTargetLive_iff (ctx : RetagCtx) (pt : RetagPointee) (p : ProvenancePtr) :
    retagTargetLive ctx pt p = true ↔
      ∀ l, ctx.localOf p = some l → ctx.slots[l]? = some .dead → pt.zeroSized = true := by
  unfold retagTargetLive
  cases hl : ctx.localOf p with
  | none => simp
  | some l =>
    cases hs : ctx.slots[l]? with
    | none => simp [hs]
    | some st => cases st <;> simp [hs]

/-- `retagRefOk` spelled out: non-null, within the pointer width, aligned, inhabited pointee,
and not dangling into a dead local unless zero-sized. -/
theorem retagRefOk_iff (ctx : RetagCtx) (pt : RetagPointee) (p : ProvenancePtr) :
    retagRefOk ctx pt p = true ↔
      ctx.addrOf p ≠ 0 ∧ ctx.addrOf p < 2 ^ ctx.ptrBits ∧
      (∃ al, pt.align = some al ∧ ctx.addrOf p % al = 0) ∧ pt.inhabited = true ∧
      (∀ l, ctx.localOf p = some l → ctx.slots[l]? = some .dead → pt.zeroSized = true) := by
  simp only [retagRefOk, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    retagAlignOk_iff, retagTargetLive_iff, and_assoc]

/-- A retag of a dead (or missing) local fails (`DeadLocal`), for every kind. -/
theorem evalRetagPlace_dead (ctx : RetagCtx) (kind : RetagKind) (place : Place) (ty : RetagTy)
    (b : Bool) (h : ctx.slots[place.local_]? = some .dead) :
    evalRetagPlace ctx kind place ty b = false := by
  simp [evalRetagPlace, h]

/-- **`Retag` through an unreadable `Index` operand local fails** (`prepare_place_access`'s index
pre-read: `DeadLocal` / `UninitializedLocal`), for every kind and every place type — even a
reference-free one, which otherwise needs only a live local. -/
theorem evalRetagPlace_bad_index_false (ctx : RetagCtx) (kind : RetagKind) {place : Place}
    (ty : RetagTy) (b : Bool) {i : Local} (hIdx : .index i ∈ place.projection)
    (hBad : ∀ sc, ctx.slots[i]? ≠ some (.init (.scalar sc))) :
    evalRetagPlace ctx kind place ty b = false := by
  have hI : indexLocalsOk ctx.slots place.projection = false := by
    cases hc : indexLocalsOk ctx.slots place.projection with
    | false => rfl
    | true =>
      unfold indexLocalsOk at hc
      rw [List.all_eq_true] at hc
      have hE := hc _ hIdx
      cases hS : ctx.slots[i]? with
      | none => simp [hS] at hE
      | some st =>
        cases st with
        | init v =>
          cases v with
          | scalar sc => exact absurd hS (hBad sc)
          | _ => simp [hS] at hE
        | _ => simp [hS] at hE
  unfold evalRetagPlace
  split
  · rfl
  · rfl
  · simp [hI]

/-- A reference-free place is retagged (by any non-raw kind) exactly when it passes the
value-dependent part of `prepare_place_access`: a live local, no `Deref`, readable `Index`
operand locals, and `check_slot_projection`. -/
theorem evalRetagPlace_noRef {ctx : RetagCtx} {kind : RetagKind} {place : Place} {ty : RetagTy}
    {b : Bool} (hKind : kind ≠ .raw) (hNoRef : ty.containsRef = false) :
    evalRetagPlace ctx kind place ty b = true ↔
      (∃ st, ctx.slots[place.local_]? = some st ∧ st ≠ .dead) ∧
        projectionHasDeref place.projection = false ∧
        indexLocalsOk ctx.slots place.projection = true ∧
        checkPlaceSlotOk ctx.slots place = true := by
  unfold evalRetagPlace checkPlaceSlotOk
  cases hS : ctx.slots[place.local_]? with
  | none => simp
  | some st =>
    cases st with
    | dead => simp
    | _ => cases kind <;> first | exact absurd rfl hKind | simp [hNoRef]

/-- **A successful read passes `check_slot_projection`**: whatever `readFieldSlot` reads along a
path, `checkSlotProjectionOk` accepts that path. -/
theorem readFieldSlot_ok_checkSlotProjectionOk_aux (locals : List LocalSlot) :
    ∀ (n : Nat) (p : List ProjectionElem), p.length ≤ n → ∀ (slot : FieldSlot) (w : Value),
      readFieldSlot locals slot p = .ok w → checkSlotProjectionOk locals slot p = true := by
  intro n
  induction n with
  | zero =>
    intro p hLen slot w _
    have hp : p = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hLen)
    subst hp
    cases slot with
    | uninit => rfl
    | init v => simp [checkSlotProjectionOk, evalValueProjRead]
    | nested var adt disc fs => rfl
  | succ n ih =>
    intro p hLen slot w h
    cases slot with
    | uninit => simp [readFieldSlot] at h
    | init v =>
      simp only [readFieldSlot] at h
      simp [checkSlotProjectionOk, h]
    | nested var adt disc fs =>
      rcases p with _ | ⟨a, rest⟩
      · rfl
      · simp only [List.length_cons] at hLen
        cases a
        case field idx ty =>
          rw [readFieldSlot_nested_field] at h
          unfold shellFieldRead at h
          by_cases hV : shellVariant ⟨var, adt, disc, fs⟩ = 0
          · simp only [hV, ↓reduceIte] at h
            cases hc : fs[idx]? with
            | none => simp [hc] at h
            | some c =>
              simp only [hc] at h
              simp only [checkSlotProjectionOk, hV, BEq.rfl, Bool.true_and, hc]
              exact ih rest (by omega) c w h
          · simp [hV] at h
        case downcast nm v =>
          rcases rest with _ | ⟨b, rest'⟩
          · simp [readFieldSlot, readFromPartialShell, isFieldHead] at h
          · simp only [List.length_cons] at hLen
            cases b
            case field idx ty =>
              rw [readFieldSlot_nested_downcast_field] at h
              unfold shellFieldRead at h
              by_cases hV : shellVariant ⟨var, adt, disc, fs⟩ = v
              · simp only [hV, ↓reduceIte] at h
                cases hc : fs[idx]? with
                | none => simp [hc] at h
                | some c =>
                  simp only [hc] at h
                  simp only [checkSlotProjectionOk, hV, BEq.rfl, Bool.true_and, hc]
                  exact ih rest' (by omega) c w h
              · simp [hV] at h
            all_goals simp [readFieldSlot, readFromPartialShell, isFieldHead] at h
        all_goals simp [readFieldSlot, readFromPartialShell] at h

/-- Every place Anneal reads passes `check_slot_projection` (`checkPlaceSlotOk`). -/
theorem checkPlaceSlotOk_of_readPlaceState {slots : List LocalSlotState} {place : Place}
    {w : Value} (h : readPlaceState slots place = .ok w) : checkPlaceSlotOk slots place = true := by
  have hND : projectionHasDeref place.projection = false := by
    cases hD : projectionHasDeref place.projection with
    | false => rfl
    | true => simp only [readPlaceState, hD] at h; nomatch h
  cases hS : slots[place.local_]? with
  | none => simp [readPlaceState, hND, get?_eq_getElem?, hS] at h
  | some st =>
    have hLive : st ≠ .dead := by
      intro hD
      subst hD
      simp [readPlaceState, hND, get?_eq_getElem?, hS] at h
    have hR := (readPlaceState_eq_readFieldSlot hS hLive place.projection hND).symm.trans h
    unfold checkPlaceSlotOk
    rw [hS]
    cases st with
    | dead => exact absurd rfl hLive
    | uninit => exact readFieldSlot_ok_checkSlotProjectionOk_aux _ _ _ (Nat.le_refl _) _ _ hR
    | init _ => exact readFieldSlot_ok_checkSlotProjectionOk_aux _ _ _ (Nat.le_refl _) _ _ hR
    | partialShell _ =>
      exact readFieldSlot_ok_checkSlotProjectionOk_aux _ _ _ (Nat.le_refl _) _ _ hR

/-- **`Retag` through an inactive enum variant fails (`InactiveVariantProjection`)**, for every
kind and every place type (`prepare_place_access` runs `check_slot_projection` first). -/
theorem evalRetagPlace_inactive_variant_false (ctx : RetagCtx) (kind : RetagKind) (ty : RetagTy)
    (b : Bool) {loc : Local} {v dv idx : Nat} (nm : Option String) (fty : Ty)
    (rest : List ProjectionElem) (hNe : v ≠ dv) {vals : List Value}
    (hRoot : ctx.slots[loc]? = some (.init (.aggregate v vals))) :
    evalRetagPlace ctx kind ⟨loc, .downcast nm dv :: .field idx fty :: rest⟩ ty b = false := by
  simp [evalRetagPlace, hRoot, slotStateToFieldSlot, checkSlotProjectionOk,
    evalValueProjRead_aggregate_downcast_field, hNe]

/-- **`Retag` of a place with a `Deref` is unsupported (`UnsupportedPlaceProjection`)**. -/
theorem evalRetagPlace_deref_false (ctx : RetagCtx) (kind : RetagKind) {place : Place}
    (ty : RetagTy) (b : Bool) (hD : projectionHasDeref place.projection = true) :
    evalRetagPlace ctx kind place ty b = false := by
  unfold evalRetagPlace
  split
  · rfl
  · rfl
  · simp [hD]

/-- **`Retag(Raw)` soundness**: a successful raw retag read an initialized pointer of the place
whose address fits the pointer width. -/
theorem evalRetagPlace_raw_sound {ctx : RetagCtx} {place : Place} {ty : RetagTy} {b : Bool}
    (h : evalRetagPlace ctx .raw place ty b = true) :
    b = true ∧ ∃ p sz, readPlaceState ctx.slots place = .ok (.ptr p sz) ∧
      ctx.addrOf p < 2 ^ ctx.ptrBits := by
  unfold evalRetagPlace at h
  split at h
  · nomatch h
  · nomatch h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨_, _, _, hb, hR⟩ := h
    refine ⟨hb, ?_⟩
    split at hR
    · rename_i p sz hRead
      exact ⟨p, sz, hRead, by simpa using hR⟩
    · nomatch hR

/-- Retagging a reference-holding place whose local is uninitialized fails
(`UninitializedLocal`), for every non-raw kind. -/
theorem evalRetagPlace_uninit_ref {ctx : RetagCtx} {kind : RetagKind} {place : Place}
    {ty : RetagTy} {b : Bool} (hKind : kind ≠ .raw) (hRef : ty.containsRef = true)
    (h : ctx.slots[place.local_]? = some .uninit) :
    evalRetagPlace ctx kind place ty b = false := by
  unfold evalRetagPlace
  rw [h]
  cases kind with
  | raw => exact absurd rfl hKind
  | _ =>
    simp only [hRef, Bool.not_true, Bool.false_or, slotStateToFieldSlot]
    cases hp : place.projection with
    | nil => simp [projectFieldSlot, retagSlotOk, hRef]
    | cons a rest => simp [projectFieldSlot]

/-- **Reference retag soundness**: a successful non-raw retag of a place of reference type
validated an initialized pointer that is non-null, within the pointer width, aligned to its
pointee, points to an inhabited type, and does not dangle into a dead local (`A3`). -/
theorem evalRetagPlace_ref_sound {ctx : RetagCtx} {kind : RetagKind} {place : Place}
    {pt : RetagPointee} {b : Bool} (hKind : kind ≠ .raw)
    (h : evalRetagPlace ctx kind place (.ref pt) b = true) :
    ∃ st p sz, ctx.slots[place.local_]? = some st ∧ st ≠ .dead ∧
      projectFieldSlot (slotsToTrustedLocals ctx.slots) (slotStateToFieldSlot st)
        place.projection = some (.init (.ptr p sz)) ∧
      ctx.addrOf p ≠ 0 ∧ ctx.addrOf p < 2 ^ ctx.ptrBits ∧
      (∃ al, pt.align = some al ∧ ctx.addrOf p % al = 0) ∧ pt.inhabited = true ∧
      (∀ l, ctx.localOf p = some l → ctx.slots[l]? = some .dead → pt.zeroSized = true) := by
  unfold evalRetagPlace at h
  split at h
  · nomatch h
  · nomatch h
  · rename_i st hNotDead hSt
    cases kind with
    | raw => exact absurd rfl hKind
    | _ =>
      simp only [RetagTy.containsRef, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
      obtain ⟨_, _, _, h⟩ := h
      split at h
      · rename_i target hT
        cases target with
        | uninit => simp [retagSlotOk, RetagTy.containsRef] at h
        | nested _ _ _ _ => simp [retagSlotOk] at h
        | init v =>
          cases v with
          | ptr p sz =>
            simp only [retagSlotOk, retagValueOk] at h
            exact ⟨st, p, sz, hSt, fun hD => hNotDead hD, hT, (retagRefOk_iff ctx pt p).mp h⟩
          | _ => simp [retagSlotOk, retagValueOk] at h
      · nomatch h

/-- The operand Trusted's `evalStmt` evaluates for `.retag` (`evalOperand (.copy place)`) agrees
with Anneal's read of the place on below-related frames for every `localDecls` on non-union places
(`placeTouchesUnion localDecls layouts place = false`): every value Anneal reads (and checks) is
the value Trusted retags. -/
theorem readPlaceState_below_evalOperand_copy {slots : List LocalSlotState}
    {locals : List LocalSlot} {place : Place} {val : Value}
    (hRel : SlotsRefine SlotBelow slots locals) (hRead : readPlaceState slots place = .ok val)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl := [])
    (hNoUnion : placeTouchesUnion localDecls layouts place = false := by
      simp [placeTouchesUnion_nil_decls, placeTouchesUnion_nil_proj]) :
    evalOperand locals (.copy place) borrows globals layouts callerLocals localDecls =
      .ok val locals := by
  have hNoDeref : projectionHasDeref place.projection = false := by
    cases hD : projectionHasDeref place.projection with
    | false => rfl
    | true => simp only [readPlaceState, hD] at hRead; nomatch hRead
  obtain ⟨rootVal, hRoot, hProj⟩ := readPlaceState_below_refines hRel hRead
  rcases place with ⟨loc, _ | ⟨hd, tl⟩⟩
  · unfold readProjectedValue at hProj
    injection hProj with hEq
    subst hEq
    unfold evalOperand
    dsimp only
    rw [hRoot]
    rfl
  · have hNotDeref : hd ≠ .deref := by
      intro hEq
      subst hEq
      simp [projectionHasDeref] at hNoDeref
    exact evalOperand_copy_proj_of_noUnion locals loc hd tl borrows globals layouts
      callerLocals localDecls rootVal val hNotDeref hNoUnion hRoot hProj

/-- Trusted's `evalStmt` on `.retag` faults when the retagged place's local is uninitialized or
dead (its `evalOperand (.copy place)` read faults), for every `localDecls` / `layouts`, exactly
where Anneal's retag of a reference-holding place fails too. -/
theorem evalStmt_retag_uninit_or_dead_ub (s : MachineState) (kind : RetagKind) (place : Place)
    (span : String) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hNoDeref : projectionHasDeref place.projection = false)
    (hT : s.frame.locals[place.local_]? = some .uninit ∨
      s.frame.locals[place.local_]? = some .dead) :
    evalStmt s ⟨.retag kind place, span⟩ localDecls layouts = .fail .ub := by
  have hOp : evalOperand s.frame.locals (.copy place) s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls = .ub := by
    rcases place with ⟨loc, _ | ⟨hd, tl⟩⟩
    · rcases hT with hT | hT <;> simp [evalOperand, get?_eq_getElem?, hT]
    · cases hd with
      | deref => simp [projectionHasDeref] at hNoDeref
      | _ => rcases hT with hT | hT <;> simp [evalOperand, get?_eq_getElem?, hT]
  simp only [evalStmt, hOp]

/-- A successful projected value read has no `Deref` (`evalValueProjRead` reports `Deref` as
unsupported). -/
theorem evalValueProjRead_ok_noDeref (locals : List LocalSlot) :
    ∀ (p : List ProjectionElem) (v w : Value), evalValueProjRead locals v p = .ok w →
      projectionHasDeref p = false
  | [], _, _, _ => rfl
  | .deref :: _, v, _, h => by cases v <;> simp [evalValueProjRead] at h
  | .field _ _ :: rest, v, w, h => by
    cases v with
    | aggregate var fields =>
      simp only [evalValueProjRead] at h
      split at h
      · exact evalValueProjRead_ok_noDeref locals rest _ w h
      · nomatch h
    | _ => simp [evalValueProjRead] at h
  | .downcast _ _ :: rest, v, w, h => by
    cases v with
    | aggregate var fields =>
      simp only [evalValueProjRead] at h
      split at h
      · exact evalValueProjRead_ok_noDeref locals rest _ w h
      · nomatch h
    | _ => simp [evalValueProjRead] at h
  | .index _ :: rest, v, w, h => by
    cases v with
    | aggregate var fields =>
      cases var with
      | zero =>
        simp only [evalValueProjRead] at h
        split at h
        · split at h
          · exact evalValueProjRead_ok_noDeref locals rest _ w h
          · nomatch h
        · nomatch h
      | succ _ => simp [evalValueProjRead] at h
    | _ => simp [evalValueProjRead] at h
  | .constantIndex _ _ _ :: rest, v, w, h => by
    cases v with
    | aggregate var fields =>
      cases var with
      | zero =>
        simp only [evalValueProjRead] at h
        split at h
        · split at h
          · exact evalValueProjRead_ok_noDeref locals rest _ w h
          · nomatch h
        · nomatch h
      | succ _ => simp [evalValueProjRead] at h
    | _ => simp [evalValueProjRead] at h
  | .subslice _ _ _ :: rest, v, w, h => by
    cases v with
    | aggregate var fields =>
      cases var with
      | zero =>
        simp only [evalValueProjRead] at h
        split at h
        · exact evalValueProjRead_ok_noDeref locals rest _ w h
        · nomatch h
      | succ _ => simp [evalValueProjRead] at h
    | _ => simp [evalValueProjRead] at h
  | .opaqueCast _ :: _, v, _, h => by cases v <;> simp [evalValueProjRead] at h
  | .unwrapUnsafeBinder _ :: _, v, _, h => by cases v <;> simp [evalValueProjRead] at h

/-- **A part `projectFieldSlot` finds initialized is what `read_place` reads there**: its path has
no `Deref`, and `readFieldSlot` reads exactly that value. -/
theorem projectFieldSlot_init_spec_aux (locals : List LocalSlot) :
    ∀ (n : Nat) (p : List ProjectionElem), p.length ≤ n → ∀ (slot : FieldSlot) (w : Value),
      projectFieldSlot locals slot p = some (.init w) →
        projectionHasDeref p = false ∧ readFieldSlot locals slot p = .ok w := by
  intro n
  induction n with
  | zero =>
    intro p hLen slot w h
    have hp : p = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hLen)
    subst hp
    simp only [projectFieldSlot, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro p hLen slot w h
    rcases p with _ | ⟨a, rest⟩
    · simp only [projectFieldSlot, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
    · simp only [List.length_cons] at hLen
      cases slot with
      | uninit => simp [projectFieldSlot] at h
      | init v =>
        simp only [projectFieldSlot] at h
        split at h
        · rename_i w' hw'
          simp only [Option.some.injEq, FieldSlot.init.injEq] at h
          subst h
          exact ⟨evalValueProjRead_ok_noDeref locals _ v _ hw', hw'⟩
        · nomatch h
      | nested var adt disc fs =>
        cases a
        case field idx ty =>
          rw [readFieldSlot_nested_field]
          unfold shellFieldRead
          by_cases hV : shellVariant ⟨var, adt, disc, fs⟩ = 0
          · simp only [projectFieldSlot, hV, ↓reduceIte] at h
            simp only [hV, ↓reduceIte]
            cases hc : fs[idx]? with
            | none => simp [hc] at h
            | some c =>
              simp only [hc] at h ⊢
              exact ih rest (by omega) c w h
          · simp [projectFieldSlot, hV] at h
        case downcast nm v =>
          rcases rest with _ | ⟨b, rest'⟩
          · simp [projectFieldSlot] at h
          · simp only [List.length_cons] at hLen
            cases b
            case field idx ty =>
              rw [readFieldSlot_nested_downcast_field]
              unfold shellFieldRead
              by_cases hV : shellVariant ⟨var, adt, disc, fs⟩ = v
              · simp only [projectFieldSlot, hV, ↓reduceIte] at h
                simp only [hV, ↓reduceIte]
                cases hc : fs[idx]? with
                | none => simp [hc] at h
                | some c =>
                  simp only [hc] at h ⊢
                  exact ih rest' (by omega) c w h
              · simp [projectFieldSlot, hV] at h
            all_goals simp [projectFieldSlot] at h
        all_goals simp [projectFieldSlot] at h

/-- `read_place` reads the value `projectFieldSlot` finds initialized in a live local. -/
theorem readPlaceState_of_projectFieldSlot_init {slots : List LocalSlotState} {place : Place}
    {st : LocalSlotState} {w : Value} (hSt : slots[place.local_]? = some st) (hLive : st ≠ .dead)
    (h : projectFieldSlot (slotsToTrustedLocals slots) (slotStateToFieldSlot st)
      place.projection = some (.init w)) :
    readPlaceState slots place = .ok w := by
  obtain ⟨hND, hRead⟩ := projectFieldSlot_init_spec_aux _ _ _ (Nat.le_refl _) _ _ h
  exact (readPlaceState_eq_readFieldSlot hSt hLive place.projection hND).trans hRead

private theorem evalStmt_retag_borrow_ok {s : MachineState} {kind : RetagKind} {place : Place}
    {span : String} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {p : ProvenancePtr} {sz : Nat} {entry : BorrowEntry}
    (hOp : evalOperand s.frame.locals (.copy place) s.memory.borrows s.memory.globals
      layouts s.memory.callerLocals localDecls = .ok (.ptr p sz) s.frame.locals)
    (hLook : lookupBorrow s.memory.borrows p.tag = some entry)
    (hPerm : entry.perm = .active ∨ entry.perm = .reserved ∨
      (entry.perm = .frozen ∧
        ∀ inner, (placeTy localDecls layouts place).map (·.kind) ≠ some (.ref .mut inner))) :
    evalStmt s ⟨.retag kind place, span⟩ localDecls layouts =
      match kind with
      | .fnEntry =>
        let protId := s.memory.nextProtector
        let borrows' := attachBorrowProtector s.memory.borrows p.tag protId
        .step (advanceStmt s s.frame.locals
          { s.memory with
            borrows := borrows'
            activeProtectors := protId :: s.memory.activeProtectors
            nextProtector := Nat.add protId 1 })
      | _ => .step (advanceStmt s s.frame.locals) := by
  rcases hPerm with hP | hP | ⟨hP, hNotMut⟩
  · cases kind <;> simp only [evalStmt, hOp, hLook, hP]
  · cases kind <;> simp only [evalStmt, hOp, hLook, hP]
  · cases hPTy : placeTy localDecls layouts place with
    | none => cases kind <;> simp only [evalStmt, hOp, hLook, hP, hPTy]
    | some pTy =>
      rcases pTy with ⟨k, lIdx⟩
      cases k with
      | ref m inner =>
        cases m with
        | not => cases kind <;> simp only [evalStmt, hOp, hLook, hP, hPTy]
        | «mut» =>
          exfalso
          apply hNotMut inner
          simp [hPTy]
      | bool | char | int _ | uint _ | float _ | never | str | tuple _ | array _ _
      | slice _ | rawPtr _ _ | adt _ _ | fnDef _ _ | fnPtr _ _ _ _ | closure _ _
      | dynamic _ | foreign _ | param _ _ | alias _ _ | other _ =>
        cases kind <;> simp only [evalStmt, hOp, hLook, hP, hPTy]

/-- **Reference `Retag` refines Trusted's `evalStmt` (`.retag`)**: on below-related frames, a
successful non-raw Anneal retag of a non-union reference-typed place read the pointer `p` stored
there (`readPlaceState`) and validated it (`retagRefOk`: non-null, within the pointer width,
aligned, inhabited pointee, not dangling into a dead local); Trusted's `.retag` reads that same
pointer (`evalOperand (.copy place)`), and whenever Trusted's borrow model grants the retag (`p`'s
tag is tracked with an `active`, `reserved`, or non-`&mut` `frozen` permission) Trusted's
`evalStmt` steps — it never faults — to the next statement with its locals unchanged
(`advanceStmt s s.frame.locals mem'`, where only `FnEntry` changes the memory, installing a
protector).
Anneal's model has no borrow tracking, so the aliasing permission is the only fact taken from
Trusted's side. -/
theorem evalStmt_retag_ref_refines {ctx : RetagCtx} {kind : RetagKind} {place : Place}
    {pt : RetagPointee} {b : Bool} (hKind : kind ≠ .raw)
    (h : evalRetagPlace ctx kind place (.ref pt) b = true) {s : MachineState}
    (hRel : SlotsRefine SlotBelow ctx.slots s.frame.locals) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hNoUnion : placeTouchesUnion localDecls layouts place = false := by
      simp [placeTouchesUnion_nil_proj]) :
    ∃ p sz, readPlaceState ctx.slots place = .ok (.ptr p sz) ∧ retagRefOk ctx pt p = true ∧
      ∀ entry, lookupBorrow s.memory.borrows p.tag = some entry →
        (entry.perm = .active ∨ entry.perm = .reserved ∨
          (entry.perm = .frozen ∧
            ∀ inner, (placeTy localDecls layouts place).map (·.kind) ≠ some (.ref .mut inner))) →
        ∃ mem', evalStmt s ⟨.retag kind place, span⟩ localDecls layouts =
          .step (advanceStmt s s.frame.locals mem') := by
  obtain ⟨st, p, sz, hSt, hLive, hProj, hChecks⟩ := evalRetagPlace_ref_sound hKind h
  have hRead := readPlaceState_of_projectFieldSlot_init hSt hLive hProj
  refine ⟨p, sz, hRead, (retagRefOk_iff ctx pt p).mpr hChecks, fun entry hLook hPerm => ?_⟩
  have hOp := readPlaceState_below_evalOperand_copy hRel hRead s.memory.borrows s.memory.globals
    layouts s.memory.callerLocals localDecls hNoUnion
  rw [evalStmt_retag_borrow_ok hOp hLook hPerm]
  cases kind <;> exact ⟨_, rfl⟩

/-- **Trusted rejects a disabled tag where Anneal has no aliasing model**: Trusted's `.retag`
faults on a pointer whose tag is `disabled`, a place Anneal's (borrow-free) retag may accept —
the refinement of `evalStmt_retag_ref_refines` is conditional on Trusted's permission. -/
theorem evalStmt_retag_disabled_ub {ctx : RetagCtx} {kind : RetagKind} {place : Place}
    {pt : RetagPointee} {b : Bool} (hKind : kind ≠ .raw)
    (h : evalRetagPlace ctx kind place (.ref pt) b = true) {s : MachineState}
    (hRel : SlotsRefine SlotBelow ctx.slots s.frame.locals) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable) {entry : BorrowEntry}
    (hDis : entry.perm = .disabled)
    (hNoUnion : placeTouchesUnion localDecls layouts place = false := by
      simp [placeTouchesUnion_nil_proj]) :
    ∃ p sz, readPlaceState ctx.slots place = .ok (.ptr p sz) ∧
      (lookupBorrow s.memory.borrows p.tag = some entry →
        evalStmt s ⟨.retag kind place, span⟩ localDecls layouts = .fail .ub) := by
  obtain ⟨st, p, sz, hSt, hLive, hProj, _⟩ := evalRetagPlace_ref_sound hKind h
  have hRead := readPlaceState_of_projectFieldSlot_init hSt hLive hProj
  refine ⟨p, sz, hRead, fun hLook => ?_⟩
  have hOp := readPlaceState_below_evalOperand_copy hRel hRead s.memory.borrows s.memory.globals
    layouts s.memory.callerLocals localDecls hNoUnion
  simp only [evalStmt, hOp, hLook, hDis]

/-- **Trusted rejects a `frozen` tag on a `&mut` place**: retagging a mutable-reference place
(`placeTy = some { kind := .ref .mut inner, .. }`) whose Tree Borrows tag has been frozen faults
with `.fail .ub` in Trusted's `evalStmt`. -/
theorem evalStmt_retag_ref_frozen_mut_ub {ctx : RetagCtx} {kind : RetagKind} {place : Place}
    {pt : RetagPointee} {b : Bool} (hKind : kind ≠ .raw)
    (h : evalRetagPlace ctx kind place (.ref pt) b = true) {s : MachineState}
    (hRel : SlotsRefine SlotBelow ctx.slots s.frame.locals) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable) {entry : BorrowEntry}
    {inner : RigidTy} {lIdx : Nat}
    (hFrz : entry.perm = .frozen)
    (hMutTy : placeTy localDecls layouts place = some { kind := .ref .mut inner, layoutIdx := lIdx })
    (hNoUnion : placeTouchesUnion localDecls layouts place = false := by
      simp [placeTouchesUnion_nil_proj]) :
    ∃ p sz, readPlaceState ctx.slots place = .ok (.ptr p sz) ∧
      (lookupBorrow s.memory.borrows p.tag = some entry →
        evalStmt s ⟨.retag kind place, span⟩ localDecls layouts = .fail .ub) := by
  obtain ⟨st, p, sz, hSt, hLive, hProj, _⟩ := evalRetagPlace_ref_sound hKind h
  have hRead := readPlaceState_of_projectFieldSlot_init hSt hLive hProj
  refine ⟨p, sz, hRead, fun hLook => ?_⟩
  have hOp := readPlaceState_below_evalOperand_copy hRel hRead s.memory.borrows s.memory.globals
    layouts s.memory.callerLocals localDecls hNoUnion
  unfold evalStmt
  simp only [hOp, hLook, hFrz, hMutTy]

/-- **`Retag(Raw)` refines Trusted's `evalStmt` (`.retag .raw`, `B4`)**: on below-related frames, a
successful raw retag (`evalRetagPlace ctx .raw place ty b = true`) on a non-union place read an
initialized pointer `.ptr p sz` at `place` with `b = true` and `ctx.addrOf p < 2 ^ ctx.ptrBits`;
Trusted's `.retag .raw` reads that same pointer (`evalOperand (.copy place)`), and whenever
Trusted's borrow model grants the tag (`lookupBorrow s.memory.borrows p.tag = some entry` with
`entry.perm = .active`, `.reserved`, or `.frozen` on any non-`&mut` place — including every
`*const T` / `*mut T` raw-pointer place created by `&raw const` / `&raw mut`), Trusted's
`evalStmt` steps without faulting to `advanceStmt s s.frame.locals`. -/
theorem evalStmt_retag_raw_refines {ctx : RetagCtx} {place : Place} {ty : RetagTy} {b : Bool}
    (h : evalRetagPlace ctx .raw place ty b = true) {s : MachineState}
    (hRel : SlotsRefine SlotBelow ctx.slots s.frame.locals) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hNoUnion : placeTouchesUnion localDecls layouts place = false := by
      simp [placeTouchesUnion_nil_proj]) :
    b = true ∧ ∃ p sz, readPlaceState ctx.slots place = .ok (.ptr p sz) ∧
      ctx.addrOf p < 2 ^ ctx.ptrBits ∧
      ∀ entry, lookupBorrow s.memory.borrows p.tag = some entry →
        (entry.perm = .active ∨ entry.perm = .reserved ∨
          (entry.perm = .frozen ∧
            ∀ inner, (placeTy localDecls layouts place).map (·.kind) ≠ some (.ref .mut inner))) →
        evalStmt s ⟨.retag .raw place, span⟩ localDecls layouts =
          .step (advanceStmt s s.frame.locals) := by
  obtain ⟨hb, p, sz, hRead, hAddr⟩ := evalRetagPlace_raw_sound h
  refine ⟨hb, p, sz, hRead, hAddr, fun entry hLook hPerm => ?_⟩
  have hOp := readPlaceState_below_evalOperand_copy hRel hRead s.memory.borrows s.memory.globals
    layouts s.memory.callerLocals localDecls hNoUnion
  exact evalStmt_retag_borrow_ok hOp hLook hPerm

/-- **`Retag(Raw)` on a global allocation refines Trusted's `evalStmt` (`B4`)**: when `p`'s tag is
not a stack borrow (`lookupBorrow = none`) and `p.allocId` resolves to a captured global allocation
`alloc` (`lookupGlobalAlloc = some alloc`) on a non-`&mut` place whose pointee fits within
`alloc.bytes`, Trusted's `.retag .raw` steps without faulting to `advanceStmt s s.frame.locals`. -/
theorem evalStmt_retag_raw_global_refines {ctx : RetagCtx} {place : Place} {ty : RetagTy}
    {b : Bool} (h : evalRetagPlace ctx .raw place ty b = true) {s : MachineState}
    (hRel : SlotsRefine SlotBelow ctx.slots s.frame.locals) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hNotMut : ∀ inner, (placeTy localDecls layouts place).map (·.kind) ≠ some (.ref .mut inner) := by
      simp [placeTy])
    (hNoUnion : placeTouchesUnion localDecls layouts place = false := by
      simp [placeTouchesUnion_nil_proj]) :
    ∃ p sz, readPlaceState ctx.slots place = .ok (.ptr p sz) ∧
      ∀ alloc, lookupBorrow s.memory.borrows p.tag = none →
        lookupGlobalAlloc s.memory.globals p.allocId = some alloc →
        p.offsetBytes +
          (match placeTy localDecls layouts place with
           | .some pTy =>
             match pointeeTyOf pTy with
             | .some innerTy => (rigidTyByteSize layouts innerTy).getD 0
             | .none => 0
           | .none => 0) ≤ alloc.bytes.length →
        evalStmt s ⟨.retag .raw place, span⟩ localDecls layouts =
          .step (advanceStmt s s.frame.locals) := by
  obtain ⟨_, p, sz, hRead, _⟩ := evalRetagPlace_raw_sound h
  refine ⟨p, sz, hRead, fun alloc hNoB hG hBounds => ?_⟩
  have hOp := readPlaceState_below_evalOperand_copy hRel hRead s.memory.borrows s.memory.globals
    layouts s.memory.callerLocals localDecls hNoUnion
  cases hPTy : placeTy localDecls layouts place with
  | none =>
    rw [hPTy] at hBounds
    have hBle : Nat.ble (Nat.add p.offsetBytes 0) (length alloc.bytes) = true :=
      Nat.ble_eq.mpr hBounds
    cases alloc.mutability <;> (simp only [evalStmt, hOp, hNoB, hG, hPTy, hBle]; rfl)
  | some pTy =>
    rw [hPTy] at hBounds
    have hPtBytes :
        (match pointeeTyOf pTy with
         | .some innerTy =>
           match rigidTyByteSize layouts innerTy with
           | .some n => n
           | .none => 0
         | .none => 0) =
        (match pointeeTyOf pTy with
         | .some innerTy => (rigidTyByteSize layouts innerTy).getD 0
         | .none => 0) := by
      cases hPt : pointeeTyOf pTy with
      | none => rfl
      | some innerTy =>
        dsimp only
        cases hSz : rigidTyByteSize layouts innerTy <;> rfl
    have hBle :
        Nat.ble
          (Nat.add p.offsetBytes
            (match pointeeTyOf pTy with
             | .some innerTy =>
               match rigidTyByteSize layouts innerTy with
               | .some n => n
               | .none => 0
             | .none => 0))
          (length alloc.bytes) = true := by
      rw [hPtBytes]
      exact Nat.ble_eq.mpr hBounds
    rcases pTy with ⟨k, lIdx⟩
    cases k with
    | ref m inner =>
      cases m with
      | not =>
        dsimp only [pointeeTyOf] at hBle
        cases hSz : rigidTyByteSize layouts { kind := inner, layoutIdx := 0 } <;>
          (simp only [hSz] at hBle;
           cases alloc.mutability <;> (simp only [evalStmt, hOp, hNoB, hG, hPTy, hSz, hBle]; rfl))
      | «mut» =>
        exfalso
        apply hNotMut inner
        simp [hPTy]
    | rawPtr m inner =>
      dsimp only [pointeeTyOf] at hBle
      cases hSz : rigidTyByteSize layouts { kind := inner, layoutIdx := 0 } <;>
        (simp only [hSz] at hBle;
         cases alloc.mutability <;> (simp only [evalStmt, hOp, hNoB, hG, hPTy, hSz, hBle]; rfl))
    | adt d args =>
      cases args with
      | nil =>
        dsimp only [pointeeTyOf] at hBle
        cases alloc.mutability <;> (simp only [evalStmt, hOp, hNoB, hG, hPTy, hBle]; rfl)
      | cons inner rest =>
        cases rest with
        | cons _ _ =>
          dsimp only [pointeeTyOf] at hBle
          cases alloc.mutability <;> (simp only [evalStmt, hOp, hNoB, hG, hPTy, hBle]; rfl)
        | nil =>
          dsimp only [pointeeTyOf] at hBle
          cases hBox : Bool.or (stringEq d "std::boxed::Box") (stringEq d "alloc::boxed::Box") with
          | false =>
            simp only [hBox] at hBle
            cases alloc.mutability <;>
              (simp only [evalStmt, pointeeTyOf, hOp, hNoB, hG, hPTy, hBox, hBle]; rfl)
          | true =>
            simp only [hBox] at hBle
            cases hSz : rigidTyByteSize layouts { kind := inner, layoutIdx := 0 } <;>
              (simp only [hSz] at hBle;
               cases alloc.mutability <;>
                 (simp only [evalStmt, pointeeTyOf, hOp, hNoB, hG, hPTy, hBox, hSz, hBle]; rfl))
    | bool | char | int _ | uint _ | float _ | never | str | tuple _ | array _ _
    | slice _ | fnDef _ _ | fnPtr _ _ _ _ | closure _ _
    | dynamic _ | foreign _ | param _ _ | alias _ _ | other _ =>
      dsimp only [pointeeTyOf] at hBle
      cases alloc.mutability <;> (simp only [evalStmt, hOp, hNoB, hG, hPTy, hBle]; rfl)

/-- **Documented `Retag(Raw)` untracked `.ptr` divergence (`B4`)**: Anneal's `Retag(Raw)` (matching
MiniRust/Miri's `Retag([raw] place)` Stacked/Tree Borrows raw-pointer retag rule: raw pointers do
not require a live pointee or active borrow/allocation entry at retag time as long as their address
fits the pointer width) accepts a thin `.ptr p sz` whose tag is absent from Trusted's borrow and
global-allocation tables (`lookupBorrow = none`, `lookupGlobalAlloc = none`), whereas Trusted's
`evalStmt` faults with `.fail .ub` (`isNonNullEmptySlice = false` on thin `.ptr`). -/
theorem evalStmt_retag_raw_untracked_divergence {ctx : RetagCtx} {place : Place}
    {ty : RetagTy} {b : Bool} (h : evalRetagPlace ctx .raw place ty b = true)
    {s : MachineState} (hRel : SlotsRefine SlotBelow ctx.slots s.frame.locals)
    (span : String) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hNoUnion : placeTouchesUnion localDecls layouts place = false := by
      simp [placeTouchesUnion_nil_proj]) :
    ∃ p sz, readPlaceState ctx.slots place = .ok (.ptr p sz) ∧
      (lookupBorrow s.memory.borrows p.tag = none →
        lookupGlobalAlloc s.memory.globals p.allocId = none →
        evalStmt s ⟨.retag .raw place, span⟩ localDecls layouts = .fail .ub) := by
  obtain ⟨_, p, sz, hRead, _⟩ := evalRetagPlace_raw_sound h
  refine ⟨p, sz, hRead, fun hNoB hNoG => ?_⟩
  have hOp := readPlaceState_below_evalOperand_copy hRel hRead s.memory.borrows s.memory.globals
    layouts s.memory.callerLocals localDecls hNoUnion
  simp only [evalStmt, hOp, hNoB, hNoG]

/-- **Provenance-less `.scalar` raw-pointer address rejection in `.retag .raw`**: in `Places.lean`,
provenance-less raw pointers (such as `0 as *const T` or integer-to-raw-ptr transmutes decoded via
`decodeScalarBytes`) are represented as `Value.scalar sc`; both `evalRetagPlace` (`.ptr`-typed raw
check) and Trusted's `evalStmt` (`extractDerefPtrVal? = none`) reject `.scalar sc` on `.retag .raw`
(whereas MiniRust/Miri's `Retag([raw] place)` permits provenance-less raw pointers without
retagging an allocation, modeled by `APtr { addr, provenance := none }` in Section 2h). -/
theorem evalStmt_retag_raw_scalar_addr_reject {ctx : RetagCtx} {place : Place}
    {ty : RetagTy} {b : Bool} {sc : ScalarInt}
    (hRead : readPlaceState ctx.slots place = .ok (.scalar sc))
    {s : MachineState} (hRel : SlotsRefine SlotBelow ctx.slots s.frame.locals)
    (span : String) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hNoUnion : placeTouchesUnion localDecls layouts place = false := by
      simp [placeTouchesUnion_nil_proj]) :
    evalRetagPlace ctx .raw place ty b = false ∧
      evalStmt s ⟨.retag .raw place, span⟩ localDecls layouts = .fail .ub := by
  have hOp := readPlaceState_below_evalOperand_copy hRel hRead s.memory.borrows s.memory.globals
    layouts s.memory.callerLocals localDecls hNoUnion
  refine ⟨?_, by simp only [evalStmt, hOp]⟩
  unfold evalRetagPlace
  split
  · rfl
  · rfl
  · simp [hRead]

/-- **Documented reference-free `Retag` divergence (`B4`)**: in Rust/MiniRust (`retag_place`), a
non-raw `Retag` of a reference-free non-union place (`ty.containsRef = false`, e.g. `u32`) that
Anneal can read is a no-op (the read discharges `prepare_place_access`'s checks), whereas Trusted's
`evalStmt` requires the retagged place itself to evaluate to a pointer (`extractDerefPtrVal?`),
faulting with `.fail .ub` on a scalar value `.scalar sc`. -/
theorem evalStmt_retag_noRef_scalar_divergence {ctx : RetagCtx} {kind : RetagKind}
    {place : Place} {ty : RetagTy} {b : Bool} {sc : ScalarInt} (hKind : kind ≠ .raw)
    (hNoRef : ty.containsRef = false) (hRead : readPlaceState ctx.slots place = .ok (.scalar sc))
    (hIdx : indexLocalsOk ctx.slots place.projection = true) {s : MachineState}
    (hRel : SlotsRefine SlotBelow ctx.slots s.frame.locals) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hNoUnion : placeTouchesUnion localDecls layouts place = false := by
      simp [placeTouchesUnion_nil_proj]) :
    evalRetagPlace ctx kind place ty b = true ∧
      evalStmt s ⟨.retag kind place, span⟩ localDecls layouts = .fail .ub := by
  have hLive : ∃ st, ctx.slots[place.local_]? = some st ∧ st ≠ .dead := by
    unfold readPlaceState at hRead
    split at hRead
    · nomatch hRead
    · cases hS : ctx.slots[place.local_]? with
      | none => simp [get?_eq_getElem?, hS] at hRead
      | some st =>
        cases st with
        | dead => simp [get?_eq_getElem?, hS] at hRead
        | uninit => exact ⟨_, rfl, by simp⟩
        | init _ => exact ⟨_, rfl, by simp⟩
        | partialShell _ => exact ⟨_, rfl, by simp⟩
  have hND : projectionHasDeref place.projection = false := by
    cases hD : projectionHasDeref place.projection with
    | false => rfl
    | true => simp only [readPlaceState, hD] at hRead; nomatch hRead
  have hOp := readPlaceState_below_evalOperand_copy hRel hRead s.memory.borrows s.memory.globals
    layouts s.memory.callerLocals localDecls hNoUnion
  exact ⟨(evalRetagPlace_noRef hKind hNoRef).mpr
      ⟨hLive, hND, hIdx, checkPlaceSlotOk_of_readPlaceState hRead⟩,
    by simp only [evalStmt, hOp]⟩

/-- **`Retag` on a niche-capable enum shell fails (`A3`)**: for a reference-bearing enum whose tag
requires a tag write (`rt = true`) but does not survive field deinitialization (`ts = false`),
retagging any incomplete shell fails (`false`), even after `SetDiscriminant` (`disc = true`). -/
theorem retagSlotOk_enum_niche_shell_false (ctx : RetagCtx) (vs : List RetagTy)
    (hRef : RetagTy.listContainsRef vs = true) (var : Nat) (adt disc : Bool)
    (cfs : List FieldSlot) :
    retagSlotOk ctx (.enum vs true false) (.nested var adt disc cfs) = false := by
  simp [retagSlotOk, hRef]

/-- **`Retag` on an ill-formed niche-capable enum value fails (`B4`)**: for a reference-bearing
niche-capable enum (`ts = false`), retagging an initialized value that fails
`check_value_well_formed` (`ctx.wf (.aggregate v vals) = false`) fails (`false`). -/
theorem retagValueOk_enum_niche_ill_formed_false (ctx : RetagCtx) (vs : List RetagTy) (rt : Bool)
    (hRef : RetagTy.listContainsRef vs = true) (v : Nat) (vals : List Value)
    (hBad : ctx.wf (.aggregate v vals) = false) :
    retagValueOk ctx (.enum vs rt false) (.aggregate v vals) = false := by
  simp [retagValueOk, hRef, hBad]

/-- The variant `v` of an enum description is uninhabited or does not exist: it is out of range,
or it is a variant whose fields are not all inhabited (e.g. a field of type `!`). -/
def RetagVariantRejected (vs : List RetagTy) (v : Nat) : Prop :=
  vs[v]? = none ∨ ∃ fs, vs[v]? = some (.tuple fs) ∧ RetagTy.allInhabited fs = false

/-- An uninhabited or out-of-range variant is rejected by both `retagVariantOk` and
`retagVariantSlotsOk` (`B2`). -/
theorem retagVariant_rejected_false (ctx : RetagCtx) :
    ∀ (vs : List RetagTy) (v : Nat), RetagVariantRejected vs v →
      (∀ vals, retagVariantOk ctx vs v vals = false) ∧
      (∀ cfs, retagVariantSlotsOk ctx vs v cfs = false)
  | [], _, _ => ⟨fun _ => rfl, fun _ => rfl⟩
  | t :: _, 0, h => by
    rcases h with hNone | ⟨fs, hSome, hUninh⟩
    · simp at hNone
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hSome
      subst hSome
      exact ⟨fun _ => by simp [retagVariantOk, hUninh], fun _ => by simp [retagVariantSlotsOk, hUninh]⟩
  | _ :: vs, v + 1, h => by
    have h' : RetagVariantRejected vs v := by
      rcases h with hNone | ⟨fs, hSome, hUninh⟩
      · exact Or.inl (by simpa using hNone)
      · exact Or.inr ⟨fs, by simpa using hSome, hUninh⟩
    simp only [retagVariantOk, retagVariantSlotsOk]
    exact retagVariant_rejected_false ctx vs v h'

/-- **`Retag` on an uninhabited or out-of-range enum variant fails (`B2`)**: for a
reference-bearing enum, retagging an initialized aggregate or a shell narrowed to a variant that
does not exist or has an uninhabited field (`UninhabitedEnumVariant`) fails. -/
theorem retagSlotOk_enum_variant_rejected_false (ctx : RetagCtx) (vs : List RetagTy)
    (rt ts : Bool) (hRef : RetagTy.listContainsRef vs = true) (v : Nat)
    (hRej : RetagVariantRejected vs v) :
    (∀ vals, retagSlotOk ctx (.enum vs rt ts) (.init (.aggregate v vals)) = false) ∧
    (∀ adt disc cfs, retagSlotOk ctx (.enum vs rt ts) (.nested v adt disc cfs) = false) := by
  obtain ⟨hVal, hSlot⟩ := retagVariant_rejected_false ctx vs v hRej
  refine ⟨fun vals => ?_, fun adt disc cfs => ?_⟩
  · simp [retagSlotOk, retagValueOk, hRef, hVal vals]
  · simp [retagSlotOk, hRef, hSlot cfs]

/-- Inversion of `retagVariantOk`: the selected variant exists, all its fields are inhabited, and
every field value passes `retag_value`. -/
theorem retagVariantOk_eq_true (ctx : RetagCtx) :
    ∀ (vs : List RetagTy) (v : Nat) (vals : List Value), retagVariantOk ctx vs v vals = true →
      ∃ fs, vs[v]? = some (.tuple fs) ∧ RetagTy.allInhabited fs = true ∧
        retagValuesOk ctx fs vals = true
  | [], _, _, h => by simp [retagVariantOk] at h
  | t :: _, 0, vals, h => by
    cases t with
    | tuple fs =>
      simp only [retagVariantOk, Bool.and_eq_true] at h
      exact ⟨fs, rfl, h.1, h.2⟩
    | _ => simp [retagVariantOk] at h
  | _ :: vs, v + 1, vals, h => by
    simp only [retagVariantOk] at h
    simpa using retagVariantOk_eq_true ctx vs v vals h

/-- **Enum retag soundness**: a successful retag of a reference-bearing enum value checked an
existing, inhabited variant (`B2`), the whole value's well-formedness when the tag may be
niche-encoded (`B4`), and every field of the variant. -/
theorem retagValueOk_enum_sound {ctx : RetagCtx} {vs : List RetagTy} {rt ts : Bool} {v : Nat}
    {vals : List Value} (hRef : RetagTy.listContainsRef vs = true)
    (h : retagValueOk ctx (.enum vs rt ts) (.aggregate v vals) = true) :
    (ts = true ∨ ctx.wf (.aggregate v vals) = true) ∧
      ∃ fs, vs[v]? = some (.tuple fs) ∧ RetagTy.allInhabited fs = true ∧
        retagValuesOk ctx fs vals = true := by
  simp only [retagValueOk, hRef, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    Bool.or_eq_true] at h
  exact ⟨h.1, retagVariantOk_eq_true ctx vs v vals h.2⟩

/-- Projecting along a deinitialized path (`UninitAt slot p`) either reaches `some .uninit` (at the
leaf of the shell tree) or stops early at an uninitialized ancestor (`none`). -/
theorem projectFieldSlot_of_uninitAt_aux (locals : List LocalSlot) :
    ∀ (n : Nat) (p : List ProjectionElem), p.length ≤ n → ∀ (slot : FieldSlot),
      UninitAt slot p →
      projectFieldSlot locals slot p = some .uninit ∨ projectFieldSlot locals slot p = none := by
  intro n
  induction n with
  | zero =>
    intro p hLen slot hU
    have hp : p = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hLen)
    subst hp
    cases slot with
    | uninit => exact Or.inl rfl
    | init v => exact absurd hU UninitAt.not_init
    | nested var adt disc fs => simp only [UninitAt] at hU
  | succ n ih =>
    intro p hLen slot hU
    cases slot with
    | uninit =>
      cases p with
      | nil => exact Or.inl rfl
      | cons a rest => exact Or.inr rfl
    | init v => exact absurd hU UninitAt.not_init
    | nested var adt disc fs =>
      rcases p with _ | ⟨a, rest⟩
      · simp only [UninitAt] at hU
      · simp only [List.length_cons] at hLen
        cases a
        case field idx ty =>
          simp only [UninitAt] at hU
          obtain ⟨hV, c, hc, hUc⟩ := hU
          simp only [projectFieldSlot, hV, ↓reduceIte, hc]
          exact ih rest (by omega) c hUc
        case downcast nm v =>
          rcases rest with _ | ⟨b, rest'⟩
          · simp only [UninitAt] at hU
          · simp only [List.length_cons] at hLen
            cases b
            case field idx ty =>
              simp only [UninitAt] at hU
              obtain ⟨hV, c, hc, hUc⟩ := hU
              simp only [projectFieldSlot, hV, ↓reduceIte, hc]
              exact ih rest' (by omega) c hUc
            all_goals simp only [UninitAt] at hU
        all_goals simp only [UninitAt] at hU

theorem projectFieldSlot_of_uninitAt (locals : List LocalSlot) {slot : FieldSlot}
    {p : List ProjectionElem} (hU : UninitAt slot p) :
    projectFieldSlot locals slot p = some .uninit ∨ projectFieldSlot locals slot p = none :=
  projectFieldSlot_of_uninitAt_aux locals p.length p (Nat.le_refl _) slot hU

/-- **`Deinit`-then-`Retag` soundness (`evalDeinitPlace_then_retag_same_false`)**: after a
successful `Deinit` of `place`, retagging `place` with any non-raw `RetagKind` and a
reference-bearing type (`ty.containsRef = true`) fails (`false`, `UninitializedLocal`). -/
theorem evalDeinitPlace_then_retag_same_false {ts : Bool} {slots : List LocalSlotState}
    {ctx : RetagCtx} {place : Place} {kind : RetagKind} {ty : RetagTy} {b : Bool}
    (hDeinit : evalDeinitPlace ts slots place = some ctx.slots)
    (hKind : kind ≠ .raw) (hRef : ty.containsRef = true) :
    evalRetagPlace ctx kind place ty b = false := by
  obtain ⟨st, hSt, _, slot', hD, hSlots⟩ := evalDeinitPlace_eq_some hDeinit
  have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hD
  obtain ⟨hRound, hNotDead⟩ := UninitAt.roundtrip hU
  have hLt : place.local_ < slots.length := (List.getElem?_eq_some_iff.mp hSt).1
  have hGet : ctx.slots[place.local_]? = some (fieldSlotToLocalSlotState slot') := by
    rw [hSlots]
    exact List.getElem?_set_self hLt
  unfold evalRetagPlace
  rw [hGet]
  split
  · rfl
  · rfl
  · rename_i st' _ hSome
    injection hSome with hEq
    subst hEq
    cases kind with
    | raw => exact absurd rfl hKind
    | _ =>
      simp only [hRef, Bool.not_true, Bool.false_or, hRound]
      rcases projectFieldSlot_of_uninitAt (slotsToTrustedLocals ctx.slots) hU with h1 | h2
      · rw [h1]; simp [retagSlotOk, hRef]
      · simp [h2]

/-! #### Unions in the typed `Deinit` walk -/

/-- Whether the `Deinit` walk of the path `p` from `root` reaches an *initialized union* with path
left to walk. In `deinit_in_slot`, "array elements and union fields have no per-part shells", so a
projected `Deinit` into an initialized union value is `UnsupportedPlaceProjection`. Union-ness is
a property of the declared types that the untyped value model cannot see (a union value is an
aggregate like any other), so `unionAt q` says whether the place prefix `q` is union-typed; the
walk reaches an initialized part at the proper prefix `p.take k` exactly when `projectFieldSlot`
yields `.init` there. -/
def deinitReachesInitUnion (unionAt : List ProjectionElem → Bool) (locals : List LocalSlot)
    (root : FieldSlot) (p : List ProjectionElem) : Bool :=
  (List.range p.length).any fun k =>
    unionAt (p.take k) &&
      match projectFieldSlot locals root (p.take k) with
      | some (.init _) => true
      | _ => false

/-- **Rust-faithful projected `Deinit`** (`StatementEvalState::deinit_place` with the declared
types' union information `unionAt`): `evalDeinitPlace`, except that a projected `Deinit` that
reaches an initialized union value with path left (`deinitReachesInitUnion`) is rejected
(`UnsupportedPlaceProjection`). -/
def evalDeinitPlaceTyped (unionAt : List ProjectionElem → Bool) (ts : Bool)
    (slots : List LocalSlotState) (place : Place) : Option (List LocalSlotState) :=
  match slots[place.local_]? with
  | none => none
  | some st =>
    if deinitReachesInitUnion unionAt (slotsToTrustedLocals slots) (slotStateToFieldSlot st)
        place.projection then none
    else evalDeinitPlace ts slots place

/-- **Every typed `Deinit` is an untyped one**: a successful `evalDeinitPlaceTyped` is a
successful `evalDeinitPlace` with the same result, so every `evalDeinitPlace` theorem (the lens
laws, the byte simulations, and the Trusted `evalStmt` refinements) applies to it. -/
theorem evalDeinitPlaceTyped_sound {unionAt : List ProjectionElem → Bool} {ts : Bool}
    {slots slots' : List LocalSlotState} {place : Place}
    (h : evalDeinitPlaceTyped unionAt ts slots place = some slots') :
    evalDeinitPlace ts slots place = some slots' := by
  unfold evalDeinitPlaceTyped at h
  split at h
  · nomatch h
  · split at h
    · nomatch h
    · exact h

/-- Without union-typed prefixes the typed `Deinit` is exactly the untyped one. -/
theorem evalDeinitPlaceTyped_no_union (ts : Bool) (slots : List LocalSlotState) (place : Place) :
    evalDeinitPlaceTyped (fun _ => false) ts slots place = evalDeinitPlace ts slots place := by
  unfold evalDeinitPlaceTyped deinitReachesInitUnion
  cases h : slots[place.local_]? with
  | none => simp [evalDeinitPlace, h]
  | some st => simp

/-- **A projected `Deinit` through an initialized union is rejected**
(`UnsupportedPlaceProjection`): if the walk reaches an initialized union-typed part at a proper
prefix of the path, the typed `Deinit` fails (while the untyped model would explode the union like
a struct; `union_field_uninit_bytes` shows why that would be wrong at the byte level). -/
theorem evalDeinitPlaceTyped_through_init_union_none {unionAt : List ProjectionElem → Bool}
    {ts : Bool} {slots : List LocalSlotState} {place : Place} {st : LocalSlotState} {k : Nat}
    {w : Value} (hSt : slots[place.local_]? = some st) (hk : k < place.projection.length)
    (hU : unionAt (place.projection.take k) = true)
    (hInit : projectFieldSlot (slotsToTrustedLocals slots) (slotStateToFieldSlot st)
      (place.projection.take k) = some (.init w)) :
    evalDeinitPlaceTyped unionAt ts slots place = none := by
  have hReach : deinitReachesInitUnion unionAt (slotsToTrustedLocals slots)
      (slotStateToFieldSlot st) place.projection = true := by
    unfold deinitReachesInitUnion
    rw [List.any_eq_true]
    exact ⟨k, List.mem_range.mpr hk, by simp [hU, hInit]⟩
  unfold evalDeinitPlaceTyped
  rw [hSt]
  simp only [hReach, ↓reduceIte]

/-- **`Deinit` of a field of an initialized union local is rejected**: the root local is
union-typed and initialized, so every projected `Deinit` of it fails, whereas the untyped
`evalDeinitPlace` would succeed on a union value's field (e.g. `Deinit(u.0)` on
`u = .init (.aggregate 0 [v])`). -/
theorem evalDeinitPlaceTyped_init_union_root_none {unionAt : List ProjectionElem → Bool}
    {ts : Bool} {slots : List LocalSlotState} {loc : Local} {v : Value} {a : ProjectionElem}
    {rest : List ProjectionElem} (hU : unionAt [] = true)
    (hRoot : slots[loc]? = some (.init v)) :
    evalDeinitPlaceTyped unionAt ts slots ⟨loc, a :: rest⟩ = none :=
  evalDeinitPlaceTyped_through_init_union_none (st := .init v) (k := 0) (w := v) hRoot
    (by simp) (by simpa using hU) (by simp [slotStateToFieldSlot, projectFieldSlot])

/-- The divergence the typed walk closes: the untyped `evalDeinitPlace` accepts `Deinit(u.0)` on
an initialized single-field aggregate (as it must for a struct), while the typed walk rejects it
when the local is a union. -/
theorem evalDeinitPlace_union_field_divergence {ts : Bool} {slots : List LocalSlotState}
    {loc : Local} {v : Value} {ty : Ty} (hRoot : slots[loc]? = some (.init (.aggregate 0 [v])))
    (unionAt : List ProjectionElem → Bool) (hU : unionAt [] = true) :
    (∃ slots', evalDeinitPlace ts slots ⟨loc, [.field 0 ty]⟩ = some slots') ∧
      evalDeinitPlaceTyped unionAt ts slots ⟨loc, [.field 0 ty]⟩ = none := by
  refine ⟨?_, evalDeinitPlaceTyped_init_union_root_none hU hRoot⟩
  simp [evalDeinitPlace, hRoot, slotStateToFieldSlot, deinitFieldSlot, deinitShellStep,
    explodeAggregate, shellVariant]

/-- Projecting into an `.uninit` root slot never reaches an initialized part (`some (.init w)`). -/
theorem projectFieldSlot_uninit_ne_init (locals : List LocalSlot) (q : List ProjectionElem)
    (w : Value) : projectFieldSlot locals .uninit q ≠ some (.init w) := by
  cases q <;> intro h <;> nomatch h

/-- `deinitReachesInitUnion` is always `false` on an `.uninit` root slot (`rvalue.rs:7943` handles
`FieldSlot::Uninit` before checking whether `slot` holds an initialized union). -/
theorem deinitReachesInitUnion_uninit (unionAt : List ProjectionElem → Bool)
    (locals : List LocalSlot) (p : List ProjectionElem) :
    deinitReachesInitUnion unionAt locals .uninit p = false := by
  unfold deinitReachesInitUnion
  cases h : ((List.range p.length).any fun k =>
      unionAt (p.take k) &&
        match projectFieldSlot locals .uninit (p.take k) with
        | some (.init _) => true
        | _ => false) with
  | false => rfl
  | true =>
    obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true] at hk
    split at hk
    · rename_i w hInit
      exact absurd hInit (projectFieldSlot_uninit_ne_init locals (p.take k) w)
    · nomatch hk.2

/-- **On an uninitialized local, `evalDeinitPlaceTyped` equals `evalDeinitPlace` for any `unionAt`
(`B4`)**: `evalDeinitPlaceTyped` only rejects projections through *initialized* union values, never
through uninitialized union places. -/
theorem evalDeinitPlaceTyped_uninit_eq (unionAt : List ProjectionElem → Bool) (ts : Bool)
    {slots : List LocalSlotState} {place : Place} (hRoot : slots[place.local_]? = some .uninit) :
    evalDeinitPlaceTyped unionAt ts slots place = evalDeinitPlace ts slots place := by
  unfold evalDeinitPlaceTyped
  rw [hRoot]
  simp [slotStateToFieldSlot, deinitReachesInitUnion_uninit]

/-- **Projected `Deinit` on an uninitialized union local succeeds (`B4`, `rvalue.rs:7943`)**: even
when the root local is union-typed (`unionAt [] = true`), deinitializing a well-formed projection
`a :: rest` (`deinitTailOk = true`) on an uninitialized union local is a successful no-op. -/
theorem evalDeinitPlaceTyped_uninit_union_ok (unionAt : List ProjectionElem → Bool) (ts : Bool)
    {slots : List LocalSlotState} {loc : Local} {a : ProjectionElem} {rest : List ProjectionElem}
    (hRoot : slots[loc]? = some .uninit)
    (hTail : deinitTailOk (slotsToTrustedLocals slots) (a :: rest) = true) :
    evalDeinitPlaceTyped unionAt ts slots ⟨loc, a :: rest⟩ = some (slots.set loc .uninit) := by
  rw [evalDeinitPlaceTyped_uninit_eq unionAt ts hRoot]
  simp [evalDeinitPlace, hRoot, slotStateToFieldSlot, deinitFieldSlot, hTail,
    fieldSlotToLocalSlotState]

/-- **Nested initialized union rejection (`evalDeinitPlaceTyped_nested_init_union_none`, `B4`)**:
if an initialized struct/tuple local `slots[loc]? = some (.init (.aggregate 0 vals))` has an
initialized union field `vals[f]? = some u` (`unionAt [.field f ty] = true`), deinitializing a
sub-place `⟨loc, .field f ty :: a :: rest⟩` inside that union field fails (`none`). -/
theorem evalDeinitPlaceTyped_nested_init_union_none {unionAt : List ProjectionElem → Bool}
    {ts : Bool} {slots : List LocalSlotState} {loc : Local} {vals : List Value} {f : Nat}
    {ty : Ty} {u : Value} {a : ProjectionElem} {rest : List ProjectionElem}
    (hRoot : slots[loc]? = some (.init (.aggregate 0 vals)))
    (hField : vals[f]? = some u) (hU : unionAt [.field f ty] = true) :
    evalDeinitPlaceTyped unionAt ts slots ⟨loc, .field f ty :: a :: rest⟩ = none := by
  apply evalDeinitPlaceTyped_through_init_union_none (st := .init (.aggregate 0 vals)) (k := 1)
    (w := u) hRoot (by simp) (by simpa using hU)
  simp [slotStateToFieldSlot, projectFieldSlot, hField, evalValueProjRead]

/-- Every `deinitTailOk` path satisfies `indexLocalsOk` (`prepare_place_access`'s index pre-read). -/
theorem deinitTailOk_indexLocalsOk (slots : List LocalSlotState) (p : List ProjectionElem)
    (h : deinitTailOk (slotsToTrustedLocals slots) p = true) :
    indexLocalsOk slots p = true := by
  fun_induction deinitTailOk (slotsToTrustedLocals slots) p with
  | case1 => rfl
  | case2 idx ty rest ih => simpa [indexLocalsOk] using ih h
  | case3 nm v idx ty rest ih => simpa [indexLocalsOk] using ih h
  | case4 i rest sc hSc ih =>
    have hSc' : slots[i]? = some (.init (.scalar sc)) := by
      simpa [get?_eq_getElem?] using (get?_slotsToTrustedLocals_scalar_iff slots i sc).mp hSc
    simpa [indexLocalsOk, hSc'] using ih h
  | case5 => nomatch h
  | case6 offset minLen fromEnd rest ih =>
    simp only [Bool.and_eq_true] at h
    simpa [indexLocalsOk] using ih h.2
  | case7 from_ to_ fromEnd rest ih =>
    simp only [Bool.and_eq_true] at h
    simpa [indexLocalsOk] using ih h.2
  | case8 => nomatch h

/-- Every successful `deinitFieldSlot` path satisfies `indexLocalsOk`. -/
theorem deinitFieldSlot_indexLocalsOk {ts : Bool} {slots : List LocalSlotState}
    {slot slot' : FieldSlot} {p : List ProjectionElem}
    (h : deinitFieldSlot ts (slotsToTrustedLocals slots) slot p = some slot') :
    indexLocalsOk slots p = true := by
  fun_induction deinitFieldSlot ts (slotsToTrustedLocals slots) slot p generalizing slot' with
  | case1 => rfl
  | case2 p rest hT => exact deinitTailOk_indexLocalsOk slots (p :: rest) hT
  | case3 => nomatch h
  | case4 var vals idx ty rest ih =>
    obtain ⟨_, c, c', _, hcc, _⟩ := deinitShellStep_eq_some h
    simpa [indexLocalsOk] using ih c hcc
  | case5 var vals nm v idx ty rest ih =>
    obtain ⟨_, c, c', _, hcc, _⟩ := deinitShellStep_eq_some h
    simpa [indexLocalsOk] using ih c hcc
  | case6 var adt disc fs idx ty rest ih =>
    obtain ⟨_, c, c', _, hcc, _⟩ := deinitShellStep_eq_some h
    simpa [indexLocalsOk] using ih c hcc
  | case7 var adt disc fs nm v idx ty rest ih =>
    obtain ⟨_, c, c', _, hcc, _⟩ := deinitShellStep_eq_some h
    simpa [indexLocalsOk] using ih c hcc
  | case8 => nomatch h

/-- **Every successful `evalDeinitPlace` satisfies `indexLocalsOk` (`B4`)**. -/
theorem evalDeinitPlace_indexLocalsOk {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} (h : evalDeinitPlace ts slots place = some slots') :
    indexLocalsOk slots place.projection = true := by
  obtain ⟨_, _, _, slot', hD, _⟩ := evalDeinitPlace_eq_some h
  exact deinitFieldSlot_indexLocalsOk hD

/-- **`Deinit` through an unreadable `Index` operand local fails (`B4`, `rvalue.rs:6299`)**: for
both `evalDeinitPlace` and `evalDeinitPlaceTyped`, if `.index i ∈ place.projection` and local `i`
does not hold an initialized scalar, `Deinit` returns `none`. -/
theorem evalDeinitPlace_bad_index_none (unionAt : List ProjectionElem → Bool) (ts : Bool)
    (slots : List LocalSlotState) {place : Place} {i : Local} (hIdx : .index i ∈ place.projection)
    (hBad : ∀ sc, slots[i]? ≠ some (.init (.scalar sc))) :
    evalDeinitPlace ts slots place = none ∧
      evalDeinitPlaceTyped unionAt ts slots place = none := by
  have hNone : evalDeinitPlace ts slots place = none := by
    cases hD : evalDeinitPlace ts slots place with
    | none => rfl
    | some slots' =>
      have hOk := evalDeinitPlace_indexLocalsOk hD
      unfold indexLocalsOk at hOk
      rw [List.all_eq_true] at hOk
      have hE := hOk _ hIdx
      cases hS : slots[i]? with
      | none => simp [hS] at hE
      | some st =>
        cases st with
        | init v =>
          cases v with
          | scalar sc => exact absurd hS (hBad sc)
          | _ => simp [hS] at hE
        | _ => simp [hS] at hE
  refine ⟨hNone, ?_⟩
  cases hT : evalDeinitPlaceTyped unionAt ts slots place with
  | none => rfl
  | some slots' =>
    have hD := evalDeinitPlaceTyped_sound hT
    rw [hNone] at hD
    nomatch hD

/-! ### Section 2g: `CopyNonOverlapping` -/

/-- A pointer operand of `copy_nonoverlapping`: its address and the allocation id of its
provenance (`none` without provenance). -/
structure CopyPtr : Type where
  addr : Nat
  allocId : Option Nat

/-- The checks `eval_copy_nonoverlapping` performs before any memory access, for a target with
`ptrBits`-bit pointers (`max_usize = 2^ptrBits - 1`, `max_object_size = isize::MAX`):
1. the count and both addresses are valid `usize` / pointer bit patterns (never truncated);
2. even when the byte length is `0` (`count = 0` or a ZST), both pointers are non-null and
   aligned to the element type;
3. `count * elemSize ≤ isize::MAX` (`CopyLengthOverflow`) and neither range wraps the address
   space (`PointerRangeOverflow`);
4. a non-empty copy between pointers of the same allocation does not overlap
   (`CopyNonOverlappingOverlap`), i.e. Trusted's `rangesDisjoint` holds. -/
def copyNonOverlappingChecks (ptrBits : Nat) (src dst : CopyPtr) (count elemSize elemAlign : Nat) :
    Bool :=
  let maxUsize := 2 ^ ptrBits - 1
  let byteLen := count * elemSize
  decide (count ≤ maxUsize) && decide (src.addr ≤ maxUsize) && decide (dst.addr ≤ maxUsize) &&
    (src.addr != 0) && (dst.addr != 0) &&
    isAlignedOffset src.addr elemAlign && isAlignedOffset dst.addr elemAlign &&
    decide (byteLen ≤ 2 ^ (ptrBits - 1) - 1) &&
    decide (src.addr + byteLen ≤ maxUsize) && decide (dst.addr + byteLen ≤ maxUsize) &&
    (count == 0 || byteLen == 0 || src.allocId != dst.allocId ||
      rangesDisjoint src.addr byteLen dst.addr byteLen)

/-- Trusted's `rangesDisjoint` spelled out. -/
theorem rangesDisjoint_iff (s₁ l₁ s₂ l₂ : Nat) :
    rangesDisjoint s₁ l₁ s₂ l₂ = true ↔ s₁ + l₁ ≤ s₂ ∨ s₂ + l₂ ≤ s₁ := by
  simp [rangesDisjoint, Nat.ble_eq]

/-- **Overlap is exactly the failure of Trusted's `rangesDisjoint`**: `eval_copy_nonoverlapping`'s
overlap test `src < dst + len ∧ dst < src + len` holds iff `rangesDisjoint src len dst len` is
false. -/
theorem copyOverlap_iff_not_rangesDisjoint (src dst len : Nat) :
    (src < dst + len ∧ dst < src + len) ↔ rangesDisjoint src len dst len = false := by
  have h := rangesDisjoint_iff src len dst len
  constructor
  · rintro ⟨h1, h2⟩
    cases hR : rangesDisjoint src len dst len with
    | false => rfl
    | true => rcases h.mp hR with h3 | h3 <;> omega
  · intro hR
    have : ¬ (src + len ≤ dst ∨ dst + len ≤ src) := fun h' => by rw [h.mpr h'] at hR; nomatch hR
    omega

/-- Inversion of `copyNonOverlappingChecks`. -/
theorem copyNonOverlappingChecks_eq_true {ptrBits : Nat} {src dst : CopyPtr}
    {count elemSize elemAlign : Nat}
    (h : copyNonOverlappingChecks ptrBits src dst count elemSize elemAlign = true) :
    count ≤ 2 ^ ptrBits - 1 ∧ src.addr ≤ 2 ^ ptrBits - 1 ∧ dst.addr ≤ 2 ^ ptrBits - 1 ∧
      src.addr ≠ 0 ∧ dst.addr ≠ 0 ∧
      isAlignedOffset src.addr elemAlign = true ∧ isAlignedOffset dst.addr elemAlign = true ∧
      count * elemSize ≤ 2 ^ (ptrBits - 1) - 1 ∧
      src.addr + count * elemSize ≤ 2 ^ ptrBits - 1 ∧
      dst.addr + count * elemSize ≤ 2 ^ ptrBits - 1 ∧
      (count = 0 ∨ count * elemSize = 0 ∨ src.allocId ≠ dst.allocId ∨
        rangesDisjoint src.addr (count * elemSize) dst.addr (count * elemSize) = true) := by
  simp only [copyNonOverlappingChecks, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_⟩
  rcases h11 with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (by simp only [rangesDisjoint, Bool.or_eq_true]; exact h)))

/-- **Zero-length copies are still checked**: even with `count = 0` (or a zero-sized element),
`copy_nonoverlapping` requires non-null, aligned, in-width pointers. -/
theorem copyNonOverlappingChecks_zero_len_sound {ptrBits : Nat} {src dst : CopyPtr}
    {count elemSize elemAlign : Nat}
    (h : copyNonOverlappingChecks ptrBits src dst count elemSize elemAlign = true) :
    src.addr ≠ 0 ∧ dst.addr ≠ 0 ∧ isAlignedOffset src.addr elemAlign = true ∧
      isAlignedOffset dst.addr elemAlign = true ∧ src.addr ≤ 2 ^ ptrBits - 1 ∧
      dst.addr ≤ 2 ^ ptrBits - 1 := by
  obtain ⟨_, h2, h3, h4, h5, h6, h7, _⟩ := copyNonOverlappingChecks_eq_true h
  exact ⟨h4, h5, h6, h7, h2, h3⟩

/-- A null pointer is rejected even for a zero-length copy (`NullPointerAccess`). -/
theorem copyNonOverlappingChecks_null_src (ptrBits : Nat) (dst : CopyPtr) (allocId : Option Nat)
    (count elemSize elemAlign : Nat) :
    copyNonOverlappingChecks ptrBits ⟨0, allocId⟩ dst count elemSize elemAlign = false := by
  simp [copyNonOverlappingChecks]

/-- **Agreement with Trusted's `rangesDisjoint`**: a successful non-empty copy within one
allocation copies between byte ranges that Trusted's `rangesDisjoint` accepts. -/
theorem copyNonOverlappingChecks_disjoint {ptrBits : Nat} {src dst : CopyPtr}
    {count elemSize elemAlign : Nat}
    (h : copyNonOverlappingChecks ptrBits src dst count elemSize elemAlign = true)
    (hLen : 0 < count * elemSize) (hSame : src.allocId = dst.allocId) :
    rangesDisjoint src.addr (count * elemSize) dst.addr (count * elemSize) = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h11⟩ := copyNonOverlappingChecks_eq_true h
  rcases h11 with h | h | h | h
  · subst h; simp at hLen
  · omega
  · exact absurd hSame h
  · exact h

/-- **Agreement with Trusted's zero-count `copyNonOverlapping`**: once its operands are
evaluated, Trusted's copy of `0` elements is a no-op step (it never faults); Anneal's zero-count
copy is likewise a no-op after `copyNonOverlappingChecks`, so every successful Anneal zero-count
copy is matched by a Trusted step (Anneal is stricter: it also checks null/alignment/width). -/
theorem evalCopyNonOverlappingWithCount_zero (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (locals₃ : List LocalSlot) :
    evalCopyNonOverlappingWithCount s src dst localDecls layouts srcVal dstVal 0 locals₃ =
      .step (advanceStmt s locals₃) := rfl

/-- The frame facts `eval_copy_nonoverlapping` consults about locals: each local's synthetic base
address (`synthetic_local_ptr`), the number of declared locals, and whether a local is declared
with the copied element type. -/
structure CopyEnv : Type where
  baseAddr : Nat → Nat
  nDecls : Nat
  declIsElem : Nat → Bool

/-- The number of locals a provenance can name (`slots.len().min(local_decls.len())`). -/
def CopyEnv.localCount (env : CopyEnv) (slots : List LocalSlotState) : Nat :=
  min slots.length env.nDecls

/-- The local a pointer's provenance names (`alloc_id - 1`, when it is one of the `n` locals of
the frame). -/
def provenanceLocal (n : Nat) (p : CopyPtr) : Option Nat :=
  match p.allocId with
  | some (l + 1) => if l < n then some l else none
  | _ => none

/-- `resolve_synthetic_local`: the local whose synthetic base pointer `p` is — its provenance
local, when `p`'s address is that local's synthetic base address. -/
def resolveSyntheticLocal (env : CopyEnv) (n : Nat) (p : CopyPtr) : Option Nat :=
  match provenanceLocal n p with
  | some l => if p.addr = env.baseAddr l then some l else none
  | none => none

/-- The `DeadLocal` check of `eval_copy_nonoverlapping`: the pointer's provenance names a
storage-dead local. -/
def copyTargetDead (env : CopyEnv) (slots : List LocalSlotState) (p : CopyPtr) : Bool :=
  match provenanceLocal (env.localCount slots) p with
  | some l =>
    match slots[l]? with
    | some .dead => true
    | _ => false
  | none => false

/-- The local a pointer designates as a whole: `resolve_synthetic_local` plus the declared-type
check (`local_decls[l] == elem_ty`). -/
def copyWholeLocal (env : CopyEnv) (slots : List LocalSlotState) (p : CopyPtr) : Option Nat :=
  match resolveSyntheticLocal env (env.localCount slots) p with
  | some l => if env.declIsElem l then some l else none
  | none => none

/-- **Stateful `Statement::Intrinsic(CopyNonOverlapping)`** (`eval_copy_nonoverlapping`, after
its operands are evaluated to the pointers `src`, `dst` and the count):
1. `copyNonOverlappingChecks` (width, null, alignment, length, wrap, overlap), even for an empty
   copy;
2. `count = 0` is then a no-op;
3. when the byte length is non-zero or `count = 1`, a pointer whose provenance names a
   storage-dead local is `DeadLocal` (an empty bulk copy skips this check);
4. an empty copy (zero-sized elements) copies the source local's state into the destination
   local when both pointers are distinct whole locals and `count = 1`, and is otherwise a no-op;
5. a non-empty copy is supported only as a whole-local copy (`count = 1`), which gives the
   destination local the source local's state verbatim (including `.uninit` and partial
   shells); any other access is `UnsupportedMemoryAccess`.
Whole locals are resolved from the pointers themselves (`resolveSyntheticLocal`), so a pointer
whose provenance is not a local of the frame is never a whole local. -/
def evalCopyNonOverlappingState (ptrBits : Nat) (env : CopyEnv) (slots : List LocalSlotState)
    (src dst : CopyPtr) (count elemSize elemAlign : Nat) : Option (List LocalSlotState) :=
  if !copyNonOverlappingChecks ptrBits src dst count elemSize elemAlign then none
  else if count = 0 then some slots
  else if (count * elemSize != 0 || count == 1) &&
      (copyTargetDead env slots src || copyTargetDead env slots dst) then none
  else if count * elemSize = 0 then
    match copyWholeLocal env slots src, copyWholeLocal env slots dst with
    | some sl, some dl =>
      if count = 1 ∧ sl ≠ dl then
        match slots[sl]? with
        | some st => some (slots.set dl st)
        | none => none
      else some slots
    | _, _ => some slots
  else
    match copyWholeLocal env slots src, copyWholeLocal env slots dst with
    | some sl, some dl =>
      if count = 1 then
        match slots[sl]? with
        | some st => some (slots.set dl st)
        | none => none
      else none
    | _, _ => none

/-- A provenance local is one of the `n` locals, named by `alloc_id = l + 1`. -/
theorem provenanceLocal_spec {n : Nat} {p : CopyPtr} {l : Nat} (h : provenanceLocal n p = some l) :
    l < n ∧ p.allocId = some (l + 1) := by
  unfold provenanceLocal at h
  split at h
  · rename_i l' hA
    split at h
    · rename_i hLt
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hLt, hA⟩
    · nomatch h
  · nomatch h

/-- `resolve_synthetic_local` returns a provenance local whose synthetic base address is the
pointer's address. -/
theorem resolveSyntheticLocal_spec {env : CopyEnv} {n : Nat} {p : CopyPtr} {l : Nat}
    (h : resolveSyntheticLocal env n p = some l) :
    l < n ∧ p.allocId = some (l + 1) ∧ p.addr = env.baseAddr l := by
  unfold resolveSyntheticLocal at h
  split at h
  · rename_i l' hP
    split at h
    · rename_i hAddr
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨(provenanceLocal_spec hP).1, (provenanceLocal_spec hP).2, hAddr⟩
    · nomatch h
  · nomatch h

/-- A whole local is a local of the frame, designated by its own synthetic base pointer. -/
theorem copyWholeLocal_spec {env : CopyEnv} {slots : List LocalSlotState} {p : CopyPtr} {l : Nat}
    (h : copyWholeLocal env slots p = some l) :
    l < slots.length ∧ l < env.nDecls ∧ p.allocId = some (l + 1) ∧ p.addr = env.baseAddr l ∧
      env.declIsElem l = true := by
  unfold copyWholeLocal at h
  split at h
  · rename_i l' hR
    split at h
    · rename_i hDecl
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hLt, hA, hAddr⟩ := resolveSyntheticLocal_spec hR
      simp only [CopyEnv.localCount, Nat.lt_min] at hLt
      exact ⟨hLt.1, hLt.2, hA, hAddr, hDecl⟩
    · nomatch h
  · nomatch h

/-- **`count = 0` is a no-op after `copyNonOverlappingChecks`**. -/
theorem evalCopyNonOverlappingState_zero_count {ptrBits : Nat} {env : CopyEnv}
    {slots : List LocalSlotState} {src dst : CopyPtr} {elemSize elemAlign : Nat}
    (hChk : copyNonOverlappingChecks ptrBits src dst 0 elemSize elemAlign = true) :
    evalCopyNonOverlappingState ptrBits env slots src dst 0 elemSize elemAlign = some slots := by
  simp [evalCopyNonOverlappingState, hChk]

/-- **Dead provenance faults (`DeadLocal`)** for every non-empty copy and every single-element
copy (including a single zero-sized element). -/
theorem evalCopyNonOverlappingState_dead_none {ptrBits : Nat} {env : CopyEnv}
    {slots : List LocalSlotState} {src dst : CopyPtr} {count elemSize elemAlign : Nat}
    (hCount : count ≠ 0) (hLen : count * elemSize ≠ 0 ∨ count = 1)
    (hDead : copyTargetDead env slots src = true ∨ copyTargetDead env slots dst = true) :
    evalCopyNonOverlappingState ptrBits env slots src dst count elemSize elemAlign = none := by
  unfold evalCopyNonOverlappingState
  cases hChk : copyNonOverlappingChecks ptrBits src dst count elemSize elemAlign with
  | false => rfl
  | true =>
    have hGuard : ((count * elemSize != 0 || count == 1) &&
        (copyTargetDead env slots src || copyTargetDead env slots dst)) = true := by
      rcases hLen with h | h <;> rcases hDead with hd | hd <;> simp [h, hd]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hCount, hGuard]

/-- An empty bulk copy (`count ≥ 2` zero-sized elements) is a no-op even through the provenance
of a storage-dead local (`eval_copy_nonoverlapping` only checks liveness when the byte length is
non-zero or `count = 1`). -/
theorem evalCopyNonOverlappingState_zst_bulk_noop {ptrBits : Nat} {env : CopyEnv}
    {slots : List LocalSlotState} {src dst : CopyPtr} {count elemAlign : Nat}
    (hChk : copyNonOverlappingChecks ptrBits src dst count 0 elemAlign = true)
    (hCount : 2 ≤ count) :
    evalCopyNonOverlappingState ptrBits env slots src dst count 0 elemAlign = some slots := by
  have h0 : count ≠ 0 := by omega
  have h1 : (count == 1) = false := by simp; omega
  unfold evalCopyNonOverlappingState
  simp only [hChk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h0, Nat.mul_zero,
    bne_self_eq_false, Bool.false_or, h1, Bool.false_and]
  split
  · split
    · rename_i hC
      omega
    · rfl
  · rfl

/-- **Whole-local copies copy the source state verbatim**: a single-element copy between whole
locals (distinct when zero-sized) gives the destination local exactly the source local's state —
including `.uninit` and partial shells. -/
theorem evalCopyNonOverlappingState_whole_local_copies_slot {ptrBits : Nat} {env : CopyEnv}
    {slots : List LocalSlotState} {src dst : CopyPtr} {elemSize elemAlign sl dl : Nat}
    {st : LocalSlotState}
    (hChk : copyNonOverlappingChecks ptrBits src dst 1 elemSize elemAlign = true)
    (hSrc : copyWholeLocal env slots src = some sl) (hDst : copyWholeLocal env slots dst = some dl)
    (hLive : copyTargetDead env slots src = false ∧ copyTargetDead env slots dst = false)
    (hDistinct : elemSize ≠ 0 ∨ sl ≠ dl) (hSt : slots[sl]? = some st) :
    evalCopyNonOverlappingState ptrBits env slots src dst 1 elemSize elemAlign =
      some (slots.set dl st) := by
  unfold evalCopyNonOverlappingState
  simp only [hChk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.one_ne_zero, hLive.1,
    hLive.2, Bool.or_self, Bool.and_false, Nat.one_mul, hSrc, hDst, hSt]
  by_cases hZ : elemSize = 0
  · have hNe : sl ≠ dl := by rcases hDistinct with h | h; exact absurd hZ h; exact h
    simp [hZ, hNe]
  · simp [hZ]

/-- The whole-local copy of an uninitialized zero-sized local uninitializes the destination
(the slot is copied verbatim; it is not a no-op). -/
theorem evalCopyNonOverlappingState_zst_copies_uninit {ptrBits : Nat} {env : CopyEnv}
    {slots : List LocalSlotState} {src dst : CopyPtr} {elemAlign sl dl : Nat}
    (hChk : copyNonOverlappingChecks ptrBits src dst 1 0 elemAlign = true)
    (hSrc : copyWholeLocal env slots src = some sl) (hDst : copyWholeLocal env slots dst = some dl)
    (hLive : copyTargetDead env slots src = false ∧ copyTargetDead env slots dst = false)
    (hNe : sl ≠ dl) (hSt : slots[sl]? = some .uninit) :
    evalCopyNonOverlappingState ptrBits env slots src dst 1 0 elemAlign =
      some (slots.set dl .uninit) :=
  evalCopyNonOverlappingState_whole_local_copies_slot hChk hSrc hDst hLive (Or.inr hNe) hSt

/-- **A non-empty copy of a whole local onto itself is rejected (`CopyNonOverlappingOverlap`)**:
both pointers carry the same provenance and the same synthetic base address, so their ranges
overlap and `copyNonOverlappingChecks` fails. -/
theorem evalCopyNonOverlappingState_same_local_non_zst_none {ptrBits : Nat} {env : CopyEnv}
    {slots : List LocalSlotState} {src dst : CopyPtr} {count elemSize elemAlign l : Nat}
    (hLen : 0 < count * elemSize) (hSrc : copyWholeLocal env slots src = some l)
    (hDst : copyWholeLocal env slots dst = some l) :
    evalCopyNonOverlappingState ptrBits env slots src dst count elemSize elemAlign = none := by
  obtain ⟨_, _, hSA, hSAddr, _⟩ := copyWholeLocal_spec hSrc
  obtain ⟨_, _, hDA, hDAddr, _⟩ := copyWholeLocal_spec hDst
  have hChkFalse : copyNonOverlappingChecks ptrBits src dst count elemSize elemAlign = false := by
    cases hC : copyNonOverlappingChecks ptrBits src dst count elemSize elemAlign with
    | false => rfl
    | true =>
      have hDisj := copyNonOverlappingChecks_disjoint hC hLen (by rw [hSA, hDA])
      rw [hSAddr, hDAddr, rangesDisjoint_iff] at hDisj
      omega
  simp [evalCopyNonOverlappingState, hChkFalse]

/-- A zero-sized copy that is not a whole-local copy (e.g. between a local and a non-local
pointer, or through a provenance that is not a local of the frame) is a successful no-op. -/
theorem evalCopyNonOverlappingState_zst_non_whole_noop {ptrBits : Nat} {env : CopyEnv}
    {slots : List LocalSlotState} {src dst : CopyPtr} {count elemAlign : Nat}
    (hChk : copyNonOverlappingChecks ptrBits src dst count 0 elemAlign = true)
    (hLive : copyTargetDead env slots src = false ∧ copyTargetDead env slots dst = false)
    (hNotWhole : copyWholeLocal env slots src = none ∨ copyWholeLocal env slots dst = none) :
    evalCopyNonOverlappingState ptrBits env slots src dst count 0 elemAlign = some slots := by
  unfold evalCopyNonOverlappingState
  simp only [hChk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hLive.1, hLive.2,
    Bool.or_self, Bool.and_false, Nat.mul_zero]
  by_cases h0 : count = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    rcases hNotWhole with h | h
    · simp [h]
    · cases copyWholeLocal env slots src <;> simp [h]

/-- A non-empty copy that is not a single whole-local copy is unsupported
(`UnsupportedMemoryAccess`): the model never invents a byte-level memory. -/
theorem evalCopyNonOverlappingState_non_whole_unsupported {ptrBits : Nat} {env : CopyEnv}
    {slots : List LocalSlotState} {src dst : CopyPtr} {count elemSize elemAlign : Nat}
    (hLen : count * elemSize ≠ 0)
    (hNotWhole : copyWholeLocal env slots src = none ∨ copyWholeLocal env slots dst = none ∨
      count ≠ 1) :
    evalCopyNonOverlappingState ptrBits env slots src dst count elemSize elemAlign = none := by
  have hC : count ≠ 0 := by intro h; subst h; simp at hLen
  unfold evalCopyNonOverlappingState
  cases hChk : copyNonOverlappingChecks ptrBits src dst count elemSize elemAlign with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hC, hLen]
    split
    · rfl
    · rcases hNotWhole with h | h | h
      · simp [h]
      · cases copyWholeLocal env slots src <;> simp [h]
      · cases copyWholeLocal env slots src <;> cases copyWholeLocal env slots dst <;> simp [h]

/-- **Whole-local `CopyNonOverlapping` preserves `SlotsRefine SlotBelow`**: when Anneal copies a
whole local `srcLoc` into `dstLoc` (`slots.set dstLoc srcSt`) and Trusted updates `dstLoc` to
`locals[srcLoc]`, the frames remain related by `SlotsRefine SlotBelow`. -/
theorem evalCopyNonOverlappingState_whole_local_below {slots : List LocalSlotState}
    {locals : List LocalSlot} {srcLoc dstLoc : Nat} {srcSt : LocalSlotState} {tSrc : LocalSlot}
    (hRel : SlotsRefine SlotBelow slots locals)
    (hSrc : slots[srcLoc]? = some srcSt) (hTSrc : locals[srcLoc]? = some tSrc) :
    SlotsRefine SlotBelow (slots.set dstLoc srcSt) (locals.set dstLoc tSrc) := by
  rcases SlotsRefine.get?_rel srcLoc hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, hAT⟩
  · simp only [get?_eq_getElem?] at hA
    rw [hA] at hSrc
    nomatch hSrc
  · simp only [get?_eq_getElem?] at hA hT
    rw [hA] at hSrc
    rw [hT] at hTSrc
    cases hSrc
    cases hTSrc
    exact SlotsRefine.set hAT dstLoc hRel

/-- **Read-After-Copy on bare destination local (`evalCopyNonOverlappingState_read_dst_bare`)**:
after a successful whole-local `evalCopyNonOverlappingState` copying `sl` to `dl`, reading the
bare destination local `⟨dl, []⟩` in the updated frame yields the exact same `ProjReadResult` as
reading the bare source local `⟨sl, []⟩` in the pre-state (whether `.ok v` or `.ub`). -/
theorem evalCopyNonOverlappingState_read_dst_bare {ptrBits : Nat} {env : CopyEnv}
    {slots slots' : List LocalSlotState} {src dst : CopyPtr} {elemSize elemAlign sl dl : Nat}
    {st : LocalSlotState}
    (hChk : copyNonOverlappingChecks ptrBits src dst 1 elemSize elemAlign = true)
    (hSrc : copyWholeLocal env slots src = some sl)
    (hDst : copyWholeLocal env slots dst = some dl)
    (hLive : copyTargetDead env slots src = false ∧ copyTargetDead env slots dst = false)
    (hDistinct : elemSize ≠ 0 ∨ sl ≠ dl) (hSt : slots[sl]? = some st)
    (hEval : evalCopyNonOverlappingState ptrBits env slots src dst 1 elemSize elemAlign =
      some slots') :
    readPlaceState slots' ⟨dl, []⟩ = readPlaceState slots ⟨sl, []⟩ := by
  have hEq := evalCopyNonOverlappingState_whole_local_copies_slot hChk hSrc hDst hLive hDistinct hSt
  rw [hEq] at hEval
  injection hEval with hSlots
  subst hSlots
  have hDlLt : dl < slots.length := (copyWholeLocal_spec hDst).1
  have hGetDl : (slots.set dl st)[dl]? = some st := List.getElem?_set_self hDlLt
  unfold readPlaceState
  simp only [projectionHasDeref, get?_eq_getElem?, hGetDl, hSt]
  cases st <;> rfl

/-- **Other-Local Frame of whole-local `CopyNonOverlapping`
(`evalCopyNonOverlappingState_read_other_bare`)**: after a successful whole-local copy from `sl`
to `dl`, reading any other bare local `⟨loc', []⟩` (`loc' ≠ dl`) is unchanged. -/
theorem evalCopyNonOverlappingState_read_other_bare {ptrBits : Nat} {env : CopyEnv}
    {slots slots' : List LocalSlotState} {src dst : CopyPtr} {elemSize elemAlign sl dl : Nat}
    {st : LocalSlotState} {loc' : Local} (hNe : loc' ≠ dl)
    (hChk : copyNonOverlappingChecks ptrBits src dst 1 elemSize elemAlign = true)
    (hSrc : copyWholeLocal env slots src = some sl)
    (hDst : copyWholeLocal env slots dst = some dl)
    (hLive : copyTargetDead env slots src = false ∧ copyTargetDead env slots dst = false)
    (hDistinct : elemSize ≠ 0 ∨ sl ≠ dl) (hSt : slots[sl]? = some st)
    (hEval : evalCopyNonOverlappingState ptrBits env slots src dst 1 elemSize elemAlign =
      some slots') :
    readPlaceState slots' ⟨loc', []⟩ = readPlaceState slots ⟨loc', []⟩ := by
  have hEq := evalCopyNonOverlappingState_whole_local_copies_slot hChk hSrc hDst hLive hDistinct hSt
  rw [hEq] at hEval
  injection hEval with hSlots
  subst hSlots
  unfold readPlaceState
  simp only [projectionHasDeref, get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hNe)]
  cases slots[loc']? with
  | none => rfl
  | some s => cases s <;> rfl

/-- **Trusted's `evalCopySingleDirect` rejects same-local whole-local copies (`B3`)**: when `src`
and `dst` resolve to the root of the same local (`srcEntry.targetLocal = dstEntry.targetLocal` and
both target projections are `[]`), `evalCopySingleDirect` faults with `.fail .ub` (matching
Anneal's `evalCopyNonOverlappingState_same_local_non_zst_none`). -/
theorem evalCopySingleDirect_same_local_ub (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry) (locals₃ : List LocalSlot)
    (hSameLoc : srcEntry.targetLocal = dstEntry.targetLocal)
    (hSrcNil : srcEntry.targetProjection = []) (hDstNil : dstEntry.targetProjection = []) :
    evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃ =
      .fail .ub := by
  unfold evalCopySingleDirect
  rcases beq_cases srcPtr.tag dstPtr.tag with ⟨hBTag, _⟩ | ⟨hBTag, _⟩
  · simp [hBTag]
  · have hOv : projectionsOverlap [] [] = true := rfl
    simp [hSameLoc, hSrcNil, hDstNil, hBTag, hOv]

/-- **Trusted's `evalCopySingleDirect` faults when the source local is dead or uninitialized**:
matching Anneal's `DeadLocal` check and uninitialized-read UB on typed values. -/
theorem evalCopySingleDirect_dead_or_uninit_src_ub (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry) (locals₃ : List LocalSlot)
    (hSrc : locals₃[srcEntry.targetLocal]? = some .dead ∨
      locals₃[srcEntry.targetLocal]? = some .uninit) :
    evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃ =
      .fail .ub := by
  unfold evalCopySingleDirect
  rcases hSrc with hD | hU
  · simp only [get?_eq_getElem?, hD]
    split <;> rfl
  · simp only [get?_eq_getElem?, hU]
    split <;> rfl

/-- **A whole local passing `!copyTargetDead` is in bounds and live (`B4`)**:
`copyWholeLocal env slots p = some l` and `copyTargetDead env slots p = false` imply
`∃ st, slots[l]? = some st ∧ st ≠ .dead`. -/
theorem copyWholeLocal_live_of_not_copyTargetDead {env : CopyEnv} {slots : List LocalSlotState}
    {p : CopyPtr} {l : Nat} (hW : copyWholeLocal env slots p = some l)
    (hNotDead : copyTargetDead env slots p = false) :
    ∃ st, slots[l]? = some st ∧ st ≠ .dead := by
  obtain ⟨hLtS, hLtD, hAlloc, _, _⟩ := copyWholeLocal_spec hW
  have hLtC : l < env.localCount slots := Nat.lt_min.mpr ⟨hLtS, hLtD⟩
  have hProv : provenanceLocal (env.localCount slots) p = some l := by
    simp [provenanceLocal, hAlloc, hLtC]
  have hSt : slots[l]? = some slots[l] := List.getElem?_eq_getElem hLtS
  refine ⟨slots[l], hSt, fun hDead => ?_⟩
  rw [hDead] at hSt
  simp [copyTargetDead, hProv, hSt] at hNotDead

/-- **Whole-local `count = 1` `CopyNonOverlapping` refines Trusted's `evalCopySingleDirect` (`B3`/`B4`)**:
on below-related frames (`SlotsRefine SlotBelow slots locals₃`), when Anneal's
`evalCopyNonOverlappingState` copies an initialized whole local `sl` (`slots[sl]? = some (.init v)`)
into a distinct whole local `dl` (`sl ≠ dl`), destination liveness follows automatically from
`copyWholeLocal` and `copyTargetDead = false`, and whenever `v` satisfies Trusted's root-local
`bool`/`char` bit-validity guard (`validateValueForTy? layouts (placeTy localDecls layouts ⟨dl, []⟩) v = true`
— automatic for every non-`bool`/non-`char` destination via `validateValueForTy?_of_not_bool_char`,
for `localDecls = []`, or for valid `bool`/`char` scalars), Trusted's `evalCopySingleDirect`
(with distinct borrow tags on root places `⟨sl, []⟩` and `⟨dl, []⟩`, for untyped or same-shape
typed pointees and any `localDecls` / borrow stack `s.memory.borrows`) steps to `advanceStmt` with
`locals₃.set dl (.init v)` and `invalidateConflictingBorrows s.memory.borrows dl (some dstPtr.tag)`,
while the updated frames stay related by `SlotsRefine SlotBelow`. -/
theorem evalCopySingleDirect_whole_local_refines {ptrBits : Nat} {env : CopyEnv}
    {slots slots' : List LocalSlotState} {locals₃ : List LocalSlot}
    {src dst : CopyPtr} {elemSize elemAlign sl dl : Nat} {v : Value}
    (hRel : SlotsRefine SlotBelow slots locals₃)
    (hChk : copyNonOverlappingChecks ptrBits src dst 1 elemSize elemAlign = true)
    (hSrcW : copyWholeLocal env slots src = some sl)
    (hDstW : copyWholeLocal env slots dst = some dl)
    (hLive : copyTargetDead env slots src = false ∧ copyTargetDead env slots dst = false)
    (hNe : sl ≠ dl)
    (hSrcInit : slots[sl]? = some (.init v))
    (hEval : evalCopyNonOverlappingState ptrBits env slots src dst 1 elemSize elemAlign =
      some slots')
    (s : MachineState) (srcOp dstOp : Operand) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (hTagNe : srcPtr.tag ≠ dstPtr.tag)
    (hSrcEntry : srcEntry.targetLocal = sl ∧ srcEntry.targetProjection = [])
    (hDstEntry : dstEntry.targetLocal = dl ∧ dstEntry.targetProjection = [])
    (hPointee : operandPointeeTy localDecls layouts srcOp = none ∨
      ∃ srcPt dstPt, operandPointeeTy localDecls layouts srcOp = some srcPt ∧
        operandPointeeTy localDecls layouts dstOp = some dstPt ∧
        sameRigidTyShape srcPt.kind dstPt.kind = true)
    (hValid : validateValueForTy? layouts (placeTy localDecls layouts ⟨dl, []⟩) v = true := by
      simp [placeTy, validateValueForTy?]) :
    evalCopySingleDirect s srcOp dstOp localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃ =
        .step (advanceStmt s (locals₃.set dl (.init v))
          { s.memory with
            borrows := invalidateConflictingBorrows s.memory.borrows dl (some dstPtr.tag) }) ∧
      SlotsRefine SlotBelow slots' (locals₃.set dl (.init v)) := by
  obtain ⟨dstSt, hDstLive, hDstNotDead⟩ := copyWholeLocal_live_of_not_copyTargetDead hDstW hLive.2
  have hEq := evalCopyNonOverlappingState_whole_local_copies_slot hChk hSrcW hDstW hLive
    (Or.inr hNe) hSrcInit
  rw [hEq] at hEval
  injection hEval with hSlots
  subst hSlots
  have hTSrc : locals₃[sl]? = some (.init v) := by
    rcases SlotsRefine.get?_rel sl hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, hAT⟩
    · simp only [get?_eq_getElem?] at hA; rw [hA] at hSrcInit; nomatch hSrcInit
    · simp only [get?_eq_getElem?] at hA hT
      rw [hA] at hSrcInit; cases hSrcInit
      cases t with
      | init w => have hvw : v = w := hAT; subst hvw; exact hT
      | _ => simp [SlotBelow] at hAT
  have hTDst : ∃ tDst, locals₃[dl]? = some tDst ∧ tDst ≠ .dead := by
    rcases SlotsRefine.get?_rel dl hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, hAT⟩
    · simp only [get?_eq_getElem?] at hA; rw [hA] at hDstLive; nomatch hDstLive
    · simp only [get?_eq_getElem?] at hA hT
      rw [hA] at hDstLive; cases hDstLive
      refine ⟨t, hT, fun hTD => ?_⟩
      subst hTD
      cases dstSt with
      | dead => exact hDstNotDead rfl
      | _ => simp [SlotBelow] at hAT
  obtain ⟨tDst, hTDstSlot, hTDstNotDead⟩ := hTDst
  have hDlLt : dl < locals₃.length := (List.getElem?_eq_some_iff.mp hTDstSlot).1
  have hGetDst : get? locals₃ dl = some tDst := by simp [get?_eq_getElem?, hTDstSlot]
  have hSetDst : set? locals₃ dl (.init v) = some (locals₃.set dl (.init v)) :=
    set?_eq_some_iff.mpr ⟨hDlLt, rfl⟩
  have hWrite :
      writePlaceValue locals₃ s.memory.borrows ⟨dl, []⟩ v localDecls layouts =
        .ok (locals₃.set dl (.init v)) :=
    writePlaceValue_root_of_valid locals₃ (locals₃.set dl (.init v)) s.memory.borrows dl tDst v
      localDecls layouts hGetDst hTDstNotDead hValid hSetDst
  refine ⟨?_, evalCopyNonOverlappingState_whole_local_below hRel hSrcInit hTSrc⟩
  unfold evalCopySingleDirect
  rcases beq_cases srcPtr.tag dstPtr.tag with ⟨_, hEqTag⟩ | ⟨hBTag, _⟩
  · exact absurd hEqTag hTagNe
  · rcases beq_cases sl dl with ⟨_, hEqLoc⟩ | ⟨hBLoc, _⟩
    · exact absurd hEqLoc hNe
    · rcases hPointee with hUntyped | ⟨srcPt, dstPt, hSPt, hDPt, hShape⟩
      · simp only [hSrcEntry.1, hSrcEntry.2, hDstEntry.1, hDstEntry.2, hBTag, hBLoc,
          get?_eq_getElem?, hTSrc, readProjectedValue, hUntyped, hWrite]
      · simp only [hSrcEntry.1, hSrcEntry.2, hDstEntry.1, hDstEntry.2, hBTag, hBLoc,
          get?_eq_getElem?, hTSrc, readProjectedValue, hSPt, hDPt, hShape, hWrite]

/-- **Documented untyped `copy_nonoverlapping` into `bool`/`char` root-local divergence**: in
Rust/MiniRust, `core::intrinsics::copy_nonoverlapping` is an untyped byte copy (so copying e.g.
`2u8` into a `bool` local via raw pointers succeeds in `evalCopyNonOverlappingState` and only a
subsequent typed load of the `bool` faults), whereas when `dl` is declared `bool` or `char` with
`validateValueForTy? layouts (placeTy localDecls layouts ⟨dl, []⟩) v = false` (which already forces
`localDecls ≠ []`), Trusted's value-based `writePlaceValue` rejects the root write at
`evalCopySingleDirect` with `.fail .ub`. -/
theorem evalCopySingleDirect_whole_local_invalid_bool_char_divergence {ptrBits : Nat}
    {env : CopyEnv} {slots : List LocalSlotState} {locals₃ : List LocalSlot}
    {src dst : CopyPtr} {elemSize elemAlign sl dl : Nat} {v : Value}
    (hRel : SlotsRefine SlotBelow slots locals₃)
    (hChk : copyNonOverlappingChecks ptrBits src dst 1 elemSize elemAlign = true)
    (hSrcW : copyWholeLocal env slots src = some sl)
    (hDstW : copyWholeLocal env slots dst = some dl)
    (hLive : copyTargetDead env slots src = false ∧ copyTargetDead env slots dst = false)
    (hNe : sl ≠ dl)
    (hSrcInit : slots[sl]? = some (.init v))
    (s : MachineState) (srcOp dstOp : Operand) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (hTagNe : srcPtr.tag ≠ dstPtr.tag)
    (hSrcEntry : srcEntry.targetLocal = sl ∧ srcEntry.targetProjection = [])
    (hDstEntry : dstEntry.targetLocal = dl ∧ dstEntry.targetProjection = [])
    (hPointee : operandPointeeTy localDecls layouts srcOp = none ∨
      ∃ srcPt dstPt, operandPointeeTy localDecls layouts srcOp = some srcPt ∧
        operandPointeeTy localDecls layouts dstOp = some dstPt ∧
        sameRigidTyShape srcPt.kind dstPt.kind = true)
    (hInvalid : validateValueForTy? layouts (placeTy localDecls layouts ⟨dl, []⟩) v = false) :
    evalCopyNonOverlappingState ptrBits env slots src dst 1 elemSize elemAlign =
        some (slots.set dl (.init v)) ∧
      evalCopySingleDirect s srcOp dstOp localDecls layouts srcPtr dstPtr srcEntry dstEntry
        locals₃ = .fail .ub := by
  obtain ⟨dstSt, hDstLive, _⟩ := copyWholeLocal_live_of_not_copyTargetDead hDstW hLive.2
  have hEq := evalCopyNonOverlappingState_whole_local_copies_slot hChk hSrcW hDstW hLive
    (Or.inr hNe) hSrcInit
  have hTSrc : locals₃[sl]? = some (.init v) := by
    rcases SlotsRefine.get?_rel sl hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, hAT⟩
    · simp only [get?_eq_getElem?] at hA; rw [hA] at hSrcInit; nomatch hSrcInit
    · simp only [get?_eq_getElem?] at hA hT
      rw [hA] at hSrcInit; cases hSrcInit
      cases t with
      | init w => have hvw : v = w := hAT; subst hvw; exact hT
      | _ => simp [SlotBelow] at hAT
  have hTDst : ∃ tDst, locals₃[dl]? = some tDst := by
    rcases SlotsRefine.get?_rel dl hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, _⟩
    · simp only [get?_eq_getElem?] at hA; rw [hA] at hDstLive; nomatch hDstLive
    · simp only [get?_eq_getElem?] at hA hT
      rw [hA] at hDstLive; cases hDstLive
      exact ⟨t, hT⟩
  obtain ⟨tDst, hTDstSlot⟩ := hTDst
  have hWriteUb :
      writePlaceValue locals₃ s.memory.borrows ⟨dl, []⟩ v localDecls layouts = .ub := by
    cases localDecls with
    | nil => simp [placeTy, validateValueForTy?] at hInvalid
    | cons d ds =>
      unfold writePlaceValue
      dsimp only
      rw [hInvalid]
  refine ⟨hEq, ?_⟩
  unfold evalCopySingleDirect
  rcases beq_cases srcPtr.tag dstPtr.tag with ⟨_, hEqTag⟩ | ⟨hBTag, _⟩
  · exact absurd hEqTag hTagNe
  · rcases beq_cases sl dl with ⟨_, hEqLoc⟩ | ⟨hBLoc, _⟩
    · exact absurd hEqLoc hNe
    · rcases hPointee with hUntyped | ⟨srcPt, dstPt, hSPt, hDPt, hShape⟩
      · simp only [hSrcEntry.1, hSrcEntry.2, hDstEntry.1, hDstEntry.2, hBTag, hBLoc,
          get?_eq_getElem?, hTSrc, readProjectedValue, hUntyped, hWriteUb, hTDstSlot]
      · simp only [hSrcEntry.1, hSrcEntry.2, hDstEntry.1, hDstEntry.2, hBTag, hBLoc,
          get?_eq_getElem?, hTSrc, readProjectedValue, hSPt, hDPt, hShape, hWriteUb, hTDstSlot]

/-! ### Section 2h: `ShallowInitBox`, `WrapUnsafeBinder`, and `PointerCoercion` -/

/-- Anneal's pointer value (`PointerValue`): an address and the allocation id of its
provenance. -/
structure APtr : Type where
  addr : Nat
  provenance : Option Nat
  deriving DecidableEq

/-- A raw pointer type `*m T` over abstract pointee types `τ`. -/
structure RawPtrTy (τ : Type) : Type where
  pointee : τ
  mutable : Bool

/-- `PointerCoercionKind`. -/
inductive PtrCoercion : Type where
  | mutToConst : PtrCoercion
  | arrayToPointer : PtrCoercion

/-- `is_valid_pointer_coercion`: `*mut T → *const T`, or `*m [T; N] → *m T` (same mutability);
`arrayElem` gives the element type of an array pointee. -/
def validPointerCoercion {τ : Type} [DecidableEq τ] (arrayElem : τ → Option τ) :
    PtrCoercion → RawPtrTy τ → RawPtrTy τ → Bool
  | .mutToConst, src, tgt => src.mutable && !tgt.mutable && decide (src.pointee = tgt.pointee)
  | .arrayToPointer, src, tgt =>
    decide (src.mutable = tgt.mutable) && decide (arrayElem src.pointee = some tgt.pointee)

/-- `PointerCoercion` (`eval_cast_in_state`): a valid coercion keeps the address (masked to the
pointer width) and the provenance and retypes the pointer. -/
def evalPointerCoercion {τ : Type} [DecidableEq τ] (arrayElem : τ → Option τ) (ptrBits : Nat)
    (c : PtrCoercion) (src tgt : RawPtrTy τ) (p : APtr) : Option (APtr × RawPtrTy τ) :=
  if validPointerCoercion arrayElem c src tgt then
    some (⟨p.addr % 2 ^ ptrBits, p.provenance⟩, tgt)
  else none

/-- **`PointerCoercion` never gains mutability**: a valid coercion to a mutable pointer starts
from a mutable pointer. -/
theorem validPointerCoercion_no_mut_gain {τ : Type} [DecidableEq τ] (arrayElem : τ → Option τ)
    (c : PtrCoercion) (src tgt : RawPtrTy τ) (h : validPointerCoercion arrayElem c src tgt = true)
    (hTgt : tgt.mutable = true) : src.mutable = true := by
  cases c with
  | mutToConst =>
    simp only [validPointerCoercion, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1
  | arrayToPointer =>
    simp only [validPointerCoercion, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1]
    exact hTgt

/-- **`PointerCoercion` preserves the pointer**: the provenance is unchanged and an in-width
address is unchanged; `MutToConstPointer` keeps the pointee and drops mutability. -/
theorem evalPointerCoercion_preserves {τ : Type} [DecidableEq τ] {arrayElem : τ → Option τ}
    {ptrBits : Nat} {c : PtrCoercion} {src tgt : RawPtrTy τ} {p q : APtr} {ty : RawPtrTy τ}
    (h : evalPointerCoercion arrayElem ptrBits c src tgt p = some (q, ty))
    (hW : p.addr < 2 ^ ptrBits) :
    q = p ∧ ty = tgt ∧ (c = .mutToConst → ty.pointee = src.pointee ∧ ty.mutable = false) := by
  unfold evalPointerCoercion at h
  split at h
  · rename_i hV
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp [Nat.mod_eq_of_lt hW], rfl, ?_⟩
    rintro rfl
    simp only [validPointerCoercion, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hV
    exact ⟨hV.2.symm, hV.1.2⟩
  · nomatch h

/-- `ShallowInitBox(op, T)` (`eval_shallow_init_box`): a raw-pointer operand becomes a `*mut T`
with the same address (masked to the pointer width) and provenance; any other operand is a
`TypeMismatch`. -/
def evalShallowInitBox {τ : Type} (ptrBits : Nat) (operandTy : Option (RawPtrTy τ)) (inner : τ)
    (p : APtr) : Option (APtr × RawPtrTy τ) :=
  match operandTy with
  | some _ => some (⟨p.addr % 2 ^ ptrBits, p.provenance⟩, ⟨inner, true⟩)
  | none => none

/-- **`ShallowInitBox` preservation**: the result is a mutable raw pointer to the boxed type
with the operand's provenance and (in-width) address. -/
theorem evalShallowInitBox_preserves {τ : Type} {ptrBits : Nat} {operandTy : Option (RawPtrTy τ)}
    {inner : τ} {p q : APtr} {ty : RawPtrTy τ}
    (h : evalShallowInitBox ptrBits operandTy inner p = some (q, ty)) :
    operandTy.isSome = true ∧ ty = ⟨inner, true⟩ ∧ q.provenance = p.provenance ∧
      q.addr < 2 ^ ptrBits ∧ (p.addr < 2 ^ ptrBits → q = p) := by
  unfold evalShallowInitBox at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, Nat.mod_lt _ (Nat.two_pow_pos _), fun hW => by
      simp [Nat.mod_eq_of_lt hW]⟩
  · nomatch h

/-- `WrapUnsafeBinder(op, ty)` (`eval_wrap_unsafe_binder`): the operand must be well formed
(`check_value_well_formed`); it is returned unchanged when `ty` is the operand type, and
otherwise wrapped as the single field of the struct `ty`, whose `scalar_valid_range` (if any,
with the field's bit width) it must satisfy. -/
def evalWrapUnsafeBinder (wf : Value → Bool) (wraps : Bool)
    (range? : Option (ScalarValidRange × Nat)) (v : Value) : Option Value :=
  if !wf v then none
  else if !wraps then some v
  else
    match range?, v with
    | none, _ => some (.aggregate 0 [v])
    | some (r, w), .scalar sc => if r.contains sc.bits w then some (.aggregate 0 [v]) else none
    | some _, _ => none

/-- **`WrapUnsafeBinder` preservation**: the result is the operand itself or the single-field
wrapper whose field `0` reads back exactly the operand; the operand is well formed. -/
theorem evalWrapUnsafeBinder_preserves {wf : Value → Bool} {wraps : Bool}
    {range? : Option (ScalarValidRange × Nat)} {v out : Value}
    (h : evalWrapUnsafeBinder wf wraps range? v = some out) (locals : List LocalSlot) (ty : Ty) :
    wf v = true ∧
      ((wraps = false ∧ out = v) ∨
        (wraps = true ∧ out = .aggregate 0 [v] ∧
          evalValueProjRead locals out [.field 0 ty] = .ok v)) := by
  unfold evalWrapUnsafeBinder at h
  cases hW : wf v with
  | false => simp [hW] at h
  | true =>
    refine ⟨rfl, ?_⟩
    cases wraps with
    | false =>
      simp only [hW, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Option.some.injEq] at h
      exact Or.inl ⟨rfl, h.symm⟩
    | true =>
      simp only [hW, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      have hOut : out = .aggregate 0 [v] := by
        split at h
        · exact (Option.some.inj h).symm
        · split at h
          · exact (Option.some.inj h).symm
          · nomatch h
        · nomatch h
      subst hOut
      exact Or.inr ⟨rfl, rfl, rfl⟩

/-- **`WrapUnsafeBinder` enforces the wrapper's niche**: a scalar outside the wrapper struct's
`scalar_valid_range` (e.g. `0` for a `NonZero`-like wrapper) is rejected. -/
theorem evalWrapUnsafeBinder_rejects_niche {wf : Value → Bool} {r : ScalarValidRange} {w : Nat}
    {sc : ScalarInt} (hOut : r.contains sc.bits w = false) :
    evalWrapUnsafeBinder wf true (some (r, w)) (.scalar sc) = none := by
  unfold evalWrapUnsafeBinder
  cases wf (.scalar sc) <;> simp [hOut]

/-- **Operand evaluation refines Trusted on below-related frames**: every successful non-union
Anneal operand evaluation (`copy`, `move`, or a constant) is matched by Trusted's `evalOperand`
with the same value for arbitrary `localDecls`, and the frames stay related. The default
`localDecls := []` is not a restriction where Section 3 uses it: Trusted's `evalTerminator`
evaluates the `switchInt` discriminant and the `assert` condition without local declarations. -/
theorem evalOperandState_below_refines (slots slots' : List LocalSlotState)
    (locals : List LocalSlot) (op : Operand) (val : Value) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (hRel : SlotsRefine SlotBelow slots locals) (hNoDeref : OperandNonDeref op)
    (hEval : evalOperandState slots op layouts globals = (.ok val, slots'))
    (localDecls : List LocalDecl := [])
    (hNoUnion : operandTouchesUnion localDecls layouts op = false := by
      simp [operandTouchesUnion_nil_decls, placeTouchesUnion_nil_proj]) :
    ∃ locals', evalOperand locals op borrows globals layouts callerLocals localDecls =
        .ok val locals' ∧
      SlotsRefine SlotBelow slots' locals' := by
  cases op with
  | constant constOp =>
    unfold evalOperandState at hEval
    dsimp only at hEval
    cases hVal : constOp.val with
    | indirect _ _ => rw [hVal] at hEval; nomatch hEval
    | unevaluated _ => rw [hVal] at hEval; nomatch hEval
    | zeroSized =>
      rw [hVal] at hEval
      dsimp only at hEval
      cases hC : evalConstValue .zeroSized constOp.ty globals layouts with
      | none => rw [hC] at hEval; nomatch hEval
      | some cVal =>
        rw [hC] at hEval
        injection hEval with hRes hSlots
        injection hRes with hV
        subst hV hSlots
        refine ⟨locals, ?_, hRel⟩
        dsimp only [evalOperand]
        rw [hVal]
        dsimp only
        rw [hC]
    | scalar sc =>
      rw [hVal] at hEval
      dsimp only at hEval
      cases hC : evalConstValue (.scalar sc) constOp.ty globals layouts with
      | none => rw [hC] at hEval; nomatch hEval
      | some cVal =>
        rw [hC] at hEval
        injection hEval with hRes hSlots
        injection hRes with hV
        subst hV hSlots
        refine ⟨locals, ?_, hRel⟩
        dsimp only [evalOperand]
        rw [hVal]
        dsimp only
        rw [hC]
    | slice aId len =>
      rw [hVal] at hEval
      dsimp only at hEval
      cases hC : evalConstValue (.slice aId len) constOp.ty globals layouts with
      | none => rw [hC] at hEval; nomatch hEval
      | some cVal =>
        rw [hC] at hEval
        injection hEval with hRes hSlots
        injection hRes with hV
        subst hV hSlots
        refine ⟨locals, ?_, hRel⟩
        dsimp only [evalOperand]
        rw [hVal]
        dsimp only
        rw [hC]
  | copy place =>
    unfold evalOperandState at hEval
    dsimp only at hEval
    injection hEval with hRead hSlots
    subst hSlots
    exact ⟨locals, readPlaceState_below_evalOperand_copy hRel hRead borrows globals layouts
      callerLocals localDecls hNoUnion, hRel⟩
  | move place =>
    rcases place with ⟨loc, proj⟩
    unfold evalOperandState movePlaceState at hEval
    dsimp only at hEval
    cases hRead : readPlaceState slots ⟨loc, proj⟩ with
    | ub => rw [hRead] at hEval; nomatch hEval
    | unsupported => rw [hRead] at hEval; nomatch hEval
    | ok outVal =>
      rw [hRead] at hEval
      dsimp only at hEval
      obtain ⟨rootVal, hGetT, hTRead⟩ := readPlaceState_below_refines hRel hRead
      cases proj with
      | nil =>
        injection hEval with hRes hSlots
        injection hRes with hV
        subst hV hSlots
        unfold readProjectedValue at hTRead
        injection hTRead with hRootEq
        subst hRootEq
        have hLtT : loc < locals.length := by
          simp only [get?_eq_getElem?] at hGetT
          exact (List.getElem?_eq_some_iff.mp hGetT).1
        have hSetT : set? locals loc .uninit = .some (locals.set loc .uninit) :=
          set?_eq_some_iff.mpr ⟨hLtT, rfl⟩
        refine ⟨locals.set loc .uninit, ?_,
          SlotsRefine.set (R := SlotBelow) (a := .uninit) (t := .uninit) trivial loc hRel⟩
        dsimp only [evalOperand]
        rw [hGetT]
        dsimp only
        rw [hSetT]
      | cons p rest =>
        injection hEval with hRes hSlots
        injection hRes with hV
        subst hV hSlots
        refine ⟨locals, ?_, hRel⟩
        have hNotDeref : p ≠ .deref := fun hEq => hNoDeref rest (congrArg (· :: rest) hEq)
        exact evalOperand_move_proj_of_noUnion locals loc p rest borrows globals layouts
          callerLocals localDecls rootVal outVal hNotDeref hNoUnion hGetT hTRead

/-- A successful Anneal place read has no `Deref`. -/
theorem readPlaceState_ok_noDeref {slots : List LocalSlotState} {place : Place} {v : Value}
    (h : readPlaceState slots place = .ok v) : projectionHasDeref place.projection = false := by
  cases hD : projectionHasDeref place.projection with
  | false => rfl
  | true => simp only [readPlaceState, hD] at h; nomatch h

/-- **`Discriminant` refines Trusted's `evalRvalue`**: on below-related frames, when Anneal reads
an initialized enum value at a non-union `place` and `evalAdtDiscriminant` succeeds with `d`,
Trusted's `evalRvalue (.discriminant place)` (without layout information for the place) succeeds
with the variant index as an 8-byte scalar and an unchanged frame, and `d` is that variant's
declared discriminant. -/
theorem evalAdtDiscriminant_refines_evalRvalue {slots : List LocalSlotState}
    {locals : List LocalSlot} {place : Place} {v : Nat} {fields : List Value}
    {spec : AdtDiscrSpec} {wf : Value → Bool} {d : Nat}
    (hRel : SlotsRefine SlotBelow slots locals)
    (hRead : readPlaceState slots place = .ok (.aggregate v fields))
    (hEnum : spec.isEnum = true)
    (h : evalAdtDiscriminant spec wf (.init (.aggregate v fields)) = some d)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hTy : placeTy localDecls layouts place = none)
    (hNoUnion : placeTouchesUnion localDecls layouts place = false := by
      simp [placeTouchesUnion_nil_proj]) :
    evalRvalue locals (.discriminant place) mem localDecls layouts =
        .ok (.scalar ⟨v, 8⟩) locals mem ∧
      spec.discriminants[v]? = some d := by
  obtain ⟨hT, hD, _⟩ :=
    evalAdtDiscriminant_init_agrees_trusted spec wf hEnum h locals mem place localDecls layouts hTy
  refine ⟨?_, hD⟩
  unfold evalRvalue
  simp only [readPlaceState_below_evalOperand_copy hRel hRead mem.borrows mem.globals layouts
    mem.callerLocals localDecls hNoUnion]
  exact hT

/-- Trusted's `evalRvalue` on `WrapUnsafeBinder` of a copied non-union place (no `Deref`) returns
the operand's value itself, with the frame unchanged, whenever Anneal can read the place on a
below-related frame and the loaded value is valid for its type (`validateLoadedValue`). -/
theorem evalRvalue_wrapUnsafeBinder_copy {slots : List LocalSlotState} {locals : List LocalSlot}
    {place : Place} {v : Value} (hRel : SlotsRefine SlotBelow slots locals)
    (hRead : readPlaceState slots place = .ok v) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hValid : validateLoadedValue layouts localDecls (.copy place) v = true)
    (hNoUnion : placeTouchesUnion localDecls layouts place = false := by
      simp [placeTouchesUnion_nil_proj]) :
    evalRvalue locals (.wrapUnsafeBinder (.copy place) ty) mem localDecls layouts =
      .ok v locals mem := by
  have hNoDeref := readPlaceState_ok_noDeref hRead
  have hOp := readPlaceState_below_evalOperand_copy hRel hRead mem.borrows mem.globals layouts
    mem.callerLocals localDecls hNoUnion
  obtain ⟨loc, proj⟩ := place
  unfold evalRvalue
  simp only [hOp, hValid]
  cases proj with
  | nil => rfl
  | cons a rest =>
    cases a with
    | deref => simp [projectionHasDeref] at hNoDeref
    | _ => rfl

/-- **`WrapUnsafeBinder` (identity) refines Trusted**: when the binder type is the operand type,
Anneal's result is the operand value, exactly Trusted's `evalRvalue` result. -/
theorem evalWrapUnsafeBinder_identity_refines_evalRvalue {slots : List LocalSlotState}
    {locals : List LocalSlot} {place : Place} {v out : Value} {wf : Value → Bool}
    {range? : Option (ScalarValidRange × Nat)} (hRel : SlotsRefine SlotBelow slots locals)
    (hRead : readPlaceState slots place = .ok v)
    (h : evalWrapUnsafeBinder wf false range? v = some out) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hValid : validateLoadedValue layouts localDecls (.copy place) v = true)
    (hNoUnion : placeTouchesUnion localDecls layouts place = false := by
      simp [placeTouchesUnion_nil_proj]) :
    out = v ∧
      evalRvalue locals (.wrapUnsafeBinder (.copy place) ty) mem localDecls layouts =
        .ok out locals mem := by
  obtain ⟨_, hCase⟩ := evalWrapUnsafeBinder_preserves h locals ty
  rcases hCase with ⟨_, rfl⟩ | ⟨hW, _⟩
  · exact ⟨rfl,
      evalRvalue_wrapUnsafeBinder_copy hRel hRead ty mem localDecls layouts hValid hNoUnion⟩
  · nomatch hW

/-- **Documented representation divergence of `WrapUnsafeBinder`**: wrapping into a distinct
binder struct type, Anneal builds the one-field struct `.aggregate 0 [v]` (whose field `0` reads
back `v`), whereas Trusted's `evalRvalue` represents the binder value by the operand value `v`
itself. -/
theorem evalWrapUnsafeBinder_wrap_vs_evalRvalue {slots : List LocalSlotState}
    {locals : List LocalSlot} {place : Place} {v out : Value} {wf : Value → Bool}
    {range? : Option (ScalarValidRange × Nat)} (hRel : SlotsRefine SlotBelow slots locals)
    (hRead : readPlaceState slots place = .ok v)
    (h : evalWrapUnsafeBinder wf true range? v = some out) (ty : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hValid : validateLoadedValue layouts localDecls (.copy place) v = true)
    (hNoUnion : placeTouchesUnion localDecls layouts place = false := by
      simp [placeTouchesUnion_nil_proj]) :
    out = .aggregate 0 [v] ∧ evalValueProjRead locals out [.field 0 ty] = .ok v ∧
      evalRvalue locals (.wrapUnsafeBinder (.copy place) ty) mem localDecls layouts =
        .ok v locals mem := by
  obtain ⟨_, hCase⟩ := evalWrapUnsafeBinder_preserves h locals ty
  rcases hCase with ⟨hW, _⟩ | ⟨_, rfl, hField⟩
  · nomatch hW
  · exact ⟨rfl, hField,
      evalRvalue_wrapUnsafeBinder_copy hRel hRead ty mem localDecls layouts hValid hNoUnion⟩

/-! ## Section 3: Multi-block terminator CFG execution -/

/-- `SwitchTargets` of a lowered `SwitchInt` (`ir.rs`): parallel value/target lists and the
`otherwise` target. -/
structure LSwitchTargets : Type where
  values : List Nat
  targets : List Nat
  otherwise : Nat

/-- `SwitchTargets::target_for_value`: the target of the first matching value, else
`otherwise` (`zip` stops at the shorter list). -/
def targetForValue : List Nat → List Nat → Nat → Nat → Nat
  | x :: xs, t :: ts, otherwise, v => if v = x then t else targetForValue xs ts otherwise v
  | _, _, otherwise, _ => otherwise

/-- **`evalSwitchTargets_eq_lookupSwitchTarget`**: Anneal's switch target selection agrees
exactly with Trusted's `lookupSwitchTarget` on the zipped branch list. -/
theorem evalSwitchTargets_eq_lookupSwitchTarget :
    ∀ (values targets : List Nat) (otherwise v : Nat),
      targetForValue values targets otherwise v =
        lookupSwitchTarget v (values.zip targets) otherwise
  | [], _, _, _ => by cases ‹List Nat› <;> rfl
  | _ :: _, [], _, _ => rfl
  | x :: xs, t :: ts, otherwise, v => by
    simp only [targetForValue, List.zip_cons_cons, lookupSwitchTarget]
    rcases beq_cases v x with ⟨hB, hE⟩ | ⟨hB, hE⟩
    · rw [hB]
      simp [hE]
    · rw [hB]
      simp only [hE, ↓reduceIte]
      exact evalSwitchTargets_eq_lookupSwitchTarget xs ts otherwise v

/-- The type of a `SwitchInt` discriminant (`discr_ty`): `bool`, `char`, or an integer of
`bytes` bytes. -/
inductive SwitchTy : Type where
  | bool : SwitchTy
  | char : SwitchTy
  | int (bytes : Nat) : SwitchTy

/-- The byte width of a switch discriminant type (`Value.scalar`'s `sizeBytes`). -/
def SwitchTy.bytes : SwitchTy → Nat
  | .bool => 1
  | .char => 4
  | .int n => n

/-- `Ty::is_valid_scalar_bits` for a switch discriminant type: `0`/`1` for `bool`, a Unicode
scalar value for `char`, and a bit pattern of the integer's width (`A3`: never truncated). -/
def SwitchTy.validBits : SwitchTy → Nat → Bool
  | .bool, b => decide (b ≤ 1)
  | .char, b => isValidUnicodeScalar b
  | .int n, b => decide (b < 2 ^ (8 * n))

/-- A lowered terminator (`LoweredTerminator` in `cfg.rs`). `SwitchInt` carries its discriminant
type; `Assert` carries the places its panic message reads; `Call` carries the type of its
destination. -/
inductive LTerminator : Type where
  | goto (target : Nat) : LTerminator
  | switchInt (discr : Operand) (discrTy : SwitchTy) (targets : LSwitchTargets) : LTerminator
  | return_ : LTerminator
  | unreachable : LTerminator
  | drop (place : Place) (target : Nat) (unwind : UnwindAction) : LTerminator
  | assert (cond : Operand) (expected : Bool) (msg : List Place) (target : Nat)
      (unwind : UnwindAction) : LTerminator
  | call (func : Operand) (args : List Operand) (destination : Place) (destTy : Ty)
      (target : Option Nat) (unwind : UnwindAction) : LTerminator
  | unwindResume : LTerminator
  | unwindTerminate : LTerminator

/-- A lowered basic block (`LoweredBasicBlock`): its statements, terminator, and whether it is a
cleanup block. -/
structure LBlock : Type where
  statements : List Statement
  terminator : LTerminator
  isCleanup : Bool

/-- A lowered body's basic blocks (`LoweredBody`). -/
structure LBody : Type where
  blocks : List LBlock

/-- Outcome of a callee reported by the call handler (`CallOutcome`). -/
inductive CallOutcome : Type where
  | ret (v : Value) : CallOutcome
  | panic : CallOutcome

/-- The frame part of `check_place_access` (`prepare_place_access`), which does not depend on
declared types: the root local exists and is live (`DeadLocal`), and every `Index` operand local
holds an initialized scalar (the index pre-read `read_index_local`: `DeadLocal` /
`UninitializedLocal`). The typed part (the declared place type, `usize` index locals, and
`validate_projection_tail` with the read index values) is `CfgEnv.placeAccessOk`. -/
def placeFrameAccessOk (slots : List LocalSlotState) (place : Place) : Bool :=
  (match slots[place.local_]? with
   | some .dead => false
   | some _ => true
   | none => false) &&
  place.projection.all (fun e =>
    match e with
    | .index i =>
      match slots[i]? with
      | some (.init (.scalar _)) => true
      | _ => false
    | _ => true)

/-- The value-dependent part of `check_place_access` (`prepare_place_access`): no `Deref`
(`UnsupportedPlaceProjection`), the frame check `placeFrameAccessOk` (a live root local and
readable `Index` operand locals), and the runtime value/shell projection check
`check_slot_projection` (`checkPlaceSlotOk`: active variants, field bounds, and dynamic array
bounds on initialized arrays; anything below an uninitialized part). The type-directed part (the
declared place type and `validate_projection_tail`) is `CfgEnv.placeAccessOk`. -/
def placeRuntimeAccessOk (slots : List LocalSlotState) (place : Place) : Bool :=
  !projectionHasDeref place.projection && placeFrameAccessOk slots place &&
    checkPlaceSlotOk slots place

/-- `placeRuntimeAccessOk` spelled out. -/
theorem placeRuntimeAccessOk_iff {slots : List LocalSlotState} {place : Place} :
    placeRuntimeAccessOk slots place = true ↔
      projectionHasDeref place.projection = false ∧ placeFrameAccessOk slots place = true ∧
        checkPlaceSlotOk slots place = true := by
  unfold placeRuntimeAccessOk
  cases projectionHasDeref place.projection <;> cases placeFrameAccessOk slots place <;>
    cases checkPlaceSlotOk slots place <;> simp

/-- The environment of CFG evaluation: layouts and globals for constants, the boundary
well-formedness check `check_value_well_formed` (with the inhabitedness of the return type
folded into `retOk`), the type-directed part of the place-access check of `Drop`/`Call`
destinations (`check_place_access`; its value-dependent part is the concrete
`placeRuntimeAccessOk`), the arity function of shell writes, the statement evaluator
(`eval_lowered_statement` over a block's statements), the call handler (`none`:
`UnsupportedCall`), and `Ty::is_inhabited_for` (a returning `Call` needs an inhabited
destination type). -/
structure CfgEnv : Type where
  layouts : LayoutTable
  globals : List CapturedAllocation
  wf : Value → Bool
  retOk : Value → Bool
  placeAccessOk : List LocalSlotState → Place → Bool
  arityOf : Ty → VariantIdx → Bool → Option Nat
  evalStmts : List Statement → List LocalSlotState → Option (List LocalSlotState)
  handler : Option (Nat → Value → List Value → Option CallOutcome)
  inhabited : Ty → Bool := fun _ => true

/-- The next control-flow step after a terminator (`CfgStep`): continue at a block with the new
frame and unwinding state (`some bb` while unwinding a panic raised in `bb`), or finish. -/
inductive CfgStep : Type where
  | goto (bb : Nat) (slots : List LocalSlotState) (unwinding : Option Nat) : CfgStep
  | returned (v : Value) : CfgStep
  | panicked (bb : Nat) : CfgStep
  | terminated (bb : Nat) : CfgStep

/-- `check_unwind_action`: `Unreachable`/`Terminate` are always allowed; `Continue` and
`Cleanup` only outside cleanup blocks, and a `Cleanup` target must be an existing cleanup
block. -/
def unwindActionOk (body : LBody) (inCleanup : Bool) : UnwindAction → Bool
  | .unreachable => true
  | .terminate => true
  | .continue_ => !inCleanup
  | .cleanup t =>
    !inCleanup &&
      (match body.blocks[t]? with
       | some b => b.isCleanup
       | none => false)

/-- The edge check of every `Goto` step: the target exists and is a cleanup block iff the
evaluation is (now) unwinding (`InvalidBlock` / `InvalidEdge`). -/
def cfgGoto (body : LBody) (next : Nat) (slots : List LocalSlotState) (unwinding : Option Nat) :
    Option CfgStep :=
  match body.blocks[next]? with
  | some nb => if nb.isCleanup = unwinding.isSome then some (.goto next slots unwinding) else none
  | none => none

/-- `start_panic` for a panic raised in block `bb` under the unwind action `unwind`:
`Unreachable` is undefined behavior; `Terminate` aborts; `Continue` unwinds out of the body;
`Cleanup(t)` starts unwinding at `t`; unwinding again while unwinding is `InvalidUnwind`. -/
def startPanic (body : LBody) (bb : Nat) (unwind : UnwindAction) (slots : List LocalSlotState)
    (unwinding : Option Nat) : Option CfgStep :=
  match unwind with
  | .unreachable => none
  | .terminate => some (.terminated bb)
  | .continue_ => if unwinding.isSome then none else some (.panicked bb)
  | .cleanup t => if unwinding.isSome then none else cfgGoto body t slots (some bb)

/-- Evaluates a list of operands left to right (`eval_operand` for call arguments). -/
def evalOperandsState (layouts : LayoutTable) (globals : List CapturedAllocation) :
    List LocalSlotState → List Operand → Option (List Value × List LocalSlotState)
  | slots, [] => some ([], slots)
  | slots, op :: ops =>
    match evalOperandState slots op layouts globals with
    | (.ok v, slots') =>
      match evalOperandsState layouts globals slots' ops with
      | some (vs, slots'') => some (v :: vs, slots'')
      | none => none
    | _ => none

/-- `eval_lowered_terminator`: evaluates the terminator of block `bb` (whose statements have
run) in `slots` and unwinding mode `unwinding`. The block must exist and be a cleanup block iff
the evaluation is unwinding. `none` is an error (undefined behavior, an ill-formed body, or an
unsupported call). -/
def evalLoweredTerminator (env : CfgEnv) (body : LBody) (bb : Nat)
    (slots : List LocalSlotState) (unwinding : Option Nat) : Option CfgStep :=
  match body.blocks[bb]? with
  | none => none
  | some block =>
    if block.isCleanup ≠ unwinding.isSome then none else
    match block.terminator with
    | .goto t => cfgGoto body t slots unwinding
    | .switchInt discr dty targets =>
      if targets.values.length = targets.targets.length ∧ targets.values.Nodup ∧
          ∀ x ∈ targets.values, dty.validBits x = true then
        match evalOperandState slots discr env.layouts env.globals with
        | (.ok (.scalar sc), slots') =>
          if sc.sizeBytes = dty.bytes ∧ dty.validBits sc.bits = true then
            cfgGoto body (targetForValue targets.values targets.targets targets.otherwise sc.bits)
              slots' unwinding
          else none
        | _ => none
      else none
    | .return_ =>
      if block.isCleanup then none else
      match readPlaceState slots ⟨0, []⟩ with
      | .ok v => if env.retOk v then some (.returned v) else none
      | _ => none
    | .unreachable => none
    | .drop place target unwind =>
      if placeRuntimeAccessOk slots place ∧ env.placeAccessOk slots place ∧
          unwindActionOk body block.isCleanup unwind then
        cfgGoto body target slots unwinding
      else none
    | .assert cond expected msg target unwind =>
      match evalOperandState slots cond env.layouts env.globals with
      | (.ok (.scalar sc), slots') =>
        if sc.sizeBytes = 1 ∧ sc.bits ≤ 1 then
          if ((sc.bits == 1) == expected) = true then
            if unwindActionOk body block.isCleanup unwind then cfgGoto body target slots' unwinding
            else none
          else
            if msg.all (fun p => match readPlaceState slots' p with
                | .ok v => env.wf v
                | _ => false) then
              startPanic body bb unwind slots' unwinding
            else none
        else none
      | _ => none
    | .call func args destination destTy target unwind =>
      match evalOperandState slots func env.layouts env.globals with
      | (.ok fv, slots1) =>
        if !env.wf fv then none else
        match evalOperandsState env.layouts env.globals slots1 args with
        | some (avs, slots2) =>
          if !(avs.all env.wf && placeRuntimeAccessOk slots2 destination &&
              env.placeAccessOk slots2 destination) then none else
          if target.isSome && !env.inhabited destTy then none else
          match env.handler with
          | none => none
          | some h =>
            match h bb fv avs with
            | some (.ret rv) =>
              if !unwindActionOk body block.isCleanup unwind then none else
              match target with
              | none => none
              | some t =>
                if !env.wf rv then none else
                match writePlaceState env.arityOf slots2 destination destTy rv with
                | .ok slots3 => cfgGoto body t slots3 unwinding
                | _ => none
            | some .panic => startPanic body bb unwind slots2 unwinding
            | none => none
        | none => none
      | _ => none
    | .unwindResume =>
      match unwinding with
      | some pbb => some (.panicked pbb)
      | none => none
    | .unwindTerminate =>
      match unwinding with
      | some pbb => some (.terminated pbb)
      | none => none

/-- Outcome of a fuel-bounded CFG evaluation (`CfgEvalOutcome`). -/
inductive CfgOutcome : Type where
  | returned (v : Value) : CfgOutcome
  | panicked (bb : Nat) : CfgOutcome
  | terminated (bb : Nat) : CfgOutcome
  | outOfFuel (bb : Nat) (slots : List LocalSlotState) (unwinding : Option Nat) : CfgOutcome

/-- `eval_cfg_in_state`'s loop: each unit of fuel runs one block's statements and then its
terminator; fuel `0` stops at the block that would run next. -/
def runLoweredCfgSteps (env : CfgEnv) (body : LBody) :
    Nat → Nat → List LocalSlotState → Option Nat → Option CfgOutcome
  | 0, bb, slots, unwinding => some (.outOfFuel bb slots unwinding)
  | fuel + 1, bb, slots, unwinding =>
    match body.blocks[bb]? with
    | none => none
    | some block =>
      match env.evalStmts block.statements slots with
      | none => none
      | some slots1 =>
        match evalLoweredTerminator env body bb slots1 unwinding with
        | none => none
        | some (.goto next slots' unwinding') =>
          runLoweredCfgSteps env body fuel next slots' unwinding'
        | some (.returned v) => some (.returned v)
        | some (.panicked b) => some (.panicked b)
        | some (.terminated b) => some (.terminated b)

/-- **Zero fuel**: no block runs; the evaluation stops where it is. -/
theorem runLoweredCfgSteps_zero_fuel (env : CfgEnv) (body : LBody) (bb : Nat)
    (slots : List LocalSlotState) (unwinding : Option Nat) :
    runLoweredCfgSteps env body 0 bb slots unwinding = some (.outOfFuel bb slots unwinding) := rfl

/-- **Fuel composition**: running with `n + k` fuel is running with `n` fuel and, if that ran out
of fuel, continuing with `k` more from where it stopped. -/
theorem runLoweredCfgSteps_add_fuel (env : CfgEnv) (body : LBody) :
    ∀ (n k bb : Nat) (slots : List LocalSlotState) (unwinding : Option Nat),
      runLoweredCfgSteps env body (n + k) bb slots unwinding =
        match runLoweredCfgSteps env body n bb slots unwinding with
        | some (.outOfFuel bb' slots' unwinding') =>
          runLoweredCfgSteps env body k bb' slots' unwinding'
        | r => r := by
  intro n
  induction n with
  | zero => intro k bb slots unwinding; simp [runLoweredCfgSteps]
  | succ n ih =>
    intro k bb slots unwinding
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [runLoweredCfgSteps]
    cases body.blocks[bb]? with
    | none => rfl
    | some block =>
      simp only
      cases env.evalStmts block.statements slots with
      | none => rfl
      | some slots1 =>
        simp only
        cases evalLoweredTerminator env body bb slots1 unwinding with
        | none => rfl
        | some step =>
          cases step with
          | goto next slots' unwinding' => exact ih k next slots' unwinding'
          | returned v => rfl
          | panicked b => rfl
          | terminated b => rfl

/-- **Fuel monotonicity**: once an evaluation finishes (returns, panics, or terminates), more
fuel gives the same outcome. -/
theorem runLoweredCfgSteps_mono (env : CfgEnv) (body : LBody) {n k bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {o : CfgOutcome}
    (h : runLoweredCfgSteps env body n bb slots unwinding = some o)
    (hDone : ∀ bb' slots' unwinding', o ≠ .outOfFuel bb' slots' unwinding') :
    runLoweredCfgSteps env body (n + k) bb slots unwinding = some o := by
  rw [runLoweredCfgSteps_add_fuel, h]
  cases o with
  | outOfFuel bb' slots' unwinding' => exact absurd rfl (hDone bb' slots' unwinding')
  | _ => rfl

/-! ### Section 3b: Refinement of Trusted's `evalTerminator` / `stepMirFn` -/

/-- The Trusted terminator a lowered terminator corresponds to (`Assert`'s panic message and
`Call`'s destination type are not part of Trusted's syntax). -/
def LTerminator.toTrusted : LTerminator → TerminatorKind
  | .goto t => .goto t
  | .switchInt discr _ targets =>
    .switchInt discr ⟨targets.values.zip targets.targets, targets.otherwise⟩
  | .return_ => .return_
  | .unreachable => .unreachable
  | .drop place t u => .drop place t u
  | .assert cond expected _ t u => .assert cond expected t u
  | .call func args dest _ t u => .call func args dest t u
  | .unwindResume => .unwindResume
  | .unwindTerminate => .unwindTerminate

/-- The terminators covered by the step refinement: all but `Call` (Anneal abstracts callees by a
handler while Trusted links captured callee bodies) and `Drop` (whose divergence is
`evalLoweredTerminator_drop_bare_divergence`); operands must not start with a `Deref`. -/
def LTerminator.Refinable : LTerminator → Prop
  | .goto _ => True
  | .switchInt discr _ _ => OperandNonDeref discr
  | .return_ => True
  | .unreachable => True
  | .drop _ _ _ => False
  | .assert cond _ _ _ _ => OperandNonDeref cond
  | .call .. => False
  | .unwindResume => True
  | .unwindTerminate => True

/-- A lowered body corresponds to a captured Trusted body: a runtime phase, the same layouts,
the same blocks (statement-free on both sides, so a block is its terminator), the same
terminators and cleanup flags, and refinable terminators. -/
structure BodyCorr (env : CfgEnv) (body : LBody) (cm : CapturedMir) : Prop where
  phase : ∀ tag, cm.phase ≠ .other tag
  layouts : cm.layouts = env.layouts
  block : ∀ (i : Nat) (b : LBlock), body.blocks[i]? = some b →
    b.statements = [] ∧ b.terminator.Refinable ∧
      ∃ span, cm.basicBlocks[i]? = some ⟨[], ⟨b.terminator.toTrusted, span⟩, b.isCleanup⟩

/-- **`StateCorr`**: the lowered state at block `bb` with frame `slots` corresponds to the Trusted
machine state `s`: `s` is at the start of `bb` (its terminator, since blocks are statement-free),
Anneal's frame is below Trusted's (`SlotBelow`: every Anneal read is a Trusted read), and `s`
runs the root body (no active callee, empty call stack) with Anneal's globals. -/
structure StateCorr (env : CfgEnv) (bb : Nat) (slots : List LocalSlotState) (s : MachineState) :
    Prop where
  block : s.frame.blockIdx = bb
  stmt : s.frame.stmtIdx = 0
  slots : SlotsRefine SlotBelow slots s.frame.locals
  callee : s.memory.activeCallee = none
  stack : s.memory.callStack = []
  globals : s.memory.globals = env.globals

/-- A Trusted transition that continues at `s'` (silently, or emitting a branch event). -/
def TrustedStep (node : MirStepNode) (s' : MachineState) : Prop :=
  node = .step s' ∨ ∃ tag, node = .emitStep (.event tag) s'

/-- Under `BodyCorr`/`StateCorr`, Trusted's `stepMirFn` at `s` evaluates the corresponding
terminator. -/
theorem stepMirFn_eq_evalTerminator {env : CfgEnv} {body : LBody} {cm : CapturedMir} {bb : Nat}
    {slots : List LocalSlotState} {s : MachineState} {b : LBlock} (hBody : BodyCorr env body cm)
    (hCorr : StateCorr env bb slots s) (hb : body.blocks[bb]? = some b) :
    ∃ span, stepMirFn cm s = evalTerminator s ⟨b.terminator.toTrusted, span⟩ (some cm) := by
  obtain ⟨_, _, span, hcm⟩ := hBody.block bb b hb
  refine ⟨span, ?_⟩
  unfold stepMirFn
  simp only [hCorr.callee, Option.getD_none]
  split
  · rename_i tag hP
    exact absurd hP (hBody.phase tag)
  · simp only [get?_eq_getElem?, hCorr.block, hcm, hCorr.stmt, List.getElem?_nil,
      length_eq_list_length, List.length_nil, BEq.rfl, ↓reduceIte]

/-- Inversion of `cfgGoto`. -/
theorem cfgGoto_eq_some {body : LBody} {t : Nat} {slots : List LocalSlotState}
    {unwinding : Option Nat} {step : CfgStep} (h : cfgGoto body t slots unwinding = some step) :
    step = .goto t slots unwinding := by
  unfold cfgGoto at h
  split at h
  · split at h
    · exact (Option.some.inj h).symm
    · nomatch h
  · nomatch h

/-- The Trusted successor of a jump to `t` with frame `locals'` stays in correspondence. -/
theorem StateCorr.jump {env : CfgEnv} {bb : Nat} {slots slots' : List LocalSlotState}
    {s : MachineState} (hCorr : StateCorr env bb slots s) (t : Nat) (locals' : List LocalSlot)
    (hRel : SlotsRefine SlotBelow slots' locals') :
    StateCorr env t slots' { s with frame := { blockIdx := t, stmtIdx := 0, locals := locals' } } :=
  ⟨rfl, rfl, hRel, hCorr.callee, hCorr.stack, hCorr.globals⟩

/-- **`evalLoweredTerminator_refines_trusted`**: under `BodyCorr` and `StateCorr`, every
successful lowered terminator step is matched by Trusted's `stepMirFn`: a jump is a Trusted
`.step`/`.emitStep` to a corresponding state (preserving `StateCorr` on `Goto`, `SwitchInt`,
`Assert`-pass, and `Assert` cleanup jumps), `Return` is Trusted's `.retNormal` of the same value,
and a panic that unwinds out of the body (or aborts) is Trusted's `.panic` (or `.abort`) outcome.
In particular Trusted never faults with `.ub` where Anneal succeeds. -/
theorem evalLoweredTerminator_refines_trusted {env : CfgEnv} {body : LBody} {cm : CapturedMir}
    {bb : Nat} {slots : List LocalSlotState} {unwinding : Option Nat} {s : MachineState}
    {step : CfgStep} (hBody : BodyCorr env body cm) (hCorr : StateCorr env bb slots s)
    (h : evalLoweredTerminator env body bb slots unwinding = some step) :
    match step with
    | .goto next slots' _ => ∃ s', TrustedStep (stepMirFn cm s) s' ∧ StateCorr env next slots' s'
    | .returned v => stepMirFn cm s = .retNormal v s.memory
    | .panicked _ => stepMirFn cm s = .retOutcome .panic
    | .terminated _ => stepMirFn cm s = .retOutcome .abort := by
  unfold evalLoweredTerminator at h
  cases hb : body.blocks[bb]? with
  | none => rw [hb] at h; nomatch h
  | some b =>
    rw [hb] at h
    simp only at h
    obtain ⟨_, hRef, _⟩ := hBody.block bb b hb
    obtain ⟨span, hStep⟩ := stepMirFn_eq_evalTerminator hBody hCorr hb
    rw [hStep]
    split at h
    · nomatch h
    · rename_i hClean
      cases hT : b.terminator with
      | goto t =>
        rw [hT] at h
        simp only at h
        obtain rfl := cfgGoto_eq_some h
        refine ⟨_, Or.inl ?_, hCorr.jump t s.frame.locals hCorr.slots⟩
        simp only [LTerminator.toTrusted, evalTerminator]
      | switchInt discr bytes targets =>
        rw [hT] at hRef
        rw [hT] at h
        simp only at h
        split at h
        · split at h
          · rename_i sc slots' hOp
            split at h
            · obtain rfl := cfgGoto_eq_some h
              obtain ⟨locals', hTOp, hRel⟩ := evalOperandState_below_refines slots slots'
                s.frame.locals discr (.scalar sc) s.memory.borrows env.globals env.layouts
                s.memory.callerLocals hCorr.slots hRef hOp
              refine ⟨_, Or.inr ⟨sc.bits, ?_⟩, hCorr.jump _ locals' hRel⟩
              simp only [LTerminator.toTrusted, evalTerminator, hBody.layouts, hCorr.globals,
                hTOp, evalSwitchTargets_eq_lookupSwitchTarget]
            · nomatch h
          · nomatch h
        · nomatch h
      | return_ =>
        rw [hT] at h
        simp only at h
        split at h
        · nomatch h
        · split at h
          · rename_i v hRead
            split at h
            · cases h
              obtain ⟨rootVal, hRoot, hProj⟩ := readPlaceState_below_refines hCorr.slots hRead
              simp only [readProjectedValue, ProjReadResult.ok.injEq] at hProj
              subst hProj
              simp only [LTerminator.toTrusted, evalTerminator, hRoot, hCorr.stack]
            · nomatch h
          · nomatch h
      | unreachable => rw [hT] at h; nomatch h
      | drop place t u => rw [hT] at hRef; exact absurd hRef id
      | assert cond expected msg t u =>
        rw [hT] at hRef
        rw [hT] at h
        simp only at h
        split at h
        · rename_i sc slots' hOp
          obtain ⟨locals', hTOp, hRel⟩ := evalOperandState_below_refines slots slots'
            s.frame.locals cond (.scalar sc) s.memory.borrows env.globals env.layouts
            s.memory.callerLocals hCorr.slots hRef hOp
          simp only [LTerminator.toTrusted, evalTerminator, hBody.layouts, hCorr.globals, hTOp]
          split at h
          · rename_i hBool
            obtain ⟨bits, sz⟩ := sc
            obtain ⟨_, hLe⟩ := hBool
            have hB01 : bits = 0 ∨ bits = 1 := by simp only at hLe; omega
            rcases hB01 with rfl | rfl <;> cases expected
            · -- `false` asserted to be `false`: the assertion passes
              rw [show (((0 : Nat) == 1) == false) = true from rfl] at h
              simp only [↓reduceIte] at h
              dsimp only
              split at h
              · obtain rfl := cfgGoto_eq_some h
                exact ⟨_, Or.inl rfl, hCorr.jump t locals' hRel⟩
              · nomatch h
            · -- `false` asserted to be `true`: the assertion fails
              rw [show (((0 : Nat) == 1) == true) = false from rfl] at h
              simp only [Bool.false_eq_true, ↓reduceIte] at h
              dsimp only
              split at h
              · cases u with
                | unreachable => simp [startPanic] at h
                | terminate =>
                  simp only [startPanic, Option.some.injEq] at h
                  subst h
                  simp [applyUnwindAction]
                | continue_ =>
                  simp only [startPanic] at h
                  split at h
                  · nomatch h
                  · cases h
                    simp [applyUnwindAction, hCorr.stack]
                | cleanup c =>
                  simp only [startPanic] at h
                  split at h
                  · nomatch h
                  · obtain rfl := cfgGoto_eq_some h
                    exact ⟨{ s with frame := { blockIdx := c, stmtIdx := 0, locals := locals' } },
                      Or.inl rfl, hCorr.jump c locals' hRel⟩
              · nomatch h
            · -- `true` asserted to be `false`: the assertion fails
              rw [show (((1 : Nat) == 1) == false) = false from rfl] at h
              simp only [Bool.false_eq_true, ↓reduceIte] at h
              dsimp only
              split at h
              · cases u with
                | unreachable => simp [startPanic] at h
                | terminate =>
                  simp only [startPanic, Option.some.injEq] at h
                  subst h
                  simp [applyUnwindAction]
                | continue_ =>
                  simp only [startPanic] at h
                  split at h
                  · nomatch h
                  · cases h
                    simp [applyUnwindAction, hCorr.stack]
                | cleanup c =>
                  simp only [startPanic] at h
                  split at h
                  · nomatch h
                  · obtain rfl := cfgGoto_eq_some h
                    exact ⟨{ s with frame := { blockIdx := c, stmtIdx := 0, locals := locals' } },
                      Or.inl rfl, hCorr.jump c locals' hRel⟩
              · nomatch h
            · -- `true` asserted to be `true`: the assertion passes
              rw [show (((1 : Nat) == 1) == true) = true from rfl] at h
              simp only [↓reduceIte] at h
              dsimp only
              split at h
              · obtain rfl := cfgGoto_eq_some h
                exact ⟨_, Or.inl rfl, hCorr.jump t locals' hRel⟩
              · nomatch h
          · nomatch h
        · nomatch h
      | call func args dest destTy t u => rw [hT] at hRef; exact absurd hRef id
      | unwindResume =>
        rw [hT] at h
        simp only at h
        split at h
        · cases h
          simp [LTerminator.toTrusted, evalTerminator, hCorr.stack]
        · nomatch h
      | unwindTerminate =>
        rw [hT] at h
        simp only at h
        split at h
        · cases h
          simp [LTerminator.toTrusted, evalTerminator]
        · nomatch h

/-- Trusted's reflexive-transitive closure of continuing steps (`.step` / `.emitStep`) of
`stepMirFn`: a Trusted execution prefix that never faults. -/
inductive TrustedRun (cm : CapturedMir) : MachineState → MachineState → Prop where
  | refl (s : MachineState) : TrustedRun cm s s
  | step {s s' s'' : MachineState} :
      TrustedStep (stepMirFn cm s) s' → TrustedRun cm s' s'' → TrustedRun cm s s''

/-- **`runLoweredCfgSteps_refines_trusted`**: under `BodyCorr` (with the empty statement list
evaluating to the identity) and `StateCorr`, every successful fuel-bounded lowered CFG run is
matched by a fault-free Trusted execution of `stepMirFn` (equivalently `stepMirState` on
`.running` states) that reaches a corresponding state when fuel runs out, Trusted's
`.retNormal` of the same value on `Return`, and Trusted's `.panic` / `.abort` outcome when a
panic unwinds out of the body or aborts. Trusted never faults with `.ub` along the way. -/
theorem runLoweredCfgSteps_refines_trusted {env : CfgEnv} {body : LBody} {cm : CapturedMir}
    (hBody : BodyCorr env body cm) (hStmts : ∀ slots, env.evalStmts [] slots = some slots) :
    ∀ (fuel bb : Nat) (slots : List LocalSlotState) (unwinding : Option Nat) (s : MachineState)
      (o : CfgOutcome), StateCorr env bb slots s →
      runLoweredCfgSteps env body fuel bb slots unwinding = some o →
      match o with
      | .outOfFuel bb' slots' _ => ∃ s', TrustedRun cm s s' ∧ StateCorr env bb' slots' s'
      | .returned v => ∃ s', TrustedRun cm s s' ∧ stepMirFn cm s' = .retNormal v s'.memory
      | .panicked _ => ∃ s', TrustedRun cm s s' ∧ stepMirFn cm s' = .retOutcome .panic
      | .terminated _ => ∃ s', TrustedRun cm s s' ∧ stepMirFn cm s' = .retOutcome .abort := by
  intro fuel
  induction fuel with
  | zero =>
    intro bb slots unwinding s o hCorr h
    simp only [runLoweredCfgSteps, Option.some.injEq] at h
    subst h
    exact ⟨s, .refl s, hCorr⟩
  | succ fuel ih =>
    intro bb slots unwinding s o hCorr h
    simp only [runLoweredCfgSteps] at h
    cases hb : body.blocks[bb]? with
    | none => rw [hb] at h; nomatch h
    | some block =>
      rw [hb] at h
      simp only at h
      obtain ⟨hNil, _, _⟩ := hBody.block bb block hb
      rw [hNil, hStmts] at h
      simp only at h
      cases hT : evalLoweredTerminator env body bb slots unwinding with
      | none => rw [hT] at h; nomatch h
      | some step =>
        rw [hT] at h
        have hRef := evalLoweredTerminator_refines_trusted hBody hCorr hT
        cases step with
        | goto next slots' unwinding' =>
          simp only at h hRef
          obtain ⟨s', hStep, hCorr'⟩ := hRef
          have hRest := ih next slots' unwinding' s' o hCorr' h
          cases o with
          | outOfFuel bb' slots'' _ =>
            obtain ⟨s'', hRun, hC⟩ := hRest
            exact ⟨s'', .step hStep hRun, hC⟩
          | returned v =>
            obtain ⟨s'', hRun, hC⟩ := hRest
            exact ⟨s'', .step hStep hRun, hC⟩
          | panicked b =>
            obtain ⟨s'', hRun, hC⟩ := hRest
            exact ⟨s'', .step hStep hRun, hC⟩
          | terminated b =>
            obtain ⟨s'', hRun, hC⟩ := hRest
            exact ⟨s'', .step hStep hRun, hC⟩
        | returned v =>
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨s, .refl s, hRef⟩
        | panicked b =>
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨s, .refl s, hRef⟩
        | terminated b =>
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨s, .refl s, hRef⟩

/-- Trusted's `stepMirState` on a running state is `stepMirFn`, so `TrustedRun` is also a
fault-free `stepMirState` execution. -/
theorem stepMirState_running (cm : CapturedMir) (s : MachineState) :
    stepMirState cm (.running s) = stepMirFn cm s := rfl

/-- `Unreachable` is undefined behavior in both semantics: Anneal's step fails and Trusted's
`evalTerminator` faults with `.ub`. -/
theorem evalLoweredTerminator_unreachable_ub {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {b : LBlock}
    (hb : body.blocks[bb]? = some b) (hT : b.terminator = .unreachable) (s : MachineState)
    (span : String) (cmOpt : Option CapturedMir) :
    evalLoweredTerminator env body bb slots unwinding = none ∧
      evalTerminator s ⟨.unreachable, span⟩ cmOpt = .fail .ub := by
  refine ⟨?_, rfl⟩
  unfold evalLoweredTerminator
  rw [hb]
  simp only [hT]
  split <;> rfl

/-- **Strict `SwitchInt` discriminant validation (`A3`)**: a discriminant value of the wrong
size or whose bits are not a valid bit pattern of the discriminant type (a `bool` other than
`0`/`1`, a `char` that is not a Unicode scalar value, or an out-of-width integer) makes the
terminator fail; it is never truncated into a branch. -/
theorem evalLoweredTerminator_switch_invalid_none {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots slots' : List LocalSlotState} {unwinding : Option Nat} {b : LBlock} {discr : Operand}
    {dty : SwitchTy} {targets : LSwitchTargets} {sc : ScalarInt}
    (hb : body.blocks[bb]? = some b) (hT : b.terminator = .switchInt discr dty targets)
    (hOp : evalOperandState slots discr env.layouts env.globals = (.ok (.scalar sc), slots'))
    (hBad : sc.sizeBytes ≠ dty.bytes ∨ dty.validBits sc.bits = false) :
    evalLoweredTerminator env body bb slots unwinding = none := by
  unfold evalLoweredTerminator
  rw [hb]
  simp only [hT]
  split
  · rfl
  · split
    · rw [hOp]
      simp only
      split
      · rename_i hOk
        rcases hBad with h | h
        · exact absurd hOk.1 h
        · rw [h] at hOk; exact absurd hOk.2 (by simp)
      · rfl
    · rfl

/-- `SwitchInt` with a target value that is not a valid bit pattern of the discriminant type
(or with duplicate values, or mismatched value/target lists) is an ill-formed terminator. -/
theorem evalLoweredTerminator_switch_bad_targets_none {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {b : LBlock} {discr : Operand}
    {dty : SwitchTy} {targets : LSwitchTargets}
    (hb : body.blocks[bb]? = some b) (hT : b.terminator = .switchInt discr dty targets)
    (hBad : targets.values.length ≠ targets.targets.length ∨ ¬ targets.values.Nodup ∨
      ∃ x ∈ targets.values, dty.validBits x = false) :
    evalLoweredTerminator env body bb slots unwinding = none := by
  unfold evalLoweredTerminator
  rw [hb]
  simp only [hT]
  split
  · rfl
  · split
    · rename_i hOk
      rcases hBad with h | h | ⟨x, hx, hv⟩
      · exact absurd hOk.1 h
      · exact absurd hOk.2.1 h
      · have := hOk.2.2 x hx
        rw [hv] at this
        nomatch this
    · rfl

/-- A `bool` switch never selects a branch from a non-boolean scalar: `SwitchTy.validBits .bool`
accepts exactly `0` and `1`. -/
theorem SwitchTy.validBits_bool (b : Nat) : SwitchTy.validBits .bool b = true ↔ b = 0 ∨ b = 1 := by
  simp only [SwitchTy.validBits, decide_eq_true_eq]
  omega

/-- A `char` switch accepts a scalar iff it is a valid Unicode scalar value (`< 0xD800` or in
`0xE000..=0x10FFFF`). -/
theorem SwitchTy.validBits_char_iff (b : Nat) :
    SwitchTy.validBits .char b = true ↔ b < 0xD800 ∨ (0xE000 ≤ b ∧ b ≤ 0x10FFFF) := by
  simp only [SwitchTy.validBits, isValidUnicodeScalar, Bool.or_eq_true, Bool.and_eq_true,
    Nat.ble_eq]
  omega

/-- **Every valid `SwitchInt` discriminant or target bit pattern fits in `8 * dty.bytes` bits**:
for `bool` (`1` byte), `char` (`4` bytes), and `int n` (`n` bytes), `dty.validBits b = true`
implies `b < 2 ^ (8 * dty.bytes)`. -/
theorem SwitchTy.validBits_lt_two_pow (dty : SwitchTy) (b : Nat)
    (h : dty.validBits b = true) : b < 2 ^ (8 * dty.bytes) := by
  cases dty with
  | bool =>
    rcases (SwitchTy.validBits_bool b).mp h with rfl | rfl <;> decide
  | char =>
    rcases (SwitchTy.validBits_char_iff b).mp h with h1 | ⟨_, h2⟩ <;>
      (simp only [SwitchTy.bytes]; omega)
  | int n =>
    simpa [SwitchTy.validBits, SwitchTy.bytes] using h

/-- **Failing `Assert` with an unreadable or ill-formed panic-message place fails closed**: if the
asserted condition evaluates to the unexpected boolean and some place `p ∈ msg` cannot be read or
holds an ill-formed value (`!env.wf v`), `evalLoweredTerminator` returns `none` instead of
panicking. -/
theorem evalLoweredTerminator_assert_bad_msg_none {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots slots' : List LocalSlotState} {unwinding : Option Nat} {b : LBlock}
    {cond : Operand} {expected : Bool} {msg : List Place} {target : Nat} {u : UnwindAction}
    {sc : ScalarInt} (hb : body.blocks[bb]? = some b)
    (hT : b.terminator = .assert cond expected msg target u)
    (hOp : evalOperandState slots cond env.layouts env.globals = (.ok (.scalar sc), slots'))
    (hFail : ((sc.bits == 1) == expected) = false) {p : Place} (hp : p ∈ msg)
    (hBad : match readPlaceState slots' p with | .ok v => env.wf v = false | _ => True) :
    evalLoweredTerminator env body bb slots unwinding = none := by
  have hAllFalse : msg.all (fun q => match readPlaceState slots' q with
      | .ok v => env.wf v
      | _ => false) = false := by
    cases hAll : msg.all (fun q => match readPlaceState slots' q with
        | .ok v => env.wf v
        | _ => false) with
    | false => rfl
    | true =>
      have hMem := List.all_eq_true.mp hAll p hp
      cases hR : readPlaceState slots' p with
      | ok v =>
        rw [hR] at hMem hBad
        dsimp only at hMem hBad
        rw [hBad] at hMem
        nomatch hMem
      | ub => rw [hR] at hMem; nomatch hMem
      | unsupported => rw [hR] at hMem; nomatch hMem
  unfold evalLoweredTerminator
  rw [hb]
  simp only [hT]
  split
  · rfl
  · rw [hOp]
    simp only
    split
    · simp only [hFail, Bool.false_eq_true, ↓reduceIte, hAllFalse]
    · rfl

/-- **Returning or cleanup-unwinding `Call` soundness (`evalLoweredTerminator_call_goto_sound`)**:
whenever a `Call` terminator steps via `.goto next slots3 unwinding'`, the callee operand and all
argument operands evaluated to well-formed values (`env.wf`), the destination place was accessible,
the call handler `fn` was invoked, and either:
- the callee returned `some (.ret rv)` with `env.wf rv = true`, `env.inhabited destTy = true`,
  `target = some next`, `unwinding' = unwinding`, and `writePlaceState` wrote `rv` into
  `destination` to produce `slots3`; or
- the callee panicked (`some .panic`) into `unwind = .cleanup next` from a non-unwinding state
  (`unwinding = none`, `unwinding' = some bb`) with `slots3 = slots2` unchanged. -/
theorem evalLoweredTerminator_call_goto_sound {env : CfgEnv} {body : LBody} {bb next : Nat}
    {slots slots3 : List LocalSlotState} {unwinding unwinding' : Option Nat} {b : LBlock}
    {func : Operand} {args : List Operand} {destination : Place} {destTy : Ty}
    {target : Option Nat} {unwind : UnwindAction}
    (hb : body.blocks[bb]? = some b)
    (hT : b.terminator = .call func args destination destTy target unwind)
    (h : evalLoweredTerminator env body bb slots unwinding =
      some (.goto next slots3 unwinding')) :
    ∃ fv slots1 avs slots2 fn,
      evalOperandState slots func env.layouts env.globals = (.ok fv, slots1) ∧
      env.wf fv = true ∧
      evalOperandsState env.layouts env.globals slots1 args = some (avs, slots2) ∧
      avs.all env.wf = true ∧
      placeRuntimeAccessOk slots2 destination = true ∧
      env.placeAccessOk slots2 destination = true ∧
      env.handler = some fn ∧
      ((∃ rv, fn bb fv avs = some (.ret rv) ∧
          env.inhabited destTy = true ∧
          unwindActionOk body b.isCleanup unwind = true ∧
          target = some next ∧
          env.wf rv = true ∧
          writePlaceState env.arityOf slots2 destination destTy rv = .ok slots3 ∧
          unwinding' = unwinding) ∨
        (fn bb fv avs = some .panic ∧
          unwinding = none ∧
          unwinding' = some bb ∧
          unwind = .cleanup next ∧
          slots3 = slots2)) := by
  unfold evalLoweredTerminator at h
  rw [hb] at h
  simp only [hT] at h
  split at h
  · nomatch h
  · split at h
    · rename_i fv slots1 hFunc
      split at h
      · nomatch h
      · rename_i hWfF
        have hWfF' : env.wf fv = true := by cases hW : env.wf fv <;> simp_all
        split at h
        · rename_i avs slots2 hArgs
          split at h
          · nomatch h
          · rename_i hArgsWf
            have hAllWf : avs.all env.wf = true ∧ placeRuntimeAccessOk slots2 destination = true ∧
                env.placeAccessOk slots2 destination = true := by
              cases h1 : avs.all env.wf <;> cases h2 : placeRuntimeAccessOk slots2 destination <;>
                cases h3 : env.placeAccessOk slots2 destination <;> simp_all
            split at h
            · nomatch h
            · rename_i hInhGuard
              split at h
              · nomatch h
              · rename_i fn hHandler
                refine ⟨fv, slots1, avs, slots2, fn, hFunc, hWfF', hArgs, hAllWf.1,
                  hAllWf.2.1, hAllWf.2.2, hHandler, ?_⟩
                split at h
                · rename_i rv hRet
                  split at h
                  · nomatch h
                  · rename_i hUnwOk
                    have hUnwOk' : unwindActionOk body b.isCleanup unwind = true := by
                      cases hU : unwindActionOk body b.isCleanup unwind <;> simp_all
                    split at h
                    · nomatch h
                    · have hInh' : env.inhabited destTy = true := by
                        cases hI : env.inhabited destTy <;> simp_all
                      split at h
                      · nomatch h
                      · rename_i hWfRv
                        have hWfRv' : env.wf rv = true := by cases hR : env.wf rv <;> simp_all
                        split at h
                        · rename_i slots3' hWrite
                          have hGoto := cfgGoto_eq_some h
                          injection hGoto with hNext hSlots hUnw
                          subst hNext hSlots hUnw
                          exact Or.inl ⟨rv, hRet, hInh', hUnwOk', rfl, hWfRv', hWrite, rfl⟩
                        · nomatch h
                · rename_i hPanic
                  cases unwind with
                  | unreachable => simp [startPanic] at h
                  | terminate => simp [startPanic] at h
                  | continue_ =>
                    simp only [startPanic] at h
                    split at h <;> nomatch h
                  | cleanup c =>
                    simp only [startPanic] at h
                    split at h
                    · nomatch h
                    · rename_i hNotUnw
                      have hUnwNone : unwinding = none := by
                        cases unwinding with
                        | none => rfl
                        | some _ => simp at hNotUnw
                      have hGoto := cfgGoto_eq_some h
                      injection hGoto with hNext hSlots hUnw
                      subst hNext hSlots hUnw
                      exact Or.inr ⟨hPanic, hUnwNone, rfl, rfl, rfl⟩
                · nomatch h
        · nomatch h
    · nomatch h

/-- A returning `Call` (`target = some _`) with an uninhabited destination type is an ill-formed
terminator (`eval_lowered_terminator` rejects it before consulting the call handler). -/
theorem evalLoweredTerminator_call_uninhabited_dest_none {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {b : LBlock} {func : Operand}
    {args : List Operand} {dest : Place} {destTy : Ty} {t : Nat} {u : UnwindAction}
    (hb : body.blocks[bb]? = some b) (hT : b.terminator = .call func args dest destTy (some t) u)
    (hInh : env.inhabited destTy = false) :
    evalLoweredTerminator env body bb slots unwinding = none := by
  unfold evalLoweredTerminator
  rw [hb]
  simp only [hT, Option.isSome_some, hInh, Bool.not_false, Bool.and_true, ↓reduceIte, ite_self]
  split
  · rfl
  · split
    · split
      · rfl
      · split <;> rfl
    · rfl

/-- An assertion that fails under `UnwindAction::Unreachable` is undefined behavior in both
semantics (Anneal's `UnwindIntoUnreachable`; Trusted's `applyUnwindAction` faults). -/
theorem assert_unreachable_unwind_ub (s : MachineState) (locals' : List LocalSlot) (body : LBody)
    (bb : Nat) (slots : List LocalSlotState) (unwinding : Option Nat) :
    startPanic body bb .unreachable slots unwinding = none ∧
      applyUnwindAction s locals' s.memory .unreachable = .faulted .ub := ⟨rfl, rfl⟩

/-- A place passing the frame access check names a live local of the frame. -/
theorem placeFrameAccessOk_live {slots : List LocalSlotState} {place : Place}
    (h : placeFrameAccessOk slots place = true) :
    ∃ st, slots[place.local_]? = some st ∧ st ≠ .dead := by
  cases hS : slots[place.local_]? with
  | none => simp [placeFrameAccessOk, hS] at h
  | some st =>
    cases st with
    | dead => simp [placeFrameAccessOk, hS] at h
    | uninit => exact ⟨_, rfl, by simp⟩
    | partialShell _ => exact ⟨_, rfl, by simp⟩
    | init _ => exact ⟨_, rfl, by simp⟩

/-- A place passing the frame access check reads every `Index` operand local as an initialized
scalar. -/
theorem placeFrameAccessOk_index {slots : List LocalSlotState} {place : Place}
    (h : placeFrameAccessOk slots place = true) {i : Local}
    (hIdx : .index i ∈ place.projection) :
    ∃ sc, slots[i]? = some (.init (.scalar sc)) := by
  unfold placeFrameAccessOk at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hI := h.2 _ hIdx
  simp only at hI
  split at hI
  · rename_i sc hSc
    exact ⟨sc, hSc⟩
  · nomatch hI

/-- The value-directed projection walk of `deinit_in_slot` over a `FieldSlot` (not the
type-directed `prepare_place_access` / `validate_projection_tail`; see `slotPlaceProjectionOk`):
- empty projection `[]` always succeeds;
- below `.uninit`, validates the remaining tail with `deinitTailOk` (no `Deref`, `Downcast`
  followed by `Field`, `Index` scalar local, static `ConstantIndex`/`Subslice` bounds);
- on an initialized aggregate `.init (.aggregate var vals)` or partial shell
  `.nested var adt disc fs`, validates active-variant matching (`var = 0` for `Field`, `var = v`
  for `Downcast(v)` + `Field`), field bounds (`idx < length`), and recurses into the child slot. -/
def slotProjectionAccessOk (locals : List LocalSlot) :
    FieldSlot → List ProjectionElem → Bool
  | _, [] => true
  | .uninit, p :: rest => deinitTailOk locals (p :: rest)
  | .init (.aggregate var vals), .field idx _ :: rest =>
    (var == 0) &&
      match vals[idx]? with
      | some fv => slotProjectionAccessOk locals (.init fv) rest
      | none => false
  | .init (.aggregate var vals), .downcast _ v :: .field idx _ :: rest =>
    (var == v) &&
      match vals[idx]? with
      | some fv => slotProjectionAccessOk locals (.init fv) rest
      | none => false
  | .nested var adt disc fs, .field idx _ :: rest =>
    (shellVariant ⟨var, adt, disc, fs⟩ == 0) &&
      match fs[idx]? with
      | some c => slotProjectionAccessOk locals c rest
      | none => false
  | .nested var adt disc fs, .downcast _ v :: .field idx _ :: rest =>
    (shellVariant ⟨var, adt, disc, fs⟩ == v) &&
      match fs[idx]? with
      | some c => slotProjectionAccessOk locals c rest
      | none => false
  | _, _ :: _ => false

/-- The value-directed path discipline of `deinit_in_slot` (`slotPlaceProjectionOk`): the root
local is live and its root slot satisfies `slotProjectionAccessOk` along `place.projection`
(active variants, in-bounds fields, well-formed tails below uninitialized parts, and no array
projections on initialized values because arrays have no per-element shells). For the runtime
value/shell projection check `check_slot_projection` that `prepare_place_access` runs alongside
`validate_projection_tail` (which also accepts in-bounds array projections on initialized arrays
and any tail below `.uninit`), see `checkSlotProjectionOk` / `checkPlaceSlotOk` below. -/
def slotPlaceProjectionOk (slots : List LocalSlotState) (place : Place) : Bool :=
  match slots[place.local_]? with
  | none | some .dead => false
  | some st =>
    slotProjectionAccessOk (slotsToTrustedLocals slots) (slotStateToFieldSlot st) place.projection

/-- `slotProjectionAccessOk` paths contain no `Deref`. -/
theorem slotProjectionAccessOk_noDeref (locals : List LocalSlot) (slot : FieldSlot)
    (p : List ProjectionElem) (h : slotProjectionAccessOk locals slot p = true) :
    projectionHasDeref p = false := by
  fun_induction slotProjectionAccessOk locals slot p with
  | case1 => rfl
  | case2 p rest => exact deinitTailOk_noDeref locals (p :: rest) h
  | case3 var vals idx ty rest ih =>
    simp only [Bool.and_eq_true] at h
    split at h
    · rename_i fv _
      simpa [projectionHasDeref] using ih fv h.2
    · nomatch h.2
  | case4 var vals nm v idx ty rest ih =>
    simp only [Bool.and_eq_true] at h
    split at h
    · rename_i fv _
      simpa [projectionHasDeref] using ih fv h.2
    · nomatch h.2
  | case5 var adt disc fs idx ty rest ih =>
    simp only [Bool.and_eq_true] at h
    split at h
    · rename_i c _
      simpa [projectionHasDeref] using ih c h.2
    · nomatch h.2
  | case6 var adt disc fs nm v idx ty rest ih =>
    simp only [Bool.and_eq_true] at h
    split at h
    · rename_i c _
      simpa [projectionHasDeref] using ih c h.2
    · nomatch h.2
  | case7 => nomatch h

/-- **Concrete `slotPlaceProjectionOk` rejects `Deref` (`UnsupportedPlaceProjection`)**. -/
theorem slotPlaceProjectionOk_noDeref {slots : List LocalSlotState} {place : Place}
    (h : slotPlaceProjectionOk slots place = true) :
    projectionHasDeref place.projection = false := by
  unfold slotPlaceProjectionOk at h
  split at h
  · nomatch h
  · nomatch h
  · exact slotProjectionAccessOk_noDeref _ _ _ h

/-- **Concrete `slotPlaceProjectionOk` rejects inactive `Downcast` variants (`B1`)**:
projecting `.downcast nm dv :: .field idx ty :: rest` on an initialized aggregate of variant `v`
or a partial shell narrowed to variant `v` with `v ≠ dv` fails (`false`,
`InactiveVariantProjection`). -/
theorem slotPlaceProjectionOk_inactive_variant_false (slots : List LocalSlotState) (loc : Local)
    {v dv idx : Nat} (nm : Option String) (ty : Ty) (rest : List ProjectionElem) (hNe : v ≠ dv) :
    (∀ vals, slots[loc]? = some (.init (.aggregate v vals)) →
      slotPlaceProjectionOk slots ⟨loc, .downcast nm dv :: .field idx ty :: rest⟩ = false) ∧
    (∀ sh, slots[loc]? = some (.partialShell sh) → shellVariant sh = v →
      slotPlaceProjectionOk slots ⟨loc, .downcast nm dv :: .field idx ty :: rest⟩ = false) := by
  refine ⟨fun vals hRoot => ?_, fun sh hRoot hVar => ?_⟩
  · simp [slotPlaceProjectionOk, hRoot, slotStateToFieldSlot, slotProjectionAccessOk, hNe]
  · obtain ⟨var, adt, disc, fs⟩ := sh
    simp [slotPlaceProjectionOk, hRoot, slotStateToFieldSlot, PartialAggregate.toFieldSlot,
      slotProjectionAccessOk, hVar, hNe]

/-- **Concrete `slotPlaceProjectionOk` rejects out-of-bounds `Field` projections (`B1`)**. -/
theorem slotPlaceProjectionOk_field_oob_false (slots : List LocalSlotState) (loc : Local)
    {vals : List Value} {idx : Nat} (ty : Ty) (rest : List ProjectionElem)
    (hRoot : slots[loc]? = some (.init (.aggregate 0 vals))) (hOob : vals.length ≤ idx) :
    slotPlaceProjectionOk slots ⟨loc, .field idx ty :: rest⟩ = false := by
  have hNone : vals[idx]? = none := List.getElem?_eq_none hOob
  simp [slotPlaceProjectionOk, hRoot, slotStateToFieldSlot, slotProjectionAccessOk, hNone]

/-- Every successful `deinitFieldSlot` path satisfies `slotProjectionAccessOk` (`check_place_access`
and `deinit_in_slot` enforce the exact same active-variant, field-bounds, and `.uninit` tail
invariants). -/
theorem slotProjectionAccessOk_of_deinitFieldSlot (ts : Bool) (locals : List LocalSlot)
    (slot : FieldSlot) (p : List ProjectionElem) (slot' : FieldSlot)
    (h : deinitFieldSlot ts locals slot p = some slot') :
    slotProjectionAccessOk locals slot p = true := by
  fun_induction deinitFieldSlot ts locals slot p generalizing slot' with
  | case1 => rfl
  | case2 p rest hT => exact hT
  | case3 => nomatch h
  | case4 var vals idx ty rest ih =>
    obtain ⟨hV, c, c', hc, hcc, _⟩ := deinitShellStep_eq_some h
    have hV' : var = 0 := hV
    subst hV'
    obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
    simp only [slotProjectionAccessOk, BEq.rfl, Bool.true_and, hcv]
    exact ih (.init cv) c' hcc
  | case5 var vals nm v idx ty rest ih =>
    obtain ⟨hV, c, c', hc, hcc, _⟩ := deinitShellStep_eq_some h
    have hV' : var = v := hV
    subst hV'
    obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
    simp only [slotProjectionAccessOk, BEq.rfl, Bool.true_and, hcv]
    exact ih (.init cv) c' hcc
  | case6 var adt disc fs idx ty rest ih =>
    obtain ⟨hV, c, c', hc, hcc, _⟩ := deinitShellStep_eq_some h
    have hV' : shellVariant ⟨var, adt, disc, fs⟩ = 0 := hV
    simp only [slotProjectionAccessOk, hV', BEq.rfl, Bool.true_and, hc]
    exact ih c c' hcc
  | case7 var adt disc fs nm v idx ty rest ih =>
    obtain ⟨hV, c, c', hc, hcc, _⟩ := deinitShellStep_eq_some h
    have hV' : shellVariant ⟨var, adt, disc, fs⟩ = v := hV
    simp only [slotProjectionAccessOk, hV', BEq.rfl, Bool.true_and, hc]
    exact ih c c' hcc
  | case8 => nomatch h

/-- **Every place that `evalDeinitPlace` can deinitialize passes `slotPlaceProjectionOk`**. -/
theorem slotPlaceProjectionOk_of_evalDeinitPlace {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} (h : evalDeinitPlace ts slots place = some slots') :
    slotPlaceProjectionOk slots place = true := by
  obtain ⟨st, hSt, hLive, slot', hD, _⟩ := evalDeinitPlace_eq_some h
  unfold slotPlaceProjectionOk
  rw [hSt]
  cases st with
  | dead => exact absurd rfl hLive
  | uninit => exact slotProjectionAccessOk_of_deinitFieldSlot ts _ _ _ _ hD
  | init _ => exact slotProjectionAccessOk_of_deinitFieldSlot ts _ _ _ _ hD
  | partialShell _ => exact slotProjectionAccessOk_of_deinitFieldSlot ts _ _ _ _ hD

/-- **Every place that `evalDeinitPlace` can deinitialize passes `placeFrameAccessOk` (`B4`)**:
its root local is live and every `Index` operand local holds an initialized scalar. -/
theorem placeFrameAccessOk_of_evalDeinitPlace {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} (h : evalDeinitPlace ts slots place = some slots') :
    placeFrameAccessOk slots place = true := by
  have hIdx := evalDeinitPlace_indexLocalsOk h
  obtain ⟨st, hSt, hLive, _⟩ := evalDeinitPlace_eq_some h
  unfold placeFrameAccessOk
  rw [Bool.and_eq_true]
  refine ⟨?_, hIdx⟩
  rw [hSt]
  cases st with
  | dead => exact absurd rfl hLive
  | _ => rfl

/-- Every path accepted by `slotProjectionAccessOk` (`deinit_in_slot`) is also accepted by
`checkSlotProjectionOk` (`check_slot_projection`). -/
theorem checkSlotProjectionOk_of_slotProjectionAccessOk (locals : List LocalSlot)
    (slot : FieldSlot) (p : List ProjectionElem)
    (h : slotProjectionAccessOk locals slot p = true) :
    checkSlotProjectionOk locals slot p = true := by
  fun_induction slotProjectionAccessOk locals slot p with
  | case1 s =>
    cases s with
    | uninit => rfl
    | init v => rfl
    | nested var adt disc fs => rfl
  | case2 p rest => rfl
  | case3 var vals idx ty rest ih =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, hField⟩
    cases hfv : vals[idx]? with
    | none => rw [hfv] at hField; nomatch hField
    | some fv =>
      rw [hfv] at hField
      have hSub := ih fv hField
      unfold checkSlotProjectionOk at hSub ⊢
      rw [evalValueProjRead_aggregate_field, hfv]
      exact hSub
  | case4 var vals nm v idx ty rest ih =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, hField⟩
    cases hfv : vals[idx]? with
    | none => rw [hfv] at hField; nomatch hField
    | some fv =>
      rw [hfv] at hField
      have hSub := ih fv hField
      unfold checkSlotProjectionOk at hSub ⊢
      rw [evalValueProjRead_aggregate_downcast_field]
      simp only [↓reduceIte, hfv]
      exact hSub
  | case5 var adt disc fs idx ty rest ih =>
    simp only [Bool.and_eq_true] at h
    rcases h with ⟨hV, hField⟩
    cases hc : fs[idx]? with
    | none => rw [hc] at hField; nomatch hField
    | some c =>
      rw [hc] at hField
      simp only [checkSlotProjectionOk, hV, Bool.true_and, hc]
      exact ih c hField
  | case6 var adt disc fs nm v idx ty rest ih =>
    simp only [Bool.and_eq_true] at h
    rcases h with ⟨hV, hField⟩
    cases hc : fs[idx]? with
    | none => rw [hc] at hField; nomatch hField
    | some c =>
      rw [hc] at hField
      simp only [checkSlotProjectionOk, hV, Bool.true_and, hc]
      exact ih c hField
  | case7 => nomatch h

/-- Every place accepted by `slotPlaceProjectionOk` passes `checkPlaceSlotOk`. -/
theorem checkPlaceSlotOk_of_slotPlaceProjectionOk {slots : List LocalSlotState} {place : Place}
    (h : slotPlaceProjectionOk slots place = true) :
    checkPlaceSlotOk slots place = true := by
  unfold slotPlaceProjectionOk at h
  unfold checkPlaceSlotOk
  split at h
  · nomatch h
  · nomatch h
  · exact checkSlotProjectionOk_of_slotProjectionAccessOk _ _ _ h

/-- Every place deinitialized by `evalDeinitPlace` passes `checkPlaceSlotOk`. -/
theorem checkPlaceSlotOk_of_evalDeinitPlace {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} (h : evalDeinitPlace ts slots place = some slots') :
    checkPlaceSlotOk slots place = true :=
  checkPlaceSlotOk_of_slotPlaceProjectionOk (slotPlaceProjectionOk_of_evalDeinitPlace h)

/-- **`checkPlaceSlotOk` rejects inactive `Downcast` variants (`B1`/`B4`)**: projecting
`.downcast nm dv :: .field idx ty :: rest` on an initialized aggregate of variant `v` or a partial
shell narrowed to variant `v` with `v ≠ dv` fails (`false`, `InactiveVariantProjection`),
matching `check_slot_projection` in `rvalue.rs:6590, 6806`. -/
theorem checkPlaceSlotOk_inactive_variant_false (slots : List LocalSlotState) (loc : Local)
    {v dv idx : Nat} (nm : Option String) (ty : Ty) (rest : List ProjectionElem) (hNe : v ≠ dv) :
    (∀ vals, slots[loc]? = some (.init (.aggregate v vals)) →
      checkPlaceSlotOk slots ⟨loc, .downcast nm dv :: .field idx ty :: rest⟩ = false) ∧
    (∀ sh, slots[loc]? = some (.partialShell sh) → shellVariant sh = v →
      checkPlaceSlotOk slots ⟨loc, .downcast nm dv :: .field idx ty :: rest⟩ = false) := by
  refine ⟨fun vals hRoot => ?_, fun sh hRoot hVar => ?_⟩
  · simp [checkPlaceSlotOk, hRoot, slotStateToFieldSlot, checkSlotProjectionOk,
      evalValueProjRead_aggregate_downcast_field, hNe]
  · obtain ⟨var, adt, disc, fs⟩ := sh
    simp [checkPlaceSlotOk, hRoot, slotStateToFieldSlot, PartialAggregate.toFieldSlot,
      checkSlotProjectionOk, hVar, hNe]

/-- **`checkPlaceSlotOk` checks dynamic `Index` bounds on initialized arrays (`B1`/`B4`)**: unlike
`slotPlaceProjectionOk` (which rejects all array projections on `.init` because arrays have no
shells), `checkPlaceSlotOk` on an initialized array `slots[loc]? = some (.init (.aggregate 0 elems))`
and an initialized scalar index local `slots[i]? = some (.init (.scalar sc))` succeeds iff
`sc.bits < elems.length` (`IndexOutOfBounds` otherwise). -/
theorem checkPlaceSlotOk_array_index_eq {slots : List LocalSlotState} {loc i : Local}
    {elems : List Value} {sc : ScalarInt}
    (hArr : slots[loc]? = some (.init (.aggregate 0 elems)))
    (hIdx : slots[i]? = some (.init (.scalar sc))) :
    checkPlaceSlotOk slots ⟨loc, [.index i]⟩ = decide (sc.bits < elems.length) := by
  have hTIdx : get? (slotsToTrustedLocals slots) i = some (.init (.scalar sc)) := by
    apply (get?_slotsToTrustedLocals_scalar_iff slots i sc).mpr
    simpa [get?_eq_getElem?] using hIdx
  simp only [checkPlaceSlotOk, hArr, slotStateToFieldSlot, checkSlotProjectionOk,
    evalValueProjRead, hTIdx, get?_eq_getElem?]
  by_cases hLt : sc.bits < elems.length <;> simp [hLt]

/-- **`Drop` checks the place and changes nothing**: a successful `Drop` jumps to its target with
the frame unchanged, after the place passed the value-dependent access check
(`placeRuntimeAccessOk`: no `Deref`, live root local, initialized index locals, and
`check_slot_projection`), the typed access check, and the unwind-action check. -/
theorem evalLoweredTerminator_drop_sound {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {b : LBlock} {place : Place}
    {target : Nat} {u : UnwindAction} (hb : body.blocks[bb]? = some b)
    (hT : b.terminator = .drop place target u) {step : CfgStep}
    (h : evalLoweredTerminator env body bb slots unwinding = some step) :
    step = .goto target slots unwinding ∧ placeRuntimeAccessOk slots place = true ∧
      env.placeAccessOk slots place = true ∧ unwindActionOk body b.isCleanup u = true ∧
      ∃ st, slots[place.local_]? = some st ∧ st ≠ .dead := by
  unfold evalLoweredTerminator at h
  rw [hb] at h
  simp only [hT] at h
  split at h
  · nomatch h
  · split at h
    · rename_i hC
      obtain ⟨h1, h2, h3⟩ := hC
      exact ⟨cfgGoto_eq_some h, h1, h2, h3,
        placeFrameAccessOk_live (placeRuntimeAccessOk_iff.mp h1).2.1⟩
    · nomatch h

/-- **`Drop` of a dead local is an error (`DeadLocal`)**. -/
theorem evalLoweredTerminator_drop_dead_none {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {b : LBlock} {place : Place}
    {target : Nat} {u : UnwindAction} (hb : body.blocks[bb]? = some b)
    (hT : b.terminator = .drop place target u) (hDead : slots[place.local_]? = some .dead) :
    evalLoweredTerminator env body bb slots unwinding = none := by
  cases hE : evalLoweredTerminator env body bb slots unwinding with
  | none => rfl
  | some step =>
    obtain ⟨_, _, _, _, st, hSt, hNe⟩ := evalLoweredTerminator_drop_sound hb hT hE
    rw [hDead] at hSt
    cases hSt
    exact absurd rfl hNe

/-- **`Drop` through an `Index` operand local that is not an initialized scalar is an error**
(`check_place_access` pre-reads every index local: `DeadLocal` / `UninitializedLocal`). -/
theorem evalLoweredTerminator_drop_bad_index_none {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {b : LBlock} {place : Place}
    {target : Nat} {u : UnwindAction} (hb : body.blocks[bb]? = some b)
    (hT : b.terminator = .drop place target u) {i : Local}
    (hIdx : .index i ∈ place.projection)
    (hBad : ∀ sc, slots[i]? ≠ some (.init (.scalar sc))) :
    evalLoweredTerminator env body bb slots unwinding = none := by
  cases hE : evalLoweredTerminator env body bb slots unwinding with
  | none => rfl
  | some step =>
    obtain ⟨_, hR, _⟩ := evalLoweredTerminator_drop_sound hb hT hE
    obtain ⟨sc, hSc⟩ := placeFrameAccessOk_index (placeRuntimeAccessOk_iff.mp hR).2.1 hIdx
    exact absurd hSc (hBad sc)

/-- **`Drop` of a dead local faults in both semantics** (`DeadLocal` in Anneal's
`check_place_access`, `.ub` in Trusted's `evalTerminator`) under `StateCorr`. -/
theorem evalLoweredTerminator_drop_dead_agrees_trusted {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {s : MachineState} {b : LBlock}
    {place : Place} {target : Nat} {u : UnwindAction}
    (hCorr : StateCorr env bb slots s) (hb : body.blocks[bb]? = some b)
    (hT : b.terminator = .drop place target u) (hDead : slots[place.local_]? = some .dead)
    (span : String) (cmOpt : Option CapturedMir) :
    evalLoweredTerminator env body bb slots unwinding = none ∧
      evalTerminator s ⟨.drop place target u, span⟩ cmOpt = MirStepNode.fail .ub := by
  refine ⟨evalLoweredTerminator_drop_dead_none hb hT hDead, ?_⟩
  rcases SlotsRefine.get?_rel place.local_ hCorr.slots with ⟨hA, _⟩ | ⟨a, t, hA, hTl, hAT⟩
  · simp only [get?_eq_getElem?] at hA
    rw [hA] at hDead
    nomatch hDead
  · simp only [get?_eq_getElem?] at hA hTl
    rw [hA] at hDead
    cases hDead
    cases t with
    | dead => simp only [evalTerminator, get?_eq_getElem?, hTl]
    | _ => simp [SlotBelow] at hAT

/-- **A successful Anneal `Drop` names a local that is live in Trusted too** (under `StateCorr`,
`SlotBelow` relates dead locals exactly), so Trusted's `Drop` does not fault on liveness; this
discharges the liveness premises of `evalLoweredTerminator_drop_bare_divergence`. -/
theorem evalLoweredTerminator_drop_trusted_live {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {s : MachineState} {b : LBlock}
    {place : Place} {target : Nat} {u : UnwindAction} {step : CfgStep}
    (hCorr : StateCorr env bb slots s) (hb : body.blocks[bb]? = some b)
    (hT : b.terminator = .drop place target u)
    (h : evalLoweredTerminator env body bb slots unwinding = some step) :
    ∃ slot, s.frame.locals[place.local_]? = some slot ∧ slot ≠ .dead := by
  obtain ⟨_, _, _, _, st, hSt, hNe⟩ := evalLoweredTerminator_drop_sound hb hT h
  rcases SlotsRefine.get?_rel place.local_ hCorr.slots with ⟨hA, _⟩ | ⟨a, t, hA, hTl, hAT⟩
  · simp only [get?_eq_getElem?] at hA
    rw [hA] at hSt
    nomatch hSt
  · simp only [get?_eq_getElem?] at hA hTl
    rw [hA] at hSt
    cases hSt
    refine ⟨t, hTl, fun hTD => ?_⟩
    subst hTD
    cases st with
    | dead => exact hNe rfl
    | _ => simp [SlotBelow] at hAT

/-- **Documented divergence of `Drop`**: Anneal's `Drop` (no drop glue) keeps the dropped bare
local's value, while Trusted's `evalTerminator` marks it uninitialized; a later read of the local
is defined in Anneal (and in Miri, for types without drop glue) but not in Trusted. Hence
`Drop` is excluded from `LTerminator.Refinable`. -/
theorem evalLoweredTerminator_drop_bare_divergence {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {b : LBlock} {loc : Local}
    {target : Nat} {u : UnwindAction} (hb : body.blocks[bb]? = some b)
    (hT : b.terminator = .drop ⟨loc, []⟩ target u) {step : CfgStep}
    (h : evalLoweredTerminator env body bb slots unwinding = some step)
    (s : MachineState) (span : String) (cmOpt : Option CapturedMir) {slot : LocalSlot}
    (hSlot : s.frame.locals[loc]? = some slot) (hLive : slot ≠ .dead) :
    step = .goto target slots unwinding ∧
      evalTerminator s ⟨.drop ⟨loc, []⟩ target u, span⟩ cmOpt =
        .step { s with frame := ⟨target, 0, s.frame.locals.set loc LocalSlot.uninit⟩ } := by
  refine ⟨?_, ?_⟩
  · unfold evalLoweredTerminator at h
    rw [hb] at h
    simp only [hT] at h
    split at h
    · nomatch h
    · split at h
      · exact cfgGoto_eq_some h
      · nomatch h
  · have hLt : loc < s.frame.locals.length := (List.getElem?_eq_some_iff.mp hSlot).1
    simp only [evalTerminator, get?_eq_getElem?, hSlot]
    cases slot with
    | dead => exact absurd rfl hLive
    | _ => simp only [set?_eq_some_iff.mpr ⟨hLt, rfl⟩]

/-- **Trivial (projected) `Drop` refines Trusted**: dropping a projected place that Anneal can
read jumps to the drop target in both semantics with the frame unchanged, preserving
`StateCorr`. -/
theorem evalLoweredTerminator_drop_projected_refines {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {s : MachineState} {b : LBlock}
    {place : Place} {target : Nat} {u : UnwindAction} {step : CfgStep}
    (hCorr : StateCorr env bb slots s) (hb : body.blocks[bb]? = some b)
    (hT : b.terminator = .drop place target u) (hProj : place.projection ≠ []) {v : Value}
    (hRead : readPlaceState slots place = .ok v)
    (h : evalLoweredTerminator env body bb slots unwinding = some step) (span : String)
    (cmOpt : Option CapturedMir) :
    step = .goto target slots unwinding ∧
      evalTerminator s ⟨.drop place target u, span⟩ cmOpt =
        .step { s with frame := ⟨target, 0, s.frame.locals⟩ } ∧
      StateCorr env target slots { s with frame := ⟨target, 0, s.frame.locals⟩ } := by
  refine ⟨?_, ?_, hCorr.jump target s.frame.locals hCorr.slots⟩
  · unfold evalLoweredTerminator at h
    rw [hb] at h
    simp only [hT] at h
    split at h
    · nomatch h
    · split at h
      · exact cfgGoto_eq_some h
      · nomatch h
  · obtain ⟨rootVal, hRoot, hTRead⟩ := readPlaceState_below_refines hCorr.slots hRead
    obtain ⟨a, rest, hP⟩ : ∃ a rest, place.projection = a :: rest := by
      cases hp : place.projection with
      | nil => exact absurd hp hProj
      | cons a rest => exact ⟨a, rest, rfl⟩
    simp only [get?_eq_getElem?] at hRoot
    simp only [evalTerminator, get?_eq_getElem?, hRoot, hP]
    rw [hP] at hTRead
    simp only [hTRead]

/-- `check_slot_projection` accepts every path below an uninitialized local. -/
theorem checkPlaceSlotOk_uninit {slots : List LocalSlotState} {place : Place}
    (hRoot : slots[place.local_]? = some .uninit) : checkPlaceSlotOk slots place = true := by
  simp [checkPlaceSlotOk, hRoot, slotStateToFieldSlot, checkSlotProjectionOk]

/-- **`Drop` through an inactive enum variant is an error (`InactiveVariantProjection`)**:
`check_slot_projection` rejects dropping `(x as V).f` while `x` holds another variant, whether `x`
is an initialized value or a partial shell narrowed to that variant. -/
theorem evalLoweredTerminator_drop_inactive_variant_none {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {b : LBlock} {loc : Local}
    {v dv idx : Nat} {nm : Option String} {ty : Ty} {rest : List ProjectionElem} {target : Nat}
    {u : UnwindAction} (hb : body.blocks[bb]? = some b)
    (hT : b.terminator = .drop ⟨loc, .downcast nm dv :: .field idx ty :: rest⟩ target u)
    (hNe : v ≠ dv)
    (hRoot : (∃ vals, slots[loc]? = some (.init (.aggregate v vals))) ∨
      (∃ sh, slots[loc]? = some (.partialShell sh) ∧ shellVariant sh = v)) :
    evalLoweredTerminator env body bb slots unwinding = none := by
  cases hE : evalLoweredTerminator env body bb slots unwinding with
  | none => rfl
  | some step =>
    obtain ⟨_, hR, _⟩ := evalLoweredTerminator_drop_sound hb hT hE
    have hC := (placeRuntimeAccessOk_iff.mp hR).2.2
    have hF := checkPlaceSlotOk_inactive_variant_false slots loc nm ty rest (idx := idx) hNe
    rcases hRoot with ⟨vals, hV⟩ | ⟨sh, hS, hVar⟩
    · rw [hF.1 vals hV] at hC
      nomatch hC
    · rw [hF.2 sh hS hVar] at hC
      nomatch hC

/-- **`Drop` of an out-of-bounds element of an initialized array is an error
(`IndexOutOfBounds`)**: `check_slot_projection` checks the read index against the runtime array
length. -/
theorem evalLoweredTerminator_drop_index_oob_none {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {b : LBlock} {loc i : Local}
    {elems : List Value} {sc : ScalarInt} {target : Nat} {u : UnwindAction}
    (hb : body.blocks[bb]? = some b) (hT : b.terminator = .drop ⟨loc, [.index i]⟩ target u)
    (hArr : slots[loc]? = some (.init (.aggregate 0 elems)))
    (hIdx : slots[i]? = some (.init (.scalar sc))) (hOob : elems.length ≤ sc.bits) :
    evalLoweredTerminator env body bb slots unwinding = none := by
  cases hE : evalLoweredTerminator env body bb slots unwinding with
  | none => rfl
  | some step =>
    obtain ⟨_, hR, _⟩ := evalLoweredTerminator_drop_sound hb hT hE
    have hC := (placeRuntimeAccessOk_iff.mp hR).2.2
    rw [checkPlaceSlotOk_array_index_eq hArr hIdx] at hC
    simp only [decide_eq_true_eq] at hC
    omega

/-- **`Drop` of a place with a `Deref` is unsupported (`UnsupportedPlaceProjection`)**. -/
theorem evalLoweredTerminator_drop_deref_none {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {b : LBlock} {place : Place}
    {target : Nat} {u : UnwindAction} (hb : body.blocks[bb]? = some b)
    (hT : b.terminator = .drop place target u)
    (hD : projectionHasDeref place.projection = true) :
    evalLoweredTerminator env body bb slots unwinding = none := by
  cases hE : evalLoweredTerminator env body bb slots unwinding with
  | none => rfl
  | some step =>
    obtain ⟨_, hR, _⟩ := evalLoweredTerminator_drop_sound hb hT hE
    rw [(placeRuntimeAccessOk_iff.mp hR).1] at hD
    nomatch hD

/-- **Projected `Drop` of an initialized local refines Trusted without a read premise**: a
successful Anneal `Drop` of a projected place whose local is initialized has walked the value
(`check_slot_projection`), so Anneal reads the place, and Trusted's `evalTerminator` jumps to the
drop target with the frame unchanged, preserving `StateCorr` (the read premise of
`evalLoweredTerminator_drop_projected_refines` is derived). -/
theorem evalLoweredTerminator_drop_projected_init_refines {env : CfgEnv} {body : LBody}
    {bb : Nat} {slots : List LocalSlotState} {unwinding : Option Nat} {s : MachineState}
    {b : LBlock} {place : Place} {target : Nat} {u : UnwindAction} {step : CfgStep}
    (hCorr : StateCorr env bb slots s) (hb : body.blocks[bb]? = some b)
    (hT : b.terminator = .drop place target u) (hProj : place.projection ≠ [])
    {rootVal : Value} (hRoot : slots[place.local_]? = some (.init rootVal))
    (h : evalLoweredTerminator env body bb slots unwinding = some step) (span : String)
    (cmOpt : Option CapturedMir) :
    step = .goto target slots unwinding ∧
      evalTerminator s ⟨.drop place target u, span⟩ cmOpt =
        .step { s with frame := ⟨target, 0, s.frame.locals⟩ } ∧
      StateCorr env target slots { s with frame := ⟨target, 0, s.frame.locals⟩ } := by
  obtain ⟨_, hR, _⟩ := evalLoweredTerminator_drop_sound hb hT h
  obtain ⟨hND, _, hC⟩ := placeRuntimeAccessOk_iff.mp hR
  have hRead : ∃ w, readPlaceState slots place = .ok w := by
    unfold checkPlaceSlotOk at hC
    rw [hRoot] at hC
    simp only [slotStateToFieldSlot, checkSlotProjectionOk] at hC
    split at hC
    · rename_i w hw
      exact ⟨w, (readPlaceState_eq_readFieldSlot hRoot (by simp) place.projection hND).trans hw⟩
    · nomatch hC
  obtain ⟨w, hw⟩ := hRead
  exact evalLoweredTerminator_drop_projected_refines hCorr hb hT hProj hw h span cmOpt

/-- **Documented divergence of projected `Drop` below an uninitialized local**: Anneal's `Drop`
(no drop glue) accepts a projected place of an uninitialized local (`check_slot_projection`
accepts any tail below `Uninit`, `checkPlaceSlotOk_uninit`) and jumps to the drop target, while
Trusted's `evalTerminator` faults when the local is uninitialized there too. -/
theorem evalLoweredTerminator_drop_projected_uninit_divergence {env : CfgEnv} {body : LBody}
    {bb : Nat} {slots : List LocalSlotState} {unwinding : Option Nat} {s : MachineState}
    {b : LBlock} {place : Place} {target : Nat} {u : UnwindAction} {step : CfgStep}
    (hb : body.blocks[bb]? = some b) (hT : b.terminator = .drop place target u)
    (hProj : place.projection ≠ []) (hRoot : slots[place.local_]? = some .uninit)
    (h : evalLoweredTerminator env body bb slots unwinding = some step)
    (hTU : s.frame.locals[place.local_]? = some .uninit) (span : String)
    (cmOpt : Option CapturedMir) :
    checkPlaceSlotOk slots place = true ∧ step = .goto target slots unwinding ∧
      evalTerminator s ⟨.drop place target u, span⟩ cmOpt = MirStepNode.fail .ub := by
  refine ⟨checkPlaceSlotOk_uninit hRoot, (evalLoweredTerminator_drop_sound hb hT h).1, ?_⟩
  obtain ⟨a, rest, hP⟩ : ∃ a rest, place.projection = a :: rest := by
    cases hp : place.projection with
    | nil => exact absurd hp hProj
    | cons a rest => exact ⟨a, rest, rfl⟩
  simp only [evalTerminator, get?_eq_getElem?, hTU, hP]

/-- Every `cfgGoto` jump targets an existing block whose `isCleanup` flag matches
`unwinding.isSome`. -/
theorem cfgGoto_cleanup_invariant {body : LBody} {t next : Nat}
    {slots slots' : List LocalSlotState} {unwinding unwinding' : Option Nat}
    (h : cfgGoto body t slots unwinding = some (.goto next slots' unwinding')) :
    next = t ∧ slots' = slots ∧ unwinding' = unwinding ∧
      ∃ nb, body.blocks[next]? = some nb ∧ nb.isCleanup = unwinding'.isSome := by
  unfold cfgGoto at h
  cases hnb : body.blocks[t]? with
  | none => rw [hnb] at h; nomatch h
  | some nb =>
    rw [hnb] at h
    simp only at h
    split at h
    · rename_i hClean
      injection h with hStep
      injection hStep with hNext hSlots hUnw
      subst hNext hSlots hUnw
      exact ⟨rfl, rfl, rfl, nb, hnb, hClean⟩
    · nomatch h

/-- Every `.goto` step produced by `startPanic` enters cleanup mode (`unwinding' = some bb`) at an
existing cleanup block (`nb.isCleanup = true`). -/
theorem startPanic_goto_cleanup_invariant {body : LBody} {bb next : Nat} {u : UnwindAction}
    {slots slots' : List LocalSlotState} {unwinding unwinding' : Option Nat}
    (h : startPanic body bb u slots unwinding = some (.goto next slots' unwinding')) :
    unwinding = none ∧ unwinding' = some bb ∧
      ∃ nb, body.blocks[next]? = some nb ∧ nb.isCleanup = true := by
  cases u with
  | unreachable => simp [startPanic] at h
  | terminate => simp [startPanic] at h
  | continue_ =>
    simp only [startPanic] at h
    split at h <;> nomatch h
  | cleanup c =>
    simp only [startPanic] at h
    split at h
    · nomatch h
    · rename_i hNotUnw
      have hUnwNone : unwinding = none := by
        cases unwinding with
        | none => rfl
        | some _ => simp at hNotUnw
      obtain ⟨rfl, rfl, rfl, nb, hnb, hClean⟩ := cfgGoto_cleanup_invariant h
      exact ⟨hUnwNone, rfl, nb, hnb, hClean⟩

/-- **Target-block cleanup/unwind invariant (`evalLoweredTerminator_goto_cleanup_invariant`)**:
every `.goto next slots' unwinding'` transition produced by `evalLoweredTerminator` targets a
valid basic block `nb` in `body.blocks` whose `isCleanup` flag matches `unwinding'.isSome`
(`B4` standalone/loop CFG edge invariant). -/
theorem evalLoweredTerminator_goto_cleanup_invariant {env : CfgEnv} {body : LBody}
    {bb next : Nat} {slots slots' : List LocalSlotState} {unwinding unwinding' : Option Nat}
    (h : evalLoweredTerminator env body bb slots unwinding =
      some (.goto next slots' unwinding')) :
    ∃ nb, body.blocks[next]? = some nb ∧ nb.isCleanup = unwinding'.isSome := by
  unfold evalLoweredTerminator at h
  cases hb : body.blocks[bb]? with
  | none => rw [hb] at h; nomatch h
  | some block =>
    rw [hb] at h
    simp only at h
    split at h
    · nomatch h
    · cases hT : block.terminator with
      | goto t =>
        rw [hT] at h
        exact (cfgGoto_cleanup_invariant h).2.2.2
      | switchInt discr bytes targets =>
        rw [hT] at h
        simp only at h
        split at h
        · split at h
          · split at h
            · exact (cfgGoto_cleanup_invariant h).2.2.2
            · nomatch h
          · nomatch h
        · nomatch h
      | return_ =>
        rw [hT] at h
        simp only at h
        split at h
        · nomatch h
        · split at h
          · split at h <;> nomatch h
          · nomatch h
      | unreachable => rw [hT] at h; nomatch h
      | drop place target unwind =>
        rw [hT] at h
        simp only at h
        split at h
        · exact (cfgGoto_cleanup_invariant h).2.2.2
        · nomatch h
      | assert cond expected msg target unwind =>
        rw [hT] at h
        simp only at h
        split at h
        · split at h
          · split at h
            · split at h
              · exact (cfgGoto_cleanup_invariant h).2.2.2
              · nomatch h
            · split at h
              · obtain ⟨_, hUnw', nb, hnb, hClean⟩ := startPanic_goto_cleanup_invariant h
                exact ⟨nb, hnb, by simp [hUnw', hClean]⟩
              · nomatch h
          · nomatch h
        · nomatch h
      | call func args dest destTy target unwind =>
        rw [hT] at h
        simp only at h
        split at h
        · split at h
          · nomatch h
          · split at h
            · split at h
              · nomatch h
              · split at h
                · nomatch h
                · split at h
                  · nomatch h
                  · split at h
                    · split at h
                      · nomatch h
                      · split at h
                        · nomatch h
                        · split at h
                          · nomatch h
                          · split at h
                            · exact (cfgGoto_cleanup_invariant h).2.2.2
                            · nomatch h
                    · obtain ⟨_, hUnw', nb, hnb, hClean⟩ := startPanic_goto_cleanup_invariant h
                      exact ⟨nb, hnb, by simp [hUnw', hClean]⟩
                    · nomatch h
            · nomatch h
        · nomatch h
      | unwindResume =>
        rw [hT] at h
        simp only at h
        split at h <;> nomatch h
      | unwindTerminate =>
        rw [hT] at h
        simp only at h
        split at h <;> nomatch h

/-- `TrustedRun` is transitive: composing two fault-free Trusted execution prefixes yields a
fault-free Trusted execution prefix. -/
theorem TrustedRun.trans {cm : CapturedMir} {s₁ s₂ s₃ : MachineState}
    (h₁ : TrustedRun cm s₁ s₂) (h₂ : TrustedRun cm s₂ s₃) : TrustedRun cm s₁ s₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hStep _ ih => exact .step hStep (ih h₂)

/-- **`BodyCorrWithStmts`**: generalizes `BodyCorr` to basic blocks with arbitrary statement
lists (not restricted to `b.statements = []`), requiring only that `env.evalStmts b.statements`
is refined by a `TrustedRun` advancing `stmtIdx` from `0` to `tStmts.length` while preserving
`SlotsRefine SlotBelow` and the machine environment. -/
structure BodyCorrWithStmts (env : CfgEnv) (body : LBody) (cm : CapturedMir) : Prop where
  phase : ∀ tag, cm.phase ≠ .other tag
  layouts : cm.layouts = env.layouts
  block : ∀ (i : Nat) (b : LBlock), body.blocks[i]? = some b →
    b.terminator.Refinable ∧
      ∃ (tStmts : List Statement) (span : String),
        cm.basicBlocks[i]? = some ⟨tStmts, ⟨b.terminator.toTrusted, span⟩, b.isCleanup⟩ ∧
        ∀ (slots slots1 : List LocalSlotState) (s : MachineState),
          StateCorr env i slots s →
          env.evalStmts b.statements slots = some slots1 →
          ∃ (locals1 : List LocalSlot),
            TrustedRun cm s { s with frame := ⟨i, tStmts.length, locals1⟩ } ∧
            SlotsRefine SlotBelow slots1 locals1

/-- At the end of a basic block's statement list (`stmtIdx = tStmts.length`), Trusted's
`stepMirFn` evaluates the block's terminator. -/
theorem stepMirFn_at_end_eq_evalTerminator {cm : CapturedMir} {bb : Nat}
    {tStmts : List Statement} {tKind : TerminatorKind} {span : String} {isCleanup : Bool}
    {s : MachineState} {locals1 : List LocalSlot}
    (hPhase : ∀ tag, cm.phase ≠ .other tag)
    (hCallee : s.memory.activeCallee = none)
    (hcm : cm.basicBlocks[bb]? = some ⟨tStmts, ⟨tKind, span⟩, isCleanup⟩) :
    stepMirFn cm { s with frame := ⟨bb, tStmts.length, locals1⟩ } =
      evalTerminator { s with frame := ⟨bb, tStmts.length, locals1⟩ } ⟨tKind, span⟩ (some cm) := by
  have hNone : tStmts[tStmts.length]? = none := List.getElem?_eq_none (Nat.le_refl _)
  unfold stepMirFn
  simp only [hCallee, Option.getD_none, get?_eq_getElem?, hcm, hNone,
    length_eq_list_length, BEq.rfl, ↓reduceIte]

/-- **`evalLoweredTerminator_at_end_refines_trusted`**: generalizes
`evalLoweredTerminator_refines_trusted` to a state sitting at the end of a block's statement list
(`stmtIdx = tStmts.length`). -/
theorem evalLoweredTerminator_at_end_refines_trusted {env : CfgEnv} {body : LBody}
    {cm : CapturedMir} {bb : Nat} {slots slots1 : List LocalSlotState} {unwinding : Option Nat}
    {s : MachineState} {locals1 : List LocalSlot} {tStmts : List Statement} {span : String}
    {b : LBlock} {step : CfgStep}
    (hPhase : ∀ tag, cm.phase ≠ .other tag)
    (hLayouts : cm.layouts = env.layouts)
    (hb : body.blocks[bb]? = some b)
    (hRef : b.terminator.Refinable)
    (hcm : cm.basicBlocks[bb]? = some ⟨tStmts, ⟨b.terminator.toTrusted, span⟩, b.isCleanup⟩)
    (hCorr : StateCorr env bb slots s)
    (hRel1 : SlotsRefine SlotBelow slots1 locals1)
    (h : evalLoweredTerminator env body bb slots1 unwinding = some step) :
    match step with
    | .goto next slots' _ =>
      ∃ s', TrustedStep (stepMirFn cm { s with frame := ⟨bb, tStmts.length, locals1⟩ }) s' ∧
        StateCorr env next slots' s'
    | .returned v =>
      stepMirFn cm { s with frame := ⟨bb, tStmts.length, locals1⟩ } = .retNormal v s.memory
    | .panicked _ =>
      stepMirFn cm { s with frame := ⟨bb, tStmts.length, locals1⟩ } = .retOutcome .panic
    | .terminated _ =>
      stepMirFn cm { s with frame := ⟨bb, tStmts.length, locals1⟩ } = .retOutcome .abort := by
  have hStepEnd : stepMirFn cm { s with frame := ⟨bb, tStmts.length, locals1⟩ } =
      evalTerminator { s with frame := ⟨bb, tStmts.length, locals1⟩ }
        ⟨b.terminator.toTrusted, span⟩ (some cm) :=
    stepMirFn_at_end_eq_evalTerminator hPhase hCorr.callee hcm
  unfold evalLoweredTerminator at h
  rw [hb] at h
  simp only at h
  rw [hStepEnd]
  split at h
  · nomatch h
  · cases hT : b.terminator with
    | goto t =>
      rw [hT] at h
      simp only at h
      obtain rfl := cfgGoto_eq_some h
      exact ⟨_, Or.inl rfl, hCorr.jump t locals1 hRel1⟩
    | switchInt discr bytes targets =>
      rw [hT] at hRef h
      simp only at h
      split at h
      · split at h
        · rename_i sc slots' hOp
          split at h
          · obtain rfl := cfgGoto_eq_some h
            obtain ⟨locals', hTOp, hRel⟩ := evalOperandState_below_refines slots1 slots'
              locals1 discr (.scalar sc) s.memory.borrows env.globals env.layouts
              s.memory.callerLocals hRel1 hRef hOp
            refine ⟨_, Or.inr ⟨sc.bits, ?_⟩, hCorr.jump _ locals' hRel⟩
            simp only [LTerminator.toTrusted, evalTerminator, hLayouts, hCorr.globals,
              hTOp, evalSwitchTargets_eq_lookupSwitchTarget]
          · nomatch h
        · nomatch h
      · nomatch h
    | return_ =>
      rw [hT] at h
      simp only at h
      split at h
      · nomatch h
      · split at h
        · rename_i v hRead
          split at h
          · cases h
            obtain ⟨rootVal, hRoot, hProj⟩ := readPlaceState_below_refines hRel1 hRead
            simp only [readProjectedValue, ProjReadResult.ok.injEq] at hProj
            subst hProj
            simp only [LTerminator.toTrusted, evalTerminator, hRoot, hCorr.stack]
          · nomatch h
        · nomatch h
    | unreachable => rw [hT] at h; nomatch h
    | drop place t u => rw [hT] at hRef; exact absurd hRef id
    | assert cond expected msg t u =>
      rw [hT] at hRef h
      simp only at h
      split at h
      · rename_i sc slots' hOp
        obtain ⟨locals', hTOp, hRel⟩ := evalOperandState_below_refines slots1 slots'
          locals1 cond (.scalar sc) s.memory.borrows env.globals env.layouts
          s.memory.callerLocals hRel1 hRef hOp
        simp only [LTerminator.toTrusted, evalTerminator, hLayouts, hCorr.globals, hTOp]
        split at h
        · rename_i hBool
          obtain ⟨bits, sz⟩ := sc
          obtain ⟨_, hLe⟩ := hBool
          have hB01 : bits = 0 ∨ bits = 1 := by simp only at hLe; omega
          rcases hB01 with rfl | rfl <;> cases expected
          · rw [show (((0 : Nat) == 1) == false) = true from rfl] at h
            simp only [↓reduceIte] at h
            dsimp only
            split at h
            · obtain rfl := cfgGoto_eq_some h
              exact ⟨_, Or.inl rfl, hCorr.jump t locals' hRel⟩
            · nomatch h
          · rw [show (((0 : Nat) == 1) == true) = false from rfl] at h
            simp only [Bool.false_eq_true, ↓reduceIte] at h
            dsimp only
            split at h
            · cases u with
              | unreachable => simp [startPanic] at h
              | terminate =>
                simp only [startPanic, Option.some.injEq] at h
                subst h
                simp [applyUnwindAction]
              | continue_ =>
                simp only [startPanic] at h
                split at h
                · nomatch h
                · cases h
                  simp [applyUnwindAction, hCorr.stack]
              | cleanup c =>
                simp only [startPanic] at h
                split at h
                · nomatch h
                · obtain rfl := cfgGoto_eq_some h
                  exact ⟨{ s with frame := { blockIdx := c, stmtIdx := 0, locals := locals' } },
                    Or.inl rfl, hCorr.jump c locals' hRel⟩
            · nomatch h
          · rw [show (((1 : Nat) == 1) == false) = false from rfl] at h
            simp only [Bool.false_eq_true, ↓reduceIte] at h
            dsimp only
            split at h
            · cases u with
              | unreachable => simp [startPanic] at h
              | terminate =>
                simp only [startPanic, Option.some.injEq] at h
                subst h
                simp [applyUnwindAction]
              | continue_ =>
                simp only [startPanic] at h
                split at h
                · nomatch h
                · cases h
                  simp [applyUnwindAction, hCorr.stack]
              | cleanup c =>
                simp only [startPanic] at h
                split at h
                · nomatch h
                · obtain rfl := cfgGoto_eq_some h
                  exact ⟨{ s with frame := { blockIdx := c, stmtIdx := 0, locals := locals' } },
                    Or.inl rfl, hCorr.jump c locals' hRel⟩
            · nomatch h
          · rw [show (((1 : Nat) == 1) == true) = true from rfl] at h
            simp only [↓reduceIte] at h
            dsimp only
            split at h
            · obtain rfl := cfgGoto_eq_some h
              exact ⟨_, Or.inl rfl, hCorr.jump t locals' hRel⟩
            · nomatch h
        · nomatch h
      · nomatch h
    | call func args dest destTy t u => rw [hT] at hRef; exact absurd hRef id
    | unwindResume =>
      rw [hT] at h
      simp only at h
      split at h
      · cases h
        simp [LTerminator.toTrusted, evalTerminator, hCorr.stack]
      · nomatch h
    | unwindTerminate =>
      rw [hT] at h
      simp only at h
      split at h
      · cases h
        simp [LTerminator.toTrusted, evalTerminator]
      · nomatch h

/-- **`runLoweredCfgSteps_with_stmts_refines_trusted`**: multi-block fuel-bounded CFG execution
over blocks with non-empty statement lists (`BodyCorrWithStmts`) is matched by a fault-free
`TrustedRun` execution of `stepMirFn` across both statements and terminators, preserving
`StateCorr` and the target-block cleanup/unwinding invariant on every block transition. -/
theorem runLoweredCfgSteps_with_stmts_refines_trusted {env : CfgEnv} {body : LBody}
    {cm : CapturedMir} (hBody : BodyCorrWithStmts env body cm) :
    ∀ (fuel bb : Nat) (slots : List LocalSlotState) (unwinding : Option Nat) (s : MachineState)
      (o : CfgOutcome), StateCorr env bb slots s →
      runLoweredCfgSteps env body fuel bb slots unwinding = some o →
      match o with
      | .outOfFuel bb' slots' _ => ∃ s', TrustedRun cm s s' ∧ StateCorr env bb' slots' s'
      | .returned v => ∃ s', TrustedRun cm s s' ∧ stepMirFn cm s' = .retNormal v s'.memory
      | .panicked _ => ∃ s', TrustedRun cm s s' ∧ stepMirFn cm s' = .retOutcome .panic
      | .terminated _ => ∃ s', TrustedRun cm s s' ∧ stepMirFn cm s' = .retOutcome .abort := by
  intro fuel
  induction fuel with
  | zero =>
    intro bb slots unwinding s o hCorr h
    simp only [runLoweredCfgSteps, Option.some.injEq] at h
    subst h
    exact ⟨s, .refl s, hCorr⟩
  | succ fuel ih =>
    intro bb slots unwinding s o hCorr h
    simp only [runLoweredCfgSteps] at h
    cases hb : body.blocks[bb]? with
    | none => rw [hb] at h; nomatch h
    | some block =>
      rw [hb] at h
      simp only at h
      cases hSt : env.evalStmts block.statements slots with
      | none => rw [hSt] at h; nomatch h
      | some slots1 =>
        rw [hSt] at h
        simp only at h
        obtain ⟨hTermRef, tStmts, span, hcm, hStmtsRun⟩ := hBody.block bb block hb
        obtain ⟨locals1, hRunStmts, hRel1⟩ := hStmtsRun slots slots1 s hCorr hSt
        cases hT : evalLoweredTerminator env body bb slots1 unwinding with
        | none => rw [hT] at h; nomatch h
        | some step =>
          rw [hT] at h
          have hRef := evalLoweredTerminator_at_end_refines_trusted
            hBody.phase hBody.layouts hb hTermRef hcm hCorr hRel1 hT
          cases step with
          | goto next slots' unwinding' =>
            simp only at h hRef
            obtain ⟨s', hStep, hCorr'⟩ := hRef
            have hRest := ih next slots' unwinding' s' o hCorr' h
            cases o with
            | outOfFuel bb' slots'' _ =>
              obtain ⟨s'', hRun, hC⟩ := hRest
              exact ⟨s'', hRunStmts.trans (.step hStep hRun), hC⟩
            | returned v =>
              obtain ⟨s'', hRun, hC⟩ := hRest
              exact ⟨s'', hRunStmts.trans (.step hStep hRun), hC⟩
            | panicked b =>
              obtain ⟨s'', hRun, hC⟩ := hRest
              exact ⟨s'', hRunStmts.trans (.step hStep hRun), hC⟩
            | terminated b =>
              obtain ⟨s'', hRun, hC⟩ := hRest
              exact ⟨s'', hRunStmts.trans (.step hStep hRun), hC⟩
          | returned v =>
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨{ s with frame := ⟨bb, tStmts.length, locals1⟩ }, hRunStmts, hRef⟩
          | panicked b =>
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨{ s with frame := ⟨bb, tStmts.length, locals1⟩ }, hRunStmts, hRef⟩
          | terminated b =>
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨{ s with frame := ⟨bb, tStmts.length, locals1⟩ }, hRunStmts, hRef⟩

/-- Every statement-free `BodyCorr` (with `env.evalStmts [] slots = some slots`) is an instance
of `BodyCorrWithStmts`. -/
theorem BodyCorr.toBodyCorrWithStmts {env : CfgEnv} {body : LBody} {cm : CapturedMir}
    (hBody : BodyCorr env body cm) (hStmts : ∀ slots, env.evalStmts [] slots = some slots) :
    BodyCorrWithStmts env body cm where
  phase := hBody.phase
  layouts := hBody.layouts
  block i b hb := by
    obtain ⟨hNil, hRef, span, hcm⟩ := hBody.block i b hb
    refine ⟨hRef, [], span, hcm, fun slots slots1 s hCorr hEval => ?_⟩
    rw [hNil, hStmts] at hEval
    injection hEval with hEq
    subst hEq
    refine ⟨s.frame.locals, ?_, hCorr.slots⟩
    have hFrame : { s with frame := ⟨i, ([] : List Statement).length, s.frame.locals⟩ } = s := by
      rcases s with ⟨⟨bIdx, sIdx, locs⟩, mem⟩
      obtain ⟨rfl, rfl, _⟩ := hCorr
      rfl
    rw [hFrame]
    exact .refl s

/-- Executing a single bare-local `Deinit` statement at the start of basic block `bb` produces a
one-step `TrustedRun` to `stmtIdx = 1` while preserving `SlotsRefine SlotBelow` (discharging
`BodyCorrWithStmts`'s block statement obligation for bare `Deinit` blocks). -/
theorem stepMirFn_deinit_root_trustedRun {env : CfgEnv} {cm : CapturedMir} {bb : Nat}
    {ts : Bool} {slots slots1 : List LocalSlotState} {place : Place} {span : String}
    {term : Terminator} {isCleanup : Bool} {s : MachineState}
    (hPhase : ∀ tag, cm.phase ≠ .other tag)
    (hCorr : StateCorr env bb slots s)
    (hcm : cm.basicBlocks[bb]? = some ⟨[⟨.deinit place, span⟩], term, isCleanup⟩)
    (hRoot : place.projection = [])
    (hDeinit : evalDeinitPlace ts slots place = some slots1) :
    TrustedRun cm s { s with frame := ⟨bb, 1, s.frame.locals.set place.local_ .uninit⟩ } ∧
      SlotsRefine SlotBelow slots1 (s.frame.locals.set place.local_ .uninit) := by
  obtain ⟨hStmt, hRel1⟩ := evalStmt_deinit_root_refines (s := s) (span := span)
    (localDecls := cm.localDecls) (layouts := cm.layouts) hCorr.slots hRoot hDeinit
  refine ⟨.step (Or.inl ?_) (.refl _), hRel1⟩
  unfold stepMirFn
  simp only [hCorr.callee, Option.getD_none, get?_eq_getElem?, hCorr.block, hcm, hCorr.stmt,
    List.getElem?_cons_zero]
  rw [hStmt]
  simp only [advanceStmt, hCorr.block, hCorr.stmt]

/-- Executing a single projected `Deinit` statement at the start of basic block `bb` produces a
one-step `TrustedRun` to `stmtIdx = 1` while preserving `SlotsRefine SlotBelow` (discharging
`BodyCorrWithStmts`'s block statement obligation for projected `Deinit` blocks). -/
theorem stepMirFn_deinit_projected_trustedRun {env : CfgEnv} {cm : CapturedMir} {bb : Nat}
    {ts : Bool} {slots slots1 : List LocalSlotState} {place : Place} {span : String}
    {term : Terminator} {isCleanup : Bool} {s : MachineState} {rootVal tv : Value}
    (hPhase : ∀ tag, cm.phase ≠ .other tag)
    (hCorr : StateCorr env bb slots s)
    (hcm : cm.basicBlocks[bb]? = some ⟨[⟨.deinit place, span⟩], term, isCleanup⟩)
    (hProj : place.projection ≠ [])
    (hDeinit : evalDeinitPlace ts slots place = some slots1)
    (hTRoot : s.frame.locals[place.local_]? = some (.init rootVal))
    (hTRead : readProjectedValue s.frame.locals rootVal place.projection = .ok tv) :
    TrustedRun cm s { s with frame := ⟨bb, 1, s.frame.locals⟩ } ∧
      SlotsRefine SlotBelow slots1 s.frame.locals := by
  obtain ⟨hStmt, hRel1⟩ := evalStmt_deinit_projected_refines (s := s) (span := span)
    (localDecls := cm.localDecls) (layouts := cm.layouts) hCorr.slots hProj hDeinit hTRoot hTRead
  refine ⟨.step (Or.inl ?_) (.refl _), hRel1⟩
  unfold stepMirFn
  simp only [hCorr.callee, Option.getD_none, get?_eq_getElem?, hCorr.block, hcm, hCorr.stmt,
    List.getElem?_cons_zero]
  rw [hStmt]
  simp only [advanceStmt, hCorr.block, hCorr.stmt]

/-! ## Section 4: Synthetic Sub-Place Pointers, `Deref` Places, and Sub-Place `CopyNonOverlapping`
-/

/-! ### Section 4a: Collision-free synthetic allocation bases (`local_base_addr_for_decls`) -/

/-- The synthetic stack page (`PAGE = 0x1000` in `local_base_addr_for_decls`). Irreducible, so that
symbolic page multiples `n * synthPage` are never unfolded into unary `Nat.mul` recursions. -/
@[irreducible] def synthPage : Nat := 0x1000

theorem synthPage_eq : synthPage = 4096 := by unfold synthPage; rfl

/-- `alloc_size_and_align` of every declared local of a frame: `some (size, align)`, or `none`
when the layout model rejects the declared type (`Err(_)`, which strides one page). -/
abbrev AllocLayouts : Type := List (Option (Nat × Nat))

/-- One step of the base scan over a preceding local (`local_base_addr_for_decls`): align the
cursor to `max(align, PAGE)` and advance by the page-rounded allocation size (at least one
page, `size.max(1).div_ceil(PAGE) * PAGE`); a layout error advances by one page. -/
def baseScanStep (cur : Nat) : Option (Nat × Nat) → Nat
  | some (size, align) =>
    PlaceAndRvalue.alignUp cur (max align synthPage) + PlaceAndRvalue.alignUp (max size 1) synthPage
  | none => cur + synthPage

/-- The cursor after scanning the preceding locals `ls` from `cur`, failing closed as soon as it
exceeds `limit` (`cur > limit ⇒ UnsupportedMemoryAccess`, never a masked address). -/
def baseScan (limit : Nat) : Nat → AllocLayouts → Option Nat
  | cur, [] => some cur
  | cur, x :: xs => if limit < baseScanStep cur x then none else baseScan limit (baseScanStep cur x) xs

/-- The layout of local `l` (`local_decls.get(l).and_then(|t| t.alloc_size_and_align().ok())`). -/
def ownLayout (lays : AllocLayouts) (l : Nat) : Option (Nat × Nat) := (lays[l]?).join

/-- The allocation size of local `l` (`0` without a layout). -/
def ownAllocSize (lays : AllocLayouts) (l : Nat) : Nat := ((ownLayout lays l).map Prod.fst).getD 0

/-- The cursor aligned to local `l`'s own alignment when that exceeds a page
(`if align > PAGE { cur = cur.div_ceil(align) * align }`). -/
def ownAlignedCursor (lays : AllocLayouts) (l cur : Nat) : Nat :=
  match ownLayout lays l with
  | some (_, align) => if synthPage < align then PlaceAndRvalue.alignUp cur align else cur
  | none => cur

/-- **`local_base_addr_for_decls`**: the synthetic base address of local `l` in a frame whose
declared locals have the allocation layouts `lays`, on a target whose largest address is
`limit` (`ptr_width.max_usize()`):
1. scan the `min(l, lays.length)` preceding locals from `PAGE` (`baseScan`), failing as soon as
   the cursor exceeds `limit`;
2. align to the local's own alignment when it exceeds a page (`ownAlignedCursor`);
3. a local beyond the declarations advances one page per missing declaration;
4. fail closed (`none`, `UnsupportedMemoryAccess`) unless the whole allocation
   `[base, base + size)` fits below `limit`. -/
def localBaseAddr (lays : AllocLayouts) (l limit : Nat) : Option Nat :=
  match baseScan limit synthPage (lays.take l) with
  | none => none
  | some cur =>
    if limit < ownAlignedCursor lays l cur + (l - lays.length) * synthPage + ownAllocSize lays l then
      none
    else some (ownAlignedCursor lays l cur + (l - lays.length) * synthPage)

theorem synthPage_pos : 0 < synthPage := by rw [synthPage_eq]; decide

/-- Characterization of a successful `localBaseAddr`. -/
theorem localBaseAddr_eq_some {lays : AllocLayouts} {l limit b : Nat} :
    localBaseAddr lays l limit = some b ↔
      ∃ cur, baseScan limit synthPage (lays.take l) = some cur ∧
        b = ownAlignedCursor lays l cur + (l - lays.length) * synthPage ∧
        b + ownAllocSize lays l ≤ limit := by
  unfold localBaseAddr
  cases hS : baseScan limit synthPage (lays.take l) with
  | none => simp
  | some cur =>
    by_cases hc : limit < ownAlignedCursor lays l cur + (l - lays.length) * synthPage +
        ownAllocSize lays l
    · simp only [hc, ↓reduceIte, reduceCtorEq, false_iff, not_exists, not_and, Option.some.injEq]
      intro c hc' hb
      subst hc'
      omega
    · simp only [hc, ↓reduceIte, Option.some.injEq]
      constructor
      · intro h
        exact ⟨cur, rfl, h.symm, by omega⟩
      · rintro ⟨c, hc', hb, _⟩
        cases hc'
        exact hb.symm

/-- The aligned cursor is at least the cursor. -/
theorem le_ownAlignedCursor (lays : AllocLayouts) (l cur : Nat) : cur ≤ ownAlignedCursor lays l cur := by
  unfold ownAlignedCursor
  split
  · split
    · exact alignUp_ge _ _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- A positive value rounds up to at least the alignment. -/
theorem alignUp_ge_align {x a : Nat} (hx : 0 < x) (ha : 0 < a) : a ≤ PlaceAndRvalue.alignUp x a := by
  have hDvd := alignUp_dvd x a ha
  have hGe := alignUp_ge x a
  exact Nat.le_of_dvd (by omega) hDvd

/-- A size of at most one page (and at least one byte) rounds up to exactly one page. -/
theorem alignUp_page_of_le {x : Nat} (h1 : 1 ≤ x) (h2 : x ≤ synthPage) :
    PlaceAndRvalue.alignUp x synthPage = synthPage := by
  rw [synthPage_eq] at *
  unfold PlaceAndRvalue.alignUp roundUpToAlign
  cases hB : Nat.beq (Nat.mod x 4096) 0 with
  | true =>
    have hM : x % 4096 = 0 := Nat.eq_of_beq_eq_true hB
    show x = 4096
    omega
  | false =>
    have hM : x % 4096 ≠ 0 := Nat.ne_of_beq_eq_false hB
    show x + (4096 - x % 4096) = 4096
    omega

/-- Every scan step advances the cursor by at least one page. -/
theorem baseScanStep_ge (cur : Nat) (x : Option (Nat × Nat)) : cur + synthPage ≤ baseScanStep cur x := by
  cases x with
  | none => exact Nat.le_refl _
  | some p =>
    obtain ⟨s, a⟩ := p
    have h1 := alignUp_ge cur (max a synthPage)
    have h2 := alignUp_ge_align (x := max s 1) (a := synthPage) (by omega) synthPage_pos
    simp only [baseScanStep]
    omega

/-- The scan of a concatenation is the scan of the suffix from the scan of the prefix. -/
theorem baseScan_append (limit : Nat) :
    ∀ (cur : Nat) (xs ys : AllocLayouts),
      baseScan limit cur (xs ++ ys) = (baseScan limit cur xs).bind (fun c => baseScan limit c ys)
  | cur, [], ys => rfl
  | cur, x :: xs, ys => by
    simp only [List.cons_append, baseScan]
    split
    · rfl
    · exact baseScan_append limit _ xs ys

/-- The scan never moves the cursor backwards. -/
theorem baseScan_ge {limit : Nat} :
    ∀ {cur cur' : Nat} {xs : AllocLayouts}, baseScan limit cur xs = some cur' → cur ≤ cur'
  | cur, cur', [], h => by simp only [baseScan, Option.some.injEq] at h; omega
  | cur, cur', x :: xs, h => by
    simp only [baseScan] at h
    split at h
    · nomatch h
    · have := baseScan_ge h
      have := baseScanStep_ge cur x
      omega

/-- **No masking (`localBaseAddr_fits`)**: a successful base address leaves room for the whole
synthetic allocation of the local below `limit`. -/
theorem localBaseAddr_fits {lays : AllocLayouts} {l limit b : Nat}
    (h : localBaseAddr lays l limit = some b) : b + ownAllocSize lays l ≤ limit := by
  obtain ⟨_, _, _, hFit⟩ := localBaseAddr_eq_some.mp h
  exact hFit

/-- Splitting a prefix of a list at an inner index. -/
theorem take_split_getElem {α : Type} :
    ∀ (l : List α) (i j : Nat) (_ : i < j) (hil : i < l.length),
      l.take j = l.take i ++ l[i] :: (l.drop (i + 1)).take (j - i - 1)
  | [], _, _, _, hil => absurd hil (by simp)
  | _ :: _, _, 0, hij, _ => absurd hij (by omega)
  | x :: xs, 0, j + 1, _, _ => by simp
  | x :: xs, i + 1, j + 1, hij, hil => by
    have ih := take_split_getElem xs i j (by omega) (by simpa using hil)
    simp only [List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons, List.cons_append]
    rw [ih, show j + 1 - (i + 1) - 1 = j - i - 1 by omega]

/-- **Collision-free synthetic allocations (`localBaseAddr_disjoint`)**: the synthetic
allocations `[base, base + size)` of two distinct locals never overlap — every earlier local's
allocation ends at or before a later local's base address, and distinct locals (even
zero-sized ones) have distinct base addresses. -/
theorem localBaseAddr_disjoint {lays : AllocLayouts} {i j limit bi bj : Nat} (hij : i < j)
    (hi : localBaseAddr lays i limit = some bi) (hj : localBaseAddr lays j limit = some bj) :
    bi + ownAllocSize lays i ≤ bj ∧ bi < bj := by
  obtain ⟨ci, hci, hbi, _⟩ := localBaseAddr_eq_some.mp hi
  obtain ⟨cj, hcj, hbj, _⟩ := localBaseAddr_eq_some.mp hj
  have hCj : cj ≤ bj := by have := le_ownAlignedCursor lays j cj; omega
  by_cases hil : i < lays.length
  · -- `lays.take j = lays.take i ++ lays[i] :: rest`: the scan for `j` passes over `i`
    rw [take_split_getElem lays i j hij hil, baseScan_append, hci] at hcj
    simp only [Option.bind_some, baseScan] at hcj
    split at hcj
    · nomatch hcj
    · have hStepLe := baseScan_ge hcj
      have hOwn : ownLayout lays i = lays[i] := by
        simp [ownLayout, List.getElem?_eq_getElem hil]
      rw [show i - lays.length = 0 by omega, Nat.zero_mul, Nat.add_zero] at hbi
      subst hbi
      unfold ownAllocSize ownAlignedCursor
      rw [hOwn]
      cases hx : lays[i] with
      | none =>
        rw [hx] at hStepLe
        simp only [baseScanStep] at hStepLe
        simp only [Option.map_none, Option.getD_none]
        have := synthPage_pos
        omega
      | some p =>
        obtain ⟨s, a⟩ := p
        rw [hx] at hStepLe
        simp only [baseScanStep] at hStepLe
        simp only [Option.map_some, Option.getD_some]
        have hSz := alignUp_ge (max s 1) synthPage
        have hSzPos := alignUp_ge_align (x := max s 1) (a := synthPage) (by omega) synthPage_pos
        split
        · rename_i hBig
          rw [show max a synthPage = a by omega] at hStepLe
          omega
        · have := alignUp_ge ci (max a synthPage)
          omega
  · -- both locals lie beyond the declarations
    have hTi : lays.take i = lays := List.take_of_length_le (by omega)
    have hTj : lays.take j = lays := List.take_of_length_le (by omega)
    rw [hTi] at hci
    rw [hTj, hci] at hcj
    cases hcj
    have hNi : ownLayout lays i = none := by
      simp [ownLayout, List.getElem?_eq_none (by omega : lays.length ≤ i)]
    have hNj : ownLayout lays j = none := by
      simp [ownLayout, List.getElem?_eq_none (by omega : lays.length ≤ j)]
    simp only [ownAlignedCursor, hNi, hNj] at hbi hbj
    simp only [ownAllocSize, hNi, Option.map_none, Option.getD_none]
    have : (i - lays.length) * synthPage + synthPage ≤ (j - lays.length) * synthPage := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    have := synthPage_pos
    omega

/-- Scanning locals that each fit in one page advances the cursor by exactly one page per local. -/
theorem baseScan_small {limit : Nat} :
    ∀ (n : Nat) (xs : AllocLayouts),
      (∀ x ∈ xs, ∀ s a, x = some (s, a) → s ≤ synthPage ∧ a ≤ synthPage) →
      (n + 1 + xs.length) * synthPage ≤ limit →
      baseScan limit ((n + 1) * synthPage) xs = some ((n + 1 + xs.length) * synthPage)
  | n, [], _, _ => rfl
  | n, x :: xs, hS, hL => by
    have hStep : baseScanStep ((n + 1) * synthPage) x = (n + 1 + 1) * synthPage := by
      rw [Nat.add_one_mul (n + 1)]
      cases x with
      | none => rfl
      | some p =>
        obtain ⟨s, a⟩ := p
        obtain ⟨hs, ha⟩ := hS (some (s, a)) (List.mem_cons_self ..) s a rfl
        have hP := synthPage_pos
        have hM : max a synthPage = synthPage := by omega
        have hA1 : PlaceAndRvalue.alignUp ((n + 1) * synthPage) synthPage = (n + 1) * synthPage :=
          alignUp_eq_self_of_mod_zero (Nat.mul_mod_left (n + 1) synthPage)
        have hA2 : PlaceAndRvalue.alignUp (max s 1) synthPage = synthPage :=
          alignUp_page_of_le (by omega) (by omega)
        show PlaceAndRvalue.alignUp ((n + 1) * synthPage) (max a synthPage) +
          PlaceAndRvalue.alignUp (max s 1) synthPage = (n + 1) * synthPage + synthPage
        rw [hM, hA1, hA2]
    have hLen : (x :: xs).length = xs.length + 1 := rfl
    rw [hLen, show n + 1 + (xs.length + 1) = n + 1 + 1 + xs.length by omega] at hL
    have ih := baseScan_small (n + 1) xs (fun y hy => hS y (List.mem_cons_of_mem _ hy)) hL
    have hLe : (n + 1 + 1) * synthPage ≤ (n + 1 + 1 + xs.length) * synthPage :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [baseScan, hStep]
    have hNot : ¬ limit < (n + 1 + 1) * synthPage := by omega
    simp only [hNot, ↓reduceIte]
    rw [ih, hLen, show n + 1 + (xs.length + 1) = n + 1 + 1 + xs.length by omega]

/-- **Page-per-local layout (`localBaseAddr_small`)**: when every preceding local fits in one page
(size and alignment at most `0x1000`, or a layout error) and the local's own alignment is at most
a page, the synthetic base address is the legacy `(local + 1) * 0x1000`. -/
theorem localBaseAddr_small {lays : AllocLayouts} {l limit : Nat}
    (hSmall : ∀ x ∈ lays.take l, ∀ s a, x = some (s, a) → s ≤ synthPage ∧ a ≤ synthPage)
    (hOwn : ∀ s a, ownLayout lays l = some (s, a) → a ≤ synthPage)
    (hFit : (l + 1) * synthPage + ownAllocSize lays l ≤ limit) :
    localBaseAddr lays l limit = some ((l + 1) * synthPage) := by
  have hLen : (lays.take l).length = min l lays.length := List.length_take ..
  have hMul : (0 + 1 + (lays.take l).length) * synthPage ≤ (l + 1) * synthPage :=
    Nat.mul_le_mul_right _ (by rw [hLen]; omega)
  have hScan := baseScan_small (limit := limit) 0 (lays.take l) hSmall (by omega)
  rw [Nat.zero_add, Nat.one_mul] at hScan
  have hCur : ownAlignedCursor lays l ((1 + (lays.take l).length) * synthPage) =
      (1 + (lays.take l).length) * synthPage := by
    unfold ownAlignedCursor
    cases hO : ownLayout lays l with
    | none => rfl
    | some p =>
      obtain ⟨s, a⟩ := p
      have := hOwn s a hO
      have hNot : ¬ synthPage < a := by omega
      simp only [hNot, ↓reduceIte]
  have hEq : (1 + (lays.take l).length) * synthPage + (l - lays.length) * synthPage =
      (l + 1) * synthPage := by
    rw [← Nat.add_mul, hLen]
    congr 1
    omega
  refine localBaseAddr_eq_some.mpr ⟨_, hScan, ?_, ?_⟩
  · rw [hCur, hEq]
  · exact hFit

/-- Alignments the scan keeps page-aligned: at most a page (powers of two dividing `0x1000`), or a
multiple of a page. -/
def PageCompatAlign (a : Nat) : Prop := a ≤ synthPage ∨ synthPage ∣ a

theorem dvd_max_page {a : Nat} (h : PageCompatAlign a) : synthPage ∣ max a synthPage := by
  rcases h with h | h
  · rw [show max a synthPage = synthPage by omega]
    exact Nat.dvd_refl _
  · by_cases ha : synthPage ≤ a
    · rw [show max a synthPage = a by omega]
      exact h
    · rw [show max a synthPage = synthPage by omega]
      exact Nat.dvd_refl _

/-- The scan keeps a page-aligned cursor page-aligned. -/
theorem baseScan_page_dvd {limit : Nat} :
    ∀ {cur cur' : Nat} {xs : AllocLayouts},
      (∀ x ∈ xs, ∀ s a, x = some (s, a) → PageCompatAlign a) →
      synthPage ∣ cur → baseScan limit cur xs = some cur' → synthPage ∣ cur'
  | cur, cur', [], _, hc, h => by
    simp only [baseScan, Option.some.injEq] at h
    subst h
    exact hc
  | cur, cur', x :: xs, hA, hc, h => by
    simp only [baseScan] at h
    split at h
    · nomatch h
    · refine baseScan_page_dvd (fun y hy => hA y (List.mem_cons_of_mem _ hy)) ?_ h
      cases x with
      | none => exact Nat.dvd_add hc (Nat.dvd_refl _)
      | some p =>
        obtain ⟨s, a⟩ := p
        have hPC := hA (some (s, a)) (List.mem_cons_self ..) s a rfl
        have hMaxPos : 0 < max a synthPage := by have := synthPage_pos; omega
        simp only [baseScanStep]
        exact Nat.dvd_add (Nat.dvd_trans (dvd_max_page hPC) (alignUp_dvd _ _ hMaxPos))
          (alignUp_dvd _ _ synthPage_pos)

/-- **Page-aligned bases (`localBaseAddr_page_dvd`)**: with page-compatible alignments (every
power of two is), every synthetic base address is a multiple of `0x1000`. -/
theorem localBaseAddr_page_dvd {lays : AllocLayouts} {l limit b : Nat}
    (hPre : ∀ x ∈ lays.take l, ∀ s a, x = some (s, a) → PageCompatAlign a)
    (hOwn : ∀ s a, ownLayout lays l = some (s, a) → PageCompatAlign a)
    (h : localBaseAddr lays l limit = some b) : synthPage ∣ b := by
  obtain ⟨cur, hScan, hb, _⟩ := localBaseAddr_eq_some.mp h
  have hCur := baseScan_page_dvd hPre (Nat.dvd_refl _) hScan
  subst hb
  refine Nat.dvd_add ?_ (Nat.dvd_mul_left _ _)
  unfold ownAlignedCursor
  split
  · rename_i s a hO
    split
    · rename_i hBig
      rcases hOwn s a hO with hPC | hPC
      · omega
      · exact Nat.dvd_trans hPC (alignUp_dvd _ _ (by omega))
    · exact hCur
  · exact hCur

/-- **Over-aligned locals (`localBaseAddr_align_dvd`)**: a local whose alignment exceeds a page is
placed at a multiple of its alignment (unconditionally). -/
theorem localBaseAddr_align_dvd {lays : AllocLayouts} {l limit b s a : Nat}
    (hOwn : ownLayout lays l = some (s, a)) (hBig : synthPage < a)
    (h : localBaseAddr lays l limit = some b) : a ∣ b := by
  have hl : l < lays.length := by
    rcases Nat.lt_or_ge l lays.length with hl | hl
    · exact hl
    · simp [ownLayout, List.getElem?_eq_none hl] at hOwn
  obtain ⟨cur, _, hb, _⟩ := localBaseAddr_eq_some.mp h
  subst hb
  rw [show l - lays.length = 0 by omega, Nat.zero_mul, Nat.add_zero]
  unfold ownAlignedCursor
  rw [hOwn]
  simp only [hBig, ↓reduceIte]
  exact alignUp_dvd _ _ (by omega)

/-- **A base is aligned for its own (page-compatible) alignment**: an alignment dividing the page
divides every page-aligned base, and a larger one is honored explicitly. -/
theorem localBaseAddr_aligned {lays : AllocLayouts} {l limit b s a : Nat}
    (hPre : ∀ x ∈ lays.take l, ∀ s a, x = some (s, a) → PageCompatAlign a)
    (hOwn : ownLayout lays l = some (s, a)) (hA : a ∣ synthPage ∨ synthPage < a)
    (h : localBaseAddr lays l limit = some b) : a ∣ b := by
  rcases hA with hA | hA
  · have hPC : PageCompatAlign a := Or.inl (Nat.le_of_dvd synthPage_pos hA)
    exact Nat.dvd_trans hA (localBaseAddr_page_dvd hPre (fun s' a' h' => by
      rw [hOwn] at h'; cases h'; exact hPC) h)
  · exact localBaseAddr_align_dvd hOwn hA h

/-- **Concrete collision-freedom witness**: in a frame `[u32, [u8; 8192], u8]` the two-page local
`_1` lives at `0x2000` and `_2` at `0x4000`, past `_1`'s allocation `[0x2000, 0x4000)`; the legacy
`(local + 1) * 0x1000` scheme would have put `_2` at `0x3000`, inside `_1`. -/
theorem localBaseAddr_example_two_page_local :
    localBaseAddr [some (4, 4), some (8192, 1), some (1, 1)] 0 (2 ^ 64 - 1) = some 0x1000 ∧
    localBaseAddr [some (4, 4), some (8192, 1), some (1, 1)] 1 (2 ^ 64 - 1) = some 0x2000 ∧
    localBaseAddr [some (4, 4), some (8192, 1), some (1, 1)] 2 (2 ^ 64 - 1) = some 0x4000 ∧
    0x2000 < (2 + 1) * synthPage + 1 ∧ (2 + 1) * synthPage < 0x2000 + 8192 := by
  with_unfolding_all decide

/-- **Fail closed without masking**: an allocation that does not fit the address space has no
synthetic base address (`UnsupportedMemoryAccess`), instead of a wrapped one. -/
theorem localBaseAddr_example_overflow_none :
    localBaseAddr [some (2 ^ 64, 1)] 0 (2 ^ 64 - 1) = none ∧
    localBaseAddr [some (2 ^ 63, 1), some (2 ^ 63, 1)] 1 (2 ^ 64 - 1) = none := by
  with_unfolding_all decide

/-! ### Section 4b: Layout-offset sub-place ranges and synthetic sub-place borrows -/

/-- The sub-layout and absolute byte offset reached by a projection inside a layout rooted at
`base` (`compute_subplace_offset_and_tag`'s offset): `Field` selects a struct/tuple/variant field,
a forward `ConstantIndex` selects an array element (an array of `n` elements is laid out as a
`ByteLayout.struct` of its elements), and `Downcast` keeps the offset (the variant's fields are
laid out in the enum's layout tree); `Deref`, `Index`, `Subslice`, and backward `ConstantIndex`
have no static synthetic offset. -/
def subplaceAt : ByteLayout → Nat → List ProjectionElem → Option (ByteLayout × Nat)
  | lay, base, [] => some (lay, base)
  | lay, base, .downcast _ _ :: rest => subplaceAt lay base rest
  | .struct _ offs ls, base, .field f _ :: rest =>
    match offs[f]?, ls[f]? with
    | some o, some l => subplaceAt l (base + o) rest
    | _, _ => none
  | .struct _ offs ls, base, .constantIndex k _ false :: rest =>
    match offs[k]?, ls[k]? with
    | some o, some l => subplaceAt l (base + o) rest
    | _, _ => none
  | _, _, _ :: _ => none

/-- **`computeSubplaceByteOffset`**: the byte range `(offset, size)` of the sub-place `proj` inside
a local of byte layout `lay`. -/
def computeSubplaceByteOffset (lay : ByteLayout) (proj : List ProjectionElem) : Option (Nat × Nat) :=
  (subplaceAt lay 0 proj).map fun r => (r.2, r.1.size)

/-- A sub-place lies inside its container, and its sub-layout is well formed. -/
theorem subplaceAt_sub :
    ∀ {lay : ByteLayout} {base : Nat} {p : List ProjectionElem} {l : ByteLayout} {o : Nat},
      lay.WF → subplaceAt lay base p = some (l, o) → l.WF ∧ base ≤ o ∧ o + l.size ≤ base + lay.size
  | lay, base, [], l, o, hWF, h => by
    simp only [subplaceAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hWF, Nat.le_refl _, Nat.le_refl _⟩
  | lay, base, .downcast _ _ :: rest, l, o, hWF, h => by
    simp only [subplaceAt] at h
    exact subplaceAt_sub hWF h
  | .leaf _, _, .field _ _ :: _, _, _, _, h => by simp [subplaceAt] at h
  | .leaf _, _, .constantIndex _ _ _ :: _, _, _, _, h => by simp [subplaceAt] at h
  | .struct n offs ls, base, .field f _ :: rest, l, o, hWF, h => by
    simp only [subplaceAt] at h
    split at h
    · rename_i o' l' ho hl
      cases hWF with
      | struct _ _ _ hLen hFit hDisj hChildren =>
        have ih := subplaceAt_sub (hChildren f l' hl) h
        have := hFit f o' l' ho hl
        have hn : (ByteLayout.struct n offs ls).size = n := rfl
        rw [hn]
        exact ⟨ih.1, by omega, by omega⟩
    · nomatch h
  | .struct n offs ls, base, .constantIndex k _ fromEnd :: rest, l, o, hWF, h => by
    cases fromEnd with
    | true => simp [subplaceAt] at h
    | false =>
      simp only [subplaceAt] at h
      split at h
      · rename_i o' l' ho hl
        cases hWF with
        | struct _ _ _ hLen hFit hDisj hChildren =>
          have ih := subplaceAt_sub (hChildren k l' hl) h
          have := hFit k o' l' ho hl
          have hn : (ByteLayout.struct n offs ls).size = n := rfl
          rw [hn]
          exact ⟨ih.1, by omega, by omega⟩
      · nomatch h
  | _, _, .deref :: _, _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h
  | _, _, .index _ :: _, _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h
  | _, _, .subslice _ _ _ :: _, _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h
  | _, _, .opaqueCast _ :: _, _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h
  | _, _, .unwrapUnsafeBinder _ :: _, _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h

/-- A projection step that selects child `i` of a struct/tuple/array layout: `Field(i)` or a
forward `ConstantIndex(i)`. -/
def SelectsChild (e : ProjectionElem) (i : Nat) : Prop :=
  (∃ ty, e = .field i ty) ∨ (∃ m, e = .constantIndex i m false)

/-- One child-selecting step from a struct layout. -/
theorem subplaceAt_struct_child {n : Nat} {offs : List Nat} {ls : List ByteLayout} {base : Nat}
    {e : ProjectionElem} {i : Nat} (he : SelectsChild e i) {r : List ProjectionElem}
    {l : ByteLayout} {o : Nat} (h : subplaceAt (.struct n offs ls) base (e :: r) = some (l, o)) :
    ∃ oi li, offs[i]? = some oi ∧ ls[i]? = some li ∧ subplaceAt li (base + oi) r = some (l, o) := by
  rcases he with ⟨ty, rfl⟩ | ⟨m, rfl⟩
  all_goals
    simp only [subplaceAt] at h
    split at h
    · rename_i oi li ho hl
      exact ⟨oi, li, ho, hl, h⟩
    · nomatch h

/-- Extending a resolved sub-place resolves the extension inside its sub-layout. -/
theorem subplaceAt_append :
    ∀ {lay : ByteLayout} {base : Nat} {p : List ProjectionElem} {l : ByteLayout} {o : Nat}
      (q : List ProjectionElem),
      subplaceAt lay base p = some (l, o) → subplaceAt lay base (p ++ q) = subplaceAt l o q
  | lay, base, [], l, o, q, h => by
    simp only [subplaceAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | lay, base, .downcast _ _ :: rest, l, o, q, h => by
    simp only [subplaceAt] at h
    simp only [List.cons_append, subplaceAt]
    exact subplaceAt_append q h
  | .leaf _, _, .field _ _ :: _, _, _, _, h => by simp [subplaceAt] at h
  | .leaf _, _, .constantIndex _ _ _ :: _, _, _, _, h => by simp [subplaceAt] at h
  | .struct n offs ls, base, .field f ty :: rest, l, o, q, h => by
    obtain ⟨o', l', ho, hl, h'⟩ := subplaceAt_struct_child (Or.inl ⟨ty, rfl⟩) h
    simp only [List.cons_append, subplaceAt, ho, hl]
    exact subplaceAt_append q h'
  | .struct n offs ls, base, .constantIndex k m fromEnd :: rest, l, o, q, h => by
    cases fromEnd with
    | true => simp [subplaceAt] at h
    | false =>
      obtain ⟨o', l', ho, hl, h'⟩ := subplaceAt_struct_child (Or.inr ⟨m, rfl⟩) h
      simp only [List.cons_append, subplaceAt, ho, hl]
      exact subplaceAt_append q h' 
  | _, _, .deref :: _, _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h
  | _, _, .index _ :: _, _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h
  | _, _, .subslice _ _ _ :: _, _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h
  | _, _, .opaqueCast _ :: _, _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h
  | _, _, .unwrapUnsafeBinder _ :: _, _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h

/-- **Disjoint siblings (`subplaceAt_disjoint_siblings`)**: on a well-formed layout, two
sub-places diverging at distinct fields or elements `i ≠ j` of the same struct/tuple/array occupy
disjoint byte ranges (the byte-level Disjoint-Sibling frame of synthetic sub-place pointers). -/
theorem subplaceAt_disjoint_siblings {lay : ByteLayout} {base : Nat} {p : List ProjectionElem}
    {n : Nat} {offs : List Nat} {ls : List ByteLayout} {o : Nat} (hWF : lay.WF)
    (hp : subplaceAt lay base p = some (.struct n offs ls, o))
    {e₁ e₂ : ProjectionElem} {i j : Nat} (hi : SelectsChild e₁ i) (hj : SelectsChild e₂ j)
    (hij : i ≠ j) {r₁ r₂ : List ProjectionElem} {l₁ l₂ : ByteLayout} {o₁ o₂ : Nat}
    (h₁ : subplaceAt lay base (p ++ e₁ :: r₁) = some (l₁, o₁))
    (h₂ : subplaceAt lay base (p ++ e₂ :: r₂) = some (l₂, o₂)) :
    o₁ + l₁.size ≤ o₂ ∨ o₂ + l₂.size ≤ o₁ := by
  rw [subplaceAt_append _ hp] at h₁ h₂
  obtain ⟨hSWF, _, _⟩ := subplaceAt_sub hWF hp
  obtain ⟨oi, li, hoi, hli, hr₁⟩ := subplaceAt_struct_child hi h₁
  obtain ⟨oj, lj, hoj, hlj, hr₂⟩ := subplaceAt_struct_child hj h₂
  cases hSWF with
  | struct _ _ _ hLen hFit hDisj hChildren =>
    obtain ⟨_, hA₁, hB₁⟩ := subplaceAt_sub (hChildren i li hli) hr₁
    obtain ⟨_, hA₂, hB₂⟩ := subplaceAt_sub (hChildren j lj hlj) hr₂
    rcases hDisj i j oi oj li lj hij hoi hoj hli hlj with hD | hD <;> omega

/-- **Agreement with `pathRange`**: every `Field` / `Downcast`+`Field` byte range of Section 2e
(`pathRange`, used by `evalDeinitPlace_spec_bytes_simulation`) is the synthetic sub-place range
`subplaceAt` assigns to the same path, so synthetic sub-place pointers and MiniRust's byte-level
`Deinit` address the same bytes. -/
theorem subplaceAt_of_pathRange :
    ∀ {lay : ByteLayout} {base : Nat} {p : List ProjectionElem} {off len : Nat},
      pathRange lay base p = some (off, len) → ∃ l, subplaceAt lay base p = some (l, off) ∧ l.size = len
  | lay, base, [], off, len, h => by
    simp only [pathRange, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨lay, rfl, rfl⟩
  | .leaf _, _, e :: rest, _, _, h => by
    cases e with
    | downcast _ _ => cases rest with
      | nil => simp [pathRange] at h
      | cons b _ => cases b <;> simp [pathRange] at h
    | _ => simp [pathRange] at h
  | .struct n offs ls, base, .field f _ :: rest, off, len, h => by
    simp only [pathRange] at h
    split at h
    · rename_i o l ho hl
      obtain ⟨l', h', hs⟩ := subplaceAt_of_pathRange h
      exact ⟨l', by simp only [subplaceAt, ho, hl, h'], hs⟩
    · nomatch h
  | .struct n offs ls, base, .downcast _ _ :: rest, off, len, h => by
    cases rest with
    | nil => simp [pathRange] at h
    | cons b rest' =>
      cases b with
      | field f ty =>
        simp only [pathRange] at h
        split at h
        · rename_i o l ho hl
          obtain ⟨l', h', hs⟩ := subplaceAt_of_pathRange h
          exact ⟨l', by simp only [subplaceAt, ho, hl, h'], hs⟩
        · nomatch h
      | _ => simp [pathRange] at h
  | .struct _ _ _, _, .deref :: _, _, _, h => by simp [pathRange] at h
  | .struct _ _ _, _, .index _ :: _, _, _, h => by simp [pathRange] at h
  | .struct _ _ _, _, .constantIndex _ _ _ :: _, _, _, h => by simp [pathRange] at h
  | .struct _ _ _, _, .subslice _ _ _ :: _, _, _, h => by simp [pathRange] at h
  | .struct _ _ _, _, .opaqueCast _ :: _, _, _, h => by simp [pathRange] at h
  | .struct _ _ _, _, .unwrapUnsafeBinder _ :: _, _, _, h => by simp [pathRange] at h

/-- Layout facts of a type that synthetic pointer resolution consults (`align_bounds`,
`alloc_size_and_align`, `layout_for`, `is_inhabited_for`): the (upper-bound) size, the minimum and
maximum alignment, whether the layout is exact, and inhabitedness. -/
structure TyLayout : Type where
  size : Nat
  minAlign : Nat
  maxAlign : Nat
  exact : Bool
  inhabited : Bool

/-- The type of a pointer value (`ptr_ty`): a reference (`&T` / `&mut T`) or a raw pointer, and
its pointee type (by identity). -/
structure PtrTy : Type where
  isRef : Bool
  pointee : Nat

/-- A synthetic pointer value (`PointerValue`): an address and an optional provenance
`(alloc_id, tag)`. -/
structure SynPtr : Type where
  addr : Nat
  prov : Option (Nat × Nat)
  deriving DecidableEq

/-- **`encode_subplace_tag` (`rvalue.rs:9771-9780`)**: packs the 32-bit type fingerprint `fp ty`
into the high 32 bits and `ordinal + 2` into the low 32 bits (returning the default untagged
provenance tag `1` when `ordinal + 2 ≥ 2^32`). -/
def encodeSubplaceTag (fp : Nat → Nat) (ty ordinal : Nat) : Nat :=
  if ordinal + 2 < 2 ^ 32 then fp ty * (2 ^ 32) + (ordinal + 2)
  else 1

/-- **`decode_subplace_tag` (`rvalue.rs:9782-9792`)**: recovers `some ordinal` iff the low 32 bits
are `≥ 2` and the high 32 bits match `fp ty`. -/
def decodeSubplaceTag (fp : Nat → Nat) (tag ty : Nat) : Option Nat :=
  let low := tag % (2 ^ 32)
  let high := tag / (2 ^ 32)
  if low < 2 then none
  else if high ≠ fp ty then none
  else some (low - 2)

/-- **Type-fingerprinted sub-place tag round-trip (`decodeSubplaceTag_encodeSubplaceTag_same`)**:
decoding an encoded sub-place tag at the same pointee type `ty` recovers `some ordinal` whenever
`ordinal + 2 < 2^32`. -/
theorem decodeSubplaceTag_encodeSubplaceTag_same (fp : Nat → Nat) (ty ordinal : Nat)
    (hOrd : ordinal + 2 < 2 ^ 32) :
    decodeSubplaceTag fp (encodeSubplaceTag fp ty ordinal) ty = some ordinal := by
  simp only [encodeSubplaceTag, decodeSubplaceTag, hOrd, ↓reduceIte]
  have hLow : (fp ty * 2 ^ 32 + (ordinal + 2)) % 2 ^ 32 = ordinal + 2 := by omega
  have hHigh : (fp ty * 2 ^ 32 + (ordinal + 2)) / 2 ^ 32 = fp ty := by omega
  have hNotLt : ¬ (ordinal + 2 < 2) := by omega
  simp [hLow, hHigh, hNotLt]

/-- **Default untagged provenance `1` never decodes (`decodeSubplaceTag_tag_one_none`)**. -/
theorem decodeSubplaceTag_tag_one_none (fp : Nat → Nat) (ty : Nat) :
    decodeSubplaceTag fp 1 ty = none := by
  simp [decodeSubplaceTag]

/-- **Cast-pointer fingerprint mismatch (`decodeSubplaceTag_mismatch_none`)**: when a pointer
created for type `ty₁` is cast and dereferenced as `ty₂` with `fp ty₁ ≠ fp ty₂`,
`decodeSubplaceTag` returns `none` so `resolveSyntheticSubplace` never misuses `ty₁`'s candidate
ordinal to index `ty₂`'s candidate list. -/
theorem decodeSubplaceTag_mismatch_none (fp : Nat → Nat) (ty₁ ty₂ ordinal : Nat)
    (hFp : fp ty₁ ≠ fp ty₂) :
    decodeSubplaceTag fp (encodeSubplaceTag fp ty₁ ordinal) ty₂ = none := by
  by_cases hOrd : ordinal + 2 < 2 ^ 32
  · simp only [encodeSubplaceTag, decodeSubplaceTag, hOrd, ↓reduceIte]
    have hLow : (fp ty₁ * 2 ^ 32 + (ordinal + 2)) % 2 ^ 32 = ordinal + 2 := by omega
    have hHigh : (fp ty₁ * 2 ^ 32 + (ordinal + 2)) / 2 ^ 32 = fp ty₁ := by omega
    have hNotLt : ¬ (ordinal + 2 < 2) := by omega
    simp [hLow, hHigh, hNotLt, hFp]
  · simp [encodeSubplaceTag, decodeSubplaceTag, hOrd]

/-- The frame-independent context of synthetic sub-place pointers: allocation layouts and the
address-space limit (for `localBaseAddr`), byte layouts of the declared locals, type identities
of the declared locals and the same-offset/same-type candidate paths (`collect_subplace_paths`),
type layouts, the pointer type stored at every `Deref`-free place, Anneal's synthetic reading of
a pointer value (`addr`, `provenance`), `decode_subplace_tag`, `slot_union_path_active`, and
`encode_subplace_tag` (`encodeTag ty ordinal`, by pointee type identity; it defaults to the
untagged provenance tag `1`). -/
structure SubplaceCtx : Type where
  allocs : AllocLayouts
  limit : Nat
  layoutOf : Nat → Option ByteLayout
  declTy : Nat → Option Nat
  candidates : Nat → Nat → Nat → List (List ProjectionElem)
  tyLayout : Nat → Option TyLayout
  ptrTyAt : Nat → List ProjectionElem → Option PtrTy
  ptrOf : ProvenancePtr → SynPtr
  decodeTag : Nat → Nat → Option Nat
  unionActive : LocalSlotState → List ProjectionElem → Bool → Bool := fun _ _ _ => true
  encodeTag : Nat → Nat → Nat := fun _ _ => 1

/-- Well-formed contexts: every local's byte layout is well formed and fits its synthetic
allocation, and every candidate path of a pointee type at offset `off` of local `l` addresses a
sub-place of that type's size at `off` (the specification of `collect_subplace_paths`). -/
structure SubplaceCtx.WF (cx : SubplaceCtx) : Prop where
  layout : ∀ l lay, cx.layoutOf l = some lay → lay.WF ∧ lay.size ≤ ownAllocSize cx.allocs l
  candidates : ∀ t l off q, q ∈ cx.candidates t l off →
    ∃ lay sub tl, cx.layoutOf l = some lay ∧ subplaceAt lay 0 q = some (sub, off) ∧
      cx.tyLayout t = some tl ∧ sub.size = tl.size

/-- Errors of synthetic pointer evaluation (`RvalueEvalError` variants of `rvalue.rs`). -/
inductive DerefErr : Type where
  | invalidBitPattern
  | nullPointer
  | misaligned
  | unsupportedLayout
  | uninhabited
  | rangeOverflow
  | deadLocal (l : Nat)
  | ub
  | unsupported
  | typeMismatch
  deriving DecidableEq, Repr

/-- **Synthetic sub-place borrow (`evalSubplaceRef`)**: `&_l.proj` / `&raw _l.proj` (the
`Deref`-free branch of `eval_projected_ref_in`): a live local (`DeadLocal` otherwise) whose runtime
state accepts the projection (`check_slot_projection`: active variants, in-bounds elements), at
address `localBaseAddr l + offset(proj)` with provenance `(l + 1, tag)`. An uninitialized local
can be borrowed (the place itself is never read). -/
def evalSubplaceRef (cx : SubplaceCtx) (slots : List LocalSlotState) (l : Nat)
    (proj : List ProjectionElem) (tag : Nat) : Except DerefErr SynPtr :=
  match slots[l]? with
  | none => .error .typeMismatch
  | some .dead => .error (.deadLocal l)
  | some st =>
    if checkSlotProjectionOk (slotsToTrustedLocals slots) (slotStateToFieldSlot st) proj then
      match cx.layoutOf l, localBaseAddr cx.allocs l cx.limit with
      | some lay, some base =>
        match subplaceAt lay 0 proj with
        | some (_, off) => .ok ⟨base + off, some (l + 1, tag)⟩
        | none => .error .unsupported
      | _, _ => .error .unsupported
    else .error .unsupported

/-- A borrow of a sub-place of a dead local faults (`DeadLocal`). -/
theorem evalSubplaceRef_dead {cx : SubplaceCtx} {slots : List LocalSlotState} {l : Nat}
    (proj : List ProjectionElem) (tag : Nat) (h : slots[l]? = some .dead) :
    evalSubplaceRef cx slots l proj tag = .error (.deadLocal l) := by
  simp [evalSubplaceRef, h]

/-- Inversion of a successful synthetic sub-place borrow. -/
theorem evalSubplaceRef_eq_ok {cx : SubplaceCtx} {slots : List LocalSlotState} {l : Nat}
    {proj : List ProjectionElem} {tag : Nat} {p : SynPtr}
    (h : evalSubplaceRef cx slots l proj tag = .ok p) :
    ∃ st lay base sub off, slots[l]? = some st ∧ st ≠ .dead ∧
      checkSlotProjectionOk (slotsToTrustedLocals slots) (slotStateToFieldSlot st) proj = true ∧
      cx.layoutOf l = some lay ∧ localBaseAddr cx.allocs l cx.limit = some base ∧
      subplaceAt lay 0 proj = some (sub, off) ∧ p = ⟨base + off, some (l + 1, tag)⟩ := by
  unfold evalSubplaceRef at h
  split at h
  · nomatch h
  · nomatch h
  · rename_i st hNotDead hSt
    split at h
    · rename_i hChk
      split at h
      · rename_i lay base hLay hBase
        split at h
        · rename_i sub off hSub
          simp only [Except.ok.injEq] at h
          exact ⟨st, lay, base, sub, off, hSt, fun hD => hNotDead hD, hChk, hLay, hBase, hSub, h.symm⟩
        · nomatch h
      · nomatch h
    · nomatch h

/-- **In-bounds synthetic borrows (`evalSubplaceRef_inbounds`)**: in a well-formed context, the
borrowed sub-place `[addr, addr + size)` lies inside the local's synthetic allocation, which fits
below the address-space limit (`offset_inbounds` never wraps), and carries the local's
provenance. -/
theorem evalSubplaceRef_inbounds {cx : SubplaceCtx} (hWF : cx.WF) {slots : List LocalSlotState}
    {l : Nat} {proj : List ProjectionElem} {tag : Nat} {p : SynPtr}
    (h : evalSubplaceRef cx slots l proj tag = .ok p) :
    ∃ (base : Nat) (lay sub : ByteLayout), localBaseAddr cx.allocs l cx.limit = some base ∧
      cx.layoutOf l = some lay ∧
      computeSubplaceByteOffset lay proj = some (p.addr - base, sub.size) ∧
      base ≤ p.addr ∧ p.addr + sub.size ≤ base + ownAllocSize cx.allocs l ∧
      base + ownAllocSize cx.allocs l ≤ cx.limit ∧ p.prov = some (l + 1, tag) := by
  obtain ⟨st, lay, base, sub, off, _, _, _, hLay, hBase, hSub, rfl⟩ := evalSubplaceRef_eq_ok h
  obtain ⟨hLWF, hFitL⟩ := hWF.layout l lay hLay
  obtain ⟨_, _, hIn⟩ := subplaceAt_sub hLWF hSub
  refine ⟨base, lay, sub, hBase, hLay, ?_, by simp, by simp only; omega, localBaseAddr_fits hBase,
    rfl⟩
  simp only [computeSubplaceByteOffset, hSub, Option.map_some, Nat.add_sub_cancel_left]

/-- **Non-aliasing of distinct locals' synthetic sub-places (`evalSubplaceRef_disjoint_locals`)**:
in a well-formed context, sub-place borrows of two distinct locals `l₁ < l₂` designate disjoint
byte ranges, whatever their projections. -/
theorem evalSubplaceRef_disjoint_locals {cx : SubplaceCtx} (hWF : cx.WF)
    {slots : List LocalSlotState} {l₁ l₂ : Nat} (hl : l₁ < l₂) {proj₁ proj₂ : List ProjectionElem}
    {t₁ t₂ : Nat} {p₁ p₂ : SynPtr} {lay₁ sub₁ : ByteLayout} {off₁ : Nat}
    (hLay₁ : cx.layoutOf l₁ = some lay₁) (hSub₁ : subplaceAt lay₁ 0 proj₁ = some (sub₁, off₁))
    (h₁ : evalSubplaceRef cx slots l₁ proj₁ t₁ = .ok p₁)
    (h₂ : evalSubplaceRef cx slots l₂ proj₂ t₂ = .ok p₂) :
    p₁.addr + sub₁.size ≤ p₂.addr := by
  obtain ⟨_, lay, base₁, sub, off, _, _, _, hL, hB₁, hS, rfl⟩ := evalSubplaceRef_eq_ok h₁
  obtain ⟨_, lay', base₂, sub', off', _, _, _, _, hB₂, _, rfl⟩ := evalSubplaceRef_eq_ok h₂
  rw [hLay₁] at hL
  cases hL
  rw [hSub₁] at hS
  cases hS
  obtain ⟨hLWF, hFitL⟩ := hWF.layout l₁ lay₁ hLay₁
  obtain ⟨_, _, hIn⟩ := subplaceAt_sub hLWF hSub₁
  obtain ⟨hDisj, _⟩ := localBaseAddr_disjoint hl hB₁ hB₂
  simp only
  omega

/-- **Disjoint sibling borrows (`evalSubplaceRef_disjoint_siblings`)**: borrows of two sibling
fields/elements `i ≠ j` (below a common prefix) of the same local designate disjoint byte
ranges. -/
theorem evalSubplaceRef_disjoint_siblings {cx : SubplaceCtx} (hWF : cx.WF)
    {slots : List LocalSlotState} {l : Nat} {lay : ByteLayout} (hLay : cx.layoutOf l = some lay)
    {p : List ProjectionElem} {n : Nat} {offs : List Nat} {ls : List ByteLayout} {o : Nat}
    (hp : subplaceAt lay 0 p = some (.struct n offs ls, o))
    {e₁ e₂ : ProjectionElem} {i j : Nat} (hi : SelectsChild e₁ i) (hj : SelectsChild e₂ j)
    (hij : i ≠ j) {r₁ r₂ : List ProjectionElem} {t₁ t₂ : Nat} {p₁ p₂ : SynPtr}
    {sub₁ sub₂ : ByteLayout} {o₁ o₂ : Nat}
    (hs₁ : subplaceAt lay 0 (p ++ e₁ :: r₁) = some (sub₁, o₁))
    (hs₂ : subplaceAt lay 0 (p ++ e₂ :: r₂) = some (sub₂, o₂))
    (h₁ : evalSubplaceRef cx slots l (p ++ e₁ :: r₁) t₁ = .ok p₁)
    (h₂ : evalSubplaceRef cx slots l (p ++ e₂ :: r₂) t₂ = .ok p₂) :
    p₁.addr + sub₁.size ≤ p₂.addr ∨ p₂.addr + sub₂.size ≤ p₁.addr := by
  obtain ⟨_, lay₁, base₁, _, _, _, _, _, hL₁, hB₁, hS₁, rfl⟩ := evalSubplaceRef_eq_ok h₁
  obtain ⟨_, lay₂, base₂, _, _, _, _, _, hL₂, hB₂, hS₂, rfl⟩ := evalSubplaceRef_eq_ok h₂
  rw [hLay] at hL₁ hL₂
  cases hL₁
  cases hL₂
  rw [hB₁] at hB₂
  cases hB₂
  rw [hs₁] at hS₁
  cases hS₁
  rw [hs₂] at hS₂
  cases hS₂
  have := subplaceAt_disjoint_siblings (hWF.layout l lay hLay).1 hp hi hj hij hs₁ hs₂
  simp only
  omega

/-! ### Section 4c: No-guess sub-place resolution (`resolveSyntheticSubplace`) -/

/-- The indices of the candidates that satisfy `ok`. -/
def consistentIdx (cands : List (List ProjectionElem)) (ok : List ProjectionElem → Bool) :
    List Nat :=
  (List.range cands.length).filter fun i =>
    match cands[i]? with
    | some q => ok q
    | none => false

theorem mem_consistentIdx {cands : List (List ProjectionElem)} {ok : List ProjectionElem → Bool}
    {i : Nat} : i ∈ consistentIdx cands ok ↔ ∃ q, cands[i]? = some q ∧ ok q = true := by
  unfold consistentIdx
  simp only [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hlt, h⟩
    rw [List.getElem?_eq_getElem hlt] at h ⊢
    exact ⟨_, rfl, h⟩
  · rintro ⟨q, hq, hok⟩
    have hlt := (List.getElem?_eq_some_iff.mp hq).1
    exact ⟨hlt, by rw [hq]; exact hok⟩

/-- The zero-sized fallback of `select_subplace_candidate_in`: all values of a zero-sized pointee
are equal, so the first readable consistent candidate (or the first one) is as good as any;
for any other pointee type, ambiguity is never resolved by guessing. -/
def zstPick (cands : List (List ProjectionElem)) (consistent : List Nat) (zst : Bool)
    (readable : List ProjectionElem → Bool) : Option (List ProjectionElem) :=
  if zst then
    match consistent.find? (fun j => (cands[j]?.map readable).getD false) with
    | some j => cands[j]?
    | none =>
      match consistent.head? with
      | some i => cands[i]?
      | none => none
  else none

/-- Selection among the consistent candidates: a unique one, else the one the provenance tag's
ordinal designates, else the zero-sized fallback. -/
def pickConsistent (cands : List (List ProjectionElem)) (consistent : List Nat)
    (ordinal : Option Nat) (zst : Bool) (readable : List ProjectionElem → Bool) :
    Option (List ProjectionElem) :=
  match consistent with
  | [] => none
  | [i] => cands[i]?
  | _ :: _ :: _ =>
    match ordinal with
    | some o => if consistent.contains o then cands[o]? else zstPick cands consistent zst readable
    | none => zstPick cands consistent zst readable

/-- **`select_subplace_candidate_in`**: chooses, without guessing, the sub-place a synthetic
pointer designates among the same-offset, same-type candidates: candidates inconsistent with the
runtime state of the local (`cons`; with a whole-place write, `consOw` admits overwriting a leaf
union field) are discarded; an overwrite designated by the tag ordinal wins; then a unique
consistent candidate, the tag-designated one, or (zero-sized pointees only) the first readable
one is chosen; anything else is `none` (`UnsupportedPlaceProjection`). -/
def selectSubplaceCandidate (cands : List (List ProjectionElem))
    (cons consOw : List ProjectionElem → Bool) (ordinal : Option Nat) (zst : Bool)
    (readable : List ProjectionElem → Bool) (ow : Bool) : Option (List ProjectionElem) :=
  let active := consistentIdx cands cons
  let overw := if ow then consistentIdx cands consOw else []
  let byOrd : Option (List ProjectionElem) :=
    match ow, ordinal with
    | true, some o => if overw.contains o then cands[o]? else none
    | _, _ => none
  match byOrd with
  | some q => some q
  | none => pickConsistent cands (if !active.isEmpty || !ow then active else overw) ordinal zst readable

theorem zstPick_spec {cands : List (List ProjectionElem)} {C : List Nat} {zst : Bool}
    {readable : List ProjectionElem → Bool} {q : List ProjectionElem}
    (h : zstPick cands C zst readable = some q) : zst = true ∧ ∃ i ∈ C, cands[i]? = some q := by
  unfold zstPick at h
  split at h
  · rename_i hz
    split at h
    · rename_i j hj
      exact ⟨hz, j, List.mem_of_find?_eq_some hj, h⟩
    · split at h
      · rename_i i hi
        exact ⟨hz, i, List.mem_of_mem_head? hi, h⟩
      · nomatch h
  · nomatch h

theorem pickConsistent_spec {cands : List (List ProjectionElem)} {C : List Nat}
    {ordinal : Option Nat} {zst : Bool} {readable : List ProjectionElem → Bool}
    {q : List ProjectionElem} (h : pickConsistent cands C ordinal zst readable = some q) :
    ∃ i ∈ C, cands[i]? = some q ∧ (C = [i] ∨ ordinal = some i ∨ zst = true) := by
  unfold pickConsistent at h
  split at h
  · nomatch h
  · rename_i i
    exact ⟨i, List.mem_singleton_self _, h, Or.inl rfl⟩
  · split at h
    · rename_i o
      split at h
      · rename_i hc
        exact ⟨o, List.contains_iff_mem.mp hc, h, Or.inr (Or.inl rfl)⟩
      · obtain ⟨hz, k, hk, hq⟩ := zstPick_spec h
        exact ⟨k, hk, hq, Or.inr (Or.inr hz)⟩
    · obtain ⟨hz, k, hk, hq⟩ := zstPick_spec h
      exact ⟨k, hk, hq, Or.inr (Or.inr hz)⟩

/-- **No-guess selection (`selectSubplaceCandidate_no_guess`)**: a selected sub-place is a
candidate that passed the runtime consistency check (or, for a whole-place write, the leaf
union-overwrite check), and it was selected because it is the unique consistent candidate, or
the provenance tag's ordinal designates it, or the pointee is zero-sized. -/
theorem selectSubplaceCandidate_no_guess {cands : List (List ProjectionElem)}
    {cons consOw : List ProjectionElem → Bool} {ordinal : Option Nat} {zst : Bool}
    {readable : List ProjectionElem → Bool} {ow : Bool} {q : List ProjectionElem}
    (h : selectSubplaceCandidate cands cons consOw ordinal zst readable ow = some q) :
    ∃ i C, (C = consistentIdx cands cons ∨ (ow = true ∧ C = consistentIdx cands consOw)) ∧
      i ∈ C ∧ cands[i]? = some q ∧ (C = [i] ∨ ordinal = some i ∨ zst = true) := by
  unfold selectSubplaceCandidate at h
  dsimp only at h
  split at h
  · rename_i q' hq
    simp only [Option.some.injEq] at h
    subst h
    split at hq
    · rename_i o
      by_cases hc : (consistentIdx cands consOw).contains o = true
      · simp only [hc, ↓reduceIte] at hq
        exact ⟨o, _, Or.inr ⟨rfl, rfl⟩, List.contains_iff_mem.mp hc, hq, Or.inr (Or.inl rfl)⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hq
        nomatch hq
    · nomatch hq
  · obtain ⟨i, hiC, hq, hDesig⟩ := pickConsistent_spec h
    refine ⟨i, _, ?_, hiC, hq, hDesig⟩
    split
    · exact Or.inl rfl
    · rename_i hc
      cases ow with
      | false => simp at hc
      | true => exact Or.inr ⟨rfl, rfl⟩

/-- A selected sub-place passed the runtime check of its mode. -/
theorem selectSubplaceCandidate_consistent {cands : List (List ProjectionElem)}
    {cons consOw : List ProjectionElem → Bool} {ordinal : Option Nat} {zst : Bool}
    {readable : List ProjectionElem → Bool} {ow : Bool} {q : List ProjectionElem}
    (h : selectSubplaceCandidate cands cons consOw ordinal zst readable ow = some q) :
    q ∈ cands ∧ (cons q = true ∨ (ow = true ∧ consOw q = true)) := by
  obtain ⟨i, C, hC, hiC, hq, _⟩ := selectSubplaceCandidate_no_guess h
  refine ⟨List.mem_of_getElem? hq, ?_⟩
  rcases hC with rfl | ⟨hOw, rfl⟩
  · obtain ⟨q', hq', hok⟩ := mem_consistentIdx.mp hiC
    rw [hq] at hq'
    cases hq'
    exact Or.inl hok
  · obtain ⟨q', hq', hok⟩ := mem_consistentIdx.mp hiC
    rw [hq] at hq'
    cases hq'
    exact Or.inr ⟨hOw, hok⟩

/-- **Ambiguity fails closed (`selectSubplaceCandidate_ambiguous_none`)**: outside a whole-place
write, two or more consistent candidates of a sized pointee that the tag does not disambiguate
(e.g. same-typed fields of two variants of an uninitialized enum, or byte-punned union fields)
are never guessed between. -/
theorem selectSubplaceCandidate_ambiguous_none {cands : List (List ProjectionElem)}
    {cons consOw : List ProjectionElem → Bool} {ordinal : Option Nat}
    {readable : List ProjectionElem → Bool} {i j : Nat} {rest : List Nat}
    (hTwo : consistentIdx cands cons = i :: j :: rest)
    (hOrd : ∀ o, ordinal = some o → o ∉ consistentIdx cands cons) :
    selectSubplaceCandidate cands cons consOw ordinal false readable false = none := by
  unfold selectSubplaceCandidate
  simp only [hTwo, List.isEmpty_cons, Bool.not_false, Bool.true_or, ↓reduceIte, pickConsistent,
    zstPick, Bool.false_eq_true]
  cases ordinal with
  | none => rfl
  | some o =>
    have hNot := hOrd o rfl
    rw [hTwo] at hNot
    have hc : (i :: j :: rest).contains o = false := by
      cases hC : (i :: j :: rest).contains o with
      | false => rfl
      | true => exact absurd (List.contains_iff_mem.mp hC) hNot
    simp only [hc, Bool.false_eq_true, ↓reduceIte]

/-- Runtime consistency of a candidate path with local `l` (`check_frame_slot_projection` plus
`slot_union_path_active`, with or without leaf union overwrite). -/
def candConsistent (cx : SubplaceCtx) (slots : List LocalSlotState) (l : Nat) (ow : Bool)
    (q : List ProjectionElem) : Bool :=
  match slots[l]? with
  | none => false
  | some .dead => false
  | some st =>
    checkSlotProjectionOk (slotsToTrustedLocals slots) (slotStateToFieldSlot st) q &&
      cx.unionActive st q ow

/-- Whether reading the sub-place succeeds (the zero-sized fallback prefers initialized parts). -/
def subplaceReadable (slots : List LocalSlotState) (l : Nat) (q : List ProjectionElem) : Bool :=
  match readPlaceState slots ⟨l, q⟩ with
  | .ok _ => true
  | _ => false

/-- **`resolve_synthetic_subplace_in`**: maps a synthetic pointer `p` of type `pty` back to
`(target_local, path)` in the frame `slots`, checking in order: the address bit pattern
(`InvalidBitPattern`), non-null (`InvalidBitPattern` for `&T`, `NullPointerAccess` otherwise), the
pointee layout (`UnsupportedLayout`), alignment (`MisalignedPointer`, or `UnsupportedLayout` for an
unspecified alignment), an inhabited `&T` pointee (`UninhabitedPointee`), a non-wrapping pointee
range (`PointerRangeOverflow` under an exact layout), synthetic provenance of a local of the frame
and its liveness (`DeadLocal`), a synthetic allocation that fits the address space, and an
in-bounds `[relOff, relOff + size)`; offset `0` with the local's own type is the root, and
otherwise the designated sub-place is selected without guessing (`selectSubplaceCandidate`).
Every unresolvable pointer is `unsupported` (never a guessed sub-place). -/
def resolveSyntheticSubplace (cx : SubplaceCtx) (slots : List LocalSlotState) (p : SynPtr)
    (pty : PtrTy) (ow : Bool) : Except DerefErr (Nat × List ProjectionElem) :=
  if cx.limit < p.addr then .error .invalidBitPattern
  else if p.addr = 0 then (if pty.isRef then .error .invalidBitPattern else .error .nullPointer)
  else
    match cx.tyLayout pty.pointee with
    | none => .error .unsupportedLayout
    | some tl =>
      if p.addr % tl.minAlign ≠ 0 then .error .misaligned
      else if p.addr % tl.maxAlign ≠ 0 then .error .unsupportedLayout
      else if pty.isRef && !tl.inhabited then .error .uninhabited
      else if cx.limit < p.addr + tl.size then
        (if tl.exact then .error .rangeOverflow else .error .unsupported)
      else
        match p.prov with
        | none => .error .unsupported
        | some (0, _) => .error .unsupported
        | some (l + 1, tag) =>
          if min slots.length cx.allocs.length ≤ l then .error .unsupported
          else
            match slots[l]? with
            | some .dead => .error (.deadLocal l)
            | _ =>
              match localBaseAddr cx.allocs l cx.limit, ownLayout cx.allocs l with
              | some base, some (allocSize, _) =>
                if p.addr < base then .error .unsupported
                else if allocSize < p.addr - base + tl.size then .error .unsupported
                else if p.addr - base = 0 ∧ cx.declTy l = some pty.pointee then .ok (l, [])
                else
                  match selectSubplaceCandidate (cx.candidates pty.pointee l (p.addr - base))
                      (candConsistent cx slots l false) (candConsistent cx slots l true)
                      (cx.decodeTag tag pty.pointee) (tl.size == 0) (subplaceReadable slots l) ow with
                  | some q => .ok (l, q)
                  | none => .error .unsupported
              | _, _ => .error .unsupported

/-- The address checks `resolveSyntheticSubplace` performs before consulting the provenance. -/
structure PtrPrechecks (cx : SubplaceCtx) (p : SynPtr) (pty : PtrTy) (tl : TyLayout) : Prop where
  inWidth : p.addr ≤ cx.limit
  nonNull : p.addr ≠ 0
  layout : cx.tyLayout pty.pointee = some tl
  minAligned : p.addr % tl.minAlign = 0
  maxAligned : p.addr % tl.maxAlign = 0
  inhabited : pty.isRef = true → tl.inhabited = true
  noWrap : p.addr + tl.size ≤ cx.limit

/-- `resolveSyntheticSubplace` once the address checks pass. -/
theorem resolveSyntheticSubplace_of_prechecks {cx : SubplaceCtx} {slots : List LocalSlotState}
    {p : SynPtr} {pty : PtrTy} {ow : Bool} {tl : TyLayout} (hP : PtrPrechecks cx p pty tl) :
    resolveSyntheticSubplace cx slots p pty ow =
      match p.prov with
      | none => .error .unsupported
      | some (0, _) => .error .unsupported
      | some (l + 1, tag) =>
        if min slots.length cx.allocs.length ≤ l then .error .unsupported
        else
          match slots[l]? with
          | some .dead => .error (.deadLocal l)
          | _ =>
            match localBaseAddr cx.allocs l cx.limit, ownLayout cx.allocs l with
            | some base, some (allocSize, _) =>
              if p.addr < base then .error .unsupported
              else if allocSize < p.addr - base + tl.size then .error .unsupported
              else if p.addr - base = 0 ∧ cx.declTy l = some pty.pointee then .ok (l, [])
              else
                match selectSubplaceCandidate (cx.candidates pty.pointee l (p.addr - base))
                    (candConsistent cx slots l false) (candConsistent cx slots l true)
                    (cx.decodeTag tag pty.pointee) (tl.size == 0) (subplaceReadable slots l) ow with
                | some q => .ok (l, q)
                | none => .error .unsupported
            | _, _ => .error .unsupported := by
  have h1 : ¬ cx.limit < p.addr := by have := hP.inWidth; omega
  have h3 : ¬ p.addr % tl.minAlign ≠ 0 := by have := hP.minAligned; omega
  have h4 : ¬ p.addr % tl.maxAlign ≠ 0 := by have := hP.maxAligned; omega
  have h5 : (pty.isRef && !tl.inhabited) = false := by
    cases hr : pty.isRef with
    | false => rfl
    | true => simp [hP.inhabited hr]
  have h6 : ¬ cx.limit < p.addr + tl.size := by have := hP.noWrap; omega
  unfold resolveSyntheticSubplace
  simp only [h1, hP.nonNull, hP.layout, h3, h4, h5, h6, ↓reduceIte, Bool.false_eq_true]

/-- **Null pointers fault (`resolveSyntheticSubplace_null`)**: `InvalidBitPattern` for a null
`&T`, `NullPointerAccess` for a null raw pointer. -/
theorem resolveSyntheticSubplace_null {cx : SubplaceCtx} {slots : List LocalSlotState}
    {p : SynPtr} (pty : PtrTy) (ow : Bool) (h0 : p.addr = 0) :
    resolveSyntheticSubplace cx slots p pty ow =
      .error (if pty.isRef then .invalidBitPattern else .nullPointer) := by
  unfold resolveSyntheticSubplace
  simp only [h0, Nat.not_lt_zero, ↓reduceIte]
  cases pty.isRef <;> rfl

/-- **Misaligned pointers fault (`resolveSyntheticSubplace_misaligned`)**. -/
theorem resolveSyntheticSubplace_misaligned {cx : SubplaceCtx} {slots : List LocalSlotState}
    {p : SynPtr} {pty : PtrTy} {ow : Bool} {tl : TyLayout} (hW : p.addr ≤ cx.limit)
    (hNZ : p.addr ≠ 0) (hL : cx.tyLayout pty.pointee = some tl) (hMis : p.addr % tl.minAlign ≠ 0) :
    resolveSyntheticSubplace cx slots p pty ow = .error .misaligned := by
  have h1 : ¬ cx.limit < p.addr := by omega
  unfold resolveSyntheticSubplace
  simp only [h1, hNZ, hL, hMis, ↓reduceIte, ne_eq, not_false_eq_true]

/-- **Exact-layout pointee ranges that wrap the address space fault
(`resolveSyntheticSubplace_rangeOverflow`)** with `PointerRangeOverflow`. -/
theorem resolveSyntheticSubplace_rangeOverflow {cx : SubplaceCtx} {slots : List LocalSlotState}
    {p : SynPtr} {pty : PtrTy} {ow : Bool} {tl : TyLayout} (hW : p.addr ≤ cx.limit)
    (hNZ : p.addr ≠ 0) (hL : cx.tyLayout pty.pointee = some tl) (hA1 : p.addr % tl.minAlign = 0)
    (hA2 : p.addr % tl.maxAlign = 0) (hInh : pty.isRef = true → tl.inhabited = true)
    (hWrap : cx.limit < p.addr + tl.size) (hExact : tl.exact = true) :
    resolveSyntheticSubplace cx slots p pty ow = .error .rangeOverflow := by
  have h1 : ¬ cx.limit < p.addr := by omega
  have h5 : (pty.isRef && !tl.inhabited) = false := by
    cases hr : pty.isRef with
    | false => rfl
    | true => simp [hInh hr]
  unfold resolveSyntheticSubplace
  simp only [h1, hNZ, hL, hA1, hA2, h5, hWrap, hExact, ↓reduceIte, ne_eq, not_true_eq_false,
    Bool.false_eq_true]

/-- **Dangling sub-place pointers fault (`resolveSyntheticSubplace_dead`)**: a pointer whose
synthetic provenance names a storage-dead local of the frame is `DeadLocal`, at any offset. -/
theorem resolveSyntheticSubplace_dead {cx : SubplaceCtx} {slots : List LocalSlotState}
    {p : SynPtr} {pty : PtrTy} {ow : Bool} {tl : TyLayout} (hP : PtrPrechecks cx p pty tl)
    {l tag : Nat} (hProv : p.prov = some (l + 1, tag)) (hl : l < min slots.length cx.allocs.length)
    (hDead : slots[l]? = some .dead) :
    resolveSyntheticSubplace cx slots p pty ow = .error (.deadLocal l) := by
  rw [resolveSyntheticSubplace_of_prechecks hP, hProv]
  have hNot : ¬ min slots.length cx.allocs.length ≤ l := by omega
  simp only [hNot, ↓reduceIte, hDead]

/-- A pointer without synthetic provenance is never resolved to a local (`unsupported`). -/
theorem resolveSyntheticSubplace_no_provenance {cx : SubplaceCtx} {slots : List LocalSlotState}
    {p : SynPtr} {pty : PtrTy} {ow : Bool} {tl : TyLayout} (hP : PtrPrechecks cx p pty tl)
    (hProv : p.prov = none) :
    resolveSyntheticSubplace cx slots p pty ow = .error .unsupported := by
  rw [resolveSyntheticSubplace_of_prechecks hP, hProv]

/-- **Soundness of synthetic sub-place resolution (`resolveSyntheticSubplace_sound`)**: a resolved
pointer passed the address checks, carries the provenance `l + 1` of a live local of the frame, and
addresses an in-bounds offset `relOff = addr - base` of that local's synthetic allocation; the
resolved path is the root (offset `0` with the local's own type) or a candidate of the pointee
type at `relOff` that passed the runtime consistency check and was designated without guessing. -/
theorem resolveSyntheticSubplace_sound {cx : SubplaceCtx} {slots : List LocalSlotState}
    {p : SynPtr} {pty : PtrTy} {ow : Bool} {l : Nat} {q : List ProjectionElem}
    (h : resolveSyntheticSubplace cx slots p pty ow = .ok (l, q)) :
    ∃ tl tag base allocSize align, PtrPrechecks cx p pty tl ∧ p.prov = some (l + 1, tag) ∧
      l < slots.length ∧ l < cx.allocs.length ∧ slots[l]? ≠ some .dead ∧
      localBaseAddr cx.allocs l cx.limit = some base ∧
      ownLayout cx.allocs l = some (allocSize, align) ∧ base ≤ p.addr ∧
      p.addr - base + tl.size ≤ allocSize ∧
      ((p.addr = base ∧ cx.declTy l = some pty.pointee ∧ q = []) ∨
        ∃ i C, ¬ (p.addr - base = 0 ∧ cx.declTy l = some pty.pointee) ∧
          (C = consistentIdx (cx.candidates pty.pointee l (p.addr - base))
              (candConsistent cx slots l false) ∨
            (ow = true ∧ C = consistentIdx (cx.candidates pty.pointee l (p.addr - base))
              (candConsistent cx slots l true))) ∧
          i ∈ C ∧ (cx.candidates pty.pointee l (p.addr - base))[i]? = some q ∧
          (C = [i] ∨ cx.decodeTag tag pty.pointee = some i ∨ tl.size = 0)) := by
  unfold resolveSyntheticSubplace at h
  split at h
  · nomatch h
  · rename_i hW
    split at h
    · split at h <;> nomatch h
    · rename_i hNZ
      split at h
      · nomatch h
      · rename_i tl hTl
        split at h
        · nomatch h
        · rename_i hA1
          split at h
          · nomatch h
          · rename_i hA2
            split at h
            · nomatch h
            · rename_i hInh
              split at h
              · split at h <;> nomatch h
              · rename_i hWrap
                have hP : PtrPrechecks cx p pty tl :=
                  ⟨by omega, hNZ, hTl, by omega, by omega,
                    fun hr => by simp [hr] at hInh; exact hInh, by omega⟩
                split at h
                · nomatch h
                · nomatch h
                · rename_i l' tag hProv
                  split at h
                  · nomatch h
                  · rename_i hLt
                    split at h
                    · nomatch h
                    · rename_i hNotDead
                      split at h
                      · rename_i base allocSize align hBase hOwn
                        split at h
                        · nomatch h
                        · rename_i hGe
                          split at h
                          · nomatch h
                          · rename_i hIn
                            split at h
                            · rename_i hRoot
                              simp only [Except.ok.injEq, Prod.mk.injEq] at h
                              obtain ⟨rfl, rfl⟩ := h
                              refine ⟨tl, tag, base, allocSize, align, hP, hProv, by omega,
                                by omega, fun hD => hNotDead hD, hBase, hOwn, by omega, by omega,
                                Or.inl ⟨by omega, hRoot.2, rfl⟩⟩
                            · rename_i hNR
                              split at h
                              · rename_i q' hSel
                                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                                obtain ⟨rfl, rfl⟩ := h
                                obtain ⟨i, C, hC, hiC, hq, hD⟩ := selectSubplaceCandidate_no_guess hSel
                                refine ⟨tl, tag, base, allocSize, align, hP, hProv, by omega,
                                  by omega, fun hD => hNotDead hD, hBase, hOwn, by omega,
                                  by omega, Or.inr ⟨i, C, hNR, hC, hiC, hq, ?_⟩⟩
                                rcases hD with hD | hD | hD
                                · exact Or.inl hD
                                · exact Or.inr (Or.inl hD)
                                · exact Or.inr (Or.inr (by simpa using hD))
                              · nomatch h
                      · nomatch h

/-- Selection from a single consistent candidate always succeeds with it, in either mode. -/
theorem selectSubplaceCandidate_singleton {q : List ProjectionElem}
    {cons consOw : List ProjectionElem → Bool} (ordinal : Option Nat) (zst : Bool)
    (readable : List ProjectionElem → Bool) (ow : Bool) (hc : cons q = true)
    (hcOw : ow = true → consOw q = true) :
    selectSubplaceCandidate [q] cons consOw ordinal zst readable ow = some q := by
  have hA : consistentIdx [q] cons = [0] := by simp [consistentIdx, hc]
  unfold selectSubplaceCandidate
  simp only [hA]
  cases ow with
  | false => simp [pickConsistent]
  | true =>
    have hO : consistentIdx [q] consOw = [0] := by simp [consistentIdx, hcOw rfl]
    simp only [hO, ↓reduceIte]
    cases ordinal with
    | none => simp [pickConsistent]
    | some o => by_cases ho : o = 0 <;> simp [ho, pickConsistent]

/-- Every synthetic base address lies at or above the first page (so it is never null). -/
theorem localBaseAddr_ge_page {lays : AllocLayouts} {l limit b : Nat}
    (h : localBaseAddr lays l limit = some b) : synthPage ≤ b := by
  obtain ⟨cur, hScan, hb, _⟩ := localBaseAddr_eq_some.mp h
  have h1 := baseScan_ge hScan
  have h2 := le_ownAlignedCursor lays l cur
  omega

/-- **Borrow/`Deref` round trip (`resolveSyntheticSubplace_evalSubplaceRef`)**: dereferencing the
pointer that a synthetic sub-place borrow `&_l.proj` produced resolves back to exactly
`(l, proj)` — in read and in whole-place-write mode — whenever `proj` is the only candidate of the
pointee type at its offset (`collect_subplace_paths` finds no other sub-place to confuse it
with), it is not the local's own root type at offset `0`, its union path is active, and the
address satisfies the pointee's alignment (and inhabitedness for `&T`). -/
theorem resolveSyntheticSubplace_evalSubplaceRef {cx : SubplaceCtx} (hWF : cx.WF)
    {slots : List LocalSlotState} {l : Nat} {proj : List ProjectionElem} {tag : Nat} {p : SynPtr}
    (hRef : evalSubplaceRef cx slots l proj tag = .ok p) {pty : PtrTy} {tl : TyLayout} (ow : Bool)
    (hTl : cx.tyLayout pty.pointee = some tl) (hA1 : p.addr % tl.minAlign = 0)
    (hA2 : p.addr % tl.maxAlign = 0) (hInh : pty.isRef = true → tl.inhabited = true)
    {lay sub : ByteLayout} {off : Nat} (hLay : cx.layoutOf l = some lay)
    (hSub : subplaceAt lay 0 proj = some (sub, off)) (hSize : sub.size = tl.size)
    (hCands : cx.candidates pty.pointee l off = [proj])
    (hNotRoot : off = 0 → cx.declTy l ≠ some pty.pointee)
    (hUnion : ∀ st, slots[l]? = some st → cx.unionActive st proj false = true ∧
      cx.unionActive st proj true = true)
    {allocSize align : Nat} (hOwn : ownLayout cx.allocs l = some (allocSize, align)) :
    resolveSyntheticSubplace cx slots p pty ow = .ok (l, proj) := by
  obtain ⟨st, lay', base, sub', off', hSt, hLive, hChk, hLay', hBase, hSub', rfl⟩ :=
    evalSubplaceRef_eq_ok hRef
  rw [hLay] at hLay'
  cases hLay'
  rw [hSub] at hSub'
  cases hSub'
  obtain ⟨hLWF, hFitL⟩ := hWF.layout l lay hLay
  obtain ⟨_, _, hIn⟩ := subplaceAt_sub hLWF hSub
  have hFits := localBaseAddr_fits hBase
  have hPage := localBaseAddr_ge_page hBase
  have hAS : ownAllocSize cx.allocs l = allocSize := by simp [ownAllocSize, hOwn]
  have hPP := synthPage_pos
  have hP : PtrPrechecks cx ⟨base + off, some (l + 1, tag)⟩ pty tl :=
    ⟨by simp only; omega, by simp only; omega, hTl, hA1, hA2, hInh, by simp only; omega⟩
  rw [resolveSyntheticSubplace_of_prechecks hP]
  have hlS : l < slots.length := (List.getElem?_eq_some_iff.mp hSt).1
  have hlA : l < cx.allocs.length := by
    rcases Nat.lt_or_ge l cx.allocs.length with h | h
    · exact h
    · simp [ownLayout, List.getElem?_eq_none h] at hOwn
  have hNot : ¬ min slots.length cx.allocs.length ≤ l := by omega
  have hRel : base + off - base = off := by omega
  simp only [hNot, ↓reduceIte, hSt, hBase, hOwn, hRel]
  have hStMatch : (match some st with
      | some .dead => (Except.error (.deadLocal l) : Except DerefErr (Nat × List ProjectionElem))
      | _ => Except.error .unsupported) = Except.error .unsupported ∨ st ≠ .dead := Or.inr hLive
  clear hStMatch
  cases st with
  | dead => exact absurd rfl hLive
  | _ =>
    have hLt : ¬ base + off < base := by omega
    have hIn' : ¬ allocSize < off + tl.size := by omega
    have hNR : ¬ (off = 0 ∧ cx.declTy l = some pty.pointee) := fun h => hNotRoot h.1 h.2
    simp only [hLt, hIn', hNR, ↓reduceIte, hCands]
    obtain ⟨hU1, hU2⟩ := hUnion _ hSt
    rw [selectSubplaceCandidate_singleton _ _ _ _
      (by simp [candConsistent, hSt, hChk, hU1])
      (fun _ => by simp [candConsistent, hSt, hChk, hU2])]

/-! ### Section 4d: `ProjectionElem.deref` places: read, write, deinit, move, and retag -/

/-- **`resolve_deref_place_in`**: resolves the `Deref` steps of a projection from left to right,
reading each dereferenced pointer from the (`Deref`-free) place resolved so far
(`readPlaceState`) and resolving it with `resolveSyntheticSubplace`; a final `Deref` of a
whole-place write (`ow`) may overwrite a leaf union field. -/
def derefTarget (cx : SubplaceCtx) (slots : List LocalSlotState) (ow : Bool) :
    Nat → List ProjectionElem → List ProjectionElem → Except DerefErr Place
  | cur, curProj, [] => .ok ⟨cur, curProj⟩
  | cur, curProj, .deref :: rest =>
    match readPlaceState slots ⟨cur, curProj⟩, cx.ptrTyAt cur curProj with
    | .ok (.ptr pv _), some pty =>
      match resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty (ow && rest.isEmpty) with
      | .ok (l, q) => derefTarget cx slots ow l q rest
      | .error e => .error e
    | .ok _, _ => .error .typeMismatch
    | .ub, _ => .error .ub
    | .unsupported, _ => .error .unsupported
  | cur, curProj, e :: rest => derefTarget cx slots ow cur (curProj ++ [e]) rest

/-- The `Deref`-free target of a place (`resolve_deref_place_in` after the live-root check). -/
def resolvePlace (cx : SubplaceCtx) (slots : List LocalSlotState) (place : Place) (ow : Bool) :
    Except DerefErr Place :=
  match slots[place.local_]? with
  | none => .error .typeMismatch
  | some .dead => .error (.deadLocal place.local_)
  | some _ => derefTarget cx slots ow place.local_ [] place.projection

/-- A `Deref`-free projection is appended to the current place without reading any slot. -/
theorem derefTarget_noDeref (cx : SubplaceCtx) (slots : List LocalSlotState) (ow : Bool) :
    ∀ (proj : List ProjectionElem) (cur : Nat) (curProj : List ProjectionElem),
      projectionHasDeref proj = false →
      derefTarget cx slots ow cur curProj proj = .ok ⟨cur, curProj ++ proj⟩ := by
  intro proj
  induction proj with
  | nil => intro cur curProj _; simp [derefTarget]
  | cons e rest ih =>
    intro cur curProj h
    cases e with
    | deref => simp [projectionHasDeref] at h
    | _ =>
      simp only [projectionHasDeref] at h
      simp only [derefTarget]
      rw [ih _ _ h, List.append_assoc, List.singleton_append]

/-- A leading `Deref` reads the pointer at the current place and continues at its target. -/
theorem derefTarget_deref {cx : SubplaceCtx} {slots : List LocalSlotState} {ow : Bool}
    {cur : Nat} {curProj rest : List ProjectionElem} {pv : ProvenancePtr} {sz : Nat}
    {pty : PtrTy} {l : Nat} {q : List ProjectionElem}
    (hPtr : readPlaceState slots ⟨cur, curProj⟩ = .ok (.ptr pv sz))
    (hTy : cx.ptrTyAt cur curProj = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty (ow && rest.isEmpty) = .ok (l, q)) :
    derefTarget cx slots ow cur curProj (.deref :: rest) = derefTarget cx slots ow l q rest := by
  simp only [derefTarget, hPtr, hTy, hRes]

/-- **Conservative extension**: a `Deref`-free place of a live local resolves to itself. -/
theorem resolvePlace_noDeref {cx : SubplaceCtx} {slots : List LocalSlotState} {place : Place}
    (ow : Bool) {st : LocalSlotState} (hSt : slots[place.local_]? = some st) (hLive : st ≠ .dead)
    (hNoDeref : projectionHasDeref place.projection = false) :
    resolvePlace cx slots place ow = .ok place := by
  unfold resolvePlace
  rw [hSt]
  cases st with
  | dead => exact absurd rfl hLive
  | _ => simp only [derefTarget_noDeref cx slots ow _ _ _ hNoDeref, List.nil_append]

/-- A place rooted at a dead local faults (`DeadLocal`), before any pointer is read. -/
theorem resolvePlace_dead {cx : SubplaceCtx} {slots : List LocalSlotState} {place : Place}
    (ow : Bool) (h : slots[place.local_]? = some .dead) :
    resolvePlace cx slots place ow = .error (.deadLocal place.local_) := by
  simp [resolvePlace, h]

/-- A single leading `Deref` `⟨p, .deref :: rest⟩` (the only shape of runtime MIR, after
`CopyForDeref` separation) with a `Deref`-free `rest` resolves to the pointer's target followed by
`rest`. -/
theorem resolvePlace_deref {cx : SubplaceCtx} {slots : List LocalSlotState} {ow : Bool}
    {p : Nat} {rest : List ProjectionElem} {stp : LocalSlotState} {pv : ProvenancePtr} {sz : Nat}
    {pty : PtrTy} {l : Nat} {q : List ProjectionElem} (hSt : slots[p]? = some stp)
    (hLive : stp ≠ .dead) (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz))
    (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty (ow && rest.isEmpty) = .ok (l, q))
    (hRest : projectionHasDeref rest = false) :
    resolvePlace cx slots ⟨p, .deref :: rest⟩ ow = .ok ⟨l, q ++ rest⟩ := by
  unfold resolvePlace
  simp only [hSt]
  cases stp with
  | dead => exact absurd rfl hLive
  | _ =>
    rw [derefTarget_deref hPtr hTy hRes, derefTarget_noDeref cx slots ow _ _ _ hRest]

/-- Lifting a value-tree read result into `Deref` evaluation. -/
def liftRead : ProjReadResult → Except DerefErr Value
  | .ok v => .ok v
  | .ub => .error .ub
  | .unsupported => .error .unsupported

/-- Lifting a slot write result into `Deref` evaluation. -/
def liftWrite {α : Type} : SlotWriteResult α → Except DerefErr α
  | .ok v => .ok v
  | .ub => .error .ub
  | .unsupported => .error .unsupported

/-- **`evalDerefPlaceRead`** (`read_place` through `Deref`): resolve the place's `Deref` steps
(read mode), then read the `Deref`-free target. -/
def evalDerefPlaceRead (cx : SubplaceCtx) (slots : List LocalSlotState) (place : Place) :
    Except DerefErr Value :=
  match resolvePlace cx slots place false with
  | .ok tgt => liftRead (readPlaceState slots tgt)
  | .error e => .error e

/-- **`evalDerefPlaceWrite`** (`write_place` through `Deref`): resolve the place's `Deref` steps
(whole-place-write mode), then write the target with `writePlaceState` — initializing
`PartialShell` fields and preserving their siblings. -/
def evalDerefPlaceWrite (arityOf : Ty → VariantIdx → Bool → Option Nat) (rootTyOf : Nat → Ty)
    (cx : SubplaceCtx) (slots : List LocalSlotState) (place : Place) (v : Value) :
    Except DerefErr (List LocalSlotState) :=
  match resolvePlace cx slots place true with
  | .ok tgt => liftWrite (writePlaceState arityOf slots tgt (rootTyOf tgt.local_) v)
  | .error e => .error e

/-- **`evalDerefPlaceDeinit`** (`deinit_place` through `Deref`): resolve, then `evalDeinitPlace`
the target. -/
def evalDerefPlaceDeinit (ts : Bool) (cx : SubplaceCtx) (slots : List LocalSlotState)
    (place : Place) : Except DerefErr (List LocalSlotState) :=
  match resolvePlace cx slots place false with
  | .ok tgt =>
    match evalDeinitPlace ts slots tgt with
    | some slots' => .ok slots'
    | none => .error .unsupported
  | .error e => .error e

/-- **Operands through `Deref`** (`eval_op`): `Copy` and `Move` of a place with a `Deref` read
through the pointer and leave every slot unchanged; any other operand is `evalOperandState`
(where `Move` of a bare local deinitializes it). -/
def evalDerefOperand (cx : SubplaceCtx) (slots : List LocalSlotState) (op : Operand) :
    Except DerefErr Value × List LocalSlotState :=
  match op with
  | .copy place | .move place =>
    if projectionHasDeref place.projection then (evalDerefPlaceRead cx slots place, slots)
    else
      let r := evalOperandState slots op
      (liftRead r.1, r.2)
  | .constant _ =>
    let r := evalOperandState slots op
    (liftRead r.1, r.2)

/-- **Move-Deref Non-Deinit (`evalDerefOperand_move_deref`)**: `Operand.move (*_p).rest` reads
the target exactly like a copy and deinitializes nothing — neither the target local nor `_p` (nor
any other local) changes. -/
theorem evalDerefOperand_move_deref (cx : SubplaceCtx) (slots : List LocalSlotState)
    (place : Place) (h : projectionHasDeref place.projection = true) :
    evalDerefOperand cx slots (.move place) = (evalDerefPlaceRead cx slots place, slots) ∧
      evalDerefOperand cx slots (.copy place) = (evalDerefPlaceRead cx slots place, slots) := by
  simp [evalDerefOperand, h]

/-- In particular, after `move (*_p)` the pointer local and the target local keep their slots. -/
theorem evalDerefOperand_move_deref_slots (cx : SubplaceCtx) (slots : List LocalSlotState)
    (p : Nat) (rest : List ProjectionElem) (l : Nat) :
    (evalDerefOperand cx slots (.move ⟨p, .deref :: rest⟩)).2[p]? = slots[p]? ∧
      (evalDerefOperand cx slots (.move ⟨p, .deref :: rest⟩)).2[l]? = slots[l]? := by
  simp [evalDerefOperand, projectionHasDeref]

/-- Contrast: moving a bare local does deinitialize it (`move_place`). -/
theorem evalDerefOperand_move_bare (cx : SubplaceCtx) (slots : List LocalSlotState) (l : Nat)
    (v : Value) (h : readPlaceState slots ⟨l, []⟩ = .ok v) :
    evalDerefOperand cx slots (.move ⟨l, []⟩) = (.ok v, slots.set l .uninit) := by
  simp [evalDerefOperand, projectionHasDeref, evalOperandState, movePlaceState, h, liftRead]

/-- `Deref` reads of a `Deref`-free place are plain `readPlaceState` reads. -/
theorem evalDerefPlaceRead_noDeref {cx : SubplaceCtx} {slots : List LocalSlotState}
    {place : Place} {st : LocalSlotState} (hSt : slots[place.local_]? = some st)
    (hLive : st ≠ .dead) (hNoDeref : projectionHasDeref place.projection = false) :
    evalDerefPlaceRead cx slots place = liftRead (readPlaceState slots place) := by
  simp only [evalDerefPlaceRead, resolvePlace_noDeref false hSt hLive hNoDeref]

/-- **`evalDerefPlaceRead` through one `Deref`**: reading `(*_p).rest` reads `rest` below the
pointer's resolved target sub-place. -/
theorem evalDerefPlaceRead_deref {cx : SubplaceCtx} {slots : List LocalSlotState}
    {p : Nat} {rest : List ProjectionElem} {stp : LocalSlotState} {pv : ProvenancePtr} {sz : Nat}
    {pty : PtrTy} {l : Nat} {q : List ProjectionElem} (hSt : slots[p]? = some stp)
    (hLive : stp ≠ .dead) (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz))
    (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty false = .ok (l, q))
    (hRest : projectionHasDeref rest = false) :
    evalDerefPlaceRead cx slots ⟨p, .deref :: rest⟩ = liftRead (readPlaceState slots ⟨l, q ++ rest⟩) := by
  have hRes' : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty (false && rest.isEmpty) =
      .ok (l, q) := by simpa using hRes
  simp only [evalDerefPlaceRead, resolvePlace_deref hSt hLive hPtr hTy hRes' hRest]

/-- `writePlaceState` only changes the written local. -/
theorem writePlaceState_frame {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {slots slots' : List LocalSlotState} {place : Place} {rootTy : Ty} {w : Value}
    (h : writePlaceState arityOf slots place rootTy w = .ok slots') :
    ∃ x, slots' = slots.set place.local_ x := by
  unfold writePlaceState at h
  split at h
  · nomatch h
  · dsimp only at h
    split at h
    · nomatch h
    · nomatch h
    · split at h
      · rename_i next _
        simp only [SlotWriteResult.ok.injEq] at h
        exact ⟨_, h.symm⟩
      · nomatch h
      · nomatch h
    · split at h
      · rename_i next _
        simp only [SlotWriteResult.ok.injEq] at h
        exact ⟨_, h.symm⟩
      · nomatch h
      · nomatch h
    · split at h
      · rename_i next _
        simp only [SlotWriteResult.ok.injEq] at h
        exact ⟨_, h.symm⟩
      · nomatch h
      · nomatch h

/-- **Distinct-Local Frame of `Deref` writes (`evalDerefPlaceWrite_frame`)**: a write through a
pointer changes only the slot of its resolved target local; every other local — including the
pointer local `_p` when the target is another local — keeps its slot. -/
theorem evalDerefPlaceWrite_frame {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {cx : SubplaceCtx} {slots slots' : List LocalSlotState} {place : Place}
    {v : Value} {tgt : Place} (hRes : resolvePlace cx slots place true = .ok tgt)
    (h : evalDerefPlaceWrite arityOf rootTyOf cx slots place v = .ok slots') :
    ∀ j, j ≠ tgt.local_ → slots'[j]? = slots[j]? := by
  intro j hj
  simp only [evalDerefPlaceWrite, hRes] at h
  cases hW : writePlaceState arityOf slots tgt (rootTyOf tgt.local_) v with
  | ub => simp [hW, liftWrite] at h
  | unsupported => simp [hW, liftWrite] at h
  | ok s =>
    simp only [hW, liftWrite, Except.ok.injEq] at h
    subst h
    obtain ⟨x, rfl⟩ := writePlaceState_frame hW
    exact List.getElem?_set_ne (Ne.symm hj)

/-- `writePlaceState` of an initialized root writes the value tree (`evalValueProjWrite`). -/
theorem writePlaceState_init_root {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {slots : List LocalSlotState} {l : Nat} {q : List ProjectionElem} {rootTy : Ty}
    {root w root' : Value} (hSt : slots[l]? = some (.init root))
    (hNoDeref : projectionHasDeref q = false)
    (hW : evalValueProjWrite (slotsToTrustedLocals slots) root q w = .ok root') :
    writePlaceState arityOf slots ⟨l, q⟩ rootTy w = .ok (slots.set l (.init root')) := by
  rw [writePlaceState_eq (place := ⟨l, q⟩) hSt (by simp) hNoDeref]
  have hT := (writeToFieldSlot_init_correspondence (slotsToTrustedLocals slots) arityOf root w
    root' rootTy q).1.mpr hW
  simp only [slotStateToFieldSlot, hT, fieldSlotToLocalSlotState]

/-- Inversion of `writePlaceState` on an initialized root. -/
theorem writePlaceState_init_root_inv {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {slots slots' : List LocalSlotState} {l : Nat} {q : List ProjectionElem} {rootTy : Ty}
    {root w : Value} (hSt : slots[l]? = some (.init root)) (hNoDeref : projectionHasDeref q = false)
    (h : writePlaceState arityOf slots ⟨l, q⟩ rootTy w = .ok slots') :
    ∃ root', evalValueProjWrite (slotsToTrustedLocals slots) root q w = .ok root' ∧
      slots' = slots.set l (.init root') := by
  rw [writePlaceState_eq (place := ⟨l, q⟩) hSt (by simp) hNoDeref] at h
  simp only [slotStateToFieldSlot] at h
  cases q with
  | nil =>
    simp only [writeToFieldSlot] at h
    simp only [SlotWriteResult.ok.injEq] at h
    exact ⟨w, rfl, by rw [← h]; rfl⟩
  | cons e rest =>
    unfold writeToFieldSlot at h
    dsimp only at h
    cases hE : evalValueProjWrite (slotsToTrustedLocals slots) root (e :: rest) w with
    | ok r' =>
      rw [hE] at h
      simp only [SlotWriteResult.ok.injEq] at h
      exact ⟨r', rfl, by rw [← h]; rfl⟩
    | ub => rw [hE] at h; nomatch h
    | unsupported => rw [hE] at h; nomatch h

/-- **Get-Put at a `Deref` target (`writePlaceState_get_put_init`)**: writing back the value read
from a sub-place of an initialized local leaves the frame unchanged. -/
theorem writePlaceState_get_put_init {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {slots : List LocalSlotState} {l : Nat} {q : List ProjectionElem} {rootTy : Ty}
    {root v : Value} (hSt : slots[l]? = some (.init root))
    (hRead : readPlaceState slots ⟨l, q⟩ = .ok v) :
    writePlaceState arityOf slots ⟨l, q⟩ rootTy v = .ok slots := by
  have hND : projectionHasDeref q = false := readPlaceState_ok_noDeref hRead
  have hR : evalValueProjRead (slotsToTrustedLocals slots) root q = .ok v := by
    simpa [readPlaceState, hND, get?_eq_getElem?, hSt] using hRead
  rw [writePlaceState_init_root hSt hND (evalValueProjWrite_read_same q _ root v hR)]
  have hLt : l < slots.length := (List.getElem?_eq_some_iff.mp hSt).1
  have hEq : slots[l] = .init root := by
    rw [List.getElem?_eq_getElem hLt] at hSt
    exact Option.some.inj hSt
  rw [← hEq, List.set_getElem_self hLt]

/-- A value-tree read of a non-empty path never succeeds on a scalar. -/
theorem evalValueProjRead_cons_scalar (locals : List LocalSlot) (sc : ScalarInt)
    (e : ProjectionElem) (rest : List ProjectionElem) (w : Value) :
    evalValueProjRead locals (.scalar sc) (e :: rest) ≠ .ok w := by
  cases e <;> simp [evalValueProjRead]

/-- A value-tree write of a non-empty path never succeeds on a scalar. -/
theorem evalValueProjWrite_cons_scalar (locals : List LocalSlot) (sc : ScalarInt)
    (e : ProjectionElem) (rest : List ProjectionElem) (w v' : Value) :
    evalValueProjWrite locals (.scalar sc) (e :: rest) w ≠ .ok v' := by
  cases e <;> simp [evalValueProjWrite]

/-- **Put-Get at a `Deref` target (`writePlaceState_put_get_init`)**: after writing `w` to a
sub-place of an initialized local, reading the sub-place yields `w`. -/
theorem writePlaceState_put_get_init {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {slots slots' : List LocalSlotState} {l : Nat} {q : List ProjectionElem} {rootTy : Ty}
    {root w : Value} (hSt : slots[l]? = some (.init root)) (hNoDeref : projectionHasDeref q = false)
    (h : writePlaceState arityOf slots ⟨l, q⟩ rootTy w = .ok slots') :
    readPlaceState slots' ⟨l, q⟩ = .ok w := by
  obtain ⟨root', hW, rfl⟩ := writePlaceState_init_root_inv hSt hNoDeref h
  have hLt : l < slots.length := (List.getElem?_eq_some_iff.mp hSt).1
  have hRd := evalValueProjRead_write_same q (slotsToTrustedLocals slots) root w root' hW
  unfold readPlaceState
  simp only [hNoDeref, get?_eq_getElem?, List.getElem?_set_self hLt]
  cases q with
  | nil => simpa [evalValueProjRead] using hRd
  | cons e rest =>
    have hNS : ∀ sc, slotStateToTrustedLocal (.init root) ≠ .init (.scalar sc) := by
      intro sc hEq
      simp only [slotStateToTrustedLocal, LocalSlot.init.injEq] at hEq
      subst hEq
      exact evalValueProjWrite_cons_scalar _ sc e rest w root' hW
    have hNS' : ∀ sc, slotStateToTrustedLocal (.init root') ≠ .init (.scalar sc) := by
      intro sc hEq
      simp only [slotStateToTrustedLocal, LocalSlot.init.injEq] at hEq
      subst hEq
      exact evalValueProjRead_cons_scalar _ sc e rest w hRd
    have hSame := sameScalarLocals_set hSt hNS hNS'
    rw [← evalValueProjRead_congr_scalar_locals hSame]
    exact hRd

/-- Reading a whole local depends only on its slot. -/
theorem readPlaceState_root_congr {s s' : List LocalSlotState} {p : Nat} (h : s'[p]? = s[p]?) :
    readPlaceState s' ⟨p, []⟩ = readPlaceState s ⟨p, []⟩ := by
  unfold readPlaceState
  simp only [projectionHasDeref, get?_eq_getElem?, h]
  cases s[p]? with
  | none => rfl
  | some st => cases st <;> simp [evalValueProjRead, readFromPartialShell]

/-- A successful read is of a live local. -/
theorem readPlaceState_ok_live {slots : List LocalSlotState} {place : Place} {v : Value}
    (h : readPlaceState slots place = .ok v) :
    ∃ st, slots[place.local_]? = some st ∧ st ≠ .dead := by
  have hND := readPlaceState_ok_noDeref h
  cases hS : slots[place.local_]? with
  | none => simp [readPlaceState, hND, get?_eq_getElem?, hS] at h
  | some st =>
    refine ⟨st, rfl, fun hD => ?_⟩
    subst hD
    simp [readPlaceState, hND, get?_eq_getElem?, hS] at h

/-- **Stability of synthetic resolution (`resolveSyntheticSubplace_stable`)**: a resolution decided
by the root shortcut or by a unique candidate gives the same sub-place in any frame of the same
size in which the target local is still live and the candidate still passes the runtime checks. -/
theorem resolveSyntheticSubplace_stable {cx : SubplaceCtx} {slots slots' : List LocalSlotState}
    {p : SynPtr} {pty : PtrTy} {ow ow' : Bool} {l : Nat} {q : List ProjectionElem}
    (hRes : resolveSyntheticSubplace cx slots p pty ow = .ok (l, q))
    (hLen : slots'.length = slots.length) (hLive : slots'[l]? ≠ some .dead)
    (hShape : ∀ base, localBaseAddr cx.allocs l cx.limit = some base →
      (p.addr = base ∧ cx.declTy l = some pty.pointee ∧ q = []) ∨
      (cx.candidates pty.pointee l (p.addr - base) = [q] ∧ candConsistent cx slots' l false q = true ∧
        candConsistent cx slots' l true q = true)) :
    resolveSyntheticSubplace cx slots' p pty ow' = .ok (l, q) := by
  obtain ⟨tl, tag, base, allocSize, align, hP, hProv, hlS, hlA, _, hBase, hOwn, hGe, hIn, hWhich⟩ :=
    resolveSyntheticSubplace_sound hRes
  rw [resolveSyntheticSubplace_of_prechecks hP, hProv]
  have hNot : ¬ min slots'.length cx.allocs.length ≤ l := by omega
  have hLt' : ¬ p.addr < base := by omega
  have hIn' : ¬ allocSize < p.addr - base + tl.size := by omega
  simp only [hNot, ↓reduceIte, hBase, hOwn, hLt', hIn']
  have hTail : (if p.addr - base = 0 ∧ cx.declTy l = some pty.pointee then
        (Except.ok (l, []) : Except DerefErr (Nat × List ProjectionElem))
      else
        match selectSubplaceCandidate (cx.candidates pty.pointee l (p.addr - base))
            (candConsistent cx slots' l false) (candConsistent cx slots' l true)
            (cx.decodeTag tag pty.pointee) (tl.size == 0) (subplaceReadable slots' l) ow' with
        | some q => .ok (l, q)
        | none => .error .unsupported) = .ok (l, q) := by
    by_cases hR : p.addr - base = 0 ∧ cx.declTy l = some pty.pointee
    · simp only [hR.1, hR.2, and_self, ↓reduceIte]
      rcases hWhich with ⟨_, _, rfl⟩ | ⟨_, _, hNR, _⟩
      · rfl
      · exact absurd hR hNR
    · simp only [hR, ↓reduceIte]
      rcases hShape base hBase with ⟨hA, hD, _⟩ | ⟨hC, hc1, hc2⟩
      · exact absurd ⟨by omega, hD⟩ hR
      · rw [hC, selectSubplaceCandidate_singleton _ _ _ _ hc1 (fun _ => hc2)]
  cases hS' : slots'[l]? with
  | none => exact hTail
  | some st =>
    cases st with
    | dead => exact absurd hS' hLive
    | _ => exact hTail

/-- **Put-Get through a pointer (`evalDerefPlaceWrite_put_get`)**: writing `v` through `*_p` into
an initialized target sub-place of another local and then reading `*_p` yields `v`, whenever the
pointer's resolution is decided by its root or by a unique candidate whose union path is active
(so that the write does not change which sub-place the pointer designates). -/
theorem evalDerefPlaceWrite_put_get {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {cx : SubplaceCtx} {slots slots' : List LocalSlotState} {p : Nat}
    {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy} {l : Nat} {q : List ProjectionElem}
    {root v : Value} (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz))
    (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty true = .ok (l, q))
    (hNe : l ≠ p) (hTgt : slots[l]? = some (.init root)) (hQ : projectionHasDeref q = false)
    (hShape : ∀ base, localBaseAddr cx.allocs l cx.limit = some base →
      ((cx.ptrOf pv).addr = base ∧ cx.declTy l = some pty.pointee ∧ q = []) ∨
      cx.candidates pty.pointee l ((cx.ptrOf pv).addr - base) = [q])
    (hUnion : ∀ st b, cx.unionActive st q b = true)
    (hW : evalDerefPlaceWrite arityOf rootTyOf cx slots ⟨p, [.deref]⟩ v = .ok slots') :
    evalDerefPlaceRead cx slots' ⟨p, [.deref]⟩ = .ok v := by
  obtain ⟨stp, hStp, hLiveP⟩ := readPlaceState_ok_live hPtr
  have hResT : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty
      (true && ([] : List ProjectionElem).isEmpty) = .ok (l, q) := by simpa using hRes
  have hPl := resolvePlace_deref (rest := []) hStp hLiveP hPtr hTy hResT rfl
  rw [List.append_nil] at hPl
  simp only [evalDerefPlaceWrite, hPl] at hW
  cases hWS : writePlaceState arityOf slots ⟨l, q⟩ (rootTyOf l) v with
  | ub => simp [hWS, liftWrite] at hW
  | unsupported => simp [hWS, liftWrite] at hW
  | ok s =>
    simp only [hWS, liftWrite, Except.ok.injEq] at hW
    subst hW
    have hPG := writePlaceState_put_get_init hTgt hQ hWS
    obtain ⟨root', _, hEq⟩ := writePlaceState_init_root_inv hTgt hQ hWS
    have hLt : l < slots.length := (List.getElem?_eq_some_iff.mp hTgt).1
    have hT' : s[l]? = some (.init root') := by rw [hEq, List.getElem?_set_self hLt]
    have hStp' : s[p]? = slots[p]? := by rw [hEq, List.getElem?_set_ne hNe]
    have hPtr' : readPlaceState s ⟨p, []⟩ = .ok (.ptr pv sz) := by
      rw [readPlaceState_root_congr hStp']
      exact hPtr
    have hEval : evalValueProjRead (slotsToTrustedLocals s) root' q = .ok v := by
      simpa [readPlaceState, hQ, get?_eq_getElem?, hT'] using hPG
    have hCons : ∀ b, candConsistent cx s l b q = true := by
      intro b
      simp [candConsistent, hT', slotStateToFieldSlot, checkSlotProjectionOk, hEval, hUnion]
    have hRes' : resolveSyntheticSubplace cx s (cx.ptrOf pv) pty false = .ok (l, q) := by
      refine resolveSyntheticSubplace_stable hRes (by rw [hEq, List.length_set]) (by simp [hT'])
        (fun base hB => ?_)
      rcases hShape base hB with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hCons false, hCons true⟩
    rw [evalDerefPlaceRead_deref (rest := []) (by rw [hStp']; exact hStp) hLiveP hPtr' hTy hRes' rfl,
      List.append_nil, hPG]
    rfl

/-- **Get-Put through a pointer (`evalDerefPlaceWrite_get_put`)**: writing back, through `*_p`,
the value read through `*_p` from an initialized target leaves the frame unchanged (whenever the
read and write modes resolve `*_p` to the same sub-place). -/
theorem evalDerefPlaceWrite_get_put {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {cx : SubplaceCtx} {slots : List LocalSlotState} {place tgt : Place}
    {root v : Value} (hResR : resolvePlace cx slots place false = .ok tgt)
    (hResW : resolvePlace cx slots place true = .ok tgt)
    (hTgt : slots[tgt.local_]? = some (.init root))
    (hRead : evalDerefPlaceRead cx slots place = .ok v) :
    evalDerefPlaceWrite arityOf rootTyOf cx slots place v = .ok slots := by
  simp only [evalDerefPlaceRead, hResR] at hRead
  have hR : readPlaceState slots tgt = .ok v := by
    cases hRS : readPlaceState slots tgt with
    | ok w => rw [hRS] at hRead; simp only [liftRead, Except.ok.injEq] at hRead; rw [hRead]
    | ub => rw [hRS] at hRead; nomatch hRead
    | unsupported => rw [hRS] at hRead; nomatch hRead
  obtain ⟨l, q⟩ := tgt
  simp only [evalDerefPlaceWrite, hResW, writePlaceState_get_put_init hTgt hR, liftWrite]

/-- **Disjoint-Sibling frame of `Deref` writes (`evalDerefPlaceWrite_read_sibling`)**: a write
through `*_p` into field `f` of an initialized target leaves every disjoint sibling field `g ≠ f`
of the same aggregate (and everything below it) unchanged. -/
theorem evalDerefPlaceWrite_read_sibling {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {cx : SubplaceCtx} {slots slots' : List LocalSlotState} {place : Place}
    {l f g : Nat} {tyF tyG : Ty} {r : List ProjectionElem} {var : Nat} {fields : List Value}
    {v : Value} (hRes : resolvePlace cx slots place true = .ok ⟨l, [.field f tyF]⟩)
    (hTgt : slots[l]? = some (.init (.aggregate var fields))) (hfg : f ≠ g)
    (h : evalDerefPlaceWrite arityOf rootTyOf cx slots place v = .ok slots') :
    readPlaceState slots' ⟨l, .field g tyG :: r⟩ = readPlaceState slots ⟨l, .field g tyG :: r⟩ := by
  simp only [evalDerefPlaceWrite, hRes] at h
  cases hWS : writePlaceState arityOf slots ⟨l, [.field f tyF]⟩ (rootTyOf l) v with
  | ub => simp [hWS, liftWrite] at h
  | unsupported => simp [hWS, liftWrite] at h
  | ok s =>
    simp only [hWS, liftWrite, Except.ok.injEq] at h
    subst h
    obtain ⟨root', hW, hEq⟩ := writePlaceState_init_root_inv hTgt (by rfl) hWS
    have hLt : l < slots.length := (List.getElem?_eq_some_iff.mp hTgt).1
    -- the written aggregate differs from the old one only at field `f`
    simp only [evalValueProjWrite, get?_eq_getElem?] at hW
    cases hF : fields[f]? with
    | none => rw [hF] at hW; nomatch hW
    | some old =>
      rw [hF] at hW
      cases hSet : set? fields f v with
      | none => rw [hSet] at hW; nomatch hW
      | some fields' =>
        rw [hSet] at hW
        simp only [ProjWriteResult.ok.injEq] at hW
        subst hW
        have hG : fields'[g]? = fields[g]? := by
          obtain ⟨_, rfl⟩ := set?_eq_some_iff.mp hSet
          exact List.getElem?_set_ne hfg
        have hNS : ∀ sc, slotStateToTrustedLocal (.init (.aggregate var fields)) ≠ .init (.scalar sc) := by
          intro sc hE; simp [slotStateToTrustedLocal] at hE
        have hNS' : ∀ sc, slotStateToTrustedLocal (.init (.aggregate var fields')) ≠ .init (.scalar sc) := by
          intro sc hE; simp [slotStateToTrustedLocal] at hE
        have hSame := sameScalarLocals_set (new := .init (.aggregate var fields')) hTgt hNS hNS'
        rw [hEq]
        unfold readPlaceState
        simp only [get?_eq_getElem?, List.getElem?_set_self hLt, hTgt]
        split
        · rfl
        · rw [← evalValueProjRead_congr_scalar_locals hSame]
          simp only [evalValueProjRead, get?_eq_getElem?, hG]

/-- **`Deinit` through a pointer (`evalDerefPlaceDeinit_target`)**: `Deinit((*_p).rest)`
deinitializes exactly the resolved target sub-place: the frame changes only at the target local
(so `_p` keeps its slot when the target is another local), and the target then reads as
uninitialized (Get-Deinit of Section 2a). -/
theorem evalDerefPlaceDeinit_target {ts : Bool} {cx : SubplaceCtx}
    {slots slots' : List LocalSlotState} {place : Place} {l : Nat} {q : List ProjectionElem}
    (hRes : resolvePlace cx slots place false = .ok ⟨l, q⟩)
    (h : evalDerefPlaceDeinit ts cx slots place = .ok slots') :
    evalDeinitPlace ts slots ⟨l, q⟩ = some slots' ∧
      (∀ j, j ≠ l → slots'[j]? = slots[j]?) ∧
      readPlaceState slots' ⟨l, q⟩ = .ub := by
  simp only [evalDerefPlaceDeinit, hRes] at h
  cases hD : evalDeinitPlace ts slots ⟨l, q⟩ with
  | none => rw [hD] at h; nomatch h
  | some s =>
    rw [hD] at h
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨_, _, _, slot', hDS, hEq⟩ := evalDeinitPlace_eq_some hD
    refine ⟨rfl, fun j hj => ?_,
      evalDeinitPlace_read_same_ub hD (Or.inl ⟨[], (List.append_nil _).symm⟩)
        (deinitFieldSlot_noDeref hDS)⟩
    rw [hEq]
    exact List.getElem?_set_ne (Ne.symm hj)

/-! ### Section 4e: `Retag` of synthetic sub-place references (dangling `DeadLocal` detection) -/

/-- The `Retag` context of a synthetic frame: Anneal's address of a pointer value, and the local
its synthetic provenance names (`resolve_synthetic_alloc_local`: by `alloc_id` alone, at the
local's base address or at any sub-place offset). -/
def synthRetagCtx (cx : SubplaceCtx) (ptrBits : Nat) (slots : List LocalSlotState) : RetagCtx where
  ptrBits := ptrBits
  addrOf pv := (cx.ptrOf pv).addr
  localOf pv :=
    match (cx.ptrOf pv).prov with
    | some (l + 1, _) => if l < slots.length then some l else none
    | _ => none
  slots := slots

/-- **Dangling sub-place references fault (`retag_subplace_ref_dead_local`)**: retagging a reference
whose synthetic provenance names a storage-dead local fails (`DeadLocal`) for every non-zero-sized
pointee — in particular a reference to a sub-place `&_s.f` at a non-zero offset `relOff > 0` from
the dead local's base address, which the base-address-only resolution `resolveSyntheticLocal`
does not recognize as that local. -/
theorem retag_subplace_ref_dead_local (cx : SubplaceCtx) (ptrBits : Nat)
    (slots : List LocalSlotState) (pt : RetagPointee) (pv : ProvenancePtr) {l tag : Nat}
    (hProv : (cx.ptrOf pv).prov = some (l + 1, tag)) (hDead : slots[l]? = some .dead)
    (hNZ : pt.zeroSized = false) :
    retagRefOk (synthRetagCtx cx ptrBits slots) pt pv = false := by
  obtain ⟨hlt, hEq⟩ := List.getElem?_eq_some_iff.mp hDead
  have hLive : retagTargetLive (synthRetagCtx cx ptrBits slots) pt pv = false := by
    simp [retagTargetLive, synthRetagCtx, hProv, hlt, hEq, hNZ]
  simp [retagRefOk, hLive]

/-- The legacy base-address-only resolution misses such a dangling sub-place reference: a pointer
at offset `relOff > 0` from its provenance local's base address is not that local's base pointer. -/
theorem resolveSyntheticLocal_misses_subplace (env : CopyEnv) (n : Nat) (p : CopyPtr) {l : Nat}
    (hl : provenanceLocal n p = some l) (hOff : p.addr ≠ env.baseAddr l) :
    resolveSyntheticLocal env n p = none := by
  simp [resolveSyntheticLocal, hl, hOff]

/-- `Retag` of a place through `Deref` (`retag_place` after `prepare_place_access` resolves every
`Deref` to its live synthetic target): the target sub-place is retagged by `evalRetagPlace`. -/
def evalRetagDerefPlace (cx : SubplaceCtx) (ctx : RetagCtx) (kind : RetagKind) (place : Place)
    (ty : RetagTy) (rawPtrPlace : Bool) : Bool :=
  match resolvePlace cx ctx.slots place false with
  | .ok tgt => evalRetagPlace ctx kind tgt ty rawPtrPlace
  | .error _ => false

/-- `Retag` through `Deref` is `evalRetagPlace` of the resolved target; a dangling pointer
(target local dead) or an unresolvable one fails. -/
theorem evalRetagDerefPlace_eq {cx : SubplaceCtx} {ctx : RetagCtx} {kind : RetagKind}
    {place tgt : Place} {ty : RetagTy} {b : Bool}
    (hRes : resolvePlace cx ctx.slots place false = .ok tgt) :
    evalRetagDerefPlace cx ctx kind place ty b = evalRetagPlace ctx kind tgt ty b := by
  simp [evalRetagDerefPlace, hRes]

/-- A `Deref`-free place is retagged exactly as before (conservative extension). -/
theorem evalRetagDerefPlace_noDeref {cx : SubplaceCtx} {ctx : RetagCtx} {kind : RetagKind}
    {place : Place} {ty : RetagTy} {b : Bool} {st : LocalSlotState}
    (hSt : ctx.slots[place.local_]? = some st) (hLive : st ≠ .dead)
    (hNoDeref : projectionHasDeref place.projection = false) :
    evalRetagDerefPlace cx ctx kind place ty b = evalRetagPlace ctx kind place ty b :=
  evalRetagDerefPlace_eq (resolvePlace_noDeref false hSt hLive hNoDeref)

/-! ### Section 4f: Step refinement of `Deref` accesses against `Trusted.Rustc.V2026_06_01.MirSemantics`

Trusted tracks a pointer by its borrow-table tag (`BorrowEntry.targetLocal` /
`targetProjection`), Anneal by its synthetic address and provenance. The refinement theorems
below relate the two through the pointer correspondence "Trusted's borrow entry for the pointer's
tag names exactly the sub-place that Anneal's address-based resolution designates", and show that
every successful Anneal `Deref` access of runtime MIR's shape `⟨p, .deref :: rest⟩` is matched by
Trusted (`evalOperand`, `writePlaceValue`, and `evalStmt` `.assign`) with the same value, keeping
the frames related by `SlotsRefine SlotBelow`. Reads are refined in Trusted's untyped mode (empty
`localDecls`) and, for scalar reads of `*_p`, in its typed mode (non-empty `localDecls`, read through
`evalStackThinPtrTypedDerefRead`), whose extra pointee-type checks (scalar width, offset, target
alignment, no union, bit validity) are hypotheses about Trusted's types and frame. -/

theorem appendProjections_eq_append :
    ∀ (xs ys : List ProjectionElem), appendProjections xs ys = xs ++ ys
  | [], _ => rfl
  | x :: xs, ys => by simp only [appendProjections, appendProjections_eq_append xs ys, List.cons_append]

/-- A static sub-place path has no `Deref`. -/
theorem subplaceAt_noDeref :
    ∀ {lay : ByteLayout} {base : Nat} {p : List ProjectionElem} {l : ByteLayout} {o : Nat},
      subplaceAt lay base p = some (l, o) → projectionHasDeref p = false
  | _, _, [], _, _, _ => rfl
  | lay, base, .downcast _ _ :: rest, l, o, h => by
    simp only [subplaceAt] at h
    simpa [projectionHasDeref] using subplaceAt_noDeref h
  | .leaf _, _, .field _ _ :: _, _, _, h => by simp [subplaceAt] at h
  | .leaf _, _, .constantIndex _ _ _ :: _, _, _, h => by simp [subplaceAt] at h
  | .struct n offs ls, base, .field f ty :: rest, l, o, h => by
    obtain ⟨o', l', _, _, h'⟩ := subplaceAt_struct_child (Or.inl ⟨ty, rfl⟩) h
    simpa [projectionHasDeref] using subplaceAt_noDeref h'
  | .struct n offs ls, base, .constantIndex k m fromEnd :: rest, l, o, h => by
    cases fromEnd with
    | true => simp [subplaceAt] at h
    | false =>
      obtain ⟨o', l', _, _, h'⟩ := subplaceAt_struct_child (Or.inr ⟨m, rfl⟩) h
      simpa [projectionHasDeref] using subplaceAt_noDeref h'
  | _, _, .deref :: _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h
  | _, _, .index _ :: _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h
  | _, _, .subslice _ _ _ :: _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h
  | _, _, .opaqueCast _ :: _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h
  | _, _, .unwrapUnsafeBinder _ :: _, _, _, h => by cases ‹ByteLayout› <;> simp [subplaceAt] at h

/-- In a well-formed context, every resolved sub-place is a static (`Deref`-free) path. -/
theorem resolveSyntheticSubplace_noDeref {cx : SubplaceCtx} (hWF : cx.WF)
    {slots : List LocalSlotState} {p : SynPtr} {pty : PtrTy} {ow : Bool} {l : Nat}
    {q : List ProjectionElem} (h : resolveSyntheticSubplace cx slots p pty ow = .ok (l, q)) :
    projectionHasDeref q = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hWhich⟩ := resolveSyntheticSubplace_sound h
  rcases hWhich with ⟨_, _, rfl⟩ | ⟨i, C, _, _, _, hq, _⟩
  · rfl
  · obtain ⟨lay, sub, tl, _, hSub, _, _⟩ := hWF.candidates _ _ _ q (List.mem_of_getElem? hq)
    exact subplaceAt_noDeref hSub

theorem projectionHasDeref_append : ∀ (xs ys : List ProjectionElem),
    projectionHasDeref (xs ++ ys) = (projectionHasDeref xs || projectionHasDeref ys)
  | [], ys => by simp [projectionHasDeref]
  | x :: xs, ys => by cases x <;> simp [projectionHasDeref, projectionHasDeref_append xs ys]

/-- **`Deref` reads refine Trusted's `evalOperand` (`evalDerefPlaceRead_refines_evalOperand`)**:
on below-related frames, if Anneal reads `v` from `(*_p).rest` and Trusted's (non-disabled)
borrow entry for `_p`'s tag names the sub-place Anneal resolves `*_p` to, then Trusted's
`Operand.copy ((*_p).rest)` evaluates to the same `v` without changing the frame. -/
theorem evalDerefPlaceRead_refines_evalOperand {cx : SubplaceCtx}
    {slots : List LocalSlotState} {locals : List LocalSlot} {p : Nat} {rest : List ProjectionElem}
    {v : Value} {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy} {borrows : List BorrowEntry}
    {entry : BorrowEntry} (hRel : SlotsRefine SlotBelow slots locals)
    (hRest : projectionHasDeref rest = false)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz)) (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty false =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow borrows pv.tag = some entry) (hPerm : entry.perm ≠ .disabled)
    (hThin : needsThinPtrElemResolution entry.targetProjection pv.offsetBytes = false)
    (hRead : evalDerefPlaceRead cx slots ⟨p, .deref :: rest⟩ = .ok v)
    (globals : List CapturedAllocation) (layouts : LayoutTable) (callerLocals : List LocalSlot) :
    evalOperand locals (.copy ⟨p, .deref :: rest⟩) borrows globals layouts callerLocals =
      .ok v locals := by
  obtain ⟨stp, hStp, hLiveP⟩ := readPlaceState_ok_live hPtr
  rw [evalDerefPlaceRead_deref hStp hLiveP hPtr hTy hRes hRest] at hRead
  have hTR : readPlaceState slots ⟨entry.targetLocal, entry.targetProjection ++ rest⟩ = .ok v := by
    cases hRS : readPlaceState slots ⟨entry.targetLocal, entry.targetProjection ++ rest⟩ with
    | ok w => rw [hRS] at hRead; simp only [liftRead, Except.ok.injEq] at hRead; rw [hRead]
    | ub => rw [hRS] at hRead; nomatch hRead
    | unsupported => rw [hRS] at hRead; nomatch hRead
  obtain ⟨rootVal, ht, hr⟩ := readPlaceState_below_refines hRel hTR
  obtain ⟨rootP, hp, hrp⟩ := readPlaceState_below_refines hRel hPtr
  simp only [readProjectedValue] at hrp
  cases hrp
  simp only [get?_eq_getElem?] at ht hp
  rw [← appendProjections_eq_append] at hr
  cases htp : entry.targetProjection with
  | nil =>
    rw [htp] at hr
    simp only [appendProjections] at hr
    cases hpe : entry.perm with
    | disabled => exact absurd hpe hPerm
    | _ => simp [evalOperand, get?_eq_getElem?, hp, hEntry, hpe, ht, htp, hr]
  | cons ph pt =>
    rw [htp] at hr hThin
    simp only [appendProjections] at hr
    cases hpe : entry.perm with
    | disabled => exact absurd hpe hPerm
    | _ => simp [evalOperand, get?_eq_getElem?, hp, hEntry, hpe, ht, htp, hr, hThin]

/-- **`Deref` reads refine Trusted's `evalRvalue` (`evalDerefPlaceRead_refines_evalRvalue`)**: under
the hypotheses of `evalDerefPlaceRead_refines_evalOperand`, Trusted's `Rvalue.use (copy (*_p).rest)`
evaluates to the same value without changing the frame (Trusted may only freeze the read tags of
its borrow table). -/
theorem evalDerefPlaceRead_refines_evalRvalue {cx : SubplaceCtx}
    {slots : List LocalSlotState} {locals : List LocalSlot} {p : Nat} {rest : List ProjectionElem}
    {v : Value} {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy} {mem : Memory}
    {entry : BorrowEntry} (hRel : SlotsRefine SlotBelow slots locals)
    (hRest : projectionHasDeref rest = false)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz)) (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty false =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow mem.borrows pv.tag = some entry) (hPerm : entry.perm ≠ .disabled)
    (hThin : needsThinPtrElemResolution entry.targetProjection pv.offsetBytes = false)
    (hRead : evalDerefPlaceRead cx slots ⟨p, .deref :: rest⟩ = .ok v) (layouts : LayoutTable) :
    ∃ mem', evalRvalue locals (.use (.copy ⟨p, .deref :: rest⟩)) mem [] layouts = .ok v locals mem' := by
  have hOp := evalDerefPlaceRead_refines_evalOperand hRel hRest hPtr hTy hRes hEntry hPerm hThin
    hRead mem.globals layouts mem.callerLocals
  have hV : validateLoadedValue layouts [] (.copy ⟨p, .deref :: rest⟩) v = true := by
    simp [validateLoadedValue, operandTy, placeTy]
  simp only [evalRvalue, hOp, hV]
  cases hb : mem.borrows with
  | nil => exact ⟨_, rfl⟩
  | cons b₁ bs =>
    cases bs with
    | nil => exact ⟨_, rfl⟩
    | cons b₂ bs => exact ⟨_, rfl⟩

/-- Trusted's scalar widths (`tyScalarBytes`) are positive. -/
theorem tyScalarBytes_pos {ty : Ty} {n : Nat} (h : tyScalarBytes ty = some n) : 1 ≤ n := by
  unfold tyScalarBytes at h
  split at h
  · simp only [Option.some.injEq] at h; omega
  · simp only [Option.some.injEq] at h; omega
  · unfold intCastTargetBytes at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> omega

/-- **Typed `Deref` reads refine Trusted's typed `evalOperand`
(`evalDerefPlaceRead_refines_evalOperand_typed`)**: with non-empty `localDecls`, Trusted reads
`Operand.copy (*_p)` through `evalStackThinPtrTypedDerefRead` (pointee-type alignment, scalar
width slicing at the pointer's offset, and bit validity). Under the correspondence hypotheses of
`evalDerefPlaceRead_refines_evalOperand` (below-related frames; Trusted's non-disabled borrow
entry for `_p`'s tag names the sub-place Anneal resolves `*_p` to), if Anneal reads the scalar `sc`
from `*_p`, then Trusted's typed `evalOperand` reads the same `sc` without changing the frame,
provided Trusted's typed checks pass: the resolved pointee type `pTy` is a scalar type of `sc`'s
width, the pointer sits at offset `0` of its borrow target, the target place is aligned for `pTy`
(`checkTargetPlaceAlign` on Trusted's target root) and touches no union, and `sc` is a valid value
of `pTy` (`validateValueForTy?`). Trusted's target value is derived from Anneal's read through
`readPlaceState_below_refines`, not assumed. -/
theorem evalDerefPlaceRead_refines_evalOperand_typed {cx : SubplaceCtx}
    {slots : List LocalSlotState} {locals : List LocalSlot} {p : Nat} {sc : ScalarInt}
    {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy} {borrows : List BorrowEntry}
    {entry : BorrowEntry} {localDecls : List LocalDecl} {layouts : LayoutTable} {pTy : Ty}
    {n : Nat} (hRel : SlotsRefine SlotBelow slots locals)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz)) (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty false =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow borrows pv.tag = some entry) (hPerm : entry.perm ≠ .disabled)
    (hRead : evalDerefPlaceRead cx slots ⟨p, [.deref]⟩ = .ok (.scalar sc))
    (hDecls : localDecls ≠ [])
    (hPTy : placeTyResolved localDecls layouts ⟨p, [.deref]⟩ = some pTy)
    (hScalar : tyScalarBytes (resolveTyWithLocalDecls localDecls layouts pTy) = some n)
    (hWidth : sc.sizeBytes = n) (hOff : pv.offsetBytes = 0)
    (hAlign : ∀ rootVal, get? locals entry.targetLocal = some (.init rootVal) →
      checkTargetPlaceAlign localDecls layouts
        (some (resolveTyWithLocalDecls localDecls layouts pTy)) entry pv (some rootVal) = true)
    (hNoUnion : placeTouchesUnion localDecls layouts
      ⟨entry.targetLocal, entry.targetProjection⟩ = false)
    (hValid : validateValueForTy? layouts
      (some (resolveTyWithLocalDecls localDecls layouts pTy)) (.scalar sc) = true)
    (globals : List CapturedAllocation) (callerLocals : List LocalSlot) :
    evalOperand locals (.copy ⟨p, [.deref]⟩) borrows globals layouts callerLocals localDecls =
      .ok (.scalar sc) locals := by
  obtain ⟨stp, hStp, hLiveP⟩ := readPlaceState_ok_live hPtr
  rw [evalDerefPlaceRead_deref hStp hLiveP hPtr hTy hRes rfl, List.append_nil] at hRead
  have hTR : readPlaceState slots ⟨entry.targetLocal, entry.targetProjection⟩ =
      .ok (.scalar sc) := by
    cases hRS : readPlaceState slots ⟨entry.targetLocal, entry.targetProjection⟩ with
    | ok w => rw [hRS] at hRead; simp only [liftRead, Except.ok.injEq] at hRead; rw [hRead]
    | ub => rw [hRS] at hRead; nomatch hRead
    | unsupported => rw [hRS] at hRead; nomatch hRead
  obtain ⟨rootVal, ht, hr⟩ := readPlaceState_below_refines hRel hTR
  obtain ⟨rootP, hp, hrp⟩ := readPlaceState_below_refines hRel hPtr
  simp only [readProjectedValue] at hrp
  cases hrp
  obtain ⟨d0, ds, hcons⟩ : ∃ d0 ds, localDecls = d0 :: ds := by
    cases h : localDecls with
    | nil => exact absurd h hDecls
    | cons d0 ds => exact ⟨d0, ds, rfl⟩
  have hAl := hAlign rootVal ht
  have hextract : extractScalarSlice? sc 0 n = some sc := by
    have hpos := tyScalarBytes_pos hScalar
    unfold extractScalarSlice?
    have hb1 : Bool.and (Nat.ble 1 n) (Nat.ble (Nat.add 0 n) sc.sizeBytes) = true := by
      simp [Nat.ble_eq, hpos, hWidth]
    have hb2 : Bool.and (Nat.beq 0 0) (Nat.beq n sc.sizeBytes) = true := by
      simp [hWidth]
    rw [hb1, hb2]
  unfold evalOperand
  dsimp only
  rw [hp]
  dsimp only
  rw [hcons]
  dsimp only
  rw [← hcons, hEntry]
  dsimp only
  cases hpe : entry.perm with
  | disabled => exact absurd hpe hPerm
  | _ =>
    dsimp only
    rw [ht]
    dsimp only
    unfold evalStackThinPtrTypedDerefRead
    rw [hPTy, hOff]
    dsimp only [stripTransparentProjections, checkDerefAlign, Nat.beq_refl]
    rw [hAl]
    simp only [Bool.and_self]
    rw [hcons]
    dsimp only [stripTransparentProjections]
    rw [← hcons, hScalar]
    dsimp only [stripTransparentProjections]
    cases hproj : entry.targetProjection with
    | nil =>
      rw [hproj] at hr
      dsimp only [readProjectedForLocal]
      rw [hr]
      dsimp only
      rw [hextract]
      dsimp only
      rw [hValid]
    | cons ph pt =>
      rw [hproj] at hr hNoUnion
      simp only [appendProjections_eq_append, List.append_nil]
      dsimp only [readProjectedForLocal]
      rw [hNoUnion]
      dsimp only
      rw [hr]
      dsimp only
      rw [hextract]
      dsimp only
      rw [hValid]

/-- **`Rvalue.use` of a `Deref` copy (`evalRvalue_use_copy_of_evalOperand`)**: for any
`localDecls`, Trusted's `evalRvalue` of `Rvalue.use (copy (*_p).rest)` returns the value and frame
of `evalOperand` once `validateLoadedValue` accepts the value (Trusted may only freeze the read
tags of its borrow table). -/
theorem evalRvalue_use_copy_of_evalOperand {locals : List LocalSlot} {p : Nat}
    {rest : List ProjectionElem} {v : Value} {mem : Memory} {localDecls : List LocalDecl}
    {layouts : LayoutTable}
    (hOp : evalOperand locals (.copy ⟨p, .deref :: rest⟩) mem.borrows mem.globals layouts
      mem.callerLocals localDecls = .ok v locals)
    (hValid : validateLoadedValue layouts localDecls (.copy ⟨p, .deref :: rest⟩) v = true) :
    ∃ mem', evalRvalue locals (.use (.copy ⟨p, .deref :: rest⟩)) mem localDecls layouts =
      .ok v locals mem' := by
  simp only [evalRvalue, hOp, hValid]
  cases hb : mem.borrows with
  | nil => exact ⟨_, rfl⟩
  | cons b₁ bs =>
    cases bs with
    | nil => exact ⟨_, rfl⟩
    | cons b₂ bs => exact ⟨_, rfl⟩

/-- **Typed `Deref` reads refine Trusted's typed `evalRvalue`
(`evalDerefPlaceRead_refines_evalRvalue_typed`)**: under the hypotheses of
`evalDerefPlaceRead_refines_evalOperand_typed` and Trusted's load validation of the read scalar
(`validateLoadedValue`), Trusted's typed `Rvalue.use (copy (*_p))` evaluates to the scalar Anneal
reads from `*_p`, without changing the frame. -/
theorem evalDerefPlaceRead_refines_evalRvalue_typed {cx : SubplaceCtx}
    {slots : List LocalSlotState} {locals : List LocalSlot} {p : Nat} {sc : ScalarInt}
    {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy} {mem : Memory}
    {entry : BorrowEntry} {localDecls : List LocalDecl} {layouts : LayoutTable} {pTy : Ty}
    {n : Nat} (hRel : SlotsRefine SlotBelow slots locals)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz)) (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty false =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow mem.borrows pv.tag = some entry) (hPerm : entry.perm ≠ .disabled)
    (hRead : evalDerefPlaceRead cx slots ⟨p, [.deref]⟩ = .ok (.scalar sc))
    (hDecls : localDecls ≠ [])
    (hPTy : placeTyResolved localDecls layouts ⟨p, [.deref]⟩ = some pTy)
    (hScalar : tyScalarBytes (resolveTyWithLocalDecls localDecls layouts pTy) = some n)
    (hWidth : sc.sizeBytes = n) (hOff : pv.offsetBytes = 0)
    (hAlign : ∀ rootVal, get? locals entry.targetLocal = some (.init rootVal) →
      checkTargetPlaceAlign localDecls layouts
        (some (resolveTyWithLocalDecls localDecls layouts pTy)) entry pv (some rootVal) = true)
    (hNoUnion : placeTouchesUnion localDecls layouts
      ⟨entry.targetLocal, entry.targetProjection⟩ = false)
    (hValid : validateValueForTy? layouts
      (some (resolveTyWithLocalDecls localDecls layouts pTy)) (.scalar sc) = true)
    (hLoad : validateLoadedValue layouts localDecls (.copy ⟨p, [.deref]⟩) (.scalar sc) = true) :
    ∃ mem', evalRvalue locals (.use (.copy ⟨p, [.deref]⟩)) mem localDecls layouts =
      .ok (.scalar sc) locals mem' :=
  evalRvalue_use_copy_of_evalOperand
    (evalDerefPlaceRead_refines_evalOperand_typed hRel hPtr hTy hRes hEntry hPerm hRead hDecls
      hPTy hScalar hWidth hOff hAlign hNoUnion hValid mem.globals mem.callerLocals) hLoad

/-- **`Deref` writes refine Trusted's `writePlaceValue` (`evalDerefPlaceWrite_refines_writePlaceValue`)**:
on below-related frames, if Anneal writes `v` through `(*_p).rest` into an initialized target and
Trusted's writable (`active`/`reserved`) borrow entry for `_p`'s tag names the sub-place Anneal
resolves `*_p` to, then Trusted's `writePlaceValue` succeeds and the updated frames stay related
by `SlotsRefine SlotBelow`. -/
theorem evalDerefPlaceWrite_refines_writePlaceValue {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {cx : SubplaceCtx} (hWF : cx.WF) {slots slots' : List LocalSlotState}
    {locals : List LocalSlot} {p : Nat} {rest : List ProjectionElem} {v root : Value}
    {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy} {borrows : List BorrowEntry}
    {entry : BorrowEntry} (hRel : SlotsRefine SlotBelow slots locals)
    (hRest : projectionHasDeref rest = false)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz)) (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty rest.isEmpty =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow borrows pv.tag = some entry)
    (hPerm : entry.perm = .active ∨ entry.perm = .reserved)
    (hThin : needsThinPtrElemResolution entry.targetProjection pv.offsetBytes = false)
    (hTgt : slots[entry.targetLocal]? = some (.init root))
    (hW : evalDerefPlaceWrite arityOf rootTyOf cx slots ⟨p, .deref :: rest⟩ v = .ok slots') :
    ∃ locals', writePlaceValue locals borrows ⟨p, .deref :: rest⟩ v = .ok locals' ∧
      SlotsRefine SlotBelow slots' locals' := by
  obtain ⟨stp, hStp, hLiveP⟩ := readPlaceState_ok_live hPtr
  have hResT : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty (true && rest.isEmpty) =
      .ok (entry.targetLocal, entry.targetProjection) := by simpa using hRes
  have hPl := resolvePlace_deref hStp hLiveP hPtr hTy hResT hRest
  simp only [evalDerefPlaceWrite, hPl] at hW
  have hQ : projectionHasDeref (entry.targetProjection ++ rest) = false := by
    rw [projectionHasDeref_append, resolveSyntheticSubplace_noDeref hWF hRes, hRest]; rfl
  cases hWS : writePlaceState arityOf slots ⟨entry.targetLocal, entry.targetProjection ++ rest⟩
      (rootTyOf entry.targetLocal) v with
  | ub => simp [hWS, liftWrite] at hW
  | unsupported => simp [hWS, liftWrite] at hW
  | ok s =>
    simp only [hWS, liftWrite, Except.ok.injEq] at hW
    subst hW
    obtain ⟨root', hWr, hEq⟩ := writePlaceState_init_root_inv hTgt hQ hWS
    subst hEq
    have hSame := sameScalarLocals_of_slotBelow hRel
    have hWT : evalValueProjWrite locals root (entry.targetProjection ++ rest) v = .ok root' := by
      rw [← evalValueProjWrite_congr_scalar_locals hSame]; exact hWr
    have hWP := evalValueProjWrite_refines_writeProjectedValue _ _ _ _ _ hWT
    obtain ⟨rootP, hp, hrp⟩ := readPlaceState_below_refines hRel hPtr
    simp only [readProjectedValue] at hrp
    cases hrp
    have hTT : locals[entry.targetLocal]? = some (.init root) := by
      rcases SlotsRefine.get?_rel entry.targetLocal hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, hAT⟩
      · simp only [get?_eq_getElem?] at hA; rw [hA] at hTgt; nomatch hTgt
      · simp only [get?_eq_getElem?] at hA hT
        rw [hA] at hTgt
        cases hTgt
        cases t with
        | init w => have hvw : root = w := hAT; subst hvw; exact hT
        | _ => simp [SlotBelow] at hAT
    have hLtT : entry.targetLocal < locals.length := (List.getElem?_eq_some_iff.mp hTT).1
    refine ⟨locals.set entry.targetLocal (.init root'), ?_,
      SlotsRefine.set (a := .init root') (t := .init root') rfl _ hRel⟩
    simp only [get?_eq_getElem?] at hp
    have hSet : set? locals entry.targetLocal (.init root') =
        some (locals.set entry.targetLocal (.init root')) := set?_eq_some_iff.mpr ⟨hLtT, rfl⟩
    cases htp : entry.targetProjection with
    | nil =>
      rw [htp] at hWP hThin hWr
      cases rest with
      | nil =>
        have hRV : root' = v := by
          simp only [List.append_nil, evalValueProjWrite, ProjWriteResult.ok.injEq] at hWr
          exact hWr.symm
        subst hRV
        rcases hPerm with hpe | hpe <;>
          simp [writePlaceValue, get?_eq_getElem?, hp, hEntry, hpe, htp, hTT, hSet]
      | cons r rs =>
        simp only [List.nil_append] at hWP
        rcases hPerm with hpe | hpe <;>
          simp [writePlaceValue, get?_eq_getElem?, hp, hEntry, hpe, htp, hTT, hWP, hSet]
    | cons ph pt =>
      rw [htp] at hWP hThin
      rw [← appendProjections_eq_append] at hWP
      simp only [appendProjections] at hWP
      rcases hPerm with hpe | hpe <;>
        simp [writePlaceValue, get?_eq_getElem?, hp, hEntry, hpe, htp, hThin, hTT, hWP, hSet]

/-- **`Deref` assignments refine Trusted's `evalStmt` (`evalStmt_assign_deref_refines`)**: with no
active function-entry protector, when Trusted evaluates the rvalue to `v` without changing the
frame, a successful Anneal write of `v` through `(*_p).rest` (as above) is matched by Trusted's
`evalStmt` stepping the `.assign` with the written frame and the deref-write borrow invalidation,
keeping the frames related by `SlotsRefine SlotBelow`. -/
theorem evalStmt_assign_deref_refines {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {cx : SubplaceCtx} (hWF : cx.WF) {slots slots' : List LocalSlotState}
    (s : MachineState) {p : Nat} {rest : List ProjectionElem} (rv : Rvalue) (span : String)
    {v root : Value} {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy} {entry : BorrowEntry}
    (hprot : s.memory.activeProtectors = [])
    (hv : evalRvalue s.frame.locals rv s.memory = .ok v s.frame.locals s.memory)
    (hRel : SlotsRefine SlotBelow slots s.frame.locals)
    (hRest : projectionHasDeref rest = false)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz)) (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty rest.isEmpty =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow s.memory.borrows pv.tag = some entry)
    (hPerm : entry.perm = .active ∨ entry.perm = .reserved)
    (hThin : needsThinPtrElemResolution entry.targetProjection pv.offsetBytes = false)
    (hTgt : slots[entry.targetLocal]? = some (.init root))
    (hW : evalDerefPlaceWrite arityOf rootTyOf cx slots ⟨p, .deref :: rest⟩ v = .ok slots') :
    ∃ locals', evalStmt s ⟨.assign ⟨p, .deref :: rest⟩ rv, span⟩ =
        MirStepNode.step (advanceStmt s locals'
          { s.memory with
            borrows := invalidateDerefWriteBorrows s.frame.locals s.memory.borrows
              ⟨p, .deref :: rest⟩ rest }) ∧
      SlotsRefine SlotBelow slots' locals' := by
  obtain ⟨locals', hWV, hRel'⟩ := evalDerefPlaceWrite_refines_writePlaceValue hWF hRel hRest hPtr
    hTy hRes hEntry hPerm hThin hTgt hW
  refine ⟨locals', ?_, hRel'⟩
  simp only [evalStmt, hv, evalPlaceWrite, hprot, hWV]

theorem appendProjections_nil_right :
    ∀ (xs : List ProjectionElem), appendProjections xs [] = xs
  | [] => rfl
  | x :: xs => by simp [appendProjections, appendProjections_nil_right xs]

/-- **Typed `Deref` writes refine Trusted's typed `writePlaceValue`
(`evalDerefPlaceWrite_refines_writePlaceValue_typed`)**: with non-empty `localDecls`, Trusted writes
`*_p = .scalar wSc` through `writeStackThinPtrTypedDeref` (checking `checkDerefAlign`,
`checkTargetPlaceAlign`, `validateValueForTy?`, and splicing `wSc` into the old scalar at offset
`0`). On below-related frames, if Anneal writes `.scalar wSc` through `*_p` into an initialized
target whose current sub-place holds `.scalar oldSc` of the same width, and Trusted's typed checks
pass, then Trusted's typed `writePlaceValue` succeeds and the updated frames stay related by
`SlotsRefine SlotBelow`. -/
theorem evalDerefPlaceWrite_refines_writePlaceValue_typed
    {arityOf : Ty → VariantIdx → Bool → Option Nat} {rootTyOf : Nat → Ty}
    {cx : SubplaceCtx} (hWF : cx.WF) {slots slots' : List LocalSlotState}
    {locals : List LocalSlot} {p : Nat} {oldSc wSc : ScalarInt} {root : Value}
    {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy} {borrows : List BorrowEntry}
    {entry : BorrowEntry} {localDecls : List LocalDecl} {layouts : LayoutTable} {pTy : Ty}
    (hRel : SlotsRefine SlotBelow slots locals)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz))
    (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty true =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow borrows pv.tag = some entry)
    (hPerm : entry.perm = .active ∨ entry.perm = .reserved)
    (hTgt : slots[entry.targetLocal]? = some (.init root))
    (hOld : readPlaceState slots ⟨entry.targetLocal, entry.targetProjection⟩ = .ok (.scalar oldSc))
    (hW : evalDerefPlaceWrite arityOf rootTyOf cx slots ⟨p, [.deref]⟩ (.scalar wSc) = .ok slots')
    (hDecls : localDecls ≠ [])
    (hPTy : placeTyResolved localDecls layouts ⟨p, [.deref]⟩ = some pTy)
    (hPos : 1 ≤ wSc.sizeBytes)
    (hWidth : wSc.sizeBytes = oldSc.sizeBytes)
    (hOff : pv.offsetBytes = 0)
    (hAlign : checkTargetPlaceAlign localDecls layouts
      (some (resolveTyWithLocalDecls localDecls layouts pTy)) entry pv (some root) = true)
    (hNoUnion : placeTouchesUnion localDecls layouts
      ⟨entry.targetLocal, entry.targetProjection⟩ = false)
    (hValid : validateValueForTy? layouts
      (some (resolveTyWithLocalDecls localDecls layouts pTy)) (.scalar wSc) = true) :
    ∃ locals', writePlaceValue locals borrows ⟨p, [.deref]⟩ (.scalar wSc) localDecls layouts =
        .ok locals' ∧
      SlotsRefine SlotBelow slots' locals' := by
  obtain ⟨stp, hStp, hLiveP⟩ := readPlaceState_ok_live hPtr
  have hResT : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty (true && ([] : List ProjectionElem).isEmpty) =
      .ok (entry.targetLocal, entry.targetProjection) := by simpa using hRes
  have hPl := resolvePlace_deref hStp hLiveP hPtr hTy hResT rfl
  simp only [evalDerefPlaceWrite, hPl, List.append_nil] at hW
  have hQ : projectionHasDeref entry.targetProjection = false :=
    resolveSyntheticSubplace_noDeref hWF hRes
  cases hWS : writePlaceState arityOf slots ⟨entry.targetLocal, entry.targetProjection⟩
      (rootTyOf entry.targetLocal) (.scalar wSc) with
  | ub => simp [hWS, liftWrite] at hW
  | unsupported => simp [hWS, liftWrite] at hW
  | ok s =>
    simp only [hWS, liftWrite, Except.ok.injEq] at hW
    subst hW
    obtain ⟨root', hWr, hEq⟩ := writePlaceState_init_root_inv hTgt hQ hWS
    subst hEq
    have hSame := sameScalarLocals_of_slotBelow hRel
    have hWT : evalValueProjWrite locals root entry.targetProjection (.scalar wSc) = .ok root' := by
      rw [← evalValueProjWrite_congr_scalar_locals hSame]; exact hWr
    have hWP := evalValueProjWrite_refines_writeProjectedValue _ _ _ _ _ hWT
    obtain ⟨rootP, hp, hrp⟩ := readPlaceState_below_refines hRel hPtr
    simp only [readProjectedValue] at hrp
    cases hrp
    obtain ⟨rootOld, htOld, hrOld⟩ := readPlaceState_below_refines hRel hOld
    have hTT : locals[entry.targetLocal]? = some (.init root) := by
      rcases SlotsRefine.get?_rel entry.targetLocal hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, hAT⟩
      · simp only [get?_eq_getElem?] at hA; rw [hA] at hTgt; nomatch hTgt
      · simp only [get?_eq_getElem?] at hA hT
        rw [hA] at hTgt
        cases hTgt
        cases t with
        | init w => have hvw : root = w := hAT; subst hvw; exact hT
        | _ => simp [SlotBelow] at hAT
    have hRootOldEq : rootOld = root := by
      simp only [get?_eq_getElem?] at htOld
      rw [hTT] at htOld
      injection htOld with h1
      injection h1 with h2
      exact h2.symm
    subst hRootOldEq
    have hLtT : entry.targetLocal < locals.length := (List.getElem?_eq_some_iff.mp hTT).1
    obtain ⟨d0, ds, hcons⟩ : ∃ d0 ds, localDecls = d0 :: ds := by
      cases h : localDecls with
      | nil => exact absurd h hDecls
      | cons d0 ds => exact ⟨d0, ds, rfl⟩
    have hsplice : spliceScalarSlice? oldSc 0 wSc = some wSc := by
      unfold spliceScalarSlice?
      have hb1 : Bool.and (Nat.ble 1 wSc.sizeBytes)
          (Nat.ble (Nat.add 0 wSc.sizeBytes) oldSc.sizeBytes) = true := by
        simp [Nat.add_eq, Nat.ble_eq, ← hWidth, hPos]
      have hb2 : Bool.and (Nat.beq 0 0) (Nat.beq wSc.sizeBytes oldSc.sizeBytes) = true := by
        simp [hWidth]
      rw [hb1, hb2]
    refine ⟨locals.set entry.targetLocal (.init root'), ?_,
      SlotsRefine.set (a := .init root') (t := .init root') rfl _ hRel⟩
    unfold writePlaceValue
    dsimp only
    rw [hp]
    dsimp only
    rw [hEntry]
    dsimp only
    rcases hPerm with hpe | hpe <;> rw [hpe]
    all_goals
      dsimp only
      rw [hcons]
      dsimp only
      rw [← hcons]
      unfold writeStackThinPtrTypedDeref
      rw [hPTy, hOff, htOld]
      dsimp only [stripTransparentProjections, checkDerefAlign, Nat.beq_refl]
      rw [hAlign, hValid]
      simp only [Bool.and_self]
      rw [hcons]
      dsimp only [stripTransparentProjections]
      rw [← hcons]
      cases htp : entry.targetProjection with
      | nil =>
        rw [htp] at hrOld hWr
        have hRV : root' = .scalar wSc := by
          simp only [evalValueProjWrite, ProjWriteResult.ok.injEq] at hWr
          exact hWr.symm
        subst hRV
        dsimp only [readProjectedForLocal]
        rw [hrOld]
        dsimp only [stripTransparentProjections]
        rw [hsplice]
        simp [set?, hLtT]
      | cons ph pt =>
        rw [htp] at hrOld hWP hNoUnion
        dsimp only [readProjectedForLocal]
        rw [appendProjections_nil_right, hNoUnion]
        dsimp only [stripTransparentProjections]
        rw [hrOld]
        dsimp only [stripTransparentProjections]
        rw [hsplice]
        dsimp only [writeProjectedForLocal]
        rw [hNoUnion]
        dsimp only [stripTransparentProjections]
        rw [hWP]
        simp [set?, hLtT]

/-- **Typed `Deref` assignments refine Trusted's typed `evalStmt`
(`evalStmt_assign_deref_refines_typed`)**: with non-empty `localDecls` and no active function-entry
protector, when Trusted's typed `evalRvalue` evaluates `rv` to `.scalar wSc` without changing the
frame, a successful Anneal write of `.scalar wSc` through `*_p` is matched by Trusted's typed
`evalStmt` stepping the `.assign` with the written frame and deref-write borrow invalidation,
keeping the frames related by `SlotsRefine SlotBelow`. -/
theorem evalStmt_assign_deref_refines_typed
    {arityOf : Ty → VariantIdx → Bool → Option Nat} {rootTyOf : Nat → Ty}
    {cx : SubplaceCtx} (hWF : cx.WF) {slots slots' : List LocalSlotState}
    (s : MachineState) {p : Nat} (rv : Rvalue) (span : String)
    {oldSc wSc : ScalarInt} {root : Value} {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy}
    {entry : BorrowEntry} {localDecls : List LocalDecl} {layouts : LayoutTable} {pTy : Ty}
    (hprot : s.memory.activeProtectors = [])
    (hv : evalRvalue s.frame.locals rv s.memory localDecls layouts =
      .ok (.scalar wSc) s.frame.locals s.memory)
    (hRel : SlotsRefine SlotBelow slots s.frame.locals)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz))
    (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty true =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow s.memory.borrows pv.tag = some entry)
    (hPerm : entry.perm = .active ∨ entry.perm = .reserved)
    (hTgt : slots[entry.targetLocal]? = some (.init root))
    (hOld : readPlaceState slots ⟨entry.targetLocal, entry.targetProjection⟩ = .ok (.scalar oldSc))
    (hW : evalDerefPlaceWrite arityOf rootTyOf cx slots ⟨p, [.deref]⟩ (.scalar wSc) = .ok slots')
    (hDecls : localDecls ≠ [])
    (hPTy : placeTyResolved localDecls layouts ⟨p, [.deref]⟩ = some pTy)
    (hPos : 1 ≤ wSc.sizeBytes)
    (hWidth : wSc.sizeBytes = oldSc.sizeBytes)
    (hOff : pv.offsetBytes = 0)
    (hAlign : checkTargetPlaceAlign localDecls layouts
      (some (resolveTyWithLocalDecls localDecls layouts pTy)) entry pv (some root) = true)
    (hNoUnion : placeTouchesUnion localDecls layouts
      ⟨entry.targetLocal, entry.targetProjection⟩ = false)
    (hValid : validateValueForTy? layouts
      (some (resolveTyWithLocalDecls localDecls layouts pTy)) (.scalar wSc) = true) :
    ∃ locals', evalStmt s ⟨.assign ⟨p, [.deref]⟩ rv, span⟩ localDecls layouts =
        MirStepNode.step (advanceStmt s locals'
          { s.memory with
            borrows := invalidateDerefWriteBorrows s.frame.locals s.memory.borrows
              ⟨p, [.deref]⟩ [] }) ∧
      SlotsRefine SlotBelow slots' locals' := by
  obtain ⟨locals', hWP, hRel'⟩ := evalDerefPlaceWrite_refines_writePlaceValue_typed hWF hRel hPtr
    hTy hRes hEntry hPerm hTgt hOld hW hDecls hPTy hPos hWidth hOff hAlign hNoUnion hValid
  refine ⟨locals', ?_, hRel'⟩
  simp only [evalStmt, hv, evalPlaceWrite, hprot, hWP]

/-! ### Section 4g: Sub-place and array-window `CopyNonOverlapping` (`eval_copy_nonoverlapping`) -/

/-- The `CopyPtr` (address and allocation id) of a synthetic pointer. -/
def SynPtr.toCopyPtr (p : SynPtr) : CopyPtr := ⟨p.addr, p.prov.map Prod.fst⟩

/-- The `DeadLocal` check of `eval_copy_nonoverlapping` on a synthetic pointer: its provenance
names a storage-dead local of the frame. -/
def synthTargetDead (slots : List LocalSlotState) (p : SynPtr) : Bool :=
  match p.prov with
  | some (l + 1, _) =>
    match slots[l]? with
    | some .dead => true
    | _ => false
  | _ => false

/-- Whether a projection tail is structurally valid for `read_slot_at_proj` on an `.uninit` slot
(no `.deref`, and every `.downcast` is immediately followed by `.field`, matching
`rvalue.rs:10426-10444`). -/
def validSubplaceUninitTail : List ProjectionElem → Bool
  | [] => true
  | .deref :: _ => false
  | .downcast _ _ :: .field _ _ :: rest => validSubplaceUninitTail rest
  | .downcast _ _ :: _ => false
  | _ :: rest => validSubplaceUninitTail rest

/-- `read_slot_at_proj` (`rvalue.rs:10416-10506`): projects a `FieldSlot` along `q`, returning
`some .uninit` whenever an `.uninit` slot (at the root or inside a `PartialShell`) is projected
along a valid non-`Deref` tail `q`. -/
def readSlotAtProj (locals : List LocalSlot) : FieldSlot → List ProjectionElem → Option FieldSlot
  | slot, [] => some slot
  | .uninit, q => if validSubplaceUninitTail q then some .uninit else none
  | .init v, q =>
    match evalValueProjRead locals v q with
    | .ok w => some (.init w)
    | _ => none
  | .nested var adt disc fs, .field idx _ :: rest =>
    if shellVariant ⟨var, adt, disc, fs⟩ = 0 then
      match fs[idx]? with
      | some c => readSlotAtProj locals c rest
      | none => none
    else none
  | .nested var adt disc fs, .downcast _ v :: .field idx _ :: rest =>
    if shellVariant ⟨var, adt, disc, fs⟩ = v then
      match fs[idx]? with
      | some c => readSlotAtProj locals c rest
      | none => none
    else none
  | _, _ => none

/-- **`read_subplace_slot`**: the field slot (`Uninit`, `PartialShell`, or `Init`) at a sub-place
of a live local (`rvalue.rs:6788-6803`). -/
def readSubplaceSlot (slots : List LocalSlotState) (l : Nat) (q : List ProjectionElem) :
    Option FieldSlot :=
  match slots[l]? with
  | none => none
  | some .dead => none
  | some st => readSlotAtProj (slotsToTrustedLocals slots) (slotStateToFieldSlot st) q

/-- Whether a sub-place slot is (known to be) uninitialized. -/
def isUninitSlot : Option FieldSlot → Bool
  | some .uninit => true
  | _ => false

@[simp] theorem isUninitSlot_readSlotAtProj_init (locals : List LocalSlot) (v : Value)
    (q : List ProjectionElem) :
    isUninitSlot (readSlotAtProj locals (.init v) q) = false := by
  cases q with
  | nil => rfl
  | cons a as =>
    simp only [readSlotAtProj]
    split <;> rfl

/-- Reading any valid non-`Deref` sub-place tail `q` of an `.uninit` local yields `some .uninit`
(`rvalue.rs:10435-10444`). -/
theorem readSubplaceSlot_uninit_tail {slots : List LocalSlotState} {l : Nat}
    {q : List ProjectionElem} (hU : slots[l]? = some .uninit)
    (hTail : validSubplaceUninitTail q = true) :
    readSubplaceSlot slots l q = some .uninit := by
  cases q with
  | nil => simp [readSubplaceSlot, hU, slotStateToFieldSlot, readSlotAtProj]
  | cons a as => simp [readSubplaceSlot, hU, slotStateToFieldSlot, readSlotAtProj, hTail]

/-- The element `0` of a 1-element array (`ConstantIndex { offset: 0, min_length: 1 }`), which
covers the whole `[T; 1]`. -/
def isUnitElem : ProjectionElem → Bool
  | .constantIndex 0 1 false => true
  | _ => false

/-- Strip trailing 1-element-array element steps (nested `[[T; 1]; 1]` included). -/
def stripUnitElems (q : List ProjectionElem) : List ProjectionElem :=
  (q.reverse.dropWhile isUnitElem).reverse

/-- Wrap `v` in a 1-element array aggregate (`.aggregate 0 [v]`) for each trailing
`ConstantIndex 0 1 false` step of `q` (`rvalue.rs:6833-6856`). -/
def wrapUnitElemsVal (q : List ProjectionElem) (v : Value) : Value :=
  (q.reverse.takeWhile isUnitElem).foldl (fun acc _ => Value.aggregate 0 [acc]) v

/-- Whether a path ends with an array element step (a forward `ConstantIndex`). -/
def endsWithElem (q : List ProjectionElem) : Bool :=
  match q.getLast? with
  | some (.constantIndex _ _ false) => true
  | _ => false

/-- Whether a projection element is an array projection (`Index`, `ConstantIndex`, or `Subslice`,
matching `rvalue.rs:6882-6889`). -/
def isArrayProjElem : ProjectionElem → Bool
  | .index _ => true
  | .constantIndex _ _ _ => true
  | .subslice _ _ _ => true
  | _ => false

/-- Whether a path contains any array projection (`rvalue.rs:6882-6889`). -/
def hasArrayProj (q : List ProjectionElem) : Bool :=
  q.any isArrayProjElem

/-- `write_partial_shell_in_slot` (`rvalue.rs:10600-10726`): writes a `PartialAggregate` shell at
sub-place `proj` of `slot` (materializing uninitialized parent shells via `arityOf`, exploding
initialized parent aggregates via `explodeAggregate`, and normalizing via `deinitShellStep`). -/
def writePartialShellInSlot (arityOf : Ty → VariantIdx → Bool → Option Nat) (tagSurvives : Bool) :
    FieldSlot → Ty → List ProjectionElem → PartialAggregate → Option FieldSlot
  | _, _, [], newShell => some (normalizeShell newShell)
  | .uninit, curTy, .field idx fTy :: rest, newShell =>
    match arityOf curTy 0 false with
    | some n =>
      deinitShellStep tagSurvives ⟨0, false, false, List.replicate n .uninit⟩ none idx
        (fun c => writePartialShellInSlot arityOf tagSurvives c fTy rest newShell)
    | none => none
  | .uninit, curTy, .downcast _ v :: .field idx fTy :: rest, newShell =>
    match arityOf curTy v true with
    | some n =>
      deinitShellStep tagSurvives ⟨v, true, false, List.replicate n .uninit⟩ (some v) idx
        (fun c => writePartialShellInSlot arityOf tagSurvives c fTy rest newShell)
    | none => none
  | .init (.aggregate var vals), _, .field idx fTy :: rest, newShell =>
    deinitShellStep tagSurvives (explodeAggregate var vals) none idx
      (fun c => writePartialShellInSlot arityOf tagSurvives c fTy rest newShell)
  | .init (.aggregate var vals), _, .downcast _ v :: .field idx fTy :: rest, newShell =>
    deinitShellStep tagSurvives (explodeAggregate var vals) (some v) idx
      (fun c => writePartialShellInSlot arityOf tagSurvives c fTy rest newShell)
  | .nested var adt disc fs, _, .field idx fTy :: rest, newShell =>
    deinitShellStep tagSurvives ⟨var, adt, disc, fs⟩ none idx
      (fun c => writePartialShellInSlot arityOf tagSurvives c fTy rest newShell)
  | .nested var adt disc fs, _, .downcast _ v :: .field idx fTy :: rest, newShell =>
    deinitShellStep tagSurvives ⟨var, adt, disc, fs⟩ (some v) idx
      (fun c => writePartialShellInSlot arityOf tagSurvives c fTy rest newShell)
  | _, _, _ :: _, _ => none

/-- **`write_subplace_slot` (`rvalue.rs:6818-6941`)**: stores a copied slot at a sub-place without
guessing:
1. an initialized slot (`.init v`) writes `v` via `writePlaceState`, promoting trailing `[T; 1]` /
   `[[T; 1]; 1]` element steps (`stripUnitElems q`, `wrapUnitElemsVal q v`) when the enclosing
   1-element array is `.uninit`;
2. an uninitialized slot (`.uninit`) strips trailing `[T; 1]` steps (`stripUnitElems q`); if any
   array projection (`Index`, `ConstantIndex`, or `Subslice`) remains (`hasArrayProj`), it is a
   no-op when the destination sub-place is already `.uninit` and fails closed (`none`) otherwise,
   and when no array projection remains it deinitializes `⟨l, stripUnitElems q⟩` via
   `evalDeinitPlace`;
3. a partially initialized shell (`.nested var adt disc fs`) strips trailing `[T; 1]` steps and
   writes the shell at `stripUnitElems q` via `writePartialShellInSlot` (failing closed if
   `stripUnitElems q` contains an array projection). -/
def writeSubplaceSlot (arityOf : Ty → VariantIdx → Bool → Option Nat) (rootTyOf : Nat → Ty)
    (ts : Bool) (slots : List LocalSlotState) (l : Nat) (q : List ProjectionElem) :
    FieldSlot → Option (List LocalSlotState)
  | .init v =>
    let q' := if isUninitSlot (readSubplaceSlot slots l (stripUnitElems q)) then stripUnitElems q else q
    let v' := if isUninitSlot (readSubplaceSlot slots l (stripUnitElems q)) then wrapUnitElemsVal q v else v
    match writePlaceState arityOf slots ⟨l, q'⟩ (rootTyOf l) v' with
    | .ok s => some s
    | _ => none
  | .uninit =>
    if hasArrayProj (stripUnitElems q) then
      if isUninitSlot (readSubplaceSlot slots l (stripUnitElems q)) then some slots
      else none
    else evalDeinitPlace ts slots ⟨l, stripUnitElems q⟩
  | .nested var adt disc fs =>
    match slots[l]? with
    | none => none
    | some .dead => none
    | some st =>
      (writePartialShellInSlot arityOf ts (slotStateToFieldSlot st) (rootTyOf l)
        (stripUnitElems q) ⟨var, adt, disc, fs⟩).map
        (fun s' => slots.set l (fieldSlotToLocalSlotState s'))

/-- The last array-element step of a path: `(array path, start, array length)`. -/
def splitLastElem (q : List ProjectionElem) : Option (List ProjectionElem × Nat × Nat) :=
  match q.getLast? with
  | some (.constantIndex k n false) => some (q.dropLast, k, n)
  | _ => none

open Classical in
/-- **Stateful sub-place `CopyNonOverlapping` (`eval_copy_nonoverlapping`)**, after its operands
are evaluated to the synthetic pointers `src`, `dst` and the count, with endpoint resolution
`resolve` (`resolve_synthetic_subplace` at the element type, the destination in whole-place-write
mode):
1. `copyNonOverlappingChecks` (width, null, alignment, length, wrap, and same-allocation byte
   overlap `rangesDisjoint`), even for an empty copy; `count = 0` is then a no-op;
2. a non-empty (or single-element) copy through the provenance of a storage-dead local is
   `DeadLocal`;
3. `count = 1`: the source sub-place's slot (`Uninit`, `PartialShell`, or `Init`) is stored at the
   destination sub-place (`writeSubplaceSlot`); a zero-sized self-copy only checks readability;
4. `count ≥ 2`: a contiguous window of `count` elements of one array is copied into a window of
   another (`Subslice` read and write; the whole destination array when the window covers it);
   an uninitialized source array leaves an uninitialized destination unchanged and
   deinitializes a fully covered one, failing closed on a partial overwrite of initialized
   elements;
5. a zero-byte copy (`count * elemSize = 0`) between unresolved pointers accesses no memory and
   is a no-op even through storage-dead locals; anything else is unsupported (`none`).
(Classical decidability only decides the zero-sized self-copy test `sp = dp`.) -/
noncomputable def evalCopyNonOverlappingSubplace (arityOf : Ty → VariantIdx → Bool → Option Nat)
    (rootTyOf : Nat → Ty) (ts : Bool) (ptrBits : Nat) (slots : List LocalSlotState)
    (resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem)) (src dst : SynPtr)
    (count elemSize elemAlign : Nat) : Option (List LocalSlotState) :=
  if !copyNonOverlappingChecks ptrBits src.toCopyPtr dst.toCopyPtr count elemSize elemAlign then none
  else if count = 0 then some slots
  else if (count * elemSize != 0 || count == 1) &&
      (synthTargetDead slots src || synthTargetDead slots dst) then none
  else
    match resolve src false, resolve dst true with
    | .ok (sl, sp), .ok (dl, dp) =>
      if count = 1 ∨ count * elemSize = 0 then
        if elemSize = 0 ∧ sl = dl ∧ sp = dp then (readSubplaceSlot slots sl sp).map fun _ => slots
        else
          match readSubplaceSlot slots sl sp with
          | some c => writeSubplaceSlot arityOf rootTyOf ts slots dl dp c
          | none => none
      else
        match splitLastElem sp, splitLastElem dp with
        | some (sArr, s0, sLen), some (dArr, d0, dLen) =>
          if s0 + count ≤ sLen ∧ d0 + count ≤ dLen then
            match readPlaceState slots ⟨sl, sArr ++ [.subslice s0 (s0 + count) false]⟩ with
            | .ok w =>
              let dstPlace : Place :=
                if d0 = 0 ∧ count = dLen then ⟨dl, dArr⟩
                else ⟨dl, dArr ++ [.subslice d0 (d0 + count) false]⟩
              match writePlaceState arityOf slots dstPlace (rootTyOf dl) w with
              | .ok s => some s
              | _ => none
            | _ =>
              if isUninitSlot (readSubplaceSlot slots sl sArr) then
                if isUninitSlot (readSubplaceSlot slots dl dArr) then some slots
                else if d0 = 0 ∧ count = dLen then evalDeinitPlace ts slots ⟨dl, dArr⟩
                else none
              else none
          else none
        | _, _ => none
    | _, _ => if count * elemSize = 0 then some slots else none

/-- `count = 0` is a no-op after the checks. -/
theorem evalCopyNonOverlappingSubplace_zero_count {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {ts : Bool} {ptrBits : Nat} {slots : List LocalSlotState}
    {resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem)} {src dst : SynPtr}
    {elemSize elemAlign : Nat}
    (hChk : copyNonOverlappingChecks ptrBits src.toCopyPtr dst.toCopyPtr 0 elemSize elemAlign = true) :
    evalCopyNonOverlappingSubplace arityOf rootTyOf ts ptrBits slots resolve src dst 0 elemSize
      elemAlign = some slots := by
  simp [evalCopyNonOverlappingSubplace, hChk]

/-- **Self-overlap rejection (`evalCopyNonOverlappingSubplace_overlap_none`)**: a non-empty copy
between overlapping byte ranges of the same allocation — e.g. a sub-place onto itself, or two
overlapping windows of one array — is rejected (`CopyNonOverlappingOverlap`). -/
theorem evalCopyNonOverlappingSubplace_overlap_none {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {ts : Bool} {ptrBits : Nat} {slots : List LocalSlotState}
    {resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem)} {src dst : SynPtr}
    {count elemSize elemAlign : Nat} (hLen : 0 < count * elemSize)
    (hSame : src.prov.map Prod.fst = dst.prov.map Prod.fst)
    (hOverlap : src.addr < dst.addr + count * elemSize ∧ dst.addr < src.addr + count * elemSize) :
    evalCopyNonOverlappingSubplace arityOf rootTyOf ts ptrBits slots resolve src dst count elemSize
      elemAlign = none := by
  have hChkF : copyNonOverlappingChecks ptrBits src.toCopyPtr dst.toCopyPtr count elemSize elemAlign = false := by
    cases hC : copyNonOverlappingChecks ptrBits src.toCopyPtr dst.toCopyPtr count elemSize elemAlign with
    | false => rfl
    | true =>
      have hDisj := copyNonOverlappingChecks_disjoint hC hLen (by simp [SynPtr.toCopyPtr, hSame])
      have := (copyOverlap_iff_not_rangesDisjoint src.addr dst.addr (count * elemSize)).mp hOverlap
      simp only [SynPtr.toCopyPtr] at hDisj
      rw [hDisj] at this
      nomatch this
  simp [evalCopyNonOverlappingSubplace, hChkF]

/-- **Zero-byte bulk copies never fault (`evalCopyNonOverlappingSubplace_zst_bulk_noop`)**: a copy of
`count ≥ 2` zero-sized elements between unresolved pointers is a no-op even through the
provenance of storage-dead locals (no memory is accessed). -/
theorem evalCopyNonOverlappingSubplace_zst_bulk_noop {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {ts : Bool} {ptrBits : Nat} {slots : List LocalSlotState}
    {resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem)} {src dst : SynPtr}
    {count elemAlign : Nat}
    (hChk : copyNonOverlappingChecks ptrBits src.toCopyPtr dst.toCopyPtr count 0 elemAlign = true)
    (hCount : 2 ≤ count) {e : DerefErr} (hUnres : resolve src false = .error e) :
    evalCopyNonOverlappingSubplace arityOf rootTyOf ts ptrBits slots resolve src dst count 0
      elemAlign = some slots := by
  have h0 : count ≠ 0 := by omega
  have h1 : (count == 1) = false := by simp; omega
  simp [evalCopyNonOverlappingSubplace, hChk, h0, h1, hUnres]

/-- Dead provenance faults (`DeadLocal`) for every non-empty or single-element copy. -/
theorem evalCopyNonOverlappingSubplace_dead_none {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {ts : Bool} {ptrBits : Nat} {slots : List LocalSlotState}
    {resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem)} {src dst : SynPtr}
    {count elemSize elemAlign : Nat} (hCount : count ≠ 0) (hLen : count * elemSize ≠ 0 ∨ count = 1)
    (hDead : synthTargetDead slots src = true ∨ synthTargetDead slots dst = true) :
    evalCopyNonOverlappingSubplace arityOf rootTyOf ts ptrBits slots resolve src dst count elemSize
      elemAlign = none := by
  unfold evalCopyNonOverlappingSubplace
  cases hChk : copyNonOverlappingChecks ptrBits src.toCopyPtr dst.toCopyPtr count elemSize elemAlign with
  | false => rfl
  | true =>
    have hGuard : ((count * elemSize != 0 || count == 1) &&
        (synthTargetDead slots src || synthTargetDead slots dst)) = true := by
      rcases hLen with h | h <;> rcases hDead with hd | hd <;> simp [h, hd]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hCount, hGuard]

/-- **Read-After-Copy (`evalCopyNonOverlappingSubplace_read_after_copy`)**: after a single-element
sub-place copy of an initialized source value `v` into a sub-place of an initialized local, the
destination sub-place reads `v`. -/
theorem evalCopyNonOverlappingSubplace_read_after_copy {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {ts : Bool} {ptrBits : Nat} {slots slots' : List LocalSlotState}
    {resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem)} {src dst : SynPtr}
    {elemSize elemAlign sl dl : Nat} {sp dp : List ProjectionElem} {v droot : Value}
    (hSrcR : resolve src false = .ok (sl, sp)) (hDstR : resolve dst true = .ok (dl, dp))
    (hDistinct : elemSize ≠ 0 ∨ sl ≠ dl ∨ sp ≠ dp)
    (hSrc : readSubplaceSlot slots sl sp = some (.init v))
    (hDst : slots[dl]? = some (.init droot)) (hDp : projectionHasDeref dp = false)
    (h : evalCopyNonOverlappingSubplace arityOf rootTyOf ts ptrBits slots resolve src dst 1 elemSize
      elemAlign = some slots') :
    readPlaceState slots' ⟨dl, dp⟩ = .ok v ∧ ∀ j, j ≠ dl → slots'[j]? = slots[j]? := by
  unfold evalCopyNonOverlappingSubplace at h
  split at h
  · nomatch h
  · split at h
    · omega
    · split at h
      · nomatch h
      · rw [hSrcR, hDstR] at h
        simp only [true_or, ↓reduceIte] at h
        have hNS : ¬ (elemSize = 0 ∧ sl = dl ∧ sp = dp) := by
          rintro ⟨h1, h2, h3⟩
          rcases hDistinct with h' | h' | h'
          · exact h' h1
          · exact h' h2
          · exact h' h3
        have hUn : isUninitSlot (readSubplaceSlot slots dl (stripUnitElems dp)) = false := by
          simp [readSubplaceSlot, hDst, slotStateToFieldSlot]
        simp only [hNS, ↓reduceIte, hSrc, writeSubplaceSlot, hUn, Bool.false_eq_true] at h
        cases hWS : writePlaceState arityOf slots ⟨dl, dp⟩ (rootTyOf dl) v with
        | ok s =>
          rw [hWS] at h
          simp only [Option.some.injEq] at h
          subst h
          refine ⟨writePlaceState_put_get_init hDst hDp hWS, fun j hj => ?_⟩
          obtain ⟨x, hx⟩ := writePlaceState_frame hWS
          rw [hx]
          exact List.getElem?_set_ne (Ne.symm hj)
        | ub => rw [hWS] at h; nomatch h
        | unsupported => rw [hWS] at h; nomatch h

/-- `writeSubplaceSlot` only changes the destination local. -/
theorem writeSubplaceSlot_frame {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {ts : Bool} {slots slots' : List LocalSlotState} {l : Nat}
    {q : List ProjectionElem} {c : FieldSlot}
    (h : writeSubplaceSlot arityOf rootTyOf ts slots l q c = some slots') :
    ∀ j, j ≠ l → slots'[j]? = slots[j]? := by
  intro j hj
  cases c with
  | init v =>
    simp only [writeSubplaceSlot] at h
    split at h
    · rename_i s hW
      obtain ⟨x, hx⟩ := writePlaceState_frame hW
      simp only [Option.some.injEq] at h
      subst h
      rw [hx]
      exact List.getElem?_set_ne (Ne.symm hj)
    · nomatch h
  | uninit =>
    simp only [writeSubplaceSlot] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        rfl
      · nomatch h
    · obtain ⟨_, _, _, _, _, hs⟩ := evalDeinitPlace_eq_some h
      subst hs
      exact List.getElem?_set_ne (Ne.symm hj)
  | nested var adt disc fs =>
    simp only [writeSubplaceSlot] at h
    split at h
    · nomatch h
    · nomatch h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      exact List.getElem?_set_ne (Ne.symm hj)

/-- **Disjoint-Frame (`evalCopyNonOverlappingSubplace_frame`)**: a successful sub-place or
array-window copy changes only the destination's local (whatever the source slot, the copied
count, or the destination's shape); every other local of the frame — in particular the source's
local when it is distinct — is untouched. -/
theorem evalCopyNonOverlappingSubplace_frame {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {ts : Bool} {ptrBits : Nat} {slots slots' : List LocalSlotState}
    {resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem)} {src dst : SynPtr}
    {count elemSize elemAlign dl : Nat} {dp : List ProjectionElem}
    (hDstR : resolve dst true = .ok (dl, dp))
    (h : evalCopyNonOverlappingSubplace arityOf rootTyOf ts ptrBits slots resolve src dst count
      elemSize elemAlign = some slots') :
    ∀ j, j ≠ dl → slots'[j]? = slots[j]? := by
  intro j hj
  have hSet : ∀ x, (slots.set dl x)[j]? = slots[j]? := fun _ => List.getElem?_set_ne (Ne.symm hj)
  unfold evalCopyNonOverlappingSubplace at h
  rw [hDstR] at h
  split at h
  · nomatch h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  split at h
  · nomatch h
  cases hS : resolve src false with
  | error e =>
    rw [hS] at h
    simp only at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
    · nomatch h
  | ok sv =>
    obtain ⟨sl, sp⟩ := sv
    rw [hS] at h
    simp only at h
    split at h
    · split at h
      · cases hr : readSubplaceSlot slots sl sp with
        | none => rw [hr] at h; nomatch h
        | some _ =>
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          rfl
      · split at h
        · exact writeSubplaceSlot_frame h j hj
        · nomatch h
    · split at h
      · split at h
        · split at h
          · split at h
            · rename_i s hW
              obtain ⟨x, hx⟩ := writePlaceState_frame hW
              simp only [Option.some.injEq] at h
              subst h
              rw [hx]
              split <;> exact hSet x
            · nomatch h
          · split at h
            · split at h
              · simp only [Option.some.injEq] at h
                subst h
                rfl
              · split at h
                · obtain ⟨_, _, _, _, _, hs⟩ := evalDeinitPlace_eq_some h
                  subst hs
                  exact hSet _
                · nomatch h
            · nomatch h
        · nomatch h
      · nomatch h

/-- **Uninitialized copies into a `[T; 1]` deinitialize the array
(`writeSubplaceSlot_uninit_unit_array`)**: storing an uninitialized slot at element `0` of a
1-element array deinitializes the whole array place; at an element of a longer initialized array
(no per-element state) it fails closed. -/
theorem writeSubplaceSlot_uninit_unit_array {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {ts : Bool} {slots : List LocalSlotState} {l : Nat}
    {arr : List ProjectionElem} (hArr : hasArrayProj (stripUnitElems arr) = false)
    (hArr' : stripUnitElems (arr ++ [.constantIndex 0 1 false]) = stripUnitElems arr) :
    writeSubplaceSlot arityOf rootTyOf ts slots l (arr ++ [.constantIndex 0 1 false]) .uninit =
      evalDeinitPlace ts slots ⟨l, stripUnitElems arr⟩ := by
  simp [writeSubplaceSlot, hArr', hArr]

/-- Stripping a trailing `[T; 1]` element step. -/
theorem stripUnitElems_append_unit (arr : List ProjectionElem) :
    stripUnitElems (arr ++ [.constantIndex 0 1 false]) = stripUnitElems arr := by
  simp [stripUnitElems, isUnitElem, List.reverse_append]

/-- **Initialized copies into an `.uninit` `[T; 1]` initialize the whole 1-element array
(`writeSubplaceSlot_init_unit_array`, `rvalue.rs:6833-6856`)**: when local `l` is `.uninit` (or the
1-element array sub-place `arr` is `.uninit` with no trailing `isUnitElem`), storing `.init v` at
`arr ++ [.constantIndex 0 1 false]` writes `.aggregate 0 [v]` at `⟨l, arr⟩`. -/
theorem writeSubplaceSlot_init_unit_array {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {ts : Bool} {slots : List LocalSlotState} {l : Nat} {v : Value}
    (hU : slots[l]? = some .uninit) :
    writeSubplaceSlot arityOf rootTyOf ts slots l [.constantIndex 0 1 false] (.init v) =
      some (slots.set l (.init (.aggregate 0 [v]))) := by
  simp [writeSubplaceSlot, stripUnitElems, wrapUnitElemsVal, isUnitElem, readSubplaceSlot, hU,
    slotStateToFieldSlot, readSlotAtProj, isUninitSlot, writePlaceState,
    fieldSlotToLocalSlotState]

/-- An element or subslice write of an uninitialized slot into an initialized multi-element array
fails closed (arrays have no per-element initialization state). -/
theorem writeSubplaceSlot_uninit_elem_init_array_none
    {arityOf : Ty → VariantIdx → Bool → Option Nat} {rootTyOf : Nat → Ty} {ts : Bool}
    {slots : List LocalSlotState} {l : Nat} {q : List ProjectionElem}
    (hElem : hasArrayProj (stripUnitElems q) = true)
    (hNotUninit : isUninitSlot (readSubplaceSlot slots l (stripUnitElems q)) = false) :
    writeSubplaceSlot arityOf rootTyOf ts slots l q .uninit = none := by
  simp [writeSubplaceSlot, hElem, hNotUninit]

/-- **Episode 1 B4 Regression (`writeSubplaceSlot_uninit_subslice_init_array_none`)**: copying an
uninitialized slot into a `Subslice` window (e.g., `arr[0..1]`) of an initialized array `arr` fails
closed (`none`) instead of deinitializing `arr`. -/
theorem writeSubplaceSlot_uninit_subslice_init_array_none
    {arityOf : Ty → VariantIdx → Bool → Option Nat} {rootTyOf : Nat → Ty} {ts : Bool}
    {slots : List LocalSlotState} {l from_ to_ : Nat} {fromEnd : Bool} {droot : Value}
    (hDst : slots[l]? = some (.init droot)) :
    writeSubplaceSlot arityOf rootTyOf ts slots l [.subslice from_ to_ fromEnd] .uninit = none := by
  have hUn : isUninitSlot (readSubplaceSlot slots l [.subslice from_ to_ fromEnd]) = false := by
    simp [readSubplaceSlot, hDst, slotStateToFieldSlot]
  simp [writeSubplaceSlot, stripUnitElems, isUnitElem, hasArrayProj, isArrayProjElem, hUn]

/-- **Projected `PartialShell` sub-place copy (`writeSubplaceSlot_nested_field_ok`)**: copying a
`PartialShell` (`FieldSlot.nested`) into field `0` of an initialized 2-field aggregate explodes the
outer aggregate into a parent `PartialShell` whose field `0` holds the normalized inner shell and
whose sibling field `1` preserves `sib`. -/
theorem writeSubplaceSlot_nested_field_ok
    {arityOf : Ty → VariantIdx → Bool → Option Nat} {rootTyOf : Nat → Ty} {ts : Bool}
    {slots : List LocalSlotState} {l : Nat} {fTy : Ty} {old0 sib v0 : Value}
    (hDst : slots[l]? = some (.init (.aggregate 0 [old0, sib]))) :
    writeSubplaceSlot arityOf rootTyOf ts slots l [.field 0 fTy]
        (.nested 0 false false [.init v0, .uninit]) =
      some (slots.set l (.partialShell
        ⟨0, true, true, [.nested 0 false false [.init v0, .uninit], .init sib]⟩)) := by
  simp [writeSubplaceSlot, hDst, slotStateToFieldSlot, stripUnitElems, isUnitElem,
    writePartialShellInSlot, explodeAggregate, deinitShellStep, shellVariant, normalizeShell,
    PartialAggregate.tryIntoValue?, PartialAggregate.toFieldSlot, tryFieldsIntoValues?,
    allFieldsUninit, fieldSlotToLocalSlotState]

/-- **Array-Window Read-After-Copy (`evalCopyNonOverlappingSubplace_window_read_after_copy`)**:
copying a contiguous window of `count ≥ 2` elements from an initialized source array sub-place
`sArr` at `s0` into an initialized destination array sub-place `dArr` at `d0` writes the `Subslice`
window value `w` so reading `⟨dl, dArr ++ [.subslice d0 (d0 + count) false]⟩` (when proper) or
`⟨dl, dArr⟩` (when `d0 = 0 ∧ count = dLen`) returns `.ok w`, leaving every other local untouched. -/
theorem evalCopyNonOverlappingSubplace_window_read_after_copy
    {arityOf : Ty → VariantIdx → Bool → Option Nat} {rootTyOf : Nat → Ty} {ts : Bool}
    {ptrBits : Nat} {slots slots' : List LocalSlotState}
    {resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem)} {src dst : SynPtr}
    {count elemSize elemAlign sl dl s0 sLen d0 dLen : Nat} {sArr dArr : List ProjectionElem}
    {w droot : Value}
    (hCount : 2 ≤ count) (hElemSz : 0 < elemSize)
    (hSrcR : resolve src false = .ok (sl, sArr ++ [.constantIndex s0 sLen false]))
    (hDstR : resolve dst true = .ok (dl, dArr ++ [.constantIndex d0 dLen false]))
    (hSrcRead : readPlaceState slots ⟨sl, sArr ++ [.subslice s0 (s0 + count) false]⟩ = .ok w)
    (hDst : slots[dl]? = some (.init droot))
    (hDArr : projectionHasDeref dArr = false)
    (h : evalCopyNonOverlappingSubplace arityOf rootTyOf ts ptrBits slots resolve src dst count
      elemSize elemAlign = some slots') :
    let dstPlace : Place :=
      if d0 = 0 ∧ count = dLen then ⟨dl, dArr⟩
      else ⟨dl, dArr ++ [.subslice d0 (d0 + count) false]⟩
    readPlaceState slots' dstPlace = .ok w ∧ ∀ j, j ≠ dl → slots'[j]? = slots[j]? := by
  have hFrame := evalCopyNonOverlappingSubplace_frame hDstR h
  refine ⟨?_, hFrame⟩
  unfold evalCopyNonOverlappingSubplace at h
  split at h
  · nomatch h
  split at h
  · omega
  split at h
  · nomatch h
  rw [hSrcR, hDstR] at h
  have hNot1 : ¬ (count = 1 ∨ count * elemSize = 0) := by
    rintro (rfl | hMul)
    · omega
    · exact absurd hMul (Nat.ne_of_gt (Nat.mul_pos (by omega) hElemSz))
  have hSplitS : splitLastElem (sArr ++ [.constantIndex s0 sLen false]) = some (sArr, s0, sLen) := by
    simp [splitLastElem]
  have hSplitD : splitLastElem (dArr ++ [.constantIndex d0 dLen false]) = some (dArr, d0, dLen) := by
    simp [splitLastElem]
  simp only [hNot1, ↓reduceIte, hSplitS, hSplitD] at h
  split at h
  · rw [hSrcRead] at h
    simp only at h
    by_cases hWhole : d0 = 0 ∧ count = dLen
    · simp only [hWhole, and_self, ↓reduceIte] at h ⊢
      cases hWS : writePlaceState arityOf slots ⟨dl, dArr⟩ (rootTyOf dl) w with
      | ok s =>
        rw [hWS] at h
        simp only [Option.some.injEq] at h
        subst h
        exact writePlaceState_put_get_init hDst hDArr hWS
      | ub => rw [hWS] at h; nomatch h
      | unsupported => rw [hWS] at h; nomatch h
    · simp only [hWhole, ↓reduceIte] at h ⊢
      have hDp : projectionHasDeref (dArr ++ [.subslice d0 (d0 + count) false]) = false := by
        rw [projectionHasDeref_append, hDArr]; rfl
      cases hWS : writePlaceState arityOf slots
          ⟨dl, dArr ++ [.subslice d0 (d0 + count) false]⟩ (rootTyOf dl) w with
      | ok s =>
        rw [hWS] at h
        simp only [Option.some.injEq] at h
        subst h
        exact writePlaceState_put_get_init hDst hDp hWS
      | ub => rw [hWS] at h; nomatch h
      | unsupported => rw [hWS] at h; nomatch h
  · nomatch h

/-- **Single-element sub-place copies refine Trusted's `evalCopySingleDirect`
(`evalCopyNonOverlappingSubplace_refines`)**: on below-related frames, when Anneal copies an
initialized source sub-place `(sl, sp)` (value `v`, from an initialized local) into a sub-place
`(dl, dp ≠ [])` of an initialized local of another local, and Trusted's borrow entries for the two
pointers name exactly these sub-places (distinct tags, no union along `dp`, a value valid for the
destination type), Trusted's `evalCopySingleDirect` steps with the written frame and the
updated frames stay related by `SlotsRefine SlotBelow`. -/
theorem evalCopyNonOverlappingSubplace_refines {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {ts : Bool} {ptrBits : Nat} {slots slots' : List LocalSlotState}
    {locals₃ : List LocalSlot}
    {resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem)} {src dst : SynPtr}
    {elemSize elemAlign sl dl : Nat} {sp : List ProjectionElem} {dh : ProjectionElem}
    {dt : List ProjectionElem} {v droot : Value}
    (hRel : SlotsRefine SlotBelow slots locals₃)
    (hSrcR : resolve src false = .ok (sl, sp)) (hDstR : resolve dst true = .ok (dl, dh :: dt))
    (hNe : sl ≠ dl) (hSrcRead : readPlaceState slots ⟨sl, sp⟩ = .ok v)
    (hSrcSlot : readSubplaceSlot slots sl sp = some (.init v))
    (hDstRoot : slots[dl]? = some (.init droot)) (hDh : dh ≠ .deref)
    (hDt : projectionHasDeref dt = false)
    (h : evalCopyNonOverlappingSubplace arityOf rootTyOf ts ptrBits slots resolve src dst 1
      elemSize elemAlign = some slots')
    (s : MachineState) (srcOp dstOp : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (hTagNe : srcPtr.tag ≠ dstPtr.tag)
    (hSrcEntry : srcEntry.targetLocal = sl ∧ srcEntry.targetProjection = sp)
    (hDstEntry : dstEntry.targetLocal = dl ∧ dstEntry.targetProjection = dh :: dt)
    (hPointee : operandPointeeTy localDecls layouts srcOp = none ∨
      ∃ srcPt dstPt, operandPointeeTy localDecls layouts srcOp = some srcPt ∧
        operandPointeeTy localDecls layouts dstOp = some dstPt ∧
        sameRigidTyShape srcPt.kind dstPt.kind = true)
    (hNoUnion : placeTouchesUnion localDecls layouts ⟨dl, dh :: dt⟩ = false)
    (hValid : validateValueForTy? layouts (placeTy localDecls layouts ⟨dl, dh :: dt⟩) v = true) :
    ∃ locals₄, evalCopySingleDirect s srcOp dstOp localDecls layouts srcPtr dstPtr srcEntry dstEntry
        locals₃ = .step (advanceStmt s locals₄
          { s.memory with
            borrows := invalidateConflictingBorrows s.memory.borrows dl (some dstPtr.tag) }) ∧
      SlotsRefine SlotBelow slots' locals₄ := by
  have hDp : projectionHasDeref (dh :: dt) = false := by
    cases dh with
    | deref => exact absurd rfl hDh
    | _ => simpa [projectionHasDeref] using hDt
  obtain ⟨hRead', hFrame⟩ := evalCopyNonOverlappingSubplace_read_after_copy hSrcR hDstR
    (Or.inr (Or.inl hNe)) hSrcSlot hDstRoot hDp h
  -- the Anneal step is an `evalValueProjWrite` of `v` into the destination root
  unfold evalCopyNonOverlappingSubplace at h
  split at h
  · nomatch h
  · split at h
    · omega
    · split at h
      · nomatch h
      · rw [hSrcR, hDstR] at h
        simp only [true_or, ↓reduceIte] at h
        have hNS : ¬ (elemSize = 0 ∧ sl = dl ∧ sp = dh :: dt) := fun hc => hNe hc.2.1
        have hUn : isUninitSlot (readSubplaceSlot slots dl (stripUnitElems (dh :: dt))) = false := by
          simp [readSubplaceSlot, hDstRoot, slotStateToFieldSlot]
        simp only [hNS, ↓reduceIte, hSrcSlot, writeSubplaceSlot, hUn, Bool.false_eq_true] at h
        cases hWS : writePlaceState arityOf slots ⟨dl, dh :: dt⟩ (rootTyOf dl) v with
        | ub => rw [hWS] at h; nomatch h
        | unsupported => rw [hWS] at h; nomatch h
        | ok s' =>
          rw [hWS] at h
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨droot', hW, hEq⟩ := writePlaceState_init_root_inv hDstRoot hDp hWS
          subst hEq
          have hSame := sameScalarLocals_of_slotBelow hRel
          -- Trusted's view of the source and destination roots
          obtain ⟨tsroot, hTS, hTSR⟩ := readPlaceState_below_refines hRel hSrcRead
          have hTD : locals₃[dl]? = some (.init droot) := by
            rcases SlotsRefine.get?_rel dl hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, hAT⟩
            · simp only [get?_eq_getElem?] at hA; rw [hA] at hDstRoot; nomatch hDstRoot
            · simp only [get?_eq_getElem?] at hA hT
              rw [hA] at hDstRoot
              cases hDstRoot
              cases t with
              | init w => have hvw : droot = w := hAT; subst hvw; exact hT
              | _ => simp [SlotBelow] at hAT
          have hLtD : dl < locals₃.length := (List.getElem?_eq_some_iff.mp hTD).1
          have hWT : evalValueProjWrite locals₃ droot (dh :: dt) v = .ok droot' := by
            rw [← evalValueProjWrite_congr_scalar_locals hSame]; exact hW
          have hWP := evalValueProjWrite_refines_writeProjectedValue _ _ _ _ _ hWT
          have hSet : set? locals₃ dl (.init droot') = some (locals₃.set dl (.init droot')) :=
            set?_eq_some_iff.mpr ⟨hLtD, rfl⟩
          have hWrite : writePlaceValue locals₃ s.memory.borrows ⟨dl, dh :: dt⟩ v localDecls layouts =
              .ok (locals₃.set dl (.init droot')) :=
            writePlaceValue_proj_of_noUnion locals₃ s.memory.borrows dl dh dt v droot droot' _
              localDecls layouts hDh hNoUnion hValid (by simp [get?_eq_getElem?, hTD]) hWP hSet
          refine ⟨locals₃.set dl (.init droot'), ?_,
            SlotsRefine.set (a := .init droot') (t := .init droot') rfl dl hRel⟩
          unfold evalCopySingleDirect
          rcases beq_cases srcPtr.tag dstPtr.tag with ⟨_, hEqTag⟩ | ⟨hBTag, _⟩
          · exact absurd hEqTag hTagNe
          · rcases beq_cases sl dl with ⟨_, hEqLoc⟩ | ⟨hBLoc, _⟩
            · exact absurd hEqLoc hNe
            · simp only [get?_eq_getElem?] at hTS
              rcases hPointee with hUntyped | ⟨srcPt, dstPt, hSPt, hDPt, hShape⟩
              · simp only [hSrcEntry.1, hSrcEntry.2, hDstEntry.1, hDstEntry.2, hBTag, hBLoc,
                  get?_eq_getElem?, hTS, hTSR, hUntyped, hWrite]
              · simp only [hSrcEntry.1, hSrcEntry.2, hDstEntry.1, hDstEntry.2, hBTag, hBLoc,
                  get?_eq_getElem?, hTS, hTSR, hSPt, hDPt, hShape, hWrite]

/-- **Trusted's `evalStmt` reaches `evalCopySingleDirect` (`evalStmt_copyNonOverlapping_singleDirect`)**:
for a `copy_nonoverlapping(src, dst, 1)` whose operands evaluate (without changing the frame) to
pointers with usable borrow entries (a readable source, a writable destination) at offset `0`
outside unions, Trusted's statement step is exactly its single-element direct copy. -/
theorem evalStmt_copyNonOverlapping_singleDirect (s : MachineState) (srcOp dstOp countOp : Operand)
    (span : String) (localDecls : List LocalDecl) (layouts : LayoutTable)
    {srcPtr dstPtr : ProvenancePtr} {srcSz dstSz : Nat} {countSc : ScalarInt}
    {srcEntry dstEntry : BorrowEntry}
    (hSrc : evalOperand s.frame.locals srcOp s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls = .ok (.ptr srcPtr srcSz) s.frame.locals)
    (hDst : evalOperand s.frame.locals dstOp s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls = .ok (.ptr dstPtr dstSz) s.frame.locals)
    (hCnt : evalOperand s.frame.locals countOp s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls = .ok (.scalar countSc) s.frame.locals)
    (hOne : countSc.bits = 1)
    (hSrcE : lookupBorrow s.memory.borrows srcPtr.tag = some srcEntry)
    (hDstE : lookupBorrow s.memory.borrows dstPtr.tag = some dstEntry)
    (hSrcP : srcEntry.perm ≠ .disabled) (hDstP : dstEntry.perm = .active ∨ dstEntry.perm = .reserved)
    (hSrcU : resolveUnionEndpoint? localDecls layouts s.frame.locals srcEntry = none)
    (hDstU : resolveUnionEndpoint? localDecls layouts s.frame.locals dstEntry = none)
    (hSrcOff : srcPtr.offsetBytes = 0) (hDstOff : dstPtr.offsetBytes = 0) :
    evalStmt s ⟨.intrinsic (.copyNonOverlapping srcOp dstOp countOp), span⟩ localDecls layouts =
      evalCopySingleDirect s srcOp dstOp localDecls layouts srcPtr dstPtr srcEntry dstEntry
        s.frame.locals := by
  have hPermOk : evalCopyNonOverlappingWithCount s srcOp dstOp localDecls layouts
      (.ptr srcPtr srcSz) (.ptr dstPtr dstSz) 1 s.frame.locals =
      evalCopyNonOverlappingPermOk s srcOp dstOp localDecls layouts srcPtr dstPtr srcEntry dstEntry 1
        s.frame.locals := by
    unfold evalCopyNonOverlappingWithCount
    simp only [hSrcE, hDstE]
    cases hs : srcEntry.perm with
    | disabled => exact absurd hs hSrcP
    | _ => rcases hDstP with hd | hd <;> simp [hd]
  simp only [evalStmt, evalCopyNonOverlapping, hSrc, hDst, hCnt, hOne, hPermOk]
  unfold evalCopyNonOverlappingPermOk
  simp only [hSrcU, hDstU, hSrcOff, hDstOff, Nat.beq_refl, Bool.and_self]

/-- **Sub-place `CopyNonOverlapping` refines Trusted's `evalStmt`
(`evalStmt_copyNonOverlapping_subplace_refines`)**: on below-related frames, a successful Anneal
single-element sub-place copy of an initialized source value into a sub-place of another
initialized local is matched by Trusted's `evalStmt` on `copy_nonoverlapping(src, dst, 1)` — whose
pointer operands carry borrow entries naming exactly the two resolved sub-places — stepping with
the written frame, and the frames stay related by `SlotsRefine SlotBelow`. -/
theorem evalStmt_copyNonOverlapping_subplace_refines {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {rootTyOf : Nat → Ty} {ts : Bool} {ptrBits : Nat} {slots slots' : List LocalSlotState}
    {resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem)} {src dst : SynPtr}
    {elemSize elemAlign sl dl : Nat} {sp : List ProjectionElem} {dh : ProjectionElem}
    {dt : List ProjectionElem} {v droot : Value} (s : MachineState)
    (hRel : SlotsRefine SlotBelow slots s.frame.locals)
    (hSrcR : resolve src false = .ok (sl, sp)) (hDstR : resolve dst true = .ok (dl, dh :: dt))
    (hNe : sl ≠ dl) (hSrcRead : readPlaceState slots ⟨sl, sp⟩ = .ok v)
    (hSrcSlot : readSubplaceSlot slots sl sp = some (.init v))
    (hDstRoot : slots[dl]? = some (.init droot)) (hDh : dh ≠ .deref)
    (hDt : projectionHasDeref dt = false)
    (h : evalCopyNonOverlappingSubplace arityOf rootTyOf ts ptrBits slots resolve src dst 1
      elemSize elemAlign = some slots')
    (srcOp dstOp countOp : Operand) (span : String) (localDecls : List LocalDecl)
    (layouts : LayoutTable) {srcPtr dstPtr : ProvenancePtr} {srcSz dstSz : Nat}
    {countSc : ScalarInt} {srcEntry dstEntry : BorrowEntry}
    (hSrcOp : evalOperand s.frame.locals srcOp s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls = .ok (.ptr srcPtr srcSz) s.frame.locals)
    (hDstOp : evalOperand s.frame.locals dstOp s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls = .ok (.ptr dstPtr dstSz) s.frame.locals)
    (hCnt : evalOperand s.frame.locals countOp s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls = .ok (.scalar countSc) s.frame.locals)
    (hOne : countSc.bits = 1)
    (hSrcE : lookupBorrow s.memory.borrows srcPtr.tag = some srcEntry)
    (hDstE : lookupBorrow s.memory.borrows dstPtr.tag = some dstEntry)
    (hSrcP : srcEntry.perm ≠ .disabled) (hDstP : dstEntry.perm = .active ∨ dstEntry.perm = .reserved)
    (hSrcU : resolveUnionEndpoint? localDecls layouts s.frame.locals srcEntry = none)
    (hDstU : resolveUnionEndpoint? localDecls layouts s.frame.locals dstEntry = none)
    (hSrcOff : srcPtr.offsetBytes = 0) (hDstOff : dstPtr.offsetBytes = 0)
    (hTagNe : srcPtr.tag ≠ dstPtr.tag)
    (hSrcEntry : srcEntry.targetLocal = sl ∧ srcEntry.targetProjection = sp)
    (hDstEntry : dstEntry.targetLocal = dl ∧ dstEntry.targetProjection = dh :: dt)
    (hPointee : operandPointeeTy localDecls layouts srcOp = none ∨
      ∃ srcPt dstPt, operandPointeeTy localDecls layouts srcOp = some srcPt ∧
        operandPointeeTy localDecls layouts dstOp = some dstPt ∧
        sameRigidTyShape srcPt.kind dstPt.kind = true)
    (hNoUnion : placeTouchesUnion localDecls layouts ⟨dl, dh :: dt⟩ = false)
    (hValid : validateValueForTy? layouts (placeTy localDecls layouts ⟨dl, dh :: dt⟩) v = true) :
    ∃ locals₄, evalStmt s ⟨.intrinsic (.copyNonOverlapping srcOp dstOp countOp), span⟩
        localDecls layouts = .step (advanceStmt s locals₄
          { s.memory with
            borrows := invalidateConflictingBorrows s.memory.borrows dl (some dstPtr.tag) }) ∧
      SlotsRefine SlotBelow slots' locals₄ := by
  rw [evalStmt_copyNonOverlapping_singleDirect s srcOp dstOp countOp span localDecls layouts hSrcOp
    hDstOp hCnt hOne hSrcE hDstE hSrcP hDstP hSrcU hDstU hSrcOff hDstOff]
  exact evalCopyNonOverlappingSubplace_refines hRel hSrcR hDstR hNe hSrcRead hSrcSlot hDstRoot hDh
    hDt h s srcOp dstOp localDecls layouts srcPtr dstPtr srcEntry dstEntry hTagNe hSrcEntry hDstEntry
    hPointee hNoUnion hValid

theorem appendValues_eq_append : ∀ (xs ys : List Value), appendValues xs ys = xs ++ ys
  | [], _ => rfl
  | x :: xs, ys => by simp [appendValues, appendValues_eq_append xs ys]

theorem spliceValues_eq_take_append_drop (srcSlice dstElems : List Value) (d0 : Nat) :
    spliceValues srcSlice d0 dstElems =
      dstElems.take d0 ++ (srcSlice ++ dstElems.drop (d0 + srcSlice.length)) := by
  simp [spliceValues, appendValues_eq_append, takeValues_eq_take, dropValues_eq_drop,
    length_eq_list_length]

/-- **Array-window (`count ≥ 2`) `CopyNonOverlapping` refines Trusted's `evalCopyNonOverlappingPermOk`
(`evalCopyNonOverlappingSubplace_window_refines`)**: on below-related frames, when Anneal copies a
contiguous window of `count ≥ 2` elements (`elemSize > 0`) from an initialized array local `sl` at
index `s0` into a distinct initialized array local `dl` at index `d0` (`s0 + count ≤ sLen`,
`d0 + count ≤ dLen`), and Trusted's borrow entries for `srcPtr` and `dstPtr` target `(sl, [])` at
`offsetBytes = s0` and `(dl, [])` at `offsetBytes = d0` (with distinct tags, outside unions, on a
non-ADT destination local), Trusted's `evalCopyNonOverlappingPermOk` steps with the exact same
spliced array `spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems` and the
updated frames stay related by `SlotsRefine SlotBelow`. -/
theorem evalCopyNonOverlappingSubplace_window_refines
    {arityOf : Ty → VariantIdx → Bool → Option Nat} {rootTyOf : Nat → Ty} {ts : Bool}
    {ptrBits : Nat} {slots slots' : List LocalSlotState} {locals₃ : List LocalSlot}
    {resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem)} {src dst : SynPtr}
    {count elemSize elemAlign sl dl s0 sLen d0 dLen : Nat} {srcElems dstElems : List Value}
    (hRel : SlotsRefine SlotBelow slots locals₃)
    (hCount : 2 ≤ count) (hElemSz : 0 < elemSize)
    (hSrcR : resolve src false = .ok (sl, [.constantIndex s0 sLen false]))
    (hDstR : resolve dst true = .ok (dl, [.constantIndex d0 dLen false]))
    (hNe : sl ≠ dl)
    (hSrcRoot : slots[sl]? = some (.init (.aggregate 0 srcElems)))
    (hDstRoot : slots[dl]? = some (.init (.aggregate 0 dstElems)))
    (hSLen : srcElems.length = sLen)
    (hDLen : dstElems.length = dLen)
    (h : evalCopyNonOverlappingSubplace arityOf rootTyOf ts ptrBits slots resolve src dst count
      elemSize elemAlign = some slots')
    (s : MachineState) (srcOp dstOp : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (hTagNe : srcPtr.tag ≠ dstPtr.tag)
    (hSrcEntry : srcEntry.targetLocal = sl ∧ srcEntry.targetProjection = [])
    (hDstEntry : dstEntry.targetLocal = dl ∧ dstEntry.targetProjection = [])
    (hSrcOff : srcPtr.offsetBytes = s0)
    (hDstOff : dstPtr.offsetBytes = d0)
    (hSrcU : resolveUnionEndpoint? localDecls layouts locals₃ srcEntry = none)
    (hDstU : resolveUnionEndpoint? localDecls layouts locals₃ dstEntry = none)
    (hNotAdt : ∀ fn args idx, placeTy localDecls layouts ⟨dl, []⟩ ≠ some { kind := .adt fn args, layoutIdx := idx }) :
    let newDstVal := Value.aggregate 0 (spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems)
    evalCopyNonOverlappingPermOk s srcOp dstOp localDecls layouts srcPtr dstPtr srcEntry dstEntry
        count locals₃ =
      .step (advanceStmt s (locals₃.set dl (.init newDstVal))
        { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows dl (some dstPtr.tag) }) ∧
    SlotsRefine SlotBelow slots' (locals₃.set dl (.init newDstVal)) := by
  unfold evalCopyNonOverlappingSubplace at h
  split at h
  · nomatch h
  split at h
  · omega
  split at h
  · nomatch h
  rw [hSrcR, hDstR] at h
  have hNot1 : ¬ (count = 1 ∨ count * elemSize = 0) := by
    rintro (rfl | hMul)
    · omega
    · exact absurd hMul (Nat.ne_of_gt (Nat.mul_pos (by omega) hElemSz))
  have hSplitS : splitLastElem [.constantIndex s0 sLen false] = some ([], s0, sLen) := rfl
  have hSplitD : splitLastElem [.constantIndex d0 dLen false] = some ([], d0, dLen) := rfl
  simp only [hNot1, ↓reduceIte, hSplitS, hSplitD] at h
  split at h
  · rename_i hBounds
    obtain ⟨hSBound, hDBound⟩ := hBounds
    have hSrcRead : readPlaceState slots ⟨sl, [.subslice s0 (s0 + count) false]⟩ =
        .ok (.aggregate 0 ((srcElems.drop s0).take count)) := by
      have hSub : extractSubslice srcElems s0 (s0 + count) false =
          some ((srcElems.drop s0).take count) := by
        apply (extractSubslice_eq_some_iff srcElems s0 (s0 + count) false _).mpr
        simp [subsliceEndIdx, hSLen, hSBound]
      simp [readPlaceState, projectionHasDeref, get?_eq_getElem?, hSrcRoot, evalValueProjRead, hSub]
    simp only [List.nil_append] at h
    rw [hSrcRead] at h
    simp only at h
    have hSpliceEq : spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems =
        dstElems.take d0 ++ ((srcElems.drop s0).take count ++ dstElems.drop (d0 + count)) := by
      rw [spliceValues_eq_take_append_drop, takeValues_eq_take, dropValues_eq_drop]
      have hTakeLen : ((srcElems.drop s0).take count).length = count := by
        rw [List.length_take, List.length_drop, hSLen]
        omega
      rw [hTakeLen]
    have hSlots' : slots' =
        slots.set dl (.init (.aggregate 0
          (spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems))) := by
      by_cases hWhole : d0 = 0 ∧ count = dLen
      · obtain ⟨rfl, rfl⟩ := hWhole
        simp only [and_self, ↓reduceIte] at h
        have hWS : writePlaceState arityOf slots ⟨dl, []⟩ (rootTyOf dl)
            (.aggregate 0 ((srcElems.drop s0).take count)) =
            .ok (slots.set dl (.init (.aggregate 0 ((srcElems.drop s0).take count)))) := by
          simp [writePlaceState, projectionHasDeref, get?_eq_getElem?, hDstRoot, writeToFieldSlot,
            fieldSlotToLocalSlotState]
        rw [hWS] at h
        simp only [Option.some.injEq] at h
        rw [← h, hSpliceEq]
        simp [← hDLen]
      · simp only [hWhole, ↓reduceIte] at h
        have hExtD : extractSubslice dstElems d0 (d0 + count) false =
            some ((dstElems.drop d0).take count) := by
          apply (extractSubslice_eq_some_iff dstElems d0 (d0 + count) false _).mpr
          simp [subsliceEndIdx, hDLen, hDBound]
        have hRep : replaceSubslice dstElems d0 (d0 + count) false ((srcElems.drop s0).take count) =
            some (dstElems.take d0 ++ ((srcElems.drop s0).take count ++ dstElems.drop (d0 + count))) := by
          apply (replaceSubslice_eq_some_iff dstElems d0 (d0 + count) false _ _).mpr
          refine ⟨by omega, by simp [subsliceEndIdx], ?_, rfl⟩
          simp [subsliceEndIdx, List.length_take, List.length_drop, hSLen]; omega
        have hWS : writePlaceState arityOf slots ⟨dl, [.subslice d0 (d0 + count) false]⟩ (rootTyOf dl)
            (.aggregate 0 ((srcElems.drop s0).take count)) =
            .ok (slots.set dl (.init (.aggregate 0
              (dstElems.take d0 ++ ((srcElems.drop s0).take count ++ dstElems.drop (d0 + count)))))) := by
          simp [writePlaceState, projectionHasDeref, get?_eq_getElem?, hDstRoot, writeToFieldSlot,
            evalValueProjWrite, hExtD, hRep, fieldSlotToLocalSlotState]
        rw [hWS] at h
        simp only [Option.some.injEq] at h
        rw [← h, hSpliceEq]
    subst hSlots'
    have hTSrc : locals₃[sl]? = some (.init (.aggregate 0 srcElems)) := by
      rcases SlotsRefine.get?_rel sl hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, hAT⟩
      · simp only [get?_eq_getElem?] at hA; rw [hA] at hSrcRoot; nomatch hSrcRoot
      · simp only [get?_eq_getElem?] at hA hT
        rw [hA] at hSrcRoot; cases hSrcRoot
        cases t with
        | init w => have hvw : Value.aggregate 0 srcElems = w := hAT; subst hvw; exact hT
        | _ => simp [SlotBelow] at hAT
    have hTDst : locals₃[dl]? = some (.init (.aggregate 0 dstElems)) := by
      rcases SlotsRefine.get?_rel dl hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, hAT⟩
      · simp only [get?_eq_getElem?] at hA; rw [hA] at hDstRoot; nomatch hDstRoot
      · simp only [get?_eq_getElem?] at hA hT
        rw [hA] at hDstRoot; cases hDstRoot
        cases t with
        | init w => have hvw : Value.aggregate 0 dstElems = w := hAT; subst hvw; exact hT
        | _ => simp [SlotBelow] at hAT
    have hLtD3 : dl < locals₃.length := (List.getElem?_eq_some_iff.mp hTDst).1
    refine ⟨?_, SlotsRefine.set (a := .init _) (t := .init _) rfl dl hRel⟩
    unfold evalCopyNonOverlappingPermOk
    have hBeqN1 : Nat.beq count 1 = false :=
      ((beq_cases count 1).resolve_left (fun ⟨_, hEq⟩ => by omega)).1
    have hBeqTag : Nat.beq srcPtr.tag dstPtr.tag = false :=
      ((beq_cases srcPtr.tag dstPtr.tag).resolve_left (fun ⟨_, hEq⟩ => hTagNe hEq)).1
    have hBeqLoc : Nat.beq sl dl = false :=
      ((beq_cases sl dl).resolve_left (fun ⟨_, hEq⟩ => hNe hEq)).1
    have hAdtFalse : (match placeTy localDecls layouts ⟨dl, []⟩ with
        | some { kind := .adt _ _, .. } => true
        | _ => false) = false := by
      cases hPT : placeTy localDecls layouts ⟨dl, []⟩ with
      | none => rfl
      | some ty =>
        rcases ty with ⟨k, lidx⟩
        cases k with
        | adt fn args => exact absurd hPT (hNotAdt fn args lidx)
        | _ => rfl
    have hBleS : Nat.ble (Nat.add s0 count) (length srcElems) = true := by
      rw [length_eq_list_length, hSLen]; exact Nat.ble_eq.mpr hSBound
    have hBleD : Nat.ble (Nat.add d0 count) (length dstElems) = true := by
      rw [length_eq_list_length, hDLen]; exact Nat.ble_eq.mpr hDBound
    have hSetD : set? locals₃ dl
        (.init (.aggregate 0 (spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems))) =
        some (locals₃.set dl
          (.init (.aggregate 0 (spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems)))) :=
      set?_eq_some_iff.mpr ⟨hLtD3, rfl⟩
    have hWPV0 : writePlaceValue locals₃ s.memory.borrows ⟨dl, []⟩
        (.aggregate 0 (spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems)) =
        .ok (locals₃.set dl
          (.init (.aggregate 0 (spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems)))) := by
      unfold writePlaceValue
      simp only [get?_eq_getElem?, hTDst, hSetD]
    let _ := hAdtFalse
    simp only [hSrcU, hDstU, hBeqN1, Bool.false_and, hSrcEntry.1, hSrcEntry.2, hDstEntry.1,
      hDstEntry.2, get?_eq_getElem?, hTSrc, hTDst, readProjectedValue, hSrcOff, hDstOff,
      Bool.not_false, hBleS, hBleD, Bool.and_self, hBeqTag, hBeqLoc,
      commitCopyDstPlaceWrite, hWPV0]
  · nomatch h

/-- **Statement-level array-window (`count ≥ 2`) `CopyNonOverlapping` refinement
(`evalStmt_copyNonOverlapping_window_refines`)**: lifts `evalCopyNonOverlappingSubplace_window_refines`
through Trusted's `evalStmt` on `copy_nonoverlapping(srcOp, dstOp, countOp)`. -/
theorem evalStmt_copyNonOverlapping_window_refines
    {arityOf : Ty → VariantIdx → Bool → Option Nat} {rootTyOf : Nat → Ty} {ts : Bool}
    {ptrBits : Nat} {slots slots' : List LocalSlotState}
    {resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem)} {src dst : SynPtr}
    {count elemSize elemAlign sl dl s0 sLen d0 dLen : Nat} {srcElems dstElems : List Value}
    (s : MachineState)
    (hRel : SlotsRefine SlotBelow slots s.frame.locals)
    (hCount : 2 ≤ count) (hElemSz : 0 < elemSize)
    (hSrcR : resolve src false = .ok (sl, [.constantIndex s0 sLen false]))
    (hDstR : resolve dst true = .ok (dl, [.constantIndex d0 dLen false]))
    (hNe : sl ≠ dl)
    (hSrcRoot : slots[sl]? = some (.init (.aggregate 0 srcElems)))
    (hDstRoot : slots[dl]? = some (.init (.aggregate 0 dstElems)))
    (hSLen : srcElems.length = sLen)
    (hDLen : dstElems.length = dLen)
    (h : evalCopyNonOverlappingSubplace arityOf rootTyOf ts ptrBits slots resolve src dst count
      elemSize elemAlign = some slots')
    (srcOp dstOp countOp : Operand) (span : String) (localDecls : List LocalDecl)
    (layouts : LayoutTable) {srcPtr dstPtr : ProvenancePtr} {srcSz dstSz : Nat}
    {countSc : ScalarInt} {srcEntry dstEntry : BorrowEntry}
    (hSrcOp : evalOperand s.frame.locals srcOp s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls = .ok (.ptr srcPtr srcSz) s.frame.locals)
    (hDstOp : evalOperand s.frame.locals dstOp s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls = .ok (.ptr dstPtr dstSz) s.frame.locals)
    (hCnt : evalOperand s.frame.locals countOp s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls = .ok (.scalar countSc) s.frame.locals)
    (hCountBits : countSc.bits = count)
    (hSrcE : lookupBorrow s.memory.borrows srcPtr.tag = some srcEntry)
    (hDstE : lookupBorrow s.memory.borrows dstPtr.tag = some dstEntry)
    (hSrcP : srcEntry.perm ≠ .disabled)
    (hDstP : dstEntry.perm = .active ∨ dstEntry.perm = .reserved)
    (hTagNe : srcPtr.tag ≠ dstPtr.tag)
    (hSrcEntry : srcEntry.targetLocal = sl ∧ srcEntry.targetProjection = [])
    (hDstEntry : dstEntry.targetLocal = dl ∧ dstEntry.targetProjection = [])
    (hSrcOff : srcPtr.offsetBytes = s0)
    (hDstOff : dstPtr.offsetBytes = d0)
    (hSrcU : resolveUnionEndpoint? localDecls layouts s.frame.locals srcEntry = none)
    (hDstU : resolveUnionEndpoint? localDecls layouts s.frame.locals dstEntry = none)
    (hNotAdt : ∀ fn args idx, placeTy localDecls layouts ⟨dl, []⟩ ≠ some { kind := .adt fn args, layoutIdx := idx }) :
    let newDstVal := Value.aggregate 0 (spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems)
    evalStmt s ⟨.intrinsic (.copyNonOverlapping srcOp dstOp countOp), span⟩ localDecls layouts =
      .step (advanceStmt s (s.frame.locals.set dl (.init newDstVal))
        { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows dl (some dstPtr.tag) }) ∧
    SlotsRefine SlotBelow slots' (s.frame.locals.set dl (.init newDstVal)) := by
  have hPermOk : evalCopyNonOverlappingWithCount s srcOp dstOp localDecls layouts
      (.ptr srcPtr srcSz) (.ptr dstPtr dstSz) count s.frame.locals =
      evalCopyNonOverlappingPermOk s srcOp dstOp localDecls layouts srcPtr dstPtr srcEntry dstEntry
        count s.frame.locals := by
    unfold evalCopyNonOverlappingWithCount
    have hCntNe0 : Nat.beq count 0 = false :=
      ((beq_cases count 0).resolve_left (fun ⟨_, hEq⟩ => by omega)).1
    simp only [hCntNe0, hSrcE, hDstE]
    cases hs : srcEntry.perm with
    | disabled => exact absurd hs hSrcP
    | _ => rcases hDstP with hd | hd <;> simp [hd]
  simp only [evalStmt, evalCopyNonOverlapping, hSrcOp, hDstOp, hCnt, hCountBits, hPermOk]
  exact evalCopyNonOverlappingSubplace_window_refines hRel hCount hElemSz hSrcR hDstR hNe hSrcRoot
    hDstRoot hSLen hDLen h s srcOp dstOp localDecls layouts srcPtr dstPtr srcEntry dstEntry
    hTagNe hSrcEntry hDstEntry hSrcOff hDstOff hSrcU hDstU hNotAdt

/-! ### Section 4h: Reborrows through a pointer (`&((*_p).tail)` vs `&raw ((*_p).tail)`) -/

/-- The local a synthetic provenance names (`alloc_id - 1`, when it is a local of the frame). -/
def synthProvLocal (slots : List LocalSlotState) (p : SynPtr) : Option Nat :=
  match p.prov with
  | some (l + 1, _) => if l < slots.length then some l else none
  | _ => none

/-- Whether the target local of a reborrow base is storage-dead. -/
def reborrowTargetDead (slots : List LocalSlotState) : Option Nat → Bool
  | some l =>
    match slots[l]? with
    | some .dead => true
    | _ => false
  | none => false

/-- The `DeadLocal` fault of a dangling reborrow base. -/
def reborrowDeadErr : Option Nat → Except DerefErr SynPtr
  | some l => .error (.deadLocal l)
  | none => .error .unsupported

/-- An address-only raw reborrow: a raw result of a raw base without `Downcast` in the tail. -/
def addrOnlyRaw (expectedRef : Bool) (pty : PtrTy) (hasDowncast : Bool) : Bool :=
  !expectedRef && !pty.isRef && !hasDowncast

/-- The provenance tag of a synthetic pointer (the untagged `1` without provenance). -/
def synthProvTag (p : SynPtr) : Nat :=
  match p.prov with
  | some (_, t) => t
  | none => 1

/-- **The provenance tag of an in-bounds `offset_inbounds` reborrow fallback**
(`rvalue.rs:9693-9701`): the untagged `1` when at most one sub-place of local `l` of the result's
pointee type `resTy` sits at offset `off` (`collect_subplace_paths`); otherwise the base tag's
candidate ordinal re-encoded for `resTy` (`encode_subplace_tag`) when it decodes for `resTy` to an
in-range ordinal (`decode_subplace_tag`), and `1` when it does not. -/
def reborrowFallbackTag (cx : SubplaceCtx) (resTy l off baseTag : Nat) : Nat :=
  if (cx.candidates resTy l off).length ≤ 1 then 1
  else
    match cx.decodeTag baseTag resTy with
    | some ord => if ord < (cx.candidates resTy l off).length then cx.encodeTag resTy ord else 1
    | none => 1

/-- A unique (or absent) fallback candidate gives the untagged provenance `1`. -/
theorem reborrowFallbackTag_unique {cx : SubplaceCtx} {resTy l off baseTag : Nat}
    (h : (cx.candidates resTy l off).length ≤ 1) :
    reborrowFallbackTag cx resTy l off baseTag = 1 := by
  simp [reborrowFallbackTag, h]

/-- With several fallback candidates, a base tag that decodes for `resTy` to an in-range ordinal
is re-encoded for `resTy`. -/
theorem reborrowFallbackTag_decoded {cx : SubplaceCtx} {resTy l off baseTag ord : Nat}
    (hMany : 1 < (cx.candidates resTy l off).length)
    (hDec : cx.decodeTag baseTag resTy = some ord) (hOrd : ord < (cx.candidates resTy l off).length) :
    reborrowFallbackTag cx resTy l off baseTag = cx.encodeTag resTy ord := by
  have hNot : ¬ (cx.candidates resTy l off).length ≤ 1 := by omega
  simp [reborrowFallbackTag, hNot, hDec, hOrd]

/-- With several fallback candidates, a base tag without a usable ordinal for `resTy` (it does not
decode, e.g. after a cast to another pointee type, or its ordinal is out of range) gives `1`. -/
theorem reborrowFallbackTag_stale {cx : SubplaceCtx} {resTy l off baseTag : Nat}
    (hStale : ∀ ord, cx.decodeTag baseTag resTy = some ord →
      (cx.candidates resTy l off).length ≤ ord) :
    reborrowFallbackTag cx resTy l off baseTag = 1 := by
  unfold reborrowFallbackTag
  split
  · rfl
  · cases hDec : cx.decodeTag baseTag resTy with
    | none => rfl
    | some ord =>
      have hLe := hStale ord hDec
      have hNot : ¬ ord < (cx.candidates resTy l off).length := by omega
      simp [hNot]

/-- **`resolve_reborrow_with_tail_in`**: `&((*p).tail)` (`expectedRef`) or `&raw ((*p).tail)` of a
base pointer `p` of type `pty` whose pointee has layout `dtl`, where `tail` (with `Downcast` steps
iff `hasDowncast`) has static offset `tailOff` inside the pointee and the result's pointee type
(`pointee_ty`, the type of `(*p).tail`) is `resTy`:
1. a reference result or a reference base needs a non-null base (`InvalidBitPattern` for `&T`,
   `NullPointerAccess` otherwise) aligned to the pointee (`MisalignedPointer`,
   `UnsupportedLayout`) with an inhabited pointee for a reference base;
2. anything but an address-only raw reborrow needs a non-null base with the synthetic provenance
   of a live local (`NullPointerAccess`, `DeadLocal`);
3. an address-only raw reborrow of a null, provenance-free, or dangling base is valid exactly at
   offset `0` (it keeps the base pointer), and otherwise faults or is unsupported (MiniRust's
   `offset_inbounds`);
4. otherwise the base resolves to a sub-place `(l, q)` (`resolveSyntheticSubplace`), and the result
   addresses `q ++ tail` inside `l`'s synthetic allocation with provenance `(l + 1, tag)`;
5. when that resolution fails, an address-only raw reborrow of a base with the provenance of a live
   local `l` falls back to `offset_inbounds`: a base outside `l`'s allocation is kept at offset `0`
   (and is unsupported otherwise), and an in-bounds base at relative offset `rel` yields the address
   at `rel + tailOff` (when that is still in bounds) with provenance
   `(l + 1, reborrowFallbackTag cx resTy l (rel + tailOff) baseTag)` (`rvalue.rs:9654-9706`). -/
def evalReborrowTail (cx : SubplaceCtx) (slots : List LocalSlotState) (base : SynPtr)
    (pty : PtrTy) (dtl : TyLayout) (expectedRef hasDowncast : Bool) (tail : List ProjectionElem)
    (tailOff tag resTy : Nat) : Except DerefErr SynPtr :=
  if cx.limit < base.addr then .error .invalidBitPattern
  else if (expectedRef || pty.isRef) && base.addr = 0 then
    (if pty.isRef then .error .invalidBitPattern else .error .nullPointer)
  else if (expectedRef || pty.isRef) && base.addr % dtl.minAlign ≠ 0 then .error .misaligned
  else if (expectedRef || pty.isRef) && base.addr % dtl.maxAlign ≠ 0 then .error .unsupportedLayout
  else if pty.isRef && !dtl.inhabited then .error .uninhabited
  else if !addrOnlyRaw expectedRef pty hasDowncast && base.addr = 0 then .error .nullPointer
  else if !addrOnlyRaw expectedRef pty hasDowncast && (synthProvLocal slots base).isNone then
    .error .unsupported
  else if !addrOnlyRaw expectedRef pty hasDowncast &&
      reborrowTargetDead slots (synthProvLocal slots base) then
    reborrowDeadErr (synthProvLocal slots base)
  else if addrOnlyRaw expectedRef pty hasDowncast && (base.addr = 0 ||
      (synthProvLocal slots base).isNone || reborrowTargetDead slots (synthProvLocal slots base)) then
    if tailOff = 0 then .ok base
    else if base.addr = 0 then .error .nullPointer
    else if reborrowTargetDead slots (synthProvLocal slots base) then
      reborrowDeadErr (synthProvLocal slots base)
    else .error .unsupported
  else
    match resolveSyntheticSubplace cx slots base pty false with
    | .ok (l, q) =>
      match cx.layoutOf l, localBaseAddr cx.allocs l cx.limit with
      | some lay, some b =>
        match subplaceAt lay 0 (q ++ tail) with
        | some (_, off) => .ok ⟨b + off, some (l + 1, tag)⟩
        | none => .error .unsupported
      | _, _ => .error .unsupported
    | .error e =>
      if addrOnlyRaw expectedRef pty hasDowncast then
        match synthProvLocal slots base with
        | some l =>
          match localBaseAddr cx.allocs l cx.limit, ownLayout cx.allocs l with
          | some b, some (allocSize, _) =>
            if base.addr < b ∨ b + allocSize < base.addr then
              if tailOff = 0 then .ok base else .error .unsupported
            else if (base.addr - b) + tailOff ≤ allocSize ∧ b + ((base.addr - b) + tailOff) ≤ cx.limit then
              .ok ⟨b + ((base.addr - b) + tailOff),
                some (l + 1, reborrowFallbackTag cx resTy l ((base.addr - b) + tailOff)
                  (synthProvTag base))⟩
            else .error .unsupported
          | _, _ => .error .unsupported
        | none => .error e
      else .error e

/-- **Resolved sub-place reborrows (`evalReborrowTail_resolved_ok`)**: when `base` resolves to a
sub-place `(l, q)` of a live local `l` (whose synthetic allocation starts at `b`) and `q ++ tail`
has static offset `off` inside `l`'s layout, `evalReborrowTail` produces the synthetic pointer
`⟨b + off, some (l + 1, tag)⟩`. -/
theorem evalReborrowTail_resolved_ok (cx : SubplaceCtx) {slots : List LocalSlotState}
    {base : SynPtr} {pty : PtrTy} {dtl : TyLayout} {expectedRef hasDowncast : Bool}
    {tail : List ProjectionElem} {tailOff tag resTy l t b off : Nat} {q : List ProjectionElem}
    {lay sub : ByteLayout} {st : LocalSlotState}
    (hW : base.addr ≤ cx.limit) (hNZ : base.addr ≠ 0)
    (hA1 : base.addr % dtl.minAlign = 0) (hA2 : base.addr % dtl.maxAlign = 0)
    (hInh : pty.isRef = true → dtl.inhabited = true)
    (hProv : base.prov = some (l + 1, t)) (hLive : slots[l]? = some st) (hNotDead : st ≠ .dead)
    (hRes : resolveSyntheticSubplace cx slots base pty false = .ok (l, q))
    (hLay : cx.layoutOf l = some lay) (hBase : localBaseAddr cx.allocs l cx.limit = some b)
    (hSub : subplaceAt lay 0 (q ++ tail) = some (sub, off)) :
    evalReborrowTail cx slots base pty dtl expectedRef hasDowncast tail tailOff tag resTy =
      .ok ⟨b + off, some (l + 1, tag)⟩ := by
  have hlt : l < slots.length := (List.getElem?_eq_some_iff.mp hLive).1
  have hT : synthProvLocal slots base = some l := by simp [synthProvLocal, hProv, hlt]
  have hDeadF : reborrowTargetDead slots (some l) = false := by
    cases st with
    | dead => exact absurd rfl hNotDead
    | _ => simp [reborrowTargetDead, hLive]
  have h1 : ¬ cx.limit < base.addr := by omega
  have h5 : (pty.isRef && !dtl.inhabited) = false := by
    cases hr : pty.isRef with
    | false => rfl
    | true => simp [hInh hr]
  simp [evalReborrowTail, h1, hNZ, hA1, hA2, h5, hT, hDeadF, hRes, hLay, hBase, hSub]

/-- **Address-only raw `offset_inbounds` fallback (`evalReborrowTail_raw_inbounds_fallback_ok`,
`rvalue.rs:9654-9706`)**: when `resolveSyntheticSubplace` fails (e.g. a misaligned raw pointer
`*const (u32, u32)` at byte offset `1` inside a `[u8; 16]` local `l`), an address-only raw
reborrow (`expectedRef = false`, `pty.isRef = false`, `hasDowncast = false`) whose `base.addr` and
`base.addr + tailOff` both lie within `[b, b + allocSize]` succeeds with the address
`b + ((base.addr - b) + tailOff)` and the provenance `(l + 1, tag')` of local `l`, where `tag'` is
`reborrowFallbackTag` of the result's pointee type `resTy` at that offset and the base's tag `t`
(`with_provenance(local_base + total_off, target_local + 1, tag)`). -/
theorem evalReborrowTail_raw_inbounds_fallback_ok (cx : SubplaceCtx) {slots : List LocalSlotState}
    {base : SynPtr} {pty : PtrTy} (dtl : TyLayout) (tail : List ProjectionElem)
    (tailOff tag resTy : Nat) {l t b allocSize align : Nat} {st : LocalSlotState} {e : DerefErr}
    (hRaw : pty.isRef = false) (hW : base.addr ≤ cx.limit) (hNZ : base.addr ≠ 0)
    (hProv : base.prov = some (l + 1, t)) (hLive : slots[l]? = some st) (hNotDead : st ≠ .dead)
    (hResErr : resolveSyntheticSubplace cx slots base pty false = .error e)
    (hBase : localBaseAddr cx.allocs l cx.limit = some b)
    (hOwn : ownLayout cx.allocs l = some (allocSize, align))
    (hInLo : b ≤ base.addr) (hInHi : (base.addr - b) + tailOff ≤ allocSize)
    (hFit : b + ((base.addr - b) + tailOff) ≤ cx.limit) :
    evalReborrowTail cx slots base pty dtl false false tail tailOff tag resTy =
      .ok ⟨b + ((base.addr - b) + tailOff),
        some (l + 1, reborrowFallbackTag cx resTy l ((base.addr - b) + tailOff) t)⟩ := by
  have hlt : l < slots.length := (List.getElem?_eq_some_iff.mp hLive).1
  have hT : synthProvLocal slots base = some l := by simp [synthProvLocal, hProv, hlt]
  have hDeadF : reborrowTargetDead slots (some l) = false := by
    cases st with
    | dead => exact absurd rfl hNotDead
    | _ => simp [reborrowTargetDead, hLive]
  have h1 : ¬ cx.limit < base.addr := by omega
  have hOut : ¬ (base.addr < b ∨ b + allocSize < base.addr) := by omega
  have hTag : synthProvTag base = t := by simp [synthProvTag, hProv]
  simp [evalReborrowTail, addrOnlyRaw, hRaw, h1, hNZ, hT, hDeadF, hResErr, hBase, hOwn, hOut,
    hInHi, hFit, hTag]

/-- **A unique-candidate `offset_inbounds` fallback is untagged
(`evalReborrowTail_raw_inbounds_fallback_unique_tag`)**: under the hypotheses of
`evalReborrowTail_raw_inbounds_fallback_ok`, when at most one sub-place of `l` of the result's
pointee type `resTy` sits at the fallback offset (`collect_subplace_paths(..).len() <= 1`), the
fallback pointer carries the untagged provenance `(l + 1, 1)`, whatever the base's tag `t`. -/
theorem evalReborrowTail_raw_inbounds_fallback_unique_tag (cx : SubplaceCtx)
    {slots : List LocalSlotState} {base : SynPtr} {pty : PtrTy} (dtl : TyLayout)
    (tail : List ProjectionElem) (tailOff tag resTy : Nat) {l t b allocSize align : Nat}
    {st : LocalSlotState} {e : DerefErr}
    (hRaw : pty.isRef = false) (hW : base.addr ≤ cx.limit) (hNZ : base.addr ≠ 0)
    (hProv : base.prov = some (l + 1, t)) (hLive : slots[l]? = some st) (hNotDead : st ≠ .dead)
    (hResErr : resolveSyntheticSubplace cx slots base pty false = .error e)
    (hBase : localBaseAddr cx.allocs l cx.limit = some b)
    (hOwn : ownLayout cx.allocs l = some (allocSize, align))
    (hInLo : b ≤ base.addr) (hInHi : (base.addr - b) + tailOff ≤ allocSize)
    (hFit : b + ((base.addr - b) + tailOff) ≤ cx.limit)
    (hUniq : (cx.candidates resTy l ((base.addr - b) + tailOff)).length ≤ 1) :
    evalReborrowTail cx slots base pty dtl false false tail tailOff tag resTy =
      .ok ⟨b + ((base.addr - b) + tailOff), some (l + 1, 1)⟩ := by
  rw [evalReborrowTail_raw_inbounds_fallback_ok cx dtl tail tailOff tag resTy hRaw hW hNZ hProv
    hLive hNotDead hResErr hBase hOwn hInLo hInHi hFit, reborrowFallbackTag_unique hUniq]

/-- **Offset-`0` raw reborrows of null pointers are valid (`evalReborrowTail_raw_null_zero`)**:
`&raw ((*p).tail)` of a null raw pointer with a zero-offset, `Downcast`-free tail is the null
pointer itself. -/
theorem evalReborrowTail_raw_null_zero (cx : SubplaceCtx) (slots : List LocalSlotState)
    {base : SynPtr} {pty : PtrTy} (dtl : TyLayout) (tail : List ProjectionElem) (tag resTy : Nat)
    (hRaw : pty.isRef = false) (h0 : base.addr = 0) :
    evalReborrowTail cx slots base pty dtl false false tail 0 tag resTy = .ok base := by
  simp [evalReborrowTail, addrOnlyRaw, hRaw, h0]

/-- **Offset-`0` raw reborrows of dangling pointers are valid; non-zero offsets fault
(`evalReborrowTail_raw_dangling`)**: an address-only raw reborrow of a pointer into a storage-dead
local keeps the pointer at offset `0` and is `DeadLocal` at any non-zero tail offset. -/
theorem evalReborrowTail_raw_dangling (cx : SubplaceCtx) {slots : List LocalSlotState}
    {base : SynPtr} {pty : PtrTy} (dtl : TyLayout) (tail : List ProjectionElem) (tag resTy : Nat)
    {l t : Nat} (hRaw : pty.isRef = false) (hW : base.addr ≤ cx.limit) (hNZ : base.addr ≠ 0)
    (hProv : base.prov = some (l + 1, t)) (hDead : slots[l]? = some .dead) :
    evalReborrowTail cx slots base pty dtl false false tail 0 tag resTy = .ok base ∧
      ∀ tailOff, tailOff ≠ 0 →
        evalReborrowTail cx slots base pty dtl false false tail tailOff tag resTy =
          .error (.deadLocal l) := by
  have hlt : l < slots.length := (List.getElem?_eq_some_iff.mp hDead).1
  have hT : synthProvLocal slots base = some l := by simp [synthProvLocal, hProv, hlt]
  have h1 : ¬ cx.limit < base.addr := by omega
  constructor
  · simp [evalReborrowTail, addrOnlyRaw, reborrowTargetDead, hRaw, h1, hT, hDead]
  · intro tailOff hOff
    simp [evalReborrowTail, addrOnlyRaw, reborrowTargetDead, reborrowDeadErr, hRaw, h1, hNZ, hT,
      hDead, hOff]

/-- **Reference reborrows of null pointers fault (`evalReborrowTail_ref_null`)**, whatever the tail. -/
theorem evalReborrowTail_ref_null (cx : SubplaceCtx) (slots : List LocalSlotState)
    {base : SynPtr} (pty : PtrTy) (dtl : TyLayout) (hasDowncast : Bool) (tail : List ProjectionElem)
    (tailOff tag resTy : Nat) (h0 : base.addr = 0) :
    evalReborrowTail cx slots base pty dtl true hasDowncast tail tailOff tag resTy =
      .error (if pty.isRef then .invalidBitPattern else .nullPointer) := by
  simp only [evalReborrowTail, h0]
  cases pty.isRef <;> simp

/-- **Reference reborrows enforce the pointee's alignment (`evalReborrowTail_ref_misaligned`)**. -/
theorem evalReborrowTail_ref_misaligned (cx : SubplaceCtx) (slots : List LocalSlotState)
    {base : SynPtr} (pty : PtrTy) {dtl : TyLayout} (hasDowncast : Bool) (tail : List ProjectionElem)
    (tailOff tag resTy : Nat) (hW : base.addr ≤ cx.limit) (hNZ : base.addr ≠ 0)
    (hMis : base.addr % dtl.minAlign ≠ 0) :
    evalReborrowTail cx slots base pty dtl true hasDowncast tail tailOff tag resTy =
      .error .misaligned := by
  have h1 : ¬ cx.limit < base.addr := by omega
  simp [evalReborrowTail, h1, hNZ, hMis]

/-- **Reference reborrows enforce liveness (`evalReborrowTail_ref_dead`)**: `&((*p).tail)` of an
aligned pointer into a storage-dead local is `DeadLocal`. -/
theorem evalReborrowTail_ref_dead (cx : SubplaceCtx) {slots : List LocalSlotState}
    {base : SynPtr} {pty : PtrTy} {dtl : TyLayout} (hasDowncast : Bool) (tail : List ProjectionElem)
    (tailOff tag resTy : Nat) {l t : Nat} (hW : base.addr ≤ cx.limit) (hNZ : base.addr ≠ 0)
    (hA1 : base.addr % dtl.minAlign = 0) (hA2 : base.addr % dtl.maxAlign = 0)
    (hInh : pty.isRef = true → dtl.inhabited = true)
    (hProv : base.prov = some (l + 1, t)) (hDead : slots[l]? = some .dead) :
    evalReborrowTail cx slots base pty dtl true hasDowncast tail tailOff tag resTy =
      .error (.deadLocal l) := by
  have hlt : l < slots.length := (List.getElem?_eq_some_iff.mp hDead).1
  have hT : synthProvLocal slots base = some l := by simp [synthProvLocal, hProv, hlt]
  have h1 : ¬ cx.limit < base.addr := by omega
  have h5 : (pty.isRef && !dtl.inhabited) = false := by
    cases hr : pty.isRef with
    | false => rfl
    | true => simp [hInh hr]
  simp [evalReborrowTail, addrOnlyRaw, reborrowTargetDead, reborrowDeadErr, h1, hNZ, hA1, hA2, h5,
    hT, hDead]

/-! ### Section 4i: A concrete synthetic frame (non-vacuity witnesses)

The frame `_0 : (u32, u32) = (7, 9)`, `_1 : *mut u32 = &raw _0.1` with the synthetic pointer
`0x1004` (base `0x1000` of `_0` plus `_0.1`'s offset `4`) exercises the whole pipeline: the
synthetic sub-place borrow, the unique-candidate resolution, `Deref` reads and writes, and the
collision-free base of `_1`. -/

/-- The `u32` field type of the witness. -/
def witnessU32 : Ty := { kind := .uint .u32, layoutIdx := 0 }

/-- The witness context: type `1` is `u32` (`4`-byte, `4`-aligned), type `100` is `(u32, u32)`;
`_0.1` is the only `u32` sub-place of `_0` at offset `4` (and `_0.0` at offset `0`); the pointer
value `⟨allocId, off⟩` reads as the synthetic pointer `off` with provenance `allocId`. -/
def witnessCtx : SubplaceCtx where
  allocs := [some (8, 4), some (8, 8)]
  limit := 2 ^ 64 - 1
  layoutOf l := if l = 0 then some (.struct 8 [0, 4] [.leaf 4, .leaf 4])
    else if l = 1 then some (.leaf 8) else none
  declTy l := if l = 0 then some 100 else if l = 1 then some 101 else none
  candidates t l off :=
    if t = 1 ∧ l = 0 ∧ off = 4 then [[.field 1 witnessU32]]
    else if t = 1 ∧ l = 0 ∧ off = 0 then [[.field 0 witnessU32]]
    else []
  tyLayout t := if t = 1 then some ⟨4, 4, 4, true, true⟩ else none
  ptrTyAt l q := if l = 1 ∧ q = [] then some ⟨false, 1⟩ else none
  ptrOf pv := ⟨pv.offsetBytes, some (pv.allocId, 0)⟩
  decodeTag _ _ := none

/-- The witness pointer value `&raw _0.1`. -/
def witnessPtr : ProvenancePtr := { allocId := 1, offsetBytes := 0x1004 }

/-- The witness frame. -/
def witnessSlots : List LocalSlotState :=
  [.init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩]), .init (.ptr witnessPtr 8)]

/-- **Witness: the synthetic sub-place borrow `&raw _0.1`** is the pointer `0x1004` (`_0`'s base
`0x1000` plus `_0.1`'s offset `4`) with provenance `1`. -/
theorem witness_borrow :
    evalSubplaceRef witnessCtx witnessSlots 0 [.field 1 witnessU32] 0 = .ok ⟨0x1004, some (1, 0)⟩ := by
  with_unfolding_all rfl

/-- **Witness: `*_1` reads `9`** (the value of `_0.1`). -/
theorem witness_deref_read :
    evalDerefPlaceRead witnessCtx witnessSlots ⟨1, [.deref]⟩ = .ok (.scalar ⟨9, 4⟩) := by
  with_unfolding_all rfl

/-- **Witness: `*_1 = 5` writes only `_0.1`**, and reading `*_1` back yields `5`. -/
theorem witness_deref_write_put_get :
    evalDerefPlaceWrite (fun _ _ _ => none) (fun _ => witnessU32) witnessCtx witnessSlots
        ⟨1, [.deref]⟩ (.scalar ⟨5, 4⟩) =
      .ok [.init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨5, 4⟩]), .init (.ptr witnessPtr 8)] ∧
    evalDerefPlaceRead witnessCtx
        [.init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨5, 4⟩]), .init (.ptr witnessPtr 8)]
        ⟨1, [.deref]⟩ = .ok (.scalar ⟨5, 4⟩) := by
  constructor <;> with_unfolding_all rfl

/-- **Witness: collision-free bases** — `_1`'s synthetic allocation starts at `0x2000`, past
`_0`'s `[0x1000, 0x1008)`. -/
theorem witness_bases :
    localBaseAddr witnessCtx.allocs 0 witnessCtx.limit = some 0x1000 ∧
    localBaseAddr witnessCtx.allocs 1 witnessCtx.limit = some 0x2000 := by
  with_unfolding_all decide

/-- The witness layout is well formed. -/
theorem witnessLayout_wf : (ByteLayout.struct 8 [0, 4] [.leaf 4, .leaf 4]).WF := by
  refine .struct 8 [0, 4] [.leaf 4, .leaf 4] rfl ?_ ?_ ?_
  · intro i o l ho hl
    match i, ho, hl with
    | 0, ho, hl =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ho hl
      subst ho hl
      decide
    | 1, ho, hl =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ho hl
      subst ho hl
      decide
    | i + 2, ho, _ => simp at ho
  · intro i j oi oj li lj hij hoi hoj hli hlj
    match i, j, hoi, hoj, hli, hlj with
    | 0, 0, _, _, _, _ => exact absurd rfl hij
    | 1, 1, _, _, _, _ => exact absurd rfl hij
    | 0, 1, hoi, hoj, hli, hlj =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hoi hoj hli hlj
      subst hoi hoj hli hlj
      decide
    | 1, 0, hoi, hoj, hli, hlj =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hoi hoj hli hlj
      subst hoi hoj hli hlj
      decide
    | i + 2, _, hoi, _, _, _ => simp at hoi
    | 0, j + 2, _, hoj, _, _ => simp at hoj
    | 1, j + 2, _, hoj, _, _ => simp at hoj
  · intro i l hl
    match i, hl with
    | 0, hl =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
      subst hl
      exact .leaf 4
    | 1, hl =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hl
      subst hl
      exact .leaf 4
    | i + 2, hl => simp at hl

/-- The witness context is well formed, so every theorem of this section applies to it. -/
theorem witnessCtx_wf : witnessCtx.WF := by
  refine ⟨fun l lay h => ?_, fun t l off q hq => ?_⟩
  · by_cases h0 : l = 0
    · subst h0
      simp only [witnessCtx, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨witnessLayout_wf, by with_unfolding_all decide⟩
    · by_cases h1 : l = 1
      · subst h1
        simp only [witnessCtx, Nat.one_ne_zero, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨.leaf 8, by with_unfolding_all decide⟩
      · simp [witnessCtx, h0, h1] at h
  · by_cases hA : t = 1 ∧ l = 0 ∧ off = 4
    · obtain ⟨rfl, rfl, rfl⟩ := hA
      have hq' : q = [.field 1 witnessU32] := by simpa [witnessCtx] using hq
      rw [hq']
      exact ⟨.struct 8 [0, 4] [.leaf 4, .leaf 4], .leaf 4, ⟨4, 4, 4, true, true⟩,
        by simp [witnessCtx], by with_unfolding_all rfl, by simp [witnessCtx], rfl⟩
    · by_cases hB : t = 1 ∧ l = 0 ∧ off = 0
      · obtain ⟨rfl, rfl, rfl⟩ := hB
        have hq' : q = [.field 0 witnessU32] := by simpa [witnessCtx] using hq
        rw [hq']
        exact ⟨.struct 8 [0, 4] [.leaf 4, .leaf 4], .leaf 4, ⟨4, 4, 4, true, true⟩,
          by simp [witnessCtx], by with_unfolding_all rfl, by simp [witnessCtx], rfl⟩
      · simp [witnessCtx, hA, hB] at hq

/-- **Witness: no-guess resolution through the general round-trip theorem**: dereferencing the
borrowed pointer `0x1004` (pointee `u32`) resolves to exactly `_0.1`, in both modes — an instance
of `resolveSyntheticSubplace_evalSubplaceRef` whose hypotheses all hold in the witness frame. -/
theorem witness_resolve (ow : Bool) :
    resolveSyntheticSubplace witnessCtx witnessSlots ⟨0x1004, some (1, 0)⟩ ⟨false, 1⟩ ow =
      .ok (0, [.field 1 witnessU32]) :=
  resolveSyntheticSubplace_evalSubplaceRef witnessCtx_wf witness_borrow ow
    (tl := ⟨4, 4, 4, true, true⟩) (by simp [witnessCtx]) (by decide) (by decide) (by simp)
    (lay := .struct 8 [0, 4] [.leaf 4, .leaf 4]) (sub := .leaf 4) (off := 4)
    (by simp [witnessCtx]) (by with_unfolding_all rfl) rfl (by simp [witnessCtx])
    (by simp) (by simp [witnessCtx]) (allocSize := 8) (align := 4)
    (by simp [ownLayout, witnessCtx])

/-- The witness under Trusted's pointer representation: Trusted represents `&raw _0.1` by its borrow
tag `1` at offset `0` (the field is the tag's `targetProjection`), which Anneal reads as the
synthetic pointer `0x1004` with provenance `1`. -/
def witnessCtxT : SubplaceCtx :=
  { witnessCtx with
    ptrOf := fun pv => if pv.allocId = 1 then ⟨0x1004, some (1, 0)⟩ else ⟨pv.offsetBytes, none⟩ }

/-- Trusted's pointer value of `&raw _0.1` (tag `1`, offset `0`). -/
def witnessPtrT : ProvenancePtr := { allocId := 1, offsetBytes := 0 }

/-- The witness frame holding Trusted's pointer value (Anneal's and Trusted's slots coincide). -/
def witnessSlotsT : List LocalSlotState :=
  [.init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩]), .init (.ptr witnessPtrT 8)]

/-- Trusted's frame. -/
def witnessLocalsT : List LocalSlot :=
  [.init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩]), .init (.ptr witnessPtrT 8)]

/-- Trusted's borrow entry of `&raw _0.1`. -/
def witnessEntry : BorrowEntry :=
  { tag := 1, targetLocal := 0, targetProjection := [.field 1 witnessU32], perm := .active }

theorem witnessCtxT_wf : witnessCtxT.WF := ⟨witnessCtx_wf.layout, witnessCtx_wf.candidates⟩

/-- **Witness: Anneal resolves Trusted's pointer to Trusted's borrow target
(`witness_trusted_resolve`)**: under `witnessCtxT`, the no-guess resolution of Trusted's pointer
value `witnessPtrT` (pointee `u32`) is exactly the sub-place `_0.1` named by Trusted's borrow entry
`witnessEntry` — an instance of `resolveSyntheticSubplace_evalSubplaceRef`. -/
theorem witness_trusted_resolve :
    resolveSyntheticSubplace witnessCtxT witnessSlotsT (witnessCtxT.ptrOf witnessPtrT)
      ⟨false, 1⟩ false = .ok (witnessEntry.targetLocal, witnessEntry.targetProjection) := by
  have hRef : evalSubplaceRef witnessCtxT witnessSlotsT 0 [.field 1 witnessU32] 0 =
      .ok ⟨0x1004, some (1, 0)⟩ := by with_unfolding_all rfl
  have hPtrOf : witnessCtxT.ptrOf witnessPtrT = ⟨0x1004, some (1, 0)⟩ := by
    simp [witnessCtxT, witnessPtrT]
  rw [hPtrOf]
  exact resolveSyntheticSubplace_evalSubplaceRef witnessCtxT_wf hRef false
    (tl := ⟨4, 4, 4, true, true⟩) (by simp [witnessCtxT, witnessCtx]) (by decide) (by decide)
    (by simp) (lay := .struct 8 [0, 4] [.leaf 4, .leaf 4]) (sub := .leaf 4) (off := 4)
    (by simp [witnessCtxT, witnessCtx]) (by with_unfolding_all rfl) rfl
    (by simp [witnessCtxT, witnessCtx]) (by simp) (by simp [witnessCtxT, witnessCtx])
    (allocSize := 8) (align := 4) (by simp [ownLayout, witnessCtxT, witnessCtx])

/-- **Non-vacuity of the `Deref` refinement (`witness_trusted_deref_read`)**: every hypothesis of
`evalDerefPlaceRead_refines_evalOperand` holds in the witness frame (below-related slots, Anneal's
no-guess resolution of `*_1` agreeing with Trusted's borrow entry), so Trusted's
`Operand.copy (*_1)` reads `9`, exactly as Anneal does. -/
theorem witness_trusted_deref_read :
    evalOperand witnessLocalsT (.copy ⟨1, [.deref]⟩) [witnessEntry] [] emptyLayoutTable [] =
      .ok (.scalar ⟨9, 4⟩) witnessLocalsT :=
  evalDerefPlaceRead_refines_evalOperand (cx := witnessCtxT) (pty := ⟨false, 1⟩)
    (sz := 8) (rest := [])
    (by simp [witnessSlotsT, witnessLocalsT, SlotsRefine, SlotBelow]) rfl
    (by with_unfolding_all rfl) (by simp [witnessCtxT, witnessCtx]) witness_trusted_resolve
    (by simp [lookupBorrow, witnessEntry, witnessPtrT, ProvenancePtr.tag])
    (by simp [witnessEntry]) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    [] emptyLayoutTable []

/-- Non-empty `localDecls` for the witness frame: `_0 : (u32, u32)`, `_1 : *mut u32`. -/
def witnessLocalDecls : List LocalDecl :=
  [ { mutability := .mut, ty := { kind := .tuple [witnessU32.kind, witnessU32.kind], layoutIdx := 0 }, debugName := none }
  , { mutability := .mut, ty := { kind := .rawPtr .mut witnessU32.kind, layoutIdx := 0 }, debugName := none } ]

/-- **Non-vacuity of the typed `Deref` refinement (`witness_trusted_deref_read_typed`)**: every
hypothesis of `evalDerefPlaceRead_refines_evalOperand_typed` and
`evalDerefPlaceRead_refines_evalRvalue_typed` holds in the witness frame with the non-empty typed
declarations `witnessLocalDecls` (pointee `u32`: 4-byte scalar, offset `0`, aligned target `_0.1`,
no union, valid value), so Anneal's `evalDerefPlaceRead`, Trusted's typed `evalOperand` (through
`evalStackThinPtrTypedDerefRead`), and Trusted's typed `evalRvalue` all read `9` from `*_1`. -/
theorem witness_trusted_deref_read_typed :
    evalDerefPlaceRead witnessCtxT witnessSlotsT ⟨1, [.deref]⟩ = .ok (.scalar ⟨9, 4⟩) ∧
    evalOperand witnessLocalsT (.copy ⟨1, [.deref]⟩) [witnessEntry] [] emptyLayoutTable []
      witnessLocalDecls = .ok (.scalar ⟨9, 4⟩) witnessLocalsT ∧
    ∃ mem', evalRvalue witnessLocalsT (.use (.copy ⟨1, [.deref]⟩))
      { borrows := [witnessEntry], globals := [], callerLocals := [], activeProtectors := [] }
      witnessLocalDecls emptyLayoutTable = .ok (.scalar ⟨9, 4⟩) witnessLocalsT mem' := by
  have hRead : evalDerefPlaceRead witnessCtxT witnessSlotsT ⟨1, [.deref]⟩ =
      .ok (.scalar ⟨9, 4⟩) := by
    with_unfolding_all rfl
  have hRel : SlotsRefine SlotBelow witnessSlotsT witnessLocalsT := by
    simp [witnessSlotsT, witnessLocalsT, SlotsRefine, SlotBelow]
  have hPtr : readPlaceState witnessSlotsT ⟨1, []⟩ = .ok (.ptr witnessPtrT 8) := by
    with_unfolding_all rfl
  have hTy : witnessCtxT.ptrTyAt 1 [] = some ⟨false, 1⟩ := by simp [witnessCtxT, witnessCtx]
  have hEntry : lookupBorrow [witnessEntry] witnessPtrT.tag = some witnessEntry := by
    simp [lookupBorrow, witnessEntry, witnessPtrT, ProvenancePtr.tag]
  have hPerm : witnessEntry.perm ≠ .disabled := by simp [witnessEntry]
  have hDecls : witnessLocalDecls ≠ [] := by simp [witnessLocalDecls]
  have hPTy : placeTyResolved witnessLocalDecls emptyLayoutTable ⟨1, [.deref]⟩ =
      some witnessU32 := by with_unfolding_all rfl
  have hScalar : tyScalarBytes
      (resolveTyWithLocalDecls witnessLocalDecls emptyLayoutTable witnessU32) = some 4 := by
    with_unfolding_all rfl
  have hAlign : ∀ rootVal, get? witnessLocalsT witnessEntry.targetLocal = some (.init rootVal) →
      checkTargetPlaceAlign witnessLocalDecls emptyLayoutTable
        (some (resolveTyWithLocalDecls witnessLocalDecls emptyLayoutTable witnessU32))
        witnessEntry witnessPtrT (some rootVal) = true := by
    intro rootVal h
    cases h
    with_unfolding_all rfl
  have hNoUnion : placeTouchesUnion witnessLocalDecls emptyLayoutTable
      ⟨witnessEntry.targetLocal, witnessEntry.targetProjection⟩ = false := by
    with_unfolding_all rfl
  have hValid : validateValueForTy? emptyLayoutTable
      (some (resolveTyWithLocalDecls witnessLocalDecls emptyLayoutTable witnessU32))
      (.scalar ⟨9, 4⟩) = true := by with_unfolding_all rfl
  have hLoad : validateLoadedValue emptyLayoutTable witnessLocalDecls (.copy ⟨1, [.deref]⟩)
      (.scalar ⟨9, 4⟩) = true := by with_unfolding_all rfl
  refine ⟨hRead, ?_, ?_⟩
  · exact evalDerefPlaceRead_refines_evalOperand_typed hRel hPtr hTy witness_trusted_resolve
      hEntry hPerm hRead hDecls hPTy hScalar rfl rfl hAlign hNoUnion hValid [] []
  · exact evalDerefPlaceRead_refines_evalRvalue_typed hRel hPtr hTy witness_trusted_resolve
      hEntry hPerm hRead hDecls hPTy hScalar rfl rfl hAlign hNoUnion hValid hLoad

/-- Witness type fingerprint mapping: type `1` (`u32`) has fingerprint `1`, type `2`
(`i32`) has fingerprint `2`. -/
def witnessTagFp (t : Nat) : Nat :=
  if t = 1 then 1 else 2

/-- **Witness: type-fingerprinted tag disambiguates same-offset candidates in read mode
(`witness_tag_disambiguates_read`)** and **in whole-union-field write mode
(`witness_tag_disambiguates_union_write`)**, while a **cast-pointer fingerprint mismatch rejects
the ambiguous offset (`witness_tag_cast_mismatch_rejects`)**. -/
theorem witness_tag_disambiguates_and_rejects_mismatch :
    let cands : List (List ProjectionElem) := [[.field 0 witnessU32], [.field 1 witnessU32]]
    let cons := fun (q : List ProjectionElem) => match q with | [.field 0 _] => true | _ => false
    let consOw := fun (_ : List ProjectionElem) => true
    let readable := fun (_ : List ProjectionElem) => true
    decodeSubplaceTag witnessTagFp (encodeSubplaceTag witnessTagFp 1 0) 1 = some 0 ∧
    decodeSubplaceTag witnessTagFp (encodeSubplaceTag witnessTagFp 1 1) 1 = some 1 ∧
    decodeSubplaceTag witnessTagFp (encodeSubplaceTag witnessTagFp 1 1) 2 = none ∧
    selectSubplaceCandidate cands cons consOw (some 0) false readable false =
      some [.field 0 witnessU32] ∧
    selectSubplaceCandidate cands cons consOw (some 1) false readable true =
      some [.field 1 witnessU32] ∧
    selectSubplaceCandidate cands (fun _ => true) consOw none false readable false =
      none := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_⟩ <;> with_unfolding_all rfl

/-- **Witness: `count = 2` array-window `CopyNonOverlapping` (`witness_window_copy`)**: copying the
2-element window `_0[1..3]` (`[20, 30]`) of `_0 : [u32; 4] = [10, 20, 30, 40]` into `_1[0..2]` of
`_1 : [u32; 4] = [1, 2, 3, 4]` produces `_1 = [20, 30, 3, 4]`. -/
theorem witness_window_copy :
    let slots : List LocalSlotState :=
      [ .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩])
      , .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]) ]
    let resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem) := fun p _ =>
      if p.addr = 0x1004 then .ok (0, [.constantIndex 1 4 false])
      else if p.addr = 0x2000 then .ok (1, [.constantIndex 0 4 false])
      else .error .unsupported
    evalCopyNonOverlappingSubplace (fun _ _ _ => none) (fun _ => witnessU32) false 64 slots resolve
        ⟨0x1004, some (1, 0)⟩ ⟨0x2000, some (2, 0)⟩ 2 4 4 =
      some [ .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩])
           , .init (.aggregate 0 [.scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]) ] := by
  with_unfolding_all rfl

/-- **Non-vacuity of the typed `Deref` write refinement (`witness_trusted_deref_write_typed`)**:
every hypothesis of `evalDerefPlaceWrite_refines_writePlaceValue_typed` holds in the witness frame
with the non-empty typed declarations `witnessLocalDecls`, so Anneal's `evalDerefPlaceWrite` and
Trusted's typed `writePlaceValue` (through `writeStackThinPtrTypedDeref`) both write `5` into
`_0.1` while preserving `_0.0 = 7`. -/
theorem witness_trusted_deref_write_typed :
    let slots' : List LocalSlotState :=
      [.init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨5, 4⟩]), .init (.ptr witnessPtrT 8)]
    let locals' : List LocalSlot :=
      [.init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨5, 4⟩]), .init (.ptr witnessPtrT 8)]
    evalDerefPlaceWrite (fun _ _ _ => none) (fun _ => witnessU32) witnessCtxT witnessSlotsT
        ⟨1, [.deref]⟩ (.scalar ⟨5, 4⟩) = .ok slots' ∧
    writePlaceValue witnessLocalsT [witnessEntry] ⟨1, [.deref]⟩ (.scalar ⟨5, 4⟩)
        witnessLocalDecls emptyLayoutTable = .ok locals' ∧
    SlotsRefine SlotBelow slots' locals' := by
  have hW : evalDerefPlaceWrite (fun _ _ _ => none) (fun _ => witnessU32) witnessCtxT witnessSlotsT
      ⟨1, [.deref]⟩ (.scalar ⟨5, 4⟩) =
      .ok [.init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨5, 4⟩]), .init (.ptr witnessPtrT 8)] := by
    with_unfolding_all rfl
  have hRel : SlotsRefine SlotBelow witnessSlotsT witnessLocalsT := by
    simp [witnessSlotsT, witnessLocalsT, SlotsRefine, SlotBelow]
  have hRef : evalSubplaceRef witnessCtxT witnessSlotsT 0 [.field 1 witnessU32] 0 =
      .ok ⟨0x1004, some (1, 0)⟩ := by with_unfolding_all rfl
  have hPtrOf : witnessCtxT.ptrOf witnessPtrT = ⟨0x1004, some (1, 0)⟩ := by
    simp [witnessCtxT, witnessPtrT]
  have hResW : resolveSyntheticSubplace witnessCtxT witnessSlotsT (witnessCtxT.ptrOf witnessPtrT)
      ⟨false, 1⟩ true = .ok (witnessEntry.targetLocal, witnessEntry.targetProjection) := by
    rw [hPtrOf]
    exact resolveSyntheticSubplace_evalSubplaceRef witnessCtxT_wf hRef true
      (tl := ⟨4, 4, 4, true, true⟩) (by simp [witnessCtxT, witnessCtx]) (by decide) (by decide)
      (by simp) (lay := .struct 8 [0, 4] [.leaf 4, .leaf 4]) (sub := .leaf 4) (off := 4)
      (by simp [witnessCtxT, witnessCtx]) (by with_unfolding_all rfl) rfl
      (by simp [witnessCtxT, witnessCtx]) (by simp) (by simp [witnessCtxT, witnessCtx])
      (allocSize := 8) (align := 4) (by simp [ownLayout, witnessCtxT, witnessCtx])
  obtain ⟨locals', hWP, hRel'⟩ := evalDerefPlaceWrite_refines_writePlaceValue_typed witnessCtxT_wf
    hRel (pty := ⟨false, 1⟩) (borrows := [witnessEntry]) (entry := witnessEntry)
    (localDecls := witnessLocalDecls) (layouts := emptyLayoutTable)
    (root := .aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩]) (oldSc := ⟨9, 4⟩) (pTy := witnessU32)
    (by with_unfolding_all rfl) (by simp [witnessCtxT, witnessCtx])
    hResW
    (by with_unfolding_all rfl)
    (Or.inl rfl) rfl (by with_unfolding_all rfl) hW (by decide)
    (by with_unfolding_all rfl) (by decide) rfl rfl
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  have hWP' : writePlaceValue witnessLocalsT [witnessEntry] ⟨1, [.deref]⟩ (.scalar ⟨5, 4⟩)
      witnessLocalDecls emptyLayoutTable =
      .ok [.init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨5, 4⟩]), .init (.ptr witnessPtrT 8)] := by
    with_unfolding_all rfl
  rw [hWP'] at hWP
  injection hWP with hEq
  subst hEq
  exact ⟨hW, hWP', hRel'⟩

/-- **Non-vacuity of the `count ≥ 2` array-window `CopyNonOverlapping` refinement
(`witness_trusted_window_copy`)**: every hypothesis of `evalCopyNonOverlappingSubplace_window_refines`
holds on the 4-element `u32` arrays `_0 = [10, 20, 30, 40]` and `_1 = [1, 2, 3, 4]` for `count = 2`
(`_0[1..3]` into `_1[0..2]`), so Anneal's `evalCopyNonOverlappingSubplace` and Trusted's
`evalCopyNonOverlappingPermOk` both produce `_1 = [20, 30, 3, 4]`. -/
theorem witness_trusted_window_copy (s : MachineState) (srcOp dstOp : Operand) :
    let srcElems : List Value := [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩]
    let dstElems : List Value := [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]
    let newDstElems : List Value := [.scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]
    let slots' : List LocalSlotState := [.init (.aggregate 0 srcElems), .init (.aggregate 0 newDstElems)]
    let locals₃ : List LocalSlot := [.init (.aggregate 0 srcElems), .init (.aggregate 0 dstElems)]
    let locals₄ : List LocalSlot := [.init (.aggregate 0 srcElems), .init (.aggregate 0 newDstElems)]
    let srcPtr : ProvenancePtr := { allocId := 1, offsetBytes := 1 }
    let dstPtr : ProvenancePtr := { allocId := 2, offsetBytes := 0 }
    let srcEntry : BorrowEntry := { tag := 1, targetLocal := 0, targetProjection := [], perm := .active }
    let dstEntry : BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := .active }
    evalCopyNonOverlappingPermOk s srcOp dstOp [] emptyLayoutTable srcPtr dstPtr srcEntry dstEntry
        2 locals₃ =
      .step (advanceStmt s locals₄
        { s.memory with borrows := invalidateConflictingBorrows s.memory.borrows 1 (some 2) }) ∧
    SlotsRefine SlotBelow slots' locals₄ := by
  exact evalCopyNonOverlappingSubplace_window_refines
    (arityOf := fun _ _ _ => none) (rootTyOf := fun _ => witnessU32) (ts := false) (ptrBits := 64)
    (slots := [ .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩])
              , .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]) ])
    (locals₃ := [ .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩])
                , .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]) ])
    (resolve := fun p _ =>
      if p.addr = 0x1004 then .ok (0, [.constantIndex 1 4 false])
      else if p.addr = 0x2000 then .ok (1, [.constantIndex 0 4 false])
      else .error .unsupported)
    (src := ⟨0x1004, some (1, 0)⟩) (dst := ⟨0x2000, some (2, 0)⟩)
    (by simp [SlotsRefine, SlotBelow]) (by decide) (by decide) rfl rfl (by decide) rfl rfl rfl rfl
    witness_window_copy s srcOp dstOp [] emptyLayoutTable
    { allocId := 1, offsetBytes := 1 } { allocId := 2, offsetBytes := 0 }
    { tag := 1, targetLocal := 0, targetProjection := [], perm := .active }
    { tag := 2, targetLocal := 1, targetProjection := [], perm := .active }
    (by decide) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl rfl rfl rfl (fun _ _ _ h => by nomatch h)

/-- **Array-window (`count ≥ 2`) `CopyNonOverlapping` refines Trusted's `evalCopyNonOverlappingPermOk`
for both cross-local (`sl ≠ dl`) and same-local disjoint (`sl = dl`, `s0 + count ≤ d0 ∨ d0 + count ≤ s0`)
copies (`evalCopyNonOverlappingSubplace_window_same_or_disjoint_refines`)**: on below-related frames,
when Anneal copies a contiguous window of `count ≥ 2` elements (`elemSize > 0`) from an initialized
array local `sl` at index `s0` into an initialized array local `dl` at index `d0` (`s0 + count ≤ sLen`,
`d0 + count ≤ dLen`), and either the copy is cross-local (`sl ≠ dl`) or the index windows
`[s0, s0 + count)` and `[d0, d0 + count)` are disjoint (`s0 + count ≤ d0 ∨ d0 + count ≤ s0`,
covering Trusted's `sameContainer` disjointness branch when `sl = dl`), Trusted's
`evalCopyNonOverlappingPermOk` steps with the exact same spliced array
`spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems` and the updated frames stay
related by `SlotsRefine SlotBelow`. -/
theorem evalCopyNonOverlappingSubplace_window_same_or_disjoint_refines
    {arityOf : Ty → VariantIdx → Bool → Option Nat} {rootTyOf : Nat → Ty} {ts : Bool}
    {ptrBits : Nat} {slots slots' : List LocalSlotState} {locals₃ : List LocalSlot}
    {resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem)} {src dst : SynPtr}
    {count elemSize elemAlign sl dl s0 sLen d0 dLen : Nat} {srcElems dstElems : List Value}
    (hRel : SlotsRefine SlotBelow slots locals₃)
    (hCount : 2 ≤ count) (hElemSz : 0 < elemSize)
    (hSrcR : resolve src false = .ok (sl, [.constantIndex s0 sLen false]))
    (hDstR : resolve dst true = .ok (dl, [.constantIndex d0 dLen false]))
    (hSrcRoot : slots[sl]? = some (.init (.aggregate 0 srcElems)))
    (hDstRoot : slots[dl]? = some (.init (.aggregate 0 dstElems)))
    (hSLen : srcElems.length = sLen)
    (hDLen : dstElems.length = dLen)
    (h : evalCopyNonOverlappingSubplace arityOf rootTyOf ts ptrBits slots resolve src dst count
      elemSize elemAlign = some slots')
    (s : MachineState) (srcOp dstOp : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (hTagNe : srcPtr.tag ≠ dstPtr.tag)
    (hDisj : sl ≠ dl ∨ s0 + count ≤ d0 ∨ d0 + count ≤ s0)
    (hSrcEntry : srcEntry.targetLocal = sl ∧ srcEntry.targetProjection = [])
    (hDstEntry : dstEntry.targetLocal = dl ∧ dstEntry.targetProjection = [])
    (hSrcOff : srcPtr.offsetBytes = s0)
    (hDstOff : dstPtr.offsetBytes = d0)
    (hSrcU : resolveUnionEndpoint? localDecls layouts locals₃ srcEntry = none)
    (hDstU : resolveUnionEndpoint? localDecls layouts locals₃ dstEntry = none)
    (hNotAdt : ∀ fn args idx, placeTy localDecls layouts ⟨dl, []⟩ ≠ some { kind := .adt fn args, layoutIdx := idx }) :
    let newDstVal := Value.aggregate 0 (spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems)
    evalCopyNonOverlappingPermOk s srcOp dstOp localDecls layouts srcPtr dstPtr srcEntry dstEntry
        count locals₃ =
      .step (advanceStmt s (locals₃.set dl (.init newDstVal))
        { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows dl (some dstPtr.tag) }) ∧
    SlotsRefine SlotBelow slots' (locals₃.set dl (.init newDstVal)) := by
  unfold evalCopyNonOverlappingSubplace at h
  split at h
  · nomatch h
  split at h
  · omega
  split at h
  · nomatch h
  rw [hSrcR, hDstR] at h
  have hNot1 : ¬ (count = 1 ∨ count * elemSize = 0) := by
    rintro (rfl | hMul)
    · omega
    · exact absurd hMul (Nat.ne_of_gt (Nat.mul_pos (by omega) hElemSz))
  have hSplitS : splitLastElem [.constantIndex s0 sLen false] = some ([], s0, sLen) := rfl
  have hSplitD : splitLastElem [.constantIndex d0 dLen false] = some ([], d0, dLen) := rfl
  simp only [hNot1, ↓reduceIte, hSplitS, hSplitD] at h
  split at h
  · rename_i hBounds
    obtain ⟨hSBound, hDBound⟩ := hBounds
    have hSrcRead : readPlaceState slots ⟨sl, [.subslice s0 (s0 + count) false]⟩ =
        .ok (.aggregate 0 ((srcElems.drop s0).take count)) := by
      have hSub : extractSubslice srcElems s0 (s0 + count) false =
          some ((srcElems.drop s0).take count) := by
        apply (extractSubslice_eq_some_iff srcElems s0 (s0 + count) false _).mpr
        simp [subsliceEndIdx, hSLen, hSBound]
      simp [readPlaceState, projectionHasDeref, get?_eq_getElem?, hSrcRoot, evalValueProjRead, hSub]
    simp only [List.nil_append] at h
    rw [hSrcRead] at h
    simp only at h
    have hSpliceEq : spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems =
        dstElems.take d0 ++ ((srcElems.drop s0).take count ++ dstElems.drop (d0 + count)) := by
      rw [spliceValues_eq_take_append_drop, takeValues_eq_take, dropValues_eq_drop]
      have hTakeLen : ((srcElems.drop s0).take count).length = count := by
        rw [List.length_take, List.length_drop, hSLen]
        omega
      rw [hTakeLen]
    have hSlots' : slots' =
        slots.set dl (.init (.aggregate 0
          (spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems))) := by
      by_cases hWhole : d0 = 0 ∧ count = dLen
      · obtain ⟨rfl, rfl⟩ := hWhole
        simp only [and_self, ↓reduceIte] at h
        have hWS : writePlaceState arityOf slots ⟨dl, []⟩ (rootTyOf dl)
            (.aggregate 0 ((srcElems.drop s0).take count)) =
            .ok (slots.set dl (.init (.aggregate 0 ((srcElems.drop s0).take count)))) := by
          simp [writePlaceState, projectionHasDeref, get?_eq_getElem?, hDstRoot, writeToFieldSlot,
            fieldSlotToLocalSlotState]
        rw [hWS] at h
        simp only [Option.some.injEq] at h
        rw [← h, hSpliceEq]
        simp [← hDLen]
      · simp only [hWhole, ↓reduceIte] at h
        have hExtD : extractSubslice dstElems d0 (d0 + count) false =
            some ((dstElems.drop d0).take count) := by
          apply (extractSubslice_eq_some_iff dstElems d0 (d0 + count) false _).mpr
          simp [subsliceEndIdx, hDLen, hDBound]
        have hRep : replaceSubslice dstElems d0 (d0 + count) false ((srcElems.drop s0).take count) =
            some (dstElems.take d0 ++ ((srcElems.drop s0).take count ++ dstElems.drop (d0 + count))) := by
          apply (replaceSubslice_eq_some_iff dstElems d0 (d0 + count) false _ _).mpr
          refine ⟨by omega, by simp [subsliceEndIdx], ?_, rfl⟩
          simp [subsliceEndIdx, List.length_take, List.length_drop, hSLen]; omega
        have hWS : writePlaceState arityOf slots ⟨dl, [.subslice d0 (d0 + count) false]⟩ (rootTyOf dl)
            (.aggregate 0 ((srcElems.drop s0).take count)) =
            .ok (slots.set dl (.init (.aggregate 0
              (dstElems.take d0 ++ ((srcElems.drop s0).take count ++ dstElems.drop (d0 + count)))))) := by
          simp [writePlaceState, projectionHasDeref, get?_eq_getElem?, hDstRoot, writeToFieldSlot,
            evalValueProjWrite, hExtD, hRep, fieldSlotToLocalSlotState]
        rw [hWS] at h
        simp only [Option.some.injEq] at h
        rw [← h, hSpliceEq]
    subst hSlots'
    have hTSrc : locals₃[sl]? = some (.init (.aggregate 0 srcElems)) := by
      rcases SlotsRefine.get?_rel sl hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, hAT⟩
      · simp only [get?_eq_getElem?] at hA; rw [hA] at hSrcRoot; nomatch hSrcRoot
      · simp only [get?_eq_getElem?] at hA hT
        rw [hA] at hSrcRoot; cases hSrcRoot
        cases t with
        | init w => have hvw : Value.aggregate 0 srcElems = w := hAT; subst hvw; exact hT
        | _ => simp [SlotBelow] at hAT
    have hTDst : locals₃[dl]? = some (.init (.aggregate 0 dstElems)) := by
      rcases SlotsRefine.get?_rel dl hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, hAT⟩
      · simp only [get?_eq_getElem?] at hA; rw [hA] at hDstRoot; nomatch hDstRoot
      · simp only [get?_eq_getElem?] at hA hT
        rw [hA] at hDstRoot; cases hDstRoot
        cases t with
        | init w => have hvw : Value.aggregate 0 dstElems = w := hAT; subst hvw; exact hT
        | _ => simp [SlotBelow] at hAT
    have hLtD3 : dl < locals₃.length := (List.getElem?_eq_some_iff.mp hTDst).1
    refine ⟨?_, SlotsRefine.set (a := .init _) (t := .init _) rfl dl hRel⟩
    unfold evalCopyNonOverlappingPermOk
    have hBeqN1 : Nat.beq count 1 = false :=
      ((beq_cases count 1).resolve_left (fun ⟨_, hEq⟩ => by omega)).1
    have hBeqTag : Nat.beq srcPtr.tag dstPtr.tag = false :=
      ((beq_cases srcPtr.tag dstPtr.tag).resolve_left (fun ⟨_, hEq⟩ => hTagNe hEq)).1
    have hAdtFalse : (match placeTy localDecls layouts ⟨dl, []⟩ with
        | some { kind := .adt _ _, .. } => true
        | _ => false) = false := by
      cases hPT : placeTy localDecls layouts ⟨dl, []⟩ with
      | none => rfl
      | some ty =>
        rcases ty with ⟨k, lidx⟩
        cases k with
        | adt fn args => exact absurd hPT (hNotAdt fn args lidx)
        | _ => rfl
    have hBleS : Nat.ble (Nat.add s0 count) (length srcElems) = true := by
      rw [length_eq_list_length, hSLen]; exact Nat.ble_eq.mpr hSBound
    have hBleD : Nat.ble (Nat.add d0 count) (length dstElems) = true := by
      rw [length_eq_list_length, hDLen]; exact Nat.ble_eq.mpr hDBound
    have hSetD : set? locals₃ dl
        (.init (.aggregate 0 (spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems))) =
        some (locals₃.set dl
          (.init (.aggregate 0 (spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems)))) :=
      set?_eq_some_iff.mpr ⟨hLtD3, rfl⟩
    have hWPV0 : writePlaceValue locals₃ s.memory.borrows ⟨dl, []⟩
        (.aggregate 0 (spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems)) =
        .ok (locals₃.set dl
          (.init (.aggregate 0 (spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems)))) := by
      unfold writePlaceValue
      simp only [get?_eq_getElem?, hTDst, hSetD]
    let _ := hAdtFalse
    simp only [hSrcU, hDstU, hBeqN1, Bool.false_and, hSrcEntry.1, hSrcEntry.2, hDstEntry.1,
      hDstEntry.2, get?_eq_getElem?, hTSrc, hTDst, readProjectedValue, hSrcOff, hDstOff,
      Bool.not_false, hBleS, hBleD, Bool.and_self, hBeqTag,
      commitCopyDstPlaceWrite, hWPV0]
    have hPO : projectionsOverlap [] [] = true := rfl
    rcases hDisj with hNe | hSD | hDS
    · have hBLoc : Nat.beq sl dl = false :=
        ((beq_cases sl dl).resolve_left (fun ⟨_, hEq⟩ => hNe hEq)).1
      simp [hPO, hBLoc]
    · have hBleSD : (s0 + count).ble d0 = true := Nat.ble_eq.mpr hSD
      cases sl.beq dl <;> simp [hPO, hBleSD]
    · have hBleDS : (d0 + count).ble s0 = true := Nat.ble_eq.mpr hDS
      cases sl.beq dl <;> simp [hPO, hBleDS]
  · nomatch h

/-- **Statement-level array-window (`count ≥ 2`) `CopyNonOverlapping` refinement for cross-local or
same-local disjoint copies (`evalStmt_copyNonOverlapping_window_same_or_disjoint_refines`)**: lifts
`evalCopyNonOverlappingSubplace_window_same_or_disjoint_refines` through Trusted's `evalStmt` on
`copy_nonoverlapping(srcOp, dstOp, countOp)`. -/
theorem evalStmt_copyNonOverlapping_window_same_or_disjoint_refines
    {arityOf : Ty → VariantIdx → Bool → Option Nat} {rootTyOf : Nat → Ty} {ts : Bool}
    {ptrBits : Nat} {slots slots' : List LocalSlotState}
    {resolve : SynPtr → Bool → Except DerefErr (Nat × List ProjectionElem)} {src dst : SynPtr}
    {count elemSize elemAlign sl dl s0 sLen d0 dLen : Nat} {srcElems dstElems : List Value}
    (s : MachineState)
    (hRel : SlotsRefine SlotBelow slots s.frame.locals)
    (hCount : 2 ≤ count) (hElemSz : 0 < elemSize)
    (hSrcR : resolve src false = .ok (sl, [.constantIndex s0 sLen false]))
    (hDstR : resolve dst true = .ok (dl, [.constantIndex d0 dLen false]))
    (hSrcRoot : slots[sl]? = some (.init (.aggregate 0 srcElems)))
    (hDstRoot : slots[dl]? = some (.init (.aggregate 0 dstElems)))
    (hSLen : srcElems.length = sLen)
    (hDLen : dstElems.length = dLen)
    (h : evalCopyNonOverlappingSubplace arityOf rootTyOf ts ptrBits slots resolve src dst count
      elemSize elemAlign = some slots')
    (srcOp dstOp countOp : Operand) (span : String) (localDecls : List LocalDecl)
    (layouts : LayoutTable) {srcPtr dstPtr : ProvenancePtr} {srcSz dstSz : Nat}
    {countSc : ScalarInt} {srcEntry dstEntry : BorrowEntry}
    (hSrcOp : evalOperand s.frame.locals srcOp s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls = .ok (.ptr srcPtr srcSz) s.frame.locals)
    (hDstOp : evalOperand s.frame.locals dstOp s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls = .ok (.ptr dstPtr dstSz) s.frame.locals)
    (hCnt : evalOperand s.frame.locals countOp s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls = .ok (.scalar countSc) s.frame.locals)
    (hCountBits : countSc.bits = count)
    (hSrcE : lookupBorrow s.memory.borrows srcPtr.tag = some srcEntry)
    (hDstE : lookupBorrow s.memory.borrows dstPtr.tag = some dstEntry)
    (hSrcP : srcEntry.perm ≠ .disabled)
    (hDstP : dstEntry.perm = .active ∨ dstEntry.perm = .reserved)
    (hTagNe : srcPtr.tag ≠ dstPtr.tag)
    (hDisj : sl ≠ dl ∨ s0 + count ≤ d0 ∨ d0 + count ≤ s0)
    (hSrcEntry : srcEntry.targetLocal = sl ∧ srcEntry.targetProjection = [])
    (hDstEntry : dstEntry.targetLocal = dl ∧ dstEntry.targetProjection = [])
    (hSrcOff : srcPtr.offsetBytes = s0)
    (hDstOff : dstPtr.offsetBytes = d0)
    (hSrcU : resolveUnionEndpoint? localDecls layouts s.frame.locals srcEntry = none)
    (hDstU : resolveUnionEndpoint? localDecls layouts s.frame.locals dstEntry = none)
    (hNotAdt : ∀ fn args idx, placeTy localDecls layouts ⟨dl, []⟩ ≠ some { kind := .adt fn args, layoutIdx := idx }) :
    let newDstVal := Value.aggregate 0 (spliceValues (takeValues count (dropValues s0 srcElems)) d0 dstElems)
    evalStmt s ⟨.intrinsic (.copyNonOverlapping srcOp dstOp countOp), span⟩ localDecls layouts =
      .step (advanceStmt s (s.frame.locals.set dl (.init newDstVal))
        { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows dl (some dstPtr.tag) }) ∧
    SlotsRefine SlotBelow slots' (s.frame.locals.set dl (.init newDstVal)) := by
  have hPermOk : evalCopyNonOverlappingWithCount s srcOp dstOp localDecls layouts
      (.ptr srcPtr srcSz) (.ptr dstPtr dstSz) count s.frame.locals =
      evalCopyNonOverlappingPermOk s srcOp dstOp localDecls layouts srcPtr dstPtr srcEntry dstEntry
        count s.frame.locals := by
    unfold evalCopyNonOverlappingWithCount
    have hCntNe0 : Nat.beq count 0 = false :=
      ((beq_cases count 0).resolve_left (fun ⟨_, hEq⟩ => by omega)).1
    simp only [hCntNe0, hSrcE, hDstE]
    cases hs : srcEntry.perm with
    | disabled => exact absurd hs hSrcP
    | _ => rcases hDstP with hd | hd <;> simp [hd]
  simp only [evalStmt, evalCopyNonOverlapping, hSrcOp, hDstOp, hCnt, hCountBits, hPermOk]
  exact evalCopyNonOverlappingSubplace_window_same_or_disjoint_refines hRel hCount hElemSz hSrcR
    hDstR hSrcRoot hDstRoot hSLen hDLen h s srcOp dstOp localDecls layouts srcPtr dstPtr
    srcEntry dstEntry hTagNe hDisj hSrcEntry hDstEntry hSrcOff hDstOff hSrcU hDstU hNotAdt

/-- Whether a `RigidTy` is a primitive scalar kind (`bool`, `char`, `int`, `uint`, `float`). -/
def isScalarRigidTy : RigidTy → Bool
  | .bool | .char | .int _ | .uint _ | .float _ => true
  | _ => false

/-- **Projected typed `Deref` reads refine Trusted's typed `evalOperand`
(`evalDerefPlaceRead_refines_evalOperand_typed_proj`)**: with non-empty `localDecls` and a
non-empty post-deref projection suffix `rHead :: rTail` (`projectionHasDeref (rHead :: rTail) = false`),
Trusted reads `Operand.copy (*_p).(rHead :: rTail)` through `evalStackThinPtrTypedDerefRead` and
`resolveStackThinPtrTargetProjWithResidual?`. When `_p` resolves to `(entry.targetLocal, entry.targetProjection)`
and `resolveStackThinPtrTargetProjWithResidual?` resolves `(entry, pv, rHead :: rTail)` to
`(entry.targetProjection ++ (rHead :: rTail), 0)` at residual byte offset `0`, Anneal's read of
`.scalar sc` from `⟨p, .deref :: rHead :: rTail⟩` is matched by Trusted's typed `evalOperand`
returning `.ok (.scalar sc) locals`. -/
theorem evalDerefPlaceRead_refines_evalOperand_typed_proj {cx : SubplaceCtx}
    {slots : List LocalSlotState} {locals : List LocalSlot} {p : Nat}
    {rHead : ProjectionElem} {rTail : List ProjectionElem} {sc : ScalarInt}
    {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy} {borrows : List BorrowEntry}
    {entry : BorrowEntry} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {ptTy accTy : Ty} {n : Nat}
    (hRel : SlotsRefine SlotBelow slots locals)
    (hRest : projectionHasDeref (rHead :: rTail) = false)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz))
    (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty false =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow borrows pv.tag = some entry)
    (hPerm : entry.perm ≠ .disabled)
    (hRead : evalDerefPlaceRead cx slots ⟨p, .deref :: rHead :: rTail⟩ = .ok (.scalar sc))
    (hDecls : localDecls ≠ [])
    (hPtTy : placeTyResolved localDecls layouts ⟨p, [.deref]⟩ = some ptTy)
    (hAccTy : placeTyResolved localDecls layouts ⟨p, .deref :: rHead :: rTail⟩ = some accTy)
    (hPtNotScalar : isScalarRigidTy ptTy.kind = false)
    (hAccNotNever : (resolveTyWithLocalDecls localDecls layouts accTy).kind ≠ .never)
    (hAccNotUnitTuple : (resolveTyWithLocalDecls localDecls layouts accTy).kind ≠ .tuple [])
    (hAccNotFnDef : ∀ fn args, (resolveTyWithLocalDecls localDecls layouts accTy).kind ≠ .fnDef fn args)
    (hScalar : tyScalarBytes (resolveTyWithLocalDecls localDecls layouts accTy) = some n)
    (hWidth : n = sc.sizeBytes)
    (hDerefAlign : checkDerefAlign localDecls layouts
      (some (resolveTyWithLocalDecls localDecls layouts ptTy)) pv.offsetBytes = true)
    (hAlign : ∀ rootVal, get? locals entry.targetLocal = some (.init rootVal) →
      checkTargetPlaceAlign localDecls layouts
        (some (resolveTyWithLocalDecls localDecls layouts ptTy)) entry pv (some rootVal) = true)
    (hResT : ∀ rootVal, get? locals entry.targetLocal = some (.init rootVal) →
      resolveStackThinPtrTargetProjWithResidual? locals rootVal entry pv (rHead :: rTail)
        localDecls layouts (some (resolveTyWithLocalDecls localDecls layouts ptTy)) none =
        some (entry.targetProjection ++ (rHead :: rTail), 0))
    (hNoUnion : placeTouchesUnion localDecls layouts
      ⟨entry.targetLocal, entry.targetProjection ++ (rHead :: rTail)⟩ = false)
    (hValid : validateValueForTy? layouts
      (some (resolveTyWithLocalDecls localDecls layouts accTy)) (.scalar sc) = true)
    (globals : List CapturedAllocation) (callerLocals : List LocalSlot) :
    evalOperand locals (.copy ⟨p, .deref :: rHead :: rTail⟩) borrows globals layouts
        callerLocals localDecls =
      .ok (.scalar sc) locals := by
  obtain ⟨stp, hStp, hLiveP⟩ := readPlaceState_ok_live hPtr
  rw [evalDerefPlaceRead_deref hStp hLiveP hPtr hTy hRes hRest] at hRead
  have hTR : readPlaceState slots ⟨entry.targetLocal, entry.targetProjection ++ (rHead :: rTail)⟩ =
      .ok (.scalar sc) := by
    cases hRS : readPlaceState slots ⟨entry.targetLocal, entry.targetProjection ++ (rHead :: rTail)⟩ with
    | ok w => rw [hRS] at hRead; simp only [liftRead, Except.ok.injEq] at hRead; rw [hRead]
    | ub => rw [hRS] at hRead; nomatch hRead
    | unsupported => rw [hRS] at hRead; nomatch hRead
  obtain ⟨rootVal, ht, hr⟩ := readPlaceState_below_refines hRel hTR
  obtain ⟨rootP, hp, hrp⟩ := readPlaceState_below_refines hRel hPtr
  simp only [readProjectedValue] at hrp
  cases hrp
  obtain ⟨d0, ds, hcons⟩ : ∃ d0 ds, localDecls = d0 :: ds := by
    cases h : localDecls with
    | nil => exact absurd h hDecls
    | cons d0 ds => exact ⟨d0, ds, rfl⟩
  have hAl := hAlign rootVal ht
  have hRT := hResT rootVal ht
  have hReadForLocal : readProjectedForLocal locals localDecls layouts entry.targetLocal rootVal
      (entry.targetProjection ++ (rHead :: rTail)) = .ok (.scalar sc) := by
    cases hFull : entry.targetProjection ++ (rHead :: rTail) with
    | nil =>
      have := List.append_eq_nil_iff.mp hFull
      nomatch this.2
    | cons fh ft =>
      rw [hFull] at hr hNoUnion
      simp only [readProjectedForLocal, hNoUnion, hr]
  have hSynthFalse : evalStackThinPtrTypedDerefRead.match_1 (fun _ _ => Bool)
      (stripTransparentProjections (rHead :: rTail)) (some ptTy)
      (fun _ _ _ _ => true) (fun _ _ _ _ => true) (fun _ _ _ _ _ => true)
      (fun _ _ _ _ _ => true) (fun _ _ _ _ _ => true) (fun _ _ => false) = false := by
    rcases ptTy with ⟨k, lidx⟩
    cases k <;> try simp [isScalarRigidTy] at hPtNotScalar
    all_goals cases stripTransparentProjections (rHead :: rTail) with
      | nil => rfl
      | cons h t => cases h <;> rfl
  unfold evalOperand
  dsimp only
  rw [hp]
  dsimp only
  rw [hcons]
  dsimp only
  rw [← hcons, hEntry]
  dsimp only
  cases hpe : entry.perm with
  | disabled => exact absurd hpe hPerm
  | _ =>
    dsimp only
    rw [ht]
    dsimp only
    unfold evalStackThinPtrTypedDerefRead
    rw [hPtTy, hAccTy, hSynthFalse]
    dsimp only
    rw [hDerefAlign, hAl]
    simp only [Bool.and_self]
    rw [hcons]
    dsimp only
    rw [← hcons, hRT]
    dsimp only
    rw [hReadForLocal]
    dsimp only
    cases hKind : (resolveTyWithLocalDecls localDecls layouts accTy).kind with
    | never => exact absurd hKind hAccNotNever
    | tuple elems =>
      cases elems with
      | nil => exact absurd hKind hAccNotUnitTuple
      | cons e es =>
        simp [hScalar, hWidth, hValid]
    | fnDef fn args => exact absurd hKind (hAccNotFnDef fn args)
    | _ =>
      simp [hScalar, hWidth, hValid]

/-- **Projected typed `Deref` reads refine Trusted's typed `evalRvalue`
(`evalDerefPlaceRead_refines_evalRvalue_typed_proj`)**: lifts
`evalDerefPlaceRead_refines_evalOperand_typed_proj` through `evalRvalue` on
`.use (.copy ⟨p, .deref :: rHead :: rTail⟩)`. -/
theorem evalDerefPlaceRead_refines_evalRvalue_typed_proj {cx : SubplaceCtx}
    {slots : List LocalSlotState} {locals : List LocalSlot} {p : Nat}
    {rHead : ProjectionElem} {rTail : List ProjectionElem} {sc : ScalarInt}
    {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy} {mem : Memory}
    {entry : BorrowEntry} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {ptTy accTy : Ty} {n : Nat}
    (hRel : SlotsRefine SlotBelow slots locals)
    (hRest : projectionHasDeref (rHead :: rTail) = false)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz))
    (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty false =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow mem.borrows pv.tag = some entry)
    (hPerm : entry.perm ≠ .disabled)
    (hRead : evalDerefPlaceRead cx slots ⟨p, .deref :: rHead :: rTail⟩ = .ok (.scalar sc))
    (hDecls : localDecls ≠ [])
    (hPtTy : placeTyResolved localDecls layouts ⟨p, [.deref]⟩ = some ptTy)
    (hAccTy : placeTyResolved localDecls layouts ⟨p, .deref :: rHead :: rTail⟩ = some accTy)
    (hPtNotScalar : isScalarRigidTy ptTy.kind = false)
    (hAccNotNever : (resolveTyWithLocalDecls localDecls layouts accTy).kind ≠ .never)
    (hAccNotUnitTuple : (resolveTyWithLocalDecls localDecls layouts accTy).kind ≠ .tuple [])
    (hAccNotFnDef : ∀ fn args, (resolveTyWithLocalDecls localDecls layouts accTy).kind ≠ .fnDef fn args)
    (hScalar : tyScalarBytes (resolveTyWithLocalDecls localDecls layouts accTy) = some n)
    (hWidth : n = sc.sizeBytes)
    (hDerefAlign : checkDerefAlign localDecls layouts
      (some (resolveTyWithLocalDecls localDecls layouts ptTy)) pv.offsetBytes = true)
    (hAlign : ∀ rootVal, get? locals entry.targetLocal = some (.init rootVal) →
      checkTargetPlaceAlign localDecls layouts
        (some (resolveTyWithLocalDecls localDecls layouts ptTy)) entry pv (some rootVal) = true)
    (hResT : ∀ rootVal, get? locals entry.targetLocal = some (.init rootVal) →
      resolveStackThinPtrTargetProjWithResidual? locals rootVal entry pv (rHead :: rTail)
        localDecls layouts (some (resolveTyWithLocalDecls localDecls layouts ptTy)) none =
        some (entry.targetProjection ++ (rHead :: rTail), 0))
    (hNoUnion : placeTouchesUnion localDecls layouts
      ⟨entry.targetLocal, entry.targetProjection ++ (rHead :: rTail)⟩ = false)
    (hValid : validateValueForTy? layouts
      (some (resolveTyWithLocalDecls localDecls layouts accTy)) (.scalar sc) = true)
    (hLoad : validateLoadedValue layouts localDecls (.copy ⟨p, .deref :: rHead :: rTail⟩)
      (.scalar sc) = true) :
    ∃ mem', evalRvalue locals (.use (.copy ⟨p, .deref :: rHead :: rTail⟩)) mem localDecls layouts =
      .ok (.scalar sc) locals mem' :=
  evalRvalue_use_copy_of_evalOperand
    (evalDerefPlaceRead_refines_evalOperand_typed_proj hRel hRest hPtr hTy hRes hEntry hPerm hRead
      hDecls hPtTy hAccTy hPtNotScalar hAccNotNever hAccNotUnitTuple hAccNotFnDef hScalar hWidth
      hDerefAlign hAlign hResT hNoUnion hValid mem.globals mem.callerLocals) hLoad

/-- **Projected typed `Deref` writes refine Trusted's typed `writePlaceValue`
(`evalDerefPlaceWrite_refines_writePlaceValue_typed_proj`)**: with non-empty `localDecls` and a
non-empty post-deref projection suffix `rHead :: rTail` (`projectionHasDeref (rHead :: rTail) = false`),
Trusted writes `(*_p).(rHead :: rTail) = .scalar wSc` through `writeStackThinPtrTypedDeref` and
`resolveStackThinPtrTargetProjWithResidual?`. On below-related frames, if Anneal writes `.scalar wSc`
through `⟨p, .deref :: rHead :: rTail⟩` into an initialized target whose current sub-place
`entry.targetProjection ++ (rHead :: rTail)` holds `.scalar oldSc` of the same width, and Trusted's
typed checks pass, then Trusted's typed `writePlaceValue` succeeds and the updated frames stay
related by `SlotsRefine SlotBelow`. -/
theorem evalDerefPlaceWrite_refines_writePlaceValue_typed_proj
    {arityOf : Ty → VariantIdx → Bool → Option Nat} {rootTyOf : Nat → Ty}
    {cx : SubplaceCtx} (hWF : cx.WF) {slots slots' : List LocalSlotState}
    {locals : List LocalSlot} {p : Nat} {rHead : ProjectionElem} {rTail : List ProjectionElem}
    {oldSc wSc : ScalarInt} {root : Value} {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy}
    {borrows : List BorrowEntry} {entry : BorrowEntry}
    {localDecls : List LocalDecl} {layouts : LayoutTable} {ptTy accTy : Ty}
    (hRel : SlotsRefine SlotBelow slots locals)
    (hRest : projectionHasDeref (rHead :: rTail) = false)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz))
    (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty false =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow borrows pv.tag = some entry)
    (hPerm : entry.perm = .active ∨ entry.perm = .reserved)
    (hTgt : slots[entry.targetLocal]? = some (.init root))
    (hOld : readPlaceState slots ⟨entry.targetLocal, entry.targetProjection ++ (rHead :: rTail)⟩ =
      .ok (.scalar oldSc))
    (hW : evalDerefPlaceWrite arityOf rootTyOf cx slots ⟨p, .deref :: rHead :: rTail⟩ (.scalar wSc) =
      .ok slots')
    (hDecls : localDecls ≠ [])
    (hPtTy : placeTyResolved localDecls layouts ⟨p, [.deref]⟩ = some ptTy)
    (hAccTy : placeTyResolved localDecls layouts ⟨p, .deref :: rHead :: rTail⟩ = some accTy)
    (hPtNotScalar : isScalarRigidTy ptTy.kind = false)
    (hAccNotNever : (resolveTyWithLocalDecls localDecls layouts accTy).kind ≠ .never)
    (hPos : 1 ≤ wSc.sizeBytes)
    (hWidth : wSc.sizeBytes = oldSc.sizeBytes)
    (hDerefAlign : checkDerefAlign localDecls layouts
      (some (resolveTyWithLocalDecls localDecls layouts ptTy)) pv.offsetBytes = true)
    (hAlign : checkTargetPlaceAlign localDecls layouts
      (some (resolveTyWithLocalDecls localDecls layouts ptTy)) entry pv (some root) = true)
    (hResT : resolveStackThinPtrTargetProjWithResidual? locals root entry pv (rHead :: rTail)
      localDecls layouts (some (resolveTyWithLocalDecls localDecls layouts ptTy)) none =
      some (entry.targetProjection ++ (rHead :: rTail), 0))
    (hNoUnion : placeTouchesUnion localDecls layouts
      ⟨entry.targetLocal, entry.targetProjection ++ (rHead :: rTail)⟩ = false)
    (hValid : validateValueForTy? layouts
      (some (resolveTyWithLocalDecls localDecls layouts accTy)) (.scalar wSc) = true) :
    ∃ locals', writePlaceValue locals borrows ⟨p, .deref :: rHead :: rTail⟩ (.scalar wSc)
        localDecls layouts = .ok locals' ∧
      SlotsRefine SlotBelow slots' locals' := by
  obtain ⟨stp, hStp, hLiveP⟩ := readPlaceState_ok_live hPtr
  have hResT0 : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty
      (true && (rHead :: rTail).isEmpty) = .ok (entry.targetLocal, entry.targetProjection) := by
    simpa using hRes
  have hPl := resolvePlace_deref hStp hLiveP hPtr hTy hResT0 hRest
  simp only [evalDerefPlaceWrite, hPl] at hW
  have hQ : projectionHasDeref (entry.targetProjection ++ (rHead :: rTail)) = false := by
    rw [projectionHasDeref_append, resolveSyntheticSubplace_noDeref hWF hRes, hRest]; rfl
  cases hWS : writePlaceState arityOf slots
      ⟨entry.targetLocal, entry.targetProjection ++ (rHead :: rTail)⟩
      (rootTyOf entry.targetLocal) (.scalar wSc) with
  | ub => simp [hWS, liftWrite] at hW
  | unsupported => simp [hWS, liftWrite] at hW
  | ok s =>
    simp only [hWS, liftWrite, Except.ok.injEq] at hW
    subst hW
    obtain ⟨root', hWr, hEq⟩ := writePlaceState_init_root_inv hTgt hQ hWS
    subst hEq
    have hSame := sameScalarLocals_of_slotBelow hRel
    have hWT : evalValueProjWrite locals root (entry.targetProjection ++ (rHead :: rTail))
        (.scalar wSc) = .ok root' := by
      rw [← evalValueProjWrite_congr_scalar_locals hSame]; exact hWr
    have hWP := evalValueProjWrite_refines_writeProjectedValue _ _ _ _ _ hWT
    obtain ⟨rootP, hp, hrp⟩ := readPlaceState_below_refines hRel hPtr
    simp only [readProjectedValue] at hrp
    cases hrp
    obtain ⟨rootOld, htOld, hrOld⟩ := readPlaceState_below_refines hRel hOld
    have hTT : locals[entry.targetLocal]? = some (.init root) := by
      rcases SlotsRefine.get?_rel entry.targetLocal hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, hAT⟩
      · simp only [get?_eq_getElem?] at hA; rw [hA] at hTgt; nomatch hTgt
      · simp only [get?_eq_getElem?] at hA hT
        rw [hA] at hTgt
        cases hTgt
        cases t with
        | init w => have hvw : root = w := hAT; subst hvw; exact hT
        | _ => simp [SlotBelow] at hAT
    have hRootOldEq : rootOld = root := by
      simp only [get?_eq_getElem?] at htOld
      rw [hTT] at htOld
      injection htOld with h1
      injection h1 with h2
      exact h2.symm
    subst hRootOldEq
    have hLtT : entry.targetLocal < locals.length := (List.getElem?_eq_some_iff.mp hTT).1
    obtain ⟨d0, ds, hcons⟩ : ∃ d0 ds, localDecls = d0 :: ds := by
      cases h : localDecls with
      | nil => exact absurd h hDecls
      | cons d0 ds => exact ⟨d0, ds, rfl⟩
    have hsplice : spliceScalarSlice? oldSc 0 wSc = some wSc := by
      unfold spliceScalarSlice?
      have hb1 : Bool.and (Nat.ble 1 wSc.sizeBytes)
          (Nat.ble (Nat.add 0 wSc.sizeBytes) oldSc.sizeBytes) = true := by
        simp [Nat.add_eq, Nat.ble_eq, ← hWidth, hPos]
      have hb2 : Bool.and (Nat.beq 0 0) (Nat.beq wSc.sizeBytes oldSc.sizeBytes) = true := by
        simp [hWidth]
      rw [hb1, hb2]
    have hSynthFalse : evalStackThinPtrTypedDerefRead.match_1 (fun _ _ => Bool)
        (stripTransparentProjections (rHead :: rTail)) (some ptTy)
        (fun _ _ _ _ => true) (fun _ _ _ _ => true) (fun _ _ _ _ _ => true)
        (fun _ _ _ _ _ => true) (fun _ _ _ _ _ => true) (fun _ _ => false) = false := by
      rcases ptTy with ⟨k, lidx⟩
      cases k <;> try simp [isScalarRigidTy] at hPtNotScalar
      all_goals cases stripTransparentProjections (rHead :: rTail) with
        | nil => rfl
        | cons h t => cases h <;> rfl
    refine ⟨locals.set entry.targetLocal (.init root'), ?_,
      SlotsRefine.set (a := .init root') (t := .init root') rfl _ hRel⟩
    unfold writePlaceValue
    dsimp only
    rw [hp]
    dsimp only
    rw [hEntry]
    dsimp only
    rcases hPerm with hpe | hpe <;> rw [hpe]
    all_goals
      dsimp only
      rw [hcons]
      dsimp only
      rw [← hcons]
      unfold writeStackThinPtrTypedDeref
      rw [hPtTy, hAccTy, hSynthFalse, htOld]
      dsimp only
      rw [hDerefAlign, hAlign, hValid]
      simp only [Bool.and_self]
      rw [hcons]
      dsimp only
      rw [← hcons, hResT]
      dsimp only
      cases hFull : entry.targetProjection ++ (rHead :: rTail) with
      | nil =>
        have := List.append_eq_nil_iff.mp hFull
        nomatch this.2
      | cons fh ft =>
        rw [hFull] at hrOld hWP hNoUnion
        dsimp only [readProjectedForLocal]
        rw [hNoUnion]
        dsimp only
        rw [hrOld]
        dsimp only
        rcases hResAcc : resolveTyWithLocalDecls localDecls layouts accTy with ⟨kAcc, lAcc⟩
        rw [hResAcc] at hAccNotNever
        cases kAcc with
        | never => exact absurd rfl hAccNotNever
        | _ =>
          simp [hsplice, writeProjectedForLocal, hNoUnion, hWP, set?, hLtT]

/-- **Projected typed `Deref` assignments refine Trusted's typed `evalStmt`
(`evalStmt_assign_deref_refines_typed_proj`)**: lifts
`evalDerefPlaceWrite_refines_writePlaceValue_typed_proj` through `evalStmt` on
`.assign ⟨p, .deref :: rHead :: rTail⟩ rv`. -/
theorem evalStmt_assign_deref_refines_typed_proj
    {arityOf : Ty → VariantIdx → Bool → Option Nat} {rootTyOf : Nat → Ty}
    {cx : SubplaceCtx} (hWF : cx.WF) {slots slots' : List LocalSlotState}
    (s : MachineState) {p : Nat} {rHead : ProjectionElem} {rTail : List ProjectionElem}
    (rv : Rvalue) (span : String)
    {oldSc wSc : ScalarInt} {root : Value} {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy}
    {entry : BorrowEntry} {localDecls : List LocalDecl} {layouts : LayoutTable} {ptTy accTy : Ty}
    (hprot : s.memory.activeProtectors = [])
    (hv : evalRvalue s.frame.locals rv s.memory localDecls layouts =
      .ok (.scalar wSc) s.frame.locals s.memory)
    (hRel : SlotsRefine SlotBelow slots s.frame.locals)
    (hRest : projectionHasDeref (rHead :: rTail) = false)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz))
    (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty false =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow s.memory.borrows pv.tag = some entry)
    (hPerm : entry.perm = .active ∨ entry.perm = .reserved)
    (hTgt : slots[entry.targetLocal]? = some (.init root))
    (hOld : readPlaceState slots ⟨entry.targetLocal, entry.targetProjection ++ (rHead :: rTail)⟩ =
      .ok (.scalar oldSc))
    (hW : evalDerefPlaceWrite arityOf rootTyOf cx slots ⟨p, .deref :: rHead :: rTail⟩ (.scalar wSc) =
      .ok slots')
    (hDecls : localDecls ≠ [])
    (hPtTy : placeTyResolved localDecls layouts ⟨p, [.deref]⟩ = some ptTy)
    (hAccTy : placeTyResolved localDecls layouts ⟨p, .deref :: rHead :: rTail⟩ = some accTy)
    (hPtNotScalar : isScalarRigidTy ptTy.kind = false)
    (hAccNotNever : (resolveTyWithLocalDecls localDecls layouts accTy).kind ≠ .never)
    (hPos : 1 ≤ wSc.sizeBytes)
    (hWidth : wSc.sizeBytes = oldSc.sizeBytes)
    (hDerefAlign : checkDerefAlign localDecls layouts
      (some (resolveTyWithLocalDecls localDecls layouts ptTy)) pv.offsetBytes = true)
    (hAlign : checkTargetPlaceAlign localDecls layouts
      (some (resolveTyWithLocalDecls localDecls layouts ptTy)) entry pv (some root) = true)
    (hResT : resolveStackThinPtrTargetProjWithResidual? s.frame.locals root entry pv (rHead :: rTail)
      localDecls layouts (some (resolveTyWithLocalDecls localDecls layouts ptTy)) none =
      some (entry.targetProjection ++ (rHead :: rTail), 0))
    (hNoUnion : placeTouchesUnion localDecls layouts
      ⟨entry.targetLocal, entry.targetProjection ++ (rHead :: rTail)⟩ = false)
    (hValid : validateValueForTy? layouts
      (some (resolveTyWithLocalDecls localDecls layouts accTy)) (.scalar wSc) = true) :
    ∃ locals', evalStmt s ⟨.assign ⟨p, .deref :: rHead :: rTail⟩ rv, span⟩ localDecls layouts =
        MirStepNode.step (advanceStmt s locals'
          { s.memory with
            borrows := invalidateDerefWriteBorrows s.frame.locals s.memory.borrows
              ⟨p, .deref :: rHead :: rTail⟩ (rHead :: rTail) }) ∧
      SlotsRefine SlotBelow slots' locals' := by
  obtain ⟨locals', hWP, hRel'⟩ := evalDerefPlaceWrite_refines_writePlaceValue_typed_proj hWF hRel
    hRest hPtr hTy hRes hEntry hPerm hTgt hOld hW hDecls hPtTy hAccTy hPtNotScalar hAccNotNever hPos
    hWidth hDerefAlign hAlign hResT hNoUnion hValid
  refine ⟨locals', ?_, hRel'⟩
  simp only [evalStmt, hv, evalPlaceWrite, hprot, hWP]

/-- Whole-pair witness context: type `100` is `(u32, u32)` (`8`-byte, `4`-aligned), and `_1` holds
`*mut (u32, u32) = &raw _0` (address `0x1000`, provenance `(1, 0)`), which resolves via
`resolveSyntheticSubplace` to the root `(0, [])`. -/
def witnessPairCtxT : SubplaceCtx where
  allocs := [some (8, 4), some (8, 8)]
  limit := 2 ^ 64 - 1
  layoutOf l := if l = 0 then some (.struct 8 [0, 4] [.leaf 4, .leaf 4])
    else if l = 1 then some (.leaf 8) else none
  declTy l := if l = 0 then some 100 else if l = 1 then some 101 else none
  candidates t l off :=
    if t = 100 ∧ l = 0 ∧ off = 0 then [[]]
    else []
  tyLayout t := if t = 100 then some ⟨8, 4, 4, true, true⟩ else none
  ptrTyAt l q := if l = 1 ∧ q = [] then some ⟨false, 100⟩ else none
  ptrOf pv := if pv.allocId = 1 then ⟨0x1000, some (1, 0)⟩ else ⟨pv.offsetBytes, none⟩
  decodeTag _ _ := none

theorem witnessPairCtxT_wf : witnessPairCtxT.WF := by
  refine ⟨fun l lay h => ?_, fun t l off q hq => ?_⟩
  · by_cases h0 : l = 0
    · subst h0
      simp only [witnessPairCtxT, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨witnessLayout_wf, by with_unfolding_all decide⟩
    · by_cases h1 : l = 1
      · subst h1
        simp only [witnessPairCtxT, Nat.one_ne_zero, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨.leaf 8, by with_unfolding_all decide⟩
      · simp [witnessPairCtxT, h0, h1] at h
  · by_cases hA : t = 100 ∧ l = 0 ∧ off = 0
    · obtain ⟨rfl, rfl, rfl⟩ := hA
      have hq' : q = [] := by simpa [witnessPairCtxT] using hq
      rw [hq']
      exact ⟨.struct 8 [0, 4] [.leaf 4, .leaf 4], .struct 8 [0, 4] [.leaf 4, .leaf 4],
        ⟨8, 4, 4, true, true⟩, by simp [witnessPairCtxT], rfl, by simp [witnessPairCtxT], rfl⟩
    · simp [witnessPairCtxT, hA] at hq

def witnessPairEntry : BorrowEntry :=
  { tag := 1, targetLocal := 0, targetProjection := [], perm := .active }

def witnessPairLocalDecls : List LocalDecl :=
  [ { mutability := .mut, ty := { kind := .tuple [witnessU32.kind, witnessU32.kind], layoutIdx := 0 }, debugName := none }
  , { mutability := .mut, ty := { kind := .rawPtr .mut (.tuple [witnessU32.kind, witnessU32.kind]), layoutIdx := 0 }, debugName := none } ]

theorem witnessPairCtxT_resolve :
    resolveSyntheticSubplace witnessPairCtxT witnessSlotsT
      (witnessPairCtxT.ptrOf witnessPtrT) ⟨false, 100⟩ false =
      .ok (witnessPairEntry.targetLocal, witnessPairEntry.targetProjection) := by
  have hPtrOf : witnessPairCtxT.ptrOf witnessPtrT = ⟨0x1000, some (1, 0)⟩ := rfl
  rw [hPtrOf]
  have hP : PtrPrechecks witnessPairCtxT ⟨0x1000, some (1, 0)⟩ ⟨false, 100⟩
      ⟨8, 4, 4, true, true⟩ :=
    ⟨by decide, by decide, rfl, by decide, by decide, (fun h => by nomatch h), by decide⟩
  rw [resolveSyntheticSubplace_of_prechecks hP]
  have hNot : ¬ min witnessSlotsT.length witnessPairCtxT.allocs.length ≤ 0 := by decide
  have hSt : witnessSlotsT[0]? =
      some (.init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩])) := rfl
  have hBase : localBaseAddr witnessPairCtxT.allocs 0 witnessPairCtxT.limit = some 0x1000 := by
    with_unfolding_all decide
  have hOwn : ownLayout witnessPairCtxT.allocs 0 = some (8, 4) := rfl
  have hRoot : (0x1000 - 0x1000 = 0 ∧ witnessPairCtxT.declTy 0 = some 100) := ⟨rfl, rfl⟩
  have hLt1 : ¬ (0x1000 < 0x1000) := by decide
  have hLt2 : ¬ (8 < 0x1000 - 0x1000 + 8) := by decide
  simp only [hNot, ↓reduceIte, hSt, hBase, hOwn, hLt1, hLt2, hRoot]
  rfl

/-- **Non-vacuity of the projected typed `Deref` read and write refinements
(`witness_trusted_deref_proj_typed`)**: every hypothesis of
`evalDerefPlaceRead_refines_evalOperand_typed_proj` and
`evalDerefPlaceWrite_refines_writePlaceValue_typed_proj` holds on `_0 : (u32, u32) = (7, 9)`,
`_1 : *mut (u32, u32) = &raw _0` for the projected deref place `(*_1).1`
(`⟨1, [.deref, .field 1 witnessU32]⟩`), so both Anneal and Trusted read `9` from `(*_1).1` and
write `(*_1).1 = 5` to produce `_0 = (7, 5)`. -/
theorem witness_trusted_deref_proj_typed :
    let slots' : List LocalSlotState :=
      [.init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨5, 4⟩]), .init (.ptr witnessPtrT 8)]
    let locals' : List LocalSlot :=
      [.init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨5, 4⟩]), .init (.ptr witnessPtrT 8)]
    evalDerefPlaceRead witnessPairCtxT witnessSlotsT ⟨1, [.deref, .field 1 witnessU32]⟩ =
      .ok (.scalar ⟨9, 4⟩) ∧
    evalOperand witnessLocalsT (.copy ⟨1, [.deref, .field 1 witnessU32]⟩) [witnessPairEntry] []
      emptyLayoutTable [] witnessPairLocalDecls = .ok (.scalar ⟨9, 4⟩) witnessLocalsT ∧
    evalDerefPlaceWrite (fun _ _ _ => none)
        (fun _ => { kind := .tuple [witnessU32.kind, witnessU32.kind], layoutIdx := 0 })
        witnessPairCtxT witnessSlotsT ⟨1, [.deref, .field 1 witnessU32]⟩ (.scalar ⟨5, 4⟩) =
      .ok slots' ∧
    writePlaceValue witnessLocalsT [witnessPairEntry] ⟨1, [.deref, .field 1 witnessU32]⟩
      (.scalar ⟨5, 4⟩) witnessPairLocalDecls emptyLayoutTable = .ok locals' ∧
    SlotsRefine SlotBelow slots' locals' := by
  have hRes := witnessPairCtxT_resolve
  have hPtr1 : readPlaceState witnessSlotsT ⟨1, []⟩ = .ok (.ptr witnessPtrT 8) := by
    with_unfolding_all rfl
  have hTy1 : witnessPairCtxT.ptrTyAt 1 [] = some ⟨false, 100⟩ := rfl
  have hRP : ∀ ow, resolvePlace witnessPairCtxT witnessSlotsT
      ⟨1, [.deref, .field 1 witnessU32]⟩ ow = .ok ⟨0, [.field 1 witnessU32]⟩ := by
    intro ow
    unfold resolvePlace derefTarget
    have hOW : (ow && ([(.field 1 witnessU32 : ProjectionElem)]).isEmpty) = false := by
      cases ow <;> rfl
    have hSt1 : witnessSlotsT[1]? = some (.init (.ptr witnessPtrT 8)) := rfl
    dsimp only
    rw [hSt1, hPtr1, hTy1, hOW]
    dsimp only
    rw [hRes]
    rfl
  have hRead : evalDerefPlaceRead witnessPairCtxT witnessSlotsT ⟨1, [.deref, .field 1 witnessU32]⟩ =
      .ok (.scalar ⟨9, 4⟩) := by
    unfold evalDerefPlaceRead
    rw [hRP false]
    with_unfolding_all rfl
  have hW : evalDerefPlaceWrite (fun _ _ _ => none)
      (fun _ => { kind := .tuple [witnessU32.kind, witnessU32.kind], layoutIdx := 0 })
      witnessPairCtxT witnessSlotsT ⟨1, [.deref, .field 1 witnessU32]⟩ (.scalar ⟨5, 4⟩) =
      .ok [.init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨5, 4⟩]), .init (.ptr witnessPtrT 8)] := by
    unfold evalDerefPlaceWrite
    rw [hRP true]
    with_unfolding_all rfl
  have hRel : SlotsRefine SlotBelow witnessSlotsT witnessLocalsT := by
    simp [witnessSlotsT, witnessLocalsT, SlotsRefine, SlotBelow]
  have hOp : evalOperand witnessLocalsT (.copy ⟨1, [.deref, .field 1 witnessU32]⟩)
      [witnessPairEntry] [] emptyLayoutTable [] witnessPairLocalDecls =
      .ok (.scalar ⟨9, 4⟩) witnessLocalsT :=
    evalDerefPlaceRead_refines_evalOperand_typed_proj
      (localDecls := witnessPairLocalDecls) (layouts := emptyLayoutTable)
      (borrows := [witnessPairEntry]) (entry := witnessPairEntry)
      (ptTy := { kind := .tuple [witnessU32.kind, witnessU32.kind], layoutIdx := 0 })
      (accTy := witnessU32) (n := 4)
      hRel rfl (by with_unfolding_all rfl) (by simp [witnessPairCtxT]) hRes
      rfl (by simp [witnessPairEntry]) hRead (by decide)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl
      (fun h => by nomatch h) (fun h => by nomatch h) (fun _ _ h => by nomatch h)
      (by with_unfolding_all rfl) rfl (by with_unfolding_all rfl)
      (fun rootVal h => by cases h; with_unfolding_all rfl)
      (fun rootVal h => by cases h; with_unfolding_all rfl)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) [] []
  obtain ⟨locals', hWP, hRel'⟩ := evalDerefPlaceWrite_refines_writePlaceValue_typed_proj
    (borrows := [witnessPairEntry]) (entry := witnessPairEntry)
    (localDecls := witnessPairLocalDecls) (layouts := emptyLayoutTable)
    (root := .aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩]) (oldSc := ⟨9, 4⟩)
    (ptTy := { kind := .tuple [witnessU32.kind, witnessU32.kind], layoutIdx := 0 })
    (accTy := witnessU32)
    witnessPairCtxT_wf hRel rfl (by with_unfolding_all rfl) (by simp [witnessPairCtxT]) hRes
    rfl (Or.inl rfl) rfl (by with_unfolding_all rfl) hW (by decide)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl
    (fun h => by nomatch h) (by decide) rfl (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  have hWP' : writePlaceValue witnessLocalsT [witnessPairEntry]
      ⟨1, [.deref, .field 1 witnessU32]⟩ (.scalar ⟨5, 4⟩) witnessPairLocalDecls emptyLayoutTable =
      .ok [.init (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨5, 4⟩]), .init (.ptr witnessPtrT 8)] := by
    with_unfolding_all rfl
  rw [hWP'] at hWP
  injection hWP with hEq
  subst hEq
  exact ⟨hRead, hOp, hW, hWP', hRel'⟩

/-- Array-window witness context (`_0 : [u32; 4]` at `0x1000..0x1010`, `_1 : [u32; 4]` at
`0x2000..0x2010`), where `resolveSyntheticSubplace` resolves element pointers `&raw _0[0]`,
`&raw _0[1]`, `&raw _0[2]`, and `&raw _1[0]` directly from the `ByteLayout.struct 16 [0, 4, 8, 12]`
4-element layout without any ad-hoc `resolve` closure. -/
def witnessArrCtx : SubplaceCtx where
  allocs := [some (16, 4), some (16, 4)]
  limit := 2 ^ 64 - 1
  layoutOf l := if l ≤ 1 then
    some (.struct 16 [0, 4, 8, 12] [.leaf 4, .leaf 4, .leaf 4, .leaf 4])
    else none
  declTy l := if l ≤ 1 then some 200 else none
  candidates t l off :=
    if t = 1 ∧ l ≤ 1 then
      if off = 0 then [[.constantIndex 0 4 false]]
      else if off = 4 then [[.constantIndex 1 4 false]]
      else if off = 8 then [[.constantIndex 2 4 false]]
      else if off = 12 then [[.constantIndex 3 4 false]]
      else []
    else []
  tyLayout t := if t = 1 then some ⟨4, 4, 4, true, true⟩ else none
  ptrTyAt _ _ := some ⟨false, 1⟩
  ptrOf pv := ⟨pv.offsetBytes, some (pv.allocId, 0)⟩
  decodeTag _ _ := none

def witnessArrSlots : List LocalSlotState :=
  [ .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩])
  , .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]) ]

theorem witnessArrCtx_resolve_0_0 :
    resolveSyntheticSubplace witnessArrCtx witnessArrSlots ⟨0x1000, some (1, 0)⟩ ⟨false, 1⟩ false =
      .ok (0, [.constantIndex 0 4 false]) := by
  have hP : PtrPrechecks witnessArrCtx ⟨0x1000, some (1, 0)⟩ ⟨false, 1⟩ ⟨4, 4, 4, true, true⟩ :=
    ⟨by decide, by decide, rfl, by decide, by decide, (fun h => by nomatch h), by decide⟩
  rw [resolveSyntheticSubplace_of_prechecks hP]
  have hNot : ¬ min witnessArrSlots.length witnessArrCtx.allocs.length ≤ 0 := by decide
  have hSt : witnessArrSlots[0]? =
      some (.init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩])) := rfl
  have hBase : localBaseAddr witnessArrCtx.allocs 0 witnessArrCtx.limit = some 0x1000 := by
    with_unfolding_all decide
  have hOwn : ownLayout witnessArrCtx.allocs 0 = some (16, 4) := rfl
  have hLt1 : ¬ (0x1000 < 0x1000) := by decide
  have hLt2 : ¬ (16 < 0x1000 - 0x1000 + 4) := by decide
  simp only [hNot, ↓reduceIte, hSt, hBase, hOwn, hLt1, hLt2]
  with_unfolding_all rfl

theorem witnessArrCtx_resolve_0_1 :
    resolveSyntheticSubplace witnessArrCtx witnessArrSlots ⟨0x1004, some (1, 0)⟩ ⟨false, 1⟩ false =
      .ok (0, [.constantIndex 1 4 false]) := by
  have hP : PtrPrechecks witnessArrCtx ⟨0x1004, some (1, 0)⟩ ⟨false, 1⟩ ⟨4, 4, 4, true, true⟩ :=
    ⟨by decide, by decide, rfl, by decide, by decide, (fun h => by nomatch h), by decide⟩
  rw [resolveSyntheticSubplace_of_prechecks hP]
  have hNot : ¬ min witnessArrSlots.length witnessArrCtx.allocs.length ≤ 0 := by decide
  have hSt : witnessArrSlots[0]? =
      some (.init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩])) := rfl
  have hBase : localBaseAddr witnessArrCtx.allocs 0 witnessArrCtx.limit = some 0x1000 := by
    with_unfolding_all decide
  have hOwn : ownLayout witnessArrCtx.allocs 0 = some (16, 4) := rfl
  have hLt1 : ¬ (0x1004 < 0x1000) := by decide
  have hLt2 : ¬ (16 < 0x1004 - 0x1000 + 4) := by decide
  simp only [hNot, ↓reduceIte, hSt, hBase, hOwn, hLt1, hLt2]
  with_unfolding_all rfl

theorem witnessArrCtx_resolve_0_2 :
    resolveSyntheticSubplace witnessArrCtx witnessArrSlots ⟨0x1008, some (1, 0)⟩ ⟨false, 1⟩ true =
      .ok (0, [.constantIndex 2 4 false]) := by
  have hP : PtrPrechecks witnessArrCtx ⟨0x1008, some (1, 0)⟩ ⟨false, 1⟩ ⟨4, 4, 4, true, true⟩ :=
    ⟨by decide, by decide, rfl, by decide, by decide, (fun h => by nomatch h), by decide⟩
  rw [resolveSyntheticSubplace_of_prechecks hP]
  have hNot : ¬ min witnessArrSlots.length witnessArrCtx.allocs.length ≤ 0 := by decide
  have hSt : witnessArrSlots[0]? =
      some (.init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩])) := rfl
  have hBase : localBaseAddr witnessArrCtx.allocs 0 witnessArrCtx.limit = some 0x1000 := by
    with_unfolding_all decide
  have hOwn : ownLayout witnessArrCtx.allocs 0 = some (16, 4) := rfl
  have hLt1 : ¬ (0x1008 < 0x1000) := by decide
  have hLt2 : ¬ (16 < 0x1008 - 0x1000 + 4) := by decide
  simp only [hNot, ↓reduceIte, hSt, hBase, hOwn, hLt1, hLt2]
  with_unfolding_all rfl

theorem witnessArrCtx_resolve_1_0 :
    resolveSyntheticSubplace witnessArrCtx witnessArrSlots ⟨0x2000, some (2, 0)⟩ ⟨false, 1⟩ true =
      .ok (1, [.constantIndex 0 4 false]) := by
  have hP : PtrPrechecks witnessArrCtx ⟨0x2000, some (2, 0)⟩ ⟨false, 1⟩ ⟨4, 4, 4, true, true⟩ :=
    ⟨by decide, by decide, rfl, by decide, by decide, (fun h => by nomatch h), by decide⟩
  rw [resolveSyntheticSubplace_of_prechecks hP]
  have hNot : ¬ min witnessArrSlots.length witnessArrCtx.allocs.length ≤ 1 := by decide
  have hSt : witnessArrSlots[1]? =
      some (.init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩])) := rfl
  have hBase : localBaseAddr witnessArrCtx.allocs 1 witnessArrCtx.limit = some 0x2000 := by
    with_unfolding_all decide
  have hOwn : ownLayout witnessArrCtx.allocs 1 = some (16, 4) := rfl
  have hLt1 : ¬ (0x2000 < 0x2000) := by decide
  have hLt2 : ¬ (16 < 0x2000 - 0x2000 + 4) := by decide
  simp only [hNot, ↓reduceIte, hSt, hBase, hOwn, hLt1, hLt2]
  with_unfolding_all rfl

/-- **Non-vacuity of the `count ≥ 2` array-window `CopyNonOverlapping` refinement backed by
`resolveSyntheticSubplace` (`witness_trusted_window_copy_resolved`)** and **same-local disjoint
array-window copy `_0[0..2]` into `_0[2..4]` (`witness_trusted_window_copy_same_local`)**. -/
theorem witness_trusted_window_copy_resolved_and_same_local (s : MachineState) (srcOp dstOp : Operand) :
    let srcElems : List Value := [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩]
    let dstElems : List Value := [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]
    let crossDstElems : List Value := [.scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]
    let sameDstElems : List Value := [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩]
    let locals₃ : List LocalSlot := [.init (.aggregate 0 srcElems), .init (.aggregate 0 dstElems)]
    let resolve := fun p ow => resolveSyntheticSubplace witnessArrCtx witnessArrSlots p ⟨false, 1⟩ ow
    (evalCopyNonOverlappingSubplace (fun _ _ _ => none) (fun _ => witnessU32) false 64 witnessArrSlots resolve
        ⟨0x1004, some (1, 0)⟩ ⟨0x2000, some (2, 0)⟩ 2 4 4 =
      some [.init (.aggregate 0 srcElems), .init (.aggregate 0 crossDstElems)] ∧
     evalCopyNonOverlappingPermOk s srcOp dstOp [] emptyLayoutTable
        { allocId := 1, offsetBytes := 1 } { allocId := 2, offsetBytes := 0 }
        { tag := 1, targetLocal := 0, targetProjection := [], perm := .active }
        { tag := 2, targetLocal := 1, targetProjection := [], perm := .active } 2 locals₃ =
      .step (advanceStmt s [.init (.aggregate 0 srcElems), .init (.aggregate 0 crossDstElems)]
        { s.memory with borrows := invalidateConflictingBorrows s.memory.borrows 1 (some 2) })) ∧
    (evalCopyNonOverlappingSubplace (fun _ _ _ => none) (fun _ => witnessU32) false 64 witnessArrSlots resolve
        ⟨0x1000, some (1, 0)⟩ ⟨0x1008, some (1, 0)⟩ 2 4 4 =
      some [.init (.aggregate 0 sameDstElems), .init (.aggregate 0 dstElems)] ∧
     evalCopyNonOverlappingPermOk s srcOp dstOp [] emptyLayoutTable
        { allocId := 1, offsetBytes := 0 } { allocId := 2, offsetBytes := 2 }
        { tag := 1, targetLocal := 0, targetProjection := [], perm := .active }
        { tag := 2, targetLocal := 0, targetProjection := [], perm := .active } 2 locals₃ =
      .step (advanceStmt s [.init (.aggregate 0 sameDstElems), .init (.aggregate 0 dstElems)]
        { s.memory with borrows := invalidateConflictingBorrows s.memory.borrows 0 (some 2) })) := by
  have hCross : evalCopyNonOverlappingSubplace (fun _ _ _ => none) (fun _ => witnessU32) false 64
      witnessArrSlots
      (fun p ow => resolveSyntheticSubplace witnessArrCtx witnessArrSlots p ⟨false, 1⟩ ow)
      ⟨0x1004, some (1, 0)⟩ ⟨0x2000, some (2, 0)⟩ 2 4 4 =
      some [ .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩])
           , .init (.aggregate 0 [.scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]) ] := by
    unfold evalCopyNonOverlappingSubplace
    dsimp only
    rw [witnessArrCtx_resolve_0_1, witnessArrCtx_resolve_1_0]
    with_unfolding_all rfl
  have hSame : evalCopyNonOverlappingSubplace (fun _ _ _ => none) (fun _ => witnessU32) false 64
      witnessArrSlots
      (fun p ow => resolveSyntheticSubplace witnessArrCtx witnessArrSlots p ⟨false, 1⟩ ow)
      ⟨0x1000, some (1, 0)⟩ ⟨0x1008, some (1, 0)⟩ 2 4 4 =
      some [ .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩])
           , .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]) ] := by
    unfold evalCopyNonOverlappingSubplace
    dsimp only
    rw [witnessArrCtx_resolve_0_0, witnessArrCtx_resolve_0_2]
    with_unfolding_all rfl
  have hCrossRef := (evalCopyNonOverlappingSubplace_window_same_or_disjoint_refines
    (arityOf := fun _ _ _ => none) (rootTyOf := fun _ => witnessU32) (ts := false) (ptrBits := 64)
    (sl := 0) (dl := 1) (s0 := 1) (sLen := 4) (d0 := 0) (dLen := 4)
    (slots := witnessArrSlots)
    (locals₃ := [ .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩])
                , .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]) ])
    (resolve := fun p ow => resolveSyntheticSubplace witnessArrCtx witnessArrSlots p ⟨false, 1⟩ ow)
    (src := ⟨0x1004, some (1, 0)⟩) (dst := ⟨0x2000, some (2, 0)⟩)
    (by simp [witnessArrSlots, SlotsRefine, SlotBelow]) (by decide) (by decide)
    witnessArrCtx_resolve_0_1 witnessArrCtx_resolve_1_0
    rfl rfl rfl rfl hCross s srcOp dstOp [] emptyLayoutTable
    { allocId := 1, offsetBytes := 1 } { allocId := 2, offsetBytes := 0 }
    { tag := 1, targetLocal := 0, targetProjection := [], perm := .active }
    { tag := 2, targetLocal := 1, targetProjection := [], perm := .active }
    (by decide) (Or.inl (by decide)) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl rfl rfl rfl
    (fun _ _ _ h => by nomatch h)).1
  have hSameRef := (evalCopyNonOverlappingSubplace_window_same_or_disjoint_refines
    (arityOf := fun _ _ _ => none) (rootTyOf := fun _ => witnessU32) (ts := false) (ptrBits := 64)
    (sl := 0) (dl := 0) (s0 := 0) (sLen := 4) (d0 := 2) (dLen := 4)
    (slots := witnessArrSlots)
    (locals₃ := [ .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩])
                , .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩, .scalar ⟨3, 4⟩, .scalar ⟨4, 4⟩]) ])
    (resolve := fun p ow => resolveSyntheticSubplace witnessArrCtx witnessArrSlots p ⟨false, 1⟩ ow)
    (src := ⟨0x1000, some (1, 0)⟩) (dst := ⟨0x1008, some (1, 0)⟩)
    (by simp [witnessArrSlots, SlotsRefine, SlotBelow]) (by decide) (by decide)
    witnessArrCtx_resolve_0_0 witnessArrCtx_resolve_0_2
    rfl rfl rfl rfl hSame s srcOp dstOp [] emptyLayoutTable
    { allocId := 1, offsetBytes := 0 } { allocId := 2, offsetBytes := 2 }
    { tag := 1, targetLocal := 0, targetProjection := [], perm := .active }
    { tag := 2, targetLocal := 0, targetProjection := [], perm := .active }
    (by decide) (Or.inr (Or.inl (by decide))) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl rfl rfl rfl
    (fun _ _ _ h => by nomatch h)).1
  exact ⟨⟨hCross, hCrossRef⟩, ⟨hSame, hSameRef⟩⟩

/-! ### Section 4j: `Operand.move` through `Deref` (`move (*_p).rest`) -/

/-- **Trusted moves through a `Deref` by reading (`evalOperand_move_deref_eq_copy`)**: in both its
untyped (`localDecls = []`) and typed modes, Trusted's `evalOperand` evaluates
`Operand.move ((*_p).rest)` exactly like `Operand.copy ((*_p).rest)` — it reads the pointee through
the borrow table and returns the frame unchanged; only a `move` of a bare local deinitializes its
slot. This is the Trusted counterpart of `evalDerefOperand_move_deref`. -/
theorem evalOperand_move_deref_eq_copy (locals : List LocalSlot) (p : Nat)
    (rest : List ProjectionElem) (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot) (localDecls : List LocalDecl) :
    evalOperand locals (.move ⟨p, .deref :: rest⟩) borrows globals layouts callerLocals localDecls =
      evalOperand locals (.copy ⟨p, .deref :: rest⟩) borrows globals layouts callerLocals
        localDecls := rfl

/-- **`Rvalue.use (move (*_p).rest)` is `Rvalue.use (copy (*_p).rest)` in Trusted
(`evalRvalue_use_move_deref_eq_copy`)**: the load validation and the Tree-Borrows read freeze of
`evalRvalue` treat a `Deref` move like a `Deref` copy. -/
theorem evalRvalue_use_move_deref_eq_copy (locals : List LocalSlot) (p : Nat)
    (rest : List ProjectionElem) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    evalRvalue locals (.use (.move ⟨p, .deref :: rest⟩)) mem localDecls layouts =
      evalRvalue locals (.use (.copy ⟨p, .deref :: rest⟩)) mem localDecls layouts := by
  simp only [evalRvalue, evalOperand_move_deref_eq_copy]
  rcases hb : mem.borrows with _ | ⟨b₁, _ | ⟨b₂, bs⟩⟩ <;> rfl

/-- **`Operand.move` through `Deref` refines Trusted (`evalDerefOperand_move_refines_evalOperand`)**:
under the pointer correspondence of `evalDerefPlaceRead_refines_evalOperand`, if Anneal's
`evalDerefOperand` reads `v` from `Operand.move ((*_p).rest)` and returns the slots `slots'`, then
`slots'` is the unchanged frame `slots` (neither the target local nor `_p` is deinitialized),
Trusted's `Operand.move ((*_p).rest)` reads the same `v` and also keeps its frame, and the frames
stay related by `SlotsRefine SlotBelow`. -/
theorem evalDerefOperand_move_refines_evalOperand {cx : SubplaceCtx}
    {slots slots' : List LocalSlotState} {locals : List LocalSlot} {p : Nat}
    {rest : List ProjectionElem} {v : Value} {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy}
    {borrows : List BorrowEntry} {entry : BorrowEntry} (hRel : SlotsRefine SlotBelow slots locals)
    (hRest : projectionHasDeref rest = false)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz)) (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty false =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow borrows pv.tag = some entry) (hPerm : entry.perm ≠ .disabled)
    (hThin : needsThinPtrElemResolution entry.targetProjection pv.offsetBytes = false)
    (hMove : evalDerefOperand cx slots (.move ⟨p, .deref :: rest⟩) = (.ok v, slots'))
    (globals : List CapturedAllocation) (layouts : LayoutTable) (callerLocals : List LocalSlot) :
    slots' = slots ∧
      evalOperand locals (.move ⟨p, .deref :: rest⟩) borrows globals layouts callerLocals =
        .ok v locals ∧
      SlotsRefine SlotBelow slots' locals := by
  rw [(evalDerefOperand_move_deref cx slots ⟨p, .deref :: rest⟩ rfl).1] at hMove
  simp only [Prod.mk.injEq] at hMove
  obtain ⟨hRead, rfl⟩ := hMove
  refine ⟨rfl, ?_, hRel⟩
  rw [evalOperand_move_deref_eq_copy]
  exact evalDerefPlaceRead_refines_evalOperand hRel hRest hPtr hTy hRes hEntry hPerm hThin hRead
    globals layouts callerLocals

/-- **Typed `Operand.move (*_p)` refines Trusted's typed `evalOperand`
(`evalDerefOperand_move_refines_evalOperand_typed`)**: the `move` analogue of
`evalDerefPlaceRead_refines_evalOperand_typed` (scalar pointee, typed mode); both frames are
unchanged by the move. -/
theorem evalDerefOperand_move_refines_evalOperand_typed {cx : SubplaceCtx}
    {slots slots' : List LocalSlotState} {locals : List LocalSlot} {p : Nat} {sc : ScalarInt}
    {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy} {borrows : List BorrowEntry}
    {entry : BorrowEntry} {localDecls : List LocalDecl} {layouts : LayoutTable} {pTy : Ty}
    {n : Nat} (hRel : SlotsRefine SlotBelow slots locals)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz)) (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty false =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow borrows pv.tag = some entry) (hPerm : entry.perm ≠ .disabled)
    (hMove : evalDerefOperand cx slots (.move ⟨p, [.deref]⟩) = (.ok (.scalar sc), slots'))
    (hDecls : localDecls ≠ [])
    (hPTy : placeTyResolved localDecls layouts ⟨p, [.deref]⟩ = some pTy)
    (hScalar : tyScalarBytes (resolveTyWithLocalDecls localDecls layouts pTy) = some n)
    (hWidth : sc.sizeBytes = n) (hOff : pv.offsetBytes = 0)
    (hAlign : ∀ rootVal, get? locals entry.targetLocal = some (.init rootVal) →
      checkTargetPlaceAlign localDecls layouts
        (some (resolveTyWithLocalDecls localDecls layouts pTy)) entry pv (some rootVal) = true)
    (hNoUnion : placeTouchesUnion localDecls layouts
      ⟨entry.targetLocal, entry.targetProjection⟩ = false)
    (hValid : validateValueForTy? layouts
      (some (resolveTyWithLocalDecls localDecls layouts pTy)) (.scalar sc) = true)
    (globals : List CapturedAllocation) (callerLocals : List LocalSlot) :
    slots' = slots ∧
      evalOperand locals (.move ⟨p, [.deref]⟩) borrows globals layouts callerLocals localDecls =
        .ok (.scalar sc) locals ∧
      SlotsRefine SlotBelow slots' locals := by
  rw [(evalDerefOperand_move_deref cx slots ⟨p, [.deref]⟩ rfl).1] at hMove
  simp only [Prod.mk.injEq] at hMove
  obtain ⟨hRead, rfl⟩ := hMove
  refine ⟨rfl, ?_, hRel⟩
  rw [evalOperand_move_deref_eq_copy]
  exact evalDerefPlaceRead_refines_evalOperand_typed hRel hPtr hTy hRes hEntry hPerm hRead hDecls
    hPTy hScalar hWidth hOff hAlign hNoUnion hValid globals callerLocals

/-- **Projected typed `Operand.move (*_p).(rHead :: rTail)` refines Trusted's typed `evalOperand`
(`evalDerefOperand_move_refines_evalOperand_typed_proj`)**: the `move` analogue of
`evalDerefPlaceRead_refines_evalOperand_typed_proj`; both frames are unchanged by the move. -/
theorem evalDerefOperand_move_refines_evalOperand_typed_proj {cx : SubplaceCtx}
    {slots slots' : List LocalSlotState} {locals : List LocalSlot} {p : Nat}
    {rHead : ProjectionElem} {rTail : List ProjectionElem} {sc : ScalarInt}
    {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy} {borrows : List BorrowEntry}
    {entry : BorrowEntry} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {ptTy accTy : Ty} {n : Nat}
    (hRel : SlotsRefine SlotBelow slots locals)
    (hRest : projectionHasDeref (rHead :: rTail) = false)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz))
    (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty false =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow borrows pv.tag = some entry)
    (hPerm : entry.perm ≠ .disabled)
    (hMove : evalDerefOperand cx slots (.move ⟨p, .deref :: rHead :: rTail⟩) =
      (.ok (.scalar sc), slots'))
    (hDecls : localDecls ≠ [])
    (hPtTy : placeTyResolved localDecls layouts ⟨p, [.deref]⟩ = some ptTy)
    (hAccTy : placeTyResolved localDecls layouts ⟨p, .deref :: rHead :: rTail⟩ = some accTy)
    (hPtNotScalar : isScalarRigidTy ptTy.kind = false)
    (hAccNotNever : (resolveTyWithLocalDecls localDecls layouts accTy).kind ≠ .never)
    (hAccNotUnitTuple : (resolveTyWithLocalDecls localDecls layouts accTy).kind ≠ .tuple [])
    (hAccNotFnDef : ∀ fn args,
      (resolveTyWithLocalDecls localDecls layouts accTy).kind ≠ .fnDef fn args)
    (hScalar : tyScalarBytes (resolveTyWithLocalDecls localDecls layouts accTy) = some n)
    (hWidth : n = sc.sizeBytes)
    (hDerefAlign : checkDerefAlign localDecls layouts
      (some (resolveTyWithLocalDecls localDecls layouts ptTy)) pv.offsetBytes = true)
    (hAlign : ∀ rootVal, get? locals entry.targetLocal = some (.init rootVal) →
      checkTargetPlaceAlign localDecls layouts
        (some (resolveTyWithLocalDecls localDecls layouts ptTy)) entry pv (some rootVal) = true)
    (hResT : ∀ rootVal, get? locals entry.targetLocal = some (.init rootVal) →
      resolveStackThinPtrTargetProjWithResidual? locals rootVal entry pv (rHead :: rTail)
        localDecls layouts (some (resolveTyWithLocalDecls localDecls layouts ptTy)) none =
        some (entry.targetProjection ++ (rHead :: rTail), 0))
    (hNoUnion : placeTouchesUnion localDecls layouts
      ⟨entry.targetLocal, entry.targetProjection ++ (rHead :: rTail)⟩ = false)
    (hValid : validateValueForTy? layouts
      (some (resolveTyWithLocalDecls localDecls layouts accTy)) (.scalar sc) = true)
    (globals : List CapturedAllocation) (callerLocals : List LocalSlot) :
    slots' = slots ∧
      evalOperand locals (.move ⟨p, .deref :: rHead :: rTail⟩) borrows globals layouts
          callerLocals localDecls =
        .ok (.scalar sc) locals ∧
      SlotsRefine SlotBelow slots' locals := by
  rw [(evalDerefOperand_move_deref cx slots ⟨p, .deref :: rHead :: rTail⟩ rfl).1] at hMove
  simp only [Prod.mk.injEq] at hMove
  obtain ⟨hRead, rfl⟩ := hMove
  refine ⟨rfl, ?_, hRel⟩
  rw [evalOperand_move_deref_eq_copy]
  exact evalDerefPlaceRead_refines_evalOperand_typed_proj hRel hRest hPtr hTy hRes hEntry hPerm
    hRead hDecls hPtTy hAccTy hPtNotScalar hAccNotNever hAccNotUnitTuple hAccNotFnDef hScalar
    hWidth hDerefAlign hAlign hResT hNoUnion hValid globals callerLocals

/-- **`Rvalue.use (move (*_p).rest)` refines Trusted's `evalRvalue`
(`evalDerefPlaceRead_refines_evalRvalue_move`)**: the `move` analogue of
`evalDerefPlaceRead_refines_evalRvalue`. -/
theorem evalDerefPlaceRead_refines_evalRvalue_move {cx : SubplaceCtx}
    {slots : List LocalSlotState} {locals : List LocalSlot} {p : Nat} {rest : List ProjectionElem}
    {v : Value} {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy} {mem : Memory}
    {entry : BorrowEntry} (hRel : SlotsRefine SlotBelow slots locals)
    (hRest : projectionHasDeref rest = false)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz)) (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty false =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow mem.borrows pv.tag = some entry) (hPerm : entry.perm ≠ .disabled)
    (hThin : needsThinPtrElemResolution entry.targetProjection pv.offsetBytes = false)
    (hRead : evalDerefPlaceRead cx slots ⟨p, .deref :: rest⟩ = .ok v) (layouts : LayoutTable) :
    ∃ mem', evalRvalue locals (.use (.move ⟨p, .deref :: rest⟩)) mem [] layouts =
      .ok v locals mem' := by
  rw [evalRvalue_use_move_deref_eq_copy]
  exact evalDerefPlaceRead_refines_evalRvalue hRel hRest hPtr hTy hRes hEntry hPerm hThin hRead
    layouts

/-- **Projected typed `Rvalue.use (move (*_p).(rHead :: rTail))` refines Trusted's typed
`evalRvalue` (`evalDerefPlaceRead_refines_evalRvalue_typed_proj_move`)**. -/
theorem evalDerefPlaceRead_refines_evalRvalue_typed_proj_move {cx : SubplaceCtx}
    {slots : List LocalSlotState} {locals : List LocalSlot} {p : Nat}
    {rHead : ProjectionElem} {rTail : List ProjectionElem} {sc : ScalarInt}
    {pv : ProvenancePtr} {sz : Nat} {pty : PtrTy} {mem : Memory}
    {entry : BorrowEntry} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {ptTy accTy : Ty} {n : Nat}
    (hRel : SlotsRefine SlotBelow slots locals)
    (hRest : projectionHasDeref (rHead :: rTail) = false)
    (hPtr : readPlaceState slots ⟨p, []⟩ = .ok (.ptr pv sz))
    (hTy : cx.ptrTyAt p [] = some pty)
    (hRes : resolveSyntheticSubplace cx slots (cx.ptrOf pv) pty false =
      .ok (entry.targetLocal, entry.targetProjection))
    (hEntry : lookupBorrow mem.borrows pv.tag = some entry)
    (hPerm : entry.perm ≠ .disabled)
    (hRead : evalDerefPlaceRead cx slots ⟨p, .deref :: rHead :: rTail⟩ = .ok (.scalar sc))
    (hDecls : localDecls ≠ [])
    (hPtTy : placeTyResolved localDecls layouts ⟨p, [.deref]⟩ = some ptTy)
    (hAccTy : placeTyResolved localDecls layouts ⟨p, .deref :: rHead :: rTail⟩ = some accTy)
    (hPtNotScalar : isScalarRigidTy ptTy.kind = false)
    (hAccNotNever : (resolveTyWithLocalDecls localDecls layouts accTy).kind ≠ .never)
    (hAccNotUnitTuple : (resolveTyWithLocalDecls localDecls layouts accTy).kind ≠ .tuple [])
    (hAccNotFnDef : ∀ fn args,
      (resolveTyWithLocalDecls localDecls layouts accTy).kind ≠ .fnDef fn args)
    (hScalar : tyScalarBytes (resolveTyWithLocalDecls localDecls layouts accTy) = some n)
    (hWidth : n = sc.sizeBytes)
    (hDerefAlign : checkDerefAlign localDecls layouts
      (some (resolveTyWithLocalDecls localDecls layouts ptTy)) pv.offsetBytes = true)
    (hAlign : ∀ rootVal, get? locals entry.targetLocal = some (.init rootVal) →
      checkTargetPlaceAlign localDecls layouts
        (some (resolveTyWithLocalDecls localDecls layouts ptTy)) entry pv (some rootVal) = true)
    (hResT : ∀ rootVal, get? locals entry.targetLocal = some (.init rootVal) →
      resolveStackThinPtrTargetProjWithResidual? locals rootVal entry pv (rHead :: rTail)
        localDecls layouts (some (resolveTyWithLocalDecls localDecls layouts ptTy)) none =
        some (entry.targetProjection ++ (rHead :: rTail), 0))
    (hNoUnion : placeTouchesUnion localDecls layouts
      ⟨entry.targetLocal, entry.targetProjection ++ (rHead :: rTail)⟩ = false)
    (hValid : validateValueForTy? layouts
      (some (resolveTyWithLocalDecls localDecls layouts accTy)) (.scalar sc) = true)
    (hLoad : validateLoadedValue layouts localDecls (.move ⟨p, .deref :: rHead :: rTail⟩)
      (.scalar sc) = true) :
    ∃ mem', evalRvalue locals (.use (.move ⟨p, .deref :: rHead :: rTail⟩)) mem localDecls
        layouts = .ok (.scalar sc) locals mem' := by
  rw [evalRvalue_use_move_deref_eq_copy]
  exact evalDerefPlaceRead_refines_evalRvalue_typed_proj hRel hRest hPtr hTy hRes hEntry hPerm
    hRead hDecls hPtTy hAccTy hPtNotScalar hAccNotNever hAccNotUnitTuple hAccNotFnDef hScalar
    hWidth hDerefAlign hAlign hResT hNoUnion hValid hLoad

/-- **Non-vacuity of the `move`-through-`Deref` refinement
(`witness_trusted_deref_move_proj_typed`)**: on the projected witness frame of
`witness_trusted_deref_proj_typed` (`_0 : (u32, u32) = (7, 9)`, `_1 : *mut (u32, u32) = &raw _0`),
Anneal's `move (*_1).1` reads `9` and keeps every slot; Trusted's typed `move (*_1).1` reads `9`
and keeps its frame (both `_0` and `_1` stay initialized), whereas Trusted's `move _0` of the bare
target local deinitializes `_0`. -/
theorem witness_trusted_deref_move_proj_typed :
    evalDerefOperand witnessPairCtxT witnessSlotsT (.move ⟨1, [.deref, .field 1 witnessU32]⟩) =
      (.ok (.scalar ⟨9, 4⟩), witnessSlotsT) ∧
    evalOperand witnessLocalsT (.move ⟨1, [.deref, .field 1 witnessU32]⟩) [witnessPairEntry] []
      emptyLayoutTable [] witnessPairLocalDecls = .ok (.scalar ⟨9, 4⟩) witnessLocalsT ∧
    evalOperand witnessLocalsT (.move ⟨0, []⟩) [witnessPairEntry] [] emptyLayoutTable []
      witnessPairLocalDecls =
      .ok (.aggregate 0 [.scalar ⟨7, 4⟩, .scalar ⟨9, 4⟩]) (witnessLocalsT.set 0 .uninit) := by
  obtain ⟨hRead, hOp, -⟩ := witness_trusted_deref_proj_typed
  refine ⟨?_, ?_, by with_unfolding_all rfl⟩
  · rw [(evalDerefOperand_move_deref witnessPairCtxT witnessSlotsT
      ⟨1, [.deref, .field 1 witnessU32]⟩ rfl).1, hRead]
  · rw [evalOperand_move_deref_eq_copy]
    exact hOp

/-! ### Section 4k: Two-level `Deref` chains (`**_pp`) and runtime MIR's `CopyForDeref` split -/

/-- A live root's `Deref`-free read of the root itself is its value. -/
theorem readPlaceState_set_init_root {slots : List LocalSlotState} {t : Nat} (v : Value)
    (ht : t < slots.length) :
    readPlaceState (slots.set t (.init v)) ⟨t, []⟩ = .ok v := by
  simp [readPlaceState, projectionHasDeref, get?_eq_getElem?, List.getElem?_set_self ht,
    evalValueProjRead]

/-- **Two-level `Deref` chains are resolved through the intermediate pointer, exactly as runtime
MIR's `CopyForDeref` split (`resolvePlace_deref_deref_split`)**: runtime MIR never dereferences twice
in one place — it first copies the intermediate pointer into a fresh temporary
(`_t = CopyForDeref(*_pp)`) and then dereferences `_t`. Anneal's direct resolution of
`(**_pp).rest` (`derefTarget`, `resolve_deref_place_in`) agrees with that split: when `*_pp`
designates the sub-place `l.q` holding the pointer `pv₂` of type `pty₂`, which resolves to
`l₂.q₂`, then `(**_pp).rest` resolves to `l₂.(q₂ ++ rest)` in `slots`, and so does `(*_t).rest` in
the frame `slots.set t (.init (.ptr pv₂ sz₂))` after the `CopyForDeref`, for any temporary `_t` of
pointer type `pty₂` whose write keeps `pv₂`'s resolution. -/
theorem resolvePlace_deref_deref_split {cx : SubplaceCtx} {slots : List LocalSlotState} {ow : Bool}
    {pp t : Nat} {rest : List ProjectionElem} {stp : LocalSlotState} {pv₁ pv₂ : ProvenancePtr}
    {sz₁ sz₂ : Nat} {pty₁ pty₂ : PtrTy} {l l₂ : Nat} {q q₂ : List ProjectionElem}
    (hSt : slots[pp]? = some stp) (hLive : stp ≠ .dead)
    (hPtr₁ : readPlaceState slots ⟨pp, []⟩ = .ok (.ptr pv₁ sz₁))
    (hTy₁ : cx.ptrTyAt pp [] = some pty₁)
    (hRes₁ : resolveSyntheticSubplace cx slots (cx.ptrOf pv₁) pty₁ false = .ok (l, q))
    (hPtr₂ : readPlaceState slots ⟨l, q⟩ = .ok (.ptr pv₂ sz₂))
    (hTy₂ : cx.ptrTyAt l q = some pty₂)
    (hRes₂ : resolveSyntheticSubplace cx slots (cx.ptrOf pv₂) pty₂ (ow && rest.isEmpty) =
      .ok (l₂, q₂))
    (hRest : projectionHasDeref rest = false)
    (ht : t < slots.length) (hTyT : cx.ptrTyAt t [] = some pty₂)
    (hRes₂' : resolveSyntheticSubplace cx (slots.set t (.init (.ptr pv₂ sz₂))) (cx.ptrOf pv₂) pty₂
      (ow && rest.isEmpty) = .ok (l₂, q₂)) :
    resolvePlace cx slots ⟨pp, .deref :: .deref :: rest⟩ ow = .ok ⟨l₂, q₂ ++ rest⟩ ∧
      resolvePlace cx (slots.set t (.init (.ptr pv₂ sz₂))) ⟨t, .deref :: rest⟩ ow =
        .ok ⟨l₂, q₂ ++ rest⟩ := by
  have hOw₁ : (ow && (.deref :: rest : List ProjectionElem).isEmpty) = false := by
    cases ow <;> rfl
  constructor
  · unfold resolvePlace
    simp only [hSt]
    cases stp with
    | dead => exact absurd rfl hLive
    | _ =>
      rw [derefTarget_deref hPtr₁ hTy₁ (by rw [hOw₁]; exact hRes₁),
        derefTarget_deref hPtr₂ hTy₂ hRes₂, derefTarget_noDeref cx slots ow _ _ _ hRest]
  · unfold resolvePlace
    have hSt' : (slots.set t (.init (.ptr pv₂ sz₂)))[t]? = some (.init (.ptr pv₂ sz₂)) :=
      List.getElem?_set_self ht
    simp only [hSt']
    rw [derefTarget_deref (readPlaceState_set_init_root _ ht) hTyT hRes₂',
      derefTarget_noDeref _ _ ow _ _ _ hRest]

/-- **Reading a two-level `Deref` chain (`evalDerefPlaceRead_deref_deref`)**: under the hypotheses of
`resolvePlace_deref_deref_split` (read mode), reading `(**_pp).rest` reads `l₂.(q₂ ++ rest)`, the
place `(*_t).rest` designates after the `CopyForDeref` split. -/
theorem evalDerefPlaceRead_deref_deref {cx : SubplaceCtx} {slots : List LocalSlotState}
    {pp : Nat} {rest : List ProjectionElem} {stp : LocalSlotState} {pv₁ pv₂ : ProvenancePtr}
    {sz₁ sz₂ : Nat} {pty₁ pty₂ : PtrTy} {l l₂ : Nat} {q q₂ : List ProjectionElem}
    (hSt : slots[pp]? = some stp) (hLive : stp ≠ .dead)
    (hPtr₁ : readPlaceState slots ⟨pp, []⟩ = .ok (.ptr pv₁ sz₁))
    (hTy₁ : cx.ptrTyAt pp [] = some pty₁)
    (hRes₁ : resolveSyntheticSubplace cx slots (cx.ptrOf pv₁) pty₁ false = .ok (l, q))
    (hPtr₂ : readPlaceState slots ⟨l, q⟩ = .ok (.ptr pv₂ sz₂))
    (hTy₂ : cx.ptrTyAt l q = some pty₂)
    (hRes₂ : resolveSyntheticSubplace cx slots (cx.ptrOf pv₂) pty₂ false = .ok (l₂, q₂))
    (hRest : projectionHasDeref rest = false) :
    evalDerefPlaceRead cx slots ⟨pp, .deref :: .deref :: rest⟩ =
      liftRead (readPlaceState slots ⟨l₂, q₂ ++ rest⟩) := by
  have hOw₁ : (false && (.deref :: rest : List ProjectionElem).isEmpty) = false := rfl
  have hOw₂ : (false && rest.isEmpty) = false := rfl
  unfold evalDerefPlaceRead resolvePlace
  simp only [hSt]
  cases stp with
  | dead => exact absurd rfl hLive
  | _ =>
    rw [derefTarget_deref hPtr₁ hTy₁ (by rw [hOw₁]; exact hRes₁),
      derefTarget_deref hPtr₂ hTy₂ (by rw [hOw₂]; exact hRes₂),
      derefTarget_noDeref cx slots false _ _ _ hRest]

/-- Witness context for two-level chains: `_0 : u32` (type `1`, at `0x1000`), `_1 : *mut u32`
(type `2`, at `0x2000`), `_2 : *mut *mut u32` (type `3`, at `0x3000`), and a `*mut u32`
temporary `_3` (at `0x4000`); every pointer designates a whole local (offset `0` with the local's
own type), so no candidate list is consulted. -/
def witnessChainCtx : SubplaceCtx where
  allocs := [some (4, 4), some (8, 8), some (8, 8), some (8, 8)]
  limit := 2 ^ 64 - 1
  layoutOf l := if l = 0 then some (.leaf 4) else if l ≤ 3 then some (.leaf 8) else none
  declTy l := if l = 0 then some 1 else if l = 1 then some 2 else if l = 2 then some 3
    else if l = 3 then some 2 else none
  candidates _ _ _ := []
  tyLayout t := if t = 1 then some ⟨4, 4, 4, true, true⟩
    else if t = 2 ∨ t = 3 then some ⟨8, 8, 8, true, true⟩ else none
  ptrTyAt l q := if q = [] then
      (if l = 1 ∨ l = 3 then some ⟨false, 1⟩ else if l = 2 then some ⟨false, 2⟩ else none)
    else none
  ptrOf pv := ⟨pv.offsetBytes, some (pv.allocId, 0)⟩
  decodeTag _ _ := none

/-- `_1 = &raw _0` and `_2 = &raw _1` as Trusted-style provenance pointers. -/
def witnessChainP0 : ProvenancePtr := { allocId := 1, offsetBytes := 0x1000 }
def witnessChainP1 : ProvenancePtr := { allocId := 2, offsetBytes := 0x2000 }

/-- The frame `_0 = 5`, `_1 = &raw _0`, `_2 = &raw _1`, `_3` uninitialized. -/
def witnessChainSlots : List LocalSlotState :=
  [.init (.scalar ⟨5, 4⟩), .init (.ptr witnessChainP0 8), .init (.ptr witnessChainP1 8), .uninit]

/-- `*_2` (the pointer `&raw _1`) resolves to the whole local `_1`. -/
theorem witnessChainCtx_resolve_P1 :
    resolveSyntheticSubplace witnessChainCtx witnessChainSlots
      (witnessChainCtx.ptrOf witnessChainP1) ⟨false, 2⟩ false = .ok (1, []) := by
  have hPtrOf : witnessChainCtx.ptrOf witnessChainP1 = ⟨0x2000, some (2, 0)⟩ := rfl
  rw [hPtrOf]
  have hP : PtrPrechecks witnessChainCtx ⟨0x2000, some (2, 0)⟩ ⟨false, 2⟩ ⟨8, 8, 8, true, true⟩ :=
    ⟨by decide, by decide, rfl, by decide, by decide, (fun h => by nomatch h), by decide⟩
  rw [resolveSyntheticSubplace_of_prechecks hP]
  have hNot : ¬ min witnessChainSlots.length witnessChainCtx.allocs.length ≤ 1 := by decide
  have hSt : witnessChainSlots[1]? = some (.init (.ptr witnessChainP0 8)) := rfl
  have hBase : localBaseAddr witnessChainCtx.allocs 1 witnessChainCtx.limit = some 0x2000 := by
    with_unfolding_all decide
  have hOwn : ownLayout witnessChainCtx.allocs 1 = some (8, 8) := rfl
  have hRoot : (0x2000 - 0x2000 = 0 ∧ witnessChainCtx.declTy 1 = some 2) := ⟨rfl, rfl⟩
  have hLt1 : ¬ (0x2000 < 0x2000) := by decide
  have hLt2 : ¬ (8 < 0x2000 - 0x2000 + 8) := by decide
  simp only [hNot, ↓reduceIte, hSt, hBase, hOwn, hLt1, hLt2, hRoot]
  rfl

/-- `&raw _0` resolves to the whole local `_0` in any frame of four slots whose `_0` is initialized
(in particular before and after the `CopyForDeref` into `_3`). -/
theorem witnessChainCtx_resolve_P0 (slots : List LocalSlotState) (hLen : slots.length = 4)
    (h0 : slots[0]? = some (.init (.scalar ⟨5, 4⟩))) :
    resolveSyntheticSubplace witnessChainCtx slots
      (witnessChainCtx.ptrOf witnessChainP0) ⟨false, 1⟩ false = .ok (0, []) := by
  have hPtrOf : witnessChainCtx.ptrOf witnessChainP0 = ⟨0x1000, some (1, 0)⟩ := rfl
  rw [hPtrOf]
  have hP : PtrPrechecks witnessChainCtx ⟨0x1000, some (1, 0)⟩ ⟨false, 1⟩ ⟨4, 4, 4, true, true⟩ :=
    ⟨by decide, by decide, rfl, by decide, by decide, (fun h => by nomatch h), by decide⟩
  rw [resolveSyntheticSubplace_of_prechecks hP]
  have hNot : ¬ min slots.length witnessChainCtx.allocs.length ≤ 0 := by
    rw [hLen]; decide
  have hBase : localBaseAddr witnessChainCtx.allocs 0 witnessChainCtx.limit = some 0x1000 := by
    with_unfolding_all decide
  have hOwn : ownLayout witnessChainCtx.allocs 0 = some (4, 4) := rfl
  have hRoot : (0x1000 - 0x1000 = 0 ∧ witnessChainCtx.declTy 0 = some 1) := ⟨rfl, rfl⟩
  have hLt1 : ¬ (0x1000 < 0x1000) := by decide
  have hLt2 : ¬ (4 < 0x1000 - 0x1000 + 4) := by decide
  simp only [hNot, ↓reduceIte, h0, hBase, hOwn, hLt1, hLt2, hRoot]
  rfl

/-- **Non-vacuity of the two-level chain split (`witness_deref_deref_split`)**: on the frame
`_0 = 5`, `_1 = &raw _0`, `_2 = &raw _1`, Anneal reads `**_2 = 5` directly, the `CopyForDeref`
of `*_2` yields `_1`'s pointer, and after storing it into the temporary `_3`, `*_3` reads the same
`5`; both places resolve to `_0`. -/
theorem witness_deref_deref_split :
    resolvePlace witnessChainCtx witnessChainSlots ⟨2, [.deref, .deref]⟩ false = .ok ⟨0, []⟩ ∧
    evalDerefPlaceRead witnessChainCtx witnessChainSlots ⟨2, [.deref, .deref]⟩ =
      .ok (.scalar ⟨5, 4⟩) ∧
    evalDerefPlaceRead witnessChainCtx witnessChainSlots ⟨2, [.deref]⟩ =
      .ok (.ptr witnessChainP0 8) ∧
    resolvePlace witnessChainCtx (witnessChainSlots.set 3 (.init (.ptr witnessChainP0 8)))
      ⟨3, [.deref]⟩ false = .ok ⟨0, []⟩ ∧
    evalDerefPlaceRead witnessChainCtx (witnessChainSlots.set 3 (.init (.ptr witnessChainP0 8)))
      ⟨3, [.deref]⟩ = .ok (.scalar ⟨5, 4⟩) := by
  have hR1 := witnessChainCtx_resolve_P1
  have hR0 := witnessChainCtx_resolve_P0 witnessChainSlots rfl rfl
  have hR0' := witnessChainCtx_resolve_P0 (witnessChainSlots.set 3 (.init (.ptr witnessChainP0 8)))
    rfl rfl
  have hP2 : readPlaceState witnessChainSlots ⟨2, []⟩ = .ok (.ptr witnessChainP1 8) := by
    with_unfolding_all rfl
  have hP1 : readPlaceState witnessChainSlots ⟨1, []⟩ = .ok (.ptr witnessChainP0 8) := by
    with_unfolding_all rfl
  obtain ⟨hS1, hS2⟩ := resolvePlace_deref_deref_split (cx := witnessChainCtx)
    (slots := witnessChainSlots) (ow := false) (pp := 2) (t := 3) (rest := [])
    (stp := .init (.ptr witnessChainP1 8)) (l := 1) (q := []) (l₂ := 0) (q₂ := [])
    rfl (by intro h; nomatch h) hP2 rfl hR1 hP1 rfl hR0 rfl (by decide) rfl hR0'
  refine ⟨hS1, ?_, ?_, hS2, ?_⟩
  · rw [evalDerefPlaceRead_deref_deref (cx := witnessChainCtx) rfl (by intro h; nomatch h) hP2
      rfl hR1 hP1 rfl hR0 rfl]
    with_unfolding_all rfl
  · rw [evalDerefPlaceRead_deref rfl (by intro h; nomatch h) hP2 rfl hR1 rfl]
    with_unfolding_all rfl
  · unfold evalDerefPlaceRead
    rw [hS2]
    with_unfolding_all rfl

end Anneal.Mir.AdtAndControl
