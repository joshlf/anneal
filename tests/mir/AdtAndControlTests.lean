-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.Mir.AdtAndControl

namespace Anneal.Mir.AdtAndControlTests

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.BitValidity
open Anneal.ByteCodec
open Anneal.Mir.PlaceAndRvalue
open Anneal.Mir.AdtAndControl

/-!
# Forward-Compatible Layout Worlds, `Stmt.evalConst` Guards, and `Deinit` Symbolic-Pad Simulation Tests (`[adv ep1-A0]`)

Kernel regression and axiom-hygiene test suite for `Anneal.Mir.AdtAndControl` Section 2e2:
1. Exercises `ForwardCompatTier`, `TCBObligationItem`, `TargetLayout`, `AdtRepr`,
   `StructLayoutWorld`, `ReprLayoutConstraint`, `ValidStructLayoutWorld`, `reprCLayoutWorld`,
   `canonicalRustLayoutWorld`, `addTrailingAlignedPad`, and `#[repr(transparent)]` uniqueness.
2. Exercises `SymbolicPairPad` ↔ `ValidStructLayoutWorld`, `ValidPairLayoutWorld`,
   `paddedPairWitness`, `reprRust_unconstrained_pad_not_intoBytes`,
   `reprRust_zst_pair_every_world_isInitCodec`, `validPairWorld_tight_isInitCodec_and_isIntoBytes`,
   `validPairWorld_tight_transmute_sound`, `reprCPaddingFree`, and `reprTransparent_pair_isInitCodec_and_isIntoBytes`.
3. Exercises $k$-field `PlacedCodecSpine` memory-order realization (`realize_validStructLayoutWorld`,
   `realize_field_windows`, `realize_validStructLayoutWorld_bitValidity`, `realizedCodec_spec`,
   `reprTransparent_struct_isIntoBytes`, `reprRust_zero_pad_of_sumSizes_eq_totalSize`,
   `reprC_struct_paddingFree_iff_isIntoBytes`, and `demoS3Placed_realizedCodec_spec`).
4. Exercises `Stmt.evalConst` size-equality guards (`evalConst_size_eq_forces_zero_pad_and_intoBytes`,
   `evalConst_structSpine_size_eq_forces_zero_pad_and_init`,
   `evalConst_structSpinePerm_size_eq_forces_zero_pad_and_init`,
   `evalConst_validWorld_size_eq_forces_zero_pad_and_init`,
   `evalConst_placedCodecSpine_size_eq_forces_zero_pad_and_init`,
   `s0_vs_s1_const_guarded_transmute_separation`, and
   `s0_vs_s1_separation_over_validStructLayoutWorlds`).
5. Exercises constructive `symbolicPadByteLayout` and `evalDeinitPlace_symbolicPad_bytes_simulation`
   / `evalDeinitPlace_symbolicPad_singleField_bytes_simulation` /
   `evalDeinitPlace_symbolicPad_sibling_bytes_preserved`.
6. Pins `#print axioms` via `#guard_msgs (whitespace := lax)` on every headline theorem,
   confirming zero `Classical.choice`, zero `sorryAx`, and zero `Lean.ofReduceBool`.
7. `[adv ep1-B1]` Exercises `MirValueCodec.ofValidStructLayoutWorld` end-to-end: a valid reordered
   `#[repr(Rust)]` world realized by a concrete `LayoutTable` entry yields Trusted-level
   `IsFromBytes` and `¬ IsIntoBytes` through the general `MirValueCodec.ofPlacedCodecSpine`.
-/

#guard reprCPaddingFree none [⟨1, 1⟩, ⟨1, 1⟩] == true
#guard reprCPaddingFree none [⟨1, 1⟩, ⟨4, 4⟩] == false
#guard reprCPaddingFree none [⟨4, 4⟩, ⟨1, 1⟩] == false
#guard demoS3Placed.realizedLead == 0
#guard demoS3Placed.realizedPads == [0, 0, 0]
#guard demoS3Placed.realizedTrail 8 == 3
#guard demoS3Placed.realizedWidth 8 == 8

/-- Concrete `ValidPairLayoutWorld` instance built from `paddedPairWitness`. -/
def concretePaddedU8U32PairWorld : ValidPairLayoutWorld .rust none ⟨1, 1⟩ ⟨4, 4⟩ where
  pad := paddedPairWitness ⟨1, 1⟩ ⟨4, 4⟩
  align := 4
  valid :=
    (paddedPairWitness_valid_and_padded (f₀ := ⟨1, 1⟩) (f₁ := ⟨4, 4⟩)
      ⟨0, rfl⟩ ⟨2, rfl⟩ (by decide)).1

theorem concretePaddedU8U32PairWorld_toSymbolicPad_pos :
    0 < concretePaddedU8U32PairWorld.toSymbolicPad.totalPad := by
  decide

/-- info: 'Anneal.Mir.AdtAndControl.reprCLayoutWorld_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reprCLayoutWorld_valid

/-- info: 'Anneal.Mir.AdtAndControl.reprC_validStructLayoutWorld_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reprC_validStructLayoutWorld_unique

/-- info: 'Anneal.Mir.AdtAndControl.reprTransparent_oneZst_offset_zero_or_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reprTransparent_oneZst_offset_zero_or_end

/-- info: 'Anneal.Mir.AdtAndControl.reprTransparent_validStructLayoutWorld_unique_of_oneZst_offsets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reprTransparent_validStructLayoutWorld_unique_of_oneZst_offsets

/-- info: 'Anneal.Mir.AdtAndControl.canonicalRustLayoutWorld_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canonicalRustLayoutWorld_valid

/-- info: 'Anneal.Mir.AdtAndControl.SymbolicPairPad.exists_of_validStructLayoutWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.AdtAndControl.SymbolicPairPad.exists_of_validStructLayoutWorld

/-- info: 'Anneal.Mir.AdtAndControl.SymbolicPairPad.toStructLayoutWorld_valid_reprRust' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.AdtAndControl.SymbolicPairPad.toStructLayoutWorld_valid_reprRust

/-- info: 'Anneal.Mir.AdtAndControl.reprRust_unconstrained_pad_not_intoBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reprRust_unconstrained_pad_not_intoBytes

/-- info: 'Anneal.Mir.AdtAndControl.reprRust_zst_pair_every_world_isInitCodec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reprRust_zst_pair_every_world_isInitCodec

/-- info: 'Anneal.Mir.AdtAndControl.validPairWorld_tight_isInitCodec_and_isIntoBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validPairWorld_tight_isInitCodec_and_isIntoBytes

/-- info: 'Anneal.Mir.AdtAndControl.validPairWorld_tight_transmute_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validPairWorld_tight_transmute_sound

/-- info: 'Anneal.Mir.AdtAndControl.reprC_pair_paddingFree_isInitCodec_and_isIntoBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reprC_pair_paddingFree_isInitCodec_and_isIntoBytes

/-- info: 'Anneal.Mir.AdtAndControl.reprC_pair_not_paddingFree_encode_uninit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reprC_pair_not_paddingFree_encode_uninit

/-- info: 'Anneal.Mir.AdtAndControl.reprTransparent_pair_isInitCodec_and_isIntoBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reprTransparent_pair_isInitCodec_and_isIntoBytes

/-- info: 'Anneal.Mir.AdtAndControl.SymbolicStructSpine.toStructLayoutWorld_valid_reprRust' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.AdtAndControl.SymbolicStructSpine.toStructLayoutWorld_valid_reprRust

/-- info: 'Anneal.Mir.AdtAndControl.validStructLayoutWorld_exists_sequential_memOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validStructLayoutWorld_exists_sequential_memOrder

/-- info: 'Anneal.Mir.AdtAndControl.maxAlign_perm_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms maxAlign_perm_eq

/-- info: 'Anneal.Mir.AdtAndControl.validStructLayoutWorld_memSort_valid_reprRust' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validStructLayoutWorld_memSort_valid_reprRust

/-- info: 'Anneal.Mir.AdtAndControl.validStructLayoutWorld_realized_by_memOrder_spine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validStructLayoutWorld_realized_by_memOrder_spine

/-- info: 'Anneal.Mir.AdtAndControl.validStructLayoutWorld_memOrder_codec_traits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validStructLayoutWorld_memOrder_codec_traits

/-- info: 'Anneal.Mir.AdtAndControl.PlacedCodecSpine.realize_validStructLayoutWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.AdtAndControl.PlacedCodecSpine.realize_validStructLayoutWorld

/-- info: 'Anneal.Mir.AdtAndControl.PlacedCodecSpine.realize_field_windows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.AdtAndControl.PlacedCodecSpine.realize_field_windows

/-- info: 'Anneal.Mir.AdtAndControl.PlacedCodecSpine.realize_validStructLayoutWorld_bitValidity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.AdtAndControl.PlacedCodecSpine.realize_validStructLayoutWorld_bitValidity

/-- info: 'Anneal.Mir.AdtAndControl.PlacedCodecSpine.realizedCodec_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.AdtAndControl.PlacedCodecSpine.realizedCodec_spec

/-- info: 'Anneal.Mir.AdtAndControl.reprTransparent_struct_isIntoBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reprTransparent_struct_isIntoBytes

/-- info: 'Anneal.Mir.AdtAndControl.reprRust_zero_pad_of_sumSizes_eq_totalSize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reprRust_zero_pad_of_sumSizes_eq_totalSize

/-- info: 'Anneal.Mir.AdtAndControl.reprC_struct_paddingFree_iff_isIntoBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reprC_struct_paddingFree_iff_isIntoBytes

/-- info: 'Anneal.Mir.AdtAndControl.demoS3World_valid' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms demoS3World_valid

/-- info: 'Anneal.Mir.AdtAndControl.demoS3_realized_field_windows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms demoS3_realized_field_windows

/-- info: 'Anneal.Mir.AdtAndControl.demoS3_realized_codec_emits_uninit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms demoS3_realized_codec_emits_uninit

/-- info: 'Anneal.Mir.AdtAndControl.demoS3Placed_realizedCodec_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms demoS3Placed_realizedCodec_spec

/-- info: 'Anneal.Mir.AdtAndControl.evalConst_size_eq_forces_zero_pad_and_intoBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalConst_size_eq_forces_zero_pad_and_intoBytes

/-- info: 'Anneal.Mir.AdtAndControl.evalConst_structSpinePerm_size_eq_forces_zero_pad_and_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalConst_structSpinePerm_size_eq_forces_zero_pad_and_init

/-- info: 'Anneal.Mir.AdtAndControl.evalConst_validWorld_size_eq_forces_zero_pad_and_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalConst_validWorld_size_eq_forces_zero_pad_and_init

/-- info: 'Anneal.Mir.AdtAndControl.evalConst_placedCodecSpine_size_eq_forces_zero_pad_and_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalConst_placedCodecSpine_size_eq_forces_zero_pad_and_init

/-- info: 'Anneal.Mir.AdtAndControl.s0_vs_s1_separation_over_validStructLayoutWorlds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms s0_vs_s1_separation_over_validStructLayoutWorlds

/-- info: 'Anneal.Mir.AdtAndControl.symbolicPadByteLayout_wf' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms symbolicPadByteLayout_wf

/-- info: 'Anneal.Mir.AdtAndControl.pathRange_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pathRange_sub

/-- info: 'Anneal.Mir.AdtAndControl.evalDeinitPlace_nested_bytes_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDeinitPlace_nested_bytes_simulation

/-- info: 'Anneal.Mir.AdtAndControl.evalDeinitPlace_symbolicPad_bytes_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDeinitPlace_symbolicPad_bytes_simulation

/-- info: 'Anneal.Mir.AdtAndControl.evalDeinitPlace_symbolicPad_singleField_bytes_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDeinitPlace_symbolicPad_singleField_bytes_simulation

/-- info: 'Anneal.Mir.AdtAndControl.evalDeinitPlace_symbolicPad_sibling_bytes_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDeinitPlace_symbolicPad_sibling_bytes_preserved

/-! ## `[adv ep1-B1]` Valid Layout Worlds → General `MirValueCodec.ofPlacedCodecSpine` -/

/--
End-to-end non-vacuity: the reordered `#[repr(Rust)]` world `demoS3World` (`u32 @ 0`, `u8 @ 4`,
`() @ 5`, size 8) is realized by the concrete `u8u32UnitPermutedLayouts` entry, so
`MirValueCodec.ofValidStructLayoutWorld` yields `IsFromBytes` but `¬ IsIntoBytes` for `(u8, u32, ())`
with no bespoke `encodeValueToBytes` / `decodeValueFromBytes` proof.
-/
theorem demoS3World_tuple_isFromBytes_not_isIntoBytes :
    IsFromBytes u8u32UnitPermutedLayouts
      { kind := .tuple [.uint .u8, .uint .u32, .tuple []], layoutIdx := 0 } ∧
    ¬ IsIntoBytes u8u32UnitPermutedLayouts
      { kind := .tuple [.uint .u8, .uint .u32, .tuple []], layoutIdx := 0 } := by
  have h := MirValueCodec.ofValidStructLayoutWorld_bitValidity demoS3World_valid
    u8u32UnitPermutedLayouts 0 u8u32UnitPermutedLayout [1, 0, 2]
    MirValueCodec.u8u32UnitPermutedPlaced (MirValueCodec.u8u32UnitPermutedFieldCodecs _)
    rfl rfl rfl rfl
  exact ⟨(h.1 ⟨FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 1 (by decide),
      FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 4 (by decide),
      FixedByteCodec.unit_isSurjectiveInitDecoder, trivial⟩).1,
    h.2.2 (by decide) (⟨0, by decide⟩, ⟨0, by decide⟩, (), ())⟩

/-- info: 'Anneal.Mir.AdtAndControl.PlacedCodecSpine.memSort_sequential_of_validStructLayoutWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.AdtAndControl.PlacedCodecSpine.memSort_sequential_of_validStructLayoutWorld

/-- info: 'Anneal.Mir.AdtAndControl.MirValueCodec.ofValidStructLayoutWorld_bitValidity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Anneal.Mir.AdtAndControl.MirValueCodec.ofValidStructLayoutWorld_bitValidity

/-- info: 'Anneal.Mir.AdtAndControlTests.demoS3World_tuple_isFromBytes_not_isIntoBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms demoS3World_tuple_isFromBytes_not_isIntoBytes

end Anneal.Mir.AdtAndControlTests
