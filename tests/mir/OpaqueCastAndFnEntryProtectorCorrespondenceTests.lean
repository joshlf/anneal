/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec
import MiniRustSpec.OpaqueCastAndFnEntryProtectorMR

/-!
# Episode 2 Correspondence Canaries & Cross-Root 3-Way Kernel Closure
# (`ProjectionElem.opaqueCast`, Callee-Only `FnEntry` Protectors `rust#166253`,
# and Machine-Backed Safe-Pointer Dereferenceability)

1. **§1 Root-Lake concrete canaries** across `D1`–`D3`: direct kernel execution
   (`decide +kernel`, independent of Episode 1 table theorems) on the REAL
   Trusted (`stepMirFn`) and MiniRust (`stepM` / `checkPtrM`) observers, codec
   round-trip / tightness / malformed-wire rejection, `D1` case `8` honest
   Trusted `.unsupported` boundary, `D1` companions (`ocCase6PayloadMir`,
   `ocCase7ProtectedDropMir`, `ocCase9DeadLocalMir`, `ocCase9InvalidBoolMir`,
   type-switch erasure boundary), `D2` mode-sensitivity (`{11, 13, 14}`) and
   `rust#166253` callee-only (`10`) vs pre-`#166253` (`11`) + reverse-transmute
   + indirect fn-ptr boundary, `D3` `some mach` vs `none` `CM.dereferenceable`
   separation + ZST dangling/null companions, the post-borrowck image (Trusted
   on the cast-erased MIR agrees with MiniRust on all 44 cells, case `8`
   included), the case-`17` fixture divergence, out-of-range fail-closed guards
   (`22`, `1000`), and root-side non-vacuous capstone instantiation.
2. **§2 Cross-root 3-way kernel closure (`run_cmd`)**: loads
   `.lake/build/lib/lean` (root) AND `examples/.lake/build/lib/lean`
   (`LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM`) into a fresh kernel
   environment, builds the genuine `OcFpLmAuthority` over `lmOcObserve`
   (translation via `LmOcFpObs.rec.{1}`, zero mocks), kernel-evaluates its
   44-cell certificate on the loop-unrolled twin `lmOcObserveU` and transports
   along `lmOcObserveU.eq_src`, discharges fail-closedness from
   `lmOcObserve_out_of_range`, closes the unified + 3 per-domain (`D1`–`D3`)
   bundles plus ALL FOUR post-borrowck bundles (`unified`, `D1`–`D3`, 8 bundles
   total; the post-borrowck gate admits every case, closing case `8`), all
   lifted theorems, observer-level (raw `MrOcFpObs`) 3-way
   agreement, 3-engine companion & UB root-cause alignment, and the Episode 2
   cross-root capstone. It also:
   - locks ALL 97 shared `section Fixtures` declarations: 93 identically-typed
     defs by `Eq.refl` (+ `mrOcCaseCount = lmOcCaseCount`), the two runner
     inductives (`OcTrustedOutcome`, `OcTrustedRun`) by constructor bijections,
     and `ocTrustedStep` / `ocRunTrustedRaw` UNIVERSALLY (every body, run
     state, and callee list) through `ocRunner_copy_lock`, whose 11 copy
     hypotheses are discharged by `Eq.refl`; the only other shared top-level
     name (`ocCombine`) is locked universally through `lmToMr`, and an
     EXHAUSTIVE audit rejects any shared MR/LM declaration without a lock;
   - closes exact 3-way raw-observer agreement on all 14 companion cells
     (`dual_companion_three_way`), the type-switch erasure boundary, and the
     `D1` static phase boundary (`dual_d1_phase_boundary`) over the REAL
     vendored-Miri companion harnesses and `lmOcPhaseObserve`, extended to
     EVERY `idx : Nat` (`dual_d1_phase_boundary_all_nat`: LeanMiri's phase
     observer is fail-closed because it factors through the `Eq.refl`-locked
     fixture table);
   - pins the lowering-dependent `D1` cells `2` / `7`
     (`dual_d1_lowering_dependent_cells`, `ocLoweringDependent_characterization`):
     LeanMiri's case `7` IS its case `5` harness (`lmCase7_is_case5_harness`,
     `Eq.refl` for every mode); vendored `Miri.Interpreter.evalOperand` treats
     `.Move` and `.Copy` identically for EVERY state/frame/place
     (`vendored_evalOperand_move_eq_copy`, `Eq.refl`), while replacing `.move`
     by `.copy` in `ocCase2Mir` turns BOTH Trusted and LeanMiri from `.ub` to
     `okScalar 7` (`lmCase2MoveAsCopy_eq`); and upstream `minimize` makes
     MiniRust return `7` on both;
   - locks LeanMiri's canonical cell `17` to its dangling-ZST companion
     harness for every mode (`lmCompanion_zstDangling_is_canonical17`) and
     closes `dual_d3_zst_fixture_divergence` (Trusted's canonical case `17` is
     a live `&()`; on the identical dangling program Trusted is `.ub`);
   - proves translation fidelity (`lmOcToVerdict = ocVerdictOf ∘ lmToMr`,
     `lmToMr`/`mrToLm` 7-constructor bijection) and locks `ocLmExpected*` to
     `lmOcExpected*.map lmToMr` by `Eq.refl`;
   - verifies EVERY forged control is REJECTED BY THE KERNEL (the rejection
     message must be a `(kernel)` type mismatch, never an elaboration or
     name-resolution accident) while its paired honest twin is ACCEPTED
     (`twins = rejected`);
   - verifies transitive reachability across Trusted, MiniRust, and vendored
     Miri.
3. **§3 Constructive purity, axiom audit, and auditor self-tests**: exhaustive
   100% choice-free `[propext, Quot.sound]` audit of
   `OpaqueCastAndFnEntryProtectorDualSpec`, standard-3-axiom + non-triviality
   audit of this module, and self-tests catching `Classical.choice`, `sorryAx`,
   `Lean.ofReduceBool`, and trivial props (`True`, `1 = 1`, `∀ x, x = x`).
-/

namespace Anneal.Mir.OpaqueCastAndFnEntryProtectorCorrespondenceTests

set_option Elab.async false

open Anneal.DualCorrespondenceBundle
open Anneal.Mir.DropBinderAndSubtypeBundle
open Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec
open MiniRustSpec.OpaqueCastAndFnEntryProtectorMR

/-! ## §1. Root-Lake Concrete Canaries -/

/-- Close an equality goal by kernel definitional reduction (`Eq.refl`, zero
`Lean.ofReduceBool`); used where the compared type has no `DecidableEq`. -/
local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq?
    | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

/-- Codec round-trip on every constructor, tightness, exact `ValidRep`
characterization, distinct tags, and malformed-wire rejection. -/
theorem oc_codec_canaries :
    ocCodec.decode (ocCodec.encode (.scalar 42)) = some (.scalar 42) ∧
    ocCodec.decode (ocCodec.encode (.retagPair 5 9)) = some (.retagPair 5 9) ∧
    ocCodec.decode (ocCodec.encode .ptrValid) = some .ptrValid ∧
    ocEncode (.scalar 0) ≠ ocEncode .ptrValid ∧
    ocEncode (.scalar 0) ≠ ocEncode (.retagPair 0 0) ∧
    ocEncode (.retagPair 0 0) ≠ ocEncode .ptrValid ∧
    ocDecode (0, 7, 1) = none ∧ ocDecode (2, 1, 0) = none ∧
    ocDecode (2, 0, 1) = none ∧ ocDecode (3, 0, 0) = none ∧
    ¬ ocValidRep (0, 7, 1) ∧ ¬ ocValidRep (2, 1, 0) ∧
    ¬ ocValidRep (2, 0, 1) ∧ ocValidRep (2, 0, 0) ∧
    ocCodec.TightValidRep := by
  refine ⟨rfl, rfl, rfl, by decide, by decide, by decide,
    rfl, rfl, rfl, rfl, id, id, id, True.intro, ocCodec_tight⟩

/-- `D1` (direct kernel execution): copy/move/assign/field/SetDiscriminant
through `.opaqueCast` match across Trusted and MiniRust (`0, 1, 3, 4, 6`),
negative UB cases (`2, 5, 7, 9`) are UB in both, flip guard `0 ≠ 2`, and case
`8` is the honest Trusted `.unsupported` deref-below-cast boundary while
MiniRust returns `okScalar 5`. -/
theorem d1_opaqueCast_canaries :
    trustedVerdict false 0 = some (.returns (.scalar 7)) ∧
    mrVerdict false 0 = some (.returns (.scalar 7)) ∧
    trustedVerdict true 1 = some (.returns (.scalar 7)) ∧
    mrVerdict true 1 = some (.returns (.scalar 7)) ∧
    trustedVerdict false 2 = some .undefinedBehavior ∧
    mrVerdict false 2 = some .undefinedBehavior ∧
    trustedVerdict false 3 = some (.returns (.scalar 42)) ∧
    mrVerdict false 3 = some (.returns (.scalar 42)) ∧
    trustedVerdict true 4 = some (.returns (.scalar 9)) ∧
    mrVerdict true 4 = some (.returns (.scalar 9)) ∧
    trustedVerdict false 5 = some .undefinedBehavior ∧
    mrVerdict false 5 = some .undefinedBehavior ∧
    trustedVerdict true 6 = some (.returns (.scalar 1)) ∧
    mrVerdict true 6 = some (.returns (.scalar 1)) ∧
    trustedVerdict false 7 = some .undefinedBehavior ∧
    mrVerdict false 7 = some .undefinedBehavior ∧
    trustedVerdict false 8 = some .unsupported ∧
    trustedVerdict true 8 = some .unsupported ∧
    mrVerdict false 8 = some (.returns (.scalar 5)) ∧
    mrVerdict true 8 = some (.returns (.scalar 5)) ∧
    trustedVerdict false 9 = some .undefinedBehavior ∧
    mrVerdict true 9 = some .undefinedBehavior ∧
    mrVerdict false 0 ≠ mrVerdict false 2 ∧
    ocClassOf 8 = .castDerefBoundary := by
  decide +kernel

/-- `D1` companions and type-switch erasure boundary (lifted Episode 1
theorems): `SetDiscriminant` payload (`ocCase6PayloadMir`), mode-sensitive
protected drop (`ocCase7ProtectedDropMir`), dead-local UB
(`ocCase9DeadLocalMir`), invalid-`bool` UB + type-switch erasure boundary
(`ocCase9InvalidBoolMir`), and upstream `minimize` contrasts. The same facts
are re-executed directly by the kernel in `companion_direct_canaries`. -/
theorem d1_companion_and_type_switch_canaries :
    type_of% mr_oc_setDiscriminant_payload_agreement ∧
    type_of% mr_oc_protected_drop_mode_sensitive ∧
    type_of% mr_oc_dead_local_ub_non_masking ∧
    type_of% mr_oc_invalid_bool_ub_non_masking ∧
    type_of% mr_oc_type_switch_erasure_boundary ∧
    type_of% mr_oc_minimize_lowering_contrasts :=
  ⟨mr_oc_setDiscriminant_payload_agreement,
   mr_oc_protected_drop_mode_sensitive,
   mr_oc_dead_local_ub_non_masking,
   mr_oc_invalid_bool_ub_non_masking,
   mr_oc_type_switch_erasure_boundary,
   mr_oc_minimize_lowering_contrasts⟩

/-- **Companions (direct kernel execution, independent of every Episode 1
theorem)**: real Trusted `stepMirFn` and real MiniRust `stepM` / `checkPtrM` on
all 7 companion fixtures in both modes.
* `payload` (`ocCase6PayloadMir`): `7` everywhere;
* `protectedDrop` (`ocCase7ProtectedDropMir`): `7` in `basic`, UB under Tree
  Borrows;
* `deadLocal` (`ocCase9DeadLocalMir`) and `invalidBool`
  (`ocCase9InvalidBoolMir`): UB everywhere, while Trusted on the cast-ERASED
  invalid-`bool` image returns the invalid byte `2` (type-switch erasure
  boundary);
* `revTransmute` (`ocCase13RevTransmuteMir`): `(5, 5)` in `basic`, UB under
  Tree Borrows;
* `zstDangling` (`ocCase17DanglingZstMir`): MiniRust accepts, Trusted rejects
  conservatively (the single companion boundary);
* `zstNull` (`ocCase18ZstNullMir`): UB everywhere. -/
theorem companion_direct_canaries :
    trustedCompanion false .payload = .okScalar 7 ∧
    trustedCompanion true .payload = .okScalar 7 ∧
    mrCompanion false .payload = .okScalar 7 ∧
    mrCompanion true .payload = .okScalar 7 ∧
    trustedCompanion false .protectedDrop = .okScalar 7 ∧
    trustedCompanion true .protectedDrop = .ub ∧
    mrCompanion false .protectedDrop = .okScalar 7 ∧
    mrCompanion true .protectedDrop = .ub ∧
    trustedCompanion false .deadLocal = .ub ∧
    mrCompanion true .deadLocal = .ub ∧
    trustedCompanion false .invalidBool = .ub ∧
    mrCompanion false .invalidBool = .ub ∧
    mrCompanion true .invalidBool = .ub ∧
    mrOcTrustedObsOf .scalar
      (ocRunTrustedRaw (ocEraseBody ocCase9InvalidBoolMir) []) = .okScalar 2 ∧
    trustedCompanion false .revTransmute = .okRetagPair 5 5 ∧
    trustedCompanion true .revTransmute = .ub ∧
    mrCompanion false .revTransmute = .okRetagPair 5 5 ∧
    mrCompanion true .revTransmute = .ub ∧
    trustedCompanion false .zstDangling = .ub ∧
    mrCompanion false .zstDangling = .okPtrValid ∧
    mrCompanion true .zstDangling = .okPtrValid ∧
    trustedCompanion true .zstNull = .ub ∧
    mrCompanion false .zstNull = .ub ∧
    mrCompanion true .zstNull = .ub ∧
    trustedCompanion false .protectedDrop ≠ trustedCompanion true .protectedDrop ∧
    mrCompanion false .revTransmute ≠ mrCompanion true .revTransmute := by
  decide +kernel

/-- **`D1` static phase boundary (direct kernel execution)**: the real
`MiniRustSpec.Correspondence.translatePlace` fails closed on every cast-bearing
place of every `D1` fixture (`0..9` are `phaseBoundary`), no `D2` / `D3` fixture
carries a cast, out-of-range indices fail closed, and yet the runtime
observers execute the same `D1` cases (flip guard `phase 0 ≠ runtime 0`). -/
theorem d1_phase_boundary_canaries :
    (List.range 22).map mrOcPhaseObserve = ocPhaseExpected ∧
    mrOcPhaseObserve 0 = .phaseBoundary ∧ mrOcPhaseObserve 8 = .phaseBoundary ∧
    mrOcPhaseObserve 9 = .phaseBoundary ∧ mrOcPhaseObserve 10 = .unsupported ∧
    mrOcPhaseObserve 21 = .unsupported ∧ mrOcPhaseObserve 22 = .unsupported ∧
    mrOcPhaseObserve 0 ≠ mrOcObserve false 0 ∧
    mrOcPhaseObserve 0 ≠ mrOcTrustedObserve false 0 ∧
    lmPhaseCheckOf (fun o => o) mrOcPhaseObserve = true ∧
    lmPhaseCheckOf (fun o => o) (mrOcObserve false) = false ∧
    mrOcPhaseCompanion .payload = .phaseBoundary ∧
    mrOcPhaseCompanion .protectedDrop = .phaseBoundary ∧
    mrOcPhaseCompanion .deadLocal = .phaseBoundary ∧
    mrOcPhaseCompanion .invalidBool = .phaseBoundary ∧
    mrOcPhaseCompanion .revTransmute = .unsupported ∧
    mrOcPhaseCompanion .zstDangling = .unsupported ∧
    mrOcPhaseCompanion .zstNull = .unsupported ∧
    lmPhaseCompanionCheckOf (fun o => o) mrOcPhaseCompanion = true ∧
    lmPhaseCompanionCheckOf (fun o => o) (mrCompanion false) = false := by
  decide +kernel

/-- **Post-borrowck image (direct kernel execution)**: Trusted `stepMirFn` on
the cast-erased image agrees with MiniRust on ALL 44 cells; case `8` reads `5`
there while the cast fixture stays honestly `.unsupported`; case `8` is the
ONLY in-range case where cast erasure changes Trusted's observation; the
post-borrowck gate admits case `8` while the cast-image gate excludes it; and
out-of-range indices fail closed. -/
theorem post_borrowck_canaries :
    trustedPostBorrowckObserve false 8 = .okScalar 5 ∧
    trustedPostBorrowckObserve true 8 = .okScalar 5 ∧
    mrOcTrustedObserve false 8 = .unsupported ∧
    mrOcObserve false 8 = .okScalar 5 ∧
    (List.range 22).map (trustedPostBorrowckObserve false) =
      (List.range 22).map (mrOcObserve false) ∧
    (List.range 22).map (trustedPostBorrowckObserve true) =
      (List.range 22).map (mrOcObserve true) ∧
    (List.range 22).filter (fun i =>
      decide (mrOcTrustedObserve false i ≠ trustedPostBorrowckObserve false i)) =
      [8] ∧
    postBorrowckGate none 8 = true ∧ mrGate none 8 = false ∧
    trustedPostBorrowckObserve true 22 = .unsupported ∧
    trustedPostBorrowckVerdict false 8 = some (.returns (.scalar 5)) ∧
    trustedVerdict false 8 = some .unsupported := by
  decide +kernel

/-- **Uniform cast erasure and cast-free fixture identity (direct kernel
execution)**: `trustedUniformErasedObserve` (zero `if idx < 10` case split)
agrees with `mrOcObserve` on all 44 cells and fails closed out of range; every
`D1` fixture (`0..9`) and `D1` companion carries a `.opaqueCast` place erased
to none by `ocEraseBody`, while every `D2`/`D3` fixture (`10..21`) and
`D2`/`D3` companion carries zero `.opaqueCast` places. -/
theorem uniform_erased_and_cast_free_canaries :
    (List.range 22).map (trustedUniformErasedObserve false) =
      (List.range 22).map (mrOcObserve false) ∧
    (List.range 22).map (trustedUniformErasedObserve true) =
      (List.range 22).map (mrOcObserve true) ∧
    trustedUniformErasedObserve false 8 = .okScalar 5 ∧
    trustedUniformErasedObserve true 22 = .unsupported ∧
    (List.range 10).all (fun i =>
      match ocCaseFixture? i with
      | some (b, []) =>
        (ocBodyPlaces b).any ocPlaceHasCast &&
        !((ocBodyPlaces (ocEraseBody b)).any ocPlaceHasCast)
      | _ => false) = true ∧
    (List.range 12).all (fun k =>
      match ocCaseFixture? (k + 10) with
      | some (b, cs) =>
        !((ocBodyPlaces b).any ocPlaceHasCast) &&
        cs.all (fun c => !((ocBodyPlaces c).any ocPlaceHasCast))
      | _ => false) = true ∧
    allOcFpCompanions.all (fun c =>
      (ocBodyPlaces (ocCompanionBody c)).any ocPlaceHasCast ==
        ocCompanionIsD1 c) = true := by
  decide +kernel

/-- **Lowering-dependent `D1` cells (direct kernel execution)**: canonical
cases `2` and `7` are `.ub` on Trusted and MiniRust, yet under upstream
`minimize` lowering MiniRust returns `7` on both; MiniRust's case `7` run is
its case `5` run; and only Trusted's fixture `7` carries a `Drop` terminator. -/
theorem d1_lowering_dependent_canaries :
    mrOcTrustedObserve false 2 = .ub ∧ mrOcObserve true 2 = .ub ∧
    mrOcTrustedObserve true 7 = .ub ∧ mrOcObserve false 7 = .ub ∧
    ocRun false [] ocMrProg2Minimize = .okScalar 7 ∧
    ocRun true [] ocMrProg7Minimize = .okScalar 7 ∧
    mrOcObserve true 7 = mrOcObserve true 5 ∧
    ocBodyHasDrop ocCase7Mir = true ∧ ocBodyHasDrop ocCase5Mir = false ∧
    ocBodyHasDrop ocCase7ProtectedDropMir = true ∧
    allOcFpCompanions.filter (fun c => ocBodyHasDrop (ocCompanionBody c)) =
      [.protectedDrop] ∧
    ocLoweringDependent 2 = true ∧ ocLoweringDependent 7 = true ∧
    ocLoweringDependent 5 = false ∧ ocLoweringDependent 8 = false ∧
    mrOcTrustedObsOf .scalar
      (ocRunTrustedRaw (ocMoveToCopyBody ocCase2Mir) []) = .okScalar 7 ∧
    mrOcTrustedObsOf .scalar
      (ocRunTrustedRaw (ocDropToNopBody ocCase7Mir) []) = .okScalar 7 := by
  decide +kernel

/-- **Fuel audit (direct kernel execution)**: Trusted's case-`8` boundary is
the genuine `.unsupported` step node (tag `2`), not fuel exhaustion (tag `3`),
in both modes; neighbouring cells end in `ret` / `ub`; and out-of-range
indices have no raw run at all. -/
theorem trusted_fuel_audit_canaries :
    (trustedRawOutcome false 8).map ocOutcomeTag = some 2 ∧
    (trustedRawOutcome true 8).map ocOutcomeTag = some 2 ∧
    (trustedRawOutcome false 0).map ocOutcomeTag = some 0 ∧
    (trustedRawOutcome true 11).map ocOutcomeTag = some 1 ∧
    (trustedRawOutcome false 21).map ocOutcomeTag = some 1 ∧
    (trustedRawOutcome true 22).isNone = true ∧
    trustedRawAuxOutcomes.length = 29 ∧
    mrProgStopsWithinFuel false ocMrProg0 120 = true ∧
    mrProgStopsWithinFuel true ocMrProg11 120 = true ∧
    mrProgStopsWithinFuel false ocMrProg0 1 = false ∧
    mrOcTrustedObserve true 8 = .unsupported := by
  decide +kernel

/-- **Case `17` fixture divergence (direct kernel execution)**: MiniRust's
canonical cell `17` IS its dangling-ZST companion, Trusted's canonical cell
`17` (a live `&()`) is `okPtrValid`, and Trusted on the identical dangling
program is conservatively `.ub`. -/
theorem d3_case17_fixture_divergence_canaries :
    mrCompanion false .zstDangling = mrOcObserve false 17 ∧
    mrCompanion true .zstDangling = mrOcObserve true 17 ∧
    mrOcObserve false 17 = .okPtrValid ∧
    mrOcTrustedObserve false 17 = .okPtrValid ∧
    trustedCompanion false .zstDangling = .ub ∧
    trustedCompanion true .zstDangling ≠ mrOcTrustedObserve true 17 := by
  decide +kernel

/-- `D2` (direct kernel execution): callee-only `rust#166253` (`10`) succeeds
in BOTH modes (`okRetagPair 5 5`), pre-`#166253` caller-retag (`11`) and
protected foreign writes (`13`, `14`) are mode-sensitive (`basic` OK, TB UB),
released-protector writes (`12`, `15`) succeed in both modes, plus
reverse-transmute mode sensitivity and Trusted indirect fn-ptr boundary. -/
theorem d2_fnentry_protector_canaries :
    trustedVerdict false 10 = some (.returns (.retagPair 5 5)) ∧
    trustedVerdict true 10 = some (.returns (.retagPair 5 5)) ∧
    mrVerdict false 10 = some (.returns (.retagPair 5 5)) ∧
    mrVerdict true 10 = some (.returns (.retagPair 5 5)) ∧
    trustedVerdict false 11 = some (.returns (.retagPair 5 5)) ∧
    trustedVerdict true 11 = some .undefinedBehavior ∧
    mrVerdict false 11 = some (.returns (.retagPair 5 5)) ∧
    mrVerdict true 11 = some .undefinedBehavior ∧
    trustedVerdict true 12 = some (.returns (.retagPair 4 9)) ∧
    mrVerdict true 12 = some (.returns (.retagPair 4 9)) ∧
    trustedVerdict false 13 = some (.returns (.retagPair 5 5)) ∧
    trustedVerdict true 13 = some .undefinedBehavior ∧
    mrVerdict false 13 = some (.returns (.retagPair 5 5)) ∧
    mrVerdict true 13 = some .undefinedBehavior ∧
    trustedVerdict false 14 = some (.returns (.retagPair 5 5)) ∧
    trustedVerdict true 14 = some .undefinedBehavior ∧
    mrVerdict false 14 = some (.returns (.retagPair 5 5)) ∧
    mrVerdict true 14 = some .undefinedBehavior ∧
    trustedVerdict true 15 = some (.returns (.retagPair 3 9)) ∧
    mrVerdict true 15 = some (.returns (.retagPair 3 9)) ∧
    mrVerdict false 11 ≠ mrVerdict true 11 ∧
    mrVerdict false 13 ≠ mrVerdict true 13 ∧
    mrVerdict false 14 ≠ mrVerdict true 14 ∧
    mrVerdict true 10 ≠ mrVerdict true 11 := by
  decide +kernel

/-- `D2` companions (lifted Episode 1 theorems): reverse-transmutation mode
sensitivity, Trusted indirect fn-ptr transmute boundary, and machine-level
`steps`/`stepsTB` contrast; re-executed directly by the kernel in
`d2_indirect_fnptr_direct_canaries`. -/
theorem d2_indirect_and_rev_transmute_canaries :
    type_of% mr_oc_d2_rev_transmute_mode_sensitive ∧
    type_of% trusted_d2_indirect_fnptr_calls ∧
    type_of% dual_d2_machine_termination_contrast :=
  ⟨mr_oc_d2_rev_transmute_mode_sensitive,
   trusted_d2_indirect_fnptr_calls,
   dual_d2_machine_termination_contrast⟩

/-- **`D2` indirect / transmuted fn-ptr boundary (direct kernel execution of
real Trusted `stepMirFn`)**: an exact-signature indirect call of the
callee-only `fn(*mut u8, *mut u8)` returns `(5, 5)`; the `&mut u8`-retagging
callee is UB under Tree Borrows and `(5, 5)` on its no-borrow-tracker image;
the fn-ptr `transmute` itself succeeds in both directions, whereas CALLING the
transmuted pointer is UB in both directions (Trusted compares call-site
signatures syntactically), while MiniRust's transmuted call of case `10`
succeeds in both modes; and the unmodified MiniRust step drivers terminate
cleanly on the callee-only program in both modes but not on case `11` under
Tree Borrows. -/
theorem d2_indirect_fnptr_direct_canaries :
    mrOcTrustedObsOf .pair (ocRunTrustedRaw
      (ocIndirectMain "oc::case10_callee" ocFnRawSigTy ocFnRawSigTy)
      [ocCase10Callee]) = .okRetagPair 5 5 ∧
    mrOcTrustedObsOf .pair (ocRunTrustedRaw
      (ocIndirectMain "oc::case11_callee" ocFnRefSigTy ocFnRefSigTy)
      [ocCase11Callee]) = .ub ∧
    mrOcTrustedObsOf .pair (ocRunTrustedRaw
      (ocIndirectMain "oc::case11_callee" ocFnRefSigTy ocFnRefSigTy)
      [ocEraseRetags ocCase11Callee]) = .okRetagPair 5 5 ∧
    mrOcTrustedObsOf .scalar (ocRunTrustedRaw
      (ocIndirectTransmuteOnly "oc::case10_callee" ocFnRawSigTy ocFnRefSigTy)
      [ocCase10Callee]) = .okScalar 1 ∧
    mrOcTrustedObsOf .scalar (ocRunTrustedRaw
      (ocIndirectTransmuteOnly "oc::case11_callee" ocFnRefSigTy ocFnRawSigTy)
      [ocCase11Callee]) = .okScalar 1 ∧
    mrOcTrustedObsOf .pair (ocRunTrustedRaw
      (ocIndirectMain "oc::case10_callee" ocFnRawSigTy ocFnRefSigTy)
      [ocCase10Callee]) = .ub ∧
    mrOcTrustedObsOf .pair (ocRunTrustedRaw
      (ocIndirectMain "oc::case11_callee" ocFnRefSigTy ocFnRawSigTy)
      [ocEraseRetags ocCase11Callee]) = .ub ∧
    mrOcObserve false 10 = .okRetagPair 5 5 ∧
    mrOcObserve true 10 = .okRetagPair 5 5 ∧
    ocTerminatesCleanly false ocMrProg10 = true ∧
    ocTerminatesCleanly true ocMrProg10 = true ∧
    ocTerminatesCleanly false ocMrProg11 = true ∧
    ocTerminatesCleanly true ocMrProg11 = false := by
  decide +kernel

/-- **`Mach` driver identity (universal, unconditional)**: on `BasicMemory`
the driver behind `mrOcObserve false` is MiniRust's own `steps`, for EVERY
fuel and machine. Discharges the hypothesis of the constructive
`steps_eq_runToStopM_bm_of` with the upstream specialization lemma
`MiniRustSpec.Correspondence.stepM_bm_eq` (the single place where its
`Classical.choice` enters, kept out of the 100% constructive `DualSpec`). -/
theorem bm_driver_is_minirust_steps (fuel : Nat) (m : MiniRustSpec.Interp.Mach) :
    MiniRustSpec.Interp.steps fuel m =
      stopProj (MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM
        (M := MiniRustSpec.Interp.BM) fuel m) :=
  steps_eq_runToStopM_bm_of MiniRustSpec.Correspondence.stepM_bm_eq fuel m

/-- `D3` (direct kernel execution): valid `&u32` (`16`) and ZST `&()` (`17`)
return `okPtrValid`; null (`18`), unaligned (`19`), OOB (`20`), and freed (`21`)
are UB in both Trusted and MiniRust; flip guard `16 ≠ 18`. -/
theorem d3_safe_ptr_dereferenceable_canaries :
    trustedVerdict false 16 = some (.returns .ptrValid) ∧
    mrVerdict false 16 = some (.returns .ptrValid) ∧
    trustedVerdict true 17 = some (.returns .ptrValid) ∧
    mrVerdict true 17 = some (.returns .ptrValid) ∧
    trustedVerdict false 18 = some .undefinedBehavior ∧
    mrVerdict true 18 = some .undefinedBehavior ∧
    trustedVerdict true 19 = some .undefinedBehavior ∧
    mrVerdict false 19 = some .undefinedBehavior ∧
    trustedVerdict false 20 = some .undefinedBehavior ∧
    mrVerdict true 20 = some .undefinedBehavior ∧
    trustedVerdict true 21 = some .undefinedBehavior ∧
    mrVerdict false 21 = some .undefinedBehavior ∧
    mrVerdict false 16 ≠ mrVerdict false 18 := by
  decide +kernel

/-- `D3` `some mach` vs `none` `CM.dereferenceable` separation on `Mach` and
`MachTB` plus ZST dangling/null companions (lifted Episode 1 theorems);
re-executed directly by the kernel in `d3_some_vs_none_direct_canaries`. -/
theorem d3_some_vs_none_and_zst_canaries :
    type_of% mr_checkPtr_some_vs_none_contrast ∧
    type_of% mr_checkPtrM_tb_some_vs_none_contrast ∧
    type_of% mr_oc_d3_zst_dangling_and_null :=
  ⟨mr_checkPtr_some_vs_none_contrast,
   mr_checkPtrM_tb_some_vs_none_contrast,
   mr_oc_d3_zst_dangling_and_null⟩

section D3Direct
open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
open MiniRustSpec.CrossFrameRefAndPanicMR MiniRustSpec.WideDstAndMaybeUninitMR

/-- **`D3` exact `some mach` vs `none` separation (direct kernel execution of
real `checkPtr` on `Mach` and `checkPtrM` on `MachTB`)**:
* valid `&u32` (`16`): `.ok ()` WITH the machine, `Stop.unsupported` without;
* out-of-bounds (`20`) and freed (`21`): exact `CM.dereferenceable`
  `Stop.ub` WITH the machine, `Stop.unsupported` without;
* null (`18`) and unaligned (`19`): `Stop.ub` both ways (never
  `Stop.unsupported`);
* ZST `&()` (`17`): `.ok ()` both ways. -/
theorem d3_some_vs_none_direct_canaries :
    ocCheckPtrContrast ocMrProg16 (.Ref .Immutable u32Pointee) =
      some (.ok (),
        unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrContrast ocMrProg17 (.Ref .Immutable ocMrUnitPointee) =
      some (.ok (), .ok ()) ∧
    ocCheckPtrContrast ocMrProg18 (.Ref .Immutable u32Pointee) =
      some (ub "Value::Ptr: null safe pointer",
        ub "Value::Ptr: null safe pointer") ∧
    ocCheckPtrContrast ocMrProg19 (.Box u32Pointee) =
      some (ub "Value::Ptr: unaligned safe pointer",
        ub "Value::Ptr: unaligned safe pointer") ∧
    ocCheckPtrContrast ocMrProg20 (.Ref .Immutable u32Pointee) =
      some (ub "Value::Ptr: non-dereferenceable safe pointer",
        unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrContrast ocMrProg21 (.Box u32Pointee) =
      some (ub "Value::Ptr: non-dereferenceable safe pointer",
        unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrMContrastTB ocMrProg16 (.Ref .Immutable u32Pointee) =
      some (.ok (),
        unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrMContrastTB ocMrProg17 (.Box ocMrUnitPointee) =
      some (.ok (), .ok ()) ∧
    ocCheckPtrMContrastTB ocMrProg18 (.Ref .Immutable ocMrUnitPointee) =
      some (ub "Value::Ptr: null safe pointer",
        ub "Value::Ptr: null safe pointer") ∧
    ocCheckPtrMContrastTB ocMrProg19 (.Ref .Immutable u32Pointee) =
      some (ub "Value::Ptr: unaligned safe pointer",
        ub "Value::Ptr: unaligned safe pointer") ∧
    ocCheckPtrMContrastTB ocMrProg20 (.Ref .Immutable u32Pointee) =
      some (ub "Value::Ptr: non-dereferenceable safe pointer",
        unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrMContrastTB ocMrProg21 (.Box u32Pointee) =
      some (ub "Value::Ptr: non-dereferenceable safe pointer",
        unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

end D3Direct

/-- Fail-closed out-of-range cells (`22`, `1000`) on Trusted and MiniRust
(direct kernel execution), and the exact class layout: 21 `threeWay`, `[8]`
`castDerefBoundary`, and `{11, 13, 14}` mode-sensitive. -/
theorem out_of_range_and_class_canaries :
    trustedVerdict false 22 = some .unsupported ∧
    mrVerdict true 22 = some .unsupported ∧
    trustedVerdict true 1000 = some .unsupported ∧
    mrVerdict false 1000 = some .unsupported ∧
    ((List.range 22).filter (fun i => ocClassOf i == .threeWay)).length = 21 ∧
    ((List.range 22).filter (fun i => ocClassOf i == .castDerefBoundary)) = [8] ∧
    ((List.range 22).filter ocCaseModeSensitive) = [11, 13, 14] ∧
    ocClassOf 22 = .outOfRange := by
  decide +kernel

/-- Root-side instantiation of BOTH capstones at the real-observer-backed
authority, companion observer, and MiniRust phase observer (non-vacuity of all
capstone hypotheses). -/
theorem root_capstone_instantiation :
    lmTableCheckOf rootBackedLmAuthority = true ∧
    (∀ sel, lmCheckOf sel rootBackedLmAuthority = true) ∧
    type_of% (projectPositive rootBackedLmAuthority
      rootBackedLmAuthority_tableCheck) ∧
    type_of% (projectFault rootBackedLmAuthority
      rootBackedLmAuthority_tableCheck) ∧
    type_of% ep2_opaquecast_fnentry_dual_authority_capstone_nonvacuous ∧
    lmCompanionCheckOf (fun o => o) rootBackedCompanion = true ∧
    OcFpLmCompanionCells (fun o => o) rootBackedCompanion ∧
    lmPhaseCheckOf (fun o => o) mrOcPhaseObserve = true ∧
    lmPhaseCompanionCheckOf (fun o => o) mrOcPhaseCompanion = true ∧
    type_of% ep2_opaquecast_fnentry_companion_phase_capstone_nonvacuous ∧
    (∀ sel, lmPostBorrowckCheckOf sel rootBackedLmAuthority = true) ∧
    type_of% ep2_opaquecast_fnentry_post_borrowck_capstone_nonvacuous :=
  ⟨rootBackedLmAuthority_tableCheck,
   fun sel => lmCheckOf_of_table sel _ rootBackedLmAuthority_tableCheck,
   projectPositive _ rootBackedLmAuthority_tableCheck,
   projectFault _ rootBackedLmAuthority_tableCheck,
   ep2_opaquecast_fnentry_dual_authority_capstone_nonvacuous,
   rootBackedCompanion_check,
   rootBackedCompanion_cells, rootBackedPhase_check,
   rootBackedPhaseCompanion_check,
   ep2_opaquecast_fnentry_companion_phase_capstone_nonvacuous,
   fun sel =>
     lmPostBorrowckCheckOf_of_table sel _ rootBackedLmAuthority_tableCheck,
   ep2_opaquecast_fnentry_post_borrowck_capstone_nonvacuous⟩

/-! ## §2. Cross-Root 3-Way Kernel Closure (`MR` + `LM` + `Anneal`) -/

section CrossRootForgedControls
open Lean Meta

private structure CrossRootForgedArgs where
  authUC : Expr
  invAuth : Expr
  swapUbAuth : Expr
  swapPhaseAuth : Expr
  lmToMr : Expr
  mrOutToLm : Expr
  runnerTy : Expr
  runnerPf : Expr
  forgedRunnerTy : Expr
  forgedRunnerPf : Expr
  compObsU : Expr
  erasedULhs : Expr
  phaseCompObs : Expr
  evalOpTy : Expr
  evalOpPf : Expr
  forgedEvalOpTy : Expr
  forgedEvalOpPf : Expr
  lmStepStopped : Expr
  lmErrOutOfFuel : Expr
  nilMir : Expr
  unsV : Expr
  noneV : Expr

private def crNs : Name :=
  `Anneal.Mir.OpaqueCastAndFnEntryProtectorCorrespondenceTests.CrossRoot
private def crBNs : Name :=
  `Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec
private def crCNs : Name :=
  `Anneal.Mir.DropBinderAndSubtypeBundle.Corpus
private def crMrNs : Name :=
  `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR
private def crLmNs : Name :=
  `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM

private def crThmD (name : Name) (ty pf : Expr) : Declaration :=
  .thmDecl { name, levelParams := [], type := ty, value := pf }

private def crDefD (name : Name) (ty val : Expr) : Declaration :=
  .defnDecl { name, levelParams := [], type := ty, value := val,
              hints := .regular 0, safety := .safe }

private def crMkEq (ty l r : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) ty l r

private def crMkRefl (ty x : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) ty x

private def crEqTrue (e : Expr) : Expr :=
  crMkEq (mkConst ``Bool) e (mkConst ``Bool.true)

private def crReflTrue : Expr :=
  crMkRefl (mkConst ``Bool) (mkConst ``Bool.true)

private def crEqFalse (e : Expr) : Expr :=
  crMkEq (mkConst ``Bool) e (mkConst ``Bool.false)

private def crReflFalse : Expr :=
  crMkRefl (mkConst ``Bool) (mkConst ``Bool.false)

private def buildForgedCore (a : CrossRootForgedArgs) :
    CoreM (List (String × Declaration × Declaration)) := do
  let natTy := mkConst ``Nat
  let obsTy := mkConst (crBNs ++ `OcFpObs)
  let domNs := crBNs ++ `OcFpDomain
  let mrObsTy0 := mkConst (crMrNs ++ `MrOcFpObs)
  let lmObsTy := mkConst (crLmNs ++ `LmOcFpObs)
  let lmObsC (c : Name) : Expr := mkConst (crLmNs ++ `LmOcFpObs ++ c)
  let lmObserveU := mkConst (crLmNs ++ `lmOcObserveU)
  let optVerdTy :=
    mkApp (mkConst ``Option [0]) (mkApp (mkConst (crCNs ++ `Verdict)) obsTy)
  let listMrTy := mkApp (mkConst ``List [0]) mrObsTy0
  let tblCheck (x : Expr) := mkApp (mkConst (crBNs ++ `lmTableCheckOf)) x
  let mrObs (tb : Bool) (i : Nat) : Expr :=
    mkApp2 (mkConst (crMrNs ++ `mrOcObserve)) (toExpr tb) (mkNatLit i)
  let trObs (tb : Bool) (i : Nat) : Expr :=
    mkApp2 (mkConst (crMrNs ++ `mrOcTrustedObserve)) (toExpr tb) (mkNatLit i)
  let lmObsU (tb : Bool) (i : Nat) : Expr :=
    mkApp2 lmObserveU (toExpr tb) (mkNatLit i)
  let mrC (c : Name) : Expr := mkConst (crMrNs ++ `MrOcFpObs ++ c)
  let mrSc (n : Nat) : Expr := mkApp (mrC `okScalar) (mkNatLit n)
  let lmSc (n : Nat) : Expr := mkApp (lmObsC `okScalar) (mkNatLit n)
  let mrPair (x y : Nat) : Expr :=
    mkApp2 (mrC `okRetagPair) (mkNatLit x) (mkNatLit y)
  let lmPair (x y : Nat) : Expr :=
    mkApp2 (lmObsC `okRetagPair) (mkNatLit x) (mkNatLit y)
  let repTy ← MetaM.run' <| inferType
    (mkApp (mkConst (crBNs ++ `ocEncode))
      (mkApp (mkConst (crBNs ++ `OcFpObs.scalar)) (mkNatLit 0)))
  let optObsTy := mkApp (mkConst ``Option [0]) obsTy
  let noneObs := mkApp (mkConst ``Option.none [0]) obsTy
  let triple (x y z : Nat) : MetaM Expr := do
    mkAppM ``Prod.mk #[mkNatLit x, ← mkAppM ``Prod.mk #[mkNatLit y, mkNatLit z]]
  let scalarObs (n : Nat) :=
    mkApp (mkConst (crBNs ++ `OcFpObs.scalar)) (mkNatLit n)
  let ptrObs := mkConst (crBNs ++ `OcFpObs.ptrValid)
  let someObs (e : Expr) := mkApp2 (mkConst ``Option.some [0]) obsTy e
  let decode (t : Expr) := mkApp (mkConst (crBNs ++ `ocDecode)) t
  let encode (o : Expr) := mkApp (mkConst (crBNs ++ `ocEncode)) o
  let t071 ← MetaM.run' <| triple 0 7 1
  let t070 ← MetaM.run' <| triple 0 7 0
  let t210 ← MetaM.run' <| triple 2 1 0
  let t201 ← MetaM.run' <| triple 2 0 1
  let t200 ← MetaM.run' <| triple 2 0 0
  let t300 ← MetaM.run' <| triple 3 0 0
  let lmVerd (x : Expr) (tb : Bool) (i : Nat) : Expr :=
    mkApp3 (mkConst (crBNs ++ `OcFpLmAuthority.verdict)) x (toExpr tb) (mkNatLit i)
  let isRet (e : Expr) : Expr := mkApp2 (mkConst (crCNs ++ `isReturn)) obsTy e
  let isFault (e : Expr) : Expr := mkApp2 (mkConst (crCNs ++ `isFaultV)) obsTy e
  let mrVerd (tb : Bool) (i : Nat) : Expr :=
    mkApp2 (mkConst (crBNs ++ `mrVerdict)) (toExpr tb) (mkNatLit i)
  let trVerd (tb : Bool) (i : Nat) : Expr :=
    mkApp2 (mkConst (crBNs ++ `trustedVerdict)) (toExpr tb) (mkNatLit i)
  let capMirTy ← MetaM.run' <| inferType (mkConst (crMrNs ++ `ocCase0Mir))
  let ocBundleTy := mkConst (crBNs ++ `OcFpBundle)
  let noneSel := mkApp (mkConst ``Option.none [0]) (mkConst domNs)
  let some (.defnInfo lmChkInfo) := (← getEnv).find? (crBNs ++ `lmCheckOf)
    | throwError "cross-root: lmCheckOf definition missing"
  let checkOnOcModel := lmChkInfo.value.bindingBody!.bindingBody!.appFn!
  let allTrueGate ← MetaM.run' <|
    withLocalDeclD `sel (mkApp (mkConst ``Option [0]) (mkConst domNs)) fun sel =>
      withLocalDeclD `i (mkConst (crBNs ++ `OcFpCase)) fun i =>
        mkLambdaFVars #[sel, i] (mkConst ``Bool.true)
  let mrSideWithCase8 := mkApp3 (mkConst (crBNs ++ `sideOf))
    noneSel allTrueGate (mkConst (crBNs ++ `mrVerdictFn))
  let mrSideWithCase8Check := mkApp checkOnOcModel mrSideWithCase8
  let lmSideWithCase8 := mkApp3 (mkConst (crBNs ++ `sideOf))
    noneSel allTrueGate (mkApp (mkConst (crBNs ++ `lmVerdictFn)) a.authUC)
  let lmSideWithCase8Check := mkApp checkOnOcModel lmSideWithCase8
  let lmMapBasic := mkApp4 (mkConst ``List.map [0, 0]) lmObsTy mrObsTy0 a.lmToMr
    (mkConst (crLmNs ++ `lmOcExpectedBasic))
  let lmMapTb := mkApp4 (mkConst ``List.map [0, 0]) lmObsTy mrObsTy0 a.lmToMr
    (mkConst (crLmNs ++ `lmOcExpectedTb))
  let termClean (tb : Bool) (i : Nat) : Expr :=
    mkApp3 (mkConst (crBNs ++ `ocTerminatesCleanly))
      (toExpr tb) (mkConst (crMrNs ++ (Name.mkSimple s!"ocMrProg{i}")))
      (mkNatLit 120)
  let lmPhase0 := mkApp (mkConst (crLmNs ++ `lmOcPhaseObserve)) (mkNatLit 0)
  let erasedInvalidBoolTr :=
    mkApp2 (mkConst (crMrNs ++ `mrOcTrustedObsOf))
      (mkConst (crMrNs ++ `OcRetKind.scalar))
      (mkApp2 (mkConst (crMrNs ++ `ocRunTrustedRaw))
        (mkApp (mkConst (crMrNs ++ `ocEraseBody))
          (mkConst (crMrNs ++ `ocCase9InvalidBoolMir)))
        a.nilMir)
  let (chkTy, chk16L, chk16R, chk20L, chk20R) ← MetaM.run' do
    let thTy ← inferType (mkConst (crMrNs ++ `mr_checkPtr_some_vs_none_contrast))
    let some (c16, rest1) := thTy.and?
      | throwError "cross-root: unexpected checkPtr contrast shape"
    let some (cty, l16, r16) := c16.eq?
      | throwError "cross-root: unexpected checkPtr eq shape"
    let mut cur := rest1
    for _ in List.range 9 do
      let some (_, nxt) := cur.and?
        | throwError "cross-root: unexpected checkPtr contrast length"
      cur := nxt
    let some (c20, _) := cur.and?
      | throwError "cross-root: unexpected checkPtr case 20 shape"
    let some (_, l20, r20) := c20.eq?
      | throwError "cross-root: unexpected checkPtr case 20 eq"
    return (cty, l16, r16, l20, r20)
  return [ ("ill-typed 0 = 1",
        crThmD (crNs ++ `forged.zeroEqOne)
          (crMkEq natTy (mkNatLit 0) (mkNatLit 1)) (crMkRefl natTy (mkNatLit 0)),
        crThmD (crNs ++ `honest.zeroEqZero)
          (crMkEq natTy (mkNatLit 0) (mkNatLit 0)) (crMkRefl natTy (mkNatLit 0))),
      ("negated LM 44-cell certificate",
        crThmD (crNs ++ `forged.lmTableFalse) (crEqFalse (tblCheck a.authUC)) crReflFalse,
        crThmD (crNs ++ `honest.lmTableTrue) (crEqTrue (tblCheck a.authUC)) crReflTrue),
      ("mode-inverted LM authority (Bool.not tb) certificate",
        crThmD (crNs ++ `forged.modeInverted) (crEqTrue (tblCheck a.invAuth)) crReflTrue,
        crThmD (crNs ++ `honest.modeInvertedFalse) (crEqFalse (tblCheck a.invAuth)) crReflFalse),
      ("ub/unsupported-swapped LM translation certificate",
        crThmD (crNs ++ `forged.swappedUbTranslation)
          (crEqTrue (tblCheck a.swapUbAuth)) crReflTrue,
        crThmD (crNs ++ `honest.swappedUbTranslationFalse)
          (crEqFalse (tblCheck a.swapUbAuth)) crReflFalse),
      ("phaseBoundary/unsupported-swapped LM translation out-of-range verdict",
        crThmD (crNs ++ `forged.swappedPhaseOutOfRange)
          (crMkEq optVerdTy (lmVerd a.swapPhaseAuth false 22) a.unsV)
          (crMkRefl optVerdTy (lmVerd a.swapPhaseAuth false 22)),
        crThmD (crNs ++ `honest.swappedPhaseOutOfRangeNone)
          (crMkEq optVerdTy (lmVerd a.swapPhaseAuth false 22) a.noneV)
          (crMkRefl optVerdTy (lmVerd a.swapPhaseAuth false 22))),
      ("forged DualCorrespondenceBundle from mode-inverted LM authority",
        crDefD (crNs ++ `forged.bundleModeInverted) ocBundleTy
          (mkApp2 (mkConst (crBNs ++ `bundleOf)) a.invAuth crReflTrue),
        crDefD (crNs ++ `honest.bundleFromUnrolled) ocBundleTy
          (mkApp2 (mkConst (crBNs ++ `bundleOf)) a.authUC crReflTrue)),
      ("swapped fixture lock (ocCase0Mir = ocCase5Mir)",
        crThmD (crNs ++ `forged.swappedFixture)
          (crMkEq capMirTy (mkConst (crMrNs ++ `ocCase0Mir))
            (mkConst (crLmNs ++ `ocCase5Mir)))
          (crMkRefl capMirTy (mkConst (crMrNs ++ `ocCase0Mir))),
        crThmD (crNs ++ `honest.fixture5)
          (crMkEq capMirTy (mkConst (crMrNs ++ `ocCase5Mir))
            (mkConst (crLmNs ++ `ocCase5Mir)))
          (crMkRefl capMirTy (mkConst (crMrNs ++ `ocCase5Mir)))),
      ("forged codec decode of non-zero padding (0,7,1)",
        crThmD (crNs ++ `forged.decodePadding0)
          (crMkEq optObsTy (decode t071) (someObs (scalarObs 7)))
          (crMkRefl optObsTy (decode t071)),
        crThmD (crNs ++ `honest.decodeCanonical0)
          (crMkEq optObsTy (decode t070) (someObs (scalarObs 7)))
          (crMkRefl optObsTy (decode t070))),
      ("forged codec decode of non-zero padding (2,1,0)",
        crThmD (crNs ++ `forged.decodePadding2a)
          (crMkEq optObsTy (decode t210) (someObs ptrObs))
          (crMkRefl optObsTy (decode t210)),
        crThmD (crNs ++ `honest.decodeCanonical2a)
          (crMkEq optObsTy (decode t200) (someObs ptrObs))
          (crMkRefl optObsTy (decode t200))),
      ("forged codec decode of non-zero padding (2,0,1)",
        crThmD (crNs ++ `forged.decodePadding2b)
          (crMkEq optObsTy (decode t201) (someObs ptrObs))
          (crMkRefl optObsTy (decode t201)),
        crThmD (crNs ++ `honest.decodeCanonical2b)
          (crMkEq optObsTy (decode t201) noneObs)
          (crMkRefl optObsTy (decode t201))),
      ("forged codec decode of invalid wire tag 3",
        crThmD (crNs ++ `forged.decodeTag3)
          (crMkEq optObsTy (decode t300) (someObs (scalarObs 0)))
          (crMkRefl optObsTy (decode t300)),
        crThmD (crNs ++ `honest.decodeTag3None)
          (crMkEq optObsTy (decode t300) noneObs)
          (crMkRefl optObsTy (decode t300))),
      ("forged colliding codec encodings (scalar 0 = ptrValid)",
        crThmD (crNs ++ `forged.encodeCollision)
          (crMkEq repTy (encode (scalarObs 0)) (encode ptrObs))
          (crMkRefl repTy (encode (scalarObs 0))),
        crThmD (crNs ++ `honest.encodePtrValid)
          (crMkEq repTy (encode ptrObs) t200)
          (crMkRefl repTy (encode ptrObs))),
      ("forged case 8: Trusted computes okScalar 5 instead of unsupported",
        crThmD (crNs ++ `forged.case8TrustedOk)
          (crMkEq mrObsTy0 (trObs false 8) (mrSc 5))
          (crMkRefl mrObsTy0 (trObs false 8)),
        crThmD (crNs ++ `honest.case8TrustedUns)
          (crMkEq mrObsTy0 (trObs false 8) (mrC `unsupported))
          (crMkRefl mrObsTy0 (trObs false 8))),
      ("forged case 8: MiniRust fails closed as unsupported",
        crThmD (crNs ++ `forged.case8MrUns)
          (crMkEq mrObsTy0 (mrObs true 8) (mrC `unsupported))
          (crMkRefl mrObsTy0 (mrObs true 8)),
        crThmD (crNs ++ `honest.case8MrOk)
          (crMkEq mrObsTy0 (mrObs true 8) (mrSc 5))
          (crMkRefl mrObsTy0 (mrObs true 8))),
      ("forged case 8: LeanMiri fails closed as unsupported",
        crThmD (crNs ++ `forged.case8LmUns)
          (crMkEq lmObsTy (lmObsU true 8) (lmObsC `unsupported))
          (crMkRefl lmObsTy (lmObsU true 8)),
        crThmD (crNs ++ `honest.case8LmOk)
          (crMkEq lmObsTy (lmObsU true 8) (lmSc 5))
          (crMkRefl lmObsTy (lmObsU true 8))),
      ("forged D1 phase boundary: case 0 returns unsupported instead of phaseBoundary",
        crThmD (crNs ++ `forged.d1Phase0Uns)
          (crMkEq lmObsTy lmPhase0 (lmObsC `unsupported))
          (crMkRefl lmObsTy lmPhase0),
        crThmD (crNs ++ `honest.d1Phase0Boundary)
          (crMkEq lmObsTy lmPhase0 (lmObsC `phaseBoundary))
          (crMkRefl lmObsTy lmPhase0)),
      ("forged D1 type-switch erasure: erased ocCase9InvalidBoolMir still UB in Trusted",
        crThmD (crNs ++ `forged.erasedInvalidBoolUb)
          (crMkEq mrObsTy0 erasedInvalidBoolTr (mrC `ub))
          (crMkRefl mrObsTy0 erasedInvalidBoolTr),
        crThmD (crNs ++ `honest.erasedInvalidBoolMasks)
          (crMkEq mrObsTy0 erasedInvalidBoolTr (mrSc 2))
          (crMkRefl mrObsTy0 erasedInvalidBoolTr)),
      ("forged case 2: Trusted accepts use-after-move through cast",
        crThmD (crNs ++ `forged.case2TrAccepts) (crEqTrue (isRet (trVerd false 2))) crReflTrue,
        crThmD (crNs ++ `honest.case2TrFaults) (crEqTrue (isFault (trVerd false 2))) crReflTrue),
      ("forged case 2: MiniRust accepts use-after-move",
        crThmD (crNs ++ `forged.case2MrAccepts) (crEqTrue (isRet (mrVerd false 2))) crReflTrue,
        crThmD (crNs ++ `honest.case2MrFaults) (crEqTrue (isFault (mrVerd false 2))) crReflTrue),
      ("forged case 2: LeanMiri accepts use-after-move",
        crThmD (crNs ++ `forged.case2LmAccepts) (crEqTrue (isRet (lmVerd a.authUC false 2))) crReflTrue,
        crThmD (crNs ++ `honest.case2LmFaults) (crEqTrue (isFault (lmVerd a.authUC false 2))) crReflTrue),
      ("forged case 9: Trusted masks uninit read through cast",
        crThmD (crNs ++ `forged.case9TrAccepts) (crEqTrue (isRet (trVerd true 9))) crReflTrue,
        crThmD (crNs ++ `honest.case9TrFaults) (crEqTrue (isFault (trVerd true 9))) crReflTrue),
      ("forged case 9: LeanMiri masks uninit read",
        crThmD (crNs ++ `forged.case9LmAccepts) (crEqTrue (isRet (lmVerd a.authUC true 9))) crReflTrue,
        crThmD (crNs ++ `honest.case9LmFaults) (crEqTrue (isFault (lmVerd a.authUC true 9))) crReflTrue),
      ("forged case 10 (rust#166253 callee-only): Trusted faults under TB",
        crThmD (crNs ++ `forged.case10TrTbUb)
          (crMkEq mrObsTy0 (trObs true 10) (mrC `ub)) (crMkRefl mrObsTy0 (trObs true 10)),
        crThmD (crNs ++ `honest.case10TrTbOk)
          (crMkEq mrObsTy0 (trObs true 10) (mrPair 5 5)) (crMkRefl mrObsTy0 (trObs true 10))),
      ("forged case 10 (rust#166253 callee-only): MiniRust faults under TB",
        crThmD (crNs ++ `forged.case10MrTbUb)
          (crMkEq mrObsTy0 (mrObs true 10) (mrC `ub)) (crMkRefl mrObsTy0 (mrObs true 10)),
        crThmD (crNs ++ `honest.case10MrTbOk)
          (crMkEq mrObsTy0 (mrObs true 10) (mrPair 5 5)) (crMkRefl mrObsTy0 (mrObs true 10))),
      ("forged case 10 (rust#166253 callee-only): LeanMiri faults under TB",
        crThmD (crNs ++ `forged.case10LmTbUb)
          (crMkEq lmObsTy (lmObsU true 10) (lmObsC `ub)) (crMkRefl lmObsTy (lmObsU true 10)),
        crThmD (crNs ++ `honest.case10LmTbOk)
          (crMkEq lmObsTy (lmObsU true 10) (lmPair 5 5)) (crMkRefl lmObsTy (lmObsU true 10))),
      ("forged case 11 mode invariance (Trusted basic = treeBorrows)",
        crThmD (crNs ++ `forged.case11TrInv)
          (crMkEq mrObsTy0 (trObs false 11) (trObs true 11)) (crMkRefl mrObsTy0 (trObs false 11)),
        crThmD (crNs ++ `honest.case11TrTbUb)
          (crMkEq mrObsTy0 (trObs true 11) (mrC `ub)) (crMkRefl mrObsTy0 (trObs true 11))),
      ("forged case 11 mode invariance (MiniRust basic = treeBorrows)",
        crThmD (crNs ++ `forged.case11MrInv)
          (crMkEq mrObsTy0 (mrObs false 11) (mrObs true 11)) (crMkRefl mrObsTy0 (mrObs false 11)),
        crThmD (crNs ++ `honest.case11MrTbUb)
          (crMkEq mrObsTy0 (mrObs true 11) (mrC `ub)) (crMkRefl mrObsTy0 (mrObs true 11))),
      ("forged case 11 mode invariance (LeanMiri basic = treeBorrows)",
        crThmD (crNs ++ `forged.case11LmInv)
          (crMkEq lmObsTy (lmObsU false 11) (lmObsU true 11)) (crMkRefl lmObsTy (lmObsU false 11)),
        crThmD (crNs ++ `honest.case11LmTbUb)
          (crMkEq lmObsTy (lmObsU true 11) (lmObsC `ub)) (crMkRefl lmObsTy (lmObsU true 11))),
      ("forged case 13 mode invariance (MiniRust basic = treeBorrows)",
        crThmD (crNs ++ `forged.case13MrInv)
          (crMkEq mrObsTy0 (mrObs false 13) (mrObs true 13)) (crMkRefl mrObsTy0 (mrObs false 13)),
        crThmD (crNs ++ `honest.case13MrTbUb)
          (crMkEq mrObsTy0 (mrObs true 13) (mrC `ub)) (crMkRefl mrObsTy0 (mrObs true 13))),
      ("forged case 13 mode invariance (LeanMiri basic = treeBorrows)",
        crThmD (crNs ++ `forged.case13LmInv)
          (crMkEq lmObsTy (lmObsU false 13) (lmObsU true 13)) (crMkRefl lmObsTy (lmObsU false 13)),
        crThmD (crNs ++ `honest.case13LmTbUb)
          (crMkEq lmObsTy (lmObsU true 13) (lmObsC `ub)) (crMkRefl lmObsTy (lmObsU true 13))),
      ("forged case 14 mode invariance (Trusted basic = treeBorrows)",
        crThmD (crNs ++ `forged.case14TrInv)
          (crMkEq mrObsTy0 (trObs false 14) (trObs true 14)) (crMkRefl mrObsTy0 (trObs false 14)),
        crThmD (crNs ++ `honest.case14TrTbUb)
          (crMkEq mrObsTy0 (trObs true 14) (mrC `ub)) (crMkRefl mrObsTy0 (trObs true 14))),
      ("forged case 14 mode invariance (LeanMiri basic = treeBorrows)",
        crThmD (crNs ++ `forged.case14LmInv)
          (crMkEq lmObsTy (lmObsU false 14) (lmObsU true 14)) (crMkRefl lmObsTy (lmObsU false 14)),
        crThmD (crNs ++ `honest.case14LmTbUb)
          (crMkEq lmObsTy (lmObsU true 14) (lmObsC `ub)) (crMkRefl lmObsTy (lmObsU true 14))),
      ("forged clean termination on TB-UB case 11 (Stop.ub must fail ocTerminatesCleanly)",
        crThmD (crNs ++ `forged.termClean11Tb) (crEqTrue (termClean true 11)) crReflTrue,
        crThmD (crNs ++ `honest.termNoClean11Tb) (crEqFalse (termClean true 11)) crReflFalse),
      ("forged D3 case 16 checkPtr contrast matches case 20 OOB contrast",
        crThmD (crNs ++ `forged.d3CheckPtr16Eq20) (crMkEq chkTy chk16L chk20R) (crMkRefl chkTy chk16L),
        crThmD (crNs ++ `honest.d3CheckPtr16Exact) (crMkEq chkTy chk16L chk16R) (crMkRefl chkTy chk16L)),
      ("forged D3 case 20 OOB checkPtr contrast matches case 16 valid contrast",
        crThmD (crNs ++ `forged.d3CheckPtr20Eq16) (crMkEq chkTy chk20L chk16R) (crMkRefl chkTy chk20L),
        crThmD (crNs ++ `honest.d3CheckPtr20Exact) (crMkEq chkTy chk20L chk20R) (crMkRefl chkTy chk20L)),
      ("forged D3 case 18: LeanMiri accepts null safe pointer",
        crThmD (crNs ++ `forged.case18LmOk)
          (crMkEq lmObsTy (lmObsU false 18) (lmObsC `okPtrValid))
          (crMkRefl lmObsTy (lmObsU false 18)),
        crThmD (crNs ++ `honest.case18LmUb)
          (crMkEq lmObsTy (lmObsU false 18) (lmObsC `ub))
          (crMkRefl lmObsTy (lmObsU false 18))),
      ("forged D3 case 19: LeanMiri accepts unaligned safe pointer",
        crThmD (crNs ++ `forged.case19LmOk)
          (crMkEq lmObsTy (lmObsU false 19) (lmObsC `okPtrValid))
          (crMkRefl lmObsTy (lmObsU false 19)),
        crThmD (crNs ++ `honest.case19LmUb)
          (crMkEq lmObsTy (lmObsU false 19) (lmObsC `ub))
          (crMkRefl lmObsTy (lmObsU false 19))),
      ("forged D3 case 20: LeanMiri accepts OOB safe pointer",
        crThmD (crNs ++ `forged.case20LmOk)
          (crMkEq lmObsTy (lmObsU false 20) (lmObsC `okPtrValid))
          (crMkRefl lmObsTy (lmObsU false 20)),
        crThmD (crNs ++ `honest.case20LmUb)
          (crMkEq lmObsTy (lmObsU false 20) (lmObsC `ub))
          (crMkRefl lmObsTy (lmObsU false 20))),
      ("forged D3 case 21: LeanMiri accepts freed safe pointer",
        crThmD (crNs ++ `forged.case21LmOk)
          (crMkEq lmObsTy (lmObsU false 21) (lmObsC `okPtrValid))
          (crMkRefl lmObsTy (lmObsU false 21)),
        crThmD (crNs ++ `honest.case21LmUb)
          (crMkEq lmObsTy (lmObsU false 21) (lmObsC `ub))
          (crMkRefl lmObsTy (lmObsU false 21))),
      ("forged observer-level agreement at case 8 (LeanMiri = Trusted on 8)",
        crThmD (crNs ++ `forged.observerLevelCase8)
          (crMkEq mrObsTy0 (mkApp a.lmToMr (lmObsU false 8)) (trObs false 8))
          (crMkRefl mrObsTy0 (mkApp a.lmToMr (lmObsU false 8))),
        crThmD (crNs ++ `honest.observerLevelCase8Mr)
          (crMkEq mrObsTy0 (mkApp a.lmToMr (lmObsU false 8)) (mrObs false 8))
          (crMkRefl mrObsTy0 (mkApp a.lmToMr (lmObsU false 8)))),
      ("forged observer-level out-of-range cell 100 returns okScalar 0",
        crThmD (crNs ++ `forged.observerLevelOobOk)
          (crMkEq mrObsTy0 (mkApp a.lmToMr (lmObsU true 100)) (mrSc 0))
          (crMkRefl mrObsTy0 (mkApp a.lmToMr (lmObsU true 100))),
        crThmD (crNs ++ `honest.observerLevelOobAgree)
          (crMkEq mrObsTy0 (mkApp a.lmToMr (lmObsU true 100)) (mrObs true 100))
          (crMkRefl mrObsTy0 (mkApp a.lmToMr (lmObsU true 100)))),
      ("forged translation fidelity (lmToMr maps phaseBoundary to unsupported)",
        crThmD (crNs ++ `forged.lmToMrPhase)
          (crMkEq mrObsTy0 (mkApp a.lmToMr (lmObsC `phaseBoundary)) (mrC `unsupported))
          (crMkRefl mrObsTy0 (mkApp a.lmToMr (lmObsC `phaseBoundary))),
        crThmD (crNs ++ `honest.lmToMrPhase)
          (crMkEq mrObsTy0 (mkApp a.lmToMr (lmObsC `phaseBoundary)) (mrC `phaseBoundary))
          (crMkRefl mrObsTy0 (mkApp a.lmToMr (lmObsC `phaseBoundary)))),
      ("forged MR Corpus.Side.check admitting cast-deref boundary case 8",
        crThmD (crNs ++ `forged.mrGateIncludesCase8) (crEqTrue mrSideWithCase8Check) crReflTrue,
        crThmD (crNs ++ `honest.mrGateRejectsCase8) (crEqFalse mrSideWithCase8Check) crReflFalse),
      ("forged LM Corpus.Side.check admitting cast-deref boundary case 8",
        crThmD (crNs ++ `forged.lmGateIncludesCase8) (crEqTrue lmSideWithCase8Check) crReflTrue,
        crThmD (crNs ++ `honest.lmGateRejectsCase8) (crEqFalse lmSideWithCase8Check) crReflFalse),
      ("forged cross-mode frozen-table lock (ocLmExpectedBasic = lmOcExpectedTb.map lmToMr)",
        crThmD (crNs ++ `forged.frozenTableCrossMode)
          (crMkEq listMrTy (mkConst (crBNs ++ `ocLmExpectedBasic)) lmMapTb)
          (crMkRefl listMrTy (mkConst (crBNs ++ `ocLmExpectedBasic))),
        crThmD (crNs ++ `honest.frozenTableBasic)
          (crMkEq listMrTy (mkConst (crBNs ++ `ocLmExpectedBasic)) lmMapBasic)
          (crMkRefl listMrTy (mkConst (crBNs ++ `ocLmExpectedBasic)))),
      ("forged LM out-of-range cell 22 returns okScalar 0 instead of unsupported",
        crThmD (crNs ++ `forged.lmOutOfRangeOk)
          (crMkEq lmObsTy (lmObsU false 22) (lmSc 0))
          (crMkRefl lmObsTy (lmObsU false 22)),
        crThmD (crNs ++ `honest.lmOutOfRangeUns)
          (crMkEq lmObsTy (lmObsU false 22) (lmObsC `unsupported))
          (crMkRefl lmObsTy (lmObsU false 22))) ]

private def buildForgedExtended (a : CrossRootForgedArgs) :
    CoreM (List (String × Declaration × Declaration)) := do
  let boolTy := mkConst ``Bool
  let natTy := mkConst ``Nat
  let domNs := crBNs ++ `OcFpDomain
  let compNs := crBNs ++ `OcFpCompanion
  let compTy := mkConst compNs
  let mrObsTy0 := mkConst (crMrNs ++ `MrOcFpObs)
  let lmObsTy := mkConst (crLmNs ++ `LmOcFpObs)
  let lmOutTy := mkConst (crLmNs ++ `OcTrustedOutcome)
  let lmOutC (c : Name) : Expr := mkConst (crLmNs ++ `OcTrustedOutcome ++ c)
  let lmObsC (c : Name) : Expr := mkConst (crLmNs ++ `LmOcFpObs ++ c)
  let lmObserve := mkConst (crLmNs ++ `lmOcObserve)
  let lmObserveU := mkConst (crLmNs ++ `lmOcObserveU)
  let lmPhaseObs := mkConst (crLmNs ++ `lmOcPhaseObserve)
  let mrObs (tb : Bool) (i : Nat) : Expr :=
    mkApp2 (mkConst (crMrNs ++ `mrOcObserve)) (toExpr tb) (mkNatLit i)
  let trObs (tb : Bool) (i : Nat) : Expr :=
    mkApp2 (mkConst (crMrNs ++ `mrOcTrustedObserve)) (toExpr tb) (mkNatLit i)
  let lmObsU (tb : Bool) (i : Nat) : Expr :=
    mkApp2 lmObserveU (toExpr tb) (mkNatLit i)
  let mrC (c : Name) : Expr := mkConst (crMrNs ++ `MrOcFpObs ++ c)
  let mrSc (n : Nat) : Expr := mkApp (mrC `okScalar) (mkNatLit n)
  let lmSc (n : Nat) : Expr := mkApp (lmObsC `okScalar) (mkNatLit n)
  let mrPair (x y : Nat) : Expr :=
    mkApp2 (mrC `okRetagPair) (mkNatLit x) (mkNatLit y)
  let compC (c : Name) : Expr := mkConst (compNs ++ c)
  let trComp (tb : Bool) (c : Name) : Expr :=
    mkApp2 (mkConst (crBNs ++ `trustedCompanion)) (toExpr tb) (compC c)
  let mrComp (tb : Bool) (c : Name) : Expr :=
    mkApp2 (mkConst (crBNs ++ `mrCompanion)) (toExpr tb) (compC c)
  let lmTwinRun (twin : Name) (tb : Bool) : Expr :=
    mkApp a.lmToMr (mkApp (mkConst (crLmNs ++ `lmOcRun))
      (mkApp (mkConst (crLmNs ++ twin)) (toExpr tb)))
  let mrPhase (i : Nat) : Expr :=
    mkApp (mkConst (crBNs ++ `mrOcPhaseObserve)) (mkNatLit i)
  let noneSel := mkApp (mkConst ``Option.none [0]) (mkConst domNs)
  let selOf (d : Name) : Expr :=
    mkApp2 (mkConst ``Option.some [0]) (mkConst domNs) (mkConst (domNs ++ d))
  let domCheck (d : Name) (x : Expr) : Expr :=
    mkApp2 (mkConst (crBNs ++ `lmCheckOf)) (selOf d) x
  let pbCheck (sel x : Expr) : Expr :=
    mkApp2 (mkConst (crBNs ++ `lmPostBorrowckCheckOf)) sel x
  let compCheck (obs : Expr) : Expr :=
    mkApp3 (mkConst (crBNs ++ `lmCompanionCheckOf)) lmObsTy a.lmToMr obs
  let phaseCheck (phase : Expr) : Expr :=
    mkApp3 (mkConst (crBNs ++ `lmPhaseCheckOf)) lmObsTy a.lmToMr phase
  let phaseCompCheck (pc : Expr) : Expr :=
    mkApp3 (mkConst (crBNs ++ `lmPhaseCompanionCheckOf)) lmObsTy a.lmToMr pc
  let layoutTy ← MetaM.run' <| inferType (mkConst (crMrNs ++ `ocU8Layout))
  let lmCombine12 := mkApp a.lmToMr
    (mkApp2 (mkConst (crLmNs ++ `ocCombine)) (lmSc 1) (lmSc 2))
  let pbObs (tb : Bool) (i : Nat) : Expr :=
    mkApp2 (mkConst (crBNs ++ `trustedPostBorrowckObserve)) (toExpr tb) (mkNatLit i)
  let some (.defnInfo lmChkInfo) := (← getEnv).find? (crBNs ++ `lmCheckOf)
    | throwError "cross-root: lmCheckOf definition missing"
  let checkOnOcModel := lmChkInfo.value.bindingBody!.bindingBody!.appFn!
  let some (.defnInfo pbChkInfo) := (← getEnv).find? (crBNs ++ `lmPostBorrowckCheckOf)
    | throwError "cross-root: lmPostBorrowckCheckOf definition missing"
  let checkOnPbModel := pbChkInfo.value.bindingBody!.bindingBody!.appFn!
  let pbSideMr := mkApp3 (mkConst (crBNs ++ `sideOf)) noneSel
    (mkConst (crBNs ++ `postBorrowckGate)) (mkConst (crBNs ++ `mrVerdictFn))
  let fin8 : Expr :=
    mkApp3 (mkConst ``Fin.mk) (mkNatLit 22) (mkNatLit 8)
      (mkApp2 (mkConst ``Nat.le_add_left) (mkNatLit 9) (mkNatLit 13))
  let bodyHasCast (mirConst : Expr) : Expr :=
    mkApp3 (mkConst ``List.any [0])
      (mkConst `Trusted.Rustc.V2026_06_01.MirAst.Place)
      (mkApp (mkConst (crMrNs ++ `ocBodyPlaces)) mirConst)
      (mkConst (crMrNs ++ `ocPlaceHasCast))
  let ptrTysNil ← MetaM.run' do
    let t ← inferType (mkConst (crMrNs ++ `ocRun))
    let listTy := t.bindingBody!.bindingDomain!
    return mkApp (mkConst ``List.nil [0]) listTy.appArg!
  let mrRunNil (tb : Bool) (prog : Name) : Expr :=
    mkApp3 (mkConst (crMrNs ++ `ocRun)) (toExpr tb) ptrTysNil
      (mkConst (crMrNs ++ prog))
  let optNatTy := mkApp (mkConst ``Option [0]) (mkConst ``Nat)
  let someNat (n : Nat) : Expr :=
    mkApp2 (mkConst ``Option.some [0]) (mkConst ``Nat) (mkNatLit n)
  let rawTag (tb : Bool) (i : Nat) : Expr :=
    mkApp4 (mkConst ``Option.map [0, 0])
      (mkConst (crMrNs ++ `OcTrustedOutcome)) (mkConst ``Nat)
      (mkConst (crBNs ++ `ocOutcomeTag))
      (mkApp2 (mkConst (crBNs ++ `trustedRawOutcome)) (toExpr tb) (mkNatLit i))
  let eqCtl (what : String) (tag : Name) (ty lhs bad good : Expr) :
      String × Declaration × Declaration :=
    (what, crThmD (crNs ++ `forged ++ tag) (crMkEq ty lhs bad) (crMkRefl ty lhs),
      crThmD (crNs ++ `honest ++ tag) (crMkEq ty lhs good) (crMkRefl ty lhs))
  return [ ("forged universal runner lock (ub/unsupported-swapped outcome constructors)",
        crThmD (crNs ++ `forged.runnerUniversal) a.forgedRunnerTy a.forgedRunnerPf,
        crThmD (crNs ++ `honest.runnerUniversal) a.runnerTy a.runnerPf),
      eqCtl "forged outcome bijection (mrOutToLm ub = unsupported)"
        `outcomeBijection lmOutTy
        (mkApp a.mrOutToLm (mkConst (crMrNs ++ `OcTrustedOutcome.ub)))
        (lmOutC `unsupported) (lmOutC `ub),
      eqCtl "forged ocCombine lock (disagreeing halves combine to the first half)"
        `combineDisagree mrObsTy0 lmCombine12 (mrSc 1) (mrC `unsupported),
      ("swapped layout fixture lock (ocU8Layout = ocU32Layout)",
        crThmD (crNs ++ `forged.swappedLayout)
          (crMkEq layoutTy (mkConst (crMrNs ++ `ocU8Layout))
            (mkConst (crLmNs ++ `ocU32Layout)))
          (crMkRefl layoutTy (mkConst (crMrNs ++ `ocU8Layout))),
        crThmD (crNs ++ `honest.layoutU32)
          (crMkEq layoutTy (mkConst (crMrNs ++ `ocU32Layout))
            (mkConst (crLmNs ++ `ocU32Layout)))
          (crMkRefl layoutTy (mkConst (crMrNs ++ `ocU32Layout)))),
      eqCtl "forged case count (mrOcCaseCount = 23)" `caseCount natTy
        (mkConst (crMrNs ++ `mrOcCaseCount)) (mkNatLit 23)
        (mkConst (crLmNs ++ `lmOcCaseCount)),
      ("forged case 13 mode invariance (Trusted basic = treeBorrows)",
        crThmD (crNs ++ `forged.case13TrInv)
          (crMkEq mrObsTy0 (trObs false 13) (trObs true 13))
          (crMkRefl mrObsTy0 (trObs false 13)),
        crThmD (crNs ++ `honest.case13TrTbUb)
          (crMkEq mrObsTy0 (trObs true 13) (mrC `ub))
          (crMkRefl mrObsTy0 (trObs true 13))),
      ("forged case 14 mode invariance (MiniRust basic = treeBorrows)",
        crThmD (crNs ++ `forged.case14MrInv)
          (crMkEq mrObsTy0 (mrObs false 14) (mrObs true 14))
          (crMkRefl mrObsTy0 (mrObs false 14)),
        crThmD (crNs ++ `honest.case14MrTbUb)
          (crMkEq mrObsTy0 (mrObs true 14) (mrC `ub))
          (crMkRefl mrObsTy0 (mrObs true 14))),
      ("forged D2 per-domain side certificate from the mode-inverted LM authority",
        crThmD (crNs ++ `forged.d2ModeInverted) (crEqTrue (domCheck `d2 a.invAuth)) crReflTrue,
        crThmD (crNs ++ `honest.d1ModeInverted) (crEqTrue (domCheck `d1 a.invAuth)) crReflTrue),
      eqCtl "forged companion: Trusted protected drop succeeds under Tree Borrows"
        `compTrProtectedDrop mrObsTy0 (trComp true `protectedDrop) (mrSc 7) (mrC `ub),
      eqCtl "forged companion: MiniRust protected drop succeeds under Tree Borrows"
        `compMrProtectedDrop mrObsTy0 (mrComp true `protectedDrop) (mrSc 7) (mrC `ub),
      eqCtl "forged companion: LeanMiri protected drop succeeds under Tree Borrows"
        `compLmProtectedDrop mrObsTy0 (lmTwinRun `lmOcProtectedDropU true)
        (mrSc 7) (mrC `ub),
      eqCtl "forged companion: Trusted reverse transmute succeeds under Tree Borrows"
        `compTrRevTransmute mrObsTy0 (trComp true `revTransmute) (mrPair 5 5) (mrC `ub),
      eqCtl "forged companion: MiniRust reverse transmute succeeds under Tree Borrows"
        `compMrRevTransmute mrObsTy0 (mrComp true `revTransmute) (mrPair 5 5) (mrC `ub),
      eqCtl "forged companion: LeanMiri reverse transmute succeeds under Tree Borrows"
        `compLmRevTransmute mrObsTy0 (lmTwinRun `lmOcD2RevTransmuteU true)
        (mrPair 5 5) (mrC `ub),
      eqCtl "forged companion: Trusted masks the invalid bool through the cast"
        `compTrInvalidBool mrObsTy0 (trComp false `invalidBool) (mrSc 2) (mrC `ub),
      eqCtl "forged companion: MiniRust masks the invalid bool"
        `compMrInvalidBool mrObsTy0 (mrComp true `invalidBool) (mrSc 2) (mrC `ub),
      eqCtl "forged companion: LeanMiri type-switched read masks the invalid bool"
        `compLmInvalidBool mrObsTy0 (lmTwinRun `lmOcInvalidBoolReadU false)
        (mrSc 2) (mrC `ub),
      eqCtl "forged companion: Trusted accepts the dangling ZST (no boundary)"
        `compTrZstDangling mrObsTy0 (trComp false `zstDangling)
        (mrC `okPtrValid) (mrC `ub),
      eqCtl "forged companion: MiniRust rejects the dangling ZST"
        `compMrZstDangling mrObsTy0 (mrComp false `zstDangling)
        (mrC `ub) (mrC `okPtrValid),
      eqCtl "forged companion: MiniRust accepts the null ZST"
        `compMrZstNull mrObsTy0 (mrComp true `zstNull) (mrC `okPtrValid) (mrC `ub),
      eqCtl "forged phase boundary: cast-free D2 case 10 rejected statically"
        `phaseD2 mrObsTy0 (mrPhase 10) (mrC `phaseBoundary) (mrC `unsupported),
      eqCtl "forged phase boundary: MiniRust translates the cast places of case 8"
        `phaseCase8 mrObsTy0 (mrPhase 8) (mrC `unsupported) (mrC `phaseBoundary),
      ("forged LM phase certificate from the RUNTIME observer",
        crThmD (crNs ++ `forged.phaseFromRuntime)
          (crEqTrue (phaseCheck (mkApp lmObserveU (toExpr false)))) crReflTrue,
        crThmD (crNs ++ `honest.phaseFromRuntimeFalse)
          (crEqFalse (phaseCheck (mkApp lmObserveU (toExpr false)))) crReflFalse),
      ("forged negated LM 14-cell companion certificate",
        crThmD (crNs ++ `forged.compCheckFalse) (crEqFalse (compCheck a.compObsU)) crReflFalse,
        crThmD (crNs ++ `honest.compCheckTrue) (crEqTrue (compCheck a.compObsU)) crReflTrue),
      ("forged mode-inverted LM 14-cell companion certificate",
        crThmD (crNs ++ `forged.compCheckInverted)
          (crEqTrue (compCheck
            (mkLambda `tb .default boolTy <| mkLambda `c .default compTy <|
              mkApp2 a.compObsU (mkApp (mkConst ``Bool.not) (.bvar 1)) (.bvar 0))))
          crReflTrue,
        crThmD (crNs ++ `honest.compCheckInvertedFalse)
          (crEqFalse (compCheck
            (mkLambda `tb .default boolTy <| mkLambda `c .default compTy <|
              mkApp2 a.compObsU (mkApp (mkConst ``Bool.not) (.bvar 1)) (.bvar 0))))
          crReflFalse),
      eqCtl "forged companion twin: LM dead-local read returns okScalar 7"
        `compLmDeadLocal mrObsTy0
        (mkApp a.lmToMr (mkApp2 a.compObsU (toExpr false) (compC `deadLocal)))
        (mrSc 7) (mrC `ub),
      eqCtl "forged companion twin: LM dangling ZST rejected as UB"
        `compLmZstDangling mrObsTy0
        (mkApp a.lmToMr (mkApp2 a.compObsU (toExpr false) (compC `zstDangling)))
        (mrC `ub) (mrC `okPtrValid),
      eqCtl "forged companion twin: LM null ZST accepted as okPtrValid"
        `compLmZstNull mrObsTy0
        (mkApp a.lmToMr (mkApp2 a.compObsU (toExpr true) (compC `zstNull)))
        (mrC `okPtrValid) (mrC `ub),
      eqCtl "forged companion twin: LM erased invalid-bool is UB instead of masking byte 2"
        `compLmErasedUb mrObsTy0 (mkApp a.lmToMr a.erasedULhs)
        (mrC `ub) (mrSc 2),
      ("forged negated LM 7-companion phase certificate",
        crThmD (crNs ++ `forged.phaseCompFalse)
          (crEqFalse (phaseCompCheck a.phaseCompObs)) crReflFalse,
        crThmD (crNs ++ `honest.phaseCompTrue)
          (crEqTrue (phaseCompCheck a.phaseCompObs)) crReflTrue),
      ("forged LM companion phase certificate from RUNTIME companion observer",
        crThmD (crNs ++ `forged.phaseCompFromRuntime)
          (crEqTrue (phaseCompCheck (mkApp a.compObsU (toExpr false)))) crReflTrue,
        crThmD (crNs ++ `honest.phaseCompFromRuntimeFalse)
          (crEqFalse (phaseCompCheck (mkApp a.compObsU (toExpr false)))) crReflFalse),
      eqCtl "forged MR companion phase: cast-free revTransmute is phaseBoundary"
        `phaseCompRevTr mrObsTy0
        (mkApp (mkConst (crBNs ++ `mrOcPhaseCompanion)) (compC `revTransmute))
        (mrC `phaseBoundary) (mrC `unsupported),
      eqCtl "forged MR companion phase: D1 invalidBool is unsupported"
        `phaseCompInvBool mrObsTy0
        (mkApp (mkConst (crBNs ++ `mrOcPhaseCompanion)) (compC `invalidBool))
        (mrC `unsupported) (mrC `phaseBoundary) ] ++
    ([18, 19, 20, 21].map fun i =>
      eqCtl s!"forged D3 case {i}: Trusted accepts the invalid safe pointer"
        (Name.mkSimple s!"d3TrAccepts{i}") mrObsTy0 (trObs false i)
        (mrC `okPtrValid) (mrC `ub)) ++
    ([18, 19, 20, 21].map fun i =>
      eqCtl s!"forged D3 case {i}: MiniRust accepts the invalid safe pointer"
        (Name.mkSimple s!"d3MrAccepts{i}") mrObsTy0 (mrObs true i)
        (mrC `okPtrValid) (mrC `ub)) ++
    [ eqCtl "forged LM phase observer out of range: idx 22 rejected at the phase boundary"
        `phaseOob22 mrObsTy0
        (mkApp a.lmToMr (mkApp lmPhaseObs (mkNatLit 22)))
        (mrC `phaseBoundary) (mrC `unsupported),
      eqCtl "forged MR phase observer out of range: idx 1000 rejected at the phase boundary"
        `phaseOob1000 mrObsTy0 (mrPhase 1000)
        (mrC `phaseBoundary) (mrC `unsupported),
      eqCtl "forged post-borrowck case 8: Trusted on the erased image stays unsupported"
        `pbCase8 mrObsTy0 (pbObs false 8) (mrC `unsupported) (mrSc 5),
      eqCtl "forged cast-erasure faithfulness at case 8 (cast fixture = erased image)"
        `pbCase8Faithful mrObsTy0 (trObs false 8) (pbObs false 8)
        (mrC `unsupported),
      ("forged all-case MR gate on the CAST model (case 8 breaks Side.check)",
        crThmD (crNs ++ `forged.pbGateOnCastModel)
          (crEqTrue (mkApp checkOnOcModel pbSideMr)) crReflTrue,
        crThmD (crNs ++ `honest.pbGateOnPostBorrowckModel)
          (crEqTrue (mkApp checkOnPbModel pbSideMr)) crReflTrue),
      ("forged post-borrowck LM side certificate from the mode-inverted LM authority",
        crThmD (crNs ++ `forged.pbModeInverted)
          (crEqTrue (pbCheck noneSel a.invAuth)) crReflTrue,
        crThmD (crNs ++ `honest.pbFromUnrolled)
          (crEqTrue (pbCheck noneSel a.authUC)) crReflTrue),
      ("forged D2 post-borrowck LM side certificate from mode-inverted authority",
        crThmD (crNs ++ `forged.pbD2ModeInverted)
          (crEqTrue (pbCheck (selOf `d2) a.invAuth)) crReflTrue,
        crThmD (crNs ++ `honest.pbD1ModeInverted)
          (crEqTrue (pbCheck (selOf `d1) a.invAuth)) crReflTrue),
      eqCtl "forged uniform erased observer at case 8: stays unsupported"
        `pbUniformCase8Uns mrObsTy0
        (mkApp2 (mkConst (crBNs ++ `trustedUniformErasedObserve))
          (toExpr false) (mkNatLit 8))
        (mrC `unsupported) (mrSc 5),
      eqCtl "forged uniform erased observer out of range (idx 22): returns scalar 5"
        `pbUniformOob22Ok mrObsTy0
        (mkApp2 (mkConst (crBNs ++ `trustedUniformErasedObserve))
          (toExpr true) (mkNatLit 22))
        (mrSc 5) (mrC `unsupported),
      eqCtl "forged D1 post-borrowck gate excludes case 8"
        `pbD1Gate8 boolTy
        (mkApp2 (mkConst (crBNs ++ `postBorrowckGate)) (selOf `d1) fin8)
        (toExpr false) (toExpr true),
      eqCtl "forged D1 case 8 carries no opaqueCast place"
        `d1Case8NoCast boolTy
        (bodyHasCast (mkConst (crMrNs ++ `ocCase8Mir)))
        (toExpr false) (toExpr true),
      eqCtl "forged D2 case 10 carries an opaqueCast place"
        `d2Case10HasCast boolTy
        (bodyHasCast (mkConst (crMrNs ++ `ocCase10Mir)))
        (toExpr true) (toExpr false),
      eqCtl "forged LM case 7 follows upstream minimize (no deinit): returns 7"
        `lmCase7Minimize mrObsTy0 (mkApp a.lmToMr (lmObsU true 7))
        (mrSc 7) (mrC `ub),
      eqCtl "forged MR upstream-minimize case 7 is UB like Trusted"
        `mrCase7MinimizeUb mrObsTy0 (mrRunNil false `ocMrProg7Minimize)
        (mrC `ub) (mrSc 7),
      eqCtl "forged MR upstream-minimize case 2 is UB like Trusted"
        `mrCase2MinimizeUb mrObsTy0 (mrRunNil true `ocMrProg2Minimize)
        (mrC `ub) (mrSc 7),
      eqCtl "forged Trusted fixture 5 carries a Drop terminator"
        `case5HasDrop boolTy
        (mkApp (mkConst (crBNs ++ `ocBodyHasDrop)) (mkConst (crMrNs ++ `ocCase5Mir)))
        (toExpr true) (toExpr false),
      ("forged vendored Miri evalOperand equates Move with RuntimeChecks.UbChecks",
        crThmD (crNs ++ `forged.vendoredEvalOpMoveEqRc) a.forgedEvalOpTy a.forgedEvalOpPf,
        crThmD (crNs ++ `honest.vendoredEvalOpMoveEqCopy) a.evalOpTy a.evalOpPf),
      eqCtl "forged LM case 2 under Move-as-Copy (vendored evalOperand) is UB"
        `lmCase2MoveAsCopyUb mrObsTy0
        (mkApp a.lmToMr (mkConst (crNs ++ `lmCase2MoveAsCopyU)))
        (mrC `ub) (mrSc 7),
      eqCtl "forged Trusted case 2 under Move-as-Copy is UB"
        `trCase2MoveAsCopyUb mrObsTy0
        (mkApp2 (mkConst (crMrNs ++ `mrOcTrustedObsOf))
          (mkConst (crMrNs ++ `OcRetKind.scalar))
          (mkApp2 (mkConst (crMrNs ++ `ocRunTrustedRaw))
            (mkApp (mkConst (crBNs ++ `ocMoveToCopyBody))
              (mkConst (crMrNs ++ `ocCase2Mir)))
            a.nilMir))
        (mrC `ub) (mrSc 7),
      eqCtl "forged Trusted case 7 under Drop-as-Nop is UB"
        `trCase7DropAsNopUb mrObsTy0
        (mkApp2 (mkConst (crMrNs ++ `mrOcTrustedObsOf))
          (mkConst (crMrNs ++ `OcRetKind.scalar))
          (mkApp2 (mkConst (crMrNs ++ `ocRunTrustedRaw))
            (mkApp (mkConst (crBNs ++ `ocDropToNopBody))
              (mkConst (crMrNs ++ `ocCase7Mir)))
            a.nilMir))
        (mrC `ub) (mrSc 7),
      eqCtl "forged lowering-dependent predicate tags genuine Deinit case 5"
        `loweringDepCase5 boolTy
        (mkApp (mkConst (crBNs ++ `ocLoweringDependent)) (mkNatLit 5))
        (toExpr true) (toExpr false),
      ("forged LM case 7 equals case 6 harness for every mode",
        crThmD (crNs ++ `forged.lmCase7IsCase6)
          (mkForall `tb .default boolTy <|
            crMkEq lmObsTy (mkApp2 lmObserve (.bvar 0) (mkNatLit 7))
              (mkApp2 lmObserve (.bvar 0) (mkNatLit 6)))
          (mkLambda `tb .default boolTy <|
            crMkRefl lmObsTy (mkApp2 lmObserve (.bvar 0) (mkNatLit 7))),
        crThmD (crNs ++ `honest.lmCase7IsCase5)
          (mkForall `tb .default boolTy <|
            crMkEq lmObsTy (mkApp2 lmObserve (.bvar 0) (mkNatLit 7))
              (mkApp2 lmObserve (.bvar 0) (mkNatLit 5)))
          (mkLambda `tb .default boolTy <|
            crMkRefl lmObsTy (mkApp2 lmObserve (.bvar 0) (mkNatLit 7)))),
      -- Fuel audit: Trusted case `8` is a genuine `.unsupported` node, MiniRust
      -- stops within `fuel := 120` (and fails at `fuel := 1`), and LeanMiri's
      -- raw `lmStepStopped` rejects `StepError.unsupported "out of fuel"`.
      eqCtl "forged Trusted case 8 unsupported is fuel exhaustion (tag 3)"
        `trCase8OutOfFuel optNatTy (rawTag false 8) (someNat 3) (someNat 2),
      eqCtl "forged Trusted case 8 (Tree Borrows) raw run returns a value (tag 0)"
        `trCase8TbRet optNatTy (rawTag true 8) (someNat 0) (someNat 2),
      eqCtl "forged Trusted outOfFuel tag collapses onto unsupported (tag 2)"
        `trOutOfFuelTag natTy
        (mkApp (mkConst (crBNs ++ `ocOutcomeTag))
          (mkConst (crMrNs ++ `OcTrustedOutcome.outOfFuel)))
        (mkNatLit 2) (mkNatLit 3),
      eqCtl "forged MiniRust case 0 stops within fuel := 1 (fuel non-vacuity)"
        `mrProg0Fuel1 boolTy
        (mkApp3 (mkConst (crBNs ++ `mrProgStopsWithinFuel))
          (toExpr false) (mkConst (crMrNs ++ `ocMrProg0)) (mkNatLit 1))
        (toExpr true) (toExpr false),
      eqCtl "forged MiniRust case 0 exhausts fuel := 120"
        `mrProg0Fuel120 boolTy
        (mkApp3 (mkConst (crBNs ++ `mrProgStopsWithinFuel))
          (toExpr false) (mkConst (crMrNs ++ `ocMrProg0)) (mkNatLit 120))
        (toExpr false) (toExpr true),
      eqCtl "forged LeanMiri lmStepStopped accepts StepError.unsupported out-of-fuel"
        `lmStepStoppedOutOfFuel boolTy
        (mkApp a.lmStepStopped a.lmErrOutOfFuel)
        (toExpr true) (toExpr false) ]

private def runCrossRootForgedControls (a : CrossRootForgedArgs) :
    CoreM (Nat × Nat) := do
  let saved ← getEnv
  let rejection (d : Declaration) : CoreM (Option String) := do
    let r ← try addDecl d; pure none
      catch ex => pure (some (← ex.toMessageData.toString))
    setEnv saved
    return r
  let pairs := (← buildForgedCore a) ++ (← buildForgedExtended a)
  let mut rejected : Nat := 0
  let mut twins : Nat := 0
  for (what, d, h) in pairs do
    match ← rejection d with
    | none =>
      throwError "cross-root negative control FAILED: kernel accepted {what}"
    | some msg =>
      -- Only `(kernel) declaration type mismatch` / `(kernel) application
      -- type mismatch` count: never a name-resolution, elaboration, or
      -- resource (`deep recursion`) failure.
      unless msg.startsWith "(kernel)" &&
          (msg.splitOn "type mismatch").length > 1 do
        throwError "cross-root negative control VACUOUS: {what} was not rejected by a kernel type mismatch: {msg}"
    rejected := rejected + 1
    if let some msg ← rejection h then
      throwError "cross-root negative control VACUOUS: honest twin of {what} was rejected: {msg}"
    twins := twins + 1
  let natTy := mkConst ``Nat
  if let some msg ← rejection (crThmD (crNs ++ `honest.selfTest)
      (crMkEq natTy (mkNatLit 2) (mkNatLit 2)) (crMkRefl natTy (mkNatLit 2))) then
    throwError "cross-root control harness self-test failed: {msg}"
  return (rejected, twins)

end CrossRootForgedControls

set_option maxRecDepth 8192 in
open Lean Elab Command Meta in
run_cmd do
  let opts := (← getOptions).setBool `Elab.async false
  let sp : SearchPath :=
    [System.FilePath.mk ".lake/build/lib/lean",
     System.FilePath.mk "examples/.lake/build/lib/lean"]
  initSearchPath (← findSysroot) sp
  let baseEnv ← importModules
    #[{ module := `Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec },
      { module := `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR },
      { module := `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM }]
    {} 0
  let ns := `Anneal.Mir.OpaqueCastAndFnEntryProtectorCorrespondenceTests.CrossRoot
  let bNs := `Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec
  let cNs := `Anneal.Mir.DropBinderAndSubtypeBundle.Corpus
  let mrNs := `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR
  let lmNs := `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM
  let act : CoreM (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Array Name) := do
    let addDef (name : Name) (val : Expr) : CoreM Expr := do
      let ty ← MetaM.run' <| inferType val
      addDecl <| .defnDecl {
        name, levelParams := [], type := ty, value := val,
        hints := .regular 0, safety := .safe }
      return ty
    let addThm (name : Name) (ty pf : Expr) : CoreM Unit := do
      addDecl <| .thmDecl { name, levelParams := [], type := ty, value := pf }
    let addThmInfer (name : Name) (pf : Expr) : CoreM Unit := do
      let ty ← MetaM.run' <| inferType pf
      addThm name ty pf
    let boolTy := mkConst ``Bool
    let natTy := mkConst ``Nat
    let eqTrue (e : Expr) : Expr :=
      mkApp3 (mkConst ``Eq [1]) boolTy e (mkConst ``Bool.true)
    let reflTrue : Expr :=
      mkApp2 (mkConst ``Eq.refl [1]) boolTy (mkConst ``Bool.true)
    let mkEq (ty a b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) ty a b
    let mkRefl (ty a : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [1]) ty a

    -- 1. Genuine LeanMiri authority over `lmOcObserve` (translation via
    -- `LmOcFpObs.rec.{1}`, zero mocks).
    let obsTy := mkConst (bNs ++ `OcFpObs)
    let verdTy := mkApp (mkConst (cNs ++ `Verdict)) obsTy
    let optVerdTy := mkApp (mkConst ``Option [0]) verdTy
    let someV (e : Expr) : Expr := mkApp2 (mkConst ``Option.some [0]) verdTy e
    let noneV : Expr := mkApp (mkConst ``Option.none [0]) verdTy
    let retV (e : Expr) : Expr :=
      mkApp2 (mkConst (cNs ++ `Verdict.returns)) obsTy e
    let ubV := someV (mkApp (mkConst (cNs ++ `Verdict.undefinedBehavior)) obsTy)
    let unsV := someV (mkApp (mkConst (cNs ++ `Verdict.unsupported)) obsTy)
    let lmObsTy := mkConst (lmNs ++ `LmOcFpObs)
    let lmObsC (c : Name) : Expr := mkConst (lmNs ++ `LmOcFpObs ++ c)
    let mkToVerdict (swapUbUns : Bool) (swapPhaseUns : Bool) : MetaM Expr :=
      withLocalDeclD `o lmObsTy fun o => do
        let motive := mkLambda `x .default lmObsTy optVerdTy
        let m1 := mkLambda `v .default natTy
          (someV (retV (mkApp (mkConst (bNs ++ `OcFpObs.scalar)) (.bvar 0))))
        let m2 := mkLambda `r .default natTy <| mkLambda `v .default natTy <|
          someV (retV (mkApp2 (mkConst (bNs ++ `OcFpObs.retagPair))
            (.bvar 1) (.bvar 0)))
        let m3 := someV (retV (mkConst (bNs ++ `OcFpObs.ptrValid)))
        let m4 := if swapUbUns then unsV else ubV
        let m5 := if swapPhaseUns then unsV else noneV
        let m6 := if swapUbUns then ubV else if swapPhaseUns then noneV else unsV
        let m7 := noneV
        mkLambdaFVars #[o] (mkAppN (mkConst (lmNs ++ `LmOcFpObs.rec) [1])
          #[motive, m1, m2, m3, m4, m5, m6, m7, o])
    let toVName := ns ++ `lmOcToVerdict
    let _ ← addDef toVName (← MetaM.run' <| mkToVerdict false false)
    let toV := mkConst toVName
    let mkAuth (observe toVerdict : Expr) : Expr :=
      mkApp3 (mkConst (bNs ++ `OcFpLmAuthority.mk)) lmObsTy observe toVerdict
    let lmObserve := mkConst (lmNs ++ `lmOcObserve)
    let lmObserveU := mkConst (lmNs ++ `lmOcObserveU)
    let authName := ns ++ `lmAuthority
    let _ ← addDef authName (mkAuth lmObserve toV)
    let authC := mkConst authName
    let authUName := ns ++ `lmAuthorityU
    let _ ← addDef authUName (mkAuth lmObserveU toV)
    let authUC := mkConst authUName
    let mut added : Array Name := #[toVName, authName, authUName]

    -- 2. Certificates: kernel evaluation on the loop-unrolled twin
    -- `lmOcObserveU`, transport along `lmOcObserveU.eq_src`, and fail-closedness
    -- from `lmOcObserve_out_of_range`.
    let eqName := ns ++ `lmAuthority_eq_unrolled
    let eqPf ← MetaM.run' do
      let g ← withLocalDeclD `g (← inferType lmObserve) fun g =>
        mkLambdaFVars #[g] (mkAuth g toV)
      mkAppM ``congrArg #[g, mkConst (lmNs ++ `lmOcObserveU.eq_src)]
    addThmInfer eqName eqPf
    added := added.push eqName
    let tblUName := ns ++ `lmAuthorityU_tableCheck
    addThm tblUName (eqTrue (mkApp (mkConst (bNs ++ `lmTableCheckOf)) authUC))
      reflTrue
    added := added.push tblUName
    let tblName := ns ++ `lmAuthority_tableCheck
    addThm tblName (eqTrue (mkApp (mkConst (bNs ++ `lmTableCheckOf)) authC))
      (mkApp4 (mkConst (bNs ++ `lmTableCheckOf_of_eq))
        authC authUC (mkConst eqName) (mkConst tblUName))
    added := added.push tblName
    let hA := mkConst tblName
    let fcName := ns ++ `lmAuthority_failClosed
    let fcPf ← MetaM.run' do
      withLocalDeclD `tb boolTy fun tb => withLocalDeclD `idx natTy fun idx => do
        let le := mkApp4 (mkConst ``LE.le [0]) natTy (mkConst ``instLENat)
          (mkConst (mrNs ++ `mrOcCaseCount)) idx
        withLocalDeclD `h le fun h => do
          let oor := mkApp3 (mkConst (lmNs ++ `lmOcObserve_out_of_range))
            tb idx h
          mkLambdaFVars #[tb, idx, h] (← mkAppM ``congrArg #[toV, oor])
    addThm fcName (mkApp (mkConst (bNs ++ `OcFpLmFailClosed)) authC) fcPf
    added := added.push fcName
    let hOob := mkConst fcName

    -- Direct kernel evaluation of every LeanMiri side certificate on the twin.
    let domNs := bNs ++ `OcFpDomain
    let domains : List Name := [`d1, `d2, `d3]
    let sels : List (Name × Expr) :=
      (`unified, mkApp (mkConst ``Option.none [0]) (mkConst domNs)) ::
        domains.map fun d =>
          (d, mkApp2 (mkConst ``Option.some [0]) (mkConst domNs)
            (mkConst (domNs ++ d)))
    for (tag, sel) in sels do
      let n := ns ++ `lmSideCheckU ++ tag
      addThm n (eqTrue (mkApp2 (mkConst (bNs ++ `lmCheckOf)) sel authUC))
        reflTrue
      added := added.push n
      let n' := ns ++ `lmSideCheck ++ tag
      addThmInfer n' (mkApp3 (mkConst (bNs ++ `lmCheckOf_of_table)) sel authC hA)
      added := added.push n'

    -- 3. Close unified + 3 per-domain bundles, lifted theorems, and capstone.
    let unifiedName := ns ++ `unifiedDualBundle
    let uTy ← addDef unifiedName (mkApp2 (mkConst (bNs ++ `bundleOf)) authC hA)
    unless uTy.getAppFn.isConstOf
        ``Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle ||
        uTy.isConstOf (bNs ++ `OcFpBundle) do
      throwError "cross-root: {unifiedName} is not a DualCorrespondenceBundle"
    added := added.push unifiedName
    let mut bundleCount : Nat := 1
    for d in domains do
      let n := ns ++ `domainBundle ++ d
      let _ ← addDef n
        (mkApp3 (mkConst (bNs ++ `domainBundleOf)) (mkConst (domNs ++ d)) authC hA)
      added := added.push n
      bundleCount := bundleCount + 1
      addThmInfer (ns ++ `domainClaims ++ d)
        (mkApp3 (mkConst (bNs ++ `domain_bundle_claims))
          (mkConst (domNs ++ d)) authC hA)
      added := added.push (ns ++ `domainClaims ++ d)
      for proj in [``DualCorrespondenceBundle.projectPositive,
                   ``DualCorrespondenceBundle.projectFault] do
        let pv ← MetaM.run' <| mkAppM proj #[mkConst n]
        let pn := ns ++ `domainProjection ++ d ++ proj.getString!.toName
        addThmInfer pn pv
        added := added.push pn
    for proj in [``DualCorrespondenceBundle.projectPositive,
                 ``DualCorrespondenceBundle.projectFault] do
      let pv ← MetaM.run' <| mkAppM proj #[mkConst unifiedName]
      let pn := ns ++ `unifiedProjection ++ proj.getString!.toName
      addThmInfer pn pv
      added := added.push pn
    for thmName in [`threeWayNormalAgreement, `crossAuthorityFaultEquiv,
                    `exactBehaviorEq_both, `projectPositive, `projectFault,
                    `modeSensitivity_present, `bundle_gate_castDerefBoundary,
                    `unified_bundle_witness_kinds,
                    `dual_exact_three_way_classification,
                    `dual_no_specPanic_all_cells,
                    `dual_mode_sensitivity_exact,
                    `dual_d2_mode_sensitivity_all_three,
                    `dual_d1_cast_erasure_and_boundary,
                    `dual_d2_fnentry_protectors_and_transmute_boundary,
                    `dual_d3_dereferenceable_and_zst_boundary] do
      addThmInfer (ns ++ thmName) (mkApp2 (mkConst (bNs ++ thmName)) authC hA)
      added := added.push (ns ++ thmName)
    addThmInfer (ns ++ `dual_fail_closed_out_of_range)
      (mkApp2 (mkConst (bNs ++ `dual_fail_closed_out_of_range)) authC hOob)
    added := added.push (ns ++ `dual_fail_closed_out_of_range)
    let capName := ns ++ `ep2_opaquecast_fnentry_dual_authority_capstone
    addThmInfer capName
      (mkApp3 (mkConst (bNs ++ `ep2_opaquecast_fnentry_dual_authority_capstone))
        authC hA hOob)
    added := added.push capName

    -- 3b. Translation fidelity (anti-mock): `lmOcToVerdict` equals
    -- `ocVerdictOf ∘ lmToMr`, where `lmToMr` / `mrToLm` form a 7-constructor
    -- bijection `LmOcFpObs ≃ MrOcFpObs`, and `ocLmExpected*` equals
    -- `lmOcExpected*.map lmToMr` by `Eq.refl`.
    let mrObsTy0 := mkConst (mrNs ++ `MrOcFpObs)
    let ctorNames : List Name :=
      [`okScalar, `okRetagPair, `okPtrValid, `ub, `phaseBoundary,
       `unsupported, `specPanic]
    let mkCtorMap (srcInd dstInd : Name) (ctors : List Name) : MetaM Expr := do
      let srcTy := mkConst srcInd
      withLocalDeclD `o srcTy fun o => do
        let motive := mkLambda `x .default srcTy (mkConst dstInd)
        let mut minors : Array Expr := #[]
        for c in ctors do
          let cTy ← inferType (mkConst (srcInd ++ c))
          minors := minors.push (← forallTelescope cTy fun xs _ =>
            mkLambdaFVars xs (mkAppN (mkConst (dstInd ++ c)) xs))
        mkLambdaFVars #[o]
          (mkAppN (mkConst (srcInd ++ `rec) [1]) (#[motive] ++ minors ++ #[o]))
    let mkPointwise (ind : Name) (ctors : List Name) (resTy : Expr)
        (lhs rhs : Expr → Expr) : MetaM (Expr × Expr) := do
      withLocalDeclD `o (mkConst ind) fun o => do
        let motive ← mkLambdaFVars #[o] (mkEq resTy (lhs o) (rhs o))
        let mut minors : Array Expr := #[]
        for c in ctors do
          let cTy ← inferType (mkConst (ind ++ c))
          minors := minors.push (← forallTelescope cTy fun xs _ =>
            mkLambdaFVars xs
              (mkRefl resTy (lhs (mkAppN (mkConst (ind ++ c)) xs))))
        let pf ← mkLambdaFVars #[o]
          (mkAppN (mkConst (ind ++ `rec) [0]) (#[motive] ++ minors ++ #[o]))
        let ty ← mkForallFVars #[o] (mkEq resTy (lhs o) (rhs o))
        return (ty, pf)
    let lmToMrName := ns ++ `lmToMr
    let _ ← addDef lmToMrName
      (← MetaM.run' <| mkCtorMap (lmNs ++ `LmOcFpObs) (mrNs ++ `MrOcFpObs) ctorNames)
    let mrToLmName := ns ++ `mrToLm
    let _ ← addDef mrToLmName
      (← MetaM.run' <| mkCtorMap (mrNs ++ `MrOcFpObs) (lmNs ++ `LmOcFpObs) ctorNames)
    added := added.push lmToMrName |>.push mrToLmName
    let lmToMr := mkConst lmToMrName
    let mrToLm := mkConst mrToLmName
    let fidelity : List (Name × Name × Expr × (Expr → Expr) × (Expr → Expr)) :=
      [ (`translation_fidelity, lmNs ++ `LmOcFpObs, optVerdTy,
          fun o => mkApp toV o,
          fun o => mkApp (mkConst (bNs ++ `ocVerdictOf)) (mkApp lmToMr o)),
        (`lmToMr_mrToLm, mrNs ++ `MrOcFpObs, mrObsTy0,
          fun o => mkApp lmToMr (mkApp mrToLm o), fun o => o),
        (`mrToLm_lmToMr, lmNs ++ `LmOcFpObs, lmObsTy,
          fun o => mkApp mrToLm (mkApp lmToMr o), fun o => o) ]
    for (tag, ind, resTy, lhs, rhs) in fidelity do
      let (ty, pf) ← MetaM.run' <| mkPointwise ind ctorNames resTy lhs rhs
      addThm (ns ++ tag) ty pf
      added := added.push (ns ++ tag)
    let listMrTy := mkApp (mkConst ``List [0]) mrObsTy0
    for (rootTbl, lmTbl) in
        [(`ocLmExpectedBasic, `lmOcExpectedBasic),
         (`ocLmExpectedTb, `lmOcExpectedTb)] do
      let lhs := mkConst (bNs ++ rootTbl)
      let rhs := mkApp4 (mkConst ``List.map [0, 0]) lmObsTy mrObsTy0 lmToMr
        (mkConst (lmNs ++ lmTbl))
      let n := ns ++ `frozenTableLock ++ rootTbl
      addThm n (mkEq listMrTy lhs rhs) (mkRefl listMrTy lhs)
      added := added.push n
    -- Also lock the shared Trusted tables across MR and LM via `lmToMr`.
    for (mrTbl, lmTbl) in
        [(`mrOcTrustedExpectedBasic, `lmOcTrustedExpectedBasic),
         (`mrOcTrustedExpectedTb, `lmOcTrustedExpectedTb)] do
      let lhs := mkConst (mrNs ++ mrTbl)
      let rhs := mkApp4 (mkConst ``List.map [0, 0]) lmObsTy mrObsTy0 lmToMr
        (mkConst (lmNs ++ lmTbl))
      let n := ns ++ `trustedTableLock ++ mrTbl
      addThm n (mkEq listMrTy lhs rhs) (mkRefl listMrTy lhs)
      added := added.push n

    -- 3c. Direct-certificate bundles: transport every twin side certificate
    -- onto `lmAuthority` via `cert_transport`, and lock each direct bundle by
    -- `Eq.refl` to its table-derived bundle.
    let directBundle := ns ++ `directUnifiedBundle
    for (tag, sel) in sels do
      let directChk := ns ++ `lmSideCheck_direct ++ tag
      let pFn ← MetaM.run' <|
        withLocalDeclD `a (mkConst (bNs ++ `OcFpLmAuthority)) fun a =>
          mkLambdaFVars #[a] (mkApp2 (mkConst (bNs ++ `lmCheckOf)) sel a)
      addThm directChk (eqTrue (mkApp2 (mkConst (bNs ++ `lmCheckOf)) sel authC))
        (mkAppN (mkConst (bNs ++ `cert_transport))
          #[authC, authUC, mkConst eqName, pFn,
            mkConst (ns ++ `lmSideCheckU ++ tag)])
      added := added.push directChk
      let dName := if tag == `unified then directBundle
                   else ns ++ `directDomainBundle ++ tag
      let origName := if tag == `unified then unifiedName
                      else ns ++ `domainBundle ++ tag
      let dTy ← addDef dName
        (mkApp3 (mkConst (bNs ++ `bundleOfSel)) sel authC (mkConst directChk))
      added := added.push dName
      let eqBName := ns ++ `directBundle_eq ++ tag
      addThm eqBName (mkEq dTy (mkConst dName) (mkConst origName))
        (mkRefl dTy (mkConst dName))
      added := added.push eqBName

    -- 3d. 3-engine companion & UB root-cause alignment (MR + LM).
    let rcName := ns ++ `three_engine_companions_and_diagnostics
    let rcPf ← MetaM.run' do
      let parts : List Expr :=
        [ mkConst (mrNs ++ `mr_oc_exact_ub_diagnostics),
          mkConst (mrNs ++ `mr_oc_setDiscriminant_payload_agreement),
          mkConst (lmNs ++ `lm_oc_setDiscriminant_payload_agreement),
          mkConst (mrNs ++ `mr_oc_protected_drop_mode_sensitive),
          mkConst (lmNs ++ `lm_oc_protected_drop_mode_sensitive),
          mkConst (mrNs ++ `mr_oc_dead_local_ub_non_masking),
          mkConst (lmNs ++ `lm_oc_dead_local_ub_non_masking),
          mkConst (mrNs ++ `mr_oc_invalid_bool_ub_non_masking),
          mkConst (lmNs ++ `lm_oc_invalid_bool_ub_non_masking),
          mkConst (mrNs ++ `mr_oc_type_switch_erasure_boundary),
          mkConst (lmNs ++ `lm_oc_type_switch_erasure_boundary),
          mkConst (mrNs ++ `mr_oc_d2_rev_transmute_mode_sensitive),
          mkConst (lmNs ++ `lm_oc_d2_rev_transmute_mode_sensitive),
          mkConst (mrNs ++ `mr_oc_d3_zst_dangling_and_null),
          mkConst (lmNs ++ `lm_oc_d3_zst_dangling_and_null),
          mkConst (mrNs ++ `mr_checkPtr_some_vs_none_contrast),
          mkConst (mrNs ++ `mr_checkPtrM_tb_some_vs_none_contrast),
          mkConst (lmNs ++ `lm_d3_exact_validityMachine_diagnostics),
          mkConst (lmNs ++ `lm_validityMachine_nonvacuity_witnesses),
          mkConst (lmNs ++ `lm_d3_null_both_halves_ub),
          mkConst (lmNs ++ `lm_d1_phase_boundary_table),
          mkConst (lmNs ++ `lm_step_adapter_boundaries),
          mkConst (lmNs ++ `lm_call_initStackFrame_fnEntry_witness),
          mkConst (mrNs ++ `trusted_d2_indirect_fnptr_calls) ]
      let rec conjRc : List Expr → MetaM Expr
        | [] => return mkConst ``True.intro
        | [p] => return p
        | p :: ps => do mkAppM ``And.intro #[p, ← conjRc ps]
      conjRc parts
    addThmInfer rcName rcPf
    added := added.push rcName

    -- 4. Definitional `Eq.refl` fixture locks over EVERY identically-typed
    -- shared definition in `section Fixtures` (all 93 defs: case count, span,
    -- builders, layouts, types, constants, all 35 `CapturedMir` fixtures,
    -- cast-erasure/place-extraction/retag-erasure helpers, `ocCaseFixture?`,
    -- and `ocTrustedFuel`) PLUS `mrOcCaseCount = lmOcCaseCount` (94 `Eq.refl`
    -- locks), PLUS constructor bijections for the two runner inductives
    -- (`OcTrustedOutcome`, `OcTrustedRun`) and UNIVERSAL lockstep / raw-run
    -- locks for `ocTrustedStep` and `ocRunTrustedRaw`, covering all 97
    -- `section Fixtures` declarations (checked exhaustively below).
    let fixtureNames : List Name :=
      [ `ocFixtureCaseCount, `ocSpan, `ocSt, `ocBb, `ocDecl, `ocLoc,
        `ocU8Layout, `ocU32Layout, `ocUnitLayout, `ocPtrLayout, `ocPairLayout,
        `ocTwoVarLayout, `ocU64Layout, `ocBytePairLayout, `ocBoolLayout,
        `ocLayouts,
        `ocU8Ty, `ocU32Ty, `ocUnitTy, `ocBoolTy, `ocUsizeTy, `ocIsizeTy,
        `ocU64Ty, `ocPairTy, `ocTwoVarTy, `ocBytePairTy,
        `ocRawConstU32Ty, `ocRawConstU8Ty, `ocRawMutU8Ty, `ocMutRefU8Ty,
        `ocShrRefU8Ty, `ocShrRefU32Ty, `ocShrRefUnitTy,
        `ocConstU8, `ocConstU32, `ocConstUsize, `ocConstU64, `ocConstIsize,
        `ocFnOp, `ocFnAbi, `ocBody, `ocCastU32, `ocInit7,
        `ocCase0Mir, `ocCase1Mir, `ocCase2Mir, `ocCase3Mir, `ocCase4Mir,
        `ocCase5Mir, `ocCase6Mir, `ocCase6PayloadMir, `ocCase7Mir,
        `ocCase7ProtectedDropMir, `ocCase8Mir, `ocCase9Mir,
        `ocCase9DeadLocalMir, `ocCase9InvalidBoolMir,
        `ocEraseProj, `ocErasePlace, `ocEraseOperand, `ocEraseRvalue,
        `ocEraseStmt, `ocEraseTerm, `ocEraseBody,
        `ocPlaceHasCast, `ocOperandPlaces, `ocRvaluePlaces, `ocBodyPlaces,
        `ocD2Main,
        `ocCase10Callee, `ocCase10Mir, `ocCase11Callee, `ocCase11Mir,
        `ocCase12Callee, `ocCase12Mir, `ocCase13Callee, `ocCase13Mir,
        `ocCase13RevTransmuteMir, `ocCase14Callee, `ocCase14Mir,
        `ocCase15Callee, `ocCase15Mir, `ocEraseRetags,
        `ocCase16Mir, `ocCase17Mir, `ocCase17DanglingZstMir,
        `ocCase18Mir, `ocCase18ZstNullMir,
        `ocCase19Mir, `ocCase20Mir, `ocCase21Mir,
        `ocCaseFixture?, `ocTrustedFuel ]
    let mut eqLockCount : Nat := 0
    let mut lockNames : Array Name := #[]
    for tag in fixtureNames do
      let lhs := mkConst (mrNs ++ tag)
      let rhs := mkConst (lmNs ++ tag)
      let ty ← MetaM.run' <| inferType lhs
      let lockName := ns ++ `fixtureLock ++ tag
      addThm lockName (mkEq ty lhs rhs) (mkRefl ty lhs)
      added := added.push lockName
      lockNames := lockNames.push lockName
      eqLockCount := eqLockCount + 1
    let countLockName := ns ++ `fixtureLock ++ `caseCount
    addThm countLockName
      (mkEq natTy (mkConst (mrNs ++ `mrOcCaseCount))
        (mkConst (lmNs ++ `lmOcCaseCount)))
      (mkRefl natTy (mkConst (mrNs ++ `mrOcCaseCount)))
    added := added.push countLockName
    lockNames := lockNames.push countLockName
    eqLockCount := eqLockCount + 1
    unless eqLockCount = 94 do
      throwError "cross-root: expected 94 Eq.refl fixture locks, got {eqLockCount}"
    -- Lock the remaining 4 `section Fixtures` declarations
    -- (`OcTrustedOutcome`, `OcTrustedRun`, `ocTrustedStep`, `ocRunTrustedRaw`):
    -- constructor bijections for both inductives + universal lockstep and
    -- raw-run locks of `ocTrustedStep` / `ocRunTrustedRaw` for EVERY body.
    let outCtors : List Name := [`ret, `ub, `unsupported, `outOfFuel]
    let mrOutToLmName := ns ++ `mrOutToLm
    let _ ← addDef mrOutToLmName
      (← MetaM.run' <|
        mkCtorMap (mrNs ++ `OcTrustedOutcome) (lmNs ++ `OcTrustedOutcome) outCtors)
    let lmOutToMrName := ns ++ `lmOutToMr
    let _ ← addDef lmOutToMrName
      (← MetaM.run' <|
        mkCtorMap (lmNs ++ `OcTrustedOutcome) (mrNs ++ `OcTrustedOutcome) outCtors)
    added := added.push mrOutToLmName |>.push lmOutToMrName
    let mrOutToLm := mkConst mrOutToLmName
    let lmOutToMr := mkConst lmOutToMrName
    let (outRtTy1, outRtPf1) ← MetaM.run' <|
      mkPointwise (mrNs ++ `OcTrustedOutcome) outCtors
        (mkConst (mrNs ++ `OcTrustedOutcome))
        (fun o => mkApp lmOutToMr (mkApp mrOutToLm o)) (fun o => o)
    let (outRtTy2, outRtPf2) ← MetaM.run' <|
      mkPointwise (lmNs ++ `OcTrustedOutcome) outCtors
        (mkConst (lmNs ++ `OcTrustedOutcome))
        (fun o => mkApp mrOutToLm (mkApp lmOutToMr o)) (fun o => o)
    addThm (ns ++ `fixtureLock ++ `OcTrustedOutcome_mr_lm) outRtTy1 outRtPf1
    addThm (ns ++ `fixtureLock ++ `OcTrustedOutcome_lm_mr) outRtTy2 outRtPf2
    added := added.push (ns ++ `fixtureLock ++ `OcTrustedOutcome_mr_lm)
      |>.push (ns ++ `fixtureLock ++ `OcTrustedOutcome_lm_mr)
    lockNames := lockNames.push (ns ++ `fixtureLock ++ `OcTrustedOutcome_mr_lm)
      |>.push (ns ++ `fixtureLock ++ `OcTrustedOutcome_lm_mr)
    -- `OcTrustedRun` bijection using `mrOutToLm` / `lmOutToMr` on `.done`.
    let mrRunTy := mkConst (mrNs ++ `OcTrustedRun)
    let lmRunTy := mkConst (lmNs ++ `OcTrustedRun)
    let stTy := mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.MachineState
    let mrOutTy := mkConst (mrNs ++ `OcTrustedOutcome)
    let lmOutTy := mkConst (lmNs ++ `OcTrustedOutcome)
    let mkRunMap (srcNs dstNs : Name) (outMap : Expr) : MetaM Expr :=
      withLocalDeclD `r (mkConst (srcNs ++ `OcTrustedRun)) fun r => do
        let motive := mkLambda `x .default (mkConst (srcNs ++ `OcTrustedRun))
          (mkConst (dstNs ++ `OcTrustedRun))
        let mRun := mkLambda `s .default stTy
          (mkApp (mkConst (dstNs ++ `OcTrustedRun.running)) (.bvar 0))
        let mDone := mkLambda `o .default (mkConst (srcNs ++ `OcTrustedOutcome))
          (mkApp (mkConst (dstNs ++ `OcTrustedRun.done)) (mkApp outMap (.bvar 0)))
        mkLambdaFVars #[r]
          (mkAppN (mkConst (srcNs ++ `OcTrustedRun.rec) [1])
            #[motive, mRun, mDone, r])
    let mrRunToLmName := ns ++ `mrRunToLm
    let _ ← addDef mrRunToLmName
      (← MetaM.run' <| mkRunMap mrNs lmNs mrOutToLm)
    let lmRunToMrName := ns ++ `lmRunToMr
    let _ ← addDef lmRunToMrName
      (← MetaM.run' <| mkRunMap lmNs mrNs lmOutToMr)
    added := added.push mrRunToLmName |>.push lmRunToMrName
    let mrRunToLm := mkConst mrRunToLmName
    let lmRunToMr := mkConst lmRunToMrName
    let mkRunRt (srcNs : Name) (f g : Expr) (outRt : Name) : MetaM (Expr × Expr) :=
      withLocalDeclD `r (mkConst (srcNs ++ `OcTrustedRun)) fun r => do
        let runTy := mkConst (srcNs ++ `OcTrustedRun)
        let motive ← mkLambdaFVars #[r] (mkEq runTy (mkApp g (mkApp f r)) r)
        let mRun ← withLocalDeclD `s stTy fun s =>
          mkLambdaFVars #[s]
            (mkRefl runTy (mkApp (mkConst (srcNs ++ `OcTrustedRun.running)) s))
        let mDone ← withLocalDeclD `o (mkConst (srcNs ++ `OcTrustedOutcome)) fun o => do
          let pf ← mkAppM ``congrArg
            #[mkConst (srcNs ++ `OcTrustedRun.done), mkApp (mkConst outRt) o]
          mkLambdaFVars #[o] pf
        let pf ← mkLambdaFVars #[r]
          (mkAppN (mkConst (srcNs ++ `OcTrustedRun.rec) [0])
            #[motive, mRun, mDone, r])
        let ty ← mkForallFVars #[r] (mkEq runTy (mkApp g (mkApp f r)) r)
        return (ty, pf)
    let (runRtTy1, runRtPf1) ← MetaM.run' <|
      mkRunRt mrNs mrRunToLm lmRunToMr
        (ns ++ `fixtureLock ++ `OcTrustedOutcome_mr_lm)
    let (runRtTy2, runRtPf2) ← MetaM.run' <|
      mkRunRt lmNs lmRunToMr mrRunToLm
        (ns ++ `fixtureLock ++ `OcTrustedOutcome_lm_mr)
    addThm (ns ++ `fixtureLock ++ `OcTrustedRun_mr_lm) runRtTy1 runRtPf1
    addThm (ns ++ `fixtureLock ++ `OcTrustedRun_lm_mr) runRtTy2 runRtPf2
    added := added.push (ns ++ `fixtureLock ++ `OcTrustedRun_mr_lm)
      |>.push (ns ++ `fixtureLock ++ `OcTrustedRun_lm_mr)
    lockNames := lockNames.push (ns ++ `fixtureLock ++ `OcTrustedRun_mr_lm)
      |>.push (ns ++ `fixtureLock ++ `OcTrustedRun_lm_mr)
    -- UNIVERSAL locks of `ocTrustedStep` and `ocRunTrustedRaw` (EVERY body,
    -- run state, and callee list): instantiate `ocRunner_copy_lock` with the
    -- LeanMiri-side copy of the runner, discharging all 11 copy hypotheses by
    -- `Eq.refl` (kernel unfolding of the verbatim-shared definitions), and
    -- check both conjuncts against explicitly constructed `∀` statements.
    let lmOutC (c : Name) : Expr := mkConst (lmNs ++ `OcTrustedOutcome ++ c)
    let lmRunC (c : Name) : Expr := mkConst (lmNs ++ `OcTrustedRun ++ c)
    let finishLm : Expr :=
      mkLambda `r .default lmRunTy <|
        mkAppN (mkConst (lmNs ++ `OcTrustedRun.rec) [1])
          #[mkLambda `x .default lmRunTy lmOutTy,
            mkLambda `s .default stTy (lmOutC `outOfFuel),
            mkLambda `o .default lmOutTy (.bvar 0), .bvar 0]
    let dischargeRefl (head : Expr) (n : Nat) : MetaM Expr := do
      let mut e := head
      for _ in List.range n do
        let ty ← whnf (← inferType e)
        let .forallE _ dom _ _ := ty
          | throwError "cross-root: expected a hypothesis binder in {ty}"
        let pf ← forallTelescope dom fun xs body => do
          let some (α, lhs, _) := body.eq?
            | throwError "cross-root: expected an equality hypothesis: {body}"
          mkLambdaFVars xs (mkRefl α lhs)
        e := mkApp e pf
      return e
    let runnerHead (ubC : Expr) : Expr :=
      mkAppN (mkConst (bNs ++ `ocRunner_copy_lock))
        #[lmRunTy, lmOutTy, lmRunC `running, lmRunC `done, lmOutC `ret, ubC,
          lmOutC `unsupported, lmOutC `outOfFuel, mrRunToLm, mrOutToLm,
          mkConst (lmNs ++ `ocTrustedStep), finishLm,
          mkConst (lmNs ++ `ocRunTrustedRaw)]
    let runnerPf ← MetaM.run' <| dischargeRefl (runnerHead (lmOutC `ub)) 11
    let runnerUnivName := ns ++ `fixtureLock ++ `runner_universal
    addThmInfer runnerUnivName runnerPf
    added := added.push runnerUnivName
    let capMirTy0 := mkConst `Trusted.Rustc.V2026_06_01.MirAst.CapturedMir
    let (stepLockTy, runLockTy) ← MetaM.run' do
      let stepTy ← withLocalDeclD `body capMirTy0 fun body =>
        withLocalDeclD `r mrRunTy fun r =>
          mkForallFVars #[body, r] <| mkEq lmRunTy
            (mkApp mrRunToLm (mkApp2 (mkConst (mrNs ++ `ocTrustedStep)) body r))
            (mkApp2 (mkConst (lmNs ++ `ocTrustedStep)) body (mkApp mrRunToLm r))
      let runTy ← withLocalDeclD `body capMirTy0 fun body =>
        withLocalDeclD `callees (mkApp (mkConst ``List [0]) capMirTy0) fun cs =>
          mkForallFVars #[body, cs] <| mkEq lmOutTy
            (mkApp mrOutToLm
              (mkApp2 (mkConst (mrNs ++ `ocRunTrustedRaw)) body cs))
            (mkApp2 (mkConst (lmNs ++ `ocRunTrustedRaw)) body cs)
      return (stepTy, runTy)
    let stepLockName := ns ++ `fixtureLock ++ `ocTrustedStep
    addThm stepLockName stepLockTy
      (← MetaM.run' <| mkAppM ``And.left #[mkConst runnerUnivName])
    added := added.push stepLockName
    lockNames := lockNames.push stepLockName
    let runLockName := ns ++ `fixtureLock ++ `ocRunTrustedRaw
    addThm runLockName runLockTy
      (← MetaM.run' <| mkAppM ``And.right #[mkConst runnerUnivName])
    added := added.push runLockName
    lockNames := lockNames.push runLockName
    let _ := mrOutTy
    let nilMir := mkApp (mkConst ``List.nil [0]) capMirTy0
    -- `ocCombine` is the only other top-level name shared by both namespaces
    -- (declared outside `section Fixtures`, over the per-namespace observation
    -- type): lock it universally through `lmToMr` via `ocCombine_copy_lock`.
    let combineLockName := ns ++ `fixtureLock ++ `ocCombine
    addThmInfer combineLockName <|
      mkAppN (mkConst (bNs ++ `ocCombine_copy_lock))
        #[lmObsTy, mkConst (lmNs ++ `instDecidableEqLmOcFpObs), lmToMr, mrToLm,
          mkConst (ns ++ `mrToLm_lmToMr), lmObsC `unsupported,
          mkRefl mrObsTy0 (mkApp lmToMr (lmObsC `unsupported)),
          mkConst (lmNs ++ `ocCombine),
          mkLambda `a .default lmObsTy <| mkLambda `b .default lmObsTy <|
            mkRefl lmObsTy
              (mkApp2 (mkConst (lmNs ++ `ocCombine)) (.bvar 1) (.bvar 0))]
    added := added.push combineLockName
    lockNames := lockNames.push combineLockName
    let runnerLockCount : Nat := 4 -- 2 inductive bijections + 2 universal locks
    let totalFixtureLockCount : Nat := eqLockCount + runnerLockCount
    unless totalFixtureLockCount = 98 do
      throwError "cross-root: expected 98 total fixture locks (97 section Fixtures + caseCount), got {totalFixtureLockCount}"
    -- EXHAUSTIVE shared-name audit: EVERY top-level declaration name that the
    -- MiniRust and LeanMiri modules both declare (the 97 `section Fixtures`
    -- declarations plus `ocCombine`) must be covered by one of the locks
    -- above, so a shared fixture can never be added without a lock.
    let lockedShared : NameSet :=
      (fixtureNames ++ [`OcTrustedOutcome, `OcTrustedRun, `ocTrustedStep,
        `ocRunTrustedRaw, `ocCombine]).foldl (fun s n => s.insert n) {}
    let envNow ← getEnv
    let some mrModIdx := envNow.getModuleIdx? mrNs
      | throwError "cross-root: module {mrNs} not loaded"
    let mut sharedTopLevel : Nat := 0
    for c in envNow.header.moduleData[mrModIdx.toNat]!.constNames do
      if mrNs.isPrefixOf c then
        let suffix := c.replacePrefix mrNs .anonymous
        if suffix.getNumParts == 1 && envNow.contains (lmNs ++ suffix) then
          unless lockedShared.contains suffix do
            throwError "cross-root: shared MR/LM declaration {suffix} has no lock"
          sharedTopLevel := sharedTopLevel + 1
    unless sharedTopLevel = 98 && lockedShared.size = 98 do
      throwError "cross-root: expected 98 shared top-level MR/LM names (97 section Fixtures + ocCombine), got {sharedTopLevel} (locked {lockedShared.size})"

    -- 4a. Companion fixtures and `D1` static phase boundary DIRECTLY over the
    -- REAL vendored-Miri companion harnesses (zero Episode 1 theorem index
    -- scraping!): build `lmCompanionObserve` over the real harnesses and
    -- `lmCompanionObserveU` over their 5 loop-unrolled twins, prove
    -- `lmCompanionObserve = lmCompanionObserveU` from the 5 `.eq_src` theorems,
    -- kernel-evaluate the 14-cell boolean certificate `lmCompanionCheckOf` on
    -- the twin by `Eq.refl`, transport to the real observer, and audit
    -- PER-CELL that every companion branch reaches its specific vendored Miri
    -- entry point and NEVER reaches Trusted `stepMirFn`.
    let compNs := bNs ++ `OcFpCompanion
    let compTy := mkConst compNs
    let lmStepObs := mkConst (lmNs ++ `lmOcStepObs)
    let lmRun := mkConst (lmNs ++ `lmOcRun)
    let lmInitC := mkConst `LeanMiriSpec.HeapAllocAndWidePtrLM.lmInit
    let (pZst4, pZst0, align0) ← MetaM.run' do
      let pvTy ← inferType (mkConst (lmNs ++ `lmOcPtrValidity))
      -- `LmState → Pointer (Option Provenance) → Nat → Align → LmOcM LmOcFpObs`
      let ptrTy := pvTy.bindingBody!.bindingDomain!
      let provOptTy := ptrTy.appArg!
      let provTy := provOptTy.appArg!
      let noneProv := mkApp (mkConst ``Option.none [0]) provTy
      let mkPtr (n : UInt64) : Expr :=
        mkApp3 (mkConst `Miri.Memory.Pointer.mk [0]) provOptTy
          (mkApp (mkConst `Miri.ABI.Size.ofBytes) (toExpr n)) noneProv
      return (mkPtr 4, mkPtr 0, mkApp (mkConst `Miri.ABI.Align.mk) (mkNatLit 0))
    let mkCompBranch (fStep fProt fInv fRev fPtr tbE : Expr) (c : Name) : Expr :=
      match c with
      | `payload =>
        mkApp2 lmStepObs (toExpr (4 : UInt64))
          (mkApp2 fStep
            (mkApp (mkConst (lmNs ++ `ocEraseBody))
              (mkConst (lmNs ++ `ocCase6PayloadMir)))
            (mkConst (lmNs ++ `ocU32Ty)))
      | `protectedDrop => mkApp lmRun (mkApp fProt tbE)
      | `deadLocal =>
        mkApp2 lmStepObs (toExpr (4 : UInt64))
          (mkApp2 fStep
            (mkApp (mkConst (lmNs ++ `ocEraseBody))
              (mkConst (lmNs ++ `ocCase9DeadLocalMir)))
            (mkConst (lmNs ++ `ocU32Ty)))
      | `invalidBool => mkApp lmRun (mkApp fInv tbE)
      | `revTransmute => mkApp lmRun (mkApp fRev tbE)
      | `zstDangling =>
        mkApp lmRun (mkApp4 fPtr (mkApp lmInitC tbE) pZst4 (mkNatLit 0) align0)
      | _ =>
        mkApp lmRun (mkApp4 fPtr (mkApp lmInitC tbE) pZst0 (mkNatLit 0) align0)
    let compCtors : List Name :=
      [`payload, `protectedDrop, `deadLocal, `invalidBool, `revTransmute,
       `zstDangling, `zstNull]
    let mkCompObs (fStep fProt fInv fRev fPtr : Expr) : Expr :=
      let minors := compCtors.toArray.map (mkCompBranch fStep fProt fInv fRev fPtr (.bvar 1))
      mkLambda `tb .default boolTy <| mkLambda `c .default compTy <|
        mkAppN (mkConst (compNs ++ `rec) [1])
          (#[mkLambda `x .default compTy lmObsTy] ++ minors ++ #[.bvar 0])
    let runStepC := mkConst (lmNs ++ `ocRunStep)
    let runStepU := mkConst (lmNs ++ `ocRunStepU)
    let protDropC := mkConst (lmNs ++ `lmOcProtectedDrop)
    let protDropU := mkConst (lmNs ++ `lmOcProtectedDropU)
    let invBoolC := mkConst (lmNs ++ `lmOcInvalidBoolRead)
    let invBoolU := mkConst (lmNs ++ `lmOcInvalidBoolReadU)
    let revTrC := mkConst (lmNs ++ `lmOcD2RevTransmute)
    let revTrU := mkConst (lmNs ++ `lmOcD2RevTransmuteU)
    let ptrValC := mkConst (lmNs ++ `lmOcPtrValidity)
    let ptrValU := mkConst (lmNs ++ `lmOcPtrValidityU)
    let compObsName := ns ++ `lmCompanionObserve
    let _ ← addDef compObsName
      (mkCompObs runStepC protDropC invBoolC revTrC ptrValC)
    let compObs := mkConst compObsName
    let compObsUName := ns ++ `lmCompanionObserveU
    let _ ← addDef compObsUName
      (mkCompObs runStepU protDropU invBoolU revTrU ptrValU)
    let compObsU := mkConst compObsUName
    added := added.push compObsName |>.push compObsUName
    let compEqName := ns ++ `lmCompanionObserve_eq_unrolled
    let compEqPf ← MetaM.run' do
      let t1 ← inferType runStepC
      let t2 ← inferType protDropC
      let t3 ← inferType invBoolC
      let t4 ← inferType revTrC
      let t5 ← inferType ptrValC
      let f ← withLocalDeclD `f1 t1 fun f1 =>
        withLocalDeclD `f2 t2 fun f2 =>
          withLocalDeclD `f3 t3 fun f3 =>
            withLocalDeclD `f4 t4 fun f4 =>
              withLocalDeclD `f5 t5 fun f5 =>
                mkLambdaFVars #[f1, f2, f3, f4, f5]
                  (mkCompObs f1 f2 f3 f4 f5)
      let p1 ← mkCongrArg f (mkConst (lmNs ++ `ocRunStepU.eq_src))
      let p2 ← mkCongr p1 (mkConst (lmNs ++ `lmOcProtectedDropU.eq_src))
      let p3 ← mkCongr p2 (mkConst (lmNs ++ `lmOcInvalidBoolReadU.eq_src))
      let p4 ← mkCongr p3 (mkConst (lmNs ++ `lmOcD2RevTransmuteU.eq_src))
      mkCongr p4 (mkConst (lmNs ++ `lmOcPtrValidityU.eq_src))
    addThmInfer compEqName compEqPf
    added := added.push compEqName
    let compCheck (obs : Expr) : Expr :=
      mkApp3 (mkConst (bNs ++ `lmCompanionCheckOf)) lmObsTy lmToMr obs
    let compCheckUName := ns ++ `lmCompanionU_check
    addThm compCheckUName (eqTrue (compCheck compObsU)) reflTrue
    added := added.push compCheckUName
    let compCheckName := ns ++ `lmCompanion_check
    addThm compCheckName (eqTrue (compCheck compObs))
      (mkAppN (mkConst (bNs ++ `lmCompanionCheckOf_of_eq))
        #[lmObsTy, lmToMr, compObs, compObsU, mkConst compEqName,
          mkConst compCheckUName])
    added := added.push compCheckName
    let compCellsName := ns ++ `lmCompanion_cells
    addThmInfer compCellsName
      (mkApp4 (mkConst (bNs ++ `lmCompanionCheckOf_sound))
        lmObsTy lmToMr compObs (mkConst compCheckName))
    added := added.push compCellsName
    let hC := mkConst compCellsName
    for thmName in [`dual_companion_three_way,
                    `dual_companion_mode_sensitivity] do
      addThmInfer (ns ++ thmName)
        (mkApp4 (mkConst (bNs ++ thmName)) lmObsTy lmToMr compObs hC)
      added := added.push (ns ++ thmName)
    -- Direct twin-evaluated erased invalid-`bool` observation (zero scraping).
    let mkErased (fStep : Expr) : Expr :=
      mkApp2 lmStepObs (toExpr (1 : UInt64))
        (mkApp2 fStep
          (mkApp (mkConst (lmNs ++ `ocEraseBody))
            (mkConst (lmNs ++ `ocCase9InvalidBoolMir)))
          (mkConst (lmNs ++ `ocBoolTy)))
    let erasedName := ns ++ `lmErasedInvalidBool
    let _ ← addDef erasedName (mkErased runStepC)
    let erasedUName := ns ++ `lmErasedInvalidBoolU
    let _ ← addDef erasedUName (mkErased runStepU)
    added := added.push erasedName |>.push erasedUName
    let erasedLhs := mkConst erasedName
    let erasedULhs := mkConst erasedUName
    let erasedEqName := ns ++ `lmErasedInvalidBool_eq_unrolled
    let erasedEqPf ← MetaM.run' do
      let g ← withLocalDeclD `f (← inferType runStepC) fun f =>
        mkLambdaFVars #[f] (mkErased f)
      mkCongrArg g (mkConst (lmNs ++ `ocRunStepU.eq_src))
    addThmInfer erasedEqName erasedEqPf
    added := added.push erasedEqName
    let mrSc2 := mkApp (mkConst (mrNs ++ `MrOcFpObs.okScalar)) (mkNatLit 2)
    let erasedUOkName := ns ++ `lmErasedInvalidBoolU_eq
    addThm erasedUOkName (mkEq mrObsTy0 (mkApp lmToMr erasedULhs) mrSc2)
      (mkRefl mrObsTy0 mrSc2)
    added := added.push erasedUOkName
    let erasedOkName := ns ++ `lmErasedInvalidBool_eq
    let erasedOkPf ← MetaM.run' do
      let p1 ← mkCongrArg lmToMr (mkConst erasedEqName)
      mkEqTrans p1 (mkConst erasedUOkName)
    addThm erasedOkName (mkEq mrObsTy0 (mkApp lmToMr erasedLhs) mrSc2) erasedOkPf
    added := added.push erasedOkName
    let hErased := mkConst erasedOkName
    addThmInfer (ns ++ `dual_type_switch_erasure_boundary)
      (mkApp6 (mkConst (bNs ++ `dual_type_switch_erasure_boundary)) lmObsTy
        lmToMr compObs hC erasedLhs hErased)
    added := added.push (ns ++ `dual_type_switch_erasure_boundary)
    -- LeanMiri static phase observer (`Miri.Interpreter.project` AND
    -- `PlaceDynamic.project` on every cast place) for BOTH canonical cases
    -- (`0..21`) AND all 7 companion fixtures (`lmPhaseCompanion`): direct
    -- kernel evaluation by `Eq.refl`.
    let lmPhaseObs := mkConst (lmNs ++ `lmOcPhaseObserve)
    let phaseCheck (phase : Expr) : Expr :=
      mkApp3 (mkConst (bNs ++ `lmPhaseCheckOf)) lmObsTy lmToMr phase
    let phaseCheckName := ns ++ `lmPhase_check
    addThm phaseCheckName (eqTrue (phaseCheck lmPhaseObs)) reflTrue
    added := added.push phaseCheckName
    let lmPhaseBody := mkConst (lmNs ++ `lmOcPhaseObserveBody)
    let compBodies : List Name :=
      [`ocCase6PayloadMir, `ocCase7ProtectedDropMir, `ocCase9DeadLocalMir,
       `ocCase9InvalidBoolMir, `ocCase13RevTransmuteMir,
       `ocCase17DanglingZstMir, `ocCase18ZstNullMir]
    let phaseCompName := ns ++ `lmPhaseCompanion
    let _ ← addDef phaseCompName <|
      mkLambda `c .default compTy <|
        mkAppN (mkConst (compNs ++ `rec) [1])
          (#[mkLambda `x .default compTy lmObsTy] ++
            (compBodies.toArray.map fun b =>
              mkApp lmPhaseBody (mkConst (lmNs ++ b))) ++ #[.bvar 0])
    added := added.push phaseCompName
    let phaseCompObs := mkConst phaseCompName
    let phaseCompCheck (pc : Expr) : Expr :=
      mkApp3 (mkConst (bNs ++ `lmPhaseCompanionCheckOf)) lmObsTy lmToMr pc
    let phaseCompCheckName := ns ++ `lmPhaseCompanion_check
    addThm phaseCompCheckName (eqTrue (phaseCompCheck phaseCompObs)) reflTrue
    added := added.push phaseCompCheckName
    let fidelityC := mkConst (ns ++ `translation_fidelity)
    addThmInfer (ns ++ `dual_d1_phase_boundary)
      (mkApp6 (mkConst (bNs ++ `dual_d1_phase_boundary)) authC hA lmToMr
        fidelityC lmPhaseObs (mkConst phaseCheckName))
    added := added.push (ns ++ `dual_d1_phase_boundary)
    addThmInfer (ns ++ `dual_d1_companion_phase_boundary)
      (mkAppN (mkConst (bNs ++ `dual_d1_companion_phase_boundary))
        #[authC, lmToMr, fidelityC, compObs, hC, phaseCompObs,
          mkConst phaseCompCheckName])
    added := added.push (ns ++ `dual_d1_companion_phase_boundary)
    -- Unconditional `Mach` driver identity inside `CrossRoot` (discharging
    -- `steps_eq_runToStopM_bm_of` with `MiniRustSpec.Correspondence.stepM_bm_eq`).
    let bmDriverName := ns ++ `bm_driver_is_minirust_steps
    addThmInfer bmDriverName
      (mkApp (mkConst (bNs ++ `steps_eq_runToStopM_bm_of))
        (mkConst `MiniRustSpec.Correspondence.stepM_bm_eq))
    added := added.push bmDriverName

    -- All-`Nat` phase agreement: LeanMiri's `lmOcPhaseObserve` factors through
    -- its copy of the shared fixture table (locked to `ocCaseFixture?` by
    -- `Eq.refl` above), so it is fail-closed for EVERY `idx ≥ 22`; the
    -- factorization hypothesis is discharged by `Eq.refl`.
    let fixOptTy ← MetaM.run' do
      let t ← inferType (mkConst (lmNs ++ `ocCaseFixture?))
      return t.bindingBody!
    let fixPairTy := fixOptTy.appArg!
    let listCapTy := mkApp (mkConst ``List [0]) capMirTy0
    let kPhase : Expr :=
      mkLambda `o .default fixOptTy <|
        mkAppN (mkConst ``Option.rec [1, 0])
          #[fixPairTy, mkLambda `x .default fixOptTy lmObsTy,
            lmObsC `unsupported,
            mkLambda `p .default fixPairTy <|
              mkAppN (mkConst ``Prod.rec [1, 0, 0])
                #[capMirTy0, listCapTy, mkLambda `x .default fixPairTy lmObsTy,
                  mkLambda `body .default capMirTy0 <|
                    mkLambda `cs .default listCapTy (mkApp lmPhaseBody (.bvar 1)),
                  .bvar 0],
            .bvar 0]
    let mrUnsupported := mkConst (mrNs ++ `MrOcFpObs.unsupported)
    let phaseOobName := ns ++ `lmPhase_failClosed
    addThmInfer phaseOobName <|
      mkAppN (mkConst (bNs ++ `phase_fail_closed_of_fixture))
        #[lmObsTy, lmToMr, mkConst (lmNs ++ `ocCaseFixture?),
          mkConst (ns ++ `fixtureLock ++ `ocCaseFixture?), kPhase,
          mkRefl mrObsTy0 mrUnsupported, lmPhaseObs,
          mkLambda `idx .default natTy
            (mkRefl lmObsTy (mkApp lmPhaseObs (.bvar 0)))]
    added := added.push phaseOobName
    addThmInfer (ns ++ `dual_d1_phase_boundary_all_nat)
      (mkApp5 (mkConst (bNs ++ `dual_d1_phase_boundary_all_nat)) lmObsTy lmToMr
        lmPhaseObs (mkConst phaseCheckName) (mkConst phaseOobName))
    added := added.push (ns ++ `dual_d1_phase_boundary_all_nat)
    let compCapName := ns ++ `ep2_opaquecast_fnentry_companion_phase_capstone
    addThmInfer compCapName <|
      mkAppN (mkConst (bNs ++ `ep2_opaquecast_fnentry_companion_phase_capstone))
        #[authC, hA, lmToMr, fidelityC, compObs, hC, erasedLhs, hErased,
          lmPhaseObs, mkConst phaseCheckName, mkConst phaseOobName,
          phaseCompObs, mkConst phaseCompCheckName]
    added := added.push compCapName

    -- 4a'. Post-borrowck image. On the cast-erased MIR, Trusted `stepMirFn`
    -- agrees with MiniRust and LeanMiri on ALL 44 cells, so ALL FOUR
    -- post-borrowck bundles (`unified`, `d1`, `d2`, `d3`) gate EVERY case
    -- (case `8` closed). Each LM side certificate is kernel-evaluated on the
    -- twin, transported onto `lmAuthority`, and its direct bundle is locked by
    -- `Eq.refl` to the table-derived bundle.
    let pbCheck (sel a : Expr) : Expr :=
      mkApp2 (mkConst (bNs ++ `lmPostBorrowckCheckOf)) sel a
    let pbUnifiedName := ns ++ `postBorrowckBundle ++ `unified
    let pbD1Name := ns ++ `postBorrowckBundle ++ `d1
    let pbD2Name := ns ++ `postBorrowckBundle ++ `d2
    let pbD3Name := ns ++ `postBorrowckBundle ++ `d3
    for (tag, sel) in sels do
      let chkU := ns ++ `lmPostBorrowckSideCheckU ++ tag
      addThm chkU (eqTrue (pbCheck sel authUC)) reflTrue
      added := added.push chkU
      let chkDirect := ns ++ `lmPostBorrowckSideCheck_direct ++ tag
      let pFn ← MetaM.run' <|
        withLocalDeclD `a (mkConst (bNs ++ `OcFpLmAuthority)) fun a =>
          mkLambdaFVars #[a] (pbCheck sel a)
      addThm chkDirect (eqTrue (pbCheck sel authC))
        (mkAppN (mkConst (bNs ++ `cert_transport))
          #[authC, authUC, mkConst eqName, pFn, mkConst chkU])
      added := added.push chkDirect
      let bName := ns ++ `postBorrowckBundle ++ tag
      let bVal :=
        if tag == `unified then
          mkApp2 (mkConst (bNs ++ `postBorrowckBundleOf)) authC hA
        else
          mkApp3 (mkConst (bNs ++ `postBorrowckDomainBundleOf))
            (mkConst (domNs ++ tag)) authC hA
      let bTy ← addDef bName bVal
      added := added.push bName
      bundleCount := bundleCount + 1
      let dName := ns ++ `postBorrowckBundle_direct ++ tag
      let _ ← addDef dName
        (mkApp3 (mkConst (bNs ++ `postBorrowckBundleOfSel)) sel authC
          (mkConst chkDirect))
      added := added.push dName
      let eqBName := ns ++ `postBorrowckBundle_eq ++ tag
      addThm eqBName (mkEq bTy (mkConst dName) (mkConst bName))
        (mkRefl bTy (mkConst dName))
      added := added.push eqBName
    for thmName in [`post_borrowck_bundle_closes_case8,
                    `postBorrowck_modeSensitivity_present,
                    `dual_post_borrowck_case8] do
      addThmInfer (ns ++ thmName) (mkApp2 (mkConst (bNs ++ thmName)) authC hA)
      added := added.push (ns ++ thmName)
    addThmInfer (ns ++ `postBorrowckDomain_bundle_claims)
      (mkLambda `d .default (mkConst domNs)
        (mkApp3 (mkConst (bNs ++ `postBorrowckDomain_bundle_claims))
          (.bvar 0) authC hA))
    added := added.push (ns ++ `postBorrowckDomain_bundle_claims)
    addThmInfer (ns ++ `dual_post_borrowck_exact_all_nat)
      (mkApp5 (mkConst (bNs ++ `dual_post_borrowck_exact_all_nat)) authC hA hOob
        lmToMr fidelityC)
    added := added.push (ns ++ `dual_post_borrowck_exact_all_nat)
    let pbCapName := ns ++ `ep2_opaquecast_fnentry_post_borrowck_capstone
    addThmInfer pbCapName
      (mkApp5 (mkConst (bNs ++ `ep2_opaquecast_fnentry_post_borrowck_capstone))
        authC hA hOob lmToMr fidelityC)
    added := added.push pbCapName
    -- Case `17` fixture divergence: LeanMiri's canonical cell `17` IS its
    -- dangling-ZST companion harness (definitional lock for every `tb`),
    -- while Trusted's canonical fixture is a live `&()`.
    let zstLockName := ns ++ `lmCompanion_zstDangling_is_canonical17
    let zstDanglingC := mkConst (compNs ++ `zstDangling)
    addThm zstLockName
      (mkForall `tb .default boolTy <|
        mkEq lmObsTy (mkApp2 compObs (.bvar 0) zstDanglingC)
          (mkApp2 lmObserve (.bvar 0) (mkNatLit 17)))
      (mkLambda `tb .default boolTy <|
        mkRefl lmObsTy (mkApp2 compObs (.bvar 0) zstDanglingC))
    added := added.push zstLockName
    addThmInfer (ns ++ `dual_d3_zst_fixture_divergence)
      (mkApp4 (mkConst (bNs ++ `dual_d3_zst_fixture_divergence)) lmObsTy lmToMr
        compObs hC)
    added := added.push (ns ++ `dual_d3_zst_fixture_divergence)
    -- Lowering-dependent cell `7`: LeanMiri's case `7` IS its case `5`
    -- (`Deinit`) harness, for every mode (definitional lock).
    let case7LockName := ns ++ `lmCase7_is_case5_harness
    addThm case7LockName
      (mkForall `tb .default boolTy <|
        mkEq lmObsTy (mkApp2 lmObserve (.bvar 0) (mkNatLit 7))
          (mkApp2 lmObserve (.bvar 0) (mkNatLit 5)))
      (mkLambda `tb .default boolTy <|
        mkRefl lmObsTy (mkApp2 lmObserve (.bvar 0) (mkNatLit 7)))
    added := added.push case7LockName
    addThmInfer (ns ++ `dual_d1_lowering_dependent_cells)
      (mkApp2 (mkConst (bNs ++ `dual_d1_lowering_dependent_cells)) authC hA)
    added := added.push (ns ++ `dual_d1_lowering_dependent_cells)
    addThmInfer (ns ++ `ocLoweringDependent_characterization)
      (mkApp2 (mkConst (bNs ++ `ocLoweringDependent_characterization)) authC hA)
    added := added.push (ns ++ `ocLoweringDependent_characterization)
    -- Fuel audit over the REAL LeanMiri authority: no in-range LeanMiri cell
    -- is `.unsupported` (so `Step.step`'s "out of fuel" never fires), Trusted's
    -- case `8` is a genuine `.unsupported` step node, AND all 12 raw
    -- `ocRunStep` runs stop directly in `.ok (some _)` or
    -- `.error (.undefinedBehavior _)` (never `.error (.unsupported _)`).
    addThmInfer (ns ++ `dual_fuel_and_unsupported_audit)
      (mkApp2 (mkConst (bNs ++ `dual_fuel_and_unsupported_audit)) authC hA)
    added := added.push (ns ++ `dual_fuel_and_unsupported_audit)
    let (stepErrTy, stepValTy, lmStepStoppedFn) ← MetaM.run' do
      let runTy ← inferType runStepC
      let resTy := runTy.bindingBody!.bindingBody!
      let errTy := resTy.appFn!.appArg!
      let valTy := resTy.appArg!
      let some (.inductInfo indInfo) :=
          (← getEnv).find? `Miri.Interpreter.StepError
        | throwError "cross-root: Miri.Interpreter.StepError missing"
      let mut minors : Array Expr := #[]
      for ctor in indInfo.ctors do
        let cTy ← inferType (mkConst ctor)
        let minor ← forallTelescopeReducing cTy fun xs _ => do
          let ret := if ctor == `Miri.Interpreter.StepError.undefinedBehavior
            then mkConst ``Bool.true else mkConst ``Bool.false
          mkLambdaFVars xs ret
        minors := minors.push minor
      let errCheck :=
        mkLambda `e .default errTy <|
          mkAppN (mkConst `Miri.Interpreter.StepError.rec [1])
            (#[mkLambda `x .default errTy boolTy] ++ minors ++ #[.bvar 0])
      let okCheck :=
        mkLambda `v .default valTy <|
          mkApp2 (mkConst ``Option.isSome [0]) valTy.appArg! (.bvar 0)
      let fn :=
        mkLambda `r .default resTy <|
          mkAppN (mkConst ``Except.rec [1, 0, 0])
            #[errTy, valTy, mkLambda `x .default resTy boolTy,
              errCheck, okCheck, .bvar 0]
      return (errTy, valTy, fn)
    let lmStepStoppedName := ns ++ `lmStepStopped
    let _ ← addDef lmStepStoppedName lmStepStoppedFn
    added := added.push lmStepStoppedName
    let lmStepStoppedC := mkConst lmStepStoppedName
    let lmErrOutOfFuel :=
      mkApp3 (mkConst ``Except.error [0, 0]) stepErrTy stepValTy
        (mkApp (mkConst `Miri.Interpreter.StepError.unsupported)
          (toExpr "out of fuel"))
    let rawStepPairs : List (Expr × Expr) :=
      [ (mkApp (mkConst (lmNs ++ `ocEraseBody)) (mkConst (lmNs ++ `ocCase0Mir)),
          mkConst (lmNs ++ `ocU32Ty)),
        (mkApp (mkConst (lmNs ++ `ocEraseBody)) (mkConst (lmNs ++ `ocCase1Mir)),
          mkConst (lmNs ++ `ocU32Ty)),
        (mkApp (mkConst (lmNs ++ `ocEraseBody)) (mkConst (lmNs ++ `ocCase2Mir)),
          mkConst (lmNs ++ `ocU32Ty)),
        (mkApp (mkConst (lmNs ++ `ocEraseBody)) (mkConst (lmNs ++ `ocCase3Mir)),
          mkConst (lmNs ++ `ocU32Ty)),
        (mkApp (mkConst (lmNs ++ `ocEraseBody)) (mkConst (lmNs ++ `ocCase4Mir)),
          mkConst (lmNs ++ `ocU32Ty)),
        (mkApp (mkConst (lmNs ++ `ocEraseBody)) (mkConst (lmNs ++ `ocCase6Mir)),
          mkConst (lmNs ++ `ocU32Ty)),
        (mkApp (mkConst (lmNs ++ `ocEraseBody)) (mkConst (lmNs ++ `ocCase8Mir)),
          mkConst (lmNs ++ `ocU32Ty)),
        (mkApp (mkConst (lmNs ++ `ocEraseBody)) (mkConst (lmNs ++ `ocCase9Mir)),
          mkConst (lmNs ++ `ocU32Ty)),
        (mkApp (mkConst (lmNs ++ `ocEraseBody))
          (mkConst (lmNs ++ `ocCase6PayloadMir)), mkConst (lmNs ++ `ocU32Ty)),
        (mkApp (mkConst (lmNs ++ `ocEraseBody))
          (mkConst (lmNs ++ `ocCase9DeadLocalMir)), mkConst (lmNs ++ `ocU32Ty)),
        (mkApp (mkConst (lmNs ++ `ocEraseBody))
          (mkConst (lmNs ++ `ocCase9InvalidBoolMir)), mkConst (lmNs ++ `ocBoolTy)),
        (mkApp (mkConst (lmNs ++ `ocEraseBody))
          (mkApp (mkConst (bNs ++ `ocMoveToCopyBody))
            (mkConst (lmNs ++ `ocCase2Mir))),
          mkConst (lmNs ++ `ocU32Ty)) ]
    let mkRawStepsCheck (fStep : Expr) : Expr :=
      rawStepPairs.foldr
        (fun (bodyE, tyE) acc =>
          mkApp2 (mkConst ``Bool.and)
            (mkApp lmStepStoppedC (mkApp2 fStep bodyE tyE)) acc)
        (mkConst ``Bool.true)
    let rawStepsChkName := ns ++ `lmRawStepsCheck
    let _ ← addDef rawStepsChkName (mkRawStepsCheck runStepC)
    let rawStepsChkUName := ns ++ `lmRawStepsCheckU
    let _ ← addDef rawStepsChkUName (mkRawStepsCheck runStepU)
    added := added.push rawStepsChkName |>.push rawStepsChkUName
    let rawStepsEqName := ns ++ `lmRawStepsCheck_eq_unrolled
    let rawStepsEqPf ← MetaM.run' do
      let runStepTy ← inferType runStepC
      let g ← withLocalDeclD `f runStepTy fun f =>
        mkLambdaFVars #[f] (mkRawStepsCheck f)
      mkCongrArg g (mkConst (lmNs ++ `ocRunStepU.eq_src))
    addThmInfer rawStepsEqName rawStepsEqPf
    added := added.push rawStepsEqName
    let rawStepsUOkName := ns ++ `lmRawSteps_within_fuelU
    addThm rawStepsUOkName (eqTrue (mkConst rawStepsChkUName)) reflTrue
    added := added.push rawStepsUOkName
    let rawStepsOkName := ns ++ `lmRawSteps_within_fuel
    let rawStepsOkPf ← MetaM.run' <|
      mkEqTrans (mkConst rawStepsEqName) (mkConst rawStepsUOkName)
    addThm rawStepsOkName (eqTrue (mkConst rawStepsChkName)) rawStepsOkPf
    added := added.push rawStepsOkName
    -- Universal vendored-Miri theorem: `Miri.Interpreter.evalOperand` treats
    -- `.Move place` and `.Copy place` identically (by `Eq.refl` for EVERY
    -- `hooks`, `frame`, `state`, `place`, `known`), proving case `2`'s
    -- move-invalidation UB comes strictly from Anneal's `annealEvalOperand`.
    let evalOpMoveEqCopyName := ns ++ `vendored_evalOperand_move_eq_copy
    let (evalOpTy, evalOpPf, forgedEvalOpTy, forgedEvalOpPf) ← MetaM.run' do
      let evalOpC := mkConst `Miri.Interpreter.evalOperand
      let ty ← inferType evalOpC
      forallTelescopeReducing ty fun xs _ => do
        let prov := xs[0]!
        let extra := xs[1]!
        let stTy := xs[2]!
        let hooks := xs[3]!
        let frame := xs[4]!
        let st := xs[5]!
        let known := xs[7]!
        withLocalDeclD `place (mkConst `Miri.MIR.Place) fun place => do
          let mv := mkApp (mkConst `Miri.MIR.Operand.Move) place
          let cp := mkApp (mkConst `Miri.MIR.Operand.Copy) place
          let rc := mkApp (mkConst `Miri.MIR.Operand.RuntimeChecks)
            (mkConst `Miri.MIR.RuntimeChecks.UbChecks)
          let lhs := mkAppN evalOpC #[prov, extra, stTy, hooks, frame, st, mv, known]
          let rhs := mkAppN evalOpC #[prov, extra, stTy, hooks, frame, st, cp, known]
          let badRhs := mkAppN evalOpC #[prov, extra, stTy, hooks, frame, st, rc, known]
          let resTy ← inferType lhs
          let fvars := #[prov, extra, stTy, hooks, frame, st, place, known]
          let thmTy ← mkForallFVars fvars (mkEq resTy lhs rhs)
          let thmPf ← mkLambdaFVars fvars (mkRefl resTy lhs)
          let badTy ← mkForallFVars fvars (mkEq resTy lhs badRhs)
          return (thmTy, thmPf, badTy, thmPf)
    addThm evalOpMoveEqCopyName evalOpTy evalOpPf
    added := added.push evalOpMoveEqCopyName
    -- Direct kernel-evaluated contrast on `ocCase2Mir`: replacing `.move` by
    -- `.copy` (modeling vendored `evalOperand`) turns LeanMiri from `.ub` into
    -- `okScalar 7` (twin-evaluated via `ocRunStepU` and transported along
    -- `ocRunStepU.eq_src`).
    let mkCase2MoveAsCopy (fStep : Expr) : Expr :=
      mkApp2 lmStepObs (toExpr (4 : UInt64))
        (mkApp2 fStep
          (mkApp (mkConst (lmNs ++ `ocEraseBody))
            (mkApp (mkConst (bNs ++ `ocMoveToCopyBody))
              (mkConst (lmNs ++ `ocCase2Mir))))
          (mkConst (lmNs ++ `ocU32Ty)))
    let case2CopyName := ns ++ `lmCase2MoveAsCopy
    let _ ← addDef case2CopyName (mkCase2MoveAsCopy runStepC)
    let case2CopyUName := ns ++ `lmCase2MoveAsCopyU
    let _ ← addDef case2CopyUName (mkCase2MoveAsCopy runStepU)
    added := added.push case2CopyName |>.push case2CopyUName
    let case2CopyEqName := ns ++ `lmCase2MoveAsCopy_eq_unrolled
    let case2CopyEqPf ← MetaM.run' do
      let runStepTy ← inferType runStepC
      let g ← withLocalDeclD `f runStepTy fun f =>
        mkLambdaFVars #[f] (mkCase2MoveAsCopy f)
      mkCongrArg g (mkConst (lmNs ++ `ocRunStepU.eq_src))
    addThmInfer case2CopyEqName case2CopyEqPf
    added := added.push case2CopyEqName
    let mrSc7 := mkApp (mkConst (mrNs ++ `MrOcFpObs.okScalar)) (mkNatLit 7)
    let case2CopyUOkName := ns ++ `lmCase2MoveAsCopyU_eq
    addThm case2CopyUOkName
      (mkEq mrObsTy0 (mkApp lmToMr (mkConst case2CopyUName)) mrSc7)
      (mkRefl mrObsTy0 mrSc7)
    added := added.push case2CopyUOkName
    let case2CopyOkName := ns ++ `lmCase2MoveAsCopy_eq
    let case2CopyOkPf ← MetaM.run' do
      let p1 ← mkCongrArg lmToMr (mkConst case2CopyEqName)
      mkEqTrans p1 (mkConst case2CopyUOkName)
    addThm case2CopyOkName
      (mkEq mrObsTy0 (mkApp lmToMr (mkConst case2CopyName)) mrSc7)
      case2CopyOkPf
    added := added.push case2CopyOkName

    -- 4b. Observer-level 3-way agreement over raw `lmOcObserve` + unified
    -- cross-root 3-engine capstone.
    let olName := ns ++ `observer_level_three_way
    addThmInfer olName
      (mkApp4 (mkConst (bNs ++ `observer_level_three_way)) authC hA lmToMr
        (mkConst (ns ++ `translation_fidelity)))
    added := added.push olName
    let olAllName := ns ++ `observer_level_exact_all_nat
    addThmInfer olAllName
      (mkApp5 (mkConst (bNs ++ `observer_level_exact_all_nat)) authC hA hOob
        lmToMr (mkConst (ns ++ `translation_fidelity)))
    added := added.push olAllName
    let crossName := ns ++ `ep2_cross_root_three_engine_capstone
    let crossPf ← MetaM.run' do
      let parts : List Expr :=
        [ mkConst capName,
          mkConst (ns ++ `translation_fidelity),
          mkConst olName,
          mkConst olAllName,
          mkConst (ns ++ `lmToMr_mrToLm),
          mkConst (ns ++ `mrToLm_lmToMr),
          mkConst (ns ++ `frozenTableLock ++ `ocLmExpectedBasic),
          mkConst (ns ++ `frozenTableLock ++ `ocLmExpectedTb),
          mkConst (ns ++ `trustedTableLock ++ `mrOcTrustedExpectedBasic),
          mkConst (ns ++ `trustedTableLock ++ `mrOcTrustedExpectedTb),
          mkConst (ns ++ `directBundle_eq ++ `unified),
          mkConst (ns ++ `directBundle_eq ++ `d1),
          mkConst (ns ++ `directBundle_eq ++ `d2),
          mkConst (ns ++ `directBundle_eq ++ `d3),
          mkConst rcName,
          mkConst (lmNs ++ `ep1_lean_miri_opaquecast_fnentry_capstone),
          mkConst (lmNs ++ `lmOcObserve_table),
          mkConst (lmNs ++ `lmOcObserve_mode_sensitivity),
          mkConst (lmNs ++ `lmOc_trusted_agreement),
          mkConst compCapName,
          mkConst compCheckName,
          mkConst compCellsName,
          mkConst phaseCheckName,
          mkConst phaseCompCheckName,
          mkConst bmDriverName,
          mkConst pbCapName,
          mkConst phaseOobName,
          mkConst (ns ++ `dual_d1_phase_boundary_all_nat),
          mkConst (ns ++ `postBorrowckBundle_eq ++ `unified),
          mkConst (ns ++ `postBorrowckBundle_eq ++ `d1),
          mkConst (ns ++ `postBorrowckBundle_eq ++ `d2),
          mkConst (ns ++ `postBorrowckBundle_eq ++ `d3),
          mkConst (ns ++ `postBorrowckDomain_bundle_claims),
          mkConst (ns ++ `postBorrowck_modeSensitivity_present),
          mkConst zstLockName,
          mkConst case7LockName,
          mkConst (ns ++ `dual_d1_lowering_dependent_cells),
          mkConst (ns ++ `ocLoweringDependent_characterization),
          mkConst (ns ++ `dual_fuel_and_unsupported_audit),
          mkConst rawStepsOkName,
          mkConst evalOpMoveEqCopyName,
          mkConst case2CopyOkName,
          mkConst (ns ++ `dual_d3_zst_fixture_divergence),
          mkConst runnerUnivName ] ++
        (lockNames.toList.map mkConst)
      let rec conj : List Expr → MetaM Expr
        | [] => return mkConst ``True.intro
        | [p] => return p
        | p :: ps => do mkAppM ``And.intro #[p, ← conj ps]
      conj parts
    addThmInfer crossName crossPf
    added := added.push crossName

    -- 5. Negative forgery controls on scratch environment copies: EVERY forged
    -- declaration MUST be rejected BY THE KERNEL (its error message must be a
    -- `(kernel)` type mismatch) AND paired with an accepted honest twin
    -- (`twins = rejected`).
    let invObserve ← MetaM.run' <|
      withLocalDeclD `tb boolTy fun tb => withLocalDeclD `idx natTy fun idx =>
        mkLambdaFVars #[tb, idx]
          (mkApp2 lmObserveU (mkApp (mkConst ``Bool.not) tb) idx)
    let invAuth := mkAuth invObserve toV
    let swapUbAuth := mkAuth lmObserveU (← MetaM.run' <| mkToVerdict true false)
    let swapPhaseAuth := mkAuth lmObserveU (← MetaM.run' <| mkToVerdict false true)
    let runnerTy ← MetaM.run' <| inferType runnerPf
    let forgedRunnerPf ← MetaM.run' <|
      dischargeRefl (runnerHead (lmOutC `unsupported)) 11
    let forgedRunnerTy ← MetaM.run' <| inferType forgedRunnerPf
    let (rejected, twins) ← runCrossRootForgedControls
      { authUC, invAuth, swapUbAuth, swapPhaseAuth, lmToMr, mrOutToLm,
        runnerTy, runnerPf, forgedRunnerTy, forgedRunnerPf,
        compObsU, erasedULhs, phaseCompObs,
        evalOpTy, evalOpPf, forgedEvalOpTy, forgedEvalOpPf,
        lmStepStopped := lmStepStoppedC, lmErrOutOfFuel,
        nilMir, unsV, noneV }

    -- 6. Axiom / non-triviality audit of every added declaration & LM theorems.
    let env ← getEnv
    let isStdAx (a : Name) : Bool :=
      a == ``propext || a == ``Classical.choice || a == ``Quot.sound
    let rec isTrivialProp : Expr → Bool
      | .forallE _ _ body _ => isTrivialProp body
      | .letE _ _ _ body _ => isTrivialProp body
      | e =>
        if e.isConstOf ``True then true
        else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
        else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
        else false
    let mut crAxioms : NameSet := {}
    for n in added do
      let some ci := env.find? n | throwError "cross-root: {n} missing"
      match ci with
      | .defnInfo v =>
        if v.safety != .safe then throwError "cross-root: {n} is not safe"
      | .thmInfo v =>
        if isTrivialProp v.type then throwError "cross-root: {n} is a trivial theorem"
      | _ => throwError "cross-root: {n} is not a defn or thm"
      for a in ← collectAxioms n do
        unless isStdAx a do
          throwError "cross-root: {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a
    let lmDeepThms : List Name :=
      [ `lmOcObserve_table, `lmOcObserve_out_of_range,
        `lmOcObserve_mode_sensitivity, `lmOcTrustedObserve_table,
        `lmOc_trusted_agreement, `lm_opaqueCast_phase_boundary,
        `lm_d1_phase_boundary_table, `lm_ocEraseBody_cast_free,
        `lm_oc_setDiscriminant_payload_agreement,
        `lm_oc_protected_drop_mode_sensitive,
        `lm_oc_dead_local_ub_non_masking,
        `lm_oc_invalid_bool_ub_non_masking,
        `lm_oc_type_switch_erasure_boundary,
        `lm_oc_d2_rev_transmute_mode_sensitive,
        `lm_oc_d3_zst_dangling_and_null,
        `lm_call_initStackFrame_fnEntry_witness,
        `lm_d3_exact_validityMachine_diagnostics,
        `lm_validityMachine_nonvacuity_witnesses,
        `lm_d3_null_both_halves_ub,
        `ep1_lean_miri_opaquecast_fnentry_capstone ]
    for t in lmDeepThms do
      let n := lmNs ++ t
      let some (.thmInfo v) := env.find? n
        | throwError "cross-root: required LM theorem {n} missing"
      if isTrivialProp v.type then
        throwError "cross-root: LM theorem {n} is trivial"
      for a in ← collectAxioms n do
        unless isStdAx a do
          throwError "cross-root: LM theorem {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a
    unless !(← collectAxioms ``sorryAx).all isStdAx do
      throwError "cross-root self-test: sorryAx was not detected"
    unless !(← collectAxioms ``Lean.ofReduceBool).all isStdAx do
      throwError "cross-root self-test: Lean.ofReduceBool was not detected"
    let trivEq := mkEq natTy (mkNatLit 1) (mkNatLit 1)
    unless isTrivialProp (mkConst ``True) && isTrivialProp trivEq &&
        !isTrivialProp (mkEq natTy (mkNatLit 1) (mkNatLit 2)) do
      throwError "cross-root self-test: trivial theorem detector failed"

    -- 7. Transitive 3-engine reachability across Trusted + MiniRust + Miri.
    let reachFrom (root : Name) : NameSet := Id.run do
      let mut seen : NameSet := {}
      let mut todo : Array Name := #[root]
      while !todo.isEmpty do
        let n := todo.back!
        todo := todo.pop
        if seen.contains n then continue
        seen := seen.insert n
        if let some ci := env.find? n then
          for d in ci.getUsedConstantsAsSet do
            if !seen.contains d then todo := todo.push d
      return seen
    let trustedCore : List Name :=
      [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
        `Trusted.Rustc.V2026_06_01.MirSemantics.stripLeadingOpaqueCast,
        `Trusted.Rustc.V2026_06_01.MirSemantics.eraseLeadingOpaqueCastDecls,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalFnEntryRetag ]
    -- Everything the REAL observers of a closed bundle execute (reached
    -- through the bundle witness itself, not through a conjoined capstone).
    let bundleCore : List Name := trustedCore ++
      [ `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcTrustedObserve,
        `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcObserve,
        `MiniRustSpec.Interp.stepM,
        `MiniRustSpec.Interp.checkPtrM,
        `MiniRustSpec.Interp.ConcurrentMemory.dereferenceable,
        `MiniRustSpec.Interp.TreeBorrowsMemory.retag_ptr,
        `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.lmOcObserve,
        `Miri.Interpreter.Step.step,
        `Miri.Interpreter.project,
        `Miri.Interpreter.Call.initStackFrame,
        `Miri.TreeBorrows.RetagPipeline.retagPointerValue,
        `Miri.Interpreter.ValidityMachine.checkPointerAccess,
        `Miri.Interpreter.ValidityMachine.checkPointerAlign,
        `Miri.Memory.Validity.checkScalar ]
    -- Companion observer: the real vendored-Miri companion harnesses.
    let companionReach : List Name :=
      [ `Miri.Interpreter.Step.step,
        `Miri.TreeBorrows.RetagPipeline.retagPointerValue,
        `Miri.Interpreter.ValidityMachine.checkPointerAccess,
        `Miri.Interpreter.ValidityMachine.checkPointerAlign,
        `Miri.Memory.Validity.checkScalar,
        `Miri.Memory.Validity.checkPrimitive ]
    -- Phase certificate: BOTH vendored projection engines.
    let phaseReach : List Name :=
      [ `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.lmOcPhaseObserve,
        `Miri.Interpreter.project,
        `Miri.Interpreter.PlaceDynamic.project ]
    -- Every vendored-Miri entry point named by the Episode 2 brief.
    let miriAll : List Name :=
      [ `Miri.Interpreter.Step.step,
        `Miri.Interpreter.project,
        `Miri.Interpreter.PlaceDynamic.project,
        `Miri.Interpreter.Call.initStackFrame,
        `Miri.TreeBorrows.RetagPipeline.retagPointerValue,
        `Miri.Interpreter.ValidityMachine.checkPointerAccess,
        `Miri.Interpreter.ValidityMachine.checkPointerAlign,
        `Miri.Memory.Validity.checkScalar,
        `Miri.Memory.Validity.checkPrimitive,
        `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.lmOcObserve,
        `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.lmOcPhaseObserve ]
    -- Closed companion / phase capstone: all three engines.
    let compCapReach : List Name := trustedCore ++ miriAll ++
      [ `MiniRustSpec.Interp.stepM,
        `MiniRustSpec.Interp.checkPtrM,
        `MiniRustSpec.Interp.ConcurrentMemory.dereferenceable,
        `MiniRustSpec.Correspondence.translatePlace,
        `Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec.trustedCompanion,
        `Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec.mrCompanion,
        `Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec.mrOcPhaseObserve,
        `Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec.mrOcPhaseCompanion ]
    -- Universal runner lock: both copies of the shared Trusted runner.
    let runnerReach : List Name :=
      [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
        `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocTrustedStep,
        `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocRunTrustedRaw,
        `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.ocTrustedStep,
        `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.ocRunTrustedRaw ]
    let crossReach : List Name := trustedCore ++ miriAll ++
      [ `MiniRustSpec.Interp.stepM,
        `MiniRustSpec.Interp.steps,
        `MiniRustSpec.Interp.stepsTB,
        `MiniRustSpec.Interp.checkPtr,
        `MiniRustSpec.Interp.checkPtrM,
        `MiniRustSpec.Interp.CM.dereferenceable,
        `MiniRustSpec.Interp.ConcurrentMemory.dereferenceable,
        `MiniRustSpec.Correspondence.translatePlace,
        `MiniRustSpec.Correspondence.stepM_bm_eq,
        `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.ep1_lean_miri_opaquecast_fnentry_capstone ]
    -- Post-borrowck bundles: Trusted on the cast-erased image.
    let erasedReach : List Name :=
      [ `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcTrustedErasedObserve,
        `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocEraseBody,
        `Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec.trustedPostBorrowckObserve ]
    let twinU : List Name :=
      [ `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.lmOcObserveU ]
    let reqs : List (Name × List Name) :=
      [ (unifiedName, bundleCore ++ twinU),
        (directBundle, bundleCore ++ twinU),
        (ns ++ `domainBundle ++ `d1, bundleCore),
        (ns ++ `domainBundle ++ `d2, bundleCore),
        (ns ++ `domainBundle ++ `d3, bundleCore),
        (compObsName, companionReach),
        (phaseCheckName, phaseReach),
        (phaseCompCheckName,
          [ `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.lmOcPhaseObserveBody,
            `Miri.Interpreter.project,
            `Miri.Interpreter.PlaceDynamic.project ]),
        (compCapName, compCapReach),
        (pbUnifiedName, bundleCore ++ erasedReach),
        (pbD1Name, bundleCore ++ erasedReach),
        (pbD2Name, bundleCore ++ erasedReach),
        (pbD3Name, bundleCore ++ erasedReach),
        (pbCapName, trustedCore ++ erasedReach ++
          [ `Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec.trustedUniformErasedObserve,
            `MiniRustSpec.Interp.stepM,
            `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.lmOcObserve,
            `Miri.Interpreter.Step.step ]),
        (bmDriverName,
          [ `MiniRustSpec.Interp.steps,
            `MiniRustSpec.Interp.stepM,
            `MiniRustSpec.Correspondence.stepM_bm_eq ]),
        (evalOpMoveEqCopyName, [`Miri.Interpreter.evalOperand]),
        (case2CopyName,
          [ `Miri.Interpreter.Step.step,
            `LeanMiriSpec.Correspondence.annealEvalOperand ]),
        (rawStepsOkName,
          [ `Miri.Interpreter.Step.step,
            `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.ocRunStep,
            `Miri.Interpreter.StepError.rec ]),
        (ns ++ `dual_fuel_and_unsupported_audit,
          [ `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
            `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocRunTrustedRaw,
            `MiniRustSpec.CrossFrameRefAndPanicMR.runToStopM ]),
        (runnerUnivName, runnerReach),
        (crossName, crossReach) ]
    let mut reachChecked : Nat := 0
    for (root, rs) in reqs do
      let seen := reachFrom root
      for r in rs do
        unless env.contains r do
          throwError "cross-root reachability: {r} is not a constant"
        unless seen.contains r do
          throwError "cross-root reachability failure: {root} does not reach {r}"
        reachChecked := reachChecked + 1
    -- Per-cell companion reachability + anti-Trusted audit: EVERY ONE of the 7
    -- companion branches plus `lmErasedInvalidBool` MUST reach its specific
    -- vendored Miri entry point AND MUST NOT reach Trusted `stepMirFn`.
    let reachFromExpr (e : Expr) : NameSet := Id.run do
      let mut seen : NameSet := {}
      let mut todo : Array Name := e.getUsedConstants
      while !todo.isEmpty do
        let n := todo.back!
        todo := todo.pop
        if seen.contains n then continue
        seen := seen.insert n
        if let some ci := env.find? n then
          for d in ci.getUsedConstantsAsSet do
            if !seen.contains d then todo := todo.push d
      return seen
    let stepMirFnName := `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn
    let mrStepMName := `MiniRustSpec.Interp.stepM
    -- Mutual 3-way authority independence: NONE of Authority 2 (LeanMiri)'s
    -- canonical, companion, or phase observers reach Authority 0 (Trusted
    -- `stepMirFn`) OR Authority 1 (MiniRust `stepM`).
    for (lmTag, lmExpr) in
        [ (`lmOcObserve, lmObserve),
          (`lmCompanionObserve, compObs),
          (`lmOcPhaseObserve, lmPhaseObs),
          (`lmPhaseCompanion, phaseCompObs),
          (`lmCase2MoveAsCopy, mkConst case2CopyName),
          (`lmRawStepsCheck, mkConst rawStepsChkName) ] do
      let seen := reachFromExpr lmExpr
      if seen.contains stepMirFnName then
        throwError "authority-independence audit FAILED: LM {lmTag} reaches Trusted stepMirFn"
      if seen.contains mrStepMName then
        throwError "authority-independence audit FAILED: LM {lmTag} reaches MiniRust stepM"
    -- Lowering-dependent case `2`: the LeanMiri `Step.step` run reaches the
    -- Anneal adapter `annealEvalOperand` (the move-invalidating operand hook)
    -- and the vendored `Miri.Interpreter.evalOperand` (which does not
    -- invalidate moved locals) is a distinct constant.
    let case2Run := mkApp2 runStepC
      (mkApp (mkConst (lmNs ++ `ocEraseBody)) (mkConst (lmNs ++ `ocCase2Mir)))
      (mkConst (lmNs ++ `ocU32Ty))
    let case2Seen := reachFromExpr case2Run
    unless env.contains `Miri.Interpreter.evalOperand do
      throwError "lowering audit: vendored Miri.Interpreter.evalOperand missing"
    unless case2Seen.contains `LeanMiriSpec.Correspondence.annealEvalOperand ||
        case2Seen.contains `LeanMiriSpec.Correspondence.annealEvalOperandLM2_3 do
      throwError "lowering audit: LM case 2 does not reach the Anneal adapter annealEvalOperand"
    reachChecked := reachChecked + 1
    -- Self-test: MiniRust `mrOcObserve` IS caught by the anti-MiniRust check.
    unless (reachFromExpr (mkConst (mrNs ++ `mrOcObserve))).contains mrStepMName do
      throwError "anti-MiniRust self-test failed: mrOcObserve not caught"
    let perCellReqs : List (Name × Expr × List Name) :=
      [ (`payload,
          mkCompBranch runStepC protDropC invBoolC revTrC ptrValC (toExpr false) `payload,
          [`Miri.Interpreter.Step.step]),
        (`protectedDrop,
          mkCompBranch runStepC protDropC invBoolC revTrC ptrValC (toExpr true) `protectedDrop,
          [`Miri.TreeBorrows.RetagPipeline.retagPointerValue,
           `Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite]),
        (`deadLocal,
          mkCompBranch runStepC protDropC invBoolC revTrC ptrValC (toExpr false) `deadLocal,
          [`Miri.Interpreter.Step.step]),
        (`invalidBool,
          mkCompBranch runStepC protDropC invBoolC revTrC ptrValC (toExpr false) `invalidBool,
          [`Miri.Memory.Validity.checkPrimitive]),
        (`revTransmute,
          mkCompBranch runStepC protDropC invBoolC revTrC ptrValC (toExpr true) `revTransmute,
          [`Miri.TreeBorrows.RetagPipeline.retagPointerValue,
           `Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite]),
        (`zstDangling,
          mkCompBranch runStepC protDropC invBoolC revTrC ptrValC (toExpr false) `zstDangling,
          [`Miri.Memory.Validity.checkScalar,
           `Miri.Interpreter.ValidityMachine.checkPointerAccess,
           `Miri.Interpreter.ValidityMachine.checkPointerAlign]),
        (`zstNull,
          mkCompBranch runStepC protDropC invBoolC revTrC ptrValC (toExpr false) `zstNull,
          [`Miri.Memory.Validity.checkScalar,
           `Miri.Interpreter.ValidityMachine.checkPointerAccess,
           `Miri.Interpreter.ValidityMachine.checkPointerAlign]),
        (`erasedInvalidBool, mkErased runStepC,
          [`Miri.Interpreter.Step.step]) ]
    for (cellTag, expr, reqsC) in perCellReqs do
      let seen := reachFromExpr expr
      if seen.contains stepMirFnName then
        throwError "per-cell companion audit FAILED: LM cell {cellTag} reaches Trusted stepMirFn"
      if seen.contains mrStepMName then
        throwError "per-cell companion audit FAILED: LM cell {cellTag} reaches MiniRust stepM"
      for r in reqsC do
        unless seen.contains r do
          throwError "per-cell companion audit FAILED: LM cell {cellTag} does not reach {r}"
        reachChecked := reachChecked + 1
    -- Self-test: the anti-Trusted detector catches Trusted `mrOcTrustedObserve`.
    unless (reachFromExpr (mkConst (mrNs ++ `mrOcTrustedObserve))).contains stepMirFnName do
      throwError "per-cell anti-Trusted self-test failed: mrOcTrustedObserve not caught"
    -- The vendored projection engines live in the modules named by the
    -- Episode 2 brief (`Miri.Interpreter.Projection` / `.PlaceDynamic`).
    for (c, m) in [(`Miri.Interpreter.project, `Miri.Interpreter.Projection),
                   (`Miri.Interpreter.PlaceDynamic.project,
                    `Miri.Interpreter.PlaceDynamic)] do
      let declMod := (env.getModuleIdxFor? c).map
        fun i => env.header.moduleNames[i.toNat]!
      unless declMod == some m do
        throwError "cross-root reachability: {c} is declared in {declMod}, expected {m}"
    -- Reachability self-test: a root-only observer never reaches vendored Miri.
    if (reachFrom `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.mrOcObserve).contains
        `Miri.Interpreter.Step.step then
      throwError "cross-root reachability self-test failed: mrOcObserve reaches Miri"
    return (added.size, bundleCount, eqLockCount, sharedTopLevel,
      rejected, twins, reachChecked, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<oc-fp-cross-root>", fileMap := default,
      options := opts, maxHeartbeats := 0 }
  let ((addedCount, bundleCount, eqLockCount, sharedCount,
        rejectedCount, twinCount, reachCount, crAxioms), _) ←
    liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount ≥ 245 && bundleCount = 8 && eqLockCount = 94 &&
      sharedCount = 98 && rejectedCount ≥ 115 &&
      twinCount = rejectedCount && reachCount ≥ 279 do
    throwError "cross-root: unexpected counts (added={addedCount}, bundles={bundleCount}, eqLocks={eqLockCount}, shared={sharedCount}, rejected={rejectedCount}, twins={twinCount}, reach={reachCount})"
  logInfo m!"oc/fp cross-root kernel bridge: added {addedCount} declarations ({bundleCount} bundles; {eqLockCount} Eq.refl + 2 bijection + 2 universal runner + 1 ocCombine locks covering {sharedCount}/98 shared MR/LM declarations), kernel-rejected {rejectedCount} forged controls ({twinCount}/{rejectedCount} honest twins accepted), {reachCount} reachability edges across Trusted+MiniRust+Miri, axioms {crAxioms}"

/-! ## §3. Constructive Purity, Axiom Audit, and Auditor Self-Tests -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let bNs := `Anneal.Mir.OpaqueCastAndFnEntryProtectorDualSpec
  let constructiveDecls : List Name :=
    [ `ocCodec, `ocEncode_decode_of_valid, `ocCodec_tight,
      `ocCodec_encode_injective, `ocCodec_decode_injective_on_valid,
      `ocValidRep_iff_decode_isSome, `ocCodec_rejects_malformed,
      `ocModel, `ocAnnealEval, `mrVerdict, `trustedVerdict,
      `lmTableCheckOf_sound, `lmTableCheckOf_of_eq, `cert_transport,
      `mrSide_check, `lmCheckOf_of_table, `bundleOfSel, `bundleOf,
      `domainBundleOf, `threeWayNormalAgreement, `crossAuthorityFaultEquiv,
      `exactBehaviorEq_both, `projectPositive, `projectFault,
      `modeSensitivity_present, `bundle_gate_castDerefBoundary,
      `unified_bundle_witness_kinds, `domain_bundle_claims,
      `dual_exact_three_way_classification, `dual_no_specPanic_all_cells,
      `ocVerdictOf_injective, `lmTable_vs_tables,
      `observer_level_three_way, `observer_level_exact_all_nat,
      `dual_fail_closed_out_of_range, `dual_mode_sensitivity_exact,
      `dual_d2_mode_sensitivity_all_three, `dual_d1_cast_erasure_and_boundary,
      `dual_d2_fnentry_protectors_and_transmute_boundary,
      `dual_d3_dereferenceable_and_zst_boundary,
      `ocTerminatesCleanly, `dual_d2_machine_termination_contrast,
      `rootBackedLmAuthority, `rootBackedLmAuthority_tableCheck,
      `rootBackedLmAuthority_failClosed, `rootBacked_observer_level,
      `stepsM_eq_runToStopM, `stepsTB_eq_runToStopM,
      `steps_eq_runToStopM_bm_of,
      `allOcFpCompanions, `allOcFpCompanions_complete,
      `trustedCompanion, `mrCompanion, `trustedCompanion_table,
      `mrCompanion_table, `OcFpLmCompanionCells,
      `lmCompanionCheckOf, `lmCompanionCheckOf_sound, `lmCompanionCheckOf_of_eq,
      `dual_companion_three_way,
      `dual_companion_mode_sensitivity, `dual_type_switch_erasure_boundary,
      `mrOcPhaseObserveBody, `mrOcPhaseObserve, `mrOcPhaseObserve_out_of_range,
      `mrOcPhaseObserve_table, `ocPhaseExpected_cell,
      `ocCompanionBody, `ocCompanionIsD1, `mrOcPhaseCompanion,
      `mrOcPhaseCompanion_table, `lmPhaseCompanionCheckOf,
      `dual_d1_companion_phase_boundary,
      `lmPhaseCheckOf, `dual_d1_phase_boundary,
      `ocStepG, `ocTrustedStep_running_eq, `ocStepG_natural, `repeat_natural,
      `ocRunner_copy_lock, `ocCombine_copy_lock,
      `rootBackedCompanion, `rootBackedCompanion_cells,
      `rootBackedCompanion_check,
      `rootBackedPhase_check, `rootBackedPhaseCompanion_check,
      `rootBackedErased_eq,
      `ep2_opaquecast_fnentry_dual_authority_capstone,
      `ep2_opaquecast_fnentry_dual_authority_capstone_nonvacuous,
      `ep2_opaquecast_fnentry_companion_phase_capstone,
      `ep2_opaquecast_fnentry_companion_phase_capstone_nonvacuous,
      `dual_d3_zst_fixture_divergence,
      `ocCaseFixture?_out_of_range, `ocDomainOf_d1_iff,
      `phase_fail_closed_of_fixture, `dual_d1_phase_boundary_all_nat,
      `trustedPostBorrowckObserve, `trustedPostBorrowckObserve_table,
      `trustedPostBorrowckVerdict_cell, `ocPostBorrowckModel,
      `postBorrowckGate, `mrPostBorrowckSide_check,
      `lmPostBorrowckCheckOf_of_table, `postBorrowckBundleOfSel,
      `postBorrowckBundleOf, `postBorrowckDomainBundleOf,
      `post_borrowck_bundle_closes_case8, `dual_post_borrowck_case8,
      `dual_post_borrowck_exact_all_nat,
      `trustedUniformErasedObserve, `ocEraseBody_ne_of_hasCast,
      `ocEraseBody_fixture_fixed_iff, `ocEraseBody_companion_fixed_iff,
      `trustedPostBorrowckObserve_eq_uniform_erased,
      `postBorrowckDomain_bundle_claims, `postBorrowck_modeSensitivity_present,
      `ocBodyHasDrop, `ocMoveToCopyOperand, `ocMoveToCopyRvalue,
      `ocMoveToCopyStmt, `ocMoveToCopyBody, `ocDropToNopBody,
      `ocLoweringDependent, `dual_d1_lowering_dependent_cells,
      `ocLoweringDependent_characterization,
      `trustedRawOutcome, `ocOutcomeTag, `mrOcTrustedObserve_eq_raw,
      `trustedRawAuxOutcomes, `mrProgStopsWithinFuel, `mrAuxProgs,
      `dual_fuel_and_unsupported_audit,
      `ep2_opaquecast_fnentry_post_borrowck_capstone,
      `ep2_opaquecast_fnentry_post_borrowck_capstone_nonvacuous ]
  let isChoiceFree (axs : Array Name) : Bool :=
    axs.all fun a => a == ``propext || a == ``Quot.sound
  for d in constructiveDecls do
    let axs ← liftCoreM <| Lean.collectAxioms (bNs ++ d)
    unless isChoiceFree axs do
      throwError "constructive audit failure: {d} uses non-constructive axiom ({axs})"
  -- Exhaustive 100% choice-free audit across the ENTIRE
  -- `OpaqueCastAndFnEntryProtectorDualSpec` module (zero allowlist entries!).
  let some modIdx := env.getModuleIdx? bNs
    | throwError "constructive audit failure: module {bNs} not found"
  let modData := env.header.moduleData[modIdx.toNat]!
  let mut exhaustiveChoiceFree : Nat := 0
  for c in modData.constNames do
    if bNs.isPrefixOf c then
      let axs ← liftCoreM <| Lean.collectAxioms c
      unless isChoiceFree axs do
        throwError "exhaustive constructive audit failure: {c} uses non-constructive axiom ({axs})"
      exhaustiveChoiceFree := exhaustiveChoiceFree + 1
  unless exhaustiveChoiceFree ≥ 500 do
    throwError "exhaustive constructive audit vacuous: only {exhaustiveChoiceFree} decls checked"
  -- Self-tests: constructive check rejects `Classical.choice`; standard-axiom
  -- check rejects `sorryAx` and `Lean.ofReduceBool`; trivial-prop detector
  -- rejects `True`, `1 = 1`, `∀ x, x = x`.
  let rec isTrivialProp : Expr → Bool
    | .forallE _ _ body _ => isTrivialProp body
    | .letE _ _ _ body _ => isTrivialProp body
    | e =>
      if e.isConstOf ``True then true
      else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
      else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
      else false
  unless !isChoiceFree (← liftCoreM <| Lean.collectAxioms ``Classical.em) do
    throwError "self-test: Classical.choice was not detected"
  unless !(← liftCoreM <| Lean.collectAxioms ``sorryAx).all
      (fun a => a == ``propext || a == ``Quot.sound || a == ``Classical.choice) do
    throwError "self-test: sorryAx was not detected"
  unless !(← liftCoreM <| Lean.collectAxioms ``Lean.ofReduceBool).all
      (fun a => a == ``propext || a == ``Quot.sound || a == ``Classical.choice) do
    throwError "self-test: Lean.ofReduceBool was not detected"
  let natTy := mkConst ``Nat
  let eq11 := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 1)
  let eq12 := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 2)
  let forallEq := Expr.forallE `x natTy
    (mkApp3 (mkConst ``Eq [1]) natTy (.bvar 0) (.bvar 0)) .default
  unless isTrivialProp (mkConst ``True) && isTrivialProp eq11 &&
      isTrivialProp forallEq && !isTrivialProp eq12 do
    throwError "self-test: trivial theorem detector failed in §3"
  let tNs := `Anneal.Mir.OpaqueCastAndFnEntryProtectorCorrespondenceTests
  let mut checked : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    if let .thmInfo v := info then
      if tNs.isPrefixOf c && !c.isInternal && isTrivialProp v.type then
        throwError "test audit failure: {c} is a trivial theorem"
    for a in ← liftCoreM <| Lean.collectAxioms c do
      if a == ``sorryAx then throwError "test audit failure: {c} uses sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "test audit failure: {c} uses non-standard axiom {a}"
    if tNs.isPrefixOf c then checked := checked + 1
  unless checked ≥ 17 do
    throwError "test audit vacuous: only {checked} test declarations"
  logInfo m!"oc/fp constructive audit: {exhaustiveChoiceFree} DualSpec decls ({constructiveDecls.length} spotlighted) 100% in [propext, Quot.sound]; {checked} test decls non-trivial & standard-axiom clean"

end Anneal.Mir.OpaqueCastAndFnEntryProtectorCorrespondenceTests
