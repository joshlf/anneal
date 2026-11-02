import Trusted.Refinement
import MiniRust.LibSpecr
import Correspondence.Framework
import Correspondence.DialectInterface
import Correspondence.GeneratedGaps
import Correspondence.GeneratedGapWitnesses
import Correspondence.V2026_06_01.L1_Scalars
import Correspondence.V2026_06_01.L2_BytesAndLayout
import Correspondence.V2026_06_01.L3_PlacesAndBasicMem
import Correspondence.V2026_06_01.L4_TreeBorrows

/-!
# `Correspondence.V2026_06_01.Scorecard` — Machine-Checked Multi-Version Rollup

Aggregates all foundation bridges (`M0`), non-correspondence ratchets & non-vacuity
proofs (`M2`), and universal horizontal correspondence slices (`L1`–`L4`, `M3`–`M4`)
directly over `Trusted.Rustc.V2026_06_01.MirSemantics` into a single kernel-checked
proposition `CorrespondenceScorecard` proved with zero unproven assumptions
(`theorem all_correspondence_slices_verified`).
-/

namespace Correspondence.V2026_06_01.Scorecard

open Trusted.Refinement
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRust.LibSpecr
open Correspondence
open Correspondence.V2026_06_01.L1_Scalars
open Correspondence.V2026_06_01.L2_BytesAndLayout
open Correspondence.V2026_06_01.L3_PlacesAndBasicMem
open Correspondence.V2026_06_01.L4_TreeBorrows

/--
Master machine-checked proposition certifying every foundation bridge, universal
slice theorem across `L1`–`L4` over `Trusted.Rustc.V2026_06_01.MirSemantics`,
two-way divergence witness, non-vacuity check, and multi-snapshot epoch separation.
-/
structure CorrespondenceScorecard : Prop where
  /-- M0: Deterministic evaluator soundness under `Trusted.Refinement.Partial`. -/
  m0_evalDet_sound :
    ∀ (c : NdComp Verdict) (h_def : (NdComp.toPartialBehavior c).defined) (s : Nat),
      (∀ msg : String, NdComp.evalDet s c ≠ .error (.ub msg)) ∧
      (∀ v : Verdict, NdComp.evalDet s c = .ok v → (NdComp.toPartialBehavior c).val h_def v)
  /-- M0: Top-element refinement for conservative UB and unmodeled features. -/
  m0_top_refines :
    ∀ (c : NdComp Verdict),
      NdComp.toPartialBehavior c ≤ (Partial.ub : Partial (BehaviorSet Verdict))
  /-- M2: Canonical baseline fixtures never trigger any registered gap guard. -/
  m2_non_vacuity :
    allCanonicalFixturesAvoidAllGaps = true
  /-- M2: Every non-gap fixture agrees 100% identically across all snapshots. -/
  m2_universal_guarded_agreement :
    ∀ (snap : MiniRustSnap) (prog : FixtureProg),
      hitsAnyGap
        (activeBugGaps .V2026_06_01 snap ++ activeEpochDivergences .V2026_06_01 snap)
        defaultFixtureState
        prog = false →
      evalAnnealV2026_06_01 prog defaultFixtureState = evalMiniRustSnapshot snap prog
  /-- M3 (`L1_Scalars`): Universal modular wrapping correspondence over `MirSemantics.wrapScalarBits`. -/
  l1_wrap_scalar_corresponds :
    ∀ (val sizeBytes : Nat),
      wrapScalarBits val (scalarModulus sizeBytes) = val % (256 ^ sizeBytes)
  /-- M3 (`L2_BytesAndLayout`): Universal little-endian byte encode/decode round-trip over `MirSemantics.{encodeLittleEndianBytes,decodeLittleEndianBytes}`. -/
  l2_le_roundtrip_corresponds :
    ∀ (numBytes bits : Nat),
      bits < scalarModulus numBytes →
      decodeLittleEndianBytes (encodeLittleEndianBytes bits numBytes none) = some (bits, none)
  /-- M4 (`L3_PlacesAndBasicMem`): Universal `MirSemantics.{readProjectedValue,writePlaceValue}` soundness + spatial/aliasing bisection. -/
  l3_memory_bisection :
    (∀ (locals : List LocalSlot) (actualVariant targetVariant : Nat)
        (fields : List Value) (variantName : String) (rest : List ProjectionElem),
      Nat.beq actualVariant targetVariant = false →
      readProjectedValue locals (.aggregate actualVariant fields)
        (.downcast variantName targetVariant :: rest) = .ub) ∧
    (∀ (restLocals : List LocalSlot) (borrows : List BorrowEntry) (v : Value),
      writePlaceValue (.dead :: restLocals) borrows { local_ := 0, projection := .nil } v = .ub) ∧
    (∀ (mem : BasicMemory) (ptr : MrPointer) (reqAlign : Align) (len : Nat),
      Align.isAligned ptr.offset reqAlign = false →
      basicMemCheckAccess mem ptr reqAlign len = .error (.ub "misaligned pointer access"))
  /-- M4 (`L4_TreeBorrows`): Universal correspondence directly over `MirSemantics.updateBorrowPerm` + `Freeze` Tree Borrows transitions. -/
  l4_tree_borrows_freeze_corresponds :
    (∀ (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat),
      (updateBorrowPerm entry targetLocal writerTag).perm =
        mrExpectedWritePerm entry targetLocal writerTag ∧
      (updateBorrowPerm entry targetLocal writerTag).tag = entry.tag ∧
      (updateBorrowPerm entry targetLocal writerTag).targetLocal = entry.targetLocal) ∧
    (∀ (snap : MiniRustSnap) (perm : TreeBorrowPerm) (loc : TbLocality)
        (acc : TbAccessKind) (prot : Bool),
      annealStepTreeBorrowPerm perm loc acc prot =
        mrStepTreeBorrowPerm snap false perm loc acc prot)
  /-- M4/M5: Epoch divergence cleanly separates `S2026_05_Matched` (`[]`) from `S2026_07_BleedingEdge`. -/
  epoch_matrix_separation :
    activeEpochDivergences .V2026_06_01 .S2026_05_Matched = [] ∧
    activeEpochDivergences .V2026_06_01 .S2026_07_BleedingEdge = [.GAP_EPOCH_0001]

/--
**Top-Level Rollup Certificate (`all_correspondence_slices_verified`)**:
Constructs a complete proof of `CorrespondenceScorecard` using only standard
Lean 4 kernel foundations (`propext`, `Quot.sound`).
-/
theorem all_correspondence_slices_verified : CorrespondenceScorecard where
  m0_evalDet_sound := NdComp.evalDet_sound_of_defined
  m0_top_refines := NdComp.top_refines_unsupported
  m2_non_vacuity := allCanonicalFixturesAvoidGaps
  m2_universal_guarded_agreement := all_non_gap_fixtures_agree_exact
  l1_wrap_scalar_corresponds := wrapScalarBits_eq_mod
  l2_le_roundtrip_corresponds := decode_encode_little_endian_roundtrip
  l3_memory_bisection :=
    ⟨mir_readProjectedValue_downcast_mismatch_is_ub,
     mir_writePlaceValue_dead_local_is_ub,
     basicMem_misaligned_access_is_ub⟩
  l4_tree_borrows_freeze_corresponds :=
    ⟨mir_updateBorrowPerm_corresponds_to_minirust_write,
     treeBorrow_transition_corresponds_for_freeze⟩
  epoch_matrix_separation := matched_snapshot_has_zero_epoch_divergences

end Correspondence.V2026_06_01.Scorecard
