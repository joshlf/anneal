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
import Correspondence.V2026_06_01.L5_ControlAndCalls
import Correspondence.V2026_06_01.L6_WholeMachine

/-!
# `Correspondence.V2026_06_01.Scorecard` — Machine-Checked Multi-Version Rollup

Aggregates all foundation bridges (`M0`), non-correspondence ratchets & non-vacuity
proofs (`M2`), and universal horizontal correspondence slices (`L1`–`L6`, `M3`–`M4`)
directly over `Trusted.Rustc.V2026_06_01.MirSemantics` into a single kernel-checked
proposition `CorrespondenceScorecard` proved with zero unproven assumptions
(`theorem all_correspondence_slices_verified`).
-/

namespace Correspondence.V2026_06_01.Scorecard

open Trusted.Sequence
open Trusted.Refinement
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRust.LibSpecr
open Correspondence
open Correspondence.V2026_06_01.L1_Scalars
open Correspondence.V2026_06_01.L2_BytesAndLayout
open Correspondence.V2026_06_01.L3_PlacesAndBasicMem
open Correspondence.V2026_06_01.L4_TreeBorrows
open Correspondence.V2026_06_01.L5_ControlAndCalls
open Correspondence.V2026_06_01.L6_WholeMachine

/--
Master machine-checked proposition certifying every foundation bridge, universal
slice theorem across `L1`–`L6` over `Trusted.Rustc.V2026_06_01.MirSemantics`,
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
  /-- M4 (`L5_ControlAndCalls`): Universal statement PC, `lookupSwitchTarget`, `findCallee?`, and terminator correspondence over `MirSemantics.{Statements,Terminators}` vs. `Generated.Ops`. -/
  l5_control_and_calls_corresponds :
    (∀ (s : MachineState) (locals' : List LocalSlot) (mem' : Memory),
      (advanceStmt s locals' mem').frame.stmtIdx =
        MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.mrAdvanceStmtPc s.frame.stmtIdx ∧
      (advanceStmt s locals' mem').frame.blockIdx = s.frame.blockIdx ∧
      (advanceStmt s locals' mem').frame.locals = locals' ∧
      (advanceStmt s locals' mem').memory = mem' ∧
      toMrStackFrame (advanceStmt s locals' mem').frame =
        { toMrStackFrame s.frame with
          stmtIdx := MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.mrAdvanceStmtPc s.frame.stmtIdx }) ∧
    (∀ (val : Nat) (branches : List (Nat × BasicBlockIdx)) (otherwise : BasicBlockIdx),
      lookupSwitchTarget val branches otherwise =
        MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.mrLookupSwitchTarget val branches otherwise) ∧
    (∀ (s : MachineState) (target : BasicBlockIdx) (span : String) (currentBody : Option CapturedMir),
      evalTerminator s ⟨.goto target, span⟩ currentBody =
        MirStepNode.step { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } } ∧
      toMrStackFrame { s.frame with blockIdx := target, stmtIdx := 0 } =
        MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.MrStackFrame.jump_to_block
          (toMrStackFrame s.frame) target) ∧
    (∀ (s : MachineState) (span : String) (currentBody : Option CapturedMir),
      evalTerminator s ⟨.unreachable, span⟩ currentBody = MirStepNode.fail .ub) ∧
    (∀ (s : MachineState) (discr : Operand) (targets : SwitchTargets)
       (span : String) (currentBody : Option CapturedMir),
      let bodyLayouts := match currentBody with | .some b => b.layouts | .none => emptyLayoutTable
      (∀ (sc : ScalarInt) (locals' : List LocalSlot),
        evalOperand s.frame.locals discr s.memory.borrows s.memory.globals bodyLayouts s.memory.callerLocals =
          .ok (.scalar sc) locals' →
        let target := MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.mrLookupSwitchTarget sc.bits targets.branches targets.otherwise
        evalTerminator s ⟨.switchInt discr targets, span⟩ currentBody =
          MirStepNode.emitStep (.event sc.bits)
            { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } } ∧
        toMrStackFrame { blockIdx := target, stmtIdx := 0, locals := locals' } =
          MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.MrStackFrame.jump_to_block (toMrStackFrame s.frame) target) ∧
      (evalOperand s.frame.locals discr s.memory.borrows s.memory.globals bodyLayouts s.memory.callerLocals = .ub →
        evalTerminator s ⟨.switchInt discr targets, span⟩ currentBody = MirStepNode.fail .ub))
  /-- M4 (`L6_WholeMachine`): Universal whole-machine PC dispatch, coalgebra simulation, and `Trusted.Refinement.GuardedRefines` correspondence over `MirSemantics.Machine`. -/
  l6_whole_machine_simulation_and_refinement :
    (∀ (body : CapturedMir) (s : MachineState) (out : MirOutcome)
       (fk : Trusted.Effect.FailureKind) (args : List Value),
      stepMirState body (.running s) = stepMirFn body s ∧
      stepMirState body (.halted out) = .ret out ∧
      stepMirState body (.faulted fk) = MirStepNode.fail fk ∧
      (mirTree body s).observe = (stepMirFn body s).map (Trusted.ITree.ITree.cofix (stepMirState body)) ∧
      mirCallTree body args = mirTree body (initMachineState body args) ∧
      MirNoUBTree (mirTree body s) = Trusted.ITree.TreeSafe (mirTree body s)) ∧
    (∀ (body : CapturedMir) (st : MirExecState)
       (snap : MiniRustSnap) (prog : FixtureProg),
      GuardedRefines
        (guardPropSpec True)
        NdComp.toPartialBehavior
        (mirStepNodeBehavior (stepMirState body st))
        (stepMirStateNd body st) ∧
      GuardedRefines
        (guardPropSpec
          (hitsAnyGap
            (activeBugGaps .V2026_06_01 snap ++ activeEpochDivergences .V2026_06_01 snap)
            defaultFixtureState
            prog = false))
        NdComp.toPartialBehavior
        (evalAnnealV2026_06_01 prog defaultFixtureState).toPartial
        (verdictToNdComp (evalMiniRustSnapshot snap prog)))
  /-- M4/M5: Epoch divergence cleanly separates `S2026_05_Matched` (`[]`) from `S2026_07_BleedingEdge`. -/
  epoch_matrix_separation :
    activeEpochDivergences .V2026_06_01 .S2026_05_Matched = [] ∧
    activeEpochDivergences .V2026_06_01 .S2026_07_BleedingEdge = [.GAP_EPOCH_0001]

/--
Per-cell `(AnnealVer × MiniRustSnap × SemanticLayer)` correspondence matrix entry
reflected into Lean 4 (`correspondence_matrix.toml`).
-/
structure ScorecardCell : Type where
  annealVersion : AnnealVer
  minirustSnapshot : MiniRustSnap
  layer : SemanticLayer
  expectedTier : ExpectedTier
  maxOpenBugs : Nat
  deriving DecidableEq, Repr

/--
Machine-checked `V2026_06_01` correspondence matrix table (`v2026_06_01_scorecard`)
ratcheting all 6 layers (`L1_Scalars`..`L6_WholeMachine`) of `V2026_06_01` × `S2026_05_Matched`
to `ExpectedTier.ExactUnconditional` with `maxOpenBugs := 0`, and `V2026_06_01` × `S2026_07_BleedingEdge`
to `ExpectedTier.ExactUnconditional` on `L1`, `L2`, `L3`, `L5` and `ExpectedTier.EpochDeltaOnly`
on `L4`, `L6` with `maxOpenBugs := 0`.
-/
@[reducible]
def v2026_06_01_scorecard : List ScorecardCell :=
  [ { annealVersion := .V2026_06_01, minirustSnapshot := .S2026_05_Matched, layer := .L1_Scalars, expectedTier := .ExactUnconditional, maxOpenBugs := 0 }
  , { annealVersion := .V2026_06_01, minirustSnapshot := .S2026_05_Matched, layer := .L2_BytesAndLayout, expectedTier := .ExactUnconditional, maxOpenBugs := 0 }
  , { annealVersion := .V2026_06_01, minirustSnapshot := .S2026_05_Matched, layer := .L3_PlacesAndBasicMem, expectedTier := .ExactUnconditional, maxOpenBugs := 0 }
  , { annealVersion := .V2026_06_01, minirustSnapshot := .S2026_05_Matched, layer := .L4_TreeBorrows, expectedTier := .ExactUnconditional, maxOpenBugs := 0 }
  , { annealVersion := .V2026_06_01, minirustSnapshot := .S2026_05_Matched, layer := .L5_ControlAndCalls, expectedTier := .ExactUnconditional, maxOpenBugs := 0 }
  , { annealVersion := .V2026_06_01, minirustSnapshot := .S2026_05_Matched, layer := .L6_WholeMachine, expectedTier := .ExactUnconditional, maxOpenBugs := 0 }
  , { annealVersion := .V2026_06_01, minirustSnapshot := .S2026_07_BleedingEdge, layer := .L1_Scalars, expectedTier := .ExactUnconditional, maxOpenBugs := 0 }
  , { annealVersion := .V2026_06_01, minirustSnapshot := .S2026_07_BleedingEdge, layer := .L2_BytesAndLayout, expectedTier := .ExactUnconditional, maxOpenBugs := 0 }
  , { annealVersion := .V2026_06_01, minirustSnapshot := .S2026_07_BleedingEdge, layer := .L3_PlacesAndBasicMem, expectedTier := .ExactUnconditional, maxOpenBugs := 0 }
  , { annealVersion := .V2026_06_01, minirustSnapshot := .S2026_07_BleedingEdge, layer := .L4_TreeBorrows, expectedTier := .EpochDeltaOnly, maxOpenBugs := 0 }
  , { annealVersion := .V2026_06_01, minirustSnapshot := .S2026_07_BleedingEdge, layer := .L5_ControlAndCalls, expectedTier := .ExactUnconditional, maxOpenBugs := 0 }
  , { annealVersion := .V2026_06_01, minirustSnapshot := .S2026_07_BleedingEdge, layer := .L6_WholeMachine, expectedTier := .EpochDeltaOnly, maxOpenBugs := 0 }
  ]

/--
Certifies that `V2026_06_01` × `S2026_05_Matched` has `0` open bug gaps, `4` closed
remediated bug gaps, and `maxOpenBugs = 0` across every scorecard cell.
-/
theorem scorecard_matched_open_bugs_ratchet :
    activeBugGaps .V2026_06_01 .S2026_05_Matched = [] ∧
    (activeBugGaps .V2026_06_01 .S2026_05_Matched).length = 0 ∧
    closedBugGaps .V2026_06_01 .S2026_05_Matched =
      [.GAP_MR_0001, .GAP_MR_0002, .GAP_MR_0003, .GAP_MR_0004] ∧
    (closedBugGaps .V2026_06_01 .S2026_05_Matched).length = 4 ∧
    (v2026_06_01_scorecard.all (fun c => c.maxOpenBugs == 0)) = true := by
  decide

/--
Certifies that `V2026_06_01` × `S2026_07_BleedingEdge` has `0` open bug gaps and
differs from `S2026_05_Matched` solely by `GAP_EPOCH_0001`.
-/
theorem scorecard_bleeding_edge_epoch_delta :
    activeBugGaps .V2026_06_01 .S2026_07_BleedingEdge = [] ∧
    activeEpochDivergences .V2026_06_01 .S2026_05_Matched = [] ∧
    activeEpochDivergences .V2026_06_01 .S2026_07_BleedingEdge = [.GAP_EPOCH_0001] := by
  decide

/--
Certifies that all 6 layers (`L1_Scalars`..`L6_WholeMachine`) of `V2026_06_01` × `S2026_05_Matched`
have `expectedTier = .ExactUnconditional` and `maxOpenBugs = 0`.
-/
theorem scorecard_layer_tiers_verified :
    (v2026_06_01_scorecard.filter (fun c => c.minirustSnapshot == .S2026_05_Matched)).length = 6 ∧
    ((v2026_06_01_scorecard.filter (fun c => c.minirustSnapshot == .S2026_05_Matched)).all
      (fun c => c.expectedTier == .ExactUnconditional && c.maxOpenBugs == 0)) = true := by
  decide

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
  l5_control_and_calls_corresponds :=
    ⟨mir_advanceStmt_corresponds,
     mir_lookupSwitchTarget_corresponds,
     mir_evalTerminator_goto_corresponds,
     mir_evalTerminator_unreachable_is_ub,
     evalTerminator_switchInt_agrees_with_generated⟩
  l6_whole_machine_simulation_and_refinement :=
    ⟨mir_stepMirState_simulation,
     mir_whole_machine_guarded_refines⟩
  epoch_matrix_separation := matched_snapshot_has_zero_epoch_divergences

/--
**Complete `V2026_06_01` Correspondence Certificate (`v2026_06_01_correspondence_certificate`)**:
Combines `CorrespondenceScorecard`, unconditional `S2026_05_Matched` fixture equivalence,
all 4 closed remediation witnesses (`GAP-MR-0001`..`GAP-MR-0004`), `0` open bug ratchet,
and `ExactUnconditional` tier verification across all 6 layers (`L1`–`L6`).
-/
theorem v2026_06_01_correspondence_certificate :
    CorrespondenceScorecard ∧
    (∀ prog : FixtureProg,
      evalAnnealV2026_06_01 prog defaultFixtureState =
        evalMiniRustSnapshot .S2026_05_Matched prog) ∧
    activeBugGaps .V2026_06_01 .S2026_05_Matched = [] ∧
    (closedBugGaps .V2026_06_01 .S2026_05_Matched).length = 4 ∧
    ((v2026_06_01_scorecard.filter (fun c => c.minirustSnapshot == .S2026_05_Matched)).all
      (fun c => c.expectedTier == .ExactUnconditional && c.maxOpenBugs == 0)) = true :=
  ⟨all_correspondence_slices_verified,
   all_matched_fixtures_agree_unconditionally,
   scorecard_matched_open_bugs_ratchet.1,
   scorecard_matched_open_bugs_ratchet.2.2.2.1,
   scorecard_layer_tiers_verified.2⟩

end Correspondence.V2026_06_01.Scorecard
