import Trusted
import Anneal
import Anneal.MirSpecLift
import Mir.WireframeDemo.clamp_payload_window
import Obligations.WireframeDemo.clamp_payload_window

namespace Proof.WireframeDemo.clamp_payload_window

set_option linter.all false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

open Anneal.PureMirExec

#mir_lift_spec clamp_req Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body [.scalar { bits := b1, sizeBytes := 2 }, .scalar { bits := b2, sizeBytes := 2 }]

private theorem wpReq_inversion (v1 v2 : Value) :
    MirBoolPredicateHolds Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body [v1, v2] →
    ∃ b1 b2 : Nat,
      v1 = .scalar { bits := b1, sizeBytes := 2 } ∧
      v2 = .scalar { bits := b2, sizeBytes := 2 } ∧
      b1 ≤ 65535 ∧ b2 ≤ 1024 := by
  intro h_holds
  rcases v1 with _ | ⟨v1, _ | ⟨_, _ | _⟩⟩
  · exact False.elim (by revert h_holds; decide)
  · exact False.elim (by revert h_holds; decide)
  · exact False.elim (by revert h_holds; decide)
  rcases v2 with _ | ⟨v2, _ | ⟨_, _ | _⟩⟩
  · exact False.elim (by revert h_holds; decide)
  · exact False.elim (by revert h_holds; decide)
  · exact False.elim (by revert h_holds; decide)
  refine ⟨v1.bits, v2.bits, rfl, rfl, ?_, ?_⟩
  · revert h_holds
    exact (by decide)
  · revert h_holds
    exact (by decide)

theorem verified : VerificationResult Obligations.WireframeDemo.clamp_payload_window.claim := by
  apply verifyMirNoPanic_of_pureExec
  · rfl
  · intro args h_pre
    rcases h_pre with ⟨h_args, h_req⟩
    rcases args with ⟨_ | ⟨v1, _ | ⟨v2, _ | _⟩⟩⟩
    · exact False.elim (by revert h_args; decide)
    · exact False.elim (by revert h_args; decide)
    · exact False.elim (by revert h_args; decide)
    · rcases wpReq_inversion v1 v2 h_req with ⟨b1, b2, rfl, rfl, h_b1, h_b2⟩
      exact ⟨_, by
        dsimp only [PureMirConverges, wpPureMirExec, wpPureMirSteps, wpMirStepsSym]
        dsimp only [Mir.WireframeDemo.clamp_payload_window.body,
          wpBlockLinear, wpBlockStep, evalSymNodeTree,
          evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
          evalRvalueSymTreeFast,
          evalOperandFast, evalOperandsFast, evalConstValue,
          evalScalarBinOpSymTree, bitwiseAndBitsFast, evalUnaryNotSymTree, operandIsSigned, operandTy, sharedBorrowPerm, rigidTyIsFreeze, stringEq, tyIsFreeze, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
          evalTerminatorSymTreeFast,
          lookupSwitchTargetTree, applyUnwindAction,
          MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
          initMachineState, initLocals, initLocalsAux, emptyMemory,
          readProjectedValue_nil, readProjectedValue_field,
          invalidateConflictingBorrows, mirNormalPost, boolToScalar,
          Mir.WireframeDemo.clamp_payload_window.layouts,
          sharedBorrowPerm, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsFreeze, rigidTyIsFreeze, stringEq,
          Obligations.WireframeDemo.clamp_payload_window.claim,
          Obligations.WireframeDemo.clamp_payload_window.refineSafeSpec,
          Obligations.WireframeDemo.clamp_payload_window.rustEnsures,
          Obligations.WireframeDemo.clamp_payload_window.defaultPost,
          ItemSpec.post,
          GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
          HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
          List.replicate, List.append, List.length, List.set, List.map, Option.getD,
          get?, set?, length, Nat.add, Nat.mul, Nat.beq, Bool.and, Bool.or,
          bitwiseAndBits_one_one, bitwiseAndBits_one_zero,
          ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
          Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
        split
        · exact ⟨fun _ => rfl, by rfl⟩
        · exact ⟨fun _ => rfl, by rfl⟩⟩
