import Trusted
import Anneal
import Mir.WireframeDemo.parse_compression_flag
import Specs.WireframeDemo.parse_compression_flag
import Obligations.WireframeDemo.parse_compression_flag

namespace Proof.WireframeDemo.parse_compression_flag

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
open Specs.WireframeDemo.parse_compression_flag

theorem verified : VerificationResult Obligations.WireframeDemo.parse_compression_flag.claim := by
  apply verifyMirNoPanic_of_pureExec
  · rfl
  · intro args h_pre
    rcases h_pre with ⟨b, hb, rfl⟩
    exact ⟨_, by
      dsimp only [PureMirConverges, wpPureMirExec, wpPureMirSteps, wpMirStepsSym]
      dsimp only [Mir.WireframeDemo.parse_compression_flag.body,
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
        Mir.WireframeDemo.parse_compression_flag.layouts,
        sharedBorrowPerm, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsFreeze, rigidTyIsFreeze, stringEq,
        Obligations.WireframeDemo.parse_compression_flag.claim,
        Obligations.WireframeDemo.parse_compression_flag.refineSafeSpec,
        Obligations.WireframeDemo.parse_compression_flag.rustEnsures,
        Obligations.WireframeDemo.parse_compression_flag.defaultPost,
        ItemSpec.post,
        GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
        HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
        List.replicate, List.append, List.length, List.set, List.map, Option.getD,
        get?, set?, length, Nat.add, Nat.mul, Nat.beq, Bool.and, Bool.or,
        bitwiseAndBits_one_one, bitwiseAndBits_one_zero,
        ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
        Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
      split
      · sorry
      · sorry⟩

end Proof.WireframeDemo.parse_compression_flag
