import Trusted
import Anneal
import Mir.WireframeDemo.advance_cursor
import Specs.WireframeDemo.advance_cursor
import Obligations.WireframeDemo.advance_cursor

namespace Proof.WireframeDemo.advance_cursor

set_option linter.all false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.ITreeWP
open Anneal.PureMirExec
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.WireframeDemo.advance_cursor

/-- Stateful verification certificate for `wireframe_demo::advance_cursor`. -/
theorem verified :
    StatefulVerificationResult Obligations.WireframeDemo.advance_cursor.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_cfg _ rfl rfl ?_
  intro args mem h_pre
  cases mem with
  | mk nextAllocId globals borrows nextTag callees traitImpls callStack activeCallee
      activeProtectors nextProtector callerLocals fnPtrs =>
    rcases h_pre with
      ⟨_, offset, limit, step, h_inv, h_lim, h_step, h_args,
       h_callee, h_stack, h_prot, h_borrows, h_caller⟩
    dsimp only at h_callee h_stack h_prot h_borrows h_caller
    rw [h_args, h_callee, h_stack, h_prot, h_borrows, h_caller]
    refine ⟨?_⟩
    dsimp only [
      Obligations.WireframeDemo.advance_cursor.statefulClaim,
      Obligations.WireframeDemo.advance_cursor.refineStatefulSpec,
      Mir.WireframeDemo.advance_cursor.body,
      Mir.WireframeDemo.advance_cursor.layouts,
      cursorCallerLocals, cursorSlotIdx, cursorValue, activeCursorBorrow, rootCursorPtr,
      defaultSpecSteps, entryBB, dummyBB, lookupBlock, wpCfgStep, dispatchBlock,
      evalSymNodeTree,
      evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTreeFast, evalRvalueFallback, evalRvalue, evalRvalueWithMemory,
      evalOperandFast, evalOperandFallback, evalOperand, evalOperandsFast, evalConstValue,
      evalScalarBinOpSymTree, evalUnaryNotSymTree, evalUnaryNot,
      evalTerminatorSymTreeFast, evalTerminatorFallback, evalTerminatorSymTree, evalTerminator,
      lookupSwitchTargetTree, lookupSwitchTarget, applyUnwindAction,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux,
      readProjectedValue, evalPlaceWrite, evalCallerPlaceWrite,
      writePlaceValue, writeProjectedValue, invalidateDerefWriteBorrows,
      operandIsSigned, operandTy, sharedBorrowPerm, rigidTyIsFreeze, stringEq,
      tyIsFreeze, placeTy, placeIsSigned, resolveProjectedTy,
      tyIsSigned, pointeeTyOf, elemTyOf, intCastTargetBytes, ProvenancePtr.tag,
      lookupBorrow, appendProjections, stripTransparentProjections,
      projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
      byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
      isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
      invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
      mirNormalPost,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.mul, Nat.beq, Bool.and, Bool.or,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    have h_ble_inv : Nat.ble offset limit = true := Nat.ble_eq_true_of_le h_inv
    have h_sub_wrap : wrapScalarBits (Nat.sub limit offset) (scalarModulus 2) = limit - offset :=
      wrapScalarBits_eq_of_lt (by change limit - offset < 65536; omega)
    rw [h_ble_inv, h_sub_wrap]
    cases h_le_b : Nat.ble step (limit - offset)
    · dsimp only [
        StatefulItemSpec.post,
        Obligations.WireframeDemo.advance_cursor.statefulClaim,
        Obligations.WireframeDemo.advance_cursor.refineStatefulSpec,
        Obligations.WireframeDemo.advance_cursor.rustEnsures,
        Obligations.WireframeDemo.advance_cursor.defaultPost,
        cursorStatefulPost]
      refine ⟨trivial, ?_⟩
      intro offset' limit' step' _ _ _ h_args_eq h_caller_eq
      injection h_args_eq with _ h_a1
      injection h_a1 with h_s1 _
      injection h_s1 with h_sc1
      injection h_sc1 with h_step_eq _
      have h_slot := congrArg (fun xs => get? xs cursorSlotIdx) h_caller_eq
      dsimp only [cursorCallerLocals, cursorSlotIdx, cursorValue, get?,
        HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
        List.replicate, List.append] at h_slot
      injection h_slot with h_init
      injection h_init with h_agg
      injection h_agg with _ h_fields
      injection h_fields with h_f0 h_f1
      injection h_f1 with h_f1_hd _
      injection h_f0 with h_off_sc
      injection h_off_sc with h_off_eq _
      injection h_f1_hd with h_lim_sc
      injection h_lim_sc with h_lim_eq _
      subst h_step_eq h_off_eq h_lim_eq
      have h_nle : ¬ (step ≤ limit - offset) := by
        intro h_c
        have h_bt : Nat.ble step (limit - offset) = true := Nat.ble_eq_true_of_le h_c
        rw [h_le_b] at h_bt
        contradiction
      simp only [h_nle, ↓reduceIte]
      exact ⟨h_inv, trivial, rfl⟩
    · have h_le : step ≤ limit - offset := Nat.le_of_ble_eq_true h_le_b
      have h_no_ovf : Nat.ble (scalarModulus 2) (Nat.add offset step) = false := by
        cases h_ovf : Nat.ble (scalarModulus 2) (Nat.add offset step)
        · rfl
        · have : 65536 ≤ offset + step := Nat.le_of_ble_eq_true h_ovf
          omega
      dsimp only
      rw [h_no_ovf]
      dsimp only [
        StatefulItemSpec.post,
        Obligations.WireframeDemo.advance_cursor.statefulClaim,
        Obligations.WireframeDemo.advance_cursor.refineStatefulSpec,
        Obligations.WireframeDemo.advance_cursor.rustEnsures,
        Obligations.WireframeDemo.advance_cursor.defaultPost,
        cursorStatefulPost]
      refine ⟨trivial, ?_⟩
      intro offset' limit' step' _ _ _ h_args_eq h_caller_eq
      injection h_args_eq with _ h_a1
      injection h_a1 with h_s1 _
      injection h_s1 with h_sc1
      injection h_sc1 with h_step_eq _
      have h_slot := congrArg (fun xs => get? xs cursorSlotIdx) h_caller_eq
      dsimp only [cursorCallerLocals, cursorSlotIdx, cursorValue, get?,
        HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
        List.replicate, List.append] at h_slot
      injection h_slot with h_init
      injection h_init with h_agg
      injection h_agg with _ h_fields
      injection h_fields with h_f0 h_f1
      injection h_f1 with h_f1_hd _
      injection h_f0 with h_off_sc
      injection h_off_sc with h_off_eq _
      injection h_f1_hd with h_lim_sc
      injection h_lim_sc with h_lim_eq _
      subst h_step_eq h_off_eq h_lim_eq
      have h_w : wrapScalarBits (Nat.add offset step) (scalarModulus 2) = offset + step :=
        wrapScalarBits_eq_of_lt (by change offset + step < 65536; omega)
      simp only [h_le, ↓reduceIte, h_w]
      exact ⟨by omega, trivial, rfl⟩

end Proof.WireframeDemo.advance_cursor
