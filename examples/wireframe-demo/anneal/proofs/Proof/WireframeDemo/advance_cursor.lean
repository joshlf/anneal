import Trusted
import Anneal
import Mir.WireframeDemo.advance_cursor
import Specs.WireframeDemo.advance_cursor
import Obligations.WireframeDemo.advance_cursor

namespace Proof.WireframeDemo.advance_cursor

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.ITreeWP
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.FunctionalTranslation
open Specs.WireframeDemo.advance_cursor

/-!
Kernel-checked stateful `&mut FrameCursor` proof for
`wireframe_demo::advance_cursor` (Journey 1, `#109`).

Uses `Anneal.FunctionalTranslation` (`TransPlan`, `ValueCodec`, `MutLens`, and
`MutUpdate`) to verify `advance_cursor` across all valid `FrameCursor` states
(`offset <= limit < 65536`) and `step < 65536`, proving both functional
correctness and preservation of `FrameCursor`'s `offset <= limit` invariant.
-/

/-- Pure `ValueCodec` for `FrameCursor { offset: u16, limit: u16 }`. -/
def frameCursorCodec : ValueCodec (Nat × Nat) :=
  ValueCodec.pair (ValueCodec.scalarNat 2) (ValueCodec.scalarNat 2)

/-- Pure functional `MutUpdate` model of `advance_cursor(&mut FrameCursor, step)`. -/
def advanceCursorUpdate (step : Nat) : MutUpdate (Nat × Nat) Bool :=
  fun (offset, limit) =>
    if step ≤ limit - offset then
      ((offset + step, limit), true)
    else
      ((offset, limit), false)

/-- Pure invariant preservation theorem for `advanceCursorUpdate`: whenever
`offset <= limit`, the updated cursor satisfies `newOffset <= limit`. -/
theorem advanceCursorUpdate_preserves_invariant
    (offset limit step : Nat) (h_inv : offset ≤ limit) :
    (advanceCursorUpdate step (offset, limit)).1.1 ≤
      (advanceCursorUpdate step (offset, limit)).1.2 := by
  dsimp [advanceCursorUpdate]
  split <;> (dsimp; omega)

/-- Control-flow `TransPlan` for `advance_cursor`: check `limit - offset`,
branch on `step <= remaining` (`bb1`), and execute either the mutation arm
(`bb2 -> bb3 -> bb5`) or the unchanged arm (`bb4 -> bb5`). -/
def advanceCursorPlan : TransPlan :=
  .seq 1 (.splitBranch (.ret 16) (.ret 16) 16) 16

private def wpExecFast (body : CapturedMir) (post : MirOutcome → Prop) :
    Nat → MirExecState → Prop
  | 0, _ => False
  | fuel' + 1, .running s =>
    evalSymNodeTree (wpExecFast body post fuel') post (stepMirSymTree body s)
  | _ + 1, .halted out => post out
  | _ + 1, .faulted _ => False

private theorem wpExecFast_eq
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) (post : MirOutcome → Prop) :
    wpMirExecSym fuel body st post = wpExecFast body post fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    have h_fn : (fun st' => wpMirExecSym fuel' body st' post) = wpExecFast body post fuel' :=
      funext (fun st' => ih st')
    cases st with
    | running s =>
      dsimp only [wpMirExecSym, stepMirExecSymTree, wpExecFast]
      rw [h_fn]
    | halted out =>
      dsimp only [wpMirExecSym, stepMirExecSymTree, evalSymNodeTree, wpExecFast]
    | faulted fk =>
      cases fk <;>
        dsimp only [wpMirExecSym, stepMirExecSymTree, evalSymNodeTree, MirStepNode.fail, wpExecFast]

/-- Stateful verification certificate for `wireframe_demo::advance_cursor`. -/
theorem verified :
    StatefulVerificationResult Obligations.WireframeDemo.advance_cursor.statefulClaim := by
  refine verifyStatefulMirNoPanicSym _ 26 ?_
  intro args mem h_pre
  cases mem with
  | mk nextAllocId globals borrows nextTag callees callStack activeCallee activeProtectors nextProtector callerLocals =>
    rcases h_pre with ⟨_, offset, limit, step, h_inv, h_lim, h_step, h_args, h_callee, h_stack, h_prot, h_borrows, h_caller⟩
    dsimp only at h_callee h_stack h_prot h_borrows h_caller
    rw [h_args, h_callee, h_stack, h_prot, h_borrows, h_caller]
    unfold wpMirSym
    rw [wpExecFast_eq]
    dsimp only [Obligations.WireframeDemo.advance_cursor.statefulClaim,
      Obligations.WireframeDemo.advance_cursor.refineStatefulSpec,
      Mir.WireframeDemo.advance_cursor.body,
      Mir.WireframeDemo.advance_cursor.layouts,
      cursorCallerLocals, cursorSlotIdx, cursorValue, activeCursorBorrow, rootCursorPtr,
      wpExecFast, evalSymNodeTree, stepMirSymTree,
      evalStmtSymTree, evalStmt, finishAssignStmtNode, advanceStmt,
      evalRvalueSymTree, evalRvalue, evalRvalueWithMemory,
      evalOperand, evalOperands, evalConstValue,
      evalScalarBinOpSymTree, evalUnaryNotSymTree, evalUnaryNot,
      evalTerminatorSymTree, evalTerminator,
      lookupSwitchTargetTree, lookupSwitchTarget, applyUnwindAction,
      MirStepNode.step, MirStepNode.retNormal,
      SymTree.bind,
      initMachineStateWithMemory, initMachineState, initLocals, initLocalsAux,
      readProjectedValue, evalPlaceWrite, evalCallerPlaceWrite,
      writePlaceValue, writeProjectedValue, invalidateDerefWriteBorrows,
      operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy,
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
      get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    have h_ble_inv : Nat.ble offset limit = true := Nat.ble_eq_true_of_le h_inv
    have h_sub_wrap : wrapScalarBits (Nat.sub limit offset) (scalarModulus 2) = limit - offset :=
      wrapScalarBits_eq_of_lt (by change limit - offset < 65536; omega)
    rw [h_ble_inv, h_sub_wrap]
    cases h_le_b : Nat.ble step (limit - offset)
    · dsimp only [StatefulItemSpec.post,
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
      dsimp only [evalSymNodeTree, wpExecFast, stepMirSymTree,
        Mir.WireframeDemo.advance_cursor.body, Mir.WireframeDemo.advance_cursor.layouts,
        evalStmtSymTree, evalStmt, finishAssignStmtNode, advanceStmt,
        evalRvalueSymTree, evalRvalue, evalRvalueWithMemory,
        evalOperand, evalOperands, evalConstValue,
        evalScalarBinOpSymTree, evalUnaryNotSymTree, evalUnaryNot,
        evalTerminatorSymTree, evalTerminator,
        lookupSwitchTargetTree, lookupSwitchTarget, applyUnwindAction,
        MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
        readProjectedValue, evalPlaceWrite, evalCallerPlaceWrite,
        writePlaceValue, writeProjectedValue, invalidateDerefWriteBorrows,
        operandIsSigned, operandTy, placeTy, placeIsSigned, resolveProjectedTy,
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
        get?, set?, length, Nat.add, Nat.beq, Bool.and, Bool.or,
        ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
        Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
      dsimp only [StatefulItemSpec.post,
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
