import Trusted
import Anneal
import Mir.WireframeDemo.frame_total_len
import Obligations.WireframeDemo.frame_total_len

namespace Proof.WireframeDemo.frame_total_len

set_option linter.all false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

private theorem ensures_holds (b1 b2 : Nat) (hb1 : b1 ≤ 16) (hb2 : b2 ≤ 1024) :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body
      [.scalar { bits := b1, sizeBytes := 2 },
       .scalar { bits := b2, sizeBytes := 2 },
       .scalar { bits := Nat.add b1 b2, sizeBytes := 2 }] := by
  apply Hold.val
  refine hold_mirBool_of_blockLinear _ _ rfl rfl ?_
  dsimp only [
    Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.layouts,
    Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body,
    defaultSpecSteps, entryBB, dummyBB, lookupBlock,
    wpBlockLinear, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
    stepMirSymTreeFast, evalSymNodeTree,
    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
    evalRvalueSymTreeFast, evalOperandFast, evalOperandsFast, evalConstValue,
    evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0,
    evalUnaryNotSymTree, operandIsSigned, operandTy, sharedBorrowPerm,
    rigidTyIsFreeze, stringEq, tyIsFreeze, placeTy, resolveProjectedTy,
    pointeeTyOf, elemTyOf, tyIsSigned,
    scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
    mul_1_8, mul_2_8, mul_4_8, mul_8_8,
    evalTerminatorSymTreeFast, lookupSwitchTargetTree, applyUnwindAction,
    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
    initMachineState, initLocals, initLocalsAux, emptyMemory,
    readProjectedValue_nil, readProjectedValue_field,
    ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
    projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
    byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
    isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
    invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
    freezeDerefReadBorrowsAt, freezeTreeBorrowsOnReadAtProj, updateBorrowPermOnReadAtProj,
    isBorrowDescendantOrSelf, isBorrowDescendantOrSelfAux,
    boolToScalar,
    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
    get?, set?, length, Nat.add, Nat.mul, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
  have h_ble : Nat.ble 65536 (Nat.add b1 b2) = false := by
    cases h : Nat.ble 65536 (Nat.add b1 b2)
    · rfl
    · have h_le := Nat.le_of_ble_eq_true h
      change 65536 ≤ b1 + b2 at h_le
      omega
  have h_wrap : wrapScalarBits (Nat.add b1 b2) 65536 = Nat.add b1 b2 := by
    unfold wrapScalarBits; rw [h_ble]
  have h_beq : Nat.beq (Nat.add b1 b2) (Nat.add b1 b2) = true :=
    Nat.beq_refl (Nat.add b1 b2)
  rw [h_ble, h_wrap, h_beq]
  exact ⟨boolTruePost_normal_one _⟩

private theorem wpReq_inversion (v1 v2 : Value)
    (h_req : MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body [v1, v2]) :
    ∃ b1 b2 : Nat,
      v1 = .scalar { bits := b1, sizeBytes := 2 } ∧
      v2 = .scalar { bits := b2, sizeBytes := 2 } ∧
      b1 ≤ 16 ∧ b2 ≤ 1024 := by
  have h_hold :=
    holdBoolReq_of_mirBool
      Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body
      [v1, v2] rfl rfl h_req
  revert h_hold
  dsimp only [
    Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.layouts,
    Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body,
    defaultSpecSteps, entryBB, dummyBB, lookupBlock,
    wpBlockLinear, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
    stepMirSymTreeFast, evalSymNodeTree,
    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
    evalRvalueSymTreeFast, evalOperandFast, evalOperandsFast, evalConstValue,
    evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0,
    evalUnaryNotSymTree, operandIsSigned, operandTy, sharedBorrowPerm,
    rigidTyIsFreeze, stringEq, tyIsFreeze, placeTy, resolveProjectedTy,
    pointeeTyOf, elemTyOf, tyIsSigned,
    scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
    mul_1_8, mul_2_8, mul_4_8, mul_8_8,
    evalTerminatorSymTreeFast, lookupSwitchTargetTree, applyUnwindAction,
    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
    initMachineState, initLocals, initLocalsAux, emptyMemory, mirSafePost,
    readProjectedValue_nil, readProjectedValue_field,
    ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
    projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
    byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
    isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
    invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
    freezeDerefReadBorrowsAt, freezeTreeBorrowsOnReadAtProj, updateBorrowPermOnReadAtProj,
    isBorrowDescendantOrSelf, isBorrowDescendantOrSelfAux,
    boolToScalar,
    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
    get?, set?, length, Nat.add, Nat.mul, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
  rcases v1 with _ | ⟨b1, sz1⟩ | ⟨p1, psz1⟩ | ⟨vid1, flds1⟩
  · intro h; exact False.elim h.val
  · dsimp only [finishAssignSymTree, evalSymNodeTree]
    cases h_sz1_0 : Nat.beq sz1 0 with
    | true => intro h; exact False.elim h.val
    | false =>
      cases h_sz1_2 : Nat.beq sz1 2 with
      | false => intro h; exact False.elim h.val
      | true =>
        cases h_ble1 : Nat.ble b1 16 <;>
          dsimp only [
            Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.layouts,
            Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body,
            lookupBlock, wpBlockLinear, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
            stepMirSymTreeFast, evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree,
            finishAssignStmtNode, advanceStmt, evalRvalueSymTreeFast, evalOperandFast,
            evalOperandsFast, evalConstValue, evalScalarBinOpSymTree, bitwiseAndBitsFast,
            mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree, operandIsSigned, operandTy,
            sharedBorrowPerm, rigidTyIsFreeze, stringEq, tyIsFreeze, placeTy,
            resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
            scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
            mul_1_8, mul_2_8, mul_4_8, mul_8_8,
            evalTerminatorSymTreeFast, lookupSwitchTargetTree, applyUnwindAction,
            MirStepNode.step, MirStepNode.retNormal, SymTree.bind, mirSafePost,
            readProjectedValue_nil, readProjectedValue_field, ProvenancePtr.tag, lookupBorrow,
            appendProjections, stripTransparentProjections, projectionsOverlap,
            projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool,
            borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected,
            natListContainsBool, invalidateConflictingBorrows,
            invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
            freezeDerefReadBorrowsAt, freezeTreeBorrowsOnReadAtProj,
            updateBorrowPermOnReadAtProj, isBorrowDescendantOrSelf,
            isBorrowDescendantOrSelfAux, boolToScalar,
            GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
            HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
            List.replicate, List.append, List.length, List.set, List.map, Option.getD,
            get?, set?, length, Nat.add, Nat.mul, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
            ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
            Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
        · rintro ⟨h_val⟩
          injection h_val with h_sc
          injection h_sc with h_bits _
          nomatch h_bits
        · rcases v2 with _ | ⟨b2, sz2⟩ | ⟨p2, psz2⟩ | ⟨vid2, flds2⟩
          · intro h; exact False.elim h.val
          · dsimp only [finishAssignSymTree, evalSymNodeTree]
            cases h_sz2_0 : Nat.beq sz2 0 with
            | true => intro h; exact False.elim h.val
            | false =>
              cases h_sz2_2 : Nat.beq sz2 2 with
              | false => intro h; exact False.elim h.val
              | true =>
                cases h_ble2 : Nat.ble b2 1024 with
                | false =>
                  dsimp only [
                    Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.layouts,
                    Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body,
                    lookupBlock, wpBlockLinear, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
                    stepMirSymTreeFast, evalSymNodeTree,
                    evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
                    evalRvalueSymTreeFast, evalOperandFast, evalOperandsFast, evalConstValue,
                    evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0,
                    evalUnaryNotSymTree, scalarModulus_1, scalarModulus_2, scalarModulus_4,
                    scalarModulus_8, mul_1_8, mul_2_8, mul_4_8, mul_8_8,
                    evalTerminatorSymTreeFast, lookupSwitchTargetTree, applyUnwindAction,
                    MirStepNode.step, MirStepNode.retNormal, SymTree.bind, mirSafePost,
                    readProjectedValue_nil, readProjectedValue_field,
                    ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
                    projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
                    byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
                    isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
                    invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
                    freezeDerefReadBorrowsAt, freezeTreeBorrowsOnReadAtProj, updateBorrowPermOnReadAtProj,
                    isBorrowDescendantOrSelf, isBorrowDescendantOrSelfAux,
                    sharedBorrowPerm, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf,
                    tyIsFreeze, rigidTyIsFreeze, stringEq, boolToScalar,
                    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
                    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
                    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
                    get?, set?, length, Nat.add, Nat.mul, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
                    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
                    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
                  rintro ⟨h_val⟩
                  injection h_val with h_sc
                  injection h_sc with h_bits _
                  nomatch h_bits
                | true =>
                  intro _
                  exact ⟨b1, b2,
                    by rw [Nat.eq_of_beq_eq_true h_sz1_2],
                    by rw [Nat.eq_of_beq_eq_true h_sz2_2],
                    Nat.le_of_ble_eq_true h_ble1,
                    Nat.le_of_ble_eq_true h_ble2⟩
          · intro h; exact False.elim h.val
          · intro h; exact False.elim h.val
  · intro h; exact False.elim h.val
  · intro h; exact False.elim h.val

/-- Universal verification certificate for `frame_total_len` across all valid
header and payload lengths (`header_len ≤ 16`, `payload_len ≤ 1024`).

The body is call-free and alias-free (`checkPureMir`), so it is lifted with the
`#mir_lift` rules applied explicitly (`lift_PureMirConverges`,
`LiftBlock.of_lookup`, `LiftStmtsTerminator.*`), which synthesize the step
budget structurally; no fuel constant appears in this proof. -/
theorem verified : VerificationResult Obligations.WireframeDemo.frame_total_len.claim := by
  refine verifyMirNoPanic_of_pureExec _ rfl fun args h_pre => ?_
  rcases h_pre with ⟨h_len, h_req⟩
  obtain ⟨v1, v2, rfl⟩ : ∃ v1 v2, args = [v1, v2] := by
    rcases args with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
    all_goals first | exact ⟨_, _, rfl⟩ | nomatch h_len
  obtain ⟨b1, b2, rfl, rfl, hb1, hb2⟩ := wpReq_inversion v1 v2 h_req
  -- bb0: `_3 = AddWithOverflow(_1, _2); assert(!_3.1) -> bb1`
  apply lift_PureMirConverges (by rfl)
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.cons_eval (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  · -- The overflow flag is clear: `b1 + b2 ≤ 16 + 1024 < 2^16`.
    change (match Nat.ble 65536 (Nat.add b1 b2) with | true => 1 | false => 0) = 0
    rw [Anneal.FunctionalTranslation.nat_ble_eq_false_of_lt (by change b1 + b2 < 65536; omega)]
  -- bb1: `_0 = move _3.0; return`
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.cons_eval (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  show MirBoolPredicateHolds Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body
    [.scalar ⟨b1, 2⟩, .scalar ⟨b2, 2⟩, .scalar ⟨wrapScalarBits (Nat.add b1 b2) 65536, 2⟩]
  rw [wrapScalarBits_eq_of_lt (by change b1 + b2 < 65536; omega)]
  exact ensures_holds b1 b2 hb1 hb2

/-- Non-vacuity witness confirming `frame_total_len`'s `requires` contract is
satisfiable (`header_len = 4`, `payload_len = 128`). -/
theorem nonVacuousRequires :
    ∃ a : List Value,
      Obligations.WireframeDemo.frame_total_len.rustRequires a := by
  refine ⟨[.scalar { bits := 4, sizeBytes := 2 }, .scalar { bits := 128, sizeBytes := 2 }],
    ⟨rfl, ?_⟩⟩
  exact mirBoolPredicateHolds_of_evalMirSpecBool_true _ _ rfl rfl

end Proof.WireframeDemo.frame_total_len
