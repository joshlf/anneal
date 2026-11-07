import Trusted
import Anneal
import Mir.WireframeDemo.clamp_payload_window
import Obligations.WireframeDemo.clamp_payload_window

namespace Proof.WireframeDemo.clamp_payload_window

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
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

private theorem ensures_holds (b1 b2 ret : Nat)
    (h_ret : (b1 ≤ b2 ∧ ret = b1) ∨ (b2 < b1 ∧ ret = b2)) :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body
      [.scalar { bits := b1, sizeBytes := 2 },
       .scalar { bits := b2, sizeBytes := 2 },
       .scalar { bits := ret, sizeBytes := 2 }] := by
  apply Hold.val
  refine hold_mirBool_of_blockLinear _ _ rfl rfl ?_
  rcases h_ret with ⟨h_le, h_ret_eq⟩ | ⟨h_gt, h_ret_eq⟩
  · rw [h_ret_eq]
    have h1 : Nat.ble b1 b2 = true := Nat.ble_eq_true_of_le h_le
    have h2 : Nat.ble b1 b1 = true := Nat.ble_eq_true_of_le (Nat.le_refl b1)
    have h3 : Nat.beq b1 b1 = true := Nat.beq_refl b1
    iterate 3 (
      dsimp only [
        Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.layouts,
        Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body,
        defaultSpecSteps, entryBB, dummyBB, lookupBlock,
        wpBlockLinear, wpCfgStep, dispatchBlock,
        evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree,
        finishAssignStmtNode, advanceStmt, evalRvalueSymTreeFast, evalOperandFast,
        evalOperandsFast, evalConstValue, evalScalarBinOpSymTree, bitwiseAndBitsFast,
        mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree, operandIsSigned, operandTy,
        sharedBorrowPerm, rigidTyIsFreeze, stringEq, tyIsFreeze, placeTy,
        resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
        scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
        mul_1_8, mul_2_8, mul_4_8, mul_8_8,
        evalTerminatorSymTreeFast, lookupSwitchTargetTree, applyUnwindAction,
        MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
        initMachineState, initLocals, initLocalsAux, emptyMemory,
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
        get?, set?, length, Nat.add, Nat.mul, Nat.beq, Bool.and, Bool.or, Bool.not,
        ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
        Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
      first | rw [h1] | rw [h2] | rw [h3])
    dsimp only [wpBlockLinear, wpCfgStep, dispatchBlock,
      evalSymNodeTree, evalTerminatorSymTreeFast,
      MirStepNode.retNormal, SymTree.bind, readProjectedValue_nil,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, get?]
    exact ⟨boolTruePost_normal_one _⟩
  · rw [h_ret_eq]
    have h1 : Nat.ble b2 b2 = true := Nat.ble_eq_true_of_le (Nat.le_refl b2)
    have h2 : Nat.ble b2 b1 = true := Nat.ble_eq_true_of_le (Nat.le_of_lt h_gt)
    have h3 : Nat.beq b2 b1 = false := by
      cases h : Nat.beq b2 b1
      · rfl
      · have := Nat.eq_of_beq_eq_true h; omega
    have h4 : Nat.beq b2 b2 = true := Nat.beq_refl b2
    iterate 4 (
      dsimp only [
        Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.layouts,
        Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body,
        defaultSpecSteps, entryBB, dummyBB, lookupBlock,
        wpBlockLinear, wpCfgStep, dispatchBlock,
        evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree,
        finishAssignStmtNode, advanceStmt, evalRvalueSymTreeFast, evalOperandFast,
        evalOperandsFast, evalConstValue, evalScalarBinOpSymTree, bitwiseAndBitsFast,
        mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree, operandIsSigned, operandTy,
        sharedBorrowPerm, rigidTyIsFreeze, stringEq, tyIsFreeze, placeTy,
        resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
        scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
        mul_1_8, mul_2_8, mul_4_8, mul_8_8,
        evalTerminatorSymTreeFast, lookupSwitchTargetTree, applyUnwindAction,
        MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
        initMachineState, initLocals, initLocalsAux, emptyMemory,
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
        get?, set?, length, Nat.add, Nat.mul, Nat.beq, Bool.and, Bool.or, Bool.not,
        ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
        Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
      first | rw [h1] | rw [h2] | rw [h3] | rw [h4])
    dsimp only [wpBlockLinear, wpCfgStep, dispatchBlock,
      evalSymNodeTree, evalTerminatorSymTreeFast,
      MirStepNode.retNormal, SymTree.bind, readProjectedValue_nil,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal, get?]
    exact ⟨boolTruePost_normal_one _⟩

private theorem wpReq_inversion (v1 v2 : Value)
    (h_req : MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body [v1, v2]) :
    ∃ b1 b2 : Nat,
      v1 = .scalar { bits := b1, sizeBytes := 2 } ∧
      v2 = .scalar { bits := b2, sizeBytes := 2 } ∧
      b1 ≤ 65535 ∧ b2 ≤ 1024 := by
  have h_hold :=
    holdBoolReq_of_mirBool
      Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body
      [v1, v2] rfl rfl h_req
  revert h_hold
  dsimp only [
    Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.layouts,
    Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body,
    defaultSpecSteps, entryBB, dummyBB, lookupBlock,
    wpBlockLinear, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
    stepMirSymTreeFast, evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree,
    finishAssignStmtNode, advanceStmt, evalRvalueSymTreeFast, evalOperandFast,
    evalOperandsFast, evalConstValue, evalScalarBinOpSymTree, bitwiseAndBitsFast,
    mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree, operandIsSigned, operandTy,
    sharedBorrowPerm, rigidTyIsFreeze, stringEq, tyIsFreeze, placeTy,
    resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
    scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
    mul_1_8, mul_2_8, mul_4_8, mul_8_8,
    evalTerminatorSymTreeFast, lookupSwitchTargetTree, applyUnwindAction,
    MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
    initMachineState, initLocals, initLocalsAux, emptyMemory, mirSafePost,
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
  rcases v1 with _ | ⟨b1, sz1⟩ | ⟨p1, psz1⟩ | ⟨vid1, flds1⟩
  · intro h; exact False.elim h.val
  · dsimp only [finishAssignSymTree, evalSymNodeTree]
    cases h_sz1_0 : Nat.beq sz1 0 with
    | true => intro h; exact False.elim h.val
    | false =>
      cases h_sz1_2 : Nat.beq sz1 2 with
      | false => intro h; exact False.elim h.val
      | true =>
        cases h_ble1 : Nat.ble b1 65535 <;>
          dsimp only [
            Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.layouts,
            Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body,
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
                    Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.layouts,
                    Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body,
                    lookupBlock, wpBlockLinear, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
                    stepMirSymTreeFast, evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree,
                    finishAssignStmtNode, advanceStmt, evalRvalueSymTreeFast, evalOperandFast,
                    evalOperandsFast, evalConstValue, evalScalarBinOpSymTree, bitwiseAndBitsFast,
                    mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree,
                    scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
                    mul_1_8, mul_2_8, mul_4_8, mul_8_8,
                    evalTerminatorSymTreeFast, lookupSwitchTargetTree, applyUnwindAction,
                    MirStepNode.step, MirStepNode.retNormal, SymTree.bind, mirSafePost,
                    readProjectedValue_nil, readProjectedValue_field, ProvenancePtr.tag,
                    lookupBorrow, appendProjections, stripTransparentProjections,
                    projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
                    byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
                    isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
                    invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
                    freezeDerefReadBorrowsAt, freezeTreeBorrowsOnReadAtProj,
                    updateBorrowPermOnReadAtProj, isBorrowDescendantOrSelf,
                    isBorrowDescendantOrSelfAux, sharedBorrowPerm, placeTy, resolveProjectedTy,
                    pointeeTyOf, elemTyOf, tyIsFreeze, rigidTyIsFreeze, stringEq, boolToScalar,
                    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
                    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
                    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
                    get?, set?, length, Nat.add, Nat.mul, Nat.ble, Nat.beq, Bool.and, Bool.or,
                    Bool.not, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq,
                    instDecidableEqNat, Bool.decEq, instDecidableEqBool, BEq.beq,
                    instBEqOfDecidableEq]
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

/-- Universal verification certificate for `clamp_payload_window` across all
`requested : u16` and `max_window ≤ 1024`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.clamp_payload_window.claim := by
  refine verifyMirNoPanic_of_blockLinear _ rfl rfl rfl ?_
  intro args h_pre
  rcases h_pre with ⟨h_len, h_req⟩
  rcases args with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · nomatch h_len
  · nomatch h_len
  · rcases wpReq_inversion v1 v2 h_req with ⟨b1, b2, hv1, hv2, _hb1, _hb2⟩
    subst hv1; subst hv2
    dsimp only [
      Obligations.WireframeDemo.clamp_payload_window.claim,
      Obligations.WireframeDemo.clamp_payload_window.defaultSpec,
      Obligations.WireframeDemo.clamp_payload_window.defaultPost,
      ItemSpec.post,
      Mir.WireframeDemo.clamp_payload_window.layouts,
      Mir.WireframeDemo.clamp_payload_window.body,
      defaultSpecSteps, entryBB, dummyBB, lookupBlock,
      wpBlockLinear, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
      stepMirSymTreeFast, evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree,
      finishAssignStmtNode, advanceStmt, evalRvalueSymTreeFast, evalOperandFast,
      evalOperandsFast, evalConstValue, evalScalarBinOpSymTree, bitwiseAndBitsFast,
      mod_1_2, bitwiseAndBits_8_1_0, evalUnaryNotSymTree, operandIsSigned, operandTy,
      sharedBorrowPerm, rigidTyIsFreeze, stringEq, tyIsFreeze, placeTy,
      resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
      scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
      mul_1_8, mul_2_8, mul_4_8, mul_8_8,
      evalTerminatorSymTreeFast, lookupSwitchTargetTree, applyUnwindAction,
      MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
      initMachineState, initLocals, initLocalsAux, emptyMemory, mirNormalPost,
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
    cases h_ble : Nat.ble b1 b2 with
    | true =>
      exact ⟨ensures_holds b1 b2 b1 (Or.inl ⟨Nat.le_of_ble_eq_true h_ble, rfl⟩)⟩
    | false =>
      have h_gt : b2 < b1 := by
        have hnot : ¬ b1 ≤ b2 := fun hle => by
          rw [Nat.ble_eq_true_of_le hle] at h_ble
          nomatch h_ble
        omega
      exact ⟨ensures_holds b1 b2 b2 (Or.inr ⟨h_gt, rfl⟩)⟩
  · nomatch h_len

/-- Non-vacuity witness confirming `clamp_payload_window`'s `requires` contract
is satisfiable (`requested = 512`, `max_window = 1024`). -/
theorem nonVacuousRequires :
    ∃ a : List Value,
      Obligations.WireframeDemo.clamp_payload_window.rustRequires a := by
  refine ⟨[.scalar { bits := 512, sizeBytes := 2 }, .scalar { bits := 1024, sizeBytes := 2 }],
    ⟨rfl, ?_⟩⟩
  exact mirBoolPredicateHolds_of_evalMirSpecBool_true _ _ rfl rfl

end Proof.WireframeDemo.clamp_payload_window
