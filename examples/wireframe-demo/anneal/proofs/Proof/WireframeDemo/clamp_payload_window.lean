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
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.FunctionalTranslation

private theorem nat_beq_eq_false_of_ne {a b : Nat} (h : a ≠ b) :
    Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem ensures_holds (b1 b2 ret : Nat)
    (h_ret : (b1 ≤ b2 ∧ ret = b1) ∨ (b2 < b1 ∧ ret = b2)) :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body
      [.scalar { bits := b1, sizeBytes := 2 },
       .scalar { bits := b2, sizeBytes := 2 },
       .scalar { bits := ret, sizeBytes := 2 }] := by
  apply Hold.val
  refine hold_mirBool_of_blockLinear _ _ rfl rfl ?_
  rcases h_ret with ⟨h_le, rfl⟩ | ⟨h_gt, rfl⟩
  all_goals
    repeat (first
      | dsimp only [
        Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.layouts,
        Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body,
        defaultSpecSteps, entryBB, dummyBB, lookupBlock,
        wpBlockLinear, wpCfgStep, dispatchBlock,
        evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree,
        finishAssignStmtNode, advanceStmt, evalRvalueSymTreeFast, validateLoadedValue, evalOperandFast,
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
      | simp (disch := omega) only [nat_ble_eq_true_of_le, Nat.beq_refl,
        nat_beq_eq_false_of_ne])
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
  -- Each round unfolds the companion further, then refutes a branch or splits
  -- `v1` / `v2` on its shape and bound.
  repeat (
    dsimp only [
      Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.layouts,
      Mir.WireframeDemo.__anodized_fn_requires_clamp_payload_window.body,
      defaultSpecSteps, entryBB, dummyBB, lookupBlock,
      wpBlockLinear, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
      stepMirSymTreeFast, evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree,
      finishAssignStmtNode, advanceStmt, evalRvalueSymTreeFast, validateLoadedValue, evalOperandFast,
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
    first
    | (rintro ⟨h_val⟩; injection h_val with h_sc; injection h_sc with h_bits _; nomatch h_bits)
    | (rcases v1 with _ | ⟨b1, _ | _ | _ | sz1⟩ | _ | _ <;>
        (dsimp only [finishAssignSymTree, evalSymNodeTree, Nat.beq]; try rintro ⟨⟨⟩⟩);
       cases h_ble1 : Nat.ble b1 65535)
    | (rcases v2 with _ | ⟨b2, _ | _ | _ | sz2⟩ | _ | _ <;>
        (dsimp only [finishAssignSymTree, evalSymNodeTree, Nat.beq]; try rintro ⟨⟨⟩⟩);
       cases h_ble2 : Nat.ble b2 1024;
       case true =>
         intro _
         exact ⟨b1, b2, rfl, rfl,
           Nat.le_of_ble_eq_true h_ble1, Nat.le_of_ble_eq_true h_ble2⟩))

/-- Universal verification certificate for `clamp_payload_window` across all
`requested : u16` and `max_window ≤ 1024`.

The body is call-free and alias-free (`checkPureMir`), so it is lifted with the
`#mir_lift` rules applied explicitly; the `switchInt` on `requested <=
max_window` is resolved by a case split, and the step budget is synthesized
structurally by the rules (no fuel constant appears in this proof). -/
theorem verified : VerificationResult Obligations.WireframeDemo.clamp_payload_window.claim := by
  refine verifyMirNoPanic_of_pureExec _ rfl fun args h_pre => ?_
  rcases h_pre with ⟨h_len, h_req⟩
  obtain ⟨v1, v2, rfl⟩ : ∃ v1 v2, args = [v1, v2] := by
    rcases args with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
    all_goals first | exact ⟨_, _, rfl⟩ | nomatch h_len
  obtain ⟨b1, b2, rfl, rfl, -, -⟩ := wpReq_inversion v1 v2 h_req
  -- bb0: `_3 = Le(_1, _2); switchInt(_3) -> [0: bb2, otherwise: bb1]`
  apply lift_PureMirConverges (by rfl)
  apply LiftBlock.of_lookup (by rfl)
  repeat apply LiftStmtsTerminator.cons_eval (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  by_cases h : b1 ≤ b2
  · -- `requested <= max_window`: bb1 `_0 = copy _1; goto bb3`; bb3 `return`.
    apply LiftStmtsTerminator.term_switchInt (target := 1) (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    · change 1 = lookupSwitchTarget (boolToScalar (Nat.ble b1 b2)).bits [(0, 2)] 1
      rw [Nat.ble_eq_true_of_le h]
      rfl
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.cons_eval (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    exact ensures_holds b1 b2 b1 (Or.inl ⟨h, rfl⟩)
  · -- `requested > max_window`: bb2 `_0 = copy _2; goto bb3`; bb3 `return`.
    apply LiftStmtsTerminator.term_switchInt (target := 2) (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    · change 2 = lookupSwitchTarget (boolToScalar (Nat.ble b1 b2)).bits [(0, 2)] 1
      rw [Anneal.FunctionalTranslation.nat_ble_eq_false_of_lt (Nat.lt_of_not_le h)]
      rfl
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.cons_eval (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    exact ensures_holds b1 b2 b2 (Or.inr ⟨Nat.lt_of_not_le h, rfl⟩)

/-- Non-vacuity witness confirming `clamp_payload_window`'s `requires` contract
is satisfiable (`requested = 512`, `max_window = 1024`). -/
theorem nonVacuousRequires :
    ∃ a : List Value,
      Obligations.WireframeDemo.clamp_payload_window.rustRequires a := by
  refine ⟨[.scalar { bits := 512, sizeBytes := 2 }, .scalar { bits := 1024, sizeBytes := 2 }],
    ⟨rfl, ?_⟩⟩
  exact mirBoolPredicateHolds_of_evalMirSpecBool_true _ _ rfl rfl

end Proof.WireframeDemo.clamp_payload_window
