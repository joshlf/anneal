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
open Anneal.SepLogicLenses
open Anneal.FunctionalTranslation
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

private theorem ensures_holds (b1 b2 : Nat) (hb1 : b1 ≤ 16) (hb2 : b2 ≤ 1024) :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body
      [.scalar { bits := b1, sizeBytes := 2 },
       .scalar { bits := b2, sizeBytes := 2 },
       .scalar { bits := Nat.add b1 b2, sizeBytes := 2 }] := by
  have h_sum : Nat.add b1 b2 < 65536 := by change b1 + b2 < 65536; omega
  have h_ov : Nat.ble 65536 (Nat.add b1 b2) = false := nat_ble_eq_false_of_lt h_sum
  have h_wrap : wrapScalarBits (Nat.add b1 b2) 65536 = Nat.add b1 b2 :=
    wrapScalarBits_eq_of_lt h_sum
  apply Hold.val
  refine hold_mirBool_of_blockLinear _ _ rfl rfl ?_
  -- `dsimp` steps the companion's CFG (without unfolding untaken `wpExecFallback`
  -- branches); each closure-capture deref read (`evalOperandFallback`) is evaluated
  -- in place by `whnf`, and the overflow / equality branches on `b1 + b2` are
  -- rewritten with `h_ov`, `h_wrap` and `Nat.beq_refl`.
  repeat (first
    | dsimp only [
        Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.layouts,
        Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body, defaultSpecSteps, entryBB,
        dummyBB, lookupBlock, wpBlockLinear, wpCfgStep, dispatchBlock, evalSymNodeTree,
        evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
        evalRvalueSymTreeFast, validateLoadedValue, evalOperandFast, evalOperandsFast,
        derefReadTreeUB, hasTreeReadUB, borrowEntryReadUB, treeBorrowTransitionIsUB,
        placeTouchesUnion, tyProjTouchesUnion, resolveTyWithLocalDecls, isUnresolvedLayoutIdx,
        isUnionLayout, LayoutTable.lookup, evalConstValue, evalScalarBinOpSymTree,
        bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, operandIsSigned, operandTy,
        sharedBorrowPerm, stringEq, tyIsFreeze, placeTy, resolveProjectedTy, pointeeTyOf,
        tyIsSigned, scalarModulus_2, evalTerminatorSymTreeFast, lookupSwitchTargetTree,
        applyUnwindAction, MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
        initMachineState, initLocalsAux, readProjectedValue_nil, readProjectedValue_field,
        ProvenancePtr.tag, lookupBorrow, stripTransparentProjections, projectionsOverlap,
        projectionsOverlapAux, borrowEntryOverlapsWrite, byteRangesOverlapBool,
        borrowEntryWriteConflicts, hasProtectedWriteConflict, isBorrowProtected,
        natListContainsBool, invalidateConflictingBorrows, updateBorrowPerm,
        freezeDerefReadBorrowsAt, freezeTreeBorrowsOnReadAtProj, updateBorrowPermOnReadAtProj,
        isBorrowDescendantOrSelf, isBorrowDescendantOrSelfAux, disableLocalBorrows,
        treeBorrowWriterRelatedness, applyTreeBorrowTransition, treeBorrowNodeAccess,
        treeBorrowPermTransition, treeBorrowProtectorCheck, treeBorrowChildRead,
        treeBorrowForeignRead, treeBorrowForeignWrite, GetElem?.getElem?, List.get?Internal,
        List.length, List.set, Option.getD, get?, set?, length, Nat.add, Nat.mul, Nat.ble,
        Nat.beq, Bool.and, Bool.or, Bool.not, ite, dite, Nat.decLt, Nat.decLe, Bool.decEq,
        instDecidableEqBool]
    | rw [h_ov]
    | rw [h_wrap]
    | rw [Nat.beq_refl]
    | conv in (evalOperandFallback _ _ _ _ _ _ _) => whnf)
  exact ⟨boolTruePost_normal_one _⟩

/-- `requires` inversion for `u16` arguments: the companion returns `true` only
if `header_len ≤ 16` and `payload_len ≤ 1024`. Each comparison is split on its
`Nat.ble` result exactly when the evaluation reaches it (the `dsimp only []`
guard fails unless the split reduces a stuck branch), and every path returning
`false` is refuted. -/
private theorem wpReq_inversion (b1 b2 : Nat)
    (h_req : MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body
      [.scalar { bits := b1, sizeBytes := 2 }, .scalar { bits := b2, sizeBytes := 2 }]) :
    b1 ≤ 16 ∧ b2 ≤ 1024 := by
  have h_hold :=
    holdBoolReq_of_mirBool
      Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body
      [.scalar { bits := b1, sizeBytes := 2 }, .scalar { bits := b2, sizeBytes := 2 }]
      rfl rfl h_req
  revert h_hold
  repeat (first
    | dsimp only [
        Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.layouts,
        Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body, defaultSpecSteps, entryBB,
        dummyBB, lookupBlock, wpBlockLinear, wpCfgStep, dispatchBlock, evalSymNodeTree,
        evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
        evalRvalueSymTreeFast, validateLoadedValue, evalOperandFast, evalOperandsFast,
        derefReadTreeUB, hasTreeReadUB, borrowEntryReadUB, treeBorrowTransitionIsUB,
        placeTouchesUnion, tyProjTouchesUnion, resolveTyWithLocalDecls, isUnresolvedLayoutIdx,
        isUnionLayout, LayoutTable.lookup, evalConstValue, evalScalarBinOpSymTree,
        bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0, operandIsSigned, operandTy,
        sharedBorrowPerm, stringEq, tyIsFreeze, placeTy, resolveProjectedTy, pointeeTyOf,
        tyIsSigned, scalarModulus_2, evalTerminatorSymTreeFast, lookupSwitchTargetTree,
        applyUnwindAction, MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
        initMachineState, initLocalsAux, mirSafePost, readProjectedValue_nil,
        readProjectedValue_field, ProvenancePtr.tag, lookupBorrow, stripTransparentProjections,
        projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
        byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
        isBorrowProtected, natListContainsBool, invalidateConflictingBorrows, updateBorrowPerm,
        freezeDerefReadBorrowsAt, freezeTreeBorrowsOnReadAtProj, updateBorrowPermOnReadAtProj,
        isBorrowDescendantOrSelf, isBorrowDescendantOrSelfAux, disableLocalBorrows,
        treeBorrowWriterRelatedness, applyTreeBorrowTransition, treeBorrowNodeAccess,
        treeBorrowPermTransition, treeBorrowProtectorCheck, treeBorrowChildRead,
        treeBorrowForeignRead, treeBorrowForeignWrite, GetElem?.getElem?, List.get?Internal,
        List.length, List.set, Option.getD, get?, set?, length, Nat.add, Nat.mul, Nat.ble,
        Nat.beq, Bool.and, Bool.or, Bool.not, ite, dite, Nat.decLt, Nat.decLe, Bool.decEq,
        instDecidableEqBool]
    | conv in (evalOperandFallback _ _ _ _ _ _ _) => whnf
    | (rintro ⟨h_val⟩; injection h_val with h_sc; injection h_sc with h_bits _; contradiction)
    | (cases h_ble1 : Nat.ble b1 16 <;> dsimp only [])
    | (cases h_ble2 : Nat.ble b2 1024 <;> dsimp only []))
  intro _
  exact ⟨Nat.le_of_ble_eq_true h_ble1, Nat.le_of_ble_eq_true h_ble2⟩

/-- Universal verification certificate for `frame_total_len` (`polyClaim`: the
signature-typed claim at the empty type substitution) across all valid header
and payload lengths (`header_len ≤ 16`, `payload_len ≤ 1024`).

The `u16` signature pins both arguments to 2-byte scalars and the `requires`
companion bounds them, so the call-free, alias-free body (`checkPureMir`) is
lifted with the `#mir_lift` rules (single-pass `eval_rest_checked_ready` per
block), which synthesize the step budget structurally; no fuel constant appears
in this proof. -/
theorem verified : Obligations.WireframeDemo.frame_total_len.polyClaim := by
  intro typeArgs h_ty
  cases typeArgs with
  | cons _ _ => nomatch h_ty
  | nil =>
  simp only [Obligations.WireframeDemo.frame_total_len.claimFor, CapturedMir.instantiate_nil]
  refine verifyMirNoPanic_of_pureExec _ rfl fun args h_pre => ?_
  obtain ⟨⟨-, h_req⟩, h_len, h_sig⟩ := h_pre
  obtain ⟨v1, v2, rfl⟩ : ∃ v1 v2, args = [v1, v2] := by
    rcases args with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
    all_goals first | exact ⟨_, _, rfl⟩ | nomatch h_len
  obtain ⟨h1, h2, -⟩ := h_sig
  obtain ⟨b1, rfl, -⟩ := u16_of_valueMatchesTy rfl rfl rfl h1
  obtain ⟨b2, rfl, -⟩ := u16_of_valueMatchesTy rfl rfl rfl h2
  obtain ⟨hb1, hb2⟩ := wpReq_inversion b1 b2 h_req
  have h_sum : Nat.add b1 b2 < 65536 := by change b1 + b2 < 65536; omega
  -- bb0: `_3 = AddWithOverflow(_1, _2); assert(!_3.1) -> bb1`, evaluated in one
  -- single-pass `evalPureStmtsCheckedN` step.
  apply lift_PureMirConverges (by rfl)
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.eval_rest_checked_ready (by rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_assert_ready (by rfl) (by rfl) rfl (by rfl) (by rfl)
  · -- The overflow flag is clear: `b1 + b2 ≤ 16 + 1024 < 2^16`.
    change (match Nat.ble 65536 (Nat.add b1 b2) with | true => 1 | false => 0) = 0
    rw [nat_ble_eq_false_of_lt h_sum]
  -- bb1: `_0 = move _3.0; return`
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.eval_rest_checked_ready (by rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_return_ready (by rfl) (by rfl) rfl (by rfl) (by rfl)
  show MirBoolPredicateHolds Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body
      [.scalar ⟨b1, 2⟩, .scalar ⟨b2, 2⟩,
        .scalar ⟨wrapScalarBits (Nat.add b1 b2) 65536, 2⟩] ∧
    retMatchesSignature Mir.WireframeDemo.frame_total_len.body
      (.scalar ⟨wrapScalarBits (Nat.add b1 b2) 65536, 2⟩) _
  rw [wrapScalarBits_eq_of_lt h_sum]
  exact ⟨ensures_holds b1 b2 hb1 hb2,
    u16_retMatchesSignature _ rfl rfl rfl h_sum⟩

/-- Non-vacuity witness confirming `frame_total_len`'s `requires` contract is
satisfiable (`header_len = 4`, `payload_len = 128`). -/
theorem nonVacuousRequires :
    ∃ a : List Value,
      Obligations.WireframeDemo.frame_total_len.rustRequires a := by
  refine ⟨[.scalar { bits := 4, sizeBytes := 2 }, .scalar { bits := 128, sizeBytes := 2 }],
    ⟨rfl, ?_⟩⟩
  exact mirBoolPredicateHolds_of_evalMirSpecBool_true _ _ rfl rfl

end Proof.WireframeDemo.frame_total_len
