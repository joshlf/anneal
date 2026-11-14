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
open Anneal.SepLogicLenses
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.FunctionalTranslation

/-- On the `clamp` result `ret`, `ret == requested` failing forces `ret = max_window`. -/
private theorem beq_max_of_beq_requested_false {b1 b2 ret : Nat}
    (h_ret : (b1 ≤ b2 ∧ ret = b1) ∨ (b2 < b1 ∧ ret = b2)) (h : Nat.beq ret b1 = false) :
    Nat.beq ret b2 = true := by
  have h_ne := Nat.ne_of_beq_eq_false h
  have h_eq : ret = b2 := by omega
  rw [h_eq]
  exact Nat.beq_refl b2

private theorem ensures_holds (b1 b2 ret : Nat)
    (h_ret : (b1 ≤ b2 ∧ ret = b1) ∨ (b2 < b1 ∧ ret = b2)) :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body
      [.scalar { bits := b1, sizeBytes := 2 },
       .scalar { bits := b2, sizeBytes := 2 },
       .scalar { bits := ret, sizeBytes := 2 }] := by
  have h_le_req : Nat.ble ret b1 = true := Nat.ble_eq_true_of_le (by omega)
  have h_le_max : Nat.ble ret b2 = true := Nat.ble_eq_true_of_le (by omega)
  apply Hold.val
  refine hold_mirBool_of_blockLinear _ _ rfl rfl ?_
  -- `dsimp` steps the companion's CFG once for symbolic `ret`; each closure-capture
  -- deref read (`evalOperandFallback`) is evaluated in place by `whnf`, while
  -- `ret <= requested` and `ret <= max_window` are rewritten to `true` immediately
  -- (pruning the dead `false` arms at `bb0`/`bb1`), and the `ret == requested || ret == max_window`
  -- disjunction is split only when evaluation reaches `bb2`.
  repeat (first
      | dsimp only [
          Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.layouts,
          Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body, defaultSpecSteps,
          entryBB, dummyBB, lookupBlock, wpBlockLinear, wpCfgStep, dispatchBlock,
          evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode,
          advanceStmt, evalRvalueSymTreeFast, validateLoadedValue, evalOperandFast,
          derefReadTreeUB, hasTreeReadUB, borrowEntryReadUB, treeBorrowTransitionIsUB,
          placeTouchesUnion, tyProjTouchesUnion, resolveTyWithLocalDecls, isUnresolvedLayoutIdx,
          isUnionLayout, LayoutTable.lookup, evalOperandsFast, evalConstValue,
          evalScalarBinOpSymTree, bitwiseAndBitsFast, mod_1_2, bitwiseAndBits_8_1_0,
          operandIsSigned, operandTy, sharedBorrowPerm, stringEq, tyIsFreeze, placeTy,
          resolveProjectedTy, pointeeTyOf, tyIsSigned, evalTerminatorSymTreeFast,
          lookupSwitchTargetTree, MirStepNode.step, MirStepNode.retNormal, SymTree.bind,
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
          List.length, List.set, Option.getD, get?, set?, length, Nat.add, Nat.mul, Nat.beq,
          Bool.and, Bool.or, Bool.not, ite, dite, Nat.decLt, Nat.decLe, Bool.decEq,
          instDecidableEqBool]
      | rw [h_le_req]
      | rw [h_le_max]
      | conv in (evalOperandFallback _ _ _ _ _ _ _) => whnf
      | rw [beq_max_of_beq_requested_false h_ret ‹Nat.beq ret b1 = false›]
      | (cases h_eq : Nat.beq ret b1 <;> dsimp only []))
  all_goals exact ⟨boolTruePost_normal_one _⟩

/-- Universal verification certificate for `clamp_payload_window` (`polyClaim`:
the signature-typed claim at the empty type substitution) across all
`requested : u16` and `max_window : u16`.

The `u16` signature pins both arguments to 2-byte scalars, so the call-free,
alias-free body (`checkPureMir`) is lifted with `liftBlock_switchInt_diamond_toJoin`
to the shared `return` block `bb3`, which is lifted once. The step budget is
synthesized structurally (no fuel constant appears in this proof). -/
theorem verified : Obligations.WireframeDemo.clamp_payload_window.polyClaim := by
  intro typeArgs h_ty
  cases typeArgs with
  | cons _ _ => nomatch h_ty
  | nil =>
  simp only [Obligations.WireframeDemo.clamp_payload_window.claimFor, CapturedMir.instantiate_nil]
  refine verifyMirNoPanic_of_pureExec _ rfl fun args h_pre => ?_
  obtain ⟨-, h_len, h_sig⟩ := h_pre
  obtain ⟨v1, v2, rfl⟩ : ∃ v1 v2, args = [v1, v2] := by
    rcases args with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
    all_goals first | exact ⟨_, _, rfl⟩ | nomatch h_len
  obtain ⟨h1, h2, -⟩ := h_sig
  obtain ⟨b1, rfl, hb1⟩ := u16_of_valueMatchesTy rfl rfl rfl h1
  obtain ⟨b2, rfl, hb2⟩ := u16_of_valueMatchesTy rfl rfl rfl h2
  -- Both arms of the `requested <= max_window` diamond reach the shared `return`
  -- block bb3 with `_0 = min(requested, max_window)`, so bb3 is lifted once.
  refine LiftBlockToJoin.pureMirConverges (joinBb := 3)
    (JoinInv := fun env => ∃ r, ((b1 ≤ b2 ∧ r = b1) ∨ (b2 < b1 ∧ r = b2)) ∧
      get? env 0 = some (.init (.scalar ⟨r, 2⟩))) ?_ ?_
  · refine liftBlock_switchInt_diamond_toJoin (thenBb := 1) (elseBb := 2) (b1 ≤ b2)
      (by rfl) (by rfl) (by rfl) rfl (by rfl)
      (fun h => ⟨by rw [Nat.ble_eq_true_of_le h]; rfl,
        liftBlock_goto_toJoin (by rfl) (by rfl) (by rfl) rfl
          (LiftBlockToJoin.refl ⟨b1, Or.inl ⟨h, rfl⟩, rfl⟩)⟩)
      (fun h => ⟨by rw [nat_ble_eq_false_of_not_le h]; rfl,
        liftBlock_goto_toJoin (by rfl) (by rfl) (by rfl) rfl
          (LiftBlockToJoin.refl ⟨b2, Or.inr ⟨Nat.lt_of_not_le h, rfl⟩, rfl⟩)⟩)
  · rintro env ⟨r, h_r, h_ret⟩
    exact LiftBlockConverges.of_lookup (by rfl)
      (LiftStmtsConverges.term_return_ready (by rfl) (by rfl) rfl rfl h_ret
        ⟨ensures_holds b1 b2 r h_r,
          u16_retMatchesSignature _ rfl rfl rfl (by omega)⟩)

/-- Non-vacuity witness confirming `clamp_payload_window`'s `requires` contract
is satisfiable (`requested = 512`, `max_window = 1024`). -/
theorem nonVacuousRequires :
    ∃ a : List Value,
      Obligations.WireframeDemo.clamp_payload_window.rustRequires a := by
  refine ⟨[.scalar { bits := 512, sizeBytes := 2 }, .scalar { bits := 1024, sizeBytes := 2 }],
    ⟨rfl, ?_⟩⟩
  exact mirBoolPredicateHolds_of_evalMirSpecBool_true _ _ rfl rfl

end Proof.WireframeDemo.clamp_payload_window
