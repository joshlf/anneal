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
  -- `dsimp` steps the companion's CFG; each closure-capture deref read
  -- (`evalOperandFallback`), its Tree Borrows read check (`derefReadTreeUB`) and
  -- union check (`placeTouchesUnion`) is evaluated in place by `whnf`, and the
  -- overflow / equality branches on `b1 + b2` are rewritten with `h_ov`, `h_wrap`
  -- and `Nat.beq_refl`.
  repeat (first
    | dsimp only [
        Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.layouts,
        Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body,
        defaultSpecSteps, entryBB, dummyBB, lookupBlock,
        wpBlockLinear, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
        stepMirSymTreeFast, evalSymNodeTree,
        evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
        evalRvalueSymTreeFast, validateLoadedValue, evalOperandFast, evalOperandsFast,
        evalConstValue,
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
        isBorrowDescendantOrSelf, isBorrowDescendantOrSelfAux, disableLocalBorrows,
        treeBorrowWriterRelatedness, applyTreeBorrowTransition, treeBorrowNodeAccess,
        treeBorrowPermTransition, treeBorrowProtectorCheck, treeBorrowChildRead,
        treeBorrowForeignRead, treeBorrowChildWrite, treeBorrowForeignWrite,
        boolToScalar,
        GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
        HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
        List.replicate, List.append, List.length, List.set, List.map, Option.getD,
        get?, set?, length, Nat.add, Nat.mul, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
        ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
        Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    | conv in (evalOperandFallback _ _ _ _ _ _ _) => whnf
    | conv in (derefReadTreeUB _ _ _ _ _) => whnf
    | conv in (placeTouchesUnion _ _ _) => whnf
    | rw [h_ov]
    | rw [h_wrap]
    | rw [Nat.beq_refl])
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
        Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body,
        defaultSpecSteps, entryBB, dummyBB, lookupBlock,
        wpBlockLinear, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
        stepMirSymTreeFast, evalSymNodeTree,
        evalStmtSymTreeFast, finishAssignSymTree, finishAssignStmtNode, advanceStmt,
        evalRvalueSymTreeFast, validateLoadedValue, evalOperandFast, evalOperandsFast,
        evalConstValue,
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
        isBorrowDescendantOrSelf, isBorrowDescendantOrSelfAux, disableLocalBorrows,
        treeBorrowWriterRelatedness, applyTreeBorrowTransition, treeBorrowNodeAccess,
        treeBorrowPermTransition, treeBorrowProtectorCheck, treeBorrowChildRead,
        treeBorrowForeignRead, treeBorrowChildWrite, treeBorrowForeignWrite,
        boolToScalar,
        GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
        HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
        List.replicate, List.append, List.length, List.set, List.map, Option.getD,
        get?, set?, length, Nat.add, Nat.mul, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
        ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
        Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    | conv in (evalOperandFallback _ _ _ _ _ _ _) => whnf
    | conv in (derefReadTreeUB _ _ _ _ _) => whnf
    | conv in (placeTouchesUnion _ _ _) => whnf
    | (rintro ⟨h_val⟩; injection h_val with h_sc; injection h_sc with h_bits _; contradiction)
    | (cases h_ble1 : Nat.ble b1 16 <;> dsimp only [])
    | (cases h_ble2 : Nat.ble b2 1024 <;> dsimp only []))
  intro _
  exact ⟨Nat.le_of_ble_eq_true h_ble1, Nat.le_of_ble_eq_true h_ble2⟩

/-- A value matching the `u16` signature local (layout 0) of the body is a
2-byte scalar below `2^16`. -/
private theorem u16_of_valueMatches {v : Value} {mem : Memory}
    (h : valueMatchesTyAndLayout defaultSignatureFuel Mir.WireframeDemo.frame_total_len.body
      { kind := .uint .u16, layoutIdx := 0 } 0 v mem) :
    ∃ b, v = .scalar { bits := b, sizeBytes := 2 } ∧ b < 65536 := by
  rcases v with _ | ⟨b, sz⟩ | _ | _ <;>
    simp only [valueMatchesTyAndLayout, valueMatchesRigidTyAndLayout, defaultSignatureFuel,
      Mir.WireframeDemo.frame_total_len.body, Mir.WireframeDemo.frame_total_len.layouts,
      sigGet?] at h
  all_goals first
    | exact h.2.2.elim
    | (obtain ⟨-, -, rfl, -, h_lt, -⟩ := h; exact ⟨b, rfl, h_lt⟩)

/-- A 2-byte scalar below `2^16` matches the `u16` return local `_0`. -/
private theorem u16_retMatches (r : Nat) (h : r < 65536) (mem : Memory) :
    retMatchesSignature Mir.WireframeDemo.frame_total_len.body
      (.scalar { bits := r, sizeBytes := 2 }) mem := by
  simp only [retMatchesSignature, valueMatchesTyAndLayout, valueMatchesRigidTyAndLayout,
    defaultSignatureFuel, Mir.WireframeDemo.frame_total_len.body,
    Mir.WireframeDemo.frame_total_len.layouts, sigGet?]
  refine ⟨trivial, rfl, trivial, Nat.two_pos, h, ?_⟩
  show (Nat.ble 0 r && Nat.ble r 65535) = true
  rw [Nat.ble_eq_true_of_le (Nat.zero_le r), Nat.ble_eq_true_of_le (Nat.le_of_lt_succ h)]
  rfl

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
  obtain ⟨b1, rfl, -⟩ := u16_of_valueMatches h1
  obtain ⟨b2, rfl, -⟩ := u16_of_valueMatches h2
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
  exact ⟨ensures_holds b1 b2 hb1 hb2, u16_retMatches _ h_sum _⟩

/-- Non-vacuity witness confirming `frame_total_len`'s `requires` contract is
satisfiable (`header_len = 4`, `payload_len = 128`). -/
theorem nonVacuousRequires :
    ∃ a : List Value,
      Obligations.WireframeDemo.frame_total_len.rustRequires a := by
  refine ⟨[.scalar { bits := 4, sizeBytes := 2 }, .scalar { bits := 128, sizeBytes := 2 }],
    ⟨rfl, ?_⟩⟩
  exact mirBoolPredicateHolds_of_evalMirSpecBool_true _ _ rfl rfl

end Proof.WireframeDemo.frame_total_len
