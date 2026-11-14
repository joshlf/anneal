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
  -- deref read (`evalOperandFallback`), its Tree Borrows read check
  -- (`derefReadTreeUB`) and union check (`placeTouchesUnion`) is evaluated in place
  -- by `whnf`; `ret <= requested` and `ret <= max_window` are rewritten to `true`,
  -- and the `ret == requested || ret == max_window` disjunction is split only when
  -- the evaluation reaches it.
  repeat (first
      | dsimp only [
          Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.layouts,
          Mir.WireframeDemo.__anodized_fn_ensures_clamp_payload_window.body,
          defaultSpecSteps, entryBB, dummyBB, lookupBlock,
          wpBlockLinear, wpCfgStep, dispatchBlock,
          evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree,
          finishAssignStmtNode, advanceStmt, evalRvalueSymTreeFast, validateLoadedValue,
          evalOperandFast,
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
          isBorrowDescendantOrSelfAux, disableLocalBorrows,
          treeBorrowWriterRelatedness, applyTreeBorrowTransition, treeBorrowNodeAccess,
          treeBorrowPermTransition, treeBorrowProtectorCheck, treeBorrowChildRead,
          treeBorrowForeignRead, treeBorrowChildWrite, treeBorrowForeignWrite,
          boolToScalar,
          GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
          HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
          List.replicate, List.append, List.length, List.set, List.map, Option.getD,
          get?, set?, length, Nat.add, Nat.mul, Nat.beq, Bool.and, Bool.or, Bool.not,
          ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
          Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
      | conv in (evalOperandFallback _ _ _ _ _ _ _) => whnf
      | conv in (derefReadTreeUB _ _ _ _ _) => whnf
      | conv in (placeTouchesUnion _ _ _) => whnf
      | rw [h_le_req]
      | rw [h_le_max]
      | rw [beq_max_of_beq_requested_false h_ret ‹Nat.beq ret b1 = false›]
      | (cases h_eq : Nat.beq ret b1 <;> dsimp only []))
  all_goals exact ⟨boolTruePost_normal_one _⟩

/-- A value matching the `u16` signature local (layout 0) of the body is a
2-byte scalar below `2^16`. -/
private theorem u16_of_valueMatches {v : Value} {mem : Memory}
    (h : valueMatchesTyAndLayout defaultSignatureFuel Mir.WireframeDemo.clamp_payload_window.body
      { kind := .uint .u16, layoutIdx := 0 } 0 v mem) :
    ∃ b, v = .scalar { bits := b, sizeBytes := 2 } ∧ b < 65536 := by
  rcases v with _ | ⟨b, sz⟩ | _ | _ <;>
    simp only [valueMatchesTyAndLayout, valueMatchesRigidTyAndLayout, defaultSignatureFuel,
      Mir.WireframeDemo.clamp_payload_window.body, Mir.WireframeDemo.clamp_payload_window.layouts,
      sigGet?] at h
  all_goals first
    | exact h.2.2.elim
    | (obtain ⟨-, -, rfl, -, h_lt, -⟩ := h; exact ⟨b, rfl, h_lt⟩)

/-- A 2-byte scalar below `2^16` matches the `u16` return local `_0`. -/
private theorem u16_retMatches (r : Nat) (h : r < 65536) (mem : Memory) :
    retMatchesSignature Mir.WireframeDemo.clamp_payload_window.body
      (.scalar { bits := r, sizeBytes := 2 }) mem := by
  simp only [retMatchesSignature, valueMatchesTyAndLayout, valueMatchesRigidTyAndLayout,
    defaultSignatureFuel, Mir.WireframeDemo.clamp_payload_window.body,
    Mir.WireframeDemo.clamp_payload_window.layouts, sigGet?]
  refine ⟨trivial, rfl, trivial, Nat.two_pos, h, ?_⟩
  show (Nat.ble 0 r && Nat.ble r 65535) = true
  rw [Nat.ble_eq_true_of_le (Nat.zero_le r), Nat.ble_eq_true_of_le (Nat.le_of_lt_succ h)]
  rfl

/-- Universal verification certificate for `clamp_payload_window` (`polyClaim`:
the signature-typed claim at the empty type substitution) across all
`requested : u16` and `max_window : u16`.

The `u16` signature pins both arguments to 2-byte scalars, so the call-free,
alias-free body (`checkPureMir`) is lifted with the `#mir_lift` rules; the
`switchInt` on `requested <= max_window` is split on a `LiftStmtsToJoin` path to
the shared `return` block bb3, which is lifted once. The step budget is
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
  obtain ⟨b1, rfl, hb1⟩ := u16_of_valueMatches h1
  obtain ⟨b2, rfl, hb2⟩ := u16_of_valueMatches h2
  -- Both arms of the `requested <= max_window` switch reach the shared `return`
  -- block bb3 with `_0 = min(requested, max_window)`, so bb3 is lifted once.
  refine LiftBlockToJoin.pureMirConverges (joinBb := 3)
    (JoinInv := fun env => ∃ r, ((b1 ≤ b2 ∧ r = b1) ∨ (b2 < b1 ∧ r = b2)) ∧
      get? env 0 = some (.init (.scalar ⟨r, 2⟩))) ?_ ?_
  · -- bb0: `_3 = Le(_1, _2); switchInt(_3) -> [0: bb2, otherwise: bb1]`
    refine LiftBlockToJoin.of_lookup (by rfl) ?_
    refine LiftStmtsToJoin.eval_rest_checked_ready (by rfl) (by rfl) (by rfl) ?_
    refine LiftStmtsToJoin.term_switchInt_cases_ready (thenBb := 1) (elseBb := 2)
      (by rfl) (by rfl) rfl (by rfl) (by rfl) (b1 ≤ b2)
      (fun h => ⟨?_, ?_⟩) (fun h => ⟨?_, ?_⟩)
    · change lookupSwitchTarget (boolToScalar (Nat.ble b1 b2)).bits [(0, 2)] 1 = 1
      rw [Nat.ble_eq_true_of_le h]
      rfl
    · -- bb1: `_0 = copy _1; goto bb3`
      refine LiftBlockToJoin.of_lookup (by rfl) ?_
      refine LiftStmtsToJoin.eval_rest_checked_ready (by rfl) (by rfl) (by rfl) ?_
      exact LiftStmtsToJoin.term_goto_ready (by rfl) (by rfl) rfl (by rfl)
        (LiftBlockToJoin.refl ⟨b1, Or.inl ⟨h, rfl⟩, rfl⟩)
    · change lookupSwitchTarget (boolToScalar (Nat.ble b1 b2)).bits [(0, 2)] 1 = 2
      rw [Anneal.FunctionalTranslation.nat_ble_eq_false_of_lt (Nat.lt_of_not_le h)]
      rfl
    · -- bb2: `_0 = copy _2; goto bb3`
      refine LiftBlockToJoin.of_lookup (by rfl) ?_
      refine LiftStmtsToJoin.eval_rest_checked_ready (by rfl) (by rfl) (by rfl) ?_
      exact LiftStmtsToJoin.term_goto_ready (by rfl) (by rfl) rfl (by rfl)
        (LiftBlockToJoin.refl ⟨b2, Or.inr ⟨Nat.lt_of_not_le h, rfl⟩, rfl⟩)
  · -- bb3: `return`, lifted once for both arms.
    rintro env ⟨r, h_r, h_ret⟩
    refine LiftBlockConverges.of_lookup (by rfl) ⟨1, ?_⟩
    exact LiftStmtsTerminator.term_return_ready (by rfl) (by rfl) rfl (by rfl) h_ret
      ⟨ensures_holds b1 b2 r h_r, u16_retMatches r (by omega) _⟩

/-- Non-vacuity witness confirming `clamp_payload_window`'s `requires` contract
is satisfiable (`requested = 512`, `max_window = 1024`). -/
theorem nonVacuousRequires :
    ∃ a : List Value,
      Obligations.WireframeDemo.clamp_payload_window.rustRequires a := by
  refine ⟨[.scalar { bits := 512, sizeBytes := 2 }, .scalar { bits := 1024, sizeBytes := 2 }],
    ⟨rfl, ?_⟩⟩
  exact mirBoolPredicateHolds_of_evalMirSpecBool_true _ _ rfl rfl

end Proof.WireframeDemo.clamp_payload_window
