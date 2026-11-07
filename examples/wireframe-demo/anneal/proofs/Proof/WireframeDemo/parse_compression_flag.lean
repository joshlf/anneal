import Trusted
import Anneal
import Mir.WireframeDemo.parse_compression_flag
import Specs.WireframeDemo.parse_compression_flag
import Obligations.WireframeDemo.parse_compression_flag

namespace Proof.WireframeDemo.parse_compression_flag

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
open Specs.WireframeDemo.parse_compression_flag

private theorem rustRequires_imp_zero_or_one (b : Nat)
    (h_req : Obligations.WireframeDemo.parse_compression_flag.rustRequires
      [.scalar { bits := b, sizeBytes := 1 }]) :
    b = 0 ∨ b = 1 := by
  have h_hold :=
    holdBoolReq_of_mirBool
      Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body
      [.scalar { bits := b, sizeBytes := 1 }] rfl rfl h_req.2
  revert h_hold
  dsimp only [
    Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.body,
    Mir.WireframeDemo.__anodized_fn_requires_parse_compression_flag.layouts,
    defaultSpecSteps, entryBB, dummyBB, lookupBlock,
    wpBlockLinear, wpCfgStep, dispatchBlock, wpExecFallback, wpExecGen,
    stepMirSymTreeFast, evalSymNodeTree, evalStmtSymTreeFast, finishAssignSymTree,
    finishAssignStmtNode, advanceStmt, evalRvalueSymTreeFast, evalOperandFast,
    evalOperandsFast, evalConstValue, evalScalarBinOpSymTree, bitwiseAndBitsFast,
    evalUnaryNotSymTree, operandIsSigned, operandTy, sharedBorrowPerm,
    rigidTyIsFreeze, stringEq, tyIsFreeze, placeTy, resolveProjectedTy,
    pointeeTyOf, elemTyOf, tyIsSigned, evalTerminatorSymTreeFast,
    lookupSwitchTargetTree, applyUnwindAction, MirStepNode.step,
    MirStepNode.retNormal, SymTree.bind, initMachineState, initLocals,
    initLocalsAux, emptyMemory, mirSafePost, readProjectedValue_nil,
    readProjectedValue_field, ProvenancePtr.tag, lookupBorrow, appendProjections,
    stripTransparentProjections, projectionsOverlap, projectionsOverlapAux,
    borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts,
    hasProtectedWriteConflict, isBorrowProtected, natListContainsBool,
    invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj,
    updateBorrowPerm, updateBorrowPermAtProj, freezeDerefReadBorrowsAt,
    freezeTreeBorrowsOnReadAtProj, updateBorrowPermOnReadAtProj,
    isBorrowDescendantOrSelf, isBorrowDescendantOrSelfAux, boolToScalar,
    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
    get?, set?, length, Nat.add, Nat.mul, Nat.ble, Nat.beq, Bool.and, Bool.or,
    Bool.not, bitwiseAndBits_one_one, bitwiseAndBits_one_zero,
    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
  intro h_hold
  cases h_eq : Nat.beq (b % 2) b with
  | false =>
    rw [h_eq] at h_hold
    rcases h_hold with ⟨h_val⟩
    injection h_val with h_sc
    injection h_sc with h_bits _
    nomatch h_bits
  | true =>
    exact eq_zero_or_one_of_mod2_eq (Nat.eq_of_beq_eq_true h_eq).symm

private theorem compressionFlagPost_bit (b : Nat) (hb : b = 0 ∨ b = 1) :
    compressionFlagPost
      [.scalar { bits := b, sizeBytes := 1 }]
      (.scalar { bits := b, sizeBytes := 1 }) := by
  intro b' h_eq
  injection h_eq with h_hd _
  injection h_hd with h_sc
  injection h_sc with h_bits _
  subst h_bits
  rcases hb with rfl | rfl <;> rfl

/-- Total-safety + functional verification certificate for
`parse_compression_flag`.

The body is call-free and alias-free (`checkPureMir`), so it is lifted with the
`#mir_lift` rules applied explicitly over all `256` inputs (the step budget is
synthesized structurally by the rules; no fuel constant appears in this proof).
Only the guarded functional postcondition consults `rustRequires`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.parse_compression_flag.claim := by
  refine verifyMirNoPanic_of_pureExec _ rfl fun args h_pre => ?_
  obtain ⟨b, -, rfl⟩ := h_pre
  -- bb0: `_2 = BitAnd(_1, const 1_u8); _0 = Ne(move _2, const 0_u8); return`
  apply lift_PureMirConverges (by rfl)
  apply LiftBlock.of_lookup (by rfl)
  repeat apply LiftStmtsTerminator.cons_eval (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro ⟨h_req, -⟩
  rcases rustRequires_imp_zero_or_one b h_req with rfl | rfl <;>
    exact ⟨mirBoolPredicateHolds_of_evalMirSpecBool_true _ _ rfl rfl,
      compressionFlagPost_bit _ (by decide)⟩

/-- Non-vacuity witness confirming `parse_compression_flag`'s functional
`rustRequires` contract is satisfiable (`flags_byte = 1`). -/
theorem nonVacuousRequires :
    ∃ a : List Value,
      Obligations.WireframeDemo.parse_compression_flag.rustRequires a := by
  refine ⟨[.scalar { bits := 1, sizeBytes := 1 }], ⟨rfl, ?_⟩⟩
  exact mirBoolPredicateHolds_of_evalMirSpecBool_true _ _ rfl rfl

end Proof.WireframeDemo.parse_compression_flag
