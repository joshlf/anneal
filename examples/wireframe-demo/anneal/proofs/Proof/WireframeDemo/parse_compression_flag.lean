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

private theorem ensures_holds_one :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body
      [.scalar { bits := 1, sizeBytes := 1 }, .scalar { bits := 1, sizeBytes := 1 }] :=
  mirBoolPredicateHolds_of_evalMirSpecBool_true _ _ rfl rfl

private theorem ensures_holds_zero :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body
      [.scalar { bits := 0, sizeBytes := 1 }, .scalar { bits := 0, sizeBytes := 1 }] :=
  mirBoolPredicateHolds_of_evalMirSpecBool_true _ _ rfl rfl

private theorem ensures_holds_of_eq_one (b : Nat) (hb1 : b = 1) :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body
      [.scalar { bits := b, sizeBytes := 1 }, .scalar { bits := 1, sizeBytes := 1 }] :=
  hb1 ▸ ensures_holds_one

private theorem ensures_holds_of_eq_zero (b : Nat) (hb0 : b = 0) :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_parse_compression_flag.body
      [.scalar { bits := b, sizeBytes := 1 }, .scalar { bits := 0, sizeBytes := 1 }] :=
  hb0 ▸ ensures_holds_zero

private theorem compressionFlagPost_one (b : Nat) (hb1 : b = 1) :
    compressionFlagPost
      [.scalar { bits := b, sizeBytes := 1 }]
      (.scalar { bits := 1, sizeBytes := 1 }) := by
  subst hb1
  intro b' h_eq
  injection h_eq with h_hd _
  injection h_hd with h_sc
  injection h_sc with h_bits _
  subst h_bits
  rfl

private theorem compressionFlagPost_zero (b : Nat) (hb0 : b = 0) :
    compressionFlagPost
      [.scalar { bits := b, sizeBytes := 1 }]
      (.scalar { bits := 0, sizeBytes := 1 }) := by
  subst hb0
  intro b' h_eq
  injection h_eq with h_hd _
  injection h_hd with h_sc
  injection h_sc with h_bits _
  subst h_bits
  rfl

/-- Total-safety + functional verification certificate for `parse_compression_flag`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.parse_compression_flag.claim := by
  refine verifyMirNoPanic_of_blockLinear _ rfl rfl rfl ?_
  intro args h_pre
  rcases h_pre with ⟨b, _hb, h_args⟩
  rw [h_args]
  dsimp only [
    Obligations.WireframeDemo.parse_compression_flag.claim,
    Obligations.WireframeDemo.parse_compression_flag.refineSafeSpec,
    Obligations.WireframeDemo.parse_compression_flag.rustEnsures,
    Obligations.WireframeDemo.parse_compression_flag.defaultPost,
    ItemSpec.post,
    Mir.WireframeDemo.parse_compression_flag.body,
    Mir.WireframeDemo.parse_compression_flag.layouts,
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
    initLocalsAux, emptyMemory, mirNormalPost, readProjectedValue_nil,
    readProjectedValue_field, invalidateConflictingBorrows, boolToScalar,
    GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
    List.replicate, List.append, List.length, List.set, List.map, Option.getD,
    get?, set?, length, Nat.add, Nat.mul, Nat.beq, Bool.and, Bool.or,
    bitwiseAndBits_one_one, bitwiseAndBits_one_zero,
    ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
    Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
  by_cases h_odd : b % 2 = 1
  · rw [beq_mod2_zero_of_odd h_odd]
    exact ⟨fun h_req_pair =>
      let hb1 : b = 1 :=
        eq_one_of_zero_or_one_and_odd
          (rustRequires_imp_zero_or_one b h_req_pair.1) h_odd
      ⟨ensures_holds_of_eq_one b hb1, compressionFlagPost_one b hb1⟩⟩
  · rw [beq_mod2_zero_of_not_odd h_odd]
    exact ⟨fun h_req_pair =>
      let hb0 : b = 0 :=
        eq_zero_of_zero_or_one_and_not_odd
          (rustRequires_imp_zero_or_one b h_req_pair.1) h_odd
      ⟨ensures_holds_of_eq_zero b hb0, compressionFlagPost_zero b hb0⟩⟩

/-- Non-vacuity witness confirming `parse_compression_flag`'s functional
`rustRequires` contract is satisfiable (`flags_byte = 1`). -/
theorem nonVacuousRequires :
    ∃ a : List Value,
      Obligations.WireframeDemo.parse_compression_flag.rustRequires a := by
  refine ⟨[.scalar { bits := 1, sizeBytes := 1 }], ⟨rfl, ?_⟩⟩
  exact mirBoolPredicateHolds_of_evalMirSpecBool_true _ _ rfl rfl

end Proof.WireframeDemo.parse_compression_flag
