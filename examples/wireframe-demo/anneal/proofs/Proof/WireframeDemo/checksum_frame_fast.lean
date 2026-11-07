import Trusted
import Anneal
import Mir.WireframeDemo.checksum_frame_safe
import Mir.WireframeDemo.checksum_frame_fast
import Specs.WireframeDemo.checksum_frame_safe
import Specs.WireframeDemo.checksum_frame_fast
import Obligations.WireframeDemo.checksum_frame_fast
import Proof.WireframeDemo.checksum_frame_safe

namespace Proof.WireframeDemo.checksum_frame_fast

set_option linter.all false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.ITreeWP
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.FunctionalTranslation
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.WireframeDemo.checksum_frame_safe
open Specs.WireframeDemo.checksum_frame_fast
open Proof.WireframeDemo.checksum_frame_safe

/-!
Kernel-checked fuel-free program-to-program behavioral equivalence and
total-correctness proof for `wireframe_demo::checksum_frame_fast` (Journey 4).

The implementation body (`checksum_frame_fast.body`) is evaluated to return
without a step count via `mirNoCallWpConverges_of_runCfgToBlock`, and the
reference specification body (`checksum_frame_safe.body`) reuses the
`forRangeUp` convergence theorem `safe_noCallWpConverges` from
`Proof.WireframeDemo.checksum_frame_safe`.
-/

private def frame4WordsLE (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : Value :=
  .aggregate 0
    [ .scalar { bits := Nat.add (UInt8.ofNat b0).toBitVec.toNat (Nat.mul 256 (UInt8.ofNat b1).toBitVec.toNat), sizeBytes := 2 }
    , .scalar { bits := Nat.add (UInt8.ofNat b2).toBitVec.toNat (Nat.mul 256 (UInt8.ofNat b3).toBitVec.toNat), sizeBytes := 2 }
    , .scalar { bits := Nat.add (UInt8.ofNat b4).toBitVec.toNat (Nat.mul 256 (UInt8.ofNat b5).toBitVec.toNat), sizeBytes := 2 }
    , .scalar { bits := Nat.add (UInt8.ofNat b6).toBitVec.toNat (Nat.mul 256 (UInt8.ofNat b7).toBitVec.toNat), sizeBytes := 2 } ]

private theorem evalByteCastAfterOperand_frame8
    (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) (locals' : List LocalSlot) (mem : Memory) :
    evalByteCastAfterOperand
      Mir.WireframeDemo.checksum_frame_fast.body
      (.move { local_ := 3, projection := .nil })
      { kind := .array (.uint .u16) 4, layoutIdx := 5 }
      (frame8Value b0 b1 b2 b3 b4 b5 b6 b7)
      locals' mem =
    .ok (frame4WordsLE b0 b1 b2 b3 b4 b5 b6 b7) locals' mem := rfl

private theorem evalByteCastAfterOperand_frame8_any
    (b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    {locals' : List LocalSlot} {mem : Memory} {body : CapturedMir}
    (h_decls : body.localDecls = Mir.WireframeDemo.checksum_frame_fast.body.localDecls := by rfl)
    (h_layouts : body.layouts = Mir.WireframeDemo.checksum_frame_fast.layouts := by rfl) :
    evalByteCastAfterOperand
      body
      (.move { local_ := 3, projection := .nil })
      { kind := .array (.uint .u16) 4, layoutIdx := 5 }
      (frame8Value b0 b1 b2 b3 b4 b5 b6 b7)
      locals' mem =
    .ok (frame4WordsLE b0 b1 b2 b3 b4 b5 b6 b7) locals' mem := by
  have h_eq :
      evalByteCastAfterOperand body (.move { local_ := 3, projection := .nil })
        { kind := .array (.uint .u16) 4, layoutIdx := 5 }
        (frame8Value b0 b1 b2 b3 b4 b5 b6 b7) locals' mem =
      evalByteCastAfterOperand Mir.WireframeDemo.checksum_frame_fast.body
        (.move { local_ := 3, projection := .nil })
        { kind := .array (.uint .u16) 4, layoutIdx := 5 }
        (frame8Value b0 b1 b2 b3 b4 b5 b6 b7) locals' mem := by
    unfold evalByteCastAfterOperand
    rw [h_decls, h_layouts]
    rfl
  rw [h_eq]
  exact evalByteCastAfterOperand_frame8 b0 b1 b2 b3 b4 b5 b6 b7 locals' mem

private theorem impl_verified
    (args : List Value) (mem : Memory)
    (h_pre : Obligations.WireframeDemo.checksum_frame_fast.equivClaim.pre args mem) :
    MirNoCallWpConverges Mir.WireframeDemo.checksum_frame_fast.body
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        Mir.WireframeDemo.checksum_frame_fast.body args mem
        Obligations.WireframeDemo.checksum_frame_fast.equivClaim.implCallees)
      (fun out =>
        out = .normal (checksumModel args mem) ∧
        Obligations.WireframeDemo.checksum_frame_fast.equivClaim.post args mem
          (checksumModel args mem).1 (checksumModel args mem).2) := by
  rcases h_pre with
    ⟨_, b0, b1, b2, b3, b4, b5, b6, b7,
      hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
      rfl, h_callee, h_stack, h_borrows, h_caller⟩
  rcases mem with
    ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls,
      callStack, activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs⟩
  dsimp at h_callee h_stack h_borrows h_caller
  subst h_callee h_stack h_borrows h_caller
  let mem₀ : Memory :=
    { nextAllocId, globals, borrows := [sharedFrame8Borrow rootFrame8Ptr],
      nextTag, callees, traitImpls, callStack := [], activeCallee := none,
      activeProtectors, nextProtector,
      callerLocals := frame8CallerLocals b0 b1 b2 b3 b4 b5 b6 b7, fnPtrs }
  rw [checksumModel_eq_of_callerLocals _ _ b0 b1 b2 b3 b4 b5 b6 b7 rfl]
  refine mirNoCallWpConverges_of_runCfgToBlock (target := 0) _ _ rfl _ ?_
  repeat (
    dsimp only [
      cfgStateWP, mem₀, runCfgToBlock, runCfgUntilAux, cfgAtBlock,
      Obligations.WireframeDemo.checksum_frame_fast.equivClaim,
      Trusted.VerificationResult.initMachineStateWithMemoryAndCallees,
      Obligations.WireframeDemo.checksum_frame_fast.defaultCallees,
      Mir.WireframeDemo.checksum_frame_fast.layouts,
      Mir.WireframeDemo.checksum_frame_fast.body,
      lookupBlock, stepCfgState, dispatchBlockCfg, stepNodeToCfg, evalTerminatorCfg,
      evalStmtFast, finishAssignStmtNodeFast, advanceStmt,
      evalRvalueFast, evalByteCastAfterOperand_frame8, frame4WordsLE,
      evalOperandFast, evalConstValue, evalScalarBinOp, evalUnaryNot,
      operandIsSigned, operandTy, sharedBorrowPerm, rigidTyIsFreeze, stringEq,
      tyIsFreeze, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
      intCastTargetBytes, shiftLeftBits, shiftRightUnsignedBits, scalarPow2_eight,
      scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
      mul_1_8, mul_2_8, mul_4_8, mul_8_8, mul_0_2, mul_1_2, mul_2_2, mul_3_2,
      wrap8_0, wrap8_1, wrap8_2, wrap8_3, wrap8_4, wrap8_5, wrap8_6, wrap8_7, wrap4_8,
      get?_frame8CallerLocals, get?Internal_frame8CallerLocals,
      lookupSwitchTarget, applyUnwindAction, MirStepNode.step, MirStepNode.retNormal,
      initMachineStateWithMemory, initLocals, initLocalsAux,
      rootFrame8Ptr, sharedFrame8Borrow, frame8SlotIdx,
      readProjectedValue_nil, readProjectedValue_field, readProjectedValue_index,
      ProvenancePtr.tag, lookupBorrow, appendProjections, stripTransparentProjections,
      projectionsOverlap, projectionsOverlapAux, borrowEntryOverlapsWrite,
      byteRangesOverlapBool, borrowEntryWriteConflicts, hasProtectedWriteConflict,
      isBorrowProtected, natListContainsBool, invalidateConflictingBorrows,
      invalidateConflictingBorrowsAtProj, updateBorrowPerm, updateBorrowPermAtProj,
      freezeDerefReadBorrowsAt, freezeTreeBorrowsOnReadAtProj,
      updateBorrowPermOnReadAtProj, isBorrowDescendantOrSelf,
      isBorrowDescendantOrSelfAux, boolToScalar,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.mod, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    try rw [evalByteCastAfterOperand_frame8_any])
  simp (disch := omega) only [Nat.add_eq, Nat.mul_eq, Nat.div_eq,
    uint8_ofNat_toBitVec_toNat_of_lt, swap_le_u16_lane,
    wrapScalarBits_eq_of_lt, nat_ble_eq_false_of_lt]
  rw [wrapScalarBits_eq_of_lt (val := b0 * 256 + b1 + (b2 * 256 + b3)) (by omega),
    wrapScalarBits_eq_of_lt (val := b0 * 256 + b1 + (b2 * 256 + b3) + (b4 * 256 + b5)) (by omega),
    wrapScalarBits_eq_of_lt (val := b0 * 256 + b1 + (b2 * 256 + b3) + (b4 * 256 + b5) + (b6 * 256 + b7)) (by omega),
    nat_ble_eq_false_of_lt (v := b0 * 256 + b1 + (b2 * 256 + b3)) (by omega),
    nat_ble_eq_false_of_lt (v := b0 * 256 + b1 + (b2 * 256 + b3) + (b4 * 256 + b5)) (by omega),
    nat_ble_eq_false_of_lt (v := b0 * 256 + b1 + (b2 * 256 + b3) + (b4 * 256 + b5) + (b6 * 256 + b7)) (by omega)]
  exact ⟨rfl, rfl, frame8_post_holds b0 b1 b2 b3 b4 b5 b6 b7 mem₀ rfl⟩

/-- Behavioral-equivalence and total-correctness certificate for
`checksum_frame_fast`. -/
theorem verified :
    StatefulEquivVerificationResult Obligations.WireframeDemo.checksum_frame_fast.equivClaim :=
  verifyStatefulEquivMir_of_wpConverges
    Obligations.WireframeDemo.checksum_frame_fast.equivClaim
    checksumModel
    impl_verified
    fun args mem h_pre =>
      Anneal.MirFuelFree.MirNoCallWpConverges.mono (fun _ h => h.1)
        (safe_noCallWpConverges args mem h_pre)

end Proof.WireframeDemo.checksum_frame_fast
