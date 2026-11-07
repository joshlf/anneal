import Trusted
import Anneal
import Mir.WireframeDemo.checksum_frame_safe
import Specs.WireframeDemo.checksum_frame_safe
import Obligations.WireframeDemo.checksum_frame_safe

namespace Proof.WireframeDemo.checksum_frame_safe

set_option linter.all false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.ITreeWP
open Anneal.PureMirExec
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.WireframeDemo.checksum_frame_safe

/-!
Kernel-checked fuel-free stateful proof for `wireframe_demo::checksum_frame_safe`
(Journey 4 baseline).
-/

private theorem mul_0_2 : Nat.mul 0 2 = 0 := rfl
private theorem mul_1_2 : Nat.mul 1 2 = 2 := rfl
private theorem mul_2_2 : Nat.mul 2 2 = 4 := rfl
private theorem mul_3_2 : Nat.mul 3 2 = 6 := rfl
private theorem mul_12_16 : Nat.mul 12 16 = 192 := rfl
private theorem wrap8_0 : wrapScalarBits 0 18446744073709551616 = 0 := rfl
private theorem wrap8_1 : wrapScalarBits 1 18446744073709551616 = 1 := rfl
private theorem wrap8_2 : wrapScalarBits 2 18446744073709551616 = 2 := rfl
private theorem wrap8_3 : wrapScalarBits 3 18446744073709551616 = 3 := rfl
private theorem wrap8_4 : wrapScalarBits 4 18446744073709551616 = 4 := rfl
private theorem wrap8_5 : wrapScalarBits 5 18446744073709551616 = 5 := rfl
private theorem wrap8_6 : wrapScalarBits 6 18446744073709551616 = 6 := rfl
private theorem wrap8_7 : wrapScalarBits 7 18446744073709551616 = 7 := rfl
private theorem wrap4_8 : wrapScalarBits 8 4294967296 = 8 := rfl

private theorem get?_frame8CallerLocals (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
    get? (frame8CallerLocals b0 b1 b2 b3 b4 b5 b6 b7) frame8SlotIdx =
      some (.init (frame8Value b0 b1 b2 b3 b4 b5 b6 b7)) := rfl

private theorem get?Internal_frame8CallerLocals (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
    List.get?Internal (frame8CallerLocals b0 b1 b2 b3 b4 b5 b6 b7) 69 =
      some (.init (frame8Value b0 b1 b2 b3 b4 b5 b6 b7)) := rfl

/-- Universal stateful verification certificate for `checksum_frame_safe`. -/
theorem verified :
    StatefulVerificationResult Obligations.WireframeDemo.checksum_frame_safe.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_runCfgSteps _ rfl rfl rfl ?_
  intro args mem h_pre
  rcases h_pre with
    ⟨_, b0, b1, b2, b3, b4, b5, b6, b7,
      hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
      rfl, h_callee, h_stack, h_borrows, h_caller⟩
  rcases mem with
    ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls,
      callStack, activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs⟩
  dsimp at h_callee h_stack h_borrows h_caller
  subst h_callee h_stack h_borrows h_caller
  refine ⟨.scalar ⟨bigEndianWordSum4 b0 b1 b2 b3 b4 b5 b6 b7, 4⟩, ?_, ?_⟩
  · dsimp only [
      Obligations.WireframeDemo.checksum_frame_safe.statefulClaim,
      Mir.WireframeDemo.checksum_frame_safe.layouts,
      Mir.WireframeDemo.checksum_frame_safe.body,
      defaultCfgSteps, entryBB, dummyBB, lookupBlock,
      runCfgSteps, stepCfgState, dispatchBlockCfg, stepNodeToCfg, evalTerminatorCfg,
      evalStmtFast, finishAssignStmtNodeFast, advanceStmt,
      evalRvalueFast, evalOperandFast, evalConstValue,
      evalScalarBinOp, evalUnaryNot,
      operandIsSigned, operandTy, sharedBorrowPerm, rigidTyIsFreeze, stringEq,
      tyIsFreeze, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
      intCastTargetBytes, shiftLeftBits, shiftRightUnsignedBits, scalarPow2_eight,
      scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
      mul_1_8, mul_2_8, mul_4_8, mul_8_8, mul_0_2, mul_1_2, mul_2_2, mul_3_2, mul_12_16,
      wrap8_0, wrap8_1, wrap8_2, wrap8_3, wrap8_4, wrap8_5, wrap8_6, wrap8_7, wrap4_8,
      get?_frame8CallerLocals, get?Internal_frame8CallerLocals,
      lookupSwitchTarget, applyUnwindAction,
      MirStepNode.step, MirStepNode.retNormal,
      initMachineStateWithMemory, initLocals, initLocalsAux,
      rootFrame8Ptr, frame8Value, sharedFrame8Borrow, frame8SlotIdx,
      readProjectedValue_nil, readProjectedValue_field, readProjectedValue_index,
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
      get?, set?, length, Nat.add, Nat.mod, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
      ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq, instDecidableEqNat,
      Bool.decEq, instDecidableEqBool, BEq.beq, instBEqOfDecidableEq]
    have h_wb0 : wrapScalarBits b0 4294967296 = b0 := wrapScalarBits_eq_of_lt (by omega)
    have h_wb1 : wrapScalarBits b1 4294967296 = b1 := wrapScalarBits_eq_of_lt (by omega)
    have h_wb2 : wrapScalarBits b2 4294967296 = b2 := wrapScalarBits_eq_of_lt (by omega)
    have h_wb3 : wrapScalarBits b3 4294967296 = b3 := wrapScalarBits_eq_of_lt (by omega)
    have h_wb4 : wrapScalarBits b4 4294967296 = b4 := wrapScalarBits_eq_of_lt (by omega)
    have h_wb5 : wrapScalarBits b5 4294967296 = b5 := wrapScalarBits_eq_of_lt (by omega)
    have h_wb6 : wrapScalarBits b6 4294967296 = b6 := wrapScalarBits_eq_of_lt (by omega)
    have h_wb7 : wrapScalarBits b7 4294967296 = b7 := wrapScalarBits_eq_of_lt (by omega)
    have h_or0 : bitwiseOrBits 32 (wrapScalarBits (b0 * 256) 4294967296) b1 = b0 * 256 + b1 := by
      rw [wrapScalarBits_eq_of_lt (by omega)]
      exact bitwiseOrBits_32_mul256_add (by omega) hb1
    have h_or1 : bitwiseOrBits 32 (wrapScalarBits (b2 * 256) 4294967296) b3 = b2 * 256 + b3 := by
      rw [wrapScalarBits_eq_of_lt (by omega)]
      exact bitwiseOrBits_32_mul256_add (by omega) hb3
    have h_or2 : bitwiseOrBits 32 (wrapScalarBits (b4 * 256) 4294967296) b5 = b4 * 256 + b5 := by
      rw [wrapScalarBits_eq_of_lt (by omega)]
      exact bitwiseOrBits_32_mul256_add (by omega) hb5
    have h_or3 : bitwiseOrBits 32 (wrapScalarBits (b6 * 256) 4294967296) b7 = b6 * 256 + b7 := by
      rw [wrapScalarBits_eq_of_lt (by omega)]
      exact bitwiseOrBits_32_mul256_add (by omega) hb7
    simp only [Nat.add_eq, Nat.mul_eq,
      h_wb0, h_wb1, h_wb2, h_wb3, h_wb4, h_wb5, h_wb6, h_wb7,
      h_or0, h_or1, h_or2, h_or3]
    have h_ovf1 : Nat.ble 4294967296 (0 + (b0 * 256 + b1)) = false := by
      cases hq : Nat.ble 4294967296 (0 + (b0 * 256 + b1))
      · rfl
      · have := Nat.le_of_ble_eq_true hq; omega
    have h_w1 : wrapScalarBits (0 + (b0 * 256 + b1)) 4294967296 = b0 * 256 + b1 := by
      rw [Nat.zero_add]; exact wrapScalarBits_eq_of_lt (by omega)
    have h_ovf2 : Nat.ble 4294967296 (b0 * 256 + b1 + (b2 * 256 + b3)) = false := by
      cases hq : Nat.ble 4294967296 (b0 * 256 + b1 + (b2 * 256 + b3))
      · rfl
      · have := Nat.le_of_ble_eq_true hq; omega
    have h_w2 :
        wrapScalarBits (b0 * 256 + b1 + (b2 * 256 + b3)) 4294967296 =
          (b0 * 256 + b1) + (b2 * 256 + b3) :=
      wrapScalarBits_eq_of_lt (by omega)
    have h_ovf3 :
        Nat.ble 4294967296 ((b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5)) = false := by
      cases hq : Nat.ble 4294967296 ((b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5))
      · rfl
      · have := Nat.le_of_ble_eq_true hq; omega
    have h_w3 :
        wrapScalarBits ((b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5)) 4294967296 =
          (b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5) :=
      wrapScalarBits_eq_of_lt (by omega)
    have h_ovf4 :
        Nat.ble 4294967296
          ((b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5) + (b6 * 256 + b7)) = false := by
      cases hq :
        Nat.ble 4294967296
          ((b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5) + (b6 * 256 + b7))
      · rfl
      · have := Nat.le_of_ble_eq_true hq; omega
    have h_w4 :
        wrapScalarBits
          ((b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5) + (b6 * 256 + b7))
          4294967296 =
          (b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5) + (b6 * 256 + b7) :=
      wrapScalarBits_eq_of_lt (by omega)
    try simp only [h_ovf1, h_w1, h_ovf2, h_w2, h_ovf3, h_w3, h_ovf4, h_w4]
    rfl
  · refine ⟨trivial, rfl, ?_⟩
    intro b0' b1' b2' b3' b4' b5' b6' b7' _ h_caller_eq
    dsimp only at h_caller_eq
    have h_slot :
        List.get?Internal (frame8CallerLocals b0 b1 b2 b3 b4 b5 b6 b7) 69 =
          List.get?Internal (frame8CallerLocals b0' b1' b2' b3' b4' b5' b6' b7') 69 := by
      rw [h_caller_eq]
    rw [get?Internal_frame8CallerLocals, get?Internal_frame8CallerLocals] at h_slot
    dsimp [frame8Value] at h_slot
    injection h_slot with h_init
    injection h_init with h_agg
    injection h_agg with _ h_elems
    injection h_elems with e0 r1
    injection r1 with e1 r2
    injection r2 with e2 r3
    injection r3 with e3 r4
    injection r4 with e4 r5
    injection r5 with e5 r6
    injection r6 with e6 r7
    injection r7 with e7 _
    injection e0 with s0; injection s0 with q0 _
    injection e1 with s1; injection s1 with q1 _
    injection e2 with s2; injection s2 with q2 _
    injection e3 with s3; injection s3 with q3 _
    injection e4 with s4; injection s4 with q4 _
    injection e5 with s5; injection s5 with q5 _
    injection e6 with s6; injection s6 with q6 _
    injection e7 with s7; injection s7 with q7 _
    subst q0 q1 q2 q3 q4 q5 q6 q7
    rfl

end Proof.WireframeDemo.checksum_frame_safe
