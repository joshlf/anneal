import Trusted
import Anneal
import Mir.WireframeDemo.checksum_frame_safe
import Mir.WireframeDemo.checksum_frame_fast
import Specs.WireframeDemo.checksum_frame_safe
import Specs.WireframeDemo.checksum_frame_fast
import Obligations.WireframeDemo.checksum_frame_fast
import Proof.WireframeDemo.checksum_frame_safe

namespace Proof.WireframeDemo.checksum_frame_fast

set_option maxRecDepth 200000

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
without a step count in two `runCfgToBlock` segments joined by
`MirNoCallWpConverges.bind_reachState` at `fastBb1State`: `bb0` (every
`StorageLive`, which consults the active function-entry protectors only when
some are active, so this segment alone splits on them) and `bb1` to the return.
The reference specification body (`checksum_frame_safe.body`) reuses the
`forRangeUp` convergence theorem `safe_noCallWpConverges` and the shared
`frame8Pre_cases` precondition split from `Proof.WireframeDemo.checksum_frame_safe`.
-/

/-- Little-endian `u16` lane decoded from the bytes `lo` and `hi`. -/
private def le16 (lo hi : Nat) : Value :=
  .scalar ⟨Nat.add (UInt8.ofNat lo).toBitVec.toNat (Nat.mul 256 (UInt8.ofNat hi).toBitVec.toNat),
    2⟩

/-- The `[u16; 4]` lanes of the frame `[b0, .., b7]`. -/
private def frame4WordsLE (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : Value :=
  .aggregate 0 [le16 b0 b1, le16 b2 b3, le16 b4 b5, le16 b6 b7]

/-- The `[u8; 8] → [u16; 4]` transmute of `_3` in `bb0`, for any body whose
local declarations and layouts are `checksum_frame_fast`'s (so it also rewrites
the unfolded body). -/
private theorem evalByteCastAfterOperand_frame8
    (b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    {locals' : List LocalSlot} {mem : Memory} {body : CapturedMir}
    (h_decls : body.localDecls = Mir.WireframeDemo.checksum_frame_fast.body.localDecls := by rfl)
    (h_layouts : body.layouts = Mir.WireframeDemo.checksum_frame_fast.layouts := by rfl) :
    evalByteCastAfterOperand body (.move { local_ := 3, projection := .nil })
      { kind := .array (.uint .u16) 4, layoutIdx := 5 }
      (frame8Value b0 b1 b2 b3 b4 b5 b6 b7) locals' mem =
    .ok (frame4WordsLE b0 b1 b2 b3 b4 b5 b6 b7) locals' mem := by
  unfold evalByteCastAfterOperand
  rw [h_decls, h_layouts]
  rfl

/-- Machine state entering `bb1`: `_2` holds the transmuted `[u16; 4]` lanes,
`_9 = 0`, and every other temporary is uninitialised. -/
private def fastBb1State (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) (m : Memory) (ap : List Nat) :
    MachineState :=
  { frame := {
      blockIdx := 1
      stmtIdx := 0
      locals := .uninit :: .init (.ptr rootFrame8Ptr 8) ::
        .init (frame4WordsLE b0 b1 b2 b3 b4 b5 b6 b7) :: List.replicate 6 .uninit ++
        .init (.scalar ⟨0, 8⟩) :: List.replicate 59 .uninit }
    memory := frame8Mem b0 b1 b2 b3 b4 b5 b6 b7 m ap }

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
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, m, ap, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
    rfl, rfl⟩ := frame8Pre_cases h_pre.2
  rw [checksumModel_eq_of_callerLocals _ _ b0 b1 b2 b3 b4 b5 b6 b7 rfl]
  refine MirNoCallWpConverges.bind_reachState
    (s' := fastBb1State b0 b1 b2 b3 b4 b5 b6 b7 m ap)
    (mirStepsConverges_of_runCfgToBlock (target := 1) _ _ _ rfl _ ?entry)
    (mirNoCallWpConverges_of_runCfgToBlock (target := 0) _ _ rfl _ ?exit)
  case' entry => cases ap -- `StorageLive` checks the active protectors if any
  all_goals
    repeat (
      dsimp only [
        cfgStepsWP, cfgStateWP, fastBb1State, frame8Mem, runCfgToBlock, runCfgUntilAux,
        cfgAtBlock, hasProtectedLocalBorrow, disableLocalBorrows, placeTouchesUnion,
        tyProjTouchesUnion, resolveTyWithLocalDecls, isUnresolvedLayoutIdx, isUnionLayout,
        LayoutTable.lookup, evalOperandFallback, evalOperand, needsThinPtrElemResolution,
        Obligations.WireframeDemo.checksum_frame_fast.equivClaim,
        Trusted.VerificationResult.initMachineStateWithMemoryAndCallees,
        Obligations.WireframeDemo.checksum_frame_fast.defaultCallees,
        Mir.WireframeDemo.checksum_frame_fast.layouts,
        Mir.WireframeDemo.checksum_frame_fast.body, lookupBlock, stepCfgState,
        dispatchBlockCfg, stepNodeToCfg, evalTerminatorCfg, evalStmtFast,
        finishAssignStmtNodeFast, advanceStmt, evalRvalueFast, validateLoadedValue,
        frame4WordsLE, le16, evalOperandFast, evalConstValue, evalScalarBinOp, operandIsSigned,
        operandTy, stringEq, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
        intCastTargetBytes, shiftLeftBits, shiftRightUnsignedBits, scalarPow2_eight,
        scalarModulus_2, scalarModulus_4, mul_2_8, wrap4_8, get?Internal_frame8CallerLocals,
        MirStepNode.step, initMachineStateWithMemory, initLocals, initLocalsAux,
        rootFrame8Ptr, sharedFrame8Borrow, frame8SlotIdx, readProjectedValue_nil,
        readProjectedValue_field, readProjectedValue_index, ProvenancePtr.tag, lookupBorrow,
        stripTransparentProjections, projectionsOverlap, projectionsOverlapAux,
        borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts,
        hasProtectedWriteConflict, isBorrowProtected, natListContainsBool,
        invalidateConflictingBorrows, updateBorrowPerm, freezeDerefReadBorrowsAt,
        freezeTreeBorrowsOnReadAtProj, updateBorrowPermOnReadAtProj, isBorrowDescendantOrSelf,
        isBorrowDescendantOrSelfAux, boolToScalar, GetElem?.getElem?, List.get?Internal,
        List.length, List.set, List.replicate, HAppend.hAppend, Append.append, List.append,
        get?, set?, length, Nat.add, Nat.mod, Nat.ble, Nat.beq, Bool.and, Bool.or, Bool.not,
        ite, dite, Nat.decLt, Nat.decLe, Bool.decEq, instDecidableEqBool]
      try rw [evalByteCastAfterOperand_frame8])
  case entry.nil | entry.cons => exact ⟨rfl, rfl⟩
  case exit =>
    simp (disch := omega) only [Nat.add_eq, Nat.mul_eq, uint8_ofNat_toBitVec_toNat_of_lt,
      swap_le_u16_lane, wrapScalarBits_eq_of_lt]
    have h1 : b0 * 256 + b1 + (b2 * 256 + b3) < 4294967296 := by omega
    have h2 : b0 * 256 + b1 + (b2 * 256 + b3) + (b4 * 256 + b5) < 4294967296 := by omega
    have h3 : b0 * 256 + b1 + (b2 * 256 + b3) + (b4 * 256 + b5) + (b6 * 256 + b7) <
      4294967296 := by omega
    rw [wrapScalarBits_eq_of_lt h1, wrapScalarBits_eq_of_lt h2, wrapScalarBits_eq_of_lt h3,
      nat_ble_eq_false_of_lt h1, nat_ble_eq_false_of_lt h2, nat_ble_eq_false_of_lt h3]
    exact ⟨rfl, rfl, frame8_post_holds b0 b1 b2 b3 b4 b5 b6 b7 _ rfl⟩

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
