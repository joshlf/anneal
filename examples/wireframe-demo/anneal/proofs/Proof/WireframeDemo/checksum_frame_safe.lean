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
open Anneal.MirFuelFree
open Anneal.MirLoops
open Anneal.PureMirExec
open Anneal.FunctionalTranslation
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.WireframeDemo.checksum_frame_safe

/-!
Stateful loop proof for `wireframe_demo::checksum_frame_safe`. The
`while i < 4` loop is proved with `mirNoCallWpConverges_forRangeUp` over the
invariant `checksumLoopInv`; the entry segment (`bb0` to the loop header
`bb1`), every iteration (`bb1` back to `bb1`), and the exit (`bb1` to the
return) are each evaluated by `runCfgToBlock` with target `bb1`, so the proof
states no step counts.
-/

theorem mul_0_2 : Nat.mul 0 2 = 0 := rfl
theorem mul_1_2 : Nat.mul 1 2 = 2 := rfl
theorem mul_2_2 : Nat.mul 2 2 = 4 := rfl
theorem mul_3_2 : Nat.mul 3 2 = 6 := rfl
theorem wrap8_0 : wrapScalarBits 0 18446744073709551616 = 0 := rfl
theorem wrap8_1 : wrapScalarBits 1 18446744073709551616 = 1 := rfl
theorem wrap8_2 : wrapScalarBits 2 18446744073709551616 = 2 := rfl
theorem wrap8_3 : wrapScalarBits 3 18446744073709551616 = 3 := rfl
theorem wrap8_4 : wrapScalarBits 4 18446744073709551616 = 4 := rfl
theorem wrap8_5 : wrapScalarBits 5 18446744073709551616 = 5 := rfl
theorem wrap8_6 : wrapScalarBits 6 18446744073709551616 = 6 := rfl
theorem wrap8_7 : wrapScalarBits 7 18446744073709551616 = 7 := rfl
theorem wrap4_8 : wrapScalarBits 8 4294967296 = 8 := rfl

theorem get?_frame8CallerLocals (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
    get? (frame8CallerLocals b0 b1 b2 b3 b4 b5 b6 b7) frame8SlotIdx =
      some (.init (frame8Value b0 b1 b2 b3 b4 b5 b6 b7)) := rfl

theorem get?Internal_frame8CallerLocals (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
    List.get?Internal (frame8CallerLocals b0 b1 b2 b3 b4 b5 b6 b7) 69 =
      some (.init (frame8Value b0 b1 b2 b3 b4 b5 b6 b7)) := rfl

/-- Total functional model computing `(ret, mem)` for any `&[u8; 8]` frame. -/
def checksumModel (_args : List Value) (mem : Memory) : Value × Memory :=
  match get? mem.callerLocals frame8SlotIdx with
  | .some (.init (.aggregate 0
      [.scalar s0, .scalar s1, .scalar s2, .scalar s3,
       .scalar s4, .scalar s5, .scalar s6, .scalar s7])) =>
    (.scalar ⟨bigEndianWordSum4 s0.bits s1.bits s2.bits s3.bits
      s4.bits s5.bits s6.bits s7.bits, 4⟩, mem)
  | _ => (.scalar ⟨0, 4⟩, mem)

theorem checksumModel_eq_of_callerLocals
    (args : List Value) (mem : Memory) (b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    (h_caller : mem.callerLocals = frame8CallerLocals b0 b1 b2 b3 b4 b5 b6 b7) :
    checksumModel args mem =
      (.scalar ⟨bigEndianWordSum4 b0 b1 b2 b3 b4 b5 b6 b7, 4⟩, mem) := by
  unfold checksumModel; rw [h_caller, get?_frame8CallerLocals]; rfl

/-- Big-endian word read at loop iteration `i ∈ {0, 1, 2, 3}`. -/
def checksumWordAt (b0 b1 b2 b3 b4 b5 b6 b7 i : Nat) : Nat :=
  if i = 0 then b0 * 256 + b1
  else if i = 1 then b2 * 256 + b3
  else if i = 2 then b4 * 256 + b5
  else b6 * 256 + b7

/-- Pure range-loop step function for `forRangeUp 0 4 0`. -/
def checksumWordStep (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) {hi : Nat}
    (i : Nat) (_ : 0 ≤ i) (_ : i < hi) (acc : Nat) : Nat :=
  acc + checksumWordAt b0 b1 b2 b3 b4 b5 b6 b7 i

/-- Closed-form accumulator after `i` loop iterations. -/
def checksumPrefix (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 =>
    checksumPrefix b0 b1 b2 b3 b4 b5 b6 b7 i +
      checksumWordAt b0 b1 b2 b3 b4 b5 b6 b7 i

private theorem checksumPrefix_le {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) :
    ∀ i, checksumPrefix b0 b1 b2 b3 b4 b5 b6 b7 i ≤ i * 65535
  | 0 => Nat.le_refl 0
  | i + 1 => by
    have ih := checksumPrefix_le hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 i
    have hw : checksumWordAt b0 b1 b2 b3 b4 b5 b6 b7 i ≤ 65535 := by
      unfold checksumWordAt
      repeat' split
      all_goals omega
    show checksumPrefix b0 b1 b2 b3 b4 b5 b6 b7 i +
      checksumWordAt b0 b1 b2 b3 b4 b5 b6 b7 i ≤ (i + 1) * 65535
    omega

private theorem checksumPrefix_four (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
    checksumPrefix b0 b1 b2 b3 b4 b5 b6 b7 4 =
      bigEndianWordSum4 b0 b1 b2 b3 b4 b5 b6 b7 := by
  show 0 + (b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5) +
    (b6 * 256 + b7) = _
  unfold bigEndianWordSum4
  omega

/-- The MIR loop's accumulator is the functional `forRangeUp` fold. -/
theorem forRangeUp_checksumWordStep_eq (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
    forRangeUp 0 4 0 (checksumWordStep b0 b1 b2 b3 b4 b5 b6 b7) =
      bigEndianWordSum4 b0 b1 b2 b3 b4 b5 b6 b7 := by
  rw [forRangeUp_induction 0 4 0 _
    (fun i a => a = checksumPrefix b0 b1 b2 b3 b4 b5 b6 b7 i)
    (by decide) rfl (fun _ _ _ _ h => by rw [h]; rfl)]
  exact checksumPrefix_four b0 b1 b2 b3 b4 b5 b6 b7

/-- Machine state at loop header `bb1` with index `_2 = i` and accumulator
`_3 = a`; loop temporaries are uninitialised before the first iteration. -/
def checksumLoopState (mem : Memory) (i a : Nat)
    (v6 v8 v9 v10 v12 v14 v15 v16 v17 v18 v20 v21 v25 v26 v27 : Value) :
    MachineState :=
  let t := fun v : Value => if i = 0 then LocalSlot.uninit else .init v
  { frame := {
      blockIdx := 1
      stmtIdx := 0
      locals := [.uninit, .init (.ptr rootFrame8Ptr 8), .init (.scalar ⟨i, 8⟩),
        .init (.scalar ⟨a, 4⟩), .uninit, .uninit, t v6, .uninit, t v8, t v9,
        t v10, .uninit, t v12, .uninit, t v14, t v15, t v16, t v17, t v18,
        .uninit, t v20, t v21, .uninit, .uninit, .uninit, t v25, t v26, t v27] }
    memory := mem }

/-- Loop invariant at `bb1` for `mirNoCallWpConverges_forRangeUp`. -/
def checksumLoopInv (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) (mem : Memory)
    (i : Nat) (a : Nat) (s : MachineState) : Prop :=
  i ≤ 4 ∧
  a = checksumPrefix b0 b1 b2 b3 b4 b5 b6 b7 i ∧
  ∃ v6 v8 v9 v10 v12 v14 v15 v16 v17 v18 v20 v21 v25 v26 v27,
    s = checksumLoopState mem i a
      v6 v8 v9 v10 v12 v14 v15 v16 v17 v18 v20 v21 v25 v26 v27

theorem frame8_post_holds (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) (mem₀ : Memory)
    (h_caller : mem₀.callerLocals = frame8CallerLocals b0 b1 b2 b3 b4 b5 b6 b7) :
    Obligations.WireframeDemo.checksum_frame_safe.statefulClaim.post
      [.ptr rootFrame8Ptr 8] mem₀
      (.scalar ⟨bigEndianWordSum4 b0 b1 b2 b3 b4 b5 b6 b7, 4⟩) mem₀ := by
  refine ⟨trivial, rfl, ?_⟩
  intro b0' b1' b2' b3' b4' b5' b6' b7' _ h_caller_eq
  have h_slot := congrArg (List.get?Internal · 69) (h_caller.symm.trans h_caller_eq)
  simp [get?Internal_frame8CallerLocals, frame8Value] at h_slot
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h_slot
  rfl

/-- Fuel-free call-forbidding convergence of `checksum_frame_safe` to
`checksumModel`, shared with the `checksum_frame_fast` equivalence proof. -/
theorem safe_noCallWpConverges
    (args : List Value) (mem : Memory)
    (h_pre : Obligations.WireframeDemo.checksum_frame_safe.statefulClaim.pre args mem) :
    MirNoCallWpConverges Mir.WireframeDemo.checksum_frame_safe.body
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        Mir.WireframeDemo.checksum_frame_safe.body args mem
        Obligations.WireframeDemo.checksum_frame_safe.defaultCallees)
      (fun out =>
        out = .normal (checksumModel args mem) ∧
        Obligations.WireframeDemo.checksum_frame_safe.statefulClaim.post args mem
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
  refine Anneal.MirFuelFree.MirNoCallWpConverges.bind
    (mirStepsConverges_of_runCfgToBlock (target := 1)
      Mir.WireframeDemo.checksum_frame_safe.body
      (checksumLoopInv b0 b1 b2 b3 b4 b5 b6 b7 mem₀ 0 0) _ rfl _ ?entry)
    (fun s₀ h_init => mirNoCallWpConverges_forRangeUp 0 4 0
      (checksumWordStep b0 b1 b2 b3 b4 b5 b6 b7) _
      (checksumLoopInv b0 b1 b2 b3 b4 b5 b6 b7 mem₀) s₀ _ h_init ?iter ?exit)
  case' iter =>
    rintro i h_i_le h_i_lt a s ⟨_, h_a,
      v6, v8, v9, v10, v12, v14, v15, v16, v17, v18, v20, v21, v25, v26, v27, rfl⟩
    have h_ab : a ≤ 196605 := by
      have := checksumPrefix_le hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 i
      omega
    refine mirStepsConverges_of_runCfgToBlock (target := 1) _ _ _ rfl _ ?_
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  case' exit =>
    rintro i a s h_ge ⟨h_le, h_a,
      v6, v8, v9, v10, v12, v14, v15, v16, v17, v18, v20, v21, v25, v26, v27, rfl⟩
    obtain rfl : i = 4 := by omega
    rw [checksumPrefix_four] at h_a
    subst h_a
    refine mirNoCallWpConverges_of_runCfgToBlock (target := 1) _ _ rfl _ ?_
  all_goals -- evaluate every segment (entry, iterations, exit) to `bb1`
    dsimp only [
      cfgStepsWP, cfgStateWP, checksumLoopState, mem₀,
      runCfgToBlock, runCfgUntilAux, cfgAtBlock,
      Obligations.WireframeDemo.checksum_frame_safe.statefulClaim,
      Trusted.VerificationResult.initMachineStateWithMemoryAndCallees,
      Obligations.WireframeDemo.checksum_frame_safe.defaultCallees,
      Mir.WireframeDemo.checksum_frame_safe.layouts,
      Mir.WireframeDemo.checksum_frame_safe.body,
      lookupBlock, stepCfgState, dispatchBlockCfg, stepNodeToCfg,
      evalTerminatorCfg, evalStmtFast, finishAssignStmtNodeFast, advanceStmt,
      evalRvalueFast, evalOperandFast, evalConstValue,
      evalScalarBinOp, evalUnaryNot,
      operandIsSigned, operandTy, sharedBorrowPerm, rigidTyIsFreeze, stringEq,
      tyIsFreeze, placeTy, resolveProjectedTy, pointeeTyOf, elemTyOf, tyIsSigned,
      intCastTargetBytes, shiftLeftBits, shiftRightUnsignedBits, scalarPow2_eight,
      scalarModulus_1, scalarModulus_2, scalarModulus_4, scalarModulus_8,
      mul_1_8, mul_2_8, mul_4_8, mul_8_8, mul_0_2, mul_1_2, mul_2_2, mul_3_2,
      wrap8_0, wrap8_1, wrap8_2, wrap8_3, wrap8_4, wrap8_5, wrap8_6,
      wrap8_7, wrap4_8,
      get?_frame8CallerLocals, get?Internal_frame8CallerLocals,
      lookupSwitchTarget, applyUnwindAction,
      MirStepNode.step, MirStepNode.retNormal,
      rootFrame8Ptr, frame8Value, sharedFrame8Borrow, frame8SlotIdx,
      readProjectedValue_nil, readProjectedValue_field, readProjectedValue_index,
      ProvenancePtr.tag, lookupBorrow, appendProjections,
      stripTransparentProjections, projectionsOverlap, projectionsOverlapAux,
      borrowEntryOverlapsWrite, byteRangesOverlapBool, borrowEntryWriteConflicts,
      hasProtectedWriteConflict, isBorrowProtected, natListContainsBool,
      invalidateConflictingBorrows, invalidateConflictingBorrowsAtProj,
      updateBorrowPerm, updateBorrowPermAtProj, freezeDerefReadBorrowsAt,
      freezeTreeBorrowsOnReadAtProj, updateBorrowPermOnReadAtProj,
      isBorrowDescendantOrSelf, isBorrowDescendantOrSelfAux, boolToScalar,
      initMachineStateWithMemory, initLocals, initLocalsAux,
      GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal,
      HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
      List.replicate, List.append, List.length, List.set, List.map, Option.getD,
      get?, set?, length, Nat.add, Nat.mod, Nat.ble, Nat.beq, Bool.and, Bool.or,
      Bool.not, ite, dite, decide, Nat.decLt, Nat.decLe, Nat.decEq,
      instDecidableEqNat, Bool.decEq, instDecidableEqBool, BEq.beq,
      instBEqOfDecidableEq]
  case entry =>
    exact ⟨rfl, by omega, rfl, .aggregate 0 [], .aggregate 0 [],
      .aggregate 0 [], .aggregate 0 [], .aggregate 0 [], .aggregate 0 [],
      .aggregate 0 [], .aggregate 0 [], .aggregate 0 [], .aggregate 0 [],
      .aggregate 0 [], .aggregate 0 [], .aggregate 0 [], .aggregate 0 [],
      .aggregate 0 [], rfl⟩
  case exit => exact ⟨rfl, rfl, frame8_post_holds b0 b1 b2 b3 b4 b5 b6 b7 mem₀ rfl⟩
  all_goals -- iterations: `omega` discharges the symbolic overflow checks
    simp (disch := omega) only [Nat.add_eq, Nat.mul_eq, wrapScalarBits_eq_of_lt,
      bitwiseOrBits_32_mul256_add, nat_ble_eq_false_of_lt]
    exact ⟨rfl, by omega, by rw [h_a]; rfl,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- Universal stateful verification certificate for `checksum_frame_safe`. -/
theorem verified :
    StatefulVerificationResult
      Obligations.WireframeDemo.checksum_frame_safe.statefulClaim :=
  verifyStatefulMirNoPanic_of_wpConverges _ fun args mem h_pre =>
    (MirWpConverges.of_noCall (safe_noCallWpConverges args mem h_pre)).mono
      fun _ ⟨h_out, h_post⟩ => h_out ▸ h_post

end Proof.WireframeDemo.checksum_frame_safe
