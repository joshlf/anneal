import Trusted
import Anneal
import Mir.FuchsiaUsercopy.hermetic_copy_stub
import Obligations.FuchsiaUsercopy.hermetic_copy_stub
import Specs.FuchsiaUsercopy.hermetic_copy_stub

namespace Proof.FuchsiaUsercopy.hermetic_copy_stub

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

@[simp]
theorem initMachineStateWithMemory_eq (body args mem) :
  initMachineStateWithMemory body args mem =
  { frame := { blockIdx := 0, stmtIdx := 0, locals := initLocals body args }, memory := mem } := rfl

@[simp]
theorem body_localDecls_eq : Mir.FuchsiaUsercopy.hermetic_copy_stub.body.localDecls = 
  [{ mutability := Trusted.Rustc.V2026_06_01.MirAst.Mutability.mut,
     ty := { kind := Trusted.Rustc.V2026_06_01.MirAst.RigidTy.uint Trusted.Rustc.V2026_06_01.MirAst.UintTy.usize, layoutIdx := 0 },
     debugName := none },
   { mutability := Trusted.Rustc.V2026_06_01.MirAst.Mutability.not,
     ty := { kind := Trusted.Rustc.V2026_06_01.MirAst.RigidTy.uint Trusted.Rustc.V2026_06_01.MirAst.UintTy.usize, layoutIdx := 0 },
     debugName := some "count" },
   { mutability := Trusted.Rustc.V2026_06_01.MirAst.Mutability.not,
     ty := { kind := Trusted.Rustc.V2026_06_01.MirAst.RigidTy.uint Trusted.Rustc.V2026_06_01.MirAst.UintTy.usize, layoutIdx := 0 },
     debugName := some "fault_offset" },
   { mutability := Trusted.Rustc.V2026_06_01.MirAst.Mutability.not,
     ty := { kind := Trusted.Rustc.V2026_06_01.MirAst.RigidTy.bool, layoutIdx := 1 },
     debugName := some "normal_mode_dest_valid" },
   { mutability := Trusted.Rustc.V2026_06_01.MirAst.Mutability.not,
     ty := { kind := Trusted.Rustc.V2026_06_01.MirAst.RigidTy.never, layoutIdx := 2 }, debugName := none }] := rfl

@[simp]
theorem initLocals_hermetic_copy_stub (count fo v : Nat) :
  initLocals Mir.FuchsiaUsercopy.hermetic_copy_stub.body
    [Value.scalar { bits := count, sizeBytes := 8 },
     Value.scalar { bits := fo, sizeBytes := 8 },
     Value.scalar { bits := v, sizeBytes := 1 }] =
  [LocalSlot.uninit,
   LocalSlot.init (Value.scalar { bits := count, sizeBytes := 8 }),
   LocalSlot.init (Value.scalar { bits := fo, sizeBytes := 8 }),
   LocalSlot.init (Value.scalar { bits := v, sizeBytes := 1 }),
   LocalSlot.dead] := rfl

@[simp]
theorem advanceStmt_eq (s : MachineState) (locals' : List LocalSlot) (mem' : Memory) :
  advanceStmt s locals' mem' = { frame := { blockIdx := s.frame.blockIdx, stmtIdx := s.frame.stmtIdx + 1, locals := locals' }, memory := mem' } := rfl

@[simp]
theorem claim_body_eq : Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim.body = Mir.FuchsiaUsercopy.hermetic_copy_stub.body := rfl

@[simp]
theorem claim_callees_eq : Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim.callees = [Mir.Core.hint_unreachable_unchecked.body] := rfl

@[simp]
theorem initLocals_unreachable_unchecked_body_eq :
  initLocals Mir.Core.hint_unreachable_unchecked.body [] = [LocalSlot.uninit, LocalSlot.dead] := rfl

@[simp]
theorem initMachineStateWithMemoryAndCallees_eq (body args mem c cs) :
  initMachineStateWithMemoryAndCallees body args mem (c :: cs) =
  initMachineStateWithMemory body args { mem with callees := c :: cs, traitImpls := body.traitImpls } := rfl

@[simp]
theorem pushDivergingCalleeFrame_eq (s callerBody locals destination unwind calleeBody args) :
  pushDivergingCalleeFrame s callerBody locals destination unwind calleeBody args =
  { frame := { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody args },
    memory :=
      { s.memory with
        callStack := { callerBody := callerBody, frame := { s.frame with locals := locals }, destination := destination, calleeProtectors := s.memory.activeProtectors, returnUnwind := unwind, isDiverging := true } :: s.memory.callStack,
        activeCallee := some calleeBody } } := rfl

set_option maxHeartbeats 10000000 in
theorem verified : UbExceptionVerificationResult Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim := by
  refine verifyUbExceptionMirSym
    Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim 20 ?_ ?_
  · intro args mem h_pre h_strict
    rcases h_pre with ⟨count, fo, v, h_fo, h_c, _, rfl, rfl⟩
    rcases h_strict with ⟨_, _, h_eq⟩
    have hv_bits : v = 1 := by
      injection h_eq with _ ht1
      injection ht1 with _ ht2
      injection ht2 with hv_head _
      injection hv_head with hv_sc
      injection hv_sc with hv_b _
    subst hv_bits
    dsimp [claim_callees_eq, claim_body_eq, initMachineStateWithMemoryAndCallees_eq] at *
    (repeat' ((conv => whnf); split))
    all_goals (conv => whnf)
    all_goals (try dsimp [Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaimFor, Obligations.FuchsiaUsercopy.hermetic_copy_stub.sigPost, ItemSpec.post, Trusted.VerificationResult.invalidateConflictingBorrows, Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim, emptyMemory] at *)
    all_goals (try dsimp at *; try simp_all; try omega)
    all_goals (
      try exact True.intro
      try (
        refine ⟨rfl, ?_⟩
        intro c' fo' v' h_args
        injection h_args with h1 ht1
        injection ht1 with h2 _
        injection h1 with hs1
        injection h2 with hs2
        cases hs1; cases hs2
        exact ⟨rfl, h_fo⟩
      )
    )
  · intro args mem h_pre
    rcases h_pre with ⟨count, fo, v, h_fo, h_c, h_v, rfl, rfl⟩
    rcases h_v with rfl | rfl
    · -- v = 0 (UB path, calls unreachable_unchecked)
      dsimp [claim_callees_eq, claim_body_eq, initMachineStateWithMemoryAndCallees_eq] at *
      (repeat' ((conv => whnf); split))
      all_goals (conv => whnf)
      all_goals (try dsimp at *; try simp_all; try omega)
      intro ans
      cases ans
      · rename_i val memAfter
        intro h_call
        (repeat' ((conv => whnf); split))
        all_goals (conv => whnf)
        all_goals (try dsimp [callAnsPreserved, callFrameAndTraitsPreserved, callFramePreserved] at *)
        all_goals (
            rcases h_call with ⟨⟨h_callees, h_callStack, h_activeCallee, h_activeProtectors, fresh, h_fnPtrs⟩, h_traitImpls⟩
            cases memAfter
            dsimp at h_activeCallee
            subst h_activeCallee
        )
        all_goals (try dsimp [Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaimFor, Obligations.FuchsiaUsercopy.hermetic_copy_stub.sigPost, ItemSpec.post, Trusted.VerificationResult.invalidateConflictingBorrows, Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim, emptyMemory] at *)
        all_goals (try (rename_i h_eqs; rcases h_eqs with ⟨h_callees, h_activeCallee, h_borrows, h_traits⟩; try rw [h_activeCallee, h_borrows, h_callees, h_traits] at *))
        all_goals (try simp_all [checkCallFrameAndTraitsPreserved, resumeExternalCall])
        all_goals (try unfold wpMirUbWaivedSym)
        all_goals (try unfold wpMirExecUbWaivedSym)
        all_goals (try dsimp [claim_body_eq, claim_callees_eq, advanceStmt_eq, initMachineStateWithMemoryAndCallees_eq, initMachineStateWithMemory_eq, initLocals_hermetic_copy_stub, pushDivergingCalleeFrame_eq, stepMirExecSymTree, resumeExternalCall, writePlaceValue, evalSymNodeTreeUbWaived, isWaivedUbFailReq, evalNodeUbWaivedWP, initMachineStateWithMemoryAndCallees, resumeExternalDivergingCall, ActiveCalleeCtx.init, ActiveCalleeCtx.initMem, Option.getD, Trusted.Sequence.get?, Trusted.Sequence.set?, List.set, List.append, Nat.add, Nat.succ, Nat.zero, stepMirSymTree, evalStmtSymTree, evalTerminatorSymTree] at *)
        (repeat' ((conv => whnf); split))
        all_goals (try (rename_i h_eqs; rcases h_eqs with ⟨h_callees, h_activeCallee, h_borrows, h_traits⟩; try rw [h_activeCallee, h_borrows, h_callees, h_traits] at *))
        all_goals (try simp_all)
        all_goals (
          try exact True.intro
          try (intro _ _ h_absurd; contradiction)
        )
      · rename_i memAfter
        intro h_call
        (repeat' ((conv => whnf); split))
        all_goals (conv => whnf)
        all_goals (try dsimp [callAnsPreserved, callFrameAndTraitsPreserved, callFramePreserved] at *)
        all_goals (
            rcases h_call with ⟨⟨h_callees, h_callStack, h_activeCallee, h_activeProtectors, fresh, h_fnPtrs⟩, h_traitImpls⟩
            cases memAfter
            dsimp at h_activeCallee
            subst h_activeCallee
        )
        all_goals (try dsimp [Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaimFor, Obligations.FuchsiaUsercopy.hermetic_copy_stub.sigPost, ItemSpec.post, Trusted.VerificationResult.invalidateConflictingBorrows, Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim, emptyMemory] at *)
        all_goals (try (rename_i h_eqs; rcases h_eqs with ⟨h_callees, h_activeCallee, h_borrows, h_traits⟩; try rw [h_activeCallee, h_borrows, h_callees, h_traits] at *))
        all_goals (try simp_all [checkCallFrameAndTraitsPreserved, resumeExternalCall])
        all_goals (try unfold wpMirUbWaivedSym)
        all_goals (try unfold wpMirExecUbWaivedSym)
        all_goals (try dsimp [claim_body_eq, claim_callees_eq, advanceStmt_eq, initMachineStateWithMemoryAndCallees_eq, initMachineStateWithMemory_eq, initLocals_hermetic_copy_stub, pushDivergingCalleeFrame_eq, stepMirExecSymTree, resumeExternalCall, writePlaceValue, evalSymNodeTreeUbWaived, isWaivedUbFailReq, evalNodeUbWaivedWP, initMachineStateWithMemoryAndCallees, resumeExternalDivergingCall, ActiveCalleeCtx.init, ActiveCalleeCtx.initMem, Option.getD, Trusted.Sequence.get?, Trusted.Sequence.set?, List.set, List.append, Nat.add, Nat.succ, Nat.zero, stepMirSymTree, evalStmtSymTree, evalTerminatorSymTree] at *)
        (repeat' ((conv => whnf); split))
        all_goals (try (rename_i h_eqs; rcases h_eqs with ⟨h_callees, h_activeCallee, h_borrows, h_traits⟩; try rw [h_activeCallee, h_borrows, h_callees, h_traits] at *))
        all_goals (try simp_all)
        all_goals (
          try exact True.intro
          try (intro _ _ h_absurd; contradiction)
        )
      · intro h_call
        (repeat' ((conv => whnf); split))
        all_goals (conv => whnf)
        all_goals (try dsimp [callAnsPreserved, callFrameAndTraitsPreserved, callFramePreserved] at *)
        all_goals (try dsimp [Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaimFor, Obligations.FuchsiaUsercopy.hermetic_copy_stub.sigPost, ItemSpec.post, Trusted.VerificationResult.invalidateConflictingBorrows, Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim, emptyMemory] at *)
        all_goals (try (rename_i h_eqs; rcases h_eqs with ⟨h_callees, h_activeCallee, h_borrows, h_traits⟩; try rw [h_activeCallee, h_borrows, h_callees, h_traits] at *))
        all_goals (try simp_all [checkCallFrameAndTraitsPreserved, resumeExternalCall])
        all_goals (try unfold wpMirUbWaivedSym)
        all_goals (try unfold wpMirExecUbWaivedSym)
        all_goals (try dsimp [claim_body_eq, claim_callees_eq, advanceStmt_eq, initMachineStateWithMemoryAndCallees_eq, initMachineStateWithMemory_eq, initLocals_hermetic_copy_stub, pushDivergingCalleeFrame_eq, stepMirExecSymTree, resumeExternalCall, writePlaceValue, evalSymNodeTreeUbWaived, isWaivedUbFailReq, evalNodeUbWaivedWP, initMachineStateWithMemoryAndCallees, resumeExternalDivergingCall, ActiveCalleeCtx.init, ActiveCalleeCtx.initMem, Option.getD, Trusted.Sequence.get?, Trusted.Sequence.set?, List.set, List.append, Nat.add, Nat.succ, Nat.zero, stepMirSymTree, evalStmtSymTree, evalTerminatorSymTree] at *)
        (repeat' ((conv => whnf); split))
        all_goals (try (rename_i h_eqs; rcases h_eqs with ⟨h_callees, h_activeCallee, h_borrows, h_traits⟩; try rw [h_activeCallee, h_borrows, h_callees, h_traits] at *))
        all_goals (try simp_all)
        all_goals (
          try exact True.intro
          try (intro _ _ h_absurd; contradiction)
        )
    · -- v = 1 (normal path, no external calls)
      dsimp [claim_callees_eq, claim_body_eq, initMachineStateWithMemoryAndCallees_eq] at *
      (repeat' ((conv => whnf); split))
      all_goals (conv => whnf)
      all_goals (try dsimp [Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaimFor, Obligations.FuchsiaUsercopy.hermetic_copy_stub.sigPost, ItemSpec.post, Trusted.VerificationResult.invalidateConflictingBorrows, Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim, emptyMemory] at *)
      all_goals (try unfold wpMirUbWaivedSym wpMirExecUbWaivedSym)
      
      all_goals (try dsimp [claim_body_eq, claim_callees_eq, advanceStmt_eq, initMachineStateWithMemoryAndCallees_eq, initMachineStateWithMemory_eq, initLocals_hermetic_copy_stub, pushDivergingCalleeFrame_eq, stepMirExecSymTree, stepMirSymTree, evalStmtSymTree, evalTerminatorSymTree, resumeExternalCall, writePlaceValue, evalSymNodeTreeUbWaived, isWaivedUbFailReq, evalNodeUbWaivedWP, initMachineStateWithMemoryAndCallees, resumeExternalDivergingCall, ActiveCalleeCtx.init, ActiveCalleeCtx.initMem, Option.getD, Trusted.Sequence.get?, Trusted.Sequence.set?, List.set, List.append, Nat.add, Nat.succ, Nat.zero] at *; try simp_all; try omega)
      all_goals (
        try exact True.intro
        try (
          refine ⟨rfl, ?_⟩
          intro c' fo' v' h_args
          injection h_args with h1 ht1
          injection ht1 with h2 _
          injection h1 with hs1
          injection h2 with hs2
          cases hs1; cases hs2
          exact ⟨rfl, h_fo⟩
        )
      )

end Proof.FuchsiaUsercopy.hermetic_copy_stub
