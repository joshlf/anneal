import Trusted
import Anneal
import Mir.FuchsiaUsercopy.usercopy_copyin_bracketed
import Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed
import Specs.FuchsiaUsercopy.usercopy_copyin_bracketed
import Proof.FuchsiaUsercopy.hermetic_copy_stub

namespace Proof.FuchsiaUsercopy.usercopy_copyin_bracketed

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 2000000 in
theorem verified : ModularVerificationResult Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed.modularClaim := by
  refine verifyModularContractWithCalleesMirSym
    Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim.callContract
    Mir.FuchsiaUsercopy.usercopy_copyin_bracketed.body
    Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed.defaultCallees
    Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.pre
    Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.post
    25 ?_
  intro args mem h_pre
  obtain ⟨in_range, dest_len, fo, v, h_ir, h_fo, h_dl, h_bound, h_v, h_args, h_mem⟩ := h_pre
  rcases h_args with rfl
  rcases h_mem with rfl
  rcases h_ir with rfl | rfl
  · conv => whnf
    intro retVal mem' h_out
    injection h_out with h_pair
    injection h_pair with h_ret h_mem
    rcases h_ret with rfl
    rcases h_mem with rfl
    refine ⟨rfl, ?_⟩
    intro ir' dl' fo' v' h_args
    injection h_args with h1 ht1
    injection ht1 with h2 _
    injection h1 with hs1
    injection h2 with hs2
    cases hs1; cases hs2
    simp; omega
  · rcases h_v with rfl | rfl
    · -- v = 0 case
      rcases h_dl with h_dl1 | h_dl2
      · contradiction
      · contradiction
    · -- v = 1 case
      conv => whnf
      (repeat' ((conv => whnf); split))
      all_goals (conv => whnf)
      all_goals (try unfold wpMirModularSym wpMirExecModularSym)
      all_goals (try dsimp [advanceStmt, initMachineStateWithMemoryAndCallees, initMachineStateWithMemory, stepMirExecSymTree, stepMirSymTree, evalStmtSymTree, evalTerminatorSymTree, resumeExternalCall, writePlaceValue, Option.getD, Trusted.Sequence.get?, Trusted.Sequence.set?, List.set, List.append, Nat.add, Nat.succ, Nat.zero, emptyMemory] at *; try simp_all; try omega)
      all_goals (
        try exact True.intro
        (
          unfold Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.post
          apply And.intro
          · simp [Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed.defaultCallees, invalidateConflictingBorrows]
          · intro ir_ dl_ fo_ v_ h_args_eq
            injection h_args_eq with h1 ht1
            injection ht1 with h2 ht2
            injection h1 with hs1
            injection h2 with hs2
            cases hs1; cases hs2
            simp_all; omega
        )
      )
/-- Model witness for `hermetic_copy_stub` returning `fault_offset`. -/
def hermeticCopyStubModel (args : List Value) (mem : Memory) : Value × Memory :=
  match args with
  | [ _, .scalar { bits := fo, .. }, _ ] =>
    (.scalar { bits := fo, sizeBytes := 8 }, mem)
  | _ => (.scalar { bits := 0, sizeBytes := 8 }, mem)

/-- End-to-end horizontal linking theorem combining the modular proof of
    `usercopy_copyin_bracketed` with the scoped UB-exception proof of
    `hermetic_copy_stub`. -/
theorem linked_with_ub_exception (fallback : ExternalCallHandler) :
    ((fun args mem =>
      (mirHandledTreeWithCallees
        Mir.FuchsiaUsercopy.usercopy_copyin_bracketed.body
        args mem
        Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed.defaultCallees
        (ubExceptionModelHandler
          Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim
          hermeticCopyStubModel
          fallback)).toPartial) ≤
      MirClosedStatefulContractSpec
        Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.pre
        Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.pre
        Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.post) ∧
    MirStatefulContractHoldsWithSafetyAndCallees
      Mir.FuchsiaUsercopy.hermetic_copy_stub.body
      Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim.callees
      (fun args mem =>
        Specs.FuchsiaUsercopy.hermetic_copy_stub.pre args mem ∧
        Specs.FuchsiaUsercopy.hermetic_copy_stub.strictSafetyPre args mem)
      Specs.FuchsiaUsercopy.hermetic_copy_stub.pre
      Specs.FuchsiaUsercopy.hermetic_copy_stub.post := by
  refine linkUbExceptionCalleeWithCallees
    verified
    Proof.FuchsiaUsercopy.hermetic_copy_stub.verified
    hermeticCopyStubModel
    fallback
    ?_
  intro args mem h_pre _
  rcases h_pre with ⟨count, fo, v, h_fo, _, _, rfl, rfl⟩
  refine ⟨rfl, ?_⟩
  intro c' fo' v' h_args
  injection h_args with h1 ht1
  injection ht1 with h2 _
  injection h1 with hs1
  injection h2 with hs2
  cases hs1; cases hs2
  exact ⟨rfl, h_fo⟩

end Proof.FuchsiaUsercopy.usercopy_copyin_bracketed