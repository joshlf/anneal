import sys

with open('examples/fuchsia-usercopy/anneal/proofs/Proof/FuchsiaUsercopy/hermetic_copy_stub.lean', 'r') as f:
    content = f.read()

prefix = content[:content.find("  · intro args mem h_pre\n    rcases h_pre")]
new_suffix = """  · intro args mem h_pre
    rcases h_pre with ⟨count, fo, v, h_fo, h_c, hv, rfl, rfl⟩
    have hv_bits : v = 1 := hv
    subst hv_bits
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
"""

with open('examples/fuchsia-usercopy/anneal/proofs/Proof/FuchsiaUsercopy/hermetic_copy_stub.lean', 'w') as f:
    f.write(prefix + new_suffix)
