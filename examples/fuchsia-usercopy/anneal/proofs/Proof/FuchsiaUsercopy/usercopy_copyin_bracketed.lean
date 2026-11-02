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
  refine verifyModularContractMirSym
    Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim.callContract
    Mir.FuchsiaUsercopy.usercopy_copyin_bracketed.body
    Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.pre
    Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.post
    25 ?_
  intro args mem h_pre
  rcases h_pre with ⟨in_range, dest_len, fo, v, h_ir, h_fo, h_dl, h_v, rfl, rfl⟩
  rcases h_ir with rfl | rfl
  · conv => whnf
    intro retVal mem' h_out
    injection h_out with h_pair
    injection h_pair with h_ret h_mem
    subst h_ret h_mem
    refine ⟨rfl, ?_⟩
    intro ir' dl' fo' v' h_args
    injection h_args with h1 ht1
    injection ht1 with h2 _
    injection h1 with hs1
    injection h2 with hs2
    cases hs1; cases hs2
    simp; omega
  · conv => whnf
    refine ⟨⟨rfl, dest_len, fo, v, h_fo, h_dl, h_v, rfl, rfl⟩, ?_⟩
    rintro _ ⟨retVal, mem', rfl, h_mem', h_ret_fn⟩
    obtain ⟨h_rv, _⟩ := h_ret_fn dest_len fo v rfl
    have h_mem_empty : mem' = emptyMemory := h_mem'
    clear h_ret_fn h_mem'
    subst h_rv h_mem_empty
    conv => whnf
    split
    · next h_ble_fo =>
      conv => whnf
      intro retVal' mem'' h_out
      injection h_out with h_pair
      injection h_pair with h_ret h_mem
      subst h_ret h_mem
      refine ⟨rfl, ?_⟩
      intro ir' dl' fo' v' h_args
      injection h_args with h1 ht1
      injection ht1 with h2 ht2
      injection ht2 with h3 _
      injection h1 with hs1
      injection h2 with hs2
      injection h3 with hs3
      cases hs1; cases hs2; cases hs3
      simp
      congr 1; congr 1; congr 1; congr 1; omega
    · next h_nble_fo =>
      have h_tr : Nat.ble fo dest_len = true := Nat.ble_eq_true_of_le h_fo
      rw [h_tr] at h_nble_fo; contradiction

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
      (mirHandledTree
        Mir.FuchsiaUsercopy.usercopy_copyin_bracketed.body
        args mem
        (ubExceptionModelHandler
          Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim
          hermeticCopyStubModel
          fallback)).toPartial) ≤
      MirClosedStatefulContractSpec
        Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.pre
        Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.pre
        Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.post) ∧
    MirStatefulContractHoldsWithSafety
      Mir.FuchsiaUsercopy.hermetic_copy_stub.body
      (fun args mem =>
        Specs.FuchsiaUsercopy.hermetic_copy_stub.pre args mem ∧
        Specs.FuchsiaUsercopy.hermetic_copy_stub.strictSafetyPre args mem)
      Specs.FuchsiaUsercopy.hermetic_copy_stub.pre
      Specs.FuchsiaUsercopy.hermetic_copy_stub.post := by
  refine linkUbExceptionCallee
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
