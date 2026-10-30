import Trusted
import Anneal
import Mir.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
import Obligations.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
import Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
import Proof.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked

namespace Proof.FxfsStorageBoundary.data_object_handle_verify_data_unfixed

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

private theorem ble_eq_false_of_lt {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases h_b : Nat.ble a b
  · rfl
  · have := Nat.le_of_ble_eq_true h_b
    omega

set_option maxHeartbeats 2000000 in
theorem verified : ModularVerificationResult Obligations.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.modularClaim := by
  refine verifyModularContractMirSym
    Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.ubExceptionClaim.callContract
    Mir.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.body
    Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.pre
    Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.post
    30 ?_
  intro args mem h_pre
  rcases h_pre with ⟨vmo_size, offset, len, t, h_vmo, h_off, h_len, h_t, rfl, rfl⟩
  conv => whnf
  split
  · next h_ble1 =>
    have h_le1 : offset ≤ vmo_size := Nat.le_of_ble_eq_true h_ble1
    conv => whnf
    split
    · next h_ble2 =>
      conv => whnf
      split
      · next h_ble3 =>
        have h_sub_lt : vmo_size - offset < 18446744073709551616 := by omega
        have h_ble3' : Nat.ble len (vmo_size - offset) = true := by
          dsimp [wrapScalarBits, scalarModulus, Nat.sub] at h_ble3
          rw [ble_eq_false_of_lt h_sub_lt] at h_ble3
          exact h_ble3
        have h_le2 : len ≤ vmo_size - offset := Nat.le_of_ble_eq_true h_ble3'
        conv => whnf
        refine ⟨⟨rfl, vmo_size, offset, len, t, h_le1, h_le2, h_vmo, h_t, rfl, rfl⟩, ?_⟩
        rintro _ ⟨retVal, mem', rfl, h_mem', h_ret_fn⟩
        have h_rv := h_ret_fn vmo_size offset len t rfl
        have h_mem_empty : mem' = emptyMemory := h_mem'
        clear h_ret_fn h_mem'
        subst h_rv h_mem_empty
        conv => whnf
        intro retVal' mem'' h_out
        injection h_out with h_pair
        injection h_pair with h_ret h_mem
        subst h_ret h_mem
        refine ⟨rfl, ?_⟩
        intro vs' off' l' t' h_args
        injection h_args with h1 ht1
        injection ht1 with h2 ht2
        injection ht2 with h3 _
        injection h1 with hs1
        injection h2 with hs2
        injection h3 with hs3
        cases hs1; cases hs2; cases hs3
        have h_ok : offset ≤ vmo_size ∧ len ≤ vmo_size - offset := ⟨h_le1, h_le2⟩
        simp [h_ok]
      · next h_nble3 =>
        have h_sub_lt : vmo_size - offset < 18446744073709551616 := by omega
        have h_nble3' : Nat.ble len (vmo_size - offset) = false := by
          dsimp [wrapScalarBits, scalarModulus, Nat.sub] at h_nble3
          rw [ble_eq_false_of_lt h_sub_lt] at h_nble3
          exact h_nble3
        have h_gt2 : ¬ len ≤ vmo_size - offset :=
          fun h_le => by rw [Nat.ble_eq_true_of_le h_le] at h_nble3'; contradiction
        conv => whnf
        intro retVal mem' h_out
        injection h_out with h_pair
        injection h_pair with h_ret h_mem
        subst h_ret h_mem
        refine ⟨rfl, ?_⟩
        intro vs' off' l' t' h_args
        injection h_args with h1 ht1
        injection ht1 with h2 ht2
        injection ht2 with h3 _
        injection h1 with hs1
        injection h2 with hs2
        injection h3 with hs3
        cases hs1; cases hs2; cases hs3
        have h_not : ¬ (offset ≤ vmo_size ∧ len ≤ vmo_size - offset) := by omega
        simp [h_not]
    · intro _ _ h; nomatch h
  · next h_nble1 =>
    have h_gt1 : ¬ offset ≤ vmo_size :=
      fun h_le => by
        have h_tr : Nat.ble offset vmo_size = true := Nat.ble_eq_true_of_le h_le
        rw [h_tr] at h_nble1; contradiction
    conv => whnf
    intro retVal mem' h_out
    injection h_out with h_pair
    injection h_pair with h_ret h_mem
    subst h_ret h_mem
    refine ⟨rfl, ?_⟩
    intro vs' off' l' t' h_args
    injection h_args with h1 ht1
    injection ht1 with h2 ht2
    injection ht2 with h3 _
    injection h1 with hs1
    injection h2 with hs2
    injection h3 with hs3
    cases hs1; cases hs2; cases hs3
    have h_not : ¬ (offset ≤ vmo_size ∧ len ≤ vmo_size - offset) := by omega
    simp [h_not]

/-- Model witness for `vmo_buffer_as_ref_unchecked` returning `offset + len`. -/
def vmoSliceEndModel (args : List Value) (mem : Memory) : Value × Memory :=
  match args with
  | [ _, .scalar { bits := offset, .. }, .scalar { bits := len, .. }, _ ] =>
    (.scalar { bits := offset + len, sizeBytes := 8 }, mem)
  | _ => (.scalar { bits := 0, sizeBytes := 8 }, mem)

/-- End-to-end horizontal linking theorem combining the modular proof of
    `data_object_handle_verify_data_unfixed` with the scoped UB-exception proof of
    `vmo_buffer_as_ref_unchecked`. -/
theorem linked_with_ub_exception (fallback : ExternalCallHandler) :
    ((fun args mem =>
      (mirHandledTree
        Mir.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.body
        args mem
        (ubExceptionModelHandler
          Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.ubExceptionClaim
          vmoSliceEndModel
          fallback)).toPartial) ≤
      MirClosedStatefulContractSpec
        Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.pre
        Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.pre
        Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed.post) ∧
    MirStatefulContractHoldsWithSafety
      Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.body
      (fun args mem =>
        Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.pre args mem ∧
        Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.strictSafetyPre args mem)
      Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.pre
      Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.post := by
  refine linkUbExceptionCallee
    verified
    Proof.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.verified
    vmoSliceEndModel
    fallback
    ?_
  intro args mem h_pre _
  rcases h_pre with ⟨vmo_size, offset, len, t, _, _, _, _, rfl, rfl⟩
  refine ⟨rfl, ?_⟩
  intro vs' off' l' t' h_args
  injection h_args with h1 ht1
  injection ht1 with h2 ht2
  injection ht2 with h3 _
  injection h2 with hs2
  injection h3 with hs3
  cases hs2; cases hs3
  rfl

end Proof.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
