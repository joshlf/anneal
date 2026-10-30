import Trusted
import Anneal
import Mir.FxfsStorageBoundary.zerocopy_check_slice_len
import Obligations.FxfsStorageBoundary.zerocopy_check_slice_len
import Specs.FxfsStorageBoundary.zerocopy_check_slice_len

namespace Proof.FxfsStorageBoundary.zerocopy_check_slice_len

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.zerocopy_check_slice_len.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FxfsStorageBoundary.zerocopy_check_slice_len.statefulClaim 100 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨bl, es, h_es_pos, h_bl, h_es, rfl⟩, rfl⟩
  have h_nat_mod : ∀ a b : Nat, a.mod b = a % b := fun _ _ => rfl
  have h_nat_div : ∀ a b : Nat, a.div b = a / b := fun _ _ => rfl
  have h_rem_le : bl % es ≤ bl := Nat.mod_le bl es
  have h_rem_lt : bl % es < 18446744073709551616 := Nat.lt_of_le_of_lt h_rem_le h_bl
  have h_sub_le : bl - (bl % es) ≤ bl := Nat.sub_le bl (bl % es)
  have h_sub_lt : bl - (bl % es) < 18446744073709551616 := Nat.lt_of_le_of_lt h_sub_le h_bl
  have h_div_le : (bl - (bl % es)) / es ≤ bl - (bl % es) := Nat.div_le_self (bl - (bl % es)) es
  have h_div_lt : (bl - (bl % es)) / es < 18446744073709551616 := Nat.lt_of_le_of_lt h_div_le h_sub_lt
  (repeat' ((conv => whnf); split))
  all_goals (conv => whnf)
  all_goals (try dsimp at *; try simp_all; try omega)
  all_goals (try rw [Nat.mod_eq_of_lt h_rem_lt] at *; try rw [Nat.mod_eq_of_lt h_div_lt] at *; try omega)

end Proof.FxfsStorageBoundary.zerocopy_check_slice_len
