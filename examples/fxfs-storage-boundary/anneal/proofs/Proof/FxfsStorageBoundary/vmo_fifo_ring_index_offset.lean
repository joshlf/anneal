import Trusted
import Anneal
import Mir.FxfsStorageBoundary.vmo_fifo_ring_index_offset
import Obligations.FxfsStorageBoundary.vmo_fifo_ring_index_offset
import Specs.FxfsStorageBoundary.vmo_fifo_ring_index_offset

namespace Proof.FxfsStorageBoundary.vmo_fifo_ring_index_offset

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.vmo_fifo_ring_index_offset.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FxfsStorageBoundary.vmo_fifo_ring_index_offset.statefulClaim 100 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨raw, cap, es, h_cap_pos, h_raw, h_cap, h_es, h_bound, rfl⟩, rfl⟩
  have h_nat_mod : ∀ a b : Nat, a.mod b = a % b := fun _ _ => rfl
  have h_rem_lt_cap : raw % cap < cap := Nat.mod_lt raw h_cap_pos
  have h_rem_lt : raw % cap < 18446744073709551616 := Nat.lt_trans h_rem_lt_cap h_cap
  have h_mul_le : (raw % cap) * es ≤ cap * es := Nat.mul_le_mul_right es (Nat.le_of_lt h_rem_lt_cap)
  have h_mul_lt : (raw % cap) * es < 18446744073709551616 := Nat.lt_of_le_of_lt h_mul_le h_bound
  (repeat' ((conv => whnf); split))
  all_goals (conv => whnf)
  all_goals (try dsimp at *; try simp_all; try omega)
  all_goals (try rw [Nat.mod_eq_of_lt h_rem_lt] at *; try omega)

end Proof.FxfsStorageBoundary.vmo_fifo_ring_index_offset
