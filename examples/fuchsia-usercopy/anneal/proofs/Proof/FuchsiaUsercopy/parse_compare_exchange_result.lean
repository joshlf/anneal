import Trusted
import Anneal
import Mir.FuchsiaUsercopy.parse_compare_exchange_result
import Obligations.FuchsiaUsercopy.parse_compare_exchange_result
import Specs.FuchsiaUsercopy.parse_compare_exchange_result

namespace Proof.FuchsiaUsercopy.parse_compare_exchange_result

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 10000000 in
theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.parse_compare_exchange_result.statefulClaim := by
  refine verifyStatefulMirNoPanicSym Obligations.FuchsiaUsercopy.parse_compare_exchange_result.statefulClaim 30 ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨exp, v, h_exp, h_v, rfl⟩, rfl⟩
  (repeat' ((conv => whnf); split))
  all_goals (conv => whnf)
  all_goals (dsimp at *; try simp_all; try omega)
  all_goals (
    intro exp' v' h_eq
    injection h_eq with h1 ht1
    injection ht1 with h2 _
    injection h1 with hs1
    injection h2 with hs2
    cases hs1; cases hs2
    try (have hv0 : v = 0 := by omega; simp [hv0])
    try (have hv1 : v = 1 := by omega; simp [hv1])
    try (have hvn : v ≠ 0 ∧ v ≠ 1 := by omega; simp [hvn.1, hvn.2])
  )

end Proof.FuchsiaUsercopy.parse_compare_exchange_result
