import Trusted
import Anneal
import Mir.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire
import Obligations.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire
import Specs.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire

namespace Proof.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Specs.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire

theorem verified :
    StatefulVerificationResult
      Obligations.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ (by decide)
    (fun args mem h_pre => by rcases h_pre with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩)
    (fun args mem h_pre => ?_)
  rcases h_pre with ⟨⟨cur, cnt, head_b, tgt, h_cur, rfl, h_head, h_tgt, h_inv, rfl⟩, rfl⟩
  rcases h_cur with rfl | rfl <;>
    rcases (by omega : head_b = 0 ∨ head_b = 1) with rfl | rfl <;>
    rcases h_tgt with rfl | rfl
  all_goals (
    apply lift_PureMirConverges (by decide)
    repeat (
      apply LiftBlock.of_lookup (by rfl)
      try apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      first
      | apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
      | apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
      | apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    )
    intro cur' cnt' head_b' tgt' h_eq
    injection h_eq with h1 h_t1
    injection h_t1 with h2 h_t2
    injection h_t2 with h3 h_t3
    injection h_t3 with h4 _
    injection h1 with hs1
    injection h2 with hs2
    injection h3 with hs3
    injection h4 with hs4
    cases hs1; cases hs2; cases hs3; cases hs4
    exact ⟨rfl, by decide⟩
  )

end Proof.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire
