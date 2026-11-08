import Trusted
import Anneal.MirLiftCore
import Mir.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire
import Obligations.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire
import Specs.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire

namespace Proof.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire

open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.MirLiftCore

theorem verified :
    StatefulVerificationResult
      Obligations.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨cur, cnt, head_b, tgt, h_cur, rfl, h_head, h_tgt, _, rfl⟩, rfl⟩
  rcases h_cur with rfl | rfl <;>
    rcases (by omega : head_b = 0 ∨ head_b = 1) with rfl | rfl <;>
    rcases h_tgt with rfl | rfl
  all_goals (
    apply lift_PureMirConverges rfl
    repeat (
      apply LiftBlock.of_lookup rfl
      try apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      first
      | apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
      | apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
      | apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    )
    rintro _ _ _ _ ⟨⟩
    exact ⟨rfl, by decide⟩
  )

end Proof.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire
