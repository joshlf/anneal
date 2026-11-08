import Trusted
import Anneal.MirLiftCore
import Mir.FxfsConcurrencyModels.fxfile_state_arc_delta
import Obligations.FxfsConcurrencyModels.fxfile_state_arc_delta
import Specs.FxfsConcurrencyModels.fxfile_state_arc_delta

namespace Proof.FxfsConcurrencyModels.fxfile_state_arc_delta

open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.MirLiftCore

theorem verified :
    StatefulVerificationResult
      Obligations.FxfsConcurrencyModels.fxfile_state_arc_delta.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨old_b, new_b, tomb_b, h_old, h_new, h_tomb, rfl⟩, rfl⟩
  rcases (by omega : old_b = 0 ∨ old_b = 1) with rfl | rfl <;>
    rcases (by omega : new_b = 0 ∨ new_b = 1) with rfl | rfl <;>
    rcases (by omega : tomb_b = 0 ∨ tomb_b = 1) with rfl | rfl
  all_goals (
    apply lift_PureMirConverges rfl
    repeat (
      apply LiftBlock.of_lookup rfl
      apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      first
      | apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
      | apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
      | apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    )
    rintro _ _ _ ⟨⟩
    exact ⟨rfl, rfl⟩
  )

end Proof.FxfsConcurrencyModels.fxfile_state_arc_delta
