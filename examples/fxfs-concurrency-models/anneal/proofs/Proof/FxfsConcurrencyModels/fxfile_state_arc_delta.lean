import Trusted
import Anneal
import Mir.FxfsConcurrencyModels.fxfile_state_arc_delta
import Obligations.FxfsConcurrencyModels.fxfile_state_arc_delta
import Specs.FxfsConcurrencyModels.fxfile_state_arc_delta

namespace Proof.FxfsConcurrencyModels.fxfile_state_arc_delta

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.MirLiftCore

theorem verified :
    StatefulVerificationResult
      Obligations.FxfsConcurrencyModels.fxfile_state_arc_delta.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ (by decide)
    (fun args mem h_pre => by rcases h_pre with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩)
    (fun args mem h_pre => ?_)
  rcases h_pre with ⟨⟨old_b, new_b, tomb_b, h_old, h_new, h_tomb, rfl⟩, rfl⟩
  rcases (by omega : old_b = 0 ∨ old_b = 1) with rfl | rfl <;>
    rcases (by omega : new_b = 0 ∨ new_b = 1) with rfl | rfl <;>
    rcases (by omega : tomb_b = 0 ∨ tomb_b = 1) with rfl | rfl
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
    intro old_b' new_b' tomb_b' h_eq
    injection h_eq with h1 h_t1
    injection h_t1 with h2 h_t2
    injection h_t2 with h3 _
    injection h1 with hs1
    injection h2 with hs2
    injection h3 with hs3
    cases hs1; cases hs2; cases hs3
    exact ⟨rfl, rfl⟩
  )

end Proof.FxfsConcurrencyModels.fxfile_state_arc_delta
