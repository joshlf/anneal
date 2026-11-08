import Trusted
import Anneal
import Mir.FuchsiaUsercopy.fidl_pointer_is_encoded_present
import Obligations.FuchsiaUsercopy.fidl_pointer_is_encoded_present
import Specs.FuchsiaUsercopy.fidl_pointer_is_encoded_present

namespace Proof.FuchsiaUsercopy.fidl_pointer_is_encoded_present

open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore

theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.fidl_pointer_is_encoded_present.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨enc, -, rfl⟩, rfl⟩
  -- The arms of bb0's switch reach `return` after different numbers of steps,
  -- and the lifted step budget is a single metavariable, so split on
  -- `enc == 0` before lifting. Rewriting it in the lifted environment then
  -- resolves the switch.
  cases h0 : Nat.beq enc 0 <;>
    (apply lift_PureMirConverges rfl
     -- bb0: `_2 = Eq(copy _1, const 0_u64); switchInt(move _2) -> [0: bb2, otherwise: bb1]`
     apply LiftBlock.of_lookup rfl
     apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
     rw [h0]
     apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
     -- bb2 (`_3 = Eq(copy _1, const u64::MAX)`) or bb1 (`_0 = Some(const false)`)
     apply LiftBlock.of_lookup rfl
     apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl))
  · -- bb2: `switchInt(move _3) -> [0: bb4, otherwise: bb3]`. Both arms assign
    -- `_0` and `goto -> bb5`, so they share one step budget.
    cases hM : Nat.beq enc 18446744073709551615 <;>
      (apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
       -- bb4 (`_0 = None`) or bb3 (`_0 = Some(const true)`); `goto -> bb5`
       apply LiftBlock.of_lookup rfl
       apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
       apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
       -- bb5: `return`
       apply LiftBlock.of_lookup rfl
       apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
       rintro _ ⟨⟩
       rw [ite_eq_right (Nat.ne_of_beq_eq_false h0)])
    · rw [ite_eq_right (Nat.ne_of_beq_eq_false hM)]
    · rw [ite_eq_left (Nat.eq_of_beq_eq_true hM)]
  · -- bb1: `goto -> bb5`; bb5: `return`
    apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    rintro _ ⟨⟩
    rw [ite_eq_left (Nat.eq_of_beq_eq_true h0)]

end Proof.FuchsiaUsercopy.fidl_pointer_is_encoded_present
