import Trusted
import Anneal
import Mir.FxfsPlatformPager.weak_node_downcast_type_check
import Obligations.FxfsPlatformPager.weak_node_downcast_type_check
import Specs.FxfsPlatformPager.weak_node_downcast_type_check

namespace Proof.FxfsPlatformPager.weak_node_downcast_type_check

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : StatefulVerificationResult Obligations.FxfsPlatformPager.weak_node_downcast_type_check.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨vt, tt, pnn, -, -, h_pnn, rfl⟩, rfl⟩
  -- Both arms of bb0's switch take the same number of steps, so one lifting
  -- script covers both values of `ptr_non_null`.
  rcases (by omega : pnn = 0 ∨ pnn = 1) with rfl | rfl <;>
    (apply lift_PureMirConverges rfl
     -- bb0: `switchInt(copy _3) -> [0: bb1, otherwise: bb2]`
     apply LiftBlock.of_lookup rfl
     apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
     -- bb1 (`_0 = const false`) or bb2 (`_0 = Eq(copy _1, copy _2)`);
     -- `goto -> bb3`
     apply LiftBlock.of_lookup rfl
     apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
     apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
     -- bb3: `return`
     apply LiftBlock.of_lookup rfl
     apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
     rintro _ _ _ ⟨⟩)
  · -- `ptr_non_null = false`: bb1 returned `false`.
    rw [ite_eq_right (by omega)]
  · -- `ptr_non_null = true`: bb2 returned `vtable_type_id == target_type_id`.
    cases h : Nat.beq vt tt
    · rw [ite_eq_right (by have := Nat.ne_of_beq_eq_false h; omega)]
      rfl
    · rw [ite_eq_left ⟨rfl, Nat.eq_of_beq_eq_true h⟩]
      rfl

end Proof.FxfsPlatformPager.weak_node_downcast_type_check
