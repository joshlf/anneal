import Trusted
import Anneal.MirLiftCore
import Mir.FxfsPlatformPager.weak_node_downcast_type_check
import Obligations.FxfsPlatformPager.weak_node_downcast_type_check
import Specs.FxfsPlatformPager.weak_node_downcast_type_check

namespace Proof.FxfsPlatformPager.weak_node_downcast_type_check

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore

theorem verified : StatefulVerificationResult Obligations.FxfsPlatformPager.weak_node_downcast_type_check.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨vt, tt, pnn, -, -, h_pnn, rfl⟩, rfl⟩
  rcases (by omega : pnn = 0 ∨ pnn = 1) with rfl | rfl <;>
    (apply lift_PureMirConverges rfl
     apply LiftBlock.of_lookup rfl
     apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
     apply LiftBlock.of_lookup rfl
     apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
     apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
     apply LiftBlock.of_lookup rfl
     apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
     rintro _ _ _ ⟨⟩)
  · simp
  · cases h : Nat.beq vt tt <;> simp_all [boolToScalar]

end Proof.FxfsPlatformPager.weak_node_downcast_type_check
