import Trusted
import Anneal.MirLiftCore
import Mir.FxfsConcurrencyModels.skiplist_level_and_epoch_valid
import Obligations.FxfsConcurrencyModels.skiplist_level_and_epoch_valid
import Specs.FxfsConcurrencyModels.skiplist_level_and_epoch_valid

namespace Proof.FxfsConcurrencyModels.skiplist_level_and_epoch_valid

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.FunctionalTranslation
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Specs.FxfsConcurrencyModels.skiplist_level_and_epoch_valid

theorem verified :
    StatefulVerificationResult
      Obligations.FxfsConcurrencyModels.skiplist_level_and_epoch_valid.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨lvl, max_lvl, readers, _, h_max, _, rfl⟩, rfl⟩
  cases h_ge1 : Nat.ble max_lvl lvl
  cases h_ge2 : Nat.ble 18446744073709551615 readers
  all_goals (
    apply lift_PureMirConverges rfl
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    rw [h_ge1]
    apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    try (
      apply LiftBlock.of_lookup rfl
      apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      rw [h_ge2]
      apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    )
  )
  have h1 : lvl < max_lvl := by simp at h_ge1; omega
  have h2 : readers < 18446744073709551615 := by simp at h_ge2; omega
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue (val := .scalar ⟨max_lvl - lvl, 8⟩)
      rfl ?h_rv_sub rfl (by nofun) rfl)
  case h_rv_sub =>
    change evalScalarBinOp .subUnchecked ⟨max_lvl, 8⟩ ⟨lvl, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus, Nat.ble_eq_true_of_le (Nat.le_of_lt h1),
      nat_ble_eq_false_of_lt (by omega : max_lvl - lvl < 18446744073709551616)]
  repeat apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue (val := .scalar ⟨readers + 1, 8⟩)
      rfl ?h_rv_add rfl (by nofun) rfl)
  case h_rv_add =>
    change evalScalarBinOp .addUnchecked ⟨readers, 8⟩ ⟨1, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus,
      nat_ble_eq_false_of_lt (by omega : readers + 1 < 18446744073709551616)]
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
  all_goals (
    repeat (
      apply LiftBlock.of_lookup rfl
      apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      first
      | apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
      | apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    )
    rintro _ _ _ ⟨⟩
  )
  · simp [expectedSkiplistRet, h1, h2]
  · simp [expectedSkiplistRet, Nat.not_lt.mpr (Nat.le_of_ble_eq_true h_ge2)]
  · simp [expectedSkiplistRet, Nat.not_lt.mpr (Nat.le_of_ble_eq_true h_ge1)]

end Proof.FxfsConcurrencyModels.skiplist_level_and_epoch_valid
