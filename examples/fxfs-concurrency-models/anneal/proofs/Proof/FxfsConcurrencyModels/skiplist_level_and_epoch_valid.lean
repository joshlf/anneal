import Trusted
import Anneal
import Anneal.MirFuelFree
import Anneal.PureMirExec
import Anneal.MirLiftCore
import Mir.FxfsConcurrencyModels.skiplist_level_and_epoch_valid
import Obligations.FxfsConcurrencyModels.skiplist_level_and_epoch_valid
import Specs.FxfsConcurrencyModels.skiplist_level_and_epoch_valid

namespace Proof.FxfsConcurrencyModels.skiplist_level_and_epoch_valid

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Specs.FxfsConcurrencyModels.skiplist_level_and_epoch_valid

theorem verified :
    StatefulVerificationResult
      Obligations.FxfsConcurrencyModels.skiplist_level_and_epoch_valid.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨lvl, max_lvl, readers, h_lvl, h_max, h_readers, rfl⟩, rfl⟩
  cases h_ge1 : Nat.ble max_lvl lvl
  · cases h_ge2 : Nat.ble 18446744073709551615 readers
    · have h1 : lvl < max_lvl := by simp at h_ge1; omega
      have h2 : readers < 18446744073709551615 := by simp at h_ge2; omega
      apply lift_PureMirConverges rfl
      apply LiftBlock.of_lookup rfl
      apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      rw [h_ge1]
      apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
      apply LiftBlock.of_lookup rfl
      apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      rw [h_ge2]
      apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
      apply LiftBlock.of_lookup rfl
      repeat apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
      apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
        (evalPureStmtNorm_assign_local_of_evalRvalue (val := .scalar ⟨max_lvl - lvl, 8⟩)
          rfl ?h_rv_sub rfl (by nofun) rfl)
      case h_rv_sub =>
        have h_ble1 : Nat.ble lvl max_lvl = true := Nat.ble_eq_true_of_le (by omega)
        have h_ble2 : Nat.ble 18446744073709551616 (max_lvl - lvl) = false :=
          Bool.eq_false_iff.mpr (by simp [Nat.ble_eq]; omega)
        change (match Nat.ble lvl max_lvl with
          | true => match Nat.ble 18446744073709551616 (max_lvl - lvl) with
            | true => RvalueEvalResult.ub
            | false => RvalueEvalResult.ok (.scalar ⟨max_lvl - lvl, 8⟩) _ _
          | false => RvalueEvalResult.ub) = _
        rw [h_ble1, h_ble2]
      repeat apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
      apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
        (evalPureStmtNorm_assign_local_of_evalRvalue (val := .scalar ⟨readers + 1, 8⟩)
          rfl ?h_rv_add rfl (by nofun) rfl)
      case h_rv_add =>
        have h_ble_add : Nat.ble 18446744073709551616 (readers + 1) = false :=
          Bool.eq_false_iff.mpr (by simp [Nat.ble_eq]; omega)
        change (match Nat.ble 18446744073709551616 (readers + 1) with
          | true => RvalueEvalResult.ub
          | false => RvalueEvalResult.ok (.scalar ⟨readers + 1, 8⟩) _ _) = _
        rw [h_ble_add]
      apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
      repeat (
        apply LiftBlock.of_lookup rfl
        apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
        apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
      )
      apply LiftBlock.of_lookup rfl
      apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
      rintro _ _ _ ⟨⟩
      simp [expectedSkiplistRet, h1, h2]
    · apply lift_PureMirConverges rfl
      apply LiftBlock.of_lookup rfl
      apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      rw [h_ge1]
      apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
      apply LiftBlock.of_lookup rfl
      apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      rw [h_ge2]
      apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
      repeat (
        apply LiftBlock.of_lookup rfl
        apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
        apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
      )
      apply LiftBlock.of_lookup rfl
      apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
      rintro _ _ _ ⟨⟩
      have h2 : ¬ readers < 18446744073709551615 := by simp [Nat.ble_eq] at h_ge2; omega
      simp [expectedSkiplistRet, h2]
  · apply lift_PureMirConverges rfl
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    rw [h_ge1]
    apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    repeat (
      apply LiftBlock.of_lookup rfl
      apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
    )
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    rintro _ _ _ ⟨⟩
    have h1 : ¬ lvl < max_lvl := by simp [Nat.ble_eq] at h_ge1; omega
    simp [expectedSkiplistRet, h1]

end Proof.FxfsConcurrencyModels.skiplist_level_and_epoch_valid
