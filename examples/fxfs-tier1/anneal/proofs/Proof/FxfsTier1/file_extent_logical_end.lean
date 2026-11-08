import Trusted
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Anneal.MirFuelFree
import Anneal.PureMirExec
import Anneal.MirLiftCore
import Mir.FxfsTier1.file_extent_logical_end
import Specs.FxfsTier1.file_extent_logical_end
import Obligations.FxfsTier1.file_extent_logical_end

namespace Proof.FxfsTier1.file_extent_logical_end

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Specs.FxfsTier1.file_extent_logical_end

/-- Universal proof that `file_extent_logical_end` (`u64::unchecked_sub` + `u64::unchecked_add`
    extracted from `fxfs/src/object_store/data_object_handle.rs`) is free of Undefined Behavior
    (`BinOp.subUnchecked` and `BinOp.addUnchecked`) for all valid 64-bit `FileExtent` values. -/
theorem verified : VerificationResult Obligations.FxfsTier1.file_extent_logical_end.claim := by
  refine verifyMirNoPanic_of_pureExec _ rfl ?_
  rintro _ ⟨ds, de, lo, h_lt, h_de_max, h_sum_max, rfl⟩
  apply lift_PureMirConverges rfl
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue (val := .scalar ⟨de - ds, 8⟩)
      rfl ?h_rv_sub rfl (by nofun) rfl)
  case h_rv_sub =>
    have h_ble1 : Nat.ble ds de = true := Nat.ble_eq_true_of_le (by omega)
    have h_ble2 : Nat.ble 18446744073709551616 (de - ds) = false :=
      Bool.eq_false_iff.mpr (by simp [Nat.ble_eq]; omega)
    change (match Nat.ble ds de with
      | true => match Nat.ble 18446744073709551616 (de - ds) with
        | true => RvalueEvalResult.ub
        | false => RvalueEvalResult.ok (.scalar ⟨de - ds, 8⟩) _ _
      | false => RvalueEvalResult.ub) = _
    rw [h_ble1, h_ble2]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue (val := .scalar ⟨lo + (de - ds), 8⟩)
      rfl ?h_rv_add rfl (by nofun) rfl)
  case h_rv_add =>
    have h_ble_add : Nat.ble 18446744073709551616 (lo + (de - ds)) = false :=
      Bool.eq_false_iff.mpr (by simp [Nat.ble_eq]; omega)
    change (match Nat.ble 18446744073709551616 (lo + (de - ds)) with
      | true => RvalueEvalResult.ub
      | false => RvalueEvalResult.ok (.scalar ⟨lo + (de - ds), 8⟩) _ _) = _
    rw [h_ble_add]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ _ ⟨⟩
  rfl

end Proof.FxfsTier1.file_extent_logical_end
