import Trusted
import Anneal.MirLiftCore
import Mir.FxfsTier1.file_extent_logical_end
import Specs.FxfsTier1.file_extent_logical_end
import Obligations.FxfsTier1.file_extent_logical_end

namespace Proof.FxfsTier1.file_extent_logical_end

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.FunctionalTranslation
open Anneal.PureMirExec
open Anneal.MirLiftCore

/-- Universal proof that `file_extent_logical_end` (`u64::unchecked_sub` + `u64::unchecked_add`
    extracted from `fxfs/src/object_store/data_object_handle.rs`) is free of Undefined Behavior
    (`BinOp.subUnchecked` and `BinOp.addUnchecked`) for all valid 64-bit `FileExtent` values. -/
theorem verified : VerificationResult Obligations.FxfsTier1.file_extent_logical_end.claim := by
  refine verifyMirNoPanic_of_pureExec _ rfl ?_
  rintro _ ⟨ds, de, lo, h_lt, _, h_sum_max, rfl⟩
  apply lift_PureMirConverges rfl
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue (val := .scalar ⟨de - ds, 8⟩)
      rfl ?h_rv_sub rfl (by nofun) rfl)
  case h_rv_sub =>
    change evalScalarBinOp .subUnchecked ⟨de, 8⟩ ⟨ds, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus, Nat.ble_eq_true_of_le (Nat.le_of_lt h_lt),
      nat_ble_eq_false_of_lt (by omega : de - ds < 18446744073709551616)]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue (val := .scalar ⟨lo + (de - ds), 8⟩)
      rfl ?h_rv_add rfl (by nofun) rfl)
  case h_rv_add =>
    change evalScalarBinOp .addUnchecked ⟨lo, 8⟩ ⟨de - ds, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus, nat_ble_eq_false_of_lt h_sum_max]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ _ ⟨⟩
  rfl

end Proof.FxfsTier1.file_extent_logical_end
