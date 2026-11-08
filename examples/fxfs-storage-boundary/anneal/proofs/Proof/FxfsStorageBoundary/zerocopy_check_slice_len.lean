import Trusted
import Anneal.MirLiftCore
import Mir.FxfsStorageBoundary.zerocopy_check_slice_len
import Obligations.FxfsStorageBoundary.zerocopy_check_slice_len
import Specs.FxfsStorageBoundary.zerocopy_check_slice_len

namespace Proof.FxfsStorageBoundary.zerocopy_check_slice_len

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.FunctionalTranslation

theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.zerocopy_check_slice_len.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨bl, es, h_es_pos, h_bl, -, rfl⟩, rfl⟩
  have h_es0 : Nat.beq es 0 = false :=
    Bool.eq_false_iff.mpr fun h => Nat.ne_of_gt h_es_pos (Nat.eq_of_beq_eq_true h)
  have h_assert : (boolToScalar (Nat.beq es 0)).bits = 0 := by rw [h_es0]; rfl
  apply lift_PureMirConverges rfl
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) h_assert
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨bl % es, 8⟩) rfl ?h_rem rfl (by nofun) rfl)
  case h_rem =>
    change evalScalarBinOp .rem ⟨bl, 8⟩ ⟨es, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus, wrapScalarBits, h_es0,
      show bl.mod es = bl % es from rfl,
      nat_ble_eq_false_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le bl es) h_bl)]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨bl - bl % es, 8⟩) rfl ?h_sub rfl (by nofun) rfl)
  case h_sub =>
    change evalScalarBinOp .subUnchecked ⟨bl, 8⟩ ⟨bl % es, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus, Nat.ble_eq_true_of_le (Nat.mod_le bl es),
      nat_ble_eq_false_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_bl)]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) h_assert
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨(bl - bl % es) / es, 8⟩) rfl ?h_div rfl (by nofun) rfl)
  case h_div =>
    change evalScalarBinOp .div ⟨bl - bl % es, 8⟩ ⟨es, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus, wrapScalarBits, h_es0,
      show (bl - bl % es).div es = (bl - bl % es) / es from rfl,
      nat_ble_eq_false_of_lt
        (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_bl))]
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ ⟨⟩
  rfl

end Proof.FxfsStorageBoundary.zerocopy_check_slice_len
