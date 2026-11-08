import Trusted
import Anneal.MirLiftCore
import Mir.FxfsStorageBoundary.vmo_subslice_bounds_valid
import Obligations.FxfsStorageBoundary.vmo_subslice_bounds_valid
import Specs.FxfsStorageBoundary.vmo_subslice_bounds_valid

namespace Proof.FxfsStorageBoundary.vmo_subslice_bounds_valid

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.FunctionalTranslation

theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.vmo_subslice_bounds_valid.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨base, len, s, e, h_se, h_el, h_bound, rfl⟩, rfl⟩
  have h_es_len : e - s ≤ len := Nat.le_trans (Nat.sub_le e s) h_el
  apply lift_PureMirConverges rfl
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨e - s, 8⟩) rfl ?h_sub rfl (by nofun) rfl)
  case h_sub =>
    change evalScalarBinOp .subUnchecked ⟨e, 8⟩ ⟨s, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus, Nat.ble_eq_true_of_le h_se,
      nat_ble_eq_false_of_lt
        (Nat.lt_of_le_of_lt (Nat.le_trans h_es_len (Nat.le_add_left _ _)) h_bound)]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨base + (e - s), 8⟩) rfl ?h_add rfl (by nofun) rfl)
  case h_add =>
    change evalScalarBinOp .addUnchecked ⟨base, 8⟩ ⟨e - s, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus,
      nat_ble_eq_false_of_lt (Nat.lt_of_le_of_lt (Nat.add_le_add_left h_es_len _) h_bound)]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ _ _ ⟨⟩
  rfl

end Proof.FxfsStorageBoundary.vmo_subslice_bounds_valid
