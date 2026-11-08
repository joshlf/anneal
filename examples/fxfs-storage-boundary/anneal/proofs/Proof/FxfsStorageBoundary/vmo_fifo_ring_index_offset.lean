import Trusted
import Anneal.MirLiftCore
import Mir.FxfsStorageBoundary.vmo_fifo_ring_index_offset
import Obligations.FxfsStorageBoundary.vmo_fifo_ring_index_offset
import Specs.FxfsStorageBoundary.vmo_fifo_ring_index_offset

namespace Proof.FxfsStorageBoundary.vmo_fifo_ring_index_offset

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.FunctionalTranslation

theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.vmo_fifo_ring_index_offset.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨raw, cap, es, h_cap_pos, h_raw, -, -, h_bound, rfl⟩, rfl⟩
  have h_cap0 : Nat.beq cap 0 = false :=
    Bool.eq_false_iff.mpr fun h => Nat.ne_of_gt h_cap_pos (Nat.eq_of_beq_eq_true h)
  have h_assert : (boolToScalar (Nat.beq cap 0)).bits = 0 := by rw [h_cap0]; rfl
  apply lift_PureMirConverges rfl
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) h_assert
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨raw % cap, 8⟩) rfl ?h_rem rfl (by nofun) rfl)
  case h_rem =>
    change evalScalarBinOp .rem ⟨raw, 8⟩ ⟨cap, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus, wrapScalarBits, h_cap0,
      show raw.mod cap = raw % cap from rfl,
      nat_ble_eq_false_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le raw cap) h_raw)]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨raw % cap * es, 8⟩) rfl ?h_mul rfl (by nofun) rfl)
  case h_mul =>
    change evalScalarBinOp .mulUnchecked ⟨raw % cap, 8⟩ ⟨es, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus,
      nat_ble_eq_false_of_lt (Nat.lt_of_le_of_lt
        (Nat.mul_le_mul_right es (Nat.le_of_lt (Nat.mod_lt raw h_cap_pos))) h_bound)]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ _ ⟨⟩
  rfl

end Proof.FxfsStorageBoundary.vmo_fifo_ring_index_offset
