import Trusted
import Anneal.MirLiftCore
import Mir.FxfsStorageBoundary.ff1_block_tail_offset
import Obligations.FxfsStorageBoundary.ff1_block_tail_offset
import Specs.FxfsStorageBoundary.ff1_block_tail_offset

namespace Proof.FxfsStorageBoundary.ff1_block_tail_offset

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.FunctionalTranslation

theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.ff1_block_tail_offset.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨d, h_d, rfl⟩, rfl⟩
  apply lift_PureMirConverges rfl
  apply LiftBlock.of_lookup rfl
  repeat apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨16 - d, 8⟩) rfl ?h_rv rfl (by nofun) rfl)
  case h_rv =>
    change evalScalarBinOp .subUnchecked ⟨16, 8⟩ ⟨d, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus,
      Nat.ble_eq_true_of_le (Nat.le_trans h_d (by decide : 12 ≤ 16)),
      nat_ble_eq_false_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le 16 d) (by decide : 16 < 18446744073709551616))]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ ⟨⟩
  rfl

end Proof.FxfsStorageBoundary.ff1_block_tail_offset
