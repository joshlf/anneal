import Trusted
import Anneal
import Mir.FxfsStorageBoundary.ff1_block_tail_offset
import Obligations.FxfsStorageBoundary.ff1_block_tail_offset
import Specs.FxfsStorageBoundary.ff1_block_tail_offset

namespace Proof.FxfsStorageBoundary.ff1_block_tail_offset

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.ff1_block_tail_offset.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨d, h_d, rfl⟩, rfl⟩
  apply lift_PureMirConverges rfl
  -- bb0: `StorageLive(_2); _2 = const 16_usize;
  --   _0 = SubUnchecked(copy _2, copy _1); StorageDead(_2); return`
  apply LiftBlock.of_lookup rfl
  repeat apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨16 - d, 8⟩)
      rfl ?h_rv rfl (by nofun) rfl)
  case h_rv =>
    -- `d ≤ 12`, so `16 - d` neither underflows nor leaves the `usize` range.
    show (match Nat.ble d 16 with | true => _ | false => _) = _
    rw [Nat.ble_eq_true_of_le (by omega)]
    show (match Nat.ble 18446744073709551616 (16 - d) with | true => _ | false => _) = _
    rw [Anneal.FunctionalTranslation.nat_ble_eq_false_of_lt (by omega)]
    rfl
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ ⟨⟩
  rfl

end Proof.FxfsStorageBoundary.ff1_block_tail_offset
