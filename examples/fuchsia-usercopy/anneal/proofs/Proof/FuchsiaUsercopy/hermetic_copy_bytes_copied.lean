import Trusted
import Anneal
import Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied
import Obligations.FuchsiaUsercopy.hermetic_copy_bytes_copied
import Specs.FuchsiaUsercopy.hermetic_copy_bytes_copied

namespace Proof.FuchsiaUsercopy.hermetic_copy_bytes_copied

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.hermetic_copy_bytes_copied.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨base, count, unread, h_bu, h_uc, h_lt, -, rfl⟩, rfl⟩
  apply lift_PureMirConverges rfl
  -- bb0: `StorageLive(_4); _4 = SubWithOverflow(copy _3, copy _1); assert(!_4.1) -> bb1`
  apply LiftBlock.of_lookup rfl
  repeat apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .aggregate 0 [.scalar ⟨unread - base, 8⟩, .scalar ⟨0, 1⟩])
      rfl ?h_rv rfl (by nofun) rfl)
  case h_rv =>
    -- `base ≤ unread`, so the checked subtraction takes its non-overflow arm.
    change (match Nat.ble base unread with | true => _ | false => _) = _
    rw [Nat.ble_eq_true_of_le h_bu]
    show RvalueEvalResult.ok (.aggregate 0
      [.scalar ⟨wrapScalarBits (unread - base) 18446744073709551616, 8⟩,
       .scalar ⟨0, 1⟩]) _ _ = _
    rw [wrapScalarBits_eq_of_lt (by omega)]
  apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
  -- bb1: `_0 = move (_4.0); return`
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ _ ⟨⟩
  exact ⟨rfl, h_uc⟩

end Proof.FuchsiaUsercopy.hermetic_copy_bytes_copied
