import Trusted
import Anneal
import Mir.FuchsiaUsercopy.assume_initialized_until_split_len
import Obligations.FuchsiaUsercopy.assume_initialized_until_split_len
import Specs.FuchsiaUsercopy.assume_initialized_until_split_len

namespace Proof.FuchsiaUsercopy.assume_initialized_until_split_len

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.assume_initialized_until_split_len.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨buf_len, init_until, h_le, h_lt, rfl⟩, rfl⟩
  apply lift_PureMirConverges rfl
  -- bb0: `StorageLive(_3); StorageLive(_4);
  --   _4 = SubWithOverflow(copy _1, copy _2); assert(!_4.1) -> bb1`
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .aggregate 0 [.scalar ⟨buf_len - init_until, 8⟩, .scalar ⟨0, 1⟩])
      (oldSlot := .uninit) rfl ?h_rv rfl (fun h => nomatch h) rfl)
  case h_rv =>
    -- `init_until ≤ buf_len`, so the checked subtraction takes its
    -- non-overflow arm.
    change (match Nat.ble init_until buf_len with | true => _ | false => _) = _
    rw [Nat.ble_eq_true_of_le h_le]
    show RvalueEvalResult.ok (.aggregate 0
      [.scalar ⟨wrapScalarBits (buf_len - init_until) 18446744073709551616, 8⟩,
       .scalar ⟨0, 1⟩]) _ _ = _
    rw [wrapScalarBits_eq_of_lt (by omega)]
  apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
  -- bb1: `_3 = move (_4.0); _0 = (copy _2, copy _3); return`
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ ⟨⟩
  exact ⟨rfl, by omega⟩

end Proof.FuchsiaUsercopy.assume_initialized_until_split_len
