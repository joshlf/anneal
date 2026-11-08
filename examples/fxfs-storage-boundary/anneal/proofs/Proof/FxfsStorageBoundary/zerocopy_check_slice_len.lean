import Trusted
import Anneal
import Mir.FxfsStorageBoundary.zerocopy_check_slice_len
import Obligations.FxfsStorageBoundary.zerocopy_check_slice_len
import Specs.FxfsStorageBoundary.zerocopy_check_slice_len

namespace Proof.FxfsStorageBoundary.zerocopy_check_slice_len

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.zerocopy_check_slice_len.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨bl, es, h_es_pos, h_bl, h_es, rfl⟩, rfl⟩
  have h_es0 : Nat.beq es 0 = false :=
    Bool.eq_false_iff.mpr fun h => by have := Nat.eq_of_beq_eq_true h; omega
  have h_rem_le : bl % es ≤ bl := Nat.mod_le bl es
  apply lift_PureMirConverges rfl
  -- bb0: `StorageLive(_4); StorageLive(_6); StorageLive(_3);
  --   _4 = Eq(copy _2, const 0_usize); assert(!move _4) -> bb1`. The
  -- zero-divisor check passes because `0 < es`.
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  · show (boolToScalar (Nat.beq es 0)).bits = 0
    rw [h_es0]
    rfl
  -- bb1: `_3 = Rem(copy _1, copy _2); StorageLive(_5);
  --   _5 = SubUnchecked(copy _1, copy _3); _6 = Eq(copy _2, const 0_usize);
  --   assert(!move _6) -> bb2`
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨bl % es, 8⟩) rfl ?h_rem rfl (by nofun) rfl)
  case h_rem =>
    -- `Rem` re-checks the divisor and wraps `bl % es ≤ bl < 2^64`.
    show (match Nat.beq es 0 with | true => _ | false => _) = _
    rw [h_es0]
    show RvalueEvalResult.ok
      (.scalar ⟨wrapScalarBits (bl % es) 18446744073709551616, 8⟩) _ _ = _
    rw [wrapScalarBits_eq_of_lt (by omega)]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨bl - bl % es, 8⟩) rfl ?h_sub rfl (by nofun) rfl)
  case h_sub =>
    -- `bl % es ≤ bl`, so `bl - bl % es` does not underflow.
    show (match Nat.ble (bl % es) bl with | true => _ | false => _) = _
    rw [Nat.ble_eq_true_of_le h_rem_le]
    show (match Nat.ble 18446744073709551616 (bl - bl % es) with
      | true => _ | false => _) = _
    rw [Anneal.FunctionalTranslation.nat_ble_eq_false_of_lt (by omega)]
    rfl
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  · show (boolToScalar (Nat.beq es 0)).bits = 0
    rw [h_es0]
    rfl
  -- bb2: `_0 = Div(copy _5, copy _2); StorageDead(_5); StorageDead(_3); return`
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨(bl - bl % es) / es, 8⟩) rfl ?h_div rfl (by nofun) rfl)
  case h_div =>
    -- `Div` re-checks the divisor and wraps
    -- `(bl - bl % es) / es ≤ bl - bl % es < 2^64`.
    show (match Nat.beq es 0 with | true => _ | false => _) = _
    rw [h_es0]
    show RvalueEvalResult.ok
      (.scalar ⟨wrapScalarBits ((bl - bl % es) / es) 18446744073709551616, 8⟩) _ _ = _
    rw [wrapScalarBits_eq_of_lt
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ ⟨⟩
  rfl

end Proof.FxfsStorageBoundary.zerocopy_check_slice_len
