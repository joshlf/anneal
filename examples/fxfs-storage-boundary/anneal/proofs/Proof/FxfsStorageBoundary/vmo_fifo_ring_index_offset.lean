import Trusted
import Anneal
import Mir.FxfsStorageBoundary.vmo_fifo_ring_index_offset
import Obligations.FxfsStorageBoundary.vmo_fifo_ring_index_offset
import Specs.FxfsStorageBoundary.vmo_fifo_ring_index_offset

namespace Proof.FxfsStorageBoundary.vmo_fifo_ring_index_offset

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.vmo_fifo_ring_index_offset.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨raw, cap, es, h_cap_pos, h_raw, h_cap, h_es, h_bound, rfl⟩, rfl⟩
  have h_cap0 : Nat.beq cap 0 = false :=
    Bool.eq_false_iff.mpr fun h => by have := Nat.eq_of_beq_eq_true h; omega
  apply lift_PureMirConverges rfl
  -- bb0: `StorageLive(_5); StorageLive(_4); _5 = Eq(copy _2, const 0_usize);
  --   assert(!move _5) -> bb1`. The zero-divisor check passes because
  -- `0 < cap`.
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  · show (boolToScalar (Nat.beq cap 0)).bits = 0
    rw [h_cap0]
    rfl
  -- bb1: `_4 = Rem(copy _1, copy _2); _0 = MulUnchecked(copy _4, copy _3);
  --   StorageDead(_4); return`
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨raw % cap, 8⟩) rfl ?h_rem rfl (by nofun) rfl)
  case h_rem =>
    -- `Rem` re-checks the divisor and wraps `raw % cap ≤ raw < 2^64`.
    show (match Nat.beq cap 0 with | true => _ | false => _) = _
    rw [h_cap0]
    show RvalueEvalResult.ok
      (.scalar ⟨wrapScalarBits (raw % cap) 18446744073709551616, 8⟩) _ _ = _
    rw [wrapScalarBits_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le raw cap) h_raw)]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨raw % cap * es, 8⟩) rfl ?h_mul rfl (by nofun) rfl)
  case h_mul =>
    -- `raw % cap < cap` and `cap * es < 2^64`, so the product does not
    -- overflow.
    show (match Nat.ble 18446744073709551616 (raw % cap * es) with
      | true => _ | false => _) = _
    rw [Anneal.FunctionalTranslation.nat_ble_eq_false_of_lt
      (Nat.lt_of_le_of_lt
        (Nat.mul_le_mul_right es (Nat.le_of_lt (Nat.mod_lt raw h_cap_pos)))
        h_bound)]
    rfl
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ _ ⟨⟩
  rfl

end Proof.FxfsStorageBoundary.vmo_fifo_ring_index_offset
