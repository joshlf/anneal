import Trusted
import Anneal
import Mir.FxfsStorageBoundary.vmo_subslice_bounds_valid
import Obligations.FxfsStorageBoundary.vmo_subslice_bounds_valid
import Specs.FxfsStorageBoundary.vmo_subslice_bounds_valid

namespace Proof.FxfsStorageBoundary.vmo_subslice_bounds_valid

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.vmo_subslice_bounds_valid.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨base, len, s, e, h_se, h_el, h_bound, rfl⟩, rfl⟩
  apply lift_PureMirConverges rfl
  -- bb0: `StorageLive(_5); _5 = SubUnchecked(copy _4, copy _3);
  --   _0 = AddUnchecked(copy _1, copy _5); StorageDead(_5); return`
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨e - s, 8⟩) rfl ?h_sub rfl (by nofun) rfl)
  case h_sub =>
    -- `s ≤ e`, so `e - s` does not underflow.
    show (match Nat.ble s e with | true => _ | false => _) = _
    rw [Nat.ble_eq_true_of_le h_se]
    show (match Nat.ble 18446744073709551616 (e - s) with | true => _ | false => _) = _
    rw [Anneal.FunctionalTranslation.nat_ble_eq_false_of_lt (by omega)]
    rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨base + (e - s), 8⟩) rfl ?h_add rfl (by nofun) rfl)
  case h_add =>
    -- `e - s ≤ len` and `base + len < 2^64`, so the sum does not overflow.
    show (match Nat.ble 18446744073709551616 (base + (e - s)) with
      | true => _ | false => _) = _
    rw [Anneal.FunctionalTranslation.nat_ble_eq_false_of_lt (by omega)]
    rfl
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ _ _ ⟨⟩
  rfl

end Proof.FxfsStorageBoundary.vmo_subslice_bounds_valid
