import Trusted
import Anneal
import Mir.FuchsiaUsercopy.atomic_load_u32_unpack
import Obligations.FuchsiaUsercopy.atomic_load_u32_unpack
import Specs.FuchsiaUsercopy.atomic_load_u32_unpack

namespace Proof.FuchsiaUsercopy.atomic_load_u32_unpack

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.atomic_load_u32_unpack.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨v, -, rfl⟩, rfl⟩
  -- bb0: `_2 = Le(copy _1, const 4294967295_u64); switchInt(move _2) -> [0: bb2, otherwise: bb1]`.
  -- Split on the comparison before lifting so that each path gets its own step
  -- budget; rewriting it in the lifted environment then resolves the switch.
  cases h_le : Nat.ble v 4294967295 <;>
    (apply lift_PureMirConverges rfl
     apply LiftBlock.of_lookup rfl
     apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
     rw [h_le])
  · -- `v > u32::MAX`: bb2 `_0 = (const false, const 0_u32); goto -> bb3`
    apply LiftStmtsTerminator.term_switchInt (target := 2) (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
    -- bb3: `return`
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    rintro _ ⟨⟩
    have h := Nat.not_le_of_not_ble_eq_true (Bool.ne_true_of_eq_false h_le)
    rw [ite_eq_right (by omega)]
  · -- `v ≤ u32::MAX`: bb1 `_3 = copy _1 as u32 (IntToInt); _0 = (const true, move _3); goto -> bb3`
    apply LiftStmtsTerminator.term_switchInt (target := 1) (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
    -- bb3: `return`
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    rintro _ ⟨⟩
    have h := Nat.le_of_ble_eq_true h_le
    rw [ite_eq_left (by omega)]
    show Value.aggregate 0 [_, .scalar ⟨wrapScalarBits v 4294967296, 4⟩] = _
    rw [wrapScalarBits_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

end Proof.FuchsiaUsercopy.atomic_load_u32_unpack
