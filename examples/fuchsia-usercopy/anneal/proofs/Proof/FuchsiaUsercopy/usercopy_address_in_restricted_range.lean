import Trusted
import Anneal
import Mir.FuchsiaUsercopy.usercopy_address_in_restricted_range
import Obligations.FuchsiaUsercopy.usercopy_address_in_restricted_range
import Specs.FuchsiaUsercopy.usercopy_address_in_restricted_range

namespace Proof.FuchsiaUsercopy.usercopy_address_in_restricted_range

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.usercopy_address_in_restricted_range.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨addr, rs, re, -, -, -, rfl⟩, rfl⟩
  -- Split on both switch conditions before lifting so that each path gets its
  -- own step budget; rewriting them in the lifted environment resolves the
  -- switches.
  cases h0 : Nat.beq addr 0
  · have h_ne := Nat.ne_of_beq_eq_false h0
    cases hs : Nat.ble rs addr <;>
      (apply lift_PureMirConverges rfl
       -- bb0: `_4 = Eq(copy _1, const 0_usize); switchInt(move _4) -> [0: bb2, otherwise: bb1]`
       apply LiftBlock.of_lookup rfl
       apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
       rw [h0]
       apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
       -- bb2: `_5 = Lt(copy _1, copy _2); switchInt(move _5) -> [0: bb4, otherwise: bb3]`
       apply LiftBlock.of_lookup rfl
       apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
       rw [hs]
       apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
       -- bb3 (`_0 = const false`) or bb4 (`_0 = Lt(copy _1, copy _3)`); `goto -> bb5`
       apply LiftBlock.of_lookup rfl
       apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
       apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
       -- bb5: `return`
       apply LiftBlock.of_lookup rfl
       apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
       rintro _ _ _ ⟨⟩
       refine ⟨?_, fun h => absurd h h_ne⟩)
    · -- `addr < rs`: bb3 returned `false`.
      have := Nat.not_le_of_not_ble_eq_true (Bool.ne_true_of_eq_false hs)
      rw [ite_eq_right (by omega)]
    · -- `rs ≤ addr`: bb4 returned `addr < re`.
      have h_rs := Nat.le_of_ble_eq_true hs
      cases hre : Nat.ble re addr
      · have := Nat.not_le_of_not_ble_eq_true (Bool.ne_true_of_eq_false hre)
        rw [ite_eq_left ⟨h_ne, h_rs, by omega⟩]
        rfl
      · have := Nat.le_of_ble_eq_true hre
        rw [ite_eq_right (by omega)]
        rfl
  · -- `addr = 0`: bb1 returns `false`.
    have h_z := Nat.eq_of_beq_eq_true h0
    apply lift_PureMirConverges rfl
    -- bb0, as above
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    rw [h0]
    apply LiftStmtsTerminator.term_switchInt (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    -- bb1: `_0 = const false; goto -> bb5`
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_goto (by rfl) (Or.inr rfl) (by rfl)
    -- bb5: `return`
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    rintro _ _ _ ⟨⟩
    exact ⟨by rw [ite_eq_right (by omega)], fun _ => rfl⟩

end Proof.FuchsiaUsercopy.usercopy_address_in_restricted_range
