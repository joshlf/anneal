import Trusted
import Anneal.MirLiftCore
import Mir.FxfsTier1.range_unchecked_length
import Specs.FxfsTier1.range_unchecked_length
import Obligations.FxfsTier1.range_unchecked_length

namespace Proof.FxfsTier1.range_unchecked_length

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.FunctionalTranslation
open Anneal.PureMirExec
open Anneal.MirLiftCore

/-- Universal proof that `range_unchecked_length` (`u64::unchecked_sub` extracted from
    `fxfs/src/range.rs`) is free of Undefined Behavior (`BinOp.subUnchecked`) for all
    64-bit ranges satisfying `start <= end`. -/
theorem verified : VerificationResult Obligations.FxfsTier1.range_unchecked_length.claim := by
  refine verifyMirNoPanic_of_pureExec _ rfl ?_
  rintro _ ⟨s, e, h_le, h_e_max, rfl⟩
  apply lift_PureMirConverges rfl
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue (val := .scalar ⟨e - s, 8⟩)
      rfl ?h_rv rfl (by nofun) rfl)
  case h_rv =>
    change evalScalarBinOp .subUnchecked ⟨e, 8⟩ ⟨s, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus, Nat.ble_eq_true_of_le h_le,
      nat_ble_eq_false_of_lt (by omega : e - s < 18446744073709551616)]
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ ⟨⟩
  rfl

end Proof.FxfsTier1.range_unchecked_length
