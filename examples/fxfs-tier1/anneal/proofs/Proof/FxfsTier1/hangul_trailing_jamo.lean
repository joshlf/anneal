import Trusted
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Anneal.PureMirExec
import Anneal.MirLiftCore
import Mir.FxfsTier1.hangul_trailing_jamo
import Specs.FxfsTier1.hangul_trailing_jamo
import Obligations.FxfsTier1.hangul_trailing_jamo

namespace Proof.FxfsTier1.hangul_trailing_jamo

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Specs.FxfsTier1.hangul_trailing_jamo

/-- Proof that `hangul_trailing_jamo` (`char::from_u32_unchecked` in `fxfs/unicode/src/nfd.rs`)
    is free of Undefined Behavior (`CastKind.transmute` to `RigidTy.char` checked by `isValidCharCode`). -/
theorem verified : VerificationResult Obligations.FxfsTier1.hangul_trailing_jamo.claim := by
  refine verifyMirNoPanic_of_pureExec _ (by decide) (fun args h_pre => ?_)
  subst h_pre
  apply lift_PureMirConverges (by decide)
  repeat (
    apply LiftBlock.of_lookup (by rfl)
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
  )
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rfl

end Proof.FxfsTier1.hangul_trailing_jamo
