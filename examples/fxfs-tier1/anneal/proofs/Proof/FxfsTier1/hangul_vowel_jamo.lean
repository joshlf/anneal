import Trusted
import Anneal.MirLiftCore
import Mir.FxfsTier1.hangul_vowel_jamo
import Specs.FxfsTier1.hangul_vowel_jamo
import Obligations.FxfsTier1.hangul_vowel_jamo

namespace Proof.FxfsTier1.hangul_vowel_jamo

open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore

/-- Proof that `hangul_vowel_jamo` (`char::from_u32_unchecked` in `fxfs/unicode/src/nfd.rs`)
    is free of Undefined Behavior (`CastKind.transmute` to `RigidTy.char` checked by `isValidCharCode`). -/
theorem verified : VerificationResult Obligations.FxfsTier1.hangul_vowel_jamo.claim := by
  refine verifyMirNoPanic_of_pureExec _ rfl ?_
  rintro _ rfl
  apply lift_PureMirConverges rfl
  repeat (
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    first
    | apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    | apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  )
  rfl

end Proof.FxfsTier1.hangul_vowel_jamo
