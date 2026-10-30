import Trusted
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FxfsTier1.hangul_vowel_jamo
import Specs.FxfsTier1.hangul_vowel_jamo
import Obligations.FxfsTier1.hangul_vowel_jamo

namespace Proof.FxfsTier1.hangul_vowel_jamo

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.FxfsTier1.hangul_vowel_jamo

/-- Proof that `hangul_vowel_jamo` (`char::from_u32_unchecked` in `fxfs/unicode/src/nfd.rs`)
    is free of Undefined Behavior (`CastKind.transmute` to `RigidTy.char` checked by `isValidCharCode`). -/
theorem verified : VerificationResult Obligations.FxfsTier1.hangul_vowel_jamo.claim := by
  refine verifyMirNoPanicSym Obligations.FxfsTier1.hangul_vowel_jamo.claim 32 ?_
  intro args h_pre
  subst h_pre
  rfl

end Proof.FxfsTier1.hangul_vowel_jamo
