import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.advance_offset
import Specs.FrameTutor.advance_offset
import Obligations.FrameTutor.advance_offset

namespace Proof.FrameTutor.advance_offset

open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.FrameTutor.advance_offset

/-!
Well-formedness (`MirNoUB`) proof for unannotated `frame_tutor::advance_offset`
using `verifyByWPSafe` (`mirSafePost`).
-/

theorem verified : VerificationResult Obligations.FrameTutor.advance_offset.claim :=
  verifyByWPSafe
    Obligations.FrameTutor.advance_offset.claim
    16
    (by
      intro args h_safe
      cases h_safe with
      | inl h2 =>
        subst h2
        exact True.intro
      | inr h255 =>
        subst h255
        exact True.intro)

end Proof.FrameTutor.advance_offset
