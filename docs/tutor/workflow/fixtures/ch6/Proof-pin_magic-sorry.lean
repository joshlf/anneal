import Trusted
import Anneal
import Mir.FrameTutor.pin_magic
import Obligations.FrameTutor.pin_magic

namespace Proof.FrameTutor.pin_magic

open Trusted.VerificationResult

/-!
An incomplete proof. Lake accepts the module with a warning, but the
`TrustedBoundary` audit finds `sorryAx` in the constant closure of
`Verify.FrameTutor.pin_magic.verified` and rejects it.
-/

theorem verified : VerificationResult Obligations.FrameTutor.pin_magic.claim := by
  sorry

end Proof.FrameTutor.pin_magic
