import Trusted
import Obligations.FrameTutor.pin_magic
import Assumptions.FrameTutor.pin_magic

namespace Proof.FrameTutor.pin_magic

open Trusted.VerificationResult

theorem verified : VerificationResult Obligations.FrameTutor.pin_magic.claim :=
  Assumptions.FrameTutor.pin_magic.assumed_pin_magic

end Proof.FrameTutor.pin_magic
