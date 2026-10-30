import Trusted
import Obligations.FrameTutor.pin_magic

namespace Assumptions.FrameTutor.pin_magic

open Trusted.VerificationResult

axiom assumed_pin_magic :
  VerificationResult Obligations.FrameTutor.pin_magic.claim

end Assumptions.FrameTutor.pin_magic
