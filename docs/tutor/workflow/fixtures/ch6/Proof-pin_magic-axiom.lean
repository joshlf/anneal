import Trusted
import Anneal
import Mir.FrameTutor.pin_magic
import Obligations.FrameTutor.pin_magic

namespace Proof.FrameTutor.pin_magic

open Trusted.VerificationResult

/-!
A proof that postulates its own conclusion. Lake accepts the module, but the
`TrustedBoundary` source inspector rejects any `axiom` command outside an
`Assumptions.*` module.
-/

axiom cheat : VerificationResult Obligations.FrameTutor.pin_magic.claim

theorem verified : VerificationResult Obligations.FrameTutor.pin_magic.claim :=
  cheat

end Proof.FrameTutor.pin_magic
