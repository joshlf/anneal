import Trusted
import Mir.FrameTutor.pin_magic
import Obligations.FrameTutor.pin_magic

namespace Specs.FrameTutor.pin_magic

open Trusted.MirSemantics
open Trusted.VerificationResult

/-!
A vacuous specification: `pre := fun _ => False` collapses `MirContractSpec` to
`Partial.ub`, which every implementation refines. `cargo anneal lock-specs`
rejects it before writing a usable lock.
-/

instance : ItemSpec "frame_tutor::pin_magic" where
  pre := fun _ => False
  post := fun args ret => Obligations.FrameTutor.pin_magic.rustEnsures args ret

end Specs.FrameTutor.pin_magic
