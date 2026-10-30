import Trusted
import Mir.FrameTutor.pin_magic
import Obligations.FrameTutor.pin_magic

namespace Specs.FrameTutor.pin_magic

open Trusted.MirSemantics
open Trusted.VerificationResult

/-!
A specification override added after `cargo anneal lock-specs`. Its contents
are irrelevant: `cargo anneal agent-verify` rejects the file because no digest
for it exists in `.anneal/spec-lock.json`.
-/

instance : ItemSpec "frame_tutor::pin_magic" :=
  Obligations.FrameTutor.pin_magic.refineSpec
    (fun _ => True)
    (fun _ _ => True)

end Specs.FrameTutor.pin_magic
