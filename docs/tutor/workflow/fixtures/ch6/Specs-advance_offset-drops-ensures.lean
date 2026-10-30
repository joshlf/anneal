import Trusted
import Mir.FrameTutor.advance_offset
import Obligations.FrameTutor.advance_offset

namespace Specs.FrameTutor.advance_offset

open Trusted.MirSemantics
open Trusted.VerificationResult

/-!
A specification override that silently drops the Rust
`#[anneal_spec::spec(ensures: ...)]` clause of `advance_offset`: it mentions
neither `rustEnsures` nor any `refine*` combinator, so `cargo anneal lock-specs`
rejects it.
-/

instance : ItemSpec "frame_tutor::advance_offset" where
  pre args := args = List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil
  post _ ret := ret = .scalar { bits := 6, sizeBytes := 1 }

end Specs.FrameTutor.advance_offset
