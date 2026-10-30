import Trusted
import Mir.FrameTutor.advance_offset
import Obligations.FrameTutor.advance_offset

namespace Specs.FrameTutor.advance_offset

open Trusted.MirSemantics
open Trusted.VerificationResult

/-!
Well-formedness-only specification for unannotated `frame_tutor::advance_offset`.

Constrains `.defined` (`pre`) to `advanceOffsetSafetyDomain` (covering both a
non-overflowing input `offset = 2` and an overflowing input `offset = 255`)
while keeping `.val` (`post`) as `defaultPost` (`True`), proving `MirNoUB`
without adding a functional `#[anneal_spec::spec]` contract in Rust.
-/

/-- Two-case safety domain covering both a non-overflowing input (`offset = 2`,
    which returns `6`) and an overflowing input (`offset = 255`, where
    `offset + 4` panics safely with `TerminationKind.panic` without triggering
    Undefined Behavior). -/
def advanceOffsetSafetyDomain (args : List Value) : Prop :=
  Or
    (args = List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil)
    (args = List.cons (.scalar { bits := 255, sizeBytes := 1 }) List.nil)

instance : ItemSpec "frame_tutor::advance_offset" where
  pre := advanceOffsetSafetyDomain
  post := Obligations.FrameTutor.advance_offset.defaultPost

end Specs.FrameTutor.advance_offset
