import Trusted
import Mir.FrameTutor.advance_offset
import Obligations.FrameTutor.advance_offset

namespace Specs.FrameTutor.advance_offset

open Trusted.MirSemantics
open Trusted.VerificationResult

/-!
Safe-function specification for `frame_tutor::advance_offset` (`#100`, `#125`).

Uses `Obligations.FrameTutor.advance_offset.refineSafeSpec` to separate the
safety domain (`advanceOffsetSafetyDomain`, which populates `.defined` of
`MirContractSpec`) from the functional precondition (`rustRequires` conjoined
with `offset = 2`, which guards `rustEnsures` and `ret = 6` inside `.val`).
-/

/-- Two-case safety domain covering both an in-contract input (`offset = 2`,
    where `offset < 4` holds and `advance_offset` returns `6`) and an
    out-of-contract overflowing input (`offset = 255`, where `offset < 4` is
    false and `offset + 4` panics safely with `TerminationKind.panic`
    without triggering Undefined Behavior). -/
def advanceOffsetSafetyDomain (args : List Value) : Prop :=
  Or
    (args = List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil)
    (args = List.cons (.scalar { bits := 255, sizeBytes := 1 }) List.nil)

instance : ItemSpec "frame_tutor::advance_offset" :=
  Obligations.FrameTutor.advance_offset.refineSafeSpec
    advanceOffsetSafetyDomain
    (fun args => args = List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil)
    (fun _ ret => ret = .scalar { bits := 6, sizeBytes := 1 })

end Specs.FrameTutor.advance_offset
