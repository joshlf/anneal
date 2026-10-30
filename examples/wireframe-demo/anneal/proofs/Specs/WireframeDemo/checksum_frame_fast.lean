import Trusted
import Mir.WireframeDemo.checksum_frame_safe
import Mir.WireframeDemo.checksum_frame_fast
import Specs.WireframeDemo.checksum_frame_safe
import Obligations.WireframeDemo.checksum_frame_fast

namespace Specs.WireframeDemo.checksum_frame_fast

open Trusted.VerificationResult
open Specs.WireframeDemo.checksum_frame_safe

/-!
Program-to-program behavioral equivalence and total-correctness contract for
`wireframe_demo::checksum_frame_fast` (Journey 4).

Freezes `Mir.WireframeDemo.checksum_frame_safe.body` directly as `specBody` via
`StatefulEquivItemSpec` (`StatefulEquivVerificationResult`), requiring both:
1. `RefinesStatefulMir`: observation-erased Layer 1A `Partial` refinement of
   `checksum_frame_safe` across all `2^64` 8-byte `&[u8; 8]` frames, and
2. `TotalClaim.holds`: `TreeSafe` (`MirNoUB`), termination (`Productive` and
   `¬ MayDiverge`), panic-freedom, and `frame8Post` memory preservation.
-/

/-- Behavioral-equivalence specification pairing `checksum_frame_fast` against
`Mir.WireframeDemo.checksum_frame_safe.body` over `frame8Pre` and `frame8Post`. -/
instance : StatefulEquivItemSpec "wireframe_demo::checksum_frame_fast" :=
  Obligations.WireframeDemo.checksum_frame_fast.refineEquivSpec
    Mir.WireframeDemo.checksum_frame_safe.body
    frame8Pre
    frame8Post

end Specs.WireframeDemo.checksum_frame_fast
