-- @anneal-def-id: wireframe_demo::checksum_frame_fast
import Trusted
import Mir.WireframeDemo.checksum_frame_fast
import Obligations.WireframeDemo.checksum_frame_fast
import Specs.WireframeDemo.checksum_frame_fast
import Proof.WireframeDemo.checksum_frame_fast

namespace Verify.WireframeDemo.checksum_frame_fast

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `wireframe_demo::checksum_frame_fast`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked behavioral-equivalence verification certificate for `wireframe_demo::checksum_frame_fast`. -/
theorem verified : StatefulEquivVerificationResult Obligations.WireframeDemo.checksum_frame_fast.equivClaim :=
  Proof.WireframeDemo.checksum_frame_fast.verified

/-- Proposition verified by `Verify.WireframeDemo.checksum_frame_fast.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := StatefulEquivVerificationResult Obligations.WireframeDemo.checksum_frame_fast.equivClaim

end Verify.WireframeDemo.checksum_frame_fast
