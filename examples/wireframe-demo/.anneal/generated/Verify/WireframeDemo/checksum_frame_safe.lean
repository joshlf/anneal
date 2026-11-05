-- @anneal-def-id: wireframe_demo::checksum_frame_safe
import Trusted
import Mir.WireframeDemo.checksum_frame_safe
import Obligations.WireframeDemo.checksum_frame_safe
import Specs.WireframeDemo.checksum_frame_safe
import Proof.WireframeDemo.checksum_frame_safe

namespace Verify.WireframeDemo.checksum_frame_safe

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `wireframe_demo::checksum_frame_safe`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked stateful verification certificate for `wireframe_demo::checksum_frame_safe`. -/
theorem verified : StatefulVerificationResult Obligations.WireframeDemo.checksum_frame_safe.statefulClaim :=
  Proof.WireframeDemo.checksum_frame_safe.verified

/-- Proposition verified by `Verify.WireframeDemo.checksum_frame_safe.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := StatefulVerificationResult Obligations.WireframeDemo.checksum_frame_safe.statefulClaim

/-- Kernel-checked guard: the monomorphic signature-typed claims instantiate
    `Mir.WireframeDemo.checksum_frame_safe.body` at `List.nil`, so they are only meaningful when its
    signature mentions no uninstantiated generic parameter. Generic items must
    be verified through `Obligations.WireframeDemo.checksum_frame_safe.poly*Claim`. -/
theorem signatureMonomorphic :
    Trusted.VerificationResult.signatureIsMonomorphic Mir.WireframeDemo.checksum_frame_safe.body = true := by
  decide

end Verify.WireframeDemo.checksum_frame_safe
