-- @anneal-def-id: wireframe_demo::frame_total_len
import Trusted
import Mir.WireframeDemo.frame_total_len
import Obligations.WireframeDemo.frame_total_len
import Proof.WireframeDemo.frame_total_len

namespace Verify.WireframeDemo.frame_total_len

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `wireframe_demo::frame_total_len`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked verification certificate for `wireframe_demo::frame_total_len`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.frame_total_len.claim :=
  Proof.WireframeDemo.frame_total_len.verified

/-- Proposition verified by `Verify.WireframeDemo.frame_total_len.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := VerificationResult Obligations.WireframeDemo.frame_total_len.claim

end Verify.WireframeDemo.frame_total_len
