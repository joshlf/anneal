-- @anneal-def-id: wireframe_demo::clamp_payload_window
import Trusted
import Mir.WireframeDemo.clamp_payload_window
import Obligations.WireframeDemo.clamp_payload_window
import Proof.WireframeDemo.clamp_payload_window

namespace Verify.WireframeDemo.clamp_payload_window

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `wireframe_demo::clamp_payload_window`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked verification certificate for `wireframe_demo::clamp_payload_window`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.clamp_payload_window.claim :=
  Proof.WireframeDemo.clamp_payload_window.verified

/-- Proposition verified by `Verify.WireframeDemo.clamp_payload_window.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := VerificationResult Obligations.WireframeDemo.clamp_payload_window.claim

end Verify.WireframeDemo.clamp_payload_window
