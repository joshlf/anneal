-- @anneal-def-id: wireframe_demo::wire_protocol_version
import Trusted
import Anneal
import Mir.WireframeDemo.wire_protocol_version
import Obligations.WireframeDemo.wire_protocol_version

namespace Verify.WireframeDemo.wire_protocol_version

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `wireframe_demo::wire_protocol_version`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Low-priority fallback `ItemProof` instance attempting bounded
    `WP` discharge when no authored `Proof.WireframeDemo.wire_protocol_version` module exists on
    disk. -/
instance (priority := low) defaultProof :
    ItemProof "wireframe_demo::wire_protocol_version" Obligations.WireframeDemo.wire_protocol_version.claim where
  verified :=
    Anneal.Rustc.V2026_06_01.SymbolicEval.verifyByWP Obligations.WireframeDemo.wire_protocol_version.claim 64 (by
      intro _ _
      exact True.intro)

/-- Kernel-checked verification certificate for `wireframe_demo::wire_protocol_version`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.wire_protocol_version.claim :=
  (inferInstance : ItemProof "wireframe_demo::wire_protocol_version" Obligations.WireframeDemo.wire_protocol_version.claim).verified

/-- Proposition verified by `Verify.WireframeDemo.wire_protocol_version.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := VerificationResult Obligations.WireframeDemo.wire_protocol_version.claim

end Verify.WireframeDemo.wire_protocol_version
