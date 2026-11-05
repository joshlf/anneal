-- @anneal-def-id: wireframe_demo::WIRE_VERSION_V1
import Trusted
import Anneal
import Mir.WireframeDemo.WIRE_VERSION_V1
import Obligations.WireframeDemo.WIRE_VERSION_V1

namespace Verify.WireframeDemo.WIRE_VERSION_V1

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `wireframe_demo::WIRE_VERSION_V1`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Low-priority fallback `ItemProof` instance attempting bounded
    `WP` discharge when no authored `Proof.WireframeDemo.WIRE_VERSION_V1` module exists on
    disk. -/
instance (priority := low) defaultProof :
    ItemProof "wireframe_demo::WIRE_VERSION_V1" Obligations.WireframeDemo.WIRE_VERSION_V1.claim where
  verified :=
    Anneal.Rustc.V2026_06_01.SymbolicEval.verifyByWP Obligations.WireframeDemo.WIRE_VERSION_V1.claim 64 (by
      intro _ _
      exact True.intro)

/-- Kernel-checked verification certificate for `wireframe_demo::WIRE_VERSION_V1`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.WIRE_VERSION_V1.claim :=
  (inferInstance : ItemProof "wireframe_demo::WIRE_VERSION_V1" Obligations.WireframeDemo.WIRE_VERSION_V1.claim).verified

/-- Proposition verified by `Verify.WireframeDemo.WIRE_VERSION_V1.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := VerificationResult Obligations.WireframeDemo.WIRE_VERSION_V1.claim

end Verify.WireframeDemo.WIRE_VERSION_V1
