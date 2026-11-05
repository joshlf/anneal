-- @anneal-def-id: wireframe_demo::parse_compression_flag
import Trusted
import Mir.WireframeDemo.parse_compression_flag
import Obligations.WireframeDemo.parse_compression_flag
import Specs.WireframeDemo.parse_compression_flag
import Proof.WireframeDemo.parse_compression_flag

namespace Verify.WireframeDemo.parse_compression_flag

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `wireframe_demo::parse_compression_flag`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked verification certificate for `wireframe_demo::parse_compression_flag`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.parse_compression_flag.claim :=
  Proof.WireframeDemo.parse_compression_flag.verified

/-- Proposition verified by `Verify.WireframeDemo.parse_compression_flag.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := VerificationResult Obligations.WireframeDemo.parse_compression_flag.claim

end Verify.WireframeDemo.parse_compression_flag
