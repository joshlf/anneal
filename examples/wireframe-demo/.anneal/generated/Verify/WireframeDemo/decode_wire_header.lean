-- @anneal-def-id: wireframe_demo::decode_wire_header
import Trusted
import Mir.WireframeDemo.decode_wire_header
import Obligations.WireframeDemo.decode_wire_header
import Specs.WireframeDemo.decode_wire_header
import Proof.WireframeDemo.decode_wire_header

namespace Verify.WireframeDemo.decode_wire_header

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `wireframe_demo::decode_wire_header`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked verification certificate for `wireframe_demo::decode_wire_header`. -/
theorem verified : VerificationResult Obligations.WireframeDemo.decode_wire_header.claim :=
  Proof.WireframeDemo.decode_wire_header.verified

/-- Proposition verified by `Verify.WireframeDemo.decode_wire_header.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := VerificationResult Obligations.WireframeDemo.decode_wire_header.claim

end Verify.WireframeDemo.decode_wire_header
