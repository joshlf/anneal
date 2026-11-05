-- @anneal-def-id: wireframe_demo::advance_cursor
import Trusted
import Mir.WireframeDemo.advance_cursor
import Obligations.WireframeDemo.advance_cursor
import Specs.WireframeDemo.advance_cursor
import Proof.WireframeDemo.advance_cursor

namespace Verify.WireframeDemo.advance_cursor

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `wireframe_demo::advance_cursor`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked stateful verification certificate for `wireframe_demo::advance_cursor`. -/
theorem verified : StatefulVerificationResult Obligations.WireframeDemo.advance_cursor.statefulClaim :=
  Proof.WireframeDemo.advance_cursor.verified

/-- Proposition verified by `Verify.WireframeDemo.advance_cursor.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := StatefulVerificationResult Obligations.WireframeDemo.advance_cursor.statefulClaim

/-- Kernel-checked guard: the monomorphic signature-typed claims instantiate
    `Mir.WireframeDemo.advance_cursor.body` at `List.nil`, so they are only meaningful when its
    signature mentions no uninstantiated generic parameter. Generic items must
    be verified through `Obligations.WireframeDemo.advance_cursor.poly*Claim`. -/
theorem signatureMonomorphic :
    Trusted.VerificationResult.signatureIsMonomorphic Mir.WireframeDemo.advance_cursor.body = true := by
  decide

end Verify.WireframeDemo.advance_cursor
