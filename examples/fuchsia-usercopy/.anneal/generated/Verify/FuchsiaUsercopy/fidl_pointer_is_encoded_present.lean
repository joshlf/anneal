-- @anneal-def-id: fuchsia_usercopy::fidl_pointer_is_encoded_present
import Trusted
import Mir.FuchsiaUsercopy.fidl_pointer_is_encoded_present
import Obligations.FuchsiaUsercopy.fidl_pointer_is_encoded_present
import Specs.FuchsiaUsercopy.fidl_pointer_is_encoded_present
import Proof.FuchsiaUsercopy.fidl_pointer_is_encoded_present

namespace Verify.FuchsiaUsercopy.fidl_pointer_is_encoded_present

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `fuchsia_usercopy::fidl_pointer_is_encoded_present`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked stateful verification certificate for `fuchsia_usercopy::fidl_pointer_is_encoded_present`. -/
theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.fidl_pointer_is_encoded_present.statefulClaim :=
  Proof.FuchsiaUsercopy.fidl_pointer_is_encoded_present.verified

/-- Proposition verified by `Verify.FuchsiaUsercopy.fidl_pointer_is_encoded_present.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := StatefulVerificationResult Obligations.FuchsiaUsercopy.fidl_pointer_is_encoded_present.statefulClaim

/-- Kernel-checked guard: the monomorphic signature-typed claims instantiate
    `Mir.FuchsiaUsercopy.fidl_pointer_is_encoded_present.body` at `List.nil`, so they are only meaningful when its
    signature mentions no uninstantiated generic parameter. Generic items must
    be verified through `Obligations.FuchsiaUsercopy.fidl_pointer_is_encoded_present.poly*Claim`. -/
theorem signatureMonomorphic :
    Trusted.VerificationResult.signatureIsMonomorphic Mir.FuchsiaUsercopy.fidl_pointer_is_encoded_present.body = true := by
  decide

end Verify.FuchsiaUsercopy.fidl_pointer_is_encoded_present
