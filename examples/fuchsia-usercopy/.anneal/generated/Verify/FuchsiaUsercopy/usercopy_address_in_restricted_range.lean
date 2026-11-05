-- @anneal-def-id: fuchsia_usercopy::usercopy_address_in_restricted_range
import Trusted
import Mir.FuchsiaUsercopy.usercopy_address_in_restricted_range
import Obligations.FuchsiaUsercopy.usercopy_address_in_restricted_range
import Specs.FuchsiaUsercopy.usercopy_address_in_restricted_range
import Proof.FuchsiaUsercopy.usercopy_address_in_restricted_range

namespace Verify.FuchsiaUsercopy.usercopy_address_in_restricted_range

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `fuchsia_usercopy::usercopy_address_in_restricted_range`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked stateful verification certificate for `fuchsia_usercopy::usercopy_address_in_restricted_range`. -/
theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.usercopy_address_in_restricted_range.statefulClaim :=
  Proof.FuchsiaUsercopy.usercopy_address_in_restricted_range.verified

/-- Proposition verified by `Verify.FuchsiaUsercopy.usercopy_address_in_restricted_range.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := StatefulVerificationResult Obligations.FuchsiaUsercopy.usercopy_address_in_restricted_range.statefulClaim

/-- Kernel-checked guard: the monomorphic signature-typed claims instantiate
    `Mir.FuchsiaUsercopy.usercopy_address_in_restricted_range.body` at `List.nil`, so they are only meaningful when its
    signature mentions no uninstantiated generic parameter. Generic items must
    be verified through `Obligations.FuchsiaUsercopy.usercopy_address_in_restricted_range.poly*Claim`. -/
theorem signatureMonomorphic :
    Trusted.VerificationResult.signatureIsMonomorphic Mir.FuchsiaUsercopy.usercopy_address_in_restricted_range.body = true := by
  decide

end Verify.FuchsiaUsercopy.usercopy_address_in_restricted_range
