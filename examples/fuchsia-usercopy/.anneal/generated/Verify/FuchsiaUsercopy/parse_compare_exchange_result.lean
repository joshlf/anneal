-- @anneal-def-id: fuchsia_usercopy::parse_compare_exchange_result
import Trusted
import Mir.FuchsiaUsercopy.parse_compare_exchange_result
import Obligations.FuchsiaUsercopy.parse_compare_exchange_result
import Specs.FuchsiaUsercopy.parse_compare_exchange_result
import Proof.FuchsiaUsercopy.parse_compare_exchange_result

namespace Verify.FuchsiaUsercopy.parse_compare_exchange_result

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `fuchsia_usercopy::parse_compare_exchange_result`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked stateful verification certificate for `fuchsia_usercopy::parse_compare_exchange_result`. -/
theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.parse_compare_exchange_result.statefulClaim :=
  Proof.FuchsiaUsercopy.parse_compare_exchange_result.verified

/-- Proposition verified by `Verify.FuchsiaUsercopy.parse_compare_exchange_result.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := StatefulVerificationResult Obligations.FuchsiaUsercopy.parse_compare_exchange_result.statefulClaim

/-- Kernel-checked guard: the monomorphic signature-typed claims instantiate
    `Mir.FuchsiaUsercopy.parse_compare_exchange_result.body` at `List.nil`, so they are only meaningful when its
    signature mentions no uninstantiated generic parameter. Generic items must
    be verified through `Obligations.FuchsiaUsercopy.parse_compare_exchange_result.poly*Claim`. -/
theorem signatureMonomorphic :
    Trusted.VerificationResult.signatureIsMonomorphic Mir.FuchsiaUsercopy.parse_compare_exchange_result.body = true := by
  decide

end Verify.FuchsiaUsercopy.parse_compare_exchange_result
