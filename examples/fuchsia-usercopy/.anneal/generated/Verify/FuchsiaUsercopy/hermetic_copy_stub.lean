-- @anneal-def-id: fuchsia_usercopy::hermetic_copy_stub
import Trusted
import Mir.FuchsiaUsercopy.hermetic_copy_stub
import Obligations.FuchsiaUsercopy.hermetic_copy_stub
import Specs.FuchsiaUsercopy.hermetic_copy_stub
import Proof.FuchsiaUsercopy.hermetic_copy_stub

namespace Verify.FuchsiaUsercopy.hermetic_copy_stub

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `fuchsia_usercopy::hermetic_copy_stub`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked scoped UB-exception verification certificate for `fuchsia_usercopy::hermetic_copy_stub`. -/
theorem verified : UbExceptionVerificationResult Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim :=
  Proof.FuchsiaUsercopy.hermetic_copy_stub.verified

/-- Proposition verified by `Verify.FuchsiaUsercopy.hermetic_copy_stub.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := UbExceptionVerificationResult Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim

/-- Kernel-checked guard: the monomorphic signature-typed claims instantiate
    `Mir.FuchsiaUsercopy.hermetic_copy_stub.body` at `List.nil`, so they are only meaningful when its
    signature mentions no uninstantiated generic parameter. Generic items must
    be verified through `Obligations.FuchsiaUsercopy.hermetic_copy_stub.poly*Claim`. -/
theorem signatureMonomorphic :
    Trusted.VerificationResult.signatureIsMonomorphic Mir.FuchsiaUsercopy.hermetic_copy_stub.body = true := by
  decide

end Verify.FuchsiaUsercopy.hermetic_copy_stub
