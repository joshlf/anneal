-- @anneal-def-id: fuchsia_usercopy::hermetic_copy_bytes_copied
import Trusted
import Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied
import Obligations.FuchsiaUsercopy.hermetic_copy_bytes_copied
import Specs.FuchsiaUsercopy.hermetic_copy_bytes_copied
import Proof.FuchsiaUsercopy.hermetic_copy_bytes_copied

namespace Verify.FuchsiaUsercopy.hermetic_copy_bytes_copied

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `fuchsia_usercopy::hermetic_copy_bytes_copied`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked stateful verification certificate for `fuchsia_usercopy::hermetic_copy_bytes_copied`. -/
theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.hermetic_copy_bytes_copied.statefulClaim :=
  Proof.FuchsiaUsercopy.hermetic_copy_bytes_copied.verified

/-- Proposition verified by `Verify.FuchsiaUsercopy.hermetic_copy_bytes_copied.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := StatefulVerificationResult Obligations.FuchsiaUsercopy.hermetic_copy_bytes_copied.statefulClaim

/-- Kernel-checked guard: the monomorphic signature-typed claims instantiate
    `Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body` at `List.nil`, so they are only meaningful when its
    signature mentions no uninstantiated generic parameter. Generic items must
    be verified through `Obligations.FuchsiaUsercopy.hermetic_copy_bytes_copied.poly*Claim`. -/
theorem signatureMonomorphic :
    Trusted.VerificationResult.signatureIsMonomorphic Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body = true := by
  decide

end Verify.FuchsiaUsercopy.hermetic_copy_bytes_copied
