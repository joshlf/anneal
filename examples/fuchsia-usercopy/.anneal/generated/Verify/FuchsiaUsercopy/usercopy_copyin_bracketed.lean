-- @anneal-def-id: fuchsia_usercopy::usercopy_copyin_bracketed
import Trusted
import Mir.FuchsiaUsercopy.usercopy_copyin_bracketed
import Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed
import Specs.FuchsiaUsercopy.usercopy_copyin_bracketed
import Proof.FuchsiaUsercopy.usercopy_copyin_bracketed

namespace Verify.FuchsiaUsercopy.usercopy_copyin_bracketed

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `fuchsia_usercopy::usercopy_copyin_bracketed`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked modular verification certificate for `fuchsia_usercopy::usercopy_copyin_bracketed`. -/
theorem verified : ModularVerificationResult Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed.modularClaim :=
  Proof.FuchsiaUsercopy.usercopy_copyin_bracketed.verified

/-- Proposition verified by `Verify.FuchsiaUsercopy.usercopy_copyin_bracketed.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := ModularVerificationResult Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed.modularClaim

/-- Kernel-checked guard: the monomorphic signature-typed claims instantiate
    `Mir.FuchsiaUsercopy.usercopy_copyin_bracketed.body` at `List.nil`, so they are only meaningful when its
    signature mentions no uninstantiated generic parameter. Generic items must
    be verified through `Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed.poly*Claim`. -/
theorem signatureMonomorphic :
    Trusted.VerificationResult.signatureIsMonomorphic Mir.FuchsiaUsercopy.usercopy_copyin_bracketed.body = true := by
  decide

end Verify.FuchsiaUsercopy.usercopy_copyin_bracketed
