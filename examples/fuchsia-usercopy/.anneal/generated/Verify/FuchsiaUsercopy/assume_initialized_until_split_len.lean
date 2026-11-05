-- @anneal-def-id: fuchsia_usercopy::assume_initialized_until_split_len
import Trusted
import Mir.FuchsiaUsercopy.assume_initialized_until_split_len
import Obligations.FuchsiaUsercopy.assume_initialized_until_split_len
import Specs.FuchsiaUsercopy.assume_initialized_until_split_len
import Proof.FuchsiaUsercopy.assume_initialized_until_split_len

namespace Verify.FuchsiaUsercopy.assume_initialized_until_split_len

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `fuchsia_usercopy::assume_initialized_until_split_len`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked stateful verification certificate for `fuchsia_usercopy::assume_initialized_until_split_len`. -/
theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.assume_initialized_until_split_len.statefulClaim :=
  Proof.FuchsiaUsercopy.assume_initialized_until_split_len.verified

/-- Proposition verified by `Verify.FuchsiaUsercopy.assume_initialized_until_split_len.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := StatefulVerificationResult Obligations.FuchsiaUsercopy.assume_initialized_until_split_len.statefulClaim

/-- Kernel-checked guard: the monomorphic signature-typed claims instantiate
    `Mir.FuchsiaUsercopy.assume_initialized_until_split_len.body` at `List.nil`, so they are only meaningful when its
    signature mentions no uninstantiated generic parameter. Generic items must
    be verified through `Obligations.FuchsiaUsercopy.assume_initialized_until_split_len.poly*Claim`. -/
theorem signatureMonomorphic :
    Trusted.VerificationResult.signatureIsMonomorphic Mir.FuchsiaUsercopy.assume_initialized_until_split_len.body = true := by
  decide

end Verify.FuchsiaUsercopy.assume_initialized_until_split_len
