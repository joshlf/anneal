-- @anneal-def-id: fuchsia_usercopy::atomic_load_u32_unpack
import Trusted
import Mir.FuchsiaUsercopy.atomic_load_u32_unpack
import Obligations.FuchsiaUsercopy.atomic_load_u32_unpack
import Specs.FuchsiaUsercopy.atomic_load_u32_unpack
import Proof.FuchsiaUsercopy.atomic_load_u32_unpack

namespace Verify.FuchsiaUsercopy.atomic_load_u32_unpack

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `fuchsia_usercopy::atomic_load_u32_unpack`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked stateful verification certificate for `fuchsia_usercopy::atomic_load_u32_unpack`. -/
theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.atomic_load_u32_unpack.statefulClaim :=
  Proof.FuchsiaUsercopy.atomic_load_u32_unpack.verified

/-- Proposition verified by `Verify.FuchsiaUsercopy.atomic_load_u32_unpack.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := StatefulVerificationResult Obligations.FuchsiaUsercopy.atomic_load_u32_unpack.statefulClaim

/-- Kernel-checked guard: the monomorphic signature-typed claims instantiate
    `Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body` at `List.nil`, so they are only meaningful when its
    signature mentions no uninstantiated generic parameter. Generic items must
    be verified through `Obligations.FuchsiaUsercopy.atomic_load_u32_unpack.poly*Claim`. -/
theorem signatureMonomorphic :
    Trusted.VerificationResult.signatureIsMonomorphic Mir.FuchsiaUsercopy.atomic_load_u32_unpack.body = true := by
  decide

end Verify.FuchsiaUsercopy.atomic_load_u32_unpack
