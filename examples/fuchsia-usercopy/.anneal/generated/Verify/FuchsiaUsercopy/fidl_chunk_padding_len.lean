-- @anneal-def-id: fuchsia_usercopy::fidl_chunk_padding_len
import Trusted
import Mir.FuchsiaUsercopy.fidl_chunk_padding_len
import Obligations.FuchsiaUsercopy.fidl_chunk_padding_len
import Specs.FuchsiaUsercopy.fidl_chunk_padding_len
import Proof.FuchsiaUsercopy.fidl_chunk_padding_len

namespace Verify.FuchsiaUsercopy.fidl_chunk_padding_len

open Trusted.VerificationResult

/-!
Disposable verification assembly root for `fuchsia_usercopy::fidl_chunk_padding_len`.

This module is generated on every `cargo anneal` run and assembles the
active `ItemSpec` and proof witness at the audited
`VerificationResult` theorem boundary.
-/

/-- Kernel-checked stateful verification certificate for `fuchsia_usercopy::fidl_chunk_padding_len`. -/
theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.fidl_chunk_padding_len.statefulClaim :=
  Proof.FuchsiaUsercopy.fidl_chunk_padding_len.verified

/-- Proposition verified by `Verify.FuchsiaUsercopy.fidl_chunk_padding_len.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := StatefulVerificationResult Obligations.FuchsiaUsercopy.fidl_chunk_padding_len.statefulClaim

/-- Kernel-checked guard: the monomorphic signature-typed claims instantiate
    `Mir.FuchsiaUsercopy.fidl_chunk_padding_len.body` at `List.nil`, so they are only meaningful when its
    signature mentions no uninstantiated generic parameter. Generic items must
    be verified through `Obligations.FuchsiaUsercopy.fidl_chunk_padding_len.poly*Claim`. -/
theorem signatureMonomorphic :
    Trusted.VerificationResult.signatureIsMonomorphic Mir.FuchsiaUsercopy.fidl_chunk_padding_len.body = true := by
  decide

end Verify.FuchsiaUsercopy.fidl_chunk_padding_len
