import Trusted
import Verify.FuchsiaUsercopy.assume_initialized_until_split_len
import Verify.FuchsiaUsercopy.atomic_load_u32_unpack
import Verify.FuchsiaUsercopy.fidl_chunk_padding_len
import Verify.FuchsiaUsercopy.fidl_pointer_is_encoded_present
import Verify.FuchsiaUsercopy.hermetic_copy_bytes_copied
import Verify.FuchsiaUsercopy.hermetic_copy_stub
import Verify.FuchsiaUsercopy.parse_compare_exchange_result
import Verify.FuchsiaUsercopy.usercopy_address_in_restricted_range
import Verify.FuchsiaUsercopy.usercopy_copyin_bracketed

namespace CrateVerify

open Trusted.VerificationResult

/-!
Disposable whole-crate verification rollup for `fuchsia_usercopy`.

Aggregates every captured subject item's kernel-checked `Verify.<Item>.verified`
certificate into a single `CrateVerificationResult` audited by `TrustedBoundary`.
-/

/-- Whole-crate verification claim inventory for `fuchsia_usercopy`. -/
def crateClaim : CrateClaim where
  crateName := "fuchsia_usercopy"
  mirDialect := "V2026_06_01"
  items := [
    { identity := {
        defPath := "fuchsia_usercopy::assume_initialized_until_split_len"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "baa4e2ac13d58b762c15dd9374dcfedfca445fd579e5e5b5254b254df0f1f0a2"
      }
      certificate := Verify.FuchsiaUsercopy.assume_initialized_until_split_len.Certificate
    },
    { identity := {
        defPath := "fuchsia_usercopy::atomic_load_u32_unpack"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "6bd09bd4b438c72708fd720556651681ecffef2bf9c600d2fbafa7f0df7b5f7a"
      }
      certificate := Verify.FuchsiaUsercopy.atomic_load_u32_unpack.Certificate
    },
    { identity := {
        defPath := "fuchsia_usercopy::fidl_chunk_padding_len"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "e9e904f5c631ac91daf13abf84f47f681583ae089f5559e3e25f8952c03500fa"
      }
      certificate := Verify.FuchsiaUsercopy.fidl_chunk_padding_len.Certificate
    },
    { identity := {
        defPath := "fuchsia_usercopy::fidl_pointer_is_encoded_present"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "2947c6b777640d3a93cf0491137ef7f149846d32037d573ea96eee2290ec2918"
      }
      certificate := Verify.FuchsiaUsercopy.fidl_pointer_is_encoded_present.Certificate
    },
    { identity := {
        defPath := "fuchsia_usercopy::hermetic_copy_bytes_copied"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "0f1dfe1ad297e374dba6dfde9107983ed93e5c514e8102fcfabda01b83ffa64d"
      }
      certificate := Verify.FuchsiaUsercopy.hermetic_copy_bytes_copied.Certificate
    },
    { identity := {
        defPath := "fuchsia_usercopy::hermetic_copy_stub"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "beb13a78638d7fa86f668e7a83ea79e5eda35964546a5474fdd76593d596536c"
      }
      certificate := Verify.FuchsiaUsercopy.hermetic_copy_stub.Certificate
    },
    { identity := {
        defPath := "fuchsia_usercopy::parse_compare_exchange_result"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "3f1be2c027519b3ee19697d1faf4ffdef53be663d62703f5ffeea561dc4bac5a"
      }
      certificate := Verify.FuchsiaUsercopy.parse_compare_exchange_result.Certificate
    },
    { identity := {
        defPath := "fuchsia_usercopy::usercopy_address_in_restricted_range"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "d7db282f25b499dcffd2360a9af88c99a8414b4d1ad9b139009b14f1bd9e8038"
      }
      certificate := Verify.FuchsiaUsercopy.usercopy_address_in_restricted_range.Certificate
    },
    { identity := {
        defPath := "fuchsia_usercopy::usercopy_copyin_bracketed"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "7db6b31cecf5d564b6c285c9cc21c6b6007ccdcc47ec2d951e43ca51507c88c7"
      }
      certificate := Verify.FuchsiaUsercopy.usercopy_copyin_bracketed.Certificate
    }
  ]

/-- Kernel-checked whole-crate verification certificate for `fuchsia_usercopy`. -/
theorem verified : CrateVerificationResult crateClaim :=
  { proof := And.intro (by intro h; nomatch h) (And.intro Verify.FuchsiaUsercopy.assume_initialized_until_split_len.verified (And.intro Verify.FuchsiaUsercopy.atomic_load_u32_unpack.verified (And.intro Verify.FuchsiaUsercopy.fidl_chunk_padding_len.verified (And.intro Verify.FuchsiaUsercopy.fidl_pointer_is_encoded_present.verified (And.intro Verify.FuchsiaUsercopy.hermetic_copy_bytes_copied.verified (And.intro Verify.FuchsiaUsercopy.hermetic_copy_stub.verified (And.intro Verify.FuchsiaUsercopy.parse_compare_exchange_result.verified (And.intro Verify.FuchsiaUsercopy.usercopy_address_in_restricted_range.verified (And.intro Verify.FuchsiaUsercopy.usercopy_copyin_bracketed.verified True.intro))))))))) }

end CrateVerify
