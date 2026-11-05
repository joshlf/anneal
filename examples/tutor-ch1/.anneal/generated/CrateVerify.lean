import Trusted
import Verify.FrameTutor.advance_offset
import Verify.FrameTutor.magic_version

namespace CrateVerify

open Trusted.VerificationResult

/-!
Disposable whole-crate verification rollup for `frame_tutor`.

Aggregates every captured subject item's kernel-checked `Verify.<Item>.verified`
certificate into a single `CrateVerificationResult` audited by `TrustedBoundary`.
-/

/-- Whole-crate verification claim inventory for `frame_tutor`. -/
def crateClaim : CrateClaim where
  crateName := "frame_tutor"
  mirDialect := "V2026_06_01"
  items := [
    { identity := {
        defPath := "frame_tutor::advance_offset"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "c064ac653b1017ecef6793068b2b5117841c410b331baa941c8b2e0b70525ec0"
      }
      certificate := Verify.FrameTutor.advance_offset.Certificate
    },
    { identity := {
        defPath := "frame_tutor::magic_version"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "780c6631a4b040182b8b8c398f7ce24a8a01877cb69bc48bae439ab8242d7450"
      }
      certificate := Verify.FrameTutor.magic_version.Certificate
    }
  ]

/-- Kernel-checked whole-crate verification certificate for `frame_tutor`. -/
theorem verified : CrateVerificationResult crateClaim :=
  { proof := And.intro (by intro h; nomatch h) (And.intro Verify.FrameTutor.advance_offset.verified (And.intro Verify.FrameTutor.magic_version.verified True.intro)) }

end CrateVerify
