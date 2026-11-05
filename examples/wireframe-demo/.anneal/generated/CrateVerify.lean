import Trusted
import Verify.WireframeDemo.WIRE_VERSION_V1
import Verify.WireframeDemo.advance_cursor
import Verify.WireframeDemo.checksum_frame_fast
import Verify.WireframeDemo.checksum_frame_safe
import Verify.WireframeDemo.clamp_payload_window
import Verify.WireframeDemo.decode_wire_header
import Verify.WireframeDemo.frame_total_len
import Verify.WireframeDemo.parse_compression_flag
import Verify.WireframeDemo.wire_protocol_version

namespace CrateVerify

open Trusted.VerificationResult

/-!
Disposable whole-crate verification rollup for `wireframe_demo`.

Aggregates every captured subject item's kernel-checked `Verify.<Item>.verified`
certificate into a single `CrateVerificationResult` audited by `TrustedBoundary`.
-/

/-- Whole-crate verification claim inventory for `wireframe_demo`. -/
def crateClaim : CrateClaim where
  crateName := "wireframe_demo"
  mirDialect := "V2026_06_01"
  items := [
    { identity := {
        defPath := "wireframe_demo::WIRE_VERSION_V1"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "2fe3abbb296b8801fc15385f85e92b5791f55f8aa081e1b525eaca0329246e75"
      }
      certificate := Verify.WireframeDemo.WIRE_VERSION_V1.Certificate
    },
    { identity := {
        defPath := "wireframe_demo::advance_cursor"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "07c4bf31bdfd3fa80b0b7519b4302fee8418fb273c2577ede0df296233088f11"
      }
      certificate := Verify.WireframeDemo.advance_cursor.Certificate
    },
    { identity := {
        defPath := "wireframe_demo::checksum_frame_fast"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "86ad11eaeef92bfcaf2410e7f9c25a8a60decef1a87de8a11dd792d772e3e2e5"
      }
      certificate := Verify.WireframeDemo.checksum_frame_fast.Certificate
    },
    { identity := {
        defPath := "wireframe_demo::checksum_frame_safe"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "573cc30983305c30a607f37368a7b29ed6f628ac43ced38900212e5892543b91"
      }
      certificate := Verify.WireframeDemo.checksum_frame_safe.Certificate
    },
    { identity := {
        defPath := "wireframe_demo::clamp_payload_window"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "3fb7e940b44f292e61bdf04960d8476356bb6e56ac777e7b63935ef14fdfd7a1"
      }
      certificate := Verify.WireframeDemo.clamp_payload_window.Certificate
    },
    { identity := {
        defPath := "wireframe_demo::decode_wire_header"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "e2a8f3766453b915b447a6fb76fc7c3465346b64f091450205e7e9ca6345f3e3"
      }
      certificate := Verify.WireframeDemo.decode_wire_header.Certificate
    },
    { identity := {
        defPath := "wireframe_demo::frame_total_len"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "8e5807f06c142b967b6401d1af0d1ab334fd5ceb8efc1b0ce97de504925daf53"
      }
      certificate := Verify.WireframeDemo.frame_total_len.Certificate
    },
    { identity := {
        defPath := "wireframe_demo::parse_compression_flag"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "767b99f2b1a53d8f1c1deb1cbd03ac966b48cc9aa3ad7aa660458aeb2f6681c0"
      }
      certificate := Verify.WireframeDemo.parse_compression_flag.Certificate
    },
    { identity := {
        defPath := "wireframe_demo::wire_protocol_version"
        mirDialect := "V2026_06_01"
        mirModuleSha256 := "a8db7ee2b93488797d7066b1aeaf28bd5a9c5d8832fe02e38c0f3fe7a906e0dd"
      }
      certificate := Verify.WireframeDemo.wire_protocol_version.Certificate
    }
  ]

/-- Kernel-checked whole-crate verification certificate for `wireframe_demo`. -/
theorem verified : CrateVerificationResult crateClaim :=
  { proof := And.intro (by intro h; nomatch h) (And.intro Verify.WireframeDemo.WIRE_VERSION_V1.verified (And.intro Verify.WireframeDemo.advance_cursor.verified (And.intro Verify.WireframeDemo.checksum_frame_fast.verified (And.intro Verify.WireframeDemo.checksum_frame_safe.verified (And.intro Verify.WireframeDemo.clamp_payload_window.verified (And.intro Verify.WireframeDemo.decode_wire_header.verified (And.intro Verify.WireframeDemo.frame_total_len.verified (And.intro Verify.WireframeDemo.parse_compression_flag.verified (And.intro Verify.WireframeDemo.wire_protocol_version.verified True.intro))))))))) }

end CrateVerify
