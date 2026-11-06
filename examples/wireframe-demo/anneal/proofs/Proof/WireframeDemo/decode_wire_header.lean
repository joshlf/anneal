import Trusted
import Mir.WireframeDemo.decode_wire_header
import Obligations.WireframeDemo.decode_wire_header

namespace Proof.WireframeDemo.decode_wire_header

open Trusted.VerificationResult

theorem verified :
    VerificationResult Obligations.WireframeDemo.decode_wire_header.claim := by
  sorry

end Proof.WireframeDemo.decode_wire_header
