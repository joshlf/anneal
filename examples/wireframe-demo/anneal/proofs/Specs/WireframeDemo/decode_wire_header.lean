import Trusted
import Mir.WireframeDemo.decode_wire_header
import Obligations.WireframeDemo.decode_wire_header

namespace Specs.WireframeDemo.decode_wire_header

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-!
Specification contract for `wireframe_demo::decode_wire_header` (Journey 2).

Universally quantifies over all `2^32` 4-byte `[u8; 4]` header arrays and
specifies that `decode_wire_header` executes without Undefined Behavior and
returns the little-endian 16-bit payload length `b2 + 256 * b3` for valid v1
headers (`b0 = 1`, `b1 <= 1`, and `b2 + 256 * b3 <= 1024`) and `0` otherwise.
-/

/-- Canonical `V2026_06_01` aggregate value encoding `[b0, b1, b2, b3] : [u8; 4]`. -/
def rawHeaderValue (b0 b1 b2 b3 : Nat) : Value :=
  .aggregate 0
    [ .scalar { bits := b0, sizeBytes := 1 }
    , .scalar { bits := b1, sizeBytes := 1 }
    , .scalar { bits := b2, sizeBytes := 1 }
    , .scalar { bits := b3, sizeBytes := 1 } ]

/-- Universal domain covering all `256^4 = 2^32` well-typed `[u8; 4]` inputs. -/
def rawHeaderDomain (args : List Value) : Prop :=
  ∃ b0 b1 b2 b3 : Nat,
    b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
      args = [rawHeaderValue b0 b1 b2 b3]

/-- Pure specification of the decoded 16-bit payload length for `[b0, b1, b2, b3]`. -/
def decodedPayloadLen (b0 b1 b2 b3 : Nat) : Nat :=
  if b0 == 1 && b1 <= 1 && b2 + 256 * b3 <= 1024 then
    b2 + 256 * b3
  else
    0

/-- Relational postcondition equating `ret` to `decodedPayloadLen b0 b1 b2 b3`. -/
def rawHeaderPost (args : List Value) (ret : Value) : Prop :=
  ∀ b0 b1 b2 b3 : Nat,
    b0 < 256 →
    b1 < 256 →
    b2 < 256 →
    b3 < 256 →
    args = [rawHeaderValue b0 b1 b2 b3] →
    ret = .scalar { bits := decodedPayloadLen b0 b1 b2 b3, sizeBytes := 2 }

/-- Normal-priority `ItemSpec` instance overriding `defaultSpec`. -/
instance : ItemSpec "wireframe_demo::decode_wire_header" :=
  Obligations.WireframeDemo.decode_wire_header.refineSpec
    rawHeaderDomain
    rawHeaderPost

end Specs.WireframeDemo.decode_wire_header
