import Trusted
import Mir.WireframeDemo.parse_compression_flag
import Obligations.WireframeDemo.parse_compression_flag

namespace Specs.WireframeDemo.parse_compression_flag

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-!
Safe-function total-safety review contract for `wireframe_demo::parse_compression_flag`
(Journey 3B, `#125`).

Uses `Obligations.WireframeDemo.parse_compression_flag.refineSafeSpec`
(`MirContractHoldsWithSafety`) to place all `256` valid `u8` inputs in the
Smyth `.defined` safety domain (`MirNoUB`) while guarding the functional
`#[anneal_spec::spec]` `ensures` clause behind `rustRequires` (`(b & 1) == b`).
Any internal `unsafe` shortcut that triggers Undefined Behavior outside
`requires` (such as `transmute::<u8, bool>(2)`) is therefore rejected.
-/

/-- All `256` well-typed `u8` scalar inputs (`0..=255`). -/
def u8SafetyDomain (args : List Value) : Prop :=
  ∃ b : Nat, b < 256 ∧ args = [.scalar { bits := b, sizeBytes := 1 }]

/-- Functional Lean postcondition under `rustRequires` (`b = 0` or `b = 1`). -/
def compressionFlagPost (args : List Value) (ret : Value) : Prop :=
  ∀ b : Nat,
    args = [.scalar { bits := b, sizeBytes := 1 }] →
    ret = .scalar { bits := if b == 1 then 1 else 0, sizeBytes := 1 }

/-- Safe-function `ItemSpec` enforcing `MirNoUB` across all `256` `u8` inputs. -/
instance : ItemSpec "wireframe_demo::parse_compression_flag" :=
  Obligations.WireframeDemo.parse_compression_flag.refineSafeSpec
    u8SafetyDomain
    (fun _ => True)
    compressionFlagPost

end Specs.WireframeDemo.parse_compression_flag
