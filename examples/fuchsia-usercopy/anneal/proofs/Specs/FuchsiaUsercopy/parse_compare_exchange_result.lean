-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FuchsiaUsercopy.parse_compare_exchange_result
import Obligations.FuchsiaUsercopy.parse_compare_exchange_result

namespace Specs.FuchsiaUsercopy.parse_compare_exchange_result

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition over `(expected : u32, value_or_error : u64)` matching
    `Usercopy::parse_compare_exchange_result` (`src/starnix/lib/usercopy/src/lib.rs:645-654`). -/
def pre (args : List Value) : Prop :=
  ∃ (exp v : Nat),
    exp < 4294967296 ∧
    v < 18446744073709551616 ∧
    args =
      [ .scalar { bits := exp, sizeBytes := 4 }
      , .scalar { bits := v, sizeBytes := 8 } ]

/-- Exact postcondition: decodes `0 -> 0` (`Ok(Err(expected))`), `1 -> 1` (`Ok(Ok(expected))`),
    and any fault value `v >= 2 -> 2` (`Err(())`). -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (exp v : Nat),
    args =
      [ .scalar { bits := exp, sizeBytes := 4 }
      , .scalar { bits := v, sizeBytes := 8 } ] →
    if v = 0 then
      ret = .scalar { bits := 0, sizeBytes := 1 }
    else if v = 1 then
      ret = .scalar { bits := 1, sizeBytes := 1 }
    else
      ret = .scalar { bits := 2, sizeBytes := 1 }

instance : ItemSpec "fuchsia_usercopy::parse_compare_exchange_result" where
  pre := pre
  post := post

instance : StatefulItemSpec "fuchsia_usercopy::parse_compare_exchange_result" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FuchsiaUsercopy.parse_compare_exchange_result
