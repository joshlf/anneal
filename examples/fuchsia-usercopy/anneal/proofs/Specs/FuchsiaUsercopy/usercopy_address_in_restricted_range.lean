-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FuchsiaUsercopy.usercopy_address_in_restricted_range
import Obligations.FuchsiaUsercopy.usercopy_address_in_restricted_range

namespace Specs.FuchsiaUsercopy.usercopy_address_in_restricted_range

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition over `(addr, range_start, range_end)` with `range_start <= range_end`. -/
def pre (args : List Value) : Prop :=
  ∃ (addr rs re : Nat),
    rs ≤ re ∧
    addr < 18446744073709551616 ∧
    re < 18446744073709551616 ∧
    args =
      [ .scalar { bits := addr, sizeBytes := 8 }
      , .scalar { bits := rs, sizeBytes := 8 }
      , .scalar { bits := re, sizeBytes := 8 } ]

/-- Exact postcondition: returns `true` (`1`) iff `addr != 0 ∧ range_start <= addr ∧ addr < range_end`,
    and always rejects `addr == 0` (`0`) to avoid the fault-encoding collision. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (addr rs re : Nat),
    args =
      [ .scalar { bits := addr, sizeBytes := 8 }
      , .scalar { bits := rs, sizeBytes := 8 }
      , .scalar { bits := re, sizeBytes := 8 } ] →
    (if addr ≠ 0 ∧ rs ≤ addr ∧ addr < re then
      ret = .scalar { bits := 1, sizeBytes := 1 }
    else
      ret = .scalar { bits := 0, sizeBytes := 1 }) ∧
    (addr = 0 → ret = .scalar { bits := 0, sizeBytes := 1 })

instance : ItemSpec "fuchsia_usercopy::usercopy_address_in_restricted_range" where
  pre := pre
  post := post

instance : StatefulItemSpec "fuchsia_usercopy::usercopy_address_in_restricted_range" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FuchsiaUsercopy.usercopy_address_in_restricted_range
