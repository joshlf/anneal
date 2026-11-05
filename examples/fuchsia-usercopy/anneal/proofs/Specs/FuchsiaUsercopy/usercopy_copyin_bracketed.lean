-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FuchsiaUsercopy.usercopy_copyin_bracketed
import Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed
import Obligations.FuchsiaUsercopy.hermetic_copy_stub
import Specs.FuchsiaUsercopy.hermetic_copy_stub

namespace Specs.FuchsiaUsercopy.usercopy_copyin_bracketed

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition over `(source_in_restricted_range, dest_len, fault_offset, normal_mode_dest_valid)`
    with `fault_offset <= dest_len`. -/
def pre (args : List Value) (mem : Memory) : Prop :=
  ∃ (in_range dest_len fo v : Nat),
    (in_range = 0 ∨ in_range = 1) ∧
    fo ≤ dest_len ∧
    (in_range = 0 ∨ v = 1) ∧
    dest_len < 18446744073709551616 ∧
    (v = 0 ∨ v = 1) ∧
    args =
      [ .scalar { bits := in_range, sizeBytes := 1 }
      , .scalar { bits := dest_len, sizeBytes := 8 }
      , .scalar { bits := fo, sizeBytes := 8 }
      , .scalar { bits := v, sizeBytes := 1 } ] ∧
    mem = emptyMemory

/-- Exact postcondition: when `source_in_restricted_range` is `true` (`1`),
    returns `(fault_offset, dest_len - fault_offset)`; when `false` (`0`),
    returns `(0, dest_len)`. -/
def post (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory) : Prop :=
  mem' = { mem with callees := mem'.callees, traitImpls := mem'.traitImpls, activeCallee := mem'.activeCallee } ∧
  ∀ (in_range dest_len fo v : Nat),
    args =
      [ .scalar { bits := in_range, sizeBytes := 1 }
      , .scalar { bits := dest_len, sizeBytes := 8 }
      , .scalar { bits := fo, sizeBytes := 8 }
      , .scalar { bits := v, sizeBytes := 1 } ] →
    if in_range = 1 then
      ret = .aggregate 0
        [ .scalar { bits := fo, sizeBytes := 8 }
        , .scalar { bits := dest_len - fo, sizeBytes := 8 } ]
    else
      ret = .aggregate 0
        [ .scalar { bits := 0, sizeBytes := 8 }
        , .scalar { bits := dest_len, sizeBytes := 8 } ]

instance : ModularItemSpec "fuchsia_usercopy::usercopy_copyin_bracketed" where
  envAssumed :=
    Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim.callContract.holdsOn
  pre := pre
  post := post

end Specs.FuchsiaUsercopy.usercopy_copyin_bracketed
