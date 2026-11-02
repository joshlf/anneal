-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FuchsiaUsercopy.atomic_load_u32_unpack
import Obligations.FuchsiaUsercopy.atomic_load_u32_unpack

namespace Specs.FuchsiaUsercopy.atomic_load_u32_unpack

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition over any 64-bit `value_or_error` returned by
    `atomic_load_u32_{relaxed,acquire}` (`src/starnix/lib/usercopy/src/lib.rs:554-565`). -/
def pre (args : List Value) : Prop :=
  ∃ (v : Nat),
    v < 18446744073709551616 ∧
    args = [ .scalar { bits := v, sizeBytes := 8 } ]

/-- Exact postcondition: returns `(true, v as u32)` when `v >> 32 == 0` (`v < 2^32`,
    i.e. `v & 0xFFFFFFFF00000000 == 0`), and `(false, 0)` when the upper 32 error bits
    are non-zero (`ATOMIC_ERROR_MASK`). -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (v : Nat),
    args = [ .scalar { bits := v, sizeBytes := 8 } ] →
    if v / 4294967296 = 0 then
      ret = .aggregate 0
        [ .scalar { bits := 1, sizeBytes := 1 }
        , .scalar { bits := v % 4294967296, sizeBytes := 4 } ]
    else
      ret = .aggregate 0
        [ .scalar { bits := 0, sizeBytes := 1 }
        , .scalar { bits := 0, sizeBytes := 4 } ]

instance : ItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
  pre := pre
  post := post

instance : StatefulItemSpec "fuchsia_usercopy::atomic_load_u32_unpack" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FuchsiaUsercopy.atomic_load_u32_unpack
