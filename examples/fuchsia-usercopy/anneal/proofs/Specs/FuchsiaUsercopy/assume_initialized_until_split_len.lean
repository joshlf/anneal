-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FuchsiaUsercopy.assume_initialized_until_split_len
import Obligations.FuchsiaUsercopy.assume_initialized_until_split_len

namespace Specs.FuchsiaUsercopy.assume_initialized_until_split_len

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition over `(buf_len, initialized_until)` with `initialized_until <= buf_len`. -/
def pre (args : List Value) : Prop :=
  ∃ (buf_len init_until : Nat),
    init_until ≤ buf_len ∧
    buf_len < 18446744073709551616 ∧
    args =
      [ .scalar { bits := buf_len, sizeBytes := 8 }
      , .scalar { bits := init_until, sizeBytes := 8 } ]

/-- Exact postcondition: returns `(initialized_until, buf_len - initialized_until)`
    and conserves `init_len + uninit_len == buf_len`. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (buf_len init_until : Nat),
    args =
      [ .scalar { bits := buf_len, sizeBytes := 8 }
      , .scalar { bits := init_until, sizeBytes := 8 } ] →
    ret = .aggregate 0
      [ .scalar { bits := init_until, sizeBytes := 8 }
      , .scalar { bits := buf_len - init_until, sizeBytes := 8 } ] ∧
    init_until + (buf_len - init_until) = buf_len

instance : ItemSpec "fuchsia_usercopy::assume_initialized_until_split_len" where
  pre := pre
  post := post

instance : StatefulItemSpec "fuchsia_usercopy::assume_initialized_until_split_len" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FuchsiaUsercopy.assume_initialized_until_split_len
