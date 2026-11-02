-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FuchsiaUsercopy.fidl_pointer_is_encoded_present
import Obligations.FuchsiaUsercopy.fidl_pointer_is_encoded_present

namespace Specs.FuchsiaUsercopy.fidl_pointer_is_encoded_present

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition over any 64-bit wire pointer word `encoded_u64`
    (`src/lib/fidl/rust_next/fidl_next_codec/src/wire/ptr.rs:28-41`). -/
def pre (args : List Value) : Prop :=
  ∃ (enc : Nat),
    enc < 18446744073709551616 ∧
    args = [ .scalar { bits := enc, sizeBytes := 8 } ]

/-- Exact postcondition: `ALLOC_ABSENT_U64` (`0`) -> `Some(false)`,
    `ALLOC_PRESENT_U64` (`u64::MAX = 18446744073709551615`) -> `Some(true)`,
    and all other values -> `None`. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (enc : Nat),
    args = [ .scalar { bits := enc, sizeBytes := 8 } ] →
    if enc = 0 then
      ret = .aggregate 1 [ .scalar { bits := 0, sizeBytes := 1 } ]
    else if enc = 18446744073709551615 then
      ret = .aggregate 1 [ .scalar { bits := 1, sizeBytes := 1 } ]
    else
      ret = .aggregate 0 []

instance : ItemSpec "fuchsia_usercopy::fidl_pointer_is_encoded_present" where
  pre := pre
  post := post

instance : StatefulItemSpec "fuchsia_usercopy::fidl_pointer_is_encoded_present" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FuchsiaUsercopy.fidl_pointer_is_encoded_present
