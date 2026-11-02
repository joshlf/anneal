-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied
import Obligations.FuchsiaUsercopy.hermetic_copy_bytes_copied

namespace Specs.FuchsiaUsercopy.hermetic_copy_bytes_copied

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition over `(dest_or_src_base, count, unread_address)`
    matching `do_hermetic_copy` (`src/starnix/lib/usercopy/src/lib.rs:247-278`):
    the assembly routine returns `unread_address` in `[base, base + count]`. -/
def pre (args : List Value) : Prop :=
  ∃ (base count unread : Nat),
    base ≤ unread ∧
    unread - base ≤ count ∧
    unread < 18446744073709551616 ∧
    count < 18446744073709551616 ∧
    args =
      [ .scalar { bits := base, sizeBytes := 8 }
      , .scalar { bits := count, sizeBytes := 8 }
      , .scalar { bits := unread, sizeBytes := 8 } ]

/-- Exact postcondition: `ret == unread_address - dest_or_src_base` and `ret <= count`. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (base count unread : Nat),
    args =
      [ .scalar { bits := base, sizeBytes := 8 }
      , .scalar { bits := count, sizeBytes := 8 }
      , .scalar { bits := unread, sizeBytes := 8 } ] →
    ret = .scalar { bits := unread - base, sizeBytes := 8 } ∧
    unread - base ≤ count

instance : ItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
  pre := pre
  post := post

instance : StatefulItemSpec "fuchsia_usercopy::hermetic_copy_bytes_copied" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FuchsiaUsercopy.hermetic_copy_bytes_copied
