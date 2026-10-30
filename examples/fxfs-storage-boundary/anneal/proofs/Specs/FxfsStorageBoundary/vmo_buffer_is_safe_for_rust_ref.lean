-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref
import Obligations.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref

namespace Specs.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Precondition over `trusted : bool` modeling `storage_device::BufferSource`
    where `ZX_RIGHT_TRANSFER` has been stripped (`trusted < 2`, i.e., any valid `bool`). -/
def pre (args : List Value) : Prop :=
  ∃ (t : Nat),
    t < 2 ∧
    args = [ .scalar { bits := t, sizeBytes := 1 } ]

/-- Exact postcondition: returns `true` (`1`) iff `trusted` is `true` (`1`),
    preventing `&[u8]` / `&mut [u8]` creation on untrusted device-shared VMOs (`t = 0`). -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (t : Nat),
    args = [ .scalar { bits := t, sizeBytes := 1 } ] →
    ret = .scalar { bits := t, sizeBytes := 1 }

instance : ItemSpec "fxfs_storage_boundary::vmo_buffer_is_safe_for_rust_ref" where
  pre := pre
  post := post

instance : StatefulItemSpec "fxfs_storage_boundary::vmo_buffer_is_safe_for_rust_ref" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FxfsStorageBoundary.vmo_buffer_is_safe_for_rust_ref
