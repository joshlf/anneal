-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
import Obligations.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
import Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
import Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked

namespace Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition across all 64-bit `(vmo_size, offset, len)` and any
    `trusted : bool` (`t = 0` or `t = 1`, including untrusted device VMOs). -/
def pre (args : List Value) (mem : Memory) : Prop :=
  ∃ (vmo_size offset len t : Nat),
    vmo_size < 18446744073709551616 ∧
    offset < 18446744073709551616 ∧
    len < 18446744073709551616 ∧
    (t = 0 ∨ t = 1) ∧
    args =
      [ .scalar { bits := vmo_size, sizeBytes := 8 }
      , .scalar { bits := offset, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := t, sizeBytes := 1 } ] ∧
    mem = emptyMemory

/-- Exact postcondition: returns `Some(offset + len)` when
    `offset <= vmo_size ∧ len <= vmo_size - offset`, and `None` otherwise. -/
def post (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory) : Prop :=
  mem' = mem ∧
  ∀ (vmo_size offset len t : Nat),
    args =
      [ .scalar { bits := vmo_size, sizeBytes := 8 }
      , .scalar { bits := offset, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := t, sizeBytes := 1 } ] →
    if offset ≤ vmo_size ∧ len ≤ vmo_size - offset then
      ret = .aggregate 1 [ .scalar { bits := offset + len, sizeBytes := 8 } ]
    else
      ret = .aggregate 0 []

instance : ModularItemSpec "fxfs_storage_boundary::data_object_handle_verify_data_unfixed" where
  envAssumed :=
    Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.ubExceptionClaim.callContract.holdsOn
  pre := pre
  post := post

end Specs.FxfsStorageBoundary.data_object_handle_verify_data_unfixed
