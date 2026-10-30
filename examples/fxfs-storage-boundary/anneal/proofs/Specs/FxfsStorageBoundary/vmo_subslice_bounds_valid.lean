-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FxfsStorageBoundary.vmo_subslice_bounds_valid
import Obligations.FxfsStorageBoundary.vmo_subslice_bounds_valid

namespace Specs.FxfsStorageBoundary.vmo_subslice_bounds_valid

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition over `(base_offset, buf_len, sub_start, sub_end)`
    matching `storage_device::BufferRef::subslice` range invariants (`sub_start <= sub_end <= buf_len`
    and `base_offset + buf_len < 2^64`). -/
def pre (args : List Value) : Prop :=
  ∃ (base len s e : Nat),
    s ≤ e ∧
    e ≤ len ∧
    base + len < 18446744073709551616 ∧
    args =
      [ .scalar { bits := base, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := s, sizeBytes := 8 }
      , .scalar { bits := e, sizeBytes := 8 } ]

/-- Exact postcondition: `ret == base_offset + (sub_end - sub_start)` within `[base, base + len]`. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (base len s e : Nat),
    args =
      [ .scalar { bits := base, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := s, sizeBytes := 8 }
      , .scalar { bits := e, sizeBytes := 8 } ] →
    ret = .scalar { bits := base + (e - s), sizeBytes := 8 }

instance : ItemSpec "fxfs_storage_boundary::vmo_subslice_bounds_valid" where
  pre := pre
  post := post

instance : StatefulItemSpec "fxfs_storage_boundary::vmo_subslice_bounds_valid" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FxfsStorageBoundary.vmo_subslice_bounds_valid
