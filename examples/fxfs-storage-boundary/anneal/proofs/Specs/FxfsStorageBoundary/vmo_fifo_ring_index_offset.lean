import Trusted
import Mir.FxfsStorageBoundary.vmo_fifo_ring_index_offset
import Obligations.FxfsStorageBoundary.vmo_fifo_ring_index_offset

namespace Specs.FxfsStorageBoundary.vmo_fifo_ring_index_offset

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition over an arbitrary demonic client `raw_index < 2^64`,
    non-zero ring `capacity > 0`, and `elem_size` satisfying `capacity * elem_size < 2^64`. -/
def pre (args : List Value) : Prop :=
  ∃ (raw cap es : Nat),
    0 < cap ∧
    raw < 18446744073709551616 ∧
    cap < 18446744073709551616 ∧
    es < 18446744073709551616 ∧
    cap * es < 18446744073709551616 ∧
    args =
      [ .scalar { bits := raw, sizeBytes := 8 }
      , .scalar { bits := cap, sizeBytes := 8 }
      , .scalar { bits := es, sizeBytes := 8 } ]

/-- Exact postcondition: `ret == (raw_index % capacity) * elem_size < capacity * elem_size`. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (raw cap es : Nat),
    args =
      [ .scalar { bits := raw, sizeBytes := 8 }
      , .scalar { bits := cap, sizeBytes := 8 }
      , .scalar { bits := es, sizeBytes := 8 } ] →
    ret = .scalar { bits := (raw % cap) * es, sizeBytes := 8 }

instance : ItemSpec "fxfs_storage_boundary::vmo_fifo_ring_index_offset" where
  pre := pre
  post := post

instance : StatefulItemSpec "fxfs_storage_boundary::vmo_fifo_ring_index_offset" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FxfsStorageBoundary.vmo_fifo_ring_index_offset
