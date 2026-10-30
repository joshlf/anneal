import Trusted
import Mir.FxfsTier1.unicode_lookup_plane_bounds
import Obligations.FxfsTier1.unicode_lookup_plane_bounds

namespace Specs.FxfsTier1.unicode_lookup_plane_bounds

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Precondition over `(ch_u32, plane_start, plane_end, total_entries)` matching `fxfs/unicode/src/lookup.rs:50-75`. -/
def pre (args : List Value) (mem : Memory) : Prop :=
  args =
    [ .scalar { bits := 0x1F600, sizeBytes := 4 }
    , .scalar { bits := 10, sizeBytes := 8 }
    , .scalar { bits := 42, sizeBytes := 8 }
    , .scalar { bits := 100, sizeBytes := 8 } ] ∧
  mem = emptyMemory

/-- Postcondition: validates `ch_u32 >> 16 <= 16` and `plane_start <= plane_end <= total_entries`,
    returning `Some((plane_start, plane_end - plane_start))`. -/
def post (_args : List Value) (_mem : Memory) (ret : Value) (_mem' : Memory) : Prop :=
  ret =
    .aggregate 1
      [ .aggregate 0
          [ .scalar { bits := 10, sizeBytes := 8 }
          , .scalar { bits := 32, sizeBytes := 8 } ] ]

instance : StatefulItemSpec "fxfs_tier1::unicode_lookup_plane_bounds" where
  pre := pre
  post := post

end Specs.FxfsTier1.unicode_lookup_plane_bounds
