import Trusted
import Mir.FxfsTier1.file_extent_logical_end
import Obligations.FxfsTier1.file_extent_logical_end

namespace Specs.FxfsTier1.file_extent_logical_end

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition over `(device_start, device_end, logical_offset)`
    matching `FileExtent`'s invariant (`device_start < device_end`) and `u64` non-overflow. -/
def pre (args : List Value) : Prop :=
  ∃ (ds de lo : Nat),
    ds < de ∧
    de < 18446744073709551616 ∧
    lo + (de - ds) < 18446744073709551616 ∧
    args =
      [ .scalar { bits := ds, sizeBytes := 8 }
      , .scalar { bits := de, sizeBytes := 8 }
      , .scalar { bits := lo, sizeBytes := 8 } ]

/-- Exact postcondition: `ret == logical_offset + (device_end - device_start)`. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (ds de lo : Nat),
    args =
      [ .scalar { bits := ds, sizeBytes := 8 }
      , .scalar { bits := de, sizeBytes := 8 }
      , .scalar { bits := lo, sizeBytes := 8 } ] →
    ret = .scalar { bits := lo + (de - ds), sizeBytes := 8 }

instance : ItemSpec "fxfs_tier1::file_extent_logical_end" where
  pre := pre
  post := post

end Specs.FxfsTier1.file_extent_logical_end
