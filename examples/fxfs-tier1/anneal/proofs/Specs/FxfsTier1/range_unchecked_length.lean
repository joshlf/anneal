import Trusted
import Mir.FxfsTier1.range_unchecked_length
import Obligations.FxfsTier1.range_unchecked_length

namespace Specs.FxfsTier1.range_unchecked_length

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition over `(start, end)` matching `RangeExt::length`
    (`start <= end < 2^64`). -/
def pre (args : List Value) : Prop :=
  ∃ (s e : Nat),
    s ≤ e ∧
    e < 18446744073709551616 ∧
    args =
      [ .scalar { bits := s, sizeBytes := 8 }
      , .scalar { bits := e, sizeBytes := 8 } ]

/-- Exact postcondition: `ret == end - start`. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (s e : Nat),
    args =
      [ .scalar { bits := s, sizeBytes := 8 }
      , .scalar { bits := e, sizeBytes := 8 } ] →
    ret = .scalar { bits := e - s, sizeBytes := 8 }

instance : ItemSpec "fxfs_tier1::range_unchecked_length" where
  pre := pre
  post := post

end Specs.FxfsTier1.range_unchecked_length
