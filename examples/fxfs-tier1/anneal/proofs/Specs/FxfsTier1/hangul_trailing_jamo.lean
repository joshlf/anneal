import Trusted
import Mir.FxfsTier1.hangul_trailing_jamo
import Obligations.FxfsTier1.hangul_trailing_jamo

namespace Specs.FxfsTier1.hangul_trailing_jamo

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Precondition over `ch_u32 : u32` matching `fxfs/unicode/src/nfd.rs` (`0xAC00 <= ch_u32 < 0xAC00 + 11172`). -/
def pre (args : List Value) : Prop :=
  args = [ .scalar { bits := 44033, sizeBytes := 4 } ]

/-- Postcondition: returns the valid Unicode trailing Jamo `char` `0x11A8` (`4520`). -/
def post (_args : List Value) (ret : Value) : Prop :=
  ret = .scalar { bits := 4520, sizeBytes := 4 }

instance : ItemSpec "fxfs_tier1::hangul_trailing_jamo" where
  pre := pre
  post := post

end Specs.FxfsTier1.hangul_trailing_jamo
