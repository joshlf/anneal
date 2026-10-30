import Trusted
import Mir.FxfsTier1.fletcher64_step
import Obligations.FxfsTier1.fletcher64_step

namespace Specs.FxfsTier1.fletcher64_step

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Precondition over `(acc_lower, acc_upper, word)` matching `fxfs/src/checksum.rs:21-38`. -/
def pre (args : List Value) (mem : Memory) : Prop :=
  args =
    [ .scalar { bits := 100, sizeBytes := 8 }
    , .scalar { bits := 200, sizeBytes := 8 }
    , .scalar { bits := 300, sizeBytes := 8 } ] ∧
  mem = emptyMemory

/-- Postcondition: returns `((acc_lower + word) % 0xffff_ffff, (acc_upper + lower) % 0xffff_ffff)`. -/
def post (_args : List Value) (_mem : Memory) (ret : Value) (_mem' : Memory) : Prop :=
  ret =
    .aggregate 0
      [ .scalar { bits := 400, sizeBytes := 8 }
      , .scalar { bits := 600, sizeBytes := 8 } ]

instance : StatefulItemSpec "fxfs_tier1::fletcher64_step" where
  pre := pre
  post := post

end Specs.FxfsTier1.fletcher64_step
