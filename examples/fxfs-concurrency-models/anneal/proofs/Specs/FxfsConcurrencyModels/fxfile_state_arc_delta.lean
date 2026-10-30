import Trusted
import Mir.FxfsConcurrencyModels.fxfile_state_arc_delta
import Obligations.FxfsConcurrencyModels.fxfile_state_arc_delta

namespace Specs.FxfsConcurrencyModels.fxfile_state_arc_delta

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Decode a 32-bit two's-complement delta (`0`, `1`, or `-1 = 0xffff_ffff`) to `Int`. -/
def decodeDeltaI32 (bits : Nat) : Int :=
  if bits = 1 then 1
  else if bits = 4294967295 then -1
  else 0

/-- Universal precondition over all boolean triples
    `(old_is_dirty, new_is_dirty, will_be_tombstoned)`. -/
def pre (args : List Value) : Prop :=
  ∃ (old_b new_b tomb_b : Nat),
    old_b < 2 ∧
    new_b < 2 ∧
    tomb_b < 2 ∧
    args =
      [ .scalar { bits := old_b, sizeBytes := 1 }
      , .scalar { bits := new_b, sizeBytes := 1 }
      , .scalar { bits := tomb_b, sizeBytes := 1 } ]

/-- Exact postcondition for `FxFile::update_state`:
    1. When `will_be_tombstoned` (`tomb_b = 1`), `final_is_dirty` is cleared (`0`);
       otherwise `final_is_dirty = new_is_dirty`.
    2. The `Arc::into_raw` (`+1`) / `Arc::from_raw` (`-1`) delta satisfies the exact
       reference-count conservation law:
       `(if old_b = 1 then 1 else 0) + decodeDeltaI32 delta_bits = (if final_b = 1 then 1 else 0)`. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (old_b new_b tomb_b : Nat),
    args =
      [ .scalar { bits := old_b, sizeBytes := 1 }
      , .scalar { bits := new_b, sizeBytes := 1 }
      , .scalar { bits := tomb_b, sizeBytes := 1 } ] →
    let final_b := if tomb_b = 0 then new_b else 0
    let delta_bits :=
      if old_b = 0 ∧ final_b = 1 then 1
      else if old_b = 1 ∧ final_b = 0 then 4294967295
      else 0
    ret =
      .aggregate 0
        [ .scalar { bits := final_b, sizeBytes := 1 }
        , .scalar { bits := delta_bits, sizeBytes := 4 } ] ∧
    (if old_b = 1 then (1 : Int) else 0) + decodeDeltaI32 delta_bits =
      (if final_b = 1 then (1 : Int) else 0)

instance : ItemSpec "fxfs_concurrency_models::fxfile_state_arc_delta" where
  pre := pre
  post := post

instance : StatefulItemSpec "fxfs_concurrency_models::fxfile_state_arc_delta" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FxfsConcurrencyModels.fxfile_state_arc_delta
