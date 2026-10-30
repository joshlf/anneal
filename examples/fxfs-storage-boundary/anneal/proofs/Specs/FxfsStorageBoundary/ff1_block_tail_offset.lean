-- @anneal-allow-replace-rust-spec
import Trusted
import Mir.FxfsStorageBoundary.ff1_block_tail_offset
import Obligations.FxfsStorageBoundary.ff1_block_tail_offset

namespace Specs.FxfsStorageBoundary.ff1_block_tail_offset

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Universal precondition over `d : usize` matching `fxfs_crypto::ff1` (`d <= 12`). -/
def pre (args : List Value) : Prop :=
  ∃ (d : Nat),
    d ≤ 12 ∧
    args = [ .scalar { bits := d, sizeBytes := 8 } ]

/-- Exact postcondition: `ret == 16 - d` (guaranteeing `4 <= ret` and `ret + d == 16`). -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (d : Nat),
    args = [ .scalar { bits := d, sizeBytes := 8 } ] →
    ret = .scalar { bits := 16 - d, sizeBytes := 8 }

instance : ItemSpec "fxfs_storage_boundary::ff1_block_tail_offset" where
  pre := pre
  post := post

instance : StatefulItemSpec "fxfs_storage_boundary::ff1_block_tail_offset" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FxfsStorageBoundary.ff1_block_tail_offset
