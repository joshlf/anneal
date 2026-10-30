import Trusted
import Mir.FxfsPlatformPager.pager_dirty_batch_split_lengths
import Obligations.FxfsPlatformPager.pager_dirty_batch_split_lengths

namespace Specs.FxfsPlatformPager.pager_dirty_batch_split_lengths

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Pure functional specification of `read_raw_len = min(range_end, content_size) - range_start`. -/
def readRawLen (rs re cs : Nat) : Nat :=
  (if re < cs then re else cs) - rs

/-- Pure functional specification of `zero_tail_len = if range_end > content_size { range_end - max(range_start, content_size) } else { 0 }`. -/
def zeroTailLen (rs re cs : Nat) : Nat :=
  if cs < re then re - (if cs < rs then rs else cs) else 0

/-- Conservation theorem: `read_raw_len + zero_tail_len == range_end - range_start`. -/
theorem split_lengths_sum_eq (rs re cs : Nat) (h_re : rs ≤ re) (h_cs : rs ≤ cs) :
    readRawLen rs re cs + zeroTailLen rs re cs = re - rs := by
  unfold readRawLen zeroTailLen
  split <;> split <;> (try split) <;> omega

/-- Precondition over `(range_start, range_end, content_size)` covering all
    comparison branches of `range_end > content_size` and `range_start <= content_size`. -/
def pre (args : List Value) : Prop :=
  ∃ (rs re cs : Nat),
    rs ≤ re ∧
    rs ≤ cs ∧
    (rs = 0 ∨ rs = 1) ∧
    (re = 1 ∨ re = 2) ∧
    (cs = 1 ∨ cs = 2) ∧
    args =
      [ .scalar { bits := rs, sizeBytes := 8 }
      , .scalar { bits := re, sizeBytes := 8 }
      , .scalar { bits := cs, sizeBytes := 8 } ]

/-- Exact postcondition: returns `(readRawLen rs re cs, zeroTailLen rs re cs)`
    satisfying `read_raw_len + zero_tail_len == range_end - range_start`. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (rs re cs : Nat),
    args =
      [ .scalar { bits := rs, sizeBytes := 8 }
      , .scalar { bits := re, sizeBytes := 8 }
      , .scalar { bits := cs, sizeBytes := 8 } ] →
    ret = .aggregate 0
      [ .scalar { bits := readRawLen rs re cs, sizeBytes := 8 }
      , .scalar { bits := zeroTailLen rs re cs, sizeBytes := 8 } ]

instance : ItemSpec "fxfs_platform_pager::pager_dirty_batch_split_lengths" where
  pre := pre
  post := post

instance : StatefulItemSpec "fxfs_platform_pager::pager_dirty_batch_split_lengths" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FxfsPlatformPager.pager_dirty_batch_split_lengths
