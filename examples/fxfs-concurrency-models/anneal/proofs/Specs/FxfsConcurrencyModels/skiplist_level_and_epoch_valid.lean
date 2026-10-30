import Trusted
import Mir.FxfsConcurrencyModels.skiplist_level_and_epoch_valid
import Obligations.FxfsConcurrencyModels.skiplist_level_and_epoch_valid

namespace Specs.FxfsConcurrencyModels.skiplist_level_and_epoch_valid

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Pure functional specification of `SkipListLayer` level indexing (`max_levels - level`)
    and epoch active-reader increment (`active_readers + 1`). -/
def expectedSkiplistRet (lvl max_lvl readers : Nat) : Value :=
  if lvl < max_lvl ∧ readers < 18446744073709551615 then
    .aggregate 1
      [ .aggregate 0
          [ .scalar { bits := max_lvl - lvl, sizeBytes := 8 }
          , .scalar { bits := readers + 1, sizeBytes := 8 } ] ]
  else
    .aggregate 0 []

/-- When `lvl < max_lvl` and `readers < u64::MAX`, the remaining level span
    `max_lvl - lvl` is strictly positive (`≥ 1`) and `readers + 1 ≤ u64::MAX`. -/
theorem skiplist_some_invariants (lvl max_lvl readers : Nat)
    (h_lvl : lvl < max_lvl) (h_readers : readers < 18446744073709551615) :
    1 ≤ max_lvl - lvl ∧ readers + 1 ≤ 18446744073709551615 := by
  omega

/-- Universal precondition over all 64-bit `(level, max_levels, active_readers)`. -/
def pre (args : List Value) : Prop :=
  ∃ (lvl max_lvl readers : Nat),
    lvl < 18446744073709551616 ∧
    max_lvl < 18446744073709551616 ∧
    readers < 18446744073709551616 ∧
    args =
      [ .scalar { bits := lvl, sizeBytes := 8 }
      , .scalar { bits := max_lvl, sizeBytes := 8 }
      , .scalar { bits := readers, sizeBytes := 8 } ]

/-- Exact postcondition for `SkipListLayer` level indexing and epoch reader refcount:
    returns `Some((max_levels - level, active_readers + 1))` when `level < max_levels`
    and `active_readers < u64::MAX`, and `None` otherwise. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (lvl max_lvl readers : Nat),
    args =
      [ .scalar { bits := lvl, sizeBytes := 8 }
      , .scalar { bits := max_lvl, sizeBytes := 8 }
      , .scalar { bits := readers, sizeBytes := 8 } ] →
    ret = expectedSkiplistRet lvl max_lvl readers

instance : ItemSpec "fxfs_concurrency_models::skiplist_level_and_epoch_valid" where
  pre := pre
  post := post

instance : StatefulItemSpec "fxfs_concurrency_models::skiplist_level_and_epoch_valid" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FxfsConcurrencyModels.skiplist_level_and_epoch_valid
