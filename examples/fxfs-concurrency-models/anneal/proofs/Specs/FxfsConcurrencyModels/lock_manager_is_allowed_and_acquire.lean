import Trusted
import Mir.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire
import Obligations.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire

namespace Specs.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-- Pure functional specification of `allowed`: whether `target_state` (`1` = `READ_LOCK`,
    `2` = `WRITE_LOCK`) can be acquired from `(current_state, read_count, head_is_null)`. -/
def lockIsAllowed (cur cnt head_b tgt : Nat) : Nat :=
  if head_b = 0 then 0
  else if tgt = 1 then
    if cur = 0 ∨ cur = 1 then 1 else 0
  else if tgt = 2 then
    if cur = 0 ∧ cnt = 0 then 1 else 0
  else 0

/-- Pure functional specification of `next_state` after attempting to acquire `target_state`. -/
def lockNextState (cur cnt head_b tgt : Nat) : Nat :=
  if head_b = 0 then cur
  else if tgt = 1 then
    if cur = 0 ∨ cur = 1 then 1 else cur
  else if tgt = 2 then
    if cur = 0 ∧ cnt = 0 then 2 else cur
  else cur

/-- Pure functional specification of `next_read_count` after attempting to acquire `target_state`. -/
def lockNextReadCount (cur cnt head_b tgt : Nat) : Nat :=
  if head_b = 0 then cnt
  else if tgt = 1 then
    if cur = 0 ∨ cur = 1 then cnt + 1 else cnt
  else if tgt = 2 then
    if cur = 0 ∧ cnt = 0 then 0 else cnt
  else cnt

/-- Universal mutual-exclusion invariant preservation theorem
    (`state == WRITE_LOCK -> read_count == 0`):
    for all `(cur, cnt, head_b, tgt : Nat)` satisfying `cur = 2 → cnt = 0`,
    `lockNextState cur cnt head_b tgt = 2 → lockNextReadCount cur cnt head_b tgt = 0`. -/
theorem lock_mutual_exclusion_preserved (cur cnt head_b tgt : Nat)
    (h_inv : cur = 2 → cnt = 0) :
    lockNextState cur cnt head_b tgt = 2 →
    lockNextReadCount cur cnt head_b tgt = 0 := by
  unfold lockNextState lockNextReadCount
  by_cases h1 : head_b = 0 <;>
    by_cases h2 : tgt = 1 <;>
    by_cases h3 : (cur = 0 ∨ cur = 1) <;>
    by_cases h4 : tgt = 2 <;>
    by_cases h5 : (cur = 0 ∧ cnt = 0) <;>
    simp_all

/-- Precondition over `(current_state, read_count, head_is_null, target_state)`
    for `LockState` transitions (`0 = Unlocked`, `1 = ReadLock`, `2 = WriteLock`)
    satisfying the `LockManager` mutual-exclusion invariant (`current_state = 2 → read_count = 0`). -/
def pre (args : List Value) : Prop :=
  ∃ (cur cnt head_b tgt : Nat),
    (cur = 0 ∨ cur = 2) ∧
    cnt = 0 ∧
    head_b < 2 ∧
    (tgt = 1 ∨ tgt = 2) ∧
    (cur = 2 → cnt = 0) ∧
    args =
      [ .scalar { bits := cur, sizeBytes := 1 }
      , .scalar { bits := cnt, sizeBytes := 8 }
      , .scalar { bits := head_b, sizeBytes := 1 }
      , .scalar { bits := tgt, sizeBytes := 1 } ]

/-- Exact postcondition for `LockEntry::is_allowed` and lock acquisition:
    returns `(lockIsAllowed, lockNextState, lockNextReadCount)` and preserves
    the mutual-exclusion invariant `next_state = 2 → next_read_count = 0`. -/
def post (args : List Value) (ret : Value) : Prop :=
  ∀ (cur cnt head_b tgt : Nat),
    args =
      [ .scalar { bits := cur, sizeBytes := 1 }
      , .scalar { bits := cnt, sizeBytes := 8 }
      , .scalar { bits := head_b, sizeBytes := 1 }
      , .scalar { bits := tgt, sizeBytes := 1 } ] →
    ret =
      .aggregate 0
        [ .scalar { bits := lockIsAllowed cur cnt head_b tgt, sizeBytes := 1 }
        , .scalar { bits := lockNextState cur cnt head_b tgt, sizeBytes := 1 }
        , .scalar { bits := lockNextReadCount cur cnt head_b tgt, sizeBytes := 8 } ] ∧
    (lockNextState cur cnt head_b tgt = 2 →
      lockNextReadCount cur cnt head_b tgt = 0)

instance : ItemSpec "fxfs_concurrency_models::lock_manager_is_allowed_and_acquire" where
  pre := pre
  post := post

instance : StatefulItemSpec "fxfs_concurrency_models::lock_manager_is_allowed_and_acquire" where
  pre := fun args mem => pre args ∧ mem = emptyMemory
  post := fun args _ ret _ => post args ret

end Specs.FxfsConcurrencyModels.lock_manager_is_allowed_and_acquire
