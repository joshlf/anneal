#![no_std]

use anneal_spec::*;

// ---------------------------------------------------------------------------
// Phase 4 Fxfs Concurrency & State-Machine Verification Suite
// (`fxfs-concurrency-models`)
//
// Models and verifies concurrency, atomic reference-counting, and lock/epoch
// state machines from Fuchsia's Fxfs filesystem:
// 1. `FxFile::update_state` (`src/storage/fxfs/platform/src/fuchsia/file.rs:349-395`):
//    `IS_DIRTY` clearing on tombstone and exact `Arc::into_raw` (+1) /
//    `Arc::from_raw` (-1) reference-count delta invariant
//    (`fxfile_state_arc_delta`).
// 2. `LockManager` / `LockEntry::is_allowed`
//    (`src/storage/fxfs/src/object_store/lock_manager.rs:1725-1765`):
//    reader/writer lock state transitions and the mutual-exclusion invariant
//    `state == WRITE_LOCK -> read_count == 0`
//    (`lock_manager_is_allowed_and_acquire`).
// 3. `SkipListLayer` (`src/storage/fxfs/src/lsm_tree/skip_list_layer.rs`):
//    skip-list pointer-array level indexing (`unchecked_sub(max_levels, level)`)
//    and epoch active-reader reference-count increment
//    (`skiplist_level_and_epoch_valid`).
// ---------------------------------------------------------------------------

/// Models `FxFile::update_state` (`src/storage/fxfs/platform/src/fuchsia/file.rs:349-395`):
/// clears `IS_DIRTY` when `will_be_tombstoned` is set and computes the exact
/// self-`Arc` reference-count delta (`+1` for `Arc::into_raw` when transitioning
/// clean -> dirty, `-1` for `Arc::from_raw` when transitioning dirty -> clean,
/// and `0` otherwise), satisfying
/// `(if old_is_dirty { 1 } else { 0 }) + delta == (if final_is_dirty { 1 } else { 0 })`.
pub fn fxfile_state_arc_delta(
    old_is_dirty: bool,
    new_is_dirty: bool,
    will_be_tombstoned: bool,
) -> (bool, i32) {
    let final_is_dirty = if will_be_tombstoned { false } else { new_is_dirty };
    let delta: i32 = if !old_is_dirty && final_is_dirty {
        1
    } else if old_is_dirty && !final_is_dirty {
        -1
    } else {
        0
    };
    (final_is_dirty, delta)
}

/// Models `LockEntry::is_allowed` and lock acquisition in
/// `src/storage/fxfs/src/object_store/lock_manager.rs:1725-1765`:
/// checks whether `target_state` (`1` = `READ_LOCK` or `2` = `WRITE_LOCK`, with
/// `0` = `UNLOCKED`) can be acquired given `(current_state, read_count, head_is_null)`
/// and returns `(allowed, next_state, next_read_count)`, preserving the
/// mutual-exclusion invariant `next_state == 2 -> next_read_count == 0`.
///
/// # Safety
///
/// `read_count < u64::MAX` and `(current_state == 2 -> read_count == 0)`.
#[anneal_spec::spec(
    requires: read_count < u64::MAX && (current_state != 2 || read_count == 0),
)]
pub unsafe fn lock_manager_is_allowed_and_acquire(
    current_state: u8,
    read_count: u64,
    head_is_null: bool,
    target_state: u8,
) -> (bool, u8, u64) {
    if !head_is_null {
        return (false, current_state, read_count);
    }
    if target_state == 1 {
        if current_state == 0 || current_state == 1 {
            let next_count = unsafe { read_count.unchecked_add(1) };
            (true, 1, next_count)
        } else {
            (false, current_state, read_count)
        }
    } else if target_state == 2 {
        if current_state == 0 && read_count == 0 {
            (true, 2, 0)
        } else {
            (false, current_state, read_count)
        }
    } else {
        (false, current_state, read_count)
    }
}

/// Models `SkipListLayer` pointer-array level indexing and epoch reader refcount
/// acquisition (`src/storage/fxfs/src/lsm_tree/skip_list_layer.rs`):
/// when `level < max_levels` and `active_readers < u64::MAX`, computes the
/// remaining level span `max_levels - level` via `usize::unchecked_sub` and
/// increments `active_readers` via `u64::unchecked_add`.
pub fn skiplist_level_and_epoch_valid(
    level: usize,
    max_levels: usize,
    active_readers: u64,
) -> Option<(usize, u64)> {
    if level < max_levels && active_readers < u64::MAX {
        let remaining_levels = unsafe { max_levels.unchecked_sub(level) };
        let next_readers = unsafe { active_readers.unchecked_add(1) };
        Some((remaining_levels, next_readers))
    } else {
        None
    }
}
