#![no_std]

use anneal_spec::*;

// ---------------------------------------------------------------------------
// Slice 1: `fxfs_platform::fuchsia::layer_pager::MappedVmo::new`
// (`src/storage/fxfs/platform/src/fuchsia/layer_pager.rs:57-76`)
// ---------------------------------------------------------------------------

/// Models `MappedVmo::new` page alignment calculation: rounds `len` up to the
/// next multiple of `page_size` (returning `None` if `page_size == 0` or if
/// rounding up overflows `usize`).
#[anneal_spec::spec(
    requires: page_size > 0,
    ensures: |ref ret| true,
)]
pub fn mapped_vmo_aligned_len(len: usize, page_size: usize) -> Option<usize> {
    if page_size == 0 {
        return None;
    }
    let rem = len % page_size;
    if rem == 0 {
        Some(len)
    } else {
        let pad = unsafe { page_size.unchecked_sub(rem) };
        let aligned = unsafe { len.unchecked_add(pad) };
        Some(aligned)
    }
}

// ---------------------------------------------------------------------------
// Slice 2: `fxfs_platform::fuchsia::paged_object_handle` dirty batch split
// (`src/storage/fxfs/platform/src/fuchsia/paged_object_handle.rs:1615-1635`)
// ---------------------------------------------------------------------------

/// Models `paged_object_handle` dirty batch splitting into `(read_raw_len, zero_tail_len)`
/// where `read_raw_len = min(range_end, content_size) - range_start` and
/// `zero_tail_len = if range_end > content_size { range_end - max(range_start, content_size) } else { 0 }`,
/// preserving the invariant `read_raw_len + zero_tail_len == range_end - range_start`.
#[anneal_spec::spec(
    requires: range_start <= range_end && range_start <= content_size,
    ensures: |ref ret| ret.0 + ret.1 == range_end - range_start,
)]
pub fn pager_dirty_batch_split_lengths(
    range_start: u64,
    range_end: u64,
    content_size: u64,
) -> (u64, u64) {
    let min_end = if range_end < content_size {
        range_end
    } else {
        content_size
    };
    let read_raw_len = unsafe { min_end.unchecked_sub(range_start) };
    let zero_tail_len = if range_end > content_size {
        let max_start = if range_start > content_size {
            range_start
        } else {
            content_size
        };
        unsafe { range_end.unchecked_sub(max_start) }
    } else {
        0
    };
    (read_raw_len, zero_tail_len)
}

// ---------------------------------------------------------------------------
// Slice 3: `fxfs_platform::fuchsia::pager::Pager::query_vmo_stats`
// (`src/storage/fxfs/platform/src/fuchsia/pager.rs:225-251`)
// ---------------------------------------------------------------------------

/// Models `Pager::query_vmo_stats`: initializes `MaybeUninit<u32>` on `ZX_OK`
/// (`status_ok == true`) via raw buffer copy and reads `unsafe { vmo_stats.assume_init() } == 1`
/// (`ZX_PAGER_VMO_STATS_MODIFIED`).
#[anneal_spec::spec(
    requires: true,
    ensures: |ref ret| true,
)]
pub fn pager_query_vmo_stats_assume_init(
    status_ok: bool,
    raw_modified_word: u32,
) -> Option<bool> {
    let mut vmo_stats = core::mem::MaybeUninit::<u32>::uninit();
    if !status_ok {
        return None;
    }
    unsafe {
        core::ptr::copy_nonoverlapping(
            &raw const raw_modified_word as *const u8,
            vmo_stats.as_mut_ptr() as *mut u8,
            4,
        );
        let modified = vmo_stats.assume_init();
        Some(modified == 1)
    }
}

// ---------------------------------------------------------------------------
// Slice 4: `fxfs_platform::fuchsia::node::WeakNode::upgrade_and_downcast_node`
// (`src/storage/fxfs/platform/src/fuchsia/node.rs:195-205`)
// ---------------------------------------------------------------------------

/// Models `upgrade_and_downcast_node` guarding `Weak::from_raw(self.ptr as *const T)`
/// behind `ptr_non_null` and `weak_node.is_type::<T>()` (`vtable_type_id == target_type_id`).
#[anneal_spec::spec(
    requires: true,
    ensures: |ref ret| *ret == (ptr_non_null && vtable_type_id == target_type_id),
)]
pub fn weak_node_downcast_type_check(
    vtable_type_id: u64,
    target_type_id: u64,
    ptr_non_null: bool,
) -> bool {
    if !ptr_non_null {
        return false;
    }
    vtable_type_id == target_type_id
}
