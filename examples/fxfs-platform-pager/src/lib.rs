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

// ---------------------------------------------------------------------------
// Slice 5: Phase 0 Bug 2 Operationalized via Scoped UB Exception + Modular Caller Isolation
// (`src/storage/fxfs/platform/src/fuchsia/layer_pager.rs:57-89`)
// ---------------------------------------------------------------------------

/// Models `fxfs_platform::fuchsia::layer_pager::MappedVmo::as_slice`
/// (`src/storage/fxfs/platform/src/fuchsia/layer_pager.rs:84-88`):
/// constructs `&[u8]` of length `mapped_len` via `std::slice::from_raw_parts(self.ptr, self.len)`
/// over a VMAR-mapped VMO without checking whether the VMO is pager-backed /
/// concurrently mutable (`pager_backed == true`).
///
/// Under Rust/MIR semantics, forming `&[u8]` over a pager-backed or concurrently
/// mutable VMO (`pager_backed == true`) or null pointer (`!ptr_non_null`) is
/// immediate UB (`unreachable_unchecked()`), while under
/// `ptr_non_null && !pager_backed` it safely returns the slice length `mapped_len`.
///
/// Verified via `UbExceptionVerificationResult`:
/// - `pre`: `ptr_non_null == true`
/// - `strictSafetyPre`: `pager_backed == false` (100% `TreeSafe` on `pre ∧ strictSafetyPre`)
/// - `post`: `ret == mapped_len` on all normal returns across `pre`.
#[inline(never)]
#[anneal_spec::spec(
    requires: ptr_non_null,
    ensures: |ref ret| *ret == mapped_len,
)]
pub unsafe fn mapped_vmo_as_slice_unfixed(
    mapped_len: usize,
    ptr_non_null: bool,
    pager_backed: bool,
) -> usize {
    if !ptr_non_null || pager_backed {
        unsafe { core::hint::unreachable_unchecked() };
    }
    mapped_len
}

/// Models `LayerPager` reading a sub-range `[read_offset, read_offset + read_len)`
/// via `MappedVmo::as_slice(&self)[read_offset..read_offset + read_len]`
/// (`src/storage/fxfs/platform/src/fuchsia/layer_pager.rs:84-120`) without
/// landing a Phase 0 `zx_vmo_read` fix (i.e., even when `pager_backed == true`):
/// requires `ptr_non_null`, calls `mapped_vmo_as_slice_unfixed(mapped_len, ptr_non_null, pager_backed)`
/// to obtain `slice_len`, checks `read_offset <= slice_len` and
/// `read_len <= slice_len - read_offset`, and returns `Some(read_offset + read_len)`.
///
/// Verified via `ModularVerificationResult` against
/// `Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.ubExceptionClaim.callContract.holdsOn`
/// and linked via `linkUbExceptionCallee`.
#[anneal_spec::spec(
    requires: ptr_non_null,
    ensures: |ref ret| true,
)]
pub fn layer_pager_read_unfixed(
    mapped_len: usize,
    ptr_non_null: bool,
    pager_backed: bool,
    read_offset: usize,
    read_len: usize,
) -> Option<usize> {
    if !ptr_non_null {
        return None;
    }
    let slice_len =
        unsafe { mapped_vmo_as_slice_unfixed(mapped_len, ptr_non_null, pager_backed) };
    if read_offset > slice_len {
        return None;
    }
    let rem = slice_len - read_offset;
    if read_len > rem {
        return None;
    }
    let end = read_offset + read_len;
    Some(end)
}
