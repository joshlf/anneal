#![no_std]

use anneal_spec::*;

// ---------------------------------------------------------------------------
// Phase 2 Fuchsia Storage Boundary Verification Suite (`fxfs-storage-boundary`)
//
// Models and verifies security-critical invariants across the Fuchsia storage
// shared-memory VMO boundary under a demonic disk / block-driver / client
// threat model:
// 1. `storage_device::buffer` (`src/storage/lib/storage_device/src/buffer.rs`):
//    `trusted: bool` VMO reference gate (`ZX_RIGHT_TRANSFER` stripped) and
//    subslice range bounds (`vmo_buffer_is_safe_for_rust_ref`, `vmo_subslice_bounds_valid`).
// 2. `vmo_fifo::SharedQueue` (`src/storage/lib/vmo-fifo/src/lib.rs`):
//    demonic client ring-buffer index masking and byte-offset calculation
//    (`vmo_fifo_ring_index_offset`).
// 3. `fxfs::zerocopy_serialization` (`src/storage/fxfs/src/zerocopy_serialization.rs`):
//    demonic bincode byte-slice length validation and element count calculation
//    (`zerocopy_check_slice_len`).
// 4. `fxfs_crypto::ff1` (`src/storage/fxfs/crypto/src/ff1.rs`):
//    16-byte AES block tail offset calculation (`ff1_block_tail_offset`).
// ---------------------------------------------------------------------------

/// Models `storage_device::buffer_allocator::BufferSource` (`trusted: bool`, stripped of
/// `ZX_RIGHT_TRANSFER`) and `BufferRef::try_as_slice` (`src/storage/lib/storage_device/src/buffer.rs`):
/// creating a Rust `&[u8]` or `&mut [u8]` reference over a VMO-backed transfer buffer is only
/// sound when `trusted` is true (i.e. no external block driver process holds a handle that can
/// concurrently mutate the shared VMO).
#[anneal_spec::spec(
    requires: trusted,
    ensures: |ref ret| *ret == true,
)]
pub fn vmo_buffer_is_safe_for_rust_ref(trusted: bool) -> bool {
    trusted
}

/// Models `storage_device::buffer::BufferRef::subslice` range calculation
/// (`src/storage/lib/storage_device/src/buffer.rs`): given a parent VMO buffer at
/// `[base_offset, base_offset + buf_len)` and a sub-range `sub_start..sub_end`
/// satisfying `sub_start <= sub_end <= buf_len`, computes the subslice end offset
/// `base_offset + (sub_end - sub_start)` within the parent VMO allocation.
///
/// # Safety
///
/// `sub_start <= sub_end <= buf_len` and `base_offset + buf_len <= usize::MAX`.
#[allow(unused_variables)]
#[anneal_spec::spec(
    requires: sub_start <= sub_end && sub_end <= buf_len && base_offset <= usize::MAX - buf_len,
    ensures: |ref ret| *ret == base_offset + (sub_end - sub_start),
)]
pub unsafe fn vmo_subslice_bounds_valid(
    base_offset: usize,
    buf_len: usize,
    sub_start: usize,
    sub_end: usize,
) -> usize {
    let sub_len = unsafe { sub_end.unchecked_sub(sub_start) };
    unsafe { base_offset.unchecked_add(sub_len) }
}

/// Models `vmo_fifo::SharedQueue` (`src/storage/lib/vmo-fifo/src/lib.rs`) ring-buffer
/// index validation and byte-offset calculation under a demonic client: given an arbitrary
/// untrusted `raw_index` read from the client-shared VMO `AtomicU64`, masks `raw_index % capacity`
/// and computes the element byte offset `(raw_index % capacity) * elem_size`.
///
/// # Safety
///
/// `capacity > 0` and `capacity <= usize::MAX / elem_size` (with `elem_size > 0`).
#[anneal_spec::spec(
    requires: capacity > 0 && elem_size > 0 && capacity <= usize::MAX / elem_size,
    ensures: |ref ret| *ret == (raw_index % capacity) * elem_size,
)]
pub unsafe fn vmo_fifo_ring_index_offset(
    raw_index: usize,
    capacity: usize,
    elem_size: usize,
) -> usize {
    let ring_idx = raw_index % capacity;
    unsafe { ring_idx.unchecked_mul(elem_size) }
}

/// Models `fxfs::zerocopy_serialization::visit_bytes` (`src/storage/fxfs/src/zerocopy_serialization.rs`):
/// given a demonic serialized byte slice length `byte_len` and non-zero `elem_size = size_of::<T::Inner>()`,
/// checks the byte-length remainder `byte_len % elem_size` and computes the element count
/// `(byte_len - (byte_len % elem_size)) / elem_size`.
#[anneal_spec::spec(
    requires: elem_size > 0,
)]
pub fn zerocopy_check_slice_len(byte_len: usize, elem_size: usize) -> usize {
    let rem = byte_len % elem_size;
    let aligned_len = unsafe { byte_len.unchecked_sub(rem) };
    aligned_len / elem_size
}

/// Models `fxfs_crypto::ff1` (`src/storage/fxfs/crypto/src/ff1.rs`): given `d <= 12`,
/// computes the tail byte offset `16 - d` within a 16-byte AES block `[u8; 16]` where
/// `d` bytes are copied via `copy_nonoverlapping(b.as_ptr(), bytes.as_mut_ptr().add(16 - d), d)`.
///
/// # Safety
///
/// `d <= 12` (so `16 - d >= 4` and `(16 - d) + d == 16 <= 16`).
#[anneal_spec::spec(
    requires: d <= 12,
    ensures: |ref ret| *ret == 16 - d,
)]
pub unsafe fn ff1_block_tail_offset(d: usize) -> usize {
    unsafe { 16usize.unchecked_sub(d) }
}
