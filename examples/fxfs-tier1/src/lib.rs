#![no_std]

use anneal_spec::*;

// ---------------------------------------------------------------------------
// Slice 1: `fxfs::object_store::data_object_handle::FileExtent` & `RangeExt`
// (`src/storage/fxfs/src/range.rs` & `src/object_store/data_object_handle.rs`)
// ---------------------------------------------------------------------------

#[anneal_spec::invariant(
    self.device_start < self.device_end
        && self.logical_offset <= u64::MAX - (self.device_end - self.device_start)
)]
#[repr(C)]
pub struct FileExtent {
    pub device_start: u64,
    pub device_end: u64,
    pub logical_offset: u64,
}

/// Extracted from `fxfs::object_store::data_object_handle::FileExtent::logical_range`:
/// computes the end logical offset using `unchecked_sub` and `unchecked_add`
/// under the `FileExtent` invariant established by `FileExtent::new`.
///
/// # Safety
///
/// `device_start < device_end` and `logical_offset + (device_end - device_start) <= u64::MAX`.
#[anneal_spec::spec(
    requires: device_start < device_end && logical_offset <= u64::MAX - (device_end - device_start),
    ensures: |ref ret| *ret == logical_offset + (device_end - device_start),
)]
pub unsafe fn file_extent_logical_end(
    device_start: u64,
    device_end: u64,
    logical_offset: u64,
) -> u64 {
    let len = unsafe { device_end.unchecked_sub(device_start) };
    unsafe { logical_offset.unchecked_add(len) }
}

/// Extracted from `fxfs::range::RangeExt::length`:
/// computes `end - start` via `u64::unchecked_sub` after validating `start <= end`.
///
/// # Safety
///
/// `start <= end`.
#[anneal_spec::spec(
    requires: start <= end,
    ensures: |ref ret| *ret == end - start,
)]
pub unsafe fn range_unchecked_length(start: u64, end: u64) -> u64 {
    unsafe { end.unchecked_sub(start) }
}

// ---------------------------------------------------------------------------
// Slice 2: `fxfs_unicode::nfd::hangul_decomposition`
// (`src/storage/fxfs/unicode/src/nfd.rs`)
// ---------------------------------------------------------------------------

/// Extracted from `fxfs_unicode::nfd::hangul_decomposition`:
/// computes the leading Jamo `l` from a Hangul syllable codepoint `ch_u32`
/// in `0xac00..0xd7a4` and converts it via `char::from_u32_unchecked`.
#[anneal_spec::spec(
    requires: ch_u32 >= 0xac00 && ch_u32 < 0xd7a4,
    ensures: |ref ret| (*ret as u32) >= 0x1100 && (*ret as u32) < 0x1113,
)]
pub fn hangul_leading_jamo(ch_u32: u32) -> char {
    let s_index = ch_u32 - 0xac00;
    let l_index = s_index / 588;
    let l = 0x1100 + l_index;
    unsafe { core::char::from_u32_unchecked(l) }
}

/// Extracted from `fxfs_unicode::nfd::hangul_decomposition`:
/// computes the vowel Jamo `v` from a Hangul syllable codepoint `ch_u32`
/// in `0xac00..0xd7a4` and converts it via `char::from_u32_unchecked`.
#[anneal_spec::spec(
    requires: ch_u32 >= 0xac00 && ch_u32 < 0xd7a4,
    ensures: |ref ret| (*ret as u32) >= 0x1161 && (*ret as u32) < 0x1176,
)]
pub fn hangul_vowel_jamo(ch_u32: u32) -> char {
    let s_index = ch_u32 - 0xac00;
    let v_index = (s_index % 588) / 28;
    let v = 0x1161 + v_index;
    unsafe { core::char::from_u32_unchecked(v) }
}

/// Extracted from `fxfs_unicode::nfd::hangul_decomposition`:
/// computes the trailing Jamo `t` from a Hangul syllable codepoint `ch_u32`
/// in `0xac00..0xd7a4` and converts it via `char::from_u32_unchecked`.
#[anneal_spec::spec(
    requires: ch_u32 >= 0xac00 && ch_u32 < 0xd7a4,
    ensures: |ref ret| (*ret as u32) >= 0x11a7 && (*ret as u32) < 0x11c3,
)]
pub fn hangul_trailing_jamo(ch_u32: u32) -> char {
    let s_index = ch_u32 - 0xac00;
    let t_index = s_index % 28;
    let t = 0x11a7 + t_index;
    unsafe { core::char::from_u32_unchecked(t) }
}

// ---------------------------------------------------------------------------
// Slice 3: `storage_ptr_slice::PtrByteSlice` (`src/storage/lib/ptr_slice/src/lib.rs`)
// ---------------------------------------------------------------------------

/// Extracted from `PtrByteSlice`: wide raw slice pointer creation, `len()` via
/// `PtrMetadata`, and `as_ptr()` via thin pointer cast.
pub fn ptr_slice_len_and_first(buf: &[u8; 4]) -> usize {
    let raw_slice: *const [u8] =
        core::ptr::slice_from_raw_parts(buf as *const [u8; 4] as *const u8, 4);
    raw_slice.len()
}

/// Extracted from `MutPtrByteSlice::copy_from_ptr_slice` & `fxfs::zerocopy_serialization`:
/// copies 4 bytes from `src` to `dst` via `core::ptr::copy_nonoverlapping`.
pub fn ptr_slice_copy4(src: &[u8; 4], dst: &mut [u8; 4]) -> usize {
    unsafe {
        core::ptr::copy_nonoverlapping(
            src as *const [u8; 4] as *const u8,
            dst as *mut [u8; 4] as *mut u8,
            4,
        );
    }
    4
}

/// Extracted from `PtrByteSlice::read`: reads a `u32` via `core::ptr::read_unaligned`.
pub fn ptr_slice_read_unaligned_u32(src: &[u8; 4]) -> u32 {
    unsafe { core::ptr::read_unaligned(src as *const [u8; 4] as *const u32) }
}

/// Extracted from `MutPtrByteSlice::write`: writes a `u32` via `core::ptr::write_unaligned`
/// when `len >= 4` (`src/storage/lib/ptr_slice/src/lib.rs:212`).
///
/// # Safety
///
/// When `len >= 4`, `dst` must be valid for writing 4 bytes.
pub unsafe fn ptr_slice_write_unaligned_u32(dst: *mut u8, len: usize, val: u32) -> bool {
    if len >= 4 {
        unsafe {
            core::ptr::write_unaligned(dst as *mut u32, val);
        }
        true
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// Slice 4: `fxfs::checksum::fletcher64` & `fxfs_unicode::lookup`
// (`src/storage/fxfs/src/checksum.rs` & `src/storage/fxfs/unicode/src/lookup.rs`)
// ---------------------------------------------------------------------------

/// Extracted from `fxfs::checksum::fletcher64`:
/// computes one Fletcher-64 accumulation step `(lower, upper)` modulo `u32::MAX as u64`
/// (`src/storage/fxfs/src/checksum.rs:21-38`).
pub fn fletcher64_step(acc_lower: u64, acc_upper: u64, word: u64) -> (u64, u64) {
    let modulus = 0xffff_ffff_u64;
    let lower = (acc_lower + word) % modulus;
    let upper = (acc_upper + lower) % modulus;
    (lower, upper)
}

/// Extracted from `fxfs_unicode::lookup`:
/// validates plane index `ch_u32 >> 16 <= 16` and plane slice bounds
/// `plane_start <= plane_end <= total_entries` (`src/storage/fxfs/unicode/src/lookup.rs:50-75`).
pub fn unicode_lookup_plane_bounds(
    ch_u32: u32,
    plane_start: usize,
    plane_end: usize,
    total_entries: usize,
) -> Option<(usize, usize)> {
    let plane = ch_u32 >> 16;
    if plane <= 16 && plane_start <= plane_end && plane_end <= total_entries {
        let len = unsafe { plane_end.unchecked_sub(plane_start) };
        Some((plane_start, len))
    } else {
        None
    }
}
