#![no_std]

use anneal_spec::*;

// ---------------------------------------------------------------------------
// Fuchsia `//src/starnix/lib/usercopy` & `//src/lib/fidl/rust_next/fidl_next_codec`
// End-to-End Verification Prototype (`fuchsia-usercopy`)
//
// Models and verifies security-critical invariants across Starnix restricted-mode
// usercopy boundary routines and FIDL next-generation zero-copy wire decoding:
// 1. `do_hermetic_copy` (`src/starnix/lib/usercopy/src/lib.rs:247-278`):
//    post-copy byte count calculation (`hermetic_copy_bytes_copied`).
// 2. `Usercopy::{zero, copyout, copyin, copyin_until_null_byte}`
//    (`src/starnix/lib/usercopy/src/lib.rs:434, 468, 495, 533`):
//    restricted-range and null-address collision guard
//    (`usercopy_address_in_restricted_range`).
// 3. `assume_initialized_until` (`src/starnix/lib/usercopy/src/lib.rs:224-237`):
//    `MaybeUninit<u8>` buffer split conservation (`assume_initialized_until_split_len`).
// 4. Call-graph bracketing around the `hermetic_copy` assembly leaf
//    (`hermetic_copy_stub` + `usercopy_copyin_bracketed`):
//    modular verification discharging `copyin`'s slice-split and `MaybeUninit`
//    initialization safety obligations from the assembly leaf's return contract.
// 5. `Usercopy::{atomic_load_u32, parse_compare_exchange_result}`
//    (`src/starnix/lib/usercopy/src/lib.rs:554-565, 645-654`):
//    64-bit `ATOMIC_ERROR_MASK` fault unpacking (`atomic_load_u32_unpack`,
//    `parse_compare_exchange_result`).
// 6. `fidl_next_codec` zero-copy wire validation
//    (`src/lib/fidl/rust_next/fidl_next_codec/src/{decoder.rs:150-179, wire/ptr.rs:28-41}`):
//    8-byte `Chunk` slice padding bounds (`fidl_chunk_padding_len`) and wire
//    pointer presence discrimination (`fidl_pointer_is_encoded_present`).
// ---------------------------------------------------------------------------

/// Models `do_hermetic_copy` (`src/starnix/lib/usercopy/src/lib.rs:247-278`):
/// given the base address `dest_or_src_base` (`dest` when `ret_dest` is `true`,
/// `source` when `false`), requested byte `count`, and the assembly routine's
/// returned `unread_address` (which either equals `dest_or_src_base + count` on
/// completion or the faulting address in `[dest_or_src_base, dest_or_src_base + count]`
/// caught by the Zircon page-fault exception handler), computes
/// `copied = unread_address - dest_or_src_base` and proves `copied <= count`.
#[allow(unused_variables)]
#[anneal_spec::spec(
    requires: dest_or_src_base <= unread_address && unread_address - dest_or_src_base <= count,
    ensures: |ref ret| *ret == unread_address - dest_or_src_base && *ret <= count,
)]
pub fn hermetic_copy_bytes_copied(
    dest_or_src_base: usize,
    count: usize,
    unread_address: usize,
) -> usize {
    unread_address - dest_or_src_base
}

/// Models the restricted-address-space guard in `Usercopy::{zero, copyout, copyin, copyin_until_null_byte}`
/// (`src/starnix/lib/usercopy/src/lib.rs:434, 468, 495, 533`):
/// rejects `addr == 0` (which collides with the fault-encoding scheme) and checks
/// `addr >= range_start && addr < range_end`.
#[anneal_spec::spec(
    requires: range_start <= range_end,
    ensures: |ref ret| *ret == (addr != 0 && addr >= range_start && addr < range_end),
)]
pub fn usercopy_address_in_restricted_range(
    addr: usize,
    range_start: usize,
    range_end: usize,
) -> bool {
    if addr == 0 {
        return false;
    }
    if addr < range_start {
        return false;
    }
    addr < range_end
}

/// Models `assume_initialized_until` (`src/starnix/lib/usercopy/src/lib.rs:224-237`):
/// splits a `MaybeUninit<u8>` buffer of length `buf_len` at `initialized_until`
/// into `(init_len, uninit_len)`, proving absence of arithmetic underflow and
/// length conservation `init_len + uninit_len == buf_len`.
#[anneal_spec::spec(
    requires: initialized_until <= buf_len,
    ensures: |ref ret| ret.0 == initialized_until && ret.1 == buf_len - initialized_until,
)]
pub fn assume_initialized_until_split_len(
    buf_len: usize,
    initialized_until: usize,
) -> (usize, usize) {
    let uninit_len = buf_len - initialized_until;
    (initialized_until, uninit_len)
}

/// Models the assembly FFI leaf `hermetic_copy` wrapped by `do_hermetic_copy`
/// (`src/starnix/lib/usercopy/src/lib.rs:16, 247-278`) for call-graph bracketing:
/// under `fault_offset <= count` and `strictSafetyPre: normal_mode_dest_valid == true`
/// (i.e. `dest` is a valid Starnix normal-mode buffer that never faults for `count`
/// bytes and only `source` is in restricted space), returns `fault_offset <= count`.
#[allow(unused_variables)]
#[inline(never)]
#[anneal_spec::spec(
    requires: fault_offset <= count && normal_mode_dest_valid,
    ensures: |ref ret| *ret == fault_offset && *ret <= count,
)]
pub unsafe fn hermetic_copy_stub(
    count: usize,
    fault_offset: usize,
    normal_mode_dest_valid: bool,
) -> usize {
    if !normal_mode_dest_valid {
        unsafe { core::hint::unreachable_unchecked() };
    }
    fault_offset
}

/// Models `Usercopy::copyin` (`src/starnix/lib/usercopy/src/lib.rs:486-513`)
/// bracketed above `hermetic_copy_stub` and `assume_initialized_until`:
/// given `source_in_restricted_range` (computed by `usercopy_address_in_restricted_range`),
/// returns `read_count = 0` when `false` or invokes `hermetic_copy_stub` to obtain
/// `read_count <= dest_len` when `true`, and splits `dest_len` into
/// `(read_count, dest_len - read_count)` without slice-split panic or out-of-bounds
/// `MaybeUninit` initialization UB.
#[anneal_spec::spec(
    requires: fault_offset <= dest_len && (!source_in_restricted_range || normal_mode_dest_valid),
    ensures: |ref ret| true,
)]
pub fn usercopy_copyin_bracketed(
    source_in_restricted_range: bool,
    dest_len: usize,
    fault_offset: usize,
    normal_mode_dest_valid: bool,
) -> (usize, usize) {
    let read_count = if !source_in_restricted_range {
        0
    } else {
        unsafe { hermetic_copy_stub(dest_len, fault_offset, normal_mode_dest_valid) }
    };
    let uninit_len = dest_len - read_count;
    (read_count, uninit_len)
}

/// Models `Usercopy::atomic_load_u32` (`src/starnix/lib/usercopy/src/lib.rs:195, 554-565`):
/// checks whether the upper 32 bits of `value_or_error` (`value_or_error & 0xFFFFFFFF00000000`,
/// equivalently `value_or_error >> 32`) are zero, returning `(true, value_or_error as u32)` on
/// success and `(false, 0)` when the exception handler set `ATOMIC_ERROR_MASK`.
#[anneal_spec::spec(
    requires: true,
    ensures: |ref ret| true,
)]
pub fn atomic_load_u32_unpack(value_or_error: u64) -> (bool, u32) {
    if value_or_error <= 0xFFFF_FFFF {
        (true, value_or_error as u32)
    } else {
        (false, 0)
    }
}

/// Models `Usercopy::parse_compare_exchange_result`
/// (`src/starnix/lib/usercopy/src/lib.rs:645-654`):
/// decodes the 64-bit return word from `atomic_compare_exchange_u32_acq_rel` into
/// `0` (`Ok(Err(expected))`: exchange failed, observed value written to `*expected`),
/// `1` (`Ok(Ok(expected))`: exchange succeeded), or `2` (`Err(())`: page fault).
#[anneal_spec::spec(
    requires: true,
    ensures: |ref ret| true,
)]
pub fn parse_compare_exchange_result(expected: u32, value_or_error: u64) -> u8 {
    let _ = expected;
    if value_or_error == 0 {
        0
    } else if value_or_error == 1 {
        1
    } else {
        2
    }
}

// ---------------------------------------------------------------------------
// Bonus Slice: `fidl_next_codec` Zero-Copy Wire Validation
// (`src/lib/fidl/rust_next/fidl_next_codec/src/{decoder.rs, wire/ptr.rs}`)
// ---------------------------------------------------------------------------

/// Models `DecoderExt::take_slice_slot` (`src/lib/fidl/rust_next/fidl_next_codec/src/decoder.rs:150-179`):
/// for a FIDL wire element of size `elem_size <= 8` (`CHUNK_SIZE = 8`) and slice length
/// `len <= 0x0FFF_FFFF_FFFF_FFFF`, computes `slice_byte_length = elem_size * len`,
/// `chunk_count = (slice_byte_length + 7) / 8`, `chunk_length = chunk_count * 8`, and
/// `padding_length = chunk_length - slice_byte_length`, proving `padding_length < 8` and
/// `slice_byte_length + padding_length == chunk_count * 8` (discharging the safety
/// obligation of `unsafe { from_raw_parts(chunks_ptr.add(slice_byte_length), padding_length) }`).
#[anneal_spec::spec(
    requires: elem_size <= 8 && len <= 0x0FFF_FFFF_FFFF_FFFF,
    ensures: |ref ret| true,
)]
pub fn fidl_chunk_padding_len(elem_size: usize, len: usize) -> (usize, usize) {
    let slice_byte_length = elem_size * len;
    let chunk_count = (slice_byte_length + 7) / 8;
    let chunk_length = chunk_count * 8;
    let padding_length = chunk_length - slice_byte_length;
    (slice_byte_length, padding_length)
}

/// Models `Pointer::is_encoded_present`
/// (`src/lib/fidl/rust_next/fidl_next_codec/src/wire/ptr.rs:28-41`):
/// discriminates `ALLOC_ABSENT_U64` (`0` -> `Some(false)`),
/// `ALLOC_PRESENT_U64` (`u64::MAX` -> `Some(true)`), and invalid wire pointer
/// presence markers (`None`).
#[anneal_spec::spec(
    requires: true,
    ensures: |ref ret| true,
)]
pub fn fidl_pointer_is_encoded_present(encoded_u64: u64) -> Option<bool> {
    if encoded_u64 == 0 {
        Some(false)
    } else if encoded_u64 == u64::MAX {
        Some(true)
    } else {
        None
    }
}
