// Copyright 2026 The Fuchsia Authors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0>, the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, or the BSD-2-Clause
// license <LICENSE-BSD or https://opensource.org/license/bsd-2-clause>, at your
// option. This file may not be copied, modified, or distributed except
// according to those terms.

//! Hermetic differential test corpus derived from upstream Miri (`pass/`,
//! `panic/`, and `fail/` suites at `rustc 1.98.0-nightly (14210df0e 2026-05-31)`,
//! commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`).
//!
//! Each public test entry point takes zero arguments and is evaluated both by:
//! 1. Upstream Miri (`miri` / `tests/miri-diff/sync_miri_suite.py`) as the
//!    reference operational semantics oracle.
//! 2. Anneal's MIR-in-Lean semantics (`Trusted.Rustc.V2026_06_01.MirSemantics`)
//!    via `Anneal.Rustc.V2026_06_01.SymbolicEval` proof and refutation
//!    combinators.
//!
//! Every divergence between Miri and Anneal is tracked in
//! `tests/miri-diff/manifest.toml` as an unfixed Anneal bug (`[tests.known_anneal_bug]`).

#![no_std]
#![allow(
    dead_code,
    arithmetic_overflow,
    unconditional_panic,
    invalid_value,
    invalid_reference_casting,
    unnecessary_transmutes,
    dangling_pointers_from_locals,
    deref_nullptr,
    internal_features
)]
#![feature(core_intrinsics)]

use core::cell::UnsafeCell;
use core::intrinsics::{
    assume, copy_nonoverlapping, exact_div, offset, unchecked_add, unchecked_div, unchecked_mul,
    unchecked_rem, unchecked_shl, unchecked_shr, unchecked_sub, unreachable,
};
use core::mem::transmute;

#[repr(C)]
union Uninit<T: Copy> {
    uninit: (),
    value: T,
}

#[repr(C)]
pub struct PairU32 {
    pub a: u32,
    pub b: u32,
}

#[repr(C)]
pub struct PaddedU8U32 {
    pub tag: u8,
    // 3 bytes of inter-field padding before `word`
    pub word: u32,
}

#[repr(u8)]
pub enum ColorTag {
    Red = 0,
    Green = 1,
    Blue = 2,
}

// ============================================================================
// Category 1: Scalar Arithmetic, Bitwise Operations, Shifts & Overflow
// ============================================================================

/// Upstream source: `tests/pass/integer-ops.rs`
pub fn pass_integer_arith_basic() -> u32 {
    let a: u32 = 15;
    let b: u32 = 27;
    let sum = a + b;
    let diff = sum - 10;
    let prod = diff * 2;
    prod / 4
}

/// Upstream source: `tests/pass/integer-ops.rs`
pub fn pass_signed_arith_neg_div_rem() -> i32 {
    let a: i32 = -45;
    let b: i32 = 6;
    let q = a / b; // -7
    let r = a % b; // -3
    (-q) * 10 + (-r) // 73
}

/// Upstream source: `tests/pass/binops.rs`
pub fn pass_bitwise_and_or_xor_not() -> u32 {
    let x: u32 = 0x0F0F_00FF;
    let y: u32 = 0x00FF_0F0F;
    let and_v = x & y;
    let or_v = x | y;
    let xor_v = x ^ y;
    (and_v ^ or_v) - xor_v + (!0u32 ^ 0xFFFF_FFFF)
}

/// Upstream source: `tests/pass/integer-ops.rs`
pub fn pass_shifts_u32_i32() -> i32 {
    let u: u32 = 1u32 << 5; // 32
    let s: i32 = -64i32 >> 2; // -16
    (u as i32) - (-s) // 16
}

/// Upstream source: `tests/pass/binops.rs`
pub fn pass_comparisons_and_eq() -> u32 {
    let a: i32 = -10;
    let b: i32 = 20;
    let c1 = (a < b) as u32;
    let c2 = (a <= -10) as u32;
    let c3 = (b > 0) as u32;
    let c4 = (a != b) as u32;
    c1 + c2 + c3 + c4
}

/// Upstream source: `tests/pass/intrinsics/integer.rs`
pub fn pass_unchecked_arith_in_bounds() -> u32 {
    unsafe {
        let a = unchecked_add(10u32, 20u32);
        let b = unchecked_sub(a, 5u32);
        unchecked_mul(b, 3u32)
    }
}

/// Upstream source: `tests/pass/intrinsics/integer.rs`
pub fn pass_exact_div_valid() -> u32 {
    unsafe { exact_div(84u32, 7u32) }
}

/// Upstream source: `tests/pass/casts.rs`
pub fn pass_int_widening_and_truncating_casts() -> i32 {
    let small_neg: i8 = -12;
    let widened: i32 = small_neg as i32; // -12
    let word: u32 = 0x0102_002A;
    let low_byte: u8 = word as u8; // 42
    widened + (low_byte as i32) // 30
}

/// Upstream source: `tests/panic/mir-validation.rs`
pub fn panic_checked_add_overflow() -> u32 {
    let x: u32 = u32::MAX;
    let y: u32 = 1;
    x + y
}

/// Upstream source: `tests/panic/mir-validation.rs`
pub fn panic_checked_sub_underflow() -> u32 {
    let x: u32 = 0;
    let y: u32 = 1;
    x - y
}

/// Upstream source: `tests/panic/mir-validation.rs`
pub fn panic_checked_mul_overflow() -> u32 {
    let x: u32 = 100_000;
    let y: u32 = 100_000;
    x * y
}

/// Upstream source: `tests/panic/div-by-zero-2.rs`
pub fn panic_div_by_zero_u32() -> u32 {
    let x: u32 = 42;
    let z: u32 = 0;
    x / z
}

/// Upstream source: `tests/panic/div-by-zero-2.rs`
pub fn panic_rem_by_zero_i32() -> i32 {
    let x: i32 = -42;
    let z: i32 = 0;
    x % z
}

/// Upstream source: `tests/panic/div-by-zero-2.rs`
pub fn panic_signed_div_min_neg_one() -> i32 {
    let x: i32 = i32::MIN;
    let y: i32 = -1;
    x / y
}

/// Upstream source: `tests/panic/overflowing-lsh-neg.rs`
pub fn panic_shl_overflow_u32() -> u32 {
    let x: u32 = 1;
    let shift: u32 = 32;
    x << shift
}

/// Upstream source: `tests/panic/overflowing-rsh-1.rs`
pub fn panic_shr_overflow_i32() -> i32 {
    let x: i32 = 100;
    let shift: i32 = -1;
    x >> shift
}

/// Upstream source: `tests/fail/intrinsics/unchecked_add1.rs`
pub fn ub_unchecked_add_overflow_u32() -> u32 {
    unsafe { unchecked_add(u32::MAX, 1u32) }
}

/// Upstream source: `tests/fail/intrinsics/unchecked_add2.rs`
pub fn ub_unchecked_add_overflow_i32() -> i32 {
    unsafe { unchecked_add(i32::MAX, 1i32) }
}

/// Upstream source: `tests/fail/intrinsics/unchecked_sub1.rs`
pub fn ub_unchecked_sub_underflow_u32() -> u32 {
    unsafe { unchecked_sub(0u32, 1u32) }
}

/// Upstream source: `tests/fail/intrinsics/unchecked_mul1.rs`
pub fn ub_unchecked_mul_overflow_u16() -> u16 {
    unsafe { unchecked_mul(300u16, 300u16) }
}

/// Upstream source: `tests/fail/intrinsics/unchecked_shl.rs`
pub fn ub_unchecked_shl_overflow() -> u32 {
    unsafe { unchecked_shl(1u32, 32u32) }
}

/// Upstream source: `tests/fail/intrinsics/unchecked_shr.rs`
pub fn ub_unchecked_shr_overflow() -> i32 {
    unsafe { unchecked_shr(1i32, 32u32) }
}

/// Upstream source: `tests/fail/intrinsics/div-by-zero.rs`
pub fn ub_unchecked_div_by_zero() -> u32 {
    unsafe { unchecked_div(1u32, 0u32) }
}

/// Upstream source: `tests/fail/intrinsics/unchecked_div1.rs`
pub fn ub_unchecked_div_signed_min_overflow() -> i32 {
    unsafe { unchecked_div(i32::MIN, -1i32) }
}

/// Upstream source: `tests/fail/intrinsics/rem-by-zero.rs`
pub fn ub_unchecked_rem_by_zero() -> u32 {
    unsafe { unchecked_rem(7u32, 0u32) }
}

/// Upstream source: `tests/fail/intrinsics/exact_div1.rs`
pub fn ub_exact_div_non_multiple() -> u32 {
    unsafe { exact_div(19u32, 2u32) }
}

// ============================================================================
// Category 2: Type Validity & Transmutes
// ============================================================================

/// Upstream source: `tests/pass/bools.rs`
pub fn pass_bool_transmute_valid() -> u8 {
    let b_true: bool = unsafe { transmute(1u8) };
    let b_false: bool = unsafe { transmute(0u8) };
    (b_true as u8) * 10 + (b_false as u8)
}

/// Upstream source: `tests/pass/char.rs`
pub fn pass_char_transmute_valid() -> u32 {
    let c: char = unsafe { transmute(0x03BBu32) }; // 'λ'
    c as u32
}

/// Upstream source: `tests/pass/c_enums.rs`
pub fn pass_enum_discriminant_valid() -> u8 {
    let tag: ColorTag = unsafe { transmute(2u8) };
    match tag {
        ColorTag::Red => 10,
        ColorTag::Green => 20,
        ColorTag::Blue => 30,
    }
}

/// Upstream source: `tests/pass/integer-ops.rs`
pub fn pass_transmute_u32_byte_array_le() -> u8 {
    let word: u32 = 0x0403_0201;
    let bytes: [u8; 4] = unsafe { transmute(word) };
    bytes[0] + bytes[3] // 1 + 4 = 5
}

/// Upstream source: `tests/pass/tuples.rs`
pub fn pass_transmute_pair_to_array() -> u32 {
    let pair = PairU32 { a: 11, b: 31 };
    let arr: [u32; 2] = unsafe { transmute(pair) };
    arr[0] + arr[1]
}

/// Upstream source: `tests/fail/validity/invalid_bool.rs`
pub fn ub_transmute_invalid_bool() -> bool {
    let b: bool = unsafe { transmute(2u8) };
    b
}

/// Upstream source: `tests/fail/validity/invalid_char.rs`
pub fn ub_transmute_invalid_char_surrogate() -> char {
    let c: char = unsafe { transmute(0xD800u32) };
    c
}

/// Upstream source: `tests/fail/validity/invalid_char.rs`
pub fn ub_transmute_invalid_char_out_of_range() -> char {
    let c: char = unsafe { transmute(0x11_0000u32) };
    c
}

/// Upstream source: `tests/fail/validity/invalid_enum_tag.rs`
pub fn ub_transmute_invalid_enum_tag() -> ColorTag {
    let c: ColorTag = unsafe { transmute(5u8) };
    c
}

/// Upstream source: `tests/fail/validity/transmute_through_ptr.rs`
pub fn ub_transmute_invalid_bool_through_ptr() -> bool {
    let mut b = false;
    let ptr = (&mut b as *mut bool) as *mut u8;
    unsafe {
        *ptr = 3u8;
    }
    b
}

// ============================================================================
// Category 3: Uninitialized Memory & Struct Padding
// ============================================================================

/// Upstream source: `tests/pass/partially-uninit.rs`
pub fn pass_uninit_union_write_then_read() -> u32 {
    let mut slot: Uninit<u32> = Uninit { uninit: () };
    unsafe {
        slot.value = 99;
        slot.value
    }
}

/// Upstream source: `tests/pass/move-uninit-primval.rs`
pub fn pass_copy_nonoverlapping_uninit_bytes_to_uninit() -> u32 {
    let src: Uninit<[u8; 4]> = Uninit { uninit: () };
    let mut dst: Uninit<[u8; 4]> = Uninit { uninit: () };
    unsafe {
        copy_nonoverlapping(
            (&raw const src.value) as *const u8,
            (&raw mut dst.value) as *mut u8,
            4,
        );
        dst.value = [1, 2, 3, 4];
        (dst.value[0] + dst.value[3]) as u32
    }
}

/// Upstream source: `tests/fail/validity/uninit_integer.rs`
pub fn ub_read_uninit_u32() -> u32 {
    let slot: Uninit<u32> = Uninit { uninit: () };
    unsafe { slot.value }
}

/// Upstream source: `tests/fail/validity/invalid_bool_uninit.rs`
pub fn ub_read_uninit_bool() -> bool {
    let slot: Uninit<bool> = Uninit { uninit: () };
    unsafe { slot.value }
}

/// Upstream source: `tests/fail/uninit/uninit_byte_read.rs`
pub fn ub_read_uninit_byte_from_array() -> u8 {
    let slot: Uninit<[u8; 4]> = Uninit { uninit: () };
    unsafe { slot.value[2] }
}

/// Upstream source: `tests/fail/uninit/padding-struct.rs`
pub fn ub_read_struct_padding_byte() -> u8 {
    let s = PaddedU8U32 {
        tag: 1,
        word: 0x1122_3344,
    };
    let bytes: [u8; 8] = unsafe { transmute(s) };
    bytes[1] // Inter-field padding byte is uninitialized; reading it as `u8` is UB.
}

// ============================================================================
// Category 4: Places, Projections, Arrays, Bounds & Pointers
// ============================================================================

/// Upstream source: `tests/pass/arrays.rs`
pub fn pass_array_index_and_mutation() -> u32 {
    let mut arr: [u32; 4] = [10, 20, 30, 40];
    let idx: usize = 2;
    arr[idx] += 5;
    arr[0] + arr[2]
}

/// Upstream source: `tests/pass/tuples.rs`
pub fn pass_nested_struct_projection() -> u32 {
    let mut pair = PairU32 { a: 7, b: 8 };
    let r = &mut pair.b;
    *r = 15;
    pair.a + pair.b
}

/// Upstream source: `tests/pass/tuples.rs`
pub fn pass_tuple_field_swap() -> u32 {
    let mut t: (u32, u32) = (14, 28);
    let tmp = t.0;
    t.0 = t.1;
    t.1 = tmp;
    t.0 - t.1
}

/// Upstream source: `tests/pass/arrays.rs`
pub fn pass_ref_array_elem_temp_index() -> u32 {
    let arr: [u32; 4] = [10, 20, 30, 40];
    let r: &u32 = &arr[2];
    *r
}

/// Upstream source: `tests/pass/ptr_offset.rs`
pub fn pass_ptr_offset_within_array() -> u32 {
    let pair = PairU32 { a: 100, b: 300 };
    let base: *const u32 = &raw const pair.a;
    unsafe {
        let p1 = offset(base, 1isize);
        *p1
    }
}

/// Upstream source: `tests/pass/subslice_array.rs`
pub fn pass_subslice_pattern_extract() -> u32 {
    let arr: [u32; 4] = [3, 6, 9, 12];
    let [first, middle @ .., last] = arr;
    first + middle[0] + middle[1] + last
}

/// Upstream source: `tests/panic/oob_subslice.rs`
pub fn panic_array_index_out_of_bounds() -> u32 {
    let arr: [u32; 3] = [1, 2, 3];
    let idx: usize = 3;
    arr[idx]
}

/// Upstream source: `tests/fail/dangling_pointers/null_pointer_deref.rs`
pub fn ub_deref_null_ptr_read() -> u32 {
    let p: *const u32 = 0usize as *const u32;
    unsafe { *p }
}

/// Upstream source: `tests/fail/dangling_pointers/null_pointer_write.rs`
pub fn ub_deref_null_ptr_write() {
    let p: *mut u32 = 0usize as *mut u32;
    unsafe {
        *p = 42;
    }
}

/// Upstream source: `tests/fail/dangling_pointers/storage_dead_dangling.rs`
pub fn ub_deref_dead_local_ptr() -> u32 {
    let dangling: *mut u32 = {
        let mut x: u32 = 55;
        &raw mut x
    };
    unsafe { *dangling }
}

/// Upstream source: `tests/fail/dangling_pointers/out_of_bounds_read.rs`
pub fn ub_ptr_offset_oob_read() -> u32 {
    let pair = PairU32 { a: 10, b: 20 };
    let base: *const u32 = &raw const pair.a;
    unsafe {
        let oob = offset(base, 2isize);
        *oob
    }
}

/// Upstream source: `tests/fail/dangling_pointers/out_of_bounds_write.rs`
pub fn ub_ptr_offset_oob_write() {
    let mut pair = PairU32 { a: 10, b: 20 };
    let base: *mut u32 = &raw mut pair.a;
    unsafe {
        let oob = offset(base, 2isize);
        *oob = 99;
    }
}

/// Upstream source: `tests/fail/intrinsics/ptr_offset_out_of_bounds_neg.rs`
pub fn ub_ptr_offset_negative_before_start() -> u32 {
    let pair = PairU32 { a: 10, b: 20 };
    let base: *const u32 = &raw const pair.a;
    unsafe {
        let before = offset(base, -1isize);
        *before
    }
}

/// Upstream source: `tests/fail/unaligned_pointers/unaligned_ptr1.rs`
pub fn ub_unaligned_ptr_read_u32() -> u32 {
    let pair = PairU32 {
        a: 0x0403_0201,
        b: 0x0807_0605,
    };
    let base: *const u8 = (&raw const pair.a) as *const u8;
    unsafe {
        let unaligned: *const u32 = offset(base, 1isize) as *const u32;
        *unaligned
    }
}

// ============================================================================
// Category 5: Intrinsics (`assume`, `copy_nonoverlapping`, `unreachable`)
// ============================================================================

/// Upstream source: `tests/pass/intrinsics/intrinsics.rs`
pub fn pass_assume_true() -> u32 {
    let x: u32 = 12;
    unsafe {
        assume(x == 12);
    }
    x
}

/// Upstream source: `tests/pass/tree_borrows/copy-nonoverlapping.rs`
pub fn pass_copy_nonoverlapping_disjoint_locals() -> u32 {
    let src: u32 = 77;
    let mut dst: u32 = 0;
    unsafe {
        copy_nonoverlapping(&raw const src, &raw mut dst, 1);
    }
    dst
}

/// Upstream source: `tests/pass/tree_borrows/copy-nonoverlapping.rs`
pub fn pass_copy_nonoverlapping_zero_count() -> u32 {
    let mut x: u32 = 50;
    let p: *mut u32 = &raw mut x;
    unsafe {
        copy_nonoverlapping(p as *const u32, p, 0);
    }
    x
}

/// Upstream source: `tests/fail/intrinsics/assume.rs`
pub fn ub_assume_false() -> u32 {
    let x: u32 = 5;
    unsafe {
        assume(x == 6);
    }
    x
}

/// Upstream source: `tests/fail/intrinsics/copy_overlapping.rs`
pub fn ub_copy_nonoverlapping_overlapping() -> u32 {
    let mut x: u32 = 10;
    let p: *mut u32 = &raw mut x;
    unsafe {
        copy_nonoverlapping(p as *const u32, p, 1);
    }
    x
}

/// Upstream source: `tests/fail/unreachable.rs`
pub fn ub_unreachable_executed() -> u32 {
    unsafe { unreachable() }
}

// ============================================================================
// Category 6: Tree Borrows Aliasing, Retags & Interior Mutability
// ============================================================================

/// Upstream source: `tests/pass/tree_borrows/reserved.rs`
pub fn pass_tb_reserved_mut_allow_parent_read() -> u32 {
    let mut x: u32 = 10;
    let root: *mut u32 = &raw mut x;
    let r: &mut u32 = unsafe { &mut *root };
    // Under Tree Borrows, `r` starts `Reserved`; a foreign read through `root`
    // is allowed while `r` remains `Reserved` before any write activates `r`.
    let val = unsafe { *root };
    let _read_r = *r;
    val
}

/// Upstream source: `tests/pass/tree_borrows/reborrow-is-read.rs`
pub fn pass_tb_shared_reborrow_coexistence() -> u32 {
    let x: u32 = 25;
    let r1 = &x;
    let r2 = &*r1;
    *r1 + *r2
}

/// Upstream source: `tests/pass/both_borrows/interior_mutability.rs`
pub fn pass_tb_unsafe_cell_shared_mutation() -> u32 {
    let cell: UnsafeCell<u32> = unsafe { transmute(10u32) };
    let shared_ref: &UnsafeCell<u32> = &cell;
    let ptr: *mut u32 = (shared_ref as *const UnsafeCell<u32>) as *mut u32;
    unsafe {
        *ptr = 42;
        *ptr
    }
}

/// Upstream source: `tests/fail/both_borrows/outdated_local.rs`
pub fn ub_tb_use_frozen_mut_after_parent_read() -> u32 {
    let mut x: u32 = 0;
    let root: *mut u32 = &raw mut x;
    let r: &mut u32 = unsafe { &mut *root };
    *r = 1; // Activates `r` (`Active`).
    let _y = unsafe { *root }; // Foreign read through parent freezes `r` (`Active -> Frozen`).
    *r = 2; // Writing through `Frozen` tag `r` is Tree Borrows UB!
    unsafe { *root }
}

/// Upstream source: `tests/fail/both_borrows/shr_frozen_violation1.rs`
pub fn ub_tb_write_through_shared_ref_cast_mut() -> u32 {
    let x: u32 = 5;
    let shr: &u32 = &x;
    let raw_mut: *mut u32 = (shr as *const u32) as *mut u32;
    unsafe {
        *raw_mut = 9;
    }
    x
}

/// Upstream source: `tests/fail/both_borrows/aliasing_mut1.rs`
pub fn ub_tb_conflicting_active_mut_borrows() -> u32 {
    let mut x: u32 = 1;
    let p1: *mut u32 = &raw mut x;
    let r2: &mut u32 = unsafe { &mut *p1 };
    *r2 = 2; // Activates `r2` (`Active`).
    unsafe {
        *p1 = 3; // Parent write disables child `r2` (`Active -> Disabled`).
    }
    *r2 // Reading through `Disabled` child `r2` is UB!
}

/// Upstream source: `tests/fail/tree_borrows/parent_read_freezes_raw_mut.rs`
pub fn ub_tb_parent_write_disables_shared_ref() -> u32 {
    let mut x: u32 = 10;
    let root: *mut u32 = &raw mut x;
    let shr: &u32 = unsafe { &*root };
    unsafe {
        *root = 20; // Parent write disables `Frozen` shared borrow `shr` (`Frozen -> Disabled`).
    }
    *shr // Reading through `Disabled` `shr` is UB!
}

/// Upstream source: `tests/pass/tree_borrows/reserved.rs`
pub fn tb_child_write_then_parent_read() -> u32 {
    let mut x: u32 = 0;
    let root: *mut u32 = &raw mut x;
    let r: &mut u32 = unsafe { &mut *root };
    *r = 1; // Child write activates `r` without disabling ancestor `root`.
    let y = unsafe { *root }; // Foreign read through parent freezes `r`, returning 1.
    y
}

/// Upstream source: `tests/pass/tree_borrows/reserved.rs`
pub fn tb_child_write_then_parent_write() -> u32 {
    let mut x: u32 = 1;
    let p1: *mut u32 = &raw mut x;
    let r2: &mut u32 = unsafe { &mut *p1 };
    *r2 = 2; // Child write activates `r2` without disabling ancestor `p1`.
    unsafe {
        // Parent write disables child `r2` (`Active -> Disabled`), which is
        // valid if `r2` is not used again.
        *p1 = 3;
    }
    unsafe { *p1 }
}

/// Upstream source: `tests/pass/tree_borrows/reborrow-is-read.rs`
pub fn safe_reborrow_then_parent_write() -> u32 {
    let mut x: u32 = 5;
    let p: &mut u32 = &mut x;
    {
        let q: &mut u32 = &mut *p;
        *q = 6;
    }
    *p = 7;
    *p
}

// ============================================================================
// Category 7: Control Flow, Loops & Function Calls
// ============================================================================

/// Upstream source: `tests/pass/loops.rs`
pub fn pass_while_loop_sum() -> u32 {
    let mut i: u32 = 0;
    let mut acc: u32 = 0;
    while i < 5 {
        acc += i;
        i += 1;
    }
    acc // 0 + 1 + 2 + 3 + 4 = 10
}

/// Upstream source: `tests/pass/enums.rs`
pub fn pass_match_switch_int_branch() -> u32 {
    let x: u32 = 2;
    match x {
        0 => 100,
        1 => 200,
        2 => 300,
        _ => 400,
    }
}

/// Upstream source: `tests/pass/bools.rs`
pub fn pass_short_circuit_and_or() -> u32 {
    let a = true;
    let b = false;
    let r1 = a || (1u32 / 0u32 == 1);
    let r2 = b && (1u32 / 0u32 == 1);
    (r1 as u32) * 10 + (r2 as u32)
}

#[inline(never)]
pub fn helper_add_ten() -> u32 {
    10
}

/// Upstream source: `tests/pass/calls.rs`
pub fn pass_direct_fn_call() -> u32 {
    32 + helper_add_ten()
}

/// Upstream source: `tests/panic/panic1.rs`
pub fn panic_explicit_macro() {
    panic!("explicit panic in corpus");
}

// Category 8: Niche-encoded scalars, `#[repr(transparent)]` wrappers,
// univariant `#[repr(C)]` enums, union overlays, and `&raw` reborrows.

use core::num::NonZeroU32;

#[repr(transparent)]
pub struct MetersU32(pub u32);

#[repr(C)]
pub enum SingleC {
    Only(u32),
}

#[repr(C)]
pub union OverlayU32 {
    pub word: u32,
    pub bytes: [u8; 4],
}

/// Niche validity: a nonzero `u32` round-trips through `NonZeroU32`.
pub fn pass_nonzero_u32_transmute_roundtrip() -> u32 {
    let n: NonZeroU32 = unsafe { transmute::<u32, NonZeroU32>(7u32) };
    unsafe { transmute::<NonZeroU32, u32>(n) }
}

/// Niche validity: transmuting `0` into `NonZeroU32` violates its valid range.
pub fn ub_nonzero_u32_transmute_zero() -> u32 {
    let n: NonZeroU32 = unsafe { transmute::<u32, NonZeroU32>(0u32) };
    unsafe { transmute::<NonZeroU32, u32>(n) }
}

/// Niche encoding: an all-zero `Option<NonZeroU32>` reads back as `None`.
pub fn pass_option_nonzero_none_niche() -> u32 {
    let o: Option<NonZeroU32> = unsafe { transmute::<u32, Option<NonZeroU32>>(0u32) };
    match o {
        Some(_) => 1u32,
        None => 2u32,
    }
}

/// `#[repr(transparent)]` wrapper: transmute a `u32` into `MetersU32` and read
/// its field.
pub fn pass_transparent_wrapper_transmute() -> u32 {
    let m: MetersU32 = unsafe { transmute::<u32, MetersU32>(41u32) };
    m.0 + 1u32
}

/// Univariant `#[repr(C)]` enum: match its payload and reinitialize the whole
/// value.
pub fn pass_single_c_enum_match_reinit() -> u32 {
    let mut s = SingleC::Only(9u32);
    s = SingleC::Only(match s {
        SingleC::Only(v) => v + 1u32,
    });
    match s {
        SingleC::Only(v) => v,
    }
}

/// Univariant `#[repr(C)]` enum: a tag other than `0` is an invalid value.
pub fn ub_single_c_enum_invalid_tag() -> u32 {
    let s: SingleC = unsafe { transmute::<[u32; 2], SingleC>([1u32, 5u32]) };
    match s {
        SingleC::Only(v) => v,
    }
}

/// Union overlay: a byte write through `bytes` changes the `word` read back.
pub fn pass_union_overlay_word_bytes() -> u32 {
    let mut o = OverlayU32 { word: 0x0403_0201 };
    unsafe {
        o.bytes[0] = 9u8;
        o.word
    }
}

/// Union overlay: after one partial byte write, reading another byte reads
/// uninitialized memory.
pub fn ub_union_uninit_bytes_partial_read() -> u32 {
    let mut u: Uninit<[u8; 4]> = Uninit { uninit: () };
    unsafe {
        u.value[0] = 3u8;
        u.value[0] as u32 + u.value[1] as u32
    }
}

/// `Retag(Raw)`: `&raw const` and `&raw mut` reborrows of disjoint fields
/// coexist.
pub fn pass_raw_ref_disjoint_fields() -> u32 {
    let mut pair = PairU32 { a: 1u32, b: 2u32 };
    let p: *mut PairU32 = &mut pair;
    unsafe {
        let ra: *const u32 = &raw const (*p).a;
        let rb: *mut u32 = &raw mut (*p).b;
        *rb = 5u32;
        *ra + *rb
    }
}

/// `Retag(Raw)`: a parent write disables the child that a `&raw mut` pointer
/// shares.
pub fn ub_raw_mut_after_parent_write() -> u32 {
    let mut slot: u32 = 1u32;
    let x: &mut u32 = &mut slot;
    let y: &mut u32 = &mut *x;
    let r: *mut u32 = &raw mut *y;
    *y = 2u32;
    let y_seen: u32 = *y;
    *x = y_seen + 1u32;
    unsafe {
        *r = 4u32;
    }
    slot
}

#[repr(transparent)]
pub struct NonZeroMeters(pub NonZeroU32);

/// `#[repr(transparent)]` niche validity: transmuting `0` into `NonZeroMeters`
/// violates its inner `NonZeroU32` valid range.
pub fn ub_transparent_nonzero_wrapper_zero() -> u32 {
    let m: NonZeroMeters = unsafe { transmute::<u32, NonZeroMeters>(0u32) };
    unsafe { transmute::<NonZeroU32, u32>(m.0) }
}

/// Niche encoding and `&mut` univariant `#[repr(C)]` projection: encode a
/// `Some(NonZeroU32)` via `transmute`, match `Option<ColorTag>`, and mutate a
/// `SingleC` payload through `&mut SingleC` before whole-value reinit.
pub fn pass_option_some_niche_and_single_c_mut() -> u32 {
    let nz: NonZeroU32 = unsafe { transmute::<u32, NonZeroU32>(7u32) };
    let some_bits: u32 = unsafe { transmute::<Option<NonZeroU32>, u32>(Some(nz)) };
    let none_bits: u32 = unsafe { transmute::<Option<NonZeroU32>, u32>(None) };
    let oc: Option<ColorTag> = Some(ColorTag::Green);
    let color_val: u32 = match oc {
        Some(ColorTag::Red) => 1u32,
        Some(ColorTag::Green) => 2u32,
        Some(ColorTag::Blue) => 3u32,
        None => 4u32,
    };
    let mut s = SingleC::Only(some_bits ^ none_bits ^ color_val);
    match &mut s {
        SingleC::Only(p) => {
            *p ^= 12u32;
        }
    }
    s = SingleC::Only(match s {
        SingleC::Only(v) => v ^ 3u32,
    });
    match s {
        SingleC::Only(v) => v,
    }
}

// ============================================================================
// Category 9: `Operand::Move` Deinitialization Borrow-Tree Invariance,
// `RetagKind::FnEntry` Reference Arguments Across `#[inline(never)]`
// Multi-Callee Chains (Including an `UnwindAction::Cleanup` Unwind Edge), and
// Inline Scalar & Memory Intrinsics.
//
// The call-chain helpers below carry `__ANNEAL_MODEL_<name>` markers, so the
// differential suite links their captured bodies as intra-crate callees rather
// than treating them as standalone zero-argument test entry points.
//
// Anneal currently mishandles memory that a reference argument points into
// across a call boundary (see "Category 9 engine gaps" in
// `tests/miri-diff/README.md`; `miri_difftest_oracle.rs` pins all five gaps
// with live kernel confirmation). Every helper here therefore takes its
// `FnEntry`-protected reference without dereferencing it, and only forwards or
// returns reborrows of it: these seeds check reference-argument passing,
// reborrow return, frame cleanup, and unwinding, not protector enforcement.
// ============================================================================

use core::intrinsics::{
    arith_offset, bitreverse, bswap, ctlz, ctlz_nonzero, ctpop, cttz, cttz_nonzero, saturating_add,
    saturating_sub, three_way_compare, wrapping_add, wrapping_mul, wrapping_sub,
};

#[repr(C)]
pub struct NonCopyU32(pub u32);

#[repr(C)]
pub struct NonCopyPairU32 {
    pub a: NonCopyU32,
    pub b: u32,
}

/// Byte-fill emulation of `write_bytes(dst, val, count)` for `*mut u32`
/// destinations, built from `transmute`, `offset`, and `copy_nonoverlapping`.
///
/// `core::intrinsics::write_bytes` is not one of the intrinsics that Anneal's
/// `MirSemantics` interprets inline (`classifyRustIntrinsic?`), so a direct call
/// would stop at an uninterpreted external call; the emulation keeps the byte
/// pattern observable to both Miri and Anneal.
#[allow(unused_macros)]
macro_rules! write_bytes {
    ($dst:expr, $val:expr, $count:expr) => {{
        let __wb_dst: *mut u32 = $dst;
        let __wb_b: u8 = $val;
        let __wb_cnt: usize = $count;
        let __wb_pat: u32 = transmute::<[u8; 4], u32>([__wb_b, __wb_b, __wb_b, __wb_b]);
        let mut __wb_i: usize = 0;
        while __wb_i < __wb_cnt {
            let __wb_slot: *mut u32 = offset(__wb_dst, __wb_i as isize);
            copy_nonoverlapping(&raw const __wb_pat, __wb_slot, 1);
            __wb_i += 1;
        }
    }};
}

#[allow(non_upper_case_globals)]
pub const __ANNEAL_MODEL_helper_reborrow_leaf: &str = "helper_reborrow_leaf";
/// Depth-2 leaf of the `helper_reborrow_mid` chain.
#[inline(never)]
pub fn helper_reborrow_leaf(v: u32) -> u32 {
    v
}

#[allow(non_upper_case_globals)]
pub const __ANNEAL_MODEL_helper_reborrow_mid: &str = "helper_reborrow_mid";
/// Takes an `FnEntry`-protected `&mut u32` (Miri retags and protects it on
/// entry and releases the protector on return) and calls `helper_reborrow_leaf`
/// while the protector is active. It does not dereference `_r` (see the
/// Category 9 header).
#[inline(never)]
pub fn helper_reborrow_mid(_r: &mut u32, _extra: u32) -> u32 {
    helper_reborrow_leaf(22u32)
}

#[allow(non_upper_case_globals)]
pub const __ANNEAL_MODEL_helper_reborrow_return: &str = "helper_reborrow_return";
/// Returns a reborrowed child of its `FnEntry`-protected `&mut u32` argument;
/// the child outlives the callee frame and its protector.
#[inline(never)]
pub fn helper_reborrow_return(r: &mut u32) -> &mut u32 {
    &mut *r
}

#[allow(non_upper_case_globals)]
pub const __ANNEAL_MODEL_helper_shared_leaf: &str = "helper_shared_leaf";
/// Depth-2 leaf of the `helper_shared_mid` chain.
#[inline(never)]
pub fn helper_shared_leaf(v: u32) -> u32 {
    v
}

#[allow(non_upper_case_globals)]
pub const __ANNEAL_MODEL_helper_shared_mid: &str = "helper_shared_mid";
/// Takes an `FnEntry`-protected `&u32` and calls `helper_shared_leaf` while the
/// protector is active, without dereferencing `_r`.
#[inline(never)]
pub fn helper_shared_mid(_r: &u32, _bonus: u32) -> u32 {
    helper_shared_leaf(25u32)
}

#[allow(non_upper_case_globals)]
pub const __ANNEAL_MODEL_helper_frozen_reborrow_write_in_callee: &str =
    "helper_frozen_reborrow_write_in_callee";
/// Tree Borrows UB confined to the callee's own frame: a `&mut` reborrow of
/// the by-value parameter `slot` is activated by a write, frozen by a read
/// through the parent raw pointer, and then written again. No reference
/// argument or `FnEntry` protector is involved.
#[inline(never)]
pub fn helper_frozen_reborrow_write_in_callee(mut slot: u32) -> u32 {
    let raw: *mut u32 = &raw mut slot;
    let r: &mut u32 = unsafe { &mut *raw };
    *r = helper_reborrow_leaf(55u32);
    let _ = unsafe { *raw };
    *r = 99u32;
    *r
}

#[allow(non_upper_case_globals)]
pub const __ANNEAL_MODEL_helper_unwind_leaf: &str = "helper_unwind_leaf";
/// Panics (`attempt to add with overflow`) when `base + delta` overflows.
#[inline(never)]
pub fn helper_unwind_leaf(base: u32, delta: u32) -> u32 {
    base + delta
}

#[allow(non_upper_case_globals)]
pub const __ANNEAL_MODEL_helper_unwind_mid: &str = "helper_unwind_mid";
/// Calls the overflowing `helper_unwind_leaf(u32::MAX, 1)` while holding an
/// `FnEntry`-protected `&u32`, so the panic unwinds through two frames.
#[inline(never)]
pub fn helper_unwind_mid(_protected: &u32, _base: u32) -> u32 {
    helper_unwind_leaf(u32::MAX, 1u32)
}

/// Guard with an (empty) `Drop` impl: while one is live, a call's unwind edge
/// is `UnwindAction::Cleanup` into a landing pad that drops the guard.
pub struct UnwindCleanupGuard(pub u32);

impl Drop for UnwindCleanupGuard {
    fn drop(&mut self) {}
}

#[allow(non_upper_case_globals)]
pub const __ANNEAL_MODEL_helper_unwind_guarded: &str = "helper_unwind_guarded";
/// Calls `helper_unwind_leaf(base, delta)` while an `UnwindCleanupGuard` is
/// live, so the call unwinds through an `UnwindAction::Cleanup` landing pad.
#[inline(never)]
pub fn helper_unwind_guarded(base: u32, delta: u32) -> u32 {
    let _guard = UnwindCleanupGuard(base);
    helper_unwind_leaf(base, delta)
}

/// `Operand::Move` deinitialization borrow-tree invariance: moving a non-`Copy`
/// wrapper does not emit a foreign `.Write`, so a prior `Reserved` `&mut u32`
/// child borrow remains `Reserved` and can re-initialize the moved place.
pub fn pass_move_deinit_preserves_reserved_child() -> u32 {
    let mut x = NonCopyU32(10u32);
    let root: *mut NonCopyU32 = &raw mut x;
    let r: &mut NonCopyU32 = unsafe { &mut *root };
    let moved: NonCopyU32 = x;
    *r = NonCopyU32(32u32);
    (*r).0 + moved.0
}

/// `Operand::Move` sub-place deinitialization: moving field `a` leaves an
/// active `Frozen` shared borrow on sibling field `b` valid.
pub fn pass_move_deinit_subplace_preserves_sibling_frozen() -> u32 {
    let p = NonCopyPairU32 {
        a: NonCopyU32(20u32),
        b: 30u32,
    };
    let r_b: &u32 = &p.b;
    let moved_a: NonCopyU32 = p.a;
    moved_a.0 + *r_b
}

/// Reading a moved-from source place through a raw pointer once its storage is
/// dead is UB in both Miri and Anneal.
///
/// Miri evaluates `Operand::Move` like `Operand::Copy` and leaves the source
/// bytes initialized, while Anneal de-initializes them, so a raw read of `x`
/// while `x` is still in scope (after `let moved = x;`) passes in Miri but is UB
/// in Anneal (a sound conservative `false_positive_ub`, pinned in
/// `miri_difftest_oracle.rs`). Ending `x`'s scope (`StorageDead`) before the
/// read makes the read UB under both semantics.
pub fn ub_move_deinit_read_source_uninit() -> u32 {
    let (raw, moved) = {
        let x = NonCopyU32(15u32);
        let raw: *const u32 = &raw const x.0;
        let moved: NonCopyU32 = x;
        (raw, moved)
    };
    let leaked: u32 = unsafe { *raw };
    moved.0 + leaked
}

/// Contrasting parent assignment vs. `Operand::Move`: an explicit assignment
/// `x = NonCopyU32(...)` emits a foreign `.Write` that disables an active child
/// borrow before subsequent child use.
pub fn ub_assign_after_reborrow_disables_child() -> u32 {
    let mut x = NonCopyU32(10u32);
    let root: *mut NonCopyU32 = &raw mut x;
    let r: &mut u32 = unsafe { &mut (*root).0 };
    *r = 11u32;
    let seen: u32 = *r;
    x = NonCopyU32(seen + 1u32);
    let after: u32 = x.0;
    *r = after + 87u32;
    x.0
}

/// A raw-derived `&mut u32` is reborrowed into the depth-2 `#[inline(never)]`
/// chain `helper_reborrow_mid` -> `helper_reborrow_leaf` (Miri protects the
/// reborrow for the duration of the call and releases the protector on return),
/// then written through the child and the parent raw pointer after the callee
/// frames are gone.
pub fn pass_fn_entry_protector_two_stage_reborrow_chain() -> u32 {
    let mut x: u32 = 10u32;
    let raw: *mut u32 = &raw mut x;
    let r0: &mut u32 = unsafe { &mut *raw };
    let delta: u32 = helper_reborrow_mid(r0, 7u32);
    *r0 = 20u32;
    unsafe {
        *raw = *r0 + delta;
        *raw
    }
}

/// A shared `&u32` passes through the `FnEntry`-protected depth-2 chain
/// `helper_shared_mid` -> `helper_shared_leaf`; once the call returns, writing
/// the parent local is legal.
pub fn pass_fn_entry_shared_reborrow_chain() -> u32 {
    let mut x: u32 = 19u32;
    let r_shared: &u32 = &x;
    let read_val: u32 = helper_shared_mid(r_shared, 3u32);
    x = read_val;
    x
}

/// After the `helper_reborrow_mid` chain returns (releasing its protector), the
/// result is passed by value to `helper_frozen_reborrow_write_in_callee`, whose
/// write through a frozen callee-local reborrow is UB inside the callee frame.
pub fn ub_frozen_reborrow_write_in_callee_frame() -> u32 {
    let mut x: u32 = 10u32;
    let raw_alias: *mut u32 = &raw mut x;
    let delta: u32 = helper_reborrow_mid(unsafe { &mut *raw_alias }, 1u32);
    unsafe {
        *raw_alias = delta;
    }
    helper_frozen_reborrow_write_in_callee(unsafe { *raw_alias })
}

/// Unwinding panic across a depth-2 `#[inline(never)]` helper call chain with
/// an `FnEntry`-protected reference argument (`UnwindAction::Continue` edges).
pub fn panic_multi_callee_unwind_chain() -> u32 {
    let x: u32 = 1u32;
    helper_unwind_mid(&x, u32::MAX)
}

/// A reborrowed child returned by `helper_reborrow_return` outlives the callee
/// frame and its released `FnEntry` protector: the caller writes through the
/// child, and a later parent write disables the (dead) child without UB.
pub fn pass_fn_entry_returns_reborrowed_child() -> u32 {
    let mut x: u32 = 3u32;
    let child: &mut u32 = helper_reborrow_return(&mut x);
    *child = *child + 4u32;
    x = x + 1u32;
    x
}

/// Unwinding panic whose depth-2 call edge `helper_unwind_guarded` ->
/// `helper_unwind_leaf` is `UnwindAction::Cleanup`: the landing pad drops the
/// live `UnwindCleanupGuard` before the panic propagates to the caller.
pub fn panic_multi_callee_unwind_cleanup_guard() -> u32 {
    let start: u32 = u32::MAX;
    helper_unwind_guarded(start, 1u32)
}

/// Inline bit-counting and byte/bit-reversal intrinsics (`ctlz`, `ctlz_nonzero`,
/// `cttz`, `cttz_nonzero`, `ctpop`, `bswap`, `bitreverse`).
pub fn pass_intrinsics_bit_count_and_reverse() -> u32 {
    let v: u32 = 0x00F0_0800u32;
    let lz: u32 = ctlz(v);
    let lz_nz: u32 = unsafe { ctlz_nonzero(v) };
    let tz: u32 = cttz(v);
    let tz_nz: u32 = unsafe { cttz_nonzero(v) };
    let pop: u32 = ctpop(v);
    let swapped: u32 = bswap(0x0102_0304u32);
    let rev_back: u32 = bitreverse(bitreverse(9u32));
    lz + lz_nz + tz + tz_nz + pop + (swapped & 0xFFu32) + rev_back
}

/// Inline saturating and wrapping arithmetic intrinsics (`saturating_add`,
/// `saturating_sub`, `wrapping_add`, `wrapping_sub`, `wrapping_mul`).
pub fn pass_intrinsics_saturating_and_wrapping() -> u32 {
    let sat_hi: u8 = saturating_add(250u8, 20u8);
    let sat_lo: u8 = saturating_sub(5u8, 12u8);
    let wrap_a: u32 = wrapping_add(u32::MAX, 10u32);
    let wrap_s: u32 = wrapping_sub(3u32, 4u32);
    let wrap_m: u32 = wrapping_mul(wrap_s, 0u32);
    let signed_sat: i8 = saturating_sub(-120i8, 20i8);
    let signed_min_flag: u32 = if signed_sat == i8::MIN { 1u32 } else { 0u32 };
    (sat_hi as u32) + (sat_lo as u32) + wrap_a + wrap_m + signed_min_flag
}

/// Inline `three_way_compare` and `exact_div` across signed and unsigned
/// integer types.
pub fn pass_intrinsics_three_way_compare_and_exact_div() -> u32 {
    let cmp_lt = three_way_compare(3u32, 9u32);
    let cmp_eq = three_way_compare(5i32, 5i32);
    let cmp_gt = three_way_compare(7i32, -2i32);
    let q_u: u32 = unsafe { exact_div(84u32, 4u32) };
    let q_s: i32 = unsafe { exact_div(-36i32, -6i32) };
    let ord_score: u32 = if (cmp_lt as i8) < 0 && (cmp_eq as i8) == 0 && (cmp_gt as i8) > 0 {
        4u32
    } else {
        0u32
    };
    q_u + (q_s as u32) + ord_score
}

/// Memory and pointer intrinsics: `write_bytes!`, disjoint `copy_nonoverlapping`,
/// and wrapping `arith_offset` pointer arithmetic.
pub fn pass_intrinsics_write_bytes_copy_and_arith_offset() -> u32 {
    let mut src = PairU32 { a: 0u32, b: 200u32 };
    let mut dst: u32 = 0u32;
    unsafe {
        write_bytes!(&raw mut src.a, 0x01u8, 1usize);
        copy_nonoverlapping(&raw const src.a, &raw mut dst, 1usize);
        let base: *const u32 = &raw const src.a;
        let far: *const u32 = arith_offset(base, 6isize);
        let back_to_b: *const u32 = arith_offset(far, -5isize);
        (dst & 0xFFu32) + *back_to_b
    }
}

/// `ctlz_nonzero(0u32)` violates the non-zero precondition.
pub fn ub_ctlz_nonzero_zero() -> u32 {
    let zero: u32 = 0u32;
    unsafe { ctlz_nonzero(zero) }
}

/// `cttz_nonzero(0u32)` violates the non-zero precondition.
pub fn ub_cttz_nonzero_zero() -> u32 {
    let zero: u32 = 0u32;
    unsafe { cttz_nonzero(zero) }
}

/// `exact_div(7u32, 2u32)` violates the exact-divisibility precondition.
pub fn ub_exact_div_non_exact_u32() -> u32 {
    unsafe { exact_div(7u32, 2u32) }
}

/// `exact_div(i8::MIN, -1i8)` overflows signed 8-bit two's-complement range.
pub fn ub_exact_div_signed_min_overflow_i8() -> i32 {
    unsafe { exact_div(i8::MIN, -1i8) as i32 }
}

/// `copy_nonoverlapping` with overlapping source and destination ranges in the
/// same array allocation is UB.
pub fn ub_copy_nonoverlapping_partial_overlap_array() -> u32 {
    let mut arr: [u32; 4] = [10u32, 20u32, 30u32, 40u32];
    let p: *mut u32 = &raw mut arr[0];
    unsafe {
        let dst: *mut u32 = offset(p, 1isize);
        copy_nonoverlapping(p as *const u32, dst, 2usize);
    }
    arr[2]
}
