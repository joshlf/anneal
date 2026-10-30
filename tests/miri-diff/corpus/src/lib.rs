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
