//! Miri oracle harness for `miri_diff_corpus`.
//!
//! Invoked by `tests/miri-diff/sync_miri_suite.py` (or `cargo +nightly-2026-06-01 miri`)
//! with `<test_name>` as the first command-line argument. Executes the named
//! corpus function under Miri (`-Zmiri-tree-borrows`) and prints a canonical
//! `MIRI_PASS:<kind>` line on normal return; panics and Undefined Behavior are
//! reported directly by Miri on stderr with non-zero exit status.

use miri_diff_corpus::*;

fn print_u8(v: u8) {
    println!("MIRI_PASS:scalar:{}:1", v as u128);
}

fn print_u16(v: u16) {
    println!("MIRI_PASS:scalar:{}:2", v as u128);
}

fn print_u32(v: u32) {
    println!("MIRI_PASS:scalar:{}:4", v as u128);
}

fn print_i32(v: i32) {
    let bits = (v as u32) as u128;
    println!("MIRI_PASS:scalar:{}:4", bits);
}

fn print_bool(v: bool) {
    println!("MIRI_PASS:scalar:{}:1", if v { 1 } else { 0 });
}

fn print_char(v: char) {
    println!("MIRI_PASS:scalar:{}:4", v as u32);
}

fn print_color(v: ColorTag) {
    println!("MIRI_PASS:scalar:{}:1", v as u8);
}

fn print_unit(_: ()) {
    println!("MIRI_PASS:unit");
}

fn main() {
    let name = std::env::args()
        .nth(1)
        .or_else(|| std::env::var("MIRI_DIFF_TEST").ok());
    let Some(name) = name else {
        eprintln!("usage: miri_eval <test_name> (or set MIRI_DIFF_TEST)");
        std::process::exit(2);
    };
    match name.as_str() {
        // Category 1: Scalar arithmetic, bitwise, shifts & overflow
        "pass_integer_arith_basic" => print_u32(pass_integer_arith_basic()),
        "pass_signed_arith_neg_div_rem" => print_i32(pass_signed_arith_neg_div_rem()),
        "pass_bitwise_and_or_xor_not" => print_u32(pass_bitwise_and_or_xor_not()),
        "pass_shifts_u32_i32" => print_i32(pass_shifts_u32_i32()),
        "pass_comparisons_and_eq" => print_u32(pass_comparisons_and_eq()),
        "pass_unchecked_arith_in_bounds" => print_u32(pass_unchecked_arith_in_bounds()),
        "pass_exact_div_valid" => print_u32(pass_exact_div_valid()),
        "pass_int_widening_and_truncating_casts" => {
            print_i32(pass_int_widening_and_truncating_casts())
        }
        "panic_checked_add_overflow" => print_u32(panic_checked_add_overflow()),
        "panic_checked_sub_underflow" => print_u32(panic_checked_sub_underflow()),
        "panic_checked_mul_overflow" => print_u32(panic_checked_mul_overflow()),
        "panic_div_by_zero_u32" => print_u32(panic_div_by_zero_u32()),
        "panic_rem_by_zero_i32" => print_i32(panic_rem_by_zero_i32()),
        "panic_signed_div_min_neg_one" => print_i32(panic_signed_div_min_neg_one()),
        "panic_shl_overflow_u32" => print_u32(panic_shl_overflow_u32()),
        "panic_shr_overflow_i32" => print_i32(panic_shr_overflow_i32()),
        "ub_unchecked_add_overflow_u32" => print_u32(ub_unchecked_add_overflow_u32()),
        "ub_unchecked_add_overflow_i32" => print_i32(ub_unchecked_add_overflow_i32()),
        "ub_unchecked_sub_underflow_u32" => print_u32(ub_unchecked_sub_underflow_u32()),
        "ub_unchecked_mul_overflow_u16" => print_u16(ub_unchecked_mul_overflow_u16()),
        "ub_unchecked_shl_overflow" => print_u32(ub_unchecked_shl_overflow()),
        "ub_unchecked_shr_overflow" => print_i32(ub_unchecked_shr_overflow()),
        "ub_unchecked_div_by_zero" => print_u32(ub_unchecked_div_by_zero()),
        "ub_unchecked_div_signed_min_overflow" => {
            print_i32(ub_unchecked_div_signed_min_overflow())
        }
        "ub_unchecked_rem_by_zero" => print_u32(ub_unchecked_rem_by_zero()),
        "ub_exact_div_non_multiple" => print_u32(ub_exact_div_non_multiple()),

        // Category 2: Type validity & transmutes
        "pass_bool_transmute_valid" => print_u8(pass_bool_transmute_valid()),
        "pass_char_transmute_valid" => print_u32(pass_char_transmute_valid()),
        "pass_enum_discriminant_valid" => print_u8(pass_enum_discriminant_valid()),
        "pass_transmute_u32_byte_array_le" => print_u8(pass_transmute_u32_byte_array_le()),
        "pass_transmute_pair_to_array" => print_u32(pass_transmute_pair_to_array()),
        "ub_transmute_invalid_bool" => print_bool(ub_transmute_invalid_bool()),
        "ub_transmute_invalid_char_surrogate" => print_char(ub_transmute_invalid_char_surrogate()),
        "ub_transmute_invalid_char_out_of_range" => {
            print_char(ub_transmute_invalid_char_out_of_range())
        }
        "ub_transmute_invalid_enum_tag" => print_color(ub_transmute_invalid_enum_tag()),
        "ub_transmute_invalid_bool_through_ptr" => {
            print_bool(ub_transmute_invalid_bool_through_ptr())
        }

        // Category 3: Uninitialized memory & struct padding
        "pass_uninit_union_write_then_read" => print_u32(pass_uninit_union_write_then_read()),
        "pass_copy_nonoverlapping_uninit_bytes_to_uninit" => {
            print_u32(pass_copy_nonoverlapping_uninit_bytes_to_uninit())
        }
        "ub_read_uninit_u32" => print_u32(ub_read_uninit_u32()),
        "ub_read_uninit_bool" => print_bool(ub_read_uninit_bool()),
        "ub_read_uninit_byte_from_array" => print_u8(ub_read_uninit_byte_from_array()),
        "ub_read_struct_padding_byte" => print_u8(ub_read_struct_padding_byte()),

        // Category 4: Places, projections, arrays, bounds & pointers
        "pass_array_index_and_mutation" => print_u32(pass_array_index_and_mutation()),
        "pass_nested_struct_projection" => print_u32(pass_nested_struct_projection()),
        "pass_tuple_field_swap" => print_u32(pass_tuple_field_swap()),
        "pass_ref_array_elem_temp_index" => print_u32(pass_ref_array_elem_temp_index()),
        "pass_ptr_offset_within_array" => print_u32(pass_ptr_offset_within_array()),
        "pass_subslice_pattern_extract" => print_u32(pass_subslice_pattern_extract()),
        "panic_array_index_out_of_bounds" => print_u32(panic_array_index_out_of_bounds()),
        "ub_deref_null_ptr_read" => print_u32(ub_deref_null_ptr_read()),
        "ub_deref_null_ptr_write" => print_unit(ub_deref_null_ptr_write()),
        "ub_deref_dead_local_ptr" => print_u32(ub_deref_dead_local_ptr()),
        "ub_ptr_offset_oob_read" => print_u32(ub_ptr_offset_oob_read()),
        "ub_ptr_offset_oob_write" => print_unit(ub_ptr_offset_oob_write()),
        "ub_ptr_offset_negative_before_start" => print_u32(ub_ptr_offset_negative_before_start()),
        "ub_unaligned_ptr_read_u32" => print_u32(ub_unaligned_ptr_read_u32()),

        // Category 5: Intrinsics (`assume`, `copy_nonoverlapping`, `unreachable`)
        "pass_assume_true" => print_u32(pass_assume_true()),
        "pass_copy_nonoverlapping_disjoint_locals" => {
            print_u32(pass_copy_nonoverlapping_disjoint_locals())
        }
        "pass_copy_nonoverlapping_zero_count" => print_u32(pass_copy_nonoverlapping_zero_count()),
        "ub_assume_false" => print_u32(ub_assume_false()),
        "ub_copy_nonoverlapping_overlapping" => print_u32(ub_copy_nonoverlapping_overlapping()),
        "ub_unreachable_executed" => print_u32(ub_unreachable_executed()),

        // Category 6: Tree Borrows aliasing, retags & interior mutability
        "pass_tb_reserved_mut_allow_parent_read" => {
            print_u32(pass_tb_reserved_mut_allow_parent_read())
        }
        "pass_tb_shared_reborrow_coexistence" => print_u32(pass_tb_shared_reborrow_coexistence()),
        "pass_tb_unsafe_cell_shared_mutation" => print_u32(pass_tb_unsafe_cell_shared_mutation()),
        "ub_tb_use_frozen_mut_after_parent_read" => {
            print_u32(ub_tb_use_frozen_mut_after_parent_read())
        }
        "ub_tb_write_through_shared_ref_cast_mut" => {
            print_u32(ub_tb_write_through_shared_ref_cast_mut())
        }
        "ub_tb_conflicting_active_mut_borrows" => print_u32(ub_tb_conflicting_active_mut_borrows()),
        "ub_tb_parent_write_disables_shared_ref" => {
            print_u32(ub_tb_parent_write_disables_shared_ref())
        }

        // Category 7: Control flow, loops & function calls
        "pass_while_loop_sum" => print_u32(pass_while_loop_sum()),
        "pass_match_switch_int_branch" => print_u32(pass_match_switch_int_branch()),
        "pass_short_circuit_and_or" => print_u32(pass_short_circuit_and_or()),
        "pass_direct_fn_call" => print_u32(pass_direct_fn_call()),
        "panic_explicit_macro" => print_unit(panic_explicit_macro()),

        other => {
            eprintln!("unknown test: {other}");
            std::process::exit(2);
        }
    }
}
