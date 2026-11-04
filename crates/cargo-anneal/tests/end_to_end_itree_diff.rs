// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Milestone 1 & Milestone 2: Hermetic `itree-diff` differential test suite
//! (`tests/itree-diff/`).
//!
//! Exercises the 30 curated seed functions in `tests/itree-diff/corpus/src/lib.rs`
//! (spanning Categories 1–6) and the 45 harvested `rustc mir-opt` / `zerocopy` /
//! `fxfs` functions in `tests/itree-diff/corpus/src/harvested.rs`:
//! 1. Verifies native execution under `TraceRecorder` (`value_as_raw_bytes`,
//!    struct padding preservation, real `#[anneal_trace::external]` call
//!    boundary interposition, and unwinding) by invoking the unmodified corpus
//!    root functions directly.
//! 2. Verifies Category 5 metamorphic call-boundary duality (`inlinedCallees` vs.
//!    `MirCallE` external call trace agreement) by executing the unmodified
//!    Category 5 root functions under `TraceRecorder::observe_root_with_inlined_callees`
//!    and `TraceRecorder::observe_root`.
//! 3. Captures MIR via `anneal-rustc-capture`, scaffolds `.anneal/`, emits a
//!    `TraceCheck` verification module, and checks kernel `by rfl` soundness and
//!    `TraceReplayDiag` diagnostics via `lake env lean` — including negative
//!    controls proving that mutating a corpus function body changes the observed
//!    trace, and that mutating captured MIR or swapping the root function makes
//!    Lean report a divergence (`!= "ok"`).

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use cargo_anneal::{
    BatchTraceEvalCase, CaptureDriverConfig, RecordedEvent, RecordedOutcome, ScaffoldConfig,
    TraceCheckModuleConfig, TraceRecorder, capture_value_bytes, parse_batch_trace_probe_output,
    render_batch_trace_eval_lean_module, render_batch_trace_probe_lean_module, run_cargo_capture,
    run_lake_verify_targets, scaffold_workspace_with_config, value_as_raw_bytes,
};

#[path = "../../../tests/itree-diff/corpus/src/lib.rs"]
mod corpus;
use corpus::harvested;

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
        .to_path_buf()
}

fn ensure_rustc_capture_bin() -> PathBuf {
    let root = repo_root();
    let bin_path = root.join("target/debug/anneal-rustc-capture");
    if bin_path.is_file() {
        return bin_path;
    }
    let status = Command::new("cargo")
        .args(["build", "-p", "anneal-rustc-capture", "--locked"])
        .current_dir(&root)
        .status()
        .expect("build anneal-rustc-capture");
    assert!(status.success(), "building anneal-rustc-capture failed");
    bin_path
}

fn unique_temp_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "anneal_itree_diff_{label}_{}_{nanos}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

/// Milestone 1 & 2 Calibration Gate:
/// Runs all 30 curated functions (Categories 1–6) and all 45 harvested functions
/// (`miropt_*`, `zc_*`, `fxfs_*`) natively under `TraceRecorder`, verifying:
/// - 100% pass rate across Categories 1–5 (25/25) and Category 6 (5/5 = 30/30 = 100%),
/// - 100% metamorphic inline-vs-external outcome parity across all 5 Category 5 functions,
/// - 100% pass rate across all 45 Milestone 2 harvested functions (45/45 = 100%).
#[test]
fn m1_and_m2_curated_30_and_harvested_45_native_and_metamorphic_calibration_gate() {
    let manifest_path = repo_root().join("tests/itree-diff/manifest.toml");
    let manifest_text =
        fs::read_to_string(&manifest_path).expect("read tests/itree-diff/manifest.toml");
    assert!(manifest_text.contains("anneal-itree-diff-v1"));

    let mut passed_curated = 0usize;

    // --- Category 1 (5/5): Multi-argument scalar & bitwise ---
    assert_eq!(corpus::clamp_u32_range(5, 10, 20), 10);
    assert_eq!(corpus::clamp_u32_range(15, 10, 20), 15);
    assert_eq!(corpus::clamp_u32_range(25, 10, 20), 20);
    passed_curated += 1;

    assert_eq!(
        corpus::rotate_xor_mix(0x1234_5678, 0x00FF_00FF, 4),
        (0x1234_5678u32 ^ 0x00FF_00FF).rotate_left(4)
    );
    passed_curated += 1;

    assert_eq!(corpus::checked_affine_step(10, 4, 7), 47);
    assert_eq!(corpus::checked_affine_step(u32::MAX, 1, 10), u32::MAX);
    passed_curated += 1;

    assert_eq!(corpus::signed_abs_diff(-10, 25), 35);
    assert_eq!(corpus::signed_abs_diff(25, -10), 35);
    passed_curated += 1;

    assert_eq!(corpus::bitfield_extract(0xABCD_EF01, 8, 0xFF), 0xEF);
    passed_curated += 1;

    // --- Category 2 (5/5): Structs, tuples & enums with inter-field padding ---
    let mut padded_hdr = corpus::PaddedHeader {
        tag: 1,
        len: 38,
    };
    unsafe {
        let base = (&raw mut padded_hdr).cast::<u8>();
        *base.add(1) = 0xAA;
        *base.add(2) = 0xBB;
        *base.add(3) = 0xCC;
    }
    let raw_hdr_bytes = value_as_raw_bytes(&padded_hdr);
    assert_eq!(
        capture_value_bytes(&padded_hdr),
        vec![
            Some(1),
            None,
            None,
            None,
            Some(38),
            Some(0),
            Some(0),
            Some(0)
        ]
    );
    assert_eq!(raw_hdr_bytes.len(), 8);
    assert_eq!(&raw_hdr_bytes[1..4], &[0, 0, 0]);
    assert_eq!(corpus::repr_c_padded_header(padded_hdr, 4), 42);
    passed_curated += 1;

    let pair = corpus::NestedPair {
        flag: 1,
        left: 7,
        right: 8,
    };
    assert_eq!(corpus::nested_tuple_struct_sum(pair, 3), 45);
    passed_curated += 1;

    assert_eq!(
        corpus::c_like_enum_dispatch(corpus::DispatchMode::Add, 19, 23),
        42
    );
    assert_eq!(
        corpus::c_like_enum_dispatch(corpus::DispatchMode::Xor, 0xFF, 0x0F),
        0xF0
    );
    passed_curated += 1;

    assert_eq!(
        corpus::option_u32_map_or(corpus::MaybeU32 { is_some: true, val: 30 }, 0, 12),
        42
    );
    assert_eq!(
        corpus::option_u32_map_or(corpus::MaybeU32 { is_some: false, val: 30 }, 99, 12),
        99
    );
    passed_curated += 1;

    assert_eq!(
        corpus::result_u16_unwrap_or(
            corpus::OutcomeU16 {
                is_ok: true,
                ok_val: 42,
                err_code: 7
            },
            100
        ),
        42
    );
    passed_curated += 1;

    // --- Category 3 (5/5): Branching & loop CFGs ---
    assert_eq!(corpus::match_four_way_tag(0, 20, 22), 42);
    assert_eq!(corpus::match_four_way_tag(1, 10, 22), 42);
    assert_eq!(corpus::match_four_way_tag(9, 0x10, 0x05), 0x10 ^ 0x05 ^ 0x55);
    passed_curated += 1;

    assert_eq!(corpus::short_circuit_guard_chain(1, 2, 3), 6);
    assert_eq!(corpus::short_circuit_guard_chain(0, 5, 9), 9);
    passed_curated += 1;

    assert_eq!(corpus::while_loop_accumulate(4, 3), 18);
    passed_curated += 1;

    assert_eq!(corpus::early_return_search_4(10, 20, 30, 40, 30), 2);
    assert_eq!(corpus::early_return_search_4(10, 20, 30, 40, 99), -1);
    passed_curated += 1;

    assert_eq!(corpus::nested_if_else_matrix(1, 3, 22), 42);
    passed_curated += 1;

    // --- Category 4 (5/5): Single & multi-step external calls (`MirCallE`) ---
    let (res_c4_1, trace_c4_1) = TraceRecorder::observe_root(
        "itree_diff_corpus::call_once_and_postprocess",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&5u32)],
        |_rec| corpus::call_once_and_postprocess(10, 5),
    );
    assert_eq!(res_c4_1.expect("normal return"), 42);
    assert_eq!(trace_c4_1.events.len(), 1);
    passed_curated += 1;

    let (res_c4_2, trace_c4_2) = TraceRecorder::observe_root(
        "itree_diff_corpus::call_twice_sequential",
        vec![value_as_raw_bytes(&2u32), value_as_raw_bytes(&1u32)],
        |_rec| corpus::call_twice_sequential(2, 1),
    );
    assert_eq!(
        res_c4_2.expect("normal return"),
        corpus::ext_transform_u32(corpus::ext_transform_u32(2) + 1)
    );
    assert_eq!(trace_c4_2.events.len(), 2);
    passed_curated += 1;

    assert_eq!(corpus::call_in_branch_arms(0, 10, 99), 37);
    assert_eq!(corpus::call_in_branch_arms(1, 10, 6), 40);
    passed_curated += 1;

    let (res_c4_4, trace_c4_4) = TraceRecorder::observe_root(
        "itree_diff_corpus::call_in_bounded_loop_3x",
        vec![value_as_raw_bytes(&1u32)],
        |_rec| corpus::call_in_bounded_loop_3x(1),
    );
    assert_eq!(res_c4_4.expect("normal return"), 118);
    assert_eq!(trace_c4_4.events.len(), 3);
    passed_curated += 1;

    assert_eq!(corpus::callee_panic_unwind_recovery(5, 10), 16);
    let (unwind_res, unwind_trace) = TraceRecorder::observe_root(
        "itree_diff_corpus::callee_panic_unwind_recovery",
        vec![value_as_raw_bytes(&0xDEADu32), value_as_raw_bytes(&10u32)],
        |_rec| corpus::callee_panic_unwind_recovery(0xDEAD, 10),
    );
    assert!(unwind_res.is_err(), "trigger == 0xDEAD must unwind cleanly");
    assert_eq!(
        unwind_trace.events,
        vec![RecordedEvent::ExtCallPanic {
            def_path: "itree_diff_corpus::ext_may_panic_u32".to_string(),
            raw_args: vec![value_as_raw_bytes(&0xDEADu32), value_as_raw_bytes(&10u32)],
        }]
    );
    assert_eq!(unwind_trace.outcome, RecordedOutcome::Panic);
    passed_curated += 1;

    // --- Category 5 (5/5): Metamorphic Inlining Duality (`inlinedCallees` vs `MirCallE`) ---
    {
        let (res_inlined, trace_inlined) = TraceRecorder::observe_root_with_inlined_callees(
            "itree_diff_corpus::pipeline_two_helpers",
            vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&7u32)],
            [
                "itree_diff_corpus::helper_add_const",
                "itree_diff_corpus::helper_xor_fold",
            ],
            |_rec| corpus::pipeline_two_helpers(10, 7),
        );
        let (res_ext, trace_ext) = TraceRecorder::observe_root(
            "itree_diff_corpus::pipeline_two_helpers",
            vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&7u32)],
            |_rec| corpus::pipeline_two_helpers(10, 7),
        );
        assert_eq!(res_inlined.unwrap(), res_ext.unwrap());
        assert_eq!(trace_inlined.outcome, trace_ext.outcome);
        assert_eq!(trace_inlined.events.len(), 0);
        assert_eq!(trace_ext.events.len(), 2);
        passed_curated += 1;
    }

    assert_eq!(
        corpus::diamond_helper_dag(14),
        corpus::helper_xor_fold(19, 23)
    );
    passed_curated += 1;

    assert_eq!(corpus::conditional_helper_dispatch(0, 20, 22), 42);
    assert_eq!(
        corpus::conditional_helper_dispatch(1, 20, 22),
        corpus::helper_xor_fold(20, 22)
    );
    passed_curated += 1;

    assert_eq!(corpus::stateful_counter_pair(3, 2), 26);
    passed_curated += 1;

    assert_eq!(corpus::recursive_depth_2_unroll(2, 10), 22);
    passed_curated += 1;

    // --- Category 6 (5/5): References, pointers & ShadowProvenanceTable metadata ---
    let watched_val = 30u32;
    assert_eq!(corpus::ref_u32_passthrough(&watched_val, 12), 42);
    passed_curated += 1;

    let other_val = 99u32;
    assert_eq!(
        corpus::pair_of_refs_select(true, &watched_val, &other_val),
        30
    );
    assert_eq!(
        corpus::pair_of_refs_select(false, &watched_val, &other_val),
        99
    );
    passed_curated += 1;

    assert_eq!(corpus::struct_field_ref_project(&padded_hdr), 39);
    passed_curated += 1;

    assert_eq!(
        corpus::raw_const_ptr_identity(core::ptr::null(), 41),
        core::ptr::null()
    );
    assert_eq!(
        corpus::raw_const_ptr_identity(&raw const watched_val, 41),
        &raw const watched_val
    );
    passed_curated += 1;

    assert_eq!(corpus::slice_len_and_ptr_meta(&watched_val, 12), 42);
    passed_curated += 1;

    assert_eq!(
        passed_curated, 30,
        "all 30/30 curated M1 functions must pass (100%)"
    );

    // --- Milestone 2 Harvested Functions (45/45 across Family A, B, C) ---
    let mut passed_harvested = 0usize;
    assert_eq!(harvested::miropt_copy_prop_chain(10, 5), 15 ^ 10);
    passed_harvested += 1;
    assert_eq!(harvested::miropt_diamond_phi_merge(true, 13, 0), 42);
    passed_harvested += 1;
    assert_eq!(harvested::miropt_switch_dense_u8(2, 22), 42);
    passed_harvested += 1;
    assert_eq!(
        harvested::miropt_switch_sparse_u32(0x414E_4E4C, 0xFFFF_002A),
        42
    );
    passed_harvested += 1;
    assert_eq!(harvested::miropt_nested_tuple_swap(10, 52, true), 42);
    passed_harvested += 1;
    assert_eq!(harvested::miropt_checked_add_fallback(u32::MAX, 1, 42), 42);
    passed_harvested += 1;
    assert_eq!(harvested::miropt_checked_sub_clamp_zero(5, 10), 0);
    passed_harvested += 1;
    assert_eq!(
        harvested::miropt_bool_to_int_weighted(false, true, true, 7),
        42
    );
    passed_harvested += 1;
    assert_eq!(harvested::miropt_array_index_const_4(11, 22, 42, 44, 2), 42);
    passed_harvested += 1;
    assert_eq!(harvested::miropt_loop_break_threshold(10, 8, 25), 26);
    passed_harvested += 1;
    assert_eq!(harvested::miropt_loop_continue_filter(1, 0xFF), 9);
    passed_harvested += 1;
    assert_eq!(harvested::miropt_sign_extend_i8_to_i32(-8, 50), 42);
    passed_harvested += 1;
    assert_eq!(harvested::miropt_zero_extend_u16_to_u64(21, 1), 42);
    passed_harvested += 1;
    assert_eq!(harvested::miropt_truncate_u64_hi_lo((12u64 << 32) | 30), 42);
    passed_harvested += 1;
    assert_eq!(harvested::miropt_double_match_state(0, 1, 32), 42);
    passed_harvested += 1;

    assert_eq!(harvested::zc_pack_le_u32(0x2A, 0, 0, 0), 42);
    passed_harvested += 1;
    assert_eq!(harvested::zc_pack_be_u32(0, 0, 0, 0x2A), 42);
    passed_harvested += 1;
    assert_eq!(harvested::zc_bswap_u32_manual(0x1234_5678), 0x7856_3412);
    passed_harvested += 1;
    assert_eq!(harvested::zc_bswap_u16_pair(0x0102, 0x0304), 0x0201_0403);
    passed_harvested += 1;
    assert_eq!(harvested::zc_align_up_pow2(35, 3), 40);
    passed_harvested += 1;
    assert!(harvested::zc_is_aligned_check(64, 4));
    passed_harvested += 1;
    assert_eq!(harvested::zc_split_at_bounds_check(10, 4, 4), 16 ^ 24);
    passed_harvested += 1;
    assert_eq!(harvested::zc_prefix_suffix_remainder(42, 8), 2);
    passed_harvested += 1;
    assert_eq!(harvested::zc_u24_from_bytes(0x2A, 0x01, 0x00), 0x012A);
    passed_harvested += 1;
    assert_eq!(harvested::zc_validate_bool_byte(1), 1);
    assert_eq!(harvested::zc_validate_bool_byte(2), -1);
    passed_harvested += 1;
    assert!(harvested::zc_validate_char_scalar(0x41));
    assert!(!harvested::zc_validate_char_scalar(0xD800));
    passed_harvested += 1;
    assert_eq!(harvested::zc_nonzero_u32_extract(0, 42), 43);
    passed_harvested += 1;
    assert_eq!(harvested::zc_ipv4_header_ihl_bytes(0x45, 62), 42);
    passed_harvested += 1;
    assert_eq!(harvested::zc_tlv_record_advance(10, 100, 1, 29), 42);
    passed_harvested += 1;
    assert_eq!(harvested::zc_checksum_ones_complement_fold(0x0001_FFFE), 0);
    passed_harvested += 1;

    assert!(harvested::fxfs_extent_valid_range(4096, 12288, 4096));
    passed_harvested += 1;
    assert_eq!(harvested::fxfs_extent_overlap_len(10, 60, 18, 80), 42);
    passed_harvested += 1;
    assert_eq!(harvested::fxfs_round_up_block(4000, 12), 4096);
    passed_harvested += 1;
    assert_eq!(harvested::fxfs_round_down_block(5000, 12), 4096);
    passed_harvested += 1;
    assert_eq!(harvested::fxfs_block_count_for_bytes(8193, 12), 3);
    passed_harvested += 1;
    assert!(harvested::fxfs_journal_record_crc_check(10, 37));
    passed_harvested += 1;
    assert_eq!(harvested::fxfs_compaction_merge_keys(12, 20, 6), 42);
    passed_harvested += 1;
    assert_eq!(harvested::fxfs_lsm_layer_select(50, 20, 100), 1);
    passed_harvested += 1;
    assert_eq!(harvested::fxfs_alloc_bitmap_find_free_bit(0b0000_0111), 3);
    passed_harvested += 1;
    assert_eq!(harvested::fxfs_object_attr_version_cmp(2, 5, 2, 5), 0);
    passed_harvested += 1;
    assert_eq!(harvested::fxfs_refcount_saturating_adjust(50, -8), 42);
    passed_harvested += 1;
    assert_eq!(harvested::fxfs_superblock_magic_verify(0x4658_4653, 2, 16), 116);
    passed_harvested += 1;
    assert_eq!(harvested::fxfs_extent_split_offset(100, 42), (42, 58));
    passed_harvested += 1;
    assert_eq!(harvested::fxfs_txn_reservation_check(50, 5, 3), 42);
    passed_harvested += 1;
    assert_eq!(
        harvested::fxfs_two_phase_commit_seq(2, 1),
        corpus::ext_combine_u32(corpus::ext_transform_u32(2), 1)
    );
    passed_harvested += 1;

    assert_eq!(
        passed_harvested, 45,
        "all 45/45 M2 harvested functions must pass (100%)"
    );
}

/// Verifies that observed traces come directly from executing the corpus
/// functions (`#[anneal_trace::external]`), that mutating a corpus function body
/// alters its observed trace, and that distinct-trace counts vary across the
/// corpus when evaluated over a sweep of inputs.
#[test]
fn observed_traces_reflect_real_corpus_bodies_and_vary_across_corpus() {
    // 1. Changing the executed body changes the observed external-call trace:
    //    `call_once_and_postprocess(10, 5)` vs. a body that passes `x + 1` to
    //    `ext_transform_u32` or calls `ext_transform_u32` twice.
    let (_r_orig, trace_orig) = TraceRecorder::observe_root(
        "itree_diff_corpus::call_once_and_postprocess",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&5u32)],
        |_rec| corpus::call_once_and_postprocess(10, 5),
    );
    let (_r_mut_arg, trace_mut_arg) = TraceRecorder::observe_root(
        "itree_diff_corpus::call_once_and_postprocess",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&5u32)],
        |_rec| {
            // Mutated body: passes `x + 1` instead of `x` to `ext_transform_u32`.
            let raw = corpus::ext_transform_u32(10 + 1);
            raw + 5
        },
    );
    assert_ne!(
        trace_orig.events, trace_mut_arg.events,
        "mutating the argument passed to an external callee in the body must change the observed trace events"
    );
    assert_ne!(
        trace_orig.outcome, trace_mut_arg.outcome,
        "mutating the body computation must change the observed trace outcome"
    );

    // 2. Sweep inputs across multiple corpus functions and verify that distinct
    //    observed trace shapes (call sequence + outcome class) vary across functions.
    let inputs: &[(u32, u32, u32)] = &[
        (0, 0, 0),
        (0, 10, 20),
        (1, 10, 20),
        (2, 10, 20),
        (3, 10, 20),
        (0xDEAD, 10, 20),
    ];

    let count_distinct_shapes = |f: &dyn Fn(u32, u32, u32) -> cargo_anneal::RecordedRawTrace| -> usize {
        let mut shapes: BTreeSet<(Vec<(String, Vec<Vec<u8>>, bool)>, bool)> = BTreeSet::new();
        for &(a, b, c) in inputs {
            let tr = f(a, b, c);
            let ev_shape: Vec<(String, Vec<Vec<u8>>, bool)> = tr
                .events
                .iter()
                .filter_map(|ev| match ev {
                    RecordedEvent::ExtCall {
                        def_path, raw_args, ..
                    } => Some((def_path.clone(), raw_args.clone(), false)),
                    RecordedEvent::ExtCallPanic { def_path, raw_args } => {
                        Some((def_path.clone(), raw_args.clone(), true))
                    }
                    _ => None,
                })
                .collect();
            let is_panic = matches!(tr.outcome, RecordedOutcome::Panic);
            shapes.insert((ev_shape, is_panic));
        }
        shapes.len()
    };

    let distinct_pure = count_distinct_shapes(&|a, b, c| {
        TraceRecorder::observe_root(
            "itree_diff_corpus::clamp_u32_range",
            vec![
                value_as_raw_bytes(&a),
                value_as_raw_bytes(&b),
                value_as_raw_bytes(&c),
            ],
            |_rec| corpus::clamp_u32_range(a, b, c),
        )
        .1
    });
    let distinct_branch_calls = count_distinct_shapes(&|a, b, c| {
        TraceRecorder::observe_root(
            "itree_diff_corpus::call_in_branch_arms",
            vec![
                value_as_raw_bytes(&a),
                value_as_raw_bytes(&b),
                value_as_raw_bytes(&c),
            ],
            |_rec| corpus::call_in_branch_arms(a, b, c),
        )
        .1
    });
    let distinct_panic_calls = count_distinct_shapes(&|a, b, _c| {
        TraceRecorder::observe_root(
            "itree_diff_corpus::callee_panic_unwind_recovery",
            vec![value_as_raw_bytes(&a), value_as_raw_bytes(&b)],
            |_rec| corpus::callee_panic_unwind_recovery(a, b),
        )
        .1
    });

    assert_eq!(distinct_pure, 1, "pure scalar function has 1 empty-call shape");
    assert!(
        distinct_branch_calls >= 2,
        "call_in_branch_arms must produce at least 2 distinct external-call trace shapes"
    );
    assert!(
        distinct_panic_calls >= 3,
        "callee_panic_unwind_recovery must produce distinct normal and panicking call shapes, got {distinct_panic_calls}"
    );
    assert_ne!(distinct_pure, distinct_branch_calls);
    assert_ne!(distinct_branch_calls, distinct_panic_calls);
}

/// End-to-End Kernel & Fast-Eval Verification of `tests/itree-diff/corpus`:
/// Captures `itree_diff_corpus` via `anneal-rustc-capture`, scaffolds `.anneal/`,
/// executes the unmodified corpus functions natively under `TraceRecorder`,
/// generates `Proof/ItreeDiffBatchCheck.lean` covering representative functions
/// from all 6 categories plus negative controls (swapped root function and
/// mutated captured MIR), and verifies all theorems in the Lean 4 kernel!
#[test]
fn m1_and_m2_end_to_end_lean_kernel_and_fast_eval_itree_diff_verification() {
    let checkout_root = repo_root();
    let temp_dir = unique_temp_dir("itree_diff_e2e");
    let src_dir = temp_dir.join("src");
    fs::create_dir_all(&src_dir).expect("create src dir");

    let corpus_lib = fs::read_to_string(checkout_root.join("tests/itree-diff/corpus/src/lib.rs"))
        .expect("read corpus/src/lib.rs");
    let harvested_rs =
        fs::read_to_string(checkout_root.join("tests/itree-diff/corpus/src/harvested.rs"))
            .expect("read corpus/src/harvested.rs");
    let anneal_trace_dir = checkout_root.join("crates/anneal-trace");

    fs::write(
        temp_dir.join("Cargo.toml"),
        format!(
            r#"[package]
name = "itree_diff_corpus"
version = "0.1.0"
edition = "2021"

[lib]
path = "src/lib.rs"

[dependencies]
anneal-trace = {{ path = {:?} }}
"#,
            anneal_trace_dir.display()
        ),
    )
    .expect("write Cargo.toml");
    fs::write(src_dir.join("lib.rs"), &corpus_lib).expect("write src/lib.rs");
    fs::write(src_dir.join("harvested.rs"), harvested_rs).expect("write src/harvested.rs");

    let wrapper_bin = ensure_rustc_capture_bin();
    let units_dir = temp_dir.join("target").join("anneal").join("units");
    let mut capture_cfg = CaptureDriverConfig::new(&temp_dir);
    capture_cfg.units_dir = units_dir.clone();
    capture_cfg.rustc_wrapper = Some(wrapper_bin);
    let (_manifest, records) =
        run_cargo_capture(&capture_cfg).expect("capture MIR for 75-function itree_diff_corpus");
    assert!(
        !records.is_empty(),
        "expected captured MIR unit records for itree_diff_corpus"
    );

    let mut scaffold_cfg = ScaffoldConfig::new(&temp_dir);
    scaffold_cfg.units_dir = Some(units_dir);
    scaffold_cfg.anneal_repo_root = Some(checkout_root.clone());
    scaffold_cfg.init_spec_templates = false;
    scaffold_cfg.init_proof_templates = false;
    let scaffold_report = scaffold_workspace_with_config(&scaffold_cfg, &records)
        .expect("scaffold .anneal/ Lean project for itree_diff_corpus");
    assert!(
        scaffold_report.generated_mir_files.len() >= 75,
        "expected >= 75 generated MIR files (30 curated + 45 harvested + helpers), got {}",
        scaffold_report.generated_mir_files.len()
    );

    // Create a mutated copy of `Mir.ItreeDiffCorpus.call_once_and_postprocess`
    // (`Mir/ItreeDiffCorpus/call_once_mutated.lean`) where the postprocess
    // addition (`BinOp.add`) is replaced with bitwise XOR (`BinOp.bitXor`) so
    // we prove in the Lean kernel that mutating captured MIR causes
    // `diagnoseRawByteTraceObsErasedBounded` to report `"outcome_mismatch"`.
    let mir_dir = temp_dir
        .join(".anneal")
        .join("generated")
        .join("Mir")
        .join("ItreeDiffCorpus");
    let orig_call_once_mir = fs::read_to_string(mir_dir.join("call_once_and_postprocess.lean"))
        .expect("read Mir/ItreeDiffCorpus/call_once_and_postprocess.lean");
    let mutated_call_once_mir = orig_call_once_mir
        .replace(
            "namespace Mir.ItreeDiffCorpus.call_once_and_postprocess",
            "namespace Mir.ItreeDiffCorpus.call_once_mutated",
        )
        .replace(
            "end Mir.ItreeDiffCorpus.call_once_and_postprocess",
            "end Mir.ItreeDiffCorpus.call_once_mutated",
        )
        .replace(".add", ".sub");
    assert_ne!(
        orig_call_once_mir, mutated_call_once_mir,
        "mutated MIR module must differ from original"
    );
    fs::write(mir_dir.join("call_once_mutated.lean"), &mutated_call_once_mir)
        .expect("write Mir/ItreeDiffCorpus/call_once_mutated.lean");
    let lakefile_text = fs::read_to_string(&scaffold_report.lakefile_path)
        .expect("read .anneal/lakefile.toml")
        .replace(
            "\"Mir.ItreeDiffCorpus.call_once_and_postprocess\"",
            "\"Mir.ItreeDiffCorpus.call_once_and_postprocess\", \"Mir.ItreeDiffCorpus.call_once_mutated\"",
        );
    fs::write(&scaffold_report.lakefile_path, lakefile_text)
        .expect("update .anneal/lakefile.toml with call_once_mutated");

    // 1. Category 1: clamp_u32_range(5, 10, 20) -> 10
    let (_res1, trace_cat1) = TraceRecorder::observe_root(
        "itree_diff_corpus::clamp_u32_range",
        vec![
            value_as_raw_bytes(&5u32),
            value_as_raw_bytes(&10u32),
            value_as_raw_bytes(&20u32),
        ],
        |_rec| corpus::clamp_u32_range(5, 10, 20),
    );

    // 1b. Category 1: checked_affine_step(10, 4, 7) -> 47 (previously blocked by wrapping_mul/sub/add calls)
    let (_res1b, trace_cat1_affine) = TraceRecorder::observe_root(
        "itree_diff_corpus::checked_affine_step",
        vec![
            value_as_raw_bytes(&10u32),
            value_as_raw_bytes(&4u32),
            value_as_raw_bytes(&7u32),
        ],
        |_rec| corpus::checked_affine_step(10, 4, 7),
    );
    // 1c. Category 1: rotate_xor_mix(0x1234_5678, 0x00FF_00FF, 4) (previously blocked by wrapping_shl/shr calls)
    let (_res1c, trace_cat1_rotate) = TraceRecorder::observe_root(
        "itree_diff_corpus::rotate_xor_mix",
        vec![
            value_as_raw_bytes(&0x1234_5678u32),
            value_as_raw_bytes(&0x00FF_00FFu32),
            value_as_raw_bytes(&4u32),
        ],
        |_rec| corpus::rotate_xor_mix(0x1234_5678, 0x00FF_00FF, 4),
    );

    // 2. Category 2: repr_c_padded_header with poisoned [0xAA, 0xBB, 0xCC] padding
    let mut padded_hdr = corpus::PaddedHeader {
        tag: 1,
        len: 38,
    };
    let mut slot = core::mem::MaybeUninit::<corpus::PaddedHeader>::new(padded_hdr);
    unsafe {
        let base = slot.as_mut_ptr().cast::<u8>();
        *base.add(1) = 0xAA;
        *base.add(2) = 0xBB;
        *base.add(3) = 0xCC;
        padded_hdr = slot.assume_init();
    }
    let raw_padded_bytes = value_as_raw_bytes(&padded_hdr);
    let (_res2, trace_cat2) = TraceRecorder::observe_root(
        "itree_diff_corpus::repr_c_padded_header",
        vec![raw_padded_bytes, value_as_raw_bytes(&4u32)],
        |_rec| corpus::repr_c_padded_header(padded_hdr, 4),
    );

    // 3. Category 3: while_loop_accumulate(4, 3) -> 18 (real loop CFG)
    let (_res3, trace_cat3_loop) = TraceRecorder::observe_root(
        "itree_diff_corpus::while_loop_accumulate",
        vec![value_as_raw_bytes(&4u32), value_as_raw_bytes(&3u32)],
        |_rec| corpus::while_loop_accumulate(4, 3),
    );

    // 4. Category 4: call_once_and_postprocess(10, 5) -> 42 (observed directly via #[anneal_trace::external])
    let (_res4, trace_cat4) = TraceRecorder::observe_root(
        "itree_diff_corpus::call_once_and_postprocess",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&5u32)],
        |_rec| corpus::call_once_and_postprocess(10, 5),
    );
    assert_eq!(trace_cat4.events.len(), 1);

    // 5. Category 5A (Inlined mode): pipeline_two_helpers(10, 7) with helpers in `inlinedCallees`
    let (_res5a, trace_cat5_inlined) = TraceRecorder::observe_root_with_inlined_callees(
        "itree_diff_corpus::pipeline_two_helpers",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&7u32)],
        [
            "itree_diff_corpus::helper_add_const",
            "itree_diff_corpus::helper_xor_fold",
        ],
        |_rec| corpus::pipeline_two_helpers(10, 7),
    );
    assert_eq!(trace_cat5_inlined.events.len(), 0);

    // 6. Category 5B (External MirCallE mode): pipeline_two_helpers(10, 7) with helpers observed at boundary
    let (_res5b, trace_cat5_ext) = TraceRecorder::observe_root(
        "itree_diff_corpus::pipeline_two_helpers",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&7u32)],
        |_rec| corpus::pipeline_two_helpers(10, 7),
    );
    assert_eq!(trace_cat5_ext.events.len(), 2);

    // 7. Category 6: raw_const_ptr_identity(&watched_box, 41) with ShadowProvenanceTable
    let watched_box = Box::new(777u32);
    let watched_ptr: *const u32 = &raw const *watched_box;
    let (_res6, trace_cat6) = TraceRecorder::observe_root(
        "itree_diff_corpus::raw_const_ptr_identity",
        vec![value_as_raw_bytes(&watched_ptr), value_as_raw_bytes(&41u32)],
        |rec| {
            rec.register_allocation(&*watched_box, 7, 7);
            corpus::raw_const_ptr_identity(watched_ptr, 41)
        },
    );

    let batch_cases = vec![
        BatchTraceEvalCase {
            case_ident: "cat1_clamp".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffBatchCheck".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.clamp_u32_range".to_string(),
                callee_sig_modules: vec![],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 32,
                check_branches: false,
            },
            trace: trace_cat1.clone(),
            expected_diag_tag: Some("ok".to_string()),
            tampered_outcome: Some(RecordedOutcome::Normal {
                raw_ret: vec![99, 0, 0, 0],
            }),
        },
        BatchTraceEvalCase {
            case_ident: "cat1_checked_affine".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffBatchCheck".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.checked_affine_step".to_string(),
                callee_sig_modules: vec![],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 40,
                check_branches: false,
            },
            trace: trace_cat1_affine,
            expected_diag_tag: Some("ok".to_string()),
            tampered_outcome: None,
        },
        BatchTraceEvalCase {
            case_ident: "cat2_padded_header".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffBatchCheck".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.repr_c_padded_header".to_string(),
                callee_sig_modules: vec![],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 32,
                check_branches: false,
            },
            trace: trace_cat2,
            expected_diag_tag: Some("ok".to_string()),
            tampered_outcome: None,
        },
        BatchTraceEvalCase {
            case_ident: "cat3_while_loop".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffBatchCheck".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.while_loop_accumulate".to_string(),
                callee_sig_modules: vec![],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 120,
                check_branches: false,
            },
            trace: trace_cat3_loop,
            expected_diag_tag: Some("ok".to_string()),
            tampered_outcome: None,
        },
        BatchTraceEvalCase {
            case_ident: "cat4_call_once".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffBatchCheck".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.call_once_and_postprocess".to_string(),
                callee_sig_modules: vec!["Mir.ItreeDiffCorpus.ext_transform_u32".to_string()],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 40,
                check_branches: false,
            },
            trace: trace_cat4.clone(),
            expected_diag_tag: Some("ok".to_string()),
            tampered_outcome: None,
        },
        // Negative control A (Acceptance Criterion 3): checking `trace_cat4`
        // (`call_once_and_postprocess`) against mutated MIR (`call_once_mutated`)
        // reports `"outcome_mismatch"` (`!= "ok"`).
        BatchTraceEvalCase {
            case_ident: "neg_mutated_mir_diverges".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffBatchCheck".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.call_once_mutated".to_string(),
                callee_sig_modules: vec!["Mir.ItreeDiffCorpus.ext_transform_u32".to_string()],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 40,
                check_branches: false,
            },
            trace: trace_cat4.clone(),
            expected_diag_tag: Some("outcome_mismatch".to_string()),
            tampered_outcome: None,
        },
        // Negative control B (Acceptance Criterion 3): swapping the root function
        // (checking `trace_cat4` from `call_once_and_postprocess` against
        // `Mir.ItreeDiffCorpus.call_twice_sequential`) reports `"unexpected_ext_call"`
        // (`!= "ok"`).
        BatchTraceEvalCase {
            case_ident: "neg_swapped_root_fn_diverges".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffBatchCheck".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.call_twice_sequential".to_string(),
                callee_sig_modules: vec!["Mir.ItreeDiffCorpus.ext_transform_u32".to_string()],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 40,
                check_branches: false,
            },
            trace: trace_cat4,
            expected_diag_tag: Some("unexpected_ext_call".to_string()),
            tampered_outcome: None,
        },
        BatchTraceEvalCase {
            case_ident: "cat5_pipeline_inlined".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffBatchCheck".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.pipeline_two_helpers".to_string(),
                callee_sig_modules: vec![],
                inlined_callee_modules: vec![
                    "Mir.ItreeDiffCorpus.helper_add_const".to_string(),
                    "Mir.ItreeDiffCorpus.helper_xor_fold".to_string(),
                ],
                init_mem_expr: None,
                fuel: 60,
                check_branches: false,
            },
            trace: trace_cat5_inlined,
            expected_diag_tag: Some("ok".to_string()),
            tampered_outcome: None,
        },
        BatchTraceEvalCase {
            case_ident: "cat5_pipeline_ext".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffBatchCheck".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.pipeline_two_helpers".to_string(),
                callee_sig_modules: vec![
                    "Mir.ItreeDiffCorpus.helper_add_const".to_string(),
                    "Mir.ItreeDiffCorpus.helper_xor_fold".to_string(),
                ],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 40,
                check_branches: false,
            },
            trace: trace_cat5_ext,
            expected_diag_tag: Some("ok".to_string()),
            tampered_outcome: None,
        },
        BatchTraceEvalCase {
            case_ident: "cat6_ptr_identity".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffBatchCheck".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.raw_const_ptr_identity".to_string(),
                callee_sig_modules: vec![],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 16,
                check_branches: false,
            },
            trace: trace_cat6,
            expected_diag_tag: Some("ok".to_string()),
            tampered_outcome: None,
        },
    ];

    let batch_lean = render_batch_trace_eval_lean_module(
        "Proof.ItreeDiffBatchCheck",
        &batch_cases,
        false,
    );

    let proof_file = temp_dir
        .join(".anneal")
        .join("generated")
        .join("Verify")
        .join("ItreeDiffCorpus")
        .join("ItreeDiffBatchCheck.lean");
    fs::create_dir_all(proof_file.parent().unwrap()).expect("create Verify/ItreeDiffCorpus dir");
    fs::write(&proof_file, &batch_lean).expect("write ItreeDiffBatchCheck.lean");

    let anneal_dir = temp_dir.join(".anneal");
    let lake_targets: Vec<String> = [
        "Anneal",
        "Mir.ItreeDiffCorpus.clamp_u32_range",
        "Mir.ItreeDiffCorpus.checked_affine_step",
        "Mir.ItreeDiffCorpus.rotate_xor_mix",
        "Mir.ItreeDiffCorpus.repr_c_padded_header",
        "Mir.ItreeDiffCorpus.while_loop_accumulate",
        "Mir.ItreeDiffCorpus.call_once_and_postprocess",
        "Mir.ItreeDiffCorpus.call_once_mutated",
        "Mir.ItreeDiffCorpus.call_twice_sequential",
        "Mir.ItreeDiffCorpus.ext_transform_u32",
        "Mir.ItreeDiffCorpus.pipeline_two_helpers",
        "Mir.ItreeDiffCorpus.helper_add_const",
        "Mir.ItreeDiffCorpus.helper_xor_fold",
        "Mir.ItreeDiffCorpus.raw_const_ptr_identity",
    ]
    .iter()
    .map(|s| (*s).to_string())
    .collect();
    run_lake_verify_targets(&anneal_dir, &lake_targets).expect("run lake build in .anneal");

    let lean_out = Command::new("lake")
        .args(["env", "lean", "-M", "2048"])
        .arg(&proof_file)
        .current_dir(&anneal_dir)
        .output()
        .expect("run lake env lean on ItreeDiffBatchCheck.lean");
    assert!(
        lean_out.status.success(),
        "ItreeDiffBatchCheck.lean failed kernel check:\nstdout:\n{}\nstderr:\n{}\nmodule:\n{}",
        String::from_utf8_lossy(&lean_out.stdout),
        String::from_utf8_lossy(&lean_out.stderr),
        batch_lean
    );

    // Also verify `rotate_xor_mix` via fast `#eval` probe (`render_batch_trace_probe_lean_module`).
    let rotate_probe_cases = vec![BatchTraceEvalCase {
        case_ident: "cat1_rotate_xor".to_string(),
        config: TraceCheckModuleConfig {
            module_namespace: "Proof.ItreeDiffRotateProbe".to_string(),
            root_mir_module: "Mir.ItreeDiffCorpus.rotate_xor_mix".to_string(),
            callee_sig_modules: vec![],
            inlined_callee_modules: vec![],
            init_mem_expr: None,
            fuel: 40,
            check_branches: false,
        },
        trace: trace_cat1_rotate,
        expected_diag_tag: Some("ok".to_string()),
        tampered_outcome: None,
    }];
    let rotate_probe_lean =
        render_batch_trace_probe_lean_module("Proof.ItreeDiffRotateProbe", &rotate_probe_cases);
    let rotate_probe_file = temp_dir
        .join(".anneal")
        .join("generated")
        .join("Verify")
        .join("ItreeDiffCorpus")
        .join("ItreeDiffRotateProbe.lean");
    fs::write(&rotate_probe_file, &rotate_probe_lean).expect("write ItreeDiffRotateProbe.lean");
    let probe_out = Command::new("lake")
        .args(["env", "lean", "-M", "2048"])
        .arg(&rotate_probe_file)
        .current_dir(&anneal_dir)
        .output()
        .expect("run lake env lean on ItreeDiffRotateProbe.lean");
    assert!(
        probe_out.status.success(),
        "ItreeDiffRotateProbe.lean failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&probe_out.stdout),
        String::from_utf8_lossy(&probe_out.stderr)
    );
    let parsed_probes =
        parse_batch_trace_probe_output(&String::from_utf8_lossy(&probe_out.stdout));
    assert_eq!(parsed_probes.len(), 1);
    assert_eq!(
        parsed_probes.get("cat1_rotate_xor").map(|(tag, _)| tag.as_str()),
        Some("ok")
    );

    let _ = fs::remove_dir_all(&temp_dir);
}
