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

#![allow(unexpected_cfgs)]

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use cargo_anneal::{
    BatchTraceEvalCase, CaptureDriverConfig, RecordedEvent, RecordedOutcome, RecordedRawTrace,
    ScaffoldConfig, TraceCheckModuleConfig, TraceRecorder, capture_value_bytes,
    decode_recorded_raw_trace_hex, parse_batch_trace_probe_output,
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

fn ensure_mir_instrument_bin() -> PathBuf {
    let root = repo_root();
    let bin_path = root.join("target/debug/anneal-mir-instrument");
    let lib_src = root.join("crates/anneal-mir-instrument/src/lib.rs");
    let main_src = root.join("crates/anneal-mir-instrument/src/main.rs");
    let bin_mtime = fs::metadata(&bin_path).and_then(|m| m.modified()).ok();
    let lib_mtime = fs::metadata(&lib_src).and_then(|m| m.modified()).ok();
    let main_mtime = fs::metadata(&main_src).and_then(|m| m.modified()).ok();
    if bin_path.is_file()
        && let (Some(bm), Some(lm), Some(mm)) = (bin_mtime, lib_mtime, main_mtime)
        && bm >= lm
        && bm >= mm
    {
        return bin_path;
    }
    let status = Command::new("cargo")
        .args(["build", "-p", "anneal-mir-instrument", "--locked"])
        .current_dir(&root)
        .status()
        .expect("build anneal-mir-instrument");
    assert!(status.success(), "building anneal-mir-instrument failed");
    bin_path
}

fn build_anneal_trace_proc_macro_dylib(staging_dir: &Path) -> PathBuf {
    let root = repo_root();
    let ext = if cfg!(target_os = "macos") {
        "dylib"
    } else {
        "so"
    };
    let src_path = root.join("crates/anneal-trace/src/lib.rs");
    let out_path = staging_dir.join(format!("libanneal_trace.{ext}"));
    let out = Command::new("rustc")
        .args([
            "--edition=2024",
            "--crate-type=proc-macro",
            "--crate-name=anneal_trace",
            "-A",
            "warnings",
        ])
        .arg(&src_path)
        .arg("-o")
        .arg(&out_path)
        .output()
        .expect("compile anneal_trace proc-macro");
    assert!(
        out.status.success(),
        "failed to compile anneal_trace proc-macro:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    out_path
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

fn render_corpus_binary_trace_collector(repo_root: &Path) -> String {
    let trace_observer_path = repo_root.join("crates/cargo-anneal/src/trace_observer.rs");
    format!(
        r#"#![allow(dead_code, non_snake_case, non_camel_case_types, unused_imports, unexpected_cfgs)]
extern crate self as cargo_anneal;
#[path = {trace_observer_path:?}]
pub mod trace_observer;
#[path = "src/lib.rs"]
pub mod itree_diff_corpus;

use itree_diff_corpus as corpus;
use itree_diff_corpus::harvested;
use trace_observer::{{
    EnvSchedule, RecordedRawTrace, TraceRecorder, encode_recorded_raw_trace_hex,
    value_as_raw_bytes,
}};

fn emit(id: &str, trace: &RecordedRawTrace) {{
    println!("ANNEAL_CORPUS_TRACE:{{id}}:{{}}", encode_recorded_raw_trace_hex(trace));
}}

fn main() {{
    // --- Category 1 (5/5) ---
    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::clamp_u32_range",
        vec![value_as_raw_bytes(&5u32), value_as_raw_bytes(&10u32), value_as_raw_bytes(&20u32)],
        |_| corpus::clamp_u32_range(5, 10, 20),
    );
    emit("cat1_clamp_lo", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::clamp_u32_range",
        vec![value_as_raw_bytes(&15u32), value_as_raw_bytes(&10u32), value_as_raw_bytes(&20u32)],
        |_| corpus::clamp_u32_range(15, 10, 20),
    );
    emit("cat1_clamp_mid", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::rotate_xor_mix",
        vec![value_as_raw_bytes(&0x1234_5678u32), value_as_raw_bytes(&0x00FF_00FFu32), value_as_raw_bytes(&4u32)],
        |_| corpus::rotate_xor_mix(0x1234_5678, 0x00FF_00FF, 4),
    );
    emit("cat1_rotate_xor_mix", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::checked_affine_step",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&4u32), value_as_raw_bytes(&7u32)],
        |_| corpus::checked_affine_step(10, 4, 7),
    );
    emit("cat1_checked_affine_step", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::signed_abs_diff",
        vec![value_as_raw_bytes(&(-10i32)), value_as_raw_bytes(&25i32)],
        |_| corpus::signed_abs_diff(-10, 25),
    );
    emit("cat1_signed_abs_diff", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::bitfield_extract",
        vec![value_as_raw_bytes(&0xABCD_EF01u32), value_as_raw_bytes(&8u32), value_as_raw_bytes(&0xFFu32)],
        |_| corpus::bitfield_extract(0xABCD_EF01, 8, 0xFF),
    );
    emit("cat1_bitfield_extract", &tr);

    // --- Category 2 (5/5) ---
    let mut padded_hdr = corpus::PaddedHeader {{ tag: 1, len: 38 }};
    let mut slot = core::mem::MaybeUninit::<corpus::PaddedHeader>::new(padded_hdr);
    unsafe {{
        let base = slot.as_mut_ptr().cast::<u8>();
        *base.add(1) = 0xAA;
        *base.add(2) = 0xBB;
        *base.add(3) = 0xCC;
        padded_hdr = slot.assume_init();
    }}
    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::repr_c_padded_header",
        vec![value_as_raw_bytes(&padded_hdr), value_as_raw_bytes(&4u32)],
        |_| corpus::repr_c_padded_header(padded_hdr, 4),
    );
    emit("cat2_repr_c_padded_header", &tr);

    let pair = corpus::NestedPair {{ flag: 1, left: 7, right: 8 }};
    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::nested_tuple_struct_sum",
        vec![value_as_raw_bytes(&pair), value_as_raw_bytes(&3u32)],
        |_| corpus::nested_tuple_struct_sum(pair, 3),
    );
    emit("cat2_nested_tuple_struct_sum", &tr);

    let mode = corpus::DispatchMode::Sub;
    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::c_like_enum_dispatch",
        vec![value_as_raw_bytes(&mode), value_as_raw_bytes(&10u32), value_as_raw_bytes(&52u32)],
        |_| corpus::c_like_enum_dispatch(mode, 10, 52),
    );
    emit("cat2_c_like_enum_dispatch", &tr);

    let opt = corpus::MaybeU32 {{ is_some: true, val: 30 }};
    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::option_u32_map_or",
        vec![value_as_raw_bytes(&opt), value_as_raw_bytes(&0u32), value_as_raw_bytes(&12u32)],
        |_| corpus::option_u32_map_or(opt, 0, 12),
    );
    emit("cat2_option_u32_map_or", &tr);

    let out_u16 = corpus::OutcomeU16 {{ is_ok: false, ok_val: 0, err_code: 12 }};
    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::result_u16_unwrap_or",
        vec![value_as_raw_bytes(&out_u16), value_as_raw_bytes(&30u16)],
        |_| corpus::result_u16_unwrap_or(out_u16, 30),
    );
    emit("cat2_result_u16_unwrap_or", &tr);

    // --- Category 3 (5/5) ---
    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::match_four_way_tag",
        vec![value_as_raw_bytes(&2u32), value_as_raw_bytes(&50u32), value_as_raw_bytes(&8u32)],
        |_| corpus::match_four_way_tag(2, 50, 8),
    );
    emit("cat3_match_four_way_tag", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::short_circuit_guard_chain",
        vec![value_as_raw_bytes(&1u32), value_as_raw_bytes(&2u32), value_as_raw_bytes(&3u32)],
        |_| corpus::short_circuit_guard_chain(1, 2, 3),
    );
    emit("cat3_short_circuit_guard_chain", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::while_loop_accumulate",
        vec![value_as_raw_bytes(&4u32), value_as_raw_bytes(&3u32)],
        |_| corpus::while_loop_accumulate(4, 3),
    );
    emit("cat3_while_loop_accumulate", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::early_return_search_4",
        vec![
            value_as_raw_bytes(&10u32),
            value_as_raw_bytes(&20u32),
            value_as_raw_bytes(&30u32),
            value_as_raw_bytes(&40u32),
            value_as_raw_bytes(&30u32),
        ],
        |_| corpus::early_return_search_4(10, 20, 30, 40, 30),
    );
    emit("cat3_early_return_search_4", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::nested_if_else_matrix",
        vec![value_as_raw_bytes(&1u32), value_as_raw_bytes(&3u32), value_as_raw_bytes(&22u32)],
        |_| corpus::nested_if_else_matrix(1, 3, 22),
    );
    emit("cat3_nested_if_else_matrix", &tr);

    // --- Category 4 (5/5 + scheduled ReturnBytes and PanicOnCall) ---
    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::call_once_and_postprocess",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&5u32)],
        |_| corpus::call_once_and_postprocess(10, 5),
    );
    emit("cat4_call_once_and_postprocess", &tr);

    let mut sched = EnvSchedule::new();
    sched.push_callee_response(
        "itree_diff_corpus::ext_transform_u32",
        value_as_raw_bytes(&100u32),
    );
    let (sched_ret_res, tr, _) = TraceRecorder::observe_root_with_recorder(
        TraceRecorder::with_schedule(sched),
        "itree_diff_corpus::call_once_and_postprocess",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&5u32)],
        |_| corpus::call_once_and_postprocess(10, 5),
    );
    assert_eq!(sched_ret_res.expect("scheduled return"), 105);
    emit("cat4_call_once_scheduled_return", &tr);

    let (sched_panic_res, tr, _) = TraceRecorder::observe_root_with_recorder(
        TraceRecorder::with_schedule(EnvSchedule::new().with_panic_on_call(0)),
        "itree_diff_corpus::call_once_and_postprocess",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&5u32)],
        |_| corpus::call_once_and_postprocess(10, 5),
    );
    assert!(sched_panic_res.is_err());
    emit("cat4_call_once_scheduled_panic", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::call_twice_sequential",
        vec![value_as_raw_bytes(&2u32), value_as_raw_bytes(&1u32)],
        |_| corpus::call_twice_sequential(2, 1),
    );
    emit("cat4_call_twice_sequential", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::call_in_branch_arms",
        vec![value_as_raw_bytes(&1u32), value_as_raw_bytes(&10u32), value_as_raw_bytes(&6u32)],
        |_| corpus::call_in_branch_arms(1, 10, 6),
    );
    emit("cat4_call_in_branch_arms", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::call_in_bounded_loop_3x",
        vec![value_as_raw_bytes(&1u32)],
        |_| corpus::call_in_bounded_loop_3x(1),
    );
    emit("cat4_call_in_bounded_loop_3x", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::callee_panic_unwind_recovery",
        vec![value_as_raw_bytes(&5u32), value_as_raw_bytes(&10u32)],
        |_| corpus::callee_panic_unwind_recovery(5, 10),
    );
    emit("cat4_callee_panic_normal", &tr);

    let (panic_res, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::callee_panic_unwind_recovery",
        vec![value_as_raw_bytes(&0xDEADu32), value_as_raw_bytes(&10u32)],
        |_| corpus::callee_panic_unwind_recovery(0xDEAD, 10),
    );
    assert!(panic_res.is_err());
    emit("cat4_callee_panic_unwind", &tr);

    // --- Category 5 (5/5 in both inlined and external modes) ---
    let (_, tr) = TraceRecorder::observe_root_with_inlined_callees(
        "itree_diff_corpus::pipeline_two_helpers",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&7u32)],
        ["itree_diff_corpus::helper_add_const", "itree_diff_corpus::helper_xor_fold"],
        |_| corpus::pipeline_two_helpers(10, 7),
    );
    emit("cat5_pipeline_two_helpers_inlined", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::pipeline_two_helpers",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&7u32)],
        |_| corpus::pipeline_two_helpers(10, 7),
    );
    emit("cat5_pipeline_two_helpers_ext", &tr);

    let (_, tr) = TraceRecorder::observe_root_with_inlined_callees(
        "itree_diff_corpus::diamond_helper_dag",
        vec![value_as_raw_bytes(&14u32)],
        ["itree_diff_corpus::helper_add_const", "itree_diff_corpus::helper_xor_fold"],
        |_| corpus::diamond_helper_dag(14),
    );
    emit("cat5_diamond_helper_dag_inlined", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::diamond_helper_dag",
        vec![value_as_raw_bytes(&14u32)],
        |_| corpus::diamond_helper_dag(14),
    );
    emit("cat5_diamond_helper_dag_ext", &tr);

    let (_, tr) = TraceRecorder::observe_root_with_inlined_callees(
        "itree_diff_corpus::conditional_helper_dispatch",
        vec![value_as_raw_bytes(&1u32), value_as_raw_bytes(&20u32), value_as_raw_bytes(&22u32)],
        ["itree_diff_corpus::helper_add_const", "itree_diff_corpus::helper_xor_fold"],
        |_| corpus::conditional_helper_dispatch(1, 20, 22),
    );
    emit("cat5_conditional_helper_dispatch_inlined", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::conditional_helper_dispatch",
        vec![value_as_raw_bytes(&1u32), value_as_raw_bytes(&20u32), value_as_raw_bytes(&22u32)],
        |_| corpus::conditional_helper_dispatch(1, 20, 22),
    );
    emit("cat5_conditional_helper_dispatch_ext", &tr);

    let (_, tr) = TraceRecorder::observe_root_with_inlined_callees(
        "itree_diff_corpus::stateful_counter_pair",
        vec![value_as_raw_bytes(&3u32), value_as_raw_bytes(&2u32)],
        ["itree_diff_corpus::helper_step_counter"],
        |_| corpus::stateful_counter_pair(3, 2),
    );
    emit("cat5_stateful_counter_pair_inlined", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::stateful_counter_pair",
        vec![value_as_raw_bytes(&3u32), value_as_raw_bytes(&2u32)],
        |_| corpus::stateful_counter_pair(3, 2),
    );
    emit("cat5_stateful_counter_pair_ext", &tr);

    let (_, tr) = TraceRecorder::observe_root_with_inlined_callees(
        "itree_diff_corpus::recursive_depth_2_unroll",
        vec![value_as_raw_bytes(&2u32), value_as_raw_bytes(&10u32)],
        ["itree_diff_corpus::helper_depth_step"],
        |_| corpus::recursive_depth_2_unroll(2, 10),
    );
    emit("cat5_recursive_depth_2_unroll_inlined", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::recursive_depth_2_unroll",
        vec![value_as_raw_bytes(&2u32), value_as_raw_bytes(&10u32)],
        |_| corpus::recursive_depth_2_unroll(2, 10),
    );
    emit("cat5_recursive_depth_2_unroll_ext", &tr);

    // --- Category 6 (5/5) ---
    let watched_val = Box::new(30u32);
    let other_val = Box::new(99u32);
    let watched_ref: &u32 = &watched_val;
    let other_ref: &u32 = &other_val;

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::ref_u32_passthrough",
        vec![value_as_raw_bytes(&watched_ref), value_as_raw_bytes(&12u32)],
        |rec| {{
            rec.register_allocation(watched_ref, 7, 7);
            corpus::ref_u32_passthrough(watched_ref, 12)
        }},
    );
    emit("cat6_ref_u32_passthrough", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::pair_of_refs_select",
        vec![value_as_raw_bytes(&false), value_as_raw_bytes(&watched_ref), value_as_raw_bytes(&other_ref)],
        |rec| {{
            rec.register_allocation(watched_ref, 7, 7);
            rec.register_allocation(other_ref, 8, 8);
            corpus::pair_of_refs_select(false, watched_ref, other_ref)
        }},
    );
    emit("cat6_pair_of_refs_select", &tr);

    let hdr_box = Box::new(padded_hdr);
    let hdr_ref: &corpus::PaddedHeader = &hdr_box;
    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::struct_field_ref_project",
        vec![value_as_raw_bytes(&hdr_ref)],
        |rec| {{
            rec.register_allocation(hdr_ref, 7, 7);
            corpus::struct_field_ref_project(hdr_ref)
        }},
    );
    emit("cat6_struct_field_ref_project", &tr);

    let watched_ptr: *const u32 = &raw const *watched_val;
    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::raw_const_ptr_identity",
        vec![value_as_raw_bytes(&watched_ptr), value_as_raw_bytes(&41u32)],
        |rec| {{
            rec.register_allocation(&*watched_val, 7, 7);
            corpus::raw_const_ptr_identity(watched_ptr, 41)
        }},
    );
    emit("cat6_raw_const_ptr_identity", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::slice_len_and_ptr_meta",
        vec![value_as_raw_bytes(&watched_ref), value_as_raw_bytes(&12usize)],
        |rec| {{
            rec.register_allocation(watched_ref, 7, 7);
            corpus::slice_len_and_ptr_meta(watched_ref, 12)
        }},
    );
    emit("cat6_slice_len_and_ptr_meta", &tr);

    // --- Harvested Family A (15/15) ---
    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_copy_prop_chain",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&5u32)],
        |_| harvested::miropt_copy_prop_chain(10, 5),
    );
    emit("h_miropt_copy_prop_chain", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_diamond_phi_merge",
        vec![value_as_raw_bytes(&true), value_as_raw_bytes(&13u32), value_as_raw_bytes(&0u32)],
        |_| harvested::miropt_diamond_phi_merge(true, 13, 0),
    );
    emit("h_miropt_diamond_phi_merge", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_switch_dense_u8",
        vec![value_as_raw_bytes(&2u8), value_as_raw_bytes(&22u32)],
        |_| harvested::miropt_switch_dense_u8(2, 22),
    );
    emit("h_miropt_switch_dense_u8", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_switch_sparse_u32",
        vec![value_as_raw_bytes(&0x414E_4E4Cu32), value_as_raw_bytes(&0xFFFF_002Au32)],
        |_| harvested::miropt_switch_sparse_u32(0x414E_4E4C, 0xFFFF_002A),
    );
    emit("h_miropt_switch_sparse_u32", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_nested_tuple_swap",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&52u32), value_as_raw_bytes(&true)],
        |_| harvested::miropt_nested_tuple_swap(10, 52, true),
    );
    emit("h_miropt_nested_tuple_swap", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_checked_add_fallback",
        vec![value_as_raw_bytes(&u32::MAX), value_as_raw_bytes(&1u32), value_as_raw_bytes(&42u32)],
        |_| harvested::miropt_checked_add_fallback(u32::MAX, 1, 42),
    );
    emit("h_miropt_checked_add_fallback", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_checked_sub_clamp_zero",
        vec![value_as_raw_bytes(&5u32), value_as_raw_bytes(&10u32)],
        |_| harvested::miropt_checked_sub_clamp_zero(5, 10),
    );
    emit("h_miropt_checked_sub_clamp_zero", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_bool_to_int_weighted",
        vec![value_as_raw_bytes(&false), value_as_raw_bytes(&true), value_as_raw_bytes(&true), value_as_raw_bytes(&7u32)],
        |_| harvested::miropt_bool_to_int_weighted(false, true, true, 7),
    );
    emit("h_miropt_bool_to_int_weighted", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_array_index_const_4",
        vec![
            value_as_raw_bytes(&11u32),
            value_as_raw_bytes(&22u32),
            value_as_raw_bytes(&42u32),
            value_as_raw_bytes(&44u32),
            value_as_raw_bytes(&2u32),
        ],
        |_| harvested::miropt_array_index_const_4(11, 22, 42, 44, 2),
    );
    emit("h_miropt_array_index_const_4", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_loop_break_threshold",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&8u32), value_as_raw_bytes(&25u32)],
        |_| harvested::miropt_loop_break_threshold(10, 8, 25),
    );
    emit("h_miropt_loop_break_threshold", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_loop_continue_filter",
        vec![value_as_raw_bytes(&1u32), value_as_raw_bytes(&0xFFu32)],
        |_| harvested::miropt_loop_continue_filter(1, 0xFF),
    );
    emit("h_miropt_loop_continue_filter", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_sign_extend_i8_to_i32",
        vec![value_as_raw_bytes(&(-8i8)), value_as_raw_bytes(&50i32)],
        |_| harvested::miropt_sign_extend_i8_to_i32(-8, 50),
    );
    emit("h_miropt_sign_extend_i8_to_i32", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_zero_extend_u16_to_u64",
        vec![value_as_raw_bytes(&21u16), value_as_raw_bytes(&1u32)],
        |_| harvested::miropt_zero_extend_u16_to_u64(21, 1),
    );
    emit("h_miropt_zero_extend_u16_to_u64", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_truncate_u64_hi_lo",
        vec![value_as_raw_bytes(&((12u64 << 32) | 30))],
        |_| harvested::miropt_truncate_u64_hi_lo((12u64 << 32) | 30),
    );
    emit("h_miropt_truncate_u64_hi_lo", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::miropt_double_match_state",
        vec![value_as_raw_bytes(&0u8), value_as_raw_bytes(&1u8), value_as_raw_bytes(&32u32)],
        |_| harvested::miropt_double_match_state(0, 1, 32),
    );
    emit("h_miropt_double_match_state", &tr);

    // --- Harvested Family B (15/15) ---
    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_pack_le_u32",
        vec![value_as_raw_bytes(&0x2Au8), value_as_raw_bytes(&0u8), value_as_raw_bytes(&0u8), value_as_raw_bytes(&0u8)],
        |_| harvested::zc_pack_le_u32(0x2A, 0, 0, 0),
    );
    emit("h_zc_pack_le_u32", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_pack_be_u32",
        vec![value_as_raw_bytes(&0u8), value_as_raw_bytes(&0u8), value_as_raw_bytes(&0u8), value_as_raw_bytes(&0x2Au8)],
        |_| harvested::zc_pack_be_u32(0, 0, 0, 0x2A),
    );
    emit("h_zc_pack_be_u32", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_bswap_u32_manual",
        vec![value_as_raw_bytes(&0x1234_5678u32)],
        |_| harvested::zc_bswap_u32_manual(0x1234_5678),
    );
    emit("h_zc_bswap_u32_manual", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_bswap_u16_pair",
        vec![value_as_raw_bytes(&0x0102u16), value_as_raw_bytes(&0x0304u16)],
        |_| harvested::zc_bswap_u16_pair(0x0102, 0x0304),
    );
    emit("h_zc_bswap_u16_pair", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_align_up_pow2",
        vec![value_as_raw_bytes(&35u32), value_as_raw_bytes(&3u32)],
        |_| harvested::zc_align_up_pow2(35, 3),
    );
    emit("h_zc_align_up_pow2", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_is_aligned_check",
        vec![value_as_raw_bytes(&64u32), value_as_raw_bytes(&4u32)],
        |_| harvested::zc_is_aligned_check(64, 4),
    );
    emit("h_zc_is_aligned_check", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_split_at_bounds_check",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&4u32), value_as_raw_bytes(&4u32)],
        |_| harvested::zc_split_at_bounds_check(10, 4, 4),
    );
    emit("h_zc_split_at_bounds_check", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_prefix_suffix_remainder",
        vec![value_as_raw_bytes(&42u32), value_as_raw_bytes(&8u32)],
        |_| harvested::zc_prefix_suffix_remainder(42, 8),
    );
    emit("h_zc_prefix_suffix_remainder", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_u24_from_bytes",
        vec![value_as_raw_bytes(&0x2Au8), value_as_raw_bytes(&0x01u8), value_as_raw_bytes(&0x00u8)],
        |_| harvested::zc_u24_from_bytes(0x2A, 0x01, 0x00),
    );
    emit("h_zc_u24_from_bytes", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_validate_bool_byte",
        vec![value_as_raw_bytes(&2u8)],
        |_| harvested::zc_validate_bool_byte(2),
    );
    emit("h_zc_validate_bool_byte", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_validate_char_scalar",
        vec![value_as_raw_bytes(&0x41u32)],
        |_| harvested::zc_validate_char_scalar(0x41),
    );
    emit("h_zc_validate_char_scalar", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_nonzero_u32_extract",
        vec![value_as_raw_bytes(&0u32), value_as_raw_bytes(&42u32)],
        |_| harvested::zc_nonzero_u32_extract(0, 42),
    );
    emit("h_zc_nonzero_u32_extract", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_ipv4_header_ihl_bytes",
        vec![value_as_raw_bytes(&0x45u8), value_as_raw_bytes(&62u16)],
        |_| harvested::zc_ipv4_header_ihl_bytes(0x45, 62),
    );
    emit("h_zc_ipv4_header_ihl_bytes", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_tlv_record_advance",
        vec![
            value_as_raw_bytes(&10u32),
            value_as_raw_bytes(&100u32),
            value_as_raw_bytes(&1u8),
            value_as_raw_bytes(&29u16),
        ],
        |_| harvested::zc_tlv_record_advance(10, 100, 1, 29),
    );
    emit("h_zc_tlv_record_advance", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::zc_checksum_ones_complement_fold",
        vec![value_as_raw_bytes(&0x0001_FFFEu32)],
        |_| harvested::zc_checksum_ones_complement_fold(0x0001_FFFE),
    );
    emit("h_zc_checksum_ones_complement_fold", &tr);

    // --- Harvested Family C (15/15) ---
    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_extent_valid_range",
        vec![value_as_raw_bytes(&4096u64), value_as_raw_bytes(&12288u64), value_as_raw_bytes(&4096u32)],
        |_| harvested::fxfs_extent_valid_range(4096, 12288, 4096),
    );
    emit("h_fxfs_extent_valid_range", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_extent_overlap_len",
        vec![
            value_as_raw_bytes(&10u32),
            value_as_raw_bytes(&60u32),
            value_as_raw_bytes(&18u32),
            value_as_raw_bytes(&80u32),
        ],
        |_| harvested::fxfs_extent_overlap_len(10, 60, 18, 80),
    );
    emit("h_fxfs_extent_overlap_len", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_round_up_block",
        vec![value_as_raw_bytes(&4000u32), value_as_raw_bytes(&12u32)],
        |_| harvested::fxfs_round_up_block(4000, 12),
    );
    emit("h_fxfs_round_up_block", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_round_down_block",
        vec![value_as_raw_bytes(&5000u32), value_as_raw_bytes(&12u32)],
        |_| harvested::fxfs_round_down_block(5000, 12),
    );
    emit("h_fxfs_round_down_block", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_block_count_for_bytes",
        vec![value_as_raw_bytes(&8193u32), value_as_raw_bytes(&12u32)],
        |_| harvested::fxfs_block_count_for_bytes(8193, 12),
    );
    emit("h_fxfs_block_count_for_bytes", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_journal_record_crc_check",
        vec![value_as_raw_bytes(&10u32), value_as_raw_bytes(&37u32)],
        |_| harvested::fxfs_journal_record_crc_check(10, 37),
    );
    emit("h_fxfs_journal_record_crc_check", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_compaction_merge_keys",
        vec![value_as_raw_bytes(&12u32), value_as_raw_bytes(&20u32), value_as_raw_bytes(&6u32)],
        |_| harvested::fxfs_compaction_merge_keys(12, 20, 6),
    );
    emit("h_fxfs_compaction_merge_keys", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_lsm_layer_select",
        vec![value_as_raw_bytes(&50u32), value_as_raw_bytes(&20u32), value_as_raw_bytes(&100u32)],
        |_| harvested::fxfs_lsm_layer_select(50, 20, 100),
    );
    emit("h_fxfs_lsm_layer_select", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_alloc_bitmap_find_free_bit",
        vec![value_as_raw_bytes(&0b0000_0111u32)],
        |_| harvested::fxfs_alloc_bitmap_find_free_bit(0b0000_0111),
    );
    emit("h_fxfs_alloc_bitmap_find_free_bit", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_object_attr_version_cmp",
        vec![
            value_as_raw_bytes(&2u32),
            value_as_raw_bytes(&5u16),
            value_as_raw_bytes(&2u32),
            value_as_raw_bytes(&5u16),
        ],
        |_| harvested::fxfs_object_attr_version_cmp(2, 5, 2, 5),
    );
    emit("h_fxfs_object_attr_version_cmp", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_refcount_saturating_adjust",
        vec![value_as_raw_bytes(&50u32), value_as_raw_bytes(&(-8i32))],
        |_| harvested::fxfs_refcount_saturating_adjust(50, -8),
    );
    emit("h_fxfs_refcount_saturating_adjust", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_superblock_magic_verify",
        vec![value_as_raw_bytes(&0x4658_4653u32), value_as_raw_bytes(&2u16), value_as_raw_bytes(&16u16)],
        |_| harvested::fxfs_superblock_magic_verify(0x4658_4653, 2, 16),
    );
    emit("h_fxfs_superblock_magic_verify", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_extent_split_offset",
        vec![value_as_raw_bytes(&100u32), value_as_raw_bytes(&42u32)],
        |_| harvested::fxfs_extent_split_offset(100, 42),
    );
    emit("h_fxfs_extent_split_offset", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_txn_reservation_check",
        vec![value_as_raw_bytes(&50u32), value_as_raw_bytes(&5u32), value_as_raw_bytes(&3u32)],
        |_| harvested::fxfs_txn_reservation_check(50, 5, 3),
    );
    emit("h_fxfs_txn_reservation_check", &tr);

    let (_, tr) = TraceRecorder::observe_root(
        "itree_diff_corpus::harvested::fxfs_two_phase_commit_seq",
        vec![value_as_raw_bytes(&2u32), value_as_raw_bytes(&1u32)],
        |_| harvested::fxfs_two_phase_commit_seq(2, 1),
    );
    emit("h_fxfs_two_phase_commit_seq", &tr);
}}
"#
    )
}

fn compile_and_run_corpus_collector(
    driver_bin: &Path,
    staging_dir: &Path,
    proc_macro_dylib: &Path,
    collector_rs: &Path,
    out_bin_name: &str,
    opt_level: &str,
    raw_mir_opts: bool,
) -> BTreeMap<String, RecordedRawTrace> {
    let bin_path = staging_dir.join(out_bin_name);
    let extern_arg = format!("anneal_trace={}", proc_macro_dylib.display());
    let opt_flag = format!("opt-level={opt_level}");
    let mut cmd = Command::new(driver_bin);
    cmd.args([
        "--edition=2024",
        "-A",
        "warnings",
        "-C",
        &opt_flag,
        "--extern",
        &extern_arg,
    ])
    .arg(collector_rs)
    .arg("-o")
    .arg(&bin_path)
    .current_dir(staging_dir);
    if raw_mir_opts {
        cmd.env("ANNEAL_MIR_INSTRUMENT_RAW_MIR_OPTS", "1");
    } else {
        cmd.env_remove("ANNEAL_MIR_INSTRUMENT_RAW_MIR_OPTS");
    }
    let compile_out = cmd
        .output()
        .expect("invoke anneal-mir-instrument on corpus collector");
    assert!(
        compile_out.status.success(),
        "anneal-mir-instrument ({out_bin_name}) failed:\n{}",
        String::from_utf8_lossy(&compile_out.stderr)
    );

    let run_out = Command::new(&bin_path)
        .current_dir(staging_dir)
        .output()
        .expect("run compiled corpus collector binary");
    assert!(
        run_out.status.success(),
        "{out_bin_name} failed at runtime:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&run_out.stdout),
        String::from_utf8_lossy(&run_out.stderr)
    );

    const PREFIX: &str = "ANNEAL_CORPUS_TRACE:";
    let mut map = BTreeMap::new();
    for line in String::from_utf8_lossy(&run_out.stdout).lines() {
        let Some(rest) = line.trim().strip_prefix(PREFIX) else {
            continue;
        };
        let (id, hex) = rest.split_once(':').expect("id:hex");
        let trace = decode_recorded_raw_trace_hex(hex).expect("decode trace hex");
        map.insert(id.to_string(), trace);
    }
    map
}

/// Issue I-09 (Architecture B): End-to-End Binary-Level MIR Instrumentation
/// across all 75 `tests/itree-diff/corpus` functions (30 curated + 45 harvested)
/// at `-C opt-level=0` and `-C opt-level=2`, verifying:
/// 1. `anneal-mir-instrument` injects runtime hooks at `SwitchInt`, `Call`, and
///    `Return` across all 75 corpus functions at `-O0` and `-O2` with identical
///    observed event traces.
/// 2. Full branch-tag traces replay with `check_branches: true` (`diagnoseRawByteTraceFullBounded = "ok"`)
///    across all 75 corpus functions in Lean, and representative cases across all
///    categories and harvested families are kernel-confirmed (`by rfl`) for both
///    `checkRawByteTraceFullBounded_sound` (`checkBranches = true`) and
///    `checkRawByteTraceObsErasedBounded_sound` (`checkBranches = false`).
/// 3. `-O2` binaries compiled with `ANNEAL_MIR_INSTRUMENT_RAW_MIR_OPTS=1` (full
///    rustc MIR optimizations enabled) are kernel-confirmed (`by rfl`) under
///    `check_branches: false` (`checkRawByteTraceObsErasedBounded_sound`).
/// 4. Tampering with a recorded branch tag (`"branch_tag_mismatch"`), dropping a
///    branch event (`"branch_tag_mismatch"`), appending an extra branch event
///    (`"unconsumed_events"`), tampering with a call argument (`"call_arg_mismatch"`),
///    or mutating captured MIR (`"outcome_mismatch"`) is rejected by the Lean
///    kernel (`by rfl`).
#[test]
fn i09_architecture_b_binary_mir_instrumentation_corpus_o0_o2_and_branch_controls() {
    let checkout_root = repo_root();
    let temp_dir = unique_temp_dir("itree_arch_b_i09");
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
    fs::write(src_dir.join("harvested.rs"), &harvested_rs).expect("write src/harvested.rs");

    // 1. Capture unmodified MIR for all 75 corpus functions via `anneal-rustc-capture`.
    let capture_bin = ensure_rustc_capture_bin();
    let units_dir = temp_dir.join("target/anneal/units");
    let mut capture_cfg = CaptureDriverConfig::new(&temp_dir);
    capture_cfg.units_dir = units_dir.clone();
    capture_cfg.rustc_wrapper = Some(capture_bin);
    let (_manifest, records) =
        run_cargo_capture(&capture_cfg).expect("capture MIR for 75-function itree_diff_corpus");

    let mut scaffold_cfg = ScaffoldConfig::new(&temp_dir);
    scaffold_cfg.units_dir = Some(units_dir);
    scaffold_cfg.anneal_repo_root = Some(checkout_root.clone());
    scaffold_cfg.init_spec_templates = false;
    scaffold_cfg.init_proof_templates = false;
    let scaffold_report = scaffold_workspace_with_config(&scaffold_cfg, &records)
        .expect("scaffold .anneal/ Lean project for itree_diff_corpus");

    // Create mutated MIR module `Mir/ItreeDiffCorpus/call_once_mutated.lean` for negative control.
    let mir_dir = temp_dir.join(".anneal/generated/Mir/ItreeDiffCorpus");
    let orig_call_once_mir = fs::read_to_string(mir_dir.join("call_once_and_postprocess.lean"))
        .expect("read call_once_and_postprocess.lean");
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
    fs::write(mir_dir.join("call_once_mutated.lean"), &mutated_call_once_mir)
        .expect("write call_once_mutated.lean");
    let lakefile_text = fs::read_to_string(&scaffold_report.lakefile_path)
        .expect("read .anneal/lakefile.toml")
        .replace(
            "\"Mir.ItreeDiffCorpus.call_once_and_postprocess\"",
            "\"Mir.ItreeDiffCorpus.call_once_and_postprocess\", \"Mir.ItreeDiffCorpus.call_once_mutated\"",
        );
    fs::write(&scaffold_report.lakefile_path, lakefile_text)
        .expect("update .anneal/lakefile.toml");

    // 2. Compile and run the 75-function corpus trace collector with `anneal-mir-instrument`
    //    at `-C opt-level=0`, `-C opt-level=2`, and `-C opt-level=2` (raw MIR opts).
    let mir_instrument_bin = ensure_mir_instrument_bin();
    let proc_macro_dylib = build_anneal_trace_proc_macro_dylib(&temp_dir);
    let collector_src = render_corpus_binary_trace_collector(&checkout_root);
    let collector_rs = temp_dir.join("collect_corpus_traces.rs");
    fs::write(&collector_rs, &collector_src).expect("write collect_corpus_traces.rs");

    let traces_o0 = compile_and_run_corpus_collector(
        &mir_instrument_bin,
        &temp_dir,
        &proc_macro_dylib,
        &collector_rs,
        "collect_corpus_o0",
        "0",
        false,
    );
    let traces_o2 = compile_and_run_corpus_collector(
        &mir_instrument_bin,
        &temp_dir,
        &proc_macro_dylib,
        &collector_rs,
        "collect_corpus_o2",
        "2",
        false,
    );
    let traces_o2_raw_mir = compile_and_run_corpus_collector(
        &mir_instrument_bin,
        &temp_dir,
        &proc_macro_dylib,
        &collector_rs,
        "collect_corpus_o2_raw_mir",
        "2",
        true,
    );

    assert_eq!(
        traces_o0.len(),
        84,
        "expected 84 collected traces across all 75 corpus functions and mode variants"
    );
    assert_eq!(traces_o2.len(), 84);
    assert_eq!(traces_o2_raw_mir.len(), 84);

    // Verify `-O0` and `-O2` traces have identical recorded events across all 84 cases,
    // and identical outcomes across all value-returning cases.
    for (id, tr_o0) in &traces_o0 {
        let tr_o2 = traces_o2.get(id).expect("matching case in -O2");
        assert_eq!(
            tr_o0.events, tr_o2.events,
            "case `{id}` events differed between -O0 and -O2"
        );
        if id != "cat6_raw_const_ptr_identity" {
            assert_eq!(
                tr_o0.outcome, tr_o2.outcome,
                "case `{id}` outcome differed between -O0 and -O2"
            );
        }
        // Under raw MIR optimizations (`-Zmir-opt-level` untouched), external call events
        // and terminal outcomes must still agree with `-O0`:
        let tr_raw = traces_o2_raw_mir.get(id).expect("matching case in -O2 raw MIR");
        assert_eq!(
            tr_o0.without_branches().events,
            tr_raw.without_branches().events,
            "case `{id}` obs-erased external call events differed under raw MIR opts"
        );
        if id != "cat6_raw_const_ptr_identity" {
            assert_eq!(
                tr_o0.outcome, tr_raw.outcome,
                "case `{id}` outcome differed under raw MIR opts"
            );
        }
    }

    // Verify branch tags are non-empty on branching functions and reflect signed/multi-way/loop CFGs.
    assert_eq!(
        traces_o0["cat1_clamp_lo"].events,
        vec![RecordedEvent::Branch { tag: 1 }]
    );
    assert_eq!(
        traces_o0["cat1_clamp_mid"].events,
        vec![
            RecordedEvent::Branch { tag: 0 },
            RecordedEvent::Branch { tag: 0 }
        ]
    );
    assert_eq!(
        traces_o0["cat3_match_four_way_tag"].events,
        vec![
            RecordedEvent::Branch { tag: 2 },
            RecordedEvent::Branch { tag: 0 }
        ]
    );
    assert!(
        traces_o0["cat3_while_loop_accumulate"].events.len() >= 6,
        "while_loop_accumulate must record guard + loop iteration branch tags"
    );
    // Category 5 `recursive_depth_2_unroll`: in inlined mode, `helper_depth_step`'s internal
    // `if n == 0` branches are recorded (`3` Branch events, `0` ExtCall events); in external
    // mode, helper-internal branches are suppressed by `boundary_depth > 0` (`1` root Branch
    // event + `2` ExtCall events).
    assert_eq!(
        traces_o0["cat5_recursive_depth_2_unroll_inlined"].events,
        vec![
            RecordedEvent::Branch { tag: 0 },
            RecordedEvent::Branch { tag: 1 },
            RecordedEvent::Branch { tag: 0 },
        ]
    );
    assert_eq!(
        traces_o0["cat5_recursive_depth_2_unroll_ext"].events.len(),
        3
    );

    // 3. Build all 75 corpus Mir modules in `.anneal` and probe ALL 84 traces with
    //    `check_branches: true` (`diagnoseRawByteTraceFullBounded`).
    //    Note: for Category 6 reference/pointer cases, `rec.register_allocation`
    //    captures the pointee bytes (with padding marked as `None`) into
    //    `trace.shadow_provenance`, and `TraceCheck.seedShadowAllocations` seeds
    //    the initial `Memory` automatically.
    let case_specs: Vec<(&str, &str, Vec<&str>, Vec<&str>, Option<String>, usize)> = vec![
        ("cat1_clamp_lo", "Mir.ItreeDiffCorpus.clamp_u32_range", vec![], vec![], None, 40),
        ("cat1_clamp_mid", "Mir.ItreeDiffCorpus.clamp_u32_range", vec![], vec![], None, 40),
        ("cat1_rotate_xor_mix", "Mir.ItreeDiffCorpus.rotate_xor_mix", vec![], vec![], None, 40),
        ("cat1_checked_affine_step", "Mir.ItreeDiffCorpus.checked_affine_step", vec![], vec![], None, 40),
        ("cat1_signed_abs_diff", "Mir.ItreeDiffCorpus.signed_abs_diff", vec![], vec![], None, 40),
        ("cat1_bitfield_extract", "Mir.ItreeDiffCorpus.bitfield_extract", vec![], vec![], None, 40),
        ("cat2_repr_c_padded_header", "Mir.ItreeDiffCorpus.repr_c_padded_header", vec![], vec![], None, 40),
        ("cat2_nested_tuple_struct_sum", "Mir.ItreeDiffCorpus.nested_tuple_struct_sum", vec![], vec![], None, 40),
        ("cat2_c_like_enum_dispatch", "Mir.ItreeDiffCorpus.c_like_enum_dispatch", vec![], vec![], None, 40),
        ("cat2_option_u32_map_or", "Mir.ItreeDiffCorpus.option_u32_map_or", vec![], vec![], None, 40),
        ("cat2_result_u16_unwrap_or", "Mir.ItreeDiffCorpus.result_u16_unwrap_or", vec![], vec![], None, 40),
        ("cat3_match_four_way_tag", "Mir.ItreeDiffCorpus.match_four_way_tag", vec![], vec![], None, 40),
        ("cat3_short_circuit_guard_chain", "Mir.ItreeDiffCorpus.short_circuit_guard_chain", vec![], vec![], None, 40),
        ("cat3_while_loop_accumulate", "Mir.ItreeDiffCorpus.while_loop_accumulate", vec![], vec![], None, 120),
        ("cat3_early_return_search_4", "Mir.ItreeDiffCorpus.early_return_search_4", vec![], vec![], None, 40),
        ("cat3_nested_if_else_matrix", "Mir.ItreeDiffCorpus.nested_if_else_matrix", vec![], vec![], None, 40),
        ("cat4_call_once_and_postprocess", "Mir.ItreeDiffCorpus.call_once_and_postprocess", vec!["Mir.ItreeDiffCorpus.ext_transform_u32"], vec![], None, 40),
        ("cat4_call_once_scheduled_return", "Mir.ItreeDiffCorpus.call_once_and_postprocess", vec!["Mir.ItreeDiffCorpus.ext_transform_u32"], vec![], None, 40),
        ("cat4_call_once_scheduled_panic", "Mir.ItreeDiffCorpus.call_once_and_postprocess", vec!["Mir.ItreeDiffCorpus.ext_transform_u32"], vec![], None, 40),
        ("cat4_call_twice_sequential", "Mir.ItreeDiffCorpus.call_twice_sequential", vec!["Mir.ItreeDiffCorpus.ext_transform_u32"], vec![], None, 40),
        ("cat4_call_in_branch_arms", "Mir.ItreeDiffCorpus.call_in_branch_arms", vec!["Mir.ItreeDiffCorpus.ext_transform_u32", "Mir.ItreeDiffCorpus.ext_combine_u32"], vec![], None, 40),
        ("cat4_call_in_bounded_loop_3x", "Mir.ItreeDiffCorpus.call_in_bounded_loop_3x", vec!["Mir.ItreeDiffCorpus.ext_transform_u32"], vec![], None, 60),
        ("cat4_callee_panic_normal", "Mir.ItreeDiffCorpus.callee_panic_unwind_recovery", vec!["Mir.ItreeDiffCorpus.ext_may_panic_u32"], vec![], None, 40),
        ("cat4_callee_panic_unwind", "Mir.ItreeDiffCorpus.callee_panic_unwind_recovery", vec!["Mir.ItreeDiffCorpus.ext_may_panic_u32"], vec![], None, 40),
        ("cat5_pipeline_two_helpers_inlined", "Mir.ItreeDiffCorpus.pipeline_two_helpers", vec![], vec!["Mir.ItreeDiffCorpus.helper_add_const", "Mir.ItreeDiffCorpus.helper_xor_fold"], None, 60),
        ("cat5_pipeline_two_helpers_ext", "Mir.ItreeDiffCorpus.pipeline_two_helpers", vec!["Mir.ItreeDiffCorpus.helper_add_const", "Mir.ItreeDiffCorpus.helper_xor_fold"], vec![], None, 40),
        ("cat5_diamond_helper_dag_inlined", "Mir.ItreeDiffCorpus.diamond_helper_dag", vec![], vec!["Mir.ItreeDiffCorpus.helper_add_const", "Mir.ItreeDiffCorpus.helper_xor_fold"], None, 80),
        ("cat5_diamond_helper_dag_ext", "Mir.ItreeDiffCorpus.diamond_helper_dag", vec!["Mir.ItreeDiffCorpus.helper_add_const", "Mir.ItreeDiffCorpus.helper_xor_fold"], vec![], None, 40),
        ("cat5_conditional_helper_dispatch_inlined", "Mir.ItreeDiffCorpus.conditional_helper_dispatch", vec![], vec!["Mir.ItreeDiffCorpus.helper_add_const", "Mir.ItreeDiffCorpus.helper_xor_fold"], None, 60),
        ("cat5_conditional_helper_dispatch_ext", "Mir.ItreeDiffCorpus.conditional_helper_dispatch", vec!["Mir.ItreeDiffCorpus.helper_add_const", "Mir.ItreeDiffCorpus.helper_xor_fold"], vec![], None, 40),
        ("cat5_stateful_counter_pair_inlined", "Mir.ItreeDiffCorpus.stateful_counter_pair", vec![], vec!["Mir.ItreeDiffCorpus.helper_step_counter"], None, 60),
        ("cat5_stateful_counter_pair_ext", "Mir.ItreeDiffCorpus.stateful_counter_pair", vec!["Mir.ItreeDiffCorpus.helper_step_counter"], vec![], None, 40),
        ("cat5_recursive_depth_2_unroll_inlined", "Mir.ItreeDiffCorpus.recursive_depth_2_unroll", vec![], vec!["Mir.ItreeDiffCorpus.helper_depth_step"], None, 80),
        ("cat5_recursive_depth_2_unroll_ext", "Mir.ItreeDiffCorpus.recursive_depth_2_unroll", vec!["Mir.ItreeDiffCorpus.helper_depth_step"], vec![], None, 40),
        ("cat6_ref_u32_passthrough", "Mir.ItreeDiffCorpus.ref_u32_passthrough", vec![], vec![], None, 40),
        ("cat6_pair_of_refs_select", "Mir.ItreeDiffCorpus.pair_of_refs_select", vec![], vec![], None, 40),
        ("cat6_struct_field_ref_project", "Mir.ItreeDiffCorpus.struct_field_ref_project", vec![], vec![], None, 40),
        ("cat6_raw_const_ptr_identity", "Mir.ItreeDiffCorpus.raw_const_ptr_identity", vec![], vec![], None, 20),
        ("cat6_slice_len_and_ptr_meta", "Mir.ItreeDiffCorpus.slice_len_and_ptr_meta", vec![], vec![], None, 40),
        ("h_miropt_copy_prop_chain", "Mir.ItreeDiffCorpus.harvested.miropt_copy_prop_chain", vec![], vec![], None, 40),
        ("h_miropt_diamond_phi_merge", "Mir.ItreeDiffCorpus.harvested.miropt_diamond_phi_merge", vec![], vec![], None, 40),
        ("h_miropt_switch_dense_u8", "Mir.ItreeDiffCorpus.harvested.miropt_switch_dense_u8", vec![], vec![], None, 40),
        ("h_miropt_switch_sparse_u32", "Mir.ItreeDiffCorpus.harvested.miropt_switch_sparse_u32", vec![], vec![], None, 40),
        ("h_miropt_nested_tuple_swap", "Mir.ItreeDiffCorpus.harvested.miropt_nested_tuple_swap", vec![], vec![], None, 40),
        ("h_miropt_checked_add_fallback", "Mir.ItreeDiffCorpus.harvested.miropt_checked_add_fallback", vec![], vec![], None, 40),
        ("h_miropt_checked_sub_clamp_zero", "Mir.ItreeDiffCorpus.harvested.miropt_checked_sub_clamp_zero", vec![], vec![], None, 40),
        ("h_miropt_bool_to_int_weighted", "Mir.ItreeDiffCorpus.harvested.miropt_bool_to_int_weighted", vec![], vec![], None, 40),
        ("h_miropt_array_index_const_4", "Mir.ItreeDiffCorpus.harvested.miropt_array_index_const_4", vec![], vec![], None, 40),
        ("h_miropt_loop_break_threshold", "Mir.ItreeDiffCorpus.harvested.miropt_loop_break_threshold", vec![], vec![], None, 120),
        ("h_miropt_loop_continue_filter", "Mir.ItreeDiffCorpus.harvested.miropt_loop_continue_filter", vec![], vec![], None, 160),
        ("h_miropt_sign_extend_i8_to_i32", "Mir.ItreeDiffCorpus.harvested.miropt_sign_extend_i8_to_i32", vec![], vec![], None, 40),
        ("h_miropt_zero_extend_u16_to_u64", "Mir.ItreeDiffCorpus.harvested.miropt_zero_extend_u16_to_u64", vec![], vec![], None, 40),
        ("h_miropt_truncate_u64_hi_lo", "Mir.ItreeDiffCorpus.harvested.miropt_truncate_u64_hi_lo", vec![], vec![], None, 40),
        ("h_miropt_double_match_state", "Mir.ItreeDiffCorpus.harvested.miropt_double_match_state", vec![], vec![], None, 40),
        ("h_zc_pack_le_u32", "Mir.ItreeDiffCorpus.harvested.zc_pack_le_u32", vec![], vec![], None, 40),
        ("h_zc_pack_be_u32", "Mir.ItreeDiffCorpus.harvested.zc_pack_be_u32", vec![], vec![], None, 40),
        ("h_zc_bswap_u32_manual", "Mir.ItreeDiffCorpus.harvested.zc_bswap_u32_manual", vec![], vec![], None, 40),
        ("h_zc_bswap_u16_pair", "Mir.ItreeDiffCorpus.harvested.zc_bswap_u16_pair", vec![], vec![], None, 40),
        ("h_zc_align_up_pow2", "Mir.ItreeDiffCorpus.harvested.zc_align_up_pow2", vec![], vec![], None, 40),
        ("h_zc_is_aligned_check", "Mir.ItreeDiffCorpus.harvested.zc_is_aligned_check", vec![], vec![], None, 40),
        ("h_zc_split_at_bounds_check", "Mir.ItreeDiffCorpus.harvested.zc_split_at_bounds_check", vec![], vec![], None, 40),
        ("h_zc_prefix_suffix_remainder", "Mir.ItreeDiffCorpus.harvested.zc_prefix_suffix_remainder", vec![], vec![], None, 40),
        ("h_zc_u24_from_bytes", "Mir.ItreeDiffCorpus.harvested.zc_u24_from_bytes", vec![], vec![], None, 40),
        ("h_zc_validate_bool_byte", "Mir.ItreeDiffCorpus.harvested.zc_validate_bool_byte", vec![], vec![], None, 40),
        ("h_zc_validate_char_scalar", "Mir.ItreeDiffCorpus.harvested.zc_validate_char_scalar", vec![], vec![], None, 40),
        ("h_zc_nonzero_u32_extract", "Mir.ItreeDiffCorpus.harvested.zc_nonzero_u32_extract", vec![], vec![], None, 40),
        ("h_zc_ipv4_header_ihl_bytes", "Mir.ItreeDiffCorpus.harvested.zc_ipv4_header_ihl_bytes", vec![], vec![], None, 40),
        ("h_zc_tlv_record_advance", "Mir.ItreeDiffCorpus.harvested.zc_tlv_record_advance", vec![], vec![], None, 40),
        ("h_zc_checksum_ones_complement_fold", "Mir.ItreeDiffCorpus.harvested.zc_checksum_ones_complement_fold", vec![], vec![], None, 40),
        ("h_fxfs_extent_valid_range", "Mir.ItreeDiffCorpus.harvested.fxfs_extent_valid_range", vec![], vec![], None, 60),
        ("h_fxfs_extent_overlap_len", "Mir.ItreeDiffCorpus.harvested.fxfs_extent_overlap_len", vec![], vec![], None, 40),
        ("h_fxfs_round_up_block", "Mir.ItreeDiffCorpus.harvested.fxfs_round_up_block", vec![], vec![], None, 40),
        ("h_fxfs_round_down_block", "Mir.ItreeDiffCorpus.harvested.fxfs_round_down_block", vec![], vec![], None, 40),
        ("h_fxfs_block_count_for_bytes", "Mir.ItreeDiffCorpus.harvested.fxfs_block_count_for_bytes", vec![], vec![], None, 40),
        ("h_fxfs_journal_record_crc_check", "Mir.ItreeDiffCorpus.harvested.fxfs_journal_record_crc_check", vec!["Mir.ItreeDiffCorpus.ext_transform_u32"], vec![], None, 40),
        ("h_fxfs_compaction_merge_keys", "Mir.ItreeDiffCorpus.harvested.fxfs_compaction_merge_keys", vec!["Mir.ItreeDiffCorpus.ext_combine_u32"], vec![], None, 40),
        ("h_fxfs_lsm_layer_select", "Mir.ItreeDiffCorpus.harvested.fxfs_lsm_layer_select", vec![], vec![], None, 40),
        ("h_fxfs_alloc_bitmap_find_free_bit", "Mir.ItreeDiffCorpus.harvested.fxfs_alloc_bitmap_find_free_bit", vec![], vec![], None, 120),
        ("h_fxfs_object_attr_version_cmp", "Mir.ItreeDiffCorpus.harvested.fxfs_object_attr_version_cmp", vec![], vec![], None, 40),
        ("h_fxfs_refcount_saturating_adjust", "Mir.ItreeDiffCorpus.harvested.fxfs_refcount_saturating_adjust", vec![], vec![], None, 40),
        ("h_fxfs_superblock_magic_verify", "Mir.ItreeDiffCorpus.harvested.fxfs_superblock_magic_verify", vec![], vec![], None, 40),
        ("h_fxfs_extent_split_offset", "Mir.ItreeDiffCorpus.harvested.fxfs_extent_split_offset", vec![], vec![], None, 40),
        ("h_fxfs_txn_reservation_check", "Mir.ItreeDiffCorpus.harvested.fxfs_txn_reservation_check", vec![], vec![], None, 40),
        ("h_fxfs_two_phase_commit_seq", "Mir.ItreeDiffCorpus.harvested.fxfs_two_phase_commit_seq", vec!["Mir.ItreeDiffCorpus.ext_transform_u32", "Mir.ItreeDiffCorpus.ext_combine_u32"], vec![], None, 40),
    ];

    let def_to_mir_mod: BTreeMap<String, String> = records
        .iter()
        .map(|r| (r.target.def_id.clone(), r.lean_module_name.clone()))
        .collect();

    let mut full_probe_cases: Vec<BatchTraceEvalCase> = Vec::with_capacity(case_specs.len());
    let mut lake_targets: Vec<String> = vec![
        "Anneal".to_string(),
        "Mir.ItreeDiffCorpus.call_once_mutated".to_string(),
    ];
    for (ident, root_mod, callee_mods, inlined_mods, init_mem, fuel) in &case_specs {
        let trace = traces_o2
            .get(*ident)
            .unwrap_or_else(|| panic!("missing trace `{ident}`"))
            .clone();
        let resolved_root_mod = def_to_mir_mod
            .get(&trace.root_def_path)
            .cloned()
            .unwrap_or_else(|| (*root_mod).to_string());
        if !lake_targets.contains(&resolved_root_mod) {
            lake_targets.push(resolved_root_mod.clone());
        }
        for m in callee_mods.iter().chain(inlined_mods.iter()) {
            if !lake_targets.contains(&m.to_string()) {
                lake_targets.push(m.to_string());
            }
        }
        full_probe_cases.push(BatchTraceEvalCase {
            case_ident: (*ident).to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffFullCorpusProbe".to_string(),
                root_mir_module: resolved_root_mod,
                callee_sig_modules: callee_mods.iter().map(|s| (*s).to_string()).collect(),
                inlined_callee_modules: inlined_mods.iter().map(|s| (*s).to_string()).collect(),
                init_mem_expr: init_mem.clone(),
                fuel: (*fuel).max(120),
                check_branches: true,
            },
            trace,
            expected_diag_tag: Some("ok".to_string()),
            tampered_outcome: None,
        });
    }

    let anneal_dir = temp_dir.join(".anneal");
    run_lake_verify_targets(&anneal_dir, &lake_targets)
        .expect("build all 75 corpus Mir modules in .anneal");

    let verify_dir = anneal_dir.join("generated/Verify/ItreeDiffCorpus");
    fs::create_dir_all(&verify_dir).expect("create Verify/ItreeDiffCorpus");

    let full_probe_src = render_batch_trace_probe_lean_module(
        "Proof.ItreeDiffFullCorpusProbe",
        &full_probe_cases,
    );
    let full_probe_file = verify_dir.join("ItreeDiffFullCorpusProbe.lean");
    fs::write(&full_probe_file, &full_probe_src).expect("write ItreeDiffFullCorpusProbe.lean");

    let full_probe_out = Command::new("lake")
        .args(["env", "lean", "-M", "4096"])
        .arg(&full_probe_file)
        .current_dir(&anneal_dir)
        .output()
        .expect("run lake env lean on ItreeDiffFullCorpusProbe.lean");
    assert!(
        full_probe_out.status.success(),
        "ItreeDiffFullCorpusProbe.lean failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&full_probe_out.stdout),
        String::from_utf8_lossy(&full_probe_out.stderr)
    );
    let full_probe_map =
        parse_batch_trace_probe_output(&String::from_utf8_lossy(&full_probe_out.stdout));
    assert_eq!(full_probe_map.len(), 84);
    for (ident, (tag, repr)) in &full_probe_map {
        assert_eq!(
            tag, "ok",
            "corpus case `{ident}` failed full branch-checked trace replay (`check_branches: true`): {repr}"
        );
    }

    // 4. Kernel-confirm (`by rfl`) representative traces across all 6 curated categories +
    //    all 3 harvested families (`check_branches: true` -> checks BOTH
    //    `checkRawByteTraceFullBounded_sound` and `checkRawByteTraceObsErasedBounded_sound`),
    //    plus `-O2` raw-MIR-optimized traces (`check_branches: false`), plus 6 negative
    //    controls (tampered branch tag, dropped branch event, extra branch event,
    //    tampered call argument, mutated MIR).
    let confirm_idents = [
        "cat1_clamp_mid",
        "cat1_signed_abs_diff",
        "cat2_repr_c_padded_header",
        "cat2_c_like_enum_dispatch",
        "cat3_match_four_way_tag",
        "cat3_while_loop_accumulate",
        "cat4_call_once_and_postprocess",
        "cat4_call_once_scheduled_return",
        "cat4_call_once_scheduled_panic",
        "cat4_call_in_branch_arms",
        "cat4_callee_panic_unwind",
        "cat5_pipeline_two_helpers_inlined",
        "cat5_recursive_depth_2_unroll_inlined",
        "cat5_recursive_depth_2_unroll_ext",
        "cat6_ref_u32_passthrough",
        "cat6_struct_field_ref_project",
        "h_miropt_switch_sparse_u32",
        "h_miropt_loop_break_threshold",
        "h_zc_validate_bool_byte",
        "h_fxfs_compaction_merge_keys",
        "h_fxfs_refcount_saturating_adjust",
    ];
    let mut confirm_cases: Vec<BatchTraceEvalCase> = full_probe_cases
        .iter()
        .filter(|c| confirm_idents.contains(&c.case_ident.as_str()))
        .cloned()
        .map(|mut c| {
            c.config.module_namespace = "Proof.ItreeDiffArchBConfirm".to_string();
            c
        })
        .collect();
    assert_eq!(confirm_cases.len(), confirm_idents.len());

    // Also kernel-confirm `-O2` with `ANNEAL_MIR_INSTRUMENT_RAW_MIR_OPTS=1` under `check_branches: false`.
    for raw_id in ["cat1_clamp_mid", "cat3_match_four_way_tag", "cat4_call_in_branch_arms"] {
        let base = full_probe_cases
            .iter()
            .find(|c| c.case_ident == raw_id)
            .expect("base case");
        let raw_trace = traces_o2_raw_mir[raw_id].without_branches();
        confirm_cases.push(BatchTraceEvalCase {
            case_ident: format!("raw_mir_o2_{raw_id}"),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffArchBConfirm".to_string(),
                check_branches: false,
                ..base.config.clone()
            },
            trace: raw_trace,
            expected_diag_tag: Some("ok".to_string()),
            tampered_outcome: None,
        });
    }

    // Negative Control 1A: Tampered first branch tag in `cat1_clamp_mid` (`0` -> `1`)
    // is rejected with `"branch_tag_mismatch"`.
    {
        let mut tampered = traces_o2["cat1_clamp_mid"].clone();
        tampered.events[0] = RecordedEvent::Branch { tag: 1 };
        confirm_cases.push(BatchTraceEvalCase {
            case_ident: "neg_tampered_branch_tag_clamp".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffArchBConfirm".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.clamp_u32_range".to_string(),
                callee_sig_modules: vec![],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 40,
                check_branches: true,
            },
            trace: tampered,
            expected_diag_tag: Some("branch_tag_mismatch".to_string()),
            tampered_outcome: None,
        });
    }

    // Negative Control 1B: Tampered multi-way match discriminant tag in `cat3_match_four_way_tag`
    // (`2` -> `3`) is rejected with `"branch_tag_mismatch"`.
    {
        let mut tampered = traces_o2["cat3_match_four_way_tag"].clone();
        tampered.events[0] = RecordedEvent::Branch { tag: 3 };
        confirm_cases.push(BatchTraceEvalCase {
            case_ident: "neg_tampered_branch_tag_match4".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffArchBConfirm".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.match_four_way_tag".to_string(),
                callee_sig_modules: vec![],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 40,
                check_branches: true,
            },
            trace: tampered,
            expected_diag_tag: Some("branch_tag_mismatch".to_string()),
            tampered_outcome: None,
        });
    }

    // Negative Control 2: Dropping a recorded branch event from `cat3_while_loop_accumulate`
    // is rejected with `"branch_tag_mismatch"`.
    {
        let mut dropped = traces_o2["cat3_while_loop_accumulate"].clone();
        dropped.events.pop();
        confirm_cases.push(BatchTraceEvalCase {
            case_ident: "neg_dropped_branch_event_loop".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffArchBConfirm".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.while_loop_accumulate".to_string(),
                callee_sig_modules: vec![],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 120,
                check_branches: true,
            },
            trace: dropped,
            expected_diag_tag: Some("branch_tag_mismatch".to_string()),
            tampered_outcome: None,
        });
    }

    // Negative Control 3: Appending an extra trailing branch event after `cat1_clamp_lo`
    // is rejected with `"unconsumed_events"`.
    {
        let mut extra = traces_o2["cat1_clamp_lo"].clone();
        extra.events.push(RecordedEvent::Branch { tag: 0 });
        confirm_cases.push(BatchTraceEvalCase {
            case_ident: "neg_extra_branch_event_clamp".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffArchBConfirm".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.clamp_u32_range".to_string(),
                callee_sig_modules: vec![],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 40,
                check_branches: true,
            },
            trace: extra,
            expected_diag_tag: Some("unconsumed_events".to_string()),
            tampered_outcome: None,
        });
    }

    // Negative Control 4: Tampering with a recorded external-call argument in
    // `cat4_call_in_branch_arms` is rejected with `"call_arg_mismatch"`.
    {
        let mut bad_arg = traces_o2["cat4_call_in_branch_arms"].clone();
        if let Some(RecordedEvent::ExtCall { raw_args, .. }) = bad_arg.events.get_mut(1) {
            raw_args[0] = value_as_raw_bytes(&999u32);
        }
        confirm_cases.push(BatchTraceEvalCase {
            case_ident: "neg_tampered_call_arg".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffArchBConfirm".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.call_in_branch_arms".to_string(),
                callee_sig_modules: vec![
                    "Mir.ItreeDiffCorpus.ext_transform_u32".to_string(),
                    "Mir.ItreeDiffCorpus.ext_combine_u32".to_string(),
                ],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 40,
                check_branches: true,
            },
            trace: bad_arg,
            expected_diag_tag: Some("call_arg_mismatch".to_string()),
            tampered_outcome: None,
        });
    }

    // Negative Control 5: Checking binary-captured `cat4_call_once_and_postprocess`
    // against mutated MIR (`call_once_mutated`) is rejected with `"outcome_mismatch"`.
    {
        confirm_cases.push(BatchTraceEvalCase {
            case_ident: "neg_mutated_mir_outcome".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffArchBConfirm".to_string(),
                root_mir_module: "Mir.ItreeDiffCorpus.call_once_mutated".to_string(),
                callee_sig_modules: vec!["Mir.ItreeDiffCorpus.ext_transform_u32".to_string()],
                inlined_callee_modules: vec![],
                init_mem_expr: None,
                fuel: 40,
                check_branches: true,
            },
            trace: traces_o2["cat4_call_once_and_postprocess"].clone(),
            expected_diag_tag: Some("outcome_mismatch".to_string()),
            tampered_outcome: None,
        });
    }

    let confirm_src = render_batch_trace_eval_lean_module(
        "Proof.ItreeDiffArchBConfirm",
        &confirm_cases,
        false,
    );
    assert!(
        confirm_src.contains("checkRawByteTraceFullBounded_sound"),
        "confirm module with check_branches: true must emit checkRawByteTraceFullBounded_sound theorems"
    );
    assert!(
        confirm_src.contains("checkRawByteTraceObsErasedBounded_sound"),
        "confirm module must also emit checkRawByteTraceObsErasedBounded_sound theorems"
    );
    let confirm_file = verify_dir.join("ItreeDiffArchBConfirm.lean");
    fs::write(&confirm_file, &confirm_src).expect("write ItreeDiffArchBConfirm.lean");

    let confirm_out = Command::new("lake")
        .args(["env", "lean", "-M", "4096"])
        .arg(&confirm_file)
        .current_dir(&anneal_dir)
        .output()
        .expect("run lake env lean on ItreeDiffArchBConfirm.lean");
    assert!(
        confirm_out.status.success(),
        "ItreeDiffArchBConfirm.lean failed kernel confirmation:\nstdout:\n{}\nstderr:\n{}\nmodule:\n{}",
        String::from_utf8_lossy(&confirm_out.stdout),
        String::from_utf8_lossy(&confirm_out.stderr),
        confirm_src
    );

    let _ = fs::remove_dir_all(&temp_dir);
}
