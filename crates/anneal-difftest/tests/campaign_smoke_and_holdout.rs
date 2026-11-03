//! Automated M4 + M5 + Blind Holdout Stitcher Verification Suite.
//!
//! Structured in strict accordance with `skills/swarm-model-refinement/SKILL.md`
//! Invariant 3 (*Mechanical Information Isolation & Discovery vs. Blind Holdout Split*):
//! - **Exposed Discovery Gates**:
//!   - [`m4_miri_difftest_5_batch_calibration_gate`]: 5 batches × 32 candidates = 160 Miri
//!     candidates at seed `0x5EED_0001`, batch-compiled under `rustc --edition=2024`,
//!     asserting compilation validity rate `>= 90%`.
//!   - [`m5_itree_difftest_5_batch_calibration_gate`]: 5 batches × 32 candidates = 160 safe
//!     ITree candidates at seed `0x5EED_0002`, asserting `0%` `unsafe` tokens, batch-compiled
//!     under `rustc --edition=2024 -D warnings` at both `-C opt-level=0` and `-C opt-level=2`,
//!     asserting compilation validity rate `>= 95%` and `MirObsPathSet` multi-path coverage.
//! - **Blind Held-Out Confirmation Gate**:
//!   - [`blind_holdout_stitcher_unseen_seed_0x484f4c44`]: Evaluates a completely separate,
//!     unexposed blind holdout seed (`0x484F_4C44`) plus adversarial edge-case inputs
//!     (empty byte slice `&[]`, single byte `&[0xFF]`, struct with multiple non-adjacent
//!     padding gaps, and `PanicOnCall(0)` immediate unwind on call `#0`) across both CLI
//!     harnesses (`miri-difftest` and `itree-difftest`) and verifies deterministic shrinker termination.

use std::collections::BTreeSet;
use std::fs;
use std::io::Write;
use std::process::{Command, Stdio};

use arbitrary::Unstructured;

use anneal_difftest::input_gen::{
    EnvScheduleGenerator, EnvStrategy, FieldLayout, LayoutAwareByteBuilder, LayoutSpec,
    MirInputDictionary, MirObsPathSet, PaddingFillPattern, ScalarLayout,
};
use anneal_difftest::instrument::{
    EnvAction, EnvSchedule, RecordedEvent, RecordedOutcome, TraceRecorder, instrument_source,
};
use anneal_difftest::mutators_itree::{contains_unsafe_token, generate_itree_batch};
use anneal_difftest::mutators_miri::generate_miri_batch;
use anneal_difftest::shrink::{shrink_bytes, shrink_mutation_chain};

fn resolve_rustc_bin() -> String {
    if let Ok(r) = std::env::var("RUSTC")
        && !r.is_empty()
    {
        return r;
    }
    if let Ok(home) = std::env::var("HOME") {
        let candidate = std::path::PathBuf::from(home).join(".cargo/bin/rustc");
        if candidate.exists() {
            return candidate.to_string_lossy().into_owned();
        }
    }
    "rustc".to_string()
}

/// Compiles a Rust source string with `rustc --edition=2024 --crate-type=lib` plus extra flags.
fn compile_module_with_rustc(label: &str, extra_flags: &[&str], source: &str) -> Result<(), String> {
    let rustc_bin = resolve_rustc_bin();
    let tmp_dir = std::env::temp_dir().join(format!(
        "anneal_campaign_gate_{}_{}",
        std::process::id(),
        label
    ));
    let _ = fs::create_dir_all(&tmp_dir);
    let out_path = tmp_dir.join("libgate.rlib");

    let mut cmd = Command::new(&rustc_bin);
    cmd.args(["--edition=2024", "--crate-type=lib"]);
    for flag in extra_flags {
        cmd.arg(flag);
    }
    cmd.arg("-o")
        .arg(&out_path)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    let mut child = cmd
        .spawn()
        .map_err(|e| format!("failed to spawn rustc for `{label}`: {e}"))?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(source.as_bytes())
            .map_err(|e| format!("failed writing stdin to rustc for `{label}`: {e}"))?;
    }

    let output = child
        .wait_with_output()
        .map_err(|e| format!("failed waiting on rustc for `{label}`: {e}"))?;
    let _ = fs::remove_dir_all(&tmp_dir);

    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// Deterministic SplitMix64 helper for test entropy slices.
fn make_seed_bytes(seed: u64, step: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    for chunk in 0..4usize {
        let mut z = seed
            .wrapping_add(step.wrapping_mul(0x9E37_79B9_7F4A_7C15))
            .wrapping_add((chunk as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9));
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^= z >> 31;
        out[chunk * 8..(chunk + 1) * 8].copy_from_slice(&z.to_le_bytes());
    }
    out
}

#[test]
fn m4_miri_difftest_5_batch_calibration_gate() {
    const BASE_SEED: u64 = 0x5EED_0001;
    const NUM_BATCHES: usize = 5;
    const BATCH_SIZE: usize = 32;
    const TOTAL_EXPECTED: usize = NUM_BATCHES * BATCH_SIZE; // 160 candidates

    let miri_seeds: &[&str] = &[
        r#"
pub fn checksum_word(x: u32, y: u32) -> u32 {
    let sum: u32 = x.wrapping_add(y);
    (sum ^ 0x55AA_55AA).rotate_left(5)
}
"#,
        r#"
pub fn signed_window(v: i32, limit: i32) -> i32 {
    let diff: i32 = v.wrapping_sub(limit);
    diff
}
"#,
    ];

    let mut all_batches = Vec::with_capacity(NUM_BATCHES);
    let mut seen_mutators = BTreeSet::new();

    for b_idx in 0..NUM_BATCHES {
        let batch_seed = BASE_SEED.wrapping_add((b_idx as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let batch = generate_miri_batch(miri_seeds, BATCH_SIZE, batch_seed);
        let replay = generate_miri_batch(miri_seeds, BATCH_SIZE, batch_seed);
        assert_eq!(
            batch, replay,
            "M4 batch {b_idx} must be bit-for-bit deterministic for seed 0x{batch_seed:016x}"
        );
        assert_eq!(batch.len(), BATCH_SIZE);

        for cand in &batch {
            for m in &cand.applied_mutators {
                seen_mutators.insert(m.clone());
            }
        }
        all_batches.push(batch);
    }

    // Verify all 5 Miri mutator families fired across the 5-batch campaign.
    for expected_mutator in [
        "ArithmeticCastMutator",
        "PlaceProjectionWrapper",
        "RawPtrOffsetMutator",
        "TreeBorrowsRetagInterleaver",
        "BitValidityTransmuteMutator",
    ] {
        assert!(
            seen_mutators.contains(expected_mutator),
            "M4 5-batch campaign must exercise `{expected_mutator}`"
        );
    }

    // Batch-compile all 5 batches (160 generated modules) under `rustc --edition=2024`.
    let mut combined_all = String::with_capacity(TOTAL_EXPECTED * 512);
    for (b_idx, batch) in all_batches.iter().enumerate() {
        for (c_idx, cand) in batch.iter().enumerate() {
            combined_all.push_str(&format!(
                "#[allow(dead_code, unused_variables, unused_assignments)]\npub mod m4_b{b_idx}_c{c_idx} {{\n{}\n}}\n",
                cand.source
            ));
        }
    }
    let total_compiled = if compile_module_with_rustc("m4_all_160", &["-A", "warnings"], &combined_all).is_ok() {
        TOTAL_EXPECTED
    } else {
        all_batches
            .iter()
            .enumerate()
            .flat_map(|(b_idx, batch)| {
                batch.iter().enumerate().map(move |(c_idx, cand)| (b_idx, c_idx, cand))
            })
            .filter(|(b_idx, c_idx, cand)| {
                compile_module_with_rustc(
                    &format!("m4_b{b_idx}_c{c_idx}"),
                    &["-A", "warnings"],
                    &cand.source,
                )
                .is_ok()
            })
            .count()
    };
    let validity_rate = (total_compiled as f64) / (TOTAL_EXPECTED as f64);

    assert!(
        validity_rate >= 0.90,
        "M4 compilation validity rate must be >= 90.0%, got {}/{} ({:.2}%)",
        total_compiled,
        TOTAL_EXPECTED,
        validity_rate * 100.0
    );
}

#[test]
fn m5_itree_difftest_5_batch_calibration_gate() {
    const BASE_SEED: u64 = 0x5EED_0002;
    const NUM_BATCHES: usize = 5;
    const BATCH_SIZE: usize = 32;
    const TOTAL_EXPECTED: usize = NUM_BATCHES * BATCH_SIZE; // 160 safe-Rust candidates

    let itree_seeds: &[&str] = &[
        r#"
pub fn ext_oracle(x: u32) -> u32 {
    x.wrapping_mul(1664525).wrapping_add(1013904223)
}

pub fn kernel_step(magic: u32, len: u32) -> u32 {
    if magic == 0x414E_4E4C {
        if len > 1024 {
            ext_oracle(len)
        } else {
            ext_oracle(magic ^ len)
        }
    } else if len == 0x80 {
        ext_oracle(0x80)
    } else {
        magic.wrapping_add(len)
    }
}
"#,
    ];

    let mut all_batches = Vec::with_capacity(NUM_BATCHES);
    let mut seen_mutators = BTreeSet::new();

    for b_idx in 0..NUM_BATCHES {
        let batch_seed = BASE_SEED.wrapping_add((b_idx as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let batch = generate_itree_batch(itree_seeds, BATCH_SIZE, batch_seed);
        assert_eq!(batch.len(), BATCH_SIZE);

        for cand in &batch {
            // Hard 0% `unsafe` token assertion across all 160 candidates!
            assert!(
                !contains_unsafe_token(&cand.source),
                "ITree candidate {} in batch {} emitted forbidden `unsafe` token:\n{}",
                cand.id,
                b_idx,
                cand.source
            );
            for m in &cand.applied_mutators {
                seen_mutators.insert(m.clone());
            }
        }
        all_batches.push(batch);
    }

    for expected_mutator in [
        "CallBoundaryOutliner",
        "LayoutPaddingPerturber",
        "BranchLoopWeaver",
        "ExtOracleInjector",
    ] {
        assert!(
            seen_mutators.contains(expected_mutator),
            "M5 5-batch campaign must exercise `{expected_mutator}`"
        );
    }

    // Batch-compile all 5 batches (160 safe candidates + instrumented module) under
    // `rustc --edition=2024 -D warnings` at BOTH `-C opt-level=0` AND `-C opt-level=2`!
    let mut combined_forbid_unsafe = String::from("#![forbid(unsafe_code)]\n");
    for (b_idx, batch) in all_batches.iter().enumerate() {
        for (c_idx, cand) in batch.iter().enumerate() {
            combined_forbid_unsafe.push_str(&format!(
                "pub mod m5_b{b_idx}_c{c_idx} {{\n{}\n}}\n",
                cand.source
            ));
        }
    }
    let inst_src = instrument_source(&all_batches[0][0].source, "kernel_step", &["ext_oracle"])
        .expect("instrument_source must succeed on safe ITree candidate");

    let (o0_all_ok, o2_all_ok, inst_ok) = std::thread::scope(|s| {
        let h0 = s.spawn(|| {
            compile_module_with_rustc(
                "m5_o0_all_160",
                &["-D", "warnings", "-C", "opt-level=0"],
                &combined_forbid_unsafe,
            )
            .is_ok()
        });
        let h2 = s.spawn(|| {
            compile_module_with_rustc(
                "m5_o2_all_160",
                &["-D", "warnings", "-C", "opt-level=2"],
                &combined_forbid_unsafe,
            )
            .is_ok()
        });
        let hi = s.spawn(|| {
            compile_module_with_rustc(
                "m5_inst_rep",
                &["-D", "warnings", "-C", "opt-level=0"],
                &inst_src,
            )
            .is_ok()
        });
        (h0.join().unwrap(), h2.join().unwrap(), hi.join().unwrap())
    });
    assert!(inst_ok, "instrumented ITree module must compile with -D warnings");

    let total_o0_compiled = if o0_all_ok { TOTAL_EXPECTED } else { 0 };
    let total_o2_compiled = if o2_all_ok { TOTAL_EXPECTED } else { 0 };
    let o0_rate = (total_o0_compiled as f64) / (TOTAL_EXPECTED as f64);
    let o2_rate = (total_o2_compiled as f64) / (TOTAL_EXPECTED as f64);

    assert!(
        o0_rate >= 0.95 && o2_rate >= 0.95,
        "M5 compilation validity rate must be >= 95.0% at both O0 and O2, got O0={}/{} ({:.2}%), O2={}/{} ({:.2}%)",
        total_o0_compiled,
        TOTAL_EXPECTED,
        o0_rate * 100.0,
        total_o2_compiled,
        TOTAL_EXPECTED,
        o2_rate * 100.0
    );

    // Verify `MirObsPathSet` multi-path coverage using `MirInputDictionary` +
    // `LayoutAwareByteBuilder` + `EnvScheduleGenerator`.
    let sample_source = &all_batches[0][0].source;
    let dict =
        MirInputDictionary::from_rust_source(sample_source).expect("valid AST for dictionary");
    let builder = LayoutAwareByteBuilder::new(&dict).with_dictionary_bias_pct(80);
    let env_gen = EnvScheduleGenerator::new(&dict)
        .with_horizon_steps(3)
        .with_panic_injection_pct(30);
    let layout = LayoutSpec::Struct {
        name: "KernelArgs".to_string(),
        total_size: 8,
        fields: vec![
            FieldLayout {
                name: "magic".to_string(),
                offset: 0,
                layout: LayoutSpec::Scalar(ScalarLayout::u32()),
            },
            FieldLayout {
                name: "len".to_string(),
                offset: 4,
                layout: LayoutSpec::Scalar(ScalarLayout::u32()),
            },
        ],
    };

    let mut path_set = MirObsPathSet::new();
    for step in 0..120u64 {
        let raw = make_seed_bytes(BASE_SEED, step);
        let mut u = Unstructured::new(&raw);
        let buf = builder.build_bytes(&layout, &mut u);
        let magic = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
        let len = u32::from_le_bytes([buf[4], buf[5], buf[6], buf[7]]);
        let sched = env_gen.generate_schedule(&["ext_oracle"], &mut u);
        let mut rec = TraceRecorder::with_schedule(sched);

        if magic == 0x414E_4E4C {
            rec.record_branch(if len > 1024 { 1 } else { 2 });
            let (idx, act) = rec.step_ext_call("ext_oracle");
            if !matches!(act, EnvAction::PanicOnCall(_)) {
                rec.record_ext_call("ext_oracle", idx, vec![len.to_le_bytes().to_vec()], vec![1]);
                rec.finish_return(&42u32);
            }
        } else if len == 0x80 {
            rec.record_branch(3);
            let (idx, act) = rec.step_ext_call("ext_oracle");
            if !matches!(act, EnvAction::PanicOnCall(_)) {
                rec.record_ext_call("ext_oracle", idx, vec![0x80u32.to_le_bytes().to_vec()], vec![2]);
                rec.finish_return(&80u32);
            }
        } else {
            rec.record_branch(4);
            rec.finish_return(&magic.wrapping_add(len));
        }

        path_set.record_trace("kernel_step", &rec, buf);
    }

    assert!(
        path_set.len() >= 4,
        "MirObsPathSet must discover multiple distinct execution/panic paths, found {}",
        path_set.len()
    );
}

#[test]
fn blind_holdout_stitcher_unseen_seed_0x484f4c44() {
    // Unexposed Blind Holdout Seed (`0x484F_4C44` = ASCII "HOLD") never used in M4/M5 calibration.
    const HOLDOUT_SEED: u64 = 0x484F_4C44;

    // -------------------------------------------------------------------------
    // Adversarial Edge Case 1: Empty byte slice `&[]` across builder, schedule,
    // and deterministic byte shrinker.
    // -------------------------------------------------------------------------
    let empty_slice: &[u8] = &[];
    let mut dict = MirInputDictionary::new();
    dict.add_switch_int_literal(0x484F_4C44, 32);

    // -------------------------------------------------------------------------
    // Adversarial Edge Case 3: Struct with MULTIPLE non-adjacent padding gaps:
    // - `b0: u8` at offset 0
    //   -> GAP #1: 3 bytes padding at offsets `1, 2, 3`
    // - `w1: u32` at offsets 4..8
    // - `b2: u8` at offset 8
    //   -> GAP #2: 7 bytes padding at offsets `9, 10, 11, 12, 13, 14, 15`
    // - `q3: u64` at offsets 16..24
    // - `flag4: bool` at offset 24
    //   -> GAP #3: 7 bytes trailing padding at offsets `25, 26, 27, 28, 29, 30, 31`
    // Total size: 32 bytes; 17 padding bytes split across 3 non-adjacent gaps!
    // -------------------------------------------------------------------------
    let multi_gap_layout = LayoutSpec::Struct {
        name: "HoldoutMultiGapStruct".to_string(),
        total_size: 32,
        fields: vec![
            FieldLayout {
                name: "b0".to_string(),
                offset: 0,
                layout: LayoutSpec::Scalar(ScalarLayout::u8()),
            },
            FieldLayout {
                name: "w1".to_string(),
                offset: 4,
                layout: LayoutSpec::Scalar(ScalarLayout::u32()),
            },
            FieldLayout {
                name: "b2".to_string(),
                offset: 8,
                layout: LayoutSpec::Scalar(ScalarLayout::u8()),
            },
            FieldLayout {
                name: "q3".to_string(),
                offset: 16,
                layout: LayoutSpec::Scalar(ScalarLayout::u64()),
            },
            FieldLayout {
                name: "flag4".to_string(),
                offset: 24,
                layout: LayoutSpec::Scalar(ScalarLayout::bool_layout()),
            },
        ],
    };

    let expected_gaps: Vec<usize> = vec![
        1, 2, 3, // Non-adjacent Gap #1
        9, 10, 11, 12, 13, 14, 15, // Non-adjacent Gap #2
        25, 26, 27, 28, 29, 30, 31, // Non-adjacent Gap #3
    ];
    let computed_gaps = multi_gap_layout.padding_offsets();
    assert_eq!(
        computed_gaps, expected_gaps,
        "HoldoutMultiGapStruct must have exact 3 non-adjacent padding gaps"
    );

    let builder = LayoutAwareByteBuilder::new(&dict)
        .with_dictionary_bias_pct(80)
        .with_validity_fault_rate_pct(0)
        .with_padding_pattern(PaddingFillPattern::PrngNonZero(HOLDOUT_SEED));
    let env_gen = EnvScheduleGenerator::new(&dict)
        .with_horizon_steps(4)
        .with_panic_injection_pct(50);

    // Evaluate Empty Slice `&[]` against the multi-gap layout & schedule generator.
    {
        let mut u_empty = Unstructured::new(empty_slice);
        let built_from_empty = builder.build_bytes(&multi_gap_layout, &mut u_empty);
        assert_eq!(built_from_empty.len(), 32);
        for &gap_off in &expected_gaps {
            assert_ne!(
                built_from_empty[gap_off], 0,
                "padding byte at offset {gap_off} must be strictly non-zero even on empty `&[]` input"
            );
        }
        assert!(
            built_from_empty[24] <= 1,
            "`bool` field at offset 24 must remain valid (`0` or `1`) on empty `&[]` input"
        );
        let sched_empty = env_gen.generate_schedule(&["holdout_ext"], &mut u_empty);
        let _ = TraceRecorder::with_schedule(sched_empty);

        let shrink_empty = shrink_bytes(empty_slice, |b| b.is_empty());
        assert!(shrink_empty.succeeded);
        assert_eq!(shrink_empty.minimized_len, 0);
    }

    // -------------------------------------------------------------------------
    // Adversarial Edge Case 2: Single byte slice `&[0xFF]` across builder,
    // schedule generator, and deterministic byte shrinker.
    // -------------------------------------------------------------------------
    let single_ff: &[u8] = &[0xFF];
    {
        let mut u_ff = Unstructured::new(single_ff);
        let built_from_ff = builder.build_bytes(&multi_gap_layout, &mut u_ff);
        assert_eq!(built_from_ff.len(), 32);
        for &gap_off in &expected_gaps {
            assert_ne!(
                built_from_ff[gap_off], 0,
                "padding byte at offset {gap_off} must be strictly non-zero on single-byte `&[0xFF]` input"
            );
        }
        assert!(
            built_from_ff[24] <= 1,
            "`bool` field at offset 24 must remain valid (`0` or `1`) on single-byte `&[0xFF]` input"
        );

        let shrink_ff = shrink_bytes(single_ff, |b| !b.is_empty() && b[0] >= 0x80);
        assert!(shrink_ff.succeeded);
        assert_eq!(
            shrink_ff.minimized_bytes,
            vec![0x80],
            "shrink_bytes(&[0xFF], b[0] >= 0x80) must reduce exact byte magnitude to `[0x80]`"
        );
    }

    // -------------------------------------------------------------------------
    // Adversarial Edge Case 4: `PanicOnCall(0)` immediate unwind on call #0!
    // -------------------------------------------------------------------------
    {
        let mut sched = EnvSchedule::new().with_panic_on_call(0);
        let mut u_panic = Unstructured::new(single_ff);
        env_gen.apply_strategy(
            &mut sched,
            "holdout_oracle",
            &EnvStrategy::PanicOnCall(0),
            &mut u_panic,
        );
        let mut rec = TraceRecorder::with_schedule(sched);
        rec.record_entry("holdout_entry", vec![single_ff.to_vec()]);

        let prev_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let (call_idx, action) = rec.step_ext_call("holdout_oracle");
            assert_eq!(call_idx, 0, "first call must have call_index == 0");
            assert_eq!(action, EnvAction::PanicOnCall(0));
            if let EnvAction::PanicOnCall(k) = action {
                panic!("immediate PanicOnCall({k}) on call #0");
            }
        }));
        std::panic::set_hook(prev_hook);

        assert!(caught.is_err(), "PanicOnCall(0) must unwind immediately on call #0");
        assert!(rec.is_panic());
        assert_eq!(rec.outcome, Some(RecordedOutcome::Panic));
        assert!(rec.events.iter().any(|ev| matches!(
            ev,
            RecordedEvent::ScheduledPanic {
                callee,
                call_index: 0
            } if callee == "holdout_oracle"
        )));
    }

    // Verify mutation-chain shrinker termination on holdout chain.
    let chain = vec!["m0", "holdout_fault", "m1", "m2", "m3"];
    let shrunk_chain = shrink_mutation_chain(&chain, |c| c.contains(&"holdout_fault"));
    assert_eq!(shrunk_chain, vec!["holdout_fault"]);

    // -------------------------------------------------------------------------
    // End-to-End Holdout Execution of BOTH Compiled CLI Harness Binaries:
    // `miri-difftest` and `itree-difftest` with unseen seed `0x484F_4C44`!
    // -------------------------------------------------------------------------
    let holdout_dir = std::env::temp_dir().join(format!(
        "anneal_holdout_0x484f4c44_{}",
        std::process::id()
    ));
    let _ = fs::create_dir_all(&holdout_dir);
    let miri_json_path = holdout_dir.join("miri_holdout.json");
    let itree_json_path = holdout_dir.join("itree_holdout.json");
    let findings_path = holdout_dir.join("findings");

    let miri_bin = env!("CARGO_BIN_EXE_miri-difftest");
    let miri_out = Command::new(miri_bin)
        .args([
            "--batches",
            "2",
            "--batch-size",
            "8",
            "--seed",
            "0x484F4C44",
            "--findings-dir",
        ])
        .arg(&findings_path)
        .arg("--output-json")
        .arg(&miri_json_path)
        .output()
        .expect("failed to execute `miri-difftest` binary");
    assert!(
        miri_out.status.success(),
        "`miri-difftest` failed on blind holdout seed 0x484F4C44:\n{}",
        String::from_utf8_lossy(&miri_out.stderr)
    );
    let miri_json = fs::read_to_string(&miri_json_path).expect("miri_holdout.json must exist");
    assert!(miri_json.contains("\"harness\": \"miri-difftest\""));
    assert!(miri_json.contains("\"compile_pass_rate_pct\": 100.00"));
    assert!(miri_json.contains("\"agreement_rate_pct\": 100.00"));

    let itree_bin = env!("CARGO_BIN_EXE_itree-difftest");
    let itree_out = Command::new(itree_bin)
        .args([
            "--batches",
            "2",
            "--batch-size",
            "8",
            "--inputs-per-fn",
            "64",
            "--seed",
            "0x484F4C44",
            "--output-json",
        ])
        .arg(&itree_json_path)
        .output()
        .expect("failed to execute `itree-difftest` binary");
    assert!(
        itree_out.status.success(),
        "`itree-difftest` failed on blind holdout seed 0x484F4C44:\n{}",
        String::from_utf8_lossy(&itree_out.stderr)
    );
    let itree_json = fs::read_to_string(&itree_json_path).expect("itree_holdout.json must exist");
    assert!(itree_json.contains("\"harness\": \"itree-difftest\""));
    assert!(itree_json.contains("\"unsafe_token_violations\": 0"));
    assert!(itree_json.contains("\"compile_pass_rate_pct\": 100.00"));
    assert!(itree_json.contains("\"metamorphic_parity_rate_pct\": 100.00"));

    let _ = fs::remove_dir_all(&holdout_dir);
}
