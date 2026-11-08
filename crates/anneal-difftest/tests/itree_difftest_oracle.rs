// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end integration tests for live `itree-difftest` trace-observation +
//! Lean `diagnoseRawByteTraceObsErasedBounded` comparison, kernel confirmation,
//! negative controls, and `--reproduce` bundle verification.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

use anneal_difftest::itree_eval::{
    ITREE_SAFE_SEEDS, ItreeEvalOptions, evaluate_itree_batches_with_options,
    reproduce_itree_finding,
};
use anneal_difftest::mutators_itree::{generate_itree_batch, generate_itree_identity_batch};

static NEXT_TEMP_ID: AtomicU64 = AtomicU64::new(0);
static TEST_LOCK: Mutex<()> = Mutex::new(());

fn unique_temp_dir(label: &str) -> PathBuf {
    let id = NEXT_TEMP_ID.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "anneal_itree_difftest_oracle_{label}_{}_{id}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("repo root")
        .to_path_buf()
}

#[test]
fn itree_difftest_live_identity_and_mutated_batches_confirm_traces_in_lean() {
    let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let dir = unique_temp_dir("live_batches");
    let root = repo_root();
    let bin = env!("CARGO_BIN_EXE_itree-difftest");

    // 1. Identity batch (the 4 `ITREE_SAFE_SEEDS` with 0, 1, 2, and 3 external calls).
    let id_json_path = dir.join("identity.json");
    let id_findings = dir.join("id_findings");
    let out = Command::new(bin)
        .current_dir(&root)
        .args([
            "--identity",
            "--batch-size",
            "4",
            "--trials",
            "8",
            "--output-json",
        ])
        .arg(&id_json_path)
        .arg("--findings-dir")
        .arg(&id_findings)
        .output()
        .expect("run itree-difftest --identity");
    assert!(
        out.status.success(),
        "itree-difftest --identity failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let id_json = fs::read_to_string(&id_json_path).expect("read identity json");
    assert!(id_json.contains("\"oracle_comparison\": \"performed\""));
    assert!(id_json.contains("\"compared_candidates\": 4"));
    assert!(id_json.contains("\"agree_candidates\": 4"));
    assert!(id_json.contains("\"diverge_candidates\": 0"));
    assert!(id_json.contains("\"not_compared_reasons\": {"));
    assert!(id_json.contains("\"obs_path_signatures\": ["));

    // Verify via the library API that per-candidate distinct trace counts vary
    // across the 4 candidates.
    let id_batches = vec![generate_itree_identity_batch(ITREE_SAFE_SEEDS)];
    let id_summary = evaluate_itree_batches_with_options(
        "identity",
        0x1DE4_7171,
        &id_batches,
        4,
        &ItreeEvalOptions {
            trials_per_candidate: 8,
            anneal_repo_root: Some(root.clone()),
            ..ItreeEvalOptions::default()
        },
    )
    .expect("evaluate identity batch");
    assert_eq!(id_summary.compared_candidates, 4);
    assert_eq!(id_summary.agree_candidates, 4);
    assert_eq!(id_summary.diverge_candidates, 0);
    assert!(id_summary.distinct_traces_checked >= 8);
    assert_eq!(id_summary.agree_traces, id_summary.distinct_traces_checked);
    assert_eq!(
        id_summary.kernel_confirmed_traces,
        id_summary.distinct_traces_checked
    );
    assert!(!id_summary.obs_path_signatures.is_empty());
    assert!(
        id_summary
            .obs_path_signatures
            .windows(2)
            .all(|w| w[0] < w[1]),
        "obs_path_signatures must be sorted and deduplicated: {:?}",
        id_summary.obs_path_signatures
    );
    assert!(
        id_summary
            .obs_path_signatures
            .iter()
            .all(|s| s.starts_with("itree:") && s.ends_with(":normal")),
        "unexpected obs_path_signatures format: {:?}",
        id_summary.obs_path_signatures
    );
    assert_eq!(id_summary.per_candidate_distinct_traces.len(), 4);
    let min_distinct = *id_summary
        .per_candidate_distinct_traces
        .values()
        .min()
        .unwrap();
    let max_distinct = *id_summary
        .per_candidate_distinct_traces
        .values()
        .max()
        .unwrap();
    assert!(
        max_distinct > min_distinct,
        "per-candidate distinct trace counts should vary across seeds, got {:?}",
        id_summary.per_candidate_distinct_traces
    );

    // 2. Two distinct seeds in default mutated mode produce distinct mutator counts
    //    and both pass full Lean kernel confirmation.
    let seed_a_json = dir.join("seed_a.json");
    let seed_b_json = dir.join("seed_b.json");
    for (seed_hex, out_path) in [("0x11112222", &seed_a_json), ("0x9999AAAA", &seed_b_json)] {
        let run = Command::new(bin)
            .current_dir(&root)
            .args([
                "--batches",
                "1",
                "--batch-size",
                "4",
                "--trials",
                "6",
                "--seed",
                seed_hex,
                "--output-json",
            ])
            .arg(out_path)
            .output()
            .expect("run itree-difftest with seed");
        assert!(
            run.status.success(),
            "itree-difftest seed {seed_hex} failed:\n{}",
            String::from_utf8_lossy(&run.stderr)
        );
    }
    let json_a = fs::read_to_string(&seed_a_json).expect("read seed_a json");
    let json_b = fs::read_to_string(&seed_b_json).expect("read seed_b json");
    assert!(json_a.contains("\"oracle_comparison\": \"performed\""));
    assert!(json_b.contains("\"oracle_comparison\": \"performed\""));
    assert!(json_a.contains("\"diverge_candidates\": 0"));
    assert!(json_b.contains("\"diverge_candidates\": 0"));
    assert_ne!(
        json_a, json_b,
        "distinct seeds must produce distinct evaluation reports"
    );

    // 3. Multi-chunk Stage 2 confirmation (> 32 distinct traces and > 16 candidates
    //    across multiple `ITREE_CONFIRM_CHUNK_SIZE = 16` chunks).
    let multi_chunk_batches = vec![generate_itree_batch(ITREE_SAFE_SEEDS, 20, 0x3333_4444)];
    let multi_summary = evaluate_itree_batches_with_options(
        "seeded",
        0x3333_4444,
        &multi_chunk_batches,
        20,
        &ItreeEvalOptions {
            trials_per_candidate: 6,
            anneal_repo_root: Some(root.clone()),
            ..ItreeEvalOptions::default()
        },
    )
    .expect("evaluate multi-chunk batch");
    assert_eq!(multi_summary.compared_candidates, 20);
    assert!(
        multi_summary.distinct_traces_checked > 32,
        "expected > 32 distinct traces across multiple Stage 2 chunks, got {}",
        multi_summary.distinct_traces_checked
    );
    assert_eq!(
        multi_summary.kernel_confirmed_traces,
        multi_summary.distinct_traces_checked
    );
    assert_eq!(multi_summary.diverge_candidates, 0);

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn negative_control_mir_mutation_and_root_swap_produce_reproducible_divergences() {
    let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let dir = unique_temp_dir("negative_controls");
    let root = repo_root();
    let bin = env!("CARGO_BIN_EXE_itree-difftest");

    let batches = vec![generate_itree_batch(ITREE_SAFE_SEEDS, 4, 0xCAFE_1234)];

    // Negative control A: Mutating `.add` -> `.sub` in `b0_c0__kernel_step`'s
    // captured Lean MIR while keeping the real observed execution trace from
    // `b0_c0__kernel_step` must produce a kernel-confirmed divergence and a
    // reproducible finding bundle.
    let findings_a = dir.join("findings_mir_mutation");
    let summary_a = evaluate_itree_batches_with_options(
        "seeded",
        0xCAFE_1234,
        &batches,
        4,
        &ItreeEvalOptions {
            trials_per_candidate: 6,
            anneal_repo_root: Some(root.clone()),
            findings_dir: Some(findings_a.clone()),
            mir_mutations: vec![(
                "b0_c0__kernel_step".to_string(),
                ".add".to_string(),
                ".sub".to_string(),
            )],
            root_mir_swaps: Vec::new(),
        },
    )
    .expect("evaluate negative control A");
    assert_eq!(summary_a.diverge_candidates, 1);
    assert!(summary_a.diverge_traces >= 1);
    assert_eq!(
        summary_a.kernel_confirmed_divergences,
        summary_a.diverge_traces
    );
    assert!(
        !summary_a.findings.is_empty(),
        "expected at least 1 finding bundle from MIR mutation"
    );
    let finding_a = &summary_a.findings[0];
    assert_ne!(finding_a.diag_tag, "ok");
    assert!(finding_a.kernel_confirmed);
    let repro_path_a = finding_a
        .repro_path
        .as_ref()
        .expect("repro_path set when findings_dir is Some");

    let repro_out = Command::new(bin)
        .current_dir(&root)
        .arg("--reproduce")
        .arg(repro_path_a)
        .output()
        .expect("run itree-difftest --reproduce");
    assert!(
        repro_out.status.success(),
        "--reproduce failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&repro_out.stdout),
        String::from_utf8_lossy(&repro_out.stderr)
    );
    let repro_stdout = String::from_utf8_lossy(&repro_out.stdout);
    assert!(repro_stdout.contains("\"verdict\": \"diverge\""));
    assert!(repro_stdout.contains(&format!("\"diag_tag\": \"{}\"", finding_a.diag_tag)));
    assert!(repro_stdout.contains("\"kernel_confirmed\": true"));

    // Negative control B (I-06 Acceptance Criterion 3): Swapping the root function
    // in `b0_c0__kernel_step` with `Mir.ItreeDiffStaged.b0_c2__kernel_step` and
    // `b0_c1__kernel_step` with `Mir.ItreeDiffStaged.b0_c0__kernel_step` must
    // cause Lean's `diagnoseRawByteTraceObsErasedBounded` to fail (`!= "ok"`)
    // with kernel-confirmed divergence bundles.
    let findings_b = dir.join("findings_root_swap");
    let summary_b = evaluate_itree_batches_with_options(
        "seeded",
        0xCAFE_1234,
        &batches,
        4,
        &ItreeEvalOptions {
            trials_per_candidate: 6,
            anneal_repo_root: Some(root.clone()),
            findings_dir: Some(findings_b.clone()),
            mir_mutations: Vec::new(),
            root_mir_swaps: vec![
                (
                    "b0_c0__kernel_step".to_string(),
                    "Mir.ItreeDiffStaged.b0_c2__kernel_step".to_string(),
                ),
                (
                    "b0_c1__kernel_step".to_string(),
                    "Mir.ItreeDiffStaged.b0_c0__kernel_step".to_string(),
                ),
            ],
        },
    )
    .expect("evaluate negative control B");
    assert_eq!(summary_b.diverge_candidates, 2);
    assert!(summary_b.diverge_traces >= 2);
    assert_eq!(
        summary_b.kernel_confirmed_divergences,
        summary_b.diverge_traces
    );
    assert!(summary_b.findings.len() >= 2);
    let mut reproduced_fns = std::collections::BTreeSet::new();
    for finding in &summary_b.findings {
        if !reproduced_fns.insert(finding.fn_name.clone()) {
            continue;
        }
        let repro_path = finding.repro_path.as_ref().expect("repro_path");
        let repro = reproduce_itree_finding(repro_path, Some(&root))
            .expect("reproduce root-swap finding");
        assert_eq!(repro.verdict, "diverge");
        assert_eq!(repro.diag_tag, finding.diag_tag);
        assert!(repro.kernel_confirmed);
    }
    assert_eq!(reproduced_fns.len(), 2);

    let _ = fs::remove_dir_all(&dir);
}
