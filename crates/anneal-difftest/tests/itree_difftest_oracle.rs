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
    ITREE_CONFIRM_CHUNK_SIZE, ITREE_SAFE_SEEDS, ItreeEvalOptions, ItreeFindingBundle,
    evaluate_itree_batches_with_options, reproduce_itree_finding,
};
use anneal_difftest::mutators_itree::{
    GeneratedItreeCandidate, generate_itree_batch, generate_itree_identity_batch,
    reconstruct_itree_mutation_steps, replay_itree_mutation_steps,
};

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

/// Every way to pick `chain` as an ordered subsequence of `names`, as increasing
/// index lists into `names`. A finding records only mutator names, which do not
/// say which pass was kept when a mutator ran more than once.
fn ordered_name_embeddings(names: &[&str], chain: &[String]) -> Vec<Vec<usize>> {
    fn extend(
        names: &[&str],
        chain: &[String],
        from: usize,
        picked: &mut Vec<usize>,
        out: &mut Vec<Vec<usize>>,
    ) {
        let Some(want) = chain.get(picked.len()) else {
            out.push(picked.clone());
            return;
        };
        for (i, name) in names.iter().enumerate().skip(from) {
            if *name == want.as_str() {
                picked.push(i);
                extend(names, chain, i + 1, picked, out);
                picked.pop();
            }
        }
    }
    let mut out = Vec::new();
    extend(names, chain, 0, &mut Vec::new(), &mut out);
    out
}

/// Checks that every finding of a seeded single-batch run was shrunk against the
/// live oracle and that its repro-facing artifacts describe the minimized
/// candidate, returning the number of findings whose chain shrinking reduced.
fn assert_itree_findings_shrunk(
    findings: &[ItreeFindingBundle],
    batch: &[GeneratedItreeCandidate],
) -> usize {
    let mut reduced = 0usize;
    for f in findings {
        let c_idx: usize = f
            .fn_name
            .strip_prefix("b0_c")
            .and_then(|rest| rest.split("__").next())
            .and_then(|idx| idx.parse().ok())
            .unwrap_or_else(|| panic!("unexpected staged root `{}`", f.fn_name));
        let cand = &batch[c_idx];
        assert_eq!(f.original_mutator_chain, cand.applied_mutators, "{}", f.finding_id);
        assert_eq!(f.applied_mutators, f.minimized_mutator_chain, "{}", f.finding_id);
        assert!(
            ["minimized", "already_one_minimal"].contains(&f.shrink_status.as_str()),
            "{}: live shrinking must judge every reduction, got `{}`",
            f.finding_id,
            f.shrink_status
        );
        // A 1- or 2-pass chain needs at least the `[]` query. A shrink executes at
        // most one live run per query, and none for a program that an earlier
        // shrink of the same candidate (another signature) already judged.
        assert!(f.shrink_evaluations >= 1, "{}", f.finding_id);
        assert!(
            f.executed_oracle_runs <= f.shrink_evaluations,
            "{}: executed_oracle_runs={} shrink_evaluations={}",
            f.finding_id,
            f.executed_oracle_runs,
            f.shrink_evaluations
        );
        let (base, steps) =
            reconstruct_itree_mutation_steps(cand, ITREE_SAFE_SEEDS).expect("replayable candidate");
        let names: Vec<&str> = steps.iter().map(|s| s.mutator_name.as_str()).collect();
        let embeddings = ordered_name_embeddings(&names, &f.minimized_mutator_chain);
        assert!(
            !embeddings.is_empty(),
            "{}: minimized_mutator_chain {:?} is not an ordered subsequence of {:?}",
            f.finding_id,
            f.minimized_mutator_chain,
            cand.applied_mutators
        );
        assert!(
            embeddings.iter().any(|kept_idx| {
                let kept: Vec<_> = kept_idx.iter().map(|&i| steps[i].clone()).collect();
                replay_itree_mutation_steps(cand, &base, &kept).source == f.candidate_source
            }),
            "{}: repro.rs must be the minimized candidate's program",
            f.finding_id
        );
        if f.shrink_status == "minimized" {
            assert!(f.minimized_mutator_chain.len() < f.original_mutator_chain.len());
            assert_ne!(f.candidate_source, cand.source, "{}", f.finding_id);
            reduced += 1;
        } else {
            assert_eq!(f.candidate_source, cand.source, "{}", f.finding_id);
        }
        let repro = f.repro_path.as_ref().expect("repro_path");
        let finding_json = fs::read_to_string(repro.with_file_name("finding.json"))
            .expect("read finding.json");
        for key in [
            "\"original_mutator_chain\": [",
            "\"minimized_mutator_chain\": [",
            "\"shrink_evaluations\": ",
            "\"executed_oracle_runs\": ",
        ] {
            assert!(finding_json.contains(key), "{}: finding.json lacks {key}", f.finding_id);
        }
        assert!(finding_json.contains(&format!("\"shrink_status\": \"{}\"", f.shrink_status)));
        assert_eq!(fs::read_to_string(repro).expect("read repro.rs"), f.candidate_source);
    }
    let distinct_fns: std::collections::BTreeSet<&str> =
        findings.iter().map(|f| f.fn_name.as_str()).collect();
    let distinct_traces: std::collections::BTreeSet<(&str, &str)> = findings
        .iter()
        .map(|f| (f.fn_name.as_str(), f.trace_hex.as_str()))
        .collect();
    if findings.len() > distinct_fns.len() {
        assert!(
            distinct_traces.len() > distinct_fns.len(),
            "multi-trace candidates must retain distinct minimized traces across findings, got {} distinct traces for {} findings across {} candidate(s)",
            distinct_traces.len(),
            findings.len(),
            distinct_fns.len()
        );
    }
    // Each candidate's first shrink starts from an empty live-oracle memo, so it
    // executes at least one live run (on the unmutated seed `[]`).
    for fn_name in &distinct_fns {
        let executed = findings
            .iter()
            .filter(|f| f.fn_name == *fn_name)
            .map(|f| f.executed_oracle_runs)
            .max()
            .unwrap_or(0);
        assert!(executed >= 1, "`{fn_name}`: shrinking executed no live oracle run");
    }
    reduced
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
    //    across multiple `ITREE_CONFIRM_CHUNK_SIZE = 16` chunks). Above 32 traces
    //    Stage 2 kernel-confirms every divergence plus the first trace of every
    //    candidate, and `kernel_confirmed_traces` must report exactly the traces
    //    the kernel checked (never the full distinct-trace count).
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
    assert_eq!(multi_summary.not_compared_candidates, 0);
    assert_eq!(
        multi_summary.not_compared_reasons.values().sum::<usize>(),
        0,
        "unexpected not-compared reasons: {:?}",
        multi_summary.not_compared_reasons
    );
    assert!(
        multi_summary.distinct_traces_checked > 32,
        "expected > 32 distinct traces across multiple Stage 2 chunks, got {}",
        multi_summary.distinct_traces_checked
    );
    assert_eq!(multi_summary.diverge_candidates, 0);
    assert_eq!(
        multi_summary.kernel_confirmed_traces, multi_summary.compared_candidates,
        "with 0 divergences, Stage 2 confirms exactly one trace per candidate"
    );
    assert!(
        multi_summary.kernel_confirmed_traces > ITREE_CONFIRM_CHUNK_SIZE
            && multi_summary.kernel_confirmed_traces < multi_summary.distinct_traces_checked,
        "Stage 2 must span multiple {ITREE_CONFIRM_CHUNK_SIZE}-case chunks without \
         over-claiming: kernel_confirmed_traces={}, distinct_traces_checked={}",
        multi_summary.kernel_confirmed_traces,
        multi_summary.distinct_traces_checked
    );
    assert!(
        multi_summary
            .obs_path_signatures
            .iter()
            .all(|s| !s.contains("b0_c")),
        "obs_path_signatures must not depend on candidate positions: {:?}",
        multi_summary.obs_path_signatures
    );

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn negative_control_mir_mutation_and_root_swap_produce_reproducible_divergences() {
    let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let dir = unique_temp_dir("negative_controls");
    let root = repo_root();
    let bin = env!("CARGO_BIN_EXE_itree-difftest");

    let batch_seed = (0u64..)
        .map(|off| 0xCAFE_1234u64.wrapping_add(off))
        .find(|&s| {
            let b = generate_itree_batch(ITREE_SAFE_SEEDS, 4, s);
            b[0].applied_mutators.len() == 2 && b[1].applied_mutators.len() == 2
        })
        .expect("find seed where b0_c0 and b0_c1 both have 2 mutator passes");
    let batches = vec![generate_itree_batch(ITREE_SAFE_SEEDS, 4, batch_seed)];
    assert_eq!(batches[0][1].applied_mutators[0], "LayoutPaddingPerturber");
    let init_word: u32 = batches[0][1]
        .source
        .lines()
        .find_map(|line| {
            let rest = line.trim().strip_prefix("aligned_word:")?.trim();
            rest.strip_suffix("u32,")?.parse().ok()
        })
        .expect("extract LayoutPaddingPerturber aligned_word literal from b0_c1");

    // Negative control A:
    // 1. Mutating `.add` -> `.sub` in `b0_c0__kernel_step`'s captured Lean MIR
    //    injects a seed-level fault (present even on `[]`), so live shrinking
    //    reduces `b0_c0`'s 2-mutator chain all the way to `[]` (`2 -> 0`).
    // 2. Mutating `aligned_word`'s `{ bits := <init_word>, sizeBytes := 4 }` ->
    //    `{ bits := 0, sizeBytes := 4 }` (injected only by `LayoutPaddingPerturber`
    //    in pass 0 of `b0_c1__kernel_step`, causing `if __itree_pad_fold == 0` to
    //    short-circuit to `0u32` in Lean MIR) leaves `[]` and pass 1 alone agreeing
    //    via `MirMutationPolicy::SkipAbsent`, so live shrinking reduces `b0_c1`'s
    //    2-mutator chain to the non-empty 1-minimal chain
    //    `["LayoutPaddingPerturber"]` (`2 -> 1`).
    let findings_a = dir.join("findings_mir_mutation");
    let summary_a = evaluate_itree_batches_with_options(
        "seeded",
        batch_seed,
        &batches,
        4,
        &ItreeEvalOptions {
            trials_per_candidate: 6,
            anneal_repo_root: Some(root.clone()),
            findings_dir: Some(findings_a.clone()),
            mir_mutations: vec![
                (
                    "b0_c0__kernel_step".to_string(),
                    ".add".to_string(),
                    ".sub".to_string(),
                ),
                (
                    "b0_c1__kernel_step".to_string(),
                    format!("{{ bits := {init_word}, sizeBytes := 4 }}"),
                    "{ bits := 0, sizeBytes := 4 }".to_string(),
                ),
            ],
            root_mir_swaps: Vec::new(),
            ..ItreeEvalOptions::default()
        },
    )
    .expect("evaluate negative control A");
    assert_eq!(summary_a.diverge_candidates, 2);
    assert!(summary_a.diverge_traces >= 2);
    assert_eq!(
        summary_a.kernel_confirmed_divergences,
        summary_a.diverge_traces
    );
    assert!(
        summary_a.findings.len() >= 2,
        "expected findings for both b0_c0 and b0_c1 from MIR mutation"
    );
    // Shrinking keeps both injected faults: the `.add -> .sub` mutation of `b0_c0`
    // and the `aligned_word` mutation of `b0_c1` apply to every reduction whose
    // captured MIR still contains the mutated pattern (and are skipped otherwise).
    let reduced_a = assert_itree_findings_shrunk(&summary_a.findings, &batches[0]);
    eprintln!(
        "negative control A: {reduced_a} of {} finding(s) minimized",
        summary_a.findings.len()
    );
    let c0_finding = summary_a
        .findings
        .iter()
        .find(|f| f.fn_name == "b0_c0__kernel_step")
        .expect("b0_c0 finding");
    assert_eq!(c0_finding.shrink_status, "minimized");
    assert!(
        c0_finding.minimized_mutator_chain.is_empty(),
        "b0_c0 seed-level MIR fault must shrink 2 -> 0, got {:?}",
        c0_finding.minimized_mutator_chain
    );
    let c1_finding = summary_a
        .findings
        .iter()
        .find(|f| f.fn_name == "b0_c1__kernel_step")
        .expect("b0_c1 finding");
    assert_eq!(c1_finding.shrink_status, "minimized");
    assert_eq!(
        c1_finding.minimized_mutator_chain,
        vec!["LayoutPaddingPerturber".to_string()],
        "b0_c1 mutator-specific MIR fault must shrink 2 -> 1"
    );

    for finding_a in [c0_finding, c1_finding] {
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
            "--reproduce failed for {}:\nstdout:\n{}\nstderr:\n{}",
            finding_a.fn_name,
            String::from_utf8_lossy(&repro_out.stdout),
            String::from_utf8_lossy(&repro_out.stderr)
        );
        let repro_stdout = String::from_utf8_lossy(&repro_out.stdout);
        assert!(repro_stdout.contains("\"verdict\": \"diverge\""));
        assert!(repro_stdout.contains(&format!("\"diag_tag\": \"{}\"", finding_a.diag_tag)));
        assert!(repro_stdout.contains("\"kernel_confirmed\": true"));
    }

    // Negative control B (I-06 Acceptance Criterion 3): Swapping the root function
    // in `b0_c0__kernel_step` with `Mir.ItreeDiffStaged.b0_c2__kernel_step` and
    // `b0_c1__kernel_step` with `Mir.ItreeDiffStaged.b0_c0__kernel_step` must
    // cause Lean's `diagnoseRawByteTraceObsErasedBounded` to fail (`!= "ok"`)
    // with kernel-confirmed divergence bundles.
    let findings_b = dir.join("findings_root_swap");
    let summary_b = evaluate_itree_batches_with_options(
        "seeded",
        batch_seed,
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
            ..ItreeEvalOptions::default()
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
    // Shrinking keeps the root swaps: each reduced program is judged against the
    // same swapped-in root `Mir` module of an unmodified candidate.
    let reduced_b = assert_itree_findings_shrunk(&summary_b.findings, &batches[0]);
    eprintln!(
        "negative control B: {reduced_b} of {} finding(s) minimized",
        summary_b.findings.len()
    );
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
