// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Batch compilation, native boundary-interposed trace collection
//! (`#[anneal_trace::external]`), trace deduplication, and batched Lean 4
//! `TraceCheck` evaluation (`diagnoseRawByteTraceObsErasedBounded` +
//! `checkRawByteTraceObsErasedBounded_sound`) for `itree-difftest`.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use arbitrary::Unstructured;
use cargo_anneal::{
    BatchTraceEvalCase, CaptureDriverConfig, RecordedEvent, RecordedOutcome, RecordedRawTrace,
    ScaffoldConfig, TraceCheckModuleConfig, decode_recorded_raw_trace_hex,
    encode_recorded_raw_trace_hex, parse_batch_trace_probe_output,
    render_batch_trace_eval_lean_module, render_batch_trace_probe_lean_module, run_cargo_capture,
    run_lake_verify_targets, scaffold_workspace_with_config,
};

use crate::input_gen::{
    LayoutAwareByteBuilder, LayoutSpec, MirInputDictionary, MirObsPathSet, PaddingFillPattern,
    ScalarLayout,
};
use crate::miri_eval::{json_escape, resolve_rustc_bin};
use crate::mutators_itree::{
    GeneratedItreeCandidate, StagedItreeCandidate, annotate_itree_external_callees,
    contains_unsafe_token, stage_itree_candidate_items,
};
use crate::mutators_miri::DetRng;

/// Strictly safe seed programs with target root function `kernel_step` and
/// external boundary callee `ext_oracle`.
///
/// All arithmetic uses widening integer casts (`((a as u64) + (b as u64)) as u32`)
/// and primitive operators so `-Zmir-opt-level=0` lowers every seed and mutant
/// to pure MIR without unmodeled `core::num` intrinsic calls. Across the four
/// seeds, `kernel_step` exhibits `0`, `1`, `2`, or `3` external calls depending
/// on `(magic, payload_len)`, ensuring distinct-trace counts vary across seeds
/// and candidates.
pub const ITREE_SAFE_SEEDS: &[&str] = &[
    r#"
pub fn ext_oracle(query: u32) -> u32 {
    ((query >> 2) * 3) + 7
}

pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {
    if magic == 0x414E_4E4C {
        if payload_len > 1024 {
            ext_oracle(payload_len)
        } else {
            ext_oracle(payload_len + 1)
        }
    } else if payload_len == 0x80 {
        ext_oracle(0x80)
    } else {
        0
    }
}
"#,
    r#"
pub fn ext_oracle(query: u32) -> u32 {
    (query >> 3) + 0x55AA
}

pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {
    let delta: u32 = if magic >= payload_len {
        magic - payload_len
    } else {
        payload_len - magic
    };
    if delta < 16 {
        ext_oracle(delta)
    } else if delta == 0xDEAD_BEEF {
        ext_oracle(0xDEAD_BEEF)
    } else if delta < 0x8000_0000 {
        delta + 42
    } else {
        delta
    }
}
"#,
    r#"
pub fn ext_oracle(query: u32) -> u32 {
    ((query % 65536) * 5) + 11
}

pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {
    match magic % 4 {
        0 => {
            if payload_len < 0x8000_0000 {
                payload_len + 1
            } else {
                payload_len
            }
        }
        1 => ext_oracle(magic),
        2 => {
            let first = ext_oracle(magic);
            ext_oracle(first)
        }
        _ => {
            let first = ext_oracle(magic);
            let second = ext_oracle(first);
            ext_oracle(second)
        }
    }
}
"#,
    r#"
pub fn ext_oracle(query: u32) -> u32 {
    (query >> 1) + 0x1020
}

pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {
    let bound: u32 = payload_len % 4;
    let mut i: u32 = 0;
    let mut acc: u32 = magic;
    while i < bound {
        acc = ext_oracle(acc);
        i = i + 1;
    }
    acc
}
"#,
];

/// Canonical mutator names always included in `mutator_applications`.
pub const ITREE_MUTATOR_NAMES: [&str; 4] = [
    "CallBoundaryOutliner",
    "LayoutPaddingPerturber",
    "BranchLoopWeaver",
    "ExtOracleInjector",
];

/// Canonical `TraceReplayDiag.tagName` keys always included in `diag_tag_counts`.
pub const ITREE_DIAG_TAG_NAMES: [&str; 11] = [
    "ok",
    "outcome_mismatch",
    "unexpected_ext_call",
    "call_arg_mismatch",
    "branch_tag_mismatch",
    "unconsumed_events",
    "step_faulted",
    "decode_arg_failed",
    "decode_event_failed",
    "decode_outcome_failed",
    "out_of_fuel",
];

/// Default number of input trials executed natively per compiled candidate.
pub const DEFAULT_ITREE_TRIALS_PER_CANDIDATE: usize = 12;

/// Step fuel bound passed to `diagnoseRawByteTraceObsErasedBounded` and
/// `checkRawByteTraceObsErasedBounded_sound`.
pub const ITREE_TRACE_CHECK_FUEL: usize = 240;

/// Per-candidate compilation results across `-C opt-level=0`, `-C opt-level=2`,
/// and the `syn` source-to-source instrumenter check.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CandidateCompile {
    /// Compiled cleanly under `#![forbid(unsafe_code)]` at `-C opt-level=0`.
    pub opt0: bool,
    /// Compiled cleanly under `#![forbid(unsafe_code)]` at `-C opt-level=2`.
    pub opt2: bool,
    /// Auto-instrumented copy compiled cleanly at `-C opt-level=0`.
    pub instrumented: bool,
}

/// Optional configuration and negative-control fault injection hooks for
/// [`evaluate_itree_batches_with_options`].
#[derive(Debug, Clone)]
pub struct ItreeEvalOptions {
    /// Number of native execution trials per compiled candidate.
    pub trials_per_candidate: usize,
    /// Optional path to the Anneal repository root (`trusted/lean` and `theory`).
    pub anneal_repo_root: Option<PathBuf>,
    /// Optional directory where self-contained finding bundles are written.
    pub findings_dir: Option<PathBuf>,
    /// Optional `(staged_fn_name, from_substr, to_substr)` replacements applied
    /// to `.anneal/generated/Mir/ItreeDiffStaged/<staged_fn_name>.lean` before
    /// Lean evaluation (used by negative-control tests to verify that mutating
    /// captured MIR produces a `TraceReplayDiag` divergence).
    pub mir_mutations: Vec<(String, String, String)>,
    /// Optional `(staged_fn_name, replacement_root_mir_module)` overrides
    /// applied when constructing `BatchTraceEvalCase`s (used by negative-control
    /// tests to verify that swapping the root function produces a
    /// `TraceReplayDiag` divergence).
    pub root_mir_swaps: Vec<(String, String)>,
}

impl Default for ItreeEvalOptions {
    fn default() -> Self {
        Self {
            trials_per_candidate: DEFAULT_ITREE_TRIALS_PER_CANDIDATE,
            anneal_repo_root: None,
            findings_dir: None,
            mir_mutations: Vec::new(),
            root_mir_swaps: Vec::new(),
        }
    }
}

/// Self-contained diagnostic bundle emitted for a single ITree trace replay
/// divergence (`TraceReplayDiag.tagName != "ok"`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ItreeFindingBundle {
    /// Stable identifier within the run (e.g., `"finding_0000_b0_c0__kernel_step"`).
    pub finding_id: String,
    /// Staged root function identifier (e.g., `"b0_c0__kernel_step"`).
    pub fn_name: String,
    /// Lean case identifier in `ItreeDiffBatchConfirm.lean`.
    pub case_ident: String,
    /// Index of the seed program from `ITREE_SAFE_SEEDS`.
    pub seed_index: usize,
    /// Ordered list of safe AST mutators applied to produce this candidate.
    pub applied_mutators: Vec<String>,
    /// `TraceReplayDiag.tagName` reported by Lean (e.g., `"outcome_mismatch"`).
    pub diag_tag: String,
    /// Full Lean `reprStr` of the `TraceReplayDiag` value.
    pub diag_repr: String,
    /// Encoded hex line of the diverging [`RecordedRawTrace`].
    pub trace_hex: String,
    /// Whether the Lean 4 kernel confirmed `(diagnoseRawByteTraceObsErasedBounded ...).tagName = "<diag_tag>"` via `by rfl`.
    pub kernel_confirmed: bool,
    /// Kernel-checked `theorem <case_ident>_diag_tag` snippet from `ItreeDiffBatchConfirm.lean`.
    pub kernel_confirm_theorem: String,
    /// Extracted neighborhood from the `.anneal/generated/Mir` module checked against the trace.
    pub mir_neighborhood: String,
    /// Full Lean source of the `Mir` module checked against the trace.
    pub checked_mir_source: String,
    /// Staged root `Mir` module name (e.g., `"Mir.ItreeDiffStaged.b0_c0__kernel_step"`).
    pub checked_mir_module: String,
    /// Standalone safe Rust candidate source (`repro.rs`).
    pub candidate_source: String,
    /// Path to `repro.rs` on disk when `findings_dir` was provided.
    pub repro_path: Option<PathBuf>,
}

/// Complete report produced by [`evaluate_itree_batches`].
#[derive(Debug, Clone)]
pub struct ItreeCampaignEvalReport {
    /// `"identity"` or `"seeded"`.
    pub mode: String,
    /// Master PRNG seed.
    pub seed: u64,
    /// Number of batches generated.
    pub batches: usize,
    /// Target candidate count per batch.
    pub batch_size: usize,
    /// Number of native trials executed per compiled candidate.
    pub trials_per_candidate: usize,
    /// Total candidates generated across all batches.
    pub total_candidates: usize,
    /// Count of candidates containing an `unsafe` token (always `0`).
    pub unsafe_token_violations: usize,
    /// Count of candidates that compiled at `-C opt-level=0`.
    pub opt_level_0_compiled: usize,
    /// Count of candidates that compiled at `-C opt-level=2`.
    pub opt_level_2_compiled: usize,
    /// Count of candidates that compiled at both `-O0` and `-O2`.
    pub opt_level_0_and_2_compiled: usize,
    /// Count of candidates whose `syn`-instrumented copy compiled at `-O0`.
    pub instrumented_compiled: usize,
    /// Percentage of generated candidates that compiled at both `-O0` and `-O2`.
    pub compile_pass_rate_pct: f64,
    /// Count of candidates evaluated against Lean `TraceCheck`.
    pub compared_candidates: usize,
    /// Count of candidates whose distinct traces all replayed with `"ok"`.
    pub agree_candidates: usize,
    /// Count of candidates with at least one trace where `TraceReplayDiag != "ok"`.
    pub diverge_candidates: usize,
    /// Count of candidates not compared (compile failures).
    pub not_compared_candidates: usize,
    /// Total native executions performed across all compiled candidates.
    pub total_traces_executed: usize,
    /// Total deduplicated distinct traces checked in Lean across all candidates.
    pub distinct_traces_checked: usize,
    /// Count of distinct traces where Lean reported `"ok"`.
    pub agree_traces: usize,
    /// Count of distinct traces where Lean reported a non-`"ok"` `TraceReplayDiag`.
    pub diverge_traces: usize,
    /// Count of distinct traces kernel-confirmed via `by rfl` in `ItreeDiffBatchConfirm.lean`.
    pub kernel_confirmed_traces: usize,
    /// Count of diverging traces kernel-confirmed via `by rfl`.
    pub kernel_confirmed_divergences: usize,
    /// Total distinct external-call observation path shapes (`MirObsPathKey`) observed.
    pub distinct_obs_paths: usize,
    /// Per-candidate distinct trace counts (`b{b_idx}_c{c_idx}__kernel_step -> count`).
    pub per_candidate_distinct_traces: BTreeMap<String, usize>,
    /// Trace counts by `TraceReplayDiag.tagName`.
    pub diag_tag_counts: BTreeMap<String, usize>,
    /// Per-mutator application counts across all generated candidates.
    pub mutator_applications: BTreeMap<String, usize>,
    /// Self-contained finding bundles for every diverging trace.
    pub findings: Vec<ItreeFindingBundle>,
    /// Total wall-clock duration in milliseconds.
    pub elapsed_ms: f64,
}

/// Result of re-running a standalone ITree finding bundle via
/// [`reproduce_itree_finding`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ItreeReproReport {
    /// Staged root function identifier.
    pub fn_name: String,
    /// `"agree"` when `diag_tag == "ok"`, or `"diverge"` otherwise.
    pub verdict: String,
    /// `TraceReplayDiag.tagName` produced on replay.
    pub diag_tag: String,
    /// Full Lean `reprStr` of `TraceReplayDiag` on replay.
    pub diag_repr: String,
    /// Whether the Lean 4 kernel confirmed `.tagName = "<diag_tag>"` via `by rfl`.
    pub kernel_confirmed: bool,
}

/// Runs `rustc --edition=2024 --crate-type=lib -D warnings -C opt-level=<level>`
/// on `source` and reports whether it compiled.
pub fn compile_rust_strict_opt(label: &str, opt_level: &str, source: &str) -> bool {
    let rustc_bin = resolve_rustc_bin();
    let tmp_dir = env::temp_dir().join(format!(
        "anneal_itree_difftest_{}_{}_o{}",
        std::process::id(),
        label,
        opt_level
    ));
    let _ = fs::create_dir_all(&tmp_dir);
    let out_path = tmp_dir.join("libitree_check.rlib");
    let opt_flag = format!("opt-level={opt_level}");

    let child_res = Command::new(&rustc_bin)
        .args([
            "--edition=2024",
            "--crate-type=lib",
            "-D",
            "warnings",
            "-C",
            &opt_flag,
            "-o",
        ])
        .arg(&out_path)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn();

    let Ok(mut child) = child_res else {
        let _ = fs::remove_dir_all(&tmp_dir);
        return false;
    };

    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(source.as_bytes());
    }
    let ok = child
        .wait_with_output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    let _ = fs::remove_dir_all(&tmp_dir);
    ok
}

/// Compiles every candidate under `#![forbid(unsafe_code)]` at `-C opt-level=0`
/// and `-C opt-level=2`, and compiles every candidate's `#[anneal_trace::external]`-
/// annotated copy at `-C opt-level=0`. Each check first compiles all candidates
/// as one crate and falls back to one candidate at a time only when the combined
/// crate fails.
pub fn compile_itree_candidates(
    batches: &[Vec<GeneratedItreeCandidate>],
) -> Vec<Vec<CandidateCompile>> {
    let mut results: Vec<Vec<CandidateCompile>> = batches
        .iter()
        .map(|b| vec![CandidateCompile::default(); b.len()])
        .collect();

    let mut combined_safe = String::from("#![forbid(unsafe_code)]\n");
    let mut combined_inst =
        String::from("#![feature(register_tool)]\n#![register_tool(anneal_trace)]\n");
    let mut inst_sources: Vec<Vec<Option<String>>> = Vec::with_capacity(batches.len());
    for (b_idx, batch) in batches.iter().enumerate() {
        let mut batch_inst = Vec::with_capacity(batch.len());
        for (c_idx, cand) in batch.iter().enumerate() {
            combined_safe.push_str(&format!(
                "pub mod b{b_idx}_c{c_idx} {{\n{}\n}}\n",
                cand.source
            ));
            let inst = annotate_itree_external_callees(&cand.source, "kernel_step")
                .ok()
                .map(|(annotated, _)| annotated);
            if let Some(src) = &inst {
                combined_inst.push_str(&format!("pub mod inst_b{b_idx}_c{c_idx} {{\n{src}\n}}\n"));
            }
            batch_inst.push(inst);
        }
        inst_sources.push(batch_inst);
    }
    let any_inst_failed = inst_sources.iter().flatten().any(Option::is_none);

    let (o0_all, o2_all, inst_all) = std::thread::scope(|s| {
        let h0 = s.spawn(|| compile_rust_strict_opt("all_safe", "0", &combined_safe));
        let h2 = s.spawn(|| compile_rust_strict_opt("all_safe", "2", &combined_safe));
        let hi = s.spawn(|| {
            !any_inst_failed
                && !combined_inst.is_empty()
                && compile_rust_strict_opt("all_inst", "0", &combined_inst)
        });
        (
            h0.join().unwrap_or(false),
            h2.join().unwrap_or(false),
            hi.join().unwrap_or(false),
        )
    });

    for (b_idx, batch) in batches.iter().enumerate() {
        for (c_idx, cand) in batch.iter().enumerate() {
            let safe_src = format!("#![forbid(unsafe_code)]\n{}", cand.source);
            let label = format!("b{b_idx}_c{c_idx}");
            let entry = &mut results[b_idx][c_idx];
            entry.opt0 = o0_all || compile_rust_strict_opt(&label, "0", &safe_src);
            entry.opt2 = o2_all || compile_rust_strict_opt(&label, "2", &safe_src);
            entry.instrumented = match &inst_sources[b_idx][c_idx] {
                None => false,
                Some(src) => {
                    let inst_src = format!(
                        "#![feature(register_tool)]\n#![register_tool(anneal_trace)]\n{src}"
                    );
                    inst_all || compile_rust_strict_opt(&format!("{label}_inst"), "0", &inst_src)
                }
            };
        }
    }
    results
}

fn default_repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
        .to_path_buf()
}

fn ensure_rustc_capture_bin(repo_root: &Path) -> Result<PathBuf, String> {
    let bin_path = repo_root.join("target/debug/anneal-rustc-capture");
    if bin_path.is_file() {
        return Ok(bin_path);
    }
    let status = Command::new("cargo")
        .args(["build", "-p", "anneal-rustc-capture", "--locked"])
        .current_dir(repo_root)
        .status()
        .map_err(|e| format!("failed to invoke cargo build for anneal-rustc-capture: {e}"))?;
    if !status.success() {
        return Err("building anneal-rustc-capture failed".to_string());
    }
    Ok(bin_path)
}

fn build_anneal_trace_proc_macro_dylib(
    repo_root: &Path,
    staging_dir: &Path,
) -> Result<PathBuf, String> {
    let ext = if cfg!(target_os = "macos") {
        "dylib"
    } else {
        "so"
    };
    // Reuse a cached proc-macro dylib in `target/debug/` when up to date.
    let src_path = repo_root.join("crates/anneal-trace/src/lib.rs");
    let shared_out = repo_root
        .join("target/debug")
        .join(format!("libanneal_trace_difftest.{ext}"));
    let src_mtime = fs::metadata(&src_path).and_then(|m| m.modified()).ok();
    let out_mtime = fs::metadata(&shared_out).and_then(|m| m.modified()).ok();
    if shared_out.is_file()
        && let (Some(sm), Some(om)) = (src_mtime, out_mtime)
        && om >= sm
    {
        return Ok(shared_out);
    }

    let tmp_out = staging_dir.join(format!("libanneal_trace.{ext}"));
    let rustc_bin = resolve_rustc_bin();
    let out = Command::new(&rustc_bin)
        .args([
            "--edition=2024",
            "--crate-type=proc-macro",
            "--crate-name=anneal_trace",
            "-A",
            "warnings",
        ])
        .arg(&src_path)
        .arg("-o")
        .arg(&tmp_out)
        .output()
        .map_err(|e| format!("failed to compile anneal-trace proc-macro: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "compiling anneal-trace proc-macro failed:\n{}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    if let Some(parent) = shared_out.parent() {
        let _ = fs::create_dir_all(parent);
        let _ = fs::copy(&tmp_out, &shared_out);
    }
    Ok(tmp_out)
}

fn create_itree_staging_dir(label: &str, repo_root: &Path) -> Result<PathBuf, String> {
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let dir = env::temp_dir().join(format!(
        "anneal_itree_eval_{label}_{}_{stamp}",
        std::process::id()
    ));
    fs::create_dir_all(dir.join("src"))
        .map_err(|e| format!("failed to create staging dir {}: {e}", dir.display()))?;
    let anneal_trace_dir = repo_root.join("crates/anneal-trace");
    let cargo_toml = format!(
        "[package]\n\
         name = \"itree_diff_staged\"\n\
         version = \"0.1.0\"\n\
         edition = \"2024\"\n\
         publish = false\n\n\
         [lib]\n\
         path = \"src/lib.rs\"\n\n\
         [dependencies]\n\
         anneal-trace = {{ path = {:?} }}\n\n\
         [workspace]\n",
        anneal_trace_dir.display()
    );
    fs::write(dir.join("Cargo.toml"), cargo_toml)
        .map_err(|e| format!("failed to write staged Cargo.toml: {e}"))?;
    Ok(dir)
}

/// Generate `trials` deterministic input pairs `(magic, payload_len, inject_panic)`
/// for `cand`, combining `MirInputDictionary::from_rust_source(&cand.source)`
/// + `LayoutAwareByteBuilder` with boundary probes that exercise all `magic & 3`,
/// `payload_len & 3`, and threshold branches, plus one scheduled external-call
/// panic trial.
fn build_candidate_trial_inputs(
    cand: &GeneratedItreeCandidate,
    trials: usize,
    batch_seed: u64,
) -> Vec<(u32, u32, bool)> {
    let count = trials.max(1);
    let dict = MirInputDictionary::from_rust_source(&cand.source)
        .unwrap_or_else(|_| MirInputDictionary::new());
    let builder = LayoutAwareByteBuilder::new(&dict)
        .with_dictionary_bias_pct(75)
        .with_validity_fault_rate_pct(0)
        .with_padding_pattern(PaddingFillPattern::AlternatingA55A);
    let pair_layout = LayoutSpec::Tuple {
        total_size: 8,
        elements: vec![
            (0, LayoutSpec::Scalar(ScalarLayout::u32())),
            (4, LayoutSpec::Scalar(ScalarLayout::u32())),
        ],
    };

    let fixed_probes: &[(u32, u32, bool)] = &[
        (0x414E_4E4C, 2048, false),
        (0x414E_4E4C, 64, false),
        (0x0000_0010, 0x80, false),
        (0x0000_0000, 0, false),
        (0x0000_0001, 1, false),
        (0x0000_0002, 2, false),
        (0x0000_0003, 3, false),
        (0xDEAD_BEEF, 0, false),
        (0x414E_4E4C, 2048, true),
    ];

    let mut out = Vec::with_capacity(count);
    let mut rng = DetRng::new(cand.seed_u64 ^ batch_seed);
    for idx in 0..count {
        if idx < fixed_probes.len() && idx + 2 <= count {
            out.push(fixed_probes[idx]);
            continue;
        }
        let mut entropy = [0u8; 32];
        for chunk in entropy.chunks_exact_mut(8) {
            chunk.copy_from_slice(&rng.next_u64().to_le_bytes());
        }
        let mut u = Unstructured::new(&entropy);
        let raw = builder.build_bytes(&pair_layout, &mut u);
        let magic = u32::from_le_bytes([raw[0], raw[1], raw[2], raw[3]]);
        let payload_len = u32::from_le_bytes([raw[4], raw[5], raw[6], raw[7]]);
        out.push((magic, payload_len, false));
    }
    out
}

fn render_trace_collector_source(
    repo_root: &Path,
    staged_candidates: &[(StagedItreeCandidate, Vec<(u32, u32, bool)>)],
) -> String {
    let trace_observer_path = repo_root.join("crates/cargo-anneal/src/trace_observer.rs");
    let mut out = String::new();
    let _ = writeln!(
        out,
        "#![allow(dead_code, non_snake_case, non_camel_case_types, unused_imports, unexpected_cfgs)]"
    );
    let _ = writeln!(out, "extern crate self as cargo_anneal;");
    let _ = writeln!(
        out,
        "#[path = {:?}]\npub mod trace_observer;",
        trace_observer_path.display()
    );
    let _ = writeln!(
        out,
        "pub mod itree_diff_staged {{\n    include!(\"src/candidates.rs\");\n}}\n"
    );
    let _ = writeln!(
        out,
        "use trace_observer::{{EnvSchedule, TraceRecorder, encode_recorded_raw_trace_hex, value_as_raw_bytes}};\n"
    );
    let _ = writeln!(out, "fn main() {{");

    for (staged, trials) in staged_candidates {
        let fn_ident = &staged.root_fn_name;
        let def_path = format!("itree_diff_staged::{fn_ident}");
        for &(magic, payload_len, inject_panic) in trials {
            let rec_expr = if inject_panic {
                "TraceRecorder::with_schedule(EnvSchedule::new().with_panic_on_call(0))"
            } else {
                "TraceRecorder::new()"
            };
            let _ = writeln!(
                out,
                "    {{\n\
                 \x20       let a0: u32 = {magic}u32;\n\
                 \x20       let a1: u32 = {payload_len}u32;\n\
                 \x20       let (_res, trace, _rec) = TraceRecorder::observe_root_with_recorder(\n\
                 \x20           {rec_expr},\n\
                 \x20           \"{def_path}\",\n\
                 \x20           vec![value_as_raw_bytes(&a0), value_as_raw_bytes(&a1)],\n\
                 \x20           |_rec| itree_diff_staged::{fn_ident}(a0, a1),\n\
                 \x20       );\n\
                 \x20       println!(\"ANNEAL_TRACE_HEX:{fn_ident}:{{}}\", encode_recorded_raw_trace_hex(&trace));\n\
                 \x20   }}"
            );
        }
    }

    let _ = writeln!(out, "}}");
    out
}

fn collect_traces_natively(
    repo_root: &Path,
    staging_dir: &Path,
    staged_candidates: &[(StagedItreeCandidate, Vec<(u32, u32, bool)>)],
) -> Result<BTreeMap<String, Vec<RecordedRawTrace>>, String> {
    let proc_macro_dylib = build_anneal_trace_proc_macro_dylib(repo_root, staging_dir)?;
    let collector_src = render_trace_collector_source(repo_root, staged_candidates);
    let collector_rs = staging_dir.join("collect_traces.rs");
    let collector_bin = staging_dir.join("collect_traces_bin");
    fs::write(&collector_rs, &collector_src)
        .map_err(|e| format!("failed to write {}: {e}", collector_rs.display()))?;

    let rustc_bin = resolve_rustc_bin();
    let extern_arg = format!("anneal_trace={}", proc_macro_dylib.display());
    let compile_out = Command::new(&rustc_bin)
        .args([
            "--edition=2024",
            "--cfg",
            "anneal_trace_ext",
            "-A",
            "warnings",
            "--extern",
            &extern_arg,
        ])
        .arg(&collector_rs)
        .arg("-o")
        .arg(&collector_bin)
        .current_dir(staging_dir)
        .output()
        .map_err(|e| format!("failed to invoke rustc for trace collector: {e}"))?;
    if !compile_out.status.success() {
        return Err(format!(
            "compiling collect_traces.rs failed:\n{}",
            String::from_utf8_lossy(&compile_out.stderr)
        ));
    }

    let run_out = Command::new(&collector_bin)
        .current_dir(staging_dir)
        .output()
        .map_err(|e| format!("failed to execute trace collector binary: {e}"))?;
    if !run_out.status.success() {
        return Err(format!(
            "running collect_traces_bin failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&run_out.stdout),
            String::from_utf8_lossy(&run_out.stderr)
        ));
    }

    const PREFIX: &str = "ANNEAL_TRACE_HEX:";
    let mut by_fn: BTreeMap<String, Vec<RecordedRawTrace>> = BTreeMap::new();
    for line in String::from_utf8_lossy(&run_out.stdout).lines() {
        let trimmed = line.trim();
        let Some(rest) = trimmed.strip_prefix(PREFIX) else {
            continue;
        };
        let Some((fn_name, hex_line)) = rest.split_once(':') else {
            continue;
        };
        let trace = decode_recorded_raw_trace_hex(hex_line)?;
        by_fn.entry(fn_name.to_string()).or_default().push(trace);
    }
    Ok(by_fn)
}

fn extract_mir_neighborhood(staging_dir: &Path, mir_module: &str) -> (String, String) {
    let rel_path = mir_module.replace('.', "/") + ".lean";
    let mir_path = staging_dir.join(".anneal/generated").join(&rel_path);
    let Ok(full) = fs::read_to_string(&mir_path) else {
        let msg = format!("(Mir module {} not found)", mir_path.display());
        return (msg.clone(), msg);
    };
    let lines: Vec<&str> = full.lines().collect();
    let max_lines = 80usize;
    let neighborhood = if lines.len() <= max_lines {
        full.clone()
    } else {
        let mut snippet = lines[..max_lines].join("\n");
        snippet.push_str(&format!(
            "\n-- ... ({} additional lines in {}) ...\n",
            lines.len() - max_lines,
            mir_path.display()
        ));
        snippet
    };
    (neighborhood, full)
}

fn extract_itree_confirm_theorem(confirm_src: &str, case_ident: &str) -> String {
    let diag_header = format!("theorem {case_ident}_diag_tag :");
    let sound_header = format!("theorem {case_ident}_trace_consistent :");
    let mut blocks = Vec::new();
    for header in [&sound_header, &diag_header] {
        if let Some(start_idx) = confirm_src.find(header) {
            let rest = &confirm_src[start_idx..];
            let end_rel = rest.find("\n\n").map(|i| i + 1).unwrap_or(rest.len());
            blocks.push(rest[..end_rel].trim().to_string());
        }
    }
    blocks.join("\n\n")
}

fn write_itree_finding_bundle_to_dir(
    findings_dir: &Path,
    finding: &mut ItreeFindingBundle,
) -> Result<(), String> {
    let bundle_dir = findings_dir.join(&finding.finding_id);
    fs::create_dir_all(&bundle_dir)
        .map_err(|e| format!("failed to create finding dir {}: {e}", bundle_dir.display()))?;
    let repro_path = bundle_dir.join("repro.rs");
    fs::write(&repro_path, &finding.candidate_source)
        .map_err(|e| format!("failed to write {}: {e}", repro_path.display()))?;
    finding.repro_path = Some(repro_path.clone());

    fs::write(bundle_dir.join("repro_trace.txt"), format!("{}\n", finding.trace_hex))
        .map_err(|e| format!("failed to write repro_trace.txt in {}: {e}", bundle_dir.display()))?;
    fs::write(bundle_dir.join("repro_mir.lean"), &finding.checked_mir_source)
        .map_err(|e| format!("failed to write repro_mir.lean in {}: {e}", bundle_dir.display()))?;

    let finding_json = render_itree_finding_bundle_json(finding, 0);
    fs::write(bundle_dir.join("finding.json"), format!("{finding_json}\n"))
        .map_err(|e| format!("failed to write finding.json in {}: {e}", bundle_dir.display()))?;

    let summary_md = format!(
        "# ITree Divergence Finding `{}`\n\n\
         - **Candidate function**: `{}`\n\
         - **Seed index**: `{}`\n\
         - **Applied mutators**: `{}`\n\
         - **Lean `TraceReplayDiag` tag**: `{}`\n\
         - **Lean `TraceReplayDiag` repr**: `{}`\n\
         - **Checked MIR module**: `{}`\n\
         - **Lean 4 kernel confirmed (`by rfl`)**: `{}`\n\
         - **Standalone reproducer**: `{}`\n\n\
         ## Lean 4 Kernel Confirmation Theorem (`ItreeDiffBatchConfirm.lean`)\n\n\
         ```lean\n{}\n```\n\n\
         ## Captured MIR Neighborhood (`.anneal/generated/Mir`)\n\n\
         ```lean\n{}\n```\n\n\
         ## Candidate Source (`repro.rs`)\n\n\
         ```rust\n{}\n```\n",
        finding.finding_id,
        finding.fn_name,
        finding.seed_index,
        if finding.applied_mutators.is_empty() {
            "identity (none)".to_string()
        } else {
            finding.applied_mutators.join(", ")
        },
        finding.diag_tag,
        finding.diag_repr,
        finding.checked_mir_module,
        finding.kernel_confirmed,
        repro_path.display(),
        finding.kernel_confirm_theorem,
        finding.mir_neighborhood.trim_end(),
        finding.candidate_source.trim_end(),
    );
    fs::write(bundle_dir.join("SUMMARY.md"), summary_md)
        .map_err(|e| format!("failed to write SUMMARY.md in {}: {e}", bundle_dir.display()))?;
    Ok(())
}

/// Evaluates `batches` of safe-Rust ITree candidates through `compile_itree_candidates`,
/// unmodified `#![no_std]` MIR extraction (`run_cargo_capture` +
/// `scaffold_workspace_with_config`), native boundary-interposed execution
/// (`#[anneal_trace::external]`), trace deduplication, and batched Lean 4
/// `TraceCheck` verification (`ItreeDiffBatchProbe.lean` +
/// `ItreeDiffBatchConfirm.lean`).
pub fn evaluate_itree_batches(
    mode: &str,
    seed: u64,
    batches: &[Vec<GeneratedItreeCandidate>],
    batch_size: usize,
    findings_dir: Option<&Path>,
    anneal_repo_root: Option<&Path>,
) -> Result<ItreeCampaignEvalReport, String> {
    let options = ItreeEvalOptions {
        trials_per_candidate: DEFAULT_ITREE_TRIALS_PER_CANDIDATE,
        anneal_repo_root: anneal_repo_root.map(Path::to_path_buf),
        findings_dir: findings_dir.map(Path::to_path_buf),
        mir_mutations: Vec::new(),
        root_mir_swaps: Vec::new(),
    };
    evaluate_itree_batches_with_options(mode, seed, batches, batch_size, &options)
}

/// Evaluates `batches` with explicit [`ItreeEvalOptions`] (including trial
/// counts and optional negative-control MIR mutation / root-swap hooks).
pub fn evaluate_itree_batches_with_options(
    mode: &str,
    seed: u64,
    batches: &[Vec<GeneratedItreeCandidate>],
    batch_size: usize,
    options: &ItreeEvalOptions,
) -> Result<ItreeCampaignEvalReport, String> {
    let start = Instant::now();
    let repo_root = options
        .anneal_repo_root
        .clone()
        .unwrap_or_else(default_repo_root);

    let total_candidates: usize = batches.iter().map(Vec::len).sum();
    let unsafe_token_violations = batches
        .iter()
        .flatten()
        .filter(|cand| contains_unsafe_token(&cand.source))
        .count();

    let compile_results = compile_itree_candidates(batches);
    let flat_compile: Vec<CandidateCompile> = compile_results.iter().flatten().copied().collect();
    let opt_level_0_compiled = flat_compile.iter().filter(|c| c.opt0).count();
    let opt_level_2_compiled = flat_compile.iter().filter(|c| c.opt2).count();
    let opt_level_0_and_2_compiled = flat_compile.iter().filter(|c| c.opt0 && c.opt2).count();
    let instrumented_compiled = flat_compile.iter().filter(|c| c.instrumented).count();
    let compile_pass_rate_pct = if total_candidates == 0 {
        0.0
    } else {
        (opt_level_0_and_2_compiled as f64 / total_candidates as f64) * 100.0
    };

    let mut mutator_applications: BTreeMap<String, usize> = ITREE_MUTATOR_NAMES
        .iter()
        .map(|m| (m.to_string(), 0))
        .collect();
    for cand in batches.iter().flatten() {
        for m in &cand.applied_mutators {
            *mutator_applications.entry(m.clone()).or_insert(0) += 1;
        }
    }

    let mut diag_tag_counts: BTreeMap<String, usize> = ITREE_DIAG_TAG_NAMES
        .iter()
        .map(|k| (k.to_string(), 0))
        .collect();

    if opt_level_0_and_2_compiled == 0 {
        return Err(format!(
            "cannot perform ITree oracle comparison: 0 of {total_candidates} candidates compiled"
        ));
    }

    let staging_dir = create_itree_staging_dir(mode, &repo_root)?;
    let eval_res = (|| -> Result<ItreeCampaignEvalReport, String> {
        let mut combined_candidates_rs = String::new();
        let mut staged_with_trials: Vec<(StagedItreeCandidate, Vec<(u32, u32, bool)>)> =
            Vec::with_capacity(opt_level_0_and_2_compiled);
        let mut cand_meta: BTreeMap<String, (&GeneratedItreeCandidate, StagedItreeCandidate)> =
            BTreeMap::new();

        for (b_idx, batch) in batches.iter().enumerate() {
            for (c_idx, cand) in batch.iter().enumerate() {
                let comp = compile_results[b_idx][c_idx];
                if !(comp.opt0 && comp.opt2) || contains_unsafe_token(&cand.source) {
                    continue;
                }
                let prefix = format!("b{b_idx}_c{c_idx}__");
                let staged = stage_itree_candidate_items(&cand.source, &prefix, "kernel_step")?;
                combined_candidates_rs.push_str(&staged.staged_source);
                combined_candidates_rs.push('\n');
                let trials =
                    build_candidate_trial_inputs(cand, options.trials_per_candidate, seed);
                cand_meta.insert(staged.root_fn_name.clone(), (cand, staged.clone()));
                staged_with_trials.push((staged, trials));
            }
        }

        fs::write(staging_dir.join("src/candidates.rs"), &combined_candidates_rs)
            .map_err(|e| format!("failed to write staged src/candidates.rs: {e}"))?;
        fs::write(
            staging_dir.join("src/lib.rs"),
            "#![no_std]\n#![allow(dead_code, non_snake_case, non_camel_case_types, unexpected_cfgs)]\ninclude!(\"candidates.rs\");\n",
        )
        .map_err(|e| format!("failed to write staged src/lib.rs: {e}"))?;

        let wrapper_bin = ensure_rustc_capture_bin(&repo_root)?;
        let units_dir = staging_dir.join("target/anneal/units");
        let mut capture_cfg = CaptureDriverConfig::new(&staging_dir);
        capture_cfg.units_dir = units_dir.clone();
        capture_cfg.rustc_wrapper = Some(wrapper_bin);
        let (_manifest, records) = run_cargo_capture(&capture_cfg)
            .map_err(|e| format!("run_cargo_capture failed on staged ITree crate: {e}"))?;

        let mut scaffold_cfg = ScaffoldConfig::new(&staging_dir);
        scaffold_cfg.units_dir = Some(units_dir);
        scaffold_cfg.anneal_repo_root = Some(repo_root.clone());
        scaffold_cfg.init_spec_templates = false;
        scaffold_cfg.init_proof_templates = false;
        scaffold_workspace_with_config(&scaffold_cfg, &records)
            .map_err(|e| format!("scaffold_workspace_with_config failed: {e}"))?;

        // Apply any negative-control MIR mutations requested by the caller.
        let mir_dir = staging_dir
            .join(".anneal/generated/Mir")
            .join("ItreeDiffStaged");
        for (target_fn, from_s, to_s) in &options.mir_mutations {
            let mir_file = mir_dir.join(format!("{target_fn}.lean"));
            let orig = fs::read_to_string(&mir_file)
                .map_err(|e| format!("failed to read {}: {e}", mir_file.display()))?;
            let mutated = orig.replace(from_s, to_s);
            if orig == mutated {
                return Err(format!(
                    "MIR mutation pattern `{from_s}` not found in {}",
                    mir_file.display()
                ));
            }
            fs::write(&mir_file, mutated)
                .map_err(|e| format!("failed to write mutated {}: {e}", mir_file.display()))?;
        }

        let swap_map: BTreeMap<String, String> =
            options.root_mir_swaps.iter().cloned().collect();

        // Execute all compiled candidates natively with boundary interposition.
        let traces_by_fn =
            collect_traces_natively(&repo_root, &staging_dir, &staged_with_trials)?;

        let mut total_traces_executed = 0usize;
        let mut obs_path_set = MirObsPathSet::new();
        let mut per_candidate_distinct_traces: BTreeMap<String, usize> = BTreeMap::new();
        let mut batch_cases: Vec<BatchTraceEvalCase> = Vec::new();
        let mut case_to_fn: BTreeMap<String, String> = BTreeMap::new();

        for (staged, _trials) in &staged_with_trials {
            let fn_name = &staged.root_fn_name;
            let raw_traces = traces_by_fn.get(fn_name).cloned().unwrap_or_default();
            total_traces_executed += raw_traces.len();

            for tr in &raw_traces {
                let mut call_seq = Vec::new();
                for (idx, ev) in tr.events.iter().enumerate() {
                    match ev {
                        RecordedEvent::ExtCall { def_path, .. }
                        | RecordedEvent::ExtCallPanic { def_path, .. }
                        | RecordedEvent::ExtCallAbort { def_path, .. } => {
                            call_seq.push((def_path.clone(), idx));
                        }
                        RecordedEvent::Branch { .. } => {}
                    }
                }
                let is_panic = matches!(tr.outcome, RecordedOutcome::Panic);
                obs_path_set.record_execution(
                    crate::input_gen::MirObsPathKey {
                        fn_name: fn_name.clone(),
                        branch_tags: Vec::new(),
                        ext_call_sequence_shape: call_seq,
                        is_panic,
                    },
                    tr.raw_args.iter().flatten().copied().collect(),
                );
            }

            // Deduplicate distinct traces per candidate by observable (events, outcome).
            let mut seen_keys: BTreeSet<String> = BTreeSet::new();
            let mut distinct_for_cand: Vec<RecordedRawTrace> = Vec::new();
            for tr in raw_traces {
                let mut sig_trace = tr.clone();
                sig_trace.raw_args.clear();
                let key = encode_recorded_raw_trace_hex(&sig_trace);
                if seen_keys.insert(key) {
                    distinct_for_cand.push(tr);
                }
            }
            per_candidate_distinct_traces.insert(fn_name.clone(), distinct_for_cand.len());

            let default_root_mir = format!("Mir.ItreeDiffStaged.{fn_name}");
            let root_mir_module = swap_map
                .get(fn_name)
                .cloned()
                .unwrap_or(default_root_mir);
            let callee_sig_modules: Vec<String> = staged
                .ext_callee_names
                .iter()
                .map(|c| format!("Mir.ItreeDiffStaged.{c}"))
                .collect();

            for (t_idx, trace) in distinct_for_cand.into_iter().enumerate() {
                let case_ident = format!("case_{fn_name}_t{t_idx}");
                case_to_fn.insert(case_ident.clone(), fn_name.clone());
                batch_cases.push(BatchTraceEvalCase {
                    case_ident,
                    config: TraceCheckModuleConfig {
                        module_namespace: "Proof.ItreeDiffBatchConfirm".to_string(),
                        root_mir_module: root_mir_module.clone(),
                        callee_sig_modules: callee_sig_modules.clone(),
                        inlined_callee_modules: Vec::new(),
                        init_mem_expr: None,
                        fuel: ITREE_TRACE_CHECK_FUEL,
                        check_branches: false,
                    },
                    trace,
                    expected_diag_tag: None,
                    tampered_outcome: None,
                });
            }
        }

        let distinct_traces_checked = batch_cases.len();
        if distinct_traces_checked == 0 {
            return Err("native trace collection produced 0 traces".to_string());
        }

        // Build Anneal + all referenced Mir modules once via `lake build`.
        let anneal_dir = staging_dir.join(".anneal");
        let mut lake_targets: Vec<String> = vec!["Anneal".to_string()];
        for case in &batch_cases {
            if !lake_targets.contains(&case.config.root_mir_module) {
                lake_targets.push(case.config.root_mir_module.clone());
            }
            for m in &case.config.callee_sig_modules {
                if !lake_targets.contains(m) {
                    lake_targets.push(m.clone());
                }
            }
        }
        run_lake_verify_targets(&anneal_dir, &lake_targets)?;

        let verify_dir = anneal_dir.join("generated/Verify/ItreeDiffStaged");
        fs::create_dir_all(&verify_dir)
            .map_err(|e| format!("failed to create {}: {e}", verify_dir.display()))?;

        // Stage 1: Probe `diagnoseRawByteTraceObsErasedBounded` across all distinct traces.
        let probe_src =
            render_batch_trace_probe_lean_module("Proof.ItreeDiffBatchProbe", &batch_cases);
        let probe_file = verify_dir.join("ItreeDiffBatchProbe.lean");
        fs::write(&probe_file, &probe_src)
            .map_err(|e| format!("failed to write {}: {e}", probe_file.display()))?;

        let probe_out = Command::new("lake")
            .args(["env", "lean", "-M", "4096"])
            .arg(&probe_file)
            .current_dir(&anneal_dir)
            .output()
            .map_err(|e| format!("failed to run `lake env lean` on probe module: {e}"))?;
        if !probe_out.status.success() {
            return Err(format!(
                "`ItreeDiffBatchProbe.lean` failed ({}):\nstdout:\n{}\nstderr:\n{}",
                probe_out.status,
                String::from_utf8_lossy(&probe_out.stdout),
                String::from_utf8_lossy(&probe_out.stderr)
            ));
        }

        let probe_map =
            parse_batch_trace_probe_output(&String::from_utf8_lossy(&probe_out.stdout));
        for case in &mut batch_cases {
            let (tag, _repr) = probe_map
                .get(&case.case_ident)
                .ok_or_else(|| format!("missing probe output for `{}`", case.case_ident))?;
            case.expected_diag_tag = Some(tag.clone());
        }

        // Stage 2: Kernel-confirm every trace's `TraceReplayDiag.tagName` (`by rfl`)
        // and `checkRawByteTraceObsErasedBounded_sound` for `"ok"` traces.
        let confirm_src = render_batch_trace_eval_lean_module(
            "Proof.ItreeDiffBatchConfirm",
            &batch_cases,
            false,
        );
        let confirm_file = verify_dir.join("ItreeDiffBatchConfirm.lean");
        fs::write(&confirm_file, &confirm_src)
            .map_err(|e| format!("failed to write {}: {e}", confirm_file.display()))?;

        let confirm_out = Command::new("lake")
            .args(["env", "lean", "-M", "4096"])
            .arg(&confirm_file)
            .current_dir(&anneal_dir)
            .output()
            .map_err(|e| format!("failed to run `lake env lean` on confirm module: {e}"))?;
        let kernel_confirmed_all = confirm_out.status.success();
        if !kernel_confirmed_all {
            return Err(format!(
                "`ItreeDiffBatchConfirm.lean` failed kernel confirmation ({}):\nstdout:\n{}\nstderr:\n{}",
                confirm_out.status,
                String::from_utf8_lossy(&confirm_out.stdout),
                String::from_utf8_lossy(&confirm_out.stderr)
            ));
        }

        let mut agree_traces = 0usize;
        let mut diverge_traces = 0usize;
        let mut kernel_confirmed_traces = 0usize;
        let mut kernel_confirmed_divergences = 0usize;
        let mut diverged_fn_names: BTreeSet<String> = BTreeSet::new();
        let mut findings: Vec<ItreeFindingBundle> = Vec::new();

        for case in &batch_cases {
            let (tag, diag_repr) = probe_map
                .get(&case.case_ident)
                .cloned()
                .unwrap_or_else(|| ("unknown".to_string(), String::new()));
            *diag_tag_counts.entry(tag.clone()).or_insert(0) += 1;
            if kernel_confirmed_all {
                kernel_confirmed_traces += 1;
            }
            let fn_name = case_to_fn
                .get(&case.case_ident)
                .cloned()
                .unwrap_or_default();

            if tag == "ok" {
                agree_traces += 1;
            } else {
                diverge_traces += 1;
                if kernel_confirmed_all {
                    kernel_confirmed_divergences += 1;
                }
                diverged_fn_names.insert(fn_name.clone());

                if let Some((cand, _staged)) = cand_meta.get(&fn_name) {
                    let (mir_neighborhood, checked_mir_source) =
                        extract_mir_neighborhood(&staging_dir, &case.config.root_mir_module);
                    let kernel_confirm_theorem =
                        extract_itree_confirm_theorem(&confirm_src, &case.case_ident);
                    let finding_id = format!("finding_{:04}_{}", findings.len(), case.case_ident);
                    let mut bundle = ItreeFindingBundle {
                        finding_id,
                        fn_name: fn_name.clone(),
                        case_ident: case.case_ident.clone(),
                        seed_index: cand.seed_index,
                        applied_mutators: cand.applied_mutators.clone(),
                        diag_tag: tag,
                        diag_repr,
                        trace_hex: encode_recorded_raw_trace_hex(&case.trace),
                        kernel_confirmed: kernel_confirmed_all,
                        kernel_confirm_theorem,
                        mir_neighborhood,
                        checked_mir_source,
                        checked_mir_module: case.config.root_mir_module.clone(),
                        candidate_source: cand.source.clone(),
                        repro_path: None,
                    };
                    if let Some(ref dir) = options.findings_dir {
                        write_itree_finding_bundle_to_dir(dir, &mut bundle)?;
                    }
                    findings.push(bundle);
                }
            }
        }

        let compared_candidates = staged_with_trials.len();
        let diverge_candidates = diverged_fn_names.len();
        let agree_candidates = compared_candidates.saturating_sub(diverge_candidates);
        let not_compared_candidates = total_candidates.saturating_sub(compared_candidates);
        let elapsed_ms = start.elapsed().as_secs_f64() * 1000.0;

        Ok(ItreeCampaignEvalReport {
            mode: mode.to_string(),
            seed,
            batches: batches.len(),
            batch_size,
            trials_per_candidate: options.trials_per_candidate,
            total_candidates,
            unsafe_token_violations,
            opt_level_0_compiled,
            opt_level_2_compiled,
            opt_level_0_and_2_compiled,
            instrumented_compiled,
            compile_pass_rate_pct,
            compared_candidates,
            agree_candidates,
            diverge_candidates,
            not_compared_candidates,
            total_traces_executed,
            distinct_traces_checked,
            agree_traces,
            diverge_traces,
            kernel_confirmed_traces,
            kernel_confirmed_divergences,
            distinct_obs_paths: obs_path_set.len(),
            per_candidate_distinct_traces,
            diag_tag_counts,
            mutator_applications,
            findings,
            elapsed_ms,
        })
    })();

    let _ = fs::remove_dir_all(&staging_dir);
    eval_res
}

/// Re-runs a standalone ITree finding bundle (or `repro.rs` inside a finding
/// bundle directory) through `run_cargo_capture`, `scaffold_workspace_with_config`,
/// and Lean `TraceCheck`, confirming that the recorded divergence reproduces
/// with `kernel_confirmed = true`.
pub fn reproduce_itree_finding(
    repro_path: &Path,
    anneal_repo_root: Option<&Path>,
) -> Result<ItreeReproReport, String> {
    let repo_root = anneal_repo_root
        .map(Path::to_path_buf)
        .unwrap_or_else(default_repo_root);
    let (bundle_dir, repro_rs_path) = if repro_path.is_dir() {
        (repro_path.to_path_buf(), repro_path.join("repro.rs"))
    } else {
        let dir = repro_path
            .parent()
            .ok_or_else(|| format!("invalid reproducer path {}", repro_path.display()))?
            .to_path_buf();
        (dir, repro_path.to_path_buf())
    };

    let cand_source = fs::read_to_string(&repro_rs_path)
        .map_err(|e| format!("failed to read {}: {e}", repro_rs_path.display()))?;
    let trace_hex_path = bundle_dir.join("repro_trace.txt");
    let trace_hex = fs::read_to_string(&trace_hex_path)
        .map_err(|e| format!("failed to read {}: {e}", trace_hex_path.display()))?;
    let trace = decode_recorded_raw_trace_hex(trace_hex.trim())?;

    let prefix = trace
        .root_def_path
        .strip_prefix("itree_diff_staged::")
        .and_then(|s| s.strip_suffix("kernel_step"))
        .unwrap_or("repro__");
    let staged = stage_itree_candidate_items(&cand_source, prefix, "kernel_step")?;

    let staging_dir = create_itree_staging_dir("repro", &repo_root)?;
    let res = (|| -> Result<ItreeReproReport, String> {
        let candidates_rs = format!("{}\n", staged.staged_source);
        fs::write(staging_dir.join("src/candidates.rs"), candidates_rs)
            .map_err(|e| format!("failed to write staged candidates.rs: {e}"))?;
        fs::write(
            staging_dir.join("src/lib.rs"),
            "#![no_std]\n#![allow(dead_code, non_snake_case, non_camel_case_types, unexpected_cfgs)]\ninclude!(\"candidates.rs\");\n",
        )
        .map_err(|e| format!("failed to write staged lib.rs: {e}"))?;

        let wrapper_bin = ensure_rustc_capture_bin(&repo_root)?;
        let units_dir = staging_dir.join("target/anneal/units");
        let mut capture_cfg = CaptureDriverConfig::new(&staging_dir);
        capture_cfg.units_dir = units_dir.clone();
        capture_cfg.rustc_wrapper = Some(wrapper_bin);
        let (_manifest, records) = run_cargo_capture(&capture_cfg)?;

        let mut scaffold_cfg = ScaffoldConfig::new(&staging_dir);
        scaffold_cfg.units_dir = Some(units_dir);
        scaffold_cfg.anneal_repo_root = Some(repo_root.clone());
        scaffold_cfg.init_spec_templates = false;
        scaffold_cfg.init_proof_templates = false;
        scaffold_workspace_with_config(&scaffold_cfg, &records)?;

        let root_mir_module = format!("Mir.ItreeDiffStaged.{}", staged.root_fn_name);
        let repro_mir_path = bundle_dir.join("repro_mir.lean");
        if repro_mir_path.is_file() {
            let override_mir = fs::read_to_string(&repro_mir_path)
                .map_err(|e| format!("failed to read {}: {e}", repro_mir_path.display()))?;
            // Normalize the namespace in `repro_mir.lean` to `root_mir_module` in case
            // the finding came from a root-swap check.
            let target_mir_file = staging_dir
                .join(".anneal/generated/Mir/ItreeDiffStaged")
                .join(format!("{}.lean", staged.root_fn_name));
            let normalized = normalize_mir_namespace(&override_mir, &root_mir_module);
            fs::write(&target_mir_file, normalized)
                .map_err(|e| format!("failed to write {}: {e}", target_mir_file.display()))?;
        }

        let callee_sig_modules: Vec<String> = staged
            .ext_callee_names
            .iter()
            .map(|c| format!("Mir.ItreeDiffStaged.{c}"))
            .collect();
        let mut case = BatchTraceEvalCase {
            case_ident: "repro_case".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffRepro".to_string(),
                root_mir_module: root_mir_module.clone(),
                callee_sig_modules: callee_sig_modules.clone(),
                inlined_callee_modules: Vec::new(),
                init_mem_expr: None,
                fuel: ITREE_TRACE_CHECK_FUEL,
                check_branches: false,
            },
            trace,
            expected_diag_tag: None,
            tampered_outcome: None,
        };

        let anneal_dir = staging_dir.join(".anneal");
        let mut lake_targets = vec!["Anneal".to_string(), root_mir_module];
        lake_targets.extend(callee_sig_modules);
        run_lake_verify_targets(&anneal_dir, &lake_targets)?;

        let verify_dir = anneal_dir.join("generated/Verify/ItreeDiffStaged");
        fs::create_dir_all(&verify_dir)
            .map_err(|e| format!("failed to create {}: {e}", verify_dir.display()))?;

        let probe_src = render_batch_trace_probe_lean_module(
            "Proof.ItreeDiffReproProbe",
            std::slice::from_ref(&case),
        );
        let probe_file = verify_dir.join("ItreeDiffReproProbe.lean");
        fs::write(&probe_file, &probe_src)
            .map_err(|e| format!("failed to write {}: {e}", probe_file.display()))?;
        let probe_out = Command::new("lake")
            .args(["env", "lean", "-M", "4096"])
            .arg(&probe_file)
            .current_dir(&anneal_dir)
            .output()
            .map_err(|e| format!("failed to run probe in repro: {e}"))?;
        if !probe_out.status.success() {
            return Err(format!(
                "repro probe failed:\n{}",
                String::from_utf8_lossy(&probe_out.stderr)
            ));
        }
        let probe_map =
            parse_batch_trace_probe_output(&String::from_utf8_lossy(&probe_out.stdout));
        let (diag_tag, diag_repr) = probe_map
            .get("repro_case")
            .cloned()
            .ok_or_else(|| "missing repro_case in probe output".to_string())?;
        case.expected_diag_tag = Some(diag_tag.clone());

        let confirm_src = render_batch_trace_eval_lean_module(
            "Proof.ItreeDiffRepro",
            std::slice::from_ref(&case),
            false,
        );
        let confirm_file = verify_dir.join("ItreeDiffRepro.lean");
        fs::write(&confirm_file, &confirm_src)
            .map_err(|e| format!("failed to write {}: {e}", confirm_file.display()))?;
        let confirm_out = Command::new("lake")
            .args(["env", "lean", "-M", "4096"])
            .arg(&confirm_file)
            .current_dir(&anneal_dir)
            .output()
            .map_err(|e| format!("failed to run confirm in repro: {e}"))?;
        let kernel_confirmed = confirm_out.status.success();
        let verdict = if diag_tag == "ok" {
            "agree".to_string()
        } else {
            "diverge".to_string()
        };

        Ok(ItreeReproReport {
            fn_name: staged.root_fn_name,
            verdict,
            diag_tag,
            diag_repr,
            kernel_confirmed,
        })
    })();

    let _ = fs::remove_dir_all(&staging_dir);
    res
}

fn normalize_mir_namespace(mir_src: &str, target_module: &str) -> String {
    let mut lines = Vec::new();
    for line in mir_src.lines() {
        if line.starts_with("namespace Mir.") {
            lines.push(format!("namespace {target_module}"));
        } else if line.starts_with("end Mir.") {
            lines.push(format!("end {target_module}"));
        } else {
            lines.push(line.to_string());
        }
    }
    lines.join("\n") + "\n"
}

fn render_usize_map_json(map: &BTreeMap<String, usize>, indent: usize) -> String {
    let pad = " ".repeat(indent);
    let inner_pad = " ".repeat(indent + 2);
    if map.is_empty() {
        return "{}".to_string();
    }
    let rows: Vec<String> = map
        .iter()
        .map(|(k, v)| format!("{inner_pad}{}: {v}", json_escape(k)))
        .collect();
    format!("{{\n{}\n{pad}}}", rows.join(",\n"))
}

/// Render an [`ItreeFindingBundle`] as a JSON object at indentation `indent`.
pub fn render_itree_finding_bundle_json(finding: &ItreeFindingBundle, indent: usize) -> String {
    let pad = " ".repeat(indent);
    let inner = " ".repeat(indent + 2);
    let mutators_json = finding
        .applied_mutators
        .iter()
        .map(|m| json_escape(m))
        .collect::<Vec<_>>()
        .join(", ");
    let repro_path_json = finding
        .repro_path
        .as_ref()
        .map(|p| json_escape(&p.to_string_lossy()))
        .unwrap_or_else(|| "null".to_string());

    format!(
        "{pad}{{\n\
         {inner}\"finding_id\": {},\n\
         {inner}\"fn_name\": {},\n\
         {inner}\"case_ident\": {},\n\
         {inner}\"seed_index\": {},\n\
         {inner}\"applied_mutators\": [{mutators_json}],\n\
         {inner}\"diag_tag\": {},\n\
         {inner}\"diag_repr\": {},\n\
         {inner}\"trace_hex\": {},\n\
         {inner}\"checked_mir_module\": {},\n\
         {inner}\"mir_neighborhood\": {},\n\
         {inner}\"kernel_confirmed\": {},\n\
         {inner}\"kernel_confirm_theorem\": {},\n\
         {inner}\"candidate_source\": {},\n\
         {inner}\"repro_path\": {repro_path_json}\n\
         {pad}}}",
        json_escape(&finding.finding_id),
        json_escape(&finding.fn_name),
        json_escape(&finding.case_ident),
        finding.seed_index,
        json_escape(&finding.diag_tag),
        json_escape(&finding.diag_repr),
        json_escape(&finding.trace_hex),
        json_escape(&finding.checked_mir_module),
        json_escape(&finding.mir_neighborhood),
        finding.kernel_confirmed,
        json_escape(&finding.kernel_confirm_theorem),
        json_escape(&finding.candidate_source),
    )
}

/// Render the full JSON report for a completed [`ItreeCampaignEvalReport`].
pub fn render_itree_eval_report_json(report: &ItreeCampaignEvalReport) -> String {
    let findings_json = if report.findings.is_empty() {
        "[]".to_string()
    } else {
        let items: Vec<String> = report
            .findings
            .iter()
            .map(|f| render_itree_finding_bundle_json(f, 4))
            .collect();
        format!("[\n{}\n  ]", items.join(",\n"))
    };

    format!(
        "{{\n\
         \x20 \"harness\": \"itree-difftest\",\n\
         \x20 \"oracle_comparison\": \"performed\",\n\
         \x20 \"mode\": {},\n\
         \x20 \"seed\": \"0x{:08x}\",\n\
         \x20 \"batches\": {},\n\
         \x20 \"batch_size\": {},\n\
         \x20 \"trials_per_candidate\": {},\n\
         \x20 \"total_candidates\": {},\n\
         \x20 \"unsafe_token_violations\": {},\n\
         \x20 \"opt_level_0_compiled\": {},\n\
         \x20 \"opt_level_2_compiled\": {},\n\
         \x20 \"opt_level_0_and_2_compiled\": {},\n\
         \x20 \"instrumented_compiled\": {},\n\
         \x20 \"compile_pass_rate_pct\": {:.2},\n\
         \x20 \"compared_candidates\": {},\n\
         \x20 \"agree_candidates\": {},\n\
         \x20 \"diverge_candidates\": {},\n\
         \x20 \"not_compared_candidates\": {},\n\
         \x20 \"total_traces_executed\": {},\n\
         \x20 \"distinct_traces_checked\": {},\n\
         \x20 \"agree_traces\": {},\n\
         \x20 \"diverge_traces\": {},\n\
         \x20 \"kernel_confirmed_traces\": {},\n\
         \x20 \"kernel_confirmed_divergences\": {},\n\
         \x20 \"distinct_obs_paths\": {},\n\
         \x20 \"per_candidate_distinct_traces\": {},\n\
         \x20 \"diag_tag_counts\": {},\n\
         \x20 \"mutator_applications\": {},\n\
         \x20 \"findings_count\": {},\n\
         \x20 \"findings\": {findings_json},\n\
         \x20 \"elapsed_ms\": {:.2}\n\
         }}\n",
        json_escape(&report.mode),
        report.seed,
        report.batches,
        report.batch_size,
        report.trials_per_candidate,
        report.total_candidates,
        report.unsafe_token_violations,
        report.opt_level_0_compiled,
        report.opt_level_2_compiled,
        report.opt_level_0_and_2_compiled,
        report.instrumented_compiled,
        report.compile_pass_rate_pct,
        report.compared_candidates,
        report.agree_candidates,
        report.diverge_candidates,
        report.not_compared_candidates,
        report.total_traces_executed,
        report.distinct_traces_checked,
        report.agree_traces,
        report.diverge_traces,
        report.kernel_confirmed_traces,
        report.kernel_confirmed_divergences,
        report.distinct_obs_paths,
        render_usize_map_json(&report.per_candidate_distinct_traces, 2),
        render_usize_map_json(&report.diag_tag_counts, 2),
        render_usize_map_json(&report.mutator_applications, 2),
        report.findings.len(),
        report.elapsed_ms,
    )
}

/// Render the human-readable Markdown report for a completed
/// [`ItreeCampaignEvalReport`].
pub fn render_itree_eval_report_markdown(report: &ItreeCampaignEvalReport) -> String {
    let mut out = String::new();
    out.push_str("# `itree-difftest` Differential Oracle Report\n\n");
    out.push_str("- **Oracle comparison**: PERFORMED (native `#[anneal_trace::external]` boundary execution vs. Anneal `TraceCheck` `diagnoseRawByteTraceObsErasedBounded` + Lean 4 kernel confirmation)\n");
    out.push_str(&format!(
        "- **Mode**: `{}` | **Seed**: `0x{:08x}` (`{}` batches × `{}` batch size = `{}` generated, `{}` trials/candidate)\n",
        report.mode,
        report.seed,
        report.batches,
        report.batch_size,
        report.total_candidates,
        report.trials_per_candidate
    ));
    out.push_str(&format!(
        "- **Candidates containing `unsafe`**: `{}`\n",
        report.unsafe_token_violations
    ));
    out.push_str(&format!(
        "- **Compiled at both `-C opt-level=0` and `-C opt-level=2`**: `{}/{}` ({:.2}%)\n",
        report.opt_level_0_and_2_compiled, report.total_candidates, report.compile_pass_rate_pct
    ));
    out.push_str(&format!(
        "- **Candidates compared**: `{}` | **Agree**: `{}` | **Diverge**: `{}` | **NotCompared**: `{}`\n",
        report.compared_candidates,
        report.agree_candidates,
        report.diverge_candidates,
        report.not_compared_candidates
    ));
    out.push_str(&format!(
        "- **Traces executed**: `{}` | **Distinct traces checked in Lean**: `{}` (`{}` agree, `{}` diverge, `{}` kernel-confirmed via `by rfl`) | **Distinct obs paths**: `{}`\n",
        report.total_traces_executed,
        report.distinct_traces_checked,
        report.agree_traces,
        report.diverge_traces,
        report.kernel_confirmed_traces,
        report.distinct_obs_paths
    ));
    out.push_str(&format!(
        "- **Wall-clock time**: `{:.2} ms`\n\n",
        report.elapsed_ms
    ));

    out.push_str("## `TraceReplayDiag` Tag Counts\n\n");
    out.push_str("| Diagnostic Tag | Distinct Traces |\n| :--- | ---: |\n");
    for (k, v) in &report.diag_tag_counts {
        out.push_str(&format!("| `{k}` | {v} |\n"));
    }

    out.push_str("\n## Per-Candidate Distinct Traces Checked\n\n");
    out.push_str("| Candidate Root Function | Distinct Traces |\n| :--- | ---: |\n");
    for (fn_name, cnt) in &report.per_candidate_distinct_traces {
        out.push_str(&format!("| `{fn_name}` | {cnt} |\n"));
    }

    out.push_str("\n## Mutator Applications\n\n");
    out.push_str("| Mutator | Applications |\n| :--- | ---: |\n");
    for (name, count) in &report.mutator_applications {
        out.push_str(&format!("| `{name}` | {count} |\n"));
    }

    if !report.findings.is_empty() {
        out.push_str("\n## Divergences Detected\n\n");
        out.push_str("| Finding ID | Function | Case | `TraceReplayDiag` | Kernel Confirmed |\n");
        out.push_str("| :--- | :--- | :--- | :--- | :--- |\n");
        for f in &report.findings {
            out.push_str(&format!(
                "| `{}` | `{}` | `{}` | `{}` | `{}` |\n",
                f.finding_id, f.fn_name, f.case_ident, f.diag_tag, f.kernel_confirmed
            ));
        }
    }

    out
}
