// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Batch compilation, binary-level MIR-instrumented trace collection
//! (`anneal-mir-instrument` at `-C opt-level=0` and `-C opt-level=2`), trace
//! deduplication, and batched Lean 4 `TraceCheck` evaluation
//! (`diagnoseRawByteTraceFullBounded` + `checkRawByteTraceFullBounded_sound`
//! and `checkRawByteTraceObsErasedBounded_sound`) for `itree-difftest`.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
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
    EnvScheduleGenerator, FieldLayout, LayoutAwareByteBuilder, LayoutSpec, MirInputDictionary,
    MirObsPathSet, PaddingFillPattern, ScalarLayout,
};
use crate::instrument::EnvSchedule;
use crate::miri_eval::{json_escape, resolve_rustc_bin};
use crate::mutators_itree::{
    GeneratedItreeCandidate, ItreeMutationStep, StagedItreeCandidate,
    annotate_itree_external_callees, contains_unsafe_token, itree_candidate_replay_is_faithful,
    reconstruct_itree_mutation_steps, replay_itree_mutation_steps, stage_itree_candidate_items,
};
use crate::mutators_miri::DetRng;
use crate::shrink::{MemoizedOracle, MutatorChainShrinkStatus, shrink_mutation_chain_detailed};

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

/// Canonical not-compared reason keys always included in `not_compared_reasons`.
///
/// Every reason except `compile_failed` means the oracle pipeline itself failed
/// on a candidate that compiled: `staging_failed` (item staging/annotation),
/// `trace_collect_failed` (native trace collector failed to compile/run/parse
/// even in isolation), `opt_level_trace_mismatch` (`-C opt-level=0` and
/// `-C opt-level=2` executions recorded different traces), `empty_trace`
/// (the candidate ran but recorded no traces), `lean_build_failed` (its
/// `Mir.ItreeDiffStaged.*` modules failed `lake build`), `lean_probe_failed`
/// (Stage 1 `diagnoseRawByteTraceFullBounded`), and `lean_confirm_failed`
/// (Stage 2 kernel confirmation).
pub const ITREE_NOT_COMPARED_REASON_NAMES: [&str; 8] = [
    "compile_failed",
    "staging_failed",
    "trace_collect_failed",
    "opt_level_trace_mismatch",
    "empty_trace",
    "lean_build_failed",
    "lean_probe_failed",
    "lean_confirm_failed",
];

/// Maximum number of trace cases per Stage 1 `ItreeDiffBatchProbeChunk` Lean module.
pub const ITREE_PROBE_CHUNK_SIZE: usize = 64;

/// Maximum number of trace cases per Stage 2 `ItreeDiffBatchConfirmChunk` Lean module.
pub const ITREE_CONFIRM_CHUNK_SIZE: usize = 16;

/// Upper bound on any configured Stage 2 chunk size
/// ([`ItreeEvalOptions::confirm_chunk_size`]).
pub const ITREE_MAX_CONFIRM_CHUNK_SIZE: usize = 64;

/// Batches with at most this many distinct traces kernel-confirm every trace in
/// Stage 2; larger batches confirm every divergence plus the first trace of
/// every compared candidate.
pub const ITREE_FULL_CONFIRM_MAX_TRACES: usize = 32;

/// Default number of input trials executed natively per compiled candidate.
pub const DEFAULT_ITREE_TRIALS_PER_CANDIDATE: usize = 12;

/// Step fuel bound passed to `diagnoseRawByteTraceFullBounded`,
/// `checkRawByteTraceFullBounded_sound`, and
/// `checkRawByteTraceObsErasedBounded_sound`.
pub const ITREE_TRACE_CHECK_FUEL: usize = 240;

/// Parses `(MemTotal, MemAvailable)` in KiB from `/proc/meminfo` contents.
fn parse_meminfo_kib(meminfo: &str) -> (Option<u64>, Option<u64>) {
    let field = |name: &str| {
        meminfo.lines().find_map(|line| {
            line.strip_prefix(name)?
                .split_whitespace()
                .next()?
                .parse::<u64>()
                .ok()
        })
    };
    (field("MemTotal:"), field("MemAvailable:"))
}

fn read_u64_file(path: &Path) -> Option<u64> {
    fs::read_to_string(path).ok()?.trim().parse::<u64>().ok()
}

fn min_opt(a: Option<u64>, b: Option<u64>) -> Option<u64> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.min(y)),
        (x, None) => x,
        (None, y) => y,
    }
}

/// Returns `(limit_kib, headroom_kib)` for the tightest cgroup v2 `memory.max`
/// between this process's cgroup (`0::<path>` in `proc_self_cgroup`) and
/// `cgroup_root`, where headroom is `memory.max - memory.current`.
///
/// `anneal-lean-run` confines commands to a transient `systemd-run --scope`
/// whose `MemoryMax` is far below host `MemAvailable` (and parent slices may be
/// capped too), so `/proc/meminfo` alone overestimates how many concurrent
/// `lake env lean` workers fit before the cgroup OOM killer fires.
fn cgroup_memory_limits_kib(
    cgroup_root: &Path,
    proc_self_cgroup: &str,
) -> (Option<u64>, Option<u64>) {
    let Some(rel) = proc_self_cgroup
        .lines()
        .find_map(|line| line.strip_prefix("0::"))
    else {
        return (None, None);
    };
    let mut dir = cgroup_root.join(rel.trim().trim_start_matches('/'));
    let mut limit_kib: Option<u64> = None;
    let mut headroom_kib: Option<u64> = None;
    while dir.starts_with(cgroup_root) {
        if let Some(max) = read_u64_file(&dir.join("memory.max")) {
            let current = read_u64_file(&dir.join("memory.current")).unwrap_or(0);
            limit_kib = min_opt(limit_kib, Some(max / 1024));
            headroom_kib = min_opt(headroom_kib, Some(max.saturating_sub(current) / 1024));
        }
        if dir == cgroup_root || !dir.pop() {
            break;
        }
    }
    (limit_kib, headroom_kib)
}

/// Maps effective total / available memory (KiB) to a `lake env lean` worker
/// count: 1 worker when available memory is below 24 GiB or total memory is at
/// most 36 GiB, at most 2 workers up to 64 GiB total (or below 48 GiB
/// available), and at most 4 workers above that.
pub fn itree_lean_jobs_for_memory(total_kib: Option<u64>, avail_kib: Option<u64>) -> usize {
    const GIB: u64 = 1024 * 1024;
    if total_kib.is_none() && avail_kib.is_none() {
        return 1;
    }
    let by_total = match total_kib {
        None => 4,
        Some(t) if t <= 36 * GIB => 1,
        Some(t) if t <= 64 * GIB => 2,
        Some(_) => 4,
    };
    let by_avail = match avail_kib {
        None => 4,
        Some(a) if a < 24 * GIB => 1,
        Some(a) if a < 48 * GIB => 2,
        Some(_) => 4,
    };
    by_total.min(by_avail)
}

/// Resolve the maximum number of concurrent `lake env lean` chunk workers for
/// `itree-difftest` from `ANNEAL_ITREE_LEAN_JOBS` (capped at 8) or, by default,
/// from host `/proc/meminfo` intersected with the enclosing cgroup v2 memory
/// limits (see [`itree_lean_jobs_for_memory`]).
pub fn resolve_itree_lean_jobs() -> usize {
    if let Ok(val) = env::var("ANNEAL_ITREE_LEAN_JOBS")
        && let Ok(parsed) = val.trim().parse::<usize>()
        && parsed >= 1
    {
        return parsed.min(8);
    }
    let (mut total_kib, mut avail_kib) = fs::read_to_string("/proc/meminfo")
        .map(|s| parse_meminfo_kib(&s))
        .unwrap_or((None, None));
    if let Ok(self_cgroup) = fs::read_to_string("/proc/self/cgroup") {
        let (cg_limit, cg_headroom) =
            cgroup_memory_limits_kib(Path::new("/sys/fs/cgroup"), &self_cgroup);
        total_kib = min_opt(total_kib, cg_limit);
        avail_kib = min_opt(avail_kib, cg_headroom);
    }
    itree_lean_jobs_for_memory(total_kib, avail_kib)
}

fn fnv1a_64_update(mut hash: u64, bytes: &[u8]) -> u64 {
    for &b in bytes {
        hash ^= u64::from(b);
        hash = hash.wrapping_mul(0x0000_0100_0000_01B3);
    }
    hash
}

/// Hashes the semantic shape of one native trace: its `switchInt` branch tag
/// sequence and its external-call sequence (callee item names with the staged
/// `b{batch}_c{candidate}__` prefix and crate path stripped, plus event
/// positions). The candidate's source text is deliberately excluded, so two
/// candidates generated from the same template and mutator chain that take the
/// same path map to the same signature across campaigns, and
/// `cumulative_distinct_obs_paths` only grows when genuinely new paths appear.
fn compute_itree_obs_shape_hash(
    prefix: &str,
    branch_tags: &[u32],
    call_seq: &[(String, usize)],
) -> String {
    let mut h: u64 = 0xCBF2_9CE4_8422_2325;
    for &tag in branch_tags {
        h = fnv1a_64_update(h, &tag.to_le_bytes());
    }
    h = fnv1a_64_update(h, &[0xFE]);
    for (def_path, idx) in call_seq {
        let item = def_path.rsplit("::").next().unwrap_or(def_path);
        let norm_callee = item.strip_prefix(prefix).unwrap_or(item);
        h = fnv1a_64_update(h, norm_callee.as_bytes());
        h = fnv1a_64_update(h, &[0xFD]);
        h = fnv1a_64_update(h, &(*idx as u64).to_le_bytes());
    }
    format!("b{}e{}h{:016x}", branch_tags.len(), call_seq.len(), h)
}

/// Maximum consecutive failed per-candidate fallback runs (with no fallback
/// success yet) before [`run_isolated_lean_stage`] stops retrying, so a
/// systematic toolchain failure (missing `lake`, broken `Anneal` build) does
/// not trigger one `lake env lean` run per candidate.
const ITREE_FALLBACK_CIRCUIT_BREAKER: usize = 4;

/// Keeps the first and last 20 lines of a (potentially huge) Lean failure log.
fn truncate_lean_diag(msg: &str) -> String {
    let lines: Vec<&str> = msg.lines().collect();
    if lines.len() <= 40 {
        return msg.to_string();
    }
    format!(
        "{}\n... ({} lines elided) ...\n{}",
        lines[..20].join("\n"),
        lines.len() - 40,
        lines[lines.len() - 20..].join("\n")
    )
}

/// Outcome of [`run_isolated_lean_stage`].
#[derive(Debug)]
struct IsolatedLeanStage<X> {
    /// Per-case results for every case whose chunk or per-candidate fallback
    /// module succeeded.
    results: BTreeMap<String, X>,
    /// Candidates (root fn names) owning at least one case without a result.
    failed_fns: BTreeSet<String>,
    /// Truncated diagnostics for each failed chunk or fallback run.
    errors: Vec<String>,
}

/// Runs one chunked Lean stage with failure isolation.
///
/// `cases` are split into chunks of at most `chunk_size`, evaluated by
/// `run_chunk(label, chunk)` in waves of at most `jobs` concurrent workers.
/// A chunk only counts as successful if `run_chunk` returns a result for every
/// case in it; a failed, incomplete, or panicking chunk is re-run one candidate
/// at a time (`{stage_label}Fallback_<fn>`), so only the offending candidate(s)
/// end up in `failed_fns`. After [`ITREE_FALLBACK_CIRCUIT_BREAKER`] consecutive
/// fallback failures without any fallback success, remaining fallbacks are
/// skipped (their candidates fail) to bound the cost of systematic failures.
fn run_isolated_lean_stage<C, X, K, F>(
    stage_label: &str,
    cases: &[C],
    chunk_size: usize,
    jobs: usize,
    case_key: K,
    case_to_fn: &BTreeMap<String, String>,
    run_chunk: F,
) -> IsolatedLeanStage<X>
where
    C: Clone + Sync,
    X: Send,
    K: Fn(&C) -> &str,
    F: Fn(&str, &[C]) -> Result<BTreeMap<String, X>, String> + Sync,
{
    let chunk_size = chunk_size.max(1);
    let jobs = jobs.max(1);
    let mut results: BTreeMap<String, X> = BTreeMap::new();
    let mut errors: Vec<String> = Vec::new();
    let mut failed_chunks: Vec<&[C]> = Vec::new();

    let accept = |results: &mut BTreeMap<String, X>,
                  cases: &[C],
                  res: Result<BTreeMap<String, X>, String>,
                  label: &str|
     -> Result<(), String> {
        let mut map = res.map_err(|e| format!("{label}: {}", truncate_lean_diag(&e)))?;
        if let Some(missing) = cases.iter().find(|&c| !map.contains_key(case_key(c))) {
            return Err(format!(
                "{label}: Lean produced no result for `{}`",
                case_key(missing)
            ));
        }
        for c in cases {
            if let Some(x) = map.remove(case_key(c)) {
                results.insert(case_key(c).to_string(), x);
            }
        }
        Ok(())
    };

    let chunks: Vec<&[C]> = cases.chunks(chunk_size).collect();
    for (wave_idx, wave) in chunks.chunks(jobs).enumerate() {
        let wave_res: Vec<(String, Result<BTreeMap<String, X>, String>)> =
            std::thread::scope(|s| {
                let handles: Vec<_> = wave
                    .iter()
                    .enumerate()
                    .map(|(i, &chunk)| {
                        let label = format!("{stage_label}Chunk{}", wave_idx * jobs + i);
                        let run_chunk = &run_chunk;
                        let worker_label = label.clone();
                        let handle = s.spawn(move || run_chunk(&worker_label, chunk));
                        (label, handle)
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|(label, h)| {
                        let res = h
                            .join()
                            .unwrap_or_else(|_| Err("Lean chunk worker panicked".to_string()));
                        (label, res)
                    })
                    .collect()
            });
        for (&chunk, (label, res)) in wave.iter().zip(wave_res) {
            if let Err(e) = accept(&mut results, chunk, res, &label) {
                errors.push(e);
                failed_chunks.push(chunk);
            }
        }
    }

    let mut fallback_successes = 0usize;
    let mut fallback_failures = 0usize;
    let mut skipped_fallbacks = 0usize;
    for chunk in failed_chunks {
        let mut by_fn: BTreeMap<&str, Vec<C>> = BTreeMap::new();
        for c in chunk {
            if let Some(fn_name) = case_to_fn.get(case_key(c)) {
                by_fn.entry(fn_name.as_str()).or_default().push(c.clone());
            }
        }
        for (fn_name, fn_cases) in by_fn {
            if fallback_successes == 0 && fallback_failures >= ITREE_FALLBACK_CIRCUIT_BREAKER {
                skipped_fallbacks += 1;
                continue;
            }
            let label = format!("{stage_label}Fallback_{fn_name}");
            let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                run_chunk(&label, &fn_cases)
            }))
            .unwrap_or_else(|_| Err("Lean fallback worker panicked".to_string()));
            match accept(&mut results, &fn_cases, res, &label) {
                Ok(()) => fallback_successes += 1,
                Err(e) => {
                    fallback_failures += 1;
                    errors.push(e);
                }
            }
        }
    }
    if skipped_fallbacks > 0 {
        errors.push(format!(
            "{stage_label}: skipped {skipped_fallbacks} per-candidate fallback run(s) after \
             {ITREE_FALLBACK_CIRCUIT_BREAKER} consecutive fallback failures (systematic Lean failure)"
        ));
    }

    let failed_fns: BTreeSet<String> = cases
        .iter()
        .filter(|&c| !results.contains_key(case_key(c)))
        .filter_map(|c| case_to_fn.get(case_key(c)).cloned())
        .collect();
    IsolatedLeanStage {
        results,
        failed_fns,
        errors,
    }
}

/// Writes `src` to `verify_dir/<label>.lean` and runs `lake env lean -M 8192`
/// on it from `anneal_dir`, returning stdout on success.
fn run_itree_lean_module(
    verify_dir: &Path,
    anneal_dir: &Path,
    label: &str,
    src: &str,
) -> Result<String, String> {
    let file = verify_dir.join(format!("{label}.lean"));
    fs::write(&file, src).map_err(|e| format!("failed to write {}: {e}", file.display()))?;
    let out = Command::new("lake")
        .args(["env", "lean", "-M", "8192"])
        .arg(&file)
        .current_dir(anneal_dir)
        .output()
        .map_err(|e| format!("failed to run `lake env lean` on {}: {e}", file.display()))?;
    if !out.status.success() {
        return Err(format!(
            "`{}` failed ({}):\nstdout:\n{}\nstderr:\n{}",
            file.display(),
            out.status,
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

fn batch_case_ident(case: &BatchTraceEvalCase) -> &str {
    &case.case_ident
}

/// Per-candidate compilation results across `-C opt-level=0`, `-C opt-level=2`,
/// and `anneal-mir-instrument` compilation at both `-O0` and `-O2`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CandidateCompile {
    /// Compiled cleanly under `#![forbid(unsafe_code)]` at `-C opt-level=0`.
    pub opt0: bool,
    /// Compiled cleanly under `#![forbid(unsafe_code)]` at `-C opt-level=2`.
    pub opt2: bool,
    /// Compiled cleanly under `anneal-mir-instrument` at both `-O0` and `-O2`.
    pub instrumented: bool,
}

/// Optional configuration and negative-control fault injection hooks for
/// [`evaluate_itree_batches_with_options`].
#[derive(Debug, Clone)]
pub struct ItreeEvalOptions {
    /// Number of native execution trials per compiled candidate.
    pub trials_per_candidate: usize,
    /// Maximum number of trace cases per Stage 2 `ItreeDiffBatchConfirmChunk` Lean
    /// module (default [`ITREE_CONFIRM_CHUNK_SIZE`]; clamped to
    /// `1..=`[`ITREE_MAX_CONFIRM_CHUNK_SIZE`]).
    pub confirm_chunk_size: usize,
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
            confirm_chunk_size: ITREE_CONFIRM_CHUNK_SIZE,
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
    /// Ordered list of safe AST mutators applied to produce the program in
    /// `repro.rs`: `minimized_mutator_chain` (equal to `original_mutator_chain`
    /// unless shrinking minimized the chain).
    pub applied_mutators: Vec<String>,
    /// Ordered list of safe AST mutators of the candidate as the batch generated
    /// it.
    pub original_mutator_chain: Vec<String>,
    /// Shortest mutator chain that the live oracle confirmed to reproduce the
    /// finding's `diag_tag` and kernel confirmation (1-minimal when
    /// `shrink_status` is `minimized` or `already_one_minimal`), or
    /// `original_mutator_chain` when shrinking did not reduce it.
    pub minimized_mutator_chain: Vec<String>,
    /// Number of shrinker predicate evaluations on proper subsequences of
    /// `original_mutator_chain` (each one a replay followed by the strict compile
    /// pre-check and, if that passes, an oracle query).
    pub shrink_evaluations: usize,
    /// Number of live ITree oracle runs that shrinking actually executed (oracle
    /// queries answered by [`MemoizedOracle`] are not counted).
    pub executed_oracle_runs: usize,
    /// Outcome of mutator-chain shrinking ([`MutatorChainShrinkStatus::slug`]).
    /// Findings of one candidate with the same `diag_tag` and kernel
    /// confirmation share one shrink.
    pub shrink_status: String,
    /// `TraceReplayDiag.tagName` reported by Lean (e.g., `"outcome_mismatch"`).
    pub diag_tag: String,
    /// Full Lean `reprStr` of the `TraceReplayDiag` value.
    pub diag_repr: String,
    /// Encoded hex line of the diverging [`RecordedRawTrace`].
    pub trace_hex: String,
    /// Whether the Lean 4 kernel confirmed `(diagnoseRawByteTraceFullBounded ...).tagName = "<diag_tag>"` via `by rfl`.
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
    /// Count of candidates whose `anneal-mir-instrument` build succeeded at `-O0` and `-O2`.
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
    /// Count of distinct traces whose `TraceReplayDiag` tag and soundness
    /// theorems the Lean kernel actually checked (`by rfl`) in Stage 2
    /// `ItreeDiffBatchConfirmChunk*` modules: every trace in identity mode or
    /// when at most [`ITREE_FULL_CONFIRM_MAX_TRACES`] distinct traces were
    /// probed, otherwise every divergence plus the first non-diverging trace of
    /// each compared candidate (so `agree_candidates + diverge_traces <=
    /// kernel_confirmed_traces <= distinct_traces_checked`).
    pub kernel_confirmed_traces: usize,
    /// Count of diverging traces kernel-confirmed via `by rfl`.
    pub kernel_confirmed_divergences: usize,
    /// Total distinct external-call observation path shapes (`MirObsPathKey`) observed.
    pub distinct_obs_paths: usize,
    /// Per-candidate distinct trace counts (`b{b_idx}_c{c_idx}__kernel_step -> count`).
    pub per_candidate_distinct_traces: BTreeMap<String, usize>,
    /// Trace counts by `TraceReplayDiag.tagName`.
    pub diag_tag_counts: BTreeMap<String, usize>,
    /// Not-compared candidate counts by reason (`compile_failed`,
    /// `staging_failed`, `empty_trace`, `lean_probe_failed`,
    /// `lean_confirm_failed`).
    pub not_compared_reasons: BTreeMap<String, usize>,
    /// Per-mutator application counts across all generated candidates.
    pub mutator_applications: BTreeMap<String, usize>,
    /// Deterministic, sorted observation-path signatures observed during live
    /// oracle evaluation (`itree:<mutator_chain_or_template>:<branch_and_ext_shape_hash>:<outcome_kind>`).
    pub obs_path_signatures: Vec<String>,
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

/// Sequence number that gives each `compile_rust_strict_opt` and
/// `compile_rust_mir_instrumented` call its own scratch directory, so
/// concurrent calls in one process sharing a label never delete each other's
/// `.rlib` output.
static ITREE_SNIPPET_COMPILE_SEQ: AtomicUsize = AtomicUsize::new(0);

/// Runs `rustc --edition=2024 --crate-type=lib -D warnings -C opt-level=<level>`
/// on `source` and reports whether it compiled.
pub fn compile_rust_strict_opt(label: &str, opt_level: &str, source: &str) -> bool {
    let rustc_bin = resolve_rustc_bin();
    let seq = ITREE_SNIPPET_COMPILE_SEQ.fetch_add(1, Ordering::Relaxed);
    let tmp_dir = env::temp_dir().join(format!(
        "anneal_itree_difftest_{}_{seq}_{}_o{}",
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

/// Runs `anneal-mir-instrument` (`--edition=2024 --crate-type=lib -D warnings
/// -C opt-level=<level>`) on `source` and reports whether it compiled cleanly.
/// Respects an explicit `RUSTC` environment override when present.
pub fn compile_rust_mir_instrumented(label: &str, opt_level: &str, source: &str) -> bool {
    let driver_bin = if let Ok(v) = env::var("RUSTC")
        && !v.trim().is_empty()
    {
        PathBuf::from(v)
    } else {
        let repo_root = default_repo_root();
        let Ok(bin) = ensure_mir_instrument_bin(&repo_root) else {
            return false;
        };
        bin
    };
    let seq = ITREE_SNIPPET_COMPILE_SEQ.fetch_add(1, Ordering::Relaxed);
    let tmp_dir = env::temp_dir().join(format!(
        "anneal_itree_difftest_{}_{seq}_{}_o{}",
        std::process::id(),
        label,
        opt_level
    ));
    let _ = fs::create_dir_all(&tmp_dir);
    let out_path = tmp_dir.join("libitree_mir_inst.rlib");
    let opt_flag = format!("opt-level={opt_level}");

    let child_res = Command::new(&driver_bin)
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
/// annotated copy under `anneal-mir-instrument` at both `-C opt-level=0` and
/// `-C opt-level=2`. Each check first compiles all candidates as one crate and
/// falls back to one candidate at a time only when the combined crate fails.
pub fn compile_itree_candidates(
    batches: &[Vec<GeneratedItreeCandidate>],
) -> Vec<Vec<CandidateCompile>> {
    let entries = batch_entries(batches);
    let mut flat = compile_itree_entries(&entries).into_iter();
    batches
        .iter()
        .map(|b| flat.by_ref().take(b.len()).collect())
        .collect()
}

/// One candidate of an ITree evaluation, identified by its position in the
/// batches (which fixes its staged item prefix `b{b_idx}_c{c_idx}__`).
#[derive(Debug, Clone, Copy)]
struct ItreeEvalEntry<'a> {
    b_idx: usize,
    c_idx: usize,
    cand: &'a GeneratedItreeCandidate,
    /// When `true`, the candidate is staged into `src/candidates.rs` so that
    /// `run_cargo_capture` emits its `Mir.ItreeDiffStaged.*` module (referenced by
    /// another candidate's `root_mir_swaps`), without running native trace
    /// collection or Lean `TraceCheck` on its own traces.
    capture_only: bool,
}

impl ItreeEvalEntry<'_> {
    /// Staged item prefix of this candidate.
    fn prefix(&self) -> String {
        format!("b{}_c{}__", self.b_idx, self.c_idx)
    }

    /// Staged root function of this candidate (`b{b_idx}_c{c_idx}__kernel_step`).
    fn root_fn_name(&self) -> String {
        format!("{}kernel_step", self.prefix())
    }
}

fn batch_entries(batches: &[Vec<GeneratedItreeCandidate>]) -> Vec<ItreeEvalEntry<'_>> {
    batches
        .iter()
        .enumerate()
        .flat_map(|(b_idx, batch)| {
            batch
                .iter()
                .enumerate()
                .map(move |(c_idx, cand)| ItreeEvalEntry {
                    b_idx,
                    c_idx,
                    cand,
                    capture_only: false,
                })
        })
        .collect()
}

/// [`compile_itree_candidates`] over an arbitrary set of entries, returning one
/// result per entry in order.
fn compile_itree_entries(entries: &[ItreeEvalEntry<'_>]) -> Vec<CandidateCompile> {
    let repo_root = default_repo_root();
    let _ = ensure_mir_instrument_bin(&repo_root);
    let mut results = vec![CandidateCompile::default(); entries.len()];

    let mut combined_safe = String::from("#![forbid(unsafe_code)]\n");
    let mut combined_inst =
        String::from("#![feature(register_tool)]\n#![register_tool(anneal_trace)]\n");
    let mut inst_sources: Vec<Option<String>> = Vec::with_capacity(entries.len());
    for entry in entries {
        let (b_idx, c_idx, cand) = (entry.b_idx, entry.c_idx, entry.cand);
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
        inst_sources.push(inst);
    }
    let any_inst_failed = inst_sources.iter().any(Option::is_none);

    let (o0_all, o2_all, inst_all) = std::thread::scope(|s| {
        let h0 = s.spawn(|| compile_rust_strict_opt("all_safe", "0", &combined_safe));
        let h2 = s.spawn(|| compile_rust_strict_opt("all_safe", "2", &combined_safe));
        let hi = s.spawn(|| {
            !any_inst_failed
                && !combined_inst.is_empty()
                && compile_rust_mir_instrumented("all_inst", "0", &combined_inst)
                && compile_rust_mir_instrumented("all_inst", "2", &combined_inst)
        });
        (
            h0.join().unwrap_or(false),
            h2.join().unwrap_or(false),
            hi.join().unwrap_or(false),
        )
    });

    for ((entry, inst_src), result) in entries.iter().zip(&inst_sources).zip(&mut results) {
        let safe_src = format!("#![forbid(unsafe_code)]\n{}", entry.cand.source);
        let label = format!("b{}_c{}", entry.b_idx, entry.c_idx);
        result.opt0 = o0_all || compile_rust_strict_opt(&label, "0", &safe_src);
        result.opt2 = o2_all || compile_rust_strict_opt(&label, "2", &safe_src);
        result.instrumented = match inst_src {
            None => false,
            Some(src) => {
                let inst_src = format!(
                    "#![feature(register_tool)]\n#![register_tool(anneal_trace)]\n{src}"
                );
                inst_all
                    || (compile_rust_mir_instrumented(&format!("{label}_inst"), "0", &inst_src)
                        && compile_rust_mir_instrumented(&format!("{label}_inst"), "2", &inst_src))
            }
        };
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

fn ensure_mir_instrument_bin(repo_root: &Path) -> Result<PathBuf, String> {
    let bin_path = repo_root.join("target/debug/anneal-mir-instrument");
    let lib_src = repo_root.join("crates/anneal-mir-instrument/src/lib.rs");
    let main_src = repo_root.join("crates/anneal-mir-instrument/src/main.rs");
    let bin_mtime = fs::metadata(&bin_path).and_then(|m| m.modified()).ok();
    let lib_mtime = fs::metadata(&lib_src).and_then(|m| m.modified()).ok();
    let main_mtime = fs::metadata(&main_src).and_then(|m| m.modified()).ok();
    if bin_path.is_file()
        && let (Some(bm), Some(lm), Some(mm)) = (bin_mtime, lib_mtime, main_mtime)
        && bm >= lm
        && bm >= mm
    {
        return Ok(bin_path);
    }
    let status = Command::new("cargo")
        .args(["build", "-p", "anneal-mir-instrument", "--locked"])
        .current_dir(repo_root)
        .status()
        .map_err(|e| format!("failed to invoke cargo build for anneal-mir-instrument: {e}"))?;
    if !status.success() {
        return Err("building anneal-mir-instrument failed".to_string());
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

struct ItreeStagingSlot {
    path: PathBuf,
}

impl std::ops::Deref for ItreeStagingSlot {
    type Target = Path;

    fn deref(&self) -> &Path {
        &self.path
    }
}

impl AsRef<std::ffi::OsStr> for ItreeStagingSlot {
    fn as_ref(&self) -> &std::ffi::OsStr {
        self.path.as_os_str()
    }
}

impl Drop for ItreeStagingSlot {
    fn drop(&mut self) {
        release_itree_staging_dir(&self.path);
    }
}

fn create_itree_staging_dir(label: &str, repo_root: &Path) -> Result<ItreeStagingSlot, String> {
    let pool_root = repo_root.join("target/anneal_itree_staging");
    let _ = fs::create_dir_all(&pool_root);

    let mut chosen_dir: Option<PathBuf> = None;
    for slot_idx in 0..8 {
        let slot_dir = pool_root.join(format!("slot_{slot_idx}"));
        let _ = fs::create_dir_all(&slot_dir);
        let lock_dir = slot_dir.join(".active_lock");
        if lock_dir.is_dir() {
            let pid_file = lock_dir.join("pid");
            let lock_older_than_5s = lock_dir
                .metadata()
                .ok()
                .and_then(|m| m.modified().ok())
                .and_then(|t| t.elapsed().ok())
                .is_some_and(|d| d > std::time::Duration::from_secs(5));
            let is_stale = match fs::read_to_string(&pid_file) {
                Ok(pid_s) => {
                    let pid = pid_s.trim();
                    if pid.is_empty() {
                        lock_older_than_5s
                    } else {
                        !Path::new(&format!("/proc/{pid}")).exists()
                    }
                }
                Err(_) => lock_older_than_5s,
            };
            if is_stale {
                let _ = fs::remove_dir_all(&lock_dir);
            }
        }
        if fs::create_dir(&lock_dir).is_ok() {
            let _ = fs::write(lock_dir.join("pid"), std::process::id().to_string());
            chosen_dir = Some(slot_dir);
            break;
        }
    }

    let slot = match chosen_dir {
        Some(slot_dir) => {
            for rel in [
                "src",
                "target",
                "anneal",
                ".anneal/generated",
                ".anneal/.lake/build/lib/lean/Mir",
                ".anneal/.lake/build/lib/lean/Obligations",
                ".anneal/.lake/build/lib/lean/Verify",
                ".anneal/.lake/build/lib/lean/Assumptions",
                ".anneal/.lake/build/lib/lean/CrateVerify",
                ".anneal/.lake/build/ir/Mir",
                ".anneal/.lake/build/ir/Obligations",
                ".anneal/.lake/build/ir/Verify",
                ".anneal/.lake/build/ir/Assumptions",
                ".anneal/.lake/build/ir/CrateVerify",
            ] {
                let _ = fs::remove_dir_all(slot_dir.join(rel));
            }
            for file_rel in [
                "collect_traces.rs",
                "collect_traces_bin_o0",
                "collect_traces_bin_o2",
            ] {
                let _ = fs::remove_file(slot_dir.join(file_rel));
            }
            ItreeStagingSlot { path: slot_dir }
        }
        None => {
            let stamp = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0);
            ItreeStagingSlot {
                path: env::temp_dir().join(format!(
                    "anneal_itree_eval_{label}_{}_{stamp}",
                    std::process::id()
                )),
            }
        }
    };

    fs::create_dir_all(slot.join("src"))
        .map_err(|e| format!("failed to create staging dir {}: {e}", slot.display()))?;
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
    fs::write(slot.join("Cargo.toml"), cargo_toml)
        .map_err(|e| format!("failed to write staged Cargo.toml: {e}"))?;
    Ok(slot)
}

fn release_itree_staging_dir(staging_dir: &Path) {
    let lock_dir = staging_dir.join(".active_lock");
    if lock_dir.is_dir() {
        for file_rel in [
            "collect_traces.rs",
            "collect_traces_bin_o0",
            "collect_traces_bin_o2",
        ] {
            let _ = fs::remove_file(staging_dir.join(file_rel));
        }
        let _ = fs::remove_dir_all(&lock_dir);
    } else if staging_dir
        .file_name()
        .is_some_and(|n| !n.to_string_lossy().starts_with("slot_"))
    {
        let _ = fs::remove_dir_all(staging_dir);
    }
}

#[derive(Debug, Clone)]
struct CandidateTrialInput {
    magic: u32,
    payload_len: u32,
    schedule: EnvSchedule,
}

/// Generate `trials` deterministic `(magic, payload_len, EnvSchedule)` trials
/// for `cand`, combining `MirInputDictionary::from_rust_source(&cand.source)`
/// and `MirInputDictionary::from_lean_mir(lean_mir_source)` with
/// `LayoutAwareByteBuilder` (using a named `LayoutSpec::Struct` so `"magic"`
/// and `"payload_len"` field hints are consulted), `EnvScheduleGenerator`, and
/// boundary probes that exercise all `magic & 3`, `payload_len & 3`, and
/// threshold branches.
fn build_candidate_trial_inputs(
    cand: &GeneratedItreeCandidate,
    staged: &StagedItreeCandidate,
    lean_mir_source: Option<&str>,
    trials: usize,
    batch_seed: u64,
) -> Vec<CandidateTrialInput> {
    let count = trials.max(1);
    let mut dict = MirInputDictionary::from_rust_source(&cand.source)
        .unwrap_or_else(|_| MirInputDictionary::new());
    if let Some(mir_src) = lean_mir_source {
        let mir_dict = MirInputDictionary::from_lean_mir(mir_src);
        dict.merge(&mir_dict);
    }
    let builder = LayoutAwareByteBuilder::new(&dict)
        .with_dictionary_bias_pct(75)
        .with_validity_fault_rate_pct(0)
        .with_padding_pattern(PaddingFillPattern::AlternatingA55A);
    let pair_layout = LayoutSpec::Struct {
        name: "KernelStepArgs".to_string(),
        total_size: 8,
        fields: vec![
            FieldLayout {
                name: "magic".to_string(),
                offset: 0,
                layout: LayoutSpec::Scalar(ScalarLayout::u32()),
            },
            FieldLayout {
                name: "payload_len".to_string(),
                offset: 4,
                layout: LayoutSpec::Scalar(ScalarLayout::u32()),
            },
        ],
    };
    let sched_gen = EnvScheduleGenerator::new(&dict)
        .with_horizon_steps(4)
        .with_panic_injection_pct(20);
    let callee_refs: Vec<&str> = staged.ext_callee_names.iter().map(String::as_str).collect();

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
    let mut dynamic_idx = 0usize;
    for idx in 0..count {
        if idx < fixed_probes.len() && idx + 2 <= count {
            let (magic, payload_len, inject_panic) = fixed_probes[idx];
            let schedule = if inject_panic {
                EnvSchedule::new().with_panic_on_call(0)
            } else {
                EnvSchedule::new()
            };
            out.push(CandidateTrialInput {
                magic,
                payload_len,
                schedule,
            });
            continue;
        }
        let mut entropy = [0u8; 64];
        for chunk in entropy.chunks_exact_mut(8) {
            chunk.copy_from_slice(&rng.next_u64().to_le_bytes());
        }
        let mut u = Unstructured::new(&entropy);
        let raw = builder.build_bytes(&pair_layout, &mut u);
        let magic = u32::from_le_bytes([raw[0], raw[1], raw[2], raw[3]]);
        let payload_len = u32::from_le_bytes([raw[4], raw[5], raw[6], raw[7]]);
        let schedule = if dynamic_idx % 2 == 1 && !callee_refs.is_empty() {
            sched_gen.generate_schedule(&callee_refs, &mut u)
        } else {
            EnvSchedule::new()
        };
        dynamic_idx += 1;
        out.push(CandidateTrialInput {
            magic,
            payload_len,
            schedule,
        });
    }
    out
}

fn render_trace_recorder_expr(sched: &EnvSchedule) -> String {
    if sched.global_panic_on_call.is_none()
        && sched.callee_panic_on_call.is_empty()
        && sched.callee_queues.is_empty()
        && sched.callee_defaults.is_empty()
    {
        return "TraceRecorder::new()".to_string();
    }
    let mut expr = "{ let mut s = EnvSchedule::new();".to_string();
    if let Some(idx) = sched.global_panic_on_call {
        let _ = write!(expr, " s.set_panic_on_call({idx});");
    }
    for (callee, idx) in &sched.callee_panic_on_call {
        let _ = write!(expr, " s.set_callee_panic_on_call({callee:?}, {idx});");
    }
    for (callee, queue) in &sched.callee_queues {
        for bytes in queue {
            let byte_list = bytes
                .iter()
                .map(|b| format!("{b}u8"))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = write!(
                expr,
                " s.push_callee_response({callee:?}, vec![{byte_list}]);"
            );
        }
    }
    for (callee, bytes) in &sched.callee_defaults {
        let byte_list = bytes
            .iter()
            .map(|b| format!("{b}u8"))
            .collect::<Vec<_>>()
            .join(", ");
        let _ = write!(
            expr,
            " s.set_callee_default({callee:?}, vec![{byte_list}]);"
        );
    }
    expr.push_str(" TraceRecorder::with_schedule(s) }");
    expr
}

fn render_trace_collector_source(
    repo_root: &Path,
    staged_candidates: &[(StagedItreeCandidate, Vec<CandidateTrialInput>)],
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
    let _ = writeln!(out, "pub mod itree_diff_staged {{");
    for (staged, _trials) in staged_candidates {
        let _ = writeln!(out, "{}", staged.staged_source);
    }
    let _ = writeln!(out, "}}\n");
    let _ = writeln!(
        out,
        "use trace_observer::{{EnvSchedule, TraceCapture, TraceRecorder, encode_recorded_raw_trace_hex, value_as_raw_bytes}};\n"
    );
    let _ = writeln!(
        out,
        "#[inline(never)]\n\
         fn __anneal_no_instrument_run_trial<R: TraceCapture>(\n\
         \x20   fn_ident: &str,\n\
         \x20   def_path: &str,\n\
         \x20   f: fn(u32, u32) -> R,\n\
         \x20   a0: u32,\n\
         \x20   a1: u32,\n\
         \x20   rec: TraceRecorder,\n\
         ) {{\n\
         \x20   let (_res, trace, _rec) = TraceRecorder::observe_root_with_recorder(\n\
         \x20       rec,\n\
         \x20       def_path,\n\
         \x20       vec![value_as_raw_bytes(&a0), value_as_raw_bytes(&a1)],\n\
         \x20       |_rec| f(a0, a1),\n\
         \x20   );\n\
         \x20   println!(\"ANNEAL_TRACE_HEX:{{fn_ident}}:{{}}\", encode_recorded_raw_trace_hex(&trace));\n\
         }}\n"
    );

    for (staged, trials) in staged_candidates {
        let fn_ident = &staged.root_fn_name;
        let def_path = format!("itree_diff_staged::{fn_ident}");
        let _ = writeln!(
            out,
            "#[inline(never)]\nfn __anneal_no_instrument_trials_{fn_ident}() {{"
        );
        for trial in trials {
            let magic = trial.magic;
            let payload_len = trial.payload_len;
            let rec_expr = render_trace_recorder_expr(&trial.schedule);
            let _ = writeln!(
                out,
                "    __anneal_no_instrument_run_trial(\"{fn_ident}\", \"{def_path}\", itree_diff_staged::{fn_ident}, {magic}u32, {payload_len}u32, {rec_expr});"
            );
        }
        let _ = writeln!(out, "}}\n");
    }

    let _ = writeln!(out, "fn main() {{");
    for (staged, _trials) in staged_candidates {
        let fn_ident = &staged.root_fn_name;
        let _ = writeln!(out, "    __anneal_no_instrument_trials_{fn_ident}();");
    }
    let _ = writeln!(out, "}}");
    out
}

fn collect_traces_natively(
    repo_root: &Path,
    staging_dir: &Path,
    staged_candidates: &[(StagedItreeCandidate, Vec<CandidateTrialInput>)],
) -> Result<NativeTraceCollection, String> {
    let proc_macro_dylib = build_anneal_trace_proc_macro_dylib(repo_root, staging_dir)?;
    let mir_instrument_bin = ensure_mir_instrument_bin(repo_root)?;
    let extern_arg = format!("anneal_trace={}", proc_macro_dylib.display());

    let parse_collector_stdout =
        |stdout: &[u8]| -> Result<BTreeMap<String, Vec<RecordedRawTrace>>, String> {
            const PREFIX: &str = "ANNEAL_TRACE_HEX:";
            let mut by_fn: BTreeMap<String, Vec<RecordedRawTrace>> = BTreeMap::new();
            for line in String::from_utf8_lossy(stdout).lines() {
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
        };

    let fn_to_fn: BTreeMap<String, String> = staged_candidates
        .iter()
        .map(|(s, _)| (s.root_fn_name.clone(), s.root_fn_name.clone()))
        .collect();

    let trace_stage = run_isolated_lean_stage(
        "ItreeDiffTraceCollect",
        staged_candidates,
        ITREE_PROBE_CHUNK_SIZE,
        1,
        |(s, _): &(StagedItreeCandidate, Vec<CandidateTrialInput>)| s.root_fn_name.as_str(),
        &fn_to_fn,
        |label: &str, chunk: &[(StagedItreeCandidate, Vec<CandidateTrialInput>)]| {
            let collector_src = render_trace_collector_source(repo_root, chunk);
            let collector_rs = staging_dir.join(format!("collect_traces_{label}.rs"));
            let collector_bin_o0 = staging_dir.join(format!("collect_traces_bin_o0_{label}"));
            let collector_bin_o2 = staging_dir.join(format!("collect_traces_bin_o2_{label}"));
            let cleanup = || {
                let _ = fs::remove_file(&collector_rs);
                let _ = fs::remove_file(&collector_bin_o0);
                let _ = fs::remove_file(&collector_bin_o2);
            };
            if let Err(e) = fs::write(&collector_rs, &collector_src) {
                cleanup();
                return Err(format!("failed to write {}: {e}", collector_rs.display()));
            }

            let compile_one = |opt_level: &str, bin_path: &Path| -> Result<(), String> {
                let opt_flag = format!("opt-level={opt_level}");
                let compile_out = Command::new(&mir_instrument_bin)
                    .args([
                        "--edition=2024",
                        "--cfg",
                        "anneal_trace_ext",
                        "-A",
                        "warnings",
                        "-C",
                        &opt_flag,
                        "-C",
                        "codegen-units=16",
                        "--extern",
                        &extern_arg,
                    ])
                    .arg(&collector_rs)
                    .arg("-o")
                    .arg(bin_path)
                    .current_dir(staging_dir)
                    .output()
                    .map_err(|e| {
                        format!(
                            "failed to invoke anneal-mir-instrument (-O{opt_level}) for trace collector: {e}"
                        )
                    })?;
                if !compile_out.status.success() {
                    return Err(format!(
                        "compiling {} with anneal-mir-instrument (-O{opt_level}) failed:\n{}",
                        collector_rs.display(),
                        String::from_utf8_lossy(&compile_out.stderr)
                    ));
                }
                Ok(())
            };
            let (res_o0, res_o2) = std::thread::scope(|s| {
                let h0 = s.spawn(|| compile_one("0", &collector_bin_o0));
                let h2 = s.spawn(|| compile_one("2", &collector_bin_o2));
                (
                    h0.join().unwrap_or_else(|_| {
                        Err("panic compiling -O0 trace collector".to_string())
                    }),
                    h2.join().unwrap_or_else(|_| {
                        Err("panic compiling -O2 trace collector".to_string())
                    }),
                )
            });
            if let Err(e) = res_o0.and(res_o2) {
                cleanup();
                return Err(e);
            }

            let run_res = (|| -> Result<CollectedChunkTraces, String> {
                let run_o0 = Command::new(&collector_bin_o0)
                    .current_dir(staging_dir)
                    .output()
                    .map_err(|e| format!("failed to execute -O0 trace collector binary: {e}"))?;
                if !run_o0.status.success() {
                    return Err(format!(
                        "running {} failed:\nstdout:\n{}\nstderr:\n{}",
                        collector_bin_o0.display(),
                        String::from_utf8_lossy(&run_o0.stdout),
                        String::from_utf8_lossy(&run_o0.stderr)
                    ));
                }
                let run_o2 = Command::new(&collector_bin_o2)
                    .current_dir(staging_dir)
                    .output()
                    .map_err(|e| format!("failed to execute -O2 trace collector binary: {e}"))?;
                if !run_o2.status.success() {
                    return Err(format!(
                        "running {} failed:\nstdout:\n{}\nstderr:\n{}",
                        collector_bin_o2.display(),
                        String::from_utf8_lossy(&run_o2.stdout),
                        String::from_utf8_lossy(&run_o2.stderr)
                    ));
                }

                let mut by_fn_o0 = parse_collector_stdout(&run_o0.stdout)?;
                let mut by_fn_o2 = parse_collector_stdout(&run_o2.stdout)?;
                let mut chunk_out = CollectedChunkTraces::new();
                for (staged, trials) in chunk {
                    let fn_name = &staged.root_fn_name;
                    let t0 = by_fn_o0.remove(fn_name).unwrap_or_default();
                    let t2 = by_fn_o2.remove(fn_name).unwrap_or_default();
                    if t0.len() != trials.len() || t2.len() != trials.len() {
                        return Err(format!(
                            "trace count mismatch for `{fn_name}`: expected {} trial(s), got -O0={} and -O2={}",
                            trials.len(),
                            t0.len(),
                            t2.len()
                        ));
                    }
                    if t0 != t2 {
                        eprintln!(
                            "itree-difftest: `{fn_name}` binary-instrumented traces differed \
                             between `-C opt-level=0` and `-C opt-level=2`"
                        );
                        chunk_out.insert(fn_name.clone(), None);
                    } else {
                        chunk_out.insert(fn_name.clone(), Some(t0));
                    }
                }
                Ok(chunk_out)
            })();
            cleanup();
            run_res
        },
    );
    for err in &trace_stage.errors {
        eprintln!("itree-difftest: native trace collector failure: {err}");
    }
    let mut collection = NativeTraceCollection {
        collect_failed: trace_stage.failed_fns,
        errors: trace_stage.errors,
        ..NativeTraceCollection::default()
    };
    for (fn_name, traces) in trace_stage.results {
        match traces {
            Some(traces) => {
                collection.traces_by_fn.insert(fn_name, traces);
            }
            None => {
                collection.opt_level_mismatch.insert(fn_name);
            }
        }
    }
    Ok(collection)
}

/// Per-candidate traces from one collector chunk: `None` marks a candidate whose
/// `-C opt-level=0` and `-C opt-level=2` traces differed.
type CollectedChunkTraces = BTreeMap<String, Option<Vec<RecordedRawTrace>>>;

/// Per-candidate outcome of [`collect_traces_natively`].
#[derive(Debug, Default)]
struct NativeTraceCollection {
    /// Raw traces of every candidate whose `-O0` and `-O2` executions agreed.
    traces_by_fn: BTreeMap<String, Vec<RecordedRawTrace>>,
    /// Candidates whose trace collector failed to compile, run, or parse,
    /// even after per-candidate fallback.
    collect_failed: BTreeSet<String>,
    /// Candidates whose `-C opt-level=0` and `-C opt-level=2` traces differed.
    opt_level_mismatch: BTreeSet<String>,
    /// Truncated diagnostics for failed collector chunks / fallbacks.
    errors: Vec<String>,
}

impl NativeTraceCollection {
    /// `not_compared_reasons` key for a candidate that has no usable traces.
    fn missing_trace_reason(&self, fn_name: &str) -> &'static str {
        if self.opt_level_mismatch.contains(fn_name) {
            "opt_level_trace_mismatch"
        } else if self.collect_failed.contains(fn_name) {
            "trace_collect_failed"
        } else {
            "empty_trace"
        }
    }
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
    let obs_erased_header = format!("theorem {case_ident}_trace_obs_erased_consistent :");
    let mut blocks = Vec::new();
    for header in [&sound_header, &obs_erased_header, &diag_header] {
        if let Some(start_idx) = confirm_src.find(header) {
            let rest = &confirm_src[start_idx..];
            let end_rel = rest.find("\n\n").map(|i| i + 1).unwrap_or(rest.len());
            blocks.push(rest[..end_rel].trim().to_string());
        }
    }
    blocks.join("\n\n")
}

/// Render a mutator chain for `SUMMARY.md` (`"identity (none)"` when empty).
fn render_itree_mutator_chain_md(chain: &[String]) -> String {
    if chain.is_empty() {
        "identity (none)".to_string()
    } else {
        chain.join(", ")
    }
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
         - **Original mutator chain**: `{}`\n\
         - **Minimized mutator chain**: `{}`\n\
         - **Shrink status**: `{}`\n\
         - **Shrink evaluations**: `{}` (live oracle runs executed: `{}`)\n\
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
        render_itree_mutator_chain_md(&finding.applied_mutators),
        render_itree_mutator_chain_md(&finding.original_mutator_chain),
        render_itree_mutator_chain_md(&finding.minimized_mutator_chain),
        finding.shrink_status,
        finding.shrink_evaluations,
        finding.executed_oracle_runs,
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
/// `TraceCheck` verification (chunked, failure-isolating
/// `ItreeDiffBatchProbeChunk*` probes + `ItreeDiffBatchConfirmChunk*` kernel
/// confirmation; see [`ITREE_PROBE_CHUNK_SIZE`] and [`ITREE_CONFIRM_CHUNK_SIZE`]).
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
        confirm_chunk_size: ITREE_CONFIRM_CHUNK_SIZE,
        anneal_repo_root: anneal_repo_root.map(Path::to_path_buf),
        findings_dir: findings_dir.map(Path::to_path_buf),
        mir_mutations: Vec::new(),
        root_mir_swaps: Vec::new(),
    };
    evaluate_itree_batches_with_options(mode, seed, batches, batch_size, &options)
}

/// Evaluates `batches` with explicit [`ItreeEvalOptions`] (including trial
/// counts and optional negative-control MIR mutation / root-swap hooks).
///
/// Every finding's mutator chain is then shrunk against the live oracle to a
/// 1-minimal chain that reproduces the finding's `TraceReplayDiag` tag and
/// kernel confirmation ([`minimize_itree_candidate_mutations`], honoring the same
/// MIR mutations and root swaps), and finding bundles describe the minimized
/// candidate's run.
pub fn evaluate_itree_batches_with_options(
    mode: &str,
    seed: u64,
    batches: &[Vec<GeneratedItreeCandidate>],
    batch_size: usize,
    options: &ItreeEvalOptions,
) -> Result<ItreeCampaignEvalReport, String> {
    let start = Instant::now();
    let entries = batch_entries(batches);
    let mut report = evaluate_itree_entries(
        mode,
        seed,
        batches.len(),
        batch_size,
        &entries,
        options,
        MirMutationPolicy::Require,
    )?;
    shrink_itree_findings(&mut report, mode, seed, batches, batch_size, options);
    if let Some(dir) = &options.findings_dir {
        for finding in &mut report.findings {
            write_itree_finding_bundle_to_dir(dir, finding)?;
        }
    }
    report.elapsed_ms = start.elapsed().as_secs_f64() * 1000.0;
    Ok(report)
}

/// How [`evaluate_itree_entries`] treats a requested MIR mutation whose target
/// module or pattern is absent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MirMutationPolicy {
    /// Fail the evaluation: a caller's negative control must apply.
    Require,
    /// Skip the mutation: shrinking replays reductions of a candidate that may
    /// lack the mutated construct, and the injected fault does not apply to them.
    SkipAbsent,
}

/// Core of [`evaluate_itree_batches_with_options`] over an arbitrary set of
/// entries (each staged under its own `b{b_idx}_c{c_idx}__` prefix), without
/// shrinking or writing finding bundles.
fn evaluate_itree_entries(
    mode: &str,
    seed: u64,
    batch_count: usize,
    batch_size: usize,
    entries: &[ItreeEvalEntry<'_>],
    options: &ItreeEvalOptions,
    mir_mutation_policy: MirMutationPolicy,
) -> Result<ItreeCampaignEvalReport, String> {
    let start = Instant::now();
    let repo_root = options
        .anneal_repo_root
        .clone()
        .unwrap_or_else(default_repo_root);

    let total_candidates = entries.len();
    let unsafe_token_violations = entries
        .iter()
        .filter(|entry| contains_unsafe_token(&entry.cand.source))
        .count();

    let flat_compile = compile_itree_entries(entries);
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
    for entry in entries {
        for m in &entry.cand.applied_mutators {
            *mutator_applications.entry(m.clone()).or_insert(0) += 1;
        }
    }

    let mut diag_tag_counts: BTreeMap<String, usize> = ITREE_DIAG_TAG_NAMES
        .iter()
        .map(|k| (k.to_string(), 0))
        .collect();
    let mut not_compared_reasons: BTreeMap<String, usize> = ITREE_NOT_COMPARED_REASON_NAMES
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
        let mut staged_candidates: Vec<(&GeneratedItreeCandidate, StagedItreeCandidate, bool)> =
            Vec::with_capacity(opt_level_0_and_2_compiled);
        let mut cand_meta: BTreeMap<String, (&GeneratedItreeCandidate, StagedItreeCandidate)> =
            BTreeMap::new();
        let mut fn_prefix_map: BTreeMap<String, String> = BTreeMap::new();

        for (entry, comp) in entries.iter().zip(&flat_compile) {
            let cand = entry.cand;
            if !(comp.opt0 && comp.opt2 && comp.instrumented) || contains_unsafe_token(&cand.source)
            {
                *not_compared_reasons
                    .entry("compile_failed".to_string())
                    .or_insert(0) += 1;
                continue;
            }
            let prefix = entry.prefix();
            let staged = match stage_itree_candidate_items(&cand.source, &prefix, "kernel_step") {
                Ok(s) => s,
                Err(_) => {
                    *not_compared_reasons
                        .entry("staging_failed".to_string())
                        .or_insert(0) += 1;
                    continue;
                }
            };
            combined_candidates_rs.push_str(&staged.staged_source);
            combined_candidates_rs.push('\n');
            fn_prefix_map.insert(staged.root_fn_name.clone(), prefix);
            cand_meta.insert(staged.root_fn_name.clone(), (cand, staged.clone()));
            staged_candidates.push((cand, staged, entry.capture_only));
        }
        if staged_candidates.is_empty() {
            return Err(format!(
                "cannot perform ITree oracle comparison: 0 of {total_candidates} candidates staged"
            ));
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
            let orig = match fs::read_to_string(&mir_file) {
                Ok(orig) => orig,
                Err(_) if mir_mutation_policy == MirMutationPolicy::SkipAbsent => continue,
                Err(e) => return Err(format!("failed to read {}: {e}", mir_file.display())),
            };
            let mutated = orig.replace(from_s, to_s);
            if orig == mutated {
                if mir_mutation_policy == MirMutationPolicy::SkipAbsent {
                    continue;
                }
                return Err(format!(
                    "MIR mutation pattern `{from_s}` not found in {}",
                    mir_file.display()
                ));
            }
            fs::write(&mir_file, mutated)
                .map_err(|e| format!("failed to write mutated {}: {e}", mir_file.display()))?;
        }

        // Now that Lean MIR is scaffolded, build MIR-guided initial inputs and
        // `EnvScheduleGenerator` schedules per evaluated candidate using both the
        // Rust source and the extracted Lean MIR (`MirInputDictionary::from_lean_mir`).
        let mut staged_with_trials: Vec<(
            StagedItreeCandidate,
            Vec<CandidateTrialInput>,
        )> = Vec::with_capacity(staged_candidates.len());
        for (cand, staged, capture_only) in staged_candidates {
            if capture_only {
                continue;
            }
            let mir_file = mir_dir.join(format!("{}.lean", staged.root_fn_name));
            let lean_mir_src = fs::read_to_string(&mir_file).ok();
            let trials = build_candidate_trial_inputs(
                cand,
                &staged,
                lean_mir_src.as_deref(),
                options.trials_per_candidate,
                seed,
            );
            staged_with_trials.push((staged, trials));
        }

        let swap_map: BTreeMap<String, String> =
            options.root_mir_swaps.iter().cloned().collect();

        // Execute all compiled candidates natively with boundary interposition.
        let native = collect_traces_natively(&repo_root, &staging_dir, &staged_with_trials)?;

        let mut raw_trace_count_by_fn: BTreeMap<String, usize> = BTreeMap::new();
        let mut obs_records_by_fn: BTreeMap<
            String,
            Vec<(crate::input_gen::MirObsPathKey, Vec<u8>)>,
        > = BTreeMap::new();
        let mut obs_sigs_by_fn: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut compared_fn_names: BTreeSet<String> = BTreeSet::new();
        let mut per_candidate_distinct_traces: BTreeMap<String, usize> = BTreeMap::new();
        let mut batch_cases: Vec<BatchTraceEvalCase> = Vec::new();
        let mut case_to_fn: BTreeMap<String, String> = BTreeMap::new();

        for (staged, _trials) in &staged_with_trials {
            let fn_name = &staged.root_fn_name;
            let raw_traces = native
                .traces_by_fn
                .get(fn_name)
                .cloned()
                .unwrap_or_default();
            if raw_traces.is_empty() {
                let reason = native.missing_trace_reason(fn_name);
                eprintln!("itree-difftest: `{fn_name}` not compared: {reason}");
                *not_compared_reasons.entry(reason.to_string()).or_insert(0) += 1;
                continue;
            }
            compared_fn_names.insert(fn_name.clone());
            raw_trace_count_by_fn.insert(fn_name.clone(), raw_traces.len());

            let prefix = fn_prefix_map
                .get(fn_name)
                .map(String::as_str)
                .unwrap_or("");
            let template_and_chain = if let Some((cand, _)) = cand_meta.get(fn_name) {
                if cand.applied_mutators.is_empty() {
                    format!("seed{}@identity", cand.seed_index)
                } else {
                    format!("seed{}@{}", cand.seed_index, cand.applied_mutators.join("+"))
                }
            } else {
                fn_name.clone()
            };

            let mut fn_obs_records = Vec::with_capacity(raw_traces.len());
            let mut fn_obs_sigs = BTreeSet::new();

            for tr in &raw_traces {
                let mut call_seq = Vec::new();
                let mut branch_tags = Vec::new();
                for (idx, ev) in tr.events.iter().enumerate() {
                    match ev {
                        RecordedEvent::ExtCall { def_path, .. }
                        | RecordedEvent::ExtCallPanic { def_path, .. }
                        | RecordedEvent::ExtCallAbort { def_path, .. } => {
                            call_seq.push((def_path.clone(), idx));
                        }
                        RecordedEvent::Branch { tag } => {
                            branch_tags.push(*tag as u32);
                        }
                    }
                }
                let is_panic = matches!(tr.outcome, RecordedOutcome::Panic);
                let outcome_kind = match &tr.outcome {
                    RecordedOutcome::Normal { .. } => "normal",
                    RecordedOutcome::Panic => "panic",
                    RecordedOutcome::Abort => "abort",
                };
                let shape_hash =
                    compute_itree_obs_shape_hash(prefix, &branch_tags, &call_seq);
                fn_obs_sigs.insert(format!(
                    "itree:{template_and_chain}:{shape_hash}:{outcome_kind}"
                ));
                fn_obs_records.push((
                    crate::input_gen::MirObsPathKey {
                        fn_name: fn_name.clone(),
                        branch_tags,
                        ext_call_sequence_shape: call_seq,
                        is_panic,
                    },
                    tr.raw_args.iter().flatten().copied().collect(),
                ));
            }
            obs_records_by_fn.insert(fn_name.clone(), fn_obs_records);
            obs_sigs_by_fn.insert(fn_name.clone(), fn_obs_sigs);

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
                        check_branches: true,
                    },
                    trace,
                    expected_diag_tag: None,
                    tampered_outcome: None,
                });
            }
        }

        if batch_cases.is_empty() {
            return Err(match native.errors.first() {
                Some(err) => format!("native trace collection produced 0 traces: {err}"),
                None => "native trace collection produced 0 traces".to_string(),
            });
        }

        // Build Anneal + referenced Mir modules via `lake build` in isolated chunks,
        // skipping unused `__AnnealSafePadded_*` derived-trait Mir modules and
        // isolating any candidate whose `Mir.ItreeDiffStaged.*` module fails to build.
        let anneal_dir = staging_dir.join(".anneal");
        let mut mir_modules_by_fn: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for case in &batch_cases {
            let Some(fn_name) = case_to_fn.get(&case.case_ident) else {
                continue;
            };
            let entry = mir_modules_by_fn.entry(fn_name.clone()).or_default();
            if !entry.contains(&case.config.root_mir_module) {
                entry.push(case.config.root_mir_module.clone());
            }
            for m in &case.config.callee_sig_modules {
                if !entry.contains(m) {
                    entry.push(m.clone());
                }
            }
        }
        let mir_fn_cases: Vec<(String, Vec<String>)> = mir_modules_by_fn.into_iter().collect();
        let mir_fn_to_fn: BTreeMap<String, String> = mir_fn_cases
            .iter()
            .map(|(f, _)| (f.clone(), f.clone()))
            .collect();
        let mir_stage = run_isolated_lean_stage(
            "ItreeDiffMirBuild",
            &mir_fn_cases,
            ITREE_PROBE_CHUNK_SIZE,
            1,
            |(f, _): &(String, Vec<String>)| f.as_str(),
            &mir_fn_to_fn,
            |_label: &str, chunk: &[(String, Vec<String>)]| {
                let mut targets = vec!["Anneal".to_string()];
                for (_f, mods) in chunk {
                    for m in mods {
                        if !targets.contains(m) {
                            targets.push(m.clone());
                        }
                    }
                }
                run_lake_verify_targets(&anneal_dir, &targets)?;
                Ok(chunk.iter().map(|(f, _)| (f.clone(), ())).collect())
            },
        );
        for err in &mir_stage.errors {
            eprintln!("itree-difftest: Lean Mir module build failure: {err}");
        }
        for fn_name in &mir_stage.failed_fns {
            if compared_fn_names.remove(fn_name) {
                eprintln!("itree-difftest: `{fn_name}` not compared: lean_build_failed");
                *not_compared_reasons
                    .entry("lean_build_failed".to_string())
                    .or_insert(0) += 1;
            }
        }
        batch_cases.retain(|c| {
            case_to_fn
                .get(&c.case_ident)
                .is_some_and(|f| compared_fn_names.contains(f))
        });
        if batch_cases.is_empty() {
            return Err(format!(
                "all ITree candidates failed Lean Mir module build: {}",
                mir_stage
                    .errors
                    .first()
                    .map(String::as_str)
                    .unwrap_or("no Mir build output")
            ));
        }

        let verify_dir = anneal_dir.join("generated/Verify/ItreeDiffStaged");
        fs::create_dir_all(&verify_dir)
            .map_err(|e| format!("failed to create {}: {e}", verify_dir.display()))?;

        let lean_jobs = resolve_itree_lean_jobs();
        eprintln!(
            "itree-difftest: Lean TraceCheck over {} distinct traces from {} candidates \
             with {lean_jobs} concurrent `lake env lean` worker(s)",
            batch_cases.len(),
            compared_fn_names.len()
        );

        // Stage 1: Probe `diagnoseRawByteTraceFullBounded` across all distinct
        // traces in chunks of `<= ITREE_PROBE_CHUNK_SIZE` cases, at most
        // `lean_jobs` concurrent `lake env lean` workers. A failed chunk is
        // re-probed one candidate at a time so only offending candidates land in
        // `not_compared_reasons["lean_probe_failed"]`.
        let probe_stage = run_isolated_lean_stage(
            "ItreeDiffBatchProbe",
            &batch_cases,
            ITREE_PROBE_CHUNK_SIZE,
            lean_jobs,
            batch_case_ident,
            &case_to_fn,
            |label: &str, chunk: &[BatchTraceEvalCase]| {
                let src = render_batch_trace_probe_lean_module(&format!("Proof.{label}"), chunk);
                let stdout = run_itree_lean_module(&verify_dir, &anneal_dir, label, &src)?;
                let parsed = parse_batch_trace_probe_output(&stdout);
                for c in chunk {
                    if !parsed.contains_key(&c.case_ident) {
                        return Err(format!(
                            "Stage 1 Lean probe module `{label}` omitted output for `{}`",
                            c.case_ident
                        ));
                    }
                }
                Ok(parsed)
            },
        );
        for err in &probe_stage.errors {
            eprintln!("itree-difftest: Stage 1 Lean probe failure: {err}");
        }
        for fn_name in &probe_stage.failed_fns {
            if compared_fn_names.remove(fn_name) {
                eprintln!("itree-difftest: `{fn_name}` not compared: lean_probe_failed");
                *not_compared_reasons
                    .entry("lean_probe_failed".to_string())
                    .or_insert(0) += 1;
            }
        }
        let probe_map = probe_stage.results;
        batch_cases.retain(|c| {
            case_to_fn
                .get(&c.case_ident)
                .is_some_and(|f| compared_fn_names.contains(f))
        });
        if batch_cases.is_empty() {
            return Err(format!(
                "all ITree candidates failed Stage 1 Lean probe evaluation: {}",
                probe_stage
                    .errors
                    .first()
                    .map(String::as_str)
                    .unwrap_or("no probe output")
            ));
        }

        for case in &mut batch_cases {
            let (tag, _repr) = probe_map
                .get(&case.case_ident)
                .ok_or_else(|| format!("missing probe output for `{}`", case.case_ident))?;
            case.expected_diag_tag = Some(tag.clone());
        }

        // Stage 2: Kernel-confirm `TraceReplayDiag.tagName` (`by rfl`) and
        // `checkRawByteTraceFullBounded_sound` + `checkRawByteTraceObsErasedBounded_sound`
        // in chunks of `<= confirm_chunk_size` cases, each chunk importing only
        // its own `Mir.ItreeDiffStaged.*` modules. Identity-mode runs and batches of
        // `<= ITREE_FULL_CONFIRM_MAX_TRACES` distinct traces confirm every trace;
        // larger batches confirm every divergence plus the first trace of every
        // candidate. `kernel_confirmed_traces` counts only traces whose theorems were
        // actually checked by the Lean kernel.
        let confirm_cases: Vec<BatchTraceEvalCase> =
            if mode == "identity" || batch_cases.len() <= ITREE_FULL_CONFIRM_MAX_TRACES {
                batch_cases.clone()
            } else {
                let mut selected = Vec::new();
                let mut confirmed_fns: BTreeSet<String> = BTreeSet::new();
                for case in &batch_cases {
                    let is_div = case.expected_diag_tag.as_deref() != Some("ok");
                    let fn_name = case_to_fn
                        .get(&case.case_ident)
                        .cloned()
                        .unwrap_or_default();
                    if is_div || confirmed_fns.insert(fn_name) {
                        selected.push(case.clone());
                    }
                }
                selected
            };

        let confirm_chunk_size = options
            .confirm_chunk_size
            .clamp(1, ITREE_MAX_CONFIRM_CHUNK_SIZE);
        let confirm_stage = run_isolated_lean_stage(
            "ItreeDiffBatchConfirm",
            &confirm_cases,
            confirm_chunk_size,
            lean_jobs,
            batch_case_ident,
            &case_to_fn,
            |label: &str, chunk: &[BatchTraceEvalCase]| {
                let src =
                    render_batch_trace_eval_lean_module(&format!("Proof.{label}"), chunk, false);
                run_itree_lean_module(&verify_dir, &anneal_dir, label, &src)?;
                Ok(chunk
                    .iter()
                    .map(|c| {
                        (
                            c.case_ident.clone(),
                            extract_itree_confirm_theorem(&src, &c.case_ident),
                        )
                    })
                    .collect::<BTreeMap<String, String>>())
            },
        );
        for err in &confirm_stage.errors {
            eprintln!("itree-difftest: Stage 2 Lean kernel confirmation failure: {err}");
        }
        for fn_name in &confirm_stage.failed_fns {
            if compared_fn_names.remove(fn_name) {
                eprintln!("itree-difftest: `{fn_name}` not compared: lean_confirm_failed");
                *not_compared_reasons
                    .entry("lean_confirm_failed".to_string())
                    .or_insert(0) += 1;
            }
        }
        let confirmed_theorems: BTreeMap<String, String> = confirm_stage.results;
        batch_cases.retain(|c| {
            case_to_fn
                .get(&c.case_ident)
                .is_some_and(|f| compared_fn_names.contains(f))
        });
        if batch_cases.is_empty() {
            return Err(format!(
                "all ITree candidates failed Stage 2 Lean kernel confirmation: {}",
                confirm_stage
                    .errors
                    .first()
                    .map(String::as_str)
                    .unwrap_or("no confirmation output")
            ));
        }

        let distinct_traces_checked = batch_cases.len();
        let total_traces_executed: usize = compared_fn_names
            .iter()
            .filter_map(|f| raw_trace_count_by_fn.get(f))
            .sum();
        per_candidate_distinct_traces.retain(|f, _| compared_fn_names.contains(f));

        let mut obs_path_set = MirObsPathSet::new();
        let mut obs_path_signatures_set = BTreeSet::new();
        for fn_name in &compared_fn_names {
            if let Some(records) = obs_records_by_fn.get(fn_name) {
                for (key, args) in records {
                    obs_path_set.record_execution(key.clone(), args.clone());
                }
            }
            if let Some(sigs) = obs_sigs_by_fn.get(fn_name) {
                obs_path_signatures_set.extend(sigs.iter().cloned());
            }
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
            let case_kernel_confirmed = confirmed_theorems.contains_key(&case.case_ident);
            if case_kernel_confirmed {
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
                if case_kernel_confirmed {
                    kernel_confirmed_divergences += 1;
                }
                diverged_fn_names.insert(fn_name.clone());

                if let Some((cand, _staged)) = cand_meta.get(&fn_name) {
                    let (mir_neighborhood, checked_mir_source) =
                        extract_mir_neighborhood(&staging_dir, &case.config.root_mir_module);
                    let kernel_confirm_theorem = confirmed_theorems
                        .get(&case.case_ident)
                        .cloned()
                        .unwrap_or_default();
                    let finding_id = format!("finding_{:04}_{}", findings.len(), case.case_ident);
                    findings.push(ItreeFindingBundle {
                        finding_id,
                        fn_name: fn_name.clone(),
                        case_ident: case.case_ident.clone(),
                        seed_index: cand.seed_index,
                        applied_mutators: cand.applied_mutators.clone(),
                        original_mutator_chain: cand.applied_mutators.clone(),
                        minimized_mutator_chain: cand.applied_mutators.clone(),
                        shrink_evaluations: 0,
                        executed_oracle_runs: 0,
                        shrink_status: String::new(),
                        diag_tag: tag,
                        diag_repr,
                        trace_hex: encode_recorded_raw_trace_hex(&case.trace),
                        kernel_confirmed: case_kernel_confirmed,
                        kernel_confirm_theorem,
                        mir_neighborhood,
                        checked_mir_source,
                        checked_mir_module: case.config.root_mir_module.clone(),
                        candidate_source: cand.source.clone(),
                        repro_path: None,
                    });
                }
            }
        }

        let compared_candidates = compared_fn_names.len();
        let diverge_candidates = diverged_fn_names.len();
        let agree_candidates = compared_candidates.saturating_sub(diverge_candidates);
        let not_compared_candidates = total_candidates.saturating_sub(compared_candidates);
        let elapsed_ms = start.elapsed().as_secs_f64() * 1000.0;

        Ok(ItreeCampaignEvalReport {
            mode: mode.to_string(),
            seed,
            batches: batch_count,
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
            not_compared_reasons,
            mutator_applications,
            obs_path_signatures: obs_path_signatures_set.into_iter().collect(),
            findings,
            elapsed_ms,
        })
    })();

    release_itree_staging_dir(&staging_dir);
    eval_res
}

/// Outcome of attempting to shrink a divergent ITree candidate's mutator chain.
pub type ItreeShrinkStatus = MutatorChainShrinkStatus;

/// The part of an ITree finding that a reduction of its candidate must
/// reproduce: the `TraceReplayDiag` tag and at least the original's kernel
/// confirmation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ItreeDiscrepancySignature {
    /// `TraceReplayDiag.tagName` of the finding's trace (never `"ok"`).
    pub diag_tag: String,
    /// Whether the Lean 4 kernel confirmed the finding's trace.
    pub kernel_confirmed: bool,
}

impl ItreeDiscrepancySignature {
    /// Signature of `finding`.
    pub fn of_finding(finding: &ItreeFindingBundle) -> Self {
        Self {
            diag_tag: finding.diag_tag.clone(),
            kernel_confirmed: finding.kernel_confirmed,
        }
    }

    /// Whether `trace` reproduces this signature: it diverges with the same tag,
    /// and the kernel confirmed it if the kernel confirmed the original.
    pub fn matches(&self, trace: &ItreeTraceVerdict) -> bool {
        trace.diag_tag != "ok"
            && trace.diag_tag == self.diag_tag
            && (trace.kernel_confirmed || !self.kernel_confirmed)
    }
}

/// One divergent trace of an ITree candidate as judged by the Lean `TraceCheck`
/// oracle, with the artifacts that a finding bundle records for it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ItreeTraceVerdict {
    /// Lean case identifier of the trace.
    pub case_ident: String,
    /// `TraceReplayDiag.tagName` reported by Lean.
    pub diag_tag: String,
    /// Full Lean `reprStr` of the `TraceReplayDiag` value.
    pub diag_repr: String,
    /// Encoded hex line of the trace.
    pub trace_hex: String,
    /// Whether the Lean 4 kernel confirmed the trace's diagnosis.
    pub kernel_confirmed: bool,
    /// Kernel-checked theorems about the trace.
    pub kernel_confirm_theorem: String,
    /// Root `Mir` module checked against the trace.
    pub checked_mir_module: String,
    /// Extracted neighborhood of `checked_mir_module`.
    pub mir_neighborhood: String,
    /// Full Lean source of `checked_mir_module`.
    pub checked_mir_source: String,
}

impl ItreeTraceVerdict {
    fn of_finding(finding: &ItreeFindingBundle) -> Self {
        Self {
            case_ident: finding.case_ident.clone(),
            diag_tag: finding.diag_tag.clone(),
            diag_repr: finding.diag_repr.clone(),
            trace_hex: finding.trace_hex.clone(),
            kernel_confirmed: finding.kernel_confirmed,
            kernel_confirm_theorem: finding.kernel_confirm_theorem.clone(),
            checked_mir_module: finding.checked_mir_module.clone(),
            mir_neighborhood: finding.mir_neighborhood.clone(),
            checked_mir_source: finding.checked_mir_source.clone(),
        }
    }
}

/// The live oracle's judgment of one compared ITree candidate program.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ItreeCandidateEvaluation {
    /// Every trace of the candidate whose `TraceReplayDiag` tag is not `"ok"`,
    /// in case order; traces that replayed with `"ok"` are omitted.
    pub divergent_traces: Vec<ItreeTraceVerdict>,
}

/// Result of shrinking a divergent [`GeneratedItreeCandidate`]'s mutator chain.
#[derive(Debug, Clone)]
pub struct ItreeCandidateShrinkResult {
    /// Original mutator sequence before shrinking.
    pub original_mutator_chain: Vec<String>,
    /// Mutator sequence of `minimized_candidate`: 1-minimal when `status` is
    /// `Minimized` or `AlreadyOneMinimal`, and the original sequence when
    /// shrinking did not reduce it.
    pub minimized_mutator_chain: Vec<String>,
    /// Number of shrinker predicate evaluations on proper subsequences of the
    /// original chain (each one a replay followed by the strict compile
    /// pre-check and, if that passes, an oracle query). The full chain is never
    /// re-evaluated: its divergence is the original finding.
    pub shrink_evaluations: usize,
    /// Number of oracle queries (`eval_fn` calls) made while shrinking.
    pub oracle_evaluations: usize,
    /// Number of replayed subsequences rejected by the compile pre-check without
    /// querying the oracle.
    pub compile_rejections: usize,
    /// Number of oracle queries that actually executed the oracle. Equals
    /// `oracle_evaluations` unless the evaluator is memoized ([`MemoizedOracle`]).
    pub executed_oracle_runs: usize,
    /// Number of oracle queries that produced no judgment (the candidate was not
    /// compared or the pipeline failed). Any failure makes `status`
    /// [`MutatorChainShrinkStatus::Inconclusive`].
    pub oracle_failures: usize,
    /// Whether shrinking ran and what it concluded.
    pub status: ItreeShrinkStatus,
    /// Shortest candidate that the oracle confirmed to reproduce the signature
    /// (the original candidate when shrinking did not reduce the chain).
    pub minimized_candidate: GeneratedItreeCandidate,
    /// First trace of `minimized_candidate` that reproduced the signature, when
    /// shrinking reduced the chain.
    pub minimized_trace: Option<ItreeTraceVerdict>,
    /// All divergent traces of `minimized_candidate` that reproduced the
    /// signature, in evaluation order, when shrinking reduced the chain.
    pub minimized_traces: Vec<ItreeTraceVerdict>,
}

impl ItreeCandidateShrinkResult {
    /// Whether `minimized_candidate` has a strictly shorter mutator chain than
    /// the original candidate.
    pub fn is_reduced(&self) -> bool {
        self.minimized_mutator_chain.len() < self.original_mutator_chain.len()
    }

    /// Pick the minimized trace from this shrink result that best corresponds to
    /// `finding` (the `ordinal`-th finding of its candidate and signature):
    /// prefers an identical `trace_hex`, then the `ordinal`-th matching trace,
    /// and finally `minimized_trace`.
    pub fn select_trace_for_finding(
        &self,
        finding: &ItreeFindingBundle,
        ordinal: usize,
    ) -> Option<&ItreeTraceVerdict> {
        self.minimized_traces
            .iter()
            .find(|t| t.trace_hex == finding.trace_hex)
            .or_else(|| self.minimized_traces.get(ordinal))
            .or(self.minimized_trace.as_ref())
    }
}

fn unshrunk_itree_result(
    cand: &GeneratedItreeCandidate,
    status: ItreeShrinkStatus,
    (shrink_evaluations, oracle_evaluations, compile_rejections, oracle_failures): (
        usize,
        usize,
        usize,
        usize,
    ),
) -> ItreeCandidateShrinkResult {
    ItreeCandidateShrinkResult {
        original_mutator_chain: cand.applied_mutators.clone(),
        minimized_mutator_chain: cand.applied_mutators.clone(),
        shrink_evaluations,
        oracle_evaluations,
        compile_rejections,
        executed_oracle_runs: oracle_evaluations,
        oracle_failures,
        status,
        minimized_candidate: cand.clone(),
        minimized_trace: None,
        minimized_traces: Vec::new(),
    }
}

/// Core of [`minimize_itree_candidate_mutations_with`] with an injectable compile
/// pre-check `compile_fn` (so unit tests can exercise compile rejection without
/// spawning `rustc`).
///
/// Shrinking runs [`shrink_mutation_chain_detailed`] over the candidate's
/// recorded mutation passes ([`reconstruct_itree_mutation_steps`] over `seeds`,
/// the seeds the candidate was generated from) with the predicate "the replayed
/// subsequence passes `compile_fn`, the oracle judges it, and one of its
/// divergent traces matches `signature`". The unmutated seed `[]` is evaluated
/// like any other subsequence. Shrinking is skipped (status
/// `SkippedReplayMismatch`, with no compile check or oracle query) unless
/// replaying the full recorded chain reproduces the candidate byte for byte
/// with zero `unsafe` tokens ([`itree_candidate_replay_is_faithful`]), and
/// skipped as `SkippedNotApplicable` for identity candidates and non-divergent
/// signatures.
pub fn minimize_itree_candidate_mutations_with_compile_check<C, F>(
    cand: &GeneratedItreeCandidate,
    seeds: &[&str],
    signature: &ItreeDiscrepancySignature,
    compile_fn: C,
    eval_fn: F,
) -> ItreeCandidateShrinkResult
where
    C: FnMut(&GeneratedItreeCandidate) -> bool,
    F: FnMut(&GeneratedItreeCandidate) -> Option<ItreeCandidateEvaluation>,
{
    if cand.applied_mutators.is_empty() || signature.diag_tag == "ok" {
        return unshrunk_itree_result(cand, ItreeShrinkStatus::SkippedNotApplicable, (0, 0, 0, 0));
    }
    let Some((base, steps)) = reconstruct_itree_mutation_steps(cand, seeds) else {
        return unshrunk_itree_result(cand, ItreeShrinkStatus::SkippedReplayMismatch, (0, 0, 0, 0));
    };
    minimize_itree_recorded_mutations_with_compile_check(
        cand, &base, &steps, signature, compile_fn, eval_fn,
    )
}

/// [`minimize_itree_candidate_mutations_with_compile_check`] for a candidate
/// whose mutation history (`base` seed and recorded `steps`) the caller already
/// has, for example a chain longer than [`crate::mutators_itree::generate_itree_batch`]
/// draws. The history must reproduce `cand` byte for byte
/// ([`itree_candidate_replay_is_faithful`]); otherwise shrinking is skipped
/// (`SkippedReplayMismatch`) with no compile check or oracle query.
pub fn minimize_itree_recorded_mutations_with_compile_check<C, F>(
    cand: &GeneratedItreeCandidate,
    base: &syn::File,
    steps: &[ItreeMutationStep],
    signature: &ItreeDiscrepancySignature,
    mut compile_fn: C,
    mut eval_fn: F,
) -> ItreeCandidateShrinkResult
where
    C: FnMut(&GeneratedItreeCandidate) -> bool,
    F: FnMut(&GeneratedItreeCandidate) -> Option<ItreeCandidateEvaluation>,
{
    if cand.applied_mutators.is_empty() || signature.diag_tag == "ok" {
        return unshrunk_itree_result(cand, ItreeShrinkStatus::SkippedNotApplicable, (0, 0, 0, 0));
    }
    if !itree_candidate_replay_is_faithful(cand, base, steps) {
        return unshrunk_itree_result(cand, ItreeShrinkStatus::SkippedReplayMismatch, (0, 0, 0, 0));
    }

    let full_len = steps.len();
    let mut oracle_evaluations = 0usize;
    let mut compile_rejections = 0usize;
    let mut oracle_failures = 0usize;
    // Last accepted reduction, keyed by the original pass indices it retains.
    let mut last_accepted: Option<(
        Vec<usize>,
        GeneratedItreeCandidate,
        Vec<ItreeTraceVerdict>,
    )> = None;

    let outcome = shrink_mutation_chain_detailed(steps, |sub_steps: &[ItreeMutationStep]| {
        if sub_steps.len() == full_len {
            // The faithful full replay is byte-identical to `cand`, whose
            // divergence is the original finding.
            return true;
        }
        let sub_cand = replay_itree_mutation_steps(cand, base, sub_steps);
        if contains_unsafe_token(&sub_cand.source) || !compile_fn(&sub_cand) {
            compile_rejections += 1;
            return false;
        }
        oracle_evaluations += 1;
        let Some(evaluation) = eval_fn(&sub_cand) else {
            oracle_failures += 1;
            return false;
        };
        let matching_traces: Vec<ItreeTraceVerdict> = evaluation
            .divergent_traces
            .iter()
            .filter(|t| signature.matches(t))
            .cloned()
            .collect();
        if matching_traces.is_empty() {
            return false;
        }
        let kept: Vec<usize> = sub_steps.iter().map(|s| s.pass_index).collect();
        last_accepted = Some((kept, sub_cand, matching_traces));
        true
    });

    // The initial full-chain predicate call is free (see above) and not counted.
    let shrink_evaluations = outcome.predicate_evaluations.saturating_sub(1);
    let minimized_indices: Vec<usize> =
        outcome.minimized_steps.iter().map(|s| s.pass_index).collect();
    if minimized_indices.len() < full_len
        && let Some((kept, min_cand, traces)) = last_accepted
        && kept == minimized_indices
    {
        return ItreeCandidateShrinkResult {
            original_mutator_chain: cand.applied_mutators.clone(),
            minimized_mutator_chain: min_cand.applied_mutators.clone(),
            shrink_evaluations,
            oracle_evaluations,
            compile_rejections,
            executed_oracle_runs: oracle_evaluations,
            oracle_failures,
            status: ItreeShrinkStatus::of_completed_shrink(true, oracle_failures),
            minimized_candidate: min_cand,
            minimized_trace: traces.first().cloned(),
            minimized_traces: traces,
        };
    }
    unshrunk_itree_result(
        cand,
        ItreeShrinkStatus::of_completed_shrink(false, oracle_failures),
        (shrink_evaluations, oracle_evaluations, compile_rejections, oracle_failures),
    )
}

/// The compile pre-check that ITree shrinking runs on every replayed reduction
/// before the trace + Lean oracle: everything that [`compile_itree_candidates`]
/// requires of generated candidates (zero `unsafe` tokens, a clean compile under
/// `#![forbid(unsafe_code)]` at both `-C opt-level=0` and `-C opt-level=2`, and
/// a clean `anneal-mir-instrument` compile of the
/// `#[anneal_trace::external]`-annotated copy at both levels), plus a stageable
/// `kernel_step` root function.
///
/// A reduction that fails the pre-check is rejected without an oracle query; one
/// that passes is a program the batch evaluation would compare, so the oracle
/// reporting it as not compared is a genuine oracle failure.
pub fn itree_candidate_passes_strict_compile(cand: &GeneratedItreeCandidate) -> bool {
    if contains_unsafe_token(&cand.source)
        || stage_itree_candidate_items(&cand.source, "shrink__", "kernel_step").is_err()
    {
        return false;
    }
    let Ok((annotated, _)) = annotate_itree_external_callees(&cand.source, "kernel_step") else {
        return false;
    };
    let safe_src = format!("#![forbid(unsafe_code)]\n{}", cand.source);
    let inst_src =
        format!("#![feature(register_tool)]\n#![register_tool(anneal_trace)]\n{annotated}");
    compile_rust_strict_opt("shrink", "0", &safe_src)
        && compile_rust_strict_opt("shrink", "2", &safe_src)
        && compile_rust_mir_instrumented("shrink_inst", "0", &inst_src)
        && compile_rust_mir_instrumented("shrink_inst", "2", &inst_src)
}

/// Minimize a divergent [`GeneratedItreeCandidate`]'s mutator chain using a
/// caller-supplied oracle `eval_fn`, pre-checking every replayed reduction with
/// [`itree_candidate_passes_strict_compile`] (memoized by source).
pub fn minimize_itree_candidate_mutations_with<F>(
    cand: &GeneratedItreeCandidate,
    seeds: &[&str],
    signature: &ItreeDiscrepancySignature,
    eval_fn: F,
) -> ItreeCandidateShrinkResult
where
    F: FnMut(&GeneratedItreeCandidate) -> Option<ItreeCandidateEvaluation>,
{
    let mut compile_memo = MemoizedOracle::new(itree_candidate_passes_strict_compile);
    minimize_itree_candidate_mutations_with_compile_check(
        cand,
        seeds,
        signature,
        |sub_cand| compile_memo.eval(sub_cand.source.clone(), sub_cand),
        eval_fn,
    )
}

/// Where an ITree finding's candidate sits in the evaluation that produced it,
/// so that the live oracle can re-run reductions of it faithfully.
#[derive(Debug, Clone, Copy)]
pub struct ItreeShrinkContext<'a> {
    /// Evaluation mode (`"identity"` or `"seeded"`).
    pub mode: &'a str,
    /// Batch seed (it seeds every candidate's native trial inputs).
    pub seed: u64,
    /// The evaluated batches.
    pub batches: &'a [Vec<GeneratedItreeCandidate>],
    /// Target candidate count per batch.
    pub batch_size: usize,
    /// Options of the evaluation, including any negative-control MIR mutations
    /// and root-module swaps.
    pub options: &'a ItreeEvalOptions,
    /// Batch index of the candidate.
    pub b_idx: usize,
    /// Index of the candidate within its batch.
    pub c_idx: usize,
}

/// Judge `sub` (a reduction of the candidate at `ctx`'s position) with the live
/// ITree oracle: compile, capture, native trace collection, and Lean
/// `TraceCheck` probing and kernel confirmation, exactly as
/// [`evaluate_itree_batches_with_options`] judges batch candidates.
///
/// `sub` is staged under the original candidate's item prefix, so `ctx`'s MIR
/// mutations and root-module swaps that target it apply unchanged. The
/// evaluation also stages (as `capture_only`) the original candidates whose MIR
/// modules the candidate's root swap names; MIR mutations of any other candidate
/// cannot affect it and are dropped, and a requested mutation whose pattern the
/// reduced program no longer contains is skipped (the injected fault does not
/// apply to it). Returns an error when `sub` could not be compared.
pub fn evaluate_itree_candidate_live(
    sub: &GeneratedItreeCandidate,
    ctx: &ItreeShrinkContext<'_>,
) -> Result<ItreeCandidateEvaluation, String> {
    let target = ItreeEvalEntry {
        b_idx: ctx.b_idx,
        c_idx: ctx.c_idx,
        cand: sub,
        capture_only: false,
    };
    let target_fn = target.root_fn_name();
    let root_mir_swaps: Vec<(String, String)> = ctx
        .options
        .root_mir_swaps
        .iter()
        .filter(|(staged_fn, _)| *staged_fn == target_fn)
        .cloned()
        .collect();
    let mut entries = vec![target];
    for (_, module) in &root_mir_swaps {
        let staged_item = module.strip_prefix("Mir.ItreeDiffStaged.").unwrap_or(module);
        for mut other in batch_entries(ctx.batches) {
            let already_staged = entries
                .iter()
                .any(|e| (e.b_idx, e.c_idx) == (other.b_idx, other.c_idx));
            if !already_staged && staged_item.starts_with(&other.prefix()) {
                other.capture_only = true;
                entries.push(other);
            }
        }
    }
    let prefixes: Vec<String> = entries.iter().map(ItreeEvalEntry::prefix).collect();
    let options = ItreeEvalOptions {
        trials_per_candidate: ctx.options.trials_per_candidate,
        confirm_chunk_size: ctx.options.confirm_chunk_size,
        anneal_repo_root: ctx.options.anneal_repo_root.clone(),
        findings_dir: None,
        mir_mutations: ctx
            .options
            .mir_mutations
            .iter()
            .filter(|(staged_fn, _, _)| prefixes.iter().any(|p| staged_fn.starts_with(p.as_str())))
            .cloned()
            .collect(),
        root_mir_swaps,
    };
    let report = evaluate_itree_entries(
        ctx.mode,
        ctx.seed,
        ctx.batches.len(),
        ctx.batch_size,
        &entries,
        &options,
        MirMutationPolicy::SkipAbsent,
    )?;
    if !report.per_candidate_distinct_traces.contains_key(&target_fn) {
        return Err(format!(
            "`{target_fn}` was not compared (not-compared reasons: {:?})",
            report.not_compared_reasons
        ));
    }
    Ok(ItreeCandidateEvaluation {
        divergent_traces: report
            .findings
            .iter()
            .filter(|f| f.fn_name == target_fn)
            .map(ItreeTraceVerdict::of_finding)
            .collect(),
    })
}

/// Minimize the mutator chain of `cand`, the divergent candidate at `ctx`'s
/// position, against the live ITree oracle ([`evaluate_itree_candidate_live`]),
/// with a [`MemoizedOracle`] keyed by candidate source so that repeated queries
/// of one program never re-run the pipeline (`executed_oracle_runs` counts only
/// the runs that executed).
pub fn minimize_itree_candidate_mutations(
    cand: &GeneratedItreeCandidate,
    seeds: &[&str],
    signature: &ItreeDiscrepancySignature,
    ctx: &ItreeShrinkContext<'_>,
) -> ItreeCandidateShrinkResult {
    let eval_live = |sub: &GeneratedItreeCandidate| -> Option<ItreeCandidateEvaluation> {
        match evaluate_itree_candidate_live(sub, ctx) {
            Ok(evaluation) => Some(evaluation),
            Err(e) => {
                eprintln!(
                    "itree-difftest: shrink oracle run failed for b{}_c{} ({} mutators): {}",
                    ctx.b_idx,
                    ctx.c_idx,
                    sub.applied_mutators.len(),
                    truncate_lean_diag(&e)
                );
                None
            }
        }
    };
    let mut memo = MemoizedOracle::new(eval_live);
    let mut res = minimize_itree_candidate_mutations_with(cand, seeds, signature, |sub| {
        memo.eval(sub.source.clone(), sub)
    });
    res.executed_oracle_runs = memo.executed_runs;
    res
}

/// Shrink every finding of `report` against the live oracle and refresh the
/// finding's repro-facing artifacts (`repro.rs` source, trace, diagnosis, MIR,
/// and kernel theorems) from the run that accepted the minimized candidate.
///
/// Findings of one candidate share a compile cache and a per-candidate live
/// oracle cache, and findings with the same `(fn_name, diag_tag, kernel_confirmed)`
/// signature share one shrink while selecting distinct minimized traces via
/// [`ItreeCandidateShrinkResult::select_trace_for_finding`].
fn shrink_itree_findings(
    report: &mut ItreeCampaignEvalReport,
    mode: &str,
    seed: u64,
    batches: &[Vec<GeneratedItreeCandidate>],
    batch_size: usize,
    options: &ItreeEvalOptions,
) {
    let entries = batch_entries(batches);
    let mut compile_memo = MemoizedOracle::new(itree_candidate_passes_strict_compile);
    let mut eval_cache_by_cand: BTreeMap<String, BTreeMap<String, Option<ItreeCandidateEvaluation>>> =
        BTreeMap::new();
    let mut shrinks: BTreeMap<(String, String, bool), ItreeCandidateShrinkResult> = BTreeMap::new();
    let mut ordinals: BTreeMap<(String, String, bool), usize> = BTreeMap::new();
    for finding in &mut report.findings {
        let Some(entry) = entries.iter().find(|e| e.root_fn_name() == finding.fn_name) else {
            finding.shrink_status = format!(
                "skipped_shrinker_error: `{}` names no evaluated candidate",
                finding.fn_name
            );
            continue;
        };
        let signature = ItreeDiscrepancySignature::of_finding(finding);
        let key = (
            finding.fn_name.clone(),
            signature.diag_tag.clone(),
            signature.kernel_confirmed,
        );
        let ord = {
            let count = ordinals.entry(key.clone()).or_insert(0);
            let cur = *count;
            *count += 1;
            cur
        };
        let res = shrinks.entry(key).or_insert_with(|| {
            let ctx = ItreeShrinkContext {
                mode,
                seed,
                batches,
                batch_size,
                options,
                b_idx: entry.b_idx,
                c_idx: entry.c_idx,
            };
            let cand_cache = eval_cache_by_cand
                .entry(finding.fn_name.clone())
                .or_default();
            let mut distinct_queried: BTreeSet<String> = BTreeSet::new();
            let mut sr = minimize_itree_candidate_mutations_with_compile_check(
                entry.cand,
                ITREE_SAFE_SEEDS,
                &signature,
                |sub| compile_memo.eval(sub.source.clone(), sub),
                |sub| {
                    distinct_queried.insert(sub.source.clone());
                    if let Some(cached) = cand_cache.get(&sub.source) {
                        return cached.clone();
                    }
                    let evaluated = match evaluate_itree_candidate_live(sub, &ctx) {
                        Ok(evaluation) => Some(evaluation),
                        Err(e) => {
                            eprintln!(
                                "itree-difftest: shrink oracle run failed for b{}_c{} ({} mutators): {}",
                                ctx.b_idx,
                                ctx.c_idx,
                                sub.applied_mutators.len(),
                                truncate_lean_diag(&e)
                            );
                            None
                        }
                    };
                    cand_cache.insert(sub.source.clone(), evaluated.clone());
                    evaluated
                },
            );
            sr.executed_oracle_runs = distinct_queried.len();
            sr
        });
        finding.original_mutator_chain = res.original_mutator_chain.clone();
        finding.minimized_mutator_chain = res.minimized_mutator_chain.clone();
        finding.shrink_evaluations = res.shrink_evaluations;
        finding.executed_oracle_runs = res.executed_oracle_runs;
        finding.shrink_status = res.status.slug().to_string();
        if res.is_reduced()
            && let Some(trace) = res.select_trace_for_finding(finding, ord)
        {
            finding.applied_mutators = res.minimized_mutator_chain.clone();
            finding.candidate_source = res.minimized_candidate.source.clone();
            finding.case_ident = trace.case_ident.clone();
            finding.diag_repr = trace.diag_repr.clone();
            finding.trace_hex = trace.trace_hex.clone();
            finding.kernel_confirmed = trace.kernel_confirmed;
            finding.kernel_confirm_theorem = trace.kernel_confirm_theorem.clone();
            finding.checked_mir_module = trace.checked_mir_module.clone();
            finding.mir_neighborhood = trace.mir_neighborhood.clone();
            finding.checked_mir_source = trace.checked_mir_source.clone();
        }
    }
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
        let has_branches = trace
            .events
            .iter()
            .any(|ev| matches!(ev, RecordedEvent::Branch { .. }));
        let mut case = BatchTraceEvalCase {
            case_ident: "repro_case".to_string(),
            config: TraceCheckModuleConfig {
                module_namespace: "Proof.ItreeDiffRepro".to_string(),
                root_mir_module: root_mir_module.clone(),
                callee_sig_modules: callee_sig_modules.clone(),
                inlined_callee_modules: Vec::new(),
                init_mem_expr: None,
                fuel: ITREE_TRACE_CHECK_FUEL,
                check_branches: has_branches,
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

    release_itree_staging_dir(&staging_dir);
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

fn render_string_list_json(items: &[String], indent: usize) -> String {
    if items.is_empty() {
        return "[]".to_string();
    }
    let pad = " ".repeat(indent);
    let inner_pad = " ".repeat(indent + 2);
    let rows: Vec<String> = items
        .iter()
        .map(|s| format!("{inner_pad}{}", json_escape(s)))
        .collect();
    format!("[\n{}\n{pad}]", rows.join(",\n"))
}

/// Render an [`ItreeFindingBundle`] as a JSON object at indentation `indent`.
pub fn render_itree_finding_bundle_json(finding: &ItreeFindingBundle, indent: usize) -> String {
    let pad = " ".repeat(indent);
    let inner = " ".repeat(indent + 2);
    let chain_json = |chain: &[String]| {
        chain
            .iter()
            .map(|m| json_escape(m))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let mutators_json = chain_json(&finding.applied_mutators);
    let orig_mutators_json = chain_json(&finding.original_mutator_chain);
    let min_mutators_json = chain_json(&finding.minimized_mutator_chain);
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
         {inner}\"original_mutator_chain\": [{orig_mutators_json}],\n\
         {inner}\"minimized_mutator_chain\": [{min_mutators_json}],\n\
         {inner}\"shrink_evaluations\": {},\n\
         {inner}\"executed_oracle_runs\": {},\n\
         {inner}\"shrink_status\": {},\n\
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
        finding.shrink_evaluations,
        finding.executed_oracle_runs,
        json_escape(&finding.shrink_status),
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
         \x20 \"not_compared_reasons\": {},\n\
         \x20 \"mutator_applications\": {},\n\
         \x20 \"obs_path_signatures\": {},\n\
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
        render_usize_map_json(&report.not_compared_reasons, 2),
        render_usize_map_json(&report.mutator_applications, 2),
        render_string_list_json(&report.obs_path_signatures, 2),
        report.findings.len(),
        report.elapsed_ms,
    )
}

/// Render the human-readable Markdown report for a completed
/// [`ItreeCampaignEvalReport`].
pub fn render_itree_eval_report_markdown(report: &ItreeCampaignEvalReport) -> String {
    let mut out = String::new();
    out.push_str("# `itree-difftest` Differential Oracle Report\n\n");
    out.push_str("- **Oracle comparison**: PERFORMED (`anneal-mir-instrument` binary MIR execution at `-O0` and `-O2` vs. Anneal `TraceCheck` `diagnoseRawByteTraceFullBounded` + Lean 4 kernel confirmation)\n");
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

    out.push_str("\n## Not-Compared Candidates by Reason\n\n");
    out.push_str("| Reason | Candidates |\n| :--- | ---: |\n");
    for (reason, count) in &report.not_compared_reasons {
        out.push_str(&format!("| `{reason}` | {count} |\n"));
    }

    out.push_str("\n## Mutator Applications\n\n");
    out.push_str("| Mutator | Applications |\n| :--- | ---: |\n");
    for (name, count) in &report.mutator_applications {
        out.push_str(&format!("| `{name}` | {count} |\n"));
    }

    if !report.findings.is_empty() {
        out.push_str("\n## Divergences Detected\n\n");
        out.push_str(
            "| Finding ID | Function | Case | `TraceReplayDiag` | Kernel Confirmed | Shrink |\n",
        );
        out.push_str("| :--- | :--- | :--- | :--- | :--- | :--- |\n");
        for f in &report.findings {
            out.push_str(&format!(
                "| `{}` | `{}` | `{}` | `{}` | `{}` | `{}` ({} -> {} mutators) |\n",
                f.finding_id,
                f.fn_name,
                f.case_ident,
                f.diag_tag,
                f.kernel_confirmed,
                f.shrink_status,
                f.original_mutator_chain.len(),
                f.minimized_mutator_chain.len()
            ));
        }
    }

    out
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Duration;

    use super::*;
    use crate::mutators_itree::{generate_itree_batch, generate_itree_identity_batch};

    const GIB_KIB: u64 = 1024 * 1024;

    fn ident(case: &String) -> &str {
        case
    }

    /// `(cases, case_to_fn)` with `n` cases `case_<fn>_t<i>` per `(fn, n)`.
    fn stage_fixture(fns: &[(&str, usize)]) -> (Vec<String>, BTreeMap<String, String>) {
        let mut cases = Vec::new();
        let mut case_to_fn = BTreeMap::new();
        for (fn_name, n) in fns {
            for t in 0..*n {
                let id = format!("case_{fn_name}_t{t}");
                case_to_fn.insert(id.clone(), (*fn_name).to_string());
                cases.push(id);
            }
        }
        (cases, case_to_fn)
    }

    fn ok_all(chunk: &[String]) -> Result<BTreeMap<String, usize>, String> {
        Ok(chunk.iter().map(|c| (c.clone(), c.len())).collect())
    }

    #[test]
    fn lean_jobs_follow_memory_thresholds() {
        // 32 GiB capsule: always 1 worker, even with > 24 GiB available.
        assert_eq!(
            itree_lean_jobs_for_memory(Some(32 * GIB_KIB), Some(30 * GIB_KIB)),
            1
        );
        assert_eq!(
            itree_lean_jobs_for_memory(Some(36 * GIB_KIB), Some(35 * GIB_KIB)),
            1
        );
        // Little available memory on a large host: 1 worker.
        assert_eq!(
            itree_lean_jobs_for_memory(Some(128 * GIB_KIB), Some(20 * GIB_KIB)),
            1
        );
        // Up to 64 GiB total: at most 2 workers.
        assert_eq!(
            itree_lean_jobs_for_memory(Some(64 * GIB_KIB), Some(60 * GIB_KIB)),
            2
        );
        assert_eq!(
            itree_lean_jobs_for_memory(Some(48 * GIB_KIB), Some(40 * GIB_KIB)),
            2
        );
        // Large host with < 48 GiB available: 2 workers.
        assert_eq!(
            itree_lean_jobs_for_memory(Some(128 * GIB_KIB), Some(40 * GIB_KIB)),
            2
        );
        // Large host with plenty available: 4 workers.
        assert_eq!(
            itree_lean_jobs_for_memory(Some(128 * GIB_KIB), Some(100 * GIB_KIB)),
            4
        );
        assert_eq!(itree_lean_jobs_for_memory(None, None), 1);
        assert_eq!(itree_lean_jobs_for_memory(None, Some(10 * GIB_KIB)), 1);
    }

    #[test]
    fn meminfo_parsing_reads_total_and_available() {
        let meminfo =
            "MemTotal:       32862004 kB\nMemFree:         1000 kB\nMemAvailable:   18271744 kB\n";
        assert_eq!(
            parse_meminfo_kib(meminfo),
            (Some(32_862_004), Some(18_271_744))
        );
        assert_eq!(parse_meminfo_kib("garbage\n"), (None, None));
    }

    #[test]
    fn cgroup_limits_use_tightest_ancestor_headroom() {
        let root = std::env::temp_dir().join(format!(
            "anneal-itree-cgroup-test-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        let leaf = root.join("user.slice/app.slice/run-1.scope");
        fs::create_dir_all(&leaf).expect("create fake cgroup tree");
        // Root of the hierarchy: no memory.max (cgroup v2 root).
        // user.slice: 22 GiB max, 16 GiB used -> 6 GiB headroom (tightest).
        fs::write(
            root.join("user.slice/memory.max"),
            format!("{}\n", 22 * GIB_KIB * 1024),
        )
        .unwrap();
        fs::write(
            root.join("user.slice/memory.current"),
            format!("{}\n", 16 * GIB_KIB * 1024),
        )
        .unwrap();
        // app.slice: unlimited.
        fs::write(root.join("user.slice/app.slice/memory.max"), "max\n").unwrap();
        // Scope: 14 GiB max (tightest limit), 1 GiB used -> 13 GiB headroom.
        fs::write(
            leaf.join("memory.max"),
            format!("{}\n", 14 * GIB_KIB * 1024),
        )
        .unwrap();
        fs::write(leaf.join("memory.current"), format!("{}\n", GIB_KIB * 1024)).unwrap();

        let (limit, headroom) =
            cgroup_memory_limits_kib(&root, "0::/user.slice/app.slice/run-1.scope\n");
        assert_eq!(limit, Some(14 * GIB_KIB));
        assert_eq!(headroom, Some(6 * GIB_KIB));
        // cgroup v1-only or malformed input: no limits.
        assert_eq!(
            cgroup_memory_limits_kib(&root, "12:memory:/foo\n"),
            (None, None)
        );
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn obs_shape_hash_is_position_independent_but_path_sensitive() {
        let a = compute_itree_obs_shape_hash(
            "b0_c1__",
            &[1, 0],
            &[("itree_diff_staged::b0_c1__ext_oracle".to_string(), 1)],
        );
        let b = compute_itree_obs_shape_hash(
            "b3_c7__",
            &[1, 0],
            &[(
                "collector::itree_diff_staged::b3_c7__ext_oracle".to_string(),
                1,
            )],
        );
        assert_eq!(
            a, b,
            "candidate position / crate path must not affect signatures"
        );
        let other_branch = compute_itree_obs_shape_hash(
            "b0_c1__",
            &[0, 0],
            &[("itree_diff_staged::b0_c1__ext_oracle".to_string(), 1)],
        );
        let other_call_pos = compute_itree_obs_shape_hash(
            "b0_c1__",
            &[1, 0],
            &[("itree_diff_staged::b0_c1__ext_oracle".to_string(), 2)],
        );
        assert_ne!(a, other_branch);
        assert_ne!(a, other_call_pos);
        assert!(a.starts_with("b2e1h"), "unexpected shape hash format: {a}");
    }

    #[test]
    fn missing_trace_reasons_distinguish_collector_failure_and_opt_level_mismatch() {
        let native = NativeTraceCollection {
            traces_by_fn: BTreeMap::from([("ok_fn".to_string(), Vec::new())]),
            collect_failed: BTreeSet::from(["crashed_fn".to_string()]),
            opt_level_mismatch: BTreeSet::from(["flaky_fn".to_string()]),
            errors: Vec::new(),
        };
        assert_eq!(
            native.missing_trace_reason("flaky_fn"),
            "opt_level_trace_mismatch"
        );
        assert_eq!(
            native.missing_trace_reason("crashed_fn"),
            "trace_collect_failed"
        );
        assert_eq!(native.missing_trace_reason("ok_fn"), "empty_trace");
        for reason in [
            "opt_level_trace_mismatch",
            "trace_collect_failed",
            "empty_trace",
            "lean_build_failed",
        ] {
            assert!(
                ITREE_NOT_COMPARED_REASON_NAMES.contains(&reason),
                "`{reason}` must be a canonical not-compared reason"
            );
        }
    }

    #[test]
    fn isolated_lean_stage_bounds_concurrency_and_collects_all_results() {
        let (cases, case_to_fn) = stage_fixture(&[("f0", 5), ("f1", 5), ("f2", 5), ("f3", 5)]);
        let active = AtomicUsize::new(0);
        let peak = AtomicUsize::new(0);
        let calls = AtomicUsize::new(0);
        let stage = run_isolated_lean_stage(
            "T",
            &cases,
            3,
            2,
            ident,
            &case_to_fn,
            |_label: &str, chunk: &[String]| {
                let now = active.fetch_add(1, Ordering::SeqCst) + 1;
                peak.fetch_max(now, Ordering::SeqCst);
                calls.fetch_add(1, Ordering::SeqCst);
                std::thread::sleep(Duration::from_millis(10));
                active.fetch_sub(1, Ordering::SeqCst);
                ok_all(chunk)
            },
        );
        assert!(stage.failed_fns.is_empty(), "{:?}", stage.errors);
        assert!(stage.errors.is_empty());
        assert_eq!(stage.results.len(), 20);
        assert_eq!(calls.load(Ordering::SeqCst), 7, "ceil(20 / 3) chunks");
        let peak = peak.load(Ordering::SeqCst);
        assert!(
            (1..=2).contains(&peak),
            "peak concurrency {peak} > jobs (2)"
        );
    }

    #[test]
    fn isolated_lean_stage_isolates_only_the_failing_candidate() {
        // Chunks of 4: [a0 a1 a2 bad0] and [bad1 b0 b1 b2] both fail as a whole.
        let (cases, case_to_fn) = stage_fixture(&[("good_a", 3), ("bad", 2), ("good_b", 3)]);
        let labels = std::sync::Mutex::new(Vec::new());
        let stage = run_isolated_lean_stage(
            "ItreeDiffBatchConfirm",
            &cases,
            4,
            2,
            ident,
            &case_to_fn,
            |label: &str, chunk: &[String]| {
                labels.lock().unwrap().push(label.to_string());
                if chunk.iter().any(|c| case_to_fn[c] == "bad") {
                    Err("error: (kernel) deep recursion detected".to_string())
                } else {
                    ok_all(chunk)
                }
            },
        );
        assert_eq!(
            stage.failed_fns,
            BTreeSet::from(["bad".to_string()]),
            "only the failing candidate may be dropped"
        );
        assert_eq!(
            stage.results.len(),
            6,
            "all good_a / good_b cases recovered"
        );
        assert!(!stage.results.keys().any(|k| k.contains("_bad_")));
        assert!(stage.errors.iter().any(
            |e| e.contains("ItreeDiffBatchConfirmFallback_bad") && e.contains("deep recursion")
        ));
        let labels = labels.lock().unwrap();
        assert!(labels.contains(&"ItreeDiffBatchConfirmChunk0".to_string()));
        assert!(labels.contains(&"ItreeDiffBatchConfirmChunk1".to_string()));
        assert!(labels.contains(&"ItreeDiffBatchConfirmFallback_good_a".to_string()));
        assert!(labels.contains(&"ItreeDiffBatchConfirmFallback_good_b".to_string()));
    }

    #[test]
    fn isolated_lean_stage_never_treats_a_panicking_chunk_as_confirmed() {
        let (cases, case_to_fn) = stage_fixture(&[("p0", 2), ("p1", 2), ("bad", 2)]);
        // Chunks of 3: [p0 p0 p1] succeeds; [p1 bad bad] panics, so `p1` must be
        // recovered by its per-candidate fallback while `bad` stays failed.
        // Chunk workers panic for any chunk holding `bad`; the per-candidate
        // fallback panics for `bad` too, and succeeds for everyone else.
        let stage = run_isolated_lean_stage(
            "T",
            &cases,
            3,
            2,
            ident,
            &case_to_fn,
            |_label: &str, chunk: &[String]| {
                if chunk.iter().any(|c| case_to_fn[c] == "bad") {
                    panic!("simulated Lean worker panic");
                }
                ok_all(chunk)
            },
        );
        assert_eq!(stage.failed_fns, BTreeSet::from(["bad".to_string()]));
        assert_eq!(stage.results.len(), 4);
        assert!(stage.errors.iter().any(|e| e.contains("panicked")));
    }

    #[test]
    fn isolated_lean_stage_retries_incomplete_chunks() {
        let (cases, case_to_fn) = stage_fixture(&[("f0", 3), ("f1", 3)]);
        // Main chunks silently drop their last case (e.g. a truncated probe
        // output); per-candidate fallbacks return complete results.
        let stage = run_isolated_lean_stage(
            "T",
            &cases,
            4,
            1,
            ident,
            &case_to_fn,
            |label: &str, chunk: &[String]| {
                let mut out = ok_all(chunk)?;
                if label.contains("Chunk") {
                    let last = chunk.last().unwrap();
                    out.remove(last);
                }
                Ok(out)
            },
        );
        assert!(stage.failed_fns.is_empty(), "{:?}", stage.errors);
        assert_eq!(stage.results.len(), 6);
        assert!(stage.errors.iter().any(|e| e.contains("no result for")));
    }

    #[test]
    fn isolated_lean_stage_circuit_breaker_bounds_systematic_failures() {
        let fns: Vec<(String, usize)> = (0..10).map(|i| (format!("f{i}"), 2)).collect();
        let fn_refs: Vec<(&str, usize)> = fns.iter().map(|(f, n)| (f.as_str(), *n)).collect();
        let (cases, case_to_fn) = stage_fixture(&fn_refs);
        let calls = AtomicUsize::new(0);
        let stage = run_isolated_lean_stage(
            "T",
            &cases,
            4,
            1,
            ident,
            &case_to_fn,
            |_label: &str, _chunk: &[String]| -> Result<BTreeMap<String, usize>, String> {
                calls.fetch_add(1, Ordering::SeqCst);
                Err("lake: command not found".to_string())
            },
        );
        assert_eq!(stage.failed_fns.len(), 10);
        assert!(stage.results.is_empty());
        assert_eq!(
            calls.load(Ordering::SeqCst),
            5 + ITREE_FALLBACK_CIRCUIT_BREAKER,
            "5 chunks + {ITREE_FALLBACK_CIRCUIT_BREAKER} fallback attempts before tripping"
        );
        assert!(stage.errors.iter().any(|e| e.contains("skipped")));
    }

    // ---- Mutator-chain shrinking of ITree findings ----

    fn trace_verdict(case: &str, tag: &str, kernel_confirmed: bool) -> ItreeTraceVerdict {
        ItreeTraceVerdict {
            case_ident: case.to_string(),
            diag_tag: tag.to_string(),
            diag_repr: format!("TraceReplayDiag.{tag} (case {case})"),
            trace_hex: format!("hex-{case}"),
            kernel_confirmed,
            kernel_confirm_theorem: if kernel_confirmed {
                format!("theorem {case}_diag_tag : ... := by\n  rfl")
            } else {
                String::new()
            },
            checked_mir_module: format!("Mir.ItreeDiffStaged.{case}"),
            mir_neighborhood: format!("-- neighborhood of {case}"),
            checked_mir_source: format!("namespace Mir.ItreeDiffStaged.{case}\nend"),
        }
    }

    fn divergent(traces: Vec<ItreeTraceVerdict>) -> Option<ItreeCandidateEvaluation> {
        Some(ItreeCandidateEvaluation {
            divergent_traces: traces,
        })
    }

    fn outcome_mismatch_signature() -> ItreeDiscrepancySignature {
        ItreeDiscrepancySignature {
            diag_tag: "outcome_mismatch".to_string(),
            kernel_confirmed: true,
        }
    }

    /// Replays every subset of `steps` and maps each replayed source to its
    /// subset bitmask (bit `i` = pass `i` kept), asserting that the replays are
    /// pairwise distinct so a mock oracle can tell them apart.
    fn itree_subset_source_map(
        cand: &GeneratedItreeCandidate,
        base: &syn::File,
        steps: &[ItreeMutationStep],
    ) -> BTreeMap<String, u32> {
        let mut map = BTreeMap::new();
        for mask in 0u32..(1u32 << steps.len()) {
            let sub: Vec<ItreeMutationStep> = steps
                .iter()
                .enumerate()
                .filter(|(i, _)| (mask >> i) & 1 == 1)
                .map(|(_, s)| s.clone())
                .collect();
            let src = replay_itree_mutation_steps(cand, base, &sub).source;
            assert!(!contains_unsafe_token(&src), "subset {mask:#b} emitted `unsafe`");
            assert!(
                map.insert(src, mask).is_none(),
                "subset replays must be pairwise distinct"
            );
        }
        map
    }

    /// First generated candidate with exactly `n` passes.
    fn generated_itree_candidate_with_passes(n: usize) -> GeneratedItreeCandidate {
        for seed in [0xCAFE_1234u64, 0x3333_4444, 0x1111_2222, 0x9999_AAAA] {
            if let Some(c) = generate_itree_batch(ITREE_SAFE_SEEDS, 16, seed)
                .into_iter()
                .find(|c| c.applied_mutators.len() == n)
            {
                return c;
            }
        }
        panic!("no generated ITree candidate with {n} passes");
    }

    /// A candidate with a recorded 3-pass history (the generator draws at most 2
    /// passes): a generated 2-pass candidate's history plus a third
    /// `BranchLoopWeaver` pass, with the subset-to-bitmask map of its replays.
    fn three_pass_itree_candidate() -> (
        GeneratedItreeCandidate,
        syn::File,
        Vec<ItreeMutationStep>,
        BTreeMap<String, u32>,
    ) {
        let cand2 = generated_itree_candidate_with_passes(2);
        let (base, mut steps) =
            reconstruct_itree_mutation_steps(&cand2, ITREE_SAFE_SEEDS).expect("reconstruct");
        steps.push(ItreeMutationStep {
            pass_index: 2,
            mutator_name: "BranchLoopWeaver".to_string(),
            rng_before_step: DetRng::new(0x5EED_3333),
        });
        let cand3 = replay_itree_mutation_steps(&cand2, &base, &steps);
        assert_eq!(cand3.applied_mutators.len(), 3);
        let subsets = itree_subset_source_map(&cand3, &base, &steps);
        (cand3, base, steps, subsets)
    }

    /// Mock oracle for the 3-pass scenario (bit `i` = pass `i` kept):
    /// `{0}` diverges with a different tag, `{2}` diverges with the original tag
    /// but without kernel confirmation, `{1, 2}` and `{1}` reproduce the
    /// signature (`{1}` after a non-matching trace), and every other subset
    /// agrees. `{0, 1}` never compiles (see the tests' compile checks).
    fn three_pass_oracle(mask: u32) -> Option<ItreeCandidateEvaluation> {
        match mask {
            0b001 => divergent(vec![trace_verdict("c_t0", "call_arg_mismatch", true)]),
            0b100 => divergent(vec![trace_verdict("c_t1", "outcome_mismatch", false)]),
            0b110 => divergent(vec![trace_verdict("c_t2", "outcome_mismatch", true)]),
            0b010 => divergent(vec![
                trace_verdict("c_t3", "branch_tag_mismatch", true),
                trace_verdict("c_t4", "outcome_mismatch", true),
            ]),
            _ => divergent(Vec::new()),
        }
    }

    #[test]
    fn itree_full_chain_replay_matches_generated_batches_identically() {
        let mut checked = 0usize;
        let mut multi_pass = 0usize;
        for seed in [
            0xCAFE_1234u64,
            0x3333_4444,
            0x1111_2222,
            0x9999_AAAA,
            0x0123_4567_89AB_CDEF,
        ] {
            for cand in generate_itree_batch(ITREE_SAFE_SEEDS, 16, seed) {
                let (base, steps) = reconstruct_itree_mutation_steps(&cand, ITREE_SAFE_SEEDS)
                    .expect("reconstruct a generated candidate's history");
                assert_eq!(steps.len(), cand.applied_mutators.len());
                assert!(steps.iter().enumerate().all(|(i, s)| s.pass_index == i));
                let replayed = replay_itree_mutation_steps(&cand, &base, &steps);
                assert_eq!(
                    replayed, cand,
                    "full-chain replay must reproduce candidate {} byte for byte",
                    cand.id
                );
                assert!(itree_candidate_replay_is_faithful(&cand, &base, &steps));
                // Every subset replays to a strictly safe program.
                let _ = itree_subset_source_map(&cand, &base, &steps);
                if steps.len() >= 2 {
                    multi_pass += 1;
                }
                checked += 1;
            }
        }
        assert_eq!(checked, 80);
        assert!(multi_pass > 0, "expected multi-pass candidates across 80 candidates");
    }

    #[test]
    fn itree_replay_fidelity_rejects_tampered_hand_built_and_identity_candidates() {
        let cand = generated_itree_candidate_with_passes(2);
        let signature = outcome_mismatch_signature();

        let mut tampered = cand.clone();
        tampered.source.push_str("\n// tampered\n");
        let (base, steps) =
            reconstruct_itree_mutation_steps(&tampered, ITREE_SAFE_SEEDS).expect("reconstruct");
        assert!(!itree_candidate_replay_is_faithful(&tampered, &base, &steps));

        let mut non_canonical_steps = steps.clone();
        non_canonical_steps[1].pass_index = 0;
        assert!(!itree_candidate_replay_is_faithful(
            &cand,
            &base,
            &non_canonical_steps
        ));
        let bad_idx_res = minimize_itree_recorded_mutations_with_compile_check(
            &cand,
            &base,
            &non_canonical_steps,
            &signature,
            |_| panic!("compile check must not run for non-canonical step indices"),
            |_| panic!("oracle must not run for non-canonical step indices"),
        );
        assert_eq!(bad_idx_res.status, ItreeShrinkStatus::SkippedReplayMismatch);
        assert_eq!(bad_idx_res.shrink_evaluations, 0);

        let mut with_unsafe = cand.clone();
        with_unsafe.source = format!("{}\npub fn sneaky() {{ unsafe {{}} }}\n", cand.source);
        let mut out_of_range_seed = cand.clone();
        out_of_range_seed.seed_index = ITREE_SAFE_SEEDS.len() + 3;
        assert!(reconstruct_itree_mutation_steps(&out_of_range_seed, ITREE_SAFE_SEEDS).is_none());
        // An in-range seed that the generator would not have mutated for this id.
        let mut other_seed = cand.clone();
        other_seed.seed_index = (cand.seed_index + 1) % ITREE_SAFE_SEEDS.len();
        assert!(reconstruct_itree_mutation_steps(&other_seed, ITREE_SAFE_SEEDS).is_none());
        let mut wrong_chain = cand.clone();
        wrong_chain.applied_mutators = vec!["ExtOracleInjector".to_string(); 3];
        assert!(reconstruct_itree_mutation_steps(&wrong_chain, ITREE_SAFE_SEEDS).is_none());
        let hand_built = GeneratedItreeCandidate {
            id: 1,
            seed_index: 0,
            seed_u64: 0x9999,
            applied_mutators: vec!["BranchLoopWeaver".to_string()],
            source: "pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {\n    \
                     magic ^ payload_len\n}\n"
                .to_string(),
        };

        for victim in [
            &tampered,
            &with_unsafe,
            &out_of_range_seed,
            &other_seed,
            &wrong_chain,
            &hand_built,
        ] {
            let res = minimize_itree_candidate_mutations_with_compile_check(
                victim,
                ITREE_SAFE_SEEDS,
                &signature,
                |_| panic!("compile check must not run for an unfaithful replay"),
                |_| panic!("oracle must not run for an unfaithful replay"),
            );
            assert_eq!(res.status, ItreeShrinkStatus::SkippedReplayMismatch);
            assert_eq!(res.minimized_candidate, *victim);
            assert_eq!(res.minimized_mutator_chain, victim.applied_mutators);
            assert!(res.minimized_trace.is_none() && !res.is_reduced());
            assert_eq!(
                (
                    res.shrink_evaluations,
                    res.oracle_evaluations,
                    res.compile_rejections,
                    res.executed_oracle_runs
                ),
                (0, 0, 0, 0)
            );
        }

        // Identity candidates and non-divergent signatures are never shrunk.
        let identity = generate_itree_identity_batch(ITREE_SAFE_SEEDS)[0].clone();
        let ok_signature = ItreeDiscrepancySignature {
            diag_tag: "ok".to_string(),
            kernel_confirmed: true,
        };
        for (victim, sig) in [(&identity, &signature), (&cand, &ok_signature)] {
            let res = minimize_itree_candidate_mutations_with_compile_check(
                victim,
                ITREE_SAFE_SEEDS,
                sig,
                |_| panic!("no compile check expected"),
                |_| panic!("no oracle run expected"),
            );
            assert_eq!(res.status, ItreeShrinkStatus::SkippedNotApplicable);
            assert_eq!(res.shrink_evaluations, 0);
        }
    }

    #[test]
    fn itree_signature_requires_same_tag_and_at_least_original_kernel_confirmation() {
        let confirmed = outcome_mismatch_signature();
        assert!(confirmed.matches(&trace_verdict("t", "outcome_mismatch", true)));
        assert!(!confirmed.matches(&trace_verdict("t", "outcome_mismatch", false)));
        assert!(!confirmed.matches(&trace_verdict("t", "event_mismatch", true)));
        assert!(!confirmed.matches(&trace_verdict("t", "ok", true)));
        let unconfirmed = ItreeDiscrepancySignature {
            diag_tag: "outcome_mismatch".to_string(),
            kernel_confirmed: false,
        };
        assert!(unconfirmed.matches(&trace_verdict("t", "outcome_mismatch", false)));
        assert!(unconfirmed.matches(&trace_verdict("t", "outcome_mismatch", true)));
        let ok_tag = ItreeDiscrepancySignature {
            diag_tag: "ok".to_string(),
            kernel_confirmed: false,
        };
        assert!(!ok_tag.matches(&trace_verdict("t", "ok", true)));
    }

    #[test]
    fn itree_shrinks_3_mutator_chain_to_1_rejecting_compile_tag_and_unconfirmed_changes() {
        let (cand3, base, steps, subsets) = three_pass_itree_candidate();
        let names = cand3.applied_mutators.clone();
        let compile_calls = RefCell::new(Vec::<u32>::new());
        let oracle_calls = RefCell::new(Vec::<u32>::new());
        let res = minimize_itree_recorded_mutations_with_compile_check(
            &cand3,
            &base,
            &steps,
            &outcome_mismatch_signature(),
            |sub| {
                let mask = subsets[&sub.source];
                compile_calls.borrow_mut().push(mask);
                mask != 0b011
            },
            |sub| {
                let mask = subsets[&sub.source];
                assert_ne!(mask, 0b011, "a non-compiling subsequence reached the oracle");
                assert_ne!(mask, 0b111, "the full chain must never be re-evaluated");
                oracle_calls.borrow_mut().push(mask);
                three_pass_oracle(mask)
            },
        );

        assert_eq!(res.status, ItreeShrinkStatus::Minimized);
        assert!(res.is_reduced());
        assert_eq!(res.original_mutator_chain, names);
        assert_eq!(res.minimized_mutator_chain, vec![names[1].clone()]);
        assert_eq!(res.minimized_candidate.applied_mutators, res.minimized_mutator_chain);
        assert_eq!(subsets[&res.minimized_candidate.source], 0b010);
        // The finding is refreshed from the first trace that reproduces the
        // signature, not from the non-matching trace listed before it.
        assert_eq!(
            res.minimized_trace,
            Some(trace_verdict("c_t4", "outcome_mismatch", true))
        );

        let compile_calls = compile_calls.into_inner();
        let oracle_calls = oracle_calls.into_inner();
        assert_eq!(
            compile_calls,
            vec![0b000, 0b100, 0b001, 0b011, 0b110, 0b100, 0b010],
            "ddmin query order"
        );
        assert_eq!(oracle_calls, vec![0b000, 0b100, 0b001, 0b110, 0b100, 0b010]);
        assert!(oracle_calls.contains(&0b001), "tag-changing {{0}} is judged and rejected");
        assert!(oracle_calls.contains(&0b100), "unconfirmed {{2}} is judged and rejected");
        assert_eq!(
            (
                res.shrink_evaluations,
                res.oracle_evaluations,
                res.compile_rejections,
                res.executed_oracle_runs,
                res.oracle_failures
            ),
            (7, 6, 1, 6, 0)
        );
        assert_eq!(res.shrink_evaluations, res.oracle_evaluations + res.compile_rejections);
    }

    #[test]
    fn itree_memoized_oracle_is_transparent_and_runs_each_distinct_program_once() {
        let (cand3, base, steps, subsets) = three_pass_itree_candidate();
        let compiles = |sub: &GeneratedItreeCandidate| subsets[&sub.source] != 0b011;
        let mut queried: Vec<u32> = Vec::new();
        let plain = minimize_itree_recorded_mutations_with_compile_check(
            &cand3,
            &base,
            &steps,
            &outcome_mismatch_signature(),
            compiles,
            |sub| {
                queried.push(subsets[&sub.source]);
                three_pass_oracle(subsets[&sub.source])
            },
        );

        let mut executed: Vec<u32> = Vec::new();
        let mut memo = MemoizedOracle::new(|sub: &GeneratedItreeCandidate| {
            executed.push(subsets[&sub.source]);
            three_pass_oracle(subsets[&sub.source])
        });
        let memoized = minimize_itree_recorded_mutations_with_compile_check(
            &cand3,
            &base,
            &steps,
            &outcome_mismatch_signature(),
            compiles,
            |sub| memo.eval(sub.source.clone(), sub),
        );
        let (executed_runs, cache_hits) = (memo.executed_runs, memo.cache_hits);
        drop(memo);

        assert_eq!(plain.status, ItreeShrinkStatus::Minimized);
        assert_eq!(memoized.status, plain.status);
        assert_eq!(memoized.minimized_candidate, plain.minimized_candidate);
        assert_eq!(memoized.minimized_trace, plain.minimized_trace);
        assert_eq!(
            (memoized.shrink_evaluations, memoized.oracle_evaluations, memoized.compile_rejections),
            (plain.shrink_evaluations, plain.oracle_evaluations, plain.compile_rejections)
        );
        let distinct: BTreeSet<u32> = queried.iter().copied().collect();
        assert!(
            distinct.len() < queried.len(),
            "the scenario must re-query an identical program: {queried:?}"
        );
        assert_eq!(executed.len(), distinct.len(), "a program was executed twice: {executed:?}");
        assert_eq!(executed.iter().copied().collect::<BTreeSet<u32>>(), distinct);
        assert_eq!((executed_runs, cache_hits), (5, 1));
        assert_eq!(executed_runs + cache_hits, memoized.oracle_evaluations);
    }

    #[test]
    fn itree_unmutated_seed_with_same_signature_shrinks_to_empty_chain_after_one_oracle_run() {
        let cand = generated_itree_candidate_with_passes(2);
        let (base, steps) =
            reconstruct_itree_mutation_steps(&cand, ITREE_SAFE_SEEDS).expect("reconstruct");
        let subsets = itree_subset_source_map(&cand, &base, &steps);
        let res = minimize_itree_candidate_mutations_with_compile_check(
            &cand,
            ITREE_SAFE_SEEDS,
            &outcome_mismatch_signature(),
            |_| true,
            |sub| {
                assert_eq!(subsets[&sub.source], 0, "only `[]` should be evaluated");
                divergent(vec![trace_verdict("seed_t0", "outcome_mismatch", true)])
            },
        );
        assert_eq!(res.status, ItreeShrinkStatus::Minimized);
        assert!(res.minimized_mutator_chain.is_empty());
        assert_eq!(subsets[&res.minimized_candidate.source], 0);
        assert_eq!(
            res.minimized_candidate.source,
            replay_itree_mutation_steps(&cand, &base, &[]).source
        );
        assert_eq!(
            (res.shrink_evaluations, res.oracle_evaluations, res.compile_rejections),
            (1, 1, 0)
        );
    }

    #[test]
    fn itree_oracle_failures_make_the_shrink_inconclusive() {
        let cand = generated_itree_candidate_with_passes(2);
        let (base, steps) =
            reconstruct_itree_mutation_steps(&cand, ITREE_SAFE_SEEDS).expect("reconstruct");
        let subsets = itree_subset_source_map(&cand, &base, &steps);
        // `[]` cannot be judged; `[s1]` reproduces the signature.
        let res = minimize_itree_candidate_mutations_with_compile_check(
            &cand,
            ITREE_SAFE_SEEDS,
            &outcome_mismatch_signature(),
            |_| true,
            |sub| match subsets[&sub.source] {
                0b00 => None,
                0b10 => divergent(vec![trace_verdict("s1_t0", "outcome_mismatch", true)]),
                _ => divergent(Vec::new()),
            },
        );
        assert_eq!(res.status, ItreeShrinkStatus::Inconclusive);
        assert!(res.is_reduced(), "the confirmed reduction is still reported");
        assert_eq!(res.minimized_mutator_chain, vec![cand.applied_mutators[1].clone()]);
        assert_eq!(res.oracle_failures, 1);
        assert!(res.minimized_trace.is_some());

        // A shrink whose every query fails never claims 1-minimality.
        let res = minimize_itree_candidate_mutations_with_compile_check(
            &cand,
            ITREE_SAFE_SEEDS,
            &outcome_mismatch_signature(),
            |_| true,
            |_| None,
        );
        assert_eq!(res.status, ItreeShrinkStatus::Inconclusive);
        assert!(!res.is_reduced());
        assert_eq!(res.oracle_failures, res.oracle_evaluations);
        assert_eq!(res.minimized_candidate, cand);
    }

    /// `minimize_itree_candidate_mutations_with` runs the real compile pre-check
    /// (strict `-O0` and `-O2` plus the instrumented `-O0` and `-O2` compiles that
    /// batch evaluation requires, memoized by source) before every oracle query.
    #[test]
    fn itree_minimize_with_runs_the_real_strict_compile_precheck() {
        let cand = generated_itree_candidate_with_passes(2);
        assert!(itree_candidate_passes_strict_compile(&cand));
        let mut broken = cand.clone();
        broken.source = "pub fn kernel_step(magic: u32, payload_len: u32) -> u32 { magic + true }\n"
            .to_string();
        assert!(!itree_candidate_passes_strict_compile(&broken));
        let mut with_unsafe = cand.clone();
        with_unsafe.source = format!("{}\npub fn f() {{ unsafe {{}} }}\n", cand.source);
        assert!(!itree_candidate_passes_strict_compile(&with_unsafe));
        let mut missing_root = cand.clone();
        missing_root.source = "pub fn not_kernel_step(magic: u32, payload_len: u32) -> u32 {\n    \
                               magic ^ payload_len\n}\n"
            .to_string();
        assert!(!itree_candidate_passes_strict_compile(&missing_root));
        // On programs with a `kernel_step` root, the pre-check accepts exactly
        // what batch compilation accepts.
        let batch = vec![cand.clone(), broken.clone(), with_unsafe.clone()];
        let compiled = compile_itree_candidates(std::slice::from_ref(&batch));
        assert_eq!(
            compiled[0]
                .iter()
                .map(|c| c.opt0 && c.opt2 && c.instrumented)
                .collect::<Vec<_>>(),
            vec![true, false, false]
        );

        let (base, steps) =
            reconstruct_itree_mutation_steps(&cand, ITREE_SAFE_SEEDS).expect("reconstruct");
        let subsets = itree_subset_source_map(&cand, &base, &steps);
        let mut oracle_masks: Vec<u32> = Vec::new();
        let res = minimize_itree_candidate_mutations_with(
            &cand,
            ITREE_SAFE_SEEDS,
            &outcome_mismatch_signature(),
            |sub| {
                let mask = subsets[&sub.source];
                oracle_masks.push(mask);
                if mask == 0b01 {
                    divergent(vec![trace_verdict("s0_t0", "outcome_mismatch", true)])
                } else {
                    divergent(Vec::new())
                }
            },
        );
        assert_eq!(res.status, ItreeShrinkStatus::Minimized);
        assert_eq!(res.minimized_mutator_chain, vec![cand.applied_mutators[0].clone()]);
        assert!(oracle_masks.contains(&0b00), "the unmutated seed `[]` must be evaluated");
        assert_eq!(res.compile_rejections, 0, "every proper subsequence compiles");
        assert_eq!(res.oracle_evaluations, oracle_masks.len());
        assert_eq!(res.shrink_evaluations, oracle_masks.len());
    }

    #[test]
    fn itree_finding_bundle_json_and_summary_serialize_shrink_metadata() {
        let dir = env::temp_dir().join(format!(
            "anneal_itree_bundle_test_{}_{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        let mut bundle = ItreeFindingBundle {
            finding_id: "finding_0000_case_b0_c0__kernel_step_t3".to_string(),
            fn_name: "b0_c0__kernel_step".to_string(),
            case_ident: "case_b0_c0__kernel_step_t1".to_string(),
            seed_index: 0,
            applied_mutators: vec!["BranchLoopWeaver".to_string()],
            original_mutator_chain: vec![
                "CallBoundaryOutliner".to_string(),
                "BranchLoopWeaver".to_string(),
            ],
            minimized_mutator_chain: vec!["BranchLoopWeaver".to_string()],
            shrink_evaluations: 3,
            executed_oracle_runs: 2,
            shrink_status: ItreeShrinkStatus::Minimized.slug().to_string(),
            diag_tag: "outcome_mismatch".to_string(),
            diag_repr: "TraceReplayDiag.outcomeMismatch ...".to_string(),
            trace_hex: "00ff".to_string(),
            kernel_confirmed: true,
            kernel_confirm_theorem: "theorem case_b0_c0__kernel_step_t1_diag_tag : ... := by\n  rfl"
                .to_string(),
            mir_neighborhood: "def body : CapturedMir := ...".to_string(),
            checked_mir_source: "namespace Mir.ItreeDiffStaged.b0_c0__kernel_step\nend".to_string(),
            checked_mir_module: "Mir.ItreeDiffStaged.b0_c0__kernel_step".to_string(),
            candidate_source: "pub fn kernel_step(magic: u32, payload_len: u32) -> u32 { 0 }\n"
                .to_string(),
            repro_path: None,
        };
        write_itree_finding_bundle_to_dir(&dir, &mut bundle).expect("write finding bundle");
        let bundle_dir = dir.join(&bundle.finding_id);
        let finding_json =
            fs::read_to_string(bundle_dir.join("finding.json")).expect("read finding.json");
        let summary_md =
            fs::read_to_string(bundle_dir.join("SUMMARY.md")).expect("read SUMMARY.md");
        let repro = fs::read_to_string(bundle_dir.join("repro.rs")).expect("read repro.rs");
        let _ = fs::remove_dir_all(&dir);

        assert_eq!(repro, bundle.candidate_source);
        assert!(finding_json.contains("\"applied_mutators\": [\"BranchLoopWeaver\"]"));
        assert!(finding_json.contains(
            "\"original_mutator_chain\": [\"CallBoundaryOutliner\", \"BranchLoopWeaver\"]"
        ));
        assert!(finding_json.contains("\"minimized_mutator_chain\": [\"BranchLoopWeaver\"]"));
        assert!(finding_json.contains("\"shrink_evaluations\": 3"));
        assert!(finding_json.contains("\"executed_oracle_runs\": 2"));
        assert!(finding_json.contains("\"shrink_status\": \"minimized\""));
        assert!(finding_json.contains("\"case_ident\": \"case_b0_c0__kernel_step_t1\""));
        assert!(summary_md.contains(
            "- **Original mutator chain**: `CallBoundaryOutliner, BranchLoopWeaver`"
        ));
        assert!(summary_md.contains("- **Minimized mutator chain**: `BranchLoopWeaver`"));
        assert!(summary_md.contains("- **Shrink status**: `minimized`"));
        assert!(
            summary_md.contains("- **Shrink evaluations**: `3` (live oracle runs executed: `2`)")
        );
    }

    #[test]
    fn itree_shrink_result_retains_all_matching_traces_and_selects_distinct_finding_traces() {
        let cand = generated_itree_candidate_with_passes(2);
        let (base, steps) =
            reconstruct_itree_mutation_steps(&cand, ITREE_SAFE_SEEDS).expect("reconstruct");
        let subsets = itree_subset_source_map(&cand, &base, &steps);
        let mut t0 = trace_verdict("case_b0_c0__kernel_step_t0", "outcome_mismatch", true);
        t0.trace_hex = "aa00".to_string();
        let mut t1 = trace_verdict("case_b0_c0__kernel_step_t1", "outcome_mismatch", true);
        t1.trace_hex = "bb11".to_string();
        let unrelated = trace_verdict("case_b0_c0__kernel_step_t2", "event_mismatch", true);
        let res = minimize_itree_recorded_mutations_with_compile_check(
            &cand,
            &base,
            &steps,
            &outcome_mismatch_signature(),
            |_| true,
            |sub| {
                if subsets[&sub.source] == 0b00 {
                    divergent(vec![t0.clone(), unrelated.clone(), t1.clone()])
                } else {
                    divergent(Vec::new())
                }
            },
        );
        assert_eq!(res.status, ItreeShrinkStatus::Minimized);
        assert_eq!(res.minimized_traces.len(), 2);
        assert_eq!(res.minimized_trace.as_ref(), Some(&t0));

        let make_finding = |case_ident: &str, trace_hex: &str| ItreeFindingBundle {
            finding_id: format!("finding_0000_{case_ident}"),
            fn_name: "b0_c0__kernel_step".to_string(),
            case_ident: case_ident.to_string(),
            seed_index: 0,
            applied_mutators: cand.applied_mutators.clone(),
            original_mutator_chain: cand.applied_mutators.clone(),
            minimized_mutator_chain: Vec::new(),
            shrink_evaluations: 0,
            executed_oracle_runs: 0,
            shrink_status: String::new(),
            diag_tag: "outcome_mismatch".to_string(),
            diag_repr: String::new(),
            trace_hex: trace_hex.to_string(),
            kernel_confirmed: true,
            kernel_confirm_theorem: String::new(),
            mir_neighborhood: String::new(),
            checked_mir_source: String::new(),
            checked_mir_module: String::new(),
            candidate_source: cand.source.clone(),
            repro_path: None,
        };
        let f0 = make_finding("case_b0_c0__kernel_step_t0", "ff00");
        let f1 = make_finding("case_b0_c0__kernel_step_t1", "ff11");
        let f_hex = make_finding("case_b0_c0__kernel_step_t9", "bb11");
        assert_eq!(res.select_trace_for_finding(&f0, 0), Some(&t0));
        assert_eq!(res.select_trace_for_finding(&f1, 1), Some(&t1));
        assert_eq!(res.select_trace_for_finding(&f_hex, 0), Some(&t1));
    }
}
