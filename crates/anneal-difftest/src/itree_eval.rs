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
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use arbitrary::Unstructured;
use cargo_anneal::{
    BatchTraceEvalCase, CaptureDriverConfig, RecordedEvent, RecordedOutcome, RecordedRawTrace,
    ScaffoldConfig, TraceCheckModuleConfig, build_lake_build_command,
    decode_recorded_raw_trace_hex, encode_recorded_raw_trace_hex, parse_batch_trace_probe_output,
    render_batch_trace_eval_lean_module, render_batch_trace_probe_lean_module, run_cargo_capture,
    scaffold_workspace_with_config,
};

use crate::input_gen::{
    EnvScheduleGenerator, FieldLayout, LayoutAwareByteBuilder, LayoutSpec, MirInputDictionary,
    MirObsPathSet, PaddingFillPattern, ScalarLayout,
};
use crate::instrument::EnvSchedule;
use crate::miri_eval::{json_escape, resolve_rustc_bin};
use crate::mutators_itree::{
    GeneratedItreeCandidate, ItreeConcreteEvaluator, ItreeConcreteRun, ItreeMutationStep,
    StagedItreeCandidate, annotate_itree_external_callees, contains_unsafe_token,
    explore_itree_concolic_trials, itree_candidate_replay_is_faithful,
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

/// Default per-invocation wall-clock timeout for a single `lake env lean` chunk
/// or fallback module (override via `ANNEAL_ITREE_LEAN_TIMEOUT_SECS` or
/// `ANNEAL_ITREE_LEAN_TIMEOUT_MS`).
pub const DEFAULT_ITREE_LEAN_TIMEOUT: Duration = Duration::from_secs(180);

/// Default per-worker process-tree physical RSS limit in KiB (`8 GiB`).
pub const DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB: u64 = 8 * 1024 * 1024;

/// Minimum auto-computed per-worker process-tree physical RSS limit in KiB
/// (`512 MiB`). Explicit `ANNEAL_ITREE_MAX_RSS_KIB` overrides may set smaller
/// values in unit tests.
pub const MIN_ITREE_LEAN_RSS_LIMIT_KIB: u64 = 512 * 1024;

/// Grace period between `SIGTERM` and `SIGKILL` when the watchdog terminates a
/// `lake env lean` process tree.
const ITREE_WATCHDOG_KILL_GRACE: Duration = Duration::from_millis(100);

/// Maximum poll interval of the `lake env lean` RSS + wall-clock watchdog loop.
/// Polling starts at [`ITREE_WATCHDOG_MIN_POLL_INTERVAL`] (so short runs are
/// reaped promptly) and doubles up to this cap: every tick scans all of
/// `/proc/*/stat`, and up to 8 workers poll concurrently, so a fixed 25 ms
/// cadence would burn a measurable share of a core per worker on busy hosts.
/// At Lean's observed ~280 MB/s kernel-reduction growth a 200 ms tick
/// overshoots the RSS ceiling by at most ~56 MB (`miri_eval` polls at 200 ms).
const ITREE_WATCHDOG_POLL_INTERVAL: Duration = Duration::from_millis(200);

/// First (shortest) poll interval of the watchdog loop.
const ITREE_WATCHDOG_MIN_POLL_INTERVAL: Duration = Duration::from_millis(5);

/// How long [`run_command_with_watchdog`] waits, after the root has exited and
/// its tracked descendants were killed, for the stdout / stderr readers to reach
/// EOF before abandoning them (a write end held open by a descendant that
/// escaped both the process group and `(pid, starttime)` tracking must not
/// block the harness forever).
const ITREE_WATCHDOG_PIPE_DRAIN_GRACE: Duration = Duration::from_secs(2);

/// Parses `(MemTotal, MemAvailable)` in KiB from `/proc/meminfo` contents.
/// Falls back to `MemFree + Buffers + Cached` when `MemAvailable:` is absent.
pub fn parse_meminfo_kib(meminfo: &str) -> (Option<u64>, Option<u64>) {
    let field = |name: &str| {
        meminfo.lines().find_map(|line| {
            line.strip_prefix(name)?
                .split_whitespace()
                .next()?
                .parse::<u64>()
                .ok()
        })
    };
    let total = field("MemTotal:");
    let avail = field("MemAvailable:").or_else(|| {
        let free = field("MemFree:")?;
        let buffers = field("Buffers:").unwrap_or(0);
        let cached = field("Cached:").unwrap_or(0);
        Some(free.saturating_add(buffers).saturating_add(cached))
    });
    (total, avail)
}

fn read_u64_file(path: &Path) -> Option<u64> {
    fs::read_to_string(path).ok()?.trim().parse::<u64>().ok()
}

fn min_opt<T: Ord>(a: Option<T>, b: Option<T>) -> Option<T> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.min(y)),
        (x, None) => x,
        (None, y) => y,
    }
}

/// Normalizes the `<path>` of a `/proc/self/cgroup` line relative to a cgroup
/// mount: strips a ` (deleted)` suffix and leading `/`, and rejects any path
/// with `..` / root / prefix components (so the ancestor walk can never leave
/// the mount via a lexically-prefixed path such as `<root>/../..`).
fn sanitize_cgroup_rel(raw: &str) -> Option<&str> {
    let trimmed = raw.trim();
    let rel = trimmed
        .strip_suffix(" (deleted)")
        .unwrap_or(trimmed)
        .trim()
        .trim_start_matches('/');
    let escapes = Path::new(rel).components().any(|c| {
        matches!(
            c,
            std::path::Component::ParentDir
                | std::path::Component::RootDir
                | std::path::Component::Prefix(_)
        )
    });
    (!escapes).then_some(rel)
}

/// Visits every existing directory from `base/rel` up to and including `base`
/// (a missing leaf, as in a container that sees its own cgroup as the mount
/// root, still walks up to `base`).
fn walk_cgroup_ancestors(base: &Path, rel: &str, visit: &mut dyn FnMut(&Path)) {
    if !base.is_dir() {
        return;
    }
    let mut dir = if rel.is_empty() {
        base.to_path_buf()
    } else {
        base.join(rel)
    };
    while dir.starts_with(base) {
        if dir.is_dir() {
            visit(&dir);
        }
        if dir == base || !dir.pop() {
            break;
        }
    }
}

/// Returns `(limit_kib, headroom_kib)` for the tightest cgroup v2 (`memory.max`
/// / `memory.high` minus `memory.stat` `anon + shmem`) or cgroup v1
/// (`memory.limit_in_bytes` / `hierarchical_memory_limit` minus `total_rss +
/// total_shmem`, under `<cgroup_root>/memory`) ancestor of this process's
/// cgroup in `proc_self_cgroup`.
///
/// Delegates to `cargo_anneal`'s hardened walkers — the same ones
/// `miri-difftest` uses through `probe_effective_memory_kib` — so both difftest
/// harnesses share one set of safety invariants (`max` / unlimited sentinels,
/// ` (deleted)` paths, `..` rejection, missing container leaves, and
/// descendant usage propagation).
///
/// `anneal-lean-run` confines commands to a transient `systemd-run --scope`
/// whose `MemoryMax` / `MemoryHigh` is far below host `MemAvailable` (and parent
/// slices may be capped too), so `/proc/meminfo` alone overestimates how many
/// concurrent `lake env lean` workers and how much per-worker RSS fit before
/// throttling or the cgroup OOM killer fires.
pub fn cgroup_memory_limits_kib(
    cgroup_root: &Path,
    proc_self_cgroup: &str,
) -> (Option<u64>, Option<u64>) {
    let (v2_limit, v2_headroom) =
        cargo_anneal::cgroup_memory_limits_kib(cgroup_root, proc_self_cgroup);
    let (v1_limit, v1_headroom) =
        cargo_anneal::cgroup_v1_memory_limits_kib(&cgroup_root.join("memory"), proc_self_cgroup);
    (min_opt(v2_limit, v1_limit), min_opt(v2_headroom, v1_headroom))
}

/// Parses a cgroup v2 `cpu.max` string (`"<quota> <period>"` or `"max <period>"`)
/// into an integer core ceiling `ceil(quota / period)`. Returns `None` when
/// unconstrained (`"max"`) or malformed.
pub fn parse_cpu_max_quota_cores(cpu_max: &str) -> Option<usize> {
    let mut parts = cpu_max.split_whitespace();
    let quota_str = parts.next()?;
    if quota_str == "max" {
        return None;
    }
    let period_str = parts.next().unwrap_or("100000");
    let quota = quota_str.parse::<u64>().ok()?;
    let period = period_str.parse::<u64>().ok()?;
    if quota == 0 || period == 0 {
        return None;
    }
    Some(quota.div_ceil(period).max(1) as usize)
}

/// Returns the tightest CPU core ceiling across the enclosing cgroup v2
/// (`cpu.max`) and cgroup v1 (`cpu.cfs_quota_us` / `cpu.cfs_period_us` under
/// `<cgroup_root>/cpu,cpuacct` or `<cgroup_root>/cpu`) hierarchy of this
/// process's cgroup in `proc_self_cgroup`.
pub fn cgroup_cpu_quota_cores(cgroup_root: &Path, proc_self_cgroup: &str) -> Option<usize> {
    let mut tightest: Option<usize> = None;

    // 1. Cgroup v2 (`0::<path>`).
    if let Some(rel) = proc_self_cgroup
        .lines()
        .map(str::trim)
        .find_map(|line| line.strip_prefix("0::"))
        .and_then(sanitize_cgroup_rel)
    {
        walk_cgroup_ancestors(cgroup_root, rel, &mut |dir| {
            if let Ok(raw) = fs::read_to_string(dir.join("cpu.max"))
                && let Some(cores) = parse_cpu_max_quota_cores(&raw)
            {
                tightest = min_opt(tightest, Some(cores));
            }
        });
    }

    // 2. Cgroup v1 (`<id>:cpu,cpuacct:<path>` or `<id>:cpu:<path>`).
    let v1_rel = proc_self_cgroup
        .lines()
        .map(str::trim)
        .find_map(|line| {
            let mut parts = line.splitn(3, ':');
            let (_id, controllers, path) = (parts.next()?, parts.next()?, parts.next()?);
            controllers
                .split(',')
                .any(|c| c == "cpu")
                .then_some(path)
        })
        .and_then(sanitize_cgroup_rel);
    if let Some(rel) = v1_rel {
        let mut visited_bases: Vec<PathBuf> = Vec::new();
        for base in [cgroup_root.join("cpu,cpuacct"), cgroup_root.join("cpu")] {
            // `cpu` is usually a symlink to `cpu,cpuacct`: walk each mount once.
            let canonical = fs::canonicalize(&base).unwrap_or_else(|_| base.clone());
            if visited_bases.contains(&canonical) {
                continue;
            }
            visited_bases.push(canonical);
            walk_cgroup_ancestors(&base, rel, &mut |dir| {
                if let Ok(q_raw) = fs::read_to_string(dir.join("cpu.cfs_quota_us"))
                    && let Ok(quota) = q_raw.trim().parse::<i64>()
                    && quota > 0
                {
                    let period = read_u64_file(&dir.join("cpu.cfs_period_us")).unwrap_or(100_000);
                    if period > 0 {
                        let cores = (quota as u64).div_ceil(period).max(1) as usize;
                        tightest = min_opt(tightest, Some(cores));
                    }
                }
            });
        }
    }

    tightest
}

/// Effective `(MemTotal, MemAvailable)` in KiB: host `/proc/meminfo` intersected
/// with the enclosing cgroup v1/v2 limits (`cargo_anneal::probe_effective_memory_kib`,
/// shared with `miri-difftest`).
fn effective_memory_limits_kib() -> (Option<u64>, Option<u64>) {
    cargo_anneal::probe_effective_memory_kib()
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
/// from host `/proc/meminfo` intersected with the enclosing cgroup v1/v2 memory
/// limits (see [`itree_lean_jobs_for_memory`]).
pub fn resolve_itree_lean_jobs() -> usize {
    if let Ok(val) = env::var("ANNEAL_ITREE_LEAN_JOBS")
        && let Ok(parsed) = val.trim().parse::<usize>()
        && parsed >= 1
    {
        return parsed.min(8);
    }
    let (total_kib, avail_kib) = effective_memory_limits_kib();
    itree_lean_jobs_for_memory(total_kib, avail_kib)
}

/// Computes `LEAN_NUM_THREADS` for one `lake env lean` worker given the host's
/// logical core count, optional cgroup CPU quota ceiling, effective available
/// memory in KiB, and number of concurrent `lake env lean` workers (`active_workers`).
pub fn itree_lean_threads_for_resources(
    host_cores: usize,
    cgroup_cores: Option<usize>,
    avail_kib: Option<u64>,
    active_workers: usize,
) -> usize {
    const GIB: u64 = 1024 * 1024;
    let workers = active_workers.max(1);
    let effective_cores = min_opt(Some(host_cores.max(1)), cgroup_cores).unwrap_or(1);
    let by_cpu = (effective_cores / workers).clamp(1, 8);
    let by_mem = match avail_kib.map(|a| a / (workers as u64)) {
        Some(per_worker_kib) if per_worker_kib < 4 * GIB => 1,
        Some(per_worker_kib) if per_worker_kib < 8 * GIB => 2,
        Some(per_worker_kib) if per_worker_kib < 16 * GIB => 4,
        _ => 8,
    };
    by_cpu.min(by_mem).max(1)
}

/// Conservative fallback `.olean`/`.ilean` mmap footprint in KiB (`512 MiB`)
/// reserved when `<anneal_dir>/.lake/build/lib/lean` cannot be measured on disk.
pub const DEFAULT_ITREE_OLEAN_RESERVE_KIB: u64 = 512 * 1024;

/// Estimated per-thread non-heap RSS overhead in KiB (`128 MiB` per
/// `LEAN_NUM_THREADS` worker thread for C++ thread stacks and glibc/mimalloc
/// per-thread arenas that Lean 4's `-M` small-object allocator cap does not
/// bound).
pub const ITREE_PER_THREAD_ARENA_KIB: u64 = 128 * 1024;

/// Minimum non-heap physical RSS reserve in KiB (`1024 MiB` = `1 GiB`) enforced
/// whenever a worker's physical RSS watchdog ceiling is at least `4 GiB`.
pub const MIN_ITREE_LARGE_BUDGET_RESERVE_KIB: u64 = 1024 * 1024;

/// Automatic `LEAN_NUM_THREADS` cap for `itree-difftest` `lake env lean`
/// workers whenever the worker's RSS ceiling is at or below
/// [`DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB`] (`8 GiB`), unless overridden via
/// `ANNEAL_ITREE_LEAN_THREADS`.
pub const ITREE_LEAN_MAX_THREADS_UNDER_8GIB_RSS: usize = 2;

const ITREE_LARGE_BUDGET_THRESHOLD_KIB: u64 = 4 * 1024 * 1024;
const ITREE_MEDIUM_BUDGET_THRESHOLD_KIB: u64 = 2 * 1024 * 1024;
const ITREE_MIN_LEAN_HEAP_MB_LARGE: u64 = 512;
const ITREE_MIN_LEAN_HEAP_MB_SMALL: u64 = 256;
const ITREE_MIN_LEAN_HEAP_MB_TINY: u64 = 64;
const ITREE_MAX_LEAN_HEAP_MB: u64 = 16_384;

fn itree_lean_measured_non_heap_kib(lean_threads: usize, olean_footprint_kib: Option<u64>) -> u64 {
    let threads = lean_threads.max(1) as u64;
    let olean_kib = olean_footprint_kib.unwrap_or(DEFAULT_ITREE_OLEAN_RESERVE_KIB);
    olean_kib.saturating_add(ITREE_PER_THREAD_ARENA_KIB.saturating_mul(threads))
}

fn itree_lean_max_mb_for_rss_and_reserve(rss_limit_kib: u64, reserve_kib: u64) -> u64 {
    let heap_kib = rss_limit_kib.saturating_sub(reserve_kib);
    // Floor-divide KiB -> MiB so `lean_max_mb * 1024 + reserve_kib <= rss_limit_kib`
    // holds without upward rounding ever eating into the non-heap reserve.
    (heap_kib / 1024).clamp(ITREE_MIN_LEAN_HEAP_MB_TINY, ITREE_MAX_LEAN_HEAP_MB)
}

/// Computes the physical RSS reserve (in KiB) withheld from Lean 4's `-M`
/// small-object heap limit to cover memory-mapped `.olean`/`.ilean` files,
/// C++ thread stacks, and allocator per-thread arenas under an outer process-tree
/// RSS ceiling of `rss_limit_kib`.
///
/// - `measured_need = olean_footprint_kib.unwrap_or(DEFAULT_ITREE_OLEAN_RESERVE_KIB)
///   + ITREE_PER_THREAD_ARENA_KIB * lean_threads.max(1)`.
/// - On budgets `>= 4 GiB`, reserves at least [`MIN_ITREE_LARGE_BUDGET_RESERVE_KIB`]
///   (`1024 MiB`) or `measured_need` (whichever is larger), capped so Lean retains
///   at least `512 MiB` for `-M`.
/// - On smaller budgets (`512 MiB .. < 4 GiB`), scales at least proportionally
///   (`max(rss_limit_kib / 4, measured_need)`), capped so Lean retains at least
///   `512 MiB` on `>= 2 GiB` budgets and `256 MiB` on `>= 512 MiB` budgets.
/// - On explicit sub-`512 MiB` budgets, reserves down to the absolute `64 MiB`
///   `-M` floor so `lean_max_mb * 1024 + reserve_kib <= rss_limit_kib` (and
///   strict `< rss_limit_kib`) holds for every budget above `64 MiB`.
pub fn itree_lean_non_heap_reserve_kib(
    rss_limit_kib: u64,
    lean_threads: usize,
    olean_footprint_kib: Option<u64>,
) -> u64 {
    let measured_need = itree_lean_measured_non_heap_kib(lean_threads, olean_footprint_kib);
    let min_heap_kib = if rss_limit_kib >= ITREE_MEDIUM_BUDGET_THRESHOLD_KIB {
        ITREE_MIN_LEAN_HEAP_MB_LARGE * 1024
    } else if rss_limit_kib >= MIN_ITREE_LEAN_RSS_LIMIT_KIB {
        ITREE_MIN_LEAN_HEAP_MB_SMALL * 1024
    } else {
        ITREE_MIN_LEAN_HEAP_MB_TINY * 1024
    };
    let max_reserve_kib = rss_limit_kib.saturating_sub(min_heap_kib);
    if max_reserve_kib == 0 {
        return 0;
    }
    let desired_kib = if rss_limit_kib >= ITREE_LARGE_BUDGET_THRESHOLD_KIB {
        measured_need.max(MIN_ITREE_LARGE_BUDGET_RESERVE_KIB)
    } else {
        measured_need.max(rss_limit_kib / 4)
    };
    desired_kib.min(max_reserve_kib)
}

/// Computes `(lean_max_mb, rss_limit_kib)` for one `lake env lean` worker from
/// effective `(total_kib, avail_kib)`, `active_workers`, `lean_threads`, and an
/// optional measured `.olean`/`.ilean` footprint in KiB.
///
/// Reserves `min(20% of available, 2 GiB)` for the rest of the system / test
/// runner, divides the remaining budget across `active_workers`, clamps
/// `rss_limit_kib` to `[MIN_ITREE_LEAN_RSS_LIMIT_KIB, DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB]`,
/// and subtracts [`itree_lean_non_heap_reserve_kib`] before deriving `lean_max_mb`
/// so `lean_max_mb * 1024 + reserve_kib <= rss_limit_kib` always holds.
pub fn itree_lean_rss_budget_with_reserve_kib(
    total_kib: Option<u64>,
    avail_kib: Option<u64>,
    active_workers: usize,
    lean_threads: usize,
    olean_footprint_kib: Option<u64>,
) -> (u64, u64) {
    const TWO_GIB_KIB: u64 = 2 * 1024 * 1024;
    let workers = (active_workers.max(1)) as u64;
    let mut rss_kib = DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB;

    if let Some(avail) = avail_kib {
        let reserve = (avail / 5).min(TWO_GIB_KIB);
        let usable = avail.saturating_sub(reserve) / workers;
        rss_kib = rss_kib.min(usable);
    }
    if let Some(total) = total_kib {
        // Compute exact `floor(3 * total / 4)` without overflowing `u64`.
        let three_quarters = (total / 4)
            .saturating_mul(3)
            .saturating_add(((total % 4) * 3) / 4);
        let usable_total = three_quarters / workers;
        rss_kib = rss_kib.min(usable_total);
    }
    let rss_limit_kib = rss_kib.clamp(
        MIN_ITREE_LEAN_RSS_LIMIT_KIB,
        DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB,
    );
    let reserve_kib =
        itree_lean_non_heap_reserve_kib(rss_limit_kib, lean_threads, olean_footprint_kib);
    let lean_max_mb = itree_lean_max_mb_for_rss_and_reserve(rss_limit_kib, reserve_kib);
    (lean_max_mb, rss_limit_kib)
}

/// Computes `(lean_max_mb, rss_limit_kib)` for one `lake env lean` worker from
/// effective `(total_kib, avail_kib)` and `active_workers`, using conservative
/// non-heap reserve defaults ([`ITREE_LEAN_MAX_THREADS_UNDER_8GIB_RSS`] threads
/// and [`DEFAULT_ITREE_OLEAN_RESERVE_KIB`]).
pub fn itree_lean_rss_budget_kib(
    total_kib: Option<u64>,
    avail_kib: Option<u64>,
    active_workers: usize,
) -> (u64, u64) {
    itree_lean_rss_budget_with_reserve_kib(
        total_kib,
        avail_kib,
        active_workers,
        ITREE_LEAN_MAX_THREADS_UNDER_8GIB_RSS,
        None,
    )
}

fn parse_positive_env_u64(raw: Option<&str>, min: u64) -> Option<u64> {
    raw.and_then(|v| v.trim().parse::<u64>().ok())
        .filter(|&n| n >= min)
}

/// Caps a resolved `LEAN_NUM_THREADS` count to
/// [`ITREE_LEAN_MAX_THREADS_UNDER_8GIB_RSS`] (`2`) whenever the worker's RSS
/// limit is at or below [`DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB`] (`8 GiB`), unless
/// `ANNEAL_ITREE_LEAN_THREADS` was explicitly set by the caller.
pub fn cap_itree_lean_threads_for_rss_with_env(
    anneal_itree_lean_threads: Option<&str>,
    threads: usize,
    rss_limit_kib: u64,
) -> usize {
    let threads = threads.max(1);
    if parse_positive_env_u64(anneal_itree_lean_threads, 1).is_some() {
        return threads;
    }
    if rss_limit_kib <= DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB {
        threads.min(ITREE_LEAN_MAX_THREADS_UNDER_8GIB_RSS)
    } else {
        threads
    }
}

/// Pure helper for [`resolve_itree_lean_threads`]:
///
/// - an explicit `ANNEAL_ITREE_LEAN_THREADS` (`>= 1`, capped at 16) is the
///   per-worker value;
/// - otherwise the per-worker budget is [`itree_lean_threads_for_resources`],
///   lowered (never raised) by a caller's `LEAN_NUM_THREADS`, which — as set by
///   `anneal-lean-run` for the whole command — is the budget shared by all
///   `active_workers` concurrent `lake env lean` workers (so `jobs` workers
///   never multiply it).
pub fn resolve_itree_lean_threads_with_env(
    anneal_itree_lean_threads: Option<&str>,
    caller_lean_num_threads: Option<&str>,
    host_cores: usize,
    cgroup_cores: Option<usize>,
    avail_kib: Option<u64>,
    active_workers: usize,
) -> usize {
    if let Some(n) = parse_positive_env_u64(anneal_itree_lean_threads, 1) {
        return n.min(16) as usize;
    }
    let computed =
        itree_lean_threads_for_resources(host_cores, cgroup_cores, avail_kib, active_workers);
    match parse_positive_env_u64(caller_lean_num_threads, 1) {
        Some(caller) => {
            let share = (caller as usize / active_workers.max(1)).max(1);
            computed.min(share)
        }
        None => computed,
    }
}

/// Resolves `LEAN_NUM_THREADS` for one of `active_workers` concurrent
/// `lake env lean` workers from `ANNEAL_ITREE_LEAN_THREADS`, the caller's
/// `LEAN_NUM_THREADS`, and host + cgroup CPU quota and memory headroom (see
/// [`resolve_itree_lean_threads_with_env`]).
pub fn resolve_itree_lean_threads(active_workers: usize) -> usize {
    let host_cores = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1);
    let cgroup_cores = fs::read_to_string("/proc/self/cgroup")
        .ok()
        .and_then(|cg| cgroup_cpu_quota_cores(Path::new("/sys/fs/cgroup"), &cg));
    let (_total_kib, avail_kib) = effective_memory_limits_kib();
    resolve_itree_lean_threads_with_env(
        env::var("ANNEAL_ITREE_LEAN_THREADS").ok().as_deref(),
        env::var("LEAN_NUM_THREADS").ok().as_deref(),
        host_cores,
        cgroup_cores,
        avail_kib,
        active_workers,
    )
}

/// Pure helper resolving `(lean_max_mb, rss_limit_kib)` with explicit thread
/// count and optional `.olean`/`.ilean` footprint:
///
/// - starts from [`itree_lean_rss_budget_with_reserve_kib`];
/// - an explicit `ANNEAL_ITREE_LEAN_MAX_MB` (`>= 64`, capped at `16384`) sets
///   Lean's `-M`, and absent `ANNEAL_ITREE_MAX_RSS_KIB` adds non-heap headroom
///   on top so `.olean` mmaps and thread arenas do not trip the RSS watchdog
///   before `-M` engages;
/// - an explicit `ANNEAL_ITREE_MAX_RSS_KIB` (`>= 1024`) sets the RSS ceiling
///   and, when `-M` was not set explicitly, derives `-M` after subtracting
///   [`itree_lean_non_heap_reserve_kib`].
pub fn resolve_itree_lean_rss_budget_with_env_and_reserve(
    anneal_itree_lean_max_mb: Option<&str>,
    anneal_itree_max_rss_kib: Option<&str>,
    total_kib: Option<u64>,
    avail_kib: Option<u64>,
    active_workers: usize,
    lean_threads: usize,
    olean_footprint_kib: Option<u64>,
) -> (u64, u64) {
    let (mut lean_max_mb, mut rss_limit_kib) = itree_lean_rss_budget_with_reserve_kib(
        total_kib,
        avail_kib,
        active_workers,
        lean_threads,
        olean_footprint_kib,
    );
    let explicit_mb = parse_positive_env_u64(anneal_itree_lean_max_mb, ITREE_MIN_LEAN_HEAP_MB_TINY)
        .map(|mb| mb.min(ITREE_MAX_LEAN_HEAP_MB));
    if let Some(mb) = explicit_mb {
        lean_max_mb = mb;
        let measured = itree_lean_measured_non_heap_kib(lean_threads, olean_footprint_kib);
        let non_heap_kib = if mb >= 3072 {
            measured.max(MIN_ITREE_LARGE_BUDGET_RESERVE_KIB)
        } else {
            measured.max(mb.saturating_mul(1024) / 3)
        };
        rss_limit_kib = mb.saturating_mul(1024).saturating_add(non_heap_kib);
    }
    if let Some(kib) = parse_positive_env_u64(anneal_itree_max_rss_kib, 1024) {
        rss_limit_kib = kib;
        if explicit_mb.is_none() {
            let reserve_kib =
                itree_lean_non_heap_reserve_kib(rss_limit_kib, lean_threads, olean_footprint_kib);
            lean_max_mb = itree_lean_max_mb_for_rss_and_reserve(rss_limit_kib, reserve_kib);
        }
    }
    (lean_max_mb, rss_limit_kib)
}

/// Pure helper for [`resolve_itree_lean_rss_budget_kib`], using conservative
/// non-heap reserve defaults ([`ITREE_LEAN_MAX_THREADS_UNDER_8GIB_RSS`] threads
/// and [`DEFAULT_ITREE_OLEAN_RESERVE_KIB`]).
pub fn resolve_itree_lean_rss_budget_with_env(
    anneal_itree_lean_max_mb: Option<&str>,
    anneal_itree_max_rss_kib: Option<&str>,
    total_kib: Option<u64>,
    avail_kib: Option<u64>,
    active_workers: usize,
) -> (u64, u64) {
    resolve_itree_lean_rss_budget_with_env_and_reserve(
        anneal_itree_lean_max_mb,
        anneal_itree_max_rss_kib,
        total_kib,
        avail_kib,
        active_workers,
        ITREE_LEAN_MAX_THREADS_UNDER_8GIB_RSS,
        None,
    )
}

/// Resolves `(lean_max_mb, rss_limit_kib, lean_threads)` jointly for one
/// `lake env lean` worker so that:
/// 1. when `rss_limit_kib <= DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB` (`8 GiB`) and
///    `ANNEAL_ITREE_LEAN_THREADS` is not explicitly set, `lean_threads` is
///    capped to [`ITREE_LEAN_MAX_THREADS_UNDER_8GIB_RSS`] (`2`);
/// 2. the non-heap reserve subtracted from `rss_limit_kib` (or added above an
///    explicit `ANNEAL_ITREE_LEAN_MAX_MB`) matches that final `lean_threads`
///    and optional `.olean`/`.ilean` footprint.
///
/// The RSS ceiling can itself depend on the thread count: an explicit
/// `ANNEAL_ITREE_LEAN_MAX_MB` without `ANNEAL_ITREE_MAX_RSS_KIB` pads the
/// ceiling by a per-thread arena estimate. The cap is therefore decided on the
/// budget of the *capped* thread count: judging it on the uncapped count would
/// let a wide host (e.g. 8 threads) inflate its own ceiling past `8 GiB` and
/// thereby exempt itself from the cap, although the same `-M` fits under
/// `8 GiB` with 2 threads. The ceiling never shrinks as threads grow, so the
/// returned triple always satisfies (1): either the capped budget is at most
/// `8 GiB` and is returned with the capped count, or even the capped budget
/// exceeds `8 GiB`, and then so does the uncapped one.
#[allow(clippy::too_many_arguments)]
pub fn resolve_itree_lean_execution_budget_with_env(
    anneal_itree_lean_max_mb: Option<&str>,
    anneal_itree_max_rss_kib: Option<&str>,
    anneal_itree_lean_threads: Option<&str>,
    caller_lean_num_threads: Option<&str>,
    host_cores: usize,
    cgroup_cores: Option<usize>,
    total_kib: Option<u64>,
    avail_kib: Option<u64>,
    active_workers: usize,
    olean_footprint_kib: Option<u64>,
) -> (u64, u64, usize) {
    let raw_threads = resolve_itree_lean_threads_with_env(
        anneal_itree_lean_threads,
        caller_lean_num_threads,
        host_cores,
        cgroup_cores,
        avail_kib,
        active_workers,
    )
    .max(1);
    let budget_for = |lean_threads: usize| {
        resolve_itree_lean_rss_budget_with_env_and_reserve(
            anneal_itree_lean_max_mb,
            anneal_itree_max_rss_kib,
            total_kib,
            avail_kib,
            active_workers,
            lean_threads,
            olean_footprint_kib,
        )
    };
    // `rss_limit_kib = 0` asks for the cap unconditionally (unless
    // `ANNEAL_ITREE_LEAN_THREADS` overrides it).
    let capped_threads =
        cap_itree_lean_threads_for_rss_with_env(anneal_itree_lean_threads, raw_threads, 0);
    let (capped_mb, capped_rss_kib) = budget_for(capped_threads);
    if capped_threads == raw_threads || capped_rss_kib <= DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB {
        return (capped_mb, capped_rss_kib, capped_threads);
    }
    let (lean_max_mb, rss_limit_kib) = budget_for(raw_threads);
    (lean_max_mb, rss_limit_kib, raw_threads)
}

/// Top-level Lean library of `<anneal_dir>/.lake/build/lib/lean` that holds the
/// staged per-candidate modules (`Mir.ItreeDiffStaged.*`).
const ITREE_STAGED_MIR_LIB: &str = "Mir";

/// On-disk size of the `.olean` / `.ilean` artifacts under
/// `<anneal_dir>/.lake/build/lib/lean`, split by which `lake env lean` workers
/// map them.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ItreeOleanFootprint {
    /// Bytes of the libraries every worker imports whole (`Trusted`, `Anneal`):
    /// everything outside the staged [`ITREE_STAGED_MIR_LIB`] library.
    pub shared_bytes: u64,
    /// Bytes of the staged per-candidate `Mir.*` modules of *all* candidates of
    /// the run. A worker imports only the modules of its own chunk's
    /// candidates, so it maps a share of these that shrinks as the run grows.
    pub staged_bytes: u64,
}

impl ItreeOleanFootprint {
    /// The whole tree in KiB (rounded up): what a worker maps when the staged
    /// modules all belong to its own module (a single-candidate reproduction).
    pub fn total_kib(self) -> u64 {
        self.shared_bytes
            .saturating_add(self.staged_bytes)
            .div_ceil(1024)
    }

    /// What one worker maps, in KiB (rounded up), when the staged modules belong
    /// to `staged_fns` candidates and one Lean module covers at most
    /// `max_chunk_fns` of them: the shared libraries plus that fraction of the
    /// staged bytes (rounded up; all of them when `staged_fns <= max_chunk_fns`).
    ///
    /// Reserving the whole tree instead would charge every worker for the
    /// modules of every other chunk: a campaign-sized run stages a few MiB per
    /// candidate, so the "measured" reserve would grow with the campaign and
    /// squeeze `-M` toward its floor for memory no worker ever maps. The share
    /// assumes candidates of similar size; a chunk of unusually large ones is
    /// under-reserved by the difference, which fails safe (the RSS watchdog
    /// still bounds the worker, and Stage 2 halves the chunk).
    pub fn worker_kib(self, staged_fns: usize, max_chunk_fns: usize) -> u64 {
        let fns = staged_fns.max(1) as u128;
        let chunk_fns = (max_chunk_fns.max(1) as u128).min(fns);
        let staged_share = (u128::from(self.staged_bytes) * chunk_fns).div_ceil(fns);
        // `staged_share <= staged_bytes`, so it fits `u64`.
        self.shared_bytes
            .saturating_add(staged_share as u64)
            .div_ceil(1024)
    }
}

/// Per-module `.olean`/`.ilean` index produced by
/// [`measure_itree_olean_footprint_index`], allowing each Stage 1 / Stage 2
/// worker slice to reserve the exact byte footprint of the shared libraries
/// plus only the specific staged `Mir.*` modules that slice actually imports.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ItreeOleanFootprintIndex {
    /// Aggregate shared vs. staged `.olean`/`.ilean` totals.
    pub footprint: ItreeOleanFootprint,
    /// Exact on-disk byte sizes (`.olean` + `.olean.server` + `.olean.private`
    /// + `.ilean`) of each built staged module under `Mir`, keyed by Lean
    /// module name (e.g. `"Mir.ItreeDiffStaged.b0_c0__kernel_step"`).
    pub staged_module_bytes: BTreeMap<String, u64>,
}

impl ItreeOleanFootprintIndex {
    /// Returns the exact KiB (rounded up) mapped by a worker that imports
    /// `modules` (plus `Mir.Common` if built and any `Mir.*` module is
    /// requested). When every requested `Mir.*` module is present in
    /// `staged_module_bytes`, avoids both proportional-share guesswork across
    /// uneven candidate sizes and overcharging smaller split/fallback slices;
    /// otherwise falls back conservatively to the max of matched bytes and
    /// [`ItreeOleanFootprint::worker_kib`].
    pub fn worker_kib_for_modules<'a>(
        &self,
        modules: impl IntoIterator<Item = &'a str>,
        staged_fns: usize,
        slice_fns: usize,
    ) -> u64 {
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        let mut staged_requested = 0usize;
        let mut staged_missing = 0usize;
        let mut matched_bytes = 0u64;
        for m in modules {
            let is_staged = m == ITREE_STAGED_MIR_LIB
                || m.strip_prefix(ITREE_STAGED_MIR_LIB)
                    .is_some_and(|rest| rest.starts_with('.'));
            if !is_staged || !seen.insert(m) {
                continue;
            }
            staged_requested += 1;
            match self.staged_module_bytes.get(m) {
                Some(&bytes) => matched_bytes = matched_bytes.saturating_add(bytes),
                None => staged_missing += 1,
            }
        }
        if staged_requested > 0
            && let Some(&common_bytes) = self.staged_module_bytes.get("Mir.Common")
            && seen.insert("Mir.Common")
        {
            matched_bytes = matched_bytes.saturating_add(common_bytes);
        }
        let exact_kib = self
            .footprint
            .shared_bytes
            .saturating_add(matched_bytes)
            .div_ceil(1024);
        if staged_requested > 0 && staged_missing == 0 {
            exact_kib
        } else {
            exact_kib.max(self.footprint.worker_kib(staged_fns, slice_fns))
        }
    }
}

fn lean_artifact_module_stem(file_name: &str) -> Option<&str> {
    file_name
        .strip_suffix(".olean.server")
        .or_else(|| file_name.strip_suffix(".olean.private"))
        .or_else(|| file_name.strip_suffix(".olean"))
        .or_else(|| file_name.strip_suffix(".ilean"))
}

/// Measures the `.olean` / `.ilean` artifacts under
/// `<anneal_dir>/.lake/build/lib/lean` and indexes staged `Mir.*` module byte
/// sizes (returning `None` if the directory does not exist or has no matching
/// artifacts, so callers fall back to [`DEFAULT_ITREE_OLEAN_RESERVE_KIB`]).
///
/// A symlinked artifact *file* counts with the size of its target (Lean maps a
/// link into a shared artifact cache exactly like a regular file, so skipping
/// it would under-reserve), while symlinked *directories* are never traversed
/// (no cycles, and nothing outside the build tree is walked).
pub fn measure_itree_olean_footprint_index(anneal_dir: &Path) -> Option<ItreeOleanFootprintIndex> {
    /// Where a directory sits relative to the library root.
    #[derive(Clone, PartialEq, Eq)]
    enum Scope {
        /// `.lake/build/lib/lean` itself.
        Root,
        /// Inside a library every worker imports whole.
        Shared,
        /// Inside the staged per-candidate library, carrying its Lean module
        /// prefix (`"Mir"`, `"Mir.ItreeDiffStaged"`, ...) when valid UTF-8.
        Staged(Option<String>),
    }

    let lib_root = anneal_dir.join(".lake/build/lib/lean");
    if !lib_root.is_dir() {
        return None;
    }
    let mut index = ItreeOleanFootprintIndex::default();
    let mut stack = vec![(lib_root, Scope::Root)];
    while let Some((dir, scope)) = stack.pop() {
        let Ok(entries) = fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            // `DirEntry::file_type` does not follow symlinks, so a symlinked
            // directory is neither `is_dir` here nor pushed below.
            let Ok(ft) = entry.file_type() else {
                continue;
            };
            let path = entry.path();
            let name = entry.file_name();
            if ft.is_dir() {
                let child_scope = match &scope {
                    Scope::Root if name == ITREE_STAGED_MIR_LIB => {
                        Scope::Staged(Some(ITREE_STAGED_MIR_LIB.to_string()))
                    }
                    Scope::Root => Scope::Shared,
                    Scope::Shared => Scope::Shared,
                    Scope::Staged(prefix) => {
                        let next = prefix
                            .as_deref()
                            .zip(name.to_str())
                            .map(|(p, seg)| format!("{p}.{seg}"));
                        Scope::Staged(next)
                    }
                };
                stack.push((path, child_scope));
                continue;
            }
            let Some(stem) = name.to_str().and_then(lean_artifact_module_stem) else {
                continue;
            };
            // `fs::metadata` follows a symlinked artifact to its target; a
            // dangling link or a link to a directory contributes nothing.
            if let Ok(meta) = fs::metadata(&path)
                && meta.is_file()
            {
                let len = meta.len();
                match &scope {
                    Scope::Staged(prefix) => {
                        index.footprint.staged_bytes =
                            index.footprint.staged_bytes.saturating_add(len);
                        if let Some(p) = prefix {
                            let mod_name = format!("{p}.{stem}");
                            let slot = index.staged_module_bytes.entry(mod_name).or_insert(0);
                            *slot = slot.saturating_add(len);
                        }
                    }
                    Scope::Root if stem == ITREE_STAGED_MIR_LIB => {
                        index.footprint.staged_bytes =
                            index.footprint.staged_bytes.saturating_add(len);
                        let slot = index
                            .staged_module_bytes
                            .entry(ITREE_STAGED_MIR_LIB.to_string())
                            .or_insert(0);
                        *slot = slot.saturating_add(len);
                    }
                    Scope::Root | Scope::Shared => {
                        index.footprint.shared_bytes =
                            index.footprint.shared_bytes.saturating_add(len);
                    }
                }
            }
        }
    }
    (index.footprint != ItreeOleanFootprint::default()).then_some(index)
}

fn itree_slice_olean_footprint_kib(
    index: Option<&ItreeOleanFootprintIndex>,
    slice: &[BatchTraceEvalCase],
    staged_fns: usize,
    case_to_fn: &BTreeMap<String, String>,
) -> Option<u64> {
    let index = index?;
    let slice_fns = slice
        .iter()
        .filter_map(|c| case_to_fn.get(&c.case_ident))
        .collect::<BTreeSet<_>>()
        .len()
        .max(1);
    let modules = slice.iter().flat_map(|c| {
        std::iter::once(c.config.root_mir_module.as_str())
            .chain(c.config.callee_sig_modules.iter().map(String::as_str))
            .chain(c.config.inlined_callee_modules.iter().map(String::as_str))
    });
    Some(index.worker_kib_for_modules(modules, staged_fns, slice_fns))
}

/// Measures the `.olean` / `.ilean` artifacts under
/// `<anneal_dir>/.lake/build/lib/lean` (see
/// [`measure_itree_olean_footprint_index`]).
pub fn measure_itree_olean_footprint(anneal_dir: &Path) -> Option<ItreeOleanFootprint> {
    measure_itree_olean_footprint_index(anneal_dir).map(|idx| idx.footprint)
}

/// Total on-disk size (in KiB, rounded up) of the artifacts measured by
/// [`measure_itree_olean_footprint`]: see [`ItreeOleanFootprint::total_kib`].
pub fn measure_itree_olean_footprint_kib(anneal_dir: &Path) -> Option<u64> {
    measure_itree_olean_footprint(anneal_dir).map(ItreeOleanFootprint::total_kib)
}

/// Resolves `(lean_max_mb, rss_limit_kib, lean_threads)` for one of
/// `active_workers` concurrent `lake env lean` workers against host + cgroup
/// limits and an optional cached `.olean`/`.ilean` footprint.
fn resolve_itree_lean_execution_budget(
    active_workers: usize,
    olean_footprint_kib: Option<u64>,
) -> (u64, u64, usize) {
    let host_cores = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1);
    let cgroup_cores = fs::read_to_string("/proc/self/cgroup")
        .ok()
        .and_then(|cg| cgroup_cpu_quota_cores(Path::new("/sys/fs/cgroup"), &cg));
    let (total_kib, avail_kib) = effective_memory_limits_kib();
    resolve_itree_lean_execution_budget_with_env(
        env::var("ANNEAL_ITREE_LEAN_MAX_MB").ok().as_deref(),
        env::var("ANNEAL_ITREE_MAX_RSS_KIB").ok().as_deref(),
        env::var("ANNEAL_ITREE_LEAN_THREADS").ok().as_deref(),
        env::var("LEAN_NUM_THREADS").ok().as_deref(),
        host_cores,
        cgroup_cores,
        total_kib,
        avail_kib,
        active_workers,
        olean_footprint_kib,
    )
}

/// Resolves `(lean_max_mb, rss_limit_kib)` for one of `active_workers`
/// concurrent `lake env lean` workers, honoring `ANNEAL_ITREE_LEAN_MAX_MB` and
/// `ANNEAL_ITREE_MAX_RSS_KIB` (see [`resolve_itree_lean_rss_budget_with_env`]).
pub fn resolve_itree_lean_rss_budget_kib(active_workers: usize) -> (u64, u64) {
    let (total_kib, avail_kib) = effective_memory_limits_kib();
    resolve_itree_lean_rss_budget_with_env(
        env::var("ANNEAL_ITREE_LEAN_MAX_MB").ok().as_deref(),
        env::var("ANNEAL_ITREE_MAX_RSS_KIB").ok().as_deref(),
        total_kib,
        avail_kib,
        active_workers,
    )
}

/// Wall-clock allowance per trace case beyond the first in one `lake env lean`
/// module, on top of [`DEFAULT_ITREE_LEAN_TIMEOUT`], so a full 64-case probe
/// chunk is not held to a single trace's budget while a bisected single case
/// still is.
pub const ITREE_LEAN_TIMEOUT_PER_CASE: Duration = Duration::from_secs(5);

/// Pure helper for [`resolve_itree_lean_timeout_for_cases`]: an explicit
/// `ANNEAL_ITREE_LEAN_TIMEOUT_MS` (`>= 10`) or `ANNEAL_ITREE_LEAN_TIMEOUT_SECS`
/// (`>= 1`) is a flat per-invocation timeout; otherwise
/// `DEFAULT_ITREE_LEAN_TIMEOUT + (cases - 1) * ITREE_LEAN_TIMEOUT_PER_CASE`.
pub fn resolve_itree_lean_timeout_with_env(
    timeout_ms: Option<&str>,
    timeout_secs: Option<&str>,
    cases: usize,
) -> Duration {
    if let Some(ms) = parse_positive_env_u64(timeout_ms, 10) {
        return Duration::from_millis(ms);
    }
    if let Some(secs) = parse_positive_env_u64(timeout_secs, 1) {
        return Duration::from_secs(secs);
    }
    let extra_cases = u32::try_from(cases.saturating_sub(1)).unwrap_or(u32::MAX);
    DEFAULT_ITREE_LEAN_TIMEOUT
        .saturating_add(ITREE_LEAN_TIMEOUT_PER_CASE.saturating_mul(extra_cases))
}

/// Resolves the wall-clock timeout for one `lake env lean` module holding
/// `cases` trace cases (see [`resolve_itree_lean_timeout_with_env`]).
pub fn resolve_itree_lean_timeout_for_cases(cases: usize) -> Duration {
    resolve_itree_lean_timeout_with_env(
        env::var("ANNEAL_ITREE_LEAN_TIMEOUT_MS").ok().as_deref(),
        env::var("ANNEAL_ITREE_LEAN_TIMEOUT_SECS").ok().as_deref(),
        cases,
    )
}

/// Resolves the per-invocation wall-clock timeout for a single-case `lake env
/// lean` module.
pub fn resolve_itree_lean_timeout() -> Duration {
    resolve_itree_lean_timeout_for_cases(1)
}

/// Parses `(state, ppid, starttime_ticks)` from `/proc/<pid>/stat` contents.
///
/// The `comm` field (field 2) is enclosed in `(` and `)` and may contain spaces,
/// parentheses, or newlines, so we locate the last `)` before splitting the
/// remaining fields by whitespace.
/// After `)`:
/// - token 0 is field 3 (`state`, e.g. `'R'`, `'S'`, `'Z'`),
/// - token 1 is field 4 (`ppid`),
/// - token 19 is field 22 (`starttime` in clock ticks since boot).
pub fn parse_proc_stat_state_ppid_starttime(stat: &str) -> Option<(char, u32, u64)> {
    let open = stat.find('(')?;
    let close = stat.rfind(')')?;
    if close <= open {
        return None;
    }
    let after_comm = stat.get(close + 1..)?.trim_start();
    let mut fields = after_comm.split_whitespace();
    let state = fields.next()?.chars().next()?;
    let ppid = fields.next()?.parse::<u32>().ok()?;
    let starttime = fields.nth(17)?.parse::<u64>().ok()?;
    Some((state, ppid, starttime))
}

fn proc_state_ppid_starttime_in(proc_root: &Path, pid: u32) -> Option<(char, u32, u64)> {
    let stat_path = proc_root.join(pid.to_string()).join("stat");
    let stat = fs::read_to_string(stat_path).ok()?;
    parse_proc_stat_state_ppid_starttime(&stat)
}

fn proc_starttime_in(proc_root: &Path, pid: u32) -> Option<u64> {
    proc_state_ppid_starttime_in(proc_root, pid).map(|(_, _, st)| st)
}

fn host_page_size_kib() -> u64 {
    #[cfg(unix)]
    {
        unsafe extern "C" {
            fn sysconf(name: i32) -> std::ffi::c_long;
        }
        #[cfg(target_os = "linux")]
        const SC_PAGESIZE: i32 = 30;
        #[cfg(target_os = "macos")]
        const SC_PAGESIZE: i32 = 29;
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        const SC_PAGESIZE: i32 = 30;
        let bytes = unsafe { sysconf(SC_PAGESIZE) };
        if bytes > 0 {
            return (bytes as u64 / 1024).max(1);
        }
    }
    4
}

/// Reads physical resident set size (RSS) in KiB for `pid` under `proc_root`,
/// preferring `<proc_root>/<pid>/statm` (field 2 = resident pages) and falling
/// back to `VmRSS:` in `<proc_root>/<pid>/status`.
pub fn proc_rss_kib_in(proc_root: &Path, pid: u32, page_size_kib: u64) -> Option<u64> {
    let pid_dir = proc_root.join(pid.to_string());
    if let Ok(statm) = fs::read_to_string(pid_dir.join("statm"))
        && let Some(res_pages_str) = statm.split_whitespace().nth(1)
        && let Ok(res_pages) = res_pages_str.parse::<u64>()
    {
        return Some(res_pages.saturating_mul(page_size_kib.max(1)));
    }
    let status = fs::read_to_string(pid_dir.join("status")).ok()?;
    for line in status.lines() {
        if let Some(rest) = line.strip_prefix("VmRSS:") {
            let kib_str = rest.split_whitespace().next()?;
            return kib_str.parse::<u64>().ok();
        }
    }
    None
}

/// Tracks a root `lake env lean` process and all of its descendants across
/// polling ticks by `(pid, starttime)` so that:
/// 1. grandchildren whose intermediate parent exits and are reparented to PID 1
///    or a subreaper remain tracked in the tree,
/// 2. PID reuse after a child exits cannot cause the watchdog to misattribute
///    RSS or signal an unrelated process whose `starttime` differs, and
/// 3. descendants can be signaled in reverse-creation order (`(starttime, seq)`
///    descending) even when Linux PID numbers wrap around `pid_max`.
#[derive(Debug, Clone)]
pub struct TrackedProcessTree {
    root_pid: u32,
    root_starttime: Option<u64>,
    /// Map from `pid` to `(starttime_ticks, discovery_seq)` for every live
    /// process known to belong to this process tree.
    tracked: BTreeMap<u32, (u64, u64)>,
    next_seq: u64,
    proc_root: PathBuf,
    page_size_kib: u64,
}

impl TrackedProcessTree {
    /// Creates a new process-tree tracker rooted at `root_pid` using `/proc`.
    pub fn new(root_pid: u32) -> Self {
        Self::with_proc_root(root_pid, Path::new("/proc"), host_page_size_kib())
    }

    /// Creates a new process-tree tracker rooted at `root_pid` reading from a
    /// custom `proc_root` and `page_size_kib` (used by deterministic unit tests).
    pub fn with_proc_root(root_pid: u32, proc_root: &Path, page_size_kib: u64) -> Self {
        let root_starttime = proc_starttime_in(proc_root, root_pid);
        let mut tracked = BTreeMap::new();
        let mut next_seq = 0u64;
        if let Some(st) = root_starttime {
            tracked.insert(root_pid, (st, next_seq));
            next_seq += 1;
        }
        Self {
            root_pid,
            root_starttime,
            tracked,
            next_seq,
            proc_root: proc_root.to_path_buf(),
            page_size_kib: page_size_kib.max(1),
        }
    }

    /// Refreshes the tracked process tree from `self.proc_root` and returns the
    /// summed physical RSS (in KiB) of all live non-zombie processes in the tree.
    pub fn sample_rss_kib(&mut self) -> u64 {
        let Some(root_st) = self.root_starttime.or_else(|| {
            let st = proc_starttime_in(&self.proc_root, self.root_pid)?;
            self.root_starttime = Some(st);
            let seq = self.next_seq;
            self.next_seq += 1;
            self.tracked.insert(self.root_pid, (st, seq));
            Some(st)
        }) else {
            return 0;
        };

        let Ok(entries) = fs::read_dir(&self.proc_root) else {
            return proc_rss_kib_in(&self.proc_root, self.root_pid, self.page_size_kib)
                .unwrap_or(0);
        };

        let mut children_by_ppid: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
        let mut live_meta: BTreeMap<u32, (char, u64)> = BTreeMap::new();
        for entry in entries.flatten() {
            let name = entry.file_name();
            let Some(pid) = name.to_str().and_then(|s| s.parse::<u32>().ok()) else {
                continue;
            };
            if let Some((state, ppid, st)) = proc_state_ppid_starttime_in(&self.proc_root, pid) {
                children_by_ppid.entry(ppid).or_default().push(pid);
                live_meta.insert(pid, (state, st));
            }
        }

        // If `root_pid` exited or was recycled for an unrelated process, do not
        // attribute `root_pid`'s own RSS; if `root_pid` is a zombie with matching
        // `starttime`, still expand its children before pruning `'Z'`/`'X'`.
        let root_matches = matches!(
            live_meta.get(&self.root_pid),
            Some(&(_, st)) if st == root_st
        );
        if !root_matches {
            self.tracked.remove(&self.root_pid);
        }

        // Seed expansion from all tracked PIDs whose `starttime` still matches
        // (including a just-zombied parent whose un-reaped PID is still its
        // live children's `ppid`).
        let mut stack: Vec<u32> = self
            .tracked
            .iter()
            .filter_map(|(&pid, &(expected_st, _))| {
                matches!(
                    live_meta.get(&pid),
                    Some(&(_, actual_st)) if actual_st == expected_st
                )
                .then_some(pid)
            })
            .collect();
        if root_matches && !stack.contains(&self.root_pid) {
            stack.push(self.root_pid);
        }

        // Prune any tracked PID that exited, turned into a zombie, or was reused
        // with a different `starttime`.
        self.tracked.retain(|&pid, &mut (expected_st, _seq)| {
            matches!(
                live_meta.get(&pid),
                Some(&(state, actual_st)) if actual_st == expected_st && state != 'Z' && state != 'X'
            )
        });

        // Expand from all verified tracked members to discover any new children
        // or grandchildren (including descendants reparented before their parent
        // exited).
        while let Some(pid) = stack.pop() {
            if let Some(children) = children_by_ppid.get(&pid) {
                for &child_pid in children {
                    if self.tracked.contains_key(&child_pid) {
                        continue;
                    }
                    if let Some(&(state, child_st)) = live_meta.get(&child_pid)
                        && state != 'Z'
                        && state != 'X'
                    {
                        let seq = self.next_seq;
                        self.next_seq += 1;
                        self.tracked.insert(child_pid, (child_st, seq));
                        stack.push(child_pid);
                    }
                }
            }
        }
        if self.tracked.is_empty() {
            return 0;
        }

        let mut total_rss_kib = 0u64;
        for (&pid, &(expected_st, _seq)) in &self.tracked {
            if let Some(&(state, actual_st)) = live_meta.get(&pid)
                && actual_st == expected_st
                && state != 'Z'
                && state != 'X'
            {
                total_rss_kib = total_rss_kib.saturating_add(
                    proc_rss_kib_in(&self.proc_root, pid, self.page_size_kib).unwrap_or(0),
                );
            }
        }
        total_rss_kib
    }

    /// Returns tracked descendants (excluding `root_pid`) ordered newest-first
    /// (`(starttime, discovery_seq)` descending) so children are signaled before
    /// parents even when PID numbers wrap around `pid_max`.
    pub fn descendant_kill_order(&self) -> Vec<(u32, u64)> {
        let mut order: Vec<(u32, u64, u64)> = self
            .tracked
            .iter()
            .filter(|&(&pid, _)| pid != self.root_pid)
            .map(|(&pid, &(st, seq))| (pid, st, seq))
            .collect();
        order.sort_by(|a, b| (b.1, b.2).cmp(&(a.1, a.2)));
        order.into_iter().map(|(pid, st, _)| (pid, st)).collect()
    }

    /// Returns true if any tracked descendant (excluding `root_pid`) is still
    /// alive (and not a zombie) with its recorded `starttime`.
    pub fn has_live_descendants(&self) -> bool {
        self.tracked.iter().any(|(&pid, &(expected_st, _))| {
            pid != self.root_pid
                && matches!(
                    proc_state_ppid_starttime_in(&self.proc_root, pid),
                    Some((state, _, actual_st))
                        if actual_st == expected_st && state != 'Z' && state != 'X'
                )
        })
    }

    /// Signals all tracked descendants whose current `starttime` still matches
    /// (`SIGTERM` followed by `SIGKILL` after `grace_period` if any remain).
    pub fn kill_descendants(&mut self, grace_period: Duration) {
        #[cfg(unix)]
        {
            unsafe extern "C" {
                fn kill(pid: i32, sig: i32) -> i32;
            }
            const SIGTERM: i32 = 15;
            const SIGKILL: i32 = 9;

            let order = self.descendant_kill_order();
            if order.is_empty() {
                return;
            }
            for &(pid, expected_st) in &order {
                if let Ok(ip) = i32::try_from(pid)
                    && ip > 1
                    && matches!(
                        proc_state_ppid_starttime_in(&self.proc_root, pid),
                        Some((state, _, actual_st))
                            if actual_st == expected_st && state != 'Z' && state != 'X'
                    )
                {
                    unsafe {
                        let _ = kill(ip, SIGTERM);
                    }
                }
            }
            if !grace_period.is_zero() {
                let deadline = Instant::now() + grace_period;
                while Instant::now() < deadline {
                    if !self.has_live_descendants() {
                        return;
                    }
                    std::thread::sleep(Duration::from_millis(10));
                }
            }
            for &(pid, expected_st) in &order {
                if let Ok(ip) = i32::try_from(pid)
                    && ip > 1
                    && matches!(
                        proc_state_ppid_starttime_in(&self.proc_root, pid),
                        Some((state, _, actual_st))
                            if actual_st == expected_st && state != 'Z' && state != 'X'
                    )
                {
                    unsafe {
                        let _ = kill(ip, SIGKILL);
                    }
                }
            }
        }
        #[cfg(not(unix))]
        {
            let _ = grace_period;
        }
    }
    /// Classifies `root_pid`'s `/proc/<root_pid>/stat` state against its
    /// recorded `starttime` without reaping `Child`:
    /// - `Some(true)`: positively observed as an un-reaped zombie (`'Z'`), so
    ///   `pgid == root_pid` is still reserved and `-pgid` can be signaled before
    ///   `wait()`.
    /// - `Some(false)`: positively observed as still running (non-`'Z'`/`'X'`)
    ///   with matching `starttime`, so `try_wait()` must NOT be called right
    ///   after (avoiding the race where `root_pid` exits between `/proc` read
    ///   and `try_wait()` and gets reaped without signaling `-pgid`).
    /// - `None`: `/proc` unavailable/unreadable or `root_pid` no longer present.
    fn root_proc_zombie_or_running(&self) -> Option<bool> {
        let root_st = self.root_starttime?;
        match proc_state_ppid_starttime_in(&self.proc_root, self.root_pid) {
            Some(('Z', _, actual_st)) if actual_st == root_st => Some(true),
            Some((state, _, actual_st))
                if actual_st == root_st && state != 'Z' && state != 'X' =>
            {
                Some(false)
            }
            _ => None,
        }
    }

    /// Returns true if `root_pid` has already exited (zombie `'Z'`/`'X'`, gone,
    /// or recycled with a different `starttime`) without reaping `Child`.
    /// Without a recorded `starttime` (no `/proc`, e.g. macOS) exit cannot be
    /// observed, so this stays `false` and [`terminate_process_tree`] waits out
    /// its full `SIGTERM` grace period before escalating to `SIGKILL`.
    fn root_has_exited(&self) -> bool {
        self.root_starttime.is_some()
            && !matches!(self.root_proc_zombie_or_running(), Some(false))
    }
}

/// Sends `sig` to process group `pgid` (`kill(-pgid, sig)`); a no-op for
/// `pgid <= 1` and on non-Unix targets.
fn signal_process_group(pgid: u32, sig: i32) {
    #[cfg(unix)]
    {
        unsafe extern "C" {
            fn kill(pid: i32, sig: i32) -> i32;
        }
        if let Ok(pg) = i32::try_from(pgid)
            && pg > 1
        {
            // SAFETY: `kill(2)` takes plain integers and has no memory-safety
            // preconditions; callers only pass the group of a still un-reaped
            // root, whose id therefore cannot have been recycled.
            unsafe {
                let _ = kill(-pg, sig);
            }
        }
    }
    #[cfg(not(unix))]
    {
        let _ = (pgid, sig);
    }
}

/// Returns `Some(status)` once the root has exited on its own (`None` while it
/// runs). Where `/proc` positively shows the root as a zombie with its recorded
/// `starttime`, its process group (`pgid == root_pid`, still reserved by the
/// un-reaped zombie) is `SIGKILL`ed before the root is reaped, so a stray group
/// member spawned after the last `(pid, starttime)` scan can neither keep
/// running nor hold the output pipes open; tracked descendants that left the
/// group are killed by `(pid, starttime)`. When `/proc` positively shows the
/// root still running, `try_wait` is skipped so `root_pid` cannot exit and get
/// reaped in the window between the `/proc` read and `try_wait`. Without `/proc`
/// this falls back to `try_wait` plus tracked-descendant cleanup.
fn reap_exited_root(
    child: &mut Child,
    tree: &mut TrackedProcessTree,
    peak_rss_kib: &mut u64,
) -> std::io::Result<Option<std::process::ExitStatus>> {
    const SIGKILL: i32 = 9;
    match tree.root_proc_zombie_or_running() {
        Some(true) => {
            *peak_rss_kib = (*peak_rss_kib).max(tree.sample_rss_kib());
            signal_process_group(tree.root_pid, SIGKILL);
            tree.kill_descendants(Duration::ZERO);
            return child.wait().map(Some);
        }
        Some(false) => return Ok(None),
        None => {}
    }
    match child.try_wait()? {
        Some(status) => {
            // Already reaped: only `(pid, starttime)`-verified descendants may be
            // signaled now (never `-pgid`).
            *peak_rss_kib = (*peak_rss_kib).max(tree.sample_rss_kib());
            tree.kill_descendants(Duration::ZERO);
            Ok(Some(status))
        }
        None => Ok(None),
    }
}

/// Terminates `child` (spawned with `.process_group(0)` so `pgid == root_pid`)
/// and all tracked descendants cleanly:
/// 1. Refreshes `tree` while `child` is still un-reaped (`root_pid` cannot be
///    reused before `wait()`).
/// 2. Sends `SIGTERM` to `-pgid` and to all `(pid, starttime)`-verified
///    descendants (in case a grandchild called `setsid` / `setpgid`).
/// 3. Polls up to `grace_period` for `child` (via `/proc` zombie state without
///    reaping so `pgid == root_pid` stays reserved) and all non-zombie
///    descendants to exit.
/// 4. Escalates to `SIGKILL` on `-pgid` and any surviving verified descendants,
///    and only then reaps `child` via `child.wait()` so no zombie is left behind.
fn terminate_process_tree(child: &mut Child, tree: &mut TrackedProcessTree, grace_period: Duration) {
    let _ = tree.sample_rss_kib();

    #[cfg(unix)]
    {
        unsafe extern "C" {
            fn kill(pid: i32, sig: i32) -> i32;
        }
        const SIGTERM: i32 = 15;
        const SIGKILL: i32 = 9;

        let pgid = i32::try_from(tree.root_pid).ok().filter(|&p| p > 1);
        if let Some(pg) = pgid {
            unsafe {
                let _ = kill(-pg, SIGTERM);
            }
        }
        for (pid, expected_st) in tree.descendant_kill_order() {
            if let Ok(ip) = i32::try_from(pid)
                && ip > 1
                && proc_starttime_in(&tree.proc_root, pid) == Some(expected_st)
            {
                unsafe {
                    let _ = kill(ip, SIGTERM);
                }
            }
        }

        let deadline = Instant::now() + grace_period;
        while Instant::now() < deadline {
            let _ = tree.sample_rss_kib();
            if tree.root_has_exited() && !tree.has_live_descendants() {
                break;
            }
            std::thread::sleep(Duration::from_millis(10));
        }

        if let Some(pg) = pgid {
            unsafe {
                let _ = kill(-pg, SIGKILL);
            }
        }
        for (pid, expected_st) in tree.descendant_kill_order() {
            if let Ok(ip) = i32::try_from(pid)
                && ip > 1
                && proc_starttime_in(&tree.proc_root, pid) == Some(expected_st)
            {
                unsafe {
                    let _ = kill(ip, SIGKILL);
                }
            }
        }
    }

    let _ = child.kill();
    let _ = child.wait();
}

/// Classification of a `lake env lean` failure so `run_isolated_lean_stage` and
/// callers can distinguish RSS/timeout watchdog terminations and Lean-internal
/// memory exhaustion from genuine Lean elaboration errors or missing-toolchain
/// failures.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ItreeLeanFailureKind {
    /// Killed by the process-tree RSS watchdog (`rss_kib > rss_limit_kib`).
    RssWatchdogExceeded,
    /// Killed by the wall-clock timeout watchdog (`elapsed >= timeout`).
    WallClockTimeout,
    /// Lean's own memory cap (`-M`: `excessive memory consumption` / `out of
    /// memory`) or a root terminated by a signal (e.g. the cgroup OOM killer):
    /// resource exhaustion that smaller modules may avoid, not a rejection.
    LeanMemoryExhausted,
    /// Missing binary / systematic host setup failure (`command not found`).
    MissingToolchain,
    /// Lean elaboration / kernel / missing-output failure.
    ElaborationOrOutputFailure,
}

/// Lowercased markers of Lean memory exhaustion (mirroring `miri_eval`'s
/// `LEAN_RESOURCE_MARKERS`) plus the signal-termination tag emitted by
/// [`run_itree_lean_module_with_workers`].
const ITREE_LEAN_MEMORY_MARKERS: [&str; 4] = [
    "out of memory",
    "excessive memory consumption",
    "memory allocation failed",
    "[lean:resource_exhausted]",
];

/// Lowercased markers of Lean's other per-declaration resource limits, which
/// bisection cannot relieve but which still are not kernel rejections.
const ITREE_LEAN_LIMIT_MARKERS: [&str; 5] = [
    "(deterministic) timeout",
    "maximum number of heartbeats",
    "maximum recursion depth",
    "deep recursion",
    "stack overflow",
];

/// Classifies an error string returned by `run_itree_lean_module` or a chunk
/// runner closure.
pub fn classify_itree_lean_failure(err: &str) -> ItreeLeanFailureKind {
    let lower = err.to_ascii_lowercase();
    if err.contains("[WATCHDOG:RSS_EXCEEDED]") || err.contains("exceeded RSS limit") {
        ItreeLeanFailureKind::RssWatchdogExceeded
    } else if err.contains("[WATCHDOG:TIMEOUT]") || err.contains("exceeded wall-clock timeout") {
        ItreeLeanFailureKind::WallClockTimeout
    } else if err.contains("command not found") || err.contains("No such file or directory") {
        ItreeLeanFailureKind::MissingToolchain
    } else if ITREE_LEAN_MEMORY_MARKERS.iter().any(|m| lower.contains(m)) {
        ItreeLeanFailureKind::LeanMemoryExhausted
    } else {
        ItreeLeanFailureKind::ElaborationOrOutputFailure
    }
}

/// Whether a failed `lake env lean` run ran out of a resource or could not run
/// at all (watchdog kill, Lean memory cap or other limit, signal, missing
/// toolchain) rather than rejecting a theorem, so a kernel confirmation that
/// failed this way is inconclusive instead of `kernel_confirmed = false`.
pub fn itree_lean_failure_is_inconclusive(err: &str) -> bool {
    let lower = err.to_ascii_lowercase();
    classify_itree_lean_failure(err) != ItreeLeanFailureKind::ElaborationOrOutputFailure
        || ITREE_LEAN_LIMIT_MARKERS.iter().any(|m| lower.contains(m))
}

/// Result of running a `Command` under [`run_command_with_watchdog`].
#[derive(Debug, Clone)]
pub struct WatchdogCommandOutput {
    /// Whether the root process exited successfully (`false` when killed by the
    /// watchdog).
    pub exit_success: bool,
    /// Captured standard output.
    pub stdout: Vec<u8>,
    /// Captured standard error.
    pub stderr: Vec<u8>,
    /// Peak process-tree physical RSS observed (in KiB).
    pub peak_rss_kib: u64,
    /// Watchdog termination reason if the process tree was killed by the
    /// watchdog (`Some(ItreeLeanFailureKind::RssWatchdogExceeded | WallClockTimeout)`).
    pub watchdog_killed: Option<ItreeLeanFailureKind>,
    /// The root exited because of a signal it did not catch (outside the
    /// watchdog), e.g. the cgroup OOM killer.
    pub signal_terminated: bool,
    /// `false` when a stdout / stderr write end was still held open
    /// [`ITREE_WATCHDOG_PIPE_DRAIN_GRACE`] after the root exited and its tracked
    /// descendants were killed (the readers were abandoned, so the captured
    /// output may be incomplete).
    pub pipes_drained: bool,
}

/// Upper bound on bytes buffered per child output stream (`stdout` / `stderr`)
/// in [`WatchdogPipeReader`] (`16 MiB`), so a runaway child spewing unbounded
/// output cannot exhaust host memory before the watchdog fires.
const MAX_WATCHDOG_PIPE_CAPTURE_BYTES: usize = 16 * 1024 * 1024;

/// Background reader that drains one child pipe into a shared buffer, so the
/// captured prefix stays available even if the reader has to be abandoned.
struct WatchdogPipeReader {
    buf: std::sync::Arc<std::sync::Mutex<Vec<u8>>>,
    abandoned: std::sync::Arc<std::sync::atomic::AtomicBool>,
    handle: Option<std::thread::JoinHandle<()>>,
}

impl WatchdogPipeReader {
    fn spawn<R: Read + Send + 'static>(pipe: Option<R>) -> Self {
        let buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let abandoned = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let handle = pipe.map(|mut pipe| {
            let sink = std::sync::Arc::clone(&buf);
            let stop = std::sync::Arc::clone(&abandoned);
            std::thread::spawn(move || {
                let mut chunk = [0u8; 8192];
                loop {
                    if stop.load(std::sync::atomic::Ordering::Relaxed) {
                        break;
                    }
                    match pipe.read(&mut chunk) {
                        Ok(0) => break,
                        Ok(n) => {
                            if stop.load(std::sync::atomic::Ordering::Relaxed) {
                                break;
                            }
                            let mut guard = sink.lock().unwrap_or_else(|e| e.into_inner());
                            if guard.len() < MAX_WATCHDOG_PIPE_CAPTURE_BYTES {
                                let take = (MAX_WATCHDOG_PIPE_CAPTURE_BYTES - guard.len()).min(n);
                                guard.extend_from_slice(&chunk[..take]);
                            }
                        }
                        Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                        Err(_) => break,
                    }
                }
            })
        });
        Self {
            buf,
            abandoned,
            handle,
        }
    }

    /// Waits until `deadline` for EOF and returns the bytes read so far plus
    /// whether EOF was reached (an unfinished reader is signaled to stop and
    /// detached).
    fn finish(self, deadline: Instant) -> (Vec<u8>, bool) {
        let drained = match self.handle {
            None => true,
            Some(handle) => {
                while !handle.is_finished() && Instant::now() < deadline {
                    std::thread::sleep(Duration::from_millis(5));
                }
                let finished = handle.is_finished();
                if finished {
                    let _ = handle.join();
                } else {
                    self.abandoned
                        .store(true, std::sync::atomic::Ordering::Relaxed);
                }
                finished
            }
        };
        let bytes = self.buf.lock().unwrap_or_else(|e| e.into_inner()).clone();
        (bytes, drained)
    }
}

/// Spawns `cmd` in its own Unix process group (`.process_group(0)`, so the whole
/// `lake` -> `lean` tree is signaled atomically via `kill(-pgid)`), drains
/// stdout / stderr concurrently on background threads so a child filling a
/// 64 KiB pipe buffer never deadlocks against the polling loop, and polls the
/// tree's `(pid, starttime)`-verified `/proc` RSS and the wall-clock elapsed time.
///
/// Before killing for RSS or timeout, the root is re-polled so a process that
/// exited while `/proc` was being scanned keeps its genuine exit status (like
/// `miri_eval::run_lean_with_rss_budget`). A root that exits on its own is
/// observed as a zombie and its whole group is killed before it is reaped
/// ([`reap_exited_root`]), so no stray group member outlives the run. The call
/// returns within roughly
/// `timeout + ITREE_WATCHDOG_KILL_GRACE + ITREE_WATCHDOG_PIPE_DRAIN_GRACE` even if
/// an escaped descendant keeps an output pipe open (`pipes_drained == false`).
///
/// Process-group trade-off: unlike `miri_eval` (which keeps `lake env lean` in
/// the harness's group so terminal `Ctrl-C` reaches it), the tree lives in its
/// own group, so a harness that dies without running this function's cleanup
/// (e.g. `SIGKILL`) does not take the tree with it; `anneal-lean-run`'s
/// cgroup-scoped `MemoryMax` still bounds such an orphan.
pub fn run_command_with_watchdog(
    mut cmd: Command,
    rss_limit_kib: u64,
    timeout: Duration,
    poll_interval: Duration,
) -> Result<WatchdogCommandOutput, String> {
    cmd.stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt as _;
        cmd.process_group(0);
    }

    let mut child = cmd
        .spawn()
        .map_err(|e| format!("failed to spawn command: {e}"))?;
    let root_pid = child.id();
    let mut tree = TrackedProcessTree::new(root_pid);
    let stdout_reader = WatchdogPipeReader::spawn(child.stdout.take());
    let stderr_reader = WatchdogPipeReader::spawn(child.stderr.take());
    let max_poll = poll_interval.max(ITREE_WATCHDOG_MIN_POLL_INTERVAL);
    let mut poll = ITREE_WATCHDOG_MIN_POLL_INTERVAL.min(max_poll);

    let start = Instant::now();
    let mut peak_rss_kib = tree.sample_rss_kib();
    let mut watchdog_killed: Option<ItreeLeanFailureKind> = None;
    let (exit_success, signal_terminated) = loop {
        match reap_exited_root(&mut child, &mut tree, &mut peak_rss_kib) {
            Ok(Some(status)) => break (status.success(), status.code().is_none()),
            Ok(None) => {}
            Err(e) => {
                terminate_process_tree(&mut child, &mut tree, ITREE_WATCHDOG_KILL_GRACE);
                let deadline = Instant::now() + ITREE_WATCHDOG_PIPE_DRAIN_GRACE;
                let _ = stdout_reader.finish(deadline);
                let _ = stderr_reader.finish(deadline);
                return Err(format!("failed polling child process {root_pid}: {e}"));
            }
        }

        let rss_kib = tree.sample_rss_kib();
        peak_rss_kib = peak_rss_kib.max(rss_kib);
        let verdict = if rss_kib > rss_limit_kib {
            Some(ItreeLeanFailureKind::RssWatchdogExceeded)
        } else if start.elapsed() >= timeout {
            Some(ItreeLeanFailureKind::WallClockTimeout)
        } else {
            None
        };
        if let Some(kind) = verdict {
            // Re-check before killing: a root that exited while `/proc` was
            // scanned keeps its genuine exit status instead of being
            // misattributed to the watchdog.
            if let Ok(Some(status)) = reap_exited_root(&mut child, &mut tree, &mut peak_rss_kib) {
                break (status.success(), status.code().is_none());
            }
            watchdog_killed = Some(kind);
            terminate_process_tree(&mut child, &mut tree, ITREE_WATCHDOG_KILL_GRACE);
            break (false, false);
        }
        std::thread::sleep(poll);
        poll = poll.saturating_mul(2).min(max_poll);
    };

    let deadline = Instant::now() + ITREE_WATCHDOG_PIPE_DRAIN_GRACE;
    let (stdout, stdout_drained) = stdout_reader.finish(deadline);
    let (mut stderr, stderr_drained) = stderr_reader.finish(deadline);
    let pipes_drained = stdout_drained && stderr_drained;
    if !pipes_drained {
        stderr.extend_from_slice(
            b"\n[WATCHDOG:PIPE_HELD] output pipe still held open by an untracked descendant; \
              captured output may be incomplete\n",
        );
    }
    Ok(WatchdogCommandOutput {
        exit_success,
        stdout,
        stderr,
        peak_rss_kib,
        watchdog_killed,
        signal_terminated,
        pipes_drained,
    })
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
    /// Per-case results for every case whose chunk, per-candidate fallback, or
    /// bisected sub-chunk succeeded.
    results: BTreeMap<String, X>,
    /// Candidates (root fn names) owning at least one case without a result.
    failed_fns: BTreeSet<String>,
    /// Cases without a result whose most specific failing run (the smallest
    /// chunk, per-candidate fallback, or bisection slice containing them that
    /// was actually run) failed inconclusively per
    /// [`itree_lean_failure_is_inconclusive`] (watchdog kill, Lean resource
    /// limit, signal, missing toolchain) rather than with a Lean rejection, so
    /// the case is unchecked rather than refuted.
    inconclusive_cases: BTreeSet<String>,
    /// Truncated diagnostics for each failed chunk, fallback, or irreducible
    /// single-case bisection run.
    errors: Vec<String>,
}

thread_local! {
    /// Number of `lake env lean` workers that [`run_isolated_lean_stage`] runs
    /// concurrently with the current thread (`0` outside a stage).
    static ITREE_LEAN_STAGE_CONCURRENCY: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Sets [`ITREE_LEAN_STAGE_CONCURRENCY`] for the current thread and restores the
/// previous value on drop (including when a chunk runner panics).
struct ItreeLeanConcurrencyGuard(usize);

impl ItreeLeanConcurrencyGuard {
    fn enter(concurrency: usize) -> Self {
        Self(ITREE_LEAN_STAGE_CONCURRENCY.with(|c| c.replace(concurrency.max(1))))
    }
}

impl Drop for ItreeLeanConcurrencyGuard {
    fn drop(&mut self) {
        ITREE_LEAN_STAGE_CONCURRENCY.with(|c| c.set(self.0));
    }
}

/// Number of `lake env lean` workers running concurrently with the calling
/// thread inside [`run_isolated_lean_stage`]: the current wave's width for
/// chunk workers and `1` for the sequential per-candidate fallback and
/// bisection runs (so those get the whole memory / thread budget instead of a
/// `jobs`-way share), or `default` outside a stage.
fn itree_lean_stage_concurrency(default: usize) -> usize {
    match ITREE_LEAN_STAGE_CONCURRENCY.with(std::cell::Cell::get) {
        0 => default.max(1),
        n => n,
    }
}

/// Maximum number of *failing* bisection runs spent on one candidate with `n`
/// cases: `2 * ceil(log2 n)` isolates one irreducible case (one failing half per
/// level, plus its failing sibling at the bottom) and `+ 2` leaves room for a
/// second offender, so a candidate whose every sub-slice fails (e.g. every
/// case times out) costs `O(log n)` Lean runs instead of `2n - 2`.
fn itree_bisect_failure_budget(n: usize) -> usize {
    let ceil_log2 = (usize::BITS - n.max(1).saturating_sub(1).leading_zeros()) as usize;
    2 * ceil_log2 + 2
}

/// Normalized, sorted, deduplicated Lean `error:` blocks of a failed run: the
/// text after each `error:` marker together with any immediately following
/// indented continuation lines, so the `<file>:<line>:<col>:` location (which
/// names the per-slice module), the harness header (peak RSS, `-M`, thread
/// count), and non-error output are dropped while multi-line tactic / type-mismatch
/// payloads stay intact.
fn lean_error_signature(err: &str) -> Vec<String> {
    let mut messages: Vec<String> = Vec::new();
    let mut current: Option<String> = None;
    for line in err.lines() {
        if let Some(idx) = line.find("error:") {
            if let Some(prev) = current.take() {
                messages.push(prev);
            }
            let msg = line[idx + "error:".len()..].trim();
            if !msg.is_empty() {
                current = Some(msg.to_string());
            }
        } else if (line.starts_with(' ') || line.starts_with('\t'))
            && !line.trim().is_empty()
            && let Some(cur) = current.as_mut()
        {
            cur.push('\n');
            cur.push_str(line.trim());
        } else if let Some(prev) = current.take() {
            messages.push(prev);
        }
    }
    if let Some(prev) = current.take() {
        messages.push(prev);
    }
    messages.sort();
    messages.dedup();
    messages
}

/// Runs one chunked Lean stage with failure isolation and multi-case bisection.
///
/// `cases` are split into chunks of at most `chunk_size`, evaluated by
/// `run_chunk(label, chunk)` in waves of at most `jobs` concurrent workers.
/// A chunk only counts as successful if `run_chunk` returns a result for every
/// case in it; a failed, incomplete, or panicking chunk is re-run one candidate
/// at a time (`{stage_label}Fallback_<fn>`). Inside `run_chunk`,
/// [`itree_lean_stage_concurrency`] reports how many Lean workers run alongside
/// (the wave width, or `1` for fallback and bisection runs).
///
/// When a multi-case candidate fallback (`fn_cases.len() > 1`) fails for any
/// reason other than a missing toolchain, `fn_cases` is bisected
/// (`{stage_label}Bisect_<fn>_...`) so that:
/// 1. candidates whose combined trace module exceeded an RSS / timeout / Lean
///    memory limit recover completely when smaller sub-slices succeed;
/// 2. an irreducible single case (`slice.len() == 1`) that exceeds limits or
///    fails elaboration still lets its healthy siblings into `results`, and
///    `errors` records an explicit single-case diagnostic (a case that only
///    exceeded resource limits also lands in `inconclusive_cases`, so
///    [`itree_partially_comparable_fns`] keeps comparing its candidate on the
///    healthy siblings);
/// 3. a failure that both halves of a slice reproduce as an elaboration error is
///    treated as candidate-wide (shared definitions, not one case) and stops
///    bisection there, and at most [`itree_bisect_failure_budget`] failing runs
///    are spent per candidate, bounding the cost of systematic failures.
///
/// After [`ITREE_FALLBACK_CIRCUIT_BREAKER`] consecutive candidate fallback
/// failures without any recovery, remaining fallbacks are skipped to bound the
/// cost of systematic failures.
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
    C: Clone + Send + Sync,
    X: Send,
    K: Fn(&C) -> &str + Sync,
    F: Fn(&str, &[C]) -> Result<BTreeMap<String, X>, String> + Sync,
{
    run_isolated_lean_stage_impl(
        stage_label,
        cases,
        chunk_size,
        jobs,
        case_key,
        case_to_fn,
        run_chunk,
        false,
    )
}

/// Stage 2 confirmation variant of [`run_isolated_lean_stage`] that runs
/// partial-preserving adaptive RSS/memory chunk halving on the outer chunk wave
/// (never nested inside per-candidate `Fallback` or `Bisect`, preventing
/// `O((log k)^2)` re-splitting and duplicate watchdog kills on irreducible
/// `k == 1` singletons).
///
/// Confirmed subchunks from a partially split chunk are retained in `results`;
/// irreducible `k == 1` leaves from a single-worker wave (`wave_width == 1`) or
/// non-memory failures are recorded directly without re-running them, while
/// memory-failed `k == 1` leaves from a multi-worker wave (`wave_width > 1`)
/// get one sequential retry at full worker memory (`concurrency = 1`).
fn run_isolated_adaptive_confirm_stage<C, X, K, F>(
    stage_label: &str,
    cases: &[C],
    chunk_size: usize,
    jobs: usize,
    case_key: K,
    case_to_fn: &BTreeMap<String, String>,
    run_chunk: F,
) -> IsolatedLeanStage<X>
where
    C: Clone + Send + Sync,
    X: Send,
    K: Fn(&C) -> &str + Sync,
    F: Fn(&str, &[C]) -> Result<BTreeMap<String, X>, String> + Sync,
{
    run_isolated_lean_stage_impl(
        stage_label,
        cases,
        chunk_size,
        jobs,
        case_key,
        case_to_fn,
        run_chunk,
        true,
    )
}

#[allow(clippy::too_many_arguments)]
fn run_isolated_lean_stage_impl<C, X, K, F>(
    stage_label: &str,
    cases: &[C],
    chunk_size: usize,
    jobs: usize,
    case_key: K,
    case_to_fn: &BTreeMap<String, String>,
    run_chunk: F,
    adaptive_confirm_chunks: bool,
) -> IsolatedLeanStage<X>
where
    C: Clone + Send + Sync,
    X: Send,
    K: Fn(&C) -> &str + Sync,
    F: Fn(&str, &[C]) -> Result<BTreeMap<String, X>, String> + Sync,
{
    let chunk_size = chunk_size.max(1);
    let jobs = jobs.max(1);
    let mut results: BTreeMap<String, X> = BTreeMap::new();
    let mut errors: Vec<String> = Vec::new();
    let mut failed_chunks: Vec<Vec<C>> = Vec::new();

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
    // Sequential (fallback / bisection) runs own the whole Lean budget.
    let run_sequential = |label: &str, slice: &[C], what: &str| {
        let _concurrency = ItreeLeanConcurrencyGuard::enter(1);
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run_chunk(label, slice)))
            .unwrap_or_else(|_| Err(format!("Lean {what} worker panicked")))
    };
    // Whether the most recent (hence most specific: chunk, then fallback, then
    // ever smaller bisection slices) failing run containing each case failed
    // inconclusively.
    let mut last_failure_inconclusive: BTreeMap<String, bool> = BTreeMap::new();
    let mut note_failure = |slice: &[C], err: &str| {
        let inconclusive = itree_lean_failure_is_inconclusive(err);
        for c in slice {
            last_failure_inconclusive.insert(case_key(c).to_string(), inconclusive);
        }
    };

    let chunks: Vec<&[C]> = cases.chunks(chunk_size).collect();
    for (wave_idx, wave) in chunks.chunks(jobs).enumerate() {
        let wave_width = wave.len();
        if adaptive_confirm_chunks {
            let wave_res: Vec<(String, Result<AdaptiveConfirmChunkOutcome<C, X>, String>)> =
                std::thread::scope(|s| {
                    let handles: Vec<_> = wave
                        .iter()
                        .enumerate()
                        .map(|(i, &chunk)| {
                            let label = format!("{stage_label}Chunk{}", wave_idx * jobs + i);
                            let run_chunk = &run_chunk;
                            let case_key = &case_key;
                            let worker_label = label.clone();
                            let handle = s.spawn(move || {
                                let _concurrency = ItreeLeanConcurrencyGuard::enter(wave_width);
                                run_adaptive_confirm_chunk_collecting(
                                    &worker_label,
                                    chunk,
                                    case_key,
                                    case_to_fn,
                                    run_chunk,
                                )
                            });
                            (label, handle)
                        })
                        .collect();
                    handles
                        .into_iter()
                        .map(|(label, h)| {
                            let res = h
                                .join()
                                .map_err(|_| "Lean chunk worker panicked".to_string());
                            (label, res)
                        })
                        .collect()
                });
            for (&chunk, (label, res)) in wave.iter().zip(wave_res) {
                let outcome = match res {
                    Ok(outcome) => outcome,
                    Err(panic_err) => {
                        errors.push(format!("{label}: {panic_err}"));
                        failed_chunks.push(chunk.to_vec());
                        continue;
                    }
                };
                results.extend(outcome.confirmed);
                let mut chunk_unresolved: Vec<C> = Vec::new();
                for (sub_label, single_case, err) in outcome.irreducible_singletons {
                    let kind = classify_itree_lean_failure(&err);
                    let is_memory_limit = matches!(
                        kind,
                        ItreeLeanFailureKind::RssWatchdogExceeded
                            | ItreeLeanFailureKind::LeanMemoryExhausted
                    );
                    note_failure(std::slice::from_ref(&single_case), &err);
                    if wave_width > 1 && is_memory_limit {
                        // Retry once sequentially at full memory (`concurrency = 1`).
                        errors.push(format!("{sub_label}: {}", truncate_lean_diag(&err)));
                        chunk_unresolved.push(single_case);
                    } else {
                        let key = case_key(&single_case);
                        let fn_name = case_to_fn
                            .get(key)
                            .map(String::as_str)
                            .unwrap_or("unknown");
                        errors.push(format!(
                            "{sub_label} (irreducible single case `{key}` of `{fn_name}`): {}",
                            truncate_lean_diag(&err)
                        ));
                    }
                }
                for (sub_label, slice, err) in outcome.unresolved {
                    note_failure(&slice, &err);
                    errors.push(format!("{sub_label}: {}", truncate_lean_diag(&err)));
                    if outcome.missing_toolchain_err.is_none() {
                        chunk_unresolved.extend(slice);
                    }
                }
                if !outcome.skipped_by_abort.is_empty() {
                    if let Some(ref missing_err) = outcome.missing_toolchain_err {
                        note_failure(&outcome.skipped_by_abort, missing_err);
                    } else if wave_width > 1 && outcome.aborted_with_memory_pressure {
                        // Multi-worker wave hit systematic memory pressure; give the
                        // remaining cases a chance under sequential full-memory fallback.
                        chunk_unresolved.extend(outcome.skipped_by_abort);
                    } else {
                        errors.push(format!(
                            "{label}: adaptive Stage 2 confirm stopped after \
                             {ITREE_FALLBACK_CIRCUIT_BREAKER} consecutive irreducible leaf \
                             failures with 0 confirmed cases ({} remaining case(s) skipped)",
                            outcome.skipped_by_abort.len()
                        ));
                        note_failure(&outcome.skipped_by_abort, "");
                    }
                }
                if !chunk_unresolved.is_empty() {
                    failed_chunks.push(chunk_unresolved);
                }
            }
        } else {
            let wave_res: Vec<(String, Result<BTreeMap<String, X>, String>)> =
                std::thread::scope(|s| {
                    let handles: Vec<_> = wave
                        .iter()
                        .enumerate()
                        .map(|(i, &chunk)| {
                            let label = format!("{stage_label}Chunk{}", wave_idx * jobs + i);
                            let run_chunk = &run_chunk;
                            let worker_label = label.clone();
                            let handle = s.spawn(move || {
                                let _concurrency = ItreeLeanConcurrencyGuard::enter(wave_width);
                                run_chunk(&worker_label, chunk)
                            });
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
                    failed_chunks.push(chunk.to_vec());
                }
            }
        }
    }

    let mut fallback_successes = 0usize;
    let mut fallback_failures = 0usize;
    let mut skipped_fallbacks = 0usize;
    for chunk in &failed_chunks {
        let mut by_fn: BTreeMap<&str, Vec<C>> = BTreeMap::new();
        for c in chunk {
            if let Some(fn_name) = case_to_fn.get(case_key(c)) {
                by_fn.entry(fn_name.as_str()).or_default().push(c.clone());
            }
        }
        for (fn_name, fn_cases) in by_fn {
            if fallback_successes == 0 && fallback_failures >= ITREE_FALLBACK_CIRCUIT_BREAKER {
                skipped_fallbacks += 1;
                note_failure(&fn_cases, "");
                continue;
            }
            let label = format!("{stage_label}Fallback_{fn_name}");
            let res = run_sequential(&label, &fn_cases, "fallback");
            let e = match accept(&mut results, &fn_cases, res, &label) {
                Ok(()) => {
                    fallback_successes += 1;
                    continue;
                }
                Err(e) => e,
            };
            note_failure(&fn_cases, &e);
            let failure_kind = classify_itree_lean_failure(&e);
            errors.push(e);
            if fn_cases.len() <= 1 || failure_kind == ItreeLeanFailureKind::MissingToolchain {
                fallback_failures += 1;
                continue;
            }

            let recovered_before = results.len();
            let budget = itree_bisect_failure_budget(fn_cases.len());
            let mut failing_runs = 0usize;
            let mut unresolved_by_budget = 0usize;
            // Every stack entry is a slice of `fn_cases` already known to fail.
            let mut stack: Vec<(usize, usize)> = vec![(0, fn_cases.len())];
            while let Some((lo, hi)) = stack.pop() {
                let mid = lo + (hi - lo) / 2;
                let mut halves: Vec<(
                    usize,
                    usize,
                    Option<(ItreeLeanFailureKind, String, bool)>,
                )> = Vec::new();
                for (a, b) in [(lo, mid), (mid, hi)] {
                    if failing_runs >= budget {
                        unresolved_by_budget += b - a;
                        note_failure(&fn_cases[a..b], "");
                        continue;
                    }
                    let slice = &fn_cases[a..b];
                    let sub_label = if slice.len() == 1 {
                        format!("{stage_label}Bisect_{fn_name}_{}", case_key(&slice[0]))
                    } else {
                        format!("{stage_label}Bisect_{fn_name}_{a}_{b}")
                    };
                    let sub_res = run_sequential(&sub_label, slice, "bisect");
                    match accept(&mut results, slice, sub_res, &sub_label) {
                        Ok(()) => halves.push((a, b, None)),
                        Err(sub_err) => {
                            failing_runs += 1;
                            note_failure(slice, &sub_err);
                            let kind = classify_itree_lean_failure(&sub_err);
                            let raw_body = sub_err
                                .strip_prefix(&format!("{sub_label}: "))
                                .unwrap_or(&sub_err)
                                .to_string();
                            let error_line_count =
                                raw_body.lines().filter(|l| l.contains("error:")).count();
                            let lower_body = raw_body.to_ascii_lowercase();
                            let is_partial_tactic_or_type_err = error_line_count > 0
                                && error_line_count < slice.len()
                                && (lower_body.contains("tactic '")
                                    || lower_body.contains("tactic `")
                                    || lower_body.contains("type mismatch"));
                            let case_or_limit_specific = slice
                                .iter()
                                .any(|c| raw_body.contains(case_key(c)))
                                || itree_lean_failure_is_inconclusive(&raw_body)
                                || is_partial_tactic_or_type_err;
                            // Compare halves by their normalized Lean `error:` messages:
                            // the raw bodies embed the per-slice module path / label and
                            // peak-RSS figures, so they never compare equal verbatim.
                            let raw_body = lean_error_signature(&raw_body).join("\n");
                            if slice.len() == 1 {
                                errors.push(format!(
                                    "{sub_label} (irreducible single case `{}` of `{fn_name}`): {}",
                                    case_key(&slice[0]),
                                    truncate_lean_diag(&sub_err)
                                ));
                            } else {
                                errors.push(sub_err);
                            }
                            halves.push((a, b, Some((kind, raw_body, case_or_limit_specific))));
                        }
                    }
                }
                let candidate_wide_elaboration = match halves.as_slice() {
                    [
                        (_, _, Some((ItreeLeanFailureKind::ElaborationOrOutputFailure, b0, false))),
                        (_, _, Some((ItreeLeanFailureKind::ElaborationOrOutputFailure, b1, false))),
                    ] => !b0.is_empty() && b0 == b1,
                    _ => false,
                };
                if candidate_wide_elaboration {
                    errors.push(format!(
                        "{stage_label}Bisect_{fn_name}: both halves of cases {lo}..{hi} fail \
                         elaboration; treating the failure as candidate-wide and stopping bisection"
                    ));
                    continue;
                }
                for (a, b, failure) in halves.iter().rev() {
                    if let Some((kind, _, _)) = failure
                        && b - a > 1
                        && *kind != ItreeLeanFailureKind::MissingToolchain
                    {
                        stack.push((*a, *b));
                    }
                }
            }
            if unresolved_by_budget > 0 {
                errors.push(format!(
                    "{stage_label}Bisect_{fn_name}: bisection failure budget ({budget} failing \
                     run(s)) exhausted with {unresolved_by_budget} case(s) unresolved"
                ));
            }
            let recovered = results.len() - recovered_before;
            if recovered == fn_cases.len() {
                // All cases of `fn_name` succeeded once split into smaller
                // modules (e.g. the combined module exceeded RSS / timeout).
                fallback_successes += 1;
            } else {
                if recovered > 0 {
                    fallback_successes += 1;
                }
                fallback_failures += 1;
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
    let inconclusive_cases: BTreeSet<String> = cases
        .iter()
        .map(&case_key)
        .filter(|&k| {
            !results.contains_key(k) && last_failure_inconclusive.get(k).copied().unwrap_or(false)
        })
        .map(str::to_string)
        .collect();
    IsolatedLeanStage {
        results,
        failed_fns,
        inconclusive_cases,
        errors,
    }
}

struct AdaptiveConfirmChunkOutcome<C, X> {
    confirmed: BTreeMap<String, X>,
    irreducible_singletons: Vec<(String, C, String)>,
    unresolved: Vec<(String, Vec<C>, String)>,
    skipped_by_abort: Vec<C>,
    aborted_by_circuit_breaker: bool,
    aborted_with_memory_pressure: bool,
    missing_toolchain_err: Option<String>,
}

/// Partial-preserving adaptive Stage 2 confirmation splitter used by
/// [`run_isolated_adaptive_confirm_stage`] on the outer chunk wave.
///
/// Preserves every kernel-confirmed subchunk (`confirmed`), isolates
/// irreducible `k == 1` leaves once instead of re-running them through
/// `Fallback` + `Bisect`, and bounds systematic failures cleanly without
/// starving unrelated healthy candidates in the same chunk:
/// - A candidate with `>= ITREE_FALLBACK_CIRCUIT_BREAKER` irreducible leaf
///   failures and `0` confirmed traces has its remaining pure-candidate slices
///   skipped (`skipped_by_abort`), while slices touching other candidates still
///   run normally.
/// - If `>= ITREE_FALLBACK_CIRCUIT_BREAKER` distinct candidates fail at the
///   leaf level while the chunk has `0` confirmed traces overall (or on a
///   missing toolchain), the remaining slices of the chunk stop immediately.
fn run_adaptive_confirm_chunk_collecting<C, X, K, F>(
    base_label: &str,
    cases: &[C],
    case_key: &K,
    case_to_fn: &BTreeMap<String, String>,
    run_slice: &F,
) -> AdaptiveConfirmChunkOutcome<C, X>
where
    C: Clone,
    K: Fn(&C) -> &str,
    F: Fn(&str, &[C]) -> Result<BTreeMap<String, X>, String>,
{
    let mut outcome = AdaptiveConfirmChunkOutcome {
        confirmed: BTreeMap::new(),
        irreducible_singletons: Vec::new(),
        unresolved: Vec::new(),
        skipped_by_abort: Vec::new(),
        aborted_by_circuit_breaker: false,
        aborted_with_memory_pressure: false,
        missing_toolchain_err: None,
    };
    if cases.is_empty() {
        return outcome;
    }

    struct SplitState<'a, C, X> {
        splits: usize,
        max_depth: usize,
        confirmed_by_fn: BTreeMap<String, usize>,
        leaf_failures_by_fn: BTreeMap<String, usize>,
        failed_leaf_fns: BTreeSet<String>,
        first_unrecovered_err: Option<String>,
        outcome: &'a mut AdaptiveConfirmChunkOutcome<C, X>,
    }

    impl<C, X> SplitState<'_, C, X> {
        fn fn_for<'b>(case_to_fn: &'b BTreeMap<String, String>, key: &'b str) -> &'b str {
            case_to_fn.get(key).map(String::as_str).unwrap_or(key)
        }

        fn fn_is_exhausted(&self, fn_name: &str) -> bool {
            self.confirmed_by_fn.get(fn_name).copied().unwrap_or(0) == 0
                && self.leaf_failures_by_fn.get(fn_name).copied().unwrap_or(0)
                    >= ITREE_FALLBACK_CIRCUIT_BREAKER
        }

        fn should_skip_slice<K: Fn(&C) -> &str>(
            &self,
            slice: &[C],
            case_key: &K,
            case_to_fn: &BTreeMap<String, String>,
        ) -> bool {
            self.outcome.aborted_by_circuit_breaker
                || self.outcome.missing_toolchain_err.is_some()
                || (!slice.is_empty()
                    && slice
                        .iter()
                        .all(|c| self.fn_is_exhausted(Self::fn_for(case_to_fn, case_key(c)))))
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn split_rec<C, X, K, F>(
        base_label: &str,
        cases: &[C],
        lo: usize,
        hi: usize,
        depth: usize,
        state: &mut SplitState<'_, C, X>,
        case_key: &K,
        case_to_fn: &BTreeMap<String, String>,
        run_slice: &F,
    ) where
        C: Clone,
        K: Fn(&C) -> &str,
        F: Fn(&str, &[C]) -> Result<BTreeMap<String, X>, String>,
    {
        let slice = &cases[lo..hi];
        if state.should_skip_slice(slice, case_key, case_to_fn) {
            state.outcome.skipped_by_abort.extend_from_slice(slice);
            return;
        }
        let label = if depth == 0 {
            base_label.to_string()
        } else {
            format!("{base_label}_split_d{depth}_{lo}_{hi}")
        };
        match run_slice(&label, slice) {
            Ok(mut map) => {
                if let Some(missing) = slice.iter().find(|c| !map.contains_key(case_key(c))) {
                    let err = format!(
                        "{label}: Lean confirm subchunk produced no result for `{}`",
                        case_key(missing)
                    );
                    if state.first_unrecovered_err.is_none() {
                        state.first_unrecovered_err = Some(err.clone());
                    }
                    if slice.len() == 1 {
                        state
                            .outcome
                            .irreducible_singletons
                            .push((label, slice[0].clone(), err));
                    } else {
                        state.outcome.unresolved.push((label, slice.to_vec(), err));
                    }
                    return;
                }
                for c in slice {
                    let key = case_key(c);
                    if let Some(val) = map.remove(key) {
                        state.outcome.confirmed.insert(key.to_string(), val);
                        let fn_name = SplitState::<C, X>::fn_for(case_to_fn, key).to_string();
                        *state.confirmed_by_fn.entry(fn_name).or_insert(0) += 1;
                    }
                }
            }
            Err(err) => {
                let kind = classify_itree_lean_failure(&err);
                if kind == ItreeLeanFailureKind::MissingToolchain {
                    if state.first_unrecovered_err.is_none() {
                        state.first_unrecovered_err = Some(err.clone());
                    }
                    state.outcome.missing_toolchain_err = Some(err.clone());
                    state.outcome.unresolved.push((label, slice.to_vec(), err));
                    return;
                }
                let is_memory_limit = matches!(
                    kind,
                    ItreeLeanFailureKind::RssWatchdogExceeded
                        | ItreeLeanFailureKind::LeanMemoryExhausted
                );
                if slice.len() <= 1 {
                    if state.first_unrecovered_err.is_none() {
                        state.first_unrecovered_err = Some(err.clone());
                    }
                    if is_memory_limit {
                        state.outcome.aborted_with_memory_pressure = true;
                    }
                    let fn_name =
                        SplitState::<C, X>::fn_for(case_to_fn, case_key(&slice[0])).to_string();
                    *state.leaf_failures_by_fn.entry(fn_name.clone()).or_insert(0) += 1;
                    state.failed_leaf_fns.insert(fn_name);
                    state
                        .outcome
                        .irreducible_singletons
                        .push((label, slice[0].clone(), err));
                    if state.outcome.confirmed.is_empty()
                        && state.failed_leaf_fns.len() >= ITREE_FALLBACK_CIRCUIT_BREAKER
                    {
                        state.outcome.aborted_by_circuit_breaker = true;
                    }
                    return;
                }
                if !is_memory_limit {
                    if state.first_unrecovered_err.is_none() {
                        state.first_unrecovered_err = Some(err.clone());
                    }
                    state.outcome.unresolved.push((label, slice.to_vec(), err));
                    return;
                }
                let mid = lo + (hi - lo) / 2;
                let next_depth = depth + 1;
                state.splits += 1;
                state.max_depth = state.max_depth.max(next_depth);
                let summary = err.lines().next().unwrap_or("");
                eprintln!(
                    "itree-difftest: adaptive Stage 2 confirm split \
                     label={label} depth={next_depth} cases={} -> left={} right={} \
                     kind={kind:?} reason={summary}",
                    hi - lo,
                    mid - lo,
                    hi - mid
                );
                split_rec(
                    base_label,
                    cases,
                    lo,
                    mid,
                    next_depth,
                    state,
                    case_key,
                    case_to_fn,
                    run_slice,
                );
                split_rec(
                    base_label,
                    cases,
                    mid,
                    hi,
                    next_depth,
                    state,
                    case_key,
                    case_to_fn,
                    run_slice,
                );
            }
        }
    }

    let (splits, max_depth, first_err) = {
        let mut state = SplitState {
            splits: 0,
            max_depth: 0,
            confirmed_by_fn: BTreeMap::new(),
            leaf_failures_by_fn: BTreeMap::new(),
            failed_leaf_fns: BTreeSet::new(),
            first_unrecovered_err: None,
            outcome: &mut outcome,
        };
        split_rec(
            base_label,
            cases,
            0,
            cases.len(),
            0,
            &mut state,
            case_key,
            case_to_fn,
            run_slice,
        );
        (state.splits, state.max_depth, state.first_unrecovered_err)
    };
    if splits > 0 {
        if outcome.irreducible_singletons.is_empty()
            && outcome.unresolved.is_empty()
            && outcome.skipped_by_abort.is_empty()
        {
            eprintln!(
                "itree-difftest: adaptive Stage 2 confirm recovered \
                 label={base_label} cases={} splits={splits} max_depth={max_depth}",
                cases.len()
            );
        } else {
            let err = first_err.as_deref().unwrap_or("");
            eprintln!(
                "itree-difftest: adaptive Stage 2 confirm unrecovered \
                 label={base_label} cases={} confirmed={} splits={splits} max_depth={max_depth} \
                 kind={:?} reason={}",
                cases.len(),
                outcome.confirmed.len(),
                classify_itree_lean_failure(err),
                err.lines().next().unwrap_or("")
            );
        }
    }
    outcome
}

/// Evaluates a Stage 2 confirmation slice with deterministic adaptive halving
/// when a multi-case module exceeds memory limits
/// ([`ItreeLeanFailureKind::RssWatchdogExceeded`] or
/// [`ItreeLeanFailureKind::LeanMemoryExhausted`]).
///
/// Direct fail-closed helper used by unit tests of the standalone halving
/// primitive; production Stage 2 confirmation calls
/// [`run_isolated_adaptive_confirm_stage`] (which uses
/// [`run_adaptive_confirm_chunk_collecting`] so confirmed subchunks are
/// retained across partial failures).
#[cfg(test)]
fn run_adaptive_confirm_chunk<C, X, K, F>(
    base_label: &str,
    cases: &[C],
    case_key: &K,
    run_slice: &F,
) -> Result<BTreeMap<String, X>, String>
where
    K: Fn(&C) -> &str,
    F: Fn(&str, &[C]) -> Result<BTreeMap<String, X>, String>,
{
    if cases.is_empty() {
        return Ok(BTreeMap::new());
    }

    #[allow(clippy::too_many_arguments)]
    fn split_rec<C, X, K, F>(
        base_label: &str,
        cases: &[C],
        lo: usize,
        hi: usize,
        depth: usize,
        splits: &mut usize,
        max_depth: &mut usize,
        case_key: &K,
        run_slice: &F,
    ) -> Result<BTreeMap<String, X>, String>
    where
        K: Fn(&C) -> &str,
        F: Fn(&str, &[C]) -> Result<BTreeMap<String, X>, String>,
    {
        let slice = &cases[lo..hi];
        let label = if depth == 0 {
            base_label.to_string()
        } else {
            format!("{base_label}_split_d{depth}_{lo}_{hi}")
        };
        match run_slice(&label, slice) {
            Ok(map) => {
                if let Some(missing) = slice.iter().find(|c| !map.contains_key(case_key(c))) {
                    return Err(format!(
                        "{label}: Lean confirm subchunk produced no result for `{}`",
                        case_key(missing)
                    ));
                }
                Ok(map)
            }
            Err(err) => {
                let kind = classify_itree_lean_failure(&err);
                let is_memory_limit = matches!(
                    kind,
                    ItreeLeanFailureKind::RssWatchdogExceeded
                        | ItreeLeanFailureKind::LeanMemoryExhausted
                );
                if slice.len() <= 1 || !is_memory_limit {
                    return Err(err);
                }
                let mid = lo + (hi - lo) / 2;
                let next_depth = depth + 1;
                *splits += 1;
                *max_depth = (*max_depth).max(next_depth);
                let summary = err.lines().next().unwrap_or("");
                eprintln!(
                    "itree-difftest: adaptive Stage 2 confirm split \
                     label={label} depth={next_depth} cases={} -> left={} right={} \
                     kind={kind:?} reason={summary}",
                    hi - lo,
                    mid - lo,
                    hi - mid
                );
                let mut merged = split_rec(
                    base_label, cases, lo, mid, next_depth, splits, max_depth, case_key, run_slice,
                )?;
                let right = split_rec(
                    base_label, cases, mid, hi, next_depth, splits, max_depth, case_key, run_slice,
                )?;
                merged.extend(right);
                Ok(merged)
            }
        }
    }

    let mut splits = 0usize;
    let mut max_depth = 0usize;
    let res = split_rec(
        base_label,
        cases,
        0,
        cases.len(),
        0,
        &mut splits,
        &mut max_depth,
        case_key,
        run_slice,
    );
    if splits > 0 {
        match &res {
            Ok(_) => eprintln!(
                "itree-difftest: adaptive Stage 2 confirm recovered \
                 label={base_label} cases={} splits={splits} max_depth={max_depth}",
                cases.len()
            ),
            // The first sub-slice that could not be halved further (a `k == 1`
            // singleton or a non-memory failure) fails the whole chunk closed:
            // no partial result is reported, so `run_isolated_lean_stage`
            // re-isolates every case of the chunk per candidate.
            Err(err) => eprintln!(
                "itree-difftest: adaptive Stage 2 confirm unrecovered \
                 label={base_label} cases={} splits={splits} max_depth={max_depth} \
                 kind={:?} reason={}",
                cases.len(),
                classify_itree_lean_failure(err),
                err.lines().next().unwrap_or("")
            ),
        }
    }
    res
}

/// Candidates of `stage.failed_fns` that stay comparable on their completed
/// cases, mapped to how many of their cases are dropped: every case of the
/// candidate without a result is in [`IsolatedLeanStage::inconclusive_cases`]
/// (unchecked because of a resource limit / watchdog kill, never refuted by
/// Lean) and `may_drop` allows dropping it, and at least one case completed.
/// Every other failed candidate must be dropped whole (a Lean rejection, or no
/// completed case to compare).
fn itree_partially_comparable_fns<C, X>(
    stage: &IsolatedLeanStage<X>,
    cases: &[C],
    case_key: impl Fn(&C) -> &str,
    case_to_fn: &BTreeMap<String, String>,
    may_drop: impl Fn(&C) -> bool,
) -> BTreeMap<String, usize> {
    let mut completed: BTreeSet<&str> = BTreeSet::new();
    let mut blocked: BTreeSet<&str> = BTreeSet::new();
    let mut dropped: BTreeMap<&str, usize> = BTreeMap::new();
    for c in cases {
        let key = case_key(c);
        let Some(fn_name) = case_to_fn.get(key) else {
            continue;
        };
        if !stage.failed_fns.contains(fn_name) {
            continue;
        }
        if stage.results.contains_key(key) {
            completed.insert(fn_name);
        } else if stage.inconclusive_cases.contains(key) && may_drop(c) {
            *dropped.entry(fn_name).or_insert(0) += 1;
        } else {
            blocked.insert(fn_name);
        }
    }
    dropped
        .into_iter()
        .filter(|(f, _)| completed.contains(f) && !blocked.contains(f))
        .map(|(f, n)| (f.to_string(), n))
        .collect()
}

/// Stage 2 replacement confirmations for a partial `selected` subset of `pool`:
/// for every candidate of `stage.failed_fns` none of whose selected cases was
/// confirmed and all of whose selected cases are Stage 1 `ok` traces (`is_ok`)
/// that failed inconclusively, the first case of `pool` (in order) owned by
/// that candidate that was not selected and is a Stage 1 `ok` trace, so a
/// confirmation that merely hit a resource limit does not cost the candidate
/// its required kernel-confirmed trace. A candidate with a refuted or divergent
/// selected case gets no replacement (it is dropped whole).
fn itree_confirm_replacements<'p, C, X>(
    stage: &IsolatedLeanStage<X>,
    selected: &[C],
    pool: &'p [C],
    case_key: impl Fn(&C) -> &str,
    case_to_fn: &BTreeMap<String, String>,
    is_ok: impl Fn(&C) -> bool,
) -> Vec<&'p C> {
    let selected_keys: BTreeSet<&str> = selected.iter().map(&case_key).collect();
    let mut out = Vec::new();
    for fn_name in &stage.failed_fns {
        let owned_by_fn = |c: &&C| case_to_fn.get(case_key(c)) == Some(fn_name);
        let mut fn_selected = selected.iter().filter(owned_by_fn).peekable();
        if fn_selected.peek().is_none() {
            continue;
        }
        let needs_replacement = fn_selected.all(|c| {
            !stage.results.contains_key(case_key(c))
                && stage.inconclusive_cases.contains(case_key(c))
                && is_ok(c)
        });
        if !needs_replacement {
            continue;
        }
        if let Some(backup) = pool
            .iter()
            .filter(owned_by_fn)
            .find(|c| !selected_keys.contains(case_key(c)) && is_ok(c))
        {
            out.push(backup);
        }
    }
    out
}

fn resolve_itree_lake_bin() -> PathBuf {
    if let Ok(lake_env) = env::var("LAKE")
        && !lake_env.trim().is_empty()
    {
        return PathBuf::from(lake_env);
    }
    if let Some(toolchain_root) = cargo_anneal::setup::resolve_installed_toolchain() {
        let bundled = toolchain_root.join("lean/bin/lake");
        if bundled.is_file() {
            return bundled;
        }
    }
    if let Ok(home) = env::var("HOME") {
        let pinned = PathBuf::from(home)
            .join(".elan/toolchains/leanprover--lean4---v4.34.1/bin/lake");
        if pinned.is_file() {
            return pinned;
        }
    }
    PathBuf::from("lake")
}

/// Runs `lake build <targets...>` in `dot_anneal_dir` under
/// [`run_command_with_watchdog`], preserving `LAKE_CACHE_ENV_DEFAULTS` while
/// bounding `LEAN_NUM_THREADS`, the process tree's physical RSS, and wall-clock
/// runtime.
fn run_itree_lake_build_targets(dot_anneal_dir: &Path, targets: &[String]) -> Result<(), String> {
    let lake_bin = resolve_itree_lake_bin();
    let mut cmd = build_lake_build_command(&lake_bin, dot_anneal_dir);
    let (_lean_max_mb, rss_limit_kib) = resolve_itree_lean_rss_budget_kib(1);
    let lean_threads = resolve_itree_lean_threads(1);
    let has_explicit_lake_jobs = env::var("CARGO_ANNEAL_LAKE_JOBS")
        .ok()
        .and_then(|s| s.trim().parse::<usize>().ok())
        .is_some_and(|n| n >= 1);
    if !has_explicit_lake_jobs {
        cmd.env("LEAN_NUM_THREADS", lean_threads.to_string());
    }
    for target in targets {
        cmd.arg(target);
    }
    let timeout = resolve_itree_lean_timeout_for_cases(targets.len().max(1));
    let out = run_command_with_watchdog(
        cmd,
        rss_limit_kib,
        timeout,
        ITREE_WATCHDOG_POLL_INTERVAL,
    )
    .map_err(|e| {
        format!(
            "failed to execute '{}' in {}: {}",
            lake_bin.display(),
            dot_anneal_dir.display(),
            e
        )
    })?;

    match out.watchdog_killed {
        Some(ItreeLeanFailureKind::RssWatchdogExceeded) => {
            return Err(format!(
                "[WATCHDOG:RSS_EXCEEDED] `lake build` in {} exceeded RSS limit ({} KiB > {} KiB, LEAN_NUM_THREADS={}):\nstdout:\n{}\nstderr:\n{}",
                dot_anneal_dir.display(),
                out.peak_rss_kib,
                rss_limit_kib,
                lean_threads,
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
        Some(ItreeLeanFailureKind::WallClockTimeout) => {
            return Err(format!(
                "[WATCHDOG:TIMEOUT] `lake build` in {} exceeded wall-clock timeout ({:?} for {} target(s), peak RSS {} KiB / {} KiB, LEAN_NUM_THREADS={}):\nstdout:\n{}\nstderr:\n{}",
                dot_anneal_dir.display(),
                timeout,
                targets.len(),
                out.peak_rss_kib,
                rss_limit_kib,
                lean_threads,
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
        _ => {}
    }

    if !out.exit_success {
        let signal_note = if out.signal_terminated {
            "[LEAN:RESOURCE_EXHAUSTED] terminated by a signal (e.g. the cgroup OOM killer) "
        } else {
            ""
        };
        return Err(format!(
            "{signal_note}lake build failed in {} (peak RSS {} KiB / {} KiB, LEAN_NUM_THREADS={}):\nstdout:\n{}\nstderr:\n{}",
            dot_anneal_dir.display(),
            out.peak_rss_kib,
            rss_limit_kib,
            lean_threads,
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok(())
}

/// Writes `src` to `verify_dir/<label>.lean` and runs `lake env lean -M <mb>`
/// on it from `anneal_dir` under [`run_command_with_watchdog`], bounding
/// `LEAN_NUM_THREADS`, Lean's internal allocator (`-M`, with non-heap headroom
/// reserved for `.olean`/`.ilean` mmaps and thread arenas), the process tree's
/// physical RSS, and wall-clock runtime for one of `active_workers` concurrent
/// workers evaluating a module of `cases` trace cases.
fn run_itree_lean_module_with_workers(
    verify_dir: &Path,
    anneal_dir: &Path,
    label: &str,
    src: &str,
    active_workers: usize,
    cases: usize,
    olean_footprint_kib: Option<u64>,
) -> Result<String, String> {
    let file = verify_dir.join(format!("{label}.lean"));
    fs::write(&file, src).map_err(|e| format!("failed to write {}: {e}", file.display()))?;
    let (lean_max_mb, rss_limit_kib, lean_threads) =
        resolve_itree_lean_execution_budget(active_workers, olean_footprint_kib);
    let timeout = resolve_itree_lean_timeout_for_cases(cases);

    let mut cmd = Command::new(resolve_itree_lake_bin());
    cmd.args(["env", "lean", "-M", &lean_max_mb.to_string()])
        .arg(&file)
        .current_dir(anneal_dir)
        .env("LEAN_NUM_THREADS", lean_threads.to_string());

    let out = run_command_with_watchdog(
        cmd,
        rss_limit_kib,
        timeout,
        ITREE_WATCHDOG_POLL_INTERVAL,
    )
    .map_err(|e| format!("failed to run `lake env lean` on {}: {e}", file.display()))?;

    match out.watchdog_killed {
        Some(ItreeLeanFailureKind::RssWatchdogExceeded) => {
            return Err(format!(
                "[WATCHDOG:RSS_EXCEEDED] `{}` exceeded RSS limit ({} KiB > {} KiB, -M {} MiB, LEAN_NUM_THREADS={}):\nstdout:\n{}\nstderr:\n{}",
                file.display(),
                out.peak_rss_kib,
                rss_limit_kib,
                lean_max_mb,
                lean_threads,
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
        Some(ItreeLeanFailureKind::WallClockTimeout) => {
            return Err(format!(
                "[WATCHDOG:TIMEOUT] `{}` exceeded wall-clock timeout ({:?} for {cases} case(s), peak RSS {} KiB / {} KiB, LEAN_NUM_THREADS={}):\nstdout:\n{}\nstderr:\n{}",
                file.display(),
                timeout,
                out.peak_rss_kib,
                rss_limit_kib,
                lean_threads,
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
        _ => {}
    }

    if !out.exit_success {
        let signal_note = if out.signal_terminated {
            "[LEAN:RESOURCE_EXHAUSTED] terminated by a signal (e.g. the cgroup OOM killer) "
        } else {
            ""
        };
        return Err(format!(
            "{signal_note}`{}` failed (peak RSS {} KiB / {} KiB, -M {} MiB, LEAN_NUM_THREADS={}):\nstdout:\n{}\nstderr:\n{}",
            file.display(),
            out.peak_rss_kib,
            rss_limit_kib,
            lean_max_mb,
            lean_threads,
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// Writes `src` to `verify_dir/<label>.lean` and runs a single-case `lake env
/// lean` module under the RSS + wall-clock watchdog with concurrency `1`.
fn run_itree_lean_module(
    verify_dir: &Path,
    anneal_dir: &Path,
    label: &str,
    src: &str,
    olean_footprint_kib: Option<u64>,
) -> Result<String, String> {
    run_itree_lean_module_with_workers(
        verify_dir,
        anneal_dir,
        label,
        src,
        1,
        1,
        olean_footprint_kib,
    )
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
    /// each compared candidate (or, when that trace's confirmation was
    /// inconclusive, its next non-diverging trace) (so `agree_candidates +
    /// diverge_traces <= kernel_confirmed_traces <= distinct_traces_checked`).
    pub kernel_confirmed_traces: usize,
    /// Count of diverging traces kernel-confirmed via `by rfl`.
    pub kernel_confirmed_divergences: usize,
    /// Total distinct external-call observation path shapes (`MirObsPathKey`) observed.
    pub distinct_obs_paths: usize,
    /// Per-candidate counts of the distinct traces checked in Lean
    /// (`b{b_idx}_c{c_idx}__kernel_step -> count`), summing to
    /// `distinct_traces_checked`; traces left unchecked by resource limits are
    /// counted in `inconclusive_traces_by_candidate` instead.
    pub per_candidate_distinct_traces: BTreeMap<String, usize>,
    /// Trace counts by `TraceReplayDiag.tagName`.
    pub diag_tag_counts: BTreeMap<String, usize>,
    /// Not-compared candidate counts by reason (`compile_failed`,
    /// `staging_failed`, `empty_trace`, `lean_probe_failed`,
    /// `lean_confirm_failed`).
    pub not_compared_reasons: BTreeMap<String, usize>,
    /// Compared candidates whose Stage 1 probe or Stage 2 confirmation left
    /// some distinct traces unchecked because a watchdog / Lean resource limit
    /// hit the smallest Lean module containing them that was run (never a Lean
    /// rejection, and never an unconfirmed divergence): candidate -> number of
    /// such traces, which are excluded from `distinct_traces_checked` while the
    /// candidate is compared on its remaining traces.
    pub inconclusive_traces_by_candidate: BTreeMap<String, usize>,
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
/// and `MirInputDictionary::from_lean_mir(lean_mir_source)` with fixed boundary
/// probes that exercise all `magic & 3`, `payload_len & 3`, threshold, and
/// `PanicOnCall(0)` branches, evaluator-verified concolic trials
/// ([`explore_itree_concolic_trials`]), and `LayoutAwareByteBuilder` (using a
/// named `LayoutSpec::Struct` so `"magic"` and `"payload_len"` field hints are
/// consulted) + `EnvScheduleGenerator` fill.
///
/// Slot order:
/// 1. the fixed probes (each slot `idx` with `idx + 2 <= trials`); identity
///    candidates keep every probe verbatim (the calibration baseline whose
///    per-seed distinct-trace counts reflect seed structure), while mutated
///    candidates drop a probe whose predicted `(events, outcome)` duplicates an
///    earlier trial's (the harness would deduplicate its trace anyway);
/// 2. concolic trials relaxing the probes' boundary-call pins: `argPinTerm`
///    negations (`arg != prev_arg` under identical prefix branch decisions and
///    earlier calls) before oracle return perturbations (prefix-return pins plus
///    one perturbed return), then branch flips;
/// 3. byte-builder trials (odd ones with a reactive `EnvScheduleGenerator`
///    schedule), skipping predicted duplicates for a bounded number of draws.
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

    let evaluator = ItreeConcreteEvaluator::new(&cand.source, "kernel_step").ok();
    let predict = |magic: u32, payload_len: u32, schedule: &EnvSchedule| {
        evaluator.as_ref().and_then(|ev| {
            ev.run_kernel_step(magic, payload_len, schedule, &staged.cand_prefix)
                .ok()
        })
    };
    let is_identity = cand.applied_mutators.is_empty();
    let mut predicted_seen: BTreeSet<ItreeConcreteRun> = BTreeSet::new();
    let mut out: Vec<CandidateTrialInput> = Vec::with_capacity(count);

    // 1. Fixed boundary probes.
    let probe_slots = fixed_probes.len().min(count.saturating_sub(1));
    for &(magic, payload_len, inject_panic) in &fixed_probes[..probe_slots] {
        let schedule = if inject_panic {
            EnvSchedule::new().with_panic_on_call(0)
        } else {
            EnvSchedule::new()
        };
        if let Some(run) = predict(magic, payload_len, &schedule)
            && !predicted_seen.insert(run)
            && !is_identity
        {
            continue;
        }
        out.push(CandidateTrialInput {
            magic,
            payload_len,
            schedule,
        });
    }

    // 2. Evaluator-verified concolic trials relaxing the probes' call pins.
    let mut bases: Vec<(u32, u32)> = Vec::new();
    for &(magic, payload_len, inject_panic) in fixed_probes {
        if !inject_panic && !bases.contains(&(magic, payload_len)) {
            bases.push((magic, payload_len));
        }
    }
    if out.len() < count {
        // Concolic trials never reproduce a probe's predicted run (the explorer
        // excludes every base run), so only the free slots need synthesizing.
        for t in explore_itree_concolic_trials(
            &cand.source,
            "kernel_step",
            &staged.cand_prefix,
            &bases,
            &dict,
            count - out.len(),
            cand.seed_u64 ^ batch_seed,
        ) {
            if out.len() >= count {
                break;
            }
            if !predicted_seen.insert(t.predicted) {
                continue;
            }
            out.push(CandidateTrialInput {
                magic: t.magic,
                payload_len: t.payload_len,
                schedule: t.schedule,
            });
        }
    }

    // 3. Byte-builder + reactive oracle-schedule fill.
    let mut rng = DetRng::new(cand.seed_u64 ^ batch_seed);
    let mut dynamic_idx = 0usize;
    let max_dedup_draws = count.saturating_mul(4);
    while out.len() < count {
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
        if let Some(run) = predict(magic, payload_len, &schedule)
            && !predicted_seen.insert(run)
            && dynamic_idx <= max_dedup_draws
        {
            continue;
        }
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
    let mut inconclusive_traces_by_candidate: BTreeMap<String, usize> = BTreeMap::new();

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
            Vec<(String, crate::input_gen::MirObsPathKey, Vec<u8>)>,
        > = BTreeMap::new();
        let mut obs_sigs_by_fn: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
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
            let mut fn_obs_sigs = Vec::with_capacity(raw_traces.len());
            let mut seen_keys: BTreeSet<String> = BTreeSet::new();
            let mut distinct_for_cand: Vec<RecordedRawTrace> = Vec::new();

            for tr in raw_traces {
                let mut sig_trace = tr.clone();
                sig_trace.raw_args.clear();
                let dedup_key = encode_recorded_raw_trace_hex(&sig_trace);

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
                fn_obs_sigs.push((
                    dedup_key.clone(),
                    format!("itree:{template_and_chain}:{shape_hash}:{outcome_kind}"),
                ));
                fn_obs_records.push((
                    dedup_key.clone(),
                    crate::input_gen::MirObsPathKey {
                        fn_name: fn_name.clone(),
                        branch_tags,
                        ext_call_sequence_shape: call_seq,
                        is_panic,
                    },
                    tr.raw_args.iter().flatten().copied().collect(),
                ));

                // Deduplicate distinct traces per candidate by observable (events, outcome).
                if seen_keys.insert(dedup_key) {
                    distinct_for_cand.push(tr);
                }
            }
            obs_records_by_fn.insert(fn_name.clone(), fn_obs_records);
            obs_sigs_by_fn.insert(fn_name.clone(), fn_obs_sigs);
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
                run_itree_lake_build_targets(&anneal_dir, &targets)?;
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

        // Measure and index the built `.olean`/`.ilean` footprint once after
        // `mir_stage` so each Stage 1 / Stage 2 worker slice reserves the exact
        // mmap bytes of shared libraries plus only the specific `Mir.*` modules
        // that slice actually imports (including smaller adaptive split slices),
        // without re-walking `.lake/build/lib/lean` per chunk.
        let olean_index = measure_itree_olean_footprint_index(&anneal_dir);
        let olean_footprint = olean_index.as_ref().map(|idx| idx.footprint);
        let max_chunk_olean_kib = olean_footprint.map(|footprint| {
            footprint.worker_kib(
                mir_fn_cases.len(),
                ITREE_PROBE_CHUNK_SIZE.max(ITREE_MAX_CONFIRM_CHUNK_SIZE),
            )
        });
        let lean_jobs = resolve_itree_lean_jobs();
        eprintln!(
            "itree-difftest: Lean TraceCheck over {} distinct traces from {} candidates \
             with {lean_jobs} concurrent `lake env lean` worker(s) \
             (max_chunk_olean_kib={max_chunk_olean_kib:?}, shared={:?} KiB, \
             staged={:?} KiB across {} indexed Mir module(s) for {} candidate(s))",
            batch_cases.len(),
            compared_fn_names.len(),
            olean_footprint.map(|f| f.shared_bytes.div_ceil(1024)),
            olean_footprint.map(|f| f.staged_bytes.div_ceil(1024)),
            olean_index
                .as_ref()
                .map_or(0, |idx| idx.staged_module_bytes.len()),
            mir_fn_cases.len()
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
                let slice_olean_kib = itree_slice_olean_footprint_kib(
                    olean_index.as_ref(),
                    chunk,
                    mir_fn_cases.len(),
                    &case_to_fn,
                );
                let stdout = run_itree_lean_module_with_workers(
                    &verify_dir,
                    &anneal_dir,
                    label,
                    &src,
                    itree_lean_stage_concurrency(lean_jobs),
                    chunk.len(),
                    slice_olean_kib,
                )?;
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
        // A candidate whose only unprobed traces hit resource limits (in the
        // smallest module containing them that was run) stays compared on its
        // probed traces (the unprobed ones are unchecked, like trials never
        // run); any other failure drops it whole.
        let probe_partial = itree_partially_comparable_fns(
            &probe_stage,
            &batch_cases,
            batch_case_ident,
            &case_to_fn,
            |_| true,
        );
        for fn_name in &probe_stage.failed_fns {
            if let Some(&dropped) = probe_partial.get(fn_name) {
                eprintln!(
                    "itree-difftest: `{fn_name}` partially compared: {dropped} trace(s) \
                     inconclusive in Stage 1 Lean probe (watchdog / Lean resource limits)"
                );
                *inconclusive_traces_by_candidate
                    .entry(fn_name.clone())
                    .or_insert(0) += dropped;
                continue;
            }
            if compared_fn_names.remove(fn_name) {
                eprintln!("itree-difftest: `{fn_name}` not compared: lean_probe_failed");
                *not_compared_reasons
                    .entry("lean_probe_failed".to_string())
                    .or_insert(0) += 1;
            }
        }
        let probe_map = probe_stage.results;
        batch_cases.retain(|c| {
            probe_map.contains_key(&c.case_ident)
                && case_to_fn
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
        // candidate (replaced by its next `ok` trace when that confirmation is
        // inconclusive). `kernel_confirmed_traces` counts only traces whose
        // theorems were actually checked by the Lean kernel.
        let mut confirm_cases: Vec<BatchTraceEvalCase> =
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
        let run_confirm_slice = |label: &str, slice: &[BatchTraceEvalCase]| {
            let src = render_batch_trace_eval_lean_module(&format!("Proof.{label}"), slice, false);
            let slice_olean_kib = itree_slice_olean_footprint_kib(
                olean_index.as_ref(),
                slice,
                mir_fn_cases.len(),
                &case_to_fn,
            );
            run_itree_lean_module_with_workers(
                &verify_dir,
                &anneal_dir,
                label,
                &src,
                itree_lean_stage_concurrency(lean_jobs),
                slice.len(),
                slice_olean_kib,
            )?;
            Ok(slice
                .iter()
                .map(|c| {
                    (
                        c.case_ident.clone(),
                        extract_itree_confirm_theorem(&src, &c.case_ident),
                    )
                })
                .collect::<BTreeMap<String, String>>())
        };
        let mut confirm_stage = run_isolated_adaptive_confirm_stage(
            "ItreeDiffBatchConfirm",
            &confirm_cases,
            confirm_chunk_size,
            lean_jobs,
            batch_case_ident,
            &case_to_fn,
            &run_confirm_slice,
        );
        // When `batch_cases.len() > ITREE_FULL_CONFIRM_MAX_TRACES`, each agreeing
        // candidate had only its first `ok` trace selected into `confirm_cases`.
        // While any candidate's selected `ok` trace(s) all hit a watchdog /
        // resource limit (`inconclusive_cases`), confirm the candidate's next
        // unselected Stage-1 `ok` trace so it can still obtain at least one
        // kernel-confirmed trace even if multiple `ok` traces time out.
        let mut rep_round = 0usize;
        while confirm_cases.len() < batch_cases.len() && !confirm_stage.failed_fns.is_empty() {
            let replacement_cases: Vec<BatchTraceEvalCase> = itree_confirm_replacements(
                &confirm_stage,
                &confirm_cases,
                &batch_cases,
                batch_case_ident,
                &case_to_fn,
                |c| c.expected_diag_tag.as_deref() == Some("ok"),
            )
            .into_iter()
            .cloned()
            .collect();
            if replacement_cases.is_empty() {
                break;
            }
            let stage_label = if rep_round == 0 {
                "ItreeDiffBatchConfirmReplacement".to_string()
            } else {
                format!("ItreeDiffBatchConfirmReplacement{}", rep_round + 1)
            };
            rep_round += 1;
            let rep_stage = run_isolated_adaptive_confirm_stage(
                &stage_label,
                &replacement_cases,
                confirm_chunk_size,
                lean_jobs,
                batch_case_ident,
                &case_to_fn,
                &run_confirm_slice,
            );
            confirm_cases.extend(replacement_cases);
            confirm_stage.results.extend(rep_stage.results);
            confirm_stage
                .inconclusive_cases
                .extend(rep_stage.inconclusive_cases);
            confirm_stage.errors.extend(rep_stage.errors);
            confirm_stage.failed_fns = confirm_cases
                .iter()
                .filter(|c| !confirm_stage.results.contains_key(&c.case_ident))
                .filter_map(|c| case_to_fn.get(&c.case_ident).cloned())
                .collect();
        }
        for err in &confirm_stage.errors {
            eprintln!("itree-difftest: Stage 2 Lean kernel confirmation failure: {err}");
        }
        // A candidate keeps being compared without its unconfirmed traces only
        // if each of them is a Stage 1 `ok` trace whose confirmation hit
        // resource limits, and at least one of its traces was kernel-confirmed:
        // an unconfirmed divergence must never be dropped (that would report
        // the candidate as agreeing), so it drops the candidate whole, as does
        // any kernel rejection.
        let confirm_partial = itree_partially_comparable_fns(
            &confirm_stage,
            &confirm_cases,
            batch_case_ident,
            &case_to_fn,
            |c| c.expected_diag_tag.as_deref() == Some("ok"),
        );
        for fn_name in &confirm_stage.failed_fns {
            if let Some(&dropped) = confirm_partial.get(fn_name) {
                eprintln!(
                    "itree-difftest: `{fn_name}` partially compared: {dropped} `ok` trace(s) \
                     inconclusive in Stage 2 Lean kernel confirmation (watchdog / Lean \
                     resource limits)"
                );
                *inconclusive_traces_by_candidate
                    .entry(fn_name.clone())
                    .or_insert(0) += dropped;
                continue;
            }
            if compared_fn_names.remove(fn_name) {
                eprintln!("itree-difftest: `{fn_name}` not compared: lean_confirm_failed");
                *not_compared_reasons
                    .entry("lean_confirm_failed".to_string())
                    .or_insert(0) += 1;
            }
        }
        let confirmed_theorems: BTreeMap<String, String> = confirm_stage.results;
        let unconfirmed_selected: BTreeSet<&str> = confirm_cases
            .iter()
            .filter(|c| !confirmed_theorems.contains_key(&c.case_ident))
            .map(|c| c.case_ident.as_str())
            .collect();
        batch_cases.retain(|c| {
            !unconfirmed_selected.contains(c.case_ident.as_str())
                && case_to_fn
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
        per_candidate_distinct_traces.clear();
        let mut checked_dedup_keys_by_fn: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for case in &batch_cases {
            if let Some(fn_name) = case_to_fn.get(&case.case_ident)
                && compared_fn_names.contains(fn_name)
            {
                *per_candidate_distinct_traces
                    .entry(fn_name.clone())
                    .or_insert(0) += 1;
                let mut sig_trace = case.trace.clone();
                sig_trace.raw_args.clear();
                checked_dedup_keys_by_fn
                    .entry(fn_name.clone())
                    .or_default()
                    .insert(encode_recorded_raw_trace_hex(&sig_trace));
            }
        }

        let mut obs_path_set = MirObsPathSet::new();
        let mut obs_path_signatures_set = BTreeSet::new();
        for fn_name in &compared_fn_names {
            let Some(checked_keys) = checked_dedup_keys_by_fn.get(fn_name) else {
                continue;
            };
            if let Some(records) = obs_records_by_fn.get(fn_name) {
                for (dedup_key, key, args) in records {
                    if checked_keys.contains(dedup_key) {
                        obs_path_set.record_execution(key.clone(), args.clone());
                    }
                }
            }
            if let Some(sigs) = obs_sigs_by_fn.get(fn_name) {
                for (dedup_key, sig) in sigs {
                    if checked_keys.contains(dedup_key) {
                        obs_path_signatures_set.insert(sig.clone());
                    }
                }
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
        inconclusive_traces_by_candidate.retain(|f, _| compared_fn_names.contains(f));

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
            inconclusive_traces_by_candidate,
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
    /// `oracle_evaluations` unless the evaluator is memoized ([`MemoizedOracle`]);
    /// when several shrinks of one candidate share a memo, it counts only the
    /// runs that this shrink executed, so it can be `0` when every query was
    /// answered by runs of an earlier shrink.
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

    /// Assign one of `minimized_traces` to each finding that this shrink
    /// minimized, given the findings' original `trace_hex`es in finding order.
    ///
    /// A finding whose own trace the minimized candidate reproduced gets that
    /// trace; the other findings get the remaining traces in order; and traces
    /// are reused (round-robin from the first) only when the minimized candidate
    /// has fewer matching traces than there are findings, so that the findings'
    /// bundles stay distinct whenever enough witnesses exist. Every finding gets
    /// `None` when shrinking did not reduce the chain.
    pub fn assign_minimized_traces(
        &self,
        finding_trace_hexes: &[&str],
    ) -> Vec<Option<&ItreeTraceVerdict>> {
        let traces = &self.minimized_traces;
        if !self.is_reduced() || traces.is_empty() {
            return vec![None; finding_trace_hexes.len()];
        }
        let mut used = vec![false; traces.len()];
        let mut assigned: Vec<Option<usize>> = finding_trace_hexes
            .iter()
            .map(|hex| {
                let t = (0..traces.len()).find(|&t| !used[t] && traces[t].trace_hex == *hex)?;
                used[t] = true;
                Some(t)
            })
            .collect();
        let mut unused = (0..traces.len()).filter(|&t| !used[t]).collect::<Vec<_>>().into_iter();
        let mut reused = (0..traces.len()).cycle();
        for slot in assigned.iter_mut().filter(|slot| slot.is_none()) {
            *slot = unused.next().or_else(|| reused.next());
        }
        assigned.into_iter().map(|t| t.map(|t| &traces[t])).collect()
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
    // A partial comparison gives no judgment: the signature may live on one of
    // the traces left unchecked by a resource limit.
    if let Some(dropped) = report.inconclusive_traces_by_candidate.get(&target_fn) {
        return Err(format!(
            "`{target_fn}` was only partially compared ({dropped} trace(s) inconclusive \
             under Lean resource limits)"
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

/// One live-oracle query of an ITree shrink: [`evaluate_itree_candidate_live`],
/// with a run that could not compare `sub` logged and answered `None` (an oracle
/// failure).
fn query_itree_shrink_oracle(
    sub: &GeneratedItreeCandidate,
    ctx: &ItreeShrinkContext<'_>,
) -> Option<ItreeCandidateEvaluation> {
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
    let mut memo =
        MemoizedOracle::new(|sub: &GeneratedItreeCandidate| query_itree_shrink_oracle(sub, ctx));
    let mut res = minimize_itree_candidate_mutations_with(cand, seeds, signature, |sub| {
        memo.eval(sub.source.clone(), sub)
    });
    res.executed_oracle_runs = memo.executed_runs;
    res
}

/// Shrink the divergent candidate `cand` once for each of its distinct
/// `signatures`, pre-checking reductions with `compile_fn` and judging them with
/// the live oracle `live`, which all of the shrinks share.
///
/// A program that one shrink judged is never re-run by a later shrink (its
/// query is a cache hit), and each result's `executed_oracle_runs` counts only
/// the runs that its own shrink executed, so summing it over the results counts
/// every executed run exactly once.
fn shrink_itree_candidate_signatures<C, F>(
    cand: &GeneratedItreeCandidate,
    seeds: &[&str],
    signatures: &[ItreeDiscrepancySignature],
    mut compile_fn: C,
    live: &mut MemoizedOracle<String, Option<ItreeCandidateEvaluation>, F>,
) -> Vec<ItreeCandidateShrinkResult>
where
    C: FnMut(&GeneratedItreeCandidate) -> bool,
    F: FnMut(&GeneratedItreeCandidate) -> Option<ItreeCandidateEvaluation>,
{
    signatures
        .iter()
        .map(|signature| {
            let executed_before = live.executed_runs;
            let mut res = minimize_itree_candidate_mutations_with_compile_check(
                cand,
                seeds,
                signature,
                &mut compile_fn,
                |sub| live.eval(sub.source.clone(), sub),
            );
            res.executed_oracle_runs = live.executed_runs - executed_before;
            res
        })
        .collect()
}

/// Shrink every finding of `report` against the live oracle and refresh the
/// finding's repro-facing artifacts (`repro.rs` source, trace, diagnosis, MIR,
/// and kernel theorems) from the run that accepted the minimized candidate.
///
/// Findings of one candidate with the same signature (`diag_tag` and original
/// `kernel_confirmed`) share one shrink, and their bundles get distinct traces
/// of the minimized candidate whenever it has enough matching traces
/// ([`ItreeCandidateShrinkResult::assign_minimized_traces`]). All shrinks share
/// one memoized compile pre-check, and the shrinks of one candidate share one
/// [`MemoizedOracle`] for the live oracle, so no program is compiled or judged
/// twice; each shrink's `executed_oracle_runs` counts only the live runs that it
/// executed itself.
fn shrink_itree_findings(
    report: &mut ItreeCampaignEvalReport,
    mode: &str,
    seed: u64,
    batches: &[Vec<GeneratedItreeCandidate>],
    batch_size: usize,
    options: &ItreeEvalOptions,
) {
    type ShrinkKey = (String, String, bool);
    let shrink_key = |f: &ItreeFindingBundle| -> ShrinkKey {
        (f.fn_name.clone(), f.diag_tag.clone(), f.kernel_confirmed)
    };
    // Findings (by index) of each shrink, and each candidate's distinct
    // signatures, in finding order.
    let mut members: BTreeMap<ShrinkKey, Vec<usize>> = BTreeMap::new();
    let mut signatures_by_fn: Vec<(String, Vec<ItreeDiscrepancySignature>)> = Vec::new();
    for (idx, finding) in report.findings.iter().enumerate() {
        members.entry(shrink_key(finding)).or_default().push(idx);
        let signature = ItreeDiscrepancySignature::of_finding(finding);
        match signatures_by_fn.iter_mut().find(|(f, _)| *f == finding.fn_name) {
            Some((_, signatures)) if signatures.contains(&signature) => {}
            Some((_, signatures)) => signatures.push(signature),
            None => signatures_by_fn.push((finding.fn_name.clone(), vec![signature])),
        }
    }

    let entries = batch_entries(batches);
    let mut compile_memo = MemoizedOracle::new(itree_candidate_passes_strict_compile);
    let mut shrinks: BTreeMap<ShrinkKey, ItreeCandidateShrinkResult> = BTreeMap::new();
    for (fn_name, signatures) in &signatures_by_fn {
        let Some(entry) = entries.iter().find(|e| e.root_fn_name() == *fn_name) else {
            continue;
        };
        let ctx = ItreeShrinkContext {
            mode,
            seed,
            batches,
            batch_size,
            options,
            b_idx: entry.b_idx,
            c_idx: entry.c_idx,
        };
        let mut live = MemoizedOracle::new(|sub: &GeneratedItreeCandidate| {
            query_itree_shrink_oracle(sub, &ctx)
        });
        let results = shrink_itree_candidate_signatures(
            entry.cand,
            ITREE_SAFE_SEEDS,
            signatures,
            |sub| compile_memo.eval(sub.source.clone(), sub),
            &mut live,
        );
        for (signature, res) in signatures.iter().zip(results) {
            let key = (
                fn_name.clone(),
                signature.diag_tag.clone(),
                signature.kernel_confirmed,
            );
            shrinks.insert(key, res);
        }
    }

    for (key, idxs) in members {
        let Some(res) = shrinks.get(&key) else {
            for idx in idxs {
                report.findings[idx].shrink_status = format!(
                    "skipped_shrinker_error: `{}` names no evaluated candidate",
                    key.0
                );
            }
            continue;
        };
        let original_hexes: Vec<String> =
            idxs.iter().map(|&idx| report.findings[idx].trace_hex.clone()).collect();
        let hex_refs: Vec<&str> = original_hexes.iter().map(String::as_str).collect();
        let traces = res.assign_minimized_traces(&hex_refs);
        for (&idx, trace) in idxs.iter().zip(traces) {
            let finding = &mut report.findings[idx];
            finding.original_mutator_chain = res.original_mutator_chain.clone();
            finding.minimized_mutator_chain = res.minimized_mutator_chain.clone();
            finding.shrink_evaluations = res.shrink_evaluations;
            finding.executed_oracle_runs = res.executed_oracle_runs;
            finding.shrink_status = res.status.slug().to_string();
            if let Some(trace) = trace {
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
        run_itree_lake_build_targets(&anneal_dir, &lake_targets)?;
        let olean_index = measure_itree_olean_footprint_index(&anneal_dir);
        let olean_footprint_kib = olean_index.as_ref().map(|idx| {
            let modules = std::iter::once(case.config.root_mir_module.as_str())
                .chain(case.config.callee_sig_modules.iter().map(String::as_str))
                .chain(
                    case.config
                        .inlined_callee_modules
                        .iter()
                        .map(String::as_str),
                );
            idx.worker_kib_for_modules(modules, 1, 1)
        });

        let verify_dir = anneal_dir.join("generated/Verify/ItreeDiffStaged");
        fs::create_dir_all(&verify_dir)
            .map_err(|e| format!("failed to create {}: {e}", verify_dir.display()))?;

        let probe_src = render_batch_trace_probe_lean_module(
            "Proof.ItreeDiffReproProbe",
            std::slice::from_ref(&case),
        );
        let probe_stdout = run_itree_lean_module(
            &verify_dir,
            &anneal_dir,
            "ItreeDiffReproProbe",
            &probe_src,
            olean_footprint_kib,
        )
        .map_err(|e| format!("repro probe failed:\n{e}"))?;
        let probe_map = parse_batch_trace_probe_output(&probe_stdout);
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
        // A watchdog kill, Lean resource limit, signal, or missing toolchain is
        // inconclusive, never a kernel rejection (`kernel_confirmed = false`).
        let kernel_confirmed = match run_itree_lean_module(
            &verify_dir,
            &anneal_dir,
            "ItreeDiffRepro",
            &confirm_src,
            olean_footprint_kib,
        ) {
            Ok(_) => true,
            Err(e) if itree_lean_failure_is_inconclusive(&e) => {
                return Err(format!(
                    "repro kernel confirmation inconclusive (resource or toolchain failure, \
                     not a kernel rejection):\n{}",
                    truncate_lean_diag(&e)
                ));
            }
            Err(_) => false,
        };
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
         \x20 \"inconclusive_traces_by_candidate\": {},\n\
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
        render_usize_map_json(&report.inconclusive_traces_by_candidate, 2),
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

    if !report.inconclusive_traces_by_candidate.is_empty() {
        out.push_str("\n## Partially Compared Candidates (Inconclusive Traces)\n\n");
        out.push_str(
            "| Candidate Root Function | Traces Unchecked (Lean Resource Limits) |\n\
             | :--- | ---: |\n",
        );
        for (fn_name, count) in &report.inconclusive_traces_by_candidate {
            out.push_str(&format!("| `{fn_name}` | {count} |\n"));
        }
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
        // 32 GiB host: always 1 worker, even with > 24 GiB available.
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

        // A finding keeps its own trace when the minimized candidate reproduced
        // it, the other findings take the remaining traces in order, and traces
        // are reused (round-robin) only once every trace has been assigned.
        assert_eq!(res.assign_minimized_traces(&["ff00", "ff11"]), vec![Some(&t0), Some(&t1)]);
        assert_eq!(res.assign_minimized_traces(&["ff00", "aa00"]), vec![Some(&t1), Some(&t0)]);
        assert_eq!(res.assign_minimized_traces(&["aa00", "aa00"]), vec![Some(&t0), Some(&t1)]);
        assert_eq!(
            res.assign_minimized_traces(&["bb11", "ff00", "ff11"]),
            vec![Some(&t1), Some(&t0), Some(&t0)]
        );
        assert_eq!(
            res.assign_minimized_traces(&["f1", "f2", "f3", "f4", "f5"]),
            vec![Some(&t0), Some(&t1), Some(&t0), Some(&t1), Some(&t0)]
        );
        assert!(res.assign_minimized_traces(&[]).is_empty());

        // A shrink that did not reduce the chain refreshes no finding.
        let unreduced =
            unshrunk_itree_result(&cand, ItreeShrinkStatus::AlreadyOneMinimal, (3, 3, 0, 0));
        assert_eq!(unreduced.assign_minimized_traces(&["aa00", "ff11"]), vec![None, None]);
    }

    /// The shrinks of one candidate's distinct signatures share one live-oracle
    /// memo: a program that the first shrink judged is a cache hit for the
    /// second, and each shrink reports only the live runs that it executed.
    #[test]
    fn itree_signature_shrinks_share_the_live_memo_and_count_their_own_runs() {
        let cand = generated_itree_candidate_with_passes(2);
        let (base, steps) =
            reconstruct_itree_mutation_steps(&cand, ITREE_SAFE_SEEDS).expect("reconstruct");
        let subsets = itree_subset_source_map(&cand, &base, &steps);
        let outcome_trace = trace_verdict("seed_t0", "outcome_mismatch", true);
        let event_trace = trace_verdict("seed_t1", "event_mismatch", true);
        let event_signature = ItreeDiscrepancySignature {
            diag_tag: "event_mismatch".to_string(),
            kernel_confirmed: true,
        };
        let mut judged: Vec<u32> = Vec::new();
        let mut live = MemoizedOracle::new(|sub: &GeneratedItreeCandidate| {
            judged.push(subsets[&sub.source]);
            if subsets[&sub.source] == 0b00 {
                divergent(vec![outcome_trace.clone(), event_trace.clone()])
            } else {
                divergent(Vec::new())
            }
        });
        let results = shrink_itree_candidate_signatures(
            &cand,
            ITREE_SAFE_SEEDS,
            &[outcome_mismatch_signature(), event_signature],
            |_| true,
            &mut live,
        );
        let (executed_runs, cache_hits) = (live.executed_runs, live.cache_hits);
        drop(live);

        assert_eq!(results.len(), 2);
        for (res, trace) in results.iter().zip([&outcome_trace, &event_trace]) {
            assert_eq!(res.status, ItreeShrinkStatus::Minimized);
            assert!(res.minimized_mutator_chain.is_empty());
            assert_eq!(res.minimized_traces, vec![trace.clone()]);
            assert_eq!((res.shrink_evaluations, res.oracle_evaluations), (1, 1));
        }
        assert_eq!(judged, vec![0b00], "`[]` must be judged exactly once");
        assert_eq!((executed_runs, cache_hits), (1, 1));
        assert_eq!(
            results.iter().map(|r| r.executed_oracle_runs).collect::<Vec<_>>(),
            vec![1, 0],
            "the second shrink's `[]` query is answered by the first shrink's run"
        );
    }

    #[test]
    fn itree_ddmin_shrinks_ep1_multi_callee_and_bit_sat_chains_to_one_minimal() {
        const MARKERS: [&str; 2] = ["__anneal_itree_outlined_stage2_", "__bit_mix"];
        let sig = outcome_mismatch_signature();
        let mut covered = BTreeSet::new();

        for seed_idx in 0..64u64 {
            if covered.len() == MARKERS.len() {
                break;
            }
            for cand in generate_itree_batch(ITREE_SAFE_SEEDS, 16, 0xE17E_0000 + seed_idx) {
                if cand.applied_mutators.len() < 2 {
                    continue;
                }
                let Some((base, steps)) =
                    reconstruct_itree_mutation_steps(&cand, ITREE_SAFE_SEEDS)
                else {
                    continue;
                };
                for &marker in &MARKERS {
                    if covered.contains(marker) || !cand.source.contains(marker) {
                        continue;
                    }
                    let res = minimize_itree_candidate_mutations_with_compile_check(
                        &cand,
                        ITREE_SAFE_SEEDS,
                        &sig,
                        |_| true,
                        |sub| {
                            if sub.source.contains(marker) {
                                divergent(vec![trace_verdict("ep1_t0", "outcome_mismatch", true)])
                            } else {
                                divergent(Vec::new())
                            }
                        },
                    );
                    assert!(
                        matches!(
                            res.status,
                            ItreeShrinkStatus::Minimized | ItreeShrinkStatus::AlreadyOneMinimal
                        ),
                        "`{marker}`: unexpected ITree shrink status {:?}",
                        res.status
                    );
                    assert!(res.minimized_candidate.source.contains(marker));
                    assert!(!crate::mutators_itree::contains_unsafe_token(
                        &res.minimized_candidate.source
                    ));
                    let n = steps.len();
                    let replay_mask = |mask: u32| {
                        let kept: Vec<ItreeMutationStep> = (0..n)
                            .filter(|i| mask & (1 << i) != 0)
                            .map(|i| steps[i].clone())
                            .collect();
                        replay_itree_mutation_steps(&cand, &base, &kept)
                    };
                    let kept_masks: Vec<u32> = (0..(1u32 << n))
                        .filter(|&mask| {
                            replay_mask(mask).source == res.minimized_candidate.source
                        })
                        .collect();
                    assert!(
                        !kept_masks.is_empty(),
                        "`{marker}`: minimized ITree candidate is not a replayable subsequence"
                    );
                    assert!(
                        kept_masks.iter().any(|&mask| {
                            (0..n)
                                .filter(|i| mask & (1 << i) != 0)
                                .all(|i| !replay_mask(mask & !(1 << i)).source.contains(marker))
                        }),
                        "`{marker}`: minimized ITree chain {:?} is not 1-minimal",
                        res.minimized_mutator_chain
                    );
                    covered.insert(marker);
                }
            }
        }
        assert_eq!(
            covered.len(),
            MARKERS.len(),
            "expected ITree ddmin coverage of both Episode 1 variants, covered {covered:?}"
        );
    }

    #[test]
    fn cgroup_v1_v2_memory_and_cpu_quotas_and_lean_budgets_respect_tightest_limits() {
        let root = std::env::temp_dir().join(format!(
            "anneal-itree-cg-v1v2-test-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        let v2_leaf = root.join("v2/user.slice/run.scope");
        fs::create_dir_all(&v2_leaf).expect("create v2 cgroup tree");
        // user.slice: memory.max = 24 GiB, memory.high = 16 GiB (tighter than max),
        // memory.stat anon=3 GiB, shmem=1 GiB, file=8 GiB (reclaimable page cache
        // ignored in working-set calculation) -> 16 - 4 = 12 GiB headroom.
        fs::write(
            root.join("v2/user.slice/memory.max"),
            format!("{}\n", 24 * GIB_KIB * 1024),
        )
        .unwrap();
        fs::write(
            root.join("v2/user.slice/memory.high"),
            format!("{}\n", 16 * GIB_KIB * 1024),
        )
        .unwrap();
        fs::write(
            root.join("v2/user.slice/memory.stat"),
            format!(
                "anon {}\nfile {}\nshmem {}\n",
                3 * GIB_KIB * 1024,
                8 * GIB_KIB * 1024,
                GIB_KIB * 1024
            ),
        )
        .unwrap();
        fs::write(root.join("v2/user.slice/cpu.max"), "600000 100000\n").unwrap();
        // run.scope: memory.max = max, memory.high = 10 GiB, memory.stat anon=2 GiB -> 8 GiB headroom,
        // cpu.max = 250000 100000 -> ceil(2.5) = 3 cores.
        fs::write(v2_leaf.join("memory.max"), "max\n").unwrap();
        fs::write(
            v2_leaf.join("memory.high"),
            format!("{}\n", 10 * GIB_KIB * 1024),
        )
        .unwrap();
        fs::write(
            v2_leaf.join("memory.stat"),
            format!("anon {}\nshmem 0\n", 2 * GIB_KIB * 1024),
        )
        .unwrap();
        fs::write(v2_leaf.join("cpu.max"), "250000 100000\n").unwrap();

        let (v2_limit, v2_headroom) =
            cgroup_memory_limits_kib(&root.join("v2"), "0::/user.slice/run.scope\n");
        assert_eq!(v2_limit, Some(10 * GIB_KIB));
        assert_eq!(v2_headroom, Some(8 * GIB_KIB));
        assert_eq!(
            cgroup_cpu_quota_cores(&root.join("v2"), "0::/user.slice/run.scope\n"),
            Some(3)
        );

        // Cgroup v1 hierarchy with hierarchical_memory_limit and cfs_quota_us.
        let v1_mem = root.join("v1/memory/kubepods/pod1");
        let v1_cpu = root.join("v1/cpu,cpuacct/kubepods/pod1");
        fs::create_dir_all(&v1_mem).unwrap();
        fs::create_dir_all(&v1_cpu).unwrap();
        fs::write(
            v1_mem.join("memory.limit_in_bytes"),
            format!("{}\n", 12 * GIB_KIB * 1024),
        )
        .unwrap();
        fs::write(
            v1_mem.join("memory.stat"),
            format!(
                "hierarchical_memory_limit {}\ntotal_rss {}\ntotal_shmem {}\n",
                8 * GIB_KIB * 1024,
                2 * GIB_KIB * 1024,
                GIB_KIB * 1024
            ),
        )
        .unwrap();
        fs::write(v1_cpu.join("cpu.cfs_quota_us"), "400000\n").unwrap();
        fs::write(v1_cpu.join("cpu.cfs_period_us"), "100000\n").unwrap();

        let v1_cg_text = "6:cpu,cpuacct:/kubepods/pod1\n12:memory:/kubepods/pod1\n";
        let (v1_limit, v1_headroom) = cgroup_memory_limits_kib(&root.join("v1"), v1_cg_text);
        assert_eq!(v1_limit, Some(8 * GIB_KIB));
        assert_eq!(v1_headroom, Some(5 * GIB_KIB));
        assert_eq!(
            cgroup_cpu_quota_cores(&root.join("v1"), v1_cg_text),
            Some(4)
        );

        // Thread & RSS budget calculations.
        assert_eq!(
            itree_lean_threads_for_resources(16, Some(4), Some(12 * GIB_KIB), 2),
            2
        );
        assert_eq!(
            itree_lean_threads_for_resources(16, None, Some(3 * GIB_KIB), 1),
            1
        );
        let (lean_mb, rss_kib) =
            itree_lean_rss_budget_kib(Some(10 * GIB_KIB), Some(5 * GIB_KIB), 2);
        // 5 GiB avail -> reserve 1 GiB -> 4 GiB usable / 2 workers = 2 GiB per worker;
        // non-heap reserve (512 MiB olean + 2 * 128 MiB thread arenas = 768 MiB) leaves
        // 1280 MiB for Lean's `-M` cap (`1280 * 1024 + 768 * 1024 == 2 GiB`).
        let reserve_kib =
            itree_lean_non_heap_reserve_kib(rss_kib, ITREE_LEAN_MAX_THREADS_UNDER_8GIB_RSS, None);
        assert_eq!(rss_kib, 2 * GIB_KIB);
        assert_eq!(reserve_kib, 768 * 1024);
        assert_eq!(lean_mb, 1280);
        assert!(lean_mb * 1024 + reserve_kib <= rss_kib);
        assert!(lean_mb * 1024 < rss_kib);

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn tracked_process_tree_measures_rss_handles_pid_wraparound_and_rejects_pid_reuse() {
        let proc_dir = std::env::temp_dir().join(format!(
            "anneal-itree-proc-test-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        fs::create_dir_all(&proc_dir).unwrap();

        let write_proc = |pid: u32, comm: &str, state: char, ppid: u32, st: u64, pages: u64| {
            let d = proc_dir.join(pid.to_string());
            fs::create_dir_all(&d).unwrap();
            // 19 fields after `)`: state(0), ppid(1), pgrp..itrealvalue(17 fields), starttime(19).
            let zeros = vec!["0"; 17].join(" ");
            let stat = format!("{pid} ({comm}) {state} {ppid} {zeros} {st} 0 0\n");
            fs::write(d.join("stat"), stat).unwrap();
            fs::write(d.join("statm"), format!("1000 {pages} 0 0 0 0 0\n")).unwrap();
        };

        // Root PID 30000 (100 pages = 400 KiB), child PID 32700 (starttime 200, 250 pages = 1000 KiB),
        // grandchild PID 105 (wrapped around pid_max, starttime 300, 500 pages = 2000 KiB).
        write_proc(30000, "lake (env)", 'S', 1, 100, 100);
        write_proc(32700, "lean worker)", 'R', 30000, 200, 250);
        write_proc(105, "lean (child)", 'R', 32700, 300, 500);

        let mut tree = TrackedProcessTree::with_proc_root(30000, &proc_dir, 4);
        assert_eq!(tree.sample_rss_kib(), 400 + 1000 + 2000);
        // A positively running root has not exited (so `reap_exited_root` must
        // not `try_wait` it).
        assert_eq!(tree.root_proc_zombie_or_running(), Some(false));
        assert!(!tree.root_has_exited());

        // Descendant kill order must put newest grandchild (PID 105, starttime 300)
        // before its parent (PID 32700, starttime 200) despite 105 < 32700.
        assert_eq!(tree.descendant_kill_order(), vec![(105, 300), (32700, 200)]);

        // Now simulate intermediate parent PID 32700 exiting and its PID being
        // immediately reused by an unrelated process (starttime 999, 5000 pages),
        // while grandchild PID 105 is reparented to PID 1.
        write_proc(32700, "unrelated", 'R', 1, 999, 5000);
        write_proc(105, "lean (child)", 'R', 1, 300, 600);

        // `sample_rss_kib` must prune the reused PID 32700 (starttime 999 != 200)
        // while retaining reparented grandchild PID 105 (400 + 2400 = 2800 KiB).
        assert_eq!(tree.sample_rss_kib(), 400 + 2400);
        assert_eq!(tree.descendant_kill_order(), vec![(105, 300)]);

        // Now simulate root PID 30000 becoming an un-reaped zombie ('Z') right
        // after spawning a new worker PID 40000 (ppid = 30000, starttime 400, 300 pages = 1200 KiB).
        write_proc(30000, "lake (env)", 'Z', 1, 100, 0);
        write_proc(40000, "lean late worker", 'R', 30000, 400, 300);
        assert_eq!(tree.sample_rss_kib(), 2400 + 1200);
        assert_eq!(tree.descendant_kill_order(), vec![(40000, 400), (105, 300)]);
        assert!(tree.root_has_exited());
        assert_eq!(tree.root_proc_zombie_or_running(), Some(true));

        // A root whose `/proc` entry vanished after its `starttime` was recorded
        // has exited, but one whose `starttime` was never observable (no
        // `/proc/<pid>`, e.g. a host without procfs) must not be reported as
        // exited, so `terminate_process_tree` still waits out the full `SIGTERM`
        // grace period before `SIGKILL`.
        fs::remove_dir_all(proc_dir.join("30000")).unwrap();
        assert_eq!(tree.root_proc_zombie_or_running(), None);
        assert!(tree.root_has_exited());
        let unobservable = TrackedProcessTree::with_proc_root(31337, &proc_dir, 4);
        assert_eq!(unobservable.root_proc_zombie_or_running(), None);
        assert!(!unobservable.root_has_exited());

        let _ = fs::remove_dir_all(&proc_dir);
    }

    #[cfg(unix)]
    #[test]
    fn watchdog_kills_runaway_process_tree_on_timeout_and_rss_and_cleans_up_children() {
        // 1. Wall-clock timeout test with a child that spawns a background grandchild.
        let pid_file = std::env::temp_dir().join(format!(
            "anneal-itree-watchdog-grandchild-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        let mut cmd = Command::new("sh");
        cmd.arg("-c")
            .arg(format!(
                "sleep 60 & echo $! > {}; wait",
                pid_file.display()
            ));
        let out = run_command_with_watchdog(
            cmd,
            DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB,
            Duration::from_millis(150),
            Duration::from_millis(15),
        )
        .expect("run command under timeout watchdog");
        assert_eq!(
            out.watchdog_killed,
            Some(ItreeLeanFailureKind::WallClockTimeout)
        );
        if let Ok(gc_pid_str) = fs::read_to_string(&pid_file)
            && let Ok(gc_pid) = gc_pid_str.trim().parse::<u32>()
        {
            // Grandchild must be dead (or not running `sleep`).
            let state = proc_state_ppid_starttime_in(Path::new("/proc"), gc_pid);
            assert!(
                state.is_none() || matches!(state, Some(('Z' | 'X', _, _))),
                "grandchild PID {gc_pid} should have been terminated by watchdog, got {state:?}"
            );
        }
        let _ = fs::remove_file(&pid_file);

        // 2. RSS watchdog test: set an artificially tight 1 KiB RSS ceiling so any
        //    live child exceeds it immediately and is killed with `RssWatchdogExceeded`.
        let mut rss_cmd = Command::new("sh");
        rss_cmd.arg("-c").arg("sleep 30");
        let rss_out = run_command_with_watchdog(
            rss_cmd,
            1, // 1 KiB ceiling -> guaranteed immediate RSS watchdog trigger
            Duration::from_secs(30),
            Duration::from_millis(10),
        )
        .expect("run command under RSS watchdog");
        assert_eq!(
            rss_out.watchdog_killed,
            Some(ItreeLeanFailureKind::RssWatchdogExceeded)
        );
        assert!(rss_out.peak_rss_kib > 1);
    }

    #[test]
    fn isolated_lean_stage_bisects_watchdog_failures_and_isolates_irreducible_single_case() {
        let (cases, case_to_fn) = stage_fixture(&[
            ("cand_batch_heavy", 4),
            ("cand_one_poison", 4),
            ("cand_healthy", 2),
        ]);
        // Scenario:
        // - `cand_batch_heavy` fails with `[WATCHDOG:RSS_EXCEEDED]` whenever > 2 of
        //   its cases are evaluated in one module, but succeeds when bisected into
        //   2-case sub-modules! So `cand_batch_heavy` must be 100% recovered.
        // - `cand_one_poison` has one irreducible poison case `case_cand_one_poison_t2`
        //   that always hits `[WATCHDOG:TIMEOUT]`, while `t0`, `t1`, and `t3` succeed
        //   once isolated by bisection.
        let stage = run_isolated_lean_stage(
            "ItreeDiffBatchConfirm",
            &cases,
            6,
            2,
            ident,
            &case_to_fn,
            |_label: &str, chunk: &[String]| {
                let heavy_count = chunk
                    .iter()
                    .filter(|c| case_to_fn[*c] == "cand_batch_heavy")
                    .count();
                if heavy_count > 2 {
                    return Err(
                        "[WATCHDOG:RSS_EXCEEDED] module exceeded RSS limit (9000000 KiB > 8388608 KiB)"
                            .to_string(),
                    );
                }
                if chunk.iter().any(|c| c == "case_cand_one_poison_t2") {
                    return Err(
                        "[WATCHDOG:TIMEOUT] module exceeded wall-clock timeout (180s)"
                            .to_string(),
                    );
                }
                ok_all(chunk)
            },
        );

        // `cand_batch_heavy` (all 4 cases) and `cand_healthy` (all 2 cases) must
        // be completely recovered, plus the 3 healthy cases of `cand_one_poison`.
        assert_eq!(
            stage.failed_fns,
            BTreeSet::from(["cand_one_poison".to_string()]),
            "only cand_one_poison has an unrecovered case; cand_batch_heavy recovered via bisection"
        );
        for t in 0..4 {
            assert!(
                stage
                    .results
                    .contains_key(&format!("case_cand_batch_heavy_t{t}")),
                "cand_batch_heavy case t{t} should be recovered by bisection"
            );
        }
        for t in [0, 1, 3] {
            assert!(
                stage
                    .results
                    .contains_key(&format!("case_cand_one_poison_t{t}")),
                "cand_one_poison healthy sibling case t{t} should be recovered by bisection"
            );
        }
        assert!(
            !stage.results.contains_key("case_cand_one_poison_t2"),
            "irreducible poison case must not be in results"
        );
        assert!(
            stage.errors.iter().any(|e| {
                e.contains("irreducible single case `case_cand_one_poison_t2` of `cand_one_poison`")
                    && e.contains("[WATCHDOG:TIMEOUT]")
            }),
            "expected explicit irreducible single-case diagnostic in {:?}",
            stage.errors
        );
        // The poison case only timed out (unchecked, not refuted), so the
        // pipeline keeps comparing `cand_one_poison` on its 3 healthy siblings.
        assert_eq!(
            stage.inconclusive_cases,
            BTreeSet::from(["case_cand_one_poison_t2".to_string()])
        );
        assert_eq!(
            itree_partially_comparable_fns(&stage, &cases, ident, &case_to_fn, |_| true),
            BTreeMap::from([("cand_one_poison".to_string(), 1)])
        );
    }

    /// `inconclusive_cases` keeps the most specific failure of each unresolved
    /// case: a case that only hit a watchdog in isolation is inconclusive, a
    /// Lean rejection never is, and [`itree_partially_comparable_fns`] keeps a
    /// candidate only when all of its unresolved cases are inconclusive (and
    /// droppable) and at least one of its cases completed.
    #[test]
    fn isolated_lean_stage_tracks_inconclusive_cases_for_partial_comparison() {
        let (cases, case_to_fn) = stage_fixture(&[
            ("cand_timeout_one", 4),
            ("cand_reject_one", 4),
            ("cand_all_timeout", 2),
            ("cand_ok", 2),
        ]);
        let stage = run_isolated_lean_stage(
            "ItreeDiffBatchProbe",
            &cases,
            4,
            1,
            ident,
            &case_to_fn,
            |label: &str, chunk: &[String]| {
                let times_out = |c: &String| {
                    c == "case_cand_timeout_one_t1" || c.starts_with("case_cand_all_timeout")
                };
                if chunk.iter().any(times_out) {
                    return Err(format!(
                        "[WATCHDOG:TIMEOUT] `/tmp/verify/{label}.lean` exceeded wall-clock timeout"
                    ));
                }
                if chunk.iter().any(|c| c == "case_cand_reject_one_t3") {
                    return Err(format!(
                        "`/tmp/verify/{label}.lean` failed:\nstdout:\n\
                         /tmp/verify/{label}.lean:9:4: error: unknown constant \
                         'case_cand_reject_one_t3_rawTrace'\nstderr:\n"
                    ));
                }
                ok_all(chunk)
            },
        );
        assert_eq!(
            stage.failed_fns,
            BTreeSet::from([
                "cand_all_timeout".to_string(),
                "cand_reject_one".to_string(),
                "cand_timeout_one".to_string(),
            ])
        );
        for healthy in [
            "case_cand_timeout_one_t0",
            "case_cand_timeout_one_t2",
            "case_cand_timeout_one_t3",
            "case_cand_reject_one_t0",
            "case_cand_reject_one_t1",
            "case_cand_reject_one_t2",
            "case_cand_ok_t0",
            "case_cand_ok_t1",
        ] {
            assert!(stage.results.contains_key(healthy), "{healthy} must be recovered");
        }
        // The chunk-level timeout first marked every case of the third chunk, but
        // `cand_ok`'s fallback succeeded, and the rejected case's most specific
        // failure (its single-case bisection run) is a Lean rejection.
        assert_eq!(
            stage.inconclusive_cases,
            BTreeSet::from([
                "case_cand_all_timeout_t0".to_string(),
                "case_cand_all_timeout_t1".to_string(),
                "case_cand_timeout_one_t1".to_string(),
            ])
        );
        // Only `cand_timeout_one` stays comparable: `cand_reject_one` has a
        // refuted case and `cand_all_timeout` has nothing left to compare.
        assert_eq!(
            itree_partially_comparable_fns(&stage, &cases, ident, &case_to_fn, |_| true),
            BTreeMap::from([("cand_timeout_one".to_string(), 1)])
        );
        // Stage 2 forbids dropping unconfirmed divergences (`may_drop == false`):
        // the candidate is then dropped whole.
        assert!(
            itree_partially_comparable_fns(&stage, &cases, ident, &case_to_fn, |c| {
                c != "case_cand_timeout_one_t1"
            })
            .is_empty()
        );
    }

    /// Stage 2 replacement selection (large batches confirm a single `ok` trace
    /// per agreeing candidate): only a candidate whose selected cases all failed
    /// inconclusively on Stage 1 `ok` traces gets a replacement, namely its first
    /// unselected `ok` trace; a refuted, divergent, already confirmed, or
    /// exhausted candidate gets none.
    #[test]
    fn confirm_replacements_retry_only_inconclusive_agreeing_selections() {
        let (pool, case_to_fn) = stage_fixture(&[
            ("cand_retry", 3),
            ("cand_skip", 3),
            ("cand_reject", 2),
            ("cand_div", 3),
            ("cand_partial", 3),
            ("cand_alone", 1),
            ("cand_done", 2),
        ]);
        let selected: Vec<String> = [
            "case_cand_retry_t0",
            "case_cand_skip_t0",
            "case_cand_reject_t0",
            "case_cand_div_t0",
            "case_cand_div_t1",
            "case_cand_partial_t0",
            "case_cand_partial_t1",
            "case_cand_alone_t0",
            "case_cand_done_t0",
        ]
        .map(str::to_string)
        .to_vec();
        let divergent: BTreeSet<&str> = BTreeSet::from(["case_cand_skip_t1", "case_cand_div_t1"]);
        let stage = IsolatedLeanStage::<usize> {
            results: BTreeMap::from([
                ("case_cand_partial_t1".to_string(), 1),
                ("case_cand_done_t0".to_string(), 1),
            ]),
            failed_fns: [
                "cand_retry",
                "cand_skip",
                "cand_reject",
                "cand_div",
                "cand_partial",
                "cand_alone",
            ]
            .map(str::to_string)
            .into_iter()
            .collect(),
            inconclusive_cases: [
                "case_cand_retry_t0",
                "case_cand_skip_t0",
                "case_cand_div_t0",
                "case_cand_div_t1",
                "case_cand_partial_t0",
                "case_cand_alone_t0",
            ]
            .map(str::to_string)
            .into_iter()
            .collect(),
            errors: Vec::new(),
        };
        let picked = itree_confirm_replacements(
            &stage,
            &selected,
            &pool,
            ident,
            &case_to_fn,
            |c: &String| !divergent.contains(c.as_str()),
        );
        assert_eq!(picked, vec!["case_cand_retry_t1", "case_cand_skip_t2"]);

        // If `case_cand_retry_t1` also hits a resource limit while
        // `case_cand_skip_t2` succeeds, a second replacement pass selects
        // `case_cand_retry_t2` and stops for `cand_skip`.
        let mut selected2 = selected;
        selected2.extend(picked.into_iter().cloned());
        let mut stage2 = stage;
        stage2.results.insert("case_cand_skip_t2".to_string(), 1);
        stage2
            .inconclusive_cases
            .insert("case_cand_retry_t1".to_string());
        let picked2 = itree_confirm_replacements(
            &stage2,
            &selected2,
            &pool,
            ident,
            &case_to_fn,
            |c: &String| !divergent.contains(c.as_str()),
        );
        assert_eq!(picked2, vec!["case_cand_retry_t2"]);
    }

    /// The trial builder keeps every fixed probe (including the `PanicOnCall(0)`
    /// probe) for identity candidates, drops only evaluator-predicted duplicate
    /// probes for mutated candidates, and fills the freed / dynamic slots with
    /// the evaluator-verified concolic trials (`argPinTerm` negations first),
    /// deterministically.
    #[test]
    fn build_candidate_trial_inputs_keeps_probes_and_fills_slots_with_verified_concolic_trials() {
        let fixed_pairs: [(u32, u32); 8] = crate::mutators_itree::ITREE_CONCOLIC_BASE_INPUTS;
        let mut checked = 0usize;
        for cand in generate_itree_batch(ITREE_SAFE_SEEDS, 12, 0xABCD_1234) {
            if !cand
                .applied_mutators
                .iter()
                .any(|m| m == "CallBoundaryOutliner" || m == "ExtOracleInjector")
            {
                continue;
            }
            let staged =
                stage_itree_candidate_items(&cand.source, "b0_c0__", "kernel_step").expect("stage");
            let trials = build_candidate_trial_inputs(&cand, &staged, None, 12, 0xABCD_1234);
            assert_eq!(trials.len(), 12);
            let again = build_candidate_trial_inputs(&cand, &staged, None, 12, 0xABCD_1234);
            assert!(
                trials.iter().zip(&again).all(|(a, b)| a.magic == b.magic
                    && a.payload_len == b.payload_len
                    && a.schedule == b.schedule),
                "trial synthesis must be deterministic"
            );
            // The injected / outlined call runs first on every input, so the
            // `PanicOnCall(0)` probe is never a predicted duplicate.
            assert!(trials.iter().any(|t| (t.magic, t.payload_len) == (0x414E_4E4C, 2048)
                && t.schedule.global_panic_on_call == Some(0)));

            let ev = ItreeConcreteEvaluator::new(&cand.source, "kernel_step").unwrap();
            let predicted: Vec<ItreeConcreteRun> = trials
                .iter()
                .map(|t| {
                    ev.run_kernel_step(t.magic, t.payload_len, &t.schedule, "b0_c0__")
                        .unwrap()
                })
                .collect();
            let distinct: BTreeSet<&ItreeConcreteRun> = predicted.iter().collect();
            assert_eq!(
                distinct.len(),
                trials.len(),
                "mutated candidates must not waste trials on predicted-duplicate traces"
            );
            // The first concolic trial is an `argPinTerm` negation verified against
            // its base probe: same prefix, same callee, different arguments.
            let dict = MirInputDictionary::from_rust_source(&cand.source).unwrap();
            let concolic = explore_itree_concolic_trials(
                &cand.source,
                "kernel_step",
                "b0_c0__",
                &fixed_pairs,
                &dict,
                12,
                cand.seed_u64 ^ 0xABCD_1234,
            );
            let first = concolic.first().expect("concolic trial");
            assert!(matches!(
                first.phase,
                crate::input_gen::ConcolicTrialPhase::NegateCallArg { .. }
            ));
            assert!(trials.iter().any(|t| t.magic == first.magic
                && t.payload_len == first.payload_len
                && t.schedule == first.schedule));
            let (bm, bp) = fixed_pairs[first.base_index];
            let base = ev
                .run_kernel_step(bm, bp, &EnvSchedule::new(), "b0_c0__")
                .unwrap();
            assert!(first.predicted.shares_prefix_with(&base, first.target_event_pos));
            assert_ne!(
                first.predicted.events[first.target_event_pos],
                base.events[first.target_event_pos]
            );
            checked += 1;
        }
        assert!(checked >= 2);

        // Identity candidates keep all 9 probes verbatim (calibration baseline).
        for cand in generate_itree_identity_batch(ITREE_SAFE_SEEDS) {
            let staged =
                stage_itree_candidate_items(&cand.source, "b0_c0__", "kernel_step").expect("stage");
            let trials = build_candidate_trial_inputs(&cand, &staged, None, 12, 0x1DE4_7171);
            assert_eq!(trials.len(), 12);
            for (i, &(m, p)) in fixed_pairs.iter().enumerate() {
                assert_eq!((trials[i].magic, trials[i].payload_len), (m, p));
                assert_eq!(trials[i].schedule, EnvSchedule::new());
            }
            assert_eq!(
                (trials[8].magic, trials[8].payload_len, trials[8].schedule.global_panic_on_call),
                (0x414E_4E4C, 2048, Some(0))
            );
        }
    }

    #[test]
    fn lean_thread_rss_and_timeout_budgets_honor_env_overrides_and_worker_partitioning() {
        // Caller `LEAN_NUM_THREADS` is the whole command's budget: 8 threads across
        // 4 workers -> at most 2 each; it lowers but never raises the computed value.
        assert_eq!(
            resolve_itree_lean_threads_with_env(None, Some("8"), 64, None, Some(256 * GIB_KIB), 4),
            2
        );
        assert_eq!(
            resolve_itree_lean_threads_with_env(None, Some("64"), 8, None, Some(256 * GIB_KIB), 4),
            2,
            "8 cores / 4 workers"
        );
        assert_eq!(
            resolve_itree_lean_threads_with_env(None, Some("2"), 64, None, Some(256 * GIB_KIB), 4),
            1
        );
        assert_eq!(
            resolve_itree_lean_threads_with_env(Some("12"), Some("2"), 64, None, None, 4),
            12,
            "explicit ANNEAL_ITREE_LEAN_THREADS wins"
        );
        assert_eq!(
            resolve_itree_lean_threads_with_env(
                Some("0"),
                None,
                64,
                Some(4),
                Some(256 * GIB_KIB),
                1
            ),
            4,
            "invalid explicit value falls back to cgroup-capped cores"
        );

        // `-M` stays explicit even when the RSS ceiling is overridden.
        assert_eq!(
            resolve_itree_lean_rss_budget_with_env(Some("4096"), Some("9000000"), None, None, 1),
            (4096, 9_000_000)
        );
        // Explicit RSS override without `-M` still withholds the non-heap reserve.
        let (derived_mb, explicit_rss) =
            resolve_itree_lean_rss_budget_with_env(None, Some("2097152"), None, None, 1);
        let reserve_2g =
            itree_lean_non_heap_reserve_kib(2_097_152, ITREE_LEAN_MAX_THREADS_UNDER_8GIB_RSS, None);
        assert_eq!(explicit_rss, 2_097_152);
        assert_eq!(derived_mb, 1280);
        assert!(derived_mb * 1024 + reserve_2g <= explicit_rss);
        assert!(derived_mb * 1024 < explicit_rss);
        // Explicit `-M` without RSS override adds non-heap headroom above `-M * 1024`.
        let (explicit_mb, padded_rss) =
            resolve_itree_lean_rss_budget_with_env(Some("1024"), None, None, None, 1);
        assert_eq!(explicit_mb, 1024);
        assert_eq!(padded_rss, (1024 + 768) * 1024);
        assert!(explicit_mb * 1024 < padded_rss);

        // Timeouts scale with the module's case count unless set explicitly.
        assert_eq!(resolve_itree_lean_timeout_with_env(None, None, 1), DEFAULT_ITREE_LEAN_TIMEOUT);
        assert_eq!(
            resolve_itree_lean_timeout_with_env(None, None, 64),
            DEFAULT_ITREE_LEAN_TIMEOUT + ITREE_LEAN_TIMEOUT_PER_CASE * 63
        );
        assert_eq!(
            resolve_itree_lean_timeout_with_env(Some("250"), Some("9"), 64),
            Duration::from_millis(250)
        );
        assert_eq!(
            resolve_itree_lean_timeout_with_env(None, Some("9"), 64),
            Duration::from_secs(9)
        );
    }

    #[test]
    fn cgroup_parsing_walks_up_from_missing_container_leaves_and_rejects_escaping_paths() {
        let root = std::env::temp_dir().join(format!(
            "anneal-itree-cg-container-test-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        // cgroup v1 container without a cgroup namespace: `/proc/self/cgroup`
        // names the host path, but the container's own limit sits at the mount root.
        fs::create_dir_all(root.join("memory")).unwrap();
        fs::create_dir_all(root.join("cpu,cpuacct")).unwrap();
        fs::write(
            root.join("memory/memory.limit_in_bytes"),
            format!("{}\n", 6 * GIB_KIB * 1024),
        )
        .unwrap();
        fs::write(
            root.join("memory/memory.stat"),
            format!("total_rss {}\ntotal_shmem 0\n", GIB_KIB * 1024),
        )
        .unwrap();
        fs::write(root.join("cpu,cpuacct/cpu.cfs_quota_us"), "150000\n").unwrap();
        fs::write(root.join("cpu,cpuacct/cpu.cfs_period_us"), "100000\n").unwrap();
        let cg = "9:memory:/docker/0123abcd\n7:cpu,cpuacct:/docker/0123abcd (deleted)\n";
        assert_eq!(
            cgroup_memory_limits_kib(&root, cg),
            (Some(6 * GIB_KIB), Some(5 * GIB_KIB))
        );
        assert_eq!(cgroup_cpu_quota_cores(&root, cg), Some(2));
        // A `..` path can never walk out of the mount.
        fs::write(root.join("cpu.max"), "100000 100000\n").unwrap();
        assert_eq!(
            cgroup_cpu_quota_cores(&root.join("cpu,cpuacct"), "0::/../../x\n"),
            None
        );
        assert_eq!(sanitize_cgroup_rel("/a/b (deleted)"), Some("a/b"));
        assert_eq!(sanitize_cgroup_rel("/a/../../b"), None);
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn lean_failure_classification_separates_resource_exhaustion_from_rejection() {
        assert_eq!(
            classify_itree_lean_failure("[WATCHDOG:TIMEOUT] x exceeded wall-clock timeout"),
            ItreeLeanFailureKind::WallClockTimeout
        );
        assert_eq!(
            classify_itree_lean_failure("error: (kernel) excessive memory consumption detected"),
            ItreeLeanFailureKind::LeanMemoryExhausted
        );
        assert_eq!(
            classify_itree_lean_failure("[LEAN:RESOURCE_EXHAUSTED] terminated by a signal"),
            ItreeLeanFailureKind::LeanMemoryExhausted
        );
        assert_eq!(
            classify_itree_lean_failure("error: (deterministic) timeout at `whnf`"),
            ItreeLeanFailureKind::ElaborationOrOutputFailure
        );
        assert!(itree_lean_failure_is_inconclusive(
            "error: (deterministic) timeout at `whnf`, maximum number of heartbeats"
        ));
        assert!(itree_lean_failure_is_inconclusive("[WATCHDOG:RSS_EXCEEDED] exceeded RSS limit"));
        assert!(!itree_lean_failure_is_inconclusive(
            "error: Tactic `rfl` failed: type mismatch"
        ));
    }

    #[cfg(unix)]
    #[test]
    fn watchdog_returns_promptly_when_an_untracked_descendant_holds_the_output_pipe() {
        // The root exits at once while a backgrounded `sleep` (in the root's
        // process group, possibly never sampled by `(pid, starttime)` tracking)
        // keeps stdout open.
        let mut cmd = Command::new("sh");
        cmd.arg("-c").arg("sleep 6 & echo started $!; exit 0");
        let start = Instant::now();
        let out = run_command_with_watchdog(
            cmd,
            DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB,
            Duration::from_secs(30),
            Duration::from_millis(20),
        )
        .expect("run command under watchdog");
        assert!(
            start.elapsed() < Duration::from_secs(5),
            "watchdog must not block on a pipe held by a stray descendant ({:?})",
            start.elapsed()
        );
        assert!(out.exit_success);
        assert_eq!(out.watchdog_killed, None);
        assert!(!out.signal_terminated);
        let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
        assert!(stdout.contains("started"));
        if Path::new("/proc/self/stat").exists() {
            // The exited root is observed as a zombie and its group is killed
            // before reaping, so the stray `sleep` dies and the pipe drains.
            assert!(out.pipes_drained, "group kill must release the held pipe");
            let stray: u32 = stdout
                .split_whitespace()
                .nth(1)
                .and_then(|v| v.parse().ok())
                .expect("stray sleep pid");
            let state = proc_state_ppid_starttime_in(Path::new("/proc"), stray);
            assert!(
                state.is_none() || matches!(state, Some(('Z' | 'X', _, _))),
                "stray group member {stray} must not outlive the run: {state:?}"
            );
        }
        // A short-lived root is reaped well within one capped poll interval.
        let mut quick = Command::new("sh");
        quick.arg("-c").arg("exit 3");
        let start = Instant::now();
        let out = run_command_with_watchdog(
            quick,
            DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB,
            Duration::from_secs(30),
            ITREE_WATCHDOG_POLL_INTERVAL,
        )
        .unwrap();
        assert!(!out.exit_success);
        assert!(out.pipes_drained);
        assert!(start.elapsed() < Duration::from_secs(2));
        // Signal termination outside the watchdog is reported (cgroup OOM kills).
        let mut killed = Command::new("sh");
        killed.arg("-c").arg("kill -9 $$");
        let out = run_command_with_watchdog(
            killed,
            DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB,
            Duration::from_secs(30),
            Duration::from_millis(20),
        )
        .unwrap();
        assert!(!out.exit_success);
        assert!(out.signal_terminated);
        assert_eq!(out.watchdog_killed, None);
    }

    #[test]
    fn isolated_lean_stage_bounds_bisection_of_systematic_and_repeated_watchdog_failures() {
        use std::sync::Mutex;
        // 1. Candidate-wide elaboration failure (e.g. its shared MIR definitions do
        //    not elaborate): chunk + fallback + one pair of halves, then stop.
        let (cases, case_to_fn) = stage_fixture(&[("cand_systematic", 8)]);
        let calls = Mutex::new(Vec::<String>::new());
        let stage = run_isolated_lean_stage(
            "ItreeDiffBatchProbe",
            &cases,
            64,
            1,
            ident,
            &case_to_fn,
            |label: &str, _chunk: &[String]| -> Result<BTreeMap<String, usize>, String> {
                calls.lock().unwrap().push(label.to_string());
                Err("error: unknown identifier 'Mir.ItreeDiffStaged.cand_systematic'".to_string())
            },
        );
        assert_eq!(calls.lock().unwrap().len(), 4, "{:?}", calls.lock().unwrap());
        assert_eq!(stage.failed_fns, BTreeSet::from(["cand_systematic".to_string()]));
        assert!(stage.errors.iter().any(|e| e.contains("candidate-wide")));

        // 1b. The same failure as real `run_itree_lean_module_with_workers` output:
        //     each half's error names its own module path / label and peak RSS, so
        //     only the normalized Lean `error:` messages coincide.
        let (cases, case_to_fn) = stage_fixture(&[("cand_systematic_real", 8)]);
        let calls = Mutex::new(0usize);
        let stage = run_isolated_lean_stage(
            "ItreeDiffBatchProbe",
            &cases,
            64,
            1,
            ident,
            &case_to_fn,
            |label: &str, chunk: &[String]| -> Result<BTreeMap<String, usize>, String> {
                let n = {
                    let mut c = calls.lock().unwrap();
                    *c += 1;
                    *c
                };
                Err(format!(
                    "`/tmp/verify/{label}.lean` failed (peak RSS {} KiB / 8388608 KiB, -M 8192 MiB, \
                     LEAN_NUM_THREADS=2):\nstdout:\n/tmp/verify/{label}.lean:{}:0: error: unknown \
                     constant 'Mir.ItreeDiffStaged.b0_c0__kernel_step.body'\nstderr:\n",
                    100_000 + n * 7,
                    10 + chunk.len()
                ))
            },
        );
        assert_eq!(*calls.lock().unwrap(), 4, "chunk + fallback + one pair of halves");
        assert!(stage.errors.iter().any(|e| e.contains("candidate-wide")));
        assert_eq!(
            lean_error_signature("x.lean:3:1: error: foo\nnoise\ny.lean:9:2: error: foo\n"),
            vec!["foo".to_string()]
        );

        // 2. Every slice times out: failing bisection runs stay within the budget.
        let (cases, case_to_fn) = stage_fixture(&[("cand_slow", 12)]);
        let calls = Mutex::new(0usize);
        let stage = run_isolated_lean_stage(
            "ItreeDiffBatchConfirm",
            &cases,
            16,
            1,
            ident,
            &case_to_fn,
            |_label: &str, _chunk: &[String]| -> Result<BTreeMap<String, usize>, String> {
                *calls.lock().unwrap() += 1;
                Err("[WATCHDOG:TIMEOUT] module exceeded wall-clock timeout".to_string())
            },
        );
        let budget = itree_bisect_failure_budget(12);
        assert_eq!(budget, 10);
        assert_eq!(*calls.lock().unwrap(), 2 + budget, "chunk + fallback + budget");
        assert!(stage.errors.iter().any(|e| e.contains("bisection failure budget")));

        // 3. Lean workers see the wave width inside chunk runs and the whole
        //    budget (`1`) inside sequential fallback / bisection runs.
        let (cases, case_to_fn) = stage_fixture(&[("cand_a", 2), ("cand_b", 2), ("cand_c", 2)]);
        let seen = Mutex::new(BTreeMap::<String, usize>::new());
        let _stage = run_isolated_lean_stage(
            "ItreeDiffBatchProbe",
            &cases,
            2,
            2,
            ident,
            &case_to_fn,
            |label: &str, chunk: &[String]| {
                seen.lock()
                    .unwrap()
                    .insert(label.to_string(), itree_lean_stage_concurrency(99));
                if label.contains("Chunk") && chunk.iter().any(|c| case_to_fn[c] == "cand_a") {
                    return Err("[WATCHDOG:RSS_EXCEEDED] exceeded RSS limit".to_string());
                }
                ok_all(chunk)
            },
        );
        let seen = seen.into_inner().unwrap();
        assert_eq!(seen["ItreeDiffBatchProbeChunk0"], 2);
        assert_eq!(seen["ItreeDiffBatchProbeChunk1"], 2);
        assert_eq!(seen["ItreeDiffBatchProbeChunk2"], 1, "last wave holds one chunk");
        assert_eq!(seen["ItreeDiffBatchProbeFallback_cand_a"], 1);
        assert_eq!(itree_lean_stage_concurrency(99), 99, "guard restores outside a stage");

        // 4. Two case-specific elaboration / missing-result failures in opposite
        //    halves (`t1` in `0..4` and `t6` in `4..8`) must NOT be mistaken for a
        //    candidate-wide failure: bisection isolates both poison cases and
        //    recovers all 6 healthy siblings.
        let (cases, case_to_fn) = stage_fixture(&[("cand_two_poison", 8)]);
        let stage = run_isolated_lean_stage(
            "ItreeDiffBatchProbe",
            &cases,
            64,
            1,
            ident,
            &case_to_fn,
            |_label: &str, chunk: &[String]| {
                let mut map = ok_all(chunk)?;
                map.remove("case_cand_two_poison_t1");
                map.remove("case_cand_two_poison_t6");
                Ok(map)
            },
        );
        for t in [0, 2, 3, 4, 5, 7] {
            assert!(
                stage
                    .results
                    .contains_key(&format!("case_cand_two_poison_t{t}")),
                "healthy sibling t{t} must be recovered even when both halves have a poison case"
            );
        }
        assert!(!stage.results.contains_key("case_cand_two_poison_t1"));
        assert!(!stage.results.contains_key("case_cand_two_poison_t6"));
        assert!(
            !stage.errors.iter().any(|e| e.contains("candidate-wide")),
            "distinct case failures in opposite halves must not trigger candidate-wide stop: {:?}",
            stage.errors
        );

        // 5. Two Stage 2 `tactic 'rfl' failed` failures in opposite halves (`t1`
        //    in `0..4` and `t6` in `4..8`) where Lean's `error:` line does not
        //    include the theorem identifier (`case_...`) and puts the mismatched
        //    terms on indented continuation lines must ALSO bisect and recover all
        //    6 healthy siblings.
        let (cases, case_to_fn) = stage_fixture(&[("cand_two_rfl_poison", 8)]);
        let stage_rfl = run_isolated_lean_stage(
            "ItreeDiffBatchConfirm",
            &cases,
            16,
            1,
            ident,
            &case_to_fn,
            |label: &str, chunk: &[String]| {
                let mut errs = Vec::new();
                if chunk.iter().any(|c| c == "case_cand_two_rfl_poison_t1") {
                    errs.push(format!(
                        "/tmp/verify/{label}.lean:18:42: error: tactic 'rfl' failed, the left-hand side\n  \"branch_tag_mismatch\"\nis not definitionally equal to the right-hand side\n  \"ok\""
                    ));
                }
                if chunk.iter().any(|c| c == "case_cand_two_rfl_poison_t6") {
                    errs.push(format!(
                        "/tmp/verify/{label}.lean:42:42: error: tactic 'rfl' failed, the left-hand side\n  \"branch_tag_mismatch\"\nis not definitionally equal to the right-hand side\n  \"ok\""
                    ));
                }
                if !errs.is_empty() {
                    return Err(format!(
                        "`/tmp/verify/{label}.lean` failed (peak RSS 120000 KiB / 8388608 KiB, -M 8192 MiB, LEAN_NUM_THREADS=2):\nstdout:\n{}\nstderr:\n",
                        errs.join("\n")
                    ));
                }
                ok_all(chunk)
            },
        );
        for t in [0, 2, 3, 4, 5, 7] {
            assert!(
                stage_rfl
                    .results
                    .contains_key(&format!("case_cand_two_rfl_poison_t{t}")),
                "healthy sibling t{t} must be recovered when t1 and t6 fail tactic 'rfl'"
            );
        }
        assert!(!stage_rfl.results.contains_key("case_cand_two_rfl_poison_t1"));
        assert!(!stage_rfl.results.contains_key("case_cand_two_rfl_poison_t6"));
        assert!(!stage_rfl.errors.iter().any(|e| e.contains("candidate-wide")));

        // 6. Cases whose bisection slice was skipped because the failure budget ran
        //    out (`cand_slow` above) or whose per-candidate fallback was skipped by
        //    `ITREE_FALLBACK_CIRCUIT_BREAKER` must NOT be marked in
        //    `inconclusive_cases` (otherwise a candidate split across chunks could
        //    silently drop an un-isolated kernel rejection).
        let (cb_cases, cb_map) = stage_fixture(&[
            ("cand_split", 2),
            ("cand_f0", 1),
            ("cand_f1", 1),
            ("cand_f2", 1),
            ("cand_f3", 1),
            ("cand_split_tail", 1),
        ]);
        // Re-map `case_cand_split_tail_t0` to `cand_split` so `cand_split` spans
        // Chunk 0 (which succeeds) and Chunk 1 (which fails with a watchdog error
        // and hits the circuit breaker before `cand_split` runs its fallback in
        // Chunk 1, because `cand_f0..f3` sort before `cand_split`!).
        let mut cb_case_to_fn = cb_map;
        cb_case_to_fn.insert("case_cand_split_tail_t0".to_string(), "cand_split".to_string());
        let cb_stage = run_isolated_lean_stage(
            "ItreeDiffBatchConfirm",
            &cb_cases,
            2,
            1,
            ident,
            &cb_case_to_fn,
            |label: &str, chunk: &[String]| {
                if label == "ItreeDiffBatchConfirmChunk0" {
                    return ok_all(chunk);
                }
                Err("[WATCHDOG:RSS_EXCEEDED] exceeded RSS limit".to_string())
            },
        );
        assert!(
            !cb_stage.inconclusive_cases.contains("case_cand_split_tail_t0"),
            "fallback skipped by circuit breaker must not mark un-tested case as inconclusive"
        );
        assert!(
            itree_partially_comparable_fns(&cb_stage, &cb_cases, ident, &cb_case_to_fn, |_| true)
                .is_empty(),
            "cand_split must not be partially compared when its Chunk 3 fallback was skipped"
        );
    }

    #[test]
    fn non_heap_reserve_enforces_strict_headroom_invariant_across_budgets_and_edge_cases() {
        const MIB_KIB: u64 = 1024;

        // 1. Canonical budgets (512 MiB, 2 GiB, 4 GiB, 8 GiB, 16 GiB) via explicit RSS
        //    and via host/avail calculation: strict headroom invariant must hold everywhere.
        for rss_kib in [
            512 * MIB_KIB,
            2 * GIB_KIB,
            4 * GIB_KIB,
            8 * GIB_KIB,
            16 * GIB_KIB,
            // Non-MiB-aligned sizes: floor division must never eat into `reserve_kib`.
            512 * MIB_KIB + 777,
            4 * GIB_KIB + 1023,
            8 * GIB_KIB - 1,
            256 * MIB_KIB + 1,
            64 * MIB_KIB + 1,
        ] {
            for threads in [0usize, 1, 2, 4, 8] {
                for olean in [None, Some(0u64), Some(256 * MIB_KIB), Some(2 * GIB_KIB)] {
                    let reserve_kib = itree_lean_non_heap_reserve_kib(rss_kib, threads, olean);
                    let rss_str = rss_kib.to_string();
                    let (lean_mb, resolved_rss) =
                        resolve_itree_lean_rss_budget_with_env_and_reserve(
                            None,
                            Some(&rss_str),
                            None,
                            None,
                            1,
                            threads,
                            olean,
                        );
                    assert_eq!(resolved_rss, rss_kib);
                    assert!(
                        lean_mb.saturating_mul(1024).saturating_add(reserve_kib) <= resolved_rss,
                        "headroom invariant violated for rss={rss_kib}, threads={threads}, \
                         olean={olean:?}: lean_mb={lean_mb}, reserve={reserve_kib}"
                    );
                    assert!(
                        lean_mb.saturating_mul(1024) < resolved_rss,
                        "strict headroom violated for rss={rss_kib}, threads={threads}, \
                         olean={olean:?}: lean_mb={lean_mb}"
                    );
                    if rss_kib >= 4 * GIB_KIB {
                        assert!(
                            reserve_kib >= MIN_ITREE_LARGE_BUDGET_RESERVE_KIB,
                            "budgets >= 4 GiB must reserve >= 1024 MiB (got {reserve_kib})"
                        );
                    }
                    if rss_kib >= 2 * GIB_KIB {
                        assert!(
                            lean_mb >= 512,
                            "budgets >= 2 GiB must keep lean_max_mb >= 512 (got {lean_mb})"
                        );
                    } else if rss_kib >= 512 * MIB_KIB {
                        assert!(
                            lean_mb >= 256,
                            "budgets >= 512 MiB must keep lean_max_mb >= 256 (got {lean_mb})"
                        );
                    }
                }
            }
        }

        // 2. Default 8 GiB budget leaves at least 1024 MiB headroom (`lean_max_mb <= 7168`).
        let (lean_mb_8g, rss_8g) = itree_lean_rss_budget_with_reserve_kib(
            Some(64 * GIB_KIB),
            Some(48 * GIB_KIB),
            1,
            2,
            None,
        );
        assert_eq!(rss_8g, DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB);
        assert_eq!(lean_mb_8g, 7168);
        assert_eq!(
            itree_lean_non_heap_reserve_kib(rss_8g, 2, None),
            MIN_ITREE_LARGE_BUDGET_RESERVE_KIB
        );

        // 3. Large measured `.olean` footprint increases reserve beyond 1024 MiB on 8 GiB,
        //    while extreme/overflow inputs stay panic-free and preserve the 512 MiB heap floor.
        let (lean_mb_big_olean, rss_big_olean) = itree_lean_rss_budget_with_reserve_kib(
            Some(64 * GIB_KIB),
            Some(48 * GIB_KIB),
            1,
            2,
            Some(1536 * MIB_KIB),
        );
        assert_eq!(rss_big_olean, DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB);
        // 1536 MiB olean + 2 * 128 MiB thread arenas = 1792 MiB reserve -> 6400 MiB heap.
        assert_eq!(lean_mb_big_olean, 6400);

        let extreme_reserve =
            itree_lean_non_heap_reserve_kib(8 * GIB_KIB, usize::MAX, Some(u64::MAX));
        assert_eq!(extreme_reserve, 8 * GIB_KIB - 512 * MIB_KIB);
        let (extreme_mb, extreme_rss) = itree_lean_rss_budget_with_reserve_kib(
            Some(u64::MAX),
            Some(u64::MAX),
            0,
            usize::MAX,
            Some(u64::MAX),
        );
        assert_eq!(extreme_rss, DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB);
        assert_eq!(extreme_mb, 512);
        assert_eq!(itree_lean_non_heap_reserve_kib(0, 1, None), 0);
        assert_eq!(itree_lean_non_heap_reserve_kib(64 * MIB_KIB, 1, None), 0);

        // 4. `measure_itree_olean_footprint_kib` sums `.olean`/`.ilean` bytes and skips missing dirs.
        let tmp = env::temp_dir().join(format!(
            "anneal-itree-olean-measure-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        assert_eq!(measure_itree_olean_footprint_kib(&tmp), None);
        let lean_lib = tmp.join(".lake/build/lib/lean/Trusted");
        fs::create_dir_all(&lean_lib).unwrap();
        fs::write(lean_lib.join("A.olean"), vec![0u8; 2049]).unwrap(); // 2049 B
        fs::write(lean_lib.join("A.ilean"), vec![0u8; 1024]).unwrap(); // 1024 B
        fs::write(lean_lib.join("A.olean.server"), vec![0u8; 512]).unwrap(); // 512 B
        fs::write(lean_lib.join("ignored.txt"), vec![0u8; 100_000]).unwrap();
        // Total matching bytes = 3585 -> ceil(3585 / 1024) = 4 KiB.
        assert_eq!(measure_itree_olean_footprint_kib(&tmp), Some(4));
        let _ = fs::remove_dir_all(&tmp);
    }

    #[test]
    fn execution_budget_caps_lean_threads_to_two_under_8gib_unless_overridden() {
        // Default 8 GiB cap on a large 64-core / 128 GiB host caps `LEAN_NUM_THREADS` to 2.
        let (lean_mb, rss_kib, threads) = resolve_itree_lean_execution_budget_with_env(
            None,
            None,
            None,
            Some("12"),
            64,
            None,
            Some(128 * GIB_KIB),
            Some(96 * GIB_KIB),
            1,
            None,
        );
        assert_eq!(rss_kib, DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB);
        assert_eq!(threads, 2);
        assert_eq!(lean_mb, 7168);

        // Explicit `ANNEAL_ITREE_LEAN_THREADS` override still wins even under `<= 8 GiB`,
        // and its higher thread count is reflected in the non-heap reserve.
        let (ov_mb, ov_rss, ov_threads) = resolve_itree_lean_execution_budget_with_env(
            None,
            None,
            Some("6"),
            Some("12"),
            64,
            None,
            Some(128 * GIB_KIB),
            Some(96 * GIB_KIB),
            1,
            None,
        );
        assert_eq!(ov_rss, DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB);
        assert_eq!(ov_threads, 6);
        // 512 MiB olean + 6 * 128 MiB arenas = 1280 MiB reserve -> 6912 MiB heap.
        assert_eq!(ov_mb, 6912);

        // Budgets strictly above 8 GiB (explicit `ANNEAL_ITREE_MAX_RSS_KIB=16 GiB`) allow > 2 threads.
        let rss_16g = (16 * GIB_KIB).to_string();
        let (big_mb, big_rss, big_threads) = resolve_itree_lean_execution_budget_with_env(
            None,
            Some(&rss_16g),
            None,
            Some("4"),
            64,
            None,
            Some(128 * GIB_KIB),
            Some(96 * GIB_KIB),
            1,
            None,
        );
        assert_eq!(big_rss, 16 * GIB_KIB);
        assert_eq!(big_threads, 4);
        assert_eq!(big_mb, 15_360);
    }

    #[test]
    fn adaptive_stage2_confirm_splits_16_case_rss_failure_cleanly_and_fails_closed_on_singleton() {
        use std::sync::Mutex;

        // 1. 16-case chunk fails with `[WATCHDOG:RSS_EXCEEDED]` whenever `slice.len() > 4`,
        //    succeeding once halved to 4-case subchunks: all 16 cases confirmed, distinct
        //    labels used, zero dropped candidates, zero `confirm_stage.errors`.
        let (cases, case_to_fn) = stage_fixture(&[("c0", 4), ("c1", 4), ("c2", 4), ("c3", 4)]);
        assert_eq!(cases.len(), 16);
        let seen_labels = Mutex::new(Vec::<String>::new());
        let stage = run_isolated_adaptive_confirm_stage(
            "ItreeDiffBatchConfirm",
            &cases,
            16,
            1,
            ident,
            &case_to_fn,
            |sub_label: &str, slice: &[String]| {
                seen_labels.lock().unwrap().push(sub_label.to_string());
                if slice.len() > 4 {
                    Err(format!(
                        "[WATCHDOG:RSS_EXCEEDED] `{sub_label}.lean` exceeded RSS limit \
                         (8432128 KiB > 8388608 KiB)"
                    ))
                } else {
                    ok_all(slice)
                }
            },
        );
        assert!(
            stage.errors.is_empty(),
            "adaptive RSS recovery must not pollute confirm_stage.errors: {:?}",
            stage.errors
        );
        assert!(stage.failed_fns.is_empty());
        assert!(stage.inconclusive_cases.is_empty());
        assert_eq!(stage.results.len(), 16);
        for c in &cases {
            assert!(
                stage.results.contains_key(c),
                "missing confirmed case `{c}`"
            );
        }
        let labels = seen_labels.into_inner().unwrap();
        let unique_labels: BTreeSet<&String> = labels.iter().collect();
        assert_eq!(
            unique_labels.len(),
            labels.len(),
            "subchunk labels must never collide: {labels:?}"
        );
        // 16 -> (8, 8) -> (4, 4, 4, 4) = 7 invocations total.
        assert_eq!(
            labels.len(),
            7,
            "expected 1 + 2 + 4 split runs, got {labels:?}"
        );

        // 2. Singleton (`k == 1`) RSS failure must fail closed and surface `Err`.
        let single = vec!["case_poison_t0".to_string()];
        let single_err = run_adaptive_confirm_chunk(
            "ItreeDiffBatchConfirmChunk0",
            &single,
            &ident,
            &|_label, _slice| {
                Err::<BTreeMap<String, ()>, String>(
                    "[WATCHDOG:RSS_EXCEEDED] singleton exceeded RSS limit".to_string(),
                )
            },
        )
        .expect_err("k=1 singleton RSS failure must fail closed");
        assert!(single_err.contains("[WATCHDOG:RSS_EXCEEDED]"));

        // 3. Non-memory failure (e.g. `rfl` kernel rejection) must NOT be swallowed or split
        //    silently; it returns `Err` on the very first attempt so `run_isolated_lean_stage`
        //    isolates/rejects it properly.
        let rej_calls = AtomicUsize::new(0);
        let rej_err = run_adaptive_confirm_chunk(
            "ItreeDiffBatchConfirmChunk0",
            &cases[..4],
            &ident,
            &|_label, _slice| {
                rej_calls.fetch_add(1, Ordering::SeqCst);
                Err::<BTreeMap<String, ()>, String>(
                    "error: Tactic `rfl` failed: type mismatch".to_string(),
                )
            },
        )
        .expect_err("non-memory kernel rejection must fail closed immediately");
        assert!(rej_err.contains("rfl"));
        assert_eq!(rej_calls.load(Ordering::SeqCst), 1);
    }

    /// One recorded `(label, cases)` Lean run of a mock Stage 2 slice runner.
    type MockLeanRuns = std::sync::Mutex<Vec<(String, Vec<String>)>>;

    /// Error text of an RSS watchdog kill of `<label>.lean`, in the format of
    /// `run_itree_lean_module_with_workers`.
    fn mock_rss_exceeded(label: &str) -> String {
        format!(
            "[WATCHDOG:RSS_EXCEEDED] `/tmp/verify/{label}.lean` exceeded RSS limit \
             (8432128 KiB > 8388608 KiB, -M 7168 MiB, LEAN_NUM_THREADS=2):\nstdout:\n\nstderr:\n"
        )
    }

    /// Error text of Lean's own `-M` exhaustion on `<label>.lean`, which the
    /// non-heap reserve makes reachable below the RSS ceiling.
    fn mock_lean_memory_exhausted(label: &str) -> String {
        format!(
            "`/tmp/verify/{label}.lean` failed (peak RSS 7400000 KiB / 8388608 KiB, -M 7168 MiB, \
             LEAN_NUM_THREADS=2):\nstdout:\n/tmp/verify/{label}.lean:12:2: error: (kernel) \
             excessive memory consumption detected at 'whnf' (potential solution: increase \
             memory consumption threshold)\nstderr:\n"
        )
    }

    /// Error text of a kernel rejection of `case`'s `by rfl` theorem in
    /// `<label>.lean`.
    fn mock_rfl_rejection(label: &str, case: &str) -> String {
        format!(
            "`/tmp/verify/{label}.lean` failed (peak RSS 600000 KiB / 8388608 KiB, -M 7168 MiB, \
             LEAN_NUM_THREADS=2):\nstdout:\n/tmp/verify/{label}.lean:9:4: error: Tactic `rfl` \
             failed: The left-hand side\n  {case}_diag\nis not definitionally equal to the \
             right-hand side\n  \"ok\"\nstderr:\n"
        )
    }

    fn assert_labels_unique_file_stems(labels: &[String]) {
        let unique: BTreeSet<&String> = labels.iter().collect();
        assert_eq!(
            unique.len(),
            labels.len(),
            "a `.lean` module label was reused: {labels:?}"
        );
        for label in labels {
            assert!(
                !label.is_empty() && label.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'),
                "`{label}` is not a plain Lean identifier / file stem"
            );
        }
    }

    /// An explicit `ANNEAL_ITREE_LEAN_MAX_MB` without `ANNEAL_ITREE_MAX_RSS_KIB`
    /// pads the RSS ceiling by a per-thread arena estimate, so the ceiling grows
    /// with the thread count. Deciding the `<= 2` thread cap on the *uncapped*
    /// count's ceiling let a wide host exempt itself: 8 threads padded `-M 7168`
    /// to `8704 MiB > 8 GiB`, so the cap never applied, although the same `-M`
    /// fits under `8 GiB` with 2 threads.
    #[test]
    fn execution_budget_thread_cap_cannot_be_evaded_by_a_thread_inflated_explicit_max_mb_ceiling() {
        let total = Some(128 * GIB_KIB);
        let avail = Some(96 * GIB_KIB);
        let resolve = |max_mb: Option<&str>, threads: Option<&str>, olean: Option<u64>| {
            resolve_itree_lean_execution_budget_with_env(
                max_mb,
                None,
                threads,
                Some("12"),
                64,
                None,
                total,
                avail,
                1,
                olean,
            )
        };
        // This host resolves 8 uncapped threads, whose padded ceiling exceeds 8 GiB.
        assert_eq!(
            resolve_itree_lean_threads_with_env(None, Some("12"), 64, None, avail, 1),
            8
        );
        assert_eq!(
            resolve_itree_lean_rss_budget_with_env_and_reserve(
                Some("7168"),
                None,
                total,
                avail,
                1,
                8,
                None
            ),
            (7168, (7168 + 1536) * 1024)
        );
        // The capped pair fits exactly: 7168 MiB heap + 1024 MiB reserve = 8 GiB.
        assert_eq!(resolve(Some("7168"), None, None), (7168, 8 * GIB_KIB, 2));
        assert_eq!(
            resolve(Some("7168"), None, Some(464_258)),
            (7168, 8 * GIB_KIB, 2),
            "the footprint measured on the frozen seed stays below the 1 GiB reserve floor"
        );
        assert_eq!(
            resolve(Some("1024"), None, None),
            (1024, (1024 + 768) * 1024, 2)
        );
        // `-M 8192` cannot fit under 8 GiB even with 2 threads (8192 + 1024 MiB), so
        // the budget is genuinely above 8 GiB and keeps the host's thread count.
        assert_eq!(
            resolve(Some("8192"), None, None),
            (8192, (8192 + 1536) * 1024, 8)
        );
        // An explicit `ANNEAL_ITREE_LEAN_THREADS` still wins and sizes the ceiling.
        assert_eq!(
            resolve(Some("7168"), Some("6"), None),
            (7168, (7168 + 1280) * 1024, 6)
        );
        assert_eq!(
            resolve(Some("7168"), Some("1"), None),
            (7168, 8 * GIB_KIB, 1)
        );
    }

    /// Postconditions of [`resolve_itree_lean_execution_budget_with_env`] over a
    /// grid of env overrides (valid, below-minimum, and capped values), host
    /// shapes, worker counts, and `.olean` footprints.
    #[test]
    fn execution_budget_postconditions_hold_across_env_host_and_footprint_grid() {
        const MIB_KIB: u64 = 1024;
        let parse = |raw: Option<&str>, min: u64| {
            raw.and_then(|v| v.trim().parse::<u64>().ok())
                .filter(|&n| n >= min)
        };
        let mut checked = 0usize;
        let mut capped_from_wider = 0usize;
        let mut uncapped_above_8gib = 0usize;
        for max_mb in [
            None,
            Some("63"),
            Some("64"),
            Some("1024"),
            Some("3071"),
            Some("3072"),
            Some("7168"),
            Some("8192"),
            Some("99999"),
        ] {
            for max_rss in [
                None,
                Some("1023"),
                Some("1024"),
                Some("524288"),
                Some("8388608"),
                Some("8388609"),
                Some("16777216"),
            ] {
                for thr in [None, Some("0"), Some("1"), Some("2"), Some("3"), Some("64")] {
                    for caller in [None, Some("1"), Some("64")] {
                        for host_cores in [1usize, 4, 64] {
                            for avail in [
                                None,
                                Some(2 * GIB_KIB),
                                Some(6 * GIB_KIB),
                                Some(96 * GIB_KIB),
                            ] {
                                let total = avail.map(|a| a.saturating_mul(2));
                                for workers in [0usize, 1, 4] {
                                    for olean in
                                        [None, Some(0u64), Some(464_258), Some(3 * GIB_KIB)]
                                    {
                                        let ctx = || {
                                            format!(
                                                "max_mb={max_mb:?} max_rss={max_rss:?} thr={thr:?} \
                                                 caller={caller:?} host_cores={host_cores} \
                                                 avail={avail:?} workers={workers} olean={olean:?}"
                                            )
                                        };
                                        let budget_for = |threads: usize| {
                                            resolve_itree_lean_rss_budget_with_env_and_reserve(
                                                max_mb, max_rss, total, avail, workers, threads,
                                                olean,
                                            )
                                        };
                                        let (mb, rss, threads) =
                                            resolve_itree_lean_execution_budget_with_env(
                                                max_mb, max_rss, thr, caller, host_cores, None,
                                                total, avail, workers, olean,
                                            );
                                        let raw = resolve_itree_lean_threads_with_env(
                                            thr, caller, host_cores, None, avail, workers,
                                        );
                                        // The triple is self-consistent: `-M` and the ceiling
                                        // are the ones derived for the returned thread count.
                                        assert!((1..=16).contains(&threads), "{}", ctx());
                                        assert_eq!((mb, rss), budget_for(threads), "{}", ctx());
                                        match parse(thr, 1) {
                                            Some(n) => {
                                                assert_eq!(threads as u64, n.min(16), "{}", ctx())
                                            }
                                            None if threads
                                                > ITREE_LEAN_MAX_THREADS_UNDER_8GIB_RSS =>
                                            {
                                                // Uncapped only when even 2 threads cannot fit
                                                // under 8 GiB.
                                                assert_eq!(threads, raw, "{}", ctx());
                                                assert!(
                                                    rss > DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB
                                                        && budget_for(
                                                            ITREE_LEAN_MAX_THREADS_UNDER_8GIB_RSS
                                                        )
                                                        .1 > DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB,
                                                    "{}",
                                                    ctx()
                                                );
                                                uncapped_above_8gib += 1;
                                            }
                                            None => {
                                                assert_eq!(
                                                    threads,
                                                    raw.min(ITREE_LEAN_MAX_THREADS_UNDER_8GIB_RSS),
                                                    "{}",
                                                    ctx()
                                                );
                                                if raw > threads {
                                                    capped_from_wider += 1;
                                                }
                                            }
                                        }
                                        let explicit_mb = parse(max_mb, 64).map(|n| n.min(16_384));
                                        let explicit_rss = parse(max_rss, 1024);
                                        if let Some(n) = explicit_mb {
                                            assert_eq!(mb, n, "{}", ctx());
                                        }
                                        if let Some(n) = explicit_rss {
                                            assert_eq!(rss, n, "{}", ctx());
                                        }
                                        let reserve =
                                            itree_lean_non_heap_reserve_kib(rss, threads, olean);
                                        match (explicit_mb, explicit_rss) {
                                            // Both explicit: honored verbatim, no derived headroom.
                                            (Some(_), Some(_)) => {}
                                            // Explicit `-M` alone: the ceiling is padded above it
                                            // by at least the measured non-heap need.
                                            (Some(_), None) => {
                                                let measured = olean
                                                    .unwrap_or(DEFAULT_ITREE_OLEAN_RESERVE_KIB)
                                                    + ITREE_PER_THREAD_ARENA_KIB * threads as u64;
                                                assert!(rss >= mb * 1024 + measured, "{}", ctx());
                                                assert!(mb * 1024 + reserve <= rss, "{}", ctx());
                                                assert!(mb * 1024 < rss, "{}", ctx());
                                            }
                                            // Derived `-M`: strict headroom above the 64 MiB floor.
                                            (None, explicit_rss) => {
                                                if explicit_rss.is_none() {
                                                    assert!(
                                                        (MIN_ITREE_LEAN_RSS_LIMIT_KIB
                                                            ..=DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB)
                                                            .contains(&rss),
                                                        "{}",
                                                        ctx()
                                                    );
                                                }
                                                if rss > 64 * MIB_KIB {
                                                    assert!(
                                                        mb * 1024 + reserve <= rss,
                                                        "{}",
                                                        ctx()
                                                    );
                                                    assert!(mb * 1024 < rss, "{}", ctx());
                                                }
                                            }
                                        }
                                        checked += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(checked, 9 * 7 * 6 * 3 * 3 * 4 * 3 * 4);
        assert!(
            capped_from_wider > 0 && uncapped_above_8gib > 0,
            "vacuous grid"
        );
    }

    /// The derived `-M` is the exact floor of `(rss_limit - reserve) / 1024` (never
    /// rounded up into the reserve, never more than `1023 KiB` below it), never
    /// decreases as the RSS budget grows, and never increases with more threads
    /// or a larger `.olean` footprint.
    #[test]
    fn derived_lean_max_mb_is_floor_tight_and_monotone_in_budget_threads_and_footprint() {
        const MIB_KIB: u64 = 1024;
        let mut budgets: Vec<u64> = Vec::new();
        for center in [
            64 * MIB_KIB,
            256 * MIB_KIB,
            MIN_ITREE_LEAN_RSS_LIMIT_KIB,
            2 * GIB_KIB,
            4 * GIB_KIB,
            DEFAULT_ITREE_LEAN_RSS_LIMIT_KIB,
            16 * GIB_KIB,
            17 * GIB_KIB,
        ] {
            for delta in 0..=2 {
                budgets.push(center - delta);
                budgets.push(center + delta);
            }
        }
        let mut rss = 64 * MIB_KIB + 1;
        while rss <= 20 * GIB_KIB {
            budgets.push(rss);
            rss += 37_717;
        }
        budgets.sort_unstable();
        budgets.dedup();

        let derive = |rss: u64, threads: usize, olean: Option<u64>| {
            let reserve = itree_lean_non_heap_reserve_kib(rss, threads, olean);
            (itree_lean_max_mb_for_rss_and_reserve(rss, reserve), reserve)
        };
        let thread_counts = [0usize, 1, 2, 4, 16];
        let footprints = [
            Some(0u64),
            Some(1),
            Some(464_258),
            None,
            Some(2 * GIB_KIB),
            Some(u64::MAX),
        ];
        for threads in thread_counts {
            for olean in footprints {
                let mut prev_mb = 0u64;
                for &rss in &budgets {
                    let (mb, reserve) = derive(rss, threads, olean);
                    let ctx = format!(
                        "rss={rss} threads={threads} olean={olean:?} mb={mb} reserve={reserve}"
                    );
                    assert!(reserve <= rss, "{ctx}");
                    assert!((64..=16_384).contains(&mb), "{ctx}");
                    if rss > 64 * MIB_KIB {
                        assert!(mb * 1024 + reserve <= rss, "{ctx}");
                        assert!(mb * 1024 < rss, "{ctx}");
                    }
                    if mb < 16_384 && rss >= 64 * MIB_KIB {
                        assert!(
                            rss - reserve - mb * 1024 < 1024,
                            "floor division wasted a whole MiB: {ctx}"
                        );
                    }
                    if rss >= 4 * GIB_KIB {
                        assert!(reserve >= MIN_ITREE_LARGE_BUDGET_RESERVE_KIB, "{ctx}");
                    }
                    if rss >= 2 * GIB_KIB {
                        assert!(mb >= 512, "{ctx}");
                    } else if rss >= MIN_ITREE_LEAN_RSS_LIMIT_KIB {
                        assert!(mb >= 256, "{ctx}");
                    }
                    assert!(
                        mb >= prev_mb,
                        "a larger RSS budget lowered -M from {prev_mb}: {ctx}"
                    );
                    prev_mb = mb;
                }
            }
        }
        for &rss in &budgets {
            for olean in footprints {
                let mbs: Vec<u64> = thread_counts
                    .iter()
                    .map(|&t| derive(rss, t, olean).0)
                    .collect();
                assert!(
                    mbs.windows(2).all(|w| w[0] >= w[1]),
                    "more threads raised -M at rss={rss} olean={olean:?}: {mbs:?}"
                );
            }
            for threads in thread_counts {
                // `footprints` is sorted by effective size (`None` is the 512 MiB default).
                let mbs: Vec<u64> = footprints
                    .iter()
                    .map(|&o| derive(rss, threads, o).0)
                    .collect();
                assert!(
                    mbs.windows(2).all(|w| w[0] >= w[1]),
                    "a larger footprint raised -M at rss={rss} threads={threads}: {mbs:?}"
                );
            }
        }
    }

    /// Lake may restore an artifact as a link into a shared cache: a symlinked
    /// `.olean` *file* is mapped like a regular one and must count, while a
    /// symlinked *directory* must never be traversed (cycles, foreign trees).
    #[cfg(unix)]
    #[test]
    fn olean_footprint_follows_symlinked_artifacts_but_never_symlinked_directories() {
        use std::os::unix::fs::symlink;

        let tmp = env::temp_dir().join(format!(
            "anneal-itree-olean-symlink-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        let lib = tmp.join(".lake/build/lib/lean");
        let cache = tmp.join("cache");
        let foreign = tmp.join("foreign");
        fs::create_dir_all(lib.join("Anneal")).unwrap();
        fs::create_dir_all(&cache).unwrap();
        fs::create_dir_all(&foreign).unwrap();
        fs::write(cache.join("blob.art"), vec![0u8; 4096]).unwrap();
        fs::write(foreign.join("X.olean"), vec![0u8; 1 << 20]).unwrap();
        fs::write(lib.join("Anneal/B.olean"), vec![0u8; 1024]).unwrap();
        // A link into the cache counts with its target's size.
        symlink(cache.join("blob.art"), lib.join("Anneal/A.olean")).unwrap();
        // A dangling link, a directory link named like an artifact, a link to a
        // foreign tree, and a cycle back to the root contribute nothing.
        symlink(tmp.join("missing.art"), lib.join("Anneal/C.olean")).unwrap();
        symlink(&foreign, lib.join("Anneal/D.olean")).unwrap();
        symlink(&foreign, lib.join("Foreign")).unwrap();
        symlink(&lib, lib.join("Anneal/cycle")).unwrap();
        assert_eq!(measure_itree_olean_footprint_kib(&tmp), Some(5));
        let _ = fs::remove_dir_all(&tmp);
    }

    /// All candidates of a run are staged in one build tree, but a worker maps
    /// only the staged `Mir.*` modules of its own chunk. Charging every worker
    /// for the whole tree makes the reserve grow with the campaign (a few MiB
    /// per candidate) and lowers `-M` for memory no worker maps.
    #[test]
    fn worker_olean_footprint_charges_shared_libraries_plus_one_chunk_of_staged_modules() {
        const MIB: u64 = 1024 * 1024;

        // 1. The on-disk split: only the top-level staged library is "staged".
        let tmp = env::temp_dir().join(format!(
            "anneal-itree-olean-split-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        assert_eq!(measure_itree_olean_footprint(&tmp), None);
        let lib = tmp.join(".lake/build/lib/lean");
        for dir in [
            "Anneal/Rustc",
            "Anneal/Mir",
            "Trusted",
            "Mir/ItreeDiffStaged",
        ] {
            fs::create_dir_all(lib.join(dir)).unwrap();
        }
        assert_eq!(
            measure_itree_olean_footprint(&tmp),
            None,
            "a tree without artifacts falls back to the default reserve"
        );
        for (file, len) in [
            ("Anneal.olean", 1000usize),
            ("Anneal/Rustc/TraceCheck.olean", 3000),
            // A nested directory that merely shares the staged library's name.
            ("Anneal/Mir/NotStaged.olean", 500),
            ("Trusted/T.ilean", 596),
            ("Mir/ItreeDiffStaged/b0_c0__f.olean", 2048),
            ("Mir/ItreeDiffStaged/b0_c1__f.olean", 2048),
            ("Mir/ItreeDiffStaged/b0_c1__f.trace", 9999),
        ] {
            fs::write(lib.join(file), vec![0u8; len]).unwrap();
        }
        let footprint = measure_itree_olean_footprint(&tmp).expect("artifacts were written");
        let _ = fs::remove_dir_all(&tmp);
        assert_eq!(
            footprint,
            ItreeOleanFootprint {
                shared_bytes: 5096,
                staged_bytes: 4096
            }
        );
        // 9192 B round up once, not per part.
        assert_eq!(footprint.total_kib(), 9);
        // A chunk that covers both candidates maps the whole tree; one that covers
        // one of them maps the shared 5096 B plus half of the staged 4096 B.
        assert_eq!(footprint.worker_kib(2, 64), 9);
        assert_eq!(footprint.worker_kib(2, 1), 7);

        // 2. Campaign scale, with the sizes of the frozen-seed run (about 438 MiB
        //    shared, 28 MiB staged per 16 candidates): 800 candidates stage 1400 MiB.
        let smoke = ItreeOleanFootprint {
            shared_bytes: 438 * MIB,
            staged_bytes: 28 * MIB,
        };
        assert_eq!(smoke.worker_kib(16, 64), smoke.total_kib());
        let campaign = ItreeOleanFootprint {
            shared_bytes: 438 * MIB,
            staged_bytes: 50 * 28 * MIB,
        };
        assert_eq!(campaign.total_kib(), (438 + 1400) * 1024);
        assert_eq!(campaign.worker_kib(800, 64), (438 + 112) * 1024);
        // Under the default 8 GiB ceiling the whole tree would cost 1070 MiB of
        // `-M` (reserve 1838 + 256 MiB); one chunk's share stays under the 1 GiB
        // reserve floor.
        let default_mb = |olean_kib: u64| {
            itree_lean_rss_budget_with_reserve_kib(
                Some(64 * GIB_KIB),
                Some(48 * GIB_KIB),
                1,
                2,
                Some(olean_kib),
            )
            .0
        };
        assert_eq!(default_mb(campaign.total_kib()), 6098);
        assert_eq!(default_mb(campaign.worker_kib(800, 64)), 7168);
        // On a 2 GiB per-worker budget the whole tree would pin `-M` to its floor.
        let small_mb = |olean_kib: u64| {
            let reserve = itree_lean_non_heap_reserve_kib(2 * GIB_KIB, 2, Some(olean_kib));
            itree_lean_max_mb_for_rss_and_reserve(2 * GIB_KIB, reserve)
        };
        assert_eq!(small_mb(campaign.total_kib()), 512);
        assert_eq!(
            small_mb(campaign.worker_kib(800, 64)),
            2048 - (438 + 112 + 256)
        );

        // 3. The share is bounded by the shared libraries and the whole tree, never
        //    shrinks as a chunk covers more candidates, and cannot overflow.
        let shared_kib = campaign.shared_bytes.div_ceil(1024);
        for fns in [0usize, 1, 2, 63, 64, 65, 800, usize::MAX] {
            let mut prev = 0u64;
            for chunk_fns in [0usize, 1, 16, 64, 65, usize::MAX] {
                let worker = campaign.worker_kib(fns, chunk_fns);
                assert!(
                    (shared_kib..=campaign.total_kib()).contains(&worker),
                    "fns={fns} chunk_fns={chunk_fns}: {worker}"
                );
                if chunk_fns.max(1) >= fns.max(1) {
                    assert_eq!(
                        worker,
                        campaign.total_kib(),
                        "fns={fns} chunk_fns={chunk_fns}"
                    );
                }
                assert!(worker >= prev, "fns={fns} chunk_fns={chunk_fns}");
                prev = worker;
            }
        }
        let huge = ItreeOleanFootprint {
            shared_bytes: u64::MAX,
            staged_bytes: u64::MAX,
        };
        assert_eq!(huge.total_kib(), u64::MAX.div_ceil(1024));
        assert_eq!(
            huge.worker_kib(usize::MAX, usize::MAX),
            u64::MAX.div_ceil(1024)
        );
        assert_eq!(
            ItreeOleanFootprint {
                shared_bytes: 0,
                staged_bytes: u64::MAX
            }
            .worker_kib(3, 2),
            (u64::MAX / 3 * 2).div_ceil(1024)
        );
    }

    /// A chunk whose adaptive split leaves one irreducible `k == 1` RSS failure
    /// preserves every confirmed subchunk in place instead of throwing them
    /// away into nested `Fallback`/`Bisect` splits: every healthy case stays
    /// confirmed, the poison case is hit only once (`O(log k)` runs total) and
    /// marked inconclusive (unchecked, not refuted), and no `.lean` module
    /// label is ever reused.
    #[test]
    fn adaptive_stage2_split_keeps_every_healthy_case_when_one_singleton_stays_over_rss() {
        let (cases, case_to_fn) = stage_fixture(&[("c0", 4), ("c1", 4), ("c2", 4), ("c3", 4)]);
        let poison = "case_c3_t2";
        let runs = MockLeanRuns::default();
        let stage = run_isolated_adaptive_confirm_stage(
            "ItreeDiffBatchConfirm",
            &cases,
            16,
            1,
            ident,
            &case_to_fn,
            |sub_label: &str, slice: &[String]| {
                runs.lock()
                    .unwrap()
                    .push((sub_label.to_string(), slice.to_vec()));
                if slice.len() > 4 || slice.iter().any(|c| c == poison) {
                    Err(mock_rss_exceeded(sub_label))
                } else {
                    ok_all(slice)
                }
            },
        );
        assert_eq!(stage.results.len(), 15);
        for c in cases.iter().filter(|c| *c != poison) {
            assert!(
                stage.results.contains_key(c),
                "healthy case `{c}` was dropped"
            );
        }
        assert_eq!(stage.failed_fns, BTreeSet::from(["c3".to_string()]));
        assert_eq!(
            stage.inconclusive_cases,
            BTreeSet::from([poison.to_string()])
        );
        assert_eq!(
            itree_partially_comparable_fns(&stage, &cases, ident, &case_to_fn, |_| true),
            BTreeMap::from([("c3".to_string(), 1)])
        );
        assert!(
            stage.errors.iter().any(|e| {
                e.contains("irreducible single case `case_c3_t2` of `c3`")
                    && e.contains("[WATCHDOG:RSS_EXCEEDED]")
            }),
            "expected an explicit single-case diagnostic in {:?}",
            stage.errors
        );

        let runs = runs.into_inner().unwrap();
        let labels: Vec<String> = runs.iter().map(|(l, _)| l.clone()).collect();
        assert_labels_unique_file_stems(&labels);
        // No run that contained the poison case (or more than 4 cases) succeeded,
        // and every healthy case was confirmed by a run without it.
        for c in cases.iter().filter(|c| *c != poison) {
            assert!(
                runs.iter()
                    .any(|(_, s)| s.len() <= 4 && s.contains(c) && !s.iter().any(|x| x == poison)),
                "`{c}` has no successful confirming run"
            );
        }
        // Partial-preserving adaptive Stage 2 cost of one irreducible case:
        // 11 chunk-phase runs total (16, 8+8, 4+4+4+4, 2+2, 1+1), ZERO fallback
        // or bisection re-runs, and the irreducible singleton is hit only ONCE.
        assert_eq!(runs.len(), 11, "unexpected Lean run count: {labels:?}");
        let poison_singleton_hits = runs
            .iter()
            .filter(|(_, s)| s.len() == 1 && s[0] == poison)
            .count();
        assert_eq!(
            poison_singleton_hits, 1,
            "irreducible poison singleton must not be re-killed across Fallback/Bisect: {labels:?}"
        );
        assert_eq!(labels[0], "ItreeDiffBatchConfirmChunk0");
        assert!(labels.contains(&"ItreeDiffBatchConfirmChunk0_split_d4_14_15".to_string()));
        assert!(
            labels
                .iter()
                .all(|l| !l.contains("Fallback") && !l.contains("Bisect")),
            "confirmed subchunks and wave_width==1 leaves must not re-enter Fallback/Bisect: {labels:?}"
        );
    }

    /// A kernel rejection that a memory failure of the enclosing module masks
    /// must surface once the split isolates it: the candidate is refuted (not
    /// inconclusive, never partially compared as agreeing), and its healthy
    /// neighbors are still confirmed without being re-run in Fallback.
    #[test]
    fn adaptive_stage2_split_never_hides_a_kernel_rejection_behind_a_memory_failure() {
        let (cases, case_to_fn) = stage_fixture(&[("c0", 4), ("c1", 4)]);
        let rejected = "case_c1_t1";
        let runs = MockLeanRuns::default();
        let stage = run_isolated_adaptive_confirm_stage(
            "ItreeDiffBatchConfirm",
            &cases,
            8,
            1,
            ident,
            &case_to_fn,
            |sub_label: &str, slice: &[String]| {
                runs.lock()
                    .unwrap()
                    .push((sub_label.to_string(), slice.to_vec()));
                if slice.len() > 2 {
                    // Lean runs out of memory before reaching the rejection.
                    Err(mock_lean_memory_exhausted(sub_label))
                } else if slice.iter().any(|c| c == rejected) {
                    Err(mock_rfl_rejection(sub_label, rejected))
                } else {
                    ok_all(slice)
                }
            },
        );
        assert_eq!(stage.results.len(), 7);
        assert!(!stage.results.contains_key(rejected));
        assert_eq!(stage.failed_fns, BTreeSet::from(["c1".to_string()]));
        assert!(
            stage.inconclusive_cases.is_empty(),
            "a kernel rejection is never inconclusive: {:?}",
            stage.inconclusive_cases
        );
        assert!(
            itree_partially_comparable_fns(&stage, &cases, ident, &case_to_fn, |_| true).is_empty(),
            "a refuted candidate must be dropped whole"
        );
        assert!(
            stage.errors.iter().any(|e| {
                e.contains("irreducible single case `case_c1_t1` of `c1`")
                    && e.contains("Tactic `rfl` failed")
            }),
            "expected the rejection diagnostic in {:?}",
            stage.errors
        );
        let labels: Vec<String> = runs
            .into_inner()
            .unwrap()
            .into_iter()
            .map(|(l, _)| l)
            .collect();
        assert_labels_unique_file_stems(&labels);
        assert!(
            labels.iter().all(|l| !l.contains("Fallback_c0")),
            "already-confirmed neighbor candidate `c0` must not be re-run in Fallback: {labels:?}"
        );
    }

    /// Concurrent chunk workers and the Stage 2 replacement rounds (which reuse
    /// the confirm runner under their own stage labels) never share a `.lean`
    /// module label, even when every chunk of every round splits.
    #[test]
    fn adaptive_stage2_split_labels_stay_disjoint_across_concurrent_chunks_and_replacement_rounds()
    {
        let (cases, case_to_fn) = stage_fixture(&[("c0", 4), ("c1", 4), ("c2", 4), ("c3", 4)]);
        let runs = MockLeanRuns::default();
        for stage_label in [
            "ItreeDiffBatchConfirm",
            "ItreeDiffBatchConfirmReplacement",
            "ItreeDiffBatchConfirmReplacement2",
        ] {
            let stage = run_isolated_adaptive_confirm_stage(
                stage_label,
                &cases,
                8,
                2,
                ident,
                &case_to_fn,
                |sub_label: &str, slice: &[String]| {
                    runs.lock()
                        .unwrap()
                        .push((sub_label.to_string(), slice.to_vec()));
                    if slice.len() > 2 {
                        Err(mock_rss_exceeded(sub_label))
                    } else {
                        ok_all(slice)
                    }
                },
            );
            assert!(stage.errors.is_empty(), "{stage_label}: {:?}", stage.errors);
            assert!(stage.failed_fns.is_empty() && stage.inconclusive_cases.is_empty());
            assert_eq!(stage.results.len(), 16);
        }
        let labels: Vec<String> = runs
            .into_inner()
            .unwrap()
            .into_iter()
            .map(|(l, _)| l)
            .collect();
        // 3 rounds x 2 concurrent chunks x (8, 4+4, 2+2+2+2).
        assert_eq!(labels.len(), 3 * 2 * 7);
        assert_labels_unique_file_stems(&labels);
    }

    /// For every chunk size up to [`ITREE_MAX_CONFIRM_CHUNK_SIZE`] and every
    /// module size that fits in memory, the successful sub-slices partition the
    /// chunk in order: no case is skipped, repeated, or reordered, whichever of
    /// the two memory failure kinds (RSS watchdog, Lean `-M`) triggers a split.
    #[test]
    fn adaptive_stage2_split_partitions_every_chunk_size_in_order_without_gaps_or_repeats() {
        for k in 1..=ITREE_MAX_CONFIRM_CHUNK_SIZE {
            let cases: Vec<String> = (0..k).map(|i| format!("case_f_t{i}")).collect();
            for max_ok in [1usize, 2, 3, 5, 8, ITREE_MAX_CONFIRM_CHUNK_SIZE] {
                let runs = MockLeanRuns::default();
                let res = run_adaptive_confirm_chunk(
                    "Base",
                    &cases,
                    &ident,
                    &|label: &str, slice: &[String]| {
                        let mut runs = runs.lock().unwrap();
                        let attempt = runs.len();
                        runs.push((label.to_string(), slice.to_vec()));
                        if slice.len() <= max_ok {
                            ok_all(slice)
                        } else if attempt % 2 == 0 {
                            Err(mock_rss_exceeded(label))
                        } else {
                            Err(mock_lean_memory_exhausted(label))
                        }
                    },
                )
                .unwrap_or_else(|e| panic!("k={k} max_ok={max_ok} must recover: {e}"));
                let runs = runs.into_inner().unwrap();
                assert_eq!(
                    res.keys().cloned().collect::<BTreeSet<String>>(),
                    cases.iter().cloned().collect::<BTreeSet<String>>(),
                    "k={k} max_ok={max_ok}"
                );
                let confirmed: Vec<String> = runs
                    .iter()
                    .filter(|(_, s)| s.len() <= max_ok)
                    .flat_map(|(_, s)| s.iter().cloned())
                    .collect();
                assert_eq!(confirmed, cases, "k={k} max_ok={max_ok}");
                for (label, slice) in &runs {
                    assert!(!slice.is_empty(), "empty module `{label}` (k={k})");
                }
                // Every failing run halves, so at most `k - 1` runs fail before
                // the at most `k` successful leaves.
                assert!(
                    runs.len() < 2 * k,
                    "k={k} max_ok={max_ok}: {} runs",
                    runs.len()
                );
                assert_eq!(runs[0].0, "Base");
                assert_eq!(runs[0].1, cases);
                let labels: Vec<String> = runs.iter().map(|(l, _)| l.clone()).collect();
                assert_labels_unique_file_stems(&labels);
            }
        }
    }

    /// Only memory failures split: a timeout, a missing toolchain, and a kernel
    /// or elaboration rejection are returned verbatim after exactly one run,
    /// while a signal-terminated root (e.g. the cgroup OOM killer) splits. A
    /// sub-slice that reports success without a result for each of its cases
    /// fails the chunk closed.
    #[test]
    fn adaptive_stage2_split_only_splits_memory_failures_and_rejects_incomplete_subchunks() {
        let cases: Vec<String> = (0..4).map(|i| format!("case_f_t{i}")).collect();
        for (err, kind) in [
            (
                "[WATCHDOG:TIMEOUT] `/tmp/verify/Base.lean` exceeded wall-clock timeout \
                 (195s for 4 case(s), peak RSS 900000 KiB / 8388608 KiB, LEAN_NUM_THREADS=2):",
                ItreeLeanFailureKind::WallClockTimeout,
            ),
            (
                "failed to run `lake env lean` on /tmp/verify/Base.lean: No such file or \
                 directory (os error 2)",
                ItreeLeanFailureKind::MissingToolchain,
            ),
            (
                "`/tmp/verify/Base.lean` failed (peak RSS 600000 KiB / 8388608 KiB, -M 7168 MiB, \
                 LEAN_NUM_THREADS=2):\nstdout:\n/tmp/verify/Base.lean:3:2: error: unknown \
                 constant 'case_f_t0_rawTrace'\nstderr:\n",
                ItreeLeanFailureKind::ElaborationOrOutputFailure,
            ),
        ] {
            assert_eq!(classify_itree_lean_failure(err), kind);
            let calls = AtomicUsize::new(0);
            let got = run_adaptive_confirm_chunk(
                "Base",
                &cases,
                &ident,
                &|_label: &str, _slice: &[String]| {
                    calls.fetch_add(1, Ordering::SeqCst);
                    Err::<BTreeMap<String, usize>, String>(err.to_string())
                },
            )
            .expect_err("a non-memory failure must fail closed");
            assert_eq!(got, err, "{kind:?} must be returned verbatim");
            assert_eq!(calls.load(Ordering::SeqCst), 1, "{kind:?} must not split");
        }

        // A root killed by a signal is a memory-kind failure: halves are retried.
        let signal_runs = MockLeanRuns::default();
        let recovered =
            run_adaptive_confirm_chunk("Base", &cases, &ident, &|label: &str, slice: &[String]| {
                signal_runs
                    .lock()
                    .unwrap()
                    .push((label.to_string(), slice.to_vec()));
                if slice.len() > 2 {
                    Err(format!(
                        "[LEAN:RESOURCE_EXHAUSTED] terminated by a signal (e.g. the cgroup OOM \
                         killer) `/tmp/verify/{label}.lean` failed (peak RSS 5900000 KiB / \
                         8388608 KiB, -M 7168 MiB, LEAN_NUM_THREADS=2):\nstdout:\n\nstderr:\n"
                    ))
                } else {
                    ok_all(slice)
                }
            })
            .expect("halves of a signal-killed module must be retried");
        assert_eq!(recovered.len(), 4);
        assert_eq!(signal_runs.into_inner().unwrap().len(), 3);

        // A sub-slice "succeeding" without `case_f_t3` must not complete the chunk.
        let incomplete =
            run_adaptive_confirm_chunk("Base", &cases, &ident, &|label: &str, slice: &[String]| {
                if slice.len() > 2 {
                    return Err(mock_rss_exceeded(label));
                }
                let mut map = ok_all(slice)?;
                map.remove("case_f_t3");
                Ok(map)
            })
            .expect_err("an incomplete sub-slice must fail the chunk closed");
        assert!(
            incomplete.contains("Base_split_d1_2_4")
                && incomplete.contains("produced no result for `case_f_t3`"),
            "{incomplete}"
        );
        // ... and neither may the unsplit chunk itself, or an empty result.
        let unsplit = run_adaptive_confirm_chunk(
            "Base",
            &cases,
            &ident,
            &|_label: &str, _slice: &[String]| Ok(BTreeMap::<String, usize>::new()),
        )
        .expect_err("an empty result must fail closed");
        assert!(
            unsplit.contains("produced no result for `case_f_t0`"),
            "{unsplit}"
        );

        // No cases, no Lean run.
        let calls = AtomicUsize::new(0);
        let empty = run_adaptive_confirm_chunk(
            "Base",
            &[] as &[String],
            &ident,
            &|_label: &str, slice: &[String]| {
                calls.fetch_add(1, Ordering::SeqCst);
                ok_all(slice)
            },
        )
        .expect("an empty chunk is trivially confirmed");
        assert!(empty.is_empty());
        assert_eq!(calls.load(Ordering::SeqCst), 0);
    }

    /// Regression pin against `O((log k)^2)` nested adaptive splitting: a
    /// single-candidate 16-case chunk with one irreducible RSS poison trace
    /// completes in 11 runs (1 hit on the poison leaf, zero Fallback/Bisect
    /// re-runs) while preserving all 15 healthy traces.
    #[test]
    fn adaptive_stage2_single_candidate_16_case_poison_uses_o_log_k_runs() {
        let (cases, case_to_fn) = stage_fixture(&[("c0", 16)]);
        let poison = "case_c0_t14";
        let runs = MockLeanRuns::default();
        let stage = run_isolated_adaptive_confirm_stage(
            "ItreeDiffBatchConfirm",
            &cases,
            16,
            1,
            ident,
            &case_to_fn,
            |label: &str, slice: &[String]| {
                runs.lock()
                    .unwrap()
                    .push((label.to_string(), slice.to_vec()));
                if slice.len() > 4 || slice.iter().any(|c| c == poison) {
                    Err(mock_rss_exceeded(label))
                } else {
                    ok_all(slice)
                }
            },
        );
        assert_eq!(stage.results.len(), 15);
        assert!(!stage.results.contains_key(poison));
        assert_eq!(stage.failed_fns, BTreeSet::from(["c0".to_string()]));
        assert_eq!(
            stage.inconclusive_cases,
            BTreeSet::from([poison.to_string()])
        );
        let runs = runs.into_inner().unwrap();
        assert_eq!(runs.len(), 11, "expected O(log k) = 11 runs, got {runs:?}");
        assert_eq!(
            runs.iter()
                .filter(|(_, s)| s.len() == 1 && s[0] == poison)
                .count(),
            1
        );
        let labels: Vec<String> = runs.into_iter().map(|(l, _)| l).collect();
        assert_labels_unique_file_stems(&labels);
    }

    /// When a multi-worker wave (`wave_width > 1`) leaves a memory-failed
    /// `k == 1` singleton under split per-worker memory, Stage 2 retries that
    /// singleton once sequentially at full worker memory (`concurrency == 1`)
    /// so transient concurrent-wave RSS pressure recovers completely.
    #[test]
    fn adaptive_stage2_concurrent_wave_retries_memory_failed_singleton_sequentially() {
        let (cases, case_to_fn) = stage_fixture(&[("c0", 4), ("c1", 4)]);
        let heavy = "case_c1_t2";
        let runs = MockLeanRuns::default();
        let stage = run_isolated_adaptive_confirm_stage(
            "ItreeDiffBatchConfirm",
            &cases,
            4,
            2,
            ident,
            &case_to_fn,
            |label: &str, slice: &[String]| {
                let conc = itree_lean_stage_concurrency(2);
                runs.lock()
                    .unwrap()
                    .push((format!("{label}@c{conc}"), slice.to_vec()));
                if conc > 1 && slice.iter().any(|c| c == heavy) {
                    Err(mock_rss_exceeded(label))
                } else {
                    ok_all(slice)
                }
            },
        );
        assert_eq!(stage.results.len(), 8);
        assert!(stage.failed_fns.is_empty());
        assert!(stage.inconclusive_cases.is_empty());
        let runs = runs.into_inner().unwrap();
        assert!(
            runs.iter()
                .any(|(l, s)| l == "ItreeDiffBatchConfirmFallback_c1@c1" && s == &[heavy]),
            "expected sequential full-memory retry of `{heavy}` only: {runs:?}"
        );
        let labels: Vec<String> = runs
            .into_iter()
            .map(|(l, _)| l.split('@').next().unwrap().to_string())
            .collect();
        assert_labels_unique_file_stems(&labels);
    }

    /// Systematic failures trip the adaptive Stage 2 circuit breaker cleanly
    /// without starving unrelated healthy candidates in the same chunk, and a
    /// missing toolchain aborts immediately without Fallback retries.
    #[test]
    fn adaptive_stage2_circuit_breaker_and_missing_toolchain_behave_precisely() {
        // A. Single-candidate 16-case all-poison chunk stops after 4 leaves
        //    (9 runs instead of 31); skipped cases stay non-inconclusive.
        let (c0_cases, c0_map) = stage_fixture(&[("c0", 16)]);
        let runs_a = MockLeanRuns::default();
        let stage_a = run_isolated_adaptive_confirm_stage(
            "ItreeDiffBatchConfirm",
            &c0_cases,
            16,
            1,
            ident,
            &c0_map,
            |label: &str, slice: &[String]| {
                runs_a
                    .lock()
                    .unwrap()
                    .push((label.to_string(), slice.to_vec()));
                Err::<BTreeMap<String, usize>, String>(mock_rss_exceeded(label))
            },
        );
        assert!(stage_a.results.is_empty());
        assert_eq!(stage_a.failed_fns, BTreeSet::from(["c0".to_string()]));
        assert_eq!(runs_a.into_inner().unwrap().len(), 9);
        assert_eq!(
            stage_a.inconclusive_cases.len(),
            ITREE_FALLBACK_CIRCUIT_BREAKER,
            "only the 4 leaves actually killed by RSS are inconclusive; skipped cases are not"
        );

        // B. One bad candidate (`c0`, 4 failing leaves) in a multi-candidate
        //    chunk must NOT trip the chunk circuit breaker or drop healthy
        //    candidates `c1`, `c2`, `c3`.
        let (mix_cases, mix_map) = stage_fixture(&[("c0", 4), ("c1", 4), ("c2", 4), ("c3", 4)]);
        let stage_b = run_isolated_adaptive_confirm_stage(
            "ItreeDiffBatchConfirm",
            &mix_cases,
            16,
            1,
            ident,
            &mix_map,
            |label: &str, slice: &[String]| {
                if slice.iter().any(|c| c.starts_with("case_c0_")) {
                    Err(mock_rss_exceeded(label))
                } else {
                    ok_all(slice)
                }
            },
        );
        assert_eq!(stage_b.results.len(), 12);
        assert_eq!(stage_b.failed_fns, BTreeSet::from(["c0".to_string()]));

        // C. 16 distinct candidates all failing systematically trip the
        //    whole-chunk breaker after 4 distinct failing candidates (9 runs).
        let spec_c: Vec<(&str, usize)> = vec![
            ("c0", 1),
            ("c1", 1),
            ("c2", 1),
            ("c3", 1),
            ("c4", 1),
            ("c5", 1),
            ("c6", 1),
            ("c7", 1),
            ("c8", 1),
            ("c9", 1),
            ("c10", 1),
            ("c11", 1),
            ("c12", 1),
            ("c13", 1),
            ("c14", 1),
            ("c15", 1),
        ];
        let (c_cases, c_map) = stage_fixture(&spec_c);
        let runs_c = MockLeanRuns::default();
        let stage_c = run_isolated_adaptive_confirm_stage(
            "ItreeDiffBatchConfirm",
            &c_cases,
            16,
            1,
            ident,
            &c_map,
            |label: &str, slice: &[String]| {
                runs_c
                    .lock()
                    .unwrap()
                    .push((label.to_string(), slice.to_vec()));
                Err::<BTreeMap<String, usize>, String>(mock_rss_exceeded(label))
            },
        );
        assert!(stage_c.results.is_empty());
        assert_eq!(stage_c.failed_fns.len(), 16);
        assert_eq!(runs_c.into_inner().unwrap().len(), 9);

        // D. Missing toolchain stops after 1 run, skips Fallback, and marks
        //    every case inconclusive.
        let runs_d = MockLeanRuns::default();
        let stage_d = run_isolated_adaptive_confirm_stage(
            "ItreeDiffBatchConfirm",
            &mix_cases,
            16,
            1,
            ident,
            &mix_map,
            |label: &str, slice: &[String]| {
                runs_d
                    .lock()
                    .unwrap()
                    .push((label.to_string(), slice.to_vec()));
                Err::<BTreeMap<String, usize>, String>(
                    "failed to run `lake env lean`: No such file or directory (os error 2)"
                        .to_string(),
                )
            },
        );
        assert!(stage_d.results.is_empty());
        assert_eq!(runs_d.into_inner().unwrap().len(), 1);
        assert_eq!(stage_d.inconclusive_cases.len(), 16);
    }

    /// `measure_itree_olean_footprint_index` classifies top-level `Mir.*`
    /// artifacts as staged (not shared), indexes exact byte sizes per staged
    /// module (handling skewed candidate sizes accurately without proportional
    /// averaging), auto-includes `Mir.Common`, and falls back conservatively
    /// when a requested module is unindexed.
    #[test]
    fn itree_olean_footprint_index_measures_exact_per_slice_modules_and_top_level_mir() {
        let tmp = env::temp_dir().join(format!(
            "anneal_itree_olean_index_test_{}_{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        let lib = tmp.join(".lake/build/lib/lean");
        fs::create_dir_all(lib.join("Anneal")).unwrap();
        fs::create_dir_all(lib.join("Mir/ItreeDiffStaged")).unwrap();
        // Shared: 100 KiB.
        fs::write(lib.join("Anneal/TraceCheck.olean"), vec![0u8; 100 * 1024]).unwrap();
        // Top-level `Mir.olean` (50 KiB) + `Mir/Common.olean` (30 KiB): both staged.
        fs::write(lib.join("Mir.olean"), vec![0u8; 50 * 1024]).unwrap();
        fs::write(lib.join("Mir/Common.olean"), vec![0u8; 30 * 1024]).unwrap();
        // Skewed staged modules: `small` = 10 KiB (.olean + .ilean), `huge` = 4000 KiB.
        fs::write(
            lib.join("Mir/ItreeDiffStaged/small.olean"),
            vec![0u8; 6 * 1024],
        )
        .unwrap();
        fs::write(
            lib.join("Mir/ItreeDiffStaged/small.ilean"),
            vec![0u8; 4 * 1024],
        )
        .unwrap();
        fs::write(
            lib.join("Mir/ItreeDiffStaged/huge.olean"),
            vec![0u8; 4000 * 1024],
        )
        .unwrap();

        let idx = measure_itree_olean_footprint_index(&tmp).expect("artifacts exist");
        let _ = fs::remove_dir_all(&tmp);

        // Top-level `Mir.olean` must be classified as staged, NOT shared.
        assert_eq!(idx.footprint.shared_bytes, 100 * 1024);
        assert_eq!(idx.footprint.staged_bytes, (50 + 30 + 10 + 4000) * 1024);
        assert_eq!(idx.staged_module_bytes.get("Mir"), Some(&(50 * 1024)));
        assert_eq!(idx.staged_module_bytes.get("Mir.Common"), Some(&(30 * 1024)));
        assert_eq!(
            idx.staged_module_bytes.get("Mir.ItreeDiffStaged.small"),
            Some(&(10 * 1024))
        );
        assert_eq!(
            idx.staged_module_bytes.get("Mir.ItreeDiffStaged.huge"),
            Some(&(4000 * 1024))
        );

        // Small slice gets exact shared (100) + Mir.Common (30) + small (10) = 140 KiB,
        // NOT the proportional average (~2145 KiB).
        assert_eq!(
            idx.worker_kib_for_modules(["Mir.ItreeDiffStaged.small"], 2, 1),
            140
        );
        // Huge slice gets exact shared (100) + Mir.Common (30) + huge (4000) = 4130 KiB,
        // NOT under-reserved at ~2145 KiB.
        assert_eq!(
            idx.worker_kib_for_modules(["Mir.ItreeDiffStaged.huge"], 2, 1),
            4130
        );
        // Deduplicates repeated imports and ignores non-Mir modules.
        assert_eq!(
            idx.worker_kib_for_modules(
                [
                    "Anneal",
                    "Mir.ItreeDiffStaged.small",
                    "Mir.ItreeDiffStaged.small",
                    "Mir.Common",
                ],
                2,
                1,
            ),
            140
        );
        // Unindexed staged module falls back conservatively to max(exact, proportional).
        let unindexed = idx.worker_kib_for_modules(["Mir.ItreeDiffStaged.missing"], 2, 1);
        assert_eq!(unindexed, idx.footprint.worker_kib(2, 1));
        assert!(unindexed > 140);
    }
}
