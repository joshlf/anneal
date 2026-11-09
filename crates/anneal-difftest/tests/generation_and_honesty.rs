// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Integration tests for candidate generation and for the honesty of the
//! harness binaries and the campaign runner.
//!
//! The harness binaries generate and compile candidates but run no oracle:
//! neither Miri, nor Anneal's Lean model, nor the generated programs. These
//! tests check the generation properties that do hold (determinism, mutator
//! coverage, compilability, absence of `unsafe` in ITree candidates) and check
//! that no binary or campaign report claims a comparison it did not perform.

use std::collections::BTreeSet;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use arbitrary::Unstructured;

use anneal_difftest::input_gen::{
    EnvScheduleGenerator, EnvStrategy, FieldLayout, LayoutAwareByteBuilder, LayoutSpec,
    MirInputDictionary, PaddingFillPattern, ScalarLayout,
};
use anneal_difftest::instrument::{
    EnvAction, EnvSchedule, RecordedEvent, RecordedOutcome, TraceRecorder,
};
use anneal_difftest::mutators_itree::{
    annotate_itree_external_callees, contains_unsafe_token, generate_itree_batch,
};
use anneal_difftest::mutators_miri::generate_miri_batch;
use anneal_difftest::shrink::{shrink_bytes, shrink_mutation_chain};

/// The only top-level keys `miri-difftest` may emit. Each is a count or
/// setting the binary computes itself. A figure derived from an oracle would
/// need a new key, so this allowlist fails the tests until such a figure is
/// backed by a real comparison.
const MIRI_JSON_KEYS: &[&str] = &[
    "batch_size",
    "batches",
    "compile_pass_rate_pct",
    "compiled_candidates",
    "elapsed_ms",
    "harness",
    "mutator_applications",
    "oracle_comparison",
    "seed",
    "total_candidates",
];

/// The only top-level keys `itree-difftest` may emit (see [`MIRI_JSON_KEYS`]).
const ITREE_JSON_KEYS: &[&str] = &[
    "batch_size",
    "batches",
    "compile_pass_rate_pct",
    "elapsed_ms",
    "harness",
    "instrumented_compiled",
    "mutator_applications",
    "opt_level_0_and_2_compiled",
    "opt_level_0_compiled",
    "opt_level_2_compiled",
    "oracle_comparison",
    "seed",
    "total_candidates",
    "unsafe_token_violations",
];

/// The mutator names that may appear under `mutator_applications`.
const MUTATOR_NAMES: &[&str] = &[
    "ArithmeticCastMutator",
    "BitValidityTransmuteMutator",
    "BranchLoopWeaver",
    "CallBoundaryOutliner",
    "ExtOracleInjector",
    "LayoutPaddingPerturber",
    "PlaceProjectionWrapper",
    "RawPtrOffsetMutator",
    "TreeBorrowsRetagInterleaver",
];

/// The only keys the runner writes to the ledger. It also preserves keys that
/// are already present and not obsolete, such as labels added by the capsule
/// launcher.
const LEDGER_KEYS: &[&str] = &[
    "last_oracle_comparison",
    "last_profile",
    "last_run_utc",
    "next_itree_seed",
    "next_miri_seed",
    "total_campaigns_run",
    "total_itree_candidates_generated",
    "total_miri_candidates_generated",
];

/// The fixed disclaimer lines that may mention agreement or divergences in a
/// campaign report. They are matched only as whole trimmed lines, so a change
/// to any disclaimer line (such as `## Divergences Detected: 0`) remains in the
/// text that [`assert_report_makes_no_claims`] inspects.
const REPORT_DISCLAIMER_LINES: &[&str] = &[
    "compile them with `rustc`; they do not run Miri, Anneal's Lean model, or",
    "the generated programs. This report therefore contains no agreement",
    "figures and no divergence findings.",
    "## Divergences",
    "No oracle comparison was performed, so this campaign cannot report",
    "divergences. The absence of findings is not evidence that Anneal agrees",
];

fn resolve_rustc_bin() -> String {
    if let Ok(r) = std::env::var("RUSTC")
        && !r.is_empty()
    {
        return r;
    }
    if let Ok(home) = std::env::var("HOME") {
        let candidate = PathBuf::from(home).join(".cargo/bin/rustc");
        if candidate.exists() {
            return candidate.to_string_lossy().into_owned();
        }
    }
    "rustc".to_string()
}

/// Compiles a Rust source string with `rustc --edition=2024 --crate-type=lib`
/// plus extra flags.
fn compile_module_with_rustc(
    label: &str,
    extra_flags: &[&str],
    source: &str,
) -> Result<(), String> {
    let tmp_dir = std::env::temp_dir().join(format!(
        "anneal_difftest_gen_{}_{}",
        std::process::id(),
        label
    ));
    let _ = fs::create_dir_all(&tmp_dir);
    let out_path = tmp_dir.join("libgate.rlib");

    let mut cmd = Command::new(resolve_rustc_bin());
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

struct TempDir(PathBuf);

impl std::ops::Deref for TempDir {
    type Target = Path;

    fn deref(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn unique_temp_dir(label: &str) -> TempDir {
    let dir = std::env::temp_dir().join(format!("anneal_difftest_{label}_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create temp dir");
    TempDir(dir)
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("repository root")
        .to_path_buf()
}

fn write_executable(path: &Path, contents: &str) {
    fs::write(path, contents).expect("write executable");
    let mut perms = fs::metadata(path)
        .expect("executable metadata")
        .permissions();
    std::os::unix::fs::PermissionsExt::set_mode(&mut perms, 0o755);
    fs::set_permissions(path, perms).expect("chmod executable");
}

/// Writes a `remote_sync` stand-in that appends its arguments to `log` and exits
/// with `status`.
fn write_remote_sync_stub(path: &Path, log: &Path, status: i32) {
    write_executable(
        path,
        &format!(
            "#!/bin/sh\necho \"$@\" >> '{}'\nexit {status}\n",
            log.display()
        ),
    );
}

/// Parses a JSON object file with Python's `json` module and returns its
/// top-level fields as `(key, JSON-encoded value)` pairs, plus the
/// `(name, count)` entries of its `mutator_applications` object, if any.
fn json_fields(path: &Path) -> (Vec<(String, String)>, Vec<(String, u64)>) {
    let out = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, sys
data = json.load(open(sys.argv[1]))
assert isinstance(data, dict), "not a JSON object"
for key in sorted(data):
    print("F", key, json.dumps(data[key]), sep="\t")
for key, val in sorted(data.get("mutator_applications", {}).items()):
    assert not isinstance(val, bool) and isinstance(val, int) and val >= 0
    print("M", key, val, sep="\t")
"#,
        )
        .arg(path)
        .output()
        .expect("run python3");
    assert!(
        out.status.success(),
        "{} is not a valid JSON object:\n{}",
        path.display(),
        String::from_utf8_lossy(&out.stderr)
    );
    let mut fields = Vec::new();
    let mut mutators = Vec::new();
    for line in String::from_utf8_lossy(&out.stdout).lines() {
        let parts: Vec<&str> = line.splitn(3, '\t').collect();
        match parts.as_slice() {
            ["F", key, value] => fields.push((key.to_string(), value.to_string())),
            ["M", key, value] => mutators.push((
                key.to_string(),
                value.parse::<u64>().expect("non-negative mutator count"),
            )),
            _ => panic!("unexpected line from JSON helper: {line}"),
        }
    }
    (fields, mutators)
}

fn json_field(fields: &[(String, String)], key: &str) -> String {
    fields
        .iter()
        .find(|(k, _)| k == key)
        .map(|(_, v)| v.clone())
        .unwrap_or_else(|| panic!("missing key `{key}` in {fields:?}"))
}

/// Asserts that a harness JSON file states that no oracle ran, contains only
/// allowlisted keys, and records non-zero mutator applications.
fn assert_harness_json_is_honest(
    harness: &str,
    path: &Path,
    allowed: &[&str],
) -> (Vec<(String, String)>, Vec<(String, u64)>) {
    let (fields, mutators) = json_fields(path);
    assert_eq!(
        json_field(&fields, "oracle_comparison"),
        "\"not_performed\""
    );
    assert_eq!(json_field(&fields, "harness"), format!("\"{harness}\""));
    for (key, _) in &fields {
        assert!(
            allowed.contains(&key.as_str()),
            "`{harness}` emits `{key}`, which is not a figure it computes itself"
        );
    }
    for (name, _) in &mutators {
        assert!(
            MUTATOR_NAMES.contains(&name.as_str()),
            "unknown mutator key `{name}`"
        );
    }
    let total_mutators: u64 = mutators.iter().map(|(_, c)| *c).sum();
    assert!(
        total_mutators > 0,
        "`{harness}` must record the mutators applied to its candidates"
    );
    (fields, mutators)
}

/// Asserts that a harness binary's stdout matches its JSON fields and mutator
/// counts line for line and adds no extra bullets or table rows.
fn assert_binary_stdout_is_honest(
    harness: &str,
    stdout: &str,
    fields: &[(String, String)],
    mutators: &[(String, u64)],
) {
    let seed = json_field(fields, "seed").trim_matches('"').to_string();
    let batches = json_field(fields, "batches");
    let batch_size = json_field(fields, "batch_size");
    let total = json_field(fields, "total_candidates");
    let rate: f64 = json_field(fields, "compile_pass_rate_pct")
        .parse()
        .expect("numeric compile_pass_rate_pct");
    let elapsed: f64 = json_field(fields, "elapsed_ms")
        .parse()
        .expect("numeric elapsed_ms");

    let mut expected_header = vec![format!("# `{harness}` candidate generation report")];
    if harness == "miri-difftest" {
        let compiled = json_field(fields, "compiled_candidates");
        expected_header.extend([
            "- **Oracle comparison**: NOT PERFORMED. This binary does not run Miri, \
             Anneal's Lean model, or the generated programs."
                .to_string(),
            format!(
                "- **Seed**: `{seed}` (`{batches}` batches × `{batch_size}` candidates = \
                 `{total}` generated)"
            ),
            format!(
                "- **Compiled with `rustc --edition=2024 --crate-type=lib`**: \
                 `{compiled}/{total}` ({rate:.2}%)"
            ),
            format!("- **Wall-clock time**: `{elapsed:.2} ms`"),
        ]);
    } else {
        let unsafe_cnt = json_field(fields, "unsafe_token_violations");
        let both = json_field(fields, "opt_level_0_and_2_compiled");
        let inst = json_field(fields, "instrumented_compiled");
        expected_header.extend([
            "- **Oracle comparison**: NOT PERFORMED. This binary does not execute the \
             generated programs or their instrumented copies, and does not run \
             Anneal's Lean model."
                .to_string(),
            format!(
                "- **Seed**: `{seed}` (`{batches}` batches × `{batch_size}` candidates = \
                 `{total}` generated)"
            ),
            format!("- **Candidates containing `unsafe`**: `{unsafe_cnt}`"),
            format!(
                "- **Compiled at both `-C opt-level=0` and `-C opt-level=2` (compile only)**: \
                 `{both}/{total}` ({rate:.2}%)"
            ),
            format!("- **Instrumented copies compiled (never executed)**: `{inst}/{total}`"),
            format!("- **Wall-clock time**: `{elapsed:.2} ms`"),
        ]);
    }
    expected_header.extend([
        "| Mutator | Applications |".to_string(),
        "| :--- | ---: |".to_string(),
    ]);

    let non_empty: Vec<&str> = stdout.lines().filter(|l| !l.is_empty()).collect();
    assert!(
        non_empty.len() > expected_header.len(),
        "unexpected `{harness}` stdout:\n{stdout}"
    );
    let actual_header: Vec<String> = non_empty[..expected_header.len()]
        .iter()
        .map(|s| (*s).to_string())
        .collect();
    assert_eq!(
        actual_header, expected_header,
        "`{harness}` stdout header must match its JSON summary:\n{stdout}"
    );
    let expected_rows: Vec<String> = mutators
        .iter()
        .map(|(name, count)| format!("| `{name}` | {count} |"))
        .collect();
    let actual_rows: Vec<String> = non_empty[expected_header.len()..]
        .iter()
        .map(|s| (*s).to_string())
        .collect();
    assert_eq!(
        actual_rows, expected_rows,
        "`{harness}` stdout mutator rows must match JSON `mutator_applications`:\n{stdout}"
    );
}

/// Asserts that a campaign report makes no agreement, divergence, parity,
/// verification, verdict, or percentage claim outside its fixed disclaimer.
fn assert_report_makes_no_claims(report: &str) {
    for line in REPORT_DISCLAIMER_LINES {
        assert!(
            report
                .lines()
                .any(|l| l.trim().trim_start_matches("> ") == *line),
            "report lacks disclaimer line `{line}`:\n{report}"
        );
    }
    let stripped: String = report
        .lines()
        .filter(|l| {
            let clean = l.trim().trim_start_matches("> ");
            !REPORT_DISCLAIMER_LINES.contains(&clean)
        })
        .collect::<Vec<_>>()
        .join("\n");
    let lowered = stripped.to_lowercase();
    for claim in [
        "diverg",
        "agree",
        "parity",
        "verified",
        "%",
        "verdict",
        "strictub",
        "identical",
        "match",
        "lean",
        "symbolic",
        "kernel",
        "ratchet",
    ] {
        assert!(
            !lowered.contains(claim),
            "report must not mention `{claim}`:\n{report}"
        );
    }
}

#[allow(clippy::too_many_arguments)]
fn assert_campaign_report_structure(
    report: &str,
    profile: &str,
    expected_status: &str,
    miri_seed: &str,
    itree_seed: &str,
    miri_gen: &str,
    itree_gen: &str,
    miri_comp: &str,
    itree_comp: &str,
    itree_inst: &str,
    itree_unsafe: &str,
    miri_oracle: &str,
    itree_oracle: &str,
) {
    assert_report_makes_no_claims(report);
    let lines: Vec<&str> = report.lines().collect();
    assert_eq!(
        lines.len(),
        25,
        "campaign report must have 25 lines:\n{report}"
    );
    assert!(
        lines[0].starts_with(&format!(
            "# Anneal Differential Testing Campaign Report (`{profile}` — `"
        )) && lines[0].ends_with("`)"),
        "unexpected title line: {}",
        lines[0]
    );
    let expected_fixed = [
        (1, "".to_string()),
        (
            2,
            format!(
                "> **Status: {expected_status}.** Neither harness compared Anneal with an oracle."
            ),
        ),
        (
            3,
            "> `miri-difftest` and `itree-difftest` generate candidate programs and".to_string(),
        ),
        (
            4,
            "> compile them with `rustc`; they do not run Miri, Anneal's Lean model, or"
                .to_string(),
        ),
        (
            5,
            "> the generated programs. This report therefore contains no agreement".to_string(),
        ),
        (6, "> figures and no divergence findings.".to_string()),
        (7, "".to_string()),
        (
            8,
            "| Metric | `miri-difftest` | `itree-difftest` |".to_string(),
        ),
        (9, "| :--- | :--- | :--- |".to_string()),
        (10, format!("| Seed | `{miri_seed}` | `{itree_seed}` |")),
        (
            11,
            format!("| Candidates generated | {miri_gen} | {itree_gen} |"),
        ),
        (
            12,
            format!("| Compiled with `rustc` | {miri_comp} | {itree_comp} |"),
        ),
        (
            13,
            format!("| Instrumented copies compiled (never executed) | n/a | {itree_inst} |"),
        ),
        (
            14,
            format!("| Candidates containing `unsafe` | n/a | {itree_unsafe} |"),
        ),
        (
            15,
            format!("| Oracle comparison | {miri_oracle} | {itree_oracle} |"),
        ),
        (17, "".to_string()),
        (19, "".to_string()),
        (20, "## Divergences".to_string()),
        (21, "".to_string()),
        (
            22,
            "No oracle comparison was performed, so this campaign cannot report".to_string(),
        ),
        (
            23,
            "divergences. The absence of findings is not evidence that Anneal agrees".to_string(),
        ),
        (24, "with Miri or with native execution.".to_string()),
    ];
    for (idx, expected) in expected_fixed {
        assert_eq!(
            lines[idx],
            expected,
            "report line {} mismatch:\n{report}",
            idx + 1
        );
    }
    assert!(
        lines[16].starts_with("| Harness wall-clock | ") && lines[16].ends_with(" |"),
        "unexpected harness wall-clock row: {}",
        lines[16]
    );
    assert!(
        lines[18].starts_with("Total campaign wall-clock: ") && lines[18].ends_with(" s."),
        "unexpected campaign wall-clock line: {}",
        lines[18]
    );
}

fn collect_relative_files(base: &Path, dir: &Path, out: &mut Vec<String>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_relative_files(base, &path, out);
        } else if let Ok(rel) = path.strip_prefix(base) {
            out.push(rel.to_string_lossy().into_owned());
        }
    }
}

/// Asserts that `state_dir` holds only `state/campaign_ledger.json`,
/// `reports/LATEST_REPORT.md`, and the dated campaign report (no findings
/// bundles or coverage ratchets), and that both report files have identical
/// contents.
fn assert_state_dir_reports_and_files(state_dir: &Path, profile: &str) -> String {
    let mut files = Vec::new();
    collect_relative_files(state_dir, state_dir, &mut files);
    files.sort_unstable();
    assert_eq!(
        files.len(),
        3,
        "state_dir must hold only the two reports and the ledger, got {files:?}"
    );
    let dated_suffix = format!("_{profile}_campaign_report.md");
    assert!(
        files[0].starts_with("reports/") && files[0].ends_with(&dated_suffix),
        "unexpected dated report path: {}",
        files[0]
    );
    assert_eq!(files[1], "reports/LATEST_REPORT.md");
    assert_eq!(files[2], "state/campaign_ledger.json");

    let latest =
        fs::read_to_string(state_dir.join("reports/LATEST_REPORT.md")).expect("read LATEST_REPORT");
    let dated = fs::read_to_string(state_dir.join(&files[0])).expect("read dated campaign report");
    assert_eq!(
        dated, latest,
        "dated report `{}` must equal LATEST_REPORT.md",
        files[0]
    );
    latest
}

fn assert_junit_xml_structure(
    junit_xml: &str,
    profile: &str,
    miri_msg: &str,
    miri_text: &str,
    itree_msg: &str,
    itree_text: &str,
) {
    assert!(
        junit_xml.contains(&format!(
            "<testsuite name=\"anneal_diff_test_{profile}\" tests=\"2\" failures=\"2\" time=\""
        )),
        "JUnit XML testsuite header mismatch:\n{junit_xml}"
    );
    assert_eq!(
        junit_xml.matches("<testcase ").count(),
        2,
        "JUnit XML must contain exactly 2 testcases:\n{junit_xml}"
    );
    assert_eq!(
        junit_xml.matches("<failure ").count(),
        2,
        "JUnit XML must contain exactly 2 failures:\n{junit_xml}"
    );
    for (name, msg, text) in [
        ("miri-difftest", miri_msg, miri_text),
        ("itree-difftest", itree_msg, itree_text),
    ] {
        let snippet = format!(
            "<testcase classname=\"anneal_difftest\" name=\"{name}\">\n      \
             <failure message=\"{msg}\">{text}</failure>\n    </testcase>"
        );
        assert!(
            junit_xml.contains(&snippet),
            "JUnit XML lacks expected `{name}` testcase:\nexpected:\n{snippet}\ngot:\n{junit_xml}"
        );
    }
}

/// Runs the campaign runner in-process so that a test can replace module
/// globals. `REMOTE_SYNC_BIN` always points at the stub given by the caller, so no
/// test can reach real remote. `harness_summary=<json>` makes every harness
/// return that summary instead of running. The remaining arguments are passed
/// to the runner.
const RUNNER_DRIVER: &str = r#"
import importlib.util, json, sys
spec = importlib.util.spec_from_file_location("runner", sys.argv[1])
runner = importlib.util.module_from_spec(spec)
# `dataclass` resolves annotations through `sys.modules[cls.__module__]`.
sys.modules["runner"] = runner
spec.loader.exec_module(runner)
runner.REMOTE_SYNC_BIN = sys.argv[2]
args = sys.argv[3:]
while args and "=" in args[0] and not args[0].startswith("--"):
    key, value = args.pop(0).split("=", 1)
    if key == "harness_summary":
        summary = json.loads(value)
        runner.run_harness = lambda *_args, **_kwargs: dict(summary)
    else:
        raise SystemExit(f"unknown driver override {key}")
sys.argv = ["run_diff_test_campaign.py", *args]
sys.exit(runner.main())
"#;

fn run_campaign_driver(
    remote_sync_stub: &Path,
    env_vars: &[(&str, &Path)],
    overrides: &[String],
    runner_args: &[&str],
    state_dir: &Path,
) -> std::process::Output {
    let root = repo_root();
    let mut cmd = Command::new("python3");
    cmd.arg("-c")
        .arg(RUNNER_DRIVER)
        .arg(root.join("scripts/run_diff_test_campaign.py"))
        .arg(remote_sync_stub)
        .args(overrides)
        .args(runner_args)
        .arg("--state-dir")
        .arg(state_dir)
        .current_dir(&root)
        .env("PYTHONDONTWRITEBYTECODE", "1");
    for (key, value) in env_vars {
        cmd.env(key, value);
    }
    cmd.output().expect("run campaign runner driver")
}

#[test]
fn miri_candidate_generation_is_deterministic_and_compiles() {
    const BASE_SEED: u64 = 0x5EED_0001;
    const NUM_BATCHES: usize = 5;
    const BATCH_SIZE: usize = 32;
    const TOTAL_EXPECTED: usize = NUM_BATCHES * BATCH_SIZE;

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
            "batch {b_idx} must be deterministic for its seed"
        );
        assert_eq!(batch.len(), BATCH_SIZE);
        for cand in &batch {
            for m in &cand.applied_mutators {
                seen_mutators.insert(m.clone());
            }
        }
        all_batches.push(batch);
    }

    for expected_mutator in [
        "ArithmeticCastMutator",
        "PlaceProjectionWrapper",
        "RawPtrOffsetMutator",
        "TreeBorrowsRetagInterleaver",
        "BitValidityTransmuteMutator",
    ] {
        assert!(
            seen_mutators.contains(expected_mutator),
            "generation must exercise `{expected_mutator}`"
        );
    }

    let total_compiled = all_batches
        .iter()
        .enumerate()
        .flat_map(|(b_idx, batch)| {
            batch
                .iter()
                .enumerate()
                .map(move |(c_idx, cand)| (b_idx, c_idx, cand))
        })
        .filter(|(b_idx, c_idx, cand)| {
            compile_module_with_rustc(
                &format!("miri_b{b_idx}_c{c_idx}"),
                &["-A", "warnings"],
                &cand.source,
            )
            .is_ok()
        })
        .count();
    assert!(
        total_compiled * 10 >= TOTAL_EXPECTED * 9,
        "at least 90% of Miri candidates must compile, got {total_compiled}/{TOTAL_EXPECTED}"
    );
}

#[test]
fn itree_candidates_are_safe_and_compile_with_instrumented_copies() {
    const BASE_SEED: u64 = 0x5EED_0002;
    const NUM_BATCHES: usize = 5;
    const BATCH_SIZE: usize = 32;

    let itree_seeds: &[&str] = &[r#"
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
"#];

    let mut seen_mutators = BTreeSet::new();
    let mut combined_forbid_unsafe = String::from("#![forbid(unsafe_code)]\n");
    let mut combined_instrumented =
        String::from("#![feature(register_tool)]\n#![register_tool(anneal_trace)]\n");
    for b_idx in 0..NUM_BATCHES {
        let batch_seed = BASE_SEED.wrapping_add((b_idx as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let batch = generate_itree_batch(itree_seeds, BATCH_SIZE, batch_seed);
        assert_eq!(batch.len(), BATCH_SIZE);
        for (c_idx, cand) in batch.iter().enumerate() {
            assert!(
                !contains_unsafe_token(&cand.source),
                "ITree candidate {c_idx} in batch {b_idx} contains `unsafe`:\n{}",
                cand.source
            );
            for m in &cand.applied_mutators {
                seen_mutators.insert(m.clone());
            }
            combined_forbid_unsafe.push_str(&format!(
                "pub mod b{b_idx}_c{c_idx} {{\n{}\n}}\n",
                cand.source
            ));
            let (inst, _) = annotate_itree_external_callees(&cand.source, "kernel_step")
                .expect("external boundary annotation must succeed on every ITree candidate");
            combined_instrumented
                .push_str(&format!("pub mod inst_b{b_idx}_c{c_idx} {{\n{inst}\n}}\n"));
        }
    }

    for expected_mutator in [
        "CallBoundaryOutliner",
        "LayoutPaddingPerturber",
        "BranchLoopWeaver",
        "ExtOracleInjector",
    ] {
        assert!(
            seen_mutators.contains(expected_mutator),
            "generation must exercise `{expected_mutator}`"
        );
    }

    for (label, flags, source) in [
        (
            "itree_o0",
            &["-D", "warnings", "-C", "opt-level=0"][..],
            &combined_forbid_unsafe,
        ),
        (
            "itree_o2",
            &["-D", "warnings", "-C", "opt-level=2"][..],
            &combined_forbid_unsafe,
        ),
        (
            "itree_inst",
            &["-D", "warnings", "-C", "opt-level=0"][..],
            &combined_instrumented,
        ),
    ] {
        if let Err(stderr) = compile_module_with_rustc(label, flags, source) {
            panic!("`{label}` must compile:\n{stderr}");
        }
    }
}

/// Unit-level checks of the input builder, schedule generator, and shrinkers on
/// edge-case inputs. These exercise library code only; they say nothing about
/// Anneal's semantics.
#[test]
fn input_builder_schedule_and_shrinker_edge_cases() {
    let mut dict = MirInputDictionary::new();
    dict.add_switch_int_literal(0x484F_4C44, 32);

    // Three non-adjacent padding gaps: 1..4, 9..16, and trailing 25..32.
    let multi_gap_layout = LayoutSpec::Struct {
        name: "MultiGapStruct".to_string(),
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
        1, 2, 3, 9, 10, 11, 12, 13, 14, 15, 25, 26, 27, 28, 29, 30, 31,
    ];
    assert_eq!(multi_gap_layout.padding_offsets(), expected_gaps);

    let builder = LayoutAwareByteBuilder::new(&dict)
        .with_dictionary_bias_pct(80)
        .with_validity_fault_rate_pct(0)
        .with_padding_pattern(PaddingFillPattern::PrngNonZero(0x484F_4C44));
    let env_gen = EnvScheduleGenerator::new(&dict)
        .with_horizon_steps(4)
        .with_panic_injection_pct(50);

    for entropy in [&[][..], &[0xFF][..]] {
        let mut u = Unstructured::new(entropy);
        let built = builder.build_bytes(&multi_gap_layout, &mut u);
        assert_eq!(built.len(), 32);
        for &gap in &expected_gaps {
            assert_ne!(
                built[gap], 0,
                "padding byte {gap} must be non-zero for entropy {entropy:?}"
            );
        }
        assert!(
            built[24] <= 1,
            "`bool` field must stay valid for entropy {entropy:?}"
        );
        let _ = TraceRecorder::with_schedule(env_gen.generate_schedule(&["ext"], &mut u));
    }

    let shrink_empty = shrink_bytes(&[], |b| b.is_empty());
    assert!(shrink_empty.succeeded);
    assert_eq!(shrink_empty.minimized_len, 0);
    let shrink_ff = shrink_bytes(&[0xFF], |b| !b.is_empty() && b[0] >= 0x80);
    assert_eq!(shrink_ff.minimized_bytes, vec![0x80]);
    let chain = vec!["m0", "fault", "m1", "m2", "m3"];
    assert_eq!(
        shrink_mutation_chain(&chain, |c| c.contains(&"fault")),
        vec!["fault"]
    );

    // `PanicOnCall(0)` fires on the very first scheduled call.
    let mut sched = EnvSchedule::new().with_panic_on_call(0);
    let mut u_panic = Unstructured::new(&[0xFF]);
    env_gen.apply_strategy(
        &mut sched,
        "oracle",
        &EnvStrategy::PanicOnCall(0),
        &mut u_panic,
    );
    let mut rec = TraceRecorder::with_schedule(sched);
    let (call_idx, action) = rec.step_ext_call("oracle");
    assert_eq!(call_idx, 0);
    assert_eq!(action, EnvAction::PanicOnCall(0));
    assert_eq!(rec.outcome, Some(RecordedOutcome::Panic));
    assert!(rec.events.iter().any(|ev| matches!(
        ev,
        RecordedEvent::ExtCallPanic { def_path, .. } if def_path == "oracle"
    )));
}

#[test]
fn harness_binaries_report_no_oracle_comparison() {
    let dir = unique_temp_dir("binaries");
    for (harness, bin, extra_flags, allowed) in [
        (
            "miri-difftest",
            env!("CARGO_BIN_EXE_miri-difftest"),
            &["--compile-only"][..],
            MIRI_JSON_KEYS,
        ),
        (
            "itree-difftest",
            env!("CARGO_BIN_EXE_itree-difftest"),
            &["--compile-only"][..],
            ITREE_JSON_KEYS,
        ),
    ] {
        let json_path = dir.join(format!("{harness}.json"));
        let out = Command::new(bin)
            .args(extra_flags)
            .args([
                "--batches",
                "1",
                "--batch-size",
                "4",
                "--seed",
                "0x484F4C44",
                "--output-json",
            ])
            .arg(&json_path)
            .output()
            .expect("run harness binary");
        assert!(
            out.status.success(),
            "`{harness}` failed:\n{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let (fields, mutators) = assert_harness_json_is_honest(harness, &json_path, allowed);
        assert_eq!(json_field(&fields, "total_candidates"), "4");

        let stdout = String::from_utf8_lossy(&out.stdout);
        assert_binary_stdout_is_honest(harness, &stdout, &fields, &mutators);

        // Compile-only mode writes no findings, so `--findings-dir` must be rejected.
        let rejected = Command::new(bin)
            .args(extra_flags)
            .args(["--findings-dir"])
            .arg(dir.join("findings"))
            .output()
            .expect("run harness binary");
        assert_eq!(
            rejected.status.code(),
            Some(2),
            "`{harness}` must reject `--findings-dir`"
        );
    }
}

#[test]
fn compile_counts_come_from_rustc() {
    let dir = unique_temp_dir("rustc_wrapper");
    let real_rustc = resolve_rustc_bin();

    // Accepts only combined-crate compilations that include all 6 candidate
    // modules (`b0_c0`..`b1_c2` or `inst_b0_c0`..`inst_b1_c2`), and rejects
    // per-candidate fallback calls, proving that the fast path in each binary
    // compiles every candidate rather than only `c_idx == 0`.
    let require_complete_combined = dir.join("rustc_require_complete_combined.sh");
    write_executable(
        &require_complete_combined,
        &format!(
            "#!/bin/sh\n\
             src=$(cat)\n\
             case \"$*\" in\n\
               *_all_batches/*|*_all_safe_*/*)\n\
                 for m in b0_c0 b0_c1 b0_c2 b1_c0 b1_c1 b1_c2; do\n\
                   case \"$src\" in *\"pub mod $m \"*) ;; *) exit 1 ;; esac\n\
                 done\n\
                 ;;\n\
               *_all_inst_*/*)\n\
                 for m in inst_b0_c0 inst_b0_c1 inst_b0_c2 inst_b1_c0 inst_b1_c1 inst_b1_c2; do\n\
                   case \"$src\" in *\"pub mod $m \"*) ;; *) exit 1 ;; esac\n\
                 done\n\
                 ;;\n\
               *)\n\
                 exit 1\n\
                 ;;\n\
             esac\n\
             printf '%s\\n' \"$src\" | exec '{real_rustc}' \"$@\"\n"
        ),
    );
    let reject_instrumented = dir.join("rustc_reject_instrumented.sh");
    write_executable(
        &reject_instrumented,
        &format!(
            "#!/bin/sh\nsrc=$(cat)\ncase \"$src\" in *anneal_trace::external*) exit 1 ;; esac\n\
             printf '%s\\n' \"$src\" | exec '{real_rustc}' \"$@\"\n"
        ),
    );
    // Rejects all combined compilations to force per-candidate fallback in
    // both binaries, then fails distinct candidates at `-O0` (`b0_c0`), `-O2`
    // (`b0_c1`), and instrumented (`b0_c2`, `b1_c2`) so that `opt_level_0`,
    // `opt_level_2`, `opt_level_0_and_2` (per-candidate conjunction: 4, not
    // `min(5, 5)`), and `instrumented_compiled` (4) are all verified.
    let reject_partial = dir.join("rustc_reject_partial.sh");
    write_executable(
        &reject_partial,
        &format!(
            "#!/bin/sh\ncase \"$*\" in\n\
               *_all_batches/*|*_all_safe_*/*|*_all_inst_*/*|\
               *anneal_miri_difftest_*_b0_c0/*|\
               *anneal_itree_difftest_*_b0_c0_o0/*|\
               *anneal_itree_difftest_*_b0_c1_o2/*|\
               *anneal_itree_difftest_*_b0_c2_inst_o0/*|\
               *anneal_itree_difftest_*_b1_c2_inst_o0/*)\n\
                 cat > /dev/null\n\
                 exit 1\n\
                 ;;\n\
             esac\nexec '{real_rustc}' \"$@\"\n"
        ),
    );
    let reject_o0_safe = dir.join("rustc_reject_o0_safe.sh");
    write_executable(
        &reject_o0_safe,
        &format!(
            "#!/bin/sh\ncase \"$*\" in\n\
             *opt-level=0*)\n\
               case \"$*\" in *_inst_o0/*) ;; *) cat > /dev/null; exit 1 ;; esac\n\
               ;;\n\
             esac\nexec '{real_rustc}' \"$@\"\n"
        ),
    );
    let reject_all = dir.join("rustc_reject_all.sh");
    write_executable(&reject_all, "#!/bin/sh\ncat > /dev/null\nexit 1\n");

    let run = |bin: &str, rustc: &Path, name: &str| -> Vec<(String, String)> {
        let json_path = dir.join(format!("{name}.json"));
        let mut cmd = Command::new(bin);
        cmd.arg("--compile-only");
        let out = cmd
            .args([
                "--batches",
                "2",
                "--batch-size",
                "3",
                "--seed",
                "0x5EED",
                "--output-json",
            ])
            .arg(&json_path)
            .env("RUSTC", rustc)
            .output()
            .expect("run harness binary");
        assert!(
            out.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        json_fields(&json_path).0
    };

    // Fast-path completeness: combined compilations must include all 6
    // candidates in the crate passed to `rustc`.
    let miri_combined = run(
        env!("CARGO_BIN_EXE_miri-difftest"),
        &require_complete_combined,
        "miri_combined",
    );
    assert_eq!(
        json_field(&miri_combined, "compiled_candidates"),
        "6",
        "miri combined compilation must include every candidate"
    );
    let itree_combined = run(
        env!("CARGO_BIN_EXE_itree-difftest"),
        &require_complete_combined,
        "itree_combined",
    );
    assert_eq!(
        json_field(&itree_combined, "opt_level_0_and_2_compiled"),
        "6",
        "itree combined safe compilation must include every candidate"
    );
    assert_eq!(
        json_field(&itree_combined, "instrumented_compiled"),
        "6",
        "itree combined instrumented compilation must include every candidate"
    );

    // Every instrumented copy is compiled on its own: a compiler that rejects
    // only instrumented sources leaves all plain candidates compiled and no
    // instrumented copy compiled.
    let itree = run(
        env!("CARGO_BIN_EXE_itree-difftest"),
        &reject_instrumented,
        "itree_inst",
    );
    assert_eq!(json_field(&itree, "opt_level_0_compiled"), "6");
    assert_eq!(json_field(&itree, "opt_level_2_compiled"), "6");
    assert_eq!(
        json_field(&itree, "opt_level_0_and_2_compiled"),
        "6",
        "plain candidates must compile when only instrumented sources are rejected"
    );
    assert_eq!(json_field(&itree, "compile_pass_rate_pct"), "100.0");
    assert_eq!(
        json_field(&itree, "instrumented_compiled"),
        "0",
        "instrumented copies must actually be compiled"
    );

    // Per-candidate fallback with distinct failures at `-O0` (`b0_c0`), `-O2`
    // (`b0_c1`), and instrumented (`b0_c2`, `b1_c2`), plus `b0_c0` in Miri.
    let itree_partial = run(
        env!("CARGO_BIN_EXE_itree-difftest"),
        &reject_partial,
        "itree_partial",
    );
    assert_eq!(
        json_field(&itree_partial, "opt_level_0_compiled"),
        "5",
        "itree per-candidate -O0 fallback must be exercised"
    );
    assert_eq!(
        json_field(&itree_partial, "opt_level_2_compiled"),
        "5",
        "itree -O2 candidates must actually be compiled"
    );
    assert_eq!(
        json_field(&itree_partial, "opt_level_0_and_2_compiled"),
        "4",
        "opt_level_0_and_2_compiled must be the per-candidate conjunction"
    );
    assert_eq!(json_field(&itree_partial, "compile_pass_rate_pct"), "66.67");
    assert_eq!(
        json_field(&itree_partial, "instrumented_compiled"),
        "4",
        "itree per-candidate instrumented fallback must be exercised"
    );

    let miri_partial = run(
        env!("CARGO_BIN_EXE_miri-difftest"),
        &reject_partial,
        "miri_partial",
    );
    assert_eq!(json_field(&miri_partial, "total_candidates"), "6");
    assert_eq!(
        json_field(&miri_partial, "compiled_candidates"),
        "5",
        "miri candidates must actually be compiled"
    );
    assert_eq!(
        json_field(&miri_partial, "compile_pass_rate_pct"),
        "83.33",
        "miri compile_pass_rate_pct must be computed from compiled_candidates"
    );

    // Rejecting `-C opt-level=0` on plain candidates proves that
    // `opt_level_0_compiled` is measured rather than set to `total_candidates`.
    let itree_no_o0 = run(
        env!("CARGO_BIN_EXE_itree-difftest"),
        &reject_o0_safe,
        "itree_no_o0",
    );
    assert_eq!(
        json_field(&itree_no_o0, "opt_level_0_compiled"),
        "0",
        "itree -O0 candidates must actually be compiled"
    );
    assert_eq!(json_field(&itree_no_o0, "opt_level_2_compiled"), "6");
    assert_eq!(json_field(&itree_no_o0, "opt_level_0_and_2_compiled"), "0");
    assert_eq!(json_field(&itree_no_o0, "compile_pass_rate_pct"), "0.0");
    assert_eq!(json_field(&itree_no_o0, "instrumented_compiled"), "6");

    // A compiler that rejects everything leaves nothing compiled.
    let itree = run(
        env!("CARGO_BIN_EXE_itree-difftest"),
        &reject_all,
        "itree_none",
    );
    assert_eq!(json_field(&itree, "opt_level_0_compiled"), "0");
    assert_eq!(json_field(&itree, "opt_level_2_compiled"), "0");
    assert_eq!(
        json_field(&itree, "opt_level_0_and_2_compiled"),
        "0",
        "itree candidates must actually be compiled"
    );
    assert_eq!(
        json_field(&itree, "instrumented_compiled"),
        "0",
        "instrumented copies must actually be compiled"
    );
    assert_eq!(json_field(&itree, "compile_pass_rate_pct"), "0.0");
    let miri = run(
        env!("CARGO_BIN_EXE_miri-difftest"),
        &reject_all,
        "miri_none",
    );
    assert_eq!(
        json_field(&miri, "compiled_candidates"),
        "0",
        "miri candidates must actually be compiled"
    );
    assert_eq!(json_field(&miri, "compile_pass_rate_pct"), "0.0");
}

#[test]
fn campaign_runner_reports_not_evaluated_and_fails() {
    let dir = unique_temp_dir("campaign");
    let state_dir = dir.join("state-dir");
    let junit = dir.join("diff_test_report.xml");
    let junit_arg = junit.to_string_lossy().into_owned();
    let remote_sync_log = dir.join("remote_sync.log");
    let remote_sync = dir.join("remote_sync_must_not_run.sh");
    write_remote_sync_stub(&remote_sync, &remote_sync_log, 1);

    fs::create_dir_all(state_dir.join("state")).expect("create state dir");
    // A ledger written by an earlier runner version, with distinct starting
    // counts, obsolete evaluation keys, and a capsule-launcher label.
    fs::write(
        state_dir.join("state/campaign_ledger.json"),
        r#"{"next_miri_seed": "0x11", "next_itree_seed": "0x22", "total_campaigns_run": 4,
            "total_miri_candidates_generated": 10, "total_itree_candidates_generated": 20,
            "total_miri_candidates_evaluated": 99, "cumulative_distinct_obs_paths": 7,
            "active_fingerprints": [], "_NONFUNCTIONAL_NOTICE": "label"}"#,
    )
    .expect("write ledger");

    let out = run_campaign_driver(
        &remote_sync,
        &[],
        &[],
        &[
            "--profile",
            "smoke",
            "--compile-only",
            "--remote-uri",
            "",
            "--junit-xml",
            &junit_arg,
        ],
        &state_dir,
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert_eq!(
        out.status.code(),
        Some(3),
        "a campaign without oracle comparison must exit with status 3:\n\
         stdout:\n{stdout}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        !remote_sync_log.exists(),
        "the runner invoked remote_sync without an remote URI"
    );

    let report = assert_state_dir_reports_and_files(&state_dir, "smoke");
    assert_eq!(
        report.trim(),
        stdout.trim(),
        "stdout must match the written report"
    );
    assert_campaign_report_structure(
        &report,
        "smoke",
        "NOT EVALUATED",
        "0x00000011",
        "0x00000022",
        "16",
        "16",
        "16",
        "16 at both `-O0` and `-O2` (compile only)",
        "16",
        "0",
        "**not performed**",
        "**not performed**",
    );

    let junit_xml = fs::read_to_string(&junit).expect("JUnit XML");
    assert_junit_xml_structure(
        &junit_xml,
        "smoke",
        "oracle comparison not performed",
        "miri-difftest generated 16 candidates, 16 of which compiled, but it did not compare \
         Anneal with Miri or with native execution, so this run is not evidence about Anneal.",
        "oracle comparison not performed",
        "itree-difftest generated 16 candidates, 16 of which compiled, but it did not compare \
         Anneal with Miri or with native execution, so this run is not evidence about Anneal.",
    );

    let (ledger, _) = json_fields(&state_dir.join("state/campaign_ledger.json"));
    let keys: Vec<&str> = ledger.iter().map(|(key, _)| key.as_str()).collect();
    let mut expected_keys = LEDGER_KEYS.to_vec();
    expected_keys.push("_NONFUNCTIONAL_NOTICE");
    expected_keys.sort_unstable();
    assert_eq!(keys, expected_keys, "the ledger may hold only known keys");
    assert_eq!(json_field(&ledger, "next_miri_seed"), "\"0x9e3779ca\"");
    assert_eq!(json_field(&ledger, "next_itree_seed"), "\"0x9e3779db\"");
    assert_eq!(json_field(&ledger, "total_campaigns_run"), "5");
    assert_eq!(
        json_field(&ledger, "total_miri_candidates_generated"),
        "26",
        "miri generated counter must add the 16 smoke candidates to 10"
    );
    assert_eq!(
        json_field(&ledger, "total_itree_candidates_generated"),
        "36",
        "itree generated counter must add the 16 smoke candidates to 20"
    );
    assert_eq!(json_field(&ledger, "last_profile"), "\"smoke\"");
    assert_eq!(
        json_field(&ledger, "last_oracle_comparison"),
        "\"not_performed\""
    );

    // Second run with a `cargo` stand-in that emits distinct numbers for every
    // JSON field, so that no table cell, JUnit message, or ledger counter can
    // be wired to the wrong field (such as `total_candidates` in place of
    // `compiled_candidates`).
    let stub_bin = dir.join("stub_bin");
    fs::create_dir_all(&stub_bin).expect("create stub_bin");
    write_executable(
        &stub_bin.join("cargo"),
        r#"#!/bin/sh
out=""
bin=""
while [ $# -gt 0 ]; do
  case "$1" in
    --bin) bin="$2"; shift 2 ;;
    --output-json) out="$2"; shift 2 ;;
    *) shift ;;
  esac
done
if [ "$bin" = "miri-difftest" ]; then
  cat > "$out" <<'JSON'
{"harness":"miri-difftest","oracle_comparison":"not_performed","seed":"0x9e3779ca","batches":2,"batch_size":8,"total_candidates":15,"compiled_candidates":11,"compile_pass_rate_pct":73.33,"elapsed_ms":4.2}
JSON
else
  cat > "$out" <<'JSON'
{"harness":"itree-difftest","oracle_comparison":"not_performed","seed":"0x9e3779db","batches":2,"batch_size":8,"total_candidates":14,"unsafe_token_violations":1,"opt_level_0_compiled":13,"opt_level_2_compiled":12,"opt_level_0_and_2_compiled":9,"instrumented_compiled":7,"compile_pass_rate_pct":64.29,"elapsed_ms":5.3}
JSON
fi
"#,
    );
    let path_env = PathBuf::from(format!(
        "{}:{}",
        stub_bin.display(),
        std::env::var("PATH").unwrap_or_default()
    ));
    let out2 = run_campaign_driver(
        &remote_sync,
        &[("PATH", &path_env)],
        &[],
        &[
            "--profile",
            "smoke",
            "--compile-only",
            "--remote-uri",
            "",
            "--junit-xml",
            &junit_arg,
        ],
        &state_dir,
    );
    assert_eq!(out2.status.code(), Some(3));
    let report2 = assert_state_dir_reports_and_files(&state_dir, "smoke");
    assert_campaign_report_structure(
        &report2,
        "smoke",
        "NOT EVALUATED",
        "0x9e3779ca",
        "0x9e3779db",
        "15",
        "14",
        "11",
        "9 at both `-O0` and `-O2` (compile only)",
        "7",
        "1",
        "**not performed**",
        "**not performed**",
    );
    let junit_xml2 = fs::read_to_string(&junit).expect("JUnit XML");
    assert_junit_xml_structure(
        &junit_xml2,
        "smoke",
        "oracle comparison not performed",
        "miri-difftest generated 15 candidates, 11 of which compiled, but it did not compare \
         Anneal with Miri or with native execution, so this run is not evidence about Anneal.",
        "oracle comparison not performed",
        "itree-difftest generated 14 candidates, 9 of which compiled, but it did not compare \
         Anneal with Miri or with native execution, so this run is not evidence about Anneal.",
    );
    let (ledger2, _) = json_fields(&state_dir.join("state/campaign_ledger.json"));
    assert_eq!(json_field(&ledger2, "total_campaigns_run"), "6");
    assert_eq!(
        json_field(&ledger2, "total_miri_candidates_generated"),
        "41"
    );
    assert_eq!(
        json_field(&ledger2, "total_itree_candidates_generated"),
        "50"
    );
}

#[test]
fn campaign_runner_syncs_remote_only_when_asked() {
    let dir = unique_temp_dir("remote_sync");
    let log = dir.join("remote_sync.log");
    let stub = dir.join("remote_sync_stub.sh");
    write_remote_sync_stub(&stub, &log, 0);

    // Without `--remote-uri`, a run must not touch remote at all.
    let out = run_campaign_driver(
        &stub,
        &[],
        &[],
        &["--profile", "smoke", "--compile-only"],
        &dir.join("default"),
    );
    assert_eq!(
        out.status.code(),
        Some(3),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        !log.exists(),
        "a run without --remote-uri invoked remote_sync:\n{}",
        fs::read_to_string(&log).unwrap_or_default()
    );

    // Positive control: with `--remote-uri`, the stub must be invoked for the
    // files this run wrote, but not for a stale report left in the state
    // directory by an earlier run.
    let explicit = dir.join("explicit");
    fs::create_dir_all(explicit.join("reports")).expect("create reports dir");
    fs::write(
        explicit.join("reports/2026-01-01_quick_campaign_report.md"),
        "stale\n",
    )
    .expect("write stale report");
    let base = "/remote/teams/example/differential-testing";
    let out = run_campaign_driver(
        &stub,
        &[],
        &[],
        &["--profile", "smoke", "--compile-only", "--remote-uri", base],
        &explicit,
    );
    assert_eq!(
        out.status.code(),
        Some(3),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let calls = fs::read_to_string(&log).expect("remote_sync stub must have been invoked");
    assert!(
        calls.contains(&format!("{base}/state/campaign_ledger.json")),
        "{calls}"
    );
    assert!(
        calls.contains(&format!("{base}/reports/LATEST_REPORT.md")),
        "{calls}"
    );
    assert!(
        !calls.contains("2026-01-01_quick_campaign_report.md"),
        "a stale report was uploaded:\n{calls}"
    );
}

#[test]
fn campaign_runner_rejects_oracle_claims_it_cannot_present() {
    let dir = unique_temp_dir("oracle_claim");
    let junit = dir.join("diff_test_report.xml");
    let junit_arg = junit.to_string_lossy().into_owned();
    let remote_sync_log = dir.join("remote_sync.log");
    let remote_sync = dir.join("remote_sync_must_not_run.sh");
    write_remote_sync_stub(&remote_sync, &remote_sync_log, 1);
    let ledger =
        r#"{"next_miri_seed": "0x11", "next_itree_seed": "0x22", "total_campaigns_run": 4}"#;

    let assert_failed_run = |state_dir: &Path, miri_gen: &str, itree_gen: &str| {
        let report = assert_state_dir_reports_and_files(state_dir, "smoke");
        assert_campaign_report_structure(
            &report,
            "smoke",
            "HARNESS FAILED",
            "0x00000011",
            "0x00000022",
            miri_gen,
            itree_gen,
            "n/a",
            "n/a",
            "n/a",
            "n/a",
            "harness failed",
            "harness failed",
        );
        let junit_xml = fs::read_to_string(&junit).expect("JUnit XML");
        assert_junit_xml_structure(
            &junit_xml,
            "smoke",
            "harness failed",
            "miri-difftest exited with an error, wrote unreadable JSON, or reported an oracle \
             status this runner cannot present.",
            "harness failed",
            "itree-difftest exited with an error, wrote unreadable JSON, or reported an oracle \
             status this runner cannot present.",
        );
        assert_eq!(
            fs::read_to_string(state_dir.join("state/campaign_ledger.json")).expect("ledger"),
            ledger,
            "the ledger must be unchanged after a harness failure"
        );
    };

    for (label, summary) in [
        (
            "performed",
            r#"{"oracle_comparison": "performed", "total_candidates": 4}"#,
        ),
        ("missing", r#"{"total_candidates": 4}"#),
    ] {
        let state_dir = dir.join(label);
        fs::create_dir_all(state_dir.join("state")).expect("create state dir");
        fs::write(state_dir.join("state/campaign_ledger.json"), ledger).expect("write ledger");
        let out = run_campaign_driver(
            &remote_sync,
            &[],
            &[format!("harness_summary={summary}")],
            &[
                "--profile",
                "smoke",
                "--remote-uri",
                "",
                "--junit-xml",
                &junit_arg,
            ],
            &state_dir,
        );
        assert_eq!(
            out.status.code(),
            Some(2),
            "a harness reporting oracle status `{label}` must fail the campaign:\n{}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert_failed_run(&state_dir, "4", "4");
    }

    // Exercise `run_harness` itself when `cargo` exits non-zero or writes no
    // JSON output: neither case may be mistaken for `"not_performed"`.
    for (label, script) in [
        ("crash", "#!/bin/sh\nexit 1\n"),
        ("no_json", "#!/bin/sh\nexit 0\n"),
    ] {
        let bin_dir = dir.join(format!("bin_{label}"));
        fs::create_dir_all(&bin_dir).expect("create bin dir");
        write_executable(&bin_dir.join("cargo"), script);
        let path_env = PathBuf::from(format!(
            "{}:{}",
            bin_dir.display(),
            std::env::var("PATH").unwrap_or_default()
        ));
        let state_dir = dir.join(label);
        fs::create_dir_all(state_dir.join("state")).expect("create state dir");
        fs::write(state_dir.join("state/campaign_ledger.json"), ledger).expect("write ledger");
        let out = run_campaign_driver(
            &remote_sync,
            &[("PATH", &path_env)],
            &[],
            &[
                "--profile",
                "smoke",
                "--remote-uri",
                "",
                "--junit-xml",
                &junit_arg,
            ],
            &state_dir,
        );
        assert_eq!(
            out.status.code(),
            Some(2),
            "a harness `{label}` failure must exit with status 2:\n{}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert_failed_run(&state_dir, "n/a", "n/a");
    }

    assert!(
        !remote_sync_log.exists(),
        "the runner invoked remote_sync without an remote URI"
    );
}
