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
    "ClosureAndAddrEqMutator",
    "ExtOracleInjector",
    "IndirectDispatchOutliner",
    "LayoutPaddingPerturber",
    "PlaceProjectionWrapper",
    "RawPtrOffsetMutator",
    "TreeBorrowsRetagInterleaver",
    "VTableAndFnPtrMutator",
];

/// The only keys the runner writes to the ledger. It also preserves keys that
/// are already present and not obsolete, such as labels added by an external
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
/// globals. `harness_summary=<json>` makes every harness return that summary
/// instead of running. The remaining arguments are passed to the runner.
const RUNNER_DRIVER: &str = r#"
import importlib.util, json, sys
spec = importlib.util.spec_from_file_location("runner", sys.argv[1])
runner = importlib.util.module_from_spec(spec)
# `dataclass` resolves annotations through `sys.modules[cls.__module__]`.
sys.modules["runner"] = runner
spec.loader.exec_module(runner)
args = sys.argv[2:]
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
        "VTableAndFnPtrMutator",
        "ClosureAndAddrEqMutator",
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
        "IndirectDispatchOutliner",
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

    fs::create_dir_all(state_dir.join("state")).expect("create state dir");
    // A ledger written by an earlier runner version, with distinct starting
    // counts, obsolete evaluation keys, and a custom launcher label.
    fs::write(
        state_dir.join("state/campaign_ledger.json"),
        r#"{"next_miri_seed": "0x11", "next_itree_seed": "0x22", "total_campaigns_run": 4,
            "total_miri_candidates_generated": 10, "total_itree_candidates_generated": 20,
            "total_miri_candidates_evaluated": 99, "cumulative_distinct_obs_paths": 7,
            "active_fingerprints": [], "_NONFUNCTIONAL_NOTICE": "label"}"#,
    )
    .expect("write ledger");

    let out = run_campaign_driver(
        &[],
        &[],
        &[
            "--profile",
            "smoke",
            "--compile-only",
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
        &[("PATH", &path_env)],
        &[],
        &[
            "--profile",
            "smoke",
            "--compile-only",
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
fn campaign_runner_rejects_oracle_claims_it_cannot_present() {
    let dir = unique_temp_dir("oracle_claim");
    let junit = dir.join("diff_test_report.xml");
    let junit_arg = junit.to_string_lossy().into_owned();
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
            &[],
            &[format!("harness_summary={summary}")],
            &[
                "--profile",
                "smoke",
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
            &[("PATH", &path_env)],
            &[],
            &[
                "--profile",
                "smoke",
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
}

fn compile_and_run_spec_harness(label: &str, source: &str) -> Vec<String> {
    let dir = unique_temp_dir(label);
    let src_path = dir.join("spec_harness.rs");
    let bin_path = dir.join("spec_harness_bin");
    fs::write(&src_path, source).expect("write spec harness source");

    let compile_out = Command::new(resolve_rustc_bin())
        .args([
            "--edition=2024",
            "-C",
            "debug-assertions=on",
            "-D",
            "warnings",
            "-o",
        ])
        .arg(&bin_path)
        .arg(&src_path)
        .output()
        .expect("spawn rustc for executable spec harness");
    assert!(
        compile_out.status.success(),
        "rustc -D warnings failed for `{label}`:\n{}\nsource:\n{source}",
        String::from_utf8_lossy(&compile_out.stderr)
    );

    let run_out = Command::new(&bin_path)
        .output()
        .expect("execute compiled spec harness");
    assert!(
        run_out.status.success(),
        "compiled spec harness `{label}` exited non-zero:\n{}",
        String::from_utf8_lossy(&run_out.stderr)
    );
    String::from_utf8_lossy(&run_out.stdout)
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| !l.is_empty())
        .collect()
}

#[test]
fn external_spec_postcondition_oracle_probe_compiles_strict_and_matches_native_execution() {
    use anneal_difftest::{
        SpecContractOracleProbe, SpecExternalCallee, SpecParamBinding, SpecPostconditionVerdict,
    };

    let u32_layout = LayoutSpec::Scalar(ScalarLayout::u32());
    let counter_pair_layout = LayoutSpec::Struct {
        name: "CounterPair".to_string(),
        total_size: 12,
        fields: vec![
            FieldLayout {
                name: "tag".to_string(),
                offset: 0,
                layout: LayoutSpec::Scalar(ScalarLayout::u8()),
            },
            FieldLayout {
                name: "active".to_string(),
                offset: 4,
                layout: u32_layout.clone(),
            },
            FieldLayout {
                name: "untouched".to_string(),
                offset: 8,
                layout: u32_layout.clone(),
            },
        ],
    };

    let probe = SpecContractOracleProbe::new(
        "advance_counter_with_bonus",
        vec![
            SpecParamBinding::mut_ref("pair", "CounterPair", counter_pair_layout)
                .with_frame_preserved_fields(["tag", "untouched"]),
            SpecParamBinding::by_value("step", "u32", u32_layout.clone()),
        ],
        "u32",
        u32_layout.clone(),
        "let raw_bonus: u32 = ext_bonus(step);\n\
         let capped_bonus: u32 = raw_bonus & 7u32;\n\
         pair.active = pair.active + step + capped_bonus;\n\
         pair.active",
    )
    .with_type_defs(
        "#[repr(C)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub struct CounterPair { pub tag: u8, pub active: u32, pub untouched: u32 }",
    )
    .with_external_callee(SpecExternalCallee::new(
        "ext_bonus",
        ["u32"],
        "u32",
        u32_layout.clone(),
    ))
    .with_requires(
        "bounded_inputs",
        "step <= 16u32 && pair.active <= u32::MAX - 23u32",
    )
    .with_ensures("monotonic", "pair.active >= old(pair.active) + step")
    .with_ensures(
        "bounded_growth",
        "result <= old(pair.active) + step + 7u32 && result == pair.active",
    );

    // 1. Standalone library module compiles cleanly under `rustc -D warnings` with zero `unsafe`.
    let lib_src = probe
        .synthesize_rust_probe()
        .expect("synthesize standalone probe");
    assert!(
        !contains_unsafe_token(&lib_src),
        "synthesized spec probe must not emit `unsafe`"
    );
    compile_module_with_rustc("ep2_sound_spec_lib", &["-D", "warnings"], &lib_src)
        .expect("standalone spec probe compiles with -D warnings");

    // 2. Non-vacuous certification across 48 dictionary-biased trials (0 panics).
    let mut dict = MirInputDictionary::new();
    dict.add_switch_int_literal(0, 32);
    dict.add_switch_int_literal(8, 32);
    dict.add_switch_int_literal(16, 32);
    dict.add_switch_int_literal(u32::MAX as u128, 32);
    let builder = LayoutAwareByteBuilder::new(&dict)
        .with_dictionary_bias_pct(65)
        .with_padding_pattern(PaddingFillPattern::AlternatingA55A);
    let combined_layout = probe.combined_input_layout();
    let sched_gen_clean = EnvScheduleGenerator::new(&dict)
        .with_horizon_steps(2)
        .with_panic_injection_pct(0)
        .with_callee_return_layout("ext_bonus", u32_layout.clone());

    let mut clean_trials: Vec<(Vec<u8>, Option<EnvSchedule>)> = Vec::with_capacity(48);
    // Seed explicit valid + boundary-filtered trials first so both outcomes are guaranteed,
    // followed by deterministic `Unstructured` fuzz trials with non-zero padding bytes.
    let mut valid_seed = vec![0x55u8; 16];
    valid_seed[0] = 3u8;
    valid_seed[4..8].copy_from_slice(&100u32.to_le_bytes());
    valid_seed[8..12].copy_from_slice(&999u32.to_le_bytes());
    valid_seed[12..16].copy_from_slice(&12u32.to_le_bytes());
    let mut u0 = Unstructured::new(&[0x21; 64]);
    clean_trials.push((
        valid_seed.clone(),
        Some(sched_gen_clean.generate_schedule(&["ext_bonus"], &mut u0)),
    ));

    let mut filtered_seed = valid_seed.clone();
    filtered_seed[12..16].copy_from_slice(&50u32.to_le_bytes());
    let mut u1 = Unstructured::new(&[0x22; 64]);
    clean_trials.push((
        filtered_seed,
        Some(sched_gen_clean.generate_schedule(&["ext_bonus"], &mut u1)),
    ));

    for seed in 0..46u8 {
        let entropy: Vec<u8> = (0..96u8)
            .map(|i| seed.wrapping_mul(37).wrapping_add(i.wrapping_mul(13)))
            .collect();
        let mut u = Unstructured::new(&entropy);
        let arg_bytes = builder.build_bytes(&combined_layout, &mut u);
        let sched = sched_gen_clean.generate_schedule(&["ext_bonus"], &mut u);
        clean_trials.push((arg_bytes, Some(sched)));
    }

    let clean_report = probe
        .verify_spec_postcondition_batch(&clean_trials)
        .expect("verify clean batch");
    assert!(
        clean_report.is_sound_and_non_vacuous(),
        "sound spec must pass non-vacuous certification: {clean_report:?}"
    );
    assert!(clean_report.vacuously_filtered_count >= 1);
    assert!(clean_report.verified_hold_count >= 1);

    // Append 4 scheduled-panic trials to verify exact 1-for-1 `HOLD`/`FILTERED`/`TRAP` parity
    // between `verify_spec_postcondition_against_schedule` and native `rustc -D warnings`.
    let mut parity_trials = clean_trials;
    let panic_gen = EnvScheduleGenerator::new(&dict)
        .with_horizon_steps(1)
        .with_callee_return_layout("ext_bonus", u32_layout);
    for seed in 0..4u8 {
        let buf = [seed.wrapping_add(0x70); 64];
        let mut u = Unstructured::new(&buf);
        let mut arg = valid_seed.clone();
        arg[12..16].copy_from_slice(&(seed as u32).to_le_bytes());
        let mut p_sched = EnvSchedule::new();
        panic_gen.apply_strategy(
            &mut p_sched,
            "ext_bonus",
            &EnvStrategy::PanicOnCall(0),
            &mut u,
        );
        parity_trials.push((arg, Some(p_sched)));
    }

    let parity_report = probe
        .verify_spec_postcondition_batch(&parity_trials)
        .expect("verify parity batch");
    let exe_src = probe
        .synthesize_rust_executable_harness_with_schedules(&parity_trials)
        .expect("synthesize executable harness");
    let native_lines = compile_and_run_spec_harness("ep2_sound_parity", &exe_src);
    assert_eq!(native_lines.len(), parity_report.verdicts.len());
    for (idx, (verdict, line)) in parity_report
        .verdicts
        .iter()
        .zip(native_lines.iter())
        .enumerate()
    {
        let expected_line = match verdict {
            SpecPostconditionVerdict::VerifiedHold => format!("TRIAL:{idx}:HOLD"),
            SpecPostconditionVerdict::VacuouslyFiltered { .. } => format!("TRIAL:{idx}:FILTERED"),
            SpecPostconditionVerdict::PanicOrTrap { .. } => format!("TRIAL:{idx}:TRAP"),
            other => panic!("unexpected verdict at trial {idx}: {other:?}"),
        };
        assert_eq!(line, &expected_line, "trial {idx} native vs oracle mismatch");
    }
}

#[test]
fn external_spec_oracle_kills_all_three_verus_unsound_spec_mutants() {
    use anneal_difftest::{
        SpecContractOracleProbe, SpecExecPhase, SpecParamBinding, SpecPostconditionVerdict,
        SpecViolationKind,
    };

    let u32_layout = LayoutSpec::Scalar(ScalarLayout::u32());
    let mut dict = MirInputDictionary::new();
    dict.add_switch_int_literal(0, 32);
    dict.add_switch_int_literal(1, 32);
    dict.add_shift_const(32, 32);
    dict.add_switch_int_literal(64, 32);
    let builder = LayoutAwareByteBuilder::new(&dict)
        .with_dictionary_bias_pct(85)
        .with_padding_pattern(PaddingFillPattern::Fixed(0xFF));

    let mut mutants_killed = 0usize;
    let mut sound_controls_passed = 0usize;

    // -------------------------------------------------------------------------
    // Mutant 1 (Verus #2674-style off-by-one postcondition):
    // `last_index(len)` returns `len - 1` for `len >= 1`, but the unsound spec
    // asserts `ensures(result == len)` instead of `ensures(result == len - 1u32)`.
    // -------------------------------------------------------------------------
    let mutant1 = SpecContractOracleProbe::new(
        "last_index_off_by_one_mutant",
        vec![SpecParamBinding::by_value("len", "u32", u32_layout.clone())],
        "u32",
        u32_layout.clone(),
        "len - 1u32",
    )
    .with_requires("non_empty", "len >= 1u32")
    .with_ensures("wrong_upper_bound", "result == len");

    let control1 = SpecContractOracleProbe::new(
        "last_index_sound_control",
        vec![SpecParamBinding::by_value("len", "u32", u32_layout.clone())],
        "u32",
        u32_layout.clone(),
        "len - 1u32",
    )
    .with_requires("non_empty", "len >= 1u32")
    .with_ensures("exact_last_index", "result == len - 1u32");

    let mut trials1: Vec<(Vec<u8>, Option<EnvSchedule>)> = vec![
        (0u32.to_le_bytes().to_vec(), None),
        (1u32.to_le_bytes().to_vec(), None),
        (8u32.to_le_bytes().to_vec(), None),
    ];
    for s in 0..16u8 {
        let buf = [s.wrapping_mul(29).wrapping_add(3); 32];
        let mut u = Unstructured::new(&buf);
        trials1.push((builder.build_bytes(&mutant1.combined_input_layout(), &mut u), None));
    }
    let rep_m1 = mutant1
        .verify_spec_postcondition_batch(&trials1)
        .expect("eval mutant 1");
    assert!(rep_m1.is_mutant_killed());
    assert!(rep_m1.verdicts.iter().any(|v| matches!(
        v,
        SpecPostconditionVerdict::PostconditionViolation {
            kind: SpecViolationKind::EnsuresClause { label, .. },
            ..
        } if label == "wrong_upper_bound"
    )));
    let raw_trials1: Vec<Vec<u8>> = trials1.iter().map(|(b, _)| b.clone()).collect();
    let lines_m1 = compile_and_run_spec_harness(
        "ep2_mutant1_verus2674",
        &mutant1
            .synthesize_rust_executable_harness(&raw_trials1)
            .expect("synth mutant 1"),
    );
    assert!(
        lines_m1
            .iter()
            .any(|l| l.ends_with(":VIOLATION:wrong_upper_bound")),
        "native compiled probe must kill Mutant 1: {lines_m1:?}"
    );
    mutants_killed += 1;
    assert!(
        control1
            .verify_spec_postcondition_batch(&trials1)
            .expect("eval control 1")
            .is_sound_and_non_vacuous()
    );
    sound_controls_passed += 1;

    // -------------------------------------------------------------------------
    // Mutant 2 (Verus #2603-style omitted shift-width / overflow precondition):
    // `shl_u32(val, shift)` omits `requires(shift < 32u32)` and shifts by an
    // unbounded `shift: u32`, trapping on `shift >= 32` (`unchecked_shl` / debug `<<`).
    // -------------------------------------------------------------------------
    let mutant2 = SpecContractOracleProbe::new(
        "shl_missing_shift_bound_mutant",
        vec![
            SpecParamBinding::by_value("val", "u32", u32_layout.clone()),
            SpecParamBinding::by_value("shift", "u32", u32_layout.clone()),
        ],
        "u32",
        u32_layout.clone(),
        "val << shift",
    )
    .with_requires("val_bounded_only", "val <= 1024u32")
    .with_ensures("non_zero_when_one", "val != 1u32 || result >= 1u32");

    let control2 = SpecContractOracleProbe::new(
        "shl_sound_control",
        vec![
            SpecParamBinding::by_value("val", "u32", u32_layout.clone()),
            SpecParamBinding::by_value("shift", "u32", u32_layout.clone()),
        ],
        "u32",
        u32_layout.clone(),
        "val << shift",
    )
    .with_requires("val_and_shift_bounded", "val <= 1024u32 && shift < 20u32")
    .with_ensures("non_zero_when_one", "val != 1u32 || result >= 1u32");

    let mut trials2: Vec<(Vec<u8>, Option<EnvSchedule>)> = Vec::new();
    for s in 0..32u8 {
        let entropy: Vec<u8> = (0..64u8)
            .map(|i| s.wrapping_mul(41).wrapping_add(i.wrapping_mul(7)))
            .collect();
        let mut u = Unstructured::new(&entropy);
        trials2.push((builder.build_bytes(&mutant2.combined_input_layout(), &mut u), None));
    }
    // Ensure a concrete valid witness `(1, 4)` is also included for non-vacuity of `control2`.
    let mut valid_shl = Vec::with_capacity(8);
    valid_shl.extend_from_slice(&1u32.to_le_bytes());
    valid_shl.extend_from_slice(&4u32.to_le_bytes());
    trials2.push((valid_shl, None));

    let rep_m2 = mutant2
        .verify_spec_postcondition_batch(&trials2)
        .expect("eval mutant 2");
    assert!(rep_m2.is_mutant_killed());
    assert!(rep_m2.verdicts.iter().any(|v| matches!(
        v,
        SpecPostconditionVerdict::PanicOrTrap {
            phase: SpecExecPhase::Body,
            ..
        }
    )));
    let raw_trials2: Vec<Vec<u8>> = trials2.iter().map(|(b, _)| b.clone()).collect();
    let lines_m2 = compile_and_run_spec_harness(
        "ep2_mutant2_verus2603",
        &mutant2
            .synthesize_rust_executable_harness(&raw_trials2)
            .expect("synth mutant 2"),
    );
    assert!(
        lines_m2.iter().any(|l| l.ends_with(":TRAP")),
        "native compiled probe must trap on Mutant 2 (`shift >= 32`): {lines_m2:?}"
    );
    mutants_killed += 1;
    assert!(
        control2
            .verify_spec_postcondition_batch(&trials2)
            .expect("eval control 2")
            .is_sound_and_non_vacuous()
    );
    sound_controls_passed += 1;

    // -------------------------------------------------------------------------
    // Mutant 3 (Verus #2606-style `&mut` frame / `old(...)` mutation violation):
    // `bump_active` promises `untouched` is framed (`post.untouched == old.untouched`)
    // and `pair.active == old(pair.active) + delta`, but covertly mutates `pair.untouched`.
    // -------------------------------------------------------------------------
    let pair_layout = LayoutSpec::Struct {
        name: "FramedAccount".to_string(),
        total_size: 12,
        fields: vec![
            FieldLayout {
                name: "flags".to_string(),
                offset: 0,
                layout: LayoutSpec::Scalar(ScalarLayout::u8()),
            },
            FieldLayout {
                name: "active".to_string(),
                offset: 4,
                layout: u32_layout.clone(),
            },
            FieldLayout {
                name: "untouched".to_string(),
                offset: 8,
                layout: u32_layout.clone(),
            },
        ],
    };
    let account_typedef = "#[repr(C)]\n\
                           #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
                           pub struct FramedAccount { pub flags: u8, pub active: u32, pub untouched: u32 }";

    let mutant3 = SpecContractOracleProbe::new(
        "bump_account_frame_mutant",
        vec![
            SpecParamBinding::mut_ref("acct", "FramedAccount", pair_layout.clone())
                .with_frame_preserved_fields(["flags", "untouched"]),
            SpecParamBinding::by_value("delta", "u32", u32_layout.clone()),
        ],
        "u32",
        u32_layout.clone(),
        "acct.active = acct.active + delta;\n\
         acct.untouched = acct.untouched.wrapping_add(1u32);\n\
         acct.active",
    )
    .with_type_defs(account_typedef)
    .with_requires(
        "safe_bump",
        "acct.active <= 100_000u32 && delta >= 1u32 && delta <= 1000u32",
    )
    .with_ensures("exact_bump", "acct.active == old(acct.active) + delta && result == acct.active");

    let control3 = SpecContractOracleProbe::new(
        "bump_account_sound_control",
        vec![
            SpecParamBinding::mut_ref("acct", "FramedAccount", pair_layout)
                .with_frame_preserved_fields(["flags", "untouched"]),
            SpecParamBinding::by_value("delta", "u32", u32_layout),
        ],
        "u32",
        LayoutSpec::Scalar(ScalarLayout::u32()),
        "acct.active = acct.active + delta;\n\
         acct.active",
    )
    .with_type_defs(account_typedef)
    .with_requires(
        "safe_bump",
        "acct.active <= 100_000u32 && delta >= 1u32 && delta <= 1000u32",
    )
    .with_ensures("exact_bump", "acct.active == old(acct.active) + delta && result == acct.active");

    let mut valid_acct = vec![0xFFu8; 16];
    valid_acct[0] = 7u8;
    valid_acct[4..8].copy_from_slice(&250u32.to_le_bytes());
    valid_acct[8..12].copy_from_slice(&42u32.to_le_bytes());
    valid_acct[12..16].copy_from_slice(&15u32.to_le_bytes());
    let mut trials3: Vec<(Vec<u8>, Option<EnvSchedule>)> = vec![(valid_acct, None)];
    for s in 0..16u8 {
        let buf = [s.wrapping_mul(19).wrapping_add(11); 48];
        let mut u = Unstructured::new(&buf);
        trials3.push((builder.build_bytes(&mutant3.combined_input_layout(), &mut u), None));
    }

    let rep_m3 = mutant3
        .verify_spec_postcondition_batch(&trials3)
        .expect("eval mutant 3");
    assert!(rep_m3.is_mutant_killed());
    assert!(rep_m3.verdicts.iter().any(|v| matches!(
        v,
        SpecPostconditionVerdict::PostconditionViolation {
            kind: SpecViolationKind::FrameCondition { param, field },
            ..
        } if param == "acct" && field == "untouched"
    )));
    let raw_trials3: Vec<Vec<u8>> = trials3.iter().map(|(b, _)| b.clone()).collect();
    let lines_m3 = compile_and_run_spec_harness(
        "ep2_mutant3_verus2606",
        &mutant3
            .synthesize_rust_executable_harness(&raw_trials3)
            .expect("synth mutant 3"),
    );
    assert!(
        lines_m3
            .iter()
            .any(|l| l.ends_with(":FRAME:acct.untouched")),
        "native compiled probe must kill Mutant 3 frame violation: {lines_m3:?}"
    );
    mutants_killed += 1;
    assert!(
        control3
            .verify_spec_postcondition_batch(&trials3)
            .expect("eval control 3")
            .is_sound_and_non_vacuous()
    );
    sound_controls_passed += 1;

    assert_eq!(mutants_killed, 3, "all 3/3 Verus-style mutants must be killed");
    assert_eq!(
        sound_controls_passed, 3,
        "all 3/3 sound control contracts must pass without false positives"
    );
}

#[test]
fn write_chain_coverage_bound_separates_depth_one_local_writes_from_scheduled_rmw_walks() {
    use anneal_difftest::{
        EnvScheduledWriteStep, UnderExplorationReason, WriteChainCoverageBound, WriteChainStep,
    };

    let mut dict = MirInputDictionary::new();
    dict.add_switch_int_literal(1, 32);
    dict.add_switch_int_literal(7, 32);
    let builder = LayoutAwareByteBuilder::new(&dict);
    let triple_u32 = LayoutSpec::Tuple {
        total_size: 12,
        elements: vec![
            (0, LayoutSpec::Scalar(ScalarLayout::u32())),
            (4, LayoutSpec::Scalar(ScalarLayout::u32())),
            (8, LayoutSpec::Scalar(ScalarLayout::u32())),
        ],
    };
    let mut u = Unstructured::new(&[0x5A; 128]);
    let seed_bytes = builder.build_bytes(&triple_u32, &mut u);
    assert_eq!(seed_bytes.len(), 12);

    // 1. Repeated independent depth-1 writes (`x = c0; y = c1; z = c2; x = c3; y = c4; z = c5`)
    //    do NOT sum to causal walk length `d = 3`.
    let mut local_only = WriteChainCoverageBound::new(3, 3);
    assert_eq!(local_only.min_walk_length(), 3);
    assert!(local_only.random_walk_step_bound() >= 9);
    for round in 0..2 {
        for slot in ["x", "y", "z"] {
            let _ = (round, &seed_bytes);
            local_only.observe_step(&WriteChainStep::local_write(slot));
        }
    }
    assert_eq!(local_only.max_observed_depth(), 1);
    assert!(!local_only.is_depth_certified());
    assert_eq!(
        local_only.under_exploration_reason(),
        Some(UnderExplorationReason::OnlyDepthOneLocalWrites {
            steps_observed: 6,
            distinct_slots_written: 3,
            required_depth: 3,
        })
    );

    // 2. Depth-2 chain followed by constant overwrite on `y` resets `y` to depth 1,
    //    preventing `z := f(y)` from falsely reaching depth 3.
    let mut overwrite_guard = WriteChainCoverageBound::new(3, 3);
    overwrite_guard.observe_write_chain(&[
        WriteChainStep::local_write("x"),
        WriteChainStep::dependent_write("y", ["x"]),
        WriteChainStep::local_write("y"),
        WriteChainStep::dependent_write("z", ["y"]),
    ]);
    assert_eq!(overwrite_guard.current_slot_depth("y"), 1);
    assert_eq!(overwrite_guard.current_slot_depth("z"), 2);
    assert_eq!(overwrite_guard.max_observed_depth(), 2);
    assert!(!overwrite_guard.is_depth_certified());
    assert!(matches!(
        overwrite_guard.under_exploration_reason(),
        Some(UnderExplorationReason::InsufficientChainDepth {
            max_observed_depth: 2,
            required_depth: 3,
            steps_observed: 4,
            ..
        })
    ));

    // 3. `EnvSchedule`-driven transitive RMW walk across 3 boundary steps:
    //    - Gapped/panicking schedule (`PanicAtCall(1)`) fails certification with `BrokenEnvScheduleLink`.
    //    - Complete non-panicking schedule (`ReturnBytes` of 4-byte `u32`) certifies `min_walk_length = 3`.
    let planned_walk = vec![
        EnvScheduledWriteStep::new("ext_rmw_hop", "x", std::iter::empty::<&str>()),
        EnvScheduledWriteStep::new("ext_rmw_hop", "y", ["x"]),
        EnvScheduledWriteStep::new("ext_rmw_hop", "z", ["y"]),
    ];

    let panic_sched_gen = EnvScheduleGenerator::new(&dict)
        .with_horizon_steps(3)
        .with_callee_return_layout("ext_rmw_hop", LayoutSpec::Scalar(ScalarLayout::u32()));
    let mut broken_sched = EnvSchedule::new();
    panic_sched_gen.apply_strategy(
        &mut broken_sched,
        "ext_rmw_hop",
        &EnvStrategy::Constant(1u32.to_le_bytes().to_vec()),
        &mut u,
    );
    broken_sched.set_callee_panic_on_call("ext_rmw_hop", 1);
    let mut broken_walk = WriteChainCoverageBound::new(3, 3);
    broken_walk.observe_env_schedule(&broken_sched, &planned_walk);
    assert!(!broken_walk.is_depth_certified());
    assert!(matches!(
        broken_walk.under_exploration_reason(),
        Some(UnderExplorationReason::BrokenEnvScheduleLink {
            required_depth: 3,
            broken_links: 1,
            ..
        })
    ));

    let valid_sched_gen = EnvScheduleGenerator::new(&dict)
        .with_horizon_steps(3)
        .with_panic_injection_pct(0)
        .with_callee_return_layout("ext_rmw_hop", LayoutSpec::Scalar(ScalarLayout::u32()));
    let complete_sched = valid_sched_gen.generate_schedule(&["ext_rmw_hop"], &mut u);
    let mut certified_walk = WriteChainCoverageBound::new(3, 3);
    let max_d = certified_walk.observe_env_schedule(&complete_sched, &planned_walk);
    assert_eq!(max_d, 3);
    assert!(certified_walk.is_depth_certified());
    assert_eq!(certified_walk.under_exploration_reason(), None);
}

#[test]
fn external_spec_oracle_lockstep_parity_on_lazy_old_padding_eq_mut_helpers_and_multi_callee_schedules()
{
    use anneal_difftest::{
        SpecContractOracleProbe, SpecExternalCallee, SpecParamBinding, SpecPostconditionVerdict,
        SpecViolationKind,
    };

    let u32_layout = LayoutSpec::Scalar(ScalarLayout::u32());
    let state_layout = LayoutSpec::Struct {
        name: "PaddedSlotBank".to_string(),
        total_size: 20,
        fields: vec![
            FieldLayout {
                name: "tag".to_string(),
                offset: 0,
                layout: LayoutSpec::Scalar(ScalarLayout::u8()),
            },
            FieldLayout {
                name: "slots".to_string(),
                offset: 4,
                layout: LayoutSpec::Array {
                    elem: Box::new(u32_layout.clone()),
                    elem_stride: 4,
                    len: 3,
                },
            },
            FieldLayout {
                name: "framed".to_string(),
                offset: 16,
                layout: u32_layout.clone(),
            },
        ],
    };

    // Exercises:
    // 1. Short-circuit guarded `old(100u32 / denom)` (and Phase-3 FrameViolation priority
    //    when `corrupt_frame == 1` even if `old(100u32 / denom)` would trap in Phase 4!),
    // 2. Poison padding (`0xA5`) on `PaddedSlotBank` compared via `*bank == PaddedSlotBank { .. }`
    //    and `..*bank` struct update,
    // 3. `&mut` helper writeback (`add_capped(&mut bank.slots[idx], step)`), `/=`, `%=`,
    //    and single-evaluation `bank.slots[ext_pick_slot() as usize] += 2u32`,
    // 4. Multi-callee `EnvSchedule` (`ext_pick_slot` + `ext_tick`) with `global_panic_on_call`
    //    AND 18 calls to `ext_tick` (exceeding any fixed 16-call horizon via `callee_defaults`).
    let probe = SpecContractOracleProbe::new(
        "stress_lockstep_parity",
        vec![
            SpecParamBinding::mut_ref("bank", "PaddedSlotBank", state_layout)
                .with_frame_preserved_fields(["tag", "framed"]),
            SpecParamBinding::by_value("denom", "u32", u32_layout.clone()),
            SpecParamBinding::by_value("corrupt_frame", "u32", u32_layout.clone()),
        ],
        "u32",
        u32_layout.clone(),
        "let slot_idx: usize = (ext_pick_slot() & 1u32) as usize;\n\
         add_capped(&mut bank.slots[slot_idx], 4u32);\n\
         bank.slots[ext_pick_slot() as usize % 3usize] += 2u32;\n\
         bank.slots[2] /= 2u32;\n\
         bank.slots[1] %= 8u32;\n\
         let mut iter: u32 = 0u32;\n\
         let mut ticks: u32 = 0u32;\n\
         while iter < 18u32 {\n    \
             ticks = ticks.wrapping_add(ext_tick() & 3u32);\n    \
             iter += 1u32;\n\
         }\n\
         if corrupt_frame == 1u32 {\n    \
             bank.framed = bank.framed.wrapping_add(1u32);\n\
         }\n\
         *bank = PaddedSlotBank { slots: bank.slots, ..*bank };\n\
         ticks",
    )
    .with_type_defs(
        "#[repr(C)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub struct PaddedSlotBank { pub tag: u8, pub slots: [u32; 3], pub framed: u32 }\n\
         pub fn add_capped(dst: &mut u32, delta: u32) {\n    \
             *dst = dst.saturating_add(delta);\n\
         }",
    )
    .with_external_callee(SpecExternalCallee::new(
        "ext_pick_slot",
        std::iter::empty::<&str>(),
        "u32",
        u32_layout.clone(),
    ))
    .with_external_callee(SpecExternalCallee::new(
        "ext_tick",
        std::iter::empty::<&str>(),
        "u32",
        u32_layout,
    ))
    .with_requires(
        "slots_bounded",
        "bank.slots[0] <= 1000u32 && bank.slots[1] <= 1000u32 && bank.slots[2] <= 1000u32",
    )
    .with_ensures(
        "guarded_old_div",
        "(corrupt_frame == 0u32 && denom == 0u32) || old(100u32 / denom) <= 100u32",
    )
    .with_ensures(
        "padded_struct_reflexive_eq",
        "*bank == PaddedSlotBank { tag: old(bank.tag), slots: bank.slots, framed: old(bank.framed) } && result <= 54u32",
    );

    let make_trial_bytes = |denom: u32, corrupt_frame: u32| -> Vec<u8> {
        let mut raw = vec![0xA5u8; 28];
        raw[0] = 4u8;
        raw[4..8].copy_from_slice(&10u32.to_le_bytes());
        raw[8..12].copy_from_slice(&19u32.to_le_bytes());
        raw[12..16].copy_from_slice(&24u32.to_le_bytes());
        raw[16..20].copy_from_slice(&555u32.to_le_bytes());
        raw[20..24].copy_from_slice(&denom.to_le_bytes());
        raw[24..28].copy_from_slice(&corrupt_frame.to_le_bytes());
        raw
    };

    let mut base_sched = EnvSchedule::new()
        .with_callee_return_size("ext_pick_slot", 4)
        .with_callee_return_size("ext_tick", 4);
    base_sched.push_callee_response("ext_pick_slot", 0u32.to_le_bytes().to_vec());
    base_sched.push_callee_response("ext_pick_slot", 1u32.to_le_bytes().to_vec());
    base_sched.set_callee_default("ext_tick", 1u32.to_le_bytes().to_vec());

    // Trial 0: `denom == 0, corrupt_frame == 0` -> short-circuits `old(100 / denom)`,
    // runs 18 `ext_tick` default calls + poison-padded struct equality -> `HOLD`.
    let t0 = (make_trial_bytes(0, 0), Some(base_sched.clone()));

    // Trial 1: `denom == 5, corrupt_frame == 0` -> evaluates `old(100 / 5) == 20 <= 100` -> `HOLD`.
    let t1 = (make_trial_bytes(5, 0), Some(base_sched.clone()));

    // Trial 2: `denom == 0, corrupt_frame == 1` -> Phase-3 `FrameViolation("bank.framed")`
    // MUST fire BEFORE Phase-4 `old(100 / 0)` trap!
    let t2 = (make_trial_bytes(0, 1), Some(base_sched.clone()));

    // Trial 3: `denom == 0, corrupt_frame == 2` -> guard `(corrupt_frame == 0 && denom == 0)`
    // is false, so Phase-4 `old(100 / 0)` executes and traps -> `TRAP`.
    let t3 = (make_trial_bytes(0, 2), Some(base_sched.clone()));

    // Trial 4: Multi-callee `global_panic_on_call = Some(2)` (call 0 = `ext_pick_slot`,
    // call 1 = `ext_pick_slot`, call 2 = 1st `ext_tick`!) -> `TRAP` in both!
    let mut global_panic_sched = base_sched;
    global_panic_sched.set_panic_on_call(2);
    let t4 = (make_trial_bytes(5, 0), Some(global_panic_sched));

    let trials = vec![t0, t1, t2, t3, t4];
    let report = probe
        .verify_spec_postcondition_batch(&trials)
        .expect("evaluate adversarial parity batch");

    assert_eq!(report.verdicts[0], SpecPostconditionVerdict::VerifiedHold);
    assert_eq!(report.verdicts[1], SpecPostconditionVerdict::VerifiedHold);
    assert!(matches!(
        &report.verdicts[2],
        SpecPostconditionVerdict::PostconditionViolation {
            kind: SpecViolationKind::FrameCondition { param, field },
            ..
        } if param == "bank" && field == "framed"
    ));
    assert!(matches!(
        &report.verdicts[3],
        SpecPostconditionVerdict::PanicOrTrap { .. }
    ));
    assert!(matches!(
        &report.verdicts[4],
        SpecPostconditionVerdict::PanicOrTrap { .. }
    ));

    let exe_src = probe
        .synthesize_rust_executable_harness_with_schedules(&trials)
        .expect("synthesize adversarial parity harness");
    assert!(!contains_unsafe_token(&exe_src));
    let native_lines = compile_and_run_spec_harness("ep2_b1_lockstep_parity", &exe_src);
    assert_eq!(
        native_lines,
        vec![
            "TRIAL:0:HOLD",
            "TRIAL:1:HOLD",
            "TRIAL:2:FRAME:bank.framed",
            "TRIAL:3:TRAP",
            "TRIAL:4:TRAP",
        ]
    );
}

#[test]
fn ep2_a1_lockstep_parity_on_diverging_returns_loops_old_ref_rewrites_and_prestepped_schedules() {
    use anneal_difftest::{
        SpecContractOracleProbe, SpecExternalCallee, SpecParamBinding, SpecPostconditionVerdict,
    };

    let u8_layout = LayoutSpec::Scalar(ScalarLayout::u8());
    let u32_layout = LayoutSpec::Scalar(ScalarLayout::u32());
    let pair_layout = LayoutSpec::Struct {
        name: "ShortPair".to_string(),
        total_size: 8,
        fields: vec![
            FieldLayout {
                name: "x".to_string(),
                offset: 0,
                layout: u32_layout.clone(),
            },
            FieldLayout {
                name: "framed".to_string(),
                offset: 4,
                layout: u32_layout.clone(),
            },
        ],
    };

    let probe = SpecContractOracleProbe::new(
        "ep2_a1_control_and_schedule_probe",
        vec![
            SpecParamBinding::mut_ref("pair", "ShortPair", pair_layout)
                .with_frame_preserved_fields(["framed"]),
            SpecParamBinding::by_value("x", "u8", u8_layout),
            SpecParamBinding::by_value("framed", "u32", u32_layout.clone()),
        ],
        "u32",
        u32_layout.clone(),
        "let ext_v: u32 = ext_hop();\n\
         let () = if x == 0u8 {\n    \
             early_bump(&mut (*pair).x, ext_v & 7u32);\n    \
             return pair.x;\n\
         } else {\n    \
             ()\n\
         };\n\
         let next_x: u8 = x + if x == 255u8 { return pair.x; } else { 1u8 };\n\
         x = next_x;\n\
         let mut i: u32 = 0u32;\n\
         let mut acc: u32 = 0u32;\n\
         while i < 6u32 {\n    \
             i += 1u32;\n    \
             if i == 2u32 { continue; }\n    \
             if i == 5u32 { break; }\n    \
             acc += i;\n\
         }\n\
         let tag_bonus: u32 = loop {\n    \
             break match x {\n        \
                 2u8 | 3u8 => 9u32,\n        \
                 n if n > 10u8 => n as u32,\n        \
                 _ => 4u32,\n    \
             };\n\
         };\n\
         pair.x = pair.x + acc + tag_bonus + (ext_v & 3u32) + (framed & 0u32);\n\
         pair.x",
    )
    .with_type_defs(
        "#[repr(C)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub struct ShortPair { pub x: u32, pub framed: u32 }\n\
         pub fn read_pair_x(p: &ShortPair) -> u32 { p.x }\n\
         pub fn early_bump(dst: &mut u32, add: u32) {\n    \
             *dst += add;\n    \
             let () = if *dst >= 1u32 { return; } else { () };\n    \
             *dst += 500u32;\n\
         }",
    )
    .with_external_callee(SpecExternalCallee::new(
        "ext_hop",
        std::iter::empty::<&str>(),
        "u32",
        u32_layout,
    ))
    .with_requires("bounded_x", "pair.x <= 1000u32")
    .with_ensures(
        "old_ref_shorthand_and_closure",
        "old(read_pair_x(pair)) == old(pair.x) \
         && old(ShortPair { x: 1u32, framed }).framed == framed \
         && old((|x: u32| x + 1u32)(5u32)) == 6u32",
    )
    .with_ensures("monotonic", "result >= old(pair.x)");

    let make_args = |px: u32, pframed: u32, x: u8, framed_arg: u32| -> Vec<u8> {
        let mut b = Vec::with_capacity(13);
        b.extend_from_slice(&px.to_le_bytes());
        b.extend_from_slice(&pframed.to_le_bytes());
        b.push(x);
        b.extend_from_slice(&framed_arg.to_le_bytes());
        b
    };

    let mut clean_sched = EnvSchedule::new().with_callee_return_size("ext_hop", 4);
    clean_sched.set_callee_default("ext_hop", 5u32.to_le_bytes().to_vec());

    // Pre-stepped schedule: consume call 0 beforehand so `callee_call_counts["ext_hop"] == 1`,
    // and arm `set_callee_panic_on_call("ext_hop", 1)` — the VERY FIRST call inside the trial
    // MUST panic in BOTH `verify_spec_postcondition_against_schedule` AND compiled `rustc`!
    let mut prestepped_panic_sched = clean_sched.clone();
    prestepped_panic_sched.set_callee_panic_on_call("ext_hop", 1);
    let _ = prestepped_panic_sched.next_action("ext_hop", 0);

    // Mismatched `callee_return_sizes` (`2` bytes vs `u32` 4 bytes) must ALSO trap in both!
    let mut mismatched_size_sched = EnvSchedule::new();
    mismatched_size_sched.push_callee_response("ext_hop", 5u32.to_le_bytes().to_vec());
    mismatched_size_sched.register_callee_return_size("ext_hop", 2);

    let trials = vec![
        (make_args(10, 99, 0, 77), Some(clean_sched.clone())),
        (make_args(10, 99, 255, 77), Some(clean_sched.clone())),
        (make_args(10, 99, 1, 77), Some(clean_sched.clone())),
        (make_args(10, 99, 25, 77), Some(clean_sched)),
        (make_args(10, 99, 1, 77), Some(prestepped_panic_sched)),
        (make_args(10, 99, 1, 77), Some(mismatched_size_sched)),
    ];

    let report = probe
        .verify_spec_postcondition_batch(&trials)
        .expect("verify ep2-A1 parity batch");
    assert_eq!(report.verdicts[0], SpecPostconditionVerdict::VerifiedHold);
    assert_eq!(report.verdicts[1], SpecPostconditionVerdict::VerifiedHold);
    assert_eq!(report.verdicts[2], SpecPostconditionVerdict::VerifiedHold);
    assert_eq!(report.verdicts[3], SpecPostconditionVerdict::VerifiedHold);
    assert!(matches!(
        &report.verdicts[4],
        SpecPostconditionVerdict::PanicOrTrap { .. }
    ));
    assert!(matches!(
        &report.verdicts[5],
        SpecPostconditionVerdict::PanicOrTrap { .. }
    ));

    let exe_src = probe
        .synthesize_rust_executable_harness_with_schedules(&trials)
        .expect("synthesize ep2-A1 executable harness");
    assert!(!contains_unsafe_token(&exe_src));
    let native_lines = compile_and_run_spec_harness("ep2_a1_lockstep_parity", &exe_src);
    assert_eq!(
        native_lines,
        vec![
            "TRIAL:0:HOLD",
            "TRIAL:1:HOLD",
            "TRIAL:2:HOLD",
            "TRIAL:3:HOLD",
            "TRIAL:4:TRAP",
            "TRIAL:5:TRAP",
        ]
    );
}

#[test]
fn ep2_b2_lockstep_parity_on_old_match_shadowing_neg_patterns_enums_aliases_recursion_and_deep_prestep()
{
    use anneal_difftest::{
        EnumVariantLayout, SpecContractOracleProbe, SpecExternalCallee, SpecParamBinding,
        SpecPostconditionVerdict, SpecViolationKind,
    };

    let i32_layout = LayoutSpec::Scalar(ScalarLayout::i32());
    let u32_layout = LayoutSpec::Scalar(ScalarLayout::u32());
    let usize_layout = LayoutSpec::Scalar(ScalarLayout::unsigned(8));
    let maybe_word_layout = LayoutSpec::Enum {
        name: "MaybeWord".to_string(),
        total_size: 8,
        tag_offset: 0,
        tag_size: 1,
        variants: vec![
            EnumVariantLayout {
                name: "Empty".to_string(),
                discriminant: 0,
                payload_offset: 4,
                payload: None,
            },
            EnumVariantLayout {
                name: "Ready".to_string(),
                discriminant: 1,
                payload_offset: 4,
                payload: Some(Box::new(u32_layout.clone())),
            },
        ],
    };
    let state_layout = LayoutSpec::Struct {
        name: "EnumState".to_string(),
        total_size: 24,
        fields: vec![
            FieldLayout {
                name: "status".to_string(),
                offset: 0,
                layout: maybe_word_layout.clone(),
            },
            FieldLayout {
                name: "cursor".to_string(),
                offset: 8,
                layout: usize_layout.clone(),
            },
            FieldLayout {
                name: "active".to_string(),
                offset: 16,
                layout: u32_layout.clone(),
            },
        ],
    };
    let pair_usize_layout = LayoutSpec::Tuple {
        total_size: 16,
        elements: vec![(0, usize_layout.clone()), (8, usize_layout)],
    };

    // Exercises all 6 `ep2-B2` adversarial findings end-to-end against `rustc -D warnings`:
    // 1. `old(match ... { x => ... })` & `old(if let MaybeWord::Ready(x) = ...)` shadowing `x: i32`,
    // 2. Negative untyped `match` patterns (`-5 | -1`, `-4..=-2`), slice rest patterns, & `if let` chains,
    // 3. Target self-recursion (`recursive_enum_probe(..., hops - 1)`),
    // 4. `type Word = u32;`, `usize` struct/tuple/array literal synthesis (`(usize, usize)`),
    // 5. Pre-stepped `EnvSchedule` > 256 calls (`300` pre-steps with `panic_on_call = 2` already passed
    //    vs `panic_on_call = 300` firing on call 0 of the trial!),
    // 6. `#[repr(C, u8)]` `Enum` inactive-payload poison frame safety vs real variant mutation (`FRAME`).
    let probe = SpecContractOracleProbe::new(
        "recursive_enum_probe",
        vec![
            SpecParamBinding::mut_ref("st", "EnumState", state_layout)
                .with_frame_preserved_fields(["status", "cursor"]),
            SpecParamBinding::by_value("x", "i32", i32_layout),
            SpecParamBinding::by_value("hops", "Word", u32_layout.clone()),
            SpecParamBinding::by_value("bounds", "(usize, usize)", pair_usize_layout),
        ],
        "Word",
        u32_layout,
        "if hops > 0u32 {\n    \
             st.active = st.active + 1u32;\n    \
             return recursive_enum_probe(st, x, hops - 1u32, bounds);\n\
         }\n\
         let ext_ev: MaybeWord = ext_poll(bounds.0);\n\
         if x == -99i32 {\n    \
             st.status = MaybeWord::Ready(77u32);\n\
         } else if let MaybeWord::Empty = st.status {\n    \
             st.status = MaybeWord::Empty;\n\
         }\n\
         let env_bonus: Word = match ext_ev {\n    \
             MaybeWord::Empty => 1u32,\n    \
             MaybeWord::Ready(v) => v & 7u32,\n\
         };\n\
         let pat_delta: Word = match x {\n    \
             -5 | -1 => 9u32,\n    \
             -4..=-2 => 4u32,\n    \
             0..=8 => (x as Word) + 2u32,\n    \
             _ => 0u32,\n\
         };\n\
         let window: [usize; 3] = [bounds.0, st.cursor, bounds.1];\n\
         let win_bonus: Word = match window {\n    \
             [lo, .., hi] if lo <= hi && hi <= 32usize => (hi - lo) as Word,\n    \
             _ => 0u32,\n\
         };\n\
         st.active = st.active + env_bonus + pat_delta + win_bonus;\n\
         st.active",
    )
    .with_type_defs(
        "pub type Word = u32;\n\
         #[repr(C, u8)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub enum MaybeWord { Empty = 0, Ready(Word) = 1 }\n\
         #[repr(C)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub struct EnumState { pub status: MaybeWord, pub cursor: usize, pub active: Word }",
    )
    .with_external_callee(SpecExternalCallee::new(
        "ext_poll",
        ["usize"],
        "MaybeWord",
        maybe_word_layout,
    ))
    .with_requires(
        "bounded",
        "hops <= 3u32 && st.active <= 500u32 && st.cursor <= 16usize && bounds.0 <= 16usize && bounds.1 <= 16usize",
    )
    .with_ensures(
        "shadowed_old_match_and_if_let",
        "old(match st.active { x if x > 0u32 => x, _ => 0u32 }) == old(st.active) \
         && old(if let MaybeWord::Ready(x) = st.status && x > 0u32 { x } else { 0u32 }) <= 1000u32",
    )
    .with_ensures("strict_progress", "result > old(st.active)");

    let make_trial = |disc: u8, payload: u32, x: i32, hops: u32| -> Vec<u8> {
        let mut b = vec![0xEEu8; 48];
        b[0] = disc;
        b[4..8].copy_from_slice(&payload.to_le_bytes());
        b[8..16].copy_from_slice(&4u64.to_le_bytes()); // cursor = 4usize
        b[16..20].copy_from_slice(&10u32.to_le_bytes()); // active = 10
        b[24..28].copy_from_slice(&x.to_le_bytes());
        b[28..32].copy_from_slice(&hops.to_le_bytes());
        b[32..40].copy_from_slice(&2u64.to_le_bytes()); // bounds.0 = 2usize
        b[40..48].copy_from_slice(&7u64.to_le_bytes()); // bounds.1 = 7usize
        b
    };

    let mut ready_bytes = vec![0xCCu8; 8];
    ready_bytes[0] = 1u8;
    ready_bytes[4..8].copy_from_slice(&6u32.to_le_bytes());
    let mut base_sched = EnvSchedule::new().with_callee_return_size("ext_poll", 8);
    base_sched.set_callee_default("ext_poll", ready_bytes);

    // Pre-stepped 300 times (> 256!) AFTER `panic_on_call = 2` already passed -> MUST HOLD, NOT TRAP!
    let mut passed_panic_sched = base_sched.clone();
    passed_panic_sched.set_callee_panic_on_call("ext_poll", 2);
    for g in 0..300usize {
        let _ = passed_panic_sched.next_action("ext_poll", g);
    }

    // Pre-stepped 300 times (> 256!) WITH `panic_on_call = 300` -> MUST TRAP on trial call 0!
    let mut deep_active_panic_sched = base_sched.clone();
    deep_active_panic_sched.set_callee_panic_on_call("ext_poll", 300);
    for g in 0..300usize {
        let _ = deep_active_panic_sched.next_action("ext_poll", g);
    }

    let trials = vec![
        // Trial 0: `Empty` with `0xEE` poison in payload + `x = -5` + `hops = 2` + passed deep panic -> HOLD
        (make_trial(0, 0xDEAD_BEEF, -5, 2), Some(passed_panic_sched)),
        // Trial 1: `Ready(15)` + `x = -3` (negative range `-4..=-2`) + `hops = 1` -> HOLD
        (make_trial(1, 15, -3, 1), Some(base_sched.clone())),
        // Trial 2: `Empty` mutated to `Ready(77)` when `x == -99` -> FRAME:st.status
        (make_trial(0, 0, -99, 0), Some(base_sched)),
        // Trial 3: Pre-stepped 300 calls hitting `callee_panic_on_call = 300` -> TRAP
        (make_trial(1, 9, 3, 0), Some(deep_active_panic_sched)),
    ];

    let report = probe
        .verify_spec_postcondition_batch(&trials)
        .expect("verify ep2-B2 parity batch");
    assert_eq!(report.verdicts[0], SpecPostconditionVerdict::VerifiedHold);
    assert_eq!(report.verdicts[1], SpecPostconditionVerdict::VerifiedHold);
    assert!(matches!(
        &report.verdicts[2],
        SpecPostconditionVerdict::PostconditionViolation {
            kind: SpecViolationKind::FrameCondition { param, field },
            ..
        } if param == "st" && field == "status"
    ));
    assert!(matches!(
        &report.verdicts[3],
        SpecPostconditionVerdict::PanicOrTrap { .. }
    ));

    let exe_src = probe
        .synthesize_rust_executable_harness_with_schedules(&trials)
        .expect("synthesize ep2-B2 executable harness");
    assert!(!contains_unsafe_token(&exe_src));
    let native_lines = compile_and_run_spec_harness("ep2_b2_lockstep_parity", &exe_src);
    assert_eq!(
        native_lines,
        vec![
            "TRIAL:0:HOLD",
            "TRIAL:1:HOLD",
            "TRIAL:2:FRAME:st.status",
            "TRIAL:3:TRAP",
        ]
    );
}

#[test]
fn ep2_a2_lockstep_parity_on_for_loops_multifield_enums_const_patterns_let_else_nonzero_and_o1_panic()
{
    use anneal_difftest::{
        EnumVariantLayout, SpecContractOracleProbe, SpecExternalCallee, SpecParamBinding,
        SpecPostconditionVerdict, SpecViolationKind,
    };

    let i32_layout = LayoutSpec::Scalar(ScalarLayout::i32());
    let u32_layout = LayoutSpec::Scalar(ScalarLayout::u32());
    let nz_u32_layout =
        LayoutSpec::Scalar(ScalarLayout::with_valid_range(4, false, 1, u32::MAX as u128));

    let both_payload = LayoutSpec::Tuple {
        total_size: 8,
        elements: vec![(0, u32_layout.clone()), (4, u32_layout.clone())],
    };
    let move_payload = LayoutSpec::Struct {
        name: "Move".to_string(),
        total_size: 8,
        fields: vec![
            FieldLayout {
                name: "dx".to_string(),
                offset: 0,
                layout: i32_layout.clone(),
            },
            FieldLayout {
                name: "dy".to_string(),
                offset: 4,
                layout: i32_layout.clone(),
            },
        ],
    };
    let action_layout = LayoutSpec::Enum {
        name: "TaggedAction".to_string(),
        total_size: 12,
        tag_offset: 0,
        tag_size: 1,
        variants: vec![
            EnumVariantLayout {
                name: "Idle".to_string(),
                discriminant: 0,
                payload_offset: 4,
                payload: None,
            },
            EnumVariantLayout {
                name: "Both".to_string(),
                discriminant: 1,
                payload_offset: 4,
                payload: Some(Box::new(both_payload)),
            },
            EnumVariantLayout {
                name: "Move".to_string(),
                discriminant: 2,
                payload_offset: 4,
                payload: Some(Box::new(move_payload)),
            },
        ],
    };
    let state_layout = LayoutSpec::Struct {
        name: "ActionState".to_string(),
        total_size: 16,
        fields: vec![
            FieldLayout {
                name: "act".to_string(),
                offset: 0,
                layout: action_layout.clone(),
            },
            FieldLayout {
                name: "total".to_string(),
                offset: 12,
                layout: u32_layout.clone(),
            },
        ],
    };

    // Exercises all 7 `ep2-A2` findings end-to-end against `rustc -D warnings`:
    // 1. `for` loops over half-open/closed ranges and `[T; N]` arrays (`for &item in &arr`),
    // 2. Multi-field tuple-variant (`TaggedAction::Both(a, b)`) and struct-variant
    //    (`TaggedAction::Move { dx, dy }`) literal synthesis (`rustc` E0061 fix) + evaluation,
    // 3. Top-level `const MAGIC_KEY: Word = 42` in expressions AND `match` patterns
    //    (proving `key != 42` does NOT silently bind `MAGIC_KEY` as a wildcard variable!)
    //    + `type` aliases (`ActionAlias`, `StateAlias`) + `core::num::NonZeroU32` (`.get()`),
    // 4. `let ... else` diverging statements in both body and `old(...)` + `[first, .., last]`
    //    and `(lo, .., hi)` rest destructuring in `let` bindings,
    // 5. `old(scratch_bump(st))` invoking an `&mut StateAlias` helper on an isolated scratch
    //    clone without mutating `old(st.total)` or failing `rustc` borrow/type checking,
    // 6. O(1) `remaining_calls_until_callee_panic` on `callee_panic_on_call = usize::MAX`
    //    after `300` pre-steps (completing instantaneously with 1-for-1 native parity).
    let probe = SpecContractOracleProbe::new(
        "action_parity_probe",
        vec![
            SpecParamBinding::mut_ref("st", "StateAlias", state_layout)
                .with_frame_preserved_fields(["act"]),
            SpecParamBinding::by_value("key", "Word", u32_layout.clone()),
            SpecParamBinding::by_value("scale", "core::num::NonZeroU32", nz_u32_layout),
            SpecParamBinding::by_value("fallback", "i32", i32_layout),
        ],
        "Word",
        u32_layout,
        "if key == 999u32 {\n    \
             st.act = ActionAlias::Move { dx: 1i32, dy: 2i32 };\n\
         }\n\
         let key_tag: Word = match key {\n    \
             MAGIC_KEY => 40u32,\n    \
             _ => 2u32,\n\
         };\n\
         let payload_sum: Word = match st.act {\n    \
             ActionAlias::Both(a, b) => a + b,\n    \
             ActionAlias::Move { dx, dy } => (dx.wrapping_abs() as u32) + (dy.wrapping_abs() as u32),\n    \
             ActionAlias::Idle => {\n        \
                 let ActionAlias::Both(v, ..) = st.act else {\n            \
                     return st.total + (fallback as Word);\n        \
                 };\n        \
                 v\n    \
             }\n\
         };\n\
         let mut acc: Word = 0u32;\n\
         for step_i in 0u32..=2u32 {\n    \
             acc += step_i;\n\
         }\n\
         let weights: [Word; 4] = [1, 2, 3, 4];\n\
         let [w_first, .., w_last]: [Word; 4] = weights;\n\
         let (tup_a, .., tup_b) = (w_first, 77u32, w_last);\n\
         for &w in &weights {\n    \
             acc += w;\n\
         }\n\
         let ext_ev: ActionAlias = ext_next_action(key);\n\
         let ext_delta: Word = match ext_ev {\n    \
             ActionAlias::Both(p, q) => p + q,\n    \
             ActionAlias::Move { dx, dy } => (dx.saturating_abs() as u32) + (dy.saturating_abs() as u32),\n    \
             ActionAlias::Idle => 0u32,\n\
         };\n\
         st.total = st.total + key_tag + payload_sum + acc + tup_a + tup_b + scale.get() + ext_delta;\n\
         st.total",
    )
    .with_type_defs(
        "pub type Word = u32;\n\
         pub const MAGIC_KEY: Word = 42;\n\
         #[repr(C, u8)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub enum TaggedAction {\n    \
             Idle = 0,\n    \
             Both(Word, Word) = 1,\n    \
             Move { dx: i32, dy: i32 } = 2,\n\
         }\n\
         pub type ActionAlias = TaggedAction;\n\
         #[repr(C)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub struct ActionState { pub act: TaggedAction, pub total: Word }\n\
         pub type StateAlias = ActionState;\n\
         pub fn scratch_bump(s: &mut StateAlias) -> Word {\n    \
             s.total += 5u32;\n    \
             s.total\n\
         }",
    )
    .with_external_callee(SpecExternalCallee::new(
        "ext_next_action",
        ["Word"],
        "ActionAlias",
        action_layout,
    ))
    .with_requires(
        "valid_domain",
        "scale.get() <= 8u32 && fallback >= 0i32 && fallback <= 50i32",
    )
    .with_ensures(
        "old_mut_scratch_and_const_discrimination",
        "old(scratch_bump(st)) == old(st.total).wrapping_add(5u32) \
         && old((|| { let ActionAlias::Both(v, _) = st.act else { return (fallback as u32) <= 50u32; }; v <= u32::MAX })()) \
         && (key == MAGIC_KEY || key != 42u32)",
    )
    .with_ensures("strict_progress", "result > old(st.total)");

    let make_trial =
        |disc: u8, p0: i32, p1: i32, total: u32, key: u32, nz: u32, fallback: i32| -> Vec<u8> {
            let mut b = vec![0xAAu8; 28];
            b[0] = disc;
            b[4..8].copy_from_slice(&p0.to_le_bytes());
            b[8..12].copy_from_slice(&p1.to_le_bytes());
            b[12..16].copy_from_slice(&total.to_le_bytes());
            b[16..20].copy_from_slice(&key.to_le_bytes());
            b[20..24].copy_from_slice(&nz.to_le_bytes());
            b[24..28].copy_from_slice(&fallback.to_le_bytes());
            b
        };

    let mut both_sched_bytes = vec![0xBBu8; 12];
    both_sched_bytes[0] = 1u8; // Both(3, 4)
    both_sched_bytes[4..8].copy_from_slice(&3u32.to_le_bytes());
    both_sched_bytes[8..12].copy_from_slice(&4u32.to_le_bytes());

    let mut move_sched_bytes = vec![0xCCu8; 12];
    move_sched_bytes[0] = 2u8; // Move { dx: -3, dy: 6 }
    move_sched_bytes[4..8].copy_from_slice(&(-3i32).to_le_bytes());
    move_sched_bytes[8..12].copy_from_slice(&6i32.to_le_bytes());

    let mut sched_o1_max = EnvSchedule::new().with_callee_return_size("ext_next_action", 12);
    sched_o1_max.push_callee_response("ext_next_action", move_sched_bytes);
    sched_o1_max.set_callee_default("ext_next_action", both_sched_bytes.clone());
    sched_o1_max.set_callee_panic_on_call("ext_next_action", usize::MAX);
    for g in 0..300usize {
        let _ = sched_o1_max.next_action("ext_next_action", g);
    }

    let mut base_sched = EnvSchedule::new().with_callee_return_size("ext_next_action", 12);
    let mut move_q_bytes = vec![0xDDu8; 12];
    move_q_bytes[0] = 2u8; // Move { dx: -4, dy: 5 } -> exercises struct-variant literal synthesis in schedule queue!
    move_q_bytes[4..8].copy_from_slice(&(-4i32).to_le_bytes());
    move_q_bytes[8..12].copy_from_slice(&5i32.to_le_bytes());
    base_sched.push_callee_response("ext_next_action", move_q_bytes);
    base_sched.set_callee_default("ext_next_action", both_sched_bytes);

    let trials = vec![
        // Trial 0: `Both(4, 6)` + `key = 7` (!= MAGIC_KEY) + O(1) `usize::MAX` panic after 300 pre-steps -> HOLD
        (make_trial(1, 4, 6, 10, 7, 2, 5), Some(sched_o1_max)),
        // Trial 1: `Move { dx: -2, dy: 8 }` + `key = 42` (== MAGIC_KEY) + queued `Move` struct-variant -> HOLD
        (make_trial(2, -2, 8, 20, 42, 3, 11), Some(base_sched.clone())),
        // Trial 2: `Idle` hits `let ... else { return st.total + 0; }` -> violates `strict_progress`!
        (make_trial(0, 0, 0, 15, 7, 1, 0), Some(base_sched.clone())),
        // Trial 3: `key == 999` mutates framed `st.act` -> FRAME:st.act
        (make_trial(0, 0, 0, 15, 999, 1, 5), Some(base_sched.clone())),
        // Trial 4: `total = u32::MAX - 1` overflows checked `+` in body -> TRAP
        (make_trial(1, 5, 5, u32::MAX - 1, 42, 4, 1), Some(base_sched)),
    ];

    let report = probe
        .verify_spec_postcondition_batch(&trials)
        .expect("verify ep2-A2 parity batch");
    assert_eq!(report.verdicts[0], SpecPostconditionVerdict::VerifiedHold);
    assert_eq!(report.verdicts[1], SpecPostconditionVerdict::VerifiedHold);
    assert!(matches!(
        &report.verdicts[2],
        SpecPostconditionVerdict::PostconditionViolation {
            kind: SpecViolationKind::EnsuresClause { label, .. },
            ..
        } if label == "strict_progress"
    ));
    assert!(matches!(
        &report.verdicts[3],
        SpecPostconditionVerdict::PostconditionViolation {
            kind: SpecViolationKind::FrameCondition { param, field },
            ..
        } if param == "st" && field == "act"
    ));
    assert!(matches!(
        &report.verdicts[4],
        SpecPostconditionVerdict::PanicOrTrap { .. }
    ));

    let exe_src = probe
        .synthesize_rust_executable_harness_with_schedules(&trials)
        .expect("synthesize ep2-A2 executable harness");
    assert!(!contains_unsafe_token(&exe_src));
    let native_lines = compile_and_run_spec_harness("ep2_a2_lockstep_parity", &exe_src);
    assert_eq!(
        native_lines,
        vec![
            "TRIAL:0:HOLD",
            "TRIAL:1:HOLD",
            "TRIAL:2:VIOLATION:strict_progress",
            "TRIAL:3:FRAME:st.act",
            "TRIAL:4:TRAP",
        ]
    );
}

#[test]
fn ep2_b3_lockstep_parity_on_for_mut_writeback_nonzero_min_old_block_mut_pure_spec_and_qualified_schedules()
{
    use anneal_difftest::{
        EnvScheduledWriteStep, SpecContractOracleProbe, SpecExecPhase, SpecExternalCallee,
        SpecParamBinding, SpecPostconditionVerdict, SpecViolationKind, WriteChainCoverageBound,
    };

    let u32_layout = LayoutSpec::Scalar(ScalarLayout::u32());
    let nz_u32_layout =
        LayoutSpec::Scalar(ScalarLayout::with_valid_range(4, false, 1, u32::MAX as u128));
    let lanes_layout = LayoutSpec::Array {
        elem: Box::new(u32_layout.clone()),
        elem_stride: 4,
        len: 3,
    };
    let state_layout = LayoutSpec::Struct {
        name: "LaneState".to_string(),
        total_size: 20,
        fields: vec![
            FieldLayout {
                name: "lanes".to_string(),
                offset: 0,
                layout: lanes_layout,
            },
            FieldLayout {
                name: "total".to_string(),
                offset: 12,
                layout: u32_layout.clone(),
            },
            FieldLayout {
                name: "framed".to_string(),
                offset: 16,
                layout: u32_layout.clone(),
            },
        ],
    };

    // Exercises all 6 `ep2-B3` adversarial findings in lockstep with `rustc -D warnings`:
    // 1. `for slot in &mut st.lanes { *slot += 2u32; }` and `for (a, b) in &mut pairs { *a += *b; }`
    //    write back in-place array mutations (while `for &mut mut c in &mut st.lanes` copies without writeback),
    // 2. `NonZeroU32::MIN` (`1`, NOT `0`!) via both `NzWord::MIN` and 4-segment
    //    `core::num::NonZeroU32::MIN` in expressions AND `match` patterns,
    // 3. `requires` scratch `&mut` mutation isolation (`scratch_bump(st) >= 5u32` does NOT mutate
    //    Phase-2 `st.total`) + `old({ st.total += 3u32; (scratch_bump)(st) })` sequential scratch mutations,
    // 4. Impure external call `ext_read()` inside `ensures` (`poison_spec == 1u32`) traps (`TRAP`)
    //    in BOTH `verify_spec_postcondition_against_schedule` AND compiled `rustc` (`__AnnealPureSpecGuard`),
    // 5. Module-qualified `EnvSchedule` keys (`"sensor_mod::ext_read"`) for queue, default,
    //    return-size validation, and pre-stepped `callee_panic_on_call`,
    // 6. `WriteChainCoverageBound` unwind cutoff halting after `PanicOnCall(0)`.
    let probe = SpecContractOracleProbe::new(
        "ep2_b3_mut_loop_nonzero_parity",
        vec![
            SpecParamBinding::mut_ref("st", "LaneState", state_layout)
                .with_frame_preserved_fields(["framed"]),
            SpecParamBinding::by_value("scale", "NzWord", nz_u32_layout),
            SpecParamBinding::by_value("poison_spec", "u32", u32_layout.clone()),
        ],
        "u32",
        u32_layout.clone(),
        "if poison_spec == 77u32 {\n    \
             st.framed += 1u32;\n\
         }\n\
         for &mut mut copied_lane in &mut st.lanes {\n    \
             copied_lane += 100u32;\n    \
             let _ = copied_lane;\n\
         }\n\
         for slot in &mut st.lanes {\n    \
             *slot += 2u32;\n    \
             if *slot > 900u32 { break; }\n\
         }\n\
         let mut pairs: [(u32, u32); 2] = [(1u32, 2u32), (3u32, 4u32)];\n\
         for (a, b) in &mut pairs {\n    \
             *a += *b;\n\
         }\n\
         let nz_tag: u32 = match scale {\n    \
             core::num::NonZeroU32::MIN => NzWord::MIN.get() + core::num::NonZeroU32::MIN.get(),\n    \
             _ => scale.get(),\n\
         };\n\
         let max_check: u32 = match st.total {\n    \
             core::primitive::u32::MAX => 0u32,\n    \
             _ => 1u32,\n\
         };\n\
         let ext_v: u32 = ext_read();\n\
         st.total = st.total + st.lanes[0] + st.lanes[1] + st.lanes[2] + pairs[0].0 + pairs[1].0 + nz_tag + max_check + ext_v;\n\
         st.total",
    )
    .with_type_defs(
        "pub type NzWord = core::num::NonZeroU32;\n\
         #[repr(C)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub struct LaneState { pub lanes: [u32; 3], pub total: u32, pub framed: u32 }\n\
         pub fn scratch_bump(s: &mut LaneState) -> u32 {\n    \
             s.total += 5u32;\n    \
             s.total\n\
         }",
    )
    .with_external_callee(SpecExternalCallee::new(
        "ext_read",
        std::iter::empty::<&str>(),
        "u32",
        u32_layout,
    ))
    .with_requires(
        "requires_scratch_isolated",
        "st.total <= 500u32 && scratch_bump(st) >= 5u32 \
         && st.lanes[0] <= 100u32 && st.lanes[1] <= 100u32 && st.lanes[2] <= 100u32 \
         && scale.get() <= 10u32",
    )
    .with_ensures(
        "old_block_mut_and_pure_ensures_guard",
        "old({ st.total += 3u32; (scratch_bump)(st) }) == old(st.total) + 8u32 \
         && st.lanes[0] == old(st.lanes[0]) + 2u32 \
         && st.lanes[1] == old(st.lanes[1]) + 2u32 \
         && st.lanes[2] == old(st.lanes[2]) + 2u32 \
         && (poison_spec != 1u32 || ext_read() > 0u32)",
    )
    .with_ensures(
        "exact_post_sum",
        "poison_spec == 2u32 || (scale.get() == 1u32 && result == old(st.total) + old(st.lanes[0]) + old(st.lanes[1]) + old(st.lanes[2]) + 6u32 + 10u32 + 2u32 + 1u32 + 4u32) \
         || (scale.get() > 1u32 && result > old(st.total))",
    );

    let make_trial = |l0: u32, l1: u32, l2: u32, total: u32, scale: u32, poison_spec: u32| -> Vec<u8> {
        let mut b = Vec::with_capacity(28);
        b.extend_from_slice(&l0.to_le_bytes());
        b.extend_from_slice(&l1.to_le_bytes());
        b.extend_from_slice(&l2.to_le_bytes());
        b.extend_from_slice(&total.to_le_bytes());
        b.extend_from_slice(&55u32.to_le_bytes()); // framed = 55
        b.extend_from_slice(&scale.to_le_bytes());
        b.extend_from_slice(&poison_spec.to_le_bytes());
        b
    };

    let mut qual_sched = EnvSchedule::new().with_callee_return_size("sensor_mod::ext_read", 4);
    qual_sched.push_callee_response("sensor_mod::ext_read", 4u32.to_le_bytes().to_vec());
    qual_sched.set_callee_default("sensor_mod::ext_read", 4u32.to_le_bytes().to_vec());

    let mut qual_panic_sched = qual_sched.clone();
    qual_panic_sched.set_callee_panic_on_call("sensor_mod::ext_read", 1);
    let _ = qual_panic_sched.next_action("sensor_mod::ext_read", 0); // 1 call served -> next panics!

    let trials = vec![
        // Trial 0: `scale = 1` (`NonZeroU32::MIN`), `poison_spec = 0`, module-qualified schedule -> HOLD
        (make_trial(1, 2, 3, 10, 1, 0), Some(qual_sched.clone())),
        // Trial 1: `scale = 20` fails `requires` (`scale.get() <= 10`) -> FILTERED
        (make_trial(1, 2, 3, 10, 20, 0), Some(qual_sched.clone())),
        // Trial 2: `poison_spec = 1` calls external `ext_read()` inside `ensures` -> TRAP in both!
        (make_trial(1, 2, 3, 10, 1, 1), Some(qual_sched.clone())),
        // Trial 3: `poison_spec = 77` mutates framed `st.framed` -> FRAME:st.framed
        (make_trial(1, 2, 3, 10, 3, 77), Some(qual_sched.clone())),
        // Trial 4: pre-stepped module-qualified `callee_panic_on_call("sensor_mod::ext_read", 1)` -> TRAP
        (make_trial(1, 2, 3, 10, 3, 0), Some(qual_panic_sched)),
        // Trial 5: queued `9u32` breaks `exact_post_sum` (expects `+ 4u32` when `scale == 1 && poison_spec == 0`) -> VIOLATION:exact_post_sum
        (
            make_trial(1, 2, 3, 10, 1, 0),
            Some({
                let mut bad_q = EnvSchedule::new().with_callee_return_size("sensor_mod::ext_read", 4);
                bad_q.push_callee_response("sensor_mod::ext_read", 9u32.to_le_bytes().to_vec());
                bad_q
            }),
        ),
    ];

    let report = probe
        .verify_spec_postcondition_batch(&trials)
        .expect("verify ep2-B3 parity batch");
    assert_eq!(report.verdicts[0], SpecPostconditionVerdict::VerifiedHold);
    assert!(matches!(
        &report.verdicts[1],
        SpecPostconditionVerdict::VacuouslyFiltered { .. }
    ));
    assert!(matches!(
        &report.verdicts[2],
        SpecPostconditionVerdict::PanicOrTrap {
            phase: SpecExecPhase::Ensures,
            ..
        }
    ));
    assert!(matches!(
        &report.verdicts[3],
        SpecPostconditionVerdict::PostconditionViolation {
            kind: SpecViolationKind::FrameCondition { param, field },
            ..
        } if param == "st" && field == "framed"
    ));
    assert!(matches!(
        &report.verdicts[4],
        SpecPostconditionVerdict::PanicOrTrap {
            phase: SpecExecPhase::Body,
            ..
        }
    ));
    assert!(matches!(
        &report.verdicts[5],
        SpecPostconditionVerdict::PostconditionViolation {
            kind: SpecViolationKind::EnsuresClause { label, .. },
            ..
        } if label == "exact_post_sum"
    ));

    let exe_src = probe
        .synthesize_rust_executable_harness_with_schedules(&trials)
        .expect("synthesize ep2-B3 executable harness");
    assert!(!contains_unsafe_token(&exe_src));
    let native_lines = compile_and_run_spec_harness("ep2_b3_lockstep_parity", &exe_src);
    assert_eq!(
        native_lines,
        vec![
            "TRIAL:0:HOLD",
            "TRIAL:1:FILTERED",
            "TRIAL:2:TRAP",
            "TRIAL:3:FRAME:st.framed",
            "TRIAL:4:TRAP",
            "TRIAL:5:VIOLATION:exact_post_sum",
        ]
    );

    // Module-qualified `EnvSchedule` keys (`"sensor_mod::ext_read"`) resolve in
    // `WriteChainCoverageBound::observe_env_schedule_with_layouts` when planned steps
    // reference short `"ext_read"`:
    let mut walk_bound = WriteChainCoverageBound::new(2, 2);
    assert_eq!(
        walk_bound.observe_env_schedule_with_layouts(
            &qual_sched,
            &probe.external_callee_layout_map(),
            &[
                EnvScheduledWriteStep::new("ext_read", "s0", std::iter::empty::<&str>()),
                EnvScheduledWriteStep::new("ext_read", "s1", ["s0"]),
            ],
        ),
        2
    );
    assert_eq!(walk_bound.broken_env_links(), 0);
    assert!(walk_bound.is_depth_certified());
}

#[test]
fn ep2_a3_lockstep_parity_on_local_mut_aliases_mixed_sched_keys_old_refs_clause_isolation_and_self_paths()
{
    use anneal_difftest::{
        EnumVariantLayout, EnvScheduledWriteStep, SpecContractOracleProbe, SpecExecPhase,
        SpecExternalCallee, SpecParamBinding, SpecPostconditionVerdict, SpecViolationKind,
        WriteChainCoverageBound,
    };

    let u32_layout = LayoutSpec::Scalar(ScalarLayout::u32());
    let lanes_layout = LayoutSpec::Array {
        elem: Box::new(u32_layout.clone()),
        elem_stride: 4,
        len: 3,
    };
    let delta_layout = LayoutSpec::Enum {
        name: "MaybeDelta".to_string(),
        total_size: 8,
        tag_offset: 0,
        tag_size: 1,
        variants: vec![
            EnumVariantLayout {
                name: "Empty".to_string(),
                discriminant: 0,
                payload_offset: 4,
                payload: None,
            },
            EnumVariantLayout {
                name: "Add".to_string(),
                discriminant: 1,
                payload_offset: 4,
                payload: Some(Box::new(u32_layout.clone())),
            },
        ],
    };
    let state_layout = LayoutSpec::Struct {
        name: "AliasState".to_string(),
        total_size: 20,
        fields: vec![
            FieldLayout {
                name: "lanes".to_string(),
                offset: 0,
                layout: lanes_layout,
            },
            FieldLayout {
                name: "total".to_string(),
                offset: 12,
                layout: u32_layout.clone(),
            },
            FieldLayout {
                name: "framed".to_string(),
                offset: 16,
                layout: u32_layout.clone(),
            },
        ],
    };

    // Exercises all 6 `ep2-A3` fixes in lockstep against compiled `rustc --edition=2024 -D warnings`:
    // 1. Local `&mut` place aliases (`let r = &mut st.total;`, tuple `(&mut a, &mut b)`,
    //    rebinding `rebind_ref = &mut st.lanes[2];`, lexical shadowing, `for whole @ (_, b)`,
    //    and `for &mut ref mut lane_ref`),
    // 2. Action-first `resolve_sched_callee_key` when `callee_return_sizes` uses short `"ext_read"`
    //    while `callee_queues` uses module-qualified `"sensor_mod::ext_read"` + cross-key size mismatch,
    // 3. Reference-returning `old(&st.total) == old(read_total_ref(st))` alongside mutating
    //    `old(self::scratch_bump(st))` + per-clause `requires[i]` / `ensures[i]` scratch isolation,
    // 4. `self::` / `crate::` module-root paths across constants, enums, structs, aliases, and helpers,
    // 5. `NonZeroU32` zero-payload validation against `ret_rust_ty` ONLY when invoked (not during staging!),
    // 6. `WriteChainCoverageBound::observe_env_schedule_until_unwind_with_layouts` single-trial cutoff.
    let probe = SpecContractOracleProbe::new(
        "ep2_a3_alias_ref_and_sched_parity",
        vec![
            SpecParamBinding::mut_ref("st", "self::StateAlias", state_layout)
                .with_frame_preserved_fields(["framed"]),
            SpecParamBinding::by_value("mode", "u32", u32_layout.clone()),
            SpecParamBinding::by_value("seed_delta", "self::MaybeDelta", delta_layout),
        ],
        "u32",
        u32_layout.clone(),
        "if mode == 77u32 {\n    \
             let f_ref = &mut st.framed;\n    \
             *f_ref += 1u32;\n\
         }\n\
         let r_tot = &mut st.total;\n\
         *r_tot += 5u32;\n\
         {\n    \
             let r_tot: u32 = 999u32;\n    \
             let _ = r_tot;\n\
         }\n\
         *r_tot += 1u32;\n\
         let (l0_ref, tot_ref) = (&mut st.lanes[0], &mut st.total);\n\
         *l0_ref += 2u32;\n\
         *tot_ref += 3u32;\n\
         let mut rebind_ref = &mut st.lanes[0];\n\
         *rebind_ref += 1u32;\n\
         rebind_ref = &mut st.lanes[2];\n\
         *rebind_ref += 4u32;\n\
         for &mut ref mut lane_ref in &mut st.lanes {\n    \
             *lane_ref += 1u32;\n\
         }\n\
         let mut pairs: [(u32, u32); 2] = [(1u32, 2u32), (3u32, 4u32)];\n\
         for whole @ &mut (a, _) in &mut pairs {\n    \
             whole.1 += a;\n\
         }\n\
         for &mut (_, ref mut b) in &mut pairs {\n    \
             *b += 10u32;\n\
         }\n\
         let d: crate::MaybeDelta = if mode == 0u32 {\n    \
             crate::MaybeDelta::Empty\n\
         } else {\n    \
             self::MaybeDelta::Add(self::MAGIC_BONUS)\n\
         };\n\
         let seed_bonus: u32 = match seed_delta {\n    \
             crate::MaybeDelta::Empty => 0u32,\n    \
             self::MaybeDelta::Add(sv) => sv,\n\
         };\n\
         let bonus: u32 = match d {\n    \
             self::MaybeDelta::Empty => seed_bonus,\n    \
             crate::MaybeDelta::Add(v) => v + seed_bonus,\n\
         };\n\
         let ext_v: u32 = self::ext_read();\n\
         let nz_extra: u32 = if mode == 2u32 { ext_nz().get() } else { 0u32 };\n\
         st.total = st.total + st.lanes[0] + st.lanes[1] + st.lanes[2] + pairs[0].1 + pairs[1].1 + bonus + ext_v + nz_extra;\n\
         st.total",
    )
    .with_type_defs(
        "pub const MAGIC_BONUS: u32 = 7;\n\
         #[repr(C, u8)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub enum MaybeDelta { Empty = 0, Add(u32) = 1 }\n\
         #[repr(C)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub struct AliasState { pub lanes: [u32; 3], pub total: u32, pub framed: u32 }\n\
         pub type StateAlias = AliasState;\n\
         pub fn read_total_ref(s: &AliasState) -> &u32 { &s.total }\n\
         pub fn scratch_bump(s: &mut AliasState) -> u32 {\n    \
             s.total += 50u32;\n    \
             s.total\n\
         }",
    )
    .with_external_callee(SpecExternalCallee::new(
        "ext_read",
        std::iter::empty::<&str>(),
        "u32",
        u32_layout.clone(),
    ))
    .with_external_callee(SpecExternalCallee::new(
        "ext_nz",
        std::iter::empty::<&str>(),
        "core::num::NonZeroU32",
        u32_layout,
    ))
    .with_requires("req_scratch_0", "self::scratch_bump(st) == st.total")
    .with_requires("req_isolated_1", "st.total <= 20u32")
    .with_ensures(
        "old_shared_refs_and_ens_scratch_0",
        "old(&st.total) == old(read_total_ref(st)) \
         && old(self::scratch_bump(st)) == old(st.total) + 50u32 \
         && self::scratch_bump(st) == result + 50u32",
    )
    .with_ensures(
        "ens_isolated_1",
        "mode != 9u32 \
         && st.total == result \
         && st.lanes[0] == old(st.lanes[0]) + 4u32 \
         && st.lanes[1] == old(st.lanes[1]) + 1u32 \
         && st.lanes[2] == old(st.lanes[2]) + 5u32",
    );

    let make_trial = |total: u32, mode: u32| -> Vec<u8> {
        let mut b = Vec::with_capacity(32);
        b.extend_from_slice(&1u32.to_le_bytes()); // lanes[0] = 1
        b.extend_from_slice(&2u32.to_le_bytes()); // lanes[1] = 2
        b.extend_from_slice(&3u32.to_le_bytes()); // lanes[2] = 3
        b.extend_from_slice(&total.to_le_bytes());
        b.extend_from_slice(&88u32.to_le_bytes()); // framed = 88
        b.extend_from_slice(&mode.to_le_bytes());
        let mut delta_bytes = [0u8; 8];
        delta_bytes[0] = 1u8; // MaybeDelta::Add(2)
        delta_bytes[4..8].copy_from_slice(&2u32.to_le_bytes());
        b.extend_from_slice(&delta_bytes);
        b
    };

    // Short `callee_return_sizes["ext_read"] = 4` + module-qualified `callee_queues["sensor_mod::ext_read"]`,
    // plus `0u32` queued on `ext_nz` (`NonZeroU32` with plain `ScalarLayout::u32()`):
    let mut mixed_sched = EnvSchedule::new().with_callee_return_size("ext_read", 4);
    mixed_sched.push_callee_response("sensor_mod::ext_read", 9u32.to_le_bytes().to_vec());
    mixed_sched.push_callee_response("ext_nz", 0u32.to_le_bytes().to_vec());

    // Cross-key return-size mismatch (`callee_return_sizes["ext_read"] = 8` registered after pushing 4-byte `"sensor_mod::ext_read"`):
    let mut bad_sz_sched = EnvSchedule::new();
    bad_sz_sched.push_callee_response("sensor_mod::ext_read", 9u32.to_le_bytes().to_vec());
    bad_sz_sched.push_callee_response("ext_nz", 3u32.to_le_bytes().to_vec());
    bad_sz_sched.register_callee_return_size("ext_read", 8);

    let trials = vec![
        // Trial 0: `total = 10, mode = 1` -> `req_scratch_0` mutates only its own scratch, so `req_isolated_1`
        // still sees `10 <= 20`, `ext_nz` (`0`) is NOT called, `ens_0` scratch does NOT pollute `ens_1` -> HOLD!
        (make_trial(10, 1), Some(mixed_sched.clone())),
        // Trial 1: `total = 25` fails `req_isolated_1` even with `0` staged in `ext_nz` -> FILTERED (no eager unwrap panic!)
        (make_trial(25, 2), Some(mixed_sched.clone())),
        // Trial 2: `total = 10, mode = 2` calls `ext_nz()` which pops invalid `0` for `NonZeroU32` -> TRAP!
        (make_trial(10, 2), Some(mixed_sched.clone())),
        // Trial 3: `total = 10, mode = 77` mutates framed `st.framed` via local `&mut` alias -> FRAME:st.framed!
        (make_trial(10, 77), Some(mixed_sched.clone())),
        // Trial 4: `total = 10, mode = 9` fails `ens_isolated_1` -> VIOLATION:ens_isolated_1!
        (make_trial(10, 9), Some(mixed_sched.clone())),
        // Trial 5: cross-key return-size mismatch (`ext_read` 8B vs `sensor_mod::ext_read` 4B) -> TRAP!
        (make_trial(10, 0), Some(bad_sz_sched)),
    ];

    let report = probe
        .verify_spec_postcondition_batch(&trials)
        .expect("verify ep2-A3 parity batch");
    assert_eq!(report.verdicts[0], SpecPostconditionVerdict::VerifiedHold);
    assert!(matches!(
        &report.verdicts[1],
        SpecPostconditionVerdict::VacuouslyFiltered {
            failed_requires_index: 1,
            ..
        }
    ));
    assert!(matches!(
        &report.verdicts[2],
        SpecPostconditionVerdict::PanicOrTrap {
            phase: SpecExecPhase::Body,
            ..
        }
    ));
    assert!(matches!(
        &report.verdicts[3],
        SpecPostconditionVerdict::PostconditionViolation {
            kind: SpecViolationKind::FrameCondition { param, field },
            ..
        } if param == "st" && field == "framed"
    ));
    assert!(matches!(
        &report.verdicts[4],
        SpecPostconditionVerdict::PostconditionViolation {
            kind: SpecViolationKind::EnsuresClause {
                clause_index: 1,
                label,
            },
            ..
        } if label == "ens_isolated_1"
    ));
    assert!(matches!(
        &report.verdicts[5],
        SpecPostconditionVerdict::PanicOrTrap {
            phase: SpecExecPhase::Body,
            ..
        }
    ));

    let exe_src = probe
        .synthesize_rust_executable_harness_with_schedules(&trials)
        .expect("synthesize ep2-A3 executable harness");
    assert!(!contains_unsafe_token(&exe_src));
    let native_lines = compile_and_run_spec_harness("ep2_a3_lockstep_parity", &exe_src);
    assert_eq!(
        native_lines,
        vec![
            "TRIAL:0:HOLD",
            "TRIAL:1:FILTERED",
            "TRIAL:2:TRAP",
            "TRIAL:3:FRAME:st.framed",
            "TRIAL:4:VIOLATION:ens_isolated_1",
            "TRIAL:5:TRAP",
        ]
    );

    // Mixed short/qualified schedule keys ALSO certify `WriteChainCoverageBound`, whereas
    // `observe_env_schedule_until_unwind_with_layouts` halts immediately on `PanicOnCall(0)`:
    let mut mixed_walk = WriteChainCoverageBound::new(2, 2);
    let mut two_hop_mixed = EnvSchedule::new().with_callee_return_size("ext_read", 4);
    two_hop_mixed.set_callee_default("sensor_mod::ext_read", 9u32.to_le_bytes().to_vec());
    assert_eq!(
        mixed_walk.observe_env_schedule_until_unwind_with_layouts(
            &two_hop_mixed,
            &probe.external_callee_layout_map(),
            &[
                EnvScheduledWriteStep::new("ext_read", "s0", std::iter::empty::<&str>()),
                EnvScheduledWriteStep::new("ext_read", "s1", ["s0"]),
            ],
        ),
        2
    );
    assert!(mixed_walk.is_depth_certified());

    let mut unwind_sched = two_hop_mixed.clone();
    unwind_sched.set_panic_on_call(0);
    let mut unwind_walk = WriteChainCoverageBound::new(2, 2);
    assert_eq!(
        unwind_walk.observe_env_schedule_until_unwind_with_layouts(
            &unwind_sched,
            &probe.external_callee_layout_map(),
            &[
                EnvScheduledWriteStep::new("ext_read", "s0", std::iter::empty::<&str>()),
                EnvScheduledWriteStep::new("ext_read", "s1", std::iter::empty::<&str>()),
                EnvScheduledWriteStep::new("ext_read", "s2", ["s1"]),
            ],
        ),
        0
    );
    assert_eq!(unwind_walk.broken_env_links(), 1);
    assert_eq!(unwind_walk.steps_observed(), 0);
}

#[test]
fn ep2_b4_lockstep_parity_on_shadowed_aliases_mut_ret_helpers_match_mut_enums_and_old_proj_refs() {
    use anneal_difftest::{
        EnumVariantLayout, SpecContractOracleProbe, SpecExecPhase, SpecExternalCallee,
        SpecParamBinding, SpecPostconditionVerdict, SpecViolationKind,
    };

    let u8_layout = LayoutSpec::Scalar(ScalarLayout::u8());
    let u32_layout = LayoutSpec::Scalar(ScalarLayout::u32());
    let bool_layout = LayoutSpec::Scalar(ScalarLayout::bool_layout());
    let padded_item_layout = LayoutSpec::Struct {
        name: "PaddedItem".to_string(),
        total_size: 8,
        fields: vec![
            FieldLayout {
                name: "tag".to_string(),
                offset: 0,
                layout: u8_layout,
            },
            FieldLayout {
                name: "word".to_string(),
                offset: 4,
                layout: u32_layout.clone(),
            },
        ],
    };
    let framed_items_layout = LayoutSpec::Array {
        elem: Box::new(padded_item_layout),
        elem_stride: 8,
        len: 2,
    };
    let lanes_layout = LayoutSpec::Array {
        elem: Box::new(u32_layout.clone()),
        elem_stride: 4,
        len: 3,
    };
    let delta_layout = LayoutSpec::Enum {
        name: "TaggedDelta".to_string(),
        total_size: 12,
        tag_offset: 0,
        tag_size: 1,
        variants: vec![
            EnumVariantLayout {
                name: "Empty".to_string(),
                discriminant: 0,
                payload_offset: 4,
                payload: None,
            },
            EnumVariantLayout {
                name: "Single".to_string(),
                discriminant: 1,
                payload_offset: 4,
                payload: Some(Box::new(u32_layout.clone())),
            },
            EnumVariantLayout {
                name: "Pair".to_string(),
                discriminant: 2,
                payload_offset: 4,
                payload: Some(Box::new(LayoutSpec::Tuple {
                    total_size: 8,
                    elements: vec![(0, u32_layout.clone()), (4, u32_layout.clone())],
                })),
            },
            EnumVariantLayout {
                name: "Shift".to_string(),
                discriminant: 3,
                payload_offset: 4,
                payload: Some(Box::new(LayoutSpec::Struct {
                    name: "ShiftPayload".to_string(),
                    total_size: 8,
                    fields: vec![
                        FieldLayout {
                            name: "dx".to_string(),
                            offset: 0,
                            layout: u32_layout.clone(),
                        },
                        FieldLayout {
                            name: "dy".to_string(),
                            offset: 4,
                            layout: u32_layout.clone(),
                        },
                    ],
                })),
            },
        ],
    };
    let state_layout = LayoutSpec::Struct {
        name: "B4ParityState".to_string(),
        total_size: 44,
        fields: vec![
            FieldLayout {
                name: "framed_items".to_string(),
                offset: 0,
                layout: framed_items_layout,
            },
            FieldLayout {
                name: "lanes".to_string(),
                offset: 16,
                layout: lanes_layout,
            },
            FieldLayout {
                name: "act".to_string(),
                offset: 28,
                layout: delta_layout,
            },
            FieldLayout {
                name: "total".to_string(),
                offset: 40,
                layout: u32_layout.clone(),
            },
        ],
    };

    // Exercises all 5 `ep2-B4` findings in lockstep with `rustc --edition=2024 -D warnings`:
    // 1. Framed strided `[PaddedItem; 2]` array with poisoned `0xA5` padding bytes preserved
    //    across `coerce_value_to_syn_type`,
    // 2. Evacuating shadowed variables targeted by live `&mut` aliases (`let r = &mut x; { let x = 999; *r += 5; }`,
    //    `{ let x = &mut x; *x += 2; }`, `{ let st = &mut st.total; *st += 1; }`) + helper `mut dst: &mut u32`
    //    rebound to `&mut scratch` without clobbering caller's `x`,
    // 3. `old({ let _ = u32::max(st.total, 1u32); &st.total }) == old(&st.total)` (zero `E0515` false positive!)
    //    alongside local-alias scratch mutation `old({ let r = st; r.total += 3u32; (scratch_bump)(r) })`,
    // 4. Conditional `if` `&mut` place selection + `&mut`-returning helper `select_lane_mut(st, idx)`
    //    (including early `return &mut s.lanes[0];`),
    // 5. `match &mut st.act`, `if let ... = &mut st.act` (with NLL reassignment!), `while let`,
    //    and `let B4ParityState { ref mut total, .. } = *st;`.
    let probe = SpecContractOracleProbe::new(
        "ep2_b4_parity_probe",
        vec![
            SpecParamBinding::mut_ref("st", "B4ParityState", state_layout)
                .with_frame_preserved_fields(["framed_items"]),
            SpecParamBinding::by_value("pick_first", "bool", bool_layout),
            SpecParamBinding::by_value("mode", "u32", u32_layout.clone()),
        ],
        "u32",
        u32_layout.clone(),
        "if mode == 77u32 {\n    \
             st.framed_items[1].word += 1u32;\n\
         }\n\
         let mut x: u32 = 10u32;\n\
         let r = &mut x;\n\
         {\n    \
             let x: u32 = 999u32;\n    \
             let _ = x;\n    \
             *r += 5u32;\n\
         }\n\
         {\n    \
             let x = &mut x;\n    \
             *x += 2u32;\n\
         }\n\
         let mut scratch_slot: u32 = 50u32;\n\
         let redir_out: u32 = redirect_helper(&mut x, &mut scratch_slot, true);\n\
         assert!(redir_out == 150u32 && scratch_slot == 150u32);\n\
         let chosen = if pick_first {\n    \
             &mut st.lanes[0]\n\
         } else {\n    \
             select_lane_mut(st, 2usize)\n\
         };\n\
         *chosen += 10u32;\n\
         *select_lane_mut(st, 1usize) += 4u32;\n\
         while let TaggedDelta::Single(cnt) = &mut st.act {\n    \
             if *cnt >= 3u32 { break; }\n    \
             *cnt += 1u32;\n\
         }\n\
         match &mut st.act {\n    \
             TaggedDelta::Single(v) => { *v += 5u32; }\n    \
             TaggedDelta::Pair(a, b) => {\n        \
                 *a += 1u32;\n        \
                 *b += 2u32;\n    \
             }\n    \
             TaggedDelta::Shift { dx, dy } => {\n        \
                 *dx += *dy;\n        \
                 st.act = TaggedDelta::Single(*dx);\n    \
             }\n    \
             TaggedDelta::Empty => {}\n\
         }\n\
         if let TaggedDelta::Pair(ref mut a, b_copy) = st.act {\n    \
             *a += b_copy;\n\
         }\n\
         let B4ParityState { ref mut total, .. } = *st;\n\
         *total += x;\n\
         let act_sum: u32 = match st.act {\n    \
             TaggedDelta::Single(v) => v,\n    \
             TaggedDelta::Pair(a, b) => a + b,\n    \
             TaggedDelta::Shift { dx, dy } => dx + dy,\n    \
             TaggedDelta::Empty => 0u32,\n\
         };\n\
         let ext_v: u32 = ext_step();\n\
         {\n    \
             let st = &mut st.total;\n    \
             *st += act_sum + ext_v;\n\
         }\n\
         st.total + st.lanes[0] + st.lanes[1] + st.lanes[2]",
    )
    .with_type_defs(
        "#[repr(C)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub struct PaddedItem { pub tag: u8, pub word: u32 }\n\
         #[repr(C, u8)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub enum TaggedDelta {\n    \
             Empty = 0,\n    \
             Single(u32) = 1,\n    \
             Pair(u32, u32) = 2,\n    \
             Shift { dx: u32, dy: u32 } = 3,\n\
         }\n\
         #[repr(C)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub struct B4ParityState {\n    \
             pub framed_items: [PaddedItem; 2],\n    \
             pub lanes: [u32; 3],\n    \
             pub act: TaggedDelta,\n    \
             pub total: u32,\n\
         }\n\
         pub fn select_lane_mut(s: &mut B4ParityState, idx: usize) -> &mut u32 {\n    \
             if idx == 0usize { return &mut s.lanes[0]; }\n    \
             &mut s.lanes[idx]\n\
         }\n\
         pub fn redirect_helper<'a>(mut dst: &'a mut u32, fallback: &'a mut u32, redirect: bool) -> u32 {\n    \
             if redirect { dst = fallback; }\n    \
             *dst += 100u32;\n    \
             *dst\n\
         }\n\
         pub fn by_val_total(s: B4ParityState) -> u32 { s.total }\n\
         pub fn scratch_bump(s: &mut B4ParityState) -> u32 {\n    \
             s.total += 7u32;\n    \
             s.total\n\
         }",
    )
    .with_external_callee(SpecExternalCallee::new(
        "ext_step",
        std::iter::empty::<&str>(),
        "u32",
        u32_layout,
    ))
    .with_requires(
        "bounded_inputs",
        "st.total <= 500u32 && st.lanes[0] <= 50u32 && st.lanes[1] <= 50u32 && st.lanes[2] <= 50u32",
    )
    .with_ensures(
        "old_proj_ref_no_e0515_and_local_alias_mut",
        "old({ let _ = u32::max(st.total, 1u32); let _ = by_val_total(*st); &st.total }) == old(&st.total) \
         && old({ let r = st; r.total += 3u32; (scratch_bump)(r) }) == old(st.total) + 10u32",
    )
    .with_ensures(
        "exact_post_check",
        "mode != 9u32 \
         && st.lanes[1] == old(st.lanes[1]) + 4u32 \
         && ((pick_first && st.lanes[0] == old(st.lanes[0]) + 10u32 && st.lanes[2] == old(st.lanes[2])) \
             || (!pick_first && st.lanes[2] == old(st.lanes[2]) + 10u32 && st.lanes[0] == old(st.lanes[0]))) \
         && st.total >= old(st.total) + 17u32",
    );

    let make_trial = |disc: u8, p0: u32, p1: u32, total: u32, pick_first: bool, mode: u32| -> Vec<u8> {
        let mut b = vec![0xA5u8; 49];
        b[0] = 3u8;
        b[4..8].copy_from_slice(&11u32.to_le_bytes());
        b[8] = 5u8;
        b[12..16].copy_from_slice(&22u32.to_le_bytes());
        b[16..20].copy_from_slice(&1u32.to_le_bytes()); // lanes[0] = 1
        b[20..24].copy_from_slice(&2u32.to_le_bytes()); // lanes[1] = 2
        b[24..28].copy_from_slice(&3u32.to_le_bytes()); // lanes[2] = 3
        b[28] = disc;
        b[32..36].copy_from_slice(&p0.to_le_bytes());
        b[36..40].copy_from_slice(&p1.to_le_bytes());
        b[40..44].copy_from_slice(&total.to_le_bytes());
        b[44] = u8::from(pick_first);
        b[45..49].copy_from_slice(&mode.to_le_bytes());
        b
    };

    let mut base_sched = EnvSchedule::new().with_callee_return_size("ext_step", 4);
    base_sched.set_callee_default("ext_step", 6u32.to_le_bytes().to_vec());

    let trials = vec![
        // Trial 0: `Pair(4, 5)`, `pick_first = false` (`select_lane_mut(st, 2)`), `mode = 0` -> HOLD
        (make_trial(2, 4, 5, 20, false, 0), Some(base_sched.clone())),
        // Trial 1: `Single(1)` (`while let` bumps 1 -> 3, then `match &mut` bumps 3 -> 8), `pick_first = true` -> HOLD
        (make_trial(1, 1, 0, 20, true, 0), Some(base_sched.clone())),
        // Trial 2: `Shift { dx: 3, dy: 4 }` (`match &mut` mutates `*dx += *dy` -> 7, then NLL reassigns `st.act = Single(7)`!) -> HOLD
        (make_trial(3, 3, 4, 20, false, 0), Some(base_sched.clone())),
        // Trial 3: `total = 900` fails `requires` -> FILTERED
        (make_trial(0, 0, 0, 900, true, 0), Some(base_sched.clone())),
        // Trial 4: `mode = 77` mutates framed `st.framed_items[1].word` -> FRAME:st.framed_items
        (make_trial(2, 4, 5, 20, true, 77), Some(base_sched.clone())),
        // Trial 5: `mode = 9` fails `exact_post_check` -> VIOLATION:exact_post_check
        (make_trial(2, 4, 5, 20, false, 9), Some(base_sched.clone())),
        // Trial 6: scheduled panic on `ext_step` -> TRAP
        (
            make_trial(2, 4, 5, 20, false, 0),
            Some(base_sched.with_panic_on_call(0)),
        ),
    ];

    let report = probe
        .verify_spec_postcondition_batch(&trials)
        .expect("verify ep2-B4 parity batch");
    assert_eq!(report.verdicts[0], SpecPostconditionVerdict::VerifiedHold);
    assert_eq!(report.verdicts[1], SpecPostconditionVerdict::VerifiedHold);
    assert_eq!(report.verdicts[2], SpecPostconditionVerdict::VerifiedHold);
    assert!(matches!(
        &report.verdicts[3],
        SpecPostconditionVerdict::VacuouslyFiltered { .. }
    ));
    assert!(matches!(
        &report.verdicts[4],
        SpecPostconditionVerdict::PostconditionViolation {
            kind: SpecViolationKind::FrameCondition { param, field },
            ..
        } if param == "st" && field == "framed_items"
    ));
    assert!(matches!(
        &report.verdicts[5],
        SpecPostconditionVerdict::PostconditionViolation {
            kind: SpecViolationKind::EnsuresClause { label, .. },
            ..
        } if label == "exact_post_check"
    ));
    assert!(matches!(
        &report.verdicts[6],
        SpecPostconditionVerdict::PanicOrTrap {
            phase: SpecExecPhase::Body,
            ..
        }
    ));

    let exe_src = probe
        .synthesize_rust_executable_harness_with_schedules(&trials)
        .expect("synthesize ep2-B4 executable harness");
    assert!(!contains_unsafe_token(&exe_src));
    let native_lines = compile_and_run_spec_harness("ep2_b4_lockstep_parity", &exe_src);
    assert_eq!(
        native_lines,
        vec![
            "TRIAL:0:HOLD",
            "TRIAL:1:HOLD",
            "TRIAL:2:HOLD",
            "TRIAL:3:FILTERED",
            "TRIAL:4:FRAME:st.framed_items",
            "TRIAL:5:VIOLATION:exact_post_check",
            "TRIAL:6:TRAP",
        ]
    );
}

#[test]
fn ep2_a4_lockstep_parity_on_direct_mut_param_ergonomics_single_eval_ref_mut_and_by_val_old_refs() {
    use anneal_difftest::{
        EnumVariantLayout, SpecContractOracleProbe, SpecExecPhase, SpecExternalCallee,
        SpecParamBinding, SpecPostconditionVerdict, SpecViolationKind,
    };

    let u32_layout = LayoutSpec::Scalar(ScalarLayout::u32());
    let usize_layout = LayoutSpec::Scalar(ScalarLayout::unsigned(8));
    let arr_layout = LayoutSpec::Array {
        elem: Box::new(u32_layout.clone()),
        elem_stride: 4,
        len: 2,
    };
    let delta_layout = LayoutSpec::Enum {
        name: "DirectDelta".to_string(),
        total_size: 8,
        tag_offset: 0,
        tag_size: 1,
        variants: vec![
            EnumVariantLayout {
                name: "Idle".to_string(),
                discriminant: 0,
                payload_offset: 4,
                payload: None,
            },
            EnumVariantLayout {
                name: "Step".to_string(),
                discriminant: 1,
                payload_offset: 4,
                payload: Some(Box::new(u32_layout.clone())),
            },
        ],
    };
    let pair_layout = LayoutSpec::Struct {
        name: "ValPair".to_string(),
        total_size: 8,
        fields: vec![
            FieldLayout {
                name: "a".to_string(),
                offset: 0,
                layout: u32_layout.clone(),
            },
            FieldLayout {
                name: "b".to_string(),
                offset: 4,
                layout: u32_layout.clone(),
            },
        ],
    };

    // Exercises all `ep2-A4` convergence fixes in lockstep with `rustc --edition=2024 -D warnings`:
    // 1. Direct `&mut` parameter ergonomics WITHOUT `&mut *` (`match act`, `for slot in arr` on a
    //    dedicated `lanes: &mut [u32; 2]`, and `let moved_arr = arr; moved_arr[0] += 3;`),
    // 2. Single-evaluation `let ref mut tmp_ext = ext_once();` against a 1-element `EnvSchedule`
    //    queue (no default!) so double evaluation would panic with `PassThrough`,
    // 3. Immediate OOB index trap on `let ref mut picked = arr[idx];`,
    // 4. By-value parameter scratch mutability in `requires[i]` / `ensures[i]`, reference-returning
    //    `old(&vp.a) == &vp.a` (zero `E0515`), and mutating `old({ vp.a += 7u32; vp.a })`.
    let probe = SpecContractOracleProbe::new(
        "ep2_a4_direct_mut_and_by_val_old_parity",
        vec![
            SpecParamBinding::mut_ref("arr", "[u32; 2]", arr_layout.clone()),
            SpecParamBinding::mut_ref("lanes", "[u32; 2]", arr_layout),
            SpecParamBinding::mut_ref("act", "DirectDelta", delta_layout),
            SpecParamBinding::by_value("vp", "ValPair", pair_layout),
            SpecParamBinding::by_value("idx", "usize", usize_layout),
        ],
        "u32",
        u32_layout.clone(),
        "let ref mut tmp_ext: u32 = ext_once();\n\
         *tmp_ext += 5u32;\n\
         let ref mut picked_elem: u32 = arr[idx];\n\
         *picked_elem += 1u32;\n\
         for slot in lanes {\n    \
             *slot += 2u32;\n\
         }\n\
         match act {\n    \
             DirectDelta::Step(dx) => { *dx += *tmp_ext; }\n    \
             DirectDelta::Idle => {}\n\
         }\n\
         let moved_arr = arr;\n\
         moved_arr[0] += 3u32;\n\
         vp.b += 4u32;\n\
         moved_arr[0] + moved_arr[1] + vp.a + vp.b",
    )
    .with_type_defs(
        "#[repr(C, u8)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub enum DirectDelta { Idle = 0, Step(u32) = 1 }\n\
         #[repr(C)]\n\
         #[derive(Copy, Clone, Debug, PartialEq, Eq)]\n\
         pub struct ValPair { pub a: u32, pub b: u32 }",
    )
    .with_external_callee(SpecExternalCallee::new(
        "ext_once",
        std::iter::empty::<&str>(),
        "u32",
        u32_layout,
    ))
    .with_requires(
        "by_val_mut_scratch_req",
        "{ vp.a += 1u32; vp.a <= 50u32 }",
    )
    .with_ensures(
        "by_val_old_ref_and_mut_old",
        "old(&vp.a) == &vp.a \
         && old({ vp.a += 7u32; vp.a }) == old(vp.a) + 7u32 \
         && { vp.b += 9u32; vp.b == old(vp.b) + 9u32 }",
    )
    .with_ensures(
        "direct_mut_params_preserved",
        "vp.a != 9u32 \
         && lanes[0] == old(lanes[0]) + 2u32 \
         && lanes[1] == old(lanes[1]) + 2u32 \
         && match *act {\n    \
             DirectDelta::Step(v) => v == 18u32,\n    \
             DirectDelta::Idle => true,\n\
         }",
    );

    let make_trial = |vpa: u32, idx: u64| -> Vec<u8> {
        let mut b = Vec::with_capacity(40);
        b.extend_from_slice(&10u32.to_le_bytes()); // arr[0] = 10
        b.extend_from_slice(&20u32.to_le_bytes()); // arr[1] = 20
        b.extend_from_slice(&3u32.to_le_bytes()); // lanes[0] = 3
        b.extend_from_slice(&4u32.to_le_bytes()); // lanes[1] = 4
        let mut act_b = [0u8; 8];
        act_b[0] = 1u8; // DirectDelta::Step(4)
        act_b[4..8].copy_from_slice(&4u32.to_le_bytes());
        b.extend_from_slice(&act_b);
        b.extend_from_slice(&vpa.to_le_bytes()); // vp.a
        b.extend_from_slice(&6u32.to_le_bytes()); // vp.b = 6
        b.extend_from_slice(&idx.to_le_bytes());
        b
    };

    // Queue ONLY 1 response (`9u32`) with NO default so any double evaluation panics!
    let mut single_q_sched = EnvSchedule::new().with_callee_return_size("ext_once", 4);
    single_q_sched.push_callee_response("ext_once", 9u32.to_le_bytes().to_vec());

    let trials = vec![
        // Trial 0: `vpa = 5, idx = 0` -> `Step(4)` becomes `Step(4 + (9 + 5)) = Step(18)` -> HOLD!
        (make_trial(5, 0), Some(single_q_sched.clone())),
        // Trial 1: `vpa = 60` fails `requires` (`60 + 1 <= 50` false) -> FILTERED!
        (make_trial(60, 0), Some(single_q_sched.clone())),
        // Trial 2: `idx = 99` triggers OOB index in `let ref mut picked_elem = arr[idx];` -> TRAP!
        (make_trial(5, 99), Some(single_q_sched.clone())),
        // Trial 3: `vpa = 9` fails `direct_mut_params_preserved` (`vp.a != 9u32`) -> VIOLATION!
        (make_trial(9, 1), Some(single_q_sched)),
    ];

    let report = probe
        .verify_spec_postcondition_batch(&trials)
        .expect("verify ep2-A4 parity batch");
    assert_eq!(report.verdicts[0], SpecPostconditionVerdict::VerifiedHold);
    assert!(matches!(
        &report.verdicts[1],
        SpecPostconditionVerdict::VacuouslyFiltered { .. }
    ));
    assert!(matches!(
        &report.verdicts[2],
        SpecPostconditionVerdict::PanicOrTrap {
            phase: SpecExecPhase::Body,
            ..
        }
    ));
    assert!(matches!(
        &report.verdicts[3],
        SpecPostconditionVerdict::PostconditionViolation {
            kind: SpecViolationKind::EnsuresClause { label, .. },
            ..
        } if label == "direct_mut_params_preserved"
    ));

    let exe_src = probe
        .synthesize_rust_executable_harness_with_schedules(&trials)
        .expect("synthesize ep2-A4 executable harness");
    assert!(!contains_unsafe_token(&exe_src));
    let native_lines = compile_and_run_spec_harness("ep2_a4_lockstep_parity", &exe_src);
    assert_eq!(
        native_lines,
        vec![
            "TRIAL:0:HOLD",
            "TRIAL:1:FILTERED",
            "TRIAL:2:TRAP",
            "TRIAL:3:VIOLATION:direct_mut_params_preserved",
        ]
    );
}
