// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end integration test suite for `cargo-anneal`:
//! 1. Declarative `.rs` verification fixtures under `tests/fixtures/` tested
//!    through [`cargo_anneal::verify_crate`] with exact stage, scope, and cause
//!    attribution (`//@ pass`, `//@ fail(...)`, `//@ known_bug(...)`,
//!    `//@ mir-contains`, `//@ mir-not-contains`).
//! 2. Host filesystem, CLI flag, environment-scrubbing, and SHA-256 tamper
//!    boundary tests.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};
use std::thread;

use cargo_anneal::{
    FailureStage, ReleaseChannel, StageFailure, VerifyConfig, VerifyError,
    VerifyReport, setup, verify_crate,
};
use walkdir::WalkDir;

fn toolchain_dir() -> PathBuf {
    env::var_os("ANNEAL_TOOLCHAIN")
        .map(PathBuf::from)
        .or_else(setup::resolve_installed)
        .expect("set ANNEAL_TOOLCHAIN or install an Anneal toolchain")
}

fn anneal_root() -> PathBuf {
    fs::canonicalize(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../.."))
        .expect("canonicalize anneal workspace root")
}

fn cfg_for(crate_dir: &Path) -> VerifyConfig {
    VerifyConfig {
        crate_dir: crate_dir.to_path_buf(),
        toolchain_dir: toolchain_dir(),
        anneal_root: anneal_root(),
        allow_candidate_features: Vec::new(),
        release_channel: ReleaseChannel::Alpha,
    }
}

fn ensure_warm() {
    static WARM: OnceLock<()> = OnceLock::new();
    WARM.get_or_init(|| {
        let warmup_dir = TempCrateDir::new("warmup", ID_PLAIN);
        let _ = verify_crate(&cfg_for(&warmup_dir.path));
    });
}

fn cli() -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_cargo-anneal"));
    cmd.arg("anneal")
        .arg("verify")
        .arg("--toolchain")
        .arg(toolchain_dir())
        .arg("--anneal-root")
        .arg(anneal_root());
    cmd
}

const POLICY: &str = "[package.metadata.anneal.trust-policy]\n\
                      allow-candidate-features = [\"*\"]\n";

const ID_SPEC: &str = "/// anneal:spec ensures(ret == x)\n\
                       pub fn id(x: usize) -> usize {\n    x\n}\n";
const ID_PLAIN: &str = "pub fn id(x: usize) -> usize {\n    x\n}\n";

struct TempCrateDir {
    _dir: tempfile::TempDir,
    path: PathBuf,
}

impl TempCrateDir {
    fn with(label: &str, source: &str, policy: bool) -> Self {
        let dir = tempfile::Builder::new()
            .prefix(&format!("anneal-integration-{label}-"))
            .tempdir_in("/tmp")
            .expect("create temp crate dir");
        let path = dir.path().to_path_buf();
        fs::create_dir_all(path.join("src")).unwrap();
        let toml = format!(
            "[package]\nname = \"sample\"\nversion = \"0.1.0\"\n\
             edition = \"2024\"\n\n{}",
            if policy { POLICY } else { "" }
        );
        fs::write(path.join("Cargo.toml"), toml).unwrap();
        fs::write(path.join("src/lib.rs"), source).unwrap();
        Self { _dir: dir, path }
    }

    fn new(label: &str, source: &str) -> Self {
        Self::with(label, source, true)
    }
}

fn assert_cli_success(output: &std::process::Output) -> String {
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    assert!(
        output.status.success(),
        "expected `cargo-anneal anneal verify` to succeed:\nstdout: {stdout}\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    stdout
}

// ---------------------------------------------------------------------------
// Declarative fixture directive model and parser
// ---------------------------------------------------------------------------

/// Formats a `//@ fail(...)` or `//@ known_bug(#..., ...)` directive line for
/// `ANNEAL_BLESS=1`.
fn format_failure_directive(
    known_bug: Option<&str>,
    stage: &FailureStage,
    actual_msg: &str,
) -> String {
    let stage_str = match stage {
        FailureStage::Capture => "capture".to_string(),
        FailureStage::Proof { scope } => format!("proof, {scope}"),
    };
    let quoted = serde_json::to_string(actual_msg).unwrap();
    match known_bug {
        Some(issue) => format!("//@ known_bug({issue}, {stage_str}): {quoted}"),
        None => format!("//@ fail({stage_str}): {quoted}"),
    }
}

/// Primary test expectation declared by a fixture case.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Expectation {
    Pass,
    Failure {
        known_bug: Option<String>,
        stage: FailureStage,
        expected_substr: String,
    },
}

/// A single parsed test case within a `.rs` fixture file.
#[derive(Debug, Clone)]
struct TestCase {
    /// Logical case name (`<rel_stem>` or `<rel_stem>::<subname>`).
    name: String,
    /// Path to the `.rs` fixture file.
    file_path: PathBuf,
    /// Pre-materialized `src/lib.rs` content with 1:1 line numbers matching
    /// `file_path`.
    source: String,
    /// 0-based line index of the primary `//@` expectation directive in
    /// `file_path` (targeted by `ANNEAL_BLESS=1`).
    primary_line_index: usize,
    /// Validated primary expectation.
    expectation: Expectation,
    /// Substrings that must appear in the captured `Mir.lean`.
    mir_contains: Vec<String>,
    /// Substrings that must not appear in the captured `Mir.lean`.
    mir_not_contains: Vec<String>,
}

/// An in-place header update queued by `ANNEAL_BLESS=1`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct BlessPatch {
    file_path: PathBuf,
    line_index: usize,
    replacement_line: String,
}

fn parse_quoted_string(raw: &str, context: &str) -> Result<String, String> {
    let trimmed = raw.trim();
    if !trimmed.starts_with('"') || !trimmed.ends_with('"') || trimmed.len() < 2
    {
        return Err(format!(
            "{context}: expected double-quoted string literal, got `{trimmed}`"
        ));
    }
    let parsed = serde_json::from_str::<String>(trimmed).map_err(|e| {
        format!("{context}: invalid string literal `{trimmed}`: {e}")
    })?;
    if parsed.is_empty() {
        return Err(format!(
            "{context}: expected non-empty string literal in directive"
        ));
    }
    Ok(parsed)
}

fn is_valid_ident(s: &str) -> bool {
    !s.is_empty()
        && s.bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

fn is_valid_issue_tag(s: &str) -> bool {
    s.strip_prefix('#')
        .is_some_and(|digits| !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()))
}

fn parse_failure_stage(
    parts: &[&str],
    context: &str,
) -> Result<FailureStage, String> {
    match parts {
        ["capture"] => Ok(FailureStage::Capture),
        ["proof", scope] => {
            if !is_valid_ident(scope) {
                return Err(format!(
                    "{context}: invalid proof scope `{scope}` (expected `crate` or function name)"
                ));
            }
            Ok(FailureStage::Proof {
                scope: (*scope).to_string(),
            })
        }
        ["proof"] => Err(format!(
            "{context}: `proof` stage requires a scope (`proof, crate` or `proof, <fn_name>`)"
        )),
        ["capture", ..] => Err(format!(
            "{context}: `capture` stage does not take a scope argument"
        )),
        _ => Err(format!(
            "{context}: invalid stage specification `{}`",
            parts.join(", ")
        )),
    }
}

fn parse_primary_directive(
    directive: &str,
    context: &str,
) -> Result<Option<Expectation>, String> {
    if directive == "pass" {
        return Ok(Some(Expectation::Pass));
    }
    let (is_known_bug, rest) = if let Some(r) = directive.strip_prefix("fail(")
    {
        (false, r)
    } else if let Some(r) = directive.strip_prefix("known_bug(") {
        (true, r)
    } else {
        return Ok(None);
    };
    let Some((args_str, after_paren)) = rest.split_once("):") else {
        return Err(format!(
            "{context}: malformed failure directive `{directive}`"
        ));
    };
    let expected_substr = parse_quoted_string(after_paren, context)?;
    let parts: Vec<&str> = args_str.split(',').map(str::trim).collect();
    let (known_bug, stage_parts) = if is_known_bug {
        let Some((&issue, tail)) = parts.split_first() else {
            return Err(format!(
                "{context}: `known_bug` requires `known_bug(#<issue>, <stage>...)`"
            ));
        };
        if tail.is_empty() {
            return Err(format!(
                "{context}: `known_bug` requires `known_bug(#<issue>, <stage>...)`"
            ));
        }
        if !is_valid_issue_tag(issue) {
            return Err(format!(
                "{context}: invalid issue reference `{issue}` in `known_bug` (expected `#<number>`)"
            ));
        }
        (Some(issue.to_string()), tail)
    } else {
        (None, parts.as_slice())
    };
    let stage = parse_failure_stage(stage_parts, context)?;
    Ok(Some(Expectation::Failure {
        known_bug,
        stage,
        expected_substr,
    }))
}

/// Parses a `.rs` fixture file into one or more [`TestCase`] records, failing
/// closed on unknown directives, missing/duplicate primary expectations, or
/// invalid directive combinations.
fn parse_fixture_file(
    rel_stem: &str,
    file_path: &Path,
    source: &str,
) -> Result<Vec<TestCase>, String> {
    if rel_stem.is_empty() || !rel_stem.split('/').all(is_valid_ident) {
        return Err(format!(
            "{}: invalid fixture path stem `{rel_stem}`",
            file_path.display()
        ));
    }
    let all_lines: Vec<String> = source.lines().map(String::from).collect();
    let mut case_headers: Vec<(String, usize)> = Vec::new();

    for (idx, line) in all_lines.iter().enumerate() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("// === case:") {
            let Some(sub_raw) = rest.strip_suffix("===") else {
                return Err(format!(
                    "{}:{}: malformed `// === case: <name> ===` divider",
                    file_path.display(),
                    idx + 1
                ));
            };
            let sub = sub_raw.trim();
            if !is_valid_ident(sub) {
                return Err(format!(
                    "{}:{}: invalid case name `{sub}`",
                    file_path.display(),
                    idx + 1
                ));
            }
            if case_headers.iter().any(|(existing, _)| existing == sub) {
                return Err(format!(
                    "{}:{}: duplicate case name `{sub}`",
                    file_path.display(),
                    idx + 1
                ));
            }
            case_headers.push((sub.to_string(), idx));
        }
    }

    let spans: Vec<(String, usize, usize)> = if case_headers.is_empty() {
        vec![(rel_stem.to_string(), 0, all_lines.len())]
    } else {
        for (idx, line) in all_lines[..case_headers[0].1].iter().enumerate() {
            if line.trim_start().starts_with("//@") {
                return Err(format!(
                    "{}:{}: `//@` directive appears before first `// === case:` divider",
                    file_path.display(),
                    idx + 1
                ));
            }
        }
        let mut out = Vec::with_capacity(case_headers.len());
        for (i, (sub, start)) in case_headers.iter().enumerate() {
            let end = case_headers
                .get(i + 1)
                .map(|(_, next_start)| *next_start)
                .unwrap_or(all_lines.len());
            out.push((format!("{rel_stem}::{sub}"), *start, end));
        }
        out
    };

    let mut cases = Vec::with_capacity(spans.len());
    for (name, start_line, end_line) in spans {
        let mut primary: Option<(usize, Expectation)> = None;
        let mut mir_contains = Vec::new();
        let mut mir_not_contains = Vec::new();

        for idx in start_line..end_line {
            let trimmed = all_lines[idx].trim();
            let Some(after_prefix) = trimmed.strip_prefix("//@") else {
                continue;
            };
            let directive = after_prefix.trim();
            let context =
                format!("{}:{} ({name})", file_path.display(), idx + 1);

            if let Some(exp) = parse_primary_directive(directive, &context)? {
                if primary.is_some() {
                    return Err(format!(
                        "{context}: multiple primary expectation directives in one case"
                    ));
                }
                primary = Some((idx, exp));
            } else if let Some(arg) = directive.strip_prefix("mir-contains:") {
                mir_contains.push(parse_quoted_string(arg, &context)?);
            } else if let Some(arg) = directive.strip_prefix("mir-not-contains:")
            {
                mir_not_contains.push(parse_quoted_string(arg, &context)?);
            } else {
                return Err(format!(
                    "{context}: unknown directive `//@ {directive}`"
                ));
            }
        }

        let Some((primary_line_index, expectation)) = primary else {
            return Err(format!(
                "{} ({name}): missing primary expectation directive \
                 (`//@ pass`, `//@ fail(...)`, or `//@ known_bug(...)`)",
                file_path.display()
            ));
        };

        if matches!(
            expectation,
            Expectation::Failure {
                stage: FailureStage::Capture,
                ..
            }
        ) && (!mir_contains.is_empty() || !mir_not_contains.is_empty())
        {
            return Err(format!(
                "{} ({name}): `mir-contains` / `mir-not-contains` cannot be used \
                 on `capture`-stage failures (no `Mir.lean` is emitted)",
                file_path.display()
            ));
        }

        cases.push(TestCase {
            name,
            file_path: file_path.to_path_buf(),
            source: materialize_case_source(&all_lines, start_line, end_line),
            primary_line_index,
            expectation,
            mir_contains,
            mir_not_contains,
        });
    }

    Ok(cases)
}

/// Materializes lines `start_line..end_line` of `all_lines` as `src/lib.rs`
/// with 1:1 line numbering matching the fixture file.
fn materialize_case_source(
    all_lines: &[String],
    start_line: usize,
    end_line: usize,
) -> String {
    let has_no_std = all_lines[start_line..end_line]
        .iter()
        .any(|l| l.trim().starts_with("#![no_std]"));
    let mut injected_no_std = has_no_std;
    let mut out = String::new();

    for (idx, line) in all_lines.iter().enumerate() {
        if idx < start_line || idx >= end_line {
            out.push_str("//\n");
        } else if !injected_no_std
            && (line.trim().starts_with("// === case:")
                || line.trim().starts_with("//@"))
        {
            out.push_str("#![no_std]\n");
            injected_no_std = true;
        } else {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}

fn first_capture_error_line(stderr: &str) -> String {
    for line in stderr.lines() {
        let trimmed = line.trim();
        if let Some((_, msg)) = trimmed.split_once("error: ") {
            return msg.trim().to_string();
        }
        if let Some(idx) = trimmed.find("error[")
            && let Some((_, msg)) = trimmed[idx..].split_once("]: ")
        {
            return msg.trim().to_string();
        }
    }
    for line in stderr.lines() {
        let trimmed = line.trim();
        if !trimmed.is_empty()
            && !trimmed.starts_with("anneal-rustc-capture: unsupported crate (")
        {
            return trimmed.to_string();
        }
    }
    "anneal-rustc-capture failed".to_string()
}

fn bless_diagnostic_for(failure: &StageFailure) -> String {
    match &failure.stage {
        FailureStage::Capture => first_capture_error_line(&failure.diagnostic),
        FailureStage::Proof { .. } => failure.diagnostic.clone(),
    }
}

fn bless_enabled() -> bool {
    for var in ["ANNEAL_BLESS", "BLESS"] {
        if let Ok(val) = env::var(var) {
            let trimmed = val.trim();
            if matches!(trimmed, "1" | "true" | "TRUE") {
                return true;
            }
            if matches!(trimmed, "0" | "false" | "FALSE") {
                return false;
            }
        }
    }
    false
}

fn check_mir_assertions(
    case: &TestCase,
    already_captured: Option<&str>,
) -> Result<(), String> {
    if case.mir_contains.is_empty() && case.mir_not_contains.is_empty() {
        return Ok(());
    }
    let mir = already_captured.ok_or_else(|| {
        format!(
            "missing captured Mir.lean for mir-contains check on `{}`",
            case.name
        )
    })?;
    for needle in &case.mir_contains {
        if !mir.contains(needle) {
            return Err(format!(
                "`{}`: captured Mir.lean did not contain expected substring {:?}\nMir.lean:\n{mir}",
                case.name, needle
            ));
        }
    }
    for needle in &case.mir_not_contains {
        if mir.contains(needle) {
            return Err(format!(
                "`{}`: captured Mir.lean unexpectedly contained forbidden substring {:?}\nMir.lean:\n{mir}",
                case.name, needle
            ));
        }
    }
    Ok(())
}

enum CaseOutcome {
    Passed,
    Blessed(BlessPatch),
    Failed(String),
}

fn save_failure_bundle(
    case: &TestCase,
    crate_dir: &Path,
    already_captured: Option<&str>,
    failure_msg: &str,
) -> PathBuf {
    let slug = case.name.replace('/', "-").replace("::", ".");
    let bundle_dir = anneal_root()
        .join("target/anneal-test-failures")
        .join(&slug);
    let _ = fs::remove_dir_all(&bundle_dir);
    let _ = fs::create_dir_all(bundle_dir.join("src"));
    let _ = fs::copy(crate_dir.join("Cargo.toml"), bundle_dir.join("Cargo.toml"));
    let _ = fs::copy(
        crate_dir.join("src/lib.rs"),
        bundle_dir.join("src/lib.rs"),
    );
    if let Some(mir) = already_captured {
        let _ = fs::write(bundle_dir.join("Mir.lean"), mir);
    }
    let _ = fs::write(bundle_dir.join("error.txt"), failure_msg);
    let repro_script = format!(
        "#!/usr/bin/env bash\nset -euo pipefail\n\
         ANNEAL_TEST_FILTER='{}' cargo test -p cargo-anneal --test integration\n",
        case.name
    );
    let repro_path = bundle_dir.join("reproduce.sh");
    if fs::write(&repro_path, repro_script).is_ok() {
        let _ =
            fs::set_permissions(&repro_path, fs::Permissions::from_mode(0o755));
    }
    bundle_dir
}

fn evaluate_case(
    case: &TestCase,
    result: &Result<VerifyReport, VerifyError>,
    bless: bool,
) -> CaseOutcome {
    let captured_mir = match result {
        Ok(r) => Some(r.mir_lean.as_str()),
        Err(e) => e.mir_lean.as_deref(),
    };
    match (&case.expectation, result) {
        (Expectation::Pass, Ok(_)) => {
            if let Err(e) = check_mir_assertions(case, captured_mir) {
                return CaseOutcome::Failed(e);
            }
            CaseOutcome::Passed
        }
        (Expectation::Pass, Err(err)) => CaseOutcome::Failed(format!(
            "`{}` ({}:{}): expected `//@ pass`, but verification failed:\n{err}",
            case.name,
            case.file_path.display(),
            case.primary_line_index + 1
        )),
        (
            Expectation::Failure {
                known_bug: None,
                stage,
                ..
            },
            Ok(_),
        ) => CaseOutcome::Failed(format!(
            "`{}` ({}:{}): expected failure `{stage:?}`, but verification succeeded",
            case.name,
            case.file_path.display(),
            case.primary_line_index + 1
        )),
        (
            Expectation::Failure {
                known_bug: Some(issue),
                ..
            },
            Ok(_),
        ) => {
            if let Err(e) = check_mir_assertions(case, captured_mir) {
                return CaseOutcome::Failed(e);
            }
            if bless {
                CaseOutcome::Blessed(BlessPatch {
                    file_path: case.file_path.clone(),
                    line_index: case.primary_line_index,
                    replacement_line: "//@ pass".to_string(),
                })
            } else {
                CaseOutcome::Failed(format!(
                    "`{}` ({}:{}): `known_bug({issue})` now passes verification! \
                     Promote the directive to `//@ pass` (or re-run with `ANNEAL_BLESS=1`).",
                    case.name,
                    case.file_path.display(),
                    case.primary_line_index + 1
                ))
            }
        }
        (
            Expectation::Failure {
                known_bug,
                stage,
                expected_substr,
            },
            Err(err),
        ) => {
            let Some(failure) = &err.failure else {
                return CaseOutcome::Failed(format!(
                    "`{}` ({}:{}): unexpected verification error format:\n{err}",
                    case.name,
                    case.file_path.display(),
                    case.primary_line_index + 1
                ));
            };
            if matches!(stage, FailureStage::Capture)
                != matches!(failure.stage, FailureStage::Capture)
            {
                return CaseOutcome::Failed(format!(
                    "`{}` ({}:{}): expected `{stage:?}` failure, \
                     but failed at `{:?}`:\n{err}",
                    case.name,
                    case.file_path.display(),
                    case.primary_line_index + 1,
                    failure.stage
                ));
            }
            if matches!(failure.stage, FailureStage::Proof { .. })
                && let Err(e) = check_mir_assertions(case, captured_mir)
            {
                return CaseOutcome::Failed(e);
            }
            if &failure.stage == stage
                && failure.diagnostic.contains(expected_substr)
            {
                return CaseOutcome::Passed;
            }
            let bless_msg = bless_diagnostic_for(failure);
            if bless {
                return CaseOutcome::Blessed(BlessPatch {
                    file_path: case.file_path.clone(),
                    line_index: case.primary_line_index,
                    replacement_line: format_failure_directive(
                        known_bug.as_deref(),
                        &failure.stage,
                        &bless_msg,
                    ),
                });
            }
            CaseOutcome::Failed(format!(
                "`{}` ({}:{}): failure mismatch:\n  expected: stage={stage:?}, substr={expected_substr:?}\n  actual:   stage={:?}, message={bless_msg:?}\n{err}",
                case.name,
                case.file_path.display(),
                case.primary_line_index + 1,
                failure.stage
            ))
        }
    }
}

fn run_case(case: &TestCase, bless: bool) -> CaseOutcome {
    let slug = case.name.replace('/', "-").replace("::", ".");
    let crate_dir = TempCrateDir::new(&slug, &case.source);
    let cfg = cfg_for(&crate_dir.path);
    let result = verify_crate(&cfg);
    let captured_mir = match &result {
        Ok(r) => Some(r.mir_lean.as_str()),
        Err(e) => e.mir_lean.as_deref(),
    };
    let keep_sandbox =
        env::var("ANNEAL_KEEP_SANDBOX").is_ok_and(|v| v == "1" || v == "true");

    let outcome = evaluate_case(case, &result, bless);
    match &outcome {
        CaseOutcome::Failed(msg) => {
            let bundle = save_failure_bundle(
                case,
                &crate_dir.path,
                captured_mir,
                msg,
            );
            CaseOutcome::Failed(format!(
                "{msg}\n  reproduction bundle: {}\n  re-run: ANNEAL_TEST_FILTER='{}' cargo test -p cargo-anneal --test integration",
                bundle.display(),
                case.name
            ))
        }
        CaseOutcome::Passed | CaseOutcome::Blessed(_) => {
            if keep_sandbox {
                let _ = save_failure_bundle(
                    case,
                    &crate_dir.path,
                    captured_mir,
                    "PASSED",
                );
            }
            outcome
        }
    }
}

fn apply_bless_patches(patches: &[BlessPatch]) -> Result<(), String> {
    let mut by_file: BTreeMap<&Path, Vec<&BlessPatch>> = BTreeMap::new();
    for patch in patches {
        by_file.entry(&patch.file_path).or_default().push(patch);
    }
    for (path, file_patches) in by_file {
        let content = fs::read_to_string(path)
            .map_err(|e| format!("cannot read {} for bless: {e}", path.display()))?;
        let mut lines: Vec<String> = content.lines().map(String::from).collect();
        for patch in file_patches {
            if patch.line_index >= lines.len() {
                return Err(format!(
                    "bless line index {} out of range for {}",
                    patch.line_index,
                    path.display()
                ));
            }
            lines[patch.line_index] = patch.replacement_line.clone();
        }
        let mut new_content = lines.join("\n");
        new_content.push('\n');
        fs::write(path, new_content)
            .map_err(|e| format!("cannot write blessed {}: {e}", path.display()))?;
    }
    Ok(())
}

/// Discovers and runs every `.rs` fixture case under `tests/fixtures/`,
/// verifying that `tests/` contains no orphan non-fixture files.
#[test]
fn verifies_fixture_corpus() {
    let root = anneal_root();
    let tests_dir = root.join("tests");
    let fixtures_dir = tests_dir.join("fixtures");
    assert!(
        fixtures_dir.is_dir(),
        "expected fixture directory at {}",
        fixtures_dir.display()
    );

    let mut fixture_files = Vec::new();
    for entry in WalkDir::new(&tests_dir).follow_links(false) {
        let entry = entry.expect("walk tests/ directory");
        if entry.file_type().is_dir() {
            continue;
        }
        let path = entry.path();
        assert!(
            entry.file_type().is_file()
                && path.starts_with(&fixtures_dir)
                && path.extension().is_some_and(|ext| ext == "rs"),
            "unexpected non-fixture file under `tests/`: {}",
            path.display()
        );
        fixture_files.push(path.to_path_buf());
    }
    fixture_files.sort();
    assert!(
        !fixture_files.is_empty(),
        "no `.rs` fixtures found under {}",
        fixtures_dir.display()
    );

    let mut all_cases = Vec::new();
    let mut seen_names = BTreeSet::new();
    for path in &fixture_files {
        let rel = path
            .strip_prefix(&fixtures_dir)
            .unwrap()
            .with_extension("");
        let rel_stem = rel.to_string_lossy().replace('\\', "/");
        let source = fs::read_to_string(path).expect("read fixture file");
        let file_cases = parse_fixture_file(&rel_stem, path, &source)
            .unwrap_or_else(|e| panic!("fixture parse error: {e}"));
        for case in file_cases {
            assert!(
                seen_names.insert(case.name.clone()),
                "duplicate test case name `{}`",
                case.name
            );
            all_cases.push(case);
        }
    }

    let filter = env::var("ANNEAL_TEST_FILTER").ok();
    let selected: Vec<&TestCase> = all_cases
        .iter()
        .filter(|c| {
            filter
                .as_ref()
                .map(|f| c.name.contains(f))
                .unwrap_or(true)
        })
        .collect();
    assert!(
        !selected.is_empty(),
        "no fixture cases matched ANNEAL_TEST_FILTER={filter:?}"
    );

    // Warm the per-process toolchain and compiled `.olean` prefix once before
    // fanning out worker threads.
    ensure_warm();

    let bless = bless_enabled();
    let concurrency = thread::available_parallelism()
        .map(|n| n.get().min(8))
        .unwrap_or(4)
        .min(selected.len());

    let queue = Mutex::new(selected.into_iter());
    let failures: Mutex<Vec<String>> = Mutex::new(Vec::new());
    let patches: Mutex<Vec<BlessPatch>> = Mutex::new(Vec::new());

    thread::scope(|s| {
        for _ in 0..concurrency {
            s.spawn(|| {
                loop {
                    let next = {
                        let mut q = queue.lock().unwrap();
                        q.next()
                    };
                    let Some(case) = next else {
                        break;
                    };
                    match run_case(case, bless) {
                        CaseOutcome::Passed => {}
                        CaseOutcome::Blessed(patch) => {
                            patches.lock().unwrap().push(patch);
                        }
                        CaseOutcome::Failed(err) => {
                            failures.lock().unwrap().push(err);
                        }
                    }
                }
            });
        }
    });

    let patches = patches.into_inner().unwrap();
    if !patches.is_empty() {
        apply_bless_patches(&patches).expect("apply ANNEAL_BLESS patches");
    }

    let failures = failures.into_inner().unwrap();
    if !failures.is_empty() {
        panic!(
            "{} fixture case(s) failed:\n\n{}",
            failures.len(),
            failures.join("\n\n")
        );
    }
}

// ---------------------------------------------------------------------------
// Parser fail-closed and polarity-safe `ANNEAL_BLESS` unit tests
// ---------------------------------------------------------------------------

#[test]
fn rejects_malformed_fixture_directives() {
    let dummy = Path::new("tests/fixtures/dummy.rs");
    for (label, bad_src, expected_err) in [
        (
            "unknown-directive",
            "//@ pass\n//@ unknown-flag: true\npub fn id(x: usize) -> usize { x }\n",
            "unknown directive",
        ),
        (
            "missing-primary",
            "//@ mir-contains: \"foo\"\npub fn id(x: usize) -> usize { x }\n",
            "missing primary expectation directive",
        ),
        (
            "duplicate-primary",
            "//@ pass\n//@ fail(capture): \"err\"\npub fn id(x: usize) -> usize { x }\n",
            "multiple primary expectation directives",
        ),
        (
            "proof-missing-scope",
            "//@ fail(proof): \"unproved\"\npub fn id(x: usize) -> usize { x }\n",
            "`proof` stage requires a scope",
        ),
        (
            "capture-with-scope",
            "//@ fail(capture, id): \"err\"\npub fn id(x: usize) -> usize { x }\n",
            "`capture` stage does not take a scope",
        ),
        (
            "mir-contains-on-capture-fail",
            "//@ fail(capture): \"err\"\n//@ mir-contains: \"foo\"\npub fn id(x: usize) -> usize { x }\n",
            "cannot be used on `capture`-stage failures",
        ),
        (
            "known-bug-bad-issue",
            "//@ known_bug(108, proof, id): \"unproved\"\npub fn id(x: usize) -> usize { x }\n",
            "invalid issue reference",
        ),
        (
            "empty-mir-contains",
            "//@ pass\n//@ mir-contains: \"\"\npub fn id(x: usize) -> usize { x }\n",
            "expected non-empty string literal",
        ),
        (
            "empty-mir-not-contains",
            "//@ pass\n//@ mir-not-contains: \"\"\npub fn id(x: usize) -> usize { x }\n",
            "expected non-empty string literal",
        ),
    ] {
        let err = parse_fixture_file("dummy", dummy, bad_src)
            .expect_err(&format!("expected `{label}` to fail parsing"));
        assert!(
            err.contains(expected_err),
            "{label}: expected error containing {expected_err:?}, got: {err}"
        );
    }
}

#[test]
fn bless_updates_expectation_and_promotes_resolved_known_bug_without_flipping_polarity()
{
    let tmp = tempfile::Builder::new()
        .prefix("anneal-bless-test-")
        .tempdir_in("/tmp")
        .unwrap();
    let fixture_path = tmp.path().join("sample_bless.rs");
    let initial = "\
// === case: stale_proof_msg ===
//@ fail(proof, wrong_scope): \"outdated message\"
pub fn id(x: usize) -> usize {
    let _ = x;
    0
}

// === case: resolved_known_bug ===
//@ known_bug(#108, proof, id): \"unproved function body\"
pub fn id(x: usize) -> usize {
    x
}

// === case: broken_pass_never_auto_flipped ===
//@ pass
pub fn id(x: usize) -> usize {
    let _ = x;
    0
}
";
    fs::write(&fixture_path, initial).unwrap();
    let cases =
        parse_fixture_file("sample_bless", &fixture_path, initial).unwrap();
    assert_eq!(cases.len(), 3);

    let mut patches = Vec::new();
    let proof_err: Result<VerifyReport, VerifyError> = Err(VerifyError {
        message: "proof [id]: unproved function body\nlean failed".to_string(),
        failure: Some(StageFailure {
            stage: FailureStage::Proof {
                scope: "id".to_string(),
            },
            diagnostic: "unproved function body".to_string(),
        }),
        mir_lean: Some("-- captured Mir.lean".to_string()),
    });
    let pass_ok: Result<VerifyReport, VerifyError> = Ok(VerifyReport {
        mir_lean: String::new(),
        candidate_features: Vec::new(),
        output_text: String::new(),
    });
    match evaluate_case(&cases[0], &proof_err, true) {
        CaseOutcome::Blessed(p) => patches.push(p),
        other => panic!(
            "expected Blessed for stale_proof_msg, got {:?}",
            matches!(other, CaseOutcome::Passed)
        ),
    }
    match evaluate_case(&cases[1], &pass_ok, true) {
        CaseOutcome::Blessed(p) => patches.push(p),
        other => panic!(
            "expected Blessed for resolved_known_bug, got {:?}",
            matches!(other, CaseOutcome::Passed)
        ),
    }
    assert!(
        matches!(
            evaluate_case(&cases[2], &proof_err, true),
            CaseOutcome::Failed(_)
        ),
        "expected broken `//@ pass` case to fail even when bless=true"
    );

    apply_bless_patches(&patches).unwrap();
    let updated = fs::read_to_string(&fixture_path).unwrap();
    assert!(
        updated.contains("//@ fail(proof, id): \"unproved function body\""),
        "expected updated proof scope and message, got:\n{updated}"
    );
    assert!(
        updated.contains("// === case: resolved_known_bug ===\n//@ pass\n"),
        "expected resolved known_bug to promote to `//@ pass`, got:\n{updated}"
    );
}

// ---------------------------------------------------------------------------
// Host-boundary, CLI flag, environment-scrubbing, and SHA-256 tamper tests
// ---------------------------------------------------------------------------

/// Because `cargo-anneal` never reads `.anneal/` as input and always compiles
/// its own in-memory capture and static `Proof.lean`, spoofed `.anneal/Mir.lean`
/// or `.anneal/Proof.lean` files cannot cause a buggy crate to pass.
#[test]
fn ignores_tampered_or_spoofed_files_in_dot_anneal() {
    let crate_dir = TempCrateDir::new(
        "spoofed-dot-anneal",
        "/// anneal:spec ensures(ret == x)\n\
         pub fn id(x: usize) -> usize {\n    0\n}\n",
    );
    fs::create_dir_all(crate_dir.path.join(".anneal")).unwrap();
    fs::write(
        crate_dir.path.join(".anneal/Mir.lean"),
        b"import Trusted\nnamespace Mir\ntheorem crate : True := trivial\nend Mir\n",
    )
    .unwrap();
    fs::write(
        crate_dir.path.join(".anneal/Proof.lean"),
        b"import Trusted\nnamespace Proof\ntheorem verify_crate : True := trivial\nend Proof\n",
    )
    .unwrap();
    let err = verify_crate(&cfg_for(&crate_dir.path)).unwrap_err();
    assert!(
        err.message.starts_with("proof [id]: unproved function body"),
        "expected structured Lean rejection despite spoofed .anneal/, got: {err}"
    );
}

#[test]
fn rejects_candidate_features_by_default_without_opt_in() {
    let crate_dir = TempCrateDir::with("default-vetted-only", ID_SPEC, false);
    let err = verify_crate(&cfg_for(&crate_dir.path)).unwrap_err();
    assert!(
        err.message
            .contains("verification requires candidate TCB features"),
        "got: {err}"
    );
}

#[test]
fn rejects_candidate_features_on_stable_release_channel() {
    let crate_dir = TempCrateDir::new("stable", ID_SPEC);
    let mut cfg = cfg_for(&crate_dir.path);
    cfg.release_channel = ReleaseChannel::Stable;
    let err = verify_crate(&cfg).unwrap_err();
    assert!(err.message.contains("stable release channel"), "got: {err}");
}

#[test]
fn verifies_via_cli_flag_and_emits_candidate_tcb_audit_section() {
    let crate_dir = TempCrateDir::with("cli-allow", ID_SPEC, false);
    let output = cli()
        .arg("--allow-candidate-features")
        .arg("*")
        .arg(&crate_dir.path)
        .output()
        .unwrap();
    let stdout = assert_cli_success(&output);
    assert!(
        stdout.contains("Candidate-Trusted TCB (Unvetted / Alpha):"),
        "{stdout}"
    );
    assert!(stdout.contains("[candidate-tcb-audit]"), "{stdout}");
}

#[test]
fn rejects_symlinked_manifest_and_lib_rs_and_extra_targets() {
    let rejected = |c: &TempCrateDir| {
        let err = verify_crate(&cfg_for(&c.path)).unwrap_err();
        assert!(err.message.contains("target-crate:"), "got: {err}");
    };
    let c = TempCrateDir::new("symlink-lib", ID_PLAIN);
    fs::rename(c.path.join("src/lib.rs"), c.path.join("lib.rs.real")).unwrap();
    symlink(c.path.join("lib.rs.real"), c.path.join("src/lib.rs")).unwrap();
    rejected(&c);

    let c = TempCrateDir::new("symlink-toml", ID_PLAIN);
    fs::rename(c.path.join("Cargo.toml"), c.path.join("real.toml")).unwrap();
    symlink(c.path.join("real.toml"), c.path.join("Cargo.toml")).unwrap();
    rejected(&c);

    for extra in ["build.rs", "src/main.rs", "src/proof.lean"] {
        let c = TempCrateDir::new("extra", ID_PLAIN);
        fs::write(c.path.join(extra), b"fn main() {}\n").unwrap();
        rejected(&c);
    }

    let c = TempCrateDir::new("bin-target", ID_PLAIN);
    let toml = fs::read_to_string(c.path.join("Cargo.toml")).unwrap();
    fs::write(
        c.path.join("Cargo.toml"),
        format!("{toml}\n[[bin]]\nname = \"helper\"\npath = \"src/lib.rs\"\n"),
    )
    .unwrap();
    rejected(&c);
}

#[test]
fn verifies_under_hostile_environment_and_cargo_configs() {
    let crate_dir = TempCrateDir::new("hostile-env", ID_PLAIN);
    let evil = tempfile::Builder::new()
        .prefix("anneal-evil-")
        .tempdir_in("/tmp")
        .unwrap();
    let e = evil.path();
    let config =
        "[build]\nrustc-wrapper = \"/bin/false\"\nrustflags = [\"--cfg\", \"evil\"]\n";
    fs::create_dir_all(e.join(".cargo")).unwrap();
    fs::write(e.join(".cargo/config.toml"), config).unwrap();
    fs::write(e.join("config.toml"), config).unwrap();
    fs::create_dir_all(e.join("work")).unwrap();
    fs::create_dir_all(e.join("lib")).unwrap();
    for lib in ["libleanshared.so", "librustc_driver-5d5a3c5207375ffc.so"] {
        fs::write(e.join("lib").join(lib), b"not an ELF file").unwrap();
    }

    let output = cli()
        .arg(&crate_dir.path)
        .current_dir(e.join("work"))
        .env("CARGO_HOME", e)
        .env("HOME", e)
        .env("XDG_CACHE_HOME", e)
        .env("RUSTC", "/bin/false")
        .env("RUSTC_WRAPPER", "/bin/false")
        .env("RUSTFLAGS", "--cfg evil")
        .env("RUSTC_LOG", "debug")
        .env("LD_LIBRARY_PATH", e.join("lib"))
        .env("LEAN_PATH", e)
        .output()
        .expect("invoke cargo-anneal binary");
    assert_cli_success(&output);
}

#[test]
fn rejects_ancestor_cargo_config_or_rust_toolchain() {
    for rel in [
        ".cargo/config",
        ".cargo/config.toml",
        "rust-toolchain",
        "rust-toolchain.toml",
    ] {
        let parent = tempfile::Builder::new()
            .prefix("anneal-ancestor-config-")
            .tempdir_in("/tmp")
            .unwrap();
        let crate_path = parent.path().join("sub/sample");
        fs::create_dir_all(crate_path.join("src")).unwrap();
        fs::write(
            crate_path.join("Cargo.toml"),
            format!(
                "[package]\nname = \"sample\"\nversion = \"0.1.0\"\n\
                 edition = \"2024\"\n\n{POLICY}"
            ),
        )
        .unwrap();
        fs::write(crate_path.join("src/lib.rs"), ID_PLAIN).unwrap();

        let bad_file = parent.path().join(rel);
        if let Some(dir) = bad_file.parent() {
            fs::create_dir_all(dir).unwrap();
        }
        fs::write(&bad_file, "disallowed\n").unwrap();
        let err = verify_crate(&cfg_for(&crate_path)).unwrap_err();
        assert!(
            err.message
                .contains("disallowed toolchain or Cargo config"),
            "expected ancestor {rel} rejection, got: {err}"
        );
    }
}

#[test]
fn rejects_external_file_inclusion_via_path_attribute() {
    let ext_dir = tempfile::Builder::new()
        .prefix("anneal-ext-src-")
        .tempdir_in("/tmp")
        .unwrap();
    let ext_file = ext_dir.path().join("outside.rs");
    fs::write(&ext_file, "pub fn helper(x: usize) -> usize { x }\n").unwrap();

    let src = format!(
        "#[path = {:?}]\npub mod outside;\npub fn id(x: usize) -> usize {{ outside::helper(x) }}\n",
        ext_file.display().to_string()
    );
    let crate_dir = TempCrateDir::new("path-attr-outside", &src);
    let err = verify_crate(&cfg_for(&crate_dir.path)).unwrap_err();
    assert!(
        err.message.contains("outside staged src/lib.rs"),
        "expected dep-info rejection for #[path = ...], got: {err}"
    );
}

#[test]
fn rejects_tampered_anneal_root_sources() {
    let crate_dir = TempCrateDir::new("tampered-root", ID_PLAIN);
    let fake_root = tempfile::Builder::new()
        .prefix("anneal-tampered-root-")
        .tempdir_in("/tmp")
        .unwrap();
    let real_root = anneal_root();
    let manifest = fs::read_to_string(
        real_root.join("trusted/cargo-anneal/src/anneal-sources.sha256"),
    )
    .unwrap();
    for line in manifest.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let (_, rel) = trimmed.split_once("  ").unwrap();
        let dst = fake_root.path().join(rel);
        if let Some(parent) = dst.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::copy(real_root.join(rel), dst).unwrap();
    }
    fs::write(
        fake_root.path().join("theory/Anneal.lean"),
        b"-- tampered\n",
    )
    .unwrap();

    let mut cfg = cfg_for(&crate_dir.path);
    cfg.anneal_root = fake_root.path().to_path_buf();
    let err = verify_crate(&cfg).unwrap_err();
    assert!(
        err.message.contains("does not match compiled-in sources"),
        "expected tampered anneal_root rejection, got: {err}"
    );
}
