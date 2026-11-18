// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Declarative integration test suite and host-boundary security tests for
//! `cargo-anneal verify` over `Trusted.MirModel`, `Trusted.MirSemantics`, and
//! `Anneal.MirWp`.
//!
//! Fixture corpus files live under `tests/fixtures/*.rs` (top-level `.rs`
//! files). Each file contains one or more `// === case: <name> ===` sections
//! with `//@ ...` expectation directives:
//!
//! - `//@ pass`
//! - `//@ fail(capture): "<expected substring>"`
//! - `//@ fail(proof, <fn_name_or_crate>): "<expected substring>"`
//! - `//@ known_bug(#<issue>, capture): "<expected substring>"`
//! - `//@ known_bug(#<issue>, proof, <fn_name_or_crate>): "<expected substring>"`
//! - `//@ mir-contains: "<substring in Captured.lean>"`
//! - `//@ mir-not-contains: "<substring in Captured.lean>"`
//!
//! Environment controls:
//! - `ANNEAL_TEST_FILTER=<substr>`: run only cases whose `<stem>::<case>`
//!   matches `<substr>`.
//! - `ANNEAL_BLESS=1`: update failed diagnostic substrings/scopes in place and
//!   promote resolved `known_bug` cases to `//@ pass`, without ever flipping
//!   pass/fail polarity.
//! - `ANNEAL_KEEP_SANDBOX=1`: retain temporary crate/proof/artifact sandboxes.

use serde_json::Value;
use std::collections::BTreeMap;
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, Mutex, OnceLock};
use std::thread;
use tempfile::TempDir;

// ---------------------------------------------------------------------------
// Tool discovery
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct Tools {
    cli: PathBuf,
    capture: PathBuf,
    lean: PathBuf,
    sysroot: PathBuf,
}

impl Tools {
    fn discover() -> Self {
        let install_root = override_path("ANNEAL_TEST_INSTALL_ROOT");
        let cli = override_path("ANNEAL_CLI")
            .or_else(|| override_path("ANNEAL_MVP_CLI"))
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_BIN_EXE_cargo-anneal")));
        let cli = required_file(cli, "cargo-anneal", "ANNEAL_CLI");
        let capture = override_path("ANNEAL_CAPTURE")
            .or_else(|| override_path("ANNEAL_MVP_CAPTURE"))
            .or_else(|| {
                let sibling = cli.with_file_name("anneal-rustc-capture");
                sibling.is_file().then_some(sibling)
            })
            .or_else(|| install_root.as_ref().map(|r| r.join("bin/anneal-rustc-capture")))
            .unwrap_or_else(|| cli.with_file_name("anneal-rustc-capture"));
        let capture = required_file(
            capture,
            "anneal-rustc-capture; build it before running this test",
            "ANNEAL_CAPTURE",
        );
        let lean = override_path("ANNEAL_LEAN")
            .or_else(|| override_path("ANNEAL_MVP_LEAN"))
            .or_else(|| install_root.as_ref().map(|r| r.join("lean/bin/lean")))
            .unwrap_or_else(cargo_anneal::default_lean_path);
        let lean = required_file(lean, "the pinned Lean executable", "ANNEAL_LEAN");
        let sysroot = override_path("ANNEAL_SYSROOT")
            .or_else(|| override_path("ANNEAL_MVP_SYSROOT"))
            .or_else(|| override_path("ANNEAL_TEST_RUST_SYSROOT"))
            .or_else(|| install_root.as_ref().map(|r| r.join("rust")))
            .unwrap_or_else(|| {
                for toolchain in [
                    "nightly-2026-10-23",
                    "nightly-2026-06-01",
                    "nightly-2026-05-31",
                ] {
                    if let Ok(output) = Command::new("rustup")
                        .args(["run", toolchain, "rustc", "--print", "sysroot"])
                        .output()
                        && output.status.success()
                    {
                        return PathBuf::from(
                            String::from_utf8(output.stdout)
                                .expect("rustc sysroot must be UTF-8")
                                .trim(),
                        );
                    }
                }
                let output = Command::new("rustc")
                    .args(["--print", "sysroot"])
                    .output()
                    .expect("install the pinned compiler or set ANNEAL_SYSROOT");
                assert!(
                    output.status.success(),
                    "cannot find the pinned compiler sysroot; set ANNEAL_SYSROOT:\n{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                PathBuf::from(
                    String::from_utf8(output.stdout)
                        .expect("rustc sysroot must be UTF-8")
                        .trim(),
                )
            });
        assert!(
            sysroot.join("lib").is_dir(),
            "missing compiler sysroot {}; set ANNEAL_SYSROOT",
            sysroot.display()
        );
        Self {
            cli,
            capture,
            lean,
            sysroot,
        }
    }

    fn command(&self) -> Command {
        let mut command = Command::new(&self.cli);
        command
            .arg("verify")
            .arg("--capture")
            .arg(&self.capture)
            .arg("--lean")
            .arg(&self.lean)
            .arg("--sysroot")
            .arg(&self.sysroot);
        command
    }
}

fn override_path(var: &str) -> Option<PathBuf> {
    env::var_os(var).filter(|v| !v.is_empty()).map(PathBuf::from)
}

fn required_file(path: PathBuf, label: &str, var: &str) -> PathBuf {
    assert!(
        path.is_file(),
        "cannot find {label} at {}; set {var}",
        path.display()
    );
    path
}

// ---------------------------------------------------------------------------
// Declarative fixture directive AST & fail-closed parser
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum FailureStage {
    Capture,
    Proof { scope: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct StageFailure {
    stage: FailureStage,
    diagnostic: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum PrimaryExpectation {
    Pass,
    Fail {
        stage: FailureStage,
        substring: String,
    },
    KnownBug {
        issue: u32,
        stage: FailureStage,
        substring: String,
    },
}

#[derive(Debug, Clone)]
struct FixtureCase {
    suite: String,
    name: String,
    file_path: PathBuf,
    primary_line_idx: usize,
    expectation: PrimaryExpectation,
    mir_contains: Vec<String>,
    mir_not_contains: Vec<String>,
    source: String,
}

impl FixtureCase {
    fn full_name(&self) -> String {
        format!("{}::{}", self.suite, self.name)
    }
}

fn parse_quoted_non_empty(raw: &str, ctx: &str) -> Result<String, String> {
    let trimmed = raw.trim();
    let val: String = serde_json::from_str(trimmed)
        .map_err(|_| format!("{ctx}: expected non-empty string literal, got {trimmed:?}"))?;
    if val.is_empty() {
        return Err(format!("{ctx}: expected non-empty string literal"));
    }
    Ok(val)
}

fn parse_stage_args(args: &[&str], ctx: &str) -> Result<FailureStage, String> {
    match args {
        ["capture"] => Ok(FailureStage::Capture),
        ["capture", ..] => Err(format!("{ctx}: `capture` stage does not take a scope")),
        ["proof"] => Err(format!(
            "{ctx}: `proof` stage requires a scope (`proof, <fn_or_crate>`)"
        )),
        ["proof", scope] => {
            let scope = scope.trim();
            if scope.is_empty()
                || !scope
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || c == '_')
            {
                return Err(format!("{ctx}: invalid proof scope {scope:?}"));
            }
            Ok(FailureStage::Proof {
                scope: scope.to_owned(),
            })
        }
        _ => Err(format!("{ctx}: unrecognized stage specification {args:?}")),
    }
}

fn parse_fixture_file(
    suite: &str,
    file_path: &Path,
    content: &str,
) -> Result<Vec<FixtureCase>, String> {
    let lines: Vec<&str> = content.lines().collect();
    let mut sections: Vec<(String, usize, usize)> = Vec::new();
    for (idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("// === case:") {
            let name = rest
                .strip_suffix("===")
                .ok_or_else(|| {
                    format!(
                        "{}:{}: malformed `// === case: <name> ===` header",
                        file_path.display(),
                        idx + 1
                    )
                })?
                .trim();
            if name.is_empty()
                || !name
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || c == '_')
            {
                return Err(format!(
                    "{}:{}: invalid case name {name:?}",
                    file_path.display(),
                    idx + 1
                ));
            }
            if let Some(last) = sections.last_mut() {
                last.2 = idx;
            }
            sections.push((name.to_owned(), idx + 1, lines.len()));
        }
    }
    if sections.is_empty() {
        sections.push(("default".to_owned(), 0, lines.len()));
    }

    let mut cases = Vec::with_capacity(sections.len());
    for (name, start, end) in sections {
        let mut primary: Option<(usize, PrimaryExpectation)> = None;
        let mut mir_contains = Vec::new();
        let mut mir_not_contains = Vec::new();
        let mut source_lines = Vec::new();

        for (offset, &line) in lines[start..end].iter().enumerate() {
            let line_idx = start + offset;
            let loc = format!("{}:{}: ({suite}::{name})", file_path.display(), line_idx + 1);
            let trimmed = line.trim();
            if let Some(directive) = trimmed.strip_prefix("//@") {
                let directive = directive.trim();
                let parsed_primary = if directive == "pass" {
                    Some(PrimaryExpectation::Pass)
                } else if let Some(rest) = directive.strip_prefix("fail(") {
                    let (inside, after) = rest
                        .split_once("):")
                        .ok_or_else(|| format!("{loc}: malformed `fail(...)` directive"))?;
                    let parts: Vec<&str> = inside.split(',').map(str::trim).collect();
                    let stage = parse_stage_args(&parts, &loc)?;
                    let substring = parse_quoted_non_empty(after, &loc)?;
                    Some(PrimaryExpectation::Fail { stage, substring })
                } else if let Some(rest) = directive.strip_prefix("known_bug(") {
                    let (inside, after) = rest
                        .split_once("):")
                        .ok_or_else(|| format!("{loc}: malformed `known_bug(...)` directive"))?;
                    let parts: Vec<&str> = inside.split(',').map(str::trim).collect();
                    if parts.len() < 2 {
                        return Err(format!("{loc}: `known_bug` requires `(#<issue>, <stage>)`"));
                    }
                    let issue_raw = parts[0]
                        .strip_prefix('#')
                        .ok_or_else(|| format!("{loc}: invalid issue reference {:?}", parts[0]))?;
                    let issue: u32 = issue_raw
                        .parse()
                        .map_err(|_| format!("{loc}: invalid issue reference {:?}", parts[0]))?;
                    if issue == 0 {
                        return Err(format!("{loc}: invalid issue reference {:?}", parts[0]));
                    }
                    let stage = parse_stage_args(&parts[1..], &loc)?;
                    let substring = parse_quoted_non_empty(after, &loc)?;
                    Some(PrimaryExpectation::KnownBug {
                        issue,
                        stage,
                        substring,
                    })
                } else if let Some(after) = directive.strip_prefix("mir-contains:") {
                    mir_contains.push(parse_quoted_non_empty(after, &loc)?);
                    None
                } else if let Some(after) = directive.strip_prefix("mir-not-contains:") {
                    mir_not_contains.push(parse_quoted_non_empty(after, &loc)?);
                    None
                } else {
                    return Err(format!("{loc}: unknown directive `//@ {directive}`"));
                };

                if let Some(exp) = parsed_primary {
                    if primary.is_some() {
                        return Err(format!(
                            "{loc}: multiple primary expectation directives in one case"
                        ));
                    }
                    primary = Some((line_idx, exp));
                }
            } else if start == 0
                && offset < 8
                && trimmed.starts_with("//")
                && !trimmed.starts_with("///")
                && !trimmed.starts_with("//!")
            {
                // Skip leading license comments in single-case files without
                // stripping `///` or `//!` doc comments.
            } else {
                source_lines.push(line);
            }
        }

        let (primary_line_idx, expectation) = primary.ok_or_else(|| {
            format!(
                "{}:{}: ({suite}::{name}): missing primary expectation directive",
                file_path.display(),
                start + 1
            )
        })?;

        if matches!(
            expectation,
            PrimaryExpectation::Fail {
                stage: FailureStage::Capture,
                ..
            } | PrimaryExpectation::KnownBug {
                stage: FailureStage::Capture,
                ..
            }
        ) && (!mir_contains.is_empty() || !mir_not_contains.is_empty())
        {
            return Err(format!(
                "{}:{}: ({suite}::{name}): `mir-contains` / `mir-not-contains` cannot be used on `capture`-stage failures",
                file_path.display(),
                primary_line_idx + 1
            ));
        }

        let mut source = source_lines.join("\n");
        source.push('\n');
        cases.push(FixtureCase {
            suite: suite.to_owned(),
            name,
            file_path: file_path.to_path_buf(),
            primary_line_idx,
            expectation,
            mir_contains,
            mir_not_contains,
            source,
        });
    }
    Ok(cases)
}

// ---------------------------------------------------------------------------
// Bless support (polarity-safe)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct BlessPatch {
    file_path: PathBuf,
    line_idx: usize,
    replacement: String,
}

#[derive(Debug)]
enum CaseOutcome {
    Passed,
    Blessed(BlessPatch),
    Failed(String),
}

#[derive(Debug, Clone)]
struct VerifyReport {
    mir_lean: String,
    output_text: String,
}

#[derive(Debug, Clone)]
struct VerifyError {
    message: String,
    failure: Option<StageFailure>,
    mir_lean: Option<String>,
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

fn format_stage(stage: &FailureStage) -> String {
    match stage {
        FailureStage::Capture => "capture".to_owned(),
        FailureStage::Proof { scope } => format!("proof, {scope}"),
    }
}

fn first_clean_line(diag: &str) -> String {
    diag.lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .unwrap_or("verification failed")
        .to_owned()
}

fn normalize_mir_dialect_needle(needle: &str, mir: &str) -> String {
    for dialect in [
        "V2026_10_22_R7189d39d9",
        "V2026_05_31_R14210df0e",
        "V2026_05_30_Rf8a08b688",
    ] {
        if mir.contains(&format!("import Trusted.Rustc.{dialect}.MirAst")) {
            return needle.replace(
                "Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.",
                &format!("Trusted.Rustc.{dialect}.MirAst."),
            );
        }
    }
    needle.to_owned()
}

fn check_mir_assertions(case: &FixtureCase, mir_lean: Option<&str>) -> Result<(), String> {
    if case.mir_contains.is_empty() && case.mir_not_contains.is_empty() {
        return Ok(());
    }
    let Some(mir) = mir_lean else {
        return Err("expected Captured.lean to be emitted for MIR assertions, but none was found"
            .to_owned());
    };
    for needle in &case.mir_contains {
        let normalized = normalize_mir_dialect_needle(needle, mir);
        if !mir.contains(needle) && !mir.contains(&normalized) {
            return Err(format!(
                "Captured.lean did not contain expected substring {needle:?}\n--- Captured.lean ---\n{mir}"
            ));
        }
    }
    for needle in &case.mir_not_contains {
        let normalized = normalize_mir_dialect_needle(needle, mir);
        if mir.contains(needle) || mir.contains(&normalized) {
            return Err(format!(
                "Captured.lean unexpectedly contained forbidden substring {needle:?}\n--- Captured.lean ---\n{mir}"
            ));
        }
    }
    Ok(())
}

fn evaluate_case(
    case: &FixtureCase,
    result: &Result<VerifyReport, VerifyError>,
    bless: bool,
) -> CaseOutcome {
    match (&case.expectation, result) {
        (PrimaryExpectation::Pass, Ok(report)) => {
            if let Err(e) = check_mir_assertions(case, Some(&report.mir_lean)) {
                CaseOutcome::Failed(e)
            } else {
                CaseOutcome::Passed
            }
        }
        (PrimaryExpectation::Pass, Err(err)) => {
            // Polarity-safe: never auto-flip `//@ pass` to `//@ fail(...)`.
            CaseOutcome::Failed(format!("expected `//@ pass`, got failure:\n{}", err.message))
        }
        (PrimaryExpectation::Fail { .. }, Ok(report)) => {
            // Polarity-safe: never auto-flip `//@ fail(...)` to `//@ pass`.
            CaseOutcome::Failed(format!(
                "expected failure, but verification succeeded:\n{}",
                report.output_text
            ))
        }
        (
            PrimaryExpectation::Fail {
                stage: exp_stage,
                substring,
            },
            Err(err),
        ) => {
            let Some(actual) = &err.failure else {
                return CaseOutcome::Failed(format!(
                    "expected structured failure, got operational error:\n{}",
                    err.message
                ));
            };
            if let Err(e) = check_mir_assertions(case, err.mir_lean.as_deref()) {
                return CaseOutcome::Failed(e);
            }
            if &actual.stage == exp_stage && actual.diagnostic.contains(substring) {
                CaseOutcome::Passed
            } else if bless {
                let quoted = serde_json::to_string(&first_clean_line(&actual.diagnostic)).unwrap();
                CaseOutcome::Blessed(BlessPatch {
                    file_path: case.file_path.clone(),
                    line_idx: case.primary_line_idx,
                    replacement: format!("//@ fail({}): {quoted}", format_stage(&actual.stage)),
                })
            } else {
                CaseOutcome::Failed(format!(
                    "failure mismatch:\n  expected stage: {:?} containing {:?}\n  actual stage:   {:?}\n  diagnostic:     {}",
                    exp_stage, substring, actual.stage, actual.diagnostic
                ))
            }
        }
        (PrimaryExpectation::KnownBug { issue, .. }, Ok(report)) => {
            if bless {
                CaseOutcome::Blessed(BlessPatch {
                    file_path: case.file_path.clone(),
                    line_idx: case.primary_line_idx,
                    replacement: "//@ pass".to_owned(),
                })
            } else {
                CaseOutcome::Failed(format!(
                    "`known_bug(#{issue})` now passes! Re-run with `ANNEAL_BLESS=1` to promote it to `//@ pass`.\nReceipt:\n{}",
                    report.output_text
                ))
            }
        }
        (
            PrimaryExpectation::KnownBug {
                issue,
                stage: exp_stage,
                substring,
            },
            Err(err),
        ) => {
            let Some(actual) = &err.failure else {
                return CaseOutcome::Failed(format!(
                    "expected structured known_bug failure, got operational error:\n{}",
                    err.message
                ));
            };
            if let Err(e) = check_mir_assertions(case, err.mir_lean.as_deref()) {
                return CaseOutcome::Failed(e);
            }
            if &actual.stage == exp_stage && actual.diagnostic.contains(substring) {
                CaseOutcome::Passed
            } else if bless {
                let quoted = serde_json::to_string(&first_clean_line(&actual.diagnostic)).unwrap();
                CaseOutcome::Blessed(BlessPatch {
                    file_path: case.file_path.clone(),
                    line_idx: case.primary_line_idx,
                    replacement: format!(
                        "//@ known_bug(#{issue}, {}): {quoted}",
                        format_stage(&actual.stage)
                    ),
                })
            } else {
                CaseOutcome::Failed(format!(
                    "known_bug(#{issue}) mismatch:\n  expected stage: {:?} containing {:?}\n  actual stage:   {:?}\n  diagnostic:     {}",
                    exp_stage, substring, actual.stage, actual.diagnostic
                ))
            }
        }
    }
}

fn apply_bless_patches(patches: &[BlessPatch]) -> Result<(), String> {
    let mut by_file: BTreeMap<PathBuf, Vec<&BlessPatch>> = BTreeMap::new();
    for patch in patches {
        by_file
            .entry(patch.file_path.clone())
            .or_default()
            .push(patch);
    }
    for (path, file_patches) in by_file {
        let content = fs::read_to_string(&path)
            .map_err(|e| format!("failed to read {} for bless: {e}", path.display()))?;
        let mut lines: Vec<String> = content.lines().map(str::to_owned).collect();
        for patch in file_patches {
            if patch.line_idx >= lines.len() {
                return Err(format!(
                    "bless line index {} out of bounds for {}",
                    patch.line_idx,
                    path.display()
                ));
            }
            lines[patch.line_idx] = patch.replacement.clone();
        }
        let mut out = lines.join("\n");
        out.push('\n');
        fs::write(&path, out)
            .map_err(|e| format!("failed to write blessed {}: {e}", path.display()))?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Lightweight Rust spec parser & Lean Spec/Proof synthesizer
// ---------------------------------------------------------------------------

const LICENSE_HEADER: &str = "\
-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

";

const LEAN_PROOF_HELPERS: &str = r#"theorem validArgs1 {args : List Val} {ty : MirTy}
    (h : checkArgsMatch args [ty] = true) :
    ∃ v, args = [v] ∧ checkVal v ty = true := by
  cases args with
  | nil => cases h
  | cons v rest =>
    unfold checkArgsMatch at h
    cases hv : checkVal v ty with
    | false => rw [hv] at h; cases h
    | true =>
      rw [hv] at h
      cases rest with
      | nil => exact ⟨v, rfl, hv⟩
      | cons _ _ => cases h

theorem validArgs2 {args : List Val} {t1 t2 : MirTy}
    (h : checkArgsMatch args [t1, t2] = true) :
    ∃ v1 v2, args = [v1, v2] ∧ checkVal v1 t1 = true ∧ checkVal v2 t2 = true := by
  cases args with
  | nil => cases h
  | cons v1 rest =>
    unfold checkArgsMatch at h
    cases hv1 : checkVal v1 t1 with
    | false => rw [hv1] at h; cases h
    | true =>
      rw [hv1] at h
      have h2 : checkArgsMatch rest [t2] = true := h
      let ⟨v2, heq, hv2⟩ := validArgs1 h2
      subst heq
      exact ⟨v1, v2, rfl, hv1, hv2⟩

theorem mirTy_int_inj {w1 w2 : IntWidth} {s1 s2 : Bool}
    (h : MirTy.beq (.int w1 s1) (.int w2 s2) = true) :
    w1 = w2 ∧ s1 = s2 := by
  cases w1 <;> cases w2 <;> cases s1 <;> cases s2 <;> first | exact ⟨rfl, rfl⟩ | cases h

theorem checkVal_scalar_inv {v : Val} {w : IntWidth} {s : Bool}
    (h : checkVal v (.int w s) = true) :
    ∃ bits : BitVec 128,
      v = .scalar ⟨w, s, bits⟩ ∧ (truncateBits w bits == bits) = true := by
  unfold checkVal Val.ty? at h
  cases v with
  | scalar sv =>
    cases sv with
    | mk sw ss bits =>
      cases hw : ScalarVal.wf ⟨sw, ss, bits⟩ with
      | false =>
        change (match (if ScalarVal.wf ⟨sw, ss, bits⟩ then some (MirTy.int sw ss) else none) with | some vTy => vTy.beq (.int w s) | none => false) = true at h
        rw [hw] at h; cases h
      | true =>
        change (match (if ScalarVal.wf ⟨sw, ss, bits⟩ then some (MirTy.int sw ss) else none) with | some vTy => vTy.beq (.int w s) | none => false) = true at h
        rw [hw] at h
        let ⟨h_w, h_s⟩ := mirTy_int_inj h
        subst h_w; subst h_s
        exact ⟨bits, rfl, hw⟩
  | ptr _ => cases h
  | bool _ => cases h
  | unit => cases h
  | tuple _ => cases h
  | bytes _ => cases h
  | enumVal ety var =>
    change (match (if enumAdmitted ety && Nat.blt var ety.discriminants.length then some (MirTy.enum ety) else none) with | some vTy => vTy.beq (.int w s) | none => false) = true at h
    cases he : (enumAdmitted ety && Nat.blt var ety.discriminants.length) <;> rw [he] at h <;> cases h

theorem truncateBits_i32_idem (x : BitVec 128) :
    truncateBits .i32 (truncateBits .i32 x) = truncateBits .i32 x := by
  let b : BitVec 32 := bvExtractLsb 31 0 x
  have hb : (bvZeroExtend 128 b).toNat = b.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (by decide))
  have hb32 : BitVec.ofNat 32 (bvZeroExtend 128 b).toNat = b := by
    apply bitVec_eq_of_toNat_eq
    change Nat.mod (bvZeroExtend 128 b).toNat (Nat.pow 2 32) = b.toNat
    rw [hb]
    exact Nat.mod_eq_of_lt b.isLt
  change bvZeroExtend 128 (BitVec.ofNat 32 (bvZeroExtend 128 b).toNat) =
    bvZeroExtend 128 b
  rw [hb32]

theorem checkVal_u32_truncateBits (x : BitVec 128) :
    checkVal (.scalar ⟨.i32, false, truncateBits .i32 x⟩) (.int .i32 false) =
      true := by
  have h_eq :
      (truncateBits .i32 (truncateBits .i32 x) == truncateBits .i32 x) =
      true := by
    rw [truncateBits_i32_idem]
    exact beq_self_eq_true (truncateBits .i32 x)
  change (match (if (truncateBits .i32 (truncateBits .i32 x) == truncateBits .i32 x) then some (MirTy.int .i32 false) else none) with | some vTy => vTy.beq (.int .i32 false) | none => false) = true
  rw [h_eq]
  rfl

theorem evalBinOp_u32_add (b1 b2 : BitVec 128) :
    evalBinOp .add (.scalar ⟨.i32, false, b1⟩) (.scalar ⟨.i32, false, b2⟩) =
      .ok (.scalar ⟨.i32, false, truncateBits .i32 (bvOfInt 128 (decodeScalar ⟨.i32, false, b1⟩ + decodeScalar ⟨.i32, false, b2⟩))⟩) := by
  unfold evalBinOp evalArithOp truncateScalar
  change (if _ && false then Except.error FaultKind.undefined else _) = _
  rw [Bool.and_false]
  rfl

theorem natListBeq_eq {xs ys : List Nat} (h : natListBeq xs ys = true) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      change (Nat.beq x y && natListBeq xs ys) = true at h
      have h1 : Nat.beq x y = true := by
        cases h_xy : Nat.beq x y
        · rw [h_xy] at h; cases h
        · rfl
      have h2 : natListBeq xs ys = true := by
        rw [h1] at h; exact h
      rw [Nat.eq_of_beq_eq_true h1, ih h2]

theorem intWidth_beq_eq {w1 w2 : IntWidth}
    (h : IntWidth.beq w1 w2 = true) : w1 = w2 := by
  cases w1 <;> cases w2 <;> first | rfl | cases h

theorem enumTagRepr_beq_eq {r1 r2 : EnumTagRepr}
    (h : EnumTagRepr.beq r1 r2 = true) : r1 = r2 := by
  cases r1 with
  | zeroSized =>
    cases r2 with
    | zeroSized => rfl
    | scalar _ _ => cases h
  | scalar w1 s1 =>
    cases r2 with
    | zeroSized => cases h
    | scalar w2 s2 =>
      cases w1 <;> cases w2 <;> cases s1 <;> cases s2 <;> first | rfl | cases h

theorem enumTy_beq_eq {e1 e2 : EnumTy}
    (h : EnumTy.beq e1 e2 = true) : e1 = e2 := by
  cases e1 with
  | mk id1 dw1 ds1 tr1 discs1 =>
    cases e2 with
    | mk id2 dw2 ds2 tr2 discs2 =>
      unfold EnumTy.beq at h
      dsimp only at h
      cases h1 : Nat.beq id1 id2 <;>
        cases h2 : IntWidth.beq dw1 dw2 <;>
        cases h3 : (ds1 == ds2) <;>
        cases h4 : EnumTagRepr.beq tr1 tr2 <;>
        cases h5 : natListBeq discs1 discs2 <;>
        rw [h1, h2, h3, h4, h5] at h <;>
        try cases h
      rw [Nat.eq_of_beq_eq_true h1, intWidth_beq_eq h2, eq_of_beq h3,
        enumTagRepr_beq_eq h4, natListBeq_eq h5]

theorem checkVal_enum2_inv {ety : EnumTy}
    (h_ds : ety.discriminants = [0, 1]) {v : Val}
    (h : checkVal v (.enum ety) = true) :
    v = .enumVal ety 0 ∨ v = .enumVal ety 1 := by
  cases v with
  | enumVal ety' var =>
    cases h_adm : (enumAdmitted ety' && Nat.blt var ety'.discriminants.length) with
    | false => simp [checkVal, Val.ty?, h_adm] at h
    | true =>
      have h_ty : MirTy.beq (.enum ety') (.enum ety) = true := by
        unfold checkVal Val.ty? at h
        dsimp only at h
        rw [h_adm] at h
        exact h
      unfold MirTy.beq at h_ty
      dsimp only at h_ty
      have h_eq := enumTy_beq_eq h_ty
      subst h_eq
      rw [h_ds] at h_adm
      cases h_e : enumAdmitted ety' with
      | false => rw [h_e] at h_adm; cases h_adm
      | true =>
        rw [h_e] at h_adm
        cases var with
        | zero => exact .inl rfl
        | succ n =>
          cases n with
          | zero => exact .inr rfl
          | succ m => cases h_adm
  | scalar sv =>
    cases h_wf : sv.wf <;> simp [checkVal, Val.ty?, h_wf, MirTy.beq] at h
  | ptr _ | bool _ | unit | tuple _ | bytes _ => cases h
"#;

#[derive(Debug, Clone)]
struct ParsedFn {
    name: String,
    is_unsafe: bool,
    params: Vec<(String, String)>,
    requires_nonzero: Option<String>,
    ensures_eq_param: Option<String>,
    body_norm: String,
}

#[derive(Debug, Clone)]
struct SynthesizedPackage {
    spec_lean: String,
    proof_lean: String,
    fn_line_ranges: Vec<(usize, usize, String)>,
}

fn normalize_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn parse_rust_functions(source: &str) -> Result<Vec<ParsedFn>, String> {
    let mut fns = Vec::new();
    let mut pending_requires: Vec<String> = Vec::new();
    let mut pending_specs: Vec<String> = Vec::new();
    let mut brace_depth: i32 = 0;

    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();
        if brace_depth == 0 {
            if let Some(doc) = trimmed.strip_prefix("///") {
                let doc = doc.trim();
                if let Some(req) = doc.strip_prefix("anneal:requires ") {
                    pending_requires.push(req.trim().to_owned());
                } else if let Some(sp) = doc.strip_prefix("anneal:spec ") {
                    pending_specs.push(sp.trim().to_owned());
                }
                i += 1;
                continue;
            }
            if trimmed.starts_with("#[") || trimmed.is_empty() || trimmed.starts_with("//") {
                i += 1;
                continue;
            }
            if let Some(fn_pos) = find_top_level_fn_header(trimmed) {
                // Collect signature + body until matching `}` back at depth 0.
                let mut chunk = String::new();
                let mut depth = 0i32;
                let mut saw_open = false;
                while i < lines.len() {
                    let l = lines[i];
                    if !chunk.is_empty() {
                        chunk.push('\n');
                    }
                    chunk.push_str(l);
                    for ch in l.chars() {
                        if ch == '{' {
                            depth += 1;
                            saw_open = true;
                        } else if ch == '}' {
                            depth -= 1;
                        }
                    }
                    i += 1;
                    if saw_open && depth <= 0 {
                        break;
                    }
                }
                if saw_open {
                    let parsed = parse_one_fn(
                        &chunk[fn_pos..],
                        &std::mem::take(&mut pending_requires),
                        &std::mem::take(&mut pending_specs),
                    )?;
                    fns.push(parsed);
                } else {
                    pending_requires.clear();
                    pending_specs.clear();
                }
                continue;
            }
            // Non-fn item at top level (struct, enum, trait, impl, use, etc.):
            // clear doc attributes attached to that item.
            if !trimmed.starts_with("#![") {
                pending_requires.clear();
                pending_specs.clear();
            }
        }
        for ch in trimmed.chars() {
            if ch == '{' {
                brace_depth += 1;
            } else if ch == '}' {
                brace_depth -= 1;
            }
        }
        i += 1;
    }
    Ok(fns)
}

fn find_top_level_fn_header(trimmed: &str) -> Option<usize> {
    for prefix in ["pub unsafe fn ", "unsafe fn ", "pub fn ", "fn "] {
        if trimmed.starts_with(prefix) {
            return Some(0);
        }
    }
    None
}

fn parse_one_fn(
    fn_chunk: &str,
    requires: &[String],
    specs: &[String],
) -> Result<ParsedFn, String> {
    let is_unsafe = fn_chunk.starts_with("pub unsafe fn ") || fn_chunk.starts_with("unsafe fn ");
    let after_fn = fn_chunk
        .split_once("fn ")
        .map(|(_, r)| r)
        .unwrap_or(fn_chunk);
    let open_paren = after_fn
        .find('(')
        .ok_or_else(|| format!("malformed fn header: {after_fn}"))?;
    let raw_name = after_fn[..open_paren].trim();
    let name = raw_name
        .split('<')
        .next()
        .unwrap_or(raw_name)
        .trim()
        .to_owned();
    let close_paren = after_fn[open_paren + 1..]
        .find(')')
        .map(|idx| open_paren + 1 + idx)
        .ok_or_else(|| format!("missing `)` in fn `{name}`"))?;
    let params_str = &after_fn[open_paren + 1..close_paren];
    let mut params = Vec::new();
    for p in params_str.split(',') {
        let p = p.trim();
        if p.is_empty() {
            continue;
        }
        if let Some((pname, pty)) = p.split_once(':') {
            let pname = pname.trim().trim_start_matches("mut ").trim().to_owned();
            let pty = pty.trim().to_owned();
            params.push((pname, pty));
        }
    }
    let open_brace = after_fn[close_paren + 1..]
        .find('{')
        .map(|idx| close_paren + 1 + idx)
        .unwrap_or(after_fn.len());
    let close_brace = after_fn.rfind('}').unwrap_or(after_fn.len());
    let body_raw = if open_brace < close_brace {
        &after_fn[open_brace + 1..close_brace]
    } else {
        ""
    };
    let body_norm = normalize_ws(body_raw);

    let mut requires_nonzero = None;
    for req in requires {
        if let Some((lhs, rhs)) = req.split_once("!=") {
            let lhs = lhs.trim();
            let rhs = rhs.trim();
            if !params.iter().any(|(pn, _)| pn == lhs) {
                return Err(format!(
                    "unknown identifier `{lhs}` in `anneal:requires {req}` on `{name}`"
                ));
            }
            if rhs == "0" {
                requires_nonzero = Some(lhs.to_owned());
            }
        } else {
            return Err(format!(
                "unsupported `anneal:requires {req}` syntax on `{name}`"
            ));
        }
    }

    let mut ensures_eq_param = None;
    for sp in specs {
        let inner = sp
            .strip_prefix("ensures(")
            .and_then(|s| s.strip_suffix(')'))
            .ok_or_else(|| format!("unsupported `anneal:spec {sp}` syntax on `{name}`"))?;
        if let Some((lhs, rhs)) = inner.split_once("==") {
            let lhs = lhs.trim();
            let rhs = rhs.trim();
            if lhs != "ret" {
                return Err(format!(
                    "expected `ret == <param>` in `anneal:spec {sp}` on `{name}`"
                ));
            }
            if !params.iter().any(|(pn, _)| pn == rhs) {
                return Err(format!(
                    "unknown identifier `{rhs}` in `anneal:spec {sp}` on `{name}`"
                ));
            }
            ensures_eq_param = Some(rhs.to_owned());
        } else {
            return Err(format!(
                "unsupported `anneal:spec {sp}` expression on `{name}`"
            ));
        }
    }

    Ok(ParsedFn {
        name,
        is_unsafe,
        params,
        requires_nonzero,
        ensures_eq_param,
        body_norm,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BodyPattern {
    DirectId,
    MoveId,
    ConstZero,
    U32Add,
    ClampNonzero,
    CustomMirNonzero,
    EnumTag,
    Unproved,
}

fn classify_body(f: &ParsedFn) -> BodyPattern {
    if f.params.len() == 1 && f.params[0].1 == "usize" {
        let p = &f.params[0].0;
        if f.body_norm == *p {
            return BodyPattern::DirectId;
        }
        if f.body_norm == format!("let y = {p}; y") {
            return BodyPattern::MoveId;
        }
        if f.body_norm == format!("let _ = {p}; 0") || f.body_norm == "0" {
            return BodyPattern::ConstZero;
        }
        if f.body_norm == format!("if {p} == 0 {{ 1 }} else {{ {p} }}") {
            return BodyPattern::ClampNonzero;
        }
        if f.body_norm.contains("mir!") && f.body_norm.contains("Unreachable()") {
            return BodyPattern::CustomMirNonzero;
        }
    }
    if f.params.len() == 2 && f.params[0].1 == "u32" && f.params[1].1 == "u32" {
        let (p0, p1) = (&f.params[0].0, &f.params[1].0);
        if f.body_norm == format!("{p0} + {p1}") {
            return BodyPattern::U32Add;
        }
    }
    if f.params.len() == 1 && f.params[0].1 == "E" && f.body_norm.contains("E::A => 0") {
        return BodyPattern::EnumTag;
    }
    if f.params.len() == 1
        && f.params[0].1 == "Single"
        && (f.body_norm == "0" || f.body_norm.ends_with("; 0"))
    {
        return BodyPattern::ConstZero;
    }
    BodyPattern::Unproved
}

fn synthesize_proof_package(source: &str) -> Result<SynthesizedPackage, String> {
    let fns = parse_rust_functions(source)?;

    // Build `Spec.lean`.
    let mut safety_branches = Vec::new();
    let mut prop_clauses: Vec<(usize, String)> = Vec::new();
    for (idx, f) in fns.iter().enumerate() {
        let pat = classify_body(f);
        // Caller safety preconditions attach to `custom_mir` functions carrying
        // `anneal:requires x != 0` (soundly usable by the proof only when
        // `selected.isUnsafe = true`).
        if f.requires_nonzero.is_some() && (f.is_unsafe || pat == BodyPattern::CustomMirNonzero) {
            safety_branches.push(format!(
                "(if identity == \"rust-path-v1::{}\" then args ≠ [.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩] else ",
                f.name
            ));
        }
        if f.ensures_eq_param.is_some() {
            let clause = if f.requires_nonzero.is_some() && !f.is_unsafe {
                format!(
                    "(∀ selected, Trusted.MirSemantics.getElem? p.bodies {idx} = some selected → \
                     ∀ v ret, ValidEntryArgs selected [v] → \
                     v ≠ .scalar ⟨.isize, false, BitVec.ofNat 128 0⟩ → \
                     Behavior (entryProgForBody p {idx}) {{ args := [v] }} (.returned ⟨ret, ⟨[]⟩⟩) → ret = v)"
                )
            } else {
                format!(
                    "(∀ selected, Trusted.MirSemantics.getElem? p.bodies {idx} = some selected → \
                     ∀ v ret, ValidEntryArgs selected [v] → \
                     Behavior (entryProgForBody p {idx}) {{ args := [v] }} (.returned ⟨ret, ⟨[]⟩⟩) → ret = v)"
                )
            };
            prop_clauses.push((idx, clause));
        }
    }

    let safety_expr = if safety_branches.is_empty() {
        "fun _ _ => False".to_owned()
    } else {
        let mut s = String::from("fun identity args => ");
        for b in &safety_branches {
            s.push_str(b);
        }
        s.push_str("False");
        for _ in &safety_branches {
            s.push(')');
        }
        s
    };

    let property_expr = if prop_clauses.is_empty() {
        "fun _ => True".to_owned()
    } else {
        let joined = prop_clauses
            .iter()
            .map(|(_, c)| c.as_str())
            .collect::<Vec<_>>()
            .join(" ∧ ");
        format!("fun p => {joined}")
    };

    let spec_lean = format!(
        r#"{LICENSE_HEADER}prelude
import Trusted.MirSemantics

namespace Spec
open Trusted.MirModel Trusted.MirSemantics

def specs : Specs where
  safety := {safety_expr}
  property := {property_expr}

end Spec
"#
    );

    // Build `Proof.lean` and record 1-based line ranges per function so Lean
    // compiler rejections map deterministically to `FailureStage::Proof { scope }`.
    let mut proof_lines: Vec<String> = Vec::new();
    let push_block = |lines: &mut Vec<String>, text: &str| {
        for l in text.lines() {
            lines.push(l.to_owned());
        }
    };

    push_block(
        &mut proof_lines,
        &format!(
            r#"{LICENSE_HEADER}prelude
import Expected
import Anneal.MirWp

namespace Proof
open Trusted.MirModel Trusted.MirSemantics Anneal.MirWp
noncomputable def program : Program := interpretV2026_10_22_R7189d39d9 Captured.program"#
        ),
    );

    if fns.is_empty() {
        push_block(
            &mut proof_lines,
            r#"theorem all_bodies_safe : ∀ id selected, Trusted.MirSemantics.getElem? program.bodies id = some selected →
    BodyVerified program id selected (Spec.specs.safety selected.identity) := by
  intro id _ found
  cases id <;> cases found
theorem verify : Expected.claim :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, all_bodies_safe, True.intro⟩
end Proof"#,
        );
        let mut proof_lean = proof_lines.join("\n");
        proof_lean.push('\n');
        return Ok(SynthesizedPackage {
            spec_lean,
            proof_lean,
            fn_line_ranges: Vec::new(),
        });
    }

    push_block(&mut proof_lines, LEAN_PROOF_HELPERS);

    let mut fn_line_ranges = Vec::new();
    for (i, f) in fns.iter().enumerate() {
        let start_line = proof_lines.len() + 1;
        let pat = classify_body(f);
        let mut block = String::new();
        let _ = writeln!(block, "noncomputable def b{i} : Body := program.bodies[{i}]");

        match pat {
            BodyPattern::DirectId => {
                let _ = writeln!(
                    block,
                    r#"theorem b{i}_exec (v : Val) (hv : checkVal v (.int .isize false) = true) :
    Executes b{i} (initial b{i} [v]) v := by
  have s0 : step b{i} (initial b{i} [v]) = .step ⟨[⟨0, 0, 1, [.live (some v), .live (some v)]⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live none, .live (some v)] 0 (.int .isize false) v with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 1, l'⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv]; rfl
  have s1 : step b{i} ⟨[⟨0, 0, 1, [.live (some v), .live (some v)]⟩], ⟨[]⟩⟩ = .done (.returned ⟨v, ⟨[]⟩⟩) := rfl
  exact .next s0 (.ret s1)
theorem b{i}_safe {{selected : Body}} (found : Trusted.MirSemantics.getElem? program.bodies {i} = some selected) :
    BodyVerified program {i} selected (Spec.specs.safety selected.identity) := by
  have same : b{i} = selected := Option.some.inj found
  subst selected
  refine bodyVerified_of_safe found rfl (fun args h_valid _ => ?_)
  let ⟨v, h_eq, hv⟩ := validArgs1 h_valid
  subst h_eq
  exact executes_safe (b{i}_exec v hv)"#
                );
                if f.ensures_eq_param.is_some() {
                    let _ = writeln!(
                        block,
                        r#"theorem b{i}_ens : ∀ selected, Trusted.MirSemantics.getElem? program.bodies {i} = some selected →
    ∀ v ret, ValidEntryArgs selected [v] → Behavior (entryProgForBody program {i}) {{ args := [v] }} (.returned ⟨ret, ⟨[]⟩⟩) → ret = v := by
  intro selected found v ret h_valid h_beh
  have h_ret : Returns selected [v] ret := (returns_of_behavior found h_beh).2
  have same : b{i} = selected := Option.some.inj found
  subst selected
  let ⟨v', h_eq, hv⟩ := validArgs1 h_valid
  injection h_eq with h_v
  subst h_v
  exact (executes_unique (b{i}_exec v hv) h_ret).symm"#
                    );
                }
            }
            BodyPattern::ConstZero => {
                let _ = writeln!(
                    block,
                    r#"theorem b{i}_runs (v : Val) :
    run b{i} 8 (initial b{i} [v]) = some (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) := rfl
theorem b{i}_safe {{selected : Body}} (found : Trusted.MirSemantics.getElem? program.bodies {i} = some selected) :
    BodyVerified program {i} selected (Spec.specs.safety selected.identity) := by
  have same : b{i} = selected := Option.some.inj found
  subst selected
  refine bodyVerified_of_safe found rfl (fun args h_valid _ => ?_)
  let ⟨v, h_eq, _⟩ := validArgs1 h_valid
  subst h_eq
  exact (run_initial_success (b{i}_runs v)).1"#
                );
                if f.ensures_eq_param.is_some() {
                    let _ = writeln!(
                        block,
                        r#"theorem b{i}_ens : ∀ selected, Trusted.MirSemantics.getElem? program.bodies {i} = some selected →
    ∀ v ret, ValidEntryArgs selected [v] → Behavior (entryProgForBody program {i}) {{ args := [v] }} (.returned ⟨ret, ⟨[]⟩⟩) → ret = v := by
  intro selected found v ret _ h_beh
  have h_ret : Returns selected [v] ret := (returns_of_behavior found h_beh).2
  have same : b{i} = selected := Option.some.inj found
  subst selected
  have h_zero : .scalar ⟨.isize, false, BitVec.ofNat 128 0⟩ = ret := run_result_unique (b{i}_runs v) h_ret
  exact h_zero.symm"#
                    );
                }
            }
            BodyPattern::Unproved => {
                let _ = writeln!(
                    block,
                    r#"theorem b{i}_exec (v : Val) :
    Executes b{i} (initial b{i} [v]) v := by
  exact .ret rfl
theorem b{i}_safe {{selected : Body}} (found : Trusted.MirSemantics.getElem? program.bodies {i} = some selected) :
    BodyVerified program {i} selected (Spec.specs.safety selected.identity) := by
  have same : b{i} = selected := Option.some.inj found
  subst selected
  refine bodyVerified_of_safe found rfl (fun args h_valid _ => ?_)
  let ⟨v, h_eq, _⟩ := validArgs1 h_valid
  subst h_eq
  exact executes_safe (b{i}_exec v)"#
                );
                if f.ensures_eq_param.is_some() {
                    let _ = writeln!(
                        block,
                        r#"theorem b{i}_ens : ∀ selected, Trusted.MirSemantics.getElem? program.bodies {i} = some selected →
    ∀ v ret, ValidEntryArgs selected [v] → Behavior (entryProgForBody program {i}) {{ args := [v] }} (.returned ⟨ret, ⟨[]⟩⟩) → ret = v := by
  intro selected found v ret _ h_beh
  have h_ret : Returns selected [v] ret := (returns_of_behavior found h_beh).2
  have same : b{i} = selected := Option.some.inj found
  subst selected
  exact (executes_unique (b{i}_exec v) h_ret).symm"#
                    );
                }
            }
            BodyPattern::MoveId => {
                let _ = writeln!(
                    block,
                    r#"theorem b{i}_exec (v : Val) (hv : checkVal v (.int .isize false) = true) :
    Executes b{i} (initial b{i} [v]) v := by
  have s0 : step b{i} (initial b{i} [v]) = .step ⟨[⟨0, 0, 1, [.live none, .live (some v), .live none]⟩], ⟨[]⟩⟩ := rfl
  have s1 : step b{i} ⟨[⟨0, 0, 1, [.live none, .live (some v), .live none]⟩], ⟨[]⟩⟩ = .step ⟨[⟨0, 0, 2, [.live none, .live (some v), .live (some v)]⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live none, .live (some v), .live none] 2 (.int .isize false) v with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 2, l'⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv]; rfl
  have s2 : step b{i} ⟨[⟨0, 0, 2, [.live none, .live (some v), .live (some v)]⟩], ⟨[]⟩⟩ = .step ⟨[⟨0, 0, 3, [.live (some v), .live (some v), .live (some v)]⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live none, .live (some v), .live (some v)] 0 (.int .isize false) v with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 3, l'⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv]; rfl
  have s3 : step b{i} ⟨[⟨0, 0, 3, [.live (some v), .live (some v), .live (some v)]⟩], ⟨[]⟩⟩ = .step ⟨[⟨0, 0, 4, [.live (some v), .live (some v), .dead]⟩], ⟨[]⟩⟩ := rfl
  have s4 : step b{i} ⟨[⟨0, 0, 4, [.live (some v), .live (some v), .dead]⟩], ⟨[]⟩⟩ = .done (.returned ⟨v, ⟨[]⟩⟩) := rfl
  exact .next s0 (.next s1 (.next s2 (.next s3 (.ret s4))))
theorem b{i}_safe {{selected : Body}} (found : Trusted.MirSemantics.getElem? program.bodies {i} = some selected) :
    BodyVerified program {i} selected (Spec.specs.safety selected.identity) := by
  have same : b{i} = selected := Option.some.inj found
  subst selected
  refine bodyVerified_of_safe found rfl (fun args h_valid _ => ?_)
  let ⟨v, h_eq, hv⟩ := validArgs1 h_valid
  subst h_eq
  exact executes_safe (b{i}_exec v hv)"#
                );
                if f.ensures_eq_param.is_some() {
                    let _ = writeln!(
                        block,
                        r#"theorem b{i}_ens : ∀ selected, Trusted.MirSemantics.getElem? program.bodies {i} = some selected →
    ∀ v ret, ValidEntryArgs selected [v] → Behavior (entryProgForBody program {i}) {{ args := [v] }} (.returned ⟨ret, ⟨[]⟩⟩) → ret = v := by
  intro selected found v ret h_valid h_beh
  have h_ret : Returns selected [v] ret := (returns_of_behavior found h_beh).2
  have same : b{i} = selected := Option.some.inj found
  subst selected
  let ⟨v', h_eq, hv⟩ := validArgs1 h_valid
  injection h_eq with h_v
  subst h_v
  exact (executes_unique (b{i}_exec v hv) h_ret).symm"#
                    );
                }
            }
            BodyPattern::U32Add => {
                let _ = writeln!(
                    block,
                    r#"theorem b{i}_exec (b1 b2 : BitVec 128)
    (hv1 : checkVal (.scalar ⟨.i32, false, b1⟩) (.int .i32 false) = true)
    (hv2 : checkVal (.scalar ⟨.i32, false, b2⟩) (.int .i32 false) = true) :
    ∃ outVal, Executes b{i} (initial b{i} [.scalar ⟨.i32, false, b1⟩, .scalar ⟨.i32, false, b2⟩]) outVal := by
  let v1 : Val := .scalar ⟨.i32, false, b1⟩
  let v2 : Val := .scalar ⟨.i32, false, b2⟩
  let raw := bvOfInt 128 (decodeScalar ⟨.i32, false, b1⟩ + decodeScalar ⟨.i32, false, b2⟩)
  let outVal : Val := .scalar ⟨.i32, false, truncateBits .i32 raw⟩
  have hout : checkVal outVal (.int .i32 false) = true := checkVal_u32_truncateBits raw
  refine ⟨outVal, ?_⟩
  have s0 : step b{i} (initial b{i} [v1, v2]) = .step ⟨[⟨0, 0, 1, [.live none, .live (some v1), .live (some v2), .live none, .dead]⟩], ⟨[]⟩⟩ := rfl
  have s1 : step b{i} ⟨[⟨0, 0, 1, [.live none, .live (some v1), .live (some v2), .live none, .dead]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 2, [.live none, .live (some v1), .live (some v2), .live (some v1), .dead]⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live none, .live (some v1), .live (some v2), .live none, .dead] 3 (.int .i32 false) v1 with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 2, l'⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv1]; rfl
  have s2 : step b{i} ⟨[⟨0, 0, 2, [.live none, .live (some v1), .live (some v2), .live (some v1), .dead]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 3, [.live none, .live (some v1), .live (some v2), .live (some v1), .live none]⟩], ⟨[]⟩⟩ := rfl
  have s3 : step b{i} ⟨[⟨0, 0, 3, [.live none, .live (some v1), .live (some v2), .live (some v1), .live none]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 4, [.live none, .live (some v1), .live (some v2), .live (some v1), .live (some v2)]⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live none, .live (some v1), .live (some v2), .live (some v1), .live none] 4 (.int .i32 false) v2 with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 4, l'⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv2]; rfl
  have s4 : step b{i} ⟨[⟨0, 0, 4, [.live none, .live (some v1), .live (some v2), .live (some v1), .live (some v2)]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 5, [.live (some outVal), .live (some v1), .live (some v2), .live none, .live none]⟩], ⟨[]⟩⟩ := by
    change (match (match evalBinOp .add v1 v2 with | .error k => Except.error k | .ok out => (Except.ok (out, [LocalSlot.live none, LocalSlot.live (some v1), LocalSlot.live (some v2), LocalSlot.live none, LocalSlot.live none]) : Except FaultKind (Val × List LocalSlot))) with | .error k => @StepResult.fault State TerminalOut k | .ok (val, l1) => match writePlace l1 0 (.int .i32 false) val with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 5, l'⟩], ⟨[]⟩⟩) = _
    rw [evalBinOp_u32_add b1 b2]
    change (match writePlace [.live none, .live (some v1), .live (some v2), .live none, .live none] 0 (.int .i32 false) outVal with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 5, l'⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hout]; rfl
  have s5 : step b{i} ⟨[⟨0, 0, 5, [.live (some outVal), .live (some v1), .live (some v2), .live none, .live none]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 6, [.live (some outVal), .live (some v1), .live (some v2), .live none, .dead]⟩], ⟨[]⟩⟩ := rfl
  have s6 : step b{i} ⟨[⟨0, 0, 6, [.live (some outVal), .live (some v1), .live (some v2), .live none, .dead]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 7, [.live (some outVal), .live (some v1), .live (some v2), .dead, .dead]⟩], ⟨[]⟩⟩ := rfl
  have s7 : step b{i} ⟨[⟨0, 0, 7, [.live (some outVal), .live (some v1), .live (some v2), .dead, .dead]⟩], ⟨[]⟩⟩ =
      .done (.returned ⟨outVal, ⟨[]⟩⟩) := rfl
  exact .next s0 (.next s1 (.next s2 (.next s3 (.next s4 (.next s5 (.next s6 (.ret s7)))))))
theorem b{i}_safe {{selected : Body}} (found : Trusted.MirSemantics.getElem? program.bodies {i} = some selected) :
    BodyVerified program {i} selected (Spec.specs.safety selected.identity) := by
  have same : b{i} = selected := Option.some.inj found
  subst selected
  refine bodyVerified_of_safe found rfl (fun args h_valid _ => ?_)
  let ⟨v1, v2, h_eq, hv1, hv2⟩ := validArgs2 h_valid
  subst h_eq
  let ⟨b1, hb1, _⟩ := checkVal_scalar_inv hv1
  let ⟨b2, hb2, _⟩ := checkVal_scalar_inv hv2
  subst hb1; subst hb2
  let ⟨_, hexec⟩ := b{i}_exec b1 b2 hv1 hv2
  exact executes_safe hexec"#
                );
            }
            BodyPattern::ClampNonzero => {
                let _ = writeln!(
                    block,
                    r#"theorem b{i}_runs_zero :
    run b{i} 12 (initial b{i} [.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩]) =
      some (.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩) := rfl
theorem b{i}_exec_nonzero (bits : BitVec 128)
    (hv : checkVal (.scalar ⟨.isize, false, bits⟩) (.int .isize false) = true)
    (hwf : (truncateBits .isize bits == bits) = true)
    (hne : (bits == BitVec.ofNat 128 0) = false) :
    Executes b{i} (initial b{i} [.scalar ⟨.isize, false, bits⟩]) (.scalar ⟨.isize, false, bits⟩) := by
  let v : Val := .scalar ⟨.isize, false, bits⟩
  have heq_int : (decodeScalar ⟨.isize, false, bits⟩ == decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩) = false := by
    unfold decodeScalar
    change (Int.ofNat (truncateBits .isize bits).toNat == Int.ofNat 0) = false
    rw [eq_of_beq hwf]
    cases h0 : (Int.ofNat bits.toNat == Int.ofNat 0) with
    | false => rfl
    | true =>
      have hi : Int.ofNat bits.toNat = Int.ofNat 0 := eq_of_beq h0
      injection hi with hn
      have hb : bits = BitVec.ofNat 128 0 := bitVec_eq_of_toNat_eq hn
      rw [hb] at hne
      cases hne
  have s0 : step b{i} (initial b{i} [v]) = .step ⟨[⟨0, 0, 1, [.live none, .live (some v), .live none, .dead]⟩], ⟨[]⟩⟩ := rfl
  have s1 : step b{i} ⟨[⟨0, 0, 1, [.live none, .live (some v), .live none, .dead]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 2, [.live none, .live (some v), .live none, .live none]⟩], ⟨[]⟩⟩ := rfl
  have s2 : step b{i} ⟨[⟨0, 0, 2, [.live none, .live (some v), .live none, .live none]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 3, [.live none, .live (some v), .live none, .live (some v)]⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live none, .live (some v), .live none, .live none] 3 (.int .isize false) v with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 3, l'⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv]; rfl
  have s3 : step b{i} ⟨[⟨0, 0, 3, [.live none, .live (some v), .live none, .live (some v)]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 4, [.live none, .live (some v), .live (some (.bool false)), .live none]⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live none, .live (some v), .live none, .live none] 2 .bool (.bool (decodeScalar ⟨.isize, false, bits⟩ == decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩)) with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 4, l'⟩], ⟨[]⟩⟩) = _
    rw [heq_int]; rfl
  have s4 : step b{i} ⟨[⟨0, 0, 4, [.live none, .live (some v), .live (some (.bool false)), .live none]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 2, 0, [.live none, .live (some v), .live none, .live none]⟩], ⟨[]⟩⟩ := rfl
  have s5 : step b{i} ⟨[⟨0, 2, 0, [.live none, .live (some v), .live none, .live none]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 2, 1, [.live none, .live (some v), .live none, .dead]⟩], ⟨[]⟩⟩ := rfl
  have s6 : step b{i} ⟨[⟨0, 2, 1, [.live none, .live (some v), .live none, .dead]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 2, 2, [.live (some v), .live (some v), .live none, .dead]⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live none, .live (some v), .live none, .dead] 0 (.int .isize false) v with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 2, 2, l'⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv]; rfl
  have s7 : step b{i} ⟨[⟨0, 2, 2, [.live (some v), .live (some v), .live none, .dead]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 3, 0, [.live (some v), .live (some v), .live none, .dead]⟩], ⟨[]⟩⟩ := rfl
  have s8 : step b{i} ⟨[⟨0, 3, 0, [.live (some v), .live (some v), .live none, .dead]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 3, 1, [.live (some v), .live (some v), .dead, .dead]⟩], ⟨[]⟩⟩ := rfl
  have s9 : step b{i} ⟨[⟨0, 3, 1, [.live (some v), .live (some v), .dead, .dead]⟩], ⟨[]⟩⟩ =
      .done (.returned ⟨v, ⟨[]⟩⟩) := rfl
  exact .next s0 (.next s1 (.next s2 (.next s3 (.next s4 (.next s5 (.next s6 (.next s7 (.next s8 (.ret s9)))))))))
theorem b{i}_safe {{selected : Body}} (found : Trusted.MirSemantics.getElem? program.bodies {i} = some selected) :
    BodyVerified program {i} selected (Spec.specs.safety selected.identity) := by
  have same : b{i} = selected := Option.some.inj found
  subst selected
  refine bodyVerified_of_safe found rfl (fun args h_valid _ => ?_)
  let ⟨v, h_eq, hv⟩ := validArgs1 h_valid
  subst h_eq
  let ⟨bits, hb, hwf⟩ := checkVal_scalar_inv hv
  subst hb
  cases hz : (bits == BitVec.ofNat 128 0) with
  | true =>
    have h0 : bits = BitVec.ofNat 128 0 := eq_of_beq hz
    subst h0
    exact (run_initial_success b{i}_runs_zero).1
  | false =>
    exact executes_safe (b{i}_exec_nonzero bits hv hwf hz)"#
                );
                if f.ensures_eq_param.is_some() {
                    let _ = writeln!(
                        block,
                        r#"theorem b{i}_ens : ∀ selected, Trusted.MirSemantics.getElem? program.bodies {i} = some selected →
    ∀ v ret, ValidEntryArgs selected [v] → v ≠ .scalar ⟨.isize, false, BitVec.ofNat 128 0⟩ → Behavior (entryProgForBody program {i}) {{ args := [v] }} (.returned ⟨ret, ⟨[]⟩⟩) → ret = v := by
  intro selected found v ret h_valid h_ne h_beh
  have h_ret : Returns selected [v] ret := (returns_of_behavior found h_beh).2
  have same : b{i} = selected := Option.some.inj found
  subst selected
  let ⟨v', h_eq, hv⟩ := validArgs1 h_valid
  injection h_eq with h_v
  subst h_v
  let ⟨bits, hb, hwf⟩ := checkVal_scalar_inv hv
  subst hb
  cases hz : (bits == BitVec.ofNat 128 0) with
  | true =>
    have h0 : bits = BitVec.ofNat 128 0 := eq_of_beq hz
    subst h0
    exact False.elim (h_ne rfl)
  | false =>
    exact (executes_unique (b{i}_exec_nonzero bits hv hwf hz) h_ret).symm"#
                    );
                }
            }
            BodyPattern::CustomMirNonzero => {
                let fn_name = &f.name;
                let _ = writeln!(
                    block,
                    r#"theorem b{i}_exec_nonzero (bits : BitVec 128)
    (hv : checkVal (.scalar ⟨.isize, false, bits⟩) (.int .isize false) = true)
    (hwf : (truncateBits .isize bits == bits) = true)
    (hne : (bits == BitVec.ofNat 128 0) = false) :
    Executes b{i} (initial b{i} [.scalar ⟨.isize, false, bits⟩]) (.scalar ⟨.isize, false, bits⟩) := by
  let v : Val := .scalar ⟨.isize, false, bits⟩
  have htr : (truncateBits .isize bits == truncateBits .isize (BitVec.ofNat 128 0)) = false := by
    rw [eq_of_beq hwf]
    exact hne
  have s0 : step b{i} (initial b{i} [v]) = .step ⟨[⟨0, 2, 0, [.live none, .live (some v)]⟩], ⟨[]⟩⟩ := by
    change (match (if (truncateBits .isize bits == truncateBits .isize (BitVec.ofNat 128 0)) then Except.ok 1 else Except.ok 2) with | .error k => @StepResult.fault State TerminalOut k | .ok tgt => jumpToBlock ⟨0, 0, 0, [.live none, .live (some v)]⟩ ⟨[]⟩ tgt) = _
    rw [htr]; rfl
  have s1 : step b{i} ⟨[⟨0, 2, 0, [.live none, .live (some v)]⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 2, 1, [.live (some v), .live (some v)]⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live none, .live (some v)] 0 (.int .isize false) v with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 2, 1, l'⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv]; rfl
  have s2 : step b{i} ⟨[⟨0, 2, 1, [.live (some v), .live (some v)]⟩], ⟨[]⟩⟩ =
      .done (.returned ⟨v, ⟨[]⟩⟩) := rfl
  exact .next s0 (.next s1 (.ret s2))
theorem b{i}_safe {{selected : Body}} (found : Trusted.MirSemantics.getElem? program.bodies {i} = some selected) :
    BodyVerified program {i} selected (Spec.specs.safety selected.identity) := by
  have same : b{i} = selected := Option.some.inj found
  subst selected
  refine bodyVerified_of_safe found rfl (fun args h_valid required => ?_)
  let ⟨v, h_eq, hv⟩ := validArgs1 h_valid
  subst h_eq
  let ⟨bits, hb, hwf⟩ := checkVal_scalar_inv hv
  subst hb
  cases hz : (bits == BitVec.ofNat 128 0) with
  | true =>
    have h0 : bits = BitVec.ofNat 128 0 := eq_of_beq hz
    subst h0
    have h_req := required rfl
    have h_id : (b{i}.identity == "rust-path-v1::{fn_name}") = true := rfl
    change (if (b{i}.identity == "rust-path-v1::{fn_name}") = true then [Val.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩] ≠ [Val.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩] else False) at h_req
    rw [h_id] at h_req
    exact False.elim (h_req rfl)
  | false =>
    exact executes_safe (b{i}_exec_nonzero bits hv hwf hz)"#
                );
            }
            BodyPattern::EnumTag => {
                let _ = writeln!(
                    block,
                    r#"noncomputable def b{i}_ety : EnumTy := match b{i}.locals with | _ :: .enum ety :: _ => ety | _ => {{ id := 0, discrWidth := .isize, discrSigned := true, tagRepr := .zeroSized, discriminants := [] }}
theorem b{i}_runs_0 :
    run b{i} 10 (initial b{i} [.enumVal b{i}_ety 0]) =
      some (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) := rfl
theorem b{i}_runs_1 :
    run b{i} 10 (initial b{i} [.enumVal b{i}_ety 1]) =
      some (.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩) := rfl
theorem b{i}_safe {{selected : Body}} (found : Trusted.MirSemantics.getElem? program.bodies {i} = some selected) :
    BodyVerified program {i} selected (Spec.specs.safety selected.identity) := by
  have same : b{i} = selected := Option.some.inj found
  subst selected
  refine bodyVerified_of_safe found rfl (fun args h_valid _ => ?_)
  let ⟨v, h_eq, hv⟩ := validArgs1 h_valid
  subst h_eq
  cases checkVal_enum2_inv (ety := b{i}_ety) rfl hv with
  | inl h0 => subst h0; exact (run_initial_success b{i}_runs_0).1
  | inr h1 => subst h1; exact (run_initial_success b{i}_runs_1).1"#
                );
            }
        }

        push_block(&mut proof_lines, &block);
        let end_line = proof_lines.len();
        fn_line_ranges.push((start_line, end_line, f.name.clone()));
    }

    // Dispatch all body indices `0..fns.len()`.
    let mut dispatch = String::from(
        "theorem all_bodies_safe : ∀ id selected, Trusted.MirSemantics.getElem? program.bodies id = some selected → BodyVerified program id selected (Spec.specs.safety selected.identity) := by\n  intro id selected found\n",
    );
    for i in 0..fns.len() {
        let indent = "  ".repeat(i + 1);
        let _ = writeln!(dispatch, "{indent}cases id with");
        let _ = writeln!(dispatch, "{indent}| zero => exact b{i}_safe found");
        let _ = writeln!(dispatch, "{indent}| succ id =>");
    }
    let _ = writeln!(dispatch, "{}cases found", "  ".repeat(fns.len() + 1));
    push_block(&mut proof_lines, &dispatch);

    let prop_term = match prop_clauses.len() {
        0 => "True.intro".to_owned(),
        1 => format!("b{}_ens", prop_clauses[0].0),
        _ => {
            let inner = prop_clauses
                .iter()
                .map(|(idx, _)| format!("b{idx}_ens"))
                .collect::<Vec<_>>()
                .join(", ");
            format!("⟨{inner}⟩")
        }
    };
    push_block(
        &mut proof_lines,
        &format!("theorem verify : Expected.claim :=\n  ⟨rfl, rfl, rfl, rfl, rfl, rfl, all_bodies_safe, {prop_term}⟩\nend Proof"),
    );

    let mut proof_lean = proof_lines.join("\n");
    proof_lean.push('\n');
    Ok(SynthesizedPackage {
        spec_lean,
        proof_lean,
        fn_line_ranges,
    })
}

// ---------------------------------------------------------------------------
// End-to-end `cargo-anneal verify --manifest-path` execution & error mapping
// ---------------------------------------------------------------------------

struct SandboxCrate {
    _root: Option<TempDir>,
    root_path: PathBuf,
    crate_dir: PathBuf,
    proof_dir: PathBuf,
    artifacts_dir: PathBuf,
}

impl SandboxCrate {
    fn new(prefix: &str, rust_source: &str) -> Self {
        let temp = tempfile::Builder::new()
            .prefix(&format!("anneal-integ-{prefix}-"))
            .tempdir()
            .expect("create integration test sandbox");
        let keep = env::var_os("ANNEAL_KEEP_SANDBOX").is_some_and(|v| !v.is_empty());
        let root_path = temp.path().to_path_buf();
        let root = if keep {
            let _ = temp.keep();
            None
        } else {
            Some(temp)
        };
        let crate_dir = root_path.join("subject");
        let proof_dir = root_path.join("proof");
        let artifacts_dir = root_path.join("artifacts");
        fs::create_dir_all(crate_dir.join("src")).unwrap();
        fs::create_dir_all(&proof_dir).unwrap();
        fs::write(
            crate_dir.join("Cargo.toml"),
            "[package]\nname = \"sample\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        fs::write(crate_dir.join("src/lib.rs"), rust_source).unwrap();
        Self {
            _root: root,
            root_path,
            crate_dir,
            proof_dir,
            artifacts_dir,
        }
    }
}

fn parse_capture_detail(detail: &str) -> String {
    if let Ok(env_json) = serde_json::from_str::<Value>(detail) {
        let mut parts = Vec::new();
        if let Some(arr) = env_json["unsupported"].as_array() {
            for item in arr {
                let path = item["path"].as_str().unwrap_or("<item>");
                let reason = item["reason"].as_str().unwrap_or("unsupported");
                parts.push(format!("{path}: {reason}"));
            }
        }
        if let Some(diags) = env_json["diagnostics"].as_array() {
            for d in diags {
                if let Some(s) = d.as_str() {
                    parts.push(s.to_owned());
                }
            }
        }
        if !parts.is_empty() {
            return parts.join("; ");
        }
    }
    detail.to_owned()
}

fn parse_proof_failure(
    detail: &str,
    fn_ranges: &[(usize, usize, String)],
) -> (String, String) {
    let mut best_scope = "crate".to_owned();
    let mut messages = Vec::new();
    for line in detail.lines() {
        let trimmed = line.trim();
        if !trimmed.starts_with('{') {
            continue;
        }
        if let Ok(msg) = serde_json::from_str::<Value>(trimmed)
            && msg["severity"].as_str() == Some("error")
        {
            if let Some(pos_line) = msg["pos"]["line"].as_u64() {
                let l = pos_line as usize;
                for (start, end, fn_name) in fn_ranges {
                    if l >= *start && l <= *end && best_scope == "crate" {
                        best_scope = fn_name.clone();
                    }
                }
            }
            if let Some(data) = msg["data"].as_str() {
                messages.push(data.to_owned());
            }
        }
    }
    let diag = if messages.is_empty() {
        detail.to_owned()
    } else {
        messages.join("\n")
    };
    (best_scope, diag)
}

fn verify_sandbox(tools: &Tools, sandbox: &SandboxCrate, rust_source: &str) -> Result<VerifyReport, VerifyError> {
    let synth = match synthesize_proof_package(rust_source) {
        Ok(s) => s,
        Err(spec_err) => {
            return Err(VerifyError {
                message: format!("capture: {spec_err}"),
                failure: Some(StageFailure {
                    stage: FailureStage::Capture,
                    diagnostic: spec_err,
                }),
                mir_lean: None,
            });
        }
    };
    fs::write(sandbox.proof_dir.join("Spec.lean"), &synth.spec_lean).unwrap();
    fs::write(sandbox.proof_dir.join("Proof.lean"), &synth.proof_lean).unwrap();

    let output = tools
        .command()
        .arg("--manifest-path")
        .arg(sandbox.crate_dir.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(&sandbox.proof_dir)
        .arg("--artifacts")
        .arg(&sandbox.artifacts_dir)
        .output()
        .map_err(|e| VerifyError {
            message: format!("failed to spawn cargo-anneal: {e}"),
            failure: None,
            mir_lean: None,
        })?;

    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let mir_lean = fs::read_to_string(sandbox.artifacts_dir.join("capture/Captured.lean")).ok();

    let receipt: Value = serde_json::from_str(&stdout).map_err(|e| VerifyError {
        message: format!("invalid JSON receipt ({e}):\nstdout:\n{stdout}\nstderr:\n{stderr}"),
        failure: None,
        mir_lean: mir_lean.clone(),
    })?;

    if output.status.success() {
        if receipt["status"] != "crate_verified"
            || receipt["audit"]["exactType"] != true
            || receipt["audit"]["replay"] != true
        {
            return Err(VerifyError {
                message: format!("unexpected verification receipt:\n{stdout}"),
                failure: None,
                mir_lean,
            });
        }
        return Ok(VerifyReport {
            mir_lean: mir_lean.unwrap_or_default(),
            output_text: stdout,
        });
    }

    let status = receipt["status"].as_str().unwrap_or("");
    let phase = receipt["phase"].as_str().unwrap_or("");
    let detail = receipt["detail"].as_str().unwrap_or(&stdout);

    let failure = match (status, phase) {
        ("proof_failed", "audit") => {
            let (scope, diagnostic) = parse_proof_failure(detail, &synth.fn_line_ranges);
            Some(StageFailure {
                stage: FailureStage::Proof { scope },
                diagnostic,
            })
        }
        ("unsupported" | "compiler_failed", "capture" | "cargo" | "inputs" | "request" | "proof") => {
            let diagnostic = parse_capture_detail(detail);
            Some(StageFailure {
                stage: FailureStage::Capture,
                diagnostic,
            })
        }
        _ => None,
    };

    Err(VerifyError {
        message: format!("status={status} phase={phase}: {detail}"),
        failure,
        mir_lean,
    })
}

fn dump_failure_bundle(case: &FixtureCase, detail: &str, mir_lean: Option<&str>) -> PathBuf {
    static FAILURE_DIR: OnceLock<PathBuf> = OnceLock::new();
    let root = FAILURE_DIR.get_or_init(|| {
        tempfile::Builder::new()
            .prefix("anneal-test-failures-")
            .tempdir()
            .expect("create process-unique failure bundle directory")
            .keep()
    });
    let dir = root.join(&case.suite).join(&case.name);
    let _ = fs::create_dir_all(&dir);
    let _ = fs::write(dir.join("lib.rs"), &case.source);
    let _ = fs::write(dir.join("failure.txt"), detail);
    if let Some(mir) = mir_lean {
        let _ = fs::write(dir.join("Captured.lean"), mir);
    }
    dir
}

// ---------------------------------------------------------------------------
// Declarative fixture corpus runner
// ---------------------------------------------------------------------------

#[test]
fn verifies_fixture_corpus() {
    let tools = Arc::new(Tools::discover());
    let fixtures_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let mut fixture_files = Vec::new();
    for entry in fs::read_dir(&fixtures_dir).expect("read tests/fixtures") {
        let entry = entry.unwrap();
        let path = entry.path();
        // Subdirectories (`scalar`, `spin`, `starnix`, `unsafe_identity`) belong
        // to `mvp_e2e.rs` and `ci/verify_starnix_e2e.py`.
        if path.is_file() && path.extension().is_some_and(|e| e == "rs") {
            fixture_files.push(path);
        }
    }
    fixture_files.sort();
    assert!(
        !fixture_files.is_empty(),
        "no declarative `.rs` fixtures found in {}",
        fixtures_dir.display()
    );

    let filter = env::var("ANNEAL_TEST_FILTER").ok().filter(|s| !s.is_empty());
    let bless = env::var("ANNEAL_BLESS").ok().as_deref() == Some("1");

    let mut all_cases = Vec::new();
    for path in &fixture_files {
        let suite = path.file_stem().unwrap().to_string_lossy().into_owned();
        let content = fs::read_to_string(path).unwrap();
        let mut parsed = parse_fixture_file(&suite, path, &content)
            .unwrap_or_else(|e| panic!("fixture parse error: {e}"));
        if let Some(f) = &filter {
            parsed.retain(|c| c.full_name().contains(f));
        }
        all_cases.extend(parsed);
    }
    assert!(
        !all_cases.is_empty(),
        "no fixture cases matched filter {filter:?}"
    );

    let concurrency = thread::available_parallelism()
        .map(|n| n.get().min(3))
        .unwrap_or(2)
        .max(1);
    let queue = Arc::new(Mutex::new(all_cases.into_iter()));
    let patches = Arc::new(Mutex::new(Vec::new()));
    let failures = Arc::new(Mutex::new(Vec::new()));

    let mut handles = Vec::with_capacity(concurrency);
    for _ in 0..concurrency {
        let tools = Arc::clone(&tools);
        let queue = Arc::clone(&queue);
        let patches = Arc::clone(&patches);
        let failures = Arc::clone(&failures);
        handles.push(thread::spawn(move || {
            while let Some(case) = {
                let mut q = queue.lock().unwrap();
                q.next()
            } {
                let sandbox = SandboxCrate::new(&case.name, &case.source);
                let res = verify_sandbox(&tools, &sandbox, &case.source);
                let mir_ref = match &res {
                    Ok(r) => Some(r.mir_lean.as_str()),
                    Err(e) => e.mir_lean.as_deref(),
                };
                match evaluate_case(&case, &res, bless) {
                    CaseOutcome::Passed => {}
                    CaseOutcome::Blessed(patch) => {
                        patches.lock().unwrap().push(patch);
                    }
                    CaseOutcome::Failed(reason) => {
                        let dump = dump_failure_bundle(&case, &reason, mir_ref);
                        failures.lock().unwrap().push(format!(
                            "=== FAIL {} ({}:{}) ===\n{reason}\n(bundle saved at {})\n",
                            case.full_name(),
                            case.file_path.display(),
                            case.primary_line_idx + 1,
                            dump.display()
                        ));
                    }
                }
            }
        }));
    }
    for h in handles {
        h.join().expect("fixture worker thread panicked");
    }

    let patches = Arc::try_unwrap(patches).unwrap().into_inner().unwrap();
    if !patches.is_empty() {
        apply_bless_patches(&patches).expect("apply ANNEAL_BLESS patches");
    }

    let failures = Arc::try_unwrap(failures).unwrap().into_inner().unwrap();
    assert!(
        failures.is_empty(),
        "{} declarative fixture case(s) failed:\n\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Parser fail-closed & polarity-safe bless unit tests
// ---------------------------------------------------------------------------

#[test]
fn rejects_malformed_fixture_directives() {
    let dummy = Path::new("dummy.rs");
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
            "//@ known_bug(87, proof, id): \"unproved\"\npub fn id(x: usize) -> usize { x }\n",
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
fn bless_updates_expectation_and_promotes_resolved_known_bug_without_flipping_polarity() {
    let tmp = tempfile::Builder::new()
        .prefix("anneal-bless-test-")
        .tempdir()
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
//@ known_bug(#87, proof, id): \"unproved function body\"
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
    let cases = parse_fixture_file("sample_bless", &fixture_path, initial).unwrap();
    assert_eq!(cases.len(), 3);

    let mut patches = Vec::new();
    let proof_err: Result<VerifyReport, VerifyError> = Err(VerifyError {
        message: "status=proof_failed phase=audit: mismatch".to_owned(),
        failure: Some(StageFailure {
            stage: FailureStage::Proof {
                scope: "id".to_owned(),
            },
            diagnostic: "Type mismatch".to_owned(),
        }),
        mir_lean: Some("-- captured Captured.lean".to_owned()),
    });
    let pass_ok: Result<VerifyReport, VerifyError> = Ok(VerifyReport {
        mir_lean: String::new(),
        output_text: String::new(),
    });

    match evaluate_case(&cases[0], &proof_err, true) {
        CaseOutcome::Blessed(p) => patches.push(p),
        other => panic!("expected Blessed for stale_proof_msg, got {other:?}"),
    }
    match evaluate_case(&cases[1], &pass_ok, true) {
        CaseOutcome::Blessed(p) => patches.push(p),
        other => panic!("expected Blessed for resolved_known_bug, got {other:?}"),
    }
    assert!(
        matches!(evaluate_case(&cases[2], &proof_err, true), CaseOutcome::Failed(_)),
        "expected broken `//@ pass` case to fail even when bless=true"
    );

    apply_bless_patches(&patches).unwrap();
    let updated = fs::read_to_string(&fixture_path).unwrap();
    assert!(
        updated.contains("//@ fail(proof, id): \"Type mismatch\""),
        "expected updated proof scope and message, got:\n{updated}"
    );
    assert!(
        updated.contains("// === case: resolved_known_bug ===\n//@ pass\n"),
        "expected resolved known_bug to promote to `//@ pass`, got:\n{updated}"
    );
}

// ---------------------------------------------------------------------------
// Host-boundary, staging, and environment-scrubbing tests
// ---------------------------------------------------------------------------

#[test]
fn ignores_tampered_or_spoofed_files_in_dot_anneal_and_proof_olean() {
    let tools = Tools::discover();
    let bad_src = "/// anneal:spec ensures(ret == x)\n\
                   pub fn id(x: usize) -> usize {\n    let _ = x;\n    0\n}\n";
    let sandbox = SandboxCrate::new("spoofed-artifacts", bad_src);
    fs::create_dir_all(sandbox.crate_dir.join(".anneal")).unwrap();
    fs::write(
        sandbox.crate_dir.join(".anneal/Captured.lean"),
        b"prelude\nimport Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst\nnamespace Captured\ndef program : Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Program := { bodies := [] }\nend Captured\n",
    )
    .unwrap();
    fs::write(
        sandbox.crate_dir.join(".anneal/Proof.lean"),
        b"prelude\ntheorem verify : True := trivial\n",
    )
    .unwrap();
    fs::write(sandbox.proof_dir.join("Proof.olean"), b"spoofed precompiled olean").unwrap();

    let err = verify_sandbox(&tools, &sandbox, bad_src).unwrap_err();
    assert_eq!(
        err.failure.as_ref().map(|f| &f.stage),
        Some(&FailureStage::Proof {
            scope: "id".to_owned()
        }),
        "expected Lean proof rejection despite spoofed .anneal/ and Proof.olean, got: {err}"
    );
}

#[test]
fn rejects_symlinked_sources_and_disallowed_manifest_targets() {
    let tools = Tools::discover();
    let ok_src = "pub fn id(x: usize) -> usize { x }\n";

    // 1. Symlinked `src/lib.rs` must not be staged via `--manifest-path`, and
    // must be rejected as `not a declared regular file` via `--request`.
    {
        let sandbox = SandboxCrate::new("symlink-lib", ok_src);
        let real_lib = sandbox.root_path.join("real_lib.rs");
        fs::rename(sandbox.crate_dir.join("src/lib.rs"), &real_lib).unwrap();
        symlink(&real_lib, sandbox.crate_dir.join("src/lib.rs")).unwrap();
        let err = verify_sandbox(&tools, &sandbox, ok_src).unwrap_err();
        assert!(
            err.message.contains("unsupported or empty compilation request"),
            "expected symlinked src/lib.rs manifest rejection, got: {err}"
        );

        let req_path = sandbox.root_path.join("request.json");
        let req = serde_json::json!({
            "schema_version": 1,
            "compilation": {
                "source_root": sandbox.crate_dir,
                "crate_root": "src/lib.rs",
                "crate_name": "sample",
                "edition": "2024",
                "target": "x86_64-unknown-linux-gnu",
                "cfg": [],
                "source_files": ["src/lib.rs"],
            },
            "scope": { "kind": "crate" },
            "proof": {
                "source_root": sandbox.proof_dir,
                "specification": "Spec.specs",
                "theorem": "Proof.verify",
                "sources": [
                    { "module": "Spec", "path": "Spec.lean", "role": "specification" },
                    { "module": "Proof", "path": "Proof.lean", "role": "proof" }
                ]
            }
        });
        fs::write(&req_path, serde_json::to_vec_pretty(&req).unwrap()).unwrap();
        let out = tools.command().arg("--request").arg(&req_path).output().unwrap();
        assert!(!out.status.success());
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains("not a declared regular file"),
            "expected symlinked src/lib.rs request rejection, got:\n{stdout}"
        );
    }

    // 2. Symlinked `proof/Proof.lean` must not be staged (`WalkDir` does not
    // follow links, so `Proof` module is missing or rejected).
    {
        let sandbox = SandboxCrate::new("symlink-proof", ok_src);
        let synth = synthesize_proof_package(ok_src).unwrap();
        fs::write(sandbox.proof_dir.join("Spec.lean"), &synth.spec_lean).unwrap();
        let real_proof = sandbox.root_path.join("RealProof.lean");
        fs::write(&real_proof, &synth.proof_lean).unwrap();
        symlink(&real_proof, sandbox.proof_dir.join("Proof.lean")).unwrap();
        let output = tools
            .command()
            .arg("--manifest-path")
            .arg(sandbox.crate_dir.join("Cargo.toml"))
            .arg("--proof-dir")
            .arg(&sandbox.proof_dir)
            .output()
            .unwrap();
        assert!(
            !output.status.success(),
            "expected symlinked Proof.lean to fail verification:\n{}",
            String::from_utf8_lossy(&output.stdout)
        );
    }

    // 3. `build.rs` custom-build target must be rejected.
    {
        let sandbox = SandboxCrate::new("build-rs", ok_src);
        fs::write(sandbox.crate_dir.join("build.rs"), "fn main() {}\n").unwrap();
        let err = verify_sandbox(&tools, &sandbox, ok_src).unwrap_err();
        assert!(
            err.message
                .contains("build scripts and procedural macros need an explicit configured compilation"),
            "expected build.rs rejection, got: {err}"
        );
    }

    // 4. Binary-only crate (no library target) must be rejected.
    {
        let sandbox = SandboxCrate::new("bin-only", ok_src);
        fs::remove_file(sandbox.crate_dir.join("src/lib.rs")).unwrap();
        fs::write(sandbox.crate_dir.join("src/main.rs"), "fn main() {}\n").unwrap();
        let err = verify_sandbox(&tools, &sandbox, ok_src).unwrap_err();
        assert!(
            err.message.contains("Cargo shortcut requires a library target"),
            "expected binary-only rejection, got: {err}"
        );
    }

    // 5. Cargo `[features]` must be rejected.
    {
        let sandbox = SandboxCrate::new("cargo-features", ok_src);
        fs::write(
            sandbox.crate_dir.join("Cargo.toml"),
            "[package]\nname = \"sample\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[features]\nfoo = []\n",
        )
        .unwrap();
        let err = verify_sandbox(&tools, &sandbox, ok_src).unwrap_err();
        assert!(
            err.message
                .contains("Cargo features require an explicit configured compilation request"),
            "expected Cargo features rejection, got: {err}"
        );
    }

    // 6. Cargo `[dependencies]` must be rejected.
    {
        let sandbox = SandboxCrate::new("cargo-deps", ok_src);
        let dep_dir = sandbox.root_path.join("dep");
        fs::create_dir_all(dep_dir.join("src")).unwrap();
        fs::write(
            dep_dir.join("Cargo.toml"),
            "[package]\nname = \"dep\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        fs::write(dep_dir.join("src/lib.rs"), "").unwrap();
        fs::write(
            sandbox.crate_dir.join("Cargo.toml"),
            format!(
                "[package]\nname = \"sample\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[dependencies]\ndep = {{ path = {:?} }}\n",
                dep_dir.display().to_string()
            ),
        )
        .unwrap();
        let err = verify_sandbox(&tools, &sandbox, ok_src).unwrap_err();
        assert!(
            err.message.contains("Cargo shortcut requires a dependency-free library"),
            "expected Cargo dependencies rejection, got: {err}"
        );
    }

    // 7. Virtual workspace `Cargo.toml` must be rejected.
    {
        let sandbox = SandboxCrate::new("virtual-ws", ok_src);
        let ws_manifest = sandbox.root_path.join("Cargo.toml");
        fs::write(
            &ws_manifest,
            "[workspace]\nmembers = [\"subject\"]\nresolver = \"2\"\n",
        )
        .unwrap();
        let synth = synthesize_proof_package(ok_src).unwrap();
        fs::write(sandbox.proof_dir.join("Spec.lean"), &synth.spec_lean).unwrap();
        fs::write(sandbox.proof_dir.join("Proof.lean"), &synth.proof_lean).unwrap();
        let output = tools
            .command()
            .arg("--manifest-path")
            .arg(&ws_manifest)
            .arg("--proof-dir")
            .arg(&sandbox.proof_dir)
            .output()
            .unwrap();
        assert!(!output.status.success());
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            stdout.contains("choose a package Cargo.toml, not a virtual workspace"),
            "expected virtual workspace rejection, got:\n{stdout}"
        );
    }
}

#[test]
fn rejects_compiler_overrides_in_source_root() {
    let tools = Tools::discover();
    let ok_src = "pub fn id(x: usize) -> usize { x }\n";
    for rel in [
        ".cargo/config",
        ".cargo/config.toml",
        "rust-toolchain",
        "rust-toolchain.toml",
    ] {
        let sandbox = SandboxCrate::new("compiler-override", ok_src);
        let override_path = sandbox.crate_dir.join(rel);
        if let Some(parent) = override_path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(&override_path, "[build]\nrustflags = [\"--cfg\", \"evil\"]\n").unwrap();
        let err = verify_sandbox(&tools, &sandbox, ok_src).unwrap_err();
        assert!(
            err.message
                .contains("compiler overrides need an explicit configured compilation"),
            "expected {rel} override rejection, got: {err}"
        );
    }
}

#[test]
fn verifies_under_hostile_environment_and_cargo_configs() {
    let tools = Tools::discover();
    let ok_src = "/// anneal:spec ensures(ret == x)\npub fn id(x: usize) -> usize { x }\n";
    let sandbox = SandboxCrate::new("hostile-env", ok_src);
    let synth = synthesize_proof_package(ok_src).unwrap();
    fs::write(sandbox.proof_dir.join("Spec.lean"), &synth.spec_lean).unwrap();
    fs::write(sandbox.proof_dir.join("Proof.lean"), &synth.proof_lean).unwrap();

    let evil = tempfile::Builder::new()
        .prefix("anneal-evil-env-")
        .tempdir()
        .unwrap();
    let e = evil.path();
    let bad_cfg = "[build]\nrustc-wrapper = \"/bin/false\"\nrustflags = [\"--cfg\", \"evil\"]\n";
    fs::create_dir_all(e.join(".cargo")).unwrap();
    fs::write(e.join(".cargo/config.toml"), bad_cfg).unwrap();
    fs::create_dir_all(e.join("work")).unwrap();
    fs::create_dir_all(e.join("lib")).unwrap();
    for lib in ["libleanshared.so", "librustc_driver.so"] {
        fs::write(e.join("lib").join(lib), b"not an ELF shared library").unwrap();
    }

    let output = tools
        .command()
        .arg("--manifest-path")
        .arg(sandbox.crate_dir.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(&sandbox.proof_dir)
        .current_dir(e.join("work"))
        .env("XDG_CACHE_HOME", e)
        .env("RUSTC", "/bin/false")
        .env("RUSTC_WRAPPER", "/bin/false")
        .env("RUSTFLAGS", "--cfg evil")
        .env("RUSTC_LOG", "debug")
        .env("LD_LIBRARY_PATH", e.join("lib"))
        .env("LEAN_PATH", e)
        .output()
        .expect("invoke cargo-anneal under hostile environment");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "expected cargo-anneal verify to succeed under hostile env:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let receipt: Value = serde_json::from_str(&stdout).unwrap();
    assert_eq!(receipt["status"], "crate_verified");
    assert_eq!(receipt["audit"]["exactType"], true);
    assert_eq!(receipt["audit"]["replay"], true);
}

#[test]
fn rejects_external_file_inclusion_via_path_attribute() {
    let tools = Tools::discover();
    let ext_dir = tempfile::Builder::new()
        .prefix("anneal-ext-src-")
        .tempdir()
        .unwrap();
    let ext_file = ext_dir.path().join("outside.rs");
    fs::write(&ext_file, "pub fn helper(x: usize) -> usize { x }\n").unwrap();

    let src = format!(
        "#[path = {:?}]\npub mod outside;\npub fn id(x: usize) -> usize {{ outside::helper(x) }}\n",
        ext_file.display().to_string()
    );
    let sandbox = SandboxCrate::new("path-attr-outside", &src);
    let err = verify_sandbox(&tools, &sandbox, &src).unwrap_err();
    assert!(
        err.message.contains("undeclared compiler read"),
        "expected undeclared compiler read rejection for #[path = ...], got: {err}"
    );
}

#[test]
fn single_case_fixture_preserves_leading_doc_comments() {
    let dummy = Path::new("single_case.rs");
    let raw = "\
// Copyright 2026 The Fuchsia Authors
//! Crate-level doc comment in header window.
/// anneal:spec ensures(ret == x)
//@ pass
pub fn id(x: usize) -> usize {
    x
}
";
    let cases = parse_fixture_file("single_case", dummy, raw).unwrap();
    assert_eq!(cases.len(), 1);
    assert!(
        cases[0].source.contains("//! Crate-level doc comment"),
        "expected `//!` doc comment to be preserved, got:\n{}",
        cases[0].source
    );
    assert!(
        cases[0].source.contains("/// anneal:spec ensures(ret == x)"),
        "expected `/// anneal:spec` doc comment to be preserved, got:\n{}",
        cases[0].source
    );
    let synth = synthesize_proof_package(&cases[0].source).unwrap();
    assert!(
        synth.spec_lean.contains("Behavior (entryProgForBody p 0)"),
        "expected Spec.lean to state Behavior contract without Returns:\n{}",
        synth.spec_lean
    );
    assert!(
        !synth.spec_lean.contains("Returns"),
        "Spec.lean must not reference proof-side `Returns`:\n{}",
        synth.spec_lean
    );
}

// ---------------------------------------------------------------------------
// Declared compiler boundaries (`--rustc` / `--rustc-version`)
// ---------------------------------------------------------------------------

/// Supported compilers as `(dialect, commit, commit-date)`, mirrored from
/// `src/compilers.rs` to choose test inputs.
const SUPPORTED_COMPILERS: &[(&str, &str, &str)] = &[
    (
        "V2026_10_22_R7189d39d9",
        "7189d39d9ce936881b8132c6addeaf3e295cd455",
        "2026-10-22",
    ),
    (
        "V2026_05_31_R14210df0e",
        "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65",
        "2026-05-31",
    ),
    (
        "V2026_05_30_Rf8a08b688",
        "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1",
        "2026-05-30",
    ),
];

const DECLARED_SRC: &str =
    "/// anneal:spec ensures(ret == x)\npub fn id(x: usize) -> usize { x }\n";

/// Return the sysroot's `bin/rustc` and its supported entry, read from the
/// compiler's own `--version --verbose` report.
fn sysroot_compiler(tools: &Tools) -> (PathBuf, (&'static str, &'static str, &'static str)) {
    let rustc = tools.sysroot.join("bin/rustc");
    let output = Command::new(&rustc)
        .args(["--version", "--verbose"])
        .output()
        .expect("run the sysroot compiler");
    assert!(output.status.success(), "{output:?}");
    let text = String::from_utf8(output.stdout).unwrap();
    let field = |name: &str| {
        text.lines()
            .find_map(|line| line.strip_prefix(name))
            .unwrap_or_else(|| panic!("missing {name} in {text}"))
            .to_owned()
    };
    let (commit, date) = (field("commit-hash: "), field("commit-date: "));
    let entry = SUPPORTED_COMPILERS
        .iter()
        .copied()
        .find(|(_, supported, supported_date)| *supported == commit && *supported_date == date)
        .unwrap_or_else(|| panic!("the test sysroot compiler is unsupported: {text}"));
    (rustc, entry)
}

fn another_compiler(dialect: &str) -> (&'static str, &'static str, &'static str) {
    SUPPORTED_COMPILERS
        .iter()
        .copied()
        .find(|(other, ..)| *other != dialect)
        .unwrap()
}

/// A crate sandbox with its synthesized proof package already written.
fn declared_sandbox(prefix: &str) -> SandboxCrate {
    let sandbox = SandboxCrate::new(prefix, DECLARED_SRC);
    let synth = synthesize_proof_package(DECLARED_SRC).unwrap();
    fs::write(sandbox.proof_dir.join("Spec.lean"), &synth.spec_lean).unwrap();
    fs::write(sandbox.proof_dir.join("Proof.lean"), &synth.proof_lean).unwrap();
    sandbox
}

/// Run `verify` for `sandbox` with `capture` and optional compiler options.
fn run_declared(
    tools: &Tools,
    sandbox: &SandboxCrate,
    capture: &Path,
    declared: Option<(&Path, &str)>,
    sysroot: bool,
) -> (Option<i32>, Value) {
    let mut command = Command::new(&tools.cli);
    command
        .arg("verify")
        .arg("--capture")
        .arg(capture)
        .arg("--lean")
        .arg(&tools.lean)
        .arg("--manifest-path")
        .arg(sandbox.crate_dir.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(&sandbox.proof_dir)
        .arg("--artifacts")
        .arg(&sandbox.artifacts_dir);
    if sysroot {
        command.arg("--sysroot").arg(&tools.sysroot);
    }
    if let Some((rustc, id)) = declared {
        command
            .arg("--rustc")
            .arg(rustc)
            .args(["--rustc-version", id]);
    }
    let output = command.output().expect("run cargo-anneal verify");
    let receipt = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "invalid receipt ({error}):\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    (output.status.code(), receipt)
}

/// Create an executable from a short-lived child process. A child that
/// another test thread forks while this process holds the file open for
/// writing keeps that descriptor until its own `exec`, and executing the file
/// meanwhile fails with ETXTBSY ("Text file busy").
fn executable_script(path: &Path, script: &str) {
    use std::io::Write as _;
    let mut child = Command::new("/bin/sh")
        .args([
            "-c",
            "cat > \"$1\" && chmod 755 \"$1\"",
            "install-executable",
        ])
        .arg(path)
        .stdin(std::process::Stdio::piped())
        .spawn()
        .expect("start executable installer");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(script.as_bytes())
        .unwrap();
    assert!(
        child.wait().unwrap().success(),
        "install {}",
        path.display()
    );
}

/// The positive end-to-end path: both `--rustc-version` spellings, with the
/// sysroot inferred from `--rustc` and given explicitly, verify the crate and
/// bind the receipt, capture, and canonical root to the declared dialect.
#[test]
fn verifies_with_declared_rustc_and_rustc_version() {
    use sha2::{Digest, Sha256};

    let tools = Tools::discover();
    let (rustc, (dialect, commit, date)) = sysroot_compiler(&tools);
    let canonical = fs::canonicalize(&rustc).unwrap();
    for (id, sysroot) in [(dialect, false), (commit, true)] {
        let sandbox = declared_sandbox("declared-rustc");
        let (code, receipt) = run_declared(
            &tools,
            &sandbox,
            &tools.capture,
            Some((&rustc, id)),
            sysroot,
        );
        assert_eq!(code, Some(0), "{receipt}");
        assert_eq!(receipt["status"], "crate_verified", "{receipt}");
        assert_eq!(receipt["audit"]["exactType"], true, "{receipt}");
        assert_eq!(receipt["audit"]["replay"], true, "{receipt}");
        let compiler = &receipt["compiler"];
        assert_eq!(compiler["mir_dialect"], dialect, "{receipt}");
        assert_eq!(compiler["commit"], commit, "{receipt}");
        assert_eq!(compiler["commit_date"], date, "{receipt}");
        assert_eq!(compiler["rustc"], canonical.to_str().unwrap(), "{receipt}");
        assert_eq!(
            receipt["rustc_binary_sha256"],
            format!("{:x}", Sha256::digest(fs::read(&canonical).unwrap())),
            "{receipt}"
        );
        let captured =
            fs::read_to_string(sandbox.artifacts_dir.join("capture/Captured.lean")).unwrap();
        assert!(
            captured.contains(&format!("import Trusted.Rustc.{dialect}.MirAst\n")),
            "{captured}"
        );
        let request: Value = serde_json::from_slice(
            &fs::read(sandbox.artifacts_dir.join("audit-request.json")).unwrap(),
        )
        .unwrap();
        // `TargetAuditRequest` serializes its fields in camelCase.
        assert_eq!(
            request["canonicalRoot"],
            format!("Trusted.MirSemantics.{dialect}.CrateTheorem"),
            "{request}"
        );
        let expected =
            fs::read_to_string(sandbox.artifacts_dir.join("generated/Expected.lean")).unwrap();
        assert!(
            expected.contains(&format!("Trusted.MirSemantics.{dialect}.CrateTheorem (")),
            "{expected}"
        );
    }
}

/// Boundary 1 before capture: the real sysroot compiler declared as another
/// supported compiler is refused without running capture.
#[test]
fn rejects_rustc_that_differs_from_rustc_version() {
    let tools = Tools::discover();
    let (rustc, (dialect, ..)) = sysroot_compiler(&tools);
    let (other, ..) = another_compiler(dialect);
    let sandbox = declared_sandbox("declared-mismatch");
    let (code, receipt) = run_declared(
        &tools,
        &sandbox,
        &tools.capture,
        Some((&rustc, other)),
        true,
    );
    assert_eq!(code, Some(2), "{receipt}");
    assert_eq!(receipt["status"], "tool_failed", "{receipt}");
    assert_eq!(receipt["phase"], "compiler", "{receipt}");
    let detail = receipt["detail"].as_str().unwrap();
    assert!(
        detail.contains(&format!("but --rustc-version {other} is {other}")),
        "{receipt}"
    );
    assert!(!sandbox.artifacts_dir.join("capture").exists(), "{receipt}");
}

/// Boundary 1 between `--rustc` and the capture driver: a compiler that
/// matches its declaration but not the driver's linked libraries is refused
/// by the driver.
#[test]
fn capture_driver_refuses_declared_rustc_of_another_compiler() {
    let tools = Tools::discover();
    let (_, (dialect, ..)) = sysroot_compiler(&tools);
    let (other, other_commit, other_date) = another_compiler(dialect);
    let fakes = tempfile::tempdir().unwrap();
    let rustc = fakes.path().join("rustc");
    executable_script(
        &rustc,
        &format!(
            "#!/bin/sh\nif [ \"$#\" -eq 2 ] && [ \"$1\" = --version ] && [ \"$2\" = --verbose ]; then\n\
             printf '%s\\n' 'rustc 1.0.0-dev (git_revisions:{other_commit})' 'binary: rustc' \
             'commit-hash: {other_commit}' 'commit-date: {other_date}'\nexit 0\nfi\nexit 97\n"
        ),
    );
    let sandbox = declared_sandbox("declared-driver-mismatch");
    let (code, receipt) = run_declared(
        &tools,
        &sandbox,
        &tools.capture,
        Some((&rustc, other)),
        true,
    );
    assert_eq!(code, Some(2), "{receipt}");
    assert_eq!(receipt["status"], "tool_failed", "{receipt}");
    assert_eq!(receipt["phase"], "capture", "{receipt}");
    let detail = receipt["detail"].as_str().unwrap();
    assert!(
        detail.contains(&format!("is {other} (commit-hash {other_commit}"))
            && detail.contains(&format!("but this capture driver links {dialect}")),
        "{receipt}"
    );
    assert!(
        !sandbox.artifacts_dir.join("capture/capture.json").exists(),
        "{receipt}"
    );
}

/// Tampered capture compiler fields fail closed at the manifest check, the
/// rendered-syntax check, or the declared-compiler check, all before Lean.
#[test]
fn rejects_tampered_capture_compiler_fields() {
    let tools = Tools::discover();
    let (rustc, (dialect, commit, date)) = sysroot_compiler(&tools);
    let (other, other_commit, other_date) = another_compiler(dialect);
    let replace = |field: &str, from: &str, to: &str| {
        format!("-e 's/\"{field}\": \"{from}\"/\"{field}\": \"{to}\"/g'")
    };
    let all_dialects = replace("mir_dialect", dialect, other);
    let without_version = format!(
        "{all_dialects} {} {}",
        replace("commit", commit, other_commit),
        replace("commit_date", date, other_date)
    );
    let consistent = format!(
        "{without_version} -e 's/{}/{}/g'",
        &commit[..9],
        &other_commit[..9]
    );
    let canonical_rustc = fs::canonicalize(&rustc).unwrap();
    let canonical_rustc = canonical_rustc.to_str().unwrap();
    let escaped_rustc = canonical_rustc.replace('/', "\\/");
    let cases = [
        // Only the top-level field: the two dialect fields disagree.
        (
            format!("-e '0,/\"mir_dialect\": \"{dialect}\"/s//\"mir_dialect\": \"{other}\"/'"),
            false,
            other,
            "unexpected capture schema or compiler".to_owned(),
        ),
        // Both dialect fields: they no longer match the commit.
        (
            all_dialects.clone(),
            false,
            other,
            "unexpected capture schema or compiler".to_owned(),
        ),
        // Commit, date, and dialects name another supported compiler, but
        // `compiler.version` still reports the linked compiler's short commit.
        (
            without_version,
            false,
            other,
            "unexpected capture schema or compiler".to_owned(),
        ),
        // An emptied `compiler.rustc` fails manifest authentication even
        // without `--rustc` / `--rustc-version`.
        (
            format!("-e 's/\"rustc\": \"{escaped_rustc}\"/\"rustc\": \"\"/'"),
            false,
            dialect,
            "unexpected capture schema or compiler".to_owned(),
        ),
        // Every compiler field names another supported compiler, but the
        // rendered subject still imports the real dialect's syntax.
        (
            consistent.clone(),
            false,
            other,
            format!("but the capture's compiler has MIR dialect {other}"),
        ),
        // With a declaration, the recorded compiler must be the declared one.
        (
            consistent,
            true,
            other,
            format!("capture reports compiler {other}"),
        ),
        // Even with the declared dialect intact, `compiler.rustc` must match
        // the canonical `--rustc` probed before capture.
        (
            format!("-e 's/\"rustc\": \"{escaped_rustc}\"/\"rustc\": \"\\/other\\/rustc\"/'"),
            true,
            dialect,
            format!("capture reports compiler {dialect} with rustc \"/other/rustc\""),
        ),
    ];
    for (index, (expressions, declare, expected_dialect, diagnostic)) in
        cases.into_iter().enumerate()
    {
        let wrappers = tempfile::tempdir().unwrap();
        let wrapper = wrappers.path().join("tampering-capture");
        executable_script(
            &wrapper,
            &format!(
                "#!/bin/sh\nout=\nprevious=\nfor argument in \"$@\"; do\n\
                 if [ \"$previous\" = --out-dir ]; then out=\"$argument\"; fi\n\
                 previous=\"$argument\"\ndone\n\
                 receipt=$('{}' \"$@\")\nstatus=$?\n\
                 if [ \"$status\" -eq 0 ]; then sed -i {expressions} \"$out/capture.json\" || exit 70; fi\n\
                 printf '%s\\n' \"$receipt\"\nexit \"$status\"\n",
                tools.capture.display()
            ),
        );
        let sandbox = declared_sandbox(&format!("tampered-{index}"));
        let declared = declare.then_some((rustc.as_path(), dialect));
        let (code, receipt) = run_declared(&tools, &sandbox, &wrapper, declared, true);
        assert_eq!(code, Some(2), "case {index}: {receipt}");
        assert_eq!(receipt["status"], "tool_failed", "case {index}: {receipt}");
        assert_eq!(receipt["phase"], "capture", "case {index}: {receipt}");
        assert!(
            receipt["detail"].as_str().unwrap().contains(&diagnostic),
            "case {index}: {receipt}"
        );
        // The tampering really happened on the retained manifest.
        let manifest: Value = serde_json::from_slice(
            &fs::read(sandbox.artifacts_dir.join("capture/capture.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(
            manifest["mir_dialect"], expected_dialect,
            "case {index}: {manifest}"
        );
        assert_ne!(
            manifest["compiler"]["rustc"].as_str(),
            (expected_dialect == dialect).then_some(canonical_rustc),
            "case {index}: {manifest}"
        );
        assert!(
            !sandbox
                .artifacts_dir
                .join("generated/Expected.lean")
                .exists(),
            "case {index}: Lean staging began"
        );
    }
}
