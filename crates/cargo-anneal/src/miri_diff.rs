// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Differential testing harness comparing upstream Miri verdicts against
//! Anneal's MIR-in-Lean operational semantics (`Trusted.Rustc.V2026_06_01.MirSemantics`).
//!
//! Reads a hermetic differential test manifest (`tests/miri-diff/manifest.toml`),
//! captures MIR from the corpus crate (`tests/miri-diff/corpus`) using the
//! Miri-matching compiler flags recorded in the manifest, generates Lean 4
//! proof and refutation obligations for every test entry, compiles them with
//! Lake, runs `trusted/audit/TrustedBoundary.lean` in `verify-audit` mode, and
//! verifies location-aware Undefined Behavior fault spans via the shared Anneal
//! oracle (`cargo_anneal::miri_oracle`).
//!
//! ## Policy on `known_anneal_bug` Entries
//!
//! Every `[tests.known_anneal_bug]` entry in `manifest.toml` records an
//! **unfixed bug** in Anneal's MIR-in-Lean model or MIR capture pipeline —
//! never a permanently admitted divergence. The harness enforces a two-way
//! regression ratchet:
//!
//! 1. Every test without `known_anneal_bug` must agree 100% with Miri:
//!    - `pass`: proved via `verifyTotalMirUnitPointBounded` or
//!      `verifyTotalMirScalarPointBounded` (`TotalVerificationResult`), or via
//!      `verifyTotalMirBounded` when the test links intra-crate callees (see
//!      below).
//!    - `panic`: proved via `verifySafePanicMirPointBounded`
//!      (`StatefulVerificationResult` with `post := False` and `¬ TotalClaim.holds`).
//!      A test whose body calls a function that is neither captured nor
//!      linked (such as the `core::fmt::Arguments` constructor that
//!      `panic!("...")` calls before `core::panicking::panic_fmt`) is instead
//!      proved via `verifyModularSafePanicMirBounded`
//!      (`ModularVerificationResult` with `post := False` under a
//!      frame-preserving rely contract on external calls, and
//!      `¬ TotalClaim.holds`), because `StatefulClaim.holds` lets an external
//!      call return a memory on which the caller can fault.
//!    - `ub`: refuted via `refuteMirPointByStrictUB`
//!      (`¬ StatefulClaim.holds ∧ ¬ TotalClaim.holds` from
//!      `reachesStrictUBBounded = true`, which rejects `FailureKind.unsupported`),
//!      AND verified via `probeMirDiffExecBounded` to fault at a statement or
//!      terminator span containing `miri_ub_span`.
//! 2. Every test with `known_anneal_bug` must match its exact recorded
//!    `observed_anneal_tag` (and `observed_anneal_ub_span`, when present) via
//!    `by rfl` in the Lean 4 kernel. As soon as an Anneal bug is fixed so that
//!    Anneal agrees with Miri (in both tag and UB fault location), the
//!    `known_anneal_bug_ratchet` theorem fails to type-check until the entry
//!    is removed from `manifest.toml`. Because `evalMirDiffTagBounded` stops
//!    at the first external call, the ratchet of a `panic` test also requires
//!    `reachesModularSafePanicBounded ... = false`, so it fails as soon as a
//!    modular certificate discharges the test.
//!
//! ## Linked Intra-Crate Callees
//!
//! A test whose MIR calls other functions captured from the corpus crate (such
//! as `pass_direct_fn_call` calling `helper_add_ten`) is evaluated with those
//! captured bodies linked as callees. Its certificate, refutation, or
//! `known_anneal_bug_ratchet`, and its UB-location probe, all start from
//! `initMachineStateWithMemoryAndCallees` with the item's scaffolded
//! `defaultCallees` table, and the certificate claims carry the same table in
//! `callees`. Only bodies captured from the corpus crate are ever linked; a call
//! to any other function remains an uninterpreted external call.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anneal_rustc_capture::{ANNEAL_CAPTURE_DIR_ENV, CapturedItemKind, UnitTargetRecord};

use crate::driver::{
    ANNEAL_CAPTURE_FILTER_ENV, CaptureDriverConfig, aggregate_unit_manifests, resolve_rustc_wrapper,
};
use crate::miri_oracle::{
    ComparisonVerdict, MiriOutcome, OracleItemSpec, SourcePos, SourceSpan, compare_miri_and_anneal,
    parse_anneal_probe_output,
};
use crate::obligations::{derive_item_module_suffix, module_suffix_to_rel_path};
use crate::scaffold::{ScaffoldConfig, extract_called_fn_defs, scaffold_workspace_with_config};
use crate::{
    normalize_path_against, resolve_lake_binary, run_lake_verify,
    run_trusted_boundary_verify_audit,
};

/// Expected Miri or observed Anneal outcome tag for a zero-argument differential
/// test entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MiriDiffVerdictSpec {
    /// Normal return with unit value `()`.
    PassUnit,
    /// Normal return with scalar `IntVal { bits, sizeBytes }`.
    PassScalar {
        /// Unsigned bit representation of the returned scalar.
        bits: u128,
        /// Width of the returned scalar in bytes.
        size_bytes: u32,
    },
    /// Unwinding panic (`MirOutcome.panic`).
    Panic,
    /// Strict undefined behavior (`MirOutcome.fault .ub`).
    Ub,
    /// Process abort (`MirOutcome.abort`).
    Abort,
    /// Semantics gap (`MirOutcome.fault .unsupported`).
    Unsupported,
    /// Uninterpreted external call (`MirEffect.call`).
    ExternalCall(String),
    /// Fuel exhaustion (`MirOutcome.fault .outOfFuel`).
    OutOfFuel,
}

impl MiriDiffVerdictSpec {
    /// Parse a compact verdict tag string from `manifest.toml`
    /// (`"pass:unit"`, `"pass:scalar:<bits>:<size>"`, `"panic"`, `"ub"`,
    /// `"abort"`, `"unsupported"`, `"externalCall:<def_path>"`, `"outOfFuel"`).
    pub fn parse(raw: &str) -> Result<Self, String> {
        let s = raw.trim();
        if s == "pass:unit" {
            return Ok(Self::PassUnit);
        }
        if let Some(rest) = s.strip_prefix("pass:scalar:") {
            let parts: Vec<&str> = rest.split(':').collect();
            if parts.len() != 2 {
                return Err(format!(
                    "invalid pass:scalar verdict '{s}'; expected 'pass:scalar:<bits>:<sizeBytes>'"
                ));
            }
            let bits = parts[0]
                .parse::<u128>()
                .map_err(|e| format!("invalid scalar bits in '{s}': {e}"))?;
            let size_bytes = parts[1]
                .parse::<u32>()
                .map_err(|e| format!("invalid scalar sizeBytes in '{s}': {e}"))?;
            return Ok(Self::PassScalar { bits, size_bytes });
        }
        if s == "panic" {
            return Ok(Self::Panic);
        }
        if s == "ub" {
            return Ok(Self::Ub);
        }
        if s == "abort" {
            return Ok(Self::Abort);
        }
        if s == "unsupported" {
            return Ok(Self::Unsupported);
        }
        if let Some(def_path) = s.strip_prefix("externalCall:") {
            let trimmed = def_path.trim();
            if trimmed.is_empty() {
                return Err("externalCall verdict requires a non-empty def_path".to_string());
            }
            return Ok(Self::ExternalCall(trimmed.to_string()));
        }
        if s == "outOfFuel" {
            return Ok(Self::OutOfFuel);
        }
        Err(format!("unrecognized Miri differential verdict tag '{s}'"))
    }

    /// Format this verdict back into its canonical manifest tag string.
    pub fn as_tag_str(&self) -> String {
        match self {
            Self::PassUnit => "pass:unit".to_string(),
            Self::PassScalar { bits, size_bytes } => format!("pass:scalar:{bits}:{size_bytes}"),
            Self::Panic => "panic".to_string(),
            Self::Ub => "ub".to_string(),
            Self::Abort => "abort".to_string(),
            Self::Unsupported => "unsupported".to_string(),
            Self::ExternalCall(def_path) => format!("externalCall:{def_path}"),
            Self::OutOfFuel => "outOfFuel".to_string(),
        }
    }

    /// Render the corresponding Lean `MirDiffTag` constructor expression.
    pub fn to_lean_mir_diff_tag(&self) -> String {
        match self {
            Self::PassUnit => "MirDiffTag.normalUnit".to_string(),
            Self::PassScalar { bits, size_bytes } => {
                format!("(MirDiffTag.normalScalar {bits} {size_bytes})")
            }
            Self::Panic => "MirDiffTag.panic".to_string(),
            Self::Ub => "MirDiffTag.ub".to_string(),
            Self::Abort => "MirDiffTag.abort".to_string(),
            Self::Unsupported => "MirDiffTag.unsupported".to_string(),
            Self::ExternalCall(def_path) => {
                let escaped = def_path.replace('\\', "\\\\").replace('"', "\\\"");
                format!("(MirDiffTag.externalCall \"{escaped}\")")
            }
            Self::OutOfFuel => "MirDiffTag.outOfFuel".to_string(),
        }
    }
}

/// Record of an unfixed bug in Anneal where Anneal's MIR-in-Lean evaluation
/// currently diverges from Miri's reference verdict.
///
/// These entries are tracked bugs to be fixed and ratcheted down to zero,
/// never permanently admitted divergences.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KnownAnnealBugSpec {
    /// Bug lifecycle status (must be `"open_bug"`).
    pub status: String,
    /// Classification of the divergence (`soundness_false_negative`,
    /// `completeness_false_positive_ub`, `completeness_wrong_return_value`,
    /// `incompleteness_unmodeled_intrinsic_or_call`, or `ub_location_mismatch`).
    pub bug_class: String,
    /// Current `MirDiffTag` produced by Anneal on this test.
    pub observed_anneal_tag: MiriDiffVerdictSpec,
    /// Optional statement/terminator span where Anneal raises `FailureKind.ub`
    /// (required when `bug_class == "ub_location_mismatch"`).
    pub observed_anneal_ub_span: Option<SourceSpan>,
    /// Anneal component where the root cause resides.
    pub suspected_component: String,
    /// Human-readable root-cause explanation of the bug.
    pub summary: String,
}

/// Single differential test entry in `tests/miri-diff/manifest.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MiriDiffTestEntry {
    /// Rust function identifier in `tests/miri-diff/corpus/src/lib.rs`.
    pub name: String,
    /// Feature category (`scalar_arithmetic`, `tree_borrows`, etc.).
    pub category: String,
    /// Relative path in the upstream public Miri test suite (`tests/pass/...`,
    /// `tests/panic/...`, or `tests/fail/...`).
    pub upstream_path: String,
    /// Reference Miri verdict.
    pub miri_verdict: MiriDiffVerdictSpec,
    /// Reference Miri Undefined Behavior fault position (`<file>:<line>:<col>`),
    /// required whenever `miri_verdict == MiriDiffVerdictSpec::Ub`.
    pub miri_ub_span: Option<SourcePos>,
    /// Step fuel bound passed to `evalMirDiffBounded` / `reachesStrictUBBounded`.
    pub fuel: u32,
    /// Optional unfixed Anneal bug annotation for tests that do not yet match
    /// Miri.
    pub known_anneal_bug: Option<KnownAnnealBugSpec>,
}

/// Parsed `tests/miri-diff/manifest.toml` specification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MiriDiffManifest {
    /// Manifest schema version (`1`).
    pub schema_version: u32,
    /// Pinned upstream `rustc` / Miri commit SHA.
    pub rustc_commit: String,
    /// Human-readable `rustc` version string.
    pub rustc_version: String,
    /// Public upstream repository URL.
    pub upstream_repo_url: String,
    /// Subtree inside the upstream repository containing Miri's `tests/`.
    pub upstream_tests_subtree: String,
    /// Flags passed to `miri` when evaluating the oracle (`["-Zmiri-tree-borrows"]`).
    pub miri_flags: Vec<String>,
    /// Flags passed via `RUSTFLAGS` when capturing MIR with `anneal-rustc-capture`.
    pub capture_rustflags: Vec<String>,
    /// Ordered differential test entries.
    pub tests: Vec<MiriDiffTestEntry>,
}

/// Configuration for executing the Miri differential test suite.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MiriDiffConfig {
    /// Root directory of the differential test corpus crate
    /// (`tests/miri-diff/corpus`).
    pub corpus_root: PathBuf,
    /// Path to `tests/miri-diff/manifest.toml`.
    pub manifest_path: PathBuf,
    /// Optional explicit path to the Anneal repository root.
    pub anneal_repo_root: Option<PathBuf>,
    /// Optional explicit path to `anneal-rustc-capture`.
    pub rustc_wrapper: Option<PathBuf>,
}

/// Summary of a completed Miri differential test suite verification and
/// `TrustedBoundary` kernel-replay run.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MiriDiffReport {
    /// Total number of differential test entries evaluated.
    pub total_tests: usize,
    /// Number of `pass` tests verified via `TotalVerificationResult`.
    pub verified_pass_count: usize,
    /// Number of `panic` tests verified via `verifySafePanicMirPointBounded`
    /// (or its callee-linked form) or `verifyModularSafePanicMirBounded`.
    pub verified_panic_count: usize,
    /// Number of `ub` tests refuted via `refuteMirPointByStrictUB`.
    pub verified_strict_ub_count: usize,
    /// Number of open Anneal bugs ratcheted via `known_anneal_bug_ratchet`.
    pub ratcheted_known_bug_count: usize,
    /// `Verify.<Crate>.<Item>` certificate modules audited by `TrustedBoundary`.
    pub audited_certificate_modules: Vec<String>,
    /// `Verify.<Crate>.<Item>` modules of `panic` tests certified by a
    /// `ModularVerificationResult` ([`MiriDiffPanicCertificate::Modular`])
    /// rather than a `StatefulVerificationResult`, in manifest order.
    pub modular_panic_certificate_modules: Vec<String>,
}

/// Load and parse `tests/miri-diff/manifest.toml` from `path`.
pub fn load_miri_diff_manifest(path: &Path) -> Result<MiriDiffManifest, String> {
    let text = fs::read_to_string(path).map_err(|err| {
        format!(
            "failed to read Miri differential manifest {}: {}",
            path.display(),
            err
        )
    })?;
    parse_miri_diff_manifest(&text)
}

/// Parse and validate `tests/miri-diff/manifest.toml` content.
pub fn parse_miri_diff_manifest(toml_text: &str) -> Result<MiriDiffManifest, String> {
    let mut schema_version: Option<u32> = None;
    let mut rustc_commit = String::new();
    let mut rustc_version = String::new();
    let mut upstream_repo_url = String::new();
    let mut upstream_tests_subtree = String::new();
    let mut miri_flags: Vec<String> = Vec::new();
    let mut capture_rustflags: Vec<String> = Vec::new();
    let mut tests: Vec<MiriDiffTestEntry> = Vec::new();

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Section {
        Top,
        Test,
        KnownBug,
    }

    let mut section = Section::Top;
    let mut current_test: BTreeMap<String, String> = BTreeMap::new();
    let mut current_bug: BTreeMap<String, String> = BTreeMap::new();
    let mut has_bug_section = false;

    let flush_test = |current_test: &mut BTreeMap<String, String>,
                      current_bug: &mut BTreeMap<String, String>,
                      has_bug_section: &mut bool,
                      tests: &mut Vec<MiriDiffTestEntry>|
     -> Result<(), String> {
        if current_test.is_empty() {
            return Ok(());
        }
        let name = current_test
            .remove("name")
            .ok_or_else(|| "missing 'name' in [[tests]] entry".to_string())?;
        let category = current_test
            .remove("category")
            .ok_or_else(|| format!("missing 'category' in [[tests]] entry '{name}'"))?;
        let upstream_path = current_test
            .remove("upstream_path")
            .ok_or_else(|| format!("missing 'upstream_path' in [[tests]] entry '{name}'"))?;
        if !upstream_path.starts_with("tests/") || upstream_path.contains("..") {
            return Err(format!(
                "invalid upstream_path '{upstream_path}' in test '{name}': must be a relative path starting with 'tests/'"
            ));
        }
        let miri_verdict_raw = current_test
            .remove("miri_verdict")
            .ok_or_else(|| format!("missing 'miri_verdict' in [[tests]] entry '{name}'"))?;
        let miri_verdict = MiriDiffVerdictSpec::parse(&miri_verdict_raw)
            .map_err(|e| format!("in test '{name}': {e}"))?;
        let miri_ub_span = match current_test.remove("miri_ub_span") {
            Some(raw_pos) => {
                if miri_verdict != MiriDiffVerdictSpec::Ub {
                    return Err(format!(
                        "test '{name}' has miri_ub_span '{raw_pos}' but miri_verdict is '{}'",
                        miri_verdict.as_tag_str()
                    ));
                }
                let pos = SourcePos::parse_rustc_pos(&raw_pos).ok_or_else(|| {
                    format!(
                        "invalid miri_ub_span '{raw_pos}' in test '{name}'; \
                         expected '<file>:<line>:<col>'"
                    )
                })?;
                Some(pos)
            }
            None => {
                if miri_verdict == MiriDiffVerdictSpec::Ub {
                    return Err(format!(
                        "missing 'miri_ub_span' in [[tests]] entry '{name}' with miri_verdict = \"ub\""
                    ));
                }
                None
            }
        };
        let fuel_raw = current_test
            .remove("fuel")
            .ok_or_else(|| format!("missing 'fuel' in [[tests]] entry '{name}'"))?;
        let fuel = fuel_raw
            .parse::<u32>()
            .map_err(|e| format!("invalid 'fuel' in test '{name}': {e}"))?;
        if fuel == 0 {
            return Err(format!("fuel must be > 0 in test '{name}'"));
        }

        let known_anneal_bug = if *has_bug_section {
            let status = current_bug.remove("status").ok_or_else(|| {
                format!("missing 'status' in [tests.known_anneal_bug] for '{name}'")
            })?;
            if status != "open_bug" {
                return Err(format!(
                    "invalid known_anneal_bug status '{status}' for '{name}': must be 'open_bug'"
                ));
            }
            let bug_class = current_bug.remove("bug_class").ok_or_else(|| {
                format!("missing 'bug_class' in [tests.known_anneal_bug] for '{name}'")
            })?;
            let observed_raw = current_bug.remove("observed_anneal_tag").ok_or_else(|| {
                format!("missing 'observed_anneal_tag' in [tests.known_anneal_bug] for '{name}'")
            })?;
            let observed_anneal_tag = MiriDiffVerdictSpec::parse(&observed_raw)
                .map_err(|e| format!("in known_anneal_bug for '{name}': {e}"))?;
            let observed_anneal_ub_span =
                if let Some(raw_span) = current_bug.remove("observed_anneal_ub_span") {
                    if observed_anneal_tag != MiriDiffVerdictSpec::Ub {
                        return Err(format!(
                            "known_anneal_bug for '{name}' has observed_anneal_ub_span '{raw_span}' \
                             but observed_anneal_tag is '{}' (expected 'ub')",
                            observed_anneal_tag.as_tag_str()
                        ));
                    }
                    let span = SourceSpan::parse_anneal_span(&raw_span).ok_or_else(|| {
                        format!(
                            "invalid observed_anneal_ub_span '{raw_span}' in known_anneal_bug \
                             for '{name}'; expected '<file>:<sline>:<scol>: <eline>:<ecol>'"
                        )
                    })?;
                    Some(span)
                } else {
                    None
                };

            if bug_class == "ub_location_mismatch" {
                let (
                    MiriDiffVerdictSpec::Ub,
                    MiriDiffVerdictSpec::Ub,
                    Some(miri_pos),
                    Some(anneal_span),
                ) = (
                    &miri_verdict,
                    &observed_anneal_tag,
                    miri_ub_span.as_ref(),
                    observed_anneal_ub_span.as_ref(),
                )
                else {
                    return Err(format!(
                        "known_anneal_bug for '{name}' with bug_class = \"ub_location_mismatch\" \
                         requires miri_verdict = \"ub\", observed_anneal_tag = \"ub\", \
                         miri_ub_span, and observed_anneal_ub_span"
                    ));
                };
                if anneal_span.contains_pos(miri_pos) {
                    return Err(format!(
                        "known_anneal_bug for '{name}' has observed_anneal_ub_span ({}) \
                         containing miri_ub_span ({}); remove the stale ub_location_mismatch entry",
                        anneal_span.display_short(),
                        miri_pos.display_short()
                    ));
                }
            } else if observed_anneal_tag == miri_verdict {
                return Err(format!(
                    "known_anneal_bug for '{name}' has observed_anneal_tag equal to miri_verdict ({}); remove the stale bug entry",
                    miri_verdict.as_tag_str()
                ));
            }
            let suspected_component =
                current_bug.remove("suspected_component").ok_or_else(|| {
                    format!(
                        "missing 'suspected_component' in [tests.known_anneal_bug] for '{name}'"
                    )
                })?;
            let summary = current_bug.remove("summary").ok_or_else(|| {
                format!("missing 'summary' in [tests.known_anneal_bug] for '{name}'")
            })?;
            if summary.trim().is_empty() || suspected_component.trim().is_empty() {
                return Err(format!(
                    "known_anneal_bug for '{name}' must have non-empty suspected_component and summary"
                ));
            }
            if let Some(unknown_key) = current_bug.keys().next() {
                return Err(format!(
                    "unknown key '{unknown_key}' in [tests.known_anneal_bug] for '{name}'"
                ));
            }
            current_bug.clear();
            *has_bug_section = false;
            Some(KnownAnnealBugSpec {
                status,
                bug_class,
                observed_anneal_tag,
                observed_anneal_ub_span,
                suspected_component,
                summary,
            })
        } else {
            None
        };

        if let Some(unknown_key) = current_test.keys().next() {
            return Err(format!(
                "unknown key '{unknown_key}' in [[tests]] entry '{name}'"
            ));
        }
        current_test.clear();
        tests.push(MiriDiffTestEntry {
            name,
            category,
            upstream_path,
            miri_verdict,
            miri_ub_span,
            fuel,
            known_anneal_bug,
        });
        Ok(())
    };

    for (line_idx, raw_line) in toml_text.lines().enumerate() {
        let line_no = line_idx + 1;
        let line = strip_toml_comment(raw_line).trim();
        if line.is_empty() {
            continue;
        }
        if line == "[[tests]]" {
            flush_test(
                &mut current_test,
                &mut current_bug,
                &mut has_bug_section,
                &mut tests,
            )?;
            section = Section::Test;
            continue;
        }
        if line == "[tests.known_anneal_bug]" {
            if section != Section::Test {
                return Err(format!(
                    "line {line_no}: [tests.known_anneal_bug] must immediately follow a [[tests]] block"
                ));
            }
            has_bug_section = true;
            section = Section::KnownBug;
            continue;
        }
        let Some((raw_key, raw_val)) = line.split_once('=') else {
            return Err(format!("line {line_no}: expected 'key = value', got '{line}'"));
        };
        let key = raw_key.trim();
        let val = raw_val.trim();

        match section {
            Section::Top => match key {
                "schema_version" => {
                    let v = val.parse::<u32>().map_err(|e| {
                        format!("line {line_no}: invalid schema_version '{val}': {e}")
                    })?;
                    schema_version = Some(v);
                }
                "rustc_commit" => {
                    rustc_commit = parse_toml_string(val, line_no)?;
                }
                "rustc_version" => {
                    rustc_version = parse_toml_string(val, line_no)?;
                }
                "upstream_repo_url" => {
                    upstream_repo_url = parse_toml_string(val, line_no)?;
                }
                "upstream_tests_subtree" => {
                    upstream_tests_subtree = parse_toml_string(val, line_no)?;
                }
                "miri_flags" => {
                    miri_flags = parse_toml_string_array(val, line_no)?;
                }
                "capture_rustflags" => {
                    capture_rustflags = parse_toml_string_array(val, line_no)?;
                }
                other => {
                    return Err(format!("line {line_no}: unknown top-level key '{other}'"));
                }
            },
            Section::Test => {
                let parsed = if val.starts_with('"') {
                    parse_toml_string(val, line_no)?
                } else {
                    val.to_string()
                };
                current_test.insert(key.to_string(), parsed);
            }
            Section::KnownBug => {
                let parsed = parse_toml_string(val, line_no)?;
                current_bug.insert(key.to_string(), parsed);
            }
        }
    }

    flush_test(
        &mut current_test,
        &mut current_bug,
        &mut has_bug_section,
        &mut tests,
    )?;

    if schema_version != Some(1) {
        return Err(format!(
            "unsupported manifest schema_version {:?}; expected 1",
            schema_version
        ));
    }
    if rustc_commit.is_empty() {
        return Err("manifest is missing rustc_commit".to_string());
    }
    if upstream_repo_url.is_empty() || !upstream_repo_url.starts_with("https://github.com/") {
        return Err(format!(
            "upstream_repo_url must be a public GitHub URL, got '{upstream_repo_url}'"
        ));
    }
    if tests.is_empty() {
        return Err("manifest must contain at least one [[tests]] entry".to_string());
    }

    let mut seen_names = BTreeSet::new();
    for entry in &tests {
        if !seen_names.insert(entry.name.clone()) {
            return Err(format!(
                "duplicate test name '{}' in manifest",
                entry.name
            ));
        }
    }

    Ok(MiriDiffManifest {
        schema_version: 1,
        rustc_commit,
        rustc_version,
        upstream_repo_url,
        upstream_tests_subtree,
        miri_flags,
        capture_rustflags,
        tests,
    })
}

fn strip_toml_comment(line: &str) -> &str {
    let mut in_quotes = false;
    let mut escaped = false;
    for (idx, ch) in line.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        if ch == '\\' && in_quotes {
            escaped = true;
            continue;
        }
        if ch == '"' {
            in_quotes = !in_quotes;
            continue;
        }
        if ch == '#' && !in_quotes {
            return &line[..idx];
        }
    }
    line
}

fn parse_toml_string(raw: &str, line_no: usize) -> Result<String, String> {
    let s = raw.trim();
    if s.len() < 2 || !s.starts_with('"') || !s.ends_with('"') {
        return Err(format!(
            "line {line_no}: expected quoted string, got '{s}'"
        ));
    }
    let inner = &s[1..s.len() - 1];
    let mut out = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            match chars.next() {
                Some('"') => out.push('"'),
                Some('\\') => out.push('\\'),
                Some('n') => out.push('\n'),
                Some('t') => out.push('\t'),
                Some(other) => {
                    return Err(format!(
                        "line {line_no}: unsupported escape '\\{other}' in string"
                    ));
                }
                None => {
                    return Err(format!("line {line_no}: trailing backslash in string"));
                }
            }
        } else {
            out.push(ch);
        }
    }
    Ok(out)
}

fn parse_toml_string_array(raw: &str, line_no: usize) -> Result<Vec<String>, String> {
    let s = raw.trim();
    if !s.starts_with('[') || !s.ends_with(']') {
        return Err(format!("line {line_no}: expected '[...]', got '{s}'"));
    }
    let inner = s[1..s.len() - 1].trim();
    if inner.is_empty() {
        return Ok(Vec::new());
    }
    let mut items = Vec::new();
    let mut current = String::new();
    let mut in_quotes = false;
    let mut escaped = false;
    for ch in inner.chars() {
        if escaped {
            current.push(ch);
            escaped = false;
            continue;
        }
        if ch == '\\' && in_quotes {
            current.push(ch);
            escaped = true;
            continue;
        }
        if ch == '"' {
            in_quotes = !in_quotes;
            current.push(ch);
            continue;
        }
        if ch == ',' && !in_quotes {
            let trimmed = current.trim();
            if !trimmed.is_empty() {
                items.push(parse_toml_string(trimmed, line_no)?);
            }
            current.clear();
            continue;
        }
        current.push(ch);
    }
    let tail = current.trim();
    if !tail.is_empty() {
        items.push(parse_toml_string(tail, line_no)?);
    }
    Ok(items)
}

/// Lean definitions of `activeSpan` and `probeMirDiffExecBounded`, which
/// evaluate a body like `evalMirDiffTagBounded` and additionally report the
/// span of the statement or terminator at which execution panicked, aborted,
/// faulted, or stopped at an external call (`"none"` on normal return).
///
/// Every rendered use must `open Trusted.Sequence` (for `get?`),
/// `Trusted.Rustc.V2026_06_01.MirSemantics`, and
/// `Anneal.Rustc.V2026_06_01.SymbolicEval` first.
const MIR_DIFF_PROBE_LEAN_DEFS: &str = "\
def activeSpan (body : CapturedMir) (st : MirExecState) : String :=\n  \
  let raw :=\n    \
    match st with\n    \
    | .running s =>\n      \
      let cur := s.memory.activeCallee.getD body\n      \
      match get? cur.basicBlocks s.frame.blockIdx with\n      \
      | some bb =>\n        \
        match get? bb.statements s.frame.stmtIdx with\n        \
        | some stmt => stmt.span\n        \
        | none => bb.terminator.span\n      \
      | none => \"none\"\n    \
    | _ => \"none\"\n  \
  if raw == \"\" || raw == \"<dummy>\" then \"none\" else raw\n\n\
def probeMirDiffExecBounded\n    \
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) :\n    \
    MirDiffTag × String :=\n  \
  match fuel with\n  \
  | 0 => (.outOfFuel, activeSpan body st)\n  \
  | fuel' + 1 =>\n    \
    match stepMirState body st with\n    \
    | .ret (.normal (.unit, _)) => (.normalUnit, \"none\")\n    \
    | .ret (.normal (.scalar sc, _)) => (.normalScalar sc.bits sc.sizeBytes, \"none\")\n    \
    | .ret (.normal (val, mem)) => ((MirDiffVerdict.normal val mem).toTagWithBody body, \"none\")\n    \
    | .ret .panic => (.panic, activeSpan body st)\n    \
    | .ret .abort => (.abort, activeSpan body st)\n    \
    | .tau st' => probeMirDiffExecBounded fuel' body st'\n    \
    | .vis (.inl (.fail .ub)) _ => (.ub, activeSpan body st)\n    \
    | .vis (.inl (.fail .unsupported)) _ => (.unsupported, activeSpan body st)\n    \
    | .vis (.inl (.fail .outOfFuel)) _ => (.outOfFuel, activeSpan body st)\n    \
    | .vis (.inr (.inl _)) k => probeMirDiffExecBounded fuel' body (k PUnit.unit)\n    \
    | .vis (.inr (.inr (.call req))) _ => (.externalCall req.defPath, activeSpan body st)\n\n";

/// Lean expression for the intra-crate callee table linked into a manifest
/// test's initial machine state.
///
/// An empty table renders the callee-free `initMachineStateWithMemory` form,
/// which `initMachineStateWithMemoryAndCallees` reduces to definitionally, so
/// tests without intra-crate calls keep their original statements.
struct LinkedCallees {
    /// Lean list literal `[Mir.<suffix>.body, ...]`, or `None` for an empty
    /// table.
    list_expr: Option<String>,
    /// Module suffixes (`<Crate>.<item>`) to import, in table order.
    suffixes: Vec<String>,
}

impl LinkedCallees {
    /// Validate `helper_module_suffixes` and build the callee table.
    ///
    /// Each suffix must name a captured `Mir.<suffix>` module, so it may contain
    /// only dot-separated identifier segments; anything else could inject Lean
    /// syntax into the generated certificate. Duplicates are rejected because a
    /// duplicated suffix indicates a caller bug rather than a meaningful table.
    fn new(helper_module_suffixes: &[String]) -> Result<Self, String> {
        let mut seen = BTreeSet::new();
        for suffix in helper_module_suffixes {
            if !is_lean_module_suffix(suffix) {
                return Err(format!(
                    "invalid linked callee module suffix '{suffix}': expected \
                     dot-separated Lean identifier segments"
                ));
            }
            if !seen.insert(suffix.as_str()) {
                return Err(format!("duplicate linked callee module suffix '{suffix}'"));
            }
        }
        let list_expr = (!helper_module_suffixes.is_empty()).then(|| {
            let elems: Vec<String> = helper_module_suffixes
                .iter()
                .map(|s| format!("Mir.{s}.body"))
                .collect();
            format!("[{}]", elems.join(", "))
        });
        Ok(Self {
            list_expr,
            suffixes: helper_module_suffixes.to_vec(),
        })
    }

    /// Lean expression for the initial `MachineState` of `Mir.{item}.body` on
    /// zero arguments and `emptyMemory` with this callee table linked.
    fn init_state_expr(&self, item: &str) -> String {
        match &self.list_expr {
            None => format!("initMachineStateWithMemory Mir.{item}.body [] emptyMemory"),
            Some(list) => format!(
                "initMachineStateWithMemoryAndCallees Mir.{item}.body [] emptyMemory {list}"
            ),
        }
    }
}

/// Return `true` when `suffix` is a sequence of at least two dot-separated
/// ASCII identifier segments (`<Crate>.<item>`), as produced for captured
/// `Mir.<Crate>.<item>` module names.
fn is_lean_module_suffix(suffix: &str) -> bool {
    let mut segs = suffix.split('.');
    let mut count = 0usize;
    while let Some(seg) = segs.next() {
        if seg.is_empty()
            || seg.starts_with(|c: char| c.is_ascii_digit())
            || !seg.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        {
            return false;
        }
        count += 1;
    }
    count >= 2
}

/// Header line of the `defaultCallees` definition in a scaffolded
/// `Obligations/<Item>.lean` module.
const DEFAULT_CALLEES_HEADER: &str = "def defaultCallees : List CapturedMir :=";

/// Read the `defaultCallees` table that scaffolding wrote for the item with
/// module suffix `item_suffix` into
/// `<dot_anneal>/generated/Obligations/<Item>.lean`, returning the module
/// suffixes of the linked bodies in table order.
///
/// Scaffolding computes this table as the cycle-safe transitive closure of the
/// captured MIR bodies reachable from the item's `.fnDef` references, so it
/// names only bodies captured from the corpus crate (including the item itself
/// when it is recursive) and never an uncaptured or synthetic body. Reusing it
/// keeps every differential theorem for a test linked to exactly the callees
/// that `cargo anneal verify` would link for the same item.
fn read_scaffolded_default_callees(
    dot_anneal: &Path,
    item_suffix: &str,
) -> Result<Vec<String>, String> {
    let obligation_path = dot_anneal
        .join("generated")
        .join("Obligations")
        .join(module_suffix_to_rel_path(item_suffix));
    let text = fs::read_to_string(&obligation_path).map_err(|err| {
        format!(
            "failed to read scaffolded obligations {}: {}",
            obligation_path.display(),
            err
        )
    })?;
    parse_default_callees_table(&text)
        .map_err(|err| format!("{}: {err}", obligation_path.display()))
}

/// Parse the `defaultCallees` table from scaffolded obligations source.
///
/// Scaffolding renders the table on the line after [`DEFAULT_CALLEES_HEADER`]
/// as either `.nil` or `[Mir.<suffix>.body, ...]`. Any other shape is an error
/// rather than an empty table, so a change to that rendering cannot silently
/// drop linked callees.
fn parse_default_callees_table(obligation_src: &str) -> Result<Vec<String>, String> {
    let mut lines = obligation_src.lines();
    while let Some(line) = lines.next() {
        if line.trim() != DEFAULT_CALLEES_HEADER {
            continue;
        }
        let value = lines
            .next()
            .map(str::trim)
            .ok_or_else(|| format!("`{DEFAULT_CALLEES_HEADER}` has no value line"))?;
        if value == ".nil" {
            return Ok(Vec::new());
        }
        let inner = value
            .strip_prefix('[')
            .and_then(|rest| rest.strip_suffix(']'))
            .ok_or_else(|| format!("unexpected `defaultCallees` value `{value}`"))?;
        return inner
            .split(',')
            .map(|elem| {
                let elem = elem.trim();
                elem.strip_prefix("Mir.")
                    .and_then(|rest| rest.strip_suffix(".body"))
                    .filter(|suffix| is_lean_module_suffix(suffix))
                    .map(str::to_string)
                    .ok_or_else(|| format!("unexpected `defaultCallees` entry `{elem}`"))
            })
            .collect();
    }
    Err(format!("missing `{DEFAULT_CALLEES_HEADER}`"))
}

/// Render the `.anneal/generated/Verify/<Crate>/<test.name>.lean` module for a
/// single differential test entry whose MIR calls no captured intra-crate
/// function.
///
/// Equivalent to [`render_miri_diff_verify_module_with_callees`] with an empty
/// callee table.
pub fn render_miri_diff_verify_module(
    crate_camel: &str,
    def_id: &str,
    entry: &MiriDiffTestEntry,
) -> Result<(String, bool), String> {
    render_miri_diff_verify_module_with_callees(crate_camel, def_id, entry, &[])
}

/// Certificate shape for a `panic` entry without a `known_anneal_bug`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MiriDiffPanicCertificate {
    /// `StatefulVerificationResult` with `post := False`, and
    /// `¬ TotalClaim.holds`, from direct bounded evaluation
    /// (`reachesPanicBounded`), which stops at the first uninterpreted
    /// external call.
    Stateful,
    /// `ModularVerificationResult` with `post := False` under a
    /// frame-preserving rely contract on external calls, and
    /// `¬ TotalClaim.holds`, from `verifyModularSafePanicMirBounded`.
    ///
    /// An entry that panics after an uninterpreted external call (such as the
    /// `core::fmt::Arguments` constructor that `panic!("...")` calls before
    /// `core::panicking::panic_fmt`) needs this shape: `StatefulClaim.holds`
    /// lets that call return any answer, including a memory with a corrupted
    /// call frame on which the caller can fault, so it is false for such an
    /// entry.
    Modular,
}

/// Render the `.anneal/generated/Verify/<Crate>/<test.name>.lean` module for a
/// single differential test entry, linking the captured intra-crate bodies
/// `Mir.<suffix>.body` for every `suffix` in `helper_module_suffixes` as
/// callees of the entry's initial machine state.
///
/// `helper_module_suffixes` must list only captured `Mir.*` modules (for
/// example `MiriDiffCorpus.helper_add_ten`); `stage_miri_diff_workspace` passes
/// the entry's scaffolded `defaultCallees` table. With an empty table the module
/// is identical to the callee-free rendering. With a non-empty table:
///
/// - `pass` entries prove `TotalVerificationResult` with
///   `callees := [Mir.<suffix>.body, ...]` via `verifyTotalMirBounded`;
/// - `panic` entries prove `StatefulVerificationResult` (`post := False`) and
///   refute `TotalClaim.holds` with the same callees;
/// - `ub` entries refute both `StatefulClaim.holds` and `TotalClaim.holds`
///   with the same callees; and
/// - `known_anneal_bug` ratchets evaluate the entry with the callees linked, so
///   a ratchet recorded before linking fails once linking fixes the bug.
///
/// A `panic` entry gets the [`MiriDiffPanicCertificate::Stateful`] shape; use
/// [`render_miri_diff_verify_module_with_panic_certificate`] to choose the
/// shape.
///
/// Returns `(module_source, is_trusted_certificate_module)` where
/// `is_trusted_certificate_module` is `true` for non-bug `pass` and `panic`
/// entries whose `theorem verified` has head type `TotalVerificationResult`,
/// `StatefulVerificationResult`, or `ModularVerificationResult`. Returns an
/// error for an invalid or duplicated callee suffix, or for a non-bug entry
/// whose Miri verdict has no certificate shape.
pub fn render_miri_diff_verify_module_with_callees(
    crate_camel: &str,
    def_id: &str,
    entry: &MiriDiffTestEntry,
    helper_module_suffixes: &[String],
) -> Result<(String, bool), String> {
    render_miri_diff_verify_module_with_panic_certificate(
        crate_camel,
        def_id,
        entry,
        helper_module_suffixes,
        MiriDiffPanicCertificate::Stateful,
    )
}

/// Render the `.anneal/generated/Verify/<Crate>/<test.name>.lean` module for a
/// single differential test entry exactly as
/// [`render_miri_diff_verify_module_with_callees`] does, except that a non-bug
/// `panic` entry gets the certificate shape `panic_certificate`.
///
/// `panic_certificate` has no effect on other entries. A
/// `known_anneal_bug_ratchet` for a `panic` entry always also requires
/// `reachesModularSafePanicBounded ... = false`, so reintroducing a bug entry
/// for a test that a modular certificate discharges fails to build.
pub fn render_miri_diff_verify_module_with_panic_certificate(
    crate_camel: &str,
    def_id: &str,
    entry: &MiriDiffTestEntry,
    helper_module_suffixes: &[String],
    panic_certificate: MiriDiffPanicCertificate,
) -> Result<(String, bool), String> {
    let item = format!("{crate_camel}.{}", entry.name);
    let fuel = entry.fuel;
    let callees = LinkedCallees::new(helper_module_suffixes)?;
    let init_state = callees.init_state_expr(&item);
    let mut out = String::new();
    out.push_str(&format!("-- @anneal-def-id: {def_id}\nimport Mir.{item}\n"));
    for suffix in &callees.suffixes {
        // A self-recursive entry links its own body, which `import Mir.{item}`
        // above already provides.
        if *suffix != item {
            out.push_str(&format!("import Mir.{suffix}\n"));
        }
    }
    out.push_str(&format!(
        "import Anneal.Rustc.V2026_06_01.SymbolicEval\n\n\
         namespace Verify.{item}\n\n\
         open Trusted.Rustc.V2026_06_01.MirAst\n\
         open Trusted.Rustc.V2026_06_01.MirSemantics\n\
         open Trusted.VerificationResult\n\
         open Anneal.Rustc.V2026_06_01.SymbolicEval\n\n\
         /-!\n\
         Differential test verification module for `{def_id}`\n\
         (upstream Miri source: `{}`).\n\
         -/\n\n",
        entry.upstream_path
    ));

    if let Some(ref bug) = entry.known_anneal_bug {
        let tag_expr = bug.observed_anneal_tag.to_lean_mir_diff_tag();
        if let Some(ref ub_span) = bug.observed_anneal_ub_span {
            let escaped_span = ub_span
                .display_short()
                .replace('\\', "\\\\")
                .replace('"', "\\\"");
            out.push_str(&format!(
                "-- @anneal-miri-diff-kind: known_anneal_bug\n\
                 -- UNFIXED ANNEAL BUG ({} in `{}`):\n\
                 -- {}\n\
                 -- Reference Miri verdict: `{}`\n\
                 -- Observed Anneal tag:    `{}`\n\
                 -- Observed Anneal UB span: `{}`\n\
                 open Trusted.Sequence\n\n\
                 {MIR_DIFF_PROBE_LEAN_DEFS}\
                 theorem known_anneal_bug_ratchet :\n    \
                     probeMirDiffExecBounded {fuel} Mir.{item}.body\n      \
                       (.running ({init_state})) =\n      \
                     ({tag_expr}, \"{escaped_span}\") := by\n  \
                   rfl\n\n\
                 end Verify.{item}\n",
                bug.bug_class,
                bug.suspected_component,
                bug.summary,
                entry.miri_verdict.as_tag_str(),
                bug.observed_anneal_tag.as_tag_str(),
                ub_span.display_short()
            ));
            return Ok((out, false));
        }
        out.push_str(&format!(
            "-- @anneal-miri-diff-kind: known_anneal_bug\n\
             -- UNFIXED ANNEAL BUG ({} in `{}`):\n\
             -- {}\n\
             -- Reference Miri verdict: `{}`\n\
             -- Observed Anneal tag:    `{}`\n",
            bug.bug_class,
            bug.suspected_component,
            bug.summary,
            entry.miri_verdict.as_tag_str(),
            bug.observed_anneal_tag.as_tag_str()
        ));
        if entry.miri_verdict == MiriDiffVerdictSpec::Panic {
            // `evalMirDiffTagBounded` stops at the first uninterpreted external
            // call, so on its own this ratchet would keep holding for a test
            // that `verifyModularSafePanicMirBounded` certifies. Requiring the
            // modular checker to reject the test makes the ratchet fail as soon
            // as the modular certificate applies.
            out.push_str(&format!(
                "-- The ratchet of a `panic` test also requires the modular safe-panic\n\
                 -- checker to reject it, so it fails once a modular certificate applies.\n\
                 theorem known_anneal_bug_ratchet :\n    \
                     evalMirDiffTagBounded {fuel} Mir.{item}.body\n      \
                       ({init_state}) =\n      \
                     {tag_expr} ∧\n    \
                     reachesModularSafePanicBounded {fuel} Mir.{item}.body\n      \
                       ({init_state}) =\n      \
                     false := by\n  \
                   exact ⟨rfl, rfl⟩\n\n\
                 end Verify.{item}\n"
            ));
            return Ok((out, false));
        }
        out.push_str(&format!(
            "theorem known_anneal_bug_ratchet :\n    \
                 evalMirDiffTagBounded {fuel} Mir.{item}.body\n      \
                   ({init_state}) =\n      \
                 {tag_expr} := by\n  \
               rfl\n\n\
             end Verify.{item}\n"
        ));
        return Ok((out, false));
    }

    if entry.miri_verdict == MiriDiffVerdictSpec::Panic
        && panic_certificate == MiriDiffPanicCertificate::Modular
    {
        render_modular_panic_certificate(
            &mut out,
            &item,
            fuel,
            callees.list_expr.as_deref(),
        );
        return Ok((out, true));
    }
    let Some(ref callees_expr) = callees.list_expr else {
        return render_callee_free_certificate(&mut out, &item, fuel, entry)
            .map(|cert| (out, cert));
    };
    render_linked_certificate(&mut out, &item, fuel, entry, callees_expr).map(|cert| (out, cert))
}

/// Append the `ModularVerificationResult` statement of a modular `panic`
/// certificate for `Mir.{item}.body`, indented by `indent`.
///
/// `TrustedBoundary.checkStatementOrigins` rejects a `theorem verified` whose
/// statement mentions an `Anneal.*` constant, so the statement spells out
/// `Anneal.Rustc.V2026_06_01.SymbolicEval.framePreservingCallContract` with
/// `Trusted.*` constants only; the two agree by unfolding. `callees_expr`
/// (`None` for an empty callee table) must match the table that the proof
/// passes to `verifyModularSafePanicMirBounded`.
fn push_modular_panic_claim(
    out: &mut String,
    item: &str,
    callees_expr: Option<&str>,
    indent: &str,
) {
    out.push_str(&format!(
        "{indent}ModularVerificationResult {{\n\
         {indent}  body := Mir.{item}.body\n\
         {indent}  envAssumed := MirCallContract.holdsOn {{\n\
         {indent}    pre := fun _ => True\n\
         {indent}    post := fun req ans =>\n\
         {indent}      match ans with\n\
         {indent}      | .returned _ memAfter => callFramePreserved req.memory memAfter\n\
         {indent}      | .panicked memAfter => callFramePreserved req.memory memAfter\n\
         {indent}      | .aborted => True\n\
         {indent}  }}\n\
         {indent}  pre := fun args mem => args = [] ∧ mem = emptyMemory\n\
         {indent}  post := fun _ _ _ _ => False\n"
    ));
    if let Some(callees_expr) = callees_expr {
        out.push_str(&format!("{indent}  callees := {callees_expr}\n"));
    }
    out.push_str(&format!("{indent}}}"));
}

/// Append the refuted `TotalClaim` of a `panic` certificate for
/// `Mir.{item}.body`, indented by `indent`.
fn push_refuted_total_claim(
    out: &mut String,
    item: &str,
    callees_expr: Option<&str>,
    indent: &str,
) {
    out.push_str(&format!(
        "{indent}¬ ({{\n\
         {indent}  body := Mir.{item}.body\n\
         {indent}  pre := fun args mem => args = [] ∧ mem = emptyMemory\n\
         {indent}  post := fun _ _ _ _ => True\n"
    ));
    if let Some(callees_expr) = callees_expr {
        out.push_str(&format!("{indent}  callees := {callees_expr}\n"));
    }
    out.push_str(&format!("{indent}}} : TotalClaim).holds"));
}

/// Append the modular certificate of a non-bug `panic` entry whose execution
/// passes through an uninterpreted external call before it panics
/// ([`MiriDiffPanicCertificate::Modular`]), linking the callee table
/// `callees_expr` (`None` for an empty table).
///
/// `theorem verified` proves `ModularVerificationResult` with `post := False`
/// under the frame-preserving rely contract on external calls, and
/// `total_refuted` refutes `TotalClaim.holds` along the path on which every
/// external call returns normally, both through
/// `verifyModularSafePanicMirBounded`.
fn render_modular_panic_certificate(
    out: &mut String,
    item: &str,
    fuel: u32,
    callees_expr: Option<&str>,
) {
    let proof = format!(
        "verifyModularSafePanicMirBounded Mir.{item}.body {} {fuel} [] emptyMemory",
        callees_expr.unwrap_or("[]")
    );
    out.push_str("-- @anneal-miri-diff-kind: panic_modular\ntheorem verified :\n");
    push_modular_panic_claim(out, item, callees_expr, "    ");
    out.push_str(&format!(" :=\n  ({proof}).1\n\ntheorem total_refuted :\n"));
    push_refuted_total_claim(out, item, callees_expr, "    ");
    out.push_str(&format!(" :=\n  ({proof}).2\n\nabbrev Certificate : Prop :=\n"));
    push_modular_panic_claim(out, item, callees_expr, "  ");
    out.push_str(" ∧\n");
    push_refuted_total_claim(out, item, callees_expr, "  ");
    out.push_str(&format!(
        "\n\n\
         theorem full_panic_certificate : Certificate :=\n  \
           And.intro verified total_refuted\n\n\
         end Verify.{item}\n"
    ));
}

/// Append the certificate or refutation for a non-bug entry that links no
/// callees, returning whether it is a trusted certificate module.
fn render_callee_free_certificate(
    out: &mut String,
    item: &str,
    fuel: u32,
    entry: &MiriDiffTestEntry,
) -> Result<bool, String> {
    match &entry.miri_verdict {
        MiriDiffVerdictSpec::PassUnit => {
            out.push_str(&format!(
                "-- @anneal-miri-diff-kind: pass_unit\n\
                 theorem verified :\n    \
                     TotalVerificationResult {{\n      \
                       body := Mir.{item}.body\n      \
                       pre := fun args mem => args = [] ∧ mem = emptyMemory\n      \
                       post := fun _ _ retVal _ => retVal = .unit\n    \
                     }} :=\n  \
                   verifyTotalMirUnitPointBounded Mir.{item}.body {fuel} [] emptyMemory\n\n\
                 abbrev Certificate : Prop :=\n  \
                   TotalVerificationResult {{\n    \
                     body := Mir.{item}.body\n    \
                     pre := fun args mem => args = [] ∧ mem = emptyMemory\n    \
                     post := fun _ _ retVal _ => retVal = .unit\n  \
                   }}\n\n\
                 end Verify.{item}\n"
            ));
            Ok(true)
        }
        MiriDiffVerdictSpec::PassScalar { bits, size_bytes } => {
            out.push_str(&format!(
                "-- @anneal-miri-diff-kind: pass_scalar\n\
                 theorem verified :\n    \
                     TotalVerificationResult {{\n      \
                       body := Mir.{item}.body\n      \
                       pre := fun args mem => args = [] ∧ mem = emptyMemory\n      \
                       post := fun _ _ retVal _ =>\n        \
                         retVal = .scalar {{ bits := {bits}, sizeBytes := {size_bytes} }}\n    \
                     }} :=\n  \
                   verifyTotalMirScalarPointBounded Mir.{item}.body {fuel} [] emptyMemory {bits} {size_bytes}\n\n\
                 abbrev Certificate : Prop :=\n  \
                   TotalVerificationResult {{\n    \
                     body := Mir.{item}.body\n    \
                     pre := fun args mem => args = [] ∧ mem = emptyMemory\n    \
                     post := fun _ _ retVal _ =>\n      \
                       retVal = .scalar {{ bits := {bits}, sizeBytes := {size_bytes} }}\n  \
                   }}\n\n\
                 end Verify.{item}\n"
            ));
            Ok(true)
        }
        MiriDiffVerdictSpec::Panic => {
            out.push_str(&format!(
                "-- @anneal-miri-diff-kind: panic\n\
                 theorem verified :\n    \
                     StatefulVerificationResult {{\n      \
                       body := Mir.{item}.body\n      \
                       pre := fun args mem => args = [] ∧ mem = emptyMemory\n      \
                       post := fun _ _ _ _ => False\n    \
                     }} :=\n  \
                   (verifySafePanicMirPointBounded Mir.{item}.body {fuel} [] emptyMemory).1\n\n\
                 theorem total_refuted :\n    \
                     ¬ ({{\n      \
                       body := Mir.{item}.body\n      \
                       pre := fun args mem => args = [] ∧ mem = emptyMemory\n      \
                       post := fun _ _ _ _ => True\n    \
                     }} : TotalClaim).holds :=\n  \
                   (verifySafePanicMirPointBounded Mir.{item}.body {fuel} [] emptyMemory).2\n\n\
                 abbrev Certificate : Prop :=\n  \
                   StatefulVerificationResult {{\n    \
                     body := Mir.{item}.body\n    \
                     pre := fun args mem => args = [] ∧ mem = emptyMemory\n    \
                     post := fun _ _ _ _ => False\n  \
                   }} ∧\n  \
                   ¬ ({{\n    \
                     body := Mir.{item}.body\n    \
                     pre := fun args mem => args = [] ∧ mem = emptyMemory\n    \
                     post := fun _ _ _ _ => True\n  \
                   }} : TotalClaim).holds\n\n\
                 theorem full_panic_certificate : Certificate :=\n  \
                   And.intro verified total_refuted\n\n\
                 end Verify.{item}\n"
            ));
            Ok(true)
        }
        MiriDiffVerdictSpec::Ub => {
            out.push_str(&format!(
                "-- @anneal-miri-diff-kind: strict_ub\n\
                 abbrev Certificate : Prop :=\n  \
                   ¬ ({{\n    \
                     body := Mir.{item}.body\n    \
                     pre := fun args mem => args = [] ∧ mem = emptyMemory\n    \
                     post := fun _ _ _ _ => True\n  \
                   }} : StatefulClaim).holds ∧\n  \
                   ¬ ({{\n    \
                     body := Mir.{item}.body\n    \
                     pre := fun args mem => args = [] ∧ mem = emptyMemory\n    \
                     post := fun _ _ _ _ => True\n  \
                   }} : TotalClaim).holds\n\n\
                 theorem strict_ub_refuted : Certificate :=\n  \
                   refuteMirPointByStrictUB Mir.{item}.body {fuel} [] emptyMemory\n\n\
                 end Verify.{item}\n"
            ));
            Ok(false)
        }
        other => Err(format!(
            "test '{}' has unsupported reference Miri verdict '{}' without a [tests.known_anneal_bug] entry",
            entry.name,
            other.as_tag_str()
        )),
    }
}

/// Append the certificate or refutation for a non-bug entry whose claims link
/// the callee table `callees_expr`, returning whether it is a trusted
/// certificate module.
///
/// The point combinators used by [`render_callee_free_certificate`] fix
/// `callees := []`, so these proofs instead instantiate the general bounded
/// combinators (`verifyTotalMirBounded`, `verifyStatefulMirBounded`,
/// `refuteTotalClaimByBoundedPanic`, and the strict-UB refutations), each of
/// which evaluates `initMachineStateWithMemoryAndCallees body args mem
/// c.callees`.
fn render_linked_certificate(
    out: &mut String,
    item: &str,
    fuel: u32,
    entry: &MiriDiffTestEntry,
    callees_expr: &str,
) -> Result<bool, String> {
    let pre = "fun args mem => args = [] ∧ mem = emptyMemory";
    let init_running = format!(
        "(.running (initMachineStateWithMemoryAndCallees Mir.{item}.body [] emptyMemory {callees_expr}))"
    );
    match &entry.miri_verdict {
        MiriDiffVerdictSpec::PassUnit | MiriDiffVerdictSpec::PassScalar { .. } => {
            let (kind, post, wp_lemma) = match &entry.miri_verdict {
                MiriDiffVerdictSpec::PassScalar { bits, size_bytes } => (
                    "pass_scalar",
                    format!("retVal = .scalar {{ bits := {bits}, sizeBytes := {size_bytes} }}"),
                    format!(
                        "wpCoalBounded_of_evalMirDiffExecBounded_normalScalar {fuel} Mir.{item}.body\n      \
                           {init_running}\n      \
                           {bits} {size_bytes} (by rfl)"
                    ),
                ),
                _ => (
                    "pass_unit",
                    "retVal = .unit".to_string(),
                    format!(
                        "wpCoalBounded_of_evalMirDiffExecBounded_normalUnit {fuel} Mir.{item}.body\n      \
                           {init_running}\n      \
                           (by rfl)"
                    ),
                ),
            };
            out.push_str(&format!(
                "-- @anneal-miri-diff-kind: {kind}\n\
                 theorem verified :\n    \
                     TotalVerificationResult {{\n      \
                       body := Mir.{item}.body\n      \
                       pre := {pre}\n      \
                       post := fun _ _ retVal _ => {post}\n      \
                       callees := {callees_expr}\n    \
                     }} :=\n  \
                   Anneal.Rustc.V2026_06_01.Lower.verifyTotalMirBounded _ {fuel} (by\n    \
                     rintro args mem ⟨rfl, rfl⟩\n    \
                     exact {wp_lemma})\n\n\
                 abbrev Certificate : Prop :=\n  \
                   TotalVerificationResult {{\n    \
                     body := Mir.{item}.body\n    \
                     pre := {pre}\n    \
                     post := fun _ _ retVal _ => {post}\n    \
                     callees := {callees_expr}\n  \
                   }}\n\n\
                 end Verify.{item}\n"
            ));
            Ok(true)
        }
        MiriDiffVerdictSpec::Panic => {
            out.push_str(&format!(
                "-- @anneal-miri-diff-kind: panic\n\
                 theorem verified :\n    \
                     StatefulVerificationResult {{\n      \
                       body := Mir.{item}.body\n      \
                       pre := {pre}\n      \
                       post := fun _ _ _ _ => False\n      \
                       callees := {callees_expr}\n    \
                     }} :=\n  \
                   Anneal.Rustc.V2026_06_01.Lower.verifyStatefulMirBounded _ {fuel} (by\n    \
                     rintro args mem ⟨rfl, rfl⟩\n    \
                     exact wpMirBounded_of_reachesPanicBounded {fuel} Mir.{item}.body\n      \
                       (initMachineStateWithMemoryAndCallees Mir.{item}.body [] emptyMemory {callees_expr})\n      \
                       (by rfl))\n\n\
                 theorem total_refuted :\n    \
                     ¬ ({{\n      \
                       body := Mir.{item}.body\n      \
                       pre := {pre}\n      \
                       post := fun _ _ _ _ => True\n      \
                       callees := {callees_expr}\n    \
                     }} : TotalClaim).holds :=\n  \
                   refuteTotalClaimByBoundedPanic _ {fuel} [] emptyMemory ⟨rfl, rfl⟩\n\n\
                 abbrev Certificate : Prop :=\n  \
                   StatefulVerificationResult {{\n    \
                     body := Mir.{item}.body\n    \
                     pre := {pre}\n    \
                     post := fun _ _ _ _ => False\n    \
                     callees := {callees_expr}\n  \
                   }} ∧\n  \
                   ¬ ({{\n    \
                     body := Mir.{item}.body\n    \
                     pre := {pre}\n    \
                     post := fun _ _ _ _ => True\n    \
                     callees := {callees_expr}\n  \
                   }} : TotalClaim).holds\n\n\
                 theorem full_panic_certificate : Certificate :=\n  \
                   And.intro verified total_refuted\n\n\
                 end Verify.{item}\n"
            ));
            Ok(true)
        }
        MiriDiffVerdictSpec::Ub => {
            out.push_str(&format!(
                "-- @anneal-miri-diff-kind: strict_ub\n\
                 abbrev Certificate : Prop :=\n  \
                   ¬ ({{\n    \
                     body := Mir.{item}.body\n    \
                     pre := {pre}\n    \
                     post := fun _ _ _ _ => True\n    \
                     callees := {callees_expr}\n  \
                   }} : StatefulClaim).holds ∧\n  \
                   ¬ ({{\n    \
                     body := Mir.{item}.body\n    \
                     pre := {pre}\n    \
                     post := fun _ _ _ _ => True\n    \
                     callees := {callees_expr}\n  \
                   }} : TotalClaim).holds\n\n\
                 theorem strict_ub_refuted : Certificate :=\n  \
                   ⟨refuteStatefulClaimByStrictUB _ {fuel} [] emptyMemory ⟨rfl, rfl⟩,\n   \
                    refuteTotalClaimByStrictUB _ {fuel} [] emptyMemory ⟨rfl, rfl⟩⟩\n\n\
                 end Verify.{item}\n"
            ));
            Ok(false)
        }
        other => Err(format!(
            "test '{}' has unsupported reference Miri verdict '{}' without a [tests.known_anneal_bug] entry",
            entry.name,
            other.as_tag_str()
        )),
    }
}

/// Render the differential `.anneal/generated/CrateVerify.lean` rollup module.
///
/// The rollup's `crateClaim : CrateClaim` bundles every non-bug `pass`, `panic`,
/// and `ub` test (plus any helper items in the crate) using pure `Trusted.*` /
/// `Mir.*` statement propositions, while `CrateVerify.verified`'s proof term
/// also binds every `known_anneal_bug_ratchet` theorem so `TrustedBoundary`'s
/// transitive constant closure and kernel replay audit every manifest test.
pub fn render_miri_diff_crate_verify_module(
    crate_name: &str,
    crate_camel: &str,
    manifest: &MiriDiffManifest,
    records_by_name: &BTreeMap<String, &UnitTargetRecord>,
    helper_records: &[&UnitTargetRecord],
) -> String {
    let mut out = String::new();
    out.push_str("import Trusted\n");
    for helper in helper_records {
        let suffix = derive_item_module_suffix(helper);
        out.push_str(&format!("import Verify.{suffix}\n"));
    }
    for entry in &manifest.tests {
        out.push_str(&format!("import Verify.{crate_camel}.{}\n", entry.name));
    }

    out.push_str("\nnamespace CrateVerify\n\n");
    out.push_str("open Trusted.VerificationResult\n\n");
    out.push_str(&format!(
        "/-!\nDisposable Miri differential testing rollup for `{crate_name}`.\n-/\n\n"
    ));

    // Collect all items that have a pure `Trusted.*` statement proposition
    // (`helper` items + all non-bug `pass`, `panic`, and `ub` entries).
    struct RollupEntry {
        def_id: String,
        sha: String,
        cert_expr: String,
        proof_expr: String,
    }

    let mut rollup_entries: Vec<RollupEntry> = Vec::new();
    for helper in helper_records {
        let suffix = derive_item_module_suffix(helper);
        rollup_entries.push(RollupEntry {
            def_id: helper.target.def_id.clone(),
            sha: helper.target.mir_module_sha256.clone(),
            cert_expr: format!("Verify.{suffix}.Certificate"),
            proof_expr: format!("Verify.{suffix}.verified"),
        });
    }

    let mut bug_ratchet_exprs: Vec<String> = Vec::new();
    for entry in &manifest.tests {
        let rec = records_by_name
            .get(&entry.name)
            .expect("validated record presence");
        let item = format!("{crate_camel}.{}", entry.name);
        if entry.known_anneal_bug.is_some() {
            bug_ratchet_exprs.push(format!("Verify.{item}.known_anneal_bug_ratchet"));
            continue;
        }
        let proof_expr = match entry.miri_verdict {
            MiriDiffVerdictSpec::PassUnit | MiriDiffVerdictSpec::PassScalar { .. } => {
                format!("Verify.{item}.verified")
            }
            MiriDiffVerdictSpec::Panic => format!("Verify.{item}.full_panic_certificate"),
            MiriDiffVerdictSpec::Ub => format!("Verify.{item}.strict_ub_refuted"),
            _ => unreachable!(),
        };
        rollup_entries.push(RollupEntry {
            def_id: rec.target.def_id.clone(),
            sha: rec.target.mir_module_sha256.clone(),
            cert_expr: format!("Verify.{item}.Certificate"),
            proof_expr,
        });
    }

    out.push_str(&format!(
        "def crateClaim : CrateClaim where\n  \
           crateName := \"{crate_name}\"\n  \
           mirDialect := \"V2026_06_01\"\n  \
           items := [\n"
    ));
    for (idx, r) in rollup_entries.iter().enumerate() {
        let comma = if idx + 1 < rollup_entries.len() {
            ","
        } else {
            ""
        };
        out.push_str(&format!(
            "    {{ identity := {{\n        \
                     defPath := \"{}\"\n        \
                     mirDialect := \"V2026_06_01\"\n        \
                     mirModuleSha256 := \"{}\"\n      \
                   }}\n      \
                   certificate := {}\n    \
                 }}{comma}\n",
            r.def_id, r.sha, r.cert_expr
        ));
    }
    out.push_str("  ]\n\n");

    let mut conj_proof = String::from("True.intro");
    for r in rollup_entries.iter().rev() {
        conj_proof = format!("(And.intro {} {conj_proof})", r.proof_expr);
    }

    out.push_str("theorem verified : CrateVerificationResult crateClaim :=\n");
    for (idx, ratchet) in bug_ratchet_exprs.iter().enumerate() {
        out.push_str(&format!("  let _bug_{idx} := {ratchet}\n"));
    }
    out.push_str(&format!(
        "  {{ proof := And.intro (by intro h; nomatch h) {conj_proof} }}\n\n\
         end CrateVerify\n"
    ));
    out
}

/// Capture MIR for `config.corpus_root` with the manifest's `capture_rustflags`,
/// scaffold `.anneal/`, and write the Miri differential `Verify` and
/// `CrateVerify` Lean modules.
///
/// Each test's `Verify` module links the scaffolded `defaultCallees` table of
/// its item (`.anneal/generated/Obligations/<Item>.lean`), so a test that calls
/// another captured function of the corpus crate is evaluated with that
/// function's captured MIR rather than stopping at an external call.
pub fn stage_miri_diff_workspace(
    config: &MiriDiffConfig,
    manifest: &MiriDiffManifest,
) -> Result<(MiriDiffReport, Vec<String>), String> {
    let base_dir = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let corpus_root = normalize_path_against(&base_dir, &config.corpus_root);
    let units_dir = corpus_root.join("target").join("anneal").join("units");
    if units_dir.exists() {
        let _ = fs::remove_dir_all(&units_dir);
    }
    fs::create_dir_all(&units_dir).map_err(|err| {
        format!(
            "failed to create capture units directory {}: {}",
            units_dir.display(),
            err
        )
    })?;

    let driver_cfg = CaptureDriverConfig {
        workspace_root: corpus_root.clone(),
        manifest_path: None,
        units_dir: units_dir.clone(),
        rustc_wrapper: config.rustc_wrapper.clone(),
        filter: None,
        extra_cargo_args: vec!["--lib".to_string()],
    };

    let cargo_bin = env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
    let mut cmd = std::process::Command::new(cargo_bin);
    cmd.current_dir(&corpus_root);
    cmd.arg("check").arg("--lib");
    let wrapper = resolve_rustc_wrapper(&driver_cfg);
    let rustflags = manifest.capture_rustflags.join(" ");
    cmd.env("RUSTC_WORKSPACE_WRAPPER", wrapper);
    cmd.env(ANNEAL_CAPTURE_DIR_ENV, &units_dir);
    cmd.env("RUSTFLAGS", rustflags);
    cmd.env_remove(ANNEAL_CAPTURE_FILTER_ENV);

    let status = cmd
        .status()
        .map_err(|err| format!("failed to execute cargo check on Miri corpus: {err}"))?;
    if !status.success() {
        return Err(format!(
            "cargo check failed on Miri corpus with status {status}"
        ));
    }

    let (_capture_manifest, records) = aggregate_unit_manifests(&units_dir)?;
    let scaffold_cfg = ScaffoldConfig {
        workspace_root: corpus_root.clone(),
        units_dir: Some(units_dir),
        anneal_repo_root: config.anneal_repo_root.clone(),
        init_spec_templates: false,
        init_proof_templates: false,
    };
    scaffold_workspace_with_config(&scaffold_cfg, &records)?;
    let dot_anneal = corpus_root.join(".anneal");

    let subject_records: Vec<&UnitTargetRecord> = records
        .iter()
        .filter(|r| r.item_kind == CapturedItemKind::Subject)
        .collect();
    if subject_records.is_empty() {
        return Err("zero subject functions captured from Miri differential corpus".to_string());
    }

    let crate_name = subject_records[0]
        .target
        .def_id
        .split("::")
        .next()
        .unwrap_or("miri_diff_corpus")
        .to_string();
    let sample_suffix = derive_item_module_suffix(subject_records[0]);
    let crate_camel = sample_suffix
        .split('.')
        .next()
        .ok_or_else(|| format!("invalid item suffix '{sample_suffix}'"))?
        .to_string();

    let mut records_by_name: BTreeMap<String, &UnitTargetRecord> = BTreeMap::new();
    for rec in &subject_records {
        let short_name = rec
            .target
            .def_id
            .rsplit("::")
            .next()
            .unwrap_or(&rec.target.def_id)
            .to_string();
        records_by_name.insert(short_name, *rec);
    }

    let manifest_names: BTreeSet<String> =
        manifest.tests.iter().map(|t| t.name.clone()).collect();
    let mut helper_records: Vec<&UnitTargetRecord> = Vec::new();
    for (name, rec) in &records_by_name {
        if !manifest_names.contains(name) {
            helper_records.push(*rec);
        }
    }

    let verify_root = corpus_root.join(".anneal/generated/Verify");
    let mut certificate_modules: Vec<String> = Vec::new();
    for helper in &helper_records {
        let suffix = derive_item_module_suffix(helper);
        certificate_modules.push(format!("Verify.{suffix}"));
    }
    let def_id_by_suffix: BTreeMap<String, String> = records
        .iter()
        .map(|r| (derive_item_module_suffix(r), r.target.def_id.clone()))
        .collect();

    let mut verified_pass_count = 0usize;
    let mut verified_panic_count = 0usize;
    let mut verified_strict_ub_count = 0usize;
    let mut ratcheted_known_bug_count = 0usize;
    let mut modular_panic_certificate_modules: Vec<String> = Vec::new();

    for entry in &manifest.tests {
        let Some(rec) = records_by_name.get(&entry.name) else {
            return Err(format!(
                "manifest test '{}' was not found in captured MIR subjects for crate '{}'",
                entry.name, crate_name
            ));
        };
        let suffix = derive_item_module_suffix(rec);
        let rel_path = module_suffix_to_rel_path(&suffix);
        let verify_path = verify_root.join(rel_path);
        let linked_callees = read_scaffolded_default_callees(&dot_anneal, &suffix)?;
        let panic_certificate = if entry.miri_verdict == MiriDiffVerdictSpec::Panic
            && entry.known_anneal_bug.is_none()
        {
            classify_panic_certificate(
                &dot_anneal,
                &suffix,
                &linked_callees,
                &def_id_by_suffix,
            )?
        } else {
            MiriDiffPanicCertificate::Stateful
        };
        if panic_certificate == MiriDiffPanicCertificate::Modular {
            modular_panic_certificate_modules.push(format!("Verify.{suffix}"));
        }
        let (content, is_cert) = render_miri_diff_verify_module_with_panic_certificate(
            &crate_camel,
            &rec.target.def_id,
            entry,
            &linked_callees,
            panic_certificate,
        )?;
        fs::write(&verify_path, content).map_err(|err| {
            format!(
                "failed to write differential Verify module {}: {}",
                verify_path.display(),
                err
            )
        })?;
        if is_cert {
            certificate_modules.push(format!("Verify.{suffix}"));
        }
        if entry.known_anneal_bug.is_some() {
            ratcheted_known_bug_count += 1;
        } else {
            match entry.miri_verdict {
                MiriDiffVerdictSpec::PassUnit | MiriDiffVerdictSpec::PassScalar { .. } => {
                    verified_pass_count += 1;
                }
                MiriDiffVerdictSpec::Panic => {
                    verified_panic_count += 1;
                }
                MiriDiffVerdictSpec::Ub => {
                    verified_strict_ub_count += 1;
                }
                _ => {}
            }
        }
    }

    certificate_modules.sort();
    let crate_verify_content = render_miri_diff_crate_verify_module(
        &crate_name,
        &crate_camel,
        manifest,
        &records_by_name,
        &helper_records,
    );
    let crate_verify_path = corpus_root.join(".anneal/generated/CrateVerify.lean");
    fs::write(&crate_verify_path, crate_verify_content).map_err(|err| {
        format!(
            "failed to write differential CrateVerify.lean {}: {}",
            crate_verify_path.display(),
            err
        )
    })?;

    let report = MiriDiffReport {
        total_tests: manifest.tests.len(),
        verified_pass_count,
        verified_panic_count,
        verified_strict_ub_count,
        ratcheted_known_bug_count,
        audited_certificate_modules: certificate_modules.clone(),
        modular_panic_certificate_modules,
    };
    Ok((report, certificate_modules))
}

/// `def_id`s of the call targets that
/// `Trusted.Rustc.V2026_06_01.MirSemantics.Terminators` models inline without
/// emitting an external `MirCallE` interaction (`isUnwindingPanicDefPath`,
/// `isAbortingPanicDefPath`, `isUnreachableCallTarget`,
/// `isDirectExactDivTarget`, and `classifyRustIntrinsic?` other than
/// `const_eval_select`, whose runtime target may be unlinked).
///
/// `Terminators` handles the panic, abort, and unreachable entry points inline
/// only in a diverging call (`target = .none`), which is how `rustc` calls
/// these `!`-returning functions; a returning call to one of them would still
/// be an external call. The unit test
/// `trusted_inline_call_def_paths_match_trusted_terminators` fails when this
/// list and those `Trusted` definitions diverge, and a stale list cannot make
/// [`classify_panic_certificate`] unsound.
const TRUSTED_INLINE_CALL_DEF_PATHS: &[&str] = &[
    // `isUnwindingPanicDefPath`
    "core::panicking::panic",
    "core::panicking::panic_fmt",
    "core::panicking::panic_fmt::panic_impl",
    "core::panicking::const_panic_fmt",
    "core::panicking::assert_failed",
    "core::panicking::assert_failed_inner",
    "core::panicking::assert_matches_failed",
    "core::slice::index::slice_index_fail",
    "core::panicking::panic_bounds_check",
    "core::panicking::panic_explicit",
    "core::panicking::panic_display",
    "core::panicking::panic_str_2015",
    "core::panicking::unreachable_display",
    "core::option::unwrap_failed",
    "core::option::expect_failed",
    "core::result::unwrap_failed",
    "core::panicking::panic_const::panic_const_add_overflow",
    "core::panicking::panic_const::panic_const_sub_overflow",
    "core::panicking::panic_const::panic_const_mul_overflow",
    "core::panicking::panic_const::panic_const_div_overflow",
    "core::panicking::panic_const::panic_const_rem_overflow",
    "core::panicking::panic_const::panic_const_neg_overflow",
    "core::panicking::panic_const::panic_const_shr_overflow",
    "core::panicking::panic_const::panic_const_shl_overflow",
    "core::panicking::panic_const::panic_const_div_by_zero",
    "core::panicking::panic_const::panic_const_rem_by_zero",
    // `isAbortingPanicDefPath`
    "core::panicking::panic_nounwind",
    "core::panicking::panic_nounwind_fmt",
    "core::panicking::panic_nounwind_fmt::panic_impl",
    "core::panicking::panic_nounwind_nobacktrace",
    "core::panicking::panic_in_cleanup",
    "core::panicking::panic_cannot_unwind",
    "core::panicking::panic_misaligned_pointer_dereference",
    "core::panicking::panic_null_pointer_dereference",
    "core::panicking::panic_invalid_enum_construction",
    "core::intrinsics::abort",
    // `isUnreachableCallTarget`
    "core::hint::unreachable_unchecked",
    "std::hint::unreachable_unchecked",
    "core::intrinsics::unreachable",
    // `isDirectExactDivTarget` and non-dispatching `classifyRustIntrinsic?`
    "core::intrinsics::exact_div",
    "core::intrinsics::ub_checks",
    "core::intrinsics::arith_offset",
    "core::intrinsics::ctlz",
    "core::intrinsics::ctlz_nonzero",
    "core::intrinsics::cttz",
    "core::intrinsics::cttz_nonzero",
    "core::intrinsics::ctpop",
    "core::intrinsics::bswap",
    "core::intrinsics::bitreverse",
    "core::intrinsics::wrapping_add",
    "core::intrinsics::wrapping_sub",
    "core::intrinsics::wrapping_mul",
    "core::intrinsics::saturating_add",
    "core::intrinsics::saturating_sub",
    "core::intrinsics::unchecked_shl",
    "core::intrinsics::unchecked_shr",
    "core::intrinsics::unchecked_add",
    "core::intrinsics::unchecked_sub",
    "core::intrinsics::unchecked_mul",
    "core::intrinsics::unchecked_div",
    "core::intrinsics::unchecked_rem",
    "core::intrinsics::three_way_compare",
    "core::intrinsics::size_of_val",
    "core::intrinsics::align_of_val",
];

/// Return `true` when `def_id` is one of [`TRUSTED_INLINE_CALL_DEF_PATHS`].
fn is_trusted_inline_call_def_path(def_id: &str) -> bool {
    TRUSTED_INLINE_CALL_DEF_PATHS.contains(&def_id)
}

/// Choose the certificate shape of the non-bug `panic` entry whose captured
/// body has module suffix `item_suffix` and links the callee table
/// `linked_callees`, using `def_id_by_suffix` to map captured module suffixes
/// to `def_id`s.
///
/// Direct evaluation (`reachesPanicBounded`) stops at the first call to a
/// function that is neither linked nor modeled inline by `Trusted`. The entry
/// therefore gets the [`MiriDiffPanicCertificate::Modular`] certificate when
/// its body or the body of a linked callee references a function (as
/// scaffolding collects callee references, from `.fnDef "<def_id>"`) that is
/// not the entry itself, not a linked callee, and not modeled inline by
/// `Trusted.Rustc.V2026_06_01.MirSemantics.Terminators`
/// ([`is_trusted_inline_call_def_path`]), and the
/// [`MiriDiffPanicCertificate::Stateful`] certificate otherwise.
///
/// The classification only selects which certificate the Lean kernel checks,
/// so a misclassification cannot produce an unsound certificate: a `Stateful`
/// certificate for a body that reaches an external call fails to build, and a
/// `Modular` certificate still holds for a body that panics without reaching
/// one (it then costs only the stronger-looking `Stateful` statement).
fn classify_panic_certificate(
    dot_anneal: &Path,
    item_suffix: &str,
    linked_callees: &[String],
    def_id_by_suffix: &BTreeMap<String, String>,
) -> Result<MiriDiffPanicCertificate, String> {
    let bodies: Vec<&str> = std::iter::once(item_suffix)
        .chain(linked_callees.iter().map(String::as_str))
        .collect();
    let mut linked_def_ids = BTreeSet::new();
    for suffix in &bodies {
        let def_id = def_id_by_suffix.get(*suffix).ok_or_else(|| {
            format!("no captured MIR record has module suffix '{suffix}'")
        })?;
        linked_def_ids.insert(def_id.as_str());
    }
    let mir_root = dot_anneal.join("generated").join("Mir");
    for suffix in &bodies {
        let mir_path = mir_root.join(module_suffix_to_rel_path(suffix));
        let mir_text = fs::read_to_string(&mir_path).map_err(|err| {
            format!(
                "failed to read captured MIR module {}: {}",
                mir_path.display(),
                err
            )
        })?;
        if extract_called_fn_defs(&mir_text).iter().any(|def_id| {
            !linked_def_ids.contains(def_id.as_str())
                && !is_trusted_inline_call_def_path(def_id.as_str())
        }) {
            return Ok(MiriDiffPanicCertificate::Modular);
        }
    }
    Ok(MiriDiffPanicCertificate::Stateful)
}

/// Run the full Miri differential test suite: load `manifest.toml`, capture MIR
/// from the corpus crate, generate Lean proof/refutation/ratchet modules,
/// compile them with Lake, run `TrustedBoundary.lean` in `verify-audit` mode,
/// and verify location-aware UB spans via the shared Anneal oracle.
pub fn run_miri_diff_suite(config: &MiriDiffConfig) -> Result<MiriDiffReport, String> {
    let manifest = load_miri_diff_manifest(&config.manifest_path)?;
    let (report, certificate_modules) = stage_miri_diff_workspace(config, &manifest)?;
    let base_dir = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let corpus_root = normalize_path_against(&base_dir, &config.corpus_root);
    let anneal_repo_root = config
        .anneal_repo_root
        .as_deref()
        .map(|r| normalize_path_against(&base_dir, r));
    let dot_anneal = corpus_root.join(".anneal");

    run_lake_verify(&dot_anneal)?;
    run_trusted_boundary_verify_audit(
        &corpus_root,
        anneal_repo_root.as_deref(),
        false,
        None,
        &certificate_modules,
    )?;

    let crate_camel = certificate_modules
        .first()
        .and_then(|m| m.strip_prefix("Verify."))
        .and_then(|s| s.split('.').next())
        .unwrap_or("MiriDiffCorpus");
    verify_miri_diff_ub_locations(&dot_anneal, crate_camel, &manifest)?;

    Ok(report)
}

/// Render `oracle/MiriOracleProbe.lean`, which prints one
/// `ANNEAL_PROBE\t<name>\t<tag>\t<span>` line (the format read by
/// `parse_anneal_probe_output`) for each `(item, linked_callees)` pair, starting
/// each item from zero arguments and `emptyMemory` with its callee table linked.
fn render_linked_probe_module(
    crate_camel: &str,
    items: &[(OracleItemSpec, Vec<String>)],
) -> Result<String, String> {
    let mut out = String::from("import Anneal.Rustc.V2026_06_01.SymbolicEval\n");
    let mut imported = BTreeSet::new();
    for (item, linked_callees) in items {
        let item_suffix = format!("{crate_camel}.{}", item.name);
        for suffix in std::iter::once(&item_suffix).chain(linked_callees) {
            if imported.insert(suffix.clone()) {
                out.push_str(&format!("import Mir.{suffix}\n"));
            }
        }
    }
    out.push_str(&format!(
        "\nnamespace MiriOracleProbe\n\n\
         open Trusted.Sequence\n\
         open Trusted.Rustc.V2026_06_01.MirAst\n\
         open Trusted.Rustc.V2026_06_01.MirSemantics\n\
         open Trusted.VerificationResult\n\
         open Anneal.Rustc.V2026_06_01.SymbolicEval\n\n\
         {MIR_DIFF_PROBE_LEAN_DEFS}\
         def formatTag : MirDiffTag → String\n  \
           | .normalUnit => \"pass:unit\"\n  \
           | .normalScalar bits sz => s!\"pass:scalar:{{bits}}:{{sz}}\"\n  \
           | .normalOther => \"pass:other\"\n  \
           | .panic => \"panic\"\n  \
           | .abort => \"abort\"\n  \
           | .ub => \"ub\"\n  \
           | .unsupported => \"unsupported\"\n  \
           | .externalCall p => s!\"externalCall:{{p}}\"\n  \
           | .outOfFuel => \"outOfFuel\"\n\n\
         def formatProbeLine (name : String) (fuel : Nat) (body : CapturedMir) (s : MachineState) : String :=\n  \
           let (tag, span) := probeMirDiffExecBounded fuel body (.running s)\n  \
           s!\"ANNEAL_PROBE\\t{{name}}\\t{{formatTag tag}}\\t{{span}}\"\n\n"
    ));
    for (item, linked_callees) in items {
        let item_suffix = format!("{crate_camel}.{}", item.name);
        let init_state = LinkedCallees::new(linked_callees)?.init_state_expr(&item_suffix);
        let escaped_name = item.name.replace('\\', "\\\\").replace('"', "\\\"");
        out.push_str(&format!(
            "#eval IO.println (formatProbeLine \"{escaped_name}\" {} Mir.{item_suffix}.body\n  \
               ({init_state}))\n",
            item.fuel
        ));
    }
    out.push_str("\nend MiriOracleProbe\n");
    Ok(out)
}

/// Evaluate `MiriOracleProbe.lean` via `lake env lean` inside `dot_anneal` and
/// verify that every `known_anneal_bug` entry with `observed_anneal_ub_span`
/// matches Anneal's fault span and every non-bug `ub` entry's Anneal fault span
/// contains `miri_ub_span`.
///
/// Each probed entry is evaluated with its scaffolded `defaultCallees` table
/// linked, matching the initial state of the entry's `Verify` module.
pub fn verify_miri_diff_ub_locations(
    dot_anneal: &Path,
    crate_camel: &str,
    manifest: &MiriDiffManifest,
) -> Result<(), String> {
    let mut probe_items = Vec::new();
    for entry in &manifest.tests {
        let needs_ub_probe = entry.miri_verdict == MiriDiffVerdictSpec::Ub
            || entry
                .known_anneal_bug
                .as_ref()
                .is_some_and(|b| b.observed_anneal_ub_span.is_some());
        if needs_ub_probe {
            let item_suffix = format!("{crate_camel}.{}", entry.name);
            let linked_callees = read_scaffolded_default_callees(dot_anneal, &item_suffix)?;
            probe_items.push((
                OracleItemSpec::with_fuel(&entry.name, entry.fuel),
                linked_callees,
            ));
        }
    }
    if probe_items.is_empty() {
        return Ok(());
    }

    let oracle_dir = dot_anneal.join("oracle");
    fs::create_dir_all(&oracle_dir)
        .map_err(|err| format!("failed to create {}: {}", oracle_dir.display(), err))?;
    let probe_path = oracle_dir.join("MiriOracleProbe.lean");
    let probe_src = render_linked_probe_module(crate_camel, &probe_items)?;
    fs::write(&probe_path, &probe_src)
        .map_err(|err| format!("failed to write {}: {}", probe_path.display(), err))?;

    let lake_bin = resolve_lake_binary();
    let probe_out = Command::new(&lake_bin)
        .current_dir(dot_anneal)
        .arg("env")
        .arg("lean")
        .arg("oracle/MiriOracleProbe.lean")
        .output()
        .map_err(|err| {
            format!(
                "failed to execute '{} env lean oracle/MiriOracleProbe.lean': {}",
                lake_bin.display(),
                err
            )
        })?;
    if !probe_out.status.success() {
        let stdout = String::from_utf8_lossy(&probe_out.stdout);
        let stderr = String::from_utf8_lossy(&probe_out.stderr);
        return Err(format!(
            "Lean UB span probe failed in {} ({}):\n{}\n{}",
            dot_anneal.display(),
            probe_out.status,
            stdout,
            stderr
        ));
    }

    let stdout = String::from_utf8_lossy(&probe_out.stdout);
    let parsed = parse_anneal_probe_output(&stdout)?;

    for entry in &manifest.tests {
        if let Some(ref bug) = entry.known_anneal_bug {
            if let Some(ref expected_span) = bug.observed_anneal_ub_span {
                let Some(outcome) = parsed.get(&entry.name) else {
                    return Err(format!(
                        "missing Anneal probe output for known_anneal_bug test '{}'",
                        entry.name
                    ));
                };
                if outcome.span() != Some(expected_span) {
                    return Err(format!(
                        "known_anneal_bug UB span mismatch for '{}': manifest records '{}', \
                         Anneal produced '{:?}'",
                        entry.name,
                        expected_span.display_short(),
                        outcome.span()
                    ));
                }
            }
            continue;
        }

        if entry.miri_verdict == MiriDiffVerdictSpec::Ub {
            let Some(ref miri_pos) = entry.miri_ub_span else {
                return Err(format!(
                    "missing miri_ub_span on UB test '{}'",
                    entry.name
                ));
            };
            let Some(anneal_outcome) = parsed.get(&entry.name) else {
                return Err(format!(
                    "missing Anneal probe output for UB test '{}'",
                    entry.name
                ));
            };
            let miri_outcome = MiriOutcome::Ub {
                pos: Some(miri_pos.clone()),
                message: String::new(),
            };
            let verdict = compare_miri_and_anneal(&miri_outcome, anneal_outcome);
            if verdict != ComparisonVerdict::Agree {
                return Err(format!(
                    "UB location mismatch on '{}': Miri faulted at '{}', \
                     Anneal produced '{}' (verdict: {:?})",
                    entry.name,
                    miri_pos.display_short(),
                    anneal_outcome.summary_tag(),
                    verdict
                ));
            }
        }
    }

    Ok(())
}

/// Render a deterministic human-readable summary of a completed Miri
/// differential test run.
///
/// The summary lists separately the `panic` certificates that are
/// `ModularVerificationResult`s: `TrustedBoundary` reports them as
/// unconditional because they use no `Assumptions.*` axiom, but each one holds
/// only for external callees that return or unwind to the caller's call frame.
pub fn render_miri_diff_report(report: &MiriDiffReport) -> String {
    format!(
        "Anneal <-> Miri Differential Testing Summary:\n\
         \x20 Total corpus tests:              {}\n\
         \x20 Verified `pass` (TotalClaim):    {}\n\
         \x20 Verified `panic` (SafePanic):    {}\n\
         \x20   of which modular (frame rely): {}\n\
         \x20 Refuted `ub` (StrictUB):         {}\n\
         \x20 Open Anneal bugs (ratcheted):    {}\n\
         \x20 TrustedBoundary kernel replay:   PASS\n",
        report.total_tests,
        report.verified_pass_count,
        report.verified_panic_count,
        report.modular_panic_certificate_modules.len(),
        report.verified_strict_ub_count,
        report.ratcheted_known_bug_count
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(name: &str, miri_verdict: MiriDiffVerdictSpec) -> MiriDiffTestEntry {
        MiriDiffTestEntry {
            name: name.to_string(),
            category: "control_flow_and_calls".to_string(),
            upstream_path: "tests/pass/calls.rs".to_string(),
            miri_verdict,
            miri_ub_span: None,
            fuel: 128,
            known_anneal_bug: None,
        }
    }

    #[test]
    fn parse_default_callees_table_reads_scaffolded_tables_and_rejects_other_shapes() {
        let linked = "/-- Default transitive callee table. -/\n\
                      def defaultCallees : List CapturedMir :=\n  \
                        [Mir.MiriDiffCorpus.helper_add_ten.body, Mir.MiriDiffCorpus.helper_b.body]\n\n";
        assert_eq!(
            parse_default_callees_table(linked).expect("parse linked table"),
            vec![
                "MiriDiffCorpus.helper_add_ten".to_string(),
                "MiriDiffCorpus.helper_b".to_string()
            ]
        );
        let empty = "def defaultCallees : List CapturedMir :=\n  .nil\n";
        assert_eq!(
            parse_default_callees_table(empty).expect("parse empty table"),
            Vec::<String>::new()
        );
        for malformed in [
            "def defaultCallees : List CapturedMir :=\n  []\n",
            "def defaultCallees : List CapturedMir :=\n  [helper.body]\n",
            "def defaultCallees : List CapturedMir :=\n  [Mir.Bad Name.body]\n",
            "def defaultCallees : List CapturedMir :=\n",
            "def other : List CapturedMir :=\n  .nil\n",
        ] {
            assert!(
                parse_default_callees_table(malformed).is_err(),
                "malformed table must be rejected: {malformed:?}"
            );
        }
    }

    #[test]
    fn verify_module_without_callees_is_unchanged_and_with_callees_links_captured_bodies() {
        let pass = entry(
            "pass_direct_fn_call",
            MiriDiffVerdictSpec::PassScalar {
                bits: 42,
                size_bytes: 4,
            },
        );
        let def_id = "miri_diff_corpus::pass_direct_fn_call";
        let (plain, plain_cert) =
            render_miri_diff_verify_module("MiriDiffCorpus", def_id, &pass).expect("render");
        let (empty, empty_cert) =
            render_miri_diff_verify_module_with_callees("MiriDiffCorpus", def_id, &pass, &[])
                .expect("render with empty callee table");
        assert_eq!(plain, empty);
        assert!(plain_cert && empty_cert);
        assert!(plain.contains("verifyTotalMirScalarPointBounded"));
        assert!(!plain.contains("callees :="));

        let helpers = vec!["MiriDiffCorpus.helper_add_ten".to_string()];
        let (linked, linked_cert) =
            render_miri_diff_verify_module_with_callees("MiriDiffCorpus", def_id, &pass, &helpers)
                .expect("render with linked callees");
        assert!(linked_cert);
        assert!(linked.contains(
            "import Mir.MiriDiffCorpus.pass_direct_fn_call\n\
             import Mir.MiriDiffCorpus.helper_add_ten\n\
             import Anneal.Rustc.V2026_06_01.SymbolicEval\n"
        ));
        assert_eq!(
            linked
                .matches("callees := [Mir.MiriDiffCorpus.helper_add_ten.body]")
                .count(),
            2,
            "theorem `verified` and `Certificate` must both carry the callee table:\n{linked}"
        );
        assert!(linked.contains("Anneal.Rustc.V2026_06_01.Lower.verifyTotalMirBounded _ 128"));
        assert!(linked.contains("wpCoalBounded_of_evalMirDiffExecBounded_normalScalar 128"));
        assert!(!linked.contains("sorry"));

        // A ratchet recorded before linking must evaluate with the callees
        // linked so that it fails once linking resolves the external call.
        let mut stale = pass.clone();
        stale.known_anneal_bug = Some(KnownAnnealBugSpec {
            status: "open_bug".to_string(),
            bug_class: "incompleteness_unmodeled_intrinsic_or_call".to_string(),
            observed_anneal_tag: MiriDiffVerdictSpec::ExternalCall(
                "miri_diff_corpus::helper_add_ten".to_string(),
            ),
            observed_anneal_ub_span: None,
            suspected_component: "Trusted.Rustc.V2026_06_01.MirSemantics.Memory".to_string(),
            summary: "Stale ratchet.".to_string(),
        });
        let (ratchet, ratchet_cert) =
            render_miri_diff_verify_module_with_callees("MiriDiffCorpus", def_id, &stale, &helpers)
                .expect("render stale ratchet");
        assert!(!ratchet_cert);
        assert!(ratchet.contains(
            "(initMachineStateWithMemoryAndCallees Mir.MiriDiffCorpus.pass_direct_fn_call.body [] \
             emptyMemory [Mir.MiriDiffCorpus.helper_add_ten.body]) =\n      \
             (MirDiffTag.externalCall \"miri_diff_corpus::helper_add_ten\")"
        ));

        // Self-recursive + PassUnit + Panic + Ub + span-ratchet callee-linked shapes.
        let self_and_helper = vec![
            "MiriDiffCorpus.pass_direct_fn_call".to_string(),
            "MiriDiffCorpus.helper_add_ten".to_string(),
        ];
        let pass_unit = entry("pass_direct_fn_call", MiriDiffVerdictSpec::PassUnit);
        let (linked_unit, linked_unit_cert) = render_miri_diff_verify_module_with_callees(
            "MiriDiffCorpus",
            def_id,
            &pass_unit,
            &self_and_helper,
        )
        .expect("render PassUnit with self + helper callees");
        assert!(linked_unit_cert);
        assert_eq!(
            linked_unit
                .matches("import Mir.MiriDiffCorpus.pass_direct_fn_call\n")
                .count(),
            1,
            "self-recursive callee must not duplicate the subject import:\n{linked_unit}"
        );
        assert!(linked_unit.contains("wpCoalBounded_of_evalMirDiffExecBounded_normalUnit 128"));

        let panic_entry = entry("panic_with_callee", MiriDiffVerdictSpec::Panic);
        let (linked_panic, linked_panic_cert) = render_miri_diff_verify_module_with_callees(
            "MiriDiffCorpus",
            "miri_diff_corpus::panic_with_callee",
            &panic_entry,
            &helpers,
        )
        .expect("render Panic with linked callees");
        assert!(linked_panic_cert);
        assert!(linked_panic.contains("Anneal.Rustc.V2026_06_01.Lower.verifyStatefulMirBounded _ 128"));
        assert!(linked_panic.contains("wpMirBounded_of_reachesPanicBounded 128"));
        assert!(linked_panic.contains("refuteTotalClaimByBoundedPanic _ 128 [] emptyMemory"));

        let mut ub_entry = entry("ub_with_callee", MiriDiffVerdictSpec::Ub);
        ub_entry.miri_ub_span = SourcePos::parse_rustc_pos("src/lib.rs:10:5");
        let (linked_ub, linked_ub_cert) = render_miri_diff_verify_module_with_callees(
            "MiriDiffCorpus",
            "miri_diff_corpus::ub_with_callee",
            &ub_entry,
            &helpers,
        )
        .expect("render Ub with linked callees");
        assert!(!linked_ub_cert);
        assert!(linked_ub.contains("refuteStatefulClaimByStrictUB _ 128 [] emptyMemory"));
        assert!(linked_ub.contains("refuteTotalClaimByStrictUB _ 128 [] emptyMemory"));
    }

    #[test]
    fn verify_module_rejects_unsafe_or_duplicate_callee_suffixes() {
        let pass = entry("pass_direct_fn_call", MiriDiffVerdictSpec::PassUnit);
        for bad in [
            vec!["MiriDiffCorpus.helper]".to_string()],
            vec!["".to_string()],
            vec!["helper".to_string()],
            vec!["MiriDiffCorpus.1helper".to_string()],
            vec!["MiriDiffCorpus.helperα".to_string()],
            vec!["MiriDiffCorpus..helper".to_string()],
            vec![
                "MiriDiffCorpus.helper_add_ten".to_string(),
                "MiriDiffCorpus.helper_add_ten".to_string(),
            ],
        ] {
            assert!(
                render_miri_diff_verify_module_with_callees(
                    "MiriDiffCorpus",
                    "miri_diff_corpus::pass_direct_fn_call",
                    &pass,
                    &bad
                )
                .is_err(),
                "callee table {bad:?} must be rejected"
            );
        }
    }

    #[test]
    fn modular_panic_certificate_states_only_trusted_constants() {
        let panic_entry = entry("panic_explicit_macro", MiriDiffVerdictSpec::Panic);
        let def_id = "miri_diff_corpus::panic_explicit_macro";
        let contract = "MirCallContract.holdsOn {\n        \
                        pre := fun _ => True\n        \
                        post := fun req ans =>\n          \
                          match ans with\n          \
                          | .returned _ memAfter => callFramePreserved req.memory memAfter\n          \
                          | .panicked memAfter => callFramePreserved req.memory memAfter\n          \
                          | .aborted => True\n      \
                        }";

        let (modular, modular_cert) = render_miri_diff_verify_module_with_panic_certificate(
            "MiriDiffCorpus",
            def_id,
            &panic_entry,
            &[],
            MiriDiffPanicCertificate::Modular,
        )
        .expect("render modular panic certificate");
        assert!(modular_cert, "a modular panic certificate is audited:\n{modular}");
        assert!(modular.contains("-- @anneal-miri-diff-kind: panic_modular\n"));
        assert!(modular.contains(&format!(
            "theorem verified :\n    \
             ModularVerificationResult {{\n      \
               body := Mir.MiriDiffCorpus.panic_explicit_macro.body\n      \
               envAssumed := {contract}\n"
        )));
        assert_eq!(
            modular
                .matches(
                    "(verifyModularSafePanicMirBounded \
                     Mir.MiriDiffCorpus.panic_explicit_macro.body [] 128 [] emptyMemory)"
                )
                .count(),
            2,
            "`verified` and `total_refuted` must both use the modular combinator:\n{modular}"
        );
        assert_eq!(modular.matches("match ans with").count(), 2);
        assert_eq!(modular.matches("post := fun _ _ _ _ => False").count(), 2);
        assert_eq!(modular.matches("} : TotalClaim).holds").count(), 2);
        assert!(modular.contains("And.intro verified total_refuted"));
        // Statements must not mention `Anneal.*` constants such as
        // `framePreservingCallContract`, and a callee-free module links nothing.
        assert!(!modular.contains("framePreservingCallContract"));
        assert!(!modular.contains("StatefulVerificationResult"));
        assert!(!modular.contains("callees :="));
        assert!(!modular.contains("sorry"));

        let helpers = vec!["MiriDiffCorpus.helper_add_ten".to_string()];
        let (linked, linked_cert) = render_miri_diff_verify_module_with_panic_certificate(
            "MiriDiffCorpus",
            def_id,
            &panic_entry,
            &helpers,
            MiriDiffPanicCertificate::Modular,
        )
        .expect("render callee-linked modular panic certificate");
        assert!(linked_cert);
        assert_eq!(
            linked
                .matches("callees := [Mir.MiriDiffCorpus.helper_add_ten.body]")
                .count(),
            4,
            "every claim must carry the callee table:\n{linked}"
        );
        assert!(linked.contains(
            "(verifyModularSafePanicMirBounded Mir.MiriDiffCorpus.panic_explicit_macro.body \
             [Mir.MiriDiffCorpus.helper_add_ten.body] 128 [] emptyMemory).1"
        ));

        // The default rendering keeps the stateful certificate, and the shape
        // does not affect other verdicts.
        let (stateful, _) =
            render_miri_diff_verify_module("MiriDiffCorpus", def_id, &panic_entry).expect("render");
        assert!(stateful.contains(
            "(verifySafePanicMirPointBounded Mir.MiriDiffCorpus.panic_explicit_macro.body \
             128 [] emptyMemory).1"
        ));
        assert!(!stateful.contains("ModularVerificationResult"));
        let pass = entry("pass_direct_fn_call", MiriDiffVerdictSpec::PassUnit);
        let pass_def_id = "miri_diff_corpus::pass_direct_fn_call";
        assert_eq!(
            render_miri_diff_verify_module_with_panic_certificate(
                "MiriDiffCorpus",
                pass_def_id,
                &pass,
                &[],
                MiriDiffPanicCertificate::Modular,
            )
            .expect("render pass"),
            render_miri_diff_verify_module("MiriDiffCorpus", pass_def_id, &pass)
                .expect("render pass")
        );
    }

    #[test]
    fn panic_ratchet_also_requires_modular_checker_to_reject() {
        let mut panic_bug = entry("panic_explicit_macro", MiriDiffVerdictSpec::Panic);
        panic_bug.known_anneal_bug = Some(KnownAnnealBugSpec {
            status: "open_bug".to_string(),
            bug_class: "incompleteness_unmodeled_intrinsic_or_call".to_string(),
            observed_anneal_tag: MiriDiffVerdictSpec::ExternalCall(
                "core::fmt::Arguments::<'a>::from_str".to_string(),
            ),
            observed_anneal_ub_span: None,
            suspected_component: "Trusted.Rustc.V2026_06_01.MirSemantics.Terminators".to_string(),
            summary: "Reintroduced ratchet.".to_string(),
        });
        for shape in [MiriDiffPanicCertificate::Stateful, MiriDiffPanicCertificate::Modular] {
            let (ratchet, ratchet_cert) = render_miri_diff_verify_module_with_panic_certificate(
                "MiriDiffCorpus",
                "miri_diff_corpus::panic_explicit_macro",
                &panic_bug,
                &[],
                shape,
            )
            .expect("render panic ratchet");
            assert!(!ratchet_cert);
            assert!(
                ratchet.contains(
                    "theorem known_anneal_bug_ratchet :\n    \
                     evalMirDiffTagBounded 128 Mir.MiriDiffCorpus.panic_explicit_macro.body\n      \
                       (initMachineStateWithMemory Mir.MiriDiffCorpus.panic_explicit_macro.body [] emptyMemory) =\n      \
                     (MirDiffTag.externalCall \"core::fmt::Arguments::<'a>::from_str\") ∧\n    \
                     reachesModularSafePanicBounded 128 Mir.MiriDiffCorpus.panic_explicit_macro.body\n      \
                       (initMachineStateWithMemory Mir.MiriDiffCorpus.panic_explicit_macro.body [] emptyMemory) =\n      \
                     false := by\n  \
                   exact ⟨rfl, rfl⟩\n"
                ),
                "unexpected panic ratchet:\n{ratchet}"
            );
            assert!(!ratchet.contains("theorem verified"));
        }

        // A ratchet for a non-`panic` verdict keeps the bare tag equality.
        let mut pass_bug = entry("pass_direct_fn_call", MiriDiffVerdictSpec::PassUnit);
        pass_bug.known_anneal_bug = panic_bug.known_anneal_bug.clone();
        let (pass_ratchet, _) = render_miri_diff_verify_module(
            "MiriDiffCorpus",
            "miri_diff_corpus::pass_direct_fn_call",
            &pass_bug,
        )
        .expect("render pass ratchet");
        assert!(!pass_ratchet.contains("reachesModularSafePanicBounded"));
        assert!(pass_ratchet.contains(
            "(MirDiffTag.externalCall \"core::fmt::Arguments::<'a>::from_str\") := by\n  rfl\n"
        ));
    }

    #[test]
    fn classify_panic_certificate_requires_modular_shape_for_unlinked_calls() {
        let root = std::env::temp_dir().join(format!(
            "cargo-anneal-classify-panic-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        let mir_dir = root.join("generated").join("Mir").join("MiriDiffCorpus");
        fs::create_dir_all(&mir_dir).expect("create MIR dir");
        let write_mir = |name: &str, refs: &[&str]| {
            let mut text = format!("namespace Mir.MiriDiffCorpus.{name}\n");
            for r in refs {
                text.push_str(&format!(
                    "-- call (RigidTy.fnDef \"{r}\" List.nil)\n"
                ));
            }
            fs::write(mir_dir.join(format!("{name}.lean")), text).expect("write MIR");
        };
        write_mir("panic_assert", &[]);
        write_mir(
            "panic_inline_trusted_calls",
            &[
                "core::intrinsics::exact_div",
                "core::intrinsics::wrapping_add",
                "core::panicking::panic_explicit",
                "core::panicking::panic_bounds_check",
                "core::option::unwrap_failed",
            ],
        );
        write_mir(
            "panic_fmt_macro",
            &["core::fmt::Arguments::<'a>::from_str", "core::panicking::panic_fmt"],
        );
        write_mir("panic_via_helper", &["miri_diff_corpus::helper"]);
        write_mir("helper", &["core::panicking::panic"]);
        write_mir("helper_calling_external", &["core::fmt::Arguments::<'a>::from_str"]);
        write_mir("panic_via_external_helper", &["miri_diff_corpus::helper_calling_external"]);
        let def_id_by_suffix: BTreeMap<String, String> = [
            "panic_assert",
            "panic_inline_trusted_calls",
            "panic_fmt_macro",
            "panic_via_helper",
            "helper",
            "helper_calling_external",
            "panic_via_external_helper",
        ]
        .into_iter()
        .map(|n| (format!("MiriDiffCorpus.{n}"), format!("miri_diff_corpus::{n}")))
        .collect();
        let classify = |item: &str, linked: &[&str]| {
            let linked: Vec<String> =
                linked.iter().map(|n| format!("MiriDiffCorpus.{n}")).collect();
            classify_panic_certificate(
                &root,
                &format!("MiriDiffCorpus.{item}"),
                &linked,
                &def_id_by_suffix,
            )
        };

        assert_eq!(classify("panic_assert", &[]), Ok(MiriDiffPanicCertificate::Stateful));
        // Inline-modeled `Trusted` panic entrypoints and intrinsics never emit
        // an external call, so they keep the stronger `Stateful` certificate.
        assert_eq!(
            classify("panic_inline_trusted_calls", &[]),
            Ok(MiriDiffPanicCertificate::Stateful)
        );
        assert_eq!(classify("panic_fmt_macro", &[]), Ok(MiriDiffPanicCertificate::Modular));
        // A linked callee (even one that calls an inline-modeled `Trusted`
        // panic entrypoint) is not an external call, but an external call
        // inside a linked callee is, and an unlinked captured function is too.
        assert_eq!(
            classify("panic_via_helper", &["helper"]),
            Ok(MiriDiffPanicCertificate::Stateful)
        );
        assert_eq!(classify("panic_via_helper", &[]), Ok(MiriDiffPanicCertificate::Modular));
        assert_eq!(
            classify("panic_via_external_helper", &["helper_calling_external"]),
            Ok(MiriDiffPanicCertificate::Modular)
        );
        // Missing MIR modules and unknown suffixes fail closed.
        assert!(classify("missing_item", &[]).is_err());
        let _ = fs::remove_dir_all(&root);
    }

    /// Collect the string literals compared by `stringEq` inside the body of
    /// each Lean definition `def <name> ` in `lean_src`, up to the next
    /// documentation comment.
    fn trusted_string_eq_literals(lean_src: &str, names: &[&str]) -> BTreeSet<String> {
        let mut literals = BTreeSet::new();
        for name in names {
            let start = lean_src
                .find(&format!("def {name} "))
                .unwrap_or_else(|| panic!("missing `def {name}` in Terminators.lean"));
            let body = &lean_src[start..];
            let body = &body[..body.find("\n/--").unwrap_or(body.len())];
            for line in body.lines() {
                let Some(pos) = line.find("stringEq ") else {
                    continue;
                };
                let after = &line[pos..];
                let Some(open) = after.find('"') else {
                    continue;
                };
                let literal = &after[open + 1..];
                let close = literal.find('"').expect("unterminated string literal");
                literals.insert(literal[..close].to_string());
            }
        }
        literals
    }

    #[test]
    fn trusted_inline_call_def_paths_match_trusted_terminators() {
        let terminators = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Terminators.lean");
        let lean_src = fs::read_to_string(&terminators).expect("read Trusted Terminators.lean");
        let mut trusted = trusted_string_eq_literals(
            &lean_src,
            &[
                "isUnwindingPanicDefPath",
                "isAbortingPanicDefPath",
                "isUnreachableCallTarget",
                "isDirectExactDivTarget",
                "classifyRustIntrinsic?",
            ],
        );
        // `const_eval_select` dispatches to a runtime target that may itself be
        // an external call, so it is deliberately not treated as inline.
        assert!(trusted.remove("core::intrinsics::const_eval_select"));
        let listed: BTreeSet<String> = TRUSTED_INLINE_CALL_DEF_PATHS
            .iter()
            .map(|s| s.to_string())
            .collect();
        assert_eq!(
            listed.len(),
            TRUSTED_INLINE_CALL_DEF_PATHS.len(),
            "TRUSTED_INLINE_CALL_DEF_PATHS has duplicates"
        );
        assert_eq!(
            listed, trusted,
            "TRUSTED_INLINE_CALL_DEF_PATHS must match the inline call targets of Terminators.lean"
        );
        assert!(!is_trusted_inline_call_def_path("core::intrinsics::const_eval_select"));
        assert!(!is_trusted_inline_call_def_path("core::fmt::Arguments::<'a>::from_str"));
    }
}
