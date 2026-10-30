//! Differential testing harness comparing upstream Miri verdicts against
//! Anneal's MIR-in-Lean operational semantics (`Trusted.Rustc.V2026_06_01.MirSemantics`).
//!
//! Reads a hermetic differential test manifest (`tests/miri-diff/manifest.toml`),
//! captures MIR from the corpus crate (`tests/miri-diff/corpus`) using the
//! Miri-matching compiler flags recorded in the manifest, generates Lean 4
//! proof and refutation obligations for every test entry, compiles them with
//! Lake, and runs `trusted/audit/TrustedBoundary.lean` in `verify-audit` mode.
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
//!      `verifyTotalMirScalarPointBounded` (`TotalVerificationResult`).
//!    - `panic`: proved via `verifySafePanicMirPointBounded`
//!      (`StatefulVerificationResult` with `post := False` and `¬ TotalClaim.holds`).
//!    - `ub`: refuted via `refuteMirPointByStrictUB`
//!      (`¬ StatefulClaim.holds ∧ ¬ TotalClaim.holds` from
//!      `reachesStrictUBBounded = true`, which rejects `FailureKind.unsupported`).
//! 2. Every test with `known_anneal_bug` must match its exact recorded
//!    `observed_anneal_tag` via `evalMirDiffTagBounded ... = ... := by rfl`.
//!    As soon as an Anneal bug is fixed so that Anneal agrees with Miri, the
//!    `known_anneal_bug_ratchet` theorem fails to type-check until the entry
//!    is removed from `manifest.toml`.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use anneal_rustc_capture::{ANNEAL_CAPTURE_DIR_ENV, CapturedItemKind, UnitTargetRecord};

use crate::driver::{
    ANNEAL_CAPTURE_FILTER_ENV, CaptureDriverConfig, aggregate_unit_manifests, resolve_rustc_wrapper,
};
use crate::obligations::{derive_item_module_suffix, module_suffix_to_rel_path};
use crate::scaffold::{ScaffoldConfig, scaffold_workspace_with_config};
use crate::{normalize_path_against, run_lake_verify, run_trusted_boundary_verify_audit};

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
    /// or `incompleteness_unmodeled_intrinsic_or_call`).
    pub bug_class: String,
    /// Current `MirDiffTag` produced by Anneal on this test.
    pub observed_anneal_tag: MiriDiffVerdictSpec,
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
    /// Number of `panic` tests verified via `verifySafePanicMirPointBounded`.
    pub verified_panic_count: usize,
    /// Number of `ub` tests refuted via `refuteMirPointByStrictUB`.
    pub verified_strict_ub_count: usize,
    /// Number of open Anneal bugs ratcheted via `known_anneal_bug_ratchet`.
    pub ratcheted_known_bug_count: usize,
    /// `Verify.<Crate>.<Item>` certificate modules audited by `TrustedBoundary`.
    pub audited_certificate_modules: Vec<String>,
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
            if observed_anneal_tag == miri_verdict {
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
            current_bug.clear();
            *has_bug_section = false;
            Some(KnownAnnealBugSpec {
                status,
                bug_class,
                observed_anneal_tag,
                suspected_component,
                summary,
            })
        } else {
            None
        };

        current_test.clear();
        tests.push(MiriDiffTestEntry {
            name,
            category,
            upstream_path,
            miri_verdict,
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

/// Render the `.anneal/generated/Verify/<Crate>/<test.name>.lean` module for a
/// single differential test entry.
///
/// Returns `(module_source, is_trusted_certificate_module)` where
/// `is_trusted_certificate_module` is `true` for non-bug `pass` and `panic`
/// entries whose `theorem verified` has head type `TotalVerificationResult` or
/// `StatefulVerificationResult`.
pub fn render_miri_diff_verify_module(
    crate_camel: &str,
    def_id: &str,
    entry: &MiriDiffTestEntry,
) -> Result<(String, bool), String> {
    let item = format!("{crate_camel}.{}", entry.name);
    let fuel = entry.fuel;
    let mut out = String::new();
    out.push_str(&format!(
        "-- @anneal-def-id: {def_id}\n\
         import Mir.{item}\n\
         import Anneal.Rustc.V2026_06_01.SymbolicEval\n\n\
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
        out.push_str(&format!(
            "-- @anneal-miri-diff-kind: known_anneal_bug\n\
             -- UNFIXED ANNEAL BUG ({} in `{}`):\n\
             -- {}\n\
             -- Reference Miri verdict: `{}`\n\
             -- Observed Anneal tag:    `{}`\n\
             theorem known_anneal_bug_ratchet :\n    \
                 evalMirDiffTagBounded {fuel} Mir.{item}.body\n      \
                   (initMachineStateWithMemory Mir.{item}.body [] emptyMemory) =\n      \
                 {tag_expr} := by\n  \
               rfl\n\n\
             end Verify.{item}\n",
            bug.bug_class,
            bug.suspected_component,
            bug.summary,
            entry.miri_verdict.as_tag_str(),
            bug.observed_anneal_tag.as_tag_str()
        ));
        return Ok((out, false));
    }

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
            Ok((out, true))
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
            Ok((out, true))
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
            Ok((out, true))
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
            Ok((out, false))
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
/// transitive constant closure and kernel replay audit all 74 tests.
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

    let mut verified_pass_count = 0usize;
    let mut verified_panic_count = 0usize;
    let mut verified_strict_ub_count = 0usize;
    let mut ratcheted_known_bug_count = 0usize;

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
        let (content, is_cert) =
            render_miri_diff_verify_module(&crate_camel, &rec.target.def_id, entry)?;
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
    };
    Ok((report, certificate_modules))
}

/// Run the full Miri differential test suite: load `manifest.toml`, capture MIR
/// from the corpus crate, generate Lean proof/refutation/ratchet modules,
/// compile them with Lake, and run `TrustedBoundary.lean` in `verify-audit`
/// mode.
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

    Ok(report)
}

/// Render a deterministic human-readable summary of a completed Miri
/// differential test run.
pub fn render_miri_diff_report(report: &MiriDiffReport) -> String {
    format!(
        "Anneal <-> Miri Differential Testing Summary:\n\
         \x20 Total corpus tests:              {}\n\
         \x20 Verified `pass` (TotalClaim):    {}\n\
         \x20 Verified `panic` (SafePanic):    {}\n\
         \x20 Refuted `ub` (StrictUB):         {}\n\
         \x20 Open Anneal bugs (ratcheted):    {}\n\
         \x20 TrustedBoundary kernel replay:   PASS\n",
        report.total_tests,
        report.verified_pass_count,
        report.verified_panic_count,
        report.verified_strict_ub_count,
        report.ratcheted_known_bug_count
    )
}
