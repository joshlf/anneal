//! Parser, validator, deterministic Lean 4 gap-ratchet code generator, and pure
//! Markdown issue payload renderer for `correspondence_gaps.toml` and
//! `correspondence_matrix.toml`.
//!
//! Strictly pure in-memory string/AST generation — zero network or subprocess calls.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use crate::lean_emit::lean_string_literal;
use crate::sha256::sha256_hex;

/// Four mutually exclusive formal classes for non-correspondences between Anneal
/// and upstream MiniRust.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum GapKind {
    /// Anneal accepts or mis-steps where MiniRust raises UB or computes a different value.
    AnnealSoundnessBug,
    /// Anneal conservatively raises `.fail .ub` where MiniRust steps to a valid state.
    AnnealFalsePositiveUb,
    /// Anneal emits `.fail .unsupported` where MiniRust defines inline execution.
    AnnealUnmodeledFeature,
    /// Intentional upstream MiniRust vs. pinned `rustc` epoch version skew.
    IntentionalEpochDivergence,
}

impl GapKind {
    /// Parses the canonical TOML string representation of `GapKind`.
    pub fn parse(raw: &str) -> Result<Self, String> {
        match raw.trim() {
            "anneal_soundness_bug" => Ok(Self::AnnealSoundnessBug),
            "anneal_false_positive_ub" => Ok(Self::AnnealFalsePositiveUb),
            "anneal_unmodeled_feature" => Ok(Self::AnnealUnmodeledFeature),
            "intentional_epoch_divergence" => Ok(Self::IntentionalEpochDivergence),
            other => Err(format!("unknown gap kind `{other}`")),
        }
    }

    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::AnnealSoundnessBug => "anneal_soundness_bug",
            Self::AnnealFalsePositiveUb => "anneal_false_positive_ub",
            Self::AnnealUnmodeledFeature => "anneal_unmodeled_feature",
            Self::IntentionalEpochDivergence => "intentional_epoch_divergence",
        }
    }

    #[must_use]
    pub const fn lean_ctor(self) -> &'static str {
        match self {
            Self::AnnealSoundnessBug => "GapKind.anneal_soundness_bug",
            Self::AnnealFalsePositiveUb => "GapKind.anneal_false_positive_ub",
            Self::AnnealUnmodeledFeature => "GapKind.anneal_unmodeled_feature",
            Self::IntentionalEpochDivergence => "GapKind.intentional_epoch_divergence",
        }
    }

    /// Whether this gap counts against the active non-epoch ratchet (`activeBugGaps` in
    /// `theory/Correspondence/Framework.lean`, where all three non-epoch gap kinds count
    /// against `max_open_bugs`).
    #[must_use]
    pub const fn is_bug_gap(self) -> bool {
        matches!(
            self,
            Self::AnnealSoundnessBug
                | Self::AnnealFalsePositiveUb
                | Self::AnnealUnmodeledFeature
        )
    }

    /// Whether this gap represents intentional cross-epoch version skew.
    #[must_use]
    pub const fn is_epoch_divergence(self) -> bool {
        matches!(self, Self::IntentionalEpochDivergence)
    }
}

/// Formal expected correspondence tier for a `(AnnealVersion, MiniRustSnapshot, Layer)` cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExpectedTier {
    ExactUnconditional,
    EpochDeltaOnly,
    GuardedRatchet,
}

impl ExpectedTier {
    pub fn parse(raw: &str) -> Result<Self, String> {
        match raw.trim() {
            "ExactUnconditional" => Ok(Self::ExactUnconditional),
            "EpochDeltaOnly" => Ok(Self::EpochDeltaOnly),
            "GuardedRatchet" => Ok(Self::GuardedRatchet),
            other => Err(format!("unknown ExpectedTier `{other}`")),
        }
    }

    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ExactUnconditional => "ExactUnconditional",
            Self::EpochDeltaOnly => "EpochDeltaOnly",
            Self::GuardedRatchet => "GuardedRatchet",
        }
    }
}

/// Single entry in `correspondence_gaps.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GapEntry {
    pub id: String,
    pub kind: GapKind,
    pub severity: String,
    pub status: String,
    pub title: String,
    pub anneal_versions: Vec<String>,
    pub minirust_snapshots: Vec<String>,
    pub layer: String,
    pub anneal_decl: String,
    pub anneal_file: String,
    pub minirust_source: String,
    pub miri_diff_cross_ref: Option<String>,
    pub rationale_citation: Option<String>,
    pub target_anneal_version: Option<String>,
    pub github_issue_number: Option<u64>,
    pub github_issue_url: Option<String>,
    pub guard_predicate: String,
    pub witness_fixture: String,
    pub expected_anneal_verdict: String,
    pub expected_minirust_verdict: String,
}

impl GapEntry {
    /// Deterministic deduplication fingerprint over `(anneal_decl, minirust_source, guard_predicate)`.
    #[must_use]
    pub fn fingerprint(&self) -> String {
        let payload = format!(
            "{}|{}|{}",
            self.anneal_decl.trim(),
            self.minirust_source.trim(),
            self.guard_predicate.trim()
        );
        sha256_hex(payload.as_bytes())
    }

    /// Converts gap ID (e.g. `GAP-MR-0001`) into a valid Lean constructor identifier (`GAP_MR_0001`).
    #[must_use]
    pub fn lean_ctor_ident(&self) -> String {
        self.id
            .chars()
            .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
            .collect()
    }
}

/// Parsed representation of `correspondence_gaps.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GapRegistry {
    pub schema_version: u32,
    pub github_repo: String,
    pub default_labels: Vec<String>,
    pub gaps: Vec<GapEntry>,
}

/// Single cell entry in `correspondence_matrix.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixCell {
    pub anneal_version: String,
    pub minirust_snapshot: String,
    pub layer: String,
    pub expected_tier: ExpectedTier,
    pub max_open_bugs: usize,
    pub allowed_epoch_gaps: Vec<String>,
}

/// Parsed representation of `correspondence_matrix.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CorrespondenceMatrix {
    pub schema_version: u32,
    pub cells: Vec<MatrixCell>,
}

/// Pure, in-memory rendered GitHub issue payload (zero network or subprocess calls).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RenderedIssuePayload {
    pub gap_id: String,
    pub repo: String,
    pub title: String,
    pub labels: Vec<String>,
    pub fingerprint: String,
    pub markdown_body: String,
}

/// Summary of validating `correspondence_gaps.toml` against `correspondence_matrix.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidationSummary {
    pub total_gaps: usize,
    pub soundness_bug_count: usize,
    pub false_positive_ub_count: usize,
    pub unmodeled_feature_count: usize,
    pub epoch_divergence_count: usize,
    pub validated_cells: usize,
}

/// Parses `correspondence_gaps.toml` into a typed `GapRegistry`.
pub fn parse_gaps_toml(content: &str) -> Result<GapRegistry, String> {
    let mut schema_version = 1u32;
    let mut github_repo = "joshlf/anneal".to_string();
    let mut default_labels = Vec::new();
    let mut gaps: Vec<GapEntry> = Vec::new();
    let mut in_gap = false;

    for (line_idx, raw_line) in content.lines().enumerate() {
        let line = strip_toml_inline_comment(raw_line).trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line == "[[gaps]]" {
            gaps.push(GapEntry {
                id: String::new(),
                kind: GapKind::AnnealSoundnessBug,
                severity: String::new(),
                status: String::new(),
                title: String::new(),
                anneal_versions: Vec::new(),
                minirust_snapshots: Vec::new(),
                layer: String::new(),
                anneal_decl: String::new(),
                anneal_file: String::new(),
                minirust_source: String::new(),
                miri_diff_cross_ref: None,
                rationale_citation: None,
                target_anneal_version: None,
                github_issue_number: None,
                github_issue_url: None,
                guard_predicate: String::new(),
                witness_fixture: String::new(),
                expected_anneal_verdict: String::new(),
                expected_minirust_verdict: String::new(),
            });
            in_gap = true;
            continue;
        }
        if line.starts_with('[') {
            in_gap = false;
            continue;
        }

        let Some((k, v)) = line.split_once('=') else {
            return Err(format!("line {}: invalid TOML assignment `{line}`", line_idx + 1));
        };
        let key = k.trim();
        let val_raw = v.trim();

        if !in_gap {
            match key {
                "schema_version" => {
                    schema_version = parse_scalar(val_raw)
                        .parse::<u32>()
                        .map_err(|e| format!("invalid schema_version: {e}"))?;
                }
                "github_repo" => github_repo = parse_scalar(val_raw),
                "default_labels" => default_labels = parse_string_array(val_raw),
                _ => {}
            }
            continue;
        }

        let g = gaps.last_mut().expect("gap entry active");
        match key {
            "id" => g.id = parse_scalar(val_raw),
            "kind" => g.kind = GapKind::parse(&parse_scalar(val_raw))?,
            "severity" => g.severity = parse_scalar(val_raw),
            "status" => g.status = parse_scalar(val_raw),
            "title" => g.title = parse_scalar(val_raw),
            "anneal_versions" => g.anneal_versions = parse_string_array(val_raw),
            "minirust_snapshots" => g.minirust_snapshots = parse_string_array(val_raw),
            "layer" => g.layer = parse_scalar(val_raw),
            "anneal_decl" => g.anneal_decl = parse_scalar(val_raw),
            "anneal_file" => g.anneal_file = parse_scalar(val_raw),
            "minirust_source" => g.minirust_source = parse_scalar(val_raw),
            "miri_diff_cross_ref" => {
                let s = parse_scalar(val_raw);
                if !s.is_empty() {
                    g.miri_diff_cross_ref = Some(s);
                }
            }
            "rationale_citation" => {
                let s = parse_scalar(val_raw);
                if !s.is_empty() {
                    g.rationale_citation = Some(s);
                }
            }
            "target_anneal_version" => {
                let s = parse_scalar(val_raw);
                if !s.is_empty() {
                    g.target_anneal_version = Some(s);
                }
            }
            "github_issue_number" => {
                if let Ok(n) = parse_scalar(val_raw).parse::<u64>() {
                    g.github_issue_number = Some(n);
                }
            }
            "github_issue_url" => {
                let s = parse_scalar(val_raw);
                if !s.is_empty() {
                    g.github_issue_url = Some(s);
                }
            }
            "guard_predicate" => g.guard_predicate = parse_scalar(val_raw),
            "witness_fixture" => g.witness_fixture = parse_scalar(val_raw),
            "expected_anneal_verdict" => g.expected_anneal_verdict = parse_scalar(val_raw),
            "expected_minirust_verdict" => g.expected_minirust_verdict = parse_scalar(val_raw),
            _ => {}
        }
    }

    Ok(GapRegistry { schema_version, github_repo, default_labels, gaps })
}

/// Parses `correspondence_matrix.toml` into a typed `CorrespondenceMatrix`.
pub fn parse_matrix_toml(content: &str) -> Result<CorrespondenceMatrix, String> {
    let mut schema_version = 1u32;
    let mut cells: Vec<MatrixCell> = Vec::new();
    let mut in_cell = false;

    for (line_idx, raw_line) in content.lines().enumerate() {
        let line = strip_toml_inline_comment(raw_line).trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line == "[[cells]]" || line == "[[matrix]]" || line == "[[profiles]]" {
            cells.push(MatrixCell {
                anneal_version: String::new(),
                minirust_snapshot: String::new(),
                layer: String::new(),
                expected_tier: ExpectedTier::GuardedRatchet,
                max_open_bugs: 0,
                allowed_epoch_gaps: Vec::new(),
            });
            in_cell = true;
            continue;
        }
        if line.starts_with('[') {
            in_cell = false;
            continue;
        }

        let Some((k, v)) = line.split_once('=') else {
            return Err(format!("line {}: invalid matrix TOML line `{line}`", line_idx + 1));
        };
        let key = k.trim();
        let val_raw = v.trim();

        if !in_cell {
            if key == "schema_version" {
                schema_version = parse_scalar(val_raw)
                    .parse::<u32>()
                    .map_err(|e| format!("invalid schema_version: {e}"))?;
            }
            continue;
        }

        let cell = cells.last_mut().expect("matrix cell active");
        match key {
            "anneal_version" => cell.anneal_version = parse_scalar(val_raw),
            "minirust_snapshot" => cell.minirust_snapshot = parse_scalar(val_raw),
            "layer" => cell.layer = parse_scalar(val_raw),
            "expected_tier" => cell.expected_tier = ExpectedTier::parse(&parse_scalar(val_raw))?,
            "max_open_bugs" => {
                cell.max_open_bugs = parse_scalar(val_raw)
                    .parse::<usize>()
                    .map_err(|e| format!("invalid max_open_bugs: {e}"))?;
            }
            "allowed_epoch_gaps" => cell.allowed_epoch_gaps = parse_string_array(val_raw),
            _ => {}
        }
    }

    Ok(CorrespondenceMatrix { schema_version, cells })
}

/// Parses a `minirust_source` span string of the form `<rel_path>:<start>-<end>`
/// (or `<rel_path>:<line>`) and validates `1 <= start <= end`.
pub fn parse_minirust_source_span(raw: &str) -> Result<(String, usize, usize), String> {
    let trimmed = raw.trim();
    let Some((path_part, range_part)) = trimmed.rsplit_once(':') else {
        return Err(format!(
            "invalid minirust_source `{trimmed}` (expected `<path>:<start>-<end>`)"
        ));
    };
    let rel_path = path_part.trim();
    if rel_path.is_empty() || !rel_path.ends_with(".md") {
        return Err(format!(
            "invalid minirust_source path `{rel_path}` (expected `.md` specification file)"
        ));
    }
    let (start_str, end_str) = range_part
        .trim()
        .split_once('-')
        .unwrap_or((range_part.trim(), range_part.trim()));
    let start = start_str
        .trim()
        .parse::<usize>()
        .map_err(|e| format!("invalid start line `{start_str}` in `{trimmed}`: {e}"))?;
    let end = end_str
        .trim()
        .parse::<usize>()
        .map_err(|e| format!("invalid end line `{end_str}` in `{trimmed}`: {e}"))?;
    if start == 0 || end < start {
        return Err(format!(
            "invalid line range {start}-{end} in `{trimmed}` (require 1 <= start <= end)"
        ));
    }
    Ok((rel_path.to_string(), start, end))
}

/// Validates a `GapRegistry` and `CorrespondenceMatrix` against all formal ratchet invariants.
pub fn validate_registry_and_matrix(
    registry: &GapRegistry,
    matrix: &CorrespondenceMatrix,
) -> Result<ValidationSummary, Vec<String>> {
    validate_registry_and_matrix_inner(registry, matrix, None)
}

/// Validates a `GapRegistry` and `CorrespondenceMatrix`, additionally verifying that
/// every `anneal_file` and every `minirust_source` (`<path>:<start>-<end>`) resolves to an
/// existing file under `repo_root` with `1 <= start <= end <= total_lines`.
pub fn validate_registry_and_matrix_with_repo_root(
    registry: &GapRegistry,
    matrix: &CorrespondenceMatrix,
    repo_root: &Path,
) -> Result<ValidationSummary, Vec<String>> {
    validate_registry_and_matrix_inner(registry, matrix, Some(repo_root))
}

fn validate_registry_and_matrix_inner(
    registry: &GapRegistry,
    matrix: &CorrespondenceMatrix,
    repo_root: Option<&Path>,
) -> Result<ValidationSummary, Vec<String>> {
    let mut errors = Vec::new();
    let mut seen_ids = BTreeSet::new();

    let mut soundness_bug_count = 0usize;
    let mut false_positive_ub_count = 0usize;
    let mut unmodeled_feature_count = 0usize;
    let mut epoch_divergence_count = 0usize;

    for g in &registry.gaps {
        if g.id.trim().is_empty() {
            errors.push("gap entry has empty `id`".to_string());
        } else if !seen_ids.insert(g.id.clone()) {
            errors.push(format!("duplicate gap id `{}`", g.id));
        }

        match g.kind {
            GapKind::AnnealSoundnessBug => soundness_bug_count += 1,
            GapKind::AnnealFalsePositiveUb => false_positive_ub_count += 1,
            GapKind::AnnealUnmodeledFeature => unmodeled_feature_count += 1,
            GapKind::IntentionalEpochDivergence => epoch_divergence_count += 1,
        }

        let gp = g.guard_predicate.trim();
        if gp.is_empty()
            || gp.eq_ignore_ascii_case("true")
            || gp == "1 = 1"
            || gp == "fun _ => true"
        {
            errors.push(format!(
                "gap `{}` has vacuous or empty guard_predicate `{gp}`",
                g.id
            ));
        }

        if g.witness_fixture.trim().is_empty() {
            errors.push(format!("gap `{}` is missing mandatory `witness_fixture`", g.id));
        }

        if g.kind == GapKind::IntentionalEpochDivergence
            && g.rationale_citation.as_deref().is_none_or(|s| s.trim().is_empty())
        {
            errors.push(format!(
                "gap `{}` has kind `intentional_epoch_divergence` without mandatory `rationale_citation`",
                g.id
            ));
        }

        match parse_minirust_source_span(&g.minirust_source) {
            Err(span_err) => {
                errors.push(format!("gap `{}`: {span_err}", g.id));
            }
            Ok((rel_md_path, start_line, end_line)) => {
                if let Some(root) = repo_root {
                    let anneal_abs = root.join(g.anneal_file.trim());
                    if g.anneal_file.trim().is_empty() || !anneal_abs.is_file() {
                        errors.push(format!(
                            "gap `{}` references missing anneal_file `{}`",
                            g.id, g.anneal_file
                        ));
                    }
                    for snap in &g.minirust_snapshots {
                        let md_abs = root
                            .join("theory/MiniRust/vendor")
                            .join(snap)
                            .join(&rel_md_path);
                        match fs::read_to_string(&md_abs) {
                            Err(_) => errors.push(format!(
                                "gap `{}` references missing vendored MiniRust file `{}` in snapshot `{}`",
                                g.id, rel_md_path, snap
                            )),
                            Ok(md_text) => {
                                let total_lines = md_text.lines().count();
                                if start_line == 0 || start_line > end_line || end_line > total_lines {
                                    errors.push(format!(
                                        "gap `{}` minirust_source `{}` range {}-{} exceeds total_lines {} in snapshot `{}`",
                                        g.id, g.minirust_source, start_line, end_line, total_lines, snap
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    for cell in &matrix.cells {
        let matching_all: Vec<&GapEntry> = registry
            .gaps
            .iter()
            .filter(|g| {
                g.anneal_versions.iter().any(|v| v == &cell.anneal_version)
                    && g.minirust_snapshots.iter().any(|s| s == &cell.minirust_snapshot)
                    && (cell.layer == "*" || g.layer == cell.layer)
            })
            .collect();

        let matching_bugs: Vec<&GapEntry> = matching_all
            .iter()
            .copied()
            .filter(|g| g.kind.is_bug_gap())
            .collect();

        let matching_epoch: Vec<&GapEntry> = matching_all
            .iter()
            .copied()
            .filter(|g| g.kind.is_epoch_divergence())
            .collect();

        match cell.expected_tier {
            ExpectedTier::ExactUnconditional => {
                if !matching_all.is_empty() {
                    errors.push(format!(
                        "cell ({}, {}, {}) requires ExactUnconditional (0 gaps of any kind) but has {} active gaps ({} bug/unmodeled, {} epoch)",
                        cell.anneal_version,
                        cell.minirust_snapshot,
                        cell.layer,
                        matching_all.len(),
                        matching_bugs.len(),
                        matching_epoch.len()
                    ));
                }
            }
            ExpectedTier::EpochDeltaOnly => {
                if !matching_bugs.is_empty() {
                    errors.push(format!(
                        "cell ({}, {}, {}) requires EpochDeltaOnly (0 bugs) but has {} bug gaps",
                        cell.anneal_version,
                        cell.minirust_snapshot,
                        cell.layer,
                        matching_bugs.len()
                    ));
                }
            }
            ExpectedTier::GuardedRatchet => {
                if matching_bugs.len() > cell.max_open_bugs {
                    errors.push(format!(
                        "ratchet ceiling exceeded for ({}, {}, {}): active_bugs={} > max_open_bugs={}",
                        cell.anneal_version,
                        cell.minirust_snapshot,
                        cell.layer,
                        matching_bugs.len(),
                        cell.max_open_bugs
                    ));
                }
            }
        }
    }

    if errors.is_empty() {
        Ok(ValidationSummary {
            total_gaps: registry.gaps.len(),
            soundness_bug_count,
            false_positive_ub_count,
            unmodeled_feature_count,
            epoch_divergence_count,
            validated_cells: matrix.cells.len(),
        })
    } else {
        Err(errors)
    }
}

/// Deterministically emits self-contained Lean 4 source code for a `GapRegistry` + `CorrespondenceMatrix`.
/// Pure function with zero I/O or network calls, zero `sorry`, zero `native_decide`.
#[must_use]
pub fn emit_generated_gaps_lean(registry: &GapRegistry, matrix: &CorrespondenceMatrix) -> String {
    let mut s = String::with_capacity(8192);
    s.push_str("-- Mechanically generated by `crates/anneal-specr-lean/src/gap_codegen.rs`.\n");
    s.push_str("-- Pure Lean 4 kernel definitions; zero automatic issue filing side effects.\n\n");
    s.push_str("namespace Correspondence\n\n");

    s.push_str("inductive GapKind where\n");
    s.push_str("  | anneal_soundness_bug\n");
    s.push_str("  | anneal_false_positive_ub\n");
    s.push_str("  | anneal_unmodeled_feature\n");
    s.push_str("  | intentional_epoch_divergence\n");
    s.push_str("  deriving DecidableEq, Repr\n\n");

    s.push_str("inductive GapId where\n");
    if registry.gaps.is_empty() {
        s.push_str("  | noneRegistered\n");
    } else {
        for g in &registry.gaps {
            s.push_str(&format!("  | {}\n", g.lean_ctor_ident()));
        }
    }
    s.push_str("  deriving DecidableEq, Repr\n\n");

    s.push_str("structure GapRecord where\n");
    s.push_str("  id : GapId\n");
    s.push_str("  rawId : String\n");
    s.push_str("  kind : GapKind\n");
    s.push_str("  layer : String\n");
    s.push_str("  annealDecl : String\n");
    s.push_str("  minirustSource : String\n");
    s.push_str("  guardPredicate : String\n");
    s.push_str("  witnessFixture : String\n");
    s.push_str("  deriving DecidableEq, Repr\n\n");

    s.push_str("def registeredGaps : List GapRecord := [\n");
    for (idx, g) in registry.gaps.iter().enumerate() {
        let comma = if idx + 1 < registry.gaps.len() { "," } else { "" };
        s.push_str(&format!(
            "  {{ id := GapId.{}, rawId := {}, kind := {}, layer := {}, annealDecl := {}, minirustSource := {}, guardPredicate := {}, witnessFixture := {} }}{}\n",
            g.lean_ctor_ident(),
            lean_string_literal(&g.id),
            g.kind.lean_ctor(),
            lean_string_literal(&g.layer),
            lean_string_literal(&g.anneal_decl),
            lean_string_literal(&g.minirust_source),
            lean_string_literal(&g.guard_predicate),
            lean_string_literal(&g.witness_fixture),
            comma
        ));
    }
    s.push_str("]\n\n");

    s.push_str(&format!("def totalGapCount : Nat := {}\n", registry.gaps.len()));
    s.push_str(&format!("def matrixCellCount : Nat := {}\n\n", matrix.cells.len()));

    s.push_str("theorem registered_gap_count_exact : registeredGaps.length = totalGapCount := rfl\n\n");
    s.push_str("end Correspondence\n");
    s
}

/// Renders a complete, publication-ready GitHub issue payload in memory without
/// executing any network request or external command.
#[must_use]
pub fn render_github_issue_markdown(gap: &GapEntry, repo: &str) -> RenderedIssuePayload {
    let mut labels = vec![
        "source:minirust-correspondence".to_string(),
        "area:mir-semantics".to_string(),
        format!("kind:{}", gap.kind.as_str()),
    ];
    if !gap.severity.is_empty() && gap.severity != "none" {
        labels.push(format!("priority:{}", gap.severity));
    }

    let fingerprint = gap.fingerprint();
    let issue_title = format!("[MiniRust Correspondence][{}] {}", gap.id, gap.title);

    let mut body = String::with_capacity(2048);
    body.push_str(&format!("## Formal Non-Correspondence Report: `{}`\n\n", gap.id));
    body.push_str(&format!("- **Classification**: `{}`\n", gap.kind.as_str()));
    body.push_str(&format!("- **Severity**: `{}`\n", gap.severity));
    body.push_str(&format!("- **Semantic Layer**: `{}`\n", gap.layer));
    body.push_str(&format!("- **Anneal Versions Affected**: `{}`\n", gap.anneal_versions.join(", ")));
    body.push_str(&format!(
        "- **MiniRust Snapshots Affected**: `{}`\n",
        gap.minirust_snapshots.join(", ")
    ));
    body.push_str(&format!(
        "- **Pinpointed Anneal Declaration**: `{}` (`{}`)\n",
        gap.anneal_decl, gap.anneal_file
    ));
    body.push_str(&format!(
        "- **Upstream MiniRust `@specr-source`**: `{}`\n",
        gap.minirust_source
    ));
    if let Some(ref miri_ref) = gap.miri_diff_cross_ref {
        body.push_str(&format!("- **Miri-Diff Cross-Reference**: `{miri_ref}`\n"));
    }
    body.push_str(&format!("- **Deduplication Fingerprint**: `{fingerprint}`\n\n"));

    body.push_str("### Two-Way Kernel Ratchet Witness\n\n");
    body.push_str(&format!("- **Guard Predicate**: `{}`\n", gap.guard_predicate));
    body.push_str(&format!("- **Counterexample Fixture**: `{}`\n", gap.witness_fixture));
    body.push_str(&format!(
        "- **Observed Verdict Divergence**: Anneal = `{}` vs. MiniRust = `{}`\n",
        gap.expected_anneal_verdict, gap.expected_minirust_verdict
    ));
    body.push_str(
        "\n> Note: This payload was generated purely offline by `anneal-specr-lean`. \
         Fixing the underlying semantics in `trusted/lean/` will automatically break the \
         kernel `by decide` witness theorem until this gap entry is retired.\n",
    );

    RenderedIssuePayload {
        gap_id: gap.id.clone(),
        repo: repo.to_string(),
        title: issue_title,
        labels,
        fingerprint,
        markdown_body: body,
    }
}

fn strip_toml_inline_comment(line: &str) -> &str {
    let mut in_str = false;
    let bytes = line.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() {
        if in_str {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_str = false;
            }
            i += 1;
            continue;
        }
        if bytes[i] == b'"' {
            in_str = true;
        } else if bytes[i] == b'#' {
            return &line[..i];
        }
        i += 1;
    }
    line
}

fn parse_scalar(raw: &str) -> String {
    let t = raw.trim();
    if let Some(inner) = t.strip_prefix('"').and_then(|s| s.strip_suffix('"')) {
        inner.replace("\\\"", "\"").replace("\\\\", "\\")
    } else {
        t.to_string()
    }
}

fn parse_string_array(raw: &str) -> Vec<String> {
    let t = raw.trim();
    let Some(inner) = t.strip_prefix('[').and_then(|s| s.strip_suffix(']')) else {
        return Vec::new();
    };
    inner
        .split(',')
        .map(parse_scalar)
        .filter(|s| !s.is_empty())
        .collect()
}
