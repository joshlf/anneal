//! Standalone opt-in non-correspondence registry linter, ratchet verifier, and
//! manual GitHub issue formatter/filer (`cargo anneal correspondence-bugs`).
//!
//! # Zero Automatic Bug Filing Invariant
//!
//! By strict project policy, **nothing** in `cargo test`, `lake build`,
//! `cargo anneal minirust-sync`, `cargo anneal correspondence-bugs lint`, or
//! `cargo anneal correspondence-bugs format-issue` ever spawns `gh` or performs
//! any network request. Even `cargo anneal correspondence-bugs file-issue`
//! defaults strictly to offline `--dry-run` preview mode (printing the exact
//! `gh issue create` invocation and formatted Markdown body without spawning any
//! external process) and only invokes `gh` when `--execute` is explicitly
//! passed on the command line by a human operator or dedicated manual job.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::miri_diff::{MiriDiffManifest, load_miri_diff_manifest};

/// Four-way formal taxonomy for every MiniRust-vs-Anneal non-correspondence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum GapKind {
    /// Anneal permits a behavior or computes a value disallowed by MiniRust
    /// ($\pi(b_{\mathrm{MR}}) \not\le b_{\mathrm{Anneal}}$). Critical bug.
    AnnealSoundnessBug,
    /// Anneal conservatively faults with UB where MiniRust steps normally.
    /// Precision / refutation bug.
    AnnealFalsePositiveUb,
    /// Anneal emits `.fail .unsupported` or an external call on an unmodeled
    /// language construct. Tracked roadmap coverage gap.
    AnnealUnmodeledFeature,
    /// Upstream MiniRust intentionally changed semantics relative to a pinned
    /// historical Anneal MIR dialect. Requires a non-empty `rationale_citation`.
    IntentionalEpochDivergence,
}

impl GapKind {
    /// Parse a canonical `kind` string from `correspondence_gaps.toml`.
    pub fn parse(raw: &str) -> Result<Self, String> {
        match raw.trim() {
            "anneal_soundness_bug" => Ok(Self::AnnealSoundnessBug),
            "anneal_false_positive_ub" => Ok(Self::AnnealFalsePositiveUb),
            "anneal_unmodeled_feature" => Ok(Self::AnnealUnmodeledFeature),
            "intentional_epoch_divergence" => Ok(Self::IntentionalEpochDivergence),
            other => Err(format!(
                "invalid gap kind '{other}' (expected 'anneal_soundness_bug', 'anneal_false_positive_ub', 'anneal_unmodeled_feature', or 'intentional_epoch_divergence')"
            )),
        }
    }

    /// Canonical snake_case identifier used in TOML schemas.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::AnnealSoundnessBug => "anneal_soundness_bug",
            Self::AnnealFalsePositiveUb => "anneal_false_positive_ub",
            Self::AnnealUnmodeledFeature => "anneal_unmodeled_feature",
            Self::IntentionalEpochDivergence => "intentional_epoch_divergence",
        }
    }

    /// Whether this entry counts toward active Anneal semantic/coverage gaps
    /// under monotonic ratchet ceilings (`max_open_bugs`), matching
    /// `GapKind.isBug` in `theory/Correspondence/Framework.lean`.
    pub fn is_anneal_bug(&self) -> bool {
        matches!(
            self,
            Self::AnnealSoundnessBug
                | Self::AnnealFalsePositiveUb
                | Self::AnnealUnmodeledFeature
        )
    }

    /// Default GitHub issue classification label for this gap class.
    pub fn github_label(&self) -> &'static str {
        match self {
            Self::AnnealSoundnessBug => "kind:soundness-bug",
            Self::AnnealFalsePositiveUb => "kind:false-positive-ub",
            Self::AnnealUnmodeledFeature => "kind:coverage-gap",
            Self::IntentionalEpochDivergence => "kind:epoch-divergence",
        }
    }
}

/// Formal expected correspondence tier for a cell in `correspondence_matrix.toml`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExpectedTier {
    /// Zero bug gaps and zero epoch divergences allowed.
    ExactUnconditional,
    /// Zero bug gaps allowed; documented `intentional_epoch_divergence` entries permitted.
    EpochDeltaOnly,
    /// Active bug gaps bounded by `max_open_bugs` ratchet ceiling.
    GuardedRatchet,
}

impl ExpectedTier {
    /// Parse a canonical tier identifier from `correspondence_matrix.toml`.
    pub fn parse(raw: &str) -> Result<Self, String> {
        match raw.trim() {
            "ExactUnconditional" | "exact_unconditional" => Ok(Self::ExactUnconditional),
            "EpochDeltaOnly" | "epoch_delta_only" => Ok(Self::EpochDeltaOnly),
            "GuardedRatchet" | "guarded_ratchet" => Ok(Self::GuardedRatchet),
            other => Err(format!(
                "invalid expected_tier '{other}' (expected 'ExactUnconditional', 'EpochDeltaOnly', or 'GuardedRatchet')"
            )),
        }
    }

    /// Canonical CamelCase tier name matching Lean `Scorecard.lean` definitions.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::ExactUnconditional => "ExactUnconditional",
            Self::EpochDeltaOnly => "EpochDeltaOnly",
            Self::GuardedRatchet => "GuardedRatchet",
        }
    }
}

/// Single non-correspondence entry parsed from `correspondence_gaps.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CorrespondenceGapEntry {
    /// Unique stable identifier (for example, `"GAP-MR-0001"` or `"GAP-EPOCH-0001"`).
    pub id: String,
    /// Four-way formal taxonomy classification.
    pub kind: GapKind,
    /// Priority/severity level (`"P0"`, `"P1"`, `"P2"`, `"P3"`, or `"none"`).
    pub severity: String,
    /// Lifecycle status (`"open"`, `"pending_triage"`, `"active_version_skew"`, etc.).
    pub status: String,
    /// Concise one-line summary of the non-correspondence.
    pub title: String,
    /// Anneal MIR dialect versions where this entry applies (for example, `["V2026_06_01"]`).
    pub anneal_versions: Vec<String>,
    /// Upstream MiniRust snapshot identifiers where this entry applies.
    pub minirust_snapshots: Vec<String>,
    /// Horizontal correspondence slice (`"L1_Scalars"` .. `"L6_WholeMachine"`).
    pub layer: String,
    /// Fully qualified Lean declaration in Anneal exhibiting the divergence.
    pub anneal_decl: String,
    /// Repository-relative path to the Anneal source file.
    pub anneal_file: String,
    /// Upstream `@specr-source` span (`"spec/mem/tree_borrows.md:214-249"`).
    pub minirust_source: String,
    /// Optional cross-reference to a `[[tests]]` entry in `tests/miri-diff/manifest.toml`.
    pub miri_diff_cross_ref: Option<String>,
    /// Optional filed GitHub issue number.
    pub github_issue_number: Option<u64>,
    /// Optional filed GitHub issue URL.
    pub github_issue_url: Option<String>,
    /// Decidable Lean predicate expression guarding the universal theorem.
    pub guard_predicate: String,
    /// Fully qualified Lean counterexample fixture proving the divergence is live.
    pub witness_fixture: String,
    /// Current outcome tag produced by Anneal on `witness_fixture`.
    pub expected_anneal_verdict: String,
    /// Reference outcome tag produced by MiniRust on `witness_fixture`.
    pub expected_minirust_verdict: String,
    /// Mandatory upstream citation for `IntentionalEpochDivergence` entries.
    pub rationale_citation: Option<String>,
    /// Optional future Anneal version slated to absorb an epoch divergence.
    pub target_anneal_version: Option<String>,
}

/// Parsed top-level registry from `theory/Correspondence/correspondence_gaps.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CorrespondenceGapsRegistry {
    /// Registry schema version (`1`).
    pub schema_version: u32,
    /// Default target GitHub repository (`"joshlf/anneal"`).
    pub github_repo: String,
    /// Default labels applied when formatting or filing issues.
    pub default_labels: Vec<String>,
    /// Optional global ratchet ceiling bounding active `anneal_soundness_bug`
    /// and `anneal_false_positive_ub` entries across the registry.
    pub max_open_bugs: Option<usize>,
    /// Ordered list of registered non-correspondence entries.
    pub gaps: Vec<CorrespondenceGapEntry>,
}

/// Single `(AnnealVersion, MiniRustSnapshot, Layer)` expectation cell from
/// `theory/Correspondence/correspondence_matrix.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CorrespondenceMatrixCell {
    /// Anneal MIR version identifier (for example, `"V2026_06_01"` or `"V2026_08_01"`).
    pub anneal_version: String,
    /// MiniRust snapshot identifier (for example, `"S2026_05_Matched"` or `"S2026_07_BleedingEdge"`).
    pub minirust_snapshot: String,
    /// Horizontal correspondence slice (for example, `"L4_TreeBorrows"` or `"*"`).
    pub layer: String,
    /// Expected correspondence tier for this cell.
    pub expected_tier: ExpectedTier,
    /// Optional status string (`"exact_unconditional"`, `"epoch_delta_only"`, `"guarded_ratchet"`).
    pub status: Option<String>,
    /// Optional per-cell ratchet ceiling on active bug entries (`GuardedRatchet`).
    pub max_open_bugs: Option<usize>,
    /// Optional explicit gap IDs associated with this cell.
    pub gap_ids: Vec<String>,
}

/// Parsed `theory/Correspondence/correspondence_matrix.toml` specification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CorrespondenceMatrix {
    /// Matrix schema version (`1`).
    pub schema_version: u32,
    /// Optional global ceiling across all matrix cells.
    pub max_open_bugs: Option<usize>,
    /// Ordered expectation cells.
    pub cells: Vec<CorrespondenceMatrixCell>,
}

/// Summary report returned by `lint_correspondence_gaps`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LintReport {
    /// Total number of `[[gaps]]` entries validated.
    pub total_gaps: usize,
    /// Count of `anneal_soundness_bug` entries.
    pub soundness_bug_count: usize,
    /// Count of `anneal_false_positive_ub` entries.
    pub false_positive_ub_count: usize,
    /// Count of `anneal_unmodeled_feature` entries.
    pub unmodeled_feature_count: usize,
    /// Count of `intentional_epoch_divergence` entries.
    pub epoch_divergence_count: usize,
    /// Combined count of active bug entries (`soundness_bug_count + false_positive_ub_count`).
    pub active_bug_count: usize,
    /// Effective global ratchet ceiling verified (if configured).
    pub max_open_bugs_ceiling: Option<usize>,
    /// Number of verified `miri_diff_cross_ref` links against `tests/miri-diff/manifest.toml`.
    pub verified_miri_cross_refs: usize,
}

/// Gate 3 cross-check summary linking `tests/miri-diff/manifest.toml` and
/// `correspondence_gaps.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MiriDiffCrossCheckReport {
    /// Total `[[tests]]` entries in `tests/miri-diff/manifest.toml`.
    pub total_miri_tests: usize,
    /// Number of Miri tests carrying `[tests.known_anneal_bug]`.
    pub total_miri_known_bugs: usize,
    /// Sorted list of Miri `known_anneal_bug` test names.
    pub miri_known_bug_names: Vec<String>,
    /// Verified `(gap_id, miri_test_name)` pairs cross-linked in `correspondence_gaps.toml`.
    pub matched_cross_refs: Vec<(String, String)>,
    /// Miri `known_anneal_bug` test names not yet referenced by a gap entry.
    pub unlinked_miri_bugs: Vec<String>,
}

/// Complete, self-contained GitHub issue payload rendered purely offline.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FormattedGitHubIssue {
    /// Source gap identifier (for example, `"GAP-MR-0001"`).
    pub gap_id: String,
    /// Target GitHub repository (`"<owner>/<repo>"`).
    pub repo: String,
    /// Issue title line.
    pub title: String,
    /// Ordered GitHub issue labels.
    pub labels: Vec<String>,
    /// Publication-ready Markdown issue body.
    pub body: String,
    /// Shell-escaped `gh issue create ...` command line for human review.
    pub gh_command_line: String,
}

/// Options controlling `file_github_issue` (`cargo anneal correspondence-bugs file-issue`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FileIssueOptions {
    /// Target gap ID in `correspondence_gaps.toml`.
    pub gap_id: String,
    /// Target GitHub repository (`"<owner>/<repo>"`).
    pub repo: String,
    /// Optional explicit `--ldap <ldap>` forwarded to the `gh` remote bridge when
    /// `execute == true`.
    pub ldap: Option<String>,
    /// When `false` (the mandatory default), NO external process is ever
    /// spawned and `FileIssueOutcome::DryRunPreview` is returned. Only when
    /// explicitly set to `true` (`--execute`) is `gh_bin` invoked.
    pub execute: bool,
    /// Executable path or name for `gh` (defaults to `"gh"`). Injectable for
    /// hermetic testing without touching real GitHub.
    pub gh_bin: PathBuf,
}

impl FileIssueOptions {
    /// Construct safe default options with `execute: false` (`--dry-run`).
    pub fn new_dry_run(gap_id: impl Into<String>, repo: impl Into<String>) -> Self {
        Self {
            gap_id: gap_id.into(),
            repo: repo.into(),
            ldap: None,
            execute: false,
            gh_bin: PathBuf::from("gh"),
        }
    }
}

/// Outcome of `file_github_issue`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FileIssueOutcome {
    /// Default safe outcome when `execute == false`: zero external processes
    /// were spawned; contains the rendered preview text and exact `gh` command.
    DryRunPreview {
        formatted: FormattedGitHubIssue,
        preview_output: String,
    },
    /// Outcome when `execute == true` (`--execute`): `gh issue create` was
    /// invoked explicitly and succeeded.
    Executed {
        formatted: FormattedGitHubIssue,
        stdout: String,
    },
}

/// Subcommands supported by `cargo anneal correspondence-bugs`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CorrespondenceBugsSubcommand {
    /// Offline schema, vacuity, epoch-rationale, Miri cross-ref, and ratchet ceiling check.
    Lint {
        gaps_toml: PathBuf,
        matrix_toml: Option<PathBuf>,
        miri_manifest: Option<PathBuf>,
        max_open_bugs_override: Option<usize>,
    },
    /// Pure offline rendering of a publication-ready GitHub issue title and Markdown body.
    FormatIssue {
        gaps_toml: PathBuf,
        gap_id: String,
        repo_override: Option<String>,
    },
    /// Opt-in issue filer: defaults strictly to `--dry-run` unless `--execute` is passed.
    FileIssue {
        gaps_toml: PathBuf,
        gap_id: String,
        repo: String,
        ldap: Option<String>,
        execute: bool,
        gh_bin: PathBuf,
    },
}

/// Load and parse `correspondence_gaps.toml` from `path`.
pub fn load_correspondence_gaps(path: &Path) -> Result<CorrespondenceGapsRegistry, String> {
    let raw = fs::read_to_string(path).map_err(|err| {
        format!(
            "failed to read correspondence gaps registry {}: {}",
            path.display(),
            err
        )
    })?;
    parse_correspondence_gaps(&raw)
}

/// Parse `correspondence_gaps.toml` text into a structured [`CorrespondenceGapsRegistry`].
pub fn parse_correspondence_gaps(toml_text: &str) -> Result<CorrespondenceGapsRegistry, String> {
    let normalized_lines = coalesce_multiline_toml(toml_text)?;
    let mut schema_version: u32 = 1;
    let mut github_repo = "joshlf/anneal".to_string();
    let mut default_labels: Vec<String> = Vec::new();
    let mut max_open_bugs: Option<usize> = None;
    let mut gaps: Vec<CorrespondenceGapEntry> = Vec::new();

    let mut in_gap = false;
    let mut current: BTreeMap<String, String> = BTreeMap::new();

    let flush_gap = |current: &mut BTreeMap<String, String>,
                     gaps: &mut Vec<CorrespondenceGapEntry>|
     -> Result<(), String> {
        if current.is_empty() {
            return Ok(());
        }
        let id = current
            .remove("id")
            .ok_or_else(|| "missing required field 'id' in [[gaps]] entry".to_string())?;
        let kind_raw = current
            .remove("kind")
            .ok_or_else(|| format!("missing required field 'kind' in gap '{id}'"))?;
        let kind = GapKind::parse(&kind_raw).map_err(|e| format!("in gap '{id}': {e}"))?;
        let severity = current
            .remove("severity")
            .unwrap_or_else(|| if kind.is_anneal_bug() { "P1".to_string() } else { "none".to_string() });
        let status = current
            .remove("status")
            .unwrap_or_else(|| "open".to_string());
        let title = current
            .remove("title")
            .or_else(|| current.remove("summary"))
            .unwrap_or_default();
        let anneal_versions = match current.remove("anneal_versions") {
            Some(v) => parse_string_list_value(&v, &format!("gap '{id}'.anneal_versions"))?,
            None => match current.remove("anneal_version") {
                Some(single) => vec![single],
                None => vec!["V2026_06_01".to_string()],
            },
        };
        let minirust_snapshots = match current.remove("minirust_snapshots") {
            Some(v) => parse_string_list_value(&v, &format!("gap '{id}'.minirust_snapshots"))?,
            None => match current.remove("minirust_snapshot") {
                Some(single) => vec![single],
                None => Vec::new(),
            },
        };
        let layer = current.remove("layer").unwrap_or_default();
        let anneal_decl = current.remove("anneal_decl").unwrap_or_default();
        let anneal_file = current.remove("anneal_file").unwrap_or_default();
        let minirust_source = current.remove("minirust_source").unwrap_or_default();
        let miri_diff_cross_ref = current
            .remove("miri_diff_cross_ref")
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty());
        let github_issue_number = match current.remove("github_issue_number") {
            Some(raw_num) if !raw_num.trim().is_empty() => Some(
                raw_num
                    .trim()
                    .parse::<u64>()
                    .map_err(|e| format!("invalid github_issue_number '{raw_num}' in gap '{id}': {e}"))?,
            ),
            _ => None,
        };
        let github_issue_url = current
            .remove("github_issue_url")
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty());
        let guard_predicate = current.remove("guard_predicate").unwrap_or_default();
        let witness_fixture = current.remove("witness_fixture").unwrap_or_default();
        let expected_anneal_verdict = current
            .remove("expected_anneal_verdict")
            .unwrap_or_default();
        let expected_minirust_verdict = current
            .remove("expected_minirust_verdict")
            .unwrap_or_default();
        let rationale_citation = current
            .remove("rationale_citation")
            .map(|s| s.trim().to_string());
        let target_anneal_version = current
            .remove("target_anneal_version")
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty());

        current.clear();
        gaps.push(CorrespondenceGapEntry {
            id,
            kind,
            severity,
            status,
            title,
            anneal_versions,
            minirust_snapshots,
            layer,
            anneal_decl,
            anneal_file,
            minirust_source,
            miri_diff_cross_ref,
            github_issue_number,
            github_issue_url,
            guard_predicate,
            witness_fixture,
            expected_anneal_verdict,
            expected_minirust_verdict,
            rationale_citation,
            target_anneal_version,
        });
        Ok(())
    };

    for (line_no, line) in normalized_lines {
        if line == "[[gaps]]" {
            flush_gap(&mut current, &mut gaps)?;
            in_gap = true;
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            flush_gap(&mut current, &mut gaps)?;
            in_gap = false;
            continue;
        }
        let Some((raw_k, raw_v)) = line.split_once('=') else {
            return Err(format!(
                "line {line_no}: expected 'key = value' in correspondence_gaps.toml, got '{line}'"
            ));
        };
        let key = raw_k.trim();
        let val = raw_v.trim();
        if !in_gap {
            match key {
                "schema_version" => {
                    schema_version = val.parse::<u32>().map_err(|e| {
                        format!("line {line_no}: invalid schema_version '{val}': {e}")
                    })?;
                }
                "github_repo" => {
                    github_repo = parse_toml_scalar_string(val, line_no)?;
                }
                "default_labels" => {
                    default_labels =
                        parse_string_list_value(val, &format!("line {line_no} default_labels"))?;
                }
                "max_open_bugs" => {
                    let ceiling = val.parse::<usize>().map_err(|e| {
                        format!("line {line_no}: invalid max_open_bugs '{val}': {e}")
                    })?;
                    max_open_bugs = Some(ceiling);
                }
                _ => {
                    // Allow benign top-level metadata keys authored by companion tools.
                }
            }
        } else {
            let parsed_val = if val.starts_with('[') {
                val.to_string()
            } else {
                parse_toml_scalar_string(val, line_no)?
            };
            current.insert(key.to_string(), parsed_val);
        }
    }
    flush_gap(&mut current, &mut gaps)?;

    Ok(CorrespondenceGapsRegistry {
        schema_version,
        github_repo,
        default_labels,
        max_open_bugs,
        gaps,
    })
}

/// Load and parse `correspondence_matrix.toml` from `path`.
pub fn load_correspondence_matrix(path: &Path) -> Result<CorrespondenceMatrix, String> {
    let raw = fs::read_to_string(path).map_err(|err| {
        format!(
            "failed to read correspondence matrix {}: {}",
            path.display(),
            err
        )
    })?;
    parse_correspondence_matrix(&raw)
}

/// Parse `correspondence_matrix.toml` text into a structured [`CorrespondenceMatrix`].
pub fn parse_correspondence_matrix(toml_text: &str) -> Result<CorrespondenceMatrix, String> {
    let normalized_lines = coalesce_multiline_toml(toml_text)?;
    let mut schema_version: u32 = 1;
    let mut global_max_open_bugs: Option<usize> = None;
    let mut cells: Vec<CorrespondenceMatrixCell> = Vec::new();
    let mut in_cell = false;
    let mut current: BTreeMap<String, String> = BTreeMap::new();

    let flush_cell = |current: &mut BTreeMap<String, String>,
                      cells: &mut Vec<CorrespondenceMatrixCell>|
     -> Result<(), String> {
        if current.is_empty() {
            return Ok(());
        }
        let anneal_version = current
            .remove("anneal_version")
            .unwrap_or_else(|| "V2026_06_01".to_string());
        let minirust_snapshot = current
            .remove("minirust_snapshot")
            .unwrap_or_else(|| "*".to_string());
        let layer = current.remove("layer").unwrap_or_else(|| "*".to_string());
        let status = current.remove("status").filter(|v| !v.trim().is_empty());
        let tier_raw = current
            .remove("expected_tier")
            .or_else(|| current.remove("tier"))
            .or_else(|| status.clone())
            .ok_or_else(|| {
                format!(
                    "missing 'expected_tier' in matrix cell ({anneal_version}, {minirust_snapshot}, {layer})"
                )
            })?;
        let expected_tier = ExpectedTier::parse(&tier_raw)?;
        let max_open_bugs = match current.remove("max_open_bugs") {
            Some(v) if !v.trim().is_empty() => Some(
                v.trim()
                    .parse::<usize>()
                    .map_err(|e| format!("invalid max_open_bugs '{v}' in matrix cell: {e}"))?,
            ),
            _ => None,
        };
        let gap_ids = match current.remove("gap_ids") {
            Some(v) if !v.trim().is_empty() => parse_string_list_value(&v, "gap_ids")?,
            _ => Vec::new(),
        };
        current.clear();
        cells.push(CorrespondenceMatrixCell {
            anneal_version,
            minirust_snapshot,
            layer,
            expected_tier,
            status,
            max_open_bugs,
            gap_ids,
        });
        Ok(())
    };

    for (line_no, line) in normalized_lines {
        if matches!(
            line.as_str(),
            "[[cells]]" | "[[matrix]]" | "[[entries]]" | "[[profiles]]"
        ) {
            flush_cell(&mut current, &mut cells)?;
            in_cell = true;
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            flush_cell(&mut current, &mut cells)?;
            in_cell = false;
            continue;
        }
        let Some((raw_k, raw_v)) = line.split_once('=') else {
            return Err(format!(
                "line {line_no}: expected 'key = value' in correspondence_matrix.toml, got '{line}'"
            ));
        };
        let key = raw_k.trim();
        let val = raw_v.trim();
        if !in_cell {
            match key {
                "schema_version" => {
                    schema_version = val.parse::<u32>().map_err(|e| {
                        format!("line {line_no}: invalid schema_version '{val}': {e}")
                    })?;
                }
                "max_open_bugs" | "global_max_open_bugs" => {
                    global_max_open_bugs = Some(val.parse::<usize>().map_err(|e| {
                        format!("line {line_no}: invalid {key} '{val}': {e}")
                    })?);
                }
                _ => {}
            }
        } else {
            let parsed_val = if val.starts_with('[') {
                val.to_string()
            } else {
                parse_toml_scalar_string(val, line_no)?
            };
            current.insert(key.to_string(), parsed_val);
        }
    }
    flush_cell(&mut current, &mut cells)?;

    Ok(CorrespondenceMatrix {
        schema_version,
        max_open_bugs: global_max_open_bugs,
        cells,
    })
}

/// Returns `true` if `guard` is empty or a vacuous tautology/constant that would
/// silently hollow out a universal correspondence theorem (`MUT-05`).
pub fn is_vacuous_guard_predicate(guard: &str) -> bool {
    let trimmed = guard.trim();
    if trimmed.is_empty() {
        return true;
    }
    // Strip balanced outer parentheses for canonical inspection.
    let mut inner = trimmed;
    while inner.starts_with('(') && inner.ends_with(')') && inner.len() >= 2 {
        inner = inner[1..inner.len() - 1].trim();
    }
    if inner.is_empty() {
        return true;
    }
    let lower = inner.to_ascii_lowercase();
    matches!(
        lower.as_str(),
        "true"
            | "false"
            | "bool.true"
            | "bool.false"
            | "1 == 1"
            | "0 == 0"
            | "1 = 1"
            | "0 = 0"
            | "always"
            | "any"
            | "*"
            | "_"
            | "fun _ => true"
            | "fun _ _ => true"
            | "fun _ _ _ => true"
            | "λ _ => true"
            | "λ _ _ => true"
            | "const true"
    )
}

/// Validate a parsed [`CorrespondenceGapsRegistry`] (plus optional matrix and
/// `tests/miri-diff/manifest.toml`) completely offline with zero network calls.
pub fn lint_correspondence_gaps(
    registry: &CorrespondenceGapsRegistry,
    matrix: Option<&CorrespondenceMatrix>,
    miri_manifest: Option<&MiriDiffManifest>,
    max_open_bugs_override: Option<usize>,
) -> Result<LintReport, String> {
    lint_correspondence_gaps_with_vendor_root(
        registry,
        matrix,
        miri_manifest,
        max_open_bugs_override,
        None,
    )
}

/// Validate a parsed [`CorrespondenceGapsRegistry`] along with optional on-disk
/// `theory/MiniRust/vendor` file existence and line-count bounds checking.
pub fn lint_correspondence_gaps_with_vendor_root(
    registry: &CorrespondenceGapsRegistry,
    matrix: Option<&CorrespondenceMatrix>,
    miri_manifest: Option<&MiriDiffManifest>,
    max_open_bugs_override: Option<usize>,
    vendor_root: Option<&Path>,
) -> Result<LintReport, String> {
    if registry.schema_version == 0 {
        return Err("schema_version in correspondence_gaps.toml must be >= 1".to_string());
    }

    let mut seen_ids = BTreeSet::new();
    let mut soundness_bug_count = 0usize;
    let mut false_positive_ub_count = 0usize;
    let mut unmodeled_feature_count = 0usize;
    let mut epoch_divergence_count = 0usize;
    let mut verified_miri_cross_refs = 0usize;

    let miri_tests_by_name: BTreeMap<&str, bool> = miri_manifest
        .map(|m| {
            m.tests
                .iter()
                .map(|t| (t.name.as_str(), t.known_anneal_bug.is_some()))
                .collect()
        })
        .unwrap_or_default();

    for gap in &registry.gaps {
        let id = gap.id.trim();
        if id.is_empty() {
            return Err("gap entry has an empty 'id'".to_string());
        }
        if !seen_ids.insert(id.to_string()) {
            return Err(format!("duplicate gap id '{id}' in correspondence_gaps.toml"));
        }

        // Reject stale / invalid status gap entries (`MUT-04`).
        let status_lower = gap.status.trim().to_ascii_lowercase();
        if gap.kind.is_anneal_bug() {
            if !matches!(status_lower.as_str(), "open" | "closed") {
                return Err(format!(
                    "stale gap entry '{id}' has status '{}': bug gaps must have status = \"open\" or status = \"closed\"",
                    gap.status
                ));
            }
        } else if matches!(
            status_lower.as_str(),
            "fixed" | "resolved" | "stale" | "obsolete" | "removed"
        ) {
            return Err(format!(
                "stale gap entry '{id}' has status '{}' (fixed or stale entries must be deleted so the ratchet tightens)",
                gap.status
            ));
        }

        if gap.title.trim().is_empty() {
            return Err(format!("gap entry '{id}' must have a non-empty 'title'"));
        }

        if gap.witness_fixture.trim().is_empty() {
            return Err(format!(
                "gap entry '{id}' must declare a non-empty 'witness_fixture'"
            ));
        }

        // Validate `minirust_source` `<relpath>:<start>-<end>` syntax and (when
        // `vendor_root` is available) verify file existence and line bounds.
        validate_minirust_source_span(
            id,
            &gap.minirust_source,
            &gap.minirust_snapshots,
            vendor_root,
        )?;

        // Reject non-divergent / stale verdict pairs where Anneal already matches MiniRust (`MUT-04`).
        let anneal_v = gap.expected_anneal_verdict.trim();
        let minirust_v = gap.expected_minirust_verdict.trim();
        if status_lower == "open"
            && !anneal_v.is_empty()
            && !minirust_v.is_empty()
            && anneal_v == minirust_v
        {
            return Err(format!(
                "stale gap entry '{id}': expected_anneal_verdict ('{anneal_v}') equals expected_minirust_verdict ('{minirust_v}'); remove the fixed entry"
            ));
        }

        // Reject empty or overly broad / vacuous guard predicates (`MUT-05`).
        if is_vacuous_guard_predicate(&gap.guard_predicate) {
            return Err(format!(
                "vacuous or overly broad guard_predicate '{}' in gap entry '{id}' (rejected to prevent hollowing out universal theorems)",
                gap.guard_predicate
            ));
        }

        // Enforce mandatory rationale_citation on intentional_epoch_divergence (`MUT-06` / epoch hygiene).
        if gap.kind == GapKind::IntentionalEpochDivergence {
            let citation = gap.rationale_citation.as_deref().map(str::trim).unwrap_or("");
            let lower_cit = citation.to_ascii_lowercase();
            if citation.is_empty()
                || matches!(lower_cit.as_str(), "none" | "n/a" | "na" | "tbd" | "unknown")
            {
                return Err(format!(
                    "gap entry '{id}' has kind 'intentional_epoch_divergence' but is missing a valid non-empty 'rationale_citation'"
                ));
            }
        }

        // Cross-check optional Miri differential suite link (`Gate 3`).
        if let Some(ref miri_ref) = gap.miri_diff_cross_ref {
            if miri_manifest.is_some() {
                match miri_tests_by_name.get(miri_ref.as_str()) {
                    None => {
                        return Err(format!(
                            "gap entry '{id}' references nonexistent miri_diff_cross_ref '{miri_ref}' in tests/miri-diff/manifest.toml"
                        ));
                    }
                    Some(false) if status_lower == "open" => {
                        return Err(format!(
                            "stale gap entry '{id}': referenced Miri test '{miri_ref}' has no open known_anneal_bug in tests/miri-diff/manifest.toml"
                        ));
                    }
                    Some(_) => {
                        verified_miri_cross_refs += 1;
                    }
                }
            }
        }

        match gap.kind {
            GapKind::AnnealSoundnessBug if status_lower == "open" => soundness_bug_count += 1,
            GapKind::AnnealFalsePositiveUb if status_lower == "open" => {
                false_positive_ub_count += 1
            }
            GapKind::AnnealUnmodeledFeature if status_lower == "open" => {
                unmodeled_feature_count += 1
            }
            GapKind::IntentionalEpochDivergence if status_lower != "closed" => {
                epoch_divergence_count += 1
            }
            _ => {}
        }
    }

    let active_bug_count =
        soundness_bug_count + false_positive_ub_count + unmodeled_feature_count;

    // Determine effective global ratchet ceiling from CLI override, gaps registry, or matrix.
    let effective_ceiling = max_open_bugs_override
        .or(registry.max_open_bugs)
        .or_else(|| matrix.and_then(|m| m.max_open_bugs));

    if let Some(max_bugs) = effective_ceiling
        && active_bug_count > max_bugs
    {
        return Err(format!(
            "ratchet ceiling exceeded: active_bug_count ({active_bug_count}) > max_open_bugs ({max_bugs})"
        ));
    }

    // Validate per-cell tier & ratchet rules when `correspondence_matrix.toml` is supplied.
    if let Some(mat) = matrix {
        for cell in &mat.cells {
            let matching_gaps: Vec<&CorrespondenceGapEntry> = registry
                .gaps
                .iter()
                .filter(|g| gap_applies_to_cell(g, cell))
                .collect();
            let cell_bug_count = matching_gaps
                .iter()
                .filter(|g| g.kind.is_anneal_bug())
                .count();
            let cell_epoch_count = matching_gaps
                .iter()
                .filter(|g| g.kind == GapKind::IntentionalEpochDivergence)
                .count();

            match cell.expected_tier {
                ExpectedTier::ExactUnconditional => {
                    if !matching_gaps.is_empty() {
                        return Err(format!(
                            "matrix cell ({}, {}, {}) requires ExactUnconditional (zero active gaps) but has {} active gaps ({cell_bug_count} bug/unmodeled gaps, {cell_epoch_count} epoch divergences)",
                            cell.anneal_version,
                            cell.minirust_snapshot,
                            cell.layer,
                            matching_gaps.len()
                        ));
                    }
                }
                ExpectedTier::EpochDeltaOnly => {
                    if cell_bug_count > 0 {
                        return Err(format!(
                            "matrix cell ({}, {}, {}) requires EpochDeltaOnly (0 bug/unmodeled gaps) but has {cell_bug_count} active bug/unmodeled gaps",
                            cell.anneal_version, cell.minirust_snapshot, cell.layer
                        ));
                    }
                }
                ExpectedTier::GuardedRatchet => {
                    if let Some(cell_max) = cell.max_open_bugs
                        && cell_bug_count > cell_max
                    {
                        return Err(format!(
                            "ratchet ceiling exceeded in matrix cell ({}, {}, {}): active_bug_count ({cell_bug_count}) > max_open_bugs ({cell_max})",
                            cell.anneal_version, cell.minirust_snapshot, cell.layer
                        ));
                    }
                }
            }
        }
    }

    Ok(LintReport {
        total_gaps: registry.gaps.len(),
        soundness_bug_count,
        false_positive_ub_count,
        unmodeled_feature_count,
        epoch_divergence_count,
        active_bug_count,
        max_open_bugs_ceiling: effective_ceiling,
        verified_miri_cross_refs,
    })
}

/// Gate 3 Cross-Check: validate alignment between `tests/miri-diff/manifest.toml`
/// and `correspondence_gaps.toml` without spawning any external tools.
pub fn cross_check_miri_diff(
    miri_manifest: &MiriDiffManifest,
    gaps_registry: &CorrespondenceGapsRegistry,
) -> Result<MiriDiffCrossCheckReport, String> {
    let mut known_bug_set = BTreeSet::new();
    for entry in &miri_manifest.tests {
        if entry.known_anneal_bug.is_some() {
            known_bug_set.insert(entry.name.clone());
        }
    }

    let all_test_names: BTreeSet<&str> =
        miri_manifest.tests.iter().map(|t| t.name.as_str()).collect();

    let mut matched_cross_refs = Vec::new();
    let mut linked_miri_names = BTreeSet::new();

    for gap in &gaps_registry.gaps {
        if let Some(ref miri_ref) = gap.miri_diff_cross_ref {
            if !all_test_names.contains(miri_ref.as_str()) {
                return Err(format!(
                    "gap '{}' cross-references unknown Miri test '{miri_ref}'",
                    gap.id
                ));
            }
            if gap.status.trim().eq_ignore_ascii_case("open")
                && !known_bug_set.contains(miri_ref.as_str())
            {
                return Err(format!(
                    "gap '{}' cross-references Miri test '{miri_ref}', which is already passing in manifest.toml (stale bug entry)",
                    gap.id
                ));
            }
            if gap.status.trim().eq_ignore_ascii_case("closed")
                && known_bug_set.contains(miri_ref.as_str())
            {
                return Err(format!(
                    "gap '{}' is marked 'closed' but cross-references Miri test '{miri_ref}', which still carries a known_anneal_bug in manifest.toml",
                    gap.id
                ));
            }
            linked_miri_names.insert(miri_ref.clone());
            matched_cross_refs.push((gap.id.clone(), miri_ref.clone()));
        }
    }

    let miri_known_bug_names: Vec<String> = known_bug_set.iter().cloned().collect();
    let unlinked_miri_bugs: Vec<String> = known_bug_set
        .difference(&linked_miri_names)
        .cloned()
        .collect();

    Ok(MiriDiffCrossCheckReport {
        total_miri_tests: miri_manifest.tests.len(),
        total_miri_known_bugs: miri_known_bug_names.len(),
        miri_known_bug_names,
        matched_cross_refs,
        unlinked_miri_bugs,
    })
}

/// Pure offline formatter producing a publication-ready GitHub issue title,
/// label list, Markdown body, and shell command preview for a single gap entry.
pub fn format_github_issue(
    registry: &CorrespondenceGapsRegistry,
    gap_id: &str,
    repo_override: Option<&str>,
) -> Result<FormattedGitHubIssue, String> {
    let target_id = gap_id.trim();
    let gap = registry
        .gaps
        .iter()
        .find(|g| g.id == target_id)
        .ok_or_else(|| format!("gap id '{target_id}' not found in correspondence_gaps.toml"))?;

    let repo = repo_override
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .unwrap_or(registry.github_repo.as_str())
        .to_string();

    let title = format!("[MiniRust Correspondence][{}] {}", gap.id, gap.title.trim());

    let mut labels: Vec<String> = registry.default_labels.clone();
    if labels.is_empty() {
        labels.push("source:minirust-correspondence".to_string());
        labels.push("area:mir-semantics".to_string());
    }
    let kind_label = gap.kind.github_label().to_string();
    if !labels.contains(&kind_label) {
        labels.push(kind_label);
    }
    if !gap.severity.is_empty() && gap.severity != "none" {
        let sev_label = format!("priority:{}", gap.severity);
        if !labels.contains(&sev_label) {
            labels.push(sev_label);
        }
    }

    let mut body = String::new();
    body.push_str(&format!(
        "## Formal Non-Correspondence Report: `{}`\n\n",
        gap.id
    ));
    body.push_str(&format!("**Summary**: {}\n\n", gap.title.trim()));
    body.push_str("### Classification & Scope\n\n");
    body.push_str("| Field | Value |\n| :--- | :--- |\n");
    body.push_str(&format!("| **Gap ID** | `{}` |\n", gap.id));
    body.push_str(&format!("| **Formal Class** | `{}` |\n", gap.kind.as_str()));
    body.push_str(&format!("| **Severity** | `{}` |\n", gap.severity));
    body.push_str(&format!("| **Status** | `{}` |\n", gap.status));
    if !gap.layer.is_empty() {
        body.push_str(&format!("| **Semantic Layer** | `{}` |\n", gap.layer));
    }
    if !gap.anneal_versions.is_empty() {
        body.push_str(&format!(
            "| **Anneal Versions** | `{}` |\n",
            gap.anneal_versions.join(", ")
        ));
    }
    if !gap.minirust_snapshots.is_empty() {
        body.push_str(&format!(
            "| **MiniRust Snapshots** | `{}` |\n",
            gap.minirust_snapshots.join(", ")
        ));
    }

    body.push_str("\n### Pinpointed Specification Provenance\n\n");
    if !gap.anneal_decl.is_empty() {
        body.push_str(&format!("- **Anneal Declaration**: `{}`\n", gap.anneal_decl));
    }
    if !gap.anneal_file.is_empty() {
        body.push_str(&format!("- **Anneal Source File**: `{}`\n", gap.anneal_file));
    }
    if !gap.minirust_source.is_empty() {
        body.push_str(&format!(
            "- **Upstream MiniRust `@specr-source`**: `{}`\n",
            gap.minirust_source
        ));
    }
    if let Some(ref miri_ref) = gap.miri_diff_cross_ref {
        body.push_str(&format!(
            "- **Cross-Referenced Miri Differential Test**: `{miri_ref}` (`tests/miri-diff/manifest.toml`)\n"
        ));
    }
    if let Some(ref citation) = gap.rationale_citation
        && !citation.is_empty()
    {
        body.push_str(&format!("- **Epoch Rationale Citation**: {citation}\n"));
    }

    body.push_str("\n### Two-Way Kernel Ratchet & Counterexample Witness\n\n");
    body.push_str(&format!(
        "- **Guard Predicate**: `{}`\n",
        gap.guard_predicate
    ));
    body.push_str(&format!(
        "- **Witness Fixture**: `{}`\n",
        gap.witness_fixture
    ));
    if !gap.expected_anneal_verdict.is_empty() || !gap.expected_minirust_verdict.is_empty() {
        body.push_str(&format!(
            "- **Observed Anneal Verdict vs. Reference MiniRust Verdict**: `{}` vs. `{}`\n",
            gap.expected_anneal_verdict, gap.expected_minirust_verdict
        ));
    }
    body.push_str(
        "\nOnce the underlying Anneal semantics bug is fixed so that Anneal matches MiniRust on the witness fixture, `GeneratedGapWitnesses.lean` will automatically fail `lake build` until this entry is removed from `theory/Correspondence/correspondence_gaps.toml`.\n",
    );

    let mut cmd_parts = vec![
        "gh".to_string(),
        "issue".to_string(),
        "create".to_string(),
        "--repo".to_string(),
        shell_escape(&repo),
        "--title".to_string(),
        shell_escape(&title),
    ];
    for label in &labels {
        cmd_parts.push("--label".to_string());
        cmd_parts.push(shell_escape(label));
    }
    cmd_parts.push("--body".to_string());
    cmd_parts.push(shell_escape(&body));

    Ok(FormattedGitHubIssue {
        gap_id: gap.id.clone(),
        repo,
        title,
        labels,
        body,
        gh_command_line: cmd_parts.join(" "),
    })
}

/// Opt-in manual issue filing entry point (`cargo anneal correspondence-bugs file-issue`).
///
/// # Hard Safety Guarantee
///
/// When `options.execute == false` (the default), this function **never** spawns
/// any child process or opens any network connection. It renders the complete
/// dry-run preview and returns [`FileIssueOutcome::DryRunPreview`]. Only when
/// `options.execute == true` (`--execute` on the CLI) does it invoke
/// `options.gh_bin`.
pub fn file_github_issue(
    registry: &CorrespondenceGapsRegistry,
    options: &FileIssueOptions,
) -> Result<FileIssueOutcome, String> {
    let formatted = format_github_issue(registry, &options.gap_id, Some(&options.repo))?;

    if !options.execute {
        let mut preview = String::new();
        preview.push_str(
            "[DRY-RUN] Zero GitHub issues were created (pass --execute explicitly to invoke `gh issue create`).\n",
        );
        preview.push_str(&format!("Command: {}\n\n", formatted.gh_command_line));
        preview.push_str(&format!("Title: {}\n", formatted.title));
        preview.push_str(&format!("Labels: {}\n\n", formatted.labels.join(", ")));
        preview.push_str(&formatted.body);
        return Ok(FileIssueOutcome::DryRunPreview {
            formatted,
            preview_output: preview,
        });
    }

    // Explicit `--execute` path: invoke the configured `gh` binary.
    let mut cmd = Command::new(&options.gh_bin);
    if let Some(ref ldap) = options.ldap
        && !ldap.trim().is_empty()
    {
        cmd.arg("--ldap").arg(ldap.trim());
    }
    cmd.arg("issue")
        .arg("create")
        .arg("--repo")
        .arg(&formatted.repo)
        .arg("--title")
        .arg(&formatted.title);
    for label in &formatted.labels {
        cmd.arg("--label").arg(label);
    }
    cmd.arg("--body").arg(&formatted.body);

    let output = cmd.output().map_err(|err| {
        format!(
            "failed to invoke '{}' for explicit --execute issue creation: {err}",
            options.gh_bin.display()
        )
    })?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        return Err(format!(
            "'{} issue create' failed with status {}:\n{}{}",
            options.gh_bin.display(),
            output.status,
            stdout,
            stderr
        ));
    }
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_string();
    Ok(FileIssueOutcome::Executed { formatted, stdout })
}

/// Parse CLI arguments following `cargo anneal correspondence-bugs ...`.
pub fn parse_correspondence_bugs_args(args: &[String]) -> Result<CorrespondenceBugsSubcommand, String> {
    let default_gaps = PathBuf::from("theory/Correspondence/correspondence_gaps.toml");
    let Some(sub) = args.first().map(String::as_str) else {
        return Err(
            "missing subcommand for 'correspondence-bugs' (expected 'lint', 'format-issue', or 'file-issue')"
                .to_string(),
        );
    };

    let rest = &args[1..];
    match sub {
        "lint" => {
            let mut gaps_toml = default_gaps;
            let mut matrix_toml: Option<PathBuf> = None;
            let mut miri_manifest: Option<PathBuf> = None;
            let mut max_open_bugs_override: Option<usize> = None;
            let mut i = 0;
            while i < rest.len() {
                match rest[i].as_str() {
                    "--gaps-toml" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --gaps-toml")?;
                        gaps_toml = PathBuf::from(val);
                    }
                    s if s.starts_with("--gaps-toml=") => {
                        gaps_toml = PathBuf::from(&s["--gaps-toml=".len()..]);
                    }
                    "--matrix-toml" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --matrix-toml")?;
                        matrix_toml = Some(PathBuf::from(val));
                    }
                    s if s.starts_with("--matrix-toml=") => {
                        matrix_toml = Some(PathBuf::from(&s["--matrix-toml=".len()..]));
                    }
                    "--miri-manifest" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --miri-manifest")?;
                        miri_manifest = Some(PathBuf::from(val));
                    }
                    s if s.starts_with("--miri-manifest=") => {
                        miri_manifest = Some(PathBuf::from(&s["--miri-manifest=".len()..]));
                    }
                    "--max-open-bugs" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --max-open-bugs")?;
                        max_open_bugs_override = Some(
                            val.parse::<usize>()
                                .map_err(|e| format!("invalid --max-open-bugs '{val}': {e}"))?,
                        );
                    }
                    "--ci" => {
                        // Accepted offline strict validation flag; never performs network I/O.
                    }
                    other => {
                        return Err(format!("unknown flag '{other}' for 'correspondence-bugs lint'"));
                    }
                }
                i += 1;
            }
            Ok(CorrespondenceBugsSubcommand::Lint {
                gaps_toml,
                matrix_toml,
                miri_manifest,
                max_open_bugs_override,
            })
        }
        "format-issue" => {
            let mut gaps_toml = default_gaps;
            let mut gap_id: Option<String> = None;
            let mut repo_override: Option<String> = None;
            let mut i = 0;
            while i < rest.len() {
                match rest[i].as_str() {
                    "--gap-id" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --gap-id")?;
                        gap_id = Some(val.clone());
                    }
                    s if s.starts_with("--gap-id=") => {
                        gap_id = Some(s["--gap-id=".len()..].to_string());
                    }
                    "--gaps-toml" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --gaps-toml")?;
                        gaps_toml = PathBuf::from(val);
                    }
                    s if s.starts_with("--gaps-toml=") => {
                        gaps_toml = PathBuf::from(&s["--gaps-toml=".len()..]);
                    }
                    "--repo" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --repo")?;
                        repo_override = Some(val.clone());
                    }
                    other => {
                        return Err(format!(
                            "unknown flag '{other}' for 'correspondence-bugs format-issue'"
                        ));
                    }
                }
                i += 1;
            }
            let gap_id = gap_id.ok_or("missing required '--gap-id <id>' for 'format-issue'")?;
            Ok(CorrespondenceBugsSubcommand::FormatIssue {
                gaps_toml,
                gap_id,
                repo_override,
            })
        }
        "file-issue" => {
            let mut gaps_toml = default_gaps;
            let mut gap_id: Option<String> = None;
            let mut repo: Option<String> = None;
            let mut ldap: Option<String> = None;
            let mut execute = false;
            let mut gh_bin = PathBuf::from("gh");
            let mut i = 0;
            while i < rest.len() {
                match rest[i].as_str() {
                    "--gap-id" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --gap-id")?;
                        gap_id = Some(val.clone());
                    }
                    s if s.starts_with("--gap-id=") => {
                        gap_id = Some(s["--gap-id=".len()..].to_string());
                    }
                    "--repo" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --repo")?;
                        repo = Some(val.clone());
                    }
                    s if s.starts_with("--repo=") => {
                        repo = Some(s["--repo=".len()..].to_string());
                    }
                    "--gaps-toml" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --gaps-toml")?;
                        gaps_toml = PathBuf::from(val);
                    }
                    s if s.starts_with("--gaps-toml=") => {
                        gaps_toml = PathBuf::from(&s["--gaps-toml=".len()..]);
                    }
                    "--ldap" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --ldap")?;
                        ldap = Some(val.clone());
                    }
                    s if s.starts_with("--ldap=") => {
                        ldap = Some(s["--ldap=".len()..].to_string());
                    }
                    "--gh-bin" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --gh-bin")?;
                        gh_bin = PathBuf::from(val);
                    }
                    "--execute" => {
                        execute = true;
                    }
                    "--dry-run" => {
                        execute = false;
                    }
                    other => {
                        return Err(format!(
                            "unknown flag '{other}' for 'correspondence-bugs file-issue'"
                        ));
                    }
                }
                i += 1;
            }
            let gap_id = gap_id.ok_or("missing required '--gap-id <id>' for 'file-issue'")?;
            let repo = repo.ok_or("missing required '--repo <owner/repo>' for 'file-issue'")?;
            Ok(CorrespondenceBugsSubcommand::FileIssue {
                gaps_toml,
                gap_id,
                repo,
                ldap,
                execute,
                gh_bin,
            })
        }
        other => Err(format!(
            "unknown 'correspondence-bugs' subcommand '{other}' (expected 'lint', 'format-issue', or 'file-issue')"
        )),
    }
}

/// Execute a parsed [`CorrespondenceBugsSubcommand`] and return formatted stdout text.
pub fn run_correspondence_bugs_cli(cmd: &CorrespondenceBugsSubcommand) -> Result<String, String> {
    match cmd {
        CorrespondenceBugsSubcommand::Lint {
            gaps_toml,
            matrix_toml,
            miri_manifest,
            max_open_bugs_override,
        } => {
            let registry = load_correspondence_gaps(gaps_toml)?;
            let matrix = match matrix_toml {
                Some(p) => Some(load_correspondence_matrix(p)?),
                None => None,
            };
            let miri = match miri_manifest {
                Some(p) => Some(load_miri_diff_manifest(p)?),
                None => None,
            };
            let vendor_root = discover_vendor_root_from_gaps_path(gaps_toml);
            let report = lint_correspondence_gaps_with_vendor_root(
                &registry,
                matrix.as_ref(),
                miri.as_ref(),
                *max_open_bugs_override,
                vendor_root.as_deref(),
            )?;
            let mut out = String::new();
            out.push_str("Correspondence Gaps Lint: PASS\n");
            out.push_str(&format!("  Total gaps: {}\n", report.total_gaps));
            out.push_str(&format!(
                "  Active bug gaps: {} (soundness: {}, false_positive_ub: {}, unmodeled_feature: {})\n",
                report.active_bug_count,
                report.soundness_bug_count,
                report.false_positive_ub_count,
                report.unmodeled_feature_count
            ));
            out.push_str(&format!(
                "  Unmodeled features: {}, Intentional epoch divergences: {}\n",
                report.unmodeled_feature_count, report.epoch_divergence_count
            ));
            if let Some(ceiling) = report.max_open_bugs_ceiling {
                out.push_str(&format!(
                    "  Ratchet ceiling: {} / {ceiling} open bugs\n",
                    report.active_bug_count
                ));
            }
            if report.verified_miri_cross_refs > 0 {
                out.push_str(&format!(
                    "  Verified Miri manifest cross-refs: {}\n",
                    report.verified_miri_cross_refs
                ));
            }
            Ok(out)
        }
        CorrespondenceBugsSubcommand::FormatIssue {
            gaps_toml,
            gap_id,
            repo_override,
        } => {
            let registry = load_correspondence_gaps(gaps_toml)?;
            let formatted = format_github_issue(&registry, gap_id, repo_override.as_deref())?;
            let mut out = String::new();
            out.push_str(&format!("Title: {}\n", formatted.title));
            out.push_str(&format!("Labels: {}\n\n", formatted.labels.join(", ")));
            out.push_str(&formatted.body);
            Ok(out)
        }
        CorrespondenceBugsSubcommand::FileIssue {
            gaps_toml,
            gap_id,
            repo,
            ldap,
            execute,
            gh_bin,
        } => {
            let registry = load_correspondence_gaps(gaps_toml)?;
            let opts = FileIssueOptions {
                gap_id: gap_id.clone(),
                repo: repo.clone(),
                ldap: ldap.clone(),
                execute: *execute,
                gh_bin: gh_bin.clone(),
            };
            match file_github_issue(&registry, &opts)? {
                FileIssueOutcome::DryRunPreview { preview_output, .. } => Ok(preview_output),
                FileIssueOutcome::Executed { stdout, .. } => Ok(format!(
                    "Created GitHub issue via explicit --execute: {stdout}\n"
                )),
            }
        }
    }
}

fn gap_applies_to_cell(gap: &CorrespondenceGapEntry, cell: &CorrespondenceMatrixCell) -> bool {
    if gap.status.trim().eq_ignore_ascii_case("closed") {
        return false;
    }
    let ver_match = cell.anneal_version == "*"
        || gap.anneal_versions.is_empty()
        || gap
            .anneal_versions
            .iter()
            .any(|v| v == "*" || v == &cell.anneal_version);
    let snap_match = cell.minirust_snapshot == "*"
        || gap.minirust_snapshots.is_empty()
        || gap
            .minirust_snapshots
            .iter()
            .any(|s| s == "*" || s == &cell.minirust_snapshot);
    let layer_match =
        cell.layer == "*" || gap.layer.is_empty() || gap.layer == "*" || gap.layer == cell.layer;
    ver_match && snap_match && layer_match
}

fn discover_vendor_root_from_gaps_path(gaps_toml: &Path) -> Option<PathBuf> {
    let abs = if gaps_toml.is_absolute() {
        gaps_toml.to_path_buf()
    } else {
        std::env::current_dir().ok()?.join(gaps_toml)
    };
    let mut cur = abs.parent();
    while let Some(dir) = cur {
        let candidate = dir.join("theory/MiniRust/vendor");
        if candidate.is_dir() {
            return Some(candidate);
        }
        cur = dir.parent();
    }
    None
}

fn validate_minirust_source_span(
    gap_id: &str,
    raw_source: &str,
    snapshots: &[String],
    vendor_root: Option<&Path>,
) -> Result<(), String> {
    let trimmed = raw_source.trim();
    if trimmed.is_empty() {
        return Err(format!(
            "gap entry '{gap_id}' must declare a non-empty 'minirust_source' (<relpath>:<start>-<end>)"
        ));
    }
    let Some((rel_path, range_part)) = trimmed.rsplit_once(':') else {
        return Err(format!(
            "invalid minirust_source '{trimmed}' in gap '{gap_id}': expected '<relpath>:<start>-<end>'"
        ));
    };
    let rel_path = rel_path.trim();
    if rel_path.is_empty() || !rel_path.starts_with("spec/") || rel_path.contains("..") {
        return Err(format!(
            "invalid minirust_source path '{rel_path}' in gap '{gap_id}': must be a relative path starting with 'spec/'"
        ));
    }
    let (start_str, end_str) = match range_part.trim().split_once('-') {
        Some((s, e)) => (s.trim(), e.trim()),
        None => (range_part.trim(), range_part.trim()),
    };
    let start_line = start_str.parse::<usize>().map_err(|e| {
        format!(
            "invalid start line '{start_str}' in minirust_source '{trimmed}' for gap '{gap_id}': {e}"
        )
    })?;
    let end_line = end_str.parse::<usize>().map_err(|e| {
        format!(
            "invalid end line '{end_str}' in minirust_source '{trimmed}' for gap '{gap_id}': {e}"
        )
    })?;
    if start_line == 0 || start_line > end_line {
        return Err(format!(
            "invalid line range {start_line}-{end_line} in minirust_source '{trimmed}' for gap '{gap_id}': require 1 <= start <= end"
        ));
    }

    if let Some(v_root) = vendor_root {
        for snap in snapshots {
            let snap_dir = v_root.join(snap);
            if !snap_dir.is_dir() {
                continue;
            }
            let target_file = snap_dir.join(rel_path);
            if !target_file.is_file() {
                return Err(format!(
                    "gap entry '{gap_id}': minirust_source file '{rel_path}' does not exist in snapshot '{snap}' ({})",
                    target_file.display()
                ));
            }
            let content = fs::read_to_string(&target_file).map_err(|err| {
                format!(
                    "failed to read minirust_source file {}: {err}",
                    target_file.display()
                )
            })?;
            let total_lines = content.lines().count();
            if end_line > total_lines {
                return Err(format!(
                    "gap entry '{gap_id}': minirust_source '{trimmed}' end line {end_line} exceeds file line count ({total_lines}) of '{rel_path}' in snapshot '{snap}'"
                ));
            }
        }
    }

    Ok(())
}

fn shell_escape(s: &str) -> String {
    if !s.is_empty()
        && s.bytes().all(|b| {
            b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'/' | b'.' | b':')
        })
    {
        return s.to_string();
    }
    let escaped = s.replace('\'', "'\"'\"'");
    format!("'{escaped}'")
}

/// Strip unquoted `# ...` comments and join bracketed multi-line array values
/// into clean logical `(line_no, line)` pairs.
pub(crate) fn coalesce_multiline_toml(text: &str) -> Result<Vec<(usize, String)>, String> {
    let mut out = Vec::new();
    let mut pending_line_no = 0usize;
    let mut pending = String::new();
    let mut bracket_depth = 0i32;

    for (idx, raw_line) in text.lines().enumerate() {
        let line_no = idx + 1;
        let clean = strip_unquoted_toml_comment(raw_line).trim();
        if clean.is_empty() {
            continue;
        }
        if bracket_depth == 0 {
            pending_line_no = line_no;
            pending.clear();
            pending.push_str(clean);
        } else {
            pending.push(' ');
            pending.push_str(clean);
        }
        bracket_depth += count_unquoted_bracket_delta(clean);
        if bracket_depth < 0 {
            return Err(format!("line {line_no}: unmatched ']' in TOML input"));
        }
        if bracket_depth == 0 {
            out.push((pending_line_no, pending.clone()));
            pending.clear();
        }
    }
    if bracket_depth != 0 {
        return Err(format!(
            "line {pending_line_no}: unclosed '[' array in TOML input"
        ));
    }
    Ok(out)
}

pub(crate) fn strip_unquoted_toml_comment(line: &str) -> &str {
    let bytes = line.as_bytes();
    let mut in_quotes = false;
    let mut escaped = false;
    for (idx, &b) in bytes.iter().enumerate() {
        if escaped {
            escaped = false;
            continue;
        }
        if in_quotes && b == b'\\' {
            escaped = true;
            continue;
        }
        if b == b'"' {
            in_quotes = !in_quotes;
            continue;
        }
        if !in_quotes && b == b'#' {
            return &line[..idx];
        }
    }
    line
}

fn count_unquoted_bracket_delta(line: &str) -> i32 {
    let mut delta = 0i32;
    let mut in_quotes = false;
    let mut escaped = false;
    for b in line.bytes() {
        if escaped {
            escaped = false;
            continue;
        }
        if in_quotes && b == b'\\' {
            escaped = true;
            continue;
        }
        if b == b'"' {
            in_quotes = !in_quotes;
            continue;
        }
        if !in_quotes {
            if b == b'[' {
                delta += 1;
            } else if b == b']' {
                delta -= 1;
            }
        }
    }
    delta
}

pub(crate) fn parse_toml_scalar_string(raw: &str, line_no: usize) -> Result<String, String> {
    let trimmed = raw.trim();
    if trimmed.starts_with('"') && trimmed.ends_with('"') && trimmed.len() >= 2 {
        let inner = &trimmed[1..trimmed.len() - 1];
        let mut out = String::with_capacity(inner.len());
        let mut chars = inner.chars();
        while let Some(c) = chars.next() {
            if c == '\\' {
                match chars.next() {
                    Some('"') => out.push('"'),
                    Some('\\') => out.push('\\'),
                    Some('n') => out.push('\n'),
                    Some('r') => out.push('\r'),
                    Some('t') => out.push('\t'),
                    Some(other) => {
                        out.push('\\');
                        out.push(other);
                    }
                    None => return Err(format!("line {line_no}: trailing backslash in string")),
                }
            } else {
                out.push(c);
            }
        }
        return Ok(out);
    }
    if trimmed.starts_with('\'') && trimmed.ends_with('\'') && trimmed.len() >= 2 {
        return Ok(trimmed[1..trimmed.len() - 1].to_string());
    }
    Ok(trimmed.to_string())
}

pub(crate) fn parse_string_list_value(raw: &str, ctx: &str) -> Result<Vec<String>, String> {
    let trimmed = raw.trim();
    if !trimmed.starts_with('[') || !trimmed.ends_with(']') {
        return Err(format!("expected TOML array for {ctx}, got '{trimmed}'"));
    }
    let inner = trimmed[1..trimmed.len() - 1].trim();
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
        if in_quotes && ch == '\\' {
            current.push(ch);
            escaped = true;
            continue;
        }
        if ch == '"' {
            in_quotes = !in_quotes;
            current.push(ch);
            continue;
        }
        if !in_quotes && ch == ',' {
            let token = current.trim();
            if !token.is_empty() {
                items.push(parse_toml_scalar_string(token, 0)?);
            }
            current.clear();
            continue;
        }
        current.push(ch);
    }
    let tail = current.trim();
    if !tail.is_empty() {
        items.push(parse_toml_scalar_string(tail, 0)?);
    }
    Ok(items)
}
