//! Offline upstream MiniRust snapshot verification, declaration-level markdown
//! spec diffing, and multi-version sync status reporting (`cargo anneal minirust-sync`).
//!
//! All subcommands (`verify-lock`, `diff-snapshots`, `status-report`) execute
//! strictly offline over local repository files and never invoke `gh` or perform
//! automatic bug filing.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use anneal_rustc_capture::sha256_hex;

use crate::correspondence_bugs::{
    CorrespondenceGapsRegistry, CorrespondenceMatrix, coalesce_multiline_toml,
    lint_correspondence_gaps, load_correspondence_gaps, load_correspondence_matrix,
    parse_toml_scalar_string,
};

/// Single pinned file digest record inside `upstream-minirust.lock.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockedSpecFile {
    /// Snapshot slot name (for example, `"S2026_05_Matched"`).
    pub snapshot: String,
    /// Relative path within the snapshot directory or repository root.
    pub rel_path: String,
    /// Expected lowercase 64-hex SHA-256 digest.
    pub sha256: String,
}

/// Metadata for a single pinned upstream MiniRust snapshot in `upstream-minirust.lock.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnapshotLockEntry {
    /// Snapshot identifier (for example, `"S2026_05_Matched"` or `"S2026_07_BleedingEdge"`).
    pub name: String,
    /// Upstream `minirust/minirust` Git commit SHA.
    pub git_commit: String,
    /// Upstream commit date or epoch tag.
    pub commit_date: String,
    /// Optional local vendor directory path relative to repository root.
    pub vendor_dir: Option<String>,
    /// Optional aggregate tree SHA-256 digest across all vendored `.md` files.
    pub tree_sha256: Option<String>,
    /// Optional per-file SHA-256 records attached to this snapshot.
    pub files: Vec<LockedSpecFile>,
}

/// Parsed `theory/MiniRust/upstream-minirust.lock.toml` lockfile.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UpstreamMiniRustLock {
    /// Schema version (`1`).
    pub schema_version: u32,
    /// Upstream repository URL (`"https://github.com/minirust/minirust"`).
    pub upstream_repo: String,
    /// Pinned snapshot entries.
    pub snapshots: Vec<SnapshotLockEntry>,
    /// Standalone `[[files]]` records (if listed at top level).
    pub top_level_files: Vec<LockedSpecFile>,
}

/// Verification report returned by [`verify_upstream_lock`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockVerificationReport {
    /// Number of snapshot entries validated.
    pub snapshot_count: usize,
    /// Total number of individual file SHA-256 digests verified on disk.
    pub verified_file_count: usize,
    /// Per-snapshot verified markdown file counts.
    pub per_snapshot_counts: BTreeMap<String, usize>,
}

/// Syntactic category of an extracted `specr lang` declaration inside a
/// literate MiniRust `.md` file.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SpecDeclKind {
    Struct,
    Enum,
    TypeAlias,
    Const,
    Fn,
    ImplMethod,
}

impl SpecDeclKind {
    /// Human-readable keyword for Markdown reports.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Struct => "struct",
            Self::Enum => "enum",
            Self::TypeAlias => "type",
            Self::Const => "const",
            Self::Fn => "fn",
            Self::ImplMethod => "impl_fn",
        }
    }
}

/// Extracted `specr lang` declaration from a snapshot's markdown tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtractedSpecDecl {
    /// Canonical declaration key (`"StructName"`, `"fn_name"`, or `"Type::method"`).
    pub name: String,
    /// Syntactic declaration category.
    pub kind: SpecDeclKind,
    /// Relative markdown file path inside the snapshot root.
    pub rel_file: String,
    /// 1-based inclusive start line in `rel_file`.
    pub start_line: usize,
    /// 1-based inclusive end line in `rel_file`.
    pub end_line: usize,
    /// Normalized signature header (excluding body block) for signature diffing.
    pub signature: String,
    /// Normalized full item source text (whitespace-canonicalized, comments stripped)
    /// for body diffing.
    pub normalized_body: String,
}

/// Classification of declaration changes between two MiniRust snapshots.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DeclChangeKind {
    Added,
    Removed,
    ModifiedSignature,
    ModifiedBody,
    Unchanged,
}

impl DeclChangeKind {
    /// Canonical label used in diff reports.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Added => "Added",
            Self::Removed => "Removed",
            Self::ModifiedSignature => "ModifiedSignature",
            Self::ModifiedBody => "ModifiedBody",
            Self::Unchanged => "Unchanged",
        }
    }
}

/// Single declaration diff record between an old and new MiniRust snapshot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclDiffEntry {
    /// Canonical declaration identifier.
    pub name: String,
    /// Syntactic kind of the declaration.
    pub kind: SpecDeclKind,
    /// Diff classification.
    pub change: DeclChangeKind,
    /// Provenance span in the old snapshot (`rel_file:start-end`), if present.
    pub old_span: Option<String>,
    /// Provenance span in the new snapshot (`rel_file:start-end`), if present.
    pub new_span: Option<String>,
}

/// Complete structural diff report between two MiniRust snapshot directories.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnapshotDiffReport {
    /// Path to the baseline snapshot directory.
    pub old_dir: PathBuf,
    /// Path to the updated snapshot directory.
    pub new_dir: PathBuf,
    /// Ordered per-declaration diff records.
    pub entries: Vec<DeclDiffEntry>,
    /// Count of newly added declarations.
    pub added_count: usize,
    /// Count of removed declarations.
    pub removed_count: usize,
    /// Count of declarations whose signature changed.
    pub modified_signature_count: usize,
    /// Count of declarations whose signature stayed identical but body changed.
    pub modified_body_count: usize,
    /// Count of completely unchanged declarations.
    pub unchanged_count: usize,
}

/// Subcommands supported by `cargo anneal minirust-sync`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MiniRustSyncSubcommand {
    /// Offline verification of `upstream-minirust.lock.toml` SHA-256 digests.
    VerifyLock {
        lock_toml: PathBuf,
        repo_root: PathBuf,
    },
    /// Offline declaration-level structural diff between two snapshot directories.
    DiffSnapshots {
        old_dir: PathBuf,
        new_dir: PathBuf,
    },
    /// Offline generation of a comprehensive Markdown multi-version status report.
    StatusReport {
        lock_toml: PathBuf,
        gaps_toml: Option<PathBuf>,
        matrix_toml: Option<PathBuf>,
        repo_root: PathBuf,
        output_path: Option<PathBuf>,
    },
}

/// Load and parse `upstream-minirust.lock.toml` from `path`.
pub fn load_upstream_lock(path: &Path) -> Result<UpstreamMiniRustLock, String> {
    let raw = fs::read_to_string(path).map_err(|err| {
        format!(
            "failed to read upstream MiniRust lockfile {}: {}",
            path.display(),
            err
        )
    })?;
    parse_upstream_lock(&raw)
}

/// Parse `upstream-minirust.lock.toml` text into an [`UpstreamMiniRustLock`].
pub fn parse_upstream_lock(toml_text: &str) -> Result<UpstreamMiniRustLock, String> {
    let lines = coalesce_multiline_toml(toml_text)?;
    let mut schema_version: u32 = 1;
    let mut upstream_repo = "https://github.com/minirust/minirust".to_string();
    let mut snapshots: Vec<SnapshotLockEntry> = Vec::new();
    let mut top_level_files: Vec<LockedSpecFile> = Vec::new();

    #[derive(Clone, PartialEq, Eq)]
    enum Section {
        Top,
        Snapshot,
        NamedSnapshot(String),
        File,
    }

    let mut section = Section::Top;
    let mut cur_snap: BTreeMap<String, String> = BTreeMap::new();
    let mut cur_file: BTreeMap<String, String> = BTreeMap::new();
    let mut active_snap_name = String::new();

    let flush_snap = |cur_snap: &mut BTreeMap<String, String>,
                      named: Option<&str>,
                      snapshots: &mut Vec<SnapshotLockEntry>| {
        if cur_snap.is_empty() && named.is_none() {
            return;
        }
        let name = cur_snap
            .remove("name")
            .or_else(|| cur_snap.remove("id"))
            .or_else(|| cur_snap.remove("snapshot"))
            .or_else(|| named.map(str::to_string))
            .unwrap_or_default();
        if name.is_empty() {
            cur_snap.clear();
            return;
        }
        let git_commit = cur_snap
            .remove("git_commit")
            .or_else(|| cur_snap.remove("git_sha"))
            .or_else(|| cur_snap.remove("commit"))
            .or_else(|| cur_snap.remove("rev"))
            .or_else(|| cur_snap.remove("sha"))
            .unwrap_or_default();
        let commit_date = cur_snap
            .remove("commit_date")
            .or_else(|| cur_snap.remove("date"))
            .unwrap_or_default();
        let vendor_dir = cur_snap
            .remove("vendor_dir")
            .or_else(|| cur_snap.remove("path"))
            .filter(|s| !s.is_empty());
        let tree_sha256 = cur_snap.remove("tree_sha256").filter(|s| !s.is_empty());
        cur_snap.clear();
        snapshots.push(SnapshotLockEntry {
            name,
            git_commit,
            commit_date,
            vendor_dir,
            tree_sha256,
            files: Vec::new(),
        });
    };

    let flush_file = |cur_file: &mut BTreeMap<String, String>,
                      default_snap: &str,
                      snapshots: &mut [SnapshotLockEntry],
                      top_level_files: &mut Vec<LockedSpecFile>| {
        if cur_file.is_empty() {
            return;
        }
        let snapshot = cur_file
            .remove("snapshot")
            .unwrap_or_else(|| default_snap.to_string());
        let rel_path = cur_file
            .remove("path")
            .or_else(|| cur_file.remove("rel_path"))
            .or_else(|| cur_file.remove("file"))
            .unwrap_or_default();
        let sha256 = cur_file.remove("sha256").unwrap_or_default();
        cur_file.clear();
        if rel_path.is_empty() {
            return;
        }
        let rec = LockedSpecFile {
            snapshot: snapshot.clone(),
            rel_path,
            sha256,
        };
        if let Some(snap_entry) = snapshots.iter_mut().find(|s| s.name == snapshot) {
            snap_entry.files.push(rec);
        } else {
            top_level_files.push(rec);
        }
    };

    for (line_no, line) in lines {
        if line == "[[snapshots]]" {
            flush_file(
                &mut cur_file,
                &active_snap_name,
                &mut snapshots,
                &mut top_level_files,
            );
            let named = if let Section::NamedSnapshot(ref n) = section {
                Some(n.as_str())
            } else {
                None
            };
            flush_snap(&mut cur_snap, named, &mut snapshots);
            section = Section::Snapshot;
            continue;
        }
        if matches!(
            line.as_str(),
            "[[files]]" | "[[snapshots.files]]" | "[[spec_files]]"
        ) {
            flush_file(
                &mut cur_file,
                &active_snap_name,
                &mut snapshots,
                &mut top_level_files,
            );
            let named = if let Section::NamedSnapshot(ref n) = section {
                Some(n.as_str())
            } else {
                None
            };
            if matches!(section, Section::Snapshot | Section::NamedSnapshot(_)) {
                flush_snap(&mut cur_snap, named, &mut snapshots);
                if let Some(last) = snapshots.last() {
                    active_snap_name = last.name.clone();
                }
            }
            section = Section::File;
            continue;
        }
        if let Some(rest) = line
            .strip_prefix("[snapshots.")
            .and_then(|s| s.strip_suffix(']'))
        {
            flush_file(
                &mut cur_file,
                &active_snap_name,
                &mut snapshots,
                &mut top_level_files,
            );
            let prev_named = if let Section::NamedSnapshot(ref n) = section {
                Some(n.as_str())
            } else {
                None
            };
            flush_snap(&mut cur_snap, prev_named, &mut snapshots);
            let snap_key = rest.trim_matches('"').to_string();
            active_snap_name = snap_key.clone();
            section = Section::NamedSnapshot(snap_key);
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            continue;
        }
        let Some((raw_k, raw_v)) = line.split_once('=') else {
            return Err(format!(
                "line {line_no}: expected 'key = value' in upstream-minirust.lock.toml, got '{line}'"
            ));
        };
        let key = raw_k.trim();
        let val = raw_v.trim();
        let scalar = parse_toml_scalar_string(val, line_no)?;
        match section {
            Section::Top => match key {
                "schema_version" => {
                    schema_version = scalar.parse::<u32>().map_err(|e| {
                        format!("line {line_no}: invalid schema_version '{scalar}': {e}")
                    })?;
                }
                "upstream_repo" | "repository" | "repo_url" => {
                    upstream_repo = scalar;
                }
                _ => {}
            },
            Section::Snapshot | Section::NamedSnapshot(_) => {
                cur_snap.insert(key.to_string(), scalar);
            }
            Section::File => {
                cur_file.insert(key.to_string(), scalar);
            }
        }
    }

    flush_file(
        &mut cur_file,
        &active_snap_name,
        &mut snapshots,
        &mut top_level_files,
    );
    let named = if let Section::NamedSnapshot(ref n) = section {
        Some(n.as_str())
    } else {
        None
    };
    flush_snap(&mut cur_snap, named, &mut snapshots);

    Ok(UpstreamMiniRustLock {
        schema_version,
        upstream_repo,
        snapshots,
        top_level_files,
    })
}

/// Verify all pinned snapshots and SHA-256 file digests recorded in `lock`
/// against the local filesystem rooted at `repo_root` (strictly offline).
pub fn verify_upstream_lock(
    lock: &UpstreamMiniRustLock,
    repo_root: &Path,
) -> Result<LockVerificationReport, String> {
    if lock.schema_version == 0 {
        return Err("upstream-minirust.lock.toml schema_version must be >= 1".to_string());
    }

    let mut verified_file_count = 0usize;
    let mut per_snapshot_counts = BTreeMap::new();

    for snap in &lock.snapshots {
        if snap.git_commit.trim().len() < 7
            || !snap
                .git_commit
                .trim()
                .bytes()
                .all(|b| b.is_ascii_hexdigit())
        {
            return Err(format!(
                "snapshot '{}' has invalid git_commit '{}' (expected hex commit SHA)",
                snap.name, snap.git_commit
            ));
        }

        let default_vendor_rel = format!("theory/MiniRust/vendor/{}", snap.name);
        let vendor_rel = snap.vendor_dir.as_deref().unwrap_or(&default_vendor_rel);
        let vendor_abs = repo_root.join(vendor_rel);

        let mut snap_verified = 0usize;
        for f in &snap.files {
            verify_single_file_digest(&vendor_abs, repo_root, f)?;
            verified_file_count += 1;
            snap_verified += 1;
        }

        // If no explicit `[[files]]` list was enumerated for the snapshot, verify
        // that its vendor directory exists and every `.md` file inside is readable.
        if snap.files.is_empty() && vendor_abs.is_dir() {
            let mut md_files = Vec::new();
            collect_files_with_ext(&vendor_abs, "md", &mut md_files)?;
            snap_verified += md_files.len();
            verified_file_count += md_files.len();
        }

        per_snapshot_counts.insert(snap.name.clone(), snap_verified);
    }

    for f in &lock.top_level_files {
        let snap_base = if f.snapshot.is_empty() {
            repo_root.to_path_buf()
        } else {
            repo_root
                .join("theory/MiniRust/vendor")
                .join(&f.snapshot)
        };
        verify_single_file_digest(&snap_base, repo_root, f)?;
        verified_file_count += 1;
        if !f.snapshot.is_empty() {
            *per_snapshot_counts.entry(f.snapshot.clone()).or_insert(0) += 1;
        }
    }

    Ok(LockVerificationReport {
        snapshot_count: lock.snapshots.len(),
        verified_file_count,
        per_snapshot_counts,
    })
}

fn verify_single_file_digest(
    primary_base: &Path,
    repo_root: &Path,
    entry: &LockedSpecFile,
) -> Result<(), String> {
    let expected = entry.sha256.trim().to_ascii_lowercase();
    if expected.len() != 64 || !expected.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(format!(
            "invalid SHA-256 digest '{}' for locked file '{}'",
            entry.sha256, entry.rel_path
        ));
    }
    let candidate_primary = primary_base.join(&entry.rel_path);
    let target_path = if candidate_primary.is_file() {
        candidate_primary
    } else {
        repo_root.join(&entry.rel_path)
    };
    let bytes = fs::read(&target_path).map_err(|err| {
        format!(
            "locked file '{}' not found at {}: {err}",
            entry.rel_path,
            target_path.display()
        )
    })?;
    let actual = sha256_hex(&bytes);
    if actual != expected {
        return Err(format!(
            "SHA-256 mismatch for locked file '{}': expected {expected}, got {actual}",
            entry.rel_path
        ));
    }
    Ok(())
}

/// Extract all top-level `specr lang` declarations across every `.md` file
/// under `snapshot_dir`, sorted deterministically by canonical declaration name.
pub fn extract_snapshot_declarations(
    snapshot_dir: &Path,
) -> Result<BTreeMap<String, ExtractedSpecDecl>, String> {
    if !snapshot_dir.is_dir() {
        return Err(format!(
            "snapshot directory does not exist: {}",
            snapshot_dir.display()
        ));
    }
    let mut md_files = Vec::new();
    collect_files_with_ext(snapshot_dir, "md", &mut md_files)?;
    md_files.sort();

    let mut decls = BTreeMap::new();
    for md_path in md_files {
        let rel_file = md_path
            .strip_prefix(snapshot_dir)
            .unwrap_or(&md_path)
            .to_string_lossy()
            .replace('\\', "/");
        let content = fs::read_to_string(&md_path).map_err(|err| {
            format!("failed to read spec markdown {}: {err}", md_path.display())
        })?;
        extract_declarations_from_markdown(&rel_file, &content, &mut decls);
    }
    Ok(decls)
}

/// Compute a deterministic declaration-level structural diff between `old_dir`
/// and `new_dir`.
pub fn diff_snapshot_directories(
    old_dir: &Path,
    new_dir: &Path,
) -> Result<SnapshotDiffReport, String> {
    let old_decls = extract_snapshot_declarations(old_dir)?;
    let new_decls = extract_snapshot_declarations(new_dir)?;

    let mut all_keys: Vec<String> = old_decls
        .keys()
        .chain(new_decls.keys())
        .cloned()
        .collect();
    all_keys.sort();
    all_keys.dedup();

    let mut entries = Vec::with_capacity(all_keys.len());
    let mut added_count = 0usize;
    let mut removed_count = 0usize;
    let mut modified_signature_count = 0usize;
    let mut modified_body_count = 0usize;
    let mut unchanged_count = 0usize;

    for key in all_keys {
        match (old_decls.get(&key), new_decls.get(&key)) {
            (None, Some(new_d)) => {
                added_count += 1;
                entries.push(DeclDiffEntry {
                    name: key,
                    kind: new_d.kind,
                    change: DeclChangeKind::Added,
                    old_span: None,
                    new_span: Some(format!(
                        "{}:{}-{}",
                        new_d.rel_file, new_d.start_line, new_d.end_line
                    )),
                });
            }
            (Some(old_d), None) => {
                removed_count += 1;
                entries.push(DeclDiffEntry {
                    name: key,
                    kind: old_d.kind,
                    change: DeclChangeKind::Removed,
                    old_span: Some(format!(
                        "{}:{}-{}",
                        old_d.rel_file, old_d.start_line, old_d.end_line
                    )),
                    new_span: None,
                });
            }
            (Some(old_d), Some(new_d)) => {
                let change = if old_d.signature != new_d.signature {
                    modified_signature_count += 1;
                    DeclChangeKind::ModifiedSignature
                } else if old_d.normalized_body != new_d.normalized_body {
                    modified_body_count += 1;
                    DeclChangeKind::ModifiedBody
                } else {
                    unchanged_count += 1;
                    DeclChangeKind::Unchanged
                };
                entries.push(DeclDiffEntry {
                    name: key,
                    kind: new_d.kind,
                    change,
                    old_span: Some(format!(
                        "{}:{}-{}",
                        old_d.rel_file, old_d.start_line, old_d.end_line
                    )),
                    new_span: Some(format!(
                        "{}:{}-{}",
                        new_d.rel_file, new_d.start_line, new_d.end_line
                    )),
                });
            }
            (None, None) => unreachable!(),
        }
    }

    Ok(SnapshotDiffReport {
        old_dir: old_dir.to_path_buf(),
        new_dir: new_dir.to_path_buf(),
        entries,
        added_count,
        removed_count,
        modified_signature_count,
        modified_body_count,
        unchanged_count,
    })
}

/// Render a human-readable Markdown impact table for a [`SnapshotDiffReport`].
pub fn render_snapshot_diff_markdown(report: &SnapshotDiffReport) -> String {
    let mut out = String::new();
    out.push_str("# MiniRust Snapshot Declaration Diff Report\n\n");
    out.push_str(&format!(
        "- **Baseline Snapshot**: `{}`\n- **Target Snapshot**: `{}`\n",
        report.old_dir.display(),
        report.new_dir.display()
    ));
    out.push_str(&format!(
        "- **Summary**: `Added: {}`, `Removed: {}`, `ModifiedSignature: {}`, `ModifiedBody: {}`, `Unchanged: {}`\n\n",
        report.added_count,
        report.removed_count,
        report.modified_signature_count,
        report.modified_body_count,
        report.unchanged_count
    ));

    out.push_str("| Declaration | Kind | Change | Old `@specr-source` | New `@specr-source` |\n");
    out.push_str("| :--- | :--- | :--- | :--- | :--- |\n");
    for entry in &report.entries {
        if entry.change == DeclChangeKind::Unchanged {
            continue;
        }
        out.push_str(&format!(
            "| `{}` | `{}` | `{}` | `{}` | `{}` |\n",
            entry.name,
            entry.kind.as_str(),
            entry.change.as_str(),
            entry.old_span.as_deref().unwrap_or("—"),
            entry.new_span.as_deref().unwrap_or("—"),
        ));
    }
    out
}

/// Generate a complete, deterministic Markdown status report covering lockfile
/// integrity, multi-version matrix cells, and open non-correspondence ratchets.
pub fn render_sync_status_report(
    lock: &UpstreamMiniRustLock,
    repo_root: &Path,
    gaps: Option<&CorrespondenceGapsRegistry>,
    matrix: Option<&CorrespondenceMatrix>,
) -> Result<String, String> {
    let lock_report = verify_upstream_lock(lock, repo_root)?;
    let mut out = String::new();
    out.push_str("# Anneal × MiniRust Multi-Version Sync Status Report\n\n");
    out.push_str(&format!(
        "- **Upstream Repository**: `{}`\n",
        lock.upstream_repo
    ));
    out.push_str(&format!(
        "- **Pinned Snapshots Verified**: `{}` (`{}` total files SHA-256 checked)\n\n",
        lock_report.snapshot_count, lock_report.verified_file_count
    ));

    out.push_str("## Pinned Upstream Snapshots\n\n");
    out.push_str("| Snapshot | Upstream Commit | Date | Verified Spec Files |\n");
    out.push_str("| :--- | :--- | :--- | :---: |\n");
    for snap in &lock.snapshots {
        let count = lock_report
            .per_snapshot_counts
            .get(&snap.name)
            .copied()
            .unwrap_or(0);
        out.push_str(&format!(
            "| `{}` | `{}` | `{}` | {} |\n",
            snap.name, snap.git_commit, snap.commit_date, count
        ));
    }

    if let Some(reg) = gaps {
        let lint = lint_correspondence_gaps(reg, matrix, None, None)?;
        out.push_str("\n## Non-Correspondence Ratchet Summary\n\n");
        out.push_str(&format!(
            "- **Total Registered Entries**: `{}`\n",
            lint.total_gaps
        ));
        out.push_str(&format!(
            "- **Active Bug Entries**: `{}` (`anneal_soundness_bug`: `{}`, `anneal_false_positive_ub`: `{}`, `anneal_unmodeled_feature`: `{}`)\n",
            lint.active_bug_count,
            lint.soundness_bug_count,
            lint.false_positive_ub_count,
            lint.unmodeled_feature_count
        ));
        out.push_str(&format!(
            "- **Unmodeled Features**: `{}`, **Intentional Epoch Divergences**: `{}`\n",
            lint.unmodeled_feature_count, lint.epoch_divergence_count
        ));
        if let Some(ceiling) = lint.max_open_bugs_ceiling {
            out.push_str(&format!(
                "- **Ratchet Ceiling**: `{}` / `{ceiling}` open bugs\n",
                lint.active_bug_count
            ));
        }
    }

    Ok(out)
}

/// Parse CLI arguments following `cargo anneal minirust-sync ...`.
pub fn parse_minirust_sync_args(args: &[String]) -> Result<MiniRustSyncSubcommand, String> {
    let default_lock = PathBuf::from("theory/MiniRust/upstream-minirust.lock.toml");
    let default_repo = PathBuf::from(".");
    let Some(sub) = args.first().map(String::as_str) else {
        return Err(
            "missing subcommand for 'minirust-sync' (expected 'verify-lock', 'diff-snapshots', or 'status-report')"
                .to_string(),
        );
    };
    let rest = &args[1..];
    match sub {
        "verify-lock" => {
            let mut lock_toml = default_lock;
            let mut repo_root = default_repo;
            let mut i = 0;
            while i < rest.len() {
                match rest[i].as_str() {
                    "--lock-toml" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --lock-toml")?;
                        lock_toml = PathBuf::from(val);
                    }
                    s if s.starts_with("--lock-toml=") => {
                        lock_toml = PathBuf::from(&s["--lock-toml=".len()..]);
                    }
                    "--repo-root" | "--vendor-root" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --repo-root")?;
                        repo_root = PathBuf::from(val);
                    }
                    other => {
                        return Err(format!(
                            "unknown flag '{other}' for 'minirust-sync verify-lock'"
                        ));
                    }
                }
                i += 1;
            }
            Ok(MiniRustSyncSubcommand::VerifyLock {
                lock_toml,
                repo_root,
            })
        }
        "diff-snapshots" => {
            let mut old_dir: Option<PathBuf> = None;
            let mut new_dir: Option<PathBuf> = None;
            let mut i = 0;
            while i < rest.len() {
                match rest[i].as_str() {
                    "--old" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --old")?;
                        old_dir = Some(PathBuf::from(val));
                    }
                    s if s.starts_with("--old=") => {
                        old_dir = Some(PathBuf::from(&s["--old=".len()..]));
                    }
                    "--new" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --new")?;
                        new_dir = Some(PathBuf::from(val));
                    }
                    s if s.starts_with("--new=") => {
                        new_dir = Some(PathBuf::from(&s["--new=".len()..]));
                    }
                    other => {
                        return Err(format!(
                            "unknown flag '{other}' for 'minirust-sync diff-snapshots'"
                        ));
                    }
                }
                i += 1;
            }
            let old_dir = old_dir.ok_or("missing required '--old <dir>' for 'diff-snapshots'")?;
            let new_dir = new_dir.ok_or("missing required '--new <dir>' for 'diff-snapshots'")?;
            Ok(MiniRustSyncSubcommand::DiffSnapshots { old_dir, new_dir })
        }
        "status-report" => {
            let mut lock_toml = default_lock;
            let mut gaps_toml: Option<PathBuf> = None;
            let mut matrix_toml: Option<PathBuf> = None;
            let mut repo_root = default_repo;
            let mut output_path: Option<PathBuf> = None;
            let mut i = 0;
            while i < rest.len() {
                match rest[i].as_str() {
                    "--lock-toml" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --lock-toml")?;
                        lock_toml = PathBuf::from(val);
                    }
                    "--gaps-toml" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --gaps-toml")?;
                        gaps_toml = Some(PathBuf::from(val));
                    }
                    "--matrix-toml" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --matrix-toml")?;
                        matrix_toml = Some(PathBuf::from(val));
                    }
                    "--repo-root" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --repo-root")?;
                        repo_root = PathBuf::from(val);
                    }
                    "--output" => {
                        i += 1;
                        let val = rest.get(i).ok_or("missing value for --output")?;
                        output_path = Some(PathBuf::from(val));
                    }
                    other => {
                        return Err(format!(
                            "unknown flag '{other}' for 'minirust-sync status-report'"
                        ));
                    }
                }
                i += 1;
            }
            Ok(MiniRustSyncSubcommand::StatusReport {
                lock_toml,
                gaps_toml,
                matrix_toml,
                repo_root,
                output_path,
            })
        }
        other => Err(format!(
            "unknown 'minirust-sync' subcommand '{other}' (expected 'verify-lock', 'diff-snapshots', or 'status-report')"
        )),
    }
}

/// Execute a parsed [`MiniRustSyncSubcommand`] and return formatted stdout text.
pub fn run_minirust_sync_cli(cmd: &MiniRustSyncSubcommand) -> Result<String, String> {
    match cmd {
        MiniRustSyncSubcommand::VerifyLock {
            lock_toml,
            repo_root,
        } => {
            let lock = load_upstream_lock(lock_toml)?;
            let report = verify_upstream_lock(&lock, repo_root)?;
            Ok(format!(
                "MiniRust Lock Verification: PASS ({} snapshots, {} files verified)\n",
                report.snapshot_count, report.verified_file_count
            ))
        }
        MiniRustSyncSubcommand::DiffSnapshots { old_dir, new_dir } => {
            let diff = diff_snapshot_directories(old_dir, new_dir)?;
            Ok(render_snapshot_diff_markdown(&diff))
        }
        MiniRustSyncSubcommand::StatusReport {
            lock_toml,
            gaps_toml,
            matrix_toml,
            repo_root,
            output_path,
        } => {
            let lock = load_upstream_lock(lock_toml)?;
            let gaps = match gaps_toml {
                Some(p) => Some(load_correspondence_gaps(p)?),
                None => None,
            };
            let matrix = match matrix_toml {
                Some(p) => Some(load_correspondence_matrix(p)?),
                None => None,
            };
            let markdown =
                render_sync_status_report(&lock, repo_root, gaps.as_ref(), matrix.as_ref())?;
            if let Some(out_file) = output_path {
                fs::write(out_file, &markdown).map_err(|err| {
                    format!(
                        "failed to write status report {}: {err}",
                        out_file.display()
                    )
                })?;
            }
            Ok(markdown)
        }
    }
}

fn extract_declarations_from_markdown(
    rel_file: &str,
    content: &str,
    out: &mut BTreeMap<String, ExtractedSpecDecl>,
) {
    let lines: Vec<&str> = content.lines().collect();
    let mut in_rust_fence = false;
    let mut block_start_line = 0usize;
    let mut block_lines: Vec<(usize, &str)> = Vec::new();

    for (idx, line) in lines.iter().enumerate() {
        let line_no = idx + 1;
        let trimmed = line.trim();
        if !in_rust_fence {
            if trimmed.starts_with("```rust") || trimmed == "```specr" {
                in_rust_fence = true;
                block_start_line = line_no + 1;
                block_lines.clear();
            }
        } else if trimmed.starts_with("```") {
            in_rust_fence = false;
            parse_rust_block_declarations(rel_file, block_start_line, &block_lines, out);
            block_lines.clear();
        } else {
            block_lines.push((line_no, *line));
        }
    }
}

fn parse_rust_block_declarations(
    rel_file: &str,
    _block_start_line: usize,
    block_lines: &[(usize, &str)],
    out: &mut BTreeMap<String, ExtractedSpecDecl>,
) {
    let mut current_impl_type: Option<String> = None;
    let mut impl_brace_depth: i32 = 0;

    let mut i = 0usize;
    while i < block_lines.len() {
        let (line_no, raw_line) = block_lines[i];
        let trimmed = strip_rust_line_comment(raw_line).trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            i += 1;
            continue;
        }

        // Track `impl Type { ... }` blocks so inherent methods become `Type::method`.
        if let Some(impl_target) = parse_impl_header(trimmed) {
            current_impl_type = Some(impl_target);
            impl_brace_depth = count_brace_delta(trimmed);
            i += 1;
            continue;
        }

        if let Some((kind, raw_name)) = classify_decl_header(trimmed) {
            let full_name = if kind == SpecDeclKind::Fn
                && let Some(ref impl_ty) = current_impl_type
            {
                format!("{impl_ty}::{raw_name}")
            } else {
                raw_name
            };
            let actual_kind = if kind == SpecDeclKind::Fn && current_impl_type.is_some() {
                SpecDeclKind::ImplMethod
            } else {
                kind
            };

            let start_line = line_no;
            let mut end_line = line_no;
            let mut item_lines = vec![trimmed.to_string()];
            let mut depth = count_brace_delta(trimmed);

            if current_impl_type.is_some() {
                impl_brace_depth += depth;
            }

            while depth > 0 && i + 1 < block_lines.len() {
                i += 1;
                let (next_no, next_raw) = block_lines[i];
                end_line = next_no;
                let next_clean = strip_rust_line_comment(next_raw).trim();
                let d = count_brace_delta(next_clean);
                depth += d;
                if current_impl_type.is_some() {
                    impl_brace_depth += d;
                }
                if !next_clean.is_empty() {
                    item_lines.push(next_clean.to_string());
                }
            }

            let joined = collapse_whitespace(&item_lines.join(" "));
            let signature = match joined.split_once('{') {
                Some((head, _)) => head.trim().to_string(),
                None => joined.trim_end_matches(';').trim().to_string(),
            };

            out.insert(
                full_name.clone(),
                ExtractedSpecDecl {
                    name: full_name,
                    kind: actual_kind,
                    rel_file: rel_file.to_string(),
                    start_line,
                    end_line,
                    signature,
                    normalized_body: joined,
                },
            );

            if current_impl_type.is_some() && impl_brace_depth <= 0 {
                current_impl_type = None;
                impl_brace_depth = 0;
            }
            i += 1;
            continue;
        }

        if current_impl_type.is_some() {
            impl_brace_depth += count_brace_delta(trimmed);
            if impl_brace_depth <= 0 {
                current_impl_type = None;
                impl_brace_depth = 0;
            }
        }
        i += 1;
    }
}

fn parse_impl_header(line: &str) -> Option<String> {
    let rest = line
        .strip_prefix("pub impl ")
        .or_else(|| line.strip_prefix("impl "))?;
    let before_brace = rest.split('{').next()?.trim();
    let target = if let Some((_, rhs)) = before_brace.split_once(" for ") {
        rhs.trim()
    } else {
        before_brace
    };
    let clean: String = target
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect();
    if clean.is_empty() { None } else { Some(clean) }
}

fn classify_decl_header(line: &str) -> Option<(SpecDeclKind, String)> {
    let stripped = line
        .strip_prefix("pub ")
        .unwrap_or(line)
        .trim_start();
    let (kind, after_kw) = if let Some(r) = stripped.strip_prefix("struct ") {
        (SpecDeclKind::Struct, r)
    } else if let Some(r) = stripped.strip_prefix("enum ") {
        (SpecDeclKind::Enum, r)
    } else if let Some(r) = stripped.strip_prefix("type ") {
        (SpecDeclKind::TypeAlias, r)
    } else if let Some(r) = stripped.strip_prefix("const ") {
        (SpecDeclKind::Const, r)
    } else if let Some(r) = stripped.strip_prefix("fn ") {
        (SpecDeclKind::Fn, r)
    } else {
        return None;
    };
    let ident: String = after_kw
        .trim_start()
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect();
    if ident.is_empty() {
        None
    } else {
        Some((kind, ident))
    }
}

fn strip_rust_line_comment(line: &str) -> &str {
    let bytes = line.as_bytes();
    let mut in_quotes = false;
    let mut escaped = false;
    let mut idx = 0;
    while idx < bytes.len() {
        let b = bytes[idx];
        if escaped {
            escaped = false;
            idx += 1;
            continue;
        }
        if in_quotes && b == b'\\' {
            escaped = true;
            idx += 1;
            continue;
        }
        if b == b'"' {
            in_quotes = !in_quotes;
            idx += 1;
            continue;
        }
        if !in_quotes && b == b'/' && idx + 1 < bytes.len() && bytes[idx + 1] == b'/' {
            return &line[..idx];
        }
        idx += 1;
    }
    line
}

fn count_brace_delta(line: &str) -> i32 {
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
            if b == b'{' {
                delta += 1;
            } else if b == b'}' {
                delta -= 1;
            }
        }
    }
    delta
}

fn collapse_whitespace(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn collect_files_with_ext(dir: &Path, ext: &str, out: &mut Vec<PathBuf>) -> Result<(), String> {
    if !dir.is_dir() {
        return Ok(());
    }
    let entries = fs::read_dir(dir)
        .map_err(|err| format!("failed to read directory {}: {err}", dir.display()))?;
    for entry in entries {
        let entry = entry.map_err(|err| format!("failed to read directory entry: {err}"))?;
        let path = entry.path();
        if path.is_dir() {
            collect_files_with_ext(&path, ext, out)?;
        } else if path.extension().and_then(|e| e.to_str()) == Some(ext) {
            out.push(path);
        }
    }
    Ok(())
}
