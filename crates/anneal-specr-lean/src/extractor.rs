//! Literate Markdown chapter loader, `SUMMARY.md` order resolver, fenced
//! ` ```rust ` block extractor with exact 1-based line ranges, and
//! `upstream-minirust.lock.toml` SHA-256 integrity verifier.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use crate::sha256::{sha256_file, sha256_hex};

/// Semantic chapter domain within the MiniRust specification.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SpecDomain {
    Prelude,
    Syntax,
    Values,
    Types,
    WellFormed,
    MemoryInterface,
    BasicMemory,
    TreeBorrows,
    ConcurrentMemory,
    Step,
    Terminators,
    Intrinsics,
    Machine,
}

impl SpecDomain {
    /// Classifies a chapter relative path (e.g. `spec/mem/tree_borrows/state_machine.md`)
    /// into its canonical MiniRust semantic domain.
    #[must_use]
    pub fn from_chapter_path(rel_path: &str) -> Self {
        let p = rel_path.replace('\\', "/").to_ascii_lowercase();
        if p.contains("tree_borrows") {
            Self::TreeBorrows
        } else if p.contains("mem/basic") {
            Self::BasicMemory
        } else if p.contains("mem/concurrent") || p.contains("step/locks") {
            Self::ConcurrentMemory
        } else if p.contains("mem/interface")
            || p.contains("mem/pointer")
            || p.contains("mem/intptrcast")
            || p.contains("mem/prelude")
        {
            Self::MemoryInterface
        } else if p.contains("step/terminators") {
            Self::Terminators
        } else if p.contains("step/intrinsics") {
            Self::Intrinsics
        } else if p.contains("lang/step") {
            Self::Step
        } else if p.contains("lang/machine") {
            Self::Machine
        } else if p.contains("lang/syntax") {
            Self::Syntax
        } else if p.contains("lang/values") || p.contains("lang/representation") {
            Self::Values
        } else if p.contains("lang/types") {
            Self::Types
        } else if p.contains("well-formed") || p.contains("well_formed") {
            Self::WellFormed
        } else {
            Self::Prelude
        }
    }

    /// Canonical identifier used in generated Lean modules and JSON lockfiles.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Prelude => "Prelude",
            Self::Syntax => "Syntax",
            Self::Values => "Values",
            Self::Types => "Types",
            Self::WellFormed => "WellFormed",
            Self::MemoryInterface => "MemoryInterface",
            Self::BasicMemory => "BasicMemory",
            Self::TreeBorrows => "TreeBorrows",
            Self::ConcurrentMemory => "ConcurrentMemory",
            Self::Step => "Step",
            Self::Terminators => "Terminators",
            Self::Intrinsics => "Intrinsics",
            Self::Machine => "Machine",
        }
    }

    /// Maps each MiniRust domain to its corresponding horizontal slice in `theory/Correspondence/`.
    #[must_use]
    pub const fn correspondence_slice(self) -> &'static str {
        match self {
            Self::Prelude | Self::Syntax | Self::Step => "L1_Scalars",
            Self::Values | Self::Types | Self::WellFormed => "L2_BytesAndLayout",
            Self::MemoryInterface | Self::BasicMemory => "L3_PlacesAndBasicMem",
            Self::TreeBorrows | Self::ConcurrentMemory => "L4_TreeBorrows",
            Self::Terminators | Self::Intrinsics => "L5_ControlAndCalls",
            Self::Machine => "L6_WholeMachine",
        }
    }
}

/// Exact 1-based source location span within an upstream MiniRust markdown file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceSpan {
    pub rel_path: String,
    pub start_line: usize,
    pub end_line: usize,
    pub git_sha: String,
}

impl SourceSpan {
    /// Formats `@specr-source` provenance string `<rel_path>:<start_line>-<end_line> @ <git_sha>`.
    #[must_use]
    pub fn format_provenance(&self) -> String {
        format!("{}:{}-{} @ {}", self.rel_path, self.start_line, self.end_line, self.git_sha)
    }

    /// Formats short `file:start-end` span string.
    #[must_use]
    pub fn format_short(&self) -> String {
        format!("{}:{}-{}", self.rel_path, self.start_line, self.end_line)
    }
}

/// A single fenced ` ```rust ` block extracted from a literate MiniRust markdown file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CodeBlock {
    pub chapter_index: usize,
    pub chapter_rel_path: String,
    pub chapter_title: String,
    pub block_index: usize,
    pub info_string: String,
    pub span: SourceSpan,
    pub source: String,
    pub line_count: usize,
}

/// A parsed MiniRust markdown specification chapter in deterministic order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Chapter {
    pub index: usize,
    pub rel_path: String,
    pub title: String,
    pub domain: SpecDomain,
    pub sha256: String,
    pub byte_len: usize,
    pub total_lines: usize,
    pub blocks: Vec<CodeBlock>,
}

/// Full extraction result across an entire MiniRust snapshot directory.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtractedSnapshot {
    pub snapshot_id: String,
    pub git_sha: String,
    pub root_dir: PathBuf,
    pub chapters: Vec<Chapter>,
    pub total_blocks: usize,
    pub total_rust_lines: usize,
}

/// Parsed representation of a single locked file entry in `upstream-minirust.lock.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockedFileEntry {
    pub path: String,
    pub sha256: String,
    pub bytes: usize,
}

/// Parsed representation of a snapshot entry in `upstream-minirust.lock.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UpstreamSnapshotLock {
    pub id: String,
    pub git_sha: String,
    pub commit_date: String,
    pub commit_title: String,
    pub role: String,
    pub paired_anneal_version: String,
    pub tarball_url: String,
    pub tarball_sha256: String,
    pub vendor_dir: String,
    pub generated_dir: String,
    pub file_count: usize,
    pub files: Vec<LockedFileEntry>,
}

/// Parsed representation of `theory/MiniRust/upstream-minirust.lock.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UpstreamLockFile {
    pub schema_version: u32,
    pub upstream_repo: String,
    pub snapshots: Vec<UpstreamSnapshotLock>,
}

/// Verification report for one snapshot in `upstream-minirust.lock.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedSnapshotSummary {
    pub snapshot_id: String,
    pub git_sha: String,
    pub verified_file_count: usize,
    pub total_verified_bytes: usize,
}

/// Parses `SUMMARY.md` markdown links of the form `[Title](path/to/chapter.md)`
/// in exact document order, normalizing relative paths.
#[must_use]
pub fn parse_summary_md_order(summary_content: &str, summary_prefix: &str) -> Vec<(String, String)> {
    let mut ordered = Vec::new();
    let mut seen = BTreeSet::new();

    for line in summary_content.lines() {
        let mut rest = line;
        while let Some(open_bracket) = rest.find('[') {
            let after_open = &rest[open_bracket + 1..];
            let Some(close_bracket) = after_open.find("](") else {
                break;
            };
            let title = after_open[..close_bracket].trim().to_string();
            let after_paren = &after_open[close_bracket + 2..];
            let Some(close_paren) = after_paren.find(')') else {
                break;
            };
            let raw_target = after_paren[..close_paren].trim();
            rest = &after_paren[close_paren + 1..];

            let target = raw_target.split('#').next().unwrap_or("").trim().trim_start_matches("./");
            if !target.ends_with(".md") {
                continue;
            }
            let full_rel = if summary_prefix.is_empty() || target.starts_with(summary_prefix) {
                target.to_string()
            } else {
                format!("{}/{}", summary_prefix.trim_end_matches('/'), target)
            };
            if seen.insert(full_rel.clone()) {
                ordered.push((full_rel, title));
            }
        }
    }

    ordered
}

/// Recursively collects all `.md` files under `dir`, returning normalized relative paths.
fn collect_markdown_files(base: &Path, current: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries = fs::read_dir(current)
        .map_err(|e| format!("failed to read directory {}: {e}", current.display()))?;
    let mut paths: Vec<PathBuf> = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|e| format!("failed to read dir entry: {e}"))?;
        paths.push(entry.path());
    }
    paths.sort();

    for path in paths {
        if path.is_dir() {
            collect_markdown_files(base, &path, out)?;
        } else if path.extension().and_then(|s| s.to_str()) == Some("md") {
            let rel = path
                .strip_prefix(base)
                .map_err(|e| format!("strip_prefix failed: {e}"))?
                .to_path_buf();
            out.push(rel);
        }
    }
    Ok(())
}

/// Canonical chapter ordering key when ordering chapters not explicitly listed in `SUMMARY.md`:
/// `spec/prelude/*` -> `spec/mem/*` -> `spec/lang/*` -> everything else, then lexicographic path.
fn canonical_chapter_rank(rel_path: &str) -> (u8, &str) {
    if rel_path.starts_with("spec/prelude/") {
        (0, rel_path)
    } else if rel_path.starts_with("spec/mem/prelude") || rel_path.starts_with("spec/mem/interface") {
        (1, rel_path)
    } else if rel_path.starts_with("spec/mem/") {
        (2, rel_path)
    } else if rel_path.starts_with("spec/lang/prelude")
        || rel_path.starts_with("spec/lang/syntax")
        || rel_path.starts_with("spec/lang/values")
        || rel_path.starts_with("spec/lang/types")
    {
        (3, rel_path)
    } else if rel_path.starts_with("spec/lang/") {
        (4, rel_path)
    } else {
        (5, rel_path)
    }
}

/// Extracts the first `# Heading` from a markdown chapter, falling back to its file stem.
fn extract_chapter_title(markdown: &str, rel_path: &str) -> String {
    let mut in_fence = false;
    for line in markdown.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("```") {
            in_fence = !in_fence;
            continue;
        }
        if !in_fence && let Some(rest) = trimmed.strip_prefix("# ") {
            let clean = rest.trim().replace('`', "");
            if !clean.is_empty() {
                return clean;
            }
        }
    }
    Path::new(rel_path)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or(rel_path)
        .to_string()
}

/// Extracts all fenced ` ```rust ` blocks from a single markdown file's text with exact
/// 1-based line ranges matching the raw file lines.
#[must_use]
pub fn extract_rust_blocks_from_str(
    markdown: &str,
    rel_path: &str,
    chapter_index: usize,
    chapter_title: &str,
    git_sha: &str,
) -> Vec<CodeBlock> {
    let lines: Vec<&str> = markdown.lines().collect();
    let mut blocks = Vec::new();
    let mut idx = 0usize;

    while idx < lines.len() {
        let trimmed = lines[idx].trim_start();
        if let Some(after_ticks) = trimmed.strip_prefix("```") {
            let info = after_ticks.trim();
            let first_token = info.split(|c: char| c.is_whitespace() || c == ',').next().unwrap_or("");
            let is_rust = first_token == "rust" || info.is_empty() && false;
            let fence_open_line_1based = idx + 1;
            idx += 1;
            let body_start_idx = idx;

            while idx < lines.len() && !lines[idx].trim_start().starts_with("```") {
                idx += 1;
            }
            let body_end_idx = idx; // exclusive 0-based index of closing ```

            if is_rust {
                let (start_line, end_line, source, line_count) = if body_start_idx < body_end_idx {
                    let slice = &lines[body_start_idx..body_end_idx];
                    (
                        body_start_idx + 1,
                        body_end_idx,
                        slice.join("\n"),
                        slice.len(),
                    )
                } else {
                    (fence_open_line_1based, fence_open_line_1based, String::new(), 0)
                };

                blocks.push(CodeBlock {
                    chapter_index,
                    chapter_rel_path: rel_path.to_string(),
                    chapter_title: chapter_title.to_string(),
                    block_index: blocks.len(),
                    info_string: info.to_string(),
                    span: SourceSpan {
                        rel_path: rel_path.to_string(),
                        start_line,
                        end_line,
                        git_sha: git_sha.to_string(),
                    },
                    source,
                    line_count,
                });
            }

            // Advance past closing fence line if present
            if idx < lines.len() {
                idx += 1;
            }
        } else {
            idx += 1;
        }
    }

    blocks
}

/// Extracts all chapters and fenced ` ```rust ` blocks from a snapshot directory.
pub fn extract_snapshot(
    root_dir: &Path,
    snapshot_id: &str,
    git_sha: &str,
) -> Result<ExtractedSnapshot, String> {
    if !root_dir.exists() {
        return Err(format!("snapshot directory does not exist: {}", root_dir.display()));
    }

    let mut all_md_rel = Vec::new();
    collect_markdown_files(root_dir, root_dir, &mut all_md_rel)?;

    let all_md_strings: Vec<String> = all_md_rel
        .iter()
        .map(|p| p.to_string_lossy().replace('\\', "/"))
        .collect();

    // Honor `SUMMARY.md` ordering when present, then append any remaining `.md` chapters
    // in canonical MiniRust domain order so zero chapters are ever dropped.
    let mut ordered_paths: Vec<(String, Option<String>)> = Vec::new();
    let mut seen: BTreeSet<String> = BTreeSet::new();

    for (summary_rel, prefix) in [("SUMMARY.md", ""), ("spec/SUMMARY.md", "spec")] {
        let summary_path = root_dir.join(summary_rel);
        if summary_path.is_file() {
            let content = fs::read_to_string(&summary_path)
                .map_err(|e| format!("failed reading {}: {e}", summary_path.display()))?;
            for (rel, title) in parse_summary_md_order(&content, prefix) {
                if all_md_strings.iter().any(|s| s == &rel) && seen.insert(rel.clone()) {
                    ordered_paths.push((rel, Some(title)));
                }
            }
        }
    }

    let mut remaining: Vec<String> = all_md_strings
        .into_iter()
        .filter(|rel| rel != "SUMMARY.md" && rel != "spec/SUMMARY.md" && !seen.contains(rel))
        .collect();
    remaining.sort_by(|a, b| canonical_chapter_rank(a).cmp(&canonical_chapter_rank(b)));
    for rel in remaining {
        ordered_paths.push((rel, None));
    }

    let mut chapters = Vec::with_capacity(ordered_paths.len());
    let mut total_blocks = 0usize;
    let mut total_rust_lines = 0usize;

    for (chapter_index, (rel_path, summary_title)) in ordered_paths.into_iter().enumerate() {
        let abs_path = root_dir.join(&rel_path);
        let raw_bytes = fs::read(&abs_path)
            .map_err(|e| format!("failed reading chapter {}: {e}", abs_path.display()))?;
        let sha256 = sha256_hex(&raw_bytes);
        let markdown = String::from_utf8(raw_bytes.clone())
            .map_err(|e| format!("invalid UTF-8 in {}: {e}", abs_path.display()))?;
        let title = summary_title.unwrap_or_else(|| extract_chapter_title(&markdown, &rel_path));
        let blocks =
            extract_rust_blocks_from_str(&markdown, &rel_path, chapter_index, &title, git_sha);
        let rust_lines_in_chapter: usize = blocks.iter().map(|b| b.line_count).sum();
        total_blocks += blocks.len();
        total_rust_lines += rust_lines_in_chapter;

        chapters.push(Chapter {
            index: chapter_index,
            domain: SpecDomain::from_chapter_path(&rel_path),
            rel_path,
            title,
            sha256,
            byte_len: raw_bytes.len(),
            total_lines: markdown.lines().count(),
            blocks,
        });
    }

    Ok(ExtractedSnapshot {
        snapshot_id: snapshot_id.to_string(),
        git_sha: git_sha.to_string(),
        root_dir: root_dir.to_path_buf(),
        chapters,
        total_blocks,
        total_rust_lines,
    })
}

/// Parses `theory/MiniRust/upstream-minirust.lock.toml` into a structured `UpstreamLockFile`.
pub fn parse_upstream_lock_toml(content: &str) -> Result<UpstreamLockFile, String> {
    let mut schema_version = 1u32;
    let mut upstream_repo = String::new();
    let mut snapshots: Vec<UpstreamSnapshotLock> = Vec::new();

    #[derive(PartialEq, Eq)]
    enum Section {
        Root,
        Snapshot,
        SnapshotFile,
    }
    let mut section = Section::Root;

    for (line_idx, raw_line) in content.lines().enumerate() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line == "[[snapshots]]" {
            snapshots.push(UpstreamSnapshotLock {
                id: String::new(),
                git_sha: String::new(),
                commit_date: String::new(),
                commit_title: String::new(),
                role: String::new(),
                paired_anneal_version: String::new(),
                tarball_url: String::new(),
                tarball_sha256: String::new(),
                vendor_dir: String::new(),
                generated_dir: String::new(),
                file_count: 0,
                files: Vec::new(),
            });
            section = Section::Snapshot;
            continue;
        }
        if line == "[[snapshots.files]]" {
            let Some(cur_snap) = snapshots.last_mut() else {
                return Err(format!("line {}: [[snapshots.files]] before [[snapshots]]", line_idx + 1));
            };
            cur_snap.files.push(LockedFileEntry { path: String::new(), sha256: String::new(), bytes: 0 });
            section = Section::SnapshotFile;
            continue;
        }

        let Some((k, v)) = line.split_once('=') else {
            return Err(format!("line {}: expected key = value, got `{line}`", line_idx + 1));
        };
        let key = k.trim();
        let val = parse_toml_scalar_str(v.trim());

        match section {
            Section::Root => match key {
                "schema_version" => {
                    schema_version = val
                        .parse::<u32>()
                        .map_err(|e| format!("invalid schema_version `{val}`: {e}"))?;
                }
                "upstream_repo" => upstream_repo = val,
                _ => {}
            },
            Section::Snapshot => {
                let snap = snapshots.last_mut().expect("snapshot present");
                match key {
                    "id" => snap.id = val,
                    "git_sha" => snap.git_sha = val,
                    "commit_date" => snap.commit_date = val,
                    "commit_title" => snap.commit_title = val,
                    "role" => snap.role = val,
                    "paired_anneal_version" => snap.paired_anneal_version = val,
                    "tarball_url" => snap.tarball_url = val,
                    "tarball_sha256" => snap.tarball_sha256 = val,
                    "vendor_dir" => snap.vendor_dir = val,
                    "generated_dir" => snap.generated_dir = val,
                    "file_count" => {
                        snap.file_count = val
                            .parse::<usize>()
                            .map_err(|e| format!("invalid file_count `{val}`: {e}"))?;
                    }
                    _ => {}
                }
            }
            Section::SnapshotFile => {
                let file_entry = snapshots
                    .last_mut()
                    .and_then(|s| s.files.last_mut())
                    .expect("snapshot file present");
                match key {
                    "path" => file_entry.path = val,
                    "sha256" => file_entry.sha256 = val,
                    "bytes" => {
                        file_entry.bytes = val
                            .parse::<usize>()
                            .map_err(|e| format!("invalid bytes `{val}`: {e}"))?;
                    }
                    _ => {}
                }
            }
        }
    }

    Ok(UpstreamLockFile { schema_version, upstream_repo, snapshots })
}

fn parse_toml_scalar_str(raw: &str) -> String {
    let trimmed = raw.trim();
    if let Some(inner) = trimmed.strip_prefix('"').and_then(|s| s.strip_suffix('"')) {
        inner.replace("\\\"", "\"").replace("\\\\", "\\")
    } else {
        trimmed.to_string()
    }
}

/// Verifies every snapshot and every vendored `.md` file recorded in
/// `theory/MiniRust/upstream-minirust.lock.toml` against on-disk SHA-256 digests and sizes.
pub fn verify_upstream_lock(
    lock_path: &Path,
    repo_root: &Path,
) -> Result<Vec<VerifiedSnapshotSummary>, String> {
    let content = fs::read_to_string(lock_path)
        .map_err(|e| format!("failed to read lockfile {}: {e}", lock_path.display()))?;
    let lock = parse_upstream_lock_toml(&content)?;
    if lock.snapshots.is_empty() {
        return Err("upstream-minirust.lock.toml contains zero snapshots".to_string());
    }

    let mut summaries = Vec::with_capacity(lock.snapshots.len());
    for snap in &lock.snapshots {
        if snap.git_sha.len() != 40 || !snap.git_sha.chars().all(|c| c.is_ascii_hexdigit()) {
            return Err(format!("snapshot `{}` has invalid 40-char git_sha `{}`", snap.id, snap.git_sha));
        }
        if snap.file_count != snap.files.len() {
            return Err(format!(
                "snapshot `{}` declares file_count={} but lists {} file entries",
                snap.id,
                snap.file_count,
                snap.files.len()
            ));
        }

        let vendor_base = repo_root.join(&snap.vendor_dir);
        let mut total_bytes = 0usize;
        for f in &snap.files {
            let abs = vendor_base.join(&f.path);
            let meta = fs::metadata(&abs)
                .map_err(|e| format!("missing vendored file {}: {e}", abs.display()))?;
            let actual_bytes = meta.len() as usize;
            if actual_bytes != f.bytes {
                return Err(format!(
                    "size mismatch for {}: expected {} bytes, got {} bytes",
                    abs.display(),
                    f.bytes,
                    actual_bytes
                ));
            }
            let actual_sha = sha256_file(&abs)
                .map_err(|e| format!("failed hashing {}: {e}", abs.display()))?;
            if actual_sha != f.sha256 {
                return Err(format!(
                    "SHA-256 mismatch for {}: expected {}, got {}",
                    abs.display(),
                    f.sha256,
                    actual_sha
                ));
            }
            total_bytes += actual_bytes;
        }

        summaries.push(VerifiedSnapshotSummary {
            snapshot_id: snap.id.clone(),
            git_sha: snap.git_sha.clone(),
            verified_file_count: snap.files.len(),
            total_verified_bytes: total_bytes,
        });
    }

    Ok(summaries)
}
