//! Structural declaration-level AST diff engine between two upstream MiniRust
//! snapshots (`Added`, `Removed`, `ModifiedSignature`, `ModifiedBody`, `Unchanged`)
//! with automatic mapping to downstream Anneal correspondence slices (`L1`..`L6`).

use std::collections::BTreeSet;

use crate::extractor::{SourceSpan, SpecDomain};
use crate::specr_ast::ItemKind;
use crate::type_env::TypeEnvironment;

/// Formal classification of a single declaration's evolution between two snapshots.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DiffKind {
    /// Declaration was newly introduced in `new_env`.
    Added,
    /// Declaration existed in `old_env` and was deleted in `new_env`.
    Removed,
    /// Declaration exists in both, and its canonical type/function signature changed.
    ModifiedSignature,
    /// Declaration exists in both with identical signature, and its canonical body changed.
    ModifiedBody,
    /// Declaration has identical canonical signature and body (may have shifted line spans).
    Unchanged,
}

impl DiffKind {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Added => "Added",
            Self::Removed => "Removed",
            Self::ModifiedSignature => "ModifiedSignature",
            Self::ModifiedBody => "ModifiedBody",
            Self::Unchanged => "Unchanged",
        }
    }

    /// Whether this diff entry represents a semantic change requiring correspondence review.
    #[must_use]
    pub const fn is_semantic_change(self) -> bool {
        !matches!(self, Self::Unchanged)
    }
}

/// Per-declaration structural diff entry between `old_env` and `new_env`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclDiffEntry {
    pub qualified_name: String,
    pub kind: ItemKind,
    pub domain: SpecDomain,
    pub diff_kind: DiffKind,
    pub old_span: Option<SourceSpan>,
    pub new_span: Option<SourceSpan>,
    pub span_shifted: bool,
    pub old_signature: Option<String>,
    pub new_signature: Option<String>,
    pub old_body_sha256: Option<String>,
    pub new_body_sha256: Option<String>,
    pub affected_slice: &'static str,
    pub summary: String,
}

/// Complete structural diff report between two upstream MiniRust snapshots.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnapshotDiffReport {
    pub old_snapshot_id: String,
    pub old_git_sha: String,
    pub new_snapshot_id: String,
    pub new_git_sha: String,
    pub entries: Vec<DeclDiffEntry>,
    pub added_count: usize,
    pub removed_count: usize,
    pub modified_signature_count: usize,
    pub modified_body_count: usize,
    pub unchanged_count: usize,
    pub cosmetic_span_shift_count: usize,
}

impl SnapshotDiffReport {
    /// Returns all entries with `DiffKind != DiffKind::Unchanged`.
    #[must_use]
    pub fn semantic_changes(&self) -> Vec<&DeclDiffEntry> {
        self.entries.iter().filter(|e| e.diff_kind.is_semantic_change()).collect()
    }

    /// Returns all `Added` declaration diff entries.
    #[must_use]
    pub fn added_items(&self) -> Vec<&DeclDiffEntry> {
        self.entries.iter().filter(|e| e.diff_kind == DiffKind::Added).collect()
    }

    /// Returns all `Removed` declaration diff entries.
    #[must_use]
    pub fn removed_items(&self) -> Vec<&DeclDiffEntry> {
        self.entries.iter().filter(|e| e.diff_kind == DiffKind::Removed).collect()
    }

    /// Returns all `ModifiedSignature` declaration diff entries.
    #[must_use]
    pub fn modified_signature_items(&self) -> Vec<&DeclDiffEntry> {
        self.entries
            .iter()
            .filter(|e| e.diff_kind == DiffKind::ModifiedSignature)
            .collect()
    }

    /// Returns all `ModifiedBody` declaration diff entries.
    #[must_use]
    pub fn modified_body_items(&self) -> Vec<&DeclDiffEntry> {
        self.entries
            .iter()
            .filter(|e| e.diff_kind == DiffKind::ModifiedBody)
            .collect()
    }

    /// Returns the sorted set of horizontal Anneal correspondence slices (`L1`..`L6`)
    /// impacted by at least one semantic declaration change.
    #[must_use]
    pub fn affected_slices(&self) -> Vec<&'static str> {
        let mut slices = BTreeSet::new();
        for e in &self.entries {
            if e.diff_kind.is_semantic_change() {
                slices.insert(e.affected_slice);
            }
        }
        slices.into_iter().collect()
    }

    /// Looks up the diff entry for a specific declaration by `qualified_name`.
    #[must_use]
    pub fn find(&self, qualified_name: &str) -> Option<&DeclDiffEntry> {
        self.entries.iter().find(|e| e.qualified_name == qualified_name)
    }

    /// Renders a deterministic, human-readable Markdown upgrade impact report.
    #[must_use]
    pub fn render_markdown_report(&self) -> String {
        let mut md = String::with_capacity(8192);
        md.push_str("# Upstream MiniRust Structural AST Diff Report\n\n");
        md.push_str(&format!(
            "- **Baseline Snapshot**: `{}` (`{}`)\n",
            self.old_snapshot_id, self.old_git_sha
        ));
        md.push_str(&format!(
            "- **Target Snapshot**: `{}` (`{}`)\n",
            self.new_snapshot_id, self.new_git_sha
        ));
        md.push_str(&format!(
            "- **Summary**: {} Added, {} Removed, {} ModifiedSignature, {} ModifiedBody, {} Unchanged ({} cosmetic span shifts)\n",
            self.added_count,
            self.removed_count,
            self.modified_signature_count,
            self.modified_body_count,
            self.unchanged_count,
            self.cosmetic_span_shift_count
        ));
        md.push_str(&format!(
            "- **Impacted Correspondence Slices**: `{}`\n\n",
            self.affected_slices().join("`, `")
        ));

        md.push_str("| Declaration | Kind | Diff Classification | Domain | Affected Slice | Provenance |\n");
        md.push_str("| :--- | :--- | :--- | :--- | :--- | :--- |\n");

        for entry in self.semantic_changes() {
            let prov = entry
                .new_span
                .as_ref()
                .or(entry.old_span.as_ref())
                .map_or_else(|| "-".to_string(), SourceSpan::format_short);
            md.push_str(&format!(
                "| `{}` | `{}` | `{}` | `{}` | `{}` | `{}` |\n",
                entry.qualified_name,
                entry.kind.as_str(),
                entry.diff_kind.as_str(),
                entry.domain.as_str(),
                entry.affected_slice,
                prov
            ));
        }

        md
    }

    /// Renders a deterministic JSON summary of the diff report.
    #[must_use]
    pub fn render_json_summary(&self) -> String {
        let mut j = String::with_capacity(4096);
        j.push_str("{\n");
        j.push_str(&format!("  \"old_snapshot_id\": \"{}\",\n", self.old_snapshot_id));
        j.push_str(&format!("  \"old_git_sha\": \"{}\",\n", self.old_git_sha));
        j.push_str(&format!("  \"new_snapshot_id\": \"{}\",\n", self.new_snapshot_id));
        j.push_str(&format!("  \"new_git_sha\": \"{}\",\n", self.new_git_sha));
        j.push_str(&format!("  \"added_count\": {},\n", self.added_count));
        j.push_str(&format!("  \"removed_count\": {},\n", self.removed_count));
        j.push_str(&format!(
            "  \"modified_signature_count\": {},\n",
            self.modified_signature_count
        ));
        j.push_str(&format!("  \"modified_body_count\": {},\n", self.modified_body_count));
        j.push_str(&format!("  \"unchanged_count\": {},\n", self.unchanged_count));
        j.push_str(&format!(
            "  \"cosmetic_span_shift_count\": {}\n",
            self.cosmetic_span_shift_count
        ));
        j.push_str("}\n");
        j
    }
}

/// Computes the exact declaration-level structural diff between `old_env` and `new_env`.
#[must_use]
pub fn diff_snapshots(old_env: &TypeEnvironment, new_env: &TypeEnvironment) -> SnapshotDiffReport {
    let mut all_names: BTreeSet<&str> = BTreeSet::new();
    for k in old_env.by_qualified_name.keys() {
        all_names.insert(k.as_str());
    }
    for k in new_env.by_qualified_name.keys() {
        all_names.insert(k.as_str());
    }

    let mut entries = Vec::with_capacity(all_names.len());
    let mut added_count = 0usize;
    let mut removed_count = 0usize;
    let mut modified_signature_count = 0usize;
    let mut modified_body_count = 0usize;
    let mut unchanged_count = 0usize;
    let mut cosmetic_span_shift_count = 0usize;

    for qname in all_names {
        let old_item = old_env.get(qname);
        let new_item = new_env.get(qname);

        match (old_item, new_item) {
            (None, Some(n)) => {
                added_count += 1;
                entries.push(DeclDiffEntry {
                    qualified_name: qname.to_string(),
                    kind: n.kind,
                    domain: n.domain,
                    diff_kind: DiffKind::Added,
                    old_span: None,
                    new_span: Some(n.span.clone()),
                    span_shifted: false,
                    old_signature: None,
                    new_signature: Some(n.signature_canonical.clone()),
                    old_body_sha256: None,
                    new_body_sha256: Some(n.body_sha256.clone()),
                    affected_slice: n.domain.correspondence_slice(),
                    summary: format!("Added {} `{}` in {}", n.kind.as_str(), qname, n.span.format_short()),
                });
            }
            (Some(o), None) => {
                removed_count += 1;
                entries.push(DeclDiffEntry {
                    qualified_name: qname.to_string(),
                    kind: o.kind,
                    domain: o.domain,
                    diff_kind: DiffKind::Removed,
                    old_span: Some(o.span.clone()),
                    new_span: None,
                    span_shifted: false,
                    old_signature: Some(o.signature_canonical.clone()),
                    new_signature: None,
                    old_body_sha256: Some(o.body_sha256.clone()),
                    new_body_sha256: None,
                    affected_slice: o.domain.correspondence_slice(),
                    summary: format!(
                        "Removed {} `{}` from {}",
                        o.kind.as_str(),
                        qname,
                        o.span.format_short()
                    ),
                });
            }
            (Some(o), Some(n)) => {
                let span_shifted =
                    o.span.start_line != n.span.start_line || o.span.end_line != n.span.end_line;
                let diff_kind = if o.signature_sha256 != n.signature_sha256 {
                    modified_signature_count += 1;
                    DiffKind::ModifiedSignature
                } else if o.body_sha256 != n.body_sha256 {
                    modified_body_count += 1;
                    DiffKind::ModifiedBody
                } else {
                    unchanged_count += 1;
                    if span_shifted {
                        cosmetic_span_shift_count += 1;
                    }
                    DiffKind::Unchanged
                };

                let summary = match diff_kind {
                    DiffKind::ModifiedSignature => format!(
                        "Signature changed on {} `{}` ({} -> {})",
                        n.kind.as_str(),
                        qname,
                        o.span.format_short(),
                        n.span.format_short()
                    ),
                    DiffKind::ModifiedBody => format!(
                        "Body changed on {} `{}` ({} -> {})",
                        n.kind.as_str(),
                        qname,
                        o.span.format_short(),
                        n.span.format_short()
                    ),
                    DiffKind::Unchanged => format!("Unchanged `{qname}`"),
                    DiffKind::Added | DiffKind::Removed => unreachable!(),
                };

                entries.push(DeclDiffEntry {
                    qualified_name: qname.to_string(),
                    kind: n.kind,
                    domain: n.domain,
                    diff_kind,
                    old_span: Some(o.span.clone()),
                    new_span: Some(n.span.clone()),
                    span_shifted,
                    old_signature: Some(o.signature_canonical.clone()),
                    new_signature: Some(n.signature_canonical.clone()),
                    old_body_sha256: Some(o.body_sha256.clone()),
                    new_body_sha256: Some(n.body_sha256.clone()),
                    affected_slice: n.domain.correspondence_slice(),
                    summary,
                });
            }
            (None, None) => unreachable!(),
        }
    }

    SnapshotDiffReport {
        old_snapshot_id: old_env.snapshot_id.clone(),
        old_git_sha: old_env.git_sha.clone(),
        new_snapshot_id: new_env.snapshot_id.clone(),
        new_git_sha: new_env.git_sha.clone(),
        entries,
        added_count,
        removed_count,
        modified_signature_count,
        modified_body_count,
        unchanged_count,
        cosmetic_span_shift_count,
    }
}
