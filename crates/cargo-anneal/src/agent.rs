//! Specification locking, anti-cheating verification gates, and agent context
//! rendering for autonomous Lean 4 proof construction.
//!
//! When an AI agent is tasked with discharging Anneal verification obligations,
//! its authority is restricted to authoring proof terms under
//! `anneal/proofs/Proof/<Crate>/<Item>.lean`. This module provides three
//! mechanisms that enforce that boundary and supply the context an agent needs:
//!
//! 1. **Specification and assumption locking (`lock_workspace_specs`)**:
//!    records SHA-256 digests of all captured MIR modules, every authored
//!    specification override under `anneal/proofs/Specs/`, and every authored
//!    assumption module under `anneal/proofs/Assumptions/` in
//!    `.anneal/spec-lock.json`.
//! 2. **Pre-build lock verification (`verify_spec_lock`,
//!    `check_specs_non_vacuous`)**: rejects verification runs before invoking
//!    Lake if captured items were filtered or altered, if any `Specs` or
//!    `Assumptions` file was added, removed, or modified relative to
//!    `.anneal/spec-lock.json`, or if a `Specs` file introduces a vacuous
//!    `False` precondition.
//! 3. **Structured agent context (`render_agent_context`)**: assembles a
//!    Markdown report containing each target item's obligation module, active
//!    specification override, lowered MIR body, and starter proof template.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use anneal_rustc_capture::manifest::{escape_json, sha256_hex};
use anneal_rustc_capture::{CapturedItemKind, CapturedTarget, UnitTargetRecord};

use crate::obligations::{
    SubjectObligationBundle, group_subject_obligations, render_obligations_module_with_options,
    render_proof_template_with_options,
};
use crate::scaffold::detect_authored_item_modules;

/// Schema identifier stored in `.anneal/spec-lock.json`.
pub const SPEC_LOCK_SCHEMA_V1: &str = "anneal.spec-lock.v1";

/// Default workspace-relative path to the specification lock manifest.
pub const SPEC_LOCK_REL_PATH: &str = ".anneal/spec-lock.json";

/// Locked metadata for a single captured compilation-unit target record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockedUnitRecord {
    /// Canonical Rust `DefId` path of the captured item.
    pub def_id: String,
    /// Dotted Lean module name (for example, `"Mir.MyCrate.foo"`).
    pub lean_module_name: String,
    /// Stable role tag (`"subject"`, `"inline_spec_requires"`, etc.).
    pub item_kind: String,
    /// Subject `def_id` to which a companion specification item attaches.
    pub associated_subject_def_id: Option<String>,
    /// Lowercase hex SHA-256 digest of the generated `Mir/<Item>.lean` file.
    pub mir_module_sha256: String,
}

impl LockedUnitRecord {
    /// Project a `UnitTargetRecord` into its locked manifest representation.
    pub fn from_unit_record(record: &UnitTargetRecord) -> Self {
        Self {
            def_id: record.target.def_id.clone(),
            lean_module_name: record.lean_module_name.clone(),
            item_kind: record.item_kind.as_str().to_string(),
            associated_subject_def_id: record.associated_subject_def_id.clone(),
            mir_module_sha256: record.target.mir_module_sha256.clone(),
        }
    }
}

/// Workspace-relative path and SHA-256 digest of a locked `.lean` source file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockedFileDigest {
    /// Forward-slash-normalized path relative to the workspace root.
    pub rel_path: String,
    /// Lowercase hex SHA-256 digest of the file's byte contents.
    pub sha256: String,
}

/// Deterministic manifest written to `.anneal/spec-lock.json` by
/// `cargo anneal lock-specs` and verified by `cargo anneal agent-verify` (or
/// `cargo anneal verify --locked-specs`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecLockManifest {
    /// Schema identifier (`"anneal.spec-lock.v1"`).
    pub schema: String,
    /// Captured subject and companion records sorted deterministically by
    /// `def_id`.
    pub locked_records: Vec<LockedUnitRecord>,
    /// Digests of all `.lean` files under `anneal/proofs/Specs/`, sorted by
    /// `rel_path`.
    pub locked_specs_files: Vec<LockedFileDigest>,
    /// Digests of all `.lean` files under `anneal/proofs/Assumptions/`, sorted
    /// by `rel_path`.
    pub locked_assumptions_files: Vec<LockedFileDigest>,
    /// Subject `def_id`s whose Rust implementation bodies (and only their
    /// `subject` MIR digests, never their `#[spec]` companions or `Specs/**`)
    /// are explicitly designated mutable via `lock-specs --allow-impl-edit`.
    pub mutable_subjects: Vec<String>,
}

impl SpecLockManifest {
    /// Current schema version string for `.anneal/spec-lock.json`.
    pub const SCHEMA_VERSION: &'static str = SPEC_LOCK_SCHEMA_V1;

    /// Serialize this manifest to deterministic, human-readable JSON.
    pub fn to_json_string(&self) -> String {
        serialize_spec_lock_manifest(self)
    }

    /// Parse a `SpecLockManifest` from its JSON text representation.
    pub fn from_json_str(input: &str) -> Result<Self, String> {
        parse_spec_lock_manifest(input)
    }
}

/// Serialize a `SpecLockManifest` to deterministic JSON without external crate
/// dependencies.
pub fn serialize_spec_lock_manifest(manifest: &SpecLockManifest) -> String {
    let mut out = String::from("{\n");
    out.push_str(&format!(
        "  \"schema\": \"{}\",\n",
        escape_json(&manifest.schema)
    ));

    if !manifest.mutable_subjects.is_empty() {
        out.push_str("  \"mutable_subjects\": [\n");
        for (i, subj) in manifest.mutable_subjects.iter().enumerate() {
            let comma = if i + 1 < manifest.mutable_subjects.len() {
                ","
            } else {
                ""
            };
            out.push_str(&format!("    \"{}\"{comma}\n", escape_json(subj)));
        }
        out.push_str("  ],\n");
    }

    out.push_str("  \"locked_records\": [\n");
    for (i, rec) in manifest.locked_records.iter().enumerate() {
        let comma = if i + 1 < manifest.locked_records.len() {
            ","
        } else {
            ""
        };
        out.push_str("    {\n");
        out.push_str(&format!(
            "      \"def_id\": \"{}\",\n",
            escape_json(&rec.def_id)
        ));
        out.push_str(&format!(
            "      \"lean_module_name\": \"{}\",\n",
            escape_json(&rec.lean_module_name)
        ));
        out.push_str(&format!(
            "      \"item_kind\": \"{}\",\n",
            escape_json(&rec.item_kind)
        ));
        match &rec.associated_subject_def_id {
            Some(assoc) => out.push_str(&format!(
                "      \"associated_subject_def_id\": \"{}\",\n",
                escape_json(assoc)
            )),
            None => out.push_str("      \"associated_subject_def_id\": null,\n"),
        }
        out.push_str(&format!(
            "      \"mir_module_sha256\": \"{}\"\n",
            escape_json(&rec.mir_module_sha256)
        ));
        out.push_str(&format!("    }}{comma}\n"));
    }
    out.push_str("  ],\n");

    out.push_str("  \"locked_specs_files\": [\n");
    for (i, entry) in manifest.locked_specs_files.iter().enumerate() {
        let comma = if i + 1 < manifest.locked_specs_files.len() {
            ","
        } else {
            ""
        };
        out.push_str("    {\n");
        out.push_str(&format!(
            "      \"rel_path\": \"{}\",\n",
            escape_json(&entry.rel_path)
        ));
        out.push_str(&format!(
            "      \"sha256\": \"{}\"\n",
            escape_json(&entry.sha256)
        ));
        out.push_str(&format!("    }}{comma}\n"));
    }
    out.push_str("  ],\n");

    out.push_str("  \"locked_assumptions_files\": [\n");
    for (i, entry) in manifest.locked_assumptions_files.iter().enumerate() {
        let comma = if i + 1 < manifest.locked_assumptions_files.len() {
            ","
        } else {
            ""
        };
        out.push_str("    {\n");
        out.push_str(&format!(
            "      \"rel_path\": \"{}\",\n",
            escape_json(&entry.rel_path)
        ));
        out.push_str(&format!(
            "      \"sha256\": \"{}\"\n",
            escape_json(&entry.sha256)
        ));
        out.push_str(&format!("    }}{comma}\n"));
    }
    out.push_str("  ]\n}\n");
    out
}

/// Parse a `SpecLockManifest` from its JSON text representation.
pub fn parse_spec_lock_manifest(input: &str) -> Result<SpecLockManifest, String> {
    let root = parse_json(input)?;
    let obj = root
        .as_object()
        .ok_or_else(|| "expected top-level JSON object in spec-lock manifest".to_string())?;

    let schema = get_string_field(obj, "schema")?;
    let records_val = get_field(obj, "locked_records")
        .ok_or_else(|| "missing field 'locked_records' in spec-lock manifest".to_string())?;
    let records_arr = records_val
        .as_array()
        .ok_or_else(|| "field 'locked_records' must be a JSON array".to_string())?;

    let mut locked_records = Vec::with_capacity(records_arr.len());
    for item in records_arr {
        let item_obj = item
            .as_object()
            .ok_or_else(|| "each entry in 'locked_records' must be a JSON object".to_string())?;
        let def_id = get_string_field(item_obj, "def_id")?;
        let lean_module_name = get_string_field(item_obj, "lean_module_name")?;
        let item_kind = get_string_field(item_obj, "item_kind")?;
        let associated_subject_def_id = match get_field(item_obj, "associated_subject_def_id") {
            None | Some(JsonValue::Null) => None,
            Some(JsonValue::Str(s)) => Some(s.clone()),
            _ => {
                return Err(
                    "field 'associated_subject_def_id' must be a string or null".to_string()
                );
            }
        };
        let mir_module_sha256 = get_string_field(item_obj, "mir_module_sha256")?;
        locked_records.push(LockedUnitRecord {
            def_id,
            lean_module_name,
            item_kind,
            associated_subject_def_id,
            mir_module_sha256,
        });
    }

    let locked_specs_files = parse_digest_list(obj, "locked_specs_files")?;
    let locked_assumptions_files = parse_digest_list(obj, "locked_assumptions_files")?;
    let mutable_subjects = match get_field(obj, "mutable_subjects") {
        None | Some(JsonValue::Null) => Vec::new(),
        Some(val) => {
            let arr = val
                .as_array()
                .ok_or_else(|| "field 'mutable_subjects' must be a JSON array".to_string())?;
            let mut subjs = Vec::with_capacity(arr.len());
            for entry in arr {
                match entry {
                    JsonValue::Str(s) => subjs.push(s.clone()),
                    _ => {
                        return Err(
                            "each entry in 'mutable_subjects' must be a JSON string".to_string()
                        );
                    }
                }
            }
            subjs
        }
    };

    Ok(SpecLockManifest {
        schema,
        locked_records,
        locked_specs_files,
        locked_assumptions_files,
        mutable_subjects,
    })
}

fn parse_digest_list(
    obj: &[(String, JsonValue)],
    key: &str,
) -> Result<Vec<LockedFileDigest>, String> {
    let val =
        get_field(obj, key).ok_or_else(|| format!("missing field '{key}' in spec-lock manifest"))?;
    let arr = val
        .as_array()
        .ok_or_else(|| format!("field '{key}' must be a JSON array"))?;
    let mut out = Vec::with_capacity(arr.len());
    for item in arr {
        let item_obj = item
            .as_object()
            .ok_or_else(|| format!("each entry in '{key}' must be a JSON object"))?;
        let rel_path = get_string_field(item_obj, "rel_path")?;
        let sha256 = get_string_field(item_obj, "sha256")?;
        out.push(LockedFileDigest { rel_path, sha256 });
    }
    Ok(out)
}

/// Scan `anneal/proofs/Specs` and `anneal/proofs/Assumptions` under
/// `workspace_root`, compute SHA-256 digests of all authored `.lean` files and
/// captured `records`, write `.anneal/spec-lock.json`, and return its path.
pub fn lock_workspace_specs(
    workspace_root: &Path,
    records: &[UnitTargetRecord],
) -> Result<PathBuf, String> {
    lock_workspace_specs_with_mutable(workspace_root, records, &[])
}

/// Lock workspace specifications into `.anneal/spec-lock.json` while permitting
/// the designated subject item bodies matching `mutable_patterns` to have their
/// Rust implementation edited (`--allow-impl-edit`). All `Specs/**`,
/// `Assumptions/**`, inline `#[spec]` companions, and non-matching subjects
/// remain strictly SHA-256 locked.
pub fn lock_workspace_specs_with_mutable(
    workspace_root: &Path,
    records: &[UnitTargetRecord],
    mutable_patterns: &[String],
) -> Result<PathBuf, String> {
    let mut mutable_set = std::collections::BTreeSet::new();
    for raw_pat in mutable_patterns {
        for pat in raw_pat.split(',').map(str::trim).filter(|s| !s.is_empty()) {
            let mut matched_any = false;
            for rec in records {
                if rec.item_kind == CapturedItemKind::Subject
                    && (rec.target.def_id.contains(pat) || rec.lean_module_name.contains(pat))
                {
                    mutable_set.insert(rec.target.def_id.clone());
                    matched_any = true;
                }
            }
            if !matched_any {
                return Err(format!(
                    "no verification subject items matched --allow-impl-edit '{pat}'"
                ));
            }
        }
    }

    let locked_records = build_sorted_locked_records(records);
    check_specs_non_vacuous_with_records(workspace_root, records)?;
    let locked_specs_files =
        collect_locked_file_digests(workspace_root, "anneal/proofs/Specs")?;
    let locked_assumptions_files =
        collect_locked_file_digests(workspace_root, "anneal/proofs/Assumptions")?;

    let manifest = SpecLockManifest {
        schema: SPEC_LOCK_SCHEMA_V1.to_string(),
        locked_records,
        locked_specs_files,
        locked_assumptions_files,
        mutable_subjects: mutable_set.into_iter().collect(),
    };

    let dot_anneal = workspace_root.join(".anneal");
    fs::create_dir_all(&dot_anneal).map_err(|err| {
        format!(
            "failed to create directory {}: {}",
            dot_anneal.display(),
            err
        )
    })?;

    let lock_path = workspace_root.join(SPEC_LOCK_REL_PATH);
    let json = manifest.to_json_string();
    fs::write(&lock_path, json).map_err(|err| {
        format!(
            "failed to write spec-lock manifest {}: {}",
            lock_path.display(),
            err
        )
    })?;

    Ok(lock_path)
}

/// Verify that `current_records` and the on-disk `anneal/proofs/Specs/**` and
/// `anneal/proofs/Assumptions/**` trees match `.anneal/spec-lock.json`, and
/// reject vacuous specification overrides.
pub fn verify_spec_lock(
    workspace_root: &Path,
    current_records: &[UnitTargetRecord],
) -> Result<SpecLockManifest, String> {
    let lock_path = workspace_root.join(SPEC_LOCK_REL_PATH);
    if !lock_path.is_file() {
        return Err(format!(
            "missing spec-lock manifest at {}; run `cargo anneal lock-specs` before running locked verification",
            lock_path.display()
        ));
    }

    let raw = fs::read_to_string(&lock_path).map_err(|err| {
        format!(
            "failed to read spec-lock manifest {}: {}",
            lock_path.display(),
            err
        )
    })?;
    let manifest = SpecLockManifest::from_json_str(&raw).map_err(|err| {
        format!(
            "malformed spec-lock manifest {}: {}",
            lock_path.display(),
            err
        )
    })?;

    if manifest.schema != SPEC_LOCK_SCHEMA_V1 {
        return Err(format!(
            "unsupported schema '{}' in {} (expected '{}')",
            manifest.schema,
            lock_path.display(),
            SPEC_LOCK_SCHEMA_V1
        ));
    }

    let current_locked = build_sorted_locked_records(current_records);
    verify_locked_records_match(&manifest.locked_records, &current_locked, &manifest.mutable_subjects)?;

    let current_specs = collect_locked_file_digests(workspace_root, "anneal/proofs/Specs")?;
    verify_file_digests_match(
        "Specs",
        "anneal/proofs/Specs",
        &manifest.locked_specs_files,
        &current_specs,
    )?;

    let current_assumptions =
        collect_locked_file_digests(workspace_root, "anneal/proofs/Assumptions")?;
    verify_file_digests_match(
        "Assumptions",
        "anneal/proofs/Assumptions",
        &manifest.locked_assumptions_files,
        &current_assumptions,
    )?;

    check_specs_non_vacuous_with_records(workspace_root, current_records)?;

    Ok(manifest)
}

fn build_sorted_locked_records(records: &[UnitTargetRecord]) -> Vec<LockedUnitRecord> {
    let mut by_def_id: BTreeMap<String, LockedUnitRecord> = BTreeMap::new();
    for rec in records {
        let locked = LockedUnitRecord::from_unit_record(rec);
        by_def_id.insert(locked.def_id.clone(), locked);
    }
    by_def_id.into_values().collect()
}

fn verify_locked_records_match(
    expected: &[LockedUnitRecord],
    actual: &[LockedUnitRecord],
    mutable_subjects: &[String],
) -> Result<(), String> {
    let expected_map: BTreeMap<&str, &LockedUnitRecord> =
        expected.iter().map(|r| (r.def_id.as_str(), r)).collect();
    let actual_map: BTreeMap<&str, &LockedUnitRecord> =
        actual.iter().map(|r| (r.def_id.as_str(), r)).collect();

    for (def_id, exp) in &expected_map {
        let Some(act) = actual_map.get(def_id) else {
            return Err(format!(
                "spec-lock violation: locked item '{def_id}' is missing from current capture records (narrowing targets with `--filter` or deleting items is forbidden)"
            ));
        };
        if exp.lean_module_name != act.lean_module_name {
            return Err(format!(
                "spec-lock violation: lean_module_name for '{def_id}' changed from '{}' to '{}'",
                exp.lean_module_name, act.lean_module_name
            ));
        }
        if exp.item_kind != act.item_kind {
            return Err(format!(
                "spec-lock violation: item_kind for '{def_id}' changed from '{}' to '{}'",
                exp.item_kind, act.item_kind
            ));
        }
        if exp.associated_subject_def_id != act.associated_subject_def_id {
            return Err(format!(
                "spec-lock violation: associated_subject_def_id for '{def_id}' changed from '{:?}' to '{:?}'",
                exp.associated_subject_def_id, act.associated_subject_def_id
            ));
        }
        let is_designated_mutable = exp.item_kind == "subject"
            && act.item_kind == "subject"
            && mutable_subjects.iter().any(|s| s == def_id);
        if !is_designated_mutable && exp.mir_module_sha256 != act.mir_module_sha256 {
            return Err(format!(
                "spec-lock violation: MIR digest for '{def_id}' changed (expected {}, got {}); Rust source or contract annotations may not be modified while specs are locked",
                exp.mir_module_sha256, act.mir_module_sha256
            ));
        }
    }

    for def_id in actual_map.keys() {
        if !expected_map.contains_key(def_id) {
            return Err(format!(
                "spec-lock violation: unlocked item '{def_id}' appeared in current capture records"
            ));
        }
    }

    Ok(())
}

fn verify_file_digests_match(
    category: &str,
    dir_rel: &str,
    expected: &[LockedFileDigest],
    actual: &[LockedFileDigest],
) -> Result<(), String> {
    let expected_map: BTreeMap<&str, &str> = expected
        .iter()
        .map(|d| (d.rel_path.as_str(), d.sha256.as_str()))
        .collect();
    let actual_map: BTreeMap<&str, &str> = actual
        .iter()
        .map(|d| (d.rel_path.as_str(), d.sha256.as_str()))
        .collect();

    for (path, act_hash) in &actual_map {
        match expected_map.get(path) {
            None => {
                return Err(format!(
                    "spec-lock violation: unlocked {category} file '{path}' was added under {dir_rel}/ after `cargo anneal lock-specs`"
                ));
            }
            Some(exp_hash) if exp_hash != act_hash => {
                return Err(format!(
                    "spec-lock violation: locked {category} file '{path}' was modified (expected SHA-256 {exp_hash}, got {act_hash})"
                ));
            }
            Some(_) => {}
        }
    }

    for path in expected_map.keys() {
        if !actual_map.contains_key(path) {
            return Err(format!(
                "spec-lock violation: locked {category} file '{path}' was removed from {dir_rel}/"
            ));
        }
    }

    Ok(())
}

fn collect_locked_file_digests(
    workspace_root: &Path,
    subdir_rel: &str,
) -> Result<Vec<LockedFileDigest>, String> {
    let root_dir = workspace_root.join(subdir_rel);
    if !root_dir.is_dir() {
        return Ok(Vec::new());
    }

    let mut files = Vec::new();
    collect_lean_files_sorted(&root_dir, &mut files)?;
    files.sort();

    let mut digests = Vec::with_capacity(files.len());
    for file_path in files {
        let rel = file_path
            .strip_prefix(workspace_root)
            .map_err(|err| format!("failed to strip workspace root prefix: {err}"))?;
        let normalized_rel = rel
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/");
        let bytes = fs::read(&file_path).map_err(|err| {
            format!("failed to read {}: {}", file_path.display(), err)
        })?;
        digests.push(LockedFileDigest {
            rel_path: normalized_rel,
            sha256: sha256_hex(&bytes),
        });
    }

    digests.sort_by(|a, b| a.rel_path.cmp(&b.rel_path));
    Ok(digests)
}

fn collect_lean_files_sorted(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    if !dir.is_dir() {
        return Ok(());
    }
    let entries = fs::read_dir(dir)
        .map_err(|err| format!("failed to read directory {}: {}", dir.display(), err))?;
    let mut paths = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|err| format!("failed to read directory entry: {err}"))?;
        paths.push(entry.path());
    }
    paths.sort();
    for path in paths {
        if path.is_dir() {
            collect_lean_files_sorted(&path, out)?;
        } else if path.extension().and_then(|e| e.to_str()) == Some("lean") {
            out.push(path);
        }
    }
    Ok(())
}

/// Scan all `.lean` files under `anneal/proofs/Specs/` (and corresponding
/// `anneal/proofs/Proof/` modules) to reject:
///
/// 1. Vacuous precondition definitions (such as `pre := fun _ => False` or
///    `pre := fun _ _ => False`).
/// 2. Authored `Specs/<Item>.lean` overrides that drop a Rust `#[spec]`
///    `ensures` clause without referencing `rustEnsures`, `defaultPost`,
///    `refineSpec`, `refineStatefulSpec`, `refineSafeSpec`, or
///    `refineSafeStatefulSpec` (unless opted out with
///    `-- @anneal-allow-replace-rust-spec`).
/// 3. Authored `Proof/<Item>.lean` modules that omit `import Specs.<Item>` when
///    `Specs/<Item>.lean` is present on disk.
pub fn check_specs_non_vacuous(workspace_root: &Path) -> Result<(), String> {
    let records = discover_workspace_records(workspace_root);
    check_specs_non_vacuous_with_records(workspace_root, &records)
}

/// Run `check_specs_non_vacuous` using an explicit slice of captured
/// `UnitTargetRecord` entries to identify items with inline Rust `#[spec]`
/// `ensures` companions.
pub fn check_specs_non_vacuous_with_records(
    workspace_root: &Path,
    records: &[UnitTargetRecord],
) -> Result<(), String> {
    let specs_dir = workspace_root.join("anneal/proofs/Specs");
    if !specs_dir.is_dir() {
        return Ok(());
    }

    let bundles = group_subject_obligations(records);
    let bundles_by_rel_path: BTreeMap<PathBuf, &SubjectObligationBundle> = bundles
        .iter()
        .map(|b| (b.item_rel_path.clone(), b))
        .collect();

    let mut files = Vec::new();
    collect_lean_files_sorted(&specs_dir, &mut files)?;
    for file_path in files {
        let content = fs::read_to_string(&file_path)
            .map_err(|err| format!("failed to read {}: {}", file_path.display(), err))?;
        let spec_rel = file_path.strip_prefix(workspace_root).unwrap_or(&file_path);

        if let Some(pattern) = detect_vacuous_precondition(&content) {
            return Err(format!(
                "vacuous specification precondition rejected in {}: found `{pattern}`",
                spec_rel.display()
            ));
        }

        let item_rel_path = file_path
            .strip_prefix(&specs_dir)
            .map_err(|err| format!("failed to strip Specs prefix: {err}"))?;
        let item_suffix = item_rel_path
            .with_extension("")
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join(".");

        // Check 4: When the item has a Rust `#[spec]` `ensures` clause, verify
        // that `Specs/<Item>.lean` preserves it unless explicitly opted out.
        let has_inline_ensures = bundles_by_rel_path
            .get(item_rel_path)
            .is_some_and(|b| !b.inline_ensures.is_empty())
            || obligation_file_has_inline_ensures(workspace_root, item_rel_path);

        if has_inline_ensures && !content.contains("-- @anneal-allow-replace-rust-spec") {
            let stripped_spec = strip_lean_comments(&content);
            let preserves_ensures = [
                "rustEnsures",
                "defaultPost",
                "refineSpec",
                "refineStatefulSpec",
                "refineSafeSpec",
                "refineSafeStatefulSpec",
                "refineTotalSpec",
                "refineEquivSpec",
                "refineModularSpec",
                "refineUbExceptionSpec",
            ]
            .iter()
            .any(|ident| stripped_spec.contains(ident));
            if !preserves_ensures {
                return Err(format!(
                    "spec override in {} drops the Rust #[spec] `ensures` clause; use `Obligations.{item_suffix}.refineSpec`, `Obligations.{item_suffix}.refineSafeSpec`, or `Obligations.{item_suffix}.rustEnsures` (or add `-- @anneal-allow-replace-rust-spec`)",
                    spec_rel.display()
                ));
            }
        }

        // Check 5: When both `Specs/<Item>.lean` and `Proof/<Item>.lean` exist
        // on disk, `Proof/<Item>.lean` must `import Specs.<Item>` in non-comment
        // text so `Obligations.<Item>.claim` resolves to the overridden
        // `ItemSpec` instance.
        let proof_path = workspace_root.join("anneal/proofs/Proof").join(item_rel_path);
        if proof_path.is_file() {
            let proof_content = fs::read_to_string(&proof_path)
                .map_err(|err| format!("failed to read {}: {}", proof_path.display(), err))?;
            let stripped_proof = strip_lean_comments(&proof_content);
            let expected_import = format!("import Specs.{item_suffix}");
            if !stripped_proof.contains(&expected_import) {
                let proof_rel = proof_path
                    .strip_prefix(workspace_root)
                    .unwrap_or(&proof_path);
                return Err(format!(
                    "missing `{expected_import}` in {}: `Proof/{}` must `{expected_import}` so `Obligations.{item_suffix}.claim` resolves to the overridden `ItemSpec` instance",
                    proof_rel.display(),
                    item_rel_path.display()
                ));
            }
        }
    }
    Ok(())
}

fn discover_workspace_records(workspace_root: &Path) -> Vec<UnitTargetRecord> {
    let lock_path = workspace_root.join(SPEC_LOCK_REL_PATH);
    if lock_path.is_file()
        && let Ok(raw) = fs::read_to_string(&lock_path)
        && let Ok(manifest) = parse_spec_lock_manifest(&raw)
    {
        let mut records = Vec::with_capacity(manifest.locked_records.len());
        for rec in manifest.locked_records {
            if let Some(item_kind) = CapturedItemKind::from_str_tag(&rec.item_kind) {
                records.push(UnitTargetRecord {
                    target: CapturedTarget {
                        def_id: rec.def_id,
                        mir_module_path: String::new(),
                        mir_module_sha256: rec.mir_module_sha256,
                    },
                    lean_module_name: rec.lean_module_name,
                    item_kind,
                    associated_subject_def_id: rec.associated_subject_def_id,
                });
            }
        }
        return records;
    }

    let units_dir = workspace_root.join("target/anneal/units");
    if units_dir.is_dir()
        && let Ok((_, records)) = crate::driver::aggregate_unit_manifests(&units_dir)
    {
        return records;
    }

    Vec::new()
}

fn obligation_file_has_inline_ensures(workspace_root: &Path, item_rel_path: &Path) -> bool {
    let ob_path = workspace_root
        .join(".anneal/generated/Obligations")
        .join(item_rel_path);
    let Ok(ob_text) = fs::read_to_string(ob_path) else {
        return false;
    };
    ob_text.contains("- Inline ensures:") || ob_text.contains("__anodized_fn_ensures_")
}

fn detect_vacuous_precondition(lean_src: &str) -> Option<&'static str> {
    let stripped = strip_lean_comments(lean_src);
    let collapsed = stripped.split_whitespace().collect::<Vec<_>>().join(" ");

    const FORBIDDEN_PATTERNS: &[&str] = &[
        "pre := fun _ => False",
        "pre := fun _ _ => False",
        "pre := fun (_ : List Value) => False",
        "pre := fun (_ : List Value) (_ : Memory) => False",
        "pre := False",
        "pre _ := False",
        "pre _ _ := False",
        "pre args := False",
        "pre args _ := False",
        "pre _ mem := False",
        "pre args mem := False",
        "def pre (args : List Value) : Prop := False",
        "def pre (_ : List Value) : Prop := False",
        "def pre (args : List Value) (mem : Memory) : Prop := False",
        "def pre : List Value → Prop := fun _ => False",
        "def pre : List Value -> Prop := fun _ => False",
        "safetyPre := fun _ => False",
        "safetyPre := fun _ _ => False",
        "safetyPre := False",
        "safetyPre _ := False",
        "safetyPre _ _ := False",
        "refineSpec (fun _ => False)",
        "refineSafeSpec (fun _ => False)",
        "refineStatefulSpec (fun _ _ => False)",
        "refineSafeStatefulSpec (fun _ _ => False)",
        "refineTotalSpec (fun _ _ => False)",
    ];

    for &pattern in FORBIDDEN_PATTERNS {
        if collapsed.contains(pattern) {
            return Some(pattern);
        }
    }
    None
}

fn strip_lean_comments(input: &str) -> String {
    let bytes = input.as_bytes();
    let mut out = String::with_capacity(input.len());
    let mut i = 0;
    let mut block_depth = 0usize;

    while i < bytes.len() {
        if block_depth > 0 {
            if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'-' {
                block_depth += 1;
                i += 2;
            } else if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'/' {
                block_depth -= 1;
                i += 2;
                out.push(' ');
            } else {
                i += 1;
            }
            continue;
        }

        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'-' {
            block_depth = 1;
            i += 2;
            continue;
        }

        if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'-' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }

        if let Some(ch) = input[i..].chars().next() {
            out.push(ch);
            i += ch.len_utf8();
        } else {
            break;
        }
    }

    out
}

/// Render a structured Markdown context report for an AI agent tasked with
/// proving obligations in `workspace_root`.
///
/// Groups subject obligations via `group_subject_obligations(records)`,
/// filters by `item_filter` (matching `def_id` or `item_module_suffix` when
/// provided), and emits a self-contained bundle with workspace rules, proof
/// status, obligation definitions, active specification overrides, captured
/// MIR, and starter proof templates.
pub fn render_agent_context(
    workspace_root: &Path,
    records: &[UnitTargetRecord],
    item_filter: Option<&str>,
) -> Result<String, String> {
    let all_bundles = group_subject_obligations(records);
    let filter_patterns: Vec<&str> = item_filter
        .map(|f| {
            f.split(',')
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .collect()
        })
        .unwrap_or_default();

    let bundles: Vec<&SubjectObligationBundle> = if filter_patterns.is_empty() {
        all_bundles.iter().collect()
    } else {
        all_bundles
            .iter()
            .filter(|b| {
                filter_patterns.iter().any(|pat| {
                    b.subject.target.def_id.contains(pat) || b.item_module_suffix.contains(pat)
                })
            })
            .collect()
    };

    if !filter_patterns.is_empty() && bundles.is_empty() {
        return Err(format!(
            "no verification subject items matched item filter '{}'",
            item_filter.unwrap_or_default()
        ));
    }

    let proofs_root = workspace_root.join("anneal/proofs");
    let generated_root = workspace_root.join(".anneal/generated");
    let spec_lock_path = workspace_root.join(SPEC_LOCK_REL_PATH);
    let spec_lock_active = spec_lock_path.is_file();

    let mut present_proofs = 0usize;
    let mut missing_proofs = 0usize;
    for bundle in &bundles {
        let authored = detect_authored_item_modules(&proofs_root, &bundle.item_rel_path);
        if authored.has_proof {
            present_proofs += 1;
        } else {
            missing_proofs += 1;
        }
    }

    let mut out = String::new();
    out.push_str("# Anneal Agent Proof Context\n\n");
    out.push_str("## Workspace Summary\n\n");
    out.push_str(&format!("- **Total Subject Items**: {}\n", bundles.len()));
    out.push_str(&format!(
        "- **Proof Status**: {} Present, {} Missing\n",
        present_proofs, missing_proofs
    ));
    out.push_str(&format!(
        "- **Spec Lock (`.anneal/spec-lock.json`)**: {}\n",
        if spec_lock_active {
            "Active (Locked)"
        } else {
            "Inactive (Unlocked)"
        }
    ));
    if let Some(f) = item_filter
        && !f.trim().is_empty()
    {
        out.push_str(&format!("- **Active Item Filter**: `{}`\n", f.trim()));
    }
    out.push_str(
        "\n## Read-Only vs. Writable Workspace Rules\n\n\
         - **ONLY WRITABLE TARGET**: `anneal/proofs/Proof/<Crate>/<Item>.lean`.\n\
         - **STRICTLY READ-ONLY**:\n  \
           - Rust source files (`src/**`, `Cargo.toml`) and inline contract attributes (`#[spec]`, `#[external_spec]`, `#[invariant]`, `#[unsafe_impl]`).\n  \
           - Specification overrides (`anneal/proofs/Specs/<Crate>/<Item>.lean`). Creating or editing `Specs` files to weaken a contract (`pre := False` or `post := True`) is rejected by `cargo anneal agent-verify`.\n  \
           - Assumption modules (`anneal/proofs/Assumptions/<Crate>/<Item>.lean`). Adding unauthorized `axiom` declarations is rejected by `verify_spec_lock` and `TrustedBoundary`.\n  \
           - Disposable generated modules (`.anneal/generated/Mir/**`, `.anneal/generated/Obligations/**`, `.anneal/generated/Verify/**`, `.anneal/lakefile.toml`, `.anneal/spec-lock.json`), which are deterministically overwritten before verification.\n\n",
    );

    for bundle in bundles {
        let def_id = &bundle.subject.target.def_id;
        let suffix = &bundle.item_module_suffix;
        let rel_lean = bundle
            .item_rel_path
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/");
        let authored = detect_authored_item_modules(&proofs_root, &bundle.item_rel_path);
        let proof_status = if authored.has_proof {
            "Present"
        } else {
            "Missing"
        };
        let contract_surface = if authored.is_equiv {
            "equiv (`StatefulEquivItemSpec` / `StatefulEquivVerificationResult`)"
        } else if authored.is_total {
            "total (`TotalItemSpec` / `TotalVerificationResult`)"
        } else if authored.is_stateful {
            "true (`StatefulItemSpec` / `StatefulVerificationResult`)"
        } else {
            "false (`ItemSpec` / `VerificationResult`)"
        };
        let companion_count = bundle.inline_requires.len()
            + bundle.inline_ensures.len()
            + bundle.external_specs.len();

        out.push_str(&format!("## Item `{def_id}` (`{suffix}`)\n\n"));
        out.push_str(&format!("- **`def_id`**: `{def_id}`\n"));
        out.push_str(&format!("- **`item_module_suffix`**: `{suffix}`\n"));
        out.push_str(&format!("- **`is_stateful`**: {contract_surface}\n"));
        out.push_str(&format!("- **Proof Status**: {proof_status}\n"));
        out.push_str(&format!(
            "- **Writable Proof Path**: `anneal/proofs/Proof/{rel_lean}`\n"
        ));
        out.push_str(&format!(
            "- **Companion Spec Count**: {companion_count} (requires: {}, ensures: {}, external: {})\n\n",
            bundle.inline_requires.len(),
            bundle.inline_ensures.len(),
            bundle.external_specs.len()
        ));

        let obligations_disk = generated_root.join("Obligations").join(&bundle.item_rel_path);
        let obligations_text = if obligations_disk.is_file() {
            fs::read_to_string(&obligations_disk).map_err(|err| {
                format!("failed to read {}: {}", obligations_disk.display(), err)
            })?
        } else {
            render_obligations_module_with_options(bundle, authored)
        };
        out.push_str(&format!(
            "### Generated Obligations (`.anneal/generated/Obligations/{rel_lean}`)\n\n```lean\n{}\n```\n\n",
            obligations_text.trim_end()
        ));

        let specs_disk = proofs_root.join("Specs").join(&bundle.item_rel_path);
        if specs_disk.is_file() {
            let specs_text = fs::read_to_string(&specs_disk).map_err(|err| {
                format!("failed to read {}: {}", specs_disk.display(), err)
            })?;
            out.push_str(&format!(
                "### Locked Specification Override (`anneal/proofs/Specs/{rel_lean}`)\n\n```lean\n{}\n```\n\n",
                specs_text.trim_end()
            ));
        }

        let mir_disk = generated_root.join("Mir").join(&bundle.item_rel_path);
        if mir_disk.is_file() {
            let mir_text = fs::read_to_string(&mir_disk).map_err(|err| {
                format!("failed to read {}: {}", mir_disk.display(), err)
            })?;
            out.push_str(&format!(
                "### Captured MIR Module (`.anneal/generated/Mir/{rel_lean}`)\n\n```lean\n{}\n```\n\n",
                mir_text.trim_end()
            ));
        }

        let proof_disk = proofs_root.join("Proof").join(&bundle.item_rel_path);
        if proof_disk.is_file() {
            let proof_text = fs::read_to_string(&proof_disk).map_err(|err| {
                format!("failed to read {}: {}", proof_disk.display(), err)
            })?;
            out.push_str(&format!(
                "### Current Proof Module (`anneal/proofs/Proof/{rel_lean}`)\n\n```lean\n{}\n```\n\n",
                proof_text.trim_end()
            ));
        } else {
            let starter = render_proof_template_with_options(bundle, authored);
            out.push_str(&format!(
                "### Starter Proof Template (`anneal/proofs/Proof/{rel_lean}`)\n\n```lean\n{}\n```\n\n",
                starter.trim_end()
            ));
        }
    }

    Ok(out)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum JsonValue {
    Null,
    Str(String),
    Array(Vec<JsonValue>),
    Object(Vec<(String, JsonValue)>),
}

impl JsonValue {
    fn as_object(&self) -> Option<&[(String, JsonValue)]> {
        match self {
            Self::Object(entries) => Some(entries),
            _ => None,
        }
    }

    fn as_array(&self) -> Option<&[JsonValue]> {
        match self {
            Self::Array(items) => Some(items),
            _ => None,
        }
    }
}

fn get_field<'a>(obj: &'a [(String, JsonValue)], key: &str) -> Option<&'a JsonValue> {
    obj.iter().find(|(k, _)| k == key).map(|(_, v)| v)
}

fn get_string_field(obj: &[(String, JsonValue)], key: &str) -> Result<String, String> {
    match get_field(obj, key) {
        Some(JsonValue::Str(s)) => Ok(s.clone()),
        Some(_) => Err(format!("field '{key}' must be a JSON string")),
        None => Err(format!("missing required JSON field '{key}'")),
    }
}

fn parse_json(input: &str) -> Result<JsonValue, String> {
    let mut parser = SimpleJsonParser {
        bytes: input.as_bytes(),
        pos: 0,
    };
    let val = parser.parse_value()?;
    parser.skip_ws();
    if parser.pos != parser.bytes.len() {
        return Err(format!("unexpected trailing JSON data at byte {}", parser.pos));
    }
    Ok(val)
}

struct SimpleJsonParser<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> SimpleJsonParser<'a> {
    fn skip_ws(&mut self) {
        while self.pos < self.bytes.len() && self.bytes[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
    }

    fn peek(&mut self) -> Option<u8> {
        self.skip_ws();
        self.bytes.get(self.pos).copied()
    }

    fn parse_value(&mut self) -> Result<JsonValue, String> {
        let b = self
            .peek()
            .ok_or_else(|| "unexpected end of JSON input".to_string())?;
        match b {
            b'{' => self.parse_object(),
            b'[' => self.parse_array(),
            b'"' => self.parse_string().map(JsonValue::Str),
            b'n' => self.parse_null(),
            _ => Err(format!("unexpected JSON token at byte {}", self.pos)),
        }
    }

    fn parse_object(&mut self) -> Result<JsonValue, String> {
        self.pos += 1;
        let mut entries = Vec::new();
        if self.peek() == Some(b'}') {
            self.pos += 1;
            return Ok(JsonValue::Object(entries));
        }
        loop {
            let key = self.parse_string()?;
            if self.peek() != Some(b':') {
                return Err(format!("expected ':' after key at byte {}", self.pos));
            }
            self.pos += 1;
            let val = self.parse_value()?;
            entries.push((key, val));
            match self.peek() {
                Some(b',') => self.pos += 1,
                Some(b'}') => {
                    self.pos += 1;
                    return Ok(JsonValue::Object(entries));
                }
                _ => return Err(format!("expected ',' or '}}' at byte {}", self.pos)),
            }
        }
    }

    fn parse_array(&mut self) -> Result<JsonValue, String> {
        self.pos += 1;
        let mut items = Vec::new();
        if self.peek() == Some(b']') {
            self.pos += 1;
            return Ok(JsonValue::Array(items));
        }
        loop {
            items.push(self.parse_value()?);
            match self.peek() {
                Some(b',') => self.pos += 1,
                Some(b']') => {
                    self.pos += 1;
                    return Ok(JsonValue::Array(items));
                }
                _ => return Err(format!("expected ',' or ']' at byte {}", self.pos)),
            }
        }
    }

    fn parse_string(&mut self) -> Result<String, String> {
        if self.peek() != Some(b'"') {
            return Err(format!("expected '\"' at byte {}", self.pos));
        }
        self.pos += 1;
        let mut bytes = Vec::new();
        while self.pos < self.bytes.len() {
            let b = self.bytes[self.pos];
            self.pos += 1;
            match b {
                b'"' => {
                    return String::from_utf8(bytes)
                        .map_err(|_| "invalid UTF-8 in JSON string".to_string());
                }
                b'\\' => {
                    let esc = *self
                        .bytes
                        .get(self.pos)
                        .ok_or_else(|| "unterminated escape in JSON string".to_string())?;
                    self.pos += 1;
                    match esc {
                        b'"' => bytes.push(b'"'),
                        b'\\' => bytes.push(b'\\'),
                        b'/' => bytes.push(b'/'),
                        b'b' => bytes.push(0x08),
                        b'f' => bytes.push(0x0c),
                        b'n' => bytes.push(b'\n'),
                        b'r' => bytes.push(b'\r'),
                        b't' => bytes.push(b'\t'),
                        b'u' => {
                            if self.pos + 4 > self.bytes.len() {
                                return Err("truncated \\uXXXX escape".to_string());
                            }
                            let hex = std::str::from_utf8(&self.bytes[self.pos..self.pos + 4])
                                .map_err(|_| "invalid \\uXXXX escape".to_string())?;
                            let code = u32::from_str_radix(hex, 16)
                                .map_err(|_| "invalid hex in \\uXXXX escape".to_string())?;
                            self.pos += 4;
                            let ch = char::from_u32(code)
                                .ok_or_else(|| "invalid Unicode scalar in \\uXXXX".to_string())?;
                            let mut buf = [0u8; 4];
                            bytes.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                        }
                        other => return Err(format!("unsupported JSON escape '\\{}'", other as char)),
                    }
                }
                other => bytes.push(other),
            }
        }
        Err("unterminated JSON string".to_string())
    }

    fn parse_null(&mut self) -> Result<JsonValue, String> {
        self.skip_ws();
        if self.bytes[self.pos..].starts_with(b"null") {
            self.pos += 4;
            Ok(JsonValue::Null)
        } else {
            Err(format!("invalid literal at byte {}", self.pos))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anneal_rustc_capture::{CapturedItemKind, CapturedTarget};
    use std::env;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn unique_temp_dir(prefix: &str) -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after epoch")
            .as_nanos();
        let dir = env::temp_dir().join(format!(
            "cargo-anneal-agent-{}-{}-{}",
            prefix,
            std::process::id(),
            nanos
        ));
        fs::create_dir_all(&dir).expect("create temp dir");
        dir
    }

    fn sample_records() -> Vec<UnitTargetRecord> {
        vec![
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "demo::add".to_string(),
                    mir_module_path: "Mir/Demo/add.lean".to_string(),
                    mir_module_sha256: "1".repeat(64),
                },
                lean_module_name: "Mir.Demo.add".to_string(),
                item_kind: CapturedItemKind::Subject,
                associated_subject_def_id: None,
            },
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "demo::__anodized_fn_requires_add".to_string(),
                    mir_module_path: "Mir/Demo/__anodized_fn_requires_add.lean".to_string(),
                    mir_module_sha256: "2".repeat(64),
                },
                lean_module_name: "Mir.Demo.__anodized_fn_requires_add".to_string(),
                item_kind: CapturedItemKind::InlineSpecRequires,
                associated_subject_def_id: Some("demo::add".to_string()),
            },
        ]
    }

    #[test]
    fn spec_lock_manifest_round_trip_and_verification() {
        let ws = unique_temp_dir("lock-roundtrip");
        let specs_dir = ws.join("anneal/proofs/Specs/Demo");
        let assumptions_dir = ws.join("anneal/proofs/Assumptions/Demo");
        fs::create_dir_all(&specs_dir).expect("create Specs/Demo");
        fs::create_dir_all(&assumptions_dir).expect("create Assumptions/Demo");

        let spec_file = specs_dir.join("add.lean");
        let spec_text = "prelude\nimport Trusted\nnamespace Specs.Demo.add\ninstance : ItemSpec \"demo::add\" where\n  pre _ := True\n  post _ _ := True\nend Specs.Demo.add\n";
        fs::write(&spec_file, spec_text).expect("write spec file");

        let records = sample_records();
        let lock_path = lock_workspace_specs(&ws, &records).expect("lock_workspace_specs");
        assert!(lock_path.is_file());

        let verified = verify_spec_lock(&ws, &records).expect("verify_spec_lock must pass");
        assert_eq!(verified.schema, SPEC_LOCK_SCHEMA_V1);
        assert_eq!(verified.locked_records.len(), 2);
        assert_eq!(verified.locked_specs_files.len(), 1);
        assert!(verified.locked_assumptions_files.is_empty());

        let json = verified.to_json_string();
        let reparsed = SpecLockManifest::from_json_str(&json).expect("reparse JSON");
        assert_eq!(reparsed, verified);

        // 1. Rejects narrowing or modifying captured records.
        let narrowed_err = verify_spec_lock(&ws, &records[..1])
            .expect_err("must reject missing companion record");
        assert!(narrowed_err.contains("spec-lock violation"));

        // 2. Rejects modifying a locked Specs file.
        fs::write(&spec_file, format!("{spec_text}-- tampered\n")).expect("tamper spec");
        let mod_err = verify_spec_lock(&ws, &records).expect_err("must reject modified spec");
        assert!(mod_err.contains("locked Specs file 'anneal/proofs/Specs/Demo/add.lean' was modified"));
        fs::write(&spec_file, spec_text).expect("restore spec");

        // 3. Rejects adding an unlocked Specs file (Spec-Override loophole).
        let rogue_spec = specs_dir.join("other.lean");
        fs::write(&rogue_spec, "-- rogue spec override\n").expect("write rogue spec");
        let add_spec_err =
            verify_spec_lock(&ws, &records).expect_err("must reject unlocked Specs file");
        assert!(add_spec_err.contains("unlocked Specs file 'anneal/proofs/Specs/Demo/other.lean' was added"));
        fs::remove_file(&rogue_spec).expect("remove rogue spec");

        // 4. Rejects adding an unlocked Assumptions file.
        let rogue_assump = assumptions_dir.join("add.lean");
        fs::write(&rogue_assump, "axiom cheat : False\n").expect("write rogue assumption");
        let add_assump_err =
            verify_spec_lock(&ws, &records).expect_err("must reject unlocked Assumptions file");
        assert!(add_assump_err.contains("unlocked Assumptions file 'anneal/proofs/Assumptions/Demo/add.lean' was added"));
        fs::remove_file(&rogue_assump).expect("remove rogue assumption");

        let _ = fs::remove_dir_all(&ws);
    }

    #[test]
    fn check_specs_non_vacuous_rejects_false_preconditions() {
        let ws = unique_temp_dir("vacuous");
        let specs_dir = ws.join("anneal/proofs/Specs/Demo");
        fs::create_dir_all(&specs_dir).expect("create Specs/Demo");
        let spec_file = specs_dir.join("add.lean");

        fs::write(
            &spec_file,
            "instance : ItemSpec \"demo::add\" where\n  pre := fun _ => False\n  post := fun _ _ => True\n",
        )
        .expect("write vacuous spec");
        let err = check_specs_non_vacuous(&ws).expect_err("must reject fun _ => False");
        assert!(err.contains("vacuous specification precondition rejected"));

        fs::write(
            &spec_file,
            "instance : StatefulItemSpec \"demo::add\" where\n  pre := fun _ _ => False\n  post := fun _ _ _ _ => True\n",
        )
        .expect("write stateful vacuous spec");
        let err2 = check_specs_non_vacuous(&ws).expect_err("must reject fun _ _ => False");
        assert!(err2.contains("vacuous specification precondition rejected"));

        fs::write(
            &spec_file,
            "-- pre := fun _ => False in a comment is ignored\ninstance : ItemSpec \"demo::add\" where\n  pre := fun _ => True\n  post := fun _ _ => True\n",
        )
        .expect("write valid spec with comment");
        check_specs_non_vacuous(&ws).expect("commented pattern must not trigger false positive");

        let _ = fs::remove_dir_all(&ws);
    }

    #[test]
    fn render_agent_context_includes_summary_and_filtered_items() {
        let ws = unique_temp_dir("context");
        let records = sample_records();
        let _ = lock_workspace_specs(&ws, &records).expect("lock specs");

        let ctx = render_agent_context(&ws, &records, Some("demo::add"))
            .expect("render_agent_context");
        assert!(ctx.contains("# Anneal Agent Proof Context"));
        assert!(ctx.contains("- **Total Subject Items**: 1"));
        assert!(ctx.contains("- **Proof Status**: 0 Present, 1 Missing"));
        assert!(ctx.contains("- **Spec Lock (`.anneal/spec-lock.json`)**: Active (Locked)"));
        assert!(ctx.contains("`anneal/proofs/Proof/<Crate>/<Item>.lean`"));
        assert!(ctx.contains("## Item `demo::add` (`Demo.add`)"));
        assert!(ctx.contains("### Generated Obligations (`.anneal/generated/Obligations/Demo/add.lean`)"));
        assert!(ctx.contains("### Starter Proof Template (`anneal/proofs/Proof/Demo/add.lean`)"));

        let bad_filter = render_agent_context(&ws, &records, Some("nonexistent_item"))
            .expect_err("non-matching filter must error");
        assert!(bad_filter.contains("no verification subject items matched"));

        let _ = fs::remove_dir_all(&ws);
    }

    #[test]
    fn check_specs_non_vacuous_enforces_preserving_rust_ensures_and_proof_imports() {
        let ws = unique_temp_dir("ensures-and-imports");
        let specs_dir = ws.join("anneal/proofs/Specs/Demo");
        let proof_dir = ws.join("anneal/proofs/Proof/Demo");
        fs::create_dir_all(&specs_dir).expect("create Specs/Demo");
        fs::create_dir_all(&proof_dir).expect("create Proof/Demo");

        let mut records = sample_records();
        records.push(UnitTargetRecord {
            target: CapturedTarget {
                def_id: "demo::__anodized_fn_ensures_add".to_string(),
                mir_module_path: "Mir/Demo/__anodized_fn_ensures_add.lean".to_string(),
                mir_module_sha256: "3".repeat(64),
            },
            lean_module_name: "Mir.Demo.__anodized_fn_ensures_add".to_string(),
            item_kind: CapturedItemKind::InlineSpecEnsures,
            associated_subject_def_id: Some("demo::add".to_string()),
        });

        let spec_file = specs_dir.join("add.lean");
        let proof_file = proof_dir.join("add.lean");
        let _ = lock_workspace_specs(&ws, &records).expect("lock specs");

        // Check 4: Rejects `Specs/Demo/add.lean` when it drops `rustEnsures`
        // (even if `rustEnsures` is mentioned inside a comment).
        fs::write(
            &spec_file,
            "-- rustEnsures in comment does not preserve it\n\
             instance : ItemSpec \"demo::add\" where\n  \
               pre args := Obligations.Demo.add.rustRequires args\n  \
               post _ _ := True\n",
        )
        .expect("write spec dropping ensures");
        assert!(
            lock_workspace_specs(&ws, &records).is_err(),
            "lock_workspace_specs must also reject spec dropping rustEnsures"
        );
        let drop_err =
            check_specs_non_vacuous(&ws).expect_err("must reject spec dropping rustEnsures");
        assert!(
            drop_err.contains("drops the Rust #[spec] `ensures` clause")
                && drop_err.contains("Obligations.Demo.add.refineSpec"),
            "unexpected Check 4 error: {drop_err}"
        );

        // Check 4: Accepts `-- @anneal-allow-replace-rust-spec` opt-out.
        fs::write(
            &spec_file,
            "-- @anneal-allow-replace-rust-spec\n\
             instance : ItemSpec \"demo::add\" where\n  \
               pre _ := True\n  \
               post _ _ := True\n",
        )
        .expect("write spec with opt-out");
        check_specs_non_vacuous(&ws).expect("opt-out comment must allow replacing rust spec");

        // Check 4: Accepts `refineSpec` (and `rustEnsures`).
        fs::write(
            &spec_file,
            "instance : ItemSpec \"demo::add\" :=\n  \
               Obligations.Demo.add.refineSpec (fun _ => True) (fun _ _ => True)\n",
        )
        .expect("write spec using refineSpec");
        check_specs_non_vacuous(&ws).expect("refineSpec must pass Check 4");

        // Check 5: Rejects `Proof/Demo/add.lean` when `Specs/Demo/add.lean`
        // exists on disk and `Proof/Demo/add.lean` omits `import Specs.Demo.add`
        // (or only has it in a comment).
        fs::write(
            &proof_file,
            "prelude\n\
             import Obligations.Demo.add\n\
             -- import Specs.Demo.add\n\
             theorem verified : VerificationResult Obligations.Demo.add.claim := sorry\n",
        )
        .expect("write proof missing Specs import");
        let import_err = check_specs_non_vacuous(&ws)
            .expect_err("must reject Proof missing `import Specs.Demo.add`");
        assert!(
            import_err.contains("missing `import Specs.Demo.add`")
                && import_err.contains("Obligations.Demo.add.claim"),
            "unexpected Check 5 error: {import_err}"
        );

        // Check 5: Accepts `Proof/Demo/add.lean` once `import Specs.Demo.add`
        // is present in non-comment text.
        fs::write(
            &proof_file,
            "prelude\n\
             import Obligations.Demo.add\n\
             import Specs.Demo.add\n\
             theorem verified : VerificationResult Obligations.Demo.add.claim := sorry\n",
        )
        .expect("write proof with Specs import");
        check_specs_non_vacuous(&ws).expect("Proof importing Specs.Demo.add must pass Check 5");

        let _ = fs::remove_dir_all(&ws);
    }

    #[test]
    fn check_specs_non_vacuous_with_records_accepts_refine_safe_spec() {
        let ws = unique_temp_dir("refine-safe-spec");
        let specs_dir = ws.join("anneal/proofs/Specs/Demo");
        fs::create_dir_all(&specs_dir).expect("create Specs/Demo");

        let mut records = sample_records();
        records.push(UnitTargetRecord {
            target: CapturedTarget {
                def_id: "demo::__anodized_fn_ensures_add".to_string(),
                mir_module_path: "Mir/Demo/__anodized_fn_ensures_add.lean".to_string(),
                mir_module_sha256: "3".repeat(64),
            },
            lean_module_name: "Mir.Demo.__anodized_fn_ensures_add".to_string(),
            item_kind: CapturedItemKind::InlineSpecEnsures,
            associated_subject_def_id: Some("demo::add".to_string()),
        });

        let spec_file = specs_dir.join("add.lean");
        fs::write(
            &spec_file,
            "instance : ItemSpec \"demo::add\" :=\n  \
               Obligations.Demo.add.refineSafeSpec (fun _ => True) (fun _ => True) (fun _ _ => True)\n",
        )
        .expect("write spec using refineSafeSpec");
        check_specs_non_vacuous_with_records(&ws, &records)
            .expect("refineSafeSpec must pass check_specs_non_vacuous_with_records");

        fs::write(
            &spec_file,
            "instance : StatefulItemSpec \"demo::add\" :=\n  \
               Obligations.Demo.add.refineSafeStatefulSpec (fun _ _ => True) (fun _ _ => True) (fun _ _ _ _ => True)\n",
        )
        .expect("write spec using refineSafeStatefulSpec");
        check_specs_non_vacuous_with_records(&ws, &records)
            .expect("refineSafeStatefulSpec must pass check_specs_non_vacuous_with_records");

        let _ = fs::remove_dir_all(&ws);
    }

    #[test]
    fn spec_lock_allows_designated_mutable_subject_impl_edit_while_locking_specs() {
        let ws = unique_temp_dir("mutable-subject");
        let mut records = sample_records();
        records.push(UnitTargetRecord {
            target: CapturedTarget {
                def_id: "demo::helper".to_string(),
                mir_module_path: "Mir/Demo/helper.lean".to_string(),
                mir_module_sha256: "9".repeat(64),
            },
            lean_module_name: "Mir.Demo.helper".to_string(),
            item_kind: CapturedItemKind::Subject,
            associated_subject_def_id: None,
        });

        let lock_path = lock_workspace_specs_with_mutable(&ws, &records, &["demo::add".to_string()])
            .expect("lock with mutable subject");
        assert!(lock_path.is_file());

        // 1. Mutating `demo::add` subject MIR digest succeeds!
        let mut edited_impl = records.clone();
        edited_impl[0].target.mir_module_sha256 = "f".repeat(64);
        let verified = verify_spec_lock(&ws, &edited_impl)
            .expect("designated mutable subject body edit must pass verify_spec_lock");
        assert_eq!(verified.mutable_subjects, vec!["demo::add".to_string()]);

        // 2. Mutating `demo::__anodized_fn_requires_add` companion MIR digest is REJECTED!
        let mut edited_req = edited_impl.clone();
        edited_req[1].target.mir_module_sha256 = "e".repeat(64);
        let req_err = verify_spec_lock(&ws, &edited_req)
            .expect_err("modifying #[spec] companion of mutable subject must fail");
        assert!(req_err.contains("__anodized_fn_requires_add"));

        // 3. Mutating non-designated `demo::helper` subject MIR digest is REJECTED!
        let mut edited_other = edited_impl.clone();
        edited_other[2].target.mir_module_sha256 = "d".repeat(64);
        let other_err = verify_spec_lock(&ws, &edited_other)
            .expect_err("modifying non-designated subject must fail");
        assert!(other_err.contains("demo::helper"));

        let _ = fs::remove_dir_all(&ws);
    }
}
