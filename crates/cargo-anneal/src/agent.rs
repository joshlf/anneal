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
//!    `.anneal/spec-lock.json`, together with each record's `MirFragment`
//!    certificate (`mir_fragment` + `spec_digest`) and a manifest-level
//!    `spec_digest` over the whole locked payload.
//! 2. **Pre-build lock verification (`verify_spec_lock`,
//!    `check_specs_non_vacuous`)**: rejects verification runs before invoking
//!    Lake if captured items were filtered or altered, if any `Specs` or
//!    `Assumptions` file was added, removed, or modified relative to
//!    `.anneal/spec-lock.json`, if a recorded fragment certificate no longer
//!    matches, or if a `Specs` file introduces a vacuous `False` precondition.
//! 3. **Structured agent context (`render_agent_context`)**: assembles a
//!    Markdown report containing each target item's obligation module, active
//!    specification override, `MirFragment` classification (with a boundary
//!    diagnostic above `pure_bounded_loop`), lowered MIR body, and starter
//!    proof template.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Component, Path, PathBuf};

use anneal_rustc_capture::manifest::{escape_json, sha256_hex};
use anneal_rustc_capture::{CapturedItemKind, CapturedTarget, UnitTargetRecord};

use crate::obligations::{
    AuthoredItemModules, SubjectObligationBundle, derive_item_module_suffix,
    group_subject_obligations, module_suffix_to_rel_path, render_obligations_module_with_options,
};
use crate::scaffold::{
    MirFragment, MirLiftingProfile, analyze_workspace_lifting_profile,
    classify_mir_fragment, compute_fragment_spec_digest, detect_authored_item_modules,
    render_mir_fragment_diagnostic, render_proof_template_with_hints,
};

/// Schema identifier stored in `.anneal/spec-lock.json`.
pub const SPEC_LOCK_SCHEMA_V1: &str = "anneal.spec-lock.v1";

/// Default workspace-relative path to the specification lock manifest.
pub const SPEC_LOCK_REL_PATH: &str = ".anneal/spec-lock.json";

/// Versioned domain-separation tag of the manifest-level `spec_digest`
/// (`compute_spec_lock_manifest_digest`).
const SPEC_LOCK_MANIFEST_DIGEST_DOMAIN: &str = "anneal-spec-lock-manifest-digest-v1";

/// Returns `true` when `tag` is a canonical `MirFragment::as_str()` tag
/// (`"pure_loop_free"`, `"pure_bounded_loop"`, `"tree_borrows_local"`,
/// `"intrinsic_copy"`, or `"full_mir"`), rejecting the Lean constructor
/// aliases accepted by `MirFragment::from_str` (`"fullMir"`,
/// `"MirFragment.fullMir"`) and any surrounding whitespace.
pub fn is_canonical_mir_fragment_tag(tag: &str) -> bool {
    tag.parse::<MirFragment>()
        .is_ok_and(|frag| frag.as_str() == tag)
}

/// Returns `true` when `digest` is exactly 64 lowercase ASCII hex characters
/// (the canonical `sha256_hex` rendering used by every `spec_digest`).
pub fn is_lowercase_sha256_hex(digest: &str) -> bool {
    digest.len() == 64
        && digest
            .bytes()
            .all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
}

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
    /// Canonical `MirFragment::as_str()` tag (`"pure_loop_free"` ..
    /// `"full_mir"`) of the locked `Mir/<Item>.lean` body, classified by
    /// `classify_mir_fragment` (fail-closed `"full_mir"` when no captured
    /// module matching `mir_module_sha256` is on disk). `None` on legacy
    /// `anneal.spec-lock.v1` manifests written before fragment certificates.
    pub mir_fragment: Option<String>,
    /// 64-char lowercase hex `compute_fragment_spec_digest(def_id,
    /// mir_module_sha256, authored Specs/<Item>.lean source, mir_fragment)`
    /// certificate. `None` on legacy manifests.
    pub spec_digest: Option<String>,
}

impl LockedUnitRecord {
    /// Project a `UnitTargetRecord` into its legacy (certificate-free) locked
    /// manifest representation (`mir_fragment` and `spec_digest` are `None`).
    pub fn from_unit_record(record: &UnitTargetRecord) -> Self {
        Self {
            def_id: record.target.def_id.clone(),
            lean_module_name: record.lean_module_name.clone(),
            item_kind: record.item_kind.as_str().to_string(),
            associated_subject_def_id: record.associated_subject_def_id.clone(),
            mir_module_sha256: record.target.mir_module_sha256.clone(),
            mir_fragment: None,
            spec_digest: None,
        }
    }

    /// Whether this record carries a fragment certificate (`mir_fragment` or
    /// `spec_digest`).
    pub fn has_fragment_certificate(&self) -> bool {
        self.mir_fragment.is_some() || self.spec_digest.is_some()
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
    /// 64-char lowercase hex `compute_spec_lock_manifest_digest` over the
    /// manifest payload itself (`schema`, sorted `locked_records` including
    /// their `mir_fragment` / `spec_digest`, `locked_specs_files`,
    /// `locked_assumptions_files`, and `mutable_subjects`), fixed at
    /// `lock-specs` time. `None` on legacy manifests.
    pub spec_digest: Option<String>,
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
///
/// The optional `spec_digest` (manifest) and `mir_fragment` / `spec_digest`
/// (record) keys are omitted when `None`, so a certificate-free manifest
/// serializes bit-for-bit identically to the legacy `anneal.spec-lock.v1`
/// shape, and are emitted in a fixed position when `Some(..)`.
pub fn serialize_spec_lock_manifest(manifest: &SpecLockManifest) -> String {
    let mut out = String::from("{\n");
    out.push_str(&format!(
        "  \"schema\": \"{}\",\n",
        escape_json(&manifest.schema)
    ));
    if let Some(digest) = &manifest.spec_digest {
        out.push_str(&format!("  \"spec_digest\": \"{}\",\n", escape_json(digest)));
    }

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
        let mut trailing = vec![format!(
            "\"mir_module_sha256\": \"{}\"",
            escape_json(&rec.mir_module_sha256)
        )];
        if let Some(frag) = &rec.mir_fragment {
            trailing.push(format!("\"mir_fragment\": \"{}\"", escape_json(frag)));
        }
        if let Some(digest) = &rec.spec_digest {
            trailing.push(format!("\"spec_digest\": \"{}\"", escape_json(digest)));
        }
        for (j, field) in trailing.iter().enumerate() {
            let sep = if j + 1 < trailing.len() { "," } else { "" };
            out.push_str(&format!("      {field}{sep}\n"));
        }
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
///
/// Backward compatible with legacy `anneal.spec-lock.v1` manifests: a missing
/// or `null` `mir_fragment` / `spec_digest` key parses as `None`. Present
/// values are validated strictly: `mir_fragment` must be a canonical
/// `MirFragment::as_str()` tag (`is_canonical_mir_fragment_tag`) and every
/// `spec_digest` must be 64 lowercase hex characters
/// (`is_lowercase_sha256_hex`). Duplicate object keys are rejected so the
/// manifest cannot mean different things to different JSON readers.
pub fn parse_spec_lock_manifest(input: &str) -> Result<SpecLockManifest, String> {
    let root = parse_json(input)?;
    let obj = root
        .as_object()
        .ok_or_else(|| "expected top-level JSON object in spec-lock manifest".to_string())?;

    let schema = get_string_field(obj, "schema")?;
    let spec_digest = parse_optional_spec_digest(obj, "spec-lock manifest")?;
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
        let mir_fragment = match get_field(item_obj, "mir_fragment") {
            None | Some(JsonValue::Null) => None,
            Some(JsonValue::Str(s)) if is_canonical_mir_fragment_tag(s) => Some(s.clone()),
            Some(JsonValue::Str(s)) => {
                return Err(format!(
                    "field 'mir_fragment' of locked record '{def_id}' must be a canonical MirFragment tag (pure_loop_free, pure_bounded_loop, tree_borrows_local, intrinsic_copy, or full_mir), got {s:?}"
                ));
            }
            Some(_) => {
                return Err(format!(
                    "field 'mir_fragment' of locked record '{def_id}' must be a canonical MirFragment tag string or null"
                ));
            }
        };
        let spec_digest =
            parse_optional_spec_digest(item_obj, &format!("locked record '{def_id}'"))?;
        locked_records.push(LockedUnitRecord {
            def_id,
            lean_module_name,
            item_kind,
            associated_subject_def_id,
            mir_module_sha256,
            mir_fragment,
            spec_digest,
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
        spec_digest,
    })
}

/// Parse an optional `"spec_digest"` key of `obj` (`owner` names the manifest
/// or record in error messages): missing / `null` is `None`; otherwise the
/// value must be a 64-char lowercase hex string.
fn parse_optional_spec_digest(
    obj: &[(String, JsonValue)],
    owner: &str,
) -> Result<Option<String>, String> {
    match get_field(obj, "spec_digest") {
        None | Some(JsonValue::Null) => Ok(None),
        Some(JsonValue::Str(s)) if is_lowercase_sha256_hex(s) => Ok(Some(s.clone())),
        Some(JsonValue::Str(s)) => Err(format!(
            "field 'spec_digest' of {owner} must be 64 lowercase hex characters, got {s:?}"
        )),
        Some(_) => Err(format!(
            "field 'spec_digest' of {owner} must be a 64-char lowercase hex string or null"
        )),
    }
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

/// Compute the manifest-level `spec_digest`: a deterministic 64-char
/// lowercase hex SHA-256 over a versioned, length-prefixed canonical encoding
/// of the manifest payload — `schema`, every `locked_records` entry (all of
/// its fields, with explicit `none` markers for absent `mir_fragment` /
/// `spec_digest` / `associated_subject_def_id`), `locked_specs_files`,
/// `locked_assumptions_files`, and `mutable_subjects` — excluding only
/// `manifest.spec_digest` itself.
///
/// Records, file digests, and subjects are sorted inside the encoding, so the
/// digest depends only on the locked *content*, never on JSON key order or
/// whitespace; any change to any field (including adding a `mutable_subjects`
/// entry, flipping a record's `mir_fragment`, or dropping a certificate)
/// changes it.
///
/// **Invariant (`--allow-impl-edit`)**: the digest commits to the manifest as
/// written by `lock-specs`, not to the live workspace. Editing the Rust body of
/// a `mutable_subjects` entry changes that subject's *current* MIR digest,
/// fragment, and record certificate, but never `.anneal/spec-lock.json`, so the
/// manifest digest stays valid while `verify_locked_records_match` and
/// `verify_locked_record_certificates` skip exactly that subject.
///
/// This is an unkeyed integrity checksum: it detects corrupted or naively
/// hand-edited lock files, but an adversary able to rewrite
/// `.anneal/spec-lock.json` can recompute it. Tamper-resistance against such an
/// adversary comes from verifying against an out-of-workspace copy
/// (`--lock-file`, `--lock-git-ref`) and from `agent-sandbox`'s read-only
/// mount of the lock file; the per-record certificates are additionally
/// re-derived from the workspace on every `verify_spec_lock`.
pub fn compute_spec_lock_manifest_digest(manifest: &SpecLockManifest) -> String {
    fn put(out: &mut String, key: &str, val: &str) {
        out.push_str(&format!("{key}:{}:{val}\n", val.len()));
    }
    fn put_opt(out: &mut String, key: &str, val: Option<&str>) {
        match val {
            Some(v) => out.push_str(&format!("{key}:some:{}:{v}\n", v.len())),
            None => out.push_str(&format!("{key}:none\n")),
        }
    }
    fn put_blocks(out: &mut String, key: &str, mut blocks: Vec<String>) {
        blocks.sort();
        out.push_str(&format!("{key}:{}\n", blocks.len()));
        for block in blocks {
            out.push_str(&format!("entry:{}\n{block}", block.len()));
        }
    }
    let file_blocks = |files: &[LockedFileDigest]| -> Vec<String> {
        files
            .iter()
            .map(|f| {
                let mut block = String::new();
                put(&mut block, "rel_path", &f.rel_path);
                put(&mut block, "sha256", &f.sha256);
                block
            })
            .collect()
    };

    let mut canonical = format!("{SPEC_LOCK_MANIFEST_DIGEST_DOMAIN}\n");
    put(&mut canonical, "schema", &manifest.schema);
    let record_blocks = manifest
        .locked_records
        .iter()
        .map(|rec| {
            let mut block = String::new();
            put(&mut block, "def_id", &rec.def_id);
            put(&mut block, "lean_module_name", &rec.lean_module_name);
            put(&mut block, "item_kind", &rec.item_kind);
            put_opt(
                &mut block,
                "associated_subject_def_id",
                rec.associated_subject_def_id.as_deref(),
            );
            put(&mut block, "mir_module_sha256", &rec.mir_module_sha256);
            put_opt(&mut block, "mir_fragment", rec.mir_fragment.as_deref());
            put_opt(&mut block, "spec_digest", rec.spec_digest.as_deref());
            block
        })
        .collect();
    put_blocks(&mut canonical, "locked_records", record_blocks);
    put_blocks(
        &mut canonical,
        "locked_specs_files",
        file_blocks(&manifest.locked_specs_files),
    );
    put_blocks(
        &mut canonical,
        "locked_assumptions_files",
        file_blocks(&manifest.locked_assumptions_files),
    );
    let subject_blocks = manifest
        .mutable_subjects
        .iter()
        .map(|subj| {
            let mut block = String::new();
            put(&mut block, "subject", subj);
            block
        })
        .collect();
    put_blocks(&mut canonical, "mutable_subjects", subject_blocks);
    sha256_hex(canonical.as_bytes())
}

/// Re-derived `MirFragment` certificate of one captured record.
struct RecordFragmentCertificate {
    fragment: MirFragment,
    spec_digest: String,
    /// Whether a captured MIR module whose bytes hash to `mir_module_sha256`
    /// was found (otherwise `fragment` is the fail-closed `FullMir`).
    mir_module_found: bool,
}

/// Locate and read the captured `Mir/<Item>.lean` text whose SHA-256 equals
/// `record.target.mir_module_sha256` (any existing candidate when the recorded
/// digest is empty), so the certified fragment is always classified from the
/// exact bytes the record's `mir_module_sha256` commits to.
///
/// Candidates, in order: `.anneal/generated/Mir/<item_rel>` with fallback to
/// `<workspace>/target/anneal/units` (`resolve_workspace_mir_file`, the same
/// resolution `agent-context` uses); the CLI's (possibly custom) `units_dir`
/// (`--units-dir`, searched like `scaffold` does); and
/// `rec.target.mir_module_path` (relative to its unit directory, e.g.
/// `Mir/<Crate>/<Item>.lean`) under `.anneal/generated/` and under
/// `workspace_root` (relative, `..`-free paths only).
fn read_certified_mir_text(
    workspace_root: &Path,
    record: &UnitTargetRecord,
    item_rel_path: &Path,
    units_dir: Option<&Path>,
) -> Option<String> {
    let expected_sha = &record.target.mir_module_sha256;
    let mut candidates = Vec::new();
    if let Some(path) = crate::scaffold::resolve_workspace_mir_file(
        &workspace_root.join(".anneal/generated/Mir"),
        record,
        item_rel_path,
    ) {
        candidates.push(path);
    }
    if let Some(units_dir) = units_dir {
        let mut config = crate::scaffold::ScaffoldConfig::new(workspace_root);
        config.units_dir = Some(units_dir.to_path_buf());
        if let Some(path) = crate::scaffold::find_source_mir_file(&config, record, item_rel_path) {
            candidates.push(path);
        }
    }
    let recorded = Path::new(&record.target.mir_module_path);
    if !record.target.mir_module_path.is_empty()
        && recorded
            .components()
            .all(|c| matches!(c, Component::Normal(_) | Component::CurDir))
    {
        candidates.push(workspace_root.join(".anneal/generated").join(recorded));
        candidates.push(workspace_root.join(recorded));
    }
    candidates.into_iter().find_map(|path| {
        let bytes = fs::read(&path).ok()?;
        if !expected_sha.is_empty() && sha256_hex(&bytes) != *expected_sha {
            return None;
        }
        String::from_utf8(bytes).ok()
    })
}

/// Re-derive `record`'s fragment certificate from the workspace: classify its
/// SHA-matching captured MIR (`classify_mir_fragment`, fail-closed
/// `MirFragment::FullMir` when no such module is on disk — e.g. synthetic
/// records in unit tests — identically at lock and verify time) and digest it
/// together with `def_id`, `mir_module_sha256`, and the authored
/// `anneal/proofs/Specs/<item_rel>` source when present.
fn compute_record_fragment_certificate(
    workspace_root: &Path,
    record: &UnitTargetRecord,
    units_dir: Option<&Path>,
) -> Result<RecordFragmentCertificate, String> {
    let item_rel_path = module_suffix_to_rel_path(&derive_item_module_suffix(record));
    let mir_text = read_certified_mir_text(workspace_root, record, &item_rel_path, units_dir);
    let fragment = mir_text
        .as_deref()
        .map_or(MirFragment::FullMir, |src| classify_mir_fragment(src).inferred_fragment);
    let spec_path = workspace_root
        .join("anneal/proofs/Specs")
        .join(&item_rel_path);
    let spec_src = if spec_path.is_file() {
        Some(fs::read_to_string(&spec_path).map_err(|err| {
            format!(
                "failed to read authored specification {}: {}",
                spec_path.display(),
                err
            )
        })?)
    } else {
        None
    };
    let spec_digest = compute_fragment_spec_digest(
        &record.target.def_id,
        &record.target.mir_module_sha256,
        spec_src.as_deref(),
        fragment,
    );
    Ok(RecordFragmentCertificate {
        fragment,
        spec_digest,
        mir_module_found: mir_text.is_some(),
    })
}

/// Like `build_sorted_locked_records`, but attaches each record's re-derived
/// fragment certificate (`mir_fragment` + `spec_digest`). Also returns the
/// `def_id`s whose SHA-matching MIR module could not be found (fail-closed
/// `full_mir`), for verification diagnostics.
fn build_sorted_certified_records(
    workspace_root: &Path,
    records: &[UnitTargetRecord],
    units_dir: Option<&Path>,
) -> Result<(Vec<LockedUnitRecord>, BTreeSet<String>), String> {
    let mut by_def_id: BTreeMap<String, LockedUnitRecord> = BTreeMap::new();
    let mut missing_mir = BTreeSet::new();
    for rec in records {
        let cert = compute_record_fragment_certificate(workspace_root, rec, units_dir)?;
        let mut locked = LockedUnitRecord::from_unit_record(rec);
        locked.mir_fragment = Some(cert.fragment.as_str().to_string());
        locked.spec_digest = Some(cert.spec_digest);
        if cert.mir_module_found {
            missing_mir.remove(&locked.def_id);
        } else {
            missing_mir.insert(locked.def_id.clone());
        }
        by_def_id.insert(locked.def_id.clone(), locked);
    }
    Ok((by_def_id.into_values().collect(), missing_mir))
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
    lock_workspace_specs_with_options(workspace_root, records, mutable_patterns, None)
}

/// Lock workspace specifications into `.anneal/spec-lock.json` and optionally
/// mirror the signed manifest to `external_lock_file` (outside the agent's
/// writable workspace).
pub fn lock_workspace_specs_with_options(
    workspace_root: &Path,
    records: &[UnitTargetRecord],
    mutable_patterns: &[String],
    external_lock_file: Option<&Path>,
) -> Result<PathBuf, String> {
    lock_workspace_specs_with_units_dir(
        workspace_root,
        records,
        mutable_patterns,
        external_lock_file,
        None,
    )
}

/// `lock_workspace_specs_with_options` that also searches the CLI's
/// (possibly custom, `--units-dir`) `units_dir` for each record's captured
/// MIR when certifying its `mir_fragment`.
pub(crate) fn lock_workspace_specs_with_units_dir(
    workspace_root: &Path,
    records: &[UnitTargetRecord],
    mutable_patterns: &[String],
    external_lock_file: Option<&Path>,
    units_dir: Option<&Path>,
) -> Result<PathBuf, String> {
    let mut mutable_set = BTreeSet::new();
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

    check_specs_non_vacuous_with_records(workspace_root, records)?;
    let (locked_records, _) = build_sorted_certified_records(workspace_root, records, units_dir)?;
    let locked_specs_files =
        collect_locked_file_digests(workspace_root, "anneal/proofs/Specs")?;
    let locked_assumptions_files =
        collect_locked_file_digests(workspace_root, "anneal/proofs/Assumptions")?;

    let mut manifest = SpecLockManifest {
        schema: SPEC_LOCK_SCHEMA_V1.to_string(),
        locked_records,
        locked_specs_files,
        locked_assumptions_files,
        mutable_subjects: mutable_set.into_iter().collect(),
        spec_digest: None,
    };
    manifest.spec_digest = Some(compute_spec_lock_manifest_digest(&manifest));

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
    fs::write(&lock_path, &json).map_err(|err| {
        format!(
            "failed to write spec-lock manifest {}: {}",
            lock_path.display(),
            err
        )
    })?;

    if let Some(ext_path) = external_lock_file {
        if let Some(parent) = ext_path.parent()
            && !parent.as_os_str().is_empty()
        {
            fs::create_dir_all(parent).map_err(|err| {
                format!(
                    "failed to create external lock directory {}: {}",
                    parent.display(),
                    err
                )
            })?;
        }
        fs::write(ext_path, &json).map_err(|err| {
            format!(
                "failed to write external spec-lock manifest {}: {}",
                ext_path.display(),
                err
            )
        })?;
    }

    Ok(lock_path)
}

/// Verify that `current_records` and the on-disk `anneal/proofs/Specs/**` and
/// `anneal/proofs/Assumptions/**` trees match `.anneal/spec-lock.json`, and
/// reject vacuous specification overrides.
pub fn verify_spec_lock(
    workspace_root: &Path,
    current_records: &[UnitTargetRecord],
) -> Result<SpecLockManifest, String> {
    verify_spec_lock_with_options(workspace_root, current_records, None, None)
}

/// Verify specification lock against `.anneal/spec-lock.json`, an external
/// `--lock-file <PATH>` stored outside the agent's writable directory, or a
/// Git-committed `--lock-git-ref <REV>` (`HEAD`, `origin/main`, etc.).
pub fn verify_spec_lock_with_options(
    workspace_root: &Path,
    current_records: &[UnitTargetRecord],
    external_lock_file: Option<&Path>,
    lock_git_ref: Option<&str>,
) -> Result<SpecLockManifest, String> {
    verify_spec_lock_with_units_dir(
        workspace_root,
        current_records,
        external_lock_file,
        lock_git_ref,
        None,
    )
}

/// `verify_spec_lock_with_options` that also searches the CLI's (possibly
/// custom, `--units-dir`) `units_dir` for each record's captured MIR when
/// re-deriving fragment certificates. `verify_workspace_with_options` runs the
/// lock check *before* re-scaffolding `.anneal/generated/Mir`, so this matters
/// when the disposable generated tree was cleaned.
pub(crate) fn verify_spec_lock_with_units_dir(
    workspace_root: &Path,
    current_records: &[UnitTargetRecord],
    external_lock_file: Option<&Path>,
    lock_git_ref: Option<&str>,
    units_dir: Option<&Path>,
) -> Result<SpecLockManifest, String> {
    let workspace_lock_path = workspace_root.join(SPEC_LOCK_REL_PATH);
    let (raw, source_desc) = if let Some(git_ref) = lock_git_ref {
        let git_raw = load_spec_lock_from_git_ref(workspace_root, git_ref)?;
        if workspace_lock_path.is_file() {
            let on_disk_raw = fs::read_to_string(&workspace_lock_path).map_err(|err| {
                format!(
                    "failed to read spec-lock manifest {}: {}",
                    workspace_lock_path.display(),
                    err
                )
            })?;
            if sha256_hex(on_disk_raw.as_bytes()) != sha256_hex(git_raw.as_bytes()) {
                return Err(format!(
                    "spec-lock violation: on-disk {} was modified relative to git ref '{git_ref}' (re-running `cargo anneal lock-specs` during locked verification is forbidden)",
                    workspace_lock_path.display()
                ));
            }
        }
        (
            git_raw,
            format!("{git_ref}:{}", workspace_lock_path.display()),
        )
    } else if let Some(ext_path) = external_lock_file {
        if !ext_path.is_file() {
            return Err(format!(
                "missing external spec-lock manifest at {}",
                ext_path.display()
            ));
        }
        let ext_raw = fs::read_to_string(ext_path).map_err(|err| {
            format!(
                "failed to read external spec-lock manifest {}: {}",
                ext_path.display(),
                err
            )
        })?;
        if workspace_lock_path.is_file() {
            let on_disk_raw = fs::read_to_string(&workspace_lock_path).map_err(|err| {
                format!(
                    "failed to read spec-lock manifest {}: {}",
                    workspace_lock_path.display(),
                    err
                )
            })?;
            if sha256_hex(on_disk_raw.as_bytes()) != sha256_hex(ext_raw.as_bytes()) {
                return Err(format!(
                    "spec-lock violation: on-disk {} differs from external lock file {} (re-running `cargo anneal lock-specs` during locked verification is forbidden)",
                    workspace_lock_path.display(),
                    ext_path.display()
                ));
            }
        }
        (ext_raw, ext_path.display().to_string())
    } else {
        if !workspace_lock_path.is_file() {
            return Err(format!(
                "missing spec-lock manifest at {}; run `cargo anneal lock-specs` before running locked verification",
                workspace_lock_path.display()
            ));
        }
        let on_disk = fs::read_to_string(&workspace_lock_path).map_err(|err| {
            format!(
                "failed to read spec-lock manifest {}: {}",
                workspace_lock_path.display(),
                err
            )
        })?;
        (on_disk, workspace_lock_path.display().to_string())
    };

    let manifest = SpecLockManifest::from_json_str(&raw).map_err(|err| {
        format!("malformed spec-lock manifest {source_desc}: {err}")
    })?;

    // 1. Integrity of the lock file itself (schema, duplicate entries, and
    //    the manifest-level `spec_digest`).
    verify_spec_lock_manifest_integrity(&manifest, &source_desc)?;

    // 2. Captured records (identity, roles, and MIR digests).
    let current_locked = build_sorted_locked_records(current_records);
    verify_locked_records_match(&manifest.locked_records, &current_locked, &manifest.mutable_subjects)?;

    // 3. Authored `Specs/**` and `Assumptions/**` trees.
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

    // 4. Per-record `MirFragment` certificates, re-derived from the workspace.
    //    Legacy manifests (no certificates anywhere, as enforced by step 1)
    //    skip this step and verify exactly as before; the guard also accepts
    //    any record-level certificate (defense in depth should step 1 change).
    if manifest.spec_digest.is_some()
        || manifest
            .locked_records
            .iter()
            .any(LockedUnitRecord::has_fragment_certificate)
    {
        let (current_certified, missing_mir) =
            build_sorted_certified_records(workspace_root, current_records, units_dir)?;
        verify_locked_record_certificates(
            &manifest.locked_records,
            &current_certified,
            &manifest.mutable_subjects,
            &missing_mir,
        )?;
    }

    check_specs_non_vacuous_with_records(workspace_root, current_records)?;

    Ok(manifest)
}

/// Verify the manifest-level invariants of a parsed `.anneal/spec-lock.json`;
/// every consumer (`agent-verify`, `agent-sandbox`, and the `lock-specs`
/// report) runs this same check before trusting any field.
///
/// The schema must be `anneal.spec-lock.v1`, and no record, locked file, or
/// `mutable_subjects` entry may be duplicated (`lock-specs` writes each at
/// most once). Certificates are all-or-nothing: either the manifest is a legacy
/// certificate-free `anneal.spec-lock.v1` lock (no manifest `spec_digest` and no
/// record `mir_fragment` / `spec_digest`), which verifies exactly as before, or
/// it carries a manifest `spec_digest` *and* every record carries both
/// `mir_fragment` and `spec_digest` — the only two shapes `lock-specs` writes.
/// A mixed shape means certificates were partially stripped (a downgrade
/// attempt) and is rejected. When present, the manifest `spec_digest` must
/// equal `compute_spec_lock_manifest_digest` recomputed from the parsed payload,
/// which detects modification of any locked field (records, fragments, record
/// digests, `locked_specs_files`, `locked_assumptions_files`, or
/// `mutable_subjects`) after `lock-specs`.
pub(crate) fn verify_spec_lock_manifest_integrity(
    manifest: &SpecLockManifest,
    source_desc: &str,
) -> Result<(), String> {
    if manifest.schema != SPEC_LOCK_SCHEMA_V1 {
        return Err(format!(
            "unsupported schema '{}' in {source_desc} (expected '{}')",
            manifest.schema, SPEC_LOCK_SCHEMA_V1
        ));
    }
    // `lock-specs` never writes duplicate entries (records are keyed by
    // `def_id`, files by `rel_path`, `mutable_subjects` is a set); a duplicate
    // would be silently collapsed by the map- and `any`-based comparisons
    // below, so reject it outright.
    let mut seen_def_ids = BTreeSet::new();
    for rec in &manifest.locked_records {
        if !seen_def_ids.insert(rec.def_id.as_str()) {
            return Err(format!(
                "spec-lock violation: duplicate locked record '{}' in {source_desc}",
                rec.def_id
            ));
        }
    }
    let mut seen_subjects = BTreeSet::new();
    for subject in &manifest.mutable_subjects {
        if !seen_subjects.insert(subject.as_str()) {
            return Err(format!(
                "spec-lock violation: duplicate 'mutable_subjects' entry '{subject}' in {source_desc}"
            ));
        }
    }
    for (key, files) in [
        ("locked_specs_files", &manifest.locked_specs_files),
        ("locked_assumptions_files", &manifest.locked_assumptions_files),
    ] {
        let mut seen_paths = BTreeSet::new();
        for entry in files {
            if !seen_paths.insert(entry.rel_path.as_str()) {
                return Err(format!(
                    "spec-lock violation: duplicate '{key}' entry '{}' in {source_desc}",
                    entry.rel_path
                ));
            }
        }
    }

    let Some(recorded) = &manifest.spec_digest else {
        if let Some(rec) = manifest
            .locked_records
            .iter()
            .find(|r| r.has_fragment_certificate())
        {
            return Err(format!(
                "spec-lock violation: locked record '{}' in {source_desc} carries a mir_fragment/spec_digest certificate but the manifest-level spec_digest is missing (certificates were partially stripped or tampered after `cargo anneal lock-specs`)",
                rec.def_id
            ));
        }
        return Ok(());
    };
    if let Some(rec) = manifest
        .locked_records
        .iter()
        .find(|r| r.mir_fragment.is_none() || r.spec_digest.is_none())
    {
        return Err(format!(
            "spec-lock violation: locked record '{}' in {source_desc} lacks its mir_fragment/spec_digest certificate although the manifest carries a spec_digest (certificates were partially stripped or tampered after `cargo anneal lock-specs`)",
            rec.def_id
        ));
    }
    let recomputed = compute_spec_lock_manifest_digest(manifest);
    if *recorded != recomputed {
        return Err(format!(
            "spec-lock violation: manifest spec_digest mismatch in {source_desc} (recorded {recorded}, recomputed {recomputed}); the lock file was modified after `cargo anneal lock-specs`"
        ));
    }
    Ok(())
}

fn load_spec_lock_from_git_ref(workspace_root: &Path, git_ref: &str) -> Result<String, String> {
    let toplevel_out = std::process::Command::new("git")
        .arg("-C")
        .arg(workspace_root)
        .arg("rev-parse")
        .arg("--show-toplevel")
        .output()
        .map_err(|err| format!("failed to invoke git rev-parse: {err}"))?;
    if !toplevel_out.status.success() {
        return Err(format!(
            "git rev-parse --show-toplevel failed in {}: {}",
            workspace_root.display(),
            String::from_utf8_lossy(&toplevel_out.stderr).trim()
        ));
    }
    let git_root = PathBuf::from(String::from_utf8_lossy(&toplevel_out.stdout).trim());
    let abs_ws = workspace_root
        .canonicalize()
        .unwrap_or_else(|_| workspace_root.to_path_buf());
    let abs_git = git_root
        .canonicalize()
        .unwrap_or_else(|_| git_root.clone());
    let ws_rel = abs_ws.strip_prefix(&abs_git).unwrap_or(Path::new(""));
    let lock_git_path = if ws_rel.as_os_str().is_empty() {
        SPEC_LOCK_REL_PATH.to_string()
    } else {
        let prefix = ws_rel
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/");
        format!("{prefix}/{SPEC_LOCK_REL_PATH}")
    };
    let spec = format!("{git_ref}:{lock_git_path}");
    let show_out = std::process::Command::new("git")
        .arg("-C")
        .arg(&git_root)
        .arg("show")
        .arg(&spec)
        .output()
        .map_err(|err| format!("failed to invoke git show {spec}: {err}"))?;
    if !show_out.status.success() {
        return Err(format!(
            "failed to read spec-lock from git ref '{spec}': {}",
            String::from_utf8_lossy(&show_out.stderr).trim()
        ));
    }
    String::from_utf8(show_out.stdout)
        .map_err(|err| format!("invalid UTF-8 in git ref '{spec}': {err}"))
}

/// Run an external agent or shell command (`command_args`) inside an OS-level
/// read-only filesystem sandbox (`bwrap` when available on Linux) that permits
/// writes only to `anneal/proofs/Proof/**` (and `src/**` when `mutable_subjects`
/// is non-empty in `.anneal/spec-lock.json`), while mounting
/// `.anneal/spec-lock.json`, `anneal/proofs/Specs/**`,
/// `anneal/proofs/Assumptions/**`, and `Cargo.toml` strictly read-only.
///
/// Re-verifies `.anneal/spec-lock.json` and `Specs/**` / `Assumptions/**` digests
/// against a pre-execution snapshot before returning.
pub fn run_agent_sandbox(
    workspace_root: &Path,
    external_lock_file: Option<&Path>,
    command_args: &[String],
) -> Result<(), String> {
    if command_args.is_empty() {
        return Err(
            "missing command for `cargo anneal agent-sandbox -- <COMMAND> [ARGS...]`".to_string(),
        );
    }
    let abs_ws = workspace_root
        .canonicalize()
        .unwrap_or_else(|_| workspace_root.to_path_buf());
    let lock_path = external_lock_file
        .map(Path::to_path_buf)
        .unwrap_or_else(|| abs_ws.join(SPEC_LOCK_REL_PATH));
    if !lock_path.is_file() {
        return Err(format!(
            "missing spec-lock manifest at {}; run `cargo anneal lock-specs` before `agent-sandbox`",
            lock_path.display()
        ));
    }
    let pre_lock_raw = fs::read_to_string(&lock_path)
        .map_err(|err| format!("failed to read {}: {err}", lock_path.display()))?;
    let manifest = SpecLockManifest::from_json_str(&pre_lock_raw)?;
    // `mutable_subjects` decides below whether `src/` is mounted writable, so
    // the lock file must pass its integrity check before it is trusted.
    verify_spec_lock_manifest_integrity(&manifest, &lock_path.display().to_string())?;

    let proof_dir = abs_ws.join("anneal/proofs/Proof");
    fs::create_dir_all(&proof_dir)
        .map_err(|err| format!("failed to create {}: {err}", proof_dir.display()))?;
    let lake_dir = abs_ws.join(".anneal/.lake");
    fs::create_dir_all(&lake_dir)
        .map_err(|err| format!("failed to create {}: {err}", lake_dir.display()))?;
    let target_dir = abs_ws.join("target");
    fs::create_dir_all(&target_dir)
        .map_err(|err| format!("failed to create {}: {err}", target_dir.display()))?;

    let has_bwrap = std::process::Command::new("bwrap")
        .arg("--version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .is_ok_and(|s| s.success());

    let status = if has_bwrap {
        let mut cmd = std::process::Command::new("bwrap");
        cmd.arg("--ro-bind")
            .arg("/")
            .arg("/")
            .arg("--dev")
            .arg("/dev")
            .arg("--proc")
            .arg("/proc")
            .arg("--bind")
            .arg("/tmp")
            .arg("/tmp")
            .arg("--bind")
            .arg(&proof_dir)
            .arg(&proof_dir)
            .arg("--bind")
            .arg(&lake_dir)
            .arg(&lake_dir)
            .arg("--bind")
            .arg(&target_dir)
            .arg(&target_dir);
        if !manifest.mutable_subjects.is_empty() {
            let src_dir = abs_ws.join("src");
            if src_dir.is_dir() {
                cmd.arg("--bind").arg(&src_dir).arg(&src_dir);
            }
        }
        // Explicitly bind-mount protected specification and lock files read-only.
        let ws_lock = abs_ws.join(SPEC_LOCK_REL_PATH);
        if ws_lock.is_file() {
            cmd.arg("--ro-bind").arg(&ws_lock).arg(&ws_lock);
        }
        for ro_rel in ["anneal/proofs/Specs", "anneal/proofs/Assumptions", "Cargo.toml"] {
            let p = abs_ws.join(ro_rel);
            if p.exists() {
                cmd.arg("--ro-bind").arg(&p).arg(&p);
            }
        }
        cmd.arg("--chdir").arg(&abs_ws).arg("--");
        for arg in command_args {
            cmd.arg(arg);
        }
        cmd.status()
            .map_err(|err| format!("failed to execute bwrap sandbox: {err}"))?
    } else {
        let mut cmd = std::process::Command::new(&command_args[0]);
        cmd.args(&command_args[1..]).current_dir(&abs_ws);
        cmd.status()
            .map_err(|err| format!("failed to execute '{}': {err}", command_args[0]))?
    };

    // Re-verify lockfile and locked directories against the pre-sandbox snapshot.
    let ws_lock_path = abs_ws.join(SPEC_LOCK_REL_PATH);
    if !ws_lock_path.is_file() {
        return Err(format!(
            "spec-lock violation: {} was deleted during agent execution",
            ws_lock_path.display()
        ));
    }
    let post_lock_raw = fs::read_to_string(&ws_lock_path)
        .map_err(|err| format!("failed to read {}: {err}", ws_lock_path.display()))?;
    if sha256_hex(post_lock_raw.as_bytes()) != sha256_hex(pre_lock_raw.as_bytes()) {
        return Err(format!(
            "spec-lock violation: {} was modified during agent execution",
            ws_lock_path.display()
        ));
    }
    let post_specs = collect_locked_file_digests(&abs_ws, "anneal/proofs/Specs")?;
    verify_file_digests_match(
        "Specs",
        "anneal/proofs/Specs",
        &manifest.locked_specs_files,
        &post_specs,
    )?;
    let post_assumptions = collect_locked_file_digests(&abs_ws, "anneal/proofs/Assumptions")?;
    verify_file_digests_match(
        "Assumptions",
        "anneal/proofs/Assumptions",
        &manifest.locked_assumptions_files,
        &post_assumptions,
    )?;

    if !status.success() {
        return Err(format!(
            "sandboxed agent command exited with non-zero status: {status}"
        ));
    }
    Ok(())
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
        let is_designated_mutable = is_designated_mutable_subject(exp, act, mutable_subjects);
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

/// Whether `exp` / `act` is a `subject` record designated mutable by
/// `lock-specs --allow-impl-edit` (`mutable_subjects`). Only the subject's own
/// implementation body may change: its `#[spec]` companions, external specs,
/// `Specs/**`, and `Assumptions/**` stay strictly locked.
fn is_designated_mutable_subject(
    exp: &LockedUnitRecord,
    act: &LockedUnitRecord,
    mutable_subjects: &[String],
) -> bool {
    exp.item_kind == "subject"
        && act.item_kind == "subject"
        && mutable_subjects.iter().any(|s| *s == exp.def_id)
}

/// Compare each locked record's `mir_fragment` / `spec_digest` certificate
/// against the certificate re-derived from the current workspace (`actual`,
/// from `build_sorted_certified_records`).
///
/// Runs after `verify_locked_records_match` (record identity, roles, and MIR
/// digests) and the `Specs/**` / `Assumptions/**` digest checks, so for every
/// non-mutable record the MIR bytes and authored spec are already known to be
/// unchanged, and a mismatch here means the certified fragment itself diverged
/// (a recorded fragment that the locked MIR does not support, a classifier
/// change, or a SHA-matching MIR module missing from disk — listed in
/// `missing_mir`).
///
/// `mutable_subjects` interplay: a designated mutable subject's *current* MIR
/// digest may legitimately differ from the locked one, so its current fragment
/// and `spec_digest` may differ too and are not compared — mirroring the
/// `mir_module_sha256` exemption in `verify_locked_records_match`. The lock
/// file itself is untouched by such an implementation edit, so the
/// manifest-level `spec_digest` (which signs the manifest as written at
/// `lock-specs` time, including the subject's locked certificate and the
/// `mutable_subjects` list) still verifies.
fn verify_locked_record_certificates(
    expected: &[LockedUnitRecord],
    actual: &[LockedUnitRecord],
    mutable_subjects: &[String],
    missing_mir: &BTreeSet<String>,
) -> Result<(), String> {
    let actual_map: BTreeMap<&str, &LockedUnitRecord> =
        actual.iter().map(|r| (r.def_id.as_str(), r)).collect();
    for exp in expected {
        let def_id = exp.def_id.as_str();
        let Some(act) = actual_map.get(def_id) else {
            return Err(format!(
                "spec-lock violation: locked item '{def_id}' is missing from current capture records (narrowing targets with `--filter` or deleting items is forbidden)"
            ));
        };
        if is_designated_mutable_subject(exp, act, mutable_subjects) {
            continue;
        }
        let missing_hint = if missing_mir.contains(def_id) {
            format!(
                " (no captured MIR module matching mir_module_sha256 {} was found under .anneal/generated/Mir, target/anneal/units, or --units-dir, so the fragment was re-derived fail-closed as `full_mir`; re-run extraction before locked verification)",
                exp.mir_module_sha256
            )
        } else {
            String::new()
        };
        if let Some(locked_frag) = &exp.mir_fragment
            && act.mir_fragment.as_ref() != Some(locked_frag)
        {
            return Err(format!(
                "spec-lock violation: mir_fragment for '{def_id}' changed from '{locked_frag}' to '{}'{missing_hint}",
                act.mir_fragment.as_deref().unwrap_or("<none>")
            ));
        }
        if let Some(locked_digest) = &exp.spec_digest
            && act.spec_digest.as_ref() != Some(locked_digest)
        {
            return Err(format!(
                "spec-lock violation: spec_digest for '{def_id}' changed (expected {locked_digest}, got {}); the locked (def_id, mir_module_sha256, authored Specs/<Item>.lean, mir_fragment) certificate no longer matches{missing_hint}",
                act.spec_digest.as_deref().unwrap_or("<none>")
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

    let mut bundles = group_subject_obligations(records);
    crate::scaffold::populate_called_callees(
        &workspace_root.join(".anneal/generated/Mir"),
        records,
        &mut bundles,
    );
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
            if let Some(weakening) = detect_tautological_ensures_weakening(&stripped_spec) {
                return Err(format!(
                    "spec override in {} trivializes the Rust #[spec] `ensures` clause via `{weakening}`",
                    spec_rel.display()
                ));
            }
        }

        // Check 4b: When the item has `#[external_spec]` callees or sibling
        // `#[spec]` `called_callees` and `Specs/<Item>.lean` overrides
        // `ModularItemSpec`, verify that it preserves every generated external
        // and sibling call contract unless opted out.
        let mut required_ext_contracts: Vec<String> = bundles_by_rel_path
            .get(item_rel_path)
            .map(|b| {
                b.external_spec_callees
                    .iter()
                    .map(crate::obligations::external_call_contract_ident)
                    .collect()
            })
            .unwrap_or_default();
        for disk_contract in obligation_file_external_call_contracts(workspace_root, item_rel_path) {
            if !required_ext_contracts.contains(&disk_contract) {
                required_ext_contracts.push(disk_contract);
            }
        }
        let mut required_called_callees: Vec<String> = bundles_by_rel_path
            .get(item_rel_path)
            .map(|b| {
                b.called_callees
                    .iter()
                    .map(|c| c.item_module_suffix.clone())
                    .collect()
            })
            .unwrap_or_default();
        for disk_callee in obligation_file_called_callees(workspace_root, item_rel_path) {
            if !required_called_callees.contains(&disk_callee) {
                required_called_callees.push(disk_callee);
            }
        }
        let has_external_spec_callees = !required_ext_contracts.is_empty()
            || obligation_file_has_external_spec_callees(workspace_root, item_rel_path);
        let has_called_callees = !required_called_callees.is_empty();

        if (has_external_spec_callees || has_called_callees)
            && !content.contains("-- @anneal-allow-replace-rust-spec")
        {
            let stripped_spec = strip_lean_comments(&content);
            if stripped_spec.contains("ModularItemSpec")
                || stripped_spec.contains("refineModularSpec")
            {
                let preserves_ext_contracts = !has_external_spec_callees
                    || stripped_spec.contains("defaultModularSpec.envAssumed")
                    || (required_ext_contracts.len() <= 1
                        && stripped_spec.contains("defaultExternalCallContract"))
                    || (!required_ext_contracts.is_empty()
                        && required_ext_contracts
                            .iter()
                            .all(|c| stripped_spec.contains(c.as_str())));
                let preserves_called_callees = !has_called_callees
                    || stripped_spec.contains("defaultModularSpec.envAssumed")
                    || required_called_callees.iter().all(|callee| {
                        stripped_spec.contains(&format!("Obligations.{callee}."))
                            || stripped_spec.contains(&format!("Specs.{callee}."))
                    });
                if !preserves_ext_contracts || !preserves_called_callees {
                    return Err(format!(
                        "spec override in {} drops the Rust #[external_spec] call contract in `ModularItemSpec.envAssumed`; reference `Obligations.{item_suffix}.defaultModularSpec.envAssumed`, `Obligations.{item_suffix}.defaultExternalCallContract`, or all `Obligations.{item_suffix}.externalCallContract_*` and `Obligations.<Callee>.defaultCallContract` contracts (or add `-- @anneal-allow-replace-rust-spec`)",
                        spec_rel.display()
                    ));
                }
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
                    trait_impls: Vec::new(),
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

fn obligation_file_has_external_spec_callees(workspace_root: &Path, item_rel_path: &Path) -> bool {
    let ob_path = workspace_root
        .join(".anneal/generated/Obligations")
        .join(item_rel_path);
    let Ok(ob_text) = fs::read_to_string(ob_path) else {
        return false;
    };
    ob_text.contains("def externalCallContract_")
        || ob_text.contains("abbrev defaultExternalCallContract")
}

fn obligation_file_external_call_contracts(
    workspace_root: &Path,
    item_rel_path: &Path,
) -> Vec<String> {
    let ob_path = workspace_root
        .join(".anneal/generated/Obligations")
        .join(item_rel_path);
    let Ok(ob_text) = fs::read_to_string(ob_path) else {
        return Vec::new();
    };
    let mut contracts = Vec::new();
    for line in ob_text.lines() {
        let trimmed = line.trim();
        if let Some(after) = trimmed.strip_prefix("def externalCallContract_") {
            let ident_suffix: String = after
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if !ident_suffix.is_empty() {
                let full_ident = format!("externalCallContract_{ident_suffix}");
                if !contracts.contains(&full_ident) {
                    contracts.push(full_ident);
                }
            }
        }
    }
    contracts
}

fn obligation_file_called_callees(workspace_root: &Path, item_rel_path: &Path) -> Vec<String> {
    let ob_path = workspace_root
        .join(".anneal/generated/Obligations")
        .join(item_rel_path);
    let Ok(ob_text) = fs::read_to_string(ob_path) else {
        return Vec::new();
    };
    let mut callees = Vec::new();
    let needle = ".defaultCallContract.holdsOn";
    for line in ob_text.lines() {
        let mut rest = line.trim();
        while let Some(end_idx) = rest.find(needle) {
            let before = &rest[..end_idx];
            if let Some(ob_idx) = before.rfind("Obligations.") {
                let suffix = &before[ob_idx + "Obligations.".len()..];
                if !suffix.is_empty()
                    && suffix
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.')
                    && !callees.contains(&suffix.to_string())
                {
                    callees.push(suffix.to_string());
                }
            }
            rest = &rest[end_idx + needle.len()..];
        }
    }
    callees
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
        "envAssumed := fun _ => False",
        "envAssumed := fun h => False",
        "envAssumed := fun (_ : ExternalCallHandler) => False",
        "envAssumed := fun (h : ExternalCallHandler) => False",
        "envAssumed := False",
        "envAssumed _ := False",
        "envAssumed h := False",
        "def envAssumed (h : ExternalCallHandler) : Prop := False",
        "def envAssumed (_ : ExternalCallHandler) : Prop := False",
        "def envAssumed : ExternalCallHandler → Prop := fun _ => False",
        "def envAssumed : ExternalCallHandler -> Prop := fun _ => False",
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
        "refineModularSpec (fun _ => False)",
        "refineModularSpec (fun h => False)",
        "refineModularSpec (fun (_ : ExternalCallHandler) => False)",
        "refineModularSpec (fun (h : ExternalCallHandler) => False)",
        "refineModularSpec envAssumed (fun _ _ => False)",
        "refineModularSpec _ (fun _ _ => False)",
        "∧ False",
        "False ∧",
        "And False",
        "=> 0 = 1",
        "=> 1 = 0",
        ":= 0 = 1",
        ":= 1 = 0",
        "=> true = false",
        "=> false = true",
        ":= true = false",
        ":= false = true",
        "=> ¬ True",
        "=> ¬True",
        "=> Not True",
        ":= ¬ True",
        ":= Not True",
    ];

    for &pattern in FORBIDDEN_PATTERNS {
        if collapsed.contains(pattern) {
            return Some(pattern);
        }
    }
    None
}

fn detect_tautological_ensures_weakening(stripped_lean_src: &str) -> Option<&'static str> {
    let collapsed = stripped_lean_src
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");

    const WEAKENING_PATTERNS: &[&str] = &[
        "∨ True",
        "True ∨",
        "Or True",
        "rustEnsures args ret → True",
        "rustEnsures args ret -> True",
        "defaultPost args ret → True",
        "defaultPost args ret -> True",
    ];

    for &pattern in WEAKENING_PATTERNS {
        if collapsed.contains(pattern) {
            return Some(pattern);
        }
    }
    None
}

pub(crate) fn is_lean_ident_char(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '\''
}

/// Return the byte length of a Lean 4 character literal starting at byte `i`
/// (`src.as_bytes()[i] == b'\''`), or `None` when `'` is an identifier prime
/// (`c'`, `s''`) or an unclosed apostrophe.
pub(crate) fn lean_char_literal_len(
    src: &str,
    i: usize,
    prev_ch: Option<char>,
) -> Option<usize> {
    if src.as_bytes().get(i).copied() != Some(b'\'') {
        return None;
    }
    if prev_ch.is_some_and(is_lean_ident_char) {
        return None;
    }
    let after_open = src.get(i + 1..)?;
    let first = after_open.chars().next()?;
    if first == '\'' || first == '\n' || first == '\r' {
        return None;
    }
    if first != '\\' {
        let rest = &after_open[first.len_utf8()..];
        return rest.starts_with('\'').then_some(1 + first.len_utf8() + 1);
    }
    let after_slash = &after_open[1..];
    if let Some(hex_rest) = after_slash.strip_prefix('x') {
        let hex = hex_rest.get(..2)?;
        if hex.bytes().all(|b| b.is_ascii_hexdigit()) && hex_rest[2..].starts_with('\'') {
            return Some(6);
        }
        return None;
    }
    if let Some(uni_rest) = after_slash.strip_prefix('u') {
        let hex = uni_rest.get(..4)?;
        if hex.bytes().all(|b| b.is_ascii_hexdigit()) && uni_rest[4..].starts_with('\'') {
            return Some(8);
        }
        return None;
    }
    let esc = after_slash.chars().next()?;
    if esc == '\n' || esc == '\r' {
        return None;
    }
    let rest = &after_slash[esc.len_utf8()..];
    rest.starts_with('\'').then_some(2 + esc.len_utf8() + 1)
}

pub(crate) fn strip_lean_comments(input: &str) -> String {
    let bytes = input.as_bytes();
    let mut out = String::with_capacity(input.len());
    let mut i = 0;
    let mut block_depth = 0usize;
    let mut in_str = false;
    let mut prev_ch: Option<char> = None;

    while i < bytes.len() {
        if block_depth > 0 {
            if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'-' {
                block_depth += 1;
                i += 2;
            } else if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'/' {
                block_depth -= 1;
                i += 2;
                if block_depth == 0 {
                    out.push(' ');
                    prev_ch = None;
                }
            } else {
                // Keep line structure: a multi-line block comment must not
                // glue the lines around it together.
                if bytes[i] == b'\n' {
                    out.push('\n');
                }
                i += 1;
            }
            continue;
        }

        if in_str {
            if bytes[i] == b'\\' {
                out.push('\\');
                i += 1;
                if let Some(ch) = input[i..].chars().next() {
                    out.push(ch);
                    i += ch.len_utf8();
                }
            } else if bytes[i] == b'"' {
                in_str = false;
                out.push('"');
                i += 1;
                prev_ch = None;
            } else if let Some(ch) = input[i..].chars().next() {
                out.push(ch);
                i += ch.len_utf8();
            } else {
                break;
            }
            continue;
        }

        if bytes[i] == b'"' {
            in_str = true;
            out.push('"');
            i += 1;
            prev_ch = None;
            continue;
        }

        // Preserve character literals (`'"'`, `'-'`, `'α'`, `'\x22'`) without
        // misclassifying identifier primes (`if c'<'"' then`).
        if let Some(char_len) = lean_char_literal_len(input, i, prev_ch) {
            out.push_str(&input[i..i + char_len]);
            i += char_len;
            prev_ch = None;
            continue;
        }

        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'-' {
            block_depth = 1;
            i += 2;
            prev_ch = None;
            continue;
        }

        if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'-' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            prev_ch = None;
            continue;
        }

        if let Some(ch) = input[i..].chars().next() {
            out.push(ch);
            i += ch.len_utf8();
            prev_ch = Some(ch);
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
    let mut all_bundles = group_subject_obligations(records);
    crate::scaffold::populate_called_callees(
        &workspace_root.join(".anneal/generated/Mir"),
        records,
        &mut all_bundles,
    );
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
    // Best-effort read of the lock file for each item's locked `mir_fragment`
    // (an unreadable or malformed lock file is reported by `agent-verify`,
    // not by the context renderer).
    let locked_manifest = if spec_lock_active {
        fs::read_to_string(&spec_lock_path)
            .ok()
            .and_then(|raw| parse_spec_lock_manifest(&raw).ok())
    } else {
        None
    };

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
    out.push_str(render_lifting_strategy_guide_section());

    for bundle in bundles {
        let def_id = &bundle.subject.target.def_id;
        let suffix = &bundle.item_module_suffix;
        let rel_lean = bundle
            .item_rel_path
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/");
        let mir_root = generated_root.join("Mir");
        let lifting_profile = analyze_workspace_lifting_profile(&mir_root, bundle);
        let raw_authored = detect_authored_item_modules(&proofs_root, &bundle.item_rel_path);
        let authored = crate::scaffold::effective_authored_for_bundle(
            bundle,
            raw_authored,
            Some(&lifting_profile),
        );
        let proof_status = if authored.has_proof {
            "Present"
        } else {
            "Missing"
        };
        let contract_surface = if authored.is_polymorphic {
            if authored.is_ub_exception {
                "polymorphic ub_exception (`polyUbExceptionClaim` / `CrateVerificationResult`)"
            } else if authored.is_modular {
                "polymorphic modular (`polyModularClaim` / `CrateVerificationResult`)"
            } else if authored.is_total {
                "polymorphic total (`polyTotalClaim` / `CrateVerificationResult`)"
            } else if authored.is_stateful {
                "polymorphic stateful (`polyStatefulClaim` / `CrateVerificationResult`)"
            } else {
                "polymorphic (`polyClaim` / `CrateVerificationResult`)"
            }
        } else if authored.is_ub_exception {
            "ub_exception (`UbExceptionItemSpec` / `UbExceptionVerificationResult`)"
        } else if authored.is_modular {
            "modular (`ModularItemSpec` / `ModularVerificationResult`)"
        } else if authored.is_equiv {
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
        let fragment_class = lifting_profile.fragment_classification();
        // `None` when no captured `Mir/<Item>.lean` body was parsed: the live
        // fragment is then only the fail-closed `full_mir`, not a measurement.
        let live_fragment = lifting_profile
            .has_captured_mir
            .then_some(fragment_class.inferred_fragment);
        let locked_fragment_line = locked_manifest.as_ref().and_then(|manifest| {
            let rec = manifest
                .locked_records
                .iter()
                .find(|r| r.def_id == *def_id)?;
            Some(render_locked_fragment_line(
                rec.mir_fragment.as_deref(),
                live_fragment,
            ))
        });

        out.push_str(&format!("## Item `{def_id}` (`{suffix}`)\n\n"));
        out.push_str(&format!("- **`def_id`**: `{def_id}`\n"));
        out.push_str(&format!("- **`item_module_suffix`**: `{suffix}`\n"));
        out.push_str(&format!("- **`is_stateful`**: {contract_surface}\n"));
        out.push_str(&format!("- **Proof Status**: {proof_status}\n"));
        out.push_str(&format!(
            "- **Writable Proof Path**: `anneal/proofs/Proof/{rel_lean}`\n"
        ));
        out.push_str(&format!(
            "- **MIR Fragment**: {}{}\n",
            render_mir_fragment_label(fragment_class.inferred_fragment),
            if live_fragment.is_some() {
                ""
            } else {
                " (fail-closed: no parsed captured `Mir/<Item>.lean` body)"
            }
        ));
        if let Some(line) = &locked_fragment_line {
            out.push_str(line);
        }
        out.push_str(&format!(
            "- **Companion Spec Count**: {companion_count} (requires: {}, ensures: {}, external: {})\n\n",
            bundle.inline_requires.len(),
            bundle.inline_ensures.len(),
            bundle.external_specs.len()
        ));
        if fragment_class.inferred_fragment > MirFragment::PureBoundedLoop
            && let Some(diagnostic) = render_mir_fragment_diagnostic(def_id, &fragment_class)
        {
            out.push_str(&format!(
                "### MIR Fragment Boundary Diagnostic\n\n```text\n{}\n```\n\n",
                diagnostic.trim_end()
            ));
        }

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

        if let Some(mir_disk) = crate::scaffold::resolve_workspace_mir_file(
            &mir_root,
            &bundle.subject,
            &bundle.item_rel_path,
        ) {
            let mir_text = fs::read_to_string(&mir_disk).map_err(|err| {
                format!("failed to read {}: {}", mir_disk.display(), err)
            })?;
            out.push_str(&format!(
                "### Captured MIR Module (`.anneal/generated/Mir/{rel_lean}`)\n\n```lean\n{}\n```\n\n",
                mir_text.trim_end()
            ));
        }

        out.push_str(&render_item_lifting_guidance(
            bundle,
            authored,
            &lifting_profile,
        ));

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
            let starter = render_proof_template_with_hints(bundle, authored, &lifting_profile);
            out.push_str(&format!(
                "### Starter Proof Template (`anneal/proofs/Proof/{rel_lean}`)\n\n```lean\n{}\n```\n\n",
                starter.trim_end()
            ));
        }
    }

    Ok(out)
}

/// `` `<tag>` (`<lean_ctor>`, rank <rank>) `` label of a `MirFragment`.
fn render_mir_fragment_label(frag: MirFragment) -> String {
    format!(
        "`{}` (`{}`, rank {})",
        frag.as_str(),
        frag.lean_ctor(),
        frag.to_rank()
    )
}

/// `- **Locked MIR Fragment**` bullet for an item recorded in
/// `.anneal/spec-lock.json`, comparing the locked certificate against the
/// fragment of the current capture (`None` when no captured body was parsed).
fn render_locked_fragment_line(locked: Option<&str>, current: Option<MirFragment>) -> String {
    const PREFIX: &str = "- **Locked MIR Fragment (`.anneal/spec-lock.json`)**:";
    match (locked.map(|tag| (tag, tag.parse::<MirFragment>())), current) {
        (Some((_, Ok(frag))), Some(current)) if frag == current => {
            format!("{PREFIX} {}\n", render_mir_fragment_label(frag))
        }
        (Some((_, Ok(frag))), Some(current)) => format!(
            "{PREFIX} {} (differs from the current capture's `{}`; `cargo anneal agent-verify` accepts this only for `--allow-impl-edit` subjects)\n",
            render_mir_fragment_label(frag),
            current.as_str()
        ),
        (Some((_, Ok(frag))), None) => format!(
            "{PREFIX} {} (no parsed captured `Mir/<Item>.lean` body to compare against)\n",
            render_mir_fragment_label(frag)
        ),
        (Some((tag, Err(_))), _) => format!("{PREFIX} invalid tag {tag:?}\n"),
        (None, _) => format!(
            "{PREFIX} not recorded (legacy certificate-free `anneal.spec-lock.v1` lock)\n"
        ),
    }
}

fn render_lifting_strategy_guide_section() -> &'static str {
    "## Proof Lifting Strategy Guide (Lift First, Evaluate Last)\n\n\
     - **`TrustedBoundary` & Zero-Fuel Discipline**:\n  \
       - `Proof/<Crate>/<Item>.lean` is re-parsed under `Init`/`Std` syntax by `TrustedBoundary.lean` (`elab`, `macro`, `syntax`, `sorry`, `native_decide`, and unauthorized `axiom` are rejected).\n  \
       - `#mir_lift` (`Anneal.MirLift`, emitting `<item>_model`, `<item>_lift_sound`, and `<item>_verified` or `LiftResidualBlock` under `residual := true`) is an interactive elaborator for closed (`argCount = 0`) bodies outside `TrustedBoundary`; inside `Proof/*.lean`, import `Anneal`, open the exact lifting namespaces (`open Anneal.PureMirExec Anneal.MirLiftCore`, plus `Anneal.MirFuelFree`, `Anneal.MirLoops`, or `Anneal.SepLogicLenses` as needed), and apply the lifting theorems directly with zero `BlockCtx` records and zero manual fuel or `iterate k` counts.\n\
     - **Pattern A — Pure Scalar/ADT/Array MIR (`#mir_lift` rules in `Anneal.PureMirExec` + `Anneal.MirLiftCore`)**:\n  \
       - Check `#eval Anneal.PureMirExec.checkPureMir Mir.<Item>.body`. When `true`, `open Anneal.PureMirExec Anneal.MirLiftCore` and bridge with `verifyMirNoPanic_of_pureExec`, `verifyMirSafe_of_pureExec`, `verifyTotalMir_of_pureExec`, or `verifyStatefulMirNoPanic_of_pureExec`.\n  \
       - Step blocks structurally via `lift_PureMirConverges (by rfl)`, `LiftBlock.of_lookup (by rfl)`, and `LiftStmtsTerminator.{cons_eval, cons_eval_norm, eval_rest, term_assert, term_switchInt, term_goto, term_drop, term_return}` (`eval_rest` / `cons_eval_norm` normalize `PureEnv` updates via `forcePureEnv?`).\n  \
       - For linked pure callees or modular call contracts, `open Anneal.PureMirExec` and use `checkPureMirWithCallees` (`verifyStatefulMirNoPanic_of_pureExecWithCallees_any`, `PureMirConverges.call_summary`) or `PureMirModularConverges` (`verifyModularMir_of_pureModularExec_any`).\n\
     - **Pattern B — Companion `#[spec]` Predicates (`#mir_lift_spec` theorems in `Anneal.PureMirExec`)**:\n  \
       - `open Anneal.PureMirExec`. When `checkPureMir` holds on a companion body, use the `#mir_lift_spec` theorem family (`mirBoolPredicateHolds_of_pureExec`, `mirBoolPredicateHolds_intro_of_pureExec`, `mirBoolPredicateHolds_elim_of_pureExec`, or `mirBoolPredicateHolds_elim_of_uniqueTruePath`, and `mirBoolPredicateHoldsWithCallees_of_checkPureMirBoolPredWithCallees` with `defaultSpecCallees`).\n  \
       - When a `#[spec]` companion captures arguments by `&` reference (`Rvalue.ref` / `ProjectionElem.deref`, so `checkPureMir = false`), invert `requires` via `holdBoolReq_of_mirBool` with count-free `repeat`, discharge `ensures` via `hold_mirBool_of_blockLinear` (`defaultSpecSteps`), and prove concrete witnesses via `mirBoolPredicateHolds_of_evalMirSpecBool_true`.\n\
     - **Pattern C — Loops (`forRangeUp` + `runCfgToBlock` in `Anneal.MirLoops` + `Anneal.PureMirExec` + `Anneal.MirFuelFree`)**:\n  \
       - `open Anneal.MirLoops Anneal.PureMirExec Anneal.MirFuelFree` and model `for i in lo..hi` / `while i < hi` loops with `forRangeUp` (`forRangeUp_induction`, `mirWpConverges_forRangeUp`, `mirNoCallWpConverges_forRangeUp`, or `mirWpConverges_whileRank` for rank-decreasing loops).\n  \
       - Step loop entry, single iterations, and exit to the loop-header block without step numerals via `runCfgToBlock` (`mirStepsConverges_of_runCfgToBlock`, `mirWpConverges_of_runCfgToBlock`, `mirNoCallWpConverges_of_runCfgToBlock`), and close with `verifyStatefulMirNoPanic_of_wpConverges`, `verifyStatefulEquivMir_of_wpConverges`, or `verifyUbExceptionMir_of_wpConverges`.\n\
     - **Pattern D — `&mut` References (`Anneal.SepLogicLenses`) & Shared `&` Reads**:\n  \
       - For `&mut` borrows, `open Anneal.SepLogicLenses Anneal.FunctionalTranslation Anneal.MirLiftCore`, erase Tree Borrows and `Memory` aliasing via whole-slot `SepLensStateInv` (`ActiveTypedMutBorrow`, `treeMemoryPtrMutLens`) or sibling-field `SepSubplaceLensStateInv` (`ActiveTypedFieldMutBorrow`, `treeFieldMemoryPtrMutLens`, `subplaceTreeMutLens`), derive `LiftLensBlock` (`LiftLensStmts`, `set?_of_forcePureEnv? rfl`), and conclude with `verifyStatefulMir_of_sepLenses`, `verifyStatefulMir_of_sepSubplaceLenses`, `mirWpConverges_of_sepLenses`, or `verifyTotalMir_of_sepLenses`.\n  \
       - For shared `&T` / `*const T` reads without `&mut` borrows, `open Anneal.PureMirExec Anneal.MirFuelFree Anneal.Rustc.V2026_06_01.SymbolicEval` and step intraprocedurally via `runCfgToBlock` (`mirWpConverges_of_runCfgToBlock`, `verifyStatefulMirNoPanic_of_wpConverges`) or `dischargeStatefulEqFuelFree` on concrete pinned memory.\n\
     - **Pattern E — Polymorphic MIR (`CapturedMir.instantiate`) & Bit-Validity (`Anneal.BitValidity`)**:\n  \
       - For generic items (`typeParamCount > 0` / `poly*Claim`), `open Trusted.MirAst Anneal.PureMirExec Anneal.MirLiftCore` (plus `Anneal.SepLogicLenses` or `Anneal.MirFuelFree` for stateful/loop bodies), introduce `typeArgs` and `h_len` (`*ClaimFor typeArgs` instantiates `Mir.<Item>.body.instantiate typeArgs` via `CapturedMir.instantiate` and `LayoutTable.instantiateForBody`), and discharge `*ClaimFor typeArgs` (`claimFor`, `statefulClaimFor`, `totalClaimFor`, `modularClaimFor`, `ubExceptionClaimFor`) with the fuel-free lifting theorems (`verifyMirNoPanic_of_pureExec`, `verifyStatefulMir_of_sepLenses`, or `verifyStatefulMirNoPanic_of_wpConverges`).\n  \
       - For `#[invariant]` and `#[unsafe_impl]` layout/transmutation proofs, `open Anneal.BitValidity` and use `ValidityMode`, `ByteSeqValid`, `IsUnaligned`, `IsFromZeros`, `IsFromBytes`, `IsIntoBytes`, `IsTryFromBytes`, `checkUnaligned_sound`, `checkFromZeros_sound`, `checkFromBytes_sound`, `checkIntoBytes_sound`, and `transmute_sound_of_into_from_bytes` over `Mir.<Item>.layouts`.\n\n"
}

fn render_item_lifting_guidance(
    bundle: &SubjectObligationBundle,
    authored: AuthoredItemModules,
    profile: &MirLiftingProfile,
) -> String {
    let item = &bundle.item_module_suffix;
    let effective = crate::scaffold::effective_authored_for_bundle(bundle, authored, Some(profile));
    let is_equiv = effective.is_equiv;
    let is_modular = effective.is_modular;
    let is_polymorphic = effective.is_polymorphic;
    let is_bit_validity_item = matches!(
        bundle.subject.item_kind,
        anneal_rustc_capture::CapturedItemKind::TypeInvariant
            | anneal_rustc_capture::CapturedItemKind::UnsafeTraitImpl
    );

    let mut out = String::from("### Recommended Lifting Strategy\n\n");
    if profile.has_captured_mir {
        out.push_str(&format!(
            "- **Detected MIR Profile**: {} basic block(s), `typeParamCount`: `{}`, `checkPureMir` candidate: `{}`, loops/back-edges: `{}`, deref projections: `{}`, mutable borrows: `{}`\n",
            profile.basic_block_count,
            profile.type_param_count,
            profile.is_pure_call_free_candidate(),
            profile.has_cfg_back_edge,
            profile.has_deref_projection,
            profile.has_mut_borrow,
        ));
    }

    if is_bit_validity_item {
        out.push_str(&format!(
            "- **Bit-Validity / Trait Route (`Anneal.BitValidity`)**: `open Anneal.BitValidity` and use `ValidityMode`, `ByteSeqValid`, `IsUnaligned`, `IsFromZeros`, `IsFromBytes`, `IsIntoBytes`, `IsTryFromBytes`, `checkUnaligned_sound`, `checkFromZeros_sound`, `checkFromBytes_sound`, `checkIntoBytes_sound`, and `transmute_sound_of_into_from_bytes` over `Mir.{item}.layouts`.\n"
        ));
    }
    if is_polymorphic {
        out.push_str(&format!(
            "- **Polymorphic MIR Route (`CapturedMir.instantiate`)**: `Mir.{item}.body` is generic (`typeParamCount > 0` or `poly*Claim`); `open Trusted.MirAst Anneal.PureMirExec Anneal.MirLiftCore` (plus `Anneal.SepLogicLenses` or `Anneal.MirFuelFree` for stateful/loop bodies), `intro typeArgs h_len` (`*ClaimFor typeArgs` instantiates `Mir.{item}.body.instantiate typeArgs` and `LayoutTable.instantiateForBody`), and discharge `*ClaimFor typeArgs` with the fuel-free lifting theorems (`verifyMirNoPanic_of_pureExec`, `verifyStatefulMir_of_sepLenses`, or `verifyStatefulMirNoPanic_of_wpConverges`).\n"
        ));
    }
    if profile.has_cfg_back_edge {
        out.push_str(&format!(
            "- **Primary Loop Route (`forRangeUp` + `runCfgToBlock`)**: `Mir.{item}.body` contains a CFG back-edge; `open Anneal.MirLoops Anneal.PureMirExec Anneal.MirFuelFree`, model loop state with `forRangeUp` (`mirWpConverges_forRangeUp` or `mirNoCallWpConverges_forRangeUp`), and discharge entry/step/exit segments via `runCfgToBlock` (`mirStepsConverges_of_runCfgToBlock`, `mirNoCallWpConverges_of_runCfgToBlock`).\n"
        ));
    }
    if profile.has_mut_borrow {
        out.push_str(&format!(
            "- **Reference / Borrow Route (`Anneal.SepLogicLenses`)**: `Mir.{item}.body` mutates or borrows `&mut` places; `open Anneal.SepLogicLenses Anneal.FunctionalTranslation Anneal.MirLiftCore`, establish `SepLensStateInv` (`ActiveTypedMutBorrow`) or `SepSubplaceLensStateInv` (`ActiveTypedFieldMutBorrow`), prove `LiftLensBlock Mir.{item}.body 0 ...` using `set?_of_forcePureEnv? rfl`, and apply `verifyStatefulMir_of_sepLenses` (or `verifyStatefulMir_of_sepSubplaceLenses`).\n"
        ));
    } else if profile.has_deref_projection {
        out.push_str(&format!(
            "- **Shared-Reference / Pointer Read Route (`Anneal.PureMirExec` + `Anneal.MirFuelFree`)**: `Mir.{item}.body` dereferences shared `&` or pointer places without `&mut` borrows (`ActiveTypedMutBorrow` requires `.active` `&mut` permission); `open Anneal.PureMirExec Anneal.MirFuelFree Anneal.Rustc.V2026_06_01.SymbolicEval` and step via `runCfgToBlock` (`mirWpConverges_of_runCfgToBlock`, `verifyStatefulMirNoPanic_of_wpConverges`) or `dischargeStatefulEqFuelFree` on pinned concrete memory.\n"
        ));
    }
    if is_modular || profile.has_callees_or_modular_contracts || profile.has_call_terminator {
        out.push_str(
            "- **Callee / Modular Route (`Anneal.PureMirExec`)**: `open Anneal.PureMirExec` and use `checkPureMirWithCallees` (`verifyStatefulMirNoPanic_of_pureExecWithCallees_any`, `PureMirConverges.call_summary`) for linked pure callees, or `PureMirModularConverges` + `verifyModularMir_of_pureModularExec_any` when modular call contracts are active.\n",
        );
    }
    if profile.is_pure_call_free_candidate() && !profile.has_cfg_back_edge && !is_modular {
        out.push_str(&format!(
            "- **Primary Pure Route (`#mir_lift` rules)**: `Mir.{item}.body` is a pure call-free candidate (`checkPureMir`); `open Anneal.PureMirExec Anneal.MirLiftCore` and apply `verifyMirNoPanic_of_pureExec` (or `verifyTotalMir_of_pureExec` / `verifyStatefulMirNoPanic_of_pureExec`), `lift_PureMirConverges (by rfl)`, `LiftBlock.of_lookup (by rfl)`, and `LiftStmtsTerminator.{{cons_eval, cons_eval_norm, eval_rest, term_*}}`.\n"
        ));
    } else if !profile.has_captured_mir {
        out.push_str(&format!(
            "- **Body Route**: test `#eval Anneal.PureMirExec.checkPureMir Mir.{item}.body`; lift pure bodies with `#mir_lift` rules (`open Anneal.PureMirExec Anneal.MirLiftCore`), loops with `forRangeUp` + `runCfgToBlock` (`open Anneal.MirLoops Anneal.PureMirExec Anneal.MirFuelFree`), and `&mut` borrows with `Anneal.SepLogicLenses`.\n"
        ));
    }
    if is_equiv {
        out.push_str(
            "- **Equivalence Route (`#[spec(equivalent_to: ...)]`)**: `open Anneal.PureMirExec Anneal.MirFuelFree` and apply `verifyStatefulEquivMir_of_wpConverges` with `mirNoCallWpConverges_of_runCfgToBlock`, reusing the reference specification's `MirNoCallWpConverges` theorem.\n",
        );
    }
    if effective.is_ub_exception {
        out.push_str(
            "- **Scoped UB-Exception Route (`UbExceptionItemSpec`)**: `open Anneal.PureMirExec Anneal.MirFuelFree` and discharge `UbExceptionVerificationResult` via `verifyUbExceptionMir_of_wpConverges` and `mirWpConverges_of_runCfgToBlock`.\n",
        );
    }
    if profile.has_inline_companions {
        if profile.has_impure_inline_companions {
            out.push_str(
                "- **Companion Spec Route (`#mir_lift_spec` / closure-upvar fallback)**: inline `#[spec]` companions capture `&` upvars (`checkPureMir = false`); `open Anneal.PureMirExec`, invert `requires` with `holdBoolReq_of_mirBool` + count-free `repeat`, and prove `ensures` with `hold_mirBool_of_blockLinear` (`defaultSpecSteps`).\n",
            );
        } else {
            out.push_str(
                "- **Companion Spec Route (`#mir_lift_spec`)**: `open Anneal.PureMirExec` and lift pure `requires` / `ensures` companions via `mirBoolPredicateHolds_of_pureExec` and `mirBoolPredicateHolds_elim_of_pureExec` (or fall back to `holdBoolReq_of_mirBool` + `repeat` and `hold_mirBool_of_blockLinear` when closure `&` upvars make `checkPureMir = false`).\n",
            );
        }
    }
    out.push('\n');
    out
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
            let key_pos = self.pos;
            let key = self.parse_string()?;
            // Duplicate keys are ambiguous (readers disagree on first- vs.
            // last-wins), so a spec-lock manifest must never contain them.
            if entries.iter().any(|(k, _): &(String, JsonValue)| *k == key) {
                return Err(format!("duplicate JSON object key '{key}' at byte {key_pos}"));
            }
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
                trait_impls: Vec::new(),
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
                trait_impls: Vec::new(),
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
            trait_impls: Vec::new(),
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
            trait_impls: Vec::new(),
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
            trait_impls: Vec::new(),
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

    #[test]
    fn verify_spec_lock_with_external_file_and_git_ref_rejects_on_disk_tampering() {
        let ws = unique_temp_dir("external-and-git-lock");
        let records = sample_records();
        let ext_lock = ws.join("external-lock.json");

        let written = lock_workspace_specs_with_options(&ws, &records, &[], Some(&ext_lock))
            .expect("write external lock");
        assert!(written.is_file());
        assert!(ext_lock.is_file());

        // Also write the workspace `.anneal/spec-lock.json` so we can test tampering.
        let ws_lock = lock_workspace_specs(&ws, &records).expect("write ws lock");

        // Tamper with `.anneal/spec-lock.json` on disk (simulating an agent overwriting it).
        let mut tampered_records = records.clone();
        tampered_records[1].target.mir_module_sha256 = "f".repeat(64);
        let tampered_manifest = SpecLockManifest {
            schema: SPEC_LOCK_SCHEMA_V1.to_string(),
            locked_records: tampered_records
                .iter()
                .map(LockedUnitRecord::from_unit_record)
                .collect(),
            locked_specs_files: Vec::new(),
            locked_assumptions_files: Vec::new(),
            mutable_subjects: Vec::new(),
            spec_digest: None,
        };
        fs::write(&ws_lock, tampered_manifest.to_json_string()).expect("overwrite ws lock");

        // External `--lock-file` must detect that `.anneal/spec-lock.json` on disk was tampered!
        let ext_err = verify_spec_lock_with_options(&ws, &tampered_records, Some(&ext_lock), None)
            .expect_err("external lock must reject tampered on-disk lockfile");
        assert!(
            ext_err.contains("differs from external lock file"),
            "unexpected ext_err: {ext_err}"
        );

        // Restore `.anneal/spec-lock.json` and commit it in a temporary Git repo to test `--lock-git-ref HEAD`.
        fs::copy(&ext_lock, &ws_lock).expect("restore ws lock");
        let _ = fs::remove_file(&ext_lock);

        let init_status = std::process::Command::new("git").arg("init").current_dir(&ws).status();
        if init_status.map(|s| s.success()).unwrap_or(false) {
            let _ = std::process::Command::new("git")
                .args(["config", "user.email", "test@example.com"])
                .current_dir(&ws)
                .status();
            let _ = std::process::Command::new("git")
                .args(["config", "user.name", "Test"])
                .current_dir(&ws)
                .status();
            let _ = std::process::Command::new("git")
                .args(["add", ".anneal/spec-lock.json"])
                .current_dir(&ws)
                .status();
            let commit_ok = std::process::Command::new("git")
                .args(["commit", "-m", "lock"])
                .current_dir(&ws)
                .status()
                .map(|s| s.success())
                .unwrap_or(false);
            if commit_ok {
                verify_spec_lock_with_options(&ws, &records, None, Some("HEAD"))
                    .expect("clean git HEAD lock must pass");
                fs::write(&ws_lock, tampered_manifest.to_json_string())
                    .expect("tamper ws lock after commit");
                let git_err =
                    verify_spec_lock_with_options(&ws, &tampered_records, None, Some("HEAD"))
                        .expect_err("git HEAD lock must reject tampered on-disk lockfile");
                assert!(
                    git_err.contains("modified relative to git ref 'HEAD'"),
                    "unexpected git_err: {git_err}"
                );
            }
        }

        let _ = fs::remove_dir_all(&ws);
    }

    #[test]
    fn check_specs_non_vacuous_rejects_arithmetic_and_tautological_ensures_weakening() {
        let ws = unique_temp_dir("semantic-weakening");
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
            trait_impls: Vec::new(),
        });

        let spec_file = specs_dir.join("add.lean");

        for bad_pre in [
            "instance : ItemSpec \"demo::add\" where\n  pre _ := 0 = 1\n  post args ret := Obligations.Demo.add.rustEnsures args ret\n",
            "instance : ItemSpec \"demo::add\" where\n  pre _ := ¬ True\n  post args ret := Obligations.Demo.add.rustEnsures args ret\n",
            "instance : ItemSpec \"demo::add\" where\n  pre args := Obligations.Demo.add.rustRequires args ∧ False\n  post args ret := Obligations.Demo.add.rustEnsures args ret\n",
            "instance : ItemSpec \"demo::add\" :=\n  Obligations.Demo.add.refineSpec (fun _ => False) (fun _ _ => True)\n",
        ] {
            fs::write(&spec_file, bad_pre).expect("write bad pre");
            let err = check_specs_non_vacuous_with_records(&ws, &records)
                .expect_err("must reject vacuous precondition");
            assert!(
                err.contains("vacuous specification precondition rejected"),
                "expected vacuous precondition error for:\n{bad_pre}\ngot: {err}"
            );
        }

        // Rejects tautological disjunction weakening `rustEnsures`:
        fs::write(
            &spec_file,
            "instance : ItemSpec \"demo::add\" where\n  \
               pre args := Obligations.Demo.add.rustRequires args\n  \
               post args ret := Obligations.Demo.add.rustEnsures args ret ∨ True\n",
        )
        .expect("write tautological ensures spec");
        let taut_err = check_specs_non_vacuous_with_records(&ws, &records)
            .expect_err("must reject tautological ensures weakening");
        assert!(
            taut_err.contains("trivializes the Rust #[spec] `ensures` clause via"),
            "unexpected tautological error: {taut_err}"
        );

        // Rejects vacuous `envAssumed` and dropped `#[external_spec]` call contracts:
        let ob_dir = ws.join(".anneal/generated/Obligations/Demo");
        fs::create_dir_all(&ob_dir).expect("create Obligations/Demo");
        fs::write(
            ob_dir.join("add.lean"),
            "def externalCallContract_Demo_ext_helper : MirCallContract := sorry\n\
             abbrev defaultExternalCallContract : MirCallContract := externalCallContract_Demo_ext_helper\n",
        )
        .expect("write synthetic Obligations/Demo/add.lean");

        for bad_mod in [
            "instance : ModularItemSpec \"demo::add\" where\n  envAssumed := fun _ => False\n  pre args _ := Obligations.Demo.add.rustRequires args\n  post args _ ret _ := Obligations.Demo.add.rustEnsures args ret\n",
            "instance : ModularItemSpec \"demo::add\" :=\n  Obligations.Demo.add.refineModularSpec (fun _ => False) (fun _ _ => True) (fun _ _ _ _ => True)\n",
        ] {
            fs::write(&spec_file, bad_mod).expect("write bad modular spec");
            let err = check_specs_non_vacuous_with_records(&ws, &records)
                .expect_err("must reject vacuous modular envAssumed");
            assert!(
                err.contains("vacuous specification precondition rejected"),
                "expected vacuous error for:\n{bad_mod}\ngot: {err}"
            );
        }

        fs::write(
            &spec_file,
            "instance : ModularItemSpec \"demo::add\" :=\n  \
               Obligations.Demo.add.refineModularSpec\n    \
                 (fun _ => True)\n    \
                 (fun _ _ => True)\n    \
                 (fun _ _ _ _ => True)\n",
        )
        .expect("write modular spec dropping externalCallContract");
        let drop_ext_err = check_specs_non_vacuous_with_records(&ws, &records)
            .expect_err("must reject modular spec override that drops #[external_spec] contract");
        assert!(
            drop_ext_err.contains("drops the Rust #[external_spec] call contract"),
            "unexpected drop_ext_err: {drop_ext_err}"
        );

        // When multiple `#[external_spec]` contracts exist for an item, referencing only one
        // (`externalCallContract_Demo_ext_helper` or `defaultExternalCallContract`) while dropping
        // the second (`externalCallContract_Demo_ext_second`) must also be rejected!
        fs::write(
            ob_dir.join("add.lean"),
            "def externalCallContract_Demo_ext_helper : MirCallContract := sorry\n\
             def externalCallContract_Demo_ext_second : MirCallContract := sorry\n\
             abbrev defaultExternalCallContract : MirCallContract := externalCallContract_Demo_ext_helper\n",
        )
        .expect("write synthetic Obligations/Demo/add.lean with 2 external contracts");

        for partial_drop in [
            "instance : ModularItemSpec \"demo::add\" :=\n  \
               Obligations.Demo.add.refineModularSpec\n    \
                 (fun h => Obligations.Demo.add.externalCallContract_Demo_ext_helper.Handles h)\n    \
                 (fun _ _ => True)\n    \
                 (fun _ _ _ _ => True)\n",
            "instance : ModularItemSpec \"demo::add\" :=\n  \
               Obligations.Demo.add.refineModularSpec\n    \
                 (fun h => Obligations.Demo.add.defaultExternalCallContract.Handles h)\n    \
                 (fun _ _ => True)\n    \
                 (fun _ _ _ _ => True)\n",
        ] {
            fs::write(&spec_file, partial_drop).expect("write partial drop spec");
            let partial_err = check_specs_non_vacuous_with_records(&ws, &records)
                .expect_err("must reject modular spec override that drops 2nd external contract");
            assert!(
                partial_err.contains("drops the Rust #[external_spec] call contract"),
                "unexpected partial_err: {partial_err}"
            );
        }

        // Referencing `defaultModularSpec.envAssumed` or both `externalCallContract_*` contracts succeeds:
        for valid_multi in [
            "instance : ModularItemSpec \"demo::add\" :=\n  \
               Obligations.Demo.add.refineModularSpec\n    \
                 Obligations.Demo.add.defaultModularSpec.envAssumed\n    \
                 (fun _ _ => True)\n    \
                 (fun _ _ _ _ => True)\n",
            "instance : ModularItemSpec \"demo::add\" :=\n  \
               Obligations.Demo.add.refineModularSpec\n    \
                 (fun h => Obligations.Demo.add.externalCallContract_Demo_ext_helper.Handles h ∧ Obligations.Demo.add.externalCallContract_Demo_ext_second.Handles h)\n    \
                 (fun _ _ => True)\n    \
                 (fun _ _ _ _ => True)\n",
        ] {
            fs::write(&spec_file, valid_multi).expect("write valid multi-contract spec");
            check_specs_non_vacuous_with_records(&ws, &records)
                .expect("valid multi-contract modular spec must pass Check 4b");
        }

        // When an item has both an `#[external_spec]` contract and a sibling `#[spec]` callee
        // (`Obligations.Demo.sibling.defaultCallContract.holdsOn`), referencing only
        // `defaultExternalCallContract` while dropping the sibling callee contract must be rejected:
        fs::write(
            ob_dir.join("add.lean"),
            "def externalCallContract_Demo_ext_helper : MirCallContract := sorry\n\
             abbrev defaultExternalCallContract : MirCallContract := externalCallContract_Demo_ext_helper\n\
             instance (priority := low) defaultModularSpec : ModularItemSpec \"demo::add\" where\n  \
               envAssumed := fun h => And (externalCallContract_Demo_ext_helper.holdsOn h) (Obligations.Demo.sibling.defaultCallContract.holdsOn h)\n",
        )
        .expect("write synthetic Obligations/Demo/add.lean with external + sibling callee");
        fs::write(
            &spec_file,
            "instance : ModularItemSpec \"demo::add\" :=\n  \
               Obligations.Demo.add.refineModularSpec\n    \
                 Obligations.Demo.add.defaultExternalCallContract.holdsOn\n    \
                 (fun _ _ => True)\n    \
                 (fun _ _ _ _ => True)\n",
        )
        .expect("write spec dropping sibling callee contract");
        let drop_sibling_err = check_specs_non_vacuous_with_records(&ws, &records)
            .expect_err("must reject modular spec override that drops sibling defaultCallContract");
        assert!(
            drop_sibling_err.contains("drops the Rust #[external_spec] call contract"),
            "unexpected drop_sibling_err: {drop_sibling_err}"
        );
        fs::write(
            &spec_file,
            "instance : ModularItemSpec \"demo::add\" :=\n  \
               Obligations.Demo.add.refineModularSpec\n    \
                 (fun h => And (Obligations.Demo.add.defaultExternalCallContract.holdsOn h) (Obligations.Demo.sibling.defaultCallContract.holdsOn h))\n    \
                 (fun _ _ => True)\n    \
                 (fun _ _ _ _ => True)\n",
        )
        .expect("write spec preserving both external and sibling callee contracts");
        check_specs_non_vacuous_with_records(&ws, &records)
            .expect("preserving both external and sibling callee contracts must pass Check 4b");

        let _ = fs::remove_dir_all(&ws);
    }

    #[test]
    fn render_agent_context_surfaces_mir_lift_spec_loops_and_sep_logic_lenses_guidance() {
        let ws = unique_temp_dir("lifting-guidance");
        let mir_dir = ws.join(".anneal/generated/Mir/Demo");
        fs::create_dir_all(&mir_dir).expect("create Mir/Demo");

        let pure_mir = r#"import Trusted
namespace Mir.Demo.pure_fn
def body : CapturedMir :=
  {
    defPath := "demo::pure_fn",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := List.nil,
    basicBlocks := (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.return_, span := "" }, isCleanup := false } List.nil),
    fnAbi := dummyAbi,
    layouts := layouts,
    allocations := List.nil
  }
end Mir.Demo.pure_fn
"#;
        let pure_comp_mir = r#"import Trusted
namespace Mir.Demo.__anodized_fn_ensures_pure_fn
def body : CapturedMir :=
  {
    defPath := "demo::__anodized_fn_ensures_pure_fn",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.ensures,
    argCount := 2,
    localDecls := List.nil,
    basicBlocks := (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.return_, span := "" }, isCleanup := false } List.nil),
    fnAbi := dummyAbi,
    layouts := layouts,
    allocations := List.nil
  }
end Mir.Demo.__anodized_fn_ensures_pure_fn
"#;
        let mut_mir = r#"import Trusted
namespace Mir.Demo.mut_fn
def body : CapturedMir :=
  {
    defPath := "demo::mut_fn",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 0 }, debugName := Option.none } List.nil),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 1, projection := (List.cons ProjectionElem.deref List.nil) } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref List.nil) }))), span := "" } List.nil), terminator := { kind := TerminatorKind.return_, span := "" }, isCleanup := false } List.nil),
    fnAbi := dummyAbi,
    layouts := layouts,
    allocations := List.nil
  }
end Mir.Demo.mut_fn
"#;
        let loop_mir = r#"import Trusted
namespace Mir.Demo.loop_fn
def body : CapturedMir :=
  {
    defPath := "demo::loop_fn",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := List.nil,
    basicBlocks := (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.goto 1), span := "" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.goto 1), span := "" }, isCleanup := false } List.nil)),
    fnAbi := dummyAbi,
    layouts := layouts,
    allocations := List.nil
  }
end Mir.Demo.loop_fn
"#;

        fs::write(mir_dir.join("pure_fn.lean"), pure_mir).expect("write pure_fn.lean");
        fs::write(
            mir_dir.join("__anodized_fn_ensures_pure_fn.lean"),
            pure_comp_mir,
        )
        .expect("write ensures companion");
        fs::write(mir_dir.join("mut_fn.lean"), mut_mir).expect("write mut_fn.lean");
        fs::write(mir_dir.join("loop_fn.lean"), loop_mir).expect("write loop_fn.lean");

        let mk_rec = |def_id: &str, rel: &str, module: &str, kind, assoc: Option<&str>| {
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: def_id.to_string(),
                    mir_module_path: rel.to_string(),
                    mir_module_sha256: "a".repeat(64),
                },
                lean_module_name: module.to_string(),
                item_kind: kind,
                associated_subject_def_id: assoc.map(str::to_string),
                trait_impls: Vec::new(),
            }
        };

        let records = vec![
            mk_rec(
                "demo::pure_fn",
                "Mir/Demo/pure_fn.lean",
                "Mir.Demo.pure_fn",
                CapturedItemKind::Subject,
                None,
            ),
            mk_rec(
                "demo::__anodized_fn_ensures_pure_fn",
                "Mir/Demo/__anodized_fn_ensures_pure_fn.lean",
                "Mir.Demo.__anodized_fn_ensures_pure_fn",
                CapturedItemKind::InlineSpecEnsures,
                Some("demo::pure_fn"),
            ),
            mk_rec(
                "demo::mut_fn",
                "Mir/Demo/mut_fn.lean",
                "Mir.Demo.mut_fn",
                CapturedItemKind::Subject,
                None,
            ),
            mk_rec(
                "demo::loop_fn",
                "Mir/Demo/loop_fn.lean",
                "Mir.Demo.loop_fn",
                CapturedItemKind::Subject,
                None,
            ),
        ];

        let ctx_pure = render_agent_context(&ws, &records, Some("demo::pure_fn"))
            .expect("render context for pure_fn");
        assert!(ctx_pure.contains("## Proof Lifting Strategy Guide (Lift First, Evaluate Last)"));
        assert!(ctx_pure.contains("### Recommended Lifting Strategy"));
        assert!(ctx_pure.contains("Primary Pure Route (`#mir_lift` rules)"));
        assert!(ctx_pure.contains("Companion Spec Route (`#mir_lift_spec`)"));
        assert!(ctx_pure.contains("mirBoolPredicateHolds_elim_of_pureExec"));
        assert!(ctx_pure.contains("<item>_lift_sound"));
        assert!(ctx_pure.contains("LiftResidualBlock"));
        assert!(ctx_pure.contains("CapturedMir.instantiate"));
        assert!(ctx_pure.contains("open Trusted.MirAst Anneal.PureMirExec Anneal.MirLiftCore"));
        assert!(!ctx_pure.contains("Trusted.Layout"));
        assert!(ctx_pure.contains("Anneal.BitValidity"));
        assert!(ctx_pure.contains("checkFromBytes_sound"));
        assert!(!ctx_pure.contains("Body.instantiate"));
        assert!(!ctx_pure.contains("verifyPoly"));

        // Verify pre-scaffold fallback from `target/anneal/units` when `.anneal/generated/Mir`
        // has not been materialized yet.
        let units_ws = unique_temp_dir("lifting-guidance-units-fallback");
        let unit_mir_dir = units_ws.join("target/anneal/units/u0/Mir/Demo");
        fs::create_dir_all(&unit_mir_dir).expect("create unit Mir/Demo");
        fs::write(unit_mir_dir.join("loop_fn.lean"), loop_mir).expect("write unit loop_fn.lean");
        let mut unit_rec = mk_rec(
            "demo::loop_fn",
            "Mir/Demo/loop_fn.lean",
            "Mir.Demo.loop_fn",
            CapturedItemKind::Subject,
            None,
        );
        unit_rec.target.mir_module_sha256.clear();
        let ctx_units = render_agent_context(&units_ws, &[unit_rec], Some("demo::loop_fn"))
            .expect("render context from target/anneal/units");
        assert!(ctx_units.contains("### Captured MIR Module"));
        assert!(ctx_units.contains("Primary Loop Route (`forRangeUp` + `runCfgToBlock`)"));
        let _ = fs::remove_dir_all(&units_ws);

        let ctx_mut = render_agent_context(&ws, &records, Some("demo::mut_fn"))
            .expect("render context for mut_fn");
        assert!(ctx_mut.contains("Reference / Borrow Route (`Anneal.SepLogicLenses`)"));
        assert!(ctx_mut.contains("Anneal.FunctionalTranslation"));
        assert!(ctx_mut.contains("verifyStatefulMir_of_sepLenses"));

        let ctx_loop = render_agent_context(&ws, &records, Some("demo::loop_fn"))
            .expect("render context for loop_fn");
        assert!(ctx_loop.contains("Primary Loop Route (`forRangeUp` + `runCfgToBlock`)"));
        assert!(ctx_loop.contains("open Anneal.MirLoops Anneal.PureMirExec Anneal.MirFuelFree"));
        assert!(ctx_loop.contains("mirNoCallWpConverges_forRangeUp"));

        // Verify `UnsafeTraitImpl` formats `Mir.<Item>.layouts` with the concrete item module,
        // and unauthored `safe_total`, `equivalent_to`, and `typeParamCount > 0` items report
        // accurate contract surfaces and starter proof templates.
        let poly_mir = "import Trusted\nnamespace Mir.Demo.poly_fn\ndef body : CapturedMir := { defPath := \"demo::poly_fn\", typeParamCount := 1, localDecls := [], basicBlocks := [{ statements := [], terminator := { kind := .return_, span := \"\" }, isCleanup := false }] }\nend Mir.Demo.poly_fn\n";
        fs::write(mir_dir.join("impl_from_bytes.lean"), pure_mir)
            .expect("write impl_from_bytes.lean");
        fs::write(mir_dir.join("tot_fn.lean"), pure_mir).expect("write tot_fn.lean");
        fs::write(mir_dir.join("fast_fn.lean"), pure_mir).expect("write fast_fn.lean");
        fs::write(mir_dir.join("poly_fn.lean"), poly_mir).expect("write poly_fn.lean");
        let extra_records = vec![
            mk_rec(
                "demo::impl_from_bytes",
                "Mir/Demo/impl_from_bytes.lean",
                "Mir.Demo.impl_from_bytes",
                CapturedItemKind::UnsafeTraitImpl,
                None,
            ),
            mk_rec(
                "demo::tot_fn",
                "Mir/Demo/tot_fn.lean",
                "Mir.Demo.tot_fn",
                CapturedItemKind::Subject,
                None,
            ),
            mk_rec(
                "demo::__ANNEAL_EXT_SPEC_TARGET___anneal_attr_safe_total_tot_fn",
                "",
                "",
                CapturedItemKind::ExternalSpec,
                Some("demo::tot_fn"),
            ),
            mk_rec(
                "demo::fast_fn",
                "Mir/Demo/fast_fn.lean",
                "Mir.Demo.fast_fn",
                CapturedItemKind::Subject,
                None,
            ),
            mk_rec(
                "demo::__ANNEAL_EXT_SPEC_TARGET___anneal_attr_equiv_tot_fn__for__fast_fn",
                "",
                "",
                CapturedItemKind::ExternalSpec,
                Some("demo::fast_fn"),
            ),
            mk_rec(
                "demo::poly_fn",
                "Mir/Demo/poly_fn.lean",
                "Mir.Demo.poly_fn",
                CapturedItemKind::Subject,
                None,
            ),
        ];
        let ctx_trait = render_agent_context(&ws, &extra_records, Some("demo::impl_from_bytes"))
            .expect("render context for impl_from_bytes");
        assert!(ctx_trait.contains("over `Mir.Demo.impl_from_bytes.layouts`"));

        let ctx_tot = render_agent_context(&ws, &extra_records, Some("demo::tot_fn"))
            .expect("render context for tot_fn");
        assert!(ctx_tot.contains("- **`is_stateful`**: total (`TotalItemSpec` / `TotalVerificationResult`)"));
        assert!(ctx_tot.contains("theorem verified : TotalVerificationResult Obligations.Demo.tot_fn.totalClaim"));

        let ctx_equiv = render_agent_context(&ws, &extra_records, Some("demo::fast_fn"))
            .expect("render context for fast_fn");
        assert!(ctx_equiv.contains("- **`is_stateful`**: equiv (`StatefulEquivItemSpec` / `StatefulEquivVerificationResult`)"));
        assert!(ctx_equiv.contains("theorem verified : StatefulEquivVerificationResult Obligations.Demo.fast_fn.equivClaim"));

        let ctx_poly = render_agent_context(&ws, &extra_records, Some("demo::poly_fn"))
            .expect("render context for poly_fn");
        assert!(ctx_poly.contains(
            "- **`is_stateful`**: polymorphic (`polyClaim` / `CrateVerificationResult`)"
        ));
        assert!(ctx_poly.contains("theorem verified : Obligations.Demo.poly_fn.polyClaim"));

        // When an authored stateless `Proof/Demo/tot_fn.lean` (`VerificationResult`) or
        // `Proof/Demo/fast_fn.lean` (on a `#[spec(safe_total, equivalent_to: ...)]` item)
        // exists, `render_agent_context` must report the authored surface without clobbering.
        let proof_demo_dir = ws.join("anneal/proofs/Proof/Demo");
        fs::create_dir_all(&proof_demo_dir).expect("create Proof/Demo");
        fs::write(
            proof_demo_dir.join("tot_fn.lean"),
            "import Trusted\nimport Obligations.Demo.tot_fn\nnamespace Proof.Demo.tot_fn\nopen Trusted.VerificationResult\ntheorem verified : VerificationResult Obligations.Demo.tot_fn.claim := by sorry\nend Proof.Demo.tot_fn\n",
        )
        .expect("write stateless Proof/Demo/tot_fn.lean");
        fs::write(
            proof_demo_dir.join("fast_fn.lean"),
            "import Trusted\nimport Obligations.Demo.fast_fn\nnamespace Proof.Demo.fast_fn\nopen Trusted.VerificationResult\ntheorem verified : VerificationResult Obligations.Demo.fast_fn.claim := by sorry\nend Proof.Demo.fast_fn\n",
        )
        .expect("write stateless Proof/Demo/fast_fn.lean");
        let ctx_tot_authored = render_agent_context(&ws, &extra_records, Some("demo::tot_fn"))
            .expect("render context for authored stateless tot_fn");
        assert!(ctx_tot_authored.contains("- **Proof Status**: Present"));
        assert!(ctx_tot_authored.contains("- **`is_stateful`**: false (`ItemSpec` / `VerificationResult`)"));

        let ctx_fast_authored = render_agent_context(&ws, &extra_records, Some("demo::fast_fn"))
            .expect("render context for authored stateless fast_fn");
        assert!(ctx_fast_authored.contains("- **Proof Status**: Present"));
        assert!(
            ctx_fast_authored
                .contains("- **`is_stateful`**: false (`ItemSpec` / `VerificationResult`)"),
            "authored stateless proof on equivalent_to item must not be clobbered to equiv: {ctx_fast_authored}"
        );
        assert!(!ctx_fast_authored.contains("Equivalence Route"));

        let _ = fs::remove_dir_all(&ws);
    }

    #[test]
    fn strip_lean_comments_preserves_comment_markers_inside_string_literals() {
        let src = "instance : ItemSpec \"demo::fn--with/-markers\" where\n  -- real comment with \"quote\n  post _ _ := True\n";
        let stripped = strip_lean_comments(src);
        assert!(stripped.contains("\"demo::fn--with/-markers\""));
        assert!(stripped.contains("post _ _ := True"));
        assert!(!stripped.contains("real comment"));

        // Identifier primes (`c'`) adjacent to `'"'` must not misparse `'<'` as a
        // char literal and open an unclosed string literal across later lines.
        let prime_src =
            r#"def f (c' : Char) := if c'<'"' then 'α' else '\x22' -- strip me
  pre := False
"#;
        let prime_stripped = strip_lean_comments(prime_src);
        assert!(!prime_stripped.contains("strip me"));
        assert!(prime_stripped.contains("pre := False"));
    }

    /// Single `return` block (`pure_loop_free`).
    const RET_BLOCKS: &str =
        "[{ statements := [], terminator := { kind := .return_, span := \"\" }, isCleanup := false }]";
    /// Self-loop `goto 0` (`pure_bounded_loop`).
    const LOOP_BLOCKS: &str =
        "[{ statements := [], terminator := { kind := .goto 0, span := \"\" }, isCleanup := false }]";
    /// `ProjectionElem.deref` read (`tree_borrows_local`).
    const DEREF_BLOCKS: &str = "[{ statements := [{ kind := .assign { local_ := 0, projection := [] } (.use (.copy { local_ := 1, projection := [.deref] })), span := \"\" }], terminator := { kind := .return_, span := \"\" }, isCleanup := false }]";
    /// `TerminatorKind.call` (`full_mir`).
    const CALL_BLOCKS: &str = "[{ statements := [], terminator := { kind := .call (.constant { ty := { kind := .fnDef \"demo::f\" [], layoutIdx := 0 }, val := .zeroSized }) [] { local_ := 0, projection := [] } (some 1) .continue_, span := \"\" }, isCleanup := false }, { statements := [], terminator := { kind := .return_, span := \"\" }, isCleanup := false }]";

    fn mir_module_text(module: &str, blocks: &str) -> String {
        format!(
            "import Trusted\nnamespace {module}\ndef body : CapturedMir := {{ defPath := \"{module}\", localDecls := [], basicBlocks := {blocks} }}\nend {module}\n"
        )
    }

    /// Write `.anneal/generated/Mir/<rel>` and return its SHA-256.
    fn write_generated_mir(ws: &Path, rel: &str, text: &str) -> String {
        let path = ws.join(".anneal/generated/Mir").join(rel);
        fs::create_dir_all(path.parent().expect("Mir parent")).expect("create Mir dir");
        fs::write(&path, text).expect("write generated Mir module");
        sha256_hex(text.as_bytes())
    }

    /// `sample_records()` whose MIR digests commit to real captured modules:
    /// `demo::add` is `pure_loop_free`, its `requires` companion `full_mir`.
    fn certified_workspace(prefix: &str) -> (PathBuf, Vec<UnitTargetRecord>) {
        let ws = unique_temp_dir(prefix);
        let mut records = sample_records();
        records[0].target.mir_module_sha256 = write_generated_mir(
            &ws,
            "Demo/add.lean",
            &mir_module_text("Mir.Demo.add", RET_BLOCKS),
        );
        records[1].target.mir_module_sha256 = write_generated_mir(
            &ws,
            "Demo/__anodized_fn_requires_add.lean",
            &mir_module_text("Mir.Demo.__anodized_fn_requires_add", CALL_BLOCKS),
        );
        (ws, records)
    }

    const ADD_SPEC_TEXT: &str = "prelude\nimport Trusted\nnamespace Specs.Demo.add\ninstance : ItemSpec \"demo::add\" where\n  pre _ := True\n  post _ _ := True\nend Specs.Demo.add\n";

    #[test]
    fn spec_lock_legacy_manifests_without_certificates_still_verify() {
        let (ws, records) = certified_workspace("legacy-lock");
        let lock_path = ws.join(SPEC_LOCK_REL_PATH);
        fs::create_dir_all(lock_path.parent().expect("lock parent")).expect("create .anneal");

        // Verbatim shape written by the pre-certificate serializer.
        let legacy_json = format!(
            "{{\n  \"schema\": \"anneal.spec-lock.v1\",\n  \"locked_records\": [\n    {{\n      \"def_id\": \"demo::__anodized_fn_requires_add\",\n      \"lean_module_name\": \"Mir.Demo.__anodized_fn_requires_add\",\n      \"item_kind\": \"{}\",\n      \"associated_subject_def_id\": \"demo::add\",\n      \"mir_module_sha256\": \"{}\"\n    }},\n    {{\n      \"def_id\": \"demo::add\",\n      \"lean_module_name\": \"Mir.Demo.add\",\n      \"item_kind\": \"{}\",\n      \"associated_subject_def_id\": null,\n      \"mir_module_sha256\": \"{}\"\n    }}\n  ],\n  \"locked_specs_files\": [\n  ],\n  \"locked_assumptions_files\": [\n  ]\n}}\n",
            records[1].item_kind.as_str(),
            records[1].target.mir_module_sha256,
            records[0].item_kind.as_str(),
            records[0].target.mir_module_sha256,
        );
        let legacy = parse_spec_lock_manifest(&legacy_json).expect("parse legacy manifest");
        assert_eq!(legacy.spec_digest, None);
        assert!(legacy.locked_records.iter().all(|r| !r.has_fragment_certificate()));
        assert_eq!(
            serialize_spec_lock_manifest(&legacy),
            legacy_json,
            "certificate-free manifests must serialize bit-for-bit in the legacy shape"
        );
        fs::write(&lock_path, &legacy_json).expect("write legacy lock");
        let verified = verify_spec_lock(&ws, &records).expect("legacy lock must verify unchanged");
        assert_eq!(verified, legacy);

        // Explicit `null` certificates are equally legacy.
        let null_json = legacy_json
            .replace(
                "  \"schema\": \"anneal.spec-lock.v1\",\n",
                "  \"schema\": \"anneal.spec-lock.v1\",\n  \"spec_digest\": null,\n",
            )
            .replace(
                "\"associated_subject_def_id\": null,\n",
                "\"associated_subject_def_id\": null,\n      \"mir_fragment\": null,\n      \"spec_digest\": null,\n",
            );
        assert_ne!(null_json, legacy_json);
        assert_eq!(parse_spec_lock_manifest(&null_json).expect("parse nulls"), legacy);
        fs::write(&lock_path, &null_json).expect("write null-certificate lock");
        verify_spec_lock(&ws, &records).expect("null certificates must verify as legacy");

        // Legacy `--allow-impl-edit` locks keep their mutable-subject semantics.
        let mutable_json = legacy_json.replace(
            "  \"locked_records\": [\n",
            "  \"mutable_subjects\": [\n    \"demo::add\"\n  ],\n  \"locked_records\": [\n",
        );
        fs::write(&lock_path, &mutable_json).expect("write legacy mutable lock");
        let mut edited = records.clone();
        edited[0].target.mir_module_sha256 = write_generated_mir(
            &ws,
            "Demo/add.lean",
            &mir_module_text("Mir.Demo.add", CALL_BLOCKS),
        );
        verify_spec_lock(&ws, &edited).expect("legacy mutable subject edit must verify");
        let mut edited_companion = records.clone();
        edited_companion[1].target.mir_module_sha256 = "e".repeat(64);
        let err = verify_spec_lock(&ws, &edited_companion)
            .expect_err("legacy companion edit must stay locked");
        assert!(err.contains("__anodized_fn_requires_add"), "{err}");

        let _ = fs::remove_dir_all(&ws);
    }

    #[test]
    fn spec_lock_certifies_mir_fragments_and_rejects_certificate_tampering() {
        let (ws, records) = certified_workspace("fragment-certs");
        let spec_file = ws.join("anneal/proofs/Specs/Demo/add.lean");
        fs::create_dir_all(spec_file.parent().expect("Specs parent")).expect("create Specs/Demo");
        fs::write(&spec_file, ADD_SPEC_TEXT).expect("write spec");

        let lock_path = lock_workspace_specs(&ws, &records).expect("lock_workspace_specs");
        let raw = fs::read_to_string(&lock_path).expect("read lock");
        let manifest = parse_spec_lock_manifest(&raw).expect("parse certified lock");
        let idx = |m: &SpecLockManifest, def_id: &str| {
            m.locked_records
                .iter()
                .position(|r| r.def_id == def_id)
                .expect("locked record")
        };
        let (add_idx, req_idx) = (idx(&manifest, "demo::add"), idx(&manifest, "demo::__anodized_fn_requires_add"));
        let add = &manifest.locked_records[add_idx];
        let req = &manifest.locked_records[req_idx];
        assert_eq!(add.mir_fragment.as_deref(), Some("pure_loop_free"));
        assert_eq!(
            add.spec_digest.as_deref(),
            Some(
                compute_fragment_spec_digest(
                    "demo::add",
                    &records[0].target.mir_module_sha256,
                    Some(ADD_SPEC_TEXT),
                    MirFragment::PureLoopFree,
                )
                .as_str()
            )
        );
        assert_eq!(req.mir_fragment.as_deref(), Some("full_mir"));
        assert_eq!(
            req.spec_digest.as_deref(),
            Some(
                compute_fragment_spec_digest(
                    "demo::__anodized_fn_requires_add",
                    &records[1].target.mir_module_sha256,
                    None,
                    MirFragment::FullMir,
                )
                .as_str()
            )
        );
        assert_eq!(
            manifest.spec_digest.as_deref(),
            Some(compute_spec_lock_manifest_digest(&manifest).as_str())
        );
        assert!(manifest.spec_digest.as_deref().is_some_and(is_lowercase_sha256_hex));
        // The manifest digest commits to locked content, not to entry order.
        let mut reordered = manifest.clone();
        reordered.locked_records.reverse();
        assert_eq!(
            compute_spec_lock_manifest_digest(&reordered),
            compute_spec_lock_manifest_digest(&manifest)
        );
        // ...but it excludes only itself: the recorded digest never feeds back.
        let mut unsigned = manifest.clone();
        unsigned.spec_digest = None;
        assert_eq!(
            compute_spec_lock_manifest_digest(&unsigned),
            compute_spec_lock_manifest_digest(&manifest)
        );
        assert!(raw.contains("\"mir_fragment\": \"pure_loop_free\""), "{raw}");
        assert_eq!(serialize_spec_lock_manifest(&manifest), raw, "deterministic round trip");
        let verified = verify_spec_lock(&ws, &records).expect("certified lock must verify");
        assert_eq!(verified, manifest);
        // Locking twice is deterministic.
        lock_workspace_specs(&ws, &records).expect("re-lock");
        assert_eq!(fs::read_to_string(&lock_path).expect("re-read lock"), raw);

        let expect_violation = |json: &str, needle: &str| {
            fs::write(&lock_path, json).expect("write tampered lock");
            let err = verify_spec_lock(&ws, &records)
                .expect_err(&format!("tampered lock must be rejected with `{needle}`"));
            assert!(err.contains(needle), "expected `{needle}` in: {err}");
            fs::write(&lock_path, &raw).expect("restore lock");
        };
        let resigned = |mut m: SpecLockManifest| {
            m.spec_digest = Some(compute_spec_lock_manifest_digest(&m));
            m.to_json_string()
        };

        // 1. Naive edits of any locked field invalidate the manifest digest.
        expect_violation(
            &raw.replacen(
                "\"mir_fragment\": \"pure_loop_free\"",
                "\"mir_fragment\": \"full_mir\"",
                1,
            ),
            "manifest spec_digest mismatch",
        );
        let mut m = manifest.clone();
        m.mutable_subjects = vec!["demo::add".to_string()];
        expect_violation(&m.to_json_string(), "manifest spec_digest mismatch");
        let mut m = manifest.clone();
        m.locked_specs_files[0].sha256 = "0".repeat(64);
        expect_violation(&m.to_json_string(), "manifest spec_digest mismatch");
        let mut m = manifest.clone();
        m.locked_assumptions_files.push(LockedFileDigest {
            rel_path: "anneal/proofs/Assumptions/Demo/add.lean".to_string(),
            sha256: "1".repeat(64),
        });
        expect_violation(&m.to_json_string(), "manifest spec_digest mismatch");
        let mut m = manifest.clone();
        m.locked_records[add_idx].associated_subject_def_id = Some("demo::other".to_string());
        expect_violation(&m.to_json_string(), "manifest spec_digest mismatch");
        let mut m = manifest.clone();
        m.locked_records[req_idx].spec_digest = Some("b".repeat(64));
        expect_violation(&m.to_json_string(), "manifest spec_digest mismatch");

        // 2. Re-signed forgeries are still caught by re-deriving certificates.
        let mut m = manifest.clone();
        m.locked_records[add_idx].mir_fragment = Some("tree_borrows_local".to_string());
        expect_violation(
            &resigned(m),
            "mir_fragment for 'demo::add' changed from 'tree_borrows_local' to 'pure_loop_free'",
        );
        let mut m = manifest.clone();
        m.locked_records[add_idx].spec_digest = Some("a".repeat(64));
        expect_violation(&resigned(m), "spec_digest for 'demo::add' changed");

        // 3. Partial certificate stripping (downgrade attempts) is rejected.
        let mut m = manifest.clone();
        m.spec_digest = None;
        expect_violation(&m.to_json_string(), "manifest-level spec_digest is missing");
        let mut m = manifest.clone();
        m.locked_records[req_idx].spec_digest = None;
        expect_violation(&resigned(m), "lacks its mir_fragment/spec_digest certificate");
        let mut m = manifest.clone();
        m.locked_records[req_idx].mir_fragment = None;
        expect_violation(&resigned(m), "lacks its mir_fragment/spec_digest certificate");
        let mut m = manifest.clone();
        let dup = m.locked_records[add_idx].clone();
        m.locked_records.push(dup);
        expect_violation(&resigned(m), "duplicate locked record 'demo::add'");

        // 4. A full downgrade to the legacy shape is indistinguishable from a
        //    legacy lock in-workspace (backward compatibility), but an
        //    out-of-workspace `--lock-file` copy rejects it byte-for-byte.
        let mut legacy = manifest.clone();
        legacy.spec_digest = None;
        for rec in &mut legacy.locked_records {
            rec.mir_fragment = None;
            rec.spec_digest = None;
        }
        fs::write(&lock_path, legacy.to_json_string()).expect("write downgraded lock");
        verify_spec_lock(&ws, &records).expect("fully downgraded lock verifies as legacy");
        let ext_lock = ws.join("external/spec-lock.json");
        fs::write(&lock_path, &raw).expect("restore lock");
        lock_workspace_specs_with_options(&ws, &records, &[], Some(&ext_lock))
            .expect("lock with external copy");
        assert_eq!(fs::read_to_string(&ext_lock).expect("read external lock"), raw);
        fs::write(&lock_path, legacy.to_json_string()).expect("write downgraded lock");
        let ext_err = verify_spec_lock_with_options(&ws, &records, Some(&ext_lock), None)
            .expect_err("external lock must reject a downgraded on-disk lock");
        assert!(ext_err.contains("differs from external lock file"), "{ext_err}");
        fs::write(&lock_path, &raw).expect("restore lock");
        verify_spec_lock_with_options(&ws, &records, Some(&ext_lock), None)
            .expect("restored lock verifies against the external copy");

        // 5. Workspace edits: non-mutable MIR digests and `Specs/**` keep their
        //    precise (pre-existing) diagnostics, and a missing SHA-matching
        //    MIR module re-derives the fail-closed `full_mir` with a hint.
        let mut edited = records.clone();
        edited[0].target.mir_module_sha256 = "c".repeat(64);
        let err = verify_spec_lock(&ws, &edited).expect_err("non-mutable MIR edit");
        assert!(err.contains("MIR digest for 'demo::add' changed"), "{err}");
        fs::write(&spec_file, format!("{ADD_SPEC_TEXT}-- tampered\n")).expect("tamper spec");
        let err = verify_spec_lock(&ws, &records).expect_err("tampered Specs file");
        assert!(
            err.contains("locked Specs file 'anneal/proofs/Specs/Demo/add.lean' was modified"),
            "{err}"
        );
        fs::write(&spec_file, ADD_SPEC_TEXT).expect("restore spec");
        let add_mir = ws.join(".anneal/generated/Mir/Demo/add.lean");
        let add_text = fs::read_to_string(&add_mir).expect("read add MIR");
        fs::remove_file(&add_mir).expect("remove add MIR");
        let err = verify_spec_lock(&ws, &records).expect_err("missing SHA-matching MIR");
        assert!(
            err.contains("mir_fragment for 'demo::add' changed from 'pure_loop_free' to 'full_mir'")
                && err.contains("no captured MIR module matching mir_module_sha256"),
            "{err}"
        );
        fs::write(&add_mir, &add_text).expect("restore add MIR");
        verify_spec_lock(&ws, &records).expect("restored workspace verifies");

        // 6. Strict parsing of certificate values and duplicate keys.
        let sha = &records[0].target.mir_module_sha256;
        for (from, to, needle) in [
            ("\"mir_fragment\": \"pure_loop_free\"", "\"mir_fragment\": \"pureLoopFree\"", "canonical MirFragment tag"),
            ("\"mir_fragment\": \"pure_loop_free\"", "\"mir_fragment\": \"MirFragment.pureLoopFree\"", "canonical MirFragment tag"),
            ("\"mir_fragment\": \"pure_loop_free\"", "\"mir_fragment\": \" pure_loop_free\"", "canonical MirFragment tag"),
            ("\"mir_fragment\": \"pure_loop_free\"", "\"mir_fragment\": \"PURE_LOOP_FREE\"", "canonical MirFragment tag"),
            ("\"mir_fragment\": \"pure_loop_free\"", "\"mir_fragment\": \"bogus\"", "canonical MirFragment tag"),
            ("\"mir_fragment\": \"pure_loop_free\"", "\"mir_fragment\": [\"pure_loop_free\"]", "canonical MirFragment tag string or null"),
            ("\"mir_fragment\": \"pure_loop_free\"", "\"mir_fragment\": {}", "canonical MirFragment tag string or null"),
            ("\"mir_fragment\": \"pure_loop_free\"", "\"mir_fragment\": \"pure_loop_free\",\n      \"mir_fragment\": \"full_mir\"", "duplicate JSON object key 'mir_fragment'"),
            ("  \"schema\": \"anneal.spec-lock.v1\",\n", "  \"schema\": \"anneal.spec-lock.v1\",\n  \"schema\": \"anneal.spec-lock.v1\",\n", "duplicate JSON object key 'schema'"),
        ] {
            let tampered = raw.replacen(from, to, 1);
            assert_ne!(tampered, raw, "{to}");
            let err = parse_spec_lock_manifest(&tampered).expect_err(to);
            assert!(err.contains(needle), "expected `{needle}` for `{to}`: {err}");
        }
        let manifest_digest = manifest.spec_digest.clone().expect("manifest digest");
        for bad in [
            manifest_digest.to_uppercase(),
            manifest_digest[..63].to_string(),
            format!("{}g", &manifest_digest[..63]),
            format!("{manifest_digest}0"),
            sha.clone() + " ",
        ] {
            let tampered = raw.replacen(&manifest_digest, &bad, 1);
            assert_ne!(tampered, raw);
            let err = parse_spec_lock_manifest(&tampered).expect_err(&bad);
            assert!(err.contains("64 lowercase hex characters"), "{bad}: {err}");
        }
        let tampered = raw.replacen(
            &format!("\"spec_digest\": \"{manifest_digest}\""),
            "\"spec_digest\": []",
            1,
        );
        let err = parse_spec_lock_manifest(&tampered).expect_err("array manifest digest");
        assert!(err.contains("64-char lowercase hex string or null"), "{err}");
        assert!(is_canonical_mir_fragment_tag("full_mir") && !is_canonical_mir_fragment_tag("fullMir"));

        let _ = fs::remove_dir_all(&ws);
    }

    #[test]
    fn spec_lock_fragment_certificates_respect_allow_impl_edit_mutable_subjects() {
        let (ws, records) = certified_workspace("fragment-mutable");
        let lock_path =
            lock_workspace_specs_with_mutable(&ws, &records, &["demo::add".to_string()])
                .expect("lock with --allow-impl-edit demo::add");
        let raw = fs::read_to_string(&lock_path).expect("read lock");
        let manifest = parse_spec_lock_manifest(&raw).expect("parse lock");
        assert_eq!(manifest.mutable_subjects, vec!["demo::add".to_string()]);
        assert_eq!(
            manifest.spec_digest.as_deref(),
            Some(compute_spec_lock_manifest_digest(&manifest).as_str())
        );

        // 1. Editing the designated subject's body escalates its *current*
        //    fragment (`pure_loop_free` -> `full_mir`) and changes its MIR
        //    digest and record certificate; all three are exempt, and the lock
        //    file (hence the manifest digest) is untouched by the edit.
        let mut edited = records.clone();
        edited[0].target.mir_module_sha256 = write_generated_mir(
            &ws,
            "Demo/add.lean",
            &mir_module_text("Mir.Demo.add", CALL_BLOCKS),
        );
        let verified = verify_spec_lock(&ws, &edited).expect("designated mutable edit must verify");
        assert_eq!(fs::read_to_string(&lock_path).expect("re-read lock"), raw);
        let locked_add = verified
            .locked_records
            .iter()
            .find(|r| r.def_id == "demo::add")
            .expect("locked add");
        assert_eq!(locked_add.mir_fragment.as_deref(), Some("pure_loop_free"));
        let (current, missing) =
            build_sorted_certified_records(&ws, &edited, None).expect("current certificates");
        assert!(missing.is_empty(), "{missing:?}");
        let current_add = current.iter().find(|r| r.def_id == "demo::add").expect("current add");
        assert_eq!(current_add.mir_fragment.as_deref(), Some("full_mir"));
        assert_ne!(current_add.spec_digest, locked_add.spec_digest);

        // 2. The subject's `#[spec]` companion stays locked (MIR digest first).
        let mut edited_companion = edited.clone();
        edited_companion[1].target.mir_module_sha256 = write_generated_mir(
            &ws,
            "Demo/__anodized_fn_requires_add.lean",
            &mir_module_text("Mir.Demo.__anodized_fn_requires_add", RET_BLOCKS),
        );
        let err = verify_spec_lock(&ws, &edited_companion).expect_err("companion edit");
        assert!(
            err.contains("MIR digest for 'demo::__anodized_fn_requires_add' changed"),
            "{err}"
        );

        // 3. Forging `mutable_subjects` is detected by the manifest digest, and
        //    even a re-signed forgery cannot make a companion mutable (only
        //    `subject` records are ever exempt).
        let mut forged = manifest.clone();
        forged
            .mutable_subjects
            .push("demo::__anodized_fn_requires_add".to_string());
        fs::write(&lock_path, forged.to_json_string()).expect("write forged lock");
        let err = verify_spec_lock(&ws, &edited_companion).expect_err("forged mutable_subjects");
        assert!(err.contains("manifest spec_digest mismatch"), "{err}");
        forged.spec_digest = Some(compute_spec_lock_manifest_digest(&forged));
        fs::write(&lock_path, forged.to_json_string()).expect("write re-signed forged lock");
        let err = verify_spec_lock(&ws, &edited_companion).expect_err("re-signed forgery");
        assert!(
            err.contains("MIR digest for 'demo::__anodized_fn_requires_add' changed"),
            "{err}"
        );

        // 4. A forged certificate on the *mutable* subject is not re-derived
        //    (exempt), but it is still covered by the manifest digest.
        let mut forged = manifest.clone();
        forged.locked_records.iter_mut().for_each(|r| {
            if r.def_id == "demo::add" {
                r.mir_fragment = Some("intrinsic_copy".to_string());
            }
        });
        fs::write(&lock_path, forged.to_json_string()).expect("write forged certificate");
        let err = verify_spec_lock(&ws, &edited).expect_err("forged mutable certificate");
        assert!(err.contains("manifest spec_digest mismatch"), "{err}");

        let _ = fs::remove_dir_all(&ws);
    }

    #[test]
    fn render_agent_context_surfaces_mir_fragment_and_boundary_diagnostic() {
        let ws = unique_temp_dir("fragment-context");
        let mk = |name: &str, blocks: Option<&str>| {
            let module = format!("Mir.Demo.{name}");
            let sha = match blocks {
                Some(b) => write_generated_mir(
                    &ws,
                    &format!("Demo/{name}.lean"),
                    &mir_module_text(&module, b),
                ),
                None => "0".repeat(64),
            };
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: format!("demo::{name}"),
                    mir_module_path: format!("Mir/Demo/{name}.lean"),
                    mir_module_sha256: sha,
                },
                lean_module_name: module,
                item_kind: CapturedItemKind::Subject,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            }
        };
        let records = vec![
            mk("pure_fn", Some(RET_BLOCKS)),
            mk("loop_fn", Some(LOOP_BLOCKS)),
            mk("deref_fn", Some(DEREF_BLOCKS)),
            mk("call_fn", Some(CALL_BLOCKS)),
            mk("ghost_fn", None),
        ];
        fn item_section<'a>(ctx: &'a str, def_id: &str) -> &'a str {
            let header = format!("## Item `{def_id}`");
            let start = ctx.find(&header).unwrap_or_else(|| panic!("missing {header}"));
            let rest = &ctx[start..];
            let end = rest[header.len()..]
                .find("\n## Item `")
                .map_or(rest.len(), |e| e + header.len());
            &rest[..end]
        }

        let ctx = render_agent_context(&ws, &records, None).expect("render context");
        for (def_id, label, diagnostic) in [
            ("demo::pure_fn", "`pure_loop_free` (`MirFragment.pureLoopFree`, rank 0)", None),
            ("demo::loop_fn", "`pure_bounded_loop` (`MirFragment.pureBoundedLoop`, rank 1)", None),
            (
                "demo::deref_fn",
                "`tree_borrows_local` (`MirFragment.treeBorrowsLocal`, rank 2)",
                Some("ProjectionElem.deref"),
            ),
            (
                "demo::call_fn",
                "`full_mir` (`MirFragment.fullMir`, rank 4)",
                Some("TerminatorKind.call"),
            ),
            (
                "demo::ghost_fn",
                "`full_mir` (`MirFragment.fullMir`, rank 4) (fail-closed: no parsed captured `Mir/<Item>.lean` body)",
                Some(crate::scaffold::NO_CAPTURED_MIR_REASON),
            ),
        ] {
            let section = item_section(&ctx, def_id);
            assert!(
                section.contains(&format!("- **MIR Fragment**: {label}\n")),
                "{def_id}: {section}"
            );
            assert!(!section.contains("Locked MIR Fragment"), "{def_id}: unlocked workspace");
            match diagnostic {
                Some(needle) => {
                    assert!(section.contains("### MIR Fragment Boundary Diagnostic"), "{def_id}");
                    assert!(
                        section.contains(&format!("MIR fragment boundary crossed for `{def_id}`")),
                        "{def_id}: {section}"
                    );
                    assert!(section.contains(needle), "{def_id}: {section}");
                }
                None => assert!(
                    !section.contains("MIR fragment boundary crossed"),
                    "{def_id}: {section}"
                ),
            }
        }

        // Locked workspaces surface the certified fragment next to the live one.
        lock_workspace_specs(&ws, &records).expect("lock specs");
        let ctx = render_agent_context(&ws, &records, Some("demo::deref_fn")).expect("locked ctx");
        assert!(ctx.contains(
            "- **Locked MIR Fragment (`.anneal/spec-lock.json`)**: `tree_borrows_local` (`MirFragment.treeBorrowsLocal`, rank 2)\n"
        ));
        // Without a parsed captured body there is nothing to compare against.
        let ctx = render_agent_context(&ws, &records, Some("demo::ghost_fn")).expect("ghost ctx");
        assert!(
            ctx.contains(
                "- **Locked MIR Fragment (`.anneal/spec-lock.json`)**: `full_mir` (`MirFragment.fullMir`, rank 4) (no parsed captured `Mir/<Item>.lean` body to compare against)\n"
            ),
            "{ctx}"
        );
        assert!(!ctx.contains("differs from the current capture"), "{ctx}");
        // A designated mutable subject whose edit escalated its fragment.
        write_generated_mir(
            &ws,
            "Demo/deref_fn.lean",
            &mir_module_text("Mir.Demo.deref_fn", CALL_BLOCKS),
        );
        let mut edited = records.clone();
        edited[2].target.mir_module_sha256 = sha256_hex(
            mir_module_text("Mir.Demo.deref_fn", CALL_BLOCKS).as_bytes(),
        );
        let ctx = render_agent_context(&ws, &edited, Some("demo::deref_fn")).expect("edited ctx");
        assert!(ctx.contains("- **MIR Fragment**: `full_mir` (`MirFragment.fullMir`, rank 4)\n"));
        assert!(ctx.contains("differs from the current capture's `full_mir`"), "{ctx}");
        // Legacy certificate-free locks say so explicitly.
        let legacy = SpecLockManifest {
            schema: SPEC_LOCK_SCHEMA_V1.to_string(),
            locked_records: build_sorted_locked_records(&records),
            locked_specs_files: Vec::new(),
            locked_assumptions_files: Vec::new(),
            mutable_subjects: Vec::new(),
            spec_digest: None,
        };
        fs::write(ws.join(SPEC_LOCK_REL_PATH), legacy.to_json_string()).expect("write legacy lock");
        let ctx = render_agent_context(&ws, &records, Some("demo::pure_fn")).expect("legacy ctx");
        assert!(
            ctx.contains("not recorded (legacy certificate-free `anneal.spec-lock.v1` lock)"),
            "{ctx}"
        );
        assert!(!ctx.contains("re-run `cargo anneal lock-specs`"), "{ctx}");

        let _ = fs::remove_dir_all(&ws);
    }

    /// B1 P1#3: `verify_workspace_with_options` checks the lock *before*
    /// re-scaffolding `.anneal/generated/Mir`, so certificates must also be
    /// re-derivable from a custom `--units-dir`.
    #[test]
    fn spec_lock_certificates_resolve_custom_units_dir_without_generated_mir() {
        let ws = unique_temp_dir("fragment-units-dir");
        let units = ws.join("custom-units");
        let write_unit = |rel: &str, text: &str| {
            let path = units.join("u0").join(rel);
            fs::create_dir_all(path.parent().expect("unit parent")).expect("create unit dir");
            fs::write(&path, text).expect("write unit Mir module");
            sha256_hex(text.as_bytes())
        };
        let mut records = sample_records();
        records[0].target.mir_module_sha256 =
            write_unit("Mir/Demo/add.lean", &mir_module_text("Mir.Demo.add", RET_BLOCKS));
        records[1].target.mir_module_sha256 = write_unit(
            "Mir/Demo/__anodized_fn_requires_add.lean",
            &mir_module_text("Mir.Demo.__anodized_fn_requires_add", CALL_BLOCKS),
        );
        assert!(!ws.join(".anneal/generated").exists());
        assert!(!ws.join("target/anneal/units").exists());

        // 1. Lock and verify straight from the custom units dir.
        let lock_path =
            lock_workspace_specs_with_units_dir(&ws, &records, &[], None, Some(&units))
                .expect("lock from custom units dir");
        let manifest = parse_spec_lock_manifest(&fs::read_to_string(&lock_path).expect("read lock"))
            .expect("parse lock");
        let fragment_of = |m: &SpecLockManifest, def_id: &str| {
            m.locked_records
                .iter()
                .find(|r| r.def_id == def_id)
                .and_then(|r| r.mir_fragment.clone())
        };
        assert_eq!(fragment_of(&manifest, "demo::add").as_deref(), Some("pure_loop_free"));
        assert_eq!(
            fragment_of(&manifest, "demo::__anodized_fn_requires_add").as_deref(),
            Some("full_mir")
        );
        verify_spec_lock_with_units_dir(&ws, &records, None, None, Some(&units))
            .expect("custom units dir verifies");
        // Without it the SHA-matching module is unreachable: fail closed, with a hint.
        let err = verify_spec_lock(&ws, &records).expect_err("unreachable MIR");
        assert!(
            err.contains("mir_fragment for 'demo::add' changed from 'pure_loop_free' to 'full_mir'")
                && err.contains("no captured MIR module matching mir_module_sha256"),
            "{err}"
        );

        // 2. Lock against `.anneal/generated/Mir`, delete the disposable tree,
        //    and verify from the custom units dir (the `agent-verify` order).
        for (rel, src) in [
            ("Demo/add.lean", "Mir/Demo/add.lean"),
            ("Demo/__anodized_fn_requires_add.lean", "Mir/Demo/__anodized_fn_requires_add.lean"),
        ] {
            let text = fs::read_to_string(units.join("u0").join(src)).expect("read unit module");
            write_generated_mir(&ws, rel, &text);
        }
        lock_workspace_specs(&ws, &records).expect("lock from generated Mir");
        assert_eq!(
            fs::read_to_string(&lock_path).expect("re-read lock"),
            manifest.to_json_string(),
            "both MIR sources certify identically"
        );
        fs::remove_dir_all(ws.join(".anneal/generated")).expect("delete generated tree");
        verify_spec_lock_with_units_dir(&ws, &records, None, None, Some(&units))
            .expect("verify from custom units dir after deleting .anneal/generated");

        let _ = fs::remove_dir_all(&ws);
    }

    /// B1 P2#4: lock consumers that trust `mutable_subjects` (the sandbox's
    /// writable `src/` mount) or report on the lock check its integrity first.
    #[test]
    fn run_agent_sandbox_rejects_tampered_lock_before_running_the_command() {
        let (ws, records) = certified_workspace("sandbox-integrity");
        let lock_path = lock_workspace_specs(&ws, &records).expect("lock");
        let raw = fs::read_to_string(&lock_path).expect("read lock");
        let mut forged = parse_spec_lock_manifest(&raw).expect("parse lock");
        forged.mutable_subjects = vec!["demo::add".to_string()];
        fs::write(&lock_path, forged.to_json_string()).expect("write forged lock");
        let marker = ws.join("sandbox-ran");
        let command = vec![
            "sh".to_string(),
            "-c".to_string(),
            format!("touch {}", marker.display()),
        ];
        let err = run_agent_sandbox(&ws, None, &command).expect_err("forged mutable_subjects");
        assert!(err.contains("manifest spec_digest mismatch"), "{err}");
        assert!(!marker.exists(), "the sandboxed command must not run on a tampered lock");
        assert!(!ws.join("anneal/proofs/Proof").exists(), "no sandbox setup on a tampered lock");

        let mut stripped = parse_spec_lock_manifest(&raw).expect("parse lock");
        stripped.spec_digest = None;
        fs::write(&lock_path, stripped.to_json_string()).expect("write stripped lock");
        let err = run_agent_sandbox(&ws, None, &command).expect_err("partially stripped lock");
        assert!(err.contains("manifest-level spec_digest is missing"), "{err}");
        assert!(!marker.exists());

        // B2 P2#3: the schema and duplicate-entry invariants are part of the
        // shared integrity check, so the sandbox enforces them exactly like
        // `agent-verify` — even when the (unkeyed) digest is recomputed.
        let mut wrong_schema = parse_spec_lock_manifest(&raw).expect("parse lock");
        wrong_schema.schema = "anneal.spec-lock.v0".to_string();
        wrong_schema.spec_digest = Some(compute_spec_lock_manifest_digest(&wrong_schema));
        fs::write(&lock_path, wrong_schema.to_json_string()).expect("write wrong-schema lock");
        let err = run_agent_sandbox(&ws, None, &command).expect_err("unsupported schema");
        assert!(err.contains("unsupported schema 'anneal.spec-lock.v0'"), "{err}");
        let err = verify_spec_lock(&ws, &records).expect_err("unsupported schema (agent-verify)");
        assert!(err.contains("unsupported schema 'anneal.spec-lock.v0'"), "{err}");
        assert!(!marker.exists());

        let mut duplicated = parse_spec_lock_manifest(&raw).expect("parse lock");
        duplicated.mutable_subjects = vec!["demo::add".to_string(), "demo::add".to_string()];
        duplicated.spec_digest = Some(compute_spec_lock_manifest_digest(&duplicated));
        fs::write(&lock_path, duplicated.to_json_string()).expect("write duplicated lock");
        let err = run_agent_sandbox(&ws, None, &command).expect_err("duplicate mutable_subjects");
        assert!(err.contains("duplicate 'mutable_subjects' entry 'demo::add'"), "{err}");
        let err = verify_spec_lock(&ws, &records).expect_err("duplicate mutable_subjects (agent-verify)");
        assert!(err.contains("duplicate 'mutable_subjects' entry 'demo::add'"), "{err}");
        assert!(!marker.exists());

        let _ = fs::remove_dir_all(&ws);
    }
}
