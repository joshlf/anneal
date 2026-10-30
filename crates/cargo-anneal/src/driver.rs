//! Parallel Cargo capture orchestration and per-unit manifest aggregation.
//!
//! During `cargo anneal extract`, Cargo may compile multiple crates in the
//! workspace graph concurrently. Each `anneal-rustc-capture` wrapper process
//! writes an isolated `UnitCaptureManifest.json` under `ANNEAL_CAPTURE_DIR`.
//! After `cargo check` finishes, this module aggregates those per-unit
//! manifests into the single deterministic `CaptureManifest.json` handshake
//! inspected by `trusted/audit/check_trusted.py`.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::SystemTime;

pub use anneal_rustc_capture::ANNEAL_CAPTURE_FILTER_ENV;
use anneal_rustc_capture::{
    ANNEAL_CAPTURE_DIR_ENV, CaptureManifest, CapturedItemKind, CapturedTarget,
    UnitCaptureManifest, UnitTargetRecord,
};
use anneal_rustc_capture::manifest::escape_json;

/// Environment variable overriding the path to the `anneal-rustc-capture`
/// wrapper executable.
pub const ANNEAL_RUSTC_CAPTURE_ENV: &str = "ANNEAL_RUSTC_CAPTURE";

/// Compiler flag passed via `RUSTFLAGS` so `anodized` embeds specification
/// companion functions into the compiled crate.
pub const ANODIZED_EMBED_SPECS_CFG: &str = "--cfg anodized_embed_specs";

/// Configuration for invoking `cargo check` under the `anneal-rustc-capture`
/// workspace wrapper.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CaptureDriverConfig {
    /// Root directory of the target Cargo workspace or package.
    pub workspace_root: PathBuf,
    /// Optional explicit `--manifest-path` passed to `cargo check`.
    pub manifest_path: Option<PathBuf>,
    /// Directory where per-unit capture subdirectories are written
    /// (`<target>/anneal/units` by default).
    pub units_dir: PathBuf,
    /// Optional explicit path to the `anneal-rustc-capture` executable.
    pub rustc_wrapper: Option<PathBuf>,
    /// Optional comma-separated item filter passed via
    /// `ANNEAL_CAPTURE_FILTER`.
    pub filter: Option<String>,
    /// Additional command-line arguments forwarded to `cargo check`.
    pub extra_cargo_args: Vec<String>,
}

impl CaptureDriverConfig {
    /// Construct a default capture configuration rooted at `workspace_root`.
    ///
    /// By default, per-unit capture artifacts are placed under
    /// `<workspace_root>/target/anneal/units`.
    pub fn new(workspace_root: impl Into<PathBuf>) -> Self {
        let root = workspace_root.into();
        let units_dir = root.join("target").join("anneal").join("units");
        Self {
            workspace_root: root,
            manifest_path: None,
            units_dir,
            rustc_wrapper: None,
            filter: None,
            extra_cargo_args: Vec::new(),
        }
    }

    /// Restrict MIR capture to items matching the comma-separated `filter`
    /// pattern (`ANNEAL_CAPTURE_FILTER`).
    pub fn with_filter(mut self, filter: impl Into<String>) -> Self {
        self.filter = Some(filter.into());
        self
    }
}

/// Resolve the path to the `anneal-rustc-capture` binary from `config` or the
/// surrounding environment.
///
/// Resolution checks the following locations in order:
/// 1. `config.rustc_wrapper` if explicitly provided.
/// 2. The `ANNEAL_RUSTC_CAPTURE` environment variable.
/// 3. A sibling `anneal-rustc-capture` binary next to the running executable.
/// 4. `<workspace_root>/target/{debug,release}/anneal-rustc-capture` and any
///    ancestor directory of `workspace_root`.
/// 5. `<anneal_checkout_root>/target/{debug,release}/anneal-rustc-capture`
///    resolved from `CARGO_MANIFEST_DIR`.
/// 6. `"anneal-rustc-capture"` on the system `PATH`.
pub fn resolve_rustc_wrapper(config: &CaptureDriverConfig) -> PathBuf {
    let base_dir = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    if let Some(ref wrapper) = config.rustc_wrapper {
        return crate::normalize_wrapper_path(&base_dir, wrapper);
    }
    if let Ok(env_path) = env::var(ANNEAL_RUSTC_CAPTURE_ENV)
        && !env_path.trim().is_empty()
    {
        return crate::normalize_wrapper_path(&base_dir, Path::new(env_path.trim()));
    }
    let exe_name = format!("anneal-rustc-capture{}", env::consts::EXE_SUFFIX);
    if let Ok(current_exe) = env::current_exe()
        && let Some(parent) = current_exe.parent()
    {
        let sibling = parent.join(&exe_name);
        if sibling.is_file() {
            return sibling;
        }
    }
    let abs_workspace_root = crate::normalize_path_against(&base_dir, &config.workspace_root);
    let mut current: Option<&Path> = Some(&abs_workspace_root);
    while let Some(dir) = current {
        for profile in ["debug", "release"] {
            let candidate = dir.join("target").join(profile).join(&exe_name);
            if candidate.is_file() {
                return candidate;
            }
        }
        current = dir.parent();
    }
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    if let Some(repo_root) = manifest_dir.parent().and_then(|p| p.parent()) {
        for profile in ["debug", "release"] {
            let candidate = repo_root.join("target").join(profile).join(&exe_name);
            if candidate.is_file() {
                return candidate;
            }
        }
    }
    if let Some(toolchain_root) = crate::setup::resolve_installed_toolchain() {
        let candidate = toolchain_root.join("bin").join(&exe_name);
        if candidate.is_file() {
            return candidate;
        }
    }
    PathBuf::from("anneal-rustc-capture")
}

/// Merge `ANODIZED_EMBED_SPECS_CFG` into an existing `RUSTFLAGS` value without
/// duplicating the flag if it is already present.
pub fn merge_rustflags(existing: Option<&str>) -> String {
    match existing {
        Some(flags) if !flags.trim().is_empty() => {
            if flags.contains(ANODIZED_EMBED_SPECS_CFG) {
                flags.to_string()
            } else {
                format!("{} {}", flags.trim_end(), ANODIZED_EMBED_SPECS_CFG)
            }
        }
        _ => ANODIZED_EMBED_SPECS_CFG.to_string(),
    }
}

/// Construct the `cargo check` command configured with
/// `RUSTC_WORKSPACE_WRAPPER`, `ANNEAL_CAPTURE_DIR`, `ANNEAL_CAPTURE_FILTER`,
/// and `RUSTFLAGS`.
pub fn build_cargo_check_command(config: &CaptureDriverConfig) -> Command {
    let base_dir = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let workspace_root = crate::normalize_path_against(&base_dir, &config.workspace_root);
    let units_dir = crate::normalize_path_against(&base_dir, &config.units_dir);
    let cargo_bin = env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
    let mut cmd = Command::new(cargo_bin);
    cmd.current_dir(&workspace_root);
    cmd.arg("check");
    if let Some(ref manifest_path) = config.manifest_path {
        let abs_manifest = crate::normalize_path_against(&base_dir, manifest_path);
        cmd.arg("--manifest-path").arg(abs_manifest);
    }
    for arg in &config.extra_cargo_args {
        cmd.arg(arg);
    }
    let wrapper = resolve_rustc_wrapper(config);
    let existing_rustflags = env::var("RUSTFLAGS").ok();
    let rustflags = merge_rustflags(existing_rustflags.as_deref());
    cmd.env("RUSTC_WORKSPACE_WRAPPER", wrapper);
    cmd.env(ANNEAL_CAPTURE_DIR_ENV, units_dir);
    if let Some(ref filter) = config.filter
        && !filter.trim().is_empty()
    {
        cmd.env(ANNEAL_CAPTURE_FILTER_ENV, filter);
    }
    cmd.env("RUSTFLAGS", rustflags);
    cmd
}

/// Invoke `cargo check` with `anneal-rustc-capture` enabled (passing
/// `ANNEAL_CAPTURE_FILTER` when configured) and aggregate all resulting
/// `UnitCaptureManifest.json` files.
pub fn invoke_cargo_capture(
    config: &CaptureDriverConfig,
) -> Result<(CaptureManifest, Vec<UnitTargetRecord>), String> {
    run_cargo_capture(config)
}

/// Run `cargo check` with `anneal-rustc-capture` enabled and aggregate all
/// resulting `UnitCaptureManifest.json` files.
///
/// Returns the aggregated root `CaptureManifest` and the sorted list of
/// `UnitTargetRecord` entries across all compiled workspace units.
pub fn run_cargo_capture(
    config: &CaptureDriverConfig,
) -> Result<(CaptureManifest, Vec<UnitTargetRecord>), String> {
    let base_dir = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let units_dir = crate::normalize_path_against(&base_dir, &config.units_dir);
    fs::create_dir_all(&units_dir).map_err(|err| {
        format!(
            "failed to create capture units directory {}: {}",
            units_dir.display(),
            err
        )
    })?;

    let mut cmd = build_cargo_check_command(config);
    let status = cmd
        .status()
        .map_err(|err| format!("failed to execute cargo check: {err}"))?;
    if !status.success() {
        return Err(format!(
            "cargo check failed with status {status}; refusing to aggregate capture manifests"
        ));
    }

    aggregate_unit_manifests(&units_dir)
}

/// Discover all per-unit capture manifests in `units_dir`, verify that every
/// unit succeeded, deduplicate sources and targets in deterministic sorted
/// order, and write the root `CaptureManifest.json`.
pub fn aggregate_unit_manifests(
    units_dir: &Path,
) -> Result<(CaptureManifest, Vec<UnitTargetRecord>), String> {
    if !units_dir.exists() {
        return Err(format!(
            "capture units directory does not exist: {}",
            units_dir.display()
        ));
    }

    let mut unit_manifest_paths = Vec::new();
    collect_files_named(units_dir, "UnitCaptureManifest.json", &mut unit_manifest_paths)?;
    unit_manifest_paths.sort();

    let mut fallback_manifest_paths = Vec::new();
    if unit_manifest_paths.is_empty() {
        collect_files_named(units_dir, "CaptureManifest.json", &mut fallback_manifest_paths)?;
        let root_manifest_path = units_dir.join("CaptureManifest.json");
        fallback_manifest_paths.retain(|p| p != &root_manifest_path);
        fallback_manifest_paths.sort();
    }

    if unit_manifest_paths.is_empty() && fallback_manifest_paths.is_empty() {
        return Err(format!(
            "no UnitCaptureManifest.json files found under {}",
            units_dir.display()
        ));
    }

    let mut sources_by_path: BTreeMap<String, String> = BTreeMap::new();
    let mut targets_by_def_id: BTreeMap<String, CapturedTarget> = BTreeMap::new();
    let mut records_by_def_id: BTreeMap<String, UnitTargetRecord> = BTreeMap::new();

    let mut units = Vec::with_capacity(unit_manifest_paths.len());
    for path in &unit_manifest_paths {
        let content = fs::read_to_string(path).map_err(|err| {
            format!("failed to read unit manifest {}: {}", path.display(), err)
        })?;
        let unit = parse_unit_capture_manifest(&content).map_err(|err| {
            format!("malformed unit manifest {}: {}", path.display(), err)
        })?;
        if unit.schema != UnitCaptureManifest::SCHEMA_VERSION {
            return Err(format!(
                "unsupported schema {} in {}",
                unit.schema,
                path.display()
            ));
        }
        if !unit.compilation_succeeded {
            return Err(format!(
                "unit '{}' (crate '{}') in {} reported compilation_succeeded = false",
                unit.unit_id,
                unit.crate_name,
                path.display()
            ));
        }
        let modified = fs::metadata(path)
            .and_then(|meta| meta.modified())
            .map_err(|err| {
                format!(
                    "failed to read modification time of {}: {}",
                    path.display(),
                    err
                )
            })?;
        units.push((path.clone(), unit, modified));
    }

    for (_, unit, _) in discard_superseded_unit_manifests(units) {
        for (src_path, src_hash) in unit.rust_sources {
            if let Some(existing_hash) = sources_by_path.get(&src_path) {
                if existing_hash != &src_hash {
                    return Err(format!(
                        "conflicting SHA-256 digest for Rust source '{src_path}': '{existing_hash}' vs '{src_hash}'"
                    ));
                }
            } else {
                sources_by_path.insert(src_path, src_hash);
            }
        }

        for record in unit.unit_targets {
            let def_id = record.target.def_id.clone();
            if let Some(existing_target) = targets_by_def_id.get(&def_id) {
                if existing_target != &record.target {
                    return Err(format!(
                        "conflicting captured target entry for def_id '{def_id}'"
                    ));
                }
            } else {
                targets_by_def_id.insert(def_id.clone(), record.target.clone());
                records_by_def_id.insert(def_id, record);
            }
        }
    }

    for path in &fallback_manifest_paths {
        let content = fs::read_to_string(path).map_err(|err| {
            format!("failed to read manifest {}: {}", path.display(), err)
        })?;
        let manifest = parse_capture_manifest(&content).map_err(|err| {
            format!("malformed manifest {}: {}", path.display(), err)
        })?;
        if manifest.schema != CaptureManifest::SCHEMA_VERSION {
            return Err(format!(
                "unsupported schema {} in {}",
                manifest.schema,
                path.display()
            ));
        }
        if !manifest.compilation_succeeded {
            return Err(format!(
                "manifest {} reported compilation_succeeded = false",
                path.display()
            ));
        }
        for (src_path, src_hash) in manifest.rust_sources {
            if let Some(existing_hash) = sources_by_path.get(&src_path) {
                if existing_hash != &src_hash {
                    return Err(format!(
                        "conflicting SHA-256 digest for Rust source '{src_path}': '{existing_hash}' vs '{src_hash}'"
                    ));
                }
            } else {
                sources_by_path.insert(src_path, src_hash);
            }
        }
        for target in manifest.targets {
            let def_id = target.def_id.clone();
            let lean_module_name = derive_lean_module_from_path(&target.mir_module_path);
            let record = UnitTargetRecord {
                target: target.clone(),
                lean_module_name,
                item_kind: CapturedItemKind::Subject,
                associated_subject_def_id: None,
            };
            if let Some(existing_target) = targets_by_def_id.get(&def_id) {
                if existing_target != &target {
                    return Err(format!(
                        "conflicting captured target entry for def_id '{def_id}'"
                    ));
                }
            } else {
                targets_by_def_id.insert(def_id.clone(), target);
                records_by_def_id.insert(def_id, record);
            }
        }
    }

    let rust_sources: Vec<(String, String)> = sources_by_path.into_iter().collect();
    let targets: Vec<CapturedTarget> = targets_by_def_id.into_values().collect();
    let unit_records: Vec<UnitTargetRecord> = records_by_def_id.into_values().collect();

    let root_manifest = CaptureManifest {
        schema: CaptureManifest::SCHEMA_VERSION,
        compilation_succeeded: true,
        rust_sources,
        targets,
    };

    let manifest_json = root_manifest.to_json_string();
    let units_manifest_path = units_dir.join("CaptureManifest.json");
    fs::write(&units_manifest_path, &manifest_json).map_err(|err| {
        format!(
            "failed to write CaptureManifest.json to {}: {}",
            units_manifest_path.display(),
            err
        )
    })?;

    if units_dir.file_name().and_then(|s| s.to_str()) == Some("units")
        && let Some(parent) = units_dir.parent()
    {
        let parent_manifest = parent.join("CaptureManifest.json");
        fs::write(&parent_manifest, &manifest_json).map_err(|err| {
            format!(
                "failed to write CaptureManifest.json to {}: {}",
                parent_manifest.display(),
                err
            )
        })?;
    }

    Ok((root_manifest, unit_records))
}

/// Drop unit manifests that a later compilation of the same crate superseded.
///
/// Cargo names each compilation unit after its crate and a metadata hash, so a
/// change to the crate's dependencies or features creates a new unit directory
/// next to the previous one, and `cargo check` neither rewrites nor removes the
/// previous one. A crate is compiled from one source tree per run, so when two
/// manifests for the same crate disagree about a source file, only the most
/// recently written manifest(s) describe the current build; the rest are
/// leftovers. Manifests that agree (for example, host and target builds of one
/// crate) are all kept, and manifests of different crates are never compared.
fn discard_superseded_unit_manifests(
    units: Vec<(PathBuf, UnitCaptureManifest, SystemTime)>,
) -> Vec<(PathBuf, UnitCaptureManifest, SystemTime)> {
    let mut newest_by_crate: BTreeMap<String, SystemTime> = BTreeMap::new();
    let mut disagreeing_crates: BTreeSet<String> = BTreeSet::new();
    let mut sources_by_crate: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
    for (_, unit, modified) in &units {
        let newest = newest_by_crate
            .entry(unit.crate_name.clone())
            .or_insert(*modified);
        if *modified > *newest {
            *newest = *modified;
        }
        let known = sources_by_crate.entry(unit.crate_name.clone()).or_default();
        for (src_path, src_hash) in &unit.rust_sources {
            match known.get(src_path) {
                Some(existing) if existing != src_hash => {
                    disagreeing_crates.insert(unit.crate_name.clone());
                }
                Some(_) => {}
                None => {
                    known.insert(src_path.clone(), src_hash.clone());
                }
            }
        }
    }
    units
        .into_iter()
        .filter(|(_, unit, modified)| {
            !disagreeing_crates.contains(&unit.crate_name)
                || Some(modified) == newest_by_crate.get(&unit.crate_name)
        })
        .collect()
}

/// Recursively collect regular files named `target_name` under `dir`.
fn collect_files_named(
    dir: &Path,
    target_name: &str,
    out: &mut Vec<PathBuf>,
) -> Result<(), String> {
    let entries = fs::read_dir(dir)
        .map_err(|err| format!("failed to read directory {}: {}", dir.display(), err))?;
    let mut paths = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|err| {
            format!("failed to read directory entry in {}: {}", dir.display(), err)
        })?;
        paths.push(entry.path());
    }
    paths.sort();
    for path in paths {
        let meta = fs::symlink_metadata(&path)
            .map_err(|err| format!("failed to inspect {}: {}", path.display(), err))?;
        if meta.is_dir() {
            collect_files_named(&path, target_name, out)?;
        } else if meta.is_file()
            && path.file_name().and_then(|n| n.to_str()) == Some(target_name)
        {
            out.push(path);
        }
    }
    Ok(())
}

/// Derive a dotted `Mir.<Item>` module name from a `Mir/<Item>.lean` path when
/// converting a root `CaptureManifest` without extended unit target metadata.
fn derive_lean_module_from_path(mir_module_path: &str) -> String {
    let trimmed = mir_module_path
        .trim_start_matches("./")
        .trim_start_matches(".anneal/generated/")
        .trim_end_matches(".lean");
    let dotted = trimmed.replace('/', ".");
    if dotted.starts_with("Mir.") {
        dotted
    } else {
        format!("Mir.{dotted}")
    }
}

/// Serialize a `UnitCaptureManifest` to deterministic JSON.
pub fn serialize_unit_capture_manifest(manifest: &UnitCaptureManifest) -> String {
    let mut out = String::from("{\n");
    out.push_str(&format!("  \"schema\": {},\n", manifest.schema));
    out.push_str(&format!(
        "  \"crate_name\": \"{}\",\n",
        escape_json(&manifest.crate_name)
    ));
    out.push_str(&format!(
        "  \"unit_id\": \"{}\",\n",
        escape_json(&manifest.unit_id)
    ));
    out.push_str(&format!(
        "  \"rustc_version\": \"{}\",\n",
        escape_json(&manifest.rustc_version)
    ));
    out.push_str(&format!(
        "  \"mir_dialect\": \"{}\",\n",
        escape_json(&manifest.mir_dialect)
    ));
    out.push_str(&format!(
        "  \"compilation_succeeded\": {},\n",
        if manifest.compilation_succeeded {
            "true"
        } else {
            "false"
        }
    ));
    out.push_str("  \"rust_sources\": [\n");
    for (i, (path, hash)) in manifest.rust_sources.iter().enumerate() {
        let comma = if i + 1 < manifest.rust_sources.len() {
            ","
        } else {
            ""
        };
        out.push_str(&format!(
            "    [\"{}\", \"{}\"]{}\n",
            escape_json(path),
            escape_json(hash),
            comma
        ));
    }
    out.push_str("  ],\n");
    out.push_str("  \"unit_targets\": [\n");
    for (i, rec) in manifest.unit_targets.iter().enumerate() {
        let comma = if i + 1 < manifest.unit_targets.len() {
            ","
        } else {
            ""
        };
        out.push_str("    {\n");
        out.push_str(&format!(
            "      \"def_id\": \"{}\",\n",
            escape_json(&rec.target.def_id)
        ));
        out.push_str(&format!(
            "      \"mir_module_path\": \"{}\",\n",
            escape_json(&rec.target.mir_module_path)
        ));
        out.push_str(&format!(
            "      \"mir_module_sha256\": \"{}\",\n",
            escape_json(&rec.target.mir_module_sha256)
        ));
        out.push_str(&format!(
            "      \"lean_module_name\": \"{}\",\n",
            escape_json(&rec.lean_module_name)
        ));
        out.push_str(&format!(
            "      \"item_kind\": \"{}\",\n",
            escape_json(rec.item_kind.as_str())
        ));
        match &rec.associated_subject_def_id {
            Some(assoc) => out.push_str(&format!(
                "      \"associated_subject_def_id\": \"{}\"\n",
                escape_json(assoc)
            )),
            None => out.push_str("      \"associated_subject_def_id\": null\n"),
        }
        out.push_str(&format!("    }}{comma}\n"));
    }
    out.push_str("  ]\n}\n");
    out
}

/// Parse a `UnitCaptureManifest` from its JSON text representation.
///
/// Accepts both flat target objects (where `def_id`, `mir_module_path`, and
/// `mir_module_sha256` appear directly on the `unit_targets` object) and nested
/// `"target": { ... }` objects.
pub fn parse_unit_capture_manifest(input: &str) -> Result<UnitCaptureManifest, String> {
    let val = parse_json(input)?;
    let obj = val
        .as_object()
        .ok_or_else(|| "expected top-level JSON object".to_string())?;

    let schema = get_u32_field(obj, "schema")?;
    let crate_name = get_string_field(obj, "crate_name")?;
    let unit_id = get_string_field(obj, "unit_id")?;
    let rustc_version = get_string_field(obj, "rustc_version")?;
    let mir_dialect = get_string_field(obj, "mir_dialect")?;
    let compilation_succeeded = get_bool_field(obj, "compilation_succeeded")?;
    let rust_sources = parse_rust_sources_field(obj)?;

    let targets_val = get_field(obj, "unit_targets")
        .or_else(|| get_field(obj, "targets"))
        .ok_or_else(|| "missing field 'unit_targets'".to_string())?;
    let targets_arr = targets_val
        .as_array()
        .ok_or_else(|| "field 'unit_targets' must be a JSON array".to_string())?;

    let mut unit_targets = Vec::with_capacity(targets_arr.len());
    for item in targets_arr {
        let item_obj = item
            .as_object()
            .ok_or_else(|| "each entry in 'unit_targets' must be an object".to_string())?;
        let target = if let Some(nested) = get_field(item_obj, "target") {
            let nested_obj = nested
                .as_object()
                .ok_or_else(|| "field 'target' in UnitTargetRecord must be an object".to_string())?;
            CapturedTarget {
                def_id: get_string_field(nested_obj, "def_id")?,
                mir_module_path: get_string_field(nested_obj, "mir_module_path")?,
                mir_module_sha256: get_string_field(nested_obj, "mir_module_sha256")?,
            }
        } else {
            CapturedTarget {
                def_id: get_string_field(item_obj, "def_id")?,
                mir_module_path: get_string_field(item_obj, "mir_module_path")?,
                mir_module_sha256: get_string_field(item_obj, "mir_module_sha256")?,
            }
        };

        let lean_module_name = match get_field(item_obj, "lean_module_name") {
            Some(JsonValue::Str(s)) => s.clone(),
            _ => derive_lean_module_from_path(&target.mir_module_path),
        };
        let item_kind_tag = get_string_field(item_obj, "item_kind")?;
        let item_kind = CapturedItemKind::from_str_tag(&item_kind_tag)
            .ok_or_else(|| format!("unknown item_kind tag '{item_kind_tag}'"))?;

        let associated_subject_def_id = match get_field(item_obj, "associated_subject_def_id") {
            None | Some(JsonValue::Null) => None,
            Some(JsonValue::Str(s)) if s.is_empty() => None,
            Some(JsonValue::Str(s)) => Some(s.clone()),
            _ => {
                return Err(
                    "field 'associated_subject_def_id' must be a string or null".to_string(),
                );
            }
        };

        unit_targets.push(UnitTargetRecord {
            target,
            lean_module_name,
            item_kind,
            associated_subject_def_id,
        });
    }

    Ok(UnitCaptureManifest {
        schema,
        crate_name,
        unit_id,
        rustc_version,
        mir_dialect,
        compilation_succeeded,
        rust_sources,
        unit_targets,
    })
}

/// Parse a root `CaptureManifest` from its JSON text representation.
pub fn parse_capture_manifest(input: &str) -> Result<CaptureManifest, String> {
    let val = parse_json(input)?;
    let obj = val
        .as_object()
        .ok_or_else(|| "expected top-level JSON object".to_string())?;

    let schema = get_u32_field(obj, "schema")?;
    let compilation_succeeded = get_bool_field(obj, "compilation_succeeded")?;
    let rust_sources = parse_rust_sources_field(obj)?;

    let targets_val = get_field(obj, "targets")
        .ok_or_else(|| "missing field 'targets'".to_string())?;
    let targets_arr = targets_val
        .as_array()
        .ok_or_else(|| "field 'targets' must be a JSON array".to_string())?;

    let mut targets = Vec::with_capacity(targets_arr.len());
    for item in targets_arr {
        let item_obj = item
            .as_object()
            .ok_or_else(|| "each entry in 'targets' must be an object".to_string())?;
        targets.push(CapturedTarget {
            def_id: get_string_field(item_obj, "def_id")?,
            mir_module_path: get_string_field(item_obj, "mir_module_path")?,
            mir_module_sha256: get_string_field(item_obj, "mir_module_sha256")?,
        });
    }

    Ok(CaptureManifest {
        schema,
        compilation_succeeded,
        rust_sources,
        targets,
    })
}

fn parse_rust_sources_field(
    obj: &[(String, JsonValue)],
) -> Result<Vec<(String, String)>, String> {
    let sources_val = get_field(obj, "rust_sources")
        .ok_or_else(|| "missing field 'rust_sources'".to_string())?;
    let sources_arr = sources_val
        .as_array()
        .ok_or_else(|| "field 'rust_sources' must be a JSON array".to_string())?;

    let mut rust_sources = Vec::with_capacity(sources_arr.len());
    for entry in sources_arr {
        let pair = entry
            .as_array()
            .ok_or_else(|| "each entry in 'rust_sources' must be a 2-element array".to_string())?;
        if pair.len() != 2 {
            return Err("each entry in 'rust_sources' must have length 2".to_string());
        }
        let path = pair[0]
            .as_str()
            .ok_or_else(|| "source path in 'rust_sources' must be a string".to_string())?;
        let hash = pair[1]
            .as_str()
            .ok_or_else(|| "source digest in 'rust_sources' must be a string".to_string())?;
        rust_sources.push((path.to_string(), hash.to_string()));
    }
    Ok(rust_sources)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum JsonValue {
    Null,
    Bool(bool),
    Number(i64),
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

    fn as_str(&self) -> Option<&str> {
        match self {
            Self::Str(s) => Some(s),
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
        Some(_) => Err(format!("field '{key}' must be a string")),
        None => Err(format!("missing required field '{key}'")),
    }
}

fn get_bool_field(obj: &[(String, JsonValue)], key: &str) -> Result<bool, String> {
    match get_field(obj, key) {
        Some(JsonValue::Bool(b)) => Ok(*b),
        Some(_) => Err(format!("field '{key}' must be a boolean")),
        None => Err(format!("missing required field '{key}'")),
    }
}

fn get_u32_field(obj: &[(String, JsonValue)], key: &str) -> Result<u32, String> {
    match get_field(obj, key) {
        Some(JsonValue::Number(n)) => {
            u32::try_from(*n).map_err(|_| format!("field '{key}' out of u32 range: {n}"))
        }
        Some(_) => Err(format!("field '{key}' must be an integer")),
        None => Err(format!("missing required field '{key}'")),
    }
}

struct JsonParser<'a> {
    bytes: &'a [u8],
    pos: usize,
}

fn parse_json(input: &str) -> Result<JsonValue, String> {
    let mut parser = JsonParser {
        bytes: input.as_bytes(),
        pos: 0,
    };
    let val = parser.parse_value()?;
    parser.skip_whitespace();
    if parser.pos != parser.bytes.len() {
        return Err(format!("unexpected trailing characters at byte {}", parser.pos));
    }
    Ok(val)
}

impl<'a> JsonParser<'a> {
    fn skip_whitespace(&mut self) {
        while self.pos < self.bytes.len() {
            match self.bytes[self.pos] {
                b' ' | b'\t' | b'\n' | b'\r' => self.pos += 1,
                _ => break,
            }
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn parse_value(&mut self) -> Result<JsonValue, String> {
        self.skip_whitespace();
        let ch = self
            .peek()
            .ok_or_else(|| "unexpected end of JSON input".to_string())?;
        match ch {
            b'{' => self.parse_object(),
            b'[' => self.parse_array(),
            b'"' => self.parse_string().map(JsonValue::Str),
            b't' => {
                self.expect_literal(b"true")?;
                Ok(JsonValue::Bool(true))
            }
            b'f' => {
                self.expect_literal(b"false")?;
                Ok(JsonValue::Bool(false))
            }
            b'n' => {
                self.expect_literal(b"null")?;
                Ok(JsonValue::Null)
            }
            b'-' | b'0'..=b'9' => self.parse_number(),
            _ => Err(format!("unexpected byte '{}' at offset {}", ch as char, self.pos)),
        }
    }

    fn expect_literal(&mut self, literal: &[u8]) -> Result<(), String> {
        if self.bytes.get(self.pos..self.pos + literal.len()) == Some(literal) {
            self.pos += literal.len();
            Ok(())
        } else {
            Err(format!("invalid JSON literal at byte {}", self.pos))
        }
    }

    fn parse_number(&mut self) -> Result<JsonValue, String> {
        let start = self.pos;
        if self.peek() == Some(b'-') {
            self.pos += 1;
        }
        while let Some(b'0'..=b'9') = self.peek() {
            self.pos += 1;
        }
        let slice = std::str::from_utf8(&self.bytes[start..self.pos])
            .map_err(|_| "invalid UTF-8 in number".to_string())?;
        let num = slice
            .parse::<i64>()
            .map_err(|err| format!("invalid integer '{slice}': {err}"))?;
        Ok(JsonValue::Number(num))
    }

    fn parse_string(&mut self) -> Result<String, String> {
        if self.peek() != Some(b'"') {
            return Err(format!("expected '\"' at byte {}", self.pos));
        }
        self.pos += 1;
        let mut out = String::new();
        while self.pos < self.bytes.len() {
            let b = self.bytes[self.pos];
            self.pos += 1;
            match b {
                b'"' => return Ok(out),
                b'\\' => {
                    if self.pos >= self.bytes.len() {
                        return Err("unterminated escape sequence in JSON string".to_string());
                    }
                    let esc = self.bytes[self.pos];
                    self.pos += 1;
                    match esc {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{0008}'),
                        b'f' => out.push('\u{000c}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            if self.pos + 4 > self.bytes.len() {
                                return Err("truncated \\uXXXX escape in JSON string".to_string());
                            }
                            let hex = std::str::from_utf8(&self.bytes[self.pos..self.pos + 4])
                                .map_err(|_| "invalid hex digits in \\uXXXX escape".to_string())?;
                            let code = u32::from_str_radix(hex, 16)
                                .map_err(|_| format!("invalid hex escape '\\u{hex}'"))?;
                            let ch = char::from_u32(code)
                                .ok_or_else(|| format!("invalid Unicode scalar \\u{hex}"))?;
                            out.push(ch);
                            self.pos += 4;
                        }
                        other => {
                            return Err(format!(
                                "unsupported escape character '\\{}' in JSON string",
                                other as char
                            ));
                        }
                    }
                }
                _ => {
                    self.pos -= 1;
                    let rest = std::str::from_utf8(&self.bytes[self.pos..])
                        .map_err(|_| "invalid UTF-8 in JSON string".to_string())?;
                    let ch = rest
                        .chars()
                        .next()
                        .ok_or_else(|| "unexpected end of string".to_string())?;
                    out.push(ch);
                    self.pos += ch.len_utf8();
                }
            }
        }
        Err("unterminated JSON string literal".to_string())
    }

    fn parse_array(&mut self) -> Result<JsonValue, String> {
        self.pos += 1; // Skip '['.
        self.skip_whitespace();
        let mut items = Vec::new();
        if self.peek() == Some(b']') {
            self.pos += 1;
            return Ok(JsonValue::Array(items));
        }
        loop {
            items.push(self.parse_value()?);
            self.skip_whitespace();
            match self.peek() {
                Some(b',') => {
                    self.pos += 1;
                }
                Some(b']') => {
                    self.pos += 1;
                    return Ok(JsonValue::Array(items));
                }
                _ => return Err(format!("expected ',' or ']' in array at byte {}", self.pos)),
            }
        }
    }

    fn parse_object(&mut self) -> Result<JsonValue, String> {
        self.pos += 1; // Skip '{'.
        self.skip_whitespace();
        let mut entries = Vec::new();
        if self.peek() == Some(b'}') {
            self.pos += 1;
            return Ok(JsonValue::Object(entries));
        }
        loop {
            self.skip_whitespace();
            let key = self.parse_string()?;
            self.skip_whitespace();
            if self.peek() != Some(b':') {
                return Err(format!("expected ':' after object key at byte {}", self.pos));
            }
            self.pos += 1;
            let val = self.parse_value()?;
            entries.push((key, val));
            self.skip_whitespace();
            match self.peek() {
                Some(b',') => {
                    self.pos += 1;
                }
                Some(b'}') => {
                    self.pos += 1;
                    return Ok(JsonValue::Object(entries));
                }
                _ => {
                    return Err(format!(
                        "expected ',' or '}}' in object at byte {}",
                        self.pos
                    ));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anneal_rustc_capture::{MIR_DIALECT_V2026_06_01, RUSTC_VERSION_STRING, sha256_hex};
    use std::time::{SystemTime, UNIX_EPOCH};

    fn unique_temp_dir(prefix: &str) -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after epoch")
            .as_nanos();
        let dir = env::temp_dir().join(format!(
            "cargo-anneal-{}-{}-{}",
            prefix,
            std::process::id(),
            nanos
        ));
        fs::create_dir_all(&dir).expect("create temp dir");
        dir
    }

    #[test]
    fn unit_manifest_json_roundtrip_and_nested_target_parsing() {
        let unit = UnitCaptureManifest {
            schema: UnitCaptureManifest::SCHEMA_VERSION,
            crate_name: "demo_crate".to_string(),
            unit_id: "demo_crate-1234abcd".to_string(),
            rustc_version: RUSTC_VERSION_STRING.to_string(),
            mir_dialect: MIR_DIALECT_V2026_06_01.to_string(),
            compilation_succeeded: true,
            rust_sources: vec![("src/lib.rs".to_string(), sha256_hex(b"pub fn add() {}"))],
            unit_targets: vec![
                UnitTargetRecord {
                    target: CapturedTarget {
                        def_id: "demo_crate::add".to_string(),
                        mir_module_path: "Mir/DemoCrate/add.lean".to_string(),
                        mir_module_sha256: sha256_hex(b"-- mir body"),
                    },
                    lean_module_name: "Mir.DemoCrate.add".to_string(),
                    item_kind: CapturedItemKind::Subject,
                    associated_subject_def_id: None,
                },
                UnitTargetRecord {
                    target: CapturedTarget {
                        def_id: "demo_crate::__anodized_fn_requires_add".to_string(),
                        mir_module_path: "Mir/DemoCrate/__anodized_fn_requires_add.lean"
                            .to_string(),
                        mir_module_sha256: sha256_hex(b"-- requires body"),
                    },
                    lean_module_name: "Mir.DemoCrate.__anodized_fn_requires_add".to_string(),
                    item_kind: CapturedItemKind::InlineSpecRequires,
                    associated_subject_def_id: Some("demo_crate::add".to_string()),
                },
            ],
        };

        let json = serialize_unit_capture_manifest(&unit);
        let parsed = parse_unit_capture_manifest(&json).expect("roundtrip parse");
        assert_eq!(parsed, unit);

        // Verify that nested `"target": { ... }` JSON representation also
        // parses.
        let nested_json = r#"{
          "schema": 1,
          "crate_name": "demo_crate",
          "unit_id": "demo_crate-nested",
          "rustc_version": "rustc 1.98.0-nightly (14210df0e 2026-05-31)",
          "mir_dialect": "V2026_06_01",
          "compilation_succeeded": true,
          "rust_sources": [["src/lib.rs", "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"]],
          "unit_targets": [
            {
              "target": {
                "def_id": "demo_crate::add",
                "mir_module_path": "Mir/DemoCrate/add.lean",
                "mir_module_sha256": "fedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210"
              },
              "lean_module_name": "Mir.DemoCrate.add",
              "item_kind": "subject",
              "associated_subject_def_id": null
            }
          ]
        }"#;
        let parsed_nested =
            parse_unit_capture_manifest(nested_json).expect("parse nested target JSON");
        assert_eq!(parsed_nested.unit_targets.len(), 1);
        assert_eq!(parsed_nested.unit_targets[0].target.def_id, "demo_crate::add");
    }

    #[test]
    fn aggregate_unit_manifests_deduplicates_and_writes_root_manifest() {
        let root = unique_temp_dir("aggregate");
        let units_dir = root.join("units");
        let unit_a_dir = units_dir.join("crate_b-02");
        let unit_b_dir = units_dir.join("crate_a-01");
        fs::create_dir_all(&unit_a_dir).expect("create unit_a");
        fs::create_dir_all(&unit_b_dir).expect("create unit_b");

        let shared_src_hash = sha256_hex(b"shared source");
        let src_a_hash = sha256_hex(b"crate a source");
        let src_b_hash = sha256_hex(b"crate b source");
        let mir_a_hash = sha256_hex(b"mir a");
        let mir_b_hash = sha256_hex(b"mir b");

        let manifest_b = UnitCaptureManifest {
            schema: 1,
            crate_name: "crate_b".to_string(),
            unit_id: "crate_b-02".to_string(),
            rustc_version: RUSTC_VERSION_STRING.to_string(),
            mir_dialect: MIR_DIALECT_V2026_06_01.to_string(),
            compilation_succeeded: true,
            rust_sources: vec![
                ("crates/b/src/lib.rs".to_string(), src_b_hash.clone()),
                ("crates/shared/src/lib.rs".to_string(), shared_src_hash.clone()),
            ],
            unit_targets: vec![UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "crate_b::zeta".to_string(),
                    mir_module_path: "Mir/CrateB/zeta.lean".to_string(),
                    mir_module_sha256: mir_b_hash.clone(),
                },
                lean_module_name: "Mir.CrateB.zeta".to_string(),
                item_kind: CapturedItemKind::Subject,
                associated_subject_def_id: None,
            }],
        };

        let manifest_a = UnitCaptureManifest {
            schema: 1,
            crate_name: "crate_a".to_string(),
            unit_id: "crate_a-01".to_string(),
            rustc_version: RUSTC_VERSION_STRING.to_string(),
            mir_dialect: MIR_DIALECT_V2026_06_01.to_string(),
            compilation_succeeded: true,
            rust_sources: vec![
                ("crates/shared/src/lib.rs".to_string(), shared_src_hash.clone()),
                ("crates/a/src/lib.rs".to_string(), src_a_hash.clone()),
            ],
            unit_targets: vec![
                UnitTargetRecord {
                    target: CapturedTarget {
                        def_id: "crate_a::alpha".to_string(),
                        mir_module_path: "Mir/CrateA/alpha.lean".to_string(),
                        mir_module_sha256: mir_a_hash.clone(),
                    },
                    lean_module_name: "Mir.CrateA.alpha".to_string(),
                    item_kind: CapturedItemKind::Subject,
                    associated_subject_def_id: None,
                },
                // Duplicate target across units with identical digest should
                // deduplicate cleanly.
                UnitTargetRecord {
                    target: CapturedTarget {
                        def_id: "crate_b::zeta".to_string(),
                        mir_module_path: "Mir/CrateB/zeta.lean".to_string(),
                        mir_module_sha256: mir_b_hash.clone(),
                    },
                    lean_module_name: "Mir.CrateB.zeta".to_string(),
                    item_kind: CapturedItemKind::Subject,
                    associated_subject_def_id: None,
                },
            ],
        };

        fs::write(
            unit_a_dir.join("UnitCaptureManifest.json"),
            serialize_unit_capture_manifest(&manifest_b),
        )
        .expect("write unit_a");
        fs::write(
            unit_b_dir.join("UnitCaptureManifest.json"),
            serialize_unit_capture_manifest(&manifest_a),
        )
        .expect("write unit_b");

        let (aggregated, records) =
            aggregate_unit_manifests(&units_dir).expect("aggregate manifests");

        assert!(aggregated.compilation_succeeded);
        assert_eq!(
            aggregated.rust_sources,
            vec![
                ("crates/a/src/lib.rs".to_string(), src_a_hash),
                ("crates/b/src/lib.rs".to_string(), src_b_hash),
                ("crates/shared/src/lib.rs".to_string(), shared_src_hash),
            ]
        );
        assert_eq!(aggregated.targets.len(), 2);
        assert_eq!(aggregated.targets[0].def_id, "crate_a::alpha");
        assert_eq!(aggregated.targets[1].def_id, "crate_b::zeta");
        assert_eq!(records.len(), 2);

        // Verify that root CaptureManifest.json was written both in units_dir
        // and its parent.
        let written_units = fs::read_to_string(units_dir.join("CaptureManifest.json"))
            .expect("read units CaptureManifest.json");
        let written_parent = fs::read_to_string(root.join("CaptureManifest.json"))
            .expect("read parent CaptureManifest.json");
        assert_eq!(written_units, aggregated.to_json_string());
        assert_eq!(written_parent, aggregated.to_json_string());

        let reparsed = parse_capture_manifest(&written_units).expect("reparse root manifest");
        assert_eq!(reparsed, aggregated);

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn aggregate_unit_manifests_rejects_failed_compilation_unit() {
        let root = unique_temp_dir("failed-unit");
        let unit_dir = root.join("bad_crate-01");
        fs::create_dir_all(&unit_dir).expect("create unit_dir");

        let bad_manifest = UnitCaptureManifest {
            schema: 1,
            crate_name: "bad_crate".to_string(),
            unit_id: "bad_crate-01".to_string(),
            rustc_version: RUSTC_VERSION_STRING.to_string(),
            mir_dialect: MIR_DIALECT_V2026_06_01.to_string(),
            compilation_succeeded: false,
            rust_sources: vec![("src/lib.rs".to_string(), sha256_hex(b"broken"))],
            unit_targets: Vec::new(),
        };
        fs::write(
            unit_dir.join("UnitCaptureManifest.json"),
            serialize_unit_capture_manifest(&bad_manifest),
        )
        .expect("write failed unit manifest");

        let err = aggregate_unit_manifests(&root).expect_err("must reject failed unit");
        assert!(err.contains("compilation_succeeded = false"));

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn aggregate_unit_manifests_prefers_the_newest_unit_of_a_recompiled_crate() {
        let root = unique_temp_dir("superseded-unit");
        let stale_dir = root.join("demo-1111111111111111");
        let fresh_dir = root.join("demo-2222222222222222");
        fs::create_dir_all(&stale_dir).expect("create stale unit dir");
        fs::create_dir_all(&fresh_dir).expect("create fresh unit dir");

        let unit = |unit_id: &str, source: &[u8], def_id: &str| UnitCaptureManifest {
            schema: 1,
            crate_name: "demo".to_string(),
            unit_id: unit_id.to_string(),
            rustc_version: RUSTC_VERSION_STRING.to_string(),
            mir_dialect: MIR_DIALECT_V2026_06_01.to_string(),
            compilation_succeeded: true,
            rust_sources: vec![("src/lib.rs".to_string(), sha256_hex(source))],
            unit_targets: vec![UnitTargetRecord {
                target: CapturedTarget {
                    def_id: def_id.to_string(),
                    mir_module_path: format!("Mir/Demo/{}.lean", def_id.replace("demo::", "")),
                    mir_module_sha256: sha256_hex(def_id.as_bytes()),
                },
                lean_module_name: format!("Mir.Demo.{}", def_id.replace("demo::", "")),
                item_kind: CapturedItemKind::Subject,
                associated_subject_def_id: None,
            }],
        };

        // Adding a dependency changes Cargo's metadata hash, so the recompiled
        // crate lands in a new unit directory while the old one lingers with
        // a different `src/lib.rs` digest. Write the stale unit first and make
        // sure its manifest is strictly older than the fresh one.
        fs::write(
            stale_dir.join("UnitCaptureManifest.json"),
            serialize_unit_capture_manifest(&unit(
                "demo-1111111111111111",
                b"old source",
                "demo::old",
            )),
        )
        .expect("write stale unit");
        let old_time = SystemTime::now() - std::time::Duration::from_secs(60);
        fs::File::open(stale_dir.join("UnitCaptureManifest.json"))
            .and_then(|f| f.set_modified(old_time))
            .expect("age stale unit manifest");
        fs::write(
            fresh_dir.join("UnitCaptureManifest.json"),
            serialize_unit_capture_manifest(&unit(
                "demo-2222222222222222",
                b"new source",
                "demo::new",
            )),
        )
        .expect("write fresh unit");

        let (aggregated, records) =
            aggregate_unit_manifests(&root).expect("stale unit must be superseded, not conflict");
        assert_eq!(
            aggregated.rust_sources,
            vec![("src/lib.rs".to_string(), sha256_hex(b"new source"))]
        );
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].target.def_id, "demo::new");

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn merge_rustflags_preserves_existing_and_adds_anodized_cfg() {
        assert_eq!(merge_rustflags(None), "--cfg anodized_embed_specs");
        assert_eq!(merge_rustflags(Some("")), "--cfg anodized_embed_specs");
        assert_eq!(
            merge_rustflags(Some("-Dwarnings")),
            "-Dwarnings --cfg anodized_embed_specs"
        );
        assert_eq!(
            merge_rustflags(Some("-Dwarnings --cfg anodized_embed_specs")),
            "-Dwarnings --cfg anodized_embed_specs"
        );
    }

    #[test]
    fn build_cargo_check_command_sets_capture_filter_env_when_configured() {
        let unfiltered_cfg = CaptureDriverConfig::new("/tmp/ws");
        let unfiltered_cmd = build_cargo_check_command(&unfiltered_cfg);
        let unfiltered_envs: Vec<_> = unfiltered_cmd.get_envs().collect();
        assert!(
            !unfiltered_envs
                .iter()
                .any(|(k, _)| *k == std::ffi::OsStr::new(ANNEAL_CAPTURE_FILTER_ENV)),
            "unfiltered command should not set {ANNEAL_CAPTURE_FILTER_ENV}"
        );

        let filtered_cfg =
            CaptureDriverConfig::new("/tmp/ws").with_filter("checked_scale,Ptr::try_from");
        let filtered_cmd = build_cargo_check_command(&filtered_cfg);
        let filter_val = filtered_cmd
            .get_envs()
            .find(|(k, _)| *k == std::ffi::OsStr::new(ANNEAL_CAPTURE_FILTER_ENV))
            .and_then(|(_, v)| v)
            .expect("filtered command must set ANNEAL_CAPTURE_FILTER");
        assert_eq!(
            filter_val,
            std::ffi::OsStr::new("checked_scale,Ptr::try_from")
        );
    }
}
