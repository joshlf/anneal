//! Workspace scaffolding for `.anneal/` (generated Lake modules) and
//! `anneal/proofs/` (durable user-authored specifications, assumptions, and
//! proofs).
//!
//! `scaffold_workspace` enforces the boundary between disposable compiler
//! output and human- or agent-authored proof artifacts:
//!
//! - `.anneal/generated/Mir/<Item>.lean`,
//!   `.anneal/generated/Obligations/<Item>.lean`,
//!   `.anneal/generated/Verify/<Item>.lean`, `.anneal/lakefile.toml`, and
//!   `.anneal/lean-toolchain` are updated on every run.
//! - By default (`init_proof_templates == false`), `scaffold_workspace` does
//!   not stamp out `anneal/proofs/Specs/<Item>.lean` or
//!   `anneal/proofs/Proof/<Item>.lean` files; generated assembly relies on
//!   Lean typeclass defaults (`Obligations.<Item>.defaultSpec` and
//!   `Verify.<Item>.defaultProof`) until the user authors an override in
//!   `anneal/proofs/`.
//! - When `init_proof_templates` is enabled (or via
//!   `scaffold_init_proof_templates`), starter `Proof/<Item>.lean` templates
//!   are created only when absent on disk and are never overwritten once
//!   created.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use anneal_rustc_capture::lean_emit::render_mir_module_header;
use anneal_rustc_capture::{CapturedItemKind, CapturedTarget, UnitTargetRecord, sha256_hex};

use crate::obligations::{
    AuthoredItemModules, SubjectObligationBundle, derive_item_module_suffix,
    group_subject_obligations, module_suffix_to_rel_path, render_crate_verify_module,
    render_obligations_module_with_options, render_proof_template_with_options,
    render_specs_template, render_verify_module_with_options,
};

/// Pinned Lean 4 toolchain identifier written to `.anneal/lean-toolchain`.
pub const LEAN_TOOLCHAIN: &str = "leanprover/lean4:v4.34.1";

/// Configuration for scaffolding an Anneal verification workspace.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScaffoldConfig {
    /// Root directory of the target Rust workspace or crate.
    pub workspace_root: PathBuf,
    /// Optional directory containing per-unit capture outputs
    /// (`<workspace_root>/target/anneal/units` by default).
    pub units_dir: Option<PathBuf>,
    /// Optional path to the Anneal repository root containing `trusted/lean`
    /// and `theory`.
    pub anneal_repo_root: Option<PathBuf>,
    /// When true, stamp out starter `anneal/proofs/Specs/<Item>.lean` templates
    /// for items that do not yet have an authored specification file on disk.
    ///
    /// Defaults to `false` so normal build and verify runs never populate
    /// generate-then-edit files in `anneal/proofs/`.
    pub init_spec_templates: bool,
    /// When true, stamp out starter `anneal/proofs/Proof/<Item>.lean` templates
    /// for items that do not yet have an authored proof file on disk.
    ///
    /// Defaults to `false` so normal build and verify runs never populate
    /// generate-then-edit files in `anneal/proofs/`.
    pub init_proof_templates: bool,
}

impl Default for ScaffoldConfig {
    fn default() -> Self {
        Self {
            workspace_root: PathBuf::from("."),
            units_dir: None,
            anneal_repo_root: None,
            init_spec_templates: false,
            init_proof_templates: false,
        }
    }
}

impl ScaffoldConfig {
    /// Create a default `ScaffoldConfig` rooted at `workspace_root`.
    pub fn new(workspace_root: impl Into<PathBuf>) -> Self {
        let root = workspace_root.into();
        let default_units = root.join("target").join("anneal").join("units");
        let units_dir = if default_units.is_dir() {
            Some(default_units)
        } else {
            None
        };
        Self {
            workspace_root: root,
            units_dir,
            anneal_repo_root: None,
            init_spec_templates: false,
            init_proof_templates: false,
        }
    }

    /// Configure whether starter `anneal/proofs/Specs/<Item>.lean` templates
    /// should be created when absent on disk.
    pub fn with_init_spec_templates(mut self, init_spec_templates: bool) -> Self {
        self.init_spec_templates = init_spec_templates;
        self
    }

    /// Configure whether starter `anneal/proofs/Proof/<Item>.lean` templates
    /// should be created when absent on disk.
    pub fn with_init_proof_templates(mut self, init_proof_templates: bool) -> Self {
        self.init_proof_templates = init_proof_templates;
        self
    }
}

/// Summary of files written and preserved by a workspace scaffold run.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ScaffoldReport {
    /// Paths to `.anneal/generated/Mir/<Item>.lean` modules placed or updated.
    pub generated_mir_files: Vec<PathBuf>,
    /// Paths to `.anneal/generated/Obligations/<Item>.lean` modules written.
    pub generated_obligation_files: Vec<PathBuf>,
    /// Paths to `.anneal/generated/Verify/<Item>.lean` modules written.
    pub generated_verify_files: Vec<PathBuf>,
    /// Paths to `anneal/proofs/Specs/<Item>.lean` files newly created on this
    /// run.
    pub created_spec_files: Vec<PathBuf>,
    /// Paths to `anneal/proofs/Specs/<Item>.lean` files that already existed on
    /// disk and were preserved without modification.
    pub preserved_spec_files: Vec<PathBuf>,
    /// Paths to `anneal/proofs/Proof/<Item>.lean` files newly created on this
    /// run.
    pub created_proof_files: Vec<PathBuf>,
    /// Paths to `anneal/proofs/Proof/<Item>.lean` files that already existed on
    /// disk and were preserved without modification.
    pub preserved_proof_files: Vec<PathBuf>,
    /// Path to the generated `.anneal/lakefile.toml`.
    pub lakefile_path: PathBuf,
    /// Path to the generated `.anneal/lean-toolchain`.
    pub toolchain_path: PathBuf,
}

/// Scaffold `.anneal/` and ensure `anneal/proofs/` exists under
/// `workspace_root` using default configuration settings (without creating
/// generate-then-edit files in `anneal/proofs/`).
pub fn scaffold_workspace(
    workspace_root: &Path,
    records: &[UnitTargetRecord],
) -> Result<ScaffoldReport, String> {
    let config = ScaffoldConfig::new(workspace_root);
    scaffold_workspace_with_config(&config, records)
}

/// Explicitly initialize starter `anneal/proofs/Proof/<Item>.lean` templates
/// (and `.anneal/generated/` assembly modules) for any items that do not yet
/// have authored proof files on disk.
pub fn scaffold_init_proof_templates(
    config: &ScaffoldConfig,
    records: &[UnitTargetRecord],
) -> Result<ScaffoldReport, String> {
    let mut init_cfg = config.clone();
    init_cfg.init_proof_templates = true;
    scaffold_workspace_with_config(&init_cfg, records)
}

/// Explicitly initialize starter `anneal/proofs/Specs/<Item>.lean` templates
/// for any items that do not yet have authored specification files on disk,
/// then refresh `.anneal/generated/` assembly modules.
pub fn scaffold_init_spec_templates(
    config: &ScaffoldConfig,
    records: &[UnitTargetRecord],
) -> Result<Vec<PathBuf>, String> {
    let mut init_cfg = config.clone();
    init_cfg.init_spec_templates = true;
    let report = scaffold_workspace_with_config(&init_cfg, records)?;
    Ok(report.created_spec_files)
}

/// Inspect `anneal/proofs/` on disk to determine which authored modules exist
/// for `item_rel_path`.
pub fn detect_authored_item_modules(proofs_root: &Path, item_rel_path: &Path) -> AuthoredItemModules {
    let spec_path = proofs_root.join("Specs").join(item_rel_path);
    let assumptions_path = proofs_root.join("Assumptions").join(item_rel_path);
    let proof_path = proofs_root.join("Proof").join(item_rel_path);

    let has_specs = spec_path.is_file();
    let spec_text = if has_specs {
        fs::read_to_string(&spec_path).ok()
    } else {
        None
    };
    let has_legacy_specs_defs = spec_text
        .as_deref()
        .is_some_and(|text| !text.contains("ItemSpec") && !text.contains("import Obligations."));

    let has_proof = proof_path.is_file();
    let proof_text = if has_proof {
        fs::read_to_string(&proof_path).ok()
    } else {
        None
    };

    let spec_is_ub_exception = spec_text.as_deref().is_some_and(|text| {
        text.contains("UbExceptionItemSpec") || text.contains("refineUbExceptionSpec")
    });
    let spec_is_modular = spec_text.as_deref().is_some_and(|text| {
        text.contains("ModularItemSpec") || text.contains("refineModularSpec")
    });

    let is_ub_exception = !spec_is_modular
        && (spec_is_ub_exception
            || proof_text.as_deref().is_some_and(|text| {
                text.contains("UbExceptionVerificationResult")
                    || (text.contains("ubExceptionClaim")
                        && !text.contains("ModularVerificationResult"))
            }));

    let is_modular = !is_ub_exception
        && (spec_is_modular
            || proof_text.as_deref().is_some_and(|text| {
                text.contains("modularClaim") || text.contains("ModularVerificationResult")
            }));

    let is_equiv = !is_ub_exception
        && !is_modular
        && (spec_text.as_deref().is_some_and(|text| {
            text.contains("StatefulEquivItemSpec") || text.contains("refineEquivSpec")
        }) || proof_text.as_deref().is_some_and(|text| {
            text.contains("equivClaim") || text.contains("StatefulEquivVerificationResult")
        }));

    let is_total = !is_ub_exception
        && !is_modular
        && !is_equiv
        && (spec_text.as_deref().is_some_and(|text| {
            text.contains("TotalItemSpec") || text.contains("refineTotalSpec")
        }) || proof_text.as_deref().is_some_and(|text| {
            text.contains("totalClaim") || text.contains("TotalVerificationResult")
        }));

    let spec_is_stateful = spec_text.as_deref().is_some_and(|text| {
        text.contains("StatefulItemSpec")
            || text.contains("refineStatefulSpec")
            || text.contains("refineSafeStatefulSpec")
    });
    let proof_is_stateful = proof_text.as_deref().is_some_and(|text| {
        text.contains("statefulClaim") || text.contains("StatefulVerificationResult")
    });

    AuthoredItemModules {
        has_specs,
        has_legacy_specs_defs,
        has_assumptions: assumptions_path.is_file(),
        has_proof,
        is_stateful: !is_ub_exception
            && !is_modular
            && !is_equiv
            && !is_total
            && (spec_is_stateful || proof_is_stateful),
        is_total,
        is_equiv,
        is_modular,
        is_ub_exception,
    }
}

fn write_if_changed(path: &Path, contents: &str) -> Result<(), String> {
    if let Ok(existing) = fs::read_to_string(path)
        && existing == contents
    {
        return Ok(());
    }
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)
            .map_err(|err| format!("failed to create directory {}: {}", parent.display(), err))?;
    }
    fs::write(path, contents)
        .map_err(|err| format!("failed to write {}: {}", path.display(), err))
}

/// Scaffold `.anneal/` and `anneal/proofs/` according to `config` for the
/// captured `records`.
///
/// Disposable files under `.anneal/` are regenerated on every call. Durable
/// files under `anneal/proofs/` are never overwritten if they already exist on
/// disk, and new `Proof/<Item>.lean` starter files are created only when
/// `config.init_proof_templates` is `true`.
pub fn scaffold_workspace_with_config(
    config: &ScaffoldConfig,
    records: &[UnitTargetRecord],
) -> Result<ScaffoldReport, String> {
    let dot_anneal = config.workspace_root.join(".anneal");
    let generated_dir = dot_anneal.join("generated");
    let mir_root = generated_dir.join("Mir");
    let obligations_root = generated_dir.join("Obligations");
    let verify_root = generated_dir.join("Verify");

    let proofs_root = config.workspace_root.join("anneal").join("proofs");
    let specs_root = proofs_root.join("Specs");
    let proof_root = proofs_root.join("Proof");

    for dir in [
        &dot_anneal,
        &generated_dir,
        &mir_root,
        &obligations_root,
        &verify_root,
        &proofs_root,
    ] {
        fs::create_dir_all(dir)
            .map_err(|err| format!("failed to create directory {}: {}", dir.display(), err))?;
    }

    let mut report = ScaffoldReport {
        lakefile_path: dot_anneal.join("lakefile.toml"),
        toolchain_path: dot_anneal.join("lean-toolchain"),
        ..ScaffoldReport::default()
    };

    // Place or initialize `.anneal/generated/Mir/<Item>.lean` for all captured
    // records.
    let mut sorted_records = records.to_vec();
    sorted_records.sort_by(|a, b| a.target.def_id.cmp(&b.target.def_id));

    for record in &sorted_records {
        let suffix = derive_item_module_suffix(record);
        let rel_path = module_suffix_to_rel_path(&suffix);
        let dest_mir_path = mir_root.join(&rel_path);
        if let Some(parent) = dest_mir_path.parent() {
            fs::create_dir_all(parent).map_err(|err| {
                format!("failed to create directory {}: {}", parent.display(), err)
            })?;
        }

        if let Some(src_mir_path) = find_source_mir_file(config, record, &rel_path) {
            if src_mir_path != dest_mir_path {
                let bytes = fs::read(&src_mir_path).map_err(|err| {
                    format!(
                        "failed to read captured MIR module {}: {}",
                        src_mir_path.display(),
                        err
                    )
                })?;
                let computed_hash = sha256_hex(&bytes);
                if !record.target.mir_module_sha256.is_empty()
                    && computed_hash != record.target.mir_module_sha256
                {
                    return Err(format!(
                        "SHA-256 mismatch for {}: expected {}, got {}",
                        src_mir_path.display(),
                        record.target.mir_module_sha256,
                        computed_hash
                    ));
                }
                if fs::read(&dest_mir_path).ok().as_deref() != Some(bytes.as_slice()) {
                    fs::write(&dest_mir_path, &bytes).map_err(|err| {
                        format!(
                            "failed to write MIR module {}: {}",
                            dest_mir_path.display(),
                            err
                        )
                    })?;
                }
            }
        } else if !dest_mir_path.exists() {
            let mir_ns = format!("Mir.{suffix}");
            let mut stub = render_mir_module_header(&mir_ns, &record.target.def_id);
            stub.push_str(&format!("\nend {mir_ns}\n"));
            fs::write(&dest_mir_path, stub).map_err(|err| {
                format!(
                    "failed to write MIR module {}: {}",
                    dest_mir_path.display(),
                    err
                )
            })?;
        }

        report.generated_mir_files.push(dest_mir_path);
    }

    let bundles = group_subject_obligations(&sorted_records);

    for bundle in &bundles {
        let spec_path = specs_root.join(&bundle.item_rel_path);
        if spec_path.exists() {
            report.preserved_spec_files.push(spec_path);
        } else if config.init_spec_templates {
            if let Some(parent) = spec_path.parent() {
                fs::create_dir_all(parent).map_err(|err| {
                    format!("failed to create directory {}: {}", parent.display(), err)
                })?;
            }
            let spec_contents = render_specs_template(bundle);
            fs::write(&spec_path, spec_contents).map_err(|err| {
                format!(
                    "failed to write specs template {}: {}",
                    spec_path.display(),
                    err
                )
            })?;
            report.created_spec_files.push(spec_path);
        }

        let mut authored = detect_authored_item_modules(&proofs_root, &bundle.item_rel_path);
        if !authored.is_ub_exception
            && !authored.is_modular
            && bundle.rust_equiv_target_module_suffix().is_some()
        {
            authored.is_equiv = true;
            authored.is_total = false;
            authored.is_stateful = false;
        }

        let proof_path = proof_root.join(&bundle.item_rel_path);
        if proof_path.exists() {
            report.preserved_proof_files.push(proof_path);
        } else if config.init_proof_templates {
            if let Some(parent) = proof_path.parent() {
                fs::create_dir_all(parent).map_err(|err| {
                    format!("failed to create directory {}: {}", parent.display(), err)
                })?;
            }
            let proof_contents = render_proof_template_with_options(bundle, authored);
            fs::write(&proof_path, proof_contents).map_err(|err| {
                format!(
                    "failed to write proof template {}: {}",
                    proof_path.display(),
                    err
                )
            })?;
            report.created_proof_files.push(proof_path);
            authored = detect_authored_item_modules(&proofs_root, &bundle.item_rel_path);
            if !authored.is_ub_exception
                && !authored.is_modular
                && bundle.rust_equiv_target_module_suffix().is_some()
            {
                authored.is_equiv = true;
                authored.is_total = false;
                authored.is_stateful = false;
            }
        }

        let obligation_path = obligations_root.join(&bundle.item_rel_path);
        let obligation_contents = render_obligations_module_with_options(bundle, authored);
        write_if_changed(&obligation_path, &obligation_contents)?;
        report.generated_obligation_files.push(obligation_path);

        let verify_path = verify_root.join(&bundle.item_rel_path);
        let verify_contents = render_verify_module_with_options(bundle, authored);
        write_if_changed(&verify_path, &verify_contents)?;
        report.generated_verify_files.push(verify_path);
    }

    let generated_this_run: BTreeSet<PathBuf> = report
        .generated_mir_files
        .iter()
        .chain(&report.generated_obligation_files)
        .chain(&report.generated_verify_files)
        .cloned()
        .collect();
    prune_stale_generated_modules(&generated_dir, &generated_this_run)?;

    let crate_verify_path = generated_dir.join("CrateVerify.lean");
    if bundles.is_empty() {
        if crate_verify_path.exists() {
            let _ = fs::remove_file(&crate_verify_path);
        }
    } else {
        let crate_name = infer_crate_name(&config.workspace_root, &bundles);
        let crate_verify_contents = render_crate_verify_module(&crate_name, &bundles);
        write_if_changed(&crate_verify_path, &crate_verify_contents)?;
    }

    let toolchain_contents = format!("{LEAN_TOOLCHAIN}\n");
    write_if_changed(&report.toolchain_path, &toolchain_contents)?;

    let lakefile_contents = render_lakefile_toml(config, &sorted_records, &bundles);
    write_if_changed(&report.lakefile_path, &lakefile_contents)?;

    Ok(report)
}

/// Delete `.lean` files under `.anneal/generated/{Mir,Obligations,Verify}` that
/// the current scaffold run did not generate.
///
/// `scaffold_workspace_with_config` only writes modules for the items it
/// currently captures. When an item disappears from the crate (or is excluded
/// by `--filter`), its previous `Verify/<Item>.lean` would otherwise survive in
/// `.anneal/generated/`, where `verify` still collects it for the
/// `TrustedBoundary` audit even though `.anneal/lakefile.toml` no longer builds
/// it. Pruning keeps the disposable directory equal to what this run generated.
fn prune_stale_generated_modules(
    generated_dir: &Path,
    keep: &BTreeSet<PathBuf>,
) -> Result<(), String> {
    for category in ["Mir", "Obligations", "Verify"] {
        let category_root = generated_dir.join(category);
        let mut files = Vec::new();
        collect_lean_files_recursive(&category_root, &mut files)?;
        for file in files {
            if !keep.contains(&file) {
                fs::remove_file(&file).map_err(|err| {
                    format!(
                        "failed to remove stale generated module {}: {}",
                        file.display(),
                        err
                    )
                })?;
            }
        }
        remove_empty_subdirs(&category_root)?;
    }
    Ok(())
}

fn remove_empty_subdirs(dir: &Path) -> Result<(), String> {
    if !dir.is_dir() {
        return Ok(());
    }
    let entries = fs::read_dir(dir)
        .map_err(|err| format!("failed to read directory {}: {}", dir.display(), err))?;
    for entry in entries {
        let entry = entry.map_err(|err| format!("failed to read dir entry: {err}"))?;
        let path = entry.path();
        if !path.is_dir() {
            continue;
        }
        remove_empty_subdirs(&path)?;
        let mut remaining = fs::read_dir(&path)
            .map_err(|err| format!("failed to read directory {}: {}", path.display(), err))?;
        if remaining.next().is_none() {
            fs::remove_dir(&path).map_err(|err| {
                format!(
                    "failed to remove empty directory {}: {}",
                    path.display(),
                    err
                )
            })?;
        }
    }
    Ok(())
}

/// Synchronize `.anneal/generated/Obligations/<Item>.lean`,
/// `.anneal/generated/Verify/<Item>.lean`, and `.anneal/lakefile.toml` with the
/// authored files currently present under `anneal/proofs/`.
///
/// This allows users and tests to create or delete `Specs/<Item>.lean`,
/// `Assumptions/<Item>.lean`, or `Proof/<Item>.lean` files after running
/// `scaffold` and have `verify_workspace` automatically wire those modules into
/// the generated assembly before invoking `lake build`.
pub fn refresh_workspace_assembly(workspace_root: &Path) -> Result<(), String> {
    let dot_anneal = workspace_root.join(".anneal");
    let generated_dir = dot_anneal.join("generated");
    let verify_root = generated_dir.join("Verify");
    let obligations_root = generated_dir.join("Obligations");
    let proofs_root = workspace_root.join("anneal").join("proofs");
    let lakefile_path = dot_anneal.join("lakefile.toml");

    if !verify_root.is_dir() || !lakefile_path.is_file() {
        return Ok(());
    }

    let mut verify_files = Vec::new();
    collect_lean_files_recursive(&verify_root, &mut verify_files)?;
    verify_files.sort();

    let mir_root = generated_dir.join("Mir");
    let mut specs_roots = BTreeSet::new();
    let mut assumptions_roots = BTreeSet::new();
    let mut proof_roots = BTreeSet::new();
    let mut refreshed_bundles = Vec::with_capacity(verify_files.len());

    for verify_path in &verify_files {
        let rel_path = verify_path
            .strip_prefix(&verify_root)
            .map_err(|err| format!("failed to strip prefix: {err}"))?
            .to_path_buf();
        let suffix = rel_path_to_module_suffix(&rel_path);
        let verify_text = fs::read_to_string(verify_path)
            .map_err(|err| format!("failed to read {}: {}", verify_path.display(), err))?;
        let def_id = extract_def_id_comment(&verify_text).unwrap_or_else(|| suffix.clone());

        let mut authored = detect_authored_item_modules(&proofs_root, &rel_path);
        let obligation_path = obligations_root.join(&rel_path);
        let ob_text_opt = if obligation_path.is_file() {
            Some(fs::read_to_string(&obligation_path).map_err(|err| {
                format!("failed to read {}: {}", obligation_path.display(), err)
            })?)
        } else {
            None
        };
        if !authored.is_ub_exception
            && !authored.is_modular
            && ob_text_opt
                .as_deref()
                .is_some_and(|t| t.contains("instance rustEquivSpec : StatefulEquivItemSpec"))
        {
            authored.is_equiv = true;
            authored.is_total = false;
            authored.is_stateful = false;
        }
        if authored.has_specs {
            specs_roots.insert(format!("Specs.{suffix}"));
        }
        if authored.has_assumptions {
            assumptions_roots.insert(format!("Assumptions.{suffix}"));
        }
        if authored.has_proof {
            proof_roots.insert(format!("Proof.{suffix}"));
        }

        let mir_disk_path = mir_root.join(&rel_path);
        let mir_sha = fs::read(&mir_disk_path)
            .ok()
            .map(|b| sha256_hex(&b))
            .unwrap_or_default();
        let synthetic_bundle = SubjectObligationBundle {
            subject: UnitTargetRecord {
                target: CapturedTarget {
                    def_id: def_id.clone(),
                    mir_module_path: format!("Mir/{}", rel_path.to_string_lossy()),
                    mir_module_sha256: mir_sha,
                },
                lean_module_name: format!("Mir.{suffix}"),
                item_kind: CapturedItemKind::Subject,
                associated_subject_def_id: None,
            },
            item_module_suffix: suffix.clone(),
            item_rel_path: rel_path.clone(),
            inline_requires: Vec::new(),
            inline_ensures: Vec::new(),
            inline_qualifiers: Vec::new(),
            external_specs: Vec::new(),
        };

        let new_verify = render_verify_module_with_options(&synthetic_bundle, authored);
        write_if_changed(verify_path, &new_verify)?;
        refreshed_bundles.push(synthetic_bundle);

        if let Some(ob_text) = ob_text_opt {
            let updated_ob = update_obligations_legacy_spec_bridge(
                &ob_text,
                &suffix,
                &def_id,
                authored.has_legacy_specs_defs,
            );
            write_if_changed(&obligation_path, &updated_ob)?;
        }
    }

    refreshed_bundles.sort_by(|a, b| a.subject.target.def_id.cmp(&b.subject.target.def_id));
    let crate_verify_path = generated_dir.join("CrateVerify.lean");
    if !refreshed_bundles.is_empty() {
        let crate_name = infer_crate_name(workspace_root, &refreshed_bundles);
        let crate_verify_contents = render_crate_verify_module(&crate_name, &refreshed_bundles);
        write_if_changed(&crate_verify_path, &crate_verify_contents)?;
    }

    let lakefile_text = fs::read_to_string(&lakefile_path)
        .map_err(|err| format!("failed to read {}: {}", lakefile_path.display(), err))?;
    let updated_lakefile = update_lakefile_authored_libs(
        &lakefile_text,
        &specs_roots,
        &assumptions_roots,
        &proof_roots,
    );
    write_if_changed(&lakefile_path, &updated_lakefile)?;

    Ok(())
}

fn collect_lean_files_recursive(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    if !dir.is_dir() {
        return Ok(());
    }
    let entries = fs::read_dir(dir)
        .map_err(|err| format!("failed to read directory {}: {}", dir.display(), err))?;
    for entry in entries {
        let entry = entry.map_err(|err| format!("failed to read dir entry: {err}"))?;
        let path = entry.path();
        if path.is_dir() {
            collect_lean_files_recursive(&path, out)?;
        } else if path.extension().and_then(|e| e.to_str()) == Some("lean") {
            out.push(path);
        }
    }
    Ok(())
}

fn rel_path_to_module_suffix(rel_path: &Path) -> String {
    let without_ext = rel_path.with_extension("");
    without_ext
        .components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join(".")
}

fn extract_def_id_comment(text: &str) -> Option<String> {
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("-- @anneal-def-id: ") {
            return Some(rest.trim().to_string());
        }
    }
    None
}

fn update_obligations_legacy_spec_bridge(
    ob_text: &str,
    suffix: &str,
    def_id: &str,
    has_legacy_specs_defs: bool,
) -> String {
    let import_line = format!("import Specs.{suffix}\n");
    let bridge_block = format!(
        "/-- Bridge instance synthesizing `ItemSpec \"{def_id}\"` from\n    \
         `Specs.{suffix}.pre` and `Specs.{suffix}.post`. -/\n\
         instance legacySpec : ItemSpec \"{def_id}\" where\n  \
         pre := Specs.{suffix}.pre\n  \
         post := Specs.{suffix}.post\n\n"
    );

    let mut cleaned = ob_text.replace(&import_line, "");
    cleaned = cleaned.replace(&bridge_block, "");

    if !has_legacy_specs_defs {
        return cleaned;
    }

    let ns_marker = format!("\nnamespace Obligations.{suffix}\n");
    if let Some(pos) = cleaned.find(&ns_marker) {
        cleaned.insert_str(pos, &format!("\n{import_line}"));
        cleaned = cleaned.replace(&format!("\n\n{import_line}"), &format!("\n{import_line}"));
    }

    let claim_marker = "/-- Canonical verification claim";
    if let Some(pos) = cleaned.find(claim_marker) {
        cleaned.insert_str(pos, &bridge_block);
    }

    cleaned
}

fn update_lakefile_authored_libs(
    lakefile_text: &str,
    specs_roots: &BTreeSet<String>,
    assumptions_roots: &BTreeSet<String>,
    proof_roots: &BTreeSet<String>,
) -> String {
    let mut kept_blocks = Vec::new();
    for block in lakefile_text.split("\n\n") {
        let trimmed = block.trim();
        if trimmed.is_empty() {
            continue;
        }
        if trimmed.contains("name = \"Specs\"")
            || trimmed.contains("name = \"Assumptions\"")
            || trimmed.contains("name = \"Proof\"")
        {
            continue;
        }
        kept_blocks.push(trimmed.to_string());
    }

    let format_roots = |roots: &BTreeSet<String>| -> String {
        roots
            .iter()
            .map(|r| format!("\"{r}\""))
            .collect::<Vec<_>>()
            .join(", ")
    };

    let verify_idx = kept_blocks
        .iter()
        .position(|b| b.contains("name = \"Verify\""))
        .unwrap_or(kept_blocks.len());

    let mut insert_blocks = Vec::new();
    if !specs_roots.is_empty() {
        insert_blocks.push(format!(
            "[[lean_lib]]\nname = \"Specs\"\nsrcDir = \"../anneal/proofs\"\nroots = [{}]",
            format_roots(specs_roots)
        ));
    }
    if !assumptions_roots.is_empty() {
        insert_blocks.push(format!(
            "[[lean_lib]]\nname = \"Assumptions\"\nsrcDir = \"../anneal/proofs\"\nroots = [{}]",
            format_roots(assumptions_roots)
        ));
    }
    if !proof_roots.is_empty() {
        insert_blocks.push(format!(
            "[[lean_lib]]\nname = \"Proof\"\nsrcDir = \"../anneal/proofs\"\nroots = [{}]",
            format_roots(proof_roots)
        ));
    }

    for (offset, blk) in insert_blocks.into_iter().enumerate() {
        kept_blocks.insert(verify_idx + offset, blk);
    }

    format!("{}\n", kept_blocks.join("\n\n"))
}

/// Locate a captured `Mir/<Item>.lean` file on disk from `config.units_dir` or
/// `config.workspace_root`.
fn find_source_mir_file(
    config: &ScaffoldConfig,
    record: &UnitTargetRecord,
    rel_item_path: &Path,
) -> Option<PathBuf> {
    let recorded_rel = Path::new(&record.target.mir_module_path);

    if let Some(ref units_dir) = config.units_dir
        && units_dir.is_dir()
    {
        let direct_recorded = units_dir.join(recorded_rel);
        if direct_recorded.is_file() {
            return Some(direct_recorded);
        }
        let direct_mir = units_dir.join("Mir").join(rel_item_path);
        if direct_mir.is_file() {
            return Some(direct_mir);
        }
        if let Ok(entries) = fs::read_dir(units_dir) {
            let mut subdirs: Vec<PathBuf> = entries
                .filter_map(|e| e.ok().map(|d| d.path()))
                .filter(|p| p.is_dir())
                .collect();
            subdirs.sort();
            for unit_subdir in subdirs {
                let candidate_recorded = unit_subdir.join(recorded_rel);
                if candidate_recorded.is_file() {
                    return Some(candidate_recorded);
                }
                let candidate_mir = unit_subdir.join("Mir").join(rel_item_path);
                if candidate_mir.is_file() {
                    return Some(candidate_mir);
                }
            }
        }
    }

    let workspace_recorded = config.workspace_root.join(recorded_rel);
    if workspace_recorded.is_file() {
        return Some(workspace_recorded);
    }

    None
}

/// Render `.anneal/lakefile.toml` wiring `Trusted` (`trusted/lean`), `Anneal`
/// (`theory`), `.anneal/generated` (`Mir`, `Obligations`, `Verify`), and any
/// authored libraries present in `anneal/proofs` (`Specs`, `Assumptions`,
/// `Proof`).
pub fn render_lakefile_toml(
    config: &ScaffoldConfig,
    records: &[UnitTargetRecord],
    bundles: &[SubjectObligationBundle],
) -> String {
    let (trusted_src_dir, theory_src_dir) = resolve_lean_library_paths(config);
    let proofs_root = config.workspace_root.join("anneal").join("proofs");

    let mut mir_roots = BTreeSet::new();
    for record in records {
        let suffix = derive_item_module_suffix(record);
        mir_roots.insert(format!("Mir.{suffix}"));
    }

    let mut specs_roots = BTreeSet::new();
    let mut assumptions_roots = BTreeSet::new();
    let mut obligations_roots = BTreeSet::new();
    let mut proof_roots = BTreeSet::new();
    let mut verify_roots = BTreeSet::new();
    for bundle in bundles {
        let item = &bundle.item_module_suffix;
        let authored = detect_authored_item_modules(&proofs_root, &bundle.item_rel_path);
        if authored.has_specs {
            specs_roots.insert(format!("Specs.{item}"));
        }
        if authored.has_assumptions {
            assumptions_roots.insert(format!("Assumptions.{item}"));
        }
        obligations_roots.insert(format!("Obligations.{item}"));
        if authored.has_proof {
            proof_roots.insert(format!("Proof.{item}"));
        }
        verify_roots.insert(format!("Verify.{item}"));
    }

    let format_roots = |roots: &BTreeSet<String>| -> String {
        roots
            .iter()
            .map(|r| format!("\"{r}\""))
            .collect::<Vec<_>>()
            .join(", ")
    };

    let default_targets = if bundles.is_empty() {
        "\"Verify\""
    } else {
        "\"Verify\", \"CrateVerify\""
    };
    let crate_verify_block = if bundles.is_empty() {
        ""
    } else {
        "\n[[lean_lib]]\n\
         name = \"CrateVerify\"\n\
         srcDir = \"generated\"\n\
         roots = [\"CrateVerify\"]\n"
    };

    let base_lakefile = format!(
        "name = \"AnnealVerification\"\n\
         defaultTargets = [{default_targets}]\n\n\
         [[lean_lib]]\n\
         name = \"Trusted\"\n\
         srcDir = \"{trusted_src_dir}\"\n\n\
         [[lean_lib]]\n\
         name = \"Anneal\"\n\
         srcDir = \"{theory_src_dir}\"\n\n\
         [[lean_lib]]\n\
         name = \"Mir\"\n\
         srcDir = \"generated\"\n\
         roots = [{mir_roots}]\n\n\
         [[lean_lib]]\n\
         name = \"Obligations\"\n\
         srcDir = \"generated\"\n\
         roots = [{obligations_roots}]\n\n\
         [[lean_lib]]\n\
         name = \"Verify\"\n\
         srcDir = \"generated\"\n\
         roots = [{verify_roots}]\n{crate_verify_block}",
        mir_roots = format_roots(&mir_roots),
        obligations_roots = format_roots(&obligations_roots),
        verify_roots = format_roots(&verify_roots),
    );

    update_lakefile_authored_libs(
        &base_lakefile,
        &specs_roots,
        &assumptions_roots,
        &proof_roots,
    )
}

fn infer_crate_name(workspace_root: &Path, bundles: &[SubjectObligationBundle]) -> String {
    let cargo_toml = workspace_root.join("Cargo.toml");
    if let Ok(raw) = fs::read_to_string(&cargo_toml) {
        let mut in_package = false;
        for line in raw.lines() {
            let trimmed = line.trim();
            if trimmed.starts_with('[') {
                in_package = trimmed == "[package]";
                continue;
            }
            if in_package
                && let Some(rest) = trimmed.strip_prefix("name")
                && let Some(eq_rest) = rest.trim_start().strip_prefix('=')
            {
                let unquoted = eq_rest.trim().trim_matches('"');
                if !unquoted.is_empty() {
                    return unquoted.replace('-', "_");
                }
            }
        }
    }
    if let Some(first) = bundles.first()
        && let Some(seg) = first.subject.target.def_id.split("::").next()
        && !seg.is_empty()
    {
        return seg.to_string();
    }
    "crate".to_string()
}

/// Resolve the `srcDir` values for `Trusted` (`trusted/lean`) and `Anneal`
/// (`theory`) in `.anneal/lakefile.toml`.
fn resolve_lean_library_paths(config: &ScaffoldConfig) -> (String, String) {
    let base_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    if let Some(ref repo_root) = config.anneal_repo_root {
        let abs_repo_root = crate::normalize_path_against(&base_dir, repo_root);
        let trusted = abs_repo_root
            .join("trusted/lean")
            .to_string_lossy()
            .into_owned();
        let theory = abs_repo_root.join("theory").to_string_lossy().into_owned();
        return (trusted, theory);
    }

    if let Ok(env_root) = std::env::var("ANNEAL_ROOT")
        && !env_root.trim().is_empty()
    {
        let abs_env_root = crate::normalize_path_against(&base_dir, Path::new(env_root.trim()));
        let trusted = abs_env_root
            .join("trusted/lean")
            .to_string_lossy()
            .into_owned();
        let theory = abs_env_root.join("theory").to_string_lossy().into_owned();
        return (trusted, theory);
    }

    let abs_workspace_root = crate::normalize_path_against(&base_dir, &config.workspace_root);
    if abs_workspace_root.join("trusted/lean").is_dir()
        && abs_workspace_root.join("theory").is_dir()
    {
        return ("../trusted/lean".to_string(), "../theory".to_string());
    }

    let mut current = abs_workspace_root.parent();
    let mut depth = 1usize;
    while let Some(ancestor) = current {
        if ancestor.join("trusted/lean").is_dir() && ancestor.join("theory").is_dir() {
            let prefix = "../".repeat(depth + 1);
            return (
                format!("{prefix}trusted/lean"),
                format!("{prefix}theory"),
            );
        }
        current = ancestor.parent();
        depth += 1;
    }

    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    if let Some(repo_root) = manifest_dir.parent().and_then(|p| p.parent())
        && repo_root.join("trusted/lean").is_dir()
        && repo_root.join("theory").is_dir()
    {
        return (
            repo_root.join("trusted/lean").to_string_lossy().into_owned(),
            repo_root.join("theory").to_string_lossy().into_owned(),
        );
    }

    if let Some(toolchain_root) = crate::setup::resolve_installed_toolchain() {
        let share_anneal = toolchain_root.join("share/anneal");
        if share_anneal.join("trusted/lean").is_dir() && share_anneal.join("theory").is_dir() {
            return (
                share_anneal
                    .join("trusted/lean")
                    .to_string_lossy()
                    .into_owned(),
                share_anneal.join("theory").to_string_lossy().into_owned(),
            );
        }
    }

    ("../trusted/lean".to_string(), "../theory".to_string())
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
            "cargo-anneal-scaffold-{}-{}-{}",
            prefix,
            std::process::id(),
            nanos
        ));
        fs::create_dir_all(&dir).expect("create temp dir");
        dir
    }

    #[test]
    fn rerunning_scaffold_updates_generated_obligations_and_preserves_authored_files() {
        let workspace = unique_temp_dir("idempotent");
        let units_dir = workspace.join("target/anneal/units/my_crate-01");
        let unit_mir_dir = units_dir.join("Mir/MyCrate");
        fs::create_dir_all(&unit_mir_dir).expect("create unit mir dir");

        let mir_content = "prelude\nimport Init.Core\nimport Trusted\n\nnamespace Mir.MyCrate.compute\nend Mir.MyCrate.compute\n";
        let mir_hash = sha256_hex(mir_content.as_bytes());
        fs::write(unit_mir_dir.join("compute.lean"), mir_content).expect("write unit mir");

        let initial_records = vec![UnitTargetRecord {
            target: CapturedTarget {
                def_id: "my_crate::compute".to_string(),
                mir_module_path: "Mir/MyCrate/compute.lean".to_string(),
                mir_module_sha256: mir_hash.clone(),
            },
            lean_module_name: "Mir.MyCrate.compute".to_string(),
            item_kind: CapturedItemKind::Subject,
            associated_subject_def_id: None,
        }];

        // Default scaffold run: creates only `.anneal/generated/` without
        // stamping generate-then-edit files in `anneal/proofs/`.
        let report1 =
            scaffold_workspace(&workspace, &initial_records).expect("first scaffold run");
        assert_eq!(report1.created_spec_files.len(), 0);
        assert_eq!(report1.preserved_spec_files.len(), 0);
        assert_eq!(report1.created_proof_files.len(), 0);
        assert_eq!(report1.preserved_proof_files.len(), 0);

        let mir_dest = workspace.join(".anneal/generated/Mir/MyCrate/compute.lean");
        let obligation_path =
            workspace.join(".anneal/generated/Obligations/MyCrate/compute.lean");
        let verify_path = workspace.join(".anneal/generated/Verify/MyCrate/compute.lean");
        let spec_path = workspace.join("anneal/proofs/Specs/MyCrate/compute.lean");
        let proof_path = workspace.join("anneal/proofs/Proof/MyCrate/compute.lean");

        assert_eq!(
            fs::read_to_string(&mir_dest).expect("read placed mir"),
            mir_content
        );
        assert!(obligation_path.is_file());
        assert!(verify_path.is_file());
        assert!(!spec_path.exists());
        assert!(!proof_path.exists());

        let toolchain_text =
            fs::read_to_string(&report1.toolchain_path).expect("read lean-toolchain");
        assert_eq!(toolchain_text, "leanprover/lean4:v4.34.1\n");

        let lakefile_text =
            fs::read_to_string(&report1.lakefile_path).expect("read lakefile.toml");
        assert!(lakefile_text.contains("name = \"Trusted\""));
        assert!(lakefile_text.contains("name = \"Anneal\""));
        assert!(lakefile_text.contains("roots = [\"Obligations.MyCrate.compute\"]"));
        assert!(!lakefile_text.contains("name = \"Specs\""));
        assert!(!lakefile_text.contains("name = \"Proof\""));
        assert!(lakefile_text.contains("roots = [\"Verify.MyCrate.compute\"]"));

        // Opt-in template initialization creates Proof/<Item>.lean and
        // Specs/<Item>.lean when requested.
        let cfg = ScaffoldConfig::new(&workspace);
        scaffold_init_spec_templates(&cfg, &initial_records).expect("init spec templates");
        let init_report =
            scaffold_init_proof_templates(&cfg, &initial_records).expect("init proof templates");
        assert_eq!(init_report.created_proof_files, vec![proof_path.clone()]);
        assert_eq!(init_report.preserved_spec_files, vec![spec_path.clone()]);

        // Simulate user edits to Specs/<Item>.lean and Proof/<Item>.lean, plus
        // stale edits in Obligations/<Item>.lean.
        let custom_spec = "-- User-edited custom specification\ndef pre (args : List Value) : Prop := args ≠ .nil\ndef post (args : List Value) (ret : Value) : Prop := True\n";
        let custom_proof = "-- User-edited custom proof\ntheorem verified : VerificationResult Obligations.MyCrate.compute.claim := custom_witness\n";
        fs::write(&spec_path, custom_spec).expect("write custom spec");
        fs::write(&proof_path, custom_proof).expect("write custom proof");
        fs::write(&obligation_path, "-- STALE GENERATED FILE\n")
            .expect("overwrite obligation with stale content");

        // Second scaffold run with a newly attached inline requires companion.
        let updated_records = vec![
            initial_records[0].clone(),
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "my_crate::__anodized_fn_requires_compute".to_string(),
                    mir_module_path: "Mir/MyCrate/__anodized_fn_requires_compute.lean"
                        .to_string(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: "Mir.MyCrate.__anodized_fn_requires_compute".to_string(),
                item_kind: CapturedItemKind::InlineSpecRequires,
                associated_subject_def_id: Some("my_crate::compute".to_string()),
            },
        ];

        let report2 =
            scaffold_workspace(&workspace, &updated_records).expect("second scaffold run");
        assert_eq!(report2.created_spec_files.len(), 0);
        assert_eq!(report2.preserved_spec_files, vec![spec_path.clone()]);
        assert_eq!(report2.created_proof_files.len(), 0);
        assert_eq!(report2.preserved_proof_files, vec![proof_path.clone()]);

        // Verify that generated Obligations/<Item>.lean was overwritten and
        // includes the newly linked companion item.
        let refreshed_obligation =
            fs::read_to_string(&obligation_path).expect("read refreshed obligation");
        assert!(!refreshed_obligation.contains("STALE GENERATED FILE"));
        assert!(refreshed_obligation.contains("def defaultPre (args : List Value) : Prop :="));
        assert!(refreshed_obligation.contains("my_crate::__anodized_fn_requires_compute"));

        // Verify that user edits in Specs/<Item>.lean and Proof/<Item>.lean
        // were preserved byte-for-byte.
        assert_eq!(
            fs::read_to_string(&spec_path).expect("read preserved spec"),
            custom_spec
        );
        assert_eq!(
            fs::read_to_string(&proof_path).expect("read preserved proof"),
            custom_proof
        );

        let _ = fs::remove_dir_all(&workspace);
    }

    #[test]
    fn rescaffolding_a_smaller_item_set_prunes_stale_generated_modules() {
        let workspace = unique_temp_dir("prune-stale");
        let record = |name: &str| UnitTargetRecord {
            target: CapturedTarget {
                def_id: format!("my_crate::{name}"),
                mir_module_path: format!("Mir/MyCrate/{name}.lean"),
                mir_module_sha256: String::new(),
            },
            lean_module_name: format!("Mir.MyCrate.{name}"),
            item_kind: CapturedItemKind::Subject,
            associated_subject_def_id: None,
        };

        scaffold_workspace(&workspace, &[record("keep"), record("gone")])
            .expect("scaffold two items");
        let generated = workspace.join(".anneal/generated");
        for category in ["Mir", "Obligations", "Verify"] {
            assert!(generated.join(category).join("MyCrate/keep.lean").is_file());
            assert!(generated.join(category).join("MyCrate/gone.lean").is_file());
        }

        // Dropping `gone` from the captured records must remove every generated
        // module that only the previous run produced, while leaving `keep`
        // (and the authored `anneal/proofs/` tree) untouched.
        let proof_path = workspace.join("anneal/proofs/Proof/MyCrate/gone.lean");
        fs::create_dir_all(proof_path.parent().expect("proof parent")).expect("create proof dir");
        fs::write(&proof_path, "-- authored proof for a removed item\n").expect("write proof");

        scaffold_workspace(&workspace, &[record("keep")]).expect("scaffold one item");
        for category in ["Mir", "Obligations", "Verify"] {
            assert!(generated.join(category).join("MyCrate/keep.lean").is_file());
            assert!(
                !generated.join(category).join("MyCrate/gone.lean").exists(),
                "stale {category}/MyCrate/gone.lean must be pruned"
            );
        }
        assert!(proof_path.is_file(), "authored files are never pruned");

        let lakefile_text =
            fs::read_to_string(workspace.join(".anneal/lakefile.toml")).expect("read lakefile");
        assert!(lakefile_text.contains("roots = [\"Verify.MyCrate.keep\"]"));

        let _ = fs::remove_dir_all(&workspace);
    }

    #[test]
    fn detects_stateful_specs_and_proofs_and_wires_verify_module() {
        let workspace = unique_temp_dir("stateful-detect");
        let proofs_root = workspace.join("anneal/proofs");
        let rel_path = Path::new("MyCrate/ptr_op.lean");
        let spec_path = proofs_root.join("Specs").join(rel_path);
        let proof_path = proofs_root.join("Proof").join(rel_path);

        fs::create_dir_all(spec_path.parent().expect("spec parent")).expect("create spec dir");
        fs::create_dir_all(proof_path.parent().expect("proof parent")).expect("create proof dir");

        // Stateless spec and proof: `is_stateful` should be false.
        fs::write(
            &spec_path,
            "import Obligations.MyCrate.ptr_op\ninstance : ItemSpec \"my_crate::ptr_op\" where\n  pre := fun _ => True\n  post := fun _ _ => True\n",
        )
        .expect("write stateless spec");
        fs::write(
            &proof_path,
            "theorem verified : VerificationResult Obligations.MyCrate.ptr_op.claim := sorry\n",
        )
        .expect("write stateless proof");

        let stateless_detected = detect_authored_item_modules(&proofs_root, rel_path);
        assert!(stateless_detected.has_specs);
        assert!(!stateless_detected.has_legacy_specs_defs);
        assert!(stateless_detected.has_proof);
        assert!(!stateless_detected.is_stateful);

        // Stateful spec via `StatefulItemSpec`: `is_stateful` should be true.
        fs::write(
            &spec_path,
            "import Obligations.MyCrate.ptr_op\ninstance : StatefulItemSpec \"my_crate::ptr_op\" where\n  pre := fun _ _ => True\n  post := fun _ _ _ _ => True\n",
        )
        .expect("write stateful spec");
        let spec_stateful_detected = detect_authored_item_modules(&proofs_root, rel_path);
        assert!(spec_stateful_detected.has_specs);
        assert!(!spec_stateful_detected.has_legacy_specs_defs);
        assert!(spec_stateful_detected.is_stateful);

        // Reset spec to stateless, make proof use `StatefulVerificationResult`:
        // `is_stateful` should be true.
        fs::write(
            &spec_path,
            "import Obligations.MyCrate.ptr_op\ninstance : ItemSpec \"my_crate::ptr_op\" where\n  pre := fun _ => True\n  post := fun _ _ => True\n",
        )
        .expect("reset stateless spec");
        fs::write(
            &proof_path,
            "theorem verified : StatefulVerificationResult Obligations.MyCrate.ptr_op.statefulClaim := sorry\n",
        )
        .expect("write stateful proof");
        let proof_stateful_detected = detect_authored_item_modules(&proofs_root, rel_path);
        assert!(proof_stateful_detected.has_proof);
        assert!(proof_stateful_detected.is_stateful);

        // Scaffold the workspace and verify that `Verify/MyCrate/ptr_op.lean`
        // emits `StatefulVerificationResult Obligations.MyCrate.ptr_op.statefulClaim`.
        let records = vec![UnitTargetRecord {
            target: CapturedTarget {
                def_id: "my_crate::ptr_op".to_string(),
                mir_module_path: "Mir/MyCrate/ptr_op.lean".to_string(),
                mir_module_sha256: String::new(),
            },
            lean_module_name: "Mir.MyCrate.ptr_op".to_string(),
            item_kind: CapturedItemKind::Subject,
            associated_subject_def_id: None,
        }];
        scaffold_workspace(&workspace, &records).expect("scaffold stateful workspace");

        let verify_path = workspace.join(".anneal/generated/Verify/MyCrate/ptr_op.lean");
        let verify_text = fs::read_to_string(&verify_path).expect("read verify module");
        assert!(verify_text.contains(
            "theorem verified : StatefulVerificationResult Obligations.MyCrate.ptr_op.statefulClaim :=\n  \
               Proof.MyCrate.ptr_op.verified"
        ));

        let _ = fs::remove_dir_all(&workspace);
    }

    #[test]
    fn init_specs_and_init_proofs_together_imports_specs_in_created_proof() {
        let workspace = unique_temp_dir("init-specs-and-proofs");
        let records = vec![UnitTargetRecord {
            target: CapturedTarget {
                def_id: "my_crate::add".to_string(),
                mir_module_path: "Mir/MyCrate/add.lean".to_string(),
                mir_module_sha256: String::new(),
            },
            lean_module_name: "Mir.MyCrate.add".to_string(),
            item_kind: CapturedItemKind::Subject,
            associated_subject_def_id: None,
        }];

        let cfg = ScaffoldConfig::new(&workspace)
            .with_init_spec_templates(true)
            .with_init_proof_templates(true);
        let report = scaffold_workspace_with_config(&cfg, &records)
            .expect("scaffold with both init_spec_templates and init_proof_templates");

        let spec_path = workspace.join("anneal/proofs/Specs/MyCrate/add.lean");
        let proof_path = workspace.join("anneal/proofs/Proof/MyCrate/add.lean");
        assert_eq!(report.created_spec_files, vec![spec_path.clone()]);
        assert_eq!(report.created_proof_files, vec![proof_path.clone()]);

        let proof_text = fs::read_to_string(&proof_path).expect("read created proof template");
        assert!(
            proof_text.contains("import Obligations.MyCrate.add\nimport Specs.MyCrate.add\n"),
            "created Proof template must automatically import Specs.MyCrate.add when --init-specs and --init-proofs are used together:\n{proof_text}"
        );

        let _ = fs::remove_dir_all(&workspace);
    }
}
