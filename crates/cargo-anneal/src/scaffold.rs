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

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};

use anneal_rustc_capture::lean_emit::render_mir_module_header;
use anneal_rustc_capture::{CapturedItemKind, CapturedTarget, UnitTargetRecord, sha256_hex};

use crate::obligations::{
    AuthoredItemModules, CalleeContractRef, ExternalSpecContractRef, SubjectObligationBundle,
    TransitiveCalleeRef,
    collect_external_spec_contracts, derive_item_module_suffix, group_subject_obligations,
    module_suffix_to_rel_path, render_crate_verify_module, render_generated_assumptions_module,
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
    /// Paths to `.anneal/generated/Assumptions/<Item>.lean` modules written for
    /// `#[spec(trusted, ...)]` items.
    pub generated_assumption_files: Vec<PathBuf>,
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
        fs::read_to_string(&spec_path)
            .ok()
            .map(|raw| crate::agent::strip_lean_comments(&raw))
    } else {
        None
    };
    let has_legacy_specs_defs = spec_text
        .as_deref()
        .is_some_and(|text| !text.contains("ItemSpec") && !text.contains("import Obligations."));

    let has_proof = proof_path.is_file();
    let proof_text = if has_proof {
        fs::read_to_string(&proof_path)
            .ok()
            .map(|raw| crate::agent::strip_lean_comments(&raw))
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
                    || text.contains("UbExceptionItemProof")
                    || ((text.contains("ubExceptionClaim")
                        || text.contains("polyUbExceptionClaim"))
                        && !text.contains("ModularVerificationResult"))
            }));

    let is_modular = !is_ub_exception
        && (spec_is_modular
            || proof_text.as_deref().is_some_and(|text| {
                text.contains("modularClaim")
                    || text.contains("polyModularClaim")
                    || text.contains("ModularVerificationResult")
                    || text.contains("ModularItemProof")
            }));

    let is_equiv = !is_ub_exception
        && !is_modular
        && (spec_text.as_deref().is_some_and(|text| {
            text.contains("StatefulEquivItemSpec") || text.contains("refineEquivSpec")
        }) || proof_text.as_deref().is_some_and(|text| {
            text.contains("equivClaim")
                || text.contains("StatefulEquivVerificationResult")
                || text.contains("StatefulEquivItemProof")
        }));

    let is_total = !is_ub_exception
        && !is_modular
        && !is_equiv
        && (spec_text.as_deref().is_some_and(|text| {
            text.contains("TotalItemSpec") || text.contains("refineTotalSpec")
        }) || proof_text.as_deref().is_some_and(|text| {
            text.contains("totalClaim")
                || text.contains("polyTotalClaim")
                || text.contains("TotalVerificationResult")
                || text.contains("TotalItemProof")
        }));

    let spec_is_stateful = spec_text.as_deref().is_some_and(|text| {
        text.contains("StatefulItemSpec")
            || text.contains("refineStatefulSpec")
            || text.contains("refineSafeStatefulSpec")
    });
    let proof_is_stateful = proof_text.as_deref().is_some_and(|text| {
        text.contains("statefulClaim")
            || text.contains("polyStatefulClaim")
            || text.contains("StatefulVerificationResult")
            || text.contains("StatefulItemProof")
    });
    let is_polymorphic = proof_text.as_deref().is_some_and(|text| {
        text.contains("polyClaim")
            || text.contains("polyStatefulClaim")
            || text.contains("polyTotalClaim")
            || text.contains("polyModularClaim")
            || text.contains("polyUbExceptionClaim")
    });

    AuthoredItemModules {
        has_specs,
        has_legacy_specs_defs,
        has_assumptions: assumptions_path.is_file(),
        has_generated_assumptions: false,
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
        is_polymorphic,
    }
}

/// Extract all `.fnDef "<def_id>"` and `implPath := "<def_id>"` references from
/// a placed `.anneal/generated/Mir/<Item>.lean` module in deterministic
/// first-appearance order.
fn extract_called_fn_defs(mir_text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();
    for marker in [".fnDef \"", "implPath := \""] {
        let mut rest = mir_text;
        while let Some(pos) = rest.find(marker) {
            let after = &rest[pos + marker.len()..];
            if let Some(end_quote) = after.find('"') {
                let def_id = &after[..end_quote];
                if !def_id.is_empty() && seen.insert(def_id.to_string()) {
                    out.push(def_id.to_string());
                }
                rest = &after[end_quote + 1..];
            } else {
                break;
            }
        }
    }
    out
}

/// Call-graph lookup tables shared by every transitive callee closure computed
/// during scaffolding.
struct CalleeGraph<'a> {
    /// Linkable captured MIR bodies keyed by canonical `def_id`, mapped to their
    /// dotted module suffix and relative `Mir/` path.
    callable_by_def_id: &'a BTreeMap<String, (String, PathBuf)>,
    /// Trait method `def_id` to the `def_id`s of every captured implementation.
    trait_impls_by_method: &'a BTreeMap<String, Vec<String>>,
    /// Explicit `#[external_spec(for = <target>)]` overrides keyed by target.
    external_spec_contracts: &'a BTreeMap<String, ExternalSpecContractRef>,
    /// Sibling `#[spec(trusted)]` subjects keyed by canonical `def_id`.
    trusted_callees: &'a BTreeMap<String, CalleeContractRef>,
}

/// Mutable worklist state of one transitive callee closure.
#[derive(Default)]
struct CalleeClosureState {
    visited: BTreeSet<String>,
    ext_seen: BTreeSet<String>,
    trusted_seen: BTreeSet<String>,
    queue: VecDeque<String>,
    external_specs: Vec<ExternalSpecContractRef>,
    trusted_callees: Vec<CalleeContractRef>,
}

impl CalleeGraph<'_> {
    /// Record a reference to `r` found in a body reachable from
    /// `subject_def_id`: an overridden target is recorded as an external spec
    /// (and not traversed), a `#[spec(trusted)]` sibling is recorded as a
    /// called callee (and not traversed), a linkable body is queued once, and
    /// a trait method additionally queues (or records as overridden/trusted)
    /// each of its captured implementations.
    fn enqueue_ref(&self, r: &str, subject_def_id: &str, state: &mut CalleeClosureState) {
        if r != subject_def_id
            && let Some(ext) = self.external_spec_contracts.get(r)
        {
            if state.ext_seen.insert(r.to_string()) {
                state.external_specs.push(ext.clone());
            }
            return;
        }
        if r != subject_def_id
            && let Some(tr) = self.trusted_callees.get(r)
        {
            if state.trusted_seen.insert(r.to_string()) {
                state.trusted_callees.push(tr.clone());
            }
            return;
        }
        if self.callable_by_def_id.contains_key(r) && state.visited.insert(r.to_string()) {
            state.queue.push_back(r.to_string());
        }
        if let Some(impls) = self.trait_impls_by_method.get(r) {
            for impl_id in impls {
                if impl_id != subject_def_id
                    && let Some(ext) = self.external_spec_contracts.get(impl_id)
                {
                    if state.ext_seen.insert(impl_id.clone()) {
                        state.external_specs.push(ext.clone());
                    }
                    continue;
                }
                if impl_id != subject_def_id
                    && let Some(tr) = self.trusted_callees.get(impl_id)
                {
                    if state.trusted_seen.insert(impl_id.clone()) {
                        state.trusted_callees.push(tr.clone());
                    }
                    continue;
                }
                if self.callable_by_def_id.contains_key(impl_id)
                    && state.visited.insert(impl_id.clone())
                {
                    state.queue.push_back(impl_id.clone());
                }
            }
        }
    }

    /// Compute the cycle-safe breadth-first closure of linkable callee bodies
    /// reachable from `root_refs`, returning the linked bodies in discovery
    /// order together with the overridden `#[external_spec]` targets and
    /// `#[spec(trusted)]` sibling callees reached.
    fn closure(
        &self,
        root_refs: &[String],
        subject_def_id: &str,
        read_outgoing: &mut dyn FnMut(&Path) -> Vec<String>,
    ) -> (
        Vec<TransitiveCalleeRef>,
        Vec<ExternalSpecContractRef>,
        Vec<CalleeContractRef>,
    ) {
        let mut state = CalleeClosureState::default();
        for r in root_refs {
            self.enqueue_ref(r, subject_def_id, &mut state);
        }
        let mut linked = Vec::new();
        while let Some(callee_def_id) = state.queue.pop_front() {
            let Some((callee_suffix, callee_rel_path)) =
                self.callable_by_def_id.get(&callee_def_id).cloned()
            else {
                continue;
            };
            linked.push(TransitiveCalleeRef {
                def_id: callee_def_id,
                item_module_suffix: callee_suffix,
            });
            for r in &read_outgoing(&callee_rel_path) {
                self.enqueue_ref(r, subject_def_id, &mut state);
            }
        }
        (linked, state.external_specs, state.trusted_callees)
    }
}

/// Populate `bundle.transitive_callees`, `bundle.external_spec_callees`,
/// `bundle.called_callees`, `bundle.spec_callees`, and
/// `bundle.spec_companions_with_calls` for each subject bundle by computing the
/// cycle-safe transitive closure of reachable `.fnDef "<callee_def_id>"` and
/// trait-impl references across all captured MIR bodies (`Subject`,
/// `UnsafeTraitImpl`, `Callee`, `Model`, `TypeInvariant`), excluding any target
/// with an explicit `#[external_spec(for = <target>)]` override or
/// `#[spec(trusted)]` attribute.
///
/// The subject body's closure becomes `defaultCallees`; the closure of its
/// `requires` / `ensures` companions (including those of reachable
/// `#[external_spec]` contracts) becomes `defaultSpecCallees`.
pub(crate) fn populate_called_callees(
    mir_root: &Path,
    records: &[UnitTargetRecord],
    bundles: &mut [SubjectObligationBundle],
) {
    let external_spec_contracts = collect_external_spec_contracts(records);
    let trusted_subject_def_ids: BTreeSet<String> = bundles
        .iter()
        .filter(|b| b.has_rust_trusted_attr())
        .map(|b| b.subject.target.def_id.clone())
        .collect();

    let trusted_callees_by_def_id: BTreeMap<String, CalleeContractRef> = bundles
        .iter()
        .filter(|b| {
            b.has_rust_trusted_attr()
                && !external_spec_contracts.contains_key(&b.subject.target.def_id)
        })
        .map(|b| {
            (
                b.subject.target.def_id.clone(),
                CalleeContractRef {
                    def_id: b.subject.target.def_id.clone(),
                    item_module_suffix: b.item_module_suffix.clone(),
                    req_module_suffix: b.inline_requires.first().map(derive_item_module_suffix),
                    ens_module_suffix: b.inline_ensures.first().map(derive_item_module_suffix),
                },
            )
        })
        .collect();

    let mut callable_by_def_id: BTreeMap<String, (String, PathBuf)> = BTreeMap::new();
    let mut trait_impls_by_method: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut record_by_rel_path: BTreeMap<PathBuf, &UnitTargetRecord> = BTreeMap::new();
    for record in records {
        let rec_suffix = derive_item_module_suffix(record);
        let rec_rel_path = module_suffix_to_rel_path(&rec_suffix);
        record_by_rel_path.insert(rec_rel_path.clone(), record);
        for entry in &record.trait_impls {
            if !entry.trait_method_def_path.is_empty() && !entry.impl_path.is_empty() {
                trait_impls_by_method
                    .entry(entry.trait_method_def_path.clone())
                    .or_default()
                    .push(entry.impl_path.clone());
            }
        }
        if !matches!(
            record.item_kind,
            CapturedItemKind::Subject
                | CapturedItemKind::UnsafeTraitImpl
                | CapturedItemKind::Callee
                | CapturedItemKind::Model
                | CapturedItemKind::TypeInvariant
        ) {
            continue;
        }
        if record.target.mir_module_path.is_empty() {
            continue;
        }
        if external_spec_contracts.contains_key(&record.target.def_id)
            || trusted_subject_def_ids.contains(&record.target.def_id)
        {
            continue;
        }
        callable_by_def_id.insert(record.target.def_id.clone(), (rec_suffix, rec_rel_path));
    }

    let graph = CalleeGraph {
        callable_by_def_id: &callable_by_def_id,
        trait_impls_by_method: &trait_impls_by_method,
        external_spec_contracts: &external_spec_contracts,
        trusted_callees: &trusted_callees_by_def_id,
    };

    let fallback_cfg = mir_root
        .parent()
        .and_then(|g| g.parent())
        .and_then(|d| d.parent())
        .map(ScaffoldConfig::new);

    let mut outgoing_cache: BTreeMap<PathBuf, Vec<String>> = BTreeMap::new();
    let mut read_outgoing = |rel_path: &Path| -> Vec<String> {
        if let Some(cached) = outgoing_cache.get(rel_path) {
            return cached.clone();
        }
        let mir_path = mir_root.join(rel_path);
        let resolved_path = if mir_path.is_file() {
            Some(mir_path)
        } else if let Some(ref cfg) = fallback_cfg
            && let Some(rec) = record_by_rel_path.get(rel_path)
        {
            find_source_mir_file(cfg, rec, rel_path)
        } else {
            None
        };
        let refs = resolved_path
            .and_then(|p| fs::read_to_string(p).ok())
            .map(|txt| extract_called_fn_defs(&txt))
            .unwrap_or_default();
        outgoing_cache.insert(rel_path.to_path_buf(), refs.clone());
        refs
    };

    for bundle in bundles.iter_mut() {
        let root_refs = read_outgoing(&bundle.item_rel_path);
        let subject_def_id = bundle.subject.target.def_id.clone();
        let (linked, external_specs, trusted_callees) =
            graph.closure(&root_refs, &subject_def_id, &mut read_outgoing);
        bundle.transitive_callees = linked;
        bundle.external_spec_callees = external_specs;
        bundle.called_callees = trusted_callees;

        let mut companion_suffixes: Vec<String> = Vec::new();
        for companion in bundle.inline_requires.iter().chain(bundle.inline_ensures.iter()) {
            companion_suffixes.push(derive_item_module_suffix(companion));
        }
        for ext in &bundle.external_spec_callees {
            companion_suffixes.extend(ext.req_module_suffix.iter().cloned());
            companion_suffixes.extend(ext.ens_module_suffix.iter().cloned());
        }
        let mut spec_root_refs: Vec<String> = Vec::new();
        let mut seen_companions: BTreeSet<String> = BTreeSet::new();
        for suffix in companion_suffixes {
            if !seen_companions.insert(suffix.clone()) {
                continue;
            }
            let refs = read_outgoing(&module_suffix_to_rel_path(&suffix));
            if !refs.is_empty() {
                bundle.spec_companions_with_calls.insert(suffix);
            }
            for r in refs {
                if !spec_root_refs.contains(&r) {
                    spec_root_refs.push(r);
                }
            }
        }
        // Overridden targets reached only from predicates are not added to the
        // modular environment: predicates are evaluated by
        // `MirBoolPredicateHoldsWithCallees`, which has no handler.
        let (spec_linked, _predicate_external_specs, _predicate_trusted_callees) =
            graph.closure(&spec_root_refs, &subject_def_id, &mut read_outgoing);
        bundle.spec_callees = spec_linked;
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

    let mut bundles = group_subject_obligations(&sorted_records);
    populate_called_callees(&mir_root, &sorted_records, &mut bundles);
    let generated_assumptions_root = generated_dir.join("Assumptions");

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

        if bundle.has_rust_trusted_attr() && !authored.has_assumptions && !authored.has_proof {
            authored.has_generated_assumptions = true;
            let gen_assumptions_path = generated_assumptions_root.join(&bundle.item_rel_path);
            let gen_assumptions_contents =
                render_generated_assumptions_module(bundle, authored);
            write_if_changed(&gen_assumptions_path, &gen_assumptions_contents)?;
            report.generated_assumption_files.push(gen_assumptions_path);
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
        .chain(&report.generated_assumption_files)
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
        let crate_name = infer_crate_name(
            &config.workspace_root,
            config.units_dir.as_deref(),
            &bundles,
        );
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
    for category in ["Mir", "Obligations", "Assumptions", "Verify"] {
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
    let generated_assumptions_root = generated_dir.join("Assumptions");
    let mut specs_roots = BTreeSet::new();
    let mut assumptions_roots = BTreeSet::new();
    let mut generated_assumptions_roots = BTreeSet::new();
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
        let gen_assumptions_path = generated_assumptions_root.join(&rel_path);
        if gen_assumptions_path.is_file() && !authored.has_assumptions && !authored.has_proof {
            authored.has_generated_assumptions = true;
            generated_assumptions_roots.insert(format!("Assumptions.{suffix}"));
        }
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
        let mut synthetic_bundle = SubjectObligationBundle {
            subject: UnitTargetRecord {
                target: CapturedTarget {
                    def_id: def_id.clone(),
                    mir_module_path: format!("Mir/{}", rel_path.to_string_lossy()),
                    mir_module_sha256: mir_sha,
                },
                lean_module_name: format!("Mir.{suffix}"),
                item_kind: CapturedItemKind::Subject,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            },
            item_module_suffix: suffix.clone(),
            item_rel_path: rel_path.clone(),
            inline_requires: Vec::new(),
            inline_ensures: Vec::new(),
            inline_qualifiers: Vec::new(),
            external_specs: Vec::new(),
            called_callees: Vec::new(),
            transitive_callees: Vec::new(),
            external_spec_callees: Vec::new(),
            spec_callees: Vec::new(),
            spec_companions_with_calls: BTreeSet::new(),
        };
        if let Some(ref ob_text) = ob_text_opt {
            rehydrate_bundle_from_obligations_text(
                &mut synthetic_bundle,
                ob_text,
                Some(&obligations_root),
            );
        }

        let should_rerender_verify = authored.has_proof
            || authored.has_specs
            || authored.has_assumptions
            || verify_text.contains(&format!("import Proof.{suffix}"))
            || verify_text.contains(&format!("import Specs.{suffix}"))
            || verify_text.contains(&format!("import Assumptions.{suffix}"));
        if should_rerender_verify {
            let new_verify = render_verify_module_with_options(&synthetic_bundle, authored);
            write_if_changed(verify_path, &new_verify)?;
        }
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
        let default_units = workspace_root.join("target").join("anneal").join("units");
        let crate_name = infer_crate_name(
            workspace_root,
            default_units.is_dir().then_some(default_units.as_path()),
            &refreshed_bundles,
        );
        let crate_verify_contents = render_crate_verify_module(&crate_name, &refreshed_bundles);
        write_if_changed(&crate_verify_path, &crate_verify_contents)?;
    }

    let lakefile_text = fs::read_to_string(&lakefile_path)
        .map_err(|err| format!("failed to read {}: {}", lakefile_path.display(), err))?;
    let updated_lakefile = update_lakefile_authored_libs(
        &lakefile_text,
        &specs_roots,
        &assumptions_roots,
        &generated_assumptions_roots,
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

/// Reconstruct companion, transitive-callee, external-spec, and trusted-callee
/// metadata on `bundle` from an existing `.anneal/generated/Obligations/<Item>.lean`
/// file so `refresh_workspace_assembly` preserves inline companions,
/// `defaultCallees`, `#[external_spec]` contracts, and sibling `#[spec(trusted)]`
/// callee references when re-rendering `Verify/<Item>.lean`.
fn rehydrate_bundle_from_obligations_text(
    bundle: &mut SubjectObligationBundle,
    ob_text: &str,
    obligations_root: Option<&Path>,
) {
    let parse_linked_item = |line: &str, prefix: &str| -> Option<(String, String)> {
        let rest = line.strip_prefix(prefix)?;
        let (def_id, after) = rest.split_once("` (`")?;
        let (lean_mod, _) = after.split_once("`)")?;
        Some((def_id.to_string(), lean_mod.to_string()))
    };
    let extract_mir_body_suffixes = |line: &str| -> Vec<String> {
        let mut out = Vec::new();
        let mut rest = line;
        while let Some(pos) = rest.find("Mir.") {
            let after_mir = &rest[pos + "Mir.".len()..];
            if let Some(body_pos) = after_mir.find(".body") {
                let candidate = &after_mir[..body_pos];
                if !candidate.is_empty()
                    && candidate
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.')
                {
                    out.push(candidate.to_string());
                    rest = &after_mir[body_pos + ".body".len()..];
                    continue;
                }
            }
            rest = &after_mir[1..];
        }
        out
    };
    let subject_def_id = bundle.subject.target.def_id.clone();
    let lines: Vec<&str> = ob_text.lines().collect();
    for (idx, &line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if let Some(callee_suffix) = trimmed.strip_prefix("import Obligations.") {
            let callee_suffix = callee_suffix.trim();
            if !callee_suffix.is_empty() && callee_suffix != bundle.item_module_suffix {
                let mut callee_def_id = callee_suffix.to_string();
                let mut req_module_suffix = None;
                let mut ens_module_suffix = None;
                if let Some(ob_root) = obligations_root {
                    let callee_ob_path = ob_root.join(module_suffix_to_rel_path(callee_suffix));
                    if let Ok(callee_ob_text) = fs::read_to_string(&callee_ob_path) {
                        for c_line in callee_ob_text.lines() {
                            let c_trimmed = c_line.trim();
                            if let Some(rest) =
                                c_trimmed.strip_prefix("Disposable verification obligations for `")
                                && let Some((did, _)) = rest.split_once("`.")
                            {
                                callee_def_id = did.to_string();
                            } else if req_module_suffix.is_none()
                                && let Some((_, lean_mod)) =
                                    parse_linked_item(c_trimmed, "- Inline requires: `")
                            {
                                req_module_suffix = Some(
                                    lean_mod
                                        .strip_prefix("Mir.")
                                        .unwrap_or(&lean_mod)
                                        .to_string(),
                                );
                            } else if ens_module_suffix.is_none()
                                && let Some((_, lean_mod)) =
                                    parse_linked_item(c_trimmed, "- Inline ensures: `")
                            {
                                ens_module_suffix = Some(
                                    lean_mod
                                        .strip_prefix("Mir.")
                                        .unwrap_or(&lean_mod)
                                        .to_string(),
                                );
                            }
                        }
                    }
                }
                bundle.called_callees.push(CalleeContractRef {
                    def_id: callee_def_id,
                    item_module_suffix: callee_suffix.to_string(),
                    req_module_suffix,
                    ens_module_suffix,
                });
            }
        } else if let Some((def_id, lean_mod)) = parse_linked_item(trimmed, "- Inline requires: `")
        {
            bundle.inline_requires.push(UnitTargetRecord {
                target: CapturedTarget {
                    def_id,
                    mir_module_path: String::new(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: lean_mod,
                item_kind: CapturedItemKind::InlineSpecRequires,
                associated_subject_def_id: Some(subject_def_id.clone()),
                trait_impls: Vec::new(),
            });
        } else if let Some((def_id, lean_mod)) = parse_linked_item(trimmed, "- Inline ensures: `") {
            bundle.inline_ensures.push(UnitTargetRecord {
                target: CapturedTarget {
                    def_id,
                    mir_module_path: String::new(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: lean_mod,
                item_kind: CapturedItemKind::InlineSpecEnsures,
                associated_subject_def_id: Some(subject_def_id.clone()),
                trait_impls: Vec::new(),
            });
        } else if let Some((def_id, lean_mod)) = parse_linked_item(trimmed, "- External spec: `") {
            bundle.external_specs.push(UnitTargetRecord {
                target: CapturedTarget {
                    def_id,
                    mir_module_path: String::new(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: lean_mod,
                item_kind: CapturedItemKind::ExternalSpec,
                associated_subject_def_id: Some(subject_def_id.clone()),
                trait_impls: Vec::new(),
            });
        } else if trimmed == "def defaultCallees : List CapturedMir :="
            && let Some(list_line) = lines.get(idx + 1)
        {
            for suffix in extract_mir_body_suffixes(list_line) {
                bundle.transitive_callees.push(TransitiveCalleeRef {
                    def_id: suffix.clone(),
                    item_module_suffix: suffix,
                });
            }
        } else if trimmed == "def defaultSpecCallees : List CapturedMir :="
            && let Some(list_line) = lines.get(idx + 1)
        {
            for suffix in extract_mir_body_suffixes(list_line) {
                bundle.spec_callees.push(TransitiveCalleeRef {
                    def_id: suffix.clone(),
                    item_module_suffix: suffix,
                });
            }
        } else if trimmed == "externalSpecCallContract"
            && let Some(target_line) = lines.get(idx + 1)
            && let Some(sidecar_line) = lines.get(idx + 2)
        {
            let target_def_id = target_line.trim().trim_matches('"').to_string();
            let sidecar_trimmed = sidecar_line.trim();
            if let Some(sidecar_suffix) = sidecar_trimmed
                .strip_prefix("Mir.")
                .and_then(|s| s.strip_suffix(".body"))
            {
                let req_module_suffix = lines
                    .get(idx + 3)
                    .and_then(|l| extract_mir_body_suffixes(l).into_iter().next());
                let ens_module_suffix = lines
                    .get(idx + 4)
                    .and_then(|l| extract_mir_body_suffixes(l).into_iter().next());
                bundle.external_spec_callees.push(ExternalSpecContractRef {
                    target_def_id,
                    sidecar_module_suffix: sidecar_suffix.to_string(),
                    req_module_suffix,
                    ens_module_suffix,
                });
            }
        }
    }
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
    generated_assumptions_roots: &BTreeSet<String>,
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
            || trimmed.contains("name = \"GeneratedAssumptions\"")
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
    if !generated_assumptions_roots.is_empty() {
        insert_blocks.push(format!(
            "[[lean_lib]]\nname = \"GeneratedAssumptions\"\nsrcDir = \"generated\"\nroots = [{}]",
            format_roots(generated_assumptions_roots)
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
    let expected_sha = &record.target.mir_module_sha256;

    let matches_sha = |path: &Path| -> bool {
        if expected_sha.is_empty() {
            return true;
        }
        fs::read(path)
            .ok()
            .is_some_and(|bytes| &sha256_hex(&bytes) == expected_sha)
    };

    if let Some(ref units_dir) = config.units_dir
        && units_dir.is_dir()
    {
        let direct_recorded = units_dir.join(recorded_rel);
        if direct_recorded.is_file() && matches_sha(&direct_recorded) {
            return Some(direct_recorded);
        }
        let direct_mir = units_dir.join("Mir").join(rel_item_path);
        if direct_mir.is_file() && matches_sha(&direct_mir) {
            return Some(direct_mir);
        }
        if let Ok(entries) = fs::read_dir(units_dir) {
            let mut subdirs: Vec<PathBuf> = entries
                .filter_map(|e| e.ok().map(|d| d.path()))
                .filter(|p| p.is_dir())
                .collect();
            subdirs.sort();
            let mut fallback_match: Option<PathBuf> = None;
            for unit_subdir in subdirs {
                let candidate_recorded = unit_subdir.join(recorded_rel);
                if candidate_recorded.is_file() {
                    if matches_sha(&candidate_recorded) {
                        return Some(candidate_recorded);
                    }
                    if fallback_match.is_none() {
                        fallback_match = Some(candidate_recorded);
                    }
                }
                let candidate_mir = unit_subdir.join("Mir").join(rel_item_path);
                if candidate_mir.is_file() {
                    if matches_sha(&candidate_mir) {
                        return Some(candidate_mir);
                    }
                    if fallback_match.is_none() {
                        fallback_match = Some(candidate_mir);
                    }
                }
            }
            if let Some(found) = fallback_match {
                return Some(found);
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
    let mut generated_assumptions_roots = BTreeSet::new();
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
        } else if bundle.has_rust_trusted_attr() && !authored.has_proof {
            generated_assumptions_roots.insert(format!("Assumptions.{item}"));
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
        &generated_assumptions_roots,
        &proof_roots,
    )
}

fn infer_crate_name(
    workspace_root: &Path,
    units_dir: Option<&Path>,
    bundles: &[SubjectObligationBundle],
) -> String {
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
    if let Some(u_dir) = units_dir
        && let Some(from_units) = crate::driver::infer_crate_name_from_units_dir(u_dir)
    {
        return from_units;
    }
    let default_units = workspace_root.join("target").join("anneal").join("units");
    if let Some(from_default_units) =
        crate::driver::infer_crate_name_from_units_dir(&default_units)
    {
        return from_default_units;
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

    for env_key in ["ANNEAL_REPO_ROOT", "ANNEAL_ROOT"] {
        if let Ok(env_root) = std::env::var(env_key)
            && !env_root.trim().is_empty()
        {
            let abs_env_root =
                crate::normalize_path_against(&base_dir, Path::new(env_root.trim()));
            if abs_env_root.join("trusted/lean").is_dir() && abs_env_root.join("theory").is_dir() {
                let trusted = abs_env_root
                    .join("trusted/lean")
                    .to_string_lossy()
                    .into_owned();
                let theory = abs_env_root.join("theory").to_string_lossy().into_owned();
                return (trusted, theory);
            }
        }
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

    if let Some(repo_root) = crate::default_anneal_repo_root() {
        return (
            repo_root.join("trusted/lean").to_string_lossy().into_owned(),
            repo_root.join("theory").to_string_lossy().into_owned(),
        );
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
            trait_impls: Vec::new(),
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
        let init_proof_text =
            fs::read_to_string(&proof_path).expect("read initial proof template");
        assert!(
            init_proof_text.contains("theorem verified : VerificationResult Obligations.MyCrate.compute.claim"),
            "stateless spec template doc comments must not cause init-proofs to emit StatefulVerificationResult:\n{init_proof_text}"
        );

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
                trait_impls: Vec::new(),
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
            trait_impls: Vec::new(),
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
            trait_impls: Vec::new(),
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
            trait_impls: Vec::new(),
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

    #[test]
    fn detects_polymorphic_proofs_across_all_claim_surfaces() {
        let workspace = unique_temp_dir("poly-detect");
        let proofs_root = workspace.join("anneal/proofs");
        let rel_path = Path::new("MyCrate/poly_fn.lean");
        let proof_path = proofs_root.join("Proof").join(rel_path);
        fs::create_dir_all(proof_path.parent().expect("proof parent")).expect("create proof dir");

        let cases = [
            ("polyClaim", false, false, false, false),
            ("polyStatefulClaim", true, false, false, false),
            ("polyTotalClaim", false, true, false, false),
            ("polyModularClaim", false, false, true, false),
            ("polyUbExceptionClaim", false, false, false, true),
        ];

        for (claim_tok, exp_stateful, exp_total, exp_modular, exp_ub) in cases {
            fs::write(
                &proof_path,
                format!("theorem verified : Obligations.MyCrate.poly_fn.{claim_tok} := sorry\n"),
            )
            .expect("write poly proof");
            let detected = detect_authored_item_modules(&proofs_root, rel_path);
            assert!(detected.has_proof);
            assert!(detected.is_polymorphic, "expected is_polymorphic for {claim_tok}");
            assert_eq!(detected.is_stateful, exp_stateful, "stateful mismatch for {claim_tok}");
            assert_eq!(detected.is_total, exp_total, "total mismatch for {claim_tok}");
            assert_eq!(detected.is_modular, exp_modular, "modular mismatch for {claim_tok}");
            assert_eq!(
                detected.is_ub_exception, exp_ub,
                "ub_exception mismatch for {claim_tok}"
            );
        }

        let _ = fs::remove_dir_all(&workspace);
    }

    #[test]
    fn transitive_callees_closure_is_cycle_safe_and_excludes_external_spec_overrides() {
        let workspace = unique_temp_dir("transitive-callees");
        let unit_dir = workspace.join("target/anneal/units/my_crate-01");
        fs::create_dir_all(unit_dir.join("Mir/MyCrate")).expect("create Mir/MyCrate");
        fs::create_dir_all(unit_dir.join("Mir/DepCrate")).expect("create Mir/DepCrate");
        fs::create_dir_all(unit_dir.join("Mir/Core")).expect("create Mir/Core");

        // `my_crate::entry` calls:
        // - `my_crate::local_step` (which calls `dep_crate::mutual_a` and trait method `core::ops::RangeBounds::contains`)
        // - `dep_crate::overridden_fn` (which has an explicit `#[external_spec]` override, so it and its private callee `dep_crate::behind_override` must be excluded from `defaultCallees`!)
        // Meanwhile `dep_crate::mutual_a` <-> `dep_crate::mutual_b` form a cycle, and `core::ops::RangeBounds::contains` resolves via `trait_impls` to `core::ops::range::<impl RangeBounds<T>>::contains`.
        let write_mir = |rel: &str, body_refs: &[&str]| {
            let mut txt = String::from("prelude\nimport Init.Core\nimport Trusted\n");
            for r in body_refs {
                txt.push_str(&format!("-- call .fnDef \"{r}\" []\n"));
            }
            fs::write(unit_dir.join(rel), txt).expect("write mir file");
        };

        write_mir(
            "Mir/MyCrate/entry.lean",
            &["my_crate::local_step", "dep_crate::overridden_fn"],
        );
        write_mir(
            "Mir/MyCrate/local_step.lean",
            &["dep_crate::mutual_a", "core::ops::RangeBounds::contains"],
        );
        write_mir(
            "Mir/DepCrate/mutual_a.lean",
            &["dep_crate::mutual_b", "dep_crate::mutual_a"],
        );
        write_mir("Mir/DepCrate/mutual_b.lean", &["dep_crate::mutual_a"]);
        write_mir(
            "Mir/DepCrate/overridden_fn.lean",
            &["dep_crate::behind_override"],
        );
        write_mir("Mir/DepCrate/behind_override.lean", &[]);
        write_mir("Mir/Core/range_contains.lean", &[]);
        write_mir("Mir/MyCrate/spec_overridden_fn.lean", &[]);

        let records = vec![
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "my_crate::entry".to_string(),
                    mir_module_path: "Mir/MyCrate/entry.lean".to_string(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: "Mir.MyCrate.entry".to_string(),
                item_kind: CapturedItemKind::Subject,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            },
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "my_crate::local_step".to_string(),
                    mir_module_path: "Mir/MyCrate/local_step.lean".to_string(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: "Mir.MyCrate.local_step".to_string(),
                item_kind: CapturedItemKind::Subject,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            },
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "dep_crate::mutual_a".to_string(),
                    mir_module_path: "Mir/DepCrate/mutual_a.lean".to_string(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: "Mir.DepCrate.mutual_a".to_string(),
                item_kind: CapturedItemKind::Callee,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            },
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "dep_crate::mutual_b".to_string(),
                    mir_module_path: "Mir/DepCrate/mutual_b.lean".to_string(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: "Mir.DepCrate.mutual_b".to_string(),
                item_kind: CapturedItemKind::Callee,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            },
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "dep_crate::overridden_fn".to_string(),
                    mir_module_path: "Mir/DepCrate/overridden_fn.lean".to_string(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: "Mir.DepCrate.overridden_fn".to_string(),
                item_kind: CapturedItemKind::Callee,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            },
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "dep_crate::behind_override".to_string(),
                    mir_module_path: "Mir/DepCrate/behind_override.lean".to_string(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: "Mir.DepCrate.behind_override".to_string(),
                item_kind: CapturedItemKind::Callee,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            },
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "core::ops::range::<impl RangeBounds<T>>::contains".to_string(),
                    mir_module_path: "Mir/Core/range_contains.lean".to_string(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: "Mir.Core.range_contains".to_string(),
                item_kind: CapturedItemKind::Callee,
                associated_subject_def_id: None,
                trait_impls: vec![anneal_rustc_capture::manifest::ManifestTraitImplEntry {
                    trait_method_def_path: "core::ops::RangeBounds::contains".to_string(),
                    trait_args_lean: Vec::new(),
                    impl_path: "core::ops::range::<impl RangeBounds<T>>::contains".to_string(),
                }],
            },
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "my_crate::spec_overridden_fn".to_string(),
                    mir_module_path: "Mir/MyCrate/spec_overridden_fn.lean".to_string(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: "Mir.MyCrate.spec_overridden_fn".to_string(),
                item_kind: CapturedItemKind::ExternalSpec,
                associated_subject_def_id: Some("dep_crate::overridden_fn".to_string()),
                trait_impls: Vec::new(),
            },
        ];

        scaffold_workspace(&workspace, &records).expect("scaffold workspace with transitive callees");

        let entry_obligations = fs::read_to_string(
            workspace.join(".anneal/generated/Obligations/MyCrate/entry.lean"),
        )
        .expect("read entry obligations");

        assert!(
            entry_obligations.contains(
                "def defaultCallees : List CapturedMir :=\n  \
                   [Mir.MyCrate.local_step.body, Mir.DepCrate.mutual_a.body, Mir.Core.range_contains.body, Mir.DepCrate.mutual_b.body]"
            ),
            "unexpected defaultCallees in entry.lean:\n{entry_obligations}"
        );
        assert!(
            !entry_obligations.contains("Mir.DepCrate.overridden_fn.body"),
            "overridden_fn must be excluded from defaultCallees:\n{entry_obligations}"
        );
        assert!(
            !entry_obligations.contains("Mir.DepCrate.behind_override.body"),
            "callees only reachable behind an overridden target must be excluded:\n{entry_obligations}"
        );
        assert!(
            entry_obligations.contains("def externalCallContract_MyCrate_spec_overridden_fn : MirCallContract :="),
            "entry obligations must include externalCallContract for overridden_fn:\n{entry_obligations}"
        );

        let _ = fs::remove_dir_all(&workspace);
    }

    #[test]
    fn spec_companion_callees_are_linked_without_widening_the_modular_environment() {
        let workspace = unique_temp_dir("spec-companion-callees");
        let unit_dir = workspace.join("target/anneal/units/my_crate-01");
        fs::create_dir_all(unit_dir.join("Mir/MyCrate")).expect("create Mir/MyCrate");
        fs::create_dir_all(unit_dir.join("Mir/Core")).expect("create Mir/Core");
        fs::create_dir_all(unit_dir.join("Mir/DepCrate")).expect("create Mir/DepCrate");

        let write_mir = |rel: &str, body_refs: &[&str]| {
            let mut txt = String::from("prelude\nimport Init.Core\nimport Trusted\n");
            for r in body_refs {
                txt.push_str(&format!("-- call .fnDef \"{r}\" []\n"));
            }
            fs::write(unit_dir.join(rel), txt).expect("write mir file");
        };
        // The subject body is call-free; its `ensures` companion calls a `core`
        // helper and an `#[external_spec]`-overridden dependency function, and
        // its `requires` companion is call-free.
        write_mir("Mir/MyCrate/entry.lean", &[]);
        write_mir("Mir/MyCrate/__anodized_fn_requires_entry.lean", &[]);
        write_mir(
            "Mir/MyCrate/__anodized_fn_ensures_entry.lean",
            &["core::num::wrapping_add", "dep_crate::overridden_fn"],
        );
        write_mir("Mir/Core/wrapping_add.lean", &[]);
        write_mir("Mir/DepCrate/overridden_fn.lean", &[]);
        write_mir("Mir/MyCrate/spec_overridden_fn.lean", &[]);

        let rec = |def_id: &str, rel: &str, module: &str, kind, assoc: Option<&str>| {
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: def_id.to_string(),
                    mir_module_path: rel.to_string(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: module.to_string(),
                item_kind: kind,
                associated_subject_def_id: assoc.map(str::to_string),
                trait_impls: Vec::new(),
            }
        };
        let records = vec![
            rec(
                "my_crate::entry",
                "Mir/MyCrate/entry.lean",
                "Mir.MyCrate.entry",
                CapturedItemKind::Subject,
                None,
            ),
            rec(
                "my_crate::__anodized_fn_requires_entry",
                "Mir/MyCrate/__anodized_fn_requires_entry.lean",
                "Mir.MyCrate.__anodized_fn_requires_entry",
                CapturedItemKind::InlineSpecRequires,
                Some("my_crate::entry"),
            ),
            rec(
                "my_crate::__anodized_fn_ensures_entry",
                "Mir/MyCrate/__anodized_fn_ensures_entry.lean",
                "Mir.MyCrate.__anodized_fn_ensures_entry",
                CapturedItemKind::InlineSpecEnsures,
                Some("my_crate::entry"),
            ),
            rec(
                "core::num::wrapping_add",
                "Mir/Core/wrapping_add.lean",
                "Mir.Core.wrapping_add",
                CapturedItemKind::Callee,
                None,
            ),
            rec(
                "dep_crate::overridden_fn",
                "Mir/DepCrate/overridden_fn.lean",
                "Mir.DepCrate.overridden_fn",
                CapturedItemKind::Callee,
                None,
            ),
            rec(
                "my_crate::spec_overridden_fn",
                "Mir/MyCrate/spec_overridden_fn.lean",
                "Mir.MyCrate.spec_overridden_fn",
                CapturedItemKind::ExternalSpec,
                Some("dep_crate::overridden_fn"),
            ),
        ];

        scaffold_workspace(&workspace, &records).expect("scaffold workspace with spec companions");
        let obligations =
            fs::read_to_string(workspace.join(".anneal/generated/Obligations/MyCrate/entry.lean"))
                .expect("read entry obligations");

        assert!(
            obligations.contains("def defaultSpecCallees : List CapturedMir :=\n  [Mir.Core.wrapping_add.body]"),
            "the ensures companion's callee must be linked for predicate evaluation:\n{obligations}"
        );
        assert!(
            obligations.contains(
                "MirBoolPredicateHoldsWithCallees Mir.MyCrate.__anodized_fn_ensures_entry.body defaultSpecCallees"
            ),
            "call-containing ensures companion must link defaultSpecCallees:\n{obligations}"
        );
        assert!(
            obligations.contains("MirBoolPredicateHolds Mir.MyCrate.__anodized_fn_requires_entry.body args"),
            "call-free requires companion keeps the plain form:\n{obligations}"
        );
        assert!(
            obligations.contains("def defaultCallees : List CapturedMir :=\n  .nil"),
            "predicate-only callees must not be linked into the subject's own callee table:\n{obligations}"
        );
        assert!(
            !obligations.contains("Mir.DepCrate.overridden_fn.body"),
            "the overridden target stays excluded from every callee table:\n{obligations}"
        );
        assert!(
            obligations.contains("envAssumed := fun _ => True"),
            "a target reached only from a predicate is not assumed in the modular environment:\n{obligations}"
        );

        let _ = fs::remove_dir_all(&workspace);
    }

    #[test]
    fn transitive_trusted_sibling_callee_is_abstracted_in_modular_environment() {
        let workspace = unique_temp_dir("transitive-trusted-callee");
        let unit_dir = workspace.join("target/anneal/units/my_crate-01");
        fs::create_dir_all(unit_dir.join("Mir/MyCrate")).expect("create Mir/MyCrate");

        let write_mir = |rel: &str, body_refs: &[&str]| {
            let mut txt = String::from("prelude\nimport Init.Core\nimport Trusted\n");
            for r in body_refs {
                txt.push_str(&format!("-- call .fnDef \"{r}\" []\n"));
            }
            fs::write(unit_dir.join(rel), txt).expect("write mir file");
        };
        // `caller` calls `linked_mid`, which in turn calls `#[spec(trusted)]`
        // sibling `trusted_leaf`.
        write_mir("Mir/MyCrate/caller.lean", &["my_crate::linked_mid"]);
        write_mir("Mir/MyCrate/linked_mid.lean", &["my_crate::trusted_leaf"]);
        write_mir("Mir/MyCrate/trusted_leaf.lean", &[]);
        write_mir("Mir/MyCrate/__anneal_attr_trusted_trusted_leaf.lean", &[]);
        write_mir("Mir/MyCrate/__anodized_fn_ensures_trusted_leaf.lean", &[]);

        let rec = |def_id: &str, rel: &str, module: &str, kind, assoc: Option<&str>| {
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: def_id.to_string(),
                    mir_module_path: rel.to_string(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: module.to_string(),
                item_kind: kind,
                associated_subject_def_id: assoc.map(str::to_string),
                trait_impls: Vec::new(),
            }
        };
        let records = vec![
            rec(
                "my_crate::caller",
                "Mir/MyCrate/caller.lean",
                "Mir.MyCrate.caller",
                CapturedItemKind::Subject,
                None,
            ),
            rec(
                "my_crate::linked_mid",
                "Mir/MyCrate/linked_mid.lean",
                "Mir.MyCrate.linked_mid",
                CapturedItemKind::Subject,
                None,
            ),
            rec(
                "my_crate::trusted_leaf",
                "Mir/MyCrate/trusted_leaf.lean",
                "Mir.MyCrate.trusted_leaf",
                CapturedItemKind::Subject,
                None,
            ),
            rec(
                "my_crate::__ANNEAL_EXT_SPEC_TARGET___anneal_attr_trusted_trusted_leaf",
                "Mir/MyCrate/__anneal_attr_trusted_trusted_leaf.lean",
                "Mir.MyCrate.__anneal_attr_trusted_trusted_leaf",
                CapturedItemKind::ExternalSpec,
                Some("my_crate::trusted_leaf"),
            ),
            rec(
                "my_crate::__anodized_fn_ensures_trusted_leaf",
                "Mir/MyCrate/__anodized_fn_ensures_trusted_leaf.lean",
                "Mir.MyCrate.__anodized_fn_ensures_trusted_leaf",
                CapturedItemKind::InlineSpecEnsures,
                Some("my_crate::trusted_leaf"),
            ),
        ];

        scaffold_workspace(&workspace, &records)
            .expect("scaffold workspace with transitive trusted callee");
        let caller_ob =
            fs::read_to_string(workspace.join(".anneal/generated/Obligations/MyCrate/caller.lean"))
                .expect("read caller obligations");
        assert!(
            caller_ob.contains("def defaultCallees : List CapturedMir :=\n  [Mir.MyCrate.linked_mid.body]"),
            "caller must link linked_mid and exclude trusted_leaf from defaultCallees:\n{caller_ob}"
        );
        assert!(
            caller_ob.contains("envAssumed := Obligations.MyCrate.trusted_leaf.defaultCallContract.holdsOn"),
            "caller must assume transitive trusted_leaf's defaultCallContract in envAssumed:\n{caller_ob}"
        );
        let initial_caller_verify =
            fs::read_to_string(workspace.join(".anneal/generated/Verify/MyCrate/caller.lean"))
                .expect("read initial caller verify");
        assert!(
            initial_caller_verify.contains("import Mir.MyCrate.linked_mid\n")
                && initial_caller_verify.contains("import Mir.MyCrate.trusted_leaf\n")
                && initial_caller_verify
                    .contains("import Mir.MyCrate.__anodized_fn_ensures_trusted_leaf\n")
                && initial_caller_verify.contains("instance (priority := low) defaultModularProof"),
            "initial Verify/MyCrate/caller.lean must import linked/trusted callees and emit defaultModularProof:\n{initial_caller_verify}"
        );

        // Author and then delete a temporary Proof/MyCrate/caller.lean, then
        // verify `refresh_workspace_assembly` rehydrates `transitive_callees`
        // and `called_callees` from `Obligations/MyCrate/caller.lean`.
        let caller_proof_path = workspace.join("anneal/proofs/Proof/MyCrate/caller.lean");
        fs::create_dir_all(caller_proof_path.parent().expect("proof parent"))
            .expect("create Proof/MyCrate");
        fs::write(
            &caller_proof_path,
            "theorem verified : ModularVerificationResult Obligations.MyCrate.caller.modularClaim := sorry\n",
        )
        .expect("write temporary caller proof");
        refresh_workspace_assembly(&workspace).expect("refresh with caller proof");
        fs::remove_file(&caller_proof_path).expect("delete temporary caller proof");
        refresh_workspace_assembly(&workspace).expect("refresh after deleting caller proof");

        let refreshed_caller_verify =
            fs::read_to_string(workspace.join(".anneal/generated/Verify/MyCrate/caller.lean"))
                .expect("read refreshed caller verify");
        assert_eq!(
            refreshed_caller_verify, initial_caller_verify,
            "refresh_workspace_assembly must preserve transitive_callees, called_callees, and defaultModularProof"
        );

        let _ = fs::remove_dir_all(&workspace);
    }
}
