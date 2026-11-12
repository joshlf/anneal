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

fn has_lean_ident_token(src: &str, ident: &str) -> bool {
    let mut offset = 0usize;
    while let Some(rel) = src[offset..].find(ident) {
        let pos = offset + rel;
        let prev_ok = !src[..pos]
            .chars()
            .next_back()
            .is_some_and(crate::agent::is_lean_ident_char);
        let after_pos = pos + ident.len();
        let next_ok = !src[after_pos..]
            .chars()
            .next()
            .is_some_and(crate::agent::is_lean_ident_char);
        if prev_ok && next_ok {
            return true;
        }
        offset = pos + 1;
    }
    false
}

fn has_any_lean_ident_token(src: &str, idents: &[&str]) -> bool {
    idents.iter().any(|id| has_lean_ident_token(src, id))
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
            .map(|raw| strip_lean_comments_and_strings(&raw))
    } else {
        None
    };
    let has_legacy_specs_defs = spec_text.as_deref().is_some_and(|text| {
        !has_any_lean_ident_token(
            text,
            &[
                "ItemSpec",
                "StatefulItemSpec",
                "TotalItemSpec",
                "StatefulEquivItemSpec",
                "ModularItemSpec",
                "UbExceptionItemSpec",
            ],
        ) && !text.contains("import Obligations.")
    });

    let has_proof = proof_path.is_file();
    let proof_text = if has_proof {
        fs::read_to_string(&proof_path)
            .ok()
            .map(|raw| strip_lean_comments_and_strings(&raw))
    } else {
        None
    };

    let spec_is_ub_exception = spec_text.as_deref().is_some_and(|text| {
        has_any_lean_ident_token(text, &["UbExceptionItemSpec", "refineUbExceptionSpec"])
    });
    let spec_is_modular = spec_text.as_deref().is_some_and(|text| {
        has_any_lean_ident_token(text, &["ModularItemSpec", "refineModularSpec"])
    });

    let is_ub_exception = !spec_is_modular
        && (spec_is_ub_exception
            || proof_text.as_deref().is_some_and(|text| {
                has_any_lean_ident_token(
                    text,
                    &["UbExceptionVerificationResult", "UbExceptionItemProof"],
                ) || (has_any_lean_ident_token(text, &["ubExceptionClaim", "polyUbExceptionClaim"])
                    && !has_lean_ident_token(text, "ModularVerificationResult"))
            }));

    let is_modular = !is_ub_exception
        && (spec_is_modular
            || proof_text.as_deref().is_some_and(|text| {
                has_any_lean_ident_token(
                    text,
                    &[
                        "modularClaim",
                        "polyModularClaim",
                        "ModularVerificationResult",
                        "ModularItemProof",
                    ],
                )
            }));

    let is_equiv = !is_ub_exception
        && !is_modular
        && (spec_text.as_deref().is_some_and(|text| {
            has_any_lean_ident_token(text, &["StatefulEquivItemSpec", "refineEquivSpec"])
        }) || proof_text.as_deref().is_some_and(|text| {
            has_any_lean_ident_token(
                text,
                &[
                    "equivClaim",
                    "StatefulEquivVerificationResult",
                    "StatefulEquivItemProof",
                ],
            )
        }));

    let is_total = !is_ub_exception
        && !is_modular
        && !is_equiv
        && (spec_text.as_deref().is_some_and(|text| {
            has_any_lean_ident_token(text, &["TotalItemSpec", "refineTotalSpec"])
        }) || proof_text.as_deref().is_some_and(|text| {
            has_any_lean_ident_token(
                text,
                &[
                    "totalClaim",
                    "polyTotalClaim",
                    "TotalVerificationResult",
                    "TotalItemProof",
                ],
            )
        }));

    let spec_is_stateful = spec_text.as_deref().is_some_and(|text| {
        has_any_lean_ident_token(
            text,
            &[
                "StatefulItemSpec",
                "refineStatefulSpec",
                "refineSafeStatefulSpec",
            ],
        )
    });
    let proof_is_stateful = proof_text.as_deref().is_some_and(|text| {
        has_any_lean_ident_token(
            text,
            &[
                "statefulClaim",
                "polyStatefulClaim",
                "StatefulVerificationResult",
                "StatefulItemProof",
            ],
        )
    });
    let is_polymorphic = proof_text.as_deref().is_some_and(|text| {
        has_any_lean_ident_token(
            text,
            &[
                "polyClaim",
                "polyStatefulClaim",
                "polyTotalClaim",
                "polyModularClaim",
                "polyUbExceptionClaim",
            ],
        )
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
    for marker in [".fnDef \"", "RigidTy.fnDef \"", "implPath := \""] {
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

fn is_builtin_unreachable_call_target(def_id: &str) -> bool {
    matches!(
        def_id,
        "core::hint::unreachable_unchecked"
            | "std::hint::unreachable_unchecked"
            | "core::intrinsics::unreachable"
    )
}

/// Populate `bundle.transitive_callees`, `bundle.external_spec_callees`,
/// `bundle.called_callees`, `bundle.spec_callees`, and
/// `bundle.spec_companions_with_calls` for each subject bundle by computing the
/// cycle-safe transitive closure of reachable `.fnDef "<callee_def_id>"` and
/// trait-impl references across all captured MIR bodies (`Subject`,
/// `UnsafeTraitImpl`, `Callee`, `Model`, `TypeInvariant`), excluding built-in
/// unreachable intrinsics (`Terminators.isUnreachableCallTarget`), any target
/// with an explicit `#[external_spec(for = <target>)]` override,
/// `#[spec(trusted)]` attribute, or authored `UbExceptionItemSpec` contract.
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
    let proofs_root = mir_root
        .parent()
        .and_then(|g| g.parent())
        .and_then(|d| d.parent())
        .map(|ws| ws.join("anneal").join("proofs"));
    let ub_exception_subject_def_ids: BTreeSet<String> = match proofs_root.as_deref() {
        Some(pr) if pr.is_dir() => bundles
            .iter()
            .filter(|b| detect_authored_item_modules(pr, &b.item_rel_path).is_ub_exception)
            .map(|b| b.subject.target.def_id.clone())
            .collect(),
        _ => BTreeSet::new(),
    };

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
        if is_builtin_unreachable_call_target(&record.target.def_id)
            || external_spec_contracts.contains_key(&record.target.def_id)
            || trusted_subject_def_ids.contains(&record.target.def_id)
            || ub_exception_subject_def_ids.contains(&record.target.def_id)
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

    let mut outgoing_cache: BTreeMap<PathBuf, Vec<String>> = BTreeMap::new();
    let mut read_outgoing = |rel_path: &Path| -> Vec<String> {
        if let Some(cached) = outgoing_cache.get(rel_path) {
            return cached.clone();
        }
        let resolved_path = if let Some(rec) = record_by_rel_path.get(rel_path) {
            resolve_workspace_mir_file(mir_root, rec, rel_path)
        } else {
            let mir_path = mir_root.join(rel_path);
            mir_path.is_file().then_some(mir_path)
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

        let mut authored = effective_authored_for_bundle(
            bundle,
            detect_authored_item_modules(&proofs_root, &bundle.item_rel_path),
            None,
        );

        let proof_path = proof_root.join(&bundle.item_rel_path);
        if proof_path.exists() {
            report.preserved_proof_files.push(proof_path);
        } else if config.init_proof_templates {
            if let Some(parent) = proof_path.parent() {
                fs::create_dir_all(parent).map_err(|err| {
                    format!("failed to create directory {}: {}", parent.display(), err)
                })?;
            }
            let lifting_profile = analyze_workspace_lifting_profile(&mir_root, bundle);
            let proof_contents =
                render_proof_template_with_hints(bundle, authored, &lifting_profile);
            fs::write(&proof_path, proof_contents).map_err(|err| {
                format!(
                    "failed to write proof template {}: {}",
                    proof_path.display(),
                    err
                )
            })?;
            report.created_proof_files.push(proof_path);
            authored = effective_authored_for_bundle(
                bundle,
                detect_authored_item_modules(&proofs_root, &bundle.item_rel_path),
                None,
            );
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
            && !authored.has_proof
            && !authored.has_specs
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
        authored = effective_authored_for_bundle(&synthetic_bundle, authored, None);

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

/// 5-element total bounded lattice of Rust `Runtime(PostCleanup)` MIR
/// sub-grammars, aligned 1-to-1 with `Anneal.PureMirExec.MirFragment`
/// (`theory/Anneal/PureMirExec.lean`, Section 11).
///
/// `MirFragment::default()` is the fail-closed top element `FullMir` (matching
/// Lean's `instance : Inhabited MirFragment := ⟨.fullMir⟩`), so an unanalyzed
/// `MirLiftingProfile::default()` never claims a restrictive fragment.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MirFragment {
    /// Loop-free alias-free pure MIR (`#mir_lift` / `PureMirExec` + DAG CFG).
    PureLoopFree,
    /// Alias-free pure MIR with control-flow loops (`PureMirExec` + `MirLoops`).
    PureBoundedLoop,
    /// Intraprocedural Tree Borrows local reference/pointer/retag MIR (`SepLogicLenses`).
    TreeBorrowsLocal,
    /// Intraprocedural MIR with `copy_nonoverlapping` and global memory constants.
    IntrinsicCopy,
    /// Full `Runtime(PostCleanup)` MIR including calls, provenance-exposing
    /// casts, and inline assembly.
    #[default]
    FullMir,
}

impl MirFragment {
    /// Exhaustive list of all 5 `MirFragment` levels in strictly ascending order.
    pub const ALL: [MirFragment; 5] = [
        MirFragment::PureLoopFree,
        MirFragment::PureBoundedLoop,
        MirFragment::TreeBorrowsLocal,
        MirFragment::IntrinsicCopy,
        MirFragment::FullMir,
    ];

    /// Numeric lattice rank in `0..=4`, matching `MirFragment.toRank` in Lean.
    pub const fn to_rank(self) -> u8 {
        match self {
            Self::PureLoopFree => 0,
            Self::PureBoundedLoop => 1,
            Self::TreeBorrowsLocal => 2,
            Self::IntrinsicCopy => 3,
            Self::FullMir => 4,
        }
    }

    /// Canonical snake_case identifier matching `MirFragment.asStr` in Lean and
    /// `.anneal/spec-lock.json` (`mir_fragment`).
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::PureLoopFree => "pure_loop_free",
            Self::PureBoundedLoop => "pure_bounded_loop",
            Self::TreeBorrowsLocal => "tree_borrows_local",
            Self::IntrinsicCopy => "intrinsic_copy",
            Self::FullMir => "full_mir",
        }
    }

    /// Canonical qualified Lean constructor name matching `MirFragment.leanCtor`.
    pub const fn lean_ctor(&self) -> &'static str {
        match self {
            Self::PureLoopFree => "MirFragment.pureLoopFree",
            Self::PureBoundedLoop => "MirFragment.pureBoundedLoop",
            Self::TreeBorrowsLocal => "MirFragment.treeBorrowsLocal",
            Self::IntrinsicCopy => "MirFragment.intrinsicCopy",
            Self::FullMir => "MirFragment.fullMir",
        }
    }

    /// Least upper bound (`self ⊔ other`) in the 5-element `MirFragment` lattice.
    pub fn join(self, other: Self) -> Self {
        std::cmp::max(self, other)
    }

    /// Greatest lower bound (`self ⊓ other`) in the 5-element `MirFragment` lattice.
    pub fn meet(self, other: Self) -> Self {
        std::cmp::min(self, other)
    }
}

impl std::fmt::Display for MirFragment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl std::str::FromStr for MirFragment {
    type Err = String;

    /// Parses exactly the identifiers accepted by Lean `MirFragment.fromStr?`
    /// (no whitespace trimming).
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "pure_loop_free" | "MirFragment.pureLoopFree" | "pureLoopFree" => {
                Ok(Self::PureLoopFree)
            }
            "pure_bounded_loop" | "MirFragment.pureBoundedLoop" | "pureBoundedLoop" => {
                Ok(Self::PureBoundedLoop)
            }
            "tree_borrows_local" | "MirFragment.treeBorrowsLocal" | "treeBorrowsLocal" => {
                Ok(Self::TreeBorrowsLocal)
            }
            "intrinsic_copy" | "MirFragment.intrinsicCopy" | "intrinsicCopy" => {
                Ok(Self::IntrinsicCopy)
            }
            "full_mir" | "MirFragment.fullMir" | "fullMir" => Ok(Self::FullMir),
            other => Err(format!("unknown MirFragment identifier: `{other}`")),
        }
    }
}

/// Result of classifying a `CapturedMir` body into the 5-element `MirFragment`
/// lattice, paired with the ordered construct escalation reasons above
/// `MirFragment::PureLoopFree`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MirFragmentClassification {
    /// Minimum `MirFragment` in the 5-element lattice admitting the body.
    pub inferred_fragment: MirFragment,
    /// Ordered, deduplicated MIR construct reasons that escalated the body
    /// above `MirFragment::PureLoopFree`.
    pub escalation_reasons: Vec<String>,
}

impl MirFragmentClassification {
    /// Returns `true` when `inferred_fragment <= MirFragment::PureBoundedLoop`,
    /// i.e. `Anneal.PureMirExec.inferMinFragment body ≤ .pureBoundedLoop`
    /// (`inferMinFragment_le_pureBoundedLoop_iff_pureStatement`: every
    /// statement satisfies `isPureStatement` and every terminator
    /// `isPureTerminator`).
    ///
    /// This is the syntactic `basicBlocks`-only layer and therefore a
    /// *necessary* condition for `Anneal.PureMirExec.checkPureMir body = true`:
    /// `checkPureMir` coincides with the borrow-free layer
    /// (`checkBorrowFreeBodyFragment .pureBoundedLoop`, i.e.
    /// `inferBorrowFreeMinFragment body ≤ .pureBoundedLoop`), which additionally
    /// requires `hasNoPtrRelationalAssign body` over `(localDecls, layouts)`
    /// (see `witnessPtrRelAssign` / `witnessUntypedRelAssign`).
    pub fn is_pure_mir(&self) -> bool {
        self.inferred_fragment <= MirFragment::PureBoundedLoop
    }

    /// Returns `true` when `inferred_fragment == MirFragment::PureLoopFree`.
    pub fn is_loop_free_pure_mir(&self) -> bool {
        self.inferred_fragment == MirFragment::PureLoopFree
    }
}

/// Classify a captured `Mir/<Item>.lean` source string into the 5-element
/// `MirFragment` lattice with exact construct-by-construct parity with the
/// syntactic `Anneal.PureMirExec.inferMinFragment` (which, like this
/// classifier, inspects only `body.basicBlocks`).
///
/// `Anneal.PureMirExec.inferBorrowFreeMinFragment` additionally escalates
/// relational `BinOp` assignments over pointer-typed or untyped operands in
/// `localDecls` (`hasNoPtrRelationalAssign`) to `.treeBorrowsLocal`; that
/// borrow-free layer is intentionally *not* mirrored here, so
/// `classify_mir_fragment(src).inferred_fragment` is always a lower bound of
/// (`≤`) `inferBorrowFreeMinFragment` on the same body.
///
/// If `mir_src` does not contain an inline `basicBlocks :=` definition (e.g. a
/// stub or external alias), classification fails closed to `MirFragment::FullMir`.
pub fn classify_mir_fragment(mir_src: &str) -> MirFragmentClassification {
    let scan = scan_captured_mir_body(mir_src);
    if !scan.has_body {
        return MirFragmentClassification {
            inferred_fragment: MirFragment::FullMir,
            escalation_reasons: vec![
                "non-inline or unparsed CapturedMir body (missing basicBlocks)".to_string(),
            ],
        };
    }
    MirFragmentClassification {
        inferred_fragment: scan.inferred_fragment,
        escalation_reasons: scan.escalation_reasons,
    }
}

/// `(inferred_fragment, has_cfg_back_edge, has_unscannable_syntax)` of an
/// inline `CapturedMir` body in `mir_src` (`None` without one), for
/// crate-internal Lean <-> Rust parity harnesses over real captured MIR
/// (`Anneal.PureMirExec.inferMinFragment` / `hasCfgBackedge`).
#[cfg(test)]
pub(crate) fn mir_fragment_parity_facts(mir_src: &str) -> Option<(MirFragment, bool, bool)> {
    let scan = scan_captured_mir_body(mir_src);
    scan.has_body.then_some((
        scan.inferred_fragment,
        scan.has_cfg_back_edge,
        scan.has_unscannable_syntax,
    ))
}

/// Render a human-readable multi-line boundary-crossing diagnostic when
/// `classification.inferred_fragment > MirFragment::PureBoundedLoop`.
///
/// Returns `None` when `classification.inferred_fragment <= MirFragment::PureBoundedLoop`
/// (`pure_loop_free` or `pure_bounded_loop`).
pub fn render_mir_fragment_diagnostic(
    def_id: &str,
    classification: &MirFragmentClassification,
) -> Option<String> {
    if classification.inferred_fragment <= MirFragment::PureBoundedLoop {
        return None;
    }

    let boundary_constructs: Vec<&str> = classification
        .escalation_reasons
        .iter()
        .map(String::as_str)
        .filter(|r| *r != "CFG back-edge")
        .collect();
    let constructs_summary = if boundary_constructs.is_empty() {
        "none recorded".to_string()
    } else {
        boundary_constructs.join(", ")
    };

    let strategy = match classification.inferred_fragment {
        MirFragment::PureLoopFree | MirFragment::PureBoundedLoop => unreachable!(),
        MirFragment::TreeBorrowsLocal => {
            "use `Anneal.SepLogicLenses` (`SepLensStateInv` / `ActiveTypedMutBorrow` + \
             `LiftLensBlock` + `verifyStatefulMir_of_sepLenses` or \
             `verifyStatefulMir_of_sepSubplaceLenses`) for `&mut` borrows, or step \
             read-only pointer/reference dereferences via `runCfgToBlock` \
             (`mirWpConverges_of_runCfgToBlock`, `verifyStatefulMirNoPanic_of_wpConverges`)."
        }
        MirFragment::IntrinsicCopy => {
            "use `Anneal.MirFuelFree` / `evalCopyNonOverlappingPermOk` with a stateful \
             memory frame (`StatefulItemSpec` + `verifyStatefulMirNoPanic_of_wpConverges` \
             and `mirWpConverges_of_runCfgToBlock`) to discharge non-overlapping bulk \
             memory copies and global constant allocations."
        }
        MirFragment::FullMir => {
            "use modular callee contracts (`PureMirModularConverges` + \
             `verifyModularMir_of_pureModularExec_any` or `#[external_spec]`), linked \
             callee tables (`checkPureMirWithCallees`), step provenance-exposing casts \
             (`CastKind.pointerExposeProvenance` / `CastKind.pointerWithExposedProvenance`) \
             statefully over concrete memory (`mirWpConverges_of_runCfgToBlock`), or mark \
             FFI / inline-assembly boundaries with `#[spec(trusted)]` / Miri differential \
             testing."
        }
    };

    let unscannable_note = if classification
        .escalation_reasons
        .iter()
        .any(|r| r.starts_with("unscannable") || r.starts_with("non-inline"))
    {
        "\n - Note: the body uses non-inline MIR syntax and was classified fail-closed; \
         regenerate `Mir/<Item>.lean` with `cargo anneal` (or inline the referenced \
         definitions) to obtain a precise fragment."
    } else {
        ""
    };

    Some(format!(
        "MIR fragment boundary crossed for `{def_id}`:\n\
         - Inferred fragment: `{frag}` (`{lean_ctor}`, rank {rank})\n\
         - Constructs exceeding `pure_bounded_loop` (`checkPureMir`): {constructs_summary}\n\
         - Recommended verification strategy: {strategy}{unscannable_note}",
        frag = classification.inferred_fragment.as_str(),
        lean_ctor = classification.inferred_fragment.lean_ctor(),
        rank = classification.inferred_fragment.to_rank(),
    ))
}

/// Compute a deterministic SHA-256 hex certificate digest (`spec_digest`)
/// binding the item identity (`def_id`), captured MIR digest (`mir_sha256`),
/// optional authored specification source (`spec_src`), and declared/inferred
/// `MirFragment` (`fragment.as_str()`).
///
/// Every component is length-prefixed in a versioned canonical encoding
/// (`anneal-fragment-spec-digest-v1`), so distinct input tuples never share a
/// preimage, and `spec_src = None` (no authored `Specs/<Item>.lean`) is
/// distinguished from `Some("")` (an empty authored file). Recorded as
/// `LockedUnitRecord::spec_digest` in `.anneal/spec-lock.json`.
pub fn compute_fragment_spec_digest(
    def_id: &str,
    mir_sha256: &str,
    spec_src: Option<&str>,
    fragment: MirFragment,
) -> String {
    let spec_segment = match spec_src {
        Some(s) => format!("some:{}:{}", s.len(), sha256_hex(s.as_bytes())),
        None => "none".to_string(),
    };
    let canonical = format!(
        "anneal-fragment-spec-digest-v1\ndef_id:{}:{}\nmir_sha256:{}:{}\nfragment:{}:{}\nspec:{}\n",
        def_id.len(),
        def_id,
        mir_sha256.len(),
        mir_sha256,
        fragment.as_str().len(),
        fragment.as_str(),
        spec_segment,
    );
    sha256_hex(canonical.as_bytes())
}

/// Static MIR and contract profile classifying which fuel-free lifting
/// pattern(s) apply to a verification subject.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MirLiftingProfile {
    /// Whether a captured `Mir/<Item>.lean` module containing a `CapturedMir`
    /// `body` was available for inspection.
    pub has_captured_mir: bool,
    /// Number of basic blocks detected in `body.basicBlocks`.
    pub basic_block_count: usize,
    /// Number of generic type parameters (`typeParamCount`) declared on `body`.
    pub type_param_count: usize,
    /// Whether `body` dereferences a pointer or reference
    /// (`ProjectionElem.deref`).
    pub has_deref_projection: bool,
    /// Whether `body` takes or forms an exclusive mutable reference
    /// (`RigidTy.ref Mutability.mut` or `BorrowKind.mut`).
    pub has_mut_borrow: bool,
    /// Whether `body` contains memory-dependent or non-intraprocedural
    /// operations other than `ProjectionElem.deref` and call terminators
    /// (`Rvalue.ref`, `Rvalue.rawPtr`, `Rvalue.copyForDeref`,
    /// `ProjectionElem.unwrapUnsafeBinder`, `BinOp.offset`,
    /// `CastKind.{pointerCoercion,ptrToPtr,fnPtrToPtr}`, provenance-exposing
    /// `CastKind.{pointerExposeProvenance,pointerWithExposedProvenance}`,
    /// `StatementKind.retag`, `copyNonOverlapping`, global-allocation
    /// constants, `Rvalue.{threadLocalRef,shallowInitBox}`,
    /// `backwardIncompatibleDropHint`, or `TerminatorKind.inlineAsm`), all of
    /// which `Anneal.PureMirExec.checkPureMir` rejects.
    pub has_impure_rvalue_or_asm: bool,
    /// Whether `body` contains a `TerminatorKind.call` or `tailCall`.
    pub has_call_terminator: bool,
    /// Whether `body.basicBlocks` has a cyclic control-flow back-edge
    /// (`bb_i -> bb_j` with `j <= i`), indicating a loop.
    pub has_cfg_back_edge: bool,
    /// Minimum `MirFragment` inferred for `body` in the 5-element lattice
    /// (syntactic `Anneal.PureMirExec.inferMinFragment` parity).
    pub inferred_fragment: MirFragment,
    /// Ordered MIR construct escalation reasons explaining why
    /// `inferred_fragment` exceeds `MirFragment::PureLoopFree`.
    pub fragment_escalation_reasons: Vec<String>,
    /// Whether `body.basicBlocks` contains syntax outside the closed inline
    /// `MirAst` literal grammar (helper `def` references, `let`/`fun`,
    /// structure updates, positional `X.mk`, or `⟨..⟩` constructors) that can
    /// hide MIR constructs from the textual scan; such bodies fail closed to
    /// `MirFragment::FullMir` and are never pure candidates.
    pub has_unscannable_mir: bool,
    /// Whether the bundle attaches inline `#[spec]` `requires` or `ensures`
    /// boolean companion predicates.
    pub has_inline_companions: bool,
    /// Whether any inspected inline `#[spec]` companion body is impure under
    /// `checkPureMir` (for example, closure-captured `&` upvars).
    pub has_impure_inline_companions: bool,
    /// Whether the bundle links concrete callees (`defaultCallees`) or assumes
    /// modular call contracts (`#[external_spec]` or `#[spec(trusted)]`).
    pub has_callees_or_modular_contracts: bool,
}

impl MirLiftingProfile {
    /// Returns `true` when a captured MIR body was inspected and contains no
    /// dereferences, memory-dependent rvalues/casts, call terminators, or
    /// unscannable syntax, i.e. exactly when
    /// `fragment_classification().is_pure_mir()` (syntactic
    /// `inferMinFragment body ≤ .pureBoundedLoop`). This is a necessary
    /// condition for `Anneal.PureMirExec.checkPureMir body = true`, which
    /// additionally rejects pointer/untyped relational `BinOp` assignments
    /// (`hasNoPtrRelationalAssign`, `inferBorrowFreeMinFragment`).
    pub fn is_pure_call_free_candidate(&self) -> bool {
        self.has_captured_mir
            && !self.has_unscannable_mir
            && !self.has_deref_projection
            && !self.has_impure_rvalue_or_asm
            && !self.has_call_terminator
    }

    /// Returns `true` when a captured MIR body is alias-free (`checkPureMir`
    /// statement/rvalue discipline) apart from function calls.
    pub fn is_pure_with_callees_candidate(&self) -> bool {
        self.has_captured_mir
            && !self.has_unscannable_mir
            && !self.has_deref_projection
            && !self.has_impure_rvalue_or_asm
    }

    /// Project the profile's inferred fragment and escalation reasons as a
    /// `MirFragmentClassification`.
    pub fn fragment_classification(&self) -> MirFragmentClassification {
        if !self.has_captured_mir {
            return MirFragmentClassification {
                inferred_fragment: MirFragment::FullMir,
                escalation_reasons: vec![
                    "non-inline or unparsed CapturedMir body (missing basicBlocks)".to_string(),
                ],
            };
        }
        MirFragmentClassification {
            inferred_fragment: self.inferred_fragment,
            escalation_reasons: self.fragment_escalation_reasons.clone(),
        }
    }
}

/// Normalize `authored` contract flags against Rust-level attributes on
/// `bundle` for unauthored items without an existing `Proof/<Item>.lean` or
/// overriding `Specs/<Item>.lean` (`#[spec(equivalent_to: ...)]`, modular
/// callees, `#[spec(safe_total)]`, and generic `typeParamCount > 0`
/// `poly*Claim` surfaces).
///
/// When `authored.has_proof` or `authored.has_specs` is `true`,
/// `detect_authored_item_modules` has already inspected `Specs/<Item>.lean`
/// and `Proof/<Item>.lean` (for example, distinguishing an `ItemSpec` override
/// or a stateless `VerificationResult` proof via `rustSafeTotalSpec` on a
/// `#[spec(safe_total, equivalent_to: ...)]` item), so Rust-attribute defaults
/// and `is_polymorphic` are never forced over authored modules.
pub(crate) fn effective_authored_for_bundle(
    bundle: &SubjectObligationBundle,
    mut authored: AuthoredItemModules,
    unauthored_profile: Option<&MirLiftingProfile>,
) -> AuthoredItemModules {
    if !authored.is_ub_exception
        && !authored.is_modular
        && !authored.has_proof
        && !authored.is_equiv
        && !authored.has_specs
    {
        if bundle.rust_equiv_target_module_suffix().is_some() {
            authored.is_equiv = true;
            authored.is_total = false;
            authored.is_stateful = false;
        } else if !authored.is_stateful {
            if !bundle.external_spec_callees.is_empty() || !bundle.called_callees.is_empty() {
                authored.is_modular = true;
            } else if bundle.has_rust_safe_total_attr() {
                authored.is_total = true;
            }
        }
    }
    if !authored.has_proof
        && !authored.is_equiv
        && unauthored_profile.is_some_and(|p| p.type_param_count > 0)
    {
        authored.is_polymorphic = true;
    }
    authored
}

/// Resolve `rel_item_path` under `mir_root` (`.anneal/generated/Mir`) when its
/// content matches `record.target.mir_module_sha256` (or no expected SHA is
/// recorded), falling back to `find_source_mir_file` in
/// `<workspace>/target/anneal/units` when `.anneal/generated/Mir` is absent or
/// holds a stale/stub file superseded by a newer unit capture.
pub(crate) fn resolve_workspace_mir_file(
    mir_root: &Path,
    record: &UnitTargetRecord,
    rel_item_path: &Path,
) -> Option<PathBuf> {
    let direct = mir_root.join(rel_item_path);
    let expected_sha = &record.target.mir_module_sha256;
    let direct_exists = direct.is_file();
    if direct_exists
        && (expected_sha.is_empty()
            || fs::read(&direct)
                .ok()
                .is_some_and(|bytes| &sha256_hex(&bytes) == expected_sha))
    {
        return Some(direct);
    }
    let fallback_cfg = mir_root
        .parent()
        .and_then(|g| g.parent())
        .and_then(|d| d.parent())
        .map(ScaffoldConfig::new);
    if let Some(cfg) = fallback_cfg
        && let Some(unit_path) = find_source_mir_file(&cfg, record, rel_item_path)
        && (!direct_exists
            || (!expected_sha.is_empty()
                && fs::read(&unit_path)
                    .ok()
                    .is_some_and(|bytes| &sha256_hex(&bytes) == expected_sha)))
    {
        return Some(unit_path);
    }
    direct_exists.then_some(direct)
}

/// Inspect `mir_root` on disk (with fallback to `target/anneal/units`) for
/// `bundle`'s subject and inline companion MIR modules and compute its
/// `MirLiftingProfile`.
pub fn analyze_workspace_lifting_profile(
    mir_root: &Path,
    bundle: &SubjectObligationBundle,
) -> MirLiftingProfile {
    let subj_mir = resolve_workspace_mir_file(mir_root, &bundle.subject, &bundle.item_rel_path)
        .and_then(|p| fs::read_to_string(p).ok());
    let mut comp_mirs = Vec::new();
    for comp in bundle.inline_requires.iter().chain(&bundle.inline_ensures) {
        let rel = module_suffix_to_rel_path(&derive_item_module_suffix(comp));
        if let Some(txt) =
            resolve_workspace_mir_file(mir_root, comp, &rel).and_then(|p| fs::read_to_string(p).ok())
        {
            comp_mirs.push(txt);
        }
    }
    let comp_refs: Vec<&str> = comp_mirs.iter().map(String::as_str).collect();
    analyze_mir_lifting_profile(bundle, subj_mir.as_deref(), &comp_refs)
}

/// Compute a `MirLiftingProfile` from `bundle`, optional subject MIR Lean text,
/// and any available inline companion MIR Lean texts.
pub fn analyze_mir_lifting_profile(
    bundle: &SubjectObligationBundle,
    subject_mir_text: Option<&str>,
    companion_mir_texts: &[&str],
) -> MirLiftingProfile {
    let mut profile = MirLiftingProfile {
        has_inline_companions: !bundle.inline_requires.is_empty()
            || !bundle.inline_ensures.is_empty(),
        has_callees_or_modular_contracts: !bundle.transitive_callees.is_empty()
            || !bundle.external_spec_callees.is_empty()
            || !bundle.called_callees.is_empty(),
        ..MirLiftingProfile::default()
    };

    if let Some(mir_src) = subject_mir_text {
        let scan = scan_captured_mir_body(mir_src);
        profile.has_captured_mir = scan.has_body;
        profile.basic_block_count = scan.basic_block_count;
        profile.type_param_count = scan.type_param_count;
        profile.has_deref_projection = scan.has_deref_projection;
        profile.has_mut_borrow = scan.has_mut_borrow;
        profile.has_impure_rvalue_or_asm = scan.has_impure_rvalue_or_asm;
        profile.has_call_terminator = scan.has_call_terminator;
        profile.has_cfg_back_edge = scan.has_cfg_back_edge;
        profile.inferred_fragment = scan.inferred_fragment;
        profile.fragment_escalation_reasons = scan.escalation_reasons;
        profile.has_unscannable_mir = scan.has_unscannable_syntax;
    } else {
        profile.inferred_fragment = MirFragment::FullMir;
    }

    for comp_src in companion_mir_texts {
        let comp_scan = scan_captured_mir_body(comp_src);
        if comp_scan.has_body
            && (comp_scan.has_deref_projection
                || comp_scan.has_impure_rvalue_or_asm
                || comp_scan.has_call_terminator
                || comp_scan.has_unscannable_syntax)
        {
            profile.has_impure_inline_companions = true;
        }
    }

    profile
}

#[derive(Debug, Default)]
struct MirBodyScan {
    has_body: bool,
    basic_block_count: usize,
    type_param_count: usize,
    has_deref_projection: bool,
    has_mut_borrow: bool,
    has_impure_rvalue_or_asm: bool,
    has_call_terminator: bool,
    has_cfg_back_edge: bool,
    has_unscannable_syntax: bool,
    inferred_fragment: MirFragment,
    escalation_reasons: Vec<String>,
}

/// Truncate `decl_src` (which starts at a `def` header) before the next line
/// that begins a new top-level Lean command, so trailing declarations (e.g.
/// `def defaultClaim`, `end Mir.X`, or another body after a non-inline
/// `def body : CapturedMir := otherBody` alias) never leak into the scan.
fn bound_to_top_level_decl(decl_src: &str) -> &str {
    const TOP_LEVEL_COMMANDS: &[&str] = &[
        "def ", "theorem ", "lemma ", "example ", "instance ", "abbrev ", "end ", "end\n",
        "namespace ", "section ", "open ", "#", "@[", "private ", "protected ",
        "noncomputable ", "set_option ", "attribute ", "structure ", "inductive ", "class ",
        "macro ", "syntax ", "variable ", "universe ", "mutual",
    ];
    let mut offset = 0usize;
    for (idx, line) in decl_src.split_inclusive('\n').enumerate() {
        let trimmed = line.trim_start();
        if idx > 0 && TOP_LEVEL_COMMANDS.iter().any(|cmd| trimmed.starts_with(cmd)) {
            return &decl_src[..offset];
        }
        offset += line.len();
    }
    decl_src
}

/// `CapturedMir` structure field names (`Trusted.Rustc.V2026_06_01.MirAst.Body`).
const CAPTURED_MIR_FIELDS: &[&str] = &[
    "defPath", "phase", "role", "argCount", "localDecls", "basicBlocks", "fnAbi", "layouts",
    "allocations", "typeParamCount", "genericParams", "traitImpls",
];

/// Return the extent of the `basicBlocks` field value that starts at
/// `after_bb` (just past `basicBlocks :=`) in comment/string-stripped text.
///
/// The value ends at the first depth-0 `,`, the first unmatched closing
/// bracket (the end of the enclosing `CapturedMir` literal), or a depth-0
/// `<CapturedMir field> :=` (newline-separated fields). Returns `None` when the
/// value is empty, brackets are mismatched, or the text ends while a bracket is
/// still open (e.g. a declaration truncated by `bound_to_top_level_decl`).
fn basic_blocks_value_extent(after_bb: &str) -> Option<&str> {
    let mut stack: Vec<char> = Vec::new();
    let mut end = after_bb.len();
    let mut prev: Option<char> = None;
    for (idx, ch) in after_bb.char_indices() {
        match ch {
            '(' | '[' | '{' => stack.push(ch),
            ')' | ']' | '}' => {
                let Some(open) = stack.pop() else {
                    end = idx;
                    break;
                };
                if !matches!((open, ch), ('(', ')') | ('[', ']') | ('{', '}')) {
                    return None;
                }
            }
            ',' if stack.is_empty() => {
                end = idx;
                break;
            }
            _ if stack.is_empty()
                && !prev.is_some_and(|c| c.is_alphanumeric() || c == '_' || c == '.')
                && CAPTURED_MIR_FIELDS.iter().any(|field| {
                    after_bb[idx..]
                        .strip_prefix(field)
                        .is_some_and(|rest| rest.trim_start().starts_with(":="))
                }) =>
            {
                end = idx;
                break;
            }
            _ => {}
        }
        prev = Some(ch);
    }
    if end == after_bb.len() && !stack.is_empty() {
        return None;
    }
    let value = &after_bb[..end];
    (!value.trim().is_empty()).then_some(value)
}

/// Locate `<field> <ws>* :=` in `src` at a Lean identifier boundary, returning
/// `(field_start_byte, after_assign_byte)` so column-aligned (`basicBlocks  :=`)
/// or compact (`basicBlocks:=`) field assignments are matched uniformly.
fn find_field_assign(src: &str, field: &str) -> Option<(usize, usize)> {
    let mut search_from = 0usize;
    while let Some(rel) = src[search_from..].find(field) {
        let start = search_from + rel;
        let prev_ok = src[..start]
            .chars()
            .next_back()
            .is_none_or(|c| !crate::agent::is_lean_ident_char(c) && c != '.');
        let after_field = start + field.len();
        if prev_ok {
            let rest = &src[after_field..];
            let trimmed = rest.trim_start();
            if let Some(after_eq) = trimmed.strip_prefix(":=") {
                let consumed = rest.len() - after_eq.len();
                return Some((start, after_field + consumed));
            }
        }
        search_from = after_field;
    }
    None
}

fn scan_captured_mir_body(mir_src: &str) -> MirBodyScan {
    let clean = strip_lean_comments_and_strings(mir_src);
    let body_clean = if let Some(idx) = clean.find("def body : CapturedMir") {
        bound_to_top_level_decl(&clean[idx..])
    } else if let Some(idx) = clean.find(": CapturedMir") {
        let line_start = clean[..idx].rfind('\n').map(|p| p + 1).unwrap_or(0);
        bound_to_top_level_decl(&clean[line_start..])
    } else {
        clean.as_str()
    };
    let Some((_, bb_val_start)) = find_field_assign(body_clean, "basicBlocks") else {
        return MirBodyScan {
            inferred_fragment: MirFragment::FullMir,
            ..MirBodyScan::default()
        };
    };
    let type_param_count = find_field_assign(body_clean, "typeParamCount")
        .and_then(|(_, val_start)| {
            body_clean[val_start..]
                .split(|c: char| !c.is_ascii_digit())
                .find(|s| !s.is_empty())
                .and_then(|s| s.parse::<usize>().ok())
        })
        .unwrap_or(0);
    let local_decls_slice = if let Some((_, ld_val_start)) = find_field_assign(body_clean, "localDecls") {
        let after_ld = &body_clean[ld_val_start..];
        basic_blocks_value_extent(after_ld).unwrap_or(after_ld)
    } else {
        ""
    };
    let after_bb = &body_clean[bb_val_start..];
    // Delimit the `basicBlocks` value by bracket structure rather than by the
    // first textual `<field> :=`, so named constructor arguments that reuse a
    // `CapturedMir` field name (`.unevaluated (defPath := ..)`) cannot truncate
    // the scan, and a truncated / unbalanced literal fails closed.
    let blocks_value = basic_blocks_value_extent(after_bb);
    let blocks_slice = blocks_value.unwrap_or(after_bb);

    let norm_decls = normalize_parens_and_ws(local_decls_slice);
    let norm_blocks = normalize_parens_and_ws(blocks_slice);
    let block_toks: Vec<&str> = norm_blocks.split_whitespace().collect();

    let (basic_block_count, has_cfg_back_edge, malformed_blocks_reason) =
        detect_blocks_and_back_edges(&norm_blocks, &block_toks);
    let unscannable_token = blocks_value
        .is_none()
        .then(|| "unbalanced, truncated, or empty basicBlocks literal".to_string())
        .or_else(|| first_unscannable_block_token(&block_toks))
        .or(malformed_blocks_reason);
    let has_unscannable_syntax = unscannable_token.is_some();

    let has_deref_projection = has_ast_ctor(&norm_blocks, "ProjectionElem", "deref");
    let has_unwrap_unsafe_binder =
        has_ast_ctor(&norm_blocks, "ProjectionElem", "unwrapUnsafeBinder");
    let has_rvalue_ref = detect_rvalue_ref(&block_toks);
    let has_rvalue_raw_ptr = detect_rvalue_raw_ptr(&block_toks);
    let has_copy_for_deref = has_ast_ctor(&norm_blocks, "Rvalue", "copyForDeref");
    let has_binop_offset = has_ast_ctor(&norm_blocks, "BinOp", "offset");
    let has_cast_pointer_coercion = has_ast_ctor(&norm_blocks, "CastKind", "pointerCoercion");
    let has_cast_ptr_to_ptr = has_ast_ctor(&norm_blocks, "CastKind", "ptrToPtr");
    let has_stmt_retag = has_ast_ctor(&norm_blocks, "StatementKind", "retag");

    let has_copy_non_overlapping = detect_copy_non_overlapping(&block_toks);
    let has_const_indirect = has_ast_ctor(&norm_blocks, "ConstValue", "indirect");
    let has_const_slice_ptr = detect_const_slice_ptr(&block_toks);

    let has_term_call = has_ast_ctor(&norm_blocks, "TerminatorKind", "call");
    let has_term_tail_call = has_ast_ctor(&norm_blocks, "TerminatorKind", "tailCall");
    let has_term_inline_asm = has_ast_ctor(&norm_blocks, "TerminatorKind", "inlineAsm");
    let has_cast_fn_ptr_to_ptr = has_ast_ctor(&norm_blocks, "CastKind", "fnPtrToPtr");
    // Wave 1 (`Anneal.PureMirExec.checkCastFragment`): both provenance-exposing
    // casts require `.fullMir`, matching `isPureRvalue = false` and the
    // kernel-checked `witnessExposeProvenanceCast` /
    // `witnessWithExposedProvenanceCast` theorems.
    let has_cast_expose_provenance =
        has_ast_ctor(&norm_blocks, "CastKind", "pointerExposeProvenance");
    let has_cast_with_exposed_provenance =
        has_ast_ctor(&norm_blocks, "CastKind", "pointerWithExposedProvenance");
    let has_rvalue_thread_local_ref = has_ast_ctor(&norm_blocks, "Rvalue", "threadLocalRef");
    let has_rvalue_shallow_init_box = has_ast_ctor(&norm_blocks, "Rvalue", "shallowInitBox");
    let has_stmt_drop_hint =
        has_ast_ctor(&norm_blocks, "StatementKind", "backwardIncompatibleDropHint");

    let mut inferred_fragment = MirFragment::PureLoopFree;
    let mut escalation_reasons = Vec::new();
    let mut record_escalation = |frag: MirFragment, reason: &str| {
        inferred_fragment = inferred_fragment.join(frag);
        escalation_reasons.push(reason.to_string());
    };

    if has_cfg_back_edge {
        record_escalation(MirFragment::PureBoundedLoop, "CFG back-edge");
    }
    if has_deref_projection {
        record_escalation(MirFragment::TreeBorrowsLocal, "ProjectionElem.deref");
    }
    if has_unwrap_unsafe_binder {
        record_escalation(
            MirFragment::TreeBorrowsLocal,
            "ProjectionElem.unwrapUnsafeBinder",
        );
    }
    if has_rvalue_ref {
        record_escalation(MirFragment::TreeBorrowsLocal, "Rvalue.ref");
    }
    if has_rvalue_raw_ptr {
        record_escalation(MirFragment::TreeBorrowsLocal, "Rvalue.rawPtr");
    }
    if has_copy_for_deref {
        record_escalation(MirFragment::TreeBorrowsLocal, "Rvalue.copyForDeref");
    }
    if has_binop_offset {
        record_escalation(MirFragment::TreeBorrowsLocal, "BinOp.offset");
    }
    if has_cast_pointer_coercion {
        record_escalation(MirFragment::TreeBorrowsLocal, "CastKind.pointerCoercion");
    }
    if has_cast_ptr_to_ptr {
        record_escalation(MirFragment::TreeBorrowsLocal, "CastKind.ptrToPtr");
    }
    if has_stmt_retag {
        record_escalation(MirFragment::TreeBorrowsLocal, "StatementKind.retag");
    }
    if has_copy_non_overlapping {
        record_escalation(
            MirFragment::IntrinsicCopy,
            "NonDivergingIntrinsic.copyNonOverlapping",
        );
    }
    if has_const_indirect {
        record_escalation(MirFragment::IntrinsicCopy, "ConstValue.indirect");
    }
    if has_const_slice_ptr {
        record_escalation(
            MirFragment::IntrinsicCopy,
            "ConstValue.slice (ConstScalar.ptr)",
        );
    }
    if has_term_call {
        record_escalation(MirFragment::FullMir, "TerminatorKind.call");
    }
    if has_term_tail_call {
        record_escalation(MirFragment::FullMir, "TerminatorKind.tailCall");
    }
    if has_term_inline_asm {
        record_escalation(MirFragment::FullMir, "TerminatorKind.inlineAsm");
    }
    if has_cast_fn_ptr_to_ptr {
        record_escalation(MirFragment::FullMir, "CastKind.fnPtrToPtr");
    }
    if has_cast_expose_provenance {
        record_escalation(MirFragment::FullMir, "CastKind.pointerExposeProvenance");
    }
    if has_cast_with_exposed_provenance {
        record_escalation(MirFragment::FullMir, "CastKind.pointerWithExposedProvenance");
    }
    if has_rvalue_thread_local_ref {
        record_escalation(MirFragment::FullMir, "Rvalue.threadLocalRef");
    }
    if has_rvalue_shallow_init_box {
        record_escalation(MirFragment::FullMir, "Rvalue.shallowInitBox");
    }
    if has_stmt_drop_hint {
        record_escalation(
            MirFragment::FullMir,
            "StatementKind.backwardIncompatibleDropHint",
        );
    }
    if let Some(tok) = &unscannable_token {
        record_escalation(
            MirFragment::FullMir,
            &format!("unscannable non-inline MIR syntax `{tok}` in basicBlocks (fail-closed)"),
        );
    }

    let decls_have_mut_ref = norm_decls.contains("RigidTy.ref Mutability.mut")
        || norm_decls.contains(".ref Mutability.mut")
        || norm_decls.contains("RigidTy.ref .mut ")
        || norm_decls.contains(".ref .mut ");
    let blocks_have_mut_borrow = detect_mut_borrow(&block_toks);
    let has_mut_borrow = blocks_have_mut_borrow || (has_deref_projection && decls_have_mut_ref);

    let has_impure_rvalue_or_asm = has_unwrap_unsafe_binder
        || has_rvalue_ref
        || has_rvalue_raw_ptr
        || has_copy_for_deref
        || has_binop_offset
        || has_cast_pointer_coercion
        || has_cast_ptr_to_ptr
        || has_stmt_retag
        || has_copy_non_overlapping
        || has_const_indirect
        || has_const_slice_ptr
        || has_term_inline_asm
        || has_cast_fn_ptr_to_ptr
        || has_cast_expose_provenance
        || has_cast_with_exposed_provenance
        || has_rvalue_thread_local_ref
        || has_rvalue_shallow_init_box
        || has_stmt_drop_hint;

    let has_call_terminator = has_term_call || has_term_tail_call;

    MirBodyScan {
        has_body: true,
        basic_block_count,
        type_param_count,
        has_deref_projection,
        has_mut_borrow,
        has_impure_rvalue_or_asm,
        has_call_terminator,
        // Fail closed: blocks hidden behind non-inline syntax may hide back-edges.
        has_cfg_back_edge: has_cfg_back_edge || has_unscannable_syntax,
        has_unscannable_syntax,
        inferred_fragment,
        escalation_reasons,
    }
}

/// Strip Lean `--` line comments, nested `/- ... -/` block comments, and
/// `"..."` string literal payloads in a single lexical pass so comment markers
/// inside string literals (`"--"` or `"/-"`) cannot truncate strings and quotes
/// inside comments cannot invert string literal polarity.
fn strip_lean_comments_and_strings(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0usize;
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
                i += 1;
            }
            continue;
        }

        if in_str {
            if bytes[i] == b'\\' {
                i += 1;
                if let Some(ch) = src[i..].chars().next() {
                    i += ch.len_utf8();
                }
            } else if bytes[i] == b'"' {
                in_str = false;
                out.push_str("\"\"");
                i += 1;
                prev_ch = None;
            } else {
                i += 1;
            }
            continue;
        }

        // Guillemet-quoted identifiers (`«...»`) are opaque: their contents may
        // contain `"`, `--`, `/-`, `,`, `]`, or `terminator :=` without starting
        // a string, comment, bracket, or field delimiter. Replace with a single
        // opaque placeholder token `«ident»` so interior punctuation cannot
        // confuse `basic_blocks_value_extent` or `normalize_parens_and_ws`.
        if src[i..].starts_with('«') {
            let end = src[i..].find('»').map_or(src.len(), |p| i + p + '»'.len_utf8());
            out.push_str(" «ident» ");
            i = end;
            prev_ch = Some('»');
            continue;
        }

        // Raw string literals (`r"..."`, `r#"..."#`) have no escapes and may
        // contain unescaped `"` (e.g. `r#"a"b"#`), so they need their own
        // delimiter matching to keep string polarity aligned.
        if let Some(end) = lean_raw_string_end(bytes, i, prev_ch) {
            out.push_str("\"\"");
            i = end;
            prev_ch = None;
            continue;
        }

        if bytes[i] == b'"' {
            if prev_ch == Some('!')
                && out[..out.len() - 1].ends_with(crate::agent::is_lean_ident_char)
            {
                // Interpolated string (`s!"..{term}.."`, `m!"..."`): the `{..}`
                // interpolations may nest string/char literals, comments, and
                // braces. The whole literal (including its `s!` prefix) only
                // produces a `String` value, so it is replaced by `""`.
                out.pop();
                while out.ends_with(|c: char| crate::agent::is_lean_ident_char(c) || c == '.') {
                    out.pop();
                }
                i = lean_interpolated_string_end(src, i);
                out.push_str("\"\"");
                prev_ch = None;
                continue;
            }
            in_str = true;
            i += 1;
            prev_ch = None;
            continue;
        }

        if let Some(char_len) = crate::agent::lean_char_literal_len(src, i, prev_ch) {
            out.push(' ');
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

        if let Some(ch) = src[i..].chars().next() {
            out.push(ch);
            i += ch.len_utf8();
            prev_ch = Some(ch);
        } else {
            break;
        }
    }
    out
}

/// If `bytes[i..]` starts a Lean raw string literal (`r"..."`, `r#"..."#`,
/// `r##"..."##`, ...) that is not part of a longer identifier, return the byte
/// index just past its closing delimiter (or `bytes.len()` if unterminated).
fn lean_raw_string_end(bytes: &[u8], i: usize, prev_ch: Option<char>) -> Option<usize> {
    if bytes.get(i) != Some(&b'r')
        || prev_ch.is_some_and(|c| crate::agent::is_lean_ident_char(c) || matches!(c, '.' | '!' | '?'))
    {
        return None;
    }
    let mut j = i + 1;
    let mut hashes = 0usize;
    while bytes.get(j) == Some(&b'#') {
        hashes += 1;
        j += 1;
    }
    if bytes.get(j) != Some(&b'"') {
        return None;
    }
    j += 1;
    while j < bytes.len() {
        if bytes[j] == b'"' && bytes.get(j + 1..j + 1 + hashes).is_some_and(|h| h.iter().all(|&b| b == b'#')) {
            return Some(j + 1 + hashes);
        }
        j += 1;
    }
    Some(bytes.len())
}

/// Return the byte index just past a plain Lean string literal whose opening
/// quote is at `bytes[i]` (honouring `\` escapes).
fn lean_plain_string_end(bytes: &[u8], i: usize) -> usize {
    let mut j = i + 1;
    while j < bytes.len() {
        match bytes[j] {
            b'\\' => j += 2,
            b'"' => return j + 1,
            _ => j += 1,
        }
    }
    bytes.len()
}

/// Return the byte index just past a Lean interpolated string literal
/// (`s!"..."`) whose opening quote is at `src.as_bytes()[i]`, skipping `{..}`
/// interpolations that may themselves contain strings, char literals, comments,
/// guillemets, and braces.
fn lean_interpolated_string_end(src: &str, i: usize) -> usize {
    let bytes = src.as_bytes();
    let mut j = i + 1;
    while j < bytes.len() {
        match bytes[j] {
            b'\\' => {
                j += 1;
                if let Some(ch) = src[j..].chars().next() {
                    j += ch.len_utf8();
                }
            }
            b'"' => return j + 1,
            b'{' => j = lean_interpolation_end(src, j + 1),
            _ => j += 1,
        }
    }
    bytes.len()
}

/// Skip Lean term syntax inside an interpolation starting at `src.as_bytes()[j]`
/// (just past `{`), returning the byte index just past the matching `}`.
fn lean_interpolation_end(src: &str, mut j: usize) -> usize {
    let bytes = src.as_bytes();
    let mut depth = 0usize;
    let mut prev_ch: Option<char> = None;
    while j < bytes.len() {
        if src[j..].starts_with('«') {
            j = src[j..].find('»').map_or(src.len(), |p| j + p + '»'.len_utf8());
            prev_ch = Some('»');
            continue;
        }
        if j + 1 < bytes.len() && bytes[j] == b'/' && bytes[j + 1] == b'-' {
            let mut bdepth = 1usize;
            j += 2;
            while j < bytes.len() && bdepth > 0 {
                if j + 1 < bytes.len() && bytes[j] == b'/' && bytes[j + 1] == b'-' {
                    bdepth += 1;
                    j += 2;
                } else if j + 1 < bytes.len() && bytes[j] == b'-' && bytes[j + 1] == b'/' {
                    bdepth -= 1;
                    j += 2;
                } else {
                    j += 1;
                }
            }
            prev_ch = None;
            continue;
        }
        if j + 1 < bytes.len() && bytes[j] == b'-' && bytes[j + 1] == b'-' {
            while j < bytes.len() && bytes[j] != b'\n' {
                j += 1;
            }
            prev_ch = None;
            continue;
        }
        if let Some(char_len) = crate::agent::lean_char_literal_len(src, j, prev_ch) {
            j += char_len;
            prev_ch = None;
            continue;
        }
        if let Some(end) = lean_raw_string_end(bytes, j, prev_ch) {
            j = end;
            prev_ch = None;
            continue;
        }
        match bytes[j] {
            b'{' => {
                depth += 1;
                j += 1;
                prev_ch = Some('{');
            }
            b'}' => {
                if depth == 0 {
                    return j + 1;
                }
                depth -= 1;
                j += 1;
                prev_ch = Some('}');
            }
            b'"' if prev_ch == Some('!') => {
                j = lean_interpolated_string_end(src, j);
                prev_ch = None;
            }
            b'"' => {
                j = lean_plain_string_end(bytes, j);
                prev_ch = None;
            }
            _ => {
                if let Some(ch) = src[j..].chars().next() {
                    j += ch.len_utf8();
                    prev_ch = Some(ch);
                } else {
                    break;
                }
            }
        }
    }
    bytes.len()
}

fn normalize_parens_and_ws(src: &str) -> String {
    let mut spaced = String::with_capacity(src.len() + 16);
    spaced.push(' ');
    let mut chars = src.chars().peekable();
    while let Some(ch) = chars.next() {
        if matches!(ch, '(' | ')' | '[' | ']' | '{' | '}' | ',') {
            spaced.push(' ');
        } else if ch == ':' && chars.peek() == Some(&'=') {
            chars.next();
            spaced.push_str(" := ");
        } else {
            spaced.push(ch);
        }
    }
    spaced.push(' ');
    let collapsed = spaced.split_whitespace().collect::<Vec<_>>().join(" ");
    format!(" {collapsed} ")
}

/// Constructor vocabulary `(TypeName, constructors)` of every inductive type
/// that can occur inside an inline `CapturedMir.basicBlocks` literal
/// (`Trusted.Rustc.V2026_06_01.MirAst`, plus `List` / `Option` / `Bool`).
const MIR_BLOCK_CTOR_VOCAB: &[(&str, &[&str])] = &[
    (
        "ProjectionElem",
        &[
            "deref", "field", "index", "constantIndex", "subslice", "downcast", "opaqueCast",
            "unwrapUnsafeBinder",
        ],
    ),
    ("Operand", &["copy", "move", "constant"]),
    (
        "BinOp",
        &[
            "add", "addUnchecked", "addWithOverflow", "sub", "subUnchecked", "subWithOverflow",
            "mul", "mulUnchecked", "mulWithOverflow", "div", "rem", "bitXor", "bitAnd", "bitOr",
            "shl", "shlUnchecked", "shr", "shrUnchecked", "eq", "lt", "le", "ne", "ge", "gt",
            "cmp", "offset",
        ],
    ),
    ("UnOp", &["not", "neg", "ptrMetadata"]),
    ("NullOp", &["sizeOf", "alignOf", "offsetOf", "ubChecks", "contractChecks"]),
    ("BorrowKind", &["shared", "mut"]),
    (
        "CastKind",
        &[
            "pointerExposeProvenance", "pointerWithExposedProvenance", "pointerCoercion",
            "intToInt", "floatToInt", "floatToFloat", "intToFloat", "ptrToPtr", "fnPtrToPtr",
            "transmute", "subtype",
        ],
    ),
    ("AggregateKind", &["array", "tuple", "adt", "closure", "coroutine", "rawPtr"]),
    (
        "Rvalue",
        &[
            "use", "repeat", "ref", "threadLocalRef", "rawPtr", "len", "cast", "binaryOp",
            "nullaryOp", "unaryOp", "discriminant", "aggregate", "shallowInitBox", "copyForDeref",
            "wrapUnsafeBinder",
        ],
    ),
    ("NonDivergingIntrinsic", &["assume", "copyNonOverlapping"]),
    ("RetagKind", &["fnEntry", "twoPhase", "raw", "default"]),
    (
        "StatementKind",
        &[
            "assign", "setDiscriminant", "deinit", "storageLive", "storageDead", "retag",
            "placeMention", "intrinsic", "coverage", "constEvalCounter",
            "backwardIncompatibleDropHint", "nop",
        ],
    ),
    ("UnwindAction", &["cleanup", "unreachable", "terminate", "continue_"]),
    (
        "TerminatorKind",
        &[
            "goto", "switchInt", "unwindResume", "unwindTerminate", "return_", "unreachable",
            "drop", "call", "tailCall", "assert", "inlineAsm",
        ],
    ),
    ("UintTy", &["u8", "u16", "u32", "u64", "u128", "usize"]),
    ("IntTy", &["i8", "i16", "i32", "i64", "i128", "isize"]),
    ("FloatTy", &["f16", "f32", "f64", "f128"]),
    ("Mutability", &["not", "mut"]),
    ("Safety", &["safe", "unsafe_"]),
    ("CallConv", &["rust", "c", "rustIntrinsic", "other"]),
    ("RigidTy", RIGID_TY_CTORS),
    ("ConstScalar", &["int", "ptr"]),
    ("ConstValue", &["zeroSized", "scalar", "slice", "indirect", "unevaluated"]),
    ("List", &["nil", "cons"]),
    ("Option", &["some", "none"]),
    ("Bool", &["true", "false"]),
];

/// Constructors of `Trusted.Rustc.V2026_06_01.MirAst.RigidTy`.
const RIGID_TY_CTORS: &[&str] = &[
    "param", "alias", "bool", "char", "int", "uint", "float", "never", "str", "tuple", "array",
    "slice", "ref", "rawPtr", "adt", "fnDef", "fnPtr", "closure", "dynamic", "foreign", "other",
];

/// Closed set of structure field names that can appear before `:=` inside an
/// inline `CapturedMir.basicBlocks` literal (`BasicBlockData`, `Statement`,
/// `Terminator`, `SwitchTargets`, `Place`, `Ty`, `ScalarInt`, `ProvenancePtr`,
/// `WrappingRange`, `ConstOperand`).
const MIR_BLOCK_FIELD_VOCAB: &[&str] = &[
    "statements",
    "terminator",
    "isCleanup",
    "kind",
    "span",
    "branches",
    "otherwise",
    "local_",
    "projection",
    "layoutIdx",
    "bits",
    "sizeBytes",
    "allocId",
    "offsetBytes",
    "start",
    "end_",
    "ty",
    "val",
    // String-valued named constructor argument (`ConstValue.unevaluated`,
    // `Rvalue.threadLocalRef`, `AggregateKind.adt`, `RigidTy.fnDef`, ...): its
    // value is a (stripped) string literal, it feeds no positional detector, and
    // `basic_blocks_value_extent` ignores it at bracket depth > 0.
    "defPath",
];

/// Validate that a namespace qualifier `qual` (the prefix before `.ctor`) is a
/// canonical qualifier for `type_name`, rejecting spoofed user namespaces such
/// as `MyHelper.Option.none` or `Evil.Mutability.not`.
fn is_valid_mir_type_qualifier(qual: &str, type_name: &str) -> bool {
    let qual = qual.strip_prefix("_root_.").unwrap_or(qual);
    if qual == type_name {
        return true;
    }
    if matches!(type_name, "List" | "Option" | "Bool") {
        return false;
    }
    let Some(prefix) = qual.strip_suffix(type_name).and_then(|p| p.strip_suffix('.')) else {
        return false;
    };
    if type_name == "CallConv"
        && matches!(
            prefix,
            "Layout"
                | "V2026_06_01.Layout"
                | "Rustc.V2026_06_01.Layout"
                | "Trusted.Rustc.V2026_06_01.Layout"
                | "Trusted.Layout"
        )
    {
        return true;
    }
    matches!(
        prefix,
        "MirAst"
            | "V2026_06_01.MirAst"
            | "Rustc.V2026_06_01.MirAst"
            | "Trusted.Rustc.V2026_06_01.MirAst"
            | "Trusted.MirAst"
    )
}

/// Return the constructor name of `tok` when it is a dotted shorthand
/// constructor (`.ctor`) or a (possibly namespace-qualified, `@`-prefixed)
/// `TypeName.ctor` token for `type_name`.
fn ast_ctor<'a>(tok: &'a str, type_name: &str) -> Option<&'a str> {
    let tok = tok.strip_prefix('@').unwrap_or(tok);
    if let Some(ctor) = tok.strip_prefix('.') {
        return (!ctor.is_empty() && !ctor.contains('.')).then_some(ctor);
    }
    let (qual, ctor) = tok.rsplit_once('.')?;
    (is_valid_mir_type_qualifier(qual, type_name) && !ctor.is_empty()).then_some(ctor)
}

/// `true` when `tok` is the *qualified* (`TypeName.ctor` / `*.TypeName.ctor`)
/// form of `type_name.ctor_name` (never the ambiguous dotted shorthand).
fn is_qualified_ctor(tok: &str, type_name: &str, ctor_name: &str) -> bool {
    !tok.trim_start_matches('@').starts_with('.') && ast_ctor(tok, type_name) == Some(ctor_name)
}

/// Match a Lean AST constructor in `norm_blocks` either in dotted shorthand
/// (`.ctor`) or type-qualified form (`TypeName.ctor` / `*.TypeName.ctor`) as a
/// standalone token, preventing false matches on identifier substrings (e.g.
/// `local_call`, `recall`, `my_retag`) or unrelated namespaces (`Mir.Demo.call`).
fn has_ast_ctor(norm_blocks: &str, type_name: &str, ctor_name: &str) -> bool {
    norm_blocks
        .split_whitespace()
        .any(|tok| ast_ctor(tok, type_name) == Some(ctor_name))
}

/// `true` when `tok` is a dotted shorthand (`.ctor`) or canonical qualified
/// (`TypeName.ctor`) constructor of the closed `MIR_BLOCK_CTOR_VOCAB`.
fn is_mir_vocab_ctor(tok: &str) -> bool {
    let tok = tok.strip_prefix('@').unwrap_or(tok);
    if let Some(ctor) = tok.strip_prefix('.') {
        return MIR_BLOCK_CTOR_VOCAB.iter().any(|(_, ctors)| ctors.contains(&ctor));
    }
    let Some((qual, ctor)) = tok.rsplit_once('.') else {
        return false;
    };
    let ty = qual.rsplit('.').next().unwrap_or(qual);
    is_valid_mir_type_qualifier(qual, ty)
        && MIR_BLOCK_CTOR_VOCAB
            .iter()
            .any(|(t, ctors)| *t == ty && ctors.contains(&ctor))
}

/// Return the first token of a normalized `basicBlocks` slice that lies outside
/// the closed inline `MirAst` literal grammar: numerals, stripped `""` string
/// literals, `true` / `false` / `some` / `none`, closed-vocabulary record field
/// names (`MIR_BLOCK_FIELD_VOCAB`) followed by `:=`, and `MIR_BLOCK_CTOR_VOCAB`
/// constructors. Anything else (a helper `def` reference such as `u32Ty` or
/// `mkTerm`, named constructor arguments such as `(target := 0)`, `let` / `fun`
/// / `with`, positional `Place.mk`, `⟨..⟩`, `++`) can hide arbitrary MIR
/// constructs from a textual scan, so the classifier fails closed to
/// `MirFragment::FullMir`.
fn first_unscannable_block_token(block_toks: &[&str]) -> Option<String> {
    block_toks.iter().enumerate().find_map(|(i, &tok)| {
        let is_valid_field = MIR_BLOCK_FIELD_VOCAB.contains(&tok)
            && block_toks.get(i + 1) == Some(&":=")
            && (i == 0 || !matches!(block_toks[i - 1], "let" | "have"));
        let allowed = tok == ":="
            || tok == "\"\""
            || tok.bytes().all(|b| b.is_ascii_digit())
            || matches!(tok, "true" | "false" | "some" | "none")
            || is_valid_field
            || is_mir_vocab_ctor(tok);
        (!allowed).then(|| tok.to_string())
    })
}

/// `true` when `tok` heads a `RigidTy` (`.uint`, `RigidTy.ref`, ...).
fn is_rigid_ty_head(tok: &str) -> bool {
    ast_ctor(tok, "RigidTy").is_some_and(|ctor| RIGID_TY_CTORS.contains(&ctor))
}

/// `true` when `tok` is a `Mutability` constructor (`.not`, `Mutability.mut`, ...).
fn is_mutability_tok(tok: &str) -> bool {
    matches!(ast_ctor(tok, "Mutability"), Some("not" | "mut"))
}

/// The shorthand `.ref` at `toks[i]` is `Rvalue.ref <BorrowKind> <Place>` unless
/// it is a `RigidTy.ref <Mutability> <RigidTy>` type annotation. `.mut` is
/// ambiguous between `BorrowKind.mut <Bool>` and `Mutability.mut`, so it is
/// resolved by its successor: a `RigidTy` head means a type.
fn shorthand_ref_is_rvalue(toks: &[&str], i: usize) -> bool {
    let Some(&next) = toks.get(i + 1) else {
        return false;
    };
    if next == ".shared" || is_qualified_ctor(next, "BorrowKind", "shared") {
        return true;
    }
    if next == ".mut" {
        return !toks.get(i + 2).is_some_and(|t| is_rigid_ty_head(t));
    }
    if next == ".not" || is_qualified_ctor(next, "Mutability", "not") || is_qualified_ctor(next, "Mutability", "mut") {
        return false;
    }
    // Fail closed on anything else (e.g. `.ref (BorrowKind.mut b) p`).
    true
}

/// Detect `Rvalue.ref` without false-triggering on `RigidTy.ref` type
/// annotations or on `Mutability.mut` written as the shorthand `.mut`.
fn detect_rvalue_ref(toks: &[&str]) -> bool {
    toks.iter().enumerate().any(|(i, &tok)| {
        is_qualified_ctor(tok, "Rvalue", "ref")
            || is_qualified_ctor(tok, "BorrowKind", "shared")
            || is_qualified_ctor(tok, "BorrowKind", "mut")
            || (tok == ".ref" && shorthand_ref_is_rvalue(toks, i))
    })
}

/// Detect an exclusive `BorrowKind.mut` borrow (`Rvalue.ref (.mut b) p`)
/// without confusing `Mutability.mut` (`&mut T` / `*mut T` types, raw
/// pointers, or `AggregateKind.rawPtr _ .mut`).
fn detect_mut_borrow(toks: &[&str]) -> bool {
    toks.iter().enumerate().any(|(i, &tok)| {
        if is_qualified_ctor(tok, "BorrowKind", "mut") {
            return true;
        }
        let qualified_ref = is_qualified_ctor(tok, "Rvalue", "ref");
        (qualified_ref || tok == ".ref")
            && toks.get(i + 1) == Some(&".mut")
            && (qualified_ref || !toks.get(i + 2).is_some_and(|t| is_rigid_ty_head(t)))
    })
}

/// Detect `Rvalue.rawPtr <Mutability> <Place>` without false-triggering on
/// `RigidTy.rawPtr <Mutability> <RigidTy>` types or the pure
/// `AggregateKind.rawPtr <Ty> <Mutability>` pointer-from-parts aggregate.
fn detect_rvalue_raw_ptr(toks: &[&str]) -> bool {
    toks.iter().enumerate().any(|(i, &tok)| {
        if is_qualified_ctor(tok, "Rvalue", "rawPtr") {
            return true;
        }
        if tok != ".rawPtr" {
            return false;
        }
        let Some(&first) = toks.get(i + 1) else {
            return false;
        };
        if matches!(first, "kind" | "layoutIdx") && toks.get(i + 2) == Some(&":=") {
            // `AggregateKind.rawPtr { kind := .., layoutIdx := .. } <Mutability>`.
            return false;
        }
        if is_mutability_tok(first) {
            return !toks.get(i + 2).is_some_and(|t| is_rigid_ty_head(t));
        }
        // Fail closed on anything else.
        true
    })
}

/// Detect `NonDivergingIntrinsic.copyNonOverlapping` (qualified or
/// `.copyNonOverlapping`), failing closed on any `StatementKind.intrinsic`
/// whose operand is not visibly `NonDivergingIntrinsic.assume`.
fn detect_copy_non_overlapping(toks: &[&str]) -> bool {
    toks.iter().enumerate().any(|(i, &tok)| {
        if ast_ctor(tok, "NonDivergingIntrinsic") == Some("copyNonOverlapping") {
            return true;
        }
        ast_ctor(tok, "StatementKind") == Some("intrinsic")
            && !toks
                .get(i + 1)
                .is_some_and(|t| ast_ctor(t, "NonDivergingIntrinsic") == Some("assume"))
    })
}

/// Detect pointer-backed `ConstValue.slice (ConstScalar.ptr ...)` (which reads
/// global allocation memory, unlike `ConstValue.slice (ConstScalar.int ...)`).
fn detect_const_slice_ptr(toks: &[&str]) -> bool {
    toks.windows(2).any(|w| {
        ast_ctor(w[0], "ConstValue") == Some("slice") && ast_ctor(w[1], "ConstScalar") == Some("ptr")
    })
}

fn count_field_assign(block_toks: &[&str], field: &str) -> usize {
    block_toks
        .windows(2)
        .filter(|w| w[0] == field && w[1] == ":=")
        .count()
}

fn detect_blocks_and_back_edges(
    norm_blocks: &str,
    block_toks: &[&str],
) -> (usize, bool, Option<String>) {
    let parts: Vec<&str> = norm_blocks.split(" terminator := ").collect();
    let term_count = parts.len().saturating_sub(1);
    let stmt_count = count_field_assign(block_toks, "statements");
    let cleanup_count = count_field_assign(block_toks, "isCleanup");
    let is_empty_list = block_toks.is_empty()
        || (block_toks.len() == 1
            && ast_ctor(block_toks[0], "List") == Some("nil"));

    if term_count == 0 {
        if is_empty_list {
            return (0, false, None);
        }
        return (
            0,
            true,
            Some("missing `terminator :=` in non-empty basicBlocks".to_string()),
        );
    }
    if stmt_count != term_count || cleanup_count != term_count {
        return (
            term_count,
            true,
            Some("mismatched BasicBlockData fields in basicBlocks".to_string()),
        );
    }

    let mut back_edge = false;
    let mut malformed = None;
    for (bb_idx, raw_part) in parts.iter().skip(1).enumerate() {
        let padded = format!(" {raw_part} ");
        let end = padded
            .find(" isCleanup := ")
            .into_iter()
            .chain(padded.find(" statements := "))
            .min()
            .unwrap_or(padded.len());
        let term = padded[..end].replace(" span := \"\" ", " ");
        match extract_terminator_targets(&term) {
            Some(targets) => {
                for target in targets {
                    if target <= bb_idx {
                        back_edge = true;
                    }
                }
            }
            None => {
                back_edge = true;
                if malformed.is_none() {
                    malformed = Some(format!("malformed terminator in bb{bb_idx}"));
                }
            }
        }
    }
    (term_count, back_edge, malformed)
}

fn is_unwind_action_tok(tok: &str) -> bool {
    matches!(
        ast_ctor(tok, "UnwindAction"),
        Some("cleanup" | "unreachable" | "terminate" | "continue_")
    )
}

fn is_unwind_cleanup_tok(tok: &str) -> bool {
    ast_ctor(tok, "UnwindAction") == Some("cleanup")
}

fn extract_terminator_targets(norm_term: &str) -> Option<Vec<usize>> {
    let tokens: Vec<&str> = norm_term.split_whitespace().collect();
    let mut targets = Vec::new();

    // Locate the terminator constructor after `kind :=` (must be present on `Terminator`).
    let kind_pos = tokens
        .windows(2)
        .position(|w| w[0] == "kind" && w[1] == ":=")
        .map(|p| p + 2)?;
    let &head_tok = tokens.get(kind_pos)?;
    // Accept `.goto`, `TerminatorKind.goto`, and fully-qualified
    // `Trusted.Rustc.V2026_06_01.MirAst.TerminatorKind.goto` heads alike.
    let head = ast_ctor(head_tok, "TerminatorKind")?;

    if matches!(
        head,
        "return_" | "unreachable" | "unwindResume" | "unwindTerminate" | "tailCall"
    ) {
        return Some(targets);
    }

    if head == "goto" {
        let n = tokens
            .get(kind_pos + 1)
            .and_then(|s| s.parse::<usize>().ok())?;
        targets.push(n);
        return Some(targets);
    }

    if head == "switchInt" {
        let br_idx = norm_term.find("branches :=")?;
        let after_br = &norm_term[br_idx + "branches :=".len()..];
        let br_end = after_br.find("otherwise :=").unwrap_or(after_br.len());
        // Switch branch discriminants are `u128` bit patterns (`0..=u128::MAX`);
        // parsing both elements as `u128` keeps `(val, target_bb)` pairs aligned
        // even when `val > usize::MAX`.
        let nums: Vec<u128> = after_br[..br_end]
            .split_whitespace()
            .filter_map(|t| t.parse::<u128>().ok())
            .collect();
        if nums.len() % 2 != 0 {
            return None;
        }
        for pair in nums.chunks_exact(2) {
            let target_bb = usize::try_from(pair[1]).ok()?;
            targets.push(target_bb);
        }
        let mut found_otherwise = false;
        for i in kind_pos..tokens.len() {
            if tokens[i] == "otherwise" && tokens.get(i + 1) == Some(&":=") {
                let n = tokens.get(i + 2).and_then(|s| s.parse::<usize>().ok())?;
                targets.push(n);
                found_otherwise = true;
            }
        }
        return found_otherwise.then_some(targets);
    }

    // `drop`, `assert`, `call`, and `inlineAsm` all end with `UnwindAction`
    // right before `span :=`. Anchoring on that trailing `UnwindAction` avoids
    // false matches on inner `Option.some` or boolean literals inside operands.
    let u = (kind_pos + 1..tokens.len())
        .rev()
        .find(|&i| is_unwind_action_tok(tokens[i]))?;

    if head == "drop" || head == "assert" {
        if u <= kind_pos {
            return None;
        }
        let n = tokens.get(u - 1).and_then(|s| s.parse::<usize>().ok())?;
        targets.push(n);
        if is_unwind_cleanup_tok(tokens[u]) {
            let cleanup_bb = tokens.get(u + 1).and_then(|s| s.parse::<usize>().ok())?;
            targets.push(cleanup_bb);
        }
        return Some(targets);
    } else if head == "call" {
        if u < kind_pos + 1 {
            return None;
        }
        if tokens[u - 1] == "none" || ast_ctor(tokens[u - 1], "Option") == Some("none") {
            // Diverging call (`target := none`).
        } else if u >= kind_pos + 2
            && (tokens[u - 2] == "some" || ast_ctor(tokens[u - 2], "Option") == Some("some"))
        {
            let n = tokens.get(u - 1).and_then(|s| s.parse::<usize>().ok())?;
            targets.push(n);
        } else {
            return None;
        }
        if is_unwind_cleanup_tok(tokens[u]) {
            let cleanup_bb = tokens.get(u + 1).and_then(|s| s.parse::<usize>().ok())?;
            targets.push(cleanup_bb);
        }
        return Some(targets);
    } else if head == "inlineAsm" {
        for tok in &tokens[kind_pos + 1..u] {
            if tok.bytes().all(|b| b.is_ascii_digit()) {
                targets.push(tok.parse::<usize>().ok()?);
            }
        }
        if is_unwind_cleanup_tok(tokens[u]) {
            let cleanup_bb = tokens.get(u + 1).and_then(|s| s.parse::<usize>().ok())?;
            targets.push(cleanup_bb);
        }
        return Some(targets);
    }

    None
}

/// Render 80-column-wrapped `--` Lean comment hints recommending the fuel-free
/// proof lifting strategy for `bundle`, `authored`, and `profile`.
///
/// Emits pure `--` line comments compatible with `TrustedBoundary.lean` and
/// stripped by `detect_authored_item_modules` and `check_specs_non_vacuous`.
pub fn render_scaffold_lifting_hints(
    bundle: &SubjectObligationBundle,
    authored: AuthoredItemModules,
    profile: &MirLiftingProfile,
) -> String {
    let effective = effective_authored_for_bundle(bundle, authored, Some(profile));
    let is_equiv = effective.is_equiv;
    let is_modular = effective.is_modular;
    let is_polymorphic = effective.is_polymorphic;
    let is_bit_validity_item = matches!(
        bundle.subject.item_kind,
        anneal_rustc_capture::CapturedItemKind::TypeInvariant
            | anneal_rustc_capture::CapturedItemKind::UnsafeTraitImpl
    );
    let mut bullets: Vec<String> = Vec::new();

    if is_bit_validity_item {
        bullets.push(
            "Bit-validity (`open Anneal.BitValidity`): use `ValidityMode`, \
             `ByteSeqValid`, `IsUnaligned`, `IsFromZeros`, `IsFromBytes`, \
             `IsIntoBytes`, `IsTryFromBytes`, `checkUnaligned_sound`, \
             `checkFromZeros_sound`, `checkFromBytes_sound`, \
             `checkIntoBytes_sound`, and \
             `transmute_sound_of_into_from_bytes` over `Mir.<Item>.layouts`."
                .to_string(),
        );
    }

    if is_polymorphic {
        bullets.push(
            "Polymorphic MIR (`open Trusted.MirAst Anneal.PureMirExec \
             Anneal.MirLiftCore`; plus `Anneal.SepLogicLenses` or \
             `Anneal.MirFuelFree` for stateful/loop bodies): `intro typeArgs \
             h_len` on `poly*Claim`, where `*ClaimFor typeArgs` instantiates \
             `Mir.<Item>.body.instantiate typeArgs` (`CapturedMir.instantiate` \
             and `LayoutTable.instantiateForBody`), then discharge `*ClaimFor \
             typeArgs` with fuel-free lifting theorems \
             (`verifyMirNoPanic_of_pureExec`, \
             `verifyStatefulMir_of_sepLenses`, or \
             `verifyStatefulMirNoPanic_of_wpConverges`)."
                .to_string(),
        );
    }

    if profile.has_cfg_back_edge {
        bullets.push(
            "Loops (`open Anneal.MirLoops Anneal.PureMirExec \
             Anneal.MirFuelFree`): model bounded loops with `forRangeUp` \
             (`forRangeUp_induction`, `mirWpConverges_forRangeUp`, \
             `mirNoCallWpConverges_forRangeUp`, or \
             `mirWpConverges_whileRank`) and step entry, body, and exit via \
             `runCfgToBlock` (`mirStepsConverges_of_runCfgToBlock`, \
             `mirNoCallWpConverges_of_runCfgToBlock`) without step numerals."
                .to_string(),
        );
    }

    if profile.has_mut_borrow {
        bullets.push(
            "References (`open Anneal.SepLogicLenses \
             Anneal.FunctionalTranslation Anneal.MirLiftCore`): erase `&mut` \
             borrow/heap aliasing via `SepLensStateInv` \
             (`ActiveTypedMutBorrow`) or sibling-field \
             `SepSubplaceLensStateInv` (`ActiveTypedFieldMutBorrow`), derive \
             `LiftLensBlock` (`set?_of_forcePureEnv? rfl`), and close with \
             `verifyStatefulMir_of_sepLenses` or \
             `verifyStatefulMir_of_sepSubplaceLenses`."
                .to_string(),
        );
    } else if profile.has_deref_projection {
        bullets.push(
            "Shared `&` / pointer reads (`open Anneal.PureMirExec \
             Anneal.MirFuelFree Anneal.Rustc.V2026_06_01.SymbolicEval`): \
             `ActiveTypedMutBorrow` requires `&mut` borrows; step read-only \
             dereferences via `runCfgToBlock` (`mirWpConverges_of_runCfgToBlock`, \
             `verifyStatefulMirNoPanic_of_wpConverges`) or \
             `dischargeStatefulEqFuelFree` on concrete pinned memory."
                .to_string(),
        );
    }

    if is_modular || profile.has_callees_or_modular_contracts || profile.has_call_terminator {
        bullets.push(
            "Callees / modular (`open Anneal.PureMirExec`): for linked pure \
             callees use `checkPureMirWithCallees` with \
             `verifyStatefulMirNoPanic_of_pureExecWithCallees_any` or \
             `PureMirConverges.call_summary`; for modular call contracts use \
             `PureMirModularConverges` and \
             `verifyModularMir_of_pureModularExec_any`."
                .to_string(),
        );
    }

    if profile.is_pure_call_free_candidate() && !profile.has_cfg_back_edge && !is_modular {
        bullets.push(
            "Pure MIR (`#mir_lift` rules; `open Anneal.PureMirExec \
             Anneal.MirLiftCore`): apply `verifyMirNoPanic_of_pureExec` (or \
             `verifyTotalMir_of_pureExec` / \
             `verifyStatefulMirNoPanic_of_pureExec`), \
             `lift_PureMirConverges (by rfl)`, `LiftBlock.of_lookup (by rfl)`, \
             and `LiftStmtsTerminator.{cons_eval, cons_eval_norm, eval_rest, \
             term_assert, term_switchInt, term_goto, term_drop, term_return}`."
                .to_string(),
        );
    } else if !profile.has_captured_mir {
        bullets.push(
            "Body lifting (`#mir_lift` / `forRangeUp` / `SepLogicLenses`): \
             check `Anneal.PureMirExec.checkPureMir` first (`*_of_pureExec` + \
             `LiftBlock` / `LiftStmtsTerminator`); use `Anneal.MirLoops` \
             (`forRangeUp` + `runCfgToBlock`) on loops and \
             `Anneal.SepLogicLenses` (`LiftLensBlock`) on `&mut` borrows."
                .to_string(),
        );
    }

    if is_equiv {
        bullets.push(
            "Equivalence (`#[spec(equivalent_to: ...)]`; `open \
             Anneal.PureMirExec Anneal.MirFuelFree`): discharge \
             `StatefulEquivVerificationResult` with \
             `verifyStatefulEquivMir_of_wpConverges` and \
             `mirNoCallWpConverges_of_runCfgToBlock`, reusing the reference \
             specification's `MirNoCallWpConverges` theorem."
                .to_string(),
        );
    }

    if effective.is_ub_exception {
        bullets.push(
            "Scoped UB-exception (`open Anneal.PureMirExec \
             Anneal.MirFuelFree`): discharge `UbExceptionVerificationResult` \
             via `verifyUbExceptionMir_of_wpConverges` and \
             `mirWpConverges_of_runCfgToBlock`."
                .to_string(),
        );
    }

    if profile.has_inline_companions {
        if profile.has_impure_inline_companions {
            bullets.push(
                "Companion specs (`#mir_lift_spec` / closure-upvar fallback; \
                 `open Anneal.PureMirExec`): inline companions capture `&` \
                 upvars (`checkPureMir = false`); invert `requires` via \
                 `holdBoolReq_of_mirBool` with count-free `repeat`, prove \
                 `ensures` via `hold_mirBool_of_blockLinear` \
                 (`defaultSpecSteps`), or lift pure companions via \
                 `mirBoolPredicateHolds_elim_of_pureExec`."
                    .to_string(),
            );
        } else {
            bullets.push(
                "Companion specs (`#mir_lift_spec` theorems; `open \
                 Anneal.PureMirExec`): when `checkPureMir` holds on a \
                 companion, use `mirBoolPredicateHolds_of_pureExec` and \
                 `mirBoolPredicateHolds_elim_of_pureExec`; if closure `&` \
                 upvars make `checkPureMir = false`, use \
                 `holdBoolReq_of_mirBool` (with `repeat`) and \
                 `hold_mirBool_of_blockLinear` (`defaultSpecSteps`)."
                    .to_string(),
            );
        }
    }

    bullets.push(
        "Boundary rule: `#mir_lift` (`Anneal.MirLift`, emitting \
         `<item>_model`, `<item>_lift_sound`, and `<item>_verified`, or \
         `LiftResidualBlock` under `residual := true`) is a closed-body \
         (`argCount = 0`) elaborator outside `TrustedBoundary`; in \
         `Proof/*.lean`, apply `Anneal` theorems directly with zero \
         `BlockCtx` records and zero manual fuel or `iterate k` counts."
            .to_string(),
    );

    let mut out =
        String::from("-- Proof lifting strategy hints (lift first, evaluate last):\n");
    for bullet in &bullets {
        out.push_str(&wrap_lean_line_comment("-- * ", "--   ", bullet, 80));
    }
    out
}

fn wrap_lean_line_comment(
    first_prefix: &str,
    cont_prefix: &str,
    text: &str,
    max_cols: usize,
) -> String {
    let mut out = String::new();
    let mut cur_prefix = first_prefix;
    let mut line = String::from(cur_prefix);

    for word in text.split_whitespace() {
        let base_len = cur_prefix.chars().count();
        let cur_len = line.chars().count();
        let word_len = word.chars().count();
        if cur_len == base_len {
            line.push_str(word);
        } else if cur_len + 1 + word_len <= max_cols {
            line.push(' ');
            line.push_str(word);
        } else {
            out.push_str(&line);
            out.push('\n');
            cur_prefix = cont_prefix;
            line = String::from(cur_prefix);
            line.push_str(word);
        }
    }
    if line.chars().count() > cur_prefix.chars().count() {
        out.push_str(&line);
        out.push('\n');
    }
    out
}

/// Render a context-aware starter `anneal/proofs/Proof/<Item>.lean` template
/// enriched with 80-column-wrapped `--` lifting strategy hints derived from
/// `profile`.
pub fn render_proof_template_with_hints(
    bundle: &SubjectObligationBundle,
    authored: AuthoredItemModules,
    profile: &MirLiftingProfile,
) -> String {
    let effective = effective_authored_for_bundle(bundle, authored, Some(profile));
    let base = render_proof_template_with_options(bundle, effective);
    let hints = render_scaffold_lifting_hints(bundle, effective, profile);
    if let Some(doc_idx) = base.find("\n/-- ") {
        let mut enriched = String::with_capacity(base.len() + hints.len() + 2);
        enriched.push_str(&base[..doc_idx + 1]);
        enriched.push_str(&hints);
        enriched.push('\n');
        enriched.push_str(&base[doc_idx + 1..]);
        enriched
    } else {
        format!("{hints}\n{base}")
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

    #[test]
    fn scaffold_init_proofs_surfaces_tailored_lifting_hints_within_80_cols() {
        let workspace = unique_temp_dir("lifting-hints");
        let unit_dir = workspace.join("target/anneal/units/my_crate-01");
        fs::create_dir_all(unit_dir.join("Mir/MyCrate")).expect("create Mir/MyCrate");

        // 1. Pure scalar function with an impure closure-capturing companion.
        let pure_mir = r#"import Trusted
namespace Mir.MyCrate.pure_add
def body : CapturedMir :=
  {
    defPath := "my_crate::pure_add",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := List.nil,
    basicBlocks := (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.goto 1), span := "ProjectionElem.deref" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.return_, span := "" }, isCleanup := false } List.nil)),
    fnAbi := dummyAbi,
    layouts := layouts,
    allocations := List.nil
  }
end Mir.MyCrate.pure_add
"#;
        let comp_mir = r#"import Trusted
namespace Mir.MyCrate.__anodized_fn_requires_pure_add
def body : CapturedMir :=
  {
    defPath := "my_crate::__anodized_fn_requires_pure_add",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.requires,
    argCount := 2,
    localDecls := List.nil,
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 1, projection := List.nil })), span := "" } List.nil), terminator := { kind := TerminatorKind.return_, span := "" }, isCleanup := false } List.nil),
    fnAbi := dummyAbi,
    layouts := layouts,
    allocations := List.nil
  }
end Mir.MyCrate.__anodized_fn_requires_pure_add
"#;

        // 2. Mutable-borrow function (`RigidTy.ref Mutability.mut` + `ProjectionElem.deref`).
        let lens_mir = r#"import Trusted
namespace Mir.MyCrate.bump_cursor
def body : CapturedMir :=
  {
    defPath := "my_crate::bump_cursor",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.uint UintTy.u16)), layoutIdx := 0 }, debugName := Option.none } List.nil),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 1, projection := (List.cons ProjectionElem.deref List.nil) } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref List.nil) }))), span := "" } List.nil), terminator := { kind := TerminatorKind.return_, span := "" }, isCleanup := false } List.nil),
    fnAbi := dummyAbi,
    layouts := layouts,
    allocations := List.nil
  }
end Mir.MyCrate.bump_cursor
"#;

        // 3. Loop function with CFG back-edge (`bb0 -> bb1 -> bb2 -> bb1`).
        let loop_mir = r#"import Trusted
namespace Mir.MyCrate.sum_loop
def body : CapturedMir :=
  {
    defPath := "my_crate::sum_loop",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 1,
    localDecls := List.nil,
    basicBlocks := (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.goto 1), span := "" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.switchInt (Operand.copy { local_ := 1, projection := List.nil }) { branches := (List.cons (0, 3) List.nil), otherwise := 2 }), span := "" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.goto 1), span := "" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.return_, span := "" }, isCleanup := false } List.nil)))),
    fnAbi := dummyAbi,
    layouts := layouts,
    allocations := List.nil
  }
end Mir.MyCrate.sum_loop
"#;

        for (rel, txt) in [
            ("Mir/MyCrate/pure_add.lean", pure_mir),
            ("Mir/MyCrate/__anodized_fn_requires_pure_add.lean", comp_mir),
            ("Mir/MyCrate/bump_cursor.lean", lens_mir),
            ("Mir/MyCrate/sum_loop.lean", loop_mir),
        ] {
            fs::write(unit_dir.join(rel), txt).expect("write synthetic mir");
        }

        let rec = |def_id: &str, rel: &str, module: &str, kind, assoc: Option<&str>| {
            let hash = sha256_hex(
                fs::read_to_string(unit_dir.join(rel))
                    .expect("read mir")
                    .as_bytes(),
            );
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: def_id.to_string(),
                    mir_module_path: rel.to_string(),
                    mir_module_sha256: hash,
                },
                lean_module_name: module.to_string(),
                item_kind: kind,
                associated_subject_def_id: assoc.map(str::to_string),
                trait_impls: Vec::new(),
            }
        };

        let records = vec![
            rec(
                "my_crate::pure_add",
                "Mir/MyCrate/pure_add.lean",
                "Mir.MyCrate.pure_add",
                CapturedItemKind::Subject,
                None,
            ),
            rec(
                "my_crate::__anodized_fn_requires_pure_add",
                "Mir/MyCrate/__anodized_fn_requires_pure_add.lean",
                "Mir.MyCrate.__anodized_fn_requires_pure_add",
                CapturedItemKind::InlineSpecRequires,
                Some("my_crate::pure_add"),
            ),
            rec(
                "my_crate::bump_cursor",
                "Mir/MyCrate/bump_cursor.lean",
                "Mir.MyCrate.bump_cursor",
                CapturedItemKind::Subject,
                None,
            ),
            rec(
                "my_crate::sum_loop",
                "Mir/MyCrate/sum_loop.lean",
                "Mir.MyCrate.sum_loop",
                CapturedItemKind::Subject,
                None,
            ),
        ];

        let cfg = ScaffoldConfig::new(&workspace);
        scaffold_init_proof_templates(&cfg, &records).expect("init proof templates with hints");

        let pure_proof = fs::read_to_string(workspace.join("anneal/proofs/Proof/MyCrate/pure_add.lean"))
            .expect("read pure_add proof");
        assert!(pure_proof.contains("#mir_lift"));
        assert!(pure_proof.contains("verifyMirNoPanic_of_pureExec"));
        assert!(pure_proof.contains("#mir_lift_spec"));
        assert!(pure_proof.contains("holdBoolReq_of_mirBool"));
        assert!(!pure_proof.contains("SepLogicLenses"));

        let lens_proof =
            fs::read_to_string(workspace.join("anneal/proofs/Proof/MyCrate/bump_cursor.lean"))
                .expect("read bump_cursor proof");
        assert!(lens_proof.contains("Anneal.SepLogicLenses"));
        assert!(lens_proof.contains("Anneal.FunctionalTranslation"));
        assert!(lens_proof.contains("verifyStatefulMir_of_sepLenses"));

        let loop_proof = fs::read_to_string(workspace.join("anneal/proofs/Proof/MyCrate/sum_loop.lean"))
            .expect("read sum_loop proof");
        assert!(loop_proof.contains("forRangeUp"));
        assert!(loop_proof.contains("runCfgToBlock"));

        for (name, proof_src) in [
            ("pure_add", &pure_proof),
            ("bump_cursor", &lens_proof),
            ("sum_loop", &loop_proof),
        ] {
            for line in proof_src.lines().filter(|l| l.starts_with("--")) {
                assert!(
                    line.chars().count() <= 80,
                    "comment line in {name} exceeded 80 cols ({}): {line}",
                    line.chars().count()
                );
            }
            let detected = detect_authored_item_modules(
                &workspace.join("anneal/proofs"),
                Path::new(&format!("MyCrate/{name}.lean")),
            );
            assert!(
                !detected.is_stateful && !detected.is_modular && !detected.is_equiv,
                "hint comments in {name} must not trigger false contract detection: {detected:?}"
            );
        }

        let _ = fs::remove_dir_all(&workspace);
    }

    #[test]
    fn mir_lifting_profile_handles_strings_slice_ptrs_u128_and_cleanup() {
        let mk_bundle = |def_id: &str, kind: CapturedItemKind| SubjectObligationBundle {
            subject: UnitTargetRecord {
                target: CapturedTarget {
                    def_id: def_id.to_string(),
                    mir_module_path: "Mir/Demo/item.lean".to_string(),
                    mir_module_sha256: "0".repeat(64),
                },
                lean_module_name: "Mir.Demo.item".to_string(),
                item_kind: kind,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            },
            item_module_suffix: "Demo.item".to_string(),
            item_rel_path: PathBuf::from("Demo/item.lean"),
            inline_requires: Vec::new(),
            inline_ensures: Vec::new(),
            inline_qualifiers: Vec::new(),
            external_specs: Vec::new(),
            transitive_callees: Vec::new(),
            external_spec_callees: Vec::new(),
            called_callees: Vec::new(),
            spec_callees: Vec::new(),
            spec_companions_with_calls: BTreeSet::new(),
        };

        // 1. `"--"` and `"/-"` inside `span` string literals must NOT invert quote
        //    polarity and blind `scan_captured_mir_body` to `ProjectionElem.deref`.
        let str_comment_mir = r#"import Trusted
def body : CapturedMir :=
  {
    defPath := "demo::str_--_/-_item",
    localDecls := List.nil,
    basicBlocks := (List.cons {
      statements := (List.cons {
        kind := (StatementKind.assign { local_ := 0, projection := List.nil }
          (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref List.nil) }))),
        span := "src/foo--bar.rs:1:1"
      } List.nil),
      terminator := { kind := TerminatorKind.return_, span := "src/a/-b.rs:2:1" },
      isCleanup := false
    } List.nil),
    allocations := List.nil
  }
"#;
        let prof_str =
            analyze_mir_lifting_profile(&mk_bundle("demo::item", CapturedItemKind::Subject), Some(str_comment_mir), &[]);
        assert!(
            prof_str.has_deref_projection && !prof_str.is_pure_call_free_candidate(),
            "comment tokens inside string literals must not hide ProjectionElem.deref"
        );
        assert!(
            !prof_str.has_mut_borrow,
            "shared deref without &mut must not set has_mut_borrow"
        );

        let shared_hints = render_scaffold_lifting_hints(
            &mk_bundle("demo::item", CapturedItemKind::Subject),
            AuthoredItemModules::default(),
            &prof_str,
        );
        assert!(shared_hints.contains("Shared `&` / pointer reads"));
        assert!(!shared_hints.contains("verifyStatefulMir_of_sepLenses"));

        // 2. Pointer-backed `ConstValue.slice (ConstScalar.ptr ...)` fails `checkPureMir`,
        //    whereas `ConstValue.slice (ConstScalar.int ...)` and nested compound types
        //    (`{ kind := .tuple [.ref .not ...], ... }` / `AggregateKind.rawPtr`) remain pure.
        let slice_ptr_mir = r#"def body : CapturedMir := {
            localDecls := List.nil,
            basicBlocks := (List.cons {
              statements := (List.cons {
                kind := (StatementKind.assign { local_ := 0, projection := List.nil }
                  (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.ref Mutability.not RigidTy.str), layoutIdx := 0 }, val := (ConstValue.slice (ConstScalar.ptr { allocId := 1, offsetBytes := 0 } 8) 5) }))),
                span := ""
              } List.nil),
              terminator := { kind := TerminatorKind.return_, span := "" },
              isCleanup := false
            } List.nil)
          }"#;
        let prof_slice_ptr = analyze_mir_lifting_profile(
            &mk_bundle("demo::slice_ptr", CapturedItemKind::Subject),
            Some(slice_ptr_mir),
            &[],
        );
        assert!(
            prof_slice_ptr.has_impure_rvalue_or_asm && !prof_slice_ptr.is_pure_call_free_candidate(),
            "ConstValue.slice (ConstScalar.ptr ...) must be classified as impure"
        );

        let pure_nested_ty_mir = r#"def body : CapturedMir := {
            localDecls := List.nil,
            basicBlocks := [
              { statements := [
                  { kind := .assign { local_ := 0, projection := [.field 0 { kind := .tuple [.ref .not (.uint .u32)], layoutIdx := 1 }] }
                      (.aggregate (.rawPtr { kind := .uint .u8, layoutIdx := 0 } .not) []),
                    span := "" }
                ],
                terminator := {
                  kind := .switchInt (.copy { local_ := 1, projection := [.subslice 0 1 false] })
                    { branches := [(340282366920938463463374607431768211455, 1), (0, 1)], otherwise := 1 },
                  span := ""
                },
                isCleanup := false },
              { statements := [],
                terminator := {
                  kind := .assert (.copy { local_ := 1, projection := [.constantIndex 0 1 false] }) true 2 .unreachable,
                  span := ""
                },
                isCleanup := false },
              { statements := [],
                terminator := { kind := .return_, span := "" },
                isCleanup := false }
            ]
          }"#;
        let prof_nested = analyze_mir_lifting_profile(
            &mk_bundle("demo::nested", CapturedItemKind::Subject),
            Some(pure_nested_ty_mir),
            &[],
        );
        assert!(
            prof_nested.is_pure_call_free_candidate(),
            "nested RigidTy.ref and AggregateKind.rawPtr must remain pure: {prof_nested:?}"
        );
        assert!(
            !prof_nested.has_cfg_back_edge,
            "u128::MAX switch arm (u128::MAX, 1) followed by (0, 1) and assert subslice/constantIndex must not invent a back-edge"
        );

        // 3. `u128::MAX` switch arm jumping back to `bb0` IS detected as a back-edge,
        //    and `TypeInvariant` surfaces `Anneal.BitValidity` within 80 columns.
        let u128_backedge_mir = r#"def body : CapturedMir := {
            localDecls := List.nil,
            basicBlocks := [
              { statements := [],
                terminator := {
                  kind := .switchInt (.copy { local_ := 1, projection := [] })
                    { branches := [(340282366920938463463374607431768211455, 0)], otherwise := 1 },
                  span := ""
                },
                isCleanup := false },
              { statements := [], terminator := { kind := .return_, span := "" }, isCleanup := false }
            ]
          }"#;
        let inv_bundle = mk_bundle("demo::__anneal_type_invariant_hdr", CapturedItemKind::TypeInvariant);
        let prof_u128_loop = analyze_mir_lifting_profile(&inv_bundle, Some(u128_backedge_mir), &[]);
        assert!(prof_u128_loop.has_cfg_back_edge);
        let inv_hints =
            render_scaffold_lifting_hints(&inv_bundle, AuthoredItemModules::default(), &prof_u128_loop);
        assert!(inv_hints.contains("Anneal.BitValidity"));
        assert!(inv_hints.contains("open Anneal.MirLoops Anneal.PureMirExec"));
        assert!(inv_hints.contains("Anneal.MirFuelFree"));
        for line in inv_hints.lines() {
            assert!(line.chars().count() <= 80, "line > 80 cols: {line}");
        }

        // 4. Non-inline `def body : CapturedMir := aliasBody` (no `basicBlocks :=`)
        //    must NOT be misclassified as a 0-block pure candidate.
        let alias_body_mir = "import Trusted\ndef body : CapturedMir := otherBody\n";
        let prof_alias = analyze_mir_lifting_profile(
            &mk_bundle("demo::alias", CapturedItemKind::Subject),
            Some(alias_body_mir),
            &[],
        );
        assert!(
            !prof_alias.has_captured_mir && !prof_alias.is_pure_call_free_candidate(),
            "non-inline alias CapturedMir must not report has_captured_mir: {prof_alias:?}"
        );

        // 5. `UnwindAction.cleanup 0` on `assert` and `typeParamCount := 2` are detected,
        //    and maximal `AuthoredItemModules` combinations respect `<= 80` cols and
        //    ground-truth namespaces.
        let cleanup_poly_mir = r#"def body : CapturedMir := {
            typeParamCount := 2,
            localDecls := [],
            basicBlocks := [
              { statements := [],
                terminator := { kind := .assert (.copy { local_ := 1, projection := [] }) true 1 (.cleanup 0), span := "" },
                isCleanup := false },
              { statements := [], terminator := { kind := .return_, span := "" }, isCleanup := false }
            ]
          }"#;
        let poly_bundle = mk_bundle("demo::poly_cleanup", CapturedItemKind::Subject);
        let mut prof_poly = analyze_mir_lifting_profile(&poly_bundle, Some(cleanup_poly_mir), &[]);
        assert_eq!(prof_poly.type_param_count, 2);
        assert!(
            prof_poly.has_cfg_back_edge,
            "UnwindAction.cleanup 0 on bb0 must register as a CFG back-edge"
        );
        prof_poly.has_inline_companions = true;
        prof_poly.has_impure_inline_companions = true;
        prof_poly.has_deref_projection = true;
        let max_authored = AuthoredItemModules {
            is_equiv: true,
            is_ub_exception: true,
            is_polymorphic: true,
            ..AuthoredItemModules::default()
        };
        let max_hints = render_scaffold_lifting_hints(&poly_bundle, max_authored, &prof_poly);
        assert!(max_hints.contains("CapturedMir.instantiate"));
        assert!(max_hints.contains("open Trusted.MirAst Anneal.PureMirExec"));
        assert!(!max_hints.contains("Trusted.Layout"));
        assert!(!max_hints.contains("Body.instantiate"));
        assert!(!max_hints.contains("verifyPoly"));
        assert!(max_hints.contains("#[spec(equivalent_to: ...)]"));
        assert!(!max_hints.contains("#[spec(equiv ="));
        assert!(max_hints.contains("verifyStatefulEquivMir_of_wpConverges"));
        assert!(max_hints.contains("verifyUbExceptionMir_of_wpConverges"));
        assert!(max_hints.contains("<item>_lift_sound"));
        for line in max_hints.lines() {
            assert!(line.chars().count() <= 80, "line > 80 cols: {line}");
        }

        // 6. An unused `&mut` local without `.deref` or `BorrowKind.mut` stays pure
        //    (`has_mut_borrow == false`), and `analyze_workspace_lifting_profile`
        //    falls back to `target/anneal/units` before `.anneal/generated/Mir` exists.
        let unused_mut_mir = r#"def body : CapturedMir := {
            localDecls := [{ mutability := .not, ty := { kind := .ref .mut (.uint .u32), layoutIdx := 0 }, debugName := .none }],
            basicBlocks := [{ statements := [], terminator := { kind := .return_, span := "" }, isCleanup := false }]
          }"#;
        let prof_unused_mut = analyze_mir_lifting_profile(
            &mk_bundle("demo::unused_mut", CapturedItemKind::Subject),
            Some(unused_mut_mir),
            &[],
        );
        assert!(
            prof_unused_mut.is_pure_call_free_candidate() && !prof_unused_mut.has_mut_borrow,
            "unused &mut in localDecls without deref or BorrowKind.mut must remain pure: {prof_unused_mut:?}"
        );

        let fallback_ws = unique_temp_dir("profile_units_fallback");
        let fallback_unit = fallback_ws.join("target/anneal/units/u0/Mir/Demo");
        fs::create_dir_all(&fallback_unit).expect("create fallback unit dir");
        fs::write(fallback_unit.join("item.lean"), cleanup_poly_mir)
            .expect("write fallback unit mir");
        let mut fallback_bundle = mk_bundle("demo::item", CapturedItemKind::Subject);
        fallback_bundle.subject.target.mir_module_sha256.clear();
        let prof_fallback = analyze_workspace_lifting_profile(
            &fallback_ws.join(".anneal/generated/Mir"),
            &fallback_bundle,
        );
        assert!(
            prof_fallback.has_captured_mir
                && prof_fallback.type_param_count == 2
                && prof_fallback.has_cfg_back_edge,
            "analyze_workspace_lifting_profile must fall back to target/anneal/units: {prof_fallback:?}"
        );

        // 7. When `.anneal/generated/Mir/<Item>.lean` holds a stale stub whose SHA
        //    mismatches `record.target.mir_module_sha256` while `target/anneal/units`
        //    holds the fresh capture matching `mir_module_sha256`, `resolve_workspace_mir_file`
        //    and `analyze_workspace_lifting_profile` must read the fresh unit capture.
        let stale_mir_dir = fallback_ws.join(".anneal/generated/Mir/Demo");
        fs::create_dir_all(&stale_mir_dir).expect("create stale Mir/Demo");
        fs::write(
            stale_mir_dir.join("item.lean"),
            "prelude\nimport Init.Core\nimport Trusted\nnamespace Mir.Demo.item\nend Mir.Demo.item\n",
        )
        .expect("write stale stub Mir/Demo/item.lean");
        fallback_bundle.subject.target.mir_module_sha256 = sha256_hex(cleanup_poly_mir.as_bytes());
        let prof_fresh_unit = analyze_workspace_lifting_profile(
            &fallback_ws.join(".anneal/generated/Mir"),
            &fallback_bundle,
        );
        assert!(
            prof_fresh_unit.has_captured_mir
                && prof_fresh_unit.type_param_count == 2
                && prof_fresh_unit.has_cfg_back_edge,
            "stale .anneal/generated/Mir stub must be superseded by SHA-matching unit capture: {prof_fresh_unit:?}"
        );
        let _ = fs::remove_dir_all(&fallback_ws);

        // 8. Identifier primes (`c'`) adjacent to `'"'` and UTF-8 char literals (`'α'`)
        //    must not invert string polarity or hide real `.deref` / `.ref (.mut Bool.true)`.
        let prime_mir = r#"-- helper: if c'<'"' then 'α' else '\x22'
          def body : CapturedMir := {
            localDecls := [],
            basicBlocks := [{
              statements := [{
                kind := .assign { local_ := 1, projection := [] } (.ref (.mut Bool.true) { local_ := 2, projection := [] }),
                span := "s" -- .deref comment after c'<'"'
              }],
              terminator := { kind := .return_, span := "" },
              isCleanup := false
            }]
          }"#;
        let prof_prime = analyze_mir_lifting_profile(
            &mk_bundle("demo::prime", CapturedItemKind::Subject),
            Some(prime_mir),
            &[],
        );
        assert!(
            prof_prime.has_captured_mir
                && prof_prime.has_mut_borrow
                && prof_prime.has_impure_rvalue_or_asm
                && !prof_prime.has_deref_projection,
            "prime-identifier comment before body must not invert string polarity: {prof_prime:?}"
        );
    }

    #[test]
    fn scaffold_init_proofs_promotes_safe_total_equiv_and_polymorphic_templates() {
        let ws = unique_temp_dir("init_proofs_poly_total_equiv");
        let unit_dir = ws.join("target/anneal/units/u0/Mir/Demo");
        fs::create_dir_all(&unit_dir).expect("create unit Mir/Demo");

        let mono_mir = "import Trusted\nnamespace Mir.Demo.mono\ndef body : CapturedMir := { defPath := \"demo::mono\", typeParamCount := 0, localDecls := [], basicBlocks := [{ statements := [], terminator := { kind := .return_, span := \"\" }, isCleanup := false }] }\nend Mir.Demo.mono\n";
        let poly_mir = "import Trusted\nnamespace Mir.Demo.poly_id\ndef body : CapturedMir := { defPath := \"demo::poly_id\", typeParamCount := 1, localDecls := [], basicBlocks := [{ statements := [], terminator := { kind := .return_, span := \"\" }, isCleanup := false }] }\nend Mir.Demo.poly_id\n";

        fs::write(unit_dir.join("safe_tot.lean"), mono_mir).expect("write safe_tot.lean");
        fs::write(unit_dir.join("fast_eq.lean"), mono_mir).expect("write fast_eq.lean");
        fs::write(unit_dir.join("poly_id.lean"), poly_mir).expect("write poly_id.lean");

        let mk_subj = |def_id: &str, name: &str, src: &str| UnitTargetRecord {
            target: CapturedTarget {
                def_id: def_id.to_string(),
                mir_module_path: format!("Mir/Demo/{name}.lean"),
                mir_module_sha256: sha256_hex(src.as_bytes()),
            },
            lean_module_name: format!("Mir.Demo.{name}"),
            item_kind: CapturedItemKind::Subject,
            associated_subject_def_id: None,
            trait_impls: Vec::new(),
        };

        let records = vec![
            mk_subj("demo::safe_tot", "safe_tot", mono_mir),
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "demo::__ANNEAL_EXT_SPEC_TARGET___anneal_attr_safe_total_safe_tot"
                        .to_string(),
                    mir_module_path: String::new(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: String::new(),
                item_kind: CapturedItemKind::ExternalSpec,
                associated_subject_def_id: Some("demo::safe_tot".to_string()),
                trait_impls: Vec::new(),
            },
            mk_subj("demo::fast_eq", "fast_eq", mono_mir),
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id:
                        "demo::__ANNEAL_EXT_SPEC_TARGET___anneal_attr_equiv_safe_tot__for__fast_eq"
                            .to_string(),
                    mir_module_path: String::new(),
                    mir_module_sha256: String::new(),
                },
                lean_module_name: String::new(),
                item_kind: CapturedItemKind::ExternalSpec,
                associated_subject_def_id: Some("demo::fast_eq".to_string()),
                trait_impls: Vec::new(),
            },
            mk_subj("demo::poly_id", "poly_id", poly_mir),
        ];

        let cfg = ScaffoldConfig::new(&ws);
        scaffold_init_proof_templates(&cfg, &records).expect("init proof templates");

        let tot_proof =
            fs::read_to_string(ws.join("anneal/proofs/Proof/Demo/safe_tot.lean")).unwrap();
        assert!(
            tot_proof.contains(
                "theorem verified : TotalVerificationResult Obligations.Demo.safe_tot.totalClaim"
            ),
            "#[spec(safe_total)] starter template must target TotalVerificationResult: {tot_proof}"
        );
        let tot_verify =
            fs::read_to_string(ws.join(".anneal/generated/Verify/Demo/safe_tot.lean")).unwrap();
        assert!(tot_verify.contains("TotalVerificationResult Obligations.Demo.safe_tot.totalClaim"));

        let eq_proof =
            fs::read_to_string(ws.join("anneal/proofs/Proof/Demo/fast_eq.lean")).unwrap();
        assert!(
            eq_proof.contains(
                "theorem verified : StatefulEquivVerificationResult Obligations.Demo.fast_eq.equivClaim"
            ),
            "#[spec(equivalent_to: ...)] starter template must target StatefulEquivVerificationResult: {eq_proof}"
        );

        let poly_proof =
            fs::read_to_string(ws.join("anneal/proofs/Proof/Demo/poly_id.lean")).unwrap();
        assert!(
            poly_proof.contains("theorem verified : Obligations.Demo.poly_id.polyClaim"),
            "generic typeParamCount > 0 starter template must target polyClaim: {poly_proof}"
        );
        let poly_verify =
            fs::read_to_string(ws.join(".anneal/generated/Verify/Demo/poly_id.lean")).unwrap();
        assert!(poly_verify.contains("mkPolyVerificationResult"));
        assert!(!poly_verify.contains("signatureMonomorphic"));

        // Regression check: an authored stateless `VerificationResult` proof on a
        // `#[spec(safe_total)]` item (using `rustSafeTotalSpec : ItemSpec`) must NOT
        // be overwritten to `TotalVerificationResult` by `scaffold` or `refresh_workspace_assembly`.
        let tot_proof_path = ws.join("anneal/proofs/Proof/Demo/safe_tot.lean");
        fs::write(
            &tot_proof_path,
            "import Trusted\nimport Obligations.Demo.safe_tot\nnamespace Proof.Demo.safe_tot\nopen Trusted.VerificationResult\ntheorem verified : VerificationResult Obligations.Demo.safe_tot.claim := by sorry\nend Proof.Demo.safe_tot\n",
        )
        .expect("write authored stateless safe_tot proof");

        let cfg_no_init = ScaffoldConfig::new(&ws);
        scaffold_workspace_with_config(&cfg_no_init, &records)
            .expect("re-scaffold with authored stateless safe_tot proof");
        let tot_verify_stateless =
            fs::read_to_string(ws.join(".anneal/generated/Verify/Demo/safe_tot.lean")).unwrap();
        assert!(
            tot_verify_stateless
                .contains("theorem verified : VerificationResult Obligations.Demo.safe_tot.claim"),
            "authored stateless VerificationResult on #[spec(safe_total)] must be preserved: {tot_verify_stateless}"
        );
        assert!(!tot_verify_stateless.contains("TotalVerificationResult"));

        refresh_workspace_assembly(&ws)
            .expect("refresh_workspace_assembly with authored stateless safe_tot proof");
        let tot_verify_refreshed =
            fs::read_to_string(ws.join(".anneal/generated/Verify/Demo/safe_tot.lean")).unwrap();
        assert!(
            tot_verify_refreshed
                .contains("theorem verified : VerificationResult Obligations.Demo.safe_tot.claim"),
            "refresh_workspace_assembly must preserve stateless VerificationResult: {tot_verify_refreshed}"
        );

        fs::remove_file(&tot_proof_path).expect("delete safe_tot proof");
        refresh_workspace_assembly(&ws)
            .expect("refresh_workspace_assembly after deleting safe_tot proof");
        let tot_verify_restored =
            fs::read_to_string(ws.join(".anneal/generated/Verify/Demo/safe_tot.lean")).unwrap();
        assert!(
            tot_verify_restored
                .contains("TotalVerificationResult Obligations.Demo.safe_tot.totalClaim"),
            "deleting Proof/Demo/safe_tot.lean must restore default TotalVerificationResult: {tot_verify_restored}"
        );

        // Regression check: an authored stateless `Proof/Demo/fast_eq.lean` or overriding
        // `Specs/Demo/fast_eq.lean` on a `#[spec(safe_total, equivalent_to: ...)]` item must
        // NOT be clobbered to `StatefulEquivVerificationResult` by `scaffold` or
        // `refresh_workspace_assembly`.
        let eq_proof_path = ws.join("anneal/proofs/Proof/Demo/fast_eq.lean");
        fs::write(
            &eq_proof_path,
            "import Trusted\nimport Obligations.Demo.fast_eq\nnamespace Proof.Demo.fast_eq\nopen Trusted.VerificationResult\ntheorem verified : VerificationResult Obligations.Demo.fast_eq.claim := by sorry\nend Proof.Demo.fast_eq\n",
        )
        .expect("write authored stateless fast_eq proof");
        scaffold_workspace_with_config(&cfg_no_init, &records)
            .expect("re-scaffold with authored stateless fast_eq proof");
        let eq_verify_stateless =
            fs::read_to_string(ws.join(".anneal/generated/Verify/Demo/fast_eq.lean")).unwrap();
        assert!(
            eq_verify_stateless
                .contains("theorem verified : VerificationResult Obligations.Demo.fast_eq.claim"),
            "authored stateless VerificationResult on equivalent_to item must be preserved: {eq_verify_stateless}"
        );
        refresh_workspace_assembly(&ws)
            .expect("refresh_workspace_assembly with authored stateless fast_eq proof");
        let eq_verify_refreshed =
            fs::read_to_string(ws.join(".anneal/generated/Verify/Demo/fast_eq.lean")).unwrap();
        assert!(
            eq_verify_refreshed
                .contains("theorem verified : VerificationResult Obligations.Demo.fast_eq.claim"),
            "refresh_workspace_assembly must preserve stateless VerificationResult on equivalent_to item: {eq_verify_refreshed}"
        );

        fs::remove_file(&eq_proof_path).expect("delete fast_eq proof");
        let specs_demo_dir = ws.join("anneal/proofs/Specs/Demo");
        fs::create_dir_all(&specs_demo_dir).expect("create Specs/Demo");
        fs::write(
            specs_demo_dir.join("fast_eq.lean"),
            "import Trusted\nimport Obligations.Demo.fast_eq\nnamespace Specs.Demo.fast_eq\nopen Trusted.VerificationResult\ninstance : ItemSpec \"demo::fast_eq\" where\n  pre _ := True\n  post _ _ := True\nend Specs.Demo.fast_eq\n",
        )
        .expect("write overriding ItemSpec for fast_eq");
        scaffold_workspace_with_config(&cfg_no_init, &records)
            .expect("re-scaffold with overriding Specs/Demo/fast_eq.lean");
        let eq_verify_specs_override =
            fs::read_to_string(ws.join(".anneal/generated/Verify/Demo/fast_eq.lean")).unwrap();
        assert!(
            !eq_verify_specs_override.contains("StatefulEquivVerificationResult"),
            "overriding ItemSpec on equivalent_to item must not emit nonexistent equivClaim: {eq_verify_specs_override}"
        );

        // Regression check: contract class/claim substrings inside `def_id` string
        // literals (`ItemSpec "demo::StatefulItemSpec::get"`) or identifier names
        // (`polyClaim_helper`) must not false-trigger `is_stateful` or `is_polymorphic`.
        let sub_rel = Path::new("Demo/polyClaim_helper.lean");
        fs::write(
            ws.join("anneal/proofs/Specs").join(sub_rel),
            "import Trusted\nimport Obligations.Demo.polyClaim_helper\nnamespace Specs.Demo.StatefulItemSpec_get\nopen Trusted.VerificationResult\ninstance : ItemSpec \"demo::StatefulItemSpec::get\" where\n  pre _ := True\n  post _ _ := True\nend Specs.Demo.StatefulItemSpec_get\n",
        )
        .expect("write substring spec");
        fs::write(
            ws.join("anneal/proofs/Proof").join(sub_rel),
            "import Trusted\nimport Obligations.Demo.polyClaim_helper\nnamespace Proof.Demo.polyClaim_helper\nopen Trusted.VerificationResult\ndef totalClaim_note : String := \"polyClaim StatefulItemSpec\"\ntheorem verified : VerificationResult Obligations.Demo.polyClaim_helper.claim := by sorry\nend Proof.Demo.polyClaim_helper\n",
        )
        .expect("write substring proof");
        let sub_authored = detect_authored_item_modules(&ws.join("anneal/proofs"), sub_rel);
        assert!(
            sub_authored.has_specs
                && !sub_authored.has_legacy_specs_defs
                && sub_authored.has_proof
                && !sub_authored.is_stateful
                && !sub_authored.is_total
                && !sub_authored.is_polymorphic,
            "string literals and identifier substrings must not false-trigger contract flags: {sub_authored:?}"
        );

        let _ = fs::remove_dir_all(&ws);
    }

    #[test]
    fn mir_fragment_lattice_algebra_parsing_and_parity_across_all_5_levels() {
        // 1. Total order, rank, string / Lean ctor roundtrips, join, and meet.
        for (idx, &frag) in MirFragment::ALL.iter().enumerate() {
            assert_eq!(usize::from(frag.to_rank()), idx);
            assert_eq!(frag.to_string(), frag.as_str());
            assert_eq!(frag.as_str().parse::<MirFragment>(), Ok(frag));
            assert_eq!(frag.lean_ctor().parse::<MirFragment>(), Ok(frag));
            assert_eq!(frag.join(frag), frag);
            assert_eq!(frag.meet(frag), frag);
            assert_eq!(frag.join(MirFragment::PureLoopFree), frag);
            assert_eq!(frag.meet(MirFragment::FullMir), frag);
            assert_eq!(frag.join(MirFragment::FullMir), MirFragment::FullMir);
            assert_eq!(frag.meet(MirFragment::PureLoopFree), MirFragment::PureLoopFree);
        }
        assert!("invalid_fragment".parse::<MirFragment>().is_err());

        for &a in &MirFragment::ALL {
            for &b in &MirFragment::ALL {
                assert_eq!(a <= b, a.to_rank() <= b.to_rank());
                assert_eq!(a.join(b), b.join(a));
                assert_eq!(a.meet(b), b.meet(a));
                assert!(a <= a.join(b) && b <= a.join(b));
                assert!(a.meet(b) <= a && a.meet(b) <= b);
            }
        }

        // 2. Classify all 5 canonical levels + verify comment/string/identifier immunity.
        let level0_pure_loop_free = r#"
            -- Comment mentioning .call, .copyNonOverlapping, .deref, and .retag
            /- Nested /* block */ comment with TerminatorKind.inlineAsm andStatementKind.retag -/
            def body : CapturedMir := {
              defPath := "demo::TerminatorKind.call::NonDivergingIntrinsic.copyNonOverlapping",
              localDecls := [],
              basicBlocks := [
                { statements := [
                    { kind := .assign { local_ := 0, projection := [.field 0 { kind := .uint .u32, layoutIdx := 0 }] }
                        (.binaryOp .add (.copy { local_ := 1, projection := [] })
                          (.constant { ty := { kind := .uint .u32, layoutIdx := 0 }, val := .scalar (.int { bits := 1, sizeBytes := 4 }) })),
                      span := "src/.deref/.call/.copyNonOverlapping.rs:1:1" },
                    { kind := .intrinsic (.assume (.copy { local_ := 1, projection := [] })), span := "" }
                  ],
                  terminator := { kind := .goto 1, span := "" },
                  isCleanup := false },
                { statements := [
                    { kind := .assign { local_ := 0, projection := [] }
                        (.cast .intToInt (.copy { local_ := 0, projection := [] }) { kind := .uint .u32, layoutIdx := 0 }),
                      span := "local_call recall my_retag offset_val indirect_val" }
                  ],
                  terminator := { kind := .return_, span := "" },
                  isCleanup := false }
              ]
            }
        "#;
        let c0 = classify_mir_fragment(level0_pure_loop_free);
        assert_eq!(c0.inferred_fragment, MirFragment::PureLoopFree);
        assert!(c0.escalation_reasons.is_empty());
        assert!(c0.is_pure_mir() && c0.is_loop_free_pure_mir());
        assert_eq!(render_mir_fragment_diagnostic("demo::l0", &c0), None);

        let level1_pure_bounded_loop = r#"
            def body : CapturedMir := {
              localDecls := [],
              basicBlocks := [
                { statements := [],
                  terminator := { kind := .goto 1, span := "" },
                  isCleanup := false },
                { statements := [],
                  terminator := {
                    kind := .switchInt (.copy { local_ := 1, projection := [] })
                      { branches := [(0, 2)], otherwise := 1 },
                    span := ""
                  },
                  isCleanup := false },
                { statements := [],
                  terminator := { kind := .return_, span := "" },
                  isCleanup := false }
              ]
            }
        "#;
        let c1 = classify_mir_fragment(level1_pure_bounded_loop);
        assert_eq!(c1.inferred_fragment, MirFragment::PureBoundedLoop);
        assert_eq!(c1.escalation_reasons, vec!["CFG back-edge".to_string()]);
        assert!(c1.is_pure_mir() && !c1.is_loop_free_pure_mir());
        assert_eq!(render_mir_fragment_diagnostic("demo::l1", &c1), None);

        let level2_tree_borrows_local = r#"
            def body : CapturedMir := {
              localDecls := [],
              basicBlocks := [
                { statements := [
                    { kind := .assign { local_ := 2, projection := [] }
                        (.ref .shared { local_ := 1, projection := [] }),
                      span := "" },
                    { kind := .retag .default { local_ := 2, projection := [] }, span := "" },
                    { kind := .assign { local_ := 0, projection := [] }
                        (.use (.copy { local_ := 2, projection := [.deref, .unwrapUnsafeBinder { kind := .uint .u32, layoutIdx := 0 }] })),
                      span := "" },
                    { kind := .assign { local_ := 3, projection := [] }
                        (.binaryOp .offset (.copy { local_ := 2, projection := [] }) (.copy { local_ := 1, projection := [] })),
                      span := "" },
                    { kind := .assign { local_ := 4, projection := [] }
                        (.cast .ptrToPtr (.copy { local_ := 2, projection := [] }) { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }),
                      span := "" },
                    { kind := .assign { local_ := 5, projection := [] }
                        (.copyForDeref { local_ := 2, projection := [] }),
                      span := "" }
                  ],
                  terminator := { kind := .return_, span := "" },
                  isCleanup := false }
              ]
            }
        "#;
        let c2 = classify_mir_fragment(level2_tree_borrows_local);
        assert_eq!(c2.inferred_fragment, MirFragment::TreeBorrowsLocal);
        assert!(!c2.is_pure_mir());
        assert!(c2.escalation_reasons.contains(&"ProjectionElem.deref".to_string()));
        assert!(c2.escalation_reasons.contains(&"ProjectionElem.unwrapUnsafeBinder".to_string()));
        assert!(c2.escalation_reasons.contains(&"Rvalue.ref".to_string()));
        assert!(c2.escalation_reasons.contains(&"Rvalue.copyForDeref".to_string()));
        assert!(c2.escalation_reasons.contains(&"BinOp.offset".to_string()));
        assert!(c2.escalation_reasons.contains(&"CastKind.ptrToPtr".to_string()));
        assert!(c2.escalation_reasons.contains(&"StatementKind.retag".to_string()));
        let diag2 = render_mir_fragment_diagnostic("demo::l2", &c2).expect("diagnostic for l2");
        assert!(diag2.contains("tree_borrows_local"));
        assert!(diag2.contains("MirFragment.treeBorrowsLocal"));
        assert!(diag2.contains("ProjectionElem.deref"));
        assert!(diag2.contains("verifyStatefulMir_of_sepLenses"));

        let level3_intrinsic_copy = r#"
            def body : CapturedMir := {
              localDecls := [],
              basicBlocks := [
                { statements := [
                    { kind := .intrinsic (.copyNonOverlapping
                        (.copy { local_ := 1, projection := [] })
                        (.copy { local_ := 2, projection := [] })
                        (.constant { ty := { kind := .uint .usize, layoutIdx := 0 }, val := .indirect 0 0 })),
                      span := "" }
                  ],
                  terminator := { kind := .return_, span := "" },
                  isCleanup := false }
              ]
            }
        "#;
        let c3 = classify_mir_fragment(level3_intrinsic_copy);
        assert_eq!(c3.inferred_fragment, MirFragment::IntrinsicCopy);
        assert!(
            c3.escalation_reasons
                .contains(&"NonDivergingIntrinsic.copyNonOverlapping".to_string())
        );
        assert!(c3.escalation_reasons.contains(&"ConstValue.indirect".to_string()));
        let diag3 = render_mir_fragment_diagnostic("demo::l3", &c3).expect("diagnostic for l3");
        assert!(diag3.contains("intrinsic_copy"));
        assert!(diag3.contains("evalCopyNonOverlappingPermOk"));

        let level4_full_mir = r#"
            def body : CapturedMir := {
              localDecls := [],
              basicBlocks := [
                { statements := [
                    { kind := .assign { local_ := 1, projection := [] } (.threadLocalRef "tls::KEY"), span := "" }
                  ],
                  terminator := {
                    kind := .call
                      (.constant { ty := { kind := .fnDef "demo::callee" [], layoutIdx := 0 }, val := .zeroSized })
                      []
                      { local_ := 0, projection := [] }
                      (.some 1)
                      .continue_,
                    span := ""
                  },
                  isCleanup := false },
                { statements := [],
                  terminator := { kind := .inlineAsm "nop" [1] .unreachable, span := "" },
                  isCleanup := false }
              ]
            }
        "#;
        let c4 = classify_mir_fragment(level4_full_mir);
        assert_eq!(c4.inferred_fragment, MirFragment::FullMir);
        assert!(c4.escalation_reasons.contains(&"TerminatorKind.call".to_string()));
        assert!(c4.escalation_reasons.contains(&"TerminatorKind.inlineAsm".to_string()));
        assert!(c4.escalation_reasons.contains(&"Rvalue.threadLocalRef".to_string()));
        let diag4 = render_mir_fragment_diagnostic("demo::l4", &c4).expect("diagnostic for l4");
        assert!(diag4.contains("full_mir"));
        assert!(diag4.contains("PureMirModularConverges"));

        // 3. Non-inline alias fails closed to FullMir.
        let alias_c = classify_mir_fragment("def body : CapturedMir := otherBody\n");
        assert_eq!(alias_c.inferred_fragment, MirFragment::FullMir);
        assert!(!alias_c.escalation_reasons.is_empty());

        // 4. `compute_fragment_spec_digest` is deterministic and sensitive to all 4 inputs.
        let d_base = compute_fragment_spec_digest(
            "demo::item",
            "abc123",
            Some("instance : ItemSpec \"demo::item\" where\n  pre _ := True\n  post _ _ := True\n"),
            MirFragment::PureLoopFree,
        );
        assert_eq!(d_base.len(), 64);
        assert!(d_base.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')));
        assert_eq!(
            d_base,
            compute_fragment_spec_digest(
                "demo::item",
                "abc123",
                Some("instance : ItemSpec \"demo::item\" where\n  pre _ := True\n  post _ _ := True\n"),
                MirFragment::PureLoopFree,
            )
        );
        for &other_frag in &MirFragment::ALL[1..] {
            let d_frag = compute_fragment_spec_digest(
                "demo::item",
                "abc123",
                Some("instance : ItemSpec \"demo::item\" where\n  pre _ := True\n  post _ _ := True\n"),
                other_frag,
            );
            assert_ne!(d_base, d_frag, "spec_digest must change when fragment changes to {other_frag}");
        }
        assert_ne!(
            d_base,
            compute_fragment_spec_digest("demo::other", "abc123", None, MirFragment::PureLoopFree)
        );
        assert_ne!(
            compute_fragment_spec_digest("demo::item", "abc123", None, MirFragment::PureLoopFree),
            compute_fragment_spec_digest("demo::item", "abc124", None, MirFragment::PureLoopFree),
        );
        assert_ne!(
            compute_fragment_spec_digest("demo::item", "abc123", None, MirFragment::PureLoopFree),
            compute_fragment_spec_digest("demo::item", "abc123", Some(""), MirFragment::PureLoopFree),
        );
        // Length-prefixed fields: shifting bytes between `def_id` and
        // `mir_sha256` must not collide.
        assert_ne!(
            compute_fragment_spec_digest("demo::a", "bc", None, MirFragment::FullMir),
            compute_fragment_spec_digest("demo::ab", "c", None, MirFragment::FullMir),
        );
    }

    /// Kernel-checked parity source of truth: Wave 1's
    /// `theory/Anneal/PureMirExec.lean` (Section 11I, `namespace
    /// MirFragment.Witness`).
    ///
    /// `Anneal.PureMirExec.inferMinFragment` is syntactic over `basicBlocks`
    /// and is mirrored 1-to-1 by `classify_mir_fragment`, whereas
    /// `Anneal.PureMirExec.inferBorrowFreeMinFragment` additionally
    /// incorporates `hasNoPtrRelationalAssign` over `localDecls` (it can only
    /// be `≥` the Rust classification; `witnessPtrRelAssign` /
    /// `witnessUntypedRelAssign` separate the two layers).
    const PURE_MIR_EXEC_LEAN: &str = include_str!("../../../theory/Anneal/PureMirExec.lean");

    /// Lean functions whose `rfl` witness claims are checked against Rust.
    const LEAN_WITNESS_CLAIM_FUNCS: [&str; 3] =
        ["inferMinFragment", "hasCfgBackedge", "inferBorrowFreeMinFragment"];

    /// The exact text strictly inside `namespace MirFragment.Witness` ...
    /// `end MirFragment.Witness`, stopping *before* the closing `end` so the
    /// `protected` aliases declared after it (`PureMirExec.witness*`,
    /// `PureMirExec.inferMinFragment_witness*`) are neither duplicated nor
    /// misparsed. Both delimiters must occur exactly once.
    fn lean_witness_namespace() -> &'static str {
        const OPEN: &str = "\nnamespace MirFragment.Witness\n";
        const CLOSE: &str = "\nend MirFragment.Witness\n";
        assert_eq!(
            PURE_MIR_EXEC_LEAN.matches(OPEN).count(),
            1,
            "expected exactly one `namespace MirFragment.Witness` in PureMirExec.lean"
        );
        assert_eq!(
            PURE_MIR_EXEC_LEAN.matches(CLOSE).count(),
            1,
            "expected exactly one `end MirFragment.Witness` in PureMirExec.lean"
        );
        let start = PURE_MIR_EXEC_LEAN.find(OPEN).expect("namespace MirFragment.Witness") + OPEN.len();
        let len = PURE_MIR_EXEC_LEAN[start..]
            .find(CLOSE)
            .expect("`end MirFragment.Witness` after `namespace MirFragment.Witness`");
        &PURE_MIR_EXEC_LEAN[start..start + len]
    }

    /// Names of every public witness `def <w> : CapturedMir :=` declared in
    /// `namespace MirFragment.Witness` (excluding `private` helpers).
    fn lean_witness_def_names() -> BTreeSet<String> {
        lean_witness_namespace()
            .lines()
            .filter_map(|line| line.strip_prefix("def "))
            .filter_map(|rest| rest.strip_suffix(" : CapturedMir :="))
            .map(str::to_string)
            .collect()
    }

    /// Extract the verbatim text of `def <name> : CapturedMir := ...` (up to the
    /// next blank line) from `namespace MirFragment.Witness` in
    /// `PureMirExec.lean`.
    fn lean_witness_def(name: &str) -> &'static str {
        let ns = lean_witness_namespace();
        let header = format!("\ndef {name} : CapturedMir :=\n");
        assert_eq!(
            ns.matches(&header).count(),
            1,
            "expected exactly one `def {name} : CapturedMir :=` in MirFragment.Witness"
        );
        let start = ns.find(&header).expect("witness header") + 1;
        let rest = &ns[start..];
        &rest[..rest.find("\n\n").unwrap_or(rest.len())]
    }

    /// One `rfl` witness claim `theorem <name> : <func> <witness> = <value> :=
    /// rfl` (or its `prototypeGuard_` form `(<func> <witness> == <value>) =
    /// true := rfl`) from `namespace MirFragment.Witness`.
    #[derive(Debug)]
    struct LeanWitnessClaim {
        theorem: String,
        func: String,
        witness: String,
        value: String,
        is_guard: bool,
    }

    /// Strictly parse every `rfl` claim about `LEAN_WITNESS_CLAIM_FUNCS` inside
    /// `namespace MirFragment.Witness`. A theorem whose name announces such a
    /// claim (`<func>_<w>` or `prototypeGuard_<func>_<w>`) but whose statement
    /// does not have the expected shape panics instead of being skipped, so a
    /// reformatted Lean witness can never silently drop out of the parity check.
    fn lean_witness_claims() -> Vec<LeanWitnessClaim> {
        let lines: Vec<&str> = lean_witness_namespace().lines().collect();
        let mut claims = Vec::new();
        for (idx, line) in lines.iter().enumerate() {
            let Some(after_kw) = line.strip_prefix("theorem ") else {
                continue;
            };
            let name: String = after_kw
                .chars()
                .take_while(|c| !c.is_whitespace() && *c != ':')
                .collect();
            let (is_guard, bare) = match name.strip_prefix("prototypeGuard_") {
                Some(rest) => (true, rest),
                None => (false, name.as_str()),
            };
            let Some(func) = LEAN_WITNESS_CLAIM_FUNCS
                .iter()
                .find(|f| bare.strip_prefix(**f).is_some_and(|r| r.starts_with('_')))
            else {
                continue;
            };
            // Join the header with continuation lines up to the `:=` proof.
            let end = (idx..lines.len())
                .find(|&j| lines[j].contains(":="))
                .unwrap_or_else(|| panic!("unterminated witness theorem `{name}`"));
            let joined = lines[idx..=end].join(" ");
            let stmt = joined["theorem ".len() + name.len()..]
                .trim_start()
                .strip_prefix(':')
                .unwrap_or_else(|| panic!("malformed witness theorem header `{name}`"));
            let norm = stmt.replace('(', " ( ").replace(')', " ) ");
            let toks: Vec<&str> = norm.split_whitespace().collect();
            let parsed = match (is_guard, toks.as_slice()) {
                (false, [f, w, "=", v, ":=", "rfl"]) => Some((*f, *w, *v)),
                (true, ["(", f, w, "==", v, ")", "=", "true", ":=", "rfl"]) => {
                    Some((*f, *w, *v))
                }
                _ => None,
            };
            let Some((f, w, v)) = parsed else {
                panic!("unparseable `{func}` witness theorem `{name}`: `{stmt}`");
            };
            assert_eq!(f, *func, "theorem `{name}` must state `{func} ...`: `{stmt}`");
            assert_eq!(
                bare,
                format!("{func}_{w}"),
                "theorem `{name}` must be named after its witness `{w}`"
            );
            claims.push(LeanWitnessClaim {
                theorem: name.clone(),
                func: f.to_string(),
                witness: w.to_string(),
                value: v.to_string(),
                is_guard,
            });
        }
        claims
    }

    #[test]
    fn mir_fragment_rust_classifier_matches_lean_witness_theorems() {
        let claims = lean_witness_claims();
        let count = |func: &str| {
            claims
                .iter()
                .filter(|c| c.func == func && !c.is_guard)
                .count()
        };
        assert_eq!(
            count("inferMinFragment"),
            19,
            "expected exactly 19 `inferMinFragment_<w>` witness theorems: {claims:#?}"
        );
        assert_eq!(
            count("hasCfgBackedge"),
            8,
            "expected exactly 8 `hasCfgBackedge_<w>` witness theorems: {claims:#?}"
        );
        assert!(
            count("inferBorrowFreeMinFragment") >= 2,
            "expected borrow-free witness theorems: {claims:#?}"
        );
        // Every public witness body carries a kernel-checked `inferMinFragment`
        // claim, and every claim names a witness defined in the namespace.
        let frag_witnesses: BTreeSet<String> = claims
            .iter()
            .filter(|c| c.func == "inferMinFragment" && !c.is_guard)
            .map(|c| c.witness.clone())
            .collect();
        assert_eq!(frag_witnesses.len(), 19, "duplicate inferMinFragment claims: {claims:#?}");
        assert_eq!(
            frag_witnesses,
            lean_witness_def_names(),
            "witness defs and `inferMinFragment_<w>` theorems must cover each other"
        );

        let mut seen_levels = BTreeSet::new();
        for claim in &claims {
            let LeanWitnessClaim { theorem, func, witness, value, is_guard } = claim;
            let def_src = lean_witness_def(witness);
            let class = classify_mir_fragment(def_src);
            let scan = scan_captured_mir_body(def_src);
            assert!(scan.has_body && !scan.has_unscannable_syntax, "{witness}: {class:?}");
            match func.as_str() {
                "inferMinFragment" => {
                    let lean_frag: MirFragment = value
                        .strip_prefix('.')
                        .unwrap_or_else(|| panic!("{theorem}: non-shorthand value `{value}`"))
                        .parse()
                        .unwrap_or_else(|e| panic!("{theorem}: {e}"));
                    assert_eq!(
                        class.inferred_fragment, lean_frag,
                        "Rust classify_mir_fragment({witness}) disagrees with the kernel-checked \
                         Lean theorem `{theorem}` (`inferMinFragment {witness} = {value}`): {class:?}"
                    );
                    if !is_guard {
                        seen_levels.insert(lean_frag);
                    }
                }
                "inferBorrowFreeMinFragment" => {
                    let lean_frag: MirFragment = value
                        .strip_prefix('.')
                        .unwrap_or_else(|| panic!("{theorem}: non-shorthand value `{value}`"))
                        .parse()
                        .unwrap_or_else(|e| panic!("{theorem}: {e}"));
                    assert!(
                        class.inferred_fragment <= lean_frag,
                        "syntactic Rust classification of {witness} must lower-bound the \
                         borrow-free `{theorem}` (`{value}`): {class:?}"
                    );
                }
                "hasCfgBackedge" => assert_eq!(
                    scan.has_cfg_back_edge.to_string(),
                    *value,
                    "Rust back-edge rule disagrees with `{theorem}` (`hasCfgBackedge {witness} = {value}`)"
                ),
                other => panic!("unexpected witness claim function `{other}`"),
            }
        }
        assert_eq!(seen_levels.len(), 5, "witnesses must cover all 5 lattice levels");

        // Wave 1 alignment pins: provenance-exposing casts are `full_mir`,
        // while pointer-relational assignments stay `pure_loop_free` under the
        // syntactic classifier (only the borrow-free layer escalates them).
        for (witness, reason) in [
            ("witnessExposeProvenanceCast", "CastKind.pointerExposeProvenance"),
            ("witnessWithExposedProvenanceCast", "CastKind.pointerWithExposedProvenance"),
        ] {
            let class = classify_mir_fragment(lean_witness_def(witness));
            assert_eq!(class.inferred_fragment, MirFragment::FullMir, "{witness}: {class:?}");
            assert_eq!(class.escalation_reasons, vec![reason.to_string()], "{witness}");
            assert!(
                render_mir_fragment_diagnostic(witness, &class)
                    .expect("full_mir diagnostic")
                    .contains(reason)
            );
        }
        for witness in ["witnessPtrRelAssign", "witnessUntypedRelAssign"] {
            let class = classify_mir_fragment(lean_witness_def(witness));
            assert_eq!(class.inferred_fragment, MirFragment::PureLoopFree, "{witness}: {class:?}");
            assert!(class.escalation_reasons.is_empty(), "{witness}: {class:?}");
        }
    }

    #[test]
    fn mir_fragment_classifier_fails_closed_and_resolves_mut_ambiguity() {
        let classify_profile = |mir: &str| {
            let bundle = SubjectObligationBundle {
                subject: UnitTargetRecord {
                    target: CapturedTarget {
                        def_id: "demo::item".to_string(),
                        mir_module_path: "Mir/Demo/item.lean".to_string(),
                        mir_module_sha256: "0".repeat(64),
                    },
                    lean_module_name: "Mir.Demo.item".to_string(),
                    item_kind: CapturedItemKind::Subject,
                    associated_subject_def_id: None,
                    trait_impls: Vec::new(),
                },
                item_module_suffix: "Demo.item".to_string(),
                item_rel_path: PathBuf::from("Demo/item.lean"),
                inline_requires: Vec::new(),
                inline_ensures: Vec::new(),
                inline_qualifiers: Vec::new(),
                external_specs: Vec::new(),
                transitive_callees: Vec::new(),
                external_spec_callees: Vec::new(),
                called_callees: Vec::new(),
                spec_callees: Vec::new(),
                spec_companions_with_calls: BTreeSet::new(),
            };
            let profile = analyze_mir_lifting_profile(&bundle, Some(mir), &[]);
            // Legacy candidate predicates agree with the fragment lattice.
            assert_eq!(
                profile.is_pure_call_free_candidate(),
                profile.fragment_classification().is_pure_mir(),
                "legacy flags and inferred_fragment diverge for:\n{mir}\n{profile:?}"
            );
            profile
        };

        // 1. `Mutability.mut` (`.mut`) in types / raw pointers / `AggregateKind.rawPtr`
        //    is neither `Rvalue.ref` nor `BorrowKind.mut` (A0 classified this body
        //    `tree_borrows_local` with a spurious `Rvalue.ref`).
        let mut_types = lean_witness_def("witnessShorthandMutTypes");
        let prof = classify_profile(mut_types);
        assert_eq!(prof.inferred_fragment, MirFragment::PureLoopFree, "{prof:?}");
        assert!(!prof.has_mut_borrow && prof.is_pure_call_free_candidate(), "{prof:?}");
        let real_mut_borrow = "def body : CapturedMir := { basicBlocks := [{ statements := [{ kind := .assign { local_ := 1, projection := [] } (.ref (.mut false) { local_ := 2, projection := [] }), span := \"\" }], terminator := { kind := .return_, span := \"\" }, isCleanup := false }] }";
        let prof = classify_profile(real_mut_borrow);
        assert!(prof.has_mut_borrow, "{prof:?}");
        assert_eq!(prof.inferred_fragment, MirFragment::TreeBorrowsLocal);
        assert_eq!(prof.fragment_escalation_reasons, vec!["Rvalue.ref".to_string()]);

        // 2. `Rvalue.rawPtr` with a reordered place record is still detected.
        let raw_ptr = "def body : CapturedMir := { basicBlocks := [{ statements := [{ kind := .assign { local_ := 1, projection := [] } (.rawPtr Mutability.mut { projection := [], local_ := 2 }), span := \"\" }], terminator := { kind := .return_, span := \"\" }, isCleanup := false }] }";
        let prof = classify_profile(raw_ptr);
        assert_eq!(prof.fragment_escalation_reasons, vec!["Rvalue.rawPtr".to_string()]);

        // 3. Non-inline references inside `basicBlocks` (helper defs, positional
        //    `X.mk`, `⟨..⟩`, structure updates) fail closed to `FullMir`.
        for (label, blocks) in [
            ("helper terminator", "[{ statements := [], terminator := mkTerm .return_, isCleanup := false }]"),
            ("helper operand", "[{ statements := [{ kind := .assign { local_ := 0, projection := [] } (.use (u32ConstOperand 10)), span := \"\" }], terminator := { kind := .return_, span := \"\" }, isCleanup := false }]"),
            ("helper block list", "blocksOf demoBody"),
            ("positional place", "[{ statements := [{ kind := .assign (Place.mk 0 []) (.use (.copy (Place.mk 1 []))), span := \"\" }], terminator := { kind := .return_, span := \"\" }, isCleanup := false }]"),
            ("anonymous ctor", "[{ statements := [], terminator := ⟨.goto 0, \"\"⟩, isCleanup := false }]"),
            ("structure update", "[{ pureBlock with terminator := { kind := .return_, span := \"\" } }]"),
            ("named goto arg", "[{ statements := [], terminator := { kind := .goto (target := 0), span := \"\" }, isCleanup := false }]"),
            ("named slice arg", "[{ statements := [{ kind := .assign { local_ := 0, projection := [] } (.use (.constant { ty := { kind := .uint .u32, layoutIdx := 0 }, val := .slice (data := .ptr { allocId := 0, offsetBytes := 0 } 8) (meta_ := 1) })), span := \"\" }], terminator := { kind := .return_, span := \"\" }, isCleanup := false }]"),
            ("spoofed namespace ctor", "[{ statements := MyHelper.List.nil, terminator := { kind := .return_, span := \"\" }, isCleanup := false }]"),
            ("let binding with field ident", "[{ statements := (let val := []; val), terminator := { kind := .return_, span := \"\" }, isCleanup := false }]"),
            ("mismatched block fields", "[{ terminator := { kind := .return_, span := \"\" } }]"),
            ("malformed goto target", "[{ statements := [], terminator := { kind := .goto, span := \"\" }, isCleanup := false }]"),
        ] {
            let mir = format!("def body : CapturedMir := {{ basicBlocks := {blocks} }}");
            let prof = classify_profile(&mir);
            assert_eq!(prof.inferred_fragment, MirFragment::FullMir, "{label}: {prof:?}");
            assert!(prof.has_unscannable_mir && !prof.is_pure_call_free_candidate(), "{label}");
            assert!(prof.has_cfg_back_edge, "{label}: hidden blocks may hide back-edges");
            assert!(
                prof.fragment_escalation_reasons.iter().any(|r| r.contains("unscannable")),
                "{label}: {prof:?}"
            );
            let diag = render_mir_fragment_diagnostic("demo::item", &prof.fragment_classification())
                .expect("FullMir diagnostic");
            assert!(diag.contains("classified fail-closed"), "{label}: {diag}");
        }

        // 4. A non-inline alias followed by an unrelated inline body must not
        //    borrow that body's (pure) blocks, even when the first declaration
        //    is not named `body` or the second declaration is preceded by an
        //    inline comment (`/- doc -/`).
        for alias_src in [
            "import Trusted\ndef body : CapturedMir := impureHelperBody\n\ndef pureOther : CapturedMir := { basicBlocks := [{ statements := [], terminator := { kind := .return_, span := \"\" }, isCleanup := false }] }\n",
            "import Trusted\ndef customBody : CapturedMir := impureHelperBody\n/- doc -/ def pureOther : CapturedMir := { basicBlocks := [{ statements := [], terminator := { kind := .return_, span := \"\" }, isCleanup := false }] }\n",
        ] {
            let prof = classify_profile(alias_src);
            assert!(!prof.has_captured_mir, "{prof:?}");
            assert_eq!(classify_mir_fragment(alias_src).inferred_fragment, MirFragment::FullMir);
        }

        // 5. Fully-qualified / `@`-explicit terminator heads still yield CFG targets.
        for head in [
            "Trusted.Rustc.V2026_06_01.MirAst.TerminatorKind.goto 0",
            "@TerminatorKind.goto 0",
            "Trusted.Rustc.V2026_06_01.MirAst.TerminatorKind.drop { local_ := 1, projection := [] } 1 (Trusted.Rustc.V2026_06_01.MirAst.UnwindAction.cleanup 0)",
        ] {
            let mir = format!("def body : CapturedMir := {{ basicBlocks := [{{ statements := [], terminator := {{ kind := {head}, span := \"\" }}, isCleanup := false }}, {{ statements := [], terminator := {{ kind := .return_, span := \"\" }}, isCleanup := false }}] }}");
            let prof = classify_profile(&mir);
            assert!(prof.has_cfg_back_edge, "{head}: {prof:?}");
            assert_eq!(prof.inferred_fragment, MirFragment::PureBoundedLoop, "{head}: {prof:?}");
        }

        // 6. A fully-qualified `assume` intrinsic is not `copyNonOverlapping`.
        let assume = "def body : CapturedMir := { basicBlocks := [{ statements := [{ kind := Trusted.Rustc.V2026_06_01.MirAst.StatementKind.intrinsic (Trusted.Rustc.V2026_06_01.MirAst.NonDivergingIntrinsic.assume (.copy { local_ := 1, projection := [] })), span := \"\" }], terminator := { kind := .return_, span := \"\" }, isCleanup := false }] }";
        assert_eq!(classify_profile(assume).inferred_fragment, MirFragment::PureLoopFree);

        // 7. Fail-closed defaults and exact `fromStr?` parity.
        assert_eq!(MirFragment::default(), MirFragment::FullMir);
        assert_eq!(MirLiftingProfile::default().inferred_fragment, MirFragment::FullMir);
        assert!(" pure_loop_free".parse::<MirFragment>().is_err());
        assert!("pure_loop_free\n".parse::<MirFragment>().is_err());

        // 8. Wave 1 provenance-exposing casts (`checkCastFragment` /
        //    `isPureRvalue = false`) escalate to `full_mir` in shorthand,
        //    qualified, and fully-qualified emitter syntax, and are never pure
        //    (`is_pure_call_free_candidate` stays in lock-step via
        //    `classify_profile`).
        for (cast, reason) in [
            (".pointerExposeProvenance", "CastKind.pointerExposeProvenance"),
            ("CastKind.pointerExposeProvenance", "CastKind.pointerExposeProvenance"),
            (
                "Trusted.Rustc.V2026_06_01.MirAst.CastKind.pointerWithExposedProvenance",
                "CastKind.pointerWithExposedProvenance",
            ),
            ("@CastKind.pointerWithExposedProvenance", "CastKind.pointerWithExposedProvenance"),
        ] {
            let mir = format!("def body : CapturedMir := {{ basicBlocks := [{{ statements := [{{ kind := .assign {{ local_ := 1, projection := [] }} (.cast {cast} (.copy {{ local_ := 2, projection := [] }}) {{ kind := .uint .usize, layoutIdx := 0 }}), span := \"\" }}], terminator := {{ kind := .return_, span := \"\" }}, isCleanup := false }}] }}");
            let prof = classify_profile(&mir);
            assert_eq!(prof.inferred_fragment, MirFragment::FullMir, "{cast}: {prof:?}");
            assert_eq!(prof.fragment_escalation_reasons, vec![reason.to_string()], "{cast}");
            assert!(prof.has_impure_rvalue_or_asm && !prof.is_pure_call_free_candidate(), "{cast}");
            assert!(!prof.is_pure_with_callees_candidate(), "{cast}");
        }
        // A spoofed namespace never counts as the provenance cast (fails closed).
        let spoofed = "def body : CapturedMir := { basicBlocks := [{ statements := [{ kind := .assign { local_ := 1, projection := [] } (.cast Evil.CastKind.pointerExposeProvenance (.copy { local_ := 2, projection := [] }) { kind := .uint .usize, layoutIdx := 0 }), span := \"\" }], terminator := { kind := .return_, span := \"\" }, isCleanup := false }] }";
        let prof = classify_profile(spoofed);
        assert_eq!(prof.inferred_fragment, MirFragment::FullMir, "{prof:?}");
        assert!(prof.has_unscannable_mir, "{prof:?}");
    }

    /// B2 lexer & truncation traps. Each body's Lean ground truth was
    /// established with `#eval inferMinFragment` (prototype
    /// `61ee217a`, `PROTOTYPE_REPORT.md` Finding 11, now
    /// `Anneal.PureMirExec.inferMinFragment`); A1's scanner classified the
    /// first four `pure_loop_free` (fail-open).
    #[test]
    fn mir_fragment_scanner_resists_lexer_and_truncation_traps() {
        let call_block = "{ statements := [], terminator := { kind := .call (.constant { ty := { kind := .fnDef \"f\" [], layoutIdx := 0 }, val := .zeroSized }) [] { local_ := 0, projection := [] } (some 1) .continue_, span := \" basicBlocks := [] fnAbi := \" }, isCleanup := false }";
        let ret_block = "{ statements := [], terminator := { kind := .return_, span := \"\" }, isCleanup := false }";
        let body_with = |prefix: &str, def_path: &str| {
            format!(
                "import Trusted\n{prefix}def body : CapturedMir := {{\n  defPath := {def_path},\n  phase := .runtimePostCleanup,\n  role := .subject,\n  argCount := 0,\n  localDecls := [],\n  basicBlocks := [{call_block}, {ret_block}],\n  fnAbi := abi,\n  layouts := emptyLayoutTable,\n  allocations := []\n}}\n"
            )
        };
        // 1-3. String-polarity traps before `basicBlocks`: a raw string with an
        //      unescaped quote, an interpolated string nesting an escaped quote,
        //      and a guillemet identifier containing `"`, `--`, and `/-`. Each
        //      must keep lexing aligned so the real `TerminatorKind.call` is seen
        //      (Lean: `full_mir`) instead of the `span` text `basicBlocks := []`.
        for (label, src) in [
            ("raw string", body_with("", "r#\"demo\"x\"#")),
            ("interpolated string", body_with("", "s!\"demo{\"\\\"\"}x\"")),
            ("interpolated char & comment", body_with("", "s!\"demo{if '}' == '\"' /- \" } -/ then \"a\" else \"b\"}\"")),
            ("guillemet identifier", body_with("def «weird\"name -- /- , ] terminator :=» : Nat := 0\n", "\"demo\"")),
        ] {
            let scan = scan_captured_mir_body(&src);
            let class = classify_mir_fragment(&src);
            assert!(scan.has_body && !scan.has_unscannable_syntax, "{label}: {class:?}");
            assert_eq!(scan.basic_block_count, 2, "{label}");
            assert_eq!(class.inferred_fragment, MirFragment::FullMir, "{label}: {class:?}");
            assert!(
                class.escalation_reasons.iter().any(|r| r == "TerminatorKind.call"),
                "{label}: the call must be scanned, not hidden: {class:?}"
            );
        }

        // 4-5. Term-level `open .. in` / `set_option .. in` lines inside the body
        //      (Lean: `full_mir` / `pure_bounded_loop`). `bound_to_top_level_decl`
        //      may truncate there, so the bracket-aware value extent must fail
        //      closed instead of scanning an empty or partial block list.
        let open_in = format!("def body : CapturedMir := {{\n  basicBlocks :=\n    open TerminatorKind in\n    [{call_block}]\n}}\n");
        let set_option_in = format!("def body : CapturedMir := {{\n  basicBlocks := [\n    {{ statements := [], terminator := {{ kind := .goto 1, span := \"\" }}, isCleanup := false }},\n    set_option maxRecDepth 2000 in\n    {{ statements := [], terminator := {{ kind := .goto 1, span := \"\" }}, isCleanup := false }}\n  ]\n}}\n");
        for (label, src) in [("open .. in", open_in), ("set_option .. in", set_option_in)] {
            let class = classify_mir_fragment(&src);
            assert_eq!(class.inferred_fragment, MirFragment::FullMir, "{label}: {class:?}");
            assert!(scan_captured_mir_body(&src).has_cfg_back_edge, "{label}");
        }

        // 6. A named argument reusing a `CapturedMir` field name must not end
        //    the `basicBlocks` value early (Lean: `tree_borrows_local`).
        let named = lean_witness_def("witnessNamedDefPathArg");
        let class = classify_mir_fragment(named);
        assert_eq!(class.inferred_fragment, MirFragment::TreeBorrowsLocal, "{class:?}");
        assert_eq!(class.escalation_reasons, vec!["ProjectionElem.deref".to_string()]);

        // 7. Unbalanced or empty `basicBlocks` values, or guillemet identifiers
        //    containing `,` / `]` after a list, fail closed.
        for src in [
            "def body : CapturedMir := { basicBlocks := [{ statements := [], terminator := { kind := .return_, span := \"\" }, isCleanup := false }",
            "def body : CapturedMir := { basicBlocks := }",
            "def body : CapturedMir := { basicBlocks := [{ statements := [), terminator := { kind := .return_, span := \"\" }, isCleanup := false }] }",
            "def body : CapturedMir := { basicBlocks := [{ statements := [], terminator := { kind := .return_, span := \"\" }, isCleanup := false }] |>.«fnAbi :=» }",
        ] {
            let class = classify_mir_fragment(src);
            assert_eq!(class.inferred_fragment, MirFragment::FullMir, "{src}: {class:?}");
        }

        // 8. Column-aligned `basicBlocks  :=` / `isCleanup  :=` and compact
        //    zero-space `basicBlocks:=[{statements:=[],terminator:={kind:=.goto 0,span:=""},isCleanup:=false}]`
        //    and `(defPath := "...")` inside `localDecls` before a `&mut` local.
        let aligned = lean_witness_def("witnessAlignedAndInterpCharDefPath");
        assert_eq!(classify_mir_fragment(aligned).inferred_fragment, MirFragment::FullMir);
        let compact = "def body : CapturedMir := { basicBlocks:=[{statements:=[],terminator:={kind:=.goto 0,span:=\"\"},isCleanup:=false}] }";
        let compact_class = classify_mir_fragment(compact);
        assert_eq!(compact_class.inferred_fragment, MirFragment::PureBoundedLoop, "{compact_class:?}");
        let ld_defpath_mut = "def body : CapturedMir := { localDecls := [{ mutability := .not, ty := { kind := .adt (defPath := \"demo::S\") [], layoutIdx := 0 }, debugName := none }, { mutability := .not, ty := { kind := .ref .mut (.uint .u32), layoutIdx := 1 }, debugName := none }], basicBlocks := [{ statements := [{ kind := .assign { local_ := 0, projection := [] } (.use (.copy { local_ := 2, projection := [.deref] })), span := \"\" }], terminator := { kind := .return_, span := \"\" }, isCleanup := false }] }";
        let ld_scan = scan_captured_mir_body(ld_defpath_mut);
        assert!(ld_scan.has_mut_borrow, "defPath := inside localDecls must not truncate localDecls before &mut local: {ld_scan:?}");
        assert_eq!(basic_blocks_value_extent(" [] }"), Some(" [] "));
        assert_eq!(basic_blocks_value_extent(" (List.cons a List.nil),\n fnAbi := x"), Some(" (List.cons a List.nil)"));
        assert_eq!(basic_blocks_value_extent(" [a]\n  fnAbi := x"), Some(" [a]\n  "));
        assert_eq!(basic_blocks_value_extent(" [f (defPath := \"\")]\n  fnAbi := x"), Some(" [f (defPath := \"\")]\n  "));
        assert_eq!(basic_blocks_value_extent(" [a"), None);
        assert_eq!(basic_blocks_value_extent("  \n "), None);
    }

    /// Differential Lean <-> Rust parity harness (opt-in, `#[ignore]`).
    ///
    /// Classifies every `*.lean` file under `$ANNEAL_MIR_FRAGMENT_CORPUS_DIR`
    /// and writes `<file> <fragment> <has_cfg_back_edge> <block_count>` lines
    /// to `$ANNEAL_MIR_FRAGMENT_CORPUS_DIR/rust_out.txt`, for comparison with
    /// `#eval Anneal.PureMirExec.inferMinFragment` over the same bodies
    /// (prototype `61ee217a`, `PROTOTYPE_REPORT.md` Section 6):
    ///
    /// `ANNEAL_MIR_FRAGMENT_CORPUS_DIR=<dir> cargo test -p cargo-anneal --lib \
    ///  mir_fragment_parity_corpus_dump -- --ignored`
    #[test]
    #[ignore]
    fn mir_fragment_parity_corpus_dump() {
        let Ok(dir) = env::var("ANNEAL_MIR_FRAGMENT_CORPUS_DIR") else {
            return;
        };
        let mut paths: Vec<PathBuf> = fs::read_dir(&dir)
            .expect("read corpus dir")
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().is_some_and(|ext| ext == "lean"))
            .collect();
        paths.sort();
        let mut out = String::new();
        for path in paths {
            let src = fs::read_to_string(&path).expect("read corpus file");
            let scan = scan_captured_mir_body(&src);
            let class = classify_mir_fragment(&src);
            out.push_str(&format!(
                "{} {} {} {}\n",
                path.file_name().expect("file name").to_string_lossy(),
                class.inferred_fragment.as_str(),
                scan.has_cfg_back_edge,
                scan.basic_block_count,
            ));
        }
        fs::write(Path::new(&dir).join("rust_out.txt"), out).expect("write rust_out.txt");
    }
}
