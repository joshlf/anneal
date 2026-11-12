//! `rustc_driver` wrapper entry point and `after_analysis` MIR capture pass for
//! `rustc 1.98.0-nightly (14210df0e 2026-05-31)`.
//!
//! When Cargo invokes `anneal-rustc-capture` via `RUSTC_WORKSPACE_WRAPPER` or
//! `RUSTC_WRAPPER`, this module normalizes the command-line arguments, checks
//! whether the invocation is a crate compilation with `ANNEAL_CAPTURE_DIR`
//! configured, and runs `rustc_driver::run_compiler` with
//! [`AnnealCaptureCallbacks`].

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_interface::interface;
use rustc_middle::ty::TyCtxt;
use rustc_span::FileName;

use crate::lean_emit::{IrContractRole, emit_mir_lean_module};
use crate::manifest::{
    ANNEAL_CAPTURE_DIR_ENV, ANNEAL_CAPTURE_FILTER_ENV, CapturedItemKind, CapturedTarget,
    MIR_DIALECT_V2026_06_01, RUSTC_VERSION_STRING, UnitCaptureManifest, UnitTargetRecord,
    sha256_hex,
};
use crate::rustc_2026_06_01::mir_lower::{
    CrateContractIndex, ItemClassification, canonical_def_path, collect_referenced_callees,
    def_id_sort_key, lower_mir_body, query_post_cleanup_mir, should_capture_mir_item,
    should_capture_non_local_callee,
};

/// Default pass-through callbacks used when `anneal-rustc-capture` is invoked
/// without `ANNEAL_CAPTURE_DIR` or for non-capture compiler queries (such as
/// `--version`, `--print`, or build scripts).
struct PassThroughCallbacks;

impl Callbacks for PassThroughCallbacks {}

/// Compiler callbacks that extract `Runtime(PostCleanup)` MIR, ABI layouts,
/// and contract metadata after `rustc` type and borrow analysis completes.
///
/// `rustc` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) defines `Callbacks`
/// in [`compiler/rustc_driver_impl/src/lib.rs` lines 119–150](https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_driver_impl/src/lib.rs#L119-L150):
///
/// >```text
/// >pub trait Callbacks {
/// >    /// Called before creating the compiler instance
/// >    fn config(&mut self, _config: &mut interface::Config) {}
/// >    ...
/// >    /// Called after analysis. Return value instructs the compiler whether to
/// >    /// continue the compilation afterwards (defaults to `Compilation::Continue`)
/// >    fn after_analysis<'tcx>(
/// >        &mut self,
/// >        _compiler: &interface::Compiler,
/// >        _tcx: TyCtxt<'tcx>,
/// >    ) -> Compilation {
/// >        Compilation::Continue
/// >    }
/// >}
/// >```
pub struct AnnealCaptureCallbacks {
    capture_dir: PathBuf,
    unit_id_override: Option<String>,
    capture_filter: Option<String>,
    rustc_args: Vec<String>,
    capture_error: Option<String>,
}

impl AnnealCaptureCallbacks {
    /// Creates a new capture callback writing unit artifacts under
    /// `capture_dir`.
    pub fn new(
        capture_dir: PathBuf,
        unit_id_override: Option<String>,
        rustc_args: Vec<String>,
    ) -> Self {
        let capture_filter = env::var(ANNEAL_CAPTURE_FILTER_ENV)
            .ok()
            .filter(|val| !val.trim().is_empty());
        Self {
            capture_dir,
            unit_id_override,
            capture_filter,
            rustc_args,
            capture_error: None,
        }
    }

    /// Sets an explicit capture filter string (overriding
    /// `ANNEAL_CAPTURE_FILTER`).
    pub fn with_filter(mut self, capture_filter: Option<String>) -> Self {
        self.capture_filter = capture_filter.filter(|val| !val.trim().is_empty());
        self
    }
}

impl Callbacks for AnnealCaptureCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        // Skip MIR extraction if type-checking or borrow-checking reported any
        // compilation errors.
        if tcx.dcx().has_errors().is_some() {
            return Compilation::Continue;
        }

        if let Err(err) = capture_crate_unit(
            tcx,
            &self.capture_dir,
            self.unit_id_override.as_deref(),
            self.capture_filter.as_deref(),
            &self.rustc_args,
        ) {
            self.capture_error = Some(err);
        }

        Compilation::Continue
    }
}

/// Candidate local item with its disambiguated `def_path`, Lean module
/// `item_stem`, and contract classification prior to `ANNEAL_CAPTURE_FILTER`
/// selection.
struct CandidateCaptureItem {
    local_def_id: LocalDefId,
    raw_def_path: String,
    def_path: String,
    raw_stem: String,
    item_stem: String,
    classification: ItemClassification,
}

/// Parses a comma-separated `ANNEAL_CAPTURE_FILTER` string into non-empty
/// trimmed filter patterns.
pub fn parse_capture_filter(raw: Option<&str>) -> Vec<String> {
    raw.unwrap_or("")
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(str::to_owned)
        .collect()
}

/// Returns `true` if `def_path` or `item_stem` matches at least one pattern in
/// `patterns` (or if `patterns` is empty).
pub fn matches_capture_filter(def_path: &str, item_stem: &str, patterns: &[String]) -> bool {
    if patterns.is_empty() {
        return true;
    }
    patterns
        .iter()
        .any(|pat| def_path.contains(pat.as_str()) || item_stem.contains(pat.as_str()))
}

/// Disambiguates `candidate` against `used` by appending `_2`, `_3`, ... when
/// `candidate` has already been assigned to an earlier item in the crate.
pub fn disambiguate_identifier(
    candidate: &str,
    used: &mut BTreeSet<String>,
    next_suffix: &mut BTreeMap<String, usize>,
) -> String {
    if used.insert(candidate.to_owned()) {
        next_suffix.entry(candidate.to_owned()).or_insert(2);
        return candidate.to_owned();
    }
    let counter = next_suffix.entry(candidate.to_owned()).or_insert(2);
    loop {
        let idx = *counter;
        *counter += 1;
        let numbered = format!("{candidate}_{idx}");
        if used.insert(numbered.clone()) {
            return numbered;
        }
    }
}

/// Returns `true` if the current compilation unit is a primary verification
/// package rather than a dependency crate compiled under `RUSTC_WRAPPER`.
///
/// When invoked by Cargo, `CARGO_PKG_NAME` is set for every package and
/// `CARGO_PRIMARY_PACKAGE` is set only for the primary package(s) requested on
/// the command line. Direct `rustc` / unit-test invocations without
/// `CARGO_PKG_NAME` default to `true` unless `ANNEAL_IS_PRIMARY_PACKAGE=0` is
/// explicitly configured.
fn is_primary_package_env(crate_name: &str) -> bool {
    if let Ok(explicit) = env::var("ANNEAL_IS_PRIMARY_PACKAGE") {
        let trimmed = explicit.trim();
        if trimmed == "0" || trimmed.eq_ignore_ascii_case("false") {
            return false;
        }
        if trimmed == "1" || trimmed.eq_ignore_ascii_case("true") {
            return true;
        }
    }
    if env::var("ANNEAL_WHOLE_GRAPH_WRAPPER").ok().as_deref() == Some("1") {
        return env::var_os("CARGO_PRIMARY_PACKAGE").is_some();
    }
    if let Ok(pkg_name) = env::var("CARGO_PKG_NAME")
        && pkg_name.replace('-', "_") == crate_name.replace('-', "_")
    {
        return env::var_os("CARGO_PRIMARY_PACKAGE").is_some();
    }
    true
}

/// Extracts all local MIR items, reachable `.rmeta` / sysroot (`core`/`alloc`)
/// callee bodies, layouts, source digests, and contract roles for the current
/// crate and writes `<capture_dir>/<unit_id>/Mir/<Crate>/<Item>.lean` along
/// with `<capture_dir>/<unit_id>/UnitCaptureManifest.json`.
fn capture_crate_unit<'tcx>(
    tcx: TyCtxt<'tcx>,
    capture_dir: &Path,
    unit_id_override: Option<&str>,
    capture_filter: Option<&str>,
    rustc_args: &[String],
) -> Result<(), String> {
    let crate_name = tcx.crate_name(LOCAL_CRATE).as_str().to_owned();
    let unit_id = match unit_id_override {
        Some(id) if !id.is_empty() => id.to_owned(),
        _ => derive_unit_id(&crate_name, rustc_args),
    };

    let unit_dir = capture_dir.join(&unit_id);
    fs::create_dir_all(&unit_dir).map_err(|e| {
        format!("failed to create unit capture directory `{}`: {e}", unit_dir.display())
    })?;

    let is_primary_package = is_primary_package_env(&crate_name);
    let rust_sources = collect_local_source_digests(tcx, is_primary_package);

    // Collect and deterministically sort all local definitions with MIR bodies.
    let mut local_defs: Vec<(String, LocalDefId)> = tcx
        .mir_keys(())
        .iter()
        .copied()
        .filter(|&local_def_id| should_capture_mir_item(tcx, local_def_id))
        .map(|local_def_id| (canonical_def_path(tcx, local_def_id.to_def_id()), local_def_id))
        .collect();
    local_defs.sort_by(|(path_a, id_a), (path_b, id_b)| {
        path_a
            .cmp(path_b)
            .then_with(|| id_a.local_def_index.cmp(&id_b.local_def_index))
    });

    let ordered_local_ids: Vec<LocalDefId> = local_defs.iter().map(|(_, id)| *id).collect();
    let contract_index = CrateContractIndex::build(tcx, &ordered_local_ids);

    // Deterministically disambiguate colliding `def_path` and `item_stem`
    // values across `local_defs` before applying `ANNEAL_CAPTURE_FILTER`.
    let mut used_def_paths = BTreeSet::new();
    let mut next_def_path_suffix = BTreeMap::new();
    let mut used_item_stems = BTreeSet::new();
    let mut next_stem_suffix = BTreeMap::new();
    let mut candidates = Vec::with_capacity(local_defs.len());

    for (raw_def_path, local_def_id) in local_defs {
        let def_id = local_def_id.to_def_id();
        let mut classification = contract_index.classify(tcx, def_id);
        if !is_primary_package {
            // For non-primary dependency crates compiled under `RUSTC_WRAPPER`,
            // only emit callable items as `CapturedItemKind::Callee` so that
            // top-level `Verify/<Crate>/<Item>.lean` obligations are generated
            // exclusively for the primary crate.
            if matches!(
                classification.item_kind,
                CapturedItemKind::Subject
                    | CapturedItemKind::UnsafeTraitImpl
                    | CapturedItemKind::Model
                    | CapturedItemKind::TypeInvariant
            ) {
                classification.item_kind = CapturedItemKind::Callee;
                classification.associated_subject_def_id = None;
            } else {
                continue;
            }
        }
        let def_path = disambiguate_identifier(
            &raw_def_path,
            &mut used_def_paths,
            &mut next_def_path_suffix,
        );
        let raw_stem = sanitize_item_module_stem(&crate_name, &def_path);
        let item_stem =
            disambiguate_identifier(&raw_stem, &mut used_item_stems, &mut next_stem_suffix);
        candidates.push(CandidateCaptureItem {
            local_def_id,
            raw_def_path,
            def_path,
            raw_stem,
            item_stem,
            classification,
        });
    }

    let filter_patterns = parse_capture_filter(capture_filter);
    if is_primary_package && !filter_patterns.is_empty() {
        let mut selected_subjects = BTreeSet::new();
        for c in &candidates {
            if matches_capture_filter(&c.def_path, &c.item_stem, &filter_patterns)
                || matches_capture_filter(&c.raw_def_path, &c.raw_stem, &filter_patterns)
            {
                selected_subjects.insert(c.raw_def_path.clone());
                selected_subjects.insert(c.def_path.clone());
                if let Some(ref subj) = c.classification.associated_subject_def_id {
                    selected_subjects.insert(subj.clone());
                }
            }
        }
        candidates.retain(|c| {
            matches_capture_filter(&c.def_path, &c.item_stem, &filter_patterns)
                || matches_capture_filter(&c.raw_def_path, &c.raw_stem, &filter_patterns)
                || selected_subjects.contains(&c.raw_def_path)
                || selected_subjects.contains(&c.def_path)
                || c.classification
                    .associated_subject_def_id
                    .as_ref()
                    .is_some_and(|subj| {
                        selected_subjects.contains(subj)
                            || matches_capture_filter(subj, subj, &filter_patterns)
                    })
        });
    }

    let crate_pascal = to_pascal_case(&crate_name);
    let mut unit_targets = Vec::with_capacity(candidates.len());
    let mut emitted_non_local: BTreeSet<(u32, u32)> = BTreeSet::new();
    let mut visited_worklist_substs: BTreeMap<
        (u32, u32),
        Vec<Option<rustc_middle::ty::GenericArgsRef<'tcx>>>,
    > = BTreeMap::new();
    let mut worklist: VecDeque<(DefId, Option<rustc_middle::ty::GenericArgsRef<'tcx>>)> =
        VecDeque::new();

    for candidate in candidates {
        let def_id = candidate.local_def_id.to_def_id();
        let body = query_post_cleanup_mir(tcx, candidate.local_def_id);
        // `requires` / `ensures` companions are evaluated with their transitive
        // callees linked (`defaultSpecCallees`), so the bodies they call must be
        // captured as well. `#[external_spec]` sidecars are deliberately not
        // traversed: their bodies only reference the abstracted target and the
        // `unimplemented!` panic machinery.
        if matches!(
            candidate.classification.item_kind,
            CapturedItemKind::Subject
                | CapturedItemKind::Callee
                | CapturedItemKind::Model
                | CapturedItemKind::UnsafeTraitImpl
                | CapturedItemKind::InlineSpecRequires
                | CapturedItemKind::InlineSpecEnsures
        ) {
            for (callee_def_id, opt_substs) in collect_referenced_callees(tcx, def_id, body, None) {
                if should_capture_non_local_callee(tcx, callee_def_id) {
                    let seen_substs = visited_worklist_substs
                        .entry(def_id_sort_key(callee_def_id))
                        .or_default();
                    if seen_substs.len() < 16 && !seen_substs.contains(&opt_substs) {
                        seen_substs.push(opt_substs);
                        worklist.push_back((callee_def_id, opt_substs));
                    }
                }
            }
        }

        let mut ir_captured = lower_mir_body(
            tcx,
            def_id,
            body,
            candidate.classification.contract_role.clone(),
        );
        ir_captured.def_path = candidate.def_path.clone();
        for ti in &mut ir_captured.trait_impls {
            ti.impl_path = candidate.def_path.clone();
        }

        let item_stem = candidate.item_stem;
        let lean_module_name = format!("Mir.{crate_pascal}.{item_stem}");
        let mir_module_rel_path = format!("Mir/{crate_pascal}/{item_stem}.lean");
        let lean_source = emit_mir_lean_module(&lean_module_name, &ir_captured);
        let mir_digest = sha256_hex(lean_source.as_bytes());

        let mir_full_path = unit_dir.join(&mir_module_rel_path);
        if let Some(parent) = mir_full_path.parent() {
            fs::create_dir_all(parent).map_err(|e| {
                format!("failed to create MIR directory `{}`: {e}", parent.display())
            })?;
        }
        fs::write(&mir_full_path, lean_source.as_bytes()).map_err(|e| {
            format!("failed to write MIR Lean module `{}`: {e}", mir_full_path.display())
        })?;

        let mut manifest_trait_impls = Vec::new();
        for ti in ir_captured.trait_impls {
            let mut trait_args_lean = Vec::new();
            for arg in ti.trait_ref.args {
                trait_args_lean.push(crate::lean_emit::render_rigid_ty_pub(&arg));
            }
            manifest_trait_impls.push(crate::manifest::ManifestTraitImplEntry {
                trait_method_def_path: ti.trait_ref.def_path,
                trait_args_lean,
                impl_path: ti.impl_path,
            });
        }

        unit_targets.push(UnitTargetRecord {
            target: CapturedTarget {
                def_id: candidate.def_path,
                mir_module_path: mir_module_rel_path,
                mir_module_sha256: mir_digest,
            },
            lean_module_name,
            item_kind: candidate.classification.item_kind,
            associated_subject_def_id: candidate.classification.associated_subject_def_id,
            trait_impls: manifest_trait_impls,
        });
    }

    // Transitively extract reachable non-local `.rmeta` / sysroot (`core`/`alloc`)
    // MIR bodies referenced by this compilation unit's captured items (both
    // primary-crate subjects and source-built dependency-crate callees).
    {
        let mut used_stems_by_crate: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut next_stem_suffix_by_crate: BTreeMap<String, BTreeMap<String, usize>> =
            BTreeMap::new();
        used_stems_by_crate.insert(crate_pascal.clone(), used_item_stems);
        next_stem_suffix_by_crate.insert(crate_pascal.clone(), next_stem_suffix);

        while let Some((callee_def_id, opt_substs)) = worklist.pop_front() {
            if !should_capture_non_local_callee(tcx, callee_def_id) {
                continue;
            }
            let body = tcx.optimized_mir(callee_def_id);
            for (next_def_id, next_substs) in
                collect_referenced_callees(tcx, callee_def_id, body, opt_substs)
            {
                if should_capture_non_local_callee(tcx, next_def_id) {
                    let seen_substs = visited_worklist_substs
                        .entry(def_id_sort_key(next_def_id))
                        .or_default();
                    if seen_substs.len() < 16 && !seen_substs.contains(&next_substs) {
                        seen_substs.push(next_substs);
                        worklist.push_back((next_def_id, next_substs));
                    }
                }
            }
            if !emitted_non_local.insert(def_id_sort_key(callee_def_id)) {
                continue;
            }

            let callee_crate_name = tcx.crate_name(callee_def_id.krate).as_str().to_owned();
            let callee_crate_pascal = to_pascal_case(&callee_crate_name);
            let raw_def_path = canonical_def_path(tcx, callee_def_id);
            let def_path = disambiguate_identifier(
                &raw_def_path,
                &mut used_def_paths,
                &mut next_def_path_suffix,
            );
            let raw_stem = sanitize_item_module_stem(&callee_crate_name, &def_path);
            let crate_used_stems = used_stems_by_crate
                .entry(callee_crate_pascal.clone())
                .or_default();
            let crate_next_suffix = next_stem_suffix_by_crate
                .entry(callee_crate_pascal.clone())
                .or_default();
            let item_stem =
                disambiguate_identifier(&raw_stem, crate_used_stems, crate_next_suffix);

            let mut ir_captured =
                lower_mir_body(tcx, callee_def_id, body, IrContractRole::Subject);
            ir_captured.def_path = def_path.clone();
            for ti in &mut ir_captured.trait_impls {
                ti.impl_path = def_path.clone();
            }

            let lean_module_name = format!("Mir.{callee_crate_pascal}.{item_stem}");
            let mir_module_rel_path = format!("Mir/{callee_crate_pascal}/{item_stem}.lean");
            let lean_source = emit_mir_lean_module(&lean_module_name, &ir_captured);
            let mir_digest = sha256_hex(lean_source.as_bytes());

            let mir_full_path = unit_dir.join(&mir_module_rel_path);
            if let Some(parent) = mir_full_path.parent() {
                fs::create_dir_all(parent).map_err(|e| {
                    format!("failed to create MIR directory `{}`: {e}", parent.display())
                })?;
            }
            fs::write(&mir_full_path, lean_source.as_bytes()).map_err(|e| {
                format!(
                    "failed to write MIR Lean module `{}`: {e}",
                    mir_full_path.display()
                )
            })?;

            let mut manifest_trait_impls = Vec::new();
            for ti in ir_captured.trait_impls {
                let mut trait_args_lean = Vec::new();
                for arg in ti.trait_ref.args {
                    trait_args_lean.push(crate::lean_emit::render_rigid_ty_pub(&arg));
                }
                manifest_trait_impls.push(crate::manifest::ManifestTraitImplEntry {
                    trait_method_def_path: ti.trait_ref.def_path,
                    trait_args_lean,
                    impl_path: ti.impl_path,
                });
            }

            unit_targets.push(UnitTargetRecord {
                target: CapturedTarget {
                    def_id: def_path,
                    mir_module_path: mir_module_rel_path,
                    mir_module_sha256: mir_digest,
                },
                lean_module_name,
                item_kind: CapturedItemKind::Callee,
                associated_subject_def_id: None,
                trait_impls: manifest_trait_impls,
            });
        }
    }

    unit_targets.sort_by(|a, b| a.target.def_id.cmp(&b.target.def_id));

    let unit_manifest = UnitCaptureManifest {
        schema: UnitCaptureManifest::SCHEMA_VERSION,
        crate_name,
        unit_id,
        rustc_version: RUSTC_VERSION_STRING.to_owned(),
        mir_dialect: MIR_DIALECT_V2026_06_01.to_owned(),
        compilation_succeeded: true,
        rust_sources,
        unit_targets,
    };

    let manifest_json = unit_manifest.to_json_string();
    let manifest_path = unit_dir.join("UnitCaptureManifest.json");
    fs::write(&manifest_path, manifest_json.as_bytes()).map_err(|e| {
        format!("failed to write UnitCaptureManifest `{}`: {e}", manifest_path.display())
    })?;

    Ok(())
}

/// Collects SHA-256 digests of all real source files belonging to `LOCAL_CRATE`
/// from `tcx.sess.source_map()`.
///
/// `rustc` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) defines `SourceFile`
/// and `FileName` in [`compiler/rustc_span/src/lib.rs` lines 505–524 and 1920–1955](https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_span/src/lib.rs#L1920-L1955):
///
/// >```text
/// >pub enum FileName {
/// >    Real(RealFileName),
/// >    ...
/// >}
/// >
/// >pub struct SourceFile {
/// >    pub name: FileName,
/// >    pub src: Option<Arc<String>>,
/// >    ...
/// >    pub cnum: CrateNum,
/// >}
/// >```
fn collect_local_source_digests(
    tcx: TyCtxt<'_>,
    is_primary_package: bool,
) -> Vec<(String, String)> {
    if !is_primary_package {
        return Vec::new();
    }
    let source_map = tcx.sess.source_map();
    let files = source_map.files();
    let cwd = env::current_dir().ok();
    let mut by_path: BTreeMap<String, String> = BTreeMap::new();

    for source_file in files.iter() {
        if source_file.cnum != LOCAL_CRATE {
            continue;
        }
        let FileName::Real(ref real_name) = source_file.name else {
            continue;
        };
        let Some(local_path) = real_name.local_path() else {
            continue;
        };

        let rel_display = if let Some(ref base) = cwd {
            local_path
                .strip_prefix(base)
                .unwrap_or(local_path)
                .to_string_lossy()
                .replace('\\', "/")
        } else {
            local_path.to_string_lossy().replace('\\', "/")
        };

        if !is_primary_package
            && (rel_display.starts_with('/')
                || rel_display.starts_with("..")
                || rel_display.contains("/../"))
        {
            continue;
        }

        let digest = if let Ok(bytes) = fs::read(local_path) {
            sha256_hex(&bytes)
        } else if let Some(ref src) = source_file.src {
            sha256_hex(src.as_bytes())
        } else {
            continue;
        };

        by_path.insert(rel_display, digest);
    }

    by_path.into_iter().collect()
}

/// Derives a deterministic compilation unit identifier from the crate name and
/// any `-C metadata=<hash>` flag passed by Cargo.
pub fn derive_unit_id(crate_name: &str, rustc_args: &[String]) -> String {
    let mut metadata: Option<&str> = None;
    let mut iter = rustc_args.iter();
    while let Some(arg) = iter.next() {
        if arg == "-C" {
            if let Some(val) = iter.next() {
                if let Some(m) = val.strip_prefix("metadata=") {
                    metadata = Some(m);
                }
            }
        } else if let Some(val) = arg.strip_prefix("-C") {
            if let Some(m) = val.strip_prefix("metadata=") {
                metadata = Some(m);
            }
        }
    }

    match metadata {
        Some(m) if !m.is_empty() => format!("{crate_name}-{m}"),
        _ => crate_name.to_owned(),
    }
}

/// Converts a `snake_case` or `kebab-case` crate name into `PascalCase` for
/// Lean module path construction (`demo` -> `Demo`, `my_crate` -> `MyCrate`).
pub fn to_pascal_case(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    for part in input.split(|c: char| c == '_' || c == '-' || !c.is_ascii_alphanumeric()) {
        if part.is_empty() {
            continue;
        }
        let mut chars = part.chars();
        if let Some(first) = chars.next() {
            out.push(first.to_ascii_uppercase());
            for ch in chars {
                out.push(ch);
            }
        }
    }
    if out.is_empty() {
        "Crate".to_owned()
    } else {
        out
    }
}

/// Converts a canonical definition path (`demo::sub::answer`) into a valid Lean
/// module stem relative to the crate (`sub_answer` or `answer`).
pub fn sanitize_item_module_stem(crate_name: &str, def_path: &str) -> String {
    let prefix = format!("{crate_name}::");
    let stripped = def_path
        .strip_prefix(&prefix)
        .unwrap_or(def_path)
        .trim_matches(|c: char| !c.is_ascii_alphanumeric() && c != '_');
    let mut out = String::with_capacity(stripped.len());
    let mut prev_sep = false;

    for ch in stripped.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
            prev_sep = false;
        } else if !prev_sep {
            out.push('_');
            prev_sep = true;
        }
    }
    if out.is_empty() {
        "item".to_owned()
    } else if out.starts_with(|c: char| c.is_ascii_digit()) {
        format!("_{out}")
    } else {
        out
    }
}

/// Returns the hierarchical Lean module segments `["Mir", "<CratePascal>", "<ItemStem>"]`
/// for a canonical `def_path` in `crate_name`.
pub fn lean_module_segments_for_def_path(crate_name: &str, def_path: &str) -> Vec<String> {
    vec![
        String::from("Mir"),
        to_pascal_case(crate_name),
        sanitize_item_module_stem(crate_name, def_path),
    ]
}

/// Normalizes command-line arguments when invoked either directly or via Cargo
/// `RUSTC_WRAPPER` / `RUSTC_WORKSPACE_WRAPPER` (where `args[1]` or `args[2]` is
/// the `rustc` executable path).
pub fn normalize_wrapper_args(raw_args: &[String]) -> Vec<String> {
    let mut args: Vec<String> = if raw_args.len() >= 2 && is_rustc_executable_arg(&raw_args[1]) {
        raw_args[1..].to_vec()
    } else if raw_args.len() >= 3 && is_rustc_executable_arg(&raw_args[2]) {
        raw_args[2..].to_vec()
    } else if raw_args.is_empty() {
        vec!["rustc".to_owned()]
    } else {
        raw_args.to_vec()
    };

    // Ensure `--sysroot` is present so `rustc_driver` can locate `core` and
    // `std` when linked as a standalone wrapper binary.
    if !has_sysroot_arg(&args) {
        if let Some(sysroot) = detect_sysroot(&args[0]) {
            args.push("--sysroot".to_owned());
            args.push(sysroot);
        }
    }

    args
}

fn is_rustc_executable_arg(arg: &str) -> bool {
    let path = Path::new(arg);
    let Some(stem) = path.file_stem().and_then(|s| s.to_str()) else {
        return false;
    };
    stem == "rustc" || stem.starts_with("rustc-")
}

fn has_sysroot_arg(args: &[String]) -> bool {
    args.iter().any(|arg| arg == "--sysroot" || arg.starts_with("--sysroot="))
}

fn detect_sysroot(rustc_bin: &str) -> Option<String> {
    // First check whether `rustc_bin` is an explicit path under
    // `<sysroot>/bin/rustc` or an omnibus archive wrapper under
    // `<install_root>/bin/anneal-rustc-capture` (where the packaged sysroot is
    // `<install_root>/rust`).
    let bin_path = Path::new(rustc_bin);
    if bin_path.components().count() > 1 {
        if let Some(parent) = bin_path.parent().and_then(|p| p.parent()) {
            if parent.join("lib").join("rustlib").exists() {
                return Some(parent.to_string_lossy().into_owned());
            }
            let packaged_rust = parent.join("rust");
            if packaged_rust.join("lib").join("rustlib").exists() {
                return Some(packaged_rust.to_string_lossy().into_owned());
            }
        }
    }

    if let Ok(exe) = env::current_exe()
        && let Some(install_root) = exe.parent().and_then(|p| p.parent())
    {
        let packaged_rust = install_root.join("rust");
        if packaged_rust.join("lib").join("rustlib").exists() {
            return Some(packaged_rust.to_string_lossy().into_owned());
        }
    }

    // Fallback to `rustc --print sysroot`.
    let cmd_name = if is_rustc_executable_arg(rustc_bin) { rustc_bin } else { "rustc" };
    let output = Command::new(cmd_name).arg("--print").arg("sysroot").output().ok()?;
    if !output.status.success() {
        return None;
    }
    let sysroot = String::from_utf8(output.stdout).ok()?.trim().to_owned();
    if sysroot.is_empty() { None } else { Some(sysroot) }
}

/// Returns `true` if `rustc_args` represents a crate compilation that should
/// be captured (rather than `--version`, `--print`, or Cargo's `___` probe /
/// `build_script_build`).
pub fn should_run_capture_for_args(rustc_args: &[String]) -> bool {
    let mut crate_name: Option<&str> = None;
    let mut is_proc_macro = false;
    let mut input_file: Option<&str> = None;

    let mut iter = rustc_args.iter().skip(1);
    while let Some(arg) = iter.next() {
        if arg == "--version"
            || arg == "-V"
            || arg == "-vV"
            || arg == "--help"
            || arg == "-h"
            || arg == "--print"
            || arg.starts_with("--print=")
            || arg == "--explain"
            || arg.starts_with("--explain=")
        {
            return false;
        }
        if arg == "--crate-name" {
            if let Some(name) = iter.next() {
                crate_name = Some(name.as_str());
            }
        } else if let Some(name) = arg.strip_prefix("--crate-name=") {
            crate_name = Some(name);
        } else if arg == "--crate-type" {
            if let Some(kind) = iter.next() {
                if kind == "proc-macro" {
                    is_proc_macro = true;
                }
            }
        } else if let Some(kind) = arg.strip_prefix("--crate-type=") {
            if kind == "proc-macro" {
                is_proc_macro = true;
            }
        } else if !arg.starts_with('-') && arg.ends_with(".rs") {
            input_file = Some(arg.as_str());
        }
    }

    let Some(input_rs) = input_file else {
        return false;
    };
    if is_proc_macro {
        return false;
    }

    let normalized_input = input_rs.replace('\\', "/");
    if normalized_input.contains("/.cargo/registry/")
        || normalized_input.contains("/.cargo/git/")
    {
        return false;
    }

    if let Some(name) = crate_name {
        if matches!(
            name,
            "___"
                | "build_script_build"
                | "anneal_spec"
                | "anneal_spec_macros"
                | "anodized"
                | "anodized_core"
                | "anodized_logic"
                | "anodized_macros"
                | "proc_macro2"
                | "quote"
                | "unicode_ident"
                | "syn"
                | "autocfg"
        ) {
            return false;
        }
    }

    true
}

/// Entry point invoked by `src/main.rs`. Reads command-line arguments and
/// `ANNEAL_CAPTURE_DIR` / `ANNEAL_UNIT_ID` from the process environment, runs
/// `rustc_driver::run_compiler`, and returns a process exit code (`0` on
/// success, `1` on failure).
///
/// `rustc` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) defines
/// `run_compiler` and `catch_with_exit_code` in
/// [`compiler/rustc_driver_impl/src/lib.rs` lines 170–185 and 1375–1382](https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_driver_impl/src/lib.rs#L170-L185):
///
/// >```text
/// >/// This is the primary entry point for rustc.
/// >pub fn run_compiler(at_args: &[String], callbacks: &mut (dyn Callbacks + Send)) {
/// >    let mut default_early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
/// >    ...
/// >    let at_args = at_args.get(1..).unwrap_or_default();
/// >```
///
/// >```text
/// >/// Variant of `catch_fatal_errors` for the `interface::Result` return type
/// >/// that also computes the exit code.
/// >pub fn catch_with_exit_code<T: Termination>(f: impl FnOnce() -> T) -> ExitCode {
/// >    match catch_fatal_errors(f) {
/// >        Ok(status) => status.report(),
/// >        _ => ExitCode::FAILURE,
/// >    }
/// >}
/// >```
pub fn run_from_env_args() -> i32 {
    let raw_args: Vec<String> = env::args().collect();
    let capture_dir = env::var(ANNEAL_CAPTURE_DIR_ENV)
        .ok()
        .filter(|val| !val.trim().is_empty())
        .map(PathBuf::from);
    let unit_id_override =
        env::var("ANNEAL_UNIT_ID").ok().filter(|val| !val.trim().is_empty());

    run_with_args(&raw_args, capture_dir, unit_id_override)
}

/// Runs the compiler driver with explicit arguments and optional capture
/// directory configuration.
pub fn run_with_args(
    raw_args: &[String],
    capture_dir: Option<PathBuf>,
    unit_id_override: Option<String>,
) -> i32 {
    let capture_filter = env::var(ANNEAL_CAPTURE_FILTER_ENV)
        .ok()
        .filter(|val| !val.trim().is_empty());
    run_with_args_and_filter(raw_args, capture_dir, unit_id_override, capture_filter)
}

/// Runs the compiler driver with explicit arguments, optional capture directory
/// configuration, and optional capture filter patterns.
pub fn run_with_args_and_filter(
    raw_args: &[String],
    capture_dir: Option<PathBuf>,
    unit_id_override: Option<String>,
    capture_filter: Option<String>,
) -> i32 {
    let rustc_args = normalize_wrapper_args(raw_args);

    if let Some(dir) = capture_dir {
        if should_run_capture_for_args(&rustc_args) {
            let mut callbacks =
                AnnealCaptureCallbacks::new(dir, unit_id_override, rustc_args.clone())
                    .with_filter(capture_filter);
            let exit_code = rustc_driver::catch_with_exit_code(|| {
                rustc_driver::run_compiler(&rustc_args, &mut callbacks);
            });
            if let Some(err) = callbacks.capture_error {
                eprintln!("anneal-rustc-capture error: {err}");
                return rustc_driver::EXIT_FAILURE;
            }
            return if exit_code == std::process::ExitCode::SUCCESS {
                rustc_driver::EXIT_SUCCESS
            } else {
                rustc_driver::EXIT_FAILURE
            };
        }
    }

    let mut callbacks = PassThroughCallbacks;
    let exit_code = rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(&rustc_args, &mut callbacks);
    });
    if exit_code == std::process::ExitCode::SUCCESS {
        rustc_driver::EXIT_SUCCESS
    } else {
        rustc_driver::EXIT_FAILURE
    }
}
