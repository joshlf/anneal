//! Obligation assembly and Lean 4 module rendering for generated and authored
//! verification artifacts.
//!
//! Each verified subject item is split across two directories:
//!
//! - `.anneal/generated/` holds disposable modules (`Mir/<Item>.lean`,
//!   `Obligations/<Item>.lean`, and `Verify/<Item>.lean`) regenerated on every
//!   `cargo anneal` run.
//! - `anneal/proofs/` holds optional durable modules (`Specs/<Item>.lean`,
//!   `Assumptions/<Item>.lean`, and `Proof/<Item>.lean`) authored by humans or
//!   agents and preserved across runs without any generate-then-edit stamping.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use anneal_rustc_capture::{CapturedItemKind, UnitTargetRecord};

/// Presence of optional user-authored Lean modules under `anneal/proofs/` for a
/// single verification subject `<Item>`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AuthoredItemModules {
    /// Whether `anneal/proofs/Specs/<Item>.lean` exists on disk.
    pub has_specs: bool,
    /// Whether `anneal/proofs/Specs/<Item>.lean` declares legacy `pre` and
    /// `post` definitions without an `ItemSpec` instance and without importing
    /// `Obligations.<Item>`.
    pub has_legacy_specs_defs: bool,
    /// Whether `anneal/proofs/Assumptions/<Item>.lean` exists on disk.
    pub has_assumptions: bool,
    /// Whether `.anneal/generated/Assumptions/<Item>.lean` was generated from
    /// `#[anneal_spec::spec(trusted, ...)]` in Rust.
    pub has_generated_assumptions: bool,
    /// Whether `anneal/proofs/Proof/<Item>.lean` exists on disk.
    pub has_proof: bool,
    /// Whether the authored specification or proof targets the stateful
    /// contract surface (`StatefulItemSpec` / `StatefulVerificationResult`).
    pub is_stateful: bool,
    /// Whether the authored specification or proof targets the total-correctness
    /// contract surface (`TotalItemSpec` / `TotalVerificationResult`).
    pub is_total: bool,
    /// Whether the authored specification or proof targets the program-to-program
    /// behavioral-equivalence surface (`StatefulEquivItemSpec` /
    /// `StatefulEquivVerificationResult`).
    pub is_equiv: bool,
    /// Whether the authored specification or proof targets the modular
    /// rely–guarantee surface (`ModularItemSpec` / `ModularVerificationResult`).
    pub is_modular: bool,
    /// Whether the authored specification or proof targets the scoped
    /// UB-exception surface (`UbExceptionItemSpec` / `UbExceptionVerificationResult`).
    pub is_ub_exception: bool,
    /// Whether the authored proof or specification targets the universally
    /// quantified polymorphic surface (`polyClaim`, `polyStatefulClaim`,
    /// `polyTotalClaim`, `polyModularClaim`, or `polyUbExceptionClaim`).
    pub is_polymorphic: bool,
}

/// Reference to a sibling verified callee invoked by a subject's MIR body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CalleeContractRef {
    /// Canonical `def_id` of the callee (for example, `"my_crate::leaf"`).
    pub def_id: String,
    /// Dotted Lean module suffix `<Callee>` (for example, `"MyCrate.leaf"`).
    pub item_module_suffix: String,
    /// Optional inline `requires` companion module suffix `<CalleeReq>`.
    pub req_module_suffix: Option<String>,
    /// Optional inline `ensures` companion module suffix `<CalleeEns>`.
    pub ens_module_suffix: Option<String>,
}

/// Reference to a transitive callee MIR body linked into `s.memory.callees`
/// (`defaultCallees`) so `evalTerminator` steps directly into its body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransitiveCalleeRef {
    /// Canonical `def_id` of the callee (for example, `"core::slice::<impl [T]>::len"`).
    pub def_id: String,
    /// Dotted Lean module suffix `<Callee>` (for example, `"Core.slice.len"`).
    pub item_module_suffix: String,
}

/// Reference to an explicit `#[external_spec(for = <target>)]` override
/// excluding `target_def_id` from `defaultCallees` and binding it to a
/// well-typed `MirCallContract`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExternalSpecContractRef {
    /// Canonical `def_id` of the abstracted target function.
    pub target_def_id: String,
    /// Dotted Lean module suffix of the `#[external_spec]` sidecar item.
    pub sidecar_module_suffix: String,
    /// Optional inline `requires` companion module suffix `<ExtReq>`.
    pub req_module_suffix: Option<String>,
    /// Optional inline `ensures` companion module suffix `<ExtEns>`.
    pub ens_module_suffix: Option<String>,
}

/// A captured subject item paired with its canonical `<Item>` module path and
/// all linked specification companion records.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubjectObligationBundle {
    /// Underlying subject item record (`CapturedItemKind::Subject`).
    pub subject: UnitTargetRecord,
    /// Dotted Lean module suffix `<Item>` without the leading category prefix
    /// (for example, `MyCrate.add` for `Mir.MyCrate.add`).
    pub item_module_suffix: String,
    /// Relative `.lean` file path corresponding to `item_module_suffix` (for
    /// example, `MyCrate/add.lean`).
    pub item_rel_path: PathBuf,
    /// Synthetic inline precondition records (`__anodized_fn_requires_*`)
    /// linked to this subject via `associated_subject_def_id`.
    pub inline_requires: Vec<UnitTargetRecord>,
    /// Synthetic inline postcondition records (`__anodized_fn_ensures_*`)
    /// linked to this subject via `associated_subject_def_id`.
    pub inline_ensures: Vec<UnitTargetRecord>,
    /// Synthetic inline qualifier records (`__anodized_fn_qualifiers_*`)
    /// linked to this subject via `associated_subject_def_id`.
    pub inline_qualifiers: Vec<UnitTargetRecord>,
    /// External sidecar specification records (`#[external_spec]`) linked to
    /// this subject via `associated_subject_def_id`.
    pub external_specs: Vec<UnitTargetRecord>,
    /// Sibling verified callees referenced via `.fnDef "<callee_def_id>"` in
    /// this subject's captured MIR body.
    pub called_callees: Vec<CalleeContractRef>,
    /// Transitive closure of reachable captured MIR callees without an active
    /// `#[external_spec]` override, wired into `s.memory.callees` by default.
    pub transitive_callees: Vec<TransitiveCalleeRef>,
    /// Reachable callees overridden by an explicit `#[external_spec(for = ...)]`
    /// declaration, excluded from `s.memory.callees` and abstracted via
    /// `MirCallE` + `externalSpecCallContract`.
    pub external_spec_callees: Vec<ExternalSpecContractRef>,
    /// Transitive closure of captured MIR callees reachable from the `requires`
    /// and `ensures` companion bodies evaluated in this subject's obligations
    /// (`defaultSpecCallees`). Companion predicates that call functions are
    /// evaluated with these bodies linked, so that a call inside a predicate
    /// steps through the callee instead of returning an arbitrary value (which
    /// would make the predicate unsatisfiable and the contract vacuous).
    pub spec_callees: Vec<TransitiveCalleeRef>,
    /// Module suffixes of companion bodies that reference at least one function
    /// and are therefore evaluated with `MirBoolPredicateHoldsWithCallees` over
    /// `defaultSpecCallees`.
    pub spec_companions_with_calls: BTreeSet<String>,
}

impl SubjectObligationBundle {
    /// Return true when this subject was annotated with `#[spec(trusted, ...)]`
    /// or `#[spec(assumed, ...)]` in Rust.
    pub fn has_rust_trusted_attr(&self) -> bool {
        self.external_specs.iter().any(|ext| {
            ext.target
                .def_id
                .contains("__ANNEAL_EXT_SPEC_TARGET___anneal_attr_trusted_")
        })
    }

    /// Return true when this subject was annotated with `#[spec(safe_total, ...)]`
    /// or `#[spec(total: true, ...)]` in Rust.
    pub fn has_rust_safe_total_attr(&self) -> bool {
        self.external_specs.iter().any(|ext| {
            ext.target
                .def_id
                .contains("__ANNEAL_EXT_SPEC_TARGET___anneal_attr_safe_total_")
        })
    }

    /// Return the sibling reference function's Lean module suffix `<Crate>.<ref_fn>`
    /// when this subject was annotated with `#[spec(equivalent_to: <ref_fn>, ...)]`.
    pub fn rust_equiv_target_module_suffix(&self) -> Option<String> {
        const PREFIX: &str = "__ANNEAL_EXT_SPEC_TARGET___anneal_attr_equiv_";
        const SEP: &str = "__for__";
        for ext in &self.external_specs {
            let def_id = &ext.target.def_id;
            if let Some(idx) = def_id.find(PREFIX) {
                let after = &def_id[idx + PREFIX.len()..];
                if let Some(sep_idx) = after.find(SEP) {
                    let ref_ident = sanitize_lean_ident(&after[..sep_idx]);
                    if !ref_ident.is_empty() {
                        if let Some((module_prefix, _)) = self.item_module_suffix.rsplit_once('.') {
                            return Some(format!("{module_prefix}.{ref_ident}"));
                        } else {
                            return Some(ref_ident);
                        }
                    }
                }
            }
        }
        None
    }
}

/// Derive the canonical dotted `<Item>` module suffix from a
/// `UnitTargetRecord`.
///
/// If `record.lean_module_name` begins with `"Mir."`, that prefix is stripped.
/// If `record.lean_module_name` is empty, the suffix is derived from
/// `record.target.mir_module_path` or `record.target.def_id`.
pub fn derive_item_module_suffix(record: &UnitTargetRecord) -> String {
    let trimmed = record.lean_module_name.trim();
    if !trimmed.is_empty() {
        if let Some(stripped) = trimmed.strip_prefix("Mir.") {
            if !stripped.is_empty() {
                return stripped.to_string();
            }
        }
        return trimmed.to_string();
    }

    let from_path = record
        .target
        .mir_module_path
        .trim_start_matches("./")
        .trim_start_matches(".anneal/generated/")
        .trim_start_matches("Mir/")
        .trim_end_matches(".lean")
        .replace('/', ".");
    if !from_path.is_empty() {
        return from_path;
    }

    record
        .target
        .def_id
        .split("::")
        .filter(|s| !s.is_empty())
        .map(sanitize_lean_ident)
        .collect::<Vec<_>>()
        .join(".")
}

/// Convert a dotted `<Item>` module suffix into a relative `.lean` file path.
///
/// For example, `"MyCrate.add"` maps to `PathBuf::from("MyCrate/add.lean")`.
pub fn module_suffix_to_rel_path(item_module_suffix: &str) -> PathBuf {
    let mut path = PathBuf::new();
    let segments: Vec<&str> = item_module_suffix
        .split('.')
        .filter(|s| !s.is_empty())
        .collect();
    if segments.is_empty() {
        path.push("Item.lean");
        return path;
    }
    for seg in &segments[..segments.len() - 1] {
        path.push(seg);
    }
    path.push(format!("{}.lean", segments[segments.len() - 1]));
    path
}

fn sanitize_lean_ident(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len());
    for (idx, ch) in raw.chars().enumerate() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            if idx == 0 && ch.is_ascii_digit() {
                out.push('_');
            }
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() {
        "_item".to_string()
    } else {
        out
    }
}

/// Group captured `UnitTargetRecord` entries by subject item and attach any
/// companion specification records referencing that subject's `def_id`.
///
/// Subject bundles are returned in deterministic lexical order of the subject's
/// `def_id`.
pub fn group_subject_obligations(records: &[UnitTargetRecord]) -> Vec<SubjectObligationBundle> {
    let mut bundles_by_def_id: BTreeMap<String, SubjectObligationBundle> = BTreeMap::new();

    for record in records {
        if matches!(
            record.item_kind,
            CapturedItemKind::Subject | CapturedItemKind::UnsafeTraitImpl
        ) {
            let suffix = derive_item_module_suffix(record);
            let rel_path = module_suffix_to_rel_path(&suffix);
            bundles_by_def_id.insert(
                record.target.def_id.clone(),
                SubjectObligationBundle {
                    subject: record.clone(),
                    item_module_suffix: suffix,
                    item_rel_path: rel_path,
                    inline_requires: Vec::new(),
                    inline_ensures: Vec::new(),
                    inline_qualifiers: Vec::new(),
                    external_specs: Vec::new(),
                    called_callees: Vec::new(),
                    transitive_callees: Vec::new(),
                    external_spec_callees: Vec::new(),
                    spec_callees: Vec::new(),
                    spec_companions_with_calls: BTreeSet::new(),
                },
            );
        }
    }

    for record in records {
        if matches!(
            record.item_kind,
            CapturedItemKind::Subject | CapturedItemKind::UnsafeTraitImpl
        ) {
            continue;
        }
        let Some(ref subject_def_id) = record.associated_subject_def_id else {
            continue;
        };
        let Some(bundle) = bundles_by_def_id.get_mut(subject_def_id) else {
            continue;
        };
        match record.item_kind {
            CapturedItemKind::InlineSpecRequires => bundle.inline_requires.push(record.clone()),
            CapturedItemKind::InlineSpecEnsures => bundle.inline_ensures.push(record.clone()),
            CapturedItemKind::InlineSpecQualifiers => {
                bundle.inline_qualifiers.push(record.clone());
            }
            CapturedItemKind::ExternalSpec => bundle.external_specs.push(record.clone()),
            CapturedItemKind::Subject
            | CapturedItemKind::Model
            | CapturedItemKind::TypeInvariant
            | CapturedItemKind::UnsafeTraitImpl
            | CapturedItemKind::Callee => {}
        }
    }

    for bundle in bundles_by_def_id.values_mut() {
        bundle
            .inline_requires
            .sort_by(|a, b| a.target.def_id.cmp(&b.target.def_id));
        bundle
            .inline_ensures
            .sort_by(|a, b| a.target.def_id.cmp(&b.target.def_id));
        bundle
            .inline_qualifiers
            .sort_by(|a, b| a.target.def_id.cmp(&b.target.def_id));
        bundle
            .external_specs
            .sort_by(|a, b| a.target.def_id.cmp(&b.target.def_id));
    }

    bundles_by_def_id.into_values().collect()
}

/// Item-name prefix of `anodized` `requires` companion functions.
const ANODIZED_REQUIRES_COMPANION_PREFIX: &str = "__anodized_fn_requires_";
/// Item-name prefix of `anodized` `ensures` companion functions.
const ANODIZED_ENSURES_COMPANION_PREFIX: &str = "__anodized_fn_ensures_";

/// Collect all explicit `#[external_spec(for = <target>)]` overrides across
/// `records`, keyed by canonical `target_def_id`.
pub fn collect_external_spec_contracts(
    records: &[UnitTargetRecord],
) -> BTreeMap<String, ExternalSpecContractRef> {
    let mut contracts = BTreeMap::new();
    for record in records {
        if record.item_kind != CapturedItemKind::ExternalSpec || !is_callable_external_spec(record)
        {
            continue;
        }
        let target_def_id = record
            .associated_subject_def_id
            .clone()
            .unwrap_or_else(|| record.target.def_id.clone());
        let sidecar_module_suffix = derive_item_module_suffix(record);
        // `anodized` emits the `requires` / `ensures` companions of a sidecar
        // `<parent>::<ident>` as sibling items
        // `<parent>::__anodized_fn_{requires,ensures}_<ident>`. Match them by
        // exact path: matching by associated subject alone would also pick up
        // the target's own inline `#[spec]` companions (which share the same
        // associated subject) or the companions of another sidecar whose name
        // extends `<ident>`.
        let (sidecar_parent, sidecar_ident) = match record.target.def_id.rsplit_once("::") {
            Some((parent, ident)) => (Some(parent), ident),
            None => (None, record.target.def_id.as_str()),
        };
        let companion_def_id = |prefix: &str| match sidecar_parent {
            Some(parent) => format!("{parent}::{prefix}{sidecar_ident}"),
            None => format!("{prefix}{sidecar_ident}"),
        };
        let req_def_id = companion_def_id(ANODIZED_REQUIRES_COMPANION_PREFIX);
        let ens_def_id = companion_def_id(ANODIZED_ENSURES_COMPANION_PREFIX);

        let mut req_module_suffix = None;
        let mut ens_module_suffix = None;
        for comp in records {
            match comp.item_kind {
                CapturedItemKind::InlineSpecRequires
                    if req_module_suffix.is_none() && comp.target.def_id == req_def_id =>
                {
                    req_module_suffix = Some(derive_item_module_suffix(comp));
                }
                CapturedItemKind::InlineSpecEnsures
                    if ens_module_suffix.is_none() && comp.target.def_id == ens_def_id =>
                {
                    ens_module_suffix = Some(derive_item_module_suffix(comp));
                }
                _ => {}
            }
        }
        contracts.insert(
            target_def_id.clone(),
            ExternalSpecContractRef {
                target_def_id,
                sidecar_module_suffix,
                req_module_suffix,
                ens_module_suffix,
            },
        );
    }
    contracts
}

/// Conjoin a slice of Lean `Prop` clause expressions using `And`, returning
/// `"True"` when `clauses` is empty.
fn conjoin_prop_clauses(clauses: &[String]) -> String {
    match clauses {
        [] => "True".to_string(),
        [single] => single.clone(),
        [first, rest @ ..] => {
            format!("And ({first}) ({})", conjoin_prop_clauses(rest))
        }
    }
}

/// Return true when an `#[external_spec]` companion record represents a
/// callable companion body rather than a synthetic marker constant.
fn is_callable_external_spec(record: &UnitTargetRecord) -> bool {
    !record.target.mir_module_path.is_empty()
        && !record.target.def_id.contains("__ANNEAL_EXT_SPEC_TARGET_")
}

/// Render the Lean proposition asserting that the boolean companion predicate
/// `Mir.<companion_suffix>.body` holds on `args_expr`.
///
/// Companions that call functions are evaluated with `defaultSpecCallees`
/// linked (`MirBoolPredicateHoldsWithCallees`); call-free companions keep the
/// plain `MirBoolPredicateHolds` form, which is definitionally the same
/// predicate with no linked callees.
fn render_companion_predicate(
    bundle: &SubjectObligationBundle,
    companion_suffix: &str,
    args_expr: &str,
) -> String {
    if !bundle.spec_callees.is_empty()
        && bundle.spec_companions_with_calls.contains(companion_suffix)
    {
        format!(
            "MirBoolPredicateHoldsWithCallees Mir.{companion_suffix}.body defaultSpecCallees {args_expr}"
        )
    } else {
        format!("MirBoolPredicateHolds Mir.{companion_suffix}.body {args_expr}")
    }
}

/// Render the Lean proposition asserting that the polymorphic boolean companion
/// predicate `(Mir.<companion_suffix>.body.instantiate typeArgs)` holds on `args_expr`.
fn render_companion_predicate_for(
    bundle: &SubjectObligationBundle,
    companion_suffix: &str,
    type_args_expr: &str,
    args_expr: &str,
) -> String {
    if !bundle.spec_callees.is_empty()
        && bundle.spec_companions_with_calls.contains(companion_suffix)
    {
        format!(
            "MirBoolPredicateHoldsWithCallees (Mir.{companion_suffix}.body.instantiate {type_args_expr}) defaultSpecCallees {args_expr}"
        )
    } else {
        format!(
            "MirBoolPredicateHolds (Mir.{companion_suffix}.body.instantiate {type_args_expr}) {args_expr}"
        )
    }
}

/// Lean identifier of the `externalSpecCallContract` definition emitted for
/// `ext` in an `Obligations.<Item>` module.
pub(crate) fn external_call_contract_ident(ext: &ExternalSpecContractRef) -> String {
    format!(
        "externalCallContract_{}",
        sanitize_lean_ident(&ext.sidecar_module_suffix)
    )
}

/// Render `defaultModularSpec.envAssumed` for `bundle`: the conjunction of
/// `holdsOn` for every `#[external_spec]` contract abstracting a reachable
/// callee and every verified sibling callee contract.
///
/// Every contract's precondition is guarded by `req.defPath`, so the
/// conjunction constrains each abstracted callee independently. A single
/// contract keeps the bare `<contract>.holdsOn` form expected by the automatic
/// modular discharge combinators.
fn render_default_env_assumed(bundle: &SubjectObligationBundle) -> String {
    let mut contracts: Vec<String> = bundle
        .external_spec_callees
        .iter()
        .map(external_call_contract_ident)
        .collect();
    contracts.extend(bundle.called_callees.iter().map(|callee| {
        format!("Obligations.{}.defaultCallContract", callee.item_module_suffix)
    }));
    match contracts.as_slice() {
        [] => "fun _ => True".to_string(),
        [single] => format!("{single}.holdsOn"),
        many => {
            let clauses: Vec<String> = many.iter().map(|c| format!("{c}.holdsOn h")).collect();
            format!("fun h => {}", conjoin_prop_clauses(&clauses))
        }
    }
}

/// Render the disposable `.anneal/generated/Obligations/<Item>.lean` module for
/// `bundle` with default authored-module settings.
pub fn render_obligations_module(bundle: &SubjectObligationBundle) -> String {
    render_obligations_module_with_options(bundle, AuthoredItemModules::default())
}

/// Render the disposable `.anneal/generated/Obligations/<Item>.lean` module for
/// `bundle` and `authored`.
///
/// This module is regenerated on every run. It imports only `Init.Core`,
/// `Trusted`, `Mir.<Item>`, and linked companion `Mir.*` modules so that no
/// constant from `Anneal.*` (`theory/`) can ever enter the theorem statement of
/// `Verify.<Item>.verified`. It registers a `priority := low` `defaultSpec`
/// instance of `ItemSpec "<def_id>"` using `MirBoolPredicateHolds` and defines
/// `claim [spec : ItemSpec "<def_id>"] : Claim`.
pub fn render_obligations_module_with_options(
    bundle: &SubjectObligationBundle,
    authored: AuthoredItemModules,
) -> String {
    let item = &bundle.item_module_suffix;
    let def_id = &bundle.subject.target.def_id;
    let mut out = String::new();

    out.push_str("import Trusted\n");
    out.push_str(&format!("import Mir.{item}\n"));

    let mut imported_companions: BTreeSet<String> = BTreeSet::new();
    for req in &bundle.inline_requires {
        let req_suffix = derive_item_module_suffix(req);
        if req_suffix != *item && imported_companions.insert(req_suffix.clone()) {
            out.push_str(&format!("import Mir.{req_suffix}\n"));
        }
    }
    for ens in &bundle.inline_ensures {
        let ens_suffix = derive_item_module_suffix(ens);
        if ens_suffix != *item && imported_companions.insert(ens_suffix.clone()) {
            out.push_str(&format!("import Mir.{ens_suffix}\n"));
        }
    }
    for ext in &bundle.external_specs {
        if is_callable_external_spec(ext) {
            let ext_suffix = derive_item_module_suffix(ext);
            if ext_suffix != *item && imported_companions.insert(ext_suffix.clone()) {
                out.push_str(&format!("import Mir.{ext_suffix}\n"));
            }
        }
    }
    if let Some(ref_suffix) = bundle.rust_equiv_target_module_suffix()
        && ref_suffix != *item
        && imported_companions.insert(ref_suffix.clone())
    {
        out.push_str(&format!("import Mir.{ref_suffix}\n"));
    }
    for callee in &bundle.transitive_callees {
        if callee.item_module_suffix != *item
            && imported_companions.insert(callee.item_module_suffix.clone())
        {
            out.push_str(&format!("import Mir.{}\n", callee.item_module_suffix));
        }
    }
    for ext in &bundle.external_spec_callees {
        if ext.sidecar_module_suffix != *item
            && imported_companions.insert(ext.sidecar_module_suffix.clone())
        {
            out.push_str(&format!("import Mir.{}\n", ext.sidecar_module_suffix));
        }
        if let Some(ref req_suf) = ext.req_module_suffix
            && req_suf != item
            && imported_companions.insert(req_suf.clone())
        {
            out.push_str(&format!("import Mir.{req_suf}\n"));
        }
        if let Some(ref ens_suf) = ext.ens_module_suffix
            && ens_suf != item
            && imported_companions.insert(ens_suf.clone())
        {
            out.push_str(&format!("import Mir.{ens_suf}\n"));
        }
    }
    for callee in &bundle.spec_callees {
        if callee.item_module_suffix != *item
            && imported_companions.insert(callee.item_module_suffix.clone())
        {
            out.push_str(&format!("import Mir.{}\n", callee.item_module_suffix));
        }
    }

    let mut imported_obligations: BTreeSet<String> = BTreeSet::new();
    for callee in &bundle.called_callees {
        if callee.item_module_suffix != *item
            && imported_obligations.insert(callee.item_module_suffix.clone())
        {
            out.push_str(&format!("import Obligations.{}\n", callee.item_module_suffix));
        }
    }

    if authored.has_legacy_specs_defs {
        out.push_str(&format!("import Specs.{item}\n"));
    }

    out.push_str(&format!("\nnamespace Obligations.{item}\n\n"));
    out.push_str("set_option linter.unusedVariables false\n\n");
    out.push_str("open Trusted.MirAst\n");
    out.push_str("open Trusted.MirSemantics\n");
    out.push_str("open Trusted.VerificationResult\n\n");

    out.push_str("/-!\n");
    out.push_str(&format!(
        "Disposable verification obligations for `{def_id}`.\n\n"
    ));
    out.push_str(
        "This file is generated on every `cargo anneal` run. Do not edit it by\n\
         hand; declare an `ItemSpec` instance in `Specs.",
    );
    out.push_str(item);
    out.push_str("` or discharge the proof in `Proof.");
    out.push_str(item);
    out.push_str("`.\n");

    if !bundle.inline_requires.is_empty()
        || !bundle.inline_ensures.is_empty()
        || !bundle.external_specs.is_empty()
    {
        out.push_str("\nLinked specification companion items:\n");
        for req in &bundle.inline_requires {
            out.push_str(&format!(
                "- Inline requires: `{}` (`{}`)\n",
                req.target.def_id, req.lean_module_name
            ));
        }
        for ens in &bundle.inline_ensures {
            out.push_str(&format!(
                "- Inline ensures: `{}` (`{}`)\n",
                ens.target.def_id, ens.lean_module_name
            ));
        }
        for ext in &bundle.external_specs {
            out.push_str(&format!(
                "- External spec: `{}` (`{}`)\n",
                ext.target.def_id, ext.lean_module_name
            ));
        }
    }
    out.push_str("-/\n\n");

    let has_contract_companions =
        !bundle.inline_requires.is_empty() || !bundle.inline_ensures.is_empty();

    if !bundle.spec_callees.is_empty() {
        let elems: Vec<String> = bundle
            .spec_callees
            .iter()
            .map(|c| format!("Mir.{}.body", c.item_module_suffix))
            .collect();
        out.push_str(&format!(
            "/-- Transitive callee table linked while evaluating the `requires` /\n    \
                `ensures` companion predicates of `{def_id}`, so that calls inside\n    \
                a predicate step through the callee bodies. -/\n\
             def defaultSpecCallees : List CapturedMir :=\n  \
               [{}]\n\n",
            elems.join(", ")
        ));
    }

    let default_pre_expr = if has_contract_companions {
        let mut clauses = Vec::with_capacity(bundle.inline_requires.len() + 1);
        clauses.push(format!(
            "Trusted.Sequence.length args = Mir.{item}.body.argCount"
        ));
        for req in &bundle.inline_requires {
            let req_suffix = derive_item_module_suffix(req);
            clauses.push(render_companion_predicate(bundle, &req_suffix, "args"));
        }
        conjoin_prop_clauses(&clauses)
    } else {
        "True".to_string()
    };

    let default_post_expr = if !bundle.inline_ensures.is_empty() {
        let clauses: Vec<String> = bundle
            .inline_ensures
            .iter()
            .map(|ens| {
                let ens_suffix = derive_item_module_suffix(ens);
                render_companion_predicate(
                    bundle,
                    &ens_suffix,
                    "(List.append args (List.cons ret List.nil))",
                )
            })
            .collect();
        conjoin_prop_clauses(&clauses)
    } else {
        "True".to_string()
    };

    let default_pre_for_expr = if has_contract_companions {
        let mut clauses = Vec::with_capacity(bundle.inline_requires.len() + 1);
        clauses.push(format!(
            "Trusted.Sequence.length args = (Mir.{item}.body.instantiate typeArgs).argCount"
        ));
        for req in &bundle.inline_requires {
            let req_suffix = derive_item_module_suffix(req);
            clauses.push(render_companion_predicate_for(
                bundle,
                &req_suffix,
                "typeArgs",
                "args",
            ));
        }
        conjoin_prop_clauses(&clauses)
    } else {
        "True".to_string()
    };

    let default_post_for_expr = if !bundle.inline_ensures.is_empty() {
        let clauses: Vec<String> = bundle
            .inline_ensures
            .iter()
            .map(|ens| {
                let ens_suffix = derive_item_module_suffix(ens);
                render_companion_predicate_for(
                    bundle,
                    &ens_suffix,
                    "typeArgs",
                    "(List.append args (List.cons ret List.nil))",
                )
            })
            .collect();
        conjoin_prop_clauses(&clauses)
    } else {
        "True".to_string()
    };

    out.push_str(&format!(
        "/-- Default precondition lowered automatically from Rust `#[spec]` /\n    \
            `#[external_spec]` `requires` companions for `{def_id}` (or `True`\n    \
            when no companion contract is present). -/\n"
    ));
    out.push_str("def defaultPre (args : List Value) : Prop :=\n");
    out.push_str(&format!("  {default_pre_expr}\n\n"));

    out.push_str(&format!(
        "/-- Default postcondition lowered automatically from Rust `#[spec]` /\n    \
            `#[external_spec]` `ensures` companions for `{def_id}` (or `True`\n    \
            when no companion contract is present). -/\n"
    ));
    out.push_str("def defaultPost (args : List Value) (ret : Value) : Prop :=\n");
    out.push_str(&format!("  {default_post_expr}\n\n"));

    out.push_str(&format!(
        "/-- Polymorphic default precondition for `{def_id}` instantiated at\n    \
            `typeArgs : Trusted.MirAst.TypeSubst`. -/\n\
         @[reducible, simp]\n\
         def defaultPreFor\n    \
             (typeArgs : Trusted.MirAst.TypeSubst)\n    \
             (args : List Value) : Prop :=\n  \
           {default_pre_for_expr}\n\n\
         /-- Polymorphic default postcondition for `{def_id}` instantiated at\n    \
             `typeArgs : Trusted.MirAst.TypeSubst`. -/\n\
         @[reducible, simp]\n\
         def defaultPostFor\n    \
             (typeArgs : Trusted.MirAst.TypeSubst)\n    \
             (args : List Value)\n    \
             (ret : Value) : Prop :=\n  \
           {default_post_for_expr}\n\n"
    ));

    out.push_str(&format!(
        "/-- Trusted `requires` predicate lowered from companion `#[spec]` and\n    \
            `#[external_spec]` items for `{def_id}`. -/\n"
    ));
    out.push_str("abbrev rustRequires : List Value → Prop := defaultPre\n\n");

    out.push_str(&format!(
        "/-- Trusted `ensures` relation lowered from companion `#[spec]` and\n    \
            `#[external_spec]` items for `{def_id}`. -/\n"
    ));
    out.push_str("abbrev rustEnsures : List Value → Value → Prop := defaultPost\n\n");

    out.push_str(&format!(
        "/-- Canonical external call contract for `{def_id}` lowered from\n    \
            `defaultPre` and `defaultPost` so modular callers can assume this\n    \
            callee's Rust `#[spec]` contract at `MirCallE` call sites. -/\n\
         def defaultCallContract : MirCallContract where\n  \
           pre req :=\n    \
             And (req.defPath = \"{def_id}\") (defaultPre req.args)\n  \
           post req ans :=\n    \
             ∃ retVal,\n      \
               And (ans = .returned retVal req.memory) (defaultPost req.args retVal)\n\n"
    ));

    out.push_str(&format!(
        "/-- Low-priority default `ItemSpec` instance for `{def_id}`.\n    \
            An authored normal-priority `ItemSpec` instance in `Specs.{item}`\n    \
            automatically overrides this instance via Lean typeclass\n    \
            synthesis. -/\n"
    ));
    out.push_str(&format!(
        "instance (priority := low) defaultSpec : ItemSpec \"{def_id}\" where\n  \
           pre := defaultPre\n  \
           post := defaultPost\n\n"
    ));

    out.push_str(&format!(
        "/-- Signature-typed stateful precondition for `{def_id}` instantiated at\n    \
            `typeArgs : Trusted.MirAst.TypeSubst`. -/\n\
         @[reducible, simp]\n\
         def sigPre\n    \
             (typeArgs : Trusted.MirAst.TypeSubst)\n    \
             (args : List Value)\n    \
             (mem : Memory) : Prop :=\n  \
           And (defaultPreFor typeArgs args)\n      \
               (Trusted.VerificationResult.argsMatchSignature\n        \
                 (Mir.{item}.body.instantiate typeArgs) args mem)\n\n\
         /-- Signature-typed stateful postcondition for `{def_id}` instantiated at\n    \
             `typeArgs : Trusted.MirAst.TypeSubst`. -/\n\
         @[reducible, simp]\n\
         def sigPost\n    \
             (typeArgs : Trusted.MirAst.TypeSubst)\n    \
             (args : List Value)\n    \
             (ret : Value)\n    \
             (mem : Memory) : Prop :=\n  \
           And (defaultPostFor typeArgs args ret)\n      \
               (Trusted.VerificationResult.retMatchesSignature\n        \
                 (Mir.{item}.body.instantiate typeArgs) ret mem)\n\n\
         /-- Low-priority default `StatefulItemSpec` instance for `{def_id}`. -/\n"
    ));
    out.push_str(&format!(
        "instance (priority := low) defaultStatefulSpec :\n    \
           StatefulItemSpec \"{def_id}\" where\n  \
           pre := fun args mem => sigPre List.nil args mem\n  \
           post := fun args _ ret mem => sigPost List.nil args ret mem\n\n"
    ));

    out.push_str(&format!(
        "/-- Low-priority default `TotalItemSpec` instance for `{def_id}`. -/\n"
    ));
    out.push_str(&format!(
        "instance (priority := low) defaultTotalSpec :\n    \
           TotalItemSpec \"{def_id}\" where\n  \
           pre := fun args mem =>\n    \
             And (And (defaultPre args) (mem = (initMachineState Mir.{item}.body args).memory))\n    \
                 (Trusted.VerificationResult.argsMatchSignature (Mir.{item}.body.instantiate List.nil) args mem)\n  \
           post := fun args _ ret _ => defaultPost args ret\n\n"
    ));

    let default_callees_expr = if bundle.transitive_callees.is_empty() {
        ".nil".to_string()
    } else {
        let elems: Vec<String> = bundle
            .transitive_callees
            .iter()
            .map(|c| format!("Mir.{}.body", c.item_module_suffix))
            .collect();
        format!("[{}]", elems.join(", "))
    };
    out.push_str(&format!(
        "/-- Default transitive callee table (`s.memory.callees`) for `{def_id}`,\n    \
            containing all reachable captured MIR bodies without an explicit\n    \
            `#[external_spec]` override. -/\n\
         def defaultCallees : List CapturedMir :=\n  \
           {default_callees_expr}\n\n"
    ));

    for (idx, ext) in bundle.external_spec_callees.iter().enumerate() {
        let contract_ident = external_call_contract_ident(ext);
        let extra_pre = if let Some(ref req_suf) = ext.req_module_suffix {
            format!(
                "(fun args => {})",
                render_companion_predicate(bundle, req_suf, "args")
            )
        } else {
            "(fun _ => True)".to_string()
        };
        let extra_post = if let Some(ref ens_suf) = ext.ens_module_suffix {
            format!(
                "(fun args ret => {})",
                render_companion_predicate(
                    bundle,
                    ens_suf,
                    "(List.append args (List.cons ret List.nil))"
                )
            )
        } else {
            "(fun _ _ => True)".to_string()
        };
        out.push_str(&format!(
            "/-- Well-typed external call contract for `{}` lowered from\n    \
                `#[external_spec]` sidecar `Mir.{}`. -/\n\
             def {contract_ident} : MirCallContract :=\n  \
               externalSpecCallContract\n    \
                 \"{}\"\n    \
                 Mir.{}.body\n    \
                 {extra_pre}\n    \
                 {extra_post}\n\n",
            ext.target_def_id,
            ext.sidecar_module_suffix,
            ext.target_def_id,
            ext.sidecar_module_suffix,
        ));
        if idx == 0 {
            out.push_str(&format!(
                "/-- Primary `#[external_spec]` call contract for `{def_id}`. -/\n\
                 abbrev defaultExternalCallContract : MirCallContract := {contract_ident}\n\n"
            ));
        }
    }

    let default_env_assumed = render_default_env_assumed(bundle);

    out.push_str(&format!(
        "/-- Low-priority default `ModularItemSpec` instance for `{def_id}`. -/\n"
    ));
    out.push_str(&format!(
        "instance (priority := low) defaultModularSpec :\n    \
           ModularItemSpec \"{def_id}\" where\n  \
           envAssumed := {default_env_assumed}\n  \
           pre := fun args mem =>\n    \
             And (And (defaultPre args) (mem = (initMachineState Mir.{item}.body args).memory))\n    \
                 (Trusted.VerificationResult.argsMatchSignature (Mir.{item}.body.instantiate List.nil) args mem)\n  \
           post := fun args _ ret _ => defaultPost args ret\n\n"
    ));

    out.push_str(&format!(
        "/-- Low-priority default `UbExceptionItemSpec` instance for `{def_id}`. -/\n"
    ));
    out.push_str(&format!(
        "instance (priority := low) defaultUbExceptionSpec :\n    \
           UbExceptionItemSpec \"{def_id}\" where\n  \
           pre := fun args mem => sigPre List.nil args mem\n  \
           strictSafetyPre := fun _ _ => False\n  \
           post := fun args _ ret mem => sigPost List.nil args ret mem\n\n"
    ));

    out.push_str(&format!(
        "/-- Refine `defaultSpec` by conjoining additional Lean `extraPre` and\n    \
            `extraPost` clauses while preserving `rustRequires` and `rustEnsures`. -/\n\
         @[instance_reducible]\n         def refineSpec\n    \
             (extraPre : List Value → Prop)\n    \
             (extraPost : List Value → Value → Prop) :\n    \
             ItemSpec \"{def_id}\" where\n  \
           pre args := And (rustRequires args) (extraPre args)\n  \
           post args ret := And (rustEnsures args ret) (extraPost args ret)\n\n\
         /-- Refine `defaultStatefulSpec` by conjoining additional stateful Lean\n    \
             `extraPre` and `extraPost` clauses while preserving `rustRequires` and\n    \
             `rustEnsures`. -/\n\
         @[instance_reducible]\n         def refineStatefulSpec\n    \
             (extraPre : List Value → Memory → Prop)\n    \
             (extraPost : List Value → Memory → Value → Memory → Prop) :\n    \
             StatefulItemSpec \"{def_id}\" where\n  \
           pre args m := And (rustRequires args) (extraPre args m)\n  \
           post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)\n\n\
         /-- Refine `defaultSpec` for a safe function whose execution is defined\n    \
             (`MirNoUB`, `.defined` of `Partial`) across `safetyDomain` while guarding\n    \
             `rustEnsures` and `extraPost` behind `rustRequires` and `extraPre` inside\n    \
             `.val` (`#125`). -/\n\
         @[instance_reducible]\n         def refineSafeSpec\n    \
             (safetyDomain : List Value → Prop)\n    \
             (extraPre : List Value → Prop)\n    \
             (extraPost : List Value → Value → Prop) :\n    \
             ItemSpec \"{def_id}\" where\n  \
           pre args := safetyDomain args\n  \
           post args ret :=\n    \
             And (rustRequires args) (extraPre args) →\n      \
               And (rustEnsures args ret) (extraPost args ret)\n\n\
         /-- Refine `defaultStatefulSpec` for a safe stateful function whose execution\n    \
             is defined (`MirNoUB`, `.defined` of `Partial`) across `safetyDomain`\n    \
             while guarding `rustEnsures` and `extraPost` behind `rustRequires` and\n    \
             `extraPre` inside `.val` (`#125`). -/\n\
         @[instance_reducible]\n         def refineSafeStatefulSpec\n    \
             (safetyDomain : List Value → Memory → Prop)\n    \
             (extraPre : List Value → Memory → Prop)\n    \
             (extraPost : List Value → Memory → Value → Memory → Prop) :\n    \
             StatefulItemSpec \"{def_id}\" where\n  \
           pre args m := safetyDomain args m\n  \
           post args m0 ret m1 :=\n    \
             And (rustRequires args) (extraPre args m0) →\n      \
               And (rustEnsures args ret) (extraPost args m0 ret m1)\n\n\
         /-- Refine `defaultTotalSpec` by conjoining additional stateful Lean\n    \
             `extraPre` and `extraPost` clauses while preserving `rustRequires` and\n    \
             `rustEnsures`. -/\n\
         @[instance_reducible]\n         def refineTotalSpec\n    \
             (extraPre : List Value → Memory → Prop)\n    \
             (extraPost : List Value → Memory → Value → Memory → Prop) :\n    \
             TotalItemSpec \"{def_id}\" where\n  \
           pre args m := And (rustRequires args) (extraPre args m)\n  \
           post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)\n\n\
         /-- Specify program-to-program behavioral equivalence and total correctness\n    \
             against reference `specBody` while preserving `rustRequires` and\n    \
             `rustEnsures`. -/\n\
         @[instance_reducible]\n         def refineEquivSpec\n    \
             (specBody : CapturedMir)\n    \
             (extraPre : List Value → Memory → Prop)\n    \
             (extraPost : List Value → Memory → Value → Memory → Prop) :\n    \
             StatefulEquivItemSpec \"{def_id}\" where\n  \
           specBody := specBody\n  \
           pre args m := And (rustRequires args) (extraPre args m)\n  \
           post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)\n\n\
         /-- Refine `defaultModularSpec` by supplying `envAssumed` and conjoining\n    \
             additional stateful Lean `extraPre` and `extraPost` clauses while\n    \
             preserving `rustRequires` and `rustEnsures`. -/\n\
         @[instance_reducible]\n         def refineModularSpec\n    \
             (envAssumed : ExternalCallHandler → Prop)\n    \
             (extraPre : List Value → Memory → Prop)\n    \
             (extraPost : List Value → Memory → Value → Memory → Prop) :\n    \
             ModularItemSpec \"{def_id}\" where\n  \
           envAssumed := envAssumed\n  \
           pre args m := And (rustRequires args) (extraPre args m)\n  \
           post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)\n\n\
         /-- Refine `defaultUbExceptionSpec` by supplying the strict-safety subdomain\n    \
             `strictSafetyPre` and conjoining additional stateful Lean `extraPre` and\n    \
             `extraPost` clauses while preserving `rustRequires` and `rustEnsures`. -/\n\
         @[instance_reducible]\n         def refineUbExceptionSpec\n    \
             (strictSafetyPre : List Value → Memory → Prop)\n    \
             (extraPre : List Value → Memory → Prop)\n    \
             (extraPost : List Value → Memory → Value → Memory → Prop) :\n    \
             UbExceptionItemSpec \"{def_id}\" where\n  \
           pre args m := And (rustRequires args) (extraPre args m)\n  \
           strictSafetyPre := strictSafetyPre\n  \
           post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)\n\n"
    ));

    if !authored.has_specs {
        if bundle.has_rust_safe_total_attr() {
            out.push_str(&format!(
                "/-- Safe-function total-safety `ItemSpec` instance lowered from\n    \
                    `#[spec(safe_total, ...)]` for `{def_id}` (`#125`). -/\n\
                 instance rustSafeTotalSpec : ItemSpec \"{def_id}\" :=\n  \
                   refineSafeSpec\n    \
                     (fun args => Trusted.Sequence.length args = Mir.{item}.body.argCount)\n    \
                     (fun _ => True)\n    \
                     (fun _ _ => True)\n\n\
                 /-- Safe-function total-safety `StatefulItemSpec` instance lowered from\n    \
                     `#[spec(safe_total, ...)]` for `{def_id}` (`#125`). -/\n\
                 instance rustSafeTotalStatefulSpec : StatefulItemSpec \"{def_id}\" :=\n  \
                   refineSafeStatefulSpec\n    \
                     (fun args _ => Trusted.Sequence.length args = Mir.{item}.body.argCount)\n    \
                     (fun _ _ => True)\n    \
                     (fun _ _ _ _ => True)\n\n"
            ));
        }
        if let Some(ref_suffix) = bundle.rust_equiv_target_module_suffix() {
            out.push_str(&format!(
                "/-- Program-to-program behavioral-equivalence `StatefulEquivItemSpec`\n    \
                    instance lowered from `#[spec(equivalent_to: ...)]` for `{def_id}`. -/\n\
                 instance rustEquivSpec : StatefulEquivItemSpec \"{def_id}\" :=\n  \
                   refineEquivSpec\n    \
                     Mir.{ref_suffix}.body\n    \
                     (fun _ _ => True)\n    \
                     (fun _ _ _ _ => True)\n\n"
            ));
        }
    }

    if authored.has_legacy_specs_defs {
        out.push_str(&format!(
            "/-- Bridge instance synthesizing `ItemSpec \"{def_id}\"` from\n    \
                `Specs.{item}.pre` and `Specs.{item}.post`. -/\n\
             instance legacySpec : ItemSpec \"{def_id}\" where\n  \
               pre := Specs.{item}.pre\n  \
               post := Specs.{item}.post\n\n"
        ));
    }

    out.push_str(&format!(
        "/-- Canonical verification claim for `{def_id}` synthesized from\n    \
            `ItemSpec \"{def_id}\"`. -/\n"
    ));
    out.push_str(&format!(
        "def claim [spec : ItemSpec \"{def_id}\"] : Claim :=\n  \
           {{ body := Mir.{item}.body, pre := spec.pre, post := spec.post, callees := defaultCallees }}\n\n"
    ));

    out.push_str(&format!(
        "/-- Canonical stateful verification claim for `{def_id}` synthesized\n    \
            from `StatefulItemSpec \"{def_id}\"`. -/\n"
    ));
    out.push_str(&format!(
        "def statefulClaim [spec : StatefulItemSpec \"{def_id}\"] : StatefulClaim :=\n  \
           {{ body := Mir.{item}.body, pre := spec.pre, post := spec.post, callees := defaultCallees }}\n\n"
    ));

    out.push_str(&format!(
        "/-- Canonical total-correctness verification claim for `{def_id}` synthesized\n    \
            from `TotalItemSpec \"{def_id}\"`. -/\n"
    ));
    out.push_str(&format!(
        "def totalClaim [spec : TotalItemSpec \"{def_id}\"] : TotalClaim :=\n  \
           {{ body := Mir.{item}.body, pre := spec.pre, post := spec.post, callees := defaultCallees }}\n\n"
    ));

    out.push_str(&format!(
        "/-- Canonical program-to-program equivalence claim for `{def_id}` synthesized\n    \
            from `StatefulEquivItemSpec \"{def_id}\"`. -/\n"
    ));
    out.push_str(&format!(
        "def equivClaim [spec : StatefulEquivItemSpec \"{def_id}\"] : StatefulEquivClaim :=\n  \
           {{ implBody := Mir.{item}.body, specBody := spec.specBody, pre := spec.pre, post := spec.post, implCallees := defaultCallees, specCallees := defaultCallees }}\n\n"
    ));

    out.push_str(&format!(
        "/-- Canonical modular verification claim for `{def_id}` synthesized\n    \
            from `ModularItemSpec \"{def_id}\"`. -/\n"
    ));
    out.push_str(&format!(
        "def modularClaim [spec : ModularItemSpec \"{def_id}\"] : ModularClaim :=\n  \
           {{ body := Mir.{item}.body, envAssumed := spec.envAssumed, pre := spec.pre, post := spec.post, callees := defaultCallees }}\n\n"
    ));

    out.push_str(&format!(
        "/-- Canonical scoped UB-exception verification claim for `{def_id}` synthesized\n    \
            from `UbExceptionItemSpec \"{def_id}\"`. -/\n"
    ));
    out.push_str(&format!(
        "def ubExceptionClaim [spec : UbExceptionItemSpec \"{def_id}\"] : UbExceptionClaim :=\n  \
           {{ body := Mir.{item}.body, pre := spec.pre, strictSafetyPre := spec.strictSafetyPre, post := spec.post, callees := defaultCallees }}\n\n"
    ));

    let sha = &bundle.subject.target.mir_module_sha256;
    out.push_str(&format!(
        "/-- Verification claim for `{def_id}` instantiated at `typeArgs`. -/\n\
         def claimFor\n    \
             [spec : ItemSpec \"{def_id}\"]\n    \
             (typeArgs : Trusted.MirAst.TypeSubst) : Claim :=\n  \
           {{ body := Mir.{item}.body.instantiate typeArgs\n    \
             pre := fun args =>\n      \
               And (spec.pre args)\n          \
                   (Trusted.VerificationResult.argsMatchSignature\n            \
                     (Mir.{item}.body.instantiate typeArgs)\n            \
                     args\n            \
                     (initMachineState (Mir.{item}.body.instantiate typeArgs) args).memory)\n    \
             post := fun args ret =>\n      \
               And (spec.post args ret)\n          \
                   (Trusted.VerificationResult.retMatchesSignature\n            \
                     (Mir.{item}.body.instantiate typeArgs)\n            \
                     ret\n            \
                     (initMachineState (Mir.{item}.body.instantiate typeArgs) args).memory)\n    \
             callees := defaultCallees }}\n\n\
         /-- Universally quantified polymorphic verification proposition for `{def_id}`\n    \
             over all `typeArgs : Trusted.MirAst.TypeSubst` of length\n    \
             `Mir.{item}.body.typeParamCount`. -/\n\
         def polyClaim [spec : ItemSpec \"{def_id}\"] : Prop :=\n  \
           ∀ (typeArgs : Trusted.MirAst.TypeSubst),\n    \
             typeArgs.length = Mir.{item}.body.typeParamCount →\n      \
               VerificationResult (claimFor typeArgs)\n\n\
         /-- Stateful verification claim for `{def_id}` instantiated at `typeArgs`. -/\n\
         def statefulClaimFor (typeArgs : Trusted.MirAst.TypeSubst) : StatefulClaim :=\n  \
           {{ body := Mir.{item}.body.instantiate typeArgs\n    \
             pre := fun args mem => sigPre typeArgs args mem\n    \
             post := fun args _ ret mem => sigPost typeArgs args ret mem\n    \
             callees := defaultCallees }}\n\n\
         /-- Universally quantified polymorphic stateful verification proposition for\n    \
             `{def_id}` over all `typeArgs : Trusted.MirAst.TypeSubst` of length\n    \
             `Mir.{item}.body.typeParamCount`. -/\n\
         def polyStatefulClaim : Prop :=\n  \
           ∀ (typeArgs : Trusted.MirAst.TypeSubst),\n    \
             typeArgs.length = Mir.{item}.body.typeParamCount →\n      \
               StatefulVerificationResult (statefulClaimFor typeArgs)\n\n\
         /-- Total-correctness verification claim for `{def_id}` instantiated at\n    \
             `typeArgs`. -/\n\
         def totalClaimFor (typeArgs : Trusted.MirAst.TypeSubst) : TotalClaim :=\n  \
           {{ body := Mir.{item}.body.instantiate typeArgs\n    \
             pre := fun args mem =>\n      \
               And (And (defaultPreFor typeArgs args)\n                \
                        (mem = (initMachineState (Mir.{item}.body.instantiate typeArgs) args).memory))\n          \
                   (Trusted.VerificationResult.argsMatchSignature\n            \
                     (Mir.{item}.body.instantiate typeArgs) args mem)\n    \
             post := fun args _ ret mem => sigPost typeArgs args ret mem\n    \
             callees := defaultCallees }}\n\n\
         /-- Universally quantified polymorphic total-correctness verification\n    \
             proposition for `{def_id}` over all `typeArgs : Trusted.MirAst.TypeSubst`\n    \
             of length `Mir.{item}.body.typeParamCount`. -/\n\
         def polyTotalClaim : Prop :=\n  \
           ∀ (typeArgs : Trusted.MirAst.TypeSubst),\n    \
             typeArgs.length = Mir.{item}.body.typeParamCount →\n      \
               TotalVerificationResult (totalClaimFor typeArgs)\n\n\
         /-- Modular verification claim for `{def_id}` instantiated at `typeArgs`. -/\n\
         def modularClaimFor\n    \
             [spec : ModularItemSpec \"{def_id}\"]\n    \
             (typeArgs : Trusted.MirAst.TypeSubst) : ModularClaim :=\n  \
           {{ body := Mir.{item}.body.instantiate typeArgs\n    \
             envAssumed := spec.envAssumed\n    \
             pre := fun args mem => sigPre typeArgs args mem\n    \
             post := fun args _ ret m1 => sigPost typeArgs args ret m1\n    \
             callees := defaultCallees }}\n\n\
         /-- Universally quantified polymorphic modular verification proposition for\n    \
             `{def_id}` over all `typeArgs : Trusted.MirAst.TypeSubst` of length\n    \
             `Mir.{item}.body.typeParamCount`. -/\n\
         def polyModularClaim [spec : ModularItemSpec \"{def_id}\"] : Prop :=\n  \
           ∀ (typeArgs : Trusted.MirAst.TypeSubst),\n    \
             typeArgs.length = Mir.{item}.body.typeParamCount →\n      \
               ModularVerificationResult (modularClaimFor typeArgs)\n\n\
         /-- Scoped UB-exception verification claim for `{def_id}` instantiated at\n    \
             `typeArgs`. -/\n\
         def ubExceptionClaimFor\n    \
             [spec : UbExceptionItemSpec \"{def_id}\"]\n    \
             (typeArgs : Trusted.MirAst.TypeSubst) : UbExceptionClaim :=\n  \
           {{ body := Mir.{item}.body.instantiate typeArgs\n    \
             pre := fun args mem => sigPre typeArgs args mem\n    \
             strictSafetyPre := spec.strictSafetyPre\n    \
             post := fun args _ ret m1 => sigPost typeArgs args ret m1\n    \
             callees := defaultCallees }}\n\n\
         /-- Universally quantified polymorphic UB-exception verification proposition\n    \
             for `{def_id}` over all `typeArgs : Trusted.MirAst.TypeSubst` of length\n    \
             `Mir.{item}.body.typeParamCount`. -/\n\
         def polyUbExceptionClaim [spec : UbExceptionItemSpec \"{def_id}\"] : Prop :=\n  \
           ∀ (typeArgs : Trusted.MirAst.TypeSubst),\n    \
             typeArgs.length = Mir.{item}.body.typeParamCount →\n      \
               UbExceptionVerificationResult (ubExceptionClaimFor typeArgs)\n\n\
         /-- Audited artifact identity for `{def_id}`. -/\n\
         def artifactIdentity : ArtifactIdentity where\n  \
           defPath := \"{def_id}\"\n  \
           mirDialect := \"V2026_06_01\"\n  \
           mirModuleSha256 := \"{sha}\"\n\n\
         /-- Package a polymorphic item proposition `P` into a single-item\n    \
             `CrateClaim` for `Verify.{item}.verified` auditing. -/\n\
         def polyCertificate (P : Prop) : CrateClaim where\n  \
           crateName := \"{def_id}\"\n  \
           mirDialect := \"V2026_06_01\"\n  \
           items := [{{ identity := artifactIdentity, certificate := P }}]\n\n"
    ));

    out.push_str(&format!("end Obligations.{item}\n"));
    out
}

/// Render the disposable `.anneal/generated/Assumptions/<Item>.lean` module
/// for a subject annotated with `#[anneal_spec::spec(trusted, ...)]` (or
/// `assumed`) in Rust when no user-authored `anneal/proofs/Assumptions/<Item>.lean`
/// exists on disk.
pub fn render_generated_assumptions_module(
    bundle: &SubjectObligationBundle,
    authored: AuthoredItemModules,
) -> String {
    let item = &bundle.item_module_suffix;
    let def_id = &bundle.subject.target.def_id;
    let claim_ty = if bundle.has_rust_safe_total_attr() || authored.is_total {
        format!(
            "Trusted.VerificationResult.TotalVerificationResult Obligations.{item}.totalClaim"
        )
    } else {
        format!("Trusted.VerificationResult.VerificationResult Obligations.{item}.claim")
    };

    format!(
        "import Trusted\n\
         import Obligations.{item}\n\n\
         namespace Assumptions.{item}\n\n\
         /-- Conditional axiom generated from `#[anneal_spec::spec(trusted, ...)]`\n    \
             for `{def_id}` in Rust. -/\n\
         axiom rust_trusted_contract :\n  \
           {claim_ty}\n\n\
         end Assumptions.{item}\n"
    )
}

/// Render the disposable `.anneal/generated/Verify/<Item>.lean` module for
/// `bundle` assuming an authored `Proof.<Item>` module is present.
pub fn render_verify_module(bundle: &SubjectObligationBundle) -> String {
    render_verify_module_with_options(
        bundle,
        AuthoredItemModules {
            has_proof: true,
            ..AuthoredItemModules::default()
        },
    )
}

/// Render the kernel-checked `signatureMonomorphic` guard emitted beside every
/// monomorphic signature-typed certificate (`statefulClaim`, `totalClaim`,
/// `modularClaim`, and `ubExceptionClaim`).
///
/// Those claims instantiate `Mir.<Item>.body` at `List.nil` and conjoin
/// `argsMatchSignature`, which rejects every value of an uninstantiated
/// `RigidTy.param` (or unlowered `RigidTy.other`) type. Without the guard, a
/// generic item's monomorphic certificate would have an unsatisfiable
/// precondition and hold vacuously; with it, `lake build` rejects the
/// `Verify.<Item>` module and generic items must use a `poly*Claim` surface.
fn render_monomorphic_signature_guard(item: &str) -> String {
    format!(
        "/-- Kernel-checked guard: the monomorphic signature-typed claims instantiate\n    \
            `Mir.{item}.body` at `List.nil`, so they are only meaningful when its\n    \
            signature mentions no uninstantiated generic parameter. Generic items must\n    \
            be verified through `Obligations.{item}.poly*Claim`. -/\n\
         theorem signatureMonomorphic :\n    \
             Trusted.VerificationResult.signatureIsMonomorphic Mir.{item}.body = true := by\n  \
           decide\n\n"
    )
}

/// Render the disposable `.anneal/generated/Verify/<Item>.lean` module for
/// `bundle` and `authored`.
///
/// Only imports `Specs.<Item>`, `Assumptions.<Item>`, and `Proof.<Item>` when
/// those authored (or generated-assumption) files exist on disk. When
/// `Proof.<Item>` does not exist on disk, emits either a conditional
/// certificate referencing `Assumptions.<Item>.rust_trusted_contract` (for
/// `#[spec(trusted, ...)]`) or a `priority := low` `defaultProof` instance
/// attempting automatic symbolic reflection and bounded `WP` discharge.
///
/// Monomorphic signature-typed certificates are accompanied by
/// `render_monomorphic_signature_guard`.
pub fn render_verify_module_with_options(
    bundle: &SubjectObligationBundle,
    authored: AuthoredItemModules,
) -> String {
    let item = &bundle.item_module_suffix;
    let def_id = &bundle.subject.target.def_id;
    let uses_rust_trusted_contract = !authored.has_proof
        && !authored.has_assumptions
        && (bundle.has_rust_trusted_attr() || authored.has_generated_assumptions);
    let mut out = String::new();

    out.push_str(&format!("-- @anneal-def-id: {def_id}\n"));
    out.push_str("import Trusted\n");
    if !authored.has_proof && !uses_rust_trusted_contract {
        out.push_str("import Anneal\n");
    }
    out.push_str(&format!("import Mir.{item}\n"));
    out.push_str(&format!("import Obligations.{item}\n"));
    if !authored.has_proof && !uses_rust_trusted_contract && !authored.has_specs {
        let mut imported_callee_mir: BTreeSet<String> = BTreeSet::new();
        for callee in &bundle.transitive_callees {
            if callee.item_module_suffix != *item
                && imported_callee_mir.insert(callee.item_module_suffix.clone())
            {
                out.push_str(&format!("import Mir.{}\n", callee.item_module_suffix));
            }
        }
        for ext in &bundle.external_spec_callees {
            if ext.sidecar_module_suffix != *item
                && imported_callee_mir.insert(ext.sidecar_module_suffix.clone())
            {
                out.push_str(&format!("import Mir.{}\n", ext.sidecar_module_suffix));
            }
            if let Some(ref req_suf) = ext.req_module_suffix
                && req_suf != item
                && imported_callee_mir.insert(req_suf.clone())
            {
                out.push_str(&format!("import Mir.{req_suf}\n"));
            }
            if let Some(ref ens_suf) = ext.ens_module_suffix
                && ens_suf != item
                && imported_callee_mir.insert(ens_suf.clone())
            {
                out.push_str(&format!("import Mir.{ens_suf}\n"));
            }
        }
        for callee in &bundle.called_callees {
            if callee.item_module_suffix != *item
                && imported_callee_mir.insert(callee.item_module_suffix.clone())
            {
                out.push_str(&format!("import Mir.{}\n", callee.item_module_suffix));
            }
            if let Some(ref req_suf) = callee.req_module_suffix
                && req_suf != item
                && imported_callee_mir.insert(req_suf.clone())
            {
                out.push_str(&format!("import Mir.{req_suf}\n"));
            }
            if let Some(ref ens_suf) = callee.ens_module_suffix
                && ens_suf != item
                && imported_callee_mir.insert(ens_suf.clone())
            {
                out.push_str(&format!("import Mir.{ens_suf}\n"));
            }
        }
    }
    if authored.has_specs {
        out.push_str(&format!("import Specs.{item}\n"));
    }
    if authored.has_assumptions || uses_rust_trusted_contract {
        out.push_str(&format!("import Assumptions.{item}\n"));
    }
    if authored.has_proof {
        out.push_str(&format!("import Proof.{item}\n"));
    }

    out.push_str(&format!(
        "\nnamespace Verify.{item}\n\n\
         open Trusted.VerificationResult\n\n\
         /-!\n\
         Disposable verification assembly root for `{def_id}`.\n\n\
         This module is generated on every `cargo anneal` run and assembles the\n\
         active `ItemSpec` and proof witness at the audited\n\
         `VerificationResult` theorem boundary.\n\
         -/\n\n"
    ));

    if authored.has_proof {
        if authored.is_polymorphic {
            let poly_prop = if authored.is_ub_exception {
                format!("Obligations.{item}.polyUbExceptionClaim")
            } else if authored.is_modular {
                format!("Obligations.{item}.polyModularClaim")
            } else if authored.is_total {
                format!("Obligations.{item}.polyTotalClaim")
            } else if authored.is_stateful {
                format!("Obligations.{item}.polyStatefulClaim")
            } else {
                format!("Obligations.{item}.polyClaim")
            };
            out.push_str(&format!(
                "/-- Kernel-checked polymorphic verification certificate for `{def_id}`. -/\n\
                 theorem verified :\n    \
                     CrateVerificationResult\n      \
                       (Obligations.{item}.polyCertificate {poly_prop}) :=\n  \
                   mkPolyVerificationResult\n    \
                     Obligations.{item}.artifactIdentity\n    \
                     Proof.{item}.verified\n\n\
                 /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
                 abbrev Certificate : Prop :=\n  \
                   CrateVerificationResult\n    \
                     (Obligations.{item}.polyCertificate {poly_prop})\n\n"
            ));
        } else if authored.is_ub_exception {
            out.push_str(&format!(
                "/-- Kernel-checked scoped UB-exception verification certificate for `{def_id}`. -/\n\
                 theorem verified : UbExceptionVerificationResult Obligations.{item}.ubExceptionClaim :=\n  \
                   Proof.{item}.verified\n\n\
                 /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
                 abbrev Certificate : Prop := UbExceptionVerificationResult Obligations.{item}.ubExceptionClaim\n\n"
            ));
            out.push_str(&render_monomorphic_signature_guard(item));
        } else if authored.is_modular {
            out.push_str(&format!(
                "/-- Kernel-checked modular verification certificate for `{def_id}`. -/\n\
                 theorem verified : ModularVerificationResult Obligations.{item}.modularClaim :=\n  \
                   Proof.{item}.verified\n\n\
                 /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
                 abbrev Certificate : Prop := ModularVerificationResult Obligations.{item}.modularClaim\n\n"
            ));
            out.push_str(&render_monomorphic_signature_guard(item));
        } else if authored.is_equiv {
            out.push_str(&format!(
                "/-- Kernel-checked behavioral-equivalence verification certificate for `{def_id}`. -/\n\
                 theorem verified : StatefulEquivVerificationResult Obligations.{item}.equivClaim :=\n  \
                   Proof.{item}.verified\n\n\
                 /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
                 abbrev Certificate : Prop := StatefulEquivVerificationResult Obligations.{item}.equivClaim\n\n"
            ));
        } else if authored.is_total {
            out.push_str(&format!(
                "/-- Kernel-checked total-correctness verification certificate for `{def_id}`. -/\n\
                 theorem verified : TotalVerificationResult Obligations.{item}.totalClaim :=\n  \
                   Proof.{item}.verified\n\n\
                 /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
                 abbrev Certificate : Prop := TotalVerificationResult Obligations.{item}.totalClaim\n\n"
            ));
            out.push_str(&render_monomorphic_signature_guard(item));
        } else if authored.is_stateful {
            out.push_str(&format!(
                "/-- Kernel-checked stateful verification certificate for `{def_id}`. -/\n\
                 theorem verified : StatefulVerificationResult Obligations.{item}.statefulClaim :=\n  \
                   Proof.{item}.verified\n\n\
                 /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
                 abbrev Certificate : Prop := StatefulVerificationResult Obligations.{item}.statefulClaim\n\n"
            ));
            out.push_str(&render_monomorphic_signature_guard(item));
        } else {
            out.push_str(&format!(
                "/-- Kernel-checked verification certificate for `{def_id}`. -/\n\
                 theorem verified : VerificationResult Obligations.{item}.claim :=\n  \
                   Proof.{item}.verified\n\n\
                 /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
                 abbrev Certificate : Prop := VerificationResult Obligations.{item}.claim\n\n"
            ));
        }
    } else if uses_rust_trusted_contract {
        if bundle.has_rust_safe_total_attr() || authored.is_total {
            out.push_str(&format!(
                "/-- Conditional total-correctness certificate for `{def_id}` backed by\n    \
                    `#[anneal_spec::spec(trusted, ...)]` in `Assumptions.{item}`. -/\n\
                 theorem verified : TotalVerificationResult Obligations.{item}.totalClaim :=\n  \
                   Assumptions.{item}.rust_trusted_contract\n\n\
                 /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
                 abbrev Certificate : Prop := TotalVerificationResult Obligations.{item}.totalClaim\n\n"
            ));
            out.push_str(&render_monomorphic_signature_guard(item));
        } else {
            out.push_str(&format!(
                "/-- Conditional verification certificate for `{def_id}` backed by\n    \
                    `#[anneal_spec::spec(trusted, ...)]` in `Assumptions.{item}`. -/\n\
                 theorem verified : VerificationResult Obligations.{item}.claim :=\n  \
                   Assumptions.{item}.rust_trusted_contract\n\n\
                 /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
                 abbrev Certificate : Prop := VerificationResult Obligations.{item}.claim\n\n"
            ));
        }
    } else if !authored.has_specs
        // The automatic modular discharge combinators assume a single callee
        // contract whose normal returns leave memory unchanged
        // (`ans = .returned retVal req.memory`). That holds for a verified
        // sibling callee's `defaultCallContract`, but not for
        // `externalSpecCallContract` (which soundly permits heap mutation and
        // unwinding) or for a conjunction of several contracts, so only the
        // single-sibling-callee case is attempted here.
        && bundle.external_spec_callees.is_empty()
        && bundle.called_callees.len() == 1
        && let Some((contract_expr, callee_def_id, callee_arg_count_expr, opt_callee_req, callee_ens_suffix)) =
            bundle.called_callees.first().and_then(|callee| {
                callee.ens_module_suffix.as_ref().map(|ens_suf| {
                    let opt_req = if let Some(ref req_suf) = callee.req_module_suffix {
                        format!("(Option.some Mir.{req_suf}.body)")
                    } else {
                        "Option.none".to_string()
                    };
                    (
                        format!(
                            "Obligations.{}.defaultCallContract",
                            callee.item_module_suffix
                        ),
                        callee.def_id.as_str(),
                        format!("Mir.{}.body.argCount", callee.item_module_suffix),
                        opt_req,
                        ens_suf.as_str(),
                    )
                })
            })
    {
        let opt_subject_req = if bundle.inline_requires.len() == 1 {
            let req_suf = derive_item_module_suffix(&bundle.inline_requires[0]);
            format!("(Option.some Mir.{req_suf}.body)")
        } else {
            "Option.none".to_string()
        };
        let opt_subject_ens = if bundle.inline_ensures.len() == 1 {
            let ens_suf = derive_item_module_suffix(&bundle.inline_ensures[0]);
            format!("(Option.some Mir.{ens_suf}.body)")
        } else {
            "Option.none".to_string()
        };
        let mut branches = format!(
            "      | exact Anneal.Rustc.V2026_06_01.SymbolicEval.dischargeRustModularContractAuto\n          \
                     {contract_expr}\n          \
                     Mir.{item}.body\n          \
                     Obligations.{item}.defaultModularSpec.pre\n          \
                     Obligations.{item}.defaultModularSpec.post\n          \
                     64 64\n          \
                     {opt_subject_req}\n          \
                     {opt_subject_ens}\n          \
                     \"{callee_def_id}\"\n          \
                     {callee_arg_count_expr}\n          \
                     {opt_callee_req}\n          \
                     Mir.{callee_ens_suffix}.body\n          \
                     Obligations.{item}.defaultCallees\n"
        );
        if bundle.inline_requires.len() == 1 {
            let req_suf = derive_item_module_suffix(&bundle.inline_requires[0]);
            branches.push_str(&format!(
                "      | exact Anneal.Rustc.V2026_06_01.SymbolicEval.dischargeRustModularBoundedRange1Auto\n          \
                         {contract_expr}\n          \
                         Mir.{item}.body\n          \
                         Obligations.{item}.defaultModularSpec.pre\n          \
                         Obligations.{item}.defaultModularSpec.post\n          \
                         64 64\n          \
                         Mir.{req_suf}.body\n          \
                         {opt_subject_ens}\n          \
                         \"{callee_def_id}\"\n          \
                         {callee_arg_count_expr}\n          \
                         {opt_callee_req}\n          \
                         Mir.{callee_ens_suffix}.body\n          \
                         Obligations.{item}.defaultCallees\n"
            ));
        }
        out.push_str(&format!(
            "/-- Low-priority fallback `ModularItemProof` instance attempting\n    \
                automatic call-graph contract reflection when no authored\n    \
                `Proof.{item}` module exists on disk. -/\n\
             instance (priority := low) defaultModularProof :\n    \
                 ModularItemProof \"{def_id}\" Obligations.{item}.modularClaim where\n  \
               verified := by\n    \
                 first\n\
             {branches}\n\
             /-- Kernel-checked modular verification certificate for `{def_id}`. -/\n\
             theorem verified : ModularVerificationResult Obligations.{item}.modularClaim :=\n  \
               (inferInstance : ModularItemProof \"{def_id}\" Obligations.{item}.modularClaim).verified\n\n\
             /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
             abbrev Certificate : Prop := ModularVerificationResult Obligations.{item}.modularClaim\n\n"
        ));
        out.push_str(&render_monomorphic_signature_guard(item));
    } else if authored.is_modular
        || (!authored.has_specs
            && (!bundle.external_spec_callees.is_empty() || !bundle.called_callees.is_empty()))
    {
        out.push_str(&format!(
            "/-- Kernel-checked modular verification certificate for `{def_id}`. -/\n\
             theorem verified : ModularVerificationResult Obligations.{item}.modularClaim :=\n  \
               (inferInstance : ModularItemProof \"{def_id}\" Obligations.{item}.modularClaim).verified\n\n\
             /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
             abbrev Certificate : Prop := ModularVerificationResult Obligations.{item}.modularClaim\n\n"
        ));
        out.push_str(&render_monomorphic_signature_guard(item));
    } else if !authored.has_specs && (bundle.has_rust_safe_total_attr() || authored.is_total) {
        let opt_req = if bundle.inline_requires.len() == 1 {
            let req_suf = derive_item_module_suffix(&bundle.inline_requires[0]);
            format!("(Option.some Mir.{req_suf}.body)")
        } else {
            "Option.none".to_string()
        };
        let opt_ens = if bundle.inline_ensures.len() == 1 {
            let ens_suf = derive_item_module_suffix(&bundle.inline_ensures[0]);
            format!("(Option.some Mir.{ens_suf}.body)")
        } else {
            "Option.none".to_string()
        };
        let mut branches = String::new();
        if bundle.inline_requires.len() <= 1 && bundle.inline_ensures.len() <= 1 {
            branches.push_str(&format!(
                "      | exact Anneal.Rustc.V2026_06_01.SymbolicEval.dischargeRustTotalPinnedContractAuto\n          \
                         Obligations.{item}.totalClaim 64 64 {opt_req} {opt_ens}\n"
            ));
        }
        if bundle.inline_requires.len() == 1 && bundle.inline_ensures.len() <= 1 {
            let req_suf = derive_item_module_suffix(&bundle.inline_requires[0]);
            branches.push_str(&format!(
                "      | exact Anneal.Rustc.V2026_06_01.SymbolicEval.dischargeRustTotalSymRange1Auto\n          \
                         Obligations.{item}.totalClaim 64 64 Mir.{req_suf}.body {opt_ens}\n      \
                       | exact Anneal.Rustc.V2026_06_01.SymbolicEval.dischargeRustTotalBoundedRange1Auto\n          \
                         Obligations.{item}.totalClaim 64 64 Mir.{req_suf}.body {opt_ens}\n"
            ));
        }
        branches.push_str(&format!(
            "      | exact Anneal.Rustc.V2026_06_01.SymbolicEval.verifyTotalMirSym\n          \
                     Obligations.{item}.totalClaim 64 (by\n            \
                       intro _ _ _\n            \
                       first\n            \
                       | (simp; try omega; done)\n            \
                       | exact True.intro)\n"
        ));
        out.push_str(&format!(
            "/-- Low-priority fallback `TotalItemProof` instance attempting\n    \
                bounded symbolic reflection and `DWP` discharge when no authored\n    \
                `Proof.{item}` module exists on disk. -/\n\
             instance (priority := low) defaultProof :\n    \
                 TotalItemProof \"{def_id}\" Obligations.{item}.totalClaim where\n  \
               verified := by\n    \
                 first\n\
             {branches}\n\
             /-- Kernel-checked total-correctness verification certificate for `{def_id}`. -/\n\
             theorem verified : TotalVerificationResult Obligations.{item}.totalClaim :=\n  \
               (inferInstance : TotalItemProof \"{def_id}\" Obligations.{item}.totalClaim).verified\n\n\
             /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
             abbrev Certificate : Prop := TotalVerificationResult Obligations.{item}.totalClaim\n\n"
        ));
        out.push_str(&render_monomorphic_signature_guard(item));
    } else if !authored.has_specs
        && bundle.inline_requires.is_empty()
        && bundle.inline_ensures.is_empty()
    {
        out.push_str(&format!(
            "/-- Low-priority fallback `ItemProof` instance attempting bounded\n    \
                `WP` discharge when no authored `Proof.{item}` module exists on\n    \
                disk. -/\n\
             instance (priority := low) defaultProof :\n    \
                 ItemProof \"{def_id}\" Obligations.{item}.claim where\n  \
               verified :=\n    \
                 Anneal.Rustc.V2026_06_01.SymbolicEval.verifyByWP Obligations.{item}.claim 64 (by\n      \
                   intro _ _\n      \
                   exact True.intro)\n\n\
             /-- Kernel-checked verification certificate for `{def_id}`. -/\n\
             theorem verified : VerificationResult Obligations.{item}.claim :=\n  \
               (inferInstance : ItemProof \"{def_id}\" Obligations.{item}.claim).verified\n\n\
             /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
             abbrev Certificate : Prop := VerificationResult Obligations.{item}.claim\n\n"
        ));
    } else {
        let opt_req = if bundle.inline_requires.len() == 1 {
            let req_suf = derive_item_module_suffix(&bundle.inline_requires[0]);
            format!("(Option.some Mir.{req_suf}.body)")
        } else {
            "Option.none".to_string()
        };
        let opt_ens = if bundle.inline_ensures.len() == 1 {
            let ens_suf = derive_item_module_suffix(&bundle.inline_ensures[0]);
            format!("(Option.some Mir.{ens_suf}.body)")
        } else {
            "Option.none".to_string()
        };
        let mut branches = String::new();
        if !authored.has_specs
            && bundle.inline_requires.len() <= 1
            && bundle.inline_ensures.len() <= 1
        {
            branches.push_str(&format!(
                "      | exact Anneal.Rustc.V2026_06_01.SymbolicEval.dischargeRustPinnedContractAuto\n          \
                         Obligations.{item}.claim 64 64 {opt_req} {opt_ens}\n"
            ));
        }
        if !authored.has_specs
            && bundle.inline_requires.len() == 1
            && bundle.inline_ensures.len() <= 1
        {
            let req_suf = derive_item_module_suffix(&bundle.inline_requires[0]);
            branches.push_str(&format!(
                "      | exact Anneal.Rustc.V2026_06_01.SymbolicEval.dischargeRustSymRange1Auto\n          \
                         Obligations.{item}.claim 64 64 Mir.{req_suf}.body {opt_ens}\n      \
                       | exact Anneal.Rustc.V2026_06_01.SymbolicEval.dischargeRustBoundedRange1Auto\n          \
                         Obligations.{item}.claim 64 64 Mir.{req_suf}.body {opt_ens}\n"
            ));
        }
        branches.push_str(&format!(
            "      | exact Anneal.Rustc.V2026_06_01.SymbolicEval.verifyByWP Obligations.{item}.claim 64 (by\n          \
                     intro _ _\n          \
                     first\n          \
                     | (simp; try omega; done)\n          \
                     | exact True.intro)\n"
        ));
        out.push_str(&format!(
            "/-- Low-priority fallback `ItemProof` instance attempting bounded\n    \
                `WP` discharge when no authored `Proof.{item}` module exists on\n    \
                disk. -/\n\
             instance (priority := low) defaultProof :\n    \
                 ItemProof \"{def_id}\" Obligations.{item}.claim where\n  \
               verified := by\n    \
                 first\n\
             {branches}\
             /-- Kernel-checked verification certificate for `{def_id}`. -/\n\
             theorem verified : VerificationResult Obligations.{item}.claim :=\n  \
               (inferInstance : ItemProof \"{def_id}\" Obligations.{item}.claim).verified\n\n\
             /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
             abbrev Certificate : Prop := VerificationResult Obligations.{item}.claim\n\n"
        ));
    }

    out.push_str(&format!("end Verify.{item}\n"));
    out
}

/// Render the disposable `.anneal/generated/CrateVerify.lean` whole-crate
/// rollup module assembling every `Verify.<Item>.verified` theorem into an
/// audited `CrateVerificationResult crateClaim` certificate (`#109`).
///
/// Imports only `Trusted` and `Verify.<Item>` modules so `CrateVerify.verified`'s
/// statement never touches `Anneal.*` (`theory/`).
pub fn render_crate_verify_module(crate_name: &str, bundles: &[SubjectObligationBundle]) -> String {
    let mut out = String::new();
    out.push_str("import Trusted\n");
    for bundle in bundles {
        out.push_str(&format!("import Verify.{}\n", bundle.item_module_suffix));
    }
    out.push_str("\nnamespace CrateVerify\n\n");
    out.push_str("open Trusted.VerificationResult\n\n");
    out.push_str(&format!(
        "/-!\nDisposable whole-crate verification rollup for `{crate_name}`.\n\n\
         Aggregates every captured subject item's kernel-checked `Verify.<Item>.verified`\n\
         certificate into a single `CrateVerificationResult` audited by `TrustedBoundary`.\n-/\n\n"
    ));
    out.push_str(&format!(
        "/-- Whole-crate verification claim inventory for `{crate_name}`. -/\n\
         def crateClaim : CrateClaim where\n  \
           crateName := \"{crate_name}\"\n  \
           mirDialect := \"V2026_06_01\"\n  \
           items := [\n"
    ));
    for (idx, bundle) in bundles.iter().enumerate() {
        let comma = if idx + 1 < bundles.len() { "," } else { "" };
        let def_id = &bundle.subject.target.def_id;
        let sha = &bundle.subject.target.mir_module_sha256;
        let item = &bundle.item_module_suffix;
        out.push_str(&format!(
            "    {{ identity := {{\n        \
                     defPath := \"{def_id}\"\n        \
                     mirDialect := \"V2026_06_01\"\n        \
                     mirModuleSha256 := \"{sha}\"\n      \
                   }}\n      \
                   certificate := Verify.{item}.Certificate\n    \
                 }}{comma}\n"
        ));
    }
    out.push_str("  ]\n\n");

    let mut conj_proof = String::from("True.intro");
    for bundle in bundles.iter().rev() {
        conj_proof = format!(
            "(And.intro Verify.{}.verified {conj_proof})",
            bundle.item_module_suffix
        );
    }

    out.push_str(&format!(
        "/-- Kernel-checked whole-crate verification certificate for `{crate_name}`. -/\n\
         theorem verified : CrateVerificationResult crateClaim :=\n  \
           {{ proof := And.intro (by intro h; nomatch h) {conj_proof} }}\n\n\
         end CrateVerify\n"
    ));
    out
}

/// Render an opt-in starter `anneal/proofs/Specs/<Item>.lean` override template
/// for `bundle`.
///
/// Normal `cargo anneal` runs do not stamp out `Specs/<Item>.lean` files on
/// disk because `Obligations.<Item>.defaultSpec` provides the default
/// specification automatically. This template is used only when a user
/// explicitly requests starter specification templates.
pub fn render_specs_template(bundle: &SubjectObligationBundle) -> String {
    let item = &bundle.item_module_suffix;
    let def_id = &bundle.subject.target.def_id;
    if !bundle.external_spec_callees.is_empty() || !bundle.called_callees.is_empty() {
        return format!(
            "import Trusted\n\
             import Mir.{item}\n\
             import Obligations.{item}\n\n\
             namespace Specs.{item}\n\n\
             set_option linter.unusedVariables false\n\n\
             open Trusted.MirSemantics\n\
             open Trusted.VerificationResult\n\n\
             /-!\n\
             Durable modular specification override module for `{def_id}`.\n\n\
             `Obligations.{item}.defaultModularSpec` provides a `priority := low` default\n\
             `ModularItemSpec \"{def_id}\"` instance lowered from Rust `#[spec]` and\n\
             `#[external_spec]` companions. Declaring a normal-priority `ModularItemSpec`\n\
             instance in this module overrides that default without modifying any\n\
             generated file.\n\n\
             To strengthen the contract while preserving Rust `#[spec]` and\n\
             `#[external_spec]` companions, use `Obligations.{item}.refineModularSpec`.\n\
             -/\n\n\
             /-- Assumed external call-handler environment contract. -/\n\
             def envAssumed (h : ExternalCallHandler) : Prop :=\n  \
               Obligations.{item}.defaultModularSpec.envAssumed h\n\n\
             /-- Precondition over the incoming argument list `args` and initial `mem`. -/\n\
             def pre (args : List Value) (mem : Memory) : Prop :=\n  \
               Obligations.{item}.defaultModularSpec.pre args mem\n\n\
             /-- Postcondition relating `(args, mem)` to `(ret, mem')`. -/\n\
             def post (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory) : Prop :=\n  \
               Obligations.{item}.defaultModularSpec.post args mem ret mem'\n\n\
             /-- Normal-priority `ModularItemSpec` instance overriding\n    \
                 `Obligations.{item}.defaultModularSpec`.\n    \
                 Alternatively, define `instance : ModularItemSpec \"{def_id}\" :=\n    \
                 Obligations.{item}.refineModularSpec envAssumed extraPre extraPost`. -/\n\
             instance : ModularItemSpec \"{def_id}\" where\n  \
               envAssumed := envAssumed\n  \
               pre := pre\n  \
               post := post\n\n\
             end Specs.{item}\n"
        );
    }
    format!(
        "import Trusted\n\
         import Mir.{item}\n\
         import Obligations.{item}\n\n\
         namespace Specs.{item}\n\n\
         set_option linter.unusedVariables false\n\n\
         open Trusted.MirSemantics\n\
         open Trusted.VerificationResult\n\n\
         /-!\n\
         Durable specification override module for `{def_id}`.\n\n\
         `Obligations.{item}.defaultSpec` provides a `priority := low` default\n\
         `ItemSpec \"{def_id}\"` instance lowered from Rust `#[spec]` and\n\
         `#[external_spec]` companions. Declaring a normal-priority `ItemSpec`\n\
         instance in this module overrides that default without modifying any\n\
         generated file.\n\n\
         To strengthen the contract while preserving Rust `#[spec]` companions,\n\
         use `Obligations.{item}.refineSpec` (or `refineStatefulSpec`) or\n\
         conjoin `Obligations.{item}.rustRequires` and\n\
         `Obligations.{item}.rustEnsures` directly.\n\
         -/\n\n\
         /-- Precondition over the incoming argument list `args`. -/\n\
         def pre (args : List Value) : Prop :=\n  \
           Obligations.{item}.defaultPre args\n\n\
         /-- Postcondition relating the incoming argument list `args` and return\n    \
             value `ret`. -/\n\
         def post (args : List Value) (ret : Value) : Prop :=\n  \
           Obligations.{item}.defaultPost args ret\n\n\
         /-- Normal-priority `ItemSpec` instance overriding\n    \
             `Obligations.{item}.defaultSpec`.\n    \
             Alternatively, define `instance : ItemSpec \"{def_id}\" :=\n    \
             Obligations.{item}.refineSpec extraPre extraPost`. -/\n\
         instance : ItemSpec \"{def_id}\" where\n  \
           pre := pre\n  \
           post := post\n\n\
         end Specs.{item}\n"
    )
}

/// Render an opt-in starter `anneal/proofs/Proof/<Item>.lean` template for
/// `bundle` with default authored-module settings.
pub fn render_proof_template(bundle: &SubjectObligationBundle) -> String {
    render_proof_template_with_options(bundle, AuthoredItemModules::default())
}

/// Render a context-aware starter `anneal/proofs/Proof/<Item>.lean` template
/// for `bundle` and `authored`.
///
/// Automatically imports `Specs.<Item>` and `Assumptions.<Item>` when those
/// authored modules exist on disk, opens `Anneal.Tactics` and
/// `Anneal.Rustc.V2026_06_01.Lower`, and emits a `StatefulVerificationResult`
/// theorem when `authored.is_stateful` is `true`.
pub fn render_proof_template_with_options(
    bundle: &SubjectObligationBundle,
    authored: AuthoredItemModules,
) -> String {
    let item = &bundle.item_module_suffix;
    let def_id = &bundle.subject.target.def_id;
    let mut out = String::new();

    out.push_str("import Trusted\n");
    out.push_str("import Anneal\n");
    out.push_str(&format!("import Mir.{item}\n"));
    out.push_str(&format!("import Obligations.{item}\n"));
    if authored.has_specs {
        out.push_str(&format!("import Specs.{item}\n"));
    }
    if authored.has_assumptions {
        out.push_str(&format!("import Assumptions.{item}\n"));
    }

    out.push_str(&format!(
        "\nnamespace Proof.{item}\n\n\
         open Trusted.VerificationResult\n\
         open Anneal.Rustc.V2026_06_01.Lower\n\
         open Anneal.Rustc.V2026_06_01.SymbolicEval\n\
         open Anneal.FunctionalTranslation\n\n"
    ));

    if authored.is_polymorphic {
        let poly_prop = if authored.is_ub_exception {
            format!("Obligations.{item}.polyUbExceptionClaim")
        } else if authored.is_modular {
            format!("Obligations.{item}.polyModularClaim")
        } else if authored.is_total {
            format!("Obligations.{item}.polyTotalClaim")
        } else if authored.is_stateful {
            format!("Obligations.{item}.polyStatefulClaim")
        } else {
            format!("Obligations.{item}.polyClaim")
        };
        out.push_str(&format!(
            "/-!\n\
             Durable polymorphic proof module for `{def_id}`.\n\n\
             Replace `sorry` below with a kernel-checked proof discharging\n\
             `{poly_prop}`.\n\
             -/\n\n\
             /-- Polymorphic verification proof discharging `{poly_prop}`. -/\n\
             theorem verified : {poly_prop} := by\n  \
               sorry\n\n\
             end Proof.{item}\n"
        ));
    } else if authored.is_ub_exception {
        out.push_str(&format!(
            "/-!\n\
             Durable scoped UB-exception proof module for `{def_id}`.\n\n\
             Replace `sorry` below with a kernel-checked proof discharging\n\
             `Obligations.{item}.ubExceptionClaim`.\n\
             -/\n\n\
             /-- Scoped UB-exception verification proof discharging `Obligations.{item}.ubExceptionClaim`. -/\n\
             theorem verified : UbExceptionVerificationResult Obligations.{item}.ubExceptionClaim := by\n  \
               sorry\n\n\
             end Proof.{item}\n"
        ));
    } else if authored.is_modular
        || (!authored.has_specs
            && (!bundle.external_spec_callees.is_empty() || !bundle.called_callees.is_empty()))
    {
        out.push_str(&format!(
            "/-!\n\
             Durable modular proof module for `{def_id}`.\n\n\
             Replace `sorry` below with a kernel-checked proof discharging\n\
             `Obligations.{item}.modularClaim`.\n\
             -/\n\n\
             /-- Modular verification proof discharging `Obligations.{item}.modularClaim`. -/\n\
             theorem verified : ModularVerificationResult Obligations.{item}.modularClaim := by\n  \
               sorry\n\n\
             end Proof.{item}\n"
        ));
    } else if authored.is_equiv {
        out.push_str(&format!(
            "/-!\n\
             Durable behavioral-equivalence proof module for `{def_id}`.\n\n\
             Replace `sorry` below with a kernel-checked proof discharging\n\
             `Obligations.{item}.equivClaim`.\n\
             -/\n\n\
             /-- Behavioral-equivalence verification proof discharging `Obligations.{item}.equivClaim`. -/\n\
             theorem verified : StatefulEquivVerificationResult Obligations.{item}.equivClaim := by\n  \
               sorry\n\n\
             end Proof.{item}\n"
        ));
    } else if authored.is_total {
        out.push_str(&format!(
            "/-!\n\
             Durable total-correctness proof module for `{def_id}`.\n\n\
             Replace `sorry` below with a kernel-checked proof discharging\n\
             `Obligations.{item}.totalClaim`.\n\
             -/\n\n\
             /-- Total-correctness verification proof discharging `Obligations.{item}.totalClaim`. -/\n\
             theorem verified : TotalVerificationResult Obligations.{item}.totalClaim := by\n  \
               sorry\n\n\
             end Proof.{item}\n"
        ));
    } else if authored.is_stateful {
        out.push_str(&format!(
            "/-!\n\
             Durable stateful proof module for `{def_id}`.\n\n\
             Replace `sorry` below with a kernel-checked proof discharging\n\
             `Obligations.{item}.statefulClaim`.\n\
             -/\n\n\
             /-- Stateful verification proof discharging `Obligations.{item}.statefulClaim`. -/\n\
             theorem verified : StatefulVerificationResult Obligations.{item}.statefulClaim := by\n  \
               sorry\n\n\
             end Proof.{item}\n"
        ));
    } else {
        out.push_str(&format!(
            "/-!\n\
             Durable proof module for `{def_id}`.\n\n\
             Replace `sorry` below with a kernel-checked proof discharging\n\
             `Obligations.{item}.claim`.\n\
             -/\n\n\
             /-- Verification proof discharging `Obligations.{item}.claim`. -/\n\
             theorem verified : VerificationResult Obligations.{item}.claim := by\n  \
               sorry\n\n\
             end Proof.{item}\n"
        ));
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use anneal_rustc_capture::CapturedTarget;

    fn sample_records() -> Vec<UnitTargetRecord> {
        vec![
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "my_crate::math::inc".to_string(),
                    mir_module_path: "Mir/MyCrate/math/inc.lean".to_string(),
                    mir_module_sha256: "a".repeat(64),
                },
                lean_module_name: "Mir.MyCrate.math.inc".to_string(),
                item_kind: CapturedItemKind::Subject,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            },
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "my_crate::math::__anodized_fn_requires_inc".to_string(),
                    mir_module_path: "Mir/MyCrate/math/__anodized_fn_requires_inc.lean"
                        .to_string(),
                    mir_module_sha256: "b".repeat(64),
                },
                lean_module_name: "Mir.MyCrate.math.__anodized_fn_requires_inc".to_string(),
                item_kind: CapturedItemKind::InlineSpecRequires,
                associated_subject_def_id: Some("my_crate::math::inc".to_string()),
                trait_impls: Vec::new(),
            },
            UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "my_crate::math::__anodized_fn_ensures_inc".to_string(),
                    mir_module_path: "Mir/MyCrate/math/__anodized_fn_ensures_inc.lean"
                        .to_string(),
                    mir_module_sha256: "c".repeat(64),
                },
                lean_module_name: "Mir.MyCrate.math.__anodized_fn_ensures_inc".to_string(),
                item_kind: CapturedItemKind::InlineSpecEnsures,
                associated_subject_def_id: Some("my_crate::math::inc".to_string()),
                trait_impls: Vec::new(),
            },
        ]
    }

    #[test]
    fn groups_companion_specs_and_renders_obligation_modules() {
        let records = sample_records();
        let bundles = group_subject_obligations(&records);
        assert_eq!(bundles.len(), 1);
        let bundle = &bundles[0];
        assert_eq!(bundle.item_module_suffix, "MyCrate.math.inc");
        assert_eq!(
            bundle.item_rel_path,
            PathBuf::from("MyCrate/math/inc.lean")
        );
        assert_eq!(bundle.inline_requires.len(), 1);
        assert_eq!(bundle.inline_ensures.len(), 1);

        let obligations = render_obligations_module(bundle);
        assert!(obligations.contains("import Trusted"));
        assert!(!obligations.contains("import Anneal"));
        assert!(!obligations.contains("import Specs.MyCrate.math.inc"));
        assert!(obligations.contains("import Mir.MyCrate.math.inc"));
        assert!(obligations.contains("import Mir.MyCrate.math.__anodized_fn_requires_inc"));
        assert!(obligations.contains("import Mir.MyCrate.math.__anodized_fn_ensures_inc"));
        assert!(obligations.contains(
            "def defaultPre (args : List Value) : Prop :=\n  And (Trusted.Sequence.length args = Mir.MyCrate.math.inc.body.argCount) (MirBoolPredicateHolds Mir.MyCrate.math.__anodized_fn_requires_inc.body args)"
        ));
        assert!(obligations.contains(
            "def defaultPost (args : List Value) (ret : Value) : Prop :=\n  MirBoolPredicateHolds Mir.MyCrate.math.__anodized_fn_ensures_inc.body (List.append args (List.cons ret List.nil))"
        ));
        assert!(obligations.contains(
            "instance (priority := low) defaultSpec : ItemSpec \"my_crate::math::inc\" where"
        ));
        assert!(obligations.contains(
            "def claim [spec : ItemSpec \"my_crate::math::inc\"] : Claim :=\n  { body := Mir.MyCrate.math.inc.body, pre := spec.pre, post := spec.post, callees := defaultCallees }"
        ));

        let verify_with_proof = render_verify_module_with_options(
            bundle,
            AuthoredItemModules {
                has_specs: true,
                has_legacy_specs_defs: false,
                has_assumptions: true,
                has_proof: true,
                is_stateful: false,
                ..AuthoredItemModules::default()
            },
        );
        assert!(verify_with_proof.contains("import Specs.MyCrate.math.inc"));
        assert!(verify_with_proof.contains("import Assumptions.MyCrate.math.inc"));
        assert!(verify_with_proof.contains("import Proof.MyCrate.math.inc"));
        assert!(verify_with_proof.contains(
            "theorem verified : VerificationResult Obligations.MyCrate.math.inc.claim :=\n  Proof.MyCrate.math.inc.verified"
        ));

        let verify_auto =
            render_verify_module_with_options(bundle, AuthoredItemModules::default());
        assert!(!verify_auto.contains("import Specs.MyCrate.math.inc"));
        assert!(!verify_auto.contains("import Assumptions.MyCrate.math.inc"));
        assert!(!verify_auto.contains("import Proof.MyCrate.math.inc"));
        assert!(verify_auto.contains(
            "instance (priority := low) defaultProof :\n    ItemProof \"my_crate::math::inc\" Obligations.MyCrate.math.inc.claim"
        ));

        let specs = render_specs_template(bundle);
        assert!(specs.contains("import Obligations.MyCrate.math.inc"));
        assert!(specs.contains("instance : ItemSpec \"my_crate::math::inc\" where"));

        let proof = render_proof_template(bundle);
        assert!(proof.contains("import Obligations.MyCrate.math.inc"));
        assert!(
            proof.contains("theorem verified : VerificationResult Obligations.MyCrate.math.inc.claim")
        );
    }

    #[test]
    fn renders_empty_and_multi_clause_rust_contracts() {
        let subject = UnitTargetRecord {
            target: CapturedTarget {
                def_id: "my_crate::math::id".to_string(),
                mir_module_path: "Mir/MyCrate/math/id.lean".to_string(),
                mir_module_sha256: "a".repeat(64),
            },
            lean_module_name: "Mir.MyCrate.math.id".to_string(),
            item_kind: CapturedItemKind::Subject,
            associated_subject_def_id: None,
            trait_impls: Vec::new(),
        };
        let empty_bundle = SubjectObligationBundle {
            subject: subject.clone(),
            item_module_suffix: "MyCrate.math.id".to_string(),
            item_rel_path: PathBuf::from("MyCrate/math/id.lean"),
            inline_requires: Vec::new(),
            inline_ensures: Vec::new(),
            inline_qualifiers: Vec::new(),
            external_specs: vec![UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "my_crate::math::__ANNEAL_EXT_SPEC_TARGET_id".to_string(),
                    mir_module_path: "Mir/MyCrate/math/__ANNEAL_EXT_SPEC_TARGET_id.lean"
                        .to_string(),
                    mir_module_sha256: "d".repeat(64),
                },
                lean_module_name: "Mir.MyCrate.math.__ANNEAL_EXT_SPEC_TARGET_id".to_string(),
                item_kind: CapturedItemKind::ExternalSpec,
                associated_subject_def_id: Some("my_crate::math::id".to_string()),
                trait_impls: Vec::new(),
            }],
            called_callees: Vec::new(),
            transitive_callees: Vec::new(),
            external_spec_callees: Vec::new(),
            spec_callees: Vec::new(),
            spec_companions_with_calls: BTreeSet::new(),
        };

        let empty_obligations = render_obligations_module(&empty_bundle);
        assert!(
            !empty_obligations
                .contains("import Mir.MyCrate.math.__ANNEAL_EXT_SPEC_TARGET_id")
        );
        assert!(empty_obligations.contains(
            "def defaultPre (args : List Value) : Prop :=\n  True"
        ));
        assert!(empty_obligations.contains(
            "def defaultPost (args : List Value) (ret : Value) : Prop :=\n  True"
        ));

        let multi_bundle = SubjectObligationBundle {
            subject,
            item_module_suffix: "MyCrate.math.id".to_string(),
            item_rel_path: PathBuf::from("MyCrate/math/id.lean"),
            inline_requires: vec![
                UnitTargetRecord {
                    target: CapturedTarget {
                        def_id: "my_crate::math::__anodized_fn_requires_id_0".to_string(),
                        mir_module_path: "Mir/MyCrate/math/__anodized_fn_requires_id_0.lean"
                            .to_string(),
                        mir_module_sha256: "1".repeat(64),
                    },
                    lean_module_name: "Mir.MyCrate.math.__anodized_fn_requires_id_0".to_string(),
                    item_kind: CapturedItemKind::InlineSpecRequires,
                    associated_subject_def_id: Some("my_crate::math::id".to_string()),
                    trait_impls: Vec::new(),
                },
                UnitTargetRecord {
                    target: CapturedTarget {
                        def_id: "my_crate::math::__anodized_fn_requires_id_1".to_string(),
                        mir_module_path: "Mir/MyCrate/math/__anodized_fn_requires_id_1.lean"
                            .to_string(),
                        mir_module_sha256: "2".repeat(64),
                    },
                    lean_module_name: "Mir.MyCrate.math.__anodized_fn_requires_id_1".to_string(),
                    item_kind: CapturedItemKind::InlineSpecRequires,
                    associated_subject_def_id: Some("my_crate::math::id".to_string()),
                    trait_impls: Vec::new(),
                },
            ],
            inline_ensures: Vec::new(),
            inline_qualifiers: Vec::new(),
            external_specs: Vec::new(),
            called_callees: Vec::new(),
            transitive_callees: Vec::new(),
            external_spec_callees: Vec::new(),
            spec_callees: Vec::new(),
            spec_companions_with_calls: BTreeSet::new(),
        };

        let multi_obligations = render_obligations_module(&multi_bundle);
        assert!(multi_obligations.contains(
            "def defaultPre (args : List Value) : Prop :=\n  And (Trusted.Sequence.length args = Mir.MyCrate.math.id.body.argCount) (And (MirBoolPredicateHolds Mir.MyCrate.math.__anodized_fn_requires_id_0.body args) (MirBoolPredicateHolds Mir.MyCrate.math.__anodized_fn_requires_id_1.body args))"
        ));
    }

    #[test]
    fn renders_verify_module_for_stateless_and_stateful_proofs() {
        let records = sample_records();
        let bundles = group_subject_obligations(&records);
        let bundle = &bundles[0];

        let verify_stateless = render_verify_module_with_options(
            bundle,
            AuthoredItemModules {
                has_specs: true,
                has_legacy_specs_defs: false,
                has_assumptions: false,
                has_proof: true,
                is_stateful: false,
                ..AuthoredItemModules::default()
            },
        );
        assert!(verify_stateless.contains(
            "/-- Kernel-checked verification certificate for `my_crate::math::inc`. -/\n\
             theorem verified : VerificationResult Obligations.MyCrate.math.inc.claim :=\n  \
               Proof.MyCrate.math.inc.verified"
        ));
        assert!(!verify_stateless.contains("StatefulVerificationResult"));

        let verify_stateful = render_verify_module_with_options(
            bundle,
            AuthoredItemModules {
                has_specs: true,
                has_legacy_specs_defs: false,
                has_assumptions: false,
                has_proof: true,
                is_stateful: true,
                ..AuthoredItemModules::default()
            },
        );
        assert!(verify_stateful.contains(
            "/-- Kernel-checked stateful verification certificate for `my_crate::math::inc`. -/\n\
             theorem verified : StatefulVerificationResult Obligations.MyCrate.math.inc.statefulClaim :=\n  \
               Proof.MyCrate.math.inc.verified"
        ));
        assert!(verify_stateful.contains(
            "theorem signatureMonomorphic :\n    \
               Trusted.VerificationResult.signatureIsMonomorphic Mir.MyCrate.math.inc.body = true := by\n  \
               decide"
        ));
        assert!(!verify_stateless.contains("signatureMonomorphic"));
    }

    #[test]
    fn renders_refine_spec_combinators_and_context_aware_proof_templates() {
        let records = sample_records();
        let bundles = group_subject_obligations(&records);
        let bundle = &bundles[0];

        let obligations = render_obligations_module(bundle);
        assert!(obligations.contains(
            "def refineSpec\n    \
                 (extraPre : List Value → Prop)\n    \
                 (extraPost : List Value → Value → Prop) :\n    \
                 ItemSpec \"my_crate::math::inc\" where\n  \
               pre args := And (rustRequires args) (extraPre args)\n  \
               post args ret := And (rustEnsures args ret) (extraPost args ret)"
        ));
        assert!(obligations.contains(
            "def refineStatefulSpec\n    \
                 (extraPre : List Value → Memory → Prop)\n    \
                 (extraPost : List Value → Memory → Value → Memory → Prop) :\n    \
                 StatefulItemSpec \"my_crate::math::inc\" where\n  \
               pre args m := And (rustRequires args) (extraPre args m)\n  \
               post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)"
        ));
        assert!(obligations.contains(
            "def refineSafeSpec\n    \
                 (safetyDomain : List Value → Prop)\n    \
                 (extraPre : List Value → Prop)\n    \
                 (extraPost : List Value → Value → Prop) :\n    \
                 ItemSpec \"my_crate::math::inc\" where\n  \
               pre args := safetyDomain args\n  \
               post args ret :=\n    \
                 And (rustRequires args) (extraPre args) →\n      \
                   And (rustEnsures args ret) (extraPost args ret)"
        ));
        assert!(obligations.contains(
            "def refineSafeStatefulSpec\n    \
                 (safetyDomain : List Value → Memory → Prop)\n    \
                 (extraPre : List Value → Memory → Prop)\n    \
                 (extraPost : List Value → Memory → Value → Memory → Prop) :\n    \
                 StatefulItemSpec \"my_crate::math::inc\" where\n  \
               pre args m := safetyDomain args m\n  \
               post args m0 ret m1 :=\n    \
                 And (rustRequires args) (extraPre args m0) →\n      \
                   And (rustEnsures args ret) (extraPost args m0 ret m1)"
        ));

        let specs = render_specs_template(bundle);
        assert!(specs.contains("Obligations.MyCrate.math.inc.refineSpec"));
        assert!(specs.contains("Obligations.MyCrate.math.inc.rustRequires"));
        assert!(specs.contains("Obligations.MyCrate.math.inc.rustEnsures"));

        let default_proof = render_proof_template(bundle);
        assert!(!default_proof.contains("import Specs.MyCrate.math.inc"));
        assert!(!default_proof.contains("import Assumptions.MyCrate.math.inc"));
        assert!(default_proof.contains("open Anneal.Rustc.V2026_06_01.SymbolicEval"));
        assert!(default_proof.contains("open Anneal.Rustc.V2026_06_01.Lower"));
        assert!(default_proof.contains(
            "theorem verified : VerificationResult Obligations.MyCrate.math.inc.claim := by\n  sorry"
        ));

        let stateful_proof = render_proof_template_with_options(
            bundle,
            AuthoredItemModules {
                has_specs: true,
                has_legacy_specs_defs: false,
                has_assumptions: true,
                has_proof: false,
                is_stateful: true,
                ..AuthoredItemModules::default()
            },
        );
        assert!(stateful_proof.contains(
            "import Obligations.MyCrate.math.inc\n\
             import Specs.MyCrate.math.inc\n\
             import Assumptions.MyCrate.math.inc\n"
        ));
        assert!(stateful_proof.contains("open Anneal.Rustc.V2026_06_01.SymbolicEval"));
        assert!(stateful_proof.contains("open Anneal.Rustc.V2026_06_01.Lower"));
        assert!(stateful_proof.contains(
            "theorem verified : StatefulVerificationResult Obligations.MyCrate.math.inc.statefulClaim := by\n  sorry"
        ));
    }

    #[test]
    fn renders_equiv_total_and_crate_verify_modules() {
        let records = sample_records();
        let bundles = group_subject_obligations(&records);
        let bundle = &bundles[0];

        let obligations = render_obligations_module(bundle);
        assert!(obligations.contains("def refineEquivSpec"));
        assert!(obligations.contains("def equivClaim [spec : StatefulEquivItemSpec \"my_crate::math::inc\"] : StatefulEquivClaim :="));
        assert!(obligations.contains("def totalClaim [spec : TotalItemSpec \"my_crate::math::inc\"] : TotalClaim :="));
        assert!(obligations.contains("def refineModularSpec"));
        assert!(obligations.contains("def refineUbExceptionSpec"));
        assert!(obligations.contains("def modularClaim [spec : ModularItemSpec \"my_crate::math::inc\"] : ModularClaim :="));
        assert!(obligations.contains("def ubExceptionClaim [spec : UbExceptionItemSpec \"my_crate::math::inc\"] : UbExceptionClaim :="));

        let verify_modular = render_verify_module_with_options(
            bundle,
            AuthoredItemModules {
                has_specs: true,
                has_proof: true,
                is_modular: true,
                ..AuthoredItemModules::default()
            },
        );
        assert!(verify_modular.contains(
            "theorem verified : ModularVerificationResult Obligations.MyCrate.math.inc.modularClaim :=\n  Proof.MyCrate.math.inc.verified"
        ));

        let verify_ub_exc = render_verify_module_with_options(
            bundle,
            AuthoredItemModules {
                has_specs: true,
                has_proof: true,
                is_ub_exception: true,
                ..AuthoredItemModules::default()
            },
        );
        assert!(verify_ub_exc.contains(
            "theorem verified : UbExceptionVerificationResult Obligations.MyCrate.math.inc.ubExceptionClaim :=\n  Proof.MyCrate.math.inc.verified"
        ));
        assert!(verify_ub_exc.contains(
            "abbrev Certificate : Prop := UbExceptionVerificationResult Obligations.MyCrate.math.inc.ubExceptionClaim"
        ));

        let verify_equiv = render_verify_module_with_options(
            bundle,
            AuthoredItemModules {
                has_specs: true,
                has_proof: true,
                is_equiv: true,
                ..AuthoredItemModules::default()
            },
        );
        assert!(verify_equiv.contains("-- @anneal-def-id: my_crate::math::inc"));
        assert!(verify_equiv.contains(
            "theorem verified : StatefulEquivVerificationResult Obligations.MyCrate.math.inc.equivClaim :=
  Proof.MyCrate.math.inc.verified"
        ));
        assert!(verify_equiv.contains(
            "abbrev Certificate : Prop := StatefulEquivVerificationResult Obligations.MyCrate.math.inc.equivClaim"
        ));
        assert!(verify_modular.contains("theorem signatureMonomorphic :"));
        assert!(verify_ub_exc.contains("theorem signatureMonomorphic :"));
        assert!(!verify_equiv.contains("signatureMonomorphic"));

        let crate_verify = render_crate_verify_module("my_crate", &bundles);
        assert!(!crate_verify.contains("import Anneal"));
        assert!(crate_verify.contains("import Verify.MyCrate.math.inc"));
        assert!(crate_verify.contains("certificate := Verify.MyCrate.math.inc.Certificate"));
        assert!(crate_verify.contains("theorem verified : CrateVerificationResult crateClaim :="));
    }

    #[test]
    fn renders_rust_safe_total_and_equiv_attribute_specs() {
        let mut records = sample_records();
        records.push(UnitTargetRecord {
            target: CapturedTarget {
                def_id: "my_crate::math::__ANNEAL_EXT_SPEC_TARGET___anneal_attr_safe_total_inc"
                    .to_string(),
                mir_module_path: String::new(),
                mir_module_sha256: String::new(),
            },
            lean_module_name: String::new(),
            item_kind: CapturedItemKind::ExternalSpec,
            associated_subject_def_id: Some("my_crate::math::inc".to_string()),
            trait_impls: Vec::new(),
        });
        records.push(UnitTargetRecord {
            target: CapturedTarget {
                def_id: "my_crate::math::__ANNEAL_EXT_SPEC_TARGET___anneal_attr_equiv_inc_ref__for__inc"
                    .to_string(),
                mir_module_path: String::new(),
                mir_module_sha256: String::new(),
            },
            lean_module_name: String::new(),
            item_kind: CapturedItemKind::ExternalSpec,
            associated_subject_def_id: Some("my_crate::math::inc".to_string()),
            trait_impls: Vec::new(),
        });

        let bundles = group_subject_obligations(&records);
        assert_eq!(bundles.len(), 1);
        let bundle = &bundles[0];
        assert!(bundle.has_rust_safe_total_attr());
        assert_eq!(
            bundle.rust_equiv_target_module_suffix().as_deref(),
            Some("MyCrate.math.inc_ref")
        );

        let obligations = render_obligations_module(bundle);
        assert!(obligations.contains("import Mir.MyCrate.math.inc_ref"));
        assert!(obligations.contains(
            "instance rustSafeTotalSpec : ItemSpec \"my_crate::math::inc\" :=\n  \
               refineSafeSpec\n    \
                 (fun args => Trusted.Sequence.length args = Mir.MyCrate.math.inc.body.argCount)"
        ));
        assert!(obligations.contains(
            "instance rustEquivSpec : StatefulEquivItemSpec \"my_crate::math::inc\" :=\n  \
               refineEquivSpec\n    \
                 Mir.MyCrate.math.inc_ref.body"
        ));
    }

    #[test]
    fn renders_rust_trusted_assumptions_and_modular_default_proofs() {
        let mut records = sample_records();
        records.push(UnitTargetRecord {
            target: CapturedTarget {
                def_id: "my_crate::math::__ANNEAL_EXT_SPEC_TARGET___anneal_attr_trusted_inc"
                    .to_string(),
                mir_module_path: String::new(),
                mir_module_sha256: String::new(),
            },
            lean_module_name: String::new(),
            item_kind: CapturedItemKind::ExternalSpec,
            associated_subject_def_id: Some("my_crate::math::inc".to_string()),
            trait_impls: Vec::new(),
        });

        let bundles = group_subject_obligations(&records);
        assert_eq!(bundles.len(), 1);
        let bundle = &bundles[0];
        assert!(bundle.has_rust_trusted_attr());

        let generated_assumptions =
            render_generated_assumptions_module(bundle, AuthoredItemModules::default());
        assert!(generated_assumptions.contains("import Obligations.MyCrate.math.inc"));
        assert!(generated_assumptions.contains(
            "axiom rust_trusted_contract :\n  \
               Trusted.VerificationResult.VerificationResult Obligations.MyCrate.math.inc.claim"
        ));

        let generated_total_assumptions = render_generated_assumptions_module(
            bundle,
            AuthoredItemModules {
                is_total: true,
                ..AuthoredItemModules::default()
            },
        );
        assert!(generated_total_assumptions.contains(
            "axiom rust_trusted_contract :\n  \
               Trusted.VerificationResult.TotalVerificationResult Obligations.MyCrate.math.inc.totalClaim"
        ));

        let verify_trusted =
            render_verify_module_with_options(bundle, AuthoredItemModules::default());
        assert!(verify_trusted.contains("import Assumptions.MyCrate.math.inc"));
        assert!(verify_trusted.contains(
            "theorem verified : VerificationResult Obligations.MyCrate.math.inc.claim :=\n  \
               Assumptions.MyCrate.math.inc.rust_trusted_contract"
        ));

        let mut caller_bundle = sample_records();
        let mut caller_bundles = group_subject_obligations(&caller_bundle);
        let caller = &mut caller_bundles[0];
        caller.called_callees.push(CalleeContractRef {
            def_id: "my_crate::math::leaf".to_string(),
            item_module_suffix: "MyCrate.math.leaf".to_string(),
            req_module_suffix: Some("MyCrate.math.__anodized_fn_requires_leaf".to_string()),
            ens_module_suffix: Some("MyCrate.math.__anodized_fn_ensures_leaf".to_string()),
        });

        let caller_obligations = render_obligations_module(caller);
        assert!(caller_obligations.contains("import Obligations.MyCrate.math.leaf"));
        assert!(caller_obligations.contains("def defaultCallContract : MirCallContract where"));
        assert!(caller_obligations.contains(
            "envAssumed := Obligations.MyCrate.math.leaf.defaultCallContract.holdsOn"
        ));

        let caller_verify =
            render_verify_module_with_options(caller, AuthoredItemModules::default());
        assert!(caller_verify.contains("import Mir.MyCrate.math.leaf"));
        assert!(caller_verify.contains("import Mir.MyCrate.math.__anodized_fn_requires_leaf"));
        assert!(caller_verify.contains("import Mir.MyCrate.math.__anodized_fn_ensures_leaf"));
        assert!(caller_verify.contains("defaultModularProof"));
        assert!(caller_verify.contains("dischargeRustModularContractAuto"));
        assert!(caller_verify.contains("dischargeRustModularBoundedRange1Auto"));
        assert!(caller_verify.contains(
            "theorem verified : ModularVerificationResult Obligations.MyCrate.math.inc.modularClaim :=\n  \
               (inferInstance : ModularItemProof \"my_crate::math::inc\" Obligations.MyCrate.math.inc.modularClaim).verified"
        ));

        caller_bundle.push(UnitTargetRecord {
            target: CapturedTarget {
                def_id: "my_crate::math::__ANNEAL_EXT_SPEC_TARGET___anneal_attr_safe_total_inc"
                    .to_string(),
                mir_module_path: String::new(),
                mir_module_sha256: String::new(),
            },
            lean_module_name: String::new(),
            item_kind: CapturedItemKind::ExternalSpec,
            associated_subject_def_id: Some("my_crate::math::inc".to_string()),
            trait_impls: Vec::new(),
        });
        let total_bundles = group_subject_obligations(&caller_bundle);
        let total_verify =
            render_verify_module_with_options(&total_bundles[0], AuthoredItemModules::default());
        assert!(total_verify.contains("instance (priority := low) defaultProof :\n    TotalItemProof"));
        assert!(total_verify.contains("dischargeRustTotalPinnedContractAuto"));
        assert!(total_verify.contains("dischargeRustTotalBoundedRange1Auto"));
        assert!(total_verify.contains(
            "theorem verified : TotalVerificationResult Obligations.MyCrate.math.inc.totalClaim :=\n  \
               (inferInstance : TotalItemProof \"my_crate::math::inc\" Obligations.MyCrate.math.inc.totalClaim).verified"
        ));
        assert!(total_verify.contains("theorem signatureMonomorphic :"));
        assert!(caller_verify.contains("theorem signatureMonomorphic :"));
        assert!(!verify_trusted.contains("signatureMonomorphic"));
    }

    #[test]
    fn renders_signature_and_polymorphic_obligations() {
        let records = sample_records();
        let bundles = group_subject_obligations(&records);
        let bundle = &bundles[0];

        let obligations = render_obligations_module(bundle);
        assert!(obligations.contains(
            "def sigPre\n    \
                 (typeArgs : Trusted.MirAst.TypeSubst)\n    \
                 (args : List Value)\n    \
                 (mem : Memory) : Prop :=\n  \
               And (defaultPreFor typeArgs args)\n      \
                   (Trusted.VerificationResult.argsMatchSignature\n        \
                     (Mir.MyCrate.math.inc.body.instantiate typeArgs) args mem)"
        ));
        assert!(obligations.contains(
            "def sigPost\n    \
                 (typeArgs : Trusted.MirAst.TypeSubst)\n    \
                 (args : List Value)\n    \
                 (ret : Value)\n    \
                 (mem : Memory) : Prop :=\n  \
               And (defaultPostFor typeArgs args ret)\n      \
                   (Trusted.VerificationResult.retMatchesSignature\n        \
                     (Mir.MyCrate.math.inc.body.instantiate typeArgs) ret mem)"
        ));
        assert!(obligations.contains(
            "def claimFor\n    \
                 [spec : ItemSpec \"my_crate::math::inc\"]\n    \
                 (typeArgs : Trusted.MirAst.TypeSubst) : Claim :="
        ));
        assert!(obligations.contains(
            "def polyClaim [spec : ItemSpec \"my_crate::math::inc\"] : Prop :=\n  \
               ∀ (typeArgs : Trusted.MirAst.TypeSubst),\n    \
                 typeArgs.length = Mir.MyCrate.math.inc.body.typeParamCount →\n      \
                   VerificationResult (claimFor typeArgs)"
        ));
        assert!(obligations.contains(
            "def statefulClaimFor (typeArgs : Trusted.MirAst.TypeSubst) : StatefulClaim :=\n  \
               { body := Mir.MyCrate.math.inc.body.instantiate typeArgs\n    \
                 pre := fun args mem => sigPre typeArgs args mem\n    \
                 post := fun args _ ret mem => sigPost typeArgs args ret mem\n    \
                 callees := defaultCallees }"
        ));
        assert!(obligations.contains(
            "def polyStatefulClaim : Prop :=\n  \
               ∀ (typeArgs : Trusted.MirAst.TypeSubst),\n    \
                 typeArgs.length = Mir.MyCrate.math.inc.body.typeParamCount →\n      \
                   StatefulVerificationResult (statefulClaimFor typeArgs)"
        ));
        assert!(obligations.contains(
            "def totalClaimFor (typeArgs : Trusted.MirAst.TypeSubst) : TotalClaim :="
        ));
        assert!(obligations.contains(
            "def polyTotalClaim : Prop :=\n  \
               ∀ (typeArgs : Trusted.MirAst.TypeSubst),\n    \
                 typeArgs.length = Mir.MyCrate.math.inc.body.typeParamCount →\n      \
                   TotalVerificationResult (totalClaimFor typeArgs)"
        ));
        assert!(obligations.contains(
            "def modularClaimFor\n    \
                 [spec : ModularItemSpec \"my_crate::math::inc\"]\n    \
                 (typeArgs : Trusted.MirAst.TypeSubst) : ModularClaim :="
        ));
        assert!(obligations.contains(
            "def polyModularClaim [spec : ModularItemSpec \"my_crate::math::inc\"] : Prop :=\n  \
               ∀ (typeArgs : Trusted.MirAst.TypeSubst),\n    \
                 typeArgs.length = Mir.MyCrate.math.inc.body.typeParamCount →\n      \
                   ModularVerificationResult (modularClaimFor typeArgs)"
        ));
        assert!(obligations.contains(
            "def ubExceptionClaimFor\n    \
                 [spec : UbExceptionItemSpec \"my_crate::math::inc\"]\n    \
                 (typeArgs : Trusted.MirAst.TypeSubst) : UbExceptionClaim :="
        ));
        assert!(obligations.contains(
            "def polyUbExceptionClaim [spec : UbExceptionItemSpec \"my_crate::math::inc\"] : Prop :=\n  \
               ∀ (typeArgs : Trusted.MirAst.TypeSubst),\n    \
                 typeArgs.length = Mir.MyCrate.math.inc.body.typeParamCount →\n      \
                   UbExceptionVerificationResult (ubExceptionClaimFor typeArgs)"
        ));
        assert!(obligations.contains(
            "def artifactIdentity : ArtifactIdentity where\n  \
               defPath := \"my_crate::math::inc\"\n  \
               mirDialect := \"V2026_06_01\""
        ));
        assert!(obligations.contains(
            "def polyCertificate (P : Prop) : CrateClaim where\n  \
               crateName := \"my_crate::math::inc\"\n  \
               mirDialect := \"V2026_06_01\"\n  \
               items := [{ identity := artifactIdentity, certificate := P }]"
        ));

        let verify_poly = render_verify_module_with_options(
            bundle,
            AuthoredItemModules {
                has_proof: true,
                is_polymorphic: true,
                ..AuthoredItemModules::default()
            },
        );
        assert!(verify_poly.contains(
            "theorem verified :\n    \
                 CrateVerificationResult\n      \
                   (Obligations.MyCrate.math.inc.polyCertificate Obligations.MyCrate.math.inc.polyClaim) :=\n  \
               mkPolyVerificationResult\n    \
                 Obligations.MyCrate.math.inc.artifactIdentity\n    \
                 Proof.MyCrate.math.inc.verified"
        ));
        assert!(!verify_poly.contains("signatureMonomorphic"));
    }

    #[test]
    fn renders_transitive_default_callees_and_external_spec_contracts() {
        let mut records = sample_records();
        // Add a clause-less `#[external_spec(for = core::slice::from_raw_parts_mut)]`
        // sidecar and a claused `#[external_spec(for = dep_crate::helper)]` sidecar.
        records.push(UnitTargetRecord {
            target: CapturedTarget {
                def_id: "my_crate::math::spec_from_raw_parts_mut".to_string(),
                mir_module_path: "Mir/MyCrate/math/spec_from_raw_parts_mut.lean".to_string(),
                mir_module_sha256: "e".repeat(64),
            },
            lean_module_name: "Mir.MyCrate.math.spec_from_raw_parts_mut".to_string(),
            item_kind: CapturedItemKind::ExternalSpec,
            associated_subject_def_id: Some("core::slice::from_raw_parts_mut".to_string()),
            trait_impls: Vec::new(),
        });
        records.push(UnitTargetRecord {
            target: CapturedTarget {
                def_id: "my_crate::math::spec_dep_helper".to_string(),
                mir_module_path: "Mir/MyCrate/math/spec_dep_helper.lean".to_string(),
                mir_module_sha256: "f".repeat(64),
            },
            lean_module_name: "Mir.MyCrate.math.spec_dep_helper".to_string(),
            item_kind: CapturedItemKind::ExternalSpec,
            associated_subject_def_id: Some("dep_crate::helper".to_string()),
            trait_impls: Vec::new(),
        });
        records.push(UnitTargetRecord {
            target: CapturedTarget {
                def_id: "my_crate::math::__anodized_fn_requires_spec_dep_helper".to_string(),
                mir_module_path: "Mir/MyCrate/math/__anodized_fn_requires_spec_dep_helper.lean"
                    .to_string(),
                mir_module_sha256: "1".repeat(64),
            },
            lean_module_name: "Mir.MyCrate.math.__anodized_fn_requires_spec_dep_helper"
                .to_string(),
            item_kind: CapturedItemKind::InlineSpecRequires,
            associated_subject_def_id: Some("dep_crate::helper".to_string()),
            trait_impls: Vec::new(),
        });
        records.push(UnitTargetRecord {
            target: CapturedTarget {
                def_id: "my_crate::math::__anodized_fn_ensures_spec_dep_helper".to_string(),
                mir_module_path: "Mir/MyCrate/math/__anodized_fn_ensures_spec_dep_helper.lean"
                    .to_string(),
                mir_module_sha256: "2".repeat(64),
            },
            lean_module_name: "Mir.MyCrate.math.__anodized_fn_ensures_spec_dep_helper"
                .to_string(),
            item_kind: CapturedItemKind::InlineSpecEnsures,
            associated_subject_def_id: Some("dep_crate::helper".to_string()),
            trait_impls: Vec::new(),
        });

        let ext_contracts = collect_external_spec_contracts(&records);
        assert_eq!(ext_contracts.len(), 2);
        let raw_parts_ext = ext_contracts
            .get("core::slice::from_raw_parts_mut")
            .expect("clause-less external spec contract");
        assert_eq!(raw_parts_ext.req_module_suffix, None);
        assert_eq!(raw_parts_ext.ens_module_suffix, None);

        let dep_ext = ext_contracts
            .get("dep_crate::helper")
            .expect("claused external spec contract");
        assert_eq!(
            dep_ext.req_module_suffix.as_deref(),
            Some("MyCrate.math.__anodized_fn_requires_spec_dep_helper")
        );
        assert_eq!(
            dep_ext.ens_module_suffix.as_deref(),
            Some("MyCrate.math.__anodized_fn_ensures_spec_dep_helper")
        );

        let mut bundles = group_subject_obligations(&records);
        let bundle = &mut bundles[0];
        bundle.transitive_callees = vec![
            TransitiveCalleeRef {
                def_id: "dep_crate::step_a".to_string(),
                item_module_suffix: "DepCrate.step_a".to_string(),
            },
            TransitiveCalleeRef {
                def_id: "core::slice::<impl [T]>::len".to_string(),
                item_module_suffix: "Core.slice_impl_T_len".to_string(),
            },
        ];
        bundle.external_spec_callees = vec![raw_parts_ext.clone(), dep_ext.clone()];

        let obligations = render_obligations_module(bundle);
        assert!(obligations.contains("import Mir.DepCrate.step_a\n"));
        assert!(obligations.contains("import Mir.Core.slice_impl_T_len\n"));
        assert!(obligations.contains("import Mir.MyCrate.math.spec_from_raw_parts_mut\n"));
        assert!(obligations.contains("import Mir.MyCrate.math.spec_dep_helper\n"));
        assert!(obligations.contains(
            "import Mir.MyCrate.math.__anodized_fn_requires_spec_dep_helper\n"
        ));
        assert!(obligations.contains(
            "import Mir.MyCrate.math.__anodized_fn_ensures_spec_dep_helper\n"
        ));
        assert!(obligations.contains(
            "def defaultCallees : List CapturedMir :=\n  \
               [Mir.DepCrate.step_a.body, Mir.Core.slice_impl_T_len.body]"
        ));
        assert!(obligations.contains(
            "def externalCallContract_MyCrate_math_spec_from_raw_parts_mut : MirCallContract :=\n  \
               externalSpecCallContract\n    \
                 \"core::slice::from_raw_parts_mut\"\n    \
                 Mir.MyCrate.math.spec_from_raw_parts_mut.body\n    \
                 (fun _ => True)\n    \
                 (fun _ _ => True)"
        ));
        assert!(obligations.contains(
            "def externalCallContract_MyCrate_math_spec_dep_helper : MirCallContract :=\n  \
               externalSpecCallContract\n    \
                 \"dep_crate::helper\"\n    \
                 Mir.MyCrate.math.spec_dep_helper.body\n    \
                 (fun args => MirBoolPredicateHolds Mir.MyCrate.math.__anodized_fn_requires_spec_dep_helper.body args)\n    \
                 (fun args ret => MirBoolPredicateHolds Mir.MyCrate.math.__anodized_fn_ensures_spec_dep_helper.body (List.append args (List.cons ret List.nil)))"
        ));
        assert!(obligations.contains("callees := defaultCallees"));
        assert!(obligations.contains("implCallees := defaultCallees"));
        assert!(obligations.contains("specCallees := defaultCallees"));
    }

    fn record(def_id: &str, kind: CapturedItemKind, assoc: Option<&str>) -> UnitTargetRecord {
        let suffix: Vec<String> = def_id
            .split("::")
            .map(|seg| if seg == "my_crate" { "MyCrate".to_string() } else { seg.to_string() })
            .collect();
        UnitTargetRecord {
            target: CapturedTarget {
                def_id: def_id.to_string(),
                mir_module_path: format!("Mir/{}.lean", suffix.join("/")),
                mir_module_sha256: "0".repeat(64),
            },
            lean_module_name: format!("Mir.{}", suffix.join(".")),
            item_kind: kind,
            associated_subject_def_id: assoc.map(str::to_string),
            trait_impls: Vec::new(),
        }
    }

    #[test]
    fn external_spec_companions_match_by_exact_sidecar_path() {
        // `my_crate::helper` carries its own inline `#[spec]` companion and is
        // also the target of the `my_crate::spec_helper` sidecar. Both
        // companions are associated with `my_crate::helper`, and the target's
        // own companion sorts first, so association alone would mis-attribute
        // it to the sidecar contract.
        let records = vec![
            record("my_crate::helper", CapturedItemKind::Subject, None),
            record(
                "my_crate::__anodized_fn_requires_helper",
                CapturedItemKind::InlineSpecRequires,
                Some("my_crate::helper"),
            ),
            record(
                "my_crate::spec_helper",
                CapturedItemKind::ExternalSpec,
                Some("my_crate::helper"),
            ),
            record(
                "my_crate::__anodized_fn_requires_spec_helper",
                CapturedItemKind::InlineSpecRequires,
                Some("my_crate::helper"),
            ),
            record(
                "my_crate::__anodized_fn_ensures_spec_helper",
                CapturedItemKind::InlineSpecEnsures,
                Some("my_crate::helper"),
            ),
            // A clause-less sidecar whose name is a prefix of `spec_helper` must
            // not adopt `spec_helper`'s companions.
            record("my_crate::spec", CapturedItemKind::ExternalSpec, Some("dep::other")),
        ];
        let contracts = collect_external_spec_contracts(&records);
        let helper = contracts.get("my_crate::helper").expect("helper contract");
        assert_eq!(
            helper.req_module_suffix.as_deref(),
            Some("MyCrate.__anodized_fn_requires_spec_helper")
        );
        assert_eq!(
            helper.ens_module_suffix.as_deref(),
            Some("MyCrate.__anodized_fn_ensures_spec_helper")
        );
        let other = contracts.get("dep::other").expect("clause-less contract");
        assert_eq!(other.req_module_suffix, None);
        assert_eq!(other.ens_module_suffix, None);
    }

    #[test]
    fn default_env_assumed_conjoins_every_abstracted_callee_contract() {
        let records = vec![record("my_crate::caller", CapturedItemKind::Subject, None)];
        let mut bundles = group_subject_obligations(&records);
        let bundle = &mut bundles[0];

        let ext = |target: &str, sidecar: &str| ExternalSpecContractRef {
            target_def_id: target.to_string(),
            sidecar_module_suffix: sidecar.to_string(),
            req_module_suffix: None,
            ens_module_suffix: None,
        };

        bundle.external_spec_callees = vec![ext("dep::a", "MyCrate.spec_a")];
        let single = render_obligations_module(bundle);
        assert!(
            single.contains("envAssumed := externalCallContract_MyCrate_spec_a.holdsOn\n"),
            "a single contract keeps the bare holdsOn form:\n{single}"
        );

        bundle.external_spec_callees.push(ext("dep::b", "MyCrate.spec_b"));
        bundle.called_callees.push(CalleeContractRef {
            def_id: "my_crate::trusted".to_string(),
            item_module_suffix: "MyCrate.trusted".to_string(),
            req_module_suffix: None,
            ens_module_suffix: None,
        });
        let many = render_obligations_module(bundle);
        assert!(
            many.contains(
                "envAssumed := fun h => And (externalCallContract_MyCrate_spec_a.holdsOn h) \
                 (And (externalCallContract_MyCrate_spec_b.holdsOn h) \
                 (Obligations.MyCrate.trusted.defaultCallContract.holdsOn h))\n"
            ),
            "every abstracted callee contract must be assumed:\n{many}"
        );

        // The automatic modular discharge assumes a single memory-preserving
        // sibling contract and is not attempted for external-spec callees.
        let verify = render_verify_module_with_options(bundle, AuthoredItemModules::default());
        assert!(
            !verify.contains("dischargeRustModularContractAuto"),
            "external-spec callees must not use the memory-preserving modular discharge:\n{verify}"
        );
    }

    #[test]
    fn call_containing_companions_are_evaluated_with_default_spec_callees() {
        let records = sample_records();
        let mut bundles = group_subject_obligations(&records);
        let bundle = &mut bundles[0];
        bundle.spec_callees = vec![TransitiveCalleeRef {
            def_id: "core::num::<impl u32>::wrapping_add".to_string(),
            item_module_suffix: "Core.num_impl_u32_wrapping_add".to_string(),
        }];
        bundle
            .spec_companions_with_calls
            .insert("MyCrate.math.__anodized_fn_ensures_inc".to_string());

        let obligations = render_obligations_module(bundle);
        assert!(obligations.contains("import Mir.Core.num_impl_u32_wrapping_add\n"));
        assert!(obligations.contains(
            "def defaultSpecCallees : List CapturedMir :=\n  [Mir.Core.num_impl_u32_wrapping_add.body]"
        ));
        let spec_callees_pos = obligations.find("def defaultSpecCallees").unwrap();
        let default_pre_pos = obligations.find("def defaultPre").unwrap();
        assert!(spec_callees_pos < default_pre_pos);
        // The call-free `requires` companion keeps the plain form.
        assert!(obligations.contains(
            "MirBoolPredicateHolds Mir.MyCrate.math.__anodized_fn_requires_inc.body args"
        ));
        assert!(obligations.contains(
            "def defaultPost (args : List Value) (ret : Value) : Prop :=\n  \
             MirBoolPredicateHoldsWithCallees Mir.MyCrate.math.__anodized_fn_ensures_inc.body \
             defaultSpecCallees (List.append args (List.cons ret List.nil))"
        ));
        assert!(obligations.contains(
            "MirBoolPredicateHoldsWithCallees (Mir.MyCrate.math.__anodized_fn_ensures_inc.body.instantiate typeArgs) \
             defaultSpecCallees (List.append args (List.cons ret List.nil))"
        ));

        // Without linked spec callees, every companion keeps the plain form.
        bundle.spec_callees.clear();
        let plain = render_obligations_module(bundle);
        assert!(!plain.contains("defaultSpecCallees"));
        assert!(plain.contains(
            "MirBoolPredicateHolds Mir.MyCrate.math.__anodized_fn_ensures_inc.body \
             (List.append args (List.cons ret List.nil))"
        ));
    }

    #[test]
    fn render_proof_template_emits_modular_claim_when_bundle_has_abstracted_callees() {
        let records = vec![record("my_crate::caller", CapturedItemKind::Subject, None)];
        let mut bundles = group_subject_obligations(&records);
        let bundle = &mut bundles[0];
        bundle.external_spec_callees.push(ExternalSpecContractRef {
            target_def_id: "dep::ffi_op".to_string(),
            sidecar_module_suffix: "MyCrate.ext_ffi_op".to_string(),
            req_module_suffix: None,
            ens_module_suffix: None,
        });
        let specs_template = render_specs_template(bundle);
        assert!(
            specs_template.contains("instance : ModularItemSpec \"my_crate::caller\" where")
                && specs_template.contains("Obligations.MyCrate.caller.defaultModularSpec.envAssumed"),
            "specs template for subject with external_spec_callees must emit ModularItemSpec:\n{specs_template}"
        );
        let template = render_proof_template_with_options(bundle, AuthoredItemModules::default());
        assert!(
            template.contains(
                "theorem verified : ModularVerificationResult Obligations.MyCrate.caller.modularClaim := by"
            ),
            "proof template for subject with external_spec_callees must target modularClaim:\n{template}"
        );
        let verify_mod = render_verify_module_with_options(
            bundle,
            AuthoredItemModules {
                has_specs: true,
                is_modular: true,
                ..AuthoredItemModules::default()
            },
        );
        assert!(
            verify_mod.contains(
                "theorem verified : ModularVerificationResult Obligations.MyCrate.caller.modularClaim :="
            ),
            "verify module with authored ModularItemSpec and no Proof must target modularClaim:\n{verify_mod}"
        );
    }
}
