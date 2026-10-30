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
}

impl SubjectObligationBundle {
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
            | CapturedItemKind::UnsafeTraitImpl => {}
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

    let default_pre_expr = if has_contract_companions {
        let mut clauses = Vec::with_capacity(bundle.inline_requires.len() + 1);
        clauses.push(format!(
            "Trusted.Sequence.length args = Mir.{item}.body.argCount"
        ));
        for req in &bundle.inline_requires {
            let req_suffix = derive_item_module_suffix(req);
            clauses.push(format!("MirBoolPredicateHolds Mir.{req_suffix}.body args"));
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
                format!(
                    "MirBoolPredicateHolds Mir.{ens_suffix}.body \
                     (List.append args (List.cons ret List.nil))"
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
        "/-- Low-priority default `StatefulItemSpec` instance for `{def_id}`. -/\n"
    ));
    out.push_str(&format!(
        "instance (priority := low) defaultStatefulSpec :\n    \
           StatefulItemSpec \"{def_id}\" where\n  \
           pre := fun args _ => defaultPre args\n  \
           post := fun args _ ret _ => defaultPost args ret\n\n"
    ));

    out.push_str(&format!(
        "/-- Low-priority default `TotalItemSpec` instance for `{def_id}`. -/\n"
    ));
    out.push_str(&format!(
        "instance (priority := low) defaultTotalSpec :\n    \
           TotalItemSpec \"{def_id}\" where\n  \
           pre := fun args _ => defaultPre args\n  \
           post := fun args _ ret _ => defaultPost args ret\n\n"
    ));

    out.push_str(&format!(
        "/-- Low-priority default `ModularItemSpec` instance for `{def_id}`. -/\n"
    ));
    out.push_str(&format!(
        "instance (priority := low) defaultModularSpec :\n    \
           ModularItemSpec \"{def_id}\" where\n  \
           envAssumed := fun _ => True\n  \
           pre := fun args _ => defaultPre args\n  \
           post := fun args _ ret _ => defaultPost args ret\n\n"
    ));

    out.push_str(&format!(
        "/-- Low-priority default `UbExceptionItemSpec` instance for `{def_id}`. -/\n"
    ));
    out.push_str(&format!(
        "instance (priority := low) defaultUbExceptionSpec :\n    \
           UbExceptionItemSpec \"{def_id}\" where\n  \
           pre := fun args _ => defaultPre args\n  \
           strictSafetyPre := fun _ _ => False\n  \
           post := fun args _ ret _ => defaultPost args ret\n\n"
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
           {{ body := Mir.{item}.body, pre := spec.pre, post := spec.post }}\n\n"
    ));

    out.push_str(&format!(
        "/-- Canonical stateful verification claim for `{def_id}` synthesized\n    \
            from `StatefulItemSpec \"{def_id}\"`. -/\n"
    ));
    out.push_str(&format!(
        "def statefulClaim [spec : StatefulItemSpec \"{def_id}\"] : StatefulClaim :=\n  \
           {{ body := Mir.{item}.body, pre := spec.pre, post := spec.post }}\n\n"
    ));

    out.push_str(&format!(
        "/-- Canonical total-correctness verification claim for `{def_id}` synthesized\n    \
            from `TotalItemSpec \"{def_id}\"`. -/\n"
    ));
    out.push_str(&format!(
        "def totalClaim [spec : TotalItemSpec \"{def_id}\"] : TotalClaim :=\n  \
           {{ body := Mir.{item}.body, pre := spec.pre, post := spec.post }}\n\n"
    ));

    out.push_str(&format!(
        "/-- Canonical program-to-program equivalence claim for `{def_id}` synthesized\n    \
            from `StatefulEquivItemSpec \"{def_id}\"`. -/\n"
    ));
    out.push_str(&format!(
        "def equivClaim [spec : StatefulEquivItemSpec \"{def_id}\"] : StatefulEquivClaim :=\n  \
           {{ implBody := Mir.{item}.body, specBody := spec.specBody, pre := spec.pre, post := spec.post }}\n\n"
    ));

    out.push_str(&format!(
        "/-- Canonical modular verification claim for `{def_id}` synthesized\n    \
            from `ModularItemSpec \"{def_id}\"`. -/\n"
    ));
    out.push_str(&format!(
        "def modularClaim [spec : ModularItemSpec \"{def_id}\"] : ModularClaim :=\n  \
           {{ body := Mir.{item}.body, envAssumed := spec.envAssumed, pre := spec.pre, post := spec.post }}\n\n"
    ));

    out.push_str(&format!(
        "/-- Canonical scoped UB-exception verification claim for `{def_id}` synthesized\n    \
            from `UbExceptionItemSpec \"{def_id}\"`. -/\n"
    ));
    out.push_str(&format!(
        "def ubExceptionClaim [spec : UbExceptionItemSpec \"{def_id}\"] : UbExceptionClaim :=\n  \
           {{ body := Mir.{item}.body, pre := spec.pre, strictSafetyPre := spec.strictSafetyPre, post := spec.post }}\n\n"
    ));

    out.push_str(&format!("end Obligations.{item}\n"));
    out
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

/// Render the disposable `.anneal/generated/Verify/<Item>.lean` module for
/// `bundle` and `authored`.
///
/// Only imports `Specs.<Item>`, `Assumptions.<Item>`, and `Proof.<Item>` when
/// those authored files exist on disk under `anneal/proofs/`. When
/// `Proof.<Item>` does not exist on disk, emits a `priority := low`
/// `defaultProof` instance of `ItemProof` attempting bounded `WP` discharge.
pub fn render_verify_module_with_options(
    bundle: &SubjectObligationBundle,
    authored: AuthoredItemModules,
) -> String {
    let item = &bundle.item_module_suffix;
    let def_id = &bundle.subject.target.def_id;
    let mut out = String::new();

    out.push_str(&format!("-- @anneal-def-id: {def_id}\n"));
    out.push_str("import Trusted\n");
    if !authored.has_proof {
        out.push_str("import Anneal\n");
    }
    out.push_str(&format!("import Mir.{item}\n"));
    out.push_str(&format!("import Obligations.{item}\n"));
    if authored.has_specs {
        out.push_str(&format!("import Specs.{item}\n"));
    }
    if authored.has_assumptions {
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
        if authored.is_ub_exception {
            out.push_str(&format!(
                "/-- Kernel-checked scoped UB-exception verification certificate for `{def_id}`. -/\n\
                 theorem verified : UbExceptionVerificationResult Obligations.{item}.ubExceptionClaim :=\n  \
                   Proof.{item}.verified\n\n\
                 /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
                 abbrev Certificate : Prop := UbExceptionVerificationResult Obligations.{item}.ubExceptionClaim\n\n"
            ));
        } else if authored.is_modular {
            out.push_str(&format!(
                "/-- Kernel-checked modular verification certificate for `{def_id}`. -/\n\
                 theorem verified : ModularVerificationResult Obligations.{item}.modularClaim :=\n  \
                   Proof.{item}.verified\n\n\
                 /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
                 abbrev Certificate : Prop := ModularVerificationResult Obligations.{item}.modularClaim\n\n"
            ));
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
        } else if authored.is_stateful {
            out.push_str(&format!(
                "/-- Kernel-checked stateful verification certificate for `{def_id}`. -/\n\
                 theorem verified : StatefulVerificationResult Obligations.{item}.statefulClaim :=\n  \
                   Proof.{item}.verified\n\n\
                 /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
                 abbrev Certificate : Prop := StatefulVerificationResult Obligations.{item}.statefulClaim\n\n"
            ));
        } else {
            out.push_str(&format!(
                "/-- Kernel-checked verification certificate for `{def_id}`. -/\n\
                 theorem verified : VerificationResult Obligations.{item}.claim :=\n  \
                   Proof.{item}.verified\n\n\
                 /-- Proposition verified by `Verify.{item}.verified` for whole-crate rollup. -/\n\
                 abbrev Certificate : Prop := VerificationResult Obligations.{item}.claim\n\n"
            ));
        }
    } else {
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

    if authored.is_ub_exception {
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
    } else if authored.is_modular {
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
            "def claim [spec : ItemSpec \"my_crate::math::inc\"] : Claim :=\n  { body := Mir.MyCrate.math.inc.body, pre := spec.pre, post := spec.post }"
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
            }],
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
                },
            ],
            inline_ensures: Vec::new(),
            inline_qualifiers: Vec::new(),
            external_specs: Vec::new(),
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
}
