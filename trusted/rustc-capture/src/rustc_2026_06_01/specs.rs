//! Specification companion classification and `#[doc = "..."]` marker
//! extraction for `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`V2026_06_01`).
//!
//! `crates/anneal-spec` lowers user-written specification attributes into
//! standard Rust companion items and hidden `#[doc = "..."]` markers that
//! survive into `Runtime(PostCleanup)` MIR:
//!
//! - `#[spec]` / `#[embed_spec]` emit `__anodized_fn_requires_<fn>`,
//!   `__anodized_fn_ensures_<fn>`, and `__anodized_fn_qualifiers_<fn>`.
//! - `#[external_spec(for = <target>)]` emits `__ANNEAL_EXT_SPEC_TARGET_<fn>`.
//! - `#[model]` emits `__ANNEAL_MODEL_<ident>`.
//! - `#[invariant(<expr>)]` emits `__anneal_type_invariant_<type>(&self) -> bool`
//!   annotated with `#[doc = "\u{200b}anneal::type_invariant=<TypeName>"]`.
//! - `#[unsafe_impl(...)]` emits `__anneal_unsafe_impl_<Trait>_for_<Type>() -> bool`
//!   annotated with `#[doc = "\u{200b}anneal::unsafe_impl=<Trait>::<Type>"]`.
//!
//! Every `rustc` query in this module quotes and links to `rustc` at commit
//! `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` per `agent_docs/trusted-rust.md`.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_middle::ty::TyCtxt;

use crate::lean_emit::IrContractRole;
use crate::manifest::CapturedItemKind;
use crate::rustc_2026_06_01::mir_lower::canonical_def_path;

/// Prefix emitted by `anodized` for synthetic precondition companion functions.
pub const ANODIZED_REQUIRES_PREFIX: &str = "__anodized_fn_requires_";

/// Prefix emitted by `anodized` for synthetic postcondition companion
/// functions.
pub const ANODIZED_ENSURES_PREFIX: &str = "__anodized_fn_ensures_";

/// Prefix emitted by `anodized` for synthetic qualifier bitmask constants.
pub const ANODIZED_QUALIFIERS_PREFIX: &str = "__anodized_fn_qualifiers_";

/// Prefix emitted by `#[anneal::external_spec]` for target path marker
/// constants.
pub const ANNEAL_EXT_SPEC_PREFIX: &str = "__ANNEAL_EXT_SPEC_TARGET_";

/// Prefix emitted by `#[anneal_spec::external_spec]` for target path marker
/// constants.
pub const ANNEAL_EXT_SPEC_TARGET_PREFIX: &str = "__ANNEAL_EXT_SPEC_TARGET_";

/// Prefix emitted by `#[anneal_spec::model]` for model marker constants.
pub const ANNEAL_MODEL_PREFIX: &str = "__ANNEAL_MODEL_";

/// Prefix emitted by `#[anneal_spec::invariant]` for companion type-invariant
/// methods.
pub const ANNEAL_TYPE_INVARIANT_FN_PREFIX: &str = "__anneal_type_invariant_";

/// Prefix emitted by `#[anneal_spec::unsafe_impl]` for companion `unsafe impl`
/// safety witness functions.
pub const ANNEAL_UNSAFE_IMPL_FN_PREFIX: &str = "__anneal_unsafe_impl_";

/// Doc-attribute payload prefix emitted by `#[anneal_spec::invariant]`
/// (`#[doc = "\u{200b}anneal::type_invariant=<TypeName>"]`).
pub const ANNEAL_TYPE_INVARIANT_DOC_MARKER: &str = "anneal::type_invariant=";

/// Doc-attribute payload prefix emitted by `#[anneal_spec::unsafe_impl]`
/// (`#[doc = "\u{200b}anneal::unsafe_impl=<Trait>::<Type>"]`).
pub const ANNEAL_UNSAFE_IMPL_DOC_MARKER: &str = "anneal::unsafe_impl=";

/// Doc-attribute payload prefix emitted by `#[anneal_spec::unsafe_trait]`
/// (`#[doc = "\u{200b}anneal::unsafe_trait=<TraitName>"]`).
pub const ANNEAL_UNSAFE_TRAIT_DOC_MARKER: &str = "anneal::unsafe_trait=";

/// Structured specification marker extracted from an item's `#[doc = "..."]`
/// attributes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DocSpecMarker {
    /// Type invariant predicate targeting `<TypeName>`.
    TypeInvariant(String),
    /// `unsafe impl` witness targeting `<Trait>::<Type>`.
    UnsafeTraitImpl(String),
}

/// Parses a single `#[doc = "..."]` string for an `anneal::type_invariant=` or
/// `anneal::unsafe_impl=` marker, stripping any leading zero-width space
/// (`\u{200b}`).
pub fn parse_doc_spec_marker(doc_str: &str) -> Option<DocSpecMarker> {
    for raw_line in doc_str.lines() {
        let line = raw_line.trim().trim_start_matches('\u{200b}').trim();
        if let Some(rest) = line.strip_prefix(ANNEAL_TYPE_INVARIANT_DOC_MARKER) {
            let target = rest.trim();
            if !target.is_empty() {
                return Some(DocSpecMarker::TypeInvariant(target.to_owned()));
            }
        }
        if let Some(rest) = line.strip_prefix(ANNEAL_UNSAFE_IMPL_DOC_MARKER) {
            let target = rest.trim();
            if !target.is_empty() {
                return Some(DocSpecMarker::UnsafeTraitImpl(target.to_owned()));
            }
        }
    }
    None
}

/// Inspects all HIR attributes attached to `def_id` via `tcx.get_all_attrs` and
/// extracts any Anneal doc specification marker via `Attribute::doc_str`.
///
/// `rustc` (`compiler/rustc_middle/src/ty/context.rs` and
/// `compiler/rustc_hir/src/attrs/mod.rs`) defines `TyCtxt::get_all_attrs` and
/// `Attribute::doc_str` as:
///
/// >```text
/// >pub fn get_all_attrs(self, did: impl Into<DefId>) -> &'tcx [Attribute] {
/// >    ...
/// >}
/// >```
///
/// >```text
/// >pub fn doc_str(&self) -> Option<Symbol> {
/// >    match self {
/// >        Attribute::Parsed(AttributeKind::DocComment { comment, .. }) => Some(*comment),
/// >        Attribute::Unparsed(attr) => attr.doc_str(),
/// >    }
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_hir/src/attrs/mod.rs#L653-L664
#[allow(deprecated)]
pub fn extract_doc_spec_marker(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DocSpecMarker> {
    for attr in tcx.get_all_attrs(def_id) {
        if let Some(sym) = attr.doc_str()
            && let Some(marker) = parse_doc_spec_marker(sym.as_str())
        {
            return Some(marker);
        }
    }
    None
}

/// Classification of a local MIR item into its `CapturedItemKind`, Lean
/// `IrContractRole`, and optional `associated_subject_def_id`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ItemClassification {
    /// Manifest item role (`subject`, `inline_spec_requires`, `type_invariant`,
    /// `unsafe_trait_impl`, etc.).
    pub item_kind: CapturedItemKind,
    /// Lean `ContractRole` constructor emitted in `def body : CapturedMir`.
    pub contract_role: IrContractRole,
    /// Canonical `def_id` of the subject item when this item is a specification
    /// companion or `unsafe impl` witness.
    pub associated_subject_def_id: Option<String>,
}

type ParentKey = Option<(u32, u32)>;

fn opt_parent_key(tcx: TyCtxt<'_>, def_id: DefId) -> ParentKey {
    tcx.opt_parent(def_id)
        .map(|p| (p.krate.as_u32(), p.index.as_u32()))
}

/// Climbs past an enclosing `impl` block (if any) so inherent methods inside a
/// companion `impl` block resolve relative to the enclosing module.
fn enclosing_module_parent_key(tcx: TyCtxt<'_>, def_id: DefId) -> ParentKey {
    let parent = tcx.opt_parent(def_id)?;
    if matches!(tcx.def_kind(parent), DefKind::Impl { .. }) {
        tcx.opt_parent(parent)
            .map(|p| (p.krate.as_u32(), p.index.as_u32()))
    } else {
        Some((parent.krate.as_u32(), parent.index.as_u32()))
    }
}

/// Crate-wide index of local `DefId`s and Anneal/anodized specification markers
/// used to link companion items to their subject `def_id`.
pub struct CrateContractIndex {
    crate_name: String,
    /// Map from `(parent_def_id, item_ident)` to canonical `def_path`.
    siblings_by_parent: BTreeMap<(ParentKey, String), String>,
    /// Set of all canonical `def_path`s in the local crate.
    local_def_paths: BTreeSet<String>,
    /// Map from `(parent_def_id, spec_fn_ident)` to resolved external target
    /// `def_path`.
    external_spec_targets: BTreeMap<(ParentKey, String), String>,
    /// Set of `(parent_def_id, model_fn_ident)` marked with `#[anneal::model]`.
    model_items: BTreeSet<(ParentKey, String)>,
}

impl CrateContractIndex {
    /// Builds the contract index by scanning all local MIR keys in `tcx`.
    pub fn build(tcx: TyCtxt<'_>, local_defs: &[LocalDefId]) -> Self {
        let crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
        let mut siblings_by_parent = BTreeMap::new();
        let mut local_def_paths = BTreeSet::new();

        for &local_def_id in local_defs {
            let def_id = local_def_id.to_def_id();
            let def_path = canonical_def_path(tcx, def_id);
            local_def_paths.insert(def_path.clone());
            if let Some(ident) = item_short_name(tcx, def_id) {
                let parent = opt_parent_key(tcx, def_id);
                siblings_by_parent.insert((parent, ident), def_path);
            }
        }

        let mut external_spec_targets = BTreeMap::new();
        let mut model_items = BTreeSet::new();

        for &local_def_id in local_defs {
            let def_id = local_def_id.to_def_id();
            let Some(ident) = item_short_name(tcx, def_id) else {
                continue;
            };
            let parent = opt_parent_key(tcx, def_id);
            if let Some(spec_ident) = ident.strip_prefix(ANNEAL_EXT_SPEC_TARGET_PREFIX) {
                let raw_target =
                    eval_const_str_item(tcx, def_id).unwrap_or_else(|| spec_ident.to_owned());
                let resolved_target = normalize_target_path(
                    &crate_name,
                    &raw_target,
                    parent,
                    &siblings_by_parent,
                    &local_def_paths,
                );
                external_spec_targets.insert((parent, spec_ident.to_owned()), resolved_target);
            } else if let Some(model_ident) = ident.strip_prefix(ANNEAL_MODEL_PREFIX) {
                let target_ident =
                    eval_const_str_item(tcx, def_id).unwrap_or_else(|| model_ident.to_owned());
                model_items.insert((parent, model_ident.to_owned()));
                model_items.insert((parent, target_ident));
            }
        }

        Self {
            crate_name,
            siblings_by_parent,
            local_def_paths,
            external_spec_targets,
            model_items,
        }
    }

    /// Classifies `def_id` into its `CapturedItemKind`, `IrContractRole`, and
    /// `associated_subject_def_id`.
    pub fn classify(&self, tcx: TyCtxt<'_>, def_id: DefId) -> ItemClassification {
        let parent = opt_parent_key(tcx, def_id);
        let mod_parent = enclosing_module_parent_key(tcx, def_id);
        let def_path = canonical_def_path(tcx, def_id);

        if let Some(doc_marker) = extract_doc_spec_marker(tcx, def_id) {
            return match doc_marker {
                DocSpecMarker::TypeInvariant(raw_type) => {
                    let subj = self.resolve_type_invariant_subject(&raw_type, &def_path, mod_parent);
                    ItemClassification {
                        item_kind: CapturedItemKind::TypeInvariant,
                        contract_role: IrContractRole::Model,
                        associated_subject_def_id: Some(subj),
                    }
                }
                DocSpecMarker::UnsafeTraitImpl(raw_impl_target) => {
                    let subj = normalize_target_path(
                        &self.crate_name,
                        &raw_impl_target,
                        mod_parent,
                        &self.siblings_by_parent,
                        &self.local_def_paths,
                    );
                    ItemClassification {
                        item_kind: CapturedItemKind::UnsafeTraitImpl,
                        contract_role: IrContractRole::Subject,
                        associated_subject_def_id: Some(subj),
                    }
                }
            };
        }

        let Some(ident) = item_short_name(tcx, def_id) else {
            return ItemClassification {
                item_kind: CapturedItemKind::Subject,
                contract_role: IrContractRole::Subject,
                associated_subject_def_id: None,
            };
        };

        if let Some(fn_ident) = ident.strip_prefix(ANODIZED_REQUIRES_PREFIX) {
            let subj =
                self.resolve_companion_subject(parent, fn_ident, &def_path, ANODIZED_REQUIRES_PREFIX);
            return ItemClassification {
                item_kind: CapturedItemKind::InlineSpecRequires,
                contract_role: IrContractRole::Requires(subj.clone()),
                associated_subject_def_id: Some(subj),
            };
        }

        if let Some(fn_ident) = ident.strip_prefix(ANODIZED_ENSURES_PREFIX) {
            let subj =
                self.resolve_companion_subject(parent, fn_ident, &def_path, ANODIZED_ENSURES_PREFIX);
            return ItemClassification {
                item_kind: CapturedItemKind::InlineSpecEnsures,
                contract_role: IrContractRole::Ensures(subj.clone()),
                associated_subject_def_id: Some(subj),
            };
        }

        if let Some(fn_ident) = ident.strip_prefix(ANODIZED_QUALIFIERS_PREFIX) {
            let subj = self.resolve_companion_subject(
                parent,
                fn_ident,
                &def_path,
                ANODIZED_QUALIFIERS_PREFIX,
            );
            return ItemClassification {
                item_kind: CapturedItemKind::InlineSpecQualifiers,
                contract_role: IrContractRole::Model,
                associated_subject_def_id: Some(subj),
            };
        }

        if let Some(spec_ident) = ident.strip_prefix(ANNEAL_EXT_SPEC_TARGET_PREFIX) {
            let subj = self
                .external_spec_targets
                .get(&(parent, spec_ident.to_owned()))
                .cloned()
                .unwrap_or_else(|| {
                    self.resolve_companion_subject(
                        parent,
                        spec_ident,
                        &def_path,
                        ANNEAL_EXT_SPEC_TARGET_PREFIX,
                    )
                });
            return ItemClassification {
                item_kind: CapturedItemKind::ExternalSpec,
                contract_role: IrContractRole::ExternalSpec(subj.clone()),
                associated_subject_def_id: Some(subj),
            };
        }

        if ident.starts_with(ANNEAL_MODEL_PREFIX)
            || self.model_items.contains(&(parent, ident.clone()))
        {
            return ItemClassification {
                item_kind: CapturedItemKind::Model,
                contract_role: IrContractRole::Model,
                associated_subject_def_id: None,
            };
        }

        if let Some(ext_target) = self.external_spec_targets.get(&(parent, ident.clone())) {
            return ItemClassification {
                item_kind: CapturedItemKind::ExternalSpec,
                contract_role: IrContractRole::ExternalSpec(ext_target.clone()),
                associated_subject_def_id: Some(ext_target.clone()),
            };
        }

        if let Some(type_snake) = ident.strip_prefix(ANNEAL_TYPE_INVARIANT_FN_PREFIX) {
            let subj = self.resolve_type_invariant_subject(type_snake, &def_path, mod_parent);
            return ItemClassification {
                item_kind: CapturedItemKind::TypeInvariant,
                contract_role: IrContractRole::Model,
                associated_subject_def_id: Some(subj),
            };
        }

        if let Some(rest) = ident.strip_prefix(ANNEAL_UNSAFE_IMPL_FN_PREFIX)
            && let Some((trait_name, type_name)) = rest.split_once("_for_")
            && !trait_name.is_empty()
            && !type_name.is_empty()
        {
            let subj = format!("{trait_name}::{type_name}");
            return ItemClassification {
                item_kind: CapturedItemKind::UnsafeTraitImpl,
                contract_role: IrContractRole::Subject,
                associated_subject_def_id: Some(subj),
            };
        }

        ItemClassification {
            item_kind: CapturedItemKind::Subject,
            contract_role: IrContractRole::Subject,
            associated_subject_def_id: None,
        }
    }

    fn resolve_type_invariant_subject(
        &self,
        raw_type: &str,
        companion_def_path: &str,
        mod_parent: ParentKey,
    ) -> String {
        // When the invariant method is an inherent method `<mod>::<Type>::__anneal_type_invariant_*`,
        // stripping the trailing `::<fn_ident>` yields the exact canonical path `<mod>::<Type>`.
        if let Some((parent_path, _fn_name)) = companion_def_path.rsplit_once("::")
            && parent_path.ends_with(&format!("::{raw_type}"))
        {
            return parent_path.to_owned();
        }
        normalize_target_path(
            &self.crate_name,
            raw_type,
            mod_parent,
            &self.siblings_by_parent,
            &self.local_def_paths,
        )
    }

    fn resolve_companion_subject(
        &self,
        parent: ParentKey,
        fn_ident: &str,
        companion_def_path: &str,
        prefix: &str,
    ) -> String {
        if let Some(ext_target) = self.external_spec_targets.get(&(parent, fn_ident.to_owned())) {
            return ext_target.clone();
        }
        if let Some(sibling_path) = self.siblings_by_parent.get(&(parent, fn_ident.to_owned())) {
            return sibling_path.clone();
        }
        let prefixed_tail = format!("{prefix}{fn_ident}");
        if let Some(stripped) = companion_def_path.strip_suffix(&prefixed_tail) {
            return format!("{stripped}{fn_ident}");
        }
        format!("{}::{fn_ident}", self.crate_name)
    }
}

pub(crate) fn normalize_target_path(
    crate_name: &str,
    raw_target: &str,
    parent: ParentKey,
    siblings_by_parent: &BTreeMap<(ParentKey, String), String>,
    local_def_paths: &BTreeSet<String>,
) -> String {
    let cleaned = raw_target
        .split("::")
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>()
        .join("::");
    if cleaned.is_empty() {
        return crate_name.to_owned();
    }
    if local_def_paths.contains(&cleaned) || cleaned.starts_with(&format!("{crate_name}::")) {
        return cleaned;
    }
    if !cleaned.contains("::") {
        if let Some(sibling) = siblings_by_parent.get(&(parent, cleaned.clone())) {
            return sibling.clone();
        }
    }
    let crate_prefixed = format!("{crate_name}::{cleaned}");
    if local_def_paths.contains(&crate_prefixed) || !cleaned.contains("::") {
        return crate_prefixed;
    }
    cleaned
}

pub(crate) fn item_short_name(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    if let Some(sym) = tcx.opt_item_name(def_id) {
        return Some(sym.to_string());
    }
    let path = tcx.def_path_str(def_id);
    path.rsplit("::").next().map(str::to_owned)
}

/// Evaluates a `const _: &str = "..."` item via `tcx.const_eval_poly` and
/// extracts its UTF-8 string contents from the referenced global allocation.
pub(crate) fn eval_const_str_item(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    let val = tcx.const_eval_poly(def_id).ok()?;
    let bytes = val.try_get_slice_bytes_for_diagnostics(tcx)?;
    std::str::from_utf8(bytes).ok().map(str::to_owned)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_doc_spec_marker_detects_type_invariant_and_unsafe_impl() {
        assert_eq!(
            parse_doc_spec_marker("\u{200b}anneal::type_invariant=NonZeroU32"),
            Some(DocSpecMarker::TypeInvariant("NonZeroU32".to_owned()))
        );
        assert_eq!(
            parse_doc_spec_marker("  anneal::type_invariant=demo::Bounded  "),
            Some(DocSpecMarker::TypeInvariant("demo::Bounded".to_owned()))
        );
        assert_eq!(
            parse_doc_spec_marker("\u{200b}anneal::unsafe_impl=Zeroable::Packet"),
            Some(DocSpecMarker::UnsafeTraitImpl(
                "Zeroable::Packet".to_owned()
            ))
        );
        assert_eq!(parse_doc_spec_marker("ordinary documentation comment"), None);
    }
}
