// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Crate-level capture: items, signatures, ADTs, specifications, and the
//! assembly of `ir::Crate`.
//!
//! # Completeness
//!
//! The capture must describe the *whole* crate: an item it skipped would be
//! code `rustc` compiles but Anneal never checks. This module therefore
//! enumerates the crate from `rustc`'s own tables and classifies every entry:
//!
//! - every item (`hir_crate_items`: free items, trait items, impl items,
//!   foreign items), and
//! - every body (`hir_body_owners`: functions, constants, inline `const`
//!   blocks, closures, statics, and anonymous constants such as array
//!   lengths).
//!
//! Each entry is either captured or rejected. Items with no runtime behavior
//! (`use`, `extern crate`, `macro_rules!` definitions) are accepted without
//! being represented. There is no "skip" outcome.
//!
//! # Post-expansion structures
//!
//! Everything here is read after macro expansion, name resolution, and
//! `#[cfg]` stripping. Consequences:
//!
//! - Macros need no separate treatment. Whatever a macro expands to is an
//!   ordinary item or body here and is checked like hand-written code.
//!   Because the capture reads `rustc`'s expanded HIR and MIR directly, a
//!   textual scanner and `rustc` can never disagree about what items the
//!   source contains.
//! - An item removed by `#[cfg]` does not exist for `rustc` and is not in the
//!   compiled program, so there is nothing to verify. The capture fixes the
//!   configuration itself (no `--cfg` flags), and `main.rs` captures the
//!   crate under both Cargo's debug and release configurations and rejects
//!   it if the results differ, so code that exists in only one of them
//!   (`#[cfg(debug_assertions)]`) is rejected rather than half-verified.
//!
//! Source citations are paths in `rust-lang/rust` at the pinned toolchain
//! commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`
//! (`https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/<path>`),
//! whose sources ship in the pinned toolchain's `rustc-src` component.

use std::collections::{BTreeMap, BTreeSet};

use rustc_abi::ExternAbi;
use rustc_hir::def::DefKind;
use rustc_hir::{self as hir, HirId, LangItem};
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
use rustc_middle::ty::{self, GenericParamDefKind, TyCtxt, TypingEnv};
use rustc_span::def_id::{CRATE_DEF_ID, LocalDefId};

use crate::extract::{self, Res};
use crate::hook;
use crate::ir;
use crate::spec::{self, Directive};

/// Accumulates rejection reasons so a user sees every problem at once.
#[derive(Default)]
struct Errors(Vec<String>);

impl Errors {
    fn push(
        &mut self,
        tcx: TyCtxt<'_>,
        def: LocalDefId,
        msg: impl std::fmt::Display,
    ) {
        let path = tcx.def_path_str(def);
        let path = if path.is_empty() { "crate root" } else { &path };
        self.0.push(format!("`{path}`: {msg}"));
    }
}

/// Captures the crate `tcx` is compiling.
pub fn capture_crate(tcx: TyCtxt<'_>) -> Res<ir::Crate> {
    let mut errs = Errors::default();
    check_session(tcx, &mut errs);

    // Directives by the item they are attached to. Collected first because
    // functions and ADTs consume them below.
    let mut directives = collect_directives(tcx, &mut errs);

    let mut functions = Vec::new();
    let mut adts = Vec::new();
    let items = tcx.hir_crate_items(());

    for id in items.free_items() {
        let def = id.owner_id.def_id;
        // Items nested in function bodies or other items would need names
        // and scoping rules the model does not have.
        if tcx.local_parent(def) != CRATE_DEF_ID {
            errs.push(
                tcx,
                def,
                "items nested inside other items are not supported",
            );
            continue;
        }
        match tcx.def_kind(def) {
            DefKind::Fn => {
                if let Some(f) = function(
                    tcx,
                    def,
                    directives.remove(&def.local_def_index.as_u32()),
                    &mut errs,
                ) {
                    functions.push(f);
                }
            }
            DefKind::Struct => {
                if let Some(a) = adt(
                    tcx,
                    def,
                    directives.remove(&def.local_def_index.as_u32()),
                    &mut errs,
                ) {
                    adts.push(a);
                }
            }
            DefKind::Trait => trait_def(tcx, def, &mut errs),
            DefKind::Impl { of_trait: true } => trait_impl(tcx, def, &mut errs),
            // A free `const`'s body is captured with the other bodies below.
            DefKind::Const { .. } => {}
            // No runtime behavior: imports, the compiler-injected
            // `extern crate std` and prelude `use`, and `macro_rules!`
            // definitions (already expanded wherever they are used).
            DefKind::Use | DefKind::ExternCrate | DefKind::Macro(_) => {}
            other => {
                errs.push(tcx, def, format!("unsupported item kind {other:?}"))
            }
        }
    }
    for id in items.trait_items() {
        let def = id.owner_id.def_id;
        match tcx.def_kind(def) {
            DefKind::AssocConst { .. } => {
                if tcx.defaultness(def).has_value() {
                    errs.push(
                        tcx,
                        def,
                        "default bodies on trait associated constants are not \
                         supported",
                    );
                }
            }
            _ => errs.push(
                tcx,
                def,
                "trait items other than associated constants are not supported",
            ),
        }
    }
    for id in items.impl_items() {
        let def = id.owner_id.def_id;
        if !matches!(tcx.def_kind(def), DefKind::AssocConst { .. }) {
            errs.push(
                tcx,
                def,
                "impl items other than associated constants are not supported",
            );
        }
    }
    for id in items.foreign_items() {
        errs.push(
            tcx,
            id.owner_id.def_id,
            "foreign (`extern` block) items are not supported",
        );
    }
    for (def, _) in directives {
        let def = LocalDefId { local_def_index: def.into() };
        errs.push(
            tcx,
            def,
            "Anneal directives are only accepted on functions and structs",
        );
    }

    // Bodies. Every body owner is a function (already classified above) or
    // a constant; anything else is rejected.
    let fn_defs: BTreeSet<_> =
        functions.iter().map(|f: &ir::Function| f.def).collect();
    let mut bodies = BTreeMap::new();
    let mut constants = Vec::new();
    for def in tcx.hir_body_owners() {
        let idx = def.local_def_index.as_u32();
        let is_const = match tcx.def_kind(def) {
            DefKind::Fn => false,
            DefKind::AssocConst { .. }
                if matches!(
                    tcx.def_kind(tcx.local_parent(def)),
                    DefKind::Trait
                ) =>
            {
                // A default body on a trait associated constant; rejected in
                // the `trait_items` check above.
                continue;
            }
            DefKind::Const { .. }
            | DefKind::AssocConst { .. }
            | DefKind::InlineConst => true,
            other => {
                errs.push(tcx, def, format!("unsupported body kind {other:?}"));
                continue;
            }
        };
        if !is_const && !fn_defs.contains(&idx) {
            // A function that `function` rejected; its error is recorded.
            continue;
        }
        match hook::captured_body(tcx, def) {
            Ok(b) => {
                if is_const
                    && (!b.arg_tys.is_empty() || b.ret_ty != ir::Ty::Unit)
                {
                    errs.push(
                        tcx,
                        def,
                        "only constants of type `()` are supported",
                    );
                }
                if is_const {
                    constants.push(ir::Constant {
                        def: idx,
                        path: tcx.def_path_str(def),
                    });
                }
                bodies.insert(idx, b);
            }
            Err(e) => errs.push(tcx, def, e),
        }
    }

    for f in &functions {
        let def = LocalDefId { local_def_index: f.def.into() };
        if let Some(b) = bodies.get_mut(&f.def) {
            if let ir::FnKind::Exported { requires, .. } = &f.kind {
                b.requires = requires.clone();
            }
            check_signature(tcx, def, b, &mut errs);
        }
    }
    check_references(tcx, &bodies, &functions, &constants, &mut errs);
    let order = match dependency_order(&bodies) {
        Ok(o) => o,
        Err(e) => {
            errs.0.push(e);
            Vec::new()
        }
    };

    if !errs.0.is_empty() {
        return Err(errs.0.join("\n"));
    }
    if !functions.iter().any(|f| f.kind != ir::FnKind::Private) {
        return Err("the crate defines no public functions".into());
    }
    Ok(ir::Crate {
        bodies: order
            .into_iter()
            .map(|d| (d, bodies.remove(&d).unwrap()))
            .collect(),
        constants,
        functions,
        adts,
    })
}

/// Session-wide preconditions of the model.
fn check_session(tcx: TyCtxt<'_>, errs: &mut Errors) {
    // `#![feature(..)]` would let the crate use unstable language features
    // that change the meaning of the structures read here (for example,
    // `unsafe_fields`, `rustc_attrs`, or `intrinsics`). The capture links
    // `rustc`'s nightly libraries, so `rustc` itself would accept them.
    let features = tcx.features();
    for f in features.enabled_lang_features() {
        errs.push(
            tcx,
            CRATE_DEF_ID,
            format!("unstable feature `{}` is not supported", f.gate_name),
        );
    }
    for f in features.enabled_lib_features() {
        errs.push(
            tcx,
            CRATE_DEF_ID,
            format!(
                "unstable library feature `{}` is not supported",
                f.gate_name
            ),
        );
    }
    // `Trusted.evalTyByteSize` fixes `usize` and `&T` at 8 bytes.
    if tcx.data_layout.pointer_size().bytes() != 8 {
        errs.push(
            tcx,
            CRATE_DEF_ID,
            "the target's pointer size is not 8 bytes",
        );
    }
}

/// Collects every `anneal:` directive in the crate's HIR attribute table.
///
/// Every HIR node's attributes are stored in its owner's `AttributeMap`
/// (`compiler/rustc_hir/src/hir.rs#L1641-L1649`), so walking the attribute
/// map of every owner, plus the crate root's, visits every attribute in the
/// crate: on items, fields, parameters, statements, and expressions alike.
/// A directive is accepted only on an owner itself (`local_id == 0`), and
/// only if the owner is a free function or struct; placement on anything
/// else is reported.
///
/// `#[doc = ".."]` and `///` comments both become
/// `AttributeKind::DocComment { comment, .. }`
/// (`compiler/rustc_hir/src/attrs/data_structures.rs#L1012-L1019`), and
/// `Attribute::doc_str` returns `comment` for exactly those
/// (`hir.rs#L1508-L1513`).
fn collect_directives(
    tcx: TyCtxt<'_>,
    errs: &mut Errors,
) -> BTreeMap<ir::DefIdx, Vec<Directive>> {
    let mut out: BTreeMap<ir::DefIdx, Vec<Directive>> = BTreeMap::new();
    let mut visit = |hir_id: HirId,
                     attrs: &[hir::Attribute],
                     errs: &mut Errors| {
        for attr in attrs {
            let Some(doc) = attr.doc_str() else { continue };
            let parsed = match spec::parse_doc(doc.as_str()) {
                Ok(p) => p,
                Err(e) => {
                    errs.push(tcx, hir_id.owner.def_id, e);
                    continue;
                }
            };
            if parsed.is_empty() {
                continue;
            }
            let owner = hir_id.owner.def_id;
            let placed_on_item = hir_id.local_id.as_u32() == 0
                && owner != CRATE_DEF_ID
                && matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::Struct);
            if placed_on_item {
                out.entry(owner.local_def_index.as_u32())
                    .or_default()
                    .extend(parsed);
            } else {
                errs.push(
                    tcx,
                    owner,
                    "Anneal directive in an unsupported position",
                );
            }
        }
    };
    for owner in tcx.hir_crate_items(()).owners() {
        for (local_id, attrs) in tcx.hir_attr_map(owner).map.iter() {
            visit(HirId { owner, local_id: *local_id }, attrs, errs);
        }
    }
    visit(hir::CRATE_HIR_ID, tcx.hir_krate_attrs(), errs);
    out
}

/// Checks that `def`'s generics are type parameters with only `Sized` and
/// `Copy` bounds, every explicit type parameter `Sized`.
///
/// This keeps `ParamTy::index` equal to the position among type parameters
/// (see `extract::ty`), keeps every parameter sized (the model gives `&T` a
/// pointer-sized layout, which is wrong for unsized `T`), and excludes trait
/// bounds through which generic code could select impls the model cannot
/// resolve. Traits additionally have an implicit `Self` parameter at index `0`
/// whose only allowed predicate is the trait's own self-predicate. Functions
/// and traits must not have parent generics, and `impl Trait` parameters
/// (synthetic type parameters) are rejected.
fn check_generics(tcx: TyCtxt<'_>, def: LocalDefId, errs: &mut Errors) {
    let is_trait = matches!(tcx.def_kind(def), DefKind::Trait);
    let generics = tcx.generics_of(def);
    if generics.parent.is_some()
        && !matches!(tcx.def_kind(def), DefKind::Impl { .. })
    {
        errs.push(tcx, def, "items with parent generics are not supported");
    }
    let mut params = BTreeSet::new();
    for (pos, p) in generics.own_params.iter().enumerate() {
        match p.kind {
            GenericParamDefKind::Type {
                synthetic: false,
                has_default: false,
            } if p.index as usize == pos => {
                if !(is_trait && p.index == 0) {
                    params.insert(p.index);
                }
            }
            _ => errs.push(
                tcx,
                def,
                format!("unsupported generic parameter `{}`", p.name),
            ),
        }
    }
    let mut sized = BTreeSet::new();
    for (clause, _) in tcx.predicates_of(def).predicates {
        let ok = clause.as_trait_clause().and_then(|tp| {
            let tp = tp.skip_binder();
            let ty::Param(p) = *tp.self_ty().kind() else { return None };
            let tr = tp.def_id();
            if is_trait && p.index == 0 {
                (tr == def.to_def_id()
                    || tcx.is_lang_item(tr, LangItem::MetaSized))
                .then_some(())
            } else if tcx.is_lang_item(tr, LangItem::Sized) {
                sized.insert(p.index);
                Some(())
            } else if tcx.is_lang_item(tr, LangItem::Copy) {
                Some(())
            } else {
                None
            }
        });
        if ok.is_none() {
            errs.push(tcx, def, format!("unsupported where-clause `{clause}`"));
        }
    }
    if sized != params {
        errs.push(tcx, def, "`?Sized` type parameters are not supported");
    }
}

/// Classifies a free function.
///
/// - Visibility: a function that is `pub` and exported from the crate
///   (`effective_visibilities`) is a root of `Trusted.Crate.functions`, whose
///   entry precondition assumes only that callers respect the type system
///   and the safety contract. Every other function is private: it has no
///   precondition of its own and no specifications, and the model verifies
///   it only inside the public functions that call it (`check_references`
///   rejects a private function that no captured body calls).
/// - Safety: `fn_sig(..).safety()` decides whether a public function has a
///   safety precondition (`CapturedFn.safetyPre`).
/// - ABI must be `Rust`, and the function must not be variadic, `const`,
///   `async`, or use `#[target_feature]` (which makes calls unsafe from
///   contexts lacking the feature).
fn function(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    directives: Option<Vec<Directive>>,
    errs: &mut Errors,
) -> Option<ir::Function> {
    let before = errs.0.len();
    let public = tcx.visibility(def).is_public()
        && tcx.effective_visibilities(()).is_exported(def);
    let sig = tcx.fn_sig(def).skip_binder().skip_binder();
    if sig.abi() != ExternAbi::Rust || sig.c_variadic() {
        errs.push(
            tcx,
            def,
            "only non-variadic `extern \"Rust\"` functions are supported",
        );
    }
    if tcx.constness(def) == hir::Constness::Const {
        errs.push(tcx, def, "`const fn` is not supported");
    }
    if tcx.asyncness(def).is_async() {
        errs.push(tcx, def, "`async fn` is not supported");
    }
    let cg = tcx.codegen_fn_attrs(def);
    if !cg.target_features.is_empty() {
        errs.push(tcx, def, "`#[target_feature]` functions are not supported");
    }
    // `#[no_mangle]`, `#[export_name]`, and `#[link_section]` place the
    // function under a chosen linker symbol or section, where it can replace
    // or be replaced by code outside the crate; `#[naked]` bodies are
    // assembly. None of that is described by the function's MIR.
    if cg.symbol_name.is_some()
        || cg.link_section.is_some()
        || cg.flags.intersects(
            CodegenFnAttrFlags::NO_MANGLE | CodegenFnAttrFlags::NAKED,
        )
    {
        errs.push(tcx, def, "functions with linker-symbol or naked attributes are not supported");
    }
    check_generics(tcx, def, errs);
    let name = tcx.item_name(def.to_def_id()).to_string();

    let unsafe_fn = sig.safety() == hir::Safety::Unsafe;
    let arg_names = tcx.fn_arg_idents(def);
    let arg_local = |ident: &str| -> Option<u32> {
        arg_names
            .iter()
            .position(|a| a.is_some_and(|a| a.name.as_str() == ident))
            .map(|i| i as u32 + 1)
    };
    let mut specs = Vec::new();
    let mut requires = None;
    for d in directives.unwrap_or_default() {
        match d {
            Directive::EnsuresRetEq(x) => match arg_local(&x) {
                Some(l) => specs.push(ir::Spec::EnsuresEqArg(l)),
                None => errs.push(
                    tcx,
                    def,
                    format!("`ensures`: `{x}` is not a parameter"),
                ),
            },
            Directive::WellFormed => {}
            Directive::Requires { ident, ne } => {
                let local = arg_local(&ident);
                let is_usize = local.is_some_and(|l| {
                    extract::ty(sig.inputs()[l as usize - 1]) == ir::Ty::Usize
                });
                if !unsafe_fn {
                    errs.push(
                        tcx,
                        def,
                        "`requires` is only accepted on `unsafe fn`",
                    );
                } else if requires.is_some() {
                    errs.push(
                        tcx,
                        def,
                        "at most one `requires` directive is supported",
                    );
                } else if !is_usize {
                    errs.push(
                        tcx,
                        def,
                        format!(
                            "`requires`: `{ident}` is not a `usize` parameter"
                        ),
                    );
                } else {
                    requires = Some(ir::RequiresSpec {
                        arg_local: local.unwrap(),
                        ne,
                    });
                }
            }
            Directive::Invariant { .. } => {
                errs.push(tcx, def, "`invariant` is only accepted on structs")
            }
        }
    }
    let kind = if !public {
        if !specs.is_empty() || requires.is_some() {
            errs.push(
                tcx,
                def,
                "Anneal directives are only accepted on public functions",
            );
        }
        ir::FnKind::Private
    } else {
        ir::FnKind::Exported { requires, specs }
    };
    (errs.0.len() == before).then(|| ir::Function {
        def: def.local_def_index.as_u32(),
        name,
        kind,
    })
}

/// Checks that `def`'s MIR body and its declared signature agree.
///
/// MIR locals `_1..=_n` hold the arguments and `_0` the return value; their
/// types come from the same signature, so a mismatch would mean the body is
/// not the function's. The check is cheap insurance that `argTys`/`retTy`
/// in `Mir.lean` describe the declared interface that callers see.
fn check_signature(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    body: &ir::Body,
    errs: &mut Errors,
) {
    let sig = tcx.fn_sig(def).skip_binder().skip_binder();
    let inputs: Vec<_> =
        sig.inputs().iter().map(|t| extract::ty(*t)).collect();
    let output = extract::ty(sig.output());
    if inputs != body.arg_tys || output != body.ret_ty {
        errs.push(
            tcx,
            def,
            "MIR argument or return types differ from the signature",
        );
    }
}

/// Classifies a struct.
///
/// `Trusted.AdtDecl` (`Trusted/MirAst.lean`) describes a struct with at most
/// one field and no type arguments; this capture accepts exactly one field
/// because multi-field layouts are not modeled in `Trusted/MirSemantics.lean`
/// and fieldless structs have no aggregate form in `Rvalue.aggregate`. Field
/// visibility and safety come from `FieldDef::vis` and `FieldDef::safety`
/// (`compiler/rustc_middle/src/ty/mod.rs#L1407-L1413`). `#[non_exhaustive]`
/// is not recorded: treating such a struct as constructible by safe code
/// only strengthens what `AdmissibleAdtInv` demands of its invariant.
///
/// The model assumes that a single-field struct has its field's size. Rust
/// does not guarantee that for the default representation (only
/// `#[repr(transparent)]` does), so the capture asks `rustc` for the struct's
/// actual layout (`layout_of`) and rejects the struct if the sizes differ. It
/// also rejects `#[repr(align(N))]` and `#[repr(packed)]` outright.
fn adt(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    directives: Option<Vec<Directive>>,
    errs: &mut Errors,
) -> Option<ir::Adt> {
    let before = errs.0.len();
    let adt = tcx.adt_def(def);
    if !tcx.generics_of(def).own_params.is_empty() {
        errs.push(tcx, def, "generic structs are not supported");
        return None;
    }
    if adt.has_dtor(tcx) {
        errs.push(tcx, def, "structs with `Drop` impls are not supported");
    }
    let variant = adt.non_enum_variant();
    let [field] = variant.fields.raw.as_slice() else {
        errs.push(
            tcx,
            def,
            format!(
                "structs must have exactly one field (found {})",
                variant.fields.len()
            ),
        );
        return None;
    };
    let field_ty = extract::ty(tcx.type_of(field.did).skip_binder());
    let access = if field.vis.is_public() && field.safety == hir::Safety::Safe {
        ir::FieldAccess::PubSafe
    } else {
        ir::FieldAccess::Priv
    };

    // `#[repr(align(N))]` and `#[repr(packed)]` change size or alignment
    // relative to the field, whereas `Trusted.evalTyByteSize` in
    // `Trusted/MirSemantics.lean` assumes that a single-field struct has its
    // field's size and alignment. The layout check below catches a size
    // change; this check also excludes an alignment change that keeps the
    // size.
    let repr = adt.repr();
    if repr.align.is_some() || repr.pack.is_some() {
        errs.push(
            tcx,
            def,
            "`#[repr(align)]` and `#[repr(packed)]` are not supported",
        );
    }

    let self_ty = tcx.type_of(def).skip_binder();
    let rustc_size = tcx
        .layout_of(TypingEnv::fully_monomorphized().as_query_input(self_ty))
        .map(|l| l.size.bytes());
    let field_size = tcx
        .layout_of(
            TypingEnv::fully_monomorphized()
                .as_query_input(tcx.type_of(field.did).skip_binder()),
        )
        .map(|l| l.size.bytes());
    match (rustc_size, field_size) {
        (Ok(a), Ok(b)) if a == b => {}
        _ => errs.push(
            tcx,
            def,
            "the struct's size differs from its field's size",
        ),
    }

    let mut invariant = None;
    for d in directives.unwrap_or_default() {
        match d {
            Directive::Invariant { ident, ne } => {
                if invariant.is_some() {
                    errs.push(
                        tcx,
                        def,
                        "at most one `invariant` directive is supported",
                    );
                } else if field.name.as_str() != ident
                    || field_ty != ir::Ty::Usize
                {
                    errs.push(tcx, def, format!("`invariant`: `{ident}` is not the struct's `usize` field"));
                } else {
                    invariant = Some(ir::InvariantSpec { ne });
                }
            }
            _ => errs.push(tcx, def, "only `invariant` is accepted on structs"),
        }
    }
    (errs.0.len() == before).then(|| ir::Adt {
        def: def.local_def_index.as_u32(),
        field_ty,
        access,
        invariant,
    })
}

/// A trait may only be safe, use lifetime-free and const-free type parameters,
/// and declare associated constants without default bodies (its items are
/// checked with the other trait items). Traits exist in the fragment only to
/// host the associated-constant PME pattern.
fn trait_def(tcx: TyCtxt<'_>, def: LocalDefId, errs: &mut Errors) {
    let t = tcx.trait_def(def);
    if t.safety == hir::Safety::Unsafe {
        errs.push(tcx, def, "`unsafe trait` is not supported");
    }
    check_generics(tcx, def, errs);
}

/// A trait impl must be safe, positive, of a trait of this crate, and contain
/// only associated constants. Impls of foreign traits are rejected: `Drop`,
/// `Clone`, `Copy`, operator traits, and `unsafe impl Send/Sync` would all
/// change behavior the model does not describe.
fn trait_impl(tcx: TyCtxt<'_>, def: LocalDefId, errs: &mut Errors) {
    let h = tcx.impl_trait_header(def);
    if !h.trait_ref.skip_binder().def_id.is_local() {
        errs.push(
            tcx,
            def,
            "impls of traits from other crates are not supported",
        );
    }
    if h.safety == hir::Safety::Unsafe {
        errs.push(tcx, def, "`unsafe impl` is not supported");
    }
    if h.polarity != ty::ImplPolarity::Positive {
        errs.push(tcx, def, "negative impls are not supported");
    }
    check_generics(tcx, def, errs);
}

/// Checks that every `call1` callee is a captured function, every required
/// constant is a captured constant body, every captured constant is required
/// by some body, and every private function is called by some body.
///
/// The last two rules reject constants and private functions that no
/// captured body uses. Neither has a place of its own in `Trusted.Crate`,
/// which mentions constants only through `requiredConsts` and private
/// functions only as `call1` callees; rejecting them, rather than dropping
/// them, keeps the rule that every body is either captured or rejected.
fn check_references(
    tcx: TyCtxt<'_>,
    bodies: &BTreeMap<ir::DefIdx, ir::Body>,
    functions: &[ir::Function],
    constants: &[ir::Constant],
    errs: &mut Errors,
) {
    let fns: BTreeSet<_> = functions.iter().map(|f| f.def).collect();
    let mut called = BTreeSet::new();
    let consts: BTreeSet<_> = constants.iter().map(|c| c.def).collect();
    let mut required = BTreeSet::new();
    let name = |d: ir::DefIdx| {
        tcx.def_path_str(LocalDefId { local_def_index: d.into() })
    };
    for (&d, b) in bodies {
        for (c, _) in &b.required_consts {
            required.insert(*c);
            if !consts.contains(c) {
                errs.0.push(format!(
                    "`{}`: requires constant `{}`, which was not captured",
                    name(d),
                    name(*c)
                ));
            }
        }
        for callee in b.callees() {
            called.insert(callee);
            if !fns.contains(&callee) {
                errs.0.push(format!(
                    "`{}`: calls `{}`, which was not captured",
                    name(d),
                    name(callee)
                ));
            }
        }
    }
    for f in functions {
        if f.kind == ir::FnKind::Private && !called.contains(&f.def) {
            errs.0.push(format!(
                "`{}`: private function is not called by any captured body",
                name(f.def)
            ));
        }
    }
    for c in constants {
        if !required.contains(&c.def) {
            errs.0.push(format!(
                "`{}`: constant is not required by any captured body",
                c.path
            ));
        }
    }
}

/// Orders bodies so each follows every body it references (callees and
/// required constants), as Lean requires of definitions. A cycle (recursion)
/// is rejected: `Trusted.MirBody` values are finite trees, and Lean
/// definitions cannot refer to themselves without a fixpoint construction.
fn dependency_order(
    bodies: &BTreeMap<ir::DefIdx, ir::Body>,
) -> Result<Vec<ir::DefIdx>, String> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum VisitState {
        Visiting,
        Done,
    }
    fn visit(
        d: ir::DefIdx,
        bodies: &BTreeMap<ir::DefIdx, ir::Body>,
        state: &mut BTreeMap<ir::DefIdx, VisitState>,
        out: &mut Vec<ir::DefIdx>,
    ) -> Result<(), String> {
        match state.get(&d) {
            Some(VisitState::Done) => return Ok(()),
            Some(VisitState::Visiting) => {
                return Err(
                    "recursive calls or constants are not supported".into()
                );
            }
            None => {}
        }
        state.insert(d, VisitState::Visiting);
        if let Some(b) = bodies.get(&d) {
            for dep in b.deps() {
                visit(dep, bodies, state, out)?;
            }
        }
        state.insert(d, VisitState::Done);
        if bodies.contains_key(&d) {
            out.push(d);
        }
        Ok(())
    }
    let mut state = BTreeMap::new();
    let mut out = Vec::new();
    for &d in bodies.keys() {
        visit(d, bodies, &mut state, &mut out)?;
    }
    Ok(out)
}
