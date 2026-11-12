// Copyright 2026 The Fuchsia Authors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0>, the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, or the BSD-2-Clause
// license <LICENSE-BSD or https://opensource.org/license/bsd-2-clause>, at your
// option. This file may not be copied, modified, or distributed except
// according to those terms.

//! Structure-aware `syn` AST mutators for Miri differential testing.
//!
//! Seeds are closed, zero-argument functions from `tests/miri-diff/corpus`
//! that use primitive operators, casts, projections, raw pointers, and core
//! intrinsics rather than standard-library method calls. The mutators
//! (`ArithmeticCastMutator`, `PlaceProjectionWrapper`, `RawPtrOffsetMutator`,
//! `TreeBorrowsRetagInterleaver`, and `BitValidityTransmuteMutator`) produce
//! closed zero-argument mutants suitable for direct execution by both Miri and
//! Anneal's helper-linked MIR-in-Lean oracle (`crate::miri_eval`).

use quote::{ToTokens, format_ident};
use syn::visit_mut::VisitMut;
use syn::{
    BinOp, Block, Expr, ExprCall, File, FnArg, GenericArgument, Item, ItemFn, Lit, Local, Pat,
    PathArguments, ReturnType, Stmt, Type,
};

/// Raw source of `tests/miri-diff/corpus/src/lib.rs` embedded at compile time.
pub const RAW_MIRI_DIFF_CORPUS_RS: &str =
    include_str!("../../../tests/miri-diff/corpus/src/lib.rs");

/// Crate-level header attributes required to compile closed Miri differential
/// candidates standalone (`#![no_std]` and `#![feature(core_intrinsics)]`).
pub const MIRI_CORPUS_CRATE_HEADER: &str = "\
#![no_std]
#![allow(
    dead_code,
    arithmetic_overflow,
    unconditional_panic,
    invalid_value,
    invalid_reference_casting,
    unnecessary_transmutes,
    dangling_pointers_from_locals,
    deref_nullptr,
    internal_features,
    non_snake_case,
    unused_imports,
    unused_parens,
    unused_variables,
    unused_assignments,
    unused_mut,
    unreachable_code
)]
#![feature(core_intrinsics)]
";

/// Shared module-level imports and helper types from `tests/miri-diff/corpus`
/// that candidates may reference without crate-level `#![...]` attributes.
pub const MIRI_CORPUS_MODULE_PREAMBLE: &str = "\
use core::cell::UnsafeCell;
use core::intrinsics::{
    assume, copy_nonoverlapping, exact_div, offset, unchecked_add, unchecked_div, unchecked_mul,
    unchecked_rem, unchecked_shl, unchecked_shr, unchecked_sub, unreachable,
};
use core::mem::transmute;

#[repr(C)]
union Uninit<T: Copy> {
    uninit: (),
    value: T,
}

#[repr(C)]
pub struct PairU32 {
    pub a: u32,
    pub b: u32,
}

#[repr(C)]
pub struct PaddedU8U32 {
    pub tag: u8,
    pub word: u32,
}

#[repr(u8)]
pub enum ColorTag {
    Red = 0,
    Green = 1,
    Blue = 2,
}

#[inline(never)]
pub fn helper_add_ten() -> u32 {
    10
}

use core::num::NonZeroU32;

#[repr(transparent)]
pub struct MetersU32(pub u32);

#[repr(transparent)]
pub struct NonZeroMeters(pub NonZeroU32);

#[repr(C)]
pub enum SingleC {
    Only(u32),
}

#[repr(C)]
pub union OverlayU32 {
    pub word: u32,
    pub bytes: [u8; 4],
}
";

/// A single closed, zero-argument seed function extracted from
/// `tests/miri-diff/corpus/src/lib.rs`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MiriCorpusSeed {
    /// Original function identifier in `tests/miri-diff/corpus/src/lib.rs`.
    pub name: String,
    /// Pretty-printed source of the `pub fn` item alone.
    pub fn_source: String,
}

/// Metadata captured for an initialized local variable discovered inside a
/// function body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrackedLocal {
    pub name: String,
    pub ty: String,
    pub is_mut: bool,
}

/// Output candidate produced by [`generate_miri_batch`],
/// [`generate_miri_corpus_batch`], or [`generate_miri_identity_batch`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneratedMiriCandidate {
    /// Zero-based index within the generated batch.
    pub id: usize,
    /// Index of the seed program from `seeds` that this candidate mutated.
    pub seed_index: usize,
    /// Name of the seed function from which this candidate was derived.
    pub seed_name: String,
    /// Public zero-argument function name of this candidate.
    pub fn_name: String,
    /// Per-candidate deterministic PRNG seed derived from the batch `seed_u64`.
    pub seed_u64: u64,
    /// Ordered list of Miri AST mutator names applied to produce this candidate.
    pub applied_mutators: Vec<String>,
    /// Snapshot of initialized `(local_name, inferred_or_declared_type)` bindings.
    pub tracked_locals: Vec<(String, String)>,
    /// Source of the mutated `pub fn` item alone (without preamble), used when
    /// assembling a multi-candidate crate for the oracle pipeline.
    pub fn_source: String,
    /// Complete standalone Rust source (`MIRI_CORPUS_CRATE_HEADER` +
    /// `MIRI_CORPUS_MODULE_PREAMBLE` + `fn_source`), compilable on its own and
    /// usable directly as `repro.rs`.
    pub source: String,
}

impl GeneratedMiriCandidate {
    /// Return module-scoped source (`MIRI_CORPUS_MODULE_PREAMBLE` + `fn_source`)
    /// without crate-level `#![...]` attributes so multiple candidates can be
    /// wrapped in `pub mod bX_cY { ... }` within one combined compilation check.
    pub fn module_body_source(&self) -> String {
        format!("{MIRI_CORPUS_MODULE_PREAMBLE}\n{}\n", self.fn_source)
    }
}

/// Target semantic regime for a mutation pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MutationMode {
    /// Perturb the seed AST in place and fold a live probe into the return path.
    Pass,
    /// Perturb or append a checked operation that panics after the seed body runs.
    Panic,
    /// Perturb or append an unsafe operation that triggers UB after the seed body runs.
    Ub,
    /// Perturb existing AST literals, operators, casts, indices, offsets,
    /// aliasing statement order, or transmutes in place.
    PerturbAst,
}

/// Deterministic SplitMix64 PRNG used to drive reproducible AST mutations.
#[derive(Debug, Clone)]
pub struct DetRng {
    state: u64,
}

impl DetRng {
    pub fn new(seed: u64) -> Self {
        Self {
            state: seed ^ 0x9E37_79B9_7F4A_7C15,
        }
    }

    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn gen_range(&mut self, upper: usize) -> usize {
        if upper <= 1 {
            0
        } else {
            (self.next_u64() as usize) % upper
        }
    }

    pub fn coin(&mut self, num: u64, den: u64) -> bool {
        if den == 0 {
            return false;
        }
        (self.next_u64() % den) < num
    }
}

/// Extract the 89 closed zero-argument test functions from
/// `tests/miri-diff/corpus/src/lib.rs` (excluding `helper_add_ten`).
pub fn load_miri_diff_corpus_seeds() -> Vec<MiriCorpusSeed> {
    extract_closed_corpus_seeds(RAW_MIRI_DIFF_CORPUS_RS)
}

/// Parse `corpus_source` and extract all zero-argument `pub fn` items other
/// than `helper_add_ten`.
pub fn extract_closed_corpus_seeds(corpus_source: &str) -> Vec<MiriCorpusSeed> {
    let parsed = syn::parse_file(corpus_source)
        .expect("tests/miri-diff/corpus/src/lib.rs must parse as valid Rust");
    let mut seeds = Vec::new();
    for item in parsed.items {
        if let Item::Fn(func) = item {
            let name = func.sig.ident.to_string();
            if name == "helper_add_ten" || !func.sig.inputs.is_empty() {
                continue;
            }
            let single_file = File {
                shebang: None,
                attrs: Vec::new(),
                items: vec![Item::Fn(func)],
            };
            let fn_source = prettyplease::unparse(&single_file);
            seeds.push(MiriCorpusSeed { name, fn_source });
        }
    }
    seeds
}

/// Build the complete standalone `#![no_std]` crate source for a single
/// candidate function body.
pub fn build_standalone_candidate_source(fn_source: &str) -> String {
    format!(
        "{MIRI_CORPUS_CRATE_HEADER}\n{MIRI_CORPUS_MODULE_PREAMBLE}\n{}\n",
        fn_source.trim()
    )
}

/// Extracts initialized local bindings and their annotated/inferred types that
/// remain in scope at the end of a function body.
///
/// Later `let` bindings of the same identifier replace earlier bindings so a
/// shadowed integer local (for example `let x: u32 = 1; let x: PairU32 = ...;`)
/// is never misclassified as an integer at the end of the function.
pub fn collect_initialized_locals(func: &ItemFn) -> Vec<TrackedLocal> {
    let mut locals: Vec<TrackedLocal> = Vec::new();
    let upsert_or_shadow =
        |locals: &mut Vec<TrackedLocal>, entry: Option<TrackedLocal>, shadowed: Option<&str>| {
            if let Some(name) = shadowed {
                locals.retain(|l| l.name != name);
            }
            if let Some(loc) = entry {
                locals.retain(|l| l.name != loc.name);
                locals.push(loc);
            }
        };

    for arg in &func.sig.inputs {
        if let FnArg::Typed(pat_ty) = arg {
            let (name_opt, is_mut) = extract_pat_ident(&pat_ty.pat);
            if let Some(name) = name_opt {
                upsert_or_shadow(
                    &mut locals,
                    Some(TrackedLocal {
                        name,
                        ty: pat_ty.ty.to_token_stream().to_string().replace(' ', ""),
                        is_mut,
                    }),
                    None,
                );
            } else {
                let mut bound = Vec::new();
                collect_pat_bound_idents(&pat_ty.pat, &mut bound);
                for name in bound {
                    upsert_or_shadow(&mut locals, None, Some(&name));
                }
            }
        }
    }

    for stmt in &func.block.stmts {
        if let Stmt::Local(local) = stmt {
            let pat = unwrap_pat_type_and_parens(&local.pat);
            let (name_opt, is_mut) = extract_pat_ident(pat);
            let Some(name) = name_opt else {
                // Evict any earlier bindings shadowed by destructuring patterns
                // (`let (x, _): (PairU32, u32) = ...;`, `let PairU32 { a: x, .. } = ...;`).
                let mut bound = Vec::new();
                collect_pat_bound_idents(&local.pat, &mut bound);
                for shadowed_name in bound {
                    upsert_or_shadow(&mut locals, None, Some(&shadowed_name));
                }
                continue;
            };
            let Some(local_init) = &local.init else {
                upsert_or_shadow(&mut locals, None, Some(&name));
                continue;
            };
            if local_init.diverge.is_some() {
                upsert_or_shadow(&mut locals, None, Some(&name));
                continue;
            }
            let ty = if let Some(pat_ty) = extract_outer_pat_type(&local.pat) {
                pat_ty.to_token_stream().to_string().replace(' ', "")
            } else {
                infer_expr_type_name(&local_init.expr)
            };
            upsert_or_shadow(&mut locals, Some(TrackedLocal { name, ty, is_mut }), None);
        }
    }

    locals
}

fn unwrap_pat_parens(mut pat: &Pat) -> &Pat {
    while let Pat::Paren(pp) = pat {
        pat = &pp.pat;
    }
    pat
}

fn extract_outer_pat_type(mut pat: &Pat) -> Option<&Type> {
    loop {
        match pat {
            Pat::Type(pt) => return Some(&pt.ty),
            Pat::Paren(pp) => pat = &pp.pat,
            _ => return None,
        }
    }
}

fn unwrap_pat_type_and_parens(mut pat: &Pat) -> &Pat {
    loop {
        match pat {
            Pat::Type(pt) => pat = &pt.pat,
            Pat::Paren(pp) => pat = &pp.pat,
            _ => return pat,
        }
    }
}

fn collect_pat_bound_idents(pat: &Pat, out: &mut Vec<String>) {
    struct PatIdentCollector<'a>(&'a mut Vec<String>);
    impl<'ast> syn::visit::Visit<'ast> for PatIdentCollector<'_> {
        fn visit_pat_ident(&mut self, node: &'ast syn::PatIdent) {
            self.0.push(node.ident.to_string());
            syn::visit::visit_pat_ident(self, node);
        }
    }
    syn::visit::Visit::visit_pat(&mut PatIdentCollector(out), pat);
}

fn extract_pat_ident(pat: &Pat) -> (Option<String>, bool) {
    match unwrap_pat_type_and_parens(pat) {
        Pat::Ident(pi) if pi.subpat.is_none() => {
            (Some(pi.ident.to_string()), pi.mutability.is_some())
        }
        _ => (None, false),
    }
}

fn infer_expr_type_name(expr: &Expr) -> String {
    match expr {
        Expr::Lit(el) => match &el.lit {
            Lit::Int(li) if !li.suffix().is_empty() => li.suffix().to_string(),
            Lit::Int(_) => "u32".to_string(),
            Lit::Bool(_) => "bool".to_string(),
            Lit::Char(_) => "char".to_string(),
            _ => "unknown".to_string(),
        },
        Expr::Cast(cast) => cast.ty.to_token_stream().to_string().replace(' ', ""),
        Expr::Struct(st) => st
            .path
            .segments
            .last()
            .map(|s| s.ident.to_string())
            .unwrap_or_else(|| "unknown".to_string()),
        Expr::Call(call) => match &*call.func {
            Expr::Path(ep) if ep.qself.is_none() => match ep.path.segments.len() {
                1 => {
                    let name = ep.path.segments[0].ident.to_string();
                    if matches!(name.as_str(), "MetersU32" | "NonZeroMeters") {
                        name
                    } else {
                        "unknown".to_string()
                    }
                }
                2 => {
                    let ty_name = ep.path.segments[0].ident.to_string();
                    if ty_name == "SingleC" {
                        ty_name
                    } else {
                        "unknown".to_string()
                    }
                }
                _ => "unknown".to_string(),
            },
            _ => "unknown".to_string(),
        },
        Expr::Path(ep) if ep.qself.is_none() && ep.path.segments.len() == 2 => {
            let ty_name = ep.path.segments[0].ident.to_string();
            if ty_name == "ColorTag" {
                ty_name
            } else {
                "unknown".to_string()
            }
        }
        _ => "unknown".to_string(),
    }
}

fn is_integer_type_name(ty: &str) -> bool {
    matches!(
        ty,
        "u8" | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
    )
}

struct LifetimeEraser;

impl VisitMut for LifetimeEraser {
    fn visit_type_reference_mut(&mut self, node: &mut syn::TypeReference) {
        node.lifetime = None;
        syn::visit_mut::visit_type_reference_mut(self, node);
    }

    fn visit_angle_bracketed_generic_arguments_mut(
        &mut self,
        node: &mut syn::AngleBracketedGenericArguments,
    ) {
        for arg in &mut node.args {
            if let GenericArgument::Lifetime(lt) = arg {
                *lt = syn::Lifetime::new("'_", lt.span());
            }
        }
        syn::visit_mut::visit_angle_bracketed_generic_arguments_mut(self, node);
    }
}

fn strip_type_lifetimes(ty: &Type) -> Type {
    let mut out = ty.clone();
    LifetimeEraser.visit_type_mut(&mut out);
    out
}

/// Convert any function parameters into leading initialized local bindings and
/// rewrite method calls (`.wrapping_add`, `.wrapping_sub`, `.wrapping_mul`,
/// `.rotate_left`) into primitive operators so every candidate is closed,
/// zero-argument, and free of unmodeled method calls.
fn close_and_normalize_function(func: &mut ItemFn, rng: &mut DetRng) {
    if !func.sig.inputs.is_empty() {
        let mut init_stmts = Vec::new();
        let mut backing_idx = 0usize;
        let inputs: Vec<FnArg> = func.sig.inputs.iter().cloned().collect();
        func.sig.inputs.clear();
        func.sig.generics.params = func
            .sig
            .generics
            .params
            .iter()
            .filter(|p| !matches!(p, syn::GenericParam::Lifetime(_)))
            .cloned()
            .collect();
        if func.sig.generics.params.is_empty() {
            func.sig.generics.lt_token = None;
            func.sig.generics.gt_token = None;
        }
        if let ReturnType::Type(_, ret_ty) = &mut func.sig.output {
            **ret_ty = strip_type_lifetimes(ret_ty);
        }
        for arg in inputs {
            if let FnArg::Typed(pat_ty) = arg {
                let clean_ty = strip_type_lifetimes(&pat_ty.ty);
                let init_val =
                    seeded_type_expr(&clean_ty, &mut init_stmts, &mut backing_idx, rng);
                let inner_pat = unwrap_pat_parens(&pat_ty.pat);
                let stmt: Stmt = match inner_pat {
                    Pat::Ident(pi) if pi.subpat.is_none() => {
                        let ident = &pi.ident;
                        syn::parse_quote! {
                            let mut #ident: #clean_ty = #init_val;
                        }
                    }
                    _ => {
                        let pat = &pat_ty.pat;
                        syn::parse_quote! {
                            let #pat: #clean_ty = #init_val;
                        }
                    }
                };
                init_stmts.push(stmt);
            }
        }
        func.block.stmts.splice(0..0, init_stmts);
    }

    let mut normalizer = MethodCallNormalizer;
    normalizer.visit_item_fn_mut(func);
}

fn seeded_type_expr(
    ty: &Type,
    backing_stmts: &mut Vec<Stmt>,
    backing_idx: &mut usize,
    rng: &mut DetRng,
) -> Expr {
    match ty {
        Type::Paren(p) => seeded_type_expr(&p.elem, backing_stmts, backing_idx, rng),
        Type::Group(g) => seeded_type_expr(&g.elem, backing_stmts, backing_idx, rng),
        Type::Tuple(tup) => {
            if tup.elems.is_empty() {
                syn::parse_quote!(())
            } else {
                let elems: Vec<Expr> = tup
                    .elems
                    .iter()
                    .map(|e| seeded_type_expr(e, backing_stmts, backing_idx, rng))
                    .collect();
                syn::parse_quote!((#(#elems,)*))
            }
        }
        Type::Array(arr) => {
            let len = match &arr.len {
                Expr::Lit(el) => match &el.lit {
                    Lit::Int(li) => li.base10_parse::<usize>().ok(),
                    _ => None,
                },
                _ => None,
            };
            if let Some(n) = len
                && n <= 32
            {
                let elems: Vec<Expr> = (0..n)
                    .map(|_| seeded_type_expr(&arr.elem, backing_stmts, backing_idx, rng))
                    .collect();
                syn::parse_quote!([#(#elems),*])
            } else {
                seeded_scalar_expr(&ty.to_token_stream().to_string().replace(' ', ""), rng)
            }
        }
        Type::Reference(r) => {
            let clean_elem = strip_type_lifetimes(&r.elem);
            let idx = *backing_idx;
            *backing_idx += 1;
            let backing_id = format_ident!("__arg_ref_{idx}");
            let val = seeded_type_expr(&clean_elem, backing_stmts, backing_idx, rng);
            backing_stmts.push(syn::parse_quote! {
                let mut #backing_id: #clean_elem = #val;
            });
            if r.mutability.is_some() {
                syn::parse_quote!(&mut #backing_id)
            } else {
                syn::parse_quote!(&#backing_id)
            }
        }
        Type::Ptr(p) => {
            let clean_elem = strip_type_lifetimes(&p.elem);
            let idx = *backing_idx;
            *backing_idx += 1;
            let backing_id = format_ident!("__arg_ptr_{idx}");
            let val = seeded_type_expr(&clean_elem, backing_stmts, backing_idx, rng);
            backing_stmts.push(syn::parse_quote! {
                let mut #backing_id: #clean_elem = #val;
            });
            if p.mutability.is_some() {
                syn::parse_quote!(&raw mut #backing_id)
            } else {
                syn::parse_quote!(&raw const #backing_id)
            }
        }
        Type::Path(tp) if tp.qself.is_none() => {
            if let Some(seg) = tp.path.segments.last() {
                let seg_name = seg.ident.to_string();
                if let PathArguments::AngleBracketed(args) = &seg.arguments
                    && let Some(GenericArgument::Type(inner_ty)) = args.args.first()
                {
                    let clean_inner = strip_type_lifetimes(inner_ty);
                    match seg_name.as_str() {
                        "Option" => {
                            return if rng.coin(1, 3) {
                                syn::parse_quote!(None)
                            } else {
                                let inner = seeded_type_expr(
                                    &clean_inner,
                                    backing_stmts,
                                    backing_idx,
                                    rng,
                                );
                                syn::parse_quote!(Some(#inner))
                            };
                        }
                        "Uninit" => {
                            let inner =
                                seeded_type_expr(&clean_inner, backing_stmts, backing_idx, rng);
                            return syn::parse_quote!(Uninit { value: #inner });
                        }
                        "UnsafeCell" => {
                            let inner =
                                seeded_type_expr(&clean_inner, backing_stmts, backing_idx, rng);
                            return syn::parse_quote!(unsafe {
                                transmute::<#clean_inner, UnsafeCell<#clean_inner>>(#inner)
                            });
                        }
                        _ => {}
                    }
                }
                if matches!(seg.arguments, PathArguments::None) {
                    return seeded_scalar_expr(&seg_name, rng);
                }
            }
            seeded_scalar_expr(&ty.to_token_stream().to_string().replace(' ', ""), rng)
        }
        _ => seeded_scalar_expr(&ty.to_token_stream().to_string().replace(' ', ""), rng),
    }
}

fn seeded_scalar_expr(ty_str: &str, rng: &mut DetRng) -> Expr {
    let pool_u32: [u32; 8] = [1, 2, 7, 15, 31, 42, 127, 255];
    let pick = pool_u32[rng.gen_range(pool_u32.len())];
    match ty_str {
        "u8" => {
            let v = (pick & 0x7F) as u8;
            syn::parse_quote!(#v)
        }
        "u16" => {
            let v = pick as u16;
            syn::parse_quote!(#v)
        }
        "u64" => {
            let v = pick as u64;
            syn::parse_quote!(#v)
        }
        "usize" => {
            let v = pick as usize;
            syn::parse_quote!(#v)
        }
        "i8" => {
            let v = (pick & 0x3F) as i8;
            syn::parse_quote!(#v)
        }
        "i16" => {
            let v = pick as i16;
            syn::parse_quote!(#v)
        }
        "i32" => {
            let v = pick as i32;
            syn::parse_quote!(#v)
        }
        "i64" => {
            let v = pick as i64;
            syn::parse_quote!(#v)
        }
        "isize" => {
            let v = pick as isize;
            syn::parse_quote!(#v)
        }
        "u128" => {
            let v = pick as u128;
            syn::parse_quote!(#v)
        }
        "i128" => {
            let v = pick as i128;
            syn::parse_quote!(#v)
        }
        "bool" => {
            let b = (pick & 1) == 1;
            syn::parse_quote!(#b)
        }
        "char" => {
            let ch = ['A', 'z', '\u{03BB}', '\u{2603}'][rng.gen_range(4)];
            syn::parse_quote!(#ch)
        }
        "ColorTag" => match rng.gen_range(3) {
            0 => syn::parse_quote!(ColorTag::Red),
            1 => syn::parse_quote!(ColorTag::Green),
            _ => syn::parse_quote!(ColorTag::Blue),
        },
        "NonZeroU32" | "core::num::NonZeroU32" => {
            syn::parse_quote!(unsafe { transmute::<u32, NonZeroU32>(#pick) })
        }
        "Option<NonZeroU32>"
        | "Option<core::num::NonZeroU32>"
        | "core::option::Option<NonZeroU32>"
        | "core::option::Option<core::num::NonZeroU32>" => {
            if (pick & 1) == 0 {
                syn::parse_quote!(None)
            } else {
                syn::parse_quote!(Some(unsafe { transmute::<u32, NonZeroU32>(#pick) }))
            }
        }
        "Option<bool>" | "core::option::Option<bool>" => match rng.gen_range(3) {
            0 => syn::parse_quote!(Some(true)),
            1 => syn::parse_quote!(Some(false)),
            _ => syn::parse_quote!(None),
        },
        "Option<ColorTag>" | "core::option::Option<ColorTag>" => match rng.gen_range(4) {
            0 => syn::parse_quote!(Some(ColorTag::Red)),
            1 => syn::parse_quote!(Some(ColorTag::Green)),
            2 => syn::parse_quote!(Some(ColorTag::Blue)),
            _ => syn::parse_quote!(None),
        },
        "MetersU32" => syn::parse_quote!(MetersU32(#pick)),
        "NonZeroMeters" => {
            syn::parse_quote!(NonZeroMeters(unsafe { transmute::<u32, NonZeroU32>(#pick) }))
        }
        "SingleC" => syn::parse_quote!(SingleC::Only(#pick)),
        "PairU32" => syn::parse_quote!(PairU32 { a: #pick, b: #pick ^ 3u32 }),
        "PaddedU8U32" => {
            let b = (pick & 0x7F) as u8;
            syn::parse_quote!(PaddedU8U32 { tag: #b, word: #pick })
        }
        "OverlayU32" => syn::parse_quote!(OverlayU32 { word: #pick }),
        "[u8;4]" => {
            let b0 = (pick & 0xFF) as u8;
            let b1 = ((pick >> 1) & 0xFF) as u8;
            syn::parse_quote!([#b0, #b1, #b0 ^ #b1, 1u8])
        }
        "[u32;2]" => syn::parse_quote!([#pick, #pick ^ 5u32]),
        _ => syn::parse_quote!(#pick),
    }
}

struct MethodCallNormalizer;

impl VisitMut for MethodCallNormalizer {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        syn::visit_mut::visit_expr_mut(self, expr);
        if let Expr::MethodCall(mc) = expr {
            let method = mc.method.to_string();
            let recv = &mc.receiver;
            if mc.args.len() == 1 {
                let arg = &mc.args[0];
                match method.as_str() {
                    "wrapping_add" | "saturating_add" => {
                        *expr = syn::parse_quote!(((#recv) ^ (#arg)));
                    }
                    "wrapping_sub" | "saturating_sub" => {
                        *expr = syn::parse_quote!(((#recv) ^ (#arg)));
                    }
                    "wrapping_mul" => {
                        *expr = syn::parse_quote!(((#recv) | (#arg)));
                    }
                    "rotate_left" => {
                        *expr = syn::parse_quote!(((#recv) << ((#arg) & 7u32)));
                    }
                    "rotate_right" => {
                        *expr = syn::parse_quote!(((#recv) >> ((#arg) & 7u32)));
                    }
                    _ => {}
                }
            }
        }
    }
}

/// Evaluate the seed function's entire body and original return expression
/// FIRST, then execute `setup_stmts` and fold `probe_ident` into the returned
/// value (for integer return types) or a live sink binding (for non-integer
/// return types).
///
/// Placing `let #tail_ident: #ret_ty = #tail_expr;` before `setup_stmts` ensures
/// that the seed body is never dead-coded by an injected probe and that any
/// divergence or fault inside the seed body executes before the tail probe.
fn inject_live_probe(func: &mut ItemFn, mut setup_stmts: Vec<Stmt>, probe_ident: &syn::Ident) {
    if let ReturnType::Type(_, ret_ty_box) = &func.sig.output {
        let ret_ty: Type = (**ret_ty_box).clone();
        let ret_ty_name = ret_ty.to_token_stream().to_string().replace(' ', "");
        if let Some(Stmt::Expr(tail_expr, None)) = func.block.stmts.last().cloned() {
            func.block.stmts.pop();
            let tail_ident = format_ident!("__tail_{probe_ident}");
            let tail_stmt: Stmt = syn::parse_quote! {
                let #tail_ident: #ret_ty = #tail_expr;
            };
            func.block.stmts.push(tail_stmt);
            func.block.stmts.append(&mut setup_stmts);
            if is_integer_type_name(&ret_ty_name) {
                let combined: Expr = syn::parse_quote! {
                    #tail_ident ^ (#probe_ident as #ret_ty)
                };
                func.block.stmts.push(Stmt::Expr(combined, None));
            } else {
                let sink_stmt: Stmt = syn::parse_quote! {
                    let mut __miri_sink: u32 = #probe_ident;
                };
                func.block.stmts.push(sink_stmt);
                let tail_ret: Expr = syn::parse_quote!(#tail_ident);
                func.block.stmts.push(Stmt::Expr(tail_ret, None));
            }
            return;
        }
    }
    let sink_stmt: Stmt = syn::parse_quote! {
        let mut __miri_sink: u32 = #probe_ident;
    };
    setup_stmts.push(sink_stmt);
    func.block.stmts.append(&mut setup_stmts);
}

/// Trait implemented by all Miri-strength AST mutators.
pub trait MiriAstMutator {
    /// Canonical human-readable name of this mutator pass.
    fn name(&self) -> &'static str;

    /// Mutates `file` in place using `rng`, appending any tracked locals to
    /// `locals_log`.
    fn mutate(&self, file: &mut File, rng: &mut DetRng, locals_log: &mut Vec<(String, String)>) {
        self.mutate_with_mode(file, rng, MutationMode::Pass, locals_log);
    }

    /// Mutates `file` in place under `mode` using `rng`.
    fn mutate_with_mode(
        &self,
        file: &mut File,
        rng: &mut DetRng,
        mode: MutationMode,
        locals_log: &mut Vec<(String, String)>,
    );
}

/// 1. Mutates integer binary operations, literals, and `as` casts (signedness
/// and width swaps) or unchecked arithmetic intrinsics over initialized integer
/// locals.
#[derive(Debug, Default, Clone, Copy)]
pub struct ArithmeticCastMutator;

struct ArithAstPerturber<'a> {
    rng: &'a mut DetRng,
}

impl VisitMut for ArithAstPerturber<'_> {
    fn visit_type_mut(&mut self, _ty: &mut Type) {
        // Never mutate array lengths `[T; N]` inside type annotations.
    }

    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        // Preserve loop termination conditions, array index expressions, and
        // intrinsic precondition arguments (`assume`, `exact_div`, shifts).
        if matches!(expr, Expr::While(_) | Expr::Index(_)) {
            return;
        }
        if let Expr::Call(call) = expr
            && let Expr::Path(ep) = &*call.func
            && let Some(seg) = ep.path.segments.last()
            && matches!(
                seg.ident.to_string().as_str(),
                "assume" | "exact_div" | "unchecked_shl" | "unchecked_shr" | "transmute" | "offset"
            )
        {
            return;
        }

        syn::visit_mut::visit_expr_mut(self, expr);

        // Swap or insert an intermediate width/signedness cast inside `Expr::Cast`
        // while keeping the outer cast type `#orig_ty` intact for type-checking.
        if let Expr::Cast(cast) = expr {
            let orig_ty: Type = (*cast.ty).clone();
            let orig_ty_str = orig_ty.to_token_stream().to_string().replace(' ', "");
            if is_integer_type_name(&orig_ty_str) && self.rng.coin(1, 2) {
                let alt_types: [&str; 10] = [
                    "u8", "i8", "u16", "i16", "u32", "i32", "u64", "i64", "usize", "isize",
                ];
                let pick_str = alt_types[self.rng.gen_range(alt_types.len())];
                if let Ok(alt_ty) = syn::parse_str::<Type>(pick_str) {
                    let inner = (*cast.expr).clone();
                    *expr = syn::parse_quote!(((#inner as #alt_ty) as #orig_ty));
                }
            }
        }
    }

    fn visit_bin_op_mut(&mut self, op: &mut BinOp) {
        if self.rng.coin(1, 2) {
            match op {
                BinOp::Add(_) => *op = syn::parse_quote!(^),
                BinOp::Sub(_) => *op = syn::parse_quote!(^),
                BinOp::BitXor(_) => *op = syn::parse_quote!(|),
                BinOp::BitAnd(_) => *op = syn::parse_quote!(^),
                BinOp::BitOr(_) => *op = syn::parse_quote!(&),
                BinOp::Lt(_) => *op = syn::parse_quote!(<=),
                BinOp::Le(_) => *op = syn::parse_quote!(<),
                _ => {}
            }
        }
    }

    fn visit_lit_mut(&mut self, lit: &mut Lit) {
        if let Lit::Int(li) = lit
            && self.rng.coin(1, 3)
        {
            let suffix = li.suffix();
            let val = li.base10_parse::<i128>().unwrap_or(0);
            if matches!(suffix, "u32" | "i32") && (1..=31).contains(&val) {
                let boundaries: &[u32] = &[1, 2, 3, 5, 7, 15, 31];
                let pick = boundaries[self.rng.gen_range(boundaries.len())];
                if let Ok(new_lit) = syn::parse_str::<Lit>(&format!("{pick}{suffix}")) {
                    *lit = new_lit;
                }
            } else if matches!(suffix, "u16" | "i16") && (1..=15).contains(&val) {
                let boundaries: &[u16] = &[1, 2, 3, 5, 7, 15];
                let pick = boundaries[self.rng.gen_range(boundaries.len())];
                if let Ok(new_lit) = syn::parse_str::<Lit>(&format!("{pick}{suffix}")) {
                    *lit = new_lit;
                }
            }
        }
    }
}

impl MiriAstMutator for ArithmeticCastMutator {
    fn name(&self) -> &'static str {
        "ArithmeticCastMutator"
    }

    fn mutate_with_mode(
        &self,
        file: &mut File,
        rng: &mut DetRng,
        mode: MutationMode,
        locals_log: &mut Vec<(String, String)>,
    ) {
        if matches!(mode, MutationMode::Pass | MutationMode::PerturbAst) {
            let mut visitor = ArithAstPerturber { rng };
            visitor.visit_file_mut(file);
        }

        for item in &mut file.items {
            let Item::Fn(func) = item else { continue };
            if func.sig.ident == "helper_add_ten" {
                continue;
            }
            let locals = collect_initialized_locals(func);
            for loc in &locals {
                locals_log.push((loc.name.clone(), loc.ty.clone()));
            }
            let tag = rng.next_u64() & 0xFFFF;
            let probe_ident = format_ident!("__miri_arith_{tag}");
            let mask_lit: u32 = [0x11u32, 0x2Au32, 0x55u32, 0x7Fu32][rng.gen_range(4)];
            let shift_lit: u32 = [1u32, 2u32, 3u32, 5u32][rng.gen_range(4)];

            let base_expr: Expr =
                if let Some(int_loc) = locals.iter().find(|l| is_integer_type_name(&l.ty)) {
                    let id = format_ident!("{}", int_loc.name);
                    syn::parse_quote!(#id as u32)
                } else {
                    syn::parse_quote!(#mask_lit)
                };

            let stmts: Vec<Stmt> = match mode {
                MutationMode::Pass | MutationMode::PerturbAst => {
                    let cast_pairs: [(&str, &str); 6] = [
                        ("i8", "i32"),
                        ("u8", "u32"),
                        ("i16", "i64"),
                        ("u16", "i64"),
                        ("i32", "i64"),
                        ("isize", "usize"),
                    ];
                    let (inter_s, wide_s) = cast_pairs[rng.gen_range(cast_pairs.len())];
                    let inter_ty: Type = syn::parse_str(inter_s).expect("valid inter_ty");
                    let wide_ty: Type = syn::parse_str(wide_s).expect("valid wide_ty");
                    syn::parse_quote! {
                        let __miri_wide: #wide_ty = ((#base_expr as #inter_ty) as #wide_ty) ^ (#mask_lit as #wide_ty);
                        let #probe_ident: u32 = ((__miri_wide as u32) << #shift_lit) ^ #mask_lit;
                    }
                }
                MutationMode::Panic => {
                    let variant = rng.gen_range(4);
                    match variant {
                        0 => syn::parse_quote! {
                            let __ovf_a: u32 = u32::MAX;
                            let __ovf_b: u32 = 1u32 + ((#base_expr) & 1u32);
                            let #probe_ident: u32 = __ovf_a + __ovf_b;
                        },
                        1 => syn::parse_quote! {
                            let __udf_a: u32 = (#base_expr) & 0u32;
                            let __udf_b: u32 = #shift_lit;
                            let #probe_ident: u32 = __udf_a - __udf_b;
                        },
                        2 => syn::parse_quote! {
                            let __div_a: u32 = #mask_lit ^ ((#base_expr) & 3u32);
                            let __div_z: u32 = (#base_expr) & 0u32;
                            let #probe_ident: u32 = __div_a / __div_z;
                        },
                        _ => syn::parse_quote! {
                            let __shl_v: u32 = #mask_lit ^ ((#base_expr) & 7u32);
                            let __shl_w: u32 = 32u32;
                            let #probe_ident: u32 = __shl_v << __shl_w;
                        },
                    }
                }
                MutationMode::Ub => {
                    let variant = rng.gen_range(4);
                    match variant {
                        0 => syn::parse_quote! {
                            let __ub_step: u32 = 1u32 + ((#base_expr) & 1u32);
                            let #probe_ident: u32 = unsafe { unchecked_add(u32::MAX, __ub_step) };
                        },
                        1 => syn::parse_quote! {
                            let __ub_step: u32 = 1u32 + ((#base_expr) & 1u32);
                            let #probe_ident: u32 = unsafe { unchecked_sub(0u32, __ub_step) };
                        },
                        2 => syn::parse_quote! {
                            let __ub_shl: u32 = 32u32 + ((#base_expr) & 1u32);
                            let #probe_ident: u32 = unsafe { unchecked_shl(1u32, __ub_shl) };
                        },
                        _ => syn::parse_quote! {
                            let __ub_zero: u32 = (#base_expr) & 0u32;
                            let #probe_ident: u32 = unsafe { unchecked_div(#mask_lit, __ub_zero) };
                        },
                    }
                }
            };
            inject_live_probe(func, stmts, &probe_ident);
        }
    }
}

/// 2. Perturbs AST array index expressions and struct field projections in
///    place, and exercises `PairU32` field projections and array indexing,
///    projections into and reinitialization of the univariant `#[repr(C)]`
///    `SingleC` enum, and partial writes to and active reads of `OverlayU32`
///    and `Uninit<[u32; 2]>` unions. In `Ub` mode it reads through dangling
///    projected fields and reads never-written union bytes.
///
/// `Uninit<PairU32>` does not type-check (`Uninit<T>` requires `T: Copy`, and
/// `PairU32` sits in the frozen first 729 lines of the corpus), so the union
/// templates overlay `[u32; 2]` instead.
#[derive(Debug, Default, Clone, Copy)]
pub struct PlaceProjectionWrapper;

fn unwrap_expr_parens_and_groups(mut expr: &Expr) -> &Expr {
    loop {
        match expr {
            Expr::Paren(p) => expr = &p.expr,
            Expr::Group(g) => expr = &g.expr,
            _ => return expr,
        }
    }
}

fn normalize_place_base(expr: &Expr) -> String {
    match unwrap_expr_parens_and_groups(expr) {
        Expr::Field(fe) => format!(
            "{}.{}",
            normalize_place_base(&fe.base),
            fe.member.to_token_stream()
        ),
        Expr::Index(ie) => format!(
            "{}[{}]",
            normalize_place_base(&ie.expr),
            ie.index.to_token_stream().to_string().replace(' ', "")
        ),
        Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => {
            format!("*({})", normalize_place_base(&u.expr))
        }
        other => other.to_token_stream().to_string().replace(' ', ""),
    }
}

fn pat_has_by_ref_field(pat: &Pat, inherited_ref: bool) -> bool {
    match unwrap_pat_type_and_parens(pat) {
        Pat::Struct(ps) => ps.fields.iter().any(|fp| match unwrap_pat_type_and_parens(&fp.pat) {
            Pat::Ident(pi) => inherited_ref || pi.by_ref.is_some(),
            other => pat_has_by_ref_field(other, inherited_ref),
        }),
        Pat::Reference(pr) => pat_has_by_ref_field(&pr.pat, true),
        _ => false,
    }
}

struct FieldRefCollector {
    bases: std::collections::BTreeSet<String>,
}

impl FieldRefCollector {
    fn record_field_chain(&mut self, expr: &Expr) {
        let mut cur = unwrap_expr_parens_and_groups(expr);
        loop {
            match cur {
                Expr::Field(fe) => {
                    if let syn::Member::Named(ident) = &fe.member
                        && matches!(ident.to_string().as_str(), "a" | "b")
                    {
                        self.bases.insert(normalize_place_base(&fe.base));
                    }
                    cur = unwrap_expr_parens_and_groups(&fe.base);
                }
                Expr::Index(ie) => {
                    cur = unwrap_expr_parens_and_groups(&ie.expr);
                }
                _ => break,
            }
        }
    }
}

impl<'ast> syn::visit::Visit<'ast> for FieldRefCollector {
    fn visit_expr_reference(&mut self, node: &'ast syn::ExprReference) {
        self.record_field_chain(&node.expr);
        syn::visit::visit_expr_reference(self, node);
    }

    fn visit_local(&mut self, node: &'ast Local) {
        if let Some(init) = &node.init
            && pat_has_by_ref_field(&node.pat, false)
        {
            let target = match unwrap_expr_parens_and_groups(&init.expr) {
                Expr::Reference(r) => &*r.expr,
                other => other,
            };
            self.bases.insert(normalize_place_base(target));
        }
        syn::visit::visit_local(self, node);
    }

    fn visit_expr_match(&mut self, node: &'ast syn::ExprMatch) {
        let scrut_is_ref = matches!(
            unwrap_expr_parens_and_groups(&node.expr),
            Expr::Reference(_)
        );
        if node
            .arms
            .iter()
            .any(|arm| pat_has_by_ref_field(&arm.pat, scrut_is_ref))
        {
            let target = match unwrap_expr_parens_and_groups(&node.expr) {
                Expr::Reference(r) => &*r.expr,
                other => other,
            };
            self.bases.insert(normalize_place_base(target));
        }
        syn::visit::visit_expr_match(self, node);
    }
}

struct ProjectionAstPerturber<'a> {
    rng: &'a mut DetRng,
    in_addr_or_lhs: bool,
    field_borrowed_bases: std::collections::BTreeSet<String>,
}

impl VisitMut for ProjectionAstPerturber<'_> {
    fn visit_type_mut(&mut self, _ty: &mut Type) {
        // Never mutate `[T; N]` array lengths in types.
    }

    fn visit_item_fn_mut(&mut self, func: &mut ItemFn) {
        let prev = std::mem::take(&mut self.field_borrowed_bases);
        let mut collector = FieldRefCollector {
            bases: std::collections::BTreeSet::new(),
        };
        syn::visit::Visit::visit_item_fn(&mut collector, func);
        self.field_borrowed_bases = collector.bases;
        syn::visit_mut::visit_item_fn_mut(self, func);
        self.field_borrowed_bases = prev;
    }

    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        match expr {
            Expr::Assign(assign) => {
                let prev = self.in_addr_or_lhs;
                self.in_addr_or_lhs = true;
                self.visit_expr_mut(&mut assign.left);
                self.in_addr_or_lhs = prev;
                self.visit_expr_mut(&mut assign.right);
                return;
            }
            Expr::Binary(bin)
                if matches!(
                    bin.op,
                    BinOp::AddAssign(_)
                        | BinOp::SubAssign(_)
                        | BinOp::MulAssign(_)
                        | BinOp::DivAssign(_)
                        | BinOp::RemAssign(_)
                        | BinOp::BitXorAssign(_)
                        | BinOp::BitAndAssign(_)
                        | BinOp::BitOrAssign(_)
                        | BinOp::ShlAssign(_)
                        | BinOp::ShrAssign(_)
                ) =>
            {
                let prev = self.in_addr_or_lhs;
                self.in_addr_or_lhs = true;
                self.visit_expr_mut(&mut bin.left);
                self.in_addr_or_lhs = prev;
                self.visit_expr_mut(&mut bin.right);
                return;
            }
            Expr::Reference(_) | Expr::RawAddr(_) => {
                // Preserve `&raw const pair.a` / `&mut pair.b` targets so pointer
                // offsets starting from `.a` retain their intended base field.
                return;
            }
            _ => {}
        }

        syn::visit_mut::visit_expr_mut(self, expr);

        match expr {
            Expr::Index(idx_expr) if !self.in_addr_or_lhs => {
                let base_clean = idx_expr.expr.to_token_stream().to_string().replace(' ', "");
                if let Expr::Lit(el) = &mut *idx_expr.index
                    && let Lit::Int(li) = &el.lit
                    && let Ok(cur_idx) = li.base10_parse::<usize>()
                    && self.rng.coin(1, 2)
                {
                    // Partial-init `Uninit` bases (`u.value`,
                    // `__part_slot.value`, `__proj_half.value`, `slot.value`)
                    // initialize only lane 0, so lane 0 must remain 0 and
                    // uninitialized lanes 1..=3 must stay in 1..=3. `bytes`
                    // and `__pad_bytes` in `PaddedU8U32` have padding at
                    // 1..=3. `OverlayU32` `.bytes[0..4]` has all four byte
                    // lanes initialized.
                    let is_partial_uninit = matches!(
                        base_clean.as_str(),
                        "u.value" | "__part_slot.value" | "__proj_half.value" | "slot.value"
                    );
                    let new_idx: usize = if (is_partial_uninit
                        || matches!(base_clean.as_str(), "bytes" | "__pad_bytes"))
                        && (1..=3).contains(&cur_idx)
                    {
                        let choices = match cur_idx {
                            1 => [2usize, 3],
                            2 => [1, 3],
                            _ => [1, 2],
                        };
                        choices[self.rng.gen_range(2)]
                    } else if is_partial_uninit && cur_idx == 0 {
                        0
                    } else if base_clean.ends_with(".bytes") && cur_idx < 4 {
                        (cur_idx + 1 + self.rng.gen_range(3)) % 4
                    } else if cur_idx == 0 {
                        1
                    } else {
                        0
                    };
                    idx_expr.index = Box::new(syn::parse_quote!(#new_idx));
                }
            }
            Expr::Field(field_expr) if !self.in_addr_or_lhs => {
                let base_clean = normalize_place_base(&field_expr.base);
                if !self.field_borrowed_bases.contains(&base_clean)
                    && let syn::Member::Named(ident) = &mut field_expr.member
                {
                    let name = ident.to_string();
                    if (name == "a" || name == "b") && self.rng.coin(1, 2) {
                        *ident = if name == "a" {
                            format_ident!("b")
                        } else {
                            format_ident!("a")
                        };
                    }
                }
            }
            _ => {}
        }
    }
}

impl MiriAstMutator for PlaceProjectionWrapper {
    fn name(&self) -> &'static str {
        "PlaceProjectionWrapper"
    }

    fn mutate_with_mode(
        &self,
        file: &mut File,
        rng: &mut DetRng,
        mode: MutationMode,
        locals_log: &mut Vec<(String, String)>,
    ) {
        if matches!(mode, MutationMode::Pass | MutationMode::PerturbAst) {
            let mut visitor = ProjectionAstPerturber {
                rng,
                in_addr_or_lhs: false,
                field_borrowed_bases: std::collections::BTreeSet::new(),
            };
            visitor.visit_file_mut(file);
        }

        for item in &mut file.items {
            let Item::Fn(func) = item else { continue };
            if func.sig.ident == "helper_add_ten" {
                continue;
            }
            let locals = collect_initialized_locals(func);
            for loc in &locals {
                locals_log.push((loc.name.clone(), loc.ty.clone()));
            }
            let tag = rng.next_u64() & 0xFFFF;
            let probe_ident = format_ident!("__miri_proj_{tag}");
            let c0: u32 = [3u32, 9u32, 17u32, 33u32][rng.gen_range(4)];
            let c1: u32 = [5u32, 12u32, 24u32, 48u32][rng.gen_range(4)];
            let seed_val: Expr =
                if let Some(int_loc) = locals.iter().find(|l| is_integer_type_name(&l.ty)) {
                    let id = format_ident!("{}", int_loc.name);
                    syn::parse_quote!((#id as u32) & 0xFFFFu32)
                } else {
                    syn::parse_quote!(#c0)
                };

            let stmts: Vec<Stmt> = match mode {
                MutationMode::Pass | MutationMode::PerturbAst => match rng.gen_range(5) {
                    0 => {
                        let idx_lit: usize = rng.gen_range(2);
                        syn::parse_quote! {
                            let mut __proj_pair: PairU32 = PairU32 { a: #seed_val, b: #c1 };
                            let __proj_ref: &mut u32 = &mut __proj_pair.b;
                            *__proj_ref = (*__proj_ref) ^ #c0;
                            let __proj_arr: [u32; 2] = [__proj_pair.a, __proj_pair.b];
                            let #probe_ident: u32 = __proj_arr[#idx_lit];
                        }
                    }
                    1 => {
                        // Project the payload of a univariant `#[repr(C)]` enum
                        // through `&mut SingleC`, then reinitialize the whole
                        // value.
                        syn::parse_quote! {
                            let mut __proj_single: SingleC = SingleC::Only(#seed_val);
                            let __proj_single_ref: &mut SingleC = &mut __proj_single;
                            match __proj_single_ref {
                                SingleC::Only(__proj_inner) => {
                                    *__proj_inner = (*__proj_inner) ^ #c0;
                                }
                            }
                            __proj_single = SingleC::Only(match __proj_single {
                                SingleC::Only(__proj_v) => __proj_v ^ #c1,
                            });
                            let #probe_ident: u32 = match __proj_single {
                                SingleC::Only(__proj_w) => __proj_w,
                            };
                        }
                    }
                    2 => {
                        // Write one byte of the `bytes` overlay through a
                        // `*mut [u8; 4]`, then read the active `word` and a
                        // byte.
                        let write_idx: usize = rng.gen_range(4);
                        let read_idx: usize = rng.gen_range(4);
                        let byte_u8: u8 = [0x5Au8, 1u8, 0x80u8, 0xFFu8][rng.gen_range(4)];
                        syn::parse_quote! {
                            let mut __proj_overlay: OverlayU32 = OverlayU32 { word: #seed_val };
                            let __proj_bytes: *mut [u8; 4] = &raw mut __proj_overlay.bytes;
                            unsafe {
                                (*__proj_bytes)[#write_idx] = #byte_u8;
                            }
                            let #probe_ident: u32 = unsafe {
                                __proj_overlay.word ^ (__proj_overlay.bytes[#read_idx] as u32)
                            };
                        }
                    }
                    3 => {
                        // Initialize both halves of an uninitialized union with
                        // partial-width writes, then read them back.
                        syn::parse_quote! {
                            let mut __proj_slot: Uninit<[u32; 2]> = Uninit { uninit: () };
                            let #probe_ident: u32 = unsafe {
                                __proj_slot.value[0] = #seed_val;
                                __proj_slot.value[1] = #c1;
                                __proj_slot.value[0] ^ __proj_slot.value[1]
                            };
                        }
                    }
                    _ => {
                        // Project `NonZeroMeters.0` via `&raw const`, then
                        // reinitialize an `OverlayU32` union wholesale via its
                        // `bytes` variant (`Deinit`) and read `word` + `bytes`.
                        let nz_u32: u32 = [1u32, 9u32, 17u32, 33u32][rng.gen_range(4)];
                        let read_idx: usize = rng.gen_range(4);
                        syn::parse_quote! {
                            let __proj_nz: NonZeroU32 = unsafe { transmute::<u32, NonZeroU32>(#nz_u32) };
                            let __proj_nzm: NonZeroMeters = NonZeroMeters(__proj_nz);
                            let __proj_nzm_ptr: *const NonZeroU32 = &raw const __proj_nzm.0;
                            let __proj_nzm_val: u32 = unsafe { transmute::<NonZeroU32, u32>(*__proj_nzm_ptr) };
                            let mut __proj_ov_reinit: OverlayU32 = OverlayU32 { word: #seed_val ^ __proj_nzm_val };
                            __proj_ov_reinit = OverlayU32 { bytes: [1u8, 2u8, 3u8, 4u8] };
                            let #probe_ident: u32 = unsafe {
                                __proj_ov_reinit.word ^ (__proj_ov_reinit.bytes[#read_idx] as u32) ^ __proj_nzm_val
                            };
                        }
                    }
                },
                MutationMode::Panic => {
                    let oob_idx: usize = 3 + rng.gen_range(3);
                    syn::parse_quote! {
                        let __oob_arr: [u32; 3] = [#seed_val, #c1, #c0 ^ #c1];
                        let __oob_idx: usize = #oob_idx;
                        let #probe_ident: u32 = __oob_arr[__oob_idx];
                    }
                }
                MutationMode::Ub => match rng.gen_range(5) {
                    0 => syn::parse_quote! {
                        let __dangling_ptr: *mut u32 = {
                            let mut __dead_slot: u32 = #seed_val;
                            &raw mut __dead_slot
                        };
                        let #probe_ident: u32 = unsafe { *__dangling_ptr };
                    },
                    1 => syn::parse_quote! {
                        let __dangling_field: *const u32 = {
                            let __dead_pair: PairU32 = PairU32 { a: #seed_val, b: #c1 };
                            &raw const __dead_pair.b
                        };
                        let #probe_ident: u32 = unsafe { *__dangling_field };
                    },
                    2 => syn::parse_quote! {
                        let __dangling_payload: *const u32 = {
                            let __dead_single: SingleC = SingleC::Only(#seed_val);
                            match &__dead_single {
                                SingleC::Only(__dead_inner) => __dead_inner as *const u32,
                            }
                        };
                        let #probe_ident: u32 = unsafe { *__dangling_payload };
                    },
                    3 => syn::parse_quote! {
                        let mut __proj_half: Uninit<[u32; 2]> = Uninit { uninit: () };
                        let __proj_half_read: usize = 1usize;
                        let #probe_ident: u32 = unsafe {
                            __proj_half.value[0] = #seed_val;
                            __proj_half.value[__proj_half_read]
                        };
                    },
                    _ => syn::parse_quote! {
                        let __dangling_ov_word: *const u32 = {
                            let __dead_ov: OverlayU32 = OverlayU32 { word: #seed_val ^ #c1 };
                            &raw const __dead_ov.word
                        };
                        let #probe_ident: u32 = unsafe { *__dangling_ov_word };
                    },
                },
            };
            inject_live_probe(func, stmts, &probe_ident);
        }
    }
}

/// 3. Perturbs `core::intrinsics::offset` arguments in place and synthesizes
/// raw pointer address-of and `offset` dereferences across in-bounds (`0isize`,
/// `1isize`), out-of-bounds (`2isize`, `-1isize`), null, and unaligned
/// addresses.
#[derive(Debug, Default, Clone, Copy)]
pub struct RawPtrOffsetMutator;

struct OffsetArgPerturber<'a> {
    rng: &'a mut DetRng,
    allow_oob: bool,
}

impl VisitMut for OffsetArgPerturber<'_> {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        syn::visit_mut::visit_expr_mut(self, expr);
        if let Expr::Call(call) = expr
            && let Expr::Path(ep) = &*call.func
            && ep.path.segments.last().is_some_and(|s| s.ident == "offset")
            && call.args.len() == 2
            && self.rng.coin(1, 2)
        {
            let step: isize = if self.allow_oob {
                let choices: [isize; 4] = [0, 1, 2, -1];
                choices[self.rng.gen_range(choices.len())]
            } else {
                let choices: [isize; 2] = [0, 1];
                choices[self.rng.gen_range(choices.len())]
            };
            call.args[1] = syn::parse_quote!(#step);
        }
    }
}

impl MiriAstMutator for RawPtrOffsetMutator {
    fn name(&self) -> &'static str {
        "RawPtrOffsetMutator"
    }

    fn mutate_with_mode(
        &self,
        file: &mut File,
        rng: &mut DetRng,
        mode: MutationMode,
        locals_log: &mut Vec<(String, String)>,
    ) {
        if matches!(
            mode,
            MutationMode::Pass | MutationMode::PerturbAst | MutationMode::Ub
        ) {
            let mut v = OffsetArgPerturber {
                rng,
                allow_oob: matches!(mode, MutationMode::PerturbAst | MutationMode::Ub),
            };
            v.visit_file_mut(file);
        }

        for item in &mut file.items {
            let Item::Fn(func) = item else { continue };
            if func.sig.ident == "helper_add_ten" {
                continue;
            }
            let locals = collect_initialized_locals(func);
            for loc in &locals {
                locals_log.push((loc.name.clone(), loc.ty.clone()));
            }
            let tag = rng.next_u64() & 0xFFFF;
            let probe_ident = format_ident!("__miri_ptr_{tag}");
            let c_a: u32 = [11u32, 22u32, 44u32, 88u32][rng.gen_range(4)];
            let c_b: u32 = [33u32, 66u32, 99u32, 132u32][rng.gen_range(4)];

            let stmts: Vec<Stmt> = match mode {
                MutationMode::Pass => {
                    syn::parse_quote! {
                        let __ptr_pair: PairU32 = PairU32 { a: #c_a, b: #c_b };
                        let __base_ptr: *const u32 = &raw const __ptr_pair.a;
                        let #probe_ident: u32 = unsafe { *offset(__base_ptr, 0isize) };
                    }
                }
                MutationMode::PerturbAst => {
                    // Cross-field offset 1isize exercises `pass_ptr_offset_within_array`.
                    let step: isize = if rng.coin(1, 2) { 1 } else { 0 };
                    syn::parse_quote! {
                        let __ptr_pair: PairU32 = PairU32 { a: #c_a, b: #c_b };
                        let __base_ptr: *const u32 = &raw const __ptr_pair.a;
                        let #probe_ident: u32 = unsafe { *offset(__base_ptr, #step) };
                    }
                }
                MutationMode::Panic => {
                    syn::parse_quote! {
                        let __ptr_arr: [u32; 2] = [#c_a, #c_b];
                        let __oob: usize = 2usize;
                        let #probe_ident: u32 = __ptr_arr[__oob];
                    }
                }
                MutationMode::Ub => {
                    let variant = rng.gen_range(4);
                    match variant {
                        0 => syn::parse_quote! {
                            let __null_p: *const u32 = 0usize as *const u32;
                            let #probe_ident: u32 = unsafe { *__null_p };
                        },
                        1 => syn::parse_quote! {
                            let __oob_pair: PairU32 = PairU32 { a: #c_a, b: #c_b };
                            let __oob_base: *const u32 = &raw const __oob_pair.a;
                            let #probe_ident: u32 = unsafe { *offset(__oob_base, 2isize) };
                        },
                        2 => syn::parse_quote! {
                            let __neg_pair: PairU32 = PairU32 { a: #c_a, b: #c_b };
                            let __neg_base: *const u32 = &raw const __neg_pair.a;
                            let #probe_ident: u32 = unsafe { *offset(__neg_base, -1isize) };
                        },
                        _ => syn::parse_quote! {
                            let __unaligned_pair: PairU32 = PairU32 { a: #c_a, b: #c_b };
                            let __u8_base: *const u8 = (&raw const __unaligned_pair.a) as *const u8;
                            let #probe_ident: u32 = unsafe { *(offset(__u8_base, 1isize) as *const u32) };
                        },
                    }
                }
            };
            inject_live_probe(func, stmts, &probe_ident);
        }
    }
}

/// 4. Reorders adjacent pointer/reference access statements in aliasing blocks
///    and interleaves Tree Borrows shared/mutable reborrow transitions,
///    including `&raw const` / `&raw mut` (`Retag(Raw)`) pointers to whole
///    places and to disjoint fields, interleaved with frozen `&` and active
///    `&mut` borrows.
///
/// `Pass`/`PerturbAst` templates never write through a sibling reborrow
/// between creating a field pointer with `&raw mut (*m).f` and using it: for
/// that pattern, Miri's Tree Borrows lets the raw pointer keep `m`'s tag, but
/// Anneal reports a false-positive UB at the raw write.
#[derive(Debug, Default, Clone, Copy)]
pub struct TreeBorrowsRetagInterleaver;

/// Visitor checking whether an expression performs a non-local control-flow
/// exit (`return`, an unenclosed or outer-labeled `break` / `continue`, or a
/// diverging `panic!` / `unreachable` invocation) from the current statement.
struct ControlExitFinder {
    unlabeled_loop_depth: usize,
    bound_labels: Vec<String>,
    found: bool,
}

impl ControlExitFinder {
    fn is_diverging_macro_path(path: &syn::Path) -> bool {
        path.segments.last().is_some_and(|s| {
            matches!(
                s.ident.to_string().as_str(),
                "panic"
                    | "unreachable"
                    | "todo"
                    | "unimplemented"
                    | "assert"
                    | "assert_eq"
                    | "assert_ne"
                    | "assert_matches"
                    | "debug_assert"
                    | "debug_assert_eq"
                    | "debug_assert_ne"
                    | "debug_assert_matches"
            )
        })
    }
}

impl<'ast> syn::visit::Visit<'ast> for ControlExitFinder {
    fn visit_item(&mut self, _item: &'ast Item) {}

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        if Self::is_diverging_macro_path(&mac.path) {
            self.found = true;
        }
    }

    fn visit_expr(&mut self, expr: &'ast Expr) {
        if self.found {
            return;
        }
        match expr {
            Expr::Closure(_) | Expr::Async(_) | Expr::Const(_) => {}
            Expr::Return(_) => {
                self.found = true;
            }
            Expr::Break(brk) => {
                let bound = match &brk.label {
                    Some(lbl) => self.bound_labels.contains(&lbl.ident.to_string()),
                    None => self.unlabeled_loop_depth > 0,
                };
                if !bound {
                    self.found = true;
                    return;
                }
                syn::visit::visit_expr(self, expr);
            }
            Expr::Continue(cnt) => {
                let bound = match &cnt.label {
                    Some(lbl) => self.bound_labels.contains(&lbl.ident.to_string()),
                    None => self.unlabeled_loop_depth > 0,
                };
                if !bound {
                    self.found = true;
                }
            }
            Expr::While(w) => {
                self.unlabeled_loop_depth += 1;
                if let Some(lbl) = &w.label {
                    self.bound_labels.push(lbl.name.ident.to_string());
                }
                syn::visit::visit_expr(self, expr);
                if w.label.is_some() {
                    self.bound_labels.pop();
                }
                self.unlabeled_loop_depth -= 1;
            }
            Expr::Loop(l) => {
                self.unlabeled_loop_depth += 1;
                if let Some(lbl) = &l.label {
                    self.bound_labels.push(lbl.name.ident.to_string());
                }
                syn::visit::visit_expr(self, expr);
                if l.label.is_some() {
                    self.bound_labels.pop();
                }
                self.unlabeled_loop_depth -= 1;
            }
            Expr::ForLoop(f) => {
                self.unlabeled_loop_depth += 1;
                if let Some(lbl) = &f.label {
                    self.bound_labels.push(lbl.name.ident.to_string());
                }
                syn::visit::visit_expr(self, expr);
                if f.label.is_some() {
                    self.bound_labels.pop();
                }
                self.unlabeled_loop_depth -= 1;
            }
            Expr::Block(b) if b.label.is_some() => {
                if let Some(lbl) = &b.label {
                    self.bound_labels.push(lbl.name.ident.to_string());
                }
                syn::visit::visit_expr(self, expr);
                self.bound_labels.pop();
            }
            Expr::Macro(m) => {
                if Self::is_diverging_macro_path(&m.mac.path) {
                    self.found = true;
                }
            }
            Expr::Call(call) => {
                if let Expr::Path(ep) = &*call.func
                    && ep.path.segments.last().is_some_and(|s| {
                        matches!(
                            s.ident.to_string().as_str(),
                            "unreachable"
                                | "abort"
                                | "panic"
                                | "panic_fmt"
                                | "panic_explicit"
                                | "panic_nounwind"
                                | "const_panic_fmt"
                        )
                    })
                {
                    self.found = true;
                    return;
                }
                syn::visit::visit_expr(self, expr);
            }
            _ => syn::visit::visit_expr(self, expr),
        }
    }
}

fn expr_has_control_exit(expr: &Expr) -> bool {
    let mut finder = ControlExitFinder {
        unlabeled_loop_depth: 0,
        bound_labels: Vec::new(),
        found: false,
    };
    syn::visit::Visit::visit_expr(&mut finder, expr);
    finder.found
}

struct IdentMentionFinder<'a> {
    target: &'a str,
    found: bool,
}

impl<'ast> syn::visit::Visit<'ast> for IdentMentionFinder<'_> {
    fn visit_ident(&mut self, ident: &'ast syn::Ident) {
        if ident == self.target {
            self.found = true;
        }
    }
}

fn stmts_mention_ident(stmts: &[Stmt], target: &str) -> bool {
    let mut finder = IdentMentionFinder {
        target,
        found: false,
    };
    for stmt in stmts {
        syn::visit::Visit::visit_stmt(&mut finder, stmt);
        if finder.found {
            return true;
        }
    }
    false
}

/// Classify `stmt` for adjacent-statement swapping:
/// - `None` if `stmt` is not a reorderable access statement;
/// - `Some(None)` if `stmt` is a non-exiting expression statement or wildcard
///   `let _ [: T] = ...;` read;
/// - `Some(Some(name))` if `stmt` is a non-exiting `let _name [: T] = ...;`
///   binding.
fn reorderable_stmt_bound_ident(stmt: &Stmt) -> Option<Option<String>> {
    match stmt {
        Stmt::Expr(expr, Some(_)) => (!expr_has_control_exit(expr)).then_some(None),
        Stmt::Local(loc) => {
            let init = loc.init.as_ref()?;
            if init.diverge.is_some() || expr_has_control_exit(&init.expr) {
                return None;
            }
            match unwrap_pat_type_and_parens(&loc.pat) {
                Pat::Wild(_) => Some(None),
                Pat::Ident(pi) if pi.subpat.is_none() => {
                    let name = pi.ident.to_string();
                    name.starts_with('_').then_some(Some(name))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn collect_stmt_idents(stmt: &Stmt) -> std::collections::BTreeSet<String> {
    struct AllIdentCollector(std::collections::BTreeSet<String>);
    impl<'ast> syn::visit::Visit<'ast> for AllIdentCollector {
        fn visit_item(&mut self, _item: &'ast Item) {}
        fn visit_ident(&mut self, ident: &'ast syn::Ident) {
            self.0.insert(ident.to_string());
        }
    }
    let mut c = AllIdentCollector(std::collections::BTreeSet::new());
    syn::visit::Visit::visit_stmt(&mut c, stmt);
    c.0
}

fn is_raw_ptr_type(ty: &Type) -> bool {
    match ty {
        Type::Paren(p) => is_raw_ptr_type(&p.elem),
        Type::Group(g) => is_raw_ptr_type(&g.elem),
        Type::Ptr(_) => true,
        _ => false,
    }
}

fn is_raw_ptr_init_expr(expr: &Expr) -> bool {
    match unwrap_expr_parens_and_groups(expr) {
        Expr::RawAddr(_) => true,
        Expr::Cast(c) => is_raw_ptr_type(&c.ty),
        Expr::Block(b) => match b.block.stmts.last() {
            Some(Stmt::Expr(tail, None)) => is_raw_ptr_init_expr(tail),
            _ => false,
        },
        Expr::Unsafe(u) => match u.block.stmts.last() {
            Some(Stmt::Expr(tail, None)) => is_raw_ptr_init_expr(tail),
            _ => false,
        },
        _ => false,
    }
}

fn extract_place_root_ident(
    expr: &Expr,
    raw_ptr_locals: &std::collections::BTreeSet<String>,
) -> Option<String> {
    let mut cur = unwrap_expr_parens_and_groups(expr);
    let mut saw_deref = false;
    loop {
        match cur {
            Expr::Field(fe) => cur = unwrap_expr_parens_and_groups(&fe.base),
            Expr::Index(ie) => cur = unwrap_expr_parens_and_groups(&ie.expr),
            Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => {
                saw_deref = true;
                cur = unwrap_expr_parens_and_groups(&u.expr);
            }
            Expr::Path(ep) if ep.qself.is_none() && ep.path.segments.len() == 1 => {
                let root = ep.path.segments[0].ident.to_string();
                if saw_deref && raw_ptr_locals.contains(&root) {
                    return None;
                }
                return Some(root);
            }
            _ => return None,
        }
    }
}

fn extract_safe_borrow_root(
    expr: &Expr,
    raw_ptr_locals: &std::collections::BTreeSet<String>,
) -> Option<String> {
    match unwrap_expr_parens_and_groups(expr) {
        Expr::Reference(r) => extract_place_root_ident(&r.expr, raw_ptr_locals),
        Expr::Block(b) => match b.block.stmts.last() {
            Some(Stmt::Expr(tail, None)) => extract_safe_borrow_root(tail, raw_ptr_locals),
            _ => None,
        },
        Expr::Unsafe(u) => match u.block.stmts.last() {
            Some(Stmt::Expr(tail, None)) => extract_safe_borrow_root(tail, raw_ptr_locals),
            _ => None,
        },
        _ => None,
    }
}

#[derive(Default)]
struct SafeBorrowContext {
    raw_ptr_locals: std::collections::BTreeSet<String>,
    direct_borrows: std::collections::BTreeMap<String, std::collections::BTreeSet<String>>,
}

impl SafeBorrowContext {
    fn from_block(block: &Block) -> Self {
        let mut ctx = Self::default();
        syn::visit::Visit::visit_block(&mut RawPtrCollector(&mut ctx.raw_ptr_locals), block);
        syn::visit::Visit::visit_block(&mut BorrowCollector(&mut ctx), block);
        ctx
    }

    fn from_item_fn(func: &ItemFn) -> Self {
        let mut ctx = Self::default();
        for arg in &func.sig.inputs {
            if let FnArg::Typed(pat_ty) = arg
                && is_raw_ptr_type(&pat_ty.ty)
                && let (Some(name), _) = extract_pat_ident(&pat_ty.pat)
            {
                ctx.raw_ptr_locals.insert(name);
            }
        }
        syn::visit::Visit::visit_block(&mut RawPtrCollector(&mut ctx.raw_ptr_locals), &func.block);
        syn::visit::Visit::visit_block(&mut BorrowCollector(&mut ctx), &func.block);
        ctx
    }

    fn transitive_roots(&self, ident: &str) -> std::collections::BTreeSet<String> {
        let mut visited = std::collections::BTreeSet::new();
        let mut stack: Vec<String> = self
            .direct_borrows
            .get(ident)
            .into_iter()
            .flatten()
            .cloned()
            .collect();
        while let Some(cur) = stack.pop() {
            if visited.insert(cur.clone())
                && let Some(nexts) = self.direct_borrows.get(&cur)
            {
                for n in nexts {
                    if !visited.contains(n) {
                        stack.push(n.clone());
                    }
                }
            }
        }
        visited
    }

    fn collect_potential_value_moves(&self, stmt: &Stmt) -> std::collections::BTreeSet<String> {
        struct ValueMoveVisitor<'a> {
            raw_ptr_locals: &'a std::collections::BTreeSet<String>,
            moves: std::collections::BTreeSet<String>,
        }
        impl ValueMoveVisitor<'_> {
            fn check_value_expr(&mut self, expr: &Expr) {
                match unwrap_expr_parens_and_groups(expr) {
                    Expr::Path(ep) if ep.qself.is_none() && ep.path.segments.len() == 1 => {
                        let name = ep.path.segments[0].ident.to_string();
                        if !name.starts_with(|c: char| c.is_ascii_uppercase())
                            && !self.raw_ptr_locals.contains(&name)
                        {
                            self.moves.insert(name);
                        }
                    }
                    Expr::Block(b) => {
                        for s in &b.block.stmts {
                            syn::visit::Visit::visit_stmt(self, s);
                        }
                    }
                    Expr::Unsafe(u) => {
                        for s in &u.block.stmts {
                            syn::visit::Visit::visit_stmt(self, s);
                        }
                    }
                    other => syn::visit::Visit::visit_expr(self, other),
                }
            }
        }
        impl<'ast> syn::visit::Visit<'ast> for ValueMoveVisitor<'_> {
            fn visit_item(&mut self, _item: &'ast Item) {}
            fn visit_expr_reference(&mut self, _node: &'ast syn::ExprReference) {}
            fn visit_expr_raw_addr(&mut self, _node: &'ast syn::ExprRawAddr) {}
            fn visit_local(&mut self, node: &'ast Local) {
                if let Some(init) = &node.init {
                    // `let _ = place;` never moves `place` in Rust.
                    if !matches!(unwrap_pat_type_and_parens(&node.pat), Pat::Wild(_)) {
                        self.check_value_expr(&init.expr);
                    } else {
                        syn::visit::visit_expr(self, &init.expr);
                    }
                }
            }
            fn visit_expr(&mut self, expr: &'ast Expr) {
                match expr {
                    Expr::Reference(_) | Expr::RawAddr(_) => {}
                    Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => {}
                    Expr::Assign(a) => {
                        self.check_value_expr(&a.right);
                    }
                    Expr::Call(c) => {
                        for arg in &c.args {
                            self.check_value_expr(arg);
                        }
                    }
                    Expr::Tuple(t) => {
                        for elem in &t.elems {
                            self.check_value_expr(elem);
                        }
                    }
                    Expr::Array(arr) => {
                        for elem in &arr.elems {
                            self.check_value_expr(elem);
                        }
                    }
                    Expr::Struct(st) => {
                        for field in &st.fields {
                            self.check_value_expr(&field.expr);
                        }
                    }
                    _ => syn::visit::visit_expr(self, expr),
                }
            }
        }
        let mut v = ValueMoveVisitor {
            raw_ptr_locals: &self.raw_ptr_locals,
            moves: std::collections::BTreeSet::new(),
        };
        match stmt {
            Stmt::Expr(e, Some(_)) => v.check_value_expr(e),
            _ => syn::visit::Visit::visit_stmt(&mut v, stmt),
        }
        v.moves
    }
}

struct RawPtrCollector<'a>(&'a mut std::collections::BTreeSet<String>);

impl<'ast> syn::visit::Visit<'ast> for RawPtrCollector<'_> {
    fn visit_item(&mut self, _item: &'ast Item) {}
    fn visit_local(&mut self, node: &'ast Local) {
        if let (Some(name), _) = extract_pat_ident(&node.pat) {
            let ty_is_raw = extract_outer_pat_type(&node.pat).is_some_and(is_raw_ptr_type);
            let init_is_raw = node
                .init
                .as_ref()
                .is_some_and(|i| is_raw_ptr_init_expr(&i.expr));
            if ty_is_raw || init_is_raw {
                self.0.insert(name);
            }
        }
        syn::visit::visit_local(self, node);
    }
}

struct BorrowCollector<'a>(&'a mut SafeBorrowContext);

impl<'ast> syn::visit::Visit<'ast> for BorrowCollector<'_> {
    fn visit_item(&mut self, _item: &'ast Item) {}

    fn visit_local(&mut self, node: &'ast Local) {
        if let Some(init) = &node.init {
            if let (Some(lhs), _) = extract_pat_ident(&node.pat)
                && let Some(root) = extract_safe_borrow_root(&init.expr, &self.0.raw_ptr_locals)
            {
                self.0.direct_borrows.entry(lhs).or_default().insert(root);
            }
            if pat_has_by_ref_field(&node.pat, false)
                || matches!(
                    unwrap_pat_type_and_parens(&node.pat),
                    Pat::Ident(pi) if pi.by_ref.is_some()
                )
            {
                let scrut = match unwrap_expr_parens_and_groups(&init.expr) {
                    Expr::Reference(r) => &*r.expr,
                    other => other,
                };
                if let Some(root) = extract_place_root_ident(scrut, &self.0.raw_ptr_locals) {
                    let mut bound = Vec::new();
                    collect_pat_bound_idents(&node.pat, &mut bound);
                    for b in bound {
                        self.0
                            .direct_borrows
                            .entry(b)
                            .or_default()
                            .insert(root.clone());
                    }
                }
            }
        }
        syn::visit::visit_local(self, node);
    }

    fn visit_expr_assign(&mut self, node: &'ast syn::ExprAssign) {
        if let Expr::Path(ep) = unwrap_expr_parens_and_groups(&node.left)
            && ep.qself.is_none()
            && ep.path.segments.len() == 1
            && let Some(root) = extract_safe_borrow_root(&node.right, &self.0.raw_ptr_locals)
        {
            let lhs = ep.path.segments[0].ident.to_string();
            self.0.direct_borrows.entry(lhs).or_default().insert(root);
        }
        syn::visit::visit_expr_assign(self, node);
    }
}

/// Checks whether swapping `stmts[idx]` and `stmts[idx + 1]` preserves lexical
/// binding scope, NLL safe-borrow disjointness, and non-`Copy` value lifetimes.
fn can_swap_adjacent_stmts(stmts: &[Stmt], idx: usize, borrow_ctx: &SafeBorrowContext) -> bool {
    let Some(bound_a) = reorderable_stmt_bound_ident(&stmts[idx]) else {
        return false;
    };
    let Some(bound_b) = reorderable_stmt_bound_ident(&stmts[idx + 1]) else {
        return false;
    };
    if let Some(name_a) = &bound_a
        && stmts_mention_ident(&stmts[idx + 1..], name_a)
    {
        return false;
    }
    if let Some(name_b) = &bound_b
        && (stmts_mention_ident(&stmts[idx + 2..], name_b)
            || stmts_mention_ident(&stmts[idx..=idx], name_b))
    {
        return false;
    }

    let idents_a = collect_stmt_idents(&stmts[idx]);
    let idents_b = collect_stmt_idents(&stmts[idx + 1]);

    // Never swap a safe reference access across an access to its borrowed
    // owner/ancestor (prevents NLL `E0506`/`E0502`/`E0503` errors while still
    // reordering raw-pointer accesses against references).
    for id_a in &idents_a {
        if borrow_ctx
            .transitive_roots(id_a)
            .iter()
            .any(|r| idents_b.contains(r))
        {
            return false;
        }
    }
    for id_b in &idents_b {
        if borrow_ctx
            .transitive_roots(id_b)
            .iter()
            .any(|r| idents_a.contains(r))
        {
            return false;
        }
    }

    // Never swap a by-value move (`let _moved = s;` / `drop(s);`) across
    // another statement mentioning `s` (`E0382` on `!Copy` ADTs).
    let moves_a = borrow_ctx.collect_potential_value_moves(&stmts[idx]);
    if moves_a.iter().any(|m| idents_b.contains(m)) {
        return false;
    }
    let moves_b = borrow_ctx.collect_potential_value_moves(&stmts[idx + 1]);
    if moves_b.iter().any(|m| idents_a.contains(m)) {
        return false;
    }

    true
}

struct AliasingAccessReorderer<'a> {
    rng: &'a mut DetRng,
}

struct ScopedBlockReorderer<'a, 'b> {
    rng: &'b mut DetRng,
    borrow_ctx: &'a SafeBorrowContext,
}

impl VisitMut for ScopedBlockReorderer<'_, '_> {
    fn visit_item_fn_mut(&mut self, func: &mut ItemFn) {
        AliasingAccessReorderer { rng: self.rng }.visit_item_fn_mut(func);
    }

    fn visit_block_mut(&mut self, block: &mut Block) {
        syn::visit_mut::visit_block_mut(self, block);
        if block.stmts.len() < 2 {
            return;
        }
        let mut idx = 0;
        while idx + 1 < block.stmts.len() {
            if can_swap_adjacent_stmts(&block.stmts, idx, self.borrow_ctx) && self.rng.coin(1, 2) {
                block.stmts.swap(idx, idx + 1);
                idx += 2;
            } else {
                idx += 1;
            }
        }
    }
}

impl VisitMut for AliasingAccessReorderer<'_> {
    fn visit_item_fn_mut(&mut self, func: &mut ItemFn) {
        let borrow_ctx = SafeBorrowContext::from_item_fn(func);
        ScopedBlockReorderer {
            rng: self.rng,
            borrow_ctx: &borrow_ctx,
        }
        .visit_block_mut(&mut func.block);
    }

    fn visit_block_mut(&mut self, block: &mut Block) {
        let borrow_ctx = SafeBorrowContext::from_block(block);
        ScopedBlockReorderer {
            rng: self.rng,
            borrow_ctx: &borrow_ctx,
        }
        .visit_block_mut(block);
    }
}

impl MiriAstMutator for TreeBorrowsRetagInterleaver {
    fn name(&self) -> &'static str {
        "TreeBorrowsRetagInterleaver"
    }

    fn mutate_with_mode(
        &self,
        file: &mut File,
        rng: &mut DetRng,
        mode: MutationMode,
        locals_log: &mut Vec<(String, String)>,
    ) {
        if matches!(
            mode,
            MutationMode::Pass | MutationMode::PerturbAst | MutationMode::Ub
        ) {
            let mut reorderer = AliasingAccessReorderer { rng };
            reorderer.visit_file_mut(file);
        }

        for item in &mut file.items {
            let Item::Fn(func) = item else { continue };
            if func.sig.ident == "helper_add_ten" {
                continue;
            }
            let locals = collect_initialized_locals(func);
            for loc in &locals {
                locals_log.push((loc.name.clone(), loc.ty.clone()));
            }
            let tag = rng.next_u64() & 0xFFFF;
            let probe_ident = format_ident!("__miri_tb_{tag}");
            let init_val: u32 = [10u32, 20u32, 30u32, 40u32][rng.gen_range(4)];
            let write_val: u32 = [1u32, 3u32, 7u32, 15u32][rng.gen_range(4)];

            let stmts: Vec<Stmt> = match mode {
                MutationMode::Pass => match rng.gen_range(4) {
                    // Reserved `&mut` coexisting with parent read before activation.
                    0 => syn::parse_quote! {
                        let mut __tb_slot: u32 = #init_val;
                        let __tb_root: *mut u32 = &raw mut __tb_slot;
                        let __tb_res: &mut u32 = unsafe { &mut *__tb_root };
                        let __tb_parent_read: u32 = unsafe { *__tb_root };
                        let #probe_ident: u32 = __tb_parent_read ^ (*__tb_res);
                    },
                    // `&raw const` and `&raw mut` pointers to disjoint fields,
                    // both derived from one `*mut PairU32`, coexist.
                    1 => syn::parse_quote! {
                        let mut __rr_pair: PairU32 = PairU32 { a: #init_val, b: #write_val };
                        let __rr_p: *mut PairU32 = &raw mut __rr_pair;
                        let __rr_a: *const u32 = unsafe { &raw const (*__rr_p).a };
                        let __rr_b: *mut u32 = unsafe { &raw mut (*__rr_p).b };
                        unsafe {
                            *__rr_b = (*__rr_b) ^ #init_val;
                        }
                        let #probe_ident: u32 = unsafe { (*__rr_a) ^ (*__rr_b) };
                    },
                    // `&raw const` field pointers derived from a frozen `&`
                    // coexist with reads through that reference.
                    2 => syn::parse_quote! {
                        let __rr_pair: PairU32 = PairU32 { a: #init_val, b: #write_val };
                        let __rr_shr: &PairU32 = &__rr_pair;
                        let __rr_ra: *const u32 = &raw const (*__rr_shr).a;
                        let __rr_rb: *const u32 = &raw const __rr_shr.b;
                        let #probe_ident: u32 = unsafe { (*__rr_ra) ^ (*__rr_rb) } ^ __rr_shr.a;
                    },
                    // `&raw mut` payload pointer derived from `&mut SingleC`
                    // writes the payload before the parent enum is matched.
                    _ => syn::parse_quote! {
                        let mut __rr_sc: SingleC = SingleC::Only(#init_val);
                        let __rr_sc_p: *mut u32 = match &mut __rr_sc {
                            SingleC::Only(__rr_inner) => &raw mut *__rr_inner,
                        };
                        unsafe {
                            *__rr_sc_p = (*__rr_sc_p) ^ #write_val;
                        }
                        let #probe_ident: u32 = match __rr_sc {
                            SingleC::Only(__rr_v) => __rr_v,
                        };
                    },
                },
                // Child write followed by parent read/write (legal in Tree
                // Borrows, exercises parent/child borrow-tree transitions).
                MutationMode::PerturbAst => match rng.gen_range(4) {
                    0 => syn::parse_quote! {
                        let mut __tb_slot: u32 = #init_val;
                        let __tb_root: *mut u32 = &raw mut __tb_slot;
                        let __tb_child: &mut u32 = unsafe { &mut *__tb_root };
                        *__tb_child = #write_val;
                        let #probe_ident: u32 = unsafe { *__tb_root };
                    },
                    1 => syn::parse_quote! {
                        let mut __tb_slot: u32 = #init_val;
                        let __tb_parent: &mut u32 = &mut __tb_slot;
                        {
                            let __tb_reborrow: &mut u32 = &mut *__tb_parent;
                            *__tb_reborrow = #write_val;
                        }
                        *__tb_parent = #init_val ^ #write_val;
                        let #probe_ident: u32 = *__tb_parent;
                    },
                    // A write through `&raw mut *m`, then a write and a read
                    // through the parent `&mut`.
                    2 => syn::parse_quote! {
                        let mut __rr_slot: u32 = #init_val;
                        let __rr_mut: &mut u32 = &mut __rr_slot;
                        let __rr_raw: *mut u32 = &raw mut *__rr_mut;
                        unsafe {
                            *__rr_raw = #write_val;
                        }
                        *__rr_mut = (*__rr_mut) ^ #init_val;
                        let #probe_ident: u32 = *__rr_mut;
                    },
                    // A write through `&raw mut (*m).b`, then parent reads of
                    // both fields.
                    _ => syn::parse_quote! {
                        let mut __rr_pair: PairU32 = PairU32 { a: #init_val, b: #write_val };
                        let __rr_fm: &mut PairU32 = &mut __rr_pair;
                        let __rr_fb: *mut u32 = &raw mut (*__rr_fm).b;
                        unsafe {
                            *__rr_fb = #init_val ^ #write_val;
                        }
                        let #probe_ident: u32 = __rr_fm.a ^ __rr_fm.b;
                    },
                },
                MutationMode::Panic => {
                    syn::parse_quote! {
                        let __tb_ovf: u32 = u32::MAX;
                        let #probe_ident: u32 = __tb_ovf + #write_val;
                    }
                }
                MutationMode::Ub => {
                    let variant = rng.gen_range(8);
                    match variant {
                        0 => syn::parse_quote! {
                            let __tb_imm: u32 = #init_val;
                            let __tb_shr: &u32 = &__tb_imm;
                            let __tb_mut: *mut u32 = (__tb_shr as *const u32) as *mut u32;
                            unsafe {
                                *__tb_mut = #write_val;
                            }
                            let #probe_ident: u32 = __tb_imm;
                        },
                        1 => syn::parse_quote! {
                            let mut __tb_x: u32 = #init_val;
                            let __tb_root: *mut u32 = &raw mut __tb_x;
                            let __tb_shr: &u32 = unsafe { &*__tb_root };
                            unsafe {
                                *__tb_root = #write_val;
                            }
                            let #probe_ident: u32 = *__tb_shr;
                        },
                        // Keep the activating write inside its own block so
                        // `AliasingAccessReorderer` cannot swap it after the
                        // parent read `let _ = unsafe { *__tb_root };` (which
                        // would leave `__tb_act` `Reserved` and erase the UB).
                        2 => syn::parse_quote! {
                            let mut __tb_x: u32 = #init_val;
                            let __tb_root: *mut u32 = &raw mut __tb_x;
                            let __tb_act: &mut u32 = unsafe { &mut *__tb_root };
                            {
                                *__tb_act = #write_val;
                            }
                            let _ = unsafe { *__tb_root };
                            *__tb_act = #init_val;
                            let #probe_ident: u32 = unsafe { *__tb_root };
                        },
                        // A write through the parent of the reborrow that
                        // `&raw mut *y` derives from disables the raw pointer.
                        // Each reference write sits in its own block so that
                        // `AliasingAccessReorderer` cannot swap them into a
                        // borrow-check error.
                        3 => syn::parse_quote! {
                            let mut __rr_slot: u32 = #init_val;
                            let __rr_x: &mut u32 = &mut __rr_slot;
                            let __rr_y: &mut u32 = &mut *__rr_x;
                            let __rr_r: *mut u32 = &raw mut *__rr_y;
                            {
                                *__rr_y = #write_val;
                            }
                            {
                                *__rr_x = #init_val ^ #write_val;
                            }
                            unsafe {
                                *__rr_r = #write_val;
                            }
                            let #probe_ident: u32 = __rr_slot;
                        },
                        // Writing through `&raw const` of a frozen `&` violates
                        // its read-only permission.
                        4 => syn::parse_quote! {
                            let mut __rr_slot: u32 = #init_val;
                            let __rr_frozen: &u32 = &__rr_slot;
                            let __rr_p: *mut u32 = (&raw const *__rr_frozen) as *mut u32;
                            unsafe {
                                *__rr_p = #write_val;
                            }
                            let #probe_ident: u32 = *__rr_frozen;
                        },
                        // A write to `.b` through `m` disables the reserved
                        // reborrow `m2` that `&raw mut (*m2).b` derives from.
                        5 => syn::parse_quote! {
                            let mut __rr_pair: PairU32 = PairU32 { a: #init_val, b: #write_val };
                            let __rr_m: &mut PairU32 = &mut __rr_pair;
                            let __rr_m2: &mut PairU32 = &mut *__rr_m;
                            let __rr_rb: *mut u32 = &raw mut (*__rr_m2).b;
                            __rr_m.b = #init_val;
                            unsafe {
                                *__rr_rb = #write_val;
                            }
                            let #probe_ident: u32 = __rr_pair.b;
                        },
                        // A write to `.a` through `m` disables the frozen
                        // reborrow `s` that `&raw const (*s).a` derives from.
                        6 => syn::parse_quote! {
                            let mut __rr_pair: PairU32 = PairU32 { a: #init_val, b: #write_val };
                            let __rr_m: &mut PairU32 = &mut __rr_pair;
                            let __rr_s: &PairU32 = &*__rr_m;
                            let __rr_ra: *const u32 = &raw const (*__rr_s).a;
                            __rr_m.a = #write_val;
                            let #probe_ident: u32 = unsafe { *__rr_ra };
                        },
                        // Whole-enum reinitialization (`Deinit` + aggregate
                        // write) through the parent `&mut SingleC` disables the
                        // child `&raw mut` payload pointer.
                        _ => syn::parse_quote! {
                            let mut __rr_sc: SingleC = SingleC::Only(#init_val);
                            let __rr_sc_m: &mut SingleC = &mut __rr_sc;
                            let __rr_sc_p: *mut u32 = match &mut *__rr_sc_m {
                                SingleC::Only(__rr_inner) => &raw mut *__rr_inner,
                            };
                            *__rr_sc_m = SingleC::Only(#init_val ^ #write_val);
                            unsafe {
                                *__rr_sc_p = #write_val;
                            }
                            let #probe_ident: u32 = match __rr_sc {
                                SingleC::Only(__rr_v) => __rr_v,
                            };
                        },
                    }
                }
            };
            inject_live_probe(func, stmts, &probe_ident);
        }
    }
}

/// 5. Exercises scalar bit-validity (`bool`, `char`, `ColorTag` discriminant,
///    the `NonZeroU32` niche, and the univariant `#[repr(C)]` `SingleC` tag),
///    niche-encoded `Option<NonZeroU32>`, `Option<bool>`, and
///    `Option<ColorTag>` values, the `#[repr(transparent)]` `MetersU32`
///    wrapper, `Uninit<T>` initialization state, and `OverlayU32` union
///    overlays via `core::mem::transmute`, `*mut` writes, and union field
///    reads.
///
/// Anneal's frozen layout lowering does not decode a niche-encoded value that
/// `transmute` produces unless it is the all-zero `None` of
/// `Option<NonZeroU32>`: transmuting a nonzero `u32` into `Option<NonZeroU32>`,
/// or a valid byte into `Option<bool>` or `Option<ColorTag>`, is a
/// false-positive UB. The templates therefore build those values with
/// constructors and transmute only the all-zero `Option<NonZeroU32>`. The
/// `*mut u32` write template targets only `MetersU32`: Anneal misses the UB of
/// copying a `NonZeroU32` after a zero is written through such a pointer, and
/// reports UB for any such write into a `SingleC`.
#[derive(Debug, Default, Clone, Copy)]
pub struct BitValidityTransmuteMutator;

/// The destination type of a `transmute` call, as far as
/// `TransmuteValidityPerturber` models its validity invariant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TransmuteTarget {
    Bool,
    Char,
    ColorTag,
    NonZeroU32,
    NonZeroMeters,
    MetersU32,
    /// `transmute::<[u32; 2], SingleC>([tag, payload])`, where only tag `0`
    /// is valid.
    SingleC,
    /// Niche-encoded `Option<...>` (where Anneal's frozen `trusted/` layout
    /// lowering reports false-positive UB on `transmute`) or any destination
    /// type without a modeled validity invariant.
    Unperturbed,
}

impl TransmuteTarget {
    fn of_type(ty: &Type) -> Self {
        match ty {
            Type::Paren(p) => Self::of_type(&p.elem),
            Type::Group(g) => Self::of_type(&g.elem),
            Type::Path(tp) if tp.qself.is_none() => {
                let Some(seg) = tp.path.segments.last() else {
                    return Self::Unperturbed;
                };
                if !matches!(seg.arguments, PathArguments::None) {
                    return Self::Unperturbed;
                }
                match seg.ident.to_string().as_str() {
                    "bool" => Self::Bool,
                    "char" => Self::Char,
                    "ColorTag" => Self::ColorTag,
                    "NonZeroU32" => Self::NonZeroU32,
                    "NonZeroMeters" => Self::NonZeroMeters,
                    "MetersU32" => Self::MetersU32,
                    "SingleC" => Self::SingleC,
                    _ => Self::Unperturbed,
                }
            }
            _ => Self::Unperturbed,
        }
    }

    /// Return the destination type that a `transmute::<Src, Dst>` turbofish
    /// explicitly names, or `None` if `call` has no turbofish or uses `_`
    /// (`Type::Infer`) for `Dst`.
    fn of_turbofish(call: &ExprCall) -> Option<Self> {
        let Expr::Path(ep) = &*call.func else {
            return None;
        };
        let PathArguments::AngleBracketed(args) = &ep.path.segments.last()?.arguments else {
            return None;
        };
        match args.args.iter().nth(1)? {
            GenericArgument::Type(Type::Infer(_)) => None,
            GenericArgument::Type(ty) => Some(Self::of_type(ty)),
            _ => None,
        }
    }
}

/// Whether `call` is a single-argument call to a function named `transmute`.
fn is_transmute_call(call: &ExprCall) -> bool {
    call.args.len() == 1
        && matches!(
            &*call.func,
            Expr::Path(ep) if ep.path.segments.last().is_some_and(|s| s.ident == "transmute")
        )
}

fn type_matches_primitive_name(mut ty: &Type, expected: &str) -> bool {
    loop {
        match ty {
            Type::Paren(p) => ty = &p.elem,
            Type::Group(g) => ty = &g.elem,
            _ => break,
        }
    }
    match ty {
        Type::Path(tp) if tp.qself.is_none() => tp
            .path
            .segments
            .last()
            .is_some_and(|s| matches!(s.arguments, PathArguments::None) && s.ident == expected),
        _ => false,
    }
}

/// Check whether a `transmute` call's first turbofish argument `Src` (when
/// present) is compatible with `expected_src` (`"u8"`, `"u32"`, or
/// `"[u32;2]"`).
///
/// Returns `None` when `call` has no turbofish arguments at all; `Some(true)`
/// when `Src` is `_` (`Type::Infer`) or matches `expected_src`; and
/// `Some(false)` when `Src` names an incompatible type such as `i8` or `i32`.
fn turbofish_src_compatible(call: &ExprCall, expected_src: &str) -> Option<bool> {
    let Expr::Path(ep) = &*call.func else {
        return None;
    };
    let PathArguments::AngleBracketed(args) = &ep.path.segments.last()?.arguments else {
        return None;
    };
    let mut ty = match args.args.first()? {
        GenericArgument::Type(Type::Infer(_)) => return Some(true),
        GenericArgument::Type(ty) => ty,
        _ => return Some(false),
    };
    loop {
        match ty {
            Type::Paren(p) => ty = &p.elem,
            Type::Group(g) => ty = &g.elem,
            _ => break,
        }
    }
    let ok = match expected_src {
        "[u32;2]" => match ty {
            Type::Array(arr) if type_matches_primitive_name(&arr.elem, "u32") => {
                match unwrap_expr_parens_and_groups(&arr.len) {
                    Expr::Lit(el) => match &el.lit {
                        Lit::Int(li) => li.base10_parse::<usize>().ok() == Some(2),
                        _ => false,
                    },
                    _ => false,
                }
            }
            _ => false,
        },
        prim => type_matches_primitive_name(ty, prim),
    };
    Some(ok)
}

/// Whether `expr` evaluates to at least one tail `transmute` call through
/// parentheses, groups, blocks, `unsafe` blocks, or `if`/`else` branches.
fn has_direct_transmute_call(expr: &Expr) -> bool {
    match expr {
        Expr::Call(call) => is_transmute_call(call),
        Expr::Paren(paren) => has_direct_transmute_call(&paren.expr),
        Expr::Group(group) => has_direct_transmute_call(&group.expr),
        Expr::Block(block_expr) => match block_expr.block.stmts.last() {
            Some(Stmt::Expr(inner, None)) => has_direct_transmute_call(inner),
            _ => false,
        },
        Expr::Unsafe(unsafe_expr) => match unsafe_expr.block.stmts.last() {
            Some(Stmt::Expr(inner, None)) => has_direct_transmute_call(inner),
            _ => false,
        },
        Expr::If(if_expr) => {
            let then_has = match if_expr.then_branch.stmts.last() {
                Some(Stmt::Expr(inner, None)) => has_direct_transmute_call(inner),
                _ => false,
            };
            let else_has = if_expr
                .else_branch
                .as_ref()
                .is_some_and(|(_, eb)| has_direct_transmute_call(eb));
            if_expr.else_branch.is_some() && (then_has || else_has)
        }
        _ => false,
    }
}

/// Return the tail `transmute` call that `expr` evaluates to, looking through
/// parentheses, groups, blocks, and `unsafe` blocks (even multi-statement
/// blocks whose final expression is `transmute(...)`).
fn direct_transmute_call_mut(expr: &mut Expr) -> Option<&mut ExprCall> {
    match expr {
        Expr::Call(call) if is_transmute_call(call) => Some(call),
        Expr::Paren(paren) => direct_transmute_call_mut(&mut paren.expr),
        Expr::Group(group) => direct_transmute_call_mut(&mut group.expr),
        Expr::Block(block_expr) => match block_expr.block.stmts.last_mut()? {
            Stmt::Expr(inner, None) => direct_transmute_call_mut(inner),
            _ => None,
        },
        Expr::Unsafe(unsafe_expr) => match unsafe_expr.block.stmts.last_mut()? {
            Stmt::Expr(inner, None) => direct_transmute_call_mut(inner),
            _ => None,
        },
        _ => None,
    }
}

struct TransmuteValidityPerturber<'a> {
    rng: &'a mut DetRng,
    inject_invalid: bool,
    fn_ret_target: Option<TransmuteTarget>,
}

impl TransmuteValidityPerturber<'_> {
    /// Return whether an integer literal with `suffix` is safe to replace with
    /// a suffixed `expected_src` literal (`"u8"` or `"u32"`).
    fn int_arg_compatible(call: &ExprCall, suffix: &str, expected_src: &str) -> bool {
        match turbofish_src_compatible(call, expected_src) {
            Some(true) => suffix.is_empty() || suffix == expected_src,
            Some(false) => false,
            None => suffix == expected_src,
        }
    }

    /// With probability 1/2, rewrite the integer literal argument of `call`
    /// (or the tag/payload literals of a `SingleC` array argument) to a value
    /// that is valid for `target`, or, if `inject_invalid` is set, to a value
    /// that violates `target`'s validity invariant.
    fn perturb_call(&mut self, call: &mut ExprCall, target: TransmuteTarget) {
        match target {
            TransmuteTarget::Unperturbed => {}
            TransmuteTarget::SingleC => {
                let turbofish_pair = turbofish_src_compatible(call, "[u32;2]");
                if turbofish_pair == Some(false) {
                    return;
                }
                if let Expr::Array(arr) = &mut call.args[0]
                    && arr.elems.len() == 2
                    && let Some(Expr::Lit(el)) = arr.elems.first()
                    && let Lit::Int(li) = &el.lit
                    && matches!(li.suffix(), "" | "u32")
                {
                    let elem1_u32 = matches!(
                        &arr.elems[1],
                        Expr::Lit(pel) if matches!(&pel.lit, Lit::Int(pli) if pli.suffix() == "u32")
                    );
                    let elem1_bad_suffix = matches!(
                        &arr.elems[1],
                        Expr::Lit(pel) if matches!(&pel.lit, Lit::Int(pli) if !matches!(pli.suffix(), "" | "u32"))
                    );
                    let array_typed_u32 = !elem1_bad_suffix
                        && (li.suffix() == "u32" || elem1_u32 || turbofish_pair == Some(true));
                    if !array_typed_u32 || !self.rng.coin(1, 2) {
                        return;
                    }
                    let tag: u32 = if self.inject_invalid {
                        [1u32, 2u32, 7u32, u32::MAX][self.rng.gen_range(4)]
                    } else {
                        0u32
                    };
                    arr.elems[0] = syn::parse_quote!(#tag);
                    if !self.inject_invalid
                        && let Expr::Lit(pel) = &arr.elems[1]
                        && let Lit::Int(pli) = &pel.lit
                        && matches!(pli.suffix(), "" | "u32")
                    {
                        let payload: u32 = [0u32, 5u32, 0x40u32, u32::MAX][self.rng.gen_range(4)];
                        arr.elems[1] = syn::parse_quote!(#payload);
                    }
                }
            }
            _ => {
                let Expr::Lit(el) = &call.args[0] else {
                    return;
                };
                let Lit::Int(li) = &el.lit else {
                    return;
                };
                let suffix = li.suffix().to_string();
                let invalid = self.inject_invalid;
                if matches!(target, TransmuteTarget::MetersU32) && invalid {
                    // Every `u32` is valid for `MetersU32`.
                    return;
                }
                let expected_src = match target {
                    TransmuteTarget::Bool | TransmuteTarget::ColorTag => "u8",
                    TransmuteTarget::NonZeroU32
                    | TransmuteTarget::NonZeroMeters
                    | TransmuteTarget::MetersU32
                    | TransmuteTarget::Char => "u32",
                    TransmuteTarget::SingleC | TransmuteTarget::Unperturbed => return,
                };
                if !Self::int_arg_compatible(call, &suffix, expected_src) {
                    return;
                }
                if !self.rng.coin(1, 2) {
                    return;
                }
                let replacement: Expr = match target {
                    TransmuteTarget::Bool => {
                        let v: u8 = if invalid {
                            [2u8, 3u8, 7u8, 255u8][self.rng.gen_range(4)]
                        } else {
                            self.rng.gen_range(2) as u8
                        };
                        syn::parse_quote!(#v)
                    }
                    TransmuteTarget::ColorTag => {
                        let v: u8 = if invalid {
                            [3u8, 5u8, 7u8, 255u8][self.rng.gen_range(4)]
                        } else {
                            self.rng.gen_range(3) as u8
                        };
                        syn::parse_quote!(#v)
                    }
                    TransmuteTarget::NonZeroU32 | TransmuteTarget::NonZeroMeters => {
                        let v: u32 = if invalid {
                            0u32
                        } else {
                            [1u32, 7u32, 0x41u32, u32::MAX][self.rng.gen_range(4)]
                        };
                        syn::parse_quote!(#v)
                    }
                    TransmuteTarget::MetersU32 => {
                        let v: u32 = [0u32, 1u32, 41u32, 0x7FFF_0000u32][self.rng.gen_range(4)];
                        syn::parse_quote!(#v)
                    }
                    TransmuteTarget::Char => {
                        let v: u32 = if invalid {
                            [0xD800u32, 0xDFFFu32, 0x11_0000u32, 0x1F_FFFFu32]
                                [self.rng.gen_range(4)]
                        } else {
                            [0x41u32, 0x7Au32, 0x03BBu32, 0x2603u32][self.rng.gen_range(4)]
                        };
                        syn::parse_quote!(#v)
                    }
                    TransmuteTarget::SingleC | TransmuteTarget::Unperturbed => return,
                };
                call.args[0] = replacement;
            }
        }
    }

    fn visit_non_tail_stmts(&mut self, expr: &mut Expr) {
        match expr {
            Expr::Paren(paren) => self.visit_non_tail_stmts(&mut paren.expr),
            Expr::Group(group) => self.visit_non_tail_stmts(&mut group.expr),
            Expr::Block(b) => {
                let n = b.block.stmts.len().saturating_sub(1);
                for stmt in &mut b.block.stmts[..n] {
                    self.visit_stmt_mut(stmt);
                }
                if let Some(Stmt::Expr(tail, None)) = b.block.stmts.last_mut() {
                    self.visit_non_tail_stmts(tail);
                }
            }
            Expr::Unsafe(u) => {
                let n = u.block.stmts.len().saturating_sub(1);
                for stmt in &mut u.block.stmts[..n] {
                    self.visit_stmt_mut(stmt);
                }
                if let Some(Stmt::Expr(tail, None)) = u.block.stmts.last_mut() {
                    self.visit_non_tail_stmts(tail);
                }
            }
            _ => {}
        }
    }

    fn visit_typed_tail_expr(&mut self, expr: &mut Expr, fallback_target: TransmuteTarget) -> bool {
        if !has_direct_transmute_call(expr) {
            return false;
        }
        match expr {
            Expr::Paren(p) => return self.visit_typed_tail_expr(&mut p.expr, fallback_target),
            Expr::Group(g) => return self.visit_typed_tail_expr(&mut g.expr, fallback_target),
            Expr::If(if_expr) if if_expr.else_branch.is_some() => {
                self.visit_expr_mut(&mut if_expr.cond);
                let n = if_expr.then_branch.stmts.len();
                let then_tail_transmute = if_expr
                    .then_branch
                    .stmts
                    .last()
                    .is_some_and(|s| matches!(s, Stmt::Expr(e, None) if has_direct_transmute_call(e)));
                if then_tail_transmute {
                    for stmt in &mut if_expr.then_branch.stmts[..n - 1] {
                        self.visit_stmt_mut(stmt);
                    }
                    if let Some(Stmt::Expr(tail, None)) = if_expr.then_branch.stmts.last_mut() {
                        self.visit_typed_tail_expr(tail, fallback_target);
                    }
                } else {
                    self.visit_block_mut(&mut if_expr.then_branch);
                }
                if let Some((_, eb)) = &mut if_expr.else_branch {
                    if !self.visit_typed_tail_expr(eb, fallback_target) {
                        self.visit_expr_mut(eb);
                    }
                }
                return true;
            }
            _ => {}
        }
        self.visit_non_tail_stmts(expr);
        if let Some(call) = direct_transmute_call_mut(expr) {
            let target = TransmuteTarget::of_turbofish(call).unwrap_or(fallback_target);
            for arg in call.args.iter_mut() {
                self.visit_expr_mut(arg);
            }
            self.perturb_call(call, target);
            return true;
        }
        false
    }
}

impl VisitMut for TransmuteValidityPerturber<'_> {
    fn visit_item_fn_mut(&mut self, func: &mut ItemFn) {
        let prev_ret = self.fn_ret_target;
        self.fn_ret_target = match &func.sig.output {
            ReturnType::Type(_, ret_ty) => Some(TransmuteTarget::of_type(ret_ty)),
            ReturnType::Default => None,
        };
        if let Some(ret_target) = self.fn_ret_target
            && func
                .block
                .stmts
                .last()
                .is_some_and(|s| matches!(s, Stmt::Expr(e, None) if has_direct_transmute_call(e)))
        {
            let n = func.block.stmts.len().saturating_sub(1);
            for stmt in &mut func.block.stmts[..n] {
                self.visit_stmt_mut(stmt);
            }
            if let Some(Stmt::Expr(tail_expr, None)) = func.block.stmts.last_mut() {
                self.visit_typed_tail_expr(tail_expr, ret_target);
            }
            self.fn_ret_target = prev_ret;
            return;
        }
        syn::visit_mut::visit_item_fn_mut(self, func);
        self.fn_ret_target = prev_ret;
    }

    fn visit_expr_closure_mut(&mut self, node: &mut syn::ExprClosure) {
        let prev_ret = self.fn_ret_target;
        self.fn_ret_target = match &node.output {
            ReturnType::Type(_, ret_ty) => Some(TransmuteTarget::of_type(ret_ty)),
            ReturnType::Default => None,
        };
        syn::visit_mut::visit_expr_closure_mut(self, node);
        self.fn_ret_target = prev_ret;
    }

    fn visit_expr_return_mut(&mut self, node: &mut syn::ExprReturn) {
        if let Some(ret_target) = self.fn_ret_target
            && let Some(ret_expr) = node.expr.as_mut()
            && self.visit_typed_tail_expr(ret_expr, ret_target)
        {
            return;
        }
        syn::visit_mut::visit_expr_return_mut(self, node);
    }

    fn visit_local_mut(&mut self, local: &mut Local) {
        // `let x: Dst = unsafe { transmute(lit) };` (or `transmute::<Src, _>`)
        // names its destination type in the `let` annotation. Check
        // `has_direct_transmute_call` first so non-tail statements in blocks
        // not ending in `transmute` are never visited twice.
        if let Some(pat_ty) = extract_outer_pat_type(&local.pat) {
            let let_target = TransmuteTarget::of_type(pat_ty);
            if let Some(init) = local.init.as_mut()
                && init.diverge.is_none()
                && self.visit_typed_tail_expr(&mut init.expr, let_target)
            {
                return;
            }
        }
        syn::visit_mut::visit_local_mut(self, local);
    }

    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        syn::visit_mut::visit_expr_mut(self, expr);
        if let Expr::Call(call) = expr
            && is_transmute_call(call)
        {
            let target =
                TransmuteTarget::of_turbofish(call).unwrap_or(TransmuteTarget::Unperturbed);
            self.perturb_call(call, target);
        }
    }
}

impl MiriAstMutator for BitValidityTransmuteMutator {
    fn name(&self) -> &'static str {
        "BitValidityTransmuteMutator"
    }

    fn mutate_with_mode(
        &self,
        file: &mut File,
        rng: &mut DetRng,
        mode: MutationMode,
        locals_log: &mut Vec<(String, String)>,
    ) {
        if matches!(
            mode,
            MutationMode::Pass | MutationMode::PerturbAst | MutationMode::Ub
        ) {
            let mut visitor = TransmuteValidityPerturber {
                rng,
                inject_invalid: mode == MutationMode::Ub,
                fn_ret_target: None,
            };
            visitor.visit_file_mut(file);
        }

        for item in &mut file.items {
            let Item::Fn(func) = item else { continue };
            if func.sig.ident == "helper_add_ten" {
                continue;
            }
            let locals = collect_initialized_locals(func);
            for loc in &locals {
                locals_log.push((loc.name.clone(), loc.ty.clone()));
            }
            let tag = rng.next_u64() & 0xFFFF;
            let probe_ident = format_ident!("__miri_valid_{tag}");

            let stmts: Vec<Stmt> = match mode {
                MutationMode::Pass | MutationMode::PerturbAst => {
                    let variant = rng.gen_range(10);
                    match variant {
                        0 => {
                            let b_u8: u8 = (rng.gen_range(2)) as u8;
                            let w_u32: u32 =
                                [0x41u32, 0x3BBu32, 0x7Fu32, 0x2Au32][rng.gen_range(4)];
                            syn::parse_quote! {
                                let __valid_b: bool = unsafe { transmute(#b_u8) };
                                let mut __valid_slot: Uninit<u32> = Uninit { uninit: () };
                                let #probe_ident: u32 = unsafe {
                                    __valid_slot.value = #w_u32;
                                    __valid_slot.value ^ (__valid_b as u32)
                                };
                            }
                        }
                        1 => {
                            let valid_char_u32: u32 =
                                [0x41u32, 0x7Au32, 0x03BBu32, 0x2603u32][rng.gen_range(4)];
                            syn::parse_quote! {
                                let __valid_ch: char = unsafe { transmute(#valid_char_u32) };
                                let #probe_ident: u32 = __valid_ch as u32;
                            }
                        }
                        2 => {
                            let valid_disc: u8 = (rng.gen_range(3)) as u8;
                            syn::parse_quote! {
                                let __valid_tag: ColorTag = unsafe { transmute(#valid_disc) };
                                let #probe_ident: u32 = match __valid_tag {
                                    ColorTag::Red => 10u32,
                                    ColorTag::Green => 20u32,
                                    ColorTag::Blue => 30u32,
                                };
                            }
                        }
                        3 => {
                            // The `NonZeroU32` niche: a nonzero `u32`
                            // round-trips.
                            let nz_u32: u32 = [1u32, 7u32, 0x41u32, u32::MAX][rng.gen_range(4)];
                            syn::parse_quote! {
                                let __valid_nz: NonZeroU32 = unsafe { transmute::<u32, NonZeroU32>(#nz_u32) };
                                let #probe_ident: u32 = unsafe { transmute::<NonZeroU32, u32>(__valid_nz) };
                            }
                        }
                        4 => {
                            // The `Option<NonZeroU32>` niche: the all-zero
                            // pattern decodes as `None`, and constructed
                            // `Some` and `None` values encode as their
                            // payload and `0`.
                            let some_u32: u32 =
                                [1u32, 9u32, 0x8000_0000u32, u32::MAX][rng.gen_range(4)];
                            let none_u32: u32 = [2u32, 5u32, 11u32, 23u32][rng.gen_range(4)];
                            syn::parse_quote! {
                                let __niche_zero: u32 = 0u32;
                                let __niche_none: Option<NonZeroU32> = unsafe { transmute::<u32, Option<NonZeroU32>>(__niche_zero) };
                                let __niche_nz: NonZeroU32 = unsafe { transmute::<u32, NonZeroU32>(#some_u32) };
                                let __niche_some: Option<NonZeroU32> = Some(__niche_nz);
                                let __niche_empty: Option<NonZeroU32> = None;
                                let __niche_a: u32 = match __niche_none {
                                    Some(__niche_inner) => unsafe { transmute::<NonZeroU32, u32>(__niche_inner) },
                                    None => #none_u32,
                                };
                                let __niche_b: u32 = unsafe { transmute::<Option<NonZeroU32>, u32>(__niche_some) };
                                let __niche_c: u32 = unsafe { transmute::<Option<NonZeroU32>, u32>(__niche_empty) };
                                let #probe_ident: u32 = __niche_a ^ __niche_b ^ __niche_c;
                            }
                        }
                        5 => {
                            // The `Option<bool>` and `Option<ColorTag>` niches,
                            // built by constructors and read back through their
                            // discriminants.
                            let opt_bool: Expr = match rng.gen_range(3) {
                                0 => syn::parse_quote!(Some(true)),
                                1 => syn::parse_quote!(Some(false)),
                                _ => syn::parse_quote!(None),
                            };
                            let opt_color: Expr = match rng.gen_range(4) {
                                0 => syn::parse_quote!(Some(ColorTag::Red)),
                                1 => syn::parse_quote!(Some(ColorTag::Green)),
                                2 => syn::parse_quote!(Some(ColorTag::Blue)),
                                _ => syn::parse_quote!(None),
                            };
                            syn::parse_quote! {
                                let __niche_ob: Option<bool> = #opt_bool;
                                let __niche_oc: Option<ColorTag> = #opt_color;
                                let __niche_x: u32 = match __niche_ob {
                                    Some(true) => 4u32,
                                    Some(false) => 8u32,
                                    None => 16u32,
                                };
                                let __niche_y: u32 = match __niche_oc {
                                    Some(ColorTag::Red) => 32u32,
                                    Some(ColorTag::Green) => 64u32,
                                    Some(ColorTag::Blue) => 128u32,
                                    None => 256u32,
                                };
                                let #probe_ident: u32 = __niche_x ^ __niche_y;
                            }
                        }
                        6 => {
                            // The `#[repr(transparent)]` wrapper: transmute
                            // in, write through `*mut u32` pointers to the
                            // field and to the whole wrapper, and transmute
                            // out.
                            let meters_u32: u32 =
                                [41u32, 0x7Fu32, 0x1234u32, 0xFFFF_FFF0u32][rng.gen_range(4)];
                            let mask_u32: u32 =
                                [5u32, 0x30u32, 0xFFu32, 0x0F0Fu32][rng.gen_range(4)];
                            syn::parse_quote! {
                                let mut __meters: MetersU32 = unsafe { transmute::<u32, MetersU32>(#meters_u32) };
                                let __meters_field: *mut u32 = &raw mut __meters.0;
                                unsafe {
                                    *__meters_field = (*__meters_field) ^ #mask_u32;
                                }
                                let __meters_whole: *mut u32 = (&raw mut __meters) as *mut u32;
                                unsafe {
                                    *__meters_whole = (*__meters_whole) | 1u32;
                                }
                                let #probe_ident: u32 = unsafe { transmute::<MetersU32, u32>(__meters) };
                            }
                        }
                        7 => {
                            // The univariant `#[repr(C)]` enum: transmute an
                            // image with the valid tag `0`, read its payload,
                            // and reinitialize the whole value.
                            let payload_u32: u32 =
                                [7u32, 0x40u32, 0x1234_5678u32, u32::MAX][rng.gen_range(4)];
                            syn::parse_quote! {
                                let mut __single: SingleC = unsafe { transmute::<[u32; 2], SingleC>([0u32, #payload_u32]) };
                                let __single_v: u32 = match __single {
                                    SingleC::Only(__single_inner) => __single_inner,
                                };
                                __single = SingleC::Only(__single_v ^ 0x55u32);
                                let #probe_ident: u32 = match __single {
                                    SingleC::Only(__single_out) => __single_out,
                                };
                            }
                        }
                        8 => {
                            // The union overlay: write one byte of `bytes`,
                            // then read `word` and a byte.
                            let word_u32: u32 =
                                [0x0403_0201u32, 0x11u32, 0xA5A5_A5A5u32, 0u32][rng.gen_range(4)];
                            let byte_u8: u8 = [9u8, 0x80u8, 0xFFu8, 0u8][rng.gen_range(4)];
                            let write_idx: usize = rng.gen_range(4);
                            let read_idx: usize = rng.gen_range(4);
                            syn::parse_quote! {
                                let mut __overlay: OverlayU32 = OverlayU32 { word: #word_u32 };
                                let #probe_ident: u32 = unsafe {
                                    __overlay.bytes[#write_idx] = #byte_u8;
                                    __overlay.word ^ (__overlay.bytes[#read_idx] as u32)
                                };
                            }
                        }
                        _ => {
                            // The `#[repr(transparent)]` niche wrapper over
                            // `NonZeroU32`: a nonzero `u32` transmutes in,
                            // projects `.0`, and round-trips out.
                            let nz_u32: u32 = [1u32, 9u32, 0x1234u32, u32::MAX][rng.gen_range(4)];
                            syn::parse_quote! {
                                let __valid_nzm: NonZeroMeters = unsafe { transmute::<u32, NonZeroMeters>(#nz_u32) };
                                let #probe_ident: u32 = unsafe { transmute::<NonZeroU32, u32>(__valid_nzm.0) };
                            }
                        }
                    }
                }
                MutationMode::Panic => {
                    syn::parse_quote! {
                        let __panic_arr: [u8; 2] = [0u8, 1u8];
                        let __panic_idx: usize = 3usize;
                        let #probe_ident: u32 = __panic_arr[__panic_idx] as u32;
                    }
                }
                MutationMode::Ub => {
                    let bad_u8: u8 = [2u8, 3u8, 7u8, 255u8][rng.gen_range(4)];
                    let bad_char_u32: u32 =
                        [0xD800u32, 0xDFFFu32, 0x11_0000u32, 0x1F_FFFFu32][rng.gen_range(4)];
                    let bad_enum_u8: u8 = [3u8, 5u8, 7u8, 255u8][rng.gen_range(4)];
                    let variant = rng.gen_range(10);
                    match variant {
                        0 => syn::parse_quote! {
                            let __bad_b_raw: u8 = #bad_u8;
                            let __bad_b: bool = unsafe { transmute(__bad_b_raw) };
                            let #probe_ident: u32 = __bad_b as u32;
                        },
                        1 => syn::parse_quote! {
                            let __bad_ch_raw: u32 = #bad_char_u32;
                            let __bad_ch: char = unsafe { transmute(__bad_ch_raw) };
                            let #probe_ident: u32 = __bad_ch as u32;
                        },
                        2 => syn::parse_quote! {
                            let __bad_tag_raw: u8 = #bad_enum_u8;
                            let __bad_tag: ColorTag = unsafe { transmute(__bad_tag_raw) };
                            let #probe_ident: u32 = match __bad_tag {
                                ColorTag::Red => 1u32,
                                ColorTag::Green => 2u32,
                                ColorTag::Blue => 3u32,
                            };
                        },
                        3 => syn::parse_quote! {
                            let __uninit_slot: Uninit<u32> = Uninit { uninit: () };
                            let #probe_ident: u32 = unsafe { __uninit_slot.value };
                        },
                        4 => syn::parse_quote! {
                            let __padded: PaddedU8U32 = PaddedU8U32 { tag: 1u8, word: 0x1122_3344u32 };
                            let __pad_bytes: [u8; 8] = unsafe { transmute(__padded) };
                            let __pad_idx: usize = 1usize;
                            let #probe_ident: u32 = __pad_bytes[__pad_idx] as u32;
                        },
                        5 => syn::parse_quote! {
                            let mut __ptr_b: bool = false;
                            let __raw_u8: *mut u8 = (&mut __ptr_b as *mut bool) as *mut u8;
                            unsafe {
                                *__raw_u8 = #bad_u8;
                            }
                            let #probe_ident: u32 = __ptr_b as u32;
                        },
                        // The all-zero pattern violates the `NonZeroU32`
                        // niche. The zero reaches `transmute` through a
                        // local so that a later
                        // `TransmuteValidityPerturber` pass cannot rewrite
                        // it.
                        6 => syn::parse_quote! {
                            let __nz_zero: u32 = 0u32;
                            let __bad_nz: NonZeroU32 = unsafe { transmute::<u32, NonZeroU32>(__nz_zero) };
                            let #probe_ident: u32 = unsafe { transmute::<NonZeroU32, u32>(__bad_nz) };
                        },
                        // Only tag `0` names `SingleC::Only`.
                        7 => {
                            let bad_tag_u32: u32 = [1u32, 2u32, 7u32, u32::MAX][rng.gen_range(4)];
                            let payload_u32: u32 =
                                [3u32, 0x40u32, 0xFFFFu32, 0u32][rng.gen_range(4)];
                            syn::parse_quote! {
                                let __bad_single_raw: [u32; 2] = [#bad_tag_u32, #payload_u32];
                                let __bad_single: SingleC = unsafe { transmute::<[u32; 2], SingleC>(__bad_single_raw) };
                                let #probe_ident: u32 = match __bad_single {
                                    SingleC::Only(__bad_inner) => __bad_inner,
                                };
                            }
                        }
                        // After one byte of an uninitialized `[u8; 4]` union
                        // field is written, reading another byte reads
                        // uninitialized memory.
                        8 => {
                            let write_idx: usize = rng.gen_range(4);
                            let read_idx: usize = (write_idx + 1 + rng.gen_range(3)) % 4;
                            let byte_u8: u8 = [3u8, 0x7Fu8, 0x80u8, 0xFFu8][rng.gen_range(4)];
                            syn::parse_quote! {
                                let mut __part_slot: Uninit<[u8; 4]> = Uninit { uninit: () };
                                let __part_read: usize = #read_idx;
                                let #probe_ident: u32 = unsafe {
                                    __part_slot.value[#write_idx] = #byte_u8;
                                    __part_slot.value[__part_read] as u32
                                };
                            }
                        }
                        // Transmuting `0` into `NonZeroMeters` violates its
                        // inner `NonZeroU32` valid range.
                        _ => syn::parse_quote! {
                            let __nzm_zero: u32 = 0u32;
                            let __bad_nzm: NonZeroMeters = unsafe { transmute::<u32, NonZeroMeters>(__nzm_zero) };
                            let #probe_ident: u32 = unsafe { transmute::<NonZeroU32, u32>(__bad_nzm.0) };
                        },
                    }
                }
            };
            inject_live_probe(func, stmts, &probe_ident);
        }
    }
}

/// Generate the 89-candidate identity batch directly from
/// `tests/miri-diff/corpus/src/lib.rs` with zero mutations applied.
pub fn generate_miri_identity_batch() -> Vec<GeneratedMiriCandidate> {
    let seeds = load_miri_diff_corpus_seeds();
    seeds
        .into_iter()
        .enumerate()
        .map(|(id, seed)| {
            let parsed = syn::parse_file(&seed.fn_source).expect("parse corpus seed");
            let mut tracked_locals = Vec::new();
            for item in &parsed.items {
                if let Item::Fn(func) = item {
                    for loc in collect_initialized_locals(func) {
                        let pair = (loc.name, loc.ty);
                        if !tracked_locals.contains(&pair) {
                            tracked_locals.push(pair);
                        }
                    }
                }
            }
            let source = build_standalone_candidate_source(&seed.fn_source);
            GeneratedMiriCandidate {
                id,
                seed_index: id,
                seed_name: seed.name.clone(),
                fn_name: seed.name,
                seed_u64: id as u64,
                applied_mutators: Vec::new(),
                tracked_locals,
                fn_source: seed.fn_source,
                source,
            }
        })
        .collect()
}

/// Generate `count` deterministic, closed, zero-argument Miri candidates from
/// the 89-function `tests/miri-diff/corpus/src/lib.rs` seed corpus.
pub fn generate_miri_corpus_batch(
    count: usize,
    seed_u64: u64,
    batch_idx: usize,
) -> Vec<GeneratedMiriCandidate> {
    let corpus_seeds = load_miri_diff_corpus_seeds();
    let raw_refs: Vec<&str> = corpus_seeds.iter().map(|s| s.fn_source.as_str()).collect();
    generate_miri_batch_with_prefix(&raw_refs, count, seed_u64, &format!("b{batch_idx}"))
}

/// Generates `count` deterministic, syntactically valid Miri-strength mutated
/// Rust programs from `seeds` using a PRNG keyed by `seed_u64`.
pub fn generate_miri_batch(
    seeds: &[&str],
    count: usize,
    seed_u64: u64,
) -> Vec<GeneratedMiriCandidate> {
    generate_miri_batch_with_prefix(seeds, count, seed_u64, "m")
}

/// Return the indices of non-faulting seeds (`pass_*`, `tb_*`, `safe_*` or
/// user-provided seeds) that do not invoke unmodeled external calls.
///
/// Crucially, this list includes ALL Miri-passing seeds in
/// `tests/miri-diff/corpus/src/lib.rs`—including both agreeing Tree Borrows
/// parent/child seeds (`tb_child_write_then_parent_read`,
/// `tb_child_write_then_parent_write`, `safe_reborrow_then_parent_write`) and
/// seeds with `known_anneal_bug` divergences (`pass_ptr_offset_within_array`,
/// `pass_copy_nonoverlapping_uninit_bytes_to_uninit`,
/// `pass_tb_unsafe_cell_shared_mutation`).
pub fn collect_non_fault_seed_indices(seeds: &[&str]) -> Vec<usize> {
    seeds
        .iter()
        .enumerate()
        .filter_map(|(idx, src)| {
            let parsed = syn::parse_str::<File>(src).ok()?;
            let fn_name = parsed.items.iter().find_map(|it| match it {
                Item::Fn(f) if f.sig.ident != "helper_add_ten" => Some(f.sig.ident.to_string()),
                _ => None,
            })?;
            if !fn_name.starts_with("panic_") && !fn_name.starts_with("ub_") {
                Some(idx)
            } else {
                None
            }
        })
        .collect()
}

fn generate_miri_batch_with_prefix(
    seeds: &[&str],
    count: usize,
    seed_u64: u64,
    batch_prefix: &str,
) -> Vec<GeneratedMiriCandidate> {
    if seeds.is_empty() || count == 0 {
        return Vec::new();
    }

    let all_mutators: [&dyn MiriAstMutator; 5] = [
        &ArithmeticCastMutator,
        &PlaceProjectionWrapper,
        &RawPtrOffsetMutator,
        &TreeBorrowsRetagInterleaver,
        &BitValidityTransmuteMutator,
    ];

    let non_fault_seed_indices = collect_non_fault_seed_indices(seeds);

    let mut master_rng = DetRng::new(seed_u64);
    let seed_offset = master_rng.gen_range(seeds.len());
    let mut out = Vec::with_capacity(count);

    for id in 0..count {
        let cand_seed = master_rng.next_u64() ^ ((id as u64).wrapping_mul(0x517C_C1B7_2722_0A95));
        let mut cand_rng = DetRng::new(cand_seed);

        // Choose the candidate's target mutation regime so every batch produces
        // a balanced, seed-dependent mix of `pass`, `panic`, and `ub` outcomes.
        let bucket = (id + cand_rng.gen_range(4)) % 4;
        let primary_mode = match bucket {
            0 => MutationMode::Pass,
            1 => MutationMode::Panic,
            2 => MutationMode::Ub,
            _ => match cand_rng.gen_range(4) {
                0 => MutationMode::Pass,
                1 => MutationMode::Panic,
                2 => MutationMode::Ub,
                _ => MutationMode::PerturbAst,
            },
        };

        let seed_index = if (primary_mode == MutationMode::Pass
            || primary_mode == MutationMode::Panic
            || (primary_mode == MutationMode::Ub && cand_rng.coin(1, 2)))
            && !non_fault_seed_indices.is_empty()
        {
            let pick = (seed_offset
                + id.wrapping_mul(7)
                + cand_rng.gen_range(non_fault_seed_indices.len()))
                % non_fault_seed_indices.len();
            non_fault_seed_indices[pick]
        } else if seeds.len() <= 8 {
            (id + seed_offset) % seeds.len()
        } else {
            (seed_offset + id.wrapping_mul(13) + cand_rng.gen_range(seeds.len())) % seeds.len()
        };

        let Ok(mut parsed) = syn::parse_str::<File>(seeds[seed_index]) else {
            continue;
        };

        // Close and rename the last function item in `parsed.items` (leaving
        // any preceding helper functions in a multi-function seed intact).
        let mut seed_name = format!("seed_{seed_index}");
        let mut fn_name = format!("cand_{batch_prefix}_c{id}");
        parsed.attrs.clear();
        parsed.items.retain(|item| {
            if let Item::Fn(f) = item {
                f.sig.ident != "helper_add_ten"
            } else {
                false
            }
        });
        if let Some(Item::Fn(func)) = parsed.items.last_mut() {
            seed_name = func.sig.ident.to_string();
            fn_name = format!("{seed_name}__{batch_prefix}_c{id}");
            func.sig.ident = format_ident!("{}", fn_name);
            close_and_normalize_function(func, &mut cand_rng);
        }

        // If the selected seed is already a faulting (`panic_*` or `ub_*`) seed,
        // mutate it in-place (`PerturbAst` / `Pass`) rather than appending a
        // second fault probe after the seed's own panic/UB.
        let seed_already_faults =
            seed_name.starts_with("panic_") || seed_name.starts_with("ub_");

        let num_passes = 1 + cand_rng.gen_range(3);
        let mut applied_mutators = Vec::with_capacity(num_passes);
        let mut raw_locals = Vec::new();

        for pass in 0..num_passes {
            let m_idx = if pass == 0 {
                (id + cand_rng.gen_range(all_mutators.len())) % all_mutators.len()
            } else {
                cand_rng.gen_range(all_mutators.len())
            };
            let pass_mode = if pass == 0 && !seed_already_faults {
                primary_mode
            } else if pass == 0 && seed_already_faults {
                MutationMode::PerturbAst
            } else {
                MutationMode::Pass
            };
            let mutator = all_mutators[m_idx];
            mutator.mutate_with_mode(&mut parsed, &mut cand_rng, pass_mode, &mut raw_locals);
            applied_mutators.push(mutator.name().to_string());
        }

        for item in &parsed.items {
            if let Item::Fn(func) = item {
                for loc in collect_initialized_locals(func) {
                    raw_locals.push((loc.name, loc.ty));
                }
            }
        }

        let mut tracked_locals = Vec::new();
        for pair in raw_locals {
            if !tracked_locals.contains(&pair) {
                tracked_locals.push(pair);
            }
        }

        let fn_source = prettyplease::unparse(&parsed);
        let source = build_standalone_candidate_source(&fn_source);
        out.push(GeneratedMiriCandidate {
            id,
            seed_index,
            seed_name,
            fn_name,
            seed_u64: cand_seed,
            applied_mutators,
            tracked_locals,
            fn_source,
            source,
        });
    }

    out
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::*;

    #[test]
    fn corpus_seeds_load_all_89_zero_arg_functions_and_do_not_blocklist_known_bugs() {
        let seeds = load_miri_diff_corpus_seeds();
        assert_eq!(
            seeds.len(),
            89,
            "expected 89 zero-arg functions from tests/miri-diff/corpus/src/lib.rs"
        );
        assert!(seeds.iter().any(|s| s.name == "pass_integer_arith_basic"));
        assert!(
            seeds
                .iter()
                .any(|s| s.name == "ub_tb_use_frozen_mut_after_parent_read")
        );
        assert!(
            seeds
                .iter()
                .any(|s| s.name == "tb_child_write_then_parent_read")
        );
        assert!(
            seeds
                .iter()
                .any(|s| s.name == "ub_transparent_nonzero_wrapper_zero")
        );
        assert!(
            seeds
                .iter()
                .any(|s| s.name == "pass_option_some_niche_and_single_c_mut")
        );
        assert!(!seeds.iter().any(|s| s.name == "helper_add_ten"));

        let raw_refs: Vec<&str> = seeds.iter().map(|s| s.fn_source.as_str()).collect();
        let non_fault_indices = collect_non_fault_seed_indices(&raw_refs);
        let non_fault_names: std::collections::BTreeSet<&str> = non_fault_indices
            .iter()
            .map(|&idx| seeds[idx].name.as_str())
            .collect();
        for known_bug_seed in [
            "pass_direct_fn_call",
            "pass_exact_div_valid",
            "pass_ptr_offset_within_array",
            "pass_copy_nonoverlapping_uninit_bytes_to_uninit",
            "pass_tb_unsafe_cell_shared_mutation",
            "tb_child_write_then_parent_read",
            "tb_child_write_then_parent_write",
            "safe_reborrow_then_parent_write",
        ] {
            assert!(
                non_fault_names.contains(known_bug_seed),
                "non_fault_seed_indices must include `{known_bug_seed}` without blocklisting"
            );
        }
    }

    #[test]
    fn generate_miri_batch_is_deterministic_closed_and_free_of_black_box() {
        let batch1 = generate_miri_corpus_batch(20, 0xCAFE_BABE_1234_5678, 0);
        let batch2 = generate_miri_corpus_batch(20, 0xCAFE_BABE_1234_5678, 0);
        assert_eq!(
            batch1, batch2,
            "same seed_u64 must produce bit-identical batch"
        );
        assert_eq!(batch1.len(), 20);

        let other_seed = generate_miri_corpus_batch(20, 0xDEAD_BEEF_0000_0001, 0);
        assert_ne!(
            batch1, other_seed,
            "different seeds must produce distinct candidate batches"
        );

        let mut seen_mutators = std::collections::BTreeSet::new();
        for cand in &batch1 {
            assert!(!cand.tracked_locals.is_empty());
            assert!(
                !cand.fn_source.contains("black_box"),
                "candidate must not emit dead-code black_box:\n{}",
                cand.fn_source
            );
            for m in &cand.applied_mutators {
                seen_mutators.insert(m.as_str());
            }
            assert!(
                syn::parse_file(&cand.source).is_ok(),
                "generated candidate {} failed syn::parse_file:\n{}",
                cand.id,
                cand.source
            );
        }

        for expected in [
            "ArithmeticCastMutator",
            "PlaceProjectionWrapper",
            "RawPtrOffsetMutator",
            "TreeBorrowsRetagInterleaver",
            "BitValidityTransmuteMutator",
        ] {
            assert!(
                seen_mutators.contains(expected),
                "expected mutator `{expected}` to appear in batch"
            );
        }
    }

    #[test]
    fn semantic_mutators_perform_cast_swaps_char_enum_transmutes_index_and_aliasing_reorder() {
        // 1. Cast swaps in ArithAstPerturber
        let cast_seed = "pub fn cast_fn() -> i32 { let x: i8 = -5i8; (x as i32) }\n";
        let mut saw_cast_swap = false;
        for s in 0..16u64 {
            let mut f = syn::parse_file(cast_seed).unwrap();
            let mut rng = DetRng::new(s);
            let mut locals = Vec::new();
            ArithmeticCastMutator.mutate_with_mode(
                &mut f,
                &mut rng,
                MutationMode::PerturbAst,
                &mut locals,
            );
            let out = prettyplease::unparse(&f);
            if out.contains("as i32") && (out.contains("as u") || out.contains("as i16") || out.contains("as i64") || out.contains("as isize")) {
                saw_cast_swap = true;
                break;
            }
        }
        assert!(saw_cast_swap, "ArithmeticCastMutator must perform Expr::Cast swaps");

        // 2. Invalid char and ColorTag enum transmutes in BitValidityTransmuteMutator
        let base_seed = "pub fn val_fn() -> u32 { 1u32 }\n";
        let mut saw_char_ub = false;
        let mut saw_enum_ub = false;
        for s in 0..128u64 {
            let mut f = syn::parse_file(base_seed).unwrap();
            let mut rng = DetRng::new(s);
            let mut locals = Vec::new();
            BitValidityTransmuteMutator.mutate_with_mode(
                &mut f,
                &mut rng,
                MutationMode::Ub,
                &mut locals,
            );
            let out = prettyplease::unparse(&f);
            if out.contains("__bad_ch: char = unsafe { transmute") {
                saw_char_ub = true;
            }
            if out.contains("__bad_tag: ColorTag = unsafe { transmute") {
                saw_enum_ub = true;
            }
        }
        assert!(saw_char_ub, "BitValidityTransmuteMutator must emit invalid char transmutes");
        assert!(saw_enum_ub, "BitValidityTransmuteMutator must emit invalid ColorTag transmutes");

        // 3. Array index perturbation in PlaceProjectionWrapper
        let idx_seed = "pub fn idx_fn() -> u32 { let arr: [u32; 4] = [1, 2, 3, 4]; arr[0] }\n";
        let mut saw_idx_perturb = false;
        for s in 0..16u64 {
            let mut f = syn::parse_file(idx_seed).unwrap();
            let mut rng = DetRng::new(s);
            let mut locals = Vec::new();
            PlaceProjectionWrapper.mutate_with_mode(
                &mut f,
                &mut rng,
                MutationMode::Pass,
                &mut locals,
            );
            let out = prettyplease::unparse(&f);
            if out.contains("arr[1usize]") || out.contains("arr[1]") {
                saw_idx_perturb = true;
                break;
            }
        }
        assert!(saw_idx_perturb, "PlaceProjectionWrapper must perturb Expr::Index in place");

        // 4. Aliasing statement reordering in TreeBorrowsRetagInterleaver
        let tb_seed = "\
pub fn tb_fn() -> u32 {
    let mut x: u32 = 1;
    let p1: *mut u32 = &raw mut x;
    let r2: &mut u32 = unsafe { &mut *p1 };
    *r2 = 2;
    let _y = unsafe { *p1 };
    *r2
}
";
        let mut saw_reorder = false;
        for s in 0..16u64 {
            let mut f = syn::parse_file(tb_seed).unwrap();
            let mut rng = DetRng::new(s);
            let mut locals = Vec::new();
            TreeBorrowsRetagInterleaver.mutate_with_mode(
                &mut f,
                &mut rng,
                MutationMode::PerturbAst,
                &mut locals,
            );
            let out = prettyplease::unparse(&f);
            let pos_read = out.find("let _y = unsafe { *p1 };").expect("read stmt");
            let pos_write = out.find("*r2 = 2;").expect("write stmt");
            if pos_read < pos_write {
                saw_reorder = true;
                break;
            }
        }
        assert!(
            saw_reorder,
            "TreeBorrowsRetagInterleaver must reorder adjacent aliasing access statements"
        );
    }

    /// Return the source of `seed` after `mutator` runs in `mode` under the
    /// first `DetRng` seed in `0..512` whose output contains `marker`.
    fn first_output_containing(
        seed: &str,
        mutator: &dyn MiriAstMutator,
        mode: MutationMode,
        marker: &str,
    ) -> Option<String> {
        (0..512u64).find_map(|s| {
            let mut f = syn::parse_file(seed).unwrap();
            let mut rng = DetRng::new(s);
            let mut locals = Vec::new();
            mutator.mutate_with_mode(&mut f, &mut rng, mode, &mut locals);
            let out = prettyplease::unparse(&f);
            out.contains(marker).then_some(out)
        })
    }

    #[test]
    fn niche_single_c_union_and_raw_retag_templates_fire_in_every_mode() {
        let seed = "pub fn ep2_fn() -> u32 {\n    let base: u32 = 6u32;\n    base\n}\n";
        let cases: [(&dyn MiriAstMutator, MutationMode, &str); 29] = [
            (
                &BitValidityTransmuteMutator,
                MutationMode::Pass,
                "transmute::<u32, NonZeroU32>",
            ),
            (
                &BitValidityTransmuteMutator,
                MutationMode::PerturbAst,
                "transmute::<u32, Option<NonZeroU32>>(__niche_zero)",
            ),
            (
                &BitValidityTransmuteMutator,
                MutationMode::Pass,
                "__niche_ob: Option<bool>",
            ),
            (
                &BitValidityTransmuteMutator,
                MutationMode::PerturbAst,
                "let __meters_field: *mut u32 = &raw mut __meters.0;",
            ),
            (
                &BitValidityTransmuteMutator,
                MutationMode::Pass,
                "transmute::<[u32; 2], SingleC>([0u32,",
            ),
            (
                &BitValidityTransmuteMutator,
                MutationMode::PerturbAst,
                "__overlay: OverlayU32",
            ),
            (
                &BitValidityTransmuteMutator,
                MutationMode::Pass,
                "transmute::<u32, NonZeroMeters>",
            ),
            (
                &BitValidityTransmuteMutator,
                MutationMode::Ub,
                "transmute::<u32, NonZeroU32>(__nz_zero)",
            ),
            (
                &BitValidityTransmuteMutator,
                MutationMode::Ub,
                "transmute::<[u32; 2], SingleC>(__bad_single_raw)",
            ),
            (
                &BitValidityTransmuteMutator,
                MutationMode::Ub,
                "__part_slot: Uninit<[u8; 4]>",
            ),
            (
                &BitValidityTransmuteMutator,
                MutationMode::Ub,
                "transmute::<u32, NonZeroMeters>(__nzm_zero)",
            ),
            (
                &PlaceProjectionWrapper,
                MutationMode::Pass,
                "__proj_single_ref: &mut SingleC",
            ),
            (
                &PlaceProjectionWrapper,
                MutationMode::PerturbAst,
                "&raw mut __proj_overlay.bytes",
            ),
            (
                &PlaceProjectionWrapper,
                MutationMode::Pass,
                "__proj_slot: Uninit<[u32; 2]>",
            ),
            (
                &PlaceProjectionWrapper,
                MutationMode::PerturbAst,
                "&raw const __proj_nzm.0",
            ),
            (
                &PlaceProjectionWrapper,
                MutationMode::Ub,
                "&raw const __dead_pair.b",
            ),
            (
                &PlaceProjectionWrapper,
                MutationMode::Ub,
                "__dead_inner as *const u32",
            ),
            (
                &PlaceProjectionWrapper,
                MutationMode::Ub,
                "__proj_half: Uninit<[u32; 2]>",
            ),
            (
                &PlaceProjectionWrapper,
                MutationMode::Ub,
                "&raw const __dead_ov.word",
            ),
            (
                &TreeBorrowsRetagInterleaver,
                MutationMode::Pass,
                "&raw mut (*__rr_p).b",
            ),
            (
                &TreeBorrowsRetagInterleaver,
                MutationMode::Pass,
                "&raw const (*__rr_shr).a",
            ),
            (
                &TreeBorrowsRetagInterleaver,
                MutationMode::Pass,
                "let __rr_sc_p: *mut u32 = match &mut __rr_sc",
            ),
            (
                &TreeBorrowsRetagInterleaver,
                MutationMode::PerturbAst,
                "&raw mut *__rr_mut",
            ),
            (
                &TreeBorrowsRetagInterleaver,
                MutationMode::PerturbAst,
                "&raw mut (*__rr_fm).b",
            ),
            (
                &TreeBorrowsRetagInterleaver,
                MutationMode::Ub,
                "&raw mut *__rr_y",
            ),
            (
                &TreeBorrowsRetagInterleaver,
                MutationMode::Ub,
                "&raw const *__rr_frozen",
            ),
            (
                &TreeBorrowsRetagInterleaver,
                MutationMode::Ub,
                "&raw mut (*__rr_m2).b",
            ),
            (
                &TreeBorrowsRetagInterleaver,
                MutationMode::Ub,
                "&raw const (*__rr_s).a",
            ),
            (
                &TreeBorrowsRetagInterleaver,
                MutationMode::Ub,
                "*__rr_sc_m = SingleC::Only",
            ),
        ];
        for (mutator, mode, marker) in cases {
            let out = first_output_containing(seed, mutator, mode, marker).unwrap_or_else(|| {
                panic!(
                    "{} never emitted `{marker}` in {mode:?} mode",
                    mutator.name()
                )
            });
            let source = build_standalone_candidate_source(&out);
            assert!(
                syn::parse_file(&source).is_ok(),
                "candidate failed syn::parse_file:\n{source}"
            );
            for banned in ["black_box", "::new(", ".unwrap()"] {
                assert!(
                    !out.contains(banned),
                    "{} emitted `{banned}` for `{marker}`:\n{out}",
                    mutator.name()
                );
            }
            // The seed body still runs before the injected template.
            assert!(
                out.contains("let base: u32 = 6u32;"),
                "seed body was dropped:\n{out}"
            );
        }

        // `Pass`/`PerturbAst` never emit the `Ub`-only invalid images.
        for s in 0..512u64 {
            for mode in [MutationMode::Pass, MutationMode::PerturbAst] {
                let mut f = syn::parse_file(seed).unwrap();
                let mut rng = DetRng::new(s);
                BitValidityTransmuteMutator.mutate_with_mode(
                    &mut f,
                    &mut rng,
                    mode,
                    &mut Vec::new(),
                );
                let out = prettyplease::unparse(&f);
                assert!(
                    !out.contains("__bad_"),
                    "{mode:?} emitted an invalid image:\n{out}"
                );
            }
        }
    }

    /// Return the integer value of the literal `expr`, or of the first element
    /// of the array literal `expr`.
    fn literal_or_first_element_value(expr: &Expr) -> u64 {
        match expr {
            Expr::Lit(el) => match &el.lit {
                Lit::Int(li) => li.base10_parse::<u64>().unwrap(),
                other => panic!("unexpected literal {}", other.to_token_stream()),
            },
            Expr::Array(arr) => literal_or_first_element_value(&arr.elems[0]),
            other => panic!("unexpected transmute argument {}", other.to_token_stream()),
        }
    }

    #[test]
    fn transmute_validity_perturber_respects_each_destination_type() {
        let seed = "\
pub fn transmute_targets() -> u32 {
    let b: bool = unsafe { transmute(1u8) };
    let tag: ColorTag = unsafe { transmute(2u8) };
    let ch: char = unsafe { transmute(0x41u32) };
    let nz: NonZeroU32 = unsafe { transmute::<u32, NonZeroU32>(7u32) };
    let nzm: NonZeroMeters = unsafe { transmute::<u32, NonZeroMeters>(7u32) };
    let meters: MetersU32 = unsafe { transmute::<u32, MetersU32>(41u32) };
    let none: Option<NonZeroU32> = unsafe { transmute::<u32, Option<NonZeroU32>>(0u32) };
    let none_infer: Option<NonZeroU32> = unsafe { transmute::<u32, _>(0u32) };
    let none_block: core::option::Option<core::num::NonZeroU32> = unsafe {
        let _ = ();
        transmute(0u32)
    };
    let opt_b: Option<bool> = unsafe { transmute(2u8) };
    let single: SingleC = unsafe { transmute::<[u32; 2], SingleC>([0u32, 5u32]) };
    0u32
}
";
        let valid_chars: BTreeSet<u64> = [0x41, 0x7A, 0x03BB, 0x2603].into_iter().collect();
        let invalid_chars: BTreeSet<u64> =
            [0xD800, 0xDFFF, 0x11_0000, 0x1F_FFFF].into_iter().collect();
        for inject_invalid in [false, true] {
            let mut seen: BTreeMap<String, BTreeSet<u64>> = BTreeMap::new();
            let mut seen_single_payloads: BTreeSet<u64> = BTreeSet::new();
            for s in 0..256u64 {
                let mut f = syn::parse_file(seed).unwrap();
                let mut rng = DetRng::new(s);
                TransmuteValidityPerturber {
                    rng: &mut rng,
                    inject_invalid,
                    fn_ret_target: None,
                }
                .visit_file_mut(&mut f);
                let Item::Fn(func) = &mut f.items[0] else {
                    panic!("expected a function");
                };
                for stmt in &mut func.block.stmts {
                    let Stmt::Local(local) = stmt else { continue };
                    let Pat::Type(pat_ty) = &local.pat else {
                        continue;
                    };
                    let (Some(name), _) = extract_pat_ident(&pat_ty.pat) else {
                        continue;
                    };
                    let init = local.init.as_mut().expect("initialized local");
                    if let Some(call) = direct_transmute_call_mut(&mut init.expr) {
                        let value = literal_or_first_element_value(&call.args[0]);
                        if name == "single"
                            && let Expr::Array(arr) = &call.args[0]
                        {
                            seen_single_payloads
                                .insert(literal_or_first_element_value(&arr.elems[1]));
                        }
                        seen.entry(name).or_default().insert(value);
                    }
                }
            }
            let at = |name: &str| seen[name].clone();
            let expected = |values: &[u64]| values.iter().copied().collect::<BTreeSet<u64>>();
            // Niche `Option<...>` transmutes are never rewritten, even with
            // `::<u32, _>` turbofish inference, path qualification, or
            // multi-statement `unsafe` blocks.
            assert_eq!(at("none"), expected(&[0]));
            assert_eq!(at("none_infer"), expected(&[0]));
            assert_eq!(at("none_block"), expected(&[0]));
            assert_eq!(at("opt_b"), expected(&[2]));
            if inject_invalid {
                assert_eq!(at("b"), expected(&[1, 2, 3, 7, 255]));
                assert_eq!(at("tag"), expected(&[2, 3, 5, 7, 255]));
                assert_eq!(at("nz"), expected(&[0, 7]));
                assert_eq!(at("nzm"), expected(&[0, 7]));
                // Every `u32` is valid for `MetersU32`, so invalid injection
                // leaves it untouched rather than injecting surrogate `char`s.
                assert_eq!(at("meters"), expected(&[41]));
                assert_eq!(at("single"), expected(&[0, 1, 2, 7, u64::from(u32::MAX)]));
                let mut ch = invalid_chars.clone();
                ch.insert(0x41);
                assert_eq!(at("ch"), ch);
            } else {
                assert_eq!(at("b"), expected(&[0, 1]));
                assert_eq!(at("tag"), expected(&[0, 1, 2]));
                assert_eq!(at("nz"), expected(&[1, 7, 0x41, u64::from(u32::MAX)]));
                assert_eq!(at("nzm"), expected(&[1, 7, 0x41, u64::from(u32::MAX)]));
                assert_eq!(at("meters"), expected(&[0, 1, 41, 0x7FFF_0000]));
                assert_eq!(at("single"), expected(&[0]));
                assert_eq!(
                    seen_single_payloads,
                    expected(&[0, 5, 0x40, u64::from(u32::MAX)])
                );
                assert_eq!(at("ch"), valid_chars);
            }
        }
    }

    #[test]
    fn perturbers_preserve_used_underscore_locals_compound_lhs_and_overlay_lanes() {
        // 1. `AliasingAccessReorderer` must NOT swap a `_`-prefixed local past
        //    a later statement that reads it, nor swap `return` statements,
        //    while DOES swap `let _ = ...;`.
        let used_underscore = "\
pub fn guard_reorder() -> u32 {
    let mut x: u32 = 1u32;
    let p: *mut u32 = &raw mut x;
    let _tmp = 4u32;
    unsafe { *p = _tmp; };
    if x == 0u32 {
        return 9u32;
    }
    return x;
    unsafe { *p = 7u32; };
    x
}
";
        for s in 0..64u64 {
            let mut f = syn::parse_file(used_underscore).unwrap();
            let mut rng = DetRng::new(s);
            AliasingAccessReorderer { rng: &mut rng }.visit_file_mut(&mut f);
            let out = prettyplease::unparse(&f);
            let def_pos = out.find("let _tmp = 4u32;").expect("def");
            let use_pos = out.find("*p = _tmp;").expect("use");
            assert!(def_pos < use_pos, "use-before-def swap on seed {s}:\n{out}");
            let ret_pos = out.find("return x;").expect("ret");
            let after_ret = out.find("*p = 7u32;").expect("after ret");
            assert!(ret_pos < after_ret, "return swapped on seed {s}:\n{out}");
        }

        let wild_seed = "\
pub fn wild_reorder() -> u32 {
    let mut x: u32 = 1u32;
    let p: *mut u32 = &raw mut x;
    let _ = unsafe { *p };
    unsafe { *p = 2u32; };
    x
}
";
        let mut saw_wild_swap = false;
        for s in 0..32u64 {
            let mut f = syn::parse_file(wild_seed).unwrap();
            let mut rng = DetRng::new(s);
            AliasingAccessReorderer { rng: &mut rng }.visit_file_mut(&mut f);
            let out = prettyplease::unparse(&f);
            if out.find("*p = 2u32;").unwrap() < out.find("let _ = unsafe { *p };").unwrap() {
                saw_wild_swap = true;
                break;
            }
        }
        assert!(saw_wild_swap, "`let _ = ...;` must be reorderable");

        // 2. `ProjectionAstPerturber` preserves compound-assignment LHS
        //    (`pair.a ^= ...`), explores all four `OverlayU32` `.bytes[0..4]`
        //    lanes, preserves `u.value[0]` (the initialized byte) as well as
        //    keeping `u.value[1]` within uninitialized lanes `1..=3`, and
        //    leaves `borrowed.a` untouched when `&mut borrowed.b` is borrowed
        //    in the same function.
        let proj_seed = "\
pub fn proj_guard() -> u32 {
    let mut pair = PairU32 { a: 1u32, b: 2u32 };
    pair.a ^= 3u32;
    let mut borrowed = PairU32 { a: 5u32, b: 6u32 };
    let rb: &mut u32 = &mut borrowed.b;
    let keep_a: u32 = borrowed.a;
    *rb = 7u32;
    let o = OverlayU32 { word: 0x0403_0201u32 };
    let mut u: Uninit<[u8; 4]> = Uninit { uninit: () };
    unsafe {
        u.value[0] = 3u8;
        (u.value[0] as u32) ^ (o.bytes[0] as u32) ^ (u.value[1] as u32) ^ pair.a ^ keep_a
    }
}
";
        let mut overlay_lanes = BTreeSet::new();
        for s in 0..128u64 {
            let mut f = syn::parse_file(proj_seed).unwrap();
            let mut rng = DetRng::new(s);
            ProjectionAstPerturber {
                rng: &mut rng,
                in_addr_or_lhs: false,
                field_borrowed_bases: BTreeSet::new(),
            }
            .visit_file_mut(&mut f);
            let out = prettyplease::unparse(&f);
            assert!(
                out.contains("pair.a ^= 3u32;"),
                "compound-assign LHS field must not swap:\n{out}"
            );
            assert!(
                out.contains("let keep_a: u32 = borrowed.a;"),
                "disjoint field access while `&mut borrowed.b` is live must not swap:\n{out}"
            );
            assert!(
                out.contains("(u.value[0usize] as u32)") || out.contains("(u.value[0] as u32)"),
                "initialized `u.value[0]` must never be rewritten to an uninit lane:\n{out}"
            );
            assert!(
                !out.contains("^ u.value[0") && !out.contains("^(u.value[0"),
                "`u.value[1]` must stay in uninitialized lanes 1..=3:\n{out}"
            );
            for lane in 0..4usize {
                if out.contains(&format!("o.bytes[{lane}")) {
                    overlay_lanes.insert(lane);
                }
            }
        }
        assert_eq!(
            overlay_lanes,
            [0usize, 1, 2, 3].into_iter().collect(),
            "expected all 4 OverlayU32 byte lanes to be explored"
        );

        // 3. `close_and_normalize_function` and `collect_initialized_locals`
        //    handle Episode 2 parameter, niche `Option`, array, and shadowed
        //    local types.
        let param_seed = "\
pub fn param_ep2(
    s: SingleC,
    m: MetersU32,
    nm: NonZeroMeters,
    o: OverlayU32,
    ob: Option<bool>,
    oc: core::option::Option<ColorTag>,
    onz: core::option::Option<NonZeroU32>,
    pad: PaddedU8U32,
    bytes: [u8; 4],
    words: [u32; 2],
) -> u32 {
    let shadowed: u32 = 1u32;
    let shadowed: PairU32 = PairU32 { a: words[0], b: pad.word };
    let s2 = SingleC::Only(bytes[0] as u32);
    let m2 = MetersU32(2u32);
    m.0 ^ m2.0 ^ shadowed.a
}
";
        let batch = generate_miri_batch(&[param_seed], 4, 0xBEEF_CAFE);
        assert_eq!(batch.len(), 4);
        for cand in &batch {
            assert!(syn::parse_file(&cand.source).is_ok(), "{}", cand.source);
            assert!(
                cand.tracked_locals
                    .contains(&("s2".to_string(), "SingleC".to_string())),
                "{:?}",
                cand.tracked_locals
            );
            assert!(
                cand.tracked_locals
                    .contains(&("m2".to_string(), "MetersU32".to_string())),
                "{:?}",
                cand.tracked_locals
            );
            assert!(
                !cand
                    .tracked_locals
                    .contains(&("shadowed".to_string(), "u32".to_string())),
                "shadowed integer local must not remain typed as u32: {:?}",
                cand.tracked_locals
            );
            assert!(
                cand.tracked_locals
                    .contains(&("shadowed".to_string(), "PairU32".to_string())),
                "{:?}",
                cand.tracked_locals
            );
        }
    }

    #[test]
    fn reorderer_and_transmute_perturber_handle_shadowing_labels_src_types_and_single_visit() {
        // 1. `AliasingAccessReorderer` must not move `*p = _x;` past a
        //    shadowing `let _x: &PairU32 = &pair;`, must not swap an outer
        //    labeled `break 'outer;` inside an inner `while`, DOES swap typed
        //    `let _: u32 = ...;` and self-contained `'blk: { break 'blk; };`,
        //    and never swaps `TreeBorrowsRetagInterleaver` `Ub` variant 2's
        //    activating write after the parent read.
        let shadow_and_label = "\
pub fn guard_shadow_and_labels() -> u32 {
    let mut slot: u32 = 1u32;
    let p: *mut u32 = &raw mut slot;
    let pair = PairU32 { a: 2u32, b: 3u32 };
    let _x: u32 = 9u32;
    unsafe { *p = _x; };
    let _x: &PairU32 = &pair;
    'outer: loop {
        while slot < 10u32 {
            break 'outer;
        }
        unsafe { *p = 5u32; };
        break;
    }
    slot
}
";
        for s in 0..64u64 {
            let mut f = syn::parse_file(shadow_and_label).unwrap();
            let mut rng = DetRng::new(s);
            AliasingAccessReorderer { rng: &mut rng }.visit_file_mut(&mut f);
            let out = prettyplease::unparse(&f);
            let write_pos = out.find("*p = _x;").expect("write _x");
            let shadow_pos = out.find("let _x: &PairU32 = &pair;").expect("shadow _x");
            assert!(
                write_pos < shadow_pos,
                "swapped use of `_x` into shadowing `let _x: &PairU32` on seed {s}:\n{out}"
            );
            let while_pos = out.find("while slot < 10u32").expect("while");
            let after_while = out.find("*p = 5u32;").expect("after while");
            assert!(
                while_pos < after_while,
                "outer-labeled `break 'outer` inside `while` must not reorder:\n{out}"
            );
        }

        let typed_wild_and_block_label = "\
pub fn allow_typed_wild_and_local_label() -> u32 {
    let mut x: u32 = 1u32;
    let p: *mut u32 = &raw mut x;
    let _: u32 = unsafe { *p };
    'blk: {
        unsafe { *p = 2u32; };
        break 'blk;
    };
    x
}
";
        let mut saw_typed_wild_swap = false;
        for s in 0..32u64 {
            let mut f = syn::parse_file(typed_wild_and_block_label).unwrap();
            let mut rng = DetRng::new(s);
            AliasingAccessReorderer { rng: &mut rng }.visit_file_mut(&mut f);
            let out = prettyplease::unparse(&f);
            if out.find("'blk:").unwrap() < out.find("let _: u32 = unsafe { *p };").unwrap() {
                saw_typed_wild_swap = true;
                break;
            }
        }
        assert!(
            saw_typed_wild_swap,
            "typed `let _: u32 = ...;` and locally labeled `'blk` must be reorderable"
        );

        let ub_var2_seed = "pub fn ub2() -> u32 {\n    1u32\n}\n";
        let ub_var2_src = first_output_containing(
            ub_var2_seed,
            &TreeBorrowsRetagInterleaver,
            MutationMode::Ub,
            "let __tb_act: &mut u32 = unsafe { &mut *__tb_root };",
        )
        .expect("TreeBorrowsRetagInterleaver Ub variant 2");
        for s in 0..64u64 {
            let mut f = syn::parse_file(&ub_var2_src).unwrap();
            let mut rng = DetRng::new(s);
            AliasingAccessReorderer { rng: &mut rng }.visit_file_mut(&mut f);
            let out = prettyplease::unparse(&f);
            let act_write = out.find("*__tb_act =").expect("activating write");
            let parent_read = out
                .find("let _ = unsafe { *__tb_root };")
                .expect("parent read");
            assert!(
                act_write < parent_read,
                "follow-up reorderer erased UB in variant 2 on seed {s}:\n{out}"
            );
        }

        // 2. `TransmuteValidityPerturber` visits non-tail statements in a typed
        //    `let` block not ending in `transmute` exactly ONCE (matching the
        //    RNG state of an untyped `let`), rejects incompatible turbofish
        //    `Src` types, and perturbs typed function-return tail `transmute`s
        //    while leaving `-> Option<NonZeroU32>` untouched.
        let typed_non_tail = "\
pub fn non_tail_typed() -> u32 {
    let x: u32 = unsafe {
        let b: bool = transmute(1u8);
        b as u32
    };
    x
}
";
        let untyped_non_tail = "\
pub fn non_tail_untyped() -> u32 {
    let x = unsafe {
        let b: bool = transmute(1u8);
        b as u32
    };
    x
}
";
        for s in 0..64u64 {
            let mut f1 = syn::parse_file(typed_non_tail).unwrap();
            let mut f2 = syn::parse_file(untyped_non_tail).unwrap();
            let mut rng1 = DetRng::new(s);
            let mut rng2 = DetRng::new(s);
            TransmuteValidityPerturber {
                rng: &mut rng1,
                inject_invalid: true,
                fn_ret_target: None,
            }
            .visit_file_mut(&mut f1);
            TransmuteValidityPerturber {
                rng: &mut rng2,
                inject_invalid: true,
                fn_ret_target: None,
            }
            .visit_file_mut(&mut f2);
            assert_eq!(
                rng1.next_u64(),
                rng2.next_u64(),
                "double-visitation RNG skew on typed block local for seed {s}"
            );
        }

        let incompatible_src = "\
pub fn src_mismatch() -> u32 {
    let b: bool = unsafe { transmute::<i8, bool>(0) };
    let m: MetersU32 = unsafe { transmute::<i32, MetersU32>(41) };
    let s: SingleC = unsafe { transmute::<[i32; 2], SingleC>([0, 5]) };
    (b as u32) ^ m.0
}
";
        for inject_invalid in [false, true] {
            for s in 0..64u64 {
                let mut f = syn::parse_file(incompatible_src).unwrap();
                let mut rng = DetRng::new(s);
                TransmuteValidityPerturber {
                    rng: &mut rng,
                    inject_invalid,
                    fn_ret_target: None,
                }
                .visit_file_mut(&mut f);
                let out = prettyplease::unparse(&f);
                assert!(
                    out.contains("transmute::<i8, bool>(0)")
                        && out.contains("transmute::<i32, MetersU32>(41)")
                        && out.contains("transmute::<[i32; 2], SingleC>([0, 5])"),
                    "incompatible turbofish Src was rewritten into type error:\n{out}"
                );
            }
        }

        let fn_ret_seed = "\
pub fn ret_nz() -> NonZeroU32 {
    unsafe { transmute(7u32) }
}
pub fn ret_opt() -> Option<NonZeroU32> {
    unsafe { transmute(0u32) }
}
";
        let mut saw_zero_ret_nz = false;
        for s in 0..64u64 {
            let mut f = syn::parse_file(fn_ret_seed).unwrap();
            let mut rng = DetRng::new(s);
            TransmuteValidityPerturber {
                rng: &mut rng,
                inject_invalid: true,
                fn_ret_target: None,
            }
            .visit_file_mut(&mut f);
            let out = prettyplease::unparse(&f);
            let (ret_nz_src, ret_opt_src) = out.split_once("pub fn ret_opt").unwrap();
            if ret_nz_src.contains("transmute(0u32)") {
                saw_zero_ret_nz = true;
            }
            assert!(
                ret_opt_src.contains("transmute(0u32)"),
                "`-> Option<NonZeroU32>` return transmute must stay unperturbed:\n{out}"
            );
        }
        assert!(
            saw_zero_ret_nz,
            "typed return `-> NonZeroU32` tail transmute must be perturbed"
        );
    }

    #[test]
    fn reorderer_and_perturbers_guard_stmt_macros_safe_borrows_moves_and_complex_params() {
        // 1. `AliasingAccessReorderer` must NOT swap:
        //    - `Stmt::Macro` (`unsafe { panic!("boom"); };`) past a pointer write;
        //    - a safe `&mut` write (`*r = 2u32;`) across a direct owner write
        //      (`x = 3u32;`, which would fail borrowck with `E0506`);
        //    - a non-`Copy` ADT move (`let _moved: SingleC = sc;`) ahead of an
        //      earlier borrow of `sc` (`E0382`).
        let reorder_hazards = "\
pub fn guard_reorder_hazards() -> u32 {
    let mut x: u32 = 1u32;
    let p: *mut u32 = &raw mut x;
    let r: &mut u32 = &mut x;
    *r = 2u32;
    x = 3u32;
    let sc = SingleC::Only(5u32);
    match &sc {
        SingleC::Only(v) => unsafe {
            *p = *v;
        },
    };
    let _moved: SingleC = sc;
    unsafe {
        panic!(\"guard macro stmt\");
    };
    unsafe {
        *p = 99u32;
    };
    x
}
";
        for s in 0..64u64 {
            let mut f = syn::parse_file(reorder_hazards).unwrap();
            let mut rng = DetRng::new(s);
            AliasingAccessReorderer { rng: &mut rng }.visit_file_mut(&mut f);
            let out = prettyplease::unparse(&f);
            assert!(
                out.find("*r = 2u32;").unwrap() < out.find("x = 3u32;").unwrap(),
                "safe borrow write swapped past owner write (`E0506`) on seed {s}:\n{out}"
            );
            assert!(
                out.find("match &sc").unwrap() < out.find("let _moved: SingleC = sc;").unwrap(),
                "non-Copy move swapped ahead of borrow (`E0382`) on seed {s}:\n{out}"
            );
            assert!(
                out.find("panic!(\"guard macro stmt\");").unwrap()
                    < out.find("*p = 99u32;").unwrap(),
                "`Stmt::Macro` panic inside `unsafe` swapped on seed {s}:\n{out}"
            );
        }

        // 2. `ProjectionAstPerturber` preserves `(borrowed).a` when
        //    `&mut (borrowed.b)` or `let PairU32 { b: ref mut rb2, .. } = s_bor`
        //    borrows a field.
        let paren_and_struct_pat = "\
pub fn proj_paren_and_pat() -> u32 {
    let mut borrowed = PairU32 { a: 1u32, b: 2u32 };
    let rb: &mut u32 = &mut (borrowed.b);
    let keep1: u32 = (borrowed).a;
    *rb = 3u32;
    let mut s_bor = PairU32 { a: 4u32, b: 5u32 };
    let PairU32 { b: ref mut rb2, .. } = s_bor;
    let keep2: u32 = s_bor.a;
    *rb2 = 6u32;
    keep1 ^ keep2
}
";
        for s in 0..64u64 {
            let mut f = syn::parse_file(paren_and_struct_pat).unwrap();
            let mut rng = DetRng::new(s);
            ProjectionAstPerturber {
                rng: &mut rng,
                in_addr_or_lhs: false,
                field_borrowed_bases: BTreeSet::new(),
            }
            .visit_file_mut(&mut f);
            let out = prettyplease::unparse(&f);
            assert!(
                out.contains(".a;") && !out.contains("keep1: u32 = (borrowed).b;"),
                "parenthesized field borrow missed on seed {s}:\n{out}"
            );
            assert!(
                out.contains("let keep2: u32 = s_bor.a;"),
                "struct-pattern `ref mut` field borrow missed on seed {s}:\n{out}"
            );
        }

        // 3. `TransmuteValidityPerturber` handles `if`/`else` branched tail
        //    transmutes, explicit `return unsafe { transmute(...) };`,
        //    `[u32; 2usize]` turbofish, and `[0, 5u32]` `SingleC` literals,
        //    while keeping `Option<NonZeroU32>` `if`/`else` & `return`
        //    transmutes untouched.
        let branched_seed = "\
pub fn ret_branch_nz() -> NonZeroU32 {
    if true {
        return unsafe { transmute(7u32) };
    } else {
        unsafe { transmute(9u32) }
    }
}
pub fn ret_branch_opt() -> Option<NonZeroU32> {
    if true {
        return unsafe { transmute(0u32) };
    } else {
        unsafe { transmute(0u32) }
    }
}
pub fn single_unannotated_tag() -> u32 {
    let s1: SingleC = unsafe { transmute([0, 5u32]) };
    let s2: SingleC = unsafe { transmute::<[u32; 2usize], SingleC>([0, 9]) };
    match (s1, s2) {
        (SingleC::Only(a), SingleC::Only(b)) => a ^ b,
    }
}
";
        let mut saw_ret_stmt_zero = false;
        let mut saw_else_zero = false;
        let mut saw_s1_bad = false;
        let mut saw_s2_bad = false;
        for s in 0..64u64 {
            let mut f = syn::parse_file(branched_seed).unwrap();
            let mut rng = DetRng::new(s);
            TransmuteValidityPerturber {
                rng: &mut rng,
                inject_invalid: true,
                fn_ret_target: None,
            }
            .visit_file_mut(&mut f);
            let out = prettyplease::unparse(&f);
            let (nz_part, rest) = out.split_once("pub fn ret_branch_opt").unwrap();
            let (opt_part, single_part) = rest.split_once("pub fn single_unannotated_tag").unwrap();
            if nz_part.contains("return unsafe { transmute(0u32) };") {
                saw_ret_stmt_zero = true;
            }
            if nz_part.contains("else {\n        unsafe { transmute(0u32) }") {
                saw_else_zero = true;
            }
            assert!(
                !opt_part.contains("0x") && opt_part.matches("transmute(0u32)").count() == 2,
                "`Option<NonZeroU32>` return/if transmutes must stay unperturbed:\n{opt_part}"
            );
            if !single_part.contains("transmute([0, 5u32])")
                && !single_part.contains("transmute([0u32, 5u32])")
            {
                saw_s1_bad = true;
            }
            if !single_part.contains("([0, 9])") && !single_part.contains("([0u32, 9])") {
                saw_s2_bad = true;
            }
        }
        assert!(saw_ret_stmt_zero && saw_else_zero && saw_s1_bad && saw_s2_bad);

        // 4. `close_and_normalize_function` and `collect_initialized_locals`
        //    handle lifetime-annotated `&'a mut`, `*mut`, destructuring
        //    parameters, `Uninit<T>`, `UnsafeCell<T>`, and tuple-destructuring
        //    shadowing.
        let complex_param_seed = "\
pub fn complex_params<'a>(
    r: &'a mut PairU32,
    p: *mut SingleC,
    MetersU32(m_inner): MetersU32,
    (t0, nzm): (u32, NonZeroMeters),
    u: Uninit<u32>,
    cell: UnsafeCell<u32>,
) -> u32 {
    let shadowed: u32 = 1u32;
    let (shadowed, _): (PairU32, u32) = (PairU32 { a: t0, b: m_inner }, 2u32);
    let _ = (p, cell);
    r.a ^ shadowed.b ^ unsafe { u.value } ^ unsafe { transmute::<NonZeroU32, u32>(nzm.0) }
}
";
        let batch = generate_miri_batch(&[complex_param_seed], 4, 0xB2B2_CAFE);
        assert_eq!(batch.len(), 4);
        for cand in &batch {
            assert!(syn::parse_file(&cand.source).is_ok(), "{}", cand.source);
            assert!(!cand.fn_source.contains("'a"), "{}", cand.fn_source);
            assert!(
                !cand
                    .tracked_locals
                    .contains(&("shadowed".to_string(), "u32".to_string())),
                "tuple-destructuring shadow left `shadowed: u32` in locals: {:?}",
                cand.tracked_locals
            );
        }
    }

    #[test]
    fn receipt_seed_batches_exercise_episode_2_seeds_and_templates() {
        // Local-name prefixes that only the Episode 2 templates introduce.
        let families: [(&str, &[&str]); 3] = [
            (
                "BitValidityTransmuteMutator",
                &[
                    "__valid_nz",
                    "__valid_nzm",
                    "__niche_",
                    "__meters",
                    "let mut __single: SingleC",
                    "__overlay",
                    "__bad_nz",
                    "__bad_nzm",
                    "__bad_single",
                    "__part_slot",
                ],
            ),
            (
                "PlaceProjectionWrapper",
                &[
                    "__proj_single",
                    "__proj_overlay",
                    "__proj_slot",
                    "__proj_nzm",
                    "__dead_pair",
                    "__dead_single",
                    "__proj_half",
                    "__dead_ov",
                ],
            ),
            ("TreeBorrowsRetagInterleaver", &["__rr_"]),
        ];
        let category_8_seeds = [
            "pass_nonzero_u32_transmute_roundtrip",
            "ub_nonzero_u32_transmute_zero",
            "pass_option_nonzero_none_niche",
            "pass_transparent_wrapper_transmute",
            "pass_single_c_enum_match_reinit",
            "ub_single_c_enum_invalid_tag",
            "pass_union_overlay_word_bytes",
            "ub_union_uninit_bytes_partial_read",
            "pass_raw_ref_disjoint_fields",
            "ub_raw_mut_after_parent_write",
            "ub_transparent_nonzero_wrapper_zero",
            "pass_option_some_niche_and_single_c_mut",
        ];
        // `miri-difftest --batches 5 --batch-size 20 --seed S` derives each
        // batch's seed this way.
        for seed in [0x5EED_0001u64, 0xCAFE_BABE] {
            let mut template_hits: BTreeMap<&str, usize> = BTreeMap::new();
            let mut category_8_hits = 0usize;
            for b_idx in 0..5usize {
                let batch_seed =
                    seed.wrapping_add((b_idx as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
                for cand in generate_miri_corpus_batch(20, batch_seed, b_idx) {
                    for (family, markers) in &families {
                        if markers.iter().any(|m| cand.fn_source.contains(m)) {
                            *template_hits.entry(family).or_default() += 1;
                        }
                    }
                    if category_8_seeds.contains(&cand.seed_name.as_str()) {
                        category_8_hits += 1;
                    }
                }
            }
            eprintln!(
                "seed {seed:#X}: candidates with Episode 2 templates {template_hits:?}, \
                 candidates mutated from Category 8 seeds {category_8_hits}"
            );
            for (family, _) in &families {
                assert!(
                    template_hits.get(family).copied().unwrap_or(0) > 0,
                    "seed {seed:#X} never emitted an Episode 2 {family} template"
                );
            }
            assert!(
                category_8_hits > 0,
                "seed {seed:#X} never chose a Category 8 seed"
            );
        }
    }
}
