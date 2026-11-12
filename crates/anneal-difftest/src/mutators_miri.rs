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

/// Extract the 87 closed zero-argument test functions from
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

/// Extracts initialized local bindings and their annotated/inferred scalar
/// types from a function signature and body block.
pub fn collect_initialized_locals(func: &ItemFn) -> Vec<TrackedLocal> {
    let mut locals = Vec::new();

    for arg in &func.sig.inputs {
        if let FnArg::Typed(pat_ty) = arg {
            let (name_opt, is_mut) = extract_pat_ident(&pat_ty.pat);
            if let Some(name) = name_opt {
                locals.push(TrackedLocal {
                    name,
                    ty: pat_ty.ty.to_token_stream().to_string().replace(' ', ""),
                    is_mut,
                });
            }
        }
    }

    for stmt in &func.block.stmts {
        if let Stmt::Local(Local {
            pat,
            init: Some(local_init),
            ..
        }) = stmt
        {
            match pat {
                Pat::Type(pat_type) => {
                    let (name_opt, is_mut) = extract_pat_ident(&pat_type.pat);
                    if let Some(name) = name_opt {
                        locals.push(TrackedLocal {
                            name,
                            ty: pat_type.ty.to_token_stream().to_string().replace(' ', ""),
                            is_mut,
                        });
                    }
                }
                _ => {
                    let (name_opt, is_mut) = extract_pat_ident(pat);
                    if let Some(name) = name_opt {
                        let inferred = infer_expr_type_name(&local_init.expr);
                        locals.push(TrackedLocal {
                            name,
                            ty: inferred,
                            is_mut,
                        });
                    }
                }
            }
        }
    }

    locals
}

fn extract_pat_ident(pat: &Pat) -> (Option<String>, bool) {
    match pat {
        Pat::Ident(pi) => (Some(pi.ident.to_string()), pi.mutability.is_some()),
        _ => (None, false),
    }
}

fn infer_expr_type_name(expr: &Expr) -> String {
    match expr {
        Expr::Lit(el) => match &el.lit {
            Lit::Int(li) if !li.suffix().is_empty() => li.suffix().to_string(),
            Lit::Int(_) => "u32".to_string(),
            Lit::Bool(_) => "bool".to_string(),
            _ => "unknown".to_string(),
        },
        Expr::Cast(cast) => cast.ty.to_token_stream().to_string().replace(' ', ""),
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

/// Convert any function parameters into leading initialized local bindings and
/// rewrite method calls (`.wrapping_add`, `.wrapping_sub`, `.wrapping_mul`,
/// `.rotate_left`) into primitive operators so every candidate is closed,
/// zero-argument, and free of unmodeled method calls.
fn close_and_normalize_function(func: &mut ItemFn, rng: &mut DetRng) {
    if !func.sig.inputs.is_empty() {
        let mut init_stmts = Vec::new();
        let inputs: Vec<FnArg> = func.sig.inputs.iter().cloned().collect();
        func.sig.inputs.clear();
        for arg in inputs {
            if let FnArg::Typed(pat_ty) = arg {
                let (name_opt, _) = extract_pat_ident(&pat_ty.pat);
                if let Some(name) = name_opt {
                    let ident = format_ident!("{}", name);
                    let ty = &pat_ty.ty;
                    let ty_str = ty.to_token_stream().to_string().replace(' ', "");
                    let init_val = seeded_scalar_expr(&ty_str, rng);
                    let stmt: Stmt = syn::parse_quote! {
                        let mut #ident: #ty = #init_val;
                    };
                    init_stmts.push(stmt);
                }
            }
        }
        func.block.stmts.splice(0..0, init_stmts);
    }

    let mut normalizer = MethodCallNormalizer;
    normalizer.visit_item_fn_mut(func);
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
        "bool" => {
            let b = (pick & 1) == 1;
            syn::parse_quote!(#b)
        }
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

struct ProjectionAstPerturber<'a> {
    rng: &'a mut DetRng,
    in_addr_or_lhs: bool,
}

impl VisitMut for ProjectionAstPerturber<'_> {
    fn visit_type_mut(&mut self, _ty: &mut Type) {
        // Never mutate `[T; N]` array lengths in types.
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
                let base_str = idx_expr.expr.to_token_stream().to_string();
                if let Expr::Lit(el) = &mut *idx_expr.index
                    && let Lit::Int(li) = &el.lit
                    && let Ok(cur_idx) = li.base10_parse::<usize>()
                    && self.rng.coin(1, 2)
                {
                    // For `bytes[1]` in `ub_read_struct_padding_byte`, indices
                    // 1..=3 are the uninitialized padding bytes of `PaddedU8U32`.
                    let new_idx: usize = if base_str == "bytes" && (1..=3).contains(&cur_idx) {
                        if cur_idx == 1 { 2 } else { 1 }
                    } else if cur_idx == 0 {
                        1
                    } else {
                        0
                    };
                    idx_expr.index = Box::new(syn::parse_quote!(#new_idx));
                }
            }
            Expr::Field(field_expr) if !self.in_addr_or_lhs => {
                if let syn::Member::Named(ident) = &mut field_expr.member {
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
                MutationMode::Pass | MutationMode::PerturbAst => match rng.gen_range(4) {
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
                    _ => {
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
                },
                MutationMode::Panic => {
                    let oob_idx: usize = 3 + rng.gen_range(3);
                    syn::parse_quote! {
                        let __oob_arr: [u32; 3] = [#seed_val, #c1, #c0 ^ #c1];
                        let __oob_idx: usize = #oob_idx;
                        let #probe_ident: u32 = __oob_arr[__oob_idx];
                    }
                }
                MutationMode::Ub => match rng.gen_range(4) {
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
                    _ => syn::parse_quote! {
                        let mut __proj_half: Uninit<[u32; 2]> = Uninit { uninit: () };
                        let #probe_ident: u32 = unsafe {
                            __proj_half.value[0] = #seed_val;
                            __proj_half.value[1]
                        };
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

/// Checks whether `stmt` is an access statement (semicolon-terminated expression
/// statement such as `*r = 1;` / `unsafe { *p1 = 3; }` or an unused `_` local
/// read `let _y = unsafe { *root };`) that does not introduce a named binding
/// referenced by subsequent statements, making adjacent pairs safe to swap.
fn is_reordering_safe_access_stmt(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Expr(_, Some(_)) => true,
        Stmt::Local(loc) => {
            let (name_opt, _) = extract_pat_ident(&loc.pat);
            name_opt.is_some_and(|n| n.starts_with('_'))
        }
        _ => false,
    }
}

struct AliasingAccessReorderer<'a> {
    rng: &'a mut DetRng,
}

impl VisitMut for AliasingAccessReorderer<'_> {
    fn visit_block_mut(&mut self, block: &mut Block) {
        syn::visit_mut::visit_block_mut(self, block);
        if block.stmts.len() < 2 {
            return;
        }
        let mut idx = 0;
        while idx + 1 < block.stmts.len() {
            if is_reordering_safe_access_stmt(&block.stmts[idx])
                && is_reordering_safe_access_stmt(&block.stmts[idx + 1])
                && self.rng.coin(1, 2)
            {
                block.stmts.swap(idx, idx + 1);
                idx += 2;
            } else {
                idx += 1;
            }
        }
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
                MutationMode::Pass => match rng.gen_range(3) {
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
                    _ => syn::parse_quote! {
                        let __rr_pair: PairU32 = PairU32 { a: #init_val, b: #write_val };
                        let __rr_shr: &PairU32 = &__rr_pair;
                        let __rr_ra: *const u32 = &raw const (*__rr_shr).a;
                        let __rr_rb: *const u32 = &raw const __rr_shr.b;
                        let #probe_ident: u32 = unsafe { (*__rr_ra) ^ (*__rr_rb) } ^ __rr_shr.a;
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
                    let variant = rng.gen_range(7);
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
                        2 => syn::parse_quote! {
                            let mut __tb_x: u32 = #init_val;
                            let __tb_root: *mut u32 = &raw mut __tb_x;
                            let __tb_act: &mut u32 = unsafe { &mut *__tb_root };
                            *__tb_act = #write_val;
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
                        _ => syn::parse_quote! {
                            let mut __rr_pair: PairU32 = PairU32 { a: #init_val, b: #write_val };
                            let __rr_m: &mut PairU32 = &mut __rr_pair;
                            let __rr_s: &PairU32 = &*__rr_m;
                            let __rr_ra: *const u32 = &raw const (*__rr_s).a;
                            __rr_m.a = #write_val;
                            let #probe_ident: u32 = unsafe { *__rr_ra };
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
    /// Every `u32` is a valid `Option<NonZeroU32>`, but Anneal reports a
    /// false-positive UB when `transmute` produces a nonzero (`Some`) value,
    /// so the perturber never rewrites the argument of such a call.
    OptionNonZeroU32,
    /// `transmute::<[u32; 2], SingleC>([tag, payload])`, where only tag `0`
    /// is valid.
    SingleC,
    /// A destination type without a modeled validity invariant, or one that
    /// neither a turbofish nor a `let` annotation names.
    Unknown,
}

impl TransmuteTarget {
    fn of_type(ty: &Type) -> Self {
        match ty.to_token_stream().to_string().replace(' ', "").as_str() {
            "bool" => Self::Bool,
            "char" => Self::Char,
            "ColorTag" => Self::ColorTag,
            "NonZeroU32" | "core::num::NonZeroU32" => Self::NonZeroU32,
            "Option<NonZeroU32>" | "Option<core::num::NonZeroU32>" => Self::OptionNonZeroU32,
            "SingleC" => Self::SingleC,
            _ => Self::Unknown,
        }
    }

    /// Return the destination type that a `transmute::<Src, Dst>` turbofish
    /// names, or `None` if `call` has no turbofish.
    fn of_turbofish(call: &ExprCall) -> Option<Self> {
        let Expr::Path(ep) = &*call.func else {
            return None;
        };
        let PathArguments::AngleBracketed(args) = &ep.path.segments.last()?.arguments else {
            return None;
        };
        match args.args.iter().nth(1)? {
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

/// Return the `transmute` call that `expr` evaluates directly, looking through
/// parentheses and an `unsafe` block that holds only that call.
fn direct_transmute_call_mut(expr: &mut Expr) -> Option<&mut ExprCall> {
    match expr {
        Expr::Call(call) if is_transmute_call(call) => Some(call),
        Expr::Paren(paren) => direct_transmute_call_mut(&mut paren.expr),
        Expr::Unsafe(unsafe_expr) if unsafe_expr.block.stmts.len() == 1 => {
            match &mut unsafe_expr.block.stmts[0] {
                Stmt::Expr(inner, None) => direct_transmute_call_mut(inner),
                _ => None,
            }
        }
        _ => None,
    }
}

struct TransmuteValidityPerturber<'a> {
    rng: &'a mut DetRng,
    inject_invalid: bool,
}

impl TransmuteValidityPerturber<'_> {
    /// With probability 1/2, rewrite the integer literal argument of `call`
    /// (or the tag literal of a `SingleC` array argument) to a value that is
    /// valid for `target`, or, if `inject_invalid` is set, to a value that
    /// violates `target`'s validity invariant.
    fn perturb_call(&mut self, call: &mut ExprCall, target: TransmuteTarget) {
        match target {
            TransmuteTarget::OptionNonZeroU32 => {}
            TransmuteTarget::SingleC => {
                if let Expr::Array(arr) = &mut call.args[0]
                    && let Some(Expr::Lit(el)) = arr.elems.first()
                    && let Lit::Int(li) = &el.lit
                    && li.suffix() == "u32"
                    && self.rng.coin(1, 2)
                {
                    let tag: u32 = if self.inject_invalid {
                        [1u32, 2u32, 7u32, u32::MAX][self.rng.gen_range(4)]
                    } else {
                        0u32
                    };
                    arr.elems[0] = syn::parse_quote!(#tag);
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
                if !self.rng.coin(1, 2) {
                    return;
                }
                let invalid = self.inject_invalid;
                let replacement: Expr = match (target, suffix.as_str()) {
                    (TransmuteTarget::Bool, "u8") => {
                        let v: u8 = if invalid {
                            [2u8, 3u8, 7u8, 255u8][self.rng.gen_range(4)]
                        } else {
                            self.rng.gen_range(2) as u8
                        };
                        syn::parse_quote!(#v)
                    }
                    (TransmuteTarget::ColorTag, "u8") => {
                        let v: u8 = if invalid {
                            [3u8, 5u8, 7u8, 255u8][self.rng.gen_range(4)]
                        } else {
                            self.rng.gen_range(3) as u8
                        };
                        syn::parse_quote!(#v)
                    }
                    (TransmuteTarget::Unknown, "u8") => {
                        let v: u8 = if invalid {
                            [3u8, 5u8, 7u8, 255u8][self.rng.gen_range(4)]
                        } else {
                            self.rng.gen_range(2) as u8
                        };
                        syn::parse_quote!(#v)
                    }
                    (TransmuteTarget::NonZeroU32, "u32") => {
                        let v: u32 = if invalid {
                            0u32
                        } else {
                            [1u32, 7u32, 0x41u32, u32::MAX][self.rng.gen_range(4)]
                        };
                        syn::parse_quote!(#v)
                    }
                    (TransmuteTarget::Char | TransmuteTarget::Unknown, "u32") => {
                        let v: u32 = if invalid {
                            [0xD800u32, 0xDFFFu32, 0x11_0000u32, 0x1F_FFFFu32]
                                [self.rng.gen_range(4)]
                        } else {
                            [0x41u32, 0x7Au32, 0x03BBu32, 0x2603u32][self.rng.gen_range(4)]
                        };
                        syn::parse_quote!(#v)
                    }
                    _ => return,
                };
                call.args[0] = replacement;
            }
        }
    }
}

impl VisitMut for TransmuteValidityPerturber<'_> {
    fn visit_local_mut(&mut self, local: &mut Local) {
        // `let x: Dst = unsafe { transmute(lit) };` names its destination type
        // only in the `let` annotation.
        if let Pat::Type(pat_ty) = &local.pat
            && let Some(init) = local.init.as_mut()
            && init.diverge.is_none()
            && let Some(call) = direct_transmute_call_mut(&mut init.expr)
            && TransmuteTarget::of_turbofish(call).is_none()
        {
            let target = TransmuteTarget::of_type(&pat_ty.ty);
            for arg in call.args.iter_mut() {
                self.visit_expr_mut(arg);
            }
            self.perturb_call(call, target);
            return;
        }
        syn::visit_mut::visit_local_mut(self, local);
    }

    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        syn::visit_mut::visit_expr_mut(self, expr);
        if let Expr::Call(call) = expr
            && is_transmute_call(call)
        {
            let target = TransmuteTarget::of_turbofish(call).unwrap_or(TransmuteTarget::Unknown);
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
                    let variant = rng.gen_range(9);
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
                        _ => {
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
                    let variant = rng.gen_range(9);
                    match variant {
                        0 => syn::parse_quote! {
                            let __bad_b: bool = unsafe { transmute(#bad_u8) };
                            let #probe_ident: u32 = __bad_b as u32;
                        },
                        1 => syn::parse_quote! {
                            let __bad_ch: char = unsafe { transmute(#bad_char_u32) };
                            let #probe_ident: u32 = __bad_ch as u32;
                        },
                        2 => syn::parse_quote! {
                            let __bad_tag: ColorTag = unsafe { transmute(#bad_enum_u8) };
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
                            let #probe_ident: u32 = __pad_bytes[1] as u32;
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
                        _ => {
                            let write_idx: usize = rng.gen_range(4);
                            let read_idx: usize = (write_idx + 1 + rng.gen_range(3)) % 4;
                            let byte_u8: u8 = [3u8, 0x7Fu8, 0x80u8, 0xFFu8][rng.gen_range(4)];
                            syn::parse_quote! {
                                let mut __part_slot: Uninit<[u8; 4]> = Uninit { uninit: () };
                                let #probe_ident: u32 = unsafe {
                                    __part_slot.value[#write_idx] = #byte_u8;
                                    __part_slot.value[#read_idx] as u32
                                };
                            }
                        }
                    }
                }
            };
            inject_live_probe(func, stmts, &probe_ident);
        }
    }
}

/// Generate the 87-candidate identity batch directly from
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
/// the 87-function `tests/miri-diff/corpus/src/lib.rs` seed corpus.
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
    fn corpus_seeds_load_all_87_zero_arg_functions_and_do_not_blocklist_known_bugs() {
        let seeds = load_miri_diff_corpus_seeds();
        assert_eq!(
            seeds.len(),
            87,
            "expected 87 zero-arg functions from tests/miri-diff/corpus/src/lib.rs"
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
        let cases: [(&dyn MiriAstMutator, MutationMode, &str); 23] = [
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
    let none: Option<NonZeroU32> = unsafe { transmute::<u32, Option<NonZeroU32>>(0u32) };
    let single: SingleC = unsafe { transmute::<[u32; 2], SingleC>([0u32, 5u32]) };
    0u32
}
";
        let valid_chars: BTreeSet<u64> = [0x41, 0x7A, 0x03BB, 0x2603].into_iter().collect();
        let invalid_chars: BTreeSet<u64> =
            [0xD800, 0xDFFF, 0x11_0000, 0x1F_FFFF].into_iter().collect();
        for inject_invalid in [false, true] {
            let mut seen: BTreeMap<String, BTreeSet<u64>> = BTreeMap::new();
            for s in 0..256u64 {
                let mut f = syn::parse_file(seed).unwrap();
                let mut rng = DetRng::new(s);
                TransmuteValidityPerturber {
                    rng: &mut rng,
                    inject_invalid,
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
                        seen.entry(name).or_default().insert(value);
                    }
                }
            }
            let at = |name: &str| seen[name].clone();
            let expected = |values: &[u64]| values.iter().copied().collect::<BTreeSet<u64>>();
            // `Option<NonZeroU32>` is never rewritten: Anneal cannot decode a
            // transmuted `Some`.
            assert_eq!(at("none"), expected(&[0]));
            if inject_invalid {
                assert_eq!(at("b"), expected(&[1, 2, 3, 7, 255]));
                assert_eq!(at("tag"), expected(&[2, 3, 5, 7, 255]));
                assert_eq!(at("nz"), expected(&[0, 7]));
                assert_eq!(at("single"), expected(&[0, 1, 2, 7, u64::from(u32::MAX)]));
                let mut ch = invalid_chars.clone();
                ch.insert(0x41);
                assert_eq!(at("ch"), ch);
            } else {
                assert_eq!(at("b"), expected(&[0, 1]));
                assert_eq!(at("tag"), expected(&[0, 1, 2]));
                assert_eq!(at("nz"), expected(&[1, 7, 0x41, u64::from(u32::MAX)]));
                assert_eq!(at("single"), expected(&[0]));
                assert_eq!(at("ch"), valid_chars);
            }
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
                    "__niche_",
                    "__meters",
                    "let mut __single: SingleC",
                    "__overlay",
                    "__bad_nz",
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
                    "__dead_pair",
                    "__dead_single",
                    "__proj_half",
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
