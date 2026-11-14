// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Milestone 5: ITree-strength strictly safe-Rust `syn` AST mutators
//! (`CallBoundaryOutliner`, `LayoutPaddingPerturber`, `BranchLoopWeaver`,
//! `ExtOracleInjector`) plus [`generate_itree_batch`] and
//! [`annotate_itree_external_callees`].
//!
//! Enforces a hard zero-`unsafe` invariant: [`contains_unsafe_token`] verifies
//! that **zero** `unsafe` tokens appear anywhere in any emitted candidate
//! program. All arithmetic in generated bodies uses widening integer casts and
//! primitive operators (`((a as u64) + (b as u64)) as u32`) so `-Zmir-opt-level=0`
//! lowers them to pure MIR `CastKind::IntToInt` + `Rvalue::BinaryOp` +
//! `SwitchInt` + `TerminatorKind::Call` without unmodeled `core::num` or
//! `core::hint::black_box` intrinsic calls.

use std::collections::BTreeSet;

use proc_macro2::{Ident, TokenStream, TokenTree};
use quote::{format_ident, quote};
use syn::visit_mut::{self, VisitMut};
use syn::{Attribute, Block, Expr, File, FnArg, Item, Pat, ReturnType, Stmt, Type};

use crate::mutators_miri::DetRng;

/// Output candidate produced by [`generate_itree_batch`].
/// Guaranteed to parse cleanly as valid Rust and contain **zero** `unsafe` tokens.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneratedItreeCandidate {
    /// Zero-based index within the generated batch.
    pub id: usize,
    /// Index of the seed program from `seeds` that this candidate mutated.
    pub seed_index: usize,
    /// Per-candidate deterministic PRNG seed derived from the batch `seed_u64`.
    pub seed_u64: u64,
    /// Ordered list of safe ITree AST mutators applied to produce this candidate.
    pub applied_mutators: Vec<String>,
    /// Pretty-printed, strictly safe (`0` `unsafe` tokens) Rust source code.
    pub source: String,
}

/// Recursively scans a lexical token stream for any occurrence of the `unsafe` keyword
/// (including inside nested `(...)`, `[...]`, `{...}` groups).
pub fn contains_unsafe_token(source: &str) -> bool {
    let Ok(tokens) = source.parse::<TokenStream>() else {
        return source.contains("unsafe");
    };
    stream_has_unsafe(tokens)
}

fn stream_has_unsafe(stream: TokenStream) -> bool {
    for tt in stream {
        match tt {
            TokenTree::Ident(id) if id == "unsafe" => return true,
            TokenTree::Group(g) if stream_has_unsafe(g.stream()) => return true,
            _ => {}
        }
    }
    false
}

/// Strips any pre-existing `unsafe` items or blocks from an input seed AST so that even
/// mixed seeds produce strictly safe ITree candidates with zero `unsafe` tokens.
fn sanitize_seed_to_safe_rust(file: &mut File) {
    for item in &mut file.items {
        if let Item::Fn(func) = item {
            func.sig.unsafety = None;
            func.block
                .stmts
                .retain(|stmt| !contains_unsafe_token(&quote!(#stmt).to_string()));
        }
    }
}

fn returns_u32(output: &ReturnType) -> bool {
    match output {
        ReturnType::Default => false,
        ReturnType::Type(_, ty) => matches!(
            ty.as_ref(),
            Type::Path(tp) if tp.qself.is_none() && tp.path.is_ident("u32")
        ),
    }
}

fn first_u32_param_expr(func: &syn::ItemFn, fallback: u32) -> Expr {
    for input in &func.sig.inputs {
        if let FnArg::Typed(pat_ty) = input
            && matches!(
                pat_ty.ty.as_ref(),
                Type::Path(tp) if tp.qself.is_none() && tp.path.is_ident("u32")
            )
            && let Pat::Ident(pat_id) = pat_ty.pat.as_ref()
        {
            let id = &pat_id.ident;
            return syn::parse_quote!(#id);
        }
    }
    syn::parse_quote!(#fallback)
}

fn target_fn_index(file: &File) -> Option<usize> {
    file.items
        .iter()
        .rposition(|it| {
            matches!(
                it,
                Item::Fn(f) if !f.sig.ident.to_string().starts_with("__anneal_")
            )
        })
        .or_else(|| file.items.iter().rposition(|it| matches!(it, Item::Fn(_))))
}

/// Wraps a `u32`-returning function body so `new_stmts` run first and fold
/// `fold_ident` into the returned `u32` (preserving live data-flow into `_0`),
/// or prepends `new_stmts` when the function does not return `u32`.
fn weave_into_fn_body(func: &mut syn::ItemFn, mut new_stmts: Vec<Stmt>, fold_ident: &Ident) {
    if returns_u32(&func.sig.output) && !func.block.stmts.is_empty() {
        let orig_block = (*func.block).clone();
        let combined: Block = syn::parse_quote!({
            #(#new_stmts)*
            if #fold_ident == 0 {
                0u32
            } else {
                #orig_block
            }
        });
        *func.block = combined;
    } else {
        let suppress: Stmt = syn::parse_quote!(let _ = #fold_ident;);
        new_stmts.push(suppress);
        new_stmts.append(&mut func.block.stmts);
        func.block.stmts = new_stmts;
    }
}

/// Trait implemented by all strictly safe ITree AST mutators.
pub trait ItreeAstMutator {
    /// Canonical human-readable name of this mutator pass.
    fn name(&self) -> &'static str;

    /// Mutates `file` in place using strictly safe Rust constructs (`0` `unsafe` tokens).
    fn mutate(&self, file: &mut File, rng: &mut DetRng);
}

fn disambiguate_itree_tag(file: &File, base_tag: u64) -> u64 {
    let mut tag = base_tag & 0xFFFF;
    let mut existing = BTreeSet::new();
    for item in &file.items {
        match item {
            Item::Fn(f) => {
                existing.insert(f.sig.ident.to_string());
                for stmt in &f.block.stmts {
                    if let Stmt::Local(loc) = stmt
                        && let Pat::Type(pt) = &loc.pat
                        && let Pat::Ident(pi) = &*pt.pat
                    {
                        existing.insert(pi.ident.to_string());
                    }
                }
            }
            Item::Struct(s) => {
                existing.insert(s.ident.to_string());
            }
            _ => {}
        }
    }
    while existing.contains(&format!("__anneal_itree_outlined_{tag}"))
        || existing.contains(&format!("__anneal_itree_outlined_stage2_{tag}"))
        || existing.contains(&format!("__AnnealSafePadded_{tag}"))
        || existing.contains(&format!("__anneal_ext_oracle_{tag}"))
        || existing.contains(&format!("__itree_step_{tag}"))
    {
        tag = (tag + 1) & 0xFFFF;
    }
    tag
}

/// 1. Outlines computation across a real function call boundary by synthesizing a pure
/// top-level safe helper function and invoking it from the target function body.
#[derive(Debug, Default, Clone, Copy)]
pub struct CallBoundaryOutliner;

impl ItreeAstMutator for CallBoundaryOutliner {
    fn name(&self) -> &'static str {
        "CallBoundaryOutliner"
    }

    fn mutate(&self, file: &mut File, rng: &mut DetRng) {
        let raw_tag = rng.next_u64();
        let tag = disambiguate_itree_tag(file, raw_tag);
        let use_multi_callee = ((raw_tag >> 16) & 1) == 1;
        let helper_ident = format_ident!("__anneal_itree_outlined_{}", tag);
        let stage2_ident = format_ident!("__anneal_itree_outlined_stage2_{}", tag);
        let leaf_ident = format_ident!("__anneal_itree_leaf_{}", tag);
        let k_const = ((rng.next_u64() % 251) as u32).wrapping_add(1);

        if use_multi_callee {
            let helper_item1: Item = syn::parse_quote! {
                #[inline(never)]
                pub fn #helper_ident(seed: u32, delta: u32) -> u32 {
                    #[inline(never)]
                    fn #leaf_ident(v: u32, d: u32) -> u32 {
                        let clamped: u32 = if v <= 0xFFFF_FF00u32 {
                            v + (d & 0xFFu32)
                        } else {
                            0xFFFF_FFFFu32
                        };
                        (clamped >> 1) ^ (d & 0x7Fu32)
                    }
                    let inner: u32 = #leaf_ident(seed, delta);
                    (((inner as u64) + (#k_const as u64)) & 0xFFFF_FFFFu64) as u32
                }
            };
            let helper_item2: Item = syn::parse_quote! {
                #[inline(never)]
                pub fn #stage2_ident(stage1_out: u32, bias: u32) -> u32 {
                    let swapped_low: u32 = ((stage1_out & 0xFFu32) << 8) | ((stage1_out >> 8) & 0xFFu32);
                    let sat_sub: u32 = if swapped_low >= (bias & 0x3Fu32) {
                        swapped_low - (bias & 0x3Fu32)
                    } else {
                        0u32
                    };
                    (sat_sub >> 1) + #k_const
                }
            };

            let target_idx = target_fn_index(file);
            if let Some(idx) = target_idx
                && let Item::Fn(func) = &mut file.items[idx]
            {
                let arg_expr = first_u32_param_expr(func, k_const);
                let stage1_local = format_ident!("__itree_call_s1_{}", tag);
                let local_ident = format_ident!("__itree_call_res_{}", tag);
                let injected: Vec<Stmt> = syn::parse_quote! {
                    let #stage1_local: u32 = #helper_ident(#arg_expr, #k_const);
                    let #local_ident: u32 = #stage2_ident(#stage1_local, #k_const);
                };
                weave_into_fn_body(func, injected, &local_ident);
            }

            file.items.push(helper_item1);
            file.items.push(helper_item2);
        } else {
            let helper_item: Item = syn::parse_quote! {
                #[inline(never)]
                pub fn #helper_ident(seed: u32, delta: u32) -> u32 {
                    let sum = (seed >> 1) + (delta >> 1);
                    (sum >> 2) + #k_const
                }
            };

            let target_idx = target_fn_index(file);
            if let Some(idx) = target_idx
                && let Item::Fn(func) = &mut file.items[idx]
            {
                let arg_expr = first_u32_param_expr(func, k_const);
                let local_ident = format_ident!("__itree_call_res_{}", tag);
                let injected: Vec<Stmt> = syn::parse_quote! {
                    let #local_ident: u32 = #helper_ident(#arg_expr, #k_const);
                };
                weave_into_fn_body(func, injected, &local_ident);
            }

            file.items.push(helper_item);
        }
    }
}

/// 2. Introduces safe `#[repr(C)]` multi-field wrapper structs with natural inter-field
/// alignment padding (`u8`, 3 bytes padding, `u32`, `u8`, 3 bytes padding) and moves values
/// through field construction and projection without a single `unsafe` token.
#[derive(Debug, Default, Clone, Copy)]
pub struct LayoutPaddingPerturber;

impl ItreeAstMutator for LayoutPaddingPerturber {
    fn name(&self) -> &'static str {
        "LayoutPaddingPerturber"
    }

    fn mutate(&self, file: &mut File, rng: &mut DetRng) {
        let tag = disambiguate_itree_tag(file, rng.next_u64());
        let struct_ident = format_ident!("__AnnealSafePadded_{}", tag);
        let init_word = ((rng.next_u64() & 0xFFFF) as u32).wrapping_add(1);

        let struct_item: Item = syn::parse_quote! {
            #[repr(C)]
            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub struct #struct_ident {
                pub lead_byte: u8,
                pub aligned_word: u32,
                pub trail_byte: u8,
            }
        };

        let target_idx = target_fn_index(file);
        if let Some(idx) = target_idx
            && let Item::Fn(func) = &mut file.items[idx]
        {
            let var_ident = format_ident!("__itree_padded_{}", tag);
            let fold_ident = format_ident!("__itree_pad_fold_{}", tag);
            let injected: Vec<Stmt> = syn::parse_quote! {
                let #var_ident = #struct_ident {
                    lead_byte: 0x5Au8,
                    aligned_word: #init_word,
                    trail_byte: 0xA5u8,
                };
                let #fold_ident: u32 = if #var_ident.lead_byte == 0x5Au8
                    && #var_ident.trail_byte == 0xA5u8
                {
                    #var_ident.aligned_word
                } else {
                    0u32
                };
            };
            weave_into_fn_body(func, injected, &fold_ident);
        }

        file.items.push(struct_item);
    }
}

/// 3. Weaves strictly terminating bounded `while` loops and multi-arm `match` switches into
/// function bodies to exercise ITree `tau` step compression and control-flow join points.
#[derive(Debug, Default, Clone, Copy)]
pub struct BranchLoopWeaver;

impl ItreeAstMutator for BranchLoopWeaver {
    fn name(&self) -> &'static str {
        "BranchLoopWeaver"
    }

    fn mutate(&self, file: &mut File, rng: &mut DetRng) {
        let raw_tag = rng.next_u64();
        let tag = disambiguate_itree_tag(file, raw_tag);
        let use_bit_sat_perturb = ((raw_tag >> 16) & 1) == 1;
        let bound: u32 = 2;

        let target_idx = target_fn_index(file);
        if let Some(idx) = target_idx
            && let Item::Fn(func) = &mut file.items[idx]
        {
            let step_ident = format_ident!("__itree_step_{}", tag);
            let acc_ident = format_ident!("__itree_acc_{}", tag);
            let injected: Vec<Stmt> = if use_bit_sat_perturb {
                syn::parse_quote! {
                    let mut #step_ident: u32 = 0;
                    let mut #acc_ident: u32 = 1;
                    while #step_ident < #bound {
                        let __bit_mix: u32 = ((#acc_ident & 0xFFu32) << 4) ^ (#acc_ident >> 2) ^ 1u32;
                        let __sat_step: u32 = if __bit_mix <= 0xFFFF_F000u32 {
                            __bit_mix + 7u32
                        } else {
                            0xFFFF_FFFFu32
                        };
                        #acc_ident = match #step_ident % 2 {
                            0 => (((__sat_step as u64) + 3u64) & 0xFFFF_FFFFu64) as u32,
                            _ => if __sat_step > 5u32 { __sat_step - 5u32 } else { 11u32 },
                        };
                        #step_ident = #step_ident + 1;
                    }
                }
            } else {
                syn::parse_quote! {
                    let mut #step_ident: u32 = 0;
                    let mut #acc_ident: u32 = 1;
                    while #step_ident < #bound {
                        #acc_ident = match #step_ident % 2 {
                            0 => if #acc_ident < 100 { #acc_ident + 3 } else { 7 },
                            _ => if #acc_ident < 100 { #acc_ident + 5 } else { 11 },
                        };
                        #step_ident = #step_ident + 1;
                    }
                }
            };
            weave_into_fn_body(func, injected, &acc_ident);
        }
    }
}

/// 4. Injects a deterministic safe external oracle function `__anneal_ext_oracle_<tag>` and
/// threads its observable call/return interaction through the target function.
#[derive(Debug, Default, Clone, Copy)]
pub struct ExtOracleInjector;

impl ItreeAstMutator for ExtOracleInjector {
    fn name(&self) -> &'static str {
        "ExtOracleInjector"
    }

    fn mutate(&self, file: &mut File, rng: &mut DetRng) {
        let tag = disambiguate_itree_tag(file, rng.next_u64());
        let oracle_ident = format_ident!("__anneal_ext_oracle_{}", tag);
        let mask = ((rng.next_u64() & 0xFF) as u32).wrapping_add(0x100);

        let oracle_item: Item = syn::parse_quote! {
            #[inline(never)]
            pub fn #oracle_ident(query: u32) -> u32 {
                if query % 2 == 0 {
                    (query >> 1) + #mask
                } else {
                    (query >> 2) + (#mask * 3)
                }
            }
        };

        let target_idx = target_fn_index(file);
        if let Some(idx) = target_idx
            && let Item::Fn(func) = &mut file.items[idx]
        {
            let arg_expr = first_u32_param_expr(func, mask);
            let ans_ident = format_ident!("__itree_oracle_ans_{}", tag);
            let injected: Vec<Stmt> = syn::parse_quote! {
                let #ans_ident: u32 = #oracle_ident(#arg_expr);
            };
            weave_into_fn_body(func, injected, &ans_ident);
        }

        file.items.push(oracle_item);
    }
}

/// Attaches `#[anneal_trace::external]` (and `#[inline(never)]`) to every
/// top-level function in `source` whose name is not `root_fn_name`, returning
/// the formatted Rust source and the ordered list of external callee names.
pub fn annotate_itree_external_callees(
    source: &str,
    root_fn_name: &str,
) -> Result<(String, Vec<String>), String> {
    let mut file = syn::parse_str::<File>(source).map_err(|e| e.to_string())?;
    let ext_attr: Attribute = syn::parse_quote!(#[anneal_trace::external]);
    let inline_never_attr: Attribute = syn::parse_quote!(#[inline(never)]);
    let mut ext_callees = Vec::new();

    for item in &mut file.items {
        if let Item::Fn(func) = item {
            let name = func.sig.ident.to_string();
            if name != root_fn_name {
                let has_ext = func.attrs.iter().any(|a| {
                    let s = quote!(#a).to_string();
                    s.contains("anneal_trace") && s.contains("external")
                });
                if !has_ext {
                    func.attrs.insert(0, ext_attr.clone());
                }
                let has_inline = func.attrs.iter().any(|a| a.path().is_ident("inline"));
                if !has_inline {
                    func.attrs.push(inline_never_attr.clone());
                }
                if !ext_callees.contains(&name) {
                    ext_callees.push(name);
                }
            }
        }
    }

    Ok((prettyplease::unparse(&file), ext_callees))
}

/// Staged representation of a single [`GeneratedItreeCandidate`] with all
/// top-level items prefixed by `cand_prefix` (for example, `"b0_c0__"`) and
/// external callees annotated with `#[anneal_trace::external]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StagedItreeCandidate {
    /// Unique candidate prefix (e.g., `"b0_c0__"`).
    pub cand_prefix: String,
    /// Staged root function identifier (e.g., `"b0_c0__kernel_step"`).
    pub root_fn_name: String,
    /// Staged external callee identifiers annotated with `#[anneal_trace::external]`.
    pub ext_callee_names: Vec<String>,
    /// Formatted Rust source ready to be included in a combined crate.
    pub staged_source: String,
}

struct TopLevelPrefixRewriter<'a> {
    prefix: &'a str,
    top_names: &'a BTreeSet<String>,
}

impl VisitMut for TopLevelPrefixRewriter<'_> {
    fn visit_path_mut(&mut self, node: &mut syn::Path) {
        if node.leading_colon.is_none() && node.segments.len() == 1 {
            let ident_str = node.segments[0].ident.to_string();
            if self.top_names.contains(&ident_str) {
                node.segments[0].ident = format_ident!("{}{}", self.prefix, ident_str);
            }
        }
        visit_mut::visit_path_mut(self, node);
    }
}

/// Prefixes every top-level declaration and reference in `source` with
/// `cand_prefix`, leaves `root_fn_name`'s body untouched (adding only
/// `#[inline(never)]`), and attaches `#[anneal_trace::external]` +
/// `#[inline(never)]` to all other top-level functions.
pub fn stage_itree_candidate_items(
    source: &str,
    cand_prefix: &str,
    root_fn_name: &str,
) -> Result<StagedItreeCandidate, String> {
    let mut file = syn::parse_str::<File>(source).map_err(|e| e.to_string())?;
    let mut top_names = BTreeSet::new();
    for item in &file.items {
        match item {
            Item::Fn(f) => {
                top_names.insert(f.sig.ident.to_string());
            }
            Item::Struct(s) => {
                top_names.insert(s.ident.to_string());
            }
            Item::Enum(e) => {
                top_names.insert(e.ident.to_string());
            }
            Item::Type(t) => {
                top_names.insert(t.ident.to_string());
            }
            Item::Const(c) => {
                top_names.insert(c.ident.to_string());
            }
            _ => {}
        }
    }

    let mut rewriter = TopLevelPrefixRewriter {
        prefix: cand_prefix,
        top_names: &top_names,
    };
    rewriter.visit_file_mut(&mut file);

    let ext_attr: Attribute = syn::parse_quote!(#[anneal_trace::external]);
    let inline_never_attr: Attribute = syn::parse_quote!(#[inline(never)]);
    let staged_root_fn = format!("{cand_prefix}{root_fn_name}");
    let mut ext_callee_names = Vec::new();
    let mut found_root = false;

    for item in &mut file.items {
        match item {
            Item::Fn(func) => {
                let orig_name = func.sig.ident.to_string();
                let new_name = format!("{cand_prefix}{orig_name}");
                func.sig.ident = format_ident!("{new_name}");
                let has_inline = func.attrs.iter().any(|a| a.path().is_ident("inline"));
                if !has_inline {
                    func.attrs.push(inline_never_attr.clone());
                }
                if orig_name == root_fn_name {
                    found_root = true;
                } else {
                    let has_ext = func.attrs.iter().any(|a| {
                        let s = quote!(#a).to_string();
                        s.contains("anneal_trace") && s.contains("external")
                    });
                    if !has_ext {
                        func.attrs.insert(0, ext_attr.clone());
                    }
                    ext_callee_names.push(new_name);
                }
            }
            Item::Struct(s) => {
                s.ident = format_ident!("{cand_prefix}{}", s.ident);
            }
            Item::Enum(e) => {
                e.ident = format_ident!("{cand_prefix}{}", e.ident);
            }
            Item::Type(t) => {
                t.ident = format_ident!("{cand_prefix}{}", t.ident);
            }
            Item::Const(c) => {
                c.ident = format_ident!("{cand_prefix}{}", c.ident);
            }
            _ => {}
        }
    }

    if !found_root {
        return Err(format!(
            "target root function `{root_fn_name}` not found in candidate source"
        ));
    }

    Ok(StagedItreeCandidate {
        cand_prefix: cand_prefix.to_string(),
        root_fn_name: staged_root_fn,
        ext_callee_names,
        staged_source: prettyplease::unparse(&file),
    })
}

/// Generates an identity (unmutated) batch containing one
/// [`GeneratedItreeCandidate`] per seed in `seeds`.
pub fn generate_itree_identity_batch(seeds: &[&str]) -> Vec<GeneratedItreeCandidate> {
    let mut out = Vec::with_capacity(seeds.len());
    for (id, seed_src) in seeds.iter().enumerate() {
        let Ok(mut parsed) = syn::parse_str::<File>(seed_src) else {
            continue;
        };
        sanitize_seed_to_safe_rust(&mut parsed);
        let formatted = prettyplease::unparse(&parsed);
        assert!(
            !contains_unsafe_token(&formatted),
            "ITree identity seed {id} emitted forbidden `unsafe` token:\n{formatted}"
        );
        out.push(GeneratedItreeCandidate {
            id,
            seed_index: id,
            seed_u64: id as u64,
            applied_mutators: Vec::new(),
            source: formatted,
        });
    }
    out
}

/// The safe ITree AST mutators, in the order in which [`generate_itree_batch`]
/// indexes them when it picks a pass's mutator.
pub const ITREE_AST_MUTATORS: [&dyn ItreeAstMutator; 4] = [
    &CallBoundaryOutliner,
    &LayoutPaddingPerturber,
    &BranchLoopWeaver,
    &ExtOracleInjector,
];

fn itree_mutator_by_name(name: &str) -> Option<&'static dyn ItreeAstMutator> {
    ITREE_AST_MUTATORS.into_iter().find(|m| m.name() == name)
}

/// One mutation pass of a generated ITree candidate, recorded so that any
/// subsequence of the candidate's passes can be replayed exactly
/// ([`replay_itree_mutation_steps`]).
#[derive(Debug, Clone)]
pub struct ItreeMutationStep {
    /// Zero-based index of this pass in the candidate's mutator chain.
    pub pass_index: usize,
    /// Canonical mutator name (`CallBoundaryOutliner`, `LayoutPaddingPerturber`,
    /// `BranchLoopWeaver`, or `ExtOracleInjector`).
    pub mutator_name: String,
    /// PRNG state immediately before this pass's `mutate` call.
    pub rng_before_step: DetRng,
}

/// Parse `seed_src` and strip any `unsafe` items or blocks from it, as
/// [`generate_itree_batch`] does before mutating a seed.
fn parse_safe_itree_seed(seed_src: &str) -> Option<File> {
    let mut parsed = syn::parse_str::<File>(seed_src).ok()?;
    sanitize_seed_to_safe_rust(&mut parsed);
    Some(parsed)
}

/// Draw and apply candidate `id`'s mutation passes, recording for each pass the
/// mutator and the PRNG state that `mutate` started from. The first pass's
/// mutator rotates with `id`; every later pass draws a different mutator.
fn apply_itree_mutation_passes(
    parsed: &mut File,
    cand_rng: &mut DetRng,
    id: usize,
) -> Vec<ItreeMutationStep> {
    let mutator_count = ITREE_AST_MUTATORS.len();
    let num_passes = 1 + cand_rng.gen_range(2);
    let first_idx = id % mutator_count;
    let mut steps = Vec::with_capacity(num_passes);
    for pass in 0..num_passes {
        let m_idx = if pass == 0 {
            first_idx
        } else {
            (first_idx + 1 + cand_rng.gen_range(mutator_count - 1)) % mutator_count
        };
        let mutator = ITREE_AST_MUTATORS[m_idx];
        let rng_before_step = cand_rng.clone();
        mutator.mutate(parsed, cand_rng);
        steps.push(ItreeMutationStep {
            pass_index: pass,
            mutator_name: mutator.name().to_string(),
            rng_before_step,
        });
    }
    steps
}

/// Reconstruct the sanitized, unmutated seed AST and the recorded mutation
/// passes of a candidate that [`generate_itree_batch`] produced from `seeds`, by
/// re-running the generator's per-candidate PRNG schedule from `cand.seed_u64`
/// with the same code the generator runs.
///
/// Returns `None` when `cand` cannot have come from this schedule over `seeds`:
/// its `seed_index` is out of range or is not the seed `id % seeds.len()` that
/// the generator mutates, or the schedule draws a different number or
/// sequence of mutators than `cand.applied_mutators`. A `Some` result is still
/// only a candidate history; [`itree_candidate_replay_is_faithful`] decides
/// whether it reproduces `cand.source` byte for byte.
pub fn reconstruct_itree_mutation_steps(
    cand: &GeneratedItreeCandidate,
    seeds: &[&str],
) -> Option<(File, Vec<ItreeMutationStep>)> {
    let base = parse_safe_itree_seed(seeds.get(cand.seed_index)?)?;
    // The generator mutates seed `id % seeds.len()` for candidate `id`.
    if cand.seed_index != cand.id % seeds.len() {
        return None;
    }
    let mut cand_rng = DetRng::new(cand.seed_u64);
    let mut probe = base.clone();
    let steps = apply_itree_mutation_passes(&mut probe, &mut cand_rng, cand.id);
    let names_match = steps.len() == cand.applied_mutators.len()
        && steps
            .iter()
            .zip(&cand.applied_mutators)
            .all(|(step, name)| step.mutator_name == *name);
    names_match.then_some((base, steps))
}

/// Replay the subsequence `steps` of a candidate's recorded mutation passes on
/// its sanitized seed `base`, starting each pass from its recorded PRNG state,
/// and return the resulting candidate (with `cand`'s identity fields).
pub fn replay_itree_mutation_steps(
    cand: &GeneratedItreeCandidate,
    base: &File,
    steps: &[ItreeMutationStep],
) -> GeneratedItreeCandidate {
    let mut parsed = base.clone();
    let mut applied_mutators = Vec::with_capacity(steps.len());
    for step in steps {
        if let Some(mutator) = itree_mutator_by_name(&step.mutator_name) {
            let mut step_rng = step.rng_before_step.clone();
            mutator.mutate(&mut parsed, &mut step_rng);
            applied_mutators.push(step.mutator_name.clone());
        }
    }
    GeneratedItreeCandidate {
        id: cand.id,
        seed_index: cand.seed_index,
        seed_u64: cand.seed_u64,
        applied_mutators,
        source: prettyplease::unparse(&parsed),
    }
}

/// Whether replaying the full recorded chain `steps` from `base` reproduces
/// `cand` byte for byte (canonical `0..steps.len()` `pass_index`es, same
/// `applied_mutators` and `source`) and the source contains zero `unsafe` tokens.
///
/// Shrinking is only meaningful when this holds: only then is every replayed
/// subsequence a reduction of the reported program, and only then is the full
/// chain known to reproduce the original finding without re-running the oracle.
pub fn itree_candidate_replay_is_faithful(
    cand: &GeneratedItreeCandidate,
    base: &File,
    steps: &[ItreeMutationStep],
) -> bool {
    if steps.len() != cand.applied_mutators.len()
        || !steps.iter().enumerate().all(|(i, s)| s.pass_index == i)
        || contains_unsafe_token(&cand.source)
    {
        return false;
    }
    let replayed = replay_itree_mutation_steps(cand, base, steps);
    replayed.applied_mutators == cand.applied_mutators && replayed.source == cand.source
}

/// Generates `count` deterministic, syntactically valid, strictly safe (`0` `unsafe` tokens)
/// ITree candidate programs from `seeds` using a PRNG keyed by `seed_u64`.
pub fn generate_itree_batch(
    seeds: &[&str],
    count: usize,
    seed_u64: u64,
) -> Vec<GeneratedItreeCandidate> {
    if seeds.is_empty() || count == 0 {
        return Vec::new();
    }

    let mut master_rng = DetRng::new(seed_u64);
    let mut out = Vec::with_capacity(count);

    for id in 0..count {
        let seed_index = id % seeds.len();
        let cand_seed = master_rng.next_u64() ^ ((id as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let mut cand_rng = DetRng::new(cand_seed);

        let Some(mut parsed) = parse_safe_itree_seed(seeds[seed_index]) else {
            continue;
        };
        let applied_mutators = apply_itree_mutation_passes(&mut parsed, &mut cand_rng, id)
            .into_iter()
            .map(|step| step.mutator_name)
            .collect();

        let formatted = prettyplease::unparse(&parsed);
        assert!(
            !contains_unsafe_token(&formatted),
            "ITree candidate emitted forbidden `unsafe` token:\n{formatted}"
        );

        out.push(GeneratedItreeCandidate {
            id,
            seed_index,
            seed_u64: cand_seed,
            applied_mutators,
            source: formatted,
        });
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAFE_SEED: &str = r#"
        pub fn evaluate_state(a: u32, b: u32) -> u32 {
            if a > b {
                (((a as u64) + 0x1_0000_0000u64) - (b as u64)) as u32
            } else {
                ((b as u64) + (a as u64)) as u32
            }
        }
    "#;

    #[test]
    fn generate_itree_batch_emits_zero_unsafe_tokens_and_valid_syntax() {
        let batch = generate_itree_batch(&[SAFE_SEED], 16, 0x0123_4567_89AB_CDEF);
        assert_eq!(batch.len(), 16);

        let mut seen = std::collections::BTreeSet::new();
        for cand in &batch {
            assert!(
                !contains_unsafe_token(&cand.source),
                "candidate {} unexpectedly contained `unsafe`:\n{}",
                cand.id,
                cand.source
            );
            assert!(
                syn::parse_file(&cand.source).is_ok(),
                "candidate {} failed syn::parse_file:\n{}",
                cand.id,
                cand.source
            );
            for m in &cand.applied_mutators {
                seen.insert(m.as_str());
            }
        }

        for expected in [
            "CallBoundaryOutliner",
            "LayoutPaddingPerturber",
            "BranchLoopWeaver",
            "ExtOracleInjector",
        ] {
            assert!(seen.contains(expected), "missing ITree mutator `{expected}`");
        }
    }

    /// The live ITree oracle test (`itree_difftest_oracle.rs`) evaluates
    /// `generate_itree_batch(ITREE_SAFE_SEEDS, 20, 0x3333_4444)` and requires 0
    /// not-compared candidates (no unmodeled external call at `-O0` or `-O2`),
    /// so that batch must contain the depth-2 multi-callee outline (including
    /// its nested leaf `fn`) and the bit/saturating loop variant, and every
    /// candidate must replay faithfully from its recorded steps.
    #[test]
    fn live_itree_oracle_batch_covers_multi_callee_and_bit_sat_variants() {
        let seeds = crate::itree_eval::ITREE_SAFE_SEEDS;
        let batch = generate_itree_batch(seeds, 20, 0x3333_4444);
        assert_eq!(batch.len(), 20);
        assert!(
            batch.iter().any(|c| c.source.contains("__anneal_itree_outlined_stage2_")
                && c.source.contains("__anneal_itree_leaf_")),
            "live ITree batch lacks the depth-2 multi-callee outline variant"
        );
        assert!(
            batch
                .iter()
                .any(|c| c.source.contains("__bit_mix") && c.source.contains("__sat_step")),
            "live ITree batch lacks the bit/saturating loop variant"
        );
        for cand in &batch {
            assert!(!contains_unsafe_token(&cand.source));
            let (base, steps) = reconstruct_itree_mutation_steps(cand, seeds)
                .expect("reconstruct ITree steps");
            assert!(
                itree_candidate_replay_is_faithful(cand, &base, &steps),
                "ITree replay mismatch on candidate {}",
                cand.id
            );
        }
    }

    #[test]
    fn call_boundary_outliner_and_branch_loop_weaver_emit_multi_callee_and_safe_bit_sat_variants() {
        let mut saw_multi_callee = false;
        let mut saw_single_callee = false;
        let mut saw_bit_sat_loop = false;

        for s in 0..32u64 {
            let mut f_call = syn::parse_file(SAFE_SEED).unwrap();
            let mut rng_call = DetRng::new(s);
            CallBoundaryOutliner.mutate(&mut f_call, &mut rng_call);
            let src_call = prettyplease::unparse(&f_call);
            assert!(!contains_unsafe_token(&src_call));
            if src_call.contains("__anneal_itree_outlined_stage2_")
                && src_call.contains("__anneal_itree_leaf_")
            {
                saw_multi_callee = true;
            } else if src_call.contains("__anneal_itree_outlined_") {
                saw_single_callee = true;
            }

            let mut f_loop = syn::parse_file(SAFE_SEED).unwrap();
            let mut rng_loop = DetRng::new(s);
            BranchLoopWeaver.mutate(&mut f_loop, &mut rng_loop);
            let src_loop = prettyplease::unparse(&f_loop);
            assert!(!contains_unsafe_token(&src_loop));
            if src_loop.contains("__bit_mix") && src_loop.contains("__sat_step") {
                saw_bit_sat_loop = true;
            }
        }

        assert!(saw_multi_callee, "expected depth-2 multi-callee outline variant");
        assert!(saw_single_callee, "expected single-callee outline variant");
        assert!(saw_bit_sat_loop, "expected bit/saturating/wrapping loop variant");
    }

    #[test]
    fn disambiguate_itree_tag_resolves_duplicate_rng_tags_without_advancing_rng() {
        for mutator in ITREE_AST_MUTATORS {
            let mut file = syn::parse_file(SAFE_SEED).unwrap();
            let mut rng1 = DetRng::new(0xABCD_1234);
            mutator.mutate(&mut file, &mut rng1);
            let mut state_after_first = rng1;
            let mut rng2 = DetRng::new(0xABCD_1234);
            mutator.mutate(&mut file, &mut rng2);
            assert_eq!(
                rng2.next_u64(),
                state_after_first.next_u64(),
                "`{}` tag disambiguation must not consume extra PRNG draws",
                mutator.name()
            );
            let rendered = prettyplease::unparse(&file);
            assert!(!contains_unsafe_token(&rendered));
            let reparsed = syn::parse_file(&rendered).unwrap();
            let mut top_names = BTreeSet::new();
            for item in &reparsed.items {
                match item {
                    Item::Fn(f) => assert!(
                        top_names.insert(f.sig.ident.to_string()),
                        "duplicate fn `{}` from `{}`",
                        f.sig.ident,
                        mutator.name()
                    ),
                    Item::Struct(s) => assert!(
                        top_names.insert(s.ident.to_string()),
                        "duplicate struct `{}` from `{}`",
                        s.ident,
                        mutator.name()
                    ),
                    _ => {}
                }
            }
        }
    }
}
